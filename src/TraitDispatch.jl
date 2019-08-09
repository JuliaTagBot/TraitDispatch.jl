module TraitDispatch

using MacroTools
using Base: @pure

export @traitfn

const selection_vector_size = 10
const trait_dispatch_method_table = Dict()
const sig_map = Dict()
const sig_from_id_map = Dict()
const dispatchee_suffix = gensym()

struct MethodSelector{F, sig, sel_vec} end

_type_intersect(@nospecialize(x), @nospecialize(y)) = ccall(:jl_intersect_types, Any, (Any, Any), x, y)

function _signature_id(sig)
  if !haskey(sig_map, sig)
    sig_map[sig] = gensym()
    sig_from_id_map[sig_map[sig]] = sig
  end
  sig_map[sig]
end

_signature_from_id(sig_id) = sig_from_id_map[sig_id]

macro _replace(expr, old, new)
  esc(:($(MacroTools.postwalk)(subex -> subex == $(Expr(:quote, old)) ? $(Expr(:quote, new)) : subex, $expr)))
end

istrait(::Any, ::Type{<:Tuple}, ::Val, params...) = false

function _fnsig_from_sig(f, sig)
  # copy signature to avoid inteference with the caller
  sig = deepcopy(sig)
  # extract underlying datatype of signature
  baresig = sig
  while !isa(baresig, DataType)
    baresig = baresig.body
  end
  # add type of function instance to signature
  baresig.parameters = Base.Core.svec(typeof(f), baresig.parameters...)
  # return altered signature
  sig
end

function dispatch_fn_def_required(mod, name, sig)
  # first try to get fn instance
  local f
  try
    f = getfield(mod, name)
  catch
    # fn instance not defined yet so return true
    return true
  end
  # first unpeal all where statements from signature
  #  i.e. turn Tuple{A} where A into Tuple{A}
  baresig = sig
  while !isa(baresig, DataType)
    baresig = baresig.body
  end
  #  now check if `f` already has a method matching the signature
  tt = _fnsig_from_sig(f, sig)
  world = typemax(UInt)
  min = UInt[typemin(UInt)]
  max = UInt[typemax(UInt)]
  ms = ccall(:jl_matching_methods, Any, (Any, Cint, Cint, UInt, Ptr{UInt}, Ptr{UInt}), tt, -1, 1, world, min, max)
  return length(ms)==0
end

function register_trait_dispatch_method(F, sig)
  if !haskey(trait_dispatch_method_table, F)
    trait_dispatch_method_table[F] = []
  end
  # find all (trait dispatched) methods of F which match the signature
  sel_vec_pos = 1
  for mt_sig in trait_dispatch_method_table[F]
    if _type_intersect(mt_sig, sig) != Union{} # todo: document & double check (maybe use jl_matching_methods)
      sel_vec_pos += 1
    end
  end
  if sel_vec_pos == selection_vector_size
    error("Method table space exhausted for trait fn $(F)")
  end
  # add method to method table
  push!(trait_dispatch_method_table[F], sig)
  # return selection vector
  sel_vec_pos
end

@pure function method_selector(f, sig_id)
  sig = sig_from_id_map[sig_id] # obtain signature for signature id
  found, sel_vec = selection_vector(f, sig)
  if found
    return MethodSelector{typeof(f), sig, sel_vec}()
  else
    return MethodSelector{typeof(f), sig, :default}()
  end
end

function selection_vector(f, sig; state=(false, ()))
  already_matched, sel_vec = state # extract state
  i = length(sel_vec)+1 # index of the selection vector

  # check if the trait matches, if it throws an exception we will just ignore it
  local matches
  try
    matches = istrait(f, sig, Val{i}())
  catch e
    # rethrow(e) # debug
    matches = false
  end

  # check for ambiguity
  if matches && already_matched
    error("Method call to $f with signature $sig is ambiguous")
  end

  new_state = (matches || already_matched, (sel_vec..., matches))

  i == selection_vector_size ? new_state : selection_vector(f, sig; state=new_state)
end

macro traitfn(ex)
  # dissect ast
  #  - extract actual trait fn definition by unpealing all macros
  #  - extract line information
  tfn = ex
  while isa(tfn, Expr) && tfn.head == :macrocall
    i = findfirst(ex->isexpr(ex), tfn.args)
    i != nothing || error("Error while unpealing macrocalls")
    tfn = tfn.args[i]
  end

  # dissect tfn ast (e.g. f(a::A, b::T1) where {T1 <: Real; trait} = body)
  #  name: function name
  #  args: vector of all function arguments, e.g. `[:(a::A, b::T1)]`
  #  kwargs: vector of all keyword arguments
  #  body: function body
  #  trait: trait expression the function dispatches on, e.g. `trait`
  #  types0: vector containg all function parameters and their type constraints, e.g. `[:(T1 <: Real)]`
  #  types1: vector containg all function parameters, e.g.`[:T1]`
  #  argvs: vector containg all argument names, e.g. `[:a, :b]`
  #  argts: vector containg all argument types, e.g. `[:A, :T1]`
  #  sig: tuple type representing the fn signature, e.g. Tuple{A, ##123} where {##123 <: Real}
  name, args, kwargs, body, whereparams = (splitdef(tfn)[key] for key in (:name, :args, :kwargs, :body, :whereparams))

  length(kwargs) == 0 || error("kw args not supported")

  if length(whereparams)==1 && isa(whereparams[1], Expr) && whereparams[1].head == :bracescat # {T_; trait}
    @assert length(whereparams[1].args) == 2
    types0 = [whereparams[1].args[1]]
    trait = whereparams[1].args[2]
    isdefault = false
  elseif length(whereparams)>1 && isa(whereparams[1], Expr) && whereparams[1].head == :parameters # {T__; trait}
    @assert length(whereparams[1].args) == 1
    types0 = whereparams[2:end]
    trait = whereparams[1].args[1]
    isdefault = false
  else
    types0 = whereparams
    trait = true
    isdefault = true
  end
  types1 = []
  stypes = []
  for ex in types0
    if isa(ex, Symbol)
      push!(types1, ex)
      push!(stypes, :Any)
    elseif @capture(ex, T_ <: ST_)
      push!(types1, T)
      push!(stypes, ST)
    else
      error("Could not parse argument type specification $(ex)")
    end
  end

  # parse arguments
  argvs = []
  argts = []
  args1 = []
  for arg in args
    if isa(arg, Expr) && arg.head == :(::)
      if length(arg.args) == 1 # ::A
        v, t = gensym(), arg.args[1]
      else
        v, t = arg.args # a::A
      end
    elseif isa(arg, Symbol) # a
      v, t = arg, :Any
    else
      error("Unsupported ast format for trait fn arg $(arg)")
    end
    push!(argvs, v)
    push!(argts, t)
    push!(args1, Expr(:(::), v, t))
  end

  # parse signature
  #  replace all free typevars in argts by new symbols to avoid clashes
  sig = let
    types_map = Dict()
    for type in types1
      types_map[type] = gensym()
    end
    argtsp = []
    for argt in argts
      # todo: if we have an static parameter T1 and an argument type containing
      #  an expression like Something.T1 then T1 should not be replaced
      push!(argtsp, MacroTools.prewalk(argt) do ex
        if isa(ex, Symbol) && ex ∈ types1
          types_map[ex]
        else
          ex
        end
      end)
    end
    types0p = map(types0) do ex
      if isa(ex, Symbol)
        types_map[ex]
      elseif @capture(ex, T_ <: ST_)
        :($(types_map[T]) <: $ST)
      else
        error("Could not parse argument type specification $(ex)")
      end
    end
    :(Tuple{$(argtsp...)} where {$(types0p...)})
  end
  traitsig = :(Tuple{$(argts...)})

  # generate resulting expression
  dispatchee_name = Symbol(name, dispatchee_suffix)

  out_ex = Expr(:block, quote
    import TraitDispatch: istrait

    if TraitDispatch.dispatch_fn_def_required(@__MODULE__, $(QuoteNode(name)), $sig)
      @generated function $name($(args1...)) where {$(types0...)}
        sig = Tuple{$(argvs...)}
        # since the signature is not a concrete type the invoked method of the method
        #  selector would not be inferred (regardless of the fact that it will only
        #  ever have one method) so we instead create a bidirectional mapping from
        #  the signature to a symbol and use it as an argument for the method
        #   selector (there might be a smarter way to do this, let me know)
        sig_id = TraitDispatch._signature_id(sig)
        :($$dispatchee_name(TraitDispatch.method_selector($$name, $(QuoteNode(sig_id))), $$(map(argv -> QuoteNode(argv), argvs)...)))
      end
    end
  end)

  if isdefault
    push!(out_ex.args, @_replace(ex, $tfn, function $dispatchee_name(::TraitDispatch.MethodSelector{typeof($name), <: $sig, :default}, $(args...)) where {$(types0...)}
      $body
    end))
  else
    push!(out_ex.args, quote
      let sel_vec_pos = TraitDispatch.register_trait_dispatch_method(typeof($name), $sig),
          method_selector = TraitDispatch.MethodSelector{typeof($name), <: $sig, (map(i -> i==sel_vec_pos, 1:TraitDispatch.selection_vector_size)...,)}
        global istrait, $dispatchee_name

        function istrait(::typeof($name), ::Type{<:$traitsig}, ::Val{sel_vec_pos}) where {$(types0...)}
          $trait
        end

        $(@_replace(ex, $tfn, function $dispatchee_name(::method_selector, $(args...)) where {$(types0...)}
          $body
        end))
      end
    end)
  end

  esc(out_ex)
end

function hasfield(mod::Module, s::Symbol)
  try
    getfield(mod, s)
    return true
  catch
    return false
  end
end

end # module
