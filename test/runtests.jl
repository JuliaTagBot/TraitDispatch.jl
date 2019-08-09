using Test

using TraitDispatch

# basic
type_property(::Type{Int}) = 1
type_property(::Type{Float64}) = 2
@traitfn test1(a::T1) where {T1; type_property(T1) == 1} = "Int"
@traitfn test1(a::T1) where {T1; type_property(T1) == 2} = "Float"

@test test1(1) == "Int"
@test test1(1.) == "Float"

# generic function
@traitfn test2(a::T1) where {T1; type_property(T1) == 1} = "Int"
@traitfn test2(a::T1) where {T1; type_property(T1) == 2} = "Float"
@traitfn test2(a::T1, b::T2) where {T1, T2; type_property(T1) == 1 && type_property(T2) == 2} = "Int, Float"

@test test2(1) == "Int"
@test test2(1.) == "Float"
@test test2(1, 1.) == "Int, Float"
@test_throws MethodError test2(1, 1)

# macrocall
@traitfn @inline test3(::T1) where {T1} = 1
@test test3(Int) == 1

# trait resolved ambiguity
struct A end
struct B end

@traitfn test4(a::T, b::Float64) where {T; T == A} = A
@traitfn test4(a::T, b::Float64) where {T; T == B} = B

@test test4(A(), 1.) == A
@test test4(B(), 1.) == B
