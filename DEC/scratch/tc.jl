using Metatheory
using Metatheory: OptBuffer
using Metatheory.Library
using Metatheory.Rewriters
using MLStyle
using Test
using Metatheory.Plotting

b = OptBuffer{UInt128}(10)

@testset "Predicate Assertions" begin
  r = @rule ~a::iseven --> true
  Base.iseven(g, ec::EClass) =
    any(ec.nodes) do n
      h = v_head(n)
      if has_constant(g, h)
        c = get_constant(g, h)
        return c isa Number && iseven(c)
      end
      false
    end
  #
  g = EGraph(:(f(2, 1)))
  @test r.ematcher_left!(g, 0, g.root, r.stack, b) == 0
  #
  g = EGraph(:2)
  @test r.ematcher_left!(g, 0, g.root, r.stack, b) == 1
  #
  g = EGraph(:3)
  @test r.ematcher_left!(g, 0, g.root, r.stack, b) == 0
  #
  new_id = addexpr!(g, :f)
  union!(g, g.root, new_id)
  #
  new_id = addexpr!(g, 4)
  union!(g, g.root, new_id)
  #
  @test r.ematcher_left!(g, 0, g.root, r.stack, b) == 1
end

###

abstract type AbstractSort end

@data Sort <: AbstractSort begin
  Scalar
  Form(dim::Int)
end

@testset "Check form" begin
  
  function isform(g, ec::EClass)
    any(ec.nodes) do n
      h = v_head(n)
      if has_constant(g, h)
        c = get_constant(g, h)
        @info "$c, $(typeof(c))"
        return c isa Form
      end
      false
    end
  end

  r = @rule ~a::isform --> true
  
  t = @theory a begin
    ~a::isform + ~b::isform --> 0
  end

  ## initialize and sanity-check
  a1=Form(1); a2=Form(2)
  a3=Form(1); a4=Form(1)
  @assert a1 isa Form; @assert a3 isa Form
  @assert a3 isa Form; @assert a4 isa Form

  g = EGraph(:($a1 + $a2))
  saturate!(g, t)
  extract!(g, astsize)

  g = EGraph(:a1)
  @test r.ematcher_left!(g, 0, g.root, r.stack, b) == 1

  g = EGraph(:a3)
  @test r.ematcher_left!(g, 0, g.root, r.stack, b) == 0


  g = EGraph(:(a + b ))
  saturate!(g, t)
  extract!(g, astsize)
  

end


abstract type AbstractSort end

@data Sort <: AbstractSort begin
  Scalar
  Form(dim::Int)
end

t = @theory a b begin
  a::Form(1) ∧ b::Form(2) --> 0
end
# breaks! makevar @ MT/src/Syntax.jl:57 (<- makepattern, ibid:151)
# expects Symbol, not Expr

function isform(g, ec::EClass)
  any(ec.nodes) do n
    h = v_head(n)
    if has_constant(g, h)
      c = get_constant(g, h)
      @info "$c, $(typeof(c)), $(c isa Form)"
      return c isa Form
    end
  end
end

r = @rule ~a::isform --> true

g = EGraph(:(f(2, 1)))
@test r.ematcher_left!(g, 0, g.root, r.stack, b) == 0

g = EGraph(:2)
@test r.ematcher_left!(g, 0, g.root, r.stack, b) == 1

g = EGraph(:3)
@test r.ematcher_left!(g, 0, g.root, r.stack, b) == 0

new_id = addexpr!(g, :f)
union!(g, g.root, new_id)

new_id = addexpr!(g, 4)
union!(g, g.root, new_id)

@test r.ematcher_left!(g, 0, g.root, r.stack, b) == 1





a=Form(1)
b=Form(2)
c=Form(1)
d=Form(1)
@assert a isa Form
@assert b isa Form
@assert c isa Form
@assert d isa Form

ex = :(a + b + c + d)
g = EGraph(ex)
saturate!(g, _T)
extract!(g, astsize)


@data Sort1 <: AbstractSort begin
  AnyForm
end

_t = @theory a b begin
  a::AnyForm ∧ b::AnyForm --> 0
end
# PatVar error

__t = @theory a b begin
  a::var"AnyForm's constructor" + 0 --> a
end

d0 = AnyForm
d1 = AnyForm
d2 = AnyForm
ex = :(d0 + 0 + (d1 + 0) + d2)

g = EGraph(ex)
saturate!(g, __t)
extract!(g, astsize)


rwth = Fixpoint(Prewalk(Chain(__t)))
rwth(ex)

g = EGraph(ex)
saturate!(g, _t)
extract!(g, astsize)
# returns (a ∧ b), as 

rwth = Fixpoint(Prewalk(Chain(_t)))
rwth(ex)

a = Form(0)
ex = :(a ∧ b)


Derivative = @theory f g a begin
  f::Function * d(g::Function) + d(f::Function) * g::Function --> d(f * g)
  d(f::Function) + d(g::Function) --> d(f + g)
  d(a::Number * f::Function) --> a * d(f)
end

_Derivative = @theory f g a begin
  f * d(g) + d(f) * g --> d(f * g)
  d(f) + d(g) --> d(f + g)
  d(a * f) --> a * d(f)
end

ex = :(f * d(g) + d(f) * g)

rwth = Fixpoint(Prewalk(Chain(_Derivative)))
rwth(ex)

foo(x) = x + 1
goo(x) = x + 3

rwth = Fixpoint(Prewalk(Chain(Derivative)))
rwth(ex)

g = EGraph(ex)
saturate!(g, Derivative);
extract!(g, astsize)


rwth(ex)


types = (U=Form(0), k=Scalar(),);

tc(x) = @match x begin
  s::Symbol => types[s]
  ::Expr => true
end

cond = x -> begin
  @info "$x, $(type(x))"
  tc(x)
end

orw = Fixpoint(Prewalk(If(cond, Chain(rewrite_theory))))

orw(expr)
