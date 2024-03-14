
@theory Spaces begin
  Dim::TYPE
  Space(d)::TYPE ⊣ [d::Dim]
  Fun(X, Y)::TYPE ⊣ [X::Space, Y::Space]

  Bun(X)::TYPE ⊣ [X::Space]
  pullback(f, V)::Bun(X) ⊣ [(X, Y)::Space, f::Fun(X, Y), V::Bun(Y)]

  Section(V)::TYPE ⊣ [X::Space, V::Bun(X)]
  @alias Γ := Section
  pullback(f, v)::Γ(pullback(f, V)) ⊣ [(X,Y)::Space, f::Fun(X,Y), V::Bun(Y), v::Γ(V)]
end

@theory SemiAdditiveSpaces <: Spaces begin
  (v + w)::Γ(V) ⊣ [X::Space, V::Bun(X), (v, w)::Γ(V)]
  zero(V)::Γ(V) ⊣ [X::Space, V::Bun(X)]
end

@theory SemiRingSpaces <: SemiAdditiveSpaces begin
  scalars(X)::Bun(X) ⊣ [X::Space]
  scale(α, v) ⊣ [X::Space, V::Bun(X), v::Γ(V), α::scalars(X)]
end

@theory RingSpaces <: SemiRingSpaces begin
  neg::Op1(V, V) ⊣ [X::Space, V::Bun(X)]
end

@theory DualSpaces <: RingSpaces begin
  Dual(V)::Bun(X) ⊣ [X::Space, V::Bun(X)]
  pairing::Op1(Dual(V) ⊗ V, scalars(X)) ⊣ [X::Space, V::Bun(X)]
end

@theory DiffSpaces <: Spaces begin
  T(X)::Bun(X) ⊣ [X::Space]
end

@theory DeRham2Space <: DiffSpaces begin
  @alias ⋀0 = scalars

  ⋀1(X)::Bun(X) ⊣ [X::Space]
  ⋀2(X)::Bun(X) ⊣ [X::Space]

  @alias Ω0(X) := Γ(⋀0(X))
  @alias Ω1(X) := Γ(⋀1(X))
  @alias Ω2(X) := Γ(⋀2(X))

  d(u)::Ω1(X) ⊣ [X::Space, u::Ω0(X)]
  d(u)::Ω2(X) ⊣ [X::Space, u::Ω1(X)]

  (u ∧ v)::Ω0(X) ⊣ [X::Space, u::Ω0(X), v::Ω0(X)]
  (u ∧ v)::Ω1(X) ⊣ [X::Space, u::Ω1(X), v::Ω0(X)]
  (u ∧ v)::Ω1(X) ⊣ [X::Space, u::Ω0(X), v::Ω1(X)]
  (u ∧ v)::Ω2(X) ⊣ [X::Space, u::Ω0(X), v::Ω2(X)]
  (u ∧ v)::Ω2(X) ⊣ [X::Space, u::Ω2(X), v::Ω0(X)]
  (u ∧ v)::Ω2(X) ⊣ [X::Space, u::Ω1(X), v::Ω1(X)]

  ♯(v)::Γ(T(X)) ⊣ [X::Space, v::Ω1(X)]
  ♭(v)::Ω1(X) ⊣ [X::Space, v::Γ(T(X))]

  @alias ⋀°0(X) := scalars(X)

  ⋀°1(X)::Bun(X) ⊣ [X::Space]
  ⋀°2(X)::Bun(X) ⊣ [X::Space]

  @alias Ω°0(X) = Γ(⋀°0(X))
  @alias Ω°1(X) = Γ(⋀°1(X))
  @alias Ω°2(X) = Γ(⋀°2(X))

  d(v)::Ω°0(X) ⊣ [X::Space, v::Ω°1(X)]
  d(v)::Ω°1(X) ⊣ [X::Space, v::Ω°2(X)]

  ⋆(v)::Ω°0(X) ⊣ [X::Space, v::Ω2(X)]
  ⋆(v)::Ω°1(X) ⊣ [X::Space, v::Ω1(X)]
  ⋆(v)::Ω°2(X) ⊣ [X::Space, v::Ω0(X)]

  ⋆(v)::Ω0(X) ⊣ [X::Space, v::Ω°2(X)]
  ⋆(v)::Ω1(X) ⊣ [X::Space, v::Ω°1(X)]
  ⋆(v)::Ω2(X) ⊣ [X::Space, v::Ω°0(X)]
end

end
