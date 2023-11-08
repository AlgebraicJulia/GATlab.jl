@theory Module begin
  using ThRing: default as Scalar
  using ThAdditiveAbelianGroup: default as Vector
  α ⋅ v :: Vector ⊣ [α::Scalar, v::Vector]
  # ... axioms
end

@theory ModuleHom begin
  using Module: Vector as DomVector
  using Module: Vector as CodomVector

  ap(x::DomVector)::CodomVector
  ap(x + y) == ap(x) + ap(y) ⊣ [x::DomVector, y::DomVector]
  ap(α ⋅ x) == α ⋅ ap(x) ⊣ [x::DomVector]
end

@theory CoChains begin
  using Module: Vector as Form0
  using Module: Vector as Form1
  using Module: Vector as Form2

  using ModuleHom: ap as d, DomVector as Form0, CodomVector as Form1
  using ModuleHom: ap as d, DomVector as Form1, CodomVector as Form2

  d(d(x)) == zero::Form2 ⊣ [x::Form0]
end

@theory Chains begin
  using CoChains: Form0 as Chain2, Form1 as Chain1, Form2 as Chain0, d as δ
end

@theory EC begin
  using CoChains
  using Chains
  
  ♯(x::Chain0)::Form2
end
