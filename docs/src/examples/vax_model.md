```@meta
EditURL = "https://github.com/AlgebraicJulia/Gatlab.jl/blob/main/docs/examples/vax_model.jl"
```

````@example vax_model
module VaxModel

using Gatlab
using ModelingToolkit

vax_production = @lens ThElementary begin
  dom = [C, VP, t] | [dC, dVP, dt]
  codom = [C, VP] | [C_max, α, τ, I]
  #expose = [C,VP]
  expose = begin
    C = C
    VP = VP
  end
  update = begin
    dC = C_max * sigmoid(I * α)
    dVP = τ * C + (-sin(t))
    dt = one
  end
end

sirv = @lens ThElementary begin
  dom = [S, I, R, V] | [dS, dI, dR, dV]
  codom = [S, I, R, V] | [β, γ, v]
  expose = begin
    S = S
    I = I
    R = R
    V = V
  end
  update = begin
    dS = - β * (I * S) + (-v * S)
    dI = β * (I * S) + (-γ * I)
    dR = γ * I
    dV = v * S
  end
end

wiring = @lens ThElementary begin
  dom = [S, I, R, V, C, VP] | [β, γ, v, C_max, α, τ, I]
  codom = [S, I, R, V] | [C_max, α, β, γ, τ]
  expose = begin
    S = S
    I = I
    R = R
    V = V
  end
  update = begin
    β = β
    γ = γ
    v = VP
    C_max = C_max
    α = α
    τ = τ
    I = I
  end
end

composed = Gatlab.compose(mcompose(sirv, vax_production), wiring)

@named sys = ODESystem(composed)

end
````

