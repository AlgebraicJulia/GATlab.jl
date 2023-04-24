module TestSystems

sirv = @system ThElementary begin
  @state [s, i, r, v]
  @params [β, γ, v]
  :d(s) = - β * (s * i)
  :d(i) = β * (s * i) + (-γ * i)
  :d(i) = -γ * i
end

vax_production = @system ThElementary begin
  @state [C, VP, t]
  @params [C_max, α, τ, I]
  :d(C) = C_max * sigmoid(I * α)
  :d(VP) = τ * C + (-sin(t))
  :d(t) = one
end

composed = @compose [sir, vax_production] begin
  @params [C_max, α, τ, β, γ]
  @link α, τ, β, γ, C_max, I = i, v = VP
  @output s, i, r, v
end


end
