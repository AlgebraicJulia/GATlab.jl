module TestSystems

sir = @system ThRing [s,i,r] [β, γ] begin
  @d(s) = - β * (s * i)
  @d(i) = β * (s * i) + (-γ * i)
  @d(i) = -γ * i
end

end
