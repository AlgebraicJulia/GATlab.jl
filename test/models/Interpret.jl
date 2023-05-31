module TestInterpret

using Test, Gatlab

Γ = @context ThRig [a,b,c]
t = @term ThRig Γ (a * (b + (c + one)))
vals = [3, 2, 1]

@test interpret(IntArith(), t, vals) == 12
@test interpret(IntMaxPlus(), t, vals) == 5

end
