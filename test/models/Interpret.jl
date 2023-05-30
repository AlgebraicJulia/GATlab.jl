module TestInterpret

using Test, Gatlab

Γ = @context ThRig.Th [a,b,c]
t = @term ThRig.Th Γ (a * (b + (c + one)))
vals = [3, 2, 1]

@test interpret(IntArith(), t, vals) == 12
@test interpret(IntMaxPlus(), t, vals) == 5

end
