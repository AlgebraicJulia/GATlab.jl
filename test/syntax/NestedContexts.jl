module TestNestedContexts

using Test, Gatlab

nctx = NestedContext()

dctx = DependentContext(
  NestedContext(),
  NestedContext()
)

push!(dctx, SymLit(:dom), Typ(Lvl(1)))
push!(dctx, SymLit(:codom), Typ(Lvl(1)))

bare_hom = DependentContext(
  copy(dctx.context),
  NestedContext()
)

push!(bare_hom, SymLit(:it), Typ(Lvl(2), [Trm(Lvl(1; argument=true)), Trm(Lvl(2; argument=true))]))

push!(dctx, SymLit(:f), bare_hom, [Lvl(1; context=true), Lvl(2; context=true)])

end
