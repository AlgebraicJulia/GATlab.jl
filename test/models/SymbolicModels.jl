module TestSymbolicModels

using Gatlab, Test

abstract type CategoryExpr{T} <: GATExpr{T} end

abstract type ObExpr{T} <: CategoryExpr{T} end

abstract type HomExpr{T} <: CategoryExpr{T} end

@symbolic_model FreeCategory{ObExpr, HomExpr} ThCategory begin
end

x, y = FreeCategory.Ob{:generator}([:x], []), FreeCategory.Ob{:generator}([:y], [])
f = FreeCategory.Hom{:generator}([:f], [x, y])

@test x isa ObExpr{:generator}
@test ThCategory.id(x) isa HomExpr{:id}
@test ThCategory.compose(ThCategory.id(x), f) isa HomExpr{:compose}
@test_throws SyntaxDomainError ThCategory.compose(f, f)

end
