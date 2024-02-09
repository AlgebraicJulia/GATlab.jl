module TestPackages

using GATlab.Syntax.Packages
using Test

p1 = namespace(:a => singleton(1), :b => namespace(:a => singleton(2), :c => singleton(3)))

@test p1.a isa Package
@test_throws Packages.PackageDerefError p1[]
@test p1.a[] == 1
@test p1.b.a isa Package
@test p1.b.a[] == 2

@test sprint(show, p1.a) == "singleton(1)::Package{Int64}"
@test sprint(show, p1.b) == "Package{Int64}\n├─ :a ⇒ 2\n└─ :c ⇒ 3\n"

@test ■ == PACKAGE_ROOT
@test ■.a isa PackageVar
@test ■.a.b isa PackageVar
@test_throws Packages.PackageVarNotFound p1[■]
@test p1[■.a] == 1
@test p1[■.b.c] == 3

end
