module TestPresentations

using Test, GATlab, GATlab.Stdlib

presentation_theory(::Presentation{Theory}) where Theory = Theory

# Presentation
##############


@symbolic_model FreeCategory{GATExpr, GATExpr} ThCategory begin
  compose(f::Hom, g::Hom) = associate(new(f,g))
end
using .ThCategory
A, B, C = Ob.(Ref(FreeCategory.Ob),[:A, :B, :C])
f, g, h = Hom(:f, A, B), Hom(:g, B, C), Hom(:h, A, C)

# Generators
pres = Presentation(FreeCategory)
@test presentation_theory(pres) == ThCategory.Meta.T
@test !has_generator(pres, :A)
add_generator!(pres, A)
@test generators(pres) == [A]
@test generator(pres, :A) == A
@test has_generator(pres, :A)
add_generator!(pres, B)
@test generators(pres) == [A, B]
@test_throws Exception add_generator!(pres, A)
@test pres[:A] == A
@test pres[[:A,:B]] == [A, B]
@test generator_index(pres, :B) == 2
@test generator_index(pres, B) == 2

add_generators!(pres, (f,g))
@test generators(pres) == [A, B, f, g]
@test generators(pres, :Ob) == [A, B]
@test generators(pres, :Hom) == [f, g]
@test generators(pres, FreeCategory.Ob) == [A, B]
@test generators(pres, FreeCategory.Hom) == [f, g]

# Equations
add_equation!(pres, compose(f,g), h)
@test length(equations(pres)) == 1

f′, g′ = Hom(:f′, A, B), Hom(:g′, B, C)
add_generators!(pres, [f′, g′])
add_equations!(pres, [f => f′, g => g′])
@test length(equations(pres)) == 3

# Presentation macro
####################

@present Company(FreeCategory) begin
  # Primitive concepts.
  Employee::Ob
  Department::Ob
  Str::Ob
  
  first_name::Hom(Employee, Str)
  last_name::Hom(Employee, Str)
  manager::Hom(Employee, Employee)
  works_in::Hom(Employee, Department)
  secretary::Hom(Department, Employee)
  
  # Defined concepts.
  second_level_manager := compose(manager, manager)
  third_level_manager := compose(manager, compose(manager, manager))
  
  # Managers work in the same department as their employees.
  compose(manager, works_in) == works_in
  # The secretary of a department works in that department.
  compose(secretary, works_in) == id(Department)
end

# Check type parameter.
@test presentation_theory(Company) == ThCategory.Meta.T

# Check generators.
Employee, Department, Str = Ob.(Ref(FreeCategory.Ob),[:Employee, :Department, :Str])
@test generators(Company) == [
  Employee,
  Department,
  Str,
  Hom(:first_name, Employee, Str),
  Hom(:last_name, Employee, Str),
  Hom(:manager, Employee, Employee),
  Hom(:works_in, Employee, Department),
  Hom(:secretary, Department, Employee),
  Hom(:second_level_manager, Employee, Employee),
  Hom(:third_level_manager, Employee, Employee),
]

# Check equations.
manager = Hom(:manager, Employee, Employee)
works_in = Hom(:works_in, Employee, Department)
secretary = Hom(:secretary, Department, Employee)
@test equations(Company) == [
  Hom(:second_level_manager, Employee, Employee) => compose(manager, manager),
  Hom(:third_level_manager, Employee, Employee) => compose(manager, compose(manager, manager)),
  compose(manager, works_in) => works_in,
  compose(secretary, works_in) => id(Department),
]

# Generators with compound type arguments.

using .ThStrictMonCat
@symbolic_model FreeMC{GATExpr, GATExpr} ThStrictMonCat begin
  compose(f::Hom, g::Hom) = associate(new(f,g))
end

@present C(FreeMC) begin
  A::Ob
  B::Ob
  f::Hom(mcompose(A,B),mcompose(B,A))
  scalar::Hom(munit(),munit()) # Nullary case.
end
A, B = Ob(FreeMC.Ob, :A), Ob(FreeMC.Ob, :B)
I = munit(FreeMC.Ob)
@test generator(C, :f) == Hom(:f, mcompose(A,B), mcompose(B,A))
@test generator(C, :scalar) == Hom(:scalar, I, I)

# Inheritance.
@present SchSet(FreeCategory) begin
  X::Ob
end
@present SchDDS <: SchSet begin
  Φ::Hom(X,X)
end
X = Ob(FreeCategory.Ob, :X)
Φ = Hom(:Φ, X, X)
@test generators(SchDDS, :Ob) == [X]
@test generators(SchDDS, :Hom) == [Φ]

# Abbreviated syntax.
@present SchGraph(FreeCategory) begin
  V::Ob
  E::Ob
  src::Hom(E,V)
  tgt::Hom(E,V)
end
@present SchGraph′(FreeCategory) begin
  (V, E)::Ob
  (src, tgt)::Hom(E,V)
end
@test SchGraph == SchGraph′

# Serialization
###############

to_json(expr) = to_json_sexpr(Company, expr)
from_json(sexpr) = parse_json_sexpr(Company, FreeCategory, sexpr)

# To JSON
to_json(generator(Company, :Employee)) == "Employee"
to_json(generator(Company, :manager)) == "manager"
to_json(compose(generator(Company, :manager), generator(Company, :manager))) ==
  ["compose", "manager", "manager"]

# From JSON
@test from_json("Employee") == generator(Company, :Employee)
@test from_json("manager") == generator(Company, :manager)
@test from_json(["compose", "manager", "manager"]) ==
  compose(generator(Company, :manager), generator(Company, :manager))

end
