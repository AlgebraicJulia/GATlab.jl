# This lesson covers the internals of Metatheory.jl-style E-Graphs. Let's reuse the heat_equation model on a new roe.
roe = Roe(DEC.ThDEC.Sort);
function heat_equation(roe)
  u = fresh!(roe, PrimalForm(0), :u)
  
  ∂ₜ(u) ≐ Δ(u)

  ([u], [])
end

# We apply the model to the roe and collect its state variables.
(state, _) = heat_equation(roe)

# Recall from the Introduction that an E-Graph is a bipartite graph of ENodes and EClasses. Let's look at the EClasses: 
classes = roe.graph.classes
# The keys are Metatheory Id types which store an Id. The values are EClasses, which are implementations of equivalence classes. Nodes which share the same EClass are considered equivalent.



# The constants in Roe are a dictionary of hashes of functions and constants. Let's extract just the values again: 
vals = collect(values(e.graph.constants))
# The `u` is ::RootVar{Form} and ∂ₜ, ★, d are all functions defined in ThDEC/signature.jl file. 
