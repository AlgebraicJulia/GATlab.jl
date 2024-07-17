module TestComputeGraphs
import Base: *

using GATlab

@theory ThSmGroup begin
    default::TYPE
    ((a::default) * (b::default))::default
end

cg = ComputeGraph{Tuple{TypedVar{default}}}(ThSmGroup.Meta.theory, Node[])

t1 = add_var!(cg, default)
t2 = add_var!(cg, default)

t3 = @withmodel cg (*,) begin
  t1 * t2
end

end