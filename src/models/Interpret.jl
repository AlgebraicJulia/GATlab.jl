module Interpret
export interpret

using ..ModelInterface
using ...Syntax

function interpret(m::Model, t::Trm, fvs::Vector)
  if is_context(t.head)
    fvs[index(t.head)]
  else
    ap(m, AnonTrmTag{index(t.head)}(), interpret.(Ref(m), t.args, Ref(fvs))...)
  end
end

end
