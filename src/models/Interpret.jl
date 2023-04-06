module Interpret
export interpret

using ...Syntax
using ...Logic

using ..ModelInterface

function interpret(m::Model, f::KleisliContextMap, xs::Tuple)
  tuple(interpret_term.(Ref(m), f.values, Ref(xs))...)
end

function interpret_term(m::Model, t::Trm, xs::Tuple)
  if is_context(t.head)
    xs[index(t.head)]
  else
    ap(m, Val(Int(index(t.head))), interpret_term.(Ref(m), t.args, Ref(xs))...)
  end
end

end
