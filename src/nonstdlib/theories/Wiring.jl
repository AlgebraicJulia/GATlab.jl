"""Wires can split and merge"""
@theory NestedWD begin
  Diagram::TYPE
  Box(d::Diagram)::TYPE
  IP(b)::TYPE ⊣ [d::Diagram, b::Box(d)] # InPort 
  OP(b)::TYPE ⊣ [d::Diagram, b::Box(d)] # OutPort
  Wire(op, ip)::TYPE ⊣ [d::Diagram, (b,b′)::Box(d), op::OP(b),ip::IP(b′)]
  OIP(d::Diagram)::TYPE # OuterInPort
  OOP(d::Diagram)::TYPE # OuterOutPort
  IWire(oip,ip)::TYPE ⊣ [d::Diagram, b::Box(d), oip::OIP(d), ip::IP(b)]
  OWire(op,oop)::TYPE ⊣ [d::Diagram, b::Box(d), oop::OOP(d), op::OP(b)]

  # Diagrams form a poset with a distinguished top element
  ⊤::Diagram 
  Leq(x::Diagram, y::Diagram)::TYPE # immediate or distant descendent
  @op (≤) := Leq
  refl(p)::(p ≤ p) ⊣ [p::Diagram]
  trans(f::(p ≤ q),g::(q ≤ r))::(p ≤ r)  ⊣ [(p,q,r)::Diagram]
  top(d::Diagram)::(d ≤ ⊤())
  irrev := f == g ⊣ [(p,q)::Diagram, (f, g)::(p ≤ q)]
  poset := x == y ⊣ [(x,y)::Diagram, f::(x ≤ y), g::(y ≤ x)]

  # Nesting associates a box to another diagram
  nest(b)::Diagram ⊣ [d::Diagram, b::Box(d)]

  # Nesting respects the ≤ relation
  nest_leq(b)::(nest(b) ≤ d) ⊣ [d::Diagram, b::Box(d)]

  # There (only) one box which refers to its own diagram
  # TODO 
  
  # Iso between inports and outer inports for any nesting
  ip_oip(i)::OIP(nest(b)) ⊣ [d::Diagram, b::Box(d), i::IP(b)]
  oip_ip(i)::IP(b)        ⊣ [d::Diagram, b::Box(d), i::OIP(nest(b))]

  oip_ip(ip_oip(i)) == i ⊣ [d::Diagram, b::Box(d), i::IP(b)]
  ip_oip(oip_ip(i)) == i ⊣ [d::Diagram, b::Box(d), i::OIP(nest(b))]
  # Likewise for outports and outer outports for any nesting
end