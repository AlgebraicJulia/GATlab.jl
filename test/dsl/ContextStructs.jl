module TestContextStructs

@context_struct ThCategory SimpleArena begin
  pos::Ob
  dir::Ob
end

# =>

module SimpleArena

struct T{Ob, Hom}
  pos::Ob
  dir::Ob
end

const spec = Dict(
  :pos => ThCategory.Ob
  :dir => ThCategory.Ob
)

end

# Or

struct SimpleArena{Ob, Hom}
  pos::Ob
  dir::Ob
end

function spec(::Type{SimpleArena})
  # ...
end



@context_struct ThCartesianCategory SimpleLens[dom::SimpleArena, codom::SimpleArena] begin
  expose::Hom(dom.pos, codom.pos)
  update::Hom(dom.pos × codom.dir, dom.dir)
end

@context_struct ThCartesianCategory FullLens begin
  dom::SimpleArena
  codom::SimpleArena
  f::SimpleLens{dom, codom}
end



end
