module TestModelMacros

using Gatlab, Test

@test ap(IntArith(), ThRig.zero()) == 0
@test ap(IntArith(), ThRig.:(+)(), 4, 5) == 9
@test ap(IntMaxPlus(), ThRig.one()) == 0
@test ap(IntMaxPlus(), ThRig.:(+)(), 4, 5) == 5

end
