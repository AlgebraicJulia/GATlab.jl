module TestCompactify

using Gatlab, Test

@test most_recent_backref(ThSet, ThGraph) == 1

end
