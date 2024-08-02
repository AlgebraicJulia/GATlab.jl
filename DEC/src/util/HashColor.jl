module HashColor
export hashcolor, hashcrayon

using Colors
using Random
using Crayons

randunif(rng, range) = rand(rng) * (range[2] - range[1]) + range[1]

"""
Returns a Color generated randomly by hashing `x`.

This uses the LCHuv space to sample uniformly across the human visual spectrum.
"""
function hashcolor(x; lightnessrange=(0.,100.), chromarange=(0.,100.), huerange=(0.,360.))
  h = hash(x)
  rng = MersenneTwister(h)
  l = randunif(rng, lightnessrange)
  c = randunif(rng, chromarange)
  h = randunif(rng, huerange)
  LCHuv{Float64}(l, c, h)
end

"""
Returns a Crayon with foreground color given by `hashcolor`
"""
function hashcrayon(x; lightnessrange=(0.,100.), chromarange=(0.,100.), huerange=(0.,360.))
  c = hashcolor(x; lightnessrange, chromarange, huerange)
  Crayon(foreground=RGB24(RGB{Float64}(c)).color)
end

end
