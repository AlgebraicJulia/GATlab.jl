module Plotting

using CairoMakie

function save_dynamics(soln, timespan, save_file_name)
  time = Observable(0.0)
  h = @lift(soln($time))
  f = Figure()
  ax = CairoMakie.Axis(f[1,1], title = @lift("Heat at time $($time)"))
  gmsh = mesh!(ax, rect, color=h, colormap=:jet,
               colorrange=extrema(soln(timespan)))
  Colorbar(f[1,2], gmsh)
  timestamps = range(0, timespan, step=5.0)
  record(f, save_file_name, timestamps; framerate = 15) do t
    time[] = t
  end
end
export save_dynamics

end
