# The Road to Dynamical Systems

## Basic steps

- [x] Tuple types
- [-] Symbolic functions
    Data type:

    ```julia
    struct AlgebraicFunction
        theory::GAT
        args::TypeScope
        ret::AlgType
        body::AlgTerm
    end
    ```

    Affordances:
    - [x] DSL for writing down functions, composing, etc.
    - [ ] A function `tcompose(t::Dtry{AlgebraicFunction})::AlgebraicFunction`, implementing the Dtry-algebra structure on morphisms
    - [ ] Interpret/compile a symbolic function into a real function
    - [ ] Serialize symbolic functions
- [ ] Compilation
- [ ] Serialization

## Lens-based dynamical systems

- [ ] Arenas
    Sketch:
    ```julia
    struct Arena
        in::AlgType
        out::AlgType
    end
    ```

    Affordances:
    - A function `tcompose(arena::Dtry{Arena})::Arena`, implementing the Dtry-algebra structure on objects
- [ ] Multilenses
    Sketch:
    ```julia
    struct MultiLens
        inner_boxes::Dtry{Arena}
        outer_box::Arena
        # used for namespacing `params` in composition, must not overlap with `inner_boxes`
        name::Symbol 
        params::AlgType
        # (params, tcompose(inner_boxes[...].out)) -> outer_box.out
        output::AlgebraicFunction
        # (params, tcompose(inner_boxes[...].out), outer_box.in) -> tcompose(inner_boxes[...].in)
        update::AlgebraicFunction
    end
    ```

    Affordances:
    - A function `ocompose(l::MultiLens, args::Dtry{MultiLens})::MultiLens` implementing the Dtry-multicategory structure
- [ ] Systems
    Sketch:
    ```julia
    struct System
        interface::Arena
        state::AlgType
        params::AlgType
        # (params, state) -> interface.out
        output::AlgebraicFunction
        # (params, state, interface.in) -> state
        input::AlgebraicFunction
    end
    ```

    Affordances:
    - A function `oapply(l::MultiLens, args::Dtry{System})::System` implementing the action of the Dtry-multicategory of multilenses on systems.

## Resource sharers

- [ ] Interfaces
- [ ] Rhizomes (epi-mono uwds)
    ```julia
    struct VariableType
        type::AlgType
        exposed::Bool
    end

    struct Rhizome
        boxes::Dtry{Interface}
        junctions::Dtry{VariableType}
        mapping::Dict{DtryVar, DtryVar}
    end
    ```

    Affordances:
    - `ocompose(r::Rhizome, rs::Dtry{Rhizome})::Rhizome`

    In `ocompose`, the names of the junctions in the top-level rhizome dominate.
- [ ] Systems
    ```julia
    struct ResourceSharer
        variables::Dtry{VariableType}
        params::AlgType
        output::AlgType
        # (params, state) -> state
        update::AlgebraicFunction
        # (params, state) -> output
        readout::AlgebraicFunction
    end
    ```

    Affordances:
    - `oapply(r::Rhizome, sharers::Dtry{ResourceSharer})::ResourceSharer`

    In `oapply`, variables get renamed to the junctions that they are attached to.
