# The Road to Dynamical Systems

- [x] Tuple types
- [ ] Symbolic functions
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
    - DSL for writing down functions, composing, etc.
    - A function `tcompose(t::Trie{AlgebraicFunction})::AlgebraicFunction`, implementing the Trie-algebra structure on morphisms
    - Interpret/compile a symbolic function into a real function
    - Serialize symbolic functions
- [ ] Arenas
    Sketch:
    ```julia
    struct Arena
        in::AlgType
        out::AlgType
    end
    ```

    Affordances:
    - A function `tcompose(arena::Trie{Arena})::Arena`, implementing the Trie-algebra structure on objects
- [ ] Multilenses
    Sketch:
    ```julia
    struct MultiLens
        inner_boxes::Trie{Arena}
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
    - A function `ocompose(l::MultiLens, args::Trie{MultiLens})::MultiLens` implementing the Trie-multicategory structure
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
    - A function `oapply(l::MultiLens, args::Trie{System})::System` implementing the action of the Trie-multicategory of multilenses on systems.
- [ ] Compilation
