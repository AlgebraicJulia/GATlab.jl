# The Road to Dynamical Systems

- [x] Tuple types
- [ ] Symbolic functions
    Data type:

    ```julia
    struct SymbolicFunction
        theory::GAT
        args::TypeScope
        ret::AlgType
        body::AlgTerm
    end
    ```

    Affordances:
    - DSL for writing down functions, composing, etc.
    - A function `Trie{SymbolicFunction} -> SymbolicFunction`, implementing the Trie-algebra structure on morphisms
- [ ] Arenas
    Sketch:
    ```julia
    struct Arena
        in::AlgType
        out::AlgType
    end
    ```

    Affordances:
    - A function `Trie{Arena} -> Arena`, implementing the Trie-algebra structure on objects
- [ ] Multilenses
    Sketch:
    ```julia
    struct MultiLens
        inner_boxes::Trie{Arena}
        outer_box::Arena
        # used for namespacing `params` in composition, must not overlap with `inner_boxes`
        name::Symbol 
        params::AlgType
        # (params, inner_boxes[...].out) -> outer_box.out
        output::SymbolicFunction
        # (params, inner_boxes[...].out, outer_box.in) -> inner_boxes[...].in
        update::SymbolicFunction
    end
    ```

    Affordances:
    - A function `ocompose(l::MultiLens, args::Trie{MultiLens})` implementing the Trie-multicategory structure
- [ ] Systems
    Sketch:
    ```julia
    struct System
        interface::Arena
        state::AlgType
        params::AlgType
        # (params, state) -> interface.out
        output::SymbolicFunction
        # (params, state, interface.in) -> state
        input::SymbolicFunction
    end
    ```

    Affordances:
    - A function `oapply(l::MultiLens, args::Trie{System})` implementing the action of the Trie-multicategory of multilenses on systems.
- [ ] Compilation
