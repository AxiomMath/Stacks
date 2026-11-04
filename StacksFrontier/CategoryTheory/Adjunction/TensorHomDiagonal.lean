module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The tensor–Hom diagonal of an adjunction

Let `T : C ⥤ C ⥤ C` be a bifunctor, thought of as a tensor product, let `G` be an object of `C`
and let `adj : T(G, -) ⊣ H` be an adjunction, so that `H` plays the role of the internal Hom out
of `G`. For objects `K` and `L` there is then a canonical morphism

`T(K, H L) ⟶ H (T(K, L))`,

namely the transpose under `adj` of

`T(G, T(K, H L)) ⟶ T(K, T(G, H L)) ⟶ T(K, L)`,

whose second step is `T(K, -)` applied to the counit of `adj` — the evaluation morphism — and
whose first step is the interchange that moves `G` past `K`. In a braided monoidal category that
interchange is the associator, the braiding and the associator again; here it is taken as an
argument, so that the construction is available in a category with no monoidal structure and so
that a caller may supply whichever interchange its development has.

This is the shape in which [Stacks, Tag 0BYS] describes its diagonal

`K ⊗^𝐋_𝒪 R ℰom(M, L) ⟶ R ℰom(M, K ⊗^𝐋_𝒪 L)`,

and in which [Stacks, Tag 0ATK] part (3) is proved: *the* morphism of that type determined by
the adjunction, rather than a morphism constructed from chosen complex representatives.

## Main definitions

* `CategoryTheory.Adjunction.tensorHomDiagonal`: the morphism.

## Main results

* `CategoryTheory.Adjunction.tensorHomDiagonal_mate`: the adjunction equation characterizing it
  — pushing it into `T(G, -)` and composing with the counit gives the interchange followed by
  `T(K, -)` of the counit.
* `CategoryTheory.Adjunction.eq_tensorHomDiagonal`: that equation determines it, so nothing else
  of its type satisfies the characterization; in particular neither the zero morphism nor the
  negative of the diagonal does.
* `CategoryTheory.Adjunction.tensorHomDiagonal_natural_right`: functoriality in `L`, from
  functoriality of the interchange in `L`.

## Implementation notes

The interchange is an argument of the definition rather than data bundled with `T`, and no
property of it is assumed: the definition, the adjunction equation and the uniqueness hold for
an arbitrary morphism `T(G, T(K, H L)) ⟶ T(K, T(G, H L))`, since they are the statement that
`tensorHomDiagonal` is the transpose of a given morphism. Only the functoriality below uses
anything about it, and what it uses is stated as a hypothesis.

Everything is in a bare category-theoretic context on purpose. A caller whose category is the
derived category of sheaves of modules on a ringed site pays the `isDefEq` cost of each rewrite
in these proofs at objects large enough that the default heartbeat budget does not cover them;
done here, over an abstract bifunctor, the same rewrites are free.

This generalizes the construction of the tensor–Hom strength of a closed monoidal category to a
setting with no monoidal structure, which is what the derived category of a ringed site is in
this development: the commutativity constraint and the associativity constraint of
[Stacks, Tag 0FPT] are available there one object at a time, but not their coherence.

## References

* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

universe v u

namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C] {T : C ⥤ C ⥤ C} {H : C ⥤ C} {G : C}

/-- **The tensor–Hom diagonal of an adjunction.** For `adj : T(G, -) ⊣ H` and an interchange
morphism `ι : T(G, T(K, H L)) ⟶ T(K, T(G, H L))`, the transpose under `adj` of `ι` followed by
`T(K, -)` of the counit of `adj`:

`T(K, H L) ⟶ H (T(K, L))`.

With `T` the derived tensor product, `H` the derived internal Hom out of `G` and the counit the
evaluation morphism, this is the diagonal of [Stacks, Tag 0BYS]. -/
def tensorHomDiagonal (adj : T.obj G ⊣ H) {K L : C}
    (ι : (T.obj G).obj ((T.obj K).obj (H.obj L)) ⟶ (T.obj K).obj ((T.obj G).obj (H.obj L))) :
    (T.obj K).obj (H.obj L) ⟶ H.obj ((T.obj K).obj L) :=
  adj.homEquiv _ _ (ι ≫ (T.obj K).map (adj.counit.app L))

/-- **The adjunction equation characterizing the tensor–Hom diagonal.** Applying `T(G, -)` to it
and composing with the counit gives back the interchange followed by `T(K, -)` of the counit.
This is what "the transpose of" means. -/
theorem tensorHomDiagonal_mate (adj : T.obj G ⊣ H) {K L : C}
    (ι : (T.obj G).obj ((T.obj K).obj (H.obj L)) ⟶ (T.obj K).obj ((T.obj G).obj (H.obj L))) :
    (T.obj G).map (tensorHomDiagonal adj ι) ≫ adj.counit.app ((T.obj K).obj L) =
      ι ≫ (T.obj K).map (adj.counit.app L) :=
  (adj.homEquiv_counit _ _ _).symm.trans ((adj.homEquiv _ _).symm_apply_apply _)

/-- **The adjunction equation determines the tensor–Hom diagonal.** No other morphism of its type
satisfies the characterization of `tensorHomDiagonal_mate`. -/
theorem eq_tensorHomDiagonal (adj : T.obj G ⊣ H) {K L : C}
    (ι : (T.obj G).obj ((T.obj K).obj (H.obj L)) ⟶ (T.obj K).obj ((T.obj G).obj (H.obj L)))
    {φ : (T.obj K).obj (H.obj L) ⟶ H.obj ((T.obj K).obj L)}
    (hφ : (T.obj G).map φ ≫ adj.counit.app ((T.obj K).obj L) =
      ι ≫ (T.obj K).map (adj.counit.app L)) :
    φ = tensorHomDiagonal adj ι :=
  (adj.homEquiv _ _).symm_apply_eq.mp ((adj.homEquiv_counit _ _ φ).trans hφ)

/-- A morphism of the type of the tensor–Hom diagonal is that diagonal exactly when it satisfies
the adjunction equation. -/
theorem eq_tensorHomDiagonal_iff (adj : T.obj G ⊣ H) {K L : C}
    (ι : (T.obj G).obj ((T.obj K).obj (H.obj L)) ⟶ (T.obj K).obj ((T.obj G).obj (H.obj L)))
    (φ : (T.obj K).obj (H.obj L) ⟶ H.obj ((T.obj K).obj L)) :
    φ = tensorHomDiagonal adj ι ↔
      (T.obj G).map φ ≫ adj.counit.app ((T.obj K).obj L) =
        ι ≫ (T.obj K).map (adj.counit.app L) :=
  ⟨fun h => h ▸ tensorHomDiagonal_mate adj ι, eq_tensorHomDiagonal adj ι⟩

/-- **The tensor–Hom diagonal depends on the adjunction only through its counit.** Two
adjunctions `T(G, -) ⊣ H` with the same counit have the same diagonal, for every interchange.

An adjunction is data and not a property, so two adjunctions on one pair of functors agree only
when their units do; but the diagonal is characterized by `eq_tensorHomDiagonal`, whose equation
mentions the counit alone. So comparing two diagonals built from two such adjunctions is
comparing two evaluation morphisms, and the units need not be compared separately. -/
theorem tensorHomDiagonal_eq_of_counit_eq (adj adj' : T.obj G ⊣ H)
    (h : adj.counit = adj'.counit) {K L : C}
    (ι : (T.obj G).obj ((T.obj K).obj (H.obj L)) ⟶ (T.obj K).obj ((T.obj G).obj (H.obj L))) :
    tensorHomDiagonal adj ι = tensorHomDiagonal adj' ι :=
  eq_tensorHomDiagonal adj' ι (h ▸ tensorHomDiagonal_mate adj ι)

/-- **Functoriality of the tensor–Hom diagonal in the target of the internal Hom.** If the two
interchanges are compatible with `g : L ⟶ L'`, then so are the two diagonals. -/
theorem tensorHomDiagonal_natural_right (adj : T.obj G ⊣ H) {K L L' : C} (g : L ⟶ L')
    (ι : (T.obj G).obj ((T.obj K).obj (H.obj L)) ⟶ (T.obj K).obj ((T.obj G).obj (H.obj L)))
    (ι' : (T.obj G).obj ((T.obj K).obj (H.obj L')) ⟶ (T.obj K).obj ((T.obj G).obj (H.obj L')))
    (hι : (T.obj G).map ((T.obj K).map (H.map g)) ≫ ι' =
      ι ≫ (T.obj K).map ((T.obj G).map (H.map g))) :
    (T.obj K).map (H.map g) ≫ tensorHomDiagonal adj ι' =
      tensorHomDiagonal adj ι ≫ H.map ((T.obj K).map g) := by
  have key : (T.obj G).map ((T.obj K).map (H.map g)) ≫ ι' ≫ (T.obj K).map (adj.counit.app L') =
      (ι ≫ (T.obj K).map (adj.counit.app L)) ≫ (T.obj K).map g := by
    rw [← Category.assoc, hι, Category.assoc, ← Functor.map_comp, Category.assoc,
      ← Functor.map_comp]
    exact congrArg _ (congrArg _ (adj.counit.naturality g))
  dsimp only [tensorHomDiagonal]
  rw [← adj.homEquiv_naturality_left, ← adj.homEquiv_naturality_right, key]

end CategoryTheory.Adjunction

end
