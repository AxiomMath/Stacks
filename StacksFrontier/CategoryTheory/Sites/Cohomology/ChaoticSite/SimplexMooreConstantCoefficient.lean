module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SimplexMooreGeneralCoefficients

/-!
# The Moore complex of a constant simplicial object, at arbitrary abelian coefficients

Let `A` be an abelian category and let `Y` be an object of it. The constant simplicial object
`(Functor.const Δᵒᵖ).obj Y` has, as its Moore complex, the alternating constant complex
`Y ←0- Y ←𝟙- Y ←0- ⋯` of `Mathlib.Algebra.Homology.AlternatingConst`, which is exact away from
degree zero; and its colimit over `Δᵒᵖ` is `Y` itself, `Δᵒᵖ` being connected. Put together with
`Stacks.ChaoticSite.SimplexValued.quasiIso_mooreCochainAugmentation_of_isZero`, this says that the
extended Moore complex of a constant simplicial object is a resolution of its value:

`Y(Δ_•) ⟶ Y[0]` is a quasi-isomorphism.

This is the `Δ`-side half of the computation of `Lπ_!` on a *constant* simplicial module, which is
what the third term of the Atiyah triangle of [Stacks, Tag 09DH] asks for; the module-coefficient
half is
`StacksFrontier/CategoryTheory/Sites/Cohomology/Simplicial/DerivedProjectionConstantCoefficient.lean`.
Nothing here is specific to modules: as everywhere in the `GeneralValued`/`SimplexValued`
development, the coefficient category is an arbitrary abelian category.

## Main definitions

* `Stacks.ChaoticSite.SimplexValued.colimConstIso`: **`colim_{Δᵒᵖ} Y = Y`** for the constant
  simplicial object on `Y`.

## Main results

* `Stacks.ChaoticSite.SimplexValued.isConnected_simplexCategory`: `Δ` is connected, `⦋0⦌` being
  terminal in it. With `CategoryTheory.isConnected_op` this gives the connectedness of `Δᵒᵖ` that
  `colimConstIso` rests on.
* `Stacks.ChaoticSite.SimplexValued.isZero_homology_alternatingFaceMapComplex_const_succ`: **the
  Moore complex of a constant simplicial object has no homology in positive degrees.**
* `Stacks.ChaoticSite.SimplexValued.quasiIso_mooreCochainAugmentation_const`: **the extended Moore
  complex of a constant simplicial object is a resolution of its value.**

## Implementation notes

**Where the positive-degree vanishing already appeared.** The same computation is run inside the
proof of
`Stacks.ChaoticSite.SimplexValued.isZero_homology_alternatingFaceMapComplex_freeSimplicial_succ`,
as the local step `hconst`: a free simplicial object is the product of a contractible standard
simplex with a constant simplicial object, and the projection off the contractible factor is a
homology isomorphism, so the vanishing for the free object is deduced from the vanishing for the
constant one. That step is local to that proof and so cannot be cited; it is stated here in its own
right, where the constant simplicial objects — not the free ones — are the objects of interest.

**Why the colimit needs connectedness and not a terminal object.** `⦋0⦌` is terminal in `Δ` and so
*initial* in `Δᵒᵖ`, which says nothing about a colimit over `Δᵒᵖ`. What makes the colimit of a
constant diagram its value is connectedness of the index category, and that is what is proved here
and fed to `CategoryTheory.Limits.isColimitConstCocone`.

## References

* [Stacks Project, Tag 09DH](https://stacks.math.columbia.edu/tag/09DH)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology Simplicial

namespace Stacks.ChaoticSite.SimplexValued

/-! ### `Δ` is connected -/

/-- **`Δ` is connected.** The object `⦋0⦌` is terminal in `Δ` — a monotone map to a one-point
linear order is unique — so every object is joined to `⦋0⦌` by a single morphism, and any two
objects by a zigzag of length two through it. -/
theorem isConnected_simplexCategory : IsConnected SimplexCategory :=
  have : Nonempty SimplexCategory := ⟨⦋0⦌⟩
  zigzag_isConnected fun m n =>
    Relation.ReflTransGen.head (Or.inl ⟨SimplexCategory.const m ⦋0⦌ 0⟩)
      (Relation.ReflTransGen.single (Or.inr ⟨SimplexCategory.const n ⦋0⦌ 0⟩))

/-- **`Δᵒᵖ` is connected**, the opposite of a connected category being connected. -/
theorem isConnected_simplexCategoryOp : IsConnected SimplexCategoryᵒᵖ :=
  have := isConnected_simplexCategory
  isConnected_op

/-! ### The colimit of a constant simplicial object -/

/-- **`colim_{Δᵒᵖ} Y = Y`.** The colimit of the constant simplicial object on `Y` is `Y`, because
`Δᵒᵖ` is connected: the identity cocone on a constant diagram over a connected category is
colimiting (`CategoryTheory.Limits.isColimitConstCocone`). -/
def colimConstIso {A : Type*} [Category* A] [HasColimitsOfShape SimplexCategoryᵒᵖ A] (Y : A) :
    (colim : (SimplexCategoryᵒᵖ ⥤ A) ⥤ A).obj ((Functor.const SimplexCategoryᵒᵖ).obj Y) ≅ Y :=
  haveI := isConnected_simplexCategoryOp
  (colimit.isColimit ((Functor.const SimplexCategoryᵒᵖ).obj Y)).coconePointUniqueUpToIso
    (isColimitConstCocone SimplexCategoryᵒᵖ Y)

/-- The colimit injection into `colim_{Δᵒᵖ} Y = Y` is the identity, in every degree. -/
@[reassoc (attr := simp)]
lemma colimit_ι_colimConstIso_hom {A : Type*} [Category* A]
    [HasColimitsOfShape SimplexCategoryᵒᵖ A] (Y : A) (n : SimplexCategoryᵒᵖ) :
    colimit.ι ((Functor.const SimplexCategoryᵒᵖ).obj Y) n ≫ (colimConstIso Y).hom = 𝟙 Y :=
  have := isConnected_simplexCategoryOp
  (colimit.isColimit ((Functor.const SimplexCategoryᵒᵖ).obj Y)).comp_coconePointUniqueUpToIso_hom
    (isColimitConstCocone SimplexCategoryᵒᵖ Y) n

/-! ### The Moore complex of a constant simplicial object -/

/-- **The Moore complex of a constant simplicial object has no homology in positive degrees.** The
alternating-face-map complex of the constant simplicial object on `Y` is the alternating constant
complex `Y ←0- Y ←𝟙- Y ←0- ⋯` (`AlgebraicTopology.alternatingFaceMapComplexConst`), which is exact
away from degree zero (`ChainComplex.alternatingConst_exactAt`).

This is the input that
`Stacks.ChaoticSite.SimplexValued.quasiIso_mooreCochainAugmentation_of_isZero` asks of the
coefficient category, at a constant simplicial object. -/
theorem isZero_homology_alternatingFaceMapComplex_const_succ {A : Type*} [Category* A] [Abelian A]
    (Y : A) (n : ℕ) :
    IsZero (((alternatingFaceMapComplex A).obj
      ((Functor.const SimplexCategoryᵒᵖ).obj Y)).homology (n + 1)) :=
  IsZero.of_iso
    ((ChainComplex.alternatingConst_exactAt Y (n + 1) (Nat.succ_ne_zero n)).isZero_homology)
    ((HomologicalComplex.homologyFunctor A (ComplexShape.down ℕ) (n + 1)).mapIso
      (alternatingFaceMapComplexConst.app Y))

/-- **The extended Moore complex of a constant simplicial object is a resolution of its value.**
Both inputs of `Stacks.ChaoticSite.GeneralValued.quasiIso_mooreCochainAugmentation` are available:
the positive homology vanishes by
`Stacks.ChaoticSite.SimplexValued.isZero_homology_alternatingFaceMapComplex_const_succ`, and the
cokernel presentation of the colimit injection at `⦋0⦌` is
`Stacks.ChaoticSite.SimplexValued.colimitIotaZeroIsColimit`, which needs no hypothesis.

Combined with `Stacks.ChaoticSite.SimplexValued.colimConstIso`, which identifies the target
`(colim Y)[0]` with `Y[0]`, this says that the Moore complex of a constant simplicial object *is*
its value, in the derived category. -/
theorem quasiIso_mooreCochainAugmentation_const {A : Type*} [Category* A] [Abelian A]
    [HasColimitsOfShape SimplexCategoryᵒᵖ A] (Y : A) :
    QuasiIso ((GeneralValued.mooreCochainAugmentation (𝟭 SimplexCategory)).app
      ((Functor.const SimplexCategoryᵒᵖ).obj Y)) :=
  quasiIso_mooreCochainAugmentation_of_isZero _
    (isZero_homology_alternatingFaceMapComplex_const_succ Y)

end Stacks.ChaoticSite.SimplexValued

end
