module

public import StacksCore.Topology.NowhereDense.Local
public import StacksCore.Topology.NowhereDense.OpenMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.NowhereDense
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.FiniteFactorization

/-!
# Images of nowhere dense subsets under quasi-finite morphisms

A quasi-finite morphism of schemes carries closed nowhere dense subsets of its source to nowhere
dense subsets of its target. This extends the finite case, Tag 03HX, to which the argument
reduces.

## Main results

* `AlgebraicGeometry.isNowhereDense_image_of_quasiFinite`: the image of a closed nowhere dense
  subset under a quasi-finite morphism of schemes is nowhere dense.

## Implementation notes

Quasi-finiteness is represented, as in
`StacksFrontier/AlgebraicGeometry/Morphisms/QuasiFinite/Defs.lean`, by the typeclasses
`AlgebraicGeometry.LocallyOfFiniteType`, `AlgebraicGeometry.LocallyQuasiFinite` and
`AlgebraicGeometry.QuasiCompact`; nowhere denseness is Mathlib's `IsNowhereDense`.

Nowhere denseness is local on an open cover of the target, by `nowhere_dense_local`, so the
target may be taken affine. Over an affine target the preimage is quasi-compact, hence a finite
union of affine opens, and nowhere denseness of a finite union is `IsNowhereDense.iUnion`; this
reduces the statement to a quasi-finite morphism between affine schemes. There Tag 03GU,
`AlgebraicGeometry.exists_isOpenImmersion_isFinite_factorization`, factors the morphism as an
open immersion `j` followed by a finite morphism `π`, and the image of the subset is contained in
the image under `π` of the closure of its image under `j`. That closure is closed and nowhere
dense, an open immersion being inducing, so the finite case Tag 03HX applies to it. Closedness of
the subset is needed only for the passage to affine opens of the source, where it feeds
`isClosedNowhereDense_preimage_of_isOpenMap`.

## References

* [Stacks Project, Tag 03J2](https://stacks.math.columbia.edu/tag/03J2)
* [Stacks Project, Tag 03HX](https://stacks.math.columbia.edu/tag/03HX)
* [Stacks Project, Tag 03GU](https://stacks.math.columbia.edu/tag/03GU)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- The image of a nowhere dense subset under a quasi-finite morphism of affine schemes is
nowhere dense. -/
private theorem isNowhereDense_image_of_quasiFinite_of_isAffine
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsAffine Y] [IsAffine X]
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (T : Set Y) (hT : IsNowhereDense T) :
    IsNowhereDense (f.base '' T) := by
  obtain ⟨Z, _, j, π, _, _, hfactor⟩ := exists_isOpenImmersion_isFinite_factorization f
  apply (Stacks.Morphisms.isNowhereDense_image_of_isFinite π isClosed_closure
    (j.isOpenEmbedding.isNowhereDense_image hT).closure).mono
  rintro _ ⟨y, hy, rfl⟩
  rw [← hfactor, Scheme.Hom.comp_apply]
  exact ⟨j y, subset_closure (Set.mem_image_of_mem j hy), rfl⟩

/-- The image of a closed nowhere dense subset under a quasi-finite morphism of schemes meets an
affine open of the target in a nowhere dense subset of that open. -/
private theorem isNowhereDense_image_of_quasiFinite_affineOpen
    {Y X : Scheme.{u}} (f : Y ⟶ X) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [QuasiCompact f] (U : X.affineOpens) (T : Set Y)
    (hT_closed : IsClosed T) (hT : IsNowhereDense T) :
    IsNowhereDense ((Subtype.val : U.1 → X) ⁻¹' (f.base '' T)) := by
  classical
  obtain ⟨s, hs, hW⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
      ⟨f.isCompact_preimage U.2.isCompact, (f ⁻¹ᵁ (U : X.Opens)).2⟩
  let I := {V : Y.affineOpens // V ∈ s}
  have hle (V : I) : V.1.1 ≤ f ⁻¹ᵁ (U : X.Opens) := by
    show (V.1.1 : Set Y) ⊆ f ⁻¹' (U : Set X)
    intro y hy
    show y ∈ ((f ⁻¹ᵁ (U : X.Opens)) : Set Y)
    rw [hW]
    exact Set.mem_iUnion.2 ⟨V.1, Set.mem_iUnion.2 ⟨V.2, hy⟩⟩
  let A : I → Set (↥(U.1 : Set X)) := fun V =>
    (f.resLE U V.1.1 (hle V)).base '' ((Subtype.val : (V.1.1 : Set Y) → Y) ⁻¹' T)
  have hcover : ((Subtype.val : U.1 → X) ⁻¹' (f.base '' T)) = ⋃ V : I, A V := by
    ext x
    constructor
    · rintro ⟨y, hyT, hzy⟩
      have hyW : y ∈ ((f ⁻¹ᵁ (U : X.Opens)) : Set Y) := by simp [hzy]
      rw [hW, Set.mem_iUnion₂] at hyW
      obtain ⟨V, hVs, hyV⟩ := hyW
      exact Set.mem_iUnion.2 ⟨⟨V, hVs⟩, ⟨y, hyV⟩, hyT,
        Subtype.ext (by simpa only [Scheme.Hom.coe_resLE_apply] using hzy)⟩
    · intro hx
      obtain ⟨V, ⟨y, hyT, hEq⟩⟩ := Set.mem_iUnion.mp hx
      exact ⟨y.1, hyT, (Scheme.Hom.coe_resLE_apply (f := f) (U := U) (V := V.1.1)
        (e := hle V) y).symm.trans (congrArg Subtype.val hEq)⟩
  rw [hcover]
  have : Finite I := hs.to_subtype
  refine IsNowhereDense.iUnion fun V => ?_
  dsimp only [A]
  exact isNowhereDense_image_of_quasiFinite_of_isAffine (f.resLE U V.1.1 (hle V)) _
    (isClosedNowhereDense_preimage_of_isOpenMap V.1.1.ι
      V.1.1.ι.isOpenEmbedding.continuous V.1.1.ι.isOpenEmbedding.isOpenMap T
      hT_closed hT).2

/-- **Stacks Project, Tag 03J2.** The image of a closed nowhere dense subset under a quasi-finite
morphism of schemes is nowhere dense. -/
@[stacks 03J2]
theorem isNowhereDense_image_of_quasiFinite {Y X : Scheme.{u}} (f : Y ⟶ X)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [QuasiCompact f] (T : Set Y)
    (hT_closed : IsClosed T) (hT_nowhereDense : IsNowhereDense T) :
    IsNowhereDense (f.base '' T) :=
  nowhere_dense_local (fun U : X.affineOpens => (U.1 : Set X)) (fun U => U.1.2)
    (by
      ext x
      simpa using (TopologicalSpace.Opens.mem_iSup.mp (show x ∈ (⨆ U : X.affineOpens,
        (U : X.Opens)) by rw [iSup_affineOpens_eq_top X]; trivial)))
    (f.base '' T)
    (fun U => isNowhereDense_image_of_quasiFinite_affineOpen f U T hT_closed hT_nowhereDense)

end AlgebraicGeometry

end
