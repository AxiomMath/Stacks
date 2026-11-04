module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Transporting an equalizer back along a fully faithful contravariant functor

Let `F : Cᵒᵖ ⥤ D` be a fully faithful contravariant functor and let `a, b : Y ⟶ Z` be two
morphisms of `C`. A morphism `π : Z ⟶ T` of `C` becomes a morphism `F π : F T ⟶ F Z` of `D`
which equalizes `F a` and `F b` as soon as `π` coequalizes `a` and `b`, and conversely by
faithfulness. This file records that, under those circumstances, `π` is the coequalizer of `a`
and `b` exactly when `F π` is the equalizer of `F a` and `F b`.

Only the direction that is needed is proved: an equalizer upstairs produces a coequalizer
downstairs. It is the step that turns a computation of equalizers of quasi-coherent algebras
into a computation of coequalizers of schemes affine over the base, under the anti-equivalence
of Stacks Tag 01SA.

## Main definitions

* `Stacks.FundamentalGroup.forkOfCofork` — the fork obtained by applying `F` to a cofork.

## Main results

* `Stacks.FundamentalGroup.isColimitCoforkOfIsLimitFork` — if the image under `F` of a cofork
  on `a, b` is an equalizer of `F a` and `F b`, then the cofork is a coequalizer of `a` and `b`.

## Implementation notes

The factorisation of a cofork `s` through the coequalizer is the preimage under `F` of the
factorisation of `forkOfCofork F s` through the equalizer; the two cofork identities are then
`F.map_injective` applied to the corresponding fork identities, after the contravariance
rewrite `(a ≫ π).op = π.op ≫ a.op`.

## References

* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂

namespace Stacks.FundamentalGroup

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The image under a contravariant functor of a relation `a ≫ π = b ≫ π`. -/
theorem map_op_comp_eq_of_comp_eq (F : Cᵒᵖ ⥤ D) {Y Z T : C} {a b : Y ⟶ Z} {π : Z ⟶ T}
    (h : a ≫ π = b ≫ π) : F.map π.op ≫ F.map a.op = F.map π.op ≫ F.map b.op := by
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, h]

/-- A faithful contravariant functor reflects a relation `a ≫ π = b ≫ π`. -/
theorem comp_eq_of_map_op_comp_eq (F : Cᵒᵖ ⥤ D) [F.Faithful] {Y Z T : C} {a b : Y ⟶ Z}
    (π : Z ⟶ T) (hw : F.map π.op ≫ F.map a.op = F.map π.op ≫ F.map b.op) : a ≫ π = b ≫ π :=
  Quiver.Hom.op_inj (F.map_injective (by rw [op_comp, op_comp, F.map_comp, F.map_comp]; exact hw))

/-- The fork on the images of `a` and `b` obtained by applying a contravariant functor to a
cofork on `a` and `b`. -/
def forkOfCofork (F : Cᵒᵖ ⥤ D) {Y Z : C} {a b : Y ⟶ Z} (s : Cofork a b) :
    Fork (F.map a.op) (F.map b.op) :=
  Fork.ofι (F.map (Cofork.π s).op) (map_op_comp_eq_of_comp_eq F (Cofork.condition s))

/-- **An equalizer transported back along a fully faithful contravariant functor is a
coequalizer.** If `F : Cᵒᵖ ⥤ D` is fully faithful and the image `F π : F T ⟶ F Z` of a morphism
`π : Z ⟶ T` is the equalizer of the images of `a, b : Y ⟶ Z`, then `π` is the coequalizer of `a`
and `b`. -/
def isColimitCoforkOfIsLimitFork (F : Cᵒᵖ ⥤ D) [F.Full] [F.Faithful]
    {Y Z T : C} {a b : Y ⟶ Z} (π : Z ⟶ T)
    (hw : F.map π.op ≫ F.map a.op = F.map π.op ≫ F.map b.op)
    (hl : IsLimit (Fork.ofι (F.map π.op) hw)) :
    IsColimit (Cofork.ofπ π (comp_eq_of_map_op_comp_eq F π hw)) := by
  have key : ∀ s : Cofork a b,
      F.map ((F.preimage (hl.lift (forkOfCofork F s))).unop).op = hl.lift (forkOfCofork F s) :=
    fun s ↦ F.map_preimage _
  refine Cofork.IsColimit.mk _ (fun s ↦ (F.preimage (hl.lift (forkOfCofork F s))).unop)
    (fun s ↦ ?_) (fun s m hm ↦ ?_)
  · refine Quiver.Hom.op_inj (F.map_injective ?_)
    rw [op_comp, F.map_comp, key s]
    exact hl.fac (forkOfCofork F s) WalkingParallelPair.zero
  · rw [Cofork.π_ofπ] at hm
    refine Quiver.Hom.op_inj (F.map_injective ?_)
    rw [key s]
    refine Fork.IsLimit.hom_ext hl ?_
    change F.map m.op ≫ F.map π.op = _
    rw [← F.map_comp, ← op_comp, hm]
    exact (hl.fac (forkOfCofork F s) WalkingParallelPair.zero).symm

end Stacks.FundamentalGroup

end
