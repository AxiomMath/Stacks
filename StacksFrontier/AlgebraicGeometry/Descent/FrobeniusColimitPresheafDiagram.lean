module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ExtendScalarsBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitPresheafCocone

/-!
# The objectwise cocone of Stacks Tag 0EXB

Let `p` be a prime, let `X` be a scheme in characteristic `p`, write `A` for the presheaf of
rings of sections of `𝒪_X` and `φ^j : A ⟶ A` for the `j`-th power of the `p`-th power map. Let
`M` be a presheaf of `A`-modules. The cocone of Stacks Tag 0EXB becomes, after
`SheafOfModules.toSheaf` and the identifications of
`AlgebraicGeometry.frobeniusExtendScalarsIterCompToSheafIso` and
`AlgebraicGeometry.frobeniusStageExtendScalarsCompToSheafIso`, the abelian sheafification of the
cocone of presheaves of `A`-modules

`j ↦ A ⊗_{φ^j, A} M`, with apex `(colim_j A) ⊗_{A} M`,

whose transition morphisms and legs are the objectwise base changes of
`Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo` along one Frobenius and along a
coprojection. This file builds that cocone.

## Main definitions

* `AlgebraicGeometry.frobeniusPresheafExtendIter`: the presheaf of `A`-modules
  `A ⊗_{φ^j, A} M`, read back as a presheaf of `A`-modules.
* `AlgebraicGeometry.frobeniusPresheafExtendIterMap` and
  `AlgebraicGeometry.frobeniusPresheafDiagram`: **the transition morphisms and the sequential
  diagram** they form.
* `AlgebraicGeometry.frobeniusPresheafLeg` and
  `AlgebraicGeometry.frobeniusPresheafCocone`: **the legs to `(colim_j A) ⊗_A M` and the cocone**
  they form.

## Main results

* `AlgebraicGeometry.frobeniusRingSheafIter_hom_comp_frobeniusRingSheafHom_hom`: the `j`-th
  power of Frobenius followed by Frobenius is the `j + 1`-st power, on sections.
* `AlgebraicGeometry.frobeniusPresheafExtendIterMap_comp_frobeniusPresheafLeg`: **the legs are
  compatible with the transitions**, which is what makes them a cocone. This is the transitivity
  of base change together with the arithmetic of the powers of Frobenius over the presheaf
  colimit.

## Implementation notes

The index arithmetic is free: `n + (j + 1)` and `(n + j) + 1` are definitionally equal, so the
coprojection which the transition morphism absorbs one Frobenius into is the right one on the
nose.

## References

* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- **The `j`-th power of Frobenius followed by Frobenius is the `j + 1`-st power, read on
sections.** -/
lemma frobeniusRingSheafIter_hom_comp_frobeniusRingSheafHom_hom (j : ℕ) :
    (frobeniusRingSheafIter X p hX j).hom ≫ (frobeniusRingSheafHom X p hX).hom =
      (frobeniusRingSheafIter X p hX (j + 1)).hom :=
  congrArg (fun t : X.ringSheafOnOpens ⟶ X.ringSheafOnOpens ↦ t.hom)
    (frobeniusRingSheafIter_comp_frobeniusRingSheafHom X p hX j)

variable (M : PresheafOfModules.{u} X.ringSheafOnOpens.obj)

/-- **The presheaf of `𝒪_X`-modules `A ⊗_{φ^j, A} M`**: the objectwise extension of scalars of
`M` along the `j`-th power of Frobenius, read back as a presheaf of `A`-modules. -/
noncomputable abbrev frobeniusPresheafExtendIter (j : ℕ) :
    PresheafOfModules.{u} X.ringSheafOnOpens.obj :=
  Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
    (frobeniusRingSheafIter X p hX j).hom M

/-- **The transition morphism of the objectwise cocone of Stacks Tag 0EXB**: the base change of
`A ⊗_{φ^j, A} M` along one more Frobenius. -/
noncomputable def frobeniusPresheafExtendIterMap (j : ℕ) :
    frobeniusPresheafExtendIter X p hX M j ⟶ frobeniusPresheafExtendIter X p hX M (j + 1) :=
  Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo (frobeniusRingSheafIter X p hX j).hom
    (frobeniusRingSheafHom X p hX).hom M (frobeniusRingSheafIter X p hX (j + 1)).hom
    (frobeniusRingSheafIter_hom_comp_frobeniusRingSheafHom_hom X p hX j)

/-- **The sequential diagram `j ↦ A ⊗_{φ^j, A} M` of presheaves of `𝒪_X`-modules.** -/
noncomputable def frobeniusPresheafDiagram :
    ℕ ⥤ PresheafOfModules.{u} X.ringSheafOnOpens.obj :=
  Functor.ofSequence (X := fun j ↦ frobeniusPresheafExtendIter X p hX M j)
    (fun j ↦ frobeniusPresheafExtendIterMap X p hX M j)

/-- The `j`-th object of the sequential diagram is `A ⊗_{φ^j, A} M`. -/
@[simp]
lemma frobeniusPresheafDiagram_obj (j : ℕ) :
    (frobeniusPresheafDiagram X p hX M).obj j = frobeniusPresheafExtendIter X p hX M j :=
  rfl

/-- The morphism `j ⟶ j + 1` of the sequential diagram is the transition morphism
`frobeniusPresheafExtendIterMap X p hX M j`. -/
@[simp]
lemma frobeniusPresheafDiagram_map_succ (j : ℕ) :
    (frobeniusPresheafDiagram X p hX M).map (homOfLE (Nat.le_add_right j 1)) =
      frobeniusPresheafExtendIterMap X p hX M j :=
  Functor.ofSequence_map_homOfLE_succ _ j

/-- **The leg of the objectwise cocone of Stacks Tag 0EXB**: the base change of `A ⊗_{φ^j, A} M`
along the stage-`n + j` coprojection into the presheaf colimit `colim_j A`. -/
noncomputable def frobeniusPresheafLeg (n j : ℕ) :
    frobeniusPresheafExtendIter X p hX M j ⟶
      Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
        (frobeniusRingPresheafι X p hX n) M :=
  Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo (frobeniusRingSheafIter X p hX j).hom
    (frobeniusRingPresheafι X p hX (n + j)) M (frobeniusRingPresheafι X p hX n)
    (frobeniusRingSheafIter_hom_comp_frobeniusRingPresheafι X p hX j n)

/-- **The legs of the objectwise cocone of Stacks Tag 0EXB are compatible with the
transitions.** This is the transitivity of base change, followed by the fact that one Frobenius
after the stage-`n + j + 1` coprojection is the stage-`n + j` coprojection. -/
theorem frobeniusPresheafExtendIterMap_comp_frobeniusPresheafLeg (n j : ℕ) :
    frobeniusPresheafExtendIterMap X p hX M j ≫ frobeniusPresheafLeg X p hX M n (j + 1) =
      frobeniusPresheafLeg X p hX M n j := by
  have hmid : (frobeniusRingSheafHom X p hX).hom ≫
      frobeniusRingPresheafι X p hX (n + (j + 1)) = frobeniusRingPresheafι X p hX (n + j) :=
    frobeniusRingSheafHom_hom_comp_frobeniusRingPresheafι_succ X p hX (n + j)
  have htot : (frobeniusRingSheafIter X p hX j).hom ≫
      ((frobeniusRingSheafHom X p hX).hom ≫ frobeniusRingPresheafι X p hX (n + (j + 1))) =
      frobeniusRingPresheafι X p hX n :=
    (congrArg (fun q ↦ (frobeniusRingSheafIter X p hX j).hom ≫ q) hmid).trans
      (frobeniusRingSheafIter_hom_comp_frobeniusRingPresheafι X p hX j n)
  refine Eq.trans (Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo_comp_baseChangeTo
    (frobeniusRingSheafIter X p hX j).hom (frobeniusRingSheafHom X p hX).hom M
    (frobeniusRingPresheafι X p hX (n + (j + 1)))
    (frobeniusRingSheafIter X p hX (j + 1)).hom
    (frobeniusRingSheafIter_hom_comp_frobeniusRingSheafHom_hom X p hX j)
    (frobeniusRingPresheafι X p hX n)
    (frobeniusRingSheafIter_hom_comp_frobeniusRingPresheafι X p hX (j + 1) n)
    ((frobeniusRingSheafHom X p hX).hom ≫ frobeniusRingPresheafι X p hX (n + (j + 1)))
    rfl htot) ?_
  exact Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo_congr
    (frobeniusRingSheafIter X p hX j).hom
    ((frobeniusRingSheafHom X p hX).hom ≫ frobeniusRingPresheafι X p hX (n + (j + 1))) M
    (frobeniusRingPresheafι X p hX (n + j)) hmid (frobeniusRingPresheafι X p hX n) htot
    (frobeniusRingSheafIter_hom_comp_frobeniusRingPresheafι X p hX j n)

/-- **The objectwise cocone of Stacks Tag 0EXB**: the diagram `j ↦ A ⊗_{φ^j, A} M` with its base
changes into `(colim_j A) ⊗_A M`. -/
noncomputable def frobeniusPresheafCocone (n : ℕ) :
    Cocone (frobeniusPresheafDiagram X p hX M) where
  pt := Stacks.NoncommChangeOfRings.Presheaf.restrictExtendObj
    (frobeniusRingPresheafι X p hX n) M
  ι := NatTrans.ofSequence (fun j ↦ frobeniusPresheafLeg X p hX M n j) (fun j ↦ by
    have h : (frobeniusPresheafDiagram X p hX M).map (homOfLE (j.le_add_right 1)) ≫
          frobeniusPresheafLeg X p hX M n (j + 1) =
        frobeniusPresheafLeg X p hX M n j := by
      rw [frobeniusPresheafDiagram_map_succ]
      exact frobeniusPresheafExtendIterMap_comp_frobeniusPresheafLeg X p hX M n j
    exact h.trans (Category.comp_id _).symm)

/-- The `j`-th leg of the cocone is `frobeniusPresheafLeg X p hX M n j`. -/
@[simp]
lemma frobeniusPresheafCocone_ι_app (n j : ℕ) :
    (frobeniusPresheafCocone X p hX M n).ι.app j = frobeniusPresheafLeg X p hX M n j :=
  rfl

end AlgebraicGeometry

end
