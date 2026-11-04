module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Composition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ActionPushPull
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeSubintegral
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationRestriction
public import StacksCore.Tactic.StacksAttribute

/-!
# Composing two base changes of a family of cycles on fibres, along a fibre inclusion

Let `f : X ⟶ S` be locally of finite type, let `g : S' ⟶ S` and `h' : T ⟶ S'`, and let `α` be a
family of `r`-cycles on the fibres of `X/S`. Base change along `g` and then along `h'` is base
change along `h' ≫ g`, read through the comparison isomorphism `(X ×_S S') ×_{S'} T ≅ X ×_S T`.
This file proves that identity when `h'` induces isomorphisms on all residue fields.

## Main results

* `Stacks.Chow.flatPullbackWeight_congr_chowSituation` — the flat-pullback multiplicity depends
  on the base situation only through which points carry the relevant delta-dimension.
* `Stacks.Chow.baseChangeFamily_baseChangeFamily_of_residueIso` — the composition of the two
  base changes, for `h'` inducing isomorphisms on residue fields.

## Implementation notes

The library already has this identity in the *other* orientation:
`Stacks.Chow.baseChangeFamily_baseChangeFamily` assumes that the first morphism `g` induces
isomorphisms on residue fields. Both orientations are needed, and neither implies the other,
because the hypothesis plays a different role in each. In that one the hypothesis makes the
*inner* base change a pure reindexing — its multiplicity is one — and the surviving multiplicity
is compared across the square by `Stacks.Chow.flatPullbackWeight_eq_of_isIso`. Here it is the
*outer* base change that becomes a reindexing, so the multiplicity that survives is the inner
one, which is read on the fibre of `X ×_S S'` over `h' t` and therefore over the residue field
of `h' t` rather than over the residue field of `t`. Comparing it with the multiplicity of the
direct base change therefore needs the two base fields identified as well as the square, and
that is what `Stacks.Chow.flatPullbackWeight_congr_chowSituation` is for: the two residue fields
are isomorphic, so a point has the same relative dimension over either.

Away from relative dimension `r` both sides vanish, and the outer multiplicity is not needed;
the case distinction is on the relative dimension of the point of the fibre of
`(X ×_S S') ×_{S'} T` over `t`, exactly as in the other orientation.

## References

* [Stacks Project, Tag 0H4P](https://stacks.math.columbia.edu/tag/0H4P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The multiplicity depends on the base situation only through delta-dimensions -/

/-- The flat-pullback multiplicity of a point is unchanged by replacing the base situation and
the structure morphism, as long as the point carries the relevant delta-dimension for one
exactly when it does for the other: the multiplicity is the coefficient of the cycle of a closed
subscheme, and the base situation enters that coefficient only through this condition. -/
theorem flatPullbackWeight_congr_chowSituation (C D : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (tA : A ⟶ D.S) [LocallyOfFiniteType tA]
    (d : A ⟶ B) (j k : ℤ) (a : A)
    (h : relativeDimension C.dimensionFunction sA a = j ↔
      relativeDimension D.dimensionFunction tA a = k) :
    flatPullbackWeight C sA d j a = flatPullbackWeight D tA d k a :=
  closedSubschemeCycleCoeff_eq_of_relativeDimension_iff C D sA tA _ j k a h

/-! ### Composing two base changes along a morphism with isomorphic residue fields -/

section CompositeBaseChange

variable {X S S' T : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S) (h' : T ⟶ S')

/-- **Stacks Project, Tag 0H4P, the composition clause for a morphism with isomorphic residue
fields.** Base change of a family of cycles on fibres along `g` followed by base change along
`h' : T ⟶ S'` is base change along `h' ≫ g`, read through the comparison isomorphism
`(X ×_S S') ×_{S'} T ≅ X ×_S T`, when `h'` induces isomorphisms on all residue fields.

This is `Stacks.Chow.baseChangeFamily_baseChangeFamily` with the hypothesis on the other
morphism of the composite; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeCompositeResidueIso` for why both
orientations are needed and why neither follows from the other.

This is a special case of part (1) of Tag 0H4P, which carries no hypothesis on either morphism
and is registered as `Stacks.Chow.baseChangeFamily_baseChangeFamily_comp`. -/
theorem baseChangeFamily_baseChangeFamily_of_residueIso
    (hres : ∀ t : T, IsIso (h'.residueFieldMap t)) (r : ℕ) (α : FamilyOfCycles f r) (t : T) :
    baseChangeFamily (pullback.snd f g) h' r (baseChangeFamily f g r α) t =
      fiberCycleRestrict (pullback.snd f (h' ≫ g)) (pullback.snd (pullback.snd f g) h')
        (pullbackLeftPullbackSndIso f g h').hom
        (pullbackLeftPullbackSndIso_hom_snd f g h') t r
        (baseChangeFamily f (h' ≫ g) r α t) := by
  classical
  have hd : IsIso (restrictedFiberMap (pullback.snd f g) (pullback.snd (pullback.snd f g) h')
      (pullback.fst (pullback.snd f g) h') h' pullback.condition t) :=
    @AlgebraicGeometry.isIso_baseChangeFiberMap _ _ _ (pullback.snd f g) h' t (hres t)
  have hR : IsIso (fiberRestrict (pullback.snd f (h' ≫ g))
      (pullback.snd (pullback.snd f g) h') (pullbackLeftPullbackSndIso f g h').hom
      (pullbackLeftPullbackSndIso_hom_snd f g h') t) :=
    (isPullback_pullbackRestrict (pullback.snd f (h' ≫ g))
      (pullback.snd (pullback.snd f g) h') (pullbackLeftPullbackSndIso f g h').hom
      (pullbackLeftPullbackSndIso_hom_snd f g h')
      (T.fromSpecResidueField t)).flip.isIso_fst_of_isIso
  have : IsIso (h'.residueFieldMap t) := hres t
  have : IsIso (Spec.map (h'.residueFieldMap t)) := inferInstance
  have : IsFinite (Spec.map (h'.residueFieldMap t)) := inferInstance
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro y
  set C := fieldChowSituation (T.residueField t) with hC
  set d := restrictedFiberMap (pullback.snd f g) (pullback.snd (pullback.snd f g) h')
    (pullback.fst (pullback.snd f g) h') h' pullback.condition t with hddef
  set R := fiberRestrict (pullback.snd f (h' ≫ g)) (pullback.snd (pullback.snd f g) h')
    (pullbackLeftPullbackSndIso f g h').hom
    (pullbackLeftPullbackSndIso_hom_snd f g h') t with hRdef
  set u := restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition (h' t)
    with hudef
  set v := restrictedFiberMap f (pullback.snd f (h' ≫ g)) (pullback.fst f (h' ≫ g)) (h' ≫ g)
    pullback.condition t with hvdef
  set s₃ := (pullback.snd (pullback.snd f g) h').fiberToSpecResidueField t with hs₃def
  set s₁ := (pullback.snd f (h' ≫ g)).fiberToSpecResidueField t with hs₁def
  have hsq : d ≫ u = R ≫ v := restrictedFiberMap_comp_restrictedFiberMap f g h' t
  -- the two routes to `X` out of the fibre of the twice-base-changed scheme agree
  have hpt : u (d y) = v (R y) := congr($hsq y)
  -- the inverse of `d` moves the structure morphism of the fibre over `h' t` to the base
  have hstruct : (inv d ≫ s₃) ≫ Spec.map (h'.residueFieldMap t) =
      (pullback.snd f g).fiberToSpecResidueField (h' t) := by
    rw [Category.assoc, hs₃def, ← restrictedFiberMap_comp_fiberToSpecResidueField
      (pullback.snd f g) (pullback.snd (pullback.snd f g) h')
      (pullback.fst (pullback.snd f g) h') h' pullback.condition t, ← hddef, ← Category.assoc,
      IsIso.inv_hom_id, Category.id_comp]
  have hRpt : (inv d ≫ R) (d y) = R y := congr($(IsIso.hom_inv_id_assoc d R) y)
  have hRstruct : R ≫ s₁ = s₃ :=
    fiberRestrict_fiberToSpecResidueField (pullback.snd f (h' ≫ g))
      (pullback.snd (pullback.snd f g) h') (pullbackLeftPullbackSndIso f g h').hom
      (pullbackLeftPullbackSndIso_hom_snd f g h') t
  have hdimR : relativeDimension C.dimensionFunction s₁ (R y) =
      relativeDimension C.dimensionFunction s₃ y := by
    rw [← hRstruct]
    exact (relativeDimension_comp_closedImmersion C.dimensionFunction R s₁ y).symm
  -- the multiplicity of the twice-base-changed family is the multiplicity of the direct one
  have hweight :
      flatPullbackWeight (fieldChowSituation (S'.residueField (h' t)))
          ((pullback.snd f g).fiberToSpecResidueField (h' t)) u (r : ℤ) (d y) *
        flatPullbackWeight C s₃ d (r : ℤ) y =
      flatPullbackWeight C s₁ v (r : ℤ) (R y) := by
    by_cases hdim : relativeDimension C.dimensionFunction s₃ y = (r : ℤ)
    · have hone : flatPullbackWeight C s₃ d (r : ℤ) y = 1 :=
        flatPullbackWeight_of_isOpenImmersion C s₃ d (r : ℤ) y hdim
      have hbridge :
          flatPullbackWeight (fieldChowSituation (S'.residueField (h' t)))
              ((pullback.snd f g).fiberToSpecResidueField (h' t)) u (r : ℤ) (d y) =
            flatPullbackWeight C (inv d ≫ s₃) u (r : ℤ) (d y) := by
        refine flatPullbackWeight_congr_chowSituation _ C _ _ u (r : ℤ) (r : ℤ) (d y) ?_
        rw [← hstruct]
        exact (congrArg (fun n : ℤ ↦ n = (r : ℤ))
          (relativeDimension_fieldChowSituation_comp (K := S'.residueField (h' t))
            (L := T.residueField t) (Spec.map (h'.residueFieldMap t)) (inv d ≫ s₃) (d y))).to_iff
      have hsq2 : u ≫ 𝟙 (f.fiber (g (h' t))) = (inv d ≫ R) ≫ v := by
        rw [Category.comp_id, Category.assoc, ← hsq]
        exact (IsIso.inv_hom_id_assoc d u).symm
      have hsquare := flatPullbackWeight_eq_of_isIso C (inv d ≫ s₃) s₁
        (𝟙 (f.fiber (g (h' t)))) (inv d ≫ R)
        (by rw [Category.assoc, hRstruct]) u v hsq2 (r : ℤ) (d y)
      rw [hone, mul_one, hbridge, hsquare, hRpt]
      rfl
    · have hzeroD : flatPullbackWeight C s₃ d (r : ℤ) y = 0 :=
        flatPullbackWeight_eq_zero_of_relativeDimension_ne C s₃ d (r : ℤ) y hdim
      have hzeroV : flatPullbackWeight C s₁ v (r : ℤ) (R y) = 0 :=
        flatPullbackWeight_eq_zero_of_relativeDimension_ne C s₁ v (r : ℤ) (R y)
          (by rw [hdimR]; exact hdim)
      rw [hzeroD, hzeroV, mul_zero]
  have hLHS : (baseChangeFamily (pullback.snd f g) h' r (baseChangeFamily f g r α) t :
        AlgebraicCycle ((pullback.snd (pullback.snd f g) h').fiber t) ℤ) y =
      (baseChangeFamily f g r α (h' t) :
            AlgebraicCycle ((pullback.snd f g).fiber (h' t)) ℤ) (d y) *
        flatPullbackWeight C s₃ d (r : ℤ) y :=
    baseChangeFamily_apply (pullback.snd f g) h' r (baseChangeFamily f g r α) t y
  have hInner : (baseChangeFamily f g r α (h' t) :
        AlgebraicCycle ((pullback.snd f g).fiber (h' t)) ℤ) (d y) =
      (α (g (h' t)) : AlgebraicCycle (f.fiber (g (h' t))) ℤ) (u (d y)) *
        flatPullbackWeight (fieldChowSituation (S'.residueField (h' t)))
          ((pullback.snd f g).fiberToSpecResidueField (h' t)) u (r : ℤ) (d y) :=
    baseChangeFamily_apply f g r α (h' t) (d y)
  have hRHS : (baseChangeFamily f (h' ≫ g) r α t :
        AlgebraicCycle ((pullback.snd f (h' ≫ g)).fiber t) ℤ) (R y) =
      (α ((h' ≫ g) t) : AlgebraicCycle (f.fiber ((h' ≫ g) t)) ℤ) (v (R y)) *
        flatPullbackWeight C s₁ v (r : ℤ) (R y) :=
    baseChangeFamily_apply f (h' ≫ g) r α t (R y)
  rw [fiberCycleRestrict_apply, hRHS, hLHS, hInner, hpt, mul_assoc, hweight]
  rfl

end CompositeBaseChange

end Stacks.Chow

end
