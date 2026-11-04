module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonTransitivity
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.TwoEngineTransitivity
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationNaturality

/-!
# Localization of higher direct images: the cocycle identity in every degree

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and let `V' ≤ V` be opens of `Y`.
The comparisons identifying `(R^p f_* ℱ)|_V` with the `p`-th higher direct image along
`f|_{f⁻¹(V)}` are compatible across `V' ≤ V`, in every degree.

## Main definitions

* `pushforwardRestrictOfLEIso`: the isomorphism between the two routes from `𝒪_X`-modules to
  `𝒪_Y|_{V'}`-modules: the composite functor `ℱ ↦ (f|_{f⁻¹(V)})_*(ℱ|_{f⁻¹(V)})` followed by
  restriction along `V' ≤ V`, or `ℱ ↦ (f|_{f⁻¹(V')})_*(ℱ|_{f⁻¹(V')})`.
* `rightDerivedPushforwardRestrictionOfLEIso`: that isomorphism after deriving, in every degree.
* `higherDirectImageRestrictIsoSuccOfLE`: the composite of the inverse of
  `compRightDerivedNatIso` for `V`, `rightDerivedPushforwardRestrictionOfLEIso`, and
  `compRightDerivedNatIso` for `V'`.

## Main results

* `pushforwardRestrictOfLEIso_compatibility`: the underived cocycle identity for
  `pushforwardRestrictOfLEIso`.
* `rightDerivedPushforwardRestrictIso_ofLE`: the comparison `rightDerivedPushforwardRestrictIso`
  attached to `V'` is the comparison attached to `V`, whiskered by restriction along `V' ≤ V`,
  followed by the derived middle comparison, read through the transitivity isomorphism on the
  `Y` side.
* `rightDerivedPushforwardRestrictionOfLEIso_zero`: in degree zero the derived middle comparison
  is `pushforwardRestrictOfLEIso`.
* `higherDirectImageRestrictIsoSucc_ofLE` and `higherDirectImageRestrictIso_ofLE`: the same
  compatibility for `higherDirectImageRestrictIsoSucc` and for `higherDirectImageRestrictIso`,
  through `higherDirectImageRestrictIsoSuccOfLE`.
* `higherDirectImageRestrictIsoSuccOfLE_hom_eq` and `higherDirectImageRestrictIsoSuccOfLE_eq`:
  `higherDirectImageRestrictIsoSuccOfLE` is the inverse of `higherDirectImageRestrictionOfLEIso`
  conjugated by `moduleRestrictionOfLEIso` on the `X` side.

## References

* [The Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [The Stacks Project, Tag 02O7](https://stacks.math.columbia.edu/tag/02O7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.HigherDirectImage

section Nested

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) {V' V : Opens Y} (h : V' ≤ V)

/-- The isomorphism between the two routes from `𝒪_X`-modules to `𝒪_Y|_{V'}`-modules: restrict
to `f⁻¹(V)`, push forward along `f|_{f⁻¹(V)}` and restrict along `V' ≤ V`; or restrict to
`f⁻¹(V')` and push forward along `f|_{f⁻¹(V')}`. It is the inverse of
`modulePushforwardRestrictionOfLEIso` followed by the transitivity isomorphism
`moduleRestrictionOfLEIso` on the `X` side. -/
noncomputable def pushforwardRestrictOfLEIso :
    (moduleRestriction X (preimageOpen f V) ⋙ modulePushforward (restrictedMorphism f V)) ⋙
        moduleRestrictionOfLE Y h ≅
      moduleRestriction X (preimageOpen f V') ⋙ modulePushforward (restrictedMorphism f V') :=
  Functor.isoWhiskerLeft (moduleRestriction X (preimageOpen f V))
      (modulePushforwardRestrictionOfLEIso f h).symm ≪≫
    Functor.isoWhiskerRight (moduleRestrictionOfLEIso X (preimageOpen_mono f h))
      (modulePushforward (restrictedMorphism f V'))

/-- Whiskering the comparison for `V` by restriction along `V' ≤ V` and following with
`pushforwardRestrictOfLEIso` is the transitivity isomorphism on the `Y` side followed by the
comparison for `V'`. -/
theorem pushforwardRestrictOfLEIso_compatibility :
    Functor.whiskerRight (modulePushforwardRestrictIso f V).inv (moduleRestrictionOfLE Y h) ≫
        (pushforwardRestrictOfLEIso f h).hom =
      Functor.whiskerLeft (modulePushforward f) (moduleRestrictionOfLEIso Y h).hom ≫
        (modulePushforwardRestrictIso f V').inv := by
  rw [Iso.eq_comp_inv, modulePushforwardRestrictIso_ofLE f h]
  dsimp only [pushforwardRestrictOfLEIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Iso.symm_hom]
  rw [Category.assoc, Category.assoc, ← Functor.whiskerRight_comp_assoc, Iso.hom_inv_id,
    Functor.whiskerRight_id', Category.id_comp, ← Functor.whiskerLeft_comp_assoc,
    Iso.inv_hom_id, Functor.whiskerLeft_id', Category.id_comp,
    ← Functor.whiskerRight_comp_assoc, Iso.inv_hom_id, Functor.whiskerRight_id',
    Category.id_comp]

/-- The isomorphism, given by `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` for the
exact functor of restriction along `V' ≤ V`, between the right derived functors of
`ℱ ↦ (f|_{f⁻¹(V)})_*(ℱ|_{f⁻¹(V)})` followed by restriction along `V' ≤ V` and the right derived
functors of `ℱ ↦ (f|_{f⁻¹(V')})_*(ℱ|_{f⁻¹(V')})`. -/
noncomputable def rightDerivedPushforwardRestrictionOfLEIso (p : ℕ) :
    (moduleRestriction X (preimageOpen f V) ⋙
          modulePushforward (restrictedMorphism f V)).rightDerived p ⋙
        moduleRestrictionOfLE Y h ≅
      (moduleRestriction X (preimageOpen f V') ⋙
        modulePushforward (restrictedMorphism f V')).rightDerived p :=
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso _ _ _ (pushforwardRestrictOfLEIso f h) p

/-- The comparison `rightDerivedPushforwardRestrictIso` attached to `V'` is the comparison
attached to `V`, whiskered by restriction along `V' ≤ V` and followed by the derived middle
comparison, read through the transitivity isomorphism `moduleRestrictionOfLEIso` on the `Y` side.

Equivalently: the two routes from `R^p f_* ℱ` restricted to `V'`, namely restricting to `V` and
then along `V' ≤ V` or restricting to `V'` directly, induce the same identification of
`(R^p f_* ℱ)|_{V'}` with the `p`-th right derived functor of
`ℱ ↦ (f|_{f⁻¹(V')})_*(ℱ|_{f⁻¹(V')})`. -/
@[stacks 01E5 "compatibility across nested opens, every degree"]
theorem rightDerivedPushforwardRestrictIso_ofLE (p : ℕ) :
    Functor.whiskerRight (rightDerivedPushforwardRestrictIso f V p).hom
          (moduleRestrictionOfLE Y h) ≫
        (rightDerivedPushforwardRestrictionOfLEIso f h p).hom =
      Functor.whiskerLeft ((modulePushforward f).rightDerived p)
          (moduleRestrictionOfLEIso Y h).hom ≫
        (rightDerivedPushforwardRestrictIso f V' p).hom :=
  Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_comp_congr
    (modulePushforward f) (moduleRestriction Y V)
    (moduleRestriction X (preimageOpen f V) ⋙ modulePushforward (restrictedMorphism f V))
    (moduleRestrictionOfLE Y h)
    (moduleRestriction X (preimageOpen f V') ⋙ modulePushforward (restrictedMorphism f V'))
    (moduleRestriction Y V') (modulePushforwardRestrictIso f V).symm
    (pushforwardRestrictOfLEIso f h) (moduleRestrictionOfLEIso Y h)
    (modulePushforwardRestrictIso f V').symm
    (fun M => congrArg (fun t => NatTrans.app t M)
      (pushforwardRestrictOfLEIso_compatibility f h)) p

/-- After the canonical maps to the zeroth right derived functors,
`rightDerivedPushforwardRestrictionOfLEIso f h 0` is `pushforwardRestrictOfLEIso f h`. -/
theorem rightDerivedPushforwardRestrictionOfLEIso_zero :
    Functor.whiskerRight
          (moduleRestriction X (preimageOpen f V) ⋙
            modulePushforward (restrictedMorphism f V)).toRightDerivedZero
          (moduleRestrictionOfLE Y h) ≫
        (rightDerivedPushforwardRestrictionOfLEIso f h 0).hom =
      (pushforwardRestrictOfLEIso f h).hom ≫
        (moduleRestriction X (preimageOpen f V') ⋙
          modulePushforward (restrictedMorphism f V')).toRightDerivedZero :=
  Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_zero _ _ _
    (pushforwardRestrictOfLEIso f h)

/-- The composite of the inverse of `compRightDerivedNatIso` for `V`, whiskered by restriction
along `V' ≤ V`, with `rightDerivedPushforwardRestrictionOfLEIso` and `compRightDerivedNatIso`
for `V'`. -/
noncomputable def higherDirectImageRestrictIsoSuccOfLE (p : ℕ) :
    moduleRestriction X (preimageOpen f V) ⋙
          (modulePushforward (restrictedMorphism f V)).rightDerived p ⋙
        moduleRestrictionOfLE Y h ≅
      moduleRestriction X (preimageOpen f V') ⋙
        (modulePushforward (restrictedMorphism f V')).rightDerived p :=
  Functor.isoWhiskerRight
      (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
          (moduleRestriction X (preimageOpen f V))
          (modulePushforward (restrictedMorphism f V)) p).symm
      (moduleRestrictionOfLE Y h) ≪≫
    rightDerivedPushforwardRestrictionOfLEIso f h p ≪≫
    Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
      (moduleRestriction X (preimageOpen f V'))
      (modulePushforward (restrictedMorphism f V')) p

/-- The comparison `higherDirectImageRestrictIsoSucc` attached to `V`, whiskered by restriction
along `V' ≤ V` and followed by the transitivity isomorphism `moduleRestrictionOfLEIso` on the
`Y` side, agrees with `higherDirectImageRestrictIsoSuccOfLE` followed by the comparison attached
to `V'`. -/
@[stacks 01E5 "higher direct images, compatibility across nested opens"]
theorem higherDirectImageRestrictIsoSucc_ofLE (p : ℕ) :
    Functor.whiskerRight (higherDirectImageRestrictIsoSucc f V p).hom
          (moduleRestrictionOfLE Y h) ≫
        Functor.whiskerLeft ((modulePushforward f).rightDerived p)
          (moduleRestrictionOfLEIso Y h).hom =
      (higherDirectImageRestrictIsoSuccOfLE f h p).hom ≫
        (higherDirectImageRestrictIsoSucc f V' p).hom := by
  dsimp only [higherDirectImageRestrictIsoSucc, higherDirectImageRestrictIsoSuccOfLE,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Functor.isoWhiskerRight_hom]
  rw [Functor.whiskerRight_comp, Category.assoc, Category.assoc, Category.assoc]
  congr 1
  rw [Iso.hom_inv_id_assoc]
  have hmul : Functor.whiskerRight (rightDerivedPushforwardRestrictIso f V p).hom
        (moduleRestrictionOfLE Y h) ≫
      ((rightDerivedPushforwardRestrictionOfLEIso f h p).hom ≫
        (rightDerivedPushforwardRestrictIso f V' p).inv) =
      Functor.whiskerLeft ((modulePushforward f).rightDerived p)
        (moduleRestrictionOfLEIso Y h).hom := by
    rw [← Category.assoc, rightDerivedPushforwardRestrictIso_ofLE f h p, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [← hmul, ← Functor.whiskerRight_comp_assoc, Iso.inv_hom_id, Functor.whiskerRight_id',
    Category.id_comp]

/-- The comparison `higherDirectImageRestrictIso` attached to `V`, whiskered by restriction along
`V' ≤ V` and followed by the transitivity isomorphism `moduleRestrictionOfLEIso` on the `Y` side,
agrees with `higherDirectImageRestrictIsoSuccOfLE` followed by the comparison attached to `V'`,
in every degree including zero. -/
theorem higherDirectImageRestrictIso_ofLE (p : ℕ) :
    Functor.whiskerRight (higherDirectImageRestrictIso f V p).hom
          (moduleRestrictionOfLE Y h) ≫
        Functor.whiskerLeft ((modulePushforward f).rightDerived p)
          (moduleRestrictionOfLEIso Y h).hom =
      (higherDirectImageRestrictIsoSuccOfLE f h p).hom ≫
        (higherDirectImageRestrictIso f V' p).hom := by
  rw [higherDirectImageRestrictIso_eq_succ f V p, higherDirectImageRestrictIso_eq_succ f V' p]
  exact higherDirectImageRestrictIsoSucc_ofLE f h p

/-- The forward map of `higherDirectImageRestrictIsoSuccOfLE` is the inverse of the middle
comparison `higherDirectImageRestrictionOfLEIso`, conjugated by the transitivity isomorphism
`moduleRestrictionOfLEIso` on the `X` side. -/
theorem higherDirectImageRestrictIsoSuccOfLE_hom_eq (p : ℕ) :
    (higherDirectImageRestrictIsoSuccOfLE f h p).hom =
      Functor.whiskerLeft (moduleRestriction X (preimageOpen f V))
          (higherDirectImageRestrictionOfLEIso f h p).inv ≫
        Functor.whiskerRight (moduleRestrictionOfLEIso X (preimageOpen_mono f h)).hom
          ((modulePushforward (restrictedMorphism f V')).rightDerived p) := by
  have key := Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_comp_compRightDerivedNatIso
    (moduleRestriction X (preimageOpen f V)) (modulePushforward (restrictedMorphism f V))
    (moduleRestrictionOfLE Y h) (moduleRestrictionOfLE X (preimageOpen_mono f h))
    (modulePushforward (restrictedMorphism f V')) (moduleRestriction X (preimageOpen f V'))
    (modulePushforwardRestrictionOfLEIso f h).symm
    (moduleRestrictionOfLEIso X (preimageOpen_mono f h)) (pushforwardRestrictOfLEIso f h)
    (fun _ => rfl) p
  dsimp only [higherDirectImageRestrictIsoSuccOfLE, rightDerivedPushforwardRestrictionOfLEIso,
    higherDirectImageRestrictionOfLEIso, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerRight_hom]
  rw [key, ← Category.assoc, ← Functor.whiskerRight_comp, Iso.inv_hom_id,
    Functor.whiskerRight_id', Functor.whiskerLeft_comp, Category.assoc]
  exact Category.id_comp _

/-- `higherDirectImageRestrictIsoSuccOfLE` is the inverse of the middle comparison
`higherDirectImageRestrictionOfLEIso`, conjugated by the transitivity isomorphism
`moduleRestrictionOfLEIso` on the `X` side. -/
theorem higherDirectImageRestrictIsoSuccOfLE_eq (p : ℕ) :
    higherDirectImageRestrictIsoSuccOfLE f h p =
      Functor.isoWhiskerLeft (moduleRestriction X (preimageOpen f V))
          (higherDirectImageRestrictionOfLEIso f h p).symm ≪≫
        Functor.isoWhiskerRight (moduleRestrictionOfLEIso X (preimageOpen_mono f h))
          ((modulePushforward (restrictedMorphism f V')).rightDerived p) :=
  Iso.ext (higherDirectImageRestrictIsoSuccOfLE_hom_eq f h p)

end Nested

end Stacks.Cohomology.HigherDirectImage

end
