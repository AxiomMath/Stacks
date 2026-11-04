module

public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.PurityCriterionLimits
public import StacksFrontier.AlgebraicGeometry.Flatness.RelativelyPure.BaseChange

/-!
# Base change of an elementary étale neighbourhood

The purity criterion of Tag 05L4 is applied, in the proof that purity passes to a finite stage
in Tag 05MA, both at the limit of an inverse system and at a finite stage of it. The data it
consumes — an elementary étale neighbourhood of the base point, an étale scheme over the source
lying over that neighbourhood, and universal purity of the module upstairs — is produced once,
at one stage, and then transported along the base-change morphisms. Universal purity is
transported by Tag 05J6; what is proved here is that an elementary étale neighbourhood stays
elementary.

## Main results

* `AlgebraicGeometry.isIso_pullback_snd_residueFieldMap_of_isIso`: a pullback projection induces
  an isomorphism on residue fields at a point where the opposite morphism does.
* `AlgebraicGeometry.exists_point_pullback_isIso_residueFieldMap`: the base change of an
  elementary étale neighbourhood of `(S, s)` along a morphism carrying `t` to `s` carries a
  point over the distinguished point and over `t` at which it is again elementary.

## Implementation notes

`AlgebraicGeometry.isIso_pullback_snd_residueFieldMap_of_isIso` restates, publicly, a lemma
which exists privately in three places in the library — in `Flatness/FiniteNeighborhood.lean`,
in `Etale/ElementaryNeighborhood/FreeSectionsFromFiniteTypeFlatness.lean` and in
`Flatness/Devissage/OneStep/BaseChangeAt.lean`. The proof is the one of the second, over the
public `AlgebraicGeometry.Scheme.Pullback` API of `Mathlib`: the fibre of the pullback over the
pair of points is the spectrum of the tensor product of the two residue fields over the common
one, the hypothesis makes one of the two structure maps of that tensor product an isomorphism,
and the point of the pullback is then recovered from its own residue field.

Purity along a fibre is *not* inherited by base change — that is the content of Tag 05MA — but
universal purity is, and that is
`AlgebraicGeometry.isUniversallyPureRelative_iff_forall_baseChange_isPureRelative`.

## References

* [Stacks Project, Tag 05J6](https://stacks.math.columbia.edu/tag/05J6)
* [Stacks Project, Tag 05MA](https://stacks.math.columbia.edu/tag/05MA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Inducing an isomorphism on residue fields is inherited by a base change: if `f` induces an
isomorphism on residue fields at the image of `z` under the first projection, then the second
projection of the pullback of `f` along `g` induces an isomorphism on residue fields at `z`. -/
public theorem isIso_pullback_snd_residueFieldMap_of_isIso
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (z : (pullback f g : Scheme.{u}).carrier)
    (hfx : IsIso (f.residueFieldMap (pullback.fst f g z))) :
    IsIso ((pullback.snd f g).residueFieldMap z) := by
  let T : Scheme.Pullback.Triplet f g := Scheme.Pullback.Triplet.ofPoint z
  let p := Scheme.Pullback.SpecOfPoint z
  let : IsIso (f.residueFieldMap T.x) := hfx
  let : IsIso ((Y.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x) := inferInstance
  let : IsIso T.tensorInr := by
    show IsIso (pushout.inr
      ((Y.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((Y.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y))
    apply CategoryTheory.Limits.pushout_inr_iso_of_left_iso
  let : Field T.tensor :=
    (MulEquiv.isField (Field.toIsField (Y'.residueField T.y))
      (asIso T.tensorInr).symm.commRingCatIsoToRingEquiv.toMulEquiv).toField
  let : IsOpenImmersion (Spec.map T.tensorInr) := inferInstance
  let q := T.SpecTensorTo
  have hp := Scheme.Pullback.isIso_residueFieldMap_specTensorTo_comp_residueFieldIso T p
  have : IsIso (q.residueFieldMap p) :=
    IsIso.of_isIso_comp_right _ (Scheme.Spec.residueFieldIso T.tensor p).hom
  have hptComp : (q ≫ pullback.snd f g) p =
      (Spec.map T.tensorInr ≫ Y'.fromSpecResidueField T.y) p := by
    rw [T.specTensorTo_snd]
  have hcomp : IsIso ((pullback.snd f g).residueFieldMap (q p) ≫ q.residueFieldMap p) := by
    rw [← Scheme.residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr T.specTensorTo_snd p]
    simp only [Scheme.residueFieldMap_comp]
    show IsIso ((Y'.residueFieldCongr hptComp).hom ≫
      (Y'.fromSpecResidueField T.y).residueFieldMap ((Spec.map T.tensorInr) p) ≫
      (Spec.map T.tensorInr).residueFieldMap p)
    exact IsIso.comp_isIso' (Y'.residueFieldCongr hptComp).isIso_hom
      (IsIso.comp_isIso' (isIso_residueFieldMap_of_isPreimmersion
        (Y'.fromSpecResidueField T.y) (Spec.map T.tensorInr p)) inferInstance)
  have hIsoAtPoint : IsIso ((pullback.snd f g).residueFieldMap (q p)) :=
    IsIso.of_isIso_comp_right _ (q.residueFieldMap p)
  rwa [Scheme.Pullback.SpecTensorTo_SpecOfPoint z] at hIsoAtPoint

/-- Inducing an isomorphism on residue fields is inherited by a base change, in the form for the
first projection. -/
public theorem isIso_pullback_fst_residueFieldMap_of_isIso
    {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (z : (pullback f g : Scheme.{u}).carrier)
    (hgy : IsIso (g.residueFieldMap (pullback.snd f g z))) :
    IsIso ((pullback.fst f g).residueFieldMap z) := by
  let w := (pullbackSymmetry f g).hom z
  have hw : pullback.fst g f w = pullback.snd f g z :=
    congrArg (fun m : pullback f g ⟶ Y => m z) (pullbackSymmetry_hom_comp_fst f g)
  have hgw : IsIso (g.residueFieldMap (pullback.fst g f w)) := by rwa [hw]
  have hc : IsIso (((pullbackSymmetry f g).hom ≫ pullback.snd g f).residueFieldMap z) := by
    simp only [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso'
      (isIso_pullback_snd_residueFieldMap_of_isIso g f w hgw) inferInstance
  rwa [pullbackSymmetry_hom_comp_snd] at hc

/-- The base change of an elementary étale neighbourhood is an elementary étale neighbourhood:
if `pi : S' ⟶ S` induces an isomorphism on residue fields at `s'` and `h : S₁ ⟶ S` carries `t`
to `pi s'`, then the pullback of `h` along `pi` carries a point lying over `t` and over `s'` at
which the projection to `S₁` induces an isomorphism on residue fields. -/
public theorem exists_point_pullback_isIso_residueFieldMap
    {S S' S₁ : Scheme.{u}} (pi : S' ⟶ S) (h : S₁ ⟶ S) (s' : S') (t : S₁)
    (ht : h t = pi s') (hel : IsIso (pi.residueFieldMap s')) :
    ∃ z : (pullback h pi : Scheme.{u}).carrier, pullback.fst h pi z = t ∧
      pullback.snd h pi z = s' ∧ IsIso ((pullback.fst h pi).residueFieldMap z) := by
  obtain ⟨z, hz1, hz2⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := h) (g := pi) t s' ht
  exact ⟨z, hz1, hz2,
    isIso_pullback_fst_residueFieldMap_of_isIso h pi z (by rwa [hz2])⟩

/-- Purity along a fibre follows from universal purity along that fibre, there being fewer
impurity diagrams to exclude. -/
public theorem isPureAlong_of_isUniversallyPureAlong {P : PrePureSituation.{u}}
    (h : IsUniversallyPureAlong P) : IsPureAlong P :=
  fun D _ _ => h D

end AlgebraicGeometry

end
