module

public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec

/-!
# Inducing an isomorphism on residue fields is preserved by base change

If `f : X ⟶ Y` induces an isomorphism on the residue field at the first projection of a point of
`X ×_Y Y'`, then the second projection induces an isomorphism on the residue field at that point.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Inducing isomorphisms on residue fields is preserved by base change. -/
lemma pullback_snd_residueFieldMap_isIso
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (z : (pullback f g : Scheme).carrier)
    (hfx : IsIso (f.residueFieldMap (pullback.fst f g z))) :
    IsIso ((pullback.snd f g).residueFieldMap z) := by
  let T : Scheme.Pullback.Triplet f g := Scheme.Pullback.Triplet.ofPoint z
  let p := Scheme.Pullback.SpecOfPoint z
  have : IsIso (f.residueFieldMap T.x) := hfx
  have : IsIso (Y.residueFieldCongr T.hx).hom := (Y.residueFieldCongr T.hx).isIso_hom
  have : IsIso ((Y.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x) := by infer_instance
  have : IsIso T.tensorInr := by
    show IsIso (pushout.inr
      ((Y.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((Y.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y))
    apply CategoryTheory.Limits.pushout_inr_iso_of_left_iso
  let _ : Field T.tensor :=
    (MulEquiv.isField (Field.toIsField (Y'.residueField T.y))
      (asIso T.tensorInr).symm.commRingCatIsoToRingEquiv.toMulEquiv).toField
  have : IsOpenImmersion (Spec.map T.tensorInr) := by infer_instance
  let q := T.SpecTensorTo
  have hp := Scheme.Pullback.isIso_residueFieldMap_specTensorTo_comp_residueFieldIso T p
  have := hp
  have : IsIso (q.residueFieldMap p) :=
    IsIso.of_isIso_comp_right _ (Scheme.Spec.residueFieldIso T.tensor p).hom
  have hptComp : (q ≫ pullback.snd f g) p =
      (Spec.map T.tensorInr ≫ Y'.fromSpecResidueField T.y) p := by
    rw [T.specTensorTo_snd]
  have : IsIso (Y'.residueFieldCongr hptComp).hom := (Y'.residueFieldCongr hptComp).isIso_hom
  have hcomp : IsIso ((pullback.snd f g).residueFieldMap (q p) ≫ q.residueFieldMap p) := by
    rw [← Scheme.residueFieldMap_comp]
    rw [Scheme.Hom.residueFieldMap_congr T.specTensorTo_snd p]
    rw [Scheme.residueFieldMap_comp]
    have hIsoFrom := isIso_residueFieldMap_fromSpecResidueField Y' T.y (Spec.map T.tensorInr p)
    have : IsIso ((Y'.fromSpecResidueField T.y).residueFieldMap ((Spec.map T.tensorInr) p)) :=
      hIsoFrom
    have : IsIso ((Spec.map T.tensorInr).residueFieldMap p) := by infer_instance
    show IsIso ((Y'.residueFieldCongr hptComp).hom ≫
      (Y'.fromSpecResidueField T.y).residueFieldMap ((Spec.map T.tensorInr) p) ≫
      (Spec.map T.tensorInr).residueFieldMap p)
    have htail : IsIso
        ((Y'.fromSpecResidueField T.y).residueFieldMap ((Spec.map T.tensorInr) p) ≫
          (Spec.map T.tensorInr).residueFieldMap p) :=
      IsIso.comp_isIso' hIsoFrom (by infer_instance)
    exact IsIso.comp_isIso' (Y'.residueFieldCongr hptComp).isIso_hom htail
  have hIsoAtPoint : IsIso ((pullback.snd f g).residueFieldMap (q p)) :=
    IsIso.of_isIso_comp_right ((pullback.snd f g).residueFieldMap (q p)) (q.residueFieldMap p)
  rw [Scheme.Pullback.SpecTensorTo_SpecOfPoint z] at hIsoAtPoint
  exact hIsoAtPoint

end AlgebraicGeometry
