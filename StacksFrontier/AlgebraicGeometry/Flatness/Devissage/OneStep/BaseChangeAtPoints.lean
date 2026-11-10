module

public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.OneStep.BaseChangeAt
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BaseChangeFiberMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.ResidueFieldMapIsIso

/-!
# The distinguished points of a base-changed one-step dévissage

For a one-step dévissage at a point and an affine pointed base change inducing an isomorphism of
residue fields, the three distinguished points of the base change exist and are unique, and for
the base change constructed in `AlgebraicGeometry.OneStepDevissage.baseChange` the base-changed
dévissage is a one-step dévissage at the first of them.

## Main results

* `AlgebraicGeometry.OneStepDevissageAt.exists_unique_points_baseChange`: the three
  distinguished points of the base change exist and are unique.
* `AlgebraicGeometry.OneStepDevissageAt.exists_baseChange_of_affine`: for the constructed base
  change, the three distinguished points together with the dévissage at the first of them.

## References

* [Stacks Project, Tag 05H8](https://stacks.math.columbia.edu/tag/05H8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace OneStepDevissageAt

/-- Two points of the vertex of a pullback square agree if they have the same images over a point
of the base along which the residue field map is an isomorphism. -/
private theorem eq_of_isPullback_of_isIso_residueFieldMap {P A B S : Scheme.{u}}
    {fst : P ⟶ A} {snd : P ⟶ B} {f : A ⟶ S} {g : B ⟶ S} (H : IsPullback fst snd f g)
    (x : A) (y : B) (hxy : f x = g y)
    (hfield : IsIso ((S.residueFieldCongr hxy.symm).inv ≫ g.residueFieldMap y)) (p q : P)
    (hp : fst p = x) (hq : snd p = y) (hp' : fst q = x) (hq' : snd q = y) : p = q := by
  have h₁ (r : P) : pullback.fst f g (H.isoPullback.hom r) = fst r := by
    rw [← Scheme.Hom.comp_apply, H.isoPullback_hom_fst]
  have h₂ (r : P) : pullback.snd f g (H.isoPullback.hom r) = snd r := by
    rw [← Scheme.Hom.comp_apply, H.isoPullback_hom_snd]
  exact (Scheme.Hom.homeomorph H.isoPullback.hom).injective
    (pullback_point_eq_of_isIso_residueFieldMap f g x y hxy hfield _ _
      ((h₁ p).trans hp) ((h₂ p).trans hq) ((h₁ q).trans hp') ((h₂ q).trans hq'))

/-- The three distinguished points of a base-changed one-step dévissage exist and are unique:
each of the three base-changed schemes has exactly one point lying both over the corresponding
distinguished point of the original dévissage and over the new base point. -/
theorem exists_unique_points_baseChange {X S S' : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (x : X) [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (D : OneStepDevissageAt f F x)
    (s' : S') (h : S' ⟶ S) (hs : h s' = f x) [IsAffine S']
    [IsIso ((S.residueFieldCongr hs).inv ≫ h.residueFieldMap s')]
    (B : OneStepDevissage.BaseChangeData f F (f x) s' h hs D.toOneStepDevissage) :
    letI := B.locallyOfFiniteType
    letI := B.quasicoherent
    letI := B.finiteType
    ∃ (x' : ↥(pullback f h)) (z' : B.devissage.Z) (y' : B.devissage.Y),
      ((pullback.fst f h x' = x ∧ pullback.snd f h x' = s') ∧
        ∀ w : ↥(pullback f h), pullback.fst f h w = x → pullback.snd f h w = s' → w = x') ∧
      ((B.pZ z' = D.z ∧ (B.devissage.π ≫ B.devissage.g) z' = s') ∧
        ∀ w : B.devissage.Z, B.pZ w = D.z →
          (B.devissage.π ≫ B.devissage.g) w = s' → w = z') ∧
      ((B.pY y' = D.y ∧ B.devissage.g y' = s') ∧
        ∀ w : B.devissage.Y, B.pY w = D.y → B.devissage.g w = s' → w = y') := by
  let := B.locallyOfFiniteType
  let := B.quasicoherent
  let := B.finiteType
  have hmap : IsIso (h.residueFieldMap s') :=
    IsIso.of_isIso_comp_left (S.residueFieldCongr hs).inv (h.residueFieldMap s')
  have hgyb : D.toOneStepDevissage.g D.y = h s' := D.g_y.trans hs.symm
  obtain ⟨y', hpy, hgy'⟩ := Scheme.exists_preimage_of_isPullback B.y_square D.y s' hgyb
  have hpiz : D.toOneStepDevissage.π D.z = B.pY y' := D.π_z.trans hpy.symm
  obtain ⟨z', hpz, hpiz'⟩ := Scheme.exists_preimage_of_isPullback B.z_square D.z y' hpiz
  have hzs : (B.devissage.π ≫ B.devissage.g) z' = s' := by
    change B.devissage.g (B.devissage.π z') = s'
    rw [hpiz']; exact hgy'
  have hfieldY : IsIso ((S.residueFieldCongr hgyb.symm).inv ≫ h.residueFieldMap s') := by
    simpa [hgyb, D.g_y] using (inferInstance :
      IsIso ((S.residueFieldCongr hs).inv ≫ h.residueFieldMap s'))
  have huy : ∀ w : B.devissage.Y, B.pY w = D.y → B.devissage.g w = s' → w = y' := by
    intro w hw hws
    exact eq_of_isPullback_of_isIso_residueFieldMap B.y_square D.y s' hgyb hfieldY w y' hw hws hpy
      hgy'
  have hmapY : IsIso (h.residueFieldMap (B.devissage.g y')) := by rw [hgy']; exact hmap
  have hpYiso : IsIso (B.pY.residueFieldMap y') :=
    isIso_residueFieldMap_of_isPullback B.y_square y' hmapY
  have hfieldZ : IsIso ((D.toOneStepDevissage.Y.residueFieldCongr hpiz.symm).inv ≫
    B.pY.residueFieldMap y') := inferInstance
  have huz : ∀ w : B.devissage.Z, B.pZ w = D.z →
      (B.devissage.π ≫ B.devissage.g) w = s' → w = z' := by
    intro w hw hws
    have hpyw : B.pY (B.devissage.π w) = D.y := by
      have hc := congrArg (fun k : B.devissage.Z ⟶ D.toOneStepDevissage.Y => k w) B.z_square.w
      simpa [Scheme.Hom.comp_apply, hw, D.π_z] using hc.symm
    have hpiw : B.devissage.π w = y' := huy _ hpyw hws
    exact eq_of_isPullback_of_isIso_residueFieldMap B.z_square D.z y' hpiz hfieldZ w z' hw hpiw hpz
      hpiz'
  have hfst_i : pullback.fst f h (B.devissage.i z') = x := by
    have hc := congrArg (fun k : B.devissage.Z ⟶ X => k z') B.x_square.w
    have hc' : D.toOneStepDevissage.i (B.pZ z') =
        pullback.fst f h (B.devissage.i z') := by simpa using hc
    rw [← hc', hpz, D.i_z]
  have hsnd_i : pullback.snd f h (B.devissage.i z') = s' := by
    calc pullback.snd f h (B.devissage.i z') = (B.devissage.i ≫ pullback.snd f h) z' := rfl
      _ = (B.devissage.π ≫ B.devissage.g) z' :=
        congrArg (fun k : B.devissage.Z ⟶ S' => k z') B.devissage.over_base
      _ = s' := hzs
  have hfieldX : IsIso ((S.residueFieldCongr hs.symm.symm).inv ≫ h.residueFieldMap s') :=
    inferInstance
  refine ⟨B.devissage.i z', z', y', ⟨⟨hfst_i, hsnd_i⟩, fun w hw hws => ?_⟩,
    ⟨⟨hpz, hzs⟩, huz⟩, ⟨⟨hpy, hgy'⟩, huy⟩⟩
  exact pullback_point_eq_of_isIso_residueFieldMap f h x s' hs.symm hfieldX w
    (B.devissage.i z') hw hws hfst_i hsnd_i

/-- **Stacks Project, Tag 05H8.** A one-step dévissage at a point survives an affine pointed
base change which induces an isomorphism of residue fields: the base change of the dévissage
constructed in `AlgebraicGeometry.OneStepDevissage.baseChange` is a one-step dévissage at the
unique point `x'` of the base-changed source lying over `x` and over the new base point, with
distinguished points the unique points `z'` and `y'` of the base-changed closed subscheme and
smooth scheme lying over `z` and `y` and over the new base point. -/
@[stacks 05H8]
theorem exists_baseChange_of_affine {X S S' : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (D : OneStepDevissageAt f F x)
    (s' : S') (h : S' ⟶ S) (hs : h s' = f x) [IsAffine S']
    [IsIso ((S.residueFieldCongr hs).inv ≫ h.residueFieldMap s')] :
    let B := OneStepDevissage.baseChange f F (f x) s' h hs D.toOneStepDevissage
    letI := B.locallyOfFiniteType
    letI := B.quasicoherent
    letI := B.finiteType
    ∃ (x' : ↥(pullback f h)) (z' : B.devissage.Z) (y' : B.devissage.Y)
      (E : OneStepDevissageAt (pullback.snd f h)
        ((Scheme.Modules.pullback (pullback.fst f h)).obj F) x'),
      ((pullback.fst f h x' = x ∧ pullback.snd f h x' = s') ∧
        ∀ w : ↥(pullback f h), pullback.fst f h w = x → pullback.snd f h w = s' → w = x') ∧
      ((B.pZ z' = D.z ∧ (B.devissage.π ≫ B.devissage.g) z' = s') ∧
        ∀ w : B.devissage.Z, B.pZ w = D.z →
          (B.devissage.π ≫ B.devissage.g) w = s' → w = z') ∧
      ((B.pY y' = D.y ∧ B.devissage.g y' = s') ∧
        ∀ w : B.devissage.Y, B.pY w = D.y → B.devissage.g w = s' → w = y') ∧
      HEq E.toOneStepDevissage B.devissage ∧ HEq E.z z' ∧ HEq E.y y' := by
  intro B
  have := B.locallyOfFiniteType
  have := B.quasicoherent
  have := B.finiteType
  obtain ⟨x', z', y', hx, hz, hy⟩ := exists_unique_points_baseChange f F x D s' h hs B
  obtain ⟨E, hEdev, hEz, hEy⟩ := exists_baseChange f F x D s' h hs B x' hx.1.1 hx.1.2 z' hz.1.1
    hz.1.2 y' hy.1.1 hy.1.2
  exact ⟨x', z', y', E, hx, hz, hy, hEdev, hEz, hEy⟩

end OneStepDevissageAt

end AlgebraicGeometry

end
