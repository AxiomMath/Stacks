module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.BaseChange.Points
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.TangentFibre
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.Functorial
public import StacksFrontier.AlgebraicGeometry.Scheme.ResidueFieldMapFromSpec

/-!
# The tangent space of a fibre product

At a point of a fibre product whose two images are rational over their common image in the
base, the relative tangent space of the fibre product is canonically the direct sum of the
relative tangent spaces of the two factors, the isomorphism being given by the tangent maps
of the two projections.

## Main definitions

* `AlgebraicGeometry.TangentSpaceProductEquiv`: the canonical linear equivalence, together
  with its characterization by the projections and by the two fibre inclusions.
* `AlgebraicGeometry.firstFactorArrow`, `AlgebraicGeometry.secondFactorArrow`,
  `AlgebraicGeometry.firstConstantArrow`, `AlgebraicGeometry.secondConstantArrow`: the arrows
  from which those inclusions are built by the universal property of the pullback.
* `AlgebraicGeometry.liftTangentPair`: the tangent arrow of the fibre product determined by a
  pair of tangent arrows of the factors.

## Main results

* `AlgebraicGeometry.tangentSpaceProductEquiv`: the equivalence, at a point of the fibre
  product whose two images are rational over the base.

## Implementation notes

For rational points over the base the two projections induce isomorphisms of residue fields
at the chosen point of the fibre product. Their inverses transport the scalar action on each
factor's tangent space from the residue field of the fibre-product point, so that the product
of the two projection tangent maps is linear. The inverse equivalence is specified on each
summand as the pullback lift of the transported tangent arrow on that factor against the
constant arrow at the point of the other factor.

## References

* [Stacks Project, Tag 0BEB](https://stacks.math.columbia.edu/tag/0BEB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- If `f` induces an isomorphism of residue fields at the image of `z` in `X`, then the second
projection of `pullback f g` induces an isomorphism of residue fields at `z`. -/
lemma snd_residueFieldMap_isIso_of_fst {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : (pullback f g : Scheme).carrier)
    (hfx : IsIso (f.residueFieldMap (pullback.fst f g z))) :
    IsIso ((pullback.snd f g).residueFieldMap z) := by
  let T : Scheme.Pullback.Triplet f g := Scheme.Pullback.Triplet.ofPoint z
  let p := Scheme.Pullback.SpecOfPoint z
  have : IsIso (f.residueFieldMap T.x) := hfx
  have : IsIso ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x) := by infer_instance
  have : IsIso T.tensorInr := by
    show IsIso (pushout.inr
      ((S.residueFieldCongr T.hx).inv ≫ f.residueFieldMap T.x)
      ((S.residueFieldCongr T.hy).inv ≫ g.residueFieldMap T.y))
    apply CategoryTheory.Limits.pushout_inr_iso_of_left_iso
  let : Field T.tensor :=
    (MulEquiv.isField (Field.toIsField (Y.residueField T.y))
      (asIso T.tensorInr).symm.commRingCatIsoToRingEquiv.toMulEquiv).toField
  have : IsOpenImmersion (Spec.map T.tensorInr) := by infer_instance
  let q := T.SpecTensorTo
  have := Scheme.Pullback.isIso_residueFieldMap_specTensorTo_comp_residueFieldIso T p
  have : IsIso (q.residueFieldMap p) :=
    IsIso.of_isIso_comp_right _ (Scheme.Spec.residueFieldIso T.tensor p).hom
  have hptComp : (q ≫ pullback.snd f g) p =
      (Spec.map T.tensorInr ≫ Y.fromSpecResidueField T.y) p := by
    rw [T.specTensorTo_snd]
  have hcomp : IsIso ((pullback.snd f g).residueFieldMap (q p) ≫ q.residueFieldMap p) := by
    rw [← Scheme.residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr T.specTensorTo_snd p,
      Scheme.residueFieldMap_comp]
    show IsIso ((Y.residueFieldCongr hptComp).hom ≫
      (Y.fromSpecResidueField T.y).residueFieldMap ((Spec.map T.tensorInr) p) ≫
      (Spec.map T.tensorInr).residueFieldMap p)
    exact IsIso.comp_isIso' (Y.residueFieldCongr hptComp).isIso_hom
      (IsIso.comp_isIso' (isIso_residueFieldMap_fromSpecResidueField Y T.y
        (Spec.map T.tensorInr p)) inferInstance)
  have := IsIso.of_isIso_comp_right ((pullback.snd f g).residueFieldMap (q p)) (q.residueFieldMap p)
  rwa [Scheme.Pullback.SpecTensorTo_SpecOfPoint z] at this

/-- If `g` induces an isomorphism of residue fields at the image of `z` in `Y`, then the first
projection of `pullback f g` induces an isomorphism of residue fields at `z`. -/
lemma fst_residueFieldMap_isIso_of_snd {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : (pullback f g : Scheme).carrier)
    (hgy : IsIso (g.residueFieldMap (pullback.snd f g z))) :
    IsIso ((pullback.fst f g).residueFieldMap z) := by
  have hpoint : pullback.fst g f ((pullbackSymmetry f g).hom z) = pullback.snd f g z :=
    congrArg (fun k : pullback f g ⟶ Y => k z) (pullbackSymmetry_hom_comp_fst f g)
  have hg' : IsIso (g.residueFieldMap (pullback.fst g f ((pullbackSymmetry f g).hom z))) := by
    rwa [hpoint]
  rw [← pullbackSymmetry_hom_comp_snd f g, Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' (snd_residueFieldMap_isIso_of_fst g f _ hg') inferInstance

/-- Transport a tangent arrow on the first factor to the residue field of a
point of the fibre product. -/
noncomputable def firstFactorArrow {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g))
    [IsIso ((pullback.fst f g).residueFieldMap z)]
    (v : DottedTangentArrow f (pullback.fst f g z)) :
    Spec (.of (DualNumber ((pullback f g).residueField z))) ⟶ X :=
  Spec.map (CommRingCat.ofHom
    (dualNumberCongr
      (asIso ((pullback.fst f g).residueFieldMap z)).commRingCatIsoToRingEquiv).toRingHom) ≫ v.val

/-- The constant arrow at the second point, over the residue field of the
fibre-product point. -/
noncomputable def secondConstantArrow {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g)) :
    Spec (.of (DualNumber ((pullback f g).residueField z))) ⟶ Y :=
  dualNumberToBase ((pullback f g).residueField z) ≫
    Spec.map ((pullback.snd f g).residueFieldMap z) ≫
      Y.fromSpecResidueField (pullback.snd f g z)

/-- The constant arrow at the first point, over the residue field of the
fibre-product point. -/
noncomputable def firstConstantArrow {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g)) :
    Spec (.of (DualNumber ((pullback f g).residueField z))) ⟶ X :=
  dualNumberToBase ((pullback f g).residueField z) ≫
    Spec.map ((pullback.fst f g).residueFieldMap z) ≫
      X.fromSpecResidueField (pullback.fst f g z)

/-- Transport a tangent arrow on the second factor to the residue field of a
point of the fibre product. -/
noncomputable def secondFactorArrow {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g))
    [IsIso ((pullback.snd f g).residueFieldMap z)]
    (v : DottedTangentArrow g (pullback.snd f g z)) :
    Spec (.of (DualNumber ((pullback f g).residueField z))) ⟶ Y :=
  Spec.map (CommRingCat.ofHom
    (dualNumberCongr
      (asIso ((pullback.snd f g).residueFieldMap z)).commRingCatIsoToRingEquiv).toRingHom) ≫ v.val

/-- The canonical linear product decomposition of tangent spaces, characterized by its
two projection maps. -/
structure TangentSpaceProductEquiv {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g)) where
  /-- The first projection induces an isomorphism of residue fields at `z`. -/
  fst_residueField_isIso : IsIso ((pullback.fst f g).residueFieldMap z)
  /-- The second projection induces an isomorphism of residue fields at `z`. -/
  snd_residueField_isIso : IsIso ((pullback.snd f g).residueFieldMap z)
  /-- The linear equivalence of the relative tangent space of the fibre product with the
  product of the relative tangent spaces of the two factors. -/
  toLinearEquiv :
    letI : Module ((pullback f g).residueField z)
        (DottedTangentArrow f (pullback.fst f g z)) :=
      Module.compHom _ (inv ((pullback.fst f g).residueFieldMap z)).hom
    letI : Module ((pullback f g).residueField z)
        (DottedTangentArrow g (pullback.snd f g z)) :=
      Module.compHom _ (inv ((pullback.snd f g).residueFieldMap z)).hom
    DottedTangentArrow (pullback.fst f g ≫ f) z ≃ₗ[((pullback f g).residueField z)]
      (DottedTangentArrow f (pullback.fst f g z) ×
        DottedTangentArrow g (pullback.snd f g z))
  /-- The equivalence has the two projection tangent maps as its components. -/
  toLinearEquiv_apply (v : DottedTangentArrow (pullback.fst f g ≫ f) z) :
    letI := fst_residueField_isIso
    letI := snd_residueField_isIso
    letI : Module ((pullback f g).residueField z)
        (DottedTangentArrow f (pullback.fst f g z)) :=
      Module.compHom _ (inv ((pullback.fst f g).residueFieldMap z)).hom
    letI : Module ((pullback f g).residueField z)
        (DottedTangentArrow g (pullback.snd f g z)) :=
      Module.compHom _ (inv ((pullback.snd f g).residueFieldMap z)).hom
    toLinearEquiv v =
      (tangentMap (pullback.fst f g) (pullback.fst f g ≫ f) f rfl z v,
        tangentMap (pullback.snd f g) (pullback.fst f g ≫ f) g
          (pullback.condition).symm z v)
  /-- The transported tangent arrow on the first factor and the constant arrow at the second
  point agree over the base, so they lift to the fibre product. -/
  first_inclusion_condition (v : DottedTangentArrow f (pullback.fst f g z)) :
    letI := fst_residueField_isIso
    firstFactorArrow f g z v ≫ f = secondConstantArrow f g z ≫ g
  /-- On the first summand the inverse equivalence is that lift. -/
  first_inclusion_apply (v : DottedTangentArrow f (pullback.fst f g z)) :
    letI := fst_residueField_isIso
    letI := snd_residueField_isIso
    letI : Module ((pullback f g).residueField z)
        (DottedTangentArrow f (pullback.fst f g z)) :=
      Module.compHom _ (inv ((pullback.fst f g).residueFieldMap z)).hom
    letI : Module ((pullback f g).residueField z)
        (DottedTangentArrow g (pullback.snd f g z)) :=
      Module.compHom _ (inv ((pullback.snd f g).residueFieldMap z)).hom
    (toLinearEquiv.symm (v, 0)).val =
      pullback.lift (firstFactorArrow f g z v) (secondConstantArrow f g z)
        (first_inclusion_condition v)
  /-- The constant arrow at the first point and the transported tangent arrow on the second
  factor agree over the base, so they lift to the fibre product. -/
  second_inclusion_condition (v : DottedTangentArrow g (pullback.snd f g z)) :
    letI := snd_residueField_isIso
    firstConstantArrow f g z ≫ f = secondFactorArrow f g z v ≫ g
  /-- On the second summand the inverse equivalence is that lift. -/
  second_inclusion_apply (v : DottedTangentArrow g (pullback.snd f g z)) :
    letI := fst_residueField_isIso
    letI := snd_residueField_isIso
    letI : Module ((pullback f g).residueField z)
        (DottedTangentArrow f (pullback.fst f g z)) :=
      Module.compHom _ (inv ((pullback.fst f g).residueFieldMap z)).hom
    letI : Module ((pullback f g).residueField z)
        (DottedTangentArrow g (pullback.snd f g z)) :=
      Module.compHom _ (inv ((pullback.snd f g).residueFieldMap z)).hom
    (toLinearEquiv.symm (0, v)).val =
      pullback.lift (firstConstantArrow f g z) (secondFactorArrow f g z v)
      (second_inclusion_condition v)

/-- The structure morphisms `Spec R[ε] ⟶ Spec R` are natural with respect to a ring isomorphism
`R ≃+* K`. -/
lemma dualNumberToBase_natural {R K : Type u} [CommRing R] [CommRing K]
    (e : R ≃+* K) :
    (Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom) :
        Spec (.of (DualNumber K)) ⟶ Spec (.of (DualNumber R))) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) :
          Spec (.of (DualNumber R)) ⟶ Spec (.of R)) =
      (Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) :
          Spec (.of (DualNumber K)) ⟶ Spec (.of K)) ≫
        (Spec.map (CommRingCat.ofHom e.toRingHom) : Spec (.of K) ⟶ Spec (.of R)) := by
  simp only [← Spec.map_comp]
  have hRing : CommRingCat.ofHom (algebraMap R (DualNumber R)) ≫
      CommRingCat.ofHom (dualNumberCongr e).toRingHom =
      CommRingCat.ofHom e.toRingHom ≫
        CommRingCat.ofHom (algebraMap K (DualNumber K)) := by
    ext x
    · rfl
    · exact map_zero e
  simpa only [Spec.map_comp] using congrArg Spec.map hRing

/-- The first-component maps `R[ε] → R` are natural with respect to a ring isomorphism
`R ≃+* K`. -/
private lemma dualNumberFstHom_natural {R K : Type u} [CommRing R] [CommRing K] (e : R ≃+* K) :
    CommRingCat.ofHom (dualNumberCongr e).toRingHom ≫
        CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom =
      CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom ≫
        CommRingCat.ofHom e.toRingHom := by
  ext w <;> rfl

/-- The transported tangent arrow on the first factor lies over the base point of the fibre
product in `S`. -/
lemma firstFactorArrow_basePoint {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g))
    [IsIso ((pullback.fst f g).residueFieldMap z)]
    (v : DottedTangentArrow f (pullback.fst f g z)) :
    firstFactorArrow f g z v ≫ f =
      dualNumberBasePoint (pullback.fst f g ≫ f) z := by
  dsimp [firstFactorArrow]
  rw [Category.assoc, v.property.2]
  unfold dualNumberBasePoint
  have hNat := dualNumberToBase_natural
    (asIso ((pullback.fst f g).residueFieldMap z)).commRingCatIsoToRingEquiv
  simp only [RingEquiv.toRingHom_eq_coe] at hNat
  rw [← Category.assoc]
  simp only [hNat]
  simp

/-- The canonical morphism from the residue field of a point of `pullback f g` to `S` through the
second factor agrees with the one through the base. -/
private lemma fromSpecResidueField_pullback_snd_comp {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g)) :
    (pullback f g).fromSpecResidueField z ≫ pullback.snd f g ≫ g =
      Spec.map ((pullback.fst f g ≫ f).residueFieldMap z) ≫
        S.fromSpecResidueField ((pullback.fst f g ≫ f) z) := by
  rw [← pullback.condition]
  exact (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField (pullback.fst f g ≫ f) z).symm

/-- The transported tangent arrow on the second factor lies over the base point of the fibre
product in `S`. -/
lemma secondFactorArrow_basePoint {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g))
    [IsIso ((pullback.snd f g).residueFieldMap z)]
    (v : DottedTangentArrow g (pullback.snd f g z)) :
    secondFactorArrow f g z v ≫ g =
      dualNumberBasePoint (pullback.fst f g ≫ f) z := by
  dsimp [secondFactorArrow]
  rw [Category.assoc, v.property.2]
  unfold dualNumberBasePoint
  have hNat := dualNumberToBase_natural
    (asIso ((pullback.snd f g).residueFieldMap z)).commRingCatIsoToRingEquiv
  simp only [RingEquiv.toRingHom_eq_coe] at hNat
  rw [← Category.assoc]
  simp only [hNat]
  have hProj :
      Spec.map ((pullback.snd f g).residueFieldMap z) ≫
          Spec.map (g.residueFieldMap (pullback.snd f g z)) ≫
          S.fromSpecResidueField (g (pullback.snd f g z)) =
        (pullback f g).fromSpecResidueField z ≫ pullback.snd f g ≫ g := by
    rw [Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField g (pullback.snd f g z),
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc (pullback.snd f g) z]
  exact congrArg (fun k => dualNumberToBase ((pullback f g).residueField z) ≫ k)
    (hProj.trans (fromSpecResidueField_pullback_snd_comp f g z))

/-- The constant arrow at the first point lies over the base point of the fibre product in `S`. -/
lemma firstConstantArrow_basePoint {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g)) :
    firstConstantArrow f g z ≫ f =
      dualNumberBasePoint (pullback.fst f g ≫ f) z := by
  dsimp [firstConstantArrow, dualNumberBasePoint, dualNumberToBase]
  simp

/-- The constant arrow at the second point lies over the base point of the fibre product in `S`. -/
lemma secondConstantArrow_basePoint {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g)) :
    secondConstantArrow f g z ≫ g =
      dualNumberBasePoint (pullback.fst f g ≫ f) z := by
  dsimp [secondConstantArrow, dualNumberBasePoint, dualNumberToBase]
  simpa [dualNumberToBase] using
    congrArg (fun k => dualNumberToBase ((pullback f g).residueField z) ≫ k)
      (fromSpecResidueField_pullback_snd_comp f g z)

/-- The transported tangent arrow on the first factor restricts on the closed point to the
canonical morphism from the residue field of `z` composed with the first projection. -/
lemma firstFactorArrow_closedPoint {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g))
    [IsIso ((pullback.fst f g).residueFieldMap z)]
    (v : DottedTangentArrow f (pullback.fst f g z)) :
    dualNumberClosedPoint (pullback f g) z ≫
        firstFactorArrow f g z v =
      (pullback f g).fromSpecResidueField z ≫ pullback.fst f g := by
  let e := (asIso ((pullback.fst f g).residueFieldMap z)).commRingCatIsoToRingEquiv
  have hClosed : dualNumberClosedPoint (pullback f g) z ≫
      Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom) =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        dualNumberClosedPoint X (pullback.fst f g z) := by
    dsimp [dualNumberClosedPoint]
    simpa only [AlgHom.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe,
      Spec.map_comp] using congrArg Spec.map (dualNumberFstHom_natural e)
  calc
    _ = (dualNumberClosedPoint (pullback f g) z ≫
        Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom)) ≫ v.val := by
          simp [firstFactorArrow]
    _ = (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        dualNumberClosedPoint X (pullback.fst f g z)) ≫ v.val := by
          rw [hClosed]
    _ = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        X.fromSpecResidueField (pullback.fst f g z) := by
          simp [v.property.1]
    _ = (pullback f g).fromSpecResidueField z ≫ pullback.fst f g := by
          simp [e]

/-- The transported tangent arrow on the second factor restricts on the closed point to the
canonical morphism from the residue field of `z` composed with the second projection. -/
lemma secondFactorArrow_closedPoint {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g))
    [IsIso ((pullback.snd f g).residueFieldMap z)]
    (v : DottedTangentArrow g (pullback.snd f g z)) :
    dualNumberClosedPoint (pullback f g) z ≫
        secondFactorArrow f g z v =
      (pullback f g).fromSpecResidueField z ≫ pullback.snd f g := by
  let e := (asIso ((pullback.snd f g).residueFieldMap z)).commRingCatIsoToRingEquiv
  have hClosed : dualNumberClosedPoint (pullback f g) z ≫
      Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom) =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        dualNumberClosedPoint Y (pullback.snd f g z) := by
    dsimp [dualNumberClosedPoint]
    simpa only [AlgHom.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe,
      Spec.map_comp] using congrArg Spec.map (dualNumberFstHom_natural e)
  calc
    _ = (dualNumberClosedPoint (pullback f g) z ≫
        Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom)) ≫ v.val := by
          simp [secondFactorArrow]
    _ = (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        dualNumberClosedPoint Y (pullback.snd f g z)) ≫ v.val := by
          rw [hClosed]
    _ = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Y.fromSpecResidueField (pullback.snd f g z) := by
          simp [v.property.1]
    _ = (pullback f g).fromSpecResidueField z ≫ pullback.snd f g := by
          simp [e]

/-- The tangent arrow of the fibre product at `z` obtained by lifting the transported tangent
arrows `v` and `w` of the two factors through the pullback. -/
noncomputable def liftTangentPair {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g))
    [IsIso ((pullback.fst f g).residueFieldMap z)]
    [IsIso ((pullback.snd f g).residueFieldMap z)]
    (v : DottedTangentArrow f (pullback.fst f g z))
    (w : DottedTangentArrow g (pullback.snd f g z)) :
    DottedTangentArrow (pullback.fst f g ≫ f) z := by
  let a := firstFactorArrow f g z v
  let b := secondFactorArrow f g z w
  have hbase : a ≫ f = b ≫ g :=
    (firstFactorArrow_basePoint f g z v).trans (secondFactorArrow_basePoint f g z w).symm
  refine ⟨pullback.lift a b hbase, ?_, ?_⟩
  · apply pullback.hom_ext
    · simpa [a, pullback.lift_fst] using
        firstFactorArrow_closedPoint f g z v
    · simpa [b, pullback.lift_snd] using
        secondFactorArrow_closedPoint f g z w
  · change pullback.lift a b hbase ≫ pullback.fst f g ≫ f =
      dualNumberBasePoint (pullback.fst f g ≫ f) z
    rw [← Category.assoc, pullback.lift_fst]
    exact firstFactorArrow_basePoint f g z v

/-- The tangent map of the first projection sends `liftTangentPair f g z v w` to `v`. -/
lemma tangentMap_fst_liftTangentPair {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g))
    [IsIso ((pullback.fst f g).residueFieldMap z)]
    [IsIso ((pullback.snd f g).residueFieldMap z)]
    (v : DottedTangentArrow f (pullback.fst f g z))
    (w : DottedTangentArrow g (pullback.snd f g z)) :
    tangentMap (pullback.fst f g) (pullback.fst f g ≫ f) f rfl z
      (liftTangentPair f g z v w) = v := by
  apply Subtype.ext
  let e := (asIso ((pullback.fst f g).residueFieldMap z)).commRingCatIsoToRingEquiv
  let α := (dualNumberCongr e.symm).toRingHom
  have hMap : Spec.map (CommRingCat.ofHom α) ≫
      Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom) = 𝟙 _ :=
    specMap_dualNumberCongr_symm_comp e
  rw [tangentMap_apply (pullback.fst f g)
    (pullback.fst f g ≫ f) f rfl z (liftTangentPair f g z v w) α
    (fun ⟨_, _⟩ => rfl) (fun ⟨_, _⟩ => rfl)]
  calc
    _ = (Spec.map (CommRingCat.ofHom α) ≫
          Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom)) ≫ v.val := by
            simp [liftTangentPair, firstFactorArrow, α, pullback.lift_fst]
    _ = v.val := by rw [hMap, Category.id_comp]

/-- The tangent map of the second projection sends `liftTangentPair f g z v w` to `w`. -/
lemma tangentMap_snd_liftTangentPair {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g))
    [IsIso ((pullback.fst f g).residueFieldMap z)]
    [IsIso ((pullback.snd f g).residueFieldMap z)]
    (v : DottedTangentArrow f (pullback.fst f g z))
    (w : DottedTangentArrow g (pullback.snd f g z)) :
    tangentMap (pullback.snd f g) (pullback.fst f g ≫ f) g
      (pullback.condition).symm z (liftTangentPair f g z v w) = w := by
  apply Subtype.ext
  let e := (asIso ((pullback.snd f g).residueFieldMap z)).commRingCatIsoToRingEquiv
  let α := (dualNumberCongr e.symm).toRingHom
  have hMap : Spec.map (CommRingCat.ofHom α) ≫
      Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom) = 𝟙 _ :=
    specMap_dualNumberCongr_symm_comp e
  rw [tangentMap_apply (pullback.snd f g)
    (pullback.fst f g ≫ f) g (pullback.condition).symm z (liftTangentPair f g z v w) α
    (fun ⟨_, _⟩ => rfl) (fun ⟨_, _⟩ => rfl)]
  calc
    _ = (Spec.map (CommRingCat.ofHom α) ≫
          Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom)) ≫ w.val := by
            simp [liftTangentPair, secondFactorArrow, α, pullback.lift_snd]
    _ = w.val := by rw [hMap, Category.id_comp]

/-- The transport of the zero tangent arrow on the second factor is the constant arrow at the
second point. -/
lemma secondFactorArrow_zero {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g))
    [IsIso ((pullback.snd f g).residueFieldMap z)] :
    secondFactorArrow f g z (0 : DottedTangentArrow g (pullback.snd f g z)) =
      secondConstantArrow f g z := by
  dsimp [secondFactorArrow, secondConstantArrow]
  rw [(dottedTangentArrowModule g (pullback.snd f g z)).zero_apply]
  have hNat := dualNumberToBase_natural
    (asIso ((pullback.snd f g).residueFieldMap z)).commRingCatIsoToRingEquiv
  simp only [RingEquiv.toRingHom_eq_coe] at hNat
  unfold dualNumberToBase
  simpa using congrArg
    (fun k => k ≫ Y.fromSpecResidueField (pullback.snd f g z)) hNat

/-- The transport of the zero tangent arrow on the first factor is the constant arrow at the
first point. -/
lemma firstFactorArrow_zero {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g))
    [IsIso ((pullback.fst f g).residueFieldMap z)] :
    firstFactorArrow f g z (0 : DottedTangentArrow f (pullback.fst f g z)) =
      firstConstantArrow f g z := by
  dsimp [firstFactorArrow, firstConstantArrow]
  rw [(dottedTangentArrowModule f (pullback.fst f g z)).zero_apply]
  have hNat := dualNumberToBase_natural
    (asIso ((pullback.fst f g).residueFieldMap z)).commRingCatIsoToRingEquiv
  simp only [RingEquiv.toRingHom_eq_coe] at hNat
  unfold dualNumberToBase
  simpa using congrArg
    (fun k => k ≫ X.fromSpecResidueField (pullback.fst f g z)) hNat

/-- The closed point `Spec K ⟶ Spec K[ε]` followed by the structure morphism
`Spec K[ε] ⟶ Spec K` is the identity. -/
lemma dualNumberClosedPoint_dualNumberToBase_spec (K : Type u) [CommRing K] :
    Spec.map (CommRingCat.ofHom
      (TrivSqZeroExt.fstHom K K K).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K))) = 𝟙 (Spec (.of K)) := by
  have hRing : CommRingCat.ofHom (algebraMap K (DualNumber K)) ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom =
      𝟙 (CommRingCat.of K) := by
    apply CommRingCat.hom_ext
    ext x
    simp
  simpa only [Spec.map_comp, Spec.map_id] using congrArg Spec.map hRing

/-- The constant arrow at the first point restricts on the closed point to the canonical
morphism from the residue field of `z` composed with the first projection. -/
lemma firstConstantArrow_closedPoint {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g)) :
    dualNumberClosedPoint (pullback f g) z ≫ firstConstantArrow f g z =
      (pullback f g).fromSpecResidueField z ≫ pullback.fst f g := by
  dsimp [firstConstantArrow, dualNumberClosedPoint,
    dualNumberToBase]
  calc
    _ = (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom
          ((pullback f g).residueField z) ((pullback f g).residueField z)
          ((pullback f g).residueField z)).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap ((pullback f g).residueField z)
            (DualNumber ((pullback f g).residueField z))))) ≫
          Spec.map ((pullback.fst f g).residueFieldMap z) ≫
          X.fromSpecResidueField (pullback.fst f g z) := by simp
    _ = Spec.map ((pullback.fst f g).residueFieldMap z) ≫
          X.fromSpecResidueField (pullback.fst f g z) := by
            rw [dualNumberClosedPoint_dualNumberToBase_spec, Category.id_comp]
    _ = _ := Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField
      (pullback.fst f g) z

/-- The constant arrow at the second point restricts on the closed point to the canonical
morphism from the residue field of `z` composed with the second projection. -/
lemma secondConstantArrow_closedPoint {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g)) :
    dualNumberClosedPoint (pullback f g) z ≫ secondConstantArrow f g z =
      (pullback f g).fromSpecResidueField z ≫ pullback.snd f g := by
  dsimp [secondConstantArrow, dualNumberClosedPoint,
    dualNumberToBase]
  calc
    _ = (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom
          ((pullback f g).residueField z) ((pullback f g).residueField z)
          ((pullback f g).residueField z)).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (algebraMap ((pullback f g).residueField z)
            (DualNumber ((pullback f g).residueField z))))) ≫
          Spec.map ((pullback.snd f g).residueFieldMap z) ≫
          Y.fromSpecResidueField (pullback.snd f g z) := by simp
    _ = Spec.map ((pullback.snd f g).residueFieldMap z) ≫
          Y.fromSpecResidueField (pullback.snd f g z) := by
            rw [dualNumberClosedPoint_dualNumberToBase_spec, Category.id_comp]
    _ = _ := Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField
      (pullback.snd f g) z

/-- The tangent space of a fibre product at a pair of points rational over the same base point
is the direct sum of the tangent spaces of the factors. The equivalence is induced by the
projections. -/
@[stacks 0BEB]
noncomputable def tangentSpaceProductEquiv {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (z : ↑(pullback f g))
    [IsIso (f.residueFieldMap (pullback.fst f g z))]
    [IsIso (g.residueFieldMap (pullback.snd f g z))] :
    TangentSpaceProductEquiv f g z := by
  have hfst : IsIso ((pullback.fst f g).residueFieldMap z) :=
    fst_residueFieldMap_isIso_of_snd f g z inferInstance
  have hsnd : IsIso ((pullback.snd f g).residueFieldMap z) :=
    snd_residueFieldMap_isIso_of_fst f g z inferInstance
  let K := (pullback f g).residueField z
  let A := DottedTangentArrow (pullback.fst f g ≫ f) z
  let B := DottedTangentArrow f (pullback.fst f g z)
  let C := DottedTangentArrow g (pullback.snd f g z)
  letI : Module K B :=
    Module.compHom _ (inv ((pullback.fst f g).residueFieldMap z)).hom
  letI : Module K C :=
    Module.compHom _ (inv ((pullback.snd f g).residueFieldMap z)).hom
  let T₁ := tangentMap (pullback.fst f g) (pullback.fst f g ≫ f) f rfl z
  let T₂ := tangentMap (pullback.snd f g) (pullback.fst f g ≫ f) g
    (pullback.condition).symm z
  let L : A →ₗ[K] B × C := {
    toFun := fun t => (T₁ t, T₂ t)
    map_add' := fun x y => Prod.ext (T₁.map_add x y) (T₂.map_add x y)
    map_smul' := fun r x => Prod.ext (T₁.map_smulₛₗ r x) (T₂.map_smulₛₗ r x) }
  have hbij : Function.Bijective L := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      apply pullback.hom_ext
      · let e := (asIso ((pullback.fst f g).residueFieldMap z)).commRingCatIsoToRingEquiv
        let α := (dualNumberCongr e.symm).toRingHom
        have hxy' : (T₁ x).val = (T₁ y).val := congrArg (fun p : B × C => p.1.val) hxy
        have hx := tangentMap_apply (pullback.fst f g)
          (pullback.fst f g ≫ f) f rfl z x α
          (by intro d; rcases d with ⟨a, b⟩; rfl)
          (by intro d; rcases d with ⟨a, b⟩; rfl)
        have hy := tangentMap_apply (pullback.fst f g)
          (pullback.fst f g ≫ f) f rfl z y α
          (by intro d; rcases d with ⟨a, b⟩; rfl)
          (by intro d; rcases d with ⟨a, b⟩; rfl)
        rw [hx, hy] at hxy'
        have : IsIso (CommRingCat.ofHom α) := by
          rw [ConcreteCategory.isIso_iff_bijective]
          exact (dualNumberCongr e.symm).bijective
        have : IsIso (Spec.map (CommRingCat.ofHom α)) := by infer_instance
        exact (cancel_epi (Spec.map (CommRingCat.ofHom α))).1 hxy'
      · let e := (asIso ((pullback.snd f g).residueFieldMap z)).commRingCatIsoToRingEquiv
        let α := (dualNumberCongr e.symm).toRingHom
        have hxy' : (T₂ x).val = (T₂ y).val := congrArg (fun p : B × C => p.2.val) hxy
        have hx := tangentMap_apply (pullback.snd f g)
          (pullback.fst f g ≫ f) g (pullback.condition).symm z x α
          (by intro d; rcases d with ⟨a, b⟩; rfl)
          (by intro d; rcases d with ⟨a, b⟩; rfl)
        have hy := tangentMap_apply (pullback.snd f g)
          (pullback.fst f g ≫ f) g (pullback.condition).symm z y α
          (by intro d; rcases d with ⟨a, b⟩; rfl)
          (by intro d; rcases d with ⟨a, b⟩; rfl)
        rw [hx, hy] at hxy'
        have : IsIso (CommRingCat.ofHom α) := by
          rw [ConcreteCategory.isIso_iff_bijective]
          exact (dualNumberCongr e.symm).bijective
        have : IsIso (Spec.map (CommRingCat.ofHom α)) := by infer_instance
        exact (cancel_epi (Spec.map (CommRingCat.ofHom α))).1 hxy'
    · intro p
      rcases p with ⟨v, w⟩
      refine ⟨liftTangentPair f g z v w, ?_⟩
      change (T₁ (liftTangentPair f g z v w), T₂ (liftTangentPair f g z v w)) = (v, w)
      exact Prod.ext (tangentMap_fst_liftTangentPair f g z v w)
        (tangentMap_snd_liftTangentPair f g z v w)
  let e : A ≃ₗ[K] B × C := LinearEquiv.ofBijective L hbij
  refine {
    fst_residueField_isIso := hfst
    snd_residueField_isIso := hsnd
    toLinearEquiv := e
    toLinearEquiv_apply := fun _ => rfl
    first_inclusion_condition := fun v =>
      (firstFactorArrow_basePoint f g z v).trans (secondConstantArrow_basePoint f g z).symm
    first_inclusion_apply := ?_
    second_inclusion_condition := fun v =>
      (firstConstantArrow_basePoint f g z).trans (secondFactorArrow_basePoint f g z v).symm
    second_inclusion_apply := ?_
  }
  · intro v
    have hi : e (liftTangentPair f g z v 0) = (v, 0) :=
      Prod.ext (tangentMap_fst_liftTangentPair f g z v 0) (tangentMap_snd_liftTangentPair f g z v 0)
    change (e.symm (v, 0)).val = _
    rw [← hi, LinearEquiv.symm_apply_apply]
    simp [liftTangentPair, secondFactorArrow_zero]
  · intro v
    have hi : e (liftTangentPair f g z 0 v) = (0, v) :=
      Prod.ext (tangentMap_fst_liftTangentPair f g z 0 v) (tangentMap_snd_liftTangentPair f g z 0 v)
    change (e.symm (0, v)).val = _
    rw [← hi, LinearEquiv.symm_apply_apply]
    simp [liftTangentPair, firstFactorArrow_zero]

end AlgebraicGeometry

end
