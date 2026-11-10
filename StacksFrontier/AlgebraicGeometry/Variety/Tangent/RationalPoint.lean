module

public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.TangentFibre

/-!
# Tangent vectors at a rational point as points with values in the dual numbers

Let `k` be a field, `X` a scheme over `k` and `σ : Spec k ⟶ X` a section of the structure
morphism, that is, a `k`-rational point `x` of `X`. The relative tangent space `T_{X/k, x}`,
defined (Stacks 0B2C) through morphisms `Spec κ(x)[ε] ⟶ X`, is in bijection with the set of
morphisms `α : Spec k[ε] ⟶ X` over `k` whose restriction to `Spec k` is `σ`. This is the remark
`κ(e) = k` in the proof of Stacks 0E6G, which reads the tangent space of a group scheme at its
identity as the kernel of `G(k[ε]) ⟶ G(k)`.

## Main definitions

* `AlgebraicGeometry.sectionResidueFieldEquiv`: the identification `κ(x) ≅ k` at a rational point.
* `AlgebraicGeometry.dottedTangentArrowEquivDualNumberPoints`: **the tangent vectors at a
  rational point are the `k[ε]`-points restricting to it.**

## References

* [Stacks Project, Tag 0B2C](https://stacks.math.columbia.edu/tag/0B2C)
* [Stacks Project, Tag 0E6G](https://stacks.math.columbia.edu/tag/0E6G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ p = 𝟙 _)

/-- A morphism `σ : Spec k ⟶ X` factors through the residue-field point `Spec κ(σ(pt)) ⟶ X`
via the canonical homomorphism `κ(σ(pt)) ⟶ k`. -/
theorem specMap_descResidueField_comp_fromSpecResidueField :
    Spec.map (Scheme.descResidueField (Scheme.stalkClosedPointTo σ)) ≫
      X.fromSpecResidueField (σ (closedPoint k)) = σ :=
  Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X σ

include hσ in
/-- For a section `σ` of `p : X ⟶ Spec k`, the homomorphism `k ⟶ κ(σ(pt))` of the composite
`Spec κ(σ(pt)) ⟶ X ⟶ Spec k`, followed by the canonical homomorphism `κ(σ(pt)) ⟶ k`, is the
identity of `k`. -/
theorem fromSpecResidueField_comp_eq_specMap_preimage :
    Spec.preimage (X.fromSpecResidueField (σ (closedPoint k)) ≫ p) ≫
      Scheme.descResidueField (Scheme.stalkClosedPointTo σ) = 𝟙 _ := by
  apply Spec.map_injective
  rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc,
    specMap_descResidueField_comp_fromSpecResidueField, hσ, Spec.map_id]

/-- **The residue field at a rational point is the base field.** For a section `σ` of
`p : X ⟶ Spec k`, the canonical homomorphism `κ(σ(pt)) ⟶ k` through which `σ` factors is an
isomorphism of fields. -/
noncomputable def sectionResidueFieldEquiv : X.residueField (σ (closedPoint k)) ≃+* k :=
  RingEquiv.ofBijective (Scheme.descResidueField (Scheme.stalkClosedPointTo σ)).hom
    ⟨RingHom.injective _, fun z => ⟨(Spec.preimage
      (X.fromSpecResidueField (σ (closedPoint k)) ≫ p)).hom z, by
        simpa using congrArg (fun φ => φ.hom z)
          (fromSpecResidueField_comp_eq_specMap_preimage p σ hσ)⟩⟩

/-- `AlgebraicGeometry.sectionResidueFieldEquiv` is the canonical homomorphism `κ(σ(pt)) ⟶ k`. -/
theorem sectionResidueFieldEquiv_apply (z : X.residueField (σ (closedPoint k))) :
    sectionResidueFieldEquiv p σ hσ z =
      (Scheme.descResidueField (Scheme.stalkClosedPointTo σ)).hom z :=
  rfl

/-- `σ` is the spectrum of `AlgebraicGeometry.sectionResidueFieldEquiv` followed by the
residue-field point `Spec κ(σ(pt)) ⟶ X`. -/
theorem specMap_sectionResidueFieldEquiv_comp_fromSpecResidueField :
    Spec.map (CommRingCat.ofHom (sectionResidueFieldEquiv p σ hσ).toRingHom) ≫
      X.fromSpecResidueField (σ (closedPoint k)) = σ :=
  specMap_descResidueField_comp_fromSpecResidueField σ

/-- The residue-field point `Spec κ(σ(pt)) ⟶ X` followed by `p` is the spectrum of the inverse of
`AlgebraicGeometry.sectionResidueFieldEquiv`. -/
theorem fromSpecResidueField_comp_eq_specMap_sectionResidueFieldEquiv_symm :
    X.fromSpecResidueField (σ (closedPoint k)) ≫ p =
      Spec.map (CommRingCat.ofHom (sectionResidueFieldEquiv p σ hσ).symm.toRingHom) := by
  rw [← Spec.map_preimage (X.fromSpecResidueField (σ (closedPoint k)) ≫ p)]
  congr 1
  ext z
  apply (sectionResidueFieldEquiv p σ hσ).injective
  change _ = sectionResidueFieldEquiv p σ hσ ((sectionResidueFieldEquiv p σ hσ).symm z)
  rw [RingEquiv.apply_symm_apply, sectionResidueFieldEquiv_apply]
  simpa using congrArg (fun φ => φ.hom z) (fromSpecResidueField_comp_eq_specMap_preimage p σ hσ)

/-- The base point of the dual-number arrows at `x` is the residue-field point followed by the
structure morphism. -/
theorem dualNumberBasePoint_eq_comp {S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    dualNumberBasePoint f x = dualNumberToBase _ ≫ X.fromSpecResidueField x ≫ f := by
  rw [dualNumberBasePoint, Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rfl

section DualNumberPoints

variable {κ : Type u} [CommRing κ] (e : κ ≃+* k)

/-- For a ring isomorphism `e : κ ≃+* k`, the structure morphism `Spec k[ε] ⟶ Spec k` is the
transport along `e` of the structure morphism `Spec κ[ε] ⟶ Spec κ`. -/
theorem specMap_dualNumberCongr_comp_dualNumberToBase :
    Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom) ≫ dualNumberToBase κ ≫
      Spec.map (CommRingCat.ofHom e.symm.toRingHom) = dualNumberToBase k := by
  simp only [dualNumberToBase, ← Spec.map_comp]
  congr 1
  ext z <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

/-- The structure morphisms `Spec k[ε] ⟶ Spec k` and `Spec κ[ε] ⟶ Spec κ` commute with the
isomorphisms induced by a ring isomorphism `e : κ ≃+* k`. -/
theorem specMap_dualNumberCongr_symm_comp_dualNumberToBase :
    Spec.map (CommRingCat.ofHom (dualNumberCongr e).symm.toRingHom) ≫ dualNumberToBase k =
      dualNumberToBase κ ≫ Spec.map (CommRingCat.ofHom e.symm.toRingHom) := by
  rw [← specMap_dualNumberCongr_comp_dualNumberToBase e, ← Category.assoc,
    specMap_dualNumberCongr_symm_comp, Category.id_comp]

/-- The closed points `Spec κ ⟶ Spec κ[ε]` and `Spec k ⟶ Spec k[ε]` commute with the isomorphisms
induced by a ring isomorphism `e : κ ≃+* k`. -/
theorem specMap_fstHom_comp_specMap_dualNumberCongr :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k)) ≫
        Spec.map (CommRingCat.ofHom (dualNumberCongr e).toRingHom) =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ)) := by
  simp only [← Spec.map_comp]
  congr 1

/-- The closed points `Spec κ ⟶ Spec κ[ε]` and `Spec k ⟶ Spec k[ε]` commute with the isomorphisms
induced by the inverse of a ring isomorphism `e : κ ≃+* k`. -/
theorem specMap_fstHom_comp_specMap_dualNumberCongr_symm :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom κ κ κ)) ≫
        Spec.map (CommRingCat.ofHom (dualNumberCongr e).symm.toRingHom) =
      Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k)) := by
  simp only [← Spec.map_comp]
  congr 1

/-- The spectra of a ring isomorphism and of its inverse compose to the identity. -/
theorem specMap_ringEquiv_symm_comp :
    Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.toRingHom) =
      𝟙 _ := by
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext z
  simp

end DualNumberPoints

/-- **The tangent vectors at a rational point are the `k[ε]`-points restricting to it.** Let
`σ : Spec k ⟶ X` be a section of `p : X ⟶ Spec k` and `x = σ(pt)`. Transport along the
identification `κ(x) ≅ k` identifies the relative tangent space `T_{X/k, x}` with the morphisms
`α : Spec k[ε] ⟶ X` over `k` whose restriction to `Spec k ⊂ Spec k[ε]` is `σ`. -/
noncomputable def dottedTangentArrowEquivDualNumberPoints :
    DottedTangentArrow p (σ (closedPoint k)) ≃
      { α : Spec (.of (DualNumber k)) ⟶ X //
          α ≫ p = dualNumberToBase k ∧
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k)) ≫ α = σ } where
  toFun θ := ⟨Spec.map (CommRingCat.ofHom
      (dualNumberCongr (sectionResidueFieldEquiv p σ hσ)).toRingHom) ≫ θ.val, by
    rw [Category.assoc, θ.2.2, dualNumberBasePoint_eq_comp]
    exact (congrArg (fun t => Spec.map (CommRingCat.ofHom
      (dualNumberCongr (sectionResidueFieldEquiv p σ hσ)).toRingHom) ≫ dualNumberToBase _ ≫ t)
      (fromSpecResidueField_comp_eq_specMap_sectionResidueFieldEquiv_symm p σ hσ)).trans
      (specMap_dualNumberCongr_comp_dualNumberToBase _), by
    rw [← Category.assoc, specMap_fstHom_comp_specMap_dualNumberCongr, Category.assoc]
    change _ ≫ dualNumberClosedPoint X _ ≫ θ.val = σ
    rw [θ.2.1, specMap_sectionResidueFieldEquiv_comp_fromSpecResidueField]⟩
  invFun α := ⟨Spec.map (CommRingCat.ofHom
      (dualNumberCongr (sectionResidueFieldEquiv p σ hσ)).symm.toRingHom) ≫ α.val, by
    rw [dualNumberClosedPoint, ← Category.assoc, specMap_fstHom_comp_specMap_dualNumberCongr_symm,
      Category.assoc, α.2.2]
    refine (congrArg (fun t => Spec.map (CommRingCat.ofHom
      (sectionResidueFieldEquiv p σ hσ).symm.toRingHom) ≫ t)
      (specMap_sectionResidueFieldEquiv_comp_fromSpecResidueField p σ hσ).symm).trans ?_
    dsimp only
    rw [← Category.assoc, specMap_ringEquiv_symm_comp, Category.id_comp], by
    rw [Category.assoc, α.2.1, specMap_dualNumberCongr_symm_comp_dualNumberToBase,
      dualNumberBasePoint_eq_comp]
    exact (congrArg (fun t => dualNumberToBase _ ≫ t)
      (fromSpecResidueField_comp_eq_specMap_sectionResidueFieldEquiv_symm p σ hσ)).symm⟩
  left_inv θ := by
    refine Subtype.ext ?_
    dsimp only
    rw [← Category.assoc, specMap_dualNumberCongr_symm_comp, Category.id_comp]
  right_inv α := by
    refine Subtype.ext ?_
    dsimp only
    rw [← Category.assoc, specMap_dualNumberCongr_comp_symm, Category.id_comp]

end AlgebraicGeometry
