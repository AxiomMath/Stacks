module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.GeometricPointStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.NeighborhoodsStalksPoints.Basic
public import StacksFrontier.RingTheory.WeaklyEtale.ResidueField
public import StacksCore.Tactic.StacksAttribute

/-!
# Geometric points lift to pro-étale coverings

Given a geometric point of a scheme and a pro-étale covering family, some member of the family
admits a geometric point mapping to the original one.

## Main results

* `AlgebraicGeometry.ProEtale.exists_geometricPoint_lift_of_proetaleCover` gives a lift of a
  geometric point to one member of a pro-étale covering family.
* `AlgebraicGeometry.ProEtale.weaklyEtale_spec_iff` compares weak étaleness of a morphism of
  affine schemes with weak étaleness of the corresponding algebra.
* `AlgebraicGeometry.ProEtale.weaklyEtale_localization` and
  `AlgebraicGeometry.weaklyEtale_fromSpecStalk` say a localization is weakly étale and
  that the canonical morphism from the spectrum of a stalk is weakly étale.
* `AlgebraicGeometry.ProEtale.weaklyEtale_stalkMap` says a weakly étale morphism induces weakly
  étale maps of local rings.

## Implementation notes

The covering family is represented by its presieve of arrows in Mathlib's pro-étale
precoverage. The lifted geometric point maps to the given point by composition with the chosen
covering morphism.

The lift is built on the residue fields of the two schemes at the relevant points: the residue
field extension induced by a weakly étale morphism is separable algebraic, so the algebraically
closed field of the given geometric point receives the residue field upstairs. The auxiliary
results reduce weak étaleness of the canonical morphism from the spectrum of a stalk to weak
étaleness of a localization.

## References

* [Stacks Project, Tag 0F6C](https://stacks.math.columbia.edu/tag/0F6C)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ProEtale

/-- A localization of a commutative ring is weakly étale over it. -/
public theorem weaklyEtale_localization (R T : Type u) [CommRing R] [CommRing T]
    [Algebra R T] (M : Submonoid R) [IsLocalization M T] :
    Algebra.WeaklyEtale R T := by
  refine ⟨IsLocalization.flat T M, ?_⟩
  apply RingHom.Flat.of_bijective
  convert IsLocalization.bijective_linearMap_mul' M T using 1
  rfl

/-- A morphism of affine schemes is weakly étale exactly when the corresponding ring map is. -/
public theorem weaklyEtale_spec_iff (R S : Type u) [CommRing R] [CommRing S]
    (f : R →+* S) :
    WeaklyEtale (Spec.map (CommRingCat.ofHom f)) ↔
      @Algebra.WeaklyEtale R S _ _ f.toAlgebra := by
  let : Algebra R S := f.toAlgebra
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine ⟨(Flat.SpecMap_iff).mp h.flat, ?_⟩
    have hd := h.flat_diagonal
    rw [AlgebraicGeometry.diagonal_SpecMap] at hd
    have hm : Flat (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.lmul' R (S := S)).toRingHom)) := by
      let e := AlgebraicGeometry.pullbackSpecIso R S S
      have hdiag : Flat (Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.lmul' R (S := S)).toRingHom) ≫ e.inv) := by
        simpa [e] using hd
      have hcomp : Flat ((Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.lmul' R (S := S)).toRingHom) ≫ e.inv) ≫ e.hom) := by
        infer_instance
      simpa [e] using hcomp
    exact (Flat.SpecMap_iff).mp hm
  · refine ⟨(Flat.SpecMap_iff).mpr h.flat, ?_⟩
    rw [AlgebraicGeometry.diagonal_SpecMap]
    exact MorphismProperty.comp_mem @Flat _ _
      ((Flat.SpecMap_iff).mpr h.flat_lmul') inferInstance

/-- The map of stalks induced by a weakly étale morphism of schemes is weakly étale. -/
public theorem weaklyEtale_stalkMap
    {X Y : Scheme.{u}} (f : X ⟶ Y) [WeaklyEtale f] (x : X) :
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
      (f.stalkMap x).hom.toAlgebra
    Algebra.WeaklyEtale (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
  let g := f.stalkMap x
  apply (weaklyEtale_spec_iff _ _ _).mp
  have : WeaklyEtale (X.fromSpecStalk x) := _root_.AlgebraicGeometry.weaklyEtale_fromSpecStalk X x
  have : WeaklyEtale (Y.fromSpecStalk (f x)) :=
    _root_.AlgebraicGeometry.weaklyEtale_fromSpecStalk Y (f x)
  have : WeaklyEtale (Spec.map g ≫ Y.fromSpecStalk (f x)) := by
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk]
    infer_instance
  exact WeaklyEtale.of_comp (Spec.map g) (Y.fromSpecStalk (f x))

/-- The identification of residue fields of a local ring with the quotient by its maximal ideal
sends the residue of `r` to the image of `r`. -/
private theorem equivQuotMaximalIdeal_residue {R : Type*} [CommRing R] [IsLocalRing R] (r : R) :
    IsLocalization.AtPrime.equivQuotMaximalIdeal (IsLocalRing.maximalIdeal R)
        (Localization.AtPrime (IsLocalRing.maximalIdeal R)) (IsLocalRing.residue R r) =
      algebraMap R (IsLocalRing.maximalIdeal R).ResidueField r := by
  change IsLocalization.AtPrime.equivQuotMaximalIdeal _ _ (Ideal.Quotient.mk _ r) = _
  rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk]
  rfl

/-- A geometric point of a scheme lifts to a member of any pro-étale covering family. -/
@[stacks 0F6C]
theorem exists_geometricPoint_lift_of_proetaleCover
    {S : Scheme.{u}} (s : AlgebraicGeometry.GeometricPoint S)
    {I : Type v} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (h : Presieve.ofArrows X f ∈ Scheme.proetalePrecoverage S) :
    ∃ i, ∃ t : AlgebraicGeometry.GeometricPoint (X i),
      t.map (f i) = s := by
  let K := s.residueField
  let y₀ : S := s.hom (IsLocalRing.closedPoint K)
  have hcov := (Scheme.ofArrows_mem_precoverage_iff
    (P := @WeaklyEtale) (X := X) (f := f)).1 h.2
  obtain ⟨i, x, hx⟩ := hcov.1 y₀
  change f i x = y₀ at hx
  have : WeaklyEtale (f i) := hcov.2 i
  obtain ⟨β, hβ⟩ : ∃ β : (X i).residueField x ⟶ CommRingCat.of K,
      (f i).residueFieldMap x ≫ β =
        (S.residueFieldCongr hx).hom ≫
          S.descResidueField (Scheme.stalkClosedPointTo s.hom) := by
    generalize (S.residueFieldCongr hx).hom ≫
      S.descResidueField (Scheme.stalkClosedPointTo s.hom) = a
    let A := S.presheaf.stalk (f i x)
    let B := (X i).presheaf.stalk x
    let p := IsLocalRing.maximalIdeal A
    let q := IsLocalRing.maximalIdeal B
    let g := (f i).stalkMap x
    let : Algebra A B := g.hom.toAlgebra
    let : p.IsPrime := (IsLocalRing.maximalIdeal.isMaximal _).isPrime
    let : q.IsPrime := (IsLocalRing.maximalIdeal.isMaximal _).isPrime
    let : IsLocalHom g.hom := inferInstance
    have hpq : p = q.comap g.hom := (IsLocalRing.maximalIdeal_comap g.hom).symm
    let : Algebra (p.ResidueField) (q.ResidueField) :=
      (Ideal.ResidueField.map p q g.hom hpq).toAlgebra
    have halg : Algebra.IsAlgebraic p.ResidueField q.ResidueField :=
      (isSeparable_and_isAlgebraic_residueField_of_weaklyEtale A B
        (weaklyEtale_stalkMap (f i) x) p q hpq).2
    let eY : S.residueField (f i x) ≃+* p.ResidueField :=
      IsLocalization.AtPrime.equivQuotMaximalIdeal p (Localization.AtPrime p) |>.toRingEquiv
    let eX : (X i).residueField x ≃+* q.ResidueField :=
      IsLocalization.AtPrime.equivQuotMaximalIdeal q (Localization.AtPrime q) |>.toRingEquiv
    let α : p.ResidueField →+* K := a.hom.comp eY.symm.toRingHom
    let : Algebra p.ResidueField K := α.toAlgebra
    let c : q.ResidueField →ₐ[p.ResidueField] K := IsAlgClosed.lift
    let β : (X i).residueField x →+* K := c.toRingHom.comp eX.toRingHom
    have hcompat : eX.toRingHom.comp ((f i).residueFieldMap x).hom =
        (Ideal.ResidueField.map p q g.hom hpq).comp eY.toRingHom := by
      ext z
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective z
      show eX (IsLocalRing.ResidueField.map g.hom (IsLocalRing.residue A r)) =
        (Ideal.ResidueField.map p q g.hom hpq) (eY (IsLocalRing.residue A r))
      have hl : eX (IsLocalRing.ResidueField.map g.hom (IsLocalRing.residue A r)) =
          algebraMap B q.ResidueField (g.hom r) := by
        rw [IsLocalRing.ResidueField.map_residue]
        exact equivQuotMaximalIdeal_residue (g.hom r)
      have hr : eY (IsLocalRing.residue A r) = algebraMap A p.ResidueField r :=
        equivQuotMaximalIdeal_residue r
      rw [hl, hr, Ideal.ResidueField.map_algebraMap]
    have hfac : β.comp ((f i).residueFieldMap x).hom = a.hom := by
      ext z
      show c ((eX.toRingHom.comp ((f i).residueFieldMap x).hom) z) = a.hom z
      rw [RingHom.congr_fun hcompat z]
      show c (algebraMap p.ResidueField q.ResidueField (eY z)) = a.hom z
      rw [c.commutes]
      show α (eY z) = a.hom z
      simp [α]
    exact ⟨CommRingCat.ofHom β, CommRingCat.hom_ext hfac⟩
  refine ⟨i, ⟨K, Spec.map β ≫ (X i).fromSpecResidueField x⟩, ?_⟩
  have ht : Spec.map β ≫ (X i).fromSpecResidueField x ≫ f i = s.hom := by
    rw [← (f i).SpecMap_residueFieldMap_fromSpecResidueField x, ← Category.assoc,
      ← Spec.map_comp, hβ, Spec.map_comp, Category.assoc,
      S.residueFieldCongr_fromSpecResidueField hx]
    exact (Scheme.SpecToEquivOfField K S).left_inv s.hom
  show (⟨K, Spec.map β ≫ (X i).fromSpecResidueField x ≫ f i⟩ :
    AlgebraicGeometry.GeometricPoint S) = ⟨K, s.hom⟩
  congr 1

end AlgebraicGeometry.ProEtale

end
