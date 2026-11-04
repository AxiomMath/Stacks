module

public import StacksFrontier.RingTheory.Etale.AffineLineFiniteEtale

/-!
# Connected finite étale coverings of the affine line in characteristic zero

Let `k` be an algebraically closed field of characteristic zero. Every finite étale morphism
`f : Y ⟶ 𝐀¹_k = Spec k[X]` with `Y` connected is an isomorphism: the affine line has no
nontrivial connected finite étale covering.

## Main results

* `AlgebraicGeometry.isIso_of_isFinite_of_etale_of_connectedSpace`: the statement above.
-/

@[expose] public section

universe u

open CategoryTheory Polynomial

namespace AlgebraicGeometry

/-- Over an algebraically closed field `k` of characteristic zero, a finite étale morphism
`Y ⟶ 𝐀¹_k = Spec k[X]` with `Y` connected is an isomorphism. -/
@[stacks 05ZI "the input: A^1_k has no nontrivial connected finite étale covering when k is \
algebraically closed of characteristic 0 (details omitted in the source)"]
theorem isIso_of_isFinite_of_etale_of_connectedSpace {k : Type u} [Field k] [IsAlgClosed k]
    [CharZero k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k[X])) [IsFinite f] [Etale f]
    [ConnectedSpace Y] : IsIso f := by
  have : IsAffine Y := isAffine_of_isAffineHom f
  set φ : CommRingCat.of k[X] ⟶ Γ(Y, ⊤) := (Scheme.ΓSpecIso (.of k[X])).inv ≫ f.appTop with hφ
  let : Algebra k[X] Γ(Y, ⊤) := φ.hom.toAlgebra
  have hfin : φ.hom.Finite :=
    RingHom.Finite.comp f.finite_appTop
      (RingHom.Finite.of_surjective _
        (Scheme.ΓSpecIso (.of k[X])).commRingCatIsoToRingEquiv.symm.surjective)
  have het : φ.hom.Etale :=
    RingHom.Etale.respectsIso.2 _ (Scheme.ΓSpecIso (.of k[X])).commRingCatIsoToRingEquiv.symm
      (HasRingHomProperty.appTop @Etale f inferInstance)
  have : Module.Finite k[X] Γ(Y, ⊤) := hfin
  have : Algebra.Etale k[X] Γ(Y, ⊤) := het
  have : ConnectedSpace (PrimeSpectrum Γ(Y, ⊤)) :=
    Y.isoSpec.hom.homeomorph.connectedSpace_iff.mp inferInstance
  have : IsIso φ := (ConcreteCategory.isIso_iff_bijective φ).mpr
    (AffineLineCovering.bijective_algebraMap_of_etale (k := k) Γ(Y, ⊤))
  have : IsIso f.appTop := by
    have : f.appTop = (Scheme.ΓSpecIso (.of k[X])).hom ≫ φ := by
      rw [hφ, Iso.hom_inv_id_assoc]
    rw [this]
    infer_instance
  have hf : f = Y.isoSpec.hom ≫ Spec.map f.appTop ≫ (Spec (.of k[X])).isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [hf]
  infer_instance

end AlgebraicGeometry
