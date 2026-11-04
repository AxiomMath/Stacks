module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Etale.NonfiniteGenerators
public import StacksFrontier.RingTheory.IntegralClosure.Basic

/-!
# A finite étale morphism to affine space from an affine scheme étale over it

Let `k` be a field of characteristic `p > 0` and let `X` be an affine scheme admitting an étale
morphism to `𝐀ⁿ_k`. Then `X` admits a *finite* étale morphism to `𝐀ⁿ_k` — in general a different
one.

Writing `X = Spec C`, an étale morphism `X ⟶ 𝐀ⁿ_k` is an étale `k`-algebra map
`k[x₁, …, xₙ] ⟶ C`, and the nonfinite-generator invariant of
`StacksFrontier.RingTheory.Etale.NonfiniteGenerators` can be lowered until it vanishes, at which
point the map is finite.

## Main results

* `AlgebraicGeometry.exists_finiteEtale_to_affineSpace` — the finite étale morphism.

## Implementation notes

Affine `n`-space over `k` is `AlgebraicGeometry.AffineSpace (ULift (Fin n)) (Spec k)`, whose
ring of functions is the polynomial ring on `ULift (Fin n)`; renaming the variables along
`Equiv.ulift` identifies it with `MvPolynomial (Fin n) k`, which is the index type the invariant
is set up for.

Lowering the invariant is `Stacks.Etale.exists_etalePresentation_nonfiniteGeneratorNumber_eq_zero`
applied with the zero algebra in the role of `B`, as in the source: with `A = 0` the
compatibility constraint on the presentation is vacuous, so the only content used is that the
invariant can be driven to zero.

## References

* [Stacks Project, Tag 0G1G](https://stacks.math.columbia.edu/tag/0G1G)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Lowering the nonfinite-generator invariant when there is no quotient to be compatible with:
an étale `k`-algebra map from a polynomial ring in positive characteristic can be replaced by
one whose invariant is zero. This is the case `A = 0` of
`Stacks.Etale.exists_etalePresentation_nonfiniteGeneratorNumber_eq_zero`. -/
private theorem exists_etalePresentation_nonfiniteGeneratorNumber_eq_zero_of_etale
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (n : ℕ)
    (C : Type u) [CommRing C] [Algebra k C]
    (φ : MvPolynomial (Fin n) k →ₐ[k] C) (hφ : φ.toRingHom.Etale) :
    ∃ ψ : MvPolynomial (Fin n) k →ₐ[k] C, ψ.toRingHom.Etale ∧
      Stacks.Etale.nonfiniteGeneratorNumber ψ.toRingHom = 0 := by
  classical
  have hB : Subsingleton (MvPolynomial (Fin n) k ⧸ (⊤ : Ideal (MvPolynomial (Fin n) k))) :=
    Ideal.Quotient.subsingleton_iff.mpr rfl
  let τ : (C ⧸ Ideal.map φ.toRingHom (⊤ : Ideal (MvPolynomial (Fin n) k))) →ₐ[k]
      (MvPolynomial (Fin n) k ⧸ (⊤ : Ideal (MvPolynomial (Fin n) k))) :=
    { toFun := fun _ => 0
      map_one' := hB.elim _ _
      map_mul' := fun _ _ => hB.elim _ _
      map_zero' := rfl
      map_add' := fun _ _ => hB.elim _ _
      commutes' := fun _ => hB.elim _ _ }
  obtain ⟨ψ, hψ, hNF, -⟩ :=
    Stacks.Etale.exists_etalePresentation_nonfiniteGeneratorNumber_eq_zero k p hp n
      (⊤ : Ideal (MvPolynomial (Fin n) k))
      (MvPolynomial (Fin n) k ⧸ (⊤ : Ideal (MvPolynomial (Fin n) k))) C φ hφ τ
      (fun _ => ⟨0, hB.elim _ _⟩) (fun _ => hB.elim _ _)
  exact ⟨ψ, hψ, hNF⟩

/-- An affine scheme étale over affine space in positive characteristic admits a
(possibly different) finite étale morphism to the same affine space. -/
@[stacks 0G1G]
theorem exists_finiteEtale_to_affineSpace
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (n : ℕ)
    {X : Scheme.{u}} [IsAffine X]
    (f : X ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of k))) [Etale f] :
    ∃ g : X ⟶ AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)),
      IsFinite g ∧ Etale g := by
  classical
  let P := MvPolynomial (Fin n) k
  let Q := MvPolynomial (ULift.{u} (Fin n)) k
  let specIso := AffineSpace.SpecIso (ULift.{u} (Fin n)) (.of k)
  let polyEquiv : Q ≃ₐ[k] P :=
    MvPolynomial.renameEquiv k (Equiv.ulift : ULift.{u} (Fin n) ≃ Fin n)
  let polyIso : CommRingCat.of Q ≅ CommRingCat.of P :=
    polyEquiv.toRingEquiv.toCommRingCatIso
  let specPolyIso : Spec (.of Q) ≅ Spec (.of P) :=
    (Scheme.Spec.mapIso polyIso.op).symm
  let hP : X ⟶ Spec (.of P) := f ≫ specIso.hom ≫ specPolyIso.hom
  have hP_etale : Etale hP := by
    dsimp [hP]
    infer_instance
  have hAppEtale : (hP.appTop).hom.Etale := by
    simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
      hP.etale_appLE (isAffineOpen_top _) (isAffineOpen_top _) (by simp)
  let ψRing : P →+* Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (.of P)).inv ≫ hP.appTop).hom
  have hψRing : ψRing.Etale := by
    dsimp only [ψRing]
    rw [CommRingCat.hom_comp]
    exact RingHom.Etale.respectsIso.2 (hP.appTop).hom
      ((Scheme.ΓSpecIso (.of P)).symm.commRingCatIsoToRingEquiv) hAppEtale
  let : Algebra k Γ(X, ⊤) := (ψRing.comp MvPolynomial.C).toAlgebra
  obtain ⟨ψ, hψ, hNF⟩ :=
    exists_etalePresentation_nonfiniteGeneratorNumber_eq_zero_of_etale k p hp n
      Γ(X, ⊤) { ψRing with commutes' := fun _ => rfl } hψRing
  have hψft : ψ.toRingHom.FiniteType := by
    let : Algebra P Γ(X, ⊤) := ψ.toRingHom.toAlgebra
    have : Algebra.Etale P Γ(X, ⊤) := hψ.toAlgebra
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have : IsFinite (Spec.map (CommRingCat.ofHom ψ.toRingHom)) := (IsFinite.SpecMap_iff _).mpr
    (Stacks.Etale.finite_of_nonfiniteGeneratorNumber_eq_zero ψ.toRingHom hψft hNF)
  have : Etale (Spec.map (CommRingCat.ofHom ψ.toRingHom)) := HasRingHomProperty.Spec_iff.mpr hψ
  exact ⟨X.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ specPolyIso.inv ≫
    specIso.inv, inferInstance, inferInstance⟩

end AlgebraicGeometry

end
