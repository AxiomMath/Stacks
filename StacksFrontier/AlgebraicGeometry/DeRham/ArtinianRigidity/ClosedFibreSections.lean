module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Sections over the base change to a quotient of the base

For a cartesian square of schemes over `Spec A → Spec (A/I)`, the restriction of sections over an
affine open `U` to its inverse image in the base change is surjective with kernel `I Γ(Y, U)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.DeRhamRigidity

/-- **The base change of a ring along a quotient map is the quotient by the extended ideal**,
read on a pushout square of commutative rings: `R → P` is surjective with kernel `I R`. -/
theorem surjective_and_ker_of_isPushout {A R P : CommRingCat.{u}} (I : Ideal A) (a : A ⟶ R)
    (c : R ⟶ P) (d : CommRingCat.of (A ⧸ I) ⟶ P)
    (h : IsPushout a (CommRingCat.ofHom (Ideal.Quotient.mk I)) c d) :
    Function.Surjective c ∧ RingHom.ker c.hom = I.map a.hom := by
  let : Algebra A R := a.hom.toAlgebra
  let : Algebra R P := c.hom.toAlgebra
  let : Algebra (A ⧸ I) P := d.hom.toAlgebra
  let : Algebra A P := (a ≫ c).hom.toAlgebra
  have : IsScalarTower A R P := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A (A ⧸ I) P := IsScalarTower.of_algebraMap_eq fun x => by
    show (a ≫ c) x = d (Ideal.Quotient.mk I x)
    exact congrArg (fun φ : A ⟶ P => φ x) h.w
  have hp : Algebra.IsPushout A R (A ⧸ I) P :=
    (CommRingCat.isPushout_iff_isPushout (R := A) (S := A ⧸ I) (R' := R) (S' := P)).1 h
  let e : (R ⧸ I.map (algebraMap A R)) ≃ₐ[R] P :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot R I).trans hp.equiv
  have hc : ∀ r, c r = e (Ideal.Quotient.mk _ r) := fun r => by
    simp [e, Algebra.IsPushout.equiv_tmul]
    rfl
  refine ⟨fun p => ?_, ?_⟩
  · obtain ⟨q, rfl⟩ := e.surjective p
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨r, hc r⟩
  · ext r
    rw [RingHom.mem_ker, show c.hom r = c r from rfl, hc, map_eq_zero_iff _ e.injective,
      Ideal.Quotient.eq_zero_iff_mem]
    rfl

/-- **Sections over the base change to `Spec (A/I)`.** For a cartesian square
`Y₀ → Y` over `Spec (A/I) → Spec A` and an affine open `U ⊆ Y`, restriction
`Γ(Y, U) → Γ(Y₀, U₀)` is surjective with kernel `I Γ(Y, U)`. -/
theorem app_surjective_and_ker_of_isPullback {A : CommRingCat.{u}} (I : Ideal A)
    {Y Y₀ : Scheme.{u}} {g : Y ⟶ Spec A} {g₀ : Y₀ ⟶ Spec (CommRingCat.of (A ⧸ I))}
    {i : Y₀ ⟶ Y} (H : IsPullback i g₀ g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
    {U : Y.Opens} (hU : IsAffineOpen U) :
    Function.Surjective (i.app U) ∧
      RingHom.ker (i.app U).hom =
        I.map ((Scheme.ΓSpecIso A).inv ≫ g.appLE ⊤ U le_top).hom := by
  have hpush := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U)
    le_top le_top (UY := i ⁻¹ᵁ U) (by simp)).1
    (isIso_pushoutSection_of_isAffineOpen H le_top le_top (by simp)
      (isAffineOpen_top _) (isAffineOpen_top _) hU)
  have h' : IsPushout ((Scheme.ΓSpecIso A).inv ≫ g.appLE ⊤ U le_top)
      (CommRingCat.ofHom (Ideal.Quotient.mk I)) (i.appLE U (i ⁻¹ᵁ U) le_rfl)
      ((Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))).inv ≫ g₀.appLE ⊤ (i ⁻¹ᵁ U) (by simp)) := by
    refine IsPushout.of_iso hpush (Scheme.ΓSpecIso A) (Iso.refl _)
      (Scheme.ΓSpecIso (CommRingCat.of (A ⧸ I))) (Iso.refl _) (by simp) ?_ (by simp) (by simp)
    rw [← Scheme.ΓSpecIso_naturality]
    congr 1
  rw [← Scheme.Hom.appLE_eq_app (f := i) (U := U)]
  exact surjective_and_ker_of_isPushout I _ _ _ h'

end Stacks.DeRhamRigidity
