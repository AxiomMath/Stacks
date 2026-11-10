module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.RingHom.Etale
public import StacksFrontier.RingTheory.DeRham.TruncatedGraphNeighbourhood

/-!
# The chart algebra of a truncated graph neighbourhood

Let `R ← A' → R'`, `R → B ← R'` be a pushout square of commutative rings, `γ : B → R₀` a ring map
(sections over the graph) and `ρ : B → T` a surjection with kernel `(ker γ)^N` (sections over the
infinitesimal neighbourhood). If `A'` is a `ℚ`-algebra with an ideal `𝔪` such that `𝔪^N = 0`,
`R → B → R₀` is surjective with kernel `𝔪 R` and `R'` is étale over a polynomial ring over `A'`,
then `Ω^•_{R/A'} → Ω^•_{T/A'}` is a quasi-isomorphism. This is
`GradedDeRham.quasiIso_deRhamComplexMap_graphNeighbourhood` on an affine chart.

## Main results

* `Stacks.DeRhamRigidity.quasiIso_deRhamComplexMap_of_isPushout`: the map of de Rham complexes
  `Ω^•_{R/A'} → Ω^•_{T/A'}` is a quasi-isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory KaehlerDifferential TensorProduct

universe u

namespace Stacks.DeRhamRigidity

variable {A' R R' B T R₀ : CommRingCat.{u}} (a : A' ⟶ R) (a' : A' ⟶ R') (c : R ⟶ B) (c' : R' ⟶ B)
  (γ : B ⟶ R₀) (ρ : B ⟶ T)

/-- **The de Rham complex of the chart of a truncated graph neighbourhood.** Let `R ← A' → R'`
be a pushout with apex `B`, let `γ : B → R₀` and let `ρ : B → T` be a surjection with kernel
`(ker γ)^N`. Assume `A'` is a `ℚ`-algebra with an ideal `𝔪` such that `𝔪^N = 0`, that
`R → B → R₀` is surjective with kernel `𝔪 R`, and that `R'` is étale over a polynomial ring
`A'[x_1, …, x_d]`. Then `Ω^•_{R/A'} → Ω^•_{T/A'}` is a quasi-isomorphism. -/
theorem quasiIso_deRhamComplexMap_of_isPushout [Algebra ℚ A'] (hpush : IsPushout a a' c c')
    (hρ : Function.Surjective ρ) {N : ℕ} (hρker : RingHom.ker ρ.hom = RingHom.ker γ.hom ^ N)
    (m : Ideal A') (hN0 : N ≠ 0) (hN : m ^ N = ⊥) (hsurj : Function.Surjective (c ≫ γ))
    (hker : RingHom.ker (c ≫ γ).hom = m.map a.hom) {d : ℕ}
    (g : MvPolynomial (Fin d) A' →+* R') (hg : g.comp MvPolynomial.C = a'.hom) (hge : g.Etale)
    (j : R ⟶ T) (hj : c ≫ ρ = j) (j₂ : A' ⟶ T) (hj₂ : a ≫ j = j₂) :
    letI := a.hom.toAlgebra
    letI : Algebra R T := j.hom.toAlgebra
    letI : Algebra A' T := j₂.hom.toAlgebra
    haveI : IsScalarTower A' R T := IsScalarTower.of_algebraMap_eq fun x =>
      (congrArg (fun φ : A' ⟶ T => φ x) hj₂).symm
    QuasiIso (deRhamComplexMap A' R T) := by
  subst hj hj₂
  let := a.hom.toAlgebra
  let : Algebra R T := (c ≫ ρ).hom.toAlgebra
  let : Algebra A' T := (a ≫ c ≫ ρ).hom.toAlgebra
  have : IsScalarTower A' R T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let := a'.hom.toAlgebra
  let : Algebra R B := c.hom.toAlgebra
  let : Algebra R' B := c'.hom.toAlgebra
  let : Algebra A' B := (a ≫ c).hom.toAlgebra
  have : IsScalarTower A' R B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A' R' B := IsScalarTower.of_algebraMap_eq fun x =>
    congrArg (fun φ : A' ⟶ B => φ x) hpush.w
  have hp : Algebra.IsPushout A' R R' B :=
    (CommRingCat.isPushout_iff_isPushout (R := A') (S := R') (R' := R) (S' := B)).1 hpush
  let : Algebra A' R₀ := (a ≫ c ≫ γ).hom.toAlgebra
  let π : R →ₐ[A'] R₀ := { (c ≫ γ).hom with commutes' := fun _ => rfl }
  let π' : R' →ₐ[A'] R₀ :=
    { (c' ≫ γ).hom with
      commutes' := fun x => by
        change (a' ≫ c' ≫ γ) x = (a ≫ c ≫ γ) x
        rw [← Category.assoc, ← hpush.w, Category.assoc] }
  let e : R ⊗[A'] R' ≃ₐ[R] B := Algebra.IsPushout.equiv A' R R' B
  have he : ∀ r r', e (r ⊗ₜ r') = c r * c' r' := fun r r' => by
    rw [Algebra.IsPushout.equiv_tmul]
    rfl
  have hγe : ∀ t, γ (e t) = GradedDeRham.graphMult π π' t := fun t => by
    induction t using TensorProduct.inductionOn with
    | tmul r r' =>
      rw [he, map_mul, GradedDeRham.graphMult_tmul]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  let ρR : B →ₐ[R] T := { ρ.hom with commutes' := fun _ => rfl }
  let ψ : R ⊗[A'] R' →ₐ[R] T := ρR.comp e.toAlgHom
  have hψ : Function.Surjective ψ := hρ.comp e.surjective
  have hkerψ : RingHom.ker ψ = GradedDeRham.graphIdeal π π' ^ N := by
    have h1 : GradedDeRham.graphIdeal π π' =
        (RingHom.ker γ.hom).comap (e : R ⊗[A'] R' →+* B) := by
      ext t
      rw [Ideal.mem_comap, RingHom.mem_ker, GradedDeRham.graphIdeal, RingHom.mem_ker, ← hγe t]
      rfl
    have h2 : RingHom.ker ψ = (RingHom.ker ρ.hom).comap (e : R ⊗[A'] R' →+* B) := by
      ext t; rfl
    have key : ∀ I : Ideal B, I.comap (e : R ⊗[A'] R' →+* B) =
        I.map (e.symm.toRingEquiv : B →+* R ⊗[A'] R') := fun I => by
      rw [Ideal.map_comap_of_equiv]
      rfl
    rw [h2, hρker, h1, key, key, Ideal.map_pow]
  let eT : T ≃ₐ[R] GradedDeRham.GraphNeighbourhood π π' N :=
    (Ideal.quotientKerAlgEquivOfSurjective hψ).symm.trans
      (Ideal.quotientEquivAlgOfEq R hkerψ)
  let : Algebra (MvPolynomial (Fin d) A') R' := g.toAlgebra
  have : IsScalarTower A' (MvPolynomial (Fin d) A') R' := IsScalarTower.of_algebraMap_eq fun x =>
    (congrArg (fun φ : A' →+* R' => φ x) hg).symm
  have : Algebra.Etale (MvPolynomial (Fin d) A') R' := hge.toAlgebra
  have hq := GradedDeRham.quasiIso_deRhamComplexMap_graphNeighbourhood (d := d) (π := π)
    (π' := π') hN0 hN hsurj hker
  let : Algebra (GradedDeRham.GraphNeighbourhood π π' N) T := eT.symm.toAlgHom.toRingHom.toAlgebra
  have : IsScalarTower R (GradedDeRham.GraphNeighbourhood π π' N) T :=
    IsScalarTower.of_algebraMap_eq fun r => (eT.symm.commutes r).symm
  have : IsScalarTower A' (GradedDeRham.GraphNeighbourhood π π' N) T :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply A' R (GradedDeRham.GraphNeighbourhood π π' N),
        IsScalarTower.algebraMap_apply A' R T]
      exact (eT.symm.commutes _).symm
  have hcomp := deRhamComplexMap_comp A' R (GradedDeRham.GraphNeighbourhood π π' N) T
  have : IsIso (deRhamComplexMap A' (GradedDeRham.GraphNeighbourhood π π' N) T) :=
    isIso_deRhamComplexMap_of_algEquiv A' (eT.symm.restrictScalars A') rfl
  rw [← hcomp]
  infer_instance

end Stacks.DeRhamRigidity
