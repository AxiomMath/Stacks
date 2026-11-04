module

public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.ExteriorPower
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Automorphisms
public import Mathlib.RingTheory.Norm.Defs

/-!
# The determinant functor on a vector space over the residue field

Let `R` be a local ring with residue field `κ` and let `M` be a finite-dimensional `κ`-vector
space, viewed as an `R`-module through the residue map. For an automorphism `e` of `M` the
residue-field determinant `AlgebraicGeometry.determinantAutomorphism e` of Stacks 02PN, which is
the scalar by which the determinant functor of Tag 05M7 acts on the one-dimensional determinant
of `M`, is the determinant of `e` in the sense of linear algebra over `κ`
(`Stacks.Chow.determinantAutomorphism_eq_det`).

As a consequence, for a `κ`-algebra `L` finite over `κ` and an element `w` acting invertibly, the
residue-field determinant of multiplication by `w` is the norm `N_{L/κ}(w)`
(`Stacks.Chow.determinantAutomorphism_eq_norm`).

## Main results

* `Stacks.Chow.determinantAutomorphism_eq_det` — `det_κ(e) = det(e)` for a `κ`-vector space.
* `Stacks.Chow.determinantAutomorphism_eq_norm` — `det_κ(w · −) = N_{L/κ}(w)`.

## References

* [Stacks Project, Tag 02PN](https://stacks.math.columbia.edu/tag/02PN)
* [Stacks Project, Tag 02P8](https://stacks.math.columbia.edu/tag/02P8)
* [Stacks Project, Tag 0GSZ](https://stacks.math.columbia.edu/tag/0GSZ)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Module.FiniteLength AlgebraicGeometry

universe u v

namespace Stacks.Chow

variable {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
  [Module (ResidueField R) M] [IsScalarTower R (ResidueField R) M]
  [Module.Finite (ResidueField R) M]

/-- On a vector space over the residue field the determinant functor acts by the determinant:
for an `R`-linear automorphism `e` of a finite-dimensional `κ`-vector space `M` and the same map
read `κ`-linearly, the residue-field determinant of Stacks 02PN is the determinant of linear
algebra. -/
theorem determinantAutomorphism_eq_det (e : M ≃ₗ[R] M) (hM : IsFiniteLength R M)
    (eK : M →ₗ[ResidueField R] M) (he : ∀ x, eK x = e x) :
    (determinantAutomorphism e hM : ResidueField R) = LinearMap.det eK := by
  classical
  let K := ResidueField R
  let DF := determinantFunctor.{u, v} R
  let mObj : FiniteLengthModuleIso.{u, v} R := ⟨⟨ModuleCat.of R M, hM⟩⟩
  let eMor : mObj ⟶ mObj := ⟨ObjectProperty.isoMk _ e.toModuleIso⟩
  let F := DF.mapLinearEquiv eMor
  have hdet : (determinantAutomorphism e hM : K) = (F.det : K) := rfl
  have hF := linearEquiv_eq_det_smul_id (finrank_determinant_eq_one hM) F
  let Cmp := determinantExteriorPowerComparison R M
  set n := Module.finrank K M with hn
  have hLen : moduleLength R M = n := Cmp.length_eq_finrank
  let b : Module.Basis (Fin n) K M := Module.finBasisOfFinrankEq K M rfl
  let L : ⋀[K]^n M →ₗ[K] K := exteriorPower.alternatingMapLinearEquiv b.det
  have hL : ∀ v : Fin n → M, L (exteriorPower.ιMulti K n v) = b.det v := fun v ↦
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _
  let s : AdmissibleSequence R M := ⟨fun i ↦ b (Fin.cast hLen i), all_admissible R M _⟩
  have hs : L (Cmp.equiv (symbol s)) = 1 := by
    rw [Cmp.equiv_symbol, hL]
    convert b.det_self using 2
    funext i
    show b (Fin.cast hLen (Fin.cast _ i)) = b i
    rfl
  have hFs : L (Cmp.equiv (F (symbol s))) = LinearMap.det eK := by
    rw [DF.map_symbol eMor s, Cmp.equiv_symbol, hL]
    have hv : (fun i : Fin n ↦ eMor.iso.hom.hom.hom
        (s.1 (Fin.cast (DF.map_length eMor).symm
          (Fin.cast Cmp.length_eq_finrank.symm i)))) = eK ∘ b := by
      funext i
      show e (b (Fin.cast hLen (Fin.cast _ (Fin.cast _ i)))) = eK (b i)
      rw [he]
      rfl
    rw [hv, b.det_comp, b.det_self, mul_one]
  have hFs' : F (symbol s) = (F.det : K) • symbol s := by
    have := congrArg (fun f : determinant R M →ₗ[K] determinant R M ↦ f (symbol s)) hF
    simpa using this
  rw [hdet, ← hFs, hFs', map_smul, map_smul, hs, smul_eq_mul, mul_one]

/-- The residue-field determinant of a multiplication is a norm. Let `L` be an algebra over
the residue field `κ` of `R`, finite over `κ`, with the `R`-module structure through `κ`, and let
`w ∈ L` act invertibly. The residue-field determinant of Stacks 02PN of multiplication by `w` is
`N_{L/κ}(w)`. -/
theorem determinantAutomorphism_eq_norm {L : Type v} [CommRing L] [Algebra R L]
    [Algebra (ResidueField R) L] [IsScalarTower R (ResidueField R) L]
    [Module.Finite (ResidueField R) L] (e : L ≃ₗ[R] L) (hL : IsFiniteLength R L) (w : L)
    (he : ∀ x, e x = w * x) :
    (determinantAutomorphism e hL : ResidueField R) = Algebra.norm (ResidueField R) w := by
  rw [determinantAutomorphism_eq_det e hL (Algebra.lmul (ResidueField R) L w)
    (fun x ↦ by rw [he]; rfl), Algebra.norm_apply]

end Stacks.Chow

end
