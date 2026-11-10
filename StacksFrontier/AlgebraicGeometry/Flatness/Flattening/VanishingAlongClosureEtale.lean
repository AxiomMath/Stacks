module

public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.VanishingOnReducedFibre
public import StacksFrontier.RingTheory.Flat.MakeMapZeroIdeal

/-!
# Étale-local projectivity suffices for vanishing along a closure

Let `R` be a commutative ring, let `R'` be an `R`-algebra whose map on prime spectra is open —
the case of interest is `R'` étale over `R` — and let `u : M →ₗ[R'] N` be a map of `R'`-modules
whose target is projective over `R'` and flat over `R`.  Let `T` be a subset of `\Spec R` and let
`K` be a field over `R` whose kernel ideal `𝔭 = \ker(R ⟶ K)` is a point of the closure of `T`.  If
every value of `u` lies in `𝔭_t · N` for each `t ∈ T`, then every value of `u` lies in `𝔭 · N`.

This is the whole of the source's proof of Stacks 0CWB downstream of its geometric input,
assembled at the ring level.  The projectivity it asks for is over `R'`, not over `R` — which is
what Stacks 0CVY produces, projectivity of the sections over the ring of an **étale** `S' ⟶ S` —
and the conclusion is over `R`, which is what the chartwise consumer of Stacks 083K needs.  The
passage between the two rings is the étale fibre `A = R' ⊗_R K`: it is reduced, so
`Module.rTensor_eq_zero_of_isReduced_of_comap_mem_closure` applies to it, and
`TensorProduct.AlgebraTensorModule.cancelBaseChange` turns the vanishing of `u ⊗_{R'} A` into the
vanishing of `u ⊗_R K`, which flatness of `N` over `R` turns back into membership in `𝔭 · N`.

## Main results

* `Stacks.Flattening.rTensor_residueField_eq_zero_of_forall_mem_smul_top`: membership of the
  values of `u` in `𝔭_t · N` for a prime `t` of `R` below a prime `t'` of `R'` gives the vanishing
  of `u ⊗_{R'} κ(t')`.
* `Stacks.Flattening.forall_mem_ker_smul_top_of_projective_of_isOpenMap`: **the statement above.**

## Implementation notes

**Why the hypothesis on `K` is `𝔭 ∈ closure T` and nothing more.**  The reduced algebra fed to
`Module.rTensor_eq_zero_of_isReduced_of_comap_mem_closure` is `A = R' ⊗_R K`, and that lemma asks
every point of `\Spec A` to lie over a point of `\Spec R` in the closure of `T`.  Only the *easy*
inclusion is needed for that: `\ker(R ⟶ K)` maps to zero in `A`, because
`Algebra.TensorProduct.tmul_one_eq_one_tmul` rewrites `algebraMap R A a` as `1 ⊗ₜ algebraMap R K a`,
so every prime of `A` contracts to a prime of `R` containing `𝔭`, i.e. to a point of
`closure {𝔭} ⊆ closure T`.  No surjectivity of `\Spec R' ⟶ \Spec R` and no identification of the
contraction with `𝔭` itself is required.

**Why the two flatness/projectivity hypotheses are both needed and are not the same.**
Projectivity over `R'` is what makes the flattening ideal of Stacks 083L exist, and it is the only
form the geometric input supplies.  Flatness over `R` is what makes the elementwise condition
`u(M) ⊆ J · N` agree with the vanishing of `u ⊗_R R/J`, in the direction used at the very end
(`Stacks.Flattening.mem_ker_smul_top_of_tmul_eq_zero`); in the situation of Stacks 0CWA it is the
flatness of `𝒢` over the base, the hypothesis the situation carries.  Neither implies the other
here: the two base rings are different.

**Reducedness of the fibre** is a hypothesis rather than a derivation, because it is a statement
about `R'` over `R` alone: for `R'` étale over `R` it is
`Algebra.FormallyUnramified.isReduced_tensorProduct_of_field`, and geometrically
`AlgebraicGeometry.isReduced_appTop_tensorProduct_residueField`.

## References

* [Stacks Project, Tag 0CWB](https://stacks.math.columbia.edu/tag/0CWB)
* [Stacks Project, Tag 0CVY](https://stacks.math.columbia.edu/tag/0CVY)
* [Stacks Project, Tag 083L](https://stacks.math.columbia.edu/tag/083L)
-/

@[expose] public section

open TensorProduct

namespace Stacks.Flattening

universe u v w

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R'] [Algebra R R']
variable {M : Type v} [AddCommGroup M] [Module R' M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module R' N] [IsScalarTower R R' N]

/-- An ideal of `R'` annihilates the residue field of any prime containing it. -/
theorem smul_residueField_eq_zero {t' : PrimeSpectrum R'} {a : R'} (ha : a ∈ t'.asIdeal)
    (x : t'.asIdeal.ResidueField) : a • x = 0 := by
  have h : algebraMap R' t'.asIdeal.ResidueField a = 0 :=
    (RingHom.mem_ker).mp (by rwa [Ideal.ker_algebraMap_residueField])
  rw [Algebra.smul_def, h, zero_mul]

/-- **From the ideal condition downstairs to fibrewise vanishing upstairs.**  If every value of
`u : M →ₗ[R'] N` lies in `𝔭 · N` for the contraction `𝔭` of a prime `t'` of `R'`, then the base
change of `u` to the residue field of `t'` vanishes.

The contraction of `t'` maps into `t'`, so the values lie in `t'.asIdeal · N` as well, and
`t'.asIdeal` annihilates `κ(t')`. -/
theorem rTensor_residueField_eq_zero_of_forall_mem_smul_top (u : M →ₗ[R'] N)
    (t' : PrimeSpectrum R')
    (h : ∀ m : M, u m ∈
      (PrimeSpectrum.comap (algebraMap R R') t').asIdeal • (⊤ : Submodule R N)) :
    LinearMap.rTensor t'.asIdeal.ResidueField u = 0 := by
  have hup : ∀ m : M, u m ∈ t'.asIdeal • (⊤ : Submodule R' N) := by
    intro m
    refine Submodule.smul_induction_on (h m) (fun a ha n _ => ?_) (fun x y hx hy => add_mem hx hy)
    rw [← IsScalarTower.algebraMap_smul R' a n]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  refine TensorProduct.ext' fun m z => ?_
  rw [LinearMap.rTensor_tmul, LinearMap.zero_apply]
  exact tmul_eq_zero_of_mem_smul_top (fun a ha => smul_residueField_eq_zero ha) (hup m) z

/-- **Étale-local projectivity suffices.**  Let `R'` be an `R`-algebra whose map on prime spectra
is open, let `u : M →ₗ[R'] N` have target projective over `R'` and flat over `R`, let `T` be a
subset of `\Spec R` and let `K` be a field over `R` with `A = R' ⊗_R K` reduced and with
`\ker(R ⟶ K)` a point of the closure of `T`.  If every value of `u` lies in `𝔭_t · N` for every
`t ∈ T`, then every value of `u` lies in `\ker(R ⟶ K) · N`.

This is the source's proof of Stacks 0CWB from its geometric input onwards, at the ring level:
fibrewise vanishing upstairs at every prime over `T`
(`Stacks.Flattening.rTensor_residueField_eq_zero_of_forall_mem_smul_top`), then the flattening
ideal of Stacks 083L and the closure argument on the reduced fibre
(`Module.rTensor_eq_zero_of_isReduced_of_comap_mem_closure`), then cancellation of the base change
and flatness over `R`. -/
theorem forall_mem_ker_smul_top_of_projective_of_isOpenMap
    (hopen : IsOpenMap (PrimeSpectrum.comap (algebraMap R R')))
    (u : M →ₗ[R'] N) (hN : Module.Projective R' N) [Module.Flat R N]
    (T : Set (PrimeSpectrum R)) (K : Type u) [Field K] [Algebra R K]
    [IsReduced (R' ⊗[R] K)]
    (hs : (⟨RingHom.ker (algebraMap R K), RingHom.ker_isPrime _⟩ : PrimeSpectrum R) ∈ closure T)
    (hT : ∀ t ∈ T, ∀ m : M, u m ∈ t.asIdeal • (⊤ : Submodule R N)) :
    ∀ m : M, u m ∈ RingHom.ker (algebraMap R K) • (⊤ : Submodule R N) := by
  -- Every prime of the fibre contracts into the closure of `T`.
  have hfibre : ∀ q : PrimeSpectrum (R' ⊗[R] K),
      PrimeSpectrum.comap (algebraMap R R')
          (PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] K)) q) ∈ closure T := by
    intro q
    refine closure_minimal (Set.singleton_subset_iff.2 hs) isClosed_closure ?_
    rw [PrimeSpectrum.closure_singleton]
    intro a ha
    change algebraMap R R' a ∈ (PrimeSpectrum.comap (algebraMap R' (R' ⊗[R] K)) q).asIdeal
    have hzero : algebraMap R' (R' ⊗[R] K) (algebraMap R R' a) = 0 := by
      have h : algebraMap R K a = 0 := (RingHom.mem_ker).mp ha
      change algebraMap R R' a ⊗ₜ[R] (1 : K) = 0
      rw [Algebra.TensorProduct.tmul_one_eq_one_tmul, h, TensorProduct.tmul_zero]
    change algebraMap R' (R' ⊗[R] K) (algebraMap R R' a) ∈ q.asIdeal
    rw [hzero]
    exact q.asIdeal.zero_mem
  -- The base change of `u` to the fibre vanishes.
  have hA : LinearMap.rTensor (R' ⊗[R] K) u = 0 :=
    Module.rTensor_eq_zero_of_isReduced_of_comap_mem_closure (algebraMap R R') hopen u hN T
      (R' ⊗[R] K) hfibre
      fun t' ht' => rTensor_residueField_eq_zero_of_forall_mem_smul_top u t' (hT _ ht')
  -- Cancel the base change and use flatness over `R`.
  intro m
  refine mem_ker_smul_top_of_tmul_eq_zero (R' := K) ?_
  have hzero : u m ⊗ₜ[R'] (1 : R' ⊗[R] K) = 0 := by
    have := LinearMap.congr_fun hA (m ⊗ₜ[R'] (1 : R' ⊗[R] K))
    rwa [LinearMap.rTensor_tmul, LinearMap.zero_apply] at this
  have hcancel := congrArg
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R R' R' N K) hzero
  rw [map_zero, show (1 : R' ⊗[R] K) = (1 : R') ⊗ₜ[R] (1 : K) from rfl,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul] at hcancel
  exact hcancel

end Stacks.Flattening

end
