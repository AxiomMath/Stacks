module

public import StacksFrontier.Homology.Perfect.BoundedProjectiveFiniteHomology
public import StacksFrontier.Homology.Perfect.LargeUniverse
public import StacksFrontier.Algebra.Module.Injective.GroupAlgebraInjectiveProjective
public import StacksFrontier.Algebra.Module.Injective.KernelInjective
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# A perfectness criterion over `(ℤ/ℓⁿ)[H]` from injective models

Let `R = (ℤ/ℓⁿ)[H]` for a prime `ℓ`, `n ≥ 1` and a finite group `H`, and let `J` be a bounded
below complex of injective `R`-modules (for instance the global sections of an injective
resolution of a sheaf of `R`-modules) whose cohomology modules are finite and vanish above `c`.
Suppose that every cocycle `R/𝔞 → J^{c+1}` of the complex `Hom_R(R/𝔞, J)` is a coboundary, for
every left ideal `𝔞`; that is, `Ext^{c+1}_R(R/𝔞, J) = 0`. Then `J` is a perfect object of `D(R)`.

Indeed the cycles `Z^c = ker(J^c → J^{c+1})` form an injective module by Baer's criterion
(`Module.injective_ker_of_injective_of_cocycle`), so the canonical truncation `τ_{≤ c} J`, which
is quasi-isomorphic to `J`, is a bounded complex of injective modules; injective `R`-modules are
projective (`MonoidAlgebra.projective_of_injective_zmod`), and a bounded complex of projective
modules with finite cohomology over a Noetherian ring is perfect
(`StacksDraft.Perfect.isPerfect_of_projective_of_finite_homology`).

This is the form in which the perfectness of `RΓ_c(U_k̄, D(A[H]))` over `A[H]`, `A = ℤ/ℓⁿ`, is
proved in Step 7 of the proof of [Stacks, Tag 03UG]: the cocycle condition is the vanishing of
`Ext^{c+1}_{A[H]}(R/𝔞, RΓ_c(U_k̄, D(A[H]))) = H^{c+1}_c(U_k̄, Hom_{A[H]}(R/𝔞, D(A[H])))`.

## Main results

* `StacksDraft.Perfect.isPerfect_of_injective_of_cocycle_zmod`

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w

namespace StacksDraft.Perfect

variable {ℓ : ℕ} [Fact ℓ.Prime] {n : ℕ} [NeZero n] {H : Type} [Group H] [Fintype H]

/-- An injective `(ℤ/ℓⁿ)[H]`-module, as an object of the module category, is projective. -/
theorem projective_of_injective_zmod (M : ModuleCat.{v} (MonoidAlgebra (ZMod (ℓ ^ n)) H))
    [Injective M] : Projective M := by
  have : Injective (ModuleCat.of (MonoidAlgebra (ZMod (ℓ ^ n)) H) M) := ‹Injective M›
  have := Module.injective_module_of_injective_object (MonoidAlgebra (ZMod (ℓ ^ n)) H) M
  have := MonoidAlgebra.projective_of_injective_zmod (ℓ := ℓ) (n := n) (H := H) M
  infer_instance

/-- **Perfectness over `(ℤ/ℓⁿ)[H]` of a bounded below complex of injective modules** with finite
cohomology vanishing above `c`, all of whose `Ext^{c+1}(R/𝔞, -)` vanish. -/
theorem isPerfect_of_injective_of_cocycle_zmod
    [HasDerivedCategory.{w} (ModuleCat.{v} (MonoidAlgebra (ZMod (ℓ ^ n)) H))]
    (J : CochainComplex (ModuleCat.{v} (MonoidAlgebra (ZMod (ℓ ^ n)) H)) ℤ) (a c : ℤ)
    [J.IsStrictlyGE a] (hJ : ∀ i, Injective (J.X i)) (hc : ∀ i, c < i → J.ExactAt i)
    (hf : ∀ i, Module.Finite (MonoidAlgebra (ZMod (ℓ ^ n)) H) (J.homology i))
    (hcoc : ∀ (𝔞 : Ideal (MonoidAlgebra (ZMod (ℓ ^ n)) H))
      (ψ : (MonoidAlgebra (ZMod (ℓ ^ n)) H ⧸ 𝔞) →ₗ[MonoidAlgebra (ZMod (ℓ ^ n)) H] J.X (c + 1)),
      (J.d (c + 1) (c + 1 + 1)).hom ∘ₗ ψ = 0 →
        ∃ χ : (MonoidAlgebra (ZMod (ℓ ^ n)) H ⧸ 𝔞) →ₗ[MonoidAlgebra (ZMod (ℓ ^ n)) H] J.X c,
          (J.d c (c + 1)).hom ∘ₗ χ = ψ) :
    IsPerfect (DerivedCategory.Q.obj J) := by
  let R := MonoidAlgebra (ZMod (ℓ ^ n)) H
  have : NeZero (ℓ ^ n) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  have : Finite R := Module.finite_of_finite (ZMod (ℓ ^ n))
  have : IsNoetherianRing R := isNoetherian_of_finite R R
  have : J.IsLE c := (CochainComplex.isLE_iff J c).2 hc
  -- the cycles `Z^c` are injective, hence projective
  have hJ' : ∀ i, Module.Injective R (J.X i) := fun i =>
    Module.injective_module_of_injective_object R (J.X i)
  have := hJ' c
  have hd : (J.d (c + 1) (c + 1 + 1)).hom ∘ₗ (J.d c (c + 1)).hom = 0 := by
    rw [← ModuleCat.hom_comp, J.d_comp_d]
    rfl
  have := Module.injective_ker_of_injective_of_cocycle _ _ hd hcoc
  let eZ : (J.truncLE c).X c ≅ ModuleCat.of R (LinearMap.ker (J.d c (c + 1)).hom) :=
    J.truncLEXIsoCycles c ≪≫ J.cyclesIsoSc' (c - 1) c (c + 1) (by simp) (by simp) ≪≫
      (J.sc' (c - 1) c (c + 1)).moduleCatCyclesIso
  have hproj : ∀ i, Projective ((J.truncLE c).X i) := by
    -- a module isomorphic to an injective module is projective
    have key : ∀ {M N : ModuleCat.{v} R} [Module.Injective R M], (N ≅ M) → Projective N := by
      intro M N _ e
      have : Injective M := Module.injective_object_of_injective_module R M
      have := projective_of_injective_zmod (ℓ := ℓ) (n := n) (H := H) M
      exact Projective.of_iso e.symm inferInstance
    intro i
    rcases lt_trichotomy i c with hi | rfl | hi
    · have := hJ' i
      exact key (J.truncLEXIso c i hi)
    · exact key eZ
    · exact ((J.truncLE c).isZero_of_isStrictlyLE c i hi).projective
  have : (J.truncLE c).IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    rcases lt_trichotomy i c with hic | rfl | hic
    · exact (J.isZero_of_isStrictlyGE a i hi).of_iso (J.truncLEXIso c i hic)
    · refine IsZero.of_iso ?_ (J.truncLEXIsoCycles i)
      exact IsZero.of_mono (J.iCycles i) (J.isZero_of_isStrictlyGE a i hi)
    · exact (J.truncLE c).isZero_of_isStrictlyLE c i hic
  have : IsIso (DerivedCategory.Q.map (J.ιTruncLE c)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  have hfE : ∀ i, Module.Finite R ((J.truncLE c).homology i) := fun i =>
    Module.Finite.equiv
      (asIso (HomologicalComplex.homologyMap (J.ιTruncLE c) i)).toLinearEquiv.symm
  exact isPerfect_of_iso (asIso (DerivedCategory.Q.map (J.ιTruncLE c))).symm
    (isPerfect_of_projective_of_finite_homology (J.truncLE c) a c hproj hfE)

end StacksDraft.Perfect
