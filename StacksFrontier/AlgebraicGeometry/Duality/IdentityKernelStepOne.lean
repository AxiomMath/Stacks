module

public import StacksFrontier.Algebra.Homology.DerivedCategory.HomSingleShiftHomology
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.DualHom
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.FlatSingleTensorHomology
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.LeftTensorNotation
public import StacksFrontier.AlgebraicGeometry.Duality.IdentityKernelBoxVanishing
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.FlatFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyNoetherianRegular
import StacksCore.Tactic.StacksAttribute

/-!
# Step 1 of the proof of Tag 0G0E: the kernel has no cohomology in negative degrees

Let `k` be a field, let `X` be a smooth proper `k`-scheme and let `K` be a perfect object of
`D(𝒪_{X ×_k X})` whose Fourier-Mukai functor induces on `D_perf(𝒪_X)` an endofunctor isomorphic to
the identity.  This file proves

`H^i(K) = 0` for `i < 0`,

which is the first step of the proof of [Stacks, Tag 0G0E].

The source argues at the *minimal* integer `i` with `H^i(K) ≠ 0`, and that minimality is essential:
the display it runs on computes `H^i(X × X, K ⊗^𝐋 (ℰ ⊠ 𝒢))` as `Γ(X × X, H^i(K) ⊗ (ℰ ⊠ 𝒢))` only in
the lowest degree where the tensor product has cohomology.  So the vanishing cannot be proved
degree by degree independently; it is proved here by induction upward from a degree below which `K`
has no cohomology at all, which exists because a perfect object on a Noetherian scheme has bounded
cohomology ([Stacks, Tag 0FXU]).

## Main results

* `Stacks.Duality.isZero_homology_of_isGE_of_neg` — **the inductive step**: at a negative degree
  `j` below which `K` has no cohomology, `H^j(K) = 0`.
* `Stacks.Duality.isGE_zero_of_representsIdentityOnPerfect` — **step 1 of [Stacks, Tag 0G0E]**:
  `K` has no cohomology below degree zero.

## Implementation notes

*The chain of the inductive step.*  Fix a negative `j` with `K.IsGE j`, and let `ℰ`, `𝒢` be finite
locally free.  Then:

1. `ℰ^∨` and `𝒢^∨` are finite locally free ([Stacks, Tag 0FA7]) and so is `ℰ^∨ ⊠ 𝒢^∨`, hence it is
   flat;
2. therefore `L = K ⊗^𝐋 (ℰ^∨ ⊠ 𝒢^∨)[0]` has no cohomology below degree `j` either
   (`AlgebraicGeometry.isGE_tensorSingleFlat`), and `H^j(L) = H^j(K) ⊗ (ℰ^∨ ⊠ 𝒢^∨)`
   (`AlgebraicGeometry.homologyTensorSingleFlatIso`);
3. every morphism `𝒪_{X × X}[0] ⟶ L⟦j⟧` is zero, because the display computes that group to be
   `H^j(X, ℰ^∨ ⊗ 𝒢^∨)`, which vanishes in negative degrees
   (`Stacks.Duality.hom_singleUnit_kernel_box_eq_zero_of_neg`);
4. `L` being bounded below by `j`, that vanishing descends to `Hom(𝒪_{X × X}, H^j(L))`
   ([Stacks, Tag 06XS], `DerivedCategory.eq_zero_of_forall_hom_single_shift_eq_zero`), so
   `H^j(K) ⊗ (ℰ^∨ ⊠ 𝒢^∨)` has no nonzero global section;
5. hence there is no nonzero morphism `ℰ ⊠ 𝒢 ⟶ H^j(K)`
   (`AlgebraicGeometry.eq_zero_of_forall_hom_unit_tensor_externalTensorProduct_dual_eq_zero`);
6. and `H^j(K) = 0` by [Stacks, Tag 0FZ0], which presents a nonzero coherent module on `X × X` as a
   quotient of such a box.

Steps 3 and 5 are where the duals appear, and they appear for the same reason: the library's form
of [Stacks, Tag 0FZ0] produces a surjection `ℰ ⊠ 𝒢 ↠ H^j(K)` with `ℰ` and `𝒢` finite locally free,
while the display is a statement about `K` tensored with a box.  The two are matched by
`Hom(P, ℱ) ≃ Γ(ℱ ⊗ P^∨)` at `P = ℰ ⊠ 𝒢`, and `(ℰ ⊠ 𝒢)^∨ = ℰ^∨ ⊠ 𝒢^∨`; the source writes the
surjection as `ℰ^∨ ⊠ 𝒢^∨ → H^i(K)` and so needs the same identification in the other direction.

*Why the induction and not the stated reduction.*
`Stacks.Duality.isGE_zero_and_isLE_zero_of_forall_externalTensorProduct_hom_eq_zero` of
`StacksFrontier/AlgebraicGeometry/Duality/IdentityFourierMukaiKernel.lean` asks for the vanishing of
every morphism `ℰ ⊠ 𝒢 ⟶ H^i(K)` at *every* `i ≠ 0`, which is strictly more than the source's proof
gives: in a degree `i` that is not the lowest nonvanishing one, the display does not compute the
group it needs, and the hypothesis cannot be discharged.  The induction below replaces it on the
negative side: the hypothesis consumed is only ever `K.IsGE j` for the `j` at hand, which is what
the source's minimality provides.

*The resolution property.*  [Stacks, Tag 0FZ0] asks for `AlgebraicGeometry.HasResolutionProperty X`
and `AlgebraicGeometry.hasResolutionProperty_of_smooth_isProper_over_field` supplies it from the
hypotheses of the tag.

*The model of the derived categories.*  `CategoryTheory.HasDerivedCategory.standard` is activated
as a local instance at high priority, as in the imported files.

## References

* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
* [Stacks Project, Tag 0FZ0](https://stacks.math.columbia.edu/tag/0FZ0)
* [Stacks Project, Tag 0FA7](https://stacks.math.columbia.edu/tag/0FA7)
* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Duality

attribute [local instance 100000] HasDerivedCategory.standard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [IsProper f]

/-- **The inductive step of step 1 of [Stacks, Tag 0G0E].**  Let `K` be a perfect object of
`D(𝒪_{X ×_k X})` whose Fourier-Mukai functor induces the identity on `D_perf(𝒪_X)`, and let `j` be
a negative degree below which `K` has no cohomology.  Then `H^j(K) = 0`.

The hypothesis `K.IsGE j` is what the source's choice of `j` as the minimal nonvanishing degree
provides, and it is what makes the display compute the group it needs: the degree-`j` cohomology
of `K ⊗^𝐋 (ℰ^∨ ⊠ 𝒢^∨)[0]` is then the global sections of `H^j(K) ⊗ (ℰ^∨ ⊠ 𝒢^∨)`.  See the
implementation notes of this file for the six links of the chain. -/
theorem isZero_homology_of_isGE_of_neg
    (K : DerivedCategory (Limits.pullback f f).Modules)
    (hK : perfectDerivedObjects (Limits.pullback f f) K)
    (hΦ : RepresentsIdentityOnPerfect f K) (j : ℤ) (hj : j < 0) (hGE : K.IsGE j) :
    IsZero ((DerivedCategory.homologyFunctor (Limits.pullback f f).Modules j).obj K) := by
  have := hGE
  have := hasResolutionProperty_of_smooth_isProper_over_field f
  refine isZero_homology_of_forall_externalTensorProduct_hom_eq_zero f K hK j ?_
  intro E G hE hG q
  have hEd := isFiniteLocallyFree_dualSheaf E hE
  have hGd := isFiniteLocallyFree_dualSheaf G hG
  have hflat := AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree
    (externalTensorProduct f f (dualSheaf E) (dualSheaf G))
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry
      (externalTensorProduct f f (dualSheaf E) (dualSheaf G))).1
      (isFiniteLocallyFree_externalTensorProduct f f (dualSheaf E) (dualSheaf G)
        ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hEd)
        ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry _).2 hGd)))
  refine eq_zero_of_forall_hom_unit_tensor_externalTensorProduct_dual_eq_zero f f E G
    ((DerivedCategory.homologyFunctor (Limits.pullback f f).Modules j).obj K)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).2 hE)
    ((Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry G).2 hG) ?_ q
  intro s
  have hLGE := isGE_tensorSingleFlat (Limits.pullback f f) K
    (externalTensorProduct f f (dualSheaf E) (dualSheaf G)) hflat j
  have key := DerivedCategory.eq_zero_of_forall_hom_single_shift_eq_zero
    (Stacks.UnitStalk.unitModule (Limits.pullback f f))
    ((dtenLeft (Limits.pullback f f) K).obj
      ((DerivedCategory.singleFunctor (Limits.pullback f f).Modules 0).obj
        (externalTensorProduct f f (dualSheaf E) (dualSheaf G)))) j hLGE
    (hom_singleUnit_kernel_box_eq_zero_of_neg f K hΦ (dualSheaf E) (dualSheaf G) hEd hGd j hj)
    (s ≫ (homologyTensorSingleFlatIso (Limits.pullback f f) K
      (externalTensorProduct f f (dualSheaf E) (dualSheaf G)) hflat j).inv)
  refine (cancel_mono (homologyTensorSingleFlatIso (Limits.pullback f f) K
    (externalTensorProduct f f (dualSheaf E) (dualSheaf G)) hflat j).inv).mp ?_
  rw [key, zero_comp]

/-- **Step 1 of the proof of [Stacks, Tag 0G0E]**: a perfect object `K` of `D(𝒪_{X ×_k X})` whose
Fourier-Mukai functor induces on `D_perf(𝒪_X)` an endofunctor isomorphic to the identity has no
cohomology below degree zero.

`K` is bounded below, being perfect on the Noetherian `X ×_k X` ([Stacks, Tag 0FXU]), so there is
a degree `n₀` below which it has no cohomology at all; the bound is then raised one degree at a
time by `Stacks.Duality.isZero_homology_of_isGE_of_neg` until it reaches zero.  The induction is on
`n : ℕ` with the bound `min 0 (n₀ + n)`, which stops at zero rather than passing it: the inductive
step consumes `n₀ + n < 0`, exactly the hypothesis the source's display needs. -/
theorem isGE_zero_of_representsIdentityOnPerfect
    (K : DerivedCategory (Limits.pullback f f).Modules)
    (hK : perfectDerivedObjects (Limits.pullback f f) K)
    (hΦ : RepresentsIdentityOnPerfect f K) :
    K.IsGE 0 := by
  have := isNoetherian_pullback_self f
  obtain ⟨n₀, hn₀⟩ :=
    (Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect
      (Limits.pullback f f) K hK).1.1
  have hbase : K.IsGE n₀ := (DerivedCategory.isGE_iff K n₀).2 fun n hn => hn₀ n hn
  have step : ∀ n : ℕ, K.IsGE (min 0 (n₀ + n)) := by
    intro n
    induction n with
    | zero =>
      have := hbase
      exact DerivedCategory.TStructure.t.isGE_of_ge K (min 0 (n₀ + (0 : ℕ))) n₀ (by simp)
    | succ n ih =>
      rcases le_or_gt 0 (n₀ + (n : ℤ)) with hle | hlt
      · have := ih
        exact DerivedCategory.TStructure.t.isGE_of_ge K (min 0 (n₀ + ((n : ℤ) + 1)))
          (min 0 (n₀ + (n : ℤ))) (by omega)
      · have hmin : min 0 (n₀ + (n : ℤ)) = n₀ + (n : ℤ) := by omega
        rw [hmin] at ih
        have hzero := isZero_homology_of_isGE_of_neg f K hK hΦ (n₀ + (n : ℤ)) hlt ih
        have : K.IsGE (n₀ + (n : ℤ) + 1) := by
          refine (DerivedCategory.isGE_iff K (n₀ + (n : ℤ) + 1)).2 fun m hm => ?_
          rcases lt_or_eq_of_le (by omega : m ≤ n₀ + (n : ℤ)) with hm' | rfl
          · exact (DerivedCategory.isGE_iff K (n₀ + (n : ℤ))).1 ih m hm'
          · exact hzero
        exact DerivedCategory.TStructure.t.isGE_of_ge K (min 0 (n₀ + ((n : ℤ) + 1)))
          (n₀ + (n : ℤ) + 1) (by omega)
  have hfin := step (-n₀).toNat
  have : min 0 (n₀ + ((-n₀).toNat : ℤ)) = 0 := by omega
  rwa [this] at hfin

end Stacks.Duality

end
