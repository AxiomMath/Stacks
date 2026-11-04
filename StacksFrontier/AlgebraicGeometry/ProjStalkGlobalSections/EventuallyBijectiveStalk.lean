module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.EventuallyBijective
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.Stalk

/-!
# Fiberwise bijectivity restricts to the stalk submodule

Let `S = ⨁_{n ≥ 0} 𝒮 n` be a nonnegatively graded ring and let `φ : M →ₗ[S] N` be a
degree-preserving linear map of `ℤ`-graded `S`-modules that is bijective on homogeneous components
in every degree `≥ N₀`. By
`ProjSheafFunctoriality.bijective_localizedModule_map_of_eventually_bijective`, the induced map on
the *ambient* localized-module fiber `ModuleFiber 𝒮 x` is bijective at every point `x` of `Proj S`;
this fiber is the full localization of `M` at the homogeneous prime of `x`. The stalk of the
associated sheaf `M̃` is the strictly smaller submodule `degreeZeroModuleAt`, spanned by the
fractions with numerator and denominator homogeneous of the same degree
(`associatedModuleSheafStalkEquiv` identifies the stalk with this submodule). Under the same
hypotheses, the induced map restricts to a bijection between the degree-zero submodules, i.e. to a
bijection on the stalks.

## Main results

* `bijOn_degreeZeroModuleAt_of_eventually_bijective`: the induced map of ambient fibers restricts
  to a bijection between the degree-zero submodules.

## Implementation notes

`LocalizedModule.map T φ` is already bundled as linear over `Localization T`, not merely over the
base ring `S` (this is stronger than the bundling used to build the comparison map on a single
standard open in `ProjSheafFunctoriality.Basic.degreeZeroLocalizedMap`, which only needed
linearity over the base ring). Composed with the algebra map from `HomogeneousLocalization.AtPrime`
that defines the scalar action on `degreeZeroModuleAt`, this gives `AtPrime`-linearity for free,
which is what drives the `smul` case of the two `Submodule.span_induction` arguments below.

`Set.MapsTo` follows from `Submodule.span_induction` on a generator of the source submodule,
since a degree-preserving map carries a homogeneous fraction to a homogeneous fraction of the
same degree; `Set.SurjOn` is proved by `Submodule.span_induction` on a generator of the *target*
submodule, producing, for a single generator `LocalizedModule.mk n s` of matching degree `d`, a
preimage generator by the same degree-raising argument as the ambient surjectivity proof: a
homogeneous unit `e` outside the prime raises the degree of `n` to the threshold `N₀` by a single
power `e ^ k`, `hsurj` supplies a homogeneous preimage `m` there, and
`LocalizedModule.mk m (⟨e ^ k, _⟩ * s)` is again a matching-degree generator, cancelling back to
`LocalizedModule.mk n s` under the map. `Set.InjOn` is immediate from the ambient injectivity.

## References

* [Stacks Project, Tag 0BXK](https://stacks.math.columbia.edu/tag/0BXK)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite DirectSum
open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.GradedLocalization
open Stacks.AlgebraicGeometry.ProjSerreCorrespondence (exists_homogeneous_pos_degree_notMem)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality
  (bijective_localizedModule_map_of_eventually_bijective)

namespace Stacks.AlgebraicGeometry.ProjStalkGlobalSections

universe u v w

attribute [local instance] ProjectiveSpectrum.isPrime

variable {S : Type u} {M N : Type v} {σ : Type w}
  [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  {τ : Type*} [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒮 𝒨]
  {υ : Type*} [SetLike υ N] [AddSubgroupClass υ N] (𝒩 : ℤ → υ) [Decomposition 𝒩]
  [SetLike.GradedSMul 𝒮 𝒩]

/-- **Fiberwise bijectivity restricted to the stalk.** Under the hypotheses of
`bijective_localizedModule_map_of_eventually_bijective`, the induced map of localized-module
fibers at a point of `Proj S` restricts to a bijection between the degree-zero submodules, i.e.
between the actual stalks of the associated sheaves. -/
theorem bijOn_degreeZeroModuleAt_of_eventually_bijective
    (φ : M →ₗ[S] N) (hφ : ∀ i (m : M), m ∈ 𝒨 i → φ m ∈ 𝒩 i) {N₀ : ℤ}
    (hinj : ∀ j : ℤ, N₀ ≤ j → ∀ m : M, m ∈ 𝒨 j → φ m = 0 → m = 0)
    (hsurj : ∀ j : ℤ, N₀ ≤ j → ∀ n : N, n ∈ 𝒩 j → ∃ m : M, m ∈ 𝒨 j ∧ φ m = n)
    (x : ProjectiveSpectrum.top 𝒮) :
    letI : Module (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
        (ModuleFiber (M := M) 𝒮 x) :=
      Module.compHom _ (algebraMap
        (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
    letI : Module (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
        (ModuleFiber (M := N) 𝒮 x) :=
      Module.compHom _ (algebraMap
        (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
    Set.BijOn (LocalizedModule.map x.asHomogeneousIdeal.toIdeal.primeCompl φ)
      (degreeZeroModuleAt 𝒮 𝒨 x) (degreeZeroModuleAt 𝒮 𝒩 x) := by
  let _ (P : Type v) [AddCommGroup P] [Module S P] :
      Module (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
        (ModuleFiber (M := P) 𝒮 x) :=
    Module.compHom _ (algebraMap
      (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
  classical
  set T := x.asHomogeneousIdeal.toIdeal.primeCompl with hT
  set g := LocalizedModule.map T φ with hg
  have hbij := bijective_localizedModule_map_of_eventually_bijective 𝒮 𝒨 𝒩 φ hφ hinj hsurj x
  have hsmul : ∀ (c : HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (a : ModuleFiber (M := M) 𝒮 x), g (c • a) = c • g a := fun c a => g.map_smul
    (algebraMap (HomogeneousLocalization.AtPrime 𝒮 x.asHomogeneousIdeal.toIdeal)
      (Localization T) c) a
  obtain ⟨e_deg, he_deg, e, he, hex⟩ := exists_homogeneous_pos_degree_notMem 𝒮 x
  refine ⟨?_, fun a _ b _ hab => hbij.1 hab, ?_⟩
  · -- MapsTo
    intro a ha
    induction ha using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨d, m, s, hm, hs, rfl⟩ := hz
        show g (LocalizedModule.mk m s) ∈ degreeZeroModuleAt 𝒮 𝒩 x
        rw [hg, LocalizedModule.map_mk]
        exact Submodule.subset_span ⟨d, φ m, s, hφ d m hm, hs, rfl⟩
    | zero => simpa using Submodule.zero_mem _
    | add a b _ _ iha ihb => simpa [map_add] using Submodule.add_mem _ iha ihb
    | smul c a _ iha => rw [hsmul]; exact Submodule.smul_mem _ c iha
  · -- SurjOn
    intro z hz
    induction hz using Submodule.span_induction with
    | mem w hw =>
        obtain ⟨d, n, s, hn, hs, rfl⟩ := hw
        set k := (N₀ - (d : ℤ)).toNat with hk
        have hge : N₀ ≤ (k : ℤ) * (e_deg : ℤ) + (d : ℤ) := by
          have hd1 : (1 : ℤ) ≤ (e_deg : ℤ) := by exact_mod_cast he_deg
          have h0 : (0 : ℤ) ≤ ((N₀ - (d : ℤ)).toNat : ℤ) := by positivity
          have h1 : N₀ - (d : ℤ) ≤ ((N₀ - (d : ℤ)).toNat : ℤ) := Int.self_le_toNat _
          nlinarith
        have hepow : e ^ k ∈ 𝒮 (k • e_deg) := SetLike.pow_mem_graded k he
        have hnmem : e ^ k • n ∈ 𝒩 ((k : ℤ) * e_deg + d) :=
          SetLike.GradedSMul.smul_mem (A := 𝒮) (B := 𝒩) hepow hn
        obtain ⟨m, hm, hφm⟩ := hsurj _ hge _ hnmem
        have hekT : e ^ k ∈ T := T.pow_mem hex k
        refine ⟨LocalizedModule.mk m (⟨e ^ k, hekT⟩ * s), ?_, ?_⟩
        · exact Submodule.subset_span ⟨k * e_deg + d, m, ⟨e ^ k, hekT⟩ * s, by
            simpa using hm, by simpa using SetLike.mul_mem_graded hepow hs, rfl⟩
        · show g (LocalizedModule.mk m (⟨e ^ k, hekT⟩ * s)) = LocalizedModule.mk n s
          rw [hg, LocalizedModule.map_mk, hφm]
          exact LocalizedModule.mk_cancel_common_left ⟨e ^ k, hekT⟩ s (n : N)
    | zero => exact ⟨0, Submodule.zero_mem _, map_zero g⟩
    | add a b _ _ iha ihb =>
        obtain ⟨wa, hwa, hgwa⟩ := iha
        obtain ⟨wb, hwb, hgwb⟩ := ihb
        exact ⟨wa + wb, Submodule.add_mem _ hwa hwb, by rw [map_add, hgwa, hgwb]⟩
    | smul c a _ iha =>
        obtain ⟨w, hw, hgw⟩ := iha
        exact ⟨c • w, Submodule.smul_mem _ c hw, by rw [hsmul, hgw]⟩

end Stacks.AlgebraicGeometry.ProjStalkGlobalSections

end
