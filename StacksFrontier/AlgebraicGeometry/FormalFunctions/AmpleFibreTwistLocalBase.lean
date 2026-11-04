module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.AmpleFibreTwistVanishing
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.FormalFunctionsFrom02O8
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesCohomologyFiniteReduction
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.TwistAdicQuotient
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.TransitionKernelTwistVanishingPos
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.NeighbourhoodHoms
public import StacksFrontier.AlgebraicGeometry.GradedProperCohomology.ProperCohomologyFiniteness
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence

/-!
# Both clauses of Tag 0D2M over a Noetherian local base

Let `A` be a Noetherian local ring with maximal ideal `𝔪`, `f : X ⟶ Spec A` proper, `ℒ` an
invertible `𝒪_X`-module whose restriction to the closed fibre `X_y = V(𝔪 𝒪_X)` is ample, and `ℱ`
a coherent `𝒪_X`-module. Write `ℱ(d) = ℱ ⊗ ℒ ^⊗ d` and `𝓘 = 𝔪 · 𝒪_X`. This file proves that there
is one `d₀` such that for every `d ≥ d₀`

1. `H ᵖ(X, ℱ(d)) = 0` for every `p > 0`, and
2. `H ⁰(X, ℱ(d)) ⟶ H ⁰(X, ℱ(d) / 𝓘 ℱ(d))` is surjective.

This is the situation the source's proof of [Stacks, Tag 0D2M] reduces to in its first
paragraph; the reduction itself (flat base change along `Spec 𝒪_{Y,y} ⟶ Y`) and the statement at
the stalk are in `AmpleFibreTwistBaseChange`, `AmpleFibreTwistStalkVanishing` and
`AmpleFibreTwistStalkSurjective`. The Nakayama step of the last paragraph of the source's proof
is `Stacks.Cohomology.FormalFunctions.subsingleton_cohomologyOverBase_of_subsingleton_tower`
(`AmpleFibreTwistVanishing.lean`).

## Main results

* `Stacks.Cohomology.FormalFunctions.subsingleton_cohomology_idealPowerQuotient` and
  `Stacks.Cohomology.FormalFunctions.surjective_cohomology_idealPowerQuotientDrop`: **the
  dévissage along the tower** `n ↦ ℱ(d) / 𝓘 ⁿ ℱ(d)`, in positive degrees and in degree zero.
* `Stacks.Cohomology.FormalFunctions.subsingleton_cohomologyOverBase_of_isCoherent` and
  `Stacks.Cohomology.FormalFunctions.surjective_adicCohomologyProj_one_of_isCoherent`: the two
  conclusions at one coherent module, from the vanishing of the whole tower and from the
  surjectivity along it.
* `Stacks.Cohomology.FormalFunctions`
  `.exists_subsingleton_cohomologyOverBase_adicQuotientTransitionKernel`: **the graded input**,
  [Stacks, Tag 0897] part (2) for the subquotients `𝓘 ⁿ ℱ(d) / 𝓘 ⁿ⁺¹ ℱ(d)` — one `d₀` serving
  every positive degree, every `d ≥ d₀` and every `n`.
* `Stacks.Cohomology.FormalFunctions.exists_subsingleton_and_surjective_twistModule`: **both
  clauses over a local base.**

## How the source's inputs are supplied

* the finiteness of `H ᵖ(X, ℱ(d))` over `A` is [Stacks, Tag 02O6],
  `Stacks.AlgebraicGeometry.GradedProperCohomology.tag02O6`;
* the clauses of [Stacks, Tag 02OB] come from [Stacks, Tag 02O8]
  (`Stacks.Cohomology.FormalFunctions.isCohomologyReesFinite`) through
  `Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8`;
* the graded vanishing the source takes from [Stacks, Tag 0897] part (2) on the fibre is
  `Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule_of_pos`, run over the
  Rees algebra of `𝓘` on `X`; the subquotients are annihilated by `𝓘`, so only ampleness of `ℒ`
  on `V(𝓘) = X_y` enters. That the subquotients of a twist are the twists of the subquotients is
  `Stacks.Cohomology.FormalFunctions.twistTransitionKernelIso`;
* the induction along `0 → 𝓘 ⁿ ℱ(d) / 𝓘 ⁿ⁺¹ ℱ(d) → ℱ(d) / 𝓘 ⁿ⁺¹ ℱ(d) → ℱ(d) / 𝓘 ⁿ ℱ(d) → 0`
  is run here in both degrees the source uses it in;
* Nakayama's lemma ([Stacks, Tag 00DV]) closes clause (1), and clause (3) of
  [Stacks, Tag 02OB] in degree zero closes clause (2).

## Implementation notes

The subquotient `𝓘 ⁿ ℱ / 𝓘 ⁿ⁺¹ ℱ` is realized as the kernel of the exponent-lowering map
`ℱ / 𝓘 ⁿ⁺¹ ℱ ⟶ ℱ / 𝓘 ⁿ ℱ` (`adicQuotientTransitionKernel`), an epimorphism, so it sits in a short
exact sequence and the long exact sequence of
`Stacks.Cohomology.FormalFunctions.cohomologyDeltaFunctor` applies. The transition kernels of the
tower of `ℱ` are those of the object of `Coh(X, 𝓘)` that `Stacks.Algebraization.completionFunctor`
produces, which is what the graded vanishing is stated for; the identification is
`transitionKernelIsoAdicQuotientTransitionKernel`.

## References

* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0884](https://stacks.math.columbia.edu/tag/0884)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits


universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Cohomology.FormalFunctions

open Stacks.Ample Stacks.AlgebraicGeometry.HyperplaneTwistSequence
open Stacks.Algebraization Stacks.Cohomology.AffineBase

/-! ### The tower of adic quotients and its transition kernels -/

/-- Lowering the exponent on an adic quotient is an epimorphism: it is
`Stacks.Algebraization.idealPowerQuotientMap` at the identity of the module, and that map is
an epimorphism whenever the map of modules it is built from is one. -/
public instance epi_idealPowerQuotientDrop {X : Scheme.{u}} (J : X.IdealSheafData) {m n : ℕ}
    (h : n ≤ m) (M : X.Modules) :
    Epi (idealPowerQuotientDrop J h M) :=
  epi_idealPowerQuotientMap J J m n (Scheme.IdealSheafData.pow_le_pow_of_le J h) (𝟙 M)

/-- **The transition kernel of the tower of adic quotients**, `Ker(ℱ / 𝓘 ᵐ ℱ ⟶ ℱ / 𝓘 ⁿ ℱ)`.
For `m = n + 1` this is the subquotient `𝓘 ⁿ ℱ / 𝓘 ⁿ⁺¹ ℱ`, the sheaf whose cohomology the
graded vanishing of [Stacks, Tag 0897] part (2) controls. -/
public abbrev adicQuotientTransitionKernel {X : Scheme.{u}} (J : X.IdealSheafData) {m n : ℕ}
    (h : n ≤ m) (M : X.Modules) : X.Modules :=
  kernel (idealPowerQuotientDrop J h M)

/-- The short complex `Ker(τ) → ℱ / 𝓘 ᵐ ℱ → ℱ / 𝓘 ⁿ ℱ` cut out by the exponent-lowering map. -/
public def adicQuotientTransitionShortComplex {X : Scheme.{u}} (J : X.IdealSheafData) {m n : ℕ}
    (h : n ≤ m) (M : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (C := X.Modules) (kernel.ι (idealPowerQuotientDrop J h M))
    (idealPowerQuotientDrop J h M) (kernel.condition _)

/-- **`0 → Ker(τ) → ℱ / 𝓘 ᵐ ℱ → ℱ / 𝓘 ⁿ ℱ → 0` is short exact.** The second map is an
epimorphism and the first is its kernel. -/
public lemma adicQuotientTransitionShortComplex_shortExact {X : Scheme.{u}}
    (J : X.IdealSheafData) {m n : ℕ} (h : n ≤ m) (M : X.Modules) :
    (adicQuotientTransitionShortComplex J h M).ShortExact :=
  ShortComplex.shortExact_mk_kernel_ι _

/-- Lowering the exponent twice is lowering it once: both composites are determined by their
compatibility with the quotient projection, which is an epimorphism. -/
public lemma idealPowerQuotientDrop_comp {X : Scheme.{u}} (J : X.IdealSheafData) {k m n : ℕ}
    (h₁ : n ≤ m) (h₂ : m ≤ k) (M : X.Modules) :
    idealPowerQuotientDrop J h₂ M ≫ idealPowerQuotientDrop J h₁ M =
      idealPowerQuotientDrop J (h₁.trans h₂) M :=
  (cancel_epi (cokernel.π (C := X.Modules) (idealPowerMultiple J k M).ι)).1 <| by
    rw [← Category.assoc, idealPowerQuotientDrop_π, idealPowerQuotientDrop_π,
      idealPowerQuotientDrop_π]

/-- **`ℱ / 𝓘 ⁰ ℱ` is a zero object**: the zeroth ideal-power multiple is all of `ℱ`, so its
inclusion is a split epimorphism and the cokernel vanishes. -/
public lemma isZero_idealPowerQuotient_zero {X : Scheme.{u}} (J : X.IdealSheafData)
    (M : X.Modules) : IsZero (idealPowerQuotient J 0 M) := by
  have : Epi (C := X.Modules) (idealPowerMultiple J 0 M).ι := by
    rw [idealPowerMultiple_zero J M]
    exact SplitEpi.epi ⟨factorThroughTop (𝟙 M), factorThroughTop_comp_ι (𝟙 M)⟩
  exact isZero_cokernel_of_epi (C := X.Modules) (idealPowerMultiple J 0 M).ι

/-! ### Two element-level consequences of exactness -/

/-- A module squeezed between two zero modules in an exact sequence is zero. -/
private lemma subsingleton_of_exact_middle {R : Type u} [Ring R]
    {S : ShortComplex (ModuleCat.{u} R)} (hex : S.Exact) (hM : Subsingleton S.X₁)
    (hP : Subsingleton S.X₃) : Subsingleton S.X₂ := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hex
  have hz : ∀ z : S.X₂, z = 0 := fun z => by
    obtain ⟨w, hw⟩ := (hex z).1 (@Subsingleton.elim _ hP _ 0)
    rw [← hw, @Subsingleton.elim _ hM w 0, map_zero]
  exact ⟨fun x y => by rw [hz x, hz y]⟩

/-- A map whose cokernel is controlled by a zero module in an exact sequence is surjective. -/
private lemma surjective_of_exact_subsingleton {R : Type u} [Ring R]
    {S : ShortComplex (ModuleCat.{u} R)} (hex : S.Exact) (hP : Subsingleton S.X₃) :
    Function.Surjective S.f.hom := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hex
  exact fun y => (hex y).1 (@Subsingleton.elim _ hP _ 0)

/-- The hypothesis of `exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8`, supplied by
[Stacks, Tag 02O8]. -/
private lemma isReesFinite_cohomologyIdealPowerSystem_of_isCoherent (A' : Type u) [CommRing A']
    [IsNoetherianRing A'] (I' : Ideal A') (X' : Over (Spec (.of A')))
    (hX' : IsProper X'.hom) (F' : X'.left.Modules)
    (hF' : Stacks.SheafOfModules.IsCoherent F') (p' : ℕ) :
    IsCohomologyReesFinite I' X' F' p' :=
  have : _root_.SheafOfModules.IsCoherent F' := ⟨hF'.1, hF'.2⟩
  isCohomologyReesFinite I' X' F' p' hX'

/-! ### The dévissage along the tower -/

/-- **The dévissage of the tower, in positive degrees.** If `H ᵖ(X, −)` kills every transition
kernel `Ker(ℱ / 𝓘 ⁿ⁺¹ ℱ ⟶ ℱ / 𝓘 ⁿ ℱ)`, then it kills every term `ℱ / 𝓘 ⁿ ℱ` of the tower.

This is the induction along the short exact sequences
`0 → 𝓘 ⁿ ℱ / 𝓘 ⁿ⁺¹ ℱ → ℱ / 𝓘 ⁿ⁺¹ ℱ → ℱ / 𝓘 ⁿ ℱ → 0`
that the source of [Stacks, Tag 0D2M] runs, with `ℱ / 𝓘 ⁰ ℱ = 0` as the base case. -/
public lemma subsingleton_cohomology_idealPowerQuotient {X : Scheme.{u}} (J : X.IdealSheafData)
    (M : X.Modules) (p : ℕ)
    (hker : ∀ k : ℕ, Subsingleton (((moduleGlobalSections X).rightDerived p).obj
      (adicQuotientTransitionKernel J (Nat.le_succ k) M))) :
    ∀ n : ℕ, Subsingleton (((moduleGlobalSections X).rightDerived p).obj
      (idealPowerQuotient J n M))
  | 0 =>
      ModuleCat.subsingleton_of_isZero
        (Functor.map_isZero _ (isZero_idealPowerQuotient_zero J M))
  | n + 1 =>
      subsingleton_of_exact_middle
        ((cohomologyDeltaFunctor X).exact_map
          (adicQuotientTransitionShortComplex_shortExact J (Nat.le_succ n) M) p)
        (hker n) (subsingleton_cohomology_idealPowerQuotient J M p hker n)

/-- **The dévissage of the tower, in degree zero.** Vanishing of `H ¹` of every transition
kernel makes every transition map of the tower surjective on `H ⁰`, hence makes
`H ⁰(X, ℱ / 𝓘 ⁿ⁺ʲ ℱ) ⟶ H ⁰(X, ℱ / 𝓘 ⁿ ℱ)` surjective for every `j`. -/
public lemma surjective_cohomology_idealPowerQuotientDrop {X : Scheme.{u}}
    (J : X.IdealSheafData) (M : X.Modules)
    (hker : ∀ k : ℕ, Subsingleton (((moduleGlobalSections X).rightDerived 1).obj
      (adicQuotientTransitionKernel J (Nat.le_succ k) M))) (n m : ℕ) (h : n ≤ m) :
    Function.Surjective (((moduleGlobalSections X).rightDerived 0).map
      (idealPowerQuotientDrop J h M)).hom := by
  induction m, h using Nat.le_induction with
  | base =>
      have hid : ((moduleGlobalSections X).rightDerived 0).map
          (idealPowerQuotientDrop J (le_refl n) M) = 𝟙 _ := by
        rw [show idealPowerQuotientDrop J (le_refl n) M = 𝟙 _ from
          idealPowerQuotientMap_id J n M]
        exact CategoryTheory.Functor.map_id _ _
      rw [hid]
      exact fun y => ⟨y, rfl⟩
  | succ m hnm ih =>
      have hstep : Function.Surjective (((moduleGlobalSections X).rightDerived 0).map
          (idealPowerQuotientDrop J (Nat.le_succ m) M)).hom :=
        surjective_of_exact_subsingleton
          ((cohomologyDeltaFunctor X).exact_δ₁
            (adicQuotientTransitionShortComplex_shortExact J (Nat.le_succ m) M) 0) (hker m)
      change Function.Surjective (((moduleGlobalSections X).rightDerived 0).map
        (idealPowerQuotientDrop J (hnm.trans (Nat.le_succ m)) M)).hom
      rw [← idealPowerQuotientDrop_comp J hnm (Nat.le_succ m) M, Functor.map_comp]
      simpa only [ModuleCat.hom_comp, LinearMap.coe_comp] using ih.comp hstep

/-- **The last paragraph of the source's proof of [Stacks, Tag 0D2M], at one coherent module and
one positive degree.** Over a Noetherian local base, a coherent module whose whole adic-quotient
tower has vanishing `H ᵖ` has vanishing `H ᵖ` itself.

The three inputs are all theorems here. Clause (1) of [Stacks, Tag 02OB] comes from
[Stacks, Tag 02O8] (`Stacks.Cohomology.FormalFunctions.isCohomologyReesFinite`) through
`exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8`; it produces the bound `c`, and the
tower is used at the single exponent `c + 1`, the smallest one for which `𝔪 ⁿ⁻ᶜ ⊆ 𝔪`. The
finiteness of `H ᵖ(X, 𝒢)` over `A` is [Stacks, Tag 02O6]
(`Stacks.AlgebraicGeometry.GradedProperCohomology.tag02O6`). Nakayama's lemma then concludes, by
`subsingleton_cohomologyOverBase_of_subsingleton_tower`. -/
public theorem subsingleton_cohomologyOverBase_of_isCoherent
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] (G : X.Modules) (hG : G.IsCoherent) (p : ℕ)
    (htower : ∀ n : ℕ,
      Subsingleton (adicCohomologyTower A f (IsLocalRing.maximalIdeal A) G p n)) :
    Subsingleton (cohomologyOverBase A f p G) := by
  obtain ⟨c, hc, -, -⟩ :=
    exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8 A f ‹IsProper f›
      (IsLocalRing.maximalIdeal A) G ⟨hG.1, hG.2⟩ p
      isReesFinite_cohomologyIdealPowerSystem_of_isCoherent
  exact subsingleton_cohomologyOverBase_of_subsingleton_tower A f G p c (c + 1)
    (Nat.lt_succ_self c)
    (Stacks.AlgebraicGeometry.GradedProperCohomology.tag02O6 A ‹IsNoetherianRing A› X f
      ‹IsProper f› G hG p)
    (htower (c + 1)) (hc (c + 1) (Nat.le_succ c))

/-- **Clause (2) of [Stacks, Tag 0D2M] over a local base, at one coherent module.** Over a
Noetherian local base, if the transition maps of the adic-quotient tower of a coherent `𝒢` are
surjective on `H ⁰`, then `H ⁰(X, 𝒢) ⟶ H ⁰(X, 𝒢 / 𝓘 𝒢)` is surjective.

This is clause (3) of [Stacks, Tag 02OB] read in degree zero at the exponents `n = 1` and
`k = 1 + c`: that clause identifies the image of `H ⁰(X, 𝒢 / 𝓘 ¹⁺ᶜ 𝒢)` in `H ⁰(X, 𝒢 / 𝓘 𝒢)` with
the image of `H ⁰(X, 𝒢)`, and the hypothesis makes the former everything. -/
public theorem surjective_adicCohomologyProj_one_of_isCoherent
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] (G : X.Modules) (hG : G.IsCoherent)
    (hdrop : ∀ (m : ℕ) (h : 1 ≤ m), Function.Surjective
      (((moduleGlobalSections X).rightDerived 0).map
        (idealPowerQuotientDrop (baseIdealSheaf A (IsLocalRing.maximalIdeal A) f) h G)).hom) :
    Function.Surjective (adicCohomologyProj A f (IsLocalRing.maximalIdeal A) G 0 1) := by
  obtain ⟨c, -, -, hrange⟩ :=
    exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8 A f ‹IsProper f›
      (IsLocalRing.maximalIdeal A) G ⟨hG.1, hG.2⟩ 0
      isReesFinite_cohomologyIdealPowerSystem_of_isCoherent
  intro y
  obtain ⟨z, hz⟩ := hdrop (1 + c) (Nat.le_add_right 1 c) y
  have hmem := LinearMap.mem_range_self (((moduleGlobalSections X).rightDerived 0).map
    (idealPowerQuotientDrop (baseIdealSheaf A (IsLocalRing.maximalIdeal A) f)
      ((Nat.le_add_right 1 c).trans (le_refl (1 + c))) G)).hom z
  rw [hrange 1 (1 + c) le_rfl] at hmem
  obtain ⟨w, hw⟩ := hmem
  exact ⟨w, hw.trans hz⟩

/-! ### The graded input: the uniform vanishing on the transition kernels of the tower -/

/-- **The transition kernels of the completion of `ℱ` are the transition kernels of its adic
tower.**

`Stacks.Algebraization.NeighbourhoodHoms.towerIso` identifies the `n`-th term of the completion
with `ℱ / 𝓘 ⁿ⁺¹ ℱ` and `Stacks.Algebraization.NeighbourhoodHoms.towerIso_naturality` carries the
transition maps across, so the kernels correspond. At `n = 0` the source's kernel is the zeroth
term itself, and `ℱ / 𝓘 ⁰ ℱ` is a zero object, so the kernel of the exponent-lowering map into it
is the whole of `ℱ / 𝓘 ℱ`. -/
private def transitionKernelIsoAdicQuotientTransitionKernel
    {X : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X] (J : X.IdealSheafData)
    (F : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf) (n : ℕ) :
    Stacks.Coherent.transitionKernel ((completionFunctor X J).obj F) n ≅
      adicQuotientTransitionKernel J (Nat.le_succ n) F.obj :=
  match n with
  | 0 =>
      Stacks.Algebraization.NeighbourhoodHoms.towerIso J F 0 ≪≫
        ((kernelIsoOfEq ((isZero_idealPowerQuotient_zero J F.obj).eq_of_tgt
          (idealPowerQuotientDrop J (Nat.le_succ 0) F.obj) 0)).trans
            kernelZeroIsoSource).symm
  | n + 1 =>
      kernel.mapIso _ _ (Stacks.Algebraization.NeighbourhoodHoms.towerIso J F (n + 1))
        (Stacks.Algebraization.NeighbourhoodHoms.towerIso J F n)
        ((Stacks.Algebraization.NeighbourhoodHoms.towerIso_naturality J F
            (Nat.le_succ n)).trans
          (congrArg (fun g => (Stacks.Algebraization.NeighbourhoodHoms.towerIso J F (n + 1)).hom ≫
              g)
            (adicQuotientSystem_map_eq_idealPowerQuotientDrop J F.obj
              (Nat.add_le_add_right (Nat.le_succ n) 1))))

/-- **[Stacks, Tag 0897] part (2) for the twists of the transition kernels of the `𝓘`-adic
tower.** Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `f : X ⟶ Spec A` proper, `ℱ` coherent
and `ℒ` an invertible `𝒪_X`-module whose restriction to the closed subscheme `V(𝓘)` is ample,
for `𝓘 = I · 𝒪_X`. Then there is one `d₀` such that

`H ᵖ(X, 𝓘 ⁿ ℱ(d) / 𝓘 ⁿ⁺¹ ℱ(d)) = 0` for every `p > 0`, every `d ≥ d₀` and **every** `n`,

for `ℱ(d) = ℱ ⊗ ℒ ^⊗ d`.

Two results of the library combine. The tower `n ↦ ℱ / 𝓘 ⁿ⁺¹ ℱ` is an object of `Coh(X, 𝓘)`
(`Stacks.Algebraization.completionFunctor`), so
`Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule_of_pos` — [Stacks,
Tag 0884] in every positive degree, which runs [Stacks, Tag 087Z] and then [Stacks, Tag 0897]
part (2) over the Rees algebra — gives one `d₀` above which every twist of every transition
kernel of that tower has vanishing cohomology in every positive degree. And the transition
kernels of the tower of a twist are the twists of the transition kernels, by
`Stacks.Cohomology.FormalFunctions.twistTransitionKernelIso`, because `ℒ ^⊗ d` is invertible.
The uniformity in `n` is the whole point and comes from the single coherent module on
`Spec_X(⨁ₙ 𝓘 ⁿ)` that [Stacks, Tag 0884] is proved through.

Ampleness is asked for on `V(𝓘)` and nowhere else, because the transition kernels are
annihilated by `𝓘` and so is the module on `Spec_X(⨁ₙ 𝓘 ⁿ)` that carries the vanishing; that is
the hypothesis of the degree-`p` form of [Stacks, Tag 0884] used here. -/
public theorem exists_subsingleton_cohomologyOverBase_adicQuotientTransitionKernel
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f] (L : X.Modules) [IsInvertibleModule X L]
    (hL : IsAmple (baseIdealSheaf A I f).subscheme
      (Stacks.AmpleLocallyClosed.pullbackModule (baseIdealSheaf A I f).subschemeι L))
    (F : X.Modules) (hF : F.IsCoherent) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ p : ℕ, 0 < p → ∀ n : ℕ,
      Subsingleton (cohomologyOverBase A f p
        (adicQuotientTransitionKernel (baseIdealSheaf A I f) (Nat.le_succ n)
          (twistModule X L F d))) := by
  let : AlgebraicGeometry.IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : F.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent F
  obtain ⟨d₀, hd₀⟩ :=
    Stacks.Coherent.exists_isZero_Hgroup_transitionKernel_tensorPowModule_of_pos A I f L hL
      ((completionFunctor X (baseIdealSheaf A I f)).obj ⟨F, hF⟩)
  refine ⟨d₀, fun d hd p hp n => ?_⟩
  -- The vanishing for the transition kernels of the tower of `ℱ`, twisted.
  have h1 := hd₀ n d hd p hp
  have h2 : IsZero (Hgroup X.ringCatSheaf ⊤ p
      ((Stacks.AlgebraicGeometry.RelativeSerreVanishing.twistFunctor L d).obj
        (adicQuotientTransitionKernel (baseIdealSheaf A I f) (Nat.le_succ n) F))) :=
    (Iso.isZero_iff ((Hfunctor X.ringCatSheaf ⊤ p).mapIso
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf,
        Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf (forget₂ CommRingCat RingCat)
          (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X)⟩).flip.obj
        (tensorPowModule X L d)).mapIso
          (transitionKernelIsoAdicQuotientTransitionKernel
            (baseIdealSheaf A I f) ⟨F, hF⟩ n)))).mp h1
  -- The transition kernels of the tower of the twist are the twists of those of `ℱ`.
  have h3 : IsZero (Hgroup X.ringCatSheaf ⊤ p
      (adicQuotientTransitionKernel (baseIdealSheaf A I f) (Nat.le_succ n)
        (twistModule X L F d))) :=
    (Iso.isZero_iff ((Hfunctor X.ringCatSheaf ⊤ p).mapIso
      (twistTransitionKernelIso A f L d I (Nat.le_succ n) F))).mp h2
  exact ModuleCat.subsingleton_of_isZero (Functor.map_isZero _
    (Stacks.Cohomology.Affine.isZero_rightDerived_evaluation_of_isZero_Hgroup
      X.ringCatSheaf ⊤ p _ h3))

/-- **Stacks Project, Tag 0D2M over a local base, both clauses.**

Let `A` be a Noetherian local ring with maximal ideal `𝔪`, let `f : X ⟶ Spec A` be a proper
morphism of schemes, let `ℒ` be an invertible `𝒪_X`-module whose restriction to the closed fibre
`X_y = V(𝔪 𝒪_X)` is ample, and let `ℱ` be a
coherent `𝒪_X`-module; write `ℱ(d) = ℱ ⊗_{𝒪_X} ℒ ^⊗ d` and `𝓘 = 𝔪 · 𝒪_X`. Then there is one `d₀`
such that for every `d ≥ d₀`

1. `H ᵖ(X, ℱ(d)) = 0` for every `p > 0`, and
2. `H ⁰(X, ℱ(d)) ⟶ H ⁰(X, ℱ(d) / 𝓘 ℱ(d))` is surjective.

Over `Spec A` with `y` the closed point these are the two displays of [Stacks, Tag 0D2M]: the
source's `R ᵖ f_*(ℱ(d))_y` is `H ᵖ(X, ℱ(d))`, and `ℱ(d) / 𝓘 ℱ(d)` is `ℱ_y ⊗ ℒ_y ^⊗ d` pushed
forward along the closed immersion `X_y ⟶ X`, whose cohomology is the cohomology on `X_y` by
[Stacks, Tag 01E8]'s affine-morphism case. This is the reduction the source's first paragraph
makes.

Ampleness is the source's own hypothesis: `ℒ_y` is ample on the closed fibre `X_y`. The fibre is
the closed subscheme `V(𝓘)` cut out by `𝓘 = 𝔪 · 𝒪_X`, which is the scheme-theoretic fibre
`X ×_{Spec A} Spec(A/𝔪)` of `f` over `y`, and `ℒ_y` is the restriction of `ℒ` to it. Nothing of
`ℒ` away from the fibre enters the proof: the subquotients `𝓘 ⁿ ℱ(d) / 𝓘 ⁿ⁺¹ ℱ(d)` that the
graded input is about are annihilated by `𝓘`, so the coherent module on `Spec_X(⨁ₙ 𝓘 ⁿ)` through
which [Stacks, Tag 0884] proves the vanishing lives on a closed subscheme affine over `X_y`, and
the vanishing is read there.

Every step of the source's proof is carried out. The graded input, [Stacks, Tag 0897] part (2)
applied to the graded module `⨁ₙ 𝔪 ⁿ ℱ(d) / 𝔪 ⁿ⁺¹ ℱ(d)`, is
`exists_subsingleton_cohomologyOverBase_adicQuotientTransitionKernel`: one `d₀` serving every
`p > 0`, every `d ≥ d₀` and every `n`, obtained from [Stacks, Tag 0884] in every positive degree
over the Rees algebra of `𝓘` together with the fact that twisting by an invertible module
commutes with the adic quotients. The dévissage along the short exact sequences
`0 → 𝓘 ⁿ ℱ(d) / 𝓘 ⁿ⁺¹ ℱ(d) → ℱ(d) / 𝓘 ⁿ⁺¹ ℱ(d) → ℱ(d) / 𝓘 ⁿ ℱ(d) → 0` is
`subsingleton_cohomology_idealPowerQuotient` in positive degrees and
`surjective_cohomology_idealPowerQuotientDrop` in degree zero; the three clauses of
[Stacks, Tag 02OB] come from [Stacks, Tag 02O8] through
`exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8`; the finiteness of `H ᵖ(X, ℱ(d))`
over `A` is [Stacks, Tag 02O6]; and Nakayama's lemma closes clause (1) while clause (3) of
[Stacks, Tag 02OB] in degree zero closes clause (2). -/
@[ega "III 5.2.3" "(ii), special case"]
public theorem exists_subsingleton_and_surjective_twistModule
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f]
    (F L : X.Modules) [IsInvertibleModule X L] [F.IsCoherent]
    (hL : IsAmple (baseIdealSheaf A (IsLocalRing.maximalIdeal A) f).subscheme
      (Stacks.AmpleLocallyClosed.pullbackModule
        (baseIdealSheaf A (IsLocalRing.maximalIdeal A) f).subschemeι L)) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      (∀ p : ℕ, 0 < p → Subsingleton (cohomologyOverBase A f p (twistModule X L F d))) ∧
        Function.Surjective (adicCohomologyProj A f (IsLocalRing.maximalIdeal A)
          (twistModule X L F d) 0 1) := by
  obtain ⟨d₀, hd₀⟩ := exists_subsingleton_cohomologyOverBase_adicQuotientTransitionKernel A
    (IsLocalRing.maximalIdeal A) f L hL F ‹F.IsCoherent›
  refine ⟨d₀, fun d hd => ⟨fun p hp => ?_, ?_⟩⟩
  · exact subsingleton_cohomologyOverBase_of_isCoherent A f (twistModule X L F d)
      (AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X F
        (tensorPowModule X L d)) p
      (subsingleton_cohomology_idealPowerQuotient
        (baseIdealSheaf A (IsLocalRing.maximalIdeal A) f) (twistModule X L F d) p
        fun k => hd₀ d hd p hp k)
  · exact surjective_adicCohomologyProj_one_of_isCoherent A f (twistModule X L F d)
      (AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible X F
        (tensorPowModule X L d))
      fun m h => surjective_cohomology_idealPowerQuotientDrop
        (baseIdealSheaf A (IsLocalRing.maximalIdeal A) f) (twistModule X L F d)
        (fun k => hd₀ d hd 1 Nat.one_pos k) 1 m h

end Stacks.Cohomology.FormalFunctions

end
