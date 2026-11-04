module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialDividedPowers
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.IdealPowerQuotient

/-!
# Sheaves annihilated by a power of an ideal sheaf

Let `X` be a scheme, `I` a quasi-coherent sheaf of ideals on `X` presented by its affine-local
ideal data, and `M` a sheaf of modules on `X`. The algebraization theorems of Stacks chapter 52
measure the failure of a comparison map to be an isomorphism by asking that its kernel and
cokernel be *annihilated by a power of `I`*: that `I ^ n M = 0` for some `n`, where `I ^ n M` is
the subsheaf `Stacks.Algebraization.idealPowerMultiple`. For an inverse system one asks for a
single `n` that works for every term at once.

This file introduces the two predicates and translates them into the elementwise module language
in which the affine descent arguments are phrased: `I ^ n M = 0` holds exactly when, on every
affine open `U`, every `r ∈ I(U) ^ n` kills every section of `M` over `U`. The translation is an
immediate consequence of the affine-local universal property of `I ^ n M` together with the
vanishing of the sections of the zero subsheaf, and in particular needs no quasi-coherence of
`M`: the condition `I ^ n M ≤ 0` is tested against a submodule whose sections are zero, which is
precisely a family of affine-local inequalities.

Two further facts make the predicates usable. The annihilation condition is preserved on
increasing the exponent, because `I ^ m ≤ I ^ n` for `n ≤ m`; this is what allows two
power-annihilated objects to be put under one common exponent. And on each affine open the
sections of a power-annihilated sheaf are an `I(U)`-power torsion module in the sense of
`IsIPowerTorsion`, which is the hypothesis consumed by the formal glueing descent over the
affine charts.

The elementwise translation also makes the condition *local on the base*: `I ^ n M = 0` may be
checked on an open covering, which is the converse of
`Stacks.Algebraization.idealPowerMultiple_restrict_eq_bot`. Both sides are conditions on the
sections over affine opens, every affine open of `X` is covered by affine opens contained in a
member of the covering, and over such an affine open the restriction map carries `I(V) ^ n` onto
`I(A) ^ n`; the sheaf condition on `M` then promotes the local vanishing of a product `r • x` to
its vanishing. Passing from a *fixed* exponent to the predicate `IsPowerAnnihilated` costs the
quasi-compactness of `X`, since the predicate demands one exponent valid on every affine open
while the local data supply one exponent per open: on a Noetherian scheme the affine opens admit
a finite subcovering and the largest of the finitely many exponents works everywhere. This is why
Stacks 0889 is stated for a Noetherian rather than a locally Noetherian scheme.

## Main definitions

* `Stacks.Algebraization.IsPowerAnnihilated` — a sheaf of modules killed by some power of `I`.
* `Stacks.Algebraization.IsSystemPowerAnnihilated` — an inverse system all of whose terms are
  killed by one common power of `I`.
* `Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower` — a morphism of inverse systems
  whose levelwise kernels and cokernels are all killed by one common positive power of `I`.

## Main results

* `Stacks.Algebraization.bot_submodule_obj_eq_bot` — the sections of the zero subsheaf vanish.
* `Stacks.Algebraization.idealPowerMultiple_eq_bot_iff_affine_smul_top` and
  `Stacks.Algebraization.idealPowerMultiple_eq_bot_iff_affine_sections_annihilated` — the
  affine-local translation of `I ^ n M = 0`, in submodule and in elementwise form.
* `Stacks.Algebraization.affine_sections_annihilated_of_idealPowerMultiple_eq_bot` — the
  direction of that translation used to produce annihilation of sections.
* `Stacks.Algebraization.isPowerAnnihilated_iff_affine_sections_annihilated` and
  `Stacks.Algebraization.isSystemPowerAnnihilated_iff_affine_sections_annihilated` — the same
  for the two predicates.
* `Stacks.Algebraization.idealPowerMultiple_eq_bot_of_le` — annihilation by `I ^ n` implies
  annihilation by `I ^ m` for `n ≤ m`.
* `Stacks.Algebraization.eq_zero_of_affine_cover` — a section vanishes as soon as it vanishes over
  every affine open subordinate to a given open covering.
* `Stacks.Algebraization.affine_sections_annihilated_of_idealPowerMultiple_comap_eq_bot` and
  `Stacks.Algebraization.affine_sections_annihilated_of_idealPowerMultiple_restrict_eq_bot` —
  annihilation of a restriction by `(I|_Y) ^ n` annihilates the sections of `M` over the affine
  opens of the image.
* `Stacks.Algebraization.idealPowerMultiple_eq_bot_of_restrict` — annihilation by a *fixed* power
  of `I` is local on the base.
* `Stacks.Algebraization.isPowerAnnihilated_of_restrict` — on a Noetherian scheme a sheaf
  annihilated by a power of `I|_U` over every affine open is annihilated by a power of `I`.
* `Stacks.Algebraization.IsPowerAnnihilated.exists_pos`,
  `Stacks.Algebraization.IsSystemPowerAnnihilated.exists_pos` and
  `Stacks.Algebraization.IsSystemPowerAnnihilated.exists_common_pos` — the exponent may always be
  taken positive, and two systems may be put under one common positive exponent.
* `Stacks.Algebraization.isIPowerTorsion_sections_of_isPowerAnnihilated` — the sections over an
  affine open of a power-annihilated sheaf are `I(U)`-power torsion.
* `Stacks.Algebraization.isKernelCokernelAnnihilatedByPower_iff_affine_sections_annihilated` —
  the affine-local elementwise form of the condition on a morphism.
* `Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower.exists_kernel_eq_bot`,
  `Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower.exists_cokernel_eq_bot` and
  `Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower.of_exists_kernel_cokernel` — the
  kernel and cokernel halves of the condition, and their recombination into one exponent.
* `Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower.of_le` — annihilation of the
  levelwise kernels and cokernels persists on raising the exponent.
* `Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower.isPowerAnnihilated_kernel` and
  `Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower.isPowerAnnihilated_cokernel` — each
  levelwise kernel, respectively cokernel, is annihilated by a power of `I`.
* `Stacks.Algebraization.IsKernelCokernelAnnihilatedByPower.exists_common_pos` — two such
  morphisms may be put under one common positive exponent.

## Implementation notes

The predicates do *not* require the exponent to be positive. This is harmless and it is the
weaker of the two possible conventions, because the exponent `0` does not trivialize the
condition: `I(U) ^ 0` is the unit ideal, so by
`idealPowerMultiple_eq_bot_iff_affine_sections_annihilated` the case `n = 0` says that `1` kills
every section, that is, that `M` is the zero sheaf. Dropping the positivity hypothesis therefore
makes the predicate easier to establish and no harder to use, and
`IsPowerAnnihilated.exists_pos` lets any consumer that needs a positive exponent — for instance
to produce an `IsIPowerTorsion` hypothesis, whose definition does demand positivity — recover
one by replacing `n` with `n + 1` through `idealPowerMultiple_eq_bot_of_le`.

`IsKernelCokernelAnnihilatedByPower` does by contrast demand a positive exponent, because the
condition it formalizes is stated for `t ≥ 1`. Nothing is lost: the exponent may always be
increased by `IsKernelCokernelAnnihilatedByPower.of_le`, which is what makes the positivity
costless to supply, and carrying it in the predicate means a consumer needing a positive power
of `I` — for instance to obtain `IsIPowerTorsion` sections of a levelwise kernel — reads it off
directly.

The condition on a morphism is phrased with the *levelwise* kernels and cokernels
`kernel (α.app (op k))`, formed in the abelian category `X.Modules`. This is what the source
condition says, and it is not interchangeable with a kernel formed in a category of coherent
adic systems: there the cokernel is computed levelwise but the kernel is not, the discrepancy
being exactly the Artin–Rees stabilization. No abelian structure on a category of adic systems
is therefore presupposed here, and a morphism of inverse systems is all that is required.

An inverse system is a functor out of `ℕᵒᵖ`, matching
`Stacks.Algebraization.AdicInverseSystem`; the predicate quantifies over the natural number
index rather than over objects of `ℕᵒᵖ`, since that is the form in which the terms of an adic
system are named.

The elementwise characterization is stated with the quantifiers in the order
`∀ r ∈ I(U) ^ n, ∀ x`, mirroring `IsIPowerTorsion`, and is derived from the submodule form
`I(U) ^ n · Γ(M, U) = 0` through `Submodule.le_annihilator_iff`, so no induction over products
of ideal elements is needed in either direction.

## References

* [Stacks Project, Tag 0888](https://stacks.math.columbia.edu/tag/0888)
* [Stacks Project, Tag 0889](https://stacks.math.columbia.edu/tag/0889)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u v

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

variable {X : Scheme.{u}}

/-- A sheaf of modules `M` is *annihilated by a power of `I`* if `I ^ n M = 0` for some `n`.

The exponent is not required to be positive; see
`Stacks.Algebraization.IsPowerAnnihilated.exists_pos`. -/
public def IsPowerAnnihilated (I : X.IdealSheafData) (M : X.Modules) : Prop :=
  ∃ n : ℕ, idealPowerMultiple I n M = ⊥

/-- An inverse system of sheaves of modules is *annihilated by a power of `I`* if one common
power of `I` annihilates every one of its terms. -/
public def IsSystemPowerAnnihilated (I : X.IdealSheafData) (F : ℕᵒᵖ ⥤ X.Modules) : Prop :=
  ∃ n : ℕ, ∀ k : ℕ, idealPowerMultiple I n (F.obj (op k)) = ⊥

/-- An ideal annihilates the whole of a module exactly when each of its elements kills each
element of the module. -/
public lemma ideal_smul_top_eq_bot_iff {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (J : Ideal R) :
    J • (⊤ : Submodule R M) = ⊥ ↔ ∀ r ∈ J, ∀ x : M, r • x = 0 := by
  rw [← Submodule.le_annihilator_iff, Submodule.annihilator_top]
  simp [SetLike.le_def, Module.mem_annihilator]

/-- The sections of the zero subsheaf of a module on a scheme vanish over every open.

This is `SheafOfModules.Submodule.bot_obj` for a module presented as `X.Modules`. -/
@[simp]
public lemma bot_submodule_obj_eq_bot (M : X.Modules) (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    (⊥ : M.Submodule).toSubmodule.obj U = ⊥ :=
  SheafOfModules.Submodule.bot_obj M U

/-- **The affine-local translation of annihilation by `I ^ n`.** The subsheaf `I ^ n M` is zero
exactly when `I(U) ^ n · Γ(M, U)` is zero for every affine open `U`.

No quasi-coherence of `M` is needed: the condition `I ^ n M ≤ 0` is the affine-local universal
property of `I ^ n M` tested against a submodule all of whose sections vanish. -/
public theorem idealPowerMultiple_eq_bot_iff_affine_smul_top (I : X.IdealSheafData) (n : ℕ)
    (M : X.Modules) :
    idealPowerMultiple I n M = ⊥ ↔
      ∀ U : X.affineOpens, I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U)) = ⊥ := by
  rw [eq_bot_iff, idealPowerMultiple_le_iff]
  simp only [bot_submodule_obj_eq_bot]
  exact forall_congr' fun _ ↦ le_bot_iff

/-- **The elementwise form of annihilation by `I ^ n`.** The subsheaf `I ^ n M` is zero exactly
when, on every affine open `U`, every element of `I(U) ^ n` kills every section of `M` over
`U`. -/
public theorem idealPowerMultiple_eq_bot_iff_affine_sections_annihilated (I : X.IdealSheafData)
    (n : ℕ) (M : X.Modules) :
    idealPowerMultiple I n M = ⊥ ↔
      ∀ U : X.affineOpens, ∀ r ∈ I.ideal U ^ n, ∀ x : Γ(M, U), r • x = 0 := by
  rw [idealPowerMultiple_eq_bot_iff_affine_smul_top]
  exact forall_congr' fun U ↦ ideal_smul_top_eq_bot_iff _

/-- If `I ^ n M` is zero then `I(U) ^ n` kills the sections of `M` over every affine open `U`. -/
public theorem affine_sections_annihilated_of_idealPowerMultiple_eq_bot {I : X.IdealSheafData}
    {n : ℕ} {M : X.Modules} (hM : idealPowerMultiple I n M = ⊥) (U : X.affineOpens)
    {r : Γ(X, U)} (hr : r ∈ I.ideal U ^ n) (x : Γ(M, U)) : r • x = 0 :=
  (idealPowerMultiple_eq_bot_iff_affine_sections_annihilated I n M).1 hM U r hr x

/-- If `I ^ n M` is zero then so is `I(U) ^ n · Γ(M, U)` over every affine open `U`. -/
public theorem affine_smul_top_eq_bot_of_idealPowerMultiple_eq_bot {I : X.IdealSheafData}
    {n : ℕ} {M : X.Modules} (hM : idealPowerMultiple I n M = ⊥) (U : X.affineOpens) :
    I.ideal U ^ n • (⊤ : Submodule Γ(X, U) Γ(M, U)) = ⊥ :=
  (idealPowerMultiple_eq_bot_iff_affine_smul_top I n M).1 hM U

/-- A sheaf of modules killed affine-locally by `I(U) ^ n` has `I ^ n M = 0`. -/
public theorem idealPowerMultiple_eq_bot_of_affine_sections_annihilated {I : X.IdealSheafData}
    {n : ℕ} {M : X.Modules}
    (hM : ∀ U : X.affineOpens, ∀ r ∈ I.ideal U ^ n, ∀ x : Γ(M, U), r • x = 0) :
    idealPowerMultiple I n M = ⊥ :=
  (idealPowerMultiple_eq_bot_iff_affine_sections_annihilated I n M).2 hM

/-- Annihilation by an ideal power persists on raising the exponent, since `I ^ m ≤ I ^ n` for
`n ≤ m`. This is what lets two power-annihilated objects be put under one common exponent. -/
public theorem idealPowerMultiple_eq_bot_of_le {I : X.IdealSheafData} {M : X.Modules} {n m : ℕ}
    (hM : idealPowerMultiple I n M = ⊥) (hnm : n ≤ m) : idealPowerMultiple I m M = ⊥ := by
  rw [idealPowerMultiple_eq_bot_iff_affine_smul_top] at hM ⊢
  intro U
  exact le_bot_iff.1 ((Submodule.smul_mono_left (Ideal.pow_le_pow_right hnm)).trans (hM U).le)

/-- **Separatedness in the form the covering argument needs.** A section of a sheaf of modules on
a scheme vanishes as soon as its restriction vanishes over every affine open contained both in
its domain and in a member of a given open covering.

Those affine opens do cover the domain, because the affine opens of a scheme form a basis of its
topology; the conclusion is then the sheaf condition for the zero subsheaf of `M`, whose sections
vanish over every open. -/
public theorem eq_zero_of_affine_cover {X : Scheme.{u}} {M : X.Modules} {V : X.Opens}
    (s : Γ(M, V)) {J : Type v} (U : J → X.Opens) (hU : iSup U = ⊤)
    (hs : ∀ (A : X.affineOpens) (j : J) (hAV : A.1 ≤ V), A.1 ≤ U j →
      M.val.map (homOfLE hAV).op s = 0) :
    s = 0 := by
  have hmem : s ∈ (⊥ : M.Submodule).toSubmodule.obj (op V) := by
    refine (⊥ : M.Submodule).isSheaf s ?_
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    have hxU : x ∈ iSup U := by rw [hU]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAV⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ (V ⊓ U j : X.Opens) from ⟨hx, hj⟩) (V ⊓ U j).2
    refine ⟨A, homOfLE (le_trans hAV inf_le_left), ?_, hxA⟩
    have hz := hs ⟨A, hA⟩ j (le_trans hAV inf_le_left) (le_trans hAV inf_le_right)
    exact Eq.mpr (congrArg (fun y => y ∈ (⊥ : M.Submodule).toSubmodule.obj (op A)) hz)
      (Submodule.zero_mem _)
  have hbot : s ∈ (⊥ : Submodule Γ(X, V) Γ(M, V)) := bot_submodule_obj_eq_bot M (op V) ▸ hmem
  exact (Submodule.mem_bot _).1 hbot

/-- A ring map carries an element of the `n`th power of an ideal into the `n`th power of any ideal
containing its image under `Ideal.map`. -/
private theorem apply_mem_pow_of_map_eq {R S : Type*} [CommSemiring R] [CommSemiring S]
    {f : R →+* S} {I : Ideal R} {J : Ideal S} (h : I.map f = J) {n : ℕ} {r : R}
    (hr : r ∈ I ^ n) : f r ∈ J ^ n := by
  rw [← h, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem f hr

/-- **Annihilation transported back across an open immersion.** If `(I|_Y) ⁿ (M|_Y)` vanishes then
`I(f(W)) ⁿ` kills every section of `M` over `f(W)`, for every affine open `W ⊆ Y`.

This reads the comparison of `Stacks.Algebraization.idealPowerMultiple_restrict_eq_bot` in the
other direction. The ideal of `I|_Y` over `W` is the preimage of the ideal of `I` over `f(W)`
under the isomorphism `Γ(X, f(W)) ≅ Γ(Y, W)`, so an element of `I(f(W)) ⁿ` is the image of an
element of `(I|_Y)(W) ⁿ`, and the two scalar actions on the common group of sections agree through
that same isomorphism. -/
public theorem affine_sections_annihilated_of_idealPowerMultiple_comap_eq_bot
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f] {I : X.IdealSheafData} {n : ℕ}
    {M : X.Modules}
    (h : idealPowerMultiple (I.comap f) n ((Scheme.Modules.restrictFunctor f).obj M) = ⊥)
    (W : Y.affineOpens) {r : Γ(X, f ''ᵁ W.1)}
    (hr : r ∈ I.ideal ⟨f ''ᵁ W.1, W.2.image_of_isOpenImmersion f⟩ ^ n)
    (x : Γ(M, f ''ᵁ W.1)) : r • x = 0 := by
  let e := (f.appIso W.1).commRingCatIsoToRingEquiv
  have ha : e r ∈ (I.comap f).ideal W ^ n := by
    refine apply_mem_pow_of_map_eq ?_ hr
    rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
    exact (Ideal.comap_symm e).symm
  have h0 : (f.appIso W.1).inv (e r) • x = 0 :=
    affine_sections_annihilated_of_idealPowerMultiple_eq_bot h W ha x
  rwa [show (f.appIso W.1).inv (e r) = r from e.symm_apply_apply r] at h0

/-- A fixed power of `I|_U` annihilating `M|_U` annihilates the sections of `M` over every affine
open contained in `U`.

Such an affine open is the image of its preimage in `U`, and that preimage is an affine open of
`U` because the inclusion `U ⟶ X` is an open immersion with image `U`. -/
public theorem affine_sections_annihilated_of_idealPowerMultiple_restrict_eq_bot
    {X : Scheme.{u}} {I : X.IdealSheafData} {n : ℕ} {M : X.Modules} {U : X.Opens}
    (h : idealPowerMultiple (I.comap U.ι) n ((Scheme.Modules.restrictFunctor U.ι).obj M) = ⊥)
    {V : X.affineOpens} (hVU : V.1 ≤ U) {r : Γ(X, V.1)} (hr : r ∈ I.ideal V ^ n)
    (x : Γ(M, V.1)) : r • x = 0 := by
  obtain ⟨W, rfl⟩ : ∃ W : U.toScheme.affineOpens,
      (⟨U.ι ''ᵁ W.1, W.2.image_of_isOpenImmersion U.ι⟩ : X.affineOpens) = V :=
    ⟨⟨U.ι ⁻¹ᵁ V.1,
      V.2.preimage_of_isOpenImmersion U.ι (by rwa [Scheme.Opens.opensRange_ι])⟩,
      Subtype.ext (by simpa [Scheme.Hom.image_preimage_eq_opensRange_inf] using hVU)⟩
  exact affine_sections_annihilated_of_idealPowerMultiple_comap_eq_bot U.ι h W hr x

/-- **Annihilation by a fixed power of `I` is local on the base.** It may be checked on an open
covering.

This is the converse of `Stacks.Algebraization.idealPowerMultiple_restrict_eq_bot`. Both sides are
conditions on the sections over the affine opens; every affine open `V` is covered by affine opens
`A` contained in a member of the covering, the restriction map `Γ(X, V) ⟶ Γ(X, A)` carries
`I(V) ^ n` onto `I(A) ^ n`, so the restriction of a product `r • x` with `r ∈ I(V) ^ n` vanishes
over each such `A`, and the sheaf condition on `M` concludes that the product itself vanishes. -/
public theorem idealPowerMultiple_eq_bot_of_restrict {X : Scheme.{u}} (I : X.IdealSheafData)
    (n : ℕ) (M : X.Modules) {J : Type v} (U : J → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ j, idealPowerMultiple (I.comap (U j).ι) n
      ((Scheme.Modules.restrictFunctor (U j).ι).obj M) = ⊥) :
    idealPowerMultiple I n M = ⊥ := by
  refine idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun V r hr x => ?_
  refine eq_zero_of_affine_cover (r • x) U hU fun A j hAV hAU => ?_
  have hrA := apply_mem_pow_of_map_eq (I.map_ideal (U := A) (V := V) hAV) hr
  exact (M.val.map_smul (homOfLE hAV).op r x).trans
    (affine_sections_annihilated_of_idealPowerMultiple_restrict_eq_bot (h j) hAU hrA _)

/-- **The exponent may be made uniform on a Noetherian scheme.** A sheaf of modules annihilated by
some power of `I|_U` over every affine open `U` is annihilated by a single power of `I`.

`Stacks.Algebraization.IsPowerAnnihilated` demands one exponent valid on every affine open at
once, whereas the hypothesis supplies one exponent per open. The quasi-compactness of `X`, which
`IsNoetherian X` provides and `IsLocallyNoetherian X` does not, extracts a *finite* affine
covering from the basis of affine opens; the largest of the finitely many exponents still
annihilates each member by `Stacks.Algebraization.idealPowerMultiple_eq_bot_of_le`, and
`Stacks.Algebraization.idealPowerMultiple_eq_bot_of_restrict` globalizes it. This is the reason
Stacks 0889 is stated for a Noetherian rather than a locally Noetherian scheme. -/
public theorem isPowerAnnihilated_of_restrict {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) (M : X.Modules)
    (h : ∀ U : X.affineOpens, IsPowerAnnihilated (I.comap U.1.ι)
      ((Scheme.Modules.restrictFunctor U.1.ι).obj M)) :
    IsPowerAnnihilated I M := by
  have hbasis : TopologicalSpace.Opens.IsBasis (Set.range fun A : X.affineOpens => A.1) := by
    simpa using X.isBasis_affineOpens
  obtain ⟨κ, hκ, a, heq⟩ := hbasis.exists_iSup_eq_of_isCompact (⊤ : X.Opens) isCompact_univ
  obtain ⟨N, hN⟩ := Finite.exists_le fun k : κ => (h (a k)).choose
  exact ⟨N, idealPowerMultiple_eq_bot_of_restrict I N M (fun k : κ => (a k).1) heq.symm
    fun k => idealPowerMultiple_eq_bot_of_le (h (a k)).choose_spec (hN k)⟩

/-- **Tag 0888.** A sheaf of modules is annihilated by a power of `I` exactly when, for some
single `n`, every element of `I(U) ^ n` kills every section over every affine open `U`. -/
public theorem isPowerAnnihilated_iff_affine_sections_annihilated (I : X.IdealSheafData)
    (M : X.Modules) :
    IsPowerAnnihilated I M ↔
      ∃ n : ℕ, ∀ U : X.affineOpens, ∀ r ∈ I.ideal U ^ n, ∀ x : Γ(M, U), r • x = 0 :=
  exists_congr fun n ↦ idealPowerMultiple_eq_bot_iff_affine_sections_annihilated I n M

/-- **Tag 0888 for an inverse system.** A system is annihilated by a power of `I` exactly when,
for some single `n`, every element of `I(U) ^ n` kills every section of every term over every
affine open `U`. -/
public theorem isSystemPowerAnnihilated_iff_affine_sections_annihilated (I : X.IdealSheafData)
    (F : ℕᵒᵖ ⥤ X.Modules) :
    IsSystemPowerAnnihilated I F ↔
      ∃ n : ℕ, ∀ (k : ℕ) (U : X.affineOpens), ∀ r ∈ I.ideal U ^ n,
        ∀ x : Γ(F.obj (op k), U), r • x = 0 :=
  exists_congr fun n ↦ forall_congr' fun k ↦
    idealPowerMultiple_eq_bot_iff_affine_sections_annihilated I n (F.obj (op k))

namespace IsPowerAnnihilated

/-- Annihilation by a power of `I` may always be witnessed by a *positive* power, by replacing
the exponent `n` by `n + 1`. -/
public theorem exists_pos {I : X.IdealSheafData} {M : X.Modules} (hM : IsPowerAnnihilated I M) :
    ∃ n : ℕ, 0 < n ∧ idealPowerMultiple I n M = ⊥ := by
  obtain ⟨n, hn⟩ := hM
  exact ⟨n + 1, n.succ_pos, idealPowerMultiple_eq_bot_of_le hn (Nat.le_succ n)⟩

/-- A single exponent `n` with `I ^ n M = 0` witnesses the predicate. -/
public theorem of_eq_bot {I : X.IdealSheafData} {M : X.Modules} {n : ℕ}
    (hM : idealPowerMultiple I n M = ⊥) : IsPowerAnnihilated I M :=
  ⟨n, hM⟩

end IsPowerAnnihilated

namespace IsSystemPowerAnnihilated

/-- Each term of a uniformly power-annihilated system is itself annihilated by a power of `I`. -/
public theorem isPowerAnnihilated {I : X.IdealSheafData} {F : ℕᵒᵖ ⥤ X.Modules}
    (hF : IsSystemPowerAnnihilated I F) (k : ℕ) : IsPowerAnnihilated I (F.obj (op k)) :=
  ⟨hF.choose, hF.choose_spec k⟩

/-- Uniform annihilation of a system persists on raising the exponent. -/
public theorem of_le {I : X.IdealSheafData} {F : ℕᵒᵖ ⥤ X.Modules} {n m : ℕ}
    (hF : ∀ k : ℕ, idealPowerMultiple I n (F.obj (op k)) = ⊥) (hnm : n ≤ m) (k : ℕ) :
    idealPowerMultiple I m (F.obj (op k)) = ⊥ :=
  idealPowerMultiple_eq_bot_of_le (hF k) hnm

/-- Uniform annihilation of a system may always be witnessed by a *positive* power of `I`. -/
public theorem exists_pos {I : X.IdealSheafData} {F : ℕᵒᵖ ⥤ X.Modules}
    (hF : IsSystemPowerAnnihilated I F) :
    ∃ n : ℕ, 0 < n ∧ ∀ k : ℕ, idealPowerMultiple I n (F.obj (op k)) = ⊥ := by
  obtain ⟨n, hn⟩ := hF
  exact ⟨n + 1, n.succ_pos, of_le hn (Nat.le_succ n)⟩

/-- Two uniformly power-annihilated systems are annihilated by one common positive power of `I`,
obtained as the larger of the two exponents. This is the form in which the kernel and cokernel
hypotheses of the algebraization theorem are used. -/
public theorem exists_common_pos {I : X.IdealSheafData} {F G : ℕᵒᵖ ⥤ X.Modules}
    (hF : IsSystemPowerAnnihilated I F) (hG : IsSystemPowerAnnihilated I G) :
    ∃ n : ℕ, 0 < n ∧ (∀ k : ℕ, idealPowerMultiple I n (F.obj (op k)) = ⊥) ∧
      ∀ k : ℕ, idealPowerMultiple I n (G.obj (op k)) = ⊥ := by
  obtain ⟨nF, hnF⟩ := hF
  obtain ⟨nG, hnG⟩ := hG
  exact ⟨max nF nG + 1, Nat.succ_pos _,
    of_le hnF ((le_max_left nF nG).trans (Nat.le_succ _)),
    of_le hnG ((le_max_right nF nG).trans (Nat.le_succ _))⟩

end IsSystemPowerAnnihilated

/-- The sections over an affine open of a sheaf annihilated by a power of `I` form an
`I(U)`-power torsion module: one positive power of `I(U)` kills all of them at once. -/
public theorem isIPowerTorsion_sections_of_isPowerAnnihilated {I : X.IdealSheafData}
    {M : X.Modules} (hM : IsPowerAnnihilated I M) (U : X.affineOpens) :
    IsIPowerTorsion Γ(X, U) Γ(M, U) (I.ideal U) := by
  obtain ⟨n, hn, hkill⟩ := hM.exists_pos
  exact fun x ↦ ⟨n, hn, fun r hr ↦
    affine_sections_annihilated_of_idealPowerMultiple_eq_bot hkill U hr x⟩

/-- **Tag 0888 (1).** A morphism `α` of inverse systems of sheaves of modules has *kernel and
cokernel annihilated by a power of `K`* if there is one positive exponent `t` for which `K ^ t`
annihilates both `Ker(α_k)` and `Coker(α_k)`, simultaneously for every index `k`.

Kernel and cokernel are taken levelwise, in the abelian category `X.Modules`. This is the notion
the source names at the end of the remark, once its three conditions have been shown
equivalent. -/
@[stacks 0888 "the notion named by the remark"]
public def IsKernelCokernelAnnihilatedByPower (K : X.IdealSheafData) {F G : ℕᵒᵖ ⥤ X.Modules}
    (α : F ⟶ G) : Prop :=
  ∃ t : ℕ, 0 < t ∧ ∀ k : ℕ,
    idealPowerMultiple K t (kernel (α.app (op k))) = ⊥ ∧
      idealPowerMultiple K t (cokernel (α.app (op k))) = ⊥

/-- **The elementwise form of Tag 0888 (1).** The levelwise kernels and cokernels of `α` are
annihilated by a power of `K` exactly when, for one positive exponent `t`, every element of
`K(U) ^ t` kills every section of every `Ker(α_k)` and of every `Coker(α_k)` over every affine
open `U`. -/
public theorem isKernelCokernelAnnihilatedByPower_iff_affine_sections_annihilated
    (K : X.IdealSheafData) {F G : ℕᵒᵖ ⥤ X.Modules} (α : F ⟶ G) :
    IsKernelCokernelAnnihilatedByPower K α ↔
      ∃ t : ℕ, 0 < t ∧ ∀ k : ℕ,
        (∀ U : X.affineOpens, ∀ r ∈ K.ideal U ^ t,
            ∀ x : Γ(kernel (α.app (op k)), U), r • x = 0) ∧
          ∀ U : X.affineOpens, ∀ r ∈ K.ideal U ^ t,
            ∀ x : Γ(cokernel (α.app (op k)), U), r • x = 0 :=
  exists_congr fun t ↦ and_congr_right fun _ ↦ forall_congr' fun k ↦
    and_congr
      (idealPowerMultiple_eq_bot_iff_affine_sections_annihilated K t (kernel (α.app (op k))))
      (idealPowerMultiple_eq_bot_iff_affine_sections_annihilated K t (cokernel (α.app (op k))))

namespace IsKernelCokernelAnnihilatedByPower

variable {K : X.IdealSheafData} {F G : ℕᵒᵖ ⥤ X.Modules} {α : F ⟶ G}

/-- One positive exponent annihilating every levelwise kernel and cokernel witnesses the
predicate. -/
public theorem of_eq_bot {t : ℕ} (ht : 0 < t)
    (h : ∀ k : ℕ, idealPowerMultiple K t (kernel (α.app (op k))) = ⊥ ∧
      idealPowerMultiple K t (cokernel (α.app (op k))) = ⊥) :
    IsKernelCokernelAnnihilatedByPower K α :=
  ⟨t, ht, h⟩

/-- The kernel half of the condition: one positive power of `K` annihilates every levelwise
kernel of `α`. -/
public theorem exists_kernel_eq_bot (h : IsKernelCokernelAnnihilatedByPower K α) :
    ∃ t : ℕ, 0 < t ∧ ∀ k : ℕ, idealPowerMultiple K t (kernel (α.app (op k))) = ⊥ := by
  obtain ⟨t, ht, h⟩ := h
  exact ⟨t, ht, fun k ↦ (h k).1⟩

/-- The cokernel half of the condition: one positive power of `K` annihilates every levelwise
cokernel of `α`. -/
public theorem exists_cokernel_eq_bot (h : IsKernelCokernelAnnihilatedByPower K α) :
    ∃ t : ℕ, 0 < t ∧ ∀ k : ℕ, idealPowerMultiple K t (cokernel (α.app (op k))) = ⊥ := by
  obtain ⟨t, ht, h⟩ := h
  exact ⟨t, ht, fun k ↦ (h k).2⟩

/-- Annihilation of the levelwise kernels and cokernels by `K ^ t` persists on raising the
exponent, since `K ^ m ≤ K ^ t` for `t ≤ m`. -/
public theorem of_le {t m : ℕ}
    (h : ∀ k : ℕ, idealPowerMultiple K t (kernel (α.app (op k))) = ⊥ ∧
      idealPowerMultiple K t (cokernel (α.app (op k))) = ⊥) (htm : t ≤ m) (k : ℕ) :
    idealPowerMultiple K m (kernel (α.app (op k))) = ⊥ ∧
      idealPowerMultiple K m (cokernel (α.app (op k))) = ⊥ :=
  ⟨idealPowerMultiple_eq_bot_of_le (h k).1 htm, idealPowerMultiple_eq_bot_of_le (h k).2 htm⟩

/-- Positive powers of `K` annihilating the levelwise kernels and the levelwise cokernels
separately combine into one, obtained as the larger of the two exponents. -/
public theorem of_exists_kernel_cokernel
    (hker : ∃ t : ℕ, 0 < t ∧ ∀ k : ℕ, idealPowerMultiple K t (kernel (α.app (op k))) = ⊥)
    (hcok : ∃ t : ℕ, 0 < t ∧ ∀ k : ℕ, idealPowerMultiple K t (cokernel (α.app (op k))) = ⊥) :
    IsKernelCokernelAnnihilatedByPower K α := by
  obtain ⟨t, ht, hk⟩ := hker
  obtain ⟨s, _, hc⟩ := hcok
  exact ⟨max t s, ht.trans_le (le_max_left t s), fun k ↦
    ⟨idealPowerMultiple_eq_bot_of_le (hk k) (le_max_left t s),
      idealPowerMultiple_eq_bot_of_le (hc k) (le_max_right t s)⟩⟩

/-- Each levelwise kernel of `α` is annihilated by a power of `K`. -/
public theorem isPowerAnnihilated_kernel (h : IsKernelCokernelAnnihilatedByPower K α) (k : ℕ) :
    IsPowerAnnihilated K (kernel (α.app (op k))) :=
  ⟨h.choose, (h.choose_spec.2 k).1⟩

/-- Each levelwise cokernel of `α` is annihilated by a power of `K`. -/
public theorem isPowerAnnihilated_cokernel (h : IsKernelCokernelAnnihilatedByPower K α) (k : ℕ) :
    IsPowerAnnihilated K (cokernel (α.app (op k))) :=
  ⟨h.choose, (h.choose_spec.2 k).2⟩

/-- Two morphisms whose levelwise kernels and cokernels are annihilated by powers of `K` are
annihilated by one common positive power, obtained as the larger of the two exponents. This is
the form in which the hypotheses on a pair of comparison maps are used. -/
public theorem exists_common_pos {F' G' : ℕᵒᵖ ⥤ X.Modules} {β : F' ⟶ G'}
    (hα : IsKernelCokernelAnnihilatedByPower K α)
    (hβ : IsKernelCokernelAnnihilatedByPower K β) :
    ∃ t : ℕ, 0 < t ∧
      (∀ k : ℕ, idealPowerMultiple K t (kernel (α.app (op k))) = ⊥ ∧
        idealPowerMultiple K t (cokernel (α.app (op k))) = ⊥) ∧
      ∀ k : ℕ, idealPowerMultiple K t (kernel (β.app (op k))) = ⊥ ∧
        idealPowerMultiple K t (cokernel (β.app (op k))) = ⊥ := by
  obtain ⟨tα, htα, hα⟩ := hα
  obtain ⟨tβ, _, hβ⟩ := hβ
  exact ⟨max tα tβ, htα.trans_le (le_max_left tα tβ),
    of_le hα (le_max_left tα tβ), of_le hβ (le_max_right tα tβ)⟩

end IsKernelCokernelAnnihilatedByPower

end Stacks.Algebraization

end
