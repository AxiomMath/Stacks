module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.Colength.PositiveOrder
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumSequence
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.ClosedUnionExactSequence
public import StacksFrontier.AlgebraicGeometry.SectionsExact.Basic
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.LongExactSequence
public import StacksFrontier.AlgebraicGeometry.Blowup.AffineBlowUpIso
public import StacksFrontier.AlgebraicGeometry.DivisorSum.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.SumKernelMap

/-!
# The residual sections are a proper subobject: the strict inequality of [Stacks, Tag 0AGT]

Let `(A, 𝔪)` be a two-dimensional regular local ring, `b : X ⟶ Spec A` the blowup at the closed
point, `E` the exceptional ideal sheaf, `J` an ideal sheaf on `Spec A`, and write
`b⁻¹J·𝒪_X = E ^ d · Z` with `d` maximal. The source's chain of inequalities is

`length_A(A/J) ≥ length_A Γ(X, 𝒪_X/J·𝒪_X) > length_A Γ(X, E^d/J·𝒪_X) = length_A Γ(X, 𝒪_X/Z)`

and the *strict* middle step is what this file supplies, in the form that makes it strict: the
global sections of `E ^ d / J·𝒪_X` are a **proper** subgroup of those of `𝒪_X / J·𝒪_X`.

## Main results

* `Stacks.SectionsExact.injective_app_of_shortExact` and
  `Stacks.SectionsExact.exact_app_of_shortExact` — left exactness of `Γ(U, -)` on sheaves of
  `𝒪_X`-modules, read on elements.
* `Stacks.SectionsExact.modulesApp_apply` — the two spellings of a morphism of `𝒪_X`-modules
  acting on sections agree.
* `Stacks.Divisors.nonempty_subscheme_of_ne_top` and
  `Stacks.Divisors.nontrivial_sections_subscheme_of_ne_top` — a closed subscheme cut out by a
  proper ideal sheaf is nonempty, so its ring of global functions is nontrivial.
* `Stacks.Divisors.notMem_range_app_sumKernelMap` — **the strict step, in general.** For `D` an
  effective Cartier divisor and `C` arbitrary with `D ≠ ⊤`, the image of `1` in `Γ(X, 𝒪_{C·D})`
  is *not* a section of `𝒪_X(-D)|_C`.
* `Stacks.Blowup.Colength.ne_top_exceptionalIdeal_pow_of_maximal` — maximality of the order
  forces `E ^ d ≠ ⊤`. No hypothesis beyond the ones the source already grants.
* `Stacks.Blowup.Colength.notMem_range_residualSections` — **the strict step in the situation of
  the source.**

## Implementation notes

**The two short exact sequences are not new, and neither is the quotient `E^d/J·𝒪_X`.** An
earlier note in `StacksFrontier/AlgebraicGeometry/Blowup/Colength/PositiveOrder.lean` recorded the
sheaf-level quotient `E ^ d ⧸ (E ^ d · Z)` as the one object nobody had built. It is built:
`Stacks.Divisors.shortExact_sumKernelMap` ([Stacks, Tag 0C4T], in
`StacksFrontier/AlgebraicGeometry/Divisors/EffectiveCartier/SumSequence.lean`) is the sequence
`0 ⟶ 𝒪_X(-D)|_C ⟶ 𝒪_{C·D} ⟶ 𝒪_D ⟶ 0`, whose first term
`i_*i^*(negativeTwist D)` for `i : C.subscheme ⟶ X` *is* `ℐ_D ⧸ (ℐ_C · ℐ_D)`. Its only
hypothesis on `C` is `C * D ≤ D`, which `Scheme.IdealSheafData.mul_le_right` supplies for free;
the effective-Cartier hypothesis falls on `D` alone, and `D = E ^ d` is one by
`Stacks.Divisors.isEffectiveCartierDivisor_pow`. Taking `D = E ^ d` and `C = Z` therefore gives
the source's second sequence outright. The first sequence
`0 ⟶ J·𝒪_X ⟶ 𝒪_X ⟶ 𝒪_X/J·𝒪_X ⟶ 0` is likewise available, in three forms — the general one is
`Stacks.IdealSheafSequence.divisorIdeal_shortExact`.

**What makes the inequality strict.** `Γ(U, -)` is left exact, so the sections of the first term
of a short exact sequence are exactly the kernel of the map to the sections of the third. The
third term here is `𝒪_D = 𝒪_X/E^d`, and the image of `1` in its global sections is nonzero
because `E ^ d ≠ ⊤`: a proper ideal sheaf cuts out a nonempty closed subscheme, whose ring of
global functions is nontrivial by `AlgebraicGeometry.Scheme.component_nontrivial`. So the image
of `1` in `Γ(X, 𝒪_X/J·𝒪_X)` is a section that the residual term misses.

**`E ^ d ≠ ⊤` is not an extra hypothesis.** It follows from the maximality of `d` that the source
already states: were `E` the unit ideal sheaf then every power of it would be, so
`b⁻¹J·𝒪_X ≤ E ^ e` for every `e`, and maximality would bound every natural number by `d`. This
is the same argument as `Stacks.Blowup.Colength.pos_order_of_le_center`, run one step further,
and it needs neither the regular local surface nor `𝔪ⁿ ⊆ J`.

**Spelling.** `1` is never written at the type `Γ(I.closedSubschemeStructureSheaf, ⊤)`, the
sections of `𝒪_X/I` as an `𝒪_X`-module. The elaborator accepts that type and
`Γ(I.subscheme, ⊤)` as equal, but `AlgebraicGeometry.Scheme.Modules` is a `def`, so instance
search does not cross it and `One` cannot be synthesized at the module spelling. Every `1` below
therefore sits at `Γ(I.subscheme, ⊤)`, a `CommRingCat` type, and is handed to the module-level
maps by unification. For the same reason the computation of the image of `1` is a chain of
separately stated `have`s composed with `Eq.trans`, not a `rw`: rewriting leaves the goal's
type at the module spelling, where `one_ne_zero` then has no instance to find, and one of the
rewrites hits a 200,000-heartbeat `whnf` timeout.

The blowup, its structure morphism and its exceptional ideal are written with their
`AlgebraicGeometry.` prefixes throughout, because the enclosing namespace `Stacks.Blowup` carries
a second, independently glued blowup, `Stacks.Blowup.blowUp` in
`StacksFrontier/AlgebraicGeometry/Blowup/ReesSheafData.lean`, together with its own `blowUpToBase`
and `exceptionalIdeal`; inside `Stacks.Blowup.Colength` the bare names resolve to *those*.

## What the strict inequality still waits on

Two things, both outside this file.

* **The surjection `A/J ↠ Γ(X, 𝒪_X/J·𝒪_X)`**, which is what bounds the middle term by
  `length_A(A/J)` and, with it, makes the lengths finite so that a proper subobject has strictly
  smaller length (`Submodule.length_lt`). It needs `H¹(X, J·𝒪_X) = 0` on
  `AlgebraicGeometry.blowUp`, and the available vanishing
  `AlgebraicGeometry.isZero_cohomology_one_comap_ofIdealTop_blowUpSpec` is on
  `Stacks.Blowup.blowUpSpec`. Transporting it along `Stacks.Blowup.affineBlowUpIso` with
  `Stacks.Cohomology.ModuleComparison.hgroupPullbackIso` requires identifying the pullback of an
  ideal sheaf of modules along that isomorphism with the ideal sheaf of the inverse image.
  `Stacks.Divisors.epi_pullbackIdealSheafComapMap` is unconditional, but the matching `Mono` is
  not in the library: `Stacks.Divisors.isIso_pullbackIdealSheafComapMap` assumes an effective
  Cartier divisor whose pullback is defined, and `J·𝒪_X` is not one. The route left open is
  `Stacks.RingedSpace.preservesMonomorphisms_modulePullback_of_isIso_stalkRingMap`, which an
  isomorphism of schemes satisfies — together with a bridge between
  `Stacks.RingedSpace.pullbackFunctor` and `AlgebraicGeometry.Scheme.Modules.pullback`, the two
  spellings of pullback that the two halves use.
* **`Γ(X, E^d/J·𝒪_X) = Γ(X, 𝒪_X/Z)`**, the source's last step: the pullback of the invertible
  `𝒪_X(-dE)` to the finite-support subscheme `Z` is trivial. The ingredients are
  `AlgebraicGeometry.length_globalSections_eq_sum_length_stalk` and
  `AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor`.

## References

* [Stacks Project, Tag 0AGT](https://stacks.math.columbia.edu/tag/0AGT)
* [Stacks Project, Tag 0C4T](https://stacks.math.columbia.edu/tag/0C4T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CohomologyVanishing

universe u

namespace Stacks.SectionsExact

variable (X : Scheme.{u}) (U : X.Opens)
  {S : ShortComplex (SheafOfModules.{u} X.ringCatSheaf)}

/-- **`Γ(U, -)` is left exact**, read on elements: the first map of a short exact sequence of
`𝒪_X`-modules is injective on sections over every open.

No hypothesis on `X`, on `U`, or on the quasi-coherence of the sheaves. -/
public theorem injective_app_of_shortExact (hS : S.ShortExact) :
    Function.Injective (S.f.val.app (op U)) :=
  (AddCommGrpCat.mono_iff_injective _).1
    ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (secF X.ringCatSheaf U)).1 inferInstance S hS).2

/-- **`Γ(U, -)` is left exact**, read on elements: the sections of the first term of a short exact
sequence of `𝒪_X`-modules are exactly the sections of the middle term killed by the map to the
third.

Together with `Stacks.SectionsExact.injective_app_of_shortExact` this says that `Γ(U, ℱ₁)` is the
kernel of `Γ(U, ℱ₂) ⟶ Γ(U, ℱ₃)`. Surjectivity onto `Γ(U, ℱ₃)` is the one part that fails in
general; it is `Stacks.SerreAffinenessCriterion.surjective_app_of_isZero_hgroup_one`. -/
public theorem exact_app_of_shortExact (hS : S.ShortExact) :
    Function.Exact (S.f.val.app (op U)) (S.g.val.app (op U)) :=
  (ShortComplex.ab_exact_iff_function_exact _).1
    ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (secF X.ringCatSheaf U)).1 inferInstance S hS).1

/-- **`Scheme.Modules.Hom.app` and the component of the underlying morphism of sheaves agree on
elements.** `AlgebraicGeometry.Scheme.Modules.Hom.app` is by definition the component of the
underlying morphism pushed along `forget₂ (ModuleCat _) AddCommGrpCat`, which does not change the
function, so this is `rfl`.

It is split off as a lemma about an arbitrary morphism because the kernel checks the identity once
here, on a variable, instead of once per use on a morphism whose source and target are large
unfoldings: inlining it left the proof of
`Stacks.Divisors.notMem_range_app_sumKernelMap` to a kernel timeout. -/
public theorem modulesApp_apply {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (V : X.Opens)
    (x : Γ(M, V)) : f.app V x = f.val.app (op V) x := rfl

end Stacks.SectionsExact

namespace Stacks.Divisors

/-- **A proper ideal sheaf cuts out a nonempty closed subscheme.** The support of `I` is empty
exactly when `I` is the unit ideal sheaf, and the support is the range of the closed
immersion. -/
public theorem nonempty_subscheme_of_ne_top {X : Scheme.{u}} (I : X.IdealSheafData) (h : I ≠ ⊤) :
    Nonempty I.subscheme := by
  have hs : I.support ≠ ⊥ := fun hb => h ((Scheme.IdealSheafData.support_eq_bot_iff I).mp hb)
  obtain ⟨x, hx⟩ : ((I.support : Set X)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    exact fun he => hs (SetLike.ext' he)
  rw [← Scheme.IdealSheafData.range_subschemeι I] at hx
  exact ⟨hx.choose⟩

/-- **The ring of global functions on the closed subscheme cut out by a proper ideal sheaf is
nontrivial.** The subscheme is nonempty, and a nonempty scheme has nontrivial global
functions. -/
public theorem nontrivial_sections_subscheme_of_ne_top {X : Scheme.{u}} (I : X.IdealSheafData)
    (h : I ≠ ⊤) :
    Nontrivial Γ(I.subscheme, ⊤) := by
  have hne : Nonempty I.subscheme := nonempty_subscheme_of_ne_top I h
  have : Nonempty ↥(⊤ : I.subscheme.Opens) :=
    ⟨⟨Classical.arbitrary I.subscheme, trivial⟩⟩
  infer_instance

/-- **The sequence of [Stacks, Tag 0C4T] at the `SheafOfModules` spelling.**
`Stacks.Divisors.shortExact_sumKernelMap` states it in `X.Modules`; the left exactness of global
sections is stated for `SheafOfModules X.ringCatSheaf`. The two are the same category —
`AlgebraicGeometry.Scheme.Modules` is a `def` for the second — but they carry separately declared
instances, so an application that crosses between them is paid for by the elaborator rather than
by instance search. This lemma is split off so that the crossing is paid once, in a declaration
of its own: inlined into the proof below it exhausted the heartbeat budget. -/
public theorem shortExact_sumKernelMap_sheafOfModules {X : Scheme.{u}} (D C : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsub : C * D ≤ D) :
    (ShortComplex.mk (C := SheafOfModules.{u} X.ringCatSheaf) (sumKernelMap D C hD)
      (Scheme.IdealSheafData.closedSubschemeRestriction hsub)
      (sumKernelMap_comp_closedSubschemeRestriction D C hD hsub)).ShortExact :=
  shortExact_sumKernelMap D C hD hsub

/-- **The strict step of [Stacks, Tag 0AGT], in general.** Let `D` be an effective Cartier
divisor on a scheme `X`, let `C` be an arbitrary quasi-coherent ideal sheaf with `C * D ≤ D`, and
suppose `D` is proper. Then the image of `1` in `Γ(X, 𝒪_{C·D})` is not a section of
`𝒪_X(-D)|_C`, so the global sections of `𝒪_X(-D)|_C` are a *proper* subgroup of those of
`𝒪_{C·D}`.

This is what makes the first inequality of the source's clause (3) strict. The sequence is
[Stacks, Tag 0C4T] with its kernel inclusion named,
`Stacks.Divisors.shortExact_sumKernelMap`; left exactness of global sections identifies the
sections of its first term with the kernel of the restriction `𝒪_{C·D} ⟶ 𝒪_D`, and `1` is outside
that kernel because `D` is proper, so `𝒪_D` has nonzero global sections. -/
public theorem notMem_range_app_sumKernelMap {X : Scheme.{u}} (D C : X.IdealSheafData)
    (hD : IsEffectiveCartierDivisor D) (hsub : C * D ≤ D) (hDtop : D ≠ ⊤) :
    (Scheme.IdealSheafData.ambientToClosedSubscheme (C * D)).app ⊤ (1 : Γ(X, ⊤)) ∉
      Set.range ((sumKernelMap D C hD).val.app (op (⊤ : X.Opens))) := by
  intro hmem
  have hone : (1 : Γ(D.subscheme, ⊤)) ≠ 0 := by
    have := nontrivial_sections_subscheme_of_ne_top D hDtop
    exact one_ne_zero
  have hex := Stacks.SectionsExact.exact_app_of_shortExact X ⊤
    (shortExact_sumKernelMap_sheafOfModules D C hD hsub)
  have hzero := (hex ((Scheme.IdealSheafData.ambientToClosedSubscheme (C * D)).app ⊤
    (1 : Γ(X, ⊤)))).2 hmem
  have hbridge := Stacks.SectionsExact.modulesApp_apply
    (Scheme.IdealSheafData.closedSubschemeRestriction hsub) ⊤
    ((Scheme.IdealSheafData.ambientToClosedSubscheme (C * D)).app ⊤ (1 : Γ(X, ⊤)))
  have a : (Scheme.IdealSheafData.ambientToClosedSubscheme (C * D)).app ⊤ (1 : Γ(X, ⊤)) =
      (C * D).subschemeι.app ⊤ 1 :=
    Scheme.IdealSheafData.ambientToClosedSubscheme_app_apply (C * D) ⊤ 1
  have b : (C * D).subschemeι.app ⊤ (1 : Γ(X, ⊤)) = 1 := map_one _
  have e1 : (Scheme.IdealSheafData.closedSubschemeRestriction hsub).app ⊤
      ((Scheme.IdealSheafData.ambientToClosedSubscheme (C * D)).app ⊤ (1 : Γ(X, ⊤))) =
      (Scheme.IdealSheafData.inclusion hsub).appTop.hom
        ((Scheme.IdealSheafData.ambientToClosedSubscheme (C * D)).app ⊤ (1 : Γ(X, ⊤))) :=
    Scheme.IdealSheafData.closedSubschemeRestriction_app_top hsub _
  have e2 : (Scheme.IdealSheafData.inclusion hsub).appTop.hom
        ((Scheme.IdealSheafData.ambientToClosedSubscheme (C * D)).app ⊤ (1 : Γ(X, ⊤))) =
      (Scheme.IdealSheafData.inclusion hsub).appTop.hom 1 :=
    congrArg _ (a.trans b)
  have e3 : (Scheme.IdealSheafData.inclusion hsub).appTop.hom
      (1 : Γ((C * D).subscheme, ⊤)) = 1 := map_one _
  exact hone ((e2.trans e3).symm.trans (e1.symm.trans (hbridge.trans hzero)))

end Stacks.Divisors

namespace Stacks.Blowup.Colength

/-- **The exceptional ideal sheaf is proper, as soon as the order of a pulled-back ideal along it
is maximal.** If the exceptional ideal were the unit ideal sheaf then so would be every power of
it, and the inverse image would be contained in all of them, so maximality would bound every
natural number.

No hypothesis beyond the maximality the source already states: neither the regular local surface
nor the containment `𝔪ⁿ ⊆ J` is used. -/
public theorem ne_top_exceptionalIdeal_of_maximal {X : Scheme.{u}} (M J : X.IdealSheafData)
    (d : ℕ)
    (hmax : ∀ e : ℕ, J.comap (AlgebraicGeometry.blowUpToBase M) ≤
      AlgebraicGeometry.exceptionalIdeal M ^ e → e ≤ d) :
    AlgebraicGeometry.exceptionalIdeal M ≠ ⊤ := by
  intro htop
  have hone : (1 : (AlgebraicGeometry.blowUp M).IdealSheafData) = ⊤ := by simp
  have hpow : AlgebraicGeometry.exceptionalIdeal M ^ (d + 1) = ⊤ := by
    rw [htop, ← hone, one_pow]
  have hle : J.comap (AlgebraicGeometry.blowUpToBase M) ≤
      AlgebraicGeometry.exceptionalIdeal M ^ (d + 1) := by
    rw [hpow]
    exact le_top
  have := hmax (d + 1) hle
  omega

/-- **The `d`-th power of the exceptional ideal sheaf is proper, for `d` positive and maximal.**
A positive power of the exceptional ideal is contained in it, so it can only be the unit ideal
sheaf if the exceptional ideal is, which maximality forbids. -/
public theorem ne_top_exceptionalIdeal_pow_of_maximal {X : Scheme.{u}} (M J : X.IdealSheafData)
    (d : ℕ) (hd : 0 < d)
    (hmax : ∀ e : ℕ, J.comap (AlgebraicGeometry.blowUpToBase M) ≤
      AlgebraicGeometry.exceptionalIdeal M ^ e → e ≤ d) :
    AlgebraicGeometry.exceptionalIdeal M ^ d ≠ ⊤ := by
  intro htop
  obtain ⟨k, rfl⟩ : ∃ k, d = k + 1 := ⟨d - 1, by omega⟩
  have hle : AlgebraicGeometry.exceptionalIdeal M ^ (k + 1) ≤
      AlgebraicGeometry.exceptionalIdeal M := by
    rw [pow_succ]
    exact Scheme.IdealSheafData.mul_le_right _ _
  rw [htop] at hle
  exact ne_top_exceptionalIdeal_of_maximal M J (k + 1) hmax (top_le_iff.mp hle)

/-- **The strict step of [Stacks, Tag 0AGT] in the situation of the source.** Let `M` be an ideal
sheaf on a scheme `X`, let `b : X' ⟶ X` be the blowup in `M` with exceptional ideal `E`, let `J`
be an ideal sheaf on `X` and suppose `b⁻¹J·𝒪_{X'} = E ^ d · Z` with `d` positive and maximal.
Then the image of `1` in `Γ(X', 𝒪_{X'}/b⁻¹J·𝒪_{X'})` is not a global section of
`E ^ d / b⁻¹J·𝒪_{X'}`.

So the global sections of `E ^ d / b⁻¹J·𝒪_{X'}` are a *proper* subgroup of those of
`𝒪_{X'}/b⁻¹J·𝒪_{X'}`, which is the content that makes the first inequality of the source's
clause (3) strict. The remaining inputs to that inequality are recorded in the module
documentation. -/
public theorem notMem_range_residualSections {X : Scheme.{u}} (M J : X.IdealSheafData)
    (d : ℕ) (hd : 0 < d) (Z : (AlgebraicGeometry.blowUp M).IdealSheafData)
    (hmax : ∀ e : ℕ, J.comap (AlgebraicGeometry.blowUpToBase M) ≤
      AlgebraicGeometry.exceptionalIdeal M ^ e → e ≤ d) :
    (Scheme.IdealSheafData.ambientToClosedSubscheme
          (Z * AlgebraicGeometry.exceptionalIdeal M ^ d)).app ⊤
        (1 : Γ(AlgebraicGeometry.blowUp M, ⊤)) ∉
      Set.range ((Stacks.Divisors.sumKernelMap (AlgebraicGeometry.exceptionalIdeal M ^ d) Z
        (Stacks.Divisors.isEffectiveCartierDivisor_pow
          (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal M) d)).val.app
        (op (⊤ : (AlgebraicGeometry.blowUp M).Opens))) :=
  Stacks.Divisors.notMem_range_app_sumKernelMap (AlgebraicGeometry.exceptionalIdeal M ^ d) Z
    (Stacks.Divisors.isEffectiveCartierDivisor_pow
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal M) d)
    (Scheme.IdealSheafData.mul_le_right Z (AlgebraicGeometry.exceptionalIdeal M ^ d))
    (ne_top_exceptionalIdeal_pow_of_maximal M J d hd hmax)

end Stacks.Blowup.Colength

end
