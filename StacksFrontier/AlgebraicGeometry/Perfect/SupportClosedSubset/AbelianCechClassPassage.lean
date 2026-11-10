module

public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.AbelianCechCokernelPassage
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.FractionClassSpellings
public import
  StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.SupportedEndoForgetDegreewise

/-!
# The localized Leibniz rule for the class map of Stacks 0G7Q, at any number of equations

Let `X` be a scheme, let `f₁, …, f_c ∈ Γ(X, 𝒪_X)` be global equations — **any number of them,
zero included** — let `T` be a closed subset containing their common zero locus and let `ℱ`, `𝒢`
be quasi-coherent `𝒪_X`-modules.  The class map `c_{f₁, …, f_c} : ℱ ⟶ i_*ℋ ᶜ_T(ℱ)` of
[Stacks, Tag 0G7Q] is `𝒪_X`-linear in the coefficient module, and its naturality in an
`𝒪_X`-linear morphism is [Stacks, Tag 0G7T]
(`Stacks.Gysin.classMapToSupport_naturality`).

**That is not the naturality [Stacks, Tag 0G85] and [Stacks, Tag 0G87] need.**  The morphism they
feed it is a relative de Rham differential `d : Ω^p_{X/S} ⟶ Ω^{p+1}_{X/S}`, which is only
`π⁻¹𝒪_S`-linear and is a morphism of `X.Modules` for no `X`; and in an *arbitrary* additive
morphism the class map is not natural, because the class of a fraction is not determined by its
numerator.  What repairs it is the **localized Leibniz rule**: the morphism need only commute with
dividing by the product of the equations, after precomposition with a factor.  That is the
hypothesis `h` of the main result below, and on the equation wedges of the Gysin formula it holds
— `Stacks.Gysin.ambientDeRhamShift_smul_gysinWedgeOn_comm`.

`Stacks.Gysin.supportedFractionSource_comm_of_smul` is this statement for
`Stacks.Perfect.SupportedFraction.supportedFractionSource`, and so only for `c = d + 1`: that map
factors through the cokernel of `Stacks.Perfect.SupportedFraction.lastDif`, the differential of
the extended alternating Čech complex into its *top* degree, and an empty family of equations
gives a complex with only degree `0` and no such differential.  This file proves it for **every**
`c` about `Stacks.Perfect.FractionClass.classMapToSupport`, which is the same map of
[Stacks, Tag 0G7Q] built without a top differential.

## What makes it general, and why `c = 0` is not a reindex of `c = d + 1`

The derived square of step (ii) of [Stacks, Tag 0G85],
`Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare_conj`, is already stated for an
arbitrary number of equations: nothing in it mentions a top degree.  What was restricted to
`c = d + 1` is the *passage* from that square down to the level the class map lives at, which
`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/AbelianCechCokernelPassage.lean`
performs through the **Čech cokernel** — an object that does not exist at `c = 0`.

This file performs the same passage through the **degree-`p` cohomology sheaf of the Čech
complex**, which exists at every `c` and in every degree.  The class map is then the class of the
cycle `Stacks.Perfect.FractionClass.fracCycle`, and the left-hand vertical arrow of the square is
`cechHomologyAb`, the action of `Hᵖ` of the abelian Čech chain map
`Stacks.Perfect.AbelianFraction.cplxAb` — not the abelian functoriality
`Stacks.Perfect.AbelianFraction.cokernelLastDifAb` of a cokernel.  At `c = d + 1` the two agree,
both being read off the same derived square; at `c = 0` only the first is defined.

So the content peculiar to `c = 0` is not in this file at all: it is that the *numerator*
hypothesis degenerates.  An empty product of equations is `1`, so the only local section inverting
it is `1`, and the localized Leibniz rule says exactly that `u ≫ ψ = w` — plain additivity, with
no localization and no fraction.  That is `fracTermTop_abelian_zero` below, and it is why the
hypothesis is discharged uniformly.

## Main definitions

* `cechHomologyAb`: **the action of the degree-`p` cohomology sheaf of the extended alternating
  Čech complex on a morphism of the underlying abelian sheaves of the coefficient modules.**  It
  is `Hᵖ` of `Stacks.Perfect.AbelianCechDerivedSquare.cplxAbExtend`, read through the
  identifications of the cohomology of the `ℕ`-graded complex with that of its `ℤ`-graded
  extension and through `Stacks.Perfect.AbelianCechCokernelPassage.forgetHomologyIso`.
* `fracExtendCycles` and `classExtendHomology`: the cycle of the fraction and its class, read on
  the `ℤ`-graded extension of the Čech complex.
* `cechHomologyToDerived` and `cechHomologyToForgetDerived`: the degree-`p` cohomology sheaf as
  the degree-`p` cohomology of the extended complex in the derived category, and the same after
  forgetting the module structure — the analogues of
  `Stacks.Perfect.AbelianCechCokernelPassage.cechCokernelToForgetDerived`, off the cokernel.

## Main results

* `cplxAbExtend_f_eq_termAb`: the degree-`p` component of the extended abelian Čech chain map is
  the induced map on the degree-`p` Čech term.  This is the only step at which the formula for
  the abelian chain map is used; everything else is formal.
* `fracExtendCycles_comp_cyclesMap_cplxAbExtend` and
  `classExtendHomology_comp_homologyMap_cplxAbExtend`: **the abelian Čech chain map carries the
  cycle of the fraction, and then its class, as soon as it carries the numerator** — the
  cycle-level and cohomology-level halves of the passage, for any number of equations.
* `classMap_comp_cechHomologyAb`: the class map of [Stacks, Tag 0G7Q] is carried by
  `cechHomologyAb` as soon as its numerator is.
* `cechHomologyAb_eq_homologyFunctor_derivedCechAb`: **the action `cechHomologyAb` is the
  degree-`p` cohomology of the abelian Čech derived map** — the left-hand vertical arrow of the
  passage, the analogue of
  `Stacks.Perfect.AbelianCechCokernelPassage.cokernelLastDifAb_eq_homologyFunctor_derivedCechAb`.
* `cechToSupport_comp_forgetSupportPushAbMap_anyFamily` and
  `homologyFunctor_map_forget_cechToSupport_anyFamily`: the derived square and the naturality of
  the forgetful comparison, restated at an arbitrary family of equations.
* `map_cechHomologyToSupport_abelian_square`: **the square of step (ii) of [Stacks, Tag 0G85]
  between the degree-`p` Čech cohomology sheaf and `i_*ℋ ᵖ_T`, for any number of equations and in
  every degree.**  This is
  `Stacks.Perfect.AbelianCechCokernelPassage.map_cokernelLastDifToSupport_abelian_square` with the
  cokernel replaced by the cohomology sheaf and both of its restrictions removed.
* `classMapToSupport_comm_of_num`: **the class map of [Stacks, Tag 0G7Q], read on the coefficient
  module and in `i_*ℋ ᶜ_T(ℱ)`, is natural along a morphism of the underlying abelian sheaves
  whose numerator is carried**, for any number of equations.
* `fracTermTop_abelian_zero`, `fracTermTop_abelian_succ` and `fracTermTop_abelian_of_smul`: the
  numerator identity at an empty family, at a nonempty one, and at an arbitrary one.  The case
  split on the number of equations happens in the last of these and nowhere else.
* `classMapToSupport_comm_of_smul`: **the localized Leibniz rule for the class map of
  [Stacks, Tag 0G7Q], at any number of equations** — the result this file exists for.

## Implementation notes

**Carried hypotheses.**  A family of global equations of arbitrary length, a closed subset
containing their common zero locus, and quasi-coherence of both coefficient modules
(`[F.IsQuasicoherent]`, `[G.IsQuasicoherent]`), which is where [Stacks, Tag 0G7M] enters — exactly
the hypotheses of `Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare`.  Nothing is
assumed of the additive morphism `ψ` beyond the localized identity, and in particular no
`𝒪_X`-linearity: the whole point of the statement is that there is none to be had.

**Why the two general-`m` re-statements.**
`Stacks.Perfect.AbelianCechCokernelPassage.cechToSupport_comp_forgetSupportPushAbMap` and
`Stacks.Perfect.AbelianCechCokernelPassage.homologyFunctor_map_forget_cechToSupport` are stated
for `f : Fin (n + 1) → Γ(X, 𝒪_X)` because the section they sit in is about the top-degree
cokernel, but neither proof uses the nonemptiness: the first is the derived square, which is
general in the family, and the second is the naturality of
`Stacks.Perfect.AbelianCechCokernelPassage.forgetDerivedHomology`.  They are restated here at an
arbitrary family rather than generalised in place, so that no existing statement changes.

**Why the degree-`p` component of the abelian chain map is the only formula touched.**  As in the
cokernel passage, `cplxAbExtend_f_eq_termAb` is the single point at which the
abelian Čech chain map `Stacks.Perfect.AbelianFraction.cplxAb` is opened up; everything else below
is formal.  The degree-generic version is *shorter* than the top-degree one, the conversion
`Stacks.Perfect.AbelianCechCokernelPassage.termAb_succ` of the top term into a product of Čech
terms being unnecessary.

**Why the leaf names `cplxAbExtend_f_eq_termAb` and the three `_anyFamily` statements differ from
the top-degree originals, and why each binds its family itself.**  Each is a strictly more
general statement than an existing one which keeps its own name and its own consumers; giving two
coexisting declarations one leaf name would be a duplicate, which this repository does not allow.
So the generalisations are named apart rather than shadowing.

Distinct names are not by themselves enough.  A duplicate-name sweep compares *printed
statements*, and the only difference between each `_anyFamily` statement and its original is the
family — `Fin m` for an arbitrary `m` against the original's `Fin (n + 1)`.  Inherit that binder
from a section `variable` and it does not appear in either printed statement, so three strictly
more general restatements were reported as same-statement twins of their originals.  Each
therefore binds `{m : ℕ} (e : Fin m → Γ(X, 𝒪_X))` in its own signature.  Only the binder's
position moved; no proposition, explicit argument or conclusion changed, and no caller can
observe the difference.

**No `@[stacks ...]` attribute is attached to any declaration here**, and nothing here proves
[Stacks, Tag 0G85] or [Stacks, Tag 0G87].  What it supplies is the one input those two were
missing at an arbitrary number of equations; the tags themselves stay where they are.

## References

* [Stacks Project, Tag 0G85](https://stacks.math.columbia.edu/tag/0G85)
* [Stacks Project, Tag 0G87](https://stacks.math.columbia.edu/tag/0G87)
* [Stacks Project, Tag 0G7Q](https://stacks.math.columbia.edu/tag/0G7Q)
* [Stacks Project, Tag 0G7T](https://stacks.math.columbia.edu/tag/0G7T)
* [Stacks Project, Tag 0G7M](https://stacks.math.columbia.edu/tag/0G7M)
* [Stacks Project, Tag 0G7L](https://stacks.math.columbia.edu/tag/0G7L)
* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Perfect.AbelianCechCokernelPassage
open Stacks.Perfect.AbelianCechDerivedSquare (cplxAbExtend derivedCechAb)
open Stacks.Perfect.AbelianFraction (abelianSheaf abHom cplxAb termAb sectionsHom)
open Stacks.Perfect.CechDerivedSupport (equationsClosedSet)
open Stacks.Perfect.ExtendedAlternatingCech
open Stacks.Perfect.FractionClass
open Stacks.Perfect.SupportedEndoForgetDegreewise
  (supportCohomologySheafAbelianMap_eq_supportCohomologyForgetAbMap)
open Stacks.Perfect.SupportedFraction
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.AbelianCechClassPassage

attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}}

/-! ### Formal rearrangements

Both are stated at a variable category and applied with `exact`.  The reason is the one the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/AbelianCechCokernelPassage.lean`
record for its own `assoc_formal`, in a sharper form here: the degree-`c` term of the Čech
complex has two spellings, `(cplx f F).X c` and
`Stacks.Perfect.ExtendedAlternatingCech.term f F c`, which are definitionally but not
syntactically equal.  A goal in which both occur is not type-correct at `implicit` transparency,
and there `rw` and `reassoc_of%` report that they cannot find their pattern.  `exact` elaborates
at default transparency and is unaffected. -/

/-- Appending a common factor to both sides of a three-term identity. -/
private lemma chase_append {C₀ : Type*} [Category* C₀] {o₀ o₁ o₁' o₂ o₃ o₄ : C₀}
    (a : o₀ ⟶ o₁) (b : o₁ ⟶ o₂) (t : o₂ ⟶ o₃)
    (a' : o₀ ⟶ o₁') (b' : o₁' ⟶ o₃) (y : o₃ ⟶ o₄)
    (h : a ≫ b ≫ t = a' ≫ b') :
    a ≫ b ≫ t ≫ y = a' ≫ b' ≫ y := by
  rw [← Category.assoc b t y, ← Category.assoc a (b ≫ t) y, h, Category.assoc]

/-- Cancelling two carried identifications off the right of an identity, when each composes with
its partner to the identity. -/
private lemma chase_cancel {C₀ : Type*} [Category* C₀]
    {x₀ x₁ x₁' x₂ x₃ x₄ x₅ x₆ x₇ : C₀}
    (a : x₀ ⟶ x₁) (k : x₁ ⟶ x₂) (p : x₂ ⟶ x₃) (q : x₃ ⟶ x₄) (hh : x₄ ⟶ x₅)
    (q' : x₅ ⟶ x₆) (p' : x₆ ⟶ x₇)
    (b : x₀ ⟶ x₁') (k' : x₁' ⟶ x₇) (pinv : x₇ ⟶ x₆) (qinv : x₆ ⟶ x₅)
    (hq : qinv ≫ q' = 𝟙 x₆) (hp : pinv ≫ p' = 𝟙 x₇)
    (h : a ≫ k ≫ p ≫ q ≫ hh = b ≫ k' ≫ pinv ≫ qinv) :
    a ≫ k ≫ p ≫ q ≫ hh ≫ q' ≫ p' = b ≫ k' := by
  have h2 : (a ≫ k ≫ p ≫ q ≫ hh) ≫ q' ≫ p' =
      (b ≫ k' ≫ pinv ≫ qinv) ≫ q' ≫ p' := by rw [h]
  simp only [Category.assoc] at h2
  rw [h2, ← Category.assoc qinv q' p', hq, Category.id_comp, hp, Category.comp_id]

/-! ### The abelian Čech chain map in an arbitrary degree -/

section Chain

variable {c : ℕ} (f : Fin c → Γ(X, ⊤)) {F G : X.Modules}
  (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)

/-- **The degree-`p` component of the extended abelian Čech chain map is the induced map on the
degree-`p` Čech term**, read through the canonical identifications of the degree-`p` terms of the
two extensions with the degree-`p` terms of the `ℕ`-graded complexes.

This is
`Stacks.Perfect.AbelianCechCokernelPassage.map_extendXIso_inv_comp_cplxAbExtend_f` with the top
degree replaced by an arbitrary one, and it is the only place below where the formula for the
abelian Čech chain map is used.  The leaf name differs from that one deliberately: both statements
live in the library, so a shared leaf name would be a duplicate. -/
lemma cplxAbExtend_f_eq_termAb (p : ℕ) :
    (abelianSheaf X).map ((cplx f F).extendXIso ComplexShape.embeddingUpNat
          (embeddingUpNat_f p)).inv ≫
        (cplxAbExtend f ψ).f (p : ℤ) =
      termAb f ψ p ≫
        (abelianSheaf X).map ((cplx f G).extendXIso ComplexShape.embeddingUpNat
          (embeddingUpNat_f p)).inv := by
  have hsq : (HomologicalComplex.mapHomologicalComplexExtendIso (abelianSheaf X) (cplx f F)
          ComplexShape.embeddingUpNat).hom ≫ cplxAbExtend f ψ =
      HomologicalComplex.extendMap (cplxAb f ψ) ComplexShape.embeddingUpNat ≫
        (HomologicalComplex.mapHomologicalComplexExtendIso (abelianSheaf X) (cplx f G)
          ComplexShape.embeddingUpNat).hom := by
    rw [cplxAbExtend, Iso.hom_inv_id_assoc]
  have hsqf := congrArg (fun α => HomologicalComplex.Hom.f α (p : ℤ)) hsq
  have hRHS := HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f (abelianSheaf X)
    (cplx f G) (cplxAb f ψ) ComplexShape.embeddingUpNat (embeddingUpNat_f p)
  rw [HomologicalComplex.comp_f] at hRHS
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    HomologicalComplex.mapHomologicalComplexExtendIso_hom_f _ _ _ (embeddingUpNat_f p),
    hRHS] at hsqf
  refine (cancel_epi ((((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (cplx f F)).extendXIso ComplexShape.embeddingUpNat (embeddingUpNat_f p)).hom).mp ?_
  rw [← Category.assoc, hsqf, Stacks.Perfect.AbelianFraction.cplxAb_f]
  rfl

/-- **The abelian Čech derived map written through the comparison of the two localizations, at an
arbitrary family of equations.**

This is `Stacks.Perfect.AbelianCechCokernelPassage.derivedCechAb_eq`, whose proof is `rfl` and
uses nothing about the family, restated off the `f : Fin (n + 1) → Γ(X, 𝒪_X)` of the section it
sits in.  It is restated rather than generalised in place so that no existing statement changes.

**The family is bound in the signature and not inherited from the section**, so that `Fin m`
appears in the text of the statement.  That is where the two differ — the original is pinned to a
nonempty family — and a duplicate-name sweep compares printed statements, so a binder left in a
section `variable` makes a strictly more general restatement look like a copy of its original. -/
lemma derivedCechAb_eq_anyFamily {m : ℕ} (e : Fin m → Γ(X, ⊤))
    (χ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    derivedCechAb e χ =
      (forgetQIso ((cplx e F).extend ComplexShape.embeddingUpNat)).hom ≫
        DerivedCategory.Q.map (cplxAbExtend e χ) ≫
        (forgetQIso ((cplx e G).extend ComplexShape.embeddingUpNat)).inv := rfl

end Chain

/-! ### The action of the degree-`p` Čech cohomology sheaf on an additive morphism -/

section Action

variable {c : ℕ} (f : Fin c → Γ(X, ⊤)) {F G : X.Modules}
  (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)

/-- **The action of the degree-`p` cohomology sheaf of the extended alternating Čech complex on a
morphism of the underlying abelian sheaves of the coefficient modules** — not required to be
`𝒪_X`-linear.

It is `Hᵖ` of the extended abelian Čech chain map
`Stacks.Perfect.AbelianCechDerivedSquare.cplxAbExtend`, conjugated by
`HomologicalComplex.extendHomologyIso` — the identification of the cohomology of the `ℕ`-graded
complex with that of its `ℤ`-graded extension — and by
`Stacks.Perfect.AbelianCechCokernelPassage.forgetHomologyIso`, which moves the forgetful functor
past the cohomology.

This is the left-hand vertical arrow of the square of step (ii) of [Stacks, Tag 0G85] in the
spelling of this file.  In the top degree of a nonempty family it is the abelian functoriality
`Stacks.Perfect.AbelianFraction.cokernelLastDifAb` of the Čech cokernel read across
`Stacks.Perfect.SupportedFraction.cokernelLastDifIsoHomology`; for an empty family there is no
cokernel and only this reading survives. -/
def cechHomologyAb (p : ℕ) :
    (abelianSheaf X).obj ((cplx f F).homology p) ⟶
      (abelianSheaf X).obj ((cplx f G).homology p) :=
  (abelianSheaf X).map ((cplx f F).extendHomologyIso ComplexShape.embeddingUpNat
      (embeddingUpNat_f p)).inv ≫
    (forgetHomologyIso ((cplx f F).extend ComplexShape.embeddingUpNat) (p : ℤ)).inv ≫
    HomologicalComplex.homologyMap (cplxAbExtend f ψ) (p : ℤ) ≫
    (forgetHomologyIso ((cplx f G).extend ComplexShape.embeddingUpNat) (p : ℤ)).hom ≫
    (abelianSheaf X).map ((cplx f G).extendHomologyIso ComplexShape.embeddingUpNat
      (embeddingUpNat_f p)).hom

/-- `cechHomologyAb` with the two identifications of the target moved to the other side: this is
the form in which it meets the derived square. -/
lemma cechHomologyAb_comp (p : ℕ) :
    cechHomologyAb f ψ p ≫
        (abelianSheaf X).map ((cplx f G).extendHomologyIso ComplexShape.embeddingUpNat
            (embeddingUpNat_f p)).inv ≫
          (forgetHomologyIso ((cplx f G).extend ComplexShape.embeddingUpNat) (p : ℤ)).inv =
      (abelianSheaf X).map ((cplx f F).extendHomologyIso ComplexShape.embeddingUpNat
          (embeddingUpNat_f p)).inv ≫
        (forgetHomologyIso ((cplx f F).extend ComplexShape.embeddingUpNat) (p : ℤ)).inv ≫
        HomologicalComplex.homologyMap (cplxAbExtend f ψ) (p : ℤ) := by
  rw [cechHomologyAb]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id, Category.comp_id]

/-- The action of the degree-`p` cohomology sheaf on the identity morphism is the identity. -/
lemma cechHomologyAb_id (p : ℕ) :
    cechHomologyAb f (Scheme.Modules.Hom.mapPresheaf (𝟙 F)) p = 𝟙 _ := by
  have hz : cplxAbExtend f (Scheme.Modules.Hom.mapPresheaf (𝟙 F)) = 𝟙 _ := by
    rw [cplxAbExtend, Stacks.Perfect.AbelianFraction.cplxAb_id,
      HomologicalComplex.extendMap_id, Category.id_comp, Iso.inv_hom_id]
  rw [cechHomologyAb, hz, HomologicalComplex.homologyMap_id, Category.id_comp,
    Iso.inv_hom_id_assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id]

end Action

/-! ### The class of the fraction on the extended complex -/

section Class

variable {c : ℕ} (f : Fin c → Γ(X, ⊤)) {E F G : X.Modules}
  (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
  (u : Scheme.Modules.presheaf E ⟶ Scheme.Modules.presheaf F)
  (w : Scheme.Modules.presheaf E ⟶ Scheme.Modules.presheaf G)

/-- **The fraction `s / (f₁ ⋯ f_c)` as a cycle in degree `c` of the `ℤ`-graded extension of the
alternating Čech complex.**  This is `Stacks.Perfect.FractionClass.fracCycle` read across
`HomologicalComplex.extendCyclesIso`; it exists at every `c`, the differential out of degree `c`
vanishing by `Stacks.Perfect.FractionClass.d_top_eq_zero`. -/
def fracExtendCycles (F : X.Modules) :
    F ⟶ ((cplx f F).extend ComplexShape.embeddingUpNat).cycles (c : ℤ) :=
  fracCycle f F ≫
    ((cplx f F).extendCyclesIso ComplexShape.embeddingUpNat (embeddingUpNat_f c)).inv

/-- The inclusion of the cycles carries the extended cycle of the fraction to the fraction. -/
lemma fracExtendCycles_comp_iCycles (F : X.Modules) :
    fracExtendCycles f F ≫
        ((cplx f F).extend ComplexShape.embeddingUpNat).iCycles (c : ℤ) =
      fracTermTop f F ≫
        ((cplx f F).extendXIso ComplexShape.embeddingUpNat (embeddingUpNat_f c)).inv := by
  rw [fracExtendCycles, Category.assoc, HomologicalComplex.extendCyclesIso_inv_iCycles,
    ← Category.assoc, fracCycle_comp_iCycles]

/-- **The fraction class of [Stacks, Tag 0G7Q] read in degree `c` of the `ℤ`-graded extension of
the alternating Čech complex.** -/
def classExtendHomology (F : X.Modules) :
    F ⟶ ((cplx f F).extend ComplexShape.embeddingUpNat).homology (c : ℤ) :=
  classMap f F ≫
    ((cplx f F).extendHomologyIso ComplexShape.embeddingUpNat (embeddingUpNat_f c)).inv

/-- The extended fraction class is the class of the extended cycle of the fraction. -/
lemma classExtendHomology_eq (F : X.Modules) :
    classExtendHomology f F =
      fracExtendCycles f F ≫
        ((cplx f F).extend ComplexShape.embeddingUpNat).homologyπ (c : ℤ) := by
  rw [classExtendHomology, classMap, fracExtendCycles]
  simp only [Category.assoc]
  rw [HomologicalComplex.homologyπ_extendHomologyIso_inv]

/-- **The abelian Čech chain map carries the extended cycle of the fraction to the extended cycle
of the fraction, as soon as it carries the numerator.**  Both sides are checked after composing
with the inclusion of the cycles, which is a monomorphism; what is left is the hypothesis and
`cplxAbExtend_f_eq_termAb`. -/
lemma fracExtendCycles_comp_cyclesMap_cplxAbExtend
    (hnum : abHom u ≫ (abelianSheaf X).map (fracTermTop f F) ≫ termAb f ψ c =
      abHom w ≫ (abelianSheaf X).map (fracTermTop f G)) :
    abHom u ≫ (abelianSheaf X).map (fracExtendCycles f F) ≫
        (forgetCyclesIso ((cplx f F).extend ComplexShape.embeddingUpNat) (c : ℤ)).inv ≫
        HomologicalComplex.cyclesMap (cplxAbExtend f ψ) (c : ℤ) =
      abHom w ≫ (abelianSheaf X).map (fracExtendCycles f G) ≫
        (forgetCyclesIso ((cplx f G).extend ComplexShape.embeddingUpNat) (c : ℤ)).inv := by
  refine (cancel_mono ((((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((cplx f G).extend ComplexShape.embeddingUpNat)).iCycles (c : ℤ))).mp ?_
  simp only [Category.assoc]
  rw [HomologicalComplex.cyclesMap_i,
    reassoc_of% (forgetCyclesIso_inv_iCycles
      ((cplx f F).extend ComplexShape.embeddingUpNat) (c : ℤ)),
    forgetCyclesIso_inv_iCycles, ← CategoryTheory.Functor.map_comp_assoc,
    ← CategoryTheory.Functor.map_comp, fracExtendCycles_comp_iCycles,
    fracExtendCycles_comp_iCycles, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [cplxAbExtend_f_eq_termAb f ψ c]
  exact chase_append _ _ _ _ _ _ hnum

/-- **The extended fraction class is carried by `Hᶜ` of the abelian Čech chain map, as soon as its
numerator is carried.**  The class is the class of a cycle by `classExtendHomology_eq`, the
projection from the cycles is natural, and the statement on cycles is
`fracExtendCycles_comp_cyclesMap_cplxAbExtend`. -/
lemma classExtendHomology_comp_homologyMap_cplxAbExtend
    (hnum : abHom u ≫ (abelianSheaf X).map (fracTermTop f F) ≫ termAb f ψ c =
      abHom w ≫ (abelianSheaf X).map (fracTermTop f G)) :
    abHom u ≫ (abelianSheaf X).map (classExtendHomology f F) ≫
        (forgetHomologyIso ((cplx f F).extend ComplexShape.embeddingUpNat) (c : ℤ)).inv ≫
        HomologicalComplex.homologyMap (cplxAbExtend f ψ) (c : ℤ) =
      abHom w ≫ (abelianSheaf X).map (classExtendHomology f G) ≫
        (forgetHomologyIso ((cplx f G).extend ComplexShape.embeddingUpNat) (c : ℤ)).inv := by
  rw [classExtendHomology_eq, classExtendHomology_eq, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% (map_homologyπ_comp_forgetHomologyIso_inv
      ((cplx f F).extend ComplexShape.embeddingUpNat) (c : ℤ)),
    HomologicalComplex.homologyπ_naturality (cplxAbExtend f ψ) (c : ℤ),
    map_homologyπ_comp_forgetHomologyIso_inv,
    reassoc_of% (fracExtendCycles_comp_cyclesMap_cplxAbExtend f ψ u w hnum)]

/-- **The class map of [Stacks, Tag 0G7Q] is carried by the action `cechHomologyAb` of the
degree-`c` Čech cohomology sheaf, as soon as its numerator is carried.**

This is `classExtendHomology_comp_homologyMap_cplxAbExtend` with the identifications of the
`ℕ`-graded cohomology with that of its `ℤ`-graded extension cancelled off both sides, and it is
the form in which the class map meets the square of step (ii) of [Stacks, Tag 0G85]. -/
theorem classMap_comp_cechHomologyAb
    (hnum : abHom u ≫ (abelianSheaf X).map (fracTermTop f F) ≫ termAb f ψ c =
      abHom w ≫ (abelianSheaf X).map (fracTermTop f G)) :
    abHom u ≫ (abelianSheaf X).map (classMap f F) ≫ cechHomologyAb f ψ c =
      abHom w ≫ (abelianSheaf X).map (classMap f G) := by
  have hkey := classExtendHomology_comp_homologyMap_cplxAbExtend f ψ u w hnum
  rw [classExtendHomology, classExtendHomology, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp] at hkey
  simp only [Category.assoc] at hkey
  rw [cechHomologyAb]
  refine chase_cancel _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ hkey
  · exact (forgetHomologyIso ((cplx f G).extend ComplexShape.embeddingUpNat)
      (c : ℤ)).inv_hom_id
  · rw [← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

end Class

/-! ### The degree-`p` cohomology sheaf in the forgetful image of the derived category -/

section Derived

variable {c : ℕ} (f : Fin c → Γ(X, ⊤)) {F G : X.Modules}

/-- **The degree-`p` cohomology sheaf of the extended alternating Čech complex, as the degree-`p`
cohomology of that complex in the derived category of `𝒪_X`-modules.**  This is the module-level
half of the passage: the identification of the cohomology of the `ℕ`-graded complex with that of
its `ℤ`-graded extension, followed by
`Stacks.Perfect.SupportedFraction.derivedQHomologyIso`.

It is the analogue of
`Stacks.Perfect.SupportedFraction.cokernelLastDifIsoDerivedHomology` with the Čech cokernel
replaced by the cohomology sheaf, and unlike that one it is defined for every family and in every
degree. -/
def cechHomologyToDerived (F : X.Modules) (p : ℕ) :
    (cplx f F).homology p ⟶
      (DerivedCategory.homologyFunctor X.Modules (p : ℤ)).obj
        (DerivedCategory.Q.obj ((cplx f F).extend ComplexShape.embeddingUpNat)) :=
  ((cplx f F).extendHomologyIso ComplexShape.embeddingUpNat (embeddingUpNat_f p)).inv ≫
    (derivedQHomologyIso ((cplx f F).extend ComplexShape.embeddingUpNat) (p : ℤ)).inv

/-- **The comparison of [Stacks, Tag 0G7L] in degree `p` factors through the derived-category
cohomology of the extended Čech complex.**  The first factor is `cechHomologyToDerived`, which
involves no local cohomology; the second is the degree-`p` cohomology of the comparison itself.

This is `Stacks.Perfect.AbelianCechCokernelPassage.cokernelLastDifToSupport_eq` with the cokernel
replaced by the cohomology sheaf.  It needs no quasi-coherence, neither
`Stacks.Perfect.SupportedFraction.cechHomologyToSupport` nor
`Stacks.Perfect.SupportedFraction.cechToSupport` carrying any. -/
lemma cechHomologyToSupport_eq {T : Set X} (hT : IsClosed T)
    (hTf : equationsClosedSet f ⊆ T) (p : ℕ) :
    cechHomologyToSupport f F hT hTf p =
      cechHomologyToDerived f F p ≫
        (DerivedCategory.homologyFunctor X.Modules (p : ℤ)).map (cechToSupport f F hT hTf) := by
  rw [cechHomologyToSupport, extendHomologyToSupport, cechHomologyToDerived, Category.assoc]

/-- **The degree-`p` cohomology sheaf, after forgetting the module structure, mapped to the
degree-`p` cohomology of the forgetful image of the extended Čech complex in the derived category
of abelian sheaves.**  This is `cechHomologyToDerived` conjugated past the comparison
`Stacks.Perfect.AbelianCechCokernelPassage.forgetDerivedHomology`, written out so that the
conjugation is never inverted; see
`cechHomologyToForgetDerived_comp_forgetDerivedHomology_hom`.

It is the analogue of
`Stacks.Perfect.AbelianCechCokernelPassage.cechCokernelToForgetDerived`, off the cokernel. -/
def cechHomologyToForgetDerived (F : X.Modules) (p : ℕ) :
    (abelianSheaf X).obj ((cplx f F).homology p) ⟶
      (DerivedCategory.homologyFunctor
          (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (p : ℤ)).obj
        ((abelianSheaf X).mapDerivedCategory.obj
          (DerivedCategory.Q.obj ((cplx f F).extend ComplexShape.embeddingUpNat))) :=
  (abelianSheaf X).map ((cplx f F).extendHomologyIso ComplexShape.embeddingUpNat
      (embeddingUpNat_f p)).inv ≫
    (forgetHomologyIso ((cplx f F).extend ComplexShape.embeddingUpNat) (p : ℤ)).inv ≫
    (derivedQHomologyIsoAb (((abelianSheaf X).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((cplx f F).extend ComplexShape.embeddingUpNat)) (p : ℤ)).inv ≫
    (DerivedCategory.homologyFunctor
        (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) (p : ℤ)).map
      (forgetQIso ((cplx f F).extend ComplexShape.embeddingUpNat)).inv

/-- Reading `cechHomologyToForgetDerived` through the comparison
`Stacks.Perfect.AbelianCechCokernelPassage.forgetDerivedHomology` gives the forgetful image of
`cechHomologyToDerived`. -/
lemma cechHomologyToForgetDerived_comp_forgetDerivedHomology_hom (F : X.Modules) (p : ℕ) :
    cechHomologyToForgetDerived f F p ≫
        (forgetDerivedHomology
          (DerivedCategory.Q.obj ((cplx f F).extend ComplexShape.embeddingUpNat))
          (p : ℤ)).hom =
      (abelianSheaf X).map (cechHomologyToDerived f F p) := by
  rw [cechHomologyToForgetDerived, forgetDerivedHomology_hom_Q, cechHomologyToDerived,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id_assoc]

/-- **The action `cechHomologyAb` of the degree-`p` Čech cohomology sheaf *is* the degree-`p`
cohomology of the abelian Čech derived map.**  Read through `cechHomologyToForgetDerived`, the
action is carried to `Hᵖ` of
`Stacks.Perfect.AbelianCechDerivedSquare.derivedCechAb`.

This is the passage from the derived square of step (ii) of [Stacks, Tag 0G85] down to the level
of the cohomology sheaf, on the left-hand vertical arrow — the analogue of
`Stacks.Perfect.AbelianCechCokernelPassage.cokernelLastDifAb_eq_homologyFunctor_derivedCechAb`,
for every family and every degree. -/
theorem cechHomologyAb_eq_homologyFunctor_derivedCechAb
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) (p : ℕ) :
    cechHomologyToForgetDerived f F p ≫
        (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
            (p : ℤ)).map (derivedCechAb f ψ) =
      cechHomologyAb f ψ p ≫ cechHomologyToForgetDerived f G p := by
  rw [cechHomologyToForgetDerived, cechHomologyToForgetDerived, derivedCechAb_eq_anyFamily f ψ,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp,
    reassoc_of% (derivedQHomologyIsoAb_inv_naturality (cplxAbExtend f ψ) (p : ℤ)),
    reassoc_of% (cechHomologyAb_comp f ψ p).symm]

end Derived

/-! ### The two inputs of the passage, at an arbitrary family -/

section AnyFamily

variable {F G : X.Modules}

/-- Reassociating a four-fold composite, at an abstract category.  Stated at a variable category
for the reason recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/AbelianCechCokernelPassage.lean`: the
two spellings `X.carrier` and `X.toRingedSpace` of the site of a scheme carry different
`Preorder.smallCategory` instance terms, so `Category.assoc` rewrites nothing in the statement of
`Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare_conj`, while at a variable
category the reassociation is immediate and `exact` instantiates it. -/
private lemma assoc4_formal {C₀ : Type*} [Category* C₀] {A B₁ B₂ B₃ Z : C₀} (a : A ⟶ B₁)
    (b : B₁ ⟶ B₂) (q : B₂ ⟶ B₃) (r : B₃ ⟶ Z) (v : A ⟶ Z) (h : (a ≫ b ≫ q) ≫ r = v) :
    a ≫ b ≫ q ≫ r = v := by
  rw [← h, Category.assoc, Category.assoc]

/-- **The derived square of step (ii) of [Stacks, Tag 0G85], at an arbitrary family of
equations.**

This is `Stacks.Perfect.AbelianCechCokernelPassage.cechToSupport_comp_forgetSupportPushAbMap`
with the nonemptiness of the family removed.  Nothing is reproved: that statement sits in a
section about the top-degree cokernel and so is stated for `f : Fin (n + 1) → Γ(X, 𝒪_X)`, but its
proof is `Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare_conj`, which is
already stated at `f : Fin m → Γ(X, 𝒪_X)` for an arbitrary `m`.  It is restated here rather than
generalised in place so that no existing statement changes, with the family bound in the signature
for the reason recorded at `derivedCechAb_eq_anyFamily`. -/
lemma cechToSupport_comp_forgetSupportPushAbMap_anyFamily {m : ℕ} (e : Fin m → Γ(X, ⊤))
    [F.IsQuasicoherent] [G.IsQuasicoherent] {T : Set X} (hT : IsClosed T)
    (hTe : equationsClosedSet e ⊆ T)
    (χ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) :
    (abelianSheaf X).mapDerivedCategory.map (cechToSupport e F hT hTe) ≫
        forgetSupportPushAbMap hT χ =
      derivedCechAb e χ ≫
        (abelianSheaf X).mapDerivedCategory.map (cechToSupport e G hT hTe) := by
  rw [forgetSupportPushAbMap]
  exact assoc4_formal _ _ _ _ _
    (Stacks.Perfect.AbelianCechDerivedSquare.abelianCechDerivedSquare_conj e hT hTe χ)

/-- **The degree-`p` cohomology of the forgetful image of the comparison of [Stacks, Tag 0G7L] is
the forgetful image of its degree-`p` cohomology, at an arbitrary family of equations.**

This is
`Stacks.Perfect.AbelianCechCokernelPassage.homologyFunctor_map_forget_cechToSupport` with the
nonemptiness of the family removed; as there, it is the naturality of
`Stacks.Perfect.AbelianCechCokernelPassage.forgetDerivedHomology` and nothing else, and that
naturality knows nothing about the family.  The family is bound in the signature for the reason
recorded at `derivedCechAb_eq_anyFamily`. -/
lemma homologyFunctor_map_forget_cechToSupport_anyFamily {m : ℕ} (e : Fin m → Γ(X, ⊤))
    [F.IsQuasicoherent] {T : Set X}
    (hT : IsClosed T) (hTe : equationsClosedSet e ⊆ T) (p : ℤ) :
    (DerivedCategory.homologyFunctor
            (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}) p).map
          ((abelianSheaf X).mapDerivedCategory.map (cechToSupport e F hT hTe)) ≫
        (forgetDerivedHomology (supportPushSingle hT F) p).hom =
      (forgetDerivedHomology
          (DerivedCategory.Q.obj ((cplx e F).extend ComplexShape.embeddingUpNat)) p).hom ≫
        (abelianSheaf X).map
          ((DerivedCategory.homologyFunctor X.Modules p).map (cechToSupport e F hT hTe)) :=
  forgetDerivedHomology_hom_naturality (cechToSupport e F hT hTe) p

end AnyFamily

/-! ### The square of step (ii) of Stacks 0G85 on the degree-`p` cohomology sheaf -/

section Square

variable {c : ℕ} (f : Fin c → Γ(X, ⊤)) {F G : X.Modules}

/-- **The square of step (ii) of [Stacks, Tag 0G85] between the degree-`p` Čech cohomology sheaf
and `i_*ℋ ᵖ_T`, for any number of equations and in every degree.**

For a morphism `ψ` of the underlying abelian sheaves of two quasi-coherent coefficient modules —
not required to be `𝒪_X`-linear — the forgetful image of the comparison of [Stacks, Tag 0G7L] in
degree `p` carries the action `cechHomologyAb` of the Čech cohomology sheaf to the action
`Stacks.Perfect.AbelianCechCokernelPassage.supportCohomologyForgetAbMap` of `i_*ℋ ᵖ_T`.

This is
`Stacks.Perfect.AbelianCechCokernelPassage.map_cokernelLastDifToSupport_abelian_square` with the
Čech cokernel replaced by the cohomology sheaf, and with both of its restrictions removed: the
family may be empty and the degree need not be the top one.  The proof is the same three steps,
with the cokernel bypassed — the derived square
(`cechToSupport_comp_forgetSupportPushAbMap_anyFamily`), the left-hand vertical arrow
(`cechHomologyAb_eq_homologyFunctor_derivedCechAb`) and the horizontal arrows
(`homologyFunctor_map_forget_cechToSupport_anyFamily`).

It carries no hypothesis beyond quasi-coherence of the two coefficient modules and the two
conditions on the closed subset. -/
theorem map_cechHomologyToSupport_abelian_square [F.IsQuasicoherent] [G.IsQuasicoherent]
    (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G) {T : Set X} (hT : IsClosed T)
    (hTf : equationsClosedSet f ⊆ T) (p : ℕ) :
    (abelianSheaf X).map (cechHomologyToSupport f F hT hTf p) ≫
        supportCohomologyForgetAbMap hT (p : ℤ) ψ =
      cechHomologyAb f ψ p ≫
        (abelianSheaf X).map (cechHomologyToSupport f G hT hTf p) := by
  rw [cechHomologyToSupport_eq, cechHomologyToSupport_eq,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
    supportCohomologyForgetAbMap,
    ← cechHomologyToForgetDerived_comp_forgetDerivedHomology_hom f F p,
    ← cechHomologyToForgetDerived_comp_forgetDerivedHomology_hom f G p]
  simp only [Category.assoc]
  rw [← reassoc_of% (homologyFunctor_map_forget_cechToSupport_anyFamily f (F := F) hT hTf
      (p : ℤ)),
    Iso.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp_assoc,
    cechToSupport_comp_forgetSupportPushAbMap_anyFamily f hT hTf ψ,
    CategoryTheory.Functor.map_comp_assoc,
    reassoc_of% (cechHomologyAb_eq_homologyFunctor_derivedCechAb f ψ p),
    homologyFunctor_map_forget_cechToSupport_anyFamily f hT hTf (p : ℤ)]

end Square

/-! ### The localized Leibniz rule for the class map of Stacks 0G7Q -/

section Leibniz

variable {c : ℕ} (f : Fin c → Γ(X, ⊤)) {E F G : X.Modules}
  (ψ : Scheme.Modules.presheaf F ⟶ Scheme.Modules.presheaf G)
  (u : Scheme.Modules.presheaf E ⟶ Scheme.Modules.presheaf F)
  (w : Scheme.Modules.presheaf E ⟶ Scheme.Modules.presheaf G)

/-- **The numerator identity, read on abelian sheaves rather than on abelian presheaves.**  The
two are the same identity: reading a composite of morphisms of abelian presheaves as a morphism of
abelian sheaves composes the readings, and
`Stacks.Perfect.AbelianFraction.abelianSheaf_map` identifies the reading of an `𝒪_X`-linear
morphism with its image under the forgetful functor — all by `rfl`. -/
lemma fracTermTop_abelian_of_presheaf
    (hnum : u ≫ Scheme.Modules.Hom.mapPresheaf (fracTermTop f F) ≫
        Stacks.Perfect.AbelianFraction.termPre f ψ c =
      w ≫ Scheme.Modules.Hom.mapPresheaf (fracTermTop f G)) :
    abHom u ≫ (abelianSheaf X).map (fracTermTop f F) ≫ termAb f ψ c =
      abHom w ≫ (abelianSheaf X).map (fracTermTop f G) :=
  congrArg (abHom (F := E) (G := term f G c)) hnum

/-- **The class map of [Stacks, Tag 0G7Q], read on the coefficient module and in `i_*ℋ ᶜ_T(ℱ)`,
is natural along a morphism of the underlying abelian sheaves whose numerator is carried** — for
any number of equations, zero included.

Both factors of `Stacks.Perfect.FractionClass.classMapToSupport` are carried: the fraction class
by `classMap_comp_cechHomologyAb`, which is where the numerator hypothesis is consumed, and the
comparison of [Stacks, Tag 0G7L] in degree `c` by
`map_cechHomologyToSupport_abelian_square`.  The two actions of `i_*ℋ ᶜ_T` on a merely additive
morphism are identified, unconditionally, by
`Stacks.Perfect.SupportedEndoForgetDegreewise`
`.supportCohomologySheafAbelianMap_eq_supportCohomologyForgetAbMap`.

This is `Stacks.Gysin.supportedFractionSource_comm_of_smul` with the `c = d + 1` removed, the
localized hypothesis on `ψ` abstracted into the numerator identity. -/
theorem classMapToSupport_comm_of_num [F.IsQuasicoherent] [G.IsQuasicoherent]
    {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T)
    (hnum : abHom u ≫ (abelianSheaf X).map (fracTermTop f F) ≫ termAb f ψ c =
      abHom w ≫ (abelianSheaf X).map (fracTermTop f G)) :
    abHom u ≫ (abelianSheaf X).map (classMapToSupport f F hT hTf) ≫
        GysinAbelianSquare.supportCohomologySheafAbelianMap hT c (abHom ψ) =
      abHom w ≫ (abelianSheaf X).map (classMapToSupport f G hT hTf) := by
  rw [supportCohomologySheafAbelianMap_eq_supportCohomologyForgetAbMap hT c ψ,
    classMapToSupport, classMapToSupport, CategoryTheory.Functor.map_comp,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  rw [map_cechHomologyToSupport_abelian_square f ψ hT hTf c,
    reassoc_of% (classMap_comp_cechHomologyAb f ψ u w hnum)]

/-- **With no equations the fraction in the top term is the section itself.**  The denominator is
the empty product `1`; this is the `c = 0` companion of
`Stacks.Perfect.FractionClass.fracTermTop_succ`, and like it holds by `rfl`. -/
lemma fracTermTop_zero (g : Fin 0 → Γ(X, ⊤)) (M : X.Modules) : fracTermTop g M = 𝟙 M := rfl

/-- **The numerator identity at an empty family of equations is plain additivity.**  The fraction
is then the section itself and the degree-`0` Čech term is the coefficient module, so the identity
says exactly that `ψ` carries `u` to `w`.

This is the whole of what is peculiar to `c = 0`, and it is why that case is not a reindex of
`c = d + 1`: there is no fraction to divide by and no localization anywhere in it. -/
lemma fracTermTop_abelian_zero (g : Fin 0 → Γ(X, ⊤)) (hψ : u ≫ ψ = w) :
    abHom u ≫ (abelianSheaf X).map (fracTermTop g F) ≫ termAb g ψ 0 =
      abHom w ≫ (abelianSheaf X).map (fracTermTop g G) := by
  change abHom u ≫ (abelianSheaf X).map (𝟙 F) ≫ abHom ψ =
    abHom w ≫ (abelianSheaf X).map (𝟙 G)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, ← hψ]
  rfl

/-- **The numerator identity at a nonempty family of equations is the localized Leibniz rule.**
It is `Stacks.Perfect.GysinFractionDeRham.fracTerm_comm_prodTermPre_of_smul`, read through
`fracTermTop_abelian_of_presheaf`: at `c = d + 1` the fraction in the top term is the fraction
with the product of the equations as denominator, and the induced map on the top Čech term is the
induced map on the product of Čech terms, both by `rfl`. -/
lemma fracTermTop_abelian_succ {d : ℕ} (e : Fin (d + 1) → Γ(X, ⊤))
    (h : ∀ (V : X.Opens) (v : Γ(X, V)) (y : Γ(E, V)),
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (∏ j, e j) * v = 1 →
      sectionsHom ψ V (v • sectionsHom u V y) = v • sectionsHom w V y) :
    abHom u ≫ (abelianSheaf X).map (fracTermTop e F) ≫ termAb e ψ (d + 1) =
      abHom w ≫ (abelianSheaf X).map (fracTermTop e G) :=
  fracTermTop_abelian_of_presheaf e ψ u w
    (Stacks.Perfect.GysinFractionDeRham.fracTerm_comm_prodTermPre_of_smul e ψ u w h)

/-- **At an empty family of equations the localized identity is the plain one.**  The only local
section inverting the empty product `1` is `1` itself, so the hypothesis at `v = 1` says that `ψ`
carries `u` to `w`, with no localization used. -/
private lemma comp_eq_of_smul_empty (g : Fin 0 → Γ(X, ⊤))
    (h : ∀ (V : X.Opens) (v : Γ(X, V)) (y : Γ(E, V)),
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (∏ j, g j) * v = 1 →
      sectionsHom ψ V (v • sectionsHom u V y) = v • sectionsHom w V y) :
    u ≫ ψ = w := by
  refine NatTrans.ext (funext fun U => AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x => ?_))
  change sectionsHom ψ U.unop (sectionsHom u U.unop x) = sectionsHom w U.unop x
  have hone : X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (∏ j, g j) *
      (1 : Γ(X, U.unop)) = 1 := by
    rw [Fin.prod_univ_zero, mul_one]
    exact map_one (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom
  have hx := h U.unop 1 x hone
  rwa [one_smul, one_smul] at hx

/-- **The numerator identity, at any number of equations.**  The case split on the number of
equations happens here and nowhere else: `fracTermTop_abelian_succ` for a nonempty family, where
the identity is the Čech-level localized Leibniz rule, and `fracTermTop_abelian_zero` for an
empty one, where it degenerates to `u ≫ ψ = w`. -/
lemma fracTermTop_abelian_of_smul {m : ℕ} (g : Fin m → Γ(X, ⊤))
    (h : ∀ (V : X.Opens) (v : Γ(X, V)) (y : Γ(E, V)),
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (∏ j, g j) * v = 1 →
      sectionsHom ψ V (v • sectionsHom u V y) = v • sectionsHom w V y) :
    abHom u ≫ (abelianSheaf X).map (fracTermTop g F) ≫ termAb g ψ m =
      abHom w ≫ (abelianSheaf X).map (fracTermTop g G) := by
  match m, g, h with
  | 0, g₀, h₀ => exact fracTermTop_abelian_zero ψ u w g₀ (comp_eq_of_smul_empty ψ u w g₀ h₀)
  | _ + 1, e, hₑ => exact fracTermTop_abelian_succ ψ u w e hₑ

/-- **The localized Leibniz rule for the class map of [Stacks, Tag 0G7Q], at any number of
equations.**  The class map `c_{f₁, …, f_c} : ℱ ⟶ i_*ℋ ᶜ_T(ℱ)` of [Stacks, Tag 0G7Q], read on the
coefficient module, is natural along a morphism `ψ` of the underlying *abelian* sheaves which
commutes with dividing by the product of the equations after precomposition with a factor `u`.

**The number of equations is an arbitrary natural number.**  This is
`Stacks.Gysin.supportedFractionSource_comm_of_smul` with the `c = d + 1` removed; that statement
is about `Stacks.Perfect.SupportedFraction.supportedFractionSource`, which factors through the
cokernel of the differential of the extended alternating Čech complex into its *top* degree, and
an empty family gives a complex with only degree `0` and no such differential.

The hypothesis is the localized identity and nothing more: no `𝒪_X`-linearity, which the relative
de Rham differential of [Stacks, Tag 0G85] and [Stacks, Tag 0G87] does not have.  The proof
splits on `c` only to discharge the *numerator*:

* for `c = d + 1` it is `fracTermTop_abelian_succ`, the Čech-level localized Leibniz rule of
  `Stacks.Perfect.GysinFractionDeRham.fracTerm_comm_prodTermPre_of_smul`;
* for `c = 0` it is `fracTermTop_abelian_zero`, where the identity degenerates to `u ≫ ψ = w` —
  the empty product is `1` and the only section inverting `1` is `1`.

Everything else, `classMapToSupport_comm_of_num`, is uniform in `c`. -/
theorem classMapToSupport_comm_of_smul [F.IsQuasicoherent] [G.IsQuasicoherent]
    (h : ∀ (V : X.Opens) (v : Γ(X, V)) (y : Γ(E, V)),
      X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op (∏ j, f j) * v = 1 →
      sectionsHom ψ V (v • sectionsHom u V y) = v • sectionsHom w V y)
    {T : Set X} (hT : IsClosed T) (hTf : equationsClosedSet f ⊆ T) :
    abHom u ≫ (abelianSheaf X).map (classMapToSupport f F hT hTf) ≫
        GysinAbelianSquare.supportCohomologySheafAbelianMap hT c (abHom ψ) =
      abHom w ≫ (abelianSheaf X).map (classMapToSupport f G hT hTf) :=
  classMapToSupport_comm_of_num f ψ u w hT hTf (fracTermTop_abelian_of_smul ψ u w f h)

end Leibniz

end Stacks.Perfect.AbelianCechClassPassage

end
