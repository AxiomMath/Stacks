module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyGlue.AffineOpenVanishing
public import StacksFrontier.AlgebraicGeometry.LeraySectionsCollapse.Leray
public import StacksFrontier.AlgebraicGeometry.UniformTwistBound.Basic
public import StacksFrontier.AlgebraicGeometry.SheafOfModulesEnoughInjectives

/-!
# Leray degeneration over an affine base

Let `f : X ⟶ Y` be a morphism of schemes with `Y` **affine**. The cohomology `Hᵖ(X, ℱ)` is the
right derived functor of the *composite* `f_* ⋙ Γ(Y, -)` — on the nose, by
`Stacks.SchemeCohomology.Hfunctor_eq_rightDerived_comp` — so it is governed by the Leray spectral
sequence of that composite, whose second page is `Hⁱ(Y, Rʲf_*ℱ)`. Over an affine base and for
quasi-coherent higher direct images the page is concentrated in the column `i = 0`, and the
sequence degenerates. The consequence this file proves is the vanishing half of that degeneration:

> if `Rᑫf_*ℱ = 0` for every `q ≥ n`, then `Hᵖ(X, ℱ) = 0` for every `p ≥ n` (and `p > 0`).

That turns a bound on the **relative** higher direct images into a bound on **absolute**
cohomology, which is exactly the step between the relative bound
`Stacks.AlgebraicGeometry.Tag0B5QUniformTwistBound.exists_isZero_rightDerivedPlus_twist` and the
hypothesis `hbound` of [Stacks, Tag 0B5Q] assertion (3).

## Main definitions

* `Stacks.AlgebraicGeometry.LerayAffineBase.hdi`: `Rᑫf_*`, Mathlib's `ℕ`-indexed higher direct
  image, in the spelling the `ℕ`-indexed cohomology `Hgroup` is stated over.
* `Stacks.AlgebraicGeometry.LerayAffineBase.HasAcyclicDirectImages`: every higher direct image of
  `ℱ` has vanishing positive-degree cohomology on `Y`. This is the hypothesis the degeneration
  really needs; over an affine base it is *supplied*, not assumed (see
  `hasAcyclicDirectImages_of_isAffine`).

## Main results

* `Stacks.AlgebraicGeometry.LerayAffineBase.isZero_hgroup_of_isZero_hdi`: **the degeneration, in
  its general form.** For any morphism of schemes, if all the higher direct images of `ℱ` are
  acyclic for `Γ(Y, -)` and those in degrees `≥ n` vanish, then `Hᵖ(X, ℱ) = 0` for `p ≥ n`,
  `p > 0`.
* `Stacks.AlgebraicGeometry.LerayAffineBase.hasAcyclicDirectImages_of_isAffine`: over an affine
  base, for `f` quasi-compact and quasi-separated and `ℱ` quasi-coherent, the acyclicity
  hypothesis holds — this is the composition of
  `Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffine` with
  `Stacks.AlgebraicGeometry.Tag01XJQcohInduction.higherDirectImage_isQuasicoherent`.
* `Stacks.AlgebraicGeometry.LerayAffineBase.isZero_hgroup_of_isZero_rightDerivedPlus`: the two
  previous results composed, with the input in the `ℤ`-indexed `rightDerivedPlus` spelling that
  the Tag 01XJ uniform vanishing produces.
* `Stacks.AlgebraicGeometry.LerayAffineBase.exists_isZero_hgroup_twist`: **`hbound` for
  [Stacks, Tag 0B5Q] assertion (3)**: for `𝒜` a graded ring whose underlying ring is Noetherian
  there is a degree `e` above which `Hᵖ(Proj 𝒜, ℱ(d))` vanishes for *every* quasi-coherent `ℱ`
  and *every* twist `d`.
* `Stacks.AlgebraicGeometry.LerayAffineBase.exists_isZero_hgroup_twist_of_step`: Tag 0B5Q
  assertion (3) with `hbound` discharged, so that `step` is its only remaining hypothesis.

## Why this is not an existing Leray collapse

Three statements in this repository are near-misses, and each fails for a different reason.

* `Stacks.LeraySections.schemeCohomologyIsoOfVanishingHigherDirectImages` ([Stacks, Tag 01F4]
  part (1)) asks that **all** positive higher direct images vanish. For the application that is
  the conclusion one is trying to reach, not a hypothesis one has. It is nevertheless the base
  case of the induction below, and the only place that collapse is used.
* `Stacks.AffineCohomologyPushforward.cohomologyPushforwardIso` ([Stacks, Tag 089W]) asks that
  `f` be an affine *morphism*. The degeneration here is from affineness of the **base**, and
  `AlgebraicGeometry.Proj.toSpecZero 𝒜` is not an affine morphism.
* `Stacks.RelativeLeray.exists_spectralSequence_relativeLeray` produces the spectral sequence as
  an existence statement with `Nonempty`-valued page identifications, so no degeneration argument
  can be run through it: nothing identifies its `E₂^{0,p}` with `Hᵖ(X, ℱ)`.

**The bridge is therefore not a composition of two known facts.** The two obvious ingredients —
affine vanishing and quasi-coherence of the higher direct images — are what make
the *second page* concentrated in one column, but collapsing a spectral sequence concentrated in
one column is itself a theorem, and nothing in the library has it for this pair of functors.
What is done here instead is the classical dimension-shifting proof of the same collapse, which
avoids the spectral sequence altogether and stays inside the `ℕ`-indexed derived functors that
`Hgroup` is defined by:

1. embed `ℱ` in an injective `𝒪_X`-module, `0 → ℱ → ℐ → 𝒬 → 0`;
2. `Rᑫf_*ℐ = 0` for `q > 0`, so the connecting map `Rᑫf_*𝒬 ⟶ Rᑫ⁺¹f_*ℱ` is an isomorphism for
   `q ≥ 1`, which moves the vanishing bound down by one on `𝒬`;
3. `Hᵖ(X, ℐ) = 0` for `p > 0`, so `Hᵖ⁻¹(X, 𝒬) = 0` forces `Hᵖ(X, ℱ) = 0`;
4. the acyclicity hypothesis `HasAcyclicDirectImages` passes from `ℱ` to `𝒬`. This is the one
   step that is not formal: `f_*` is only left exact, so `f_*𝒬` sits in a **four**-term exact
   sequence `0 → f_*ℱ → f_*ℐ → f_*𝒬 → R¹f_*ℱ → 0` (right exactness at the last term is
   `R¹f_*ℐ = 0`), which is split here into two short exact sequences through `coker(f_*ℱ → f_*ℐ)`.
   Acyclicity of `f_*ℐ` for `Γ(Y, -)` is
   `Stacks.LeraySections.rightAcyclic_secF_schemePushforward_obj` ([Stacks, Tag 01EX]), and
   acyclicity of `R¹f_*ℱ` is where the affine base enters;
5. the induction terminates at `n = 0`, where all higher direct images vanish and
   Tag 01F4 part (1) applies.

So the degeneration is **unconditional over an affine base** for `f` quasi-compact and
quasi-separated and `ℱ` quasi-coherent: `hasAcyclicDirectImages_of_isAffine` carries no further
hypothesis. Stated for a general base it carries exactly one, `HasAcyclicDirectImages`, and that
hypothesis is necessary — it is the statement that the second page has only one column.

## What is still owed for [Stacks, Tag 0B5Q]

`hbound` is discharged (`exists_isZero_hgroup_twist`). The other hypothesis, `step`, is Tag 0B5Q
assertion (1) — every coherent sheaf on `Proj 𝒜` is a quotient of a finite direct sum of twists
`𝒪(-d)` — together with short exactness of the twisted sequence and eventual acyclicity of the
middle term. None of that is here, and none of it is in either tree: the only statement of that
shape is `Stacks.AmpleGlobalGeneration.IsQuotientOfNegativeTwists`, which is for an ample
invertible module rather than for the twisting sheaf of an arbitrary graded ring.

## Implementation notes

**Indexing.** Everything is in Mathlib's `ℕ`-indexed `CategoryTheory.Functor.rightDerived`,
because `Hgroup` is, and because the long exact sequence available in this repository
(`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`) is stated there. The
`ℤ`-indexed inputs are converted at the boundary by
`Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff`, and `R⁰f_*` is identified with `f_*` by
`CategoryTheory.Functor.rightDerivedZeroIsoSelf`, which needs left exactness of `f_*` —
`Stacks.SchemeCohomology.pushforward_preservesFiniteLimits`.

**The three `rfl`-equal spellings of the `Proj` ring sheaf.** `projRingSheaf 𝒜` and
`(Proj 𝒜).ringCatSheaf` are the same term (`Stacks.AlgebraicGeometry.ProjTrivialization`'s
`ringCatSheaf_eq`, by `rfl`), but instance search crosses neither direction, `Scheme.Modules`
being a `def`. In the `Proj` section below the quasi-coherence of a twist is therefore passed by
`@`-application rather than left to search.

## References

* [Stacks Project, Tag 01F4](https://stacks.math.columbia.edu/tag/01F4)
* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 0B5Q](https://stacks.math.columbia.edu/tag/0B5Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u v

namespace Stacks.AlgebraicGeometry.LerayAffineBase

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

-- Module sheaves on a scheme form an abelian category with enough injectives, at the spelling
-- `AlgebraicGeometry.Scheme.ringCatSheaf` the statements below use.
attribute [local instance] _root_.Stacks.SchemeCohomology.sheafOfModules_abelian
  _root_.Stacks.Cohomology.enoughInjectives_sheafOfModules_ringCatSheaf

/-! ### Three-term chases in a cohomological δ-functor

The long exact sequence is used only through the three statements below, each of which reads one
vanishing off the vanishing of the two neighbouring terms. They are stated for an arbitrary
cohomological δ-functor; `isZero_obj_X₃` is
`Stacks.HighTwistDevissage.isZero_obj_of_shortExact_of_isZero` restated here so that this file
does not depend on the dévissage engine. -/

section DeltaFunctorChase

variable {A : Type*} [Category* A] [Abelian A] {B : Type*} [Category* B]
  [Preadditive B] (D : DeltaFunctor A B) {S : ShortComplex A}

/-- If `Dⁿ(X₂)` and `Dⁿ⁺¹(X₁)` vanish then so does `Dⁿ(X₃)`. -/
theorem isZero_obj_X₃ (hS : S.ShortExact) (n : ℕ) (h₂ : IsZero ((D.functor n).obj S.X₂))
    (h₁ : IsZero ((D.functor (n + 1)).obj S.X₁)) : IsZero ((D.functor n).obj S.X₃) :=
  haveI : Mono (D.δ hS n) :=
    D.mono_δ_of_map_g_eq_zero hS n (h₂.eq_zero_of_src ((D.functor n).map S.g))
  IsZero.of_mono_eq_zero (D.δ hS n) (h₁.eq_zero_of_tgt (D.δ hS n))

/-- If `Dⁿ⁺¹(X₂)` and `Dⁿ(X₃)` vanish then so does `Dⁿ⁺¹(X₁)`. -/
theorem isZero_obj_X₁_succ (hS : S.ShortExact) (n : ℕ)
    (h₂ : IsZero ((D.functor (n + 1)).obj S.X₂)) (h₃ : IsZero ((D.functor n).obj S.X₃)) :
    IsZero ((D.functor (n + 1)).obj S.X₁) :=
  haveI : Epi (D.δ hS n) :=
    D.epi_δ_of_map_f_eq_zero hS n (h₂.eq_zero_of_tgt ((D.functor (n + 1)).map S.f))
  IsZero.of_epi_eq_zero (D.δ hS n) (h₃.eq_zero_of_src (D.δ hS n))

variable [HasZeroObject B]

/-- If `Dⁿ(X₁)` and `Dⁿ(X₃)` vanish then so does `Dⁿ(X₂)`. -/
theorem isZero_obj_X₂ (hS : S.ShortExact) (n : ℕ) (h₁ : IsZero ((D.functor n).obj S.X₁))
    (h₃ : IsZero ((D.functor n).obj S.X₃)) : IsZero ((D.functor n).obj S.X₂) :=
  haveI : Mono ((D.functor n).map S.g) :=
    (ShortComplex.exact_iff_mono _ (h₁.eq_zero_of_src ((D.functor n).map S.f))).1
      (D.exact_map hS n)
  IsZero.of_mono_eq_zero ((D.functor n).map S.g) (h₃.eq_zero_of_tgt _)

end DeltaFunctorChase

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **The `q`-th higher direct image, `ℕ`-indexed.** This is the spelling that pairs with
`Hgroup`; the `ℤ`-indexed `Functor.rightDerivedPlus` form is converted to it by
`Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff`. -/
abbrev hdi (q : ℕ) (F : X.Modules) : Y.Modules :=
  ((Scheme.Modules.pushforward f).rightDerived q).obj F

/-- The long exact sequence of the higher direct images, as a cohomological δ-functor. -/
abbrev pushDelta : DeltaFunctor X.Modules Y.Modules :=
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives (Scheme.Modules.pushforward f)

/-- The long exact cohomology sequence over the top open of a scheme, as a cohomological
δ-functor. -/
abbrev secDelta (Z : Scheme.{u}) :=
  Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
    (secF Z.ringCatSheaf (⊤ : Opens Z.carrier))

/-- The degree-`n` part of `secDelta` is the cohomology functor `Hⁿ(Z, -)`. -/
theorem secDelta_functor (Z : Scheme.{u}) (n : ℕ) :
    (secDelta Z).functor n = Hfunctor Z.ringCatSheaf ⊤ n :=
  rfl

/-- The degree-`n` part of `pushDelta` is the `n`-th higher direct image. -/
theorem pushDelta_functor (n : ℕ) :
    (pushDelta f).functor n = (Scheme.Modules.pushforward f).rightDerived n :=
  rfl

/-! ### Vanishing on injectives -/

/-- The higher direct images of an injective module vanish in positive degrees. -/
theorem isZero_hdi_injective (q : ℕ) (I : X.Modules) (hI : Injective I) :
    IsZero (hdi f (q + 1) I) :=
  have := hI
  Functor.isZero_rightDerived_obj_injective_succ (Scheme.Modules.pushforward f) q I

/-- The cohomology of an injective module vanishes in positive degrees. -/
theorem isZero_hgroup_injective (p : ℕ) (I : X.Modules) (hI : Injective I) :
    IsZero (Hgroup X.ringCatSheaf ⊤ (p + 1) I) :=
  @Functor.isZero_rightDerived_obj_injective_succ _ _ _ _ _ _ _
    (secF X.ringCatSheaf ⊤) _ p I hI

/-- Vanishing of the cohomology `Hᵖ(Y, -)` transfers along an isomorphism of modules. -/
private theorem isZero_hgroup_of_iso {p : ℕ} {G H : Y.Modules} (e : G ≅ H)
    (h : IsZero (Hgroup Y.ringCatSheaf ⊤ p H)) : IsZero (Hgroup Y.ringCatSheaf ⊤ p G) :=
  h.of_iso ((Hfunctor Y.ringCatSheaf ⊤ p).mapIso e)

/-- **The pushforward of an injective module has vanishing higher cohomology on the target.**
This is the acyclicity input of [Stacks, Tag 01EX], proved as
`Stacks.LeraySections.rightAcyclic_secF_schemePushforward_obj`, read in Mathlib's `ℕ`-indexed
right derived functors. -/
theorem isZero_hgroup_pushforward_injective (p : ℕ) (hp : 0 < p) (I : X.Modules)
    (hI : Injective I) :
    IsZero (Hgroup Y.ringCatSheaf ⊤ p ((Scheme.Modules.pushforward f).obj I)) := by
  have h := Stacks.LeraySections.rightAcyclic_secF_schemePushforward_obj f ⊤ I hI
  have h2 := ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus
    (secF Y.ringCatSheaf ⊤) _).2 inferInstance).1 h (p : ℤ) (by exact_mod_cast hp)
  exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ rfl _).1 h2

/-- `R⁰f_*ℐ` has vanishing higher cohomology on the target, for `ℐ` injective: the previous
statement transported along `CategoryTheory.Functor.rightDerivedZeroIsoSelf`. -/
theorem isZero_hgroup_hdi_zero_injective (p : ℕ) (hp : 0 < p) (I : X.Modules)
    (hI : Injective I) : IsZero (Hgroup Y.ringCatSheaf ⊤ p (hdi f 0 I)) :=
  isZero_hgroup_of_iso ((Functor.rightDerivedZeroIsoSelf (Scheme.Modules.pushforward f)).app I)
    (isZero_hgroup_pushforward_injective f p hp I hI)

/-! ### The acyclicity hypothesis -/

/-- **Every higher direct image of `ℱ` is acyclic for `Γ(Y, -)`.** This is the hypothesis under
which the Leray spectral sequence of `f_* ⋙ Γ(Y, -)` has its second page concentrated in the
column `i = 0`, and therefore degenerates. Over an affine base it is automatic for a
quasi-coherent `ℱ` and a quasi-compact quasi-separated `f`
(`hasAcyclicDirectImages_of_isAffine`). -/
def HasAcyclicDirectImages (F : X.Modules) : Prop :=
  ∀ q p : ℕ, 0 < p → IsZero (Hgroup Y.ringCatSheaf ⊤ p (hdi f q F))

/-! ### The dévissage step -/

section Devissage

variable {S : ShortComplex X.Modules}

/-- For a short exact sequence `0 → ℱ → ℐ → 𝒬 → 0` with `ℐ` injective, the connecting morphism
`Rᑫ⁺¹f_*𝒬 ⟶ Rᑫ⁺²f_*ℱ` is an isomorphism: both neighbours in the long exact sequence are higher
direct images of `ℐ`, hence zero. -/
theorem isIso_pushDelta_δ (hS : S.ShortExact) (hinj : Injective S.X₂) (q : ℕ) :
    IsIso ((pushDelta f).δ hS (q + 1)) := by
  have := (pushDelta f).mono_δ_of_map_g_eq_zero hS (q + 1)
    ((isZero_hdi_injective f q S.X₂ hinj).eq_zero_of_src _)
  have := (pushDelta f).epi_δ_of_map_f_eq_zero hS (q + 1)
    ((isZero_hdi_injective f (q + 1) S.X₂ hinj).eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

/-- The connecting isomorphism `Rᑫ⁺¹f_*𝒬 ≅ Rᑫ⁺²f_*ℱ` of `isIso_pushDelta_δ`. -/
def hdiδIso (hS : S.ShortExact) (hinj : Injective S.X₂) (q : ℕ) :
    ((pushDelta f).functor (q + 1)).obj S.X₃ ≅
      ((pushDelta f).functor (q + 1 + 1)).obj S.X₁ :=
  have := isIso_pushDelta_δ f hS hinj q
  asIso ((pushDelta f).δ hS (q + 1))

/-- The vanishing bound on the higher direct images drops by one along the dévissage. -/
theorem isZero_hdi_X₃_of_isZero_hdi_X₁ (hS : S.ShortExact) (hinj : Injective S.X₂) (q : ℕ)
    (h : IsZero (hdi f (q + 1 + 1) S.X₁)) : IsZero (hdi f (q + 1) S.X₃) :=
  h.of_iso (hdiδIso f hS hinj q)

/-- **The degree shift on cohomology along a dévissage by an injective.** For
`0 → ℱ → ℐ → 𝒬 → 0` with `ℐ` injective, `Hᵐ(X, 𝒬) = 0` forces `Hᵐ⁺¹(X, ℱ) = 0`: the connecting
morphism is epi because `Hᵐ⁺¹(X, ℐ) = 0`. -/
theorem isZero_hgroup_succ_of_isZero_hgroup (hS : S.ShortExact) (hinj : Injective S.X₂) (m : ℕ)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ m S.X₃)) :
    IsZero (Hgroup X.ringCatSheaf ⊤ (m + 1) S.X₁) := by
  have hz := isZero_obj_X₁_succ (secDelta X) hS m
    (isZero_hgroup_injective m S.X₂ hinj) h
  rwa [secDelta_functor] at hz

/-- **The acyclicity hypothesis passes to the quotient term of a dévissage by an injective.**
This is the step that is not formal: `f_*` is only left exact, so the sequence
`0 → f_*ℱ → f_*ℐ → f_*𝒬 → R¹f_*ℱ → 0` has four terms, and it is split here through
`coker(f_*ℱ → f_*ℐ)`. Exactness at the last term is `R¹f_*ℐ = 0`. -/
theorem hasAcyclicDirectImages_X₃ (hS : S.ShortExact) (hinj : Injective S.X₂)
    (h₁ : HasAcyclicDirectImages f S.X₁) : HasAcyclicDirectImages f S.X₃ := by
  intro q p hp
  match q with
  | q + 1 =>
      exact isZero_hgroup_of_iso (hdiδIso f hS hinj q) (h₁ (q + 1 + 1) p hp)
  | 0 =>
      -- `u`, `v` and `δ₀` are the first three maps of the four-term sequence.
      set u := ((pushDelta f).functor 0).map S.f with hu
      set v := ((pushDelta f).functor 0).map S.g with hv
      have hmap := (pushDelta f).exact_map hS 0
      have hδ₁ := (pushDelta f).exact_δ₁ hS 0
      have hδepi : Epi ((pushDelta f).δ hS 0) :=
        (pushDelta f).epi_δ_of_map_f_eq_zero hS 0
          ((isZero_hdi_injective f 0 S.X₂ hinj).eq_zero_of_tgt _)
      -- The first short exact sequence, `0 → R⁰f_*ℱ → R⁰f_*ℐ → coker u → 0`.
      have hSC₁ : (ShortComplex.mk u (cokernel.π u) (cokernel.condition u)).ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel u)
          mono_f := (pushDelta f).mono_map_f hS
          epi_g := inferInstance }
      -- The second one, `0 → coker u → R⁰f_*𝒬 → R¹f_*ℱ → 0`.
      set w := cokernel.desc u v (ShortComplex.map S ((pushDelta f).functor 0)).zero with hw
      have hπw : cokernel.π u ≫ w = v := cokernel.π_desc _ _ _
      have hw0 : w ≫ (pushDelta f).δ hS 0 = 0 := by
        rw [← cancel_epi (cokernel.π u), comp_zero, ← Category.assoc, hπw]
        exact (pushDelta f).map_g_δ hS 0
      have hlift : kernel.lift ((pushDelta f).δ hS 0) v ((pushDelta f).map_g_δ hS 0) =
          cokernel.π u ≫ kernel.lift ((pushDelta f).δ hS 0) w hw0 := by
        rw [← cancel_mono (kernel.ι ((pushDelta f).δ hS 0))]
        simp only [kernel.lift_ι, Category.assoc]
        exact hπw.symm
      have hSC₂ : (ShortComplex.mk w ((pushDelta f).δ hS 0) hw0).ShortExact := by
        refine { exact := ?_, mono_f := hmap.mono_cokernelDesc, epi_g := hδepi }
        rw [ShortComplex.exact_iff_epi_kernel_lift]
        have : Epi (cokernel.π u ≫ kernel.lift ((pushDelta f).δ hS 0) w hw0) := by
          rw [← hlift]; exact hδ₁.epi_kernelLift
        exact epi_of_epi (cokernel.π u) _
      -- `coker u` is acyclic: both its neighbours in the first sequence are.
      have hcoker : ∀ m : ℕ, 0 < m → IsZero (Hgroup Y.ringCatSheaf ⊤ m (cokernel u)) :=
        fun m hm ↦ isZero_obj_X₃ (secDelta Y) hSC₁ m
          (isZero_hgroup_hdi_zero_injective f m hm S.X₂ hinj) (h₁ 0 (m + 1) (by omega))
      -- and then so is `R⁰f_*𝒬`, by the second sequence and acyclicity of `R¹f_*ℱ`.
      exact isZero_obj_X₂ (secDelta Y) hSC₂ p (hcoker p hp) (h₁ 1 p hp)

end Devissage

/-! ### The degeneration -/

/-- **Leray degeneration, in its general form.** Let `f : X ⟶ Y` be a morphism of schemes and let
`ℱ` be an `𝒪_X`-module all of whose higher direct images are acyclic for `Γ(Y, -)`. If
`Rᑫf_*ℱ = 0` for every `q ≥ n`, then `Hᵖ(X, ℱ) = 0` for every `p ≥ n` with `p > 0`.

The proof is descending induction on `n` by dimension shifting; the case `n = 0` is
[Stacks, Tag 01F4] part (1),
`Stacks.LeraySections.schemeCohomologyIsoOfVanishingHigherDirectImages`, followed by the
acyclicity hypothesis in degree `0`. -/
theorem isZero_hgroup_of_isZero_hdi (n : ℕ) :
    ∀ F : X.Modules, HasAcyclicDirectImages f F →
      (∀ q : ℕ, 0 < q → n ≤ q → IsZero (hdi f q F)) →
        ∀ p : ℕ, 0 < p → n ≤ p → IsZero (Hgroup X.ringCatSheaf ⊤ p F) := by
  induction n with
  | zero =>
      intro F hA hvan p hp _
      exact (isZero_hgroup_of_iso
        ((Functor.rightDerivedZeroIsoSelf (Scheme.Modules.pushforward f)).app F).symm
          (hA 0 p hp)).of_iso
        (Stacks.LeraySections.schemeCohomologyIsoOfVanishingHigherDirectImages f
          (fun q hq ↦ hvan q hq (Nat.zero_le q)) p)
  | succ n ih =>
      intro F hA hvan p hp hnp
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact ih F hA (fun q hq _ ↦ hvan q hq hq) p hp (Nat.zero_le p)
      set S : ShortComplex X.Modules :=
        ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
          (cokernel.condition _) with hSdef
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _)
          mono_f := inferInstance
          epi_g := inferInstance }
      have hinj : Injective S.X₂ := Injective.injective_under F
      have hvan₃ : ∀ q : ℕ, 0 < q → n ≤ q → IsZero (hdi f q S.X₃) := by
        intro q hq hnq
        obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
        exact isZero_hdi_X₃_of_isZero_hdi_X₁ f hS hinj q'
          (hvan (q' + 1 + 1) (by omega) (by omega))
      obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
      have hQ := ih S.X₃ (hasAcyclicDirectImages_X₃ f hS hinj hA) hvan₃ m (by omega) (by omega)
      exact isZero_hgroup_succ_of_isZero_hgroup hS hinj m hQ

/-- **Over an affine base the acyclicity hypothesis is automatic.** For `f` quasi-compact and
quasi-separated and `ℱ` quasi-coherent, every higher direct image `Rᑫf_*ℱ` is quasi-coherent
(`Stacks.AlgebraicGeometry.Tag01XJQcohInduction.higherDirectImage_isQuasicoherent`) and therefore
has no higher cohomology on an affine scheme
(`Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffine`).

This is the only place affineness of the base is used, and it carries no further hypothesis. -/
theorem hasAcyclicDirectImages_of_isAffine [IsAffine Y] [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] : HasAcyclicDirectImages f F := by
  intro q p hp
  have : (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj F).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.Tag01XJQcohInduction.higherDirectImage_isQuasicoherent f F (q : ℤ)
  exact isZero_hgroup_of_iso
    ((Stacks.DerivedIndexing.rightDerivedIso (Scheme.Modules.pushforward f) q).app F)
    (Stacks.Cohomology.AffineOpen.isZero_hgroup_of_isAffine Y
      (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj F) p hp)

/-- **Leray degeneration over an affine base.** For `Y` affine, `f` quasi-compact and
quasi-separated and `ℱ` quasi-coherent, a vanishing bound on the higher direct images is a
vanishing bound on the cohomology of `ℱ`. The input is in the `ℤ`-indexed `rightDerivedPlus`
spelling, which is the one the Tag 01XJ uniform vanishing produces. -/
theorem isZero_hgroup_of_isZero_rightDerivedPlus [IsAffine Y] [QuasiCompact f] [QuasiSeparated f]
    (n : ℕ) (F : X.Modules) [F.IsQuasicoherent]
    (hvan : ∀ q : ℕ, n ≤ q →
      IsZero (((Scheme.Modules.pushforward f).rightDerivedPlus (q : ℤ)).obj F))
    (p : ℕ) (hp : 0 < p) (hnp : n ≤ p) : IsZero (Hgroup X.ringCatSheaf ⊤ p F) :=
  isZero_hgroup_of_isZero_hdi f n F (hasAcyclicDirectImages_of_isAffine f F)
    (fun q _ hnq ↦
      (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff _ rfl F).1 (hvan q hnq)) p hp hnp


/-! ### `hbound` for Tag 0B5Q -/

section Proj

open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistFunctor

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] [IsNoetherianRing A]

/-- **`hbound` for [Stacks, Tag 0B5Q] assertion (3).** For `𝒜` a graded ring whose underlying
ring is Noetherian there is a degree `e` such that `Hᵖ(Proj 𝒜, ℱ(d))` vanishes for every `p > e`,
every quasi-coherent `ℱ` and **every** twist index `d`.

The bound is the one of
`Stacks.AlgebraicGeometry.Tag0B5QUniformTwistBound.exists_isZero_rightDerivedPlus_twist`, which is
uniform in the module and hence uniform over all twists at once; the degeneration above turns it
from a statement about higher direct images along `Proj 𝒜 ⟶ Spec (𝒜 0)` into one about cohomology
on `Proj 𝒜`. The base `Spec (𝒜 0)` is affine, which is the only reason the degeneration is
available. -/
theorem exists_isZero_hgroup_twist :
    ∃ e : ℕ, ∀ p : ℕ, e < p → ∀ F : SheafOfModules.{u} (projRingSheaf 𝒜),
      SheafOfModules.IsQuasicoherent (R := projRingSheaf 𝒜) F → ∀ d : ℤ,
        IsZero (Hgroup (projRingSheaf 𝒜) ⊤ p (twistSheafOfModules 𝒜 F d)) := by
  obtain ⟨n, hn⟩ :=
    Stacks.AlgebraicGeometry.Tag0B5QUniformTwistBound.exists_isZero_rightDerivedPlus_twist 𝒜
  have hqc := Stacks.AlgebraicGeometry.Tag0B5QUniformTwistBound.quasiCompact_toSpecZero 𝒜
  have hqs := Stacks.AlgebraicGeometry.Tag0B5QUniformTwistBound.quasiSeparated_toSpecZero 𝒜
  refine ⟨n.toNat, fun p hp F hF d ↦ ?_⟩
  exact @isZero_hgroup_of_isZero_rightDerivedPlus _ _ (Proj.toSpecZero 𝒜) _ hqc hqs n.toNat
    (twistSheafOfModules 𝒜 F d)
    (Stacks.AlgebraicGeometry.Tag0B5QUniformTwistBound.isQuasicoherent_twistSheafOfModules
      𝒜 F hF d)
    (fun q hq ↦ hn (q : ℤ) (le_trans (Int.self_le_toNat n) (by exact_mod_cast hq)) F hF d)
    p (by omega) hp.le

/-- **[Stacks, Tag 0B5Q] assertion (3) with `hbound` discharged.** The only hypothesis left is
`step`, assertion (1) of the same tag together with the short exactness and eventual acyclicity it
is used with; see the module docstring for what that still owes.

No attribute is attached: `step` is not proved, so there is no covering set for the label
`eventual_higher_cohomology_vanishing`. -/
theorem exists_isZero_hgroup_twist_of_step
    [EnoughInjectives (SheafOfModules.{u} (projRingSheaf 𝒜))]
    [HasDerivedCategory (SheafOfModules.{u} (projRingSheaf 𝒜))]
    [HasDerivedCategory AddCommGrpCat.{u}]
    (P : SheafOfModules.{u} (projRingSheaf 𝒜) → Prop)
    (hP : ∀ F : SheafOfModules.{u} (projRingSheaf 𝒜), P F →
      SheafOfModules.IsQuasicoherent (R := projRingSheaf 𝒜) F)
    (step : ∀ F : SheafOfModules.{u} (projRingSheaf 𝒜), P F →
      ∃ T : ShortComplex (SheafOfModules.{u} (projRingSheaf 𝒜)), T.X₃ = F ∧ P T.X₁ ∧
        (∀ d : ℤ, (T.map (twistFunctor 𝒜 d)).ShortExact) ∧
        ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d → ∀ m : ℕ, 0 < m →
          IsZero (Hgroup (projRingSheaf 𝒜) ⊤ m (twistSheafOfModules 𝒜 T.X₂ d)))
    (p : ℕ) (hp : 0 < p) (F : SheafOfModules.{u} (projRingSheaf 𝒜)) (hF : P F) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      IsZero (Hgroup (projRingSheaf 𝒜) ⊤ p (twistSheafOfModules 𝒜 F d)) := by
  obtain ⟨e, he⟩ := exists_isZero_hgroup_twist 𝒜
  exact exists_isZero_hgroup_twist_of_descending_devissage 𝒜 ⊤ P e
    (fun q hq G hG d ↦ he q hq G (hP G hG) d) step p hp F hF

end Proj

end Stacks.AlgebraicGeometry.LerayAffineBase

end
