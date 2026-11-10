module

public import StacksFrontier.AlgebraicGeometry.RelativeTwistRigidity.Basic

/-!
# Rigidity of the graded twists from compatibility with the homogeneous sections alone

`Stacks.AlgebraicGeometry.TwistRigidity.eq_id` and its relative form
`Stacks.AlgebraicGeometry.RelativeTwistRigidity.eq_id_res` force a family of endomorphisms
`α n : 𝒪(n) ⟶ 𝒪(n)` of the graded twists on `Proj 𝒜` to be the identity, from two hypotheses:
the family fixes the global sections attached to homogeneous elements, and it is
**multiplicative** — `Stacks.AlgebraicGeometry.TwistRigidity.IsMultiplicative`, an equation
about the canonical product of two *arbitrary* local sections of two twists.

This file weakens the second hypothesis to the only instances of it that the proofs of those
two theorems actually use: the product of an arbitrary local section with the restriction of a
homogeneous global section.

## Main definitions

* `Stacks.AlgebraicGeometry.TwistRigidityDS.IsDegreeSectionMultiplicative`: the family carries
  the product of a homogeneous section with an arbitrary local section to the product of that
  same homogeneous section with the image of the local section.

## Main results

* `Stacks.AlgebraicGeometry.TwistRigidityDS.isDegreeSectionMultiplicative_of_isMultiplicative`:
  the new hypothesis is implied by the old pair, so every consumer of the statements below is a
  consumer of the old ones as well.
* `Stacks.AlgebraicGeometry.TwistRigidityDS.eq_id_of_fixesDegreeSections`: **absolute rigidity
  under the weakened hypothesis.**
* `Stacks.AlgebraicGeometry.TwistRigidityDS.fixesDegreeSections`: generation upgrades the
  relative fixing hypothesis to the absolute one, under the weakened hypothesis.
* `Stacks.AlgebraicGeometry.TwistRigidityDS.eq_id`: **relative rigidity relative to a graded
  ring homomorphism, under the weakened hypothesis.**
* `Stacks.AlgebraicGeometry.TwistRigidityDS.eq_id_res`: **relative rigidity for a nested pair of
  affine opens of the base of a quasi-coherent graded algebra, under the weakened hypothesis** —
  the drop-in replacement for `Stacks.AlgebraicGeometry.RelativeTwistRigidity.eq_id_res`.

## Why the weakening is the point, and not a cosmetic generalisation

The consumer these statements exist for is
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle`, the one named gap the glued
twists of Tag 01NR are conditional on. Its intended proof applies relative rigidity to a
composite of Tag 01NO's twist comparisons, and the hypothesis it cannot supply is
multiplicativity of that composite.

**In the single degree `n = 1` the hypothesis can be dropped outright rather than weakened**, and
that is the statement that consumer should use: `Stacks.AlgebraicGeometry.TwistRigidityDegreeOne`
proves relative rigidity in degree one with **no** multiplicativity hypothesis at all, at the cost
of asking that the graded ring have a nonvanishing degree-one element at each point of its `Proj`
— which holds for a ring generated in degree one, so for the symmetric algebra whose relative
`Proj` is a projective bundle. The file below remains the statement to use in any other degree,
where no free generator of `𝒪(n)` is available and some multiplicative input is unavoidable.

That comparison, `Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistIso`, is a
composite of six factors: five are components of the pseudofunctoriality isomorphisms of the
inverse image (`AlgebraicGeometry.Scheme.Modules.pullbackComp`, `pullbackCongr`, `pullbackId`)
and one is the functor image of Tag 01MY's twist map. Multiplicativity in the old sense is an
equation about the *sheafified tensor product* of two twists, so for each of the five structural
factors it asks that the factor commute with the Tag 01CD comparison between the inverse image
of a tensor product and the tensor product of the inverse images. Nothing in this repository
supplies that: `StacksFrontier/AlgebraicGeometry/TwistTensor/Basic.lean` records, for the
companion problem of restriction to an open, that `CategoryTheory.SheafOfModules.overFunctor` is
not known to be monoidal, and the same is true of the inverse image here.

Under the hypothesis of this file no tensor product occurs. For a fixed homogeneous `c` of
degree `K`, the map `t ↦ c · t` is a single morphism `𝒪(n) ⟶ 𝒪(K + n)` of sheaves of modules,
and the hypothesis is the commutation of `α` with it — a naturality square. The five structural
factors satisfy it **by naturality of the natural transformation they are components of**, with
nothing monoidal required, and the remaining factor is Tag 01MY's twist map, whose
section-level multiplicativity is
`Stacks.AlgebraicGeometry.ProjTwistTheta.twistPushforwardMap_mul_val` — the fibre comparison is
a ring homomorphism. So the weakened hypothesis is reachable by the route the strong one blocks.

## Implementation notes

**Where the two hypotheses are used in the existing proofs, declaration by declaration.**
`Stacks.AlgebraicGeometry.TwistRigidity.app_eq_self_of_isFraction_nonneg` invokes
`IsMultiplicative` exactly once, at `(degreeSectionOn 𝒜 K hc V, t)`, and immediately rewrites the
first component of its right-hand side with
`Stacks.AlgebraicGeometry.TwistRigidity.app_degreeSectionOn`.
`Stacks.AlgebraicGeometry.RelativeTwistRigidity.app_degreeSection_apply` invokes it exactly once,
at `(degreeSection 𝒜 k a, degreeSection 𝒜 0 ⟨g, hg⟩)`. Those are the only two occurrences in the
two files, so a hypothesis covering a homogeneous section against an arbitrary section covers both
— and in the second case the homogeneous section has to be the *left* factor, which fixes the
orientation of `IsDegreeSectionMultiplicative`.

**The orientation costs one `mul_comm` and saves one hypothesis.** With the homogeneous section on
the left, the product of `c` with `a` is `c * a` while
`Stacks.AlgebraicGeometry.RelativeTwistRigidity.Generates` produces `a * ψ d`; the two are
identified by `mul_comm` inside `app_degreeSection_apply`. In exchange, the degree-zero
multiplier's own homogeneous section no longer has to be assumed fixed:
`fixesDegreeSections_of_forall_point` asks for both
`α 0 (degreeSection 𝒜 0 g) = degreeSection 𝒜 0 g` and
`α k (degreeSection 𝒜 k (a * g)) = degreeSection 𝒜 k (a * g)`, and the version here asks only for
the second, because the hypothesis already keeps the left factor untouched.

The degree arithmetic is routed through the free integer index exactly as in the existing rigidity
files: `Stacks.AlgebraicGeometry.RelativeTwistRigidity.app_eq_self_of_values_mkOne'` takes
`(N : ℤ) = m` as a hypothesis and substitutes into `m`, rather than rewriting the index of a
dependent type.

`Stacks.AlgebraicGeometry.TwistRigidity` and
`Stacks.AlgebraicGeometry.RelativeTwistRigidity` are **not** opened, and every reference to them
is qualified: the declarations below carry the same names as the ones they weaken, and opening
the namespaces would make each call site ambiguous between the two.

## References

* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)

## What is not done here

The commutation of Tag 01NO's twist comparison with multiplication by a homogeneous section is
**not** proved: this file supplies the criterion that makes that statement sufficient, not the
statement. `Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle` is therefore still
open, no `Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` is constructed, and no project
tag is attached to any declaration below — nothing here is a label of any tag.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjTwists
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.TwistRigidityDS

universe u u' w w' v

variable {R : Type u} {σ : Type w} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local implicit_reducible]
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- **The weakened multiplicativity hypothesis.** The family carries the canonical product of
the restriction of a homogeneous global section with an arbitrary local section of a twist to
the product of that same homogeneous section with the image of the local section.

Compared with `Stacks.AlgebraicGeometry.TwistRigidity.IsMultiplicative` the left factor is no
longer arbitrary, and the family is not applied to it on the right-hand side — which is how the
existing proofs use multiplicativity, once
`Stacks.AlgebraicGeometry.TwistRigidity.FixesDegreeSections` has been used to remove it. -/
public def IsDegreeSectionMultiplicative
    (α : ∀ n : ℤ, twistingSheaf 𝒜 n ⟶ twistingSheaf 𝒜 n) : Prop :=
  ∀ (K : ℕ) {c : R} (hc : c ∈ 𝒜 K) (n : ℤ) (V : Opens (ProjectiveSpectrum.top 𝒜))
    (t : (twistingSheaf 𝒜 n).val.obj (op V)),
    (α ((K : ℤ) + n)).val.app (op V)
        (absoluteTwistProduct 𝒜 (K : ℤ) n V (TwistRigidity.degreeSectionOn 𝒜 K hc V) t) =
      absoluteTwistProduct 𝒜 (K : ℤ) n V (TwistRigidity.degreeSectionOn 𝒜 K hc V)
        ((α n).val.app (op V) t)

variable {α : ∀ n : ℤ, twistingSheaf 𝒜 n ⟶ twistingSheaf 𝒜 n}

/-- **The weakened hypothesis is implied by the original pair.** So the rigidity statements below
are strictly more general than the ones they replace, and nothing is lost by a consumer that
switches to them. -/
public theorem isDegreeSectionMultiplicative_of_isMultiplicative
    (hmul : TwistRigidity.IsMultiplicative α)
    (hfix : TwistRigidity.FixesDegreeSections α) :
    IsDegreeSectionMultiplicative α := by
  intro K c hc n V t
  have h := hmul (K : ℤ) n V (TwistRigidity.degreeSectionOn 𝒜 K hc V) t
  rwa [TwistRigidity.app_degreeSectionOn hfix K hc V] at h

/-! ### The absolute statement -/

/-- **The cancellation step at a point.** If `α` fixes the product of the homogeneous section
of `c` with `t`, then it fixes the value of `t` at every point where `c` does not vanish. -/
private theorem app_apply_eq_of_absoluteTwistProduct_fixed (hmul : IsDegreeSectionMultiplicative α)
    {K : ℕ} {c : R} (hc : c ∈ 𝒜 K) (n : ℤ) (V : Opens (ProjectiveSpectrum.top 𝒜))
    (t : (twistingSheaf 𝒜 n).val.obj (op V))
    (hfixed : (α ((K : ℤ) + n)).val.app (op V)
        (absoluteTwistProduct 𝒜 (K : ℤ) n V (TwistRigidity.degreeSectionOn 𝒜 K hc V) t) =
      absoluteTwistProduct 𝒜 (K : ℤ) n V (TwistRigidity.degreeSectionOn 𝒜 K hc V) t)
    (y : V) (hy : c ∉ y.1.asHomogeneousIdeal) :
    ((α n).val.app (op V) t).1 y = t.1 y := by
  refine TwistRigidity.eq_of_mkOne_mul_eq _ hy ?_
  rw [← TwistRigidity.degreeSectionOn_apply 𝒜 K hc V y]
  calc (TwistRigidity.degreeSectionOn 𝒜 K hc V).1 y * ((α n).val.app (op V) t).1 y
      = (absoluteTwistProduct 𝒜 (K : ℤ) n V (TwistRigidity.degreeSectionOn 𝒜 K hc V)
          ((α n).val.app (op V) t)).1 y :=
          (TwistRigidity.absoluteTwistProduct_apply 𝒜 (K : ℤ) n V
            (TwistRigidity.degreeSectionOn 𝒜 K hc V) _ y).symm
    _ = ((α ((K : ℤ) + n)).val.app (op V)
          (absoluteTwistProduct 𝒜 (K : ℤ) n V
            (TwistRigidity.degreeSectionOn 𝒜 K hc V) t)).1 y :=
          (TwistRigidity.twist_val_congr 𝒜 (hmul K hc n V t) y).symm
    _ = (absoluteTwistProduct 𝒜 (K : ℤ) n V
          (TwistRigidity.degreeSectionOn 𝒜 K hc V) t).1 y :=
          TwistRigidity.twist_val_congr 𝒜 hfixed y
    _ = (TwistRigidity.degreeSectionOn 𝒜 K hc V).1 y * t.1 y :=
          TwistRigidity.absoluteTwistProduct_apply 𝒜 (K : ℤ) n V
            (TwistRigidity.degreeSectionOn 𝒜 K hc V) t y

/-- **The generation-and-cancellation step, nonnegative case, under the weakened hypothesis.**
A section of `𝒪(n)` given on the whole of its open by a single homogeneous fraction `β / c`
whose numerator has nonnegative degree is fixed.

This is `Stacks.AlgebraicGeometry.TwistRigidity.app_eq_self_of_isFraction_nonneg` with the
hypothesis weakened; the only change in the proof is that the equation supplied by the
hypothesis already has its left factor untouched, so the rewrite by
`Stacks.AlgebraicGeometry.TwistRigidity.app_degreeSectionOn` is no longer needed. -/
public theorem app_eq_self_of_isFraction_nonneg (hmul : IsDegreeSectionMultiplicative α)
    (hfix : TwistRigidity.FixesDegreeSections α) (n : ℤ)
    (V : Opens (ProjectiveSpectrum.top 𝒜)) (t : (twistingSheaf 𝒜 n).val.obj (op V))
    {K N : ℕ} {β c : R} (hN : (N : ℤ) = (K : ℤ) + n) (hβ : β ∈ 𝒜 N) (hc : c ∈ 𝒜 K)
    (hnv : ∀ y : V, c ∉ y.1.asHomogeneousIdeal)
    (hval : ∀ y : V, t.1 y = LocalizedModule.mk β ⟨c, hnv y⟩) :
    (α n).val.app (op V) t = t := by
  have hfixed : (α ((K : ℤ) + n)).val.app (op V)
      (absoluteTwistProduct 𝒜 (K : ℤ) n V (TwistRigidity.degreeSectionOn 𝒜 K hc V) t) =
      absoluteTwistProduct 𝒜 (K : ℤ) n V (TwistRigidity.degreeSectionOn 𝒜 K hc V) t :=
    TwistRigidity.app_eq_self_of_values_mkOne hfix hN hβ V
      (absoluteTwistProduct 𝒜 (K : ℤ) n V (TwistRigidity.degreeSectionOn 𝒜 K hc V) t)
      (TwistRigidity.degreeSectionOn_mul_apply 𝒜 K hc n V t hnv hval)
  exact Subtype.ext (funext fun y =>
    app_apply_eq_of_absoluteTwistProduct_fixed hmul hc n V t hfixed y (hnv y))

/-- **The generation-and-cancellation step, under the weakened hypothesis.** If the numerator's
degree is negative the numerator lies in the zero submodule and the section vanishes; otherwise
this is `app_eq_self_of_isFraction_nonneg`. -/
public theorem app_eq_self_of_isFraction (hmul : IsDegreeSectionMultiplicative α)
    (hfix : TwistRigidity.FixesDegreeSections α) (n : ℤ)
    (V : Opens (ProjectiveSpectrum.top 𝒜)) (t : (twistingSheaf 𝒜 n).val.obj (op V))
    {K : ℕ} {β c : R} (hβ : β ∈ twistGrading (S := R) 𝒜 n (K : ℤ)) (hc : c ∈ 𝒜 K)
    (hnv : ∀ y : V, c ∉ y.1.asHomogeneousIdeal)
    (hval : ∀ y : V, t.1 y = LocalizedModule.mk β ⟨c, hnv y⟩) :
    (α n).val.app (op V) t = t := by
  have hβg : β ∈ integerGrading (S := R) 𝒜 ((K : ℤ) + n) := hβ
  rcases le_or_gt 0 ((K : ℤ) + n) with hKn | hKn
  · have hβ' : β ∈ 𝒜 ((K : ℤ) + n).toNat := by simpa [integerGrading, hKn] using hβg
    exact app_eq_self_of_isFraction_nonneg hmul hfix n V t
      (Int.toNat_of_nonneg hKn) hβ' hc hnv hval
  · have hβ0 : β = 0 := by
      have hb : β ∈ (⊥ : Submodule ℤ R) := by
        simpa [integerGrading, not_le.mpr hKn] using hβg
      simpa using hb
    have ht0 : t = 0 := by
      refine Subtype.ext (funext fun y => ?_)
      have h1 : t.1 y = 0 := by
        rw [hval y, hβ0]
        simp
      exact h1
    rw [ht0, map_zero]

/-- **Rigidity on sections, under the weakened hypothesis.** -/
public theorem app_eq_self (hmul : IsDegreeSectionMultiplicative α)
    (hfix : TwistRigidity.FixesDegreeSections α) (n : ℤ)
    (V : Opens (ProjectiveSpectrum.top 𝒜)) (t : (twistingSheaf 𝒜 n).val.obj (op V)) :
    (α n).val.app (op V) t = t := by
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨V', hxV', i, K, β, c, hβ, hc, hnv, heq⟩ := t.2 x
  have hval : ∀ y : V',
      ((twistingSheaf 𝒜 n).val.map i.op t).1 y = LocalizedModule.mk β ⟨c, hnv y⟩ := heq
  have hlocal := app_eq_self_of_isFraction hmul hfix n V'
    ((twistingSheaf 𝒜 n).val.map i.op t) hβ hc hnv hval
  have hnat : (α n).val.app (op V') ((twistingSheaf 𝒜 n).val.map i.op t) =
      (twistingSheaf 𝒜 n).val.map i.op ((α n).val.app (op V) t) :=
    PresheafOfModules.naturality_apply (α n).val i.op t
  calc ((α n).val.app (op V) t).1 x
      = ((twistingSheaf 𝒜 n).val.map i.op
          ((α n).val.app (op V) t)).1 ⟨x.1, hxV'⟩ := rfl
    _ = ((α n).val.app (op V') ((twistingSheaf 𝒜 n).val.map i.op t)).1
          ⟨x.1, hxV'⟩ := TwistRigidity.twist_val_congr 𝒜 hnat.symm _
    _ = ((twistingSheaf 𝒜 n).val.map i.op t).1 ⟨x.1, hxV'⟩ :=
          TwistRigidity.twist_val_congr 𝒜 hlocal _
    _ = t.1 x := rfl

/-- **Absolute rigidity, under the weakened hypothesis.** A family of endomorphisms of the twists
on `Proj 𝒜` which commutes with multiplication by the homogeneous sections and fixes the global
section attached to every homogeneous element is the identity in every integer degree. -/
public theorem eq_id_of_fixesDegreeSections (hmul : IsDegreeSectionMultiplicative α)
    (hfix : TwistRigidity.FixesDegreeSections α) (n : ℤ) : α n = 𝟙 (twistingSheaf 𝒜 n) :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun t => app_eq_self hmul hfix n V.unop t))

/-! ### The relative statement -/

/-- **The cancellation step of relative rigidity, under the weakened hypothesis.** At a point
where a degree-zero element `g` does not vanish, the family fixes the value of the homogeneous
section of `a` as soon as it fixes the homogeneous section of `a * g`.

The original `Stacks.AlgebraicGeometry.RelativeTwistRigidity.app_degreeSection_apply` also assumes
the homogeneous section of `g` to be fixed. Here it need not be: the hypothesis keeps the left
factor of the product untouched, and `g` is the left factor. -/
public theorem app_degreeSection_apply (hmul : IsDegreeSectionMultiplicative α) (k : ℕ)
    (a : 𝒜 k) {g : R} (hg : g ∈ 𝒜 0) (hag : (a : R) * g ∈ 𝒜 k)
    (hfixag : (α (k : ℤ)).val.app (op ⊤) (degreeSection 𝒜 k ⟨(a : R) * g, hag⟩)
      = degreeSection 𝒜 k ⟨(a : R) * g, hag⟩)
    (x : (⊤ : Opens (ProjectiveSpectrum.top 𝒜)))
    (hx : g ∉ x.1.asHomogeneousIdeal) :
    ((α (k : ℤ)).val.app (op ⊤) (degreeSection 𝒜 k a)).1 x = (degreeSection 𝒜 k a).1 x := by
  have hs : ∀ y : (⊤ : Opens (ProjectiveSpectrum.top 𝒜)),
      (absoluteTwistProduct 𝒜 ((0 : ℕ) : ℤ) (k : ℤ) ⊤
        (TwistRigidity.degreeSectionOn 𝒜 0 hg ⊤) (degreeSection 𝒜 k a)).1 y =
      LocalizedModule.mk ((a : R) * g)
        (1 : y.1.asHomogeneousIdeal.toIdeal.primeCompl) := by
    intro y
    refine Eq.trans (TwistRigidity.absoluteTwistProduct_apply 𝒜 ((0 : ℕ) : ℤ) (k : ℤ) ⊤ _ _ y) ?_
    rw [TwistRigidity.degreeSectionOn_apply 𝒜 0 hg ⊤ y,
      degreeSection_apply 𝒜 k a ⟨y.1, trivial⟩,
      RelativeTwistRigidity.mkOne_mul_mkOne, mul_comm g (a : R)]
  have h1 := RelativeTwistRigidity.app_eq_self_of_values_mkOne' (α := α)
    (m := ((0 : ℕ) : ℤ) + (k : ℤ)) (N := k) (by simp) hag hfixag ⊤ _ hs
  exact app_apply_eq_of_absoluteTwistProduct_fixed hmul hg (k : ℤ) ⊤ _ h1 x hx

/-- **The rigidity criterion, under the weakened hypothesis.** The family fixes every homogeneous
global section as soon as, at every point and for every homogeneous `a`, there is a degree-zero
`g` nonvanishing there such that the homogeneous section of `a * g` is fixed. -/
public theorem fixesDegreeSections_of_forall_point (hmul : IsDegreeSectionMultiplicative α)
    (hgen : ∀ (k : ℕ) (a : 𝒜 k) (x : ProjectiveSpectrum 𝒜),
      ∃ (g : R) (_hg : g ∈ 𝒜 0) (hag : (a : R) * g ∈ 𝒜 k), g ∉ x.asHomogeneousIdeal ∧
        (α (k : ℤ)).val.app (op ⊤) (degreeSection 𝒜 k ⟨(a : R) * g, hag⟩) =
          degreeSection 𝒜 k ⟨(a : R) * g, hag⟩) :
    TwistRigidity.FixesDegreeSections α := by
  refine RelativeTwistRigidity.fixesDegreeSections_of_apply fun k a x => ?_
  obtain ⟨g, hg, hag, hnv, hfixag⟩ := hgen k a x.1
  exact app_degreeSection_apply hmul k a hg hag hfixag x hnv

section Res

variable {R' : Type u'} {σ' : Type w'} [CommRing R'] [SetLike σ' R'] [AddSubgroupClass σ' R']
  {ℬ : ℕ → σ'} [GradedRing ℬ]

omit [AddSubgroupClass σ' R'] [GradedRing ℬ] in
/-- **Relative rigidity on the homogeneous sections, under the weakened hypothesis.** Generation
plus the relative fixing hypothesis force the absolute one. -/
public theorem fixesDegreeSections {ψ : ℬ →+*ᵍ 𝒜} (hmul : IsDegreeSectionMultiplicative α)
    (hgen : RelativeTwistRigidity.Generates ψ)
    (hfix : RelativeTwistRigidity.FixesResDegreeSections ψ α) :
    TwistRigidity.FixesDegreeSections α := by
  refine fixesDegreeSections_of_forall_point hmul fun k a x => ?_
  obtain ⟨d, c, hnv, heq⟩ := hgen k a x
  have hag : (a : R) * ψ (d : R') ∈ 𝒜 k := by
    rw [heq]
    exact ψ.map_mem c.2
  exact ⟨ψ (d : R'), ψ.map_mem d.2, hag, hnv,
    RelativeTwistRigidity.fixes_of_eq_res hfix k c ⟨(a : R) * ψ (d : R'), hag⟩ heq⟩

omit [AddSubgroupClass σ' R'] [GradedRing ℬ] in
/-- **Relative rigidity, under the weakened hypothesis.** A family of endomorphisms of the twists
on `Proj 𝒜` which commutes with multiplication by the homogeneous sections and fixes the
homogeneous global sections attached to the images of a graded ring homomorphism `ψ` is the
identity in every integer degree, provided `ψ` generates `𝒜` pointwise. -/
public theorem eq_id {ψ : ℬ →+*ᵍ 𝒜} (hmul : IsDegreeSectionMultiplicative α)
    (hgen : RelativeTwistRigidity.Generates ψ)
    (hfix : RelativeTwistRigidity.FixesResDegreeSections ψ α) (n : ℤ) :
    α n = 𝟙 (twistingSheaf 𝒜 n) :=
  eq_id_of_fixesDegreeSections hmul (fixesDegreeSections hmul hgen hfix) n

end Res

/-! ### The geometric instance: a nested pair of affine opens of the base -/

section Nested

variable {X : Scheme.{v}} (A : SheafGradedAlgebra X) (U V : X.Opens) (h : U ≤ V)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V)

include hU hV

/-- **Relative rigidity for a nested pair of affine opens, under the weakened hypothesis.** The
drop-in replacement for `Stacks.AlgebraicGeometry.RelativeTwistRigidity.eq_id_res`: a family of
endomorphisms of the twists on `Proj Γ(U, A)` which commutes with multiplication by the
homogeneous sections and fixes the global sections attached to the restrictions of the
homogeneous elements over a larger affine open is the identity in every integer degree. -/
public theorem eq_id_res
    {α : ∀ n : ℤ, twistingSheaf (A.grading U) n ⟶ twistingSheaf (A.grading U) n}
    (hmul : IsDegreeSectionMultiplicative α)
    (hfix : RelativeTwistRigidity.FixesResDegreeSections (A.res h) α) (n : ℤ) :
    α n = 𝟙 (twistingSheaf (A.grading U) n) :=
  eq_id hmul (RelativeTwistRigidity.generates_res A U V h hU hV) hfix n

end Nested

end Stacks.AlgebraicGeometry.TwistRigidityDS

end

