module

public import StacksFrontier.AlgebraicGeometry.SectionProduct.PullbackUnitComparisonSection
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplanePushforwardCohomology
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.HyperplaneRestrictionCanonical
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.PullbackTwistRegroupingFamily
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The hyperplane restriction data of [Stacks, Tag 08A7]

`AlgebraicGeometry.HyperplaneRestrictionPackage` in
`StacksFrontier/AlgebraicGeometry/Variety/Projective/RegularitySectionMultiplication.lean` is the
hypothesis of this repository's [Stacks, Tag 08A7]: for a coherent `ℱ` on `ℙ^{n+1}_k` it bundles
the hyperplane, its coherent restriction `𝒢`, the section `s` of `𝒪(1)` cutting it out, the
restriction arrows `ℱ(d) ⟶ j_*(𝒢(d))`, the twisted restriction sequences, the degree-zero
cohomology comparison, and the lifting of degree-one forms off the hyperplane.

This file produces that data over an infinite field, with **no hypothesis**: every clause of the
package, `liftSection` included, is proved. Its one geometric input — that restriction of
degree-one forms to a hyperplane is surjective on global sections of `𝒪(1)` — is
`AlgebraicGeometry.surjective_restriction_zeroScheme`, and
`AlgebraicGeometry.exists_restrictionSequences_pullbackRes` hands it out for the hyperplane it
builds.

## Main results

* `AlgebraicGeometry.exists_hyperplaneRestrictionData`: **the hyperplane restriction data with
  all ten of the package's clauses except `liftSection`**, over an infinite field.
* `AlgebraicGeometry.LiftsSectionAlong`: the `liftSection` clause, stated for given data.
* `AlgebraicGeometry.nonempty_hyperplaneRestrictionPackage_of_liftSection`: the data together
  with `LiftsSectionAlong` for it **is** a package.
* `AlgebraicGeometry.liftsSectionAlong_of_pushforward_square`: **that clause, for the canonical
  comparison, reduced to a square of sheaves** — restriction to the hyperplane intertwines
  multiplication by a degree-one form upstairs with multiplication by its restriction, read in
  the direct image. No cohomology is left in the hypothesis.
* `AlgebraicGeometry.nonempty_hyperplaneRestrictionPackage_of_pushforward_square`: the two
  combined — hyperplane restriction data over a closed immersion over `Spec k`, plus that square,
  is a package.
* `AlgebraicGeometry.pushforward_square_pullbackTwistUnitRes`: **that square for the canonical
  restriction arrows**, from the corresponding square upstairs of the hyperplane, by naturality of
  the unit of `j^* ⊣ j_*`.
* `AlgebraicGeometry.nonempty_hyperplaneRestrictionPackage_of_liftSectionHom` and
  `AlgebraicGeometry.nonempty_hyperplaneRestrictionPackage_of_surjective_restriction`: the
  package over an infinite field, on the single hypothesis that degree-one forms restrict onto
  **every** hyperplane — in the `sectionHom` form and in the geometric form respectively. The two
  readings of that hypothesis are identified by
  `AlgebraicGeometry.exists_sectionHom_eq_of_surjective_restriction`.
* `AlgebraicGeometry.nonempty_hyperplaneRestrictionPackage`: **the package over an infinite field,
  with no hypothesis at all.** The hypothesis above is not needed for every hyperplane, only for
  the one the data is built on, and there it is proved.

## The mathematics

Apart from the reduction of `liftSection` to a square of sheaves there is none: this is the
assembly step. The pieces are

* `AlgebraicGeometry.exists_restrictionSequences`, which supplies `G`, `isCoherent`, `j`,
  `isAffineHom`, `s` and — through `AlgebraicGeometry.HasMulRestrictionSequences` — the
  sequences `0 ⟶ ℱ(d) ⟶ ℱ(d+1) ⟶ j_*(𝒢(d+1)) ⟶ 0` whose first arrow is multiplication by `s`
  on the nose, which is the shape `comp_res` and `shortExact` ask for;
* `AlgebraicGeometry.projectiveHPushforwardIso` for `compare`, which needs `j` to be a closed
  immersion over `Spec k` — both recorded by `exists_restrictionSequences`.

The `res` family is the second arrows of those sequences, chosen with `choose` and reindexed.
`HasMulRestrictionSequences` indexes its arrow by the source of the multiplication, so the arrow
at `c` goes out of `ℱ(c+1)`, while the package indexes `res` by the source of the arrow itself;
`c + 1` is not syntactically `d`, so the two indexings differ by a transport, which `shiftedRes`
carries. Everything said about it is proved by substituting the index equation, after which the
transports are identities — that is why `shiftedRes_shortExact` and `shiftedRes_shortExact'` take
the index and the equation as separate arguments instead of writing `d - 1` inline, and why the
two index equations are lemmas rather than inline tactic proofs: a `ring` proof placed in an
`eqToHom` argument is a term the kernel rechecks at every use site, and inlining it there
overran the elaborator's heartbeat limit. `shortExact'` is the same data read at its middle
term, which is how the package asks for it.

## Why `liftSection` is not hypothesised on its own

`LiftsSectionAlong` is a statement about a **particular** `res` and `compare`, and it must be:
`res` is determined by the restriction sequences only up to an automorphism of each target, and
such a change — `res (d₀+1)` replaced by `res (d₀+1) ≫ (2 • 𝟙)`, say — leaves `comp_res` and
`shortExact` intact while destroying the intertwining with multiplication at `d₀` and at `d₀+1`
in incompatible ways. So `LiftsSectionAlong` quantified over every `res` with short exact
sequences is false, and a reduction of [Stacks, Tag 08A7] to such a hypothesis would be vacuous.
The clause is therefore stated for the data that `exists_hyperplaneRestrictionData` produces,
and `AlgebraicGeometry.liftsSectionAlong_of_pushforward_square` likewise takes as hypothesis the
square for the `res` it is handed.

## How `liftSection` is proved

Restriction of degree-one forms to a hyperplane is onto on global sections of `𝒪(1)`:
`AlgebraicGeometry.surjective_restriction_zeroScheme`, for the zero scheme of a section of `𝒪(1)`
presented by a nonzero degree-one form and for *any* identification of that zero scheme with
`ℙᵐ_k` and of the twists along it. It is the algebraic statement — along a graded surjection the
canonical section of `a` restricts to the canonical section of `ψ a`, [Stacks, Tag 01MY] part (1),
and over a field every section of `𝒪(1)` is the section of a form — transported across the
comparison of models, `Stacks.ProjectiveSpace.restrictsOnto_projMap` and
`AlgebraicGeometry.RestrictsOnto` being the two ingredients.

The hypothesis of
`AlgebraicGeometry.nonempty_hyperplaneRestrictionPackage_of_surjective_restriction` asks for more:
surjectivity for an *arbitrary* closed immersion `j : ℙⁿ_k ⟶ ℙ^{n+1}_k` over `Spec k` with
`j^*𝒪(1) ≅ 𝒪(1)`, rather than for the hyperplane of a form. It is true (the image of the
restriction map generates `𝒪(1)`, and a proper subspace of the degree-one forms has a common zero
in `Proj`), but only the hyperplane case is used.

* *The canonical `res`.* `AlgebraicGeometry.pullbackTwistUnitRes`
  (`StacksFrontier/AlgebraicGeometry/Variety/Projective/HyperplaneRestrictionCanonical.lean`) is
  `res d = unit_{ℱ(d)} ≫ j_*(c d)` with `c d` the comparison of [Stacks, Tag 01CD] followed by an
  identification of the twists — a definition, given by one formula in every degree, so that 08A7
  has something to compare across `d`. `AlgebraicGeometry.exists_restrictionSequences_pullbackRes`
  (same file) produces the hyperplane, the section and short exactness of
  `0 ⟶ ℱ(d) ⟶ ℱ(d+1) ⟶ j_*(𝒢(d+1)) ⟶ 0` for it, with `twistSectionMul` as first arrow on the
  nose. No regrouping coherence is needed, and no isomorphism has to be absorbed into the
  *second* arrow, which would destroy canonicity: all three inputs of [Stacks, Tag 08A0] hold for
  `twistSectionMul n S ℱ s d` itself
  (`AlgebraicGeometry.mono_twistSectionMul_of_nonvanishing`,
  `AlgebraicGeometry.twistSectionMul_comp_hyperplaneUnit`,
  `AlgebraicGeometry.isIso_unit_app_cokernel_twistSectionMul`).
* *The twist identifications over all of `ℤ`.*
  `Stacks.AlgebraicGeometry.PullbackTwistRegrouping.exists_regroupingFamily`
  (`StacksFrontier/AlgebraicGeometry/Variety/Projective/PullbackTwistRegroupingFamily.lean`)
  produces
  a family `θ_d : j^*𝒪(d) ≅ 𝒪(d)` satisfying the regrouping square of
  `…PullbackTwistSectionMul.pullback_twistSectionMul` in **every** integer degree. The downward
  step needs `- ⊗ 𝒪(1)` to be full, which
  `…PullbackTwistRegrouping.whiskerRight_eq_tensorRightModules` supplies by identifying right
  whiskering with `Stacks.SheafOfModules.TensorPower.tensorRightFunctor`, an equivalence for an
  invertible module.
* *The square, and the passage from sheaves to `H⁰`.*
  `AlgebraicGeometry.pushforward_square_pullbackTwistUnitRes` turns the pullback square into the
  square for `res` by naturality of the unit — which is the step that needs `res` to be a formula
  — and `AlgebraicGeometry.liftsSectionAlong_of_pushforward_square` removes the cohomology.
  `AlgebraicGeometry.nonempty_hyperplaneRestrictionPackage_of_liftSectionHom` is the whole
  assembly, on the lifting hypothesis in its `sectionHom` form; the geometric reading of that
  hypothesis is `…of_surjective_restriction` above, through
  `Stacks.PullbackUnitComparisonSection.eval_top_of_sectionHom_eq`.

The descent to an arbitrary field is
`AlgebraicGeometry.span_mulSections_eq_top_of_isMRegular_of_infinite`, which takes the
infinite-field conclusion as a hypothesis; its composition with the package of this file is
`AlgebraicGeometry.span_mulSections_eq_top_of_isMRegular_field`.

## References

* [Stacks Project, Tag 08A7](https://stacks.math.columbia.edu/tag/08A7)
* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 08A4](https://stacks.math.columbia.edu/tag/08A4)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 01XU](https://stacks.math.columbia.edu/tag/01XU)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication (sectionHom twistSectionMul)

universe u

namespace AlgebraicGeometry

/-- **The `liftSection` clause of `AlgebraicGeometry.HyperplaneRestrictionPackage`, stated for
given hyperplane data.** Every degree-one form `σ` on `ℙⁿ_k` is the restriction of a degree-one
form `σ'` on `ℙ^{n+1}_k`, compatibly with multiplication on `H⁰`: restricting and then
multiplying by `σ` is multiplying by `σ'` and then restricting.

In the source this clause is "see the proof of Lemma 33.35.2". It is a statement about the given
`res` and `compare`, not about the hyperplane alone — see the module documentation. -/
def LiftsSectionAlong (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing (n + 1) (.of k)).Modules)
    (G : (projectiveSpaceOverRing n (.of k)).Modules)
    {j : projectiveSpaceOverRing n (.of k) ⟶ projectiveSpaceOverRing (n + 1) (.of k)}
    (res : ∀ d : ℤ, projectiveTwist (n + 1) F d ⟶
      (Scheme.Modules.pushforward j).obj (projectiveTwist n G d))
    (compare : ∀ d : ℤ, projectiveH k n (projectiveTwist n G d) 0 ≅
      projectiveH k (n + 1) ((Scheme.Modules.pushforward j).obj (projectiveTwist n G d)) 0) :
    Prop :=
  ∀ σ : (twistOver n (Spec (.of k)) 1).sections,
    ∃ σ' : (twistOver (n + 1) (Spec (.of k)) 1).sections, ∀ d : ℤ,
      mulSection k (n + 1) F σ' d ≫ projectiveHZeroMap k (n + 1) (res (d + 1))
        = projectiveHZeroMap k (n + 1) (res d) ≫ (compare d).inv ≫
            mulSection k n G σ d ≫ (compare (d + 1)).hom

/-! ### The clause, reduced to a square of sheaves -/

/-- **`AlgebraicGeometry.LiftsSectionAlong` for the canonical comparison holds as soon as the
corresponding square of *sheaves* commutes**: restricting to the hyperplane intertwines
multiplication by `σ'` upstairs with multiplication by `σ` downstairs, read in the direct image.

This removes the cohomological layer from the `liftSection` clause of the package. The
`compare` family is the canonical one, `AlgebraicGeometry.projectiveHPushforwardIso`, which is
natural in the module
(`AlgebraicGeometry.cohomologyOverFieldMap_pushforward_eq_conj`); the conjugation
`(compare d).inv ≫ … ≫ (compare (d+1)).hom` in `AlgebraicGeometry.LiftsSectionAlong` is therefore
exactly `H⁰` of `j_*` of multiplication by `σ`, and the clause says no more than that `H⁰` of the
square below commutes. The hypothesis is stated for the **given** `res`, not for an arbitrary one:
see the module documentation for why no quantified form of it is available. -/
theorem liftsSectionAlong_of_pushforward_square (k : Type u) [Field k] (n : ℕ)
    (F : (projectiveSpaceOverRing (n + 1) (.of k)).Modules)
    (G : (projectiveSpaceOverRing n (.of k)).Modules)
    {j : projectiveSpaceOverRing n (.of k) ⟶ projectiveSpaceOverRing (n + 1) (.of k)}
    [IsClosedImmersion j]
    (hj : j ≫ projectiveSpaceToBase k (n + 1) = projectiveSpaceToBase k n)
    (res : ∀ d : ℤ, projectiveTwist (n + 1) F d ⟶
      (Scheme.Modules.pushforward j).obj (projectiveTwist n G d))
    (hsq : ∀ σ : (twistOver n (Spec (.of k)) 1).sections,
      ∃ σ' : (twistOver (n + 1) (Spec (.of k)) 1).sections, ∀ d : ℤ,
        twistSectionMul (n + 1) (Spec (.of k)) F σ' d ≫ res (d + 1) =
          res d ≫ (Scheme.Modules.pushforward j).map
            (twistSectionMul n (Spec (.of k)) G σ d)) :
    LiftsSectionAlong k n F G res
      (fun d => projectiveHPushforwardIso k j hj (projectiveTwist n G d) 0) := by
  intro σ
  obtain ⟨σ', hσ⟩ := hsq σ
  refine ⟨σ', fun d => ?_⟩
  rw [mulSection, projectiveHZeroMap, projectiveHZeroMap, ← cohomologyOverFieldMap_comp, hσ d,
    cohomologyOverFieldMap_comp,
    cohomologyOverFieldMap_pushforward_eq_conj k j hj (twistSectionMul n (Spec (.of k)) G σ d) 0]

/-! ### The restriction arrows, reindexed -/

section Res

/-- `d - 1 + 1 = d`, proved once: this equation is supplied to `eqToHom` at every `d`, and a
tactic proof inlined there is a term the kernel rechecks at each use site. -/
private theorem sub_one_add_one (d : ℤ) : d - 1 + 1 = d := sub_add_cancel d 1

/-- `d + 1 - 1 = d`, proved once, for the same reason as `sub_one_add_one`. -/
private theorem add_one_sub_one (d : ℤ) : d + 1 - 1 = d := add_sub_cancel_right d 1

variable (k : Type u) [Field k] (n : ℕ)
  {F : (projectiveSpaceOverRing (n + 1) (.of k)).Modules}
  {G : (projectiveSpaceOverRing n (.of k)).Modules}
  {j : projectiveSpaceOverRing n (.of k) ⟶ projectiveSpaceOverRing (n + 1) (.of k)}
  (s : (twistOver (n + 1) (Spec (.of k)) 1).sections)
  (b : ∀ d : ℤ, projectiveTwist (n + 1) F (d + 1) ⟶
    (Scheme.Modules.pushforward j).obj (projectiveTwist n G (d + 1)))

/-- The second arrow of the restriction sequence at `c`, read as an arrow out of `ℱ(d)` for a
`d` with `c + 1 = d`. `AlgebraicGeometry.HasMulRestrictionSequences` indexes its arrow by the
source of the multiplication, the package by the source of the arrow itself, and `c + 1` is not
syntactically `d`, so the two indexings differ by a transport. -/
private def shiftedRes (c d : ℤ) (h : c + 1 = d) :
    projectiveTwist (n + 1) F d ⟶
      (Scheme.Modules.pushforward j).obj (projectiveTwist n G d) :=
  eqToHom (congrArg (projectiveTwist (n + 1) F) h.symm) ≫ b c ≫
    eqToHom (congrArg
      (fun e : ℤ => (Scheme.Modules.pushforward j).obj (projectiveTwist n G e)) h)

/-- The restriction sequence of `AlgebraicGeometry.HasMulRestrictionSequences`, read with its
second arrow out of `ℱ(d + 1)`: the `comp_res` and `shortExact` clauses of the package. -/
private theorem shiftedRes_shortExact
    (wb : ∀ d : ℤ, twistSectionMul (n + 1) (Spec (.of k)) F s d ≫ b d = 0)
    (hb : ∀ d : ℤ, (ShortComplex.mk (twistSectionMul (n + 1) (Spec (.of k)) F s d)
      (b d) (wb d)).ShortExact)
    (c d : ℤ) (h : c = d) (h' : c + 1 = d + 1) :
    ∃ w : twistSectionMul (n + 1) (Spec (.of k)) F s d ≫
        shiftedRes k n b c (d + 1) h' = 0,
      (ShortComplex.mk (twistSectionMul (n + 1) (Spec (.of k)) F s d)
        (shiftedRes k n b c (d + 1) h') w).ShortExact := by
  subst h
  refine ⟨by simp [shiftedRes, wb c], ShortComplex.shortExact_of_iso ?_ (hb c)⟩
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
    (by simp [shiftedRes])

/-- The same sequence read at its middle term, `0 ⟶ ℱ(d-1) ⟶ ℱ(d) ⟶ j_*(𝒢(d)) ⟶ 0`: the
`shortExact'` clause of the package, whose first arrow is existential. -/
private theorem shiftedRes_shortExact'
    (wb : ∀ d : ℤ, twistSectionMul (n + 1) (Spec (.of k)) F s d ≫ b d = 0)
    (hb : ∀ d : ℤ, (ShortComplex.mk (twistSectionMul (n + 1) (Spec (.of k)) F s d)
      (b d) (wb d)).ShortExact)
    (c d : ℤ) (h : c + 1 = d) :
    ∃ (a : projectiveTwist (n + 1) F c ⟶ projectiveTwist (n + 1) F d)
      (w : a ≫ shiftedRes k n b c d h = 0),
      (ShortComplex.mk a (shiftedRes k n b c d h) w).ShortExact := by
  subst h
  refine ⟨twistSectionMul (n + 1) (Spec (.of k)) F s c, by simp [shiftedRes, wb c],
    ShortComplex.shortExact_of_iso ?_ (hb c)⟩
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
    (by simp [shiftedRes])

end Res

/-! ### The data, with every clause but `liftSection` -/

/-- **The hyperplane restriction data of [Stacks, Tag 08A0], twisted as in [Stacks, Tag 0EGK]
and compared on degree-zero cohomology through [Stacks, Tag 089Z] and [Stacks, Tag 089W], over
an infinite field: every clause of `AlgebraicGeometry.HyperplaneRestrictionPackage` except
`liftSection`.**

For an infinite field `k` and a coherent `ℱ` on `ℙ^{n+1}_k` there are a coherent `𝒢` on `ℙⁿ_k`,
a morphism `j : ℙⁿ_k ⟶ ℙ^{n+1}_k` that is affine, a closed immersion and a morphism over
`Spec k`, a global section `s` of `𝒪(1)`, restriction arrows `res d : ℱ(d) ⟶ j_*(𝒢(d))` with
`s · (-) ≫ res = 0`, the degree-zero cohomology comparison, and short exactness of

`0 ⟶ ℱ(d) ⟶ ℱ(d+1) ⟶ j_*(𝒢(d+1)) ⟶ 0`

with multiplication by `s` as its first arrow, in both the package's indexing and the one
indexed by the middle term.

`G`, `isCoherent`, `j`, `isAffineHom` and `s` are `AlgebraicGeometry.exists_restrictionSequences`;
`res`, `comp_res` and the two exactness clauses are its
`AlgebraicGeometry.HasMulRestrictionSequences` clause, reindexed from the source of the
multiplication to the source of the arrow; the comparison is
`AlgebraicGeometry.projectiveHPushforwardIso`, which is where the over-`Spec k` clause of
[Stacks, Tag 089Z] is used. -/
theorem exists_hyperplaneRestrictionData (k : Type u) [Field k] [Infinite k] (n : ℕ)
    (F : (projectiveSpaceOverRing (n + 1) (.of k)).Modules) (hFc : F.IsCoherent) :
    ∃ (G : (projectiveSpaceOverRing n (.of k)).Modules) (_ : G.IsCoherent)
      (j : projectiveSpaceOverRing n (.of k) ⟶ projectiveSpaceOverRing (n + 1) (.of k))
      (_ : IsAffineHom j) (_ : IsClosedImmersion j)
      (_ : j ≫ projectiveSpaceToBase k (n + 1) = projectiveSpaceToBase k n)
      (s : (twistOver (n + 1) (Spec (.of k)) 1).sections)
      (res : ∀ d : ℤ, projectiveTwist (n + 1) F d ⟶
        (Scheme.Modules.pushforward j).obj (projectiveTwist n G d))
      (comp_res : ∀ d : ℤ, twistSectionMul (n + 1) (Spec (.of k)) F s d ≫ res (d + 1) = 0)
      (_ : ∀ d : ℤ, projectiveH k n (projectiveTwist n G d) 0 ≅
        projectiveH k (n + 1) ((Scheme.Modules.pushforward j).obj (projectiveTwist n G d)) 0),
      (∀ d : ℤ, (ShortComplex.mk (twistSectionMul (n + 1) (Spec (.of k)) F s d)
        (res (d + 1)) (comp_res d)).ShortExact) ∧
      ∀ d : ℤ, ∃ (a : projectiveTwist (n + 1) F (d - 1) ⟶ projectiveTwist (n + 1) F d)
        (w : a ≫ res d = 0), (ShortComplex.mk a (res d) w).ShortExact := by
  obtain ⟨G, hGc, j, hjaff, hjover, hjci, s, hmul, -⟩ :=
    exists_restrictionSequences k n F hFc
  choose b wb hb using hmul
  have hcs : ∀ d : ℤ, ∃ w : twistSectionMul (n + 1) (Spec (.of k)) F s d ≫
        shiftedRes k n b (d + 1 - 1) (d + 1) (sub_one_add_one (d + 1)) = 0,
      (ShortComplex.mk (twistSectionMul (n + 1) (Spec (.of k)) F s d)
        (shiftedRes k n b (d + 1 - 1) (d + 1)
          (sub_one_add_one (d + 1))) w).ShortExact :=
    fun d => shiftedRes_shortExact k n s b wb hb (d + 1 - 1) d (add_one_sub_one d)
      (sub_one_add_one (d + 1))
  choose comp_res shortExact using hcs
  exact ⟨G, hGc, j, hjaff, hjci, hjover, s,
    fun d => shiftedRes k n b (d - 1) d (sub_one_add_one d), comp_res,
    fun d => projectiveHPushforwardIso k j hjover (projectiveTwist n G d) 0, shortExact,
    fun d => shiftedRes_shortExact' k n s b wb hb (d - 1) d (sub_one_add_one d)⟩

/-- **Hyperplane restriction data together with its `liftSection` clause is a
`AlgebraicGeometry.HyperplaneRestrictionPackage`.**

Read against `AlgebraicGeometry.exists_hyperplaneRestrictionData`, which produces the data over
an infinite field, this says that `AlgebraicGeometry.LiftsSectionAlong` for that data is all the
`pkg` hypothesis of [Stacks, Tag 08A7] needs beyond it. -/
theorem nonempty_hyperplaneRestrictionPackage_of_liftSection (k : Type u) [Field k] (n : ℕ)
    {F : (projectiveSpaceOverRing (n + 1) (.of k)).Modules}
    (G : (projectiveSpaceOverRing n (.of k)).Modules) (hGc : G.IsCoherent)
    {j : projectiveSpaceOverRing n (.of k) ⟶ projectiveSpaceOverRing (n + 1) (.of k)}
    (hjaff : IsAffineHom j) (s : (twistOver (n + 1) (Spec (.of k)) 1).sections)
    (res : ∀ d : ℤ, projectiveTwist (n + 1) F d ⟶
      (Scheme.Modules.pushforward j).obj (projectiveTwist n G d))
    (comp_res : ∀ d : ℤ, twistSectionMul (n + 1) (Spec (.of k)) F s d ≫ res (d + 1) = 0)
    (hse : ∀ d : ℤ, (ShortComplex.mk (twistSectionMul (n + 1) (Spec (.of k)) F s d)
      (res (d + 1)) (comp_res d)).ShortExact)
    (hse' : ∀ d : ℤ, ∃ (a : projectiveTwist (n + 1) F (d - 1) ⟶ projectiveTwist (n + 1) F d)
      (w : a ≫ res d = 0), (ShortComplex.mk a (res d) w).ShortExact)
    (compare : ∀ d : ℤ, projectiveH k n (projectiveTwist n G d) 0 ≅
      projectiveH k (n + 1) ((Scheme.Modules.pushforward j).obj (projectiveTwist n G d)) 0)
    (hlift : LiftsSectionAlong k n F G res compare) :
    Nonempty (HyperplaneRestrictionPackage k n F) :=
  ⟨{ G := G, isCoherent := hGc, j := j, isAffineHom := hjaff, s := s, res := res
     comp_res := comp_res, shortExact := hse, shortExact' := hse', compare := compare
     liftSection := hlift }⟩

/-- **Hyperplane restriction data over a closed immersion over `Spec k` is a package as soon as
its restriction arrows intertwine multiplication by a degree-one form upstairs with
multiplication by one on the hyperplane.**

This is `AlgebraicGeometry.nonempty_hyperplaneRestrictionPackage_of_liftSection` with the
canonical comparison supplied and `liftSection` replaced, through
`AlgebraicGeometry.liftsSectionAlong_of_pushforward_square`, by the square of sheaves it reduces
to. Read against `AlgebraicGeometry.exists_hyperplaneRestrictionData`, which produces everything
but the square over an infinite field, the square is all the `pkg` hypothesis of
[Stacks, Tag 08A7] needs there — a statement with no cohomology in it. -/
theorem nonempty_hyperplaneRestrictionPackage_of_pushforward_square (k : Type u) [Field k]
    (n : ℕ) {F : (projectiveSpaceOverRing (n + 1) (.of k)).Modules}
    (G : (projectiveSpaceOverRing n (.of k)).Modules) (hGc : G.IsCoherent)
    {j : projectiveSpaceOverRing n (.of k) ⟶ projectiveSpaceOverRing (n + 1) (.of k)}
    (hjaff : IsAffineHom j) [IsClosedImmersion j]
    (hj : j ≫ projectiveSpaceToBase k (n + 1) = projectiveSpaceToBase k n)
    (s : (twistOver (n + 1) (Spec (.of k)) 1).sections)
    (res : ∀ d : ℤ, projectiveTwist (n + 1) F d ⟶
      (Scheme.Modules.pushforward j).obj (projectiveTwist n G d))
    (comp_res : ∀ d : ℤ, twistSectionMul (n + 1) (Spec (.of k)) F s d ≫ res (d + 1) = 0)
    (hse : ∀ d : ℤ, (ShortComplex.mk (twistSectionMul (n + 1) (Spec (.of k)) F s d)
      (res (d + 1)) (comp_res d)).ShortExact)
    (hse' : ∀ d : ℤ, ∃ (a : projectiveTwist (n + 1) F (d - 1) ⟶ projectiveTwist (n + 1) F d)
      (w : a ≫ res d = 0), (ShortComplex.mk a (res d) w).ShortExact)
    (hsq : ∀ σ : (twistOver n (Spec (.of k)) 1).sections,
      ∃ σ' : (twistOver (n + 1) (Spec (.of k)) 1).sections, ∀ d : ℤ,
        twistSectionMul (n + 1) (Spec (.of k)) F σ' d ≫ res (d + 1) =
          res d ≫ (Scheme.Modules.pushforward j).map
            (twistSectionMul n (Spec (.of k)) G σ d)) :
    Nonempty (HyperplaneRestrictionPackage k n F) :=
  nonempty_hyperplaneRestrictionPackage_of_liftSection k n G hGc hjaff s res comp_res hse hse'
    (fun d => projectiveHPushforwardIso k j hj (projectiveTwist n G d) 0)
    (liftsSectionAlong_of_pushforward_square k n F G hj res hsq)

/-! ### The square for the canonical restriction arrows -/

section Canonical

variable (k : Type u) [Field k] (n : ℕ)
  (F : (projectiveSpaceOverRing (n + 1) (.of k)).Modules)
  {j : projectiveSpaceOverRing n (.of k) ⟶ projectiveSpaceOverRing (n + 1) (.of k)}
  (θ : ∀ d : ℤ, (Scheme.Modules.pullback j).obj (twistOver (n + 1) (Spec (.of k)) d) ≅
    twistOver n (Spec (.of k)) d)

/-- **The square of sheaves that `liftSection` reduces to, for the canonical restriction arrows,
follows from the corresponding square upstairs of the hyperplane.**

`AlgebraicGeometry.pullbackTwistUnitRes` is the unit of `j^* ⊣ j_*` followed by `j_*` of
`AlgebraicGeometry.pullbackTwistIso`, so naturality of the unit turns the square for it into the
square for `pullbackTwistIso` alone — which is the conclusion of
`Stacks.AlgebraicGeometry.PullbackTwistSectionMul.pullback_twistSectionMul`. This is the step that
needs `res` to be given by a formula rather than chosen out of the restriction sequences. -/
theorem pushforward_square_pullbackTwistUnitRes
    (σ' : (twistOver (n + 1) (Spec (.of k)) 1).sections)
    (σ : (twistOver n (Spec (.of k)) 1).sections) (d : ℤ)
    (hsq : (Scheme.Modules.pullback j).map (twistSectionMul (n + 1) (Spec (.of k)) F σ' d) ≫
        (pullbackTwistIso j F θ (d + 1)).hom =
      (pullbackTwistIso j F θ d).hom ≫
        twistSectionMul n (Spec (.of k)) ((Scheme.Modules.pullback j).obj F) σ d) :
    twistSectionMul (n + 1) (Spec (.of k)) F σ' d ≫ pullbackTwistUnitRes j F θ (d + 1) =
      pullbackTwistUnitRes j F θ d ≫ (Scheme.Modules.pushforward j).map
        (twistSectionMul n (Spec (.of k)) ((Scheme.Modules.pullback j).obj F) σ d) := by
  calc twistSectionMul (n + 1) (Spec (.of k)) F σ' d ≫ pullbackTwistUnitRes j F θ (d + 1)
      = (twistSectionMul (n + 1) (Spec (.of k)) F σ' d ≫
            (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
              (projectiveTwist (n + 1) F (d + 1))) ≫
          (Scheme.Modules.pushforward j).map (pullbackTwistIso j F θ (d + 1)).hom := by
        rw [pullbackTwistUnitRes, Category.assoc]
        rfl
    _ = (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
            (projectiveTwist (n + 1) F d) ≫
          (Scheme.Modules.pushforward j).map
            ((Scheme.Modules.pullback j).map
              (twistSectionMul (n + 1) (Spec (.of k)) F σ' d) ≫
                (pullbackTwistIso j F θ (d + 1)).hom) := by
        rw [← (Scheme.Modules.pullbackPushforwardAdjunction j).unit_naturality
            (twistSectionMul (n + 1) (Spec (.of k)) F σ' d),
          Category.assoc, ← CategoryTheory.Functor.map_comp]
    _ = (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
            (projectiveTwist (n + 1) F d) ≫
          (Scheme.Modules.pushforward j).map ((pullbackTwistIso j F θ d).hom ≫
            twistSectionMul n (Spec (.of k)) ((Scheme.Modules.pullback j).obj F) σ d) := by
        rw [hsq]
    _ = pullbackTwistUnitRes j F θ d ≫ (Scheme.Modules.pushforward j).map
          (twistSectionMul n (Spec (.of k)) ((Scheme.Modules.pullback j).obj F) σ d) := by
        rw [pullbackTwistUnitRes, CategoryTheory.Functor.map_comp, Category.assoc]
        rfl

/-- A short exact sequence read with its first object replaced by an isomorphic one: pure
category theory, isolated so that the index transport below is a single argument rather than a
subterm of a tactic proof the kernel rechecks. -/
theorem exists_shortExact_of_isoLeft {C : Type*} [Category C] [Abelian C]
    {A₁ X₁ X₂ X₃ : C} {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃} {w : f ≫ g = 0}
    (hse : (ShortComplex.mk f g w).ShortExact) (e : A₁ ≅ X₁) :
    ∃ (a : A₁ ⟶ X₂) (w' : a ≫ g = 0), (ShortComplex.mk a g w').ShortExact := by
  refine ⟨e.hom ≫ f, by rw [Category.assoc, w, Limits.comp_zero], ?_⟩
  exact ShortComplex.shortExact_of_iso (S₁ := ShortComplex.mk f g w)
    (ShortComplex.isoMk e.symm (Iso.refl _) (Iso.refl _) (by simp) (by simp)) hse

/-- The restriction sequence read at its middle term, `0 ⟶ ℱ(d-1) ⟶ ℱ(d) ⟶ j_*(𝒢(d)) ⟶ 0`: the
`shortExact'` clause of the package. The index equation is an argument, so that after
substitution the transport is the identity. -/
theorem exists_shortExact_of_index_eq (s : (twistOver (n + 1) (Spec (.of k)) 1).sections)
    (c d : ℤ) (h : c + 1 = d)
    (w : twistSectionMul (n + 1) (Spec (.of k)) F s c ≫
      pullbackTwistUnitRes j F θ (c + 1) = 0)
    (hse : (ShortComplex.mk (twistSectionMul (n + 1) (Spec (.of k)) F s c)
      (pullbackTwistUnitRes j F θ (c + 1)) w).ShortExact) :
    ∃ (a : projectiveTwist (n + 1) F (d - 1) ⟶ projectiveTwist (n + 1) F d)
      (w' : a ≫ pullbackTwistUnitRes j F θ d = 0),
      (ShortComplex.mk a (pullbackTwistUnitRes j F θ d) w').ShortExact := by
  subst h
  exact exists_shortExact_of_isoLeft hse
    (eqToIso (congrArg (projectiveTwist (n + 1) F) (add_one_sub_one c)))

end Canonical

/-! ### The package, over an infinite field -/

/-- The package from the canonical restriction data, given the `sectionHom` form of the lifting
of degree-one forms for any hyperplane whose restriction map is surjective on `𝒪(1)`. -/
private theorem nonempty_package_of_canonical_lift (k : Type u) [Field k] [Infinite k] (n : ℕ)
    (hlift : ∀ (j : projectiveSpaceOverRing n (.of k) ⟶
          projectiveSpaceOverRing (n + 1) (.of k)) (_ : IsClosedImmersion j)
        (_ : j ≫ projectiveSpaceToBase k (n + 1) = projectiveSpaceToBase k n)
        (θ1 : (Scheme.Modules.pullback j).obj (twistOver (n + 1) (Spec (.of k)) 1) ≅
          twistOver n (Spec (.of k)) 1),
        (Function.Surjective fun x : Γ(twistOver (n + 1) (Spec (.of k)) 1, ⊤) =>
          θ1.hom.app ⊤ (pullbackGlobalSections j (twistOver (n + 1) (Spec (.of k)) 1) x)) →
        ∀ σ : (twistOver n (Spec (.of k)) 1).sections,
        ∃ σ' : (twistOver (n + 1) (Spec (.of k)) 1).sections,
          sectionHom (twistOver n (Spec (.of k)) 1) σ =
            (Stacks.PullbackAlgebra.pullbackUnitIso j.toLRSHom.toShHom).inv ≫
              (Scheme.Modules.pullback j).map
                (sectionHom (twistOver (n + 1) (Spec (.of k)) 1) σ') ≫ θ1.hom)
    (F : (projectiveSpaceOverRing (n + 1) (.of k)).Modules) (hFc : F.IsCoherent) :
    Nonempty (HyperplaneRestrictionPackage k n F) := by
  obtain ⟨j, hjaff, hjci, hjover, hGc, s, θ1, hres, hSE⟩ :=
    exists_restrictionSequences_pullbackRes k n F hFc
  have := hjci
  obtain ⟨θ, hθ1, hθ⟩ := Stacks.AlgebraicGeometry.PullbackTwistRegrouping.exists_regroupingFamily
    (n + 1) n (Spec (.of k)) j θ1
  refine nonempty_hyperplaneRestrictionPackage_of_pushforward_square k n
    ((Scheme.Modules.pullback j).obj F) hGc hjaff hjover s (pullbackTwistUnitRes j F θ)
    (fun d => (hSE θ d).choose) (fun d => (hSE θ d).choose_spec)
    (fun d => exists_shortExact_of_index_eq k n F θ s (d - 1) d (sub_one_add_one d)
      (hSE θ (d - 1)).choose (hSE θ (d - 1)).choose_spec)
    (fun σ => ?_)
  obtain ⟨σ', hσ'⟩ := hlift j hjci hjover θ1 hres σ
  rw [← hθ1] at hσ'
  exact ⟨σ', fun d => pushforward_square_pullbackTwistUnitRes k n F θ σ' σ d
    (Stacks.AlgebraicGeometry.PullbackTwistSectionMul.pullback_twistSectionMul (n + 1) n
      (Spec (.of k)) j F d (θ d) (θ 1) (θ (d + 1)) (hθ d) σ' σ hσ')⟩

/-- **The hyperplane restriction package of [Stacks, Tag 08A7] over an infinite field, given that
degree-one forms restrict onto the hyperplane.**

Every clause of `AlgebraicGeometry.HyperplaneRestrictionPackage` is proved here except the one
hypothesis `hlift`: that along a closed immersion `j : ℙⁿ_k ⟶ ℙ^{n+1}_k` over `Spec k` carrying
`𝒪(1)` to `𝒪(1)`, every global section of `𝒪_{ℙⁿ}(1)` is the restriction of a global section of
`𝒪_{ℙ^{n+1}}(1)` — "restriction" in the sense of
`Stacks.AlgebraicGeometry.PullbackTwistSectionMul.pullback_twistSectionMul`'s `hst`, i.e. the
comparison of [Stacks, Tag 01CD] on the unit followed by `θ1`. By
`Stacks.PullbackUnitComparisonSection.eval_top_of_sectionHom_eq` that is the *geometric*
restriction read on `Γ(·, ⊤)`, so `hlift` says exactly that
`AlgebraicGeometry.pullbackGlobalSections j (𝒪(1))` is surjective onto `Γ(j^*𝒪(1), ⊤)`.

For the rest, `AlgebraicGeometry.exists_restrictionSequences_pullbackRes`
supplies the hyperplane, the section and the restriction sequences for the *canonical* arrows
`AlgebraicGeometry.pullbackTwistUnitRes`;
`Stacks.AlgebraicGeometry.PullbackTwistRegrouping.exists_regroupingFamily` supplies the family of
twist identifications satisfying the regrouping square in **every** integer degree, which is what
`…PullbackTwistSectionMul.pullback_twistSectionMul` asks for; and
`AlgebraicGeometry.pushforward_square_pullbackTwistUnitRes` carries its square down to the square
of `AlgebraicGeometry.liftsSectionAlong_of_pushforward_square`. -/
theorem nonempty_hyperplaneRestrictionPackage_of_liftSectionHom (k : Type u) [Field k]
    [Infinite k] (n : ℕ)
    (hlift : ∀ (j : projectiveSpaceOverRing n (.of k) ⟶
          projectiveSpaceOverRing (n + 1) (.of k)) (_ : IsClosedImmersion j)
        (_ : j ≫ projectiveSpaceToBase k (n + 1) = projectiveSpaceToBase k n)
        (θ1 : (Scheme.Modules.pullback j).obj (twistOver (n + 1) (Spec (.of k)) 1) ≅
          twistOver n (Spec (.of k)) 1)
        (σ : (twistOver n (Spec (.of k)) 1).sections),
        ∃ σ' : (twistOver (n + 1) (Spec (.of k)) 1).sections,
          sectionHom (twistOver n (Spec (.of k)) 1) σ =
            (Stacks.PullbackAlgebra.pullbackUnitIso j.toLRSHom.toShHom).inv ≫
              (Scheme.Modules.pullback j).map
                (sectionHom (twistOver (n + 1) (Spec (.of k)) 1) σ') ≫ θ1.hom)
    (F : (projectiveSpaceOverRing (n + 1) (.of k)).Modules) (hFc : F.IsCoherent) :
    Nonempty (HyperplaneRestrictionPackage k n F) :=
  nonempty_package_of_canonical_lift k n (fun j hji hjo θ1 _ σ => hlift j hji hjo θ1 σ) F hFc

/-- **Surjectivity of restriction gives the `liftSection` clause in its `sectionHom` form.**
If every global section of `𝒪_{ℙⁿ}(1)` is `θ1` of the restriction along `j` of a global section
of `𝒪_{ℙ^{n+1}}(1)`, then every `σ` is the section whose `sectionHom` is the comparison of
[Stacks, Tag 01CD] on the unit followed by `θ1`, which is the shape
`AlgebraicGeometry.nonempty_hyperplaneRestrictionPackage_of_liftSectionHom` consumes.

The two readings of "restriction" are identified by
`Stacks.PullbackUnitComparisonSection.eval_top_of_sectionHom_eq`, and a section of a sheaf of
modules is determined by its value on `⊤` (`Stacks.NonvanishingSpelling.sectionsEquiv`). -/
theorem exists_sectionHom_eq_of_surjective_restriction (k : Type u) [Field k] (n : ℕ)
    {j : projectiveSpaceOverRing n (.of k) ⟶ projectiveSpaceOverRing (n + 1) (.of k)}
    (θ1 : (Scheme.Modules.pullback j).obj (twistOver (n + 1) (Spec (.of k)) 1) ≅
      twistOver n (Spec (.of k)) 1)
    (hsurj : Function.Surjective fun x : Γ(twistOver (n + 1) (Spec (.of k)) 1, ⊤) =>
      θ1.hom.app ⊤ (pullbackGlobalSections j (twistOver (n + 1) (Spec (.of k)) 1) x))
    (σ : (twistOver n (Spec (.of k)) 1).sections) :
    ∃ σ' : (twistOver (n + 1) (Spec (.of k)) 1).sections,
      sectionHom (twistOver n (Spec (.of k)) 1) σ =
        (Stacks.PullbackAlgebra.pullbackUnitIso j.toLRSHom.toShHom).inv ≫
          (Scheme.Modules.pullback j).map
            (sectionHom (twistOver (n + 1) (Spec (.of k)) 1) σ') ≫ θ1.hom := by
  obtain ⟨x, hx⟩ := hsurj (σ.eval (Opposite.op ⊤))
  set σ' := (Stacks.NonvanishingSpelling.sectionsEquiv
    (projectiveSpaceOverRing (n + 1) (.of k))
    (twistOver (n + 1) (Spec (.of k)) 1)).symm x with hσ'
  refine ⟨σ', ?_⟩
  set t := (twistOver n (Spec (.of k)) 1).unitHomEquiv
    ((Stacks.PullbackAlgebra.pullbackUnitIso j.toLRSHom.toShHom).inv ≫
      (Scheme.Modules.pullback j).map
        (sectionHom (twistOver (n + 1) (Spec (.of k)) 1) σ') ≫ θ1.hom)
  have hst : sectionHom (twistOver n (Spec (.of k)) 1) t =
      (Stacks.PullbackAlgebra.pullbackUnitIso j.toLRSHom.toShHom).inv ≫
        (Scheme.Modules.pullback j).map
          (sectionHom (twistOver (n + 1) (Spec (.of k)) 1) σ') ≫ θ1.hom :=
    Equiv.symm_apply_apply (twistOver n (Spec (.of k)) 1).unitHomEquiv _
  have hx' : σ'.eval (Opposite.op ⊤) = x := by
    rw [hσ', ← Stacks.NonvanishingSpelling.sectionsEquiv_apply, Equiv.apply_symm_apply]
  have hts : t = σ := by
    refine (Stacks.NonvanishingSpelling.sectionsEquiv
      (projectiveSpaceOverRing n (.of k)) (twistOver n (Spec (.of k)) 1)).injective ?_
    rwa [Stacks.NonvanishingSpelling.sectionsEquiv_apply,
      Stacks.NonvanishingSpelling.sectionsEquiv_apply,
      Stacks.PullbackUnitComparisonSection.eval_top_of_sectionHom_eq (n + 1) n
        (Spec (.of k)) j θ1 σ' t hst, hx']
  rwa [← hts]

/-- **The hyperplane restriction package of [Stacks, Tag 08A7] over an infinite field, given that
restriction to a hyperplane is surjective on global sections of `𝒪(1)`.**

This is `AlgebraicGeometry.nonempty_hyperplaneRestrictionPackage_of_liftSectionHom` with its
hypothesis read geometrically, through
`AlgebraicGeometry.exists_sectionHom_eq_of_surjective_restriction`: the section whose `sectionHom`
is the comparison of [Stacks, Tag 01CD] followed by `θ1` is the one whose value on `⊤` is the
image of the given one under `AlgebraicGeometry.pullbackGlobalSections` and `θ1`.

The hypothesis quantifies over the closed immersion and over the identification of the twists
because [Stacks, Tag 089Z] supplies them only existentially. It is **not** needed in that
generality: `AlgebraicGeometry.nonempty_hyperplaneRestrictionPackage` below is the same
conclusion with no hypothesis at all, surjectivity being available for the *particular*
hyperplane the data is built on (`AlgebraicGeometry.surjective_restriction_zeroScheme`). -/
theorem nonempty_hyperplaneRestrictionPackage_of_surjective_restriction (k : Type u) [Field k]
    [Infinite k] (n : ℕ)
    (hsurj : ∀ (j : projectiveSpaceOverRing n (.of k) ⟶
          projectiveSpaceOverRing (n + 1) (.of k)) (_ : IsClosedImmersion j)
        (_ : j ≫ projectiveSpaceToBase k (n + 1) = projectiveSpaceToBase k n)
        (θ1 : (Scheme.Modules.pullback j).obj (twistOver (n + 1) (Spec (.of k)) 1) ≅
          twistOver n (Spec (.of k)) 1),
        Function.Surjective fun x : Γ(twistOver (n + 1) (Spec (.of k)) 1, ⊤) =>
          θ1.hom.app ⊤ (pullbackGlobalSections j (twistOver (n + 1) (Spec (.of k)) 1) x))
    (F : (projectiveSpaceOverRing (n + 1) (.of k)).Modules) (hFc : F.IsCoherent) :
    Nonempty (HyperplaneRestrictionPackage k n F) :=
  nonempty_hyperplaneRestrictionPackage_of_liftSectionHom k n
    (fun j hji hjo θ1 σ => exists_sectionHom_eq_of_surjective_restriction k n θ1
      (hsurj j hji hjo θ1) σ) F hFc

/-! ### The package, unconditionally -/

/-- **The hyperplane restriction package of [Stacks, Tag 08A7] over an infinite field.** For a
coherent sheaf `ℱ` on `ℙ^{n+1}_k` with `k` an infinite field, the hyperplane restriction data of
[Stacks, Tag 08A7] exists: every clause of `AlgebraicGeometry.HyperplaneRestrictionPackage`,
`liftSection` included, holds for the hyperplane, the section and the canonical restriction arrows
that `AlgebraicGeometry.exists_restrictionSequences_pullbackRes` produces.

This is `AlgebraicGeometry.nonempty_hyperplaneRestrictionPackage_of_liftSectionHom` with its
hypothesis discharged. The hypothesis is about the hyperplane that theorem is handed, and
`exists_restrictionSequences_pullbackRes` reports it: restriction of degree-one forms to that
hyperplane is onto (`AlgebraicGeometry.surjective_restriction_zeroScheme`), which
`AlgebraicGeometry.exists_sectionHom_eq_of_surjective_restriction` turns into the `sectionHom`
form the assembly consumes.

It is what the `pkg` hypothesis of
`AlgebraicGeometry.span_mulSections_eq_top_of_isMRegular` asks for. -/
@[sga "6 XIII 2.5" "partial"]
theorem nonempty_hyperplaneRestrictionPackage (k : Type u) [Field k] [Infinite k] (n : ℕ)
    (F : (projectiveSpaceOverRing (n + 1) (.of k)).Modules) (hFc : F.IsCoherent) :
    Nonempty (HyperplaneRestrictionPackage k n F) :=
  nonempty_package_of_canonical_lift k n
    (fun _ _ _ θ1 hres σ => exists_sectionHom_eq_of_surjective_restriction k n θ1 hres σ) F hFc

end AlgebraicGeometry

end
