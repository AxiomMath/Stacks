module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.CechVanishing
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineBaseCohomology
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SituationBaseChange
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# A top-degree base-change situation of positive top degree

`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation` packages the hypotheses of
[Stacks, Tag 0EX3]: a morphism `f : X ⟶ Y` of quasi-compact quasi-separated schemes, a degree
`d` above which the higher direct images of every quasi-coherent module vanish, and a cartesian
square. Two constructions of one exist.
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.baseChange` takes a situation as input, so
it is not a base case, and
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHom` builds one from an affine
morphism, for which `Rⁱ f_* F` vanishes already for `i > 0` ([Stacks, Tag 01XC]); at `d > 0` the
degree-`d` object of that situation is therefore *itself zero*
(`…isZero_topDirectImage_of_pos`), and the three conclusions of the tag say nothing at it.

This file builds a situation of positive top degree whose vanishing is not of that kind: the
structure morphism of projective `n`-space over a ring, at `d = n`. Its vanishing field is
[Stacks, Tag 01YS] clause (2), which bounds the cohomology of a quasi-coherent module on `ℙⁿ_R`
*above* `n` and gives nothing in degree `n`. Nothing in the development makes the degree-`n`
object of this situation zero, and this file reduces the question of whether it is to a
statement about an explicit finite complex (see `## What is not proved` below).

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofProjectiveSpace`: the situation of
  `ℙⁿ_R ⟶ Spec R` at `d = n`, with an arbitrary cartesian square.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofProjectiveSpaceBaseChange`: the same
  with the canonical cartesian square over a morphism `g : Y' ⟶ Spec R`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofProjectiveSpaceSelf`: the same with
  the identity square, so that the base-changed morphism is the structure morphism itself.

## Main results

* `Stacks.Cohomology.AffineBase.isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup`:
  the two spellings of `Hⁱ(X, ℱ)` used in this development — the `ℤ`-indexed right derived
  functor of module-valued global sections, and the `ℕ`-indexed `Hgroup` — agree on vanishing,
  in both directions and for every scheme. This is unconditional and had not been composed.
* `Stacks.ProjectiveCohomology.compactSpace_projectiveSpaceOverRing` and
  `quasiSeparatedSpace_projectiveSpaceOverRing`: projective space over a ring is quasi-compact
  and quasi-separated.
* `Stacks.ProjectiveCohomology.isZero_rightDerivedPlus_pushforward_of_lt`: the higher direct
  images of a quasi-coherent module along `ℙⁿ_R ⟶ Spec R` vanish above `n`.
* `Stacks.ProjectiveCohomology.isZero_Hgroup_of_isZero_rightDerivedPlus_pushforward` and
  `Stacks.ProjectiveCohomology.isZero_Hgroup_iff_isZero_cechHomology_chart`: the converse
  direction, and its translation into the Čech complex of the standard charts.
* `…TopDegreeBaseChangeSituation.not_isZero_topDirectImage_of_not_isZero_Hgroup` and
  `…not_isZero_topDirectImage_of_not_isZero_cechHomology`: **where this situation is tight.**
  The degree-`d` object of `ofProjectiveSpaceSelf n R` is nonzero as soon as `Hⁿ(ℙⁿ_R, ℱ)` is,
  equivalently as soon as the degree-`n` homology of the Čech complex of the `n + 1` standard
  charts is.
* `Stacks.ProjectiveCohomology.isZero_rightDerivedPlus_pushforward_of_isAffineHom_structure`:
  and that same nonvanishing is exactly what separates this situation from `ofIsAffineHom` —
  were the structure morphism of `ℙⁿ_R` affine, every positive degree would vanish.
* `…TopDegreeBaseChangeSituation.isZero_rightDerivedPlus_pushforward_baseChange_projectiveSpace`:
  **the vacuity control.** Conclusion (a) of [Stacks, Tag 0EX3], instantiated at this situation:
  for *every* cartesian square over `ℙⁿ_R ⟶ Spec R`, the higher direct images along the
  base-changed morphism vanish above `n`. Its statement mentions no situation, and it is not a
  consequence of [Stacks, Tag 01YS] clause (2), which is stated over a *ring* base only.
* `…TopDegreeBaseChangeSituation.isZero_cohomology_baseChange_projectiveSpace`:
  a second such control, over an affine base, from the family's `isZero_cohomology_of_lt`.

## What is not proved

**That the degree-`n` object is nonzero for some quasi-coherent module.** By
`not_isZero_topDirectImage_of_not_isZero_cechHomology` this is equivalent to the degree-`n`
homology of the Čech complex of the standard charts being nonzero for some quasi-coherent
module, and the witness the source uses is the twist `𝒪(-n-1)`, whose cohomology is
[Stacks, Tag 01XT]. That computation is not in the development: the implementation notes of
`StacksFrontier/AlgebraicGeometry/ProjectiveCohomology/Basic.lean` and of
`…/ProjectiveCohomology/TwistWeights.lean` name what is missing, namely the splitting of the
Čech *differential* along the `ℤ^{n+1}`-valued Laurent weight and the weightwise contracting
homotopy. [Stacks, Tag 01XT] is independent of [Stacks, Tag 0EX3]: the tag's vanishing above
`d` is a hypothesis of 0EX3 and the nonvanishing in degree `d` is not among its conclusions, so
nothing here is circular.

## Implementation notes

*Why the vanishing field is a composite of three bridges.* [Stacks, Tag 01YS] clause (2)
is stated for the *absolute* cohomology `Hᵍ(ℙⁿ_R, ℱ)` in the `Hgroup` spelling, while the
situation's field asks for the vanishing of a higher direct image. Three steps connect them, all
available and none of them new mathematics: the `ℕ`/`ℤ` reindexing of right derived functors
(`Stacks.DerivedIndexing.isZero_rightDerived_obj_iff`), the module-valued/abelian-group-valued
comparison
(`Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup`), and the
affine-base comparison of [Stacks, Tag 01XK]
(`…TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_of_isZero_cohomology`). The first two
are packaged here as one `Iff` because both directions are needed — the forward direction for
the vanishing field and the backward direction for the tightness statements.

*Why the four finiteness hypotheses are proved from the chart cover.* Projective space over a
ring is the base change of the integral model, not `Proj` of a polynomial ring on the nose, and
Mathlib's properness of `Proj.toSpecZero` needs an `Algebra.FiniteType` instance that is not
available at `MvPolynomial.homogeneousSubmodule _ _ 0`. The `n + 1` standard charts are affine
opens and so are their pairwise intersections, which is all that compactness and
quasi-separatedness need.

*Why the situation is written out at each use.* `(ofProjectiveSpace …).X'` is `X'` by `rfl`, but
a quasi-coherence instance on a module over `X'` is not found at the projected spelling; it is
re-declared with `inferInstanceAs` at the type the family asks for. Binding the situation with
`let` inside a proof makes the projection opaque and leaves the universe of `SheafOfModules`
undetermined, so it is spelled out instead.

*No tag attribute.* Nothing here states a clause of a tag. The vanishing is
[Stacks, Tag 01YS] clause (2), which carries its attribute in
`StacksFrontier/AlgebraicGeometry/ProjectiveCohomology/Basic.lean`, repackaged as the
hypothesis bundle of [Stacks, Tag 0EX3]; the two controls are conclusion (a) of
[Stacks, Tag 0EX3], which carries its attribute in
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/BaseChangeVanishing.lean`, instantiated
at one situation. By the covering-set rule none of these declarations belongs to the covering
set of either tag.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.CechSheaf

universe u

attribute [local instance] HasDerivedCategory.standard

noncomputable section

namespace Stacks.Cohomology.AffineBase

/-- **The two spellings of `Hᵍ(X, ℱ)` agree on vanishing.** The left-hand side is the
`ℤ`-indexed right derived functor of module-valued global sections, which is the spelling
[Stacks, Tag 01XK] and the affine-base comparisons of this directory are stated in; the
right-hand side is `Hgroup`, the `ℕ`-indexed right derived functor of abelian-group-valued
sections, which is the spelling [Stacks, Tag 01XB] and [Stacks, Tag 01YS] are stated in.

It is the reindexing comparison `Stacks.DerivedIndexing.isZero_rightDerived_obj_iff` composed
with the module-valued/abelian-group-valued comparison
`Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup`.
Both are isomorphisms, so
no hypothesis on `X` or on `ℱ` appears. -/
theorem isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup
    (X : Scheme.{u}) (F : X.Modules) (q : ℕ) :
    IsZero (((moduleGlobalSections X).rightDerivedPlus (q : ℤ)).obj F) ↔
      IsZero (Hgroup X.ringCatSheaf ⊤ q F) :=
  (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff (moduleGlobalSections X) q F).symm.trans
    (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      X.ringCatSheaf ⊤ q F)

end Stacks.Cohomology.AffineBase

namespace Stacks.ProjectiveCohomology

open Stacks.Cohomology.AffineBase

variable (n : ℕ) (R : CommRingCat.{u})

/-- The intersection of two standard charts of projective `n`-space over a ring is compact,
being an affine open. -/
theorem isCompact_chart_inf (i j : Fin (n + 1)) :
    IsCompact ((chart n R i ⊓ chart n R j : (projectiveSpaceOverRing n R).Opens) :
      Set (projectiveSpaceOverRing n R)) := by
  have h : (⨅ k, chart n R (![i, j] k)) = chart n R i ⊓ chart n R j :=
    le_antisymm (le_inf (iInf_le _ 0) (iInf_le _ 1))
      (le_iInf fun k => by fin_cases k <;> simp)
  have hc := isAffineOpen_iInf_chart n R (![i, j])
  rw [h] at hc
  exact hc.isCompact

/-- **Projective `n`-space over a ring is quasi-compact**: it is the union of its `n + 1`
standard charts, each of which is an affine open and so compact. -/
instance compactSpace_projectiveSpaceOverRing : CompactSpace (projectiveSpaceOverRing n R) := by
  rw [← isCompact_univ_iff]
  have h : (Set.univ : Set (projectiveSpaceOverRing n R)) =
      ⋃ i, (chart n R i : Set (projectiveSpaceOverRing n R)) := by
    have hcov := iSup_chart_eq_top n R
    rw [← SetLike.coe_set_eq] at hcov
    simpa using hcov.symm
  rw [h]
  exact isCompact_iUnion fun i => (isAffineOpen_chart n R i).isCompact

/-- **Projective `n`-space over a ring is quasi-separated**: the standard charts are affine
opens covering it and their pairwise intersections are compact. -/
instance quasiSeparatedSpace_projectiveSpaceOverRing :
    QuasiSeparatedSpace (projectiveSpaceOverRing n R) :=
  AlgebraicGeometry.Scheme.quasiSeparatedSpace_of_isOpenCover (chart n R)
    (iSup_chart_eq_top n R) (isAffineOpen_chart n R)
    fun i j => by simpa using isCompact_chart_inf n R i j

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **The higher direct images of a quasi-coherent module along `ℙⁿ_R ⟶ Spec R` vanish above
`n`.** This is [Stacks, Tag 01YS] clause (2) — `Hᵍ(ℙⁿ_R, ℱ) = 0` for `q > n` — carried across
the affine-base comparison of [Stacks, Tag 01XK]: the base `Spec R` is affine and the structure
morphism is quasi-compact and quasi-separated, so a quasi-coherent module with vanishing
cohomology in a degree has vanishing higher direct image in that degree.

This is the vanishing hypothesis of [Stacks, Tag 0EX3] for the pair `(ℙⁿ_R ⟶ Spec R, n)`, and
nothing in it bounds the degree-`n` object: clause (2) is a statement about degrees `q > n`
only. -/
theorem isZero_rightDerivedPlus_pushforward_of_lt
    (i : ℤ) (hi : (n : ℤ) < i) (F : (projectiveSpaceOverRing n R).Modules)
    [F.IsQuasicoherent] :
    IsZero (((Scheme.Modules.pushforward
      ((projectiveSpaceOverRing n R) ↘ (Spec R))).rightDerivedPlus i).obj F) := by
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, (q : ℤ) = i :=
    ⟨i.toNat, Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg n) hi.le)⟩
  exact isZero_rightDerivedPlus_pushforward_of_isZero_cohomology _ (q : ℤ) F
    ((isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup _ F q).mpr
      (isZero_Hgroup_of_lt n R F q (by exact_mod_cast hi)))

open Stacks.AlgebraicGeometry.TopDegreeBaseChange in
/-- **The converse direction over the affine base `Spec R`**: if the degree-`q` higher direct
image of a quasi-coherent module along `ℙⁿ_R ⟶ Spec R` vanishes, so does its degree-`q`
cohomology. This is the reflecting half of [Stacks, Tag 01XK], and it is what turns a
nonvanishing cohomology group into a nonvanishing higher direct image. -/
theorem isZero_Hgroup_of_isZero_rightDerivedPlus_pushforward
    (q : ℕ) (F : (projectiveSpaceOverRing n R).Modules) [F.IsQuasicoherent]
    (h : IsZero (((Scheme.Modules.pushforward
      ((projectiveSpaceOverRing n R) ↘ (Spec R))).rightDerivedPlus (q : ℤ)).obj F)) :
    IsZero (Hgroup (projectiveSpaceOverRing n R).ringCatSheaf ⊤ q F) :=
  (isZero_rightDerivedPlus_moduleGlobalSections_iff_isZero_Hgroup _ F q).mp
    (isZero_cohomology_of_isZero_rightDerivedPlus_pushforward _ (q : ℤ) F h)

/-- **The cohomology of projective space is the homology of the Čech complex of the standard
charts.** This is `Stacks.Cohomology.CechVanishing.isZero_Hgroup_iff_isZero_cechHomology`, whose
hypothesis — that every finite intersection of members of the covering is an affine open — is
`Stacks.ProjectiveCohomology.isAffineOpen_iInf_chartAtUniverse` for the standard cover. It is
stated as an `Iff` because the direction that matters here is the one carrying *nonvanishing*
into the explicit complex. -/
theorem isZero_Hgroup_iff_isZero_cechHomology_chart
    (F : (projectiveSpaceOverRing n R).Modules) [F.IsQuasicoherent] (q : ℕ) :
    IsZero (Hgroup (projectiveSpaceOverRing n R).ringCatSheaf ⊤ q F) ↔
      IsZero ((cechComplex.{u, u, u, u} (⊤ : (projectiveSpaceOverRing n R).Opens)
        (chartAtUniverse n R) (iSup_chartAtUniverse_eq_top n R).symm F).homology q) :=
  Stacks.Cohomology.CechVanishing.isZero_Hgroup_iff_isZero_cechHomology
    (projectiveSpaceOverRing n R) ⊤ (chartAtUniverse n R)
    (iSup_chartAtUniverse_eq_top n R).symm
    (fun _ s => isAffineOpen_iInf_chartAtUniverse n R s) F q

/-- **Were the structure morphism of `ℙⁿ_R` affine, all of its positive higher direct images
would vanish**, by [Stacks, Tag 01XC].

This is the statement that separates the situation built below from
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.ofIsAffineHom`, and it locates the
separation in exactly the same place as the tightness statements: a single nonvanishing
`Rᵍ f_* ℱ` with `q > 0` both shows that this situation is not degenerate and shows that it is
not an instance of the affine one. -/
theorem isZero_rightDerivedPlus_pushforward_of_isAffineHom_structure
    [IsAffineHom ((projectiveSpaceOverRing n R) ↘ (Spec R))]
    (F : (projectiveSpaceOverRing n R).Modules) [F.IsQuasicoherent] (q : ℕ) (hq : 0 < q) :
    IsZero (((Scheme.Modules.pushforward
      ((projectiveSpaceOverRing n R) ↘ (Spec R))).rightDerivedPlus (q : ℤ)).obj F) :=
  Stacks.Cohomology.Affine.isZero_rightDerived_pushforward_of_isAffineHom _ F (q : ℤ)
    (by exact_mod_cast hq)

end Stacks.ProjectiveCohomology

namespace Stacks.AlgebraicGeometry

namespace TopDegreeBaseChangeSituation

open Stacks.ProjectiveCohomology

/-- **A top-degree base-change situation of top degree `n`, from projective `n`-space.** The
vanishing hypothesis of [Stacks, Tag 0EX3] asks that `Rⁱ f_* ℱ` vanish for every quasi-coherent
`ℱ` and every `i > d`; for the structure morphism of `ℙⁿ_R` and `d = n` that is
[Stacks, Tag 01YS] clause (2) read through [Stacks, Tag 01XK], which is
`Stacks.ProjectiveCohomology.isZero_rightDerivedPlus_pushforward_of_lt`. The two finiteness
hypotheses hold because projective space is covered by its `n + 1` affine standard charts with
affine pairwise intersections, and the base is affine. The cartesian square is an argument.

Unlike `ofIsAffineHom`, the vanishing here is *not* available in degree `d`: clause (2) bounds
the cohomology above `n` and says nothing at `n`. See
`not_isZero_topDirectImage_of_not_isZero_cechHomology` for what the degree-`n` object being
nonzero reduces to. -/
def ofProjectiveSpace (n : ℕ) (R : CommRingCat.{u}) {X' Y' : Scheme.{u}}
    (g' : X' ⟶ projectiveSpaceOverRing n R) (f' : X' ⟶ Y') (g : Y' ⟶ Spec R)
    (sq : IsPullback g' f' ((projectiveSpaceOverRing n R) ↘ (Spec R)) g) :
    TopDegreeBaseChangeSituation.{u} where
  X := projectiveSpaceOverRing n R
  Y := Spec R
  f := (projectiveSpaceOverRing n R) ↘ (Spec R)
  d := n
  isCompact_X := inferInstance
  isQuasiSeparated_X := inferInstance
  isCompact_Y := inferInstance
  isQuasiSeparated_Y := inferInstance
  vanishes_above i hi F hF :=
    have := hF
    isZero_rightDerivedPlus_pushforward_of_lt n R i hi F
  X' := X'
  Y' := Y'
  g' := g'
  f' := f'
  g := g
  isPullback := sq

section Projections

variable (n : ℕ) (R : CommRingCat.{u}) {X' Y' : Scheme.{u}}
  (g' : X' ⟶ projectiveSpaceOverRing n R) (f' : X' ⟶ Y') (g : Y' ⟶ Spec R)
  (sq : IsPullback g' f' ((projectiveSpaceOverRing n R) ↘ (Spec R)) g)

/-- The top degree of `ofProjectiveSpace n R g' f' g sq` is `n`. -/
@[simp]
theorem ofProjectiveSpace_d : (ofProjectiveSpace n R g' f' g sq).d = n := rfl

/-- The morphism of `ofProjectiveSpace n R g' f' g sq` is the structure morphism of `ℙⁿ_R`. -/
@[simp]
theorem ofProjectiveSpace_f :
    (ofProjectiveSpace n R g' f' g sq).f = (projectiveSpaceOverRing n R) ↘ (Spec R) := rfl

/-- The base-changed morphism of `ofProjectiveSpace n R g' f' g sq` is `f'`. -/
@[simp]
theorem ofProjectiveSpace_f' : (ofProjectiveSpace n R g' f' g sq).f' = f' := rfl

end Projections

/-- **The projective situation with the canonical cartesian square over `g : Y' ⟶ Spec R`**,
which is the square [Stacks, Tag 0EX3] considers. -/
def ofProjectiveSpaceBaseChange (n : ℕ) (R : CommRingCat.{u}) {Y' : Scheme.{u}}
    (g : Y' ⟶ Spec R) : TopDegreeBaseChangeSituation.{u} :=
  ofProjectiveSpace n R (pullback.fst ((projectiveSpaceOverRing n R) ↘ (Spec R)) g)
    (pullback.snd _ _) g (IsPullback.of_hasPullback _ _)

/-- **The projective situation with the identity square**, in which the base-changed morphism is
the structure morphism of `ℙⁿ_R` itself. -/
def ofProjectiveSpaceSelf (n : ℕ) (R : CommRingCat.{u}) : TopDegreeBaseChangeSituation.{u} :=
  ofProjectiveSpace n R (𝟙 _) ((projectiveSpaceOverRing n R) ↘ (Spec R)) (𝟙 _)
    (IsPullback.of_horiz_isIso ⟨by simp⟩)

/-- The top degree of `ofProjectiveSpaceSelf n R` is `n`. -/
@[simp]
theorem ofProjectiveSpaceSelf_d (n : ℕ) (R : CommRingCat.{u}) :
    (ofProjectiveSpaceSelf n R).d = n := rfl

/-- The base-changed morphism of `ofProjectiveSpaceSelf n R` is the structure morphism of
`ℙⁿ_R`. -/
@[simp]
theorem ofProjectiveSpaceSelf_f' (n : ℕ) (R : CommRingCat.{u}) :
    (ofProjectiveSpaceSelf n R).f' = (projectiveSpaceOverRing n R) ↘ (Spec R) := rfl

/-- **The degree-`d` object of the projective situation is nonzero as soon as `Hⁿ(ℙⁿ_R, ℱ)`
is.** The degree-`d` object that the three conclusions of [Stacks, Tag 0EX3] are about is here
`Rⁿ f_* ℱ` for the structure morphism of `ℙⁿ_R`, and over the affine base `Spec R` its vanishing
is the vanishing of `Hⁿ(ℙⁿ_R, ℱ)` by [Stacks, Tag 01XK].

This is the positive-degree counterpart of
`…ofIsAffineHom`'s `not_isZero_topDirectImage_unit`, which is available only at `d = 0`. -/
theorem not_isZero_topDirectImage_of_not_isZero_Hgroup (n : ℕ) (R : CommRingCat.{u})
    (F : (projectiveSpaceOverRing n R).Modules) [F.IsQuasicoherent]
    (h : ¬ IsZero (Hgroup (projectiveSpaceOverRing n R).ringCatSheaf ⊤ n F)) :
    ¬ IsZero (((Scheme.Modules.pushforward (ofProjectiveSpaceSelf n R).f').rightDerivedPlus
      (((ofProjectiveSpaceSelf n R).d : ℕ) : ℤ)).obj F) :=
  fun hz => h (isZero_Hgroup_of_isZero_rightDerivedPlus_pushforward n R n F hz)

/-- **Non-degeneracy of the projective situation, reduced to an explicit complex.** The
degree-`d` object of `ofProjectiveSpaceSelf n R` is nonzero as soon as the degree-`n` homology of
the Čech cochain complex of the `n + 1` standard charts is nonzero on some quasi-coherent module.

This is the whole of the question left open about this situation, and the statement mentions
neither a situation, nor a derived category, nor a higher direct image: it is a statement about
the homology of a finite complex of modules of sections over the standard opens. The witness the
source uses is the twist `𝒪(-n-1)`; its cohomology is [Stacks, Tag 01XT], which is not in this
development. -/
theorem not_isZero_topDirectImage_of_not_isZero_cechHomology (n : ℕ) (R : CommRingCat.{u})
    (F : (projectiveSpaceOverRing n R).Modules) [F.IsQuasicoherent]
    (h : ¬ IsZero ((cechComplex.{u, u, u, u} (⊤ : (projectiveSpaceOverRing n R).Opens)
      (chartAtUniverse n R) (iSup_chartAtUniverse_eq_top n R).symm F).homology n)) :
    ¬ IsZero (((Scheme.Modules.pushforward (ofProjectiveSpaceSelf n R).f').rightDerivedPlus
      (((ofProjectiveSpaceSelf n R).d : ℕ) : ℤ)).obj F) :=
  not_isZero_topDirectImage_of_not_isZero_Hgroup n R F
    fun hH => h ((isZero_Hgroup_iff_isZero_cechHomology_chart n R F n).mp hH)

/-- **The vacuity control: conclusion (a) of [Stacks, Tag 0EX3] at a situation of top degree
`n`.** For every cartesian square

```
X' --g'--> ℙⁿ_R
|f'        |
v          v
Y' --g---> Spec R
```

the higher direct images of a quasi-coherent module along the base-changed morphism `f'` vanish
above `n`.

Its statement mentions no situation; it is obtained by instantiating
`…TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_baseChange` at `ofProjectiveSpace`, so
it is a measurement that the family says something at positive top degree. It is also not a
consequence of [Stacks, Tag 01YS] clause (2), which is stated for projective space over a
*ring*: here `Y'` is an arbitrary scheme and `X'` is identified with projective space over `Y'`
by no declaration in the development. -/
theorem isZero_rightDerivedPlus_pushforward_baseChange_projectiveSpace
    (n : ℕ) (R : CommRingCat.{u}) {X' Y' : Scheme.{u}}
    (g' : X' ⟶ projectiveSpaceOverRing n R) (f' : X' ⟶ Y') (g : Y' ⟶ Spec R)
    (sq : IsPullback g' f' ((projectiveSpaceOverRing n R) ↘ (Spec R)) g)
    (i : ℤ) (hi : (n : ℤ) < i) (F' : X'.Modules) [F'.IsQuasicoherent] :
    IsZero (((Scheme.Modules.pushforward f').rightDerivedPlus i).obj F') := by
  have : (show (ofProjectiveSpace n R g' f' g sq).X'.Modules from F').IsQuasicoherent :=
    inferInstanceAs F'.IsQuasicoherent
  exact TopDegreeBaseChange.isZero_rightDerivedPlus_pushforward_baseChange
    (ofProjectiveSpace n R g' f' g sq) i hi
    (show (ofProjectiveSpace n R g' f' g sq).X'.Modules from F')

/-- **A second control, over an affine base.** The absolute cohomology of the source of any
base change of `ℙⁿ_R ⟶ Spec R` along a morphism from an affine scheme vanishes above `n`.

This is the family's `isZero_cohomology_of_lt` — the sentence the source's proof of conclusion
(b) opens with — instantiated at `ofProjectiveSpace`; as above, its statement mentions no
situation. -/
theorem isZero_cohomology_baseChange_projectiveSpace
    (n : ℕ) (R : CommRingCat.{u}) {X' Y' : Scheme.{u}}
    (g' : X' ⟶ projectiveSpaceOverRing n R) (f' : X' ⟶ Y') (g : Y' ⟶ Spec R)
    (sq : IsPullback g' f' ((projectiveSpaceOverRing n R) ↘ (Spec R)) g) [IsAffine Y']
    (i : ℤ) (hi : (n : ℤ) < i) (F' : X'.Modules) [F'.IsQuasicoherent] :
    IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections X').rightDerivedPlus i).obj
      F') := by
  have h1 : IsAffine (ofProjectiveSpace n R g' f' g sq).Y' := ‹IsAffine Y'›
  have h2 : (show (ofProjectiveSpace n R g' f' g sq).X'.Modules from F').IsQuasicoherent :=
    inferInstanceAs F'.IsQuasicoherent
  exact (ofProjectiveSpace n R g' f' g sq).isZero_cohomology_of_lt i hi
    (show (ofProjectiveSpace n R g' f' g sq).X'.Modules from F')

end TopDegreeBaseChangeSituation

end Stacks.AlgebraicGeometry

end

end
