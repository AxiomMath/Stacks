module

public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.ModelComparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveCohomology.WeightSplittingNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.InjectiveVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Čech complex of a twist on projective space, in terms of the localizations

Let `R` be a commutative ring. The proof of [Stacks, Tag 01XT] computes the cohomology of a
twist `𝒪(d)` on `Proj R[T₀, …, Tₙ]` from the Čech complex of the `n + 1` standard coordinate
charts. Three files built the pieces of that complex:

* `StacksFrontier/AlgebraicGeometry/ProjectiveCohomology/TwistWeights.lean` identified the
  sections of `𝒪(d)` over an intersection of standard charts with the degree-`d` part of a
  localization of the polynomial ring, and gave its Laurent monomial basis;
* `StacksFrontier/AlgebraicGeometry/ProjectiveCohomology/WeightSplitting.lean` split that
  degree-`d` part along the `ℤ^{n+1}`-valued Laurent weight, and built the localization map
  `Stacks.ProjectiveCohomology.chartTransition` between two of them, weight by weight;
* `StacksFrontier/AlgebraicGeometry/ProjectiveCohomology/WeightSplittingNaturality.lean`
  proved that the restriction maps of `𝒪(d)` between standard opens *are* those localization
  maps.

What was still missing is the crossing from those three to
`Stacks.Cohomology.CechSheaf.cechComplex` itself — the complex whose homology
`Stacks.ProjectiveCohomology.projModelRightDerivedCechIso` identifies with the cohomology of
`𝒪(d)`. That complex is Mathlib's `CategoryTheory.cechComplexFunctor` applied to the sections
presheaf over the *slice category* `Over ⊤`, valued in modules over the ring of global
sections. This file supplies the crossing, and with it the splitting of the Čech complex.

**The terms.** `Stacks.ProjectiveCohomology.cechTwistTermEquiv` identifies the degree-`p` term
with the product, over the tuples `x` of `p + 1` coordinate indices, of the degree-`d` parts
`Stacks.ProjectiveCohomology.twistWeightSpan` of the localizations. Nothing has to be
constructed for the slice and change-of-scalars layers: the underlying abelian group of
`Stacks.Cohomology.CechSheaf.sectionsPresheaf ⊤ 𝒪(d)` at an object of the slice is the group of
sections of `𝒪(d)` over the underlying open, and the presheaf restriction of the former is the
sheaf restriction of the latter, both by `rfl`. The only comparison is the equality of opens
`Stacks.ProjectiveCohomology.interCoverObject_left_eq`, and it is consumed as an inequality in
each direction through `Stacks.Cohomology.Basis.res`, so no `eqToHom` appears anywhere below.

**The differential.** `Stacks.ProjectiveCohomology.cechTwistComp_cechTwistD` reads the Čech
differential through that identification: at each tuple it is the alternating sum, over the
faces of the tuple, of `Stacks.ProjectiveCohomology.chartTransitionWeight`, the localization
map restricted to the degree-`d` parts. Since those maps are weight-diagonal, the Čech
differential is weight-diagonal:
`Stacks.ProjectiveCohomology.cechTwistComp_cechTwistD_mem_twistChartWeight`.

## Main definitions

* `Stacks.ProjectiveCohomology.cechTwistComplex`: the Čech complex of `𝒪(d)` for the `n + 1`
  standard coordinate charts, in the spelling the existing cohomology comparisons use.
* `Stacks.ProjectiveCohomology.chartIndices`: the tuple of coordinate indices a Čech index
  selects.
* `Stacks.ProjectiveCohomology.cechTwistComp` and
  `Stacks.ProjectiveCohomology.cechTwistMk`: the components of a Čech cochain, as elements of
  the degree-`d` parts of the localizations, and a cochain with prescribed components.
* `Stacks.ProjectiveCohomology.chartTransitionWeight`: the localization map between two Čech
  terms, restricted to the degree-`d` parts.
* `Stacks.ProjectiveCohomology.twistChartWeight`: the weight-`e` piece of a degree-`d` part,
  as a submodule of it.

## Main results

* `Stacks.ProjectiveCohomology.inter_basicOpenXAtUniverse` and
  `Stacks.ProjectiveCohomology.interCoverObject_left_eq`: **the intersection of standard
  coordinate charts selected by a Čech index is the standard open of the product of the
  corresponding coordinates**, both in the opens of the scheme and in the slice category.
* `Stacks.ProjectiveCohomology.cechTwist_ext` and
  `Stacks.ProjectiveCohomology.cechTwistComp_cechTwistMk`: a Čech cochain is determined by its
  components, and every family of components occurs.
* `Stacks.ProjectiveCohomology.cechTwistTermEquiv`: **the degree-`p` term of the Čech complex
  of `𝒪(d)` is the product of the degree-`d` parts of the localizations.**
* `Stacks.ProjectiveCohomology.cechTwistComp_cechTwistD`: **the Čech differential is the
  alternating sum of the localization maps.**
* `Stacks.ProjectiveCohomology.cechTwistComp_cechTwistD_mem_twistChartWeight`: **the Čech
  differential is diagonal for the Laurent weight splitting.**

## Implementation notes

**No attribute for tag 01XT is attached, and the omission is deliberate**, for the same reason
as in `TwistWeights.lean`, `WeightSplitting.lean` and `WeightSplittingNaturality.lean`: that tag
is a statement about the cohomology groups `H^q(ℙⁿ_R, 𝒪(d))`, and nothing here computes a
homology group. What is proved is that the complex which computes them is, term by term and map
by map, built from the localizations of the polynomial ring, and that it splits along the
Laurent weight. The attribute token is deliberately not spelled out in this comment: a
comment-blind attribute grep reads a spelled token as coverage.

**Why the proofs are in term mode.** Every statement below that mentions a Čech term crosses
the seam between `AlgebraicGeometry.ProjectiveSpectrum.Proj.structureSheaf`, which is a
`TopCat.Sheaf`, and the `CategoryTheory.Sheaf` over `TopologicalSpace.Opens.grothendieckTopology`
that `Stacks.Cohomology.CechSheaf.cechComplex` is stated over. The two are definitionally equal
but not at the `implicit` transparency level that `rw` checks its motive against, so `rw` on
such a goal fails, either as a deterministic `isDefEq` timeout at 200000 heartbeats or as an
outright refusal naming that seam. `Eq.trans`, `congrArg` and `Subtype.ext` form
no motive and go through every time; `res_sum`, `res_zsmul` and `res_res` are therefore applied
as terms rather than rewritten with. No heartbeat option is raised anywhere in this file.

**What the element layer is reused from.** The components and the differential are taken from
`StacksFrontier/Topology/Sheaves/Cohomology/CechOfSheavesOfModules/InjectiveVanishing.lean` —
`rawcomp`, `mcomp`, `mmk`, `md`, `rawcomp_md`, `mcomp_mmk`, `mcech_ext` and
`inter_coverObject_left` — rather than rebuilt. That layer was
written for the Čech acyclicity of an injective sheaf of modules, and it is model-free: nothing
in it mentions projective space.
`StacksFrontier/AlgebraicGeometry/Cohomology/Cech/StandardCoverVanishing.lean` is the same crossing at
an affine cover, done with an isomorphism of terms instead of elementwise; the elementwise route is
taken here because the weight splitting of `WeightSplitting.lean` is a statement about elements
of the localizations.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
-/

@[expose] public noncomputable section


open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpectrum.Proj CategoryTheory
open CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.CechSheaf
open Stacks.Cohomology.Basis (res res_id res_res res_zero res_sum res_zsmul)
open Stacks.PartialLaurent

universe u

namespace Stacks.ProjectiveCohomology

attribute [local instance] MvPolynomial.gradedAlgebra

section CechTwist

variable (R : Type u) [CommRing R] (n : ℕ) (d : ℤ)

/-- The tuple of coordinate indices a Čech index of the standard cover selects. -/
abbrev chartIndices {n p : ℕ} (x : Fin (p + 1) → ULift.{u} (Fin (n + 1))) :
    Fin (p + 1) → Fin (n + 1) := fun j => (x j).down

/-- The presheaf of abelian groups of sections of the twist `𝒪(d)` on `Proj R[T₀, …, Tₙ]`. -/
abbrev twistSections :
    ((AlgebraicGeometry.Proj (polyGrading R n)).Opens)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  abSections (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)

/-- **The Čech complex of `𝒪(d)` for the `n + 1` standard coordinate charts of
`Proj R[T₀, …, Tₙ]`**, the complex whose homology is the cohomology computed by
[Stacks, Tag 01XT]. -/
abbrev cechTwistComplex :
    CochainComplex
      (ModuleCat.{u}
        (SectionRing (AlgebraicGeometry.Proj (polyGrading R n)).ringCatSheaf ⊤)) ℕ :=
  cechComplex.{u, u, u, u} (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
    (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)

/-- The raw component of a Čech cochain of `𝒪(d)` at a tuple. -/
abbrev twistRawcomp {p : ℕ} (s : ToType ((cechTwistComplex R n d).X p))
    (x : Fin (p + 1) → ULift.{u} (Fin (n + 1))) :
    ToType ((twistSections R n d).obj (op (inter (coverObject (basicOpenXAtUniverse R n)
      (iSup_basicOpenXAtUniverse_eq_top R n).symm) x).left)) :=
  rawcomp (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
    (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) s x

/-- The component of a Čech cochain of `𝒪(d)` at a tuple, as a section over the intersection
of the charts selected by that tuple. -/
abbrev twistMcomp {p : ℕ} (s : ToType ((cechTwistComplex R n d).X p))
    (x : Fin (p + 1) → ULift.{u} (Fin (n + 1))) :
    ToType ((twistSections R n d).obj (op (inter (basicOpenXAtUniverse R n) x))) :=
  mcomp (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
    (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) s x

/-- The differential of the Čech complex of `𝒪(d)`, on elements. -/
abbrev cechTwistD {p : ℕ} (s : ToType ((cechTwistComplex R n d).X p)) :
    ToType ((cechTwistComplex R n d).X (p + 1)) :=
  md (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
    (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) s

/-! ### The intersections of the standard charts are standard opens -/

/-- The intersection of standard coordinate charts selected by a Čech index is the standard
open of the product of the corresponding coordinates. -/
@[ega "II 2.3.3" "special case"]
theorem inter_basicOpenXAtUniverse {p : ℕ} (x : Fin (p + 1) → ULift.{u} (Fin (n + 1))) :
    inter (basicOpenXAtUniverse R n) x =
      ProjectiveSpectrum.basicOpen (polyGrading R n)
        (∏ j, MvPolynomial.X (chartIndices x j)) := by
  rw [inter_eq_iInf]
  exact iInf_projectiveSpectrum_basicOpen_X R (chartIndices x)

/-- **The open underlying the product in the slice category is that same standard open.** This
is the only comparison of opens the crossing from the Čech complex to the localizations needs,
and it is consumed as an inequality in each direction rather than as an `eqToHom`. -/
theorem interCoverObject_left_eq {p : ℕ} (x : Fin (p + 1) → ULift.{u} (Fin (n + 1))) :
    (inter (coverObject (basicOpenXAtUniverse R n)
        (iSup_basicOpenXAtUniverse_eq_top R n).symm) x).left =
      ProjectiveSpectrum.basicOpen (polyGrading R n)
        (∏ j, MvPolynomial.X (chartIndices x j)) :=
  (inter_coverObject_left (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
      (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm x).trans
    (inter_basicOpenXAtUniverse R n x)

/-- Omitting an index of a tuple enlarges the chart intersection it selects. -/
theorem range_chartIndices_subset {p : ℕ} (y : Fin (p + 2) → ULift.{u} (Fin (n + 1)))
    (a : Fin (p + 2)) :
    Set.range (chartIndices (y ∘ a.succAbove)) ⊆ Set.range (chartIndices y) := by
  rintro _ ⟨j, rfl⟩
  exact ⟨a.succAbove j, rfl⟩

/-! ### `chartTransition` on the degree-`d` parts -/

/-- **The localization map between two Čech terms, restricted to the degree-`d` parts.** This is
the map the Čech differential of [Stacks, Tag 01XT] is an alternating sum of, and
`Stacks.ProjectiveCohomology.chartTransition_mem_chartWeight` says it is diagonal for the
Laurent weight. -/
def chartTransitionWeight {q r : ℕ} (s : Fin (r + 1) → Fin (n + 1))
    (t : Fin (q + 1) → Fin (n + 1)) (hst : Set.range s ⊆ Set.range t) :
    twistWeightSpan R s d →+ twistWeightSpan R t d where
  toFun z := ⟨chartTransition R s t hst (z : chartRing R s),
    chartTransition_mem_twistWeightSpan R s t hst d z.2⟩
  map_zero' := Subtype.ext (map_zero (chartTransition R s t hst))
  map_add' _ _ := Subtype.ext (map_add (chartTransition R s t hst) _ _)

/-- The underlying element of `chartTransitionWeight R n d s t hst z` is the image of `z` under
`chartTransition R s t hst`. -/
@[simp]
theorem coe_chartTransitionWeight {q r : ℕ} (s : Fin (r + 1) → Fin (n + 1))
    (t : Fin (q + 1) → Fin (n + 1)) (hst : Set.range s ⊆ Set.range t)
    (z : twistWeightSpan R s d) :
    ((chartTransitionWeight R n d s t hst z : twistWeightSpan R t d) :
        chartRing R t) =
      chartTransition R s t hst (z : chartRing R s) := rfl

/-- **The degree-`d` localization map carries each Laurent weight piece into the piece of the
same weight.** This is `Stacks.ProjectiveCohomology.chartTransition_mem_chartWeight` for the
bundled map. -/
theorem chartTransitionWeight_mem_chartWeight {q r : ℕ} (s : Fin (r + 1) → Fin (n + 1))
    (t : Fin (q + 1) → Fin (n + 1)) (hst : Set.range s ⊆ Set.range t)
    (e : Fin (n + 1) →₀ ℤ) {z : twistWeightSpan R s d}
    (hz : (z : chartRing R s) ∈ chartWeight R s e) :
    ((chartTransitionWeight R n d s t hst z : twistWeightSpan R t d) : chartRing R t) ∈
      chartWeight R t e :=
  chartTransition_mem_chartWeight R s t hst e hz

/-! ### The components of a Čech cochain, as elements of the localizations -/

/-- **The component of a Čech cochain of `𝒪(d)` at a tuple**, read as an element of the
degree-`d` part of `R[T₀, …, Tₙ, 1/(T_{i₀} ⋯ T_{i_p})]`. -/
def cechTwistComp {p : ℕ} (s : ToType ((cechTwistComplex R n d).X p))
    (x : Fin (p + 1) → ULift.{u} (Fin (n + 1))) :
    twistWeightSpan R (chartIndices x) d :=
  sectionsTwistProdXEquivWeightSpan R (chartIndices x) d
    (res (twistSections R n d) (interCoverObject_left_eq R n x).ge (twistRawcomp R n d s x))

/-- Taking components is additive. -/
theorem cechTwistComp_add {p : ℕ} (s t : ToType ((cechTwistComplex R n d).X p))
    (x : Fin (p + 1) → ULift.{u} (Fin (n + 1))) :
    cechTwistComp R n d (s + t) x = cechTwistComp R n d s x + cechTwistComp R n d t x := by
  refine Eq.trans (congrArg (sectionsTwistProdXEquivWeightSpan R (chartIndices x) d)
    (Eq.trans (congrArg (res (twistSections R n d) (interCoverObject_left_eq R n x).ge)
      (map_add (ConcreteCategory.hom (π (coverObject (basicOpenXAtUniverse R n)
        (iSup_basicOpenXAtUniverse_eq_top R n).symm)
        (sectionsPresheaf ⊤ (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)) p x))
        s t))
      (map_add _ _ _))) ?_
  exact map_add _ _ _

/-- The component of a Čech cochain, in the `mcomp` spelling of
`StacksFrontier/Topology/Sheaves/Cohomology/CechOfSheavesOfModules/InjectiveVanishing.lean`. -/
theorem cechTwistComp_eq_mcomp {p : ℕ} (s : ToType ((cechTwistComplex R n d).X p))
    (x : Fin (p + 1) → ULift.{u} (Fin (n + 1))) :
    cechTwistComp R n d s x =
      sectionsTwistProdXEquivWeightSpan R (chartIndices x) d
        (res (twistSections R n d) (inter_basicOpenXAtUniverse R n x).ge
          (twistMcomp R n d s x)) :=
  congrArg (sectionsTwistProdXEquivWeightSpan R (chartIndices x) d)
    (res_res (twistSections R n d) (inter_basicOpenXAtUniverse R n x).ge
      (inter_coverObject_left (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
        (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm x).ge
      (twistRawcomp R n d s x)).symm

/-- **A Čech cochain of `𝒪(d)` is determined by its components.** -/
theorem cechTwist_ext {p : ℕ} (s t : ToType ((cechTwistComplex R n d).X p))
    (h : ∀ x, cechTwistComp R n d s x = cechTwistComp R n d t x) : s = t :=
  mcech_ext (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
    (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) s t fun x =>
    have h2 : res (twistSections R n d) (inter_basicOpenXAtUniverse R n x).ge
          (twistMcomp R n d s x) =
        res (twistSections R n d) (inter_basicOpenXAtUniverse R n x).ge
          (twistMcomp R n d t x) :=
      (sectionsTwistProdXEquivWeightSpan R (chartIndices x) d).injective
        (((cechTwistComp_eq_mcomp R n d s x).symm.trans (h x)).trans
          (cechTwistComp_eq_mcomp R n d t x))
    (res_id (twistSections R n d) (twistMcomp R n d s x)).symm.trans
      ((res_res (twistSections R n d) (inter_basicOpenXAtUniverse R n x).le
            (inter_basicOpenXAtUniverse R n x).ge (twistMcomp R n d s x)).symm.trans
        ((congrArg (res (twistSections R n d) (inter_basicOpenXAtUniverse R n x).le) h2).trans
          ((res_res (twistSections R n d) (inter_basicOpenXAtUniverse R n x).le
              (inter_basicOpenXAtUniverse R n x).ge (twistMcomp R n d t x)).trans
            (res_id (twistSections R n d) (twistMcomp R n d t x)))))

/-- A Čech cochain of `𝒪(d)` with prescribed components. -/
def cechTwistMk {p : ℕ}
    (g : ∀ x : Fin (p + 1) → ULift.{u} (Fin (n + 1)), twistWeightSpan R (chartIndices x) d) :
    ToType ((cechTwistComplex R n d).X p) :=
  mmk (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
    (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm
    (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d)
    fun x => res (twistSections R n d) (inter_basicOpenXAtUniverse R n x).le
      ((sectionsTwistProdXEquivWeightSpan R (chartIndices x) d).symm (g x))

/-- The Čech cochain with prescribed components has those components. -/
theorem cechTwistComp_cechTwistMk {p : ℕ}
    (g : ∀ x : Fin (p + 1) → ULift.{u} (Fin (n + 1)), twistWeightSpan R (chartIndices x) d)
    (x : Fin (p + 1) → ULift.{u} (Fin (n + 1))) :
    cechTwistComp R n d (cechTwistMk R n d g) x = g x :=
  (cechTwistComp_eq_mcomp R n d (cechTwistMk R n d g) x).trans
    ((congrArg
        (fun z => sectionsTwistProdXEquivWeightSpan R (chartIndices x) d
          (res (twistSections R n d) (inter_basicOpenXAtUniverse R n x).ge z))
        (mcomp_mmk (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
          (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) _ x)).trans
      ((congrArg (sectionsTwistProdXEquivWeightSpan R (chartIndices x) d)
          ((res_res (twistSections R n d) (inter_basicOpenXAtUniverse R n x).ge
              (inter_basicOpenXAtUniverse R n x).le _).trans
            (res_id (twistSections R n d) _))).trans
        ((sectionsTwistProdXEquivWeightSpan R (chartIndices x) d).apply_symm_apply (g x))))

/-- **The degree-`p` term of the Čech complex of `𝒪(d)` is the product, over the tuples of
`p + 1` coordinate indices, of the degree-`d` parts of the localizations.** This is the
identification of the Čech terms of [Stacks, Tag 01XT] with the modules the Laurent weight
splitting of `WeightSplitting.lean` is stated about. -/
def cechTwistTermEquiv (p : ℕ) :
    ToType ((cechTwistComplex R n d).X p) ≃+
      (∀ x : Fin (p + 1) → ULift.{u} (Fin (n + 1)), twistWeightSpan R (chartIndices x) d) where
  toFun s := fun x => cechTwistComp R n d s x
  invFun g := cechTwistMk R n d g
  left_inv _ := cechTwist_ext R n d _ _ fun x => cechTwistComp_cechTwistMk R n d _ x
  right_inv g := funext fun x => cechTwistComp_cechTwistMk R n d g x
  map_add' s t := funext fun x => cechTwistComp_add R n d s t x

/-! ### The differential is the alternating sum of the localization maps -/

/-- **Restriction of a section of `𝒪(d)` between two chart intersections is
`chartTransition`**, in the `res` spelling the Čech element layer produces and on the
degree-`d` parts. -/
theorem sectionsTwistProdXEquivWeightSpan_res {q r : ℕ}
    (s : Fin (r + 1) → Fin (n + 1)) (t : Fin (q + 1) → Fin (n + 1))
    (hst : Set.range s ⊆ Set.range t)
    (z : ToType ((twistSections R n d).obj
      (op (ProjectiveSpectrum.basicOpen (polyGrading R n) (∏ j, MvPolynomial.X (s j)))))) :
    sectionsTwistProdXEquivWeightSpan R t d
        (res (twistSections R n d) (basicOpen_prod_X_le R s t hst) z) =
      chartTransitionWeight R n d s t hst (sectionsTwistProdXEquivWeightSpan R s d z) :=
  Subtype.ext (coe_sectionsTwistProdXEquivWeightSpan_map_homOfLE R s t hst d z)

/-- The restricted raw component of a Čech differential is the alternating sum of the
restrictions of the restricted raw components. -/
theorem res_twistRawcomp_cechTwistD {p : ℕ} (s : ToType ((cechTwistComplex R n d).X p))
    (y : Fin (p + 2) → ULift.{u} (Fin (n + 1))) :
    res (twistSections R n d) (interCoverObject_left_eq R n y).ge
        (twistRawcomp R n d (cechTwistD R n d s) y) =
      ∑ a : Fin (p + 2), (-1 : ℤ) ^ (a : ℕ) •
        res (twistSections R n d)
          (basicOpen_prod_X_le R (chartIndices (y ∘ a.succAbove)) (chartIndices y)
            (range_chartIndices_subset n y a))
          (res (twistSections R n d) (interCoverObject_left_eq R n (y ∘ a.succAbove)).ge
            (twistRawcomp R n d s (y ∘ a.succAbove))) := by
  refine Eq.trans (congrArg
    (res (twistSections R n d) (interCoverObject_left_eq R n y).ge)
    (rawcomp_md (⊤ : (AlgebraicGeometry.Proj (polyGrading R n)).Opens)
      (basicOpenXAtUniverse R n) (iSup_basicOpenXAtUniverse_eq_top R n).symm
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R n) d) s y)) ?_
  refine Eq.trans (res_sum (twistSections R n d)
    (interCoverObject_left_eq R n y).ge Finset.univ _) ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Eq.trans (res_zsmul (twistSections R n d) (interCoverObject_left_eq R n y).ge _ _) ?_
  refine Eq.trans (congrArg (fun z => ((-1 : ℤ) ^ (a : ℕ)) • z)
    (res_res (twistSections R n d) (interCoverObject_left_eq R n y).ge _ _)) ?_
  exact (congrArg (fun z => ((-1 : ℤ) ^ (a : ℕ)) • z)
    (res_res (twistSections R n d)
      (basicOpen_prod_X_le R (chartIndices (y ∘ a.succAbove)) (chartIndices y)
        (range_chartIndices_subset n y a))
      (interCoverObject_left_eq R n (y ∘ a.succAbove)).ge _)).symm

/-- **The Čech differential of `𝒪(d)` is the alternating sum of the localization maps.**
Read through the identification of the Čech terms with the degree-`d` parts of the
localizations, the differential of the Čech complex of the `n + 1` standard coordinate charts
of `Proj R[T₀, …, Tₙ]` is, at each tuple, the alternating sum over the faces of that tuple of
the maps `Stacks.ProjectiveCohomology.chartTransitionWeight`.

Together with `Stacks.ProjectiveCohomology.cechTwistTermEquiv` this is the identification of the
Čech complex of [Stacks, Tag 01XT] with a complex built from the localizations alone, and with
`Stacks.ProjectiveCohomology.chartTransitionWeight_mem_chartWeight` it says the Čech
differential is diagonal for the Laurent weight splitting. -/
theorem cechTwistComp_cechTwistD {p : ℕ} (s : ToType ((cechTwistComplex R n d).X p))
    (y : Fin (p + 2) → ULift.{u} (Fin (n + 1))) :
    cechTwistComp R n d (cechTwistD R n d s) y =
      ∑ a : Fin (p + 2), (-1 : ℤ) ^ (a : ℕ) •
        chartTransitionWeight R n d (chartIndices (y ∘ a.succAbove)) (chartIndices y)
          (range_chartIndices_subset n y a) (cechTwistComp R n d s (y ∘ a.succAbove)) := by
  refine Eq.trans (congrArg (sectionsTwistProdXEquivWeightSpan R (chartIndices y) d)
    (res_twistRawcomp_cechTwistD R n d s y)) ?_
  refine Eq.trans (map_sum (sectionsTwistProdXEquivWeightSpan R (chartIndices y) d) _
    Finset.univ) ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Eq.trans (map_zsmul (sectionsTwistProdXEquivWeightSpan R (chartIndices y) d) _ _) ?_
  exact congrArg (fun z : twistWeightSpan R (chartIndices y) d => ((-1 : ℤ) ^ (a : ℕ)) • z)
    (sectionsTwistProdXEquivWeightSpan_res R n d (chartIndices (y ∘ a.succAbove))
      (chartIndices y) (range_chartIndices_subset n y a) _)

/-! ### The weight splitting of the Čech complex -/

/-- **The weight-`e` piece of the degree-`d` part of a Čech term**, as a submodule of that
degree-`d` part. This is `Stacks.ProjectiveCohomology.chartWeight` transported inside the
module the Čech term has been identified with. -/
def twistChartWeight {r : ℕ} (s : Fin (r + 1) → Fin (n + 1)) (e : Fin (n + 1) →₀ ℤ) :
    Submodule R (twistWeightSpan R s d) :=
  (chartWeight R s e).comap (twistWeightSpan R s d).subtype

/-- An element of the degree-`d` part lies in `twistChartWeight R n d s e` if and only if, as an
element of `chartRing R s`, it lies in `chartWeight R s e`. -/
theorem mem_twistChartWeight {r : ℕ} (s : Fin (r + 1) → Fin (n + 1)) (e : Fin (n + 1) →₀ ℤ)
    (z : twistWeightSpan R s d) :
    z ∈ twistChartWeight R n d s e ↔ (z : chartRing R s) ∈ chartWeight R s e := Iff.rfl

/-- The localization map between two Čech terms carries each weight piece into the piece of the
same weight. -/
theorem chartTransitionWeight_mem_twistChartWeight {q r : ℕ} (s : Fin (r + 1) → Fin (n + 1))
    (t : Fin (q + 1) → Fin (n + 1)) (hst : Set.range s ⊆ Set.range t) (e : Fin (n + 1) →₀ ℤ)
    {z : twistWeightSpan R s d} (hz : z ∈ twistChartWeight R n d s e) :
    chartTransitionWeight R n d s t hst z ∈ twistChartWeight R n d t e :=
  chartTransition_mem_chartWeight R s t hst e hz

/-- The element differential of the Čech complex of `𝒪(d)` is the differential of that complex
applied to an element. -/
theorem cechTwistD_eq {p : ℕ} (s : ToType ((cechTwistComplex R n d).X p)) :
    cechTwistD R n d s =
      ConcreteCategory.hom ((cechTwistComplex R n d).d p (p + 1)) s := rfl

/-- **The Čech differential of `𝒪(d)` is diagonal for the Laurent weight splitting.** If every
component of a Čech cochain lies in the weight-`e` piece of its term, then so does every
component of its differential. With
`Stacks.ProjectiveCohomology.iSup_chartWeight_eq_twistWeightSpan` and
`Stacks.ProjectiveCohomology.iSupIndep_chartWeight`, which decompose each term over the
Laurent weights of total degree `d`, this is the splitting of the Čech complex of
[Stacks, Tag 01XT] along the Laurent weight. -/
theorem cechTwistComp_cechTwistD_mem_twistChartWeight {p : ℕ}
    (s : ToType ((cechTwistComplex R n d).X p)) (e : Fin (n + 1) →₀ ℤ)
    (hs : ∀ x : Fin (p + 1) → ULift.{u} (Fin (n + 1)),
      cechTwistComp R n d s x ∈ twistChartWeight R n d (chartIndices x) e)
    (y : Fin (p + 2) → ULift.{u} (Fin (n + 1))) :
    cechTwistComp R n d (cechTwistD R n d s) y ∈
      twistChartWeight R n d (chartIndices y) e := by
  rw [cechTwistComp_cechTwistD]
  refine Submodule.sum_mem _ fun a _ => ?_
  exact Submodule.smul_of_tower_mem _ _
    (chartTransitionWeight_mem_twistChartWeight R n d _ _
      (range_chartIndices_subset n y a) e (hs (y ∘ a.succAbove)))


end CechTwist

end Stacks.ProjectiveCohomology

end
