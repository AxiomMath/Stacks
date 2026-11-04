module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeBasis
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeChartOver
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeChartSquare
public import StacksFrontier.AlgebraicGeometry.Descent.RelativeGluingOverBasis
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistGlue.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistGradedAlgebra.Basic

/-!
# Tag 02NC over a base scheme: the glueing

Tag 02NC's proof is *"this is the identity map when `ℒ ≅ 𝒪_S`; in general choose an open covering
of `S` such that `ℒ` is trivialized over the pieces and glue the corresponding maps."* This file
performs that glueing, over the basis of affine opens of `S` trivializing `ℒ`
(`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.isBasis_trivializingOpens`), and produces the
tag's canonical isomorphism `Proj_S(ℬ) ≅ Proj_S(𝒜)` over `S`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.basisSection`: the trivializing section chosen
  at a member of the basis.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.basisComparison`: the comparison of Tag 02NC
  over a member of the basis, `Proj ℬ(V) ⟶ Proj 𝒜(V)`.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.twistGluingData`: the glueing datum of Tag
  01LH over that basis — the charts of `Proj_S(ℬ)`, with the chart transitions of Tag 01NO.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.gluingTwist` and `gluingBase`: `Proj_S(ℬ)`
  with its own charts, and `Proj_S(𝒜)` with its charts precomposed with the comparisons, as two
  solutions of that one glueing problem.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.relativeTwistIso`: **the canonical
  isomorphism `Proj_S(ℬ) ≅ Proj_S(𝒜)`.**
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.relativeTwistHom`: **the tag's
  `g : Proj_S(𝒜) ⟶ Proj_S(ℬ)`**, in the direction the source states it — the inverse of
  `relativeTwistIso`, hence an isomorphism.

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.projMap_psiSectionAt_eq_of_trivializesPower`:
  the chart comparison depends only on the open, not on the trivializing section chosen there.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.projInclusionMap_comp_basisComparison`: the
  comparisons at the chosen sections commute with the chart transitions, with no coherence
  condition on the choice.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.existsUnique_relativeTwistIsoOver`: **Tag
  02NC's canonical isomorphism**, as the unique isomorphism `Proj_S(ℬ) ≅ Proj_S(𝒜)` over `S`
  restricting to the comparison over every member of the basis.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.relativeTwistIso_hom_comp_toBase`,
  `relativeTwistIso_inv_comp_toBase`, `relativeTwistHom_comp_toBase`: it is a morphism over `S` in
  both directions — the triangle of the source's diagram.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.chartThetaGradedIso`: over one open of the
  base carrying a trivializing section, the comparison maps on the twisting sheaves attached to
  the morphism of homogeneous spectra fit together into an isomorphism of sheaves of `ℤ`-graded
  algebras. These are the maps of Tag 07ZG in the direction of that morphism, not the source's
  `θ_n`.

## Implementation notes

**Why a basis and not a covering.** The glueing tool is
`AlgebraicGeometry.Scheme.BasisGluingData.existsUnique_isoOver` (Tag 01LH, uniqueness), which
takes an arbitrary basis of the topology of `S`. The sibling
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.existsUnique_isoOver` — proved *from* it — cannot
be used: it is stated for a `Stacks.AlgebraicGeometry.RelativeProj.RelativeProjData`, whose
`chart` field demands a chart over **every** affine open of `S`, and over an affine open carrying
no trivializing section of `ℒ` there is no comparison to put there.

**The choice of section is unconstrained.** A member of the basis carries *some* trivializing
section; the section is chosen by
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.exists_trivializesPower_of_mem` with no
coherence between the choices at two members. That costs nothing, because the comparison does not
depend on the section: two trivializing sections over one open differ by a unit of the functions
there (`Stacks.SheafOfModules.TensorGenerator.exists_unit_smul_generator`) and rescaling by a
unit leaves the morphism of homogeneous spectra unchanged
(`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.projMap_psiSectionAt_eq_of_unit_smul`). So the
cocycle condition on a nesting reduces to
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.projInclusionMap_comp_projMap_psiSectionAt`,
which is about the *restricted* section.

**The second solution.** That `Proj_S(𝒜)`, with its charts precomposed with the comparisons,
solves the same glueing problem is where the two inputs of this file's prerequisites are spent:
the Cartesian square is the chart square of `Proj_S(𝒜)` pasted with the square expressing that
the comparison is a morphism over the open
(`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.projMap_psiSectionAt_comp_projInclusionToOpen`,
a square whose horizontal arrows are both isomorphisms), and the compatibility with the
restrictions is the chart transition of `Proj_S(𝒜)` after the commuting square above.

## Clause (1)

This file produces `g` only. Clause (1) — the isomorphisms
`θ_n : g^*𝒪_{P'}(n) ≅ 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` and their assembly into an isomorphism of `ℤ`-graded
algebras — is built on top of it, by a second glueing over the same basis, of sheaves of graded
algebras on `P'`: the target `⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`
(`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.targetAlgebra`, with its tensor factor) is
transported to `P'` along `g`, given chart identifications over the members of the basis there
(`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.targetTwistData`), and compared with the
twists of `P'` by `Stacks.AlgebraicGeometry.TwistExistenceBasis.glueAlgIso`.
`chartThetaGradedIso` below is not that construction: it assembles the comparison maps of
Tag 07ZG over one chart, whose target has no factor `π^*ℒ^{⊗ n}`. The whole tag is stated as one
theorem in `StacksFrontier/AlgebraicGeometry/Constructions/ProjInvertibleTwistRelativeTag.lean`.

The factor `π^*ℒ^{⊗ n}` of clause (1)'s target is not trivial in general; it is trivial only over
the members of the basis, where the powers of a trivializing section trivialize it.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules.TensorGenerator
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistGradedAlgebra

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]
  (𝒜 : SheafGradedAlgebra S)

/-! ### The comparison does not depend on the trivializing section -/

/-- **The chart comparison of Tag 02NC depends only on the open of the base, not on the
trivializing section chosen there.**

Two sections trivializing `ℒ` over one open are the canonical generators of two trivializations,
hence differ by a unit of the functions on the open
(`Stacks.SheafOfModules.TensorGenerator.exists_unit_smul_generator`), and rescaling by a unit
leaves the morphism of homogeneous spectra unchanged. This is the form of the canonicity the
glueing consumes: the comparisons attached to an *arbitrary* family of trivializing sections over
the members of the basis already agree on nestings. -/
theorem projMap_psiSectionAt_eq_of_trivializesPower {V : S.Opens}
    {x x' : (tp L 1).val.obj (op V)}
    (hx : ∀ d : ℕ, 0 < d → TrivializesPower L V x d)
    (hx' : ∀ d : ℕ, 0 < d → TrivializesPower L V x' d) :
    projMap_psiSectionAt L 𝒜 hx' = projMap_psiSectionAt L 𝒜 hx := by
  obtain ⟨e, he⟩ := hx 1 Nat.one_pos
  obtain ⟨e', he'⟩ := hx' 1 Nat.one_pos
  obtain ⟨u, hu⟩ :=
    exists_unit_smul_generator S.sheaf.obj S.ringCatSheaf.property V (tp L 1) e e'
  refine projMap_psiSectionAt_eq_of_unit_smul L 𝒜 u ?_ hx hx'
  refine Eq.trans (he'.trans (powSecAt_one_eq L (op V) x')).symm ?_
  exact hu.trans (congrArg (fun z => (u : funsAt V) • z) (he.trans (powSecAt_one_eq L (op V) x)))

/-! ### The data chosen at a member of the basis -/

/-- The trivializing section chosen at a member of the basis of trivializing affine opens. The
choice is unconstrained: by
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.projMap_psiSectionAt_eq_of_trivializesPower` the
comparison does not depend on it. -/
def basisSection (V : trivializingOpens L) : (tp L 1).val.obj (op (V : S.Opens)) :=
  (exists_trivializesPower_of_mem L V.2).choose

/-- The chosen section trivializes every positive tensor power of `ℒ` over its open. -/
theorem basisSection_trivializesPower (V : trivializingOpens L) :
    ∀ d : ℕ, 0 < d → TrivializesPower L (V : S.Opens) (basisSection L V) d :=
  (exists_trivializesPower_of_mem L V.2).choose_spec

/-- **The comparison of Tag 02NC over a member of the basis**, `Proj ℬ(V) ⟶ Proj 𝒜(V)`. For `V`
an affine open of the base the two spectra are the inverse images of `V` in `Proj_S(ℬ)` and
`Proj_S(𝒜)`, so this is the tag's `g` over that chart. -/
def basisComparison (V : trivializingOpens L) :
    AlgebraicGeometry.Proj ((twist 𝒜 L).grading (V : S.Opens)) ⟶
      AlgebraicGeometry.Proj (𝒜.grading (V : S.Opens)) :=
  projMap_psiSectionAt L 𝒜 (basisSection_trivializesPower L V)

/-- The comparison `basisComparison` over a member of the basis is an isomorphism. -/
instance isIso_basisComparison (V : trivializingOpens L) : IsIso (basisComparison L 𝒜 V) :=
  isIso_projMap_psiSectionAt L 𝒜 (basisSection_trivializesPower L V)

/-- **The comparison over a member of the basis is a morphism over that open.** -/
theorem basisComparison_comp_projInclusionToOpen (V : trivializingOpens L) :
    basisComparison L 𝒜 V ≫ projInclusionToOpen 𝒜 (V : S.Opens) V.2.1 =
      projInclusionToOpen (twist 𝒜 L) (V : S.Opens) V.2.1 :=
  projMap_psiSectionAt_comp_projInclusionToOpen L 𝒜 V.2.1 (basisSection_trivializesPower L V)

/-- **The comparisons at the chosen sections commute with the chart transitions.**

The comparison over the smaller member attached to the *restricted* section is the one
`projInclusionMap_comp_projMap_psiSectionAt` speaks about, and it coincides with the comparison at
the section chosen there because the comparison does not depend on the section. -/
theorem projInclusionMap_comp_basisComparison {W V : trivializingOpens L}
    (h : (W : S.Opens) ≤ (V : S.Opens)) :
    projInclusionMap (twist 𝒜 L) (W : S.Opens) (V : S.Opens) h W.2.1 V.2.1 ≫
        basisComparison L 𝒜 V =
      basisComparison L 𝒜 W ≫
        projInclusionMap 𝒜 (W : S.Opens) (V : S.Opens) h W.2.1 V.2.1 := by
  have hres : ∀ d : ℕ, 0 < d →
      TrivializesPower L (W : S.Opens)
        ((tp L 1).val.map (homOfLE h).op (basisSection L V)) d :=
    trivializesPower_of_one L
      (trivializesPower_of_le L h (basisSection_trivializesPower L V 1 Nat.one_pos))
  refine Eq.trans
    (projInclusionMap_comp_projMap_psiSectionAt L 𝒜 h W.2.1 V.2.1
      (basisSection_trivializesPower L V) hres) ?_
  exact congrArg (fun k => k ≫ projInclusionMap 𝒜 (W : S.Opens) (V : S.Opens) h W.2.1 V.2.1)
    (projMap_psiSectionAt_eq_of_trivializesPower L 𝒜
      (basisSection_trivializesPower L W) hres)

/-! ### The glueing datum -/

/-- **The glueing datum of Tag 01LH over the trivializing basis**: the chart `Proj ℬ(V)` of
`Proj_S(ℬ)` over each member `V`, with the chart transitions of Tag 01NO as its restriction
morphisms. The Cartesian squares and the cocycle condition are Tag 01NO's
`Stacks.AlgebraicGeometry.RelativeProj.projInclusion_isPullback` and Tag 01NP's
`Stacks.AlgebraicGeometry.RelativeProjTwistGlue.projInclusionMap_comp`. -/
def twistGluingData : AlgebraicGeometry.Scheme.BasisGluingData S (trivializingOpens L) where
  obj V := AlgebraicGeometry.Proj ((twist 𝒜 L).grading (V : S.Opens))
  proj V := projInclusionToOpen (twist 𝒜 L) (V : S.Opens) V.2.1
  res h := projInclusionMap (twist 𝒜 L) _ _ h _ _
  isPullback_res h := projInclusion_isPullback (twist 𝒜 L) _ _ h _ _
  res_trans hWV hVU :=
    (RelativeProjTwistGlue.projInclusionMap_comp (twist 𝒜 L) _ _ _ hWV hVU _ _ _).symm

/-! ### The two solutions -/

/-- **`Proj_S(ℬ)` with its own charts solves the glueing problem.** -/
def gluingTwist : (twistGluingData L 𝒜).Gluing where
  base := (relativeProj (twist 𝒜 L)).scheme
  toBase := (relativeProj (twist 𝒜 L)).toBase
  chart V := (relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1
  isPullback_chart _ := ((relativeProj (twist 𝒜 L)).chart_isPullback _ _).flip
  res_comp_chart h := (relativeProj (twist 𝒜 L)).chart_transition _ _ h _ _

/-- **`Proj_S(𝒜)`, with its charts precomposed with the comparisons, solves the same glueing
problem.** The Cartesian square is the chart square of `Proj_S(𝒜)` pasted with the square saying
the comparison is a morphism over the open — whose horizontal arrows are both isomorphisms, hence
itself Cartesian — and the compatibility with the restrictions is
`projInclusionMap_comp_basisComparison` followed by the chart transition of `Proj_S(𝒜)`. -/
def gluingBase : (twistGluingData L 𝒜).Gluing where
  base := (relativeProj 𝒜).scheme
  toBase := (relativeProj 𝒜).toBase
  chart V := basisComparison L 𝒜 V ≫ (relativeProj 𝒜).chart (V : S.Opens) V.2.1
  isPullback_chart V := by
    have hiso : IsPullback (basisComparison L 𝒜 V)
        (projInclusionToOpen (twist 𝒜 L) (V : S.Opens) V.2.1)
        (projInclusionToOpen 𝒜 (V : S.Opens) V.2.1) (𝟙 (V : S.Opens).toScheme) :=
      IsPullback.of_horiz_isIso
        ⟨(basisComparison_comp_projInclusionToOpen L 𝒜 V).trans (Category.comp_id _).symm⟩
    refine (Category.id_comp ((V : S.Opens).ι)) ▸
      (hiso.paste_horiz ((relativeProj 𝒜).chart_isPullback (V : S.Opens) V.2.1)).flip
  res_comp_chart h :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ (relativeProj 𝒜).chart _ _)
          (projInclusionMap_comp_basisComparison L 𝒜 h)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun k => basisComparison L 𝒜 _ ≫ k)
            ((relativeProj 𝒜).chart_transition _ _ h _ _))))

/-! ### Clause (1) over one chart of the base, as the graded assembly -/

/-- **The comparison maps on the twisting sheaves over one chart, as a graded assembly.**

Over an open `V` carrying a section whose powers trivialize the powers of `ℒ` there, the comparison
maps on the twisting sheaves attached to the morphism `Proj ℬ(V) ⟶ Proj 𝒜(V)` are not merely
isomorphisms one degree at a time
(`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.isIso_twistMap_psiSectionAt`): they fit
together into an isomorphism of sheaves of `ℤ`-graded algebras. The assembly is the absolute
`Stacks.AlgebraicGeometry.ProjTwistGradedAlgebra.thetaGradedIso`, applied to the comparison
homomorphism of graded rings of sections.

These are the maps of Tag 07ZG in the direction of that morphism, and their target carries no
factor `π^*ℒ^{⊗ n}`; they are not the source's `θ_n`, which is
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.twistThetaIso`. -/
def chartThetaGradedIso {V : S.Opens} {x : (tp L 1).val.obj (op V)}
    (hx : ∀ᶠ d : ℕ in Filter.atTop, TrivializesPower L V x d) :
    pullbackTwistAlgebra (𝒜.grading V)
        (mapHom (𝒜.grading V) ((twist 𝒜 L).grading V) (psiSectionAt L 𝒜 V x)) ≅
      pullbackTwistAlgebra ((twist 𝒜 L).grading V)
        (mapDomain (𝒜.grading V) ((twist 𝒜 L).grading V) (psiSectionAt L 𝒜 V x)).ι :=
  thetaGradedIso (𝒜.grading V) ((twist 𝒜 L).grading V)
    (psiSectionAt L 𝒜 V x) (isIso_twistMap_psiSectionAt L 𝒜 hx)

/-! ### Tag 02NC's canonical isomorphism -/

/-- **Tag 02NC's canonical isomorphism `Proj_S(ℬ) ≅ Proj_S(𝒜)`.** The tag's
`g : Proj_S(𝒜) ⟶ Proj_S(ℬ)` is its inverse. -/
def relativeTwistIso :
    (relativeProj (twist 𝒜 L)).scheme ≅ (relativeProj 𝒜).scheme :=
  (gluingTwist L 𝒜).isoOfGluing (isBasis_trivializingOpens L) (gluingBase L 𝒜)

/-- Over every member of the basis the canonical isomorphism is the comparison of Tag 02NC. -/
theorem chart_comp_relativeTwistIso_hom (V : trivializingOpens L) :
    (relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ≫ (relativeTwistIso L 𝒜).hom =
      basisComparison L 𝒜 V ≫ (relativeProj 𝒜).chart (V : S.Opens) V.2.1 :=
  (gluingTwist L 𝒜).chart_comp_desc (isBasis_trivializingOpens L) (gluingBase L 𝒜) V

/-- **The canonical isomorphism is a morphism over `S`** — the triangle of the source's
diagram. -/
theorem relativeTwistIso_hom_comp_toBase :
    (relativeTwistIso L 𝒜).hom ≫ (relativeProj 𝒜).toBase =
      (relativeProj (twist 𝒜 L)).toBase :=
  (gluingTwist L 𝒜).desc_comp_toBase (isBasis_trivializingOpens L) (gluingBase L 𝒜)

/-- **The tag's `g : Proj_S(𝒜) ⟶ Proj_S(ℬ)` is a morphism over `S`.** -/
theorem relativeTwistIso_inv_comp_toBase :
    (relativeTwistIso L 𝒜).inv ≫ (relativeProj (twist 𝒜 L)).toBase =
      (relativeProj 𝒜).toBase :=
  (gluingBase L 𝒜).desc_comp_toBase (isBasis_trivializingOpens L) (gluingTwist L 𝒜)

/-- **Tag 02NC's `g`, in the direction the source states it**:
`g : P = Proj_S(𝒜) ⟶ Proj_S(ℬ) = P'`. It is the inverse of
`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.relativeTwistIso`, hence an isomorphism, and
`relativeTwistIso_inv_comp_toBase` is the triangle `π' ∘ g = π` of the source's diagram. -/
def relativeTwistHom : (relativeProj 𝒜).scheme ⟶ (relativeProj (twist 𝒜 L)).scheme :=
  (relativeTwistIso L 𝒜).inv

/-- The morphism `relativeTwistHom : Proj_S(𝒜) ⟶ Proj_S(ℬ)` is an isomorphism. -/
instance isIso_relativeTwistHom : IsIso (relativeTwistHom L 𝒜) :=
  inferInstanceAs (IsIso (relativeTwistIso L 𝒜).inv)

/-- **The tag's `g` is a morphism over `S`**, at the `relativeTwistHom` spelling. -/
theorem relativeTwistHom_comp_toBase :
    relativeTwistHom L 𝒜 ≫ (relativeProj (twist 𝒜 L)).toBase = (relativeProj 𝒜).toBase :=
  relativeTwistIso_inv_comp_toBase L 𝒜

/-- **Tag 02NC's isomorphism is the unique one over `S` that is the comparison over every member
of the trivializing basis.** This is the glueing of the source's proof, through Tag 01LH's
uniqueness clause. -/
theorem existsUnique_relativeTwistIsoOver :
    ∃! e : (relativeProj (twist 𝒜 L)).scheme ≅ (relativeProj 𝒜).scheme,
      (∀ V : trivializingOpens L,
          (relativeProj (twist 𝒜 L)).chart (V : S.Opens) V.2.1 ≫ e.hom =
            basisComparison L 𝒜 V ≫ (relativeProj 𝒜).chart (V : S.Opens) V.2.1) ∧
        e.hom ≫ (relativeProj 𝒜).toBase = (relativeProj (twist 𝒜 L)).toBase :=
  AlgebraicGeometry.Scheme.BasisGluingData.existsUnique_isoOver (isBasis_trivializingOpens L)
    (twistGluingData L 𝒜) (gluingTwist L 𝒜).isPullback_chart (gluingBase L 𝒜).isPullback_chart
    (fun h => (gluingTwist L 𝒜).res_comp_chart h) (fun h => (gluingBase L 𝒜).res_comp_chart h)

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
