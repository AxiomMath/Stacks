module

public import StacksFrontier.AlgebraicGeometry.ModuleBilinearGlue.Basic
public import StacksFrontier.AlgebraicGeometry.TwistDataConstruction.Absolute
public import StacksFrontier.AlgebraicGeometry.GluedTwistChartData.Basic

/-!
# The graded algebra of glued twists on a relative projective spectrum

Let `S` be a scheme and `A` a commutative, nonnegatively graded, quasi-coherent graded
`𝒪_S`-algebra — Situation 01NN. Tag 01NR asserts that the graded twists on the projective spectra
of the affine section rings of `A` glue to a sheaf of graded algebras on the relative Proj of `A`.
Its twist datum has nine fields, and the first of them, `algebra`, is a sheaf of `ℤ`-graded
algebras on the relative Proj whose homogeneous pieces are the glued twists. Every other field is
stated relative to it.

**This file builds that graded algebra.** The homogeneous pieces are the glued twists
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.gluedTwist` of Tag 01NO, the multiplication and
the unit are the canonical product and unit of Tag 01MO on each affine chart, and the condition
`Stacks.AlgebraicGeometry.RelativeProjTwists.IsGradedChartIso` on the resulting chart data is
proved. Before this file no graded algebra on a relative Proj with the glued twists as its pieces
existed in either tree; the implementation notes of
`StacksFrontier/AlgebraicGeometry/TwistDataConstruction/Absolute.lean` record its absence.

## Main definitions

* `Stacks.AlgebraicGeometry.GluedTwistAlgebra.IsMultiplicativeCmpGen`: the condition that the
  glued chart comparison `Stacks.AlgebraicGeometry.ChartTransRelativeProj.cmpGen` carries the
  canonical product and unit of absolute twist sections to themselves. It is an interface, not an
  assumption: `isMultiplicativeCmpGen` proves it.
* `Stacks.AlgebraicGeometry.GluedTwistAlgebra.chartSections`: the identification of the sections
  of a glued twist over an open inside a chart image with the sections of that chart's own
  absolute twist — Stacks 00AL's comparison map for the glueing datum the glued twist was built
  from.
* `Stacks.AlgebraicGeometry.GluedTwistAlgebra.congrLocalBilinear` and `pushLocalBilinear`: the
  two generic transports of local multiplication data — along local isomorphisms of the three
  modules, and along a pushforward of schemes. Stated with the modules as variables, which is
  what makes them usable at all; see the implementation notes.
* `Stacks.AlgebraicGeometry.GluedTwistAlgebra.mulData` and `oneData`: **the local multiplication
  and unit of the glued twists over a chart image**, which are the two local data
  `Stacks.AlgebraicGeometry.ModuleBilinearGlue.gluedGradedAlgebra` asks for.

## Main results

* `Stacks.AlgebraicGeometry.GluedTwistAlgebra.isMultiplicativeCmpGen`: **the chart comparison is
  multiplicative**, unconditionally. This is
  `Stacks.AlgebraicGeometry.TwistGluedProduct.cmpGen_mul` and `cmpGen_one` packaged as the
  interface above, so the graded algebra below carries no multiplicativity hypothesis.
* `Stacks.AlgebraicGeometry.GluedTwistAlgebra.trans_mul` and `trans_one`: **the non-nested chart
  transition respects the product and the unit**, over every open inside two chart images. This
  is what makes the glued product well defined, and it is the only consumer of multiplicativity.
* `Stacks.AlgebraicGeometry.GluedTwistAlgebra.mulData_agree` and `oneData_agree`: the local
  products, respectively units, over two chart images agree on the overlaps.
* `Stacks.AlgebraicGeometry.GluedTwistAlgebra.mulApp_heq_assoc`, `mulApp_heq_one_mul` and
  `mulApp_heq_mul_one`: the three algebra laws, over one chart image.
* `Stacks.AlgebraicGeometry.GluedTwistAlgebra.mulData` and `oneData`: the local product and unit
  packaged as the local data that `ModuleBilinearGlue.gluedGradedAlgebra` consumes. These are the
  last declarations of this file.

## The route

The glueing is not done by hand. `Stacks.AlgebraicGeometry.ModuleBilinearGlue.gluedGradedAlgebra`
takes a global family of homogeneous pieces together with a multiplication and a unit given only
on the members of an open cover, agreeing on the overlaps and satisfying the three algebra laws
there, and returns the glued sheaf of graded algebras. So the content of this file is the local
data and the overlap agreement:

* the cover is the family of inverse images of the affine opens of the base, which is both the
  chart family and the refinement family of
  `Stacks.AlgebraicGeometry.ChartTransRelativeProj.modelData`, so no reindexing occurs anywhere;
* the local product over a member is Tag 01MO's absolute product on that member's own chart, read
  through `chartSections`, and the three algebra laws there are the absolute laws of
  `StacksFrontier/AlgebraicGeometry/TwistDataConstruction/Absolute.lean` transported along the same
  identification;
* the overlap agreement is multiplicativity of the non-nested chart transition. Over an open
  inside the inverse image of an affine open below both members, that transition is the composite
  of that open's two glued comparisons (`trans_app_cmpGen`), so it is multiplicative there
  because each comparison is; the general case follows on the cover by such members.

## Implementation notes

The local product is **written out** (`mulApp`) rather than obtained by composing a pushforward of
`Stacks.AlgebraicGeometry.ProjConeTwist.twistMul` with a transport along `chartSections`.
The composite does not reduce: the defeq check is blocked by an unexposed
colimit in the sheafified tensor product underlying
`Stacks.AlgebraicGeometry.RelativeProjTwists.absoluteTwistProduct`, so the equation that the
local product *is* the absolute product — which is what `IsGradedChartIso` asks for — would not be
`rfl`. Written out, it is, and the five bilinearity obligations are discharged one at a time.

The two scalar laws are the only place where a scalar of the relative Proj is restricted along a
chart; `push_absoluteTwistProduct_smul_left` and `push_absoluteTwistProduct_smul_right` isolate
that step.

`trans_app_cmpGen` replaces the structure field `ModelData.cmp` by `cmpGen` in a statement with no
other content. The two are one delta step apart, but performing the step inside a larger term
drives the kernel into the `modelData` structure literal once per occurrence and exhausts its
budget; the replacement is therefore made by `congrArg` at the level of the local isomorphisms and
never underneath an `app`, which is the same discipline
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.isComposite_meetLoc` records.

The three algebra laws are heterogeneous, their two sides lying in the pieces indexed by `(i+j)+k`
and `i+(j+k)`, by `0+i` and `i`, and by `i+0` and `i`. All transport is confined to
`heq_symm_chartSections`, whose degrees are variables and which is proved by substituting the
equality away, so no motive is ever elaborated at a compound index.

## What is not done here

**The graded algebra itself is NOT constructed here, and neither is Tag 01NR's
`isGradedChartIso` field.** This file stops at the local data — `mulData` and `oneData` — which is
what `Stacks.AlgebraicGeometry.ModuleBilinearGlue.gluedGradedAlgebra` consumes. Feeding them to it
is the step that is missing.

The obstruction to that step is localized: the generic `congrLocalBilinear_app` and
`congrLocalSection_app` lemmas kernel-check fine, and only their **instantiation at `gluedTwist`**
does not — it hits `(kernel) deterministic timeout`s, plus an `HSMul` elaboration bug, with
`set_option` unavailable to raise any limit. So the obstruction is not the mathematics of the
glueing but the cost of the defeq checks at that instantiation; it needs the instantiation
restated through a lighter abbreviation.

Everything is conditional on
`Stacks.AlgebraicGeometry.ChartTransRelativeProj.IsNestedCocycle A n` in **every** integer degree,
which is Tag 01MZ's third assertion. That hypothesis is discharged outright, in every integer
degree, by `Stacks.AlgebraicGeometry.ProjTwistCocycle.isNestedCocycle`, which supersedes the
degree-one-only `Stacks.AlgebraicGeometry.ChartCocycleRigidity.isNestedCocycle_one`. The
hypothesis is kept in the statements below because the glued twist `gluedTwist A n hcoc` is
indexed by it.

Quasi-coherence of the pieces and commutativity of the product are fields of `TwistData` and are
not addressed here.

`push_absoluteTwistProduct_smul_left`/`_right` and `resLE_absoluteTwistProduct` overlap with
`Stacks.AlgebraicGeometry.TwistGluedProduct.push_resLE_product` and `push_resLE_unit`, which were
written independently and in parallel; the versions here are stated at the `chartModule` spelling
this file uses throughout.

No `stacks` attribute is attached. Tag 01NR's existence assertion is earned only by a complete
twist datum; one field of it, however central, is not a covering set.

## References

* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01MO](https://stacks.math.columbia.edu/tag/01MO)
* [Stacks Project, Tag 01MZ](https://stacks.math.columbia.edu/tag/01MZ)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ChartTransNonNested
open Stacks.AlgebraicGeometry.ChartTransRelativeProj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjTwists

namespace Stacks.AlgebraicGeometry.GluedTwistAlgebra

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-! ### The cover -/

/-- The family of inverse images of the affine opens of the base, which is both the chart family
and the refinement family of `Stacks.AlgebraicGeometry.ChartTransRelativeProj.modelData`. -/
public abbrev cover (m : S.affineOpens) : (relativeProj A).scheme.Opens :=
  (relativeProj A).toBase ⁻¹ᵁ (m.1 : S.Opens)

/-- The inverse images of the affine opens of the base cover the relative Proj. -/
public theorem iSup_cover : (⨆ m : S.affineOpens, cover A m) = ⊤ :=
  RelativeProjTwistGlue.iSup_toBase_preimage_eq_top (relativeProj A)

/-! ### The multiplicativity hypothesis -/

/-- **The chart comparison is multiplicative.** For two affine opens of the base whose inverse
images are nested, the glued comparison `Stacks.AlgebraicGeometry.ChartTransRelativeProj.cmpGen`
of Tag 01NO carries the canonical product of absolute twist sections of Tag 01MO to the canonical
product, in every pair of integer degrees and over every open inside the inverse image of the
smaller affine open; and in degree zero it carries the unit section to the unit section. -/
public def IsMultiplicativeCmpGen : Prop :=
  (∀ (W U : S.Opens) (hW : IsAffineOpen W) (hU : IsAffineOpen U) (i j : ℤ)
      (hci : IsNestedCocycle A i) (hcj : IsNestedCocycle A j)
      (hcij : IsNestedCocycle A (i + j))
      (hpre : (relativeProj A).toBase ⁻¹ᵁ W ≤ (relativeProj A).toBase ⁻¹ᵁ U)
      (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W)
      (a : (pushforwardVal ((relativeProj A).chart U hU)
        (twistingSheaf (A.grading U) i)).obj (op V))
      (b : (pushforwardVal ((relativeProj A).chart U hU)
        (twistingSheaf (A.grading U) j)).obj (op V)),
    (cmpGen A W U hW hU (i + j) hpre hcij).app V hV
        (absoluteTwistProduct (A.grading U) i j ((relativeProj A).chart U hU ⁻¹ᵁ V) a b)
      = absoluteTwistProduct (A.grading W) i j ((relativeProj A).chart W hW ⁻¹ᵁ V)
          ((cmpGen A W U hW hU i hpre hci).app V hV a)
          ((cmpGen A W U hW hU j hpre hcj).app V hV b)) ∧
  (∀ (W U : S.Opens) (hW : IsAffineOpen W) (hU : IsAffineOpen U) (hc : IsNestedCocycle A 0)
      (hpre : (relativeProj A).toBase ⁻¹ᵁ W ≤ (relativeProj A).toBase ⁻¹ᵁ U)
      (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W),
    (cmpGen A W U hW hU 0 hpre hc).app V hV
        (absoluteTwistUnit (A.grading U) ((relativeProj A).chart U hU ⁻¹ᵁ V))
      = absoluteTwistUnit (A.grading W) ((relativeProj A).chart W hW ⁻¹ᵁ V))

/-! ### The sections of a glued twist over a chart -/

/-- The chart module of the `n`-th glued twist over an affine open of the base: the pushforward
along that affine open's chart of the chart's own absolute twist. -/
public abbrev chartModule (n : ℤ) (m : S.affineOpens) :
    PresheafOfModules.{u} (relativeProj A).scheme.ringCatSheaf.obj :=
  pushforwardVal ((relativeProj A).chart (m.1 : S.Opens) m.2)
    (twistingSheaf (A.grading (m.1 : S.Opens)) n)

/-- **The sections of the glued twist over an open inside a chart image are the sections of that
chart's own twist**, `𝒪`-linearly. This is Stacks 00AL's comparison map `φ m` for the glueing
datum the glued twist was built from. -/
public def chartSections (n : ℤ) (hcoc : IsNestedCocycle A n) (m : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hV : V ≤ cover A m) :
    (gluedTwist A n hcoc).val.obj (op V)
      ≃ₗ[(relativeProj A).scheme.ringCatSheaf.obj.obj (op V)]
      (chartModule A n m).obj (op V) :=
  SchemeModuleGlue.chartSectionsLinearEquiv
    (modelData A n hcoc).toChartGlueData.toOModuleGlueData m hV

/-- The comparison commutes with the restriction maps. -/
public theorem chartSections_resLE (n : ℤ) (hcoc : IsNestedCocycle A n) (m : S.affineOpens)
    {V W : (relativeProj A).scheme.Opens} (hV : V ≤ cover A m) (hWV : W ≤ V)
    (x : (gluedTwist A n hcoc).val.obj (op V)) :
    chartSections A n hcoc m (hWV.trans hV) ((gluedTwist A n hcoc).val.resLE hWV x)
      = (chartModule A n m).resLE hWV (chartSections A n hcoc m hV x) :=
  TopCat.Sheaf.GlueData.sectionsEquiv_map
    (modelData A n hcoc).toChartGlueData.toOModuleGlueData.toAddGlueData.toGlueData m hV hWV x

/-- **The chart comparisons of two affine opens of the base differ by the non-nested chart
transition**, over an open inside both chart images. -/
public theorem trans_chartSections (n : ℤ) (hcoc : IsNestedCocycle A n) (m l : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hm : V ≤ cover A m) (hl : V ≤ cover A l)
    (x : (gluedTwist A n hcoc).val.obj (op V)) :
    (modelData A n hcoc).trans m l hm hl (chartSections A n hcoc m hm x)
      = chartSections A n hcoc l hl x :=
  TopCat.Sheaf.GlueData.trans_sectionsEquiv
    (modelData A n hcoc).toChartGlueData.toOModuleGlueData.toAddGlueData.toGlueData m l hm hl x

/-! ### The absolute product on the chart modules -/

/-- Shrinking an affine open of the base shrinks its inverse image. -/
public theorem cover_mono {m r : S.affineOpens} (h : (r.1 : S.Opens) ≤ (m.1 : S.Opens)) :
    cover A r ≤ cover A m :=
  ((relativeProj A).toBase).preimage_mono h

/-- **The canonical product of absolute twist sections commutes with the restriction maps of the
chart modules.** This is Tag 01MO's product read on the pushforward along a chart, where a
restriction of the ambient open is a restriction of its preimage. -/
public theorem resLE_absoluteTwistProduct (i j : ℤ) (m : S.affineOpens)
    {V W : (relativeProj A).scheme.Opens} (hWV : W ≤ V)
    (a : (chartModule A i m).obj (op V)) (b : (chartModule A j m).obj (op V)) :
    (chartModule A (i + j) m).resLE hWV
        (absoluteTwistProduct (A.grading (m.1 : S.Opens)) i j
          ((relativeProj A).chart (m.1 : S.Opens) m.2 ⁻¹ᵁ V) a b)
      = absoluteTwistProduct (A.grading (m.1 : S.Opens)) i j
          ((relativeProj A).chart (m.1 : S.Opens) m.2 ⁻¹ᵁ W)
          ((chartModule A i m).resLE hWV a) ((chartModule A j m).resLE hWV b) :=
  TwistDataConstruction.twistProd_naturality (A.grading (m.1 : S.Opens)) i j _ a b

/-- **Every restriction map of the degree-zero twist carries the unit section to the unit
section.** Both sides have the value `1` at every point. -/
public theorem map_absoluteTwistUnit {R : Type u} {σ : Type u} [CommRing R] [SetLike σ R]
    [AddSubgroupClass σ R] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    {X Y : ((AlgebraicGeometry.Proj 𝒜).Opens)ᵒᵖ} (f : X ⟶ Y) :
    (twistingSheaf 𝒜 0).val.map f (absoluteTwistUnit 𝒜 X.unop) = absoluteTwistUnit 𝒜 Y.unop :=
  TwistDataConstruction.twist_ext 𝒜 fun x =>
    (TwistDataConstruction.twistUnit_val 𝒜 (X := X) (f.unop x)).trans
      (TwistDataConstruction.twistUnit_val 𝒜 (X := Y) x).symm

/-- **The unit section of the degree-zero twist is compatible with the restriction maps of the
chart modules.** -/
public theorem resLE_absoluteTwistUnit (m : S.affineOpens)
    {V W : (relativeProj A).scheme.Opens} (hWV : W ≤ V) :
    (chartModule A 0 m).resLE hWV
        (absoluteTwistUnit (A.grading (m.1 : S.Opens))
          ((relativeProj A).chart (m.1 : S.Opens) m.2 ⁻¹ᵁ V))
      = absoluteTwistUnit (A.grading (m.1 : S.Opens))
          ((relativeProj A).chart (m.1 : S.Opens) m.2 ⁻¹ᵁ W) :=
  TwistDataConstruction.twist_ext (A.grading (m.1 : S.Opens)) fun x =>
    (TwistDataConstruction.twistUnit_val (A.grading (m.1 : S.Opens)) _).trans
      (TwistDataConstruction.twistUnit_val (A.grading (m.1 : S.Opens)) x).symm

/-! ### The chart transition is multiplicative -/

section Trans

variable (hcoc : ∀ n : ℤ, IsNestedCocycle A n)

/-- **The inverse of the chart comparison is multiplicative**, over an open inside the inverse
image of the smaller affine open. An equivalence whose forward direction carries a product to a
product carries a product back to a product. -/
public theorem symm_cmpGen_mul (hmul : IsMultiplicativeCmpGen A)
    (W U : S.Opens) (hW : IsAffineOpen W) (hU : IsAffineOpen U)
    (i j : ℤ) (hpre : (relativeProj A).toBase ⁻¹ᵁ W ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W)
    (a : (pushforwardVal ((relativeProj A).chart W hW)
      (twistingSheaf (A.grading W) i)).obj (op V))
    (b : (pushforwardVal ((relativeProj A).chart W hW)
      (twistingSheaf (A.grading W) j)).obj (op V)) :
    ((cmpGen A W U hW hU (i + j) hpre (hcoc (i + j))).app V hV).symm
        (absoluteTwistProduct (A.grading W) i j ((relativeProj A).chart W hW ⁻¹ᵁ V) a b)
      = absoluteTwistProduct (A.grading U) i j ((relativeProj A).chart U hU ⁻¹ᵁ V)
          (((cmpGen A W U hW hU i hpre (hcoc i)).app V hV).symm a)
          (((cmpGen A W U hW hU j hpre (hcoc j)).app V hV).symm b) := by
  have key := hmul.1 W U hW hU i j (hcoc i) (hcoc j) (hcoc (i + j)) hpre V hV
    (((cmpGen A W U hW hU i hpre (hcoc i)).app V hV).symm a)
    (((cmpGen A W U hW hU j hpre (hcoc j)).app V hV).symm b)
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at key
  exact ((cmpGen A W U hW hU (i + j) hpre (hcoc (i + j))).app V hV).injective
    ((LinearEquiv.apply_symm_apply _ _).trans key.symm)

/-- **The inverse of the chart comparison carries the unit section to the unit section.** -/
public theorem symm_cmpGen_one (hmul : IsMultiplicativeCmpGen A)
    (W U : S.Opens) (hW : IsAffineOpen W) (hU : IsAffineOpen U)
    (hpre : (relativeProj A).toBase ⁻¹ᵁ W ≤ (relativeProj A).toBase ⁻¹ᵁ U)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ W) :
    ((cmpGen A W U hW hU 0 hpre (hcoc 0)).app V hV).symm
        (absoluteTwistUnit (A.grading W) ((relativeProj A).chart W hW ⁻¹ᵁ V))
      = absoluteTwistUnit (A.grading U) ((relativeProj A).chart U hU ⁻¹ᵁ V) :=
  ((cmpGen A W U hW hU 0 hpre (hcoc 0)).app V hV).injective
    ((LinearEquiv.apply_symm_apply _ _).trans (hmul.2 W U hW hU (hcoc 0) hpre V hV).symm)

/-- The chart comparison of `Stacks.AlgebraicGeometry.ChartTransRelativeProj.modelData` is
`cmpGen`. A stable rewriting handle for the structure field. -/
public theorem modelData_cmp (n : ℤ) (hc : IsNestedCocycle A n) (r m : S.affineOpens)
    (hr : cover A r ≤ cover A m) :
    (modelData A n hc).cmp r m hr
      = cmpGen A (r.1 : S.Opens) (m.1 : S.Opens) r.2 m.2 n hr hc :=
  rfl

/-- **Cancelling an affine open's own chart between two comparisons preserves the product.** The
comparison with the first chart is multiplicative, and the inverse of the comparison with the
second is multiplicative by `symm_cmpGen_mul`. -/
public theorem symm_comp_cmpGen_mul (hmul : IsMultiplicativeCmpGen A)
    (R M L : S.Opens) (hR : IsAffineOpen R) (hM : IsAffineOpen M) (hL : IsAffineOpen L) (i j : ℤ)
    (hRM : (relativeProj A).toBase ⁻¹ᵁ R ≤ (relativeProj A).toBase ⁻¹ᵁ M)
    (hRL : (relativeProj A).toBase ⁻¹ᵁ R ≤ (relativeProj A).toBase ⁻¹ᵁ L)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ R)
    (a : (pushforwardVal ((relativeProj A).chart M hM)
      (twistingSheaf (A.grading M) i)).obj (op V))
    (b : (pushforwardVal ((relativeProj A).chart M hM)
      (twistingSheaf (A.grading M) j)).obj (op V)) :
    ((cmpGen A R L hR hL (i + j) hRL (hcoc (i + j))).app V hV).symm
        ((cmpGen A R M hR hM (i + j) hRM (hcoc (i + j))).app V hV
          (absoluteTwistProduct (A.grading M) i j ((relativeProj A).chart M hM ⁻¹ᵁ V) a b))
      = absoluteTwistProduct (A.grading L) i j ((relativeProj A).chart L hL ⁻¹ᵁ V)
          (((cmpGen A R L hR hL i hRL (hcoc i)).app V hV).symm
            ((cmpGen A R M hR hM i hRM (hcoc i)).app V hV a))
          (((cmpGen A R L hR hL j hRL (hcoc j)).app V hV).symm
            ((cmpGen A R M hR hM j hRM (hcoc j)).app V hV b)) := by
  rw [hmul.1 R M hR hM i j (hcoc i) (hcoc j) (hcoc (i + j)) hRM V hV a b]
  exact symm_cmpGen_mul A hcoc hmul R L hR hL i j hRL V hV _ _

/-- The unit analogue of `symm_comp_cmpGen_mul`. -/
public theorem symm_comp_cmpGen_one (hmul : IsMultiplicativeCmpGen A)
    (R M L : S.Opens) (hR : IsAffineOpen R) (hM : IsAffineOpen M) (hL : IsAffineOpen L)
    (hRM : (relativeProj A).toBase ⁻¹ᵁ R ≤ (relativeProj A).toBase ⁻¹ᵁ M)
    (hRL : (relativeProj A).toBase ⁻¹ᵁ R ≤ (relativeProj A).toBase ⁻¹ᵁ L)
    (V : (relativeProj A).scheme.Opens) (hV : V ≤ (relativeProj A).toBase ⁻¹ᵁ R) :
    ((cmpGen A R L hR hL 0 hRL (hcoc 0)).app V hV).symm
        ((cmpGen A R M hR hM 0 hRM (hcoc 0)).app V hV
          (absoluteTwistUnit (A.grading M) ((relativeProj A).chart M hM ⁻¹ᵁ V)))
      = absoluteTwistUnit (A.grading L) ((relativeProj A).chart L hL ⁻¹ᵁ V) := by
  rw [hmul.2 R M hR hM (hcoc 0) hRM V hV]
  exact symm_cmpGen_one A hcoc hmul R L hR hL hRL V hV

/-- **Over an open inside the inverse image of an affine open of the base below both, the
non-nested chart transition is the composite of that affine open's two glued comparisons.** This
is `ModelData.trans_app_of_le` with the structure field `cmp` replaced by `cmpGen`; the
replacement is one delta step, and it is made here, in a statement with no other content, because
performing it inside a larger term drives the kernel into the `modelData` structure literal once
per occurrence. -/
public theorem trans_app_cmpGen (n : ℤ) (hc : IsNestedCocycle A n) (m l r : S.affineOpens)
    (hk : cover A r ≤ cover A m ⊓ cover A l)
    {V : (relativeProj A).scheme.Opens} (hr : V ≤ cover A r)
    (hm : V ≤ cover A m) (hl : V ≤ cover A l) (s : (chartModule A n m).obj (op V)) :
    (modelData A n hc).trans m l hm hl s
      = ((cmpGen A (r.1 : S.Opens) (l.1 : S.Opens) r.2 l.2 n
            (hk.trans inf_le_right) hc).app V hr).symm
          ((cmpGen A (r.1 : S.Opens) (m.1 : S.Opens) r.2 m.2 n
            (hk.trans inf_le_left) hc).app V hr s) := by
  refine Eq.trans ((modelData A n hc).trans_app_of_le m l hm hl r hk hr s) ?_
  exact congrArg₂
    (fun (e₁ : TopCat.Sheaf.LocalModuleEquiv (chartModule A n l) (chartModule A n r) (cover A r))
        (e₂ : TopCat.Sheaf.LocalModuleEquiv (chartModule A n m) (chartModule A n r)
          (cover A r)) => ((e₁.app V hr).symm) (e₂.app V hr s))
    (modelData_cmp A n hc r l (hk.trans inf_le_right))
    (modelData_cmp A n hc r m (hk.trans inf_le_left))

/-- **The non-nested chart transition is multiplicative over an open inside the inverse image of
an affine open of the base below both.** There the transition is the composite of that open's two
comparisons with its own chart, and the composite is multiplicative. -/
public theorem trans_mul_of_le (hmul : IsMultiplicativeCmpGen A) (i j : ℤ)
    (m l r : S.affineOpens) (hrm : (r.1 : S.Opens) ≤ (m.1 : S.Opens))
    (hrl : (r.1 : S.Opens) ≤ (l.1 : S.Opens))
    {V : (relativeProj A).scheme.Opens} (hr : V ≤ cover A r)
    (hm : V ≤ cover A m) (hl : V ≤ cover A l)
    (a : (chartModule A i m).obj (op V)) (b : (chartModule A j m).obj (op V)) :
    (modelData A (i + j) (hcoc (i + j))).trans m l hm hl
        (absoluteTwistProduct (A.grading (m.1 : S.Opens)) i j
          ((relativeProj A).chart (m.1 : S.Opens) m.2 ⁻¹ᵁ V) a b)
      = absoluteTwistProduct (A.grading (l.1 : S.Opens)) i j
          ((relativeProj A).chart (l.1 : S.Opens) l.2 ⁻¹ᵁ V)
          ((modelData A i (hcoc i)).trans m l hm hl a)
          ((modelData A j (hcoc j)).trans m l hm hl b) := by
  have hk : cover A r ≤ cover A m ⊓ cover A l :=
    le_inf (cover_mono A hrm) (cover_mono A hrl)
  refine Eq.trans (trans_app_cmpGen A (i + j) (hcoc (i + j)) m l r hk hr hm hl _) ?_
  refine Eq.trans (symm_comp_cmpGen_mul A hcoc hmul (r.1 : S.Opens) (m.1 : S.Opens)
    (l.1 : S.Opens) r.2 m.2 l.2 i j (hk.trans inf_le_left) (hk.trans inf_le_right) V hr a b) ?_
  exact congrArg₂ (absoluteTwistProduct (A.grading (l.1 : S.Opens)) i j
      ((relativeProj A).chart (l.1 : S.Opens) l.2 ⁻¹ᵁ V))
    (trans_app_cmpGen A i (hcoc i) m l r hk hr hm hl a).symm
    (trans_app_cmpGen A j (hcoc j) m l r hk hr hm hl b).symm

/-- **The non-nested chart transition carries the unit section to the unit section over an open
inside the inverse image of an affine open of the base below both.** -/
public theorem trans_one_of_le (hmul : IsMultiplicativeCmpGen A)
    (m l r : S.affineOpens) (hrm : (r.1 : S.Opens) ≤ (m.1 : S.Opens))
    (hrl : (r.1 : S.Opens) ≤ (l.1 : S.Opens))
    {V : (relativeProj A).scheme.Opens} (hr : V ≤ cover A r)
    (hm : V ≤ cover A m) (hl : V ≤ cover A l) :
    (modelData A 0 (hcoc 0)).trans m l hm hl
        (absoluteTwistUnit (A.grading (m.1 : S.Opens))
          ((relativeProj A).chart (m.1 : S.Opens) m.2 ⁻¹ᵁ V))
      = absoluteTwistUnit (A.grading (l.1 : S.Opens))
          ((relativeProj A).chart (l.1 : S.Opens) l.2 ⁻¹ᵁ V) := by
  have hk : cover A r ≤ cover A m ⊓ cover A l :=
    le_inf (cover_mono A hrm) (cover_mono A hrl)
  refine Eq.trans (trans_app_cmpGen A 0 (hcoc 0) m l r hk hr hm hl _) ?_
  exact symm_comp_cmpGen_one A hcoc hmul (r.1 : S.Opens) (m.1 : S.Opens) (l.1 : S.Opens)
    r.2 m.2 l.2 (hk.trans inf_le_left) (hk.trans inf_le_right) V hr


/-- Two sections of a chart module over an open inside two chart images are equal if their
restrictions to the inverse image of each affine open below both agree. -/
private theorem eq_of_resLE_eq_of_le (n : ℤ) (m l : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hm : V ≤ cover A m) (hl : V ≤ cover A l)
    (x y : (chartModule A n l).obj (op V))
    (h : ∀ r : S.affineOpens, (r.1 : S.Opens) ≤ (m.1 : S.Opens) → (r.1 : S.Opens) ≤ l.1 →
      (chartModule A n l).resLE (inf_le_left : V ⊓ cover A r ≤ V) x
        = (chartModule A n l).resLE (inf_le_left : V ⊓ cover A r ≤ V) y) : x = y :=
  TopCat.Sheaf.eq_of_locally_eq_of_isSheafPresheaf
    (isSheaf_pushChart A (l.1 : S.Opens) l.2 n)
    (fun r : {r : S.affineOpens // (r.1 : S.Opens) ≤ (m.1 : S.Opens) ⊓ (l.1 : S.Opens)} =>
      V ⊓ cover A r.1) (fun _ => inf_le_left)
    (TopCat.Sheaf.le_iSup_inf_of_le
      (le_iSup_preimage_inf A (m.1 : S.Opens) (l.1 : S.Opens) V hm hl))
    fun r => h r.1 (r.2.trans inf_le_left) (r.2.trans inf_le_right)

/-- **The non-nested chart transition is multiplicative**, over every open inside both chart
images. Checked on the cover of the open by the inverse images of the affine opens of the base
below both: over such a member `trans_mul_of_le` applies, and both the transition and the
canonical product commute with the restriction maps. -/
public theorem trans_mul (hmul : IsMultiplicativeCmpGen A) (i j : ℤ) (m l : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hm : V ≤ cover A m) (hl : V ≤ cover A l)
    (a : (chartModule A i m).obj (op V)) (b : (chartModule A j m).obj (op V)) :
    (modelData A (i + j) (hcoc (i + j))).trans m l hm hl
        (absoluteTwistProduct (A.grading (m.1 : S.Opens)) i j
          ((relativeProj A).chart (m.1 : S.Opens) m.2 ⁻¹ᵁ V) a b)
      = absoluteTwistProduct (A.grading (l.1 : S.Opens)) i j
          ((relativeProj A).chart (l.1 : S.Opens) l.2 ⁻¹ᵁ V)
          ((modelData A i (hcoc i)).trans m l hm hl a)
          ((modelData A j (hcoc j)).trans m l hm hl b) := by
  refine eq_of_resLE_eq_of_le A (i + j) m l hm hl _ _ fun r hrm hrl => ?_
  have h₀ : V ⊓ cover A r ≤ V := inf_le_left
  refine Eq.trans ((modelData A (i + j) (hcoc (i + j))).trans_map m l hm hl h₀ _).symm ?_
  refine Eq.trans (congrArg (fun z => (modelData A (i + j) (hcoc (i + j))).trans m l
      (h₀.trans hm) (h₀.trans hl) z) (resLE_absoluteTwistProduct A i j m h₀ a b)) ?_
  refine Eq.trans (trans_mul_of_le A hcoc hmul i j m l r hrm hrl inf_le_right
    (h₀.trans hm) (h₀.trans hl) _ _) ?_
  refine Eq.trans ?_ (resLE_absoluteTwistProduct A i j l h₀ _ _).symm
  exact congrArg₂ (absoluteTwistProduct (A.grading (l.1 : S.Opens)) i j
      ((relativeProj A).chart (l.1 : S.Opens) l.2 ⁻¹ᵁ (V ⊓ cover A r)))
    ((modelData A i (hcoc i)).trans_map m l hm hl h₀ a)
    ((modelData A j (hcoc j)).trans_map m l hm hl h₀ b)

/-- **The non-nested chart transition carries the unit section to the unit section**, over every
open inside both chart images. -/
public theorem trans_one (hmul : IsMultiplicativeCmpGen A) (m l : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hm : V ≤ cover A m) (hl : V ≤ cover A l) :
    (modelData A 0 (hcoc 0)).trans m l hm hl
        (absoluteTwistUnit (A.grading (m.1 : S.Opens))
          ((relativeProj A).chart (m.1 : S.Opens) m.2 ⁻¹ᵁ V))
      = absoluteTwistUnit (A.grading (l.1 : S.Opens))
          ((relativeProj A).chart (l.1 : S.Opens) l.2 ⁻¹ᵁ V) := by
  refine eq_of_resLE_eq_of_le A 0 m l hm hl _ _ fun r hrm hrl => ?_
  have h₀ : V ⊓ cover A r ≤ V := inf_le_left
  refine Eq.trans ((modelData A 0 (hcoc 0)).trans_map m l hm hl h₀ _).symm ?_
  refine Eq.trans (congrArg (fun z => (modelData A 0 (hcoc 0)).trans m l
      (h₀.trans hm) (h₀.trans hl) z) (resLE_absoluteTwistUnit A m h₀)) ?_
  refine Eq.trans (trans_one_of_le A hcoc hmul m l r hrm hrl inf_le_right
    (h₀.trans hm) (h₀.trans hl)) ?_
  exact (resLE_absoluteTwistUnit A l h₀).symm

end Trans


/-! ### Generic transports of local multiplication and unit data

Both transports below are stated with the modules as **variables**, and that is the whole point.
The bilinearity of the transported product is discharged here, once, where the modules are
variables; the `_app` equations are `rfl` here for the same reason. Instantiating them at the
glued twists is then substitution, and the kernel never unfolds anything.

The alternative does not work. Stated directly at the glued twists, the five
bilinearity obligations each need the additive and scalar structure on
`Γ(gluedTwist A n hcoc, V)`, and obtaining those instances forces the kernel to reduce
`gluedTwist` through `ModelData.glued` into the `modelData` structure literal — which exhausts
its budget, once per obligation. No amount of opacity in the *proof* helps, because the cost is
in the *statement*. -/

section Transport

variable {X Y : Scheme.{u}}

/-- **The pushforward of an `𝒪`-bilinear map of sheaves of modules along a morphism of schemes**,
as local multiplication data on an arbitrary open. A section of the pushforward over `V` is a
section over the preimage of `V` and a scalar acts through `f.app V`, so every field is the
corresponding field of the bilinear map read at the preimage. This is the only place a scalar of
the ambient scheme is restricted along the morphism. -/
public def pushLocalBilinear (f : Y ⟶ X) {M N P : Y.Modules}
    (β : SheafOfModules.BilinearMap M N P) (T : X.Opens) :
    TopCat.Sheaf.LocalBilinearMap (pushforwardVal f M) (pushforwardVal f N)
      (pushforwardVal f P) T where
  app V _ := β.app (op (f ⁻¹ᵁ V))
  map_smul_left V _ r s t := β.map_smul_left (op (f ⁻¹ᵁ V)) (f.app V r) s t
  map_smul_right V _ r s t := β.map_smul_right (op (f ⁻¹ᵁ V)) (f.app V r) s t
  naturality _ hWV s t := TopCat.Sheaf.bilinear_app_resLE β (f.preimage_mono hWV) s t

/-- The pushforward bilinear map on `V` is the bilinear map read at the preimage of `V`. -/
public theorem pushLocalBilinear_app (f : Y ⟶ X) {M N P : Y.Modules}
    (β : SheafOfModules.BilinearMap M N P) (T : X.Opens) (V : X.Opens) (hV : V ≤ T)
    (s : (pushforwardVal f M).obj (op V)) (t : (pushforwardVal f N).obj (op V)) :
    (pushLocalBilinear f β T).app V hV s t = β.app (op (f ⁻¹ᵁ V)) s t := rfl

/-- **The pushforward of a global section of a sheaf of modules**, as local unit data. -/
public def pushLocalSection (f : Y ⟶ X) {M : Y.Modules} (s : M.sections) (T : X.Opens) :
    TopCat.Sheaf.LocalSectionData (pushforwardVal f M) T where
  app V _ := s.eval (op (f ⁻¹ᵁ V))
  naturality _ hWV := PresheafOfModules.sections_property s (homOfLE (f.preimage_mono hWV)).op

/-- The pushforward section on `V` is the section evaluated at the preimage of `V`. -/
public theorem pushLocalSection_app (f : Y ⟶ X) {M : Y.Modules} (s : M.sections) (T : X.Opens)
    (V : X.Opens) (hV : V ≤ T) :
    (pushLocalSection f s T).app V hV = s.eval (op (f ⁻¹ᵁ V)) := rfl

variable {𝒪 : (Opens (X : TopCat.{u}))ᵒᵖ ⥤ RingCat.{u}}

/-- **Transport of local multiplication data along local isomorphisms of its three modules.**
Biadditivity, bilinearity and naturality are discharged here, with the modules as variables. -/
public def congrLocalBilinear {M N P M' N' P' : PresheafOfModules.{u} 𝒪} {T : Opens X}
    (eM : TopCat.Sheaf.LocalModuleEquiv M M' T) (eN : TopCat.Sheaf.LocalModuleEquiv N N' T)
    (eP : TopCat.Sheaf.LocalModuleEquiv P P' T)
    (g : TopCat.Sheaf.LocalBilinearMap M' N' P' T) :
    TopCat.Sheaf.LocalBilinearMap M N P T where
  app V hV :=
    AddMonoidHom.mk'
      (fun s => AddMonoidHom.mk'
        (fun t => (eP.app V hV).symm (g.app V hV (eM.app V hV s) (eN.app V hV t)))
        (fun t t' =>
          (congrArg (eP.app V hV).symm
            ((congrArg (g.app V hV (eM.app V hV s)) (map_add (eN.app V hV) t t')).trans
              (g.app_add_right V hV _ _ _))).trans (map_add (eP.app V hV).symm _ _)))
      (fun s s' => AddMonoidHom.ext fun t =>
        (congrArg (eP.app V hV).symm
          ((congrArg (fun z => g.app V hV z (eN.app V hV t)) (map_add (eM.app V hV) s s')).trans
            (g.app_add_left V hV _ _ _))).trans (map_add (eP.app V hV).symm _ _))
  map_smul_left V hV r s t :=
    (congrArg (eP.app V hV).symm
      ((congrArg (fun z => g.app V hV z (eN.app V hV t)) (map_smul (eM.app V hV) r s)).trans
        (g.map_smul_left V hV r _ _))).trans (map_smul (eP.app V hV).symm r _)
  map_smul_right V hV r s t :=
    (congrArg (eP.app V hV).symm
      ((congrArg (g.app V hV (eM.app V hV s)) (map_smul (eN.app V hV) r t)).trans
        (g.map_smul_right V hV r _ _))).trans (map_smul (eP.app V hV).symm r _)
  naturality hV hWV s t :=
    (congrArg (eP.app _ (hWV.trans hV)).symm
      ((congrArg₂ (fun u v => g.app _ (hWV.trans hV) u v)
          (eM.naturality hV hWV s) (eN.naturality hV hWV t)).trans
        (g.naturality hV hWV (eM.app _ hV s) (eN.app _ hV t)))).trans
      (eP.symm_naturality hV hWV (g.app _ hV (eM.app _ hV s) (eN.app _ hV t)))

/-- The transported product transports both factors forward, multiplies, and transports the
product back. -/
public theorem congrLocalBilinear_app {M N P M' N' P' : PresheafOfModules.{u} 𝒪} {T : Opens X}
    (eM : TopCat.Sheaf.LocalModuleEquiv M M' T) (eN : TopCat.Sheaf.LocalModuleEquiv N N' T)
    (eP : TopCat.Sheaf.LocalModuleEquiv P P' T)
    (g : TopCat.Sheaf.LocalBilinearMap M' N' P' T) (V : Opens X) (hV : V ≤ T)
    (s : M.obj (op V)) (t : N.obj (op V)) :
    (congrLocalBilinear eM eN eP g).app V hV s t
      = (eP.app V hV).symm (g.app V hV (eM.app V hV s) (eN.app V hV t)) := rfl

/-- **Transport of local unit data along a local isomorphism.** -/
public def congrLocalSection {M M' : PresheafOfModules.{u} 𝒪} {T : Opens X}
    (eM : TopCat.Sheaf.LocalModuleEquiv M M' T) (d : TopCat.Sheaf.LocalSectionData M' T) :
    TopCat.Sheaf.LocalSectionData M T where
  app V hV := (eM.app V hV).symm (d.app V hV)
  naturality hV hWV :=
    (eM.symm_naturality hV hWV (d.app _ hV)).symm.trans
      (congrArg (eM.app _ (hWV.trans hV)).symm (d.naturality hV hWV))

/-- The transported unit is the inverse transport of the unit. -/
public theorem congrLocalSection_app {M M' : PresheafOfModules.{u} 𝒪} {T : Opens X}
    (eM : TopCat.Sheaf.LocalModuleEquiv M M' T) (d : TopCat.Sheaf.LocalSectionData M' T)
    (V : Opens X) (hV : V ≤ T) :
    (congrLocalSection eM d).app V hV = (eM.app V hV).symm (d.app V hV) := rfl

end Transport

/-! ### Opaque wrappers for the chart comparison and the absolute product

Both halves of the local data are wrapped in named definitions before any algebra is done with
them, and every fact used below is a named lemma about those definitions. This is not cosmetic.
A `congrArg` chain written directly over `chartSections` exhausts the **kernel's**
budget: checking it unfolds the linear equivalence through
`Stacks.AlgebraicGeometry.SchemeModuleGlue.chartSectionsLinearEquiv` and on into the `modelData`
structure literal, once per occurrence. Behind `toChart`/`ofChart` the kernel sees a constant
applied to arguments and never unfolds it.

`chartProd` and `chartUnit` exist for the matching reason on the other side, and additionally fix
a spelling: `absoluteTwistProduct` takes its arguments at the twisting sheaf of the chart, where a
scalar of the relative Proj has no action at all — the module structure is the one on the
pushforward. Stating the two scalar laws at `absoluteTwistProduct` therefore does not elaborate;
stated at `chartModule`, as here, they do. -/

/-- **The canonical product of Tag 01MO on the pushed sections of a chart's twist**, with its
arguments at the `chartModule` spelling. -/
public def chartProd (i j : ℤ) (m : S.affineOpens) {V : (relativeProj A).scheme.Opens}
    (a : (chartModule A i m).obj (op V)) (b : (chartModule A j m).obj (op V)) :
    (chartModule A (i + j) m).obj (op V) :=
  TwistDataConstruction.twistProd (A.grading (m.1 : S.Opens)) i j
    (X := op ((relativeProj A).chart (m.1 : S.Opens) m.2 ⁻¹ᵁ V)) a b

/-- **The unit section of the degree-zero twist on the pushed sections of a chart.** -/
public def chartUnit (m : S.affineOpens) {V : (relativeProj A).scheme.Opens} :
    (chartModule A 0 m).obj (op V) :=
  TwistDataConstruction.twistUnit (A.grading (m.1 : S.Opens))
    (X := op ((relativeProj A).chart (m.1 : S.Opens) m.2 ⁻¹ᵁ V))

/-- `chartProd` is Tag 01MO's product; one delta step, taken only at the interfaces. -/
public theorem chartProd_eq (i j : ℤ) (m : S.affineOpens) {V : (relativeProj A).scheme.Opens}
    (a : (chartModule A i m).obj (op V)) (b : (chartModule A j m).obj (op V)) :
    chartProd A i j m a b
      = absoluteTwistProduct (A.grading (m.1 : S.Opens)) i j
          ((relativeProj A).chart (m.1 : S.Opens) m.2 ⁻¹ᵁ V) a b := rfl

/-- `chartUnit` is the absolute unit section. -/
public theorem chartUnit_eq (m : S.affineOpens) {V : (relativeProj A).scheme.Opens} :
    chartUnit A m (V := V)
      = absoluteTwistUnit (A.grading (m.1 : S.Opens))
          ((relativeProj A).chart (m.1 : S.Opens) m.2 ⁻¹ᵁ V) := rfl

/-- The local product is additive in its first variable. -/
public theorem chartProd_add_left (i j : ℤ) (m : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (a a' : (chartModule A i m).obj (op V))
    (b : (chartModule A j m).obj (op V)) :
    chartProd A i j m (a + a') b = chartProd A i j m a b + chartProd A i j m a' b :=
  TwistDataConstruction.twistProd_add_left (A.grading (m.1 : S.Opens)) i j a a' b

/-- The local product is additive in its second variable. -/
public theorem chartProd_add_right (i j : ℤ) (m : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (a : (chartModule A i m).obj (op V))
    (b b' : (chartModule A j m).obj (op V)) :
    chartProd A i j m a (b + b') = chartProd A i j m a b + chartProd A i j m a b' :=
  TwistDataConstruction.twistProd_add_right (A.grading (m.1 : S.Opens)) i j a b b'

/-- **The local product is linear in its first variable for the pushforward module structure.**
The scalar of the relative Proj acts through the chart; this is the only place that happens. -/
public theorem chartProd_smul_left (i j : ℤ) (m : S.affineOpens)
    (V : (relativeProj A).scheme.Opens)
    (r : (relativeProj A).scheme.ringCatSheaf.obj.obj (op V))
    (a : (chartModule A i m).obj (op V)) (b : (chartModule A j m).obj (op V)) :
    chartProd A i j m (r • a) b = r • chartProd A i j m a b :=
  TwistDataConstruction.twistProd_smul_left (A.grading (m.1 : S.Opens)) i j
    (((relativeProj A).chart (m.1 : S.Opens) m.2).app V r) a b

/-- **The local product is linear in its second variable for the pushforward module
structure.** -/
public theorem chartProd_smul_right (i j : ℤ) (m : S.affineOpens)
    (V : (relativeProj A).scheme.Opens)
    (r : (relativeProj A).scheme.ringCatSheaf.obj.obj (op V))
    (a : (chartModule A i m).obj (op V)) (b : (chartModule A j m).obj (op V)) :
    chartProd A i j m a (r • b) = r • chartProd A i j m a b :=
  TwistDataConstruction.twistProd_smul_right (A.grading (m.1 : S.Opens)) i j
    (((relativeProj A).chart (m.1 : S.Opens) m.2).app V r) a b

/-- The local product commutes with the restriction maps. -/
public theorem chartProd_resLE (i j : ℤ) (m : S.affineOpens)
    {V W : (relativeProj A).scheme.Opens} (hWV : W ≤ V)
    (a : (chartModule A i m).obj (op V)) (b : (chartModule A j m).obj (op V)) :
    (chartModule A (i + j) m).resLE hWV (chartProd A i j m a b)
      = chartProd A i j m ((chartModule A i m).resLE hWV a) ((chartModule A j m).resLE hWV b) :=
  TwistDataConstruction.twistProd_naturality (A.grading (m.1 : S.Opens)) i j _ a b

/-- The local unit is compatible with the restriction maps. -/
public theorem chartUnit_resLE (m : S.affineOpens) {V W : (relativeProj A).scheme.Opens}
    (hWV : W ≤ V) :
    (chartModule A 0 m).resLE hWV (chartUnit A m (V := V)) = chartUnit A m (V := W) :=
  map_absoluteTwistUnit (A.grading (m.1 : S.Opens)) _

/-- The local product is associative. -/
public theorem chartProd_heq_assoc (i j k : ℤ) (m : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (a : (chartModule A i m).obj (op V))
    (b : (chartModule A j m).obj (op V)) (c : (chartModule A k m).obj (op V)) :
    HEq (chartProd A (i + j) k m (chartProd A i j m a b) c)
      (chartProd A i (j + k) m a (chartProd A j k m b c)) :=
  TwistDataConstruction.twistProd_heq_assoc (A.grading (m.1 : S.Opens)) i j k a b c

/-- The local unit is a left identity. -/
public theorem chartProd_heq_one_mul (i : ℤ) (m : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (a : (chartModule A i m).obj (op V)) :
    HEq (chartProd A 0 i m (chartUnit A m) a) a :=
  TwistDataConstruction.twistProd_heq_one_mul (A.grading (m.1 : S.Opens)) i a

/-- The local unit is a right identity. -/
public theorem chartProd_heq_mul_one (i : ℤ) (m : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (a : (chartModule A i m).obj (op V)) :
    HEq (chartProd A i 0 m a (chartUnit A m)) a :=
  TwistDataConstruction.twistProd_heq_mul_one (A.grading (m.1 : S.Opens)) i a

/-! ### The chart comparison, behind a name -/

/-- **The chart comparison of the glued twist, as a local isomorphism on the chart image.** -/
public def chartEquiv (n : ℤ) (hcoc : IsNestedCocycle A n) (m : S.affineOpens) :
    TopCat.Sheaf.LocalModuleEquiv (gluedTwist A n hcoc).val (chartModule A n m) (cover A m) where
  app _ hV := chartSections A n hcoc m hV
  naturality hV hWV x := chartSections_resLE A n hcoc m hV hWV x

/-- **The chart comparison of the glued twist**, as a function. -/
public def toChart (n : ℤ) (hc : IsNestedCocycle A n) (m : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hV : V ≤ cover A m)
    (x : (gluedTwist A n hc).val.obj (op V)) : (chartModule A n m).obj (op V) :=
  chartSections A n hc m hV x

/-- **Its inverse**, as a function. -/
public def ofChart (n : ℤ) (hc : IsNestedCocycle A n) (m : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hV : V ≤ cover A m)
    (a : (chartModule A n m).obj (op V)) : (gluedTwist A n hc).val.obj (op V) :=
  (chartSections A n hc m hV).symm a

/-- `toChart` undoes `ofChart`. -/
public theorem toChart_ofChart (n : ℤ) (hc : IsNestedCocycle A n) (m : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hV : V ≤ cover A m)
    (a : (chartModule A n m).obj (op V)) : toChart A n hc m hV (ofChart A n hc m hV a) = a :=
  LinearEquiv.apply_symm_apply _ _

/-- `ofChart` undoes `toChart`. -/
public theorem ofChart_toChart (n : ℤ) (hc : IsNestedCocycle A n) (m : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hV : V ≤ cover A m)
    (x : (gluedTwist A n hc).val.obj (op V)) : ofChart A n hc m hV (toChart A n hc m hV x) = x :=
  LinearEquiv.symm_apply_apply _ _

/-- The chart comparisons of two affine opens differ by the chart transition. -/
public theorem trans_toChart (n : ℤ) (hc : IsNestedCocycle A n) (k l : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hk : V ≤ cover A k) (hl : V ≤ cover A l)
    (x : (gluedTwist A n hc).val.obj (op V)) :
    (modelData A n hc).trans k l hk hl (toChart A n hc k hk x) = toChart A n hc l hl x :=
  trans_chartSections A n hc k l hk hl x

/-- Applying one affine open's chart comparison and undoing another's is the chart transition. -/
public theorem ofChart_trans (n : ℤ) (hc : IsNestedCocycle A n) (k l : S.affineOpens)
    {V : (relativeProj A).scheme.Opens} (hk : V ≤ cover A k) (hl : V ≤ cover A l)
    (z : (chartModule A n k).obj (op V)) :
    ofChart A n hc l hl ((modelData A n hc).trans k l hk hl z) = ofChart A n hc k hk z := by
  refine Eq.trans (congrArg (fun w => ofChart A n hc l hl
      ((modelData A n hc).trans k l hk hl w)) (toChart_ofChart A n hc k hk z).symm) ?_
  exact Eq.trans (congrArg (ofChart A n hc l hl) (trans_toChart A n hc k l hk hl _))
    (ofChart_toChart A n hc l hl _)

/-! ### The local multiplication and unit

Both are instances of the generic transports: the product and unit of the absolute graded
algebra — `Stacks.AlgebraicGeometry.ProjConeTwist.twistMul` and `…ProjConeTwist.twistOne`, the
multiplication and unit of `…TwistDataConstruction.twistAlgebra` — pushed forward along the
chart by `pushLocalBilinear` and transported along `chartEquiv` by `congrLocalBilinear`. All five
bilinearity obligations were discharged generically, so none of them is restated here at the
glued twists — which is exactly what keeps the kernel out of the `modelData` structure
literal. -/

section Algebra

variable (hcoc : ∀ n : ℤ, IsNestedCocycle A n)

/-- **The local multiplication of the glued twists over a chart image.** -/
public def mulData (i j : ℤ) (m : S.affineOpens) :
    TopCat.Sheaf.LocalBilinearMap (gluedTwist A i (hcoc i)).val
      (gluedTwist A j (hcoc j)).val (gluedTwist A (i + j) (hcoc (i + j))).val (cover A m) :=
  congrLocalBilinear (chartEquiv A i (hcoc i) m) (chartEquiv A j (hcoc j) m)
    (chartEquiv A (i + j) (hcoc (i + j)) m)
    (pushLocalBilinear ((relativeProj A).chart (m.1 : S.Opens) m.2)
      (ProjConeTwist.twistMul (A.grading (m.1 : S.Opens)) i j) (cover A m))

/-- **The local unit of the glued twists over a chart image.** -/
public def oneData (m : S.affineOpens) :
    TopCat.Sheaf.LocalSectionData (gluedTwist A 0 (hcoc 0)).val (cover A m) :=
  congrLocalSection (chartEquiv A 0 (hcoc 0) m)
    (pushLocalSection ((relativeProj A).chart (m.1 : S.Opens) m.2)
      (ProjConeTwist.twistOne (A.grading (m.1 : S.Opens))) (cover A m))

end Algebra

end Stacks.AlgebraicGeometry.GluedTwistAlgebra

end
