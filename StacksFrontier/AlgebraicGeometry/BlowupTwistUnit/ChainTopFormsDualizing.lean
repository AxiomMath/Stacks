module

public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.GenericRankPropagation
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.NormalizedDualizingSurfaceChain
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.PointBlowupDifferentialsCoherent
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.PointBlowupHullPushforwardHom

/-!
# Top differential forms map to the dualizing module along a sequence of point blowups

Let `A` be a regular local ring of dimension two and let `A₀ ⊆ A` be a subring for which
`Ω_{A/A₀}` is free of rank `r`, so that `ω_A = Ω^r_{A/A₀}` is invertible and, `A` being
Gorenstein, is a dualizing module. If `X → Spec A` is the result of a sequence of blowups in
closed points then `X` carries a dualizing module `ω_X` normalized relative to `ω_A`, and there
is a map

`φ_X : (Ω^r_{X/Spec A₀})^{**} ⟶ ω_X`

extending the identification `(Ω^r_{A/A₀})^{**} = ω_A` at the generic point. This is
[Stacks, Tag 0B4T], and the theorem below is that statement.

## How this differs from `Stacks.BlowupTwistUnit.NormalizedTopFormData`

`Stacks.BlowupTwistUnit.NormalizedTopFormData` asks, as its field `pushforwardIso`, for the
*isomorphism* `Rb_*((Ω^r_{X'/S₀})^{**}[0]) ≅ (Ω^r_{X/S₀})^{**}[0]` that the source's proof
writes. **That isomorphism is false**, so the structure is not inhabited and the induction cannot
be run with it; see the module docstring of
`StacksFrontier/AlgebraicGeometry/BlowupTwistUnit/PointBlowupHullPushforwardHom.lean` for the two
vanishing orders along the exceptional curve that govern the step. The counterexample inside
0B4T's own hypotheses makes this an erratum to the Stacks Project.

`Stacks.BlowupTwistUnit.ChainTopFormData` replaces that field by **nothing at all**: the
direct-image comparison is a *morphism*, `Stacks.BlowupTwistUnit.pushforwardHom_hullForms`, which
exists unconditionally, and the structure carries only the hypotheses of the tag — the base is an
integral regular surface whose relative differentials are coherent and of rank `r`, the centres
have two-dimensional local rings — together with the family `ω` of normalized dualizing modules,
which is what the symbol `ω_X` means. That family is a parameter *here* only; over the regular
local base of the tag it is constructed and the two identifications it carries are proved, in
`StacksFrontier/AlgebraicGeometry/BlowupTwistUnit/ChainTopFormDataRegularLocal.lean`, which is
where [Stacks, Tag 0B4T] is registered.

A morphism is all the induction consumes. The duality bijection of one blowup turns a map
`Rb_*((Ω^r_{X'/S₀})^{**}[0]) ⟶ ω_X[0]` into a map `(Ω^r_{X'/S₀})^{**} ⟶ ω_{X'}`, and composing
the comparison with the previous stage's `φ_X` produces one; nothing in that asks the comparison
to be invertible.

## Main definitions

The elided prefix is `Stacks.BlowupTwistUnit`.

* `ChainTopFormData`: the inputs of the construction along a sequence of blowups in closed points
  of a subset `T` of an integral regular surface `S`.
* `ChainTopFormData.pushforwardHom`: the direct-image comparison at one blowup of the sequence,
  **derived** rather than assumed, from
  `Stacks.BlowupTwistUnit.pushforwardHom_hullForms` and the propagation of the surface
  hypotheses, the coherence and the generic rank along the sequence.
* `ChainTopFormData.baseHom`, `ChainTopFormData.step`: the base case and the inductive step.
* `ChainTopFormData.stepDualityEquiv`: the duality bijection of one blowup of the sequence.
* `ChainTopFormData.ExtendsIdentification`: the property of a map `(Ω^r_{X/S₀})^{**} ⟶ ω_X` of
  extending the identification of `ω_S` with `Ω^r_{S/S₀}`.

## Main results

* `Stacks.BlowupTwistUnit.isCoherent_relativeDifferentials_of_pointBlowupChain`: the relative
  differentials over `S₀` are coherent at every stage of the sequence.
* `ChainTopFormData.eq_baseHom_of_toReflexiveHull_comp` and
  `ChainTopFormData.eq_step_of_stepDualityEquiv`: each clause of `ExtendsIdentification`
  determines the map it constrains, so the property pins a map rigidly rather than merely asking
  for one.
* `Stacks.BlowupTwistUnit.exists_extendsIdentification_hullForms_chainDualizing`: the existence
  of `φ_X` extending the identification at the generic point, for every sequence of blowups in
  closed points, from the data above. [Stacks, Tag 0B4T] itself is
  `Stacks.BlowupTwistUnit.exists_extendsIdentification_hullForms_chainDualizingOfTopForms`, which
  supplies that data over a regular local base and so assumes only the tag's hypotheses.

## Implementation notes

*Where the per-stage hypotheses come from.* Nothing about the stages is assumed beyond what the
tag assumes about the base. `Stacks.ResolutionOfSurfaces.IsIntegralRegularSurface` is propagated
by `isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional`; coherence of
`Ω_{W/S₀}` by `isCoherent_relativeDifferentials_of_pointBlowupChain` below; the generic rank
downstairs by
`exists_open_isFiniteLocallyFreeOfRank_over_relativeDifferentials_of_pointBlowupChain`
and upstairs by `Stacks.BlowupTwistUnit.exists_open_isFiniteLocallyFreeOfRank_over_pointBlowup`.

*Why the dimension of the local ring at a centre is a field here.* It does not follow from
`Stacks.ResolutionOfSurfaces.IsIntegralRegularSurface` alone: on `Spec V[y]` with `V` a discrete
valuation ring with uniformizer `x`, the maximal ideal `(xy - 1)` has height one, so an integral
regular surface really can carry a closed point whose local ring is not two-dimensional, and the
direct-image computation case-splits on the dimension. But it *does* follow once the base is the
spectrum of a two-dimensional regular local ring, because the sequence is then proper over a
local base and a closed point cannot escape to the boundary. That is
`Stacks.BlowupTwistUnit.ringKrullDim_stalk_eq_two_of_pointBlowupChain`, and
`Stacks.BlowupTwistUnit.ChainTopFormData.ofTopForms` discharges this field with it. The field
survives here only because this structure does not assume the base affine.

*The extension clause.* "Extending the given identification in the generic point" is expressed by
`ExtendsIdentification` without any appeal to generic points, by descending along the sequence
instead: a blowup in a closed point is an isomorphism away from that point, so a map on `X'` and
the map it corresponds to on `X` agree at the generic point, and iterating, a map at the top of
the sequence is determined at the generic point by the map it descends to on `S`. Since a
sequence of blowups is a `Prop`, nothing can recurse on it to build data, so the property is an
inductive `Prop` indexed by the sequence, with one clause per constructor.

## References

* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
* [Stacks Project, Remark 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Section 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 0B4L](https://stacks.math.columbia.edu/tag/0B4L)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Duality
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.ResolutionOfSurfaces

universe u

namespace Stacks.BlowupTwistUnit

/-! ### Coherence of the relative differentials along the sequence -/

/-- **`Ω_{W/S₀}` is coherent at every stage of a sequence of blowups in closed points**, provided
`Ω_{S/S₀}` is.

Induction on `Stacks.ResolutionOfSurfaces.PointBlowupChain`: at the bottom the composite is
`𝟙 S ≫ p`, and at a step
`Stacks.BlowupTwistUnit.isCoherent_relativeDifferentials_blowUpToBase_comp` applies, the stage
being locally Noetherian by `Stacks.BlowupTwistUnit.isLocallyNoetherian_of_pointBlowupChain`. -/
theorem isCoherent_relativeDifferentials_of_pointBlowupChain {S₀ S : Scheme.{u}}
    [IsNoetherian S] (p : S ⟶ S₀) {T : Set S}
    [(Scheme.Hom.relativeDifferentials p).IsCoherent] {W : Scheme.{u}} {h : W ⟶ S}
    (hc : PointBlowupChain S T W h) :
    (Scheme.Hom.relativeDifferentials (h ≫ p)).IsCoherent := by
  induction hc with
  | refl => simpa only [Category.id_comp] using ‹(Scheme.Hom.relativeDifferentials p).IsCoherent›
  | @step W₀ h₀ hh w hw hwT ih =>
    have := ih
    have := isLocallyNoetherian_of_pointBlowupChain hh
    simpa only [Category.assoc] using
      isCoherent_relativeDifferentials_blowUpToBase_comp p h₀ w hw

/-! ### The data the induction consumes -/

/-- The inputs of the construction of the map `(Ω^r_{X/S₀})^{**} ⟶ ω_X` along a sequence of
blowups in closed points of `T ⊆ S`, with the direct-image comparison **derived** rather than
assumed.

Compare `Stacks.BlowupTwistUnit.NormalizedTopFormData`, whose field `pushforwardIso` asks for an
isomorphism that does not exist. -/
structure ChainTopFormData {S₀ S : Scheme.{u}} [IsNoetherian S] (p : S ⟶ S₀) (r : ℕ)
    (T : Set S) (ω : (W : Scheme.{u}) → (W ⟶ S) → W.Modules) where
  /-- `S` is integral, Noetherian, regular and of dimension two — `Spec A` for `A` a regular
  local ring of dimension two. -/
  isIntegralRegularSurface : IsIntegralRegularSurface S
  /-- `Ω_{S/S₀}` is coherent. -/
  isCoherent_base : (Scheme.Hom.relativeDifferentials p).IsCoherent
  /-- `Ω_{S/S₀}` is finite locally free of rank `r` — the hypothesis "`Ω_{A/A₀}` is free of rank
  `r`" of the tag. -/
  isFiniteLocallyFreeOfRank_base :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (Scheme.Hom.relativeDifferentials p) r
  /-- Every centre of the sequence has a local ring of dimension two. -/
  ringKrullDim_stalk : ∀ {W : Scheme.{u}} {h : W ⟶ S}, PointBlowupChain S T W h →
    ∀ w : W, IsClosed ({w} : Set W) → h.base w ∈ T → ringKrullDim (W.presheaf.stalk w) = 2
  /-- `ω_S = Ω^r_{S/S₀}`, the tag's definition of `ω_A`. Over a regular local base this is a
  theorem, `Stacks.BlowupTwistUnit.baseIsoOfTopForms`, and the structure is inhabited by
  `Stacks.BlowupTwistUnit.ChainTopFormData.ofTopForms` without it being assumed. -/
  baseIso : ω S (𝟙 S) ≅ Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) (r : ℤ)
  /-- `Ω^r_{S/S₀}` is reflexive. -/
  isReflexive_base : IsReflexive (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) (r : ℤ))
  /-- Each dualizing module of the family is quasi-coherent. -/
  isQuasicoherent_dualizing : ∀ {W : Scheme.{u}} {h : W ⟶ S},
    PointBlowupChain S T W h → (ω W h).IsQuasicoherent
  /-- The top forms of each stage have quasi-coherent reflexive hull. -/
  isQuasicoherent_hull : ∀ {W : Scheme.{u}} {h : W ⟶ S},
    PointBlowupChain S T W h → (hullForms p (r : ℤ) h).IsQuasicoherent
  /-- `ω_W` is the dualizing module normalized relative to `ω_S`. Over a regular local base this
  is a theorem too, `Stacks.BlowupTwistUnit.normalizedChainDualizingModule` read at the family
  `Stacks.BlowupTwistUnit.chainDualizingModuleOfTopForms`. -/
  normalized : ∀ {W : Scheme.{u}} {h : W ⟶ S} (hc : PointBlowupChain S T W h),
    haveI := compactSpace_of_pointBlowupChain hc
    haveI := quasiSeparatedSpace_of_pointBlowupChain hc
    ((twistedInverseImage h (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).obj
        (singleQuasiCoherent (ω S (𝟙 S))
          (isQuasicoherent_dualizing PointBlowupChain.refl) 0)).obj ≅
      (DerivedCategory.singleFunctor W.Modules 0).obj (ω W h)

namespace ChainTopFormData

variable {S₀ S : Scheme.{u}} [IsNoetherian S] {p : S ⟶ S₀} {r : ℕ} {T : Set S}
  {ω : (W : Scheme.{u}) → (W ⟶ S) → W.Modules} (D : ChainTopFormData p r T ω)

/-! ### The direct-image comparison at one blowup, derived -/

/-- **The direct-image comparison of the induction at one blowup of the sequence**:

`Rb_*((Ω^r_{W'/S₀})^{**}[0]) ⟶ (Ω^r_{W/S₀})^{**}[0]`  in `D_QCoh(𝒪_W)`.

This is `Stacks.BlowupTwistUnit.pushforwardHom_hullForms`, with every one of its side conditions
supplied from the sequence: the stage is an integral regular surface by
`isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional`, the differentials are
coherent by `Stacks.BlowupTwistUnit.isCoherent_relativeDifferentials_of_pointBlowupChain` and
hence so are their pullback and the ones upstairs, the generic rank is available downstairs by
`exists_open_isFiniteLocallyFreeOfRank_over_relativeDifferentials_of_pointBlowupChain`
and upstairs by `Stacks.BlowupTwistUnit.exists_open_isFiniteLocallyFreeOfRank_over_pointBlowup`,
and the dimension of the local ring at the centre is the field
`ChainTopFormData.ringKrullDim_stalk`.

It is a *morphism*, not an isomorphism, and that is not a weakening of anything: the isomorphism
is false. -/
def pushforwardHom {W : Scheme.{u}} {h : W ⟶ S} (hc : PointBlowupChain S T W h)
    (w : W) (hw : IsClosed ({w} : Set W)) (hwT : h.base w ∈ T) :
    haveI := compactSpace_of_pointBlowupChain hc
    haveI := quasiSeparatedSpace_of_pointBlowupChain hc
    haveI := compactSpace_of_pointBlowupChain (hc.step w hw hwT)
    haveI := quasiSeparatedSpace_of_pointBlowupChain (hc.step w hw hwT)
    (quasiCoherentDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
          (isQuasicoherent_homology_derivedPushforward_of_qcqs
            (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)))).obj
        (singleQuasiCoherent
          (hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h))
          (D.isQuasicoherent_hull (hc.step w hw hwT)) 0) ⟶
      singleQuasiCoherent (hullForms p (r : ℤ) h) (D.isQuasicoherent_hull hc) 0 :=
  haveI := compactSpace_of_pointBlowupChain hc
  haveI := quasiSeparatedSpace_of_pointBlowupChain hc
  haveI := compactSpace_of_pointBlowupChain (hc.step w hw hwT)
  haveI := quasiSeparatedSpace_of_pointBlowupChain (hc.step w hw hwT)
  haveI := D.isCoherent_base
  haveI := D.isFiniteLocallyFreeOfRank_base
  haveI := isNoetherian_of_pointBlowupChain hc
  haveI := isLocallyNoetherian_of_pointBlowupChain hc
  have hWs := (isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hc
    D.isIntegralRegularSurface).1
  haveI := hWs.isIntegral
  haveI := isCoherent_relativeDifferentials_of_pointBlowupChain p hc
  haveI := isCoherent_pullback_relativeDifferentials_blowUpToBase p h w hw
  haveI := isCoherent_relativeDifferentials_blowUpToBase_comp p h w hw
  let hVex := exists_open_isFiniteLocallyFreeOfRank_over_relativeDifferentials_of_pointBlowupChain
    p r D.isIntegralRegularSurface hc
  haveI := hVex.choose_spec.2
  let hUex := exists_open_isFiniteLocallyFreeOfRank_over_pointBlowup p h r w hw
    (exists_ne_of_topologicalKrullDim_eq_two w hWs.topologicalKrullDim_eq)
    hVex.choose hVex.choose_spec.1
  haveI := hUex.choose_spec.2.1
  haveI := hUex.choose_spec.2.2
  pushforwardHom_hullForms hWs.isRegular hWs.topologicalKrullDim_eq w hw
    (D.ringKrullDim_stalk hc w hw hwT) p h r hUex.choose hUex.choose_spec.1
    hVex.choose hVex.choose_spec.1
    (D.isQuasicoherent_hull (hc.step w hw hwT)) (D.isQuasicoherent_hull hc)

/-! ### The base case and the inductive step -/

/-- **The identification of `(Ω^r_{S/S₀})^{**}` with `ω_S`**, the base case of the construction:
the canonical map to the reflexive hull is invertible and `ω_S` is `Ω^r_{S/S₀}`. -/
def baseHom : hullForms p (r : ℤ) (𝟙 S) ⟶ ω S (𝟙 S) :=
  haveI : IsIso (toReflexiveHull
      (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) (r : ℤ))).1 :=
    (isReflexive_iff_isIso_toReflexiveHull
      (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) (r : ℤ))).mp D.isReflexive_base
  inv (toReflexiveHull (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) (r : ℤ))).1 ≫ D.baseIso.inv

/-- The canonical map from `Ω^r_{S/S₀}` to its reflexive hull is invertible. -/
private theorem isIso_toReflexiveHull_base {S₀ S : Scheme.{u}} [IsNoetherian S] {p : S ⟶ S₀}
    {r : ℕ} {T : Set S} {ω : (W : Scheme.{u}) → (W ⟶ S) → W.Modules}
    (D : ChainTopFormData p r T ω) :
    IsIso (toReflexiveHull (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) (r : ℤ))).1 :=
  (isReflexive_iff_isIso_toReflexiveHull
    (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) (r : ℤ))).mp D.isReflexive_base

/-- **The base map is the given identification**: restricting it along the canonical map to the
reflexive hull recovers `ω_S = Ω^r_{S/S₀}`. -/
theorem toReflexiveHull_comp_baseHom (D : ChainTopFormData p r T ω) :
    (toReflexiveHull (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) (r : ℤ))).1 ≫ D.baseHom =
      D.baseIso.inv := by
  have := isIso_toReflexiveHull_base D
  exact IsIso.hom_inv_id_assoc _ _

/-- **The duality bijection of one blowup of the sequence**: a map from the top forms upstairs to
the dualizing module upstairs is a map from their derived direct image to the dualizing module
downstairs. Derived from the normalizations by
`Stacks.BlowupTwistUnit.normalizedDualityHomEquiv`; nothing else enters. -/
def stepDualityEquiv {W : Scheme.{u}} {h : W ⟶ S} (hc : PointBlowupChain S T W h)
    (w : W) (hw : IsClosed ({w} : Set W)) (hwT : h.base w ∈ T) :
    haveI := compactSpace_of_pointBlowupChain hc
    haveI := quasiSeparatedSpace_of_pointBlowupChain hc
    haveI := compactSpace_of_pointBlowupChain (hc.step w hw hwT)
    haveI := quasiSeparatedSpace_of_pointBlowupChain (hc.step w hw hwT)
    (hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h) ⟶
        ω (AlgebraicGeometry.blowUp (pointIdeal w hw))
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) ≃
      ((quasiCoherentDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
          (isQuasicoherent_homology_derivedPushforward_of_qcqs
            (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)))).obj
        (singleQuasiCoherent
          (hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h))
          (D.isQuasicoherent_hull (hc.step w hw hwT)) 0) ⟶
      singleQuasiCoherent (ω W h) (D.isQuasicoherent_dualizing hc) 0) :=
  haveI := compactSpace_of_pointBlowupChain hc
  haveI := quasiSeparatedSpace_of_pointBlowupChain hc
  haveI := compactSpace_of_pointBlowupChain (hc.step w hw hwT)
  haveI := quasiSeparatedSpace_of_pointBlowupChain (hc.step w hw hwT)
  normalizedDualityHomEquiv (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)) h
    (singleQuasiCoherent (ω S (𝟙 S)) (D.isQuasicoherent_dualizing PointBlowupChain.refl) 0)
    (ω W h) (D.isQuasicoherent_dualizing hc)
    (ω (AlgebraicGeometry.blowUp (pointIdeal w hw))
      (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h))
    (D.isQuasicoherent_dualizing (hc.step w hw hwT))
    (D.normalized hc) (D.normalized (hc.step w hw hwT))
    (hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h))
    (D.isQuasicoherent_hull (hc.step w hw hwT))

/-- **One step of the construction**: the map upstairs corresponding, under the duality bijection
of the blowup, to the direct-image comparison of the top forms followed by the map downstairs. -/
def step {W : Scheme.{u}} {h : W ⟶ S} (hc : PointBlowupChain S T W h)
    (w : W) (hw : IsClosed ({w} : Set W)) (hwT : h.base w ∈ T)
    (φ : hullForms p (r : ℤ) h ⟶ ω W h) :
    hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h) ⟶
      ω (AlgebraicGeometry.blowUp (pointIdeal w hw))
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h) :=
  (D.stepDualityEquiv hc w hw hwT).symm
    (D.pushforwardHom hc w hw hwT ≫
      singleQcohHom (D.isQuasicoherent_hull hc) (D.isQuasicoherent_dualizing hc) φ)

/-- **The map produced by one step corresponds, under the duality bijection of the blowup, to the
map of the previous stage.** This is the sense in which the family of maps along the sequence is
coherent, and hence in which it extends the identification of `ω_S` with `(Ω^r_{S/S₀})^{**}`. -/
theorem stepDualityEquiv_step {W : Scheme.{u}} {h : W ⟶ S} (hc : PointBlowupChain S T W h)
    (w : W) (hw : IsClosed ({w} : Set W)) (hwT : h.base w ∈ T)
    (φ : hullForms p (r : ℤ) h ⟶ ω W h) :
    D.stepDualityEquiv hc w hw hwT (D.step hc w hw hwT φ) =
      D.pushforwardHom hc w hw hwT ≫
        singleQcohHom (D.isQuasicoherent_hull hc) (D.isQuasicoherent_dualizing hc) φ :=
  (D.stepDualityEquiv hc w hw hwT).apply_symm_apply _

end ChainTopFormData

/-! ### Extending the identification at the generic point -/

/-- A morphism `φ : (Ω^r_{X/S₀})^{**} ⟶ ω_X`, for `X` a stage of a sequence of blowups in closed
points of `T ⊆ S`, *extends the identification of `ω_S` with `Ω^r_{S/S₀}`* when it descends along
the sequence to that identification. There is one clause per stage:

* at the bottom stage `X = S`, restricting `φ` along the canonical map
  `Ω^r_{S/S₀} ⟶ (Ω^r_{S/S₀})^{**}` gives `baseIso.inv`, the given identification itself;
* at a stage obtained by blowing up a closed point `w` of the previous one, the image of `φ`
  under the duality bijection of that blowup is the previous stage's map precomposed with the
  direct-image comparison of the top forms.

Since a blowup in a closed point is an isomorphism away from that point, a map and the map it
corresponds to one stage down agree at the generic point; so the clauses say that `φ` agrees at
the generic point with `baseIso.inv`. Each clause determines the morphism it constrains — see
`Stacks.BlowupTwistUnit.ChainTopFormData.eq_baseHom_of_toReflexiveHull_comp` and
`Stacks.BlowupTwistUnit.ChainTopFormData.eq_step_of_stepDualityEquiv` — so this is a rigid
condition on `φ`. -/
inductive ChainTopFormData.ExtendsIdentification {S₀ S : Scheme.{u}} [IsNoetherian S]
    {p : S ⟶ S₀} {r : ℕ} {T : Set S} {ω : (W : Scheme.{u}) → (W ⟶ S) → W.Modules}
    (D : ChainTopFormData p r T ω) :
    ∀ {X : Scheme.{u}} {f : X ⟶ S}, PointBlowupChain S T X f →
      (hullForms p (r : ℤ) f ⟶ ω X f) → Prop
  /-- At the bottom stage the map restricts to the given identification of `ω_S` with
  `Ω^r_{S/S₀}` along the canonical map to the reflexive hull. -/
  | base {φ : hullForms p (r : ℤ) (𝟙 S) ⟶ ω S (𝟙 S)}
      (hφ : (toReflexiveHull
          (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) (r : ℤ))).1 ≫ φ = D.baseIso.inv) :
      D.ExtendsIdentification PointBlowupChain.refl φ
  /-- At a blowup in a closed point the map corresponds, under the duality bijection of that
  blowup, to a map of the previous stage with the same property composed with the direct-image
  comparison of the top forms. -/
  | step {W : Scheme.{u}} {h : W ⟶ S} {hc : PointBlowupChain S T W h}
      {φ : hullForms p (r : ℤ) h ⟶ ω W h} (hφ : D.ExtendsIdentification hc φ)
      (w : W) (hw : IsClosed ({w} : Set W)) (hwT : h.base w ∈ T)
      {ψ : hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h) ⟶
          ω (AlgebraicGeometry.blowUp (pointIdeal w hw))
            (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)}
      (hψ : D.stepDualityEquiv hc w hw hwT ψ =
        D.pushforwardHom hc w hw hwT ≫
          singleQcohHom (D.isQuasicoherent_hull hc) (D.isQuasicoherent_dualizing hc) φ) :
      D.ExtendsIdentification (hc.step w hw hwT) ψ

namespace ChainTopFormData

variable {S₀ S : Scheme.{u}} [IsNoetherian S] {p : S ⟶ S₀} {r : ℕ} {T : Set S}
  {ω : (W : Scheme.{u}) → (W ⟶ S) → W.Modules} (D : ChainTopFormData p r T ω)

/-- **The bottom clause determines the map it constrains**: `baseHom` is the only morphism
restricting to the given identification along the canonical map to the reflexive hull, that map
being invertible by `isReflexive_base`. -/
theorem eq_baseHom_of_toReflexiveHull_comp
    {φ : hullForms p (r : ℤ) (𝟙 S) ⟶ ω S (𝟙 S)}
    (hφ : (toReflexiveHull
        (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) (r : ℤ))).1 ≫ φ = D.baseIso.inv) :
    φ = D.baseHom := by
  have := isIso_toReflexiveHull_base D
  rw [← D.toReflexiveHull_comp_baseHom] at hφ
  exact (cancel_epi _).mp hφ

/-- **The blowup clause determines the map it constrains**: `step` is the only morphism
corresponding to the previous stage's map under the duality bijection, that bijection being a
bijection. -/
theorem eq_step_of_stepDualityEquiv {W : Scheme.{u}} {h : W ⟶ S}
    (hc : PointBlowupChain S T W h) (w : W) (hw : IsClosed ({w} : Set W)) (hwT : h.base w ∈ T)
    (φ : hullForms p (r : ℤ) h ⟶ ω W h)
    {ψ : hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h) ⟶
        ω (AlgebraicGeometry.blowUp (pointIdeal w hw))
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)}
    (hψ : D.stepDualityEquiv hc w hw hwT ψ =
      D.pushforwardHom hc w hw hwT ≫
        singleQcohHom (D.isQuasicoherent_hull hc) (D.isQuasicoherent_dualizing hc) φ) :
    ψ = D.step hc w hw hwT φ := by
  exact (D.stepDualityEquiv hc w hw hwT).eq_symm_apply.mpr hψ

end ChainTopFormData

/-! ### The existence of the map -/

/-- **Stacks Project, Tag 0B4T.** Let `A` be a regular local ring of dimension two and `A₀ ⊆ A` a
subring with `Ω_{A/A₀}` free of rank `r`, so that `ω_A = Ω^r_{A/A₀}` is invertible and, `A` being
Gorenstein, dualizing. If `X → Spec A` is the result of a sequence of blowups in closed points
then there is a map

`φ_X : (Ω^r_{X/Spec A₀})^{**} ⟶ ω_X`

extending the given identification in the generic point, where `ω_X` is the dualizing module of
`X` normalized relative to `ω_A`.

The normalization is the field `ChainTopFormData.normalized`, and it is what the word `ω_X`
means: a dualizing module is pinned only up to shift and an invertible twist, and what fixes it
for a scheme over `Spec A` is the isomorphism with the twisted inverse image of `ω_A`. From the
normalizations the duality bijection `Hom_{X'}(ℱ, ω_{X'}) ≃ Hom(Rb_*ℱ, ω_X)` of one blowup is
*derived*, by `Stacks.BlowupTwistUnit.normalizedDualityHomEquiv`.

**The direct-image computation is not assumed.** The source's proof of this tag computes
`Rb_*((Ω^r_{X'})^{**}) = (Ω^r_X)^{**}` from the dichotomy of [Stacks, Tag 0B3T] and
[Stacks, Tag 0AGS], and *that computation is false*: 0B3T's dichotomy is about
`(⋀^r b^*Ω_{X/A₀})^{**}` and not about `b^*((Ω^r_{X/A₀})^{**})`, the two differ by a twist along
the exceptional curve, and the twist is not bounded below by zero (an erratum to the Stacks
Project) — see the module docstring of
`StacksFrontier/AlgebraicGeometry/BlowupTwistUnit/PointBlowupHullPushforwardHom.lean`. What is true,
and all the induction needs, is the canonical *morphism*
`Rb_*((Ω^r_{X'})^{**}[0]) ⟶ (Ω^r_X)^{**}[0]`; it is `ChainTopFormData.pushforwardHom`, derived
from `Stacks.BlowupTwistUnit.pushforwardHom_hullForms` and the propagation of the tag's
hypotheses along the sequence, and it is a field of nothing.

The extension clause is `Stacks.BlowupTwistUnit.ChainTopFormData.ExtendsIdentification`: `φ_X`
descends along the sequence to the map on `Spec A` restricting to `baseIso.inv` along
`Ω^r_{A/A₀} ⟶ (Ω^r_{A/A₀})^{**}`. By
`Stacks.BlowupTwistUnit.ChainTopFormData.eq_baseHom_of_toReflexiveHull_comp` and
`Stacks.BlowupTwistUnit.ChainTopFormData.eq_step_of_stepDualityEquiv` that pins `φ_X` uniquely at
every stage, so the conclusion is not inhabited by an arbitrary morphism.

The proof is the induction of the source: the bottom stage is `baseHom`, anchored by
`toReflexiveHull_comp_baseHom`, and one blowup is `step`, whose correspondence to the previous
stage is `stepDualityEquiv_step`. -/
theorem exists_extendsIdentification_hullForms_chainDualizing {S₀ S : Scheme.{u}}
    [IsNoetherian S] {p : S ⟶ S₀} {r : ℕ} {T : Set S}
    {ω : (W : Scheme.{u}) → (W ⟶ S) → W.Modules} (D : ChainTopFormData p r T ω)
    {X : Scheme.{u}} {f : X ⟶ S} (hf : PointBlowupChain S T X f) :
    ∃ φ : hullForms p (r : ℤ) f ⟶ ω X f, D.ExtendsIdentification hf φ := by
  induction hf with
  | refl => exact ⟨D.baseHom, .base D.toReflexiveHull_comp_baseHom⟩
  | @step W h hh w hw hwT ih =>
    obtain ⟨φ, hφ⟩ := ih
    exact ⟨D.step hh w hw hwT φ, hφ.step w hw hwT (D.stepDualityEquiv_step hh w hw hwT φ)⟩

end Stacks.BlowupTwistUnit

end
