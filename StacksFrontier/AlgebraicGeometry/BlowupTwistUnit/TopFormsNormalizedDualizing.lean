module

public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.NormalizedDualityStep

/-!
# Top differential forms map to the dualizing module along a sequence of point blowups

Let `A` be a regular local ring of dimension two and let `A₀ ⊆ A` be a subring for which
`Ω_{A/A₀}` is free of rank `r`, so that `ω_A = Ω^r_{A/A₀}` is invertible and, `A` being
Gorenstein, is a dualizing module. If `X → Spec A` is the result of a sequence of blowups in
closed points then `X` carries a dualizing module `ω_X` normalized relative to `ω_A`, and there
is a map

`φ_X : (Ω^r_{X/Spec A₀})^{**} ⟶ ω_X`

extending the identification `(Ω^r_{A/A₀})^{**} = ω_A` at the generic point. The map is built by
induction along the sequence: for a blowup `b : X' ⟶ X` in a closed point the normalization makes
`ω_{X'} = b^!ω_X`, so a map out of `(Ω^r_{X'/Spec A₀})^{**}` into `ω_{X'}` is a map out of its
derived direct image into `ω_X`, and that derived direct image is `(Ω^r_{X/Spec A₀})^{**}` again.

## Main definitions

The elided prefix is `Stacks.BlowupTwistUnit`.

* `pointIdeal` and `hullForms`: the ideal sheaf cut out by a closed point, and `(Ω^n_{W/S₀})^{**}`
  for a scheme over `S₀` presented through a factorization `W ⟶ S ⟶ S₀`.
* `NormalizedTopFormData`: the inputs the construction consumes along a sequence of blowups in
  closed points of a subset `T` of a Noetherian scheme `S`. The dualizing modules form a family
  `ω` normalized relative to `ω_S`, which is what the symbol `ω_X` means — a dualizing module is
  pinned only up to shift and an invertible twist, and what fixes it for a scheme over `S` is the
  isomorphism with the twisted inverse image of `ω_S`.
* `NormalizedTopFormData.baseHom` and `NormalizedTopFormData.step`: the base case and the
  inductive step of the construction.
* `NormalizedTopFormData.stepDualityEquiv`: the duality bijection of one blowup of the sequence,
  *derived* from the normalizations by `normalizedDualityHomEquiv`.
* `NormalizedTopFormData.ExtendsIdentification`: the property of a map
  `(Ω^n_{X/S₀})^{**} ⟶ ω_X` of extending the identification of `ω_S` with `Ω^n_{S/S₀}`.

## Main results

* `Stacks.BlowupTwistUnit.compactSpace_of_pointBlowupChain`,
  `quasiSeparatedSpace_of_pointBlowupChain`, `isLocallyNoetherian_of_pointBlowupChain`: every
  stage of a sequence of blowups in closed points of a Noetherian scheme is Noetherian, hence
  quasi-compact, quasi-separated and locally Noetherian.
* `Stacks.BlowupTwistUnit.isQuasicoherent_reflexiveHull_of_pointBlowupChain`: on such a stage the
  reflexive hull of the top forms is quasi-coherent as soon as the top forms are coherent. This
  discharges the field `NormalizedTopFormData.isQuasicoherent_hull`.
* `NormalizedTopFormData.toReflexiveHull_comp_baseHom` and
  `NormalizedTopFormData.stepDualityEquiv_step`: the map at the bottom stage is the given
  identification, and the map produced by one step corresponds to the map of the previous stage.
* `NormalizedTopFormData.eq_baseHom_of_toReflexiveHull_comp` and
  `NormalizedTopFormData.eq_step_of_stepDualityEquiv`: each clause of `ExtendsIdentification`
  determines the map it constrains, so the property pins a map rigidly rather than merely asking
  for one.
* `Stacks.BlowupTwistUnit.exists_extendsIdentification_hullForms_normalizedDualizing`:
  **[Stacks, Tag 0B4T]**, the existence of `φ_X` extending the identification at the generic
  point, for every sequence of blowups in closed points.

## Implementation notes

*What the duality step costs.* Nothing. The source invokes [Stacks, Section 0AU3] twice at this
point: once for `ω_{X'} = b^!ω_X` and once for the resulting bijection between maps upstairs and
maps out of the derived direct image. Both come out of the normalizations alone:
`Stacks.Duality.twistedInverseImageObjIsoOfNormalizedObjOfQcqs` turns the pair of normalizations
into `b^×(ω_X) ≅ ω_{X'}` by the composition formula for right adjoints, and
`Stacks.Duality.relativeDualizingComplexHomEquiv` is the adjunction `Rb_* ⊣ b^×` itself, which
for a morphism of quasi-compact quasi-separated schemes is proved unconditionally
([Stacks, Tag 0A9E]). The assembly is `Stacks.BlowupTwistUnit.normalizedDualityHomEquiv`, and
`NormalizedTopFormData.stepDualityEquiv` is its instance at one blowup of the sequence.

*What is still an input.* The field `NormalizedTopFormData.pushforwardIso`, the computation
`Rb_*((Ω^n_{X'/S₀})^{**}) = (Ω^n_{X/S₀})^{**}` for one blowup in a closed point. In the source
this is the dichotomy `Ω^r_{X'} ≅ (b^*Ω^r_X)(E)` or `Ω^r_{X'} ≅ b^*Ω^r_X` of
[Stacks, Tag 0B3T], read off from the exceptional computation of [Stacks, Tag 0B4L], followed by
the vanishing of `R^1b_*` and the computation of `b_*` of [Stacks, Tag 0AGS]. It is stated with
the derived direct image, which is the form the source uses.

*Quasi-compactness along the sequence.* The duality step asks the schemes to be quasi-compact and
quasi-separated, which is what makes [Stacks, Tag 0A9E] available. For a sequence of blowups in
closed points of a Noetherian `S` this is not an extra hypothesis: each stage is proper over the
previous one, hence Noetherian, hence quasi-compact and quasi-separated. The three lemmas at the
head of the file record this, and every field of `NormalizedTopFormData` that needs the instances
derives them from the sequence rather than assuming them, which is why the fields are quantified
over the stages of a sequence and not over arbitrary schemes over `S`.

*The model of the derived category* is the locally small one throughout; see the implementation
notes of `Stacks.BlowupTwistUnit.normalizedDualityHomEquiv`.

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
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Stacks.Duality
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.ResolutionOfSurfaces

universe u

namespace Stacks.BlowupTwistUnit

/-- The ideal sheaf cut out by a closed point, the centre of the blowups of a sequence of
blowups in closed points. -/
abbrev pointIdeal {W : Scheme.{u}} (w : W) (hw : IsClosed ({w} : Set W)) : W.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩

/-- `(Ω^n_{W/S₀})^{**}`, the reflexive hull of the degree-`n` relative differential forms of a
scheme over `S₀` presented through a factorization `W ⟶ S ⟶ S₀`. -/
abbrev hullForms {S₀ S W : Scheme.{u}} (p : S ⟶ S₀) (n : ℤ) (h : W ⟶ S) : W.Modules :=
  reflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) n)

section Chain

variable {S : Scheme.{u}} [IsNoetherian S] {T : Set S}

/-- Every stage of a sequence of blowups in closed points of a Noetherian scheme is
quasi-compact: it is Noetherian by `Stacks.ResolutionOfSurfaces.isNoetherian_of_pointBlowupChain`,
a blowup being proper. -/
theorem compactSpace_of_pointBlowupChain {W : Scheme.{u}} {h : W ⟶ S}
    (hc : PointBlowupChain S T W h) : CompactSpace W :=
  have := isNoetherian_of_pointBlowupChain hc
  inferInstance

/-- Every stage of a sequence of blowups in closed points of a Noetherian scheme is
quasi-separated. -/
theorem quasiSeparatedSpace_of_pointBlowupChain {W : Scheme.{u}} {h : W ⟶ S}
    (hc : PointBlowupChain S T W h) : QuasiSeparatedSpace W :=
  have := isNoetherian_of_pointBlowupChain hc
  inferInstance

/-- Every stage of a sequence of blowups in closed points of a Noetherian scheme is locally
Noetherian. -/
theorem isLocallyNoetherian_of_pointBlowupChain {W : Scheme.{u}} {h : W ⟶ S}
    (hc : PointBlowupChain S T W h) : IsLocallyNoetherian W :=
  have := isNoetherian_of_pointBlowupChain hc
  inferInstance

/-- **The reflexive hull of a coherent module on a stage of a sequence of blowups in closed
points is quasi-coherent.** The hull is the dual of the dual, the dual of a coherent module on a
locally Noetherian scheme is coherent, and a coherent module is quasi-coherent. -/
theorem isQuasicoherent_reflexiveHull_of_pointBlowupChain {S₀ : Scheme.{u}} {W : Scheme.{u}}
    {h : W ⟶ S} (hc : PointBlowupChain S T W h) (p : S ⟶ S₀) (n : ℤ)
    (hcoh : (Scheme.Hom.relativeDifferentialForms (h ≫ p) n).IsCoherent) :
    (hullForms p n h).IsQuasicoherent :=
  have := isLocallyNoetherian_of_pointBlowupChain hc
  have := hcoh
  _root_.isQuasicoherent_of_isCoherent _

end Chain


/-! ### The data the induction consumes -/

variable {S₀ S : Scheme.{u}} [IsNoetherian S] {p : S ⟶ S₀} {n : ℤ} {T : Set S}
  {ω : (W : Scheme.{u}) → (W ⟶ S) → W.Modules}

/-- The inputs of the construction of the map `(Ω^n_{X/S₀})^{**} ⟶ ω_X` along a sequence of
blowups in closed points of `T ⊆ S`. -/
structure NormalizedTopFormData {S₀ S : Scheme.{u}} [IsNoetherian S] (p : S ⟶ S₀) (n : ℤ)
    (T : Set S) (ω : (W : Scheme.{u}) → (W ⟶ S) → W.Modules) where
  /-- `ω_S = Ω^n_{S/S₀}`. -/
  baseIso : ω S (𝟙 S) ≅ Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n
  /-- `Ω^n_{S/S₀}` is reflexive. -/
  isReflexive_base : IsReflexive (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n)
  /-- Each dualizing module of the family is quasi-coherent. -/
  isQuasicoherent_dualizing : ∀ {W : Scheme.{u}} {h : W ⟶ S},
      PointBlowupChain S T W h → (ω W h).IsQuasicoherent
  /-- The top forms of each stage have quasi-coherent reflexive hull. -/
  isQuasicoherent_hull : ∀ {W : Scheme.{u}} {h : W ⟶ S},
      PointBlowupChain S T W h → (hullForms p n h).IsQuasicoherent
  /-- `ω_W` is the dualizing module normalized relative to `ω_S`. -/
  normalized : ∀ {W : Scheme.{u}} {h : W ⟶ S} (hc : PointBlowupChain S T W h),
      haveI := compactSpace_of_pointBlowupChain hc
      haveI := quasiSeparatedSpace_of_pointBlowupChain hc
      ((twistedInverseImage h (isQuasicoherent_homology_derivedPushforward_of_qcqs h)).obj
          (singleQuasiCoherent (ω S (𝟙 S))
            (isQuasicoherent_dualizing PointBlowupChain.refl) 0)).obj ≅
        (DerivedCategory.singleFunctor W.Modules 0).obj (ω W h)
  /-- The derived direct image of the top forms along one blowup. -/
  pushforwardIso : ∀ {W : Scheme.{u}} {h : W ⟶ S} (hc : PointBlowupChain S T W h)
      (w : W) (hw : IsClosed ({w} : Set W)) (hwT : h.base w ∈ T),
      haveI := compactSpace_of_pointBlowupChain hc
      haveI := quasiSeparatedSpace_of_pointBlowupChain hc
      haveI := compactSpace_of_pointBlowupChain (hc.step w hw hwT)
      haveI := quasiSeparatedSpace_of_pointBlowupChain (hc.step w hw hwT)
      (quasiCoherentDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
          (isQuasicoherent_homology_derivedPushforward_of_qcqs
            (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)))).obj
        (singleQuasiCoherent
          (hullForms p n (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h))
          (isQuasicoherent_hull (hc.step w hw hwT)) 0) ≅
      singleQuasiCoherent (hullForms p n h) (isQuasicoherent_hull hc) 0


/-! ### The base case and the inductive step -/

namespace NormalizedTopFormData

variable (D : NormalizedTopFormData p n T ω)

/-- **The identification of `(Ω^n_{S/S₀})^{**}` with `ω_S`**, the base case of the construction:
the canonical map to the reflexive hull is invertible and `ω_S` is `Ω^n_{S/S₀}`. -/
def baseHom : hullForms p n (𝟙 S) ⟶ ω S (𝟙 S) :=
  haveI : IsIso (toReflexiveHull (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n)).1 :=
    (isReflexive_iff_isIso_toReflexiveHull
      (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n)).mp D.isReflexive_base
  inv (toReflexiveHull (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n)).1 ≫ D.baseIso.inv

/-- The canonical map to the reflexive hull of the base forms is invertible. -/
private theorem isIso_toReflexiveHull_base (D : NormalizedTopFormData p n T ω) :
    IsIso (toReflexiveHull (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n)).1 :=
  (isReflexive_iff_isIso_toReflexiveHull
    (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n)).mp D.isReflexive_base

/-- **The base map is the given identification**: restricting it along the canonical map to the
reflexive hull recovers `ω_S = Ω^n_{S/S₀}`.

The normalized family `D` is named explicitly in the statement rather than taken from the
section, since the identity holds for the normalized data of a chain of blowups in closed points
and the same equation reads differently for a different family of dualizing modules. -/
theorem toReflexiveHull_comp_baseHom (D : NormalizedTopFormData p n T ω) :
    (toReflexiveHull (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n)).1 ≫ D.baseHom =
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
    (hullForms p n (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h) ⟶
        ω (AlgebraicGeometry.blowUp (pointIdeal w hw))
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) ≃
      ((quasiCoherentDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
          (isQuasicoherent_homology_derivedPushforward_of_qcqs
            (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)))).obj
        (singleQuasiCoherent
          (hullForms p n (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h))
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
    (hullForms p n (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h))
    (D.isQuasicoherent_hull (hc.step w hw hwT))


/-- **One step of the construction**: the map upstairs corresponding, under the duality bijection
of the blowup, to the direct-image identification of the top forms followed by the map
downstairs. -/
def step {W : Scheme.{u}} {h : W ⟶ S} (hc : PointBlowupChain S T W h)
    (w : W) (hw : IsClosed ({w} : Set W)) (hwT : h.base w ∈ T)
    (φ : hullForms p n h ⟶ ω W h) :
    hullForms p n (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h) ⟶
      ω (AlgebraicGeometry.blowUp (pointIdeal w hw))
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h) :=
  (D.stepDualityEquiv hc w hw hwT).symm
    ((D.pushforwardIso hc w hw hwT).hom ≫
      singleQcohHom (D.isQuasicoherent_hull hc) (D.isQuasicoherent_dualizing hc) φ)

/-- **The map produced by one step corresponds, under the duality bijection of the blowup, to the
map of the previous stage.** This is the sense in which the family of maps along the sequence is
coherent, and hence in which it extends the identification of `ω_S` with `(Ω^n_{S/S₀})^{**}`. -/
theorem stepDualityEquiv_step {W : Scheme.{u}} {h : W ⟶ S} (hc : PointBlowupChain S T W h)
    (w : W) (hw : IsClosed ({w} : Set W)) (hwT : h.base w ∈ T)
    (φ : hullForms p n h ⟶ ω W h) :
    D.stepDualityEquiv hc w hw hwT (D.step hc w hw hwT φ) =
      (D.pushforwardIso hc w hw hwT).hom ≫
        singleQcohHom (D.isQuasicoherent_hull hc) (D.isQuasicoherent_dualizing hc) φ :=
  (D.stepDualityEquiv hc w hw hwT).apply_symm_apply _

end NormalizedTopFormData

/-! ### Extending the identification at the generic point -/

/-- A morphism `φ : (Ω^n_{X/S₀})^{**} ⟶ ω_X`, for `X` a stage of a sequence of blowups in closed
points of `T ⊆ S`, *extends the identification of `ω_S` with `Ω^n_{S/S₀}`* when it descends along
the sequence to that identification. There is one clause per stage:

* at the bottom stage `X = S`, restricting `φ` along the canonical map
  `Ω^n_{S/S₀} ⟶ (Ω^n_{S/S₀})^{**}` gives `baseIso.inv`, the given identification itself;
* at a stage obtained by blowing up a closed point `w` of the previous one, the image of `φ`
  under the duality bijection of that blowup is the previous stage's map precomposed with the
  direct-image identification of the top forms.

Since a blowup in a closed point is an isomorphism away from that point, a map and the map it
corresponds to one stage down agree at the generic point; so the clauses say that `φ` agrees at
the generic point with `baseIso.inv`. Each clause determines the morphism it constrains — see
`Stacks.BlowupTwistUnit.NormalizedTopFormData.eq_baseHom_of_toReflexiveHull_comp` and
`Stacks.BlowupTwistUnit.NormalizedTopFormData.eq_step_of_stepDualityEquiv` — so this is a rigid
condition on `φ`: in particular the zero morphism satisfies it only if `baseIso.inv` is zero. -/
inductive NormalizedTopFormData.ExtendsIdentification (D : NormalizedTopFormData p n T ω) :
    ∀ {X : Scheme.{u}} {f : X ⟶ S}, PointBlowupChain S T X f →
      (hullForms p n f ⟶ ω X f) → Prop
  /-- At the bottom stage the map restricts to the given identification of `ω_S` with
  `Ω^n_{S/S₀}` along the canonical map to the reflexive hull. -/
  | base {φ : hullForms p n (𝟙 S) ⟶ ω S (𝟙 S)}
      (hφ : (toReflexiveHull (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n)).1 ≫ φ =
        D.baseIso.inv) :
      D.ExtendsIdentification PointBlowupChain.refl φ
  /-- At a blowup in a closed point the map corresponds, under the duality bijection of that
  blowup, to a map of the previous stage with the same property composed with the direct-image
  identification of the top forms. -/
  | step {W : Scheme.{u}} {h : W ⟶ S} {hc : PointBlowupChain S T W h}
      {φ : hullForms p n h ⟶ ω W h} (hφ : D.ExtendsIdentification hc φ)
      (w : W) (hw : IsClosed ({w} : Set W)) (hwT : h.base w ∈ T)
      {ψ : hullForms p n (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h) ⟶
          ω (AlgebraicGeometry.blowUp (pointIdeal w hw))
            (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)}
      (hψ : D.stepDualityEquiv hc w hw hwT ψ =
        (D.pushforwardIso hc w hw hwT).hom ≫
          singleQcohHom (D.isQuasicoherent_hull hc) (D.isQuasicoherent_dualizing hc) φ) :
      D.ExtendsIdentification (hc.step w hw hwT) ψ

namespace NormalizedTopFormData

variable (D : NormalizedTopFormData p n T ω)

/-- **The bottom clause determines the map it constrains**: `baseHom` is the only morphism
restricting to the given identification along the canonical map to the reflexive hull, that map
being invertible by `isReflexive_base`. -/
theorem eq_baseHom_of_toReflexiveHull_comp
    {φ : hullForms p n (𝟙 S) ⟶ ω S (𝟙 S)}
    (hφ : (toReflexiveHull (Scheme.Hom.relativeDifferentialForms (𝟙 S ≫ p) n)).1 ≫ φ =
      D.baseIso.inv) :
    φ = D.baseHom := by
  have := isIso_toReflexiveHull_base D
  rw [← D.toReflexiveHull_comp_baseHom] at hφ
  exact (cancel_epi _).mp hφ

/-- **The blowup clause determines the map it constrains**: `step` is the only morphism
corresponding to the previous stage's map under the duality bijection, that bijection being a
bijection. -/
theorem eq_step_of_stepDualityEquiv {W : Scheme.{u}} {h : W ⟶ S}
    (hc : PointBlowupChain S T W h) (w : W) (hw : IsClosed ({w} : Set W)) (hwT : h.base w ∈ T)
    (φ : hullForms p n h ⟶ ω W h)
    {ψ : hullForms p n (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h) ⟶
        ω (AlgebraicGeometry.blowUp (pointIdeal w hw))
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)}
    (hψ : D.stepDualityEquiv hc w hw hwT ψ =
      (D.pushforwardIso hc w hw hwT).hom ≫
        singleQcohHom (D.isQuasicoherent_hull hc) (D.isQuasicoherent_dualizing hc) φ) :
    ψ = D.step hc w hw hwT φ := by
  have hsymm := (D.stepDualityEquiv hc w hw hwT).symm_apply_apply ψ
  rw [hψ] at hsymm
  exact hsymm.symm

end NormalizedTopFormData

/-! ### The existence of the map -/

/-- **Stacks Project, Tag 0B4T.** Let `A` be a regular local ring of dimension two and `A₀ ⊆ A` a
subring with `Ω_{A/A₀}` free of rank `r`, so that `ω_A = Ω^r_{A/A₀}` is invertible and, `A` being
Gorenstein, dualizing. If `X → Spec A` is the result of a sequence of blowups in closed points
then there is a map

`φ_X : (Ω^r_{X/Spec A₀})^{**} ⟶ ω_X`

extending the given identification in the generic point, where `ω_X` is the dualizing module of
`X` normalized relative to `ω_A`.

The normalization is the field `normalized`, and it is what the word `ω_X` means: a dualizing
module is pinned only up to shift and an invertible twist, and what fixes it for a scheme over
`Spec A` is the isomorphism with the twisted inverse image of `ω_A`. From the normalizations the
duality bijection `Hom_{X'}(ℱ, ω_{X'}) ≃ Hom(Rb_*ℱ, ω_X)` of one blowup is *derived*, by
`Stacks.BlowupTwistUnit.normalizedDualityHomEquiv`: the composition formula for right adjoints
turns the two normalizations into `ω_{X'} = b^×(ω_X)`, and the adjunction `Rb_* ⊣ b^×` does the
rest.

The one input still assumed is `pushforwardIso`, the computation
`Rb_*((Ω^r_{X'})^{**}) = (Ω^r_X)^{**}` of one blowup.

The extension clause is `Stacks.BlowupTwistUnit.NormalizedTopFormData.ExtendsIdentification`:
`φ_X` descends along the sequence to the map on `Spec A` restricting to `baseIso.inv` along
`Ω^r_{A/A₀} ⟶ (Ω^r_{A/A₀})^{**}`. By
`Stacks.BlowupTwistUnit.NormalizedTopFormData.eq_baseHom_of_toReflexiveHull_comp` and
`Stacks.BlowupTwistUnit.NormalizedTopFormData.eq_step_of_stepDualityEquiv` that pins `φ_X`
uniquely at every stage, so the conclusion is not inhabited by an arbitrary morphism.

The proof is the induction of the source: the bottom stage is `baseHom`, anchored by
`toReflexiveHull_comp_baseHom`, and one blowup is `step`, whose correspondence to the previous
stage is `stepDualityEquiv_step`. -/
theorem exists_extendsIdentification_hullForms_normalizedDualizing
    (D : NormalizedTopFormData p n T ω)
    {X : Scheme.{u}} {f : X ⟶ S} (hf : PointBlowupChain S T X f) :
    ∃ φ : hullForms p n f ⟶ ω X f, D.ExtendsIdentification hf φ := by
  induction hf with
  | refl => exact ⟨D.baseHom, .base D.toReflexiveHull_comp_baseHom⟩
  | @step W h hh w hw hwT ih =>
    obtain ⟨φ, hφ⟩ := ih
    exact ⟨D.step hh w hw hwT φ, hφ.step w hw hwT (D.stepDualityEquiv_step hh w hw hwT φ)⟩

end Stacks.BlowupTwistUnit

end
