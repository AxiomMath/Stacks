module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartAlphaInstance
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartCocycle
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Basic

/-!
# The two trivialising families of Stacks Tag 01N8 match

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `X = Proj(A)`, `d > 0`, and let `U_d ⊆ X` be the open of
Equation 27.12.0.1. Let `Y` be a scheme, `L` an invertible `𝒪_Y`-module, `ψ` a graded map
`A^{(d)} → Γ_*(Y, L)` in the degreewise spelling
`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections`, and `φ : Y ⟶ U_d` the morphism
glued from the charts of `ψ` (`Stacks.AlgebraicGeometry.ProjChartCocycle.glued`). The existence
half of [Stacks, Tag 01N8] also produces an isomorphism `α : φ⁎𝒪_{U_d}(d) ≅ L`, and the machinery
that glues it from the per-chart isomorphisms
(`Stacks.AlgebraicGeometry.ProjChartAlphaInstance.alpha`) has exactly one hypothesis left open:
that the two families of trivialising sections **match**, i.e. that

  `m f / m g` and `ψ(f) / ψ(g)` are one and the same regular function on `W g`,

where `m f` is the pullback along `φ` of the degree-`d` section of `f`. This file proves it. It is
the source's own sentence *"the `α_f` agree because the regular functions `s/s'` and
`ψ_{(f')}(f/f')` agree"*, and with it every hypothesis of `alpha` is discharged.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartCocycleMatch.resTop_degreeSection_eq_smul`: **on `D₊(q)` the
  degree-`d` section of `p` is the fraction `p/q` times the degree-`d` section of `q`**, for two
  homogeneous elements of one common degree `d`. This is
  `Stacks.TwistPullbackRatio.degreeSection_res_eq` with the degree freed from `1`; the proof is
  the same pointwise computation, which never used `d = 1`.
* `Stacks.AlgebraicGeometry.ProjChartCocycleMatch.resTop_pullbackDegreeSection_eq_smul`: **the
  same identity after pullback along a morphism through `U_d`**, over any open mapping into
  `D₊(q)`. The scalar is `φ^♯(p/q)`.
* `Stacks.AlgebraicGeometry.ProjChartCocycleMatch.lift_mk_one_eq_ratio`: the chart's ring map
  sends the fraction `f/g` to the ratio `ψ(f)/ψ(g)`.
* `Stacks.AlgebraicGeometry.ProjChartCocycleMatch.matching_pullbackDegreeSection`: **the matching
  condition `hmatch`**, the one hypothesis the `α` construction leaves open.
* `Stacks.AlgebraicGeometry.ProjChartCocycleMatch.alphaGlued` and
  `…alphaGlued_hom_app_top`: the isomorphism `α` for the glued `φ`, with every hypothesis
  discharged, and its normalisation `α(m f) = ψ(f)`.

## Implementation notes

**The common scalar is `φ^♯(f/g)`, named on the `ψ` side.** `Matching` asks for one scalar
serving both clauses. The clause about `ψ` has a canonical witness — the ratio
`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.ratio`, which is *defined* as
`ψ(f)/ψ(g)` — so that is the scalar supplied, and the work is all in the clause about the pulled
back degree sections. There the scalar arrives as `φ^♯` of the degree-zero fraction `f/g` of
`A_{(g)}`, and `Stacks.AlgebraicGeometry.ProjChartGluing.appLE_awayToSection` identifies `φ^♯` on
such a fraction with the chart's ring map `lift` on it, which by
`Stacks.MorphismToProj.HomogeneousRatios.lift_mk` is that same ratio. So the two clauses hold for
one scalar because `φ` *is* the chart of `g` over `W g`, which is `hglue`.

**`Matching` is proved over `W j`, not over the intersection.** Nothing here weakens it: the open
mapped into `D₊(f_j)` is `W j` itself — `W j ≤ Y_{ψ(f_j)}` and the preimage of `D₊(f_j)` under the
glued morphism *is* `Y_{ψ(f_j)}` by clause (a)
(`Stacks.AlgebraicGeometry.ProjChartGluing.preimage_basicOpen_eq_nonvanishingOpen`), so the
fraction `f_i/f_j` pulls back to a regular function on all of `W j` whatever `i` is. The index `i`
enters only as the numerator.

**The degree is not raised.** The fraction used is `HomogeneousLocalization.Away.mk 𝒜 hg 1 f _`,
i.e. `f/g` with numerator of Veronese degree `1`, not `f^d/g^d`. That is why
`resTop_degreeSection_eq_smul` is needed at the general degree `d` rather than at degree `1`: the
*elements* have degree `d`, while the *fraction* has Veronese degree `1`.

**Spelling of the pullback of a section.** `Stacks.AlgebraicGeometry.ProjChartAlphaInstance`
writes `m f` with `AlgebraicGeometry.pullbackSectionHom`, whose semilinearity
(`AlgebraicGeometry.pullbackSectionHom_smul`) and compatibility with shrinking the open on `Proj`
(`AlgebraicGeometry.pullbackSectionHom_map`) are available. The one missing structural lemma,
compatibility with shrinking the open on `Y`, is `resTop_pullbackSectionHom` below; it is the
same two steps as the end of `pullbackSectionHom_map`. No new pullback API is introduced, and the
parallel `pbSec`/`pullbackSectionOn` spellings of `StacksFrontier/AlgebraicGeometry/
TwistPullbackRatio/` are not used.

**No `@[stacks 01N8]` attribute is attached here, because it is attached elsewhere.** The tag is
the conjunction of existence and uniqueness; neither is asserted here on its own, so the
attribute belongs on the combined statement, and that statement exists:
`Stacks.AlgebraicGeometry.MorphismToProjUniversal.existsUnique_pair` carries `@[stacks 01N8]` and
is the one registration of the tag in this repository. The glued trivialization `alphaGlued`
below is one of its inputs.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry HomogeneousLocalization
open AlgebraicGeometry.Proj (degreeOpen)
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.ProjChartAlphaInstance
open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.MorphismToProj (HomogeneousRatios)
open Stacks.TensorPowers (natTensorPow)
open Stacks.TensorPowerTrivialize (resTop)
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartCocycleMatch

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### Pulling a section back commutes with shrinking the open downstairs -/

/-- **The pullback of a section is compatible with restriction on the source.** The companion of
`AlgebraicGeometry.pullbackSectionHom_map`, which shrinks the open on the target; the proof is the
same, two restriction maps of the pullback presheaf composing into one. -/
theorem resTop_pullbackSectionHom {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (U : X.Opens) {V V' : Y.Opens} (h : V ≤ f ⁻¹ᵁ U) (h' : V' ≤ f ⁻¹ᵁ U) (hV : V' ≤ V)
    (a : Γ(M, U)) :
    ((Scheme.Modules.pullback f).obj M).presheaf.map (homOfLE hV).op
        (pullbackSectionHom f M U V h a)
      = pullbackSectionHom f M U V' h' a :=
  (PresheafOfModules.map_comp_apply (((Scheme.Modules.pullback f).obj M).val)
    (homOfLE h).op (homOfLE hV).op _).symm.trans
    (PresheafOfModules.congr_map_apply _ (Subsingleton.elim _ _) _)

/-! ### The ratio of two degree-`d` sections on a standard open -/

section Proj

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {d : ℕ} {Y : Scheme.{u}}

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance_reducible] ProjectiveSpectrum.top

/-- `𝒪(d)` on `Proj 𝒜`, read as a module on the scheme. The twisting sheaf has to be read at this
spelling for the scalar action on its sections to be found; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/TwistPullbackRatio/Basic.lean`. -/
abbrev twistDeg : (AlgebraicGeometry.Proj 𝒜).Modules := twistingSheaf 𝒜 (d : ℤ)

/-- **On `D₊(q)` the degree-`d` section of `p` is the fraction `p/q` times the degree-`d` section
of `q`**, for two homogeneous elements of one common degree `d`.

This is `Stacks.TwistPullbackRatio.degreeSection_res_eq` with the degree freed from `1`: the
pointwise computation is the same, because the local value of the degree-`k` section of an element
is the fraction `element / 1` in every degree
(`Stacks.AlgebraicGeometry.ProjTwistSections.degreeSection_apply`), the local value of
`AlgebraicGeometry.Proj.awayToSection` is the fraction itself, and what is left is
`p/1 = (p/q)·(q/1)` in the local ring. -/
theorem resTop_degreeSection_eq_smul {p q : A} (hp : p ∈ 𝒜 d) (hq : q ∈ 𝒜 d) :
    resTop (twistDeg 𝒜 (d := d)) (degreeSection 𝒜 d ⟨p, hp⟩)
          (AlgebraicGeometry.Proj.basicOpen 𝒜 q)
      = (AlgebraicGeometry.Proj.awayToSection 𝒜 q).hom
            (Away.mk 𝒜 hq 1 p (by simpa using hp)) •
        resTop (twistDeg 𝒜 (d := d)) (degreeSection 𝒜 d ⟨q, hq⟩)
          (AlgebraicGeometry.Proj.basicOpen 𝒜 q) := by
  refine Subtype.ext (funext fun x => ?_)
  have hdeg : ∀ (r : A) (hr : r ∈ 𝒜 d),
      (resTop (twistDeg 𝒜 (d := d)) (degreeSection 𝒜 d ⟨r, hr⟩)
        (AlgebraicGeometry.Proj.basicOpen 𝒜 q)).1 x = Localization.mk r 1 :=
    fun r hr => degreeSection_apply 𝒜 d ⟨r, hr⟩ _
  have hR : ((AlgebraicGeometry.Proj.awayToSection 𝒜 q).hom
          (Away.mk 𝒜 hq 1 p (by simpa using hp)) •
        resTop (twistDeg 𝒜 (d := d)) (degreeSection 𝒜 d ⟨q, hq⟩)
          (AlgebraicGeometry.Proj.basicOpen 𝒜 q)).1 x =
      HomogeneousLocalization.val
          (((AlgebraicGeometry.Proj.awayToSection 𝒜 q).hom
            (Away.mk 𝒜 hq 1 p (by simpa using hp))).1 x) *
        (resTop (twistDeg 𝒜 (d := d)) (degreeSection 𝒜 d ⟨q, hq⟩)
          (AlgebraicGeometry.Proj.basicOpen 𝒜 q)).1 x := rfl
  have hval : HomogeneousLocalization.val
      (((AlgebraicGeometry.Proj.awayToSection 𝒜 q).hom
        (Away.mk 𝒜 hq 1 p (by simpa using hp))).1 x) =
      Localization.mk p ⟨q ^ 1, _⟩ := rfl
  rw [hdeg p hp, hR, hval, hdeg q hq, Localization.mk_mul]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp; ring))

/-! ### The same identity, pulled back along a morphism through `U_d` -/

/-- The restriction to an open of `Y` of a pulled-back degree-`d` section is the pullback of that
section read over the open. -/
theorem resTop_pullbackDegreeSection (φ : Y ⟶ (degreeOpen 𝒜 d).toScheme) (e : 𝒜 d)
    (V : Y.Opens) :
    resTop (pullbackTwist 𝒜 φ (d : ℤ)) (pullbackDegreeSection 𝒜 φ e) V
      = pullbackSectionHom (toProj 𝒜 φ) (twistingSheaf 𝒜 (d : ℤ)) ⊤ V (by simp)
          (degreeSection 𝒜 d e) :=
  resTop_pullbackSectionHom (toProj 𝒜 φ) (twistingSheaf 𝒜 (d : ℤ)) ⊤ (by simp) (by simp)
    le_top (degreeSection 𝒜 d e)

/-- **The ratio of two pulled-back degree-`d` sections.** Over an open mapping into `D₊(f_j)` the
pullback of the degree-`d` section of `f_i` is `φ^♯(f_i/f_j)` times the pullback of the degree-`d`
section of `f_j`.

This is `resTop_degreeSection_eq_smul` pushed along `φ`: pulling a section back is semilinear
(`AlgebraicGeometry.pullbackSectionHom_smul`) and compatible with restricting the open upstairs
(`AlgebraicGeometry.pullbackSectionHom_map`) and downstairs
(`resTop_pullbackSectionHom`). -/
theorem resTop_pullbackDegreeSection_eq_smul (φ : Y ⟶ (degreeOpen 𝒜 d).toScheme) (i j : 𝒜 d)
    {V : Y.Opens} (hV : V ≤ toProj 𝒜 φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (j : A)) :
    resTop (pullbackTwist 𝒜 φ (d : ℤ)) (pullbackDegreeSection 𝒜 φ i) V
      = (toProj 𝒜 φ).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (j : A)) V hV
          ((AlgebraicGeometry.Proj.awayToSection 𝒜 (j : A)).hom
            (Away.mk 𝒜 j.2 1 (i : A) (by simp)))
        • resTop (pullbackTwist 𝒜 φ (d : ℤ)) (pullbackDegreeSection 𝒜 φ j) V := by
  have key : ∀ e : 𝒜 d, resTop (pullbackTwist 𝒜 φ (d : ℤ)) (pullbackDegreeSection 𝒜 φ e) V
      = pullbackSectionHom (toProj 𝒜 φ) (twistingSheaf 𝒜 (d : ℤ))
          (AlgebraicGeometry.Proj.basicOpen 𝒜 (j : A)) V hV
          (resTop (twistDeg 𝒜 (d := d)) (degreeSection 𝒜 d e)
            (AlgebraicGeometry.Proj.basicOpen 𝒜 (j : A))) := fun e => by
    rw [resTop_pullbackDegreeSection]
    exact (pullbackSectionHom_map (toProj 𝒜 φ) (twistingSheaf 𝒜 (d : ℤ)) ⊤
      (AlgebraicGeometry.Proj.basicOpen 𝒜 (j : A)) le_top V hV (by simp)
      (degreeSection 𝒜 d e)).symm
  rw [key i, key j, resTop_degreeSection_eq_smul 𝒜 i.2 j.2]
  exact pullbackSectionHom_smul _ _ _ _ _ _ _

end Proj

/-! ### The matching condition -/

section Match

open Stacks.AlgebraicGeometry.ProjChartAlpha
open Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {d : ℕ} {Y : Scheme.{u}} {L : Y.Modules}
  [Stacks.Ample.IsInvertibleModule Y L]

/-- **The chart's ring map on the fraction `f/g`** is the ratio `ψ(f)/ψ(g)`. One application of
`Stacks.MorphismToProj.HomogeneousRatios.lift_mk` together with
`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.toFun_eq_pow`, which identifies the
value of `ψ` on `f` with the first power of the trivialising section. -/
theorem lift_mk_one_eq_ratio (ψ : VeroneseSections 𝒜 d L) (hd : 0 < d) {f g : A} (hf : f ∈ 𝒜 d)
    (hg : g ∈ 𝒜 d) {V : Y.Opens}
    (hV : V ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow hg 1)) :
    (ψ.homogeneousRatios hg hV).lift hd (Away.mk 𝒜 hg 1 f (by simpa using hf))
      = ψ.ratio hg hV 1 (ψ.pow hf 1) := by
  have hfd : f ∈ 𝒜 (1 * d) := by simpa using hf
  rw [(ψ.homogeneousRatios hg hV).lift_mk hd 1 f (by simpa using hf) ⟨f, hfd⟩ rfl]
  show ψ.ratio hg hV 1 (ψ.toFun 1 ⟨f, hfd⟩) = _
  rw [ψ.toFun_eq_pow hf 1 ⟨f, hfd⟩ (pow_one f).symm]

variable (ψ : VeroneseSections 𝒜 d L) (hd : 0 < d)
  {φ : Y ⟶ (degreeOpen 𝒜 d).toScheme} {W : 𝒜 d → Y.Opens}
  (hWle : ∀ g : 𝒜 d, W g ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow g.2 1))
  (hcover : ⨆ g : 𝒜 d, W g = ⊤)
  (hglue : ∀ g : 𝒜 d, (W g).ι ≫ φ = ψ.toDegreeOpen g.2 (hWle g) hd)

include hglue

/-- **Over `W g` the morphism into `Proj 𝒜` is the chart of `g`.** This is `hglue` read into
`Proj 𝒜`, which is what
`Stacks.AlgebraicGeometry.ProjChartGluing.appLE_awayToSection` consumes. -/
theorem ι_comp_toProj (g : 𝒜 d) :
    (W g).ι ≫ toProj 𝒜 φ = (ψ.homogeneousRatios g.2 (hWle g)).chartToProj hd := by
  rw [show (W g).ι ≫ toProj 𝒜 φ = ((W g).ι ≫ φ) ≫ (degreeOpen 𝒜 d).ι from
    (Category.assoc _ _ _).symm, hglue g]
  exact (ψ.homogeneousRatios g.2 (hWle g)).toProj_toDegreeOpen hd

include hcover

/-- `W g` maps into the standard open `D₊(g)`, by clause (a) of [Stacks, Tag 01N8]. -/
theorem le_preimage_basicOpen (g : 𝒜 d) :
    W g ≤ toProj 𝒜 φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (g : A) :=
  (hWle g).trans
    (ProjChartGluing.preimage_basicOpen_eq_nonvanishingOpen 𝒜 hd ψ hWle hcover hglue g).ge

/-- **`φ^♯` of the fraction `f_i/f_j`, over `W j`, is the ratio `ψ(f_i)/ψ(f_j)`.** Over `W j` the
morphism is the chart of `f_j` (`ι_comp_toProj`), so its effect on the section
`AlgebraicGeometry.Proj.awayToSection` of a fraction is the chart's ring map on that fraction
(`Stacks.AlgebraicGeometry.ProjChartGluing.appLE_awayToSection`), which is the ratio
(`lift_mk_one_eq_ratio`). -/
theorem appLE_awayToSection_eq_ratio (i j : 𝒜 d) :
    (toProj 𝒜 φ).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 (j : A)) (W j)
        (le_preimage_basicOpen 𝒜 ψ hd hWle hcover hglue j)
        ((AlgebraicGeometry.Proj.awayToSection 𝒜 (j : A)).hom
          (Away.mk 𝒜 j.2 1 (i : A) (by simp)))
      = ψ.ratio j.2 (hWle j) 1 (ψ.pow i.2 1) := by
  rw [ProjChartGluing.appLE_awayToSection (ψ.homogeneousRatios j.2 (hWle j)) hd
    (ι_comp_toProj 𝒜 ψ hd hWle hglue j) (le_preimage_basicOpen 𝒜 ψ hd hWle hcover hglue j)]
  exact lift_mk_one_eq_ratio 𝒜 ψ hd i.2 j.2 (hWle j)

/-- **The matching condition `hmatch` of [Stacks, Tag 01N8].** The pulled-back degree-`d`
sections `m f` and the sections `ψ(f)` have the same transition functions on the covering `W`: on
`W j` the common scalar is the ratio `ψ(f_i)/ψ(f_j)`.

This is the source's sentence *"the `α_f` agree because the regular functions `s/s'` and
`ψ_{(f')}(f/f')` agree"*. Two clauses, one scalar. The clause about `ψ` is the defining identity
of the ratio
(`Stacks.AlgebraicGeometry.ProjChartFromRatios.VeroneseSections.resTop_eq_ratio_smul`). The clause
about the `m f` is `resTop_pullbackDegreeSection_eq_smul`, whose scalar is `φ^♯(f_i/f_j)`, and
`appLE_awayToSection_eq_ratio` identifies that with the same ratio — because over `W j` the
morphism `φ` *is* the chart of `f_j`.

The condition is proved over the whole of `W j`, not merely over `W i ⊓ W j`; see the
implementation notes of `ProjChartAlphaGluing.lean` for why the stronger form is needed, and the
notes above for why it is available. -/
theorem matching_pullbackDegreeSection :
    Matching (pullbackDegreeSection 𝒜 φ) (fun g : 𝒜 d => ψ.pow g.2 1) W := by
  intro i j
  refine ⟨ψ.ratio j.2 (hWle j) 1 (ψ.pow i.2 1), ?_, ?_⟩
  · rw [resTop_pullbackDegreeSection_eq_smul 𝒜 φ i j
      (le_preimage_basicOpen 𝒜 ψ hd hWle hcover hglue j),
      appLE_awayToSection_eq_ratio 𝒜 ψ hd hWle hcover hglue i j]
  · exact ψ.resTop_eq_ratio_smul j.2 (hWle j) 1 (ψ.pow i.2 1)

end Match

/-! ### The isomorphism `α` for the glued morphism -/

section Alpha

open Stacks.AlgebraicGeometry.ProjChartAlpha
open Stacks.AlgebraicGeometry.ProjChartCocycle

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {d : ℕ} {Y : Scheme.{u}} {L : Y.Modules}
  [Stacks.Ample.IsInvertibleModule Y L]

/-- **The isomorphism `α : φ⁎𝒪_{U_d}(d) ≅ L^{⊗ 1}` for the glued morphism `φ`**, with every
hypothesis discharged: `Stacks.AlgebraicGeometry.ProjChartAlphaInstance.alpha` applied to
`Stacks.AlgebraicGeometry.ProjChartCocycle.glued`, whose `hglue` is `ι_glued` and whose `hmatch`
is `matching_pullbackDegreeSection`. -/
def alphaGlued (ψ : VeroneseSections 𝒜 d L) (hd : 0 < d) {W : 𝒜 d → Y.Opens}
    (hWle : ∀ g : 𝒜 d, W g ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow g.2 1))
    (hcover : ⨆ g : 𝒜 d, W g = ⊤) :
    pullbackTwist 𝒜 (glued 𝒜 ψ hd hWle hcover) (d : ℤ) ≅ natTensorPow L 1 :=
  alpha 𝒜 hd ψ hWle hcover (ι_glued 𝒜 ψ hd hWle hcover)
    (matching_pullbackDegreeSection 𝒜 ψ hd hWle hcover (ι_glued 𝒜 ψ hd hWle hcover))

/-- **The normalisation of `α`** for the glued morphism: it carries the pullback of the degree-`d`
section of `f` to `ψ(f)`, for every `f ∈ 𝒜 d`. -/
theorem alphaGlued_hom_app_top (ψ : VeroneseSections 𝒜 d L) (hd : 0 < d) {W : 𝒜 d → Y.Opens}
    (hWle : ∀ g : 𝒜 d, W g ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow g.2 1))
    (hcover : ⨆ g : 𝒜 d, W g = ⊤) (f : 𝒜 d) :
    (alphaGlued 𝒜 ψ hd hWle hcover).hom.app ⊤
        (pullbackDegreeSection 𝒜 (glued 𝒜 ψ hd hWle hcover) f) = ψ.pow f.2 1 :=
  alpha_hom_app_top 𝒜 hd ψ hWle hcover (ι_glued 𝒜 ψ hd hWle hcover) _ f

end Alpha

end Stacks.AlgebraicGeometry.ProjChartCocycleMatch

end
