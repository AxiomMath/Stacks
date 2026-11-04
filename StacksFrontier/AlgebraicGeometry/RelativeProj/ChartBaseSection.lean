module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.Charts.Descent
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.StructureMorphism
public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence2.AffineOpenHom

/-!
# Pulling a section of the base back to a chart of a relative `Proj`

Let `s` be a relative-`Proj` situation — a scheme `s.base` with a quasi-coherent nonnegatively
graded algebra on it — and let `U` be an affine open of the base. The chart over `U` is
`Proj (s.sectionRingGrading U)`, and `Stacks.RelativeProj.Situation.chartToBase` is its structure
morphism to the base, which lands in `U`. This file computes what a section `r ∈ Γ(s.base, U)`
becomes when pulled back along that morphism: it is the global function on the chart whose value
at every homogeneous prime is the *constant fraction* of the degree-zero element
`Stacks.RelativeProj.Situation.sectionRingBaseMap U r`.

This is the general-base counterpart of `Stacks.Blowup.baseSection_val`, which says the same for
the `Proj` of an ordinary Rees algebra over a ring. It is what lets a trivialization of a sheaf of
modules on the chart — phrased in terms of degree-one elements of the graded section ring — be
multiplied by a section pulled back from the base, which is phrased in terms of the structure
sheaf of the relative `Proj`: the two descriptions of the pulled-back section have to be
identified first.

## Main definitions

* `Stacks.RelativeProj.Situation.chartBaseSection`: the pullback of a section of the base to the
  chart over an affine open, as a global function on the chart, and
  `Stacks.RelativeProj.Situation.chartBaseSectionRes` its restriction to an open of the chart.

## Main results

* `Stacks.RelativeProj.Situation.chartBaseSection_eq`: the pullback factors through
  `AlgebraicGeometry.Proj.toSpecZero`, at the degree-zero element
  `Stacks.RelativeProj.Situation.sectionRingBaseMap U r`.
* `Stacks.RelativeProj.Situation.chartBaseSection_val`: **the pullback of `r` has the constant
  fraction `r / 1` as its value at every point of the chart.**
* `Stacks.RelativeProj.Situation.chartBaseSectionRes_val_eq`: the same for the restriction, with
  the two steps composed — inside a product neither half can be used by `rw`, because the goal is
  then not type-correct at `implicit` transparency.
* `Stacks.RelativeProj.Situation.app_relativeProjChart_appLE`: **the chart reads the pullback of
  `r` along the structure morphism of the relative `Proj` as that constant fraction.** Restricting
  a section of the base to an open `V` of the relative `Proj` lying over `U` and then pulling it
  back along the chart over `U` gives the restriction of `chartBaseSection`.

## Implementation notes

`Stacks.RelativeProj.Situation.appLE_congr` is what makes the last statement provable. Both sides
are values of `AlgebraicGeometry.Scheme.Hom.appLE`, whose inequality argument has a type
mentioning the morphism, so the morphism cannot be rewritten underneath it — and the equation that
has to be used, the commuting square
`Stacks.RelativeProj.Situation.relativeProjChart_isPullback`, is exactly an equation of morphisms.
Stating the congruence with the two morphisms as *variables* makes `subst` available, after which
the inequality arguments agree by proof irrelevance.

Every step is taken on elements rather than on morphisms. Reassociating the composite that
`Stacks.RelativeProj.Situation.projInclusionToOpen` unfolds to runs `rw` into a 200,000-heartbeat
`isDefEq` wall, and `simp` with the naturality square of `AlgebraicGeometry.Scheme.ΓSpecIso`
available rewrites `U.topIso.inv ≫ U.topIso.hom` through the naturality before it can cancel it.
Applying each morphism equation to the section with `DFunLike.congr_fun` avoids both.

## References

* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.RelativeProj.Situation

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime

variable (s : Situation.{u})

/-- The whole chart over `U` lies over `U`, in the form the inequality argument of
`AlgebraicGeometry.Scheme.Hom.appLE` asks for. -/
theorem top_le_preimage_chartToBase (U : s.base.Opens) (hU : IsAffineOpen U) :
    (⊤ : (AlgebraicGeometry.Proj (s.sectionRingGrading U)).Opens) ≤
      s.chartToBase U hU ⁻¹ᵁ U := fun x _ => chartToBase_mem s U hU x

/-- **The pullback of a section of the base to the chart over an affine open**: a global function
on `Proj (s.sectionRingGrading U)`. -/
def chartBaseSection (U : s.base.Opens) (hU : IsAffineOpen U) (r : Γ(s.base, U)) :
    Γ(AlgebraicGeometry.Proj (s.sectionRingGrading U), ⊤) :=
  ((s.chartToBase U hU).appLE U ⊤ (s.top_le_preimage_chartToBase U hU)).hom r

/-- The pullback of `r` to the chart is the pullback of the degree-zero element
`Stacks.RelativeProj.Situation.sectionRingBaseMap U r` along
`AlgebraicGeometry.Proj.toSpecZero`. -/
theorem chartBaseSection_eq (U : s.base.Opens) (hU : IsAffineOpen U) (r : Γ(s.base, U)) :
    s.chartBaseSection U hU r =
      ((Proj.toSpecZero (s.sectionRingGrading U)).appTop).hom
        ((Scheme.ΓSpecIso (CommRingCat.of (s.sectionRingGrading U 0))).inv.hom
          ⟨s.sectionRingBaseMap U r, sectionRingBaseMap_mem_zero s U r⟩) := by
  have hi : (U.ι).appLE U ⊤ U.ι_preimage_self.ge = U.topIso.inv := by
    rw [Scheme.Opens.ι_appLE]; rfl
  have hp := Scheme.Hom.appLE_comp_appLE (s.projInclusionToOpen U hU) U.ι U ⊤ ⊤
    U.ι_preimage_self.ge (by simp)
  rw [hi] at hp
  have ht : (s.projInclusionToOpen U hU).appLE (⊤ : U.toScheme.Opens) ⊤ (by simp) =
      (s.projInclusionToOpen U hU).appTop :=
    Stacks.AffineAlgebraEquivalence.appLE_top_top _ _
  rw [ht] at hp
  have key : U.topIso.inv ≫ (s.projInclusionToOpen U hU).appTop =
      (Scheme.ΓSpecIso Γ(s.base, U)).inv ≫
        (Spec.map (sectionRingZeroMap s U)).appTop ≫
          (Proj.toSpecZero (s.sectionRingGrading U)).appTop := by
    rw [projInclusionToOpen, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
      IsAffineOpen.isoSpec_inv_appTop]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hp' := ConcreteCategory.congr_hom hp r
  have hkey := ConcreteCategory.congr_hom key r
  have hnat := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (sectionRingZeroMap s U)) r
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hp' hkey hnat
  refine Eq.trans (show s.chartBaseSection U hU r =
    ((s.projInclusionToOpen U hU).appTop).hom (U.topIso.inv.hom r) from hp'.symm) ?_
  refine hkey.trans ?_
  refine Eq.trans (congrArg (((Proj.toSpecZero (s.sectionRingGrading U)).appTop).hom)
    hnat.symm) ?_
  refine congrArg
    (fun z => ((Proj.toSpecZero (s.sectionRingGrading U)).appTop).hom
      ((Scheme.ΓSpecIso (CommRingCat.of (s.sectionRingGrading U 0))).inv.hom z)) ?_
  exact GradedRing.projZeroRingHom'_apply_coe (s.sectionRingGrading U)
    ⟨s.sectionRingBaseMap U r, sectionRingBaseMap_mem_zero s U r⟩

/-- **The pullback of `r` has the constant fraction `r / 1` as its value at every point of the
chart**, the numerator being the degree-zero element
`Stacks.RelativeProj.Situation.sectionRingBaseMap U r`. -/
theorem chartBaseSection_val (U : s.base.Opens) (hU : IsAffineOpen U) (r : Γ(s.base, U))
    (x : ProjectiveSpectrum.top (s.sectionRingGrading U)) :
    HomogeneousLocalization.val ((s.chartBaseSection U hU r).1 ⟨x, trivial⟩) =
      algebraMap (s.sectionRing U) (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)
        (s.sectionRingBaseMap U r) := by
  rw [chartBaseSection_eq]
  exact Stacks.AlgebraicGeometry.ProjEulerSequence.toSpecZero_appTop_val
    (s.sectionRingGrading U) ⟨s.sectionRingBaseMap U r, sectionRingBaseMap_mem_zero s U r⟩ x

/-- The pullback of a section of the base, restricted to an open of the chart. -/
def chartBaseSectionRes (U : s.base.Opens) (hU : IsAffineOpen U) (r : Γ(s.base, U))
    (W : (AlgebraicGeometry.Proj (s.sectionRingGrading U)).Opens) :
    Γ(AlgebraicGeometry.Proj (s.sectionRingGrading U), W) :=
  (((AlgebraicGeometry.Proj (s.sectionRingGrading U)).presheaf.map
    (homOfLE (le_top (a := W))).op)).hom (s.chartBaseSection U hU r)

/-- The restricted pullback has the same value at a point of the open as the pullback itself. -/
theorem chartBaseSectionRes_val (U : s.base.Opens) (hU : IsAffineOpen U) (r : Γ(s.base, U))
    {W : (AlgebraicGeometry.Proj (s.sectionRingGrading U)).Opens} (x : W) :
    (s.chartBaseSectionRes U hU r W).1 x = (s.chartBaseSection U hU r).1 ⟨x.1, trivial⟩ := rfl

/-- **The restricted pullback of `r` is the constant fraction of
`Stacks.RelativeProj.Situation.sectionRingBaseMap U r` at every point.** This is the form the
comparison of two charts consumes: both `chartBaseSectionRes_val` and `chartBaseSection_val`
have a goal that is not type-correct at `implicit` transparency once they are placed inside a
product, so `rw` cannot build a motive for either and the two have to be composed beforehand. -/
theorem chartBaseSectionRes_val_eq (U : s.base.Opens) (hU : IsAffineOpen U) (r : Γ(s.base, U))
    {W : Opens (ProjectiveSpectrum.top (s.sectionRingGrading U))} (x : W) :
    HomogeneousLocalization.val ((s.chartBaseSectionRes U hU r W).1 x) =
      algebraMap (s.sectionRing U) (Localization x.1.asHomogeneousIdeal.toIdeal.primeCompl)
        (s.sectionRingBaseMap U r) :=
  (congrArg HomogeneousLocalization.val (s.chartBaseSectionRes_val U hU r x)).trans
    (s.chartBaseSection_val U hU r x.1)

/-- Restricting the pullback of `r` from one open of the chart to a smaller one gives the
pullback there. -/
theorem map_chartBaseSectionRes (U : s.base.Opens) (hU : IsAffineOpen U) (r : Γ(s.base, U))
    {V W : (AlgebraicGeometry.Proj (s.sectionRingGrading U)).Opens} (hWV : W ≤ V) :
    (((AlgebraicGeometry.Proj (s.sectionRingGrading U)).presheaf.map
        (homOfLE hWV).op)).hom (s.chartBaseSectionRes U hU r V)
      = s.chartBaseSectionRes U hU r W := by
  rw [chartBaseSectionRes, chartBaseSectionRes, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- Two equal morphisms act the same way on sections. The inequality argument of
`AlgebraicGeometry.Scheme.Hom.appLE` has a type mentioning the morphism, so the morphism cannot be
rewritten underneath it; with both morphisms variables, `subst` is available and the two
inequalities then agree by proof irrelevance. -/
theorem appLE_congr {Y Z : Scheme.{u}} {f g : Y ⟶ Z} (hfg : f = g) (U : Z.Opens)
    (V : Y.Opens) (e : V ≤ f ⁻¹ᵁ U) (e' : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V e' := by
  subst hfg; rfl

/-- **The chart over `U` reads a section pulled back from the base as the constant fraction.**
Restricting `r ∈ Γ(s.base, U)` along the structure morphism of the relative `Proj` to an open `V`
lying over `U`, and then pulling the result back along the chart over `U`, gives the restriction
of `Stacks.RelativeProj.Situation.chartBaseSection`.

Together with `chartBaseSection_val` this is the identification the chartwise comparison of
`𝒪(1)` with the exceptional ideal sheaf of a blowup needs: the ideal-sheaf side names the
pulled-back section as a section of the structure sheaf of the relative `Proj`, the twist side
names it as a degree-zero element of the graded section ring, and the two have to be the same
before the two trivializations over a chart can be multiplied together. -/
theorem app_relativeProjChart_appLE (U : s.base.affineOpens) (r : Γ(s.base, U.1))
    {V : s.relativeProj.Opens} (hV : V ≤ s.relativeProjToBase ⁻¹ᵁ U.1) :
    ((s.relativeProjChart U).app V).hom ((s.relativeProjToBase).appLE U.1 V hV r)
      = s.chartBaseSectionRes U.1 U.2 r (s.relativeProjChart U ⁻¹ᵁ V) := by
  have h1 := Scheme.Hom.appLE_comp_appLE (s.relativeProjChart U) s.relativeProjToBase
    U.1 V (s.relativeProjChart U ⁻¹ᵁ V) hV le_rfl
  rw [Scheme.Hom.appLE_eq_app] at h1
  have h2 := appLE_congr ((s.relativeProjChart_isPullback U).w) U.1
    (s.relativeProjChart U ⁻¹ᵁ V) (fun x hx => hV hx)
    (fun x _ => s.chartToBase_mem U.1 U.2 x)
  have h3 := Scheme.Hom.appLE_map (s.chartToBase U.1 U.2)
    (s.top_le_preimage_chartToBase U.1 U.2)
    (homOfLE (le_top (a := s.relativeProjChart U ⁻¹ᵁ V))).op
  have e1 := ConcreteCategory.congr_hom h1 r
  have e2 := ConcreteCategory.congr_hom (h2.trans h3.symm) r
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1 e2 ⊢
  exact e1.trans e2

end Stacks.RelativeProj.Situation

end
