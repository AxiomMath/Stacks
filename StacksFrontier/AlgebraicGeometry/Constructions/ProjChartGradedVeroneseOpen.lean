module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedTransport
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedVeronese

/-!
# The morphism comparison of Tag 01NK on an arbitrary open where `ψ(A_d)` generates

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `T` a scheme, `L` an invertible `𝒪_T`-module and
`ψ : A → Γ_*(T, L)` a graded map in the degreewise spelling
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections`.

`Stacks.AlgebraicGeometry.ProjChartGradedVeronese.homOfLE_glued_eq_gluedVeronese` compares the
morphism `r_{L, ψ}` of [Stacks, Tag 01NK] with the morphism of [Stacks, Tag 01N8] attached to the
Veronese restriction `ψ|_{A^{(d)}}` over the union of the degree-`d` nonvanishing opens of `ψ`,
which is all of `T` when `ψ(A_d)` generates `L ^⊗ d` globally. The final clause of
[Stacks, Tag 01NK] asks for it over an **arbitrary open `V ⊆ T` on which `ψ(A_d)` generates
`L ^⊗ d`**, and [Stacks, Tag 01N8] applied over `V` needs the restriction of `ψ` to `V` as a datum.

This file supplies that comparison. The restricted datum is
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.pullback` along the open immersion
`V.ι`, and the hypothesis "`ψ(A_d)` generates `L ^⊗ d` on `V`" is read as
`V ≤ ⨆_{g ∈ 𝒜 d} T_{ψ(g)}` — by [Stacks, Tag 01CY] the degree-`d` values generate `L ^⊗ d` at a
point exactly when one of them does not vanish there.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartGradedVeroneseOpen.iSup_nonvanishingOpen_pullback_eq_top` —
  the degree-`d` nonvanishing opens of the restricted datum cover `V`.
* `Stacks.AlgebraicGeometry.ProjChartGradedVeroneseOpen.homOfLE_glued_eq_gluedVeronese_pullback` —
  **over `V`, the morphism `r_{L, ψ}` of [Stacks, Tag 01NK] is the morphism of
  [Stacks, Tag 01N8] attached to the Veronese restriction of the inverse-image datum `ψ|_V`.**

## Implementation notes

**No new mathematics about the charts.** Both sides restrict, on the member
`V ∩ T_{ψ(g)}` of the cover of `V`, to the dehomogenisation chart of `g` for the restricted datum:
the right side by `Stacks.AlgebraicGeometry.ProjChartGradedVeronese.ι_gluedVeronese`, the left side
by `Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.homOfLE_glued_of_pos` followed by
`Stacks.AlgebraicGeometry.ProjChartGradedPullback.resLE_chartToProj`, which says that the chart of
a homogeneous element commutes with pullback. The hypothesis `hψ` of that file — that each value
of the restricted datum is the pullback of the corresponding value of `ψ` — holds for
`GradedSections.pullback` by `rfl` in each degree.

**Why the cover of `V` is handled through the inclusion of its union.**
`Scheme.Opens.iSupOpenCover` covers `⨆ i, U i`, not the ambient scheme; here the union of the
members is `⊤`, so its inclusion into `V` is an isomorphism and in particular an epimorphism, which
is what reduces the identity of two morphisms out of `V` to an identity out of the union.

## References

* [Stacks Project, Tag 01NK](https://stacks.math.columbia.edu/tag/01NK)
* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjChartFullGraded (GradedSections)
open Stacks.AlgebraicGeometry.ProjChartGradedPullback (resLE_chartToProj)
open Stacks.AlgebraicGeometry.ProjChartGradedVeronese (gluedVeronese ι_gluedVeronese
  iSup_nonvanishingOpen_le_coveringOpen)
open Stacks.AlgebraicGeometry.ProjChartRatioPullback (pullSection)
open Stacks.NonvanishingOpen (nonvanishingOpen)
open Stacks.TensorPowers (natTensorPow)

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartGradedVeroneseOpen

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {T : Scheme.{u}} {L : T.Modules}
  [Stacks.Ample.IsInvertibleModule T L] (ψ : GradedSections 𝒜 L) {d : ℕ} (hd : 0 < d)
  {V : T.Opens}
  (hVgen : V ≤ ⨆ g : 𝒜 d, nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g))

/-- The values of the inverse-image datum along `V.ι` are the pullbacks of the values of `ψ`,
which is the hypothesis `Stacks.AlgebraicGeometry.ProjChartGradedPullback` takes on a restricted
datum. -/
theorem pullback_toFun_eq (n : ℕ) (a : 𝒜 n) :
    (GradedSections.pullback V.ι ψ).toFun n a = pullSection V.ι L n (ψ.toFun n a) :=
  rfl

/-- The nonvanishing open of a value of `ψ|_V` is the preimage of that of `ψ` under `V.ι`. -/
private theorem nonvanishingOpen_pullback_eq (g : 𝒜 d) :
    nonvanishingOpen V.toScheme (natTensorPow ((Scheme.Modules.pullback V.ι).obj L) d)
        ((GradedSections.pullback V.ι ψ).toFun d g)
      = V.ι ⁻¹ᵁ nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g) :=
  GradedSections.nonvanishingOpenAt_pullback V.ι ψ d g

omit hd in
include hVgen in
/-- **The degree-`d` nonvanishing opens of the restricted datum cover `V`.** Each is the preimage
under `V.ι` of the corresponding nonvanishing open of `ψ`
(`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.nonvanishingOpenAt_pullback`, which
is [Stacks, Tag 0H78]), and `V` lies in the union of those. -/
theorem iSup_nonvanishingOpen_pullback_eq_top :
    (⨆ g : 𝒜 d, nonvanishingOpen V.toScheme
        (natTensorPow ((Scheme.Modules.pullback V.ι).obj L) d)
        ((GradedSections.pullback V.ι ψ).toFun d g)) = ⊤ := by
  rw [iSup_congr (nonvanishingOpen_pullback_eq 𝒜 ψ), ← Scheme.Hom.preimage_iSup]
  refine Opens.ext ?_
  simp only [Scheme.Hom.coe_preimage, Opens.coe_top]
  rw [Set.eq_univ_iff_forall]
  exact fun x => hVgen x.2

/-- **Over an open `V` on which the degree-`d` values of `ψ` generate `L ^⊗ d`, the morphism
`r_{L, ψ}` of [Stacks, Tag 01NK] is the morphism of [Stacks, Tag 01N8] attached to the Veronese
restriction of the inverse-image datum `ψ|_V`.**

Both sides restrict, on the member `V ∩ T_{ψ(g)}` of the cover of `V` by the degree-`d`
nonvanishing opens of `ψ|_V`, to the dehomogenisation chart of `g` for `ψ|_V`: the right side by
`Stacks.AlgebraicGeometry.ProjChartGradedVeronese.ι_gluedVeronese`, the left side by
`Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.homOfLE_glued_of_pos` and the
commutation of the chart of a homogeneous element with pullback
(`Stacks.AlgebraicGeometry.ProjChartGradedPullback.resLE_chartToProj`). Those opens cover `V`, so
the two morphisms out of `V` are equal. -/
-- Beyond what this declaration proves: the companion clause that θ restricts on V to the
-- isomorphism α of Tag 01N8, as an equality of morphisms of sheaves over V, is
-- ProjChartGradedThetaMoreover.moreover; both halves of the final clause are part of the carrier
-- ProjChartGradedTripleTag.tag01NK. The same comparison over the union of the degree-d
-- nonvanishing opens of ψ, with no restriction of the datum, is
-- ProjChartGradedVeronese.homOfLE_glued_eq_gluedVeronese.
theorem homOfLE_glued_eq_gluedVeronese_pullback :
    T.homOfLE (hVgen.trans (iSup_nonvanishingOpen_le_coveringOpen 𝒜 ψ hd)) ≫ ψ.glued
      = Stacks.AlgebraicGeometry.MorphismsIntoProj.toProj 𝒜
          (gluedVeronese 𝒜 (GradedSections.pullback V.ι ψ) hd
            (iSup_nonvanishingOpen_pullback_eq_top 𝒜 ψ hVgen)) := by
  have htop := iSup_nonvanishingOpen_pullback_eq_top 𝒜 ψ hVgen
  have hiso : IsIso (⨆ g : 𝒜 d, nonvanishingOpen V.toScheme
      (natTensorPow ((Scheme.Modules.pullback V.ι).obj L) d)
      ((GradedSections.pullback V.ι ψ).toFun d g)).ι := by
    rw [htop]
    exact ⟨V.toScheme.topIso.inv, V.toScheme.ι_toIso_inv, V.toScheme.toIso_inv_ι⟩
  have key : ∀ g : 𝒜 d, (nonvanishingOpen V.toScheme
        (natTensorPow ((Scheme.Modules.pullback V.ι).obj L) d)
        ((GradedSections.pullback V.ι ψ).toFun d g)).ι
          ≫ T.homOfLE (hVgen.trans (iSup_nonvanishingOpen_le_coveringOpen 𝒜 ψ hd)) ≫ ψ.glued
      = (nonvanishingOpen V.toScheme
          (natTensorPow ((Scheme.Modules.pullback V.ι).obj L) d)
          ((GradedSections.pullback V.ι ψ).toFun d g)).ι
          ≫ Stacks.AlgebraicGeometry.MorphismsIntoProj.toProj 𝒜
              (gluedVeronese 𝒜 (GradedSections.pullback V.ι ψ) hd htop) := by
    intro g
    have hW := (nonvanishingOpen_pullback_eq 𝒜 ψ (V := V) g).le
    have hsplit : (nonvanishingOpen V.toScheme
            (natTensorPow ((Scheme.Modules.pullback V.ι).obj L) d)
            ((GradedSections.pullback V.ι ψ).toFun d g)).ι
            ≫ T.homOfLE (hVgen.trans (iSup_nonvanishingOpen_le_coveringOpen 𝒜 ψ hd))
        = V.ι.resLE (nonvanishingOpen T (natTensorPow L d) (ψ.toFun d g)) _ hW
            ≫ T.homOfLE (ψ.nonvanishingOpenAt_le_coveringOpen_of_pos g.2 hd) := by
      rw [← cancel_mono ψ.coveringOpen.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι,
        Scheme.homOfLE_ι, Scheme.Hom.resLE_comp_ι]
    rw [← Category.assoc, hsplit, Category.assoc, ψ.homOfLE_glued_of_pos g.2 hd,
      ι_gluedVeronese 𝒜 (GradedSections.pullback V.ι ψ) hd htop g]
    exact resLE_chartToProj V.ι L ψ (GradedSections.pullback V.ι ψ) (pullback_toFun_eq 𝒜 ψ) g.2 hd
      le_rfl hW le_rfl
  rw [← cancel_epi (⨆ g : 𝒜 d, nonvanishingOpen V.toScheme
    (natTensorPow ((Scheme.Modules.pullback V.ι).obj L) d)
    ((GradedSections.pullback V.ι ψ).toFun d g)).ι]
  refine Scheme.Cover.hom_ext (Scheme.Opens.iSupOpenCover
    (fun g : 𝒜 d => nonvanishingOpen V.toScheme
      (natTensorPow ((Scheme.Modules.pullback V.ι).obj L) d)
      ((GradedSections.pullback V.ι ψ).toFun d g))) _ _ fun g => ?_
  have h := key g
  dsimp only [Scheme.Opens.iSupOpenCover]
  simp only [← Category.assoc, Scheme.homOfLE_ι]
  exact h

end Stacks.AlgebraicGeometry.ProjChartGradedVeroneseOpen

end
