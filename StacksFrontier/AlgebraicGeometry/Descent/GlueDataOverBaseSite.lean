module

public import StacksFrontier.AlgebraicGeometry.Descent.GlueDataOverBase
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability

/-!
# Gluing objects of the big fppf site over an object of the site

Let `M` be an object of the big fppf site of `S` and let `D` be a gluing datum of schemes over the
underlying scheme of `M` (`AlgebraicGeometry.Scheme.GlueDataOverBase`) whose pieces are the
underlying schemes of objects `N i` of the site, with structure morphisms the underlying
morphisms of morphisms `N i ⟶ M` of the site. If the index type and the sizes of the pieces are
bounded below the cutoff of the site, the glued scheme lies in the site: it is the underlying
scheme of an object `Y` of the site, with a morphism `Y ⟶ M` of the site restricting to the given
ones, and charts `N i ⟶ Y` which are open immersions.

This is the gluing step of Stacks 01JA–01JB in the form the proof of Stacks 0DUS uses, where the
pieces are the moduli spaces of the members of an open covering of `𝒳'`.

## Main definitions

* `AlgebraicGeometry.Scheme.GlueDataOverBase.siteObj`: the glued object of the site.
* `AlgebraicGeometry.Scheme.GlueDataOverBase.siteToBase`: its morphism to `M`.
* `AlgebraicGeometry.Scheme.GlueDataOverBase.siteι`: the charts.

## Main results

* `AlgebraicGeometry.Scheme.GlueDataOverBase.contains_glued`: the glued scheme lies in the site.

## References

* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
* [Stacks Project, Tag 01JB](https://stacks.math.columbia.edu/tag/01JB)
* [Stacks Project, Tag 000Q](https://stacks.math.columbia.edu/tag/000Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace AlgebraicGeometry.Scheme.GlueDataOverBase

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {Mo : BigFppfOver B S hS} (D : GlueDataOverBase ((BigFppfOver.toScheme B S hS).obj Mo))

/-- **The glued scheme lies in the site** when the index type and the sizes of the pieces are
bounded below the cutoff (Stacks 000Q for the open covering by the charts). -/
theorem contains_glued (hJ : #D.J < B.cutoff) {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
    (hsize : ∀ i, (D.obj i).size ≤ μ) : B.Contains D.glued := by
  by_cases hEmpty : IsEmpty D.J
  · have hpt : IsEmpty D.glued := ⟨fun x => by
      obtain ⟨i, -, -⟩ := D.ι_jointly_surjective x
      exact hEmpty.false i⟩
    exact lt_of_le_of_lt (size_le_aleph0_of_isEmpty D.glued hpt) B.aleph0_lt_cutoff
  · have _ : Nonempty D.J := not_isEmpty_iff.mp hEmpty
    have hsz : D.glued.size ≤ max #D.J (⨆ i : D.J, (D.obj i).size) := by
      refine le_of_le_of_eq (Scheme.size_le_of_iSup_eq_top
        (fun i => (D.ι i).opensRange) D.iSup_opensRange_ι) ?_
      congr 2
      funext i
      simpa only [Scheme.Hom.image_top_eq_opensRange] using
        (Scheme.size_congr ((D.obj i).topIso.symm ≪≫ (D.ι i).isoImage ⊤)).symm
    exact hsz.trans_lt (max_lt hJ ((ciSup_le' hsize).trans_lt hμ))

variable (hJ : #D.J < B.cutoff) {μ : Cardinal.{u}} (hμ : μ < B.cutoff)
  (hsize : ∀ i, (D.obj i).size ≤ μ)

/-- The glued object of the site: the glued scheme, over `S` through the base `M`. -/
noncomputable abbrev siteObj : BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk (X := B.obj (D.contains_glued hJ hμ hsize)) (Y := B.obj hS)
    (D.toBase ≫ Mo.hom.hom))

/-- The structure morphism of the glued object to `M`, as a morphism of the site. -/
noncomputable abbrev siteToBase : D.siteObj hJ hμ hsize ⟶ Mo :=
  Over.homMk (ObjectProperty.homMk (X := B.obj (D.contains_glued hJ hμ hsize)) D.toBase) rfl

/-- On underlying schemes the structure morphism of the glued object is that of the glued
scheme. -/
theorem toScheme_map_siteToBase :
    (BigFppfOver.toScheme B S hS).map (D.siteToBase hJ hμ hsize) = D.toBase := rfl

end AlgebraicGeometry.Scheme.GlueDataOverBase

end
