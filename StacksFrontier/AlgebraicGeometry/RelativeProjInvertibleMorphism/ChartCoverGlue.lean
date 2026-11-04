module

public import StacksFrontier.AlgebraicGeometry.Morphism.Twist
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwistGlue.Basic

/-!
# Morphisms of sheaves of modules glue over a cover indexed by the affine opens of a base

Let `p : X ⟶ S` be a morphism of schemes and let `g V : Z V ⟶ X`, one open immersion for each
affine open `V` of `S`, present the inverse image `p^{-1}(V)` as the image of the top open of
`Z V`. Two such families occur in [Stacks, Tag 01O9]: the charts
`rp.chart V : Proj 𝒜(V) ⟶ Proj_S(𝒜)` of a relative homogeneous spectrum
([Stacks, Tag 01NQ]), and the open subschemes `U(ψ) ∩ f^{-1}(V) ⊆ U(ψ)` over which the morphism
`r_{ℒ,ψ}` was glued.

A morphism of sheaves of modules on `X` may be glued from data on such a family by
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`. **That theorem asks
for the agreement of two members of the data over an arbitrary open that two members of the cover
both see, for an arbitrary pair of indices.** What a family built out of a construction functorial
in the base open supplies, however, is agreement for a *nested* pair `Z ≤ V` of affine opens only.
This file closes that gap: the pairwise overlap is `p^{-1}(V ⊓ V')`, the affine opens inside
`V ⊓ V'` cover it, and `Stacks.AlgebraicGeometry.Tag07ZGTwist.localApp_eq_of_refine` — which
leaves the nesting relation free for exactly this reason — reduces the arbitrary pair to the
nested one along the order of `S.affineOpens`.

This is for a cover indexed by the affine opens of a base what
`Stacks.RelativeProj.Situation.localApp_baseChangeCover_eq_of_nested` in
`StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleBaseChangeGlue` is for
the base-change cover of a relative `Proj`.

## Main results

* `…RelativeProjChartGlue.iSup_image_top_eq_top`: the family exhausts `X`, written with the images
  as images of the top open — the shape the glueing theorem's covering hypothesis takes.
* `…RelativeProjChartGlue.image_top_inf_le_iSup`: **the overlap of two members is covered by the
  members over the affine opens inside both base opens.**
* `…RelativeProjChartGlue.localApp_eq_of_nested_affineOpens`: **the glueing compatibility over an
  arbitrary pair of affine opens of the base follows from the case of a nested pair.** Nothing is
  assumed of the two sheaves of modules or of the local data.
* `…RelativeProjChartGlue.existsUnique_hom_of_nested_affineOpens`: **data compatible along the
  inclusions between affine opens of the base come from exactly one morphism on all of `X`.**
* `…RelativeProjChartGlue.existsUnique_hom_of_chart_nested` and
  `…RelativeProjChartGlue.existsUnique_hom_of_preimage_nested`: the two instances, for the chart
  cover of a relative `Proj` and for the cover by the inverse images of the affine opens.

## Implementation notes

The relation along which the nested case is taken is the order on `S.affineOpens`, not the
containment of images. The two differ: an image is `p^{-1}(V)`, so one sits inside another
whenever `p` misses the difference of the two base opens, while a construction functorial in the
base open supplies its comparison only for a genuine inclusion of affine opens. Nothing below
uses the containment of images.

No attribute is claimed. This is one rung of the glueing of [Stacks, Tag 01O9]'s `θ`, not a
covering set for any tag.

## References

* [Stacks Project, Tag 01NQ](https://stacks.math.columbia.edu/tag/01NQ)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ModuleHomGlue
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjChartGlue

/-! ### The affine opens of a base refine the intersection of two of them -/

variable {S : Scheme.{u}}

/-- **The affine opens of a scheme inside two given ones cover their intersection.** The affine
opens are a basis of the topology (`AlgebraicGeometry.Scheme.isBasis_affineOpens`), so a point of
`V ⊓ V'` has an affine neighbourhood inside `V ⊓ V'`. -/
public theorem inf_le_iSup_affineOpens (m m' : S.affineOpens) :
    (m.1 : S.Opens) ⊓ (m'.1 : S.Opens)
      ≤ ⨆ r : {r : S.affineOpens // r.1 ≤ m.1 ∧ r.1 ≤ m'.1}, (r.1.1 : S.Opens) := by
  intro x hx
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVle⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hx
      ((m.1 : S.Opens) ⊓ (m'.1 : S.Opens)).2
  have hle : (V : S.Opens) ≤ (m.1 : S.Opens) ⊓ (m'.1 : S.Opens) := hVle
  exact TopologicalSpace.Opens.mem_iSup.mpr
    ⟨⟨⟨V, hV⟩, hle.trans inf_le_left, hle.trans inf_le_right⟩, hxV⟩

/-! ### A cover whose members are the inverse images of the affine opens of a base -/

section Generic

variable {X : Scheme.{u}} (p : X ⟶ S) {Z : S.affineOpens → Scheme.{u}}
  (g : ∀ m : S.affineOpens, Z m ⟶ X) [∀ m : S.affineOpens, IsOpenImmersion (g m)]
  (hg : ∀ m : S.affineOpens, g m ''ᵁ (⊤ : (Z m).Opens) = p ⁻¹ᵁ (m.1 : S.Opens))

include hg

/-- **The members of the family exhaust `X`**, the inverse images of the affine opens of the base
being a covering. This is the covering hypothesis of
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover`. -/
public theorem iSup_image_top_eq_top :
    (⨆ m : S.affineOpens, g m ''ᵁ (⊤ : (Z m).Opens)) = ⊤ := by
  rw [iSup_congr hg, ← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top,
    Scheme.Hom.preimage_top]

/-- **The overlap of two members of the family is covered by the members over the affine opens of
the base inside both.** Each image is the inverse image of its affine open, so the overlap is the
inverse image of the intersection, and `…RelativeProjChartGlue.inf_le_iSup_affineOpens` covers
that intersection. This is the shape
`Stacks.AlgebraicGeometry.Tag07ZGTwist.localApp_eq_of_refine` consumes. -/
public theorem image_top_inf_le_iSup (m m' : S.affineOpens) :
    g m ''ᵁ (⊤ : (Z m).Opens) ⊓ g m' ''ᵁ (⊤ : (Z m').Opens)
      ≤ ⨆ r : {r : S.affineOpens // r.1 ≤ m.1 ∧ r.1 ≤ m'.1},
          g r.1 ''ᵁ (⊤ : (Z r.1).Opens) := by
  rw [hg m, hg m', iSup_congr fun r : {r : S.affineOpens // r.1 ≤ m.1 ∧ r.1 ≤ m'.1} => hg r.1,
    ← Scheme.Hom.preimage_inf, ← Scheme.Hom.preimage_iSup]
  exact Scheme.Hom.preimage_mono p (inf_le_iSup_affineOpens m m')

variable {M N : X.Modules} (Θ : ∀ m : S.affineOpens, M.restrict (g m) ⟶ N.restrict (g m))
  (hnest : ∀ m m' : S.affineOpens, m'.1 ≤ m.1 →
    ∀ (V : X.Opens) (W₁ : (Z m).Opens) (W₂ : (Z m').Opens)
      (h₁ : g m ''ᵁ W₁ = V) (h₂ : g m' ''ᵁ W₂ = V),
      localApp (g m) (Θ m) h₁ = localApp (g m') (Θ m') h₂)

include hnest

/-- **For a cover indexed by the affine opens of a base, the glueing compatibility over an
arbitrary pair of indices follows from the nested case.** Given local morphism data which agrees
wherever one affine open of the base is inside another, the data agrees wherever two members see
the same open of `X` — which is the hypothesis `hψ` of
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` for this cover.

Nothing is assumed of the two sheaves of modules. -/
public theorem localApp_eq_of_nested_affineOpens (m m' : S.affineOpens)
    (W₁ : (Z m).Opens) (W₂ : (Z m').Opens) (V : X.Opens)
    (h₁ : g m ''ᵁ W₁ = V) (h₂ : g m' ''ᵁ W₂ = V) :
    localApp (g m) (Θ m) h₁ = localApp (g m') (Θ m') h₂ :=
  Stacks.AlgebraicGeometry.Tag07ZGTwist.localApp_eq_of_refine g Θ
    (κ := fun m m' => {r : S.affineOpens // r.1 ≤ m.1 ∧ r.1 ≤ m'.1})
    (fun _ _ r => r.1) (fun m m' => m'.1 ≤ m.1)
    (fun _ _ r => r.2.1) (fun _ _ r => r.2.2)
    (image_top_inf_le_iSup p g hg) hnest m m' W₁ W₂ V h₁ h₂

/-- **Local data on a cover indexed by the affine opens of a base, compatible along the inclusions
between those affine opens, come from exactly one morphism of sheaves of modules on `X`.** This is
`Stacks.AlgebraicGeometry.ModuleHomGlue.existsUnique_hom_of_restrict_cover` with its
arbitrary-pair compatibility supplied by `…localApp_eq_of_nested_affineOpens`. -/
public theorem existsUnique_hom_of_nested_affineOpens :
    ∃! φ : M ⟶ N, ∀ m : S.affineOpens,
      (Scheme.Modules.restrictFunctor (g m)).map φ = Θ m :=
  existsUnique_hom_of_restrict_cover g (iSup_image_top_eq_top p g hg) Θ
    (localApp_eq_of_nested_affineOpens p g hg Θ hnest)

end Generic

/-! ### The chart cover of a relative `Proj` -/

section Chart

variable {A : SheafGradedAlgebra.{u} S} (rp : RelativeProjData A)

/-- The chart over an affine open of the base is an open immersion. This is
`Stacks.AlgebraicGeometry.RelativeProjTwistGlue.isOpenImmersion_chart` restated with the affine
open presented as a member of `Scheme.affineOpens`, at which spelling that instance does not fire
— it is keyed on `rp.chart U hU` with the open and its affineness separate. -/
public instance isOpenImmersion_chart_affineOpens (m : S.affineOpens) :
    IsOpenImmersion (rp.chart (m.1 : S.Opens) m.2) :=
  RelativeProjTwistGlue.isOpenImmersion_chart rp (m.1 : S.Opens) m.2

/-- The chart images of a relative `Proj` are the inverse images of the affine opens of the base,
which is the hypothesis the generic statements of this file take. -/
public theorem chart_image_top_affineOpens (m : S.affineOpens) :
    rp.chart (m.1 : S.Opens) m.2 ''ᵁ
        (⊤ : (AlgebraicGeometry.Proj (A.grading (m.1 : S.Opens))).Opens)
      = rp.toBase ⁻¹ᵁ (m.1 : S.Opens) :=
  RelativeProjTwistGlue.chart_image_top rp (m.1 : S.Opens) m.2

/-- **Chart data on a relative `Proj` compatible along the inclusions between the affine opens of
the base come from exactly one morphism of sheaves of modules.** The instance of
`…existsUnique_hom_of_nested_affineOpens` at the chart cover of [Stacks, Tag 01NQ]. -/
public theorem existsUnique_hom_of_chart_nested {M N : rp.scheme.Modules}
    (Θ : ∀ m : S.affineOpens,
      M.restrict (rp.chart (m.1 : S.Opens) m.2) ⟶ N.restrict (rp.chart (m.1 : S.Opens) m.2))
    (hnest : ∀ m m' : S.affineOpens, m'.1 ≤ m.1 →
      ∀ (V : rp.scheme.Opens)
        (W₁ : (AlgebraicGeometry.Proj (A.grading (m.1 : S.Opens))).Opens)
        (W₂ : (AlgebraicGeometry.Proj (A.grading (m'.1 : S.Opens))).Opens)
        (h₁ : rp.chart (m.1 : S.Opens) m.2 ''ᵁ W₁ = V)
        (h₂ : rp.chart (m'.1 : S.Opens) m'.2 ''ᵁ W₂ = V),
        localApp (rp.chart (m.1 : S.Opens) m.2) (Θ m) h₁
          = localApp (rp.chart (m'.1 : S.Opens) m'.2) (Θ m') h₂) :
    ∃! φ : M ⟶ N, ∀ m : S.affineOpens,
      (Scheme.Modules.restrictFunctor (rp.chart (m.1 : S.Opens) m.2)).map φ = Θ m :=
  existsUnique_hom_of_nested_affineOpens rp.toBase
    (fun m : S.affineOpens => rp.chart (m.1 : S.Opens) m.2)
    (chart_image_top_affineOpens rp) Θ hnest

end Chart

/-! ### The cover by the inverse images of the affine opens -/

section Preimage

variable {X : Scheme.{u}} (p : X ⟶ S)

/-- The inverse images of the affine opens of the base are the images of the top opens of
themselves, which is the hypothesis the generic statements of this file take. -/
public theorem preimage_image_top_affineOpens (m : S.affineOpens) :
    (p ⁻¹ᵁ (m.1 : S.Opens)).ι ''ᵁ (⊤ : (p ⁻¹ᵁ (m.1 : S.Opens)).toScheme.Opens)
      = p ⁻¹ᵁ (m.1 : S.Opens) :=
  Scheme.Opens.ι_image_top _

/-- **Data on the inverse images of the affine opens of the base, compatible along the inclusions
between those inverse images, come from exactly one morphism of sheaves of modules on `X`.** The
instance of `…existsUnique_hom_of_nested_affineOpens` at the cover over which
`AlgebraicGeometry.Scheme.glueOverAffinePreimages` glues a morphism, hence at the cover of `U(ψ)`
over which the `θ` of [Stacks, Tag 01O9] is assembled. -/
public theorem existsUnique_hom_of_preimage_nested {M N : X.Modules}
    (Θ : ∀ m : S.affineOpens, M.restrict (p ⁻¹ᵁ (m.1 : S.Opens)).ι
      ⟶ N.restrict (p ⁻¹ᵁ (m.1 : S.Opens)).ι)
    (hnest : ∀ m m' : S.affineOpens, m'.1 ≤ m.1 →
      ∀ (V : X.Opens) (W₁ : (p ⁻¹ᵁ (m.1 : S.Opens)).toScheme.Opens)
        (W₂ : (p ⁻¹ᵁ (m'.1 : S.Opens)).toScheme.Opens)
        (h₁ : (p ⁻¹ᵁ (m.1 : S.Opens)).ι ''ᵁ W₁ = V)
        (h₂ : (p ⁻¹ᵁ (m'.1 : S.Opens)).ι ''ᵁ W₂ = V),
        localApp (p ⁻¹ᵁ (m.1 : S.Opens)).ι (Θ m) h₁
          = localApp (p ⁻¹ᵁ (m'.1 : S.Opens)).ι (Θ m') h₂) :
    ∃! φ : M ⟶ N, ∀ m : S.affineOpens,
      (Scheme.Modules.restrictFunctor (p ⁻¹ᵁ (m.1 : S.Opens)).ι).map φ = Θ m :=
  existsUnique_hom_of_nested_affineOpens p
    (fun m : S.affineOpens => (p ⁻¹ᵁ (m.1 : S.Opens)).ι)
    (preimage_image_top_affineOpens p) Θ hnest

end Preimage

end Stacks.AlgebraicGeometry.RelativeProjChartGlue

end
