module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.PullbackSectionCalculus
public import StacksFrontier.AlgebraicGeometry.TwistPullbackRatio.Comparison

/-!
# Base change of a morphism along a chart, and the vanishing of a pulled-back section

Let `c : V ⟶ X` be an open immersion — a *chart* of `X` — and let `i : Z ⟶ X` be an arbitrary
morphism of schemes. The open of `X` that the chart covers is `c ''ᵁ ⊤`, and the base change of
`i` along `c` is the restriction of `i` to that open, read on `V` through the identification of
`V` with it. This file constructs that base change and computes when a section pulls back to
zero along it.

The point of the computation is that both sides of a *chart comparison* — a statement that an
ideal built from vanishing on a relative construction agrees, over a chart, with the ideal built
from vanishing on the absolute one — are vanishing conditions, but they are written in different
vocabularies. On the relative side a section lives over the open `c ''ᵁ ⊤` of `X` and is pulled
back with `AlgebraicGeometry.Scheme.Modules.pullbackSection` along `i`; on the absolute side the
same section is a *global* section of the restriction `F.restrict c` on `V` and is pulled back
with `AlgebraicGeometry.pullbackGlobalSections` along the base change.
`Stacks.AlgebraicGeometry.ChartBaseChange.pullbackGlobalSections_chartRestrict_eq_zero_iff` says
the two conditions agree.

## Main definitions

* `Stacks.AlgebraicGeometry.ChartBaseChange.chartIsoOpen`: the chart, as an isomorphism of `V`
  with the open subscheme it covers.
* `Stacks.AlgebraicGeometry.ChartBaseChange.chartRestrict`: **the base change of `i` along the
  chart**, a morphism `i ⁻¹ᵁ (c ''ᵁ ⊤) ⟶ V`.

## Main results

* `Stacks.AlgebraicGeometry.ChartBaseChange.chartRestrict_comp`: the base change is a morphism
  over `X`, i.e. the square whose other side is the open immersion of `i ⁻¹ᵁ (c ''ᵁ ⊤)` into `Z`
  commutes.
* `Stacks.AlgebraicGeometry.ChartBaseChange.isClosedImmersion_chartRestrict`: the base change of
  a closed immersion is a closed immersion.
* `Stacks.AlgebraicGeometry.ChartBaseChange.pullbackGlobalSections_chartRestrict_eq_zero_iff`:
  **the comparison of the two vanishing conditions.**

## Implementation notes

The base change is *not* built as a limit. A pullback of `i` along `c` would have to be compared
with the restriction `i ∣_ (c ''ᵁ ⊤)` before anything could be computed on sections, and that
comparison is the only thing a limit would buy. Taking the restriction as the definition makes
`chartRestrict_comp` the composite of `AlgebraicGeometry.morphismRestrict_ι` with the
factorization of `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq`, and makes the closed-immersion
statement an instance search: being a closed immersion is local at the target.

The vanishing comparison is a chain of four identities in the
`AlgebraicGeometry.Scheme.Modules.pullbackSection` vocabulary, each an existing lemma, with the
isomorphism appearing in it discharged by
`Stacks.AlgebraicGeometry.ChartBaseChange.val_app_eq_zero_iff`: the comparison of a restriction
with a pullback (`Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctorIsoPullback_hom_val_app`),
naturality in the module, the composite `AlgebraicGeometry.Scheme.Modules.pullbackSection_comp`
twice — once along `chartRestrict c i ≫ c` and once along the other side of the square — and the
transport `AlgebraicGeometry.Scheme.Modules.pullbackSection_congr` between them. The last step,
that a section pulled back along an open immersion to the whole source vanishes only if it
vanishes, is `pullbackSection_top_eq_zero_iff_of_isOpenImmersion`, proved by `subst` on the open
and the same restriction-pullback comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.AlgebraicGeometry.ChartBaseChange

/-! ### Vanishing under an isomorphism of modules -/

/-- An isomorphism of sheaves of modules detects the vanishing of a section. -/
theorem val_app_eq_zero_iff {Y : Scheme.{u}} {A B : Y.Modules} (θ : A ⟶ B) [IsIso θ]
    (V : Y.Opens) (x : A.val.obj (op V)) : θ.val.app (op V) x = 0 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h]; exact map_zero _⟩
  have h0 := ModuleLimits.inv_val_app_apply θ V x
  rw [h, map_zero] at h0
  exact h0.symm

/-- **Pulling a section back along an open immersion, to the whole source, detects vanishing.**
Over the open the immersion covers, the pullback is the comparison of the restriction with the
pullback applied to the section, and that comparison is an isomorphism. -/
theorem pullbackSection_top_eq_zero_iff_of_isOpenImmersion {Y X : Scheme.{u}} (j : Y ⟶ X)
    [IsOpenImmersion j] (N : X.Modules) (U : X.Opens) (hU : j ''ᵁ (⊤ : Y.Opens) = U)
    (h : (⊤ : Y.Opens) ≤ j ⁻¹ᵁ U) (y : N.val.obj (op U)) :
    pullbackSection j N U ⊤ h y = 0 ↔ y = 0 := by
  subst hU
  rw [← ModuleLimits.restrictFunctorIsoPullback_hom_val_app j N ⊤ h y]
  exact val_app_eq_zero_iff ((restrictFunctorIsoPullback j).hom.app N) ⊤ y

/-- Pulling back a section of the whole space to the whole space is
`AlgebraicGeometry.pullbackGlobalSections`: the two differ by a restriction along the unique
morphism `⊤ ⟶ f ⁻¹ᵁ ⊤`. -/
theorem pullbackSection_top_eq_pullbackGlobalSections {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : X.Modules) (h : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ (⊤ : X.Opens)) (a : F.val.obj (op ⊤)) :
    pullbackSection f F ⊤ ⊤ h a = pullbackGlobalSections f F a := by
  unfold pullbackSection pullbackGlobalSections
  congr 1

/-- A pulled-back global section vanishes iff its pullback to the whole source does. -/
private theorem pullbackGlobalSections_eq_zero_iff_pullbackSection {X Y : Scheme.{u}}
    (f : Y ⟶ X) (F : X.Modules) (a : F.val.obj (op ⊤)) :
    pullbackGlobalSections f F a = 0 ↔ pullbackSection f F ⊤ ⊤ le_top a = 0 :=
  (Iff.of_eq (congrArg (· = 0) (pullbackSection_top_eq_pullbackGlobalSections f F le_top a))).symm

/-- **An isomorphism of modules detects the vanishing of a pulled-back global section.** -/
theorem pullbackGlobalSections_hom_eq_zero_iff {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N : X.Modules} (θ : M ⟶ N) [IsIso θ] (x : M.val.obj (op ⊤)) :
    pullbackGlobalSections f N (θ.val.app (op ⊤) x) = 0 ↔
      pullbackGlobalSections f M x = 0 := by
  rw [pullbackGlobalSections_eq_zero_iff_pullbackSection,
    pullbackGlobalSections_eq_zero_iff_pullbackSection,
    ← pullbackSection_naturality f θ ⊤ ⊤ le_top x]
  exact val_app_eq_zero_iff (((Scheme.Modules.pullback f).map θ)) ⊤ _

/-- **Transporting a vanishing condition along an equality of opens.** -/
theorem pullbackSection_eq_zero_iff_congr {X Z : Scheme.{u}} (i : Z ⟶ X) (F : X.Modules)
    {W W' : X.Opens} (hW : W = W') {t : F.val.obj (op W)} {t' : F.val.obj (op W')}
    (ht : hW ▸ t = t') :
    pullbackSection i F W (i ⁻¹ᵁ W) le_rfl t = 0 ↔
      pullbackSection i F W' (i ⁻¹ᵁ W') le_rfl t' = 0 := by
  subst hW
  rw [← ht]

/-! ### The base change of a morphism along a chart -/

variable {X V Z : Scheme.{u}} (c : V ⟶ X) [IsOpenImmersion c] (i : Z ⟶ X)

/-- **The chart, as an isomorphism of `V` with the open subscheme it covers.** -/
def chartIsoOpen : V ≅ (c ''ᵁ (⊤ : V.Opens)).toScheme :=
  IsOpenImmersion.isoOfRangeEq c (c ''ᵁ (⊤ : V.Opens)).ι (by
    rw [Scheme.Opens.range_ι, Scheme.Hom.image_top_eq_opensRange]; rfl)

/-- The isomorphism `chartIsoOpen c` followed by the inclusion of the image of `c` is `c`. -/
theorem chartIsoOpen_hom_comp :
    (chartIsoOpen c).hom ≫ (c ''ᵁ (⊤ : V.Opens)).ι = c :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- The inverse of `chartIsoOpen c` followed by `c` is the inclusion of the image of `c`. -/
theorem chartIsoOpen_inv_comp :
    (chartIsoOpen c).inv ≫ c = (c ''ᵁ (⊤ : V.Opens)).ι :=
  (Iso.inv_comp_eq _).mpr (chartIsoOpen_hom_comp c).symm

/-- **The base change of `i` along the chart `c`**: the restriction of `i` to the open the chart
covers, read on `V`. -/
def chartRestrict : (i ⁻¹ᵁ (c ''ᵁ (⊤ : V.Opens))).toScheme ⟶ V :=
  i ∣_ (c ''ᵁ (⊤ : V.Opens)) ≫ (chartIsoOpen c).inv

/-- **The base change is a morphism over `X`.** -/
theorem chartRestrict_comp :
    chartRestrict c i ≫ c = (i ⁻¹ᵁ (c ''ᵁ (⊤ : V.Opens))).ι ≫ i := by
  rw [chartRestrict, Category.assoc, chartIsoOpen_inv_comp c, morphismRestrict_ι]

/-- **The base change of a closed immersion along a chart is a closed immersion.** -/
instance isClosedImmersion_chartRestrict [IsClosedImmersion i] :
    IsClosedImmersion (chartRestrict c i) := by
  rw [chartRestrict]
  infer_instance

/-! ### The vanishing of a pulled-back section -/

/-- Half of the comparison: pulling a global section of the restriction back along the base
change is, up to three isomorphisms, pulling the section back along the other side of the
square. -/
theorem pullbackSection_chartRestrict_eq_zero_iff (F : X.Modules)
    (t : (Scheme.Modules.restrict F c).val.obj (op ⊤))
    (h : (⊤ : (i ⁻¹ᵁ (c ''ᵁ (⊤ : V.Opens))).toScheme.Opens) ≤
      ((i ⁻¹ᵁ (c ''ᵁ (⊤ : V.Opens))).ι ≫ i) ⁻¹ᵁ (c ''ᵁ (⊤ : V.Opens))) :
    pullbackSection (chartRestrict c i) (Scheme.Modules.restrict F c) ⊤ ⊤ le_top t = 0 ↔
      pullbackSection ((i ⁻¹ᵁ (c ''ᵁ (⊤ : V.Opens))).ι ≫ i) F
        (c ''ᵁ (⊤ : V.Opens)) ⊤ h t = 0 := by
  have hg : (⊤ : V.Opens) ≤ c ⁻¹ᵁ (c ''ᵁ (⊤ : V.Opens)) := (c.preimage_image_eq ⊤).ge
  have hsq := chartRestrict_comp c i
  have hcomp : (⊤ : (i ⁻¹ᵁ (c ''ᵁ (⊤ : V.Opens))).toScheme.Opens) ≤
      (chartRestrict c i ≫ c) ⁻¹ᵁ (c ''ᵁ (⊤ : V.Opens)) := by rw [hsq]; exact h
  rw [← pullbackSection_congr hsq F (c ''ᵁ (⊤ : V.Opens)) ⊤ hcomp h t,
    val_app_eq_zero_iff,
    ← pullbackSection_comp (chartRestrict c i) c F (c ''ᵁ (⊤ : V.Opens)) ⊤ ⊤ hg le_top hcomp t,
    val_app_eq_zero_iff,
    ← ModuleLimits.restrictFunctorIsoPullback_hom_val_app c F ⊤ hg t,
    ← pullbackSection_naturality (chartRestrict c i)
      ((restrictFunctorIsoPullback c).hom.app F) ⊤ ⊤ le_top t,
    val_app_eq_zero_iff]

/-- The other half: pulling a section back along the open immersion of `i ⁻¹ᵁ (c ''ᵁ ⊤)` into `Z`
composed with `i` detects exactly what pulling it back along `i` does. -/
theorem pullbackSection_comp_ι_eq_zero_iff (F : X.Modules) (W : X.Opens)
    (t : F.val.obj (op W))
    (h : (⊤ : (i ⁻¹ᵁ W).toScheme.Opens) ≤ ((i ⁻¹ᵁ W).ι ≫ i) ⁻¹ᵁ W) :
    pullbackSection ((i ⁻¹ᵁ W).ι ≫ i) F W ⊤ h t = 0 ↔
      pullbackSection i F W (i ⁻¹ᵁ W) le_rfl t = 0 := by
  have hf2 : (⊤ : (i ⁻¹ᵁ W).toScheme.Opens) ≤ (i ⁻¹ᵁ W).ι ⁻¹ᵁ (i ⁻¹ᵁ W) := by simp
  rw [← pullbackSection_comp (i ⁻¹ᵁ W).ι i F W (i ⁻¹ᵁ W) ⊤ le_rfl hf2 h t,
    val_app_eq_zero_iff,
    pullbackSection_top_eq_zero_iff_of_isOpenImmersion (i ⁻¹ᵁ W).ι
      ((Scheme.Modules.pullback i).obj F) (i ⁻¹ᵁ W) (by simp) hf2]

/-- **The comparison of the two vanishing conditions.** A global section `t` of the restriction
`F.restrict c` — equivalently, a section of `F` over the open `c ''ᵁ ⊤` the chart covers — pulls
back to zero along the base change of `i` exactly when it pulls back to zero along `i` itself. -/
theorem pullbackGlobalSections_chartRestrict_eq_zero_iff (F : X.Modules)
    (t : (Scheme.Modules.restrict F c).val.obj (op ⊤)) :
    pullbackGlobalSections (chartRestrict c i) (Scheme.Modules.restrict F c) t = 0 ↔
      pullbackSection i F (c ''ᵁ (⊤ : V.Opens))
        (i ⁻¹ᵁ (c ''ᵁ (⊤ : V.Opens))) le_rfl t = 0 := by
  have hgen : ∀ W : X.Opens, (⊤ : (i ⁻¹ᵁ W).toScheme.Opens) ≤ ((i ⁻¹ᵁ W).ι ≫ i) ⁻¹ᵁ W :=
    fun W => by simp
  rw [pullbackGlobalSections_eq_zero_iff_pullbackSection]
  exact (pullbackSection_chartRestrict_eq_zero_iff c i F t (hgen _)).trans
    (pullbackSection_comp_ι_eq_zero_iff i F (c ''ᵁ (⊤ : V.Opens)) t (hgen _))

end Stacks.AlgebraicGeometry.ChartBaseChange

end
