module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafDataFromCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedEtaleDiagonalChartFunctoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleHomDescentSingleChart

/-!
# The chart transport of a morphism of `𝒪_X`-modules at two charts

Let `F` be an algebraic space over a scheme `S` of a big fppf site `B`, let `M` and `N` be
presheaves of modules over the structure presheaf of its small étale site, let `A` be an étale
chart and let `α : M|_A ⟶ N|_A` be a morphism of the restrictions to the slice of the small étale
site at `A`. For a morphism of charts `k : A' ⟶ A`, this file relates the relocalization
`AlgebraicGeometry.Space.homRestr … k α` to the components of `α` over Zariski opens of
`chartScheme A`, and proves the étale base-change comparison for the chart restriction of a
quasi-coherent module.

A Zariski open `V` of `chartScheme A` cuts out an étale chart `openChart A V` of `F`, and its
preimage under `chartSchemeMap k` cuts out one of `A'`; `AlgebraicGeometry.Space.openChartRestrict`
is the morphism of charts between them, and it sits in a commuting square over `k`. The component
of `homRestr … k α` over an open of `chartScheme A'` lying over `V` is the relocalization along
`openChartRestrict` of the component of `α` over `V`.

## Main results

* `Stacks.PresheafOfModules.homRestr_of_comm_sq`: a commuting square of the site sends the two
  relocalizations of a morphism to one and the same morphism.
* `Stacks.PresheafOfModules.toPresheaf_map_homRestr_app`: the component of a relocalization over
  an object `Z` of the slice at the smaller index is the component of the morphism itself over
  `Z` pushed into the slice at the larger one.
* `AlgebraicGeometry.Space.homRestr_openChartRestrict`: the naturality of the chart transport in
  the chart. Relocalizing `α` to the chart cut out by a Zariski open `V` of `chartScheme A` and
  then along `AlgebraicGeometry.Space.openChartRestrict` is relocalizing it along `k` and then to
  the chart cut out by the preimage of `V`.
* `AlgebraicGeometry.Space.homRestr_openChartInclusion_comp`: the same with an open of
  `chartScheme A'` lying over `V` in place of the whole preimage.
* `AlgebraicGeometry.Space.ofArrows_openChartInclusion_mem_topology`: a family of Zariski opens
  covering a chart's scheme induces a covering sieve of the chart in the small étale site.
* `AlgebraicGeometry.Space.homRestr_ext`: two morphisms `M|_A ⟶ N|_A` agreeing after
  relocalization along every arrow of a covering sieve of `A` are equal.
* `AlgebraicGeometry.Space.homRestr_eq_of_forall_openChart` and
  `AlgebraicGeometry.Space.homRestr_eq_of_forall_openChart_le`: the equality of the two
  relocalizations of `α` along a pair of chart morphisms is local on the smaller chart's scheme,
  and over each member of a cover it is an equality of relocalizations of the components of `α`
  over Zariski opens of the larger chart's scheme.
* `AlgebraicGeometry.Space.existsUnique_hom_of_single_chart_prod_openChart`: the one-chart gluing
  with its compatibility condition read at the opens of the kernel pair's scheme.
* `AlgebraicGeometry.Space.bijective_sectionsBaseChange_openChartRestrict`: the étale base-change
  comparison for the chart restriction of a quasi-coherent module. Over an affine open of
  `chartScheme A'` lying over an affine open of `chartScheme A`, the sections of a quasi-coherent
  `𝒪_F`-module are the base change of its sections over the larger open.
* `AlgebraicGeometry.Space.support_compl_idealSheafDataOfChart` and
  `AlgebraicGeometry.Space.le_preimage_support_compl_idealSheafDataOfChart`: the open over which
  the chartwise sheaf of ideals is trivial is pulled back along a morphism of charts, so an open
  of the smaller chart's scheme off the support lies over the corresponding open of the larger
  one.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 03G6](https://stacks.math.columbia.edu/tag/03G6)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 07UM](https://stacks.math.columbia.edu/tag/07UM)
-/

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

namespace Stacks.PresheafOfModules

universe v₁ u₁ t₁

variable {C : Type u₁} [Category.{v₁} C] (O : Cᵒᵖ ⥤ CommRingCat)
  (M N : _root_.PresheafOfModules.{t₁} (Oforget O))

/-- **A commuting square sends the two relocalizations of a morphism to one and the same
morphism.**  If `r ≫ j = j' ≫ k` then relocalizing `α : M|_A ⟶ N|_A` along `j` and then along
`r` agrees with relocalizing it along `k` and then along `j'`. -/
theorem homRestr_of_comm_sq {A A' Q Q' : C} (k : A' ⟶ A) (j : Q ⟶ A) (j' : Q' ⟶ A')
    (r : Q' ⟶ Q) (hsq : r ≫ j = j' ≫ k)
    (α : (restrFun O A).obj M ⟶ (restrFun O A).obj N) :
    homRestr O M N r (homRestr O M N j α) = homRestr O M N j' (homRestr O M N k α) :=
  by rw [← homRestr_comp, ← homRestr_comp, hsq]

/-- **The component of a relocalization.**  Over an object `Z` of the slice at the smaller index,
the relocalization of `α` along `f` is `α` itself over the image of `Z` in the slice at the
larger index, as maps of the underlying abelian presheaves. -/
theorem toPresheaf_map_homRestr_app {V U : C} (f : V ⟶ U)
    (α : (restrFun O U).obj M ⟶ (restrFun O U).obj N) (Z : (Over V)ᵒᵖ) :
    ((_root_.PresheafOfModules.toPresheaf (ORestr O V)).map
          (homRestr O M N f α)).app Z =
      ((_root_.PresheafOfModules.toPresheaf (ORestr O U)).map α).app
        (op ((Over.map f).obj Z.unop)) := rfl

end Stacks.PresheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-! ### The squares of charts cut out by Zariski opens -/

/-- **The square over a morphism of charts cut out by an open lying over a Zariski open.**  Let
`k : A' ⟶ A` be a morphism of charts, let `V` be a Zariski open of `chartScheme A` and let `U` be
a Zariski open of `chartScheme A'` inside the preimage of `V`.  The chart `openChart A' U` maps
to `openChart A V`, over `k`. -/
theorem openChartHomOfLE_comp_openChartRestrict_comp_openChartInclusion
    {A A' : SmallEtale B S hS F} (k : A' ⟶ A) (V : (chartScheme A).Opens)
    {U : (chartScheme A').Opens} (hU : U ≤ chartSchemeMap k ⁻¹ᵁ V) :
    (openChartHomOfLE B S hS F A' hU ≫ openChartRestrict B S hS F k V) ≫
        openChartInclusion B S hS F A V =
      openChartInclusion B S hS F A' U ≫ k := by
  rw [Category.assoc, openChartRestrict_comp_openChartInclusion, ← Category.assoc,
    openChartHomOfLE_comp_openChartInclusion]

/-- **A family of Zariski opens covering a chart's scheme induces a covering sieve of the
chart** in the small étale site. -/
theorem ofArrows_openChartInclusion_mem_topology (A : SmallEtale B S hS F) {ι : Type*}
    (Ω : ι → (chartScheme A).Opens) (hΩ : ⨆ i, Ω i = ⊤) :
    Sieve.ofArrows (fun i => openChart B S hS F A (Ω i))
        (fun i => openChartInclusion B S hS F A (Ω i)) ∈
      SmallEtale.topology B S hS F A := by
  refine SmallEtale.ofArrows_mem_topology B S hS F _ _ ?_
  rw [Scheme.ofArrows_mem_etalePrecoverage_iff]
  refine ⟨fun x ↦ ?_, fun i ↦ etale_toScheme_toOver_map B S hS F _⟩
  have hx : x ∈ (⊤ : (chartScheme A).Opens) := trivial
  rw [← hΩ] at hx
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨y, hy⟩ := (Scheme.Opens.range_ι (X := chartScheme A) (Ω i)).ge hi
  refine ⟨i, y, ?_⟩
  rwa [toScheme_map_toOver_map_openChartInclusion B S hS F A (Ω i)]

/-! ### Naturality of the chart transport in the chart -/

variable (M N : PresheafOfModules.{u} (Oforget (smallEtaleStructurePresheaf B S hS F hF)))

/-- **The naturality of the chart transport in the chart.**  Let `k : A' ⟶ A` be a morphism of
étale charts and let `V` be a Zariski open of `chartScheme A`.  Relocalizing
`α : M|_A ⟶ N|_A` to the chart which `V` cuts out and then along
`AlgebraicGeometry.Space.openChartRestrict` agrees with relocalizing it along `k` and then to the
chart which the preimage of `V` cuts out. -/
theorem homRestr_openChartRestrict {A A' : SmallEtale B S hS F} (k : A' ⟶ A)
    (V : (chartScheme A).Opens)
    (α : (restrFun (smallEtaleStructurePresheaf B S hS F hF) A).obj M ⟶
      (restrFun (smallEtaleStructurePresheaf B S hS F hF) A).obj N) :
    homRestr (smallEtaleStructurePresheaf B S hS F hF) M N (openChartRestrict B S hS F k V)
        (homRestr (smallEtaleStructurePresheaf B S hS F hF) M N
          (openChartInclusion B S hS F A V) α) =
      homRestr (smallEtaleStructurePresheaf B S hS F hF) M N
        (openChartInclusion B S hS F A' (chartSchemeMap k ⁻¹ᵁ V))
        (homRestr (smallEtaleStructurePresheaf B S hS F hF) M N k α) :=
  Stacks.PresheafOfModules.homRestr_of_comm_sq _ M N k _ _ _
    (openChartRestrict_comp_openChartInclusion B S hS F k V) α

/-- **The relocalization of `α` along a morphism of charts, read over an open of the smaller
chart's scheme lying over a Zariski open of the larger one.**  It is the relocalization of the
component of `α` over that Zariski open. -/
theorem homRestr_openChartInclusion_comp {A A' : SmallEtale B S hS F} (k : A' ⟶ A)
    (V : (chartScheme A).Opens) {U : (chartScheme A').Opens}
    (hU : U ≤ chartSchemeMap k ⁻¹ᵁ V)
    (α : (restrFun (smallEtaleStructurePresheaf B S hS F hF) A).obj M ⟶
      (restrFun (smallEtaleStructurePresheaf B S hS F hF) A).obj N) :
    homRestr (smallEtaleStructurePresheaf B S hS F hF) M N
        (openChartInclusion B S hS F A' U ≫ k) α =
      homRestr (smallEtaleStructurePresheaf B S hS F hF) M N
        (openChartHomOfLE B S hS F A' hU ≫ openChartRestrict B S hS F k V)
        (homRestr (smallEtaleStructurePresheaf B S hS F hF) M N
          (openChartInclusion B S hS F A V) α) :=
  (homRestr_comp (smallEtaleStructurePresheaf B S hS F hF) M N
      (openChartInclusion B S hS F A' U) k α).trans
    (Stacks.PresheafOfModules.homRestr_of_comm_sq _ M N k _ _ _
      (openChartHomOfLE_comp_openChartRestrict_comp_openChartInclusion B S hS F k V hU) α).symm

/-! ### Equality of relocalizations is local on the chart's scheme -/

/-- **Two morphisms `M|_A ⟶ N|_A` agreeing after relocalization along every arrow of a covering
sieve of `A` are equal.** -/
theorem homRestr_ext (hN : Presheaf.IsSheaf (SmallEtale.topology B S hS F) N.presheaf)
    {A : SmallEtale B S hS F} {T : Sieve A} (hT : T ∈ SmallEtale.topology B S hS F A)
    (β₁ β₂ : (restrFun (smallEtaleStructurePresheaf B S hS F hF) A).obj M ⟶
      (restrFun (smallEtaleStructurePresheaf B S hS F hF) A).obj N)
    (h : ∀ ⦃Z : SmallEtale B S hS F⦄ (f : Z ⟶ A), T f →
      homRestr (smallEtaleStructurePresheaf B S hS F hF) M N f β₁ =
        homRestr (smallEtaleStructurePresheaf B S hS F hF) M N f β₂) :
    β₁ = β₂ := by
  have hsh := internalHom_isSheaf_forget (smallEtaleStructurePresheaf B S hS F hF) M N hN
  rw [isSheaf_iff_isSheaf_of_type] at hsh
  exact (hsh T hT).isSeparatedFor.ext (t₁ := β₁) (t₂ := β₂) fun Z f hf ↦
    (internalHomForget_map_apply _ M N f β₁).trans
      ((h f hf).trans (internalHomForget_map_apply _ M N f β₂).symm)

/-- **The equality of the two relocalizations of `α` along a pair of chart morphisms is local on
the smaller chart's scheme.**  If the two relocalizations agree after being relocalized to the
charts cut out by the members of an open cover of `chartScheme A'`, they are equal. -/
theorem homRestr_eq_of_forall_openChart
    (hN : Presheaf.IsSheaf (SmallEtale.topology B S hS F) N.presheaf)
    {A A' : SmallEtale B S hS F} (p q : A' ⟶ A) {ι : Type*}
    (Ω : ι → (chartScheme A').Opens) (hΩ : ⨆ i, Ω i = ⊤)
    (α : (restrFun (smallEtaleStructurePresheaf B S hS F hF) A).obj M ⟶
      (restrFun (smallEtaleStructurePresheaf B S hS F hF) A).obj N)
    (h : ∀ i, homRestr (smallEtaleStructurePresheaf B S hS F hF) M N
          (openChartInclusion B S hS F A' (Ω i) ≫ p) α =
        homRestr (smallEtaleStructurePresheaf B S hS F hF) M N
          (openChartInclusion B S hS F A' (Ω i) ≫ q) α) :
    homRestr (smallEtaleStructurePresheaf B S hS F hF) M N p α =
      homRestr (smallEtaleStructurePresheaf B S hS F hF) M N q α := by
  refine homRestr_ext B S hS F hF M N hN
    (ofArrows_openChartInclusion_mem_topology B S hS F A' Ω hΩ) _ _ ?_
  rintro Z f ⟨Y, g, j, ⟨i⟩, hfac⟩
  subst hfac
  simp only [homRestr_comp] at h ⊢
  rw [h i]

/-- **The equality of the two relocalizations of `α` along a pair of chart morphisms, reduced to
the components of `α` over Zariski opens of the larger chart's scheme.**

Let `Ω` be an open cover of `chartScheme A'` such that `Ω i` lies over a Zariski open `V i` of
`chartScheme A` under `p` and over `V' i` under `q`.  Then `homRestr … p α = homRestr … q α` as
soon as, for each `i`, the relocalizations of the components of `α` over `V i` and over `V' i` to
the chart cut out by `Ω i` agree. -/
theorem homRestr_eq_of_forall_openChart_le
    (hN : Presheaf.IsSheaf (SmallEtale.topology B S hS F) N.presheaf)
    {A A' : SmallEtale B S hS F} (p q : A' ⟶ A) {ι : Type*}
    (Ω : ι → (chartScheme A').Opens) (hΩ : ⨆ i, Ω i = ⊤)
    (V V' : ι → (chartScheme A).Opens)
    (hp : ∀ i, Ω i ≤ chartSchemeMap p ⁻¹ᵁ V i)
    (hq : ∀ i, Ω i ≤ chartSchemeMap q ⁻¹ᵁ V' i)
    (α : (restrFun (smallEtaleStructurePresheaf B S hS F hF) A).obj M ⟶
      (restrFun (smallEtaleStructurePresheaf B S hS F hF) A).obj N)
    (h : ∀ i, homRestr (smallEtaleStructurePresheaf B S hS F hF) M N
            (openChartHomOfLE B S hS F A' (hp i) ≫ openChartRestrict B S hS F p (V i))
            (homRestr (smallEtaleStructurePresheaf B S hS F hF) M N
              (openChartInclusion B S hS F A (V i)) α) =
          homRestr (smallEtaleStructurePresheaf B S hS F hF) M N
            (openChartHomOfLE B S hS F A' (hq i) ≫ openChartRestrict B S hS F q (V' i))
            (homRestr (smallEtaleStructurePresheaf B S hS F hF) M N
              (openChartInclusion B S hS F A (V' i)) α)) :
    homRestr (smallEtaleStructurePresheaf B S hS F hF) M N p α =
      homRestr (smallEtaleStructurePresheaf B S hS F hF) M N q α :=
  homRestr_eq_of_forall_openChart B S hS F hF M N hN p q Ω hΩ α fun i ↦
    (homRestr_openChartInclusion_comp B S hS F hF M N p (V i) (hp i) α).trans
      ((h i).trans
        (homRestr_openChartInclusion_comp B S hS F hF M N q (V' i) (hq i) α).symm)

/-- **The one-chart gluing with its compatibility condition read at the opens of the kernel
pair's scheme.**  Let `W` be an étale chart covering the final object of the small étale site and
let `α : M|_W ⟶ N|_W`.  Cover `chartScheme (W ⨯ W)` by opens `Ω i`, each lying over a Zariski
open `V i` of `chartScheme W` under the first projection and over `V' i` under the second.  If
the relocalizations to the chart cut out by `Ω i` of the components of `α` over `V i` and over
`V' i` agree for every `i`, then `α` is the restriction of a unique morphism `M ⟶ N`. -/
theorem existsUnique_hom_of_single_chart_prod_openChart
    (hN : Presheaf.IsSheaf (SmallEtale.topology B S hS F) N.presheaf)
    (W : SmallEtale B S hS F)
    (hW : (SmallEtale.topology B S hS F).CoversTop (fun _ : Unit => W))
    (α : (restrFun (smallEtaleStructurePresheaf B S hS F hF) W).obj M ⟶
      (restrFun (smallEtaleStructurePresheaf B S hS F hF) W).obj N)
    {ι : Type*} (Ω : ι → (chartScheme (W ⨯ W : SmallEtale B S hS F)).Opens)
    (hΩ : ⨆ i, Ω i = ⊤) (V V' : ι → (chartScheme W).Opens)
    (hp : ∀ i, Ω i ≤ chartSchemeMap (Limits.prod.fst : (W ⨯ W : SmallEtale B S hS F) ⟶ W) ⁻¹ᵁ V i)
    (hq : ∀ i, Ω i ≤
      chartSchemeMap (Limits.prod.snd : (W ⨯ W : SmallEtale B S hS F) ⟶ W) ⁻¹ᵁ V' i)
    (h : ∀ i, homRestr (smallEtaleStructurePresheaf B S hS F hF) M N
            (openChartHomOfLE B S hS F (W ⨯ W) (hp i) ≫
              openChartRestrict B S hS F Limits.prod.fst (V i))
            (homRestr (smallEtaleStructurePresheaf B S hS F hF) M N
              (openChartInclusion B S hS F W (V i)) α) =
          homRestr (smallEtaleStructurePresheaf B S hS F hF) M N
            (openChartHomOfLE B S hS F (W ⨯ W) (hq i) ≫
              openChartRestrict B S hS F Limits.prod.snd (V' i))
            (homRestr (smallEtaleStructurePresheaf B S hS F hF) M N
              (openChartInclusion B S hS F W (V' i)) α)) :
    ∃! φ : M ⟶ N, (restrFun (smallEtaleStructurePresheaf B S hS F hF) W).map φ = α :=
  existsUnique_hom_of_single_chart_prod B S hS F hF M N hN W hW α
    (homRestr_eq_of_forall_openChart_le B S hS F hF M N hN Limits.prod.fst Limits.prod.snd
      Ω hΩ V V' hp hq α h)

/-! ### The étale base-change comparison on sections -/

/-- **The étale base-change comparison for the chart restriction of a quasi-coherent
`𝒪_F`-module.**  Let `k : A' ⟶ A` be a morphism of étale charts, let `V` be an affine open of
`chartScheme A` and let `U` be an affine open of `chartScheme A'` lying over `V`.  Then the
sections of a quasi-coherent `𝒪_F`-module over the chart cut out by `U` are the base change,
along the induced map of rings of sections, of its sections over the chart cut out by `V`. -/
theorem bijective_sectionsBaseChange_openChartRestrict (G : Modules.{u, u} B S hS F hF)
    (hG : G.IsQuasicoherentOnSite) {A A' : SmallEtale B S hS F} (k : A' ⟶ A)
    {V : (chartScheme A).Opens} {U : (chartScheme A').Opens}
    (hV : IsAffineOpen V) (hU : IsAffineOpen U) (hUV : U ≤ chartSchemeMap k ⁻¹ᵁ V) :
    Function.Bijective (sectionsBaseChange G
      (openChartHomOfLE B S hS F A' hUV ≫ openChartRestrict B S hS F k V)) :=
  bijective_sectionsBaseChange_of_isQuasicoherentOnSite B S hS F hF G hG
    (show IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj
      (openChart B S hS F A V)) from hV)
    (show IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj
      (openChart B S hS F A' U)) from hU) _

/-! ### Compatibility with the chartwise sheaf of ideals -/

section IdealSheafData

variable (X : AlgebraicSpaces B S hS)
  (I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
  (hI : IsCartesianOnAffineCharts I.toSheafOfModules)

/-- **The open over which the chartwise sheaf of ideals is trivial is pulled back along a
morphism of charts.**  The complement of the support of
`AlgebraicGeometry.Space.idealSheafDataOfChart` at the smaller chart is the preimage of the one
at the larger chart. -/
theorem support_compl_idealSheafDataOfChart {A A' : SmallEtale B S hS X.1} (m : A' ⟶ A) :
    ((idealSheafDataOfChart B S hS X I hI A').support.compl : (chartScheme A').Opens) =
      chartSchemeMap m ⁻¹ᵁ
        ((idealSheafDataOfChart B S hS X I hI A).support.compl : (chartScheme A).Opens) := by
  rw [← comap_idealSheafDataOfChart B S hS X I hI m, Scheme.IdealSheafData.support_comap]
  rfl

/-- **A Zariski open of a chart's scheme off the support of the chartwise sheaf of ideals lies
over the complement of the support at any larger chart.** -/
theorem le_preimage_support_compl_idealSheafDataOfChart {A A' : SmallEtale B S hS X.1}
    (m : A' ⟶ A) {U : (chartScheme A').Opens}
    (hU : U ≤ ((idealSheafDataOfChart B S hS X I hI A').support.compl :
      (chartScheme A').Opens)) :
    U ≤ chartSchemeMap m ⁻¹ᵁ
      ((idealSheafDataOfChart B S hS X I hI A).support.compl : (chartScheme A).Opens) :=
  hU.trans (support_compl_idealSheafDataOfChart B S hS X I hI m).le

end IdealSheafData

end AlgebraicGeometry.Space

end
