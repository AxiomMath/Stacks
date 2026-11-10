module

public import StacksFrontier.AlgebraicGeometry.Size.FiniteTypeCount
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeOnSiteAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!
# A small dense family of affine charts above an affine surjective étale chart

Let `F` be a presheaf on the big fppf site of a scheme `S` and let `U₀` be an étale chart of
`F` whose underlying scheme is affine and which covers the final object of the small étale site
(for instance an affine chart with surjective structure morphism of an algebraic space).  Every
étale chart of `F` is covered by charts admitting a morphism of charts to `U₀`, and these by the
charts cut out by their affine opens.  Such an affine chart is an affine scheme étale over `U₀`, so
up to isomorphism it is one of the affine `U₀`-schemes of finite type of
`AlgebraicGeometry.exists_index_affineFiniteTypeOver`.

So the small étale site of `F` has a dense family of affine charts indexed by a type of
cardinality at most `ℵ₀ * 2 ^ max ℵ₀ #Γ(U₀, ⊤)`, each of whose members is of finite type over
`U₀`.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtale.ofEtaleMap`: the chart of an étale morphism to a chart.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.exists_hom_of_comp_eq`: a scheme morphism between charts
  above `U₀` compatible with the maps to `U₀` is a morphism of charts.
* `AlgebraicGeometry.Space.SmallEtale.isCoverDense_of_coversTop`: a family meeting every affine
  chart above a covering chart is dense.
* `AlgebraicGeometry.Space.SmallEtale.exists_denseAffineFamily`: the dense family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The chart of an étale morphism to a chart**: an object `W` of the site with an étale
morphism `w : W ⟶ U₀` to the object underlying a chart `U₀` is a chart, through `U₀`. -/
def SmallEtale.ofEtaleMap (U₀ : SmallEtale B S hS F) {W : BigFppfOver B S hS}
    (w : W ⟶ U₀.obj.left) (hw : Etale ((BigFppfOver.toScheme B S hS).map w)) :
    SmallEtale B S hS F :=
  ⟨CostructuredArrow.mk (yoneda.map w ≫ U₀.obj.hom),
    etale_comp_of_scheme B S hS w U₀.obj.hom hw U₀.property⟩

/-- The morphism of charts from the chart of an étale morphism to a chart to that chart. -/
def SmallEtale.ofEtaleMapHom (U₀ : SmallEtale B S hS F) {W : BigFppfOver B S hS}
    (w : W ⟶ U₀.obj.left) (hw : Etale ((BigFppfOver.toScheme B S hS).map w)) :
    SmallEtale.ofEtaleMap U₀ w hw ⟶ U₀ :=
  ObjectProperty.homMk (CostructuredArrow.homMk w rfl)

/-- A morphism of charts `W ⟶ W'` is determined by the induced morphism of underlying schemes. -/
theorem SmallEtale.chartSchemeMap_injective {W W' : SmallEtale B S hS F} :
    Function.Injective (chartSchemeMap (U := W') (V := W)) := fun _ _ h =>
  (SmallEtale.toOver B S hS F).map_injective ((BigFppfOver.toScheme B S hS).map_injective h)

/-- **A morphism of charts from a scheme isomorphism compatible with maps to a chart.**  If
`W` and `W'` are charts with morphisms of charts `β, β'` to `U₀`, a scheme morphism `e` between
their underlying schemes with `e ≫ β' = β` on schemes is a morphism of charts. -/
theorem SmallEtale.exists_hom_of_comp_eq {U₀ W W' : SmallEtale B S hS F} (β : W ⟶ U₀)
    (β' : W' ⟶ U₀) (e : chartScheme W ⟶ chartScheme W')
    (he : e ≫ chartSchemeMap β' = chartSchemeMap β) :
    ∃ m : W ⟶ W', chartSchemeMap m = e := by
  have hw : ∀ V : SmallEtale B S hS F, ∀ γ : V ⟶ U₀,
      chartSchemeMap γ ≫ B.inclusion.map U₀.obj.left.hom = B.inclusion.map V.obj.left.hom ∧
      yoneda.map ((SmallEtale.toOver B S hS F).map γ) ≫ U₀.obj.hom = V.obj.hom := fun V γ => by
    refine ⟨?_, CostructuredArrow.w ((SmallEtale.inclusion B S hS F).map γ)⟩
    have := congrArg B.inclusion.map (Over.w ((SmallEtale.toOver B S hS F).map γ))
    rwa [Functor.map_comp] at this
  have hcomp : e ≫ B.inclusion.map W'.obj.left.hom = B.inclusion.map W.obj.left.hom := by
    rw [← (hw W' β').1, ← Category.assoc, he, (hw W β).1]
  obtain ⟨m₀, hm₀⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS e hcomp
  have hβ : m₀ ≫ ((SmallEtale.toOver B S hS F).map β') = (SmallEtale.toOver B S hS F).map β :=
    (BigFppfOver.toScheme B S hS).map_injective (by rwa [Functor.map_comp, hm₀])
  refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk m₀ ?_), hm₀⟩
  change yoneda.map m₀ ≫ W'.obj.hom = W.obj.hom
  rw [← (hw W' β').2, ← Category.assoc, ← Functor.map_comp, hβ, (hw W β).2]

/-- **A chart with a morphism to `U₀` is covered by affine charts isomorphic to members of a
family `c`**, as soon as every affine chart with a morphism to `U₀` is isomorphic to a member of
`c`: the charts cut out by its affine opens cover it, and each maps to `U₀`. -/
theorem SmallEtale.coverByImage_mem_of_hom {ι : Type*} (c : ι → SmallEtale B S hS F)
    (U₀ : SmallEtale B S hS F)
    (hc : ∀ (W : SmallEtale B S hS F), (W ⟶ U₀) → IsAffine (chartScheme W) →
      ∃ i, Nonempty (W ≅ c i))
    (V : SmallEtale B S hS F) (β : V ⟶ U₀) :
    Sieve.coverByImage (inducedFunctor c) V ∈ SmallEtale.topology B S hS F V := by
  refine (SmallEtale.topology B S hS F).superset_covering ?_
    (SmallEtale.ofArrows_openChart_affineOpens_mem B S hS F V)
  rintro W f ⟨Y, h, g, ⟨O⟩, rfl⟩
  obtain ⟨i, ⟨e⟩⟩ := hc _ (openChartInclusion B S hS F V O.down.1 ≫ β)
    (isAffine_chartScheme_openChart B S hS F V O.down)
  exact ⟨{ obj := i, lift := h ≫ e.hom, map := e.inv ≫ openChartInclusion B S hS F V O.down.1 }⟩

/-- **A family meeting every affine chart above a covering chart is dense.**  If the chart `U₀`
covers the final object of the small étale site of `F`, and every affine chart with a morphism to
`U₀` is isomorphic to a member of `c`, then `c` is a dense family of objects of the small étale
site: every chart is covered by charts mapping to `U₀`, and these by charts isomorphic to members
of `c`.  A chart whose structure morphism is surjective covers the final object
(`AlgebraicGeometry.Space.SmallEtale.coversTop_of_isSurjective`). -/
theorem SmallEtale.isCoverDense_of_coversTop {ι : Type*}
    (c : ι → SmallEtale B S hS F) (U₀ : SmallEtale B S hS F)
    (hcov : (SmallEtale.topology B S hS F).CoversTop (fun _ : PUnit.{u + 2} => U₀))
    (hc : ∀ (W : SmallEtale B S hS F), (W ⟶ U₀) → IsAffine (chartScheme W) →
      ∃ i, Nonempty (W ≅ c i)) :
    (inducedFunctor c).IsCoverDense (SmallEtale.topology B S hS F) where
  is_cover W := by
    refine (SmallEtale.topology B S hS F).transitive (hcov W) _ (fun Z f hf => ?_)
    obtain ⟨_, ⟨β⟩⟩ := hf
    refine (SmallEtale.topology B S hS F).superset_covering ?_
      (SmallEtale.coverByImage_mem_of_hom c U₀ hc Z β)
    rintro Y g ⟨⟨i, lift, map, fac⟩⟩
    exact ⟨{ obj := i, lift := lift, map := map ≫ f }⟩

/-- **A small dense family of affine charts above an affine covering chart.**  If `U₀` is an
étale chart of `F` with affine underlying scheme which covers the final object of the small étale
site, the small étale site of `F` has a dense family of affine charts, each of finite type over
`U₀`, indexed by a type of cardinality at most `ℵ₀ * 2 ^ max ℵ₀ #Γ(U₀, ⊤)`. -/
theorem SmallEtale.exists_denseAffineFamily
    (U₀ : SmallEtale B S hS F) [IsAffine (chartScheme U₀)]
    (hcov : (SmallEtale.topology B S hS F).CoversTop (fun _ : PUnit.{u + 2} => U₀)) :
    ∃ (ι : Type u) (c : ι → SmallEtale B S hS F),
      (inducedFunctor c).IsCoverDense (SmallEtale.topology B S hS F) ∧
      #ι ≤ ℵ₀ * 2 ^ max ℵ₀ #Γ(chartScheme U₀, ⊤) ∧
      ∀ i, IsAffine (chartScheme (c i)) ∧
        ∃ f : chartScheme (c i) ⟶ chartScheme U₀, LocallyOfFiniteType f := by
  obtain ⟨I, V, hI, hV⟩ := exists_index_affineFiniteTypeOver (chartScheme U₀)
  let ι := {x : I // B.Contains (V x).obj ∧ Etale (V x).hom}
  let W : ι → BigFppfOver B S hS := fun x =>
    siteObject B S hS x.2.1 ((V x.1).hom ≫ B.inclusion.map U₀.obj.left.hom)
  have hw : ∀ x : ι, ∃ w : W x ⟶ U₀.obj.left,
      (BigFppfOver.toScheme B S hS).map w = (V x.1).hom := fun x =>
    BigFppfOver.exists_hom_of_comp_eq B S hS (X := W x) (Y := U₀.obj.left) (V x.1).hom rfl
  choose w hw using hw
  have hetW : ∀ x : ι, Etale ((BigFppfOver.toScheme B S hS).map (w x)) := fun x => by
    rw [hw x]
    exact x.2.2
  let c : ι → SmallEtale B S hS F := fun x => SmallEtale.ofEtaleMap U₀ (w x) (hetW x)
  refine ⟨ι, c, ?_, (Cardinal.mk_subtype_le _).trans hI, fun x => ⟨(V x.1).isAffine,
    (V x.1).hom, (V x.1).locallyOfFiniteType⟩⟩
  refine SmallEtale.isCoverDense_of_coversTop c U₀ hcov (fun W' β hW' => ?_)
  have hβet : Etale (chartSchemeMap β) := etale_toScheme_toOver_map B S hS F β
  obtain ⟨x, e, he⟩ := hV ⟨chartScheme W', chartSchemeMap β, hW', inferInstance⟩
  have hcont : B.Contains (V x).obj :=
    lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact e.hom) W'.obj.left.left.property
  have het : Etale (V x).hom := by
    rw [← he]
    infer_instance
  let x' : ι := ⟨x, hcont, het⟩
  have hβ' : chartSchemeMap (SmallEtale.ofEtaleMapHom U₀ (w x') (hetW x')) =
      (V x).hom := hw x'
  obtain ⟨m, hm⟩ := SmallEtale.exists_hom_of_comp_eq β
    (SmallEtale.ofEtaleMapHom U₀ (w x') (hetW x')) e.inv
    ((congrArg (e.inv ≫ ·) hβ').trans (by rw [← he, Iso.inv_hom_id_assoc]))
  obtain ⟨m', hm'⟩ := SmallEtale.exists_hom_of_comp_eq
    (SmallEtale.ofEtaleMapHom U₀ (w x') (hetW x')) β e.hom (he.trans hβ'.symm)
  refine ⟨x', ⟨⟨m, m', ?_, ?_⟩⟩⟩ <;> apply SmallEtale.chartSchemeMap_injective <;>
    simp only [chartSchemeMap, Functor.map_comp] at hm hm' ⊢ <;> rw [hm, hm']
  exacts [e.inv_hom_id, e.hom_inv_id]

end AlgebraicGeometry.Space
