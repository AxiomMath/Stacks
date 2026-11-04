module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.SpecSliceChart
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.ModelBiduality
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The model of a locally Noetherian algebraic space is covered by full duality charts

Let `F` be a locally Noetherian algebraic space. For an object `W` of the equi-universe model of
its small étale site and an affine open `A` of the scheme `X_W` of its chart, the chart
restricted along the open immersion `Spec Γ(X_W, A) ⟶ X_W` is an étale chart whose scheme is
literally `Spec Γ(X_W, A)`. These charts cover the model, and for a dualizing complex `K` on `F`
(Stacks 0E4Z) the slice of the model at each of them carries a full duality chart for `K`
(Stacks 0A89 read through Stacks 0E50).

## Main definitions

* `AlgebraicGeometry.Space.chartOfOpenImmersion`: an étale chart restricted along an open
  immersion into its source.
* `AlgebraicGeometry.Space.SpecChartIndex`, `AlgebraicGeometry.Space.specChartObj`: the covering
  family.
* `AlgebraicGeometry.Space.specFullChart`: the full duality chart of `K` at each member.

## Main results

* `AlgebraicGeometry.Space.specChartObj_coversTop`.

## References

* [Stacks Project, Tag 0E51](https://stacks.math.columbia.edu/tag/0E51)
* [Stacks Project, Tag 0E50](https://stacks.math.columbia.edu/tag/0E50)
* [Stacks Project, Tag 0E4Z](https://stacks.math.columbia.edu/tag/0E4Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### Restricting an étale chart along an open immersion -/

/-- An étale chart of `F` restricted along an open immersion `j : Z ⟶ X_U` into the scheme of its
source; the scheme of the new chart is `Z` itself. -/
def chartOfOpenImmersion (U : SmallEtale B S hS F) {Z : Scheme.{u}}
    (j : Z ⟶ (BigFppfOver.toScheme B S hS).obj U.1.left)
    [_root_.AlgebraicGeometry.IsOpenImmersion j] :
    SmallEtale B S hS F := by
  let hZ : B.Contains Z := Scheme.size_lt_of_isOpenImmersion j U.1.left.left.property
  let i : B.obj hZ ⟶ U.1.left.left := B.inclusion.preimage (X := B.obj hZ) (Y := U.1.left.left) j
  let W : BigFppfOver B S hS := Over.mk (i ≫ U.1.left.hom)
  let g : W ⟶ U.1.left := Over.homMk i (by simp [W])
  refine ⟨CostructuredArrow.mk (yoneda.map g ≫ U.1.hom), ?_⟩
  refine etale_comp_of_scheme B S hS g U.1.hom ?_ U.2
  rw [show (BigFppfOver.toScheme B S hS).map g = j from B.inclusion.map_preimage _]
  infer_instance

/-- The inclusion of a chart restricted along an open immersion into the chart. -/
def chartOfOpenImmersionHom (U : SmallEtale B S hS F) {Z : Scheme.{u}}
    (j : Z ⟶ (BigFppfOver.toScheme B S hS).obj U.1.left)
    [_root_.AlgebraicGeometry.IsOpenImmersion j] :
    chartOfOpenImmersion B S hS F U j ⟶ U :=
  ObjectProperty.homMk (CostructuredArrow.homMk
    (Over.homMk (B.inclusion.preimage j)) (by rfl))

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.chartOfOpenImmersionHom` is the
open immersion. -/
theorem chartOfOpenImmersionHom_toScheme (U : SmallEtale B S hS F) {Z : Scheme.{u}}
    (j : Z ⟶ (BigFppfOver.toScheme B S hS).obj U.1.left)
    [_root_.AlgebraicGeometry.IsOpenImmersion j] :
    (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map
      (chartOfOpenImmersionHom B S hS F U j) = j :=
  B.inclusion.map_preimage _

/-! ### The covering family -/

/-- The indices of the covering family: an object of the model together with an affine open of
the scheme of its chart. -/
def SpecChartIndex : Type u :=
  Σ W : SmallEtaleModel B S hS F,
    {A : ((BigFppfOver.toScheme B S hS).obj (chartBase B S hS F W)).Opens // IsAffineOpen A}

variable {B S hS F} in
/-- The ring of the affine open of an index. -/
abbrev SpecChartIndex.ring (k : SpecChartIndex B S hS F) : CommRingCat.{u} :=
  Γ((BigFppfOver.toScheme B S hS).obj (chartBase B S hS F k.1), k.2.1)

/-- The étale chart with scheme `Spec Γ(X_W, A)` of an index. -/
def specChart (k : SpecChartIndex B S hS F) : SmallEtale B S hS F :=
  chartOfOpenImmersion B S hS F (chartObj B S hS F k.1) k.2.2.fromSpec

/-- The object of the model of an index. -/
def specChartObj (k : SpecChartIndex B S hS F) : SmallEtaleModel B S hS F :=
  (smallEtaleModelEquivalence B S hS F).inverse.obj (specChart B S hS F k)

/-- The chart underlying the object of the model of an index is the étale chart of the index. -/
def specChartIso (k : SpecChartIndex B S hS F) :
    chartObj B S hS F (specChartObj B S hS F k) ≅ specChart B S hS F k :=
  (smallEtaleModelEquivalence B S hS F).counitIso.app _

/-- The scheme of the étale chart of an index is `Spec` of the ring of the index. -/
theorem reprScheme_specChart (k : SpecChartIndex B S hS F) :
    reprScheme B S hS (etaleChartBase B S hS F (specChart B S hS F k)) = Spec k.ring :=
  rfl

/-- A family of objects of the model covers it as soon as the sieves they generate, pushed to the
small étale site, cover. -/
private theorem model_coversTop_of_functorPushforward_mem (hF : IsAlgebraicSpace B S hS F)
    {ι : Type*} (X : ι → SmallEtaleModel B S hS F)
    (h : ∀ W, (Sieve.ofObjects X W).functorPushforward (smallEtaleModelEquivalence B S hS F).functor
      ∈ SmallEtale.topology B S hS F ((smallEtaleModelEquivalence B S hS F).functor.obj W)) :
    (smallEtaleModelRingedSite B S hS F hF).J.CoversTop
      (fun i => (X i : (smallEtaleModelRingedSite B S hS F hF).C)) := by
  intro W
  change Sieve.ofObjects _ W ∈ smallEtaleModelTopology B S hS F W
  exact (Functor.functorPushforward_mem_iff (G := (smallEtaleModelEquivalence B S hS F).functor)
    (smallEtaleModelTopology B S hS F) (SmallEtale.topology B S hS F)).1 (h W)

/-- Every point of an étale chart lies in the image of the restriction of the chart to any affine
open containing it. -/
private theorem exists_chartOfOpenImmersionHom_range (V : SmallEtale B S hS F)
    {A : ((BigFppfOver.toScheme B S hS).obj V.1.left).Opens} (hA : IsAffineOpen A)
    {z : (BigFppfOver.toScheme B S hS).obj V.1.left} (hz : z ∈ A) :
    ∃ g : chartOfOpenImmersion B S hS F V hA.fromSpec ⟶ V,
      ∃ z', (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map g) z' = z := by
  obtain ⟨z', hz'⟩ : z ∈ Set.range hA.fromSpec := by rwa [hA.range_fromSpec]
  refine ⟨chartOfOpenImmersionHom B S hS F V hA.fromSpec, z', ?_⟩
  rwa [show (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map
      (chartOfOpenImmersionHom B S hS F V hA.fromSpec)) = hA.fromSpec
    from chartOfOpenImmersionHom_toScheme B S hS F V hA.fromSpec]

/-- **The étale charts with affine schemes `Spec Γ(X_W, A)` cover the model of the small étale
site.** -/
theorem specChartObj_coversTop (hF : IsAlgebraicSpace B S hS F) :
    (smallEtaleModelRingedSite B S hS F hF).J.CoversTop
      (fun k : SpecChartIndex B S hS F =>
        (specChartObj B S hS F k : (smallEtaleModelRingedSite B S hS F hF).C)) := by
  refine model_coversTop_of_functorPushforward_mem B S hS F hF _ fun W => ?_
  let e := smallEtaleModelEquivalence B S hS F
  apply smallEtale_sieve_of_pointwise_covering B S hS F (e.functor.obj W)
  intro z
  obtain ⟨A, hA, hzA, -⟩ := exists_isAffineOpen_mem_and_subset (x := z)
    (U := (⊤ : ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj
      (e.functor.obj W))).Opens)) (by simp)
  let k : SpecChartIndex B S hS F := ⟨W, A, hA⟩
  obtain ⟨g, hg⟩ := exists_chartOfOpenImmersionHom_range B S hS F (e.functor.obj W) hA hzA
  exact ⟨specChart B S hS F k, g, ⟨e.inverse.obj (specChart B S hS F k),
    e.inverse.map g ≫ e.unitInv.app W, e.counitInv.app _, ⟨k, ⟨𝟙 _⟩⟩,
    eq_counitInv_comp_functor_map e g⟩, hg⟩

/-- **A covering of the small étale site gives a covering of its model.** -/
theorem modelCoversTop_of_coversTop (hF : IsAlgebraicSpace B S hS F) {ι : Type*}
    (U' : ι → SmallEtale B S hS F) (h : (SmallEtale.topology B S hS F).CoversTop U') :
    (smallEtaleModelRingedSite B S hS F hF).J.CoversTop
      (fun i => ((smallEtaleModelEquivalence B S hS F).inverse.obj (U' i) :
        (smallEtaleModelRingedSite B S hS F hF).C)) := by
  refine model_coversTop_of_functorPushforward_mem B S hS F hF _ fun W => ?_
  let e := smallEtaleModelEquivalence B S hS F
  refine (SmallEtale.topology B S hS F).superset_covering ?_ (h (e.functor.obj W))
  rintro Y g ⟨i, ⟨q⟩⟩
  exact ⟨e.inverse.obj Y, e.inverse.map g ≫ e.unitInv.app W, e.counitInv.app Y,
    ⟨i, ⟨e.inverse.map q⟩⟩, eq_counitInv_comp_functor_map e g⟩

/-- **On a quasi-compact algebraic space one chart with scheme `Spec R` covers the model**: the
affine surjective étale chart of Stacks 03H6, read as the object `Spec Γ(X_W, ⊤)` of an index
whose open is the whole affine scheme. -/
theorem exists_specChartIndex_coversTop (hF : IsAlgebraicSpace B S hS F)
    (hqc : IsQuasiCompactSpace B S hS F) :
    ∃ k : SpecChartIndex B S hS F, (smallEtaleModelRingedSite B S hS F hF).J.CoversTop
      (fun _ : Unit => (specChartObj B S hS F k : (smallEtaleModelRingedSite B S hS F hF).C)) := by
  obtain ⟨U, a, hUaff, hasurj, haet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS F hF).mp hqc
  have hid : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (𝟙 U)) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
      (@Etale.{u} : MorphismProperty Scheme.{u}) (𝟙 U)).2
      (by rw [CategoryTheory.Functor.map_id]; infer_instance)
  have haet' : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a := by
    simpa only [CategoryTheory.Functor.map_id, Category.id_comp] using haet U (yoneda.map (𝟙 U)) hid
  let Uc : SmallEtale B S hS F := ⟨CostructuredArrow.mk a, haet'⟩
  have hcovU : (SmallEtale.topology B S hS F).CoversTop (fun _ : PUnit.{u + 2} => Uc) :=
    SmallEtale.coversTop_of_isSurjective B S hS F hF Uc
      ((presheafSurjective_iff_isSurjective_yoneda B S hS F hF U a).1 hasurj)
  let e := smallEtaleModelEquivalence B S hS F
  let W0 := e.inverse.obj Uc
  let ε := (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS F).map (e.counit.app Uc))
  have : IsIso ε := inferInstance
  have : _root_.AlgebraicGeometry.IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS F).obj ((𝟭 (SmallEtale B S hS F)).obj Uc))) := hUaff
  have hW0 : _root_.AlgebraicGeometry.IsAffine
      ((BigFppfOver.toScheme B S hS).obj (chartBase B S hS F W0)) := IsAffine.of_isIso ε
  have hk : IsAffineOpen (⊤ : ((BigFppfOver.toScheme B S hS).obj (chartBase B S hS F W0)).Opens) :=
    isAffineOpen_top _
  let k : SpecChartIndex B S hS F := ⟨W0, ⊤, hk⟩
  refine ⟨k, ?_⟩
  have h1 : Sieve.ofObjects (fun _ : Unit => specChart B S hS F k) (e.functor.obj W0) ∈
      SmallEtale.topology B S hS F (e.functor.obj W0) := by
    apply smallEtale_sieve_of_pointwise_covering B S hS F (e.functor.obj W0)
    intro z
    obtain ⟨g, hg⟩ := exists_chartOfOpenImmersionHom_range B S hS F (e.functor.obj W0) hk
      (Set.mem_univ z)
    exact ⟨specChart B S hS F k, g, ⟨(), ⟨𝟙 _⟩⟩, hg⟩
  have h2 : Sieve.ofObjects (fun _ : Unit => specChart B S hS F k) Uc ∈
      SmallEtale.topology B S hS F Uc :=
    (SmallEtale.topology B S hS F).superset_covering (fun _ _ hq => hq)
      ((SmallEtale.topology B S hS F).pullback_stable (e.counitInv.app Uc) h1)
  have hcov : (SmallEtale.topology B S hS F).CoversTop (fun _ : Unit => specChart B S hS F k) := by
    intro X
    refine (SmallEtale.topology B S hS F).transitive (hcovU X) _ ?_
    intro Z h hh
    obtain ⟨-, ⟨p⟩⟩ := (Sieve.mem_ofObjects_iff _ h).1 hh
    refine (SmallEtale.topology B S hS F).superset_covering ?_
      ((SmallEtale.topology B S hS F).pullback_stable p h2)
    intro Y q hq
    exact hq
  exact modelCoversTop_of_coversTop B S hS F hF _ hcov

/-! ### The full duality charts -/

variable (hF : IsAlgebraicSpace B S hS F)
  (hN : HasEtaleLocalProperty B S hS F (fun T : Scheme.{u} => IsLocallyNoetherian T))

include hF hN in
/-- The ring of an index is Noetherian. -/
theorem SpecChartIndex.isNoetherianRing (k : SpecChartIndex B S hS F) :
    IsNoetherianRing k.ring :=
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (chartBase B S hS F k.1)) :=
    isLocallyNoetherian_of_etaleChart B S hS F hF hN _ _ (chartObj B S hS F k.1).property
  IsLocallyNoetherian.component_noetherian ⟨k.2.1, k.2.2⟩

/-- The base scheme of the chart of an index is affine. -/
instance specChart_isAffine (k : SpecChartIndex B S hS F) :
    _root_.AlgebraicGeometry.IsAffine
      (reprScheme B S hS (etaleChartBase B S hS F (specChart B S hS F k))) :=
  inferInstanceAs (_root_.AlgebraicGeometry.IsAffine (Spec k.ring))

include hF hN in
/-- The base scheme of the chart of an index is Noetherian. -/
theorem specChart_isNoetherian (k : SpecChartIndex B S hS F) :
    _root_.AlgebraicGeometry.IsNoetherian
      (reprScheme B S hS (etaleChartBase B S hS F (specChart B S hS F k))) :=
  have := k.isNoetherianRing B S hS F hF hN
  inferInstanceAs (_root_.AlgebraicGeometry.IsNoetherian (Spec k.ring))

/-- **The restriction of a dualizing complex to the chart of an index is `ε^* ω`** for a
dualizing complex `ω` on `Spec Γ(X_W, A)` (Stacks 0E4Z). -/
theorem exists_dualizing_specChart (K : QuasicoherentDerivedCategory.{u, u} B S hS F hF)
    (hK : IsDualizingComplexOnSpace B S hS F hF hN K) (k : SpecChartIndex B S hS F) :
    ∃ ω : RingedSite.SchemeStdDerived
        (reprScheme B S hS (etaleChartBase B S hS F (specChart B S hS F k))),
      (letI : HasDerivedCategory
          (reprScheme B S hS (etaleChartBase B S hS F (specChart B S hS F k))).Modules :=
        HasDerivedCategory.standard _
      haveI := specChart_isNoetherian B S hS F hF hN k
      Stacks.Duality.IsDualizingComplex ω) ∧
      Nonempty ((representedChartDerivedRestriction B S hS hF
          (etaleChartBase B S hS F (specChart B S hS F k)) (specChart B S hS F k).obj.hom
          (etaleChartMap_isEtale B S hS F hF (specChart B S hS F k))).obj K.obj ≅
        (representedDerivedAssociatedModule B S hS
          (etaleChartBase B S hS F (specChart B S hS F k))).obj ω) :=
  hK _ _ (specChart B S hS F k).property

/-- **The full duality chart of a dualizing complex on the slice of the model at the object of an
index** (Stacks 0A89, Stacks 0E50). -/
def specFullChart (K : QuasicoherentDerivedCategory.{u, u} B S hS F hF)
    (hK : IsDualizingComplexOnSpace B S hS F hF hN K) (k : SpecChartIndex B S hS F) :
    RingedSite.DualityChart ((smallEtaleModelRingedSite B S hS F hF).over (specChartObj B S hS F k))
      ((RingedSite.stdRestrict (smallEtaleModelRingedSite B S hS F hF)
          (specChartObj B S hS F k)).obj
        ((modelDerivedEquivalence B S hS F hF).functor.obj K.obj))
      RingedSite.ChartClass.all :=
  haveI := specChart_isNoetherian B S hS F hF hN k
  haveI := k.isNoetherianRing B S hS F hF hN
  let hω := exists_dualizing_specChart B S hS F hF hN K hK k
  sliceChartOfIso B S hS F hF (specChartObj B S hS F k) (specChart B S hS F k)
    (specChartIso B S hS F k) K.obj hω.choose hω.choose_spec.1
    (SmallEtale.exists_etaleBound k.ring (associatedBigEtaleSite B)
      (etaleChartBase B S hS F (specChart B S hS F k)).left.property hω.choose
      hω.choose_spec.1).choose
    (SmallEtale.exists_etaleBound k.ring (associatedBigEtaleSite B)
      (etaleChartBase B S hS F (specChart B S hS F k)).left.property hω.choose
      hω.choose_spec.1).choose_spec
    hω.choose_spec.2.some

end AlgebraicGeometry.Space

end
