module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SiteEnlargementChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAffineRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveSurjective
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.StandardCoveringSieves
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

/-!
# The small étale site of an algebraic space is a dense subsite after enlarging the big site

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B` and let
`X` be an algebraic space over `S` for `B`, with inverse image `X'` on the enlarged site. The
transport of étale charts `AlgebraicGeometry.SiteEnlargement.chartTransport` exhibits the small
étale site of `X` as a dense subsite of the small étale site of `X'`. Consequently restriction of
sheaves along it is an equivalence of topoi, for every coefficient category with the limits of
size `u`: the small étale topos of an algebraic space does not depend on the big fppf site used
to define it.

## Main results

* `AlgebraicGeometry.SiteEnlargement.mem_topology_iff_forall_exists_mem_range`: a sieve of the
  small étale site is covering exactly when its arrows are jointly surjective on the underlying
  schemes.
* `AlgebraicGeometry.SiteEnlargement.chartTransport_functorPushforward_mem_iff`: a sieve of the
  small étale site of `X` covers exactly when its image in the small étale site of `X'` does.
* `AlgebraicGeometry.SiteEnlargement.chartTransport_isCoverDense`: every étale chart of `X'` is
  covered by transported charts.
* `AlgebraicGeometry.SiteEnlargement.chartTransport_isDenseSubsite`: the transport of charts is
  a dense subsite inclusion.

## Implementation notes

Both directions of the comparison of topologies go through the description of a covering sieve
by joint surjectivity, because the transport of charts does not change the underlying scheme of
a chart or of a morphism of charts. Cover density is the point where the enlargement is used:
an étale chart `V` of `X'` meets the transported atlas `h_{i W} ⟶ X'` of `X` in a scheme `P`
étale and surjective over `V` and étale over `i W`; every affine open of `P` is étale over the
object `W` of the smaller site, hence below its cutoff
(`AlgebraicGeometry.size_lt_cutoff_of_isAffine_of_locallyOfFiniteType`), and so it is the
underlying scheme of a chart of `X`.

## References

* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.SiteEnlargement

open Space

section Topology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **A sieve of the small étale site covers exactly when its arrows are jointly surjective on
the underlying schemes.** The arrows of a sieve of étale charts are étale on the underlying
schemes (Stacks 03EC), so the family of all of them is an étale covering family of schemes as
soon as it is jointly surjective, and such a family generates a covering sieve with no bound on
its index set. -/
theorem mem_topology_iff_forall_exists_mem_range {W : Space.SmallEtale B S hS F} {T : Sieve W} :
    T ∈ Space.SmallEtale.topology B S hS F W ↔
      ∀ x : chartScheme W, ∃ (V : Space.SmallEtale B S hS F) (g : V ⟶ W), T g ∧
        x ∈ Set.range ((BigFppfOver.toScheme B S hS).map
          ((Space.SmallEtale.toOver B S hS F).map g)).base := by
  constructor
  · intro hT x
    obtain ⟨R, hR, hRT⟩ := (Space.SmallEtale.mem_topology_iff B S hS F).mp hT
    rw [Space.SmallEtale.precoverage_eq_comap, Precoverage.mem_comap_iff,
      BigFppfSite.etalePrecoverage_eq_comap, Precoverage.mem_comap_iff] at hR
    obtain ⟨Y, g, ⟨⟨⟨hg⟩⟩⟩, hx⟩ := hR.1 x
    exact ⟨_, _, hRT _ _ hg, hx⟩
  · intro hT
    let ι := {p : Σ V : Space.SmallEtale B S hS F, V ⟶ W // T p.2}
    refine GrothendieckTopology.superset_covering _ ?_
      (Space.SmallEtale.ofArrows_mem_topology B S hS F (fun p : ι => p.1.1) (fun p => p.1.2) ?_)
    · rintro _ _ ⟨_, _, _, ⟨p⟩, rfl⟩
      exact T.downward_closed p.2 _
    · refine Scheme.ofArrows_mem_etalePrecoverage_iff.mpr ⟨fun x => ?_, fun p =>
        etale_toScheme_toOver_map B S hS F p.1.2⟩
      obtain ⟨V, g, hg, hx⟩ := hT x
      exact ⟨⟨⟨V, g⟩, hg⟩, hx⟩

end Topology

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **A sieve of étale charts of `X` covers exactly when its image under the transport of
charts covers.** The transport does not change the underlying morphisms of schemes, and both
conditions are joint surjectivity of those morphisms. -/
theorem chartTransport_functorPushforward_mem_iff {W : Space.SmallEtale B S hS X.obj}
    {T : Sieve W} :
    T.functorPushforward (chartTransport B B' h S hS X) ∈
        Space.SmallEtale.topology B' S (largerContains h hS)
          ((changeBigSite B B' h S hS).obj X).obj ((chartTransport B B' h S hS X).obj W) ↔
      T ∈ Space.SmallEtale.topology B S hS X.obj W := by
  refine mem_topology_iff_forall_exists_mem_range.trans
    (Iff.trans ?_ mem_topology_iff_forall_exists_mem_range.symm)
  constructor
  · intro hT x
    obtain ⟨V', g', ⟨V, g, k, hg, rfl⟩, hx⟩ := hT x
    refine ⟨V, g, hg, ?_⟩
    exact Set.range_comp_subset_range
      ((BigFppfOver.toScheme B' S (largerContains h hS)).map
        ((Space.SmallEtale.toOver B' S (largerContains h hS)
          ((changeBigSite B B' h S hS).obj X).obj).map k)).base
      ((BigFppfOver.toScheme B S hS).map ((Space.SmallEtale.toOver B S hS X.obj).map g)).base hx
  · intro hT x
    obtain ⟨V, g, hg, hx⟩ := hT x
    exact ⟨_, (chartTransport B B' h S hS X).map g, ⟨V, g, 𝟙 _, hg, (Category.id_comp _).symm⟩,
      hx⟩

/-- The localized inclusion of big fppf sites is full, as an instance at `τ = fppf`. -/
local instance : (inclusionOver h S hS).Full := inclusionOver_full (τ := .fppf) h S hS

/-- The localized inclusion of big fppf sites is faithful, as an instance at `τ = fppf`. -/
local instance : (inclusionOver h S hS).Faithful := inclusionOver_faithful (τ := .fppf) h S hS

variable {B B' h S hS X}

/-- An object of the enlarged localized site whose underlying scheme is below the cutoff of the
smaller site, read as an object of the smaller localized site. -/
def descendObj (h : IsContained (τ := .fppf) B B') (V : BigFppfOver B' S (largerContains h hS))
    (hV : ((BigFppfOver.toScheme B' S (largerContains h hS)).obj V).size < B.cutoff) :
    BigFppfOver B S hS :=
  Over.mk (ObjectProperty.homMk V.hom.hom : (⟨_, hV⟩ : B.Schemes) ⟶ B.obj hS)

/-- The descended object is sent back to the given one by the localized inclusion. -/
theorem inclusionOver_obj_descendObj (h : IsContained (τ := .fppf) B B')
    (V : BigFppfOver B' S (largerContains h hS))
    (hV : ((BigFppfOver.toScheme B' S (largerContains h hS)).obj V).size < B.cutoff) :
    (inclusionOver h S hS).obj (descendObj h V hV) = V :=
  rfl

/-- The morphism of the smaller localized site underlying a morphism from a chart of `X'` with
small underlying scheme to a transported chart. -/
def descendHom (Y : Space.SmallEtale B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj X).obj)
    (hY : (chartScheme Y).size < B.cutoff) (U : Space.SmallEtale B S hS X.obj)
    (m : Y ⟶ (chartTransport B B' h S hS X).obj U) : descendObj h Y.obj.left hY ⟶ U.obj.left :=
  @Functor.preimage _ _ _ _ (descendObj h Y.obj.left hY) U.obj.left (inclusionOver h S hS)
    (inclusionOver_full (τ := .fppf) h S hS) m.hom.left

/-- The localized inclusion sends the descended morphism back to the morphism of schemes it was
descended from. -/
theorem inclusionOver_map_descendHom (Y : Space.SmallEtale B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj X).obj)
    (hY : (chartScheme Y).size < B.cutoff) (U : Space.SmallEtale B S hS X.obj)
    (m : Y ⟶ (chartTransport B B' h S hS X).obj U) :
    (inclusionOver h S hS).map (descendHom Y hY U m) = m.hom.left :=
  @Functor.map_preimage _ _ _ _ (inclusionOver h S hS) (inclusionOver_full (τ := .fppf) h S hS)
    (descendObj h Y.obj.left hY) U.obj.left m.hom.left

/-- **An étale chart of `X'` which maps to a transported chart and whose scheme is below the
cutoff of the smaller site descends to an étale chart of `X`.** The chart of `X` is the
composite of the preimage of the given morphism with the chart it maps to; it is étale because
the underlying morphism of schemes of a morphism of étale charts is étale (Stacks 03EC). -/
def descendChart (Y : Space.SmallEtale B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj X).obj)
    (hY : (chartScheme Y).size < B.cutoff) (U : Space.SmallEtale B S hS X.obj)
    (m : Y ⟶ (chartTransport B B' h S hS X).obj U) : Space.SmallEtale B S hS X.obj :=
  ⟨CostructuredArrow.mk (yoneda.map (descendHom Y hY U m) ≫ U.obj.hom),
    etale_comp_of_scheme B S hS _ U.obj.hom (by
      have e := etale_toScheme_toOver_map B' S (largerContains h hS)
        ((changeBigSite B B' h S hS).obj X).obj m
      have e' : Etale ((BigFppfOver.toScheme B' S (largerContains h hS)).map
          ((inclusionOver h S hS).map (descendHom Y hY U m))) :=
        (inclusionOver_map_descendHom Y hY U m).symm ▸ e
      exact e')
      U.property⟩

/-- The transport of a descended chart is the chart it was descended from. -/
def chartTransportDescendChartIso (Y : Space.SmallEtale B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj X).obj)
    (hY : (chartScheme Y).size < B.cutoff) (U : Space.SmallEtale B S hS X.obj)
    (m : Y ⟶ (chartTransport B B' h S hS X).obj U) :
    (chartTransport B B' h S hS X).obj (descendChart Y hY U m) ≅ Y :=
  ObjectProperty.isoMk _ (CostructuredArrow.isoMk
    (eqToIso (inclusionOver_obj_descendObj h Y.obj.left hY)) (by
    refine (congrArg (fun k => yoneda.map k ≫ Y.obj.hom)
      (eqToHom_refl Y.obj.left rfl)).trans ?_
    refine (congrArg (· ≫ Y.obj.hom) (yoneda.map_id _)).trans ((Category.id_comp _).trans ?_)
    change Y.obj.hom = chartHom B B' h S hS X (yoneda.map (descendHom Y hY U m) ≫ U.obj.hom)
    refine Eq.trans ?_ (chartHom_comp B B' h S hS X (descendHom Y hY U m) U.obj.hom).symm
    refine (CostructuredArrow.w m.hom).symm.trans ?_
    exact congrArg (fun k => yoneda.map k ≫ chartHom B B' h S hS X U.obj.hom)
      (inclusionOver_map_descendHom Y hY U m).symm))

variable (B B' h S hS X) in
/-- **The transport of an étale atlas of `X` is locally surjective.** A surjective étale atlas
presents `X` as the coequalizer of its kernel pair in sheaves of sets (Stacks 0262, part (3)),
so it is an epimorphism of sheaves; the inverse image along the localized inclusion is a left
adjoint, hence preserves epimorphisms, and an epimorphism of sheaves of sets is locally
surjective. The transported chart differs from the inverse image of the atlas by the
identification `h_{i U} ≅ f⁻¹h_U` of Stacks 03FP, part (1). -/
theorem isLocallySurjective_chartHom {U : BigFppfOver B S hS} (q : yoneda.obj U ⟶ X.obj)
    (hqs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) q)
    (hqe : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) q) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B' S (largerContains h hS))
      (chartHom B B' h S hS X q) := by
  let J := overTopology .fppf B S hS
  let K := overTopology .fppf B' S (largerContains h hS)
  let i := inclusionOver h S hS
  let : i.IsContinuous J K :=
    (inclusionOver_isMorphismOfSites (τ := .fppf) B B' h S hS).toIsContinuous
  let : (i.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint :=
    inclusionOver_sheafPushforwardContinuous_isRightAdjoint B B' h S hS
  let : HasSheafify K (Type u) := hasSheafify_overTopology B' S (largerContains h hS)
  let L := i.sheafPullback (Type u) J K
  let : L.IsLeftAdjoint := ⟨_, ⟨i.sheafAdjunctionContinuous (Type u) J K⟩⟩
  let R := hqe.rep.pullback q
  let s : R ⟶ U := hqe.rep.fst' q
  let t : R ⟶ U := hqe.rep.snd q
  have hR : IsPullback (yoneda.map s) (yoneda.map t) q q := hqe.rep.isPullback' q
  obtain ⟨hRsh, hUsh, ⟨hcoeq⟩⟩ :=
    Space.isCoequalizer_of_surjectiveEtale B S hS q s t hR X.property hqs hqe
  let ff : (⟨yoneda.obj U, hUsh⟩ : Sheaf J (Type u)) ⟶ ⟨X.obj, X.property.isSheaf⟩ := ⟨q⟩
  have hepi : Epi ff := Cofork.IsColimit.epi hcoeq
  have hls : Sheaf.IsLocallySurjective (L.map ff) :=
    (Sheaf.isLocallySurjective_iff_epi (L.map ff)).mpr inferInstance
  have hsh : Presheaf.IsSheaf K (yoneda.obj ((inclusionOver h S hS).obj U)) :=
    (Presheaf.isSheaf_of_iso_iff (changeBigSiteYonedaIso B B' h S hS U)).mpr
      (L.obj ⟨yoneda.obj U, hUsh⟩).property
  let eS : (⟨yoneda.obj ((inclusionOver h S hS).obj U), hsh⟩ : Sheaf K (Type u)) ≅
      L.obj ⟨yoneda.obj U, hUsh⟩ :=
    ObjectProperty.isoMk _ (changeBigSiteYonedaIso B B' h S hS U)
  have hc : Presheaf.IsLocallySurjective K
      ((changeBigSiteYonedaIso B B' h S hS U).hom ≫ (L.map ff).hom) :=
    (inferInstance : Sheaf.IsLocallySurjective (eS.hom ≫ L.map ff))
  exact chartHom_eq B B' h S hS X q ▸ hc

variable (B B' h S hS X) in
/-- **Every étale chart of `X'` is covered by transported charts of `X`.** An étale chart `V`
of `X'` meets the transported atlas `h_{i W} ⟶ X'` of `X` in a scheme `P`, étale and surjective
over `V` and étale over `i W`; every affine open of `P` is étale over the object `W` of the
smaller site, hence below its cutoff, so it is the scheme of a chart of `X`, and the affine
opens of `P` cover `V`. -/
theorem chartTransport_isCoverDense :
    (chartTransport B B' h S hS X).IsCoverDense
      (Space.SmallEtale.topology B' S (largerContains h hS)
        ((changeBigSite B B' h S hS).obj X).obj) := by
  refine ⟨fun V => mem_topology_iff_forall_exists_mem_range.mpr fun x => ?_⟩
  obtain ⟨U, q, hqs, hqe⟩ := X.property.exists_atlas
  let Uc : Space.SmallEtale B S hS X.obj := ⟨CostructuredArrow.mk q, hqe⟩
  let ψ := chartHom B B' h S hS X q
  have hψe := isEtaleChart_chartHom B B' h S hS X q hqe
  have hψs := Space.presheaf_surjective_of_isLocallySurjective B' S (largerContains h hS)
    hψe.rep (isLocallySurjective_chartHom B B' h S hS X q hqs hqe)
  let P := hψe.rep.pullback V.obj.hom
  let p₁ : P ⟶ V.obj.left := hψe.rep.snd V.obj.hom
  let p₂ : P ⟶ (inclusionOver h S hS).obj U := hψe.rep.fst' V.obj.hom
  have hsq : IsPullback (yoneda.map p₂) (yoneda.map p₁) ψ V.obj.hom :=
    hψe.rep.isPullback' V.obj.hom
  have hp₁ : Surjective ((BigFppfOver.toScheme B' S (largerContains h hS)).map p₁) :=
    hψs.property_snd V.obj.hom
  let Pc : Space.SmallEtale B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj :=
    ⟨CostructuredArrow.mk (yoneda.map p₁ ≫ V.obj.hom),
      etale_comp_of_scheme B' S (largerContains h hS) p₁ V.obj.hom
        (hψe.property_snd V.obj.hom) V.property⟩
  let mP : Pc ⟶ V := ObjectProperty.homMk (CostructuredArrow.homMk p₁ rfl)
  let mPU : Pc ⟶ (chartTransport B B' h S hS X).obj Uc :=
    ObjectProperty.homMk (CostructuredArrow.homMk p₂ hsq.w)
  obtain ⟨p, hp⟩ := hp₁.surj x
  obtain ⟨_, ⟨Q, hQ, rfl⟩, hpQ, -⟩ :=
    ((BigFppfOver.toScheme B' S (largerContains h hS)).obj P).isBasis_affineOpens
      |>.exists_subset_of_mem_open (Set.mem_univ p) isOpen_univ
  let Y := openChart B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj Pc Q
  let inc := openChartInclusion B' S (largerContains h hS)
    ((changeBigSite B B' h S hS).obj X).obj Pc Q
  have hYaff : IsAffine (chartScheme Y) := hQ
  have hY : (chartScheme Y).size < B.cutoff := by
    let f := (BigFppfOver.toScheme B' S (largerContains h hS)).map
      ((Space.SmallEtale.toOver B' S (largerContains h hS)
        ((changeBigSite B B' h S hS).obj X).obj).map (inc ≫ mPU))
    have : Etale f := etale_toScheme_toOver_map B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj X).obj (inc ≫ mPU)
    exact size_lt_cutoff_of_isAffine_of_locallyOfFiniteType (τ := .fppf) B f U.left.property
  let e := chartTransportDescendChartIso Y hY Uc (inc ≫ mPU)
  refine ⟨_, e.hom ≫ inc ≫ mP, Presieve.in_coverByImage _ _, ⟨p, hpQ⟩, ?_⟩
  have h1 := toScheme_map_toOver_map_openChartInclusion B' S (largerContains h hS)
    ((changeBigSite B B' h S hS).obj X).obj Pc Q
  simp only [Functor.map_comp]
  have h2 : ((BigFppfOver.toScheme B' S (largerContains h hS)).map
      ((Space.SmallEtale.toOver B' S (largerContains h hS)
        ((changeBigSite B B' h S hS).obj X).obj).map inc)) ⟨p, hpQ⟩ = p :=
    congrArg (fun f => f ⟨p, hpQ⟩) h1
  exact (congrArg ((BigFppfOver.toScheme B' S (largerContains h hS)).map p₁) h2).trans hp

variable (B B' h S hS X) in
/-- **The transport of étale charts is a dense subsite inclusion**: it is fully faithful, every
étale chart of `X'` is covered by transported charts, and a sieve of charts of `X` covers exactly
when its image does. Restriction along it is therefore an equivalence of small étale topoi
(`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`). -/
theorem chartTransport_isDenseSubsite :
    (chartTransport B B' h S hS X).IsDenseSubsite (Space.SmallEtale.topology B S hS X.obj)
      (Space.SmallEtale.topology B' S (largerContains h hS)
        ((changeBigSite B B' h S hS).obj X).obj) where
  isCoverDense' := chartTransport_isCoverDense B B' h S hS X
  functorPushforward_mem_iff := chartTransport_functorPushforward_mem_iff B B' h S hS X

end AlgebraicGeometry.SiteEnlargement

end
