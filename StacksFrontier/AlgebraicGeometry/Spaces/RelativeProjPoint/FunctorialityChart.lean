module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjFunctoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelPairRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspacePushforwardCech
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.Presentation

/-!
# The charts of `U(ψ)` and of `r_ψ` over the scheme points of the base

Let `ψ` be a map of graded algebras read over the scheme points of the base
(`AlgebraicGeometry.Space.RelativeProjHomPoints`), between presentations of `P = Proj_X(𝒜)` and
`Q = Proj_X(ℬ)` by their base changes to the scheme points `f : T ⟶ X`. This file describes the
open subspace `U(ψ) ⊆ Q` and the morphism `r_ψ : U(ψ) ⟶ P` of Stacks 085F on these base changes:
`U(ψ) ×_X T` is the open subobject of `Q ×_X T` which the identification of `Q ×_X T` with
`Proj_T(ℬ|_T)` carries onto the open `U(ψ|_T)` of Tag 07ZG, and on it `r_ψ` is the morphism
`r_{ψ|_T}` of Tag 07ZG. Morphisms of base changes restrict to these charts compatibly with
`r_ψ`; read on schemes they are the data along which the map `θ` of Tag 07ZG is transported
(`Stacks.AlgebraicGeometry.Tag07ZGTwist.transportTwistHom`).

## Main definitions

* `AlgebraicGeometry.Space.RelativeProjHomPoints.chartObj`: the chart `U(ψ) ×_X T`, with
  `…chartIncl` its inclusion into `Q ×_X T` and `…chartToSubfunctor` its morphism to `U(ψ)`.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.chartSchemeIso`: its scheme is `U(ψ|_T)`.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.chartMapHom`: `r_ψ` on the chart.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.chartTransition` and `…chartSchemeTransition`:
  a morphism of base changes, restricted to the charts.

## Main results

* `AlgebraicGeometry.Space.RelativeProjHomPoints.isPullback_chartToSubfunctor`: the chart is
  `U(ψ) ×_Q (Q ×_X T)`; it is étale and surjective over `U(ψ)` when `f` is
  (`…etale_chartToSubfunctor`, `…surjective_chartToSubfunctor`).
* `AlgebraicGeometry.Space.RelativeProjHomPoints.toScheme_map_chartMapHom`: on the chart `r_ψ`
  is `r_{ψ|_T}`.
* `AlgebraicGeometry.Space.RelativeProjHomPoints.chartSchemeTransition_ι` and
  `…relativeMapHom_comp_chartSchemeTransition`: the restricted morphisms of base changes are
  compatible with the inclusions of Tag 07ZG's opens and with the morphisms of Tag 07ZG.

## References

* [Stacks Project, Tag 085F](https://stacks.math.columbia.edu/tag/085F)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj (relativeProj)
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.Tag07ZGMorphism

universe u

/-- **The kernel pair of a base change.** If `U' = G ×_F U` and `R' = G ×_F R` and `R = U ×_F U`,
and `t, s : R' ⟶ U'` lie over the two projections of `R` and over `G`, then `R' = U' ×_G U'`. -/
theorem CategoryTheory.IsPullback.kernelPair_of_baseChange {C : Type*} [Category C]
    {G F U R U' R' : C} {ι : G ⟶ F} {q : U ⟶ F} {cT cS : R ⟶ U} {φU : U' ⟶ G} {iU : U' ⟶ U}
    {φR : R' ⟶ G} {iR : R' ⟶ R} {t s : R' ⟶ U'}
    (hU : IsPullback φU iU ι q) (hR : IsPullback φR iR ι (cT ≫ q)) (hK : IsPullback cT cS q q)
    (ht : t ≫ iU = iR ≫ cT) (hs : s ≫ iU = iR ≫ cS) (htφ : t ≫ φU = φR) (hsφ : s ≫ φU = φR) :
    IsPullback t s φU φU := by
  refine ⟨⟨by rw [htφ, hsφ]⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => ?lift) ?_ ?_ ?_⟩⟩
  case lift =>
    have hab : (c.fst ≫ iU) ≫ q = (c.snd ≫ iU) ≫ q := by
      rw [Category.assoc, ← hU.w, ← Category.assoc, c.condition, Category.assoc, hU.w,
        Category.assoc]
    have h2 : (c.fst ≫ φU) ≫ ι = hK.lift _ _ hab ≫ cT ≫ q := by
      rw [← Category.assoc, hK.lift_fst, Category.assoc, Category.assoc, hU.w]
    exact hR.lift _ _ h2
  · intro c
    apply hU.hom_ext
    · rw [Category.assoc, htφ, hR.lift_fst]
    · rw [Category.assoc, ht, ← Category.assoc, hR.lift_snd, hK.lift_fst]
  · intro c
    apply hU.hom_ext
    · rw [Category.assoc, hsφ, hR.lift_fst, c.condition]
    · rw [Category.assoc, hs, ← Category.assoc, hR.lift_snd, hK.lift_snd]
  · intro c m hm₁ hm₂
    apply hR.hom_ext
    · rw [hR.lift_fst, ← htφ, ← Category.assoc, hm₁]
    · rw [hR.lift_snd]
      apply hK.hom_ext
      · rw [hK.lift_fst, Category.assoc, ← ht, ← Category.assoc, hm₁]
      · rw [hK.lift_snd, Category.assoc, ← hs, ← Category.assoc, hm₂]

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {πP : P ⟶ X} {πQ : Q ⟶ X}

namespace RelativeProjPoints

variable (d : RelativeProjPoints B S hS πQ)

/-- The point `T ×_X Q ⟶ Q` itself corresponds to the identification of `T ×_X Q` with the
relative Proj. -/
theorem sectionOfPoint_fibreToSpace (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    d.sectionOfPoint T f (d.fibreHom T f) (d.fibreToSpace T f) (d.isPullback T f).w =
      (d.fibreIso T f).hom := by
  have h : (d.pointEquivOver T f (d.fibreHom T f) ⟨d.fibreToSpace T f, (d.isPullback T f).w⟩) =
      ⟨𝟙 _, Category.id_comp _⟩ := by
    apply (d.pointEquivOver T f (d.fibreHom T f)).symm.injective
    rw [Equiv.symm_apply_apply]
    apply Subtype.ext
    show d.fibreToSpace T f = yoneda.map (𝟙 _) ≫ d.fibreToSpace T f
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
  show (d.pointEquivProjOver T f (d.fibreHom T f) ⟨_, _⟩).1 = _
  rw [pointEquivProjOver_apply, h, CategoryTheory.Functor.map_id, Category.id_comp]

/-- A morphism of fibres lying over a morphism `k` of test objects, read on the relative Projs,
lies over `k`. -/
theorem fibreIso_inv_map_fibreIso_hom_toBase {T T' : BigFppfOver B S hS} {f : yoneda.obj T ⟶ X}
    {f' : yoneda.obj T' ⟶ X} (c : d.fibre T' f' ⟶ d.fibre T f) (k : T' ⟶ T)
    (hck : c ≫ d.fibreHom T f = d.fibreHom T' f' ≫ k) :
    ((d.fibreIso T' f').inv ≫ (BigFppfOver.toScheme B S hS).map c ≫ (d.fibreIso T f).hom) ≫
        (relativeProj (d.algebra T f)).toBase =
      (relativeProj (d.algebra T' f')).toBase ≫ (BigFppfOver.toScheme B S hS).map k := by
  rw [Category.assoc, Category.assoc, ← d.fibreHom_comp, ← Functor.map_comp, hck,
    Functor.map_comp, d.fibreHom_comp, Category.assoc, Iso.inv_hom_id_assoc]

end RelativeProjPoints

namespace RelativeProjHomPoints

variable {dP : RelativeProjPoints B S hS πP} {dQ : RelativeProjPoints B S hS πQ}
  (hψ : RelativeProjHomPoints dP dQ)

/-- **The part of `T ×_X Q` lying in `U(ψ)`**, read on the relative Proj of the restricted algebra:
the inverse image of the open `U(ψ|_T)` of Tag 07ZG. -/
def chartDomain (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    ((BigFppfOver.toScheme B S hS).obj (dQ.fibre T f)).Opens :=
  (dQ.fibreIso T f).hom ⁻¹ᵁ (hψ.hom T f).relativeMapDomain

/-- A point of `T ×_X Q` lies in `U(ψ)` exactly when it lands in `chartDomain`. -/
theorem mem_relativeMapSubfunctor_fibre_iff (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ dQ.fibre T f) :
    yonedaEquiv (yoneda.map r ≫ dQ.fibreToSpace T f) ∈ hψ.relativeMapSubfunctor.obj (op T') ↔
      Set.range ((BigFppfOver.toScheme B S hS).map r) ⊆ (hψ.chartDomain T f : Set _) := by
  have hu : (yoneda.map r ≫ dQ.fibreToSpace T f) ≫ πQ = yoneda.map (r ≫ dQ.fibreHom T f) ≫ f := by
    rw [Category.assoc, (dQ.isPullback T f).w, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp]
  rw [hψ.mem_relativeMapSubfunctor_iff T f (r ≫ dQ.fibreHom T f) _ hu,
    dQ.sectionOfPoint_restrict T f (dQ.fibreHom T f) r (dQ.fibreToSpace T f) (dQ.isPullback T f).w
      hu,
    dQ.sectionOfPoint_fibreToSpace, Scheme.Hom.comp_preimage, preimage_eq_top_iff]
  rfl

/-- **The chart `U(ψ) ×_X T` of `U(ψ)`** over a scheme point `f : T ⟶ X`: the open subobject of
`Q ×_X T` cut out by `chartDomain`. -/
abbrev chartObj (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) : BigFppfOver B S hS :=
  openSub (dQ.fibre T f) (hψ.chartDomain T f)

/-- The inclusion of the chart into `Q ×_X T`. -/
abbrev chartIncl (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    hψ.chartObj T f ⟶ dQ.fibre T f :=
  openSubHom (dQ.fibre T f) (hψ.chartDomain T f)

/-- A morphism into `Q ×_X T` factors through the chart exactly when it lands in `U(ψ)`. -/
theorem range_subset_chartDomain_of_mem (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ hψ.chartObj T f) :
    Set.range ((BigFppfOver.toScheme B S hS).map (r ≫ hψ.chartIncl T f)) ⊆
      (hψ.chartDomain T f : Set _) := by
  rintro _ ⟨y, rfl⟩
  rw [CategoryTheory.Functor.map_comp, Scheme.Hom.comp_apply, toScheme_map_openSubHom]
  exact ((BigFppfOver.toScheme B S hS).map r y).2

/-- **The chart maps into `U(ψ)`.** -/
def chartToSubfunctor (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    yoneda.obj (hψ.chartObj T f) ⟶ hψ.relativeMapSubfunctor.toFunctor :=
  Subfunctor.lift (yoneda.map (hψ.chartIncl T f) ≫ dQ.fibreToSpace T f) (by
    rintro ⟨T'⟩ _ ⟨r, rfl⟩
    have h := (hψ.mem_relativeMapSubfunctor_fibre_iff T f (r ≫ hψ.chartIncl T f)).2
      (hψ.range_subset_chartDomain_of_mem T f r)
    rw [CategoryTheory.Functor.map_comp, Category.assoc] at h
    exact h)

/-- The chart map into `U(ψ)`, composed with the inclusion of `U(ψ)`, is the inclusion of the
chart followed by the map `Q ×_X T ⟶ Q`. -/
@[reassoc]
theorem chartToSubfunctor_ι (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    hψ.chartToSubfunctor T f ≫ hψ.relativeMapSubfunctor.ι =
      yoneda.map (hψ.chartIncl T f) ≫ dQ.fibreToSpace T f :=
  Subfunctor.lift_ι _ _

/-- The points of `Q ×_X T` lying in `U(ψ)` are those factoring through the chart. -/
theorem range_yoneda_map_chartIncl (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    Subfunctor.range (yoneda.map (hψ.chartIncl T f)) =
      hψ.relativeMapSubfunctor.preimage (dQ.fibreToSpace T f) := by
  ext ⟨T'⟩ r
  show (∃ h, h ≫ hψ.chartIncl T f = r) ↔
    (dQ.fibreToSpace T f).app (op T') r ∈ hψ.relativeMapSubfunctor.obj (op T')
  have e : (dQ.fibreToSpace T f).app (op T') r =
      yonedaEquiv (yoneda.map r ≫ dQ.fibreToSpace T f) := by
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
  rw [e, hψ.mem_relativeMapSubfunctor_fibre_iff]
  constructor
  · rintro ⟨h, rfl⟩
    exact hψ.range_subset_chartDomain_of_mem T f h
  · intro hr
    exact ⟨openSubLift _ _ r (fun y => hr ⟨y, rfl⟩), openSubLift_comp_openSubHom _ _ _ _⟩

/-- **The chart is the fibre product `U(ψ) ×_Q (Q ×_X T)`.** -/
theorem isPullback_chartToSubfunctor (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    IsPullback (hψ.chartToSubfunctor T f) (yoneda.map (hψ.chartIncl T f))
      hψ.relativeMapSubfunctor.ι (dQ.fibreToSpace T f) := by
  have hmono : Mono (hψ.chartIncl T f) := mono_openSubHom_of_opens _ _
  have hkey := hψ.range_yoneda_map_chartIncl T f
  have hsq := Subfunctor.isPullback_fromPreimage hψ.relativeMapSubfunctor (dQ.fibreToSpace T f)
  have hiso := Subfunctor.isIso_lift hkey.le hkey.ge
  have hfac : hψ.chartToSubfunctor T f =
      Subfunctor.lift (yoneda.map (hψ.chartIncl T f)) hkey.le ≫
        hψ.relativeMapSubfunctor.fromPreimage (dQ.fibreToSpace T f) := by
    rw [← cancel_mono hψ.relativeMapSubfunctor.ι, chartToSubfunctor_ι, Category.assoc,
      hψ.relativeMapSubfunctor.fromPreimage_ι, ← Category.assoc, Subfunctor.lift_ι]
  rw [hfac]
  refine IsPullback.of_iso_pullback
    ⟨by rw [Category.assoc, hψ.relativeMapSubfunctor.fromPreimage_ι, ← Category.assoc,
      Subfunctor.lift_ι]⟩
    (asIso (Subfunctor.lift (yoneda.map (hψ.chartIncl T f)) hkey.le) ≪≫ hsq.isoPullback) ?_ ?_
  · simp [hsq.isoPullback_hom_fst]
  · simp [hsq.isoPullback_hom_snd]

/-- **The scheme of the chart is the open `U(ψ|_T)` of Tag 07ZG**, through the identification of
`Q ×_X T` with the relative Proj of the restricted algebra. -/
def chartSchemeIso (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    (BigFppfOver.toScheme B S hS).obj (hψ.chartObj T f) ≅
      (hψ.hom T f).relativeMapDomain.toScheme :=
  (dQ.fibreIso T f).hom.preimageIso (hψ.hom T f).relativeMapDomain

/-- `chartSchemeIso` followed by the inclusion of `U(ψ|_T)` is the inclusion of the chart
followed by the identification of `Q ×_X T` with the relative Proj. -/
@[reassoc]
theorem chartSchemeIso_hom_ι (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    (hψ.chartSchemeIso T f).hom ≫ (hψ.hom T f).relativeMapDomain.ι =
      (BigFppfOver.toScheme B S hS).map (hψ.chartIncl T f) ≫ (dQ.fibreIso T f).hom := by
  rw [toScheme_map_openSubHom]
  exact Scheme.Hom.preimageIso_hom_ι _ _

/-- The point of `U(ψ)` given by the chart lies over `f`. -/
theorem chartToSubfunctor_comp (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    (hψ.chartToSubfunctor T f ≫ hψ.relativeMapSpaceHom) ≫ πP =
      yoneda.map (hψ.chartIncl T f ≫ dQ.fibreHom T f) ≫ f := by
  rw [Category.assoc, relativeMapSpaceHom_comp, chartToSubfunctor_ι_assoc, (dQ.isPullback T f).w,
    CategoryTheory.Functor.map_comp, Category.assoc]

/-- **The morphism `r_ψ` on the chart**, as a morphism of the site into `P ×_X T`. -/
def chartMapHom (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    hψ.chartObj T f ⟶ dP.fibre T f :=
  (dP.pointEquivOver T f (hψ.chartIncl T f ≫ dQ.fibreHom T f)
    ⟨hψ.chartToSubfunctor T f ≫ hψ.relativeMapSpaceHom, hψ.chartToSubfunctor_comp T f⟩).1

/-- `chartMapHom` lies over `T`: composed with the projection `P ×_X T ⟶ T` it is the inclusion of
the chart followed by the projection `Q ×_X T ⟶ T`. -/
@[reassoc]
theorem chartMapHom_fibreHom (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    hψ.chartMapHom T f ≫ dP.fibreHom T f = hψ.chartIncl T f ≫ dQ.fibreHom T f :=
  (dP.pointEquivOver T f (hψ.chartIncl T f ≫ dQ.fibreHom T f)
    ⟨hψ.chartToSubfunctor T f ≫ hψ.relativeMapSpaceHom, hψ.chartToSubfunctor_comp T f⟩).2

/-- `chartMapHom` followed by `P ×_X T ⟶ P` is the chart map into `U(ψ)` followed by
`r_ψ : U(ψ) ⟶ P`. -/
@[reassoc]
theorem yoneda_map_chartMapHom_fibreToSpace (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    yoneda.map (hψ.chartMapHom T f) ≫ dP.fibreToSpace T f =
      hψ.chartToSubfunctor T f ≫ hψ.relativeMapSpaceHom :=
  dP.map_pointEquivOver T f _ _

/-- The section of `Proj_T(ℬ|_T)` attached to the chart is the inclusion of `U(ψ|_T)`, read
through `chartSchemeIso`. -/
theorem sectionOfPoint_chart (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    (hu : (yoneda.map (hψ.chartIncl T f) ≫ dQ.fibreToSpace T f) ≫ πQ =
      yoneda.map (hψ.chartIncl T f ≫ dQ.fibreHom T f) ≫ f) :
    dQ.sectionOfPoint T f (hψ.chartIncl T f ≫ dQ.fibreHom T f)
        (yoneda.map (hψ.chartIncl T f) ≫ dQ.fibreToSpace T f) hu =
      (hψ.chartSchemeIso T f).hom ≫ (hψ.hom T f).relativeMapDomain.ι := by
  rw [dQ.sectionOfPoint_restrict T f (dQ.fibreHom T f) (hψ.chartIncl T f)
    (dQ.fibreToSpace T f) (dQ.isPullback T f).w hu, dQ.sectionOfPoint_fibreToSpace,
    chartSchemeIso_hom_ι]

/-- A section of the relative Proj depends only on the point, not on the proof that it lies
over the base. -/
theorem _root_.AlgebraicGeometry.Space.RelativeProjPoints.sectionOfPoint_congr
    (d : RelativeProjPoints B S hS πP) (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) {u v : yoneda.obj T' ⟶ P} (huv : u = v)
    (hu : u ≫ πP = yoneda.map r ≫ f) (hv : v ≫ πP = yoneda.map r ≫ f) :
    d.sectionOfPoint T f r u hu = d.sectionOfPoint T f r v hv := by
  subst huv
  rfl

/-- **On the chart, `r_ψ` is the morphism `r_{ψ|_T}` of Tag 07ZG**, through the identifications
of `U(ψ) ×_X T` with `U(ψ|_T)` and of `P ×_X T` with `Proj_T(𝒜|_T)`. -/
theorem toScheme_map_chartMapHom (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) :
    (BigFppfOver.toScheme B S hS).map (hψ.chartMapHom T f) ≫ (dP.fibreIso T f).hom =
      (hψ.chartSchemeIso T f).hom ≫ relativeMapHom (hψ.hom T f) := by
  have hu : (yoneda.map (hψ.chartIncl T f) ≫ dQ.fibreToSpace T f) ≫ πQ =
      yoneda.map (hψ.chartIncl T f ≫ dQ.fibreHom T f) ≫ f := by
    rw [Category.assoc, (dQ.isPullback T f).w, CategoryTheory.Functor.map_comp, Category.assoc]
  have hx : yonedaEquiv (yoneda.map (hψ.chartIncl T f) ≫ dQ.fibreToSpace T f) ∈
      hψ.relativeMapSubfunctor.obj (op (hψ.chartObj T f)) := by
    rw [← hψ.chartToSubfunctor_ι, yonedaEquiv_comp]
    exact (yonedaEquiv (hψ.chartToSubfunctor T f)).2
  have hd : IsDefinedOn dP dQ hψ.hom T f (hψ.chartIncl T f ≫ dQ.fibreHom T f)
      (yoneda.map (hψ.chartIncl T f) ≫ dQ.fibreToSpace T f) hu :=
    (hψ.mem_relativeMapSubfunctor_iff T f _ _ hu).1 hx
  have hpt : hψ.chartToSubfunctor T f ≫ hψ.relativeMapSpaceHom =
      pointHomOn dP dQ hψ.hom T f (hψ.chartIncl T f ≫ dQ.fibreHom T f)
        (yoneda.map (hψ.chartIncl T f) ≫ dQ.fibreToSpace T f) hu hd := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, ← hψ.app_relativeMapSpaceHom T f _ _ hu hd hx]
    congr 1
  show (dP.pointEquivProjOver T f _ ⟨_, _⟩).1 = _
  refine (dP.sectionOfPoint_congr T f _ hpt _ (pointHomOn_comp dP dQ hψ.hom T f _ _ hu hd)).trans ?_
  rw [sectionOfPoint_pointHomOn]
  congr 1
  exact (liftToOpens_unique _ _ hd _ (hψ.sectionOfPoint_chart T f hu).symm).symm

/-! ### The chart over an étale atlas, and morphisms between charts -/

/-- A property of morphisms of the site, read on presheaves, passes from the point `f` of the base
to the chart map into `U(ψ)`. -/
private theorem presheaf_chartToSubfunctor (W : MorphismProperty (BigFppfOver B S hS))
    (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X) (hf : W.presheaf f) :
    W.presheaf (hψ.chartToSubfunctor T f) :=
  (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
    (hψ.isPullback_chartToSubfunctor T f).flip
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (dQ.isPullback T f).flip hf)

/-- The chart is étale over `U(ψ)` as soon as the point of the base is. -/
theorem etale_chartToSubfunctor (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    (hf : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hψ.chartToSubfunctor T f) :=
  hψ.presheaf_chartToSubfunctor _ T f hf

/-- The chart is surjective onto `U(ψ)` as soon as the point of the base is surjective. -/
theorem surjective_chartToSubfunctor (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    (hf : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf f) :
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hψ.chartToSubfunctor T f) :=
  hψ.presheaf_chartToSubfunctor _ T f hf

section Transition

variable {T T' : BigFppfOver B S hS} {f : yoneda.obj T ⟶ X} {f' : yoneda.obj T' ⟶ X}

/-- A morphism of fibres of `Q` over `X` maps the chart of `U(ψ)` into the chart. -/
theorem range_chartIncl_comp_subset (cQ : dQ.fibre T' f' ⟶ dQ.fibre T f)
    (hcQ : yoneda.map cQ ≫ dQ.fibreToSpace T f = dQ.fibreToSpace T' f') :
    Set.range ((BigFppfOver.toScheme B S hS).map (hψ.chartIncl T' f' ≫ cQ)) ⊆
      (hψ.chartDomain T f : Set _) := by
  rw [← hψ.mem_relativeMapSubfunctor_fibre_iff, CategoryTheory.Functor.map_comp, Category.assoc,
    hcQ, ← hψ.chartToSubfunctor_ι, yonedaEquiv_comp]
  exact (yonedaEquiv (hψ.chartToSubfunctor T' f')).2

/-- **A morphism of fibres of `Q` restricts to the charts of `U(ψ)`.** -/
def chartTransition (cQ : dQ.fibre T' f' ⟶ dQ.fibre T f)
    (hcQ : yoneda.map cQ ≫ dQ.fibreToSpace T f = dQ.fibreToSpace T' f') :
    hψ.chartObj T' f' ⟶ hψ.chartObj T f :=
  openSubLift _ _ (hψ.chartIncl T' f' ≫ cQ) (fun y =>
    hψ.range_chartIncl_comp_subset cQ hcQ ⟨y, rfl⟩)

/-- `chartTransition` commutes with the inclusions of the charts into the fibres. -/
@[reassoc]
theorem chartTransition_chartIncl (cQ : dQ.fibre T' f' ⟶ dQ.fibre T f)
    (hcQ : yoneda.map cQ ≫ dQ.fibreToSpace T f = dQ.fibreToSpace T' f') :
    hψ.chartTransition cQ hcQ ≫ hψ.chartIncl T f = hψ.chartIncl T' f' ≫ cQ :=
  openSubLift_comp_openSubHom _ _ _ _

/-- `chartTransition` commutes with the chart maps into `U(ψ)`. -/
@[reassoc]
theorem yoneda_map_chartTransition_chartToSubfunctor (cQ : dQ.fibre T' f' ⟶ dQ.fibre T f)
    (hcQ : yoneda.map cQ ≫ dQ.fibreToSpace T f = dQ.fibreToSpace T' f') :
    yoneda.map (hψ.chartTransition cQ hcQ) ≫ hψ.chartToSubfunctor T f =
      hψ.chartToSubfunctor T' f' := by
  rw [← cancel_mono hψ.relativeMapSubfunctor.ι, Category.assoc, chartToSubfunctor_ι,
    ← Category.assoc, ← CategoryTheory.Functor.map_comp, chartTransition_chartIncl,
    CategoryTheory.Functor.map_comp, Category.assoc, hcQ, chartToSubfunctor_ι]

/-- **The charts of `r_ψ` are compatible with morphisms of fibres** lying over a morphism of the
test objects. -/
theorem chartTransition_chartMapHom (cQ : dQ.fibre T' f' ⟶ dQ.fibre T f)
    (hcQ : yoneda.map cQ ≫ dQ.fibreToSpace T f = dQ.fibreToSpace T' f') (k : T' ⟶ T)
    (cP : dP.fibre T' f' ⟶ dP.fibre T f)
    (hcP : yoneda.map cP ≫ dP.fibreToSpace T f = dP.fibreToSpace T' f')
    (hcPk : cP ≫ dP.fibreHom T f = dP.fibreHom T' f' ≫ k)
    (hcQk : cQ ≫ dQ.fibreHom T f = dQ.fibreHom T' f' ≫ k) :
    hψ.chartTransition cQ hcQ ≫ hψ.chartMapHom T f = hψ.chartMapHom T' f' ≫ cP := by
  apply Yoneda.fullyFaithful.map_injective
  refine (dP.isPullback T f).hom_ext ?_ ?_
  · rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
      Category.assoc, yoneda_map_chartMapHom_fibreToSpace, hcP,
      yoneda_map_chartMapHom_fibreToSpace, yoneda_map_chartTransition_chartToSubfunctor_assoc]
  · rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    congr 1
    rw [Category.assoc, Category.assoc, chartMapHom_fibreHom, hcPk, chartMapHom_fibreHom_assoc,
      chartTransition_chartIncl_assoc, hcQk]

/-- The morphism `U(ψ|_{T'}) ⟶ U(ψ|_T)` of Tag 07ZG opens induced by a morphism of fibres. -/
def chartSchemeTransition (cQ : dQ.fibre T' f' ⟶ dQ.fibre T f)
    (hcQ : yoneda.map cQ ≫ dQ.fibreToSpace T f = dQ.fibreToSpace T' f') :
    (hψ.hom T' f').relativeMapDomain.toScheme ⟶ (hψ.hom T f).relativeMapDomain.toScheme :=
  (hψ.chartSchemeIso T' f').inv ≫ (BigFppfOver.toScheme B S hS).map (hψ.chartTransition cQ hcQ) ≫
    (hψ.chartSchemeIso T f).hom

/-- `chartSchemeTransition` lies over the morphism of relative Projs of `ℬ`. -/
theorem chartSchemeTransition_ι (cQ : dQ.fibre T' f' ⟶ dQ.fibre T f)
    (hcQ : yoneda.map cQ ≫ dQ.fibreToSpace T f = dQ.fibreToSpace T' f') :
    hψ.chartSchemeTransition cQ hcQ ≫ (hψ.hom T f).relativeMapDomain.ι =
      (hψ.hom T' f').relativeMapDomain.ι ≫
        ((dQ.fibreIso T' f').inv ≫ (BigFppfOver.toScheme B S hS).map cQ ≫
          (dQ.fibreIso T f).hom) := by
  have h' := hψ.chartSchemeIso_hom_ι T' f'
  have hinv : (hψ.chartSchemeIso T' f').inv ≫ (BigFppfOver.toScheme B S hS).map
      (hψ.chartIncl T' f') = (hψ.hom T' f').relativeMapDomain.ι ≫ (dQ.fibreIso T' f').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, h', Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hm : (BigFppfOver.toScheme B S hS).map (hψ.chartTransition cQ hcQ) ≫
      (BigFppfOver.toScheme B S hS).map (hψ.chartIncl T f) =
      (BigFppfOver.toScheme B S hS).map (hψ.chartIncl T' f') ≫
        (BigFppfOver.toScheme B S hS).map cQ := by
    rw [← Functor.map_comp, ← Functor.map_comp, chartTransition_chartIncl]
  rw [chartSchemeTransition, Category.assoc, Category.assoc, chartSchemeIso_hom_ι,
    ← Category.assoc ((BigFppfOver.toScheme B S hS).map _), hm]
  simp only [← Category.assoc]
  rw [hinv]

/-- `chartSchemeTransition` is compatible with the morphisms of Tag 07ZG. -/
theorem relativeMapHom_comp_chartSchemeTransition (cQ : dQ.fibre T' f' ⟶ dQ.fibre T f)
    (hcQ : yoneda.map cQ ≫ dQ.fibreToSpace T f = dQ.fibreToSpace T' f') (k : T' ⟶ T)
    (cP : dP.fibre T' f' ⟶ dP.fibre T f)
    (hcP : yoneda.map cP ≫ dP.fibreToSpace T f = dP.fibreToSpace T' f')
    (hcPk : cP ≫ dP.fibreHom T f = dP.fibreHom T' f' ≫ k)
    (hcQk : cQ ≫ dQ.fibreHom T f = dQ.fibreHom T' f' ≫ k) :
    relativeMapHom (hψ.hom T' f') ≫
        ((dP.fibreIso T' f').inv ≫ (BigFppfOver.toScheme B S hS).map cP ≫ (dP.fibreIso T f).hom) =
      hψ.chartSchemeTransition cQ hcQ ≫ relativeMapHom (hψ.hom T f) := by
  have h' := hψ.toScheme_map_chartMapHom T' f'
  have h := hψ.toScheme_map_chartMapHom T f
  have hr' : relativeMapHom (hψ.hom T' f') = (hψ.chartSchemeIso T' f').inv ≫
      (BigFppfOver.toScheme B S hS).map (hψ.chartMapHom T' f') ≫ (dP.fibreIso T' f').hom := by
    rw [h', Iso.inv_hom_id_assoc]
  have hm : (BigFppfOver.toScheme B S hS).map (hψ.chartTransition cQ hcQ) ≫
      (BigFppfOver.toScheme B S hS).map (hψ.chartMapHom T f) =
      (BigFppfOver.toScheme B S hS).map (hψ.chartMapHom T' f') ≫
        (BigFppfOver.toScheme B S hS).map cP := by
    rw [← Functor.map_comp, ← Functor.map_comp,
      hψ.chartTransition_chartMapHom cQ hcQ k cP hcP hcPk hcQk]
  rw [hr', chartSchemeTransition]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← h, ← Category.assoc ((BigFppfOver.toScheme B S hS).map (hψ.chartTransition cQ hcQ)), hm,
    Category.assoc]

end Transition

/-! ### The presentation of `U(ψ)` over a presentation of the base -/

section Presentation

variable {hX : IsAlgebraicSpace B S hS X} (Px : Presentation B S hS X hX)
  (cT cS : dQ.fibre Px.R (yoneda.map Px.target ≫ Px.toSpace) ⟶ dQ.fibre Px.U Px.toSpace)
  (hcT : yoneda.map cT ≫ dQ.fibreToSpace Px.U Px.toSpace =
    dQ.fibreToSpace Px.R (yoneda.map Px.target ≫ Px.toSpace))
  (hcS : yoneda.map cS ≫ dQ.fibreToSpace Px.U Px.toSpace =
    dQ.fibreToSpace Px.R (yoneda.map Px.target ≫ Px.toSpace))
  (hK : IsPullback (yoneda.map cT) (yoneda.map cS) (dQ.fibreToSpace Px.U Px.toSpace)
    (dQ.fibreToSpace Px.U Px.toSpace))

include hK in
/-- **The charts of `U(ψ)` over `U` and `R` form a kernel pair**:
`U(ψ)_R = U(ψ)_U ×_{U(ψ)} U(ψ)_U`, for `Q_R = Q_U ×_Q Q_U` presented by two morphisms of fibres
over `Q`. -/
theorem isPullback_chartTransition :
    IsPullback (yoneda.map (hψ.chartTransition cT hcT)) (yoneda.map (hψ.chartTransition cS hcS))
      (hψ.chartToSubfunctor Px.U Px.toSpace) (hψ.chartToSubfunctor Px.U Px.toSpace) := by
  have hR := hψ.isPullback_chartToSubfunctor Px.R (yoneda.map Px.target ≫ Px.toSpace)
  rw [← hcT] at hR
  refine IsPullback.kernelPair_of_baseChange (hψ.isPullback_chartToSubfunctor Px.U Px.toSpace)
    hR hK ?_ ?_ (hψ.yoneda_map_chartTransition_chartToSubfunctor cT hcT)
    (hψ.yoneda_map_chartTransition_chartToSubfunctor cS hcS) <;>
  rw [← Functor.map_comp, chartTransition_chartIncl, Functor.map_comp]

/-- **The étale presentation of `U(ψ)` over an étale presentation `X = U/R`** of the base:
`U(ψ)_U = U(ψ) ×_X U` and `U(ψ)_R = U(ψ) ×_X R`, the charts of
`AlgebraicGeometry.Space.RelativeProjHomPoints.chartObj`, with the projections restricted from
two morphisms `Q_R ⇉ Q_U` presenting `Q_R` as `Q_U ×_Q Q_U`. -/
def chartPresentation (hG : IsAlgebraicSpace B S hS hψ.relativeMapSubfunctor.toFunctor) :
    Presentation B S hS hψ.relativeMapSubfunctor.toFunctor hG where
  U := hψ.chartObj Px.U Px.toSpace
  R := hψ.chartObj Px.R (yoneda.map Px.target ≫ Px.toSpace)
  target := hψ.chartTransition cT hcT
  source := hψ.chartTransition cS hcS
  isEtaleEquivalenceRelation := by
    have hP := hψ.isPullback_chartTransition Px cT cS hcT hcS hK
    have hEt := hψ.etale_chartToSubfunctor Px.U Px.toSpace Px.etale
    have hRel := isEquivalenceRelation_of_isPullback B S hS
      (hψ.chartToSubfunctor Px.U Px.toSpace) _ _ hP
    have hSe : Etale ((BigFppfOver.toScheme B S hS).map (hψ.chartTransition cS hcS)) :=
      hEt.property _ _ _ hP
    have hTe : Etale ((BigFppfOver.toScheme B S hS).map (hψ.chartTransition cT hcT)) :=
      hEt.property _ _ _ hP.flip
    refine { isEquivalenceRelation := ?_, etale_source := ?_, etale_target := ?_ }
    · simp only [Stacks.Groupoids.PreRelation.target, Stacks.Groupoids.PreRelation.source,
        prod.lift_fst, prod.lift_snd]
      exact hRel
    · simp only [Stacks.Groupoids.PreRelation.source, prod.lift_snd]
      exact hSe
    · simp only [Stacks.Groupoids.PreRelation.target, prod.lift_fst]
      exact hTe
  toSpace := hψ.chartToSubfunctor Px.U Px.toSpace
  surjective := hψ.surjective_chartToSubfunctor Px.U Px.toSpace Px.surjective
  etale := hψ.etale_chartToSubfunctor Px.U Px.toSpace Px.etale
  isPullback := hψ.isPullback_chartTransition Px cT cS hcT hcS hK

/-- The source projection of the presentation `Q = Q_U / Q_R` lies over the atlas of `Q`. -/
theorem _root_.AlgebraicGeometry.Space.RelativeProjPoints.map_presentationSource_comp_fibreToSpace
    (d : RelativeProjPoints B S hS πQ) :
    yoneda.map (d.presentationSource Px) ≫ d.fibreToSpace Px.U Px.toSpace =
      d.fibreToSpace Px.R (yoneda.map Px.target ≫ Px.toSpace) :=
  (d.map_presentationTarget_comp_fibreToSpace Px).symm.trans
    (d.map_fibreComparison_comp_fibreToSpace _ _ _)

/-- **The étale presentation of `U(ψ)` over an étale presentation `X = U/R`**, restricted from the
presentation `Q = Q_U / Q_R` by the comparison morphisms of Stacks 084B (3)
(`AlgebraicGeometry.Space.RelativeProjPoints.presentation`). -/
def presentationOfBase (hG : IsAlgebraicSpace B S hS hψ.relativeMapSubfunctor.toFunctor) :
    Presentation B S hS hψ.relativeMapSubfunctor.toFunctor hG :=
  hψ.chartPresentation Px (dQ.presentationTarget Px) (dQ.presentationSource Px)
    (dQ.map_fibreComparison_comp_fibreToSpace _ _ _)
    (dQ.map_presentationSource_comp_fibreToSpace Px)
    (dQ.isPullback_presentationTarget_presentationSource Px) hG

variable (hG : IsAlgebraicSpace B S hS hψ.relativeMapSubfunctor.toFunctor)

/-- The target projection of `presentationOfBase` lies over the target projection
`R ×_X P ⟶ U ×_X P` along the charts of `r_ψ`. -/
theorem presentationOfBase_target_comp_chartMapHom :
    CategoryStruct.comp (X := (hψ.presentationOfBase Px hG).R)
        (Y := (hψ.presentationOfBase Px hG).U) (Z := dP.fibre Px.U Px.toSpace)
        (hψ.presentationOfBase Px hG).target (hψ.chartMapHom Px.U Px.toSpace) =
      CategoryStruct.comp (X := (hψ.presentationOfBase Px hG).R)
        (Y := dP.fibre Px.R (RelativeProjPoints.relationPoint Px)) (Z := dP.fibre Px.U Px.toSpace)
        (hψ.chartMapHom Px.R (RelativeProjPoints.relationPoint Px)) (dP.presentationTarget Px) :=
  hψ.chartTransition_chartMapHom (dQ.presentationTarget Px)
    (dQ.map_fibreComparison_comp_fibreToSpace _ _ _) Px.target (dP.presentationTarget Px)
    (dP.map_fibreComparison_comp_fibreToSpace _ _ _) (dP.fibreComparison_comp_fibreHom _ _ _)
    (dQ.fibreComparison_comp_fibreHom _ _ _)

/-- The source projection of `presentationOfBase` lies over the source projection
`R ×_X P ⟶ U ×_X P` along the charts of `r_ψ`. -/
theorem chartMapHom_comp_presentationOfBase_source :
    CategoryStruct.comp (X := (hψ.presentationOfBase Px hG).R)
        (Y := dP.fibre Px.R (RelativeProjPoints.relationPoint Px)) (Z := dP.fibre Px.U Px.toSpace)
        (hψ.chartMapHom Px.R (RelativeProjPoints.relationPoint Px)) (dP.presentationSource Px) =
      CategoryStruct.comp (X := (hψ.presentationOfBase Px hG).R)
        (Y := (hψ.presentationOfBase Px hG).U) (Z := dP.fibre Px.U Px.toSpace)
        (hψ.presentationOfBase Px hG).source (hψ.chartMapHom Px.U Px.toSpace) :=
  (hψ.chartTransition_chartMapHom (dQ.presentationSource Px)
    (dQ.map_presentationSource_comp_fibreToSpace Px) Px.source (dP.presentationSource Px)
    (dP.map_presentationSource_comp_fibreToSpace Px) (dP.presentationSource_comp_fibreHom Px)
    (dQ.presentationSource_comp_fibreHom Px)).symm

/-- The target projection of `presentationOfBase` lies over the target projection
`R ×_X Q ⟶ U ×_X Q` along the inclusions of the charts. -/
theorem presentationOfBase_target_comp_chartIncl :
    CategoryStruct.comp (X := (hψ.presentationOfBase Px hG).R)
        (Y := (hψ.presentationOfBase Px hG).U) (Z := dQ.fibre Px.U Px.toSpace)
        (hψ.presentationOfBase Px hG).target (hψ.chartIncl Px.U Px.toSpace) =
      CategoryStruct.comp (X := (hψ.presentationOfBase Px hG).R)
        (Y := dQ.fibre Px.R (RelativeProjPoints.relationPoint Px)) (Z := dQ.fibre Px.U Px.toSpace)
        (hψ.chartIncl Px.R (RelativeProjPoints.relationPoint Px)) (dQ.presentationTarget Px) :=
  hψ.chartTransition_chartIncl (dQ.presentationTarget Px)
    (dQ.map_fibreComparison_comp_fibreToSpace _ _ _)

/-- The source projection of `presentationOfBase` lies over the source projection
`R ×_X Q ⟶ U ×_X Q` along the inclusions of the charts. -/
theorem chartIncl_comp_presentationOfBase_source :
    CategoryStruct.comp (X := (hψ.presentationOfBase Px hG).R)
        (Y := dQ.fibre Px.R (RelativeProjPoints.relationPoint Px)) (Z := dQ.fibre Px.U Px.toSpace)
        (hψ.chartIncl Px.R (RelativeProjPoints.relationPoint Px)) (dQ.presentationSource Px) =
      CategoryStruct.comp (X := (hψ.presentationOfBase Px hG).R)
        (Y := (hψ.presentationOfBase Px hG).U) (Z := dQ.fibre Px.U Px.toSpace)
        (hψ.presentationOfBase Px hG).source (hψ.chartIncl Px.U Px.toSpace) :=
  (hψ.chartTransition_chartIncl (dQ.presentationSource Px)
    (dQ.map_presentationSource_comp_fibreToSpace Px)).symm

end Presentation

end RelativeProjHomPoints

end AlgebraicGeometry.Space

end
