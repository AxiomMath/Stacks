module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms

/-!
# Étale morphisms of algebraic spaces

Étaleness of a morphism of algebraic spaces over `S` can be tested on charts, and the resulting
criteria give its permanence properties.

The chart criteria compare étaleness of `f : F ⟶ G` with

* étaleness of `p ≫ f` for one surjective étale chart `p` of the source;
* étaleness of the base change of `f` along one surjective étale chart `q` of the target;
* the existence of a commuting square of charts `p` of `F` and `q` of `G`, with `p`
  surjective étale, `q` étale and the morphism of schemes between them étale.

The permanence properties are composition, base change, and cancellation of two morphisms étale
over a common target.

## Main results

* `AlgebraicGeometry.Space.isEtale_iff_exists_source_chart`,
  `AlgebraicGeometry.Space.isEtale_iff_exists_target_chart`,
  `AlgebraicGeometry.Space.isEtale_iff_exists_etale_chart_square`: the three chart criteria
  for étaleness.
* `AlgebraicGeometry.Space.isEtale_comp`: a composite of étale morphisms is étale.
* `AlgebraicGeometry.Space.isEtale_of_isPullback_yoneda`: étaleness of a morphism with
  representable source is stable under base change.
* `AlgebraicGeometry.Space.isEtale_of_isPullback`: a base change of an étale morphism of
  algebraic spaces is étale.
* `AlgebraicGeometry.Space.isEtale_of_isEtale_over`: a morphism between algebraic spaces étale
  over a common algebraic space is étale.

## References

* [Stacks Project, Tag 03FS](https://stacks.math.columbia.edu/tag/03FS)
* [Stacks Project, Tag 03FT](https://stacks.math.columbia.edu/tag/03FT)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 03FV](https://stacks.math.columbia.edu/tag/03FV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Étaleness of morphisms of presheaves on the big fppf site is stable under base change. -/
private instance presheaf_etale_isStableUnderBaseChange :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
  have := inverseImage_isStableUnderBaseChange B S hS
    AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
  MorphismProperty.relative_isStableUnderBaseChange _

/-- Surjectivity of morphisms of presheaves on the big fppf site is stable under base change. -/
private instance presheaf_surjective_isStableUnderBaseChange :
    (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
  have := inverseImage_isStableUnderBaseChange B S hS (inferInstance :
    MorphismProperty.IsStableUnderBaseChange (@AlgebraicGeometry.Surjective.{u}))
  MorphismProperty.relative_isStableUnderBaseChange _

/-- The composite of two étale morphisms of presheaves on the big fppf site of `S` is étale. -/
@[stacks 03FT, stacks 0465 "the composition of two etale morphisms of algebraic spaces is etale"]
theorem isEtale_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G} {g : G ⟶ H}
    (hf : IsEtale B S hS f) (hg : IsEtale B S hS g) : IsEtale B S hS (f ≫ g) :=
  fun _ _ hφ ↦ by simpa using hg _ _ (hf _ _ hφ)

/-- For a chart of a presheaf on the big fppf site of `S`, étaleness as a morphism of
algebraic spaces and the relatively representable étaleness property agree. -/
theorem isEtale_iff_presheaf_of_yoneda {U : BigFppfOver B S hS}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : yoneda.obj U ⟶ F) :
    IsEtale B S hS g ↔
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf g := by
  constructor
  · intro hg
    have hid : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (𝟙 (yoneda.obj U)) := by
      simpa using (presheaf_yoneda_map_etale_iff B S hS (𝟙 U)).2 inferInstance
    simpa using hg U (𝟙 (yoneda.obj U)) hid
  · intro hg T φ hφ
    have hρ := prop_preimage_of_presheaf B S hS
      AlgebraicGeometry.Etale.etale_isStableUnderBaseChange φ hφ
    simpa using etale_comp_of_scheme B S hS (yoneda.preimage φ) g hρ hg

/-- Étaleness of a morphism with representable source is stable under base change: in a pullback
square, the base change of an étale morphism `g : yoneda.obj U ⟶ G` along `f : F ⟶ G` is étale. -/
theorem isEtale_of_isPullback_yoneda
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {R U : BigFppfOver B S hS}
    {g : yoneda.obj U ⟶ G} {f : F ⟶ G}
    {f' : yoneda.obj R ⟶ yoneda.obj U} {g' : yoneda.obj R ⟶ F}
    (sq : IsPullback f' g' g f) (hg : IsEtale B S hS g) : IsEtale B S hS g' :=
  (isEtale_iff_presheaf_of_yoneda B S hS g').2
    (MorphismProperty.IsStableUnderBaseChange.of_isPullback sq
      ((isEtale_iff_presheaf_of_yoneda B S hS g).1 hg))

/-- A morphism of algebraic spaces over `S` is étale exactly when its composite with some
surjective étale chart of its source is étale. -/
@[stacks 03FS "condition (2)"]
theorem isEtale_iff_exists_source_chart {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) :
    IsEtale B S hS f ↔
      ∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ F),
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf p ∧
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf p ∧
        IsEtale B S hS (p ≫ f) := by
  constructor
  · intro hf
    obtain ⟨U, p, hp_surj, hp_etale⟩ := hF.exists_atlas
    exact ⟨U, p, hp_surj, hp_etale,
      (isEtale_iff_presheaf_of_yoneda B S hS (p ≫ f)).2 (hf U p hp_etale)⟩
  · rintro ⟨P, p, hp_surj, hp_etale, hpf⟩
    intro T φ hφ
    obtain ⟨W, r, α, hcomm, hr_surj, hr_etale⟩ :=
      exists_surjective_etale_presentation_lift B S hS
        (isAlgebraicSpace_yoneda B S hS T) hF φ P p hp_surj hp_etale
    have hρ_surj := prop_preimage_of_presheaf B S hS
      (inferInstance :
        MorphismProperty.IsStableUnderBaseChange (@AlgebraicGeometry.Surjective.{u})) r hr_surj
    have hρ_etale := prop_preimage_of_presheaf B S hS
      AlgebraicGeometry.Etale.etale_isStableUnderBaseChange r hr_etale
    have hmap : yoneda.map (yoneda.preimage r) = r := yoneda.map_preimage r
    have hrφ := MorphismProperty.comp_mem _ r φ hr_etale hφ
    have hα : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map α) :=
      etale_of_etale_charts B S hS (r ≫ φ) p hrφ hp_etale α hcomm.symm
    have hαp : (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map α ≫ p ≫ f) :=
      etale_comp_of_scheme B S hS α (p ≫ f) hα
        ((isEtale_iff_presheaf_of_yoneda B S hS (p ≫ f)).1 hpf)
    apply etale_of_comp_surjective_etale B S hS hG (yoneda.preimage r) (φ ≫ f)
    rw [← Category.assoc, hmap, hcomm]
    exact hαp

/-- A morphism of algebraic spaces over `S` is étale exactly when its base change along some
surjective étale chart of its target is étale. -/
@[stacks 03FS "condition (3)"]
theorem isEtale_iff_exists_target_chart {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (_hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) :
    IsEtale B S hS f ↔
      ∃ (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ G),
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf q ∧
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf q ∧
        IsEtale B S hS (pullback.snd f q) := by
  let QEtale := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  let QSurj := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS)
  have fst_mem {V : BigFppfOver B S hS} {Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u)}
      [Q.IsStableUnderBaseChange] {q : yoneda.obj V ⟶ G} (hq : Q q) : Q (pullback.fst f q) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f q).flip hq
  constructor
  · intro hf
    obtain ⟨V, q, hq_surj, hq_etale⟩ := hG.exists_atlas
    have hfst : QEtale.presheaf (pullback.fst f q) := fst_mem hq_etale
    refine ⟨V, q, hq_surj, hq_etale, fun T η hη => ?_⟩
    have hcomp := hf T (η ≫ pullback.fst f q)
      (MorphismProperty.comp_mem QEtale.presheaf η (pullback.fst f q) hη hfst)
    have hcompat : yoneda.map (yoneda.preimage (η ≫ pullback.snd f q)) ≫ q =
        (η ≫ pullback.fst f q) ≫ f := by
      rw [Functor.map_preimage, Category.assoc, Category.assoc, pullback.condition]
    have hβ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map
        (yoneda.preimage (η ≫ pullback.snd f q))) :=
      etale_of_etale_charts B S hS ((η ≫ pullback.fst f q) ≫ f) q hcomp hq_etale _ hcompat
    rw [← yoneda.map_preimage (η ≫ pullback.snd f q)]
    exact (presheaf_yoneda_map_etale_iff B S hS _).2 hβ
  · rintro ⟨V, q, hq_surj, hq_etale, hg⟩
    have hfst : QEtale.presheaf (pullback.fst f q) := fst_mem hq_etale
    have hfst_surj : QSurj.presheaf (pullback.fst f q) := fst_mem hq_surj
    have hχrep : yoneda.relativelyRepresentable (pullback.fst f q) := hfst.1
    intro T φ hφ
    have hWpb := hχrep.isPullback φ
    have hχ_surj : AlgebraicGeometry.Surjective
        ((BigFppfOver.toScheme B S hS).map (hχrep.snd φ)) :=
      hfst_surj.2 φ (hχrep.fst φ) (hχrep.snd φ) hWpb
    have hχ_etale : AlgebraicGeometry.Etale
        ((BigFppfOver.toScheme B S hS).map (hχrep.snd φ)) :=
      hfst.2 φ (hχrep.fst φ) (hχrep.snd φ) hWpb
    have hη : QEtale.presheaf (hχrep.fst φ) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hWpb.flip hφ
    have hηgq : QEtale.presheaf ((hχrep.fst φ ≫ pullback.snd f q) ≫ q) :=
      MorphismProperty.comp_mem QEtale.presheaf _ q (hg _ (hχrep.fst φ) hη) hq_etale
    have hcompat : (hχrep.fst φ ≫ pullback.snd f q) ≫ q =
        (yoneda.map (hχrep.snd φ) ≫ φ) ≫ f := by
      calc (hχrep.fst φ ≫ pullback.snd f q) ≫ q
            = hχrep.fst φ ≫ (pullback.snd f q ≫ q) := by rw [Category.assoc]
        _ = hχrep.fst φ ≫ (pullback.fst f q ≫ f) := by rw [pullback.condition]
        _ = (hχrep.fst φ ≫ pullback.fst f q) ≫ f := by rw [Category.assoc]
        _ = (yoneda.map (hχrep.snd φ) ≫ φ) ≫ f := by rw [hWpb.w]
    refine etale_of_comp_surjective_etale B S hS hG (hχrep.snd φ) (φ ≫ f) ?_
    have : QEtale.presheaf ((yoneda.map (hχrep.snd φ) ≫ φ) ≫ f) := hcompat ▸ hηgq
    simpa only [Category.assoc] using this

/-- A morphism of algebraic spaces over `S` is étale exactly when it fits in a commuting square
of charts, with the chart of the source surjective and étale, the chart of the target étale, and
the morphism of schemes between them étale. -/
@[stacks 03FS "condition (4)"]
theorem isEtale_iff_exists_etale_chart_square {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) :
    IsEtale B S hS f ↔
      ∃ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ F) (q : yoneda.obj V ⟶ G) (α : U ⟶ V),
        p ≫ f = yoneda.map α ≫ q ∧
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf p ∧
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf p ∧
        (MorphismProperty.inverseImage
          (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)).presheaf q ∧
        AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map α) := by
  constructor
  · intro hf
    obtain ⟨V, q, hq_surj, hq_etale⟩ := hG.exists_atlas
    obtain ⟨U, p, α, hcomm, hp_surj, hp_etale⟩ :=
      exists_surjective_etale_presentation_lift B S hS hF hG f V q hq_surj hq_etale
    exact ⟨U, V, p, q, α, hcomm, hp_surj, hp_etale, hq_etale,
      etale_of_etale_charts B S hS (p ≫ f) q (hf U p hp_etale) hq_etale α hcomm.symm⟩
  · rintro ⟨U, V, p, q, α, hcomm, hp_surj, hp_etale, hq_etale, hα⟩
    rw [isEtale_iff_exists_source_chart B S hS hF hG f]
    refine ⟨U, p, hp_surj, hp_etale, fun T r hr => ?_⟩
    rw [hcomm]
    exact MorphismProperty.comp_mem _ r _ hr (etale_comp_of_scheme B S hS α q hα hq_etale)

/-- A base change of an étale morphism of algebraic spaces over `S` is étale. -/
@[stacks 03FU,
  stacks 0466 "the base change of an étale morphism of algebraic spaces is étale",
  sga "1 IX 1.3"]
theorem isEtale_of_isPullback {X' X Z Y : AlgebraicSpaces B S hS}
    (p : X' ⟶ X) (f' : X' ⟶ Z) (f : X ⟶ Y) (g : Z ⟶ Y)
    (h : IsPullback p f' f g) (hf : IsEtale B S hS f.hom) :
    IsEtale B S hS f'.hom := by
  let Tsch := BigFppfOver.toScheme B S hS
  let QEtale := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) Tsch
  let QSurj := MorphismProperty.inverseImage
    (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u}) Tsch
  obtain ⟨V, q, hqSurj, hqEtale, hfV⟩ :=
    (isEtale_iff_exists_target_chart B S hS X.property Y.property f.hom).mp hf
  let Vsp : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
  let qsp : Vsp ⟶ Y := ObjectProperty.homMk q
  let Fsp := AlgebraicSpaces.fiberProduct B S hS f qsp
  let toX : Fsp ⟶ X := ObjectProperty.homMk (pullback.fst f.hom q)
  let toV : Fsp ⟶ Vsp := ObjectProperty.homMk (pullback.snd f.hom q)
  have hFpb := AlgebraicSpaces.isPullback_fiberProduct B S hS f qsp
  have hFpb' : IsPullback toX.hom toV.hom f.hom q := IsPullback.of_hasPullback f.hom q
  obtain ⟨U, r, hrSurj, hrEtale, hrV⟩ :=
    (isEtale_iff_exists_source_chart B S hS Fsp.property Vsp.property toV.hom).mp hfV
  let α : U ⟶ V := yoneda.preimage (r ≫ toV.hom)
  have hmapα : yoneda.map α = r ≫ toV.hom := by simp [α]
  have hαPresheaf : QEtale.presheaf (yoneda.map α) := by
    rw [hmapα]
    exact (isEtale_iff_presheaf_of_yoneda B S hS (r ≫ toV.hom)).1 hrV
  have hαEtale : AlgebraicGeometry.Etale (Tsch.map α) :=
    (presheaf_yoneda_map_etale_iff B S hS α).1 hαPresheaf
  let pX := r ≫ toX.hom
  have hchart : pX ≫ f.hom = yoneda.map α ≫ q := by
    rw [hmapα]
    simpa only [pX, toX, toV, qsp, ObjectProperty.FullSubcategory.comp_hom,
      ObjectProperty.homMk_hom, Category.assoc] using congrArg (fun k ↦ r ≫ k.hom) hFpb.w
  let Usp : AlgebraicSpaces B S hS := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩
  let pXsp : Usp ⟶ X := ObjectProperty.homMk pX
  let αsp : Usp ⟶ Vsp := ObjectProperty.homMk (yoneda.map α)
  have hchartSp : pXsp ≫ f = αsp ≫ qsp := ObjectProperty.hom_ext _ hchart
  let Tfp := AlgebraicSpaces.fiberProduct B S hS qsp g
  let tV : Tfp ⟶ Vsp := ObjectProperty.homMk (pullback.fst qsp.hom g.hom)
  let tZ : Tfp ⟶ Z := ObjectProperty.homMk (pullback.snd qsp.hom g.hom)
  have hTpb := AlgebraicSpaces.isPullback_fiberProduct B S hS qsp g
  have hTpbRaw : IsPullback tV.hom tZ.hom qsp.hom g.hom :=
    IsPullback.of_hasPullback qsp.hom g.hom
  obtain ⟨W, w, hwSurj, hwEtale⟩ := Tfp.property.exists_atlas
  let Wsp : AlgebraicSpaces B S hS := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩
  let rT : Wsp ⟶ Tfp := ObjectProperty.homMk w
  let β : W ⟶ V := yoneda.preimage (rT.hom ≫ tV.hom)
  have hmapβ : yoneda.map β = rT.hom ≫ tV.hom := by simp [β]
  let βsp : Wsp ⟶ Vsp := ObjectProperty.homMk (yoneda.map β)
  have hβspEq : βsp = rT ≫ tV := ObjectProperty.hom_ext _ hmapβ
  let qWsp : Wsp ⟶ Z := rT ≫ tZ
  have hβq : βsp ≫ qsp = qWsp ≫ g := by
    rw [hβspEq]
    simpa only [qWsp, tV, tZ, Category.assoc] using congrArg (fun k ↦ rT ≫ k) hTpb.w
  have hqWEtale : QEtale.presheaf qWsp.hom :=
    MorphismProperty.comp_mem QEtale.presheaf rT.hom tZ.hom hwEtale
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hTpbRaw hqEtale)
  let Psite := pullback α β
  let πU : Psite ⟶ U := pullback.fst α β
  let πW : Psite ⟶ W := pullback.snd α β
  have hPsitePb : IsPullback πU πW α β := IsPullback.of_hasPullback α β
  let Psp : AlgebraicSpaces B S hS := ⟨yoneda.obj Psite, isAlgebraicSpace_yoneda B S hS Psite⟩
  let πUsp : Psp ⟶ Usp := ObjectProperty.homMk (yoneda.map πU)
  let πWsp : Psp ⟶ Wsp := ObjectProperty.homMk (yoneda.map πW)
  have hPfull : IsPullback πUsp πWsp αsp βsp :=
    IsPullback.of_map (ObjectProperty.ι _)
      (ObjectProperty.hom_ext _ (congrArg (fun k ↦ yoneda.map k) hPsitePb.w))
      (IsPullback.map yoneda hPsitePb)
  have hcompat : (πUsp ≫ pXsp) ≫ f = (πWsp ≫ qWsp) ≫ g := by
    calc (πUsp ≫ pXsp) ≫ f = (πUsp ≫ αsp) ≫ qsp := by
          simp only [Category.assoc, hchartSp]
      _ = (πWsp ≫ βsp) ≫ qsp := by rw [hPfull.w]
      _ = (πWsp ≫ qWsp) ≫ g := by simp only [Category.assoc, hβq]
  let qP : Psp ⟶ X' := h.lift (πUsp ≫ pXsp) (πWsp ≫ qWsp) hcompat
  have hqPp : qP ≫ p = πUsp ≫ pXsp := h.lift_fst _ _ hcompat
  have hqPf : qP ≫ f' = πWsp ≫ qWsp := h.lift_snd _ _ hcompat
  let A := AlgebraicSpaces.fiberProduct B S hS pXsp p
  let aU : A ⟶ Usp := ObjectProperty.homMk (pullback.fst pXsp.hom p.hom)
  let aX : A ⟶ X' := ObjectProperty.homMk (pullback.snd pXsp.hom p.hom)
  have hApb := AlgebraicSpaces.isPullback_fiberProduct B S hS pXsp p
  have hApbRaw : IsPullback aU.hom aX.hom pXsp.hom p.hom :=
    IsPullback.of_hasPullback pXsp.hom p.hom
  have hAcompat : (aU ≫ αsp) ≫ qsp = (aX ≫ f') ≫ g := by
    calc (aU ≫ αsp) ≫ qsp = (aU ≫ pXsp) ≫ f := by simp only [Category.assoc, ← hchartSp]
      _ = (aX ≫ f') ≫ g := by rw [hApb.w]; simp only [aX, Category.assoc, h.w]
  let aT : A ⟶ Tfp := hTpb.lift (aU ≫ αsp) (aX ≫ f') hAcompat
  have haTsnd : aT ≫ tZ = aX ≫ f' := hTpb.lift_snd _ _ hAcompat
  have hATcomm : aU ≫ αsp = aT ≫ tV := (hTpb.lift_fst _ _ hAcompat).symm
  have hBig : IsPullback aU (aT ≫ tZ) (αsp ≫ qsp) g := by
    rw [haTsnd, ← hchartSp]
    exact hApb.paste_vert h
  have hAT : IsPullback aU aT αsp tV := (hTpb.paste_vert_iff hATcomm).1 hBig
  let k : Psp ⟶ A := hApb.lift πUsp qP hqPp.symm
  have hkU : k ≫ aU = πUsp := hApb.lift_fst πUsp qP hqPp.symm
  have hkX : k ≫ aX = qP := hApb.lift_snd πUsp qP hqPp.symm
  have hkT : k ≫ aT = πWsp ≫ rT := by
    refine hTpb.hom_ext ?_ ?_
    · calc k ≫ aT ≫ tV = (k ≫ aU) ≫ αsp := by simp only [Category.assoc, ← hATcomm]
        _ = πWsp ≫ rT ≫ tV := by rw [hkU, hPfull.w, hβspEq]
    · calc k ≫ aT ≫ tZ = (k ≫ aX) ≫ f' := by simp only [Category.assoc, haTsnd]
        _ = πWsp ≫ rT ≫ tZ := by rw [hkX, hqPf]
  have hPA : IsPullback k πWsp aT rT := by
    refine (hAT.paste_horiz_iff hkT).mp ?_
    simpa [hkU, hβspEq] using hPfull
  have hqP : ∀ Q : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u),
      Q.IsStableUnderBaseChange → Q.IsStableUnderComposition → Q q → Q r → Q w → Q qP.hom := by
    intro Q _ _ hq hr hw
    rw [← congrArg (fun k ↦ k.hom) hkX]
    exact MorphismProperty.comp_mem Q k.hom aX.hom
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (hPA.flip.map (ObjectProperty.ι _)) hw)
      (MorphismProperty.IsStableUnderBaseChange.of_isPullback hApbRaw
        (MorphismProperty.comp_mem Q r toX.hom hr
          (MorphismProperty.IsStableUnderBaseChange.of_isPullback hFpb'.flip hq)))
  have hπWEtale : AlgebraicGeometry.Etale (Tsch.map πW) :=
    AlgebraicGeometry.Etale.etale_isStableUnderBaseChange.of_isPullback
      (hPsitePb.map Tsch) hαEtale
  exact (isEtale_iff_exists_etale_chart_square B S hS X'.property Z.property f'.hom).2
    ⟨Psite, W, qP.hom, qWsp.hom, πW, congrArg (fun k ↦ k.hom) hqPf,
      hqP QSurj.presheaf inferInstance inferInstance hqSurj hrSurj hwSurj,
      hqP QEtale.presheaf inferInstance inferInstance hqEtale hrEtale hwEtale, hqWEtale, hπWEtale⟩

/-- A morphism between two algebraic spaces which are étale over a common algebraic space is
itself étale. -/
@[stacks 03FV, stacks 05W3 "a morphism over Z between algebraic spaces étale over Z is étale"]
theorem isEtale_of_isEtale_over {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (_hH : IsAlgebraicSpace B S hS H) (f : F ⟶ G) (g : F ⟶ H) (h : G ⟶ H)
    (hg : IsEtale B S hS g) (hh : IsEtale B S hS h) (hfg : f ≫ h = g) :
    IsEtale B S hS f := by
  obtain ⟨V, q, hqs, hqe⟩ := hG.exists_atlas
  obtain ⟨U, p, α, hcomm, hps, hpe⟩ :=
    exists_surjective_etale_presentation_lift B S hS hF hG f V q hqs hqe
  refine (isEtale_iff_exists_etale_chart_square B S hS hF hG f).2
    ⟨U, V, p, q, α, hcomm, hps, hpe, hqe, ?_⟩
  refine etale_of_etale_charts B S hS (p ≫ g) (q ≫ h) (hg U p hpe) (hh V q hqe) α ?_
  simpa only [Category.assoc, hfg] using congrArg (· ≫ h) hcomm.symm

end AlgebraicGeometry.Space

end
