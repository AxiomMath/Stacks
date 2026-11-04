module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.HigherPushforwardQuasicoherentReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardRelation
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardAffineGeometry
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EtaleRelationChart
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae03KM

/-!
# The sections of a direct image over a chart, as an equalizer over an étale cover

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site `B`, let
`F` be an `𝒪_X`-module and let `e : W ⟶ V` be a chart diagram over `f`.  If `W ⟶ V ×_Y X` is
surjective, `R` is an étale scheme chart of `X` presenting `W ×_{V ×_Y X} W` by two morphisms
`t, s : R ⟶ W`, and `k : R' ⟶ R` is a surjective morphism of étale scheme charts, then the
projection of the sections of `f_*F` over `V` to the sections of `F` over `W` is injective with
image the equalizer of the restrictions along `k ≫ t` and `k ≫ s`.

## Main results

* `AlgebraicGeometry.Space.injective_modulePushforwardCounitApp`: injectivity.
* `AlgebraicGeometry.Space.exists_modulePushforwardCounitApp_eq`: the image is the equalizer.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

/-- The projection of the sections of a direct image to a chart, through the right Kan extension
along the comparison functor: the comparison with the Kan extension form, restriction along the
cartesian form of the chart diagram, and the counit of the Kan extension adjunction. -/
theorem modulePushforwardCounitApp_eq_ran (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (e : ChartDiagram B S hS X.1 Y.1 f.hom)
    (x : ((modulePushforward B S hS f).obj F).val.obj (op e.V)) :
    modulePushforwardCounitApp B S hS f F e x =
      ((comparisonAdjunction B S hS X).counit.app (moduleSetSheaf B S hS X F)).hom.app (op e.U)
        (((smallEtaleComparisonRan B S hS X).obj (moduleSetSheaf B S hS X F)).obj.map
          (chartLift B S hS f e).op
          (((smallEtaleDirectImageRanIso B S hS f).hom.app
            (moduleSetSheaf B S hS X F)).hom.app (op e.V) x)) := rfl

/-- The components of an isomorphism of sheaves of types are bijective. -/
theorem bijective_sheaf_hom_app {C : Type*} [Category C] {J : GrothendieckTopology C}
    {G H : Sheaf J (Type u)} (φ : G ⟶ H) [IsIso φ] (U : Cᵒᵖ) :
    Function.Bijective (φ.hom.app U) := by
  have : IsIso φ.hom := inferInstanceAs (IsIso ((sheafToPresheaf J _).map φ))
  rw [← isIso_iff_bijective]
  infer_instance

/-- The counit of the Kan extension adjunction of the comparison functor is bijective on
sections. -/
theorem bijective_comparisonAdjunction_counit (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    Function.Bijective (((comparisonAdjunction B S hS X).counit.app G).hom.app U) :=
  bijective_sheaf_hom_app _ U

/-- The comparison of the direct image with its right Kan extension form is bijective on
sections. -/
theorem bijective_smallEtaleDirectImageRanIso (f : X ⟶ Y)
    (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) (V : (SmallEtale B S hS Y.1)ᵒᵖ) :
    Function.Bijective (((smallEtaleDirectImageRanIso B S hS f).hom.app G).hom.app V) :=
  bijective_sheaf_hom_app _ V

section Equalizer

variable (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) (e : ChartDiagram B S hS X.1 Y.1 f.hom)
  (hc : IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map (chartLift B S hS f e)).hom)
  {R R' : SmallEtale B S hS X.1} (t s : R ⟶ e.U)
  (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
    (chartLift B S hS f e) (chartLift B S hS f e)) (k : R' ⟶ R)
  (hk : IsSurjective B S hS
    ((SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map k)).hom)

/-- The restriction of a sheaf on the spaces-étale site along a surjective morphism is
injective. -/
theorem injective_map_of_isSurjective {Q : Sheaf (SpacesEtale.topology B S hS X) (Type u)}
    {Z Z' : SpacesEtale B S hS X} (q : Z' ⟶ Z)
    (hq : IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map q).hom) :
    Function.Injective (Q.obj.map q.op) := by
  have hlim := isLimitForkOfSurjectiveSingleton B S hS Q.obj Q.property hq
    (IsPullback.of_hasPullback q q)
    (by rw [← Q.obj.map_comp, ← Q.obj.map_comp, ← op_comp, ← op_comp, pullback.condition])
  have : Mono (Q.obj.map q.op) := Fork.IsLimit.mono hlim
  exact (mono_iff_injective _).1 this

include hc in
/-- **The projection of the sections of `f_*F` over `V` to a surjective chart is injective.** -/
theorem injective_modulePushforwardCounitApp :
    Function.Injective (modulePushforwardCounitApp B S hS f F e) := by
  intro x y hxy
  rw [modulePushforwardCounitApp_eq_ran, modulePushforwardCounitApp_eq_ran] at hxy
  have h1 := (bijective_comparisonAdjunction_counit (moduleSetSheaf B S hS X F) (op e.U)).1 hxy
  have h2 := injective_map_of_isSurjective (Q := (smallEtaleComparisonRan B S hS X).obj
    (moduleSetSheaf B S hS X F)) _ hc h1
  exact (bijective_smallEtaleDirectImageRanIso f (moduleSetSheaf B S hS X F) (op e.V)).1 h2

/-- The counit of the Kan extension adjunction is natural along morphisms of étale scheme
charts. -/
theorem comparisonAdjunction_counit_naturality (G : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    {U U' : SmallEtale B S hS X.1} (m : U' ⟶ U)
    (y : ((smallEtaleComparisonRan B S hS X).obj G).obj.obj
      (op ((comparisonFunctor B S hS X).obj U))) :
    ((comparisonAdjunction B S hS X).counit.app G).hom.app (op U')
        (((smallEtaleComparisonRan B S hS X).obj G).obj.map ((comparisonFunctor B S hS X).map m).op
          y) =
      G.obj.map m.op (((comparisonAdjunction B S hS X).counit.app G).hom.app (op U) y) :=
  NatTrans.naturality_apply ((comparisonAdjunction B S hS X).counit.app G).hom m.op y

include hc hR hk in
/-- **The image of the projection of the sections of `f_*F` over `V` to a surjective chart is the
equalizer of the two restrictions to a cover of the relation.** -/
theorem exists_modulePushforwardCounitApp_eq (p : (moduleSetSheaf B S hS X F).obj.obj (op e.U))
    (hp : (moduleSetSheaf B S hS X F).obj.map k.op ((moduleSetSheaf B S hS X F).obj.map t.op p) =
      (moduleSetSheaf B S hS X F).obj.map k.op ((moduleSetSheaf B S hS X F).obj.map s.op p)) :
    ∃ x, modulePushforwardCounitApp B S hS f F e x = p := by
  let G := moduleSetSheaf B S hS X F
  let PR := (smallEtaleComparisonRan B S hS X).obj G
  let ε := (comparisonAdjunction B S hS X).counit.app G
  obtain ⟨y, hy⟩ := (bijective_comparisonAdjunction_counit G (op e.U)).2 p
  have hk' : Function.Injective (fun z => ε.hom.app (op R')
      (PR.obj.map ((comparisonFunctor B S hS X).map k).op z)) :=
    (bijective_comparisonAdjunction_counit G (op R')).1.comp
      (injective_map_of_isSurjective (Q := PR) _ hk)
  have key : ∀ m : R ⟶ e.U, ε.hom.app (op R') (PR.obj.map ((comparisonFunctor B S hS X).map k).op
      (PR.obj.map ((comparisonFunctor B S hS X).map m).op y)) = G.obj.map k.op (G.obj.map m.op p) :=
    fun m => (comparisonAdjunction_counit_naturality G k _).trans (congrArg (G.obj.map k.op)
      ((comparisonAdjunction_counit_naturality G m y).trans (congrArg (G.obj.map m.op) hy)))
  have hts : PR.obj.map ((comparisonFunctor B S hS X).map t).op y =
      PR.obj.map ((comparisonFunctor B S hS X).map s).op y :=
    hk' ((key t).trans (hp.trans (key s).symm))
  have hw : PR.obj.map (chartLift B S hS f e).op ≫
        PR.obj.map ((comparisonFunctor B S hS X).map t).op =
      PR.obj.map (chartLift B S hS f e).op ≫ PR.obj.map ((comparisonFunctor B S hS X).map s).op :=
    (PR.obj.map_comp _ _).symm.trans ((congrArg (fun m => PR.obj.map m.op) hR.w).trans
      (PR.obj.map_comp _ _))
  have hlim := isLimitForkOfSurjectiveSingleton B S hS PR.obj PR.property hc hR hw
  let fk : Fork (PR.obj.map ((comparisonFunctor B S hS X).map t).op)
      (PR.obj.map ((comparisonFunctor B S hS X).map s).op) :=
    Fork.ofι (P := PUnit.{u + 1}) (TypeCat.ofHom fun _ => y) (by ext; exact hts)
  let z := hlim.lift fk PUnit.unit
  have hz : PR.obj.map (chartLift B S hS f e).op z = y :=
    ConcreteCategory.congr_hom (hlim.fac fk WalkingParallelPair.zero) PUnit.unit
  obtain ⟨x, hx⟩ := (bijective_smallEtaleDirectImageRanIso f G (op e.V)).2 z
  exact ⟨x, (modulePushforwardCounitApp_eq_ran f F e x).trans <|
    (congrArg (fun z' => ε.hom.app (op e.U) (PR.obj.map (chartLift B S hS f e).op z')) hx).trans <|
      (congrArg (ε.hom.app (op e.U)) hz).trans hy⟩

/-- The two morphisms of a presentation of `W ×_{V ×_Y X} W` have the same composite to `V`. -/
theorem chartMap_comp_eq_of_isPullback (f : X ⟶ Y) (e : ChartDiagram B S hS X.1 Y.1 f.hom)
    {R : SmallEtale B S hS X.1} {t s : R ⟶ e.U}
    (hR : IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
      (chartLift B S hS f e) (chartLift B S hS f e)) :
    (SmallEtale.toOver B S hS X.1).map t ≫ e.g = (SmallEtale.toOver B S hS X.1).map s ≫ e.g := by
  apply yoneda.map_injective
  have h1 := congrArg (fun φ => ((SpacesEtale.toSpaces B S hS X).map φ ≫
    (spacesBaseChange B S hS f).projection.app ((comparisonFunctor B S hS Y).obj e.V)).hom) hR.w
  simp only [Functor.map_comp, Category.assoc, chartLift_projection] at h1
  have e1 := toSpaces_comparisonFunctor_map_hom B S hS X t
  have e2 := toSpaces_comparisonFunctor_map_hom B S hS X s
  change ((SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map t)).hom ≫
      yoneda.map e.g = ((SpacesEtale.toSpaces B S hS X).map
        ((comparisonFunctor B S hS X).map s)).hom ≫ yoneda.map e.g at h1
  rw [e1, e2] at h1
  exact ((yoneda.map_comp _ _).trans h1).trans (yoneda.map_comp _ _).symm

/-- Precomposing the vertical morphism of a chart diagram with a morphism of charts gives a chart
diagram. -/
theorem chart_comp_comm (f : X ⟶ Y) {V : SmallEtale B S hS Y.1} {U W : SmallEtale B S hS X.1}
    (m : U ⟶ W) (b : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (hb : W.1.hom ≫ f.hom = yoneda.map b ≫ V.1.hom) :
    U.1.hom ≫ f.hom = yoneda.map ((SmallEtale.toOver B S hS X.1).map m ≫ b) ≫ V.1.hom :=
  (congrArg (· ≫ f.hom) (CostructuredArrow.w m.hom).symm).trans ((Category.assoc _ _ _).trans
    ((congrArg (yoneda.map ((SmallEtale.toOver B S hS X.1).map m) ≫ ·) hb).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ V.1.hom) (yoneda.map_comp _ _).symm))))

end Equalizer

section Presentation

variable (f : X ⟶ Y)

/-- **An affine étale presentation of `V ×_Y X` by charts of `X`.**  For a quasi-compact,
quasi-separated `f` and an affine étale scheme chart `V` of `Y` there are an affine étale scheme
chart `W` of `X` with a morphism `W ⟶ V` over `f` whose cartesian form `W ⟶ V ×_Y X` is
surjective, an étale scheme chart `R` of `X` presenting `W ×_{V ×_Y X} W`, and a surjective
morphism to `R` from an affine étale scheme chart. -/
theorem exists_affine_presentation_chartBaseChange (hfqc : IsQuasiCompact B S hS f.hom)
    (hfqs : IsQuasiSeparated B S hS f.hom) (V : SmallEtale B S hS Y.1)
    (hV : IsAffine (chartScheme V)) :
    ∃ (W : SmallEtale B S hS X.1)
      (b : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
      (hb : W.1.hom ≫ f.hom = yoneda.map b ≫ V.1.hom) (R R' : SmallEtale B S hS X.1)
      (t s : R ⟶ W) (k : R' ⟶ R),
      IsAffine (chartScheme W) ∧ IsAffine (chartScheme R') ∧
      IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map
        (chartLift B S hS f ⟨W, V, b, hb⟩)).hom ∧
      IsPullback ((comparisonFunctor B S hS X).map t) ((comparisonFunctor B S hS X).map s)
        (chartLift B S hS f ⟨W, V, b, hb⟩) (chartLift B S hS f ⟨W, V, b, hb⟩) ∧
      IsSurjective B S hS
        ((SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map k)).hom := by
  obtain ⟨T₀, p₀, hT₀, hsurj₀, het₀⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS
      (chartBaseChangeSpace B S hS f V).1 (chartBaseChangeSpace B S hS f V).2).1
      (isQuasiCompactSpace_chartBaseChange B S hS f V hV hfqc)
  have P1 := AlgebraicSpaces.isPullback_hom B S hS (isPullback_chartBaseChangeInclusion B S hS f V)
  let W : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (p₀ ≫ (chartBaseChangeInclusion B S hS f V).hom),
      presheaf_etale_of_isEtale B S hS (isEtale_comp B S hS het₀
        (isEtale_chartBaseChangeInclusion B S hS f V))⟩
  let b : (SmallEtale.toOver B S hS X.1).obj W ⟶ (SmallEtale.toOver B S hS Y.1).obj V :=
    yoneda.preimage (show yoneda.obj ((SmallEtale.toOver B S hS X.1).obj W) ⟶
      yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj V) from
        p₀ ≫ (chartBaseChangeProjection B S hS f V).hom)
  have hyb : yoneda.map b = p₀ ≫ (chartBaseChangeProjection B S hS f V).hom :=
    yoneda.map_preimage _
  have hb : W.1.hom ≫ f.hom = yoneda.map b ≫ V.1.hom := by
    rw [hyb]
    exact (Category.assoc _ _ _).trans ((congrArg (p₀ ≫ ·) P1.w).trans
      (Category.assoc _ _ _).symm)
  let c₀ : (comparisonFunctor B S hS X).obj W ⟶ chartBaseChange B S hS f V :=
    ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk p₀) rfl)
  have hlift : chartLift B S hS f ⟨W, V, b, hb⟩ = c₀ :=
    (chartLift_eq B S hS f ⟨W, V, b, hb⟩ c₀ (ObjectProperty.hom_ext _ hyb.symm)).symm
  obtain ⟨T, t, s, hpb, ht, -⟩ := exists_etale_kernelPair B S hS p₀
    ((isEtale_iff_presheaf_of_yoneda B S hS p₀).1 het₀)
  let R : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (yoneda.map t ≫ W.1.hom), etale_comp_of_scheme B S hS t _ ht W.2⟩
  let t₀ : R ⟶ W := ObjectProperty.homMk (CostructuredArrow.homMk t rfl)
  let s₀ : R ⟶ W := ObjectProperty.homMk (CostructuredArrow.homMk s (by
    change yoneda.map s ≫ p₀ ≫ (chartBaseChangeInclusion B S hS f V).hom =
      yoneda.map t ≫ p₀ ≫ (chartBaseChangeInclusion B S hS f V).hom
    rw [← Category.assoc, ← Category.assoc, hpb.w]))
  have hpbT : IsPullback ((comparisonFunctor B S hS X).map t₀)
      ((comparisonFunctor B S hS X).map s₀) c₀ c₀ := by
    refine IsPullback.of_map_of_faithful (SpacesEtale.toSpaces B S hS X ⋙ ObjectProperty.ι _) ?_
    have e1 : (SpacesEtale.toSpaces B S hS X ⋙ ObjectProperty.ι _).map
        ((comparisonFunctor B S hS X).map t₀) = yoneda.map t :=
      toSpaces_comparisonFunctor_map_hom B S hS X t₀
    have e2 : (SpacesEtale.toSpaces B S hS X ⋙ ObjectProperty.ι _).map
        ((comparisonFunctor B S hS X).map s₀) = yoneda.map s :=
      toSpaces_comparisonFunctor_map_hom B S hS X s₀
    have e3 : (SpacesEtale.toSpaces B S hS X ⋙ ObjectProperty.ι _).map c₀ = p₀ := rfl
    rw [e1, e2, e3]
    exact hpb
  have hRqc : IsQuasiCompactSpace B S hS (yoneda.obj T) := by
    have hqc := isQuasiCompactSpace_selfPullback B S hS p₀
      (chartBaseChangeProjection B S hS f V).hom (isAlgebraicSpace_yoneda B S hS T₀)
      (isAlgebraicSpace_yoneda B S hS _)
      (isQuasiCompactSpace_yoneda B S hS T₀ (by have := hT₀; infer_instance))
      (isQuasiSeparated_chartBaseChangeProjection B S hS f V hfqs)
      (by rw [← hyb]; exact isQuasiCompact_yoneda_of_isAffine B S hS (yoneda.map b) hT₀ hV)
    exact hqc.of_iso B S hS hpb.isoPullback.symm
  obtain ⟨T₁, q, hT₁, hqs, hqe⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS (yoneda.obj T)
      (isAlgebraicSpace_yoneda B S hS T)).1 hRqc
  let q' : T₁ ⟶ T := yoneda.preimage q
  let R' : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk (q ≫ R.1.hom), presheaf_etale_of_isEtale B S hS
      (isEtale_comp B S hS hqe (isEtale_of_presheaf_etale B S hS R.2))⟩
  let k : R' ⟶ R := ObjectProperty.homMk (CostructuredArrow.homMk q' (by
    change yoneda.map q' ≫ R.1.hom = q ≫ R.1.hom
    rw [yoneda.map_preimage]))
  refine ⟨W, b, hb, R, R', t₀, s₀, k, hT₀, hT₁, ?_, hlift ▸ hpbT, ?_⟩
  · rw [hlift]
    exact isSurjective_of_presheafSurjective B S hS p₀ hsurj₀
  · have e : ((SpacesEtale.toSpaces B S hS X).map ((comparisonFunctor B S hS X).map k)).hom = q :=
      (toSpaces_comparisonFunctor_map_hom B S hS X k).trans (yoneda.map_preimage _)
    rw [e]
    exact isSurjective_of_presheafSurjective B S hS q hqs

end Presentation

end AlgebraicGeometry.Space

end
