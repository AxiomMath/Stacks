module

public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.EquivalenceRelation
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.HomToSheafGlue
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Sheafification
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubsetSeparationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ChartBaseChangeCartesian
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactStackInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactFiniteCoverDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsFibreProductAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InvariantSpectrumSiteCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentingMapFibrewisePullback
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMori.GeometricPoints
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMoriEtaleLocal.CartesianCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionOpenSourceRestriction

/-!
# The moduli space `M = U/R` and the moduli map `𝒳 ⟶ M` (Stacks 0DUT)

For a small Keel–Mori cover `C` of an algebraic stack `𝒳`, the étale equivalence relation
`R = ∐ N i j ⇉ U = ∐ M i` has an algebraic space quotient `M = U/R` (Stacks 02WW). This file
constructs it, with the étale maps `u i : M i ⟶ M`, and constructs the moduli map `f : 𝒳 ⟶ M`
with `g i ≫ f = f i ≫ u i`: the 1-morphisms `f i ≫ u i` agree on objects with isomorphic images
in `𝒳`, because such objects come from an object of `𝒳 i ×_𝒳 𝒳 j`, and `u i ∘ s i j = u j ∘ t i j`;
and every object of `𝒳` lifts locally to some `𝒳 i`, because the base changes of the `g i` along
it are étale schemes over its base which cover it.

## Main definitions

* `AlgebraicGeometry.Stack.KeelMoriCover.Mq`, `.π`, `.u`
* `AlgebraicGeometry.Stack.KeelMoriCover.moduliMap`

## Main results

* `AlgebraicGeometry.Stack.KeelMoriCover.isAlgebraicSpace_Mq`
* `AlgebraicGeometry.Stack.KeelMoriCover.map_comp_moduliMap`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Groupoids

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace KeelMoriCover

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {C : KeelMoriCover B S hS 𝒳} (hC : C.IsSmall)

attribute [local instance] hasSheafify_bigFppfOver

/-! ### The quotient `M = U/R` -/

/-- **The moduli space `M = U/R`**, as a presheaf on the site. -/
noncomputable def Mq : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (quotientSheaf (BigFppfOver.topology B S hS) (Over.post B.inclusion) (rel hC)).obj

/-- **`M = U/R` is an algebraic space** (Stacks 02WW). -/
theorem isAlgebraicSpace_Mq : IsAlgebraicSpace B S hS (Mq hC) :=
  Space.isAlgebraicSpace_quotient_unconditional B S hS (tR hC) (sR hC)

/-- `M`, as an object of the category of algebraic spaces. -/
noncomputable abbrev Msp' : AlgebraicSpaces B S hS := ⟨Mq hC, isAlgebraicSpace_Mq hC⟩

/-- **The quotient map `π : U ⟶ M`.** -/
noncomputable def π : yoneda.obj (U hC) ⟶ Mq hC := Space.quotientMap B S hS (tR hC) (sR hC)

/-- The quotient map `π : U ⟶ M` is surjective. -/
theorem π_surjective : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) (π hC) :=
  Space.quotientMap_surjective_unconditional B S hS (tR hC) (sR hC)

/-- The quotient map `π : U ⟶ M` is étale. -/
theorem π_etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) (π hC) :=
  Space.quotientMap_etale_unconditional B S hS (tR hC) (sR hC)

/-- **`R` is the kernel pair of `U ⟶ M`** (Stacks 02WV). -/
theorem isPullback_π : IsPullback (yoneda.map (sR hC)) (yoneda.map (tR hC)) (π hC) (π hC) :=
  Space.quotientMap_isPullback B S hS (tR hC) (sR hC)

/-- **The étale map `u i : M i ⟶ M`.** -/
noncomputable def u (i : C.ι) : yoneda.obj (C.M i) ⟶ Mq hC := yoneda.map (ιU hC i) ≫ π hC

/-- The maps `u i ∘ s i j` and `u j ∘ t i j` from `N i j` to `M` agree. -/
theorem s_comp_u (i j : C.ι) : yoneda.map (C.s i j) ≫ u hC i = yoneda.map (C.t i j) ≫ u hC j := by
  have h₁ : yoneda.map (C.s i j) ≫ yoneda.map (ιU hC i) = yoneda.map (ιR hC (i, j)) ≫
      yoneda.map (sR hC) := by rw [← yoneda.map_comp, ← yoneda.map_comp, ιR_sR]
  have h₂ : yoneda.map (C.t i j) ≫ yoneda.map (ιU hC j) = yoneda.map (ιR hC (i, j)) ≫
      yoneda.map (tR hC) := by rw [← yoneda.map_comp, ← yoneda.map_comp, ιR_tR]
  rw [u, u, reassoc_of% h₁, reassoc_of% h₂, (isPullback_π hC).w]

/-! ### The family `f i ≫ u i` -/

/-- The 1-morphism `𝒳 i ⟶ M`, the moduli map of `𝒳 i` followed by `u i`. -/
noncomputable abbrev φu (i : C.ι) : (C.obj i).val ⟶ fibredCategory B S hS (Mq hC) :=
  (C.f i).hom ≫ (associatedMap B S hS (u hC i)).1

/-- An object of `𝒳 i ×_𝒳 𝒳 j` from two objects joined by a vertical morphism of `𝒳`. -/
noncomputable def pairObj {i j : C.ι} (y : (C.obj i).val.val.obj) (y' : (C.obj j).val.val.obj)
    (V : BigFppfOver B S hS) (θ : (C.map i).hom.hom.obj y ⟶ (C.map j).hom.hom.obj y')
    (hθ : 𝒳.val.val.p.IsHomLift (𝟙 V) θ) : (C.X i j).val.val.obj :=
  have : IsIso θ :=
    Functor.isIso_of_fiber_isGroupoid (𝒳.val.isFiberedInGroupoids.fiber_isGroupoid V) θ hθ
  { base := V
    x := y
    y := y'
    hx := (Functor.congr_obj (C.map i).hom.hom.w y).symm.trans
      (IsHomLift.domain_eq 𝒳.val.val.p (𝟙 V) θ)
    hy := (Functor.congr_obj (C.map j).hom.hom.w y').symm.trans
      (IsHomLift.codomain_eq 𝒳.val.val.p (𝟙 V) θ)
    iso := asIso θ
    vertical := hθ }

/-- The first projection of `pairObj y y' V θ hθ` is `y`. -/
theorem pr₁_obj_pairObj {i j : C.ι} (y : (C.obj i).val.val.obj) (y' : (C.obj j).val.val.obj)
    (V : BigFppfOver B S hS) (θ : (C.map i).hom.hom.obj y ⟶ (C.map j).hom.hom.obj y')
    (hθ : 𝒳.val.val.p.IsHomLift (𝟙 V) θ) : (C.pr₁ i j).hom.hom.obj (pairObj y y' V θ hθ) = y := rfl

/-- The second projection of `pairObj y y' V θ hθ` is `y'`. -/
theorem pr₂_obj_pairObj {i j : C.ι} (y : (C.obj i).val.val.obj) (y' : (C.obj j).val.val.obj)
    (V : BigFppfOver B S hS) (θ : (C.map i).hom.hom.obj y ⟶ (C.map j).hom.hom.obj y')
    (hθ : 𝒳.val.val.p.IsHomLift (𝟙 V) θ) : (C.pr₂ i j).hom.hom.obj (pairObj y y' V θ hθ) = y' := rfl

/-- If `p ≫ f k` factors as `φ i j ≫ s`, then `φu k` sends `p c` to the image of `φ i j c`. -/
private theorem φu_obj_eq_of_φ_comp {i j k : C.ι} (p : C.X i j ⟶ C.obj k) (s : C.N i j ⟶ C.M k)
    (h : (C.φ i j).hom ≫ (associatedMap B S hS (yoneda.map s)).1 = p.hom ≫ (C.f k).hom)
    (c : (C.X i j).val.val.obj) : (φu hC k).hom.obj (p.hom.hom.obj c) =
      (associatedMap B S hS (yoneda.map s ≫ u hC k)).1.hom.obj ((C.φ i j).hom.hom.obj c) :=
  calc (φu hC k).hom.obj (p.hom.hom.obj c)
      = ((p.hom ≫ (C.f k).hom) ≫ (associatedMap B S hS (u hC k)).1).hom.obj c := rfl
    _ = (((C.φ i j).hom ≫ (associatedMap B S hS (yoneda.map s)).1) ≫
          (associatedMap B S hS (u hC k)).1).hom.obj c := by rw [h]
    _ = _ := by rw [associatedMap_comp]; rfl

/-- **The family `f i ≫ u i` is compatible along the cover.** -/
theorem compatibleAlong_φu : CompatibleAlong (g := fun i => (C.map i).hom) (φu hC) := by
  intro i j y y' V θ hθ
  let c := pairObj (C := C) y y' V θ hθ
  have h₁ : (φu hC i).hom.obj y = _ :=
    φu_obj_eq_of_φ_comp hC (C.pr₁ i j) (C.s i j) (C.φ_comp_s i j) c
  have h₂ : (φu hC j).hom.obj y' = _ :=
    φu_obj_eq_of_φ_comp hC (C.pr₂ i j) (C.t i j) (C.φ_comp_t i j) c
  rw [h₁, h₂, s_comp_u]

/-! ### Local lifting along the cover -/

/-- If `eqToHom e ≫ f = g`, then `f = eqToHom e.symm ≫ g`. -/
theorem _root_.CategoryTheory.eq_eqToHom_comp_of {𝒜 : Type*} [Category 𝒜] {X X' Y : 𝒜}
    (e : X' = X) (f : X ⟶ Y) (g : X' ⟶ Y) (h : eqToHom e ≫ f = g) : f = eqToHom e.symm ≫ g := by
  subst e
  simpa using h

/-- The 1-morphism `T ⟶ 𝒳` attached to an object `x` of `𝒳` over `T` (Stacks 004B). -/
noncomputable def objHom (x : 𝒳.val.val.obj) :
    schemeStack.{u, w} B S hS (𝒳.val.val.p.obj x) ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    (Functor.TwoYoneda.liftBased 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids (𝒳.val.val.p.obj x)
      (Functor.Fiber.mk (a := x) rfl)))

variable (C) in
/-- **Every object of `𝒳` lifts along an étale cover of its base to the members of the cover.**
The base change of `g i` along `x : T ⟶ 𝒳` is a scheme `W i` étale over `T` (Stacks 0DUS, first
step); the `W i` cover `T` because the `g i` are jointly surjective on points (Stacks 04XH); and
along every arrow `V ⟶ W i` the object `x` is the image of an object of `𝒳 i`. -/
theorem exists_etaleCover_lifts (x : 𝒳.val.val.obj) :
    ∃ (W : C.ι → BigFppfOver B S hS) (fU : ∀ i, W i ⟶ 𝒳.val.val.p.obj x),
      (∀ i, Etale ((BigFppfOver.toScheme B S hS).map (fU i))) ∧
      (∀ t : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x),
        ∃ i, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (fU i)).base) ∧
      ∀ (i : C.ι) {V : BigFppfOver B S hS} (l : V ⟶ W i),
        ∃ (y : (C.obj i).val.val.obj) (m : (C.map i).hom.hom.obj y ⟶ x),
          𝒳.val.val.p.IsHomLift (l ≫ fU i) m := by
  choose W eK fU hfU het _ using fun i =>
    ChartBaseChange.exists_etale_isSeparated_chartBaseChange (C.map i) (objHom x) (C.etale i)
      (C.separated i) (C.inducesIso i)
  refine ⟨W, fU, het, ?_, ?_⟩
  · intro t
    let T := 𝒳.val.val.p.obj x
    let := pointTopology B S hS (schemeFibredCategory B S hS T)
    let := fun i => pointTopology B S hS (schemeFibredCategory B S hS (W i))
    let z := (pointsHomeomorphScheme B S hS T).symm t
    obtain ⟨i, y₀, hy₀⟩ := C.cover (AlgebraicStacks.pointsMap B S hS (objHom x) z)
    obtain ⟨q, hq₁, hq₂⟩ := exists_point_of_isTwoFibreProduct_algebraicStacks B S hS
      (chartBaseChangeSquare (C.map i) (objHom x))
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS _ _) y₀ z hy₀
    have : (eK i).hom.functor.EssSurj := ((eK i).toEquivalence).essSurj_functor
    obtain ⟨w', hw'⟩ := pointsMap_surjective_of_essSurj B S hS _ _
      (⟨(eK i).hom.functor, (eK i).hom.w⟩ : (schemeStack.{u, w} B S hS (W i)).val.val ⥤ᵇ
        (chartBaseChangeSquare (C.map i) (objHom x)).pt.val.val) q
    refine ⟨i, pointsHomeomorphScheme B S hS (W i) w', ?_⟩
    have hsite : siteMap B S hS (Bicategory.InducedBicategory.mkHom
        (ChartBaseChange.chartMap (C.map i) (objHom x) (eK i))) = fU i := by
      apply Yoneda.fullyFaithful.map_injective
      rw [hfU i, ← representingMap_schemeFibredCategoryMap B S hS]
      exact (representingMap_congr_twoIso B S hS _ _ _ _
        (Bicategory.InducedBicategory.isoHom (schemeStackMapIso B S hS
          (Bicategory.InducedBicategory.mkHom
            (ChartBaseChange.chartMap (C.map i) (objHom x) (eK i)))))).symm
    have hpts := AlgebraicStacks.pointsMap_eq_of_iso B S hS (schemeStackMapIso B S hS
      (Bicategory.InducedBicategory.mkHom (ChartBaseChange.chartMap (C.map i) (objHom x) (eK i))) ≪≫
      eqToIso (congrArg (schemeStackMap.{u, w} B S hS) hsite))
    refine (pointsHomeomorphScheme_naturality B S hS (fU i) w').symm.trans ?_
    refine Eq.trans (congrArg (pointsHomeomorphScheme B S hS T) ?_)
      ((pointsHomeomorphScheme B S hS T).apply_symm_apply t)
    refine (congrFun hpts w').symm.trans ?_
    refine (pointsMap_comp B S hS (z := w')
      (h𝒴 := (chartBaseChangeSquare (C.map i) (objHom x)).pt.val.isFiberedInGroupoids)
      ..).symm.trans ?_
    exact (congrArg _ hw').trans hq₂
  · intro i V l
    let c := (eK i).hom.functor.obj (Over.mk l)
    have hcb : c.base = V :=
      ChartBaseChange.comparison_base (C.map i) (objHom x) (eK i) (Over.mk l)
    have hsec : PresheafOfCategories.sectionOfObj
        (PresheafOfCategories.sliceElementsEquivalenceOver (𝒳.val.val.p.obj x)) c.y
        (c.hy.trans hcb) = l ≫ fU i := by
      refine (representingMap_app_sectionOfObj
        (PresheafOfCategories.sliceElementsEquivalenceOver (W i))
        (PresheafOfCategories.sliceElementsEquivalenceOver _)
        (ChartBaseChange.chartMap (C.map i) (objHom x) (eK i)) (Over.mk l) rfl).symm.trans ?_
      rw [← hfU i]
      change (PresheafOfCategories.sectionOfObj
        (PresheafOfCategories.sliceElementsEquivalenceOver (W i)) (Over.mk l) rfl) ≫ fU i = _
      rw [ChartBaseChange.sectionOfObj_sliceElementsEquivalenceOver']
      simp
    have hsec' := (ChartBaseChange.sectionOfObj_sliceElementsEquivalenceOver' c.y
      (c.hy.trans hcb)).symm.trans hsec
    let L := Functor.TwoYoneda.chosenLift 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (𝒳.val.val.p.obj x) (Functor.Fiber.mk (a := x) rfl) c.y
    refine ⟨c.x, c.iso.hom ≫ L.φ, ?_⟩
    have h₁ : 𝒳.val.val.p.IsHomLift (𝟙 V) c.iso.hom := by
      rw [← hcb]
      exact c.vertical
    have hy' : c.y.hom = eqToHom (c.hy.trans hcb) ≫ (l ≫ fU i) :=
      eq_eqToHom_comp_of _ _ _ hsec'
    have h₂ : 𝒳.val.val.p.IsHomLift (l ≫ fU i) L.φ :=
      (IsHomLift.lift_eqToHom_comp_iff _ _ _ _).mp (hy' ▸ L.isStronglyCartesian.toIsHomLift)
    have h₃ := @IsHomLift.comp _ _ _ _ 𝒳.val.val.p _ _ _ _ _ _ (𝟙 V) (l ≫ fU i) c.iso.hom L.φ h₁
      h₂
    rwa [Category.id_comp] at h₃

variable (C) in
/-- **Every object of `𝒳` lifts locally to some member of the cover.** -/
theorem liftsLocally_map :
    LiftsLocally (𝒳 := 𝒳.val) (𝒴 := fun i => (C.obj i).val) (fun i => (C.map i).hom) := by
  intro x
  obtain ⟨W, fU, het, hsurj, hlift⟩ := exists_etaleCover_lifts C x
  refine ⟨Sieve.generate (Presieve.ofArrows W fU),
    Space.generate_ofArrows_mem_topology_of_etale W fU het hsurj, ?_⟩
  rintro V k ⟨Y, l, g', ⟨i⟩, rfl⟩
  exact ⟨i, hlift i l⟩

variable (C) in
/-- **An object of `𝒳` over the spectrum of a separably closed field is the image of an object of
some member of the cover**, by a morphism over the identity: the étale cover of its base has a
section. -/
theorem exists_lift_of_isSpec (x : 𝒳.val.val.obj) {k : Type u} [Field k] [IsSepClosed k]
    (hV : (BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj x) ≅ Spec (.of k)) :
    ∃ (i : C.ι) (y : (C.obj i).val.val.obj) (m : (C.map i).hom.hom.obj y ⟶ x),
      𝒳.val.val.p.IsHomLift (𝟙 (𝒳.val.val.p.obj x)) m := by
  obtain ⟨W, fU, het, hsurj, hlift⟩ := exists_etaleCover_lifts C x
  obtain ⟨i, w, -⟩ := hsurj (hV.inv default)
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed
    ((BigFppfOver.toScheme B S hS).map (fU i)) hV.inv w (eq_of_isSpec hV _ _)
  obtain ⟨σ, hσ⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS (X := 𝒳.val.val.p.obj x) (Y := W i)
    (hV.hom ≫ l) (by
      calc (hV.hom ≫ l) ≫ B.inclusion.map (W i).hom
          = hV.hom ≫ (l ≫ (BigFppfOver.toScheme B S hS).map (fU i)) ≫
              B.inclusion.map (𝒳.val.val.p.obj x).hom := by
            rw [← BigFppfOver.toScheme_map_comp_hom (fU i)]
            simp only [Category.assoc]
        _ = hV.hom ≫ hV.inv ≫ B.inclusion.map (𝒳.val.val.p.obj x).hom := by rw [hl]
        _ = B.inclusion.map (𝒳.val.val.p.obj x).hom := by rw [hV.hom_inv_id_assoc])
  have hσf : σ ≫ fU i = 𝟙 _ := (BigFppfOver.toScheme B S hS).map_injective (by
    rw [Functor.map_comp, hσ, Category.assoc, hl, hV.hom_inv_id,
      CategoryTheory.Functor.map_id])
  obtain ⟨y, m, hm⟩ := hlift i σ
  rw [hσf] at hm
  exact ⟨i, y, m, hm⟩

/-! ### The moduli map -/

/-- The presheaf `M = U/R` is a sheaf for the fppf topology. -/
theorem isSheaf_Mq : Presieve.IsSheaf (BigFppfOver.topology B S hS) (Mq hC) :=
  (isSheaf_iff_isSheaf_of_type _ _).1 (isAlgebraicSpace_Mq hC).isSheaf

/-- **The moduli map `f : 𝒳 ⟶ M`**, glued from the `f i ≫ u i`. -/
noncomputable def moduliMap :
    𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS (Mq hC) (isAlgebraicSpace_Mq hC) :=
  Bicategory.InducedBicategory.mkHom
    (glueHom (isSheaf_Mq hC) (liftsLocally_map C) (compatibleAlong_φu hC))

/-- **The squares `g i ≫ f = f i ≫ u i` commute** (the diagrams (0DUU) of the source). -/
theorem map_comp_moduliMap (i : C.ι) :
    (C.map i).hom ≫ (moduliMap hC).hom = (C.f i).hom ≫ (associatedMap B S hS (u hC i)).1 :=
  comp_glueHom (isSheaf_Mq hC) (liftsLocally_map C) (compatibleAlong_φu hC) i

/-- **A 1-morphism out of `𝒳` into a sheaf is determined by its restrictions to the cover.** -/
theorem hom_ext_of_cover {E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hE : Presieve.IsSheaf (BigFppfOver.topology B S hS) E)
    {F₁ F₂ : 𝒳.val ⟶ fibredCategory B S hS E}
    (h : ∀ i, (C.map i).hom ≫ F₁ = (C.map i).hom ≫ F₂) : F₁ = F₂ :=
  hom_ext_of_liftsLocally hE (liftsLocally_map C) h

/-! ### Geometric points of `M` -/

/-- The image of an object under a 1-morphism into a represented presheaf, as an element. -/
theorem obj_eq_mk_elementOf {𝒜 : AlgebraicStacks.{u, w} B S hS} {N : BigFppfOver B S hS}
    (F : 𝒜 ⟶ algebraicSpaceStack.{u, w} B S hS (yoneda.obj N) (isAlgebraicSpace_yoneda B S hS N))
    (a : 𝒜.val.val.obj) {V : BigFppfOver B S hS} (ha : 𝒜.val.val.p.obj a = V) :
    ∃ n : V ⟶ N, F.hom.hom.obj a =
      (⟨V, Discrete.mk n⟩ : (fibredCategory B S hS (yoneda.obj N)).val.obj) := by
  have hb : (F.hom.hom.obj a).base = V := (Functor.congr_obj F.hom.hom.w a).trans ha
  exact ⟨PresheafOfCategories.elementOf (yoneda.obj N) hb,
    PresheafOfCategories.obj_eq_of_elementOf_eq (P := yoneda.obj N) hb rfl rfl⟩

/-- The 1-morphism associated with `u i` sends the object given by `n : V ⟶ M i` to the object
given by the image of `n` under `u i`. -/
theorem u_obj (i : C.ι) {V : BigFppfOver B S hS} (n : V ⟶ C.M i) :
    (associatedMap B S hS (u hC i)).1.hom.obj
      (⟨V, Discrete.mk n⟩ : (fibredCategory B S hS (yoneda.obj (C.M i))).val.obj) =
      ⟨V, Discrete.mk ((u hC i).app (op V) n)⟩ :=
  associatedMap_obj B S hS _ _

/-- **The moduli map is injective on isomorphism classes over algebraically closed fields.** Two
geometric points with the same image in `M` lift to `𝒳 a` and `𝒳 b`; their images in `U` are
related by `R = U ×_M U`, hence by a point of `N a b`, which comes from a geometric point of
`𝒳 a ×_𝒳 𝒳 b` whose components are isomorphic to the two lifts. -/
theorem moduliMap_injective_geometricPoints (k : Type u) [Field k] [IsAlgClosed k]
    (V : BigFppfOver B S hS) (hV : (BigFppfOver.toScheme B S hS).obj V ≅ Spec (.of k))
    (x₁ x₂ : 𝒳.val.val.obj) (h₁ : 𝒳.val.val.p.obj x₁ = V) (h₂ : 𝒳.val.val.p.obj x₂ = V)
    (h : (moduliMap hC).hom.hom.obj x₁ = (moduliMap hC).hom.hom.obj x₂) :
    ∃ α : x₁ ⟶ x₂, 𝒳.val.val.p.IsHomLift (𝟙 V) α := by
  have hp := 𝒳.val.isFiberedInGroupoids
  obtain ⟨a, y₁, m₁, hm₁⟩ := exists_lift_of_isSpec C x₁ (eqToIso (congrArg _ h₁) ≪≫ hV)
  obtain ⟨b, y₂, m₂, hm₂⟩ := exists_lift_of_isSpec C x₂ (eqToIso (congrArg _ h₂) ≪≫ hV)
  rw [h₁] at hm₁
  rw [h₂] at hm₂
  have hy₁ : (C.obj a).val.val.p.obj y₁ = V :=
    (Functor.congr_obj (C.map a).hom.hom.w y₁).symm.trans (IsHomLift.domain_eq 𝒳.val.val.p (𝟙 V) m₁)
  have hy₂ : (C.obj b).val.val.p.obj y₂ = V :=
    (Functor.congr_obj (C.map b).hom.hom.w y₂).symm.trans (IsHomLift.domain_eq 𝒳.val.val.p (𝟙 V) m₂)
  obtain ⟨n₁, hn₁⟩ := obj_eq_mk_elementOf (C.f a) y₁ hy₁
  obtain ⟨n₂, hn₂⟩ := obj_eq_mk_elementOf (C.f b) y₂ hy₂
  have himg : ∀ (j : C.ι) (y : (C.obj j).val.val.obj) (x : 𝒳.val.val.obj) (n : V ⟶ C.M j)
      (m : (C.map j).hom.hom.obj y ⟶ x), 𝒳.val.val.p.IsHomLift (𝟙 V) m →
      (C.f j).hom.hom.obj y = ⟨V, Discrete.mk n⟩ →
      (moduliMap hC).hom.hom.obj x = ⟨V, Discrete.mk ((u hC j).app (op V) n)⟩ := by
    intro j y x n m hm hn
    have hx : 𝒳.val.val.p.obj x = V := IsHomLift.codomain_eq 𝒳.val.val.p (𝟙 V) m
    have e₁ := fibredCategory_obj_eq_of_isHomLift_id B S hS
      ((Functor.congr_obj (moduliMap hC).hom.hom.w _).trans
        (IsHomLift.domain_eq 𝒳.val.val.p (𝟙 V) m))
      ((Functor.congr_obj (moduliMap hC).hom.hom.w x).trans hx)
      ((moduliMap hC).hom.hom.map m)
      (by have := hm; exact Functor.isHomLift_map_of_comp_eq (moduliMap hC).hom.hom.w (𝟙 V) m)
    refine e₁.symm.trans ((congrArg (fun G => G.hom.obj y) (map_comp_moduliMap hC j)).trans ?_)
    change (associatedMap B S hS (u hC j)).1.hom.obj ((C.f j).hom.hom.obj y) = _
    rw [hn, u_obj]
  have hM := (himg a y₁ x₁ n₁ m₁ hm₁ hn₁).symm.trans (h.trans (himg b y₂ x₂ n₂ m₂ hm₂ hn₂))
  have hel : (u hC a).app (op V) n₁ = (u hC b).app (op V) n₂ := by
    injection hM with _ h'
    exact congrArg Discrete.as h'
  have hπ : yoneda.map (n₁ ≫ ιU hC a) ≫ π hC = yoneda.map (n₂ ≫ ιU hC b) ≫ π hC := by
    apply yonedaEquiv.injective
    simp only [yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact hel
  obtain ⟨r, hr₁, hr₂⟩ := (isPullback_π hC).exists_lift _ _ hπ
  obtain ⟨p, n, hn⟩ := exists_factor_ιR hC hV (Yoneda.fullyFaithful.preimage r)
  have hs : n ≫ C.s p.1 p.2 ≫ ιU hC p.1 = n₁ ≫ ιU hC a := by
    apply yoneda.map_injective
    rw [← ιR_sR, ← Category.assoc, hn, Functor.map_comp, Yoneda.fullyFaithful.map_preimage, hr₁]
  have ht : n ≫ C.t p.1 p.2 ≫ ιU hC p.2 = n₂ ≫ ιU hC b := by
    apply yoneda.map_injective
    rw [← ιR_tR, ← Category.assoc, hn, Functor.map_comp, Yoneda.fullyFaithful.map_preimage, hr₂]
  rw [← Category.assoc] at hs ht
  obtain ⟨a', b'⟩ := p
  have ha : a' = a := eq_of_comp_ιU_eq hC hV _ _ hs
  have hb : b' = b := eq_of_comp_ιU_eq hC hV _ _ ht
  subst ha hb
  have hs' := (mono_ιU hC a').right_cancellation _ _ hs
  have ht' := (mono_ιU hC b').right_cancellation _ _ ht
  obtain ⟨c, hc, hcn⟩ :=
    exists_obj_of_universalHomeomorphism (C.φ a' b') (C.universalHomeomorphism_φ a' b') k V hV n
  obtain ⟨α₁, hα₁⟩ := exists_isHomLift_id_of_universalHomeomorphism_algebraicSpace
    (N := C.Msp a') (C.f a') (C.chart a').universalHomeomorphism_moduliMap k V hV _ _ hy₁
    ((Functor.congr_obj (C.pr₁ a' b').hom.hom.w c).trans hc)
    (hn₁.trans (by rw [C.obj_f_pr₁ c n hcn, hs']))
  obtain ⟨α₂, hα₂⟩ := exists_isHomLift_id_of_universalHomeomorphism_algebraicSpace
    (N := C.Msp b') (C.f b') (C.chart b').universalHomeomorphism_moduliMap k V hV _ _
    ((Functor.congr_obj (C.pr₂ a' b').hom.hom.w c).trans hc) hy₂
    ((C.obj_f_pr₂ c n hcn).trans (by rw [ht', hn₂]))
  have hciso : 𝒳.val.val.p.IsHomLift (𝟙 V) c.iso.hom := by
    rw [← show c.base = V from hc]
    exact c.vertical
  have hm₁i : IsIso m₁ := Functor.isIso_of_fiber_isGroupoid (hp.fiber_isGroupoid V) m₁ hm₁
  have hm₁' := @IsHomLift.lift_id_inv _ _ _ _ 𝒳.val.val.p _ _ _ (asIso m₁) hm₁
  have hgα₁ := Functor.isHomLift_map_of_comp_eq (C.map a').hom.hom.w (𝟙 V) α₁
  have hgα₂ := Functor.isHomLift_map_of_comp_eq (C.map b').hom.hom.w (𝟙 V) α₂
  have l₄ := @IsHomLift.comp_of_lift_id _ _ _ _ 𝒳.val.val.p V _ _ _
    ((C.map b').hom.hom.map α₂) m₂ hgα₂ hm₂
  have l₃ := @IsHomLift.comp_of_lift_id _ _ _ _ 𝒳.val.val.p V _ _ _ c.iso.hom _ hciso l₄
  have l₂ := @IsHomLift.comp_of_lift_id _ _ _ _ 𝒳.val.val.p V _ _ _
    ((C.map a').hom.hom.map α₁) _ hgα₁ l₃
  exact ⟨_, @IsHomLift.comp_of_lift_id _ _ _ _ 𝒳.val.val.p V _ _ _ (asIso m₁).inv _ hm₁' l₂⟩

/-! ### The squares `𝒳 i = M i ×_M 𝒳` are 2-cartesian -/

/-- The map `u i : M i ⟶ M` is étale. -/
theorem isEtale_u (i : C.ι) : Space.IsEtale B S hS (u hC i) :=
  Space.isEtale_comp B S hS
    ((Space.isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map (ιU hC i))).2
      ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ (ιU hC i)).2 inferInstance))
    ((Space.isEtale_iff_presheaf_of_yoneda B S hS (π hC)).2 (π_etale hC))

/-- The morphism of algebraic spaces `u i : M i ⟶ M`. -/
noncomputable abbrev uSp (i : C.ι) : C.Msp i ⟶ Msp' hC := ObjectProperty.homMk (u hC i)

/-- **The squares (0DUU) are 2-cartesian**: `𝒳 i = M i ×_M 𝒳` (Stacks 0DUD, through the
cartesian criterion of `AlgebraicGeometry.Stack.nonempty_isTwoFibreProduct_spaceModuliSquare`). -/
theorem nonempty_isTwoFibreProduct_square (i : C.ι) :
    Nonempty (Bicategory.IsTwoFibreProduct (spaceModuliSquare B S hS (M := Msp' hC)
      (M' := C.Msp i) (C.map i) (moduliMap hC) (C.f i) (uSp hC i)
      (map_comp_moduliMap hC i).symm)) :=
  nonempty_isTwoFibreProduct_spaceModuliSquare B S hS (M := Msp' hC) (M' := C.Msp i) (C.map i)
    (moduliMap hC) (C.f i) (uSp hC i) (map_comp_moduliMap hC i).symm (C.etale i) (C.inducesIso i)
    (isEtale_u hC i)
    (fun k _ _ V hV x₁ x₂ h₁ h₂ e => moduliMap_injective_geometricPoints hC k V hV x₁ x₂ h₁ h₂ e)
    (fun k _ _ V hV x₁ x₂ h₁ h₂ e => exists_isHomLift_id_of_universalHomeomorphism_algebraicSpace
      (N := C.Msp i) (C.f i)
      (C.chart i).universalHomeomorphism_moduliMap k V hV x₁ x₂ h₁ h₂ e)
    (fun k _ _ V hV n => exists_obj_of_universalHomeomorphism (C.f i)
      (C.chart i).universalHomeomorphism_moduliMap k V hV n)

end KeelMoriCover

end AlgebraicGeometry.Stack

end
