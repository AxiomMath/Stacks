module

public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackification.LocalInjectivity

/-!
# The pullback of a stackification

If `G : 𝒮 ⥤ 𝒮'` exhibits `𝒮'` as the stackification of `𝒮`, then
`Ψ : u_p 𝒮 ⥤ u_p 𝒮'` is locally bijective on morphism presheaves and locally essentially
surjective, and the stackification of `u_p 𝒮'` is the stackification of `u_p 𝒮`.

## Main results

* `CategoryTheory.isLocallyBijective_morPresheafMap_pullbackLocalizationMap`: the maps of
  morphism presheaves induced by `Ψ` are locally injective and locally surjective.
* `CategoryTheory.localEssSurj_pullbackLocalizationMap`: every object of a fibre of `u_p 𝒮'` is
  locally in the essential image of `Ψ`.
* `CategoryTheory.pullback_stackification`: the stackification of `u_p 𝒮'` is the
  stackification of `u_p 𝒮`.

## References

* [Stacks Project, Tag 04WR](https://stacks.math.columbia.edu/tag/04WR)
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

/-! ### Local essential surjectivity of `Ψ` -/

section Local

universe w v

variable {𝒞 : Type u₁} [Category.{v} 𝒞] {𝒟 : Type u₂} [Category.{max u₂ u₃ u₄ v w} 𝒟]
  {𝒮 : Type u₃} [Category.{v} 𝒮] {𝒮' : Type u₄} [Category.{v} 𝒮']
  (u : 𝒞 ⥤ 𝒟) (p : 𝒮 ⥤ 𝒞) (p' : 𝒮' ⥤ 𝒞) {G : 𝒮 ⥤ 𝒮'}

/-- The fibre functor induced by `Ψ` sends `Q(V, a, ψ)` to `Q(V, G a, ψ)`. -/
lemma fiberFunctorOfCompEq_obj_fiberObj (hGG : p.IsFibredOneMorphism p' G) (V : 𝒟) (a : 𝒮)
    (ψ : V ⟶ u.obj (p.obj a)) :
    (Functor.fiberFunctorOfCompEq (pullbackLocalizationMap_comp_pullbackProj u hGG) V).obj
        (Comma.fiberObj p u V a ψ) =
      Comma.fiberObj p' u V (G.obj a) (ψ ≫ eqToHom (comp_obj_eq u p p' hGG.comp_eq a)) := by
  refine Subtype.ext ?_
  rw [Functor.fiberFunctorOfCompEq_obj_val, Comma.fiberObj_val, Comma.fiberObj_val,
    pullbackLocalizationMap_obj, commaMapOver_obj_mk u p p']

/-- **Two morphisms of a fibre of `u_p 𝒮` with the same image under `Ψ` agree after base change
along the members of a `K`-covering sieve.** -/
theorem locallyEqual_pullbackFiberHom
    [p.IsFibered] [p'.IsFibered] [HasNonemptyFiniteLimits 𝒞]
    (J : GrothendieckTopology 𝒞) (K : GrothendieckTopology 𝒟) [u.IsContinuous J K]
    (hu : ∀ (J' : Type) [SmallCategory J'] [FinCategory J'] [Nonempty J'],
      Limits.PreservesLimitsOfShape J' u)
    (hGG : p.IsFibredOneMorphism p' G)
    (hinj : ∀ (U : 𝒞) (x y : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hGG.morPresheafMap x y)) (W : 𝒟) :
    haveI : (Comma.pullbackProj p u).IsFibered := Comma.isFibered_pullbackProj p u hu
    ∀ {A B : (Comma.pullbackProj p u).Fiber W} (m₁ m₂ : A ⟶ B),
      (Functor.fiberFunctorOfCompEq (pullbackLocalizationMap_comp_pullbackProj u hGG) W).map m₁ =
          (Functor.fiberFunctorOfCompEq
            (pullbackLocalizationMap_comp_pullbackProj u hGG) W).map m₂ →
        ∃ T ∈ K W, ∀ ⦃W' : 𝒟⦄ ⦃β : W' ⟶ W⦄, T.arrows β →
          Functor.pullbackFiberHom m₁ β = Functor.pullbackFiberHom m₂ β := by
  have : (Comma.pullbackProj p u).IsFibered := Comma.isFibered_pullbackProj p u hu
  intro A B m₁ m₂ h
  obtain ⟨a, ψ, rfl⟩ := Comma.exists_fiberObj_eq p u W A
  obtain ⟨b, ω, rfl⟩ := Comma.exists_fiberObj_eq p u W B
  have hn : ∀ m : Comma.fiberObj p u W a ψ ⟶ Comma.fiberObj p u W b ω,
      (Comma.pullbackProj p u).map (Functor.Fiber.fiberInclusion.map m) = 𝟙 W := fun m ↦ by
    have : (Comma.pullbackProj p u).IsHomLift (𝟙 W)
      (Functor.Fiber.fiberInclusion.map m) := m.2
    exact (IsHomLift.eq_of_isHomLift (Comma.pullbackProj p u)
      (a := (Comma.fiberObj p u W a ψ).1) (b := (Comma.fiberObj p u W b ω).1) (𝟙 W)
      (Functor.Fiber.fiberInclusion.map m)).symm
  have hΨn : (pullbackLocalizationMap u hGG).map (Functor.Fiber.fiberInclusion.map m₁) =
      (pullbackLocalizationMap u hGG).map (Functor.Fiber.fiberInclusion.map m₂) :=
    congrArg Functor.Fiber.fiberInclusion.map h
  obtain ⟨T, hT, hTeq⟩ := locallyEqual_of_pullbackLocalizationMap_map_eq u p p' J K hu hGG hinj
    ψ ω (Functor.Fiber.fiberInclusion.map m₁) (Functor.Fiber.fiberInclusion.map m₂) (hn m₁)
    (hn m₂) hΨn
  refine ⟨T, hT, ?_⟩
  intro W' β hβ
  refine (Functor.pullbackFiberHom_uniq m₁ β (Functor.pullbackFiberHom m₂ β) ?_).symm
  rw [Functor.pullbackFiberHom_fac,
    ← Comma.pullbackFiberObjIso_hom_fac p u hu W a ψ β, Category.assoc, Category.assoc,
    hTeq hβ]

/-- **Clause (1) of Stacks 02ZN for `Ψ`, injectivity half.** The map of morphism presheaves on
`𝒟/V` induced by `Ψ` is locally injective. -/
theorem isLocallyInjective_morPresheafMap_pullbackLocalizationMap
    [p.IsFibered] [p'.IsFibered] [HasNonemptyFiniteLimits 𝒞]
    (J : GrothendieckTopology 𝒞) (K : GrothendieckTopology 𝒟) [u.IsContinuous J K]
    (hu : ∀ (J' : Type) [SmallCategory J'] [FinCategory J'] [Nonempty J'],
      Limits.PreservesLimitsOfShape J' u)
    (hGG : p.IsFibredOneMorphism p' G)
    (hinj : ∀ (U : 𝒞) (x y : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hGG.morPresheafMap x y))
    (V : 𝒟) :
    haveI : (Comma.pullbackProj p u).IsFibered := Comma.isFibered_pullbackProj p u hu
    haveI : (Comma.pullbackProj p' u).IsFibered := Comma.isFibered_pullbackProj p' u hu
    ∀ (x y : (Comma.pullbackProj p u).Fiber V),
      Presheaf.IsLocallyInjective (K.over V)
        ((Comma.isFibredOneMorphism_pullbackLocalizationMap p u hu hGG).morPresheafMap x y) := by
  have : (Comma.pullbackProj p u).IsFibered := Comma.isFibered_pullbackProj p u hu
  have : (Comma.pullbackProj p' u).IsFibered := Comma.isFibered_pullbackProj p' u hu
  intro x y
  refine ⟨fun {g} m₁ m₂ heq ↦ ?_⟩
  have hΨ := Comma.isFibredOneMorphism_pullbackLocalizationMap p u hu hGG
  have heq' : hΨ.morMapAt x y g.unop.hom m₁ = hΨ.morMapAt x y g.unop.hom m₂ := heq
  rw [hΨ.morMapAt_def, hΨ.morMapAt_def] at heq'
  have hFΨ : (Functor.fiberFunctorOfCompEq hΨ.comp_eq g.unop.left).map m₁ =
      (Functor.fiberFunctorOfCompEq hΨ.comp_eq g.unop.left).map m₂ := by
    simpa using heq'
  obtain ⟨T, hT, hTeq⟩ := locallyEqual_pullbackFiberHom u p p' J K hu hGG hinj g.unop.left
    m₁ m₂ hFΨ
  refine (K.over V).superset_covering ?_ (K.overEquiv_symm_mem_over g.unop T hT)
  intro Z h hh
  exact Functor.morRestrict_eq_of_pullbackFiberHom_eq (Comma.pullbackProj p u) x y h m₁ m₂
    (hTeq ((Sieve.overEquiv_symm_iff T h).1 hh))

/-- **Clause (1) of Stacks 02ZN for `Ψ`, surjectivity half.** The map of morphism presheaves on
`𝒟/V` induced by `Ψ` is locally surjective. -/
theorem isLocallySurjective_morPresheafMap_pullbackLocalizationMap
    [p.IsFibered] [p'.IsFibered] [HasNonemptyFiniteLimits 𝒞]
    (J : GrothendieckTopology 𝒞) (K : GrothendieckTopology 𝒟) [u.IsContinuous J K]
    (hu : ∀ (J' : Type) [SmallCategory J'] [FinCategory J'] [Nonempty J'],
      Limits.PreservesLimitsOfShape J' u)
    (hGG : p.IsFibredOneMorphism p' G)
    (hmor : ∀ (U : 𝒞) (x y : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hGG.morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective (J.over U) (hGG.morPresheafMap x y))
    (V : 𝒟) :
    haveI : (Comma.pullbackProj p u).IsFibered := Comma.isFibered_pullbackProj p u hu
    haveI : (Comma.pullbackProj p' u).IsFibered := Comma.isFibered_pullbackProj p' u hu
    ∀ (x y : (Comma.pullbackProj p u).Fiber V),
      Presheaf.IsLocallySurjective (K.over V)
        ((Comma.isFibredOneMorphism_pullbackLocalizationMap p u hu hGG).morPresheafMap x y) := by
  have : (Comma.pullbackProj p u).IsFibered := Comma.isFibered_pullbackProj p u hu
  have : (Comma.pullbackProj p' u).IsFibered := Comma.isFibered_pullbackProj p' u hu
  exact Functor.isLocallySurjective_morPresheafMap
    (Comma.isFibredOneMorphism_pullbackLocalizationMap p u hu hGG)
    (fun {_A _B} θ ↦ exists_covering_lift_pullbackLocalizationMap u p p' J K hu hGG hmor θ) V

/-- **Clause (1) of Stacks 02ZN for `Ψ`.** The maps of morphism presheaves induced by `Ψ` are
locally injective and locally surjective. -/
theorem isLocallyBijective_morPresheafMap_pullbackLocalizationMap
    [p.IsFibered] [p'.IsFibered] [HasNonemptyFiniteLimits 𝒞]
    (J : GrothendieckTopology 𝒞) (K : GrothendieckTopology 𝒟) [u.IsContinuous J K]
    (hu : ∀ (J' : Type) [SmallCategory J'] [FinCategory J'] [Nonempty J'],
      Limits.PreservesLimitsOfShape J' u)
    (hGG : p.IsFibredOneMorphism p' G)
    (hmor : ∀ (U : 𝒞) (x y : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hGG.morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective (J.over U) (hGG.morPresheafMap x y)) :
    haveI : (Comma.pullbackProj p u).IsFibered := Comma.isFibered_pullbackProj p u hu
    haveI : (Comma.pullbackProj p' u).IsFibered := Comma.isFibered_pullbackProj p' u hu
    ∀ (V : 𝒟) (x y : (Comma.pullbackProj p u).Fiber V),
      Presheaf.IsLocallyInjective (K.over V)
          ((Comma.isFibredOneMorphism_pullbackLocalizationMap p u hu hGG).morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective (K.over V)
          ((Comma.isFibredOneMorphism_pullbackLocalizationMap p u hu hGG).morPresheafMap x y) :=
  fun V x y ↦
    ⟨isLocallyInjective_morPresheafMap_pullbackLocalizationMap u p p' J K hu hGG
      (fun U x y ↦ (hmor U x y).1) V x y,
     isLocallySurjective_morPresheafMap_pullbackLocalizationMap u p p' J K hu hGG hmor V x y⟩

/-- **Local essential surjectivity of `Ψ`.** If every object of a fibre of `𝒮'` is, along a
`J`-covering sieve, in the essential image of `G` — clause (2) of Stacks 02ZN for `G` — then every
object of a fibre of `u_p 𝒮'` is, along a `K`-covering sieve, in the essential image of `Ψ`. -/
theorem localEssSurj_pullbackLocalizationMap
    [p.IsFibered] [p'.IsFibered] [HasNonemptyFiniteLimits 𝒞]
    (J : GrothendieckTopology 𝒞) (K : GrothendieckTopology 𝒟) [u.IsContinuous J K]
    (hu : ∀ (J' : Type) [SmallCategory J'] [FinCategory J'] [Nonempty J'],
      Limits.PreservesLimitsOfShape J' u)
    (hGG : p.IsFibredOneMorphism p' G)
    (hobj : ∀ (U : 𝒞) (x' : p'.Fiber U), ∃ R ∈ J U, ∀ ⦃U₁ : 𝒞⦄ ⦃d : U₁ ⟶ U⦄, R.arrows d →
      (Functor.fiberFunctorOfCompEq hGG.comp_eq U₁).essImage
        (Functor.pullbackFiber p' x' d)) :
    haveI : (Comma.pullbackProj p' u).IsFibered := Comma.isFibered_pullbackProj p' u hu
    ∀ (V : 𝒟) (z : (Comma.pullbackProj p' u).Fiber V), ∃ T ∈ K V,
      ∀ ⦃V₁ : 𝒟⦄ ⦃β : V₁ ⟶ V⦄, T.arrows β →
        (Functor.fiberFunctorOfCompEq
            (pullbackLocalizationMap_comp_pullbackProj u hGG) V₁).essImage
          (Functor.pullbackFiber (Comma.pullbackProj p' u) z β) := by
  have : (Comma.pullbackProj p' u).IsFibered := Comma.isFibered_pullbackProj p' u hu
  rintro V ⟨W, hW⟩
  obtain ⟨Y, rfl⟩ : ∃ Y, (Comma.idBaseStronglyCartesian p' u).Q.obj Y = W :=
    ⟨_, (Localization.Construction.objEquiv
      (Comma.idBaseStronglyCartesian p' u)).apply_symm_apply W⟩
  obtain ⟨V₀, a, ψ⟩ := Y
  have hV : V₀ = V := (Comma.pullbackProj_obj p' u (Comma.mk V₀ a ψ)).symm.trans hW
  subst hV
  have hz : (⟨(Comma.idBaseStronglyCartesian p' u).Q.obj (Comma.mk V₀ a ψ), hW⟩ :
      (Comma.pullbackProj p' u).Fiber V₀) = Comma.fiberObj p' u V₀ a ψ := rfl
  rw [hz]
  obtain ⟨R, hR, hRess⟩ := hobj (p'.obj a) (Functor.Fiber.mk rfl)
  refine ⟨Sieve.pullback ψ (Sieve.functorPushforward u R),
    mem_pullback_functorPushforward u J K hR ψ, ?_⟩
  intro V₁ β hβ
  obtain ⟨U₁, d, χ, hd, hfac⟩ :=
    exists_factorisation_of_mem_pullback_functorPushforward u ψ hβ
  set b : p'.Fiber U₁ := Functor.pullbackFiber p' (Functor.Fiber.mk (rfl : p'.obj a = _)) d
    with hbdef
  obtain ⟨y, ⟨θ⟩⟩ := hRess hd
  set α : b.1 ⟶ a :=
    Functor.IsPreFibered.pullbackMap (Functor.Fiber.mk (rfl : p'.obj a = _)).2 d with hαdef
  have hαcart : p'.IsStronglyCartesian d α := inferInstance
  have hα : stronglyCartesianOver p' α :=
    Comma.stronglyCartesianOver_of_isStronglyCartesian p' hαcart
  set θ' : G.obj y.1 ⟶ b.1 := Functor.Fiber.fiberInclusion.map θ.hom with hθdef
  have hθiso : IsIso θ' := by rw [hθdef]; infer_instance
  have hθlift : p'.IsHomLift (𝟙 U₁) θ' := θ.hom.2
  set χb : V₁ ⟶ u.obj (p'.obj b.1) := χ ≫ eqToHom (congrArg u.obj b.2.symm) with hχb
  set χG : V₁ ⟶ u.obj (p'.obj (G.obj y.1)) :=
    χ ≫ eqToHom (congrArg u.obj ((Functor.fiberFunctorOfCompEq hGG.comp_eq U₁).obj y).2.symm)
    with hχG
  set χy : V₁ ⟶ u.obj (p.obj y.1) := χ ≫ eqToHom (congrArg u.obj y.2.symm) with hχy
  have hE1 : β ≫ ψ = χb ≫ (p' ⋙ u).map α := by
    rw [hχb, Category.assoc, show (p' ⋙ u).map α = u.map (p'.map α) from rfl,
      IsHomLift.fac' p' d α]
    simp only [eqToHom_map, Functor.map_comp, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id]
    simpa using hfac
  have hE2 : χb = χG ≫ (p' ⋙ u).map θ' := by
    have := hθlift
    rw [hχb, hχG, Category.assoc, show (p' ⋙ u).map θ' = u.map (p'.map θ') from rfl,
      IsHomLift.fac' p' (𝟙 U₁) θ']
    simp [eqToHom_map]
  have hE3 : χy ≫ eqToHom (comp_obj_eq u p p' hGG.comp_eq y.1) = χG := by
    rw [hχy, hχG, Category.assoc, eqToHom_trans]
  refine ⟨Comma.fiberObj p u V₁ y.1 χy, ⟨?_⟩⟩
  rw [fiberFunctorOfCompEq_obj_fiberObj u p p' hGG, hE3]
  refine ?_ ≪≫ (Comma.pullbackFiberObjIso p' u hu V₀ a ψ β).symm
  rw [hE1]
  refine ?_ ≪≫ Comma.fiberObjIsoOfStronglyCartesian p' u hα χb
  rw [hE2]
  exact Comma.fiberObjIsoOfIso p' u θ' χG

/-! ### Stacks 04WR -/

variable {𝒯 : Type u₅} [Category.{max u₂ u₃ u₄ v w} 𝒯]

/-- Let `f : 𝒟 ⟶ 𝒞` be the morphism of sites given by a continuous
`u : 𝒞 ⥤ 𝒟` satisfying the hypotheses of Sites 00X6, let `p : 𝒮 ⥤ 𝒞` be a fibred category and let
`G : 𝒮 ⥤ 𝒮'` be its stackification (clauses (1) and (2) of Stacks 02ZN, spelled out as `hmor` and
`hobj`). Let `G' : u_p 𝒮' ⥤ 𝒯` exhibit the stack `q : 𝒯 ⥤ 𝒟` as the stackification of `u_p 𝒮'` —
that is, let `𝒯` be `f⁻¹𝒮'` in the sense of Stacks 04WJ — and let `H : u_p 𝒮 ⥤ 𝒯` be the canonical
functor, pinned down by its restriction `Q ⋙ H = Φ ⋙ Q' ⋙ G'` along the localization functor.
Then `H` exhibits `𝒯` as the stackification of `u_p 𝒮`: `f⁻¹𝒮'` is the stackification of
`u_p 𝒮`. -/
@[stacks 04WR]
theorem pullback_stackification
    [p.IsFibered] [p'.IsFibered] [HasNonemptyFiniteLimits 𝒞]
    (J : GrothendieckTopology 𝒞) (K : GrothendieckTopology 𝒟) [u.IsContinuous J K]
    (hu : ∀ (J' : Type) [SmallCategory J'] [FinCategory J'] [Nonempty J'],
      Limits.PreservesLimitsOfShape J' u)
    (hGG : p.IsFibredOneMorphism p' G)
    (hmor : ∀ (U : 𝒞) (x y : p.Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hGG.morPresheafMap x y) ∧
        Presheaf.IsLocallySurjective (J.over U) (hGG.morPresheafMap x y))
    (hobj : ∀ (U : 𝒞) (x' : p'.Fiber U), ∃ R ∈ J U, ∀ ⦃U₁ : 𝒞⦄ ⦃d : U₁ ⟶ U⦄, R.arrows d →
      (Functor.fiberFunctorOfCompEq hGG.comp_eq U₁).essImage (Functor.pullbackFiber p' x' d))
    {q : 𝒯 ⥤ 𝒟} (hq : q.IsStack K)
    {G' : Comma.pullbackLocalization p' u ⥤ 𝒯}
    (hG' : haveI : (Comma.pullbackProj p' u).IsFibered := Comma.isFibered_pullbackProj p' u hu
      (Comma.pullbackProj p' u).IsFibredOneMorphism q G')
    (hmor' : haveI : (Comma.pullbackProj p' u).IsFibered := Comma.isFibered_pullbackProj p' u hu
      haveI : q.IsFibered := hq.isFibered
      ∀ (V : 𝒟) (x y : (Comma.pullbackProj p' u).Fiber V),
        Presheaf.IsLocallyInjective (K.over V) (hG'.morPresheafMap x y) ∧
          Presheaf.IsLocallySurjective (K.over V) (hG'.morPresheafMap x y))
    (hobj' : haveI : q.IsFibered := hq.isFibered
      ∀ (V : 𝒟) (z : q.Fiber V), ∃ T ∈ K V, ∀ ⦃V₁ : 𝒟⦄ ⦃β : V₁ ⟶ V⦄, T.arrows β →
        (Functor.fiberFunctorOfCompEq hG'.comp_eq V₁).essImage (Functor.pullbackFiber q z β))
    (H : Comma.pullbackLocalization p u ⥤ 𝒯)
    (hH : (Comma.idBaseStronglyCartesian p u).Q ⋙ H =
      commaMapOver u hGG.comp_eq ⋙ (Comma.idBaseStronglyCartesian p' u).Q ⋙ G') :
    haveI : (Comma.pullbackProj p u).IsFibered := Comma.isFibered_pullbackProj p u hu
    haveI : q.IsFibered := hq.isFibered
    ∃ hH' : (Comma.pullbackProj p u).IsFibredOneMorphism q H,
      (∀ (V : 𝒟) (x y : (Comma.pullbackProj p u).Fiber V),
          Presheaf.IsLocallyInjective (K.over V) (hH'.morPresheafMap x y) ∧
            Presheaf.IsLocallySurjective (K.over V) (hH'.morPresheafMap x y)) ∧
        ∀ (V : 𝒟) (z : q.Fiber V), ∃ T ∈ K V, ∀ ⦃V₁ : 𝒟⦄ ⦃β : V₁ ⟶ V⦄, T.arrows β →
          (Functor.fiberFunctorOfCompEq hH'.comp_eq V₁).essImage
            (Functor.pullbackFiber q z β) := by
  have hfib : (Comma.pullbackProj p u).IsFibered := Comma.isFibered_pullbackProj p u hu
  have hfib' : (Comma.pullbackProj p' u).IsFibered := Comma.isFibered_pullbackProj p' u hu
  have hqfib : q.IsFibered := hq.isFibered
  have hΨ := Comma.isFibredOneMorphism_pullbackLocalizationMap p u hu hGG
  have hmorΨ := isLocallyBijective_morPresheafMap_pullbackLocalizationMap u p p' J K hu hGG hmor
  obtain rfl : H = pullbackLocalizationMap u hGG ⋙ G' :=
    eq_pullbackLocalizationMap_comp u hGG G' H hH
  refine ⟨hΨ.comp hG', fun V x y ↦ ?_, ?_⟩
  · have hcomp := Functor.IsFibredOneMorphism.morPresheafMap_comp hΨ hG' x y
    have h1 := (hmorΨ V x y).1
    have h2 := (hmorΨ V x y).2
    have h3 := (hmor' V ((Functor.fiberFunctorOfCompEq hΨ.comp_eq V).obj x)
      ((Functor.fiberFunctorOfCompEq hΨ.comp_eq V).obj y)).1
    have h4 := (hmor' V ((Functor.fiberFunctorOfCompEq hΨ.comp_eq V).obj x)
      ((Functor.fiberFunctorOfCompEq hΨ.comp_eq V).obj y)).2
    exact ⟨hcomp ▸ Presheaf.isLocallyInjective_comp (K.over V) _ _,
      hcomp ▸ Presheaf.isLocallySurjective_comp (K.over V) _ _⟩
  · exact locallyEssSurj_comp hΨ hG' K
      (localEssSurj_pullbackLocalizationMap u p p' J K hu hGG hobj) hobj'

end Local

end CategoryTheory

end
