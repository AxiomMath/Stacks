module

public import StacksFrontier.AlgebraicGeometry.Stacks.PointwisePresentationDescentDatum

/-!
# The pointwise cocycle conditions of a descent morphism

Lemmas on restriction along 2-morphisms of algebraic spaces, inverse images of sheaves of modules
along morphisms of algebraic spaces, transports, and the sections of module pullbacks, leading to
the unit and cocycle conditions of the descent morphism of a pointwise groupoid fibration, read
pointwise.

## Main results

* `AlgebraicGeometry.Stack.descComp_descentMorphism_identity` and
  `AlgebraicGeometry.Stack.descComp_descentMorphism_compose`: the unit and cocycle conditions of
  the descent morphism, pointwise.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

section Spaces

variable {X Y Z : AlgebraicSpaces C S hS}

/-- Restriction along the identity 2-morphism of `f` is the identity. -/
theorem spaceTwoMorphism_id (f : spaceCat X ⥤ spaceCat Z)
    (hf₁ : (spaceProj X).IsFibredOneMorphism (spaceProj Z) f)
    (hf₂ : (spaceProj X).IsFibredOneMorphism (spaceProj Z) f)
    (hθ : ∀ W, (spaceProj Z).IsHomLift (𝟙 ((spaceProj Z).obj (f.obj W))) ((𝟙 f : f ⟶ f).app W))
    (M : SheafOfModules.{u} (spaceRing Z)) :
    spaceTwoMorphism f f hf₁ hf₂ (𝟙 f) hθ M = 𝟙 _ := by
  ext W x
  exact PresheafOfModules.map_id_apply _ _ _

/-- Restriction along a 2-morphism which is a transport is a transport. -/
theorem spaceTwoMorphism_eqToHom (f₁ f₂ : spaceCat X ⥤ spaceCat Z)
    (hf₁ : (spaceProj X).IsFibredOneMorphism (spaceProj Z) f₁)
    (hf₂ : (spaceProj X).IsFibredOneMorphism (spaceProj Z) f₂) (e : f₂ = f₁)
    (hθ : ∀ W, (spaceProj Z).IsHomLift (𝟙 ((spaceProj Z).obj (f₂.obj W))) ((eqToHom e).app W))
    (M : SheafOfModules.{u} (spaceRing Z)) :
    spaceTwoMorphism f₁ f₂ hf₁ hf₂ (eqToHom e) hθ M = eqToHom (by subst e; rfl) := by
  subst e
  exact spaceTwoMorphism_id f₂ hf₁ hf₂ hθ M

/-- The étale-restricted inverse images of `M` along equal 1-morphisms `f₁ = f₂` agree. -/
theorem spaceEtaleInverseImage_congr (f₁ f₂ : spaceCat X ⥤ spaceCat Z)
    (hf₁ : (spaceProj X).IsFibredOneMorphism (spaceProj Z) f₁)
    (hf₂ : (spaceProj X).IsFibredOneMorphism (spaceProj Z) f₂) (e : f₂ = f₁)
    (M : SheafOfModules.{u} (spaceRing Z)) :
    Space.etaleRestrictedModuleInverseImage C S hS (spaceProj X) (spaceProj Z)
        (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Z) (spacePresentation X)
        f₁ hf₁ (spaceEtale M) =
      Space.etaleRestrictedModuleInverseImage C S hS (spaceProj X) (spaceProj Z)
        (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Z) (spacePresentation X)
        f₂ hf₂ (spaceEtale M) := by
  subst e
  rfl

/-- The étale-restricted inverse images of `M` along composites `k₁ ≫ t₁ = k₂ ≫ t₂` agree. -/
theorem spaceEtaleInverseImage_comp_congr {Y' : AlgebraicSpaces C S hS} {k₁ : X ⟶ Y}
    {t₁ : Y ⟶ Z} {k₂ : X ⟶ Y'} {t₂ : Y' ⟶ Z} (h : k₁ ≫ t₁ = k₂ ≫ t₂)
    (M : SheafOfModules.{u} (spaceRing Z)) :
    Space.etaleRestrictedModuleInverseImage C S hS (spaceProj X) (spaceProj Z)
        (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Z) (spacePresentation X)
        (spaceFunctor k₁ ⋙ spaceFunctor t₁) (isFibredOneMorphism_spaceFunctor_comp k₁ t₁)
        (spaceEtale M) =
      Space.etaleRestrictedModuleInverseImage C S hS (spaceProj X) (spaceProj Z)
        (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Z) (spacePresentation X)
        (spaceFunctor k₂ ⋙ spaceFunctor t₂) (isFibredOneMorphism_spaceFunctor_comp k₂ t₂)
        (spaceEtale M) :=
  spaceEtaleInverseImage_congr _ _ _ _ (congrArg spaceFunctor h).symm M

/-- `spaceTwoMorphism_eqToHom` for the transport between two composites. -/
theorem spaceTwoMorphism_comp_eqToHom {k₁ k₂ : X ⟶ Y} {t₁ t₂ : Y ⟶ Z}
    (h : k₁ ≫ t₁ = k₂ ≫ t₂) (M : SheafOfModules.{u} (spaceRing Z))
    (hθ : ∀ W, (spaceProj Z).IsHomLift (𝟙 ((spaceProj Z).obj
      ((spaceFunctor k₂ ⋙ spaceFunctor t₂).obj W)))
      ((eqToHom (congrArg spaceFunctor h).symm :
        spaceFunctor k₂ ⋙ spaceFunctor t₂ ⟶ spaceFunctor k₁ ⋙ spaceFunctor t₁).app W)) :
    spaceTwoMorphism _ _ (isFibredOneMorphism_spaceFunctor_comp k₁ t₁)
        (isFibredOneMorphism_spaceFunctor_comp k₂ t₂) (eqToHom (congrArg spaceFunctor h).symm)
        hθ M = eqToHom (spaceEtaleInverseImage_comp_congr h M) :=
  spaceTwoMorphism_eqToHom _ _ _ _ _ _ M

/-- The étale-restricted inverse image of `M` along `h ⋙ k` is that of `k^*M` along `h`. -/
theorem spaceEtaleInverseImage_comp' (h : X ⟶ Y) (k : Y ⟶ Z)
    (M : SheafOfModules.{u} (spaceRing Z)) :
    Space.etaleRestrictedModuleInverseImage C S hS (spaceProj X) (spaceProj Z)
        (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Z)
        (spacePresentation X) (spaceFunctor h ⋙ spaceFunctor k)
        (isFibredOneMorphism_spaceFunctor_comp h k) (spaceEtale M) =
      spaceEtaleInverseImage h ((spacePullback k).obj M) := rfl

/-- The inverse of `spacePullbackRestrictionIso h k M` is a transport. -/
theorem spacePullbackRestrictionIso_inv' (h : X ⟶ Y) (k : Y ⟶ Z)
    (M : SheafOfModules.{u} (spaceRing Z)) :
    (spacePullbackRestrictionIso h k M).inv = eqToHom (spaceEtaleInverseImage_comp' h k M) := by
  ext W x
  rfl

/-- The forward map of `spacePullbackRestrictionIso h k M` is a transport. -/
theorem spacePullbackRestrictionIso_hom' (h : X ⟶ Y) (k : Y ⟶ Z)
    (M : SheafOfModules.{u} (spaceRing Z)) :
    (spacePullbackRestrictionIso h k M).hom =
      eqToHom (spaceEtaleInverseImage_comp' h k M).symm := by
  ext W x
  rfl

/-- If `k₁ ≫ t₁ = k₂ ≫ t₂`, then `k₁^*(t₁^*M) = k₂^*(t₂^*M)`. -/
theorem spacePullback_comp_obj_eq {Y' : AlgebraicSpaces C S hS} (k₁ : X ⟶ Y) (t₁ : Y ⟶ Z)
    {k₂ : X ⟶ Y'} (t₂ : Y' ⟶ Z) (M : SheafOfModules.{u} (spaceRing Z)) (h : k₁ ≫ t₁ = k₂ ≫ t₂) :
    (spacePullback k₁).obj ((spacePullback t₁).obj M) =
      (spacePullback k₂).obj ((spacePullback t₂).obj M) :=
  ((spacePullback_comp_obj k₁ t₁ M).symm.trans
    (congrArg (fun m => (spacePullback m).obj M) h)).trans (spacePullback_comp_obj k₂ t₂ M)

/-- Cancelling the identifications `spacePullbackRestrictionIso` around a transport. -/
theorem spaceEtaleInverseImageMap_eq_eqToHom (t s : Y ⟶ Z)
    (M : SheafOfModules.{u} (spaceRing Z))
    (β : (spacePullback t).obj M ⟶ (spacePullback s).obj M) (k : X ⟶ Y)
    (h₀ : k ≫ t = k ≫ s)
    (h1 : (spacePullbackRestrictionIso k t M).inv ≫ spaceEtaleInverseImageMap k β ≫
        (spacePullbackRestrictionIso k s M).hom =
      eqToHom (spaceEtaleInverseImage_comp_congr h₀ M)) :
    spaceEtaleInverseImageMap k β = eqToHom ((spaceEtaleInverseImage_comp' k t M).symm.trans
      ((spaceEtaleInverseImage_comp_congr h₀ M).trans
        (spaceEtaleInverseImage_comp' k s M))) := by
  rw [spacePullbackRestrictionIso_inv' k t M, spacePullbackRestrictionIso_hom' k s M] at h1
  exact eq_eqToHom_of_eqToHom_comp_comp_eqToHom _ _ _ _ h1

/-- The transport between two composites of functors of spaces lifts the identity. -/
private theorem isHomLift_comp_eqToHom_app {k₁ k₂ : X ⟶ Y} {t₁ t₂ : Y ⟶ Z}
    (h : k₁ ≫ t₁ = k₂ ≫ t₂) (W : spaceCat X) :
    (spaceProj Z).IsHomLift (𝟙 ((spaceProj Z).obj ((spaceFunctor k₂ ⋙ spaceFunctor t₂).obj W)))
      ((eqToHom (congrArg spaceFunctor h).symm :
        spaceFunctor k₂ ⋙ spaceFunctor t₂ ⟶ spaceFunctor k₁ ⋙ spaceFunctor t₁).app W) :=
  isHomLift_eqToHom_app_target _ _ W

/-- **The restriction to `X_étale` of `k^*β` is a transport when the transition reindexes to a
transport along `k`.** -/
theorem selfChartRestrictionMap_spacePullback_map_eq_eqToHom (t s : Y ⟶ Z)
    (M : SheafOfModules.{u} (spaceRing Z))
    (β : (spacePullback t).obj M ⟶ (spacePullback s).obj M)
    (α : (Space.modulePullback C S hS t).obj (selfChartRestriction M) ⟶
      (Space.modulePullback C S hS s).obj (selfChartRestriction M))
    (hβ : spaceEtaleInverseImageComparison t M ≫ (spacePullbackSelfIso t M).inv ≫
      selfChartRestrictionMap β ≫ (spacePullbackSelfIso s M).hom =
        α ≫ spaceEtaleInverseImageComparison s M) (k : X ⟶ Y)
    (h₀ : k ≫ t = k ≫ s)
    (hα : (Space.modulePullbackCompIso C S hS k t).inv.app
        (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj Z) (spaceProj Z)
          (isFiberedInGroupoids_spaceProj Z) (isFiberedInGroupoids_spaceProj Z)
          (spacePresentation Z) (𝟭 _) (isFibredOneMorphism_spaceId Z) (spaceEtale M)) ≫
        (Space.modulePullback C S hS k).map α ≫
          (Space.modulePullbackCompIso C S hS k s).hom.app
            (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj Z) (spaceProj Z)
          (isFiberedInGroupoids_spaceProj Z) (isFiberedInGroupoids_spaceProj Z)
          (spacePresentation Z) (𝟭 _) (isFibredOneMorphism_spaceId Z) (spaceEtale M)) =
      Space.pullbackTransport (selfChartRestriction M) h₀)
    [IsIso (compComparison k t M)] :
    selfChartRestrictionMap (M := (spacePullback k).obj ((spacePullback t).obj M))
        (M' := (spacePullback k).obj ((spacePullback s).obj M)) ((spacePullback k).map β) =
      eqToHom (congrArg selfChartRestriction (spacePullback_comp_obj_eq k t s M h₀)) := by
  have hθ := isHomLift_comp_eqToHom_app h₀
  have h1 := (restrictionMap_eq_spaceTwoMorphism t s M β α hβ k h₀ hα hθ).trans
    (spaceTwoMorphism_comp_eqToHom h₀ M hθ)
  have h2 := spaceEtaleInverseImageMap_eq_eqToHom t s M β k h₀ h1
  rw [selfChartRestrictionMap_spacePullback_map, h2, eqToHom_trans, eqToHom_trans]

/-- **The comparison `(k ≫ t)_small^*(M|_{Z_étale}) ⟶ (k^*t^*M)|_{X_étale}`**: the comparison map
along `k ≫ t`, read on the nested inverse image. -/
def nestedComparison (k : X ⟶ Y) (t : Y ⟶ Z) (M : SheafOfModules.{u} (spaceRing Z)) :
    (Space.modulePullback C S hS (k ≫ t)).obj
        (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj Z) (spaceProj Z)
          (isFiberedInGroupoids_spaceProj Z) (isFiberedInGroupoids_spaceProj Z)
          (spacePresentation Z) (𝟭 _) (isFibredOneMorphism_spaceId Z) (spaceEtale M)) ⟶
      selfChartRestriction ((spacePullback k).obj ((spacePullback t).obj M)) :=
  compComparison k t M ≫ (spacePullbackRestrictionIso k t M).inv ≫
    eqToHom (spaceEtaleInverseImage_eq k ((spacePullback t).obj M))

/-- `nestedComparison k t M` is an isomorphism when `compComparison k t M` is. -/
instance (k : X ⟶ Y) (t : Y ⟶ Z) (M : SheafOfModules.{u} (spaceRing Z))
    [IsIso (compComparison k t M)] : IsIso (nestedComparison k t M) := by
  unfold nestedComparison
  infer_instance

/-- **The restriction of `k^*β` through the nested comparisons is the reindexing of the
transition along `k`.** -/
theorem nestedComparison_comp_restrictionMap (t s : Y ⟶ Z)
    (M : SheafOfModules.{u} (spaceRing Z))
    (β : (spacePullback t).obj M ⟶ (spacePullback s).obj M)
    (α : (Space.modulePullback C S hS t).obj (selfChartRestriction M) ⟶
      (Space.modulePullback C S hS s).obj (selfChartRestriction M))
    (hβ : spaceEtaleInverseImageComparison t M ≫ (spacePullbackSelfIso t M).inv ≫
      selfChartRestrictionMap β ≫ (spacePullbackSelfIso s M).hom =
        α ≫ spaceEtaleInverseImageComparison s M) (k : X ⟶ Y) :
    nestedComparison k t M ≫
        selfChartRestrictionMap (M := (spacePullback k).obj ((spacePullback t).obj M))
          (M' := (spacePullback k).obj ((spacePullback s).obj M)) ((spacePullback k).map β) =
      ((Space.modulePullbackCompIso C S hS k t).inv.app
        (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj Z) (spaceProj Z)
          (isFiberedInGroupoids_spaceProj Z) (isFiberedInGroupoids_spaceProj Z)
          (spacePresentation Z) (𝟭 _) (isFibredOneMorphism_spaceId Z) (spaceEtale M)) ≫
        (Space.modulePullback C S hS k).map α ≫
          (Space.modulePullbackCompIso C S hS k s).hom.app
            (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj Z) (spaceProj Z)
          (isFiberedInGroupoids_spaceProj Z) (isFiberedInGroupoids_spaceProj Z)
          (spacePresentation Z) (𝟭 _) (isFibredOneMorphism_spaceId Z) (spaceEtale M))) ≫
        nestedComparison k s M := by
  have h1 := spaceEtaleInverseImageComparison_comp_restrictionMap_assoc t s M β α hβ k
  rw [selfChartRestrictionMap_spacePullback_map]
  unfold nestedComparison
  refine Eq.trans ?_ ((congrArg (fun z => z ≫ (spacePullbackRestrictionIso k s M).inv ≫
    eqToHom (spaceEtaleInverseImage_eq k ((spacePullback s).obj M))) h1).trans
      (by simp only [Category.assoc]))
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Iso.hom_inv_id_assoc]

/-- `pullbackTransport_comp_spaceComparison`, with the module on the small étale site spelled as
the restriction it is. -/
theorem pullbackTransport_raw_comp_spaceComparison {m₁ m₂ : X ⟶ Z} (h : m₁ = m₂)
    (f₁ f₂ : spaceCat X ⥤ spaceCat Z)
    (hf₁ : (spaceProj X).IsFibredOneMorphism (spaceProj Z) f₁)
    (hf₂ : (spaceProj X).IsFibredOneMorphism (spaceProj Z) f₂)
    (φ₁ : spaceFunctor m₁ ⋙ 𝟭 _ ≅ f₁) (φ₂ : spaceFunctor m₂ ⋙ 𝟭 _ ≅ f₂)
    (hφ₁ : ∀ W, (spaceProj Z).IsHomLift (𝟙 ((spaceProj Z).obj (f₁.obj W))) (φ₁.inv.app W))
    (hφ₂ : ∀ W, (spaceProj Z).IsHomLift (𝟙 ((spaceProj Z).obj (f₂.obj W))) (φ₂.inv.app W))
    (θ : f₂ ⟶ f₁)
    (hθ : ∀ W, (spaceProj Z).IsHomLift (𝟙 ((spaceProj Z).obj (f₂.obj W))) (θ.app W))
    (hc : ∀ W, φ₂.hom.app W ≫ θ.app W =
      eqToHom (by subst h; rfl) ≫ φ₁.hom.app W)
    (M : SheafOfModules.{u} (spaceRing Z)) :
    Space.pullbackTransport
        (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj Z) (spaceProj Z)
          (isFiberedInGroupoids_spaceProj Z) (isFiberedInGroupoids_spaceProj Z)
          (spacePresentation Z) (𝟭 _) (isFibredOneMorphism_spaceId Z) (spaceEtale M)) h ≫
        spaceComparison m₂ f₂ hf₂ φ₂ hφ₂ M =
      spaceComparison m₁ f₁ hf₁ φ₁ hφ₁ M ≫ spaceTwoMorphism f₁ f₂ hf₁ hf₂ θ hθ M := by
  subst h
  have htφ : φ₂.hom ≫ θ = φ₁.hom := by
    ext W
    simpa using hc W
  have key := Space.comparisonAlgebraicSpacesModules_twoMorphism C S hS (spaceProj X) (spaceProj Z)
    (spaceProj Z) (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Z)
    (isFiberedInGroupoids_spaceProj Z) (spacePresentation X) (spacePresentation Z) f₁ f₂ hf₁ hf₂
    θ hθ (spaceFunctor m₁) (𝟭 _) (isFibredOneMorphism_spaceId Z) φ₁ φ₂ m₁
    (spaceFunctorChartIso m₁) hφ₁ hφ₂ (isHomLift_spaceFunctorChartIso_hom_app m₁) htφ (spaceEtale M)
  have hT : Space.pullbackTransport
        (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj Z) (spaceProj Z)
          (isFiberedInGroupoids_spaceProj Z) (isFiberedInGroupoids_spaceProj Z)
          (spacePresentation Z) (𝟭 _) (isFibredOneMorphism_spaceId Z) (spaceEtale M))
        (rfl : m₁ = m₁) = 𝟙 _ := by
    simp [Space.pullbackTransport]
  rw [hT, Category.id_comp]
  exact key

/-- `pullbackTransport_comp_compComparison`, with the module on the small étale site spelled as
the restriction it is. -/
theorem pullbackTransport_raw_comp_compComparison {k₁ k₂ : X ⟶ Y} {t₁ t₂ : Y ⟶ Z}
    (h : k₁ ≫ t₁ = k₂ ≫ t₂) (M : SheafOfModules.{u} (spaceRing Z))
    (hθ : ∀ W, (spaceProj Z).IsHomLift (𝟙 ((spaceProj Z).obj
      ((spaceFunctor k₂ ⋙ spaceFunctor t₂).obj W)))
      ((eqToHom (congrArg spaceFunctor h).symm :
        spaceFunctor k₂ ⋙ spaceFunctor t₂ ⟶ spaceFunctor k₁ ⋙ spaceFunctor t₁).app W)) :
    Space.pullbackTransport
        (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj Z) (spaceProj Z)
          (isFiberedInGroupoids_spaceProj Z) (isFiberedInGroupoids_spaceProj Z)
          (spacePresentation Z) (𝟭 _) (isFibredOneMorphism_spaceId Z) (spaceEtale M)) h ≫
        compComparison k₂ t₂ M =
      compComparison k₁ t₁ M ≫ spaceTwoMorphism _ _ (isFibredOneMorphism_spaceFunctor_comp k₁ t₁)
        (isFibredOneMorphism_spaceFunctor_comp k₂ t₂) (eqToHom (congrArg spaceFunctor h).symm)
        hθ M :=
  pullbackTransport_raw_comp_spaceComparison h _ _ _ _ _ _ _ _ _ hθ
    (fun W => rightUnitor_hom_app_comp_eqToHom_app (F := spaceFunctor (k₂ ≫ t₂))
      (G := spaceFunctor (k₁ ≫ t₁)) (congrArg spaceFunctor h).symm W _) M

/-- **Transport of the nested comparisons along an equality `k₁ ≫ t₁ = k₂ ≫ t₂`.** -/
theorem pullbackTransport_comp_nestedComparison {k₁ k₂ : X ⟶ Y} {t₁ t₂ : Y ⟶ Z}
    (h : k₁ ≫ t₁ = k₂ ≫ t₂) (M : SheafOfModules.{u} (spaceRing Z)) :
    Space.pullbackTransport
        (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj Z) (spaceProj Z)
          (isFiberedInGroupoids_spaceProj Z) (isFiberedInGroupoids_spaceProj Z)
          (spacePresentation Z) (𝟭 _) (isFibredOneMorphism_spaceId Z) (spaceEtale M)) h ≫
        nestedComparison k₂ t₂ M =
      nestedComparison k₁ t₁ M ≫
        eqToHom (congrArg selfChartRestriction (spacePullback_comp_obj_eq k₁ t₁ t₂ M h)) := by
  have hθ := isHomLift_comp_eqToHom_app h
  have h1 := (pullbackTransport_raw_comp_compComparison h M hθ).trans
    (congrArg (fun z => compComparison k₁ t₁ M ≫ z) (spaceTwoMorphism_comp_eqToHom h M hθ))
  unfold nestedComparison
  rw [reassoc_of% h1, spacePullbackRestrictionIso_inv' k₁ t₁ M,
    spacePullbackRestrictionIso_inv' k₂ t₂ M]
  simp only [eqToHom_trans, Category.assoc]

/-- `ψ ↦ ψ|_{Y_étale}` preserves composition. -/
theorem selfChartRestrictionMap_comp {N₁ N₂ N₃ : SheafOfModules.{u} (spaceRing Y)} (φ : N₁ ⟶ N₂)
    (ψ : N₂ ⟶ N₃) :
    selfChartRestrictionMap (M := N₁) (M' := N₃) (φ ≫ ψ) =
      selfChartRestrictionMap (M := N₁) (M' := N₂) φ ≫
        selfChartRestrictionMap (M := N₂) (M' := N₃) ψ := by
  simp only [selfChartRestrictionMap, Space.etaleRestrictedModuleInverseImageMap,
    CategoryTheory.Functor.map_comp]
  exact CategoryTheory.Functor.map_comp _ _ _

/-- `eq_of_selfChartRestrictionMap_eq` for modules given with their quasi-coherence. -/
theorem eq_of_selfChartRestrictionMap_eq' {N₁ N₂ : SheafOfModules.{u} (spaceRing Y)}
    (h₁ : N₁.IsQuasicoherentOnSite) (h₂ : N₂.IsQuasicoherentOnSite) {φ₁ φ₂ : N₁ ⟶ N₂}
    (h : selfChartRestrictionMap (M := N₁) (M' := N₂) φ₁ =
      selfChartRestrictionMap (M := N₁) (M' := N₂) φ₂) : φ₁ = φ₂ :=
  eq_of_selfChartRestrictionMap_eq (P₁ := ⟨N₁, h₁⟩) (P₂ := ⟨N₂, h₂⟩) h

/-- `(k ≫ t)^*M = k^*(t^*M)`. -/
theorem stackPullback_comp_obj (k : X ⟶ Y) (t : Y ⟶ Z) (M : SheafOfModules.{u} (spaceStackRing Z)) :
    (stackPullback (k ≫ t)).obj M = (stackPullback k).obj ((stackPullback t).obj M) := rfl

/-- `spacePullback_comp_obj_eq` in the spelling of `AlgebraicGeometry.Stack.modulePullback`. -/
theorem stackPullback_comp_obj_eq {Y' : AlgebraicSpaces C S hS} (k₁ : X ⟶ Y) (t₁ : Y ⟶ Z)
    {k₂ : X ⟶ Y'} (t₂ : Y' ⟶ Z) (M : SheafOfModules.{u} (spaceStackRing Z))
    (h : k₁ ≫ t₁ = k₂ ≫ t₂) :
    (stackPullback k₁).obj ((stackPullback t₁).obj M) =
      (stackPullback k₂).obj ((stackPullback t₂).obj M) :=
  ((stackPullback_comp_obj k₁ t₁ M).symm.trans
    (congrArg (fun m => (stackPullback m).obj M) h)).trans (stackPullback_comp_obj k₂ t₂ M)

end Spaces

section Transport

variable {X Z : AlgebraicSpaces C S hS}

/-- The functor of `k : X ⟶ Z` sends the `T`-point `a` of `X` to the `T`-point `k(a)` of `Z`. -/
theorem spaceFunctor_obj_mk (k : X ⟶ Z) (T : BigFppfOver C S hS) (a : X.obj.obj (op T)) :
    (spaceFunctor k).obj (⟨T, ⟨a⟩⟩ : spaceCat X) = (⟨T, ⟨k.hom.app (op T) a⟩⟩ : spaceCat Z) :=
  rfl

end Transport

/-- A natural transformation at equal objects, through the transports. -/
theorem NatTrans.app_eq_eqToHom_comp {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] {F F' : 𝒞 ⥤ 𝒟}
    (φ : F ⟶ F') {X Y : 𝒞} (h : X = Y) :
    φ.app Y = eqToHom (congrArg F.obj h).symm ≫ φ.app X ≫ eqToHom (congrArg F'.obj h) := by
  subst h
  simp

/-- A composite of three transports is a transport. -/
theorem eqToHom_comp_eqToHom_comp_eqToHom {𝒞 : Type*} [Category 𝒞] {A B C D : 𝒞} (p : A = B)
    (q : B = C) (r : C = D) (s : A = D) : eqToHom p ≫ eqToHom q ≫ eqToHom r = eqToHom s := by
  subst p q r
  simp

/-- The sections of a transport of sheaves of modules are a transport. -/
theorem SheafOfModules.toPresheaf_map_eqToHom_val_app {𝒞 : Type*} [Category 𝒞]
    {J : GrothendieckTopology 𝒞} {R : Sheaf J RingCat.{u}} {N₁ N₂ : SheafOfModules.{u} R}
    (h : N₁ = N₂) (X : 𝒞ᵒᵖ) :
    ((PresheafOfModules.toPresheaf _).map (eqToHom h).val).app X =
      eqToHom (congrArg (fun N : SheafOfModules.{u} R => N.val.presheaf.obj X) h) := by
  subst h
  exact congrArg (fun f => NatTrans.app f X) ((PresheafOfModules.toPresheaf _).map_id _)

/-- Pasting commuting squares along the isomorphism `Φc`: if `gc` is the composite of `p₁`,
`g₁`, `p₂`, `g₂` and `p₃`, and the `Φ`s intertwine `gc`, `p₁`, `g₁`, `p₂`, `g₂`, `p₃` with `Rc`,
`e₁`, `R₁`, `e₂`, `R₂`, `e₃`, then `Rc = e₁ ≫ R₁ ≫ e₂ ≫ R₂ ≫ e₃`. -/
theorem cocycle_pasting {𝒞 : Type*} [Category 𝒞]
    {A₀ A₁ A₂ A₃ A₄ A₅ B₀ B₁ B₂ B₃ B₄ B₅ : 𝒞}
    (p₁ : A₀ ⟶ A₁) (g₁ : A₁ ⟶ A₂) (p₂ : A₂ ⟶ A₃) (g₂ : A₃ ⟶ A₄) (p₃ : A₄ ⟶ A₅) (gc : A₀ ⟶ A₅)
    (Φc : A₀ ⟶ B₀) (Φ₁ : A₁ ⟶ B₁) (Φ₁' : A₂ ⟶ B₂) (Φ₂ : A₃ ⟶ B₃) (Φ₂' : A₄ ⟶ B₄)
    (Φc' : A₅ ⟶ B₅) (Rc : B₀ ⟶ B₅) (e₁ : B₀ ⟶ B₁) (R₁ : B₁ ⟶ B₂) (e₂ : B₂ ⟶ B₃) (R₂ : B₃ ⟶ B₄)
    (e₃ : B₄ ⟶ B₅) (hΦc : IsIso Φc)
    (hc : gc = comp₃ p₁ (comp₃ g₁ p₂ g₂) p₃) (hRc : Φc ≫ Rc = gc ≫ Φc')
    (hR₁ : Φ₁ ≫ R₁ = g₁ ≫ Φ₁') (hR₂ : Φ₂ ≫ R₂ = g₂ ≫ Φ₂')
    (hp₁ : p₁ ≫ Φ₁ = Φc ≫ e₁) (hp₂ : p₂ ≫ Φ₂ = Φ₁' ≫ e₂) (hp₃ : p₃ ≫ Φc' = Φ₂' ≫ e₃) :
    Rc = e₁ ≫ R₁ ≫ e₂ ≫ R₂ ≫ e₃ := by
  refine (cancel_epi Φc).1 ?_
  rw [hRc, hc, comp₃_eq, comp₃_eq]
  simp only [Category.assoc]
  rw [hp₃, ← reassoc_of% hR₂, reassoc_of% hp₂, ← reassoc_of% hR₁, reassoc_of% hp₁]

open GroupoidInAlgebraicSpaces in
/-- The cocycle condition of the transition `α`, read through comparison maps along the
composition and the two projections of the space of composable pairs. -/
theorem cocycle_of_comparisons {A : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS A)
    (F : Space.Modules.{u, u} C S hS G.objects.1 G.objects.2)
    (α : (Space.modulePullback C S hS G.target).obj F ⟶
      (Space.modulePullback C S hS G.source).obj F)
    (hc : Space.groupoidPullbackTransition C S hS G F α G.comp =
      Space.groupoidTransitionComposite C S hS G F α)
    {B₀ B₁ B₂ B₃ B₄ B₅ : Space.Modules.{u, u} C S hS
      (AlgebraicSpaces.fiberProduct C S hS G.source G.target).1
      (AlgebraicSpaces.fiberProduct C S hS G.source G.target).2}
    (Φc : (Space.modulePullback C S hS (G.comp ≫ G.target)).obj F ⟶ B₀)
    (Φ₁ : (Space.modulePullback C S hS (firstArrow G ≫ G.target)).obj F ⟶ B₁)
    (Φ₁' : (Space.modulePullback C S hS (firstArrow G ≫ G.source)).obj F ⟶ B₂)
    (Φ₂ : (Space.modulePullback C S hS (secondArrow G ≫ G.target)).obj F ⟶ B₃)
    (Φ₂' : (Space.modulePullback C S hS (secondArrow G ≫ G.source)).obj F ⟶ B₄)
    (Φc' : (Space.modulePullback C S hS (G.comp ≫ G.source)).obj F ⟶ B₅)
    (Rc : B₀ ⟶ B₅) (e₁ : B₀ ⟶ B₁) (R₁ : B₁ ⟶ B₂) (e₂ : B₂ ⟶ B₃) (R₂ : B₃ ⟶ B₄) (e₃ : B₄ ⟶ B₅)
    (hΦc : IsIso Φc)
    (hRc : Φc ≫ Rc = Space.groupoidPullbackTransition C S hS G F α G.comp ≫ Φc')
    (hR₁ : Φ₁ ≫ R₁ = Space.groupoidPullbackTransition C S hS G F α (firstArrow G) ≫ Φ₁')
    (hR₂ : Φ₂ ≫ R₂ = Space.groupoidPullbackTransition C S hS G F α (secondArrow G) ≫ Φ₂')
    (hp₁ : Space.pullbackTransport F (comp_comp_target G) ≫ Φ₁ = Φc ≫ e₁)
    (hp₂ : Space.pullbackTransport F (firstArrow_comp_source G) ≫ Φ₂ = Φ₁' ≫ e₂)
    (hp₃ : Space.pullbackTransport F (comp_comp_source G).symm ≫ Φc' = Φ₂' ≫ e₃) :
    Rc = e₁ ≫ R₁ ≫ e₂ ≫ R₂ ≫ e₃ := by
  rw [Space.groupoidTransitionComposite, Space.groupoidTransitionPair] at hc
  exact cocycle_pasting (Space.pullbackTransport F (comp_comp_target G))
    (Space.groupoidPullbackTransition C S hS G F α (firstArrow G))
    (Space.pullbackTransport F (firstArrow_comp_source G))
    (Space.groupoidPullbackTransition C S hS G F α (secondArrow G))
    (Space.pullbackTransport F (comp_comp_source G).symm)
    (Space.groupoidPullbackTransition C S hS G F α G.comp) Φc Φ₁ Φ₁' Φ₂ Φ₂' Φc' Rc e₁ R₁ e₂ R₂ e₃
    hΦc hc hRc hR₁ hR₂ hp₁ hp₂ hp₃

section ModulePullbackSections

universe v' w'

variable {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver C S hS) (q : 𝒴 ⥤ BigFppfOver C S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)

/-- **A morphism whose inverse image is a transport is a transport on the sections over the
image objects.** -/
theorem toPresheaf_map_val_app_of_modulePullback_map_eq_eqToHom
    {N₁ N₂ : SheafOfModules.{u} (ringStructureSheafCore C S hS q hq C.topology le_rfl)}
    (β : N₁ ⟶ N₂)
    (e : (modulePullback C S hS p q hp hq f hf C.topology le_rfl).obj N₁ =
      (modulePullback C S hS p q hp hq f hf C.topology le_rfl).obj N₂)
    (h : (modulePullback C S hS p q hp hq f hf C.topology le_rfl).map β = eqToHom e) (x : 𝒳) :
    ((PresheafOfModules.toPresheaf _).map β.val).app (op (f.obj x)) =
      eqToHom (congrArg (fun N : SheafOfModules.{u} (ringStructureSheafCore C S hS p hp
        C.topology le_rfl) => N.val.presheaf.obj (op x)) e) :=
  (congrArg (fun φ => ((PresheafOfModules.toPresheaf _).map φ.val).app (op x)) h).trans
    (SheafOfModules.toPresheaf_map_eqToHom_val_app e (op x))

/-- **A morphism whose inverse image satisfies a cocycle-type equation**, on the sections over
the image objects. -/
theorem toPresheaf_map_val_app_of_modulePullback_map_eq_comp
    (f₁ f₂ : 𝒳 ⥤ 𝒴) (hf₁ : f₁ ⋙ q = p) (hf₂ : f₂ ⋙ q = p)
    {N₁ N₂ : SheafOfModules.{u} (ringStructureSheafCore C S hS q hq C.topology le_rfl)}
    (β : N₁ ⟶ N₂)
    (e₁ : (modulePullback C S hS p q hp hq f hf C.topology le_rfl).obj N₁ =
      (modulePullback C S hS p q hp hq f₁ hf₁ C.topology le_rfl).obj N₁)
    (e₂ : (modulePullback C S hS p q hp hq f₁ hf₁ C.topology le_rfl).obj N₂ =
      (modulePullback C S hS p q hp hq f₂ hf₂ C.topology le_rfl).obj N₁)
    (e₃ : (modulePullback C S hS p q hp hq f₂ hf₂ C.topology le_rfl).obj N₂ =
      (modulePullback C S hS p q hp hq f hf C.topology le_rfl).obj N₂)
    (h : (modulePullback C S hS p q hp hq f hf C.topology le_rfl).map β = eqToHom e₁ ≫
      (modulePullback C S hS p q hp hq f₁ hf₁ C.topology le_rfl).map β ≫ eqToHom e₂ ≫
        (modulePullback C S hS p q hp hq f₂ hf₂ C.topology le_rfl).map β ≫ eqToHom e₃) (x : 𝒳) :
    ((PresheafOfModules.toPresheaf _).map β.val).app (op (f.obj x)) =
      eqToHom (congrArg (fun N : SheafOfModules.{u} (ringStructureSheafCore C S hS p hp
        C.topology le_rfl) => N.val.presheaf.obj (op x)) e₁) ≫
        ((PresheafOfModules.toPresheaf _).map β.val).app (op (f₁.obj x)) ≫
          eqToHom (congrArg (fun N : SheafOfModules.{u} (ringStructureSheafCore C S hS p hp
            C.topology le_rfl) => N.val.presheaf.obj (op x)) e₂) ≫
            ((PresheafOfModules.toPresheaf _).map β.val).app (op (f₂.obj x)) ≫
              eqToHom (congrArg (fun N : SheafOfModules.{u} (ringStructureSheafCore C S hS p hp
                C.topology le_rfl) => N.val.presheaf.obj (op x)) e₃) := by
  have h' := congrArg (fun φ => ((PresheafOfModules.toPresheaf _).map φ.val).app (op x)) h
  simp only [SheafOfModules.comp_val, CategoryTheory.Functor.map_comp, NatTrans.comp_app,
    SheafOfModules.toPresheaf_map_eqToHom_val_app] at h'
  exact h'

end ModulePullbackSections

section ModulePullbackSectionsSpelled

universe v' w'

variable {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver C S hS) (q : 𝒴 ⥤ BigFppfOver C S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)

/-- Equal inverse images have equal sections over the image objects. -/
theorem sections_eq_of_modulePullback_obj_eq (f f' : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) (hf' : f' ⋙ q = p)
    {N N' : SheafOfModules.{u} (ringStructureSheafCore C S hS q hq C.topology le_rfl)}
    (e : (modulePullback C S hS p q hp hq f hf C.topology le_rfl).obj N =
      (modulePullback C S hS p q hp hq f' hf' C.topology le_rfl).obj N') (x : 𝒳) :
    ((PresheafOfModules.toPresheaf _).obj N.val).obj (op (f.obj x)) =
      ((PresheafOfModules.toPresheaf _).obj N'.val).obj (op (f'.obj x)) :=
  congrArg (fun N : SheafOfModules.{u} (ringStructureSheafCore C S hS p hp
    C.topology le_rfl) => N.val.presheaf.obj (op x)) e

variable (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)

/-- `toPresheaf_map_val_app_of_modulePullback_map_eq_comp`, with every transport read on the
sections of the modules over the image objects. -/
theorem toPresheaf_map_val_app_eq_comp_of_modulePullback_map_eq
    (f₁ f₂ : 𝒳 ⥤ 𝒴) (hf₁ : f₁ ⋙ q = p) (hf₂ : f₂ ⋙ q = p)
    {N₁ N₂ : SheafOfModules.{u} (ringStructureSheafCore C S hS q hq C.topology le_rfl)}
    (β : N₁ ⟶ N₂)
    (e₁ : (modulePullback C S hS p q hp hq f hf C.topology le_rfl).obj N₁ =
      (modulePullback C S hS p q hp hq f₁ hf₁ C.topology le_rfl).obj N₁)
    (e₂ : (modulePullback C S hS p q hp hq f₁ hf₁ C.topology le_rfl).obj N₂ =
      (modulePullback C S hS p q hp hq f₂ hf₂ C.topology le_rfl).obj N₁)
    (e₃ : (modulePullback C S hS p q hp hq f₂ hf₂ C.topology le_rfl).obj N₂ =
      (modulePullback C S hS p q hp hq f hf C.topology le_rfl).obj N₂)
    (h : (modulePullback C S hS p q hp hq f hf C.topology le_rfl).map β = eqToHom e₁ ≫
      (modulePullback C S hS p q hp hq f₁ hf₁ C.topology le_rfl).map β ≫ eqToHom e₂ ≫
        (modulePullback C S hS p q hp hq f₂ hf₂ C.topology le_rfl).map β ≫ eqToHom e₃) (x : 𝒳) :
    ((PresheafOfModules.toPresheaf _).map β.val).app (op (f.obj x)) =
      eqToHom (sections_eq_of_modulePullback_obj_eq p q hp hq f f₁ hf hf₁ e₁ x) ≫
        ((PresheafOfModules.toPresheaf _).map β.val).app (op (f₁.obj x)) ≫
          eqToHom (sections_eq_of_modulePullback_obj_eq p q hp hq f₁ f₂ hf₁ hf₂ e₂ x) ≫
            ((PresheafOfModules.toPresheaf _).map β.val).app (op (f₂.obj x)) ≫
              eqToHom (sections_eq_of_modulePullback_obj_eq p q hp hq f₂ f hf₂ hf e₃ x) :=
  toPresheaf_map_val_app_of_modulePullback_map_eq_comp p q hp hq f hf f₁ f₂ hf₁ hf₂ β e₁ e₂ e₃ h x

end ModulePullbackSectionsSpelled

section DescCompSpelled

variable {A : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS A}

/-- The sections of `M` at the target of the `T`-point `r` of `R` are the sections of `t^*M` at
an object of `𝒮_R` equal to `(T, r)`. -/
theorem descComp_source_eq (M : SheafOfModules.{u} (objRing G)) (T : BigFppfOver C S hS)
    (r : G.arrows.obj.obj (op T)) (W : spaceCat G.arrows) (hW : W = ⟨T, ⟨r⟩⟩) :
    M.val.presheaf.obj (op (objPt G T (G.target.hom.app (op T) r))) =
      ((PresheafOfModules.toPresheaf (ringStructureSheafCore C S hS (spaceProj G.arrows)
        (isFiberedInGroupoids_spaceProj G.arrows) C.topology le_rfl).obj).obj
          ((targetPullback G).obj M).val).obj (op W) := by
  subst hW; rfl

/-- The sections of `s^*M` at an object of `𝒮_R` equal to `(T, r)` are the sections of `M` at
the source of the `T`-point `r` of `R`. -/
theorem descComp_target_eq (M : SheafOfModules.{u} (objRing G)) (T : BigFppfOver C S hS)
    (r : G.arrows.obj.obj (op T)) (W : spaceCat G.arrows) (hW : W = ⟨T, ⟨r⟩⟩) :
    ((PresheafOfModules.toPresheaf (ringStructureSheafCore C S hS (spaceProj G.arrows)
        (isFiberedInGroupoids_spaceProj G.arrows) C.topology le_rfl).obj).obj
          ((sourcePullback G).obj M).val).obj (op W) =
      M.val.presheaf.obj (op (objPt G T (G.source.hom.app (op T) r))) := by
  subst hW; rfl

/-- The component of a descent morphism at a point, read at an equal object of `𝒮_R`, in the
spelling of `AlgebraicGeometry.Stack.modulePullback`. -/
theorem descComp_eq_eqToHom_comp_stack {M : SheafOfModules.{u} (objRing G)}
    (β : (targetPullback G).obj M ⟶ (sourcePullback G).obj M) (T : BigFppfOver C S hS)
    (r : G.arrows.obj.obj (op T)) (W : spaceCat G.arrows) (hW : W = ⟨T, ⟨r⟩⟩) :
    descComp β T r = eqToHom (descComp_source_eq M T r W hW) ≫
      ((PresheafOfModules.toPresheaf (ringStructureSheafCore C S hS (spaceProj G.arrows)
        (isFiberedInGroupoids_spaceProj G.arrows) C.topology le_rfl).obj).map β.val).app (op W) ≫
          eqToHom (descComp_target_eq M T r W hW) := by
  subst hW
  simp only []
  exact (Category.comp_id _).symm

/-- The sections of `M` at equal `T`-points `a = a'` of `U` agree. -/
theorem objPt_sections_eq (M : SheafOfModules.{u} (objRing G)) {T : BigFppfOver C S hS}
    {a a' : G.objects.obj.obj (op T)} (h : a = a') :
    M.val.presheaf.obj (op (objPt G T a')) = M.val.presheaf.obj (op (objPt G T a)) := by
  rw [h]

/-- `ptTransport M h` is the transport along `objPt_sections_eq M h`. -/
theorem ptTransport_eq_eqToHom_sections (M : SheafOfModules.{u} (objRing G))
    {T : BigFppfOver C S hS} {a a' : G.objects.obj.obj (op T)} (h : a = a') :
    ptTransport M h = eqToHom (objPt_sections_eq M h) := by
  subst h
  simp only [ptTransport_rfl, eqToHom_refl]

end DescCompSpelled


section Congr

variable {A : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS A}

/-- The component of a descent morphism at equal points, through the transports. -/
theorem descComp_congr {M : SheafOfModules.{u} (objRing G)}
    (β : (targetPullback G).obj M ⟶ (sourcePullback G).obj M) {T : BigFppfOver C S hS}
    {r r' : G.arrows.obj.obj (op T)} (h : r = r') :
    descComp β T r = ptTransport M (congrArg (G.target.hom.app (op T)) h).symm ≫
      descComp β T r' ≫ ptTransport M (congrArg (G.source.hom.app (op T)) h) := by
  subst h
  simp only [ptTransport_rfl, Category.id_comp]
  exact (Category.comp_id _).symm

/-- The component of a descent morphism at a point, read at an equal object of `𝒮_R`. -/
theorem descComp_eq_eqToHom_comp {M : SheafOfModules.{u} (objRing G)}
    (β : (targetPullback G).obj M ⟶ (sourcePullback G).obj M) (T : BigFppfOver C S hS)
    (r : G.arrows.obj.obj (op T)) (W : spaceCat G.arrows) (hW : W = ⟨T, ⟨r⟩⟩) :
    descComp β T r = eqToHom (by subst hW; rfl) ≫
      ((PresheafOfModules.toPresheaf _).map β.val).app (op W) ≫ eqToHom (by subst hW; rfl) :=
  descComp_eq_eqToHom_comp_stack β T r W hW

/-- `ptTransport M h` is the transport between the sections of `M` at equal points. -/
theorem ptTransport_eq_eqToHom (M : SheafOfModules.{u} (objRing G)) {T : BigFppfOver C S hS}
    {a a' : G.objects.obj.obj (op T)} (h : a = a') :
    ptTransport M h =
      eqToHom (congrArg (fun b => M.val.presheaf.obj (op (objPt G T b))) h.symm) :=
  ptTransport_eq_eqToHom_sections M h

end Congr

section PointwiseCocycle

variable {A : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS A)

/-- Two composites of transports around `X₁` and `X₂` with the same endpoints are equal. -/
theorem eqToHom_collapse₂ {𝒞 : Type*} [Category 𝒞]
    {A A₁ P₁ P₂ P₃ P₄ B₁ B D₁ D₂ D₃ D₄ : 𝒞} (X₁ : P₁ ⟶ P₂) (X₂ : P₃ ⟶ P₄)
    {c₁ : A = A₁} {e₁ : A₁ = P₁} {e₂ : P₂ = P₃} {e₃ : P₄ = B₁} {c₂ : B₁ = B}
    {u₁ : A = D₁} {r₁ : D₁ = P₁} {r₂ : P₂ = D₂} {u₂ : D₂ = D₃} {s₁ : D₃ = P₃} {s₂ : P₄ = D₄}
    {u₃ : D₄ = B} :
    eqToHom c₁ ≫ (eqToHom e₁ ≫ X₁ ≫ eqToHom e₂ ≫ X₂ ≫ eqToHom e₃) ≫ eqToHom c₂ =
      eqToHom u₁ ≫ (eqToHom r₁ ≫ X₁ ≫ eqToHom r₂) ≫ eqToHom u₂ ≫
        (eqToHom s₁ ≫ X₂ ≫ eqToHom s₂) ≫ eqToHom u₃ := by
  subst c₁ e₁ e₂ e₃ c₂ u₁ r₂ u₂ s₂
  simp

open GroupoidInAlgebraicSpaces in
/-- The pointwise cocycle condition of a descent morphism whose inverse image along the
composition is the composite of its inverse images along the two projections. -/
theorem descComp_compose_of_stackPullback_map_eq (M : SheafOfModules.{u} (objRing G))
    (β : (targetPullback G).obj M ⟶ (sourcePullback G).obj M)
    (e₁ : (stackPullback G.comp).obj ((targetPullback G).obj M) =
      (stackPullback (firstArrow G)).obj ((targetPullback G).obj M))
    (e₂ : (stackPullback (firstArrow G)).obj ((sourcePullback G).obj M) =
      (stackPullback (secondArrow G)).obj ((targetPullback G).obj M))
    (e₃ : (stackPullback (secondArrow G)).obj ((sourcePullback G).obj M) =
      (stackPullback G.comp).obj ((sourcePullback G).obj M))
    (hβ : (stackPullback G.comp).map β = eqToHom e₁ ≫ (stackPullback (firstArrow G)).map β ≫
      eqToHom e₂ ≫ (stackPullback (secondArrow G)).map β ≫ eqToHom e₃)
    (T : BigFppfOver C S hS) (a b : G.arrows.obj.obj (op T))
    (h : G.source.hom.app (op T) a = G.target.hom.app (op T) b)
    (W : spaceCat (AlgebraicSpaces.fiberProduct C S hS G.source G.target))
    (hcW : (spaceFunctor G.comp).obj W =
      (⟨T, ⟨G.toGroupoidInFunctors.compose (op T) a b h⟩⟩ : spaceCat G.arrows))
    (h1W : (spaceFunctor (firstArrow G)).obj W = (⟨T, ⟨a⟩⟩ : spaceCat G.arrows))
    (h2W : (spaceFunctor (secondArrow G)).obj W = (⟨T, ⟨b⟩⟩ : spaceCat G.arrows)) :
    descComp β T (G.toGroupoidInFunctors.compose (op T) a b h) =
      ptTransport M (target_compose G T a b h).symm ≫ descComp β T a ≫
        ptTransport M h.symm ≫ descComp β T b ≫ ptTransport M (source_compose G T a b h) := by
  have hx := toPresheaf_map_val_app_eq_comp_of_modulePullback_map_eq
      (spaceProj (AlgebraicSpaces.fiberProduct C S hS G.source G.target)) (spaceProj G.arrows)
      (isFiberedInGroupoids_spaceProj _) (isFiberedInGroupoids_spaceProj _)
      (spaceFunctor G.comp) (spaceFunctor_comp_spaceProj G.comp)
      (spaceFunctor (firstArrow G)) (spaceFunctor (secondArrow G))
      (spaceFunctor_comp_spaceProj _) (spaceFunctor_comp_spaceProj _) β _ _ _ hβ W
  have hc := descComp_eq_eqToHom_comp_stack β T _ _ hcW
  have ha := descComp_eq_eqToHom_comp_stack β T a _ h1W
  have hb := descComp_eq_eqToHom_comp_stack β T b _ h2W
  rw [hc, ha, hb, ptTransport_eq_eqToHom_sections, ptTransport_eq_eqToHom_sections,
    ptTransport_eq_eqToHom_sections]
  refine (congrArg (fun z => eqToHom _ ≫ z ≫ eqToHom _) hx).trans ?_
  exact eqToHom_collapse₂ _ _


open GroupoidInAlgebraicSpaces in
/-- `descComp_compose_of_stackPullback_map_eq` for a module and a morphism in the spelling of the
fppf site of `𝒮_R`. -/
theorem descComp_compose_of_spacePullback_map_eq (M : SheafOfModules.{u} (spaceRing G.objects))
    (β : (spacePullback G.target).obj M ⟶ (spacePullback G.source).obj M)
    (hβ : (spacePullback G.comp).map β =
      eqToHom (spacePullback_comp_obj_eq _ _ _ M (comp_comp_target G)) ≫
        (spacePullback (firstArrow G)).map β ≫
          eqToHom (spacePullback_comp_obj_eq _ _ _ M (firstArrow_comp_source G)) ≫
            (spacePullback (secondArrow G)).map β ≫
              eqToHom (spacePullback_comp_obj_eq _ _ _ M (comp_comp_source G).symm))
    (T : BigFppfOver C S hS) (a b : G.arrows.obj.obj (op T))
    (h : G.source.hom.app (op T) a = G.target.hom.app (op T) b) :
    descComp (M := M) β T (G.toGroupoidInFunctors.compose (op T) a b h) =
      ptTransport M (target_compose G T a b h).symm ≫ descComp (M := M) β T a ≫
        ptTransport M h.symm ≫ descComp (M := M) β T b ≫
          ptTransport M (source_compose G T a b h) := by
  have h1 := pullbackFst_app_composableToPullback G.source.hom G.target.hom (op T) ⟨(a, b), h⟩
  have h2 := pullbackSnd_app_composableToPullback G.source.hom G.target.hom (op T) ⟨(a, b), h⟩
  exact descComp_compose_of_stackPullback_map_eq G M β _ _ _ hβ T a b h
    ⟨T, ⟨(composableToPullback G.source.hom G.target.hom).app (op T) ⟨(a, b), h⟩⟩⟩
    ((spaceFunctor_obj_mk G.comp T _).trans (congrArg (fun r => (⟨T, ⟨r⟩⟩ : spaceCat G.arrows))
      ((comp_hom_app_eq_compose T _).trans (compose_congr' G (op T) _ h h1 h2))))
    ((spaceFunctor_obj_mk (firstArrow G) T _).trans
      (congrArg (fun r => (⟨T, ⟨r⟩⟩ : spaceCat G.arrows)) h1))
    ((spaceFunctor_obj_mk (secondArrow G) T _).trans
      (congrArg (fun r => (⟨T, ⟨r⟩⟩ : spaceCat G.arrows)) h2))

end PointwiseCocycle

end AlgebraicGeometry.Stack

end
