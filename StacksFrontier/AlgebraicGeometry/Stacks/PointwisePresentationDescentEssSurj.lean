module

public import StacksFrontier.AlgebraicGeometry.Stacks.SpaceChartComparison

/-!
# The descent morphism on the object space attached to a groupoid transition

Let `t, s : Y ⟶ Z` be two morphisms of algebraic spaces and let `M` be a quasi-coherent module on
the fppf site of `𝒮_Z`.  Through the comparison maps of equation 076R along `t` and `s`, a
morphism `α : t_small^*(M|_{Z_étale}) ⟶ s_small^*(M|_{Z_étale})` of modules on the small étale
site of `Y` is the restriction to `Y_étale` of a unique morphism `β : t^*M ⟶ s^*M` of
quasi-coherent modules on `𝒮_Y`, by Stacks 0GQD for `Y`.

## Main definitions

* `AlgebraicGeometry.Stack.descentMorphismOfTransition`: the morphism `β : t^*M ⟶ s^*M` attached
  to `α`.

## Main results

* `AlgebraicGeometry.Stack.descentMorphismOfTransition_spec`: `β` restricts to `α` through the
  comparison maps along `t` and `s`.
* `AlgebraicGeometry.Stack.spaceEtaleInverseImageComparison_comp_restrictionMap`: for every
  `k : X ⟶ Y`, the restriction of `k^*β` to `X_étale` is the reindexing of `α` along `k`, read
  through the comparison maps along `k ≫ t` and `k ≫ s` (Stacks 075D (1)).
* `AlgebraicGeometry.Stack.pullbackTransport_comp_spaceComparison`: the comparison maps of
  equation 076R are compatible with transport along an equality of morphisms.

## References

* [Stacks Project, Tag 06WT](https://stacks.math.columbia.edu/tag/06WT)
* [Stacks Project, Tag 0GQD](https://stacks.math.columbia.edu/tag/0GQD)
* [Stacks Project, Tag 076R](https://stacks.math.columbia.edu/tag/076R)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

section Spaces

variable {X Y Z : AlgebraicSpaces C S hS}

/-- `h^*(k^*M)|_{X_étale} ≅ (h ⋙ k)^*M|_{X_étale}`, with identity components. -/
abbrev spacePullbackRestrictionIso (h : X ⟶ Y) (k : Y ⟶ Z) (M : SheafOfModules.{u} (spaceRing Z)) :
    @Iso (Space.Modules.{u, u} C S hS X.1 X.2) _
      (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj X) (spaceProj Y)
        (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Y)
        (spacePresentation X) (spaceFunctor h) (isFibredOneMorphism_spaceFunctor h)
        (spaceEtale ((spacePullback k).obj M)))
      (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj X) (spaceProj Z)
        (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Z)
        (spacePresentation X) (spaceFunctor h ⋙ spaceFunctor k)
        (isFibredOneMorphism_spaceFunctor_comp h k) (spaceEtale M)) :=
  pullbackRestrictionIso (spaceProj Y) (isFiberedInGroupoids_spaceProj Y) (spaceFunctor k)
    (spaceFunctor_comp_spaceProj k) (isFiberedInGroupoids_spaceProj Z) (spaceProj X)
    (isFiberedInGroupoids_spaceProj X) (spacePresentation X) (spaceFunctor h)
    (isFibredOneMorphism_spaceFunctor h) (isFibredOneMorphism_spaceFunctor_comp h k) M

/-- `(k^*M)|_{Y_étale} ≅ k^*M|_{Y_étale}`, with identity components. -/
abbrev spacePullbackSelfIso (k : Y ⟶ Z) (M : SheafOfModules.{u} (spaceRing Z)) :
    @Iso (Space.Modules.{u, u} C S hS Y.1 Y.2) _ (selfChartRestriction ((spacePullback k).obj M))
      (spaceEtaleInverseImage k M) :=
  pullbackRestrictionIso (spaceProj Y) (isFiberedInGroupoids_spaceProj Y) (spaceFunctor k)
    (spaceFunctor_comp_spaceProj k) (isFiberedInGroupoids_spaceProj Z) (spaceProj Y)
    (isFiberedInGroupoids_spaceProj Y) (spacePresentation Y) (𝟭 _)
    (isFibredOneMorphism_spaceId Y) (isFibredOneMorphism_spaceFunctor k) M

/-- The comparison map along `h` of the triangle `h ⋙ k = h ⋙ k`. -/
abbrev arrowComparison (h : X ⟶ Y) (k : Y ⟶ Z) (M : SheafOfModules.{u} (spaceRing Z)) :=
  Space.comparisonAlgebraicSpacesModules C S hS (spaceProj X) (spaceProj Y) (spaceProj Z)
    (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Y)
    (spacePresentation X) (spacePresentation Y) (spaceFunctor h) (spaceFunctor h ⋙ spaceFunctor k)
    (spaceFunctor k) (isFibredOneMorphism_spaceFunctor_comp h k)
    (isFibredOneMorphism_spaceFunctor k)
    (Iso.refl _) h (spaceFunctorChartIso h) (isFiberedInGroupoids_spaceProj Z)
    (isHomLift_spaceRefl_inv_app h k) (isHomLift_spaceFunctorChartIso_hom_app h) (spaceEtale M)

/-- **The comparison map along `h` of `k^*M` is the comparison map along `h` of the triangle
`h ⋙ k = h ⋙ k` for `M`.** -/
theorem spaceEtaleInverseImageComparison_spacePullback (h : X ⟶ Y) (k : Y ⟶ Z)
    (M : SheafOfModules.{u} (spaceRing Z)) :
    spaceEtaleInverseImageComparison h ((spacePullback k).obj M) ≫
      (spacePullbackRestrictionIso h k M).hom =
      (Space.modulePullback C S hS h).map (spacePullbackSelfIso k M).hom ≫
        arrowComparison h k M := by
  have h1 := comparisonAlgebraicSpacesModules_pullbackFunctor (spaceProj Y)
    (isFiberedInGroupoids_spaceProj Y) (spaceFunctor k) (spaceFunctor_comp_spaceProj k)
    (isFiberedInGroupoids_spaceProj Z) (spaceProj X) (isFiberedInGroupoids_spaceProj X)
    (spacePresentation X) (spaceProj Y) (isFiberedInGroupoids_spaceProj Y) (spacePresentation Y)
    (spaceFunctor h) (spaceFunctor h) (𝟭 _) (isFibredOneMorphism_spaceFunctor h)
    (isFibredOneMorphism_spaceId Y) (isFibredOneMorphism_spaceFunctor_comp h k)
    (isFibredOneMorphism_spaceFunctor k) (Functor.rightUnitor _) h (spaceFunctorChartIso h)
    (isHomLift_spaceRightUnitor_inv_app h) (isHomLift_spaceFunctorChartIso_hom_app h)
    (fun W => Space.isHomLift_whiskerTriangleIso_inv_app C S hS _ _ (spaceFunctor k)
      (isFibredOneMorphism_spaceFunctor k) _ _ _ _ (isHomLift_spaceRightUnitor_inv_app h) W) M
  refine h1.trans (congrArg (fun c => _ ≫ c) ?_)
  exact Space.comparisonAlgebraicSpacesModules_congr C S hS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ fun d => by simp [Space.comparisonMorphism]

/-- **The restriction of a descent morphism along `k`.**  Let `β : t^*M ⟶ s^*M` be a morphism of
modules on `𝒮_Y` whose restriction to `Y_étale` is, through the comparison maps along `t` and
`s`, a morphism `α : t_small^*(M|_{Z_étale}) ⟶ s_small^*(M|_{Z_étale})`.  Then for every
`k : X ⟶ Y` the restriction of `k^*β` to `X_étale` is, through the comparison maps along
`k ≫ t` and `k ≫ s`, the reindexing of `α` along `k`. -/
theorem spaceEtaleInverseImageComparison_comp_restrictionMap (t s : Y ⟶ Z)
    (M : SheafOfModules.{u} (spaceRing Z))
    (β : (spacePullback t).obj M ⟶ (spacePullback s).obj M)
    (α : (Space.modulePullback C S hS t).obj (selfChartRestriction M) ⟶
      (Space.modulePullback C S hS s).obj (selfChartRestriction M))
    (hβ : spaceEtaleInverseImageComparison t M ≫ (spacePullbackSelfIso t M).inv ≫
      selfChartRestrictionMap β ≫ (spacePullbackSelfIso s M).hom =
        α ≫ spaceEtaleInverseImageComparison s M) (k : X ⟶ Y) :
    spaceComparison (k ≫ t) (spaceFunctor k ⋙ spaceFunctor t)
          (isFibredOneMorphism_spaceFunctor_comp k t) (Functor.rightUnitor (spaceFunctor (k ≫ t)))
          (isHomLift_spaceRightUnitor_inv_app (k ≫ t)) M ≫ (spacePullbackRestrictionIso k t M).inv ≫
        spaceEtaleInverseImageMap k β ≫ (spacePullbackRestrictionIso k s M).hom =
      (Space.modulePullbackCompIso C S hS k t).inv.app
        (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj Z) (spaceProj Z)
          (isFiberedInGroupoids_spaceProj Z) (isFiberedInGroupoids_spaceProj Z)
          (spacePresentation Z) (𝟭 _) (isFibredOneMorphism_spaceId Z) (spaceEtale M)) ≫
        (Space.modulePullback C S hS k).map α ≫
          (Space.modulePullbackCompIso C S hS k s).hom.app
        (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj Z) (spaceProj Z)
          (isFiberedInGroupoids_spaceProj Z) (isFiberedInGroupoids_spaceProj Z)
          (spacePresentation Z) (𝟭 _) (isFibredOneMorphism_spaceId Z) (spaceEtale M)) ≫
            spaceComparison (k ≫ s) (spaceFunctor k ⋙ spaceFunctor s)
          (isFibredOneMorphism_spaceFunctor_comp k s) (Functor.rightUnitor (spaceFunctor (k ≫ s)))
          (isHomLift_spaceRightUnitor_inv_app (k ≫ s)) M := by
  have d1 := spaceEtaleInverseImageComparison_comp k t M
  have d2 := spaceEtaleInverseImageComparison_comp k s M
  have c1 := spaceEtaleInverseImageComparison_spacePullback k t M
  have c2 := spaceEtaleInverseImageComparison_spacePullback k s M
  have n := spaceEtaleInverseImageComparison_naturality k β
  have c1' : arrowComparison k t M ≫ (spacePullbackRestrictionIso k t M).inv =
      (Space.modulePullback C S hS k).map (spacePullbackSelfIso t M).inv ≫
        spaceEtaleInverseImageComparison k ((spacePullback t).obj M) := by
    rw [Iso.comp_inv_eq, Category.assoc, c1, ← CategoryTheory.Functor.map_comp_assoc,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← Iso.app_inv, Iso.eq_inv_comp, Iso.app_hom, ← reassoc_of% d1, reassoc_of% c1',
    reassoc_of% n, c2, ← d2]
  simp only [← CategoryTheory.Functor.map_comp_assoc]
  congr 2

/-- The forward map of `spacePullbackRestrictionIso h k M` is the transport along
`spaceEtaleInverseImage_comp h k M`. -/
theorem spacePullbackRestrictionIso_hom (h : X ⟶ Y) (k : Y ⟶ Z)
    (M : SheafOfModules.{u} (spaceRing Z)) :
    (spacePullbackRestrictionIso h k M).hom = eqToHom (spaceEtaleInverseImage_comp h k M).symm := by
  ext W x
  rfl

/-- The inverse map of `spacePullbackRestrictionIso h k M` is the transport along
`spaceEtaleInverseImage_comp h k M`. -/
theorem spacePullbackRestrictionIso_inv (h : X ⟶ Y) (k : Y ⟶ Z)
    (M : SheafOfModules.{u} (spaceRing Z)) :
    (spacePullbackRestrictionIso h k M).inv = eqToHom (spaceEtaleInverseImage_comp h k M) := by
  ext W x
  rfl

/-- The comparison map along `k ≫ t` with the composite 1-morphism. -/
abbrev compComparison (k : X ⟶ Y) (t : Y ⟶ Z) (M : SheafOfModules.{u} (spaceRing Z)) :=
  spaceComparison (k ≫ t) (spaceFunctor k ⋙ spaceFunctor t)
    (isFibredOneMorphism_spaceFunctor_comp k t) (Functor.rightUnitor (spaceFunctor (k ≫ t)))
    (isHomLift_spaceRightUnitor_inv_app (k ≫ t)) M

/-- The restriction to `X_étale` along a 2-morphism `θ : f₂ ⟶ f₁` of 1-morphisms into `𝒮_Z`. -/
abbrev spaceTwoMorphism (f₁ f₂ : spaceCat X ⥤ spaceCat Z)
    (hf₁ : (spaceProj X).IsFibredOneMorphism (spaceProj Z) f₁)
    (hf₂ : (spaceProj X).IsFibredOneMorphism (spaceProj Z) f₂) (θ : f₂ ⟶ f₁)
    (hθ : ∀ W, (spaceProj Z).IsHomLift (𝟙 ((spaceProj Z).obj (f₂.obj W))) (θ.app W))
    (M : SheafOfModules.{u} (spaceRing Z)) :=
  Space.etaleRestrictedModuleInverseImageTwoMorphism C S hS (spaceProj X) (spaceProj Z)
    (isFiberedInGroupoids_spaceProj X) (isFiberedInGroupoids_spaceProj Z) (spacePresentation X)
    f₁ f₂ hf₁ hf₂ θ hθ (spaceEtale M)

/-- **Transport of the comparison map of equation 076R along an equality of morphisms**, with a
2-morphism of the 1-morphisms. -/
theorem pullbackTransport_comp_spaceComparison {m₁ m₂ : X ⟶ Z} (h : m₁ = m₂)
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
    Space.pullbackTransport (selfChartRestriction M) h ≫ spaceComparison m₂ f₂ hf₂ φ₂ hφ₂ M =
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
  have hT : Space.pullbackTransport (selfChartRestriction M) (rfl : m₁ = m₁) = 𝟙 _ := by
    simp [Space.pullbackTransport]
  rwa [hT, Category.id_comp]

/-- The right unitor followed by a transport along an equality of functors. -/
theorem rightUnitor_hom_app_comp_eqToHom_app {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    {F G : 𝒟 ⥤ 𝒞} (e : F = G) (W : 𝒟) (p : (F ⋙ 𝟭 𝒞).obj W = (G ⋙ 𝟭 𝒞).obj W) :
    (Functor.rightUnitor F).hom.app W ≫ (eqToHom e).app W =
      eqToHom p ≫ (Functor.rightUnitor G).hom.app W := by
  subst e
  simp

/-- Transport of the comparison maps along composites. -/
theorem pullbackTransport_comp_compComparison {k₁ k₂ : X ⟶ Y} {t₁ t₂ : Y ⟶ Z}
    (h : k₁ ≫ t₁ = k₂ ≫ t₂) (M : SheafOfModules.{u} (spaceRing Z))
    (hθ : ∀ W, (spaceProj Z).IsHomLift (𝟙 ((spaceProj Z).obj
      ((spaceFunctor k₂ ⋙ spaceFunctor t₂).obj W)))
      ((eqToHom (congrArg spaceFunctor h).symm :
        spaceFunctor k₂ ⋙ spaceFunctor t₂ ⟶ spaceFunctor k₁ ⋙ spaceFunctor t₁).app W)) :
    Space.pullbackTransport (selfChartRestriction M) h ≫ compComparison k₂ t₂ M =
      compComparison k₁ t₁ M ≫ spaceTwoMorphism _ _ (isFibredOneMorphism_spaceFunctor_comp k₁ t₁)
        (isFibredOneMorphism_spaceFunctor_comp k₂ t₂) (eqToHom (congrArg spaceFunctor h).symm)
        hθ M :=
  pullbackTransport_comp_spaceComparison h _ _ _ _ _ _ _ _ _ hθ
    (fun W => rightUnitor_hom_app_comp_eqToHom_app (F := spaceFunctor (k₂ ≫ t₂))
      (G := spaceFunctor (k₁ ≫ t₁)) (congrArg spaceFunctor h).symm W _) M

/-- Cancellation of an isomorphism on the left. -/
theorem eq_of_comp_eq_comp_of_isIso {𝒞 : Type*} [Category 𝒞] {A B C : 𝒞} (f : A ⟶ B) [IsIso f]
    {g g' : B ⟶ C} (h : f ≫ g = f ≫ g') : g = g' := by
  simpa using congrArg (inv f ≫ ·) h

/-- `spaceEtaleInverseImageComparison_comp_restrictionMap`, stated with `compComparison` and with
the reindexing of `α` along `k` grouped. -/
theorem spaceEtaleInverseImageComparison_comp_restrictionMap_assoc (t s : Y ⟶ Z)
    (M : SheafOfModules.{u} (spaceRing Z))
    (β : (spacePullback t).obj M ⟶ (spacePullback s).obj M)
    (α : (Space.modulePullback C S hS t).obj (selfChartRestriction M) ⟶
      (Space.modulePullback C S hS s).obj (selfChartRestriction M))
    (hβ : spaceEtaleInverseImageComparison t M ≫ (spacePullbackSelfIso t M).inv ≫
      selfChartRestrictionMap β ≫ (spacePullbackSelfIso s M).hom =
        α ≫ spaceEtaleInverseImageComparison s M) (k : X ⟶ Y) :
    compComparison k t M ≫ (spacePullbackRestrictionIso k t M).inv ≫
      spaceEtaleInverseImageMap k β ≫ (spacePullbackRestrictionIso k s M).hom =
      ((Space.modulePullbackCompIso C S hS k t).inv.app
        (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj Z) (spaceProj Z)
          (isFiberedInGroupoids_spaceProj Z) (isFiberedInGroupoids_spaceProj Z)
          (spacePresentation Z) (𝟭 _) (isFibredOneMorphism_spaceId Z) (spaceEtale M)) ≫
        (Space.modulePullback C S hS k).map α ≫
          (Space.modulePullbackCompIso C S hS k s).hom.app
            (Space.etaleRestrictedModuleInverseImage C S hS (spaceProj Z) (spaceProj Z)
          (isFiberedInGroupoids_spaceProj Z) (isFiberedInGroupoids_spaceProj Z)
          (spacePresentation Z) (𝟭 _) (isFibredOneMorphism_spaceId Z) (spaceEtale M))) ≫
        compComparison k s M := by
  rw [spaceEtaleInverseImageComparison_comp_restrictionMap t s M β α hβ k]
  simp only [Category.assoc]

end Spaces

/-! ### The descent morphism attached to a transition on the small étale site -/

section Beta

variable {Y Z : AlgebraicSpaces C S hS} (t s : Y ⟶ Z)
  (M : FibredSite.quasicoherentModules.{u, u + 1, u, u} C S hS (spaceProj Z)
    (isFiberedInGroupoids_spaceProj Z))

/-- The inverse image of a quasi-coherent module along a morphism of algebraic spaces, as a
quasi-coherent module on `𝒮_Y`. -/
abbrev spaceQuasicoherentPullback (k : Y ⟶ Z) :
    FibredSite.quasicoherentModules.{u, u + 1, u, u} C S hS (spaceProj Y)
      (isFiberedInGroupoids_spaceProj Y) :=
  ⟨(spacePullback k).obj M.obj, isQuasicoherentOnSite_modulePullback' C S hS _ _
    (isFiberedInGroupoids_spaceProj Y) (isFiberedInGroupoids_spaceProj Z) (spaceFunctor k)
    (spaceFunctor_comp_spaceProj k) M.obj M.property⟩

/-- The comparison map along `k` of a quasi-coherent module is an isomorphism. -/
instance (k : Y ⟶ Z) : IsIso (spaceEtaleInverseImageComparison k M.obj) :=
  Space.isIso_comparisonAlgebraicSpacesModules_of_quasicoherentModules C S hS _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ M

/-- **The descent morphism `β : t^*M ⟶ s^*M` on `𝒮_Y` attached to a morphism
`α : t_small^*(M|_{Z_étale}) ⟶ s_small^*(M|_{Z_étale})`**: the preimage under the equivalence of
Stacks 0GQD on `Y` of `α` read through the comparison maps along `t` and `s`. -/
def descentMorphismOfTransition
    (α : (Space.modulePullback C S hS t).obj (selfChartRestriction M.obj) ⟶
      (Space.modulePullback C S hS s).obj (selfChartRestriction M.obj)) :
    (spacePullback t).obj M.obj ⟶ (spacePullback s).obj M.obj :=
  ((spaceQuasicoherentRestriction Y).preimage
    (X := spaceQuasicoherentPullback M t) (Y := spaceQuasicoherentPullback M s)
    (ObjectProperty.homMk ((spacePullbackSelfIso t M.obj).hom ≫
      inv (spaceEtaleInverseImageComparison t M.obj) ≫ α ≫
        spaceEtaleInverseImageComparison s M.obj ≫ (spacePullbackSelfIso s M.obj).inv))).hom

/-- `descentMorphismOfTransition t s M α` restricts to `α` through the comparison maps along `t`
and `s`. -/
theorem descentMorphismOfTransition_spec
    (α : (Space.modulePullback C S hS t).obj (selfChartRestriction M.obj) ⟶
      (Space.modulePullback C S hS s).obj (selfChartRestriction M.obj)) :
    spaceEtaleInverseImageComparison t M.obj ≫ (spacePullbackSelfIso t M.obj).inv ≫
        selfChartRestrictionMap (descentMorphismOfTransition t s M α) ≫
          (spacePullbackSelfIso s M.obj).hom = α ≫ spaceEtaleInverseImageComparison s M.obj := by
  have h := congrArg (fun φ => φ.hom)
    ((spaceQuasicoherentRestriction Y).map_preimage
      (X := spaceQuasicoherentPullback M t) (Y := spaceQuasicoherentPullback M s)
      (ObjectProperty.homMk ((spacePullbackSelfIso t M.obj).hom ≫
        inv (spaceEtaleInverseImageComparison t M.obj) ≫ α ≫
          spaceEtaleInverseImageComparison s M.obj ≫ (spacePullbackSelfIso s M.obj).inv)))
  rw [spaceQuasicoherentRestriction_map_hom] at h
  change selfChartRestrictionMap (descentMorphismOfTransition t s M α) = _ at h
  rw [h]
  change spaceEtaleInverseImageComparison t M.obj ≫ (spacePullbackSelfIso t M.obj).inv ≫
      ((spacePullbackSelfIso t M.obj).hom ≫ inv (spaceEtaleInverseImageComparison t M.obj) ≫ α ≫
        spaceEtaleInverseImageComparison s M.obj ≫ (spacePullbackSelfIso s M.obj).inv) ≫
          (spacePullbackSelfIso s M.obj).hom = α ≫ spaceEtaleInverseImageComparison s M.obj
  simp only [Category.assoc, Iso.inv_hom_id_assoc, IsIso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id]

end Beta

end AlgebraicGeometry.Stack

end
