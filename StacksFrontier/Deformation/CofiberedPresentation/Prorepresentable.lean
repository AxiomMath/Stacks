module

import StacksFrontier.Deformation.Examples.Linear.ContinuousRepresentationsDenseRestriction
public import StacksFrontier.Deformation.Applications.TangentModuleEquivalence
public import StacksFrontier.Deformation.Applications.TwoFibreProductSelfExact
public import StacksFrontier.Deformation.Cofibered.BasedEquivalenceFibre
public import StacksFrontier.Deformation.CofiberedPresentation.Groupoid
public import StacksFrontier.Deformation.Examples.Linear.RimSchlessingerTransportEquivalence
public import StacksFrontier.Deformation.Formal.Groupoid.Prorepresentable
public import StacksFrontier.Deformation.Groupoid.Smooth
public import StacksFrontier.Deformation.Schlessinger.Prorepresentable

/-!
# Prorepresentability of the groupoid in functors of a presentation

Let `ℱ` be a deformation category, let `U : 𝒞_Λ → Sets` be a prorepresentable functor and let
`f : U → ℱ` be a `1`-morphism of categories cofibered in groupoids. The groupoid in functors
`(U, R, s, t, c)` that `Deformation.presentationGroupoid` builds from `f` is prorepresentable as
soon as the infinitesimal automorphisms of `ℱ` form a finite-dimensional `k`-vector space.

## Main definitions

* `Deformation.uliftFunctorSelfIsoId`: wrapping in `ULift` to a universe a type already lies in
  does not change it.
* `Deformation.presentationArrowsEquivalence`, `Deformation.presentationArrowsBasedFunctor`: the
  comparison of the arrow functor's category of elements with the self `2`-fibre product taken
  over the projections `f ⋙ p`, as an equivalence and as a `1`-morphism over the base.
* `Deformation.presentationSourceBasedFunctor`: the source projection `s`, as a `1`-morphism
  from `R` to `U` over the base.

## Main results

* `CategoryTheory.TwoFibreProductOver.congrProjections`: equal projections present the same
  `2`-fibre product.
* `Deformation.isProrepresentable_comp_uliftFunctor`: prorepresentability is unaffected by
  raising the values of the functor into a universe they already lie in.
* `Deformation.chosenPushforwardsAtOfCofibered`: a category cofibered in groupoids admits a
  choice of pushforwards of a given object.
* `Deformation.finiteDimensional_tangentModuleAt_of_eq`: finite-dimensionality of a tangent
  module transports along an equality of the projections.
* `Deformation.isDeformationFunctor_presentationArrows`: the arrow functor is a deformation
  functor.
* `Deformation.injective_derivationToTangentSpace_presentationArrows`: the derivation map of the
  arrow functor is injective.
* `Deformation.finiteDimensional_tangentSpace_presentationArrows`: the tangent space of the
  arrow functor is finite-dimensional.
* `Deformation.isProrepresentable_presentationArrows`: the arrow functor is prorepresentable.
* `Deformation.isProrepresentable_presentationGroupoid`: Stacks 06L7, the groupoid in functors of
  a presentation is prorepresentable.

## References

* [Stacks Project, Tag 06L7](https://stacks.math.columbia.edu/tag/06L7)
-/

@[expose] public section

/-! ### Transport of a 2-fibre product along equalities of the two projections -/

namespace CategoryTheory.TwoFibreProductOver

section
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  {p𝒳 p𝒳' : 𝒳 ⥤ 𝒞} {p𝒴 p𝒴' : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {Φ : 𝒳 ⥤ 𝒮} {Ψ : 𝒴 ⥤ 𝒮}

/-- `2`-fibre products taken over equal projections are equivalent. -/
public def congrProjections (h𝒳 : p𝒳 = p𝒳') (h𝒴 : p𝒴 = p𝒴') :
    TwoFibreProductOver p𝒳 p𝒴 p𝒮 Φ Ψ ≌ TwoFibreProductOver p𝒳' p𝒴' p𝒮 Φ Ψ := by
  subst h𝒳
  subst h𝒴
  exact CategoryTheory.Equivalence.refl

/-- The transport along equal projections is a functor over the base. -/
public theorem congrProjections_comp_structureFunctor (h𝒳 : p𝒳 = p𝒳') (h𝒴 : p𝒴 = p𝒴') :
    (congrProjections (p𝒮 := p𝒮) (Φ := Φ) (Ψ := Ψ) h𝒳 h𝒴).functor ⋙
        structureFunctor p𝒳' p𝒴' p𝒮 Φ Ψ = structureFunctor p𝒳 p𝒴 p𝒮 Φ Ψ := by
  subst h𝒳
  subst h𝒴
  rfl

end

end CategoryTheory.TwoFibreProductOver

namespace Deformation

/-! ### Raising the values of a prorepresentable functor -/

section
open CategoryTheory
universe u w a b

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Wrapping a type in `ULift` to a universe it already lies in does not change it. -/
public def uliftFunctorSelfIsoId : uliftFunctor.{a, max a b} ≅ 𝟭 (Type (max a b)) :=
  NatIso.ofComponents fun _ => Equiv.ulift.toIso

/-- Prorepresentability is unaffected by raising the values of the functor into a universe they
already lie in. -/
public theorem isProrepresentable_comp_uliftFunctor
    (U : ArtinianLocalAlgCat.{u, max a b, w} Λ k ⥤ Type (max a b))
    (hU : IsProrepresentable U) :
    IsProrepresentable (U ⋙ uliftFunctor.{a, max a b}) := by
  obtain ⟨R, ⟨e⟩⟩ := hU
  exact ⟨R, ⟨Functor.isoWhiskerLeft U uliftFunctorSelfIsoId.{a, b} ≪≫ e⟩⟩

end

/-! ### Choices of pushforwards at a single object -/

section
open CategoryTheory
universe u₁ v₁ u₂ v₂

/-- A category cofibered in groupoids admits a choice of pushforwards of a given object along
every arrow out of its base. -/
public noncomputable def chosenPushforwardsAtOfCofibered {X : Type u₁} [Category.{v₁} X]
    {C : Type u₂} [Category.{v₂} C] {p : X ⥤ C} (hp : IsCofiberedInGroupoids p) (x : X) :
    ChosenPushforwardsAt p x := by
  classical
  choose y i hi using fun A : Under (p.obj x) => exists_pushforward hp A.hom x rfl
  have hobj : ∀ A : Under (p.obj x), p.obj (y A) = A.right := by
    intro A
    let := hi A
    exact CategoryTheory.IsHomLift.codomain_eq p A.hom (i A)
  exact ChosenPushforwardsAt.ofCofiberedInGroupoids hp
    (fun A => ⟨y A, hobj A⟩) (fun A => i A) (fun A => hi A)

end

/-! ### Fullness and faithfulness on fibres -/

section
open CategoryTheory CategoryTheory.Functor
universe uB vB uA vA uA' vA'

variable {B : Type uB} [Category.{vB} B] {𝓐 : BasedCategory.{vA, uA} B}
  {𝓑 : BasedCategory.{vA', uA'} B}

end

/-! ### The comparisons attached to a presentation -/

section
open CategoryTheory CategoryTheory.Functor
universe uC vC uF vF uU

variable {C : Type uC} [Category.{vC} C] {F : Type uF} [Category.{vF} F]
  {pF : F ⥤ C} {U : C ⥤ Type uU} {f : U.Elements ⥤ F}
  {hover : f ⋙ pF = CategoryOfElements.π U}

/-- The category of elements of a presentation's arrow functor, compared with the self
`2`-fibre product taken over the projections `f ⋙ p` of the two legs. -/
public def presentationArrowsEquivalence (P : PresentationGroupoid pF U f hover) :
    P.arrows.Elements ≌ TwoFibreProductOver (f ⋙ pF) (f ⋙ pF) pF f f :=
  P.fibreProductEquivalence.trans
    (CategoryTheory.TwoFibreProductOver.congrProjections hover.symm hover.symm)

/-- The comparison of a presentation's arrow functor with the self `2`-fibre product, as a
`1`-morphism over the base. -/
public def presentationArrowsBasedFunctor (P : PresentationGroupoid pF U f hover) :
    BasedCategory.ofFunctor (CategoryOfElements.π P.arrows) ⥤ᵇ
      BasedCategory.ofFunctor
        (TwoFibreProductOver.structureFunctor (f ⋙ pF) (f ⋙ pF) pF f f) where
  toFunctor := (presentationArrowsEquivalence P).functor
  w := by
    change (P.fibreProductEquivalence.functor ⋙
      (CategoryTheory.TwoFibreProductOver.congrProjections hover.symm hover.symm).functor) ⋙
        TwoFibreProductOver.structureFunctor (f ⋙ pF) (f ⋙ pF) pF f f = _
    rw [Functor.assoc,
      CategoryTheory.TwoFibreProductOver.congrProjections_comp_structureFunctor]
    exact P.fibreProductOverBase

/-- The source projection `s : R → U` of a presentation, as a `1`-morphism over the base: the map
on categories of elements induced by `s`, followed by the comparison identifying the category of
elements of a universe-lifted functor with that of the functor itself. -/
public def presentationSourceBasedFunctor (P : PresentationGroupoid pF U f hover) :
    BasedCategory.ofFunctor (CategoryOfElements.π P.arrows) ⥤ᵇ
      BasedCategory.ofFunctor (CategoryOfElements.π U) where
  toFunctor := CategoryOfElements.map P.source ⋙ (uliftElementsEquivalence U).inverse
  w := rfl

end

/-! ### Transport of a tangent module along an equality of the projections -/

section
open CategoryTheory CategoryTheory.Functor
universe u v w uX vX

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Finite-dimensionality of a tangent module transports along an equality of the projections. -/
public theorem finiteDimensional_tangentModuleAt_of_eq {X : Type uX} [Category.{vX} X]
    {p q : X ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k} (h : p = q)
    (hp : IsDeformationCategory.{u, v, w} p) (hq : IsDeformationCategory.{u, v, w} q)
    (M : FGModuleCat.{max v w} k)
    (hfin : FiniteDimensional k
      ↥(tangentModuleAt.{u, v, w} (BasedCategory.ofFunctor q) hq M)) :
    FiniteDimensional k
      ↥(tangentModuleAt.{u, v, w} (BasedCategory.ofFunctor p) hp M) := by
  subst h
  exact hfin

end

/-! ### Stacks 06L7 -/

section
open CategoryTheory CategoryTheory.Functor
universe u v w u₃ v₃

variable {Λ : Type u} {k : Type w} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k] {F : Type u₃} [Category.{v₃} F]
  (pF : F ⥤ ArtinianLocalAlgCat.{u, max v v₃ w, w} Λ k)
  (U : ArtinianLocalAlgCat.{u, max v v₃ w, w} Λ k ⥤ Type (max v v₃ w))
  (f : U.Elements ⥤ F) (hover : f ⋙ pF = CategoryOfElements.π U)

omit [IsNoetherianRing Λ] [Module.Finite Λ k] in
/-- The arrow functor of a presentation of a deformation category by a deformation functor is a
deformation functor. -/
public theorem isDeformationFunctor_presentationArrows
    (hU : IsDeformationFunctor.{u, max v v₃, w} U)
    (hF : IsDeformationCategory.{u, max v v₃, w} pF) :
    IsDeformationFunctor.{u, max v v₃, w}
      (presentationGroupoid pF U f hover hF.predeformation.cofibered).arrows := by
  have hπU : IsDeformationCategory.{u, max v v₃, w} (CategoryOfElements.π U) :=
    (isDeformationCategory_iff U).mpr hU
  set P := presentationGroupoid pF U f hover hF.predeformation.cofibered
  have h𝒲 : IsDeformationCategory.{u, max v v₃, w}
      (TwoFibreProductOver.structureFunctor
        (CategoryOfElements.π U) (CategoryOfElements.π U) pF f f) :=
    isDeformationCategory_twoFibreProductOver.{u, max v v₃, w} (CategoryOfElements.π U)
      (CategoryOfElements.π U) pF f f hover hover hπU hπU hF
  have hcof : IsCofiberedInGroupoids
      (P.fibreProductEquivalence.functor ⋙ TwoFibreProductOver.structureFunctor
        (CategoryOfElements.π U) (CategoryOfElements.π U) pF f f) := by
    rw [P.fibreProductOverBase]
    exact categoryOfElements_projection_isCofibered P.arrows
  have hne : Nonempty
      ((P.fibreProductEquivalence.functor ⋙ TwoFibreProductOver.structureFunctor
        (CategoryOfElements.π U) (CategoryOfElements.π U) pF f f).Fiber
          (residueFieldObject.{u, max v v₃, w} Λ k)) := by
    rw [P.fibreProductOverBase]
    let := hU.1.some
    refine ⟨⟨⟨residueFieldObject.{u, max v v₃, w} Λ k, (P.arrowEquiv _).symm ?_⟩, rfl⟩⟩
    exact
      { target := default
        source := default
        iso := Iso.refl _
        vertical := by simp }
  have hπR : IsDeformationCategory.{u, max v v₃, w} (CategoryOfElements.π P.arrows) := by
    rw [← P.fibreProductOverBase]
    exact Deformation.Examples.isDeformationCategory_comp_of_essSurj.{u, max v v₃, w}
      P.fibreProductEquivalence.functor _ hcof hne h𝒲
  exact (isDeformationCategory_iff P.arrows).mp hπR

/-- When `U` is prorepresentable, the derivation map of the arrow functor of a presentation is
injective. -/
public theorem injective_derivationToTangentSpace_presentationArrows
    (hU : IsProrepresentable U) (hF : IsDeformationCategory.{u, max v v₃, w} pF)
    (hR : IsDeformationCategory.{u, max v v₃, w} (CategoryOfElements.π
      (presentationGroupoid pF U f hover hF.predeformation.cofibered).arrows)) :
    Function.Injective (derivationToTangentSpace.{u, max v v₃, w}
      (CategoryOfElements.π
        (presentationGroupoid pF U f hover hF.predeformation.cofibered).arrows)
      hR.predeformation) := by
  obtain ⟨hUdef, -, hUinj⟩ := (isProrepresentable_iff_isDeformationFunctor U).mp hU
  have hπU : IsDeformationCategory.{u, max v v₃, w} (CategoryOfElements.π U) :=
    (isDeformationCategory_iff U).mpr hUdef
  set P := presentationGroupoid pF U f hover hF.predeformation.cofibered
  have nat := derivationToTangentSpace_naturality.{u, max v v₃, w}
    (CategoryOfElements.π P.arrows) hR.predeformation
    (CategoryOfElements.π U) hπU.predeformation (presentationSourceBasedFunctor P)
  intro D D' hDD
  apply hUinj
  rw [← nat D, ← nat D', hDD]

/-- When `U` is prorepresentable and the infinitesimal automorphisms of `ℱ` are finite-dimensional,
the tangent space of the arrow functor of a presentation is finite-dimensional. -/
public theorem finiteDimensional_tangentSpace_presentationArrows
    (hU : IsProrepresentable U) (hF : IsDeformationCategory.{u, max v v₃, w} pF)
    {y₀ : U.Elements} (PF : ChosenPushforwardsAt pF (f.obj y₀))
    (hInf : FiniteDimensional k
      ↥((infinitesimalAutomorphismLinearLift.{u, max v v₃, w} PF hF.satisfiesRS).functor.obj
        (FGModuleCat.of k (ULift.{max v v₃} k))))
    (hR : IsDeformationCategory.{u, max v v₃, w} (CategoryOfElements.π
      (presentationGroupoid pF U f hover hF.predeformation.cofibered).arrows))
    [Fact (IsPredeformationCategory.{u, max v v₃, w}
      (BasedCategory.ofFunctor (CategoryOfElements.π
        (presentationGroupoid pF U f hover hF.predeformation.cofibered).arrows)).p)]
    [Fact (SchlessingerConditionS2 (CategoryOfElements.π (isomorphismClasses
      (BasedCategory.ofFunctor (CategoryOfElements.π
        (presentationGroupoid pF U f hover hF.predeformation.cofibered).arrows))
      hR.predeformation.cofibered)))] :
    FiniteDimensional k (tangentSpaceArtinian.{u, w, max v v₃} Λ k (isomorphismClasses
      (BasedCategory.ofFunctor (CategoryOfElements.π
        (presentationGroupoid pF U f hover hF.predeformation.cofibered).arrows))
      hR.predeformation.cofibered)) := by
  classical
  obtain ⟨hUdef, hUfin, -⟩ := (isProrepresentable_iff_isDeformationFunctor U).mp hU
  have hπU : IsDeformationCategory.{u, max v v₃, w} (CategoryOfElements.π U) :=
    (isDeformationCategory_iff U).mpr hUdef
  set M₁ : FGModuleCat.{max v v₃ w} k := FGModuleCat.of k (ULift.{max v v₃} k)
  set P := presentationGroupoid pF U f hover hF.predeformation.cofibered
  have hH : IsDeformationCategory.{u, max v v₃, w} (f ⋙ pF) :=
    isDeformationCategory_comp_of_isDeformationFunctor.{u, max v v₃, w} U pF f hover hUdef
  let : Fact (IsPredeformationCategory.{u, max v v₃, w}
      (BasedCategory.ofFunctor (CategoryOfElements.π U)).p) := ⟨hπU.predeformation⟩
  let : Fact (SchlessingerConditionS2 (CategoryOfElements.π (isomorphismClasses
      (BasedCategory.ofFunctor (CategoryOfElements.π U))
      hπU.predeformation.cofibered))) := ⟨tangentConditionS2.{u, max v v₃, w} hπU⟩
  have hTU : FiniteDimensional k ↥(tangentModuleAt.{u, max v v₃, w}
      (BasedCategory.ofFunctor (CategoryOfElements.π U)) hπU M₁) :=
    (associatedTangentSpaceCarrierLinearEquiv.{u, max v v₃, w}
      (BasedCategory.ofFunctor (CategoryOfElements.π U)) hπU.predeformation
      (tangentConditionS2.{u, max v v₃, w} hπU)).symm.finiteDimensional
  have hTH : FiniteDimensional k ↥(tangentModuleAt.{u, max v v₃, w}
      (BasedCategory.ofFunctor (f ⋙ pF)) hH M₁) :=
    finiteDimensional_tangentModuleAt_of_eq hover hH hπU M₁ hTU
  let PH : ChosenPushforwardsAt (f ⋙ pF) y₀ :=
    chosenPushforwardsAtOfCofibered hH.predeformation.cofibered y₀
  obtain ⟨-, hex⟩ := exact_selfBoundaryLinearMap_tangentProjPair.{u, max v v₃, w}
    U pF f hover hUdef hF PH PF M₁
  have hexr : Function.Exact
      (selfBoundaryLinearMap.{u, max v v₃, w} pF U f
        hH hF PH PF M₁)
      (tangentProjPair.{u, max v v₃, w} pF f f hH hH hF M₁).rangeRestrict := by
    rwa [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, ← LinearMap.exact_iff]
  have hT𝒲 : FiniteDimensional k ↥(tangentModuleAt.{u, max v v₃, w}
      (productBased.{u, max v v₃, w} pF f f)
      (isDeformationCategory_productBased.{u, max v v₃, w} pF f f hH hH hF) M₁) :=
    Module.Finite.of_exact hexr (LinearMap.surjective_rangeRestrict _)
  have : (presentationArrowsBasedFunctor P).toFunctor.Full :=
    CategoryTheory.Equivalence.full_functor (presentationArrowsEquivalence P)
  have : (presentationArrowsBasedFunctor P).toFunctor.Faithful :=
    CategoryTheory.Equivalence.faithful_functor (presentationArrowsEquivalence P)
  have : (presentationArrowsBasedFunctor P).toFunctor.EssSurj :=
    CategoryTheory.Equivalence.essSurj_functor (presentationArrowsEquivalence P)
  have hTR : FiniteDimensional k ↥(tangentModuleAt.{u, max v v₃, w}
      (BasedCategory.ofFunctor (CategoryOfElements.π P.arrows)) hR M₁) :=
    finiteDimensional_tangentModuleAt_of_fiberEquivalence.{u, max v v₃, w} hR
      (isDeformationCategory_productBased.{u, max v v₃, w} pF f f hH hH hF)
      (presentationArrowsBasedFunctor P) M₁
      (Deformation.full_fiberFunctor (presentationArrowsBasedFunctor P) _)
      (Deformation.faithful_fiberFunctor (presentationArrowsBasedFunctor P) _)
      (essSurj_fiberFunctor (categoryOfElements_projection_isCofibered P.arrows)
        (presentationArrowsBasedFunctor P) _) hT𝒲
  exact (associatedTangentSpaceCarrierLinearEquiv.{u, max v v₃, w}
    (BasedCategory.ofFunctor (CategoryOfElements.π P.arrows)) hR.predeformation
    (tangentConditionS2.{u, max v v₃, w} hR)).finiteDimensional

/-- When `U` is prorepresentable and the infinitesimal automorphisms of `ℱ` are finite-dimensional,
the arrow functor of a presentation is prorepresentable. -/
public theorem isProrepresentable_presentationArrows
    (hU : IsProrepresentable U) (hF : IsDeformationCategory.{u, max v v₃, w} pF)
    {y₀ : U.Elements} (PF : ChosenPushforwardsAt pF (f.obj y₀))
    (hInf : FiniteDimensional k
      ↥((infinitesimalAutomorphismLinearLift.{u, max v v₃, w} PF hF.satisfiesRS).functor.obj
        (FGModuleCat.of k (ULift.{max v v₃} k)))) :
    IsProrepresentable
      (presentationGroupoid pF U f hover hF.predeformation.cofibered).arrows := by
  obtain ⟨hUdef, -, -⟩ := (isProrepresentable_iff_isDeformationFunctor U).mp hU
  have hRdef : IsDeformationFunctor.{u, max v v₃, w}
      (presentationGroupoid pF U f hover hF.predeformation.cofibered).arrows :=
    isDeformationFunctor_presentationArrows.{u, v, w, u₃, v₃} pF U f hover hUdef hF
  have hR : IsDeformationCategory.{u, max v v₃, w} (CategoryOfElements.π
      (presentationGroupoid pF U f hover hF.predeformation.cofibered).arrows) :=
    (isDeformationCategory_iff _).mpr hRdef
  let : Fact (IsPredeformationCategory.{u, max v v₃, w}
      (BasedCategory.ofFunctor (CategoryOfElements.π
        (presentationGroupoid pF U f hover hF.predeformation.cofibered).arrows)).p) :=
    ⟨hR.predeformation⟩
  let : Fact (SchlessingerConditionS2 (CategoryOfElements.π (isomorphismClasses
      (BasedCategory.ofFunctor (CategoryOfElements.π
        (presentationGroupoid pF U f hover hF.predeformation.cofibered).arrows))
      hR.predeformation.cofibered))) := ⟨tangentConditionS2.{u, max v v₃, w} hR⟩
  exact (isProrepresentable_iff_isDeformationFunctor _).mpr ⟨hRdef,
    finiteDimensional_tangentSpace_presentationArrows.{u, v, w, u₃, v₃} pF U f hover hU hF PF hInf
      hR,
    injective_derivationToTangentSpace_presentationArrows.{u, v, w, u₃, v₃} pF U f hover hU hF hR⟩

/-- Let `ℱ` be a deformation category, let `U : 𝒞_Λ → Sets` be a prorepresentable functor and let
`f : U → ℱ` be a `1`-morphism of categories cofibered in groupoids. Let `(U, R, s, t, c)` be the
groupoid in functors on `𝒞_Λ` constructed from `f` in Stacks 06KY. If `dim_k Inf(ℱ) < ∞`, then
`(U, R, s, t, c)` is prorepresentable.

The finite-dimensionality hypothesis is read at one basepoint `y₀` of `U` and one choice `PF` of
pushforwards there. -/
@[stacks 06L7 "the hom-set universe of ℱ is at most that of 𝒞_Λ: the base is written \
ArtinianLocalAlgCat.{u, max v v₃ w, w} with v₃ the hom-set universe of ℱ, because the criterion \
of 06KG part (2) is available only at value universe equal to the hom-set universe"]
public theorem isProrepresentable_presentationGroupoid
    (hU : IsProrepresentable U) (hF : IsDeformationCategory.{u, max v v₃, w} pF)
    {y₀ : U.Elements} (PF : ChosenPushforwardsAt pF (f.obj y₀))
    (hInf : FiniteDimensional k
      ↥((infinitesimalAutomorphismLinearLift.{u, max v v₃, w} PF hF.satisfiesRS).functor.obj
        (FGModuleCat.of k (ULift.{max v v₃} k)))) :
    GroupoidInFunctors.IsProrepresentable
      ((presentationGroupoid pF U f hover hF.predeformation.cofibered).toGroupoidInFunctors) :=
  (GroupoidInFunctors.isProrepresentable_iff_objects_arrows _).mpr
    ⟨isProrepresentable_comp_uliftFunctor.{u, w, v₃, max v w} U hU,
      isProrepresentable_presentationArrows.{u, v, w, u₃, v₃} pF U f hover hU hF PF hInf⟩

end

end Deformation

end
