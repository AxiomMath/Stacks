module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleMorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleModuleComparison

/-!
# The associated module and the pullback along `a_{small}^♯`

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `φ : x ⟶ y` be an arrow
of `𝒳` lying over a morphism of schemes `a : U ⟶ V`. The map `a_{small}^♯` of structure sheaves
`AlgebraicGeometry.Stack.smallEtaleStructureComparison` is the structure map of the morphism of
ringed sites `ε_a` of small étale sites, and the sheafification of the pullback of presheaves of
modules of `𝓕^a` along `a_{small}^♯` is `(a^*𝓕)^a`, naturally in the `𝒪_V`-module `𝓕`.

## Main definitions

* `PresheafOfModules.pullbackCongr`: the pullbacks of presheaves of modules along two equal maps
  of presheaves of rings are isomorphic.
* `AlgebraicGeometry.Stack.smallEtalePullbackComparisonIso`: the pullback of presheaves of
  modules along `a_{small}^♯` is the pullback along the structure map of `ε_a`.
* `AlgebraicGeometry.Stack.associatedModuleSmallEtaleBaseChangeIso`: the sheafified pullback of
  `𝓕^a` along `a_{small}^♯` is `(a^*𝓕)^a`, as an isomorphism of functors.
* `AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso`: the same at one module.

## Main results

* `AlgebraicGeometry.Stack.localStructurePresheafIso_hom_app`: the identification
  `AlgebraicGeometry.Stack.localStructurePresheafIso` acts on sections over a small étale object
  as restriction along the counit of the localization equivalence.
* `AlgebraicGeometry.Stack.smallEtaleStructureComparison_eq_smallEtaleStructureMapRing`: the map
  `a_{small}^♯` is the structure map of `ε_a`, that is pullback of global functions along the
  base-change projection.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06W2](https://stacks.math.columbia.edu/tag/06W2)
* [Stacks Project, Tag 06W9](https://stacks.math.columbia.edu/tag/06W9)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u v w v₁ v₂ u₁ u₂

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{v}} {S : Cᵒᵖ ⥤ RingCat.{v}}

/-- Two equal maps `φ = ψ` of presheaves of rings have isomorphic pullback functors of presheaves
of modules. -/
public noncomputable def pullbackCongr {φ ψ : S ⟶ F.op ⋙ R} (hφψ : φ = ψ)
    [(pushforward.{v} φ).IsRightAdjoint] [(pushforward.{v} ψ).IsRightAdjoint] :
    pullback.{v} φ ≅ pullback.{v} ψ :=
  Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction.{v} φ)
    ((pullbackPushforwardAdjunction.{v} ψ).ofNatIsoRight
      (eqToIso (congrArg (fun k ↦ pushforward.{v} k) hφψ.symm)))

end PresheafOfModules

namespace AlgebraicGeometry.SmallEtale

/-- The small étale site of a scheme is locally small in the universe of its structure sheaf. -/
public instance locallySmall (E : BigEtaleSite.{u}) (T : Scheme.{u}) (hT : E.Contains T) :
    LocallySmall.{u} (SmallEtale E T hT) :=
  ⟨fun _ _ ↦ inferInstance⟩

/-- The pushforward of presheaves of modules along the structure map of the morphism of ringed
sites `ε_a` of small étale sites has a left adjoint. -/
public instance presheafPushforward_smallEtaleStructureMapRing_isRightAdjoint
    (E : BigEtaleSite.{u}) {X Y : E.Scheme} (a : X ⟶ Y) :
    (PresheafOfModules.pushforward.{u}
      (smallEtaleStructureMapRing E a).hom).IsRightAdjoint :=
  PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall.{u}
    (show (structureSheaf E Y.obj Y.property).obj ⟶
        (smallEtaleBaseChange E a).op ⋙ (structureSheaf E X.obj X.property).obj from
      (smallEtaleStructureMapRing E a).hom)

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- Over a small étale object `W` of the scheme below `x`, the identification of the structure
sheaf of the small étale site with the restriction at `x` of the structure sheaf of `𝒳` is the
restriction map of the structure sheaf of the big fppf site along the counit, at the image of
`W`, of the localization equivalence. -/
public theorem localStructurePresheafIso_hom_app (x : 𝒳)
    (W : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) :
    letI : (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).IsEquivalence :=
      isEquivalence_overPost B S hS p hp x
    (localStructurePresheafIso B E h S hS p hp x τ hτ).hom.app (op W) =
      (baseRingStructureSheaf B (p.obj x).left.1 (p.obj x).left.2 τ hτ).obj.map
        (((Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).asEquivalence.counit.app
          ((smallEtaleInclusion B E h (p.obj x).left.1
            (contains_base B E h S hS p x)).obj W)).op) :=
  rfl

variable {x y : 𝒳} (φ : x ⟶ y)

/-- Below an arrow `φ : x ⟶ y` of `𝒳` lying over a morphism of schemes `a : U ⟶ V`, the map
`a_{small}^♯` of structure sheaves `AlgebraicGeometry.Stack.smallEtaleStructureComparison` is the
structure map of the morphism of ringed sites `ε_a` of small étale sites: pullback of global
functions along the base-change projection `U ×_V W ⟶ W`. -/
public theorem smallEtaleStructureComparison_eq_smallEtaleStructureMapRing :
    smallEtaleStructureComparison B E h S hS p hp φ τ hτ =
      (SmallEtale.smallEtaleStructureMapRing E
        (smallEtaleBaseMorphism B E h S hS p φ)).hom := by
  have := isEquivalence_overPost B S hS p hp x
  have := isEquivalence_overPost B S hS p hp y
  refine NatTrans.ext (funext fun W ↦ ?_)
  induction W with | op W => ?_
  obtain ⟨φ', hfac, hproj⟩ := exists_restrictionComparisonLift B E h S hS p hp φ W
  have hcomp := restrictionPushforwardComparison_app B E h S hS p hp φ
    (ringStructureSheafCore B S hS p hp τ hτ).obj W φ' hfac hproj
  have hy := localStructurePresheafIso_hom_app B E h S hS p hp τ hτ y W
  have hx := localStructurePresheafIso_hom_app B E h S hS p hp τ hτ x
    ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj W)
  have hgoal : (smallEtaleStructureComparison B E h S hS p hp φ τ hτ).app (op W) =
      (localStructurePresheafIso B E h S hS p hp y τ hτ).hom.app (op W) ≫
        ((restrictionPushforwardComparison B E h S hS p hp φ
            (ringStructureSheafCore B S hS p hp τ hτ).obj).app (op W) ≫
          ((localStructurePresheafIso B E h S hS p hp x τ hτ).app
            (op ((smallEtaleBaseChange E
              (smallEtaleBaseMorphism B E h S hS p φ)).obj W))).inv) := rfl
  have hx' : ((localStructurePresheafIso B E h S hS p hp x τ hτ).app
        (op ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj W))).hom =
      (localStructurePresheafIso B E h S hS p hp x τ hτ).hom.app
        (op ((smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).obj W)) := rfl
  have key := congrArg
    (fun k ↦ (forget₂ CommRingCat.{u} RingCat.{u}).map (Scheme.Γ.map k.op)) hproj
  simp only [op_comp, Functor.map_comp] at key
  rw [hgoal, ← Category.assoc, Iso.comp_inv_eq, hx', hy, hcomp, hx]
  exact key

/-- The pushforward of presheaves of modules along the structure map of `ε_a`, with the structure
sheaves written as in `AlgebraicGeometry.Stack.smallEtaleStructureComparison`, has a left
adjoint. -/
public instance presheafPushforward_structureMapRing_isRightAdjoint :
    (PresheafOfModules.pushforward.{u}
      (show (SmallEtale.structureSheaf E (p.obj y).left.1
            (contains_base B E h S hS p y)).obj ⟶
          (smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ)).op ⋙
            (SmallEtale.structureSheaf E (p.obj x).left.1
              (contains_base B E h S hS p x)).obj from
        (SmallEtale.smallEtaleStructureMapRing E
          (smallEtaleBaseMorphism B E h S hS p φ)).hom)).IsRightAdjoint :=
  PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall.{u} _

/-- The pullback of presheaves of modules along `a_{small}^♯` is the pullback along the structure
map of the morphism of ringed sites `ε_a`. -/
public noncomputable def smallEtalePullbackComparisonIso :
    PresheafOfModules.pullback.{u} (smallEtaleStructureComparison B E h S hS p hp φ τ hτ) ≅
      PresheafOfModules.pullback.{u} (SmallEtale.smallEtaleStructureMapRing E
        (smallEtaleBaseMorphism B E h S hS p φ)).hom :=
  PresheafOfModules.pullbackCongr.{u}
    (smallEtaleStructureComparison_eq_smallEtaleStructureMapRing B E h S hS p hp τ hτ φ)

/-- For `φ : x ⟶ y` an arrow of `𝒳` lying over a morphism of schemes `a : U ⟶ V`, the
sheafification of the pullback of presheaves of modules of `𝓕^a` along `a_{small}^♯` is
`(a^*𝓕)^a`, naturally in the `𝒪_V`-module `𝓕`. -/
public noncomputable def associatedModuleSmallEtaleBaseChangeIso :
    SmallEtale.associatedModule E (p.obj y).left.1 (contains_base B E h S hS p y) ⋙
        SheafOfModules.forget (SmallEtale.structureSheaf E (p.obj y).left.1
          (contains_base B E h S hS p y)) ⋙
        PresheafOfModules.pullback.{u} (smallEtaleStructureComparison B E h S hS p hp φ τ hτ) ⋙
        PresheafOfModules.sheafification
          (R₀ := (SmallEtale.structureSheaf E (p.obj x).left.1
            (contains_base B E h S hS p x)).obj) (𝟙 _) ≅
      Scheme.Modules.pullback (B.inclusion.map (p.map φ).left) ⋙
        SmallEtale.associatedModule E (p.obj x).left.1 (contains_base B E h S hS p x) :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _ (Functor.isoWhiskerRight
      (smallEtalePullbackComparisonIso B E h S hS p hp τ hτ φ) _)) ≪≫
    Functor.isoWhiskerLeft _ (SheafOfModules.pullbackIso.{u}
      (SmallEtale.smallEtaleStructureMapRing E (smallEtaleBaseMorphism B E h S hS p φ))).symm ≪≫
    (SmallEtale.associatedModuleBaseChangeIso E
      (smallEtaleBaseMorphism B E h S hS p φ)).symm

/-- The sheafification of the pullback of presheaves of modules of `𝓕^a` along `a_{small}^♯` is
`(a^*𝓕)^a`, at one `𝒪_V`-module `𝓕`. -/
public noncomputable def associatedModuleObjSmallEtaleBaseChangeIso
    (𝓕 : (p.obj y).left.1.Modules) :
    (PresheafOfModules.sheafification
        (R₀ := (SmallEtale.structureSheaf E (p.obj x).left.1
          (contains_base B E h S hS p x)).obj) (𝟙 _)).obj
        ((PresheafOfModules.pullback.{u}
            (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).obj
          ((SmallEtale.associatedModule E (p.obj y).left.1
            (contains_base B E h S hS p y)).obj 𝓕).val) ≅
      (SmallEtale.associatedModule E (p.obj x).left.1 (contains_base B E h S hS p x)).obj
        ((Scheme.Modules.pullback (B.inclusion.map (p.map φ).left)).obj 𝓕) :=
  (associatedModuleSmallEtaleBaseChangeIso B E h S hS p hp τ hτ φ).app 𝓕

end AlgebraicGeometry.Stack

end
