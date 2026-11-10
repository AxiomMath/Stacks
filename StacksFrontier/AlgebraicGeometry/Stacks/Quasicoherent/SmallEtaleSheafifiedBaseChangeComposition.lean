module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleAssociatedModuleBaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SmallEtaleRestrictionComposition
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateOfNatIsoLeft

/-!
# The sheafified base change of Stacks 06WC is compatible with composition

`AlgebraicGeometry.Stack.associatedModuleSmallEtaleBaseChangeIso` is the identification of the
sheafified Stacks 06WC pullback of `𝓕^a` with `(a^*𝓕)^a`, for an arrow `φ : x ⟶ y` of a category
fibred in groupoids lying over a morphism of schemes `a`.  This file proves that those
identifications compose, which is factor 4 of the cocycle condition that
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LiftedFppfFamilySheafCondition.lean` carries
as `AlgebraicGeometry.Stack.LiftedSectionsCocycle`.

## What composes with what

The functor the identification pulls back along is
`AlgebraicGeometry.Stack.sheafifiedPullbackComparison`, the composite
`forget ⋙ pullback along a_{small}^♯ ⋙ sheafification`.  Two of those compose, and the
composition law needs an identification of that composite with the one for `ψ ∘ φ`.  There is no
construction producing such an identification directly: the composite is a left adjoint, so it
has no formula, and the comparison can only be assembled out of comparisons that uniqueness of a
left adjoint provides.  `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonCompIso` is that
assembly — through `AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso`, the composition law
for the pullbacks along the morphisms of ringed sites of **Stacks 070R (2)**, which
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SmallEtaleBaseChangeConjugate.lean` pins by
its conjugate.

With that identification in hand the composition law is the existing pentagon
`AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso_comp` with one naturality square
pasted onto it: the identification of this file differs from the one of that pentagon by
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonIso`, which appears on both sides of the
law, on one side at the associated module of the pullback and on the other at the pullback of
the associated module, and the exchange law for whiskerings moves it from one to the other.

## Main definitions

* `AlgebraicGeometry.Stack.sheafifiedPullbackComparison`: the functor of sheaves of modules the
  identification pulls back along — `forget`, the Stacks 06WC pullback of presheaves of modules,
  and sheafification.
* `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonIso`: it is the pullback of sheaves of
  modules along the morphism of ringed sites `ε_a` of **Stacks 070R (2)**.
* `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonAdjunction`: the resulting adjunction with
  the pushforward along `ε_a`.
* `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonCompIso`: **two sheafified Stacks 06WC
  pullbacks compose.**

## Main results

* `AlgebraicGeometry.Stack.conjugateEquiv_sheafifiedPullbackComparisonIso_hom`: the unit
  characterisation of `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonIso` — its conjugate
  is the identity of the pushforward along `ε_a`, the two functors being left adjoints of that
  one functor.
* `AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso_comp`: **the
  identifications of the sheafified Stacks 06WC pullback of `𝓕^a` with `(a^*𝓕)^a` compose**, at
  one module — the composition law for factor 4 of the identification of sections of
  `AlgebraicGeometry.Stack.liftedSectionsIso`.
* `AlgebraicGeometry.Stack.associatedModuleSmallEtaleBaseChangeIso_eq` and
  `AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso_hom`: the identification
  of Stacks 06WC read off as `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonIso` followed
  by the identification of **Stacks 03LC (1)**, as an isomorphism of functors and at one module.
* `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso_factoredComp_inv` and
  `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso_factoredComp_inv_obj`: the
  pentagon of `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso_comp` at one module
  and read through the inverse identifications, at a morphism of schemes which is only provably
  the composite of the two given ones — the form the composition law for the sheafified pullback
  consumes.

## Implementation notes

The morphism of schemes below `ψ ∘ φ` is only *provably* the composite of the morphisms below
`ψ` and below `φ` — `AlgebraicGeometry.Stack.smallEtaleBaseMorphism_comp` — while the
pentagon is stated at a literal composite `a ≫ b`.  Rather than generalise that pentagon and
everything it is built from, the three declarations of
the existing composition file
that the statement mentions are restated here at a morphism `ab` together with a proof
`a ≫ b = ab`, each by substituting that proof: the generalisation is free in that direction and
costs one line apiece, whereas carrying it through the construction of
`AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` would touch every intermediate
comparison.

Every step of the composition law is taken on terms whose spelling has been fixed in advance —
by a `show` that names the two sides, by the exchange law applied at the level of functors
rather than at a module, and by a private restatement of the pentagon at the morphisms of
schemes below the two arrows.  This is not stylistic: the identifications involved are indexed
by objects of the big étale category of schemes, which are only *definitionally* the schemes
below the objects of `𝒳`, and a tactic left to reconcile the two spellings itself runs the
elaborator past its heartbeat ceiling.

No new Stacks tag is registered.  Stacks 03LC (1) and Stacks 075D (1) are tagged where they are
proved; this file composes constructions of the library.

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Opposite

universe u v w v₁

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z) (ab : X ⟶ Z) (hab : a ≫ b = ab)

/-- `AlgebraicGeometry.Scheme.Modules.pullbackComp` at a morphism which is only provably the
composite of the two given ones. -/
public noncomputable def pullbackFactoredComp :
    pullback b ⋙ pullback a ≅ pullback ab := by
  subst hab; exact pullbackComp a b

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) {X Y Z : B.Scheme} (a : X ⟶ Y) (b : Y ⟶ Z) (ab : X ⟶ Z)
  (hab : a ≫ b = ab)

/-- `AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` at a morphism which is only provably
the composite of the two given ones. -/
public noncomputable def smallEtalePullbackFactoredCompIso :
    SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B b) ⋙
        SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a) ≅
      SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B ab) := by
  subst hab; exact smallEtalePullbackCompIso B a b

/-- The underlying morphisms of schemes inherit the factorisation of a composite. -/
public theorem schemeHom_factored (hab' : a ≫ b = ab) :
    schemeHom B a ≫ schemeHom B b = schemeHom B ab := by
  rw [← hab']; rfl

/-- `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso_comp` at a morphism which is only
provably the composite of the two given ones. -/
public theorem associatedModuleBaseChangeIso_factoredComp :
    isoWhiskerLeft (Scheme.Modules.pullback (schemeHom B b))
          (associatedModuleBaseChangeIso B a) ≪≫
        isoWhiskerRight (associatedModuleBaseChangeIso B b)
          (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)) ≪≫
        isoWhiskerLeft (associatedModule B Z.obj Z.property)
          (smallEtalePullbackFactoredCompIso B a b ab hab) =
      isoWhiskerRight (Scheme.Modules.pullbackFactoredComp (schemeHom B a) (schemeHom B b)
            (schemeHom B ab) (schemeHom_factored B a b ab hab))
          (associatedModule B X.obj X.property) ≪≫
        associatedModuleBaseChangeIso B ab := by
  subst hab; exact associatedModuleBaseChangeIso_comp B a b

/-- **The pentagon of `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso_comp` at one
module, read through the inverse identifications.**  This is the form in which the composition
law for the sheafified pullback of Stacks 06WC consumes it: the identification `ε_a^*(𝓕^a) ≅
(r^*𝓕)^a` below `a`, preceded by `ε_a^*` of the one below `b`, is the composition law for the
pullbacks along `ε` followed by the identification below the composite. -/
public theorem associatedModuleObjBaseChangeIso_factoredComp_inv (𝓖 : Z.obj.Modules) :
    (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).map
          ((associatedModuleBaseChangeIso B b).inv.app 𝓖) ≫
        (associatedModuleBaseChangeIso B a).inv.app
          ((Scheme.Modules.pullback (schemeHom B b)).obj 𝓖) =
      (smallEtalePullbackFactoredCompIso B a b ab hab).hom.app
          ((associatedModule B Z.obj Z.property).obj 𝓖) ≫
        (associatedModuleBaseChangeIso B ab).inv.app 𝓖 ≫
        (associatedModule B X.obj X.property).map
          ((Scheme.Modules.pullbackFactoredComp (schemeHom B a) (schemeHom B b)
            (schemeHom B ab) (schemeHom_factored B a b ab hab)).inv.app 𝓖) := by
  have key := NatTrans.congr_app (congrArg Iso.inv
    (associatedModuleBaseChangeIso_factoredComp B a b ab hab)) 𝓖
  simp only [Iso.trans_inv, isoWhiskerLeft_inv, isoWhiskerRight_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc] at key
  rw [← key, ← Category.assoc, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]


/-- `AlgebraicGeometry.SmallEtale.associatedModuleObjBaseChangeIso_factoredComp_inv` with every
identification read at the module, rather than as a component of the isomorphism of functors.
This is the spelling in which the composition law for the sheafified pullback of Stacks 06WC
consumes it: the source and target of each map are the images of the module under the functors
applied one at a time, which is how a naturality square of the comparison of the two pullback
functors presents them. -/
public theorem associatedModuleObjBaseChangeIso_factoredComp_inv_obj (𝓖 : Z.obj.Modules) :
    (SheafOfModules.pullback.{u} (smallEtaleStructureMapRing B a)).map
          (associatedModuleObjBaseChangeIso B b 𝓖).inv ≫
        (associatedModuleObjBaseChangeIso B a
          ((Scheme.Modules.pullback (schemeHom B b)).obj 𝓖)).inv =
      (smallEtalePullbackFactoredCompIso B a b ab hab).hom.app
          ((associatedModule B Z.obj Z.property).obj 𝓖) ≫
        (associatedModuleObjBaseChangeIso B ab 𝓖).inv ≫
        (associatedModule B X.obj X.property).map
          ((Scheme.Modules.pullbackFactoredComp (schemeHom B a) (schemeHom B b)
            (schemeHom B ab) (schemeHom_factored B a b ab hab)).inv.app 𝓖) :=
  associatedModuleObjBaseChangeIso_factoredComp_inv B a b ab hab 𝓖

end AlgebraicGeometry.SmallEtale

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{v₁} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  {x y z : 𝒳} (φ : x ⟶ y) (ψ : y ⟶ z)

/-- **The functor the identification of Stacks 06WC pulls back along**: the underlying presheaf
of modules of a sheaf on the small étale site of the scheme below `y`, pulled back along the map
`a_{small}^♯` of **Stacks 06WC**, and sheafified.

This is the left-hand side of `AlgebraicGeometry.Stack.associatedModuleSmallEtaleBaseChangeIso`,
named so that the composition law can speak about it. -/
public noncomputable def sheafifiedPullbackComparison :
    SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj y).left.1
        (contains_base B E h S hS p y)) ⥤
      SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x)) :=
  SheafOfModules.forget _ ⋙
    PresheafOfModules.pullback.{u} (smallEtaleStructureComparison B E h S hS p hp φ τ hτ) ⋙
      PresheafOfModules.sheafification
        (R₀ := (SmallEtale.structureSheaf E (p.obj x).left.1
          (contains_base B E h S hS p x)).obj) (𝟙 _)

/-- The comparison of `AlgebraicGeometry.Stack.sheafifiedPullbackComparison` with the left
adjoint `AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` is stated for: the construction
of `SheafOfModules.pullback` along `ε_a` out of the pullback of presheaves of modules and
sheafification, read at the map `a_{small}^♯` of Stacks 06WC rather than at the structure map of
`ε_a` itself. -/
public noncomputable def pullbackConstructionComparisonIso :
    SheafOfModules.forget (SmallEtale.structureSheaf E (p.obj y).left.1
          (contains_base B E h S hS p y)) ⋙
        PresheafOfModules.pullback.{u} (SmallEtale.smallEtaleStructureMapRing E
          (smallEtaleBaseMorphism B E h S hS p φ)).hom ⋙
        PresheafOfModules.sheafification
          (R₀ := (SmallEtale.structureSheaf E (p.obj x).left.1
            (contains_base B E h S hS p x)).obj) (𝟙 _) ≅
      sheafifiedPullbackComparison B E h S hS p hp τ hτ φ :=
  isoWhiskerLeft _ (isoWhiskerRight
    (smallEtalePullbackComparisonIso B E h S hS p hp τ hτ φ).symm _)

/-- **`AlgebraicGeometry.Stack.sheafifiedPullbackComparison` is the pullback of sheaves of
modules along the morphism of ringed sites `ε_a` of Stacks 070R (2).**  The map `a_{small}^♯` of
Stacks 06WC is the structure map of `ε_a`, and the pullback of sheaves of modules is the
sheafification of the pullback of presheaves of modules. -/
public noncomputable def sheafifiedPullbackComparisonIso :
    sheafifiedPullbackComparison B E h S hS p hp τ hτ φ ≅
      SheafOfModules.pullback.{u} (SmallEtale.smallEtaleStructureMapRing E
        (smallEtaleBaseMorphism B E h S hS p φ)) :=
  (pullbackConstructionComparisonIso B E h S hS p hp τ hτ φ).symm ≪≫
    (SheafOfModules.pullbackIso.{u} (SmallEtale.smallEtaleStructureMapRing E
      (smallEtaleBaseMorphism B E h S hS p φ))).symm

/-- **The adjunction `AlgebraicGeometry.Stack.sheafifiedPullbackComparison` is the left half
of**: it is a left adjoint of the pushforward along `ε_a`, by transporting the adjunction that
builds the pullback of sheaves of modules out of presheaves along
`AlgebraicGeometry.Stack.pullbackConstructionComparisonIso`.

The transport is what makes the conjugate calculus available for this functor: no construction
produces an adjunction for it on the nose, its middle factor being a pullback along the map of
Stacks 06WC rather than along the structure map of `ε_a`. -/
public noncomputable def sheafifiedPullbackComparisonAdjunction :
    sheafifiedPullbackComparison B E h S hS p hp τ hτ φ ⊣
      SheafOfModules.pushforward.{u} (SmallEtale.smallEtaleStructureMapRing E
        (smallEtaleBaseMorphism B E h S hS p φ)) :=
  (SheafOfModules.PullbackConstruction.adjunction.{u}
    (SmallEtale.smallEtaleStructureMapRing E
      (smallEtaleBaseMorphism B E h S hS p φ))).ofNatIsoLeft
      (pullbackConstructionComparisonIso B E h S hS p hp τ hτ φ)

/-- **The unit characterisation of
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonIso`.**  Its conjugate, with respect to the
adjunction of the pullback of sheaves of modules along `ε_a` and the transported adjunction of
`AlgebraicGeometry.Stack.sheafifiedPullbackComparison`, is the identity of the pushforward along
`ε_a`: the two functors are left adjoints of that one functor, and the comparison is the one
uniqueness of a left adjoint produces.

This pins the comparison, `CategoryTheory.conjugateEquiv` being a bijection, and it is what
makes the comparison disappear from a conjugate computation. -/
public theorem conjugateEquiv_sheafifiedPullbackComparisonIso_hom :
    conjugateEquiv
        (SheafOfModules.pullbackPushforwardAdjunction.{u}
          (SmallEtale.smallEtaleStructureMapRing E (smallEtaleBaseMorphism B E h S hS p φ)))
        (sheafifiedPullbackComparisonAdjunction B E h S hS p hp τ hτ φ)
        (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ φ).hom = 𝟙 _ := by
  have hcomp := conjugateEquiv_comp
    (adj₁ := SheafOfModules.PullbackConstruction.adjunction.{u}
      (SmallEtale.smallEtaleStructureMapRing E (smallEtaleBaseMorphism B E h S hS p φ)))
    (adj₂ := SheafOfModules.pullbackPushforwardAdjunction.{u}
      (SmallEtale.smallEtaleStructureMapRing E (smallEtaleBaseMorphism B E h S hS p φ)))
    (adj₃ := SheafOfModules.PullbackConstruction.adjunction.{u}
      (SmallEtale.smallEtaleStructureMapRing E (smallEtaleBaseMorphism B E h S hS p φ)))
    (α := (SheafOfModules.pullbackIso.{u} (SmallEtale.smallEtaleStructureMapRing E
      (smallEtaleBaseMorphism B E h S hS p φ))).hom)
    (β := (SheafOfModules.pullbackIso.{u} (SmallEtale.smallEtaleStructureMapRing E
      (smallEtaleBaseMorphism B E h S hS p φ))).inv)
  rw [SheafOfModules.conjugateEquiv_pullbackIso_hom, Category.id_comp, Iso.inv_hom_id,
    conjugateEquiv_id] at hcomp
  rw [show sheafifiedPullbackComparisonAdjunction B E h S hS p hp τ hτ φ =
      (SheafOfModules.PullbackConstruction.adjunction.{u}
        (SmallEtale.smallEtaleStructureMapRing E
          (smallEtaleBaseMorphism B E h S hS p φ))).ofNatIsoLeft
        (pullbackConstructionComparisonIso B E h S hS p hp τ hτ φ) from rfl,
    Stacks.CategoryTheory.conjugateEquiv_ofNatIsoLeft_right]
  refine Eq.trans (congrArg _ ?_) hcomp
  change (pullbackConstructionComparisonIso B E h S hS p hp τ hτ φ).hom ≫
      ((pullbackConstructionComparisonIso B E h S hS p hp τ hτ φ).symm ≪≫
        (SheafOfModules.pullbackIso.{u} (SmallEtale.smallEtaleStructureMapRing E
          (smallEtaleBaseMorphism B E h S hS p φ))).symm).hom =
    (SheafOfModules.pullbackIso.{u} (SmallEtale.smallEtaleStructureMapRing E
      (smallEtaleBaseMorphism B E h S hS p φ))).inv
  simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- **`AlgebraicGeometry.Stack.associatedModuleSmallEtaleBaseChangeIso`, read off as the
identification of Stacks 03LC (1) preceded by
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonIso`.**  This holds by `rfl`: it is the
definition of that identification, with its first two factors packaged as the single comparison
of the sheafified Stacks 06WC pullback with the pullback of sheaves of modules along `ε_a`. -/
public theorem associatedModuleSmallEtaleBaseChangeIso_eq :
    associatedModuleSmallEtaleBaseChangeIso B E h S hS p hp τ hτ φ =
      isoWhiskerLeft (SmallEtale.associatedModule E (p.obj y).left.1
            (contains_base B E h S hS p y))
          (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ φ) ≪≫
        (SmallEtale.associatedModuleBaseChangeIso E
          (smallEtaleBaseMorphism B E h S hS p φ)).symm :=
  rfl

/-- **Two sheafified Stacks 06WC pullbacks compose.**  For arrows `φ : x ⟶ y` and `ψ : y ⟶ z` of
`𝒳` lying over `a : U ⟶ V` and `b : V ⟶ W`, the sheafified pullback along `b_{small}^♯` followed
by the sheafified pullback along `a_{small}^♯` is the sheafified pullback along
`(b ∘ a)_{small}^♯`.

Both sides are left adjoints, so there is no formula for the comparison: it is assembled out of
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonIso`, which identifies each sheafified
Stacks 06WC pullback with the pullback of sheaves of modules along the morphism of ringed sites
`ε` of **Stacks 070R (2)**, and the composition law
`AlgebraicGeometry.SmallEtale.smallEtalePullbackCompIso` for those pullbacks. -/
public noncomputable def sheafifiedPullbackComparisonCompIso :
    sheafifiedPullbackComparison B E h S hS p hp τ hτ ψ ⋙
        sheafifiedPullbackComparison B E h S hS p hp τ hτ φ ≅
      sheafifiedPullbackComparison B E h S hS p hp τ hτ (φ ≫ ψ) :=
  isoWhiskerRight (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ ψ)
      (sheafifiedPullbackComparison B E h S hS p hp τ hτ φ) ≪≫
    isoWhiskerLeft (SheafOfModules.pullback.{u} (SmallEtale.smallEtaleStructureMapRing E
        (smallEtaleBaseMorphism B E h S hS p ψ)))
      (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ φ) ≪≫
    SmallEtale.smallEtalePullbackFactoredCompIso E
        (smallEtaleBaseMorphism B E h S hS p φ) (smallEtaleBaseMorphism B E h S hS p ψ)
        (smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ))
        (smallEtaleBaseMorphism_comp B E h S hS p φ ψ).symm ≪≫
    (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ (φ ≫ ψ)).symm

/-- The component of `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonCompIso` at a sheaf of
modules, read off from its definition. -/
public theorem sheafifiedPullbackComparisonCompIso_hom_app
    (M : SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj z).left.1
      (contains_base B E h S hS p z))) :
    (sheafifiedPullbackComparisonCompIso B E h S hS p hp τ hτ φ ψ).hom.app M =
      (sheafifiedPullbackComparison B E h S hS p hp τ hτ φ).map
          ((sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ ψ).hom.app M) ≫
        (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ φ).hom.app
            ((SheafOfModules.pullback.{u} (SmallEtale.smallEtaleStructureMapRing E
              (smallEtaleBaseMorphism B E h S hS p ψ))).obj M) ≫
        (SmallEtale.smallEtalePullbackFactoredCompIso E
              (smallEtaleBaseMorphism B E h S hS p φ) (smallEtaleBaseMorphism B E h S hS p ψ)
              (smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ))
              (smallEtaleBaseMorphism_comp B E h S hS p φ ψ).symm).hom.app M ≫
        (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ (φ ≫ ψ)).inv.app M :=
  rfl

/-- The identification of `AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso` at
one module, read off as the identification of Stacks 03LC (1) preceded by
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonIso`. -/
public theorem associatedModuleObjSmallEtaleBaseChangeIso_hom
    (𝓗 : (p.obj y).left.1.Modules) :
    (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp τ hτ φ 𝓗).hom =
      (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ φ).hom.app
          ((SmallEtale.associatedModule E (p.obj y).left.1
            (contains_base B E h S hS p y)).obj 𝓗) ≫
        (SmallEtale.associatedModuleBaseChangeIso E
          (smallEtaleBaseMorphism B E h S hS p φ)).inv.app 𝓗 :=
  rfl

/-- **The identifications of the sheafified Stacks 06WC pullback of `𝓕^a` with `(a^*𝓕)^a`
compose, at one module.**  For arrows `φ : x ⟶ y` and `ψ : y ⟶ z` of `𝒳` lying over `a : U ⟶ V`
and `b : V ⟶ W`, and a module `𝓖` on `W`, the identification below `ψ` pulled back along `φ`,
followed by the identification below `φ`, is
`AlgebraicGeometry.Stack.sheafifiedPullbackComparisonCompIso` followed by the identification
below `ψ ∘ φ` and by the composition law for the pullbacks of modules on the schemes.

This is **the composition law for factor 4** of the identification of sections of
`AlgebraicGeometry.Stack.liftedSectionsIso`, which the assembly of the step of **Stacks 076T**
carries as the hypothesis `AlgebraicGeometry.Stack.LiftedSectionsCocycle`.

It is the pentagon `AlgebraicGeometry.SmallEtale.associatedModuleBaseChangeIso_comp` with the
comparison `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonIso` pasted onto it: that
comparison enters the identification on both sides of the law, on one side at the associated
module of the pullback and on the other at the pullback of the associated module, and the
exchange law for whiskerings moves it from one to the other.  No hypothesis on the arrows or on
the module is used: in particular the comparison map `c_φ` of Stacks 06WC is not assumed
invertible, here or anywhere this file reaches. -/
public theorem associatedModuleObjSmallEtaleBaseChangeIso_comp
    (𝓖 : (p.obj z).left.1.Modules) :
    (sheafifiedPullbackComparison B E h S hS p hp τ hτ φ).map
          (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp τ hτ ψ 𝓖).hom ≫
        (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp τ hτ φ
          ((Scheme.Modules.pullback (SmallEtale.schemeHom E
            (smallEtaleBaseMorphism B E h S hS p ψ))).obj 𝓖)).hom =
      (sheafifiedPullbackComparisonCompIso B E h S hS p hp τ hτ φ ψ).hom.app
          ((SmallEtale.associatedModule E (p.obj z).left.1
            (contains_base B E h S hS p z)).obj 𝓖) ≫
        (associatedModuleObjSmallEtaleBaseChangeIso B E h S hS p hp τ hτ (φ ≫ ψ) 𝓖).hom ≫
        (SmallEtale.associatedModule E (p.obj x).left.1 (contains_base B E h S hS p x)).map
          ((Scheme.Modules.pullbackFactoredComp
            (SmallEtale.schemeHom E (smallEtaleBaseMorphism B E h S hS p φ))
            (SmallEtale.schemeHom E (smallEtaleBaseMorphism B E h S hS p ψ))
            (SmallEtale.schemeHom E (smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ)))
            (SmallEtale.schemeHom_factored E _ _ _
              (smallEtaleBaseMorphism_comp B E h S hS p φ ψ).symm)).inv.app 𝓖) := by
  have nat := NatTrans.congr_app (whiskerLeft_comp_whiskerRight
    (SmallEtale.associatedModuleBaseChangeIso E
      (smallEtaleBaseMorphism B E h S hS p ψ)).inv
    (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ φ).hom) 𝓖
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj] at nat
  have nat' : (sheafifiedPullbackComparison B E h S hS p hp τ hτ φ).map
          ((SmallEtale.associatedModuleBaseChangeIso E
            (smallEtaleBaseMorphism B E h S hS p ψ)).inv.app 𝓖) ≫
        (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ φ).hom.app
            ((SmallEtale.associatedModule E (p.obj y).left.1
                (contains_base B E h S hS p y)).obj
              ((Scheme.Modules.pullback (SmallEtale.schemeHom E
                (smallEtaleBaseMorphism B E h S hS p ψ))).obj 𝓖)) ≫
        (SmallEtale.associatedModuleBaseChangeIso E
            (smallEtaleBaseMorphism B E h S hS p φ)).inv.app
          ((Scheme.Modules.pullback (SmallEtale.schemeHom E
            (smallEtaleBaseMorphism B E h S hS p ψ))).obj 𝓖) =
      (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ φ).hom.app
            ((SheafOfModules.pullback.{u} (SmallEtale.smallEtaleStructureMapRing E
                (smallEtaleBaseMorphism B E h S hS p ψ))).obj
              ((SmallEtale.associatedModule E (p.obj z).left.1
                (contains_base B E h S hS p z)).obj 𝓖)) ≫
          (SheafOfModules.pullback.{u} (SmallEtale.smallEtaleStructureMapRing E
              (smallEtaleBaseMorphism B E h S hS p φ))).map
            ((SmallEtale.associatedModuleBaseChangeIso E
              (smallEtaleBaseMorphism B E h S hS p ψ)).inv.app 𝓖) ≫
          (SmallEtale.associatedModuleBaseChangeIso E
              (smallEtaleBaseMorphism B E h S hS p φ)).inv.app
            ((Scheme.Modules.pullback (SmallEtale.schemeHom E
              (smallEtaleBaseMorphism B E h S hS p ψ))).obj 𝓖) := by
    rw [← Category.assoc, ← Category.assoc, ← nat]
  change (sheafifiedPullbackComparison B E h S hS p hp τ hτ φ).map
          ((sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ ψ).hom.app
              ((SmallEtale.associatedModule E (p.obj z).left.1
                (contains_base B E h S hS p z)).obj 𝓖) ≫
            (SmallEtale.associatedModuleBaseChangeIso E
              (smallEtaleBaseMorphism B E h S hS p ψ)).inv.app 𝓖) ≫
        ((sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ φ).hom.app
            ((SmallEtale.associatedModule E (p.obj y).left.1
                (contains_base B E h S hS p y)).obj
              ((Scheme.Modules.pullback (SmallEtale.schemeHom E
                (smallEtaleBaseMorphism B E h S hS p ψ))).obj 𝓖)) ≫
          (SmallEtale.associatedModuleBaseChangeIso E
              (smallEtaleBaseMorphism B E h S hS p φ)).inv.app
            ((Scheme.Modules.pullback (SmallEtale.schemeHom E
              (smallEtaleBaseMorphism B E h S hS p ψ))).obj 𝓖)) =
      ((sheafifiedPullbackComparison B E h S hS p hp τ hτ φ).map
            ((sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ ψ).hom.app
              ((SmallEtale.associatedModule E (p.obj z).left.1
                (contains_base B E h S hS p z)).obj 𝓖)) ≫
          (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ φ).hom.app
              ((SheafOfModules.pullback.{u} (SmallEtale.smallEtaleStructureMapRing E
                (smallEtaleBaseMorphism B E h S hS p ψ))).obj
                ((SmallEtale.associatedModule E (p.obj z).left.1
                  (contains_base B E h S hS p z)).obj 𝓖)) ≫
            (SmallEtale.smallEtalePullbackFactoredCompIso E
                  (smallEtaleBaseMorphism B E h S hS p φ)
                  (smallEtaleBaseMorphism B E h S hS p ψ)
                  (smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ))
                  (smallEtaleBaseMorphism_comp B E h S hS p φ ψ).symm).hom.app
              ((SmallEtale.associatedModule E (p.obj z).left.1
                (contains_base B E h S hS p z)).obj 𝓖) ≫
            (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ (φ ≫ ψ)).inv.app
              ((SmallEtale.associatedModule E (p.obj z).left.1
                (contains_base B E h S hS p z)).obj 𝓖)) ≫
        ((sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ (φ ≫ ψ)).hom.app
              ((SmallEtale.associatedModule E (p.obj z).left.1
                (contains_base B E h S hS p z)).obj 𝓖) ≫
            (SmallEtale.associatedModuleBaseChangeIso E
              (smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ))).inv.app 𝓖) ≫
          (SmallEtale.associatedModule E (p.obj x).left.1
              (contains_base B E h S hS p x)).map
            ((Scheme.Modules.pullbackFactoredComp
              (SmallEtale.schemeHom E (smallEtaleBaseMorphism B E h S hS p φ))
              (SmallEtale.schemeHom E (smallEtaleBaseMorphism B E h S hS p ψ))
              (SmallEtale.schemeHom E (smallEtaleBaseMorphism B E h S hS p (φ ≫ ψ)))
              (SmallEtale.schemeHom_factored E _ _ _
                (smallEtaleBaseMorphism_comp B E h S hS p φ ψ).symm)).inv.app 𝓖)
  rw [Functor.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [nat', SmallEtale.associatedModuleObjBaseChangeIso_factoredComp_inv E _ _ _
    (smallEtaleBaseMorphism_comp B E h S hS p φ ψ).symm]

end AlgebraicGeometry.Stack

end
