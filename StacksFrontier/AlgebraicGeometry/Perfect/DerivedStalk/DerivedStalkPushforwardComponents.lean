module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkSpellingGermBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TrianglesComponents

/-!
# The rungs of the derived stalk of a pushforward, below `DerivedCategory.Q`

`AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing` — the derived stalk at
`i z` of `Ri_* K` for a closed immersion of schemes, over the local ring `𝒪_{X,i z}` — is a
composite of six isomorphisms of functors, each of them built from
`Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryIsoOfNatIso` and
`...mapDerivedCategoryCompIso`, and the library proves nothing about it beyond its definition.
This file computes the component of each of its *rungs* at an object `DerivedCategory.Q.obj P`:
every one of them is `DerivedCategory.Q` of the degreewise isomorphism it descends from,
conjugated by the two `CategoryTheory.Functor.mapDerivedCategoryFactors` of its two sides.

It also computes the degreewise content that the four rungs compose to: the germ map
`AlgebraicGeometry.restrictScalarsStalkPushforwardMap`, in the spelling
`Stacks.ModuleSkyscraper.pushStalkMap` presents it as a morphism of functors.

## Main definitions

* `AlgebraicGeometry.restrictScalarsStalkMapSquareDerivedIso`: the germ square of the two
  spellings of the stalk ring, on derived categories.  It occurs inside
  `derivedStalkDerivedPushforwardIsoOfSchemesLocalRing` as an unnamed three-fold composite; naming
  it is what lets that composite be evaluated.

## Main results

* `Stacks.ClosedImmersion.derivedStalkPushforwardModuleFunctorIso_hom_app_Q` and
  `...derivedStalkDerivedPushforwardIso_hom_app_Q`: **the pushforward rung.**  The derived stalk
  of `i_*` — and of `Ri_*` — on the image, at `DerivedCategory.Q.obj C`.
* `AlgebraicGeometry.derivedStalkSpellingFunctorIsoOfRingSheaf_hom_app_Q` and
  `..._inv_app_Q`: **the spelling rung**, in both directions.
* `AlgebraicGeometry.restrictScalarsStalkMapSquareDerivedIso_hom_app_Q`: **the germ-square rung.**
* `AlgebraicGeometry.derivedStalkPushforwardTail`: **the degreewise content.**  The four
  degreewise isomorphisms the four rungs descend from compose to
  `Stacks.ModuleSkyscraper.pushStalkMap`, applied degreewise.
* `StacksDraft.DerivedStalkComponentChase.twoFoldComponentChase` and
  `...threeFoldComponentChase`: the two cancellations each rung needs, at free objects and
  morphisms of an arbitrary category.

## Implementation notes

*Why the cancellations are run at free objects and morphisms.*  Each rung is a two- or three-fold
`CategoryTheory.Iso.trans`, and its component is the composite of the components with the
factorizations of the intermediate functors cancelling in pairs.  That is three rewrites, and none
of them fires: the goal mixes `AlgebraicGeometry.Scheme.Modules X` with
`CategoryTheory.SheafOfModules (structureSheafRing X.toRingedSpace)`, and the
`RingCat`-valued stalk of the ring sheaf with the local ring, each pair being two definitionally
but not *reducibly* equal spellings of one object.  A goal of that shape is not type-correct at the
transparency at which `rw` and `simp` check their motives, and `simp only [Iso.trans_hom]` reports
that argument unused against a `≪≫` that is plainly there.  So the cancellation is stated for free
objects and morphisms, where every rewrite fires, and applied by `exact`, which pays the
conversion once.  This is the technique of
`StacksDraft.DerivedStalkCompositionChase.stalkCompChase`.

*Why each rung is unfolded by `rfl` at a free object.*  The unfolding of a rung into the
components of its factors — `Iso.trans_hom`, `Iso.symm_hom` and `NatTrans.comp_app`, all of them
`rfl` — is cheap at a *variable* object of the derived category and expensive at
`DerivedCategory.Q.obj C`: restating the whole component with the three factors spelled out and
proving it by `rfl` runs out of heartbeats.  So each rung is unfolded once at a free object, and
the chase then specializes it.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 00AE](https://stacks.math.columbia.edu/tag/00AE)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.PerfectComplexTriangles

noncomputable section

namespace StacksDraft.DerivedStalkComponentChase

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E]

/-- A functor applied to a composite of two morphisms, as a composite. -/
theorem map_comp₂ (F : C ⥤ D) {W X Y : C} (α : W ⟶ X) (β : X ⟶ Y) :
    F.map (α ≫ β) = F.map α ≫ F.map β :=
  CategoryTheory.Functor.map_comp _ _ _

/-- A functor applied to a composite of four morphisms, as a composite — read as the merge of
four localized morphisms into one. -/
theorem map_comp₄ (F : C ⥤ D) {W X Y Z T : C} (α : W ⟶ X) (β : X ⟶ Y) (γ : Y ⟶ Z) (δ : Z ⟶ T) :
    F.map α ≫ F.map β ≫ F.map γ ≫ F.map δ = F.map (α ≫ β ≫ γ ≫ δ) := by
  simp only [Functor.map_comp]

/-- A functor applied to a composite of six morphisms, as a composite. -/
theorem map_comp₆ (F : C ⥤ D) {W X Y Z T U V : C} (α : W ⟶ X) (β : X ⟶ Y) (γ : Y ⟶ Z)
    (δ : Z ⟶ T) (ε : T ⟶ U) (ζ : U ⟶ V) :
    F.map (α ≫ β ≫ γ ≫ δ ≫ ε ≫ ζ) =
      F.map α ≫ F.map β ≫ F.map γ ≫ F.map δ ≫ F.map ε ≫ F.map ζ := by
  simp only [Functor.map_comp]

/-- A composite functor applied to a composite of two morphisms, with both functors applied
separately.  This is the shape in which the naturality of a morphism of functors into a composite
meets a two-step morphism. -/
theorem comp_map_comp₂ (F : C ⥤ D) (G : D ⥤ E) {W X Y : C} (α : W ⟶ X) (β : X ⟶ Y) :
    (F ⋙ G).map (α ≫ β) = G.map (F.map α) ≫ G.map (F.map β) := by
  rw [Functor.comp_map, map_comp₂, map_comp₂]

/-- A functor carries a pair of mutually inverse morphisms to a pair of mutually inverse
morphisms. -/
theorem map_inv_hom (F : C ⥤ D) {a b : C} (α : a ⟶ b) (β : b ⟶ a)
    (h : α ≫ β = CategoryStruct.id a) :
    F.map α ≫ F.map β = CategoryStruct.id (F.obj a) := by
  rw [← map_comp₂, h, F.map_id]

/-- `map_inv_hom` for two functors in a row. -/
theorem map_map_inv_hom (F : D ⥤ E) (G : C ⥤ D) {a b : C} (α : a ⟶ b) (β : b ⟶ a)
    (h : α ≫ β = CategoryStruct.id a) :
    F.map (G.map α) ≫ F.map (G.map β) = CategoryStruct.id (F.obj (G.obj a)) :=
  map_inv_hom F _ _ (map_inv_hom G α β h)

/-- Four morphisms separated by identities, as a four-fold composite.  The identities are the
components of the three `CategoryTheory.Functor.associator` of a six-fold composite of
isomorphisms of functors; they cannot be removed by `rfl`. -/
theorem comp_id_comp₄ {a b c d e : C} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) (k : d ⟶ e) :
    f ≫ CategoryStruct.id b ≫ g ≫ CategoryStruct.id c ≫ h ≫ CategoryStruct.id d ≫ k =
      f ≫ g ≫ h ≫ k := by
  simp

/-- **The cancellation behind the component of a two-fold rung.**  Read `u ≫ v` as the component
of the rung, `c₁` and `c₂` as the two factorizations of the intermediate functor, which are
mutually inverse, and `a ≫ b ≫ p ≫ q` as the answer.

Stated at free objects and morphisms of an arbitrary category because the concrete equation is not
type-correct at the transparency at which `rw` and `simp` check their motives; see the
implementation notes. -/
theorem twoFoldComponentChase {O₀ M M' A B O₂ : C}
    {ψ : O₀ ⟶ O₂} {u : O₀ ⟶ M} {v : M ⟶ O₂}
    {a : O₀ ⟶ A} {b : A ⟶ M'} {c₁ : M' ⟶ M} {c₂ : M ⟶ M'} {p : M' ⟶ B} {q : B ⟶ O₂}
    (h₀ : ψ = u ≫ v) (h₁ : u = a ≫ b ≫ c₁) (h₂ : v = c₂ ≫ p ≫ q)
    (hc : c₁ ≫ c₂ = CategoryStruct.id M') :
    ψ = a ≫ b ≫ p ≫ q := by
  rw [h₀, h₁, h₂]
  simp only [Category.assoc, reassoc_of% hc]

/-- **The cancellation behind the component of a three-fold rung**, with two intermediate functors
cancelling.  Read `m` as `DerivedCategory.Q` of the degreewise isomorphism.

Stated at free objects and morphisms for the reason given in the implementation notes. -/
theorem threeFoldComponentChase {O₀ M N M' N' A B O₃ : C}
    {ψ : O₀ ⟶ O₃} {u : O₀ ⟶ M} {v : M ⟶ N} {w : N ⟶ O₃}
    {a : O₀ ⟶ A} {b : A ⟶ M'} {c₁ : M' ⟶ M} {c₂ : M ⟶ M'}
    {m : M' ⟶ N'} {d₁ : N' ⟶ N} {d₂ : N ⟶ N'} {p : N' ⟶ B} {q : B ⟶ O₃}
    (h₀ : ψ = u ≫ v ≫ w) (h₁ : u = a ≫ b ≫ c₁) (h₂ : v = c₂ ≫ m ≫ d₁)
    (h₃ : w = d₂ ≫ p ≫ q) (hc : c₁ ≫ c₂ = CategoryStruct.id M')
    (hd : d₁ ≫ d₂ = CategoryStruct.id N') :
    ψ = a ≫ b ≫ m ≫ p ≫ q := by
  rw [h₀, h₁, h₂, h₃]
  simp only [Category.assoc, reassoc_of% hc, reassoc_of% hd]

end StacksDraft.DerivedStalkComponentChase

namespace Stacks.ClosedImmersion

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] preservesFiniteLimits_restrictScalars_stalkRingMap
  preservesFiniteColimits_restrictScalars_stalkRingMap

variable {Z X : RingedSpace.{u, u}} (i : Z ⟶ X) (z : Z.carrier)
  [PreservesFiniteColimits (modulePushforward i)]

/-! ### The pushforward rung -/

/-- The component of `derivedStalkPushforwardModuleFunctorIso` at a free object, as the composite
of the components of its three factors.  Unfolding it here rather than at
`DerivedCategory.Q.obj C` is what keeps the conversion cheap. -/
theorem derivedStalkPushforwardModuleFunctorIso_hom_app
    (hi : Topology.IsInducing (ConcreteCategory.hom i.hom.base))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) :
    (derivedStalkPushforwardModuleFunctorIso i z hi).hom.app K =
      (mapDerivedCategoryCompIso (modulePushforward i)
          (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X)
            (i.hom.base z))).inv.app K ≫
        (mapDerivedCategoryIsoOfNatIso _ _ (stalkPushforwardModuleFunctorIso i z hi)).hom.app K ≫
        (mapDerivedCategoryCompIso
          (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Z) z)
          (ModuleCat.restrictScalars.{u, u, u}
            (Stacks.RingedSpace.stalkRingMap i z).hom)).hom.app K :=
  rfl

/-- **The derived stalk of `i_*` on the image, at a complex.**  At `DerivedCategory.Q.obj C` the
computation `derivedStalkPushforwardModuleFunctorIso` is `DerivedCategory.Q` of the degreewise
stalk computation `stalkPushforwardModuleFunctorIso`, conjugated by the factorizations of the
stalk functor at `i z` on the left and of the stalk functor at `z` followed by restriction of
scalars along the germ map on the right.

This is `StacksDraft.DerivedStalkComponentChase.threeFoldComponentChase` at the three components
of `Stacks.Cohomology.PerfectComplexTriangles`. -/
theorem derivedStalkPushforwardModuleFunctorIso_hom_app_Q
    (hi : Topology.IsInducing (ConcreteCategory.hom i.hom.base))
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) :
    (derivedStalkPushforwardModuleFunctorIso i z hi).hom.app (DerivedCategory.Q.obj C) =
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X)
          (i.hom.base z)).mapDerivedCategory.map
          ((modulePushforward i).mapDerivedCategoryFactors.hom.app C) ≫
        (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X)
            (i.hom.base z)).mapDerivedCategoryFactors.hom.app
          (((modulePushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (stalkPushforwardModuleFunctorIso i z hi) (ComplexShape.up ℤ)).hom.app C) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (Stacks.RingedSpace.stalkRingMap i z).hom).mapDerivedCategoryFactors.inv.app
          (((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Z)
            z).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (Stacks.RingedSpace.stalkRingMap i z).hom).mapDerivedCategory.map
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Z)
            z).mapDerivedCategoryFactors.inv.app C) :=
  StacksDraft.DerivedStalkComponentChase.threeFoldComponentChase
    (derivedStalkPushforwardModuleFunctorIso_hom_app i z hi (DerivedCategory.Q.obj C))
    (mapDerivedCategoryCompIso_inv_app (modulePushforward i)
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X) (i.hom.base z)) C)
    (mapDerivedCategoryIsoOfNatIso_hom_app _ _ (stalkPushforwardModuleFunctorIso i z hi) C)
    (mapDerivedCategoryCompIso_hom_app
      (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Z) z)
      (ModuleCat.restrictScalars.{u, u, u} (Stacks.RingedSpace.stalkRingMap i z).hom) C)
    (Iso.inv_hom_id_app _ C) (Iso.inv_hom_id_app _ C)

/-- The component of `derivedStalkDerivedPushforwardIso` at a free object: the comparison
`Ri_* ≅ i_*` under the derived stalk, then the computation for `i_*`. -/
theorem derivedStalkDerivedPushforwardIso_hom_app
    (hi : Topology.IsInducing (ConcreteCategory.hom i.hom.base))
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z))) :
    (derivedStalkDerivedPushforwardIso i z hi).hom.app K =
      (AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing X)
            (i.hom.base z)).map
          ((derivedPushforwardIsoMapDerivedCategory i).hom.app K) ≫
        (derivedStalkPushforwardModuleFunctorIso i z hi).hom.app K :=
  rfl

/-- **The derived stalk of `Ri_*` on the image, at a complex.**  `derivedStalkDerivedPushforwardIso`
is the comparison `Ri_* ≅ i_*` of `derivedPushforwardIsoMapDerivedCategory` followed by
`derivedStalkPushforwardModuleFunctorIso`, so this is
`derivedStalkPushforwardModuleFunctorIso_hom_app_Q` with that comparison prefixed. -/
theorem derivedStalkDerivedPushforwardIso_hom_app_Q
    (hi : Topology.IsInducing (ConcreteCategory.hom i.hom.base))
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) :
    (derivedStalkDerivedPushforwardIso i z hi).hom.app (DerivedCategory.Q.obj C) =
      (AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing X)
            (i.hom.base z)).map
          ((derivedPushforwardIsoMapDerivedCategory i).hom.app (DerivedCategory.Q.obj C)) ≫
        (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X)
            (i.hom.base z)).mapDerivedCategory.map
          ((modulePushforward i).mapDerivedCategoryFactors.hom.app C) ≫
        (AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X)
            (i.hom.base z)).mapDerivedCategoryFactors.hom.app
          (((modulePushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (stalkPushforwardModuleFunctorIso i z hi) (ComplexShape.up ℤ)).hom.app C) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (Stacks.RingedSpace.stalkRingMap i z).hom).mapDerivedCategoryFactors.inv.app
          (((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Z)
            z).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (Stacks.RingedSpace.stalkRingMap i z).hom).mapDerivedCategory.map
          ((AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing Z)
            z).mapDerivedCategoryFactors.inv.app C) :=
  (derivedStalkDerivedPushforwardIso_hom_app i z hi (DerivedCategory.Q.obj C)).trans
    (congrArg (fun t => (AlgebraicGeometry.SheafOfModules.derivedStalkFunctor (structureSheafRing X)
          (i.hom.base z)).map
        ((derivedPushforwardIsoMapDerivedCategory i).hom.app (DerivedCategory.Q.obj C)) ≫ t)
      (derivedStalkPushforwardModuleFunctorIso_hom_app_Q i z hi C))

end Stacks.ClosedImmersion

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] additive_restrictScalarsRingSheafStalk
  preservesFiniteLimits_restrictScalarsRingSheafStalk
  preservesFiniteColimits_restrictScalarsRingSheafStalk
  preservesFiniteLimits_restrictScalars_stalkRingMap'
  preservesFiniteColimits_restrictScalars_stalkRingMap'

/-! ### The spelling rung -/

section Spelling

variable {X : Scheme.{u}} (x : X)

/-- The component of `derivedStalkSpellingFunctorIsoOfRingSheaf` at a free object. -/
theorem derivedStalkSpellingFunctorIsoOfRingSheaf_hom_app (K : DerivedCategory X.Modules) :
    (derivedStalkSpellingFunctorIsoOfRingSheaf x).hom.app K =
      (mapDerivedCategoryIsoOfNatIso _ _ (modulesRingCatStalkFunctorIso x)).inv.app K ≫
        (mapDerivedCategoryCompIso (modulesRingCatStalkFunctor x)
          (ModuleCat.restrictScalars.{u, u, u}
            (ringCatStalkRingEquiv x).symm.toRingHom)).hom.app K :=
  rfl

/-- **The two spellings of the derived stalk, at a complex.**  At `DerivedCategory.Q.obj P` the
comparison `derivedStalkSpellingFunctorIsoOfRingSheaf` is the factorization of the derived stalk
over the local ring, then `DerivedCategory.Q` of the degreewise comparison
`modulesRingCatStalkFunctorIso` read backwards, then the two factorizations of the `RingCat`-stalk
side read backwards. -/
theorem derivedStalkSpellingFunctorIsoOfRingSheaf_hom_app_Q (P : CochainComplex X.Modules ℤ) :
    (derivedStalkSpellingFunctorIsoOfRingSheaf x).hom.app (DerivedCategory.Q.obj P) =
      (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (modulesRingCatStalkFunctorIso x) (ComplexShape.up ℤ)).inv.app P) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (ringCatStalkRingEquiv x).symm.toRingHom).mapDerivedCategoryFactors.inv.app
          (((modulesRingCatStalkFunctor x).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (ringCatStalkRingEquiv x).symm.toRingHom).mapDerivedCategory.map
          ((modulesRingCatStalkFunctor x).mapDerivedCategoryFactors.inv.app P) :=
  StacksDraft.DerivedStalkComponentChase.twoFoldComponentChase
    (derivedStalkSpellingFunctorIsoOfRingSheaf_hom_app x (DerivedCategory.Q.obj P))
    (mapDerivedCategoryIsoOfNatIso_inv_app _ _ (modulesRingCatStalkFunctorIso x) P)
    (mapDerivedCategoryCompIso_hom_app (modulesRingCatStalkFunctor x)
      (ModuleCat.restrictScalars.{u, u, u} (ringCatStalkRingEquiv x).symm.toRingHom) P)
    (Iso.inv_hom_id_app _ P)

/-- The component of `derivedStalkSpellingFunctorIsoOfRingSheaf` read backwards, at a free
object. -/
theorem derivedStalkSpellingFunctorIsoOfRingSheaf_inv_app (K : DerivedCategory X.Modules) :
    (derivedStalkSpellingFunctorIsoOfRingSheaf x).inv.app K =
      (mapDerivedCategoryCompIso (modulesRingCatStalkFunctor x)
          (ModuleCat.restrictScalars.{u, u, u}
            (ringCatStalkRingEquiv x).symm.toRingHom)).inv.app K ≫
        (mapDerivedCategoryIsoOfNatIso _ _ (modulesRingCatStalkFunctorIso x)).hom.app K :=
  rfl

/-- `derivedStalkSpellingFunctorIsoOfRingSheaf_hom_app_Q` read backwards, which is the direction
the derived stalk of a pushforward composes with on its target side. -/
theorem derivedStalkSpellingFunctorIsoOfRingSheaf_inv_app_Q (P : CochainComplex X.Modules ℤ) :
    (derivedStalkSpellingFunctorIsoOfRingSheaf x).inv.app (DerivedCategory.Q.obj P) =
      (ModuleCat.restrictScalars.{u, u, u}
            (ringCatStalkRingEquiv x).symm.toRingHom).mapDerivedCategory.map
          ((modulesRingCatStalkFunctor x).mapDerivedCategoryFactors.hom.app P) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (ringCatStalkRingEquiv x).symm.toRingHom).mapDerivedCategoryFactors.hom.app
          (((modulesRingCatStalkFunctor x).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (modulesRingCatStalkFunctorIso x) (ComplexShape.up ℤ)).hom.app P) ≫
        (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryFactors.inv.app P :=
  StacksDraft.DerivedStalkComponentChase.twoFoldComponentChase
    (derivedStalkSpellingFunctorIsoOfRingSheaf_inv_app x (DerivedCategory.Q.obj P))
    (mapDerivedCategoryCompIso_inv_app (modulesRingCatStalkFunctor x)
      (ModuleCat.restrictScalars.{u, u, u} (ringCatStalkRingEquiv x).symm.toRingHom) P)
    (mapDerivedCategoryIsoOfNatIso_hom_app _ _ (modulesRingCatStalkFunctorIso x) P)
    (Iso.inv_hom_id_app _ P)

end Spelling

/-! ### The germ-square rung -/

section Square

variable {Z X : Scheme.{u}} (i : Z ⟶ X) (z : Z)

/-- **The germ square of the two spellings of the stalk ring, on derived categories.**
`restrictScalarsStalkMapSquareIso` says that restricting scalars along the `RingCat`-valued germ
map and then along `ringCatStalkRingEquiv` at `i z` is restricting scalars along
`ringCatStalkRingEquiv` at `z` and then along the `CommRingCat`-valued germ map.  All four
functors are exact, so the square carries to derived categories.

This is the three-fold composite that occurs unnamed inside
`derivedStalkDerivedPushforwardIsoOfSchemesLocalRing`; naming it is what lets that definition's
component be evaluated. -/
def restrictScalarsStalkMapSquareDerivedIso :
    (ModuleCat.restrictScalars.{u, u, u}
          (Stacks.RingedSpace.stalkRingMap i.toLRSHom.toShHom z).hom).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{u, u, u}
          (ringCatStalkRingEquiv
            (i.toLRSHom.toShHom.hom.base z)).symm.toRingHom).mapDerivedCategory ≅
      (ModuleCat.restrictScalars.{u, u, u}
          (ringCatStalkRingEquiv z).symm.toRingHom).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{u, u, u}
          (i.toLRSHom.toShHom.hom.stalkMap z).hom).mapDerivedCategory :=
  (mapDerivedCategoryCompIso
        (ModuleCat.restrictScalars.{u, u, u}
          (Stacks.RingedSpace.stalkRingMap i.toLRSHom.toShHom z).hom)
        (ModuleCat.restrictScalars.{u, u, u}
          (ringCatStalkRingEquiv (i.toLRSHom.toShHom.hom.base z)).symm.toRingHom)).symm ≪≫
    mapDerivedCategoryIsoOfNatIso _ _ (restrictScalarsStalkMapSquareIso i z) ≪≫
    mapDerivedCategoryCompIso
      (ModuleCat.restrictScalars.{u, u, u} (ringCatStalkRingEquiv z).symm.toRingHom)
      (ModuleCat.restrictScalars.{u, u, u} (i.toLRSHom.toShHom.hom.stalkMap z).hom)

/-- **The germ square on derived categories, at a complex.**  It is `DerivedCategory.Q` of the
degreewise germ square `restrictScalarsStalkMapSquareIso`, conjugated by the factorizations of the
two composites of restriction-of-scalars functors. -/
theorem restrictScalarsStalkMapSquareDerivedIso_hom_app_Q
    (P : CochainComplex (ModuleCat.{u} (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (structureSheafRing Z.toRingedSpace).obj z))) ℤ) :
    (restrictScalarsStalkMapSquareDerivedIso i z).hom.app (DerivedCategory.Q.obj P) =
      (ModuleCat.restrictScalars.{u, u, u}
            (ringCatStalkRingEquiv
              (i.toLRSHom.toShHom.hom.base z)).symm.toRingHom).mapDerivedCategory.map
          ((ModuleCat.restrictScalars.{u, u, u}
            (Stacks.RingedSpace.stalkRingMap
              i.toLRSHom.toShHom z).hom).mapDerivedCategoryFactors.hom.app P) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (ringCatStalkRingEquiv
              (i.toLRSHom.toShHom.hom.base z)).symm.toRingHom).mapDerivedCategoryFactors.hom.app
          (((ModuleCat.restrictScalars.{u, u, u}
            (Stacks.RingedSpace.stalkRingMap i.toLRSHom.toShHom z).hom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex
          (restrictScalarsStalkMapSquareIso i z) (ComplexShape.up ℤ)).hom.app P) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (i.toLRSHom.toShHom.hom.stalkMap z).hom).mapDerivedCategoryFactors.inv.app
          (((ModuleCat.restrictScalars.{u, u, u}
            (ringCatStalkRingEquiv z).symm.toRingHom).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj P) ≫
        (ModuleCat.restrictScalars.{u, u, u}
            (i.toLRSHom.toShHom.hom.stalkMap z).hom).mapDerivedCategory.map
          ((ModuleCat.restrictScalars.{u, u, u}
            (ringCatStalkRingEquiv z).symm.toRingHom).mapDerivedCategoryFactors.inv.app P) :=
  StacksDraft.DerivedStalkComponentChase.threeFoldComponentChase
    (rfl : (restrictScalarsStalkMapSquareDerivedIso i z).hom.app (DerivedCategory.Q.obj P) = _)
    (mapDerivedCategoryCompIso_inv_app
      (ModuleCat.restrictScalars.{u, u, u}
        (Stacks.RingedSpace.stalkRingMap i.toLRSHom.toShHom z).hom)
      (ModuleCat.restrictScalars.{u, u, u}
        (ringCatStalkRingEquiv (i.toLRSHom.toShHom.hom.base z)).symm.toRingHom) P)
    (mapDerivedCategoryIsoOfNatIso_hom_app _ _ (restrictScalarsStalkMapSquareIso i z) P)
    (mapDerivedCategoryCompIso_hom_app
      (ModuleCat.restrictScalars.{u, u, u} (ringCatStalkRingEquiv z).symm.toRingHom)
      (ModuleCat.restrictScalars.{u, u, u} (i.toLRSHom.toShHom.hom.stalkMap z).hom) P)
    (Iso.inv_hom_id_app _ P) (Iso.inv_hom_id_app _ P)

end Square

/-! ### The degreewise content of the four rungs -/

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] (z : Z)

/-- **The degreewise content of the derived stalk of a pushforward.**  In each degree, the
spelling comparison at `i z` read backwards, then restriction of scalars along
`ringCatStalkRingEquiv` of the degreewise stalk computation of
`Stacks.ClosedImmersion.stalkPushforwardModuleFunctorIso`, then the germ square, then restriction
of scalars along the germ map of the spelling comparison at `z`, is
`Stacks.ModuleSkyscraper.pushStalkMap`.

That is `AlgebraicGeometry.restrictScalarsStalkPushforwardMap` spelled out, and
`pushStalkMap_app_eq_restrictScalarsStalkPushforwardMap` identifies the two. -/
theorem derivedStalkPushforwardTail (C : CochainComplex Z.Modules ℤ) :
    (NatIso.mapHomologicalComplex
          (modulesRingCatStalkFunctorIso (i.toLRSHom.toShHom.hom.base z))
          (ComplexShape.up ℤ)).inv.app
        (((Scheme.Modules.pushforward i).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
      ((ModuleCat.restrictScalars.{u, u, u}
          (ringCatStalkRingEquiv
            (i.toLRSHom.toShHom.hom.base z)).symm.toRingHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
        ((NatIso.mapHomologicalComplex
          (Stacks.ClosedImmersion.stalkPushforwardModuleFunctorIso i.toLRSHom.toShHom z
            (Stacks.ClosedImmersion.isClosedEmbedding_base_toShHom i).isInducing)
          (ComplexShape.up ℤ)).hom.app C) ≫
      (NatIso.mapHomologicalComplex (restrictScalarsStalkMapSquareIso i z)
          (ComplexShape.up ℤ)).hom.app
        (((modulesRingCatStalkFunctor z).mapHomologicalComplex (ComplexShape.up ℤ)).obj C) ≫
      ((ModuleCat.restrictScalars.{u, u, u}
          (i.toLRSHom.toShHom.hom.stalkMap z).hom).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
        ((NatIso.mapHomologicalComplex (modulesRingCatStalkFunctorIso z)
          (ComplexShape.up ℤ)).hom.app C) =
    (NatTrans.mapHomologicalComplex (Stacks.ModuleSkyscraper.pushStalkMap i z)
      (ComplexShape.up ℤ)).app C := by
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f,
    NatTrans.mapHomologicalComplex_app_f]
  exact (pushStalkMap_app_eq_restrictScalarsStalkPushforwardMap i z (C.X n)).symm

end AlgebraicGeometry

end

end
