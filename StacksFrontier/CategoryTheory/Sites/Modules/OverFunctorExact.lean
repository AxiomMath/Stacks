module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Limits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes

/-!
# Pushforward of sheaves of modules is additive, and restriction to a slice is exact

Let `F : C ⥤ D` be a continuous functor between sites and let
`φ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R` be a morphism of sheaves of rings.
The pushforward functor
`SheafOfModules.pushforward φ : SheafOfModules.{v} R ⥤ SheafOfModules.{v} S` is additive and
preserves monomorphisms. Restriction `SheafOfModules.overFunctor R x` of a sheaf of `R`-modules
to the slice site over an object `x` is moreover exact.

## Main definitions

* `SheafOfModules.overFunctorMapHomologicalComplex`: restricting a complex to the slice over `y`
  and then to the slice over `x` is restricting it to the slice over `x`.
* `SheafOfModules.overFunctorMapHomotopy`: a homotopy between two maps restricted to the slice
  over `y` restricts to the slice over `x`.

## Main results

* `SheafOfModules.pushforward_additive`: `pushforward φ` is additive, for any continuous `F`.
* `SheafOfModules.pushforward_preservesMonomorphisms`: `pushforward φ` preserves
  monomorphisms, for any continuous `F`.
* `SheafOfModules.overMap_additive` and `SheafOfModules.overMap_preservesMonomorphisms`: the
  same two facts for `SheafOfModules.overMap`, the comparison between two slices.
* `SheafOfModules.overFunctor_preservesHomology`: restriction to a slice preserves homology.
* `SheafOfModules.overFunctor_preservesFiniteLimits` and
  `SheafOfModules.overFunctor_preservesFiniteColimits`: restriction to a slice is left and
  right exact.
* `SheafOfModules.shortExact_map_overFunctor`: a short exact sequence of sheaves of
  `R`-modules stays short exact after restriction to the slice over `x`.

## References

* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public section

universe w v v₁ v₂ u₁ u₂ u

open CategoryTheory CategoryTheory.Limits

namespace SheafOfModules

section Pushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- Pushforward of sheaves of modules is additive. -/
instance pushforward_additive : (pushforward.{v} φ).Additive where
  map_add := (fullyFaithfulForget _).map_injective <| by ext : 1; rfl

/-- Pushforward of sheaves of modules preserves monomorphisms. -/
instance pushforward_preservesMonomorphisms :
    (pushforward.{v} φ).PreservesMonomorphisms where
  preserves f _ := Functor.mono_of_mono_map (forget S) <| PresheafOfModules.mono_of_injective
    fun ⦃_⦄ _ _ hab => PresheafOfModules.injective_of_mono ((forget R).map f) _ hab

end Pushforward

section OverMap

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) {x y : C} (g : x ⟶ y)

/-- Extension from the slice over `y` to the slice over `x` along `g : x ⟶ y` is additive. -/
instance overMap_additive : (overMap.{v} R g).Additive :=
  inferInstanceAs (pushforward.{v} (F := Over.map g)
    (Sheaf.pushforwardOverMapIso R g).inv).Additive

/-- Extension from the slice over `y` to the slice over `x` preserves monomorphisms. -/
instance overMap_preservesMonomorphisms : (overMap.{v} R g).PreservesMonomorphisms :=
  inferInstanceAs (pushforward.{v} (F := Over.map g)
    (Sheaf.pushforwardOverMapIso R g).inv).PreservesMonomorphisms

end OverMap

section Over

variable {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) (x : C)

/-- Restriction to the slice over `x` is a left adjoint. -/
instance overFunctor_isLeftAdjoint : (overFunctor.{v} R x).IsLeftAdjoint :=
  inferInstanceAs (pushforward.{v} (𝟙 (R.over x))).IsLeftAdjoint

/-- Restriction to the slice over `x` preserves monomorphisms. -/
instance overFunctor_preservesMonomorphisms :
    (overFunctor.{v} R x).PreservesMonomorphisms :=
  inferInstanceAs (pushforward.{v} (𝟙 (R.over x))).PreservesMonomorphisms

section Abelian

variable [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasSheafify (J.over x) AddCommGrpCat.{v}]
  [(J.over x).WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Restriction to a slice preserves homology. -/
noncomputable instance overFunctor_preservesHomology :
    (overFunctor.{v} R x).PreservesHomology :=
  Functor.preservesHomology_of_preservesMonos_and_cokernels _

/-- Restriction to a slice is left exact: it preserves finite limits. -/
noncomputable instance overFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (overFunctor.{v} R x) :=
  (overFunctor.{v} R x).preservesFiniteLimits_of_preservesHomology

/-- Restriction to a slice is right exact: it preserves finite colimits. -/
noncomputable instance overFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (overFunctor.{v} R x) :=
  (overFunctor.{v} R x).preservesFiniteColimits_of_preservesHomology

/-- Restriction to a slice is exact: a short exact sequence of sheaves of `R`-modules stays short
exact after restricting to the slice site over `x`. -/
lemma shortExact_map_overFunctor (T : ShortComplex (SheafOfModules.{v} R))
    (hT : T.ShortExact) : (T.map (overFunctor.{v} R x)).ShortExact :=
  hT.map_of_exact (overFunctor.{v} R x)

end Abelian

end Over

section Homotopy

variable {C : Type u₁} [Category.{v₁} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) {x y : C} (g : x ⟶ y) {ι : Type*} (c : ComplexShape ι)

/-- Restricting a homological complex of sheaves of `R`-modules first to the slice over `y` and
then to the slice over `x` along `g : x ⟶ y` is restricting it to the slice over `x`. -/
noncomputable def overFunctorMapHomologicalComplex :
    (overFunctor.{v} R y).mapHomologicalComplex c ⋙
        (overMap.{v} R g).mapHomologicalComplex c ≅
      (overFunctor.{v} R x).mapHomologicalComplex c :=
  Functor.mapHomologicalComplexCompIso (overFunctorMap.{v} R g) c

/-- If the restrictions of `α` and `β` to the slice over `y` are homotopic, so are their
restrictions to the slice over `x`, for any `g : x ⟶ y`. -/
noncomputable def overFunctorMapHomotopy
    {E F : HomologicalComplex (SheafOfModules.{v} R) c} {α β : E ⟶ F}
    (H : Homotopy (((overFunctor.{v} R y).mapHomologicalComplex c).map α)
      (((overFunctor.{v} R y).mapHomologicalComplex c).map β)) :
    Homotopy (((overFunctor.{v} R x).mapHomologicalComplex c).map α)
      (((overFunctor.{v} R x).mapHomologicalComplex c).map β) := by
  have e := overFunctorMapHomologicalComplex.{v} R g c
  refine (Homotopy.ofEq ?_).trans ((((((overMap.{v} R g).mapHomotopy H).compLeft
    (e.inv.app E)).compRight (e.hom.app F))).trans (Homotopy.ofEq ?_))
  · have h := e.hom.naturality α
    dsimp at h
    rw [Category.assoc, h, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  · have h := e.hom.naturality β
    dsimp at h
    rw [Category.assoc, h, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

end Homotopy

end SheafOfModules

end
