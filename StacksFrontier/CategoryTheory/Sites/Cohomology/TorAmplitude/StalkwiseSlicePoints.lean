module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.StalkwiseFiniteTor
public import StacksFrontier.CategoryTheory.Sites.Point.LocalizedPoint
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeTorDimensionStalkBridge

/-!
# Locally finite Tor dimension from a uniform bound at the points of a site

Let `(C, O)` be a ringed site and let `(Φ_i)` be a family of points of `C` such that, for every
object `V`, the lifts `Φ_i.over x` of the `Φ_i` to the slice over `V` (one for each `x` in the
fibre of `Φ_i` at `V`) form a conservative family of points of the slice. If one interval `[a, b]`
contains the Tor amplitude of the derived stalk `E_{Φ_i}` of an object `E` of `D(O)` at every
`Φ_i`, then `E` locally has finite Tor dimension, in fact has Tor amplitude in `[a, b]` on every
slice. This is Stacks 0DJJ (2) read on the slices, together with Stacks 04H2: the stalk of the
restriction `E|_V` at `Φ.over x` is the stalk of `E` at `Φ`.

## Main definitions

* `AlgebraicGeometry.RingedSite.overRingFiberIso`: the fibre of the structure sheaf of the slice
  over `V` at `Φ.over x` is the fibre of the structure sheaf at `Φ`.
* `AlgebraicGeometry.RingedSite.overModuleStalkIso`: the stalk of `M|_V` at `Φ.over x` is the stalk
  of `M` at `Φ`, read through `overRingFiberIso`.
* `AlgebraicGeometry.RingedSite.overModuleStalkNatIso`: the same, naturally in `M`.

## Main results

* `AlgebraicGeometry.RingedSite.hasTorAmplitudeCanonical_derivedModuleFiber_over_iff`: the derived
  stalk of `E|_V` at `Φ.over x` and the derived stalk of `E` at `Φ` have the same Tor amplitude.
* `Stacks.SheafOfModules.DerivedTensorProduct.locallyHasFiniteTorDimension_of_uniform_pointBound`:
  the statement of the title.

## References

* [Stacks Project, Tag 0DJJ](https://stacks.math.columbia.edu/tag/0DJJ)
* [Stacks Project, Tag 04H2](https://stacks.math.columbia.edu/tag/04H2)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w d

namespace AlgebraicGeometry.RingedSite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Z : RingedSite.{u, v, w}} [LocallySmall.{w} Z.C]
  (Φ : Z.J.Point.{w}) {V : Z.C} (x : Φ.fiber.obj V)

/-- The fibre at `Φ.over x` of the structure sheaf of the slice over `V` is the fibre of the
structure sheaf at `Φ`, by Stacks 04H2. -/
def overRingFiberIso :
    ((Φ.over x).presheafFiber (A := CommRingCat.{w})).obj (Z.over V).O.obj ≅
      (Φ.presheafFiber (A := CommRingCat.{w})).obj Z.O.obj :=
  (GrothendieckTopology.Point.presheafFiberOverIso Φ x CommRingCat.{w}).app Z.O.obj

/-- The comparison of Stacks 04H2 takes a germ at a neighbourhood of `Φ.over x` to the germ at
the underlying neighbourhood of `Φ`. -/
lemma presheafFiberOverIso_hom_toPresheafFiber' {A : Type*} [Category A]
    [HasColimitsOfSize.{w, w} A] (P : Z.Cᵒᵖ ⥤ A) (W : Over V) (y : (Φ.over x).fiber.obj W) :
    (Φ.over x).toPresheafFiber W y ((Over.forget V).op ⋙ P) ≫
        ((GrothendieckTopology.Point.presheafFiberOverIso Φ x A).app P).hom =
      Φ.toPresheafFiber W.left y.val P :=
  Functor.Final.ι_colimitIso_hom (GrothendieckTopology.Point.overElements Φ x).op
    ((Functor.Elements.π Φ.fiber).op ⋙ P) (op ((Φ.over x).fiber.elementsMk W y))

/-- The fibre comparison of the structure sheaf takes ring germs to ring germs. -/
lemma overRingFiberIso_ringStalkGerm (W : Over V) (y : (Φ.over x).fiber.obj W)
    (a : (Stacks.commRingSheafToRingSheaf (Z.over V).O).obj.obj (op W)) :
    (overRingFiberIso Φ x).hom (Stacks.ringStalkGerm (Φ.over x) (Z.over V).O W y a) =
      Stacks.ringStalkGerm Φ Z.O W.left y.val a :=
  ConcreteCategory.congr_hom
    (presheafFiberOverIso_hom_toPresheafFiber' Φ x Z.O.obj W y) a

/-! ### Underlying abelian groups -/

section Generic

variable {C : Type*} [Category C] [LocallySmall.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The stalk of a sheaf of modules, forgotten to abelian groups, is the fibre of the underlying
presheaf of abelian groups. -/
def moduleStalkForget₂Iso (Ψ : J.Point.{w}) (O : Sheaf J CommRingCat.{w})
    (M : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) :
    (forget₂ _ AddCommGrpCat.{w}).obj (Stacks.moduleStalk Ψ O M) ≅
      (Ψ.presheafFiber (A := AddCommGrpCat.{w})).obj M.val.presheaf :=
  Iso.refl _

/-- The stalk of a sheaf of modules with its scalars restricted along a ring map, forgotten to
abelian groups, is the fibre of the underlying presheaf of abelian groups. -/
def moduleStalkRestrictScalarsForget₂Iso (Ψ : J.Point.{w}) (O : Sheaf J CommRingCat.{w})
    {R : Type w} [Ring R] (ρ : R →+* (Ψ.presheafFiber (A := CommRingCat.{w})).obj O.obj)
    (M : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) :
    (forget₂ _ AddCommGrpCat.{w}).obj
        ((ModuleCat.restrictScalars ρ).obj (Stacks.moduleStalk Ψ O M)) ≅
      (Ψ.presheafFiber (A := AddCommGrpCat.{w})).obj M.val.presheaf :=
  Iso.refl _

/-- The comparison `moduleStalkForget₂Iso` takes the germ of a section in the module stalk to its
germ in the fibre of the underlying presheaf of abelian groups. -/
lemma moduleStalkForget₂Iso_hom_germ (Ψ : J.Point.{w}) (O : Sheaf J CommRingCat.{w})
    (M : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) (U : C) (ξ : Ψ.fiber.obj U)
    (t : M.val.obj (op U)) :
    (moduleStalkForget₂Iso Ψ O M).hom (Stacks.moduleStalkGerm Ψ O M U ξ t) =
      Ψ.toPresheafFiber U ξ M.val.presheaf t :=
  rfl

/-- The inverse of `moduleStalkRestrictScalarsForget₂Iso` takes the germ of a section in the fibre
of the underlying presheaf of abelian groups to its germ in the module stalk. -/
lemma moduleStalkRestrictScalarsForget₂Iso_inv_toPresheafFiber (Ψ : J.Point.{w})
    (O : Sheaf J CommRingCat.{w}) {R : Type w} [Ring R]
    (ρ : R →+* (Ψ.presheafFiber (A := CommRingCat.{w})).obj O.obj)
    (M : SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf O)) (U : C) (ξ : Ψ.fiber.obj U)
    (t : M.val.obj (op U)) :
    (moduleStalkRestrictScalarsForget₂Iso Ψ O ρ M).inv (Ψ.toPresheafFiber U ξ M.val.presheaf t) =
      Stacks.moduleStalkGerm Ψ O M U ξ t :=
  rfl

end Generic

/-- The underlying presheaf of abelian groups of the restriction `M|_V` is the restriction of the
underlying presheaf of `M`. -/
def overPresheafIso (M : RingedSite.Modules.{u, v, w} Z) :
    ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).obj
        M).val.presheaf ≅ (Over.forget V).op ⋙ M.val.presheaf :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- **The stalk of a restriction to a slice, on underlying abelian groups.** -/
def overFiberAddIso (M : RingedSite.Modules.{u, v, w} Z) :
    ((Φ.over x).presheafFiber (A := AddCommGrpCat.{w})).obj
        ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).obj
          M).val.presheaf ≅
      (Φ.presheafFiber (A := AddCommGrpCat.{w})).obj M.val.presheaf :=
  (Φ.over x).presheafFiber.mapIso (overPresheafIso M) ≪≫
    (GrothendieckTopology.Point.presheafFiberOverIso Φ x AddCommGrpCat.{w}).app M.val.presheaf

/-- The comparison `overFiberAddIso` takes the germ of a section of `M|_V` at a neighbourhood of
`Φ.over x` to the germ of the same section of `M` at the underlying neighbourhood of `Φ`. -/
lemma overFiberAddIso_hom_toPresheafFiber (M : RingedSite.Modules.{u, v, w} Z) (W : Over V)
    (y : (Φ.over x).fiber.obj W) (t : M.val.obj (op W.left)) :
    (overFiberAddIso Φ x M).hom ((Φ.over x).toPresheafFiber W y
        ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).obj
          M).val.presheaf t) =
      Φ.toPresheafFiber W.left y.val M.val.presheaf t := by
  have h₁ := ConcreteCategory.congr_hom
    ((Φ.over x).toPresheafFiber_naturality (overPresheafIso M).hom W y) t
  have h₂ := ConcreteCategory.congr_hom
    (presheafFiberOverIso_hom_toPresheafFiber' Φ x M.val.presheaf W y) t
  exact (congrArg (ConcreteCategory.hom
    ((GrothendieckTopology.Point.presheafFiberOverIso Φ x AddCommGrpCat.{w}).hom.app
      M.val.presheaf)) h₁).trans h₂

/-- The comparison of stalks along a restriction to a slice, on underlying abelian groups. -/
def overStalkAddIso (M : RingedSite.Modules.{u, v, w} Z) :
    (forget₂ _ AddCommGrpCat.{w}).obj (Stacks.moduleStalk (Φ.over x) (Z.over V).O
        ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).obj M)) ≅
      (forget₂ _ AddCommGrpCat.{w}).obj ((ModuleCat.restrictScalars
        (overRingFiberIso Φ x).hom.hom).obj (Stacks.moduleStalk Φ Z.O M)) :=
  moduleStalkForget₂Iso (Φ.over x) (Z.over V).O _ ≪≫ overFiberAddIso Φ x M ≪≫
    (moduleStalkRestrictScalarsForget₂Iso Φ Z.O _ M).symm

/-- The comparison of stalks along a restriction to a slice takes germs to germs. -/
lemma overStalkAddIso_hom_germ (M : RingedSite.Modules.{u, v, w} Z) (W : Over V)
    (y : (Φ.over x).fiber.obj W) (t : M.val.obj (op W.left)) :
    (overStalkAddIso Φ x M).hom (Stacks.moduleStalkGerm (Φ.over x) (Z.over V).O
        ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).obj M)
        W y t) =
      Stacks.moduleStalkGerm Φ Z.O M W.left y.val t :=
  overFiberAddIso_hom_toPresheafFiber Φ x M W y t

/-- The comparison `overStalkAddIso` is semilinear along `overRingFiberIso`: it takes `r • n` to
the image of `r` acting on the image of `n`. -/
lemma overStalkAddIso_hom_smul (M : RingedSite.Modules.{u, v, w} Z)
    (r : ((Φ.over x).presheafFiber (A := CommRingCat.{w})).obj (Z.over V).O.obj)
    (n : Stacks.moduleStalk (Φ.over x) (Z.over V).O
      ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).obj M)) :
    (overStalkAddIso Φ x M).hom (r • n) =
      (overRingFiberIso Φ x).hom r •
        @id (Stacks.moduleStalk Φ Z.O M) ((overStalkAddIso Φ x M).hom n) := by
  obtain ⟨W₁, y₁, s, rfl⟩ := Stacks.moduleStalkGerm_jointly_surjective (Φ.over x)
    (Z.over V).O
    ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).obj M) n
  obtain ⟨W₂, y₂, a, rfl⟩ := Stacks.ringStalkGerm_jointly_surjective (Φ.over x)
    (Z.over V).O r
  obtain ⟨W, y, g₁, g₂, h₁, h₂⟩ := Stacks.exists_common_nbhd (Φ := Φ.over x) y₁ y₂
  have hs := Stacks.moduleStalkGerm_restrict (Φ.over x) (Z.over V).O
    ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).obj M)
    g₁ y s
  have ha := Stacks.ringStalkGerm_restrict (Φ.over x) (Z.over V).O g₂ y a
  rw [h₁] at hs
  rw [h₂] at ha
  rw [← hs, ← ha]
  refine (congrArg (overStalkAddIso Φ x M).hom
    (Stacks.moduleStalkGerm_smul (Φ.over x) (Z.over V).O _ W y _ _).symm).trans ?_
  refine (overStalkAddIso_hom_germ Φ x M W y _).trans ?_
  refine (Stacks.moduleStalkGerm_smul Φ Z.O M W.left y.val _ _).trans ?_
  rw [overRingFiberIso_ringStalkGerm]
  exact congrArg (fun m => Stacks.ringStalkGerm Φ Z.O W.left y.val _ • m)
    (overStalkAddIso_hom_germ Φ x M W y _).symm

variable [HasSheafify Z.J AddCommGrpCat.{w}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The stalk functor at `Φ`, with its source spelled as the modules of the ringed site. -/
def stalkFunctor :
    RingedSite.Modules.{u, v, w} Z ⥤
      ModuleCat.{w} ((Φ.presheafFiber (A := CommRingCat.{w})).obj Z.O.obj) :=
  Stacks.sheafModuleFiberOfCommRing Φ Z.O

/-- The stalk functor at `Φ` is additive. -/
instance stalkFunctor_additive : (stalkFunctor Φ).Additive :=
  Stacks.instAdditiveSheafModuleFiberOfCommRing Φ Z.O

/-- The stalk functor at `Φ` preserves finite limits. -/
instance stalkFunctor_preservesFiniteLimits : PreservesFiniteLimits (stalkFunctor Φ) :=
  Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing Φ Z.O

/-- The stalk functor at `Φ` preserves finite colimits. -/
instance stalkFunctor_preservesFiniteColimits : PreservesFiniteColimits (stalkFunctor Φ) :=
  Stacks.instPreservesFiniteColimitsSheafModuleFiberOfCommRing Φ Z.O

variable [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{w}]
  [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] sliceHasSheafify sliceWEqualsLocallyBijective
  sliceRestrictionPreservesFiniteLimits sliceRestrictionPreservesFiniteColimits
  Stacks.SheafOfModules.DerivedTensorProduct.sliceLocallySmall

/-- The stalk functor at `Φ.over x` is additive, at the spelling of the slice as `Over V`. -/
local instance overFiber_additive :
    (Stacks.sheafModuleFiberOfCommRing (Φ.over x) (Z.over V).O).Additive :=
  Stacks.instAdditiveSheafModuleFiberOfCommRing (Φ.over x) (Z.over V).O

/-- The stalk functor at `Φ.over x` is left exact, at the spelling of the slice as `Over V`. -/
local instance overFiber_preservesFiniteLimits :
    PreservesFiniteLimits (Stacks.sheafModuleFiberOfCommRing (Φ.over x) (Z.over V).O) :=
  Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing (Φ.over x) (Z.over V).O

/-- The stalk functor at `Φ.over x` is right exact, at the spelling of the slice as `Over V`. -/
local instance overFiber_preservesFiniteColimits :
    PreservesFiniteColimits (Stacks.sheafModuleFiberOfCommRing (Φ.over x) (Z.over V).O) :=
  Stacks.instPreservesFiniteColimitsSheafModuleFiberOfCommRing (Φ.over x) (Z.over V).O

/-- The stalk functor at `Φ.over x` is additive, at the spelling of the slice as `(Z.over V).C`. -/
local instance overFiber_additive' :
    (Stacks.sheafModuleFiberOfCommRing (C := (Z.over V).C) (J := (Z.over V).J) (Φ.over x)
      (Z.over V).O).Additive :=
  Stacks.instAdditiveSheafModuleFiberOfCommRing (Φ.over x) (Z.over V).O

/-- The stalk functor at `Φ.over x` is left exact, at the spelling of the slice as `(Z.over V).C`.
-/
local instance overFiber_preservesFiniteLimits' :
    PreservesFiniteLimits (Stacks.sheafModuleFiberOfCommRing (C := (Z.over V).C)
      (J := (Z.over V).J) (Φ.over x) (Z.over V).O) :=
  Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing (Φ.over x) (Z.over V).O

/-- The stalk functor at `Φ.over x` is right exact, at the spelling of the slice as `(Z.over V).C`.
-/
local instance overFiber_preservesFiniteColimits' :
    PreservesFiniteColimits (Stacks.sheafModuleFiberOfCommRing (C := (Z.over V).C)
      (J := (Z.over V).J) (Φ.over x) (Z.over V).O) :=
  Stacks.instPreservesFiniteColimitsSheafModuleFiberOfCommRing (Φ.over x) (Z.over V).O


/-- **The stalk of a restriction to a slice, Stacks 04H2 for modules.** The stalk at `Φ.over x`
of the restriction `M|_V` of a sheaf of `O`-modules is the stalk of `M` at `Φ`, read over the
fibre of the structure sheaf of the slice through `overRingFiberIso`. -/
def overModuleStalkIso (M : RingedSite.Modules.{u, v, w} Z) :
    Stacks.moduleStalk (Φ.over x) (Z.over V).O
        ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).obj M) ≅
      (ModuleCat.restrictScalars (overRingFiberIso Φ x).hom.hom).obj
        (Stacks.moduleStalk Φ Z.O M) :=
  ModuleCat.isoMk (overStalkAddIso Φ x M) (fun r => by
    ext n
    exact (overStalkAddIso_hom_smul Φ x M r n).symm)

omit [HasSheafify Z.J AddCommGrpCat.{w}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{w}]
  [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- The comparison `overModuleStalkIso` takes the germ of a section of `M|_V` at a neighbourhood of
`Φ.over x` to the germ of the same section of `M` at the underlying neighbourhood of `Φ`. -/
lemma overModuleStalkIso_hom_germ (M : RingedSite.Modules.{u, v, w} Z) (W : Over V)
    (y : (Φ.over x).fiber.obj W) (t : M.val.obj (op W.left)) :
    (overModuleStalkIso Φ x M).hom (Stacks.moduleStalkGerm (Φ.over x) (Z.over V).O
        ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).obj M)
        W y t) =
      Stacks.moduleStalkGerm Φ Z.O M W.left y.val t :=
  overStalkAddIso_hom_germ Φ x M W y t

/-- **Stacks 04H2 for modules, naturally in the module.** -/
def overModuleStalkNatIso :
    SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V ⋙
        Stacks.sheafModuleFiberOfCommRing (Φ.over x) (Z.over V).O ≅
      Stacks.sheafModuleFiberOfCommRing Φ Z.O ⋙
        ModuleCat.restrictScalars (overRingFiberIso Φ x).hom.hom :=
  NatIso.ofComponents (overModuleStalkIso Φ x) (fun {M M'} g => by
    ext n
    obtain ⟨W, y, t, rfl⟩ := Stacks.moduleStalkGerm_jointly_surjective (Φ.over x)
      (Z.over V).O
      ((SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V).obj M) n
    change (overModuleStalkIso Φ x M').hom ((Stacks.sheafModuleFiberOfCommRing (Φ.over x)
        (Z.over V).O).map ((SheafOfModules.overFunctor _ V).map g)
          (Stacks.moduleStalkGerm (Φ.over x) (Z.over V).O _ W y t)) =
      (Stacks.sheafModuleFiberOfCommRing Φ Z.O).map g
        ((overModuleStalkIso Φ x M).hom (Stacks.moduleStalkGerm (Φ.over x) (Z.over V).O _ W y t))
    refine (congrArg (overModuleStalkIso Φ x M').hom.hom
      (Stacks.moduleStalkGerm_naturality (Φ.over x) (Z.over V).O
        ((SheafOfModules.overFunctor _ V).map g) W y t)).trans ?_
    refine (overModuleStalkIso_hom_germ Φ x M' W y (g.val.app (op W.left) t)).trans ?_
    refine (Stacks.moduleStalkGerm_naturality Φ Z.O g W.left y.val t).symm.trans ?_
    exact congrArg ((Stacks.sheafModuleFiberOfCommRing Φ Z.O).map g).hom
      (overModuleStalkIso_hom_germ Φ x M W y t).symm)

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits

variable [hd : HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} Z)]
  [hSliceDerived : ∀ U : Z.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{max u v, v, w} (Z.over U))]

attribute [local instance] sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived

/-- The stalk functor at `Φ.over x`, with its source spelled as the target of the restriction
functor to the slice over `V`. -/
def overStalkFunctor :
    SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over V) ⥤
      ModuleCat.{w} (((Φ.over x).presheafFiber (A := CommRingCat.{w})).obj (Z.over V).O.obj) :=
  Stacks.sheafModuleFiberOfCommRing (Φ.over x) (Z.over V).O

/-- The stalk functor at `Φ.over x` is additive. -/
instance overStalkFunctor_additive : (overStalkFunctor Φ x).Additive :=
  Stacks.instAdditiveSheafModuleFiberOfCommRing (Φ.over x) (Z.over V).O

/-- The stalk functor at `Φ.over x` preserves finite limits. -/
instance overStalkFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (overStalkFunctor Φ x) :=
  Stacks.preservesFiniteLimits_sheafModuleFiberOfCommRing (Φ.over x) (Z.over V).O

/-- The stalk functor at `Φ.over x` preserves finite colimits. -/
instance overStalkFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (overStalkFunctor Φ x) :=
  Stacks.instPreservesFiniteColimitsSheafModuleFiberOfCommRing (Φ.over x) (Z.over V).O

/-- `overModuleStalkNatIso`, read through `overStalkFunctor` and `stalkFunctor`. -/
def overModuleStalkNatIso' :
    SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V ⋙
        overStalkFunctor Φ x ≅
      stalkFunctor Φ ⋙ ModuleCat.restrictScalars (overRingFiberIso Φ x).hom.hom :=
  overModuleStalkNatIso Φ x

/-- **The derived stalk of a restriction to a slice.** The derived stalk at `Φ.over x` of the
restriction `E|_V` is the derived stalk of `E` at `Φ`, read through `overRingFiberIso`. -/
def derivedModuleFiberOverIso (E : RingedSite.DerivedModules.{u, v, w, d} Z) :
    letI : HasDerivedCategory.{d}
        (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, u, w} Z.O)) := hd
    letI : HasDerivedCategory.{d}
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over V)) :=
      hSliceDerived V
    (overStalkFunctor Φ x).mapDerivedCategory.obj
        ((RingedSite.derivedRestriction.{u, v, w, d} Z V).obj E) ≅
      (ModuleCat.restrictScalars (overRingFiberIso Φ x).hom.hom).mapDerivedCategory.obj
        ((stalkFunctor Φ).mapDerivedCategory.obj E) :=
  letI : HasDerivedCategory.{d}
      (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, u, w} Z.O)) := hd
  letI : HasDerivedCategory.{d}
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Z.O).over V)) :=
    hSliceDerived V
  ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
      (SheafOfModules.overFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O) V)
      (overStalkFunctor Φ x)).app E).symm ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (overModuleStalkNatIso' Φ x)).app E ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso (stalkFunctor Φ)
      (ModuleCat.restrictScalars (overRingFiberIso Φ x).hom.hom)).app E

/-- The derived stalk of `E|_V` at `Φ.over x` and the derived stalk of `E` at `Φ` have the same
Tor amplitude. -/
theorem hasTorAmplitudeCanonical_derivedModuleFiber_over_iff
    (E : RingedSite.DerivedModules.{u, v, w, d} Z) (a b : ℤ) :
    letI : HasDerivedCategory.{d}
        (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, max u v, w} (Z.over V).O)) :=
      hSliceDerived V
    letI : HasDerivedCategory.{d}
        (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, u, w} Z.O)) := hd
    StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        (((Φ.over x).presheafFiber (A := CommRingCat.{w})).obj (Z.over V).O.obj)
        ((Stacks.derivedModuleFiber (C := (Z.over V).C) (J := (Z.over V).J) (Φ.over x)
          (Z.over V).O).obj ((RingedSite.derivedRestriction.{u, v, w, d} Z V).obj E)) a b ↔
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        ((Φ.presheafFiber (A := CommRingCat.{w})).obj Z.O.obj)
        ((Stacks.derivedModuleFiber Φ Z.O).obj E) a b := by
  let : HasDerivedCategory.{d}
      (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, max u v, w} (Z.over V).O)) :=
    hSliceDerived V
  let : HasDerivedCategory.{d}
      (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, u, w} Z.O)) := hd
  let e : (Stacks.derivedModuleFiber (C := (Z.over V).C) (J := (Z.over V).J) (Φ.over x)
        (Z.over V).O).obj ((RingedSite.derivedRestriction.{u, v, w, d} Z V).obj E) ≅
      (ModuleCat.restrictScalars (overRingFiberIso Φ x).hom.hom).mapDerivedCategory.obj
        ((Stacks.derivedModuleFiber Φ Z.O).obj E) :=
    Iso.refl _ ≪≫ derivedModuleFiberOverIso Φ x E ≪≫ Iso.refl _
  refine Iff.trans
    ⟨fun h => AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso e a b h,
      fun h => AlgebraicGeometry.BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
        e.symm a b h⟩ ?_
  exact AlgebraicGeometry.Scheme.Hom.hasTorAmplitudeCanonical_restrictScalars_ringEquiv_obj_iff
    (overRingFiberIso Φ x).commRingCatIsoToRingEquiv _ a b

end AlgebraicGeometry.RingedSite


namespace Stacks.SheafOfModules.DerivedTensorProduct

open _root_.AlgebraicGeometry

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {Z : RingedSite.{u, v, w}} [LocallySmall.{w} Z.C]
  [HasSheafify Z.J AddCommGrpCat.{w}]
  [Z.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ U : Z.C, HasSheafify (Z.J.over U) AddCommGrpCat.{w}]
  [∀ U : Z.C, (Z.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits sliceLocallySmall

variable [hd : HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} Z)]
  [hSliceDerived : ∀ U : Z.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{max u v, v, w} (Z.over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived

variable
  [∀ U : Z.C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w} (Z.over U).O).Additive]
  [∀ (U : Z.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u v, v, w, w, w} (Z.over U).O).obj M).Additive]
  [∀ (U : Z.C) (K L : CochainComplex (RingedSite.Modules.{max u v, v, w} (Z.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (Z.over U).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

/-- **Locally finite Tor dimension from a uniform bound at a family of points.** Let `(Φ_i)` be a
family of points of the site whose lifts `Φ_i.over x` to every slice form a conservative family
of points of that slice. If one interval `[a, b]` contains the Tor amplitude of the derived stalk
of `E` at every `Φ_i`, then `E` has Tor amplitude in `[a, b]` on every slice, and in particular
locally has finite Tor dimension.

On each slice this is Stacks 0DJJ (2), tested on the lifts of the `Φ_i`; the derived stalk of the
restriction at `Φ_i.over x` is the derived stalk of `E` at `Φ_i`, by Stacks 04H2. -/
theorem locallyHasFiniteTorDimension_of_uniform_pointBound
    (T : ∀ U : Z.C, DerivedTensorProduct.{max u v, v, w, d} (Z.over U))
    (E : RingedSite.DerivedModules.{u, v, w, d} Z)
    {ι : Type*} (p : ι → Z.J.Point.{w})
    (hcons : ∀ V : Z.C, (ObjectProperty.ofObj (fun ψ : Σ i, (p i).fiber.obj V =>
      ((p ψ.1).over ψ.2 : (Z.over V).J.Point.{w}))).IsConservativeFamilyOfPoints)
    (a b : ℤ)
    (h : ∀ i : ι,
      letI : HasDerivedCategory.{d}
          (SheafOfModules.{w} (Stacks.commRingSheafToRingSheaf.{v, u, w} Z.O)) := hd
      StacksDraft.TorAmplitude.HasTorAmplitudeCanonical
        (((p i).presheafFiber (A := CommRingCat.{w})).obj Z.O.obj)
        ((Stacks.derivedModuleFiber (p i) Z.O).obj E) a b) :
    LocallyHasFiniteTorDimension T E :=
  locallyHasFiniteTorDimension_of_stalkwise_family T E
    (t := fun V => Σ i, (p i).fiber.obj V)
    (fun V ψ => ((p ψ.1).over ψ.2 : (Z.over V).J.Point.{w})) hcons
    (fun _ => ⟨⊤, by simp, fun V _ _ => ⟨a, b, fun ψ =>
      (RingedSite.hasTorAmplitudeCanonical_derivedModuleFiber_over_iff (p ψ.1) ψ.2 E a b).2
        (h ψ.1)⟩⟩)

end Stacks.SheafOfModules.DerivedTensorProduct

end
