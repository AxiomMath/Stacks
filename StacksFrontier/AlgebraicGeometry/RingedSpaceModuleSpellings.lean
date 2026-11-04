module

public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# The spellings of the category of modules on a ringed space

A sheaf of modules on a ringed space `(X, 𝒪_X)` is a `SheafOfModules` over a `RingCat`-valued
sheaf of rings obtained from `𝒪_X` by postcomposition with `forget₂ CommRingCat RingCat`. Four
names for that sheaf of rings are in use, differing only in the *declared type* of the result:
`ringCatSheaf X` and `AlgebraicGeometry.Scheme.ringCatSheaf X` are typed `TopCat.Sheaf RingCat X`,
whereas `structureSheafRing X` and `Stacks.SheafOfModules.Tensor.ringSheaf
X.sheaf` are typed `CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat`. This file
records that all four, and the four categories of modules over them, are *equal by `rfl`*, and
supplies at the `TopCat.Sheaf`-typed spellings the instances that are otherwise only available
at the other one.

## Main results

* `Stacks.RingedSpaceModules.ringCatSheaf_eq_ringSheaf` and
  `Stacks.RingedSpaceModules.schemeRingCatSheaf_eq_ringSheaf`: the sheaves of rings agree.
* `Stacks.RingedSpaceModules.modules_eq`, `Stacks.RingedSpaceModules.ringedSiteModules_eq` and
  `Stacks.RingedSpaceModules.schemeModules_eq`: the four categories of modules agree, and
  `Stacks.RingedSpaceModules.category_modules_eq`,
  `Stacks.RingedSpaceModules.category_schemeModules_eq`: so do their category structures.
* `Stacks.RingedSpaceModules.pushforward_eq`, `Stacks.RingedSpaceModules.pullback_eq` and
  `Stacks.RingedSpaceModules.relativePushforward_eq`: the direct and inverse image functors
  agree across the spellings.
* `Stacks.RingedSpaceModules.schemeModulesEquivalence`: the identity equivalence between
  `AlgebraicGeometry.Scheme.Modules` and the sheaves of modules over `Scheme.ringCatSheaf`,
  which is the identity on objects and on morphisms.

## Implementation notes

Every identification here is `rfl`, so no transport is ever needed: all four spellings denote
one and the same term. What does not cross between them is *typeclass synthesis*. An instance
whose subject is `SheafOfModules R` for a variable `R : Sheaf J RingCat` cannot be applied to
`SheafOfModules (ringCatSheaf X)`, because recognising `TopCat.Sheaf RingCat X` as a
`Sheaf J RingCat` means unfolding the semireducible definition `TopCat.Sheaf`, which instance
search does not do; this is why `structureSheafRing`, whose declared type is
already `Sheaf (Opens.grothendieckTopology X.carrier) RingCat`, exists alongside
`ringCatSheaf`. The instances in the `Instances` section below close that gap by restating the
abelian, Grothendieck-abelian and enough-injectives structures with the `TopCat.Sheaf`-typed
sheaf of rings as their subject.

For the same reason `rw` and `simp` do not act across the equalities below even though they are
`rfl`: their two sides have types that are definitionally but not syntactically equal, and the
motive check of `rw` runs at a transparency at which `TopCat.Sheaf` stays folded. Consumers
should use them in term mode, through `Eq.trans` and `congrArg`.

## References

* [Stacks Project, Tag 01AC](https://stacks.math.columbia.edu/tag/01AC)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.RingedSpaceModules

/-! ### The sheaves of rings -/

/-- The `TopCat.Sheaf`-typed and the `Sheaf`-typed sheaves of rings of a ringed space are the
same sheaf of rings. -/
theorem ringCatSheaf_eq_ringSheaf (X : RingedSpace.{u, u}) :
    ringCatSheaf X = structureSheafRing X :=
  rfl

/-- The sheaf of rings of a scheme is the sheaf of rings of its underlying ringed space. -/
theorem schemeRingCatSheaf_eq_ringSheaf (S : Scheme.{u}) :
    S.ringCatSheaf = structureSheafRing S.toRingedSpace :=
  rfl

/-! ### The categories of modules -/

/-- The category of modules on a ringed space, spelled through `ringCatSheaf`, is the one
spelled through `structureSheafRing`. -/
theorem modules_eq (X : RingedSpace.{u, u}) :
    Modules X = SheafOfModules.{u} (structureSheafRing X) :=
  rfl

/-- The category of modules on a ringed site, applied to the structure sheaf of a ringed space,
is the category of modules on that ringed space. -/
theorem ringedSiteModules_eq (X : RingedSpace.{u, u}) :
    Stacks.DerivedTensor.RingedSite.Modules X.sheaf =
      SheafOfModules.{u} (structureSheafRing X) :=
  rfl

/-- The category of modules on a scheme is the category of modules on its underlying ringed
space. -/
theorem schemeModules_eq (S : Scheme.{u}) :
    S.Modules = SheafOfModules.{u} (structureSheafRing S.toRingedSpace) :=
  rfl

/-- The two spellings of modules on a ringed space carry the same category structure, not
merely the same objects. -/
theorem category_modules_eq (X : RingedSpace.{u, u}) :
    (inferInstance : Category.{u} (Modules X)) =
      (inferInstance : Category.{u}
        (SheafOfModules.{u} (structureSheafRing X))) :=
  rfl

/-- The category structure `AlgebraicGeometry.Scheme.Modules` carries, which is defined through
its own hom type, is the category structure of sheaves of modules. -/
theorem category_schemeModules_eq (S : Scheme.{u}) :
    (inferInstance : Category.{u} S.Modules) =
      (inferInstance : Category.{u} (SheafOfModules.{u} S.ringCatSheaf)) :=
  rfl

/-! ### The functors -/

/-- The structure map of a morphism of ringed spaces, as a morphism of `RingCat`-valued sheaves,
has one value in the two spellings. -/
theorem structureSheafHom_eq {X Y : RingedSpace.{u, u}} (g : X ⟶ Y) :
    toRingCatSheafHom g = RingedSpaceModuleAdjunction.structureSheafHom g :=
  rfl

/-- Direct image of sheaves of modules along a morphism of ringed spaces has one value in the
two spellings. -/
theorem pushforward_eq {X Y : RingedSpace.{u, u}} (g : X ⟶ Y) :
    pushforward g = RingedSpaceModuleAdjunction.modulePushforward g :=
  rfl

/-- Inverse image of sheaves of modules along a morphism of ringed spaces has one value in the
two spellings. -/
theorem pullback_eq {X Y : RingedSpace.{u, u}} (g : X ⟶ Y) :
    pullback g = RingedSpaceModuleAdjunction.modulePullback g :=
  rfl

/-- The direct image of `f^{-1}𝒪_S`-modules along `f` is the direct image of modules along the
morphism of ringed spaces `(X, f^{-1}𝒪_S) ⟶ (S, 𝒪_S)` in the other spelling. -/
theorem relativePushforward_eq {X S : Scheme.{u}} (f : X ⟶ S) :
    Stacks.DeRhamDirectImage.relativePushforward f =
      RingedSpaceModuleAdjunction.modulePushforward
        (Stacks.DeRhamDirectImage.inverseImageBaseProjection f) :=
  rfl

/-! ### The identity equivalence across `AlgebraicGeometry.Scheme.Modules` -/

/-- Modules on a scheme, read as sheaves of modules over its sheaf of rings. It is the identity
on objects and on morphisms. -/
def schemeModulesFunctor (S : Scheme.{u}) : S.Modules ⥤ SheafOfModules.{u} S.ringCatSheaf where
  obj M := M
  map φ := φ

/-- Sheaves of modules over the sheaf of rings of a scheme, read as modules on the scheme. It is
the identity on objects and on morphisms. -/
def schemeModulesInverse (S : Scheme.{u}) : SheafOfModules.{u} S.ringCatSheaf ⥤ S.Modules where
  obj M := M
  map φ := φ

/-- `schemeModulesFunctor S` sends a module on `S` to itself. -/
@[simp]
theorem schemeModulesFunctor_obj (S : Scheme.{u}) (M : S.Modules) :
    (schemeModulesFunctor S).obj M = M :=
  rfl

/-- `schemeModulesFunctor S` sends a morphism of modules on `S` to itself. -/
@[simp]
theorem schemeModulesFunctor_map (S : Scheme.{u}) {M N : S.Modules} (φ : M ⟶ N) :
    (schemeModulesFunctor S).map φ = φ :=
  rfl

/-- `schemeModulesInverse S` sends a sheaf of modules over `S.ringCatSheaf` to itself. -/
@[simp]
theorem schemeModulesInverse_obj (S : Scheme.{u}) (M : SheafOfModules.{u} S.ringCatSheaf) :
    (schemeModulesInverse S).obj M = M :=
  rfl

/-- `schemeModulesInverse S` sends a morphism of sheaves of modules over `S.ringCatSheaf` to
itself. -/
@[simp]
theorem schemeModulesInverse_map (S : Scheme.{u})
    {M N : SheafOfModules.{u} S.ringCatSheaf} (φ : M ⟶ N) :
    (schemeModulesInverse S).map φ = φ :=
  rfl

/-- **Modules on a scheme are the sheaves of modules over its sheaf of rings**, by an
equivalence that is the identity on objects and on morphisms in both directions. -/
def schemeModulesEquivalence (S : Scheme.{u}) :
    S.Modules ≌ SheafOfModules.{u} S.ringCatSheaf where
  functor := schemeModulesFunctor S
  inverse := schemeModulesInverse S
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- The functor of `schemeModulesEquivalence S` is `schemeModulesFunctor S`. -/
@[simp]
theorem schemeModulesEquivalence_functor (S : Scheme.{u}) :
    (schemeModulesEquivalence S).functor = schemeModulesFunctor S :=
  rfl

/-- The inverse of `schemeModulesEquivalence S` is `schemeModulesInverse S`. -/
@[simp]
theorem schemeModulesEquivalence_inverse (S : Scheme.{u}) :
    (schemeModulesEquivalence S).inverse = schemeModulesInverse S :=
  rfl

/-! ### Instances at the `TopCat.Sheaf`-typed spelling -/

section Instances

variable (X : RingedSpace.{u, u})

/-- Sheaves of modules on a ringed space, spelled through `ringCatSheaf`, form an abelian
category. -/
instance abelian_sheafOfModules_ringCatSheaf :
    Abelian (SheafOfModules.{u} (ringCatSheaf X)) :=
  AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules
    (structureSheafRing X)

/-- Sheaves of modules on a ringed space, spelled through `ringCatSheaf`, form a Grothendieck
abelian category. -/
instance isGrothendieckAbelian_sheafOfModules_ringCatSheaf :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} (ringCatSheaf X)) :=
  _root_.SheafOfModules.instIsGrothendieckAbelian
    (structureSheafRing X)

/-- Sheaves of modules on a ringed space, spelled through `ringCatSheaf`, have enough
injectives. -/
instance enoughInjectives_sheafOfModules_ringCatSheaf :
    EnoughInjectives (SheafOfModules.{u} (ringCatSheaf X)) :=
  IsGrothendieckAbelian.enoughInjectives.{u}

/-- Sheaves of modules on a ringed space, spelled through
`structureSheafRing`, form an abelian category. -/
instance abelian_sheafOfModules_ringSheaf :
    Abelian (SheafOfModules.{u} (structureSheafRing X)) :=
  AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules
    (structureSheafRing X)

/-- Sheaves of modules on a ringed space, spelled through
`structureSheafRing`, form a Grothendieck abelian category. -/
instance isGrothendieckAbelian_sheafOfModules_ringSheaf :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} (structureSheafRing X)) :=
  _root_.SheafOfModules.instIsGrothendieckAbelian
    (structureSheafRing X)

/-- Sheaves of modules on a ringed space, spelled through
`structureSheafRing`, have enough injectives. -/
instance enoughInjectives_sheafOfModules_ringSheaf :
    EnoughInjectives (SheafOfModules.{u} (structureSheafRing X)) :=
  IsGrothendieckAbelian.enoughInjectives.{u}

/-- Sheaves of modules on a ringed space, spelled through
`Stacks.SheafOfModules.Tensor.ringSheaf`, form an abelian category. -/
instance abelian_sheafOfModules_tensorRingSheaf :
    Abelian (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) :=
  AlgebraicGeometry.SheafOfModules.instAbelianSheafOfModules
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)

/-- Sheaves of modules on a ringed space, spelled through
`Stacks.SheafOfModules.Tensor.ringSheaf`, form a Grothendieck abelian category. -/
instance isGrothendieckAbelian_sheafOfModules_tensorRingSheaf :
    IsGrothendieckAbelian.{u}
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) :=
  _root_.SheafOfModules.instIsGrothendieckAbelian
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)

/-- Sheaves of modules on a ringed space, spelled through
`Stacks.SheafOfModules.Tensor.ringSheaf`, have enough injectives. -/
instance enoughInjectives_sheafOfModules_tensorRingSheaf :
    EnoughInjectives
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)) :=
  IsGrothendieckAbelian.enoughInjectives.{u}

end Instances

end Stacks.RingedSpaceModules

end
