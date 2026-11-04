module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.Cotangent.SheavesOfRings.RingedSpace
public import StacksFrontier.Deformation.Examples.Geometric.BaseSpectrum
public import StacksFrontier.Deformation.Examples.Linear.ResidueFieldBase
public import StacksFrontier.Deformation.RingedSpaceThickening.NaiveCotangentDerivedExt
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The coefficient terms of the deformation sequence of a morphism of schemes

Let `f : X ⟶ Y` be a morphism of schemes over a field `k`. The exact sequence of
[Stacks Project, Tag 0E3V] has six terms, four of which are the infinitesimal automorphism
groups and the tangent spaces of the deformation categories of `f` and of its two endpoints.
The two remaining ones do not come from a deformation category: they are the `k`-vector spaces

* `Der_k(𝒪_Y, f_*𝒪_X)`, the third term, and
* `Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X)`, the sixth.

This file builds those two terms, each as a `k`-vector space.

`X` is a scheme over `k` through `f ≫ pY`, so the structure morphism of `Y` is the only datum
needed beyond `f` itself: both terms are built from `f` and `pY`.

## Main definitions

* `Deformation.Examples.schemeMorphismPushforwardStructureSheaf`: the `𝒪_Y`-module `f_*𝒪_X`.
* `Deformation.Examples.schemeMorphismDerivations`: the third term `Der_k(𝒪_Y, f_*𝒪_X)` of the
  sequence of [Stacks Project, Tag 0E3V], the `k`-derivations of `𝒪_Y` with values in
  `f_*𝒪_X`.
* `Deformation.Examples.schemeMorphismDerivationsModule`: its `k`-vector space structure.
* `Deformation.Examples.schemeMorphismObstructionExt`: the sixth term
  `Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X)` of that sequence.
* `Deformation.Examples.schemeMorphismObstructionExtModule`: its `k`-vector space structure.
* `Deformation.Examples.schemeMorphismCoefficientSheaf`: the `𝒪_X`-module `𝒪_X ⊗_k M` attached
  to a finite-dimensional `k`-vector space `M`.
* `Deformation.Examples.schemeMorphismObstructionExtTwisted`: the sixth term with those
  coefficients, `Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k M)`, which is where the obstruction over the
  square-zero base `k ⊕ M` lives. At `M = k` it is canonically the source's own sixth term.
* `Deformation.Examples.schemeMorphismObstructionExtTwistedModule`: its `k`-vector space
  structure.

## Main results

* `Deformation.Examples.schemeMorphismDerivationsAddEquiv`: the derivations of `𝒪_Y` with values
  in `f_*N` are the group of `𝒪_Y`-module maps out of `Ω_{Y/k}`, by the corepresentability of
  derivations of [Stacks Project, Tag 04BL]. This is what carries the `k`-action onto them. At
  `N = 𝒪_X` it is the third term.
* `Deformation.Examples.schemeMorphismDerivationsLinearEquiv`: that identification is `k`-linear
  for the `k`-vector space structure the derivations thereby carry, so at `N = 𝒪_X` the third
  term *is* the `k`-vector space `Hom_{𝒪_Y}(Ω_{Y/k}, f_*𝒪_X)`.

The coefficient sheaf of the derivations is a parameter `N` throughout, the third term being the
case `N = 𝒪_X`. Nothing in the corepresentability of derivations or in the `k`-action on them
depends on the coefficients, and leaving them free is what lets the lift-group bridge of
`StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismLiftGroup.lean` be stated without a
rank-one hypothesis on the base object of `𝒞_Λ`.

## Implementation notes

Both terms are read on the ringed spaces underlying the two schemes, where the library's naive
cotangent complex ([Stacks Project, Tag 08TN],
`AlgebraicGeometry.RingedSpace.naiveCotangentComplex`), derived pullback
([Stacks Project, Tag 06YJ],
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback`) and relative derivations
([Stacks Project, Tag 08RT],
`Stacks.Sheaves.RingedSpaceDifferentials.SDerivation`) live. A morphism of schemes is read
there as `f.toLRSHom.toShHom`, as elsewhere in the library.

`Ext¹` is `CategoryTheory.DerivedCategory.Ext _ _ 1`, a morphism into the shift, and the
derived pullback needs no hypothesis: `Lf^*` exists for every morphism of ringed spaces by
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.hasLeftDerivedFunctor_pullbackOnHomotopy`.
The model of the derived category is `HasDerivedCategory.standard`, pinned as a local instance
exactly as in `StacksFrontier/Deformation/RingedSpaceThickening/NaiveCotangentDerivedExt.lean`,
which is where the two groups `Ext¹_{𝒪_X}(NL_{X/S}, 𝒢)` and `Ext¹_{𝒪_X}(Lf^*NL_{S/S'}, 𝒢)` of
the obstruction theory are built.

The `k`-action on sheaves of modules over a scheme over `k` is
`AlgebraicGeometry.modulesLinear`, which depends on the structure morphism and so is supplied
explicitly rather than by instance search. On `Ext¹` it is the `k`-action of the induced linear
structure on the derived category; on `Der_k(𝒪_Y, f_*𝒪_X)` it is transported from
`Hom_{𝒪_Y}(Ω_{Y/k}, f_*𝒪_X)` along `schemeMorphismDerivationsAddEquiv`, there being no action
on a derivation defined termwise. Both are definitions rather than instances: the linear
structure is not determined by the type, only by the structure morphism, so instance search
must not be allowed to guess it.

The arrows of the sequence into and out of these two terms are not here; the part of
[Stacks Project, Tag 0E3V] that the endpoint-forgetting morphism of deformation categories
supplies is `StacksFrontier/Deformation/Examples/Geometric/SchemeMorphismEndpoints.lean`, whose
implementation notes record what the arrows touching these two terms would need.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 08TN](https://stacks.math.columbia.edu/tag/08TN)
* [Stacks Project, Tag 08RT](https://stacks.math.columbia.edu/tag/08RT)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Sheaves.RingedSpaceDifferentials (inverseImageSheaf inverseImageStructureMap
  moduleOfDifferentials)

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (pY : Y ⟶ baseSpec (residueFieldBase Λ k))

/-! ### The third term `Der_k(𝒪_Y, f_*𝒪_X)` -/

/-- The `𝒪_Y`-module `f_*𝒪_X`, the pushforward along `f` of the structure sheaf of `X`: the
module of coefficients of the third term of the sequence of [Stacks Project, Tag 0E3V]. -/
abbrev schemeMorphismPushforwardStructureSheaf :
    SheafOfModules.{u} (structureSheafRing Y.toRingedSpace) :=
  (modulePushforward f.toLRSHom.toShHom).obj
    (SheafOfModules.unit (structureSheafRing X.toRingedSpace))

/-- **Stacks 0E3V**, the third term `Der_k(𝒪_Y, f_*𝒪_X)` of the source's exact sequence: the
derivations of the structure sheaf of `Y` relative to the residue field, with values in the
`𝒪_Y`-module `f_*𝒪_X`. -/
@[sga "3 VIIA 1.2.0" "special case"]
abbrev schemeMorphismDerivations : Type u :=
  Stacks.Sheaves.RingedSpaceDifferentials.SDerivation pY.toLRSHom.toShHom
    (schemeMorphismPushforwardStructureSheaf f)

/-! ### Derivations with values in the pushforward of an arbitrary coefficient sheaf

The third term of the sequence takes its coefficients in `f_*𝒪_X`, but nothing in the
corepresentability of derivations or in the `k`-action on them depends on the coefficient sheaf
being the structure sheaf: the group of derivations, its additive structure, its `k`-vector
space structure and its identification with `Hom_{𝒪_Y}(Ω_{Y/k}, f_*N)` are stated below for an
arbitrary `𝒪_X`-module `N`. The third term is the case `N = 𝒪_X`, where
`(modulePushforward f).obj (SheafOfModules.unit _)` is
`Deformation.Examples.schemeMorphismPushforwardStructureSheaf f` and the type of derivations is
`Deformation.Examples.schemeMorphismDerivations f pY`, both as the same term.

The rank of the base object of `𝒞_Λ` enters the deformation theory only through this coefficient
sheaf: over a square-zero base with maximal ideal of rank `n` the conormal sheaf of the special
fibre is free of rank `n` rather than `1`, and it is the acting group of
[Stacks Project, Tag 0CK2] that has to accommodate it.
-/

variable (N : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- Derivations of `𝒪_Y` relative to the residue field with values in the pushforward `f_*N` of
an `𝒪_X`-module form an additive group, termwise. At `N = 𝒪_X` this is the additive structure of
the third term `Der_k(𝒪_Y, f_*𝒪_X)` of the sequence of [Stacks Project, Tag 0E3V]. -/
instance schemeMorphismDerivationsAddCommGroup :
    AddCommGroup (Stacks.Sheaves.RingedSpaceDifferentials.SDerivation pY.toLRSHom.toShHom
      ((modulePushforward f.toLRSHom.toShHom).obj N)) :=
  AlgebraicGeometry.SheafOfModules.derivationAddCommGroup
    (inverseImageStructureMap pY.toLRSHom.toShHom).hom
    ((modulePushforward f.toLRSHom.toShHom).obj N).val

/-- **The derivations of `𝒪_Y` relative to the residue field with values in `f_*N` are the
`𝒪_Y`-module maps `Ω_{Y/k} ⟶ f_*N`**: a derivation is the same thing as a map out of the module
of differentials, by the corepresentability of relative derivations of
[Stacks Project, Tag 04BL], and the identification is additive. At `N = 𝒪_X` this is the third
term of the sequence of [Stacks Project, Tag 0E3V] as the group of maps `Ω_{Y/k} ⟶ f_*𝒪_X`. -/
def schemeMorphismDerivationsAddEquiv :
    (moduleOfDifferentials pY.toLRSHom.toShHom ⟶
        (modulePushforward f.toLRSHom.toShHom).obj N) ≃+
      Stacks.Sheaves.RingedSpaceDifferentials.SDerivation pY.toLRSHom.toShHom
        ((modulePushforward f.toLRSHom.toShHom).obj N) :=
  ((AlgebraicGeometry.SheafOfModules.derivationsAddCommGrpCorepresentation.{u, u, u, u}
      (inverseImageSheaf pY.toLRSHom.toShHom) Y.toRingedSpace.sheaf
      (inverseImageStructureMap pY.toLRSHom.toShHom)
      (Stacks.Sheaves.RingedSpaceCotangent.moduleOfDifferentials_corepresentableBy
        pY.toLRSHom.toShHom)).app
    ((modulePushforward f.toLRSHom.toShHom).obj N)).addCommGroupIsoToAddEquiv

/-- The `k`-vector space structure on the derivations of `𝒪_Y` with values in `f_*N`: the
`k`-action on `Hom_{𝒪_Y}(Ω_{Y/k}, f_*N)` coming from the structure morphism of `Y`, transported
along `schemeMorphismDerivationsAddEquiv`. At `N = 𝒪_X` this is the `k`-vector space structure
on the third term `Der_k(𝒪_Y, f_*𝒪_X)` of the sequence of [Stacks Project, Tag 0E3V]. -/
@[instance_reducible]
def schemeMorphismDerivationsModule :
    Module k (Stacks.Sheaves.RingedSpaceDifferentials.SDerivation pY.toLRSHom.toShHom
      ((modulePushforward f.toLRSHom.toShHom).obj N)) :=
  letI : Module k (moduleOfDifferentials pY.toLRSHom.toShHom ⟶
      (modulePushforward f.toLRSHom.toShHom).obj N) :=
    (AlgebraicGeometry.modulesLinear k (Over.mk pY)).homModule _ _
  (schemeMorphismDerivationsAddEquiv f pY N).symm.module k

/-- The identification of the derivations of `𝒪_Y` with values in `f_*N` with
`Hom_{𝒪_Y}(Ω_{Y/k}, f_*N)` is `k`-linear for the `k`-vector space structure
`schemeMorphismDerivationsModule` they thereby carry, that structure being transported along it.
At `N = 𝒪_X` this says that the third term of the sequence of [Stacks Project, Tag 0E3V] *is*
the `k`-vector space `Hom_{𝒪_Y}(Ω_{Y/k}, f_*𝒪_X)`. -/
def schemeMorphismDerivationsLinearEquiv :
    letI : Module k (moduleOfDifferentials pY.toLRSHom.toShHom ⟶
        (modulePushforward f.toLRSHom.toShHom).obj N) :=
      (AlgebraicGeometry.modulesLinear k (Over.mk pY)).homModule _ _
    letI := schemeMorphismDerivationsModule f pY N
    Stacks.Sheaves.RingedSpaceDifferentials.SDerivation pY.toLRSHom.toShHom
        ((modulePushforward f.toLRSHom.toShHom).obj N) ≃ₗ[k]
      (moduleOfDifferentials pY.toLRSHom.toShHom ⟶
        (modulePushforward f.toLRSHom.toShHom).obj N) :=
  letI : Module k (moduleOfDifferentials pY.toLRSHom.toShHom ⟶
      (modulePushforward f.toLRSHom.toShHom).obj N) :=
    (AlgebraicGeometry.modulesLinear k (Over.mk pY)).homModule _ _
  (schemeMorphismDerivationsAddEquiv f pY N).symm.linearEquiv k

/-! ### The sixth term `Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X)` -/

/-- **Stacks 0E3V**, the sixth term `Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X)` of the source's exact
sequence: the first `Ext` group, with coefficients the structure sheaf of `X`, of the derived
pullback along `f` of the naive cotangent complex of `Y` over the residue field. -/
abbrev schemeMorphismObstructionExt : Type (u + 1) :=
  AlgebraicGeometry.RingedSpaceThickening.extOnePulledNaiveCotangent
    f.toLRSHom.toShHom pY.toLRSHom.toShHom
    (SheafOfModules.unit (structureSheafRing X.toRingedSpace))

/-- The `k`-vector space structure on the sixth term `Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X)` of the
sequence of [Stacks Project, Tag 0E3V]: `Ext¹` is a group of morphisms of the derived category
of `𝒪_X`-modules, and `X` is a scheme over the residue field through `f ≫ pY`, so the `k`-linear
structure on `𝒪_X`-modules induces one on that derived category and hence on `Ext¹`. -/
@[instance_reducible]
def schemeMorphismObstructionExtModule : Module k (schemeMorphismObstructionExt f pY) :=
  letI : Linear k (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
    AlgebraicGeometry.modulesLinear k (Over.mk (f ≫ pY))
  (inferInstance : Linear k
    (DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))).homModule _ _

/-! ### The sixth term with coefficients twisted by a finite-dimensional `k`-vector space

A first-order deformation with coefficients in a finite-dimensional `k`-vector space `M` is a
deformation over the square-zero base `k ⊕ M`, whose maximal ideal is `M`. The ideal sheaf of
the special fibre inside such a deformation of `X` is `𝒪_X ⊗_k M`, so the obstruction to
deforming `f` along a pair of them is a class in `Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k M)`, not in
the untwisted group. The source's sequence is the case `M = k`, where `𝒪_X ⊗_k k` is
canonically `𝒪_X`.
-/

/-- The `𝒪_X`-module `𝒪_X ⊗_k M` attached to a finite-dimensional `k`-vector space `M`: the
quasi-coherent sheaf `M^~` on the spectrum of the residue field, pulled back along the structure
morphism `f ≫ pY` of `X`. At `M = k` it is canonically the structure sheaf of `X`; that
identification is not built here.

This is the coefficient sheaf in which a deformation over the square-zero base `k ⊕ M` takes its
obstruction: the ideal sheaf of the special fibre of such a deformation of `X` is free on the
maximal ideal `M` of the base, which is `𝒪_X ⊗_k M`. -/
abbrev schemeMorphismCoefficientSheaf (M : FGModuleCat.{u} k) :
    SheafOfModules.{u} (structureSheafRing X.toRingedSpace) :=
  (Scheme.Modules.pullback (f ≫ pY)).obj (AlgebraicGeometry.tilde M.obj)

/-- The sixth term of the sequence of [Stacks Project, Tag 0E3V] with coefficients twisted by a
finite-dimensional `k`-vector space `M`: the group `Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k M)` in
which the obstruction to deforming `f` along a pair of deformations of its endpoints over the
square-zero base `k ⊕ M` lives.

At `M = k` the coefficient sheaf is canonically `𝒪_X` and this is canonically
`Deformation.Examples.schemeMorphismObstructionExt`, the source's own sixth term; neither
identification is built here. There is no canonical map between the two groups for `M` of
dimension greater than one, which is why the obstruction over a base of higher rank has to be
read here rather than there. -/
abbrev schemeMorphismObstructionExtTwisted (M : FGModuleCat.{u} k) : Type (u + 1) :=
  AlgebraicGeometry.RingedSpaceThickening.extOnePulledNaiveCotangent
    f.toLRSHom.toShHom pY.toLRSHom.toShHom (schemeMorphismCoefficientSheaf f pY M)

/-- The `k`-vector space structure on `Ext¹_{𝒪_X}(Lf^*NL_{Y/k}, 𝒪_X ⊗_k M)`, by the same
argument as for `Deformation.Examples.schemeMorphismObstructionExtModule`: the `k`-linear
structure on `𝒪_X`-modules coming from the structure morphism `f ≫ pY` of `X` induces one on
the derived category of `𝒪_X`-modules and hence on `Ext¹`, whatever the coefficients. -/
@[instance_reducible]
def schemeMorphismObstructionExtTwistedModule (M : FGModuleCat.{u} k) :
    Module k (schemeMorphismObstructionExtTwisted f pY M) :=
  letI : Linear k (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) :=
    AlgebraicGeometry.modulesLinear k (Over.mk (f ≫ pY))
  (inferInstance : Linear k
    (DerivedCategory (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)))).homModule _ _

end Deformation.Examples

end
