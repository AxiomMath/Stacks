module

public import StacksFrontier.AlgebraicGeometry.AlgebraSheafFiniteCoherent
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FiniteFlat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.UniqueExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ModuleAlgebraData
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.AlgebraSheafIsomorphism
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The relative spectrum of a finite locally free algebra

A commutative algebra structure on a sheaf of `𝒪_X`-modules `ℰ` is a
`Stacks.FundamentalGroup.ModuleAlgebraData ℰ`: a unit `𝒪_X ⟶ ℰ`, a multiplication
`ℰ ⊗ ℰ ⟶ ℰ`, and the three laws. Such a datum turns `ℰ` into a sheaf of algebras
`Stacks.FundamentalGroup.algebraSheafOfModule ℰ d`, and that sheaf of algebras has a relative
spectrum `Spec_X(ℰ, μ) ⟶ X`.

This file records what that morphism is when `ℰ` is finite locally free: it is **finite locally
free** in the sense of [Stacks, Tag 02KA], hence finite, flat and locally of finite
presentation. This is the step "take the relative spectrum" of the construction in the proof of
[Stacks, Tag 0EK1]: there `ℰ` is the algebraization of the tower `(π_{n,*}𝒪_{U_n})` of pushed
forward structure sheaves of a tower of finite étale covers, `μ` is the transported
multiplication, and the resulting scheme is the sought cover once it has been seen to be étale
near the closed subscheme.

The chain is short because every link is already in the library: the module underlying
`algebraSheafOfModule ℰ d` is isomorphic to `ℰ`
(`Stacks.FundamentalGroup.algebraSheafOfModuleIso`), finite local freeness and quasi-coherence
transport along that isomorphism, the relative spectrum of a quasi-coherent algebra sheaf whose
module is of finite type is finite
(`Stacks.FundamentalGroup.ExtendedEtaleFold.isFinite_relativeSpecToBase_of_isFiniteType`), and
the direct image of the structure sheaf of a relative spectrum is the algebra one started from
([Stacks, Tag 01LX(3)], `Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`), which is what
the definition of a finite locally free morphism asks about.

## Main results

* `Stacks.FundamentalGroup.isFiniteLocallyFree_relativeSpecToBase` — the relative spectrum of a
  quasi-coherent algebra sheaf whose underlying module is finite locally free is a finite locally
  free morphism. Stated for an arbitrary algebra sheaf, so it does not mention
  `ModuleAlgebraData`.
* `Stacks.FundamentalGroup.algebraSheafOfModule_isQuasicoherent` and
  `Stacks.FundamentalGroup.isFiniteLocallyFree_underlyingModule_algebraSheafOfModule` — the two
  transports along `Stacks.FundamentalGroup.algebraSheafOfModuleIso`.
* `Stacks.FundamentalGroup.moduleAlgebraSpecToBase` — the morphism `Spec_X(ℰ, μ) ⟶ X`, together
  with `Stacks.FundamentalGroup.isFiniteLocallyFree_moduleAlgebraSpecToBase`,
  `Stacks.FundamentalGroup.isFinite_moduleAlgebraSpecToBase`,
  `Stacks.FundamentalGroup.flat_moduleAlgebraSpecToBase` and
  `Stacks.FundamentalGroup.locallyOfFinitePresentation_moduleAlgebraSpecToBase`.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 0EK1](https://stacks.math.columbia.edu/tag/0EK1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.RelativeSpec (AlgebraSheaf)
open Stacks.AffineAlgebraEquivalence (relativeSpec relativeSpecToBase pushforwardAlgebra
  pushforwardAlgebraIso)

universe u

namespace Stacks.FundamentalGroup

/-! ### The relative spectrum of a finite locally free algebra sheaf -/

/-- **The direct image of the structure sheaf of a relative spectrum is the algebra one started
from.** This is the module underlying [Stacks, Tag 01LX(3)]: the direct image of the structure
sheaf, as a module, is the module underlying the direct image as an algebra, and that algebra is
`A`. -/
@[sga "6 VI 2.3.1" "isomorphism A ≅ f_*𝒪_Y"]
public def pushforwardStructureSheaf_relativeSpecToBase_iso {X : Scheme.{u}}
    (A : AlgebraSheaf X) [AlgebraSheaf.IsQuasicoherent A] :
    Stacks.Morphisms.pushforwardStructureSheaf (relativeSpecToBase A) ≅
      AlgebraSheaf.underlyingModule A :=
  AlgebraSheaf.underlyingModuleIso (pushforwardAlgebraIso A)

/-- **The relative spectrum of a finite locally free algebra sheaf is a finite locally free
morphism.** By [Stacks, Tag 01LX] the relative spectrum is an affine morphism and the direct
image of its structure sheaf is the algebra sheaf itself, so the module appearing in the
definition of a finite locally free morphism ([Stacks, Tag 02KA]) is the module underlying the
algebra. -/
@[sga "1 VIII 7.6" "partial"]
public theorem isFiniteLocallyFree_relativeSpecToBase {X : Scheme.{u}} (A : AlgebraSheaf X)
    [AlgebraSheaf.IsQuasicoherent A]
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (AlgebraSheaf.underlyingModule A)) :
    Stacks.Morphisms.IsFiniteLocallyFree (relativeSpecToBase A) :=
  let := h
  .mk (toIsAffineHom := inferInstance)
    (toIsFiniteLocallyFree := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
      (pushforwardStructureSheaf_relativeSpecToBase_iso A).symm)

/-! ### Transporting the two module properties along `algebraSheafOfModuleIso` -/

variable {X : Scheme.{u}} (E : X.Modules) (d : ModuleAlgebraData E)

/-- **The sheaf of algebras attached to a commutative algebra structure on a quasi-coherent
module is quasi-coherent.** Its underlying module is isomorphic to the module one started
from. -/
public theorem algebraSheafOfModule_isQuasicoherent (h : E.IsQuasicoherent) :
    AlgebraSheaf.IsQuasicoherent (algebraSheafOfModule E d) :=
  Stacks.Descent.isQuasicoherent_of_iso
    (algebraSheafOfModuleIso E d).symm h

/-- **The module underlying the sheaf of algebras attached to a commutative algebra structure on
a finite locally free module is finite locally free.** -/
public theorem isFiniteLocallyFree_underlyingModule_algebraSheafOfModule
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (AlgebraSheaf.underlyingModule (algebraSheafOfModule E d)) :=
  let := h
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso (algebraSheafOfModuleIso E d).symm

/-! ### The relative spectrum of a commutative algebra structure on a module -/

/-- **The sheaf of algebras attached to a commutative algebra structure on a finite locally free
module is quasi-coherent.** A finite locally free module is quasi-coherent. -/
public theorem algebraSheafOfModule_isQuasicoherent_of_isFiniteLocallyFree
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    AlgebraSheaf.IsQuasicoherent (algebraSheafOfModule E d) :=
  let := h
  algebraSheafOfModule_isQuasicoherent E d
    (Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E)

/-- **The relative spectrum `Spec_X(ℰ, μ)` of a commutative algebra structure on a finite locally
free module.** The finite local freeness of `ℰ` enters only through quasi-coherence, which the
relative spectrum needs in order to exist. -/
public def moduleAlgebraSpec
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) : Scheme.{u} :=
  let := algebraSheafOfModule_isQuasicoherent_of_isFiniteLocallyFree E d h
  relativeSpec (algebraSheafOfModule E d)

/-- **The structure morphism `Spec_X(ℰ, μ) ⟶ X`.** -/
public def moduleAlgebraSpecToBase
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    moduleAlgebraSpec E d h ⟶ X :=
  let := algebraSheafOfModule_isQuasicoherent_of_isFiniteLocallyFree E d h
  relativeSpecToBase (algebraSheafOfModule E d)

/-- **`Spec_X(ℰ, μ) ⟶ X` is finite locally free when `ℰ` is.** -/
public theorem isFiniteLocallyFree_moduleAlgebraSpecToBase
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    Stacks.Morphisms.IsFiniteLocallyFree (moduleAlgebraSpecToBase E d h) :=
  let := algebraSheafOfModule_isQuasicoherent_of_isFiniteLocallyFree E d h
  isFiniteLocallyFree_relativeSpecToBase (algebraSheafOfModule E d)
    (isFiniteLocallyFree_underlyingModule_algebraSheafOfModule E d h)

/-- Unpacking finite local freeness of `Spec_X(ℰ, μ) ⟶ X` into its three constituent properties. -/
private theorem moduleAlgebraSpecToBase_isFinite_flat_locallyOfFinitePresentation
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    IsFinite (moduleAlgebraSpecToBase E d h) ∧ Flat (moduleAlgebraSpecToBase E d h) ∧
      LocallyOfFinitePresentation (moduleAlgebraSpecToBase E d h) :=
  (Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
    (moduleAlgebraSpecToBase E d h)).mp (isFiniteLocallyFree_moduleAlgebraSpecToBase E d h)

/-- **`Spec_X(ℰ, μ) ⟶ X` is finite when `ℰ` is finite locally free.** -/
public theorem isFinite_moduleAlgebraSpecToBase
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    IsFinite (moduleAlgebraSpecToBase E d h) :=
  (moduleAlgebraSpecToBase_isFinite_flat_locallyOfFinitePresentation E d h).1

/-- **`Spec_X(ℰ, μ) ⟶ X` is flat when `ℰ` is finite locally free.** -/
public theorem flat_moduleAlgebraSpecToBase
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    Flat (moduleAlgebraSpecToBase E d h) :=
  (moduleAlgebraSpecToBase_isFinite_flat_locallyOfFinitePresentation E d h).2.1

/-- **`Spec_X(ℰ, μ) ⟶ X` is locally of finite presentation when `ℰ` is finite locally free.** -/
public theorem locallyOfFinitePresentation_moduleAlgebraSpecToBase
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    LocallyOfFinitePresentation (moduleAlgebraSpecToBase E d h) :=
  (moduleAlgebraSpecToBase_isFinite_flat_locallyOfFinitePresentation E d h).2.2

end Stacks.FundamentalGroup

end
