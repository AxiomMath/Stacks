module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.Finiteness
public import StacksFrontier.AlgebraicGeometry.RelativeSpec.QuasicoherentSquare

/-!
# Quasi-coherent algebras on a scheme

A sheaf of commutative algebras over the structure sheaf of a scheme is recorded as an object
under the structure sheaf. Its underlying module is obtained by restriction of scalars along its
structure morphism, which is what quasi-coherence is imposed on; finite presentation is imposed
on the sections over every affine open.

## Main definitions

* `AlgebraicGeometry.Scheme.QuasicoherentAlgebra` is the category of sheaves of commutative
  `O_X`-algebras.
* `AlgebraicGeometry.Scheme.QuasicoherentAlgebra.underlyingModule` is the underlying
  `O_X`-module of such an algebra.
* `AlgebraicGeometry.Scheme.QuasicoherentAlgebra.IsQuasicoherent` and
  `AlgebraicGeometry.Scheme.QuasicoherentAlgebra.IsOfFinitePresentation` are the two properties
  of an algebra sheaf.

## Implementation notes

Keeping the category unbundled, rather than carrying quasi-coherence in the type, lets colimits
be stated in the ambient category of algebra sheaves. The underlying module is formed by
restricting scalars along the structure morphism after forgetting commutativity, since
restriction of scalars is available for sheaves of (not necessarily commutative) rings.

The same notion is also carried by `Stacks.RelativeSpec.AlgebraSheaf`, whose two modules this
one re-exports: `Stacks.RelativeSpec.AlgebraSheaf.ringSheaf`,
`Stacks.RelativeSpec.AlgebraSheaf.structureMap`,
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModule` and
`Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent` are the same constructions under different
names, and `Stacks.RelativeSpec.AlgebraSheaf.IsFinite`,
`Stacks.RelativeSpec.AlgebraSheaf.IsFiniteType`,
`Stacks.RelativeSpec.AlgebraSheaf.IsFinitePresentation` and
`Stacks.RelativeSpec.AlgebraSheaf.IsIntegral` are the finiteness conditions stated there, also
tested on the sections over the affine opens.
`Stacks.FPAlgebraSheaf.isOfFinitePresentation_iff_isFinitePresentation` identifies
`IsOfFinitePresentation` with `Stacks.RelativeSpec.AlgebraSheaf.IsFinitePresentation`, so a
lemma proved against either spelling applies to the other.

## References

* [Stacks Project, Tag 05JS](https://stacks.math.columbia.edu/tag/05JS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme

/-- The category of sheaves of commutative `O_X`-algebras. -/
public abbrev QuasicoherentAlgebra (X : Scheme.{u}) := Under X.sheaf

namespace QuasicoherentAlgebra

/-- The underlying sheaf of rings of an `O_X`-algebra sheaf. -/
public noncomputable def ringSheaf {X : Scheme.{u}} (A : X.QuasicoherentAlgebra) :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).obj A.right

/-- The structure morphism of an algebra sheaf, after forgetting commutativity. -/
public noncomputable def structureMap {X : Scheme.{u}} (A : X.QuasicoherentAlgebra) :
    X.ringCatSheaf ⟶ ringSheaf A :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat)).map A.hom

/-- The underlying `O_X`-module of an algebra sheaf. -/
public noncomputable def underlyingModule {X : Scheme.{u}} (A : X.QuasicoherentAlgebra) :
    X.Modules :=
  (SheafOfModules.restrictScalars.{u} (structureMap A)).obj
    (SheafOfModules.unit (ringSheaf A))

/-- An algebra sheaf is quasi-coherent when its underlying module is quasi-coherent. -/
public abbrev IsQuasicoherent {X : Scheme.{u}} (A : X.QuasicoherentAlgebra) : Prop :=
  (underlyingModule A).IsQuasicoherent

/-- An algebra sheaf is of finite presentation when its structural ring map is finitely
presented on every affine open. -/
public def IsOfFinitePresentation {X : Scheme.{u}} (A : X.QuasicoherentAlgebra) : Prop :=
  ∀ U : X.Opens, IsAffineOpen U →
    RingHom.FinitePresentation (A.hom.hom.app (.op U)).hom

end QuasicoherentAlgebra

end AlgebraicGeometry.Scheme

end
