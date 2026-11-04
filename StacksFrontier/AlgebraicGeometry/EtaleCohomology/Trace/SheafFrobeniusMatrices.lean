module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CharPowerSeries
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusClosedPoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Frobenius matrices of a sheaf

The L-function of a sheaf on the étale site of a scheme over a finite field is the Euler product
of the local factors `det(1 - π_x^* T ^ (deg x))` of the geometric Frobenius acting on the stalk
at each closed point. This file constructs those matrices from the sheaf.

Over a local coefficient ring the stalk of a sheaf whose stalks are finite and projective is
finite free, so it has a basis, and the geometric Frobenius at a closed point becomes a square
matrix in that basis. The rank is the rank of the stalk. Choosing a basis is not a loss of
information: the local factor of the resulting matrix is the basis-free local factor of the
Frobenius endomorphism, so nothing depends on the choice.

The residue field at a closed point of a scheme locally of finite type over a finite field is
itself finite, so the geometric Frobenius at that point is defined.

## Main definitions

* `Stacks.EtaleCohomology.rankOf` and `Stacks.EtaleCohomology.matrixOf`: the rank of a module and
  the matrix of an endomorphism in a chosen basis.
* `Stacks.EtaleCohomology.frobeniusStalkEnd`: the geometric Frobenius at a closed point as an
  endomorphism of the stalk.
* `Stacks.EtaleCohomology.frobeniusMatricesOfSheaf`: the family of Frobenius matrices of a sheaf.
* `Stacks.EtaleCohomology.lFunctionOfSheaf`: its L-function.

## Main results

* `Stacks.EtaleCohomology.charPowerSeries_eq_localCharSeries_matrixOf` and
  `Stacks.EtaleCohomology.charPowerSeries_frobeniusStalkEnd`: the local factor of the matrix is
  the basis-free local factor of the endomorphism, at the level of modules and of stalks.
* `Stacks.EtaleCohomology.finite_residueField`: the residue field at a closed point of a scheme
  locally of finite type over a finite field is finite.
* `Stacks.EtaleCohomology.isUnit_lFunctionOfSheaf`: the L-function of a sheaf is a unit.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u v w r

namespace Stacks.EtaleCohomology

/-! ### Matrices of endomorphisms of finite projective modules over a local ring -/

section LinearAlgebra

variable (Λ : Type v) [CommRing Λ] (M : Type w) [AddCommGroup M] [Module Λ M]

/-- The rank of a `Λ`-module. -/
public def rankOf : ℕ := Module.finrank Λ M

variable [IsLocalRing Λ] [Module.Finite Λ M] [Module.Projective Λ M]

/-- A basis of a finite projective module over a commutative local ring indexed by
`Fin (rankOf Λ M)`. -/
public def chooseBasisFin : Module.Basis (Fin (rankOf Λ M)) Λ M :=
  haveI : Module.Flat Λ M := Module.Flat.of_projective
  haveI : Module.Free Λ M := Module.free_of_flat_of_isLocalRing
  letI := Module.Free.ChooseBasisIndex.fintype Λ M
  (Module.Free.chooseBasis Λ M).reindex
    (Fintype.equivFinOfCardEq (Module.finrank_eq_card_chooseBasisIndex Λ M).symm)

/-- The matrix of an endomorphism in the chosen basis. -/
public def matrixOf (φ : M →ₗ[Λ] M) : Matrix (Fin (rankOf Λ M)) (Fin (rankOf Λ M)) Λ :=
  LinearMap.toMatrix (chooseBasisFin Λ M) (chooseBasisFin Λ M) φ

/-- The local factor of the matrix of an endomorphism is the basis-free local factor of the
endomorphism. -/
public theorem charPowerSeries_eq_localCharSeries_matrixOf (φ : M →ₗ[Λ] M) (d : ℕ) :
    charPowerSeries φ d = localCharSeries (matrixOf Λ M φ) d :=
  charPowerSeries_eq_localCharSeries (chooseBasisFin Λ M) φ d

end LinearAlgebra

/-! ### Finiteness of residue fields at closed points -/

/-- At a closed point of a scheme locally of finite type over a finite field the residue field is
finite. -/
public theorem finite_residueField {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    Finite (X.residueField x) := by
  let _ : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
  have : Algebra.FiniteType k (X.residueField x) := finiteType_fieldToResidue f x hx
  have : Module.Finite k (X.residueField x) :=
    finite_of_finite_type_of_isJacobsonRing k (X.residueField x)
  exact Module.finite_of_finite k

/-! ### The Frobenius matrices of a sheaf -/

section Geometric

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]
  [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)] [HasLimitsOfSize.{u, u} (ModuleCat.{w} Λ)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))

/-- The étale stalk of `F` at the geometric point at `x`, read on Mathlib's small étale site. -/
public abbrev frobeniusStalkModule (x : X.obj) : ModuleCat.{w} Λ :=
  ((Scheme.pointSmallEtale (geometricPointAt X.obj x).hom).sheafFiber
      (A := ModuleCat.{w} Λ)).obj
    ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{w} Λ)).functor.obj F)

/-- If the étale stalk of `F` at `s` is projective, so is the stalk at `s` of the corresponding
sheaf on Mathlib's small étale site. -/
public theorem projective_sheafFiber_sheafEquiv (s : GeometricPoint X.obj)
    (hF : Module.Projective Λ ((etaleModuleStalkFunctor B X Λ s).obj F)) :
    Module.Projective Λ (((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{w} Λ)).obj
      ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{w} Λ)).functor.obj F)) :=
  Module.Projective.of_equiv ((sheafEquivCompSheafFiberIso B X Λ s).app F).symm.toLinearEquiv

variable [IsLocalRing Λ] {k : Type u} [Field k] [Finite k] (f : X.obj ⟶ Spec (.of k))
  [LocallyOfFiniteType f]
  (hfin : ∀ s : GeometricPoint X.obj, Module.Finite Λ ((etaleModuleStalkFunctor B X Λ s).obj F))
  (hproj : ∀ s : GeometricPoint X.obj,
    Module.Projective Λ ((etaleModuleStalkFunctor B X Λ s).obj F))

/-- The geometric Frobenius at a closed point, as an endomorphism of the stalk there. -/
@[sga "4½ Rapport 1.5"]
public def frobeniusStalkEnd (x : closedPoints X.obj) :
    ↥(frobeniusStalkModule B X Λ F x.1) →ₗ[Λ] ↥(frobeniusStalkModule B X Λ F x.1) :=
  haveI := finite_residueField f x.1 x.2
  (frobeniusStalk (ModuleCat.{w} Λ) X.obj x.1
    ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{w} Λ)).functor.obj F)).hom

/-- **The Frobenius matrices of a sheaf.** The rank at a closed point is the rank of the stalk
there and the matrix is that of the geometric Frobenius acting on it, both read off the sheaf. -/
public def frobeniusMatricesOfSheaf : FrobeniusMatrices f Λ where
  rank x := rankOf Λ ↥(frobeniusStalkModule B X Λ F x.1)
  matrix x :=
    haveI := finite_sheafFiber_sheafEquiv B X Λ (geometricPointAt X.obj x.1) F (hfin _)
    haveI := projective_sheafFiber_sheafEquiv B X Λ F (geometricPointAt X.obj x.1) (hproj _)
    matrixOf Λ ↥(frobeniusStalkModule B X Λ F x.1) (frobeniusStalkEnd B X Λ F f x)

/-- The rank of the Frobenius matrix at a closed point is the rank of the stalk there. -/
public theorem rank_frobeniusMatricesOfSheaf (x : closedPoints X.obj) :
    (frobeniusMatricesOfSheaf B X Λ F f hfin hproj).rank x =
      rankOf Λ ↥(frobeniusStalkModule B X Λ F x.1) :=
  rfl

/-- The matrix at a closed point has the same local factor as the geometric Frobenius
endomorphism of the stalk. -/
public theorem charPowerSeries_frobeniusStalkEnd (x : closedPoints X.obj) (d : ℕ) :
    charPowerSeries (frobeniusStalkEnd B X Λ F f x) d =
      localCharSeries ((frobeniusMatricesOfSheaf B X Λ F f hfin hproj).matrix x) d :=
  have := finite_sheafFiber_sheafEquiv B X Λ (geometricPointAt X.obj x.1) F (hfin _)
  have := projective_sheafFiber_sheafEquiv B X Λ F (geometricPointAt X.obj x.1) (hproj _)
  charPowerSeries_eq_localCharSeries_matrixOf Λ _ (frobeniusStalkEnd B X Λ F f x) d

/-- The L-function of a sheaf: the Euler product of the local factors of the geometric Frobenius
on its stalks at the closed points. -/
@[sga "4½ Rapport 1.6" "partial"]
public def lFunctionOfSheaf [QuasiCompact f] : PowerSeries Λ :=
  (frobeniusMatricesOfSheaf B X Λ F f hfin hproj).lFunction

/-- The L-function of a sheaf is a unit of `Λ⟦T⟧`. -/
public theorem isUnit_lFunctionOfSheaf [QuasiCompact f] :
    IsUnit (lFunctionOfSheaf B X Λ F f hfin hproj) :=
  FrobeniusMatrices.isUnit_lFunction _

end Geometric

end Stacks.EtaleCohomology

end
