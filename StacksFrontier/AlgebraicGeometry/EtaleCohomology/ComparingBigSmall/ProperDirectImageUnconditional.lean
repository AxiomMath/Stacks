module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.Topologies.BigEtale.SmallEtaleFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BaseChangeCommutationUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallToBigTopos
public import StacksFrontier.CategoryTheory.Sites.PullbackSectionsComparisonUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperDirectImage
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.ProperDirectImage

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundedSetBaseChangeTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundedSetBaseChangeTransferUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackSections

/-!
# Restriction squares between the big and small étale sites

Let `B` be a big étale site, `U` an object of the big étale site over `S` and `f : T ⟶ S` a
morphism of `B`. For sheaves with values in a category `A`, restriction from the big étale topos
over `S` to the small étale topos of `U` commutes with the inverse image along `U ⟶ S` and with
the big direct image along `f`.

## Main definitions

* `AlgebraicGeometry.bigEtaleRestrictionPullbackSquareGeneral`: the comparison
  `(U ⟶ S)⁻¹ ⟶ π_S⁻¹ ⋙ ρ_U` of inverse images, as a 2-square.
* `AlgebraicGeometry.bigEtaleRestrictionDirectImageSquareGeneral`: the 2-square comparing
  restriction followed by the small direct image along `U ×_S T ⟶ U` with the big direct image
  along `f` followed by restriction.

## Main results

* `AlgebraicGeometry.isIso_bigEtaleRestrictionPullbackSquare_general`: the comparison of inverse
  images is an isomorphism.
* `AlgebraicGeometry.isIso_bigEtaleRestrictionDirectImageSquare_general`: restriction commutes
  with the big direct image along `f`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.TwoSquare
open Opposite

universe u v v₁ u₁

attribute [-instance] Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange

namespace AlgebraicGeometry

section BaseChange

variable (B : BigEtaleSite.{u})

variable (A : Type u₁) [Category.{v₁} A]

variable {T S : B.Scheme} (f : T ⟶ S)

end BaseChange

section Restriction

variable (B : BigEtaleSite.{u}) (A : Type u₁) [Category.{v₁} A] (S : B.Scheme)
  (U : BigEtaleOver B S.obj S.property)

variable {LS : Sheaf (SmallEtale.topology B S.obj S.property) A ⥤
    Sheaf (BigEtaleOver.topology B S.obj S.property) A}
  (adjS : LS ⊣ bigEtaleProjectionPushforward B A S)
  [((smallEtaleBaseChange B U.hom).sheafPushforwardContinuous A
    (SmallEtale.topology B S.obj S.property)
    (SmallEtale.topology B U.left.obj U.left.property)).IsRightAdjoint]
  [∀ F : (SmallEtale B U.left.obj U.left.property)ᵒᵖ ⥤ A,
    (smallEtaleToBigEtaleFunctor B U.left S U.hom).op.HasPointwiseRightKanExtension F]

/-- The comparison `(U ⟶ S)⁻¹ ⟶ π_S⁻¹ ⋙ ρ_U` of inverse images, as a 2-square: the small étale
pullback along `U ⟶ S` is the inverse image along `π_S` followed by restriction to `U`. -/
alias bigEtaleRestrictionPullbackSquareGeneral := bigEtaleRestrictionPullbackSquare

/-- The comparison of inverse images `bigEtaleRestrictionPullbackSquareGeneral` is an
isomorphism. -/
public instance isIso_bigEtaleRestrictionPullbackSquare_general :
    IsIso (bigEtaleRestrictionPullbackSquareGeneral B A S U adjS).natTrans :=
  isIso_bigEtaleRestrictionPullbackSquare B A S U adjS

end Restriction

section FibreSquare

variable (B : BigEtaleSite.{u}) (A : Type u₁) [Category.{v₁} A] {T S : B.Scheme} (f : T ⟶ S)
  (U : BigEtaleOver B S.obj S.property)

/-- Restriction to the small étale site of `U ×_S T` followed by the small direct image along
`U ×_S T ⟶ U` compared with the big direct image along `f` followed by restriction to the small
étale site of `U`. -/
alias bigEtaleRestrictionDirectImageSquareGeneral := bigEtaleRestrictionDirectImageSquare

/-- **Restriction commutes with the big direct image along `f`**: the comparison
`bigEtaleRestrictionDirectImageSquareGeneral` is an isomorphism. -/
public instance isIso_bigEtaleRestrictionDirectImageSquare_general :
    IsIso (bigEtaleRestrictionDirectImageSquareGeneral B A f U) :=
  isIso_bigEtaleRestrictionDirectImageSquare B A f U

end FibreSquare

section Cube

variable (B : BigEtaleSite.{u}) (A : Type u₁) [Category.{v₁} A] {T S : B.Scheme} (f : T ⟶ S)
  (U : BigEtaleOver B S.obj S.property)
  [∀ {X Y : B.Scheme} (k : X ⟶ Y), ((smallEtaleBaseChange B k).sheafPushforwardContinuous A
    (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)).IsRightAdjoint]
  [∀ (X Y : B.Scheme) (k : X ⟶ Y) (F : (SmallEtale B X.obj X.property)ᵒᵖ ⥤ A),
    (smallEtaleToBigEtaleFunctor B X Y k).op.HasPointwiseRightKanExtension F]
  {LT : Sheaf (SmallEtale.topology B T.obj T.property) A ⥤
    Sheaf (BigEtaleOver.topology B T.obj T.property) A}
  {LS : Sheaf (SmallEtale.topology B S.obj S.property) A ⥤
    Sheaf (BigEtaleOver.topology B S.obj S.property) A}
  (adjT : LT ⊣ bigEtaleProjectionPushforward B A T)
  (adjS : LS ⊣ bigEtaleProjectionPushforward B A S)

end Cube

section Main

variable (B : BigEtaleSite.{u}) (A : Type u₁) [Category.{v₁} A] {T S : B.Scheme} (f : T ⟶ S)

end Main

end AlgebraicGeometry

end
