module

public import StacksFrontier.AlgebraicGeometry.Flatness.GrothendieckExistence.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatDerivedSectionsPseudoCoherent
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSectionsTensorPullback
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.CanonicalBifunctorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.DerivedTensorProduct

/-!
# The cohomology of the levels of a derived Grothendieck existence situation

In Situation [Stacks, Tag 0DIB] fix an object `E` of `D(𝒪_X)` and write `E_n = E|_{X_n}` for its
derived pullback to the base change `X_n = X ×_{Spec A} Spec A_n`. The proof of
[Stacks, Tag 0DID] studies the objects

`M_n = RΓ(X_n, K_n ⊗^L E_n)`

of `D(A_n)`. This file defines them and proves the first assertion made about them: when `E` is
pseudo-coherent (for instance perfect) each `M_n` is a pseudo-coherent object of `D(A_n)`.

## Main definitions

All names below are in the namespace `AlgebraicGeometry.GrothendieckExistence`.

* `levelStructure`: the structure morphism `X_n ⟶ Spec A_n`.
* `DerivedExistenceSituation.levelPullback`: `E_n`.
* `DerivedExistenceSituation.levelTensor`: `K_n ⊗^L E_n`.
* `DerivedExistenceSituation.levelCohomology`: `M_n`.

## Main results

* `DerivedExistenceSituation.isPseudoCoherent_levelCohomology`: `M_n` is pseudo-coherent.

## Implementation notes

The structure morphism `X_n ⟶ Spec A_n` is the base change of `X ⟶ Spec A`, so it is flat,
proper and of finite presentation; [Stacks, Tag 0CSD] over the affine base
(`AlgebraicGeometry.isPseudoCoherent_derivedGlobalSectionsOver_of_flat_of_isProper`) then applies
to the pseudo-coherent `K_n ⊗^L E_n` ([Stacks, Tag 09J3] and [Stacks, Tag 09U7]).

## References

* [Stacks Project, Tag 0DID](https://stacks.math.columbia.edu/tag/0DID)
* [Stacks Project, Tag 0DIB](https://stacks.math.columbia.edu/tag/0DIB)
* [Stacks Project, Tag 0CSD](https://stacks.math.columbia.edu/tag/0CSD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- **The derived tensor product of two pseudo-coherent objects of `D(𝒪_Y)` is pseudo-coherent**
([Stacks, Tag 09J3] part (2)), for the derived tensor product
`Stacks.SheafOfModules.derivedTensor` of the ringed site of opens, which is identified with the one
of [Stacks, Tag 09J3] by `AlgebraicGeometry.RingedSite.derivedTensorObjIso`. -/
theorem isPseudoCoherent_derivedTensor (Y : Scheme.{u})
    (K E : DerivedCategory (Stacks.SheafOfModules.StructureSheafModules Y.sheaf))
    (hK : RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace) K)
    (hE : RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace) E) :
    RingedSpace.IsPseudoCoherent (X := Y.toRingedSpace)
      (((Stacks.SheafOfModules.derivedTensor Y.sheaf).obj K).obj E) := by
  have e : ((Stacks.SheafOfModules.derivedTensor Y.sheaf).obj K).obj E ≅
      ((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Y.sheaf).obj K).obj E :=
    RingedSite.derivedTensorObjIso (Stacks.SheafOfModules.ringedSite Y.sheaf) K E
  exact (RingedSpace.isPseudoCoherent_derivedTensorProduct Y.toRingedSpace
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _) K E hK hE).of_iso e.symm

end AlgebraicGeometry

namespace AlgebraicGeometry.GrothendieckExistence

attribute [local instance] HasDerivedCategory.standard

variable (F : ℕᵒᵖ ⥤ CommRingCat.{u}) (X : Over (limitBase F))

/-- The structure morphism `X_n ⟶ Spec A_n` of the base change at level `n`, the second
projection of the fibre product. -/
public abbrev levelStructure (n : ℕ) : schemeAt F X n ⟶ baseAt F n :=
  pullback.snd X.hom (baseProjection F n)

namespace DerivedExistenceSituation

variable (S : DerivedExistenceSituation.{u})
  (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X.left.toRingedSpace)))

/-- `E_n = E|_{X_n}`, the derived pullback of an object of `D(𝒪_X)` to the base change at level
`n`. -/
public abbrev levelPullback (n : ℕ) :
    DerivedCategory
      (SheafOfModules.{u} (structureSheafRing (schemeAt S.system S.X n).toRingedSpace)) :=
  (derivedPullback (schemeProjection S.system S.X n).toLRSHom.toShHom).obj E

/-- `K_n ⊗^L E_n`, the derived tensor product at level `n`. -/
public abbrev levelTensor (n : ℕ) :
    DerivedCategory
      (SheafOfModules.{u} (structureSheafRing (schemeAt S.system S.X n).toRingedSpace)) :=
  ((LerayOver.tensor (schemeAt S.system S.X n)).obj (S.K n)).obj (S.levelPullback E n)

/-- `M_n = RΓ(X_n, K_n ⊗^L E_n)`, an object of `D(A_n)`. -/
public abbrev levelCohomology (n : ℕ) : DerivedCategory (ModuleCat.{u} (S.system.obj (op n))) :=
  (derivedGlobalSectionsOver (levelStructure S.system S.X n)).obj (S.levelTensor E n)

/-- `K_n ⊗^L E_n` is pseudo-coherent when `E` is: the derived pullback of a pseudo-coherent object
is pseudo-coherent ([Stacks, Tag 09U7]) and so is a derived tensor product of two of them
([Stacks, Tag 09J3]). -/
theorem isPseudoCoherent_levelTensor
    (hE : RingedSpace.IsPseudoCoherent (X := S.X.left.toRingedSpace) E) (n : ℕ) :
    RingedSpace.IsPseudoCoherent (X := (schemeAt S.system S.X n).toRingedSpace)
      (S.levelTensor E n) :=
  RingedSpace.isPseudoCoherent_derivedTensorProduct (schemeAt S.system S.X n).toRingedSpace
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _) (S.K n)
    (S.levelPullback E n) (S.pseudoCoherent n)
    (Scheme.Hom.isPseudoCoherent_derivedPullback _ E hE)

/-- **`M_n` is pseudo-coherent.** In Situation [Stacks, Tag 0DIB], for a pseudo-coherent (for
instance perfect) `E` in `D(𝒪_X)`, the object `M_n = RΓ(X_n, K_n ⊗^L E|_{X_n})` of `D(A_n)` is
pseudo-coherent: `X_n ⟶ Spec A_n` is flat, proper and of finite presentation, being a base change
of `X ⟶ Spec A`, so [Stacks, Tag 0CSD] applies to the pseudo-coherent `K_n ⊗^L E_n`. -/
theorem isPseudoCoherent_levelCohomology
    (hE : RingedSpace.IsPseudoCoherent (X := S.X.left.toRingedSpace) E) (n : ℕ) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent (S.levelCohomology E n) := by
  have := S.proper
  have := S.flat
  have : LocallyOfFinitePresentation S.X.hom := S.finitePresentation.1
  exact isPseudoCoherent_derivedGlobalSectionsOver_of_flat_of_isProper
    (levelStructure S.system S.X n) (S.levelTensor E n) (S.isPseudoCoherent_levelTensor E hE n)

end DerivedExistenceSituation

end AlgebraicGeometry.GrothendieckExistence

end
