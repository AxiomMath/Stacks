module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekLocalCompleteIntersection.Factorization
public import StacksFrontier.AlgebraicGeometry.Duality.SmoothProper.RelativeDualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.StructureSheafPullback
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackBraided
public import StacksFrontier.AlgebraicGeometry.Modules.DerivedTensorShiftedInverse
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic

/-!
# `f^!𝒪_Y` for a Koszul-regular immersion into a smooth proper scheme, at constant ranks

Let `S` be a Noetherian scheme and `f : X ⟶ Y` a morphism of `FTS S` which factors as a
Koszul-regular closed immersion `i : X ⟶ U` whose conormal sheaf has constant rank `c`, the
inclusion of an open `U ⊆ P`, and a proper morphism `g : P ⟶ Y` smooth of relative dimension `d`.
Then, for every compactification computing `f^!`,

`f^!𝒪_Y ≅ (∧^c 𝒩 ⊗ (i ≫ U.ι)^* ∧^d Ω_{P/Y})[d - c]`,

where `𝒩` is the normal sheaf of `i`. This is the computation in the proof of
[Stacks, Tag 0E9Z]: `g^!𝒪_Y = ∧^d Ω_{P/Y}[d]` ([Stacks, Tag 0BRT]), restriction to `U`,
`i^!K = Li^*K ⊗ᴸ i^!𝒪_U` ([Stacks, Tag 0A9U]) and `i^!𝒪_U = ∧^c 𝒩[-c]` ([Stacks, Tag 0BR0]).
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace Stacks.Duality.ClosedOpenProperFactorization

section Determinant

variable {Z P Y : Scheme.{u}} (U : P.Opens) (i : Z ⟶ U.toScheme) (g : P ⟶ Y) (d : ℕ)
  [SmoothOfRelativeDimension d g]

/-- The top exterior power `∧^d Ω_{P/Y}` pulled back to `X`. -/
abbrev pulledBackDeterminant : Z.Modules :=
  (Scheme.Modules.pullback (i ≫ U.ι)).obj
    (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials g) d)

/-- The top exterior power of `Ω_{P/Y}` is invertible. -/
private theorem isFiniteLocallyFreeOfRank_exteriorPower_relativeDifferentials :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (R := P.ringCatSheaf)
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials g) d) 1 := by
  have := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials g d
  have h := Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower
    (Scheme.Hom.relativeDifferentials g) d d
  rwa [Nat.choose_self] at h

/-- The pulled back top exterior power of `Ω_{P/Y}` is invertible. -/
theorem isFiniteLocallyFreeOfRank_pulledBackDeterminant :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (pulledBackDeterminant U i g d) 1 := by
  have := isFiniteLocallyFreeOfRank_exteriorPower_relativeDifferentials g d
  exact AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback (i ≫ U.ι) _ 1

/-- The top exterior power of `Ω_{P/Y}` is flat. -/
theorem isFlat_exteriorPower_relativeDifferentials :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := P.sheaf)
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials g) d) := by
  have h := isFiniteLocallyFreeOfRank_exteriorPower_relativeDifferentials g d
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := P.ringCatSheaf)
      (Scheme.Modules.exteriorPower (Scheme.Hom.relativeDifferentials g) d) :=
    ⟨(AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
      (hM := h)).exists_isFiniteLocallyFreeData⟩
  exact Scheme.Modules.isFlat_of_isFiniteLocallyFree _

end Determinant

variable {S : Scheme.{u}} [IsNoetherian S] {X Y : FTS S} (f : X ⟶ Y)
  {P : Scheme.{u}} (U : P.Opens) (i : X.left ⟶ U.toScheme) (g : P ⟶ Y.left)
  [IsClosedImmersion i] [IsProper g] (hf : i ≫ U.ι ≫ g = f.left)
  (j : CompactificationOf (Over.mk f.left)) (d c : ℕ) [SmoothOfRelativeDimension d g]

variable (hi : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsKoszulRegularImmersion i)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (R := X.left.ringCatSheaf) (Stacks.Conormal.conormalSheaf i) c]

/-- **`f^!𝒪_Y ≅ (∧^c 𝒩 ⊗ (i ≫ U.ι)^* ∧^d Ω_{P/Y})[d - c]`**, for every compactification `j`
computing `f^!`, when `f = i ≫ U.ι ≫ g` with `i` a Koszul-regular closed immersion whose conormal
sheaf has rank `c` and `g` proper and smooth of relative dimension `d`. -/
def upperShriekStructureSheafIso :
    ((upperShriek f j).obj (DerivedPushforward.derivedStructureSheaf Y.left)).obj ≅
      (DerivedCategory.singleFunctor X.left.Modules ((c : ℤ) + -(d : ℤ))).obj
        (Scheme.Modules.tensorObjRingedSpace X.left
          (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf i) c)
          (pulledBackDeterminant U i g d)) :=
  haveI : IsNoetherian P := isNoetherian_of_isProper g
  haveI : IsNoetherian U.toScheme := isNoetherian_of_isOpenImmersion U.ι
  haveI : CompactSpace U.toScheme := QuasiCompact.compactSpace_of_compactSpace U.ι
  haveI : QuasiSeparatedSpace U.toScheme := U.ι.isOpenEmbedding.quasiSeparatedSpace
  haveI : Perfect i := perfect_of_isKoszulRegularImmersion i hi
  haveI : IsProper i := inferInstance
  let hpi := isQuasicoherent_homology_derivedPushforward_of_qcqs i
  let hpg := isQuasicoherent_homology_derivedPushforward_of_qcqs g
  let K := (quasiCoherentDerivedPullback' U.ι).obj
    ((twistedInverseImage g hpg).obj (DerivedPushforward.derivedStructureSheaf Y.left))
  haveI := isIso_twistedInverseImageCompareWithPullback_of_perfect_of_isProper i K
  have hL := isFiniteLocallyFreeOfRank_pulledBackDeterminant U i g d
  let hfree : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u}
      (R := X.left.ringCatSheaf) (pulledBackDeterminant U i g d) :=
    ⟨(AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _ 1
      (hM := hL)).exists_isFiniteLocallyFreeData⟩
  letI := Scheme.Modules.canonicalDerivedMonoidal X.left
  letI : SymmetricCategory (DerivedCategory X.left.Modules) :=
    Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric X.left.sheaf
  let A := (DerivedCategory.singleFunctor X.left.Modules (-(d : ℤ))).obj
    (pulledBackDeterminant U i g d)
  let B := (DerivedCategory.singleFunctor X.left.Modules (c : ℤ)).obj
    (Scheme.Modules.exteriorPower (Stacks.Divisors.normalSheaf i) c)
  let e₁ : ((derivedTensor X.left).obj ((derivedPullback i).obj K.obj)).obj
        ((twistedInverseImage i hpi).obj
          (DerivedPushforward.derivedStructureSheaf U.toScheme)).obj ≅
      ((derivedTensor X.left).obj A).obj B :=
    ((derivedTensor X.left).mapIso
        ((derivedPullbackCompIso i U.ι).app _ ≪≫
          (derivedPullback (i ≫ U.ι)).mapIso
            (singleFunctorExteriorPowerIsoRelativeDualizingComplex g d).symm ≪≫
          derivedPullbackSingleIsoOfIsFlat (i ≫ U.ι) _
            (isFlat_exteriorPower_relativeDifferentials g d) _)).app _ ≪≫
      ((derivedTensor X.left).obj A).mapIso
        (KoszulRegular.twistedInverseImageIsoOfIsKoszulRegularImmersion i hpi hi c).symm
  (ObjectProperty.ι _).mapIso (upperShriekObjIso f i U.ι g hf j
      (DerivedPushforward.derivedStructureSheaf Y.left)
      (KoszulRegular.isBoundedBelow_singleFunctor_obj _)) ≪≫
    ((ObjectProperty.ι _).mapIso (asIso (twistedInverseImageCompareWithPullback i
      hpi
      (quasiCoherentDerivedPullbackTensorIso i).hom
      (quasiCoherentDerivedTensorRightUnitor U.toScheme) K))).symm ≪≫
    e₁ ≪≫ (β_ A B) ≪≫ derivedTensorSingleSingleIso _ _ hfree _ _

end Stacks.Duality.ClosedOpenProperFactorization
