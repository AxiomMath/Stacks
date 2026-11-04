module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.DegreeZeroPureTensor
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.SituationComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TensorProduct
import StacksCore.Tactic.StacksAttribute

/-!
# The complex of [Stacks, Tag 0G0A] in Situation [Stacks, Tag 0G08]

`AlgebraicGeometry.exists_transformedDiagonalComplex` is (0G0A) at exactly the hypotheses of
Situation [Stacks, Tag 0G08], with no other hypothesis: it is
`AlgebraicGeometry.exists_kunnethComplex_of_imagePairingStd` with its one input, the Künneth
identification on `X ×_k Y`, supplied by
`AlgebraicGeometry.DiagonalResolution.isTensorPairing_transformedImagePairingStd`, together with
the perfectness of the terms `ℰᵢ ⊠ F(𝒢ᵢ)`, so that the complex lies in `D_perf(𝒪_{X ×_k Y})`.

That perfectness is [Stacks, Tag 09UA] and [Stacks, Tag 09J5], which the library states at the
standard model of the derived category; the terms are at the locally small one, so the two
factors are moved to the standard model (`StacksDraft.DerivedModel.isPerfect_inverse_obj`), the
external tensor product is taken there, and the result is brought back along
`AlgebraicGeometry.derivedExternalTensorModelIso`.

## Main results

* `AlgebraicGeometry.isPerfect_derivedExternalTensor`: the derived external tensor product of two
  perfect objects is perfect.
* `AlgebraicGeometry.exists_transformedDiagonalComplex`: **[Stacks, Tag 0G0A]**.

## References

* [Stacks Project, Tag 0G08](https://stacks.math.columbia.edu/tag/0G08)
* [Stacks Project, Tag 0G0A](https://stacks.math.columbia.edu/tag/0G0A)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Cohomology.PerfectComplexes

universe u

namespace AlgebraicGeometry

attribute [local instance] CategoryTheory.Linear.fullSubcategory
attribute [local instance] isTriangulated_isPerfect_locallySmall

/-! ### Perfectness of the derived external tensor product -/

section Perfect

open StacksDraft.DerivedModel

/-- **Perfectness passes from the standard model to the locally small one**, the converse of
`StacksDraft.DerivedModel.isPerfect_inverse_obj`: the comparison matches the two localization
functors on the nose. -/
theorem isPerfect_comparisonFunctor_obj {V : Scheme.{u}}
    (K : @DerivedCategory V.Modules _ _ (HasDerivedCategory.standard _))
    (hK : @IsPerfect V.toRingedSpace (HasDerivedCategory.standard _) K) :
    IsPerfect (X := V.toRingedSpace) ((schemeModulesComparison V).functor.obj K) := by
  obtain ⟨E, hE, ⟨e⟩⟩ := hK
  exact ⟨E, hE, ⟨(schemeModulesComparison V).functor.mapIso e⟩⟩

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

section Standard

attribute [local instance 100000] HasDerivedCategory.standard

attribute [local implicit_reducible] structureSheafRing StrictlyPerfect.structureSheafOfRings

/-- **At the standard model, the derived external tensor product of two perfect objects is
perfect**: [Stacks, Tag 09UA] for the two derived pullbacks and [Stacks, Tag 09J5] for the derived
tensor product. -/
theorem isPerfect_derivedExternalTensorStd (K : DerivedCategory X.Modules)
    (L : DerivedCategory Y.Modules) (hK : IsPerfect (X := X.toRingedSpace) K)
    (hL : IsPerfect (X := Y.toRingedSpace) L) :
    IsPerfect (X := (pullback f g).toRingedSpace) (derivedExternalTensorStd f g K L) :=
  RingedSpace.isPerfect_canonicalDerivedTensorProduct (pullback f g).toRingedSpace _ _
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
      (pullback.fst f g).toLRSHom.toShHom K hK)
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback
      (pullback.snd f g).toLRSHom.toShHom L hL)

end Standard

/-- **The derived external tensor product of two perfect objects is perfect.** Read at the
standard model, where [Stacks, Tag 09UA] and [Stacks, Tag 09J5] are stated, and brought back to
the locally small model along `AlgebraicGeometry.derivedExternalTensorModelIso`. -/
theorem isPerfect_derivedExternalTensor (A : DerivedCategory X.Modules)
    (B : DerivedCategory Y.Modules) (hA : IsPerfect (X := X.toRingedSpace) A)
    (hB : IsPerfect (X := Y.toRingedSpace) B) :
    IsPerfect (X := (pullback f g).toRingedSpace) (derivedExternalTensor f g A B) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    (derivedExternalTensorModelIso f g ((schemeModulesComparison X).inverse.obj A)
        ((schemeModulesComparison Y).inverse.obj B) ≪≫
      ((Stacks.Duality.derivedTensor (pullback f g)).mapIso
          ((Stacks.Duality.derivedPullback (pullback.fst f g)).mapIso
            ((schemeModulesComparison X).counitIso.app A))).app _ ≪≫
      ((Stacks.Duality.derivedTensor (pullback f g)).obj _).mapIso
        ((Stacks.Duality.derivedPullback (pullback.snd f g)).mapIso
          ((schemeModulesComparison Y).counitIso.app B)))
    (isPerfect_comparisonFunctor_obj _
      (isPerfect_derivedExternalTensorStd f g _ _ (isPerfect_inverse_obj X A hA)
        (isPerfect_inverse_obj Y B hB)))

end Perfect

open DiagonalResolution in
/-- **(0G0A).** For `X`, `Y` proper smooth over a field `k`, `F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)`
`k`-linear exact fully faithful and `R` a resolution of the diagonal by `ℰᵢ ⊠ 𝒢ᵢ`, there is a
complex `… ⟶ ℰ₁ ⊠ F(𝒢₁) ⟶ ℰ₀ ⊠ F(𝒢₀)` in `D_perf(𝒪_{X ×_k Y})` whose differentials are those of
`R` transported by the identification of Hom groups sending `a ⊠ b` to `a ⊠ F(b)`. -/
@[stacks 0G0A]
theorem exists_transformedDiagonalComplex (k : Type u) [Field k]
    (X Y : Over (Spec (.of k))) [Smooth X.hom] [Smooth Y.hom]
    [IsProper X.hom] [IsProper Y.hom] :
    letI : Linear k X.left.Modules := modulesLinear k X
    letI : Linear k Y.left.Modules := modulesLinear k Y
    ∀ (F : perfectDerived X.left ⥤ perfectDerived Y.left) [F.CommShift ℤ] [F.IsTriangulated],
      F.Linear k → Nonempty F.FullyFaithful →
      ∀ (R : DiagonalResolution X.hom),
        ∃ T : ImageHomTransport R Y.hom F,
          (∀ i, T.complex.X i = R.imageTerm Y.hom F i) ∧
          (∀ i, IsPerfect (X := (pullback X.hom Y.hom).toRingedSpace) (T.complex.X i)) ∧
          (∀ i, T.complex.d (i + 1) i = T.hom (i + 1) i (R.boxDifferential i)) ∧
          ∀ (i j : ℕ) (a : R.left i ⟶ R.left j) (b : R.right i ⟶ R.right j),
            T.hom i j (externalTensorProductMap X.hom X.hom a b) =
              R.transformedMap Y.hom F a b := by
  let _ : Linear k X.left.Modules := modulesLinear k X
  let _ : Linear k Y.left.Modules := modulesLinear k Y
  intro F _ _ hlin hff R
  obtain ⟨T, hX, hd, hT⟩ := exists_kunnethComplex_of_imagePairingStd k X Y
    (DiagonalResolution.isTensorPairing_transformedImagePairingStd k X Y) F hlin hff R
  refine ⟨T, hX, fun i => ?_, hd, hT⟩
  rw [hX i]
  exact isPerfect_derivedExternalTensor X.hom Y.hom _ _
    (isPerfect_singleFunctor_of_isFiniteLocallyFree X.left _
      ⟨(R.left_finiteLocallyFree i).exists_isFiniteLocallyFreeData⟩)
    (F.obj ⟨_, R.isPerfect_singleFunctor_right i⟩).property

end AlgebraicGeometry

end
