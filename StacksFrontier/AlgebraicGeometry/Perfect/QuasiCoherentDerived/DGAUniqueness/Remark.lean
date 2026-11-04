module

public import
  StacksFrontier.AlgebraicGeometry.Perfect.QuasiCoherentDerived.DGAUniqueness.ModelTransport
public import
  StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.DerivedComparisonIso
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleTensorEquivalence

/-!
# Uniqueness of the differential graded algebra of Tag 09M5 (Tag 09SU)

Let `X` be a quasi-compact and quasi-separated scheme over a ring `R`. The construction of the
proof of Tag 09M5 produces, for a K-injective complex `K` of `𝒪_X`-modules representing a perfect
generator of `D_QCoh(𝒪_X)`, the differential graded `R`-algebra `A = Hom_{Comp^dg(𝒪_X)}(K, K)`
and an `R`-linear exact equivalence `D_QCoh(𝒪_X) ≌ D(A, d)`. For a second such complex `L`, with
`B = Hom_{Comp^dg(𝒪_X)}(L, L)`, the Hom complexes `Ω = Hom(K, L)` and `Ω' = Hom(L, K)` are a
differential graded `(B, A)`-bimodule and an `(A, B)`-bimodule, i.e. (Tag 0FQJ) differential
graded modules over `B^{opp} ⊗_R A` and `A^{opp} ⊗_R B`, and the composite equivalence

`D(A, d) → D_QCoh(𝒪_X) → D(B, d)`

is `- ⊗_A^𝐋 Ω'`, with quasi-inverse `- ⊗_B^𝐋 Ω`: the situation of Tag 09ST.

The identification of the composite rests on the comparison
`θ : (- ⊗_A^𝐋 Ω') ⊗_B^𝐋 L ⟶ - ⊗_A^𝐋 K` of
`AlgebraicGeometry.RingedSite.tensorHomComparisonDerived`, an isomorphism by
`AlgebraicGeometry.RingedSite.isIso_tensorHomComparisonDerived`.

## Main results

* `AlgebraicGeometry.dgaModelEquivalence_functor_comp_inverseIso`: at the standard model,
  `(- ⊗_A^𝐋 K) ⋙ (- ⊗_B^𝐋 L)⁻¹ ≅ - ⊗_A^𝐋 Ω'`.
* `AlgebraicGeometry.dgaModelEquivalenceAt_inverse_comp_functorIso`: the same at every model.
* `AlgebraicGeometry.exists_dga_quasiCoherentDerived_linearEquivalence_and_derivedTensor_iso`:
  Tag 09SU.

## References

* [Stacks Project, Tag 09SU](https://stacks.math.columbia.edu/tag/09SU)
* [Stacks Project, Tag 09ST](https://stacks.math.columbia.edu/tag/09ST)
* [Stacks Project, Tag 09M5](https://stacks.math.columbia.edu/tag/09M5)
* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Duality.CompactBoundedness StacksDraft.DerivedModel

universe u w

namespace AlgebraicGeometry

/-- The scheme read as a ringed site. -/
local notation "𝒮" X => Stacks.AlgebraicGeometry.ReflexiveModules.schemeRingedSite X

attribute [local instance] modulesLinearOfSite

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

section Comparison

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  (R : Type u) [CommRing R] [Linear R (RingedSite.TensorModO.{u, u, u, u, u} (𝒮 X))]
  [RingedSite.ScalarSections.{u, u, u, u, u, u} (𝒮 X) R]
  {K L : CochainComplex (RingedSite.ModO.{u, u, u, u} (𝒮 X)) ℤ}
  (hK : IsPerfectGeneratorRepresentative X K) (hL : IsPerfectGeneratorRepresentative X L)

include hK hL in
/-- For two complexes `K`, `L` of the construction of Tag 09M5, the comparison
`θ : (- ⊗_A^𝐋 Hom(L, K)) ⊗_B^𝐋 L ⟶ - ⊗_A^𝐋 K` is an isomorphism. -/
theorem isIso_tensorHomComparisonDerived_of_isPerfectGeneratorRepresentative :
    IsIso (RingedSite.tensorHomComparisonDerived (𝒮 X) R K L) := by
  have := hK.isKInjective
  have := hL.isKInjective
  have := RingedSite.tensorWithComplexDerived_lift_isEquivalence_of_isCompactGeneratorOver.{u, u,
    u, u, u, u} (𝒮 X) R L (qcohDerivedProperty X) (hL.tensor_mem R) qcohDerivedProperty_sum hL.mem
    hL.isCompactObject hL.generates
  exact RingedSite.isIso_tensorHomComparisonDerived (𝒮 X) R K L (qcohDerivedProperty X)
    (hK.tensor_mem R) (hL.tensor_mem R)

/-- `θ`, read in `D_QCoh(𝒪_X)`: `(- ⊗_A^𝐋 Hom(L, K)) ⋙ (- ⊗_B^𝐋 L) ≅ - ⊗_A^𝐋 K`, as functors to
`D_QCoh(𝒪_X)`. -/
def derivedTensorHom_comp_dgaModelEquivalenceIso :
    RingedSite.derivedTensorHom (𝒮 X) R K L ⋙ (dgaModelEquivalence R hL).functor ≅
      (dgaModelEquivalence R hK).functor :=
  ((qcohDerivedProperty X).fullyFaithfulι.whiskeringRight _).preimageIso
    (@asIso _ _ _ _ (RingedSite.tensorHomComparisonDerived (𝒮 X) R K L)
      (isIso_tensorHomComparisonDerived_of_isPerfectGeneratorRepresentative R hK hL))

/-- **The composite `D(A, d) → D_QCoh(𝒪_X) → D(B, d)` is `- ⊗_A^𝐋 Hom(L, K)`**, at the standard
model of `D(𝒪_X)`. -/
def dgaModelEquivalence_functor_comp_inverseIso :
    (dgaModelEquivalence R hK).functor ⋙ (dgaModelEquivalence R hL).inverse ≅
      RingedSite.derivedTensorHom (𝒮 X) R K L :=
  Functor.isoWhiskerRight (derivedTensorHom_comp_dgaModelEquivalenceIso R hK hL).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (dgaModelEquivalence R hL).unitIso.symm ≪≫ Functor.rightUnitor _

/-- **The composite `D(A, d) → D_QCoh(𝒪_X) → D(B, d)` is `- ⊗_A^𝐋 Hom(L, K)`**, at every model
`h` of `D(𝒪_X)`. -/
def dgaModelEquivalenceAt_inverse_comp_functorIso (h : HasDerivedCategory.{w} X.Modules) :
    (dgaModelEquivalenceAt R hK h).inverse ⋙ (dgaModelEquivalenceAt R hL h).functor ≅
      RingedSite.derivedTensorHom (𝒮 X) R K L :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (dgaModelEquivalence R hK).functor
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (qcohModelEquiv X h).unitIso.symm _ ≪≫
        Functor.leftUnitor _) ≪≫
    dgaModelEquivalence_functor_comp_inverseIso R hK hL

end Comparison

/-- **Stacks 09SU** (uniqueness of the differential graded algebra). *Let `X` be a quasi-compact
and quasi-separated scheme over a ring `R`. By the construction of the proof of Tag 09M5 there
exists a differential graded algebra `(A, d)` over `R` such that `D_QCoh(X)` is `R`-linearly
equivalent to `D(A, d)` as a triangulated category. If `(B, d)` is a second such pair, then
`(A, d) = Hom_{Comp^dg(𝒪_X)}(K, K)` and `(B, d) = Hom_{Comp^dg(𝒪_X)}(L, L)` for K-injective
complexes `K`, `L` of `𝒪_X`-modules corresponding to perfect generators of `D_QCoh(𝒪_X)`; with
`Ω = Hom(K, L)` and `Ω' = Hom(L, K)`, `Ω` is a differential graded `B^{opp} ⊗_R A`-module and `Ω'`
a differential graded `A^{opp} ⊗_R B`-module, and the equivalence
`D(A, d) → D_QCoh(𝒪_X) → D(B, d)` is given by `- ⊗_A^𝐋 Ω'`, and similarly its quasi-inverse by
`- ⊗_B^𝐋 Ω`.*

The scheme is over `R` through `f : X ⟶ Spec R`, which makes `𝒪_X`-modules `R`-linear
(`AlgebraicGeometry.overRingLinear`). `D_QCoh(X)` is taken at an arbitrary model `h` of the derived
category of `𝒪_X`-modules. The pairs of the construction are indexed by the complexes `K` with
`IsPerfectGeneratorRepresentative X K` (K-injective, perfect, generating `D_QCoh(𝒪_X)`): the
algebra is `A = Hom_{Comp^dg(𝒪_X)}(K, K)` (`RingedSite.Rep … K`'s algebra, a differential graded
`R`-algebra) and the equivalence is `AlgebraicGeometry.dgaModelEquivalenceAt`, the quasi-inverse
of `- ⊗_A^𝐋 K`.

1. Such a `K` exists, and the equivalence `D_QCoh(X) ≌ D(A, d)` is `R`-linear and exact.
2. For two of them `K`, `L`, `Ω' = Hom(L, K)` is the differential graded `(A, B)`-bimodule
   `RingedSite.homBimodule … K L` — its right `B`-module is the Hom complex of Tag 09LE, and
   `a ∈ A` acts by postcomposition — and, through Tag 0FQJ, comes from a differential graded
   `A^{opp} ⊗_R B`-module; symmetrically for `Ω = Hom(K, L)`, a `(B, A)`-bimodule coming from a
   `B^{opp} ⊗_R A`-module.
3. The composite equivalence `D(A, d) ≌ D_QCoh(X) ≌ D(B, d)` has functor isomorphic to
   `- ⊗_A^𝐋 Ω'` and quasi-inverse isomorphic to `- ⊗_B^𝐋 Ω`. -/
@[stacks 09SU]
theorem exists_dga_quasiCoherentDerived_linearEquivalence_and_derivedTensor_iso
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] {R : CommRingCat.{u}}
    (f : X ⟶ Spec R) [h : HasDerivedCategory.{w} X.Modules] :
    letI := overRingLinear f
    letI := overRingScalarSections f
    (∃ K : CochainComplex (RingedSite.ModO.{u, u, u, u} (𝒮 X)) ℤ,
      ∃ hK : IsPerfectGeneratorRepresentative X K,
        (dgaModelEquivalenceAt R hK h).functor.Linear R ∧
          ∃ _ : (dgaModelEquivalenceAt R hK h).functor.CommShift ℤ,
            (dgaModelEquivalenceAt R hK h).functor.IsTriangulated) ∧
    ∀ (K L : CochainComplex (RingedSite.ModO.{u, u, u, u} (𝒮 X)) ℤ)
      (hK : IsPerfectGeneratorRepresentative X K) (hL : IsPerfectGeneratorRepresentative X L),
      -- `Ω' = Hom(L, K)`: an `(A, B)`-bimodule, by pre- and postcomposition
      (RingedSite.homBimodule (𝒮 X) R K L).rightModule =
          (RingedSite.Rep.{u, u, u, u, u, u} (𝒮 X) R L).functor.obj
            (RingedSite.liftComplex.{u, u, u, u, u} (𝒮 X) K) ∧
        (∀ (n : ℤ) (a : (RingedSite.Rep.{u, u, u, u, u, u} (𝒮 X) R K).algebra.grading n),
          (RingedSite.homBimodule (𝒮 X) R K L).leftAction.1.action n a =
            DifferentialGradedModule.homogeneousMapToCochain _
              ((RingedSite.Rep.{u, u, u, u, u, u} (𝒮 X) R L).functor.map
                ((RingedSite.Rep.{u, u, u, u, u, u} (𝒮 X) R K).algebraHom n a))) ∧
        -- `Ω' = Hom(L, K)`: a differential graded `A^{opp} ⊗_R B`-module (Tag 0FQJ)
        (∃ N : DifferentialGradedModule.{u, u, u} (DifferentialGraded.Bimodule.tensorAlgebra
            (RingedSite.Rep.{u, u, u, u, u, u} (𝒮 X) R K).algebra
            (RingedSite.Rep.{u, u, u, u, u, u} (𝒮 X) R L).algebra),
          Nonempty ((DifferentialGraded.Bimodule.tensorEquivalence _ _).equivalence.inverse.obj N ≅
            RingedSite.homBimodule (𝒮 X) R K L)) ∧
        -- `Ω = Hom(K, L)`: a `(B, A)`-bimodule, by pre- and postcomposition
        (RingedSite.homBimodule (𝒮 X) R L K).rightModule =
          (RingedSite.Rep.{u, u, u, u, u, u} (𝒮 X) R K).functor.obj
            (RingedSite.liftComplex.{u, u, u, u, u} (𝒮 X) L) ∧
        (∀ (n : ℤ) (b : (RingedSite.Rep.{u, u, u, u, u, u} (𝒮 X) R L).algebra.grading n),
          (RingedSite.homBimodule (𝒮 X) R L K).leftAction.1.action n b =
            DifferentialGradedModule.homogeneousMapToCochain _
              ((RingedSite.Rep.{u, u, u, u, u, u} (𝒮 X) R K).functor.map
                ((RingedSite.Rep.{u, u, u, u, u, u} (𝒮 X) R L).algebraHom n b))) ∧
        -- `Ω = Hom(K, L)`: a differential graded `B^{opp} ⊗_R A`-module (Tag 0FQJ)
        (∃ N : DifferentialGradedModule.{u, u, u} (DifferentialGraded.Bimodule.tensorAlgebra
            (RingedSite.Rep.{u, u, u, u, u, u} (𝒮 X) R L).algebra
            (RingedSite.Rep.{u, u, u, u, u, u} (𝒮 X) R K).algebra),
          Nonempty ((DifferentialGraded.Bimodule.tensorEquivalence _ _).equivalence.inverse.obj N ≅
            RingedSite.homBimodule (𝒮 X) R L K)) ∧
        -- the composite `D(A, d) ≌ D_QCoh(X) ≌ D(B, d)` is `- ⊗_A^𝐋 Ω'`, with quasi-inverse
        -- `- ⊗_B^𝐋 Ω`
        Nonempty (((dgaModelEquivalenceAt R hK h).symm.trans
            (dgaModelEquivalenceAt R hL h)).functor ≅
          RingedSite.derivedTensorHom (𝒮 X) R K L) ∧
        Nonempty (((dgaModelEquivalenceAt R hK h).symm.trans
            (dgaModelEquivalenceAt R hL h)).inverse ≅
          RingedSite.derivedTensorHom (𝒮 X) R L K) := by
  let := overRingLinear f
  let := overRingScalarSections f
  refine ⟨?_, fun K L hK hL => ⟨rfl, fun n a => rfl,
    ⟨_, ⟨((DifferentialGraded.Bimodule.tensorEquivalence _ _).equivalence.unitIso.app _).symm⟩⟩,
    rfl, fun n b => rfl,
    ⟨_, ⟨((DifferentialGraded.Bimodule.tensorEquivalence _ _).equivalence.unitIso.app _).symm⟩⟩,
    ⟨dgaModelEquivalenceAt_inverse_comp_functorIso R hK hL h⟩,
    ⟨dgaModelEquivalenceAt_inverse_comp_functorIso R hL hK h⟩⟩⟩
  obtain ⟨G, hG, hgen⟩ := exists_isPerfect_generator_stdDerived X
  obtain ⟨K, hKinj, ⟨i⟩⟩ := RingedSite.exists_isKInjective_liftComplex_iso (𝒮 X) G
  have hK : IsPerfectGeneratorRepresentative X K :=
    { isKInjective := hKinj
      isPerfect := @Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1}
        X.toRingedSpace (HasDerivedCategory.standard _) _ _ i.symm hG
      generates := by
        intro M hM hz
        refine hgen M hM (fun n g => ?_)
        have h₀ := hz n (((CategoryTheory.shiftFunctor _ n).mapIso i).hom ≫ g)
        rw [← Iso.inv_hom_id_assoc ((CategoryTheory.shiftFunctor _ n).mapIso i) g, h₀,
          comp_zero] }
  exact ⟨K, hK, inferInstance, dgaModelEquivalenceAt_isTriangulated R hK h⟩

end AlgebraicGeometry

end
