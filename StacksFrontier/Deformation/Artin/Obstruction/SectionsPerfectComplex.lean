module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsUniversalModel
public import StacksFrontier.Deformation.Artin.Obstruction.DualSituation
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsExample
public import StacksFrontier.Homology.TensorComplex.BifunctorSingleLeftComplex

/-!
# The obstruction theory of the functor of sections of a proper flat coherent module

Let `Λ` be Noetherian, let `W → Spec Λ` be proper and let `𝓕` be a coherent `𝒪_W`-module flat
over `Λ`. Then a single finite complex `N` of finite projective `Λ`-modules computes the
cohomology of `𝓕` after every base change, and the obstruction modules
`𝒪(M) = H¹(N ⊗_Λ M)` of the functor of sections are the degree-two cohomology of the derived
tensor product with the shifted complex `K = (N ⊗_Λ A)[-1]`.

## Main definitions

* `Deformation.Artin.SectionsPerfectComplex.shiftedBaseChange`: the complex
  `K = (N ⊗_Λ A)[-1]` of `A`-modules.
* `Deformation.Artin.SectionsPerfectComplex.tensorComplex`: `M ⊗_A -` applied degreewise to a
  complex of `A`-modules.

## Main results

* `Deformation.Artin.SectionsPerfectComplex.tensorComplexXLinearEquiv`: in degree `i` the
  complex `M ⊗_A (N ⊗_Λ A)` is `M ⊗_Λ Nⁱ`, so its cohomology is the source's `H¹(N ⊗_Λ M)`.
* `Deformation.Artin.SectionsPerfectComplex.nonempty_derivedTensorProduct_single_iso`: for a
  K-flat complex `G` of `A`-modules the derived tensor product `M ⊗^𝐋_A G` is the degreewise
  tensor product `M ⊗_A G`.
* `Deformation.Artin.SectionsPerfectComplex.nonempty_derivedCohomology_shift_iso`: for a
  bounded above complex `P` of flat `A`-modules and `K = P[-1]`,
  `H^{i+1}(K ⊗^𝐋_A M) ≅ Hⁱ(P ⊗_A M)`; this is the degree shift of the source.
* The complex `N` of the source together with both descriptions of the obstruction modules is
  `Deformation.Artin.SectionsObstructionModel.exists_finiteProjectiveModel_homology_iso_obstruction`
  in a later file, which derives it from the results here.

## Implementation notes

The derived tensor product is the one of the surrounding development,
`CochainComplex.DerivedTensor.derivedTensorProduct`, read through
`Deformation.Artin.derivedCohomology`, which is the functor
`M ↦ Hⁿ(M[0] ⊗^𝐋_A K)` appearing in the data of a dual deformation situation. That functor is
built from a K-flat resolution of a representative of `K`; since `K = (N ⊗_Λ A)[-1]` is itself
bounded above with flat — indeed finite projective — terms, it is its own K-flat resolution, and
the derived tensor product is computed by the degreewise one. This is what makes the degree shift
visible: `Tot(M[0] ⊗ K)` is `M ⊗_A K` degreewise, and shifting a complex by `-1` shifts its
cohomology by one degree.

The complex `N` is existentially quantified, exactly as in the source: the source obtains it from
[Stacks, Tag 07VL], which produces it from a perfect model of `RΓ(W, 𝓕)`, and the assertion of
this example is a property of any such `N`. No choice is made here to produce data; the
constructions `shiftedBaseChange` and `tensorComplex` take `N` as an argument.

Only the second description of the obstruction modules — the degree-two reformulation — is
proved; the identification of `H¹(W_A, 𝓕_A ⊗_A M)` with `H¹(N ⊗_Λ M)` for a general `A`-module
`M` is not, since cohomology and base change is available here only along ring maps and not with
module coefficients. The attributes record that narrowing.

No hypothesis on the affine-base case of [Stacks, Tag 02O5] is needed: [Stacks, Tag 07VL]
(`Stacks.AlgebraicGeometry.ProperFlatGlobalSections.exists_finiteProjectiveModel_homology_iso`)
is unconditional, having discharged it against the hypothesis-free
`AlgebraicGeometry.ProperCoherenceWitness.higherDirectImageIsCoherentOverAffineBase`, and the
unconditional statement of [Stacks, Tag 07YW] is
`Deformation.Artin.SectionsObstructionModel.exists_finiteProjectiveModel_homology_iso_obstruction`.

## References

* [Stacks Project, Tag 07YW](https://stacks.math.columbia.edu/tag/07YW)
* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 07VL](https://stacks.math.columbia.edu/tag/07VL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open TensorProduct

universe u

namespace Deformation.Artin.SectionsPerfectComplex

attribute [local instance 10000] HasDerivedCategory.standard

section Algebra

variable {A : Type u} [CommRing A]

/-- **`M ⊗_A -` applied degreewise to a complex of `A`-modules.** This is the complex written
`N ⊗_Λ M` in [Stacks, Tag 07YW] once `N` has been base changed to `A`. -/
public abbrev tensorComplex (M : ModuleCat.{u} A) :
    CochainComplex (ModuleCat.{u} A) ℤ ⥤ CochainComplex (ModuleCat.{u} A) ℤ :=
  ((curriedTensor (ModuleCat.{u} A)).obj M).mapHomologicalComplex (ComplexShape.up ℤ)

/-- **The shifted base change `K = (N ⊗_Λ A)[-1]` of [Stacks, Tag 07YW].** The termwise
extension of scalars of `N` along `φ : Λ → A`, shifted by `-1`. -/
public def shiftedBaseChange {Λ : Type u} [CommRing Λ] (φ : Λ →+* A)
    (N : CochainComplex (ModuleCat.{u} Λ) ℤ) : CochainComplex (ModuleCat.{u} A) ℤ :=
  (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) (-1 : ℤ)).obj
    (Stacks.AlgebraicGeometry.ProperFlatGlobalSections.extendScalarsComplex φ N)

/-- **In degree `i` the complex `M ⊗_A (N ⊗_Λ A)` is `M ⊗_Λ Nⁱ`.** So the cohomology of the
degreewise tensor product of `M` with the base change of `N` is the source's `Hⁱ(N ⊗_Λ M)`. This
is the cancellation of base change already used for the obstruction modules themselves, see
`Deformation.Artin.SectionsExample.baseChangeTensorEquiv`. -/
public def tensorComplexXLinearEquiv {Λ : Type u} [CommRing Λ] [Algebra Λ A]
    (N : CochainComplex (ModuleCat.{u} Λ) ℤ) (M : Type u) [AddCommGroup M] [Module A M]
    [Module Λ M] [IsScalarTower Λ A M] (i : ℤ) :
    M ⊗[A] (A ⊗[Λ] (N.X i : Type u)) ≃ₗ[A] M ⊗[Λ] (N.X i : Type u) :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange Λ A A M (N.X i)

/-- **The derived tensor product with a K-flat complex is the degreewise tensor product.** For a
K-flat complex `G` of `A`-modules and an `A`-module `M`, the object `M[0] ⊗^𝐋_A G` of `D(A)` is
represented by the complex `M ⊗_A G` formed degreewise. The derived tensor product is built from
a K-flat resolution of a representative of `G`; `G` is its own, and the total complex of
`M[0] ⊗ G` is the degreewise tensor product because `M[0]` is concentrated in degree zero. -/
public theorem nonempty_derivedTensorProduct_single_iso
    (G : CochainComplex (ModuleCat.{u} A) ℤ) (hG : CochainComplex.KFlat.{u, u} G)
    (M : ModuleCat.{u} A) :
    Nonempty ((CochainComplex.DerivedTensor.derivedTensorProduct.{u, u, _}
          (DerivedCategory.Q.obj G)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M) ≅
      DerivedCategory.Q.obj ((tensorComplex M).obj G)) := by
  obtain ⟨α⟩ :=
    (CochainComplex.DerivedTensor.derivedTensorProduct_iso_lift_of_kFlat_resolution.{u, u, _}
      (DerivedCategory.Q.obj G) G G (𝟙 G) hG
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app G)).1
  refine ⟨?_⟩
  refine (CochainComplex.DerivedTensor.derivedTensorProduct.{u, u, _}
      (DerivedCategory.Q.obj G)).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app M ≪≫
        ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app _).symm) ≪≫ ?_
  refine α.app _ ≪≫ (DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app _ ≪≫ ?_
  exact DerivedCategory.Q.mapIso
    (HomologicalComplex.mapBifunctorSingleLeftIso (curriedTensor (ModuleCat.{u} A)) M G)

/-- **The degree shift of [Stacks, Tag 07YW].** Let `P` be a complex of `A`-modules which is
bounded above and flat in every degree, and let `K = P[-1]`. Then for every `A`-module `M` and
every degree `i`,

`H^{i+1}(K ⊗^𝐋_A M) ≅ Hⁱ(P ⊗_A M)`.

Taking `i = 1` and `P = N ⊗_Λ A`, with `N` the finite complex of finite projective `Λ`-modules
of [Stacks, Tag 07VL], this is the source's passage from `𝒪(M) = H¹(N ⊗_Λ M)` to
`𝒪(M) = H²(K ⊗^𝐋_A M)`. Flatness of the terms is what makes the derived tensor product the
degreewise one; projective terms, as in the source, are flat. -/
public theorem nonempty_derivedCohomology_shift_iso (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (b : ℤ) [P.IsStrictlyLE b] (hP : ∀ n : ℤ, Module.Flat A (P.X n)) (M : ModuleCat.{u} A)
    (i : ℤ) :
    Nonempty ((Deformation.Artin.derivedCohomology A
          (DerivedCategory.Q.obj
            ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) (-1 : ℤ)).obj P))
          (i + 1)).obj M ≅
      ((tensorComplex M).obj P).homology i) := by
  have hLE : ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ)
      (-1 : ℤ)).obj P).IsStrictlyLE (b + 1) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    exact P.isZero_of_isStrictlyLE b (j + -1) (by omega)
  have hflat : ∀ n : ℤ, Module.Flat A
      (((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ)
        (-1 : ℤ)).obj P).X n) := fun n => hP (n + -1)
  obtain ⟨e⟩ := nonempty_derivedTensorProduct_single_iso _
    (@CochainComplex.KFlat.kFlat_of_flat.{u, u} A _ _ (b + 1) hLE hflat) M
  refine ⟨?_⟩
  refine (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (i + 1)).mapIso e ≪≫ ?_
  refine (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) (i + 1)).app _ ≪≫ ?_
  refine (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ)
      (i + 1)).mapIso (((tensorComplex M).commShiftIso (-1 : ℤ)).app P) ≪≫ ?_
  exact ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).shiftIso
    (-1 : ℤ) (i + 1) i (by ring)).app ((tensorComplex M).obj P)

/-- **[Stacks, Tag 07YW], the degree shift.** With `K = (N ⊗_Λ A)[-1]` for a bounded above
complex `N` of flat `Λ`-modules, the degree-one cohomology of `N ⊗_Λ M` — the obstruction module
of [Stacks, Tag 07YH] in the form the source reaches through [Stacks, Tag 07VL] — is the
degree-two cohomology of `K ⊗^𝐋_A M`:

`H¹((N ⊗_Λ A) ⊗_A M) ≅ H²(K ⊗^𝐋_A M)`.

In degree `i` the left-hand complex is `M ⊗_Λ Nⁱ` by `tensorComplexXLinearEquiv`, so the
left-hand side is the source's `H¹(N ⊗_Λ M)`. -/
@[stacks 07YW "the reformulation 𝒪(M) = H²(K ⊗^𝐋_A M) with K = (N ⊗_Λ A)[-1], from the \
  description 𝒪(M) = H¹(N ⊗_Λ M)"]
public theorem nonempty_derivedCohomology_two_iso_homology_one {Λ : Type u} [CommRing Λ]
    (φ : Λ →+* A) (N : CochainComplex (ModuleCat.{u} Λ) ℤ) (b : ℤ) [N.IsStrictlyLE b]
    (hN : ∀ i : ℤ, Module.Flat Λ (N.X i)) (M : ModuleCat.{u} A) :
    Nonempty ((Deformation.Artin.derivedCohomology A
          (DerivedCategory.Q.obj (shiftedBaseChange φ N)) 2).obj M ≅
      ((tensorComplex M).obj
        (Stacks.AlgebraicGeometry.ProperFlatGlobalSections.extendScalarsComplex φ N)).homology
          1) := by
  have hLE : (Stacks.AlgebraicGeometry.ProperFlatGlobalSections.extendScalarsComplex φ
      N).IsStrictlyLE b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro j hj
    exact (ModuleCat.extendScalars φ).map_isZero (N.isZero_of_isStrictlyLE b j hj)
  have hflat : ∀ n : ℤ, Module.Flat A
      ((Stacks.AlgebraicGeometry.ProperFlatGlobalSections.extendScalarsComplex φ N).X n) := by
    intro n
    let _ : Algebra Λ A := φ.toAlgebra
    have := hN n
    change Module.Flat A (TensorProduct Λ A (N.X n : Type u))
    infer_instance
  exact nonempty_derivedCohomology_shift_iso
    (Stacks.AlgebraicGeometry.ProperFlatGlobalSections.extendScalarsComplex φ N) b hflat M 1

end Algebra

section Geometry

open Stacks.AlgebraicGeometry.ProperFlatGlobalSections

variable {Λ : Type u} [CommRing Λ] {W : Scheme.{u}} (g : W ⟶ Spec (.of Λ)) (F : W.Modules)

end Geometry

end Deformation.Artin.SectionsPerfectComplex

end
