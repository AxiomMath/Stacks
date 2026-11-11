module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeCohomology.HodgeDuality

/-!
# Nondegeneracy of the contraction pairing against an invertible target

Let `X` be a proper Cohen--Macaulay scheme over a field `k`, equidimensional of dimension `d`,
with dualizing module `ω_X` and trace `t : Hᵈ(X, ω_X) ⟶ k` ([Stacks, Tag 0FVV],
[Stacks, Tag 0FVW]). Let `ℰ` be a finite locally free `𝒪_X`-module and `ℳ` an `𝒪_X`-module with an
isomorphism `ψ : ℳ ≅ ω_X`. Then the contraction cup product

`Hⁱ(X, ℳ ⊗ ℰ^∨) × Hʲ(X, ℰ) ⟶ Hᵈ(X, ℳ),  (ξ, η) ↦ (1 ⊗ ε)(ξ ∪ η)`,  `i + j = d`,

is nondegenerate on both sides: a nonzero class on either side pairs nontrivially with some class
on the other side. This is the pairing of [Stacks, Tag 0FW0] with `ω_X` replaced by `ℳ`.

The case used in [Stacks, Tag 0D1R] is a smooth proper surface with trivial canonical bundle
(a K3 surface): `ℳ = 𝒪_X`, `ℰ = Ω_{X/k}`, so `ℳ ⊗ ℰ^∨ = 𝒪_X ⊗ T_{X/k}` and the pairing is the cup
product `H¹(X, T_{X/k}) × H¹(X, Ω_{X/k}) ⟶ H²(X, 𝒪_X)`, "a nondegenerate pairing by coherent
duality".

## Main results

* `Stacks.Duality.bijective_sheafTensor_map_comp_dualContraction`: morphisms into `ℳ ⊗ ℰ^∨` are
  morphisms out of `- ⊗ ℰ` into `ℳ`, through `1 ⊗ ε`, for `ℰ` finite locally free.
* `Stacks.Duality.isPerfPair_tracePairing_dualContraction_comp`: the pairing
  `(ξ, η) ↦ t(ψ((1 ⊗ ε)(ξ ∪ η)))` is perfect.
* `Stacks.Duality.exists_cupContraction_dualContraction_ne_zero_left` and
  `Stacks.Duality.exists_cupContraction_dualContraction_ne_zero_right`: **nondegeneracy** of the
  `Hᵈ(X, ℳ)`-valued contraction cup product.

## References

* [Stacks Project, Tag 0FW0](https://stacks.math.columbia.edu/tag/0FW0)
* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Stacks.Cohomology.GlobalKunneth (baseRing baseSections)
open Stacks.Cohomology.DerivedGlobalCupProduct

universe u

namespace Stacks.Duality

section SheafLevel

variable {X : Scheme.{u}}

/-- **Morphisms into `ℳ ⊗ ℰ^∨` are morphisms out of `- ⊗ ℰ` into `ℳ`**: for `ℰ` finite locally
free, `g ↦ (g ⊗ 1) ≫ (1 ⊗ ε)` is a bijection `Hom(𝒯, ℳ ⊗ ℰ^∨) ≃ Hom(𝒯 ⊗ ℰ, ℳ)`. It is the
adjunction `- ⊗ ℰ ⊣ - ⊗ ℰ^∨` of the duality of [Stacks, Tag 0FNY], whose counit is `1 ⊗ ε`. -/
theorem bijective_sheafTensor_map_comp_dualContraction (M E : X.Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) (T : X.Modules) :
    Function.Bijective (fun g : T ⟶ tensorModule M (dualModule E) =>
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map g).app E ≫
        dualContraction M E) := by
  rw [dualContraction_eq_counit M E hE]
  exact ((@tensorRightAdjunction (Stacks.SheafOfModules.DerivedMonoidal.Mod X.sheaf) _
    (SheafOfModules.monoidalCategorySheafTensor X.sheaf) E (dualModule E)
    (@HasRightDual.exact _ _ (SheafOfModules.monoidalCategorySheafTensor X.sheaf) E
      (hasRightDualOfFiniteLocallyFree E hE))).homEquiv T M).symm.bijective

end SheafLevel

section Pairing

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- **The pairing `(ξ, η) ↦ t(ψ((1 ⊗ ε)(ξ ∪ η)))` is perfect**, for `ℰ` finite locally free and an
isomorphism `ψ : ℳ ≅ ω_X`: this is [Stacks, Tag 0FW0] with `ω_X` replaced by `ℳ`. -/
theorem isPerfPair_tracePairing_dualContraction_comp (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    {M E : X.Modules} (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E)
    (ψ : M ≅ dualizingModule f) (i j : ℤ) (hij : i + j = d) :
    (tracePairing f hCM hequi d hd (cupProductOnSpace X.toRingedSpace)
      (dualContraction M E ≫ ψ.hom) i j hij).IsPerfPair := by
  refine isPerfPair_tracePairing f (canonicalOnePointComparison X.toRingedSpace) hCM hequi d hd hE
    _ (fun T => ?_) i j hij
  have h := bijective_sheafTensor_map_comp_dualContraction M E hE T
  have hfun : (fun g : T ⟶ tensorModule M (dualModule E) =>
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map g).app E ≫
        (dualContraction M E ≫ ψ.hom)) =
      (fun φ => φ ≫ ψ.hom) ∘ (fun g : T ⟶ tensorModule M (dualModule E) =>
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).map g).app E ≫
          dualContraction M E) := by
    funext g
    exact (Category.assoc _ _ _).symm
  exact (congrArg Function.Bijective hfun).mpr <| (show Function.Bijective
      (fun φ : tensorModule T E ⟶ M => φ ≫ ψ.hom) from
    ⟨fun φ φ' e' => (Iso.cancel_iso_hom_right φ φ' ψ).1 e',
      fun φ => ⟨φ ≫ ψ.inv, (Category.assoc _ _ _).trans
        ((congrArg (φ ≫ ·) ψ.inv_hom_id).trans (Category.comp_id φ))⟩⟩).comp h

/-- The `k`-linear map `Hᵈ(X, ℳ) ⟶ k`: the map on cohomology induced by `ψ : ℳ ≅ ω_X`, then the
trace. -/
def traceOfIso (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    {M : X.Modules} (ψ : M ≅ dualizingModule f) :
    sheafCohomology f M d →ₗ[k] k :=
  letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing X.toRingedSpace))
  letI := HasDerivedCategory.standard (ModuleCat.{u} (baseRing X.toRingedSpace))
  (topTrace f hCM hequi d hd).hom ∘ₗ ((ModuleCat.restrictScalars.{u} (globalRingHom f)).map
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing X.toRingedSpace)) d).map
      ((baseSections X.toRingedSpace).map
        (DerivedCategory.Q.map ((CochainComplex.singleFunctor X.Modules 0).map ψ.hom))))).hom

/-- The perfect pairing of `isPerfPair_tracePairing_dualContraction_comp` is the trace of the
contraction cup product. -/
theorem tracePairing_dualContraction_comp_apply (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    {M E : X.Modules} (ψ : M ≅ dualizingModule f) (i j : ℤ) (hij : i + j = d)
    (ξ : sheafCohomology f (tensorModule M (dualModule E)) i) (η : sheafCohomology f E j) :
    tracePairing f hCM hequi d hd (cupProductOnSpace X.toRingedSpace)
        (dualContraction M E ≫ ψ.hom) i j hij ξ η =
      traceOfIso f hCM hequi d hd ψ
        ((cupContraction (cupProductOnSpace X.toRingedSpace) (dualContraction M E) i j d
          hij).hom (ξ ⊗ₜ η)) := by
  rw [tracePairing_apply, cupContraction_comp]
  rfl

/-- **Nondegeneracy on the right**: for `ℰ` finite locally free and `ℳ ≅ ω_X`, every nonzero
`η ∈ Hʲ(X, ℰ)` has some `ξ ∈ Hⁱ(X, ℳ ⊗ ℰ^∨)`, `i + j = d`, with `(1 ⊗ ε)(ξ ∪ η) ≠ 0` in
`Hᵈ(X, ℳ)`. -/
theorem exists_cupContraction_dualContraction_ne_zero_right
    (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    {M E : X.Modules} (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E)
    (ψ : M ≅ dualizingModule f) (i j : ℤ) (hij : i + j = d) (η : sheafCohomology f E j)
    (hη : η ≠ 0) :
    ∃ ξ : sheafCohomology f (tensorModule M (dualModule E)) i,
      (cupContraction (cupProductOnSpace X.toRingedSpace) (dualContraction M E) i j d
        hij).hom (ξ ⊗ₜ η) ≠ 0 := by
  have hP := isPerfPair_tracePairing_dualContraction_comp f hCM hequi d hd hE ψ i j hij
  obtain ⟨ξ, hξ⟩ : ∃ ξ, tracePairing f hCM hequi d hd (cupProductOnSpace X.toRingedSpace)
      (dualContraction M E ≫ ψ.hom) i j hij ξ η ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hη (hP.bijective_right.1 (LinearMap.ext fun ξ => by
      rw [LinearMap.flip_apply, hall ξ, map_zero, LinearMap.zero_apply]))
  refine ⟨ξ, fun h0 => hξ ?_⟩
  rw [tracePairing_dualContraction_comp_apply]
  exact (congrArg (traceOfIso f hCM hequi d hd ψ) h0).trans
    (map_zero (traceOfIso f hCM hequi d hd ψ))

/-- **Nondegeneracy on the left**: for `ℰ` finite locally free and `ℳ ≅ ω_X`, every nonzero
`ξ ∈ Hⁱ(X, ℳ ⊗ ℰ^∨)` has some `η ∈ Hʲ(X, ℰ)`, `i + j = d`, with `(1 ⊗ ε)(ξ ∪ η) ≠ 0` in
`Hᵈ(X, ℳ)`. -/
theorem exists_cupContraction_dualContraction_ne_zero_left
    (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hequi : TopologicalSpace.Equidimensional X) (d : ℕ) (hd : topologicalKrullDim X = d)
    {M E : X.Modules} (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E)
    (ψ : M ≅ dualizingModule f) (i j : ℤ) (hij : i + j = d)
    (ξ : sheafCohomology f (tensorModule M (dualModule E)) i) (hξ : ξ ≠ 0) :
    ∃ η : sheafCohomology f E j,
      (cupContraction (cupProductOnSpace X.toRingedSpace) (dualContraction M E) i j d
        hij).hom (ξ ⊗ₜ η) ≠ 0 := by
  have hP := isPerfPair_tracePairing_dualContraction_comp f hCM hequi d hd hE ψ i j hij
  obtain ⟨η, hη⟩ : ∃ η, tracePairing f hCM hequi d hd (cupProductOnSpace X.toRingedSpace)
      (dualContraction M E ≫ ψ.hom) i j hij ξ η ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hξ (hP.bijective_left.1 (LinearMap.ext fun η => by
      rw [hall η, map_zero, LinearMap.zero_apply]))
  refine ⟨η, fun h0 => hη ?_⟩
  rw [tracePairing_dualContraction_comp_apply]
  exact (congrArg (traceOfIso f hCM hequi d hd ψ) h0).trans
    (map_zero (traceOfIso f hCM hequi d hd ψ))

end Pairing

section TrivialCanonical

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]

/-- **The tangent–forms pairing on a smooth proper variety with trivial canonical bundle is
nondegenerate.** Let `X` be smooth and proper over a field `k`, equidimensional of dimension `d`,
with `Ω^d_{X/k} ≅ 𝒪_X`. For `i + j = d`, every nonzero `c ∈ Hʲ(X, Ω_{X/k})` has some
`v ∈ Hⁱ(X, 𝒪_X ⊗ T_{X/k})`, `T_{X/k} = Ω_{X/k}^∨`, whose contraction cup product
`(1 ⊗ ε)(v ∪ c) ∈ Hᵈ(X, 𝒪_X)` is nonzero. For a K3 surface (`d = 2`, `i = j = 1`) this is the
nondegeneracy of `H¹(X, T_{X/k}) × H¹(X, Ω_{X/k}) ⟶ H²(X, 𝒪_X)` used in [Stacks, Tag 0D1R]. -/
theorem exists_cupContraction_tangent_ne_zero_of_trivialCanonical [Smooth f] (d : ℕ)
    (hequi : TopologicalSpace.Equidimensional X) (hd : topologicalKrullDim X = d)
    (σ : Scheme.Hom.relativeDifferentialForms f d ≅ SheafOfModules.unit X.ringCatSheaf)
    (i j : ℤ) (hij : i + j = d) (c : sheafCohomology f (Scheme.Hom.relativeDifferentials f) j)
    (hc : c ≠ 0) :
    ∃ v : sheafCohomology f (tensorModule (SheafOfModules.unit X.ringCatSheaf)
        (dualModule (Scheme.Hom.relativeDifferentials f))) i,
      (cupContraction (cupProductOnSpace X.toRingedSpace)
        (dualContraction (SheafOfModules.unit X.ringCatSheaf)
          (Scheme.Hom.relativeDifferentials f)) i j d hij).hom (v ⊗ₜ c) ≠ 0 := by
  have := smoothOfRelativeDimension_of_equidimensional k f hequi d hd
  have hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Scheme.Hom.relativeDifferentials f) :=
    have := Stacks.Discriminant.isFiniteLocallyFreeOfRank_relativeDifferentials f d
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      (Scheme.Hom.relativeDifferentials f) d
  exact exists_cupContraction_dualContraction_ne_zero_right f
    (isCohenMacaulay_of_syntomic_over_field f (syntomic_of_smooth f)) hequi d hd hE
    (σ.symm ≪≫ (nonempty_relativeDualizingComplex_iso_and_relativeDualizingModule_iso_of_smooth
      f d).2.some.symm)
    i j hij c hc

end TrivialCanonical

end Stacks.Duality

end
