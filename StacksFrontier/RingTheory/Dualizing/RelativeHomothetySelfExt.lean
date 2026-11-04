module

public import StacksFrontier.Algebra.Homology.Resolution.InjectiveResolution
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ExtComparison
public import StacksFrontier.RingTheory.Dualizing.DerivedHomothety.CoextensionHomothety
public import StacksFrontier.RingTheory.Dualizing.FiniteMapDualizing
public import StacksFrontier.RingTheory.Dualizing.RelativeHomothety

/-!
# The derived homothety and the self-extensions of an object

Let `A` be a commutative ring and `K` an object of `D(A)`.  The derived homothety
`A ⟶ RHom_A(K, K)` of `Dualizing.relativeHomothety` is an isomorphism exactly when the scalars
act on `End_{D(A)}(K)` freely of rank one through the identity and `K` has no nonzero morphism to
a nonzero shift of itself, at least when `K` is bounded below.

## Main results

* `Dualizing.bijective_smul_id_of_isIso_relativeHomothety`,
  `Dualizing.subsingleton_shift_of_isIso_relativeHomothety` — the forward implication.
* `Dualizing.isIso_relativeHomothety_of_bijective_smul_id` — the converse for an object bounded
  below.
* `Dualizing.isIso_relativeHomothety_iff_selfExt` — the equivalence.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Dualizing

open StacksDraft.DerivedHom

attribute [local instance] HasDerivedCategory.standard

universe u

noncomputable section

variable (A : Type u) [CommRing A]

/-- Scalars act on the free rank-one module `ULift A` placed in degree zero freely of rank one
through the identity. -/
private theorem bijective_smul_id_single :
    Function.Bijective (fun a : A => a • 𝟙 ((DerivedCategory.singleFunctor
      (ModuleCat.{u} A) 0).obj (ModuleCat.of A (ULift.{0} A)))) := by
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  have h₁ : Function.Bijective (fun a : A => a • 𝟙 (ModuleCat.of A (ULift.{0} A))) := by
    constructor
    · intro a b h
      simpa using congrArg ULift.down (ConcreteCategory.congr_hom h (ULift.up 1))
    · intro f
      refine ⟨(f (ULift.up 1)).down, ModuleCat.hom_ext (LinearMap.ext fun ⟨x⟩ => ?_)⟩
      have hx : (ULift.up x : ULift.{0} A) = x • ULift.up 1 := by ext; simp
      simp only [ModuleCat.hom_smul, ModuleCat.hom_id, LinearMap.smul_apply, LinearMap.id_coe,
        id_eq]
      rw [hx, map_smul]
      ext
      simp [mul_comm]
  have h₂ : Function.Bijective
      (S.map (X := ModuleCat.of A (ULift.{0} A)) (Y := ModuleCat.of A (ULift.{0} A))) :=
    ⟨S.map_injective, S.map_surjective⟩
  convert h₂.comp h₁ using 1
  ext a
  simp [S, Functor.map_smul]

/-- Scalars act on the tensor unit of the adjunction of [stacks 0A63] freely of rank one through
the identity. -/
private theorem bijective_smul_id_derivedTensorUnit :
    Function.Bijective (fun a : A => a • 𝟙 (derivedTensorUnit.{u, 0} A)) := by
  let e := ExtComparison.unitIsoSingle.{u, 0} A
  convert (Iso.homCongr e.symm e.symm).bijective.comp (bijective_smul_id_single A) using 1
  ext a
  simp [Iso.homCongr, Linear.smul_comp, Linear.comp_smul]

/-- The degree-zero identification of [stacks 0A63] sends the derived homothety to the
identity. -/
private theorem homZeroEquivOverRing_relativeHomothety (K : DerivedCategory (ModuleCat.{u} A)) :
    ExtComparison.homZeroEquivOverRing.{u, 0} A K K (relativeHomothety A K) = 𝟙 K := by
  simp [ExtComparison.homZeroEquivOverRing, relativeHomothety, derivedHomothety]

/-- **Scalars act on `End_{D(A)}(K)` freely of rank one through the identity** as soon as the
derived homothety `A ⟶ RHom_A(K, K)` is an isomorphism. -/
theorem bijective_smul_id_of_isIso_relativeHomothety (K : DerivedCategory (ModuleCat.{u} A))
    [IsIso (relativeHomothety A K)] :
    Function.Bijective (fun a : A => a • 𝟙 K) := by
  let e₁ := ExtComparison.homZeroEquivOverRing.{u, 0} A K K
  have key : (fun a : A => a • 𝟙 K) =
      e₁ ∘ (fun g => g ≫ relativeHomothety A K) ∘
        (fun a : A => a • 𝟙 (derivedTensorUnit.{u, 0} A)) := by
    ext a
    simp only [Function.comp_apply, Linear.smul_comp, Category.id_comp]
    rw [ExtComparison.homZeroEquivOverRing_map_smul, homZeroEquivOverRing_relativeHomothety]
  rw [key]
  refine e₁.bijective.comp (Function.Bijective.comp ?_ (bijective_smul_id_derivedTensorUnit A))
  convert (Iso.homCongr (Iso.refl (derivedTensorUnit.{u, 0} A))
    (asIso (relativeHomothety A K))).bijective using 1
  ext g
  simp [Iso.homCongr]

/-- **`K` has no nonzero morphism to a nonzero shift of itself** as soon as the derived homothety
`A ⟶ RHom_A(K, K)` is an isomorphism. -/
theorem subsingleton_shift_of_isIso_relativeHomothety (K : DerivedCategory (ModuleCat.{u} A))
    [IsIso (relativeHomothety A K)] (n : ℤ) (hn : n ≠ 0) :
    Subsingleton (K ⟶ K⟦n⟧) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) n
  have hU : IsZero (H.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (ULift.{0} A)))) := by
    rcases lt_or_gt_of_ne hn with h | h
    · exact DerivedCategory.isZero_of_isGE _ 0 n h
    · exact DerivedCategory.isZero_of_isLE _ 0 n h
  have hRHom : IsZero (H.obj ((derivedHomAdjunctionOverRing.{u, 0} A).hom.obj
      (Opposite.op K, K))) :=
    hU.of_iso (H.mapIso ((asIso (relativeHomothety A K)).symm ≪≫
      ExtComparison.unitIsoSingle.{u, 0} A))
  exact ModuleCat.subsingleton_of_isZero (((ModuleCat.uliftFunctor.{u + 1, u} A).map_isZero
    hRHom).of_iso ((ExtComparison.extCohomologyComparisonIso.{u, 0} A K n).app (Opposite.op K)))

/-- **The rank-one criterion for the derived homothety.**  Let `K` be bounded below in `D(A)`.  If
scalars act on `End_{D(A)}(K)` freely of rank one through the identity and `K` has no nonzero
morphism to a nonzero shift of itself, then the derived homothety `A ⟶ RHom_A(K, K)` is an
isomorphism. -/
theorem isIso_relativeHomothety_of_bijective_smul_id (K : DerivedCategory (ModuleCat.{u} A))
    (a : ℤ) [K.IsGE a] (hbij : Function.Bijective (fun c : A => c • 𝟙 K))
    (hvan : ∀ n : ℤ, n ≠ 0 → Subsingleton (K ⟶ K⟦n⟧)) :
    IsIso (relativeHomothety A K) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE K a
  obtain ⟨Rs, -, hR⟩ := CochainComplex.exists_injectiveResolution_isStrictlyGE a P
  let J := Rs.cocomplex
  have : J.IsKInjective := CochainComplex.isKInjective_of_injective J a
  let e : K ≅ DerivedCategory.Q.obj J := eP ≪≫ asIso (DerivedCategory.Q.map Rs.ι)
  let e₀ : End K ≃ₗ[A] A :=
    (LinearEquiv.ofBijective (LinearMap.toSpanSingleton A (End K) (𝟙 K)) hbij).symm
  have hJ : QuasiIso (homothety J) := by
    refine quasiIso_homothety_of_rankOne.{u, 0} J
      ((homologyZeroEndLinearEquiv J).trans ((endLinearEquivOfIso e.symm).trans e₀))
      fun n hn => ?_
    refine isZero_homology_homComplexR_of_subsingleton.{u, 0} J a n ?_
    have := hvan n hn
    exact Equiv.subsingleton
      (Iso.homCongr e ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) n).mapIso e)).symm
  exact isIso_derivedHomothety_overRing_of_injectiveRepresentative.{u, 0} A K J a hR
    Rs.injective e hJ

/-- **The derived homothety is invertible exactly when the self-extensions are those of `A`**:
for `K` bounded below in `D(A)`, `A ⟶ RHom_A(K, K)` is an isomorphism if and only if
`a ↦ a • 𝟙 K` is bijective onto `End_{D(A)}(K)` and `K ⟶ K⟦n⟧` is zero for every `n ≠ 0`. -/
theorem isIso_relativeHomothety_iff_selfExt (K : DerivedCategory (ModuleCat.{u} A)) (a : ℤ)
    [K.IsGE a] :
    IsIso (relativeHomothety A K) ↔
      Function.Bijective (fun c : A => c • 𝟙 K) ∧
        ∀ n : ℤ, n ≠ 0 → Subsingleton (K ⟶ K⟦n⟧) :=
  ⟨fun _ => ⟨bijective_smul_id_of_isIso_relativeHomothety A K,
      subsingleton_shift_of_isIso_relativeHomothety A K⟩,
    fun h => isIso_relativeHomothety_of_bijective_smul_id A K a h.1 h.2⟩

end

end Dualizing
