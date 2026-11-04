module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSectionsBaseChange
public import StacksFrontier.Algebra.Module.TwoTermComplex.Noetherian
public import Mathlib.Order.ULift
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper

/-!
# The two-term Čech complex of a scheme over a ring covered by two affine opens

Let `A` be a ring, `f : X ⟶ Spec A` separated, and `U₀, U₁` affine opens covering `X`. For a
quasi-coherent `𝒪_X`-module `F` the alternating Čech complex of the covering, a complex of
`A`-modules, has only two nonzero terms:

`Γ(U₀, F) × Γ(U₁, F) ⟶ Γ(U₀ ⊓ U₁, F)`.

So `Hⁱ(X, F)` is the kernel (`i = 0`) and the cokernel (`i = 1`) of a single `A`-linear map
`cechD`, and vanishes for `i ≥ 2`; both terms are flat over `A` when `F` is; and the map `cechD`
commutes with arbitrary base change `A ⟶ A'`.

## Main definitions

* `Stacks.TwoAffineCech.Cover`: the index type `ULift (Fin 2)` of the covering.
* `Stacks.TwoAffineCech.cechD`: the degree-zero differential of the alternating Čech complex.
* `Stacks.TwoAffineCech.cohomologyZeroIso`, `Stacks.TwoAffineCech.cohomologyOneIso`: `H⁰(X, F)`
  and `H¹(X, F)` as the kernel and the cokernel of `cechD`.
* `Stacks.TwoAffineCech.baseChangeEquiv`: the base-change isomorphism `A' ⊗_A Cᵖ ≃ C'ᵖ`.

## Main results

* `Stacks.TwoAffineCech.isZero_cohomology_of_two_le`: `Hᵐ(X, F) = 0` for `m ≥ 2`.
* `Stacks.TwoAffineCech.flat_X`: both terms of the complex are flat over `A` when `F` is.
* `Stacks.TwoAffineCech.baseChangeEquiv_comm`: `cechD` commutes with base change.
* `Stacks.TwoAffineCech.moduleFinite_ker`, `Stacks.TwoAffineCech.moduleFinite_coker`: over a
  Noetherian base, for `f` proper and `F` coherent, the kernel and the cokernel of `cechD` are
  finite `A`-modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Stacks.TwoAffineCech

/-- The index type of a covering by two opens. -/
abbrev Cover : Type u := ULift.{u} (Fin 2)

/-- A tuple of length at least three in a two-element index type has a repeated entry. -/
theorem not_injective_of_two_le {p : ℕ} (hp : 2 ≤ p) (i : Fin (p + 1) → Cover.{u}) :
    ¬ Function.Injective i := by
  intro hi
  have := Fintype.card_le_of_injective i hi
  simp only [Fintype.card_fin, Fintype.card_ulift] at this
  omega

section Basic

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (U : Cover.{u} → X.Opens) (F : X.Modules)

/-- **The alternating Čech complex of a two-element covering vanishes in degrees `≥ 2`.** -/
theorem isZero_X_of_two_le {p : ℕ} (hp : 2 ≤ p) :
    IsZero ((Stacks.Cech.alternatingCechModuleComplex f U F).X p) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun s t ↦ ?_⟩
  apply Subtype.ext
  funext i
  rw [s.2.1 i (not_injective_of_two_le hp i), t.2.1 i (not_injective_of_two_le hp i)]

/-- The degree-zero differential of the alternating Čech complex, as an `A`-linear map. -/
abbrev cechD :
    (Stacks.Cech.alternatingCechModuleComplex f U F).X 0 →ₗ[A]
      (Stacks.Cech.alternatingCechModuleComplex f U F).X 1 :=
  ((Stacks.Cech.alternatingCechModuleComplex f U F).d 0 1).hom

/-- **`H⁰` of the alternating Čech complex is the kernel of `cechD`.** -/
def homologyZeroIso :
    (Stacks.Cech.alternatingCechModuleComplex f U F).homology 0 ≅
      ModuleCat.of A (LinearMap.ker (cechD f U F)) :=
  (Stacks.Cech.alternatingCechModuleComplex f U F).isoHomologyπ₀.symm ≪≫
    IsLimit.conePointUniqueUpToIso
      ((Stacks.Cech.alternatingCechModuleComplex f U F).cyclesIsKernel 0 1 (by simp))
      (kernelIsKernel _) ≪≫
    ModuleCat.kernelIsoKer _

/-- **`H¹` of the alternating Čech complex is the cokernel of `cechD`**, the term in degree two
being zero. -/
def homologyOneIso :
    (Stacks.Cech.alternatingCechModuleComplex f U F).homology 1 ≅
      ModuleCat.of A ((Stacks.Cech.alternatingCechModuleComplex f U F).X 1 ⧸
        LinearMap.range (cechD f U F)) :=
  (Stacks.Cech.alternatingCechModuleComplex f U F).isoHomologyι 1 2 (by simp)
      ((isZero_X_of_two_le f U F (le_refl 2)).eq_of_tgt _ _) ≪≫
    IsColimit.coconePointUniqueUpToIso
      ((Stacks.Cech.alternatingCechModuleComplex f U F).opcyclesIsCokernel 0 1 (by simp))
      (cokernelIsCokernel _) ≪≫
    ModuleCat.cokernelIsoRangeQuotient _

/-- The homology of the alternating Čech complex vanishes in degrees `≥ 2`. -/
theorem isZero_homology_of_two_le {p : ℕ} (hp : 2 ≤ p) :
    IsZero ((Stacks.Cech.alternatingCechModuleComplex f U F).homology p) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _ (isZero_X_of_two_le f U F hp)

variable [IsSeparated f] [F.IsQuasicoherent] (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (hUaff : ∀ i, IsAffineOpen (U i))

/-- **The alternating Čech complex of a covering by two affine opens computes cohomology,
`A`-linearly.** -/
def homologyIsoCohomology (m : ℕ) :
    (Stacks.Cech.alternatingCechModuleComplex f U F).homology m ≅
      (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).obj
        ((((AlgebraicGeometry.moduleGlobalSections X)).rightDerived m).obj F) :=
  ((Stacks.Cech.alternatingCechModuleComplex f U F).extendHomologyIso
      ComplexShape.embeddingUpNat (j := m) (j' := (m : ℤ)) rfl).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ (m : ℤ)).mapIso
      (Stacks.AlgebraicGeometry.ProperFlatGlobalSections.baseAlternatingCechComplexIsoExtend
        f U hU F).symm ≪≫
    Stacks.AlgebraicGeometry.ProperFlatGlobalSections.homologyBaseAlternatingCechComplexIso
      f U hU F (fun _ s => Stacks.Cech.inter_isAffineOpen f U hUaff s) m

/-- **`H⁰(X, F)` is the kernel of the two-term Čech differential**, `A`-linearly. -/
def cohomologyZeroIso :
    (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).obj
        ((((AlgebraicGeometry.moduleGlobalSections X)).rightDerived 0).obj F) ≅
      ModuleCat.of A (LinearMap.ker (cechD f U F)) :=
  (homologyIsoCohomology f U F hU hUaff 0).symm ≪≫ homologyZeroIso f U F

/-- **`H¹(X, F)` is the cokernel of the two-term Čech differential**, `A`-linearly. -/
def cohomologyOneIso :
    (ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).obj
        ((((AlgebraicGeometry.moduleGlobalSections X)).rightDerived 1).obj F) ≅
      ModuleCat.of A ((Stacks.Cech.alternatingCechModuleComplex f U F).X 1 ⧸
        LinearMap.range (cechD f U F)) :=
  (homologyIsoCohomology f U F hU hUaff 1).symm ≪≫ homologyOneIso f U F

include hU hUaff in
/-- **`Hᵐ(X, F) = 0` for `m ≥ 2`.** -/
theorem isZero_cohomology_of_two_le {m : ℕ} (hm : 2 ≤ m) :
    IsZero ((ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).obj
        ((((AlgebraicGeometry.moduleGlobalSections X)).rightDerived m).obj F)) :=
  (isZero_homology_of_two_le f U F hm).of_iso (homologyIsoCohomology f U F hU hUaff m).symm

include hUaff in
/-- Both terms of the two-term Čech complex are flat over `A` when `F` is. -/
theorem flat_X (hflat : IsFlatOver f.toLRSHom.toShHom F) (n : ℕ) :
    Module.Flat A ((Stacks.Cech.alternatingCechModuleComplex f U F).X n) :=
  Stacks.Cech.alternatingCechModuleComplex_flat f U F hUaff hflat n

end Basic

/-! ### Base change -/

section BaseChange

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
  {X X' : Scheme.{u}} (f : X ⟶ Spec (.of A)) (f' : X' ⟶ Spec (.of A')) (g : X' ⟶ X)
  (hsq : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))
  (U : Cover.{u} → X.Opens) (F : X.Modules) [IsSeparated f] [F.IsQuasicoherent]
  (hUaff : ∀ i, IsAffineOpen (U i))

/-- The degree-`p` base-change isomorphism of the two-term Čech complex, as a linear
equivalence `A' ⊗_A Cᵖ ≃ C'ᵖ`. -/
def baseChangeEquiv (p : ℕ) :
    letI : Algebra A A' := φ.toAlgebra
    A' ⊗[A] (Stacks.Cech.alternatingCechModuleComplex f U F).X p ≃ₗ[A']
      (Stacks.Cech.alternatingCechModuleComplex f' (fun i => g ⁻¹ᵁ U i)
        ((Scheme.Modules.pullback g).obj F)).X p :=
  letI : Algebra A A' := φ.toAlgebra
  (Stacks.Cech.alternatingCechModuleObjBaseChangeIso g U (fun i => g ⁻¹ᵁ U i) (Equiv.refl _)
    F (fun _ => rfl) φ f f' (Stacks.Cech.baseRingHom_comp_app φ f f' g hsq) hsq hUaff
    p).toLinearEquiv

/-- **The two-term Čech differential commutes with base change.** -/
theorem baseChangeEquiv_comm :
    letI : Algebra A A' := φ.toAlgebra
    (baseChangeEquiv φ f f' g hsq U F hUaff 1).toLinearMap ∘ₗ
        (cechD f U F).baseChange A' =
      cechD f' (fun i => g ⁻¹ᵁ U i) ((Scheme.Modules.pullback g).obj F) ∘ₗ
        (baseChangeEquiv φ f f' g hsq U F hUaff 0).toLinearMap := by
  let : Algebra A A' := φ.toAlgebra
  have h := congrArg ModuleCat.Hom.hom
    (Stacks.Cech.alternatingCechModuleObjBaseChangeIso_comm g U (fun i ↦ g ⁻¹ᵁ U i)
      (Equiv.refl _) F (fun _ ↦ rfl) φ f f' (Stacks.Cech.baseRingHom_comp_app φ f f' g hsq) hsq
      hUaff 0)
  simp only [ModuleCat.hom_comp] at h
  exact LinearMap.ext fun x ↦ (LinearMap.congr_fun h x).symm

end BaseChange

/-! ### Finiteness over a Noetherian base -/

section Noetherian

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  (U : Cover.{u} → X.Opens) (F : X.Modules) [IsSeparated f] [F.IsQuasicoherent]
  (hU : (⊤ : X.Opens) = ⨆ i, U i) (hUaff : ∀ i, IsAffineOpen (U i))

omit [IsSeparated f] [F.IsQuasicoherent] in
/-- **Finiteness of the cohomology over a Noetherian base**: for `f` proper over a Noetherian ring
and `F` coherent, `Hⁱ(X, F)` is a finite `A`-module ([Stacks, Tag 02O6]). -/
theorem moduleFinite_cohomology [IsNoetherianRing A] [IsProper f] [F.IsCoherent] (i : ℕ) :
    Module.Finite A ((ModuleCat.restrictScalars.{u} (Stacks.Cech.globalRingHom f).hom).obj
        ((((AlgebraicGeometry.moduleGlobalSections X)).rightDerived i).obj F)) := by
  have := AlgebraicGeometry.ProperCoherenceWitness.moduleFinite_cohomology f F i
  exact Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_compHom_of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
    ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((AlgebraicGeometry.moduleGlobalSections X).rightDerived i).obj F))

include hU hUaff in
omit [IsSeparated f] in
/-- The kernel of the two-term Čech differential is finite over a Noetherian base. -/
theorem moduleFinite_ker [IsNoetherianRing A] [IsProper f] [F.IsCoherent] :
    Module.Finite A (LinearMap.ker (cechD f U F)) := by
  have := moduleFinite_cohomology f F 0
  exact Module.Finite.equiv (cohomologyZeroIso f U F hU hUaff).toLinearEquiv

include hU hUaff in
omit [IsSeparated f] in
/-- The cokernel of the two-term Čech differential is finite over a Noetherian base. -/
theorem moduleFinite_coker [IsNoetherianRing A] [IsProper f] [F.IsCoherent] :
    Module.Finite A ((Stacks.Cech.alternatingCechModuleComplex f U F).X 1 ⧸
      LinearMap.range (cechD f U F)) := by
  have := moduleFinite_cohomology f F 1
  exact Module.Finite.equiv (cohomologyOneIso f U F hU hUaff).toLinearEquiv

end Noetherian

end Stacks.TwoAffineCech
