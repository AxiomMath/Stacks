module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.BoundedDirectSums
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.AffineBaseSectionsNatIndexed
public import StacksFrontier.AlgebraicGeometry.HigherDirectImageQcqs.Qcqs
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.GlobalFunctions
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.TwistCohomologyMonomial
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartQcoh
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.Homology.DerivedCategory.IsZero
public import StacksFrontier.Homology.DerivedCategory.LocallySmall

/-!
# Derived direct image of the twists along `P^n_A → Spec A`

Let `A` be a ring and `f : X = P^n_A = Proj A[T₀, …, Tₙ] ⟶ Spec A` the structure morphism. In the
locally small model of `D(𝒪)`, this file computes `Rf_*` on the twists `𝒪_X(d)` placed in a
single degree, in the range used by duality for projective space:

* `Rf_* 𝒪_X(d) = 0` for `-n ≤ d ≤ -1`;
* `Rf_* (𝒪_X(-n-1)[n]) ≅ 𝒪_{Spec A}`;
* `Rf_* 𝒪_X(0) ≅ 𝒪_{Spec A}`.

The input is the cohomology of the twists on projective space ([Stacks, Tag 01XT]) together with
the identification of the higher direct images over an affine base with the cohomology modules
([Stacks, Tags 01XJ, 01XK]).
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

universe u

namespace Stacks.Duality.ProjectiveSpace

/-! ### Quasi-coherent modules on an affine scheme -/

section Affine

variable {R : CommRingCat.{u}}

/-- A quasi-coherent module on `Spec R` whose module of global sections is zero is zero. -/
theorem isZero_of_isQuasicoherent_of_subsingleton (Q : (Spec R).Modules) [Q.IsQuasicoherent]
    (h : Subsingleton (moduleSpecΓFunctor.obj Q)) : IsZero Q :=
  ((tilde.functor R).map_isZero (ModuleCat.isZero_of_subsingleton
    (moduleSpecΓFunctor.obj Q))).of_iso (asIso Q.fromTildeΓ).symm

/-- A quasi-coherent module on `Spec R` whose module of global sections is free of rank one is
the structure sheaf. -/
def isoUnitOfIsQuasicoherent (Q : (Spec R).Modules) [Q.IsQuasicoherent]
    (e : moduleSpecΓFunctor.obj Q ≅ ModuleCat.of R R) :
    Q ≅ SheafOfModules.unit (Spec R).ringCatSheaf :=
  (asIso Q.fromTildeΓ).symm ≪≫ (tilde.functor R).mapIso e ≪≫ tildeSelf

end Affine

/-! ### Higher direct images over an affine base -/

section HigherDirectImage

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (f : X ⟶ Spec R) [QuasiCompact f]
  [QuasiSeparated f]

/-- The cohomology `H^i(X, F)` read as an `R`-module through `f`. -/
abbrev cohomologyOver (F : X.Modules) (i : ℕ) : ModuleCat.{u} R :=
  (ModuleCat.restrictScalars ((Scheme.ΓSpecIso R).inv ≫ f.appTop).hom).obj
    (((moduleGlobalSections X).rightDerived i).obj F)

/-- **[Stacks, Tag 01XK] over `Spec R`, with `R`-coefficients**: the global sections of
`R^i f_* F` are `H^i(X, F)`, as `R`-modules. -/
def sectionsRightDerivedIsoCohomologyOver (F : X.Modules) [F.IsQuasicoherent] (i : ℕ) :
    moduleSpecΓFunctor.obj (((Scheme.Modules.pushforward f).rightDerived i).obj F) ≅
      cohomologyOver f F i :=
  ((ModuleCat.restrictScalars (Scheme.ΓSpecIso R).inv.hom).mapIso
      (Stacks.AlgebraicGeometry.HigherDirectImageQcoh.sectionsRightDerivedPushforwardIso
        f F i)).symm ≪≫
    (ModuleCat.restrictScalarsComp' _ _ _ rfl).symm.app _

/-- If `H^i(X, F)` vanishes then so does `R^i f_* F`, for `F` quasi-coherent. -/
theorem isZero_rightDerived_of_isZero (F : X.Modules) [F.IsQuasicoherent] (i : ℕ)
    (h : IsZero (((moduleGlobalSections X).rightDerived i).obj F)) :
    IsZero (((Scheme.Modules.pushforward f).rightDerived i).obj F) := by
  refine isZero_of_isQuasicoherent_of_subsingleton _ ?_
  have : Subsingleton (((moduleGlobalSections X).rightDerived i).obj F) :=
    ModuleCat.subsingleton_of_isZero h
  have : Subsingleton (cohomologyOver f F i) := this
  exact (sectionsRightDerivedIsoCohomologyOver f F i).toLinearEquiv.toEquiv.subsingleton

/-- The cohomology sheaves of `Rf_*(F[a])` vanish below degree `a`. -/
theorem isZero_homology_derivedPushforward_single_of_lt (F : X.Modules) (a m : ℤ) (hm : m < a) :
    IsZero ((DerivedCategory.homologyFunctor (Spec R).Modules m).obj
      ((Stacks.Duality.derivedPushforward f).obj
        ((DerivedCategory.singleFunctor X.Modules a).obj F))) := by
  have hge : ((Stacks.Duality.derivedPushforward f).obj
      ((DerivedCategory.singleFunctor X.Modules a).obj F)).IsGE a :=
    Stacks.DerivedFunctor.isGE_totalRightDerived_obj (Scheme.Modules.pushforward f) _ a
  exact DerivedCategory.isZero_of_isGE _ a m hm

/-- The cohomology sheaf of `Rf_*(F[a])` in degree `a + i` is `R^i f_* F`. -/
def homologyDerivedPushforwardSingleIso (F : X.Modules) (a m : ℤ) (i : ℕ) (hi : m - a = i) :
    (DerivedCategory.homologyFunctor (Spec R).Modules m).obj
      ((Stacks.Duality.derivedPushforward f).obj
        ((DerivedCategory.singleFunctor X.Modules a).obj F)) ≅
      ((Scheme.Modules.pushforward f).rightDerived i).obj F :=
  (Stacks.Duality.DerivedPushforward.singleCompDerivedPushforwardHomologyIso f a m i hi).app F

/-- The cohomology sheaf of `Rf_*(F[a])` in degree `m` vanishes if `R^i f_* F` does for the
`i = m - a ≥ 0`. -/
private theorem isZero_homology_derivedPushforward_single (F : X.Modules) [F.IsQuasicoherent]
    (a m : ℤ) (h : ∀ i : ℕ, m - a = i → IsZero (((moduleGlobalSections X).rightDerived i).obj F)) :
    IsZero ((DerivedCategory.homologyFunctor (Spec R).Modules m).obj
      ((Stacks.Duality.derivedPushforward f).obj
        ((DerivedCategory.singleFunctor X.Modules a).obj F))) := by
  rcases lt_or_ge m a with hm | hm
  · exact isZero_homology_derivedPushforward_single_of_lt f F a m hm
  · obtain ⟨i, hi⟩ : ∃ i : ℕ, m - a = i := ⟨(m - a).toNat, by omega⟩
    exact (isZero_rightDerived_of_isZero f F i (h i hi)).of_iso
      (homologyDerivedPushforwardSingleIso f F a m i hi)

/-- **`Rf_*(F[a]) = 0` when `F` is quasi-coherent with vanishing cohomology.** -/
theorem isZero_derivedPushforward_single (F : X.Modules) [F.IsQuasicoherent] (a : ℤ)
    (h : ∀ i : ℕ, IsZero (((moduleGlobalSections X).rightDerived i).obj F)) :
    IsZero ((Stacks.Duality.derivedPushforward f).obj
      ((DerivedCategory.singleFunctor X.Modules a).obj F)) := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  exact fun m => isZero_homology_derivedPushforward_single f F a m fun i _ => h i

/-- **`Rf_*(F[k]) ≅ 𝒪_{Spec R}` when `F` has cohomology only in degree `k`, free of rank one.** -/
theorem nonempty_derivedPushforward_single_iso (F : X.Modules) [F.IsQuasicoherent] (k : ℕ)
    (h : ∀ i : ℕ, i ≠ k → IsZero (((moduleGlobalSections X).rightDerived i).obj F))
    (e : cohomologyOver f F k ≅ ModuleCat.of R R) :
    Nonempty ((Stacks.Duality.derivedPushforward f).obj
        ((DerivedCategory.singleFunctor X.Modules (-(k : ℤ))).obj F) ≅
      (DerivedCategory.singleFunctor (Spec R).Modules 0).obj
        (SheafOfModules.unit (Spec R).ringCatSheaf)) := by
  set N := (Stacks.Duality.derivedPushforward f).obj
    ((DerivedCategory.singleFunctor X.Modules (-(k : ℤ))).obj F)
  have hvan : ∀ m : ℤ, m ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ m).obj N) := by
    intro m hm
    exact isZero_homology_derivedPushforward_single f F _ m fun i hi => h i (by omega)
  have : N.IsGE 0 := by
    rw [DerivedCategory.isGE_iff]
    exact fun i hi => hvan i (by omega)
  have : N.IsLE 0 := by
    rw [DerivedCategory.isLE_iff]
    exact fun i hi => hvan i (by omega)
  obtain ⟨Y, ⟨eY⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE N 0
  have e0 : Y ≅ ((Scheme.Modules.pushforward f).rightDerived k).obj F :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (Spec R).Modules 0).app Y).symm ≪≫
      (DerivedCategory.homologyFunctor _ 0).mapIso eY.symm ≪≫
      homologyDerivedPushforwardSingleIso f F _ 0 k (by omega)
  exact ⟨eY ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso (e0 ≪≫
    isoUnitOfIsQuasicoherent _ (sectionsRightDerivedIsoCohomologyOver f F k ≪≫ e))⟩

end HigherDirectImage

/-! ### Projective space -/

section ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable (A : Type u) [CommRing A] (n : ℕ)

/-- The only Laurent monomial of degree `-n-1` in `n + 1` variables with every exponent negative
is `1/(T₀ ⋯ Tₙ)`. -/
instance uniqueNegativeLaurentMonomials :
    Unique (Stacks.ProjectiveSpace.Cohomology.negativeLaurentMonomials n (-(n : ℤ) - 1)) where
  default := ⟨fun _ => -1, by
    refine ⟨?_, fun _ => by norm_num⟩
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring⟩
  uniq e := by
    obtain ⟨hsum, hneg⟩ := e.2
    have h0 : ∑ i, (e.1 i + 1) = 0 := by
      rw [Finset.sum_add_distrib, hsum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      push_cast; ring
    have hle : ∀ i ∈ Finset.univ, e.1 i + 1 ≤ 0 := fun i _ => by have := hneg i; omega
    have := (Finset.sum_eq_zero_iff_of_nonpos hle).1 h0
    exact Subtype.ext (funext fun i => by have := this i (Finset.mem_univ _); simp; omega)

/-- The top-degree part `((T₀ ⋯ Tₙ)⁻¹ A[T₀⁻¹, …, Tₙ⁻¹])_{-n-1}` is free of rank one. -/
def negativeTwistPartTopEquiv :
    Stacks.ProjectiveSpace.Cohomology.negativeTwistPart A n (-(n : ℤ) - 1) ≃ₗ[A] A :=
  (Stacks.ProjectiveSpace.Cohomology.negativeTwistPartEquivFinsupp A n (-(n : ℤ) - 1)).trans
    (Finsupp.LinearEquiv.finsuppUnique A A _)

/-- The structure morphism `P^n_A ⟶ Spec A`. -/
abbrev projStructureMorphism :
    AlgebraicGeometry.Proj (polyGrading A n) ⟶ Spec (CommRingCat.of A) :=
  projToSpecCoeff A n

/-- The structure morphism `P^n_A ⟶ Spec A` is quasi-compact. -/
instance quasiCompact_structureMorphism : QuasiCompact (projStructureMorphism A n) :=
  haveI := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff A n
  inferInstance

/-- The structure morphism `P^n_A ⟶ Spec A` is quasi-separated. -/
instance quasiSeparated_structureMorphism : QuasiSeparated (projStructureMorphism A n) :=
  haveI := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff A n
  inferInstance

/-- The twist `𝒪(d)` on `P^n_A`, as an `𝒪`-module of the scheme. -/
abbrev twist (d : ℤ) : (AlgebraicGeometry.Proj (polyGrading A n)).Modules :=
  ProjectiveSpectrum.Proj.twistingSheaf (polyGrading A n) d

/-- The twist `𝒪(d)` on `P^n_A` is quasi-coherent. -/
instance isQuasicoherent_twist (d : ℤ) : (twist A n d).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.TwistChartLocality.isQuasicoherent_twistingSheaf _ d

/-- The cohomology of `𝒪(d)` over `Spec A` is the cohomology module of Serre's computation. -/
def cohomologyOverIsoTwistCohomology (d : ℤ) (q : ℕ) :
    cohomologyOver (projStructureMorphism A n) (twist A n d) q ≅
      Stacks.ProjectiveSpace.Cohomology.twistCohomology A n d q :=
  Iso.refl _

/-- The vanishing of a cohomology module of Serre's computation is the vanishing of the
corresponding cohomology module of `𝒪(d)`. -/
theorem isZero_cohomology_twist_of_isZero (d : ℤ) (q : ℕ)
    (h : IsZero (Stacks.ProjectiveSpace.Cohomology.twistCohomology A n d q)) :
    IsZero (((moduleGlobalSections _).rightDerived q).obj (twist A n d)) := by
  have : Subsingleton (Stacks.ProjectiveSpace.Cohomology.twistCohomology A n d q) :=
    ModuleCat.subsingleton_of_isZero h
  have : Subsingleton (((moduleGlobalSections _).rightDerived q).obj (twist A n d)) := this
  exact ModuleCat.isZero_of_subsingleton _

/-- **`Rf_* 𝒪(d) = 0` for `-n ≤ d ≤ -1`**, on `f : P^n_A ⟶ Spec A`, in every degree `a`. -/
theorem isZero_derivedPushforward_twist (d : ℤ) (h₁ : -(n : ℤ) ≤ d) (h₂ : d < 0) (a : ℤ) :
    IsZero ((Stacks.Duality.derivedPushforward (projStructureMorphism A n)).obj
      ((DerivedCategory.singleFunctor _ a).obj (twist A n d))) := by
  refine isZero_derivedPushforward_single _ _ a fun q => ?_
  have hz : IsZero (Stacks.ProjectiveSpace.Cohomology.twistCohomology A n d q) := by
    by_cases hq : q = n
    · subst hq
      refine (Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoNegative A q d h₂).isZero_iff.2
        ?_
      have : Subsingleton (Stacks.ProjectiveSpace.Cohomology.negativeTwistPart A q d) := by
        rw [Stacks.ProjectiveSpace.Cohomology.negativeTwistPart_eq_bot_of_le A q d h₁]
        infer_instance
      exact ModuleCat.isZero_of_subsingleton _
    · exact Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology A n d q (by omega)
  exact isZero_cohomology_twist_of_isZero A n d q hz

/-- **`Rf_* 𝒪 ≅ 𝒪_{Spec A}`** for `f : P^n_A ⟶ Spec A`, with `𝒪 = 𝒪(0)` placed in degree zero. -/
theorem nonempty_derivedPushforward_twist_zero_iso :
    Nonempty ((Stacks.Duality.derivedPushforward (projStructureMorphism A n)).obj
        ((DerivedCategory.singleFunctor _ 0).obj (twist A n 0)) ≅
      (DerivedCategory.singleFunctor (Spec (CommRingCat.of A)).Modules 0).obj
        (SheafOfModules.unit _)) := by
  have h := nonempty_derivedPushforward_single_iso (projStructureMorphism A n) (twist A n 0) 0
    (fun i hi => isZero_cohomology_twist_of_isZero A n 0 i
      (Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology A n 0 i (by omega)))
    (cohomologyOverIsoTwistCohomology A n 0 0 ≪≫
      Stacks.ProjectiveSpace.Cohomology.twistCohomologyZeroIsoCoeff A n)
  simpa using h

/-- **`Rf_* 𝒪(-n-1)[n] ≅ 𝒪_{Spec A}`** for `f : P^n_A ⟶ Spec A`: the cohomology of `𝒪(-n-1)` is
concentrated in degree `n`, where it is free of rank one. -/
theorem nonempty_derivedPushforward_twist_top_iso :
    Nonempty ((Stacks.Duality.derivedPushforward (projStructureMorphism A n)).obj
        ((DerivedCategory.singleFunctor _ (-(n : ℤ))).obj (twist A n (-(n : ℤ) - 1))) ≅
      (DerivedCategory.singleFunctor (Spec (CommRingCat.of A)).Modules 0).obj
        (SheafOfModules.unit _)) :=
  nonempty_derivedPushforward_single_iso (projStructureMorphism A n) (twist A n (-(n : ℤ) - 1)) n
    (fun i hi => isZero_cohomology_twist_of_isZero A n _ i
      (Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology A n (-(n : ℤ) - 1) i
        (by omega)))
    (cohomologyOverIsoTwistCohomology A n _ n ≪≫
      Stacks.ProjectiveSpace.Cohomology.twistCohomologyIsoNegative A n _ (by omega) ≪≫
      (negativeTwistPartTopEquiv A n).toModuleIso)

end ProjectiveSpace

end Stacks.Duality.ProjectiveSpace

end
