module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.Comparison
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.IsoCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.TwistHom
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCoherator
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.AlgebraicGeometry.AffineVanishingQuasicoherentComplex
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.TwistedInverseImageBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.UnitStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceCoefficient.BoundedBelowDetection
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness

/-!
# The comparison map `(𝒪(-n-1) ⊗ p^*M~)[n] ⟶ p^×(M~)` is an isomorphism

Let `p : ℙⁿ_R ⟶ Spec R`. The trace `Rp_*((𝒪(-n-1) ⊗ p^*M~)[n]) ≅ M~` of
`StacksFrontier/AlgebraicGeometry/Duality/ProjectiveSpaceCoefficient/Comparison.lean` has, under the
adjunction `Rp_* ⊣ p^×`, an adjoint `c : (𝒪(-n-1) ⊗ p^*M~)[n] ⟶ p^×(M~)`. This file proves that
`c` is bijective on the maps out of the twists `𝒪(-i)[j]`, `0 ≤ i ≤ n`:

* for `i = 0` because the unit of `Lp^* ⊣ Rp_*` is an isomorphism at `𝒪_{Spec R}`, so that `Rp_*`
  is bijective on the maps out of `Lp^* 𝒪_{Spec R} ≅ 𝒪_{ℙⁿ_R}`;
* for `1 ≤ i ≤ n` because both sides vanish: `Rp_* 𝒪(-i) = 0`, and the twists of
  `(𝒪(-n-1) ⊗ p^*M~) ⊗ 𝒪(i)` are acyclic.

The cone of `c` is then a bounded below complex with quasi-coherent cohomology receiving only zero
maps from the `𝒪(-i)[j]`, hence zero (`Stacks.Duality.ProjCoeff.isIso_comparison_of`, with the
geometric inputs as hypotheses); `Stacks.Duality.ProjCoeff.isIso_comparison` discharges them and
`Stacks.Duality.ProjCoeff.twistedInverseImageIso` is the resulting
`p^×(M~) ≅ (𝒪(-n-1) ⊗ p^*M~)[n]`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Duality.ProjCoeff

variable (R : Type u) [CommRing R] (n : ℕ)

/-- `Rp_*` on `D_QCoh`. -/
abbrev Rpq := Stacks.ProjectiveSpace.Cohomology.quasiCoherentDerivedPushforwardProjToSpec R n

/-- The adjunction `Rp_* ⊣ p^×` on `D_QCoh`. -/
abbrev adjq :=
  Stacks.ProjectiveSpace.Cohomology.adjunction_quasiCoherentDerivedPushforward_projToSpecCoeff R n

/-- The trace isomorphism `Rp_*((𝒪(-n-1) ⊗ p^*M~)[n]) ≅ M~`. -/
def traceIso (M : ModuleCat.{u} R) : (Rpq R n).obj (Gqc R n M) ≅ Mqc R M :=
  (nonempty_trace R n M).some

/-- **The comparison map** `c : (𝒪(-n-1) ⊗ p^*M~)[n] ⟶ p^×(M~)`, adjoint to the trace. -/
def comparison (M : ModuleCat.{u} R) :
    Gqc R n M ⟶ (Stacks.ProjectiveSpace.Cohomology.twistedInverseImageProjToSpec R n).obj
      (Mqc R M) :=
  (adjq R n).homEquiv _ _ (traceIso R n M).hom

/-- `𝒪(d)[0]⟦j⟧` has quasi-coherent cohomology. -/
theorem isQuasicoherent_homology_singleShift (F : (P R n).Modules) (hF : F.IsQuasicoherent)
    (j : ℤ) (k : ℤ) :
    ((DerivedCategory.homologyFunctor (P R n).Modules k).obj
      (((DerivedCategory.singleFunctor (P R n).Modules 0).obj F)⟦j⟧)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (P R n).ringCatSheaf).prop_of_iso
    (((DerivedCategory.homologyFunctor (P R n).Modules 0).shiftIso j k (j + k)
      (by omega)).app _).symm
    (Stacks.Duality.DerivedPushforward.derivedCategoryB_singleFunctor_obj F hF (j + k))

/-- `𝒪(-i)[0]⟦j⟧` as an object of `D_QCoh(ℙⁿ_R)`. -/
def Eq' (i j : ℤ) : Stacks.Duality.quasiCoherentDerivedCategory (P R n) :=
  ⟨((DerivedCategory.singleFunctor (P R n).Modules 0).obj (O R n (-i)))⟦j⟧,
    isQuasicoherent_homology_singleShift R n _
      (Stacks.ProjectiveCohomology.isQuasicoherent_twistingSheaf R n _) j⟩

/-- The cohomology of `RΓ(ℙⁿ_R, F[0])` is that of `F`, as `R`-modules. -/
def homologyRΓSingleIso (F : (P R n).Modules) (q : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (q : ℤ)).obj
        ((derivedGlobalSectionsOver (projToSpecCoeff R n)).obj
          ((DerivedCategory.singleFunctor (P R n).Modules 0).obj F)) ≅
      (ModuleCat.restrictScalars.{u} (Stacks.ProjectiveSpace.Cohomology.coeffScalar R n)).obj
        ((H R n q).obj F) :=
  ((Stacks.Duality.rightDerivedGlobalSectionsIsoDerivedCohomology
      (projToSpecCoeff R n) q).app _).symm ≪≫
    ((Stacks.Duality.rightDerivedCompRestrictScalarsIso
      (Stacks.ProjectiveSpace.Cohomology.coeffScalar R n)
      (Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading R n)) ⊤)
      (hE := Stacks.Cohomology.sectionsFunctor_additive _ _)
      (AlgebraicGeometry.globalSectionsOver (projToSpecCoeff R n))
      (hH := AlgebraicGeometry.globalSectionsOver_additive _)
      (eqToIso (Stacks.ProjectiveSpace.Cohomology.globalSectionsOver_projToSpecCoeff R n).symm)
      q).app _).symm

/-- `RΓ(ℙⁿ_R, F[0]) = 0` when `F` is acyclic. -/
theorem isZero_RΓ_single (F : (P R n).Modules) (hF : ∀ q, IsZero ((H R n q).obj F)) :
    IsZero ((derivedGlobalSectionsOver (projToSpecCoeff R n)).obj
      ((DerivedCategory.singleFunctor (P R n).Modules 0).obj F)) := by
  refine Stacks.SmallDerivedCategory.isZero_of_isZero_homologyFunctor_obj _ (fun q => ?_)
  rcases lt_or_ge q 0 with h | h
  · have := Stacks.ProjectiveSpace.Cohomology.isGE_singleFunctor_obj (P R n) F
    exact Stacks.DerivedFunctor.isZero_homology_totalRightDerived_obj
      (AlgebraicGeometry.globalSectionsOver (projToSpecCoeff R n)) _ 0 q h
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, q = (m : ℤ) := ⟨q.toNat, (Int.toNat_of_nonneg h).symm⟩
    refine (homologyRΓSingleIso R n F m).isZero_iff.2 ?_
    have h0 := hF m
    rw [ModuleCat.isZero_iff_subsingleton] at h0 ⊢
    exact h0

/-- An object sent to a zero object by a faithful functor is zero. -/
theorem isZero_of_faithful {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C]
    (E : C ⥤ D) [E.Faithful] {Y : C} (h : IsZero (E.obj Y)) : IsZero Y :=
  ⟨fun _ => ⟨⟨⟨0⟩, fun _ => E.map_injective (h.eq_of_src _ _)⟩⟩,
    fun _ => ⟨⟨⟨0⟩, fun _ => E.map_injective (h.eq_of_tgt _ _)⟩⟩⟩

/-- Pullback of `𝒪`-modules along the flat morphism `ℙⁿ_R ⟶ Spec R` preserves finite limits. -/
instance : Limits.PreservesFiniteLimits (Scheme.Modules.pullback (projToSpecCoeff R n)) :=
  AlgebraicGeometry.preservesFiniteLimits_pullback_of_flat (projToSpecCoeff R n)

/-- `Rp_*(F[0]⟦j⟧) = 0` in `D_QCoh(Spec R)` when `F` is acyclic. -/
theorem isZero_Rpq_single (F : (P R n).Modules) (hqc : F.IsQuasicoherent)
    (hF : ∀ q, IsZero ((H R n q).obj F)) (j : ℤ) :
    IsZero ((Rpq R n).obj
      ⟨((DerivedCategory.singleFunctor (P R n).Modules 0).obj F)⟦j⟧,
        isQuasicoherent_homology_singleShift R n F hqc j⟩) := by
  have := derivedGlobalSectionsQuasicoherent_isEquivalence (.of R)
  refine isZero_of_faithful (derivedGlobalSectionsQuasicoherent (.of R)) ?_
  let X := (DerivedCategory.singleFunctor (P R n).Modules 0).obj F
  have h1 : IsZero ((derivedGlobalSectionsOver (projToSpecCoeff R n)).obj (X⟦j⟧)) :=
    (((derivedGlobalSectionsOver (projToSpecCoeff R n)).commShiftIso j).app X).isZero_iff.2
      ((shiftFunctor _ j).map_isZero (isZero_RΓ_single R n F hF))
  exact h1.of_iso ((derivedGlobalSectionsOverIsoDerivedPushforward (projToSpecCoeff R n)).app
      (X⟦j⟧)).symm

/-- On `D_QCoh`, `Rp_*` is bijective on maps as soon as the ambient `Rp_*` is. -/
theorem bijective_Rpq_map {X Y : Stacks.Duality.quasiCoherentDerivedCategory (P R n)}
    (h : Function.Bijective (fun φ : X.obj ⟶ Y.obj =>
      (Stacks.Duality.derivedPushforward (projToSpecCoeff R n)).map φ)) :
    Function.Bijective (fun φ : X ⟶ Y => (Rpq R n).map φ) := by
  let e₁ := (ObjectProperty.fullyFaithfulι _).homEquiv (X := X) (Y := Y)
  let e₂ := (ObjectProperty.fullyFaithfulι _).homEquiv (X := (Rpq R n).obj X)
    (Y := (Rpq R n).obj Y)
  exact e₂.symm.bijective.comp (h.comp e₁.bijective)

/-- Composition with a map of `D_QCoh` is bijective on ambient maps as soon as it is on maps of
`D_QCoh`. -/
theorem bijective_comp_hom {X Y Y' : Stacks.Duality.quasiCoherentDerivedCategory (P R n)}
    (c : Y ⟶ Y') (h : Function.Bijective (fun φ : X ⟶ Y => φ ≫ c)) :
    Function.Bijective (fun φ : X.obj ⟶ Y.obj => φ ≫ c.hom) := by
  let e₁ := (ObjectProperty.fullyFaithfulι _).homEquiv (X := X) (Y := Y)
  let e₂ := (ObjectProperty.fullyFaithfulι _).homEquiv (X := X) (Y := Y')
  exact e₂.bijective.comp (h.comp e₁.symm.bijective)

/-- `𝒪(-i)[0]⟦j⟧` admits no nonzero map to `(𝒪(-n-1) ⊗ p^*M~)[n]` for `1 ≤ i ≤ n`. -/
theorem hom_Eq'_Gqc_eq_zero (M : ModuleCat.{u} R) (i : ℤ) (h₁ : 1 ≤ i) (h₂ : i ≤ n) (j : ℤ)
    (f : (Eq' R n i j).obj ⟶ (Gqc R n M).obj) : f = 0 :=
  hom_twist_eq_zero R n i ((T R n (-(n : ℤ) - 1)).obj M) j n
    (fun q _ => isZero_H_Ttw R n (-(n : ℤ) - 1) i (by omega) (by omega) q M) f

/-- **`c` is bijective on the maps out of `𝒪(-i)[j]`, `1 ≤ i ≤ n`**: both sides vanish. -/
theorem bijective_comparison_twist (M : ModuleCat.{u} R) (i : ℤ) (h₁ : 1 ≤ i) (h₂ : i ≤ n)
    (j : ℤ) :
    Function.Bijective (fun φ : Eq' R n i j ⟶ Gqc R n M => φ ≫ comparison R n M) := by
  refine bijective_comp_homEquiv (adjq R n) _ ⟨fun φ ψ _ => ?_, fun g => ⟨0, ?_⟩⟩
  · exact ObjectProperty.hom_ext _ ((hom_Eq'_Gqc_eq_zero R n M i h₁ h₂ j _).trans
      (hom_Eq'_Gqc_eq_zero R n M i h₁ h₂ j _).symm)
  · exact (isZero_Rpq_single R n (O R n (-i))
      (Stacks.ProjectiveCohomology.isQuasicoherent_twistingSheaf R n _)
      (fun q => (isZero_H_O_iff R n _ q).2
        (Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology_of_neg_le R n _
          (by omega) (by omega) q)) j).eq_of_src _ _

/-- `𝒪_{Spec R}[0]`. -/
abbrev OS : DerivedCategory (Spec (.of R)).Modules :=
  (DerivedCategory.singleFunctor (Spec (.of R)).Modules 0).obj
    (SheafOfModules.unit (Spec (.of R)).ringCatSheaf)

/-- **`c` is bijective on the maps out of `𝒪[j]`**, given that the unit of `Lp^* ⊣ Rp_*` is an
isomorphism at `𝒪_{Spec R}` and that `Lp^* 𝒪_{Spec R} ≅ 𝒪_{ℙⁿ_R}`. -/
theorem bijective_comparison_zero (M : ModuleCat.{u} R)
    (hunit : IsIso ((Stacks.Duality.derivedAdjunction (projToSpecCoeff R n)).unit.app (OS R)))
    (hpull : (Stacks.Duality.derivedPullback (projToSpecCoeff R n)).obj (OS R) ≅
      (DerivedCategory.singleFunctor (P R n).Modules 0).obj (O R n 0))
    (j : ℤ) :
    Function.Bijective (fun φ : Eq' R n 0 j ⟶ Gqc R n M => φ ≫ comparison R n M) := by
  refine bijective_comp_homEquiv (adjq R n) _ (bijective_Rpq_map R n ?_)
  let adj := Stacks.Duality.derivedAdjunction (projToSpecCoeff R n)
  have := isIso_unit_app_shift adj (OS R) j
  let e : (Eq' R n 0 j).obj ≅
      (Stacks.Duality.derivedPullback (projToSpecCoeff R n)).obj ((OS R)⟦j⟧) :=
    (shiftFunctor _ j).mapIso
        ((DerivedCategory.singleFunctor (P R n).Modules 0).mapIso (eqToIso (by simp)) ≪≫
          hpull.symm) ≪≫ (leftAdjointShiftIso adj (OS R) j).symm
  exact bijective_map_of_iso _ e _ (bijective_map_of_isIso_unit adj _ _)

/-- `M~` lives in degrees `≥ 0`. -/
theorem isGE_Mqc (M : ModuleCat.{u} R) : (Mqc R M).obj.IsGE 0 := by
  have : (tilde.functor (CommRingCat.of R)).Additive := ⟨fun {_ _} f g => tilde.map_add f g⟩
  have := AlgebraicGeometry.tilde.preservesFiniteLimits (CommRingCat.of R)
  have := Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor (CommRingCat.of R)
  have : DerivedCategory.TStructure.t.IsGE ((tilde.functor (CommRingCat.of R) ⋙
      DerivedCategory.singleFunctor (Spec (CommRingCat.of R)).Modules 0).obj M) 0 :=
    (inferInstance : ((DerivedCategory.singleFunctor (Spec (CommRingCat.of R)).Modules 0).obj
      ((tilde.functor (CommRingCat.of R)).obj M)).IsGE 0)
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (((tilde.functor (CommRingCat.of R)).mapDerivedCategorySingleFunctor 0).app M).symm 0

/-- `p^×(M~)` lives in degrees `≥ -n`. -/
theorem isGE_twistedInverseImage_Mqc (M : ModuleCat.{u} R) :
    ((Stacks.ProjectiveSpace.Cohomology.twistedInverseImageProjToSpec R n).obj
      (Mqc R M)).obj.IsGE (-(n : ℤ)) := by
  simpa using isGE_twistedInverseImageProjToSpec R n (Mqc R M) 0 (isGE_Mqc R M)

/-- `c` is bijective on the maps out of every `𝒪(-i)[j]`, `0 ≤ i ≤ n`. -/
theorem bijective_comparison (M : ModuleCat.{u} R)
    (hunit : IsIso ((Stacks.Duality.derivedAdjunction (projToSpecCoeff R n)).unit.app (OS R)))
    (hpull : (Stacks.Duality.derivedPullback (projToSpecCoeff R n)).obj (OS R) ≅
      (DerivedCategory.singleFunctor (P R n).Modules 0).obj (O R n 0))
    (i : Fin (n + 1)) (j : ℤ) :
    Function.Bijective (fun φ : (Eq' R n i j).obj ⟶ (Gqc R n M).obj =>
      φ ≫ (comparison R n M).hom) := by
  refine bijective_comp_hom R n _ ?_
  obtain ⟨i, hi⟩ := i
  rcases Nat.eq_zero_or_pos i with rfl | h
  · simpa using bijective_comparison_zero R n M hunit hpull j
  · exact bijective_comparison_twist R n M i (by omega) (by omega) j

/-- **The comparison map `(𝒪(-n-1) ⊗ p^*M~)[n] ⟶ p^×(M~)` is an isomorphism**, given the three
geometric inputs: the unit of `Lp^* ⊣ Rp_*` is an isomorphism at `𝒪_{Spec R}`,
`Lp^* 𝒪_{Spec R} ≅ 𝒪_{ℙⁿ_R}`, and a bounded below complex with quasi-coherent cohomology which
receives no nonzero map from the `𝒪(-i)[j]`, `0 ≤ i ≤ n`, is zero. -/
theorem isIso_comparison_of (M : ModuleCat.{u} R)
    (hunit : IsIso ((Stacks.Duality.derivedAdjunction (projToSpecCoeff R n)).unit.app (OS R)))
    (hpull : (Stacks.Duality.derivedPullback (projToSpecCoeff R n)).obj (OS R) ≅
      (DerivedCategory.singleFunctor (P R n).Modules 0).obj (O R n 0))
    (hdet : ∀ (Z : DerivedCategory (P R n).Modules)
      (_ : ∀ k : ℤ, ((DerivedCategory.homologyFunctor (P R n).Modules k).obj Z).IsQuasicoherent)
      (_ : ∃ b : ℤ, Z.IsGE b)
      (_ : ∀ (i : Fin (n + 1)) (j : ℤ)
        (φ : ((DerivedCategory.singleFunctor (P R n).Modules 0).obj (O R n (-(i : ℤ))))⟦j⟧ ⟶ Z),
        φ = 0), IsZero Z) :
    IsIso (comparison R n M) := by
  let c := comparison R n M
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle c.hom
  let T := Triangle.mk c.hom g h
  have hqc : (Stacks.Duality.Coherator.quasiCoherentProp (P R n)) Z :=
    (Stacks.Duality.Coherator.quasiCoherentProp (P R n)).ext_of_isTriangulatedClosed₃ T hT
      (Gqc R n M).property (((Stacks.ProjectiveSpace.Cohomology.twistedInverseImageProjToSpec
        R n).obj (Mqc R M)).property)
  have hb : Z.IsGE (-(n : ℤ) - 1) := by
    have h₁ : ((Stacks.ProjectiveSpace.Cohomology.twistedInverseImageProjToSpec R n).obj
        (Mqc R M)).obj.IsGE (-(n : ℤ) - 1) := by
      have := isGE_twistedInverseImage_Mqc R n M
      exact DerivedCategory.TStructure.t.isGE_of_ge _ _ (-(n : ℤ))
    have h₃ : ((Gqc R n M).obj⟦(1 : ℤ)⟧).IsGE (-(n : ℤ) - 1) := by
      have : ((Gsingle R n M)⟦(n : ℤ)⟧).IsGE (-(n : ℤ)) :=
        DerivedCategory.TStructure.t.isGE_shift _ 0 (n : ℤ) (-(n : ℤ)) (by omega)
      exact DerivedCategory.TStructure.t.isGE_shift ((Gsingle R n M)⟦(n : ℤ)⟧) (-(n : ℤ)) 1
        (-(n : ℤ) - 1) (by omega)
    exact DerivedCategory.TStructure.t.isGE₂ T.rotate (rot_of_distTriang _ hT) _ h₁ h₃
  have hZ : IsZero Z := by
    refine hdet Z hqc ⟨_, hb⟩ (fun i j φ => ?_)
    let W' := (Eq' R n i (j - 1)).obj
    let e : ((DerivedCategory.singleFunctor (P R n).Modules 0).obj (O R n (-(i : ℤ))))⟦j⟧ ≅
        W'⟦(1 : ℤ)⟧ :=
      (shiftFunctorAdd' (DerivedCategory (P R n).Modules) (j - 1) 1 j (by omega)).app _
    exact eq_zero_of_bijective_comp T hT e
      (bijective_comparison R n M hunit hpull i j).2
      (bijective_comparison R n M hunit hpull i (j - 1)).1 φ
  have : IsIso ((ObjectProperty.ι _).map c) := (Triangle.isZero₃_iff_isIso₁ T hT).1 hZ
  exact (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map c

/-- `Lp^* 𝒪_{Spec R}[0] ≅ 𝒪(0)[0]`. -/
def derivedPullbackOSIso :
    (Stacks.Duality.derivedPullback (projToSpecCoeff R n)).obj (OS R) ≅
      (DerivedCategory.singleFunctor (P R n).Modules 0).obj (O R n 0) :=
  derivedPullbackStructureSheafIso R n ≪≫ (DerivedCategory.singleFunctor (P R n).Modules 0).mapIso
    (Stacks.AlgebraicGeometry.ProjEulerSequence.twistingSheafZeroIsoUnit (polyGrading R n)).symm

/-- **The comparison map `(𝒪(-n-1) ⊗ p^*M~)[n] ⟶ p^×(M~)` is an isomorphism**, given that the unit
of `Lp^* ⊣ Rp_*` is an isomorphism at `𝒪_{Spec R}`. -/
theorem isIso_comparison_of_isIso_unit (M : ModuleCat.{u} R)
    (hunit : IsIso ((Stacks.Duality.derivedAdjunction (projToSpecCoeff R n)).unit.app (OS R))) :
    IsIso (comparison R n M) :=
  isIso_comparison_of R n M hunit (derivedPullbackOSIso R n)
    (isZero_of_hom_twist_eq_zero R n)

/-- **[Stacks, Tag 0A9W] with coefficients: the comparison map
`(𝒪(-n-1) ⊗ p^*M~)[n] ⟶ p^×(M~)` is an isomorphism**, for `p : ℙⁿ_R ⟶ Spec R` and every
`R`-module `M`. -/
theorem isIso_comparison (M : ModuleCat.{u} R) : IsIso (comparison R n M) :=
  isIso_comparison_of_isIso_unit R n M (isIso_derivedAdjunction_unit_structureSheaf R n)

/-- **Duality on `ℙⁿ_R` with coefficients**: `p^×(M~) ≅ (𝒪(-n-1) ⊗ p^*M~)[n]` in `D_QCoh(ℙⁿ_R)`. -/
def twistedInverseImageIso (M : ModuleCat.{u} R) :
    (Stacks.ProjectiveSpace.Cohomology.twistedInverseImageProjToSpec R n).obj (Mqc R M) ≅
      Gqc R n M :=
  haveI := isIso_comparison R n M
  (asIso (comparison R n M)).symm

end Stacks.Duality.ProjCoeff
