module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatExtendScalarsNoncomm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatOfProjectiveStalks
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekSumResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlatStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesCtfOpenClosed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.RestrictionOfScalarsNoncomm
public import StacksFrontier.CategoryTheory.Abelian.SerreClass.WeakInverseImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructible flat representatives over a finite, possibly noncommutative, ring

Let `X` be a quasi-compact and quasi-separated scheme and `Λ` a finite ring, not necessarily
commutative. This file proves the construction of the direction (1) ⟹ (2) of [Stacks, Tag 03TT]
for such a ring: an object `K` of `D(X_étale, Λ)` whose cohomology sheaves vanish outside
`[a, b]` and are constructible, and whose bounded above representatives by sheaves with finite
projective stalks have projective stalks of the cokernel of the differential into degree `a`, is
represented by a complex of constructible flat sheaves of `Λ`-modules concentrated in `[a, b]`.

Constructibility of the cohomology sheaves is asked of their underlying sheaves of abelian groups.

## Main definitions

* `Stacks.EtaleCohomology.IsIntConstructible`: a sheaf of `Λ`-modules whose underlying sheaf of
  abelian groups is constructible.
* `Stacks.EtaleCohomology.IsExtendedAffineShriekSum`: a sheaf of `Λ`-modules isomorphic to the
  extension of scalars of a finite direct sum of sheaves `j_{U!}\underline{ℤ}_U` with `U` affine.

## Main results

* `Stacks.EtaleCohomology.exists_constructibleFlat_representative_of_projective_cokernel`: on the
  small étale site of Stacks 021B, such an object `K` is represented by a complex of constructible
  flat sheaves of `Λ`-modules concentrated in `[a, b]`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type) [Ring Λ]

/-- The underlying sheaf of abelian groups (as `ℤ`-modules) of a sheaf of `Λ`-modules on the
small étale site of Stacks 021B. -/
abbrev intRestrictScalarsSheaf :
    Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ) ⥤
      Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} ℤ) :=
  restrictScalarsSheafNoncomm.{u + 1} (Int.castRingHom Λ) (SmallEtale.topology B X.obj X.property)

/-- Sheafified extension of scalars from `ℤ` to `Λ` on the small étale site of Stacks 021B. -/
abbrev intExtendScalarsSheaf :
    Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} ℤ) ⥤
      Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ) :=
  letI := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X Λ
  extendScalarsSheafNoncomm.{u + 1} (Int.castRingHom Λ) (SmallEtale.topology B X.obj X.property)

/-- Extension of scalars is left adjoint to restriction of scalars. -/
def intExtendRestrictScalarsSheafAdj :
    intExtendScalarsSheaf B X Λ ⊣ intRestrictScalarsSheaf B X Λ :=
  letI := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X Λ
  letI := hasSheafCompose_restrictScalarsNoncomm.{u + 1} (Int.castRingHom Λ)
    (SmallEtale.topology B X.obj X.property)
  Sheaf.adjunction _ (Stacks.NoncommChangeOfRings.extendRestrictScalarsAdj.{u + 1}
    (Int.castRingHom Λ))

/-- Restriction of scalars is left adjoint to coextension of scalars. -/
def intRestrictCoextendScalarsSheafAdj :
    intRestrictScalarsSheaf B X Λ ⊣
      (letI := hasSheafCompose_coextendScalars_noncomm.{u + 1} (Int.castRingHom Λ)
        (SmallEtale.topology B X.obj X.property)
      sheafCompose (SmallEtale.topology B X.obj X.property)
        (ModuleCat.coextendScalars.{0, 0, u + 1} (Int.castRingHom Λ))) :=
  letI := hasSheafCompose_coextendScalars_noncomm.{u + 1} (Int.castRingHom Λ)
    (SmallEtale.topology B X.obj X.property)
  ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, 0, 0} (Int.castRingHom Λ)).whiskerRight
      (SmallEtale B X.obj X.property)ᵒᵖ).restrictFullyFaithful
    (fullyFaithfulSheafToPresheaf _ _) (fullyFaithfulSheafToPresheaf _ _) (Iso.refl _) (Iso.refl _)

/-- Restriction of scalars from `Λ` to `ℤ` is a left adjoint. -/
instance intRestrictScalarsSheaf_isLeftAdjoint : (intRestrictScalarsSheaf B X Λ).IsLeftAdjoint :=
  (intRestrictCoextendScalarsSheafAdj B X Λ).isLeftAdjoint

/-- Restriction of scalars from `Λ` to `ℤ` is a right adjoint. -/
instance intRestrictScalarsSheaf_isRightAdjoint : (intRestrictScalarsSheaf B X Λ).IsRightAdjoint :=
  (intExtendRestrictScalarsSheafAdj B X Λ).isRightAdjoint

/-- Extension of scalars from `ℤ` to `Λ` is a left adjoint. -/
instance intExtendScalarsSheaf_isLeftAdjoint : (intExtendScalarsSheaf B X Λ).IsLeftAdjoint :=
  (intExtendRestrictScalarsSheafAdj B X Λ).isLeftAdjoint

/-- Restriction of scalars from `Λ` to `ℤ` is faithful. -/
instance intRestrictScalarsSheaf_faithful : (intRestrictScalarsSheaf B X Λ).Faithful where
  map_injective {F G} f g h := by
    ext U x
    exact congrArg (fun φ => φ.hom.app U x) h

/-- A sheaf of `Λ`-modules whose underlying sheaf of abelian groups is constructible. -/
def IsIntConstructible :
    ObjectProperty (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) :=
  letI := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X ℤ
  (isConstructibleModuleSheafProperty.{u, u + 1, 0} B X ℤ).inverseImage
    (intRestrictScalarsSheaf B X Λ)

/-- The sheaves of `Λ`-modules whose underlying sheaf of abelian groups is constructible form a
weak Serre class. -/
instance isWeakSerreClass_isIntConstructible : (IsIntConstructible B X Λ).IsWeakSerreClass := by
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X ℤ
  have := isWeakSerreClass_isConstructibleModuleSheafProperty.{u, 0} B X ℤ
  unfold IsIntConstructible
  infer_instance

/-- A sheaf of `Λ`-modules isomorphic to the extension of scalars of a finite direct sum of
sheaves `j_{U!}\underline{ℤ}_U` with `U` affine. -/
def IsExtendedAffineShriekSum
    (M : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) : Prop :=
  ∃ H, IsAffineShriekSum.{u, 0} B X ℤ H ∧ Nonempty (M ≅ (intExtendScalarsSheaf B X Λ).obj H)

/-- The extension of scalars of a finite affine shriek sum over `ℤ` is constructible flat over
`Λ`, the ambient scheme being quasi-separated. -/
theorem isConstructibleFlatModuleSheaf_of_isExtendedAffineShriekSum [QuasiSeparatedSpace X.obj]
    {M : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)}
    (hM : IsExtendedAffineShriekSum B X Λ M) : IsConstructibleFlatModuleSheaf B X Λ M := by
  obtain ⟨H, ⟨n, U, hU, ⟨eH⟩⟩, ⟨e⟩⟩ := hM
  have hH : IsConstructibleFlatModuleSheaf B X ℤ H :=
    isConstructibleFlatModuleSheaf_congr B X ℤ eH.symm
      (isConstructibleFlatModuleSheaf_sigma_moduleShriekConstant_of_quasiSeparated B X ℤ U hU)
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X Λ
  exact isConstructibleFlatModuleSheaf_congr B X Λ e.symm
    (isConstructibleFlatModuleSheaf_extendScalarsSheafNoncomm.{u, u + 1} B X (Int.castRingHom Λ)
      H hH)

variable [Finite Λ]

/-- A constructible sheaf of `Λ`-modules is constructible as a sheaf of abelian groups. -/
theorem isIntConstructible_of_isConstructibleModuleSheaf
    {M : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)}
    (hM : IsConstructibleModuleSheaf B X Λ M) : IsIntConstructible B X Λ M := by
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X ℤ
  exact isConstructibleModuleSheaf_restrictScalarsInt.{u, u + 1, 0} B X Λ M hM

/-- **The extensions of scalars of finite affine shriek sums over `ℤ` cover epimorphisms onto
sheaves of `Λ`-modules with constructible underlying abelian sheaf.** -/
@[sga "4½ Rapport 4.8" "special case"]
theorem coversEpis_isExtendedAffineShriekSum [CompactSpace X.obj] [QuasiSeparatedSpace X.obj] :
    Stacks.Homology.BoundedAboveResolution.CoversEpis (IsIntConstructible B X Λ)
      (IsExtendedAffineShriekSum B X Λ) := by
  intro V W f hf hW
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X ℤ
  let adj := intExtendRestrictScalarsSheafAdj B X Λ
  obtain ⟨H, g, hG, -, hepi⟩ :=
    coversEpis_isAffineShriekSum.{u, 0} B X ℤ ((intRestrictScalarsSheaf B X Λ).map f)
      inferInstance hW
  have hext : IsExtendedAffineShriekSum B X Λ ((intExtendScalarsSheaf B X Λ).obj H) :=
    ⟨H, hG, ⟨Iso.refl _⟩⟩
  refine ⟨_, (adj.homEquiv _ _).symm g, hext, ?_, ?_⟩
  · exact isIntConstructible_of_isConstructibleModuleSheaf B X Λ
      (isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf B X Λ
        (isConstructibleFlatModuleSheaf_of_isExtendedAffineShriekSum B X Λ hext))
  · have hfac : adj.unit.app H ≫ (intRestrictScalarsSheaf B X Λ).map
        ((adj.homEquiv _ _).symm g ≫ f) = g ≫ (intRestrictScalarsSheaf B X Λ).map f := by
      have h1 : adj.homEquiv _ _ ((adj.homEquiv _ _).symm g) = g := Equiv.apply_symm_apply _ _
      rw [Adjunction.homEquiv_unit] at h1
      rw [Functor.map_comp, ← Category.assoc, h1]
    have : Epi (adj.unit.app H ≫ (intRestrictScalarsSheaf B X Λ).map
        ((adj.homEquiv _ _).symm g ≫ f)) := by rw [hfac]; exact hepi
    have : Epi ((intRestrictScalarsSheaf B X Λ).map ((adj.homEquiv _ _).symm g ≫ f)) :=
      epi_of_epi (adj.unit.app H) _
    exact (intRestrictScalarsSheaf B X Λ).epi_of_epi_map this

omit [Finite Λ] in
/-- The stalks of a constructible flat sheaf are finite projective modules. -/
theorem finite_projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf
    (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) (s : GeometricPoint X.obj) :
    Module.Finite Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ s).obj F) ∧
      Module.Projective Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ s).obj F) := by
  refine stalk_prop_of_isStratifiedLocallyConstantWith B X Λ
    (fun E : ModuleCat.{u + 1} Λ => Module.Finite Λ E ∧ Module.Projective Λ E)
    (fun e hE => by
      obtain ⟨h1, h2⟩ := hE
      exact ⟨Module.Finite.equiv e.toLinearEquiv, Module.Projective.of_equiv' e.toLinearEquiv⟩)
    (fun E hE => by
      have := hE
      have : Module.Free Λ E := Module.Free.of_basis (Module.Basis.empty (ι := PEmpty.{1}) E)
      exact ⟨inferInstance, Module.Projective.of_free⟩) F ?_ s
  intro U
  obtain ⟨σ, hσ⟩ := hF U
  refine ⟨σ, fun i V => ?_⟩
  obtain ⟨I, W, f, hcover, hloc⟩ := hσ i V
  refine ⟨I, W, f, hcover, fun j => ?_⟩
  obtain ⟨E, hfin, hproj, he⟩ := hloc j
  exact ⟨E, ⟨hfin, hproj⟩, he⟩

/-- **Constructible flat representatives over a finite ring.** On a quasi-compact and
quasi-separated scheme, let `K` be an object of `D(X_étale, Λ)`, `Λ` a finite ring, whose
cohomology sheaves vanish outside `[a, b]` and have constructible underlying abelian sheaves.
Suppose that for every bounded above complex representing `K`, concentrated in degrees `≤ b` and
with finite projective stalks, the cokernel of the differential into degree `a` has projective
stalks. Then `K` is represented by a complex of constructible flat sheaves of `Λ`-modules
concentrated in `[a, b]`. -/
theorem exists_constructibleFlat_representative_of_projective_cokernel
    [CompactSpace X.obj] [QuasiSeparatedSpace X.obj]
    (K : DerivedCategory
      (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ))) (a b : ℤ)
    (hcons : ∀ i : ℤ, IsIntConstructible B X Λ
      ((DerivedCategory.homologyFunctor _ i).obj K))
    (hvan : ∀ i : ℤ, i ∉ Set.Icc a b → IsZero ((DerivedCategory.homologyFunctor _ i).obj K))
    (hproj : ∀ (Y : CochainComplex
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) ℤ),
      Nonempty (DerivedCategory.Q.obj Y ≅ K) → Y.IsStrictlyLE b →
      (∀ (n : ℤ) (s : GeometricPoint X.obj),
        Module.Finite Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ s).obj (Y.X n)) ∧
          Module.Projective Λ ((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ s).obj (Y.X n))) →
      ∀ s : GeometricPoint X.obj, Module.Projective Λ
        ((etaleModuleStalkFunctor.{u, u + 1, 0} B X Λ s).obj (cokernel (Y.d (a - 1) a)))) :
    ∃ F : CochainComplex
        (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)) ℤ,
      F.IsStrictlyGE a ∧ F.IsStrictlyLE b ∧
        (∀ i : ℤ, IsConstructibleFlatModuleSheaf B X Λ (F.X i)) ∧
        Nonempty (DerivedCategory.Q.obj F ≅ K) := by
  let := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X Λ
  let 𝒜 := Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ)
  have hKLE : K.IsLE b := (DerivedCategory.isLE_iff K b).2 fun i hi =>
    hvan i (by simp only [Set.mem_Icc]; omega)
  have hKGE : K.IsGE a := (DerivedCategory.isGE_iff K a).2 fun i hi =>
    hvan i (by simp only [Set.mem_Icc]; omega)
  by_cases hab : b < a
  · have hKz : IsZero K := DerivedCategory.TStructure.t.isZero K b a hab
    have hz (i : ℤ) : IsZero ((0 : CochainComplex 𝒜 ℤ).X i) :=
      (HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _)
    exact ⟨0, (CochainComplex.isStrictlyGE_iff _ _).2 fun i _ => hz i,
      (CochainComplex.isStrictlyLE_iff _ _).2 fun i _ => hz i,
      fun i => isConstructibleFlatModuleSheaf_of_isZero B Λ X _ (hz i),
      ⟨IsZero.iso (DerivedCategory.Q.map_isZero (isZero_zero _)) hKz⟩⟩
  set P := IsIntConstructible B X Λ with hP
  obtain ⟨A, hA, ⟨e⟩⟩ := K.exists_iso_Q_obj_of_isLE b
  have hAhom : ∀ i : ℤ, P (A.homology i) := fun i =>
    P.prop_of_iso
      ((((DerivedCategory.homologyFunctorFactors _ i).app A).symm ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso e.symm).symm) (hcons i)
  obtain ⟨Y, hY, f, hf, hterms⟩ :=
    Stacks.Homology.BoundedAboveResolution.exists_quasiIso_isStrictlyLE_of_coversEpis
      P (IsExtendedAffineShriekSum B X Λ) A
      (coversEpis_isExtendedAffineShriekSum B X Λ)
      ⟨0, isAffineShriekSum_zero.{u, 0} B X ℤ,
        ⟨(isZero_zero 𝒜).iso ((intExtendScalarsSheaf B X Λ).map_isZero (isZero_zero _))⟩⟩
      (fun C E hC hE => by
        obtain ⟨HC, hHC, ⟨eC⟩⟩ := hC
        obtain ⟨HE, hHE, ⟨eE⟩⟩ := hE
        let := SmallEtale.hasSheafify_moduleCat.{u, 0, 0} B X ℤ
        exact ⟨HC ⊞ HE, isAffineShriekSum_biprod.{u, 0} B X ℤ hHC hHE,
          ⟨biprod.mapIso eC eE ≪≫ (by
            have := preservesBinaryBiproduct_of_preservesBinaryCoproduct
              (X := HC) (Y := HE) (intExtendScalarsSheaf B X Λ)
            exact (Functor.mapBiprod _ HC HE).symm)⟩⟩)
      (fun _ _ g hg hM => by
        have := hg
        obtain ⟨H, hH, ⟨eM⟩⟩ := hM
        exact ⟨H, hH, ⟨(asIso g).symm ≪≫ eM⟩⟩)
      b hAhom
  have eY : DerivedCategory.Q.obj Y ≅ K := asIso (DerivedCategory.Q.map f) ≪≫ e.symm
  have hYflat : ∀ i : ℤ, IsConstructibleFlatModuleSheaf B X Λ (Y.X i) := fun i =>
    isConstructibleFlatModuleSheaf_of_isExtendedAffineShriekSum B X Λ (hterms i)
  have hcok : IsConstructibleFlatModuleSheaf B X Λ (cokernel (Y.d (a - 1) a) : 𝒜) := by
    have := isWeakSerreClass_isConstructibleModuleSheafProperty.{u, 0} B X Λ
    refine isConstructibleFlatModuleSheaf_of_projective_etaleModuleStalk.{u, 0} B X Λ _
      ((isConstructibleModuleSheafProperty.{u, u + 1, 0} B X Λ).prop_of_isColimit_cokernelCofork
        (colimit.isColimit _)
        (isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf B X Λ (hYflat (a - 1)))
        (isConstructibleModuleSheaf_of_isConstructibleFlatModuleSheaf B X Λ (hYflat a)))
      (hproj Y ⟨eY⟩ hY (fun n s =>
        finite_projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ _
          (hYflat n) s))
  have hYGE : Y.IsGE a := by
    rw [← DerivedCategory.isGE_Q_obj_iff]
    exact DerivedCategory.TStructure.t.isGE_of_iso eY.symm a
  have eOpCoker : Y.opcycles a ≅ (cokernel (Y.d (a - 1) a) : 𝒜) :=
    IsColimit.coconePointUniqueUpToIso
      (Y.opcyclesIsCokernel (a - 1) a (by simp)) (colimit.isColimit _)
  refine ⟨Y.truncGE a, inferInstance, ?_, fun i => ?_,
    ⟨(asIso (DerivedCategory.Q.map (Y.πTruncGE a))).symm ≪≫ eY⟩⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact (Y.isZero_of_isStrictlyLE b i hi).of_iso (Y.truncGEXIso a i (by omega))
  · rcases lt_trichotomy i a with hlt | heq | hgt
    · exact isConstructibleFlatModuleSheaf_of_isZero B Λ X _
        ((Y.truncGE a).isZero_of_isStrictlyGE a i hlt)
    · subst heq
      exact isConstructibleFlatModuleSheaf_congr B X Λ
        (eOpCoker.symm ≪≫ (Y.truncGEXIsoOpcycles i).symm) hcok
    · exact isConstructibleFlatModuleSheaf_congr B X Λ (Y.truncGEXIso a i hgt).symm (hYflat i)

end Stacks.EtaleCohomology

end
