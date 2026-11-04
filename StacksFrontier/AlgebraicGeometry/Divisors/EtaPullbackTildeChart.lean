module

public import StacksFrontier.AlgebraicGeometry.Divisors.EtaPullbackAffineChart
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBijectiveOfModel

/-!
# The comparison of décalages under a pullback, at the sheaf of a matrix complex on a spectrum

Let `R` be a ring and `C^•` a bounded complex of finite free `R`-modules, given in chosen bases,
with associated complex `C̃^•` of quasi-coherent `𝒪_{Spec R}`-modules.  This file identifies the
complex of global sections of `C̃^•`, as a complex over `Γ(Spec R, 𝒪)`, with the base change of
`C^•` along `R ≅ Γ(Spec R, 𝒪)`, deduces that `C̃^•` is a K-flat complex of flat modules, and
specializes the affine computation of
`Stacks.Divisors.Eta.isIso_divisorPullbackEtaKFlatComparison_of_isAffine` to it: for every
morphism `g : V ⟶ Spec R` from an affine scheme and every effective Cartier divisor `D` of
`Spec R` with equation `f` whose pullback along `g` is defined, if the determinantal ideals
`I_n(C^•, f)` are principal then the derived comparison of décalages at `C̃^•` is an isomorphism.

## Main results

* `Stacks.Divisors.Eta.tildeTopIso`: `Γ(Spec R, M̃) ≅ Γ(Spec R, 𝒪) ⊗_R M`, naturally in `M`.
* `Stacks.Divisors.Eta.sectionsTildeComplexIso`: the complex of global sections of `C̃^•`.
* `Stacks.Divisors.Eta.kFlat_tildeComplex`: `C̃^•` is K-flat.
* `Stacks.Divisors.Eta.isIso_divisorPullbackEtaKFlatComparison_tildeComplex`.
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.TensorSheafification.structureSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings

open Stacks.IdealTorsion.Eta (etaObj sectionsFunctor sectionsComplex)
open Stacks.AlgebraicGeometry.ModuleLimits (appTopHom)

universe u

namespace Stacks.Divisors.Eta

attribute [local instance] Stacks.Divisors.Eta.etaHasDerivedCategory

/-! ### Extension of scalars along a surjection -/

/-- **The extension of a bijective map along a surjective ring map is bijective**: the unit
`m ↦ 1 ⊗ m` of extension of scalars is then surjective. -/
theorem bijective_extendScalars_homEquiv_symm_of_bijective {A A' : Type u} [CommRing A]
    [CommRing A'] (φ : A →+* A') (hφ : Function.Surjective φ) {M : ModuleCat.{u} A}
    {P : ModuleCat.{u} A'} (v : M ⟶ (ModuleCat.restrictScalars φ).obj P)
    (hv : Function.Bijective v) :
    Function.Bijective (((ModuleCat.extendRestrictScalarsAdj φ).homEquiv M P).symm v) := by
  have hunit : Function.Surjective (Stacks.ModuleCat.extendScalarsUnit φ (M := M)) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul b m =>
      obtain ⟨a, rfl⟩ := hφ b
      exact ⟨a • m, (Stacks.ModuleCat.extendScalarsUnit_smul φ a m).trans
        (Stacks.ModuleCat.smul_extendScalarsUnit φ (φ a) m)⟩
    | add x y hx hy =>
      obtain ⟨m, rfl⟩ := hx
      obtain ⟨m', rfl⟩ := hy
      exact ⟨m + m', map_add _ _ _⟩
  have hcomp := Stacks.ModuleCat.extendScalars_homEquiv_symm_extendScalarsUnit φ v
  refine ⟨fun x y hxy => ?_, fun y => ?_⟩
  · obtain ⟨m, rfl⟩ := hunit x
    obtain ⟨m', rfl⟩ := hunit y
    rw [hcomp, hcomp] at hxy
    rw [hv.1 hxy]
  · obtain ⟨m, rfl⟩ := hv.2 y
    exact ⟨_, hcomp m⟩

/-! ### Global sections of the sheaf associated with a module -/

variable (R : CommRingCat.{u})

/-- The identification of `R` with the global functions on `Spec R`. -/
abbrev specΓInvHom : R →+* Γ(Spec R, ⊤) :=
  (Scheme.ΓSpecIso R).inv.hom

/-- The identification of `R` with the global functions on `Spec R` is bijective. -/
theorem bijective_specΓInvHom : Function.Bijective (specΓInvHom R) :=
  (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.bijective

/-- Restriction from the top open to itself is the identity on global functions. -/
theorem spec_presheaf_map_leTop_top (y : Γ(Spec R, ⊤)) :
    (Spec R).presheaf.map (TopologicalSpace.Opens.leTop (⊤ : (Spec R).Opens)).op y = y := by
  have h : (TopologicalSpace.Opens.leTop (⊤ : (Spec R).Opens)).op =
      𝟙 (Opposite.op (⊤ : (Spec R).Opens)) := rfl
  rw [h, CategoryTheory.Functor.map_id]
  rfl

variable {R}

/-- The canonical map `M ⟶ Γ(Spec R, M̃)`, linear over `R` acting on global sections through
`R ≅ Γ(Spec R, 𝒪)`. -/
def tildeTopUnit (M : ModuleCat.{u} R) :
    M ⟶ (ModuleCat.restrictScalars (specΓInvHom R)).obj
      (ModuleCat.of Γ(Spec R, ⊤) Γ(tilde M, ⊤)) :=
  ModuleCat.ofHom
    { toFun := (tilde.toOpen M ⊤).hom
      map_add' := map_add _
      map_smul' := fun c x => (map_smul (tilde.toOpen M ⊤).hom c x).trans (by
        exact congrArg (fun r : Γ(Spec R, ⊤) =>
            r • (show Γ(tilde M, ⊤) from (tilde.toOpen M ⊤).hom x))
          (spec_presheaf_map_leTop_top R (specΓInvHom R c))) }

/-- `Stacks.Divisors.Eta.tildeTopUnit M` sends `m` to the global section of `M̃` it defines. -/
theorem tildeTopUnit_apply (M : ModuleCat.{u} R) (m : M) :
    tildeTopUnit M m = (tilde.toOpen M ⊤).hom m := rfl

/-- **The global sections of `M̃` are the base change of `M` along `R ≅ Γ(Spec R, 𝒪)`.** -/
def tildeTopIso (M : ModuleCat.{u} R) :
    (ModuleCat.extendScalars (specΓInvHom R)).obj M ≅
      ModuleCat.of Γ(Spec R, ⊤) Γ(tilde M, ⊤) :=
  (LinearEquiv.ofBijective
    (((ModuleCat.extendRestrictScalarsAdj (specΓInvHom R)).homEquiv _ _).symm
      (tildeTopUnit M)).hom
    (bijective_extendScalars_homEquiv_symm_of_bijective _ (bijective_specΓInvHom R).2 _
      ((ConcreteCategory.isIso_iff_bijective (tilde.isoTop M).hom).mp
        (by rw [tilde.isoTop_hom]; exact inferInstance)))).toModuleIso

/-- `Stacks.Divisors.Eta.tildeTopIso M` sends `1 ⊗ m` to the global section of `M̃` defined by
`m`. -/
theorem tildeTopIso_hom_extendScalarsUnit (M : ModuleCat.{u} R) (m : M) :
    (tildeTopIso M).hom (Stacks.ModuleCat.extendScalarsUnit _ m) = (tilde.toOpen M ⊤).hom m :=
  Stacks.ModuleCat.extendScalars_homEquiv_symm_extendScalarsUnit _ (tildeTopUnit M) m

/-- The identification of global sections is natural. -/
theorem tildeTopIso_hom_naturality {M M' : ModuleCat.{u} R} (χ : M ⟶ M') :
    (tildeTopIso M).hom ≫ appTopHom ((tilde.functor R).map χ) =
      (ModuleCat.extendScalars (specΓInvHom R)).map χ ≫ (tildeTopIso M').hom := by
  refine Stacks.AlgebraicGeometry.ModuleLimits.extendScalars_hom_ext' _ fun m x hx => ?_
  subst hx
  refine (congrArg (appTopHom ((tilde.functor R).map χ))
    (tildeTopIso_hom_extendScalarsUnit M m)).trans ?_
  refine Eq.trans ?_ (congrArg (tildeTopIso M').hom (ModuleCat.ExtendScalars.map_tmul _ χ 1 m)).symm
  refine Eq.trans ?_ (tildeTopIso_hom_extendScalarsUnit M' (χ m)).symm
  exact ConcreteCategory.congr_hom (tilde.toOpen_map_app χ ⊤) m

/-! ### The sheaf of a matrix complex -/

/-- The complex of quasi-coherent `𝒪_{Spec R}`-modules associated with a bounded complex of
finite free `R`-modules. -/
abbrev tildeComplex (C : BoundedComplex R) :
    CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Spec R).toRingedSpace.sheaf)) ℤ :=
  ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj C.toCochainComplex

/-- **The complex of global sections of `C̃^•` is the base change of `C^•`** along
`R ≅ Γ(Spec R, 𝒪)`. -/
def sectionsTildeComplexIso (C : BoundedComplex R) :
    sectionsComplex (Spec R).toRingedSpace (tildeComplex C) ⊤ ≅
      (C.baseChange (specΓInvHom R)).toCochainComplex :=
  (HomologicalComplex.Hom.isoOfComponents (fun n => tildeTopIso (C.toCochainComplex.X n))
    (fun i j _ => tildeTopIso_hom_naturality (C.toCochainComplex.d i j))).symm ≪≫
    Stacks.Eta.DeterminantalIdeal.baseChangeCochainIso (specΓInvHom R) C

/-- The terms of `C̃^•` are quasi-coherent. -/
theorem isQuasicoherent_tildeComplex_X (C : BoundedComplex R) (n : ℤ) :
    ((tildeComplex C).X n).IsQuasicoherent :=
  (inferInstance : (tilde (C.toCochainComplex.X n)).IsQuasicoherent)

/-- **A complex of quasi-coherent modules on an affine scheme whose complex of global sections
is a bounded matrix complex has flat terms, vanishing where the matrix complex does**: the global
sections of each term are finite free, so the term is finite locally free. -/
theorem isFlat_and_isZero_of_sectionsComplex_iso {U : Scheme.{u}} [IsAffine U]
    (N : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf U.toRingedSpace.sheaf)) ℤ)
    (hqc : ∀ n : ℤ, (N.X n).IsQuasicoherent) (C : BoundedComplex Γ(U, ⊤))
    (eC : sectionsComplex U.toRingedSpace N ⊤ ≅ C.toCochainComplex) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := U.toRingedSpace.sheaf) (N.X n) ∧
      (C.rank n = 0 → IsZero (N.X n)) := by
  let ε : (sectionsFunctor U.toRingedSpace ⊤).obj (N.X n) ≃ₗ[U.toRingedSpace.presheaf.obj (op ⊤)]
      (Fin (C.rank n) → U.toRingedSpace.presheaf.obj (op ⊤)) :=
    ((HomologicalComplex.eval _ _ n).mapIso eC).toLinearEquiv
  have hfin : Module.Finite (U.toRingedSpace.presheaf.obj (op ⊤))
      ((sectionsFunctor U.toRingedSpace ⊤).obj (N.X n)) := Module.Finite.equiv ε.symm
  have hproj : Module.Projective (U.toRingedSpace.presheaf.obj (op ⊤))
      ((sectionsFunctor U.toRingedSpace ⊤).obj (N.X n)) := Module.Projective.of_equiv ε.symm
  have hqcn := hqc n
  refine ⟨?_, fun h0 => ?_⟩
  · have hlf : Module.IsFiniteLocallyFree (U.toRingedSpace.presheaf.obj (op ⊤))
        ((sectionsFunctor U.toRingedSpace ⊤).obj (N.X n)) :=
      (Module.isFiniteLocallyFree_iff_finite_projective _ _).mpr ⟨hfin, hproj⟩
    exact AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree _
      ((Scheme.Modules.isFiniteLocallyFree_iff _).mp
        (@Stacks.BlowUpComplexes.isFiniteLocallyFree_of_module_affineOpens U _ hqcn
          fun _ => ⟨⟨⊤, isAffineOpen_top U⟩, trivial, hlf⟩))
  · have hsub : Subsingleton ((sectionsFunctor U.toRingedSpace ⊤).obj (N.X n)) :=
      ⟨fun a b => ε.injective (funext fun i => (Fin.cast h0 i).elim0)⟩
    exact @isZero_of_subsingleton_sections_top U _ _ hqcn hsub

/-- Under the hypotheses of `isFlat_and_isZero_of_sectionsComplex_iso` the complex is K-flat: it
is a bounded above complex of flat modules. -/
theorem kFlat_of_sectionsComplex_iso {U : Scheme.{u}} [IsAffine U]
    (N : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf U.toRingedSpace.sheaf)) ℤ)
    (hqc : ∀ n : ℤ, (N.X n).IsQuasicoherent) (C : BoundedComplex Γ(U, ⊤))
    (eC : sectionsComplex U.toRingedSpace N ⊤ ≅ C.toCochainComplex) :
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex U.toRingedSpace N := by
  obtain ⟨n₀, hn₀⟩ := C.bounded.bddAbove
  refine AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.kFlat_of_boundedAbove_of_flat
    U.toRingedSpace _ ⟨n₀, (CochainComplex.isStrictlyLE_iff _ _).mpr fun i hi => ?_⟩
    fun i => (isFlat_and_isZero_of_sectionsComplex_iso N hqc C eC i).1
  refine (isFlat_and_isZero_of_sectionsComplex_iso N hqc C eC i).2 ?_
  by_contra h
  exact absurd (hn₀ h) (not_le.mpr hi)

/-- The terms of `C̃^•` are flat. -/
theorem isFlat_tildeComplex_X (C : BoundedComplex R) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := (Spec R).toRingedSpace.sheaf)
      ((tildeComplex C).X n) :=
  (isFlat_and_isZero_of_sectionsComplex_iso (tildeComplex C) (isQuasicoherent_tildeComplex_X C)
    _ (sectionsTildeComplexIso C) n).1

/-- **`C̃^•` is K-flat.** -/
theorem kFlat_tildeComplex (C : BoundedComplex R) :
    Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex (Spec R).toRingedSpace (tildeComplex C) :=
  kFlat_of_sectionsComplex_iso (tildeComplex C) (isQuasicoherent_tildeComplex_X C) _
    (sectionsTildeComplexIso C)

/-- **The derived comparison of décalages at the sheaf of a matrix complex.**  Let
`g : V ⟶ Spec R` be a morphism from an affine scheme, `D` an effective Cartier divisor on
`Spec R` with equation the image of `f ∈ R`, whose pullback along `g` is defined, and `C^•` a
bounded complex of finite free `R`-modules whose determinantal ideals `I_n(C^•, f)` are
principal.  Then `Lg^*[η_{ℐ_D} C̃^•] ⟶ [η_{ℐ_{g^{-1}D}}(g^* C̃^•)]` is an isomorphism. -/
theorem isIso_divisorPullbackEtaKFlatComparison_tildeComplex {V : Scheme.{u}} [IsAffine V]
    (g : V ⟶ Spec R) (D : (Spec R).IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    [Stacks.Divisors.IsPullbackDefined g D] (C : BoundedComplex R) (f : R)
    (hf : D.ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {specΓInvHom R f})
    (hI : ∀ n : ℤ, (idealI C f n).IsPrincipal) :
    IsIso (divisorPullbackEtaKFlatComparison g D (tildeComplex C) (isFlat_tildeComplex_X C)) := by
  refine isIso_divisorPullbackEtaKFlatComparison_of_isAffine g D (tildeComplex C)
    (isFlat_tildeComplex_X C) (isQuasicoherent_tildeComplex_X C) _ hf _
    (sectionsTildeComplexIso C) fun n => ?_
  obtain ⟨x, hx⟩ := hI n
  refine ⟨specΓInvHom R x, ?_⟩
  rw [← map_idealI_eq_idealI_baseChange, hx]
  exact (Ideal.map_span _ {x}).trans (by rw [Set.image_singleton])

end Stacks.Divisors.Eta

end
