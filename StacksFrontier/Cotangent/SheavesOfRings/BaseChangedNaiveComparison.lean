module

public import StacksFrontier.Cotangent.SheavesOfRings.NaiveComparisonCanonical
public import StacksFrontier.Cotangent.SheavesOfRings.PullbackCotangentComplex

/-!
# The base-changed cotangent complex and the base-changed naive cotangent complex

Let `g : A ⟶ B` and `h : B ⟶ D` be homomorphisms of sheaves of commutative rings on a site. The
first vertex of the fundamental triangle of the tower `A ⟶ B ⟶ D` (Tag 08SZ) is the degreewise
base change `L_{B/A} ⊗_B D`, `CategoryTheory.Sheaf.baseChangedCotangentComplex`. This file
compares it with the degreewise base change `NL_{B/A} ⊗_B D` of the naive cotangent complex.

The canonical map `L_{B/A} ⟶ NL_{B/A}` of Tag 08US is, in degree `-1`, a cokernel of the
differential into degree `-1`, and in degree `0` an isomorphism
(`CategoryTheory.Sheaf.isColimitNaiveComparisonFNegOne`,
`CategoryTheory.Sheaf.isIso_naiveComparison_f_zero`). Extension of scalars is a left adjoint, so
both properties survive base change: `NL_{B/A} ⊗_B D` is the truncation of `L_{B/A} ⊗_B D` in
degrees `-1` and `0`, and the base-changed comparison is an isomorphism on `H^{-1}` and `H⁰`. A
map of complexes out of `L_{B/A} ⊗_B D` into a complex concentrated in degrees `-1` and `0`
therefore factors uniquely through `NL_{B/A} ⊗_B D`; this is how the first displayed arrow of
Tag 08SZ followed by the comparison `L_{D/A} ⟶ NL_{D/A}` is read on the naive cotangent complex.

## Main definitions

* `CategoryTheory.Sheaf.baseChangedNaiveCotangentComplex`: `NL_{B/A} ⊗_B D`.
* `CategoryTheory.Sheaf.baseChangedNaiveComparison`: the base-changed comparison
  `L_{B/A} ⊗_B D ⟶ NL_{B/A} ⊗_B D`.
* `CategoryTheory.Sheaf.baseChangedNaiveMap`: the map `NL_{B/A} ⊗_B D ⟶ NL_{D/A}` through which
  the first displayed arrow of Tag 08SZ followed by the comparison of Tag 08US factors.

## Main results

* `CategoryTheory.Sheaf.baseChangedNaiveComparison_isIso_homologyMap_negOne` and
  `CategoryTheory.Sheaf.baseChangedNaiveComparison_isIso_homologyMap_zero`: the base-changed
  comparison is an isomorphism on `H^{-1}` and `H⁰`.
* `CategoryTheory.Sheaf.baseChangedNaiveComparison_comp_baseChangedNaiveMap`: the factorization.

## References

* [Stacks Project, Tag 08SZ](https://stacks.math.columbia.edu/tag/08SZ)
* [Stacks Project, Tag 08US](https://stacks.math.columbia.edu/tag/08US)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.Sheaf

/-! ### Truncations in degrees `-1` and `0` -/

section General

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {K L M : CochainComplex 𝒜 ℤ}

/-- The differential into degree `-1` followed by a map of complexes into a complex with no term in
degree `-2` is zero in degree `-1`. -/
private theorem d_comp_f_negOne_eq_zero (φ : K ⟶ L) (hL : IsZero (L.X (-2))) :
    K.d (-2) (-1) ≫ φ.f (-1) = 0 := by
  rw [← φ.comm, hL.eq_of_tgt (φ.f (-2)) 0, zero_comp]

/-- A map of complexes which is a cokernel of the incoming differential in degree `-1` and an
isomorphism in degree `0`, into a complex with no term in degree `-2`, is an isomorphism on
`H^{-1}`. -/
theorem isIso_homologyMap_negOne_of_isColimit (φ : K ⟶ L)
    (w : K.d (-2) (-1) ≫ φ.f (-1) = 0) (hφ : IsColimit (CokernelCofork.ofπ (φ.f (-1)) w))
    [IsIso (φ.f 0)] (hL : IsZero (L.X (-2))) :
    IsIso (HomologicalComplex.homologyMap φ (-1)) := by
  have hK := K.opcyclesIsCokernel (-2) (-1) (by simp)
  let e := hK.coconePointUniqueUpToIso hφ
  have he : K.pOpcycles (-1) ≫ e.hom = φ.f (-1) :=
    hK.comp_coconePointUniqueUpToIso_hom hφ WalkingParallelPair.one
  have hLp := L.isIso_pOpcycles (-2) (-1) (by simp) (hL.eq_of_src _ _)
  have hop : HomologicalComplex.opcyclesMap φ (-1) = e.hom ≫ L.pOpcycles (-1) := by
    rw [← cancel_epi (K.pOpcycles (-1)), HomologicalComplex.p_opcyclesMap, reassoc_of% he]
  have h₁ : IsIso (HomologicalComplex.opcyclesMap φ (-1)) := by
    rw [hop]
    infer_instance
  have h₃ : Mono (φ.f ((ComplexShape.up ℤ).next (-1))) := by
    rw [show (ComplexShape.up ℤ).next (-1) = 0 by simp]
    infer_instance
  exact ShortComplex.isIso_homologyMap_of_isIso_opcyclesMap_of_mono h₁ h₃

/-- A map of complexes which is an epimorphism in degree `-1` and an isomorphism in degree `0`,
between complexes with no term in degree `1`, is an isomorphism on `H⁰`. -/
theorem isIso_homologyMap_zero_of_epi (φ : K ⟶ L) [Epi (φ.f (-1))] [IsIso (φ.f 0)]
    (hK : IsZero (K.X 1)) :
    IsIso (HomologicalComplex.homologyMap φ 0) := by
  have h₁ : Epi ((HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) 0).map φ).τ₁ := by
    change Epi (φ.f ((ComplexShape.up ℤ).prev 0))
    rw [show (ComplexShape.up ℤ).prev 0 = -1 by simp]
    infer_instance
  have h₂ : IsIso ((HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) 0).map φ).τ₂ := by
    change IsIso (φ.f 0)
    infer_instance
  have h₃ : Mono ((HomologicalComplex.shortComplexFunctor 𝒜 (ComplexShape.up ℤ) 0).map φ).τ₃ := by
    change Mono (φ.f ((ComplexShape.up ℤ).next 0))
    rw [show (ComplexShape.up ℤ).next 0 = 1 by simp]
    exact hK.mono _
  exact ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono' _ h₁ h₂ h₃

/-- A map of complexes out of `K` into a complex concentrated in degrees `-1` and `0` factors
through a map `φ : K ⟶ L` which is a cokernel of the incoming differential in degree `-1` and an
isomorphism in degree `0`, `L` being concentrated in degrees `-1` and `0` as well. -/
theorem exists_factor_of_isColimit (φ : K ⟶ L)
    (w : K.d (-2) (-1) ≫ φ.f (-1) = 0) (hφ : IsColimit (CokernelCofork.ofπ (φ.f (-1)) w))
    [IsIso (φ.f 0)] (hL : ∀ n : ℤ, n ≠ -1 → n ≠ 0 → IsZero (L.X n))
    (ψ : K ⟶ M) (hM : ∀ n : ℤ, n ≠ -1 → n ≠ 0 → IsZero (M.X n)) :
    ∃ χ : L ⟶ M, φ ≫ χ = ψ := by
  have hepi : Epi φ := by
    refine HomologicalComplex.epi_of_epi_f φ (fun n => ?_)
    by_cases h₁ : n = -1
    · subst h₁
      exact epi_of_isColimit_cofork hφ
    by_cases h₀ : n = 0
    · subst h₀
      infer_instance
    · exact (hL n h₁ h₀).epi _
  have hψ : kernel.ι φ ≫ ψ = 0 := by
    ext n
    rw [HomologicalComplex.comp_f, HomologicalComplex.zero_f]
    by_cases h₁ : n = -1
    · subst h₁
      have hfac := hφ.fac (CokernelCofork.ofπ (ψ.f (-1))
        (d_comp_f_negOne_eq_zero ψ (hM (-2) (by decide) (by decide)))) WalkingParallelPair.one
      change φ.f (-1) ≫ _ = ψ.f (-1) at hfac
      rw [← hfac, ← Category.assoc, ← HomologicalComplex.comp_f, kernel.condition,
        HomologicalComplex.zero_f, zero_comp]
    by_cases h₀ : n = 0
    · subst h₀
      have h : (kernel.ι φ).f 0 ≫ φ.f 0 = 0 := by
        rw [← HomologicalComplex.comp_f, kernel.condition, HomologicalComplex.zero_f]
      rw [(cancel_mono (φ.f 0)).1 (h.trans (zero_comp).symm), zero_comp]
    · exact (hM n h₁ h₀).eq_of_tgt _ _
  exact ⟨(Abelian.epiIsCokernelOfKernel _ (kernelIsKernel φ)).desc (CokernelCofork.ofπ ψ hψ),
    (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel φ)).fac (CokernelCofork.ofπ ψ hψ)
      WalkingParallelPair.one⟩

end General

/-! ### The comparison with the naive cotangent complex, base-changed -/

section Tower

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A B D : Sheaf J CommRingCat.{max u v w}} (g : A ⟶ B) (h : B ⟶ D)

/-- The differential of `L_{B/A}` into degree `-1`, followed by the canonical map
`L_{B/A} ⟶ NL_{B/A}` of Tag 08US in degree `-1`, is zero. -/
theorem canonicalNaiveComparison_d :
    (cotangentComplex.{u, v, w} J g).d (-2) (-1) ≫ (canonicalNaiveComparison.{u, v, w} J g).f (-1) =
      0 := by
  exact d_comp_f_negOne_eq_zero _
    (Stacks.SheafOfModules.naiveCotangentComplex_isZero_X J A B g (-2) (by decide) (by decide))

/-- The canonical map `L_{B/A} ⟶ NL_{B/A}` of Tag 08US is, in degree `-1`, a cokernel of the
differential of `L_{B/A}` into degree `-1`. -/
def isColimitCanonicalNaiveComparison :
    IsColimit (CokernelCofork.ofπ ((canonicalNaiveComparison.{u, v, w} J g).f (-1))
      (canonicalNaiveComparison_d.{u, v, w} J g)) :=
  IsColimit.ofIsoColimit (isColimitNaiveComparisonFNegOne.{u, v, w} J g)
    (Cofork.ext (((HomologicalComplex.eval _ _ (-1)).mapIso
        (naiveCotangentComplexIsoCanonical.{u, v, w} J g)))
      (by
        change (naiveComparison.{u, v, w} J g).f (-1) ≫
            (naiveCotangentComplexIsoCanonical.{u, v, w} J g).hom.f (-1) =
          (canonicalNaiveComparison.{u, v, w} J g).f (-1)
        rfl))

/-- The canonical map `L_{B/A} ⟶ NL_{B/A}` of Tag 08US is an isomorphism in degree `0`. -/
instance isIso_canonicalNaiveComparison_f_zero :
    IsIso ((canonicalNaiveComparison.{u, v, w} J g).f 0) := by
  change IsIso ((naiveComparison.{u, v, w} J g).f 0 ≫
    (naiveCotangentComplexIsoCanonical.{u, v, w} J g).hom.f 0)
  infer_instance

/-- `NL_{B/A} ⊗_B D`, the degreewise base change of the naive cotangent complex of Tag 08TW. -/
abbrev baseChangedNaiveCotangentComplex : CochainComplex (targetModules.{u, v, w} J D) ℤ :=
  ((towerExtendScalars.{u, v, w} J h).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (Stacks.SheafOfModules.naiveCotangentComplex.{v, u, max u v w, u} J A B g)

/-- The comparison `L_{B/A} ⊗_B D ⟶ NL_{B/A} ⊗_B D` read on the extended complex. -/
abbrev extendedNaiveComparison :
    ((towerExtendScalars.{u, v, w} J h).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex.{u, v, w} J g) ⟶ baseChangedNaiveCotangentComplex.{u, v, w} J g h :=
  ((towerExtendScalars.{u, v, w} J h).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (canonicalNaiveComparison.{u, v, w} J g)

/-- The differential of `L_{B/A} ⊗_B D` into degree `-1`, followed by the base-changed
comparison in degree `-1`, is zero. -/
theorem extendedNaiveComparison_d :
    (((towerExtendScalars.{u, v, w} J h).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (cotangentComplex.{u, v, w} J g)).d (-2) (-1) ≫
      (extendedNaiveComparison.{u, v, w} J g h).f (-1) = 0 := by
  change (towerExtendScalars.{u, v, w} J h).map _ ≫ (towerExtendScalars.{u, v, w} J h).map _ = 0
  rw [← Functor.map_comp, canonicalNaiveComparison_d, Functor.map_zero]

/-- The base-changed comparison is, in degree `-1`, a cokernel of the incoming differential:
extension of scalars is a left adjoint. -/
def isColimitExtendedNaiveComparison :
    IsColimit (CokernelCofork.ofπ ((extendedNaiveComparison.{u, v, w} J g h).f (-1))
      (extendedNaiveComparison_d.{u, v, w} J g h)) :=
  have : (towerExtendScalars.{u, v, w} J h).IsLeftAdjoint :=
    (towerExtendRestrictAdjunction.{u, v, w} J h).isLeftAdjoint
  CokernelCofork.mapIsColimit _ (isColimitCanonicalNaiveComparison.{u, v, w} J g)
    (towerExtendScalars.{u, v, w} J h)

/-- The base-changed comparison is an isomorphism in degree `0`. -/
instance isIso_extendedNaiveComparison_f_zero :
    IsIso ((extendedNaiveComparison.{u, v, w} J g h).f 0) := by
  change IsIso ((towerExtendScalars.{u, v, w} J h).map
    ((canonicalNaiveComparison.{u, v, w} J g).f 0))
  infer_instance

/-- The base-changed comparison is an epimorphism in degree `-1`. -/
instance epi_extendedNaiveComparison_f_negOne :
    Epi ((extendedNaiveComparison.{u, v, w} J g h).f (-1)) :=
  epi_of_isColimit_cofork (isColimitExtendedNaiveComparison.{u, v, w} J g h)

/-- `NL_{B/A} ⊗_B D` is concentrated in degrees `-1` and `0`. -/
theorem baseChangedNaiveCotangentComplex_isZero_X (n : ℤ) (h₁ : n ≠ -1) (h₀ : n ≠ 0) :
    IsZero ((baseChangedNaiveCotangentComplex.{u, v, w} J g h).X n) :=
  (towerExtendScalars.{u, v, w} J h).map_isZero
    (Stacks.SheafOfModules.naiveCotangentComplex_isZero_X J A B g n h₁ h₀)

/-- **The base-changed comparison** `L_{B/A} ⊗_B D ⟶ NL_{B/A} ⊗_B D`. -/
def baseChangedNaiveComparison :
    baseChangedCotangentComplex.{u, v, w} J g h ⟶
      baseChangedNaiveCotangentComplex.{u, v, w} J g h :=
  (towerExtendScalarsCotangentComplexIso.{u, v, w} J g h).inv ≫
    extendedNaiveComparison.{u, v, w} J g h

/-- The base-changed comparison is an isomorphism on `H^{-1}`. -/
theorem baseChangedNaiveComparison_isIso_homologyMap_negOne :
    IsIso (HomologicalComplex.homologyMap (baseChangedNaiveComparison.{u, v, w} J g h) (-1)) := by
  have := isIso_homologyMap_negOne_of_isColimit (extendedNaiveComparison.{u, v, w} J g h)
    (extendedNaiveComparison_d.{u, v, w} J g h) (isColimitExtendedNaiveComparison.{u, v, w} J g h)
    (baseChangedNaiveCotangentComplex_isZero_X.{u, v, w} J g h (-2) (by decide) (by decide))
  rw [baseChangedNaiveComparison, HomologicalComplex.homologyMap_comp]
  infer_instance

/-- The base-changed comparison is an isomorphism on `H⁰`. -/
theorem baseChangedNaiveComparison_isIso_homologyMap_zero :
    IsIso (HomologicalComplex.homologyMap (baseChangedNaiveComparison.{u, v, w} J g h) 0) := by
  have := isIso_homologyMap_zero_of_epi (extendedNaiveComparison.{u, v, w} J g h)
    ((towerExtendScalars.{u, v, w} J h).map_isZero
      (cotangentComplex_isZero_pos.{u, v, w} J g 1 (by decide)))
  rw [baseChangedNaiveComparison, HomologicalComplex.homologyMap_comp]
  infer_instance

/-- The first displayed arrow of Tag 08SZ followed by the comparison `L_{D/A} ⟶ NL_{D/A}` of
Tag 08US factors through the base-changed comparison. -/
theorem exists_baseChangedNaiveMap :
    ∃ χ : baseChangedNaiveCotangentComplex.{u, v, w} J g h ⟶
        Stacks.SheafOfModules.naiveCotangentComplex.{v, u, max u v w, u} J A D (g ≫ h),
      baseChangedNaiveComparison.{u, v, w} J g h ≫ χ =
        towerCotangentBaseChange.{u, v, w} J g h ≫
          canonicalNaiveComparison.{u, v, w} J (g ≫ h) := by
  obtain ⟨χ, hχ⟩ := exists_factor_of_isColimit (extendedNaiveComparison.{u, v, w} J g h)
    (extendedNaiveComparison_d.{u, v, w} J g h) (isColimitExtendedNaiveComparison.{u, v, w} J g h)
    (baseChangedNaiveCotangentComplex_isZero_X.{u, v, w} J g h)
    ((towerExtendScalarsCotangentComplexIso.{u, v, w} J g h).hom ≫
      towerCotangentBaseChange.{u, v, w} J g h ≫ canonicalNaiveComparison.{u, v, w} J (g ≫ h))
    (Stacks.SheafOfModules.naiveCotangentComplex_isZero_X J A D (g ≫ h))
  exact ⟨χ, by rw [baseChangedNaiveComparison, Category.assoc, hχ, Iso.inv_hom_id_assoc]⟩

/-- **The map `NL_{B/A} ⊗_B D ⟶ NL_{D/A}`** through which the first displayed arrow of Tag 08SZ
followed by the comparison of Tag 08US factors. -/
def baseChangedNaiveMap :
    baseChangedNaiveCotangentComplex.{u, v, w} J g h ⟶
      Stacks.SheafOfModules.naiveCotangentComplex.{v, u, max u v w, u} J A D (g ≫ h) :=
  (exists_baseChangedNaiveMap.{u, v, w} J g h).choose

/-- The base-changed comparison followed by `CategoryTheory.Sheaf.baseChangedNaiveMap` is the
first displayed arrow of Tag 08SZ followed by the comparison `L_{D/A} ⟶ NL_{D/A}` of Tag 08US. -/
theorem baseChangedNaiveComparison_comp_baseChangedNaiveMap :
    baseChangedNaiveComparison.{u, v, w} J g h ≫ baseChangedNaiveMap.{u, v, w} J g h =
      towerCotangentBaseChange.{u, v, w} J g h ≫ canonicalNaiveComparison.{u, v, w} J (g ≫ h) :=
  (exists_baseChangedNaiveMap.{u, v, w} J g h).choose_spec

end Tower

end CategoryTheory.Sheaf

end
