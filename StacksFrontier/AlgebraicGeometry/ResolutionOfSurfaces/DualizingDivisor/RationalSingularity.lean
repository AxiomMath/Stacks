module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedGlobalSectionsSmul
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.DivisorSections
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.DualizingComplexConcentration
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.DualizingModuleDepth
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.FirstCohomologyTorsion
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ResolutionFirstCohomology
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.DerivedPushforwardDegreeZero
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.GrauertRiemenschneiderFinite
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ModificationCurve

/-!
# The first sentence of Tag 0EA2

Let `A` be a Noetherian normal local Nagata domain of dimension two with a dualizing module
`ω_A` and a resolution of singularities `f : X ⟶ Spec(A)`, and let `ω_X = H^{-2}(f^×(ω_A[2]))`
([Stacks, Tag 0B4R]). This file proves that `ω_X ≅ 𝒪_X(E)`, for an effective Cartier divisor `E`
supported on the exceptional fibre, forces `A` to define a rational singularity.

## Main results

* `AlgebraicGeometry.DualizingDivisor.definesRationalSingularity_of_relativeDualizingModule_iso`:
  the first sentence of [Stacks, Tag 0EA2].
* `AlgebraicGeometry.DualizingDivisor.nonempty_iso_of_relativeDualizingModule_iso`: under the
  same hypotheses `ω_A ≅ A`.
* `AlgebraicGeometry.DualizingDivisor.subsingleton_rightDerived_one_and_nonempty_iso`: the core,
  for a modification with normal source: `H¹(X, 𝒪_X) = 0` and `ω_A ≅ A`.

## Implementation notes

The source computes `Rf_*ω_X = ω_A` from the trace map and Grauert–Riemenschneider and dualizes.
Here the dual statement is proved directly: `K = RΓ(X, 𝒪_X[2])` has cohomology `A` in degree
`-2` and the torsion module `H¹(X, 𝒪_X)` in degree `-1`, duality identifies
`Hom(K, ω_A[2])` with `Hom(𝒪_X, ω_X) = Hom(𝒪_X, 𝒪_X(E)) = A`, and
`Stacks.PurityRamification.subsingleton_homology_succ_of_forall_eq_smul` with [Stacks, Tag 0AXC]
concludes. The morphisms are stated over `Y : Over (Spec A)` so that the `A`-linear structure
`modulesLinear A Y` on `𝒪_X`-modules applies.

## References

* [Stacks Project, Tag 0EA2](https://stacks.math.columbia.edu/tag/0EA2)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0AXC](https://stacks.math.columbia.edu/tag/0AXC)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite IsLocalRing DerivedCategory Stacks.Duality

universe u

namespace AlgebraicGeometry.DualizingDivisor

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A]
  (Y : Over (Spec (.of A))) [IsProper Y.hom] [CompactSpace Y.left] [QuasiSeparatedSpace Y.left]

/-- `RΓ(X, 𝒪_X[2])`, the complex `K` of the proof of [Stacks, Tag 0EA2]. -/
abbrev derivedSectionsUnitShift : DerivedCategory (ModuleCat.{u} A) :=
  (derivedGlobalSectionsOver Y.hom).obj
    ((singleFunctor Y.left.Modules (-2)).obj (Stacks.Ample.unitModule Y.left))

/-- **Duality on `𝒪_X[2]`.** When `ω_X^• = f^×(ω_A[2])` lies in degrees `≥ -2`, maps
`𝒪_X ⟶ H^{-2}(ω_X^•)` are maps `𝒪_X[2] ⟶ ω_X^•`, which by the adjunction `Rf_* ⊣ f^×` are maps
`RΓ(X, 𝒪_X[2]) ⟶ ω_A[2]`. -/
def unitHomDualityEquiv (ωA : ModuleCat.{u} A) [(dualizingComplex Y.hom ωA).obj.IsGE (-2)] :
    (Stacks.Ample.unitModule Y.left ⟶
        (homologyFunctor Y.left.Modules (-2)).obj (dualizingComplex Y.hom ωA).obj) ≃
      (derivedSectionsUnitShift Y ⟶ (singleFunctor (ModuleCat.{u} A) (-2)).obj ωA) :=
  (Equiv.ofBijective _ (bijective_homologyFromSingle_of_isGE (Stacks.Ample.unitModule Y.left)
    (dualizingComplex Y.hom ωA).obj (-2))).symm.trans
    ((ObjectProperty.fullyFaithfulι _).homEquiv.symm.trans
      (dualityHomEquiv Y.hom (singleQuasiCoherent (Stacks.Ample.unitModule Y.left) (-2)) _))

/-- An explicit formula for `unitHomDualityEquiv` as the composite of its three bijections. -/
theorem unitHomDualityEquiv_apply (ωA : ModuleCat.{u} A) [(dualizingComplex Y.hom ωA).obj.IsGE (-2)]
    (g : Stacks.Ample.unitModule Y.left ⟶
      (homologyFunctor Y.left.Modules (-2)).obj (dualizingComplex Y.hom ωA).obj) :
    unitHomDualityEquiv Y ωA g = dualityHomEquiv Y.hom
      (singleQuasiCoherent (Stacks.Ample.unitModule Y.left) (-2))
      ((singleFunctor (ModuleCat.{u} A) (-2)).obj ωA)
      ((ObjectProperty.fullyFaithfulι _).preimage
        (X := singleQuasiCoherent (Stacks.Ample.unitModule Y.left) (-2))
        (Y := dualizingComplex Y.hom ωA) ((Equiv.ofBijective _
        (bijective_homologyFromSingle_of_isGE (Stacks.Ample.unitModule Y.left)
          (dualizingComplex Y.hom ωA).obj (-2))).symm g)) := rfl

/-- `homologyFromSingle` is natural in the source object. -/
theorem homologyFromSingle_single_map_comp {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] {P P' : C} (u : P' ⟶ P) (Y : DerivedCategory C) (q : ℤ)
    (h : (singleFunctor C q).obj P ⟶ Y) :
    homologyFromSingle P' Y q ((singleFunctor C q).map u ≫ h) =
      u ≫ homologyFromSingle P Y q h := by
  rw [homologyFromSingle_apply, homologyFromSingle_apply, Functor.map_comp, ← Category.assoc,
    ← Category.assoc]
  congr 1
  exact ((singleFunctorCompHomologyFunctorIso C q).inv.naturality u).symm

/-- **Linearity of the duality bijection.** Precomposing with multiplication by `b ∈ A` on `𝒪_X`
multiplies the corresponding map `RΓ(X, 𝒪_X[2]) ⟶ ω_A[2]` by `b`. -/
theorem unitHomDualityEquiv_smul (ωA : ModuleCat.{u} A) [(dualizingComplex Y.hom ωA).obj.IsGE (-2)]
    (b : A) (g : Stacks.Ample.unitModule Y.left ⟶
      (homologyFunctor Y.left.Modules (-2)).obj (dualizingComplex Y.hom ωA).obj) :
    letI := modulesLinear A Y
    unitHomDualityEquiv Y ωA ((b • 𝟙 (Stacks.Ample.unitModule Y.left)) ≫ g) =
      b • unitHomDualityEquiv Y ωA g := by
  let := modulesLinear A Y
  let φ := Equiv.ofBijective _ (bijective_homologyFromSingle_of_isGE
    (Stacks.Ample.unitModule Y.left) (dualizingComplex Y.hom ωA).obj (-2))
  set h := φ.symm g with hh
  have h1 : φ.symm ((b • 𝟙 (Stacks.Ample.unitModule Y.left)) ≫ g) =
      (singleFunctor Y.left.Modules (-2)).map (b • 𝟙 (Stacks.Ample.unitModule Y.left)) ≫ h := by
    rw [Equiv.symm_apply_eq]
    show _ = homologyFromSingle _ _ (-2) _
    rw [homologyFromSingle_single_map_comp, hh]
    exact congrArg _ (φ.apply_symm_apply g).symm
  rw [unitHomDualityEquiv_apply, unitHomDualityEquiv_apply, h1, ← hh]
  refine (congrArg (dualityHomEquiv Y.hom
      (singleQuasiCoherent (Stacks.Ample.unitModule Y.left) (-2))
      ((singleFunctor (ModuleCat.{u} A) (-2)).obj ωA))
    ((ObjectProperty.fullyFaithfulι _).preimage_comp
      (X := singleQuasiCoherent (Stacks.Ample.unitModule Y.left) (-2))
      (Y := singleQuasiCoherent (Stacks.Ample.unitModule Y.left) (-2))
      ((singleFunctor Y.left.Modules (-2)).map (b • 𝟙 (Stacks.Ample.unitModule Y.left)))
        h)).trans ?_
  rw [dualityHomEquiv_comp]
  show (derivedGlobalSectionsOver Y.hom).map
    ((singleFunctor Y.left.Modules (-2)).map (b • 𝟙 (Stacks.Ample.unitModule Y.left))) ≫ _ = _
  rw [Functor.map_smul, CategoryTheory.Functor.map_id,
    derivedGlobalSectionsOver_map_smul_id_of_hasDerivedCategory]
  exact (Linear.smul_comp _ _ _ _ _ _).trans (congrArg (b • ·) (Category.id_comp _))

/-- **`Hom(RΓ(X, 𝒪_X[2]), ω_A[2])` is free of rank one** when `H^{-2}(ω_X^•) ≅ 𝒪_X(E)` for an
effective Cartier divisor `E` over the closed point: by duality it is `Hom(𝒪_X, 𝒪_X(E))`, which
is `A · s_E` freely (`exists_eq_smul_canonicalHom`, `eq_zero_of_smul_canonicalHom_eq_zero`). -/
theorem hom_derivedSectionsUnitShift_free (hdim : ringKrullDim A = 2) (hY : IsModification Y.hom)
    (ωA : ModuleCat.{u} A) [(dualizingComplex Y.hom ωA).obj.IsGE (-2)]
    (E : Y.left.IdealSheafData) (hE : ∀ x : Y.left, x ∈ E.support → Y.hom x = closedPoint A)
    (e : (homologyFunctor Y.left.Modules (-2)).obj (dualizingComplex Y.hom ωA).obj ≅
      divisorSheaf E) :
    (∀ χ : derivedSectionsUnitShift Y ⟶ (singleFunctor (ModuleCat.{u} A) (-2)).obj ωA,
      ∃ b : A, χ = b • unitHomDualityEquiv Y ωA (canonicalHom E ≫ e.inv)) ∧
    ∀ b : A, b • unitHomDualityEquiv Y ωA (canonicalHom E ≫ e.inv) = 0 → b = 0 := by
  let := modulesLinear A Y
  have key : ∀ b : A, b • unitHomDualityEquiv Y ωA (canonicalHom E ≫ e.inv) =
      unitHomDualityEquiv Y ωA ((b • canonicalHom E) ≫ e.inv) := by
    intro b
    rw [← unitHomDualityEquiv_smul, ← Category.assoc, Linear.smul_comp, Category.id_comp]
  refine ⟨fun χ => ?_, fun b hb => ?_⟩
  · obtain ⟨b, hb⟩ := exists_eq_smul_canonicalHom hdim Y hY E hE
      ((unitHomDualityEquiv Y ωA).symm χ ≫ e.hom)
    refine ⟨b, ?_⟩
    rw [key, ← hb, Category.assoc, e.hom_inv_id, Category.comp_id, Equiv.apply_symm_apply]
  · apply eq_zero_of_smul_canonicalHom_eq_zero hdim Y hY E hE b
    have h0 : unitHomDualityEquiv Y ωA ((b • canonicalHom E) ≫ e.inv) =
        unitHomDualityEquiv Y ωA (((0 : A) • canonicalHom E) ≫ e.inv) := by
      rw [← key, ← key, hb, zero_smul]
    simpa only [Category.assoc, e.inv_hom_id, Category.comp_id, zero_smul] using
      congrArg (· ≫ e.hom) ((unitHomDualityEquiv Y ωA).injective h0)

/-- A finite module all of whose elements are killed by elements outside a prime `p` is killed
by a single element outside `p`. -/
theorem exists_notMem_forall_smul_eq_zero {M : Type*} [AddCommGroup M] [Module A M]
    [Module.Finite A M] (p : Ideal A) [p.IsPrime] (h : ∀ x : M, ∃ a : A, a ∉ p ∧ a • x = 0) :
    ∃ c : A, c ∉ p ∧ ∀ x : M, c • x = 0 := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := A) (M := M))
  choose a ha using h
  refine ⟨∏ x ∈ s, a x, Submonoid.prod_mem p.primeCompl fun x _ => (ha x).1, fun x => ?_⟩
  have hx : x ∈ Submodule.span A (s : Set M) := hs ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
    classical
    rw [← Finset.prod_erase_mul s a hy, mul_smul, (ha y).2, smul_zero]
  | zero => exact smul_zero _
  | add y z _ _ hy hz => rw [smul_add, hy, hz, add_zero]
  | smul b y _ hy => rw [smul_comm, hy, smul_zero]

/-- `H^i(RΓ(X, 𝒪_X[2])) = H^{i+2}(X, 𝒪_X)`. -/
def homologyDerivedSectionsUnitShiftIso (i j : ℤ) (h : -(-2) + i = j) :
    (homologyFunctor (ModuleCat.{u} A) i).obj (derivedSectionsUnitShift Y) ≅
      (homologyFunctor (ModuleCat.{u} A) j).obj
        (derivedSections Y.hom (Stacks.Ample.unitModule Y.left)) :=
  (homologyFunctor _ i).mapIso (derivedSectionsSingleIso Y.hom _ (-2)) ≪≫
    ((homologyFunctor _ 0).shiftIso (-(-2)) i j h).app _

/-- `RΓ(X, 𝒪_X[2])` lies in degrees `≥ -2`. -/
theorem isGE_derivedSectionsUnitShift : (derivedSectionsUnitShift Y).IsGE (-2) := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact (DerivedCategory.isZero_of_isGE _ 0 (-(-2) + i) (by omega)).of_iso
    (homologyDerivedSectionsUnitShiftIso Y i _ rfl)

/-- For a modification of a normal local domain of dimension `2`, `RΓ(X, 𝒪_X[2])` lies in degrees
`≤ -1`. -/
theorem isLE_derivedSectionsUnitShift (hdim : ringKrullDim A = 2) [IsNormal Y.left]
    (hY : IsModification Y.hom) : (derivedSectionsUnitShift Y).IsLE (-1) := by
  have := isLE_derivedSections hdim Y.hom hY (Stacks.Ample.unitModule Y.left)
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact (DerivedCategory.isZero_of_isLE _ 1 (-(-2) + i) (by omega)).of_iso
    (homologyDerivedSectionsUnitShiftIso Y i _ rfl)

/-- `H^{-2}(RΓ(X, 𝒪_X[2])) = Γ(X, 𝒪_X) = A` for a modification of a normal local domain. -/
def homologyDerivedSectionsUnitShiftIsoBase (hY : IsModification Y.hom) :
    (homologyFunctor (ModuleCat.{u} A) (-2)).obj (derivedSectionsUnitShift Y) ≅
      ModuleCat.of A A :=
  homologyDerivedSectionsUnitShiftIso Y (-2) 0 (by norm_num) ≪≫
    homologyDerivedSectionsIso Y.hom (Stacks.Ample.unitModule Y.left) 0 ≪≫
    (secsOver Y.hom).rightDerivedZeroIsoSelf.app (SheafOfModules.unit Y.left.ringCatSheaf) ≪≫
    modificationSecsOverUnitIso Y.hom hY

/-- `H¹(X, 𝒪_X)` with its `A`-module structure, as the base-module form of the first cohomology
of the structure sheaf. -/
def rightDerivedOneUnitIso :
    ((globalSectionsOver Y.hom).rightDerived 1).obj (SheafOfModules.unit Y.left.ringCatSheaf) ≅
      firstCohomologySheafAsBaseModule Y.left Y.hom (SheafOfModules.unit Y.left.ringCatSheaf) :=
  ((Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
    (Stacks.Cohomology.sectionsFunctor Y.left ⊤)
    (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ Y.hom.appTop).hom)
    (globalSectionsOver Y.hom) (Iso.refl _) 1).app _).symm

/-- **The core of the first sentence of [Stacks, Tag 0EA2].** Let `A` be a Noetherian normal
local domain of dimension two, `f : X ⟶ Spec(A)` a modification with `X` normal, and `ω_A` a
finite `A`-module of depth two such that `ω_X^• = f^×(ω_A[2])` has `H^{-2}(ω_X^•) ≅ 𝒪_X(E)` for an
effective Cartier divisor `E` over the closed point. Then `H¹(X, 𝒪_X) = 0` and `ω_A ≅ A`.

This is `Stacks.PurityRamification.subsingleton_homology_succ_of_forall_eq_smul` at
`K = RΓ(X, 𝒪_X[2])`, `n = -2`, `N = ω_A`: `K` has cohomology `A` in degree `-2` and the torsion
module `H¹(X, 𝒪_X)` in degree `-1`; `Hom(K, ω_A[2])` is free of rank one by duality and the
Hartogs step; and every map `κ[1] ⟶ K` vanishes by [Stacks, Tag 0AXC]. -/
theorem subsingleton_rightDerived_one_and_nonempty_iso (hdim : ringKrullDim A = 2)
    [IsNormal Y.left] (hY : IsModification Y.hom) (ωA : ModuleCat.{u} A) [Module.Finite A ωA]
    (hdepth : (2 : ℕ∞) ≤ Module.depth A (maximalIdeal A) ωA)
    (E : Y.left.IdealSheafData) (hE : ∀ x : Y.left, x ∈ E.support → Y.hom x = closedPoint A)
    (e : (homologyFunctor Y.left.Modules (-2)).obj (dualizingComplex Y.hom ωA).obj ≅
      divisorSheaf E) :
    Subsingleton (((globalSectionsOver Y.hom).rightDerived 1).obj
        (SheafOfModules.unit Y.left.ringCatSheaf)) ∧
      Nonempty (ωA ≅ ModuleCat.of A A) := by
  have hdepth1 : (1 : ℕ∞) ≤ Module.depth A (maximalIdeal A) ωA := le_trans (by norm_num) hdepth
  have : (dualizingComplex Y.hom ωA).obj.IsGE (-2) :=
    isGE_dualizingComplex Y.hom hdim hY ωA hdepth1
  have := isGE_derivedSectionsUnitShift Y
  have : (derivedSectionsUnitShift Y).IsLE (-2 + 1) := isLE_derivedSectionsUnitShift Y hdim hY
  obtain ⟨hgen, hfree⟩ := hom_derivedSectionsUnitShift_free Y hdim hY ωA E hE e
  let e1 := homologyDerivedSectionsUnitShiftIso Y (-2 + 1) 1 (by norm_num) ≪≫
    homologyDerivedSectionsIso Y.hom (Stacks.Ample.unitModule Y.left) 1
  have : Module.Finite A (((globalSectionsOver Y.hom).rightDerived 1).obj
      (SheafOfModules.unit Y.left.ringCatSheaf)) := by
    have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
    have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
    have := Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit (X := Y.left)
    have := moduleFinite_firstCohomologySheafAsBaseModule Y.hom
      (SheafOfModules.unit Y.left.ringCatSheaf)
    exact Module.Finite.equiv (rightDerivedOneUnitIso Y).toLinearEquiv.symm
  have : Module.Finite A ((homologyFunctor (ModuleCat.{u} A) (-2 + 1)).obj
      (derivedSectionsUnitShift Y)) := Module.Finite.equiv e1.toLinearEquiv.symm
  have hM : ∀ (p : Ideal A) (_ : p.IsPrime), p ≠ maximalIdeal A →
      ∃ c : A, c ∉ p ∧ ∀ x : (homologyFunctor (ModuleCat.{u} A) (-2 + 1)).obj
        (derivedSectionsUnitShift Y), c • x = 0 := by
    intro p hp hpm
    refine exists_notMem_forall_smul_eq_zero p fun x => ?_
    obtain ⟨a, ha, hax⟩ := exists_smul_eq_zero_rightDerived_one hdim Y.hom hY
      (Stacks.Ample.unitModule Y.left) p hpm (e1.hom x)
    refine ⟨a, ha, e1.toLinearEquiv.injective ?_⟩
    rw [map_smul, map_zero]
    exact hax
  have hκ : ∀ g : (singleFunctor (ModuleCat.{u} A) (-2 + 1)).obj
      (ModuleCat.of A (ResidueField A)) ⟶ derivedSectionsUnitShift Y, g = 0 := by
    intro g
    let V := VanishingSituation.ofModification A hdim Y.hom hY
    have : IsNormal V.X := ‹IsNormal Y.left›
    rw [← cancel_mono (derivedSectionsSingleIso Y.hom (Stacks.Ample.unitModule Y.left) (-2)).hom,
      Limits.zero_comp]
    exact V.hom_singleFunctor_residueField_shift_eq_zero (-2)
      (g ≫ (derivedSectionsSingleIso Y.hom (Stacks.Ample.unitModule Y.left) (-2)).hom)
  obtain ⟨hsub, hiso⟩ := Stacks.PurityRamification.subsingleton_homology_succ_of_forall_eq_smul
    (by rw [hdim]) (derivedSectionsUnitShift Y) (-2) (homologyDerivedSectionsUnitShiftIsoBase Y hY)
    hM ωA hdepth1 _ hgen hfree hκ
  exact ⟨e1.toLinearEquiv.toEquiv.subsingleton_congr.mp hsub, hiso⟩

/-- The two conclusions drawn in the proof of [Stacks, Tag 0EA2] from `ω_X ≅ 𝒪_X(E)`:
`H¹(X, 𝒪_X) = 0` and `ω_A ≅ A`. The hypotheses are those of the first sentence of the tag; the
instances `[IsProper f]`, `[CompactSpace X]`, `[QuasiSeparatedSpace X]` are consequences of
`IsResolution f` (a resolution is proper, and `Spec(A)` is quasi-compact and separated); they are
what this library needs to form `f^×` and hence `ω_X`. -/
theorem isZero_structureSheafH1_and_nonempty_iso (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsNormalDomain A] (hdim : ringKrullDim A = 2)
    (ωA : ModuleCat.{u} A) (hω : Stacks.Duality.IsDualizingRingModule A ωA)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] [CompactSpace X]
    [QuasiSeparatedSpace X] (hf : IsResolution f)
    (E : X.IdealSheafData) (hE : ∀ x : X, x ∈ E.support → f x = closedPoint A)
    (e : Nonempty (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
      ((derivedTilde (CommRingCat.of A)).obj ((singleFunctor (ModuleCat.{u} A) (-2)).obj ωA)) ≅
        (Stacks.Divisors.invertibleSheaf' E : X.Modules))) :
    Limits.IsZero (structureSheafH1 X) ∧ Nonempty (ωA ≅ ModuleCat.of A A) := by
  obtain ⟨e⟩ := e
  have : IsNormal X := isNormal_of_isRegular X hf.2
  have : IsIntegral X := hf.1.source_isIntegral
  have : Module.Finite A ωA := hω.1
  have hdepth := two_le_depth_of_isDualizingRingModule hdim ωA hω
  -- `X` has dimension two
  have hdimX : topologicalKrullDim X = 2 := by
    have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
    rw [IsBirational.topologicalKrullDim_eq_of_isClosedMap hf.1.isBirational f.isClosedMap]
    show topologicalKrullDim (PrimeSpectrum A) = 2
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hdim]
  have hidx : (-(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ)) = -2 := by
    rw [hdimX]
    rfl
  let Y := Over.mk f
  have : IsProper Y.hom := ‹IsProper f›
  have : CompactSpace Y.left := ‹CompactSpace X›
  have : QuasiSeparatedSpace Y.left := ‹QuasiSeparatedSpace X›
  have : IsNormal Y.left := ‹IsNormal X›
  have e' : (homologyFunctor Y.left.Modules (-2)).obj (dualizingComplex Y.hom ωA).obj ≅
      divisorSheaf E :=
    eqToIso (by rw [relativeDualizingModule, hidx]; rfl) ≪≫ e
  obtain ⟨hsub, hiso⟩ :=
    subsingleton_rightDerived_one_and_nonempty_iso Y hdim hf.1 ωA hdepth E hE e'
  have : Subsingleton (structureSheafH1 X) :=
    (rightDerivedOneUnitIso Y).toLinearEquiv.toEquiv.subsingleton_congr.mp hsub
  exact ⟨ModuleCat.isZero_of_subsingleton _, hiso⟩

/-- **`ω_A ≅ A`** in the situation of the first sentence of [Stacks, Tag 0EA2]: a dualizing module
`ω_A` of a two-dimensional Noetherian normal local domain `A` with a resolution `f : X ⟶ Spec(A)`
whose `ω_X` (normalized with respect to `ω_A`, [Stacks, Tag 0B4R]) is `𝒪_X(E)` for a divisor `E`
over the closed point is free of rank one. This is the fact `Rf_*ω_X = ω_A` of the proof of the
tag read through `f_*𝒪_X = A`; it is what the second sentence of the tag builds on. Forming
`ω_X` uses that `f` is proper and `X` quasi-compact and quasi-separated; these are derived from
`IsResolution f` inside the statement (`haveI`), not assumed. -/
theorem nonempty_iso_of_relativeDualizingModule_iso (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsNormalDomain A] (hdim : ringKrullDim A = 2)
    (ωA : ModuleCat.{u} A) (hω : Stacks.Duality.IsDualizingRingModule A ωA)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsResolution f)
    (E : X.IdealSheafData) (hE : ∀ x : X, x ∈ E.support → f x = closedPoint A)
    (e : haveI : IsProper f := hf.1.isProper
      haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
      haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
      Nonempty (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        ((derivedTilde (CommRingCat.of A)).obj ((singleFunctor (ModuleCat.{u} A) (-2)).obj ωA)) ≅
          (Stacks.Divisors.invertibleSheaf' E : X.Modules))) :
    Nonempty (ωA ≅ ModuleCat.of A A) :=
  have : IsProper f := hf.1.isProper
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  (isZero_structureSheafH1_and_nonempty_iso A hdim ωA hω f hf E hE e).2

/-- **[Stacks, Tag 0EA2], first sentence.** Let `A` be a Noetherian normal local domain of
dimension two which is Nagata, has a dualizing module `ω_A`, and has a resolution of
singularities `f : X ⟶ Spec(A)`. Let `ω_X` be as in [Stacks, Tag 0B4R]: the dualizing module of
`X` normalized with respect to `ω_A`, that is `ω_X = H^{-2}(f^×(ω_A[2]))` with `f^×` the twisted
inverse image (`Stacks.Duality.relativeDualizingModule` at `ω_A[2]^~`, whose degree `-dim X` is
`-2`). If `ω_X ≅ 𝒪_X(E)` for an effective Cartier divisor `E ⊆ X` supported on the exceptional
fibre (every point of `E` lies over the closed point), then `A` defines a rational singularity.

Following the source, duality turns the map `𝒪_X ⟶ 𝒪_X(E) = ω_X` into a generator of
`Hom(RΓ(X, 𝒪_X[2]), ω_A[2])` (`hom_derivedSectionsUnitShift_free`); the criterion
`Stacks.PurityRamification.subsingleton_homology_succ_of_forall_eq_smul` (depth of `ω_A`,
[Stacks, Tag 0AXC], torsion of `H¹(X, 𝒪_X)`) gives `H¹(X, 𝒪_X) = 0`, and a resolution with
`H¹(X, 𝒪_X) = 0` makes `A` a rational singularity
(`definesRationalSingularity_of_isResolution_of_isZero_structureSheafH1`). Forming `f^×`, hence
`ω_X`, uses that `f` is proper and `X` quasi-compact and quasi-separated; inside the statement
these are derived from `IsResolution f` (a resolution is proper over the affine scheme
`Spec(A)`) by `haveI`, not assumed. -/
@[stacks 0EA2 "first sentence: if ω_X ≅ O_X(E) for an effective Cartier divisor E supported on \
the exceptional fibre of a resolution, then A defines a rational singularity"]
theorem definesRationalSingularity_of_relativeDualizingModule_iso (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] (hdim : ringKrullDim A = 2)
    (hNagata : IsNagataRing A) (ωA : ModuleCat.{u} A)
    (hω : Stacks.Duality.IsDualizingRingModule A ωA)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsResolution f)
    (E : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor E]
    (hE : ∀ x : X, x ∈ E.support → f x = closedPoint A)
    (e : haveI : IsProper f := hf.1.isProper
      haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
      haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
      Nonempty (relativeDualizingModule f (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
        ((derivedTilde (CommRingCat.of A)).obj ((singleFunctor (ModuleCat.{u} A) (-2)).obj ωA)) ≅
          (Stacks.Divisors.invertibleSheaf' E : X.Modules))) :
    DefinesRationalSingularity A :=
  have : IsProper f := hf.1.isProper
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  definesRationalSingularity_of_isResolution_of_isZero_structureSheafH1 A hNagata hdim f hf
    (isZero_structureSheafH1_and_nonempty_iso A hdim ωA hω f hf E hE e).1

end AlgebraicGeometry.DualizingDivisor
