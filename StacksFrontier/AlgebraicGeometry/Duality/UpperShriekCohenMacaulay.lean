module

public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinMorphisms.UpperShriekCriterion
public import StacksFrontier.AlgebraicGeometry.Etale.FlatFiniteTypeModules
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekBounded
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativeTorDimension
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.AffineSpaceCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.AffineSpaceCriterionQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayRelativeDimensionOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.QuasiFiniteOverPolynomial
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.CohenMacaulayFibres
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteOverSmooth
import all StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayLocus
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekBoundedCharts

/-!
# `f^!𝒪_Y` for a Cohen–Macaulay morphism

Let `S` be a Noetherian scheme and `f : X ⟶ Y` a Cohen–Macaulay morphism of
`AlgebraicGeometry.FTS S`. Then `f^!𝒪_Y = ω_{X/Y}[d]` for a coherent `𝒪_X`-module `ω_{X/Y}` flat
over `Y`, where `d` is the locally constant relative dimension of `X` over `Y`
([Stacks, Tag 0BV8]).

## Main results

* `Stacks.Duality.exists_isCoherent_isFlatOver_iso_shift_of_charts`: [Stacks, Tag 0BV8] given the
  affine chart description `Stacks.Duality.UpperShriekStructureSheafCharts` of `f^!𝒪_Y`.
* `Stacks.Duality.isCohenMacaulayAt_iff_exists_unique_nonzero_homology_of_charts`:
  [Stacks, Tag 0C0Z] given the same chart description.
* `Stacks.Duality.chart_homology_of_quasiFinite_mvPolynomial`: on an affine chart flat and
  quasi-finite over affine `d`-space, the cohomology sheaves of `f^!𝒪_Y` vanish outside degree
  `-d` and the one in degree `-d` is the associated sheaf of a finite module flat over the base.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Duality

section Charts

/-- The sections over an affine open `U ⊆ f⁻¹(V)` of a module which is on `U` the associated sheaf
of a module `N` flat over `Γ(Y, V)` are flat over `Γ(Y, V)`. -/
theorem flat_sections_of_iso_tilde {X Y : Scheme.{u}} (f : X ⟶ Y) (F : X.Modules)
    {U : X.Opens} (hU : IsAffineOpen U) {V : Y.Opens} (hUV : U ≤ f ⁻¹ᵁ V)
    (N : ModuleCat.{u} Γ(X, U))
    (hN : Module.Flat Γ(Y, V) ((ModuleCat.restrictScalars (f.appLE V U hUV).hom).obj N))
    (e : F.restrict U.ι ≅ (Scheme.Modules.pullback hU.isoSpec.hom).obj (tilde N)) :
    letI : Module Γ(Y, V) Γ(F, U) := Module.compHom Γ(F, U) (f.appLE V U hUV).hom
    Module.Flat Γ(Y, V) Γ(F, U) := by
  let E : ModuleCat.of Γ(X, U) Γ(F, U) ≅ N :=
    (Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.specModuleIsoSections F ⟨U, hU⟩).symm ≪≫
      specModuleIsoOfTildeIso F hU N e
  let : Module Γ(Y, V) Γ(F, U) := Module.compHom Γ(F, U) (f.appLE V U hUV).hom
  exact @Module.Flat.of_linearEquiv Γ(Y, V) _ _ _ _ _ _ _ hN
    ((ModuleCat.restrictScalars (f.appLE V U hUV).hom).mapIso E).toLinearEquiv

/-- A module with zero underlying module has trivial localizations. -/
private theorem not_nontrivial_localizedModule_of_isZero {R : Type*} [CommRing R] (S : Submonoid R)
    {M : ModuleCat R} (h : IsZero M) : ¬ Nontrivial (LocalizedModule S M) := fun hM =>
  have := ModuleCat.isZero_iff_subsingleton.mp h
  not_subsingleton_iff_nontrivial.mpr hM (LocalizedModule.subsingleton_iff.mpr fun m =>
    ⟨1, Submonoid.one_mem _, by rw [Subsingleton.elim m 0, smul_zero]⟩)

variable {S : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] {X Y : AlgebraicGeometry.FTS S}
  {f : X ⟶ Y} {j : AlgebraicGeometry.CompactificationOf (Over.mk f.left)}

/-- A polynomial presentation exists for `Γ(Y, V) → Γ(X, U)` when `f` is of finite type. -/
private theorem nonempty_polynomialPresentation_appLE {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) {V : Y.Opens} (hV : IsAffineOpen V) {U : X.Opens}
    (hU : IsAffineOpen U) (hUV : U ≤ f ⁻¹ᵁ V) :
    Nonempty (Dualizing.PolynomialPresentation (f.appLE V U hUV).hom) :=
  Dualizing.nonempty_polynomialPresentation _ (hf.finiteType_appLE hV hU hUV)

/-- A point `x ∈ W` has an affine neighbourhood `U ⊆ W` inside the preimage of an affine `V`. -/
private theorem exists_affine_chart_le {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (W : X.Opens)
    (hxW : x ∈ W) :
    ∃ (V : Y.Opens) (_ : IsAffineOpen V) (U : X.Opens) (_ : IsAffineOpen U)
      (_ : U ≤ f ⁻¹ᵁ V), x ∈ U ∧ U ≤ W := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f x) (U := ⊤) trivial
  obtain ⟨U, hU, hxU, hUWV⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := W ⊓ f ⁻¹ᵁ V)
    ⟨hxW, hxV⟩
  exact ⟨V, hV, U, hU, fun z hz => (hUWV hz).2, hxU, fun z hz => (hUWV hz).1⟩

/-- A module which is on an affine open `U` the associated sheaf of `N` vanishes on `U` exactly
when `N` is zero. -/
private theorem isZero_restrict_iff_of_iso_tilde {Z : Scheme.{u}} {G : Z.Modules} {U : Z.Opens}
    (hU : IsAffineOpen U) {N : ModuleCat.{u} Γ(Z, U)}
    (e : G.restrict U.ι ≅ (Scheme.Modules.pullback hU.isoSpec.hom).obj (tilde N)) :
    IsZero ((Scheme.Modules.restrictFunctor U.ι).obj G) ↔ IsZero N :=
  ⟨fun h0 => (moduleSpecΓFunctor.map_isZero
    ((Scheme.Modules.restrictFunctor hU.isoSpec.inv).map_isZero h0)).of_iso
      (specModuleIsoOfTildeIso _ hU _ e).symm,
    fun hN => IsZero.of_iso ((Scheme.Modules.pullback hU.isoSpec.hom).map_isZero
      ((tilde.functor Γ(Z, U)).map_isZero hN)) e⟩

/-- **The cohomology of `f^!𝒪_Y` on a chart flat and quasi-finite over affine space.** On affine
opens `U ⊆ f⁻¹(V)` with a flat quasi-finite `Γ(Y, V)[x_1, …, x_d] → Γ(X, U)` over `Γ(Y, V)`, the
cohomology sheaves of `f^!𝒪_Y` are on `U` the associated sheaves of finite `Γ(X, U)`-modules
flat over `Γ(Y, V)`, zero outside degree `-d`. -/
theorem chart_homology_of_quasiFinite_mvPolynomial (hchart : UpperShriekStructureSheafCharts f j)
    {V : Y.left.Opens} (hV : IsAffineOpen V) {U : X.left.Opens} (hU : IsAffineOpen U)
    (hUV : U ≤ f.left ⁻¹ᵁ V) (d : ℕ) (θ : MvPolynomial (Fin d) Γ(Y.left, V) →+* Γ(X.left, U))
    (hθ : θ.comp MvPolynomial.C = (f.left.appLE V U hUV).hom) (hqf : θ.QuasiFinite)
    (hfl : θ.Flat) :
    ∃ N : ℤ → ModuleCat.{u} Γ(X.left, U), (∀ i, Module.Finite Γ(X.left, U) (N i)) ∧
      (∀ i, Module.Flat Γ(Y.left, V)
        ((ModuleCat.restrictScalars (f.left.appLE V U hUV).hom).obj (N i))) ∧
      (∀ i : ℤ, i ≠ -(d : ℤ) → IsZero (N i)) ∧
      (∀ q : PrimeSpectrum Γ(X.left, U), ∃ i : ℤ,
        Nontrivial (LocalizedModule q.asIdeal.primeCompl (N i))) ∧
      ∀ i, Nonempty (((DerivedCategory.homologyFunctor X.left.Modules i).obj
          (relativeDualizingComplexObj f j)).restrict U.ι ≅
        (Scheme.Modules.pullback hU.isoSpec.hom).obj (tilde (N i))) := by
  have : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsNoetherianRing Γ(X.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let p := (nonempty_polynomialPresentation_appLE (locallyOfFiniteType_left f) hV hU hUV).some
  let ω := relativeDualizingComplexObj f j
  let K := p.upperShriekFunctor.{u, 0}.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Y.left, V)) 0).obj
      (ModuleCat.of Γ(Y.left, V) Γ(Y.left, V)))
  obtain ⟨e⟩ := hchart V hV U hU hUV p
  let e' := Stacks.Injectives.mapDerivedCategoryObjIso X.left.Modules
    (Scheme.Modules.restrictFunctor U.ι) ω ≪≫ e
  let eH : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.left.Modules i).obj ω).restrict U.ι ≅
      (Scheme.Modules.pullback hU.isoSpec.hom).obj (tilde
        ((@DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X.left, U)) _ _
          (HasDerivedCategory.standard _) i).obj K)) := fun i =>
    (Scheme.Modules.restrictFunctor U.ι).mapIso
        ((homologyFunctorModelIso X.left.Modules i).app ω) ≪≫
      @homologyRestrictIsoTilde X.left (HasDerivedCategory.standard _) ω U hU K e' i
  have hz := fun i hi =>
    Dualizing.isZero_homology_upperShriekFunctor_unit_of_quasiFinite_mvPolynomial p d θ hθ hqf hfl
      i hi
  refine ⟨fun i => (@DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X.left, U)) _ _
      (HasDerivedCategory.standard _) i).obj K,
    fun i => Dualizing.finite_homology_upperShriekFunctor p i, fun i => ?_, hz, fun q => ?_,
    fun i => ⟨eH i⟩⟩
  · by_cases hi : i = -(d : ℤ)
    · subst hi
      exact Dualizing.flat_homology_upperShriekFunctor_unit_of_quasiFinite_mvPolynomial p d θ hθ
        hqf hfl
    have h0 : Subsingleton ((@DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X.left, U)) _ _
        (HasDerivedCategory.standard _) i).obj K) :=
      ModuleCat.isZero_iff_subsingleton.mp (hz i hi)
    have : Subsingleton ((ModuleCat.restrictScalars (f.left.appLE V U hUV).hom).obj
        ((@DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X.left, U)) _ _
          (HasDerivedCategory.standard _) i).obj K)) := h0
    infer_instance
  · let := (f.left.appLE V U hUV).hom.toAlgebra
    have : Module.Flat Γ(Y.left, V) Γ(X.left, U) := by
      change (f.left.appLE V U hUV).hom.Flat
      rw [← hθ]
      exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.mpr inferInstance) hfl
    exact Dualizing.exists_nontrivial_localizedModule_homology_upperShriekFunctor_unit p q.asIdeal

/-- **Charts of `f^!𝒪_Y` at a Cohen–Macaulay point.** If the flat morphism `f` of
`AlgebraicGeometry.FTS S` is Cohen–Macaulay at `x`, with fibre of dimension `n` at `x`, then
inside any neighbourhood `G` of `x` and over any affine `V ∋ f(x)` there is an affine open
`U ∋ x` on which the cohomology sheaves of `f^!𝒪_Y` are the associated sheaves of finite modules
flat over `Γ(Y, V)`, zero outside degree `-n`. -/
theorem exists_chart_homology_of_isCohenMacaulayAt (hchart : UpperShriekStructureSheafCharts f j)
    [Flat f.left] (x : X.left)
    (hx : f.left.IsCohenMacaulayAt (isLocallyNoetherian_fiber_left f) x) (n : ℕ)
    (hn : topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) = (n : WithBot ℕ∞))
    (G : X.left.Opens) (hxG : x ∈ G) (V : Y.left.Opens) (hV : IsAffineOpen V)
    (hxV : f.left x ∈ V) :
    ∃ (U : X.left.Opens) (hU : IsAffineOpen U) (hUV : U ≤ f.left ⁻¹ᵁ V), x ∈ U ∧ U ≤ G ∧
      ∃ N : ℤ → ModuleCat.{u} Γ(X.left, U), (∀ i, Module.Finite Γ(X.left, U) (N i)) ∧
        (∀ i, Module.Flat Γ(Y.left, V)
          ((ModuleCat.restrictScalars (f.left.appLE V U hUV).hom).obj (N i))) ∧
        (∀ i : ℤ, i ≠ -(n : ℤ) → IsZero (N i)) ∧
        (∀ q : PrimeSpectrum Γ(X.left, U), ∃ i : ℤ,
          Nontrivial (LocalizedModule q.asIdeal.primeCompl (N i))) ∧
        ∀ i, Nonempty (((DerivedCategory.homologyFunctor X.left.Modules i).obj
            (relativeDualizingComplexObj f j)).restrict U.ι ≅
          (Scheme.Modules.pullback hU.isoSpec.hom).obj (tilde (N i))) := by
  have := locallyOfFinitePresentation_left f
  obtain ⟨U, hU, hUV, hxU, hUG, θ, hθ, hqf, hfl⟩ :=
    exists_affine_flat_quasiFinite_mvPolynomial f.left (isLocallyNoetherian_fiber_left f) x hx n
      hn G hxG V hV hxV
  let e := (MvPolynomial.renameEquiv Γ(Y.left, V)
    (Equiv.ulift.{u, 0} (α := Fin n)).symm).toRingEquiv
  have hθ' : (θ.comp e.toRingHom).comp MvPolynomial.C = (f.left.appLE V U hUV).hom := by
    rw [← hθ, RingHom.comp_assoc]
    congr 1
    ext r
    simp [e]
  refine ⟨U, hU, hUV, hxU, hUG, chart_homology_of_quasiFinite_mvPolynomial hchart hV hU hUV n
    (θ.comp e.toRingHom) hθ'
    (hqf.comp (RingHom.QuasiFinite.of_finite (RingHom.Finite.of_surjective _ e.surjective)))
    (RingHom.Flat.comp (RingHom.Flat.of_bijective e.bijective) hfl)⟩

/-- **The cohomology sheaves of `f^!𝒪_Y` are flat over `Y` when `f` is Cohen–Macaulay.** -/
theorem isFlatOver_homology_of_isCohenMacaulay (hchart : UpperShriekStructureSheafCharts f j)
    [Flat f.left] (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f)) (i : ℤ) :
    IsFlatOver f.left.toLRSHom.toShHom
      ((DerivedCategory.homologyFunctor X.left.Modules i).obj
        (relativeDualizingComplexObj f j)) := by
  have := locallyOfFinitePresentation_left f
  let F := (DerivedCategory.homologyFunctor X.left.Modules i).obj (relativeDualizingComplexObj f j)
  have : F.IsQuasicoherent :=
    ((upperShriek f j).obj (DerivedPushforward.derivedStructureSheaf Y.left)).property i
  have key : ∀ (V : Y.left.affineOpens) (z : {z : X.left // f.left z ∈ V.1}),
      ∃ (U : X.left.Opens) (_ : IsAffineOpen U) (hUV : U ≤ f.left ⁻¹ᵁ V.1), z.1 ∈ U ∧
        (let : Module Γ(Y.left, V.1) Γ(F, U) := Module.compHom Γ(F, U) (f.left.appLE V.1 U hUV).hom
        Module.Flat Γ(Y.left, V.1) Γ(F, U)) := by
    intro V z
    obtain ⟨n, hn⟩ := exists_nat_topologicalKrullDimAt_fiber f.left z.1
    obtain ⟨U, hU, hUV, hzU, -, N, -, hNfl, -, -, he⟩ :=
      exists_chart_homology_of_isCohenMacaulayAt hchart z.1 (hCM z.1) n hn ⊤ trivial V.1 V.2 z.2
    exact ⟨U, hU, hUV, hzU, flat_sections_of_iso_tilde f.left F hU hUV (N i) (hNfl i) (he i).some⟩
  choose U hU hUV hzU hflat using key
  have h41 := ((isFlatOver_tfae f.left F).out 1 4).2
  refine h41 ⟨Y.left.affineOpens, fun V => V.1,
    iSup_affineOpens_eq_top Y.left, fun V => V.2, fun V => ⟨_, U V,
      le_antisymm (iSup_le fun z => hUV V z)
        (fun x hx => Opens.mem_iSup.2 ⟨⟨x, hx⟩, hzU V ⟨x, hx⟩⟩), fun z => hU V z,
      fun z => hflat V z⟩⟩

/-- **On the locus of relative dimension `d`, the cohomology sheaves of `f^!𝒪_Y` vanish outside
degree `-d`.** -/
theorem isZero_restrict_homology_relativeDimensionOpen
    (hchart : UpperShriekStructureSheafCharts f j) [Flat f.left]
    [LocallyOfFinitePresentation f.left]
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f))
    (hfib : ∀ y : Y.left, IsCohenMacaulay (f.left.fiber y)) (d : ℕ) (i : ℤ) (hi : i ≠ -(d : ℤ)) :
    IsZero ((Scheme.Modules.restrictFunctor (relativeDimensionOpen f.left hfib d).ι).obj
      ((DerivedCategory.homologyFunctor X.left.Modules i).obj
        (relativeDualizingComplexObj f j))) := by
  refine AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun y => ?_
  let x : X.left := (relativeDimensionOpen f.left hfib d).ι y
  have hn : topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) =
      (d : WithBot ℕ∞) := by
    rw [relativeDimensionFunction_apply f.left hfib x,
      (mem_relativeDimensionOpen f.left hfib d x).1 y.2]
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f.left x) (U := ⊤) trivial
  obtain ⟨U, hU, hUV, hxU, -, N, -, -, hNz, -, he⟩ :=
    exists_chart_homology_of_isCohenMacaulayAt hchart x (hCM x) d hn ⊤ trivial V hV hxV
  have hzU := (isZero_restrict_iff_of_iso_tilde hU (he i).some).2 (hNz i hi)
  exact (Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isZero_stalk_of_isZero_restrict U _ x hxU
    hzU).of_iso
    ((Scheme.Modules.restrictStalkNatIso (relativeDimensionOpen f.left hfib d).ι y).app _)

/-- **On the locus of relative dimension `d`, `f^!𝒪_Y` is its cohomology sheaf in degree `-d`
shifted by `d`.** -/
theorem nonempty_restrict_relativeDualizingComplexObj_iso_shift
    (hchart : UpperShriekStructureSheafCharts f j) [Flat f.left]
    [LocallyOfFinitePresentation f.left]
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f))
    (hfib : ∀ y : Y.left, IsCohenMacaulay (f.left.fiber y)) (d : ℕ) :
    Nonempty ((Scheme.Modules.restrictFunctor (relativeDimensionOpen f.left hfib d).ι
        ).mapDerivedCategory.obj (relativeDualizingComplexObj f j) ≅
      ((DerivedCategory.singleFunctor _ 0).obj
        ((Scheme.Modules.restrictFunctor (relativeDimensionOpen f.left hfib d).ι).obj
          ((DerivedCategory.homologyFunctor X.left.Modules (-(d : ℤ))).obj
            (relativeDualizingComplexObj f j))))⟦(d : ℤ)⟧) := by
  let W := relativeDimensionOpen f.left hfib d
  let R := Scheme.Modules.restrictFunctor W.ι
  let ω := relativeDualizingComplexObj f j
  let E := R.mapDerivedCategory.obj ω
  let eH := fun i : ℤ =>
    (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso R i).app ω
  have hzE : ∀ i : ℤ, i ≠ -(d : ℤ) →
      IsZero ((DerivedCategory.homologyFunctor W.toScheme.Modules i).obj E) := fun i hi =>
    (isZero_restrict_homology_relativeDimensionOpen hchart hCM hfib d i hi).of_iso (eH i)
  let L := E⟦-(d : ℤ)⟧
  have hzL : ∀ i : ℤ, i ≠ 0 →
      IsZero ((DerivedCategory.homologyFunctor W.toScheme.Modules i).obj L) := fun i hi =>
    (hzE (i + -(d : ℤ)) (by omega)).of_iso (Dualizing.homologyShiftObjIso E i (-(d : ℤ)))
  have : L.IsGE 0 := (DerivedCategory.isGE_iff L 0).2 fun i hi => hzL i (by omega)
  have : L.IsLE 0 := (DerivedCategory.isLE_iff L 0).2 fun i hi => hzL i (by omega)
  obtain ⟨M, ⟨eL⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE L 0
  let eM : M ≅ R.obj ((DerivedCategory.homologyFunctor X.left.Modules (-(d : ℤ))).obj ω) :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso W.toScheme.Modules 0).app M).symm ≪≫
      (DerivedCategory.homologyFunctor W.toScheme.Modules 0).mapIso eL.symm ≪≫
      Dualizing.homologyShiftObjIso E 0 (-(d : ℤ)) ≪≫
      eqToIso (congrArg (fun n => (DerivedCategory.homologyFunctor W.toScheme.Modules n).obj E)
        (zero_add _)) ≪≫ eH (-(d : ℤ))
  exact ⟨((shiftFunctorCompIsoId _ (-(d : ℤ)) (d : ℤ) (by omega)).app E).symm ≪≫
    (shiftFunctor _ (d : ℤ)).mapIso (eL ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso eM)⟩

/-- **The sum of the cohomology sheaves of `f^!𝒪_Y` on the locus of relative dimension `d`.** If
the relative dimension is at most `N`, then on that locus the direct sum of the cohomology sheaves
of `f^!𝒪_Y` in degrees `0, -1, …, -N` is the one in degree `-d`. -/
private theorem nonempty_restrict_biproduct_homology_iso
    (hchart : UpperShriekStructureSheafCharts f j) [Flat f.left]
    [LocallyOfFinitePresentation f.left]
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f))
    (hfib : ∀ y : Y.left, IsCohenMacaulay (f.left.fiber y)) (N : ℕ)
    (hN : N ∈ upperBounds (Set.range (relativeDimensionFunction f.left hfib))) (d : ℕ) :
    Nonempty ((Scheme.Modules.restrictFunctor (relativeDimensionOpen f.left hfib d).ι).obj
        (⨁ fun k : Fin (N + 1) => (DerivedCategory.homologyFunctor X.left.Modules
          (-((k : ℕ) : ℤ))).obj (relativeDualizingComplexObj f j)) ≅
      (Scheme.Modules.restrictFunctor (relativeDimensionOpen f.left hfib d).ι).obj
        ((DerivedCategory.homologyFunctor X.left.Modules (-(d : ℤ))).obj
          (relativeDualizingComplexObj f j))) := by
  let G : ℕ → X.left.Modules := fun k =>
    (DerivedCategory.homologyFunctor X.left.Modules (-(k : ℤ))).obj
      (relativeDualizingComplexObj f j)
  let R := Scheme.Modules.restrictFunctor (relativeDimensionOpen f.left hfib d).ι
  by_cases hd : d ≤ N
  · let k₀ : Fin (N + 1) := ⟨d, Nat.lt_succ_of_le hd⟩
    have hz : ∀ k : Fin (N + 1), k ≠ k₀ → IsZero (R.obj (G k)) := fun k hk =>
      isZero_restrict_homology_relativeDimensionOpen hchart hCM hfib d _ (fun he => hk
        (Fin.ext (by simpa [k₀] using he)))
    have : IsIso (biproduct.π (fun k : Fin (N + 1) => R.obj (G k)) k₀) := by
      refine ⟨⟨biproduct.ι (fun k : Fin (N + 1) => R.obj (G k)) k₀,
        biproduct.hom_ext' _ _ fun k => ?_, biproduct.ι_π_self _ _⟩⟩
      by_cases hk : k = k₀
      · subst hk
        simp
      · exact (hz k hk).eq_of_src _ _
    exact ⟨R.mapBiproduct _ ≪≫ asIso (biproduct.π (fun k : Fin (N + 1) => R.obj (G k)) k₀)⟩
  · have hempty : ∀ M : (relativeDimensionOpen f.left hfib d).toScheme.Modules, IsZero M :=
      fun M => AlgebraicGeometry.isZero_of_forall_isZero_stalk M fun y => by
        have hy := (mem_relativeDimensionOpen f.left hfib d _).1 y.2
        exact absurd (hy ▸ hN ⟨_, rfl⟩) hd
    exact ⟨(hempty _).iso (hempty _)⟩

/-- **The cohomology sheaves of `f^!𝒪_Y` are coherent**, given its chart description. -/
private theorem isCoherent_homology_of_charts (hchart : UpperShriekStructureSheafCharts f j)
    [Flat f.left] [LocallyOfFinitePresentation f.left] (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.left.Modules i).obj
      (relativeDualizingComplexObj f j)).IsCoherent :=
  (derivedCategoryBBounded_upperShriek_derivedStructureSheaf_of_charts f j (fun x => by
    obtain ⟨V, hV, U, hU, hUV, hxU, -⟩ := exists_affine_chart_le f.left x ⊤ trivial
    let p := (nonempty_polynomialPresentation_appLE (locallyOfFiniteType_left f) hV hU hUV).some
    exact ⟨U, hU, V, hV, hUV, hxU, p, hchart V hV U hU hUV p⟩)).2 i

/-- **[Stacks, Tag 0BV8], from the chart description of `f^!𝒪_Y`.** For a Cohen–Macaulay
morphism `f` of `AlgebraicGeometry.FTS S` there is a coherent `𝒪_X`-module `ω`, flat over `Y`,
with `f^!𝒪_Y ≅ ω[d]` on the open and closed locus where the relative dimension of `X` over `Y`
is `d`, for every `d`. -/
theorem exists_isCoherent_isFlatOver_iso_shift_of_charts
    (hchart : UpperShriekStructureSheafCharts f j)
    (hCM : f.left.IsCohenMacaulay (isLocallyNoetherian_fiber_left f)) :
    letI h := (isCohenMacaulay_iff_flat_and_fibers f.left (isLocallyNoetherian_fiber_left f)).mp hCM
    letI : Flat f.left := h.1
    letI := locallyOfFinitePresentation_left f
    ∃ ω : X.left.Modules, ω.IsCoherent ∧ IsFlatOver f.left.toLRSHom.toShHom ω ∧
      ∀ d : ℕ, Nonempty ((Scheme.Modules.restrictFunctor (relativeDimensionOpen f.left h.2 d).ι
          ).mapDerivedCategory.obj (relativeDualizingComplexObj f j) ≅
        ((DerivedCategory.singleFunctor _ 0).obj
          ((Scheme.Modules.restrictFunctor (relativeDimensionOpen f.left h.2 d).ι).obj ω))⟦
            (d : ℤ)⟧) := by
  let h := (isCohenMacaulay_iff_flat_and_fibers f.left (isLocallyNoetherian_fiber_left f)).mp hCM
  let : Flat f.left := h.1
  let := locallyOfFinitePresentation_left f
  have hXc : CompactSpace X.left := by
    have : CompactSpace ((Functor.fromPUnit S).obj X.right) :=
      inferInstanceAs (CompactSpace S)
    exact QuasiCompact.compactSpace_of_compactSpace X.hom
  let rd := relativeDimensionFunction f.left h.2
  obtain ⟨N, hN⟩ := rd.range_finite.bddAbove
  let G : ℕ → X.left.Modules := fun k =>
    (DerivedCategory.homologyFunctor X.left.Modules (-(k : ℤ))).obj
      (relativeDualizingComplexObj f j)
  let G' : Fin (N + 1) → X.left.Modules := fun k => G k
  let ω : X.left.Modules := ⨁ G'
  let Ud := fun d : ℕ => relativeDimensionOpen f.left h.2 d
  have hres : ∀ d : ℕ, Nonempty ((Scheme.Modules.restrictFunctor (Ud d).ι).obj ω ≅
      (Scheme.Modules.restrictFunctor (Ud d).ι).obj (G d)) :=
    nonempty_restrict_biproduct_homology_iso hchart hCM h.2 N hN
  refine ⟨ω, ?_, ?_, fun d => ?_⟩
  · have hG : ∀ k : ℕ, (G k).IsCoherent := fun k => isCoherent_homology_of_charts hchart _
    exact AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent
      ((Stacks.SheafOfModules.coherentModules X.left.ringCatSheaf).prop_of_iso
        (Limits.biproduct.isoCoproduct G').symm
        (Stacks.SheafOfModules.isCoherent_sigma _ fun k =>
          AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent (hG k)))
  · intro x
    let d := rd x
    have hx : x ∈ Ud d := (mem_relativeDimensionOpen f.left h.2 d x).2 rfl
    let e : (Scheme.Modules.pullback (Ud d).ι).obj ω ≅
        (Scheme.Modules.pullback (Ud d).ι).obj (G d) :=
      (Scheme.Modules.restrictFunctorIsoPullback (Ud d).ι).symm.app _ ≪≫ (hres d).some ≪≫
        (Scheme.Modules.restrictFunctorIsoPullback (Ud d).ι).app _
    refine (isFlatOverAt_pullback_ι_iff f.left (Ud d) ω ⟨x, hx⟩).1 ?_
    refine (flatOverAt_iff_of_iso ((Ud d).ι ≫ f.left) e ⟨x, hx⟩).2 ?_
    exact (isFlatOverAt_pullback_ι_iff f.left (Ud d) (G d) ⟨x, hx⟩).2
      (isFlatOver_homology_of_isCohenMacaulay hchart hCM _ x)
  · obtain ⟨e⟩ := nonempty_restrict_relativeDualizingComplexObj_iso_shift hchart hCM h.2 d
    exact ⟨e ≪≫ (shiftFunctor _ (d : ℤ)).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso (hres d).some.symm)⟩

/-- **The forward implication of [Stacks, Tag 0C0Z], from the chart description of `f^!𝒪_Y`.**
If the flat morphism `f` of `AlgebraicGeometry.FTS S` is Cohen–Macaulay at `x`, then `f^!𝒪_Y` has
a unique nonzero cohomology sheaf on a neighbourhood of `x`. -/
theorem exists_unique_nonzero_homology_of_isCohenMacaulayAt_of_charts
    (hchart : UpperShriekStructureSheafCharts f j) [Flat f.left] (x : X.left)
    (hx : f.left.IsCohenMacaulayAt (isLocallyNoetherian_fiber_left f) x) :
    ∃ W : X.left.Opens, x ∈ W ∧ ∃ n : ℤ,
      ¬ IsZero ((Scheme.Modules.restrictFunctor W.ι).obj
        ((DerivedCategory.homologyFunctor X.left.Modules n).obj
          (relativeDualizingComplexObj f j))) ∧
      ∀ i : ℤ, i ≠ n → IsZero ((Scheme.Modules.restrictFunctor W.ι).obj
        ((DerivedCategory.homologyFunctor X.left.Modules i).obj
          (relativeDualizingComplexObj f j))) := by
  have := locallyOfFinitePresentation_left f
  obtain ⟨d, hd⟩ := exists_nat_topologicalKrullDimAt_fiber f.left x
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f.left x) (U := ⊤) trivial
  obtain ⟨U, hU, hUV, hxU, -, N, -, -, hNz, hNnt, he⟩ :=
    exists_chart_homology_of_isCohenMacaulayAt hchart x hx d hd ⊤ trivial V hV hxV
  have hz : ∀ i : ℤ, i ≠ -(d : ℤ) → IsZero ((Scheme.Modules.restrictFunctor U.ι).obj
      ((DerivedCategory.homologyFunctor X.left.Modules i).obj (relativeDualizingComplexObj f j))) :=
    fun i hi => (isZero_restrict_iff_of_iso_tilde hU (he i).some).2 (hNz i hi)
  refine ⟨U, hxU, -(d : ℤ), fun h0 => ?_, hz⟩
  obtain ⟨i, hi⟩ := hNnt (hU.primeIdealOf ⟨x, hxU⟩)
  refine not_nontrivial_localizedModule_of_isZero _ ?_ hi
  by_cases hid : i = -(d : ℤ)
  · subst hid
    exact (isZero_restrict_iff_of_iso_tilde hU (he (-(d : ℤ))).some).1 h0
  · exact hNz i hid

/-- **The cohomology sheaves of `f^!𝒪_Y` on an affine chart.** On affine opens `U ⊆ f⁻¹(V)` and
for a polynomial presentation `p` of `Γ(Y, V) → Γ(X, U)`, the restriction to `U` of
`H^i(f^!𝒪_Y)` is the associated sheaf of `H^i(ω^•_{Γ(X, U)/Γ(Y, V)})`. -/
theorem nonempty_restrict_homology_iso_tilde (hchart : UpperShriekStructureSheafCharts f j)
    {V : Y.left.Opens} (hV : IsAffineOpen V) {U : X.left.Opens} (hU : IsAffineOpen U)
    (hUV : U ≤ f.left ⁻¹ᵁ V) (p : Dualizing.PolynomialPresentation (f.left.appLE V U hUV).hom)
    (i : ℤ) :
    Nonempty (((DerivedCategory.homologyFunctor X.left.Modules i).obj
        (relativeDualizingComplexObj f j)).restrict U.ι ≅
      (Scheme.Modules.pullback hU.isoSpec.hom).obj (tilde
        ((@DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X.left, U)) _ _
          (HasDerivedCategory.standard _) i).obj (p.upperShriekFunctor.{u, 0}.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Y.left, V)) 0).obj
              (ModuleCat.of Γ(Y.left, V) Γ(Y.left, V))))))) := by
  let ω := relativeDualizingComplexObj f j
  obtain ⟨e⟩ := hchart V hV U hU hUV p
  let e' := Stacks.Injectives.mapDerivedCategoryObjIso X.left.Modules
    (Scheme.Modules.restrictFunctor U.ι) ω ≪≫ e
  exact ⟨(Scheme.Modules.restrictFunctor U.ι).mapIso
      ((homologyFunctorModelIso X.left.Modules i).app ω) ≪≫
    @homologyRestrictIsoTilde X.left (HasDerivedCategory.standard _) ω U hU _ e' i⟩

/-- A module vanishing on an open `W` vanishes on every open `U ⊆ W`. -/
theorem isZero_restrict_of_le {Z : Scheme.{u}} (G : Z.Modules) {U W : Z.Opens} (hUW : U ≤ W)
    (h : IsZero ((Scheme.Modules.restrictFunctor W.ι).obj G)) :
    IsZero ((Scheme.Modules.restrictFunctor U.ι).obj G) :=
  AlgebraicGeometry.isZero_of_forall_isZero_stalk _ fun y =>
    (Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isZero_stalk_of_isZero_restrict W G _
      (hUW y.2) h).of_iso ((Scheme.Modules.restrictStalkNatIso U.ι y).app _)

/-- **A Cohen–Macaulay point of at least the fibre dimension nearby.** Every neighbourhood `W` of
`x` contains a point `ξ` at which the flat morphism `f` is Cohen–Macaulay and whose fibre
dimension is at least that of `x`. -/
private theorem exists_isCohenMacaulayAt_le_topologicalKrullDimAt [Flat f.left] (x : X.left) (d : ℕ)
    (hd : topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) = (d : WithBot ℕ∞))
    (W : X.left.Opens) (hxW : x ∈ W) :
    ∃ ξ ∈ W, f.left.IsCohenMacaulayAt (isLocallyNoetherian_fiber_left f) ξ ∧ ∃ e : ℕ, d ≤ e ∧
      topologicalKrullDimAt (f.left.fiber (f.left ξ)) (f.left.asFiber ξ) = (e : WithBot ℕ∞) := by
  have := locallyOfFinitePresentation_left f
  obtain ⟨V, hV, U, hU, hUV, hxU, hUW⟩ := exists_affine_chart_le f.left x W hxW
  let : Algebra Γ(Y.left, V) Γ(X.left, U) := (f.left.appLE V U hUV).hom.toAlgebra
  have : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsNoetherianRing Γ(X.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Module.Flat Γ(Y.left, V) Γ(X.left, U) :=
    HasRingHomProperty.appLE @Flat f.left inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV
  have hft : (f.left.appLE V U hUV).hom.FiniteType :=
    (locallyOfFiniteType_left f).finiteType_appLE hV hU hUV
  have : Algebra.FiniteType Γ(Y.left, V) Γ(X.left, U) := hft
  let p : Dualizing.PolynomialPresentation (algebraMap Γ(Y.left, V) Γ(X.left, U)) :=
    (Dualizing.nonempty_polynomialPresentation _ hft).some
  let z := hU.primeIdealOf ⟨x, hxU⟩
  have hdz : Algebra.relativeDimensionAt Γ(Y.left, V) z.asIdeal = (d : WithBot ℕ∞) :=
    (Stacks.Flatness.topologicalKrullDimAt_fiber_eq_relativeDimensionAt f.left ⟨V, hV⟩
      ⟨U, hU⟩ hUV x hxU).symm.trans hd
  obtain ⟨q₀, hq₀p, -, -, hq₀min, hq₀d⟩ :=
    Dualizing.exists_minimal_le_le_relativeDimensionAt z.asIdeal d hdz
  let z₀ : PrimeSpectrum Γ(X.left, U) := ⟨q₀, hq₀p⟩
  let ξ := hU.fromSpec z₀
  have hξU : ξ ∈ U := by
    have : ξ ∈ Set.range hU.fromSpec := ⟨z₀, rfl⟩
    rwa [hU.range_fromSpec] at this
  have hξz₀ : hU.primeIdealOf ⟨ξ, hξU⟩ = z₀ :=
    hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf ⟨ξ, hξU⟩)
  obtain ⟨Q₀, hQ₀p, hQ₀⟩ :=
    Ideal.Fiber.exists_comap_includeRight_eq q₀ (q₀.under Γ(Y.left, V)) rfl
  let : IsNoetherianRing ((q₀.under Γ(Y.left, V)).Fiber Γ(X.left, U)) :=
    Dualizing.isNoetherianRing_baseChange _ p
  let : IsNoetherianRing (Localization.AtPrime Q₀) :=
    IsLocalization.isNoetherianRing Q₀.primeCompl _ inferInstance
  have hCMξ : f.left.IsCohenMacaulayAt (isLocallyNoetherian_fiber_left f) ξ :=
    isCohenMacaulayAt_fromSpec_of_isCohenMacaulayLocalRing f.left _ ⟨V, hV⟩ ⟨U, hU⟩ hUV z₀
      Q₀ hQ₀ (Dualizing.isCohenMacaulayLocalRing_fiber_of_minimal q₀ hq₀min Q₀ hQ₀)
  obtain ⟨e, he⟩ := exists_nat_topologicalKrullDimAt_fiber f.left ξ
  have h1 := Stacks.Flatness.topologicalKrullDimAt_fiber_eq_relativeDimensionAt f.left
    ⟨V, hV⟩ ⟨U, hU⟩ hUV ξ hξU
  rw [he, hξz₀] at h1
  have hde : (d : WithBot ℕ∞) ≤ (e : WithBot ℕ∞) := h1 ▸ hq₀d
  exact ⟨ξ, hUW hξU, hCMξ, e, by exact_mod_cast hde, he⟩

/-- **The single nonzero degree at a Cohen–Macaulay point.** If the cohomology sheaves of
`f^!𝒪_Y` vanish on `W` in all degrees but `n`, and `f` is Cohen–Macaulay at `ξ ∈ W` with fibre
dimension `e`, then `n = -e`. -/
private theorem eq_neg_of_isZero_restrict_homology_of_isCohenMacaulayAt
    (hchart : UpperShriekStructureSheafCharts f j) [Flat f.left] (W : X.left.Opens) (n : ℤ)
    (hz : ∀ i : ℤ, i ≠ n → IsZero ((Scheme.Modules.restrictFunctor W.ι).obj
      ((DerivedCategory.homologyFunctor X.left.Modules i).obj (relativeDualizingComplexObj f j))))
    (ξ : X.left) (hξW : ξ ∈ W)
    (hCMξ : f.left.IsCohenMacaulayAt (isLocallyNoetherian_fiber_left f) ξ) (e : ℕ)
    (he : topologicalKrullDimAt (f.left.fiber (f.left ξ)) (f.left.asFiber ξ) = (e : WithBot ℕ∞)) :
    n = -(e : ℤ) := by
  have := locallyOfFinitePresentation_left f
  obtain ⟨V, hV, hξV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f.left ξ) (U := ⊤) trivial
  obtain ⟨U', hU', -, hξU', -, N', -, -, hN'z, hN'nt, he'⟩ :=
    exists_chart_homology_of_isCohenMacaulayAt hchart ξ hCMξ e he ⊤ trivial V hV hξV
  by_contra hne
  obtain ⟨i, hi⟩ := hN'nt (hU'.primeIdealOf ⟨ξ, hξU'⟩)
  by_cases hie : i = -(e : ℤ)
  · subst hie
    let F := (DerivedCategory.homologyFunctor X.left.Modules (-(e : ℤ))).obj
      (relativeDualizingComplexObj f j)
    have : F.IsQuasicoherent :=
      ((upperShriek f j).obj (DerivedPushforward.derivedStructureSheaf Y.left)).property _
    obtain ⟨eL⟩ := nonempty_localizedModule_linearEquiv_stalk F hU'
      (specModuleIsoOfTildeIso F hU' _ (he' (-(e : ℤ))).some) hξU'
    have hst := Stacks.AlgebraicGeometry.SchemeHigherDirectImage.isZero_stalk_of_isZero_restrict
      W F ξ hξW (hz _ (Ne.symm hne))
    have : Subsingleton (F.presheaf.stalk ξ) :=
      (AddCommGrpCat.isZero_iff_subsingleton).mp hst
    exact not_subsingleton_iff_nontrivial.mpr hi eL.toEquiv.subsingleton
  · exact not_nontrivial_localizedModule_of_isZero _ (hN'z i hie) hi

/-- **Cohen–Macaulayness from the cohomology sheaves of `f^!𝒪_Y`, given the degree bound.** If the
cohomology sheaves of `f^!𝒪_Y` vanish on a neighbourhood `W` of `x` in all degrees but
`n ≤ -dim_x(X_y)`, then `f` is Cohen–Macaulay at `x`. -/
private theorem isCohenMacaulayAt_of_isZero_restrict_homology_of_le
    (hchart : UpperShriekStructureSheafCharts f j) [Flat f.left] (x : X.left) (W : X.left.Opens)
    (hxW : x ∈ W) (n : ℤ)
    (hz : ∀ i : ℤ, i ≠ n → IsZero ((Scheme.Modules.restrictFunctor W.ι).obj
      ((DerivedCategory.homologyFunctor X.left.Modules i).obj (relativeDualizingComplexObj f j))))
    (d : ℕ)
    (hd : topologicalKrullDimAt (f.left.fiber (f.left x)) (f.left.asFiber x) = (d : WithBot ℕ∞))
    (hnd : n ≤ -(d : ℤ)) :
    f.left.IsCohenMacaulayAt (isLocallyNoetherian_fiber_left f) x := by
  have := locallyOfFinitePresentation_left f
  obtain ⟨V, hV, U, hU, hUV, hxU, hUW⟩ := exists_affine_chart_le f.left x W hxW
  let : Algebra Γ(Y.left, V) Γ(X.left, U) := (f.left.appLE V U hUV).hom.toAlgebra
  have : IsNoetherianRing Γ(Y.left, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : IsNoetherianRing Γ(X.left, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Module.Flat Γ(Y.left, V) Γ(X.left, U) :=
    HasRingHomProperty.appLE @Flat f.left inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV
  have hft : (f.left.appLE V U hUV).hom.FiniteType :=
    (locallyOfFiniteType_left f).finiteType_appLE hV hU hUV
  have : Algebra.FiniteType Γ(Y.left, V) Γ(X.left, U) := hft
  let p : Dualizing.PolynomialPresentation (algebraMap Γ(Y.left, V) Γ(X.left, U)) :=
    (Dualizing.nonempty_polynomialPresentation _ hft).some
  let K := p.upperShriekFunctor.{u, 0}.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(Y.left, V)) 0).obj
      (ModuleCat.of Γ(Y.left, V) Γ(Y.left, V)))
  have hzK : ∀ i : ℤ, i ≠ n → IsZero ((@DerivedCategory.homologyFunctor
      (ModuleCat.{u} Γ(X.left, U)) _ _ (HasDerivedCategory.standard _) i).obj K) := by
    intro i hi
    have h0 := isZero_restrict_of_le _ hUW (hz i hi)
    exact (isZero_restrict_iff_of_iso_tilde hU
      (nonempty_restrict_homology_iso_tilde hchart hV hU hUV p i).some).1 h0
  let z := hU.primeIdealOf ⟨x, hxU⟩
  have hdz : Algebra.relativeDimensionAt Γ(Y.left, V) z.asIdeal = (d : WithBot ℕ∞) :=
    (Stacks.Flatness.topologicalKrullDimAt_fiber_eq_relativeDimensionAt f.left ⟨V, hV⟩
      ⟨U, hU⟩ hUV x hxU).symm.trans hd
  obtain ⟨Q, hQp, hQ⟩ :=
    Ideal.Fiber.exists_comap_includeRight_eq z.asIdeal (z.asIdeal.under Γ(Y.left, V)) rfl
  let : IsNoetherianRing ((z.asIdeal.under Γ(Y.left, V)).Fiber Γ(X.left, U)) :=
    Dualizing.isNoetherianRing_baseChange _ p
  let : IsNoetherianRing (Localization.AtPrime Q) :=
    IsLocalization.isNoetherianRing Q.primeCompl _ inferInstance
  have hCMQ := Dualizing.isCohenMacaulayLocalRing_fiber_of_isZero_homology_gt p n
    (fun i hi => hzK i (ne_of_gt hi)) z.asIdeal Q hQ d hdz hnd
  have h := isCohenMacaulayAt_fromSpec_of_isCohenMacaulayLocalRing f.left
    (isLocallyNoetherian_fiber_left f) ⟨V, hV⟩ ⟨U, hU⟩ hUV z Q hQ hCMQ
  rwa [hU.fromSpec_primeIdealOf] at h

/-- **The converse of [Stacks, Tag 0C0Z], from the chart description of `f^!𝒪_Y`.** If the flat
morphism `f` of `AlgebraicGeometry.FTS S` has `f^!𝒪_Y` with cohomology sheaves vanishing on a
neighbourhood `W` of `x` in all degrees but one, then `f` is Cohen–Macaulay at `x`. -/
theorem isCohenMacaulayAt_of_isZero_restrict_homology_of_charts
    (hchart : UpperShriekStructureSheafCharts f j) [Flat f.left] (x : X.left) (W : X.left.Opens)
    (hxW : x ∈ W) (n : ℤ)
    (hz : ∀ i : ℤ, i ≠ n → IsZero ((Scheme.Modules.restrictFunctor W.ι).obj
      ((DerivedCategory.homologyFunctor X.left.Modules i).obj (relativeDualizingComplexObj f j)))) :
    f.left.IsCohenMacaulayAt (isLocallyNoetherian_fiber_left f) x := by
  have := locallyOfFinitePresentation_left f
  obtain ⟨d, hd⟩ := exists_nat_topologicalKrullDimAt_fiber f.left x
  obtain ⟨ξ, hξW, hCMξ, e, hde, he⟩ :=
    exists_isCohenMacaulayAt_le_topologicalKrullDimAt x d hd W hxW
  have hne :=
    eq_neg_of_isZero_restrict_homology_of_isCohenMacaulayAt hchart W n hz ξ hξW hCMξ e he
  exact isCohenMacaulayAt_of_isZero_restrict_homology_of_le hchart x W hxW n hz d hd (by omega)

/-- **[Stacks, Tag 0C0Z], from the chart description of `f^!𝒪_Y`.** For a flat morphism `f` of
`AlgebraicGeometry.FTS S` and `x ∈ X`, `f` is Cohen–Macaulay at `x` exactly when `f^!𝒪_Y` has a
unique nonzero cohomology sheaf on some neighbourhood of `x`. -/
theorem isCohenMacaulayAt_iff_exists_unique_nonzero_homology_of_charts
    (hchart : UpperShriekStructureSheafCharts f j) [Flat f.left] (x : X.left) :
    f.left.IsCohenMacaulayAt (isLocallyNoetherian_fiber_left f) x ↔
      ∃ W : X.left.Opens, x ∈ W ∧ ∃ n : ℤ,
        ¬ IsZero ((Scheme.Modules.restrictFunctor W.ι).obj
          ((DerivedCategory.homologyFunctor X.left.Modules n).obj
            (relativeDualizingComplexObj f j))) ∧
        ∀ i : ℤ, i ≠ n → IsZero ((Scheme.Modules.restrictFunctor W.ι).obj
          ((DerivedCategory.homologyFunctor X.left.Modules i).obj
            (relativeDualizingComplexObj f j))) :=
  ⟨exists_unique_nonzero_homology_of_isCohenMacaulayAt_of_charts hchart x,
    fun ⟨W, hxW, n, _, hz⟩ =>
      isCohenMacaulayAt_of_isZero_restrict_homology_of_charts hchart x W hxW n hz⟩

end Charts

end Stacks.Duality
