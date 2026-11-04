module

public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.RiemannRoch
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.AutomaticProperties
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletionDiscreteValuation
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.StalkwiseInvertible
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.AffineOfModuleCategory
public import StacksFrontier.RingTheory.Dualizing.GorensteinCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafHom
public import StacksFrontier.AlgebraicGeometry.InvertibleModuleEndomorphismOverField
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexOverFieldClauses
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ClosedImmersionNormalizedStalk
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexModel
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtensionInvertibleGlobal
public import StacksCore.Tactic.StacksAttribute

/-!
# The dualizing sheaf of a Gorenstein proper curve

Let `k` be a field and `X` a proper scheme over `k` of dimension one with `H⁰(X, 𝒪_X) = k`. If `X`
is Gorenstein, the dualizing sheaf `ω_X = H^{-1}(ω_X^•)` of [Stacks, Tag 0BS2] is invertible and
`deg(ω_X) = 2g - 2`, where `g` is the genus.

## Main results

* `AlgebraicGeometry.ringKrullDim_stalk_eq_one_of_isClosed`: on a connected proper scheme of
  dimension one over a field, every closed point has a one-dimensional local ring.
* `AlgebraicGeometry.isInvertible_homology_neg_one_of_isGorenstein`: on a Gorenstein proper scheme
  of dimension at most one over a field whose closed points have one-dimensional local rings,
  `H^{-1}` of a dualizing complex normalized at the closed points is an invertible module;
  `isInvertible_homology_neg_one_of_isGorenstein_of_connectedSpace` is the connected form.
* `AlgebraicGeometry.invertibleCurveDegree_eq_two_mul_genus_sub_two`: an invertible module with
  `h⁰ = g` and `h¹ = 1` has degree `2g - 2`.

## References

* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS6](https://stacks.math.columbia.edu/tag/0BS6)
* [Stacks Project, Tag 0BFQ](https://stacks.math.columbia.edu/tag/0BFQ)
* [Stacks Project, Tag 0C19](https://stacks.math.columbia.edu/tag/0C19)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace Stacks.Duality

open _root_.AlgebraicGeometry

/-- **The derived stalks of `ω_X^•` at the closed points are normalized** ([Stacks, Tag 0FVV]).
Let `X` be proper over a field `k` and `ω_X^• = f^×(𝒪_{Spec k})`. At a closed point `x` the
derived stalk `ω_{X,x}^•`, read at the standard model, is a normalized dualizing complex over
`𝒪_{X,x}`. -/
theorem isNormalizedDualizingComplex_derivedStalk_dualizingComplexOverField {k : Type u}
    [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (x : X)
    (hx : IsClosed ({x} : Set X)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI := HasDerivedCategory.standard X.Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} (X.presheaf.stalk x))
    Dualizing.IsNormalizedDualizingComplex.{u, 0}
      ((derivedStalkFunctor x).obj (dualizingComplexOverField f).obj) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨ω, hω⟩ := isDualizingComplex_dualizingComplexOverField f U hU
  have h0 := ProperOverField.associatedShiftFunction_eq_zero_of_charts
    (ProperOverField.hasCharts f) x hx
  have h1 := associatedShiftFunction_eq_dualizingDimension hU ω hω x hxU
  exact (isNormalizedDualizingComplex_derivedStalkFunctor_iff _ hU ω
    ((isDualizingModelOn_standard_iff _ hU ω).2 hω) x hxU).2 (h1.symm.trans h0)

end Stacks.Duality

attribute [local instance high] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- In a connected Noetherian sober space, a closed point which is the generic point of an
irreducible component is the whole space. -/
theorem eq_univ_of_isClosed_of_mem_genericPoints {Z : Type*} [TopologicalSpace Z]
    [NoetherianSpace Z] [QuasiSober Z] [T0Space Z] [ConnectedSpace Z] {x : Z}
    (hx : IsClosed ({x} : Set Z)) (hg : x ∈ genericPoints Z) : ({x} : Set Z) = Set.univ := by
  have hcomp : ({x} : Set Z) ∈ irreducibleComponents Z := by
    rwa [genericPoints, Set.mem_setOf_eq, hx.closure_eq] at hg
  have hopen : IsOpen ({x} : Set Z) := by
    have heq : ({x} : Set Z)ᶜ = ⋃ C ∈ irreducibleComponents Z \ {({x} : Set Z)}, C := by
      ext y
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_iUnion, Set.mem_diff,
        exists_prop]
      constructor
      · intro hyx
        exact ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y,
          fun h ↦ hyx (show y ∈ ({x} : Set Z) from h ▸ mem_irreducibleComponent)⟩,
          mem_irreducibleComponent⟩
      · rintro ⟨C, ⟨hC, hCx⟩, hyC⟩ rfl
        exact hCx (hcomp.eq_of_subset hC.1 (Set.singleton_subset_iff.mpr hyC)).symm
    rw [← isClosed_compl_iff, heq]
    exact ((NoetherianSpace.finite_irreducibleComponents).subset Set.diff_subset).isClosed_biUnion
      fun C hC => isClosed_of_mem_irreducibleComponents C hC.1
  exact (isClopen_iff.mp ⟨hx, hopen⟩).resolve_left (Set.singleton_nonempty x).ne_empty

/-- **On a connected proper scheme of dimension one over a field, the local ring at every closed
point has dimension one.** -/
theorem ringKrullDim_stalk_eq_one_of_isClosed (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [ConnectedSpace X] (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : IsClosed ({x} : Set X)) : ringKrullDim (X.presheaf.stalk x) = 1 := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := { }
  refine Stacks.CurveProjectiveCompletion.ringKrullDim_stalk_eq_one_of_notMem_genericPoints k f
    hdim.le (U := genericPoints X) le_rfl fun hg => ?_
  have huniv := eq_univ_of_isClosed_of_mem_genericPoints hx hg
  have : Subsingleton X := Set.subsingleton_univ_iff.mp (huniv ▸ Set.subsingleton_singleton)
  have h0 := topologicalKrullDim_zero_of_discreteTopology (X := X)
  rw [hdim] at h0
  exact absurd h0 (by decide)

/-- **On a Gorenstein proper scheme of dimension at most one over a field whose closed points have
one-dimensional local rings, `H^{-1}` of a dualizing complex normalized at the closed points is
invertible.** -/
theorem isInvertible_homology_neg_one_of_isGorenstein (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsGorenstein X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hstalk : ∀ x : X, IsClosed ({x} : Set X) → ringKrullDim (X.presheaf.stalk x) = 1)
    (ω : DerivedCategory X.Modules)
    (hω : letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
      Stacks.Duality.IsDualizingComplex ω)
    (hnorm : letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
      ∀ x : X, IsClosed ({x} : Set X) →
        Dualizing.IsNormalizedDualizingComplex.{u, 0} ((derivedStalkFunctor x).obj ω)) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((DerivedCategory.homologyFunctor X.Modules (-1)).obj ω) := by
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  set M := (DerivedCategory.homologyFunctor X.Modules (-1)).obj ω with hM
  have hcoh : _root_.SheafOfModules.IsCoherent M :=
    Stacks.Duality.isCoherent_homology_neg_one f ω hω
  have hfp : M.IsFinitePresentation := isFinitePresentation_of_isCoherent M
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hlf : SheafOfModules.IsFiniteLocallyFreeOfRank (R := X.ringCatSheaf) M 1 := by
    refine AffineOfModuleCategory.isFiniteLocallyFreeOfRank_of_closedPoint_stalks M hfp 1
      fun x hx => ?_
    have hA : Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x) :=
      IsGorenstein.isGorensteinLocalRing x
    have hinv := (Stacks.Duality.isGorensteinLocalRing_stalk_iff_isInvertible_derivedStalk
      ω hω x).mp hA
    obtain ⟨n, -, ⟨e⟩⟩ := (Dualizing.isInvertible_iff_homology_concentrated_free _).mp hinv
    have hCM : IsCohenMacaulayLocalRing (X.presheaf.stalk x) :=
      Dualizing.IsGorensteinLocalRing.isCohenMacaulayLocalRing _ hA
    have hnt : Nontrivial ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (X.presheaf.stalk x)) n).obj ((derivedStalkFunctor x).obj ω)) :=
      e.toLinearEquiv.toEquiv.nontrivial
    have hn : n = -1 := by
      by_contra hne
      by_cases h0 : n = 0
      · subst h0
        rcases (Stacks.Duality.nontrivial_homology_zero_derivedStalk_iff f hdim ω x
          (hnorm x hx)).mp hnt with h | ⟨-, h⟩
        · rw [hstalk x hx] at h
          exact absurd h (by decide)
        · exact h hCM
      · have hz := Stacks.Duality.isZero_homology_derivedStalk_of_ne f hdim ω x (hnorm x hx)
          hne h0
        exact (not_subsingleton _) (ModuleCat.subsingleton_of_isZero hz)
    subst hn
    let e₂ := ((((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).mapDerivedCategoryHomologyIso
      (-1)).app ω).symm ≪≫ e).toLinearEquiv
    exact ⟨AffineOfModuleCategory.stalkLinearEquivOverRingCatStalk M x
      (e₂.trans (Finsupp.LinearEquiv.finsuppUnique _ _ (ULift.{u} (Fin 1))).symm)⟩
  exact Stacks.ModuleDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one X M hlf

/-- **An invertible module with `h⁰ = g` and `h¹ = 1` has degree `2g - 2`**, on a proper scheme of
dimension at most one over `k` with `H⁰(X, 𝒪_X) = k`. -/
theorem invertibleCurveDegree_eq_two_mul_genus_sub_two (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (h0 : Module.finrank k (cohomologyOverField k f L 0) = genus f)
    (h1 : Module.finrank k (cohomologyOverField k f L 1) = 1) :
    invertibleCurveDegree k f hdim L = 2 * (genus f : ℤ) - 2 := by
  have h := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k f hdim L
  rw [h0, h1] at h
  push_cast at h
  linarith

/-- **On a connected Gorenstein proper scheme of dimension one over a field, `H^{-1}` of a
dualizing complex normalized at the closed points is invertible.** -/
theorem isInvertible_homology_neg_one_of_isGorenstein_of_connectedSpace (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsGorenstein X] [ConnectedSpace X]
    (hdim : topologicalKrullDim X = 1) (ω : DerivedCategory X.Modules)
    (hω : letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
      Stacks.Duality.IsDualizingComplex ω)
    (hnorm : letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
      ∀ x : X, IsClosed ({x} : Set X) →
        Dualizing.IsNormalizedDualizingComplex.{u, 0} ((derivedStalkFunctor x).obj ω)) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      ((DerivedCategory.homologyFunctor X.Modules (-1)).obj ω) :=
  isInvertible_homology_neg_one_of_isGorenstein k f hdim.le
    (fun x hx => ringKrullDim_stalk_eq_one_of_isClosed k f hdim x hx) ω hω hnorm

/-- **`dim_k H¹(X, ω_X) = 1` when `ω_X` is invertible**, on a proper scheme of dimension at most
one over `k` with `H⁰(X, 𝒪_X) = k`. -/
theorem finrank_cohomologyOverField_one_dualizingSheafOverField_of_isInvertible (k : Type u)
    [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim X ≤ 1)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f)] :
    Module.finrank k (cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 1) =
      1 := by
  let := modulesLinearOverField k f
  have := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f
    (Stacks.Duality.dualizingSheafOverField f) 1
  have := finiteDimensional_cohomologyOverField_of_isProper k f
    (Stacks.Duality.dualizingSheafOverField f) 1
  rw [← Subspace.dual_finrank_eq, ← (Stacks.Duality.homDualizingSheafLinearEquiv f hdim
      (Stacks.Duality.dualizingSheafOverField f) (isQuasicoherent_of_isCoherent _)).finrank_eq]
  exact finrank_end_eq_one_of_isInvertible k f _

/-- **`deg(ω_X) = 2g - 2` when `ω_X` is invertible**, on a proper scheme of dimension at most one
over `k` with `H⁰(X, 𝒪_X) = k`. -/
theorem invertibleCurveDegree_dualizingSheafOverField_of_isInvertible (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hdim : topologicalKrullDim X ≤ 1)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f)] :
    invertibleCurveDegree k f hdim (Stacks.Duality.dualizingSheafOverField f) =
      2 * (genus f : ℤ) - 2 :=
  invertibleCurveDegree_eq_two_mul_genus_sub_two k f hdim _
    (Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField f hdim)
    (finrank_cohomologyOverField_one_dualizingSheafOverField_of_isInvertible k f hdim)

/-- **On a Gorenstein proper scheme of dimension at most one over a field whose closed points have
one-dimensional local rings, the dualizing sheaf `ω_X` is invertible.** -/
theorem isInvertible_dualizingSheafOverField (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsGorenstein X]
    (hdim : topologicalKrullDim X ≤ 1)
    (hstalk : ∀ x : X, IsClosed ({x} : Set X) → ringKrullDim (X.presheaf.stalk x) = 1) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact Stacks.UFDExtensionGlobal.isInvertible_of_iso
    (Stacks.Duality.homologyModelIso (Stacks.Duality.dualizingComplexOverField f).obj (-1))
    (isInvertible_homology_neg_one_of_isGorenstein k f hdim hstalk _
      ((Stacks.Duality.isDualizingComplex_standard_iff _).2
        (Stacks.Duality.isDualizingComplex_dualizingComplexOverField f))
      fun x hx =>
        Stacks.Duality.isNormalizedDualizingComplex_derivedStalk_dualizingComplexOverField f x hx)

/-- **On a connected Gorenstein proper scheme of dimension one over a field, the dualizing sheaf
`ω_X` is invertible.** -/
theorem isInvertible_dualizingSheafOverField_of_connectedSpace (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [IsGorenstein X] [ConnectedSpace X]
    (hdim : topologicalKrullDim X = 1) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f) :=
  isInvertible_dualizingSheafOverField k f hdim.le
    fun x hx => ringKrullDim_stalk_eq_one_of_isClosed k f hdim x hx

/-- Let `X` be a proper scheme over a field `k` of dimension one with `H⁰(X, 𝒪_X) = k`. If `X` is
Gorenstein, then `deg(ω_X) = 2g - 2`, where `g` is the genus of `X` and `ω_X` is the dualizing
sheaf of [Stacks, Tag 0BS2]. -/
@[stacks 0C19]
theorem invertibleCurveDegree_dualizingSheafOverField (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    [IsGorenstein X] (hdim : topologicalKrullDim X = 1) :
    letI := connectedSpace_of_isIso_globalSections k f
    letI := isInvertible_dualizingSheafOverField_of_connectedSpace k f hdim
    invertibleCurveDegree k f hdim.le (Stacks.Duality.dualizingSheafOverField f) =
      2 * (genus f : ℤ) - 2 :=
  let := connectedSpace_of_isIso_globalSections k f
  let := isInvertible_dualizingSheafOverField_of_connectedSpace k f hdim
  invertibleCurveDegree_dualizingSheafOverField_of_isInvertible k f hdim.le

end AlgebraicGeometry

end
