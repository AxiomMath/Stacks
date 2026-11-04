module

public import StacksFrontier.Deformation.Examples.Geometric.SchemesUnobstructed
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheafCurve
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReduction
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic

/-!
# The two-chart cover of a curve, and smoothness on an affine chart

Let `X` be a separated scheme of finite type over a field `k` with `dim X ≤ 1`. The proofs of
Stacks 0DZP and 0DZQ start by covering `X` by two affine opens, the second containing a given
finite closed set (the non-smooth points) and every generic point, the first avoiding the set.

## Main results

* `Deformation.Examples.exists_isAffineOpen_subset_le_of_topologicalKrullDim_le_one`: a finite
  subset of `X` lies in an affine open inside any given open containing it.
* `Deformation.Examples.exists_affineOpen_cover_avoiding_of_topologicalKrullDim_le_one'`: the
  two-chart cover.
* `Deformation.Examples.smooth_sectionsAlgebra_of_le_smoothLocus` and
  `Deformation.Examples.isSmoothAt_primeIdealOf`: the affine-local reading of smoothness over
  `k`.

## Implementation notes

`Deformation.Examples.exists_affineOpen_cover_avoiding_of_topologicalKrullDim_le_one` takes the
existence of an ample invertible sheaf (Stacks 09NZ) as a hypothesis; its primed version takes
none. The reduction `X_red` is reduced, Noetherian, separated and of dimension at
most one, so Stacks 09NX gives it an ample invertible sheaf and Properties, Lemma 28.30.5
(Stacks 01ZY) puts any finite set inside an affine open of `X_red`; the corresponding open of `X`
is affine because `X_red → X` restricted to it is a thickening of an affine scheme (Stacks 06AD).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Deformation.Examples

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- A finite subset of a separated scheme of finite type over a field of dimension at most one
lies in an affine open contained in any prescribed open containing it. -/
theorem exists_isAffineOpen_subset_le_of_topologicalKrullDim_le_one [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (hdim : topologicalKrullDim (X : Type u) ≤ 1)
    {E : Set X} (hE : E.Finite) (W : X.Opens) (hEW : E ⊆ W) :
    ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ U ∧ U ≤ W := by
  classical
  have : AlgebraicGeometry.IsNoetherian X :=
    Stacks.HQuasiProjectiveDimensionOne.isNoetherian_of_finiteType_over_field f
  have : X.IsSeparated :=
    Stacks.HQuasiProjectiveDimensionOne.isSeparated_of_isSeparated_over_field f
  -- pass to the reduction
  let ι := X.nilradical.subschemeι
  have hι : Stacks.Thickenings.IsThickening ι :=
    AlgebraicGeometry.FormalSpace.isThickening_nilradical_subschemeι X
  have : IsClosedImmersion ι := hι.1
  have : AlgebraicGeometry.IsReduced X.nilradical.subscheme := isReduced_nilradical_subscheme X
  have : AlgebraicGeometry.IsNoetherian X.nilradical.subscheme :=
    Stacks.HQuasiProjectiveDimensionOne.isNoetherian_of_finiteType_over_field (ι ≫ f)
  have : X.nilradical.subscheme.IsSeparated :=
    Stacks.HQuasiProjectiveDimensionOne.isSeparated_of_isSeparated_over_field (ι ≫ f)
  have hdim' : topologicalKrullDim (X.nilradical.subscheme : Type u) ≤ 1 := by
    rwa [IsHomeomorph.topologicalKrullDim_eq _ hι.isHomeomorph]
  obtain ⟨L, hLinv, hL⟩ :=
    InvertibleSheafGeneral.exists_isAmple_of_isReduced_of_topologicalKrullDim_le_one
      X.nilradical.subscheme hdim'
  have := hLinv
  have hE' : (ι.base ⁻¹' E).Finite := hE.preimage ι.isClosedEmbedding.injective.injOn
  obtain ⟨U', hU', hEU', hU'W⟩ :=
    Stacks.AmpleAffineAvoidance.exists_affineOpen_containing_finite_le_of_ample L hL hE'
      (ι ⁻¹ᵁ W) (Set.preimage_mono hEW)
  have hmem (y) : ι.base y ∈ hι.opensCongr U' ↔ y ∈ U' :=
    SetLike.ext_iff.mp (hι.preimage_opensCongr U') y
  refine ⟨hι.opensCongr U', ?_, ?_, ?_⟩
  · have : IsAffine (ι ⁻¹ᵁ hι.opensCongr U') := by
      rwa [hι.preimage_opensCongr]
    exact Stacks.Thickenings.isAffine_of_isThickening (hι.morphismRestrict (hι.opensCongr U'))
  · intro x hx
    obtain ⟨y, rfl⟩ := hι.2 x
    exact (hmem y).2 (hEU' hx)
  · intro x hx
    obtain ⟨y, rfl⟩ := hι.2 x
    exact hU'W ((hmem y).1 hx)

/-- The two-chart cover of a separated scheme of finite type over a field of dimension at most
one, around a finite closed subset: one chart contains the subset, the other avoids it. -/
theorem exists_affineOpen_cover_avoiding_of_topologicalKrullDim_le_one' [IsSeparated f]
    [LocallyOfFiniteType f] [QuasiCompact f] (hdim : topologicalKrullDim (X : Type u) ≤ 1)
    {E : Set X} (hEfin : E.Finite) (hEclosed : IsClosed E) :
    ∃ U₁ U₂ : X.Opens, IsAffineOpen U₁ ∧ IsAffineOpen U₂ ∧ U₁ ⊔ U₂ = ⊤ ∧
      E ⊆ (U₂ : Set X) ∧ Disjoint E (U₁ : Set X) := by
  classical
  have : AlgebraicGeometry.IsNoetherian X :=
    Stacks.HQuasiProjectiveDimensionOne.isNoetherian_of_finiteType_over_field f
  have hgen : (genericPoints (X : Type u)).Finite :=
    genericPoints.finite TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  obtain ⟨U₂, hU₂, hEU₂, -⟩ :=
    exists_isAffineOpen_subset_le_of_topologicalKrullDim_le_one f hdim (hEfin.union hgen) ⊤
      fun _ _ => trivial
  have hEU₂' : E ⊆ (U₂ : Set X) := fun x hx => hEU₂ (Set.mem_union_left _ hx)
  have hCfin : ((U₂ : Set X)ᶜ).Finite :=
    finite_of_isClosed_disjoint_genericPoints hdim U₂.2.isClosed_compl
      (Set.disjoint_left.mpr fun x hx hgx => hx (hEU₂ (Set.mem_union_right _ hgx)))
  obtain ⟨U₁, hU₁, hCU₁, hU₁E⟩ :=
    exists_isAffineOpen_subset_le_of_topologicalKrullDim_le_one f hdim hCfin
      ⟨Eᶜ, hEclosed.isOpen_compl⟩ fun x hx hxE => hx (hEU₂' hxE)
  refine ⟨U₁, U₂, hU₁, hU₂, le_antisymm le_top fun x _ => ?_, hEU₂',
    Set.disjoint_right.mpr fun x hx => hU₁E hx⟩
  exact or_iff_not_imp_right.2 fun h => hCU₁ h

/-- The point of an affine open corresponding to a prime of its sections. -/
theorem exists_primeIdealOf_eq {U : X.Opens} (hU : IsAffineOpen U) (q : PrimeSpectrum Γ(X, U)) :
    ∃ x : U, hU.primeIdealOf x = q :=
  hU.isoSpec.hom.homeomorph.surjective q

/-- Distinct points of an affine open have distinct primes. -/
theorem primeIdealOf_injective {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Injective hU.primeIdealOf := fun _ _ h =>
  hU.isoSpec.hom.homeomorph.injective h

/-- The sections of a scheme of finite type over `k` on an affine open form a finite type
`k`-algebra. -/
theorem finiteType_sectionsAlgebra [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U) :
    letI := sectionsAlgebra f U
    Algebra.FiniteType k Γ(X, U) := by
  let := sectionsAlgebra f U
  have h1 : (f.appLE ⊤ U (by simp)).hom.FiniteType :=
    f.finiteType_appLE (isAffineOpen_top _) hU (by simp)
  rw [← RingHom.finiteType_algebraMap]
  exact h1.comp (RingHom.FiniteType.of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2)

/-- At a point of the smooth locus inside an affine open, the sections are smooth over `k` at the
corresponding prime. -/
theorem isSmoothAt_primeIdealOf [LocallyOfFinitePresentation f] {U : X.Opens}
    (hU : IsAffineOpen U) (x : U) (hx : (x : X) ∈ f.smoothLocus) :
    letI := sectionsAlgebra f U
    Algebra.IsSmoothAt k (hU.primeIdealOf x).asIdeal := by
  let K : Type u := Γ(Spec (CommRingCat.of k), ⊤)
  let A : Type u := Γ(X, U)
  let : Algebra K A := (f.appLE ⊤ U (by simp)).hom.toAlgebra
  let : Algebra k A := sectionsAlgebra f U
  have : Algebra.IsSmoothAt K (hU.primeIdealOf x).asIdeal :=
    (formallySmooth_stalkMap_iff (f := f) (x := (x : X)) ⊤ (isAffineOpen_top _) U hU
      (by simp) x.2).mp hx
  let : Algebra k K := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.toAlgebra
  have : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FormallySmooth k K := .of_equiv (AlgEquiv.ofBijective (Algebra.ofId k K)
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv))
  exact Algebra.FormallySmooth.comp k K (Localization.AtPrime (hU.primeIdealOf x).asIdeal)

/-- The sections on an affine open contained in the smooth locus form a smooth `k`-algebra. -/
theorem smooth_sectionsAlgebra_of_le_smoothLocus [LocallyOfFinitePresentation f] {U : X.Opens}
    (hU : IsAffineOpen U) (hle : U ≤ f.smoothLocus) :
    letI := sectionsAlgebra f U
    Algebra.Smooth k Γ(X, U) := by
  let := sectionsAlgebra f U
  have : Algebra.FinitePresentation k Γ(X, U) :=
    Algebra.FinitePresentation.of_finiteType.mp (finiteType_sectionsAlgebra f hU)
  refine ⟨?_, this⟩
  rw [← Algebra.smoothLocus_eq_univ_iff]
  refine Set.eq_univ_iff_forall.mpr fun q => ?_
  obtain ⟨x, rfl⟩ := exists_primeIdealOf_eq hU q
  exact isSmoothAt_primeIdealOf f hU x (hle x.2)

end Deformation.Examples
