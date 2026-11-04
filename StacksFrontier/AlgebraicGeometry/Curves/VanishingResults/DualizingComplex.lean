module

public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentCohomology
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.NormalizedAtClosedPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.SerreAffinenessCriterion.ClosedPoints
public import StacksFrontier.RingTheory.Dualizing.DualExtDepthDimension
public import StacksFrontier.RingTheory.LocalCohomology.TopLocalCohomology
public import StacksFrontier.Topology.Sheaves.Modules.SupportCoproduct

/-!
# The dualizing complex of a scheme of dimension at most one over a field

Let `X` be a proper scheme of dimension at most one over a field `k` and let `ω_X^•` be a
dualizing complex on `X` whose stalk at each closed point is normalized. Then `ω_X^•` has
cohomology only in the degrees `-1` and `0`, and at a point of `X` the degree-zero cohomology of
the stalk complex `ω_{X,x}^•` is nonzero exactly when the local ring `𝒪_{X,x}` has dimension zero,
or has dimension one and is not Cohen--Macaulay.

## Main results

* `Dualizing.isZero_homology_of_isNormalizedDualizingComplex_of_ringKrullDim_le_one` — over a
  Noetherian local ring of dimension at most one a normalized dualizing complex has cohomology
  only in degrees `-1` and `0`.
* `Dualizing.nontrivial_homology_zero_iff_depth_eq_zero` — the degree-zero cohomology of a
  normalized dualizing complex is nonzero exactly when the ring has depth zero.
* `Dualizing.nontrivial_homology_zero_iff_of_ringKrullDim_le_one` — the same nonvanishing, read
  through the dimension and the Cohen--Macaulay property.
* `Stacks.Duality.isZero_homology_derivedStalk_of_ne` and
  `Stacks.Duality.isZero_homology_of_ne` — **[Stacks, Tag 0BS2], clause (1)**, on the stalk
  complexes and on the cohomology sheaves.
* `Stacks.Duality.isCoherent_homology_neg_one` — the coherence assertion of **[Stacks, Tag
  0BS2], clause (2)**.
* `Stacks.Duality.nontrivial_homology_zero_derivedStalk_iff` — **[Stacks, Tag 0BS2],
  clause (3)**.

## Implementation notes

The ring-level results read a normalized dualizing complex through the Ext groups out of the ring
placed in degree zero: those compute the cohomology modules of the complex
(`Stacks.LocalCohomology.extSingleRegularLinearEquivHomology`), the degrees in which they can be
nonzero are bounded by the dimension of the support ([Stacks, Tag 0DWZ], part (1)), and the least
one is the depth ([Stacks, Tag 0A7U], part (3)). For the ring itself the support has dimension
`dim(A)`, which turns both facts into statements about `dim(A)`, and Cohen--Macaulayness of a
local ring is the equality of its depth with its dimension.

The hypothesis that the stalk of `ω_X^•` at a closed point is a *normalized* dualizing complex is
[Stacks, Tag 0AWL] —
`Stacks.Duality.isNormalizedDualizingComplex_derivedStalkOfComplex_normalizedDualizingComplex` —
and is carried here. The dimension bound passes from `X` to its local rings by [Stacks, Tag 04MU].

For the cohomology *sheaves* the vanishing is detected at closed points: a cohomology sheaf of a
dualizing complex is coherent, so its support is closed, and a nonempty closed subset of a proper
scheme contains a point closed in `X` ([Stacks, Tag 01XF]). Taking stalks commutes with
cohomology because the stalk functor is exact.

## References

* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
* [Stacks Project, Tag 0AWL](https://stacks.math.columbia.edu/tag/0AWL)
* [Stacks Project, Tag 0DWZ](https://stacks.math.columbia.edu/tag/0DWZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- The `i`-th cohomology of a complex is nontrivial exactly when `Ext^i(A, K)` is. -/
private theorem nontrivial_homology_iff_nontrivial_moduleExtInto {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (i : ℤ) :
    Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) ↔
      Nontrivial (moduleExtInto A K i) :=
  (Equiv.nontrivial_congr
    (Stacks.LocalCohomology.extSingleRegularLinearEquivHomology A K i).toEquiv).symm

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]

/-- Over a Noetherian local ring of Krull dimension at most one, a normalized dualizing complex
has vanishing cohomology outside the degrees `-1` and `0`. -/
theorem isZero_homology_of_isNormalizedDualizingComplex_of_ringKrullDim_le_one
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsNormalizedDualizingComplex.{u, 0} K)
    (hdim : ringKrullDim A ≤ 1) {i : ℤ} (hi : i ≠ -1) (hi0 : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  by_contra hcon
  have hext : Nontrivial (moduleExtInto A K (-(-i))) := by
    rw [neg_neg]
    exact (nontrivial_homology_iff_nontrivial_moduleExtInto K i).mp
      (not_subsingleton_iff_nontrivial.mp hcon)
  obtain ⟨d, hd, hmem⟩ := moduleExtInto_degree_range K hK (-i) hext
  rw [Module.supportDim_self_eq_ringKrullDim] at hd
  have hd1 : d ≤ 1 := by
    rw [hd] at hdim
    exact_mod_cast hdim
  obtain ⟨hlo, hhi⟩ := hmem
  omega

/-- The degree-zero cohomology of a normalized dualizing complex over a Noetherian local ring is
nonzero exactly when the ring has depth zero. -/
theorem nontrivial_homology_zero_iff_depth_eq_zero
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsNormalizedDualizingComplex.{u, 0} K) :
    Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj K) ↔
      Module.depth A (IsLocalRing.maximalIdeal A) A = 0 := by
  obtain ⟨delta, hleast, hdepth⟩ :=
    depth_eq_least_nonzero_negative_ext (M := A) K hK inferInstance
  rw [nontrivial_homology_iff_nontrivial_moduleExtInto, hdepth]
  refine ⟨fun h0 => by simp [Nat.le_zero.mp (hleast.2 h0)], fun h0 => ?_⟩
  obtain rfl : delta = 0 := by exact_mod_cast h0
  exact hleast.1

/-- A Noetherian local ring of Krull dimension at most one has depth zero exactly when its
dimension is zero, or its dimension is one and it is not Cohen--Macaulay. -/
theorem depth_eq_zero_iff_of_ringKrullDim_le_one (hdim : ringKrullDim A ≤ 1) :
    Module.depth A (IsLocalRing.maximalIdeal A) A = 0 ↔
      ringKrullDim A = 0 ∨ ringKrullDim A = 1 ∧ ¬ IsCohenMacaulayLocalRing A := by
  have hI : IsLocalRing.maximalIdeal A • (⊤ : Submodule A A) ≠ ⊤ := by
    rw [smul_eq_mul, Ideal.mul_top]
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
  have hcm : IsCohenMacaulayLocalRing A ↔
      ((Module.depth A (IsLocalRing.maximalIdeal A) A : ℕ∞) : WithBot ℕ∞) = ringKrullDim A :=
    isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay A
  obtain ⟨d, hd⟩ : ∃ d : ℕ, ringKrullDim A = ((d : ℕ∞) : WithBot ℕ∞) := by
    rw [← Module.supportDim_self_eq_ringKrullDim]
    exact exists_supportDim_eq_natCast A A
  have hledep : Module.depth A (IsLocalRing.maximalIdeal A) A ≤ (d : ℕ∞) := by
    have h := Module.depth_le_supportDim A (IsLocalRing.maximalIdeal A) A hI
    rw [Module.supportDim_self_eq_ringKrullDim, hd] at h
    exact_mod_cast h
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Module.depth A (IsLocalRing.maximalIdeal A) A = (n : ℕ∞) :=
    (ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by simp) hledep)).imp fun _ h => h.symm
  have hnd : n ≤ d := by
    rw [hn] at hledep
    exact_mod_cast hledep
  have hd1 : d ≤ 1 := by
    have h : ((d : ℕ∞) : WithBot ℕ∞) ≤ 1 := hd ▸ hdim
    exact_mod_cast h
  rw [hcm, hn, hd]
  interval_cases d <;> interval_cases n <;> simp

end Dualizing

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The Krull dimension of a local ring of a scheme is bounded by the dimension of the scheme. -/
private theorem ringKrullDim_stalk_le_topologicalKrullDim (Y : Scheme.{u}) (y : Y) :
    ringKrullDim (Y.presheaf.stalk y) ≤ topologicalKrullDim Y := by
  rw [topologicalKrullDim_eq_iSup_krullDimOfRing_stalk Y]
  exact le_iSup (fun z : Y => ringKrullDim (Y.presheaf.stalk z)) y

/-- **Stacks Project, Tag 0BS2, clause (1), at a point.** On a proper scheme of dimension at most
one over a field, a dualizing complex whose stalk at `x` is normalized has vanishing cohomology
there outside the degrees `-1` and `0`. -/
theorem isZero_homology_derivedStalk_of_ne (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (ω : DerivedCategory X.Modules) (x : X)
    (hω : letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
      _root_.Dualizing.IsNormalizedDualizingComplex.{u, 0} ((derivedStalkFunctor x).obj ω))
    {i : ℤ} (hi : i ≠ -1) (hi0 : i ≠ 0) :
    letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) i).obj
      ((derivedStalkFunctor x).obj ω)) :=
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  _root_.Dualizing.isZero_homology_of_isNormalizedDualizingComplex_of_ringKrullDim_le_one _ hω
    ((ringKrullDim_stalk_le_topologicalKrullDim X x).trans hdim) hi hi0

/-- **Stacks Project, Tag 0BS2, clause (1).** On a proper scheme of dimension at most one over a
field, a dualizing complex whose stalk at every closed point is normalized has vanishing
cohomology sheaves outside the degrees `-1` and `0`. -/
theorem isZero_homology_of_ne (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (ω : DerivedCategory X.Modules)
    (hω : letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
      IsDualizingComplex ω)
    (hnorm : letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
      ∀ x : X, IsClosed ({x} : Set X) →
        _root_.Dualizing.IsNormalizedDualizingComplex.{u, 0} ((derivedStalkFunctor x).obj ω))
    {i : ℤ} (hi : i ≠ -1) (hi0 : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj ω) := by
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have hcoh : _root_.SheafOfModules.IsCoherent
      ((DerivedCategory.homologyFunctor X.Modules i).obj ω) :=
    isCoherent_homology_of_isDualizingComplex hω i
  refine Stacks.AlgebraicGeometry.DevissageNoetherian.isZero_of_supp_eq_empty _ ?_
  by_contra hne
  obtain ⟨z, hz, hzcl⟩ := Stacks.SerreAffinenessCriterion.exists_isClosed_singleton_mem
    (Stacks.AlgebraicGeometry.DevissageNoetherian.isClosed_supp_of_isCoherent _ hcoh)
    (Set.nonempty_iff_ne_empty.mpr hne)
  have hstalk : IsZero ((Stacks.ModuleSkyscraper.modulesStalkFunctor X z).obj
      ((DerivedCategory.homologyFunctor X.Modules i).obj ω)) :=
    (isZero_homology_derivedStalk_of_ne f hdim ω z (hnorm z hzcl) hi hi0).of_iso
      (((Stacks.ModuleSkyscraper.modulesStalkFunctor X z).mapDerivedCategoryHomologyIso
        i).app ω).symm
  have hmod : IsZero ((AlgebraicGeometry.SheafOfModules.stalkFunctor X.ringCatSheaf z).obj
      ((DerivedCategory.homologyFunctor X.Modules i).obj ω)) := by
    have h := ModuleCat.isZero_iff_subsingleton.mp (hstalk.of_iso
      (restrictScalarsStalkObjIso z ((DerivedCategory.homologyFunctor X.Modules i).obj ω)))
    rw [ModuleCat.isZero_iff_subsingleton]
    exact h
  obtain ⟨a, ha⟩ := hz
  have hsub := AddCommGrpCat.isZero_iff_subsingleton.mp
    ((AlgebraicGeometry.SheafOfModules.isZero_stalkFunctor_obj_iff X.ringCatSheaf z _).mp hmod)
  exact ha (Subsingleton.elim a 0)

/-- **Stacks Project, Tag 0BS2, clause (2), coherence.** The dualizing sheaf
`ω_X = H^{-1}(ω_X^•)` of a dualizing complex on a proper scheme over a field is a coherent
`𝒪_X`-module. -/
theorem isCoherent_homology_neg_one (f : X ⟶ Spec (.of k)) [IsProper f]
    (ω : DerivedCategory X.Modules)
    (hω : letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
      IsDualizingComplex ω) :
    _root_.SheafOfModules.IsCoherent
      ((DerivedCategory.homologyFunctor X.Modules (-1)).obj ω) :=
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  isCoherent_homology_of_isDualizingComplex hω (-1)

/-- **Stacks Project, Tag 0BS2, clause (3).** On a proper scheme of dimension at most one over a
field, the degree-zero cohomology of the stalk at `x` of a dualizing complex normalized there is
nonzero exactly when `𝒪_{X,x}` has dimension zero, or has dimension one and is not
Cohen--Macaulay. -/
theorem nontrivial_homology_zero_derivedStalk_iff (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (ω : DerivedCategory X.Modules) (x : X)
    (hω : letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
      _root_.Dualizing.IsNormalizedDualizingComplex.{u, 0} ((derivedStalkFunctor x).obj ω)) :
    letI : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
    (Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj
        ((derivedStalkFunctor x).obj ω)) ↔
      ringKrullDim (X.presheaf.stalk x) = 0 ∨
        ringKrullDim (X.presheaf.stalk x) = 1 ∧
          ¬ IsCohenMacaulayLocalRing (X.presheaf.stalk x)) :=
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  (_root_.Dualizing.nontrivial_homology_zero_iff_depth_eq_zero _ hω).trans
    (_root_.Dualizing.depth_eq_zero_iff_of_ringKrullDim_le_one
      ((ringKrullDim_stalk_le_topologicalKrullDim X x).trans hdim))

end Stacks.Duality

end
