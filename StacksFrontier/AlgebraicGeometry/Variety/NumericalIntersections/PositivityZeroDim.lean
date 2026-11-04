module

public import StacksFrontier.AlgebraicGeometry.Cohomology.ZeroDimensionalSupport.Vanishing
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersection

/-!
# The intersection number of a zero-dimensional subscheme is positive

This is the base case of the induction proving [Stacks, Tag 0BEV], the positivity of the
intersection number of `d` ample invertible modules against a closed subscheme of dimension `d`.
At `d = 0` there are no modules to intersect with and the intersection number is the Euler
characteristic `χ(Z, 𝒪_Z)` of the structure sheaf (`AlgebraicGeometry.intersectionNumber_zero`),
so the statement is that this Euler characteristic is positive.

The support of the structure sheaf is the whole space, so for a zero-dimensional `Z` the higher
cohomology of `𝒪_Z` vanishes by [Stacks, Tag 0AYT] (3) and the alternating sum collapses to
`dim_k H⁰(Z, 𝒪_Z) = dim_k Γ(Z, 𝒪_Z)`.  That is positive because the global sections of a nonempty
scheme form a nonzero ring, and a zero-dimensional `Z` is nonempty: the empty scheme has Krull
dimension `⊥`.

## Main results

* `AlgebraicGeometry.supp_unit_eq_univ`: the structure sheaf is supported everywhere.
* `AlgebraicGeometry.eulerCharacteristic_unit_pos_of_topologicalKrullDim_le_zero`:
  `0 < χ(Z, 𝒪_Z)` for `Z` nonempty, proper over a field and of dimension at most zero.
* `AlgebraicGeometry.intersectionNumber_pos_of_topologicalKrullDim_eq_zero`: the `d = 0` case
  of [Stacks, Tag 0BEV].

## References

* [Stacks Project, Tag 0BEV](https://stacks.math.columbia.edu/tag/0BEV)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
* [Stacks Project, Tag 0BEP](https://stacks.math.columbia.edu/tag/0BEP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The structure sheaf is supported everywhere.** Its stalk at a point is the local ring
there, which is not the zero ring. -/
public theorem supp_unit_eq_univ (Z : Scheme.{u}) :
    _root_.SheafOfModules.supp (SheafOfModules.unit Z.ringCatSheaf) = Set.univ :=
  Set.eq_univ_of_forall fun x =>
    (_root_.SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).mpr
      (Stacks.Ample.unitStalkEquiv Z x).symm.injective.nontrivial

/-- The support of the structure sheaf has the Krull dimension of the scheme. -/
public theorem topologicalKrullDim_supp_unit (Z : Scheme.{u}) :
    topologicalKrullDim (_root_.SheafOfModules.supp (SheafOfModules.unit Z.ringCatSheaf)) =
      topologicalKrullDim Z := by
  rw [supp_unit_eq_univ]
  exact IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Z).isHomeomorph

/-- **The degree-zero cohomology of the structure sheaf of a nonempty scheme is a nonzero
`k`-vector space.** Degree-zero cohomology is global sections
(`AlgebraicGeometry.cohomologyOverFieldZeroEquivSections`), and the global sections of a nonempty
scheme form a nonzero ring. -/
public theorem finrank_cohomologyOverField_unit_zero_pos (k : Type u) [Field k] {Z : Scheme.{u}}
    (g : Z ⟶ Spec (.of k)) [IsProper g] [Nonempty Z] :
    0 < Module.finrank k (cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) 0) := by
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨Classical.arbitrary Z, trivial⟩⟩
  have : Nontrivial Γ(SheafOfModules.unit Z.ringCatSheaf, ⊤) := Z.component_nontrivial ⊤
  have : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k g
  have : FiniteDimensional k
      (cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) 0) :=
    finiteDimensional_cohomologyOverField_of_isProper k g _ 0
  have : Nontrivial (cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) 0) :=
    (cohomologyOverFieldZeroEquivSections k g (SheafOfModules.unit Z.ringCatSheaf)).nontrivial
  exact Module.finrank_pos

/-- **The Euler characteristic of the structure sheaf of a nonempty zero-dimensional scheme,
proper over a field, is positive.** The higher cohomology vanishes by [Stacks, Tag 0AYT] (3), so
the alternating sum is `dim_k Γ(Z, 𝒪_Z) > 0`. -/
public theorem eulerCharacteristic_unit_pos_of_topologicalKrullDim_le_zero (k : Type u) [Field k]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k)) [IsProper g] [Nonempty Z]
    (hdim : topologicalKrullDim Z ≤ 0)
    (hcoh : _root_.SheafOfModules.IsCoherent (SheafOfModules.unit Z.ringCatSheaf)) :
    0 < @eulerCharacteristic k _ Z g _ (SheafOfModules.unit Z.ringCatSheaf) hcoh := by
  have : (SheafOfModules.unit Z.ringCatSheaf).IsCoherent := hcoh
  have hsupp : topologicalKrullDim
      (_root_.SheafOfModules.supp (SheafOfModules.unit Z.ringCatSheaf)) ≤ 0 :=
    (topologicalKrullDim_supp_unit Z).le.trans hdim
  have hz : ∀ m : ℕ, 1 ≤ m →
      Module.finrank k (cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) m) = 0 :=
    fun m hm =>
      have := ModuleCat.subsingleton_of_isZero
        (isZero_cohomologyOverField_of_topologicalKrullDim_supp_le_zero k g _ hsupp m hm)
      Module.finrank_zero_of_subsingleton
  have hchi : @eulerCharacteristic k _ Z g _ (SheafOfModules.unit Z.ringCatSheaf) hcoh =
      ∑ᶠ m : ℕ, (-1 : ℤ) ^ m *
        (Module.finrank k (cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) m) : ℤ) :=
    rfl
  rw [hchi, finsum_eq_sum_of_support_subset
    (f := fun m : ℕ => (-1 : ℤ) ^ m *
      (Module.finrank k (cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) m) : ℤ))
    (s := Finset.range 1) fun m hm => ?_]
  · rw [Finset.sum_range_one]
    simpa using (by exact_mod_cast finrank_cohomologyOverField_unit_zero_pos k g :
      (0 : ℤ) < (Module.finrank k
        (cohomologyOverField k g (SheafOfModules.unit Z.ringCatSheaf) 0) : ℤ))
  · by_contra hn
    simp only [Finset.coe_range, Set.mem_Iio, not_lt] at hn
    simp [hz m hn] at hm

/-- **The `d = 0` case of [Stacks, Tag 0BEV].** The empty intersection number of a
zero-dimensional closed subscheme `Z ⊂ X` of a scheme proper over a field is positive: it is
`χ(Z, 𝒪_Z)` by `AlgebraicGeometry.intersectionNumber_zero`, and `Z` is nonempty because the empty
scheme has Krull dimension `⊥`. -/
public theorem intersectionNumber_pos_of_topologicalKrullDim_eq_zero (k : Type u) [Field k]
    {X Z : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (i : Z ⟶ X) [IsClosedImmersion i]
    (hdim : topologicalKrullDim Z = ((0 : ℕ) : WithBot ℕ∞)) (L : Fin 0 → X.Modules)
    [∀ j, SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (L j)] :
    0 < intersectionNumber k f i 0 hdim.le L := by
  have : Nonempty Z := by
    by_contra h
    rw [(topologicalKrullDim_eq_bot_iff_isEmpty Z).2 (not_nonempty_iff.mp h)] at hdim
    exact absurd hdim (by simp)
  rw [intersectionNumber_zero]
  exact eulerCharacteristic_unit_pos_of_topologicalKrullDim_le_zero k (i ≫ f)
    (by simp [hdim]) _

end AlgebraicGeometry

end
