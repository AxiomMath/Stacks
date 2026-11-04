module

public import StacksFrontier.AlgebraicGeometry.AffineVanishingBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Cohomology.QuasicoherentAmplitude
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.GlobalSections
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The sharp cohomological amplitude of derived global sections on a curve

Let `f : X ⟶ Spec k` be a proper morphism to the spectrum of a field with `X` of topological
Krull dimension at most one — the hypotheses of Situation [Stacks, Tag 0B5D]. Then derived global
sections

  `RΓ(X, -) : D(𝒪_X) ⥤ D(k)`

raises an upper cohomological bound by **at most one** on the objects with quasi-coherent
cohomology: if `K` lies in `D^{≤a}` then `RΓ(X, K)` lies in `D^{≤a+1}`.

## Main results

The elided prefix is `AlgebraicGeometry`.

* `isLE_derivedGlobalSectionsOver_obj_of_isZero_hgroup`: if the cohomology of every
  quasi-coherent module vanishes from degree `N` on, then `RΓ(X, -)` carries `D^{≤b}` with
  quasi-coherent cohomology into `D^{≤b+N-1}`.
* `isLE_derivedGlobalSectionsOver_obj_of_topologicalKrullDim_le`: the sharp bound on a proper `X`
  of dimension at most `d`, `D^{≤a} ↦ D^{≤a+d}`.
* `isZero_derivedCohomology_of_isLE_of_topologicalKrullDim_le`: `H^j(X, K) = 0` for `K` in
  `D^{≤a}` with quasi-coherent cohomology and `j > a + d`.
* `isLE_derivedGlobalSectionsOver_obj_of_topologicalKrullDim_le_one` and
  `isZero_derivedCohomology_of_isLE_of_topologicalKrullDim_le_one`: the two statements at
  `d = 1`, the dimension of Situation [Stacks, Tag 0B5D].

## Implementation notes

No model of the derived category is pinned: `DerivedCategory X.Modules` resolves to
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` and `DerivedCategory (ModuleCat.{u} A)` to
`ModuleCat.hasDerivedCategory`. A statement proved at `CategoryTheory.HasDerivedCategory.standard`
would say nothing about these.

## References

* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 0B5D](https://stacks.math.columbia.edu/tag/0B5D)
* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}}

/-! ### Matching the two sections functors -/

/-- If the cohomology group `Hⁿ(X, M)` vanishes, then so does the `n`th right derived functor
of `A`-linear global sections at `M`. -/
theorem isZero_rightDerived_globalSectionsOver_obj_of_isZero_hgroup (f : X ⟶ Spec (.of A))
    (M : X.Modules) (n : ℕ) (h : IsZero (Hgroup X.ringCatSheaf (⊤ : X.Opens) n M)) :
    IsZero (((globalSectionsOver f).rightDerived n).obj M) := by
  obtain ⟨e⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (globalSectionsOver f) (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) n M
  have h' : IsZero (((globalSectionsOver f ⋙
      forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).rightDerived n).obj M) := h
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (AddCommGrpCat.subsingleton_of_isZero
      (show IsZero (((globalSectionsOver f).rightDerived n ⋙
        forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj M) from h'.of_iso e))

/-! ### An upper bound for derived global sections -/

/-- **An upper bound on `RΓ(X, -)` from a vanishing degree for cohomology.** If `Hᵖ(X, ℱ) = 0`
for every quasi-coherent `𝒪_X`-module `ℱ` and every `p ≥ N`, then `A`-linear derived global
sections carries an object of `D(𝒪_X)` with quasi-coherent cohomology lying in degrees `≤ b` into
degrees `≤ b + N - 1`. -/
theorem isLE_derivedGlobalSectionsOver_obj_of_isZero_hgroup (f : X ⟶ Spec (.of A)) (N : ℕ)
    (hN : ∀ M : X.Modules, M.IsQuasicoherent → ∀ p : ℕ, N ≤ p →
      IsZero (Hgroup X.ringCatSheaf (⊤ : X.Opens) p M))
    (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (b : ℤ) (hE : E.IsLE b) :
    ((derivedGlobalSectionsOver f).obj E).IsLE (b + (N : ℤ) - 1) := by
  refine Stacks.QuasicoherentAmplitude.isLE_obj_of_isZero X (globalSectionsOver f)
    (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f) N ?_ E hcoh b hE
  intro M hM p hp
  obtain ⟨q, hq⟩ : ∃ q : ℕ, p = (q : ℤ) :=
    ⟨p.toNat, (Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg N) hp)).symm⟩
  exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff (globalSectionsOver f) hq M).2
    (isZero_rightDerived_globalSectionsOver_obj_of_isZero_hgroup f M q
      (hN M hM q (by lia)))

/-! ### The sharp bound in dimension at most `d` -/

/-- **Derived global sections of a proper scheme of dimension at most `d` over a field raise the
cohomological amplitude by at most `d`.** For `f : X ⟶ Spec k` proper with `X` of topological
Krull dimension at most `d` and `K` an object of `D(𝒪_X)` with quasi-coherent cohomology lying in
degrees `≤ a`, the complex `RΓ(X, K)` lies in degrees `≤ a + d`. -/
theorem isLE_derivedGlobalSectionsOver_obj_of_topologicalKrullDim_le (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] {d : ℕ}
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (a : ℤ) (hE : E.IsLE a) :
    ((derivedGlobalSectionsOver f).obj E).IsLE (a + (d : ℤ)) := by
  have hvan : ∀ M : X.Modules, M.IsQuasicoherent → ∀ p : ℕ, d + 1 ≤ p →
      IsZero (Hgroup X.ringCatSheaf (⊤ : X.Opens) p M) := fun M _ p hp =>
    (isZero_cohomologyOverField_iff_isZero_hgroup k f M p).mp
      (isZero_cohomologyOverField_of_topologicalKrullDim_le k f M (d := d) hdim (by lia))
  have h := isLE_derivedGlobalSectionsOver_obj_of_isZero_hgroup f (d + 1) hvan E hcoh a hE
  exact DerivedCategory.TStructure.t.isLE_of_le _ (a + ((d + 1 : ℕ) : ℤ) - 1) (a + (d : ℤ))
    (by push_cast; lia)

/-- **The cohomology of `RΓ(X, K)` vanishes more than `d` degrees above an upper bound for `K`**,
on a proper `X` of dimension at most `d` over a field: for `K` with quasi-coherent cohomology in
degrees `≤ a`, `H^j(X, K) = 0` for `j > a + d`. -/
theorem isZero_derivedCohomology_of_isLE_of_topologicalKrullDim_le (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] {d : ℕ}
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (a : ℤ) (hE : E.IsLE a) (j : ℤ) (hj : a + (d : ℤ) < j) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) j).obj
      ((derivedGlobalSectionsOver f).obj E)) :=
  have := isLE_derivedGlobalSectionsOver_obj_of_topologicalKrullDim_le k f hdim E hcoh a hE
  DerivedCategory.isZero_of_isLE _ (a + (d : ℤ)) j hj

/-! ### The sharp bound in dimension at most one -/

/-- **Derived global sections of a proper scheme of dimension at most one over a field raise the
cohomological amplitude by at most one.** For `f : X ⟶ Spec k` proper with `X` of topological
Krull dimension at most one and `K` an object of `D(𝒪_X)` with quasi-coherent cohomology lying in
degrees `≤ a`, the complex `RΓ(X, K)` lies in degrees `≤ a + 1`.

This is `AlgebraicGeometry.isLE_derivedGlobalSectionsOver_obj_of_topologicalKrullDim_le` at
`d = 1`. -/
theorem isLE_derivedGlobalSectionsOver_obj_of_topologicalKrullDim_le_one (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (a : ℤ) (hE : E.IsLE a) :
    ((derivedGlobalSectionsOver f).obj E).IsLE (a + 1) :=
  have h := isLE_derivedGlobalSectionsOver_obj_of_topologicalKrullDim_le k f (d := 1)
    (by exact_mod_cast hdim) E hcoh a hE
  DerivedCategory.TStructure.t.isLE_of_le _ (a + ((1 : ℕ) : ℤ)) (a + 1) (by push_cast; lia)

/-- **The cohomology of `RΓ(X, K)` vanishes more than one degree above an upper bound for `K`**,
on a proper `X` of dimension at most one over a field: for `K` with quasi-coherent cohomology in
degrees `≤ a`, `H^j(X, K) = 0` for `j > a + 1`. -/
theorem isZero_derivedCohomology_of_isLE_of_topologicalKrullDim_le_one (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ (1 : WithBot ℕ∞))
    (E : DerivedCategory X.Modules)
    (hcoh : ∀ j : ℤ, ((DerivedCategory.homologyFunctor X.Modules j).obj E).IsQuasicoherent)
    (a : ℤ) (hE : E.IsLE a) (j : ℤ) (hj : a + 1 < j) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) j).obj
      ((derivedGlobalSectionsOver f).obj E)) :=
  have := isLE_derivedGlobalSectionsOver_obj_of_topologicalKrullDim_le_one k f hdim E hcoh a hE
  DerivedCategory.isZero_of_isLE _ (a + 1) j hj

end AlgebraicGeometry

end
