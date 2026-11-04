module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechVanishingCriteria.OnABasis
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.AbelianCohomologySheafOnSections
public import StacksFrontier.Topology.Sheaves.Cohomology.AbelianFilteredColimits.FromCechVanishing

/-!
# Stacks 01EW for abelian sheaves

`StacksDraft.Ch20.Sec11.Tag01EWCycles` proves Stacks Tag 01EW for an arbitrary abelian category
`𝒜` of coefficients equipped with an exact functor `T` to the abelian sheaves on `X` whose
injective objects have Čech-acyclic underlying sheaves.  This file instantiates that development
at `𝒜 = Sheaf (Opens.grothendieckTopology X) AddCommGrpCat` and `T = 𝟭`, which gives Tag 01EW
for abelian sheaves and so discharges `Stacks.Cohomology.AbelianColimit.CechToCohomologyOnBasis`
— the single remaining mathematical input of abelian Stacks 01FF, and hence of the two
colimit-comparison clauses of Stacks 0A37.

Two things make the instantiation short.  The Čech acyclicity of the injective objects is
`Stacks.Cohomology.AbelianVanishing.isZero_cechComplex_homology_of_injective`, Stacks 09SZ
applied to an injective abelian sheaf, which is already available in this spelling.  And the passage
from the right-derived sections that Tag 01EW concludes about to Mathlib's native `Sheaf.H'` is
`Stacks.Cohomology.AbelianColimit.nonempty_H'functor_iso_rightDerived`.

## Main results

* `cechAcyclicInjectives_id`: abelian sheaves are admissible coefficients for Tag 01EW.
* `isZero_rightDerived_sections_of_cech_isZero_on_basis`: **Stacks 01EW for abelian sheaves**,
  concluded about right-derived sections.
* `cechToCohomologyOnBasis`: the same statement in the `Sheaf.H'` spelling, i.e.
  `Stacks.Cohomology.AbelianColimit.CechToCohomologyOnBasis X`.
* `isZero_H'_succ_colimit_of_injective'` and `isIso_colimit_post_H'functor_of_isCompact'`:
  the two consequences recorded in `StacksDraft.Ch20.Sec16.Tag0A37Colimit2`, now
  unconditional.  The second is **Stacks 01FF for abelian sheaves**, and its index category is
  free in two universes.

## Implementation notes

The spelling is `Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}` with `X : Type u`
carrying a topology rather than `TopCat.Sheaf AddCommGrpCat.{u} X`: the latter is a
semireducible `def` over the former, and the `HasExt` and `HasExactColimitsOfShape` instances
behind `Sheaf.H'` are not found across that crossing.

Tag 01EW is stated for coefficients in `AddCommGrpCat.{max u w}`; here `w = u`, so the generic
development specialises with no universe gymnastics.  The one instance it needs that is not
found by search is `GrothendieckTopology.WEqualsLocallyBijective`, whose Mathlib instance fires
only when the coefficient universe is the universe of the site; it is supplied from
`Stacks.Cohomology.AbelianHigherDirectImage.abelianSheafWEqualsLocallyBijective`.

## References

* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 09SZ](https://stacks.math.columbia.edu/tag/09SZ)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.Basis (OpenCover abPresheaf Hobj)
open Stacks.Cohomology.AbelianColimit (abSections H'functor CechToCohomologyOnBasis
  nonempty_H'functor_iso_rightDerived isIso_colimit_post_H'functor_of_isCompact)

universe u

namespace Stacks.Cohomology.AbelianBasis

variable {X : Type u} [TopologicalSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-! ### Abelian sheaves as coefficients for Stacks 01EW -/

/-- The identity functor on abelian sheaves, read as a functor to the abelian sheaves on `X`:
the coefficient functor of Tag 01EW for abelian coefficients. -/
abbrev toSelf (X : Type u) [TopologicalSpace X] :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  𝟭 _

omit [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] in
/-- **Abelian sheaves are admissible coefficients for Stacks 01EW**: an injective abelian sheaf
has vanishing positive-degree Čech cohomology for every family of open subsets, by Stacks 09SZ
through `Stacks.Cohomology.AbelianVanishing.isZero_cechComplex_homology_of_injective`. -/
theorem cechAcyclicInjectives_id :
    BasisCycles.CechAcyclicInjectives (toSelf X) := by
  intro F hF κ Y q
  refine (BasisCycles.cechSurj_iff_isZero_homology Y (abPresheaf (toSelf X) F) q).2 ?_
  have := hF
  exact AbelianVanishing.isZero_cechComplex_homology_of_injective F Y (q + 1) (Nat.succ_pos q)

/-! ### Stacks 01EW for abelian sheaves -/

/-- **Stacks Tag 01EW for abelian sheaves**, concluded about right-derived sections.  Let `B` be
a basis of open subsets of `X` and let `Cov` be a collection of open covers by members of `B`
whose finite intersections also lie in `B`.  If every open cover of a member of `B` is refined by
a member of `Cov` covering it, and the positive-degree Čech cohomology of the abelian sheaf `F`
vanishes for every cover in `Cov`, then `Hⁿ(V, F)` vanishes over every member `V` of `B` for
`n > 0`.

This is `Stacks.Cohomology.BasisCycles.isZero_Hobj_of_cech_isZero_on_basis` at `T = 𝟭`, with
`cechAcyclicInjectives_id` for its one coefficient-specific input. -/
theorem isZero_rightDerived_sections_of_cech_isZero_on_basis
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (B : Set (Opens X))
    (hB : Opens.IsBasis B) (Cov : Set (OpenCover X))
    (hCovBasis : ∀ W ∈ Cov, W.carrier ∈ B ∧ (∀ i, W.obj i ∈ B) ∧
      ∀ (p : ℕ) (s : Fin (p + 1) → W.ι), (⨅ k, W.obj (s k)) ∈ B)
    (hCovCofinal : ∀ V ∈ B, ∀ W : OpenCover X, W.carrier = V →
      ∃ W' ∈ Cov, W'.carrier = V ∧ W'.Refines W)
    (hCech : ∀ W ∈ Cov, ∀ n : ℕ, 0 < n →
      IsZero (((cechComplexFunctor W.obj).obj F.obj).homology n))
    (V : Opens X) (hV : V ∈ B) (n : ℕ) (hn : 0 < n) :
    IsZero (((abSections V).rightDerived n).obj F) :=
  have : (Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    Stacks.Cohomology.AbelianHigherDirectImage.abelianSheafWEqualsLocallyBijective
  BasisCycles.isZero_Hobj_of_cech_isZero_on_basis (toSelf X) cechAcyclicInjectives_id F B hB
    Cov hCovBasis hCovCofinal hCech V hV n hn

/-- **Stacks Tag 01EW for abelian sheaves, in the `Sheaf.H'` spelling.**  This is
`Stacks.Cohomology.AbelianColimit.CechToCohomologyOnBasis X`: the property of the space that
`StacksDraft.Ch20.Sec16.Tag0A37Colimit2` isolates as the single remaining mathematical input of
abelian Stacks 01FF.  It holds for every space, with no hypotheses beyond the sheafification
instance that the statement itself carries.

The conclusion of `isZero_rightDerived_sections_of_cech_isZero_on_basis` is moved to native
cohomology by `nonempty_H'functor_iso_rightDerived`, the comparison of `Sheaf.H'` with
right-derived sections over `V`. -/
theorem cechToCohomologyOnBasis : CechToCohomologyOnBasis X := by
  intro F B hB Cov hCovBasis hCovCofinal hCech V hV n hn
  exact (isZero_rightDerived_sections_of_cech_isZero_on_basis F B hB Cov hCovBasis hCovCofinal
    hCech V hV n hn).of_iso ((nonempty_H'functor_iso_rightDerived V n).some.app F)

/-! ### The two consequences, now unconditional -/

/-- **The vanishing input of abelian Stacks 01FF, unconditionally.**  Let `X` have a basis of
quasi-compact opens whose binary intersections are quasi-compact, let `U` be a quasi-compact open
and let `E` be a filtered system of *injective* abelian sheaves.  Then `Hⁿ⁺¹(U, colimᵢ Eᵢ) = 0`
for every `n`.

This is `Stacks.Cohomology.AbelianColimit.isZero_H'_succ_colimit_of_injective` with its
hypothesis discharged by `cechToCohomologyOnBasis`. -/
theorem isZero_H'_succ_colimit_of_injective' {I : Type u} [SmallCategory I] [IsFiltered I]
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    (U : Opens X) (hU : IsCompact (U : Set X))
    (E : I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hE : ∀ i, Injective (E.obj i)) (n : ℕ) :
    IsZero (Sheaf.H'.{u, u, u} (colimit E) (n + 1) U) :=
  AbelianColimit.isZero_H'_succ_colimit_of_injective cechToCohomologyOnBasis hBasis hInter U hU
    E hE n

section Index

universe t s

/-- **Stacks 01FF for abelian sheaves, unconditionally.**  Let `X` be a topological space with a
basis of quasi-compact opens whose binary intersections are quasi-compact and let `U` be a
quasi-compact open of `X`.  Then for every filtered system `F` of abelian sheaves and every
degree `q` the canonical map `colimᵢ Hᑫ(U, Fᵢ) ⟶ Hᑫ(U, colimᵢ Fᵢ)` is an isomorphism.

This is `Stacks.Cohomology.AbelianColimit.isIso_colimit_post_H'functor_of_cechToCohomology` with
its hypothesis discharged by `cechToCohomologyOnBasis`; it is the shape the two
colimit-comparison clauses of Stacks 0A37 need on the limit space.

The index category is free in two universes, `Type t` for its objects and `Type s` for its
morphisms, both asked only to be `u`-small; see the implementation notes of
`Stacks.Cohomology.AbelianColimit.isIso_colimit_post_H'functor_of_cechToCohomology` for why
smallness is both necessary and sufficient, and for why the space and the coefficients cannot be
separated from each other. -/
theorem isIso_colimit_post_H'functor_of_isCompact' {I : Type t} [Category.{s} I] [IsFiltered I]
    [UnivLE.{t, u}] [UnivLE.{s, u}]
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    (U : Opens X) (hU : IsCompact (U : Set X))
    (F : I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ) :
    IsIso (colimit.post F (H'functor U q)) :=
  AbelianColimit.isIso_colimit_post_H'functor_of_cechToCohomology cechToCohomologyOnBasis
    hBasis hInter U hU F q

end Index

end Stacks.Cohomology.AbelianBasis

end
