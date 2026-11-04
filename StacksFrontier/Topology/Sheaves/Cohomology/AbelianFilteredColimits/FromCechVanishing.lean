module

public import StacksFrontier.Topology.Sheaves.Cohomology.AbelianFilteredColimits.NativeCohomologyAndColimits
public import StacksFrontier.Topology.Sheaves.Cohomology.AbelianFilteredColimits.CechAcyclicityOfInjectives

/-!
# Stacks 01EW for abelian sheaves is the only remaining input of abelian Stacks 01FF

`StacksDraft.Ch20.Sec16.Tag0A37Colimits` proves Stacks 01FF for abelian sheaves —
`isIso_colimit_post_H'functor_of_isCompact` — modulo a single hypothesis `hvan`, the vanishing
of `Hⁿ⁺¹(U, colimᵢ Eᵢ)` for a filtered system `E` of injective abelian sheaves.
`StacksDraft.Ch20.Sec16.Tag0A37Vanishing` proves the Čech half of that vanishing for abelian
sheaves.  What stands between the two is the *engine* of Stacks 01EW: the passage from Čech
vanishing on a cofinal collection of covers to the vanishing of sheaf cohomology.  That engine
is available only in the sheaves-of-modules spelling
(`Stacks.Cohomology.BasisCycles.isZero_hgroup_of_cech_isZero_on_basis`).

This file records that engine as an explicit property of the space, `CechToCohomologyOnBasis`,
and discharges everything else: granted it, the vanishing input and hence abelian Stacks 01FF
follow.  So the abelian 01EW engine is the single remaining mathematical input, as a checked
implication.

## Main definitions

* `CechToCohomologyOnBasis X` is Stacks 01EW for abelian sheaves on `X`, stated exactly as the
  module-spelling tag states it, with `SheafOfModules R` replaced by
  `Sheaf (Opens.grothendieckTopology X) AddCommGrpCat` and `Hgroup R` by `Sheaf.H'`.

## Main results

* `isZero_H'_succ_colimit_of_injective`: granted `CechToCohomologyOnBasis`, the vanishing
  hypothesis `hvan` of `isIso_colimit_post_H'functor_of_isCompact` holds on every quasi-compact
  open of a space with a basis of quasi-compact opens closed under binary intersection.
* `isIso_colimit_post_H'functor_of_cechToCohomology`: granted `CechToCohomologyOnBasis`,
  **Stacks 01FF for abelian sheaves, unconditionally** — cohomology over a quasi-compact open
  commutes with filtered colimits of abelian sheaves.  Its index category is free in two
  universes, subject only to `u`-smallness; see its implementation notes.

## Implementation notes

The spelling is `Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}` with `X : Type u`
carrying a topology, not `TopCat.Sheaf AddCommGrpCat.{u} X`: the latter is a semireducible `def`
over the former, and the `HasExt` and `HasExactColimitsOfShape` instances that `Sheaf.H'` and the
δ-functor induction need are not found across that crossing.  This is the spelling of both files
this one combines.

`CechToCohomologyOnBasis` keeps the basis hypothesis `Opens.IsBasis B` that the module-spelling
tag carries, even though the docstring of that tag records that its proof never uses it — the
cofinality hypothesis already supplies every cover the proof needs.  Keeping it costs the
consumer nothing here, because the only basis used is the quasi-compact opens and
`Stacks.Cohomology.Vanishing.isBasis_compactOpens` supplies the hypothesis; and it means an
eventual abelian 01EW can be stated as the tag states it.

The Čech hypothesis is discharged at `p = m + 1` rather than at a general positive `p`, because
`isZero_cechComplex_homology_colimit_of_injective` is stated in the successor form.

## References

* [Stacks Project, Tag 01EW](https://stacks.math.columbia.edu/tag/01EW)
* [Stacks Project, Tag 01FF](https://stacks.math.columbia.edu/tag/01FF)
* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.Basis (OpenCover compactOpens)
open Stacks.Cohomology.Vanishing (compactCovers isBasis_compactOpens
  compactCovers_mem_compactOpens exists_compactCover_refines)

universe u

namespace Stacks.Cohomology.AbelianColimit

variable {X : Type u} [TopologicalSpace X]
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-! ### Stacks 01EW for abelian sheaves, as a property of the space -/

/-- **Stacks 01EW for abelian sheaves**, as a property of the space `X`.  Let `B` be a basis of
open subsets of `X` and let `Cov` be a collection of open covers by members of `B` whose finite
intersections also lie in `B`.  If every open cover of a member of `B` is refined by a member of
`Cov` covering it, and the positive-degree Čech cohomology of `F` vanishes for every cover in
`Cov`, then the higher cohomology `Sheaf.H' F n V` vanishes over every member `V` of `B`.

This is the statement of `Stacks.Cohomology.BasisCycles.isZero_hgroup_of_cech_isZero_on_basis`
with `SheafOfModules R` replaced by abelian sheaves on the site of opens and `Hgroup R` by
Mathlib's native `Sheaf.H'`.  It is the single remaining mathematical input of abelian
Stacks 01FF, and hence of the two colimit-comparison clauses of Stacks 0A37. -/
def CechToCohomologyOnBasis (X : Type u) [TopologicalSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}] : Prop :=
  ∀ (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (B : Set (Opens X)),
    Opens.IsBasis B → ∀ Cov : Set (OpenCover X),
    (∀ W ∈ Cov, W.carrier ∈ B ∧ (∀ i, W.obj i ∈ B) ∧
      ∀ (p : ℕ) (s : Fin (p + 1) → W.ι), (⨅ k, W.obj (s k)) ∈ B) →
    (∀ V ∈ B, ∀ W : OpenCover X, W.carrier = V →
      ∃ W' ∈ Cov, W'.carrier = V ∧ W'.Refines W) →
    (∀ W ∈ Cov, ∀ n : ℕ, 0 < n →
      IsZero (((cechComplexFunctor W.obj).obj F.obj).homology n)) →
    ∀ V ∈ B, ∀ n : ℕ, 0 < n → IsZero (Sheaf.H'.{u, u, u} F n V)

/-! ### The vanishing input of abelian Stacks 01FF -/

/-- **The vanishing input of abelian Stacks 01FF**, granted the abelian 01EW engine.  Let `X`
have a basis of quasi-compact opens whose binary intersections are quasi-compact, let `U` be a
quasi-compact open and let `E` be a filtered system of *injective* abelian sheaves.  Then
`Hⁿ⁺¹(U, colimᵢ Eᵢ) = 0` for every `n`.

This is `CechToCohomologyOnBasis` applied to the basis of all quasi-compact opens and the
collection of finite covers by quasi-compact opens: those covers are cofinal
(`Stacks.Cohomology.Vanishing.exists_compactCover_refines`, Stacks 0069), only quasi-compact
opens occur in their Čech complexes
(`Stacks.Cohomology.Vanishing.compactCovers_mem_compactOpens`), and the positive-degree Čech
cohomology of the colimit for such a cover vanishes
(`Stacks.Cohomology.AbelianVanishing.isZero_cechComplex_homology_colimit_of_injective`).

It is exactly the hypothesis `hvan` of `isIso_colimit_post_H'functor_of_isCompact`. -/
theorem isZero_H'_succ_colimit_of_injective (h01EW : CechToCohomologyOnBasis X)
    {I : Type u} [SmallCategory I] [IsFiltered I]
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    (U : Opens X) (hU : IsCompact (U : Set X))
    (E : I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hE : ∀ i, Injective (E.obj i)) (n : ℕ) :
    IsZero (Sheaf.H'.{u, u, u} (colimit E) (n + 1) U) :=
  h01EW (colimit E) (compactOpens X) (isBasis_compactOpens hBasis) (compactCovers X)
    (compactCovers_mem_compactOpens hInter)
    (exists_compactCover_refines hBasis hInter)
    (fun W hW p hp => by
      obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp).symm⟩
      exact AbelianVanishing.isZero_cechComplex_homology_colimit_of_injective
        hBasis hInter W hW E hE m)
    U hU (n + 1) (Nat.succ_pos n)

/-! ### Abelian Stacks 01FF, granted the abelian 01EW engine -/

section Index

universe t s

/-- **Stacks 01FF for abelian sheaves.**  Let `X` be a topological space with a basis of
quasi-compact opens whose binary intersections are quasi-compact and let `U` be a quasi-compact
open of `X`.  Then for every filtered system `F` of abelian sheaves and every degree `q` the
canonical map `colimᵢ Hᑫ(U, Fᵢ) ⟶ Hᑫ(U, colimᵢ Fᵢ)` is an isomorphism.

The only hypothesis beyond the geometry is `CechToCohomologyOnBasis X`, the abelian 01EW engine:
`isIso_colimit_post_H'functor_of_isCompact` has no other open input, and
`isZero_H'_succ_colimit_of_injective` discharges the one it does have.  This is the shape the two
colimit-comparison clauses of Stacks 0A37 need on the limit space.

The index category is *not* pinned to the universe of the space and the coefficients: its objects
live in `Type t`, its morphisms in `Type s`, and all that is asked of them is that both be
`u`-small.  The space and the coefficients remain in one universe `u`, which is forced:
`Sheaf.H'` is `Ext` out of the free abelian sheaf on `yoneda.obj U`, so its coefficient universe
is the morphism universe of the site, and the site `Opens X` of a space `X : Type u` has
`Category.{u}`.

Smallness of the index is what makes the statement available at all — `colimit.post` needs the
two colimits to exist, and `AddCommGrpCat.{u}` has colimits of shape `I` exactly when `I` is
`u`-small — and it is also all the proof needs: the two `UnivLE` instances give an equivalence
`I ≌ Shrink (ShrinkHoms I)` onto a genuinely `u`-small model, on which the pinned statement above
applies, and `Limits.preservesColimitsOfShape_of_equiv` carries the conclusion back.  The input
statements are therefore left at their own universes and nothing below this file changes. -/
theorem isIso_colimit_post_H'functor_of_cechToCohomology (h01EW : CechToCohomologyOnBasis X)
    {I : Type t} [Category.{s} I] [IsFiltered I] [UnivLE.{t, u}] [UnivLE.{s, u}]
    (hBasis : PrespectralSpace X) (hInter : QuasiSeparatedSpace X)
    (U : Opens X) (hU : IsCompact (U : Set X))
    (F : I ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (q : ℕ) :
    IsIso (colimit.post F (H'functor U q)) := by
  have e : I ≌ Shrink.{u} (ShrinkHoms.{t} I) :=
    (ShrinkHoms.equivalence.{u} I).trans (Shrink.equivalence.{u} (ShrinkHoms.{t} I))
  have : IsFiltered (Shrink.{u} (ShrinkHoms.{t} I)) := IsFiltered.of_equivalence e
  have : PreservesColimitsOfShape (Shrink.{u} (ShrinkHoms.{t} I)) (H'functor U q) := by
    constructor
    intro G
    have := isIso_colimit_post_H'functor_of_isCompact hBasis hInter U hU
      (isZero_H'_succ_colimit_of_injective h01EW hBasis hInter U hU) G q
    exact preservesColimit_of_isIso_post (H'functor U q) G
  have : PreservesColimitsOfShape I (H'functor U q) :=
    preservesColimitsOfShape_of_equiv e.symm _
  infer_instance

end Index

end Stacks.Cohomology.AbelianColimit

end
