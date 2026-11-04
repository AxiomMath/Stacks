module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DualOfAPerfectComplex
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.HomFromAPerfectComplex
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.PerfectHomVanishingWindow
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.QuasiCompactBounded
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedDualTensorIsoSheafHom

/-!
# A window of Hom-vanishing against a perfect complex, from perfectness alone

Let `X` be a quasi-compact and quasi-separated scheme and let `K` be a perfect object of
`D(𝒪_X)`. [Stacks, Tag 09M4] produces a window of cohomological degrees `[a, b]` such that an
object of `D_{QCoh}(𝒪_X)` with no cohomology in the window admits no nonzero morphism from `K`,
and deduces that `Ext^n(K, L)` vanishes for all but finitely many `n` when `L` is bounded.

`Stacks.DerivedQCoh.exists_window_subsingleton_hom_of_isPerfect` and
`Stacks.DerivedQCoh.finite_setOf_not_subsingleton_hom_shift_of_isPerfect` state the two parts
with the dual perfect complex of [Stacks, Tag 08DQ] and the boundedness above of `K` of
[Stacks, Tags 0BCJ and 08E8] taken as data. The two statements below are the general form: they
take only the hypotheses of the source — `X` quasi-compact and quasi-separated, `K` perfect —
and construct what those two carry.

The two statements take the derived global sections functor `RΓ(X, -)` as a parameter, through
which the proof runs; `Stacks.DerivedQCoh.exists_window_subsingleton_hom_of_isPerfect_qcqs` and
`Stacks.DerivedQCoh.finite_setOf_not_subsingleton_hom_shift_of_isPerfect_qcqs` in
`StacksFrontier.AlgebraicGeometry.Duality.DetectingBoundednessOfAPerfectComplex` instantiate it at
derived global sections, which exist for every scheme, and carry the tag.

## Main results

* `Stacks.DerivedQCoh.exists_window_subsingleton_hom_of_isPerfect_general`: part (1) of the tag
  from perfectness of `K` alone.
* `Stacks.DerivedQCoh.finite_setOf_not_subsingleton_hom_shift_of_isPerfect_general`: part (2) of
  the tag from perfectness of `K` alone.

## Implementation notes

**What replaces the carried data.** The boundedness above of `K` is
`Stacks.AlgebraicGeometry.PerfectCohomology.exists_isLE_of_isPerfect`, the globalization of the
local statement [Stacks, Tag 0FEP] along quasi-compactness of `X`. The dual `K^∨` is written
down: it is `Stacks.SheafOfModules.derivedDual X.sheaf K`, the derived internal Hom into the
structure sheaf over the ringed site of opens of `X`. Its own boundedness above is
`Stacks.DerivedQCoh.exists_isLE_derivedDual`, which conjugates [Stacks, Tag 08JJ] through the
comparison of the ringed-site perfectness predicate of [Stacks, Tag 08G5] with the ringed-space
one of [Stacks, Tag 08CM] that the window is stated at.

Quasi-coherence of the cohomology sheaves of `K^∨ ⊗^𝐋 M` is
`AlgebraicGeometry.TorFormula.isQuasicoherent_homology_derivedTensor` applied to
`Stacks.DerivedQCoh.isQuasicoherent_homology_derivedDual`: the dual lies in `D_QCoh(𝒪_X)`, and
[Stacks, Tag 08DX] closes that subcategory under the derived tensor product.

The implication from vanishing of `H⁰(X, K^∨ ⊗^𝐋 M)` to vanishing of `Hom_{D(𝒪_X)}(K, M)`,
step (5) of the proof of [Stacks, Tag 08JJ], is
`Stacks.DerivedQCoh.subsingleton_hom_of_isZero_homology_derivedTensorDual`, in the one direction
consumed here. It identifies the pair of objects `M ⊗^𝐋 K^∨` and `R𝓗om(K, M)` through the
diagonal morphism of [Stacks, Tag 0BYS], which [Stacks, Tag 0ATN] part (1) inverts for perfect
`K`; the canonical map of [Stacks, Tag 08JD] is not used.

## References

* [Stacks Project, Tag 09M4](https://stacks.math.columbia.edu/tag/09M4)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0ATN](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology (sectionsFunctor)
open Stacks.Cohomology.TorAmplitude (derTensor)

universe u

namespace Stacks.DerivedQCoh

attribute [local instance 100000] HasDerivedCategory.standard

section MainGeneral

variable (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
  (RΓ : DerivedCategory X.Modules ⥤ DerivedCategory (ModuleCat.{u} Γ(X, ⊤)))
  (α : (sectionsFunctor X ⊤).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RΓ)
  [RΓ.IsRightDerivedFunctor α (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ))]
  (K : DerivedCategory X.Modules)

/-- The dual perfect complex data of a perfect object `K`, built from `derivedDual`. -/
private def dualData
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K) :
    DualPerfectComplexData X RΓ K :=
  { dual := Stacks.SheafOfModules.derivedDual X.sheaf K
    upper := (Stacks.DerivedQCoh.exists_isLE_derivedDual X K hK).choose
    isLE_dual := (Stacks.DerivedQCoh.exists_isLE_derivedDual X K hK).choose_spec
    isQuasicoherent_derivedTensor := fun M hM =>
      AlgebraicGeometry.TorFormula.isQuasicoherent_homology_derivedTensor X _ M
        (fun j => isQuasicoherent_homology_derivedDual X K hK j) hM
    subsingleton_hom_of_isZero := fun M h =>
      subsingleton_hom_of_isZero_homology_derivedTensorDual X RΓ α K M hK h }

include α in
/-- **Stacks Project, Tag 09M4, part (1), from perfectness alone.** Let `X` be a quasi-compact
and quasi-separated scheme and let `K` be a perfect object of `D(𝒪_X)`. Then there are integers
`a ≤ b` such that every `L ∈ D_{QCoh}(𝒪_X)` whose cohomology sheaves vanish in the degrees
`a, a + 1, …, b` admits no nonzero morphism from `K`.

This is the general form of `Stacks.DerivedQCoh.exists_window_subsingleton_hom_of_isPerfect`:
the dual perfect complex of [Stacks, Tag 08DQ] and the boundedness above of `K` of
[Stacks, Tags 0BCJ and 08E8] are constructed from perfectness of `K` rather than taken as data,
so the hypotheses are exactly those of the source. -/
theorem exists_window_subsingleton_hom_of_isPerfect_general
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K) :
    ∃ a b : ℤ, a ≤ b ∧
      ∀ L : DerivedCategory X.Modules,
        (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsQuasicoherent) →
        (∀ i : ℤ, a ≤ i → i ≤ b → IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj L)) →
        Subsingleton (K ⟶ L) := by
  obtain ⟨bK, hKLE⟩ :=
    Stacks.AlgebraicGeometry.PerfectCohomology.exists_isLE_of_isPerfect X K hK
  exact exists_window_subsingleton_hom_of_isPerfect X RΓ α K hK (dualData X RΓ α K hK) bK hKLE

include α in
/-- **Stacks Project, Tag 09M4, part (2), from perfectness alone.** Let `X` be a quasi-compact
and quasi-separated scheme, let `K` be a perfect object of `D(𝒪_X)` and let `L` be a bounded
object of `D_{QCoh}(𝒪_X)`. Then `Ext^n_{D(𝒪_X)}(K, L) = Hom_{D(𝒪_X)}(K, L⟦n⟧)` vanishes for all
but finitely many `n`.

Outside a bounded range of `n` the shift `L⟦n⟧` has no cohomology at all in the window of part
(1), because `L` is bounded. The window is the one of
`exists_window_subsingleton_hom_of_isPerfect_general`, so the hypotheses are those of the
source and nothing is taken as data. -/
theorem finite_setOf_not_subsingleton_hom_shift_of_isPerfect_general
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K)
    (L : DerivedCategory X.Modules)
    (hLqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsQuasicoherent)
    (c d : ℤ) (hLGE : L.IsGE c) (hLLE : L.IsLE d) :
    {n : ℤ | ¬ Subsingleton (K ⟶ L⟦n⟧)}.Finite := by
  obtain ⟨bK, hKLE⟩ :=
    Stacks.AlgebraicGeometry.PerfectCohomology.exists_isLE_of_isPerfect X K hK
  exact finite_setOf_not_subsingleton_hom_shift_of_isPerfect X RΓ α K hK
    (dualData X RΓ α K hK) bK hKLE L hLqc c d hLGE hLLE

end MainGeneral

end Stacks.DerivedQCoh

end
