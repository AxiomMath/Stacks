module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ExtSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ExtSheafStalkIdentification
import StacksCore.Tactic.StacksAttribute

/-!
# The four clauses of Tag 0ECM for the Ext sheaves of a dualizing complex

Let `X` be a locally Noetherian scheme, let `ω_X^• = K` be a dualizing complex on `X` with its
associated dimension function `δ` ([Stacks, Tag 0AWF]), let `F` be a coherent `𝒪_X`-module, and let

`𝓔ⁱ = 𝓔xt^{-i}_{𝒪_X}(F, ω_X^•)`

be the Ext sheaves (`Stacks.Duality.extSheafOf`). [Stacks, Tag 0ECM] asserts that each `𝓔ⁱ` is
coherent and, at every point `x`, the four clauses proved here.

The clauses are `Stacks.Duality.extSheaf_stalk_degree_range` and its three companions in
`ExtSheafDepthDimension.lean`, stated for an arbitrary family `E` satisfying
`Stacks.Duality.IsStalkwiseDualExt`, applied to the Ext sheaves themselves: that hypothesis is
discharged by `Stacks.Duality.isStalkwiseDualExt_extSheafOf` and
`Stacks.Duality.nonempty_stalk_extSheafOf_moduleExtInto`, so the four statements hold at the
hypotheses of the source and nothing is assumed about `𝓔ⁱ`.

## Main results

* `Stacks.Duality.isStalkwiseDualExt_extSheafOf_of_isDualizingComplex` — the bundle, discharged.
* `Stacks.Duality.extSheaf_stalk_degree_range_of_isDualizingComplex` — clause (1).
* `Stacks.Duality.supportDim_extSheaf_stalk_le_of_isDualizingComplex` — clause (2).
* `Stacks.Duality.depth_stalk_eq_iInf_nontrivial_extSheaf_stalk_of_isDualizingComplex` —
  clause (3).
* `Stacks.Duality.exists_nontrivial_extSheaf_stalk_iff_depth_add_le_of_isDualizingComplex` —
  clause (4).

The coherence assertion is `Stacks.Duality.isCoherent_extSheafOf`, in `ExtSheafCoherent.lean`.

## Implementation notes

`δ` is `Stacks.Duality.associatedShiftFunction K`, the shift function of `K` itself, which is a
dimension function associated to `K` by [Stacks, Tag 0AWF]
(`Stacks.Duality.isUniversallyCatenary_and_isDimensionFunction_associatedShiftFunction`). The
source says "with associated dimension function `δ`"; taking `K`'s own shift function is that
hypothesis, not a specialisation of it, because 0AWF produces `δ` from `K` and the clauses are
insensitive to which representative of the dimension function is used.

Clause (4) is read pointwise and clause (2) in `WithBot ℕ∞`, exactly as in the general lemmas; see
the implementation notes of `ExtSheafDepthDimension.lean` for why those readings are faithful.

## References

* [Stacks Project, Tag 0ECM](https://stacks.math.columbia.edu/tag/0ECM)
* [Stacks Project, Tag 0AWF](https://stacks.math.columbia.edu/tag/0AWF)
* [Stacks Project, Tag 0A6H](https://stacks.math.columbia.edu/tag/0A6H)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

-- Standard model only: `Stacks.Duality.IsStalkwiseDualExt`,
--   `Stacks.Duality.associatedShiftFunction`.
attribute [local instance 10000] HasDerivedCategory.standard

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

/-- **The bundle of `Stacks.Duality.IsStalkwiseDualExt`, discharged for the actual Ext sheaves.**
For `F` coherent on a locally Noetherian scheme and `K` a dualizing complex, the family
`𝓔ⁱ = 𝓔xt^{-i}(F, K)` satisfies `Stacks.Duality.IsStalkwiseDualExt` with `δ` the shift function of
`K`. -/
theorem isStalkwiseDualExt_extSheafOf_of_isDualizingComplex (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) :
    IsStalkwiseDualExt F K (associatedShiftFunction K) (extSheafOf F K) :=
  isStalkwiseDualExt_extSheafOf F hK fun x i =>
    nonempty_stalk_extSheafOf_moduleExtInto F hK x i

/-- **Stacks Project, Tag 0ECM, clause (1).** For a coherent module `F` on a locally Noetherian
scheme and a dualizing complex `K` with associated dimension function `δ`, a nonzero stalk of the
Ext sheaf `𝓔ⁱ = 𝓔xt^{-i}(F, K)` at `x` forces `δ(x) ≤ i ≤ δ(x) + dim Supp(F_x)`; in particular that
dimension is finite. -/
@[stacks 0ECM "clause (1): E^i_x ≠ 0 → δ(x) ≤ i ≤ δ(x) + dim Supp(F_x), for E^i the Ext sheaf \
Ext^{-i}(F, K) of a dualizing complex K with its associated dimension function δ"]
theorem extSheaf_stalk_degree_range_of_isDualizingComplex (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (x : X) (i : ℤ)
    (hi : Nontrivial ↑((extSheafOf F K i).presheaf.stalk x)) :
    associatedShiftFunction K x ≤ i ∧ ∃ d : ℕ,
      Module.supportDim ↑(X.presheaf.stalk x) ↑(F.presheaf.stalk x) = (d : WithBot ℕ∞) ∧
        i ≤ associatedShiftFunction K x + d :=
  extSheaf_stalk_degree_range F K (associatedShiftFunction K) (extSheafOf F K)
    (isStalkwiseDualExt_extSheafOf_of_isDualizingComplex F hK) x i hi

/-- **Stacks Project, Tag 0ECM, clause (2).** The stalk of `𝓔^{i + δ(x)}` at `x` has support of
dimension at most `i`; for `i < 0` the bound is `⊥`, which says that the stalk vanishes. -/
@[stacks 0ECM "clause (2): dim Supp(E^{i + δ(x)}_x) ≤ i, for E^i the Ext sheaf Ext^{-i}(F, K) of \
a dualizing complex K with its associated dimension function δ"]
theorem supportDim_extSheaf_stalk_le_of_isDualizingComplex (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (x : X) (i : ℤ) :
    Module.supportDim ↑(X.presheaf.stalk x)
        ↑((extSheafOf F K (i + associatedShiftFunction K x)).presheaf.stalk x) ≤
      if 0 ≤ i then ((i.toNat : ℕ∞) : WithBot ℕ∞) else ⊥ :=
  supportDim_extSheaf_stalk_le F K (associatedShiftFunction K) (extSheafOf F K)
    (isStalkwiseDualExt_extSheafOf_of_isDualizingComplex F hK) x i

/-- **Stacks Project, Tag 0ECM, clause (3).** The depth of `F_x` is the least `i ≥ 0` for which the
stalk of `𝓔^{i + δ(x)}` at `x` is nonzero. If all of these stalks vanish, both sides are `⊤`. -/
@[stacks 0ECM "clause (3): depth(F_x) = least i ≥ 0 with E^{i + δ(x)}_x ≠ 0, for E^i the Ext \
sheaf Ext^{-i}(F, K) of a dualizing complex K with its associated dimension function δ"]
theorem depth_stalk_eq_iInf_nontrivial_extSheaf_stalk_of_isDualizingComplex (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (x : X) :
    Module.depth ↑(X.presheaf.stalk x) (IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x))
        ↑(F.presheaf.stalk x) =
      ⨅ (k : ℕ) (_ : Nontrivial
        ↑((extSheafOf F K ((k : ℤ) + associatedShiftFunction K x)).presheaf.stalk x)), (k : ℕ∞) :=
  depth_stalk_eq_iInf_nontrivial_extSheaf_stalk F K (associatedShiftFunction K) (extSheafOf F K)
    (isStalkwiseDualExt_extSheafOf_of_isDualizingComplex F hK) x

/-- **Stacks Project, Tag 0ECM, clause (4).** A point `x` lies in the support of `⨁_{j ≤ i} 𝓔^j` —
that is, some `𝓔^j` with `j ≤ i` has nonzero stalk at `x` — exactly when the depth of `F_x` is
finite and `depth(F_x) + δ(x) ≤ i`. -/
@[stacks 0ECM "clause (4): x ∈ Supp(⊕_{j ≤ i} E^j) ↔ depth(F_x) + δ(x) ≤ i, for E^i the Ext \
sheaf Ext^{-i}(F, K) of a dualizing complex K with its associated dimension function δ"]
theorem exists_nontrivial_extSheaf_stalk_iff_depth_add_le_of_isDualizingComplex (F : X.Modules)
    [_root_.SheafOfModules.IsCoherent F] {K : DerivedCategory X.Modules}
    (hK : IsDualizingComplex K) (x : X) (i : ℤ) :
    (∃ j : ℤ, j ≤ i ∧ Nontrivial ↑((extSheafOf F K j).presheaf.stalk x)) ↔
      ∃ n : ℕ, Module.depth ↑(X.presheaf.stalk x)
            (IsLocalRing.maximalIdeal ↑(X.presheaf.stalk x)) ↑(F.presheaf.stalk x) = (n : ℕ∞) ∧
          (n : ℤ) + associatedShiftFunction K x ≤ i :=
  exists_nontrivial_extSheaf_stalk_iff_depth_add_le F K (associatedShiftFunction K)
    (extSheafOf F K) (isStalkwiseDualExt_extSheafOf_of_isDualizingComplex F hK) x i

end Stacks.Duality

end
