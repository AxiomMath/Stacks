module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.AffineCurveTorsionBound
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.FieldExtensionTorsionBound
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.LocallyFiniteTypeSiteGabberInputs

/-!
# Input (2) of the vanishing above `d_V` in Stacks 0DC6: the bound along a field extension

Stacks 0DC6 uses the bound `cd_ℓ(L) ≤ cd_ℓ(K) + trdeg_K(L)` for a field extension `L/K` (Serre,
Cohomologie galoisienne, Chapter II, §4.2), for coefficients killed by an integer `n` invertible in
`K`. This is `AlgebraicGeometry.Scheme.TrdegVanishingBound n`, the second of the three inputs of
`AlgebraicGeometry.Scheme.LocallyFiniteTypeEtale.gabberVanishing_of_inputs`. This file proves it,
for every `n`.

The proof is that of Stacks 0F0T with coefficients killed by `n`. For `trdeg_K(L) ≤ 1`, `L` is the
directed union of its finitely generated `K`-subalgebras `K[s]`
(`AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_of_forall_adjoin`), each an affine scheme
of finite type and dimension at most one over `K` (Stacks 00P0), so of bound `1 + c` by Stacks 0F0S
(`AlgebraicGeometry.Scheme.isTorsionVanishingBound_one_add_of_topologicalKrullDim_le_one`). The
general case is the tower of transcendence degree one steps
(`AlgebraicGeometry.Scheme.isTorsionVanishingBound_add_trdeg_of_le_one_add`).

## Main results

* `AlgebraicGeometry.Scheme.isTorsionVanishingBound_spec_one_add_of_trdeg_le_one`: the case
  `trdeg_K(L) ≤ 1`.
* `AlgebraicGeometry.Scheme.trdegVanishingBound`: input (2), `TrdegVanishingBound n`, for every
  `n`.

## References

* [Stacks Project, Tag 0DC6](https://stacks.math.columbia.edu/tag/0DC6)
* [Stacks Project, Tag 0F0T](https://stacks.math.columbia.edu/tag/0F0T)
* J.-P. Serre, *Cohomologie galoisienne*, Chapter II, §4.2
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- **The bound along a field extension of transcendence degree at most one**, for coefficients
killed by a positive integer `n`: if `c` bounds the cohomology of `Spec K`, then `1 + c` bounds
that of `Spec L`. Every `K[s]`, `s` a finite subset of `L`, is affine of finite type over `K` and
of dimension at most `trdeg_K(L) ≤ 1` (Stacks 00P0), so Stacks 0F0S with coefficients killed by
`n` applies to it, and `Spec L` is the directed limit of the `Spec K[s]`. -/
theorem isTorsionVanishingBound_spec_one_add_of_trdeg_le_one {K L : Type u} [Field K] [Field L]
    [Algebra K L] (h : Algebra.trdeg K L ≤ 1) {n : ℕ} (hn : 0 < n) {c : WithBot ℕ∞}
    (hK : IsTorsionVanishingBound (Spec (.of K)) n c) :
    IsTorsionVanishingBound (Spec (.of L)) n (1 + c) := by
  refine isTorsionVanishingBound_spec_of_forall_adjoin K L fun s => ?_
  let A := Algebra.adjoin K (s : Set L)
  have : Algebra.FiniteType K A :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_adjoin_finset s)
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap K A))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  have hdim : topologicalKrullDim (Spec (.of A)) ≤ 1 := by
    refine (topologicalKrullDim_spec_adjoin_le_trdeg K L s).trans ?_
    have : Cardinal.toENat (Algebra.trdeg K L) ≤ 1 := by
      simpa using Cardinal.toENat.monotone' h
    exact_mod_cast this
  exact isTorsionVanishingBound_one_add_of_topologicalKrullDim_le_one
    (Spec.map (CommRingCat.ofHom (algebraMap K A))) hdim hn hK

/-- **Input (2) of Stacks 0DC6: `cd_n(L) ≤ cd_n(K) + trdeg_K(L)`** (Serre, Cohomologie galoisienne,
Chapter II, §4.2, for coefficients killed by `n`), for every integer `n`. An integer invertible in
the field `K` is positive, so the case of transcendence degree at most one
(`isTorsionVanishingBound_spec_one_add_of_trdeg_le_one`) feeds the tower
(`isTorsionVanishingBound_add_trdeg_of_le_one_add`). -/
theorem trdegVanishingBound (n : ℕ) : TrdegVanishingBound.{u} n := by
  intro K L _ _ _ hn c hK
  refine isTorsionVanishingBound_add_trdeg_of_le_one_add (fun K' L' _ _ _ hn' h c' hK' => ?_)
    K L hn c hK
  have hpos : 0 < n := Nat.pos_of_ne_zero fun h0 => by simp [h0] at hn'
  exact isTorsionVanishingBound_spec_one_add_of_trdeg_le_one h hpos hK'

end AlgebraicGeometry.Scheme

end
