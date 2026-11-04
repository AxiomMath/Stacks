module

public import StacksFrontier.AlgebraicGeometry.F6Rank89.StalkDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.FibrePointResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueField
public import StacksFrontier.RingTheory.KrullDimension.FiniteTypeNeTop

/-!
# The local dimension of a closed subscheme cut out by a regular sequence

Let `X` be a scheme locally of finite type over a field `k` and let `D` be a closed subscheme
whose ideal sheaf has, in the local ring at a point, a generating regular sequence of length
`n`. Then the dimension of `D` at that point is `n` less than the dimension of `X` there.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_subscheme_add_length`: the local dimension of a
  closed subscheme cut out by a regular sequence of length `n` is `n` less than the ambient
  one.
* `AlgebraicGeometry.topologicalKrullDimAt_lt_top`: the local dimension of a scheme locally of
  finite type over a field is finite.
* `AlgebraicGeometry.length_eq_of_topologicalKrullDimAt_add`: that length is determined by the
  dimension drop.

## Implementation notes

Both local dimensions are read through the dimension formula
`AlgebraicGeometry.topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk`, which splits the local
dimension into the transcendence degree of the residue field and the dimension of the local
ring. The transcendence-degree terms agree by
`AlgebraicGeometry.trdeg_residueField_of_surjectiveOnStalks`, a closed immersion being
surjective on stalks; the local rings differ by exactly the length of the regular sequence,
which is `Stacks.Divisors.ringKrullDim_stalk_subscheme_add_length`. No finiteness is needed
there, since the two formulas are added rather than subtracted.

Reading the length off the dimension drop does need finiteness, to cancel the dimension of the
subscheme from both sides; that is `AlgebraicGeometry.topologicalKrullDimAt_lt_top`, which
computes the local dimension on an affine chart whose ring is of finite type over the field.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A closed subscheme cut out in the local ring by a regular sequence of length `n` has local
dimension `n` less than the ambient scheme.** -/
theorem topologicalKrullDimAt_subscheme_add_length (k : Type u) [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (D : X.IdealSheafData) (z : D.subscheme)
    (rs : List (X.presheaf.stalk (D.subschemeι z)))
    (hreg : RingTheory.Sequence.IsRegular (X.presheaf.stalk (D.subschemeι z)) rs)
    (hstalk : IdealSheafData.stalk D (D.subschemeι z) = Ideal.ofList rs) :
    topologicalKrullDimAt D.subscheme z + (rs.length : WithBot ℕ∞)
      = topologicalKrullDimAt X (D.subschemeι z) := by
  let : Algebra k (X.residueField (D.subschemeι z)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop ≫
      X.Γevaluation (D.subschemeι z)).hom.toAlgebra
  let : Algebra k (D.subscheme.residueField z) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ p).appTop ≫
      D.subscheme.Γevaluation z).hom.toAlgebra
  rw [topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k X p (D.subschemeι z),
    topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k D.subscheme (D.subschemeι ≫ p) z,
    ← trdeg_residueField_of_surjectiveOnStalks k p D.subschemeι z, add_assoc,
    Stacks.Divisors.ringKrullDim_stalk_subscheme_add_length D z rs hreg hstalk]

/-- The local dimension of a scheme locally of finite type over a field is finite at every
point:  it is read on an affine chart, whose ring is of finite type over the field. -/
theorem topologicalKrullDimAt_lt_top (k : Type u) [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] (x : X) :
    topologicalKrullDimAt X x < ⊤ := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  let : Algebra k Γ(X, U) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appLE ⊤ U (by simp)).hom.toAlgebra
  have hft := p.finiteType_appLE (isAffineOpen_top _) hU (show U ≤ p ⁻¹ᵁ ⊤ by simp)
  let : Algebra.FiniteType k Γ(X, U) :=
    hft.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  have hfin : ringKrullDim Γ(X, U) < ⊤ :=
    lt_top_iff_ne_top.mpr (ringKrullDim_ne_top_of_finiteType (κ := k))
  refine ((topologicalKrullDimAt_isLeast X x).2 ⟨U, hxU, U.2, rfl⟩).trans_lt ?_
  have heq := IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph
  exact (heq.trans (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U))).symm ▸ hfin

/-- **The number of equations cutting out a closed subscheme is the drop in local dimension.**
If the ideal sheaf of `D` is generated in the local ring at a point by a regular sequence, then
any natural number realising the dimension drop there is the length of that sequence. -/
theorem length_eq_of_topologicalKrullDimAt_add (k : Type u) [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (D : X.IdealSheafData) (z : D.subscheme)
    (rs : List (X.presheaf.stalk (D.subschemeι z)))
    (hreg : RingTheory.Sequence.IsRegular (X.presheaf.stalk (D.subschemeι z)) rs)
    (hstalk : IdealSheafData.stalk D (D.subschemeι z) = Ideal.ofList rs) {c : ℕ}
    (hdim : topologicalKrullDimAt D.subscheme z + (c : WithBot ℕ∞)
      = topologicalKrullDimAt X (D.subschemeι z)) :
    c = rs.length := by
  have hlen := topologicalKrullDimAt_subscheme_add_length k p D z rs hreg hstalk
  have hbot : topologicalKrullDimAt D.subscheme z ≠ ⊥ := by
    obtain ⟨⟨V, hzV, -, hVeq⟩, -⟩ := topologicalKrullDimAt_isLeast D.subscheme z
    intro h
    exact ((topologicalKrullDim_eq_bot_iff_isEmpty (↥V)).mp (by rw [← hVeq, h])).false ⟨z, hzV⟩
  have htop : topologicalKrullDimAt D.subscheme z < ⊤ :=
    topologicalKrullDimAt_lt_top k (D.subschemeι ≫ p) z
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp hbot
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
    (show a ≠ ⊤ from fun h => absurd (ha.trans_lt htop) (by rw [h]; simp))
  have hA : topologicalKrullDimAt D.subscheme z = (m : WithBot ℕ∞) := by
    rw [← ha, ← hm]; rfl
  rw [hA] at hdim hlen
  have h : ((m + c : ℕ) : WithBot ℕ∞) = ((m + rs.length : ℕ) : WithBot ℕ∞) := by
    push_cast
    exact hdim.trans hlen.symm
  exact Nat.add_left_cancel (by exact_mod_cast h)

end AlgebraicGeometry

end
