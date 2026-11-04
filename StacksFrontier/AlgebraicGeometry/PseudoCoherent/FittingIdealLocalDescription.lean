module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FittingIdeal

/-!
# The local description of the Fitting ideal sheaf of a pseudo-coherent complex

`AlgebraicGeometry.fittingIdealSheaf` is `Scheme.IdealSheafData.ofIdeals` applied to the family
whose value on an affine open `U` is the infimum of the ideals of minors of all bounded-above
finite free models over `U` of all complexes representing `E`. Being a largest quasi-coherent
ideal sheaf below a family, it comes with one inclusion for free:
`AlgebraicGeometry.ideal_fittingIdealSheaf_le` bounds it above by the ideal of minors of any one
model. This file supplies the arguments that the reverse inclusion feeds, and isolates exactly
what the reverse inclusion needs.

The reverse inclusion is a *lower* bound on `ofIdeals`, and `ofIdeals A` is by definition the
supremum of the quasi-coherent ideal sheaves below `A`. A lower bound therefore cannot be read
off the family: it has to be a quasi-coherent ideal sheaf `J` with `J.ideal ≤ A`. Everything
below is phrased in terms of such a `J`, so that the geometric statements the source's
applications need — finite type of the Fitting ideal sheaf, and the vanishing of its support
over an open where the index matches the ranks — follow from the purely local statement that
`J` realizes the ideals of minors.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.disjoint_support_of_forall_exists_ideal_eq_top`: an
  ideal sheaf which is the unit ideal on affine opens covering a given open is supported away
  from that open.
* `AlgebraicGeometry.Scheme.IdealSheafData.subset_support_of_ideal_eq_bot`: an affine open on
  which an ideal sheaf vanishes lies in its support.
* `AlgebraicGeometry.le_fittingIdealSheaf_of_le_minorIdeal`: a quasi-coherent ideal sheaf which
  on every affine open is contained in the ideal of minors of every bounded-above finite free
  model is contained in the Fitting ideal sheaf. This is the reverse inclusion, reduced to the
  construction of one quasi-coherent ideal sheaf.
* `AlgebraicGeometry.ideal_fittingIdealSheaf_eq_minorIdeal`: with such an ideal sheaf realizing
  the ideal of minors on an affine open, the Fitting ideal sheaf *equals* the ideal of minors
  there, which is the local description of [Stacks, Tag 0ESP].
* `AlgebraicGeometry.isFiniteType_fittingIdealSheaf` and
  `AlgebraicGeometry.disjoint_support_fittingIdealSheaf`: the two consequences of the local
  description that the blowup construction of [Stacks, Tag 0ESQ] consumes.
* `AlgebraicGeometry.ideal_fittingIdealSheaf_eq_bot_of_card_lt_minorSize` and
  `AlgebraicGeometry.not_disjoint_support_fittingIdealSheaf_of_card_lt_minorSize`: for an index
  `k` far enough below the alternating sum of the ranks of a model the Fitting ideal sheaf
  vanishes on that affine open, and then its support contains it. So the disjointness statement
  is false for a freely chosen index `k`: it can only hold once `k` is tied to the ranks.

## Implementation notes

The ideal of minors is written out as `minorIdeal (M.matrix p) (M.toFreeData.minorSize p k).toNat`
rather than as `M.fittingIdeal p k`, which is the same ideal by
`AlgebraicGeometry.FreeModel.fittingIdeal_eq`, so that the statements match the form in which
`AlgebraicGeometry.ideal_fittingIdealSheaf_le` is stated.

`Scheme.IdealSheafData.IsFiniteType` is the finite-type predicate of the Fitting ideal sheaves of
a module, `∀ U, (I.ideal U).FG`; it is reused here so that the complex and the module case speak
of one predicate.

The vanishing statement needs no hypothesis on `E` beyond the existence of one model, and the
sizes it asks for do occur: a model all of whose ranks vanish has alternating rank sum `0`, so
every negative index `k` satisfies the hypothesis.

## References

* [Stacks Project, Tag 0ESP](https://stacks.math.columbia.edu/tag/0ESP)
* [Stacks Project, Tag 0ESQ](https://stacks.math.columbia.edu/tag/0ESQ)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u w

/-- An ideal sheaf whose ideal is the unit ideal on affine opens covering an open `U` has support
disjoint from `U`: the support of an ideal sheaf meets an affine open in the zero locus of its
ideal there, and the zero locus of the unit ideal is empty. -/
theorem Scheme.IdealSheafData.disjoint_support_of_forall_exists_ideal_eq_top
    {X : Scheme.{u}} (I : X.IdealSheafData) (U : X.Opens)
    (h : ∀ x ∈ U, ∃ V : X.affineOpens, x ∈ V.1 ∧ I.ideal V = ⊤) :
    Disjoint (U : Set X) (I.support : Set X) := by
  rw [Set.disjoint_left]
  intro x hxU hxI
  obtain ⟨V, hxV, hV⟩ := h x hxU
  have hx := (Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := V) hxV).mp hxI
  rw [hV] at hx
  simp only [Scheme.mem_zeroLocus_iff] at hx
  have h1 := hx 1 Submodule.mem_top
  rw [Scheme.basicOpen_one] at h1
  exact h1 hxV

/-- An affine open on which an ideal sheaf has zero ideal is contained in its support: every
point of the affine open lies in the zero locus of the zero ideal. -/
theorem Scheme.IdealSheafData.subset_support_of_ideal_eq_bot {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.affineOpens) (h : I.ideal U = ⊥) :
    (U.1 : Set X) ⊆ (I.support : Set X) := by
  intro x hx
  refine (Scheme.IdealSheafData.mem_support_iff_of_mem (I := I) (U := U) hx).mpr ?_
  rw [h]
  simp only [Scheme.mem_zeroLocus_iff]
  intro f hf
  have hf0 : f = 0 := hf
  subst hf0
  simp

variable {X : Scheme.{u}} [HasDerivedCategory.{w} X.Modules]

/-- **The reverse inclusion of the local description of [Stacks, Tag 0ESP], reduced to one
quasi-coherent ideal sheaf.** A quasi-coherent sheaf of ideals which on every affine open is
contained in the ideal of minors of the matrix of `d_p` of every bounded-above finite free model,
over that open, of every complex representing `E`, is contained in the Fitting ideal sheaf.

The Fitting ideal sheaf is the largest quasi-coherent sheaf of ideals with that property, so this
is the defining property of `Scheme.IdealSheafData.ofIdeals`. It is stated because it is the only
route to a lower bound on the Fitting ideal sheaf: a supremum of quasi-coherent ideal sheaves is
bounded below only by exhibiting one of them. -/
theorem le_fittingIdealSheaf_of_le_minorIdeal
    (E : DerivedCategory X.Modules) (p k : ℤ) (J : X.IdealSheafData)
    (hJ : ∀ (U : X.affineOpens) (K : CochainComplex X.Modules ℤ)
      (_ : Nonempty (DerivedCategory.Q.obj K ≅ E)) (M : FreeModel K U.1),
      J.ideal U ≤ minorIdeal (M.matrix p) (M.toFreeData.minorSize p k).toNat) :
    J ≤ fittingIdealSheaf E p k :=
  Scheme.IdealSheafData.le_ofIdeals_iff.mpr fun U =>
    le_iInf fun K => le_iInf fun hK => le_iInf fun M => hJ U K hK M

/-- **The local description of [Stacks, Tag 0ESP], granted a quasi-coherent ideal sheaf realizing
the ideals of minors.** On an affine open `U` carrying a bounded-above finite free model of a
complex representing `E`, the Fitting ideal sheaf is the ideal generated by the minors of the
matrix of `d_p` of size `-k + n_{p+1} - n_{p+2} + ⋯ + (-1)^{b-p+1} n_b`.

One inclusion is `AlgebraicGeometry.ideal_fittingIdealSheaf_le`; the other is
`AlgebraicGeometry.le_fittingIdealSheaf_of_le_minorIdeal` applied to `J`. -/
theorem ideal_fittingIdealSheaf_eq_minorIdeal
    (E : DerivedCategory X.Modules) (p k : ℤ) (J : X.IdealSheafData)
    (hJ : ∀ (U : X.affineOpens) (K : CochainComplex X.Modules ℤ)
      (_ : Nonempty (DerivedCategory.Q.obj K ≅ E)) (M : FreeModel K U.1),
      J.ideal U ≤ minorIdeal (M.matrix p) (M.toFreeData.minorSize p k).toNat)
    (U : X.affineOpens) (K : CochainComplex X.Modules ℤ)
    (hK : Nonempty (DerivedCategory.Q.obj K ≅ E)) (M : FreeModel K U.1)
    (hJU : minorIdeal (M.matrix p) (M.toFreeData.minorSize p k).toNat ≤ J.ideal U) :
    (fittingIdealSheaf E p k).ideal U =
      minorIdeal (M.matrix p) (M.toFreeData.minorSize p k).toNat :=
  le_antisymm (ideal_fittingIdealSheaf_le E p k U K hK M)
    (hJU.trans (le_fittingIdealSheaf_of_le_minorIdeal E p k J hJ U))

/-- **The Fitting ideal sheaf of a pseudo-coherent complex is of finite type**, granted a
quasi-coherent ideal sheaf realizing the ideals of minors on every affine open. This is the
analogue for a complex of [Stacks, Tag 0C3E], `AlgebraicGeometry.fittingIdeal_isFiniteType`.

On an affine open the ideal sheaf is then the ideal of minors of one model, and an ideal
generated by the minors of a fixed size of a matrix with finitely many rows and columns is
finitely generated. -/
theorem isFiniteType_fittingIdealSheaf
    (E : DerivedCategory X.Modules) (p k : ℤ) (J : X.IdealSheafData)
    (hJ : ∀ (U : X.affineOpens) (K : CochainComplex X.Modules ℤ)
      (_ : Nonempty (DerivedCategory.Q.obj K ≅ E)) (M : FreeModel K U.1),
      J.ideal U ≤ minorIdeal (M.matrix p) (M.toFreeData.minorSize p k).toNat)
    (hJ' : ∀ U : X.affineOpens, ∃ (K : CochainComplex X.Modules ℤ)
      (_ : Nonempty (DerivedCategory.Q.obj K ≅ E)) (M : FreeModel K U.1),
      minorIdeal (M.matrix p) (M.toFreeData.minorSize p k).toNat ≤ J.ideal U) :
    (fittingIdealSheaf E p k).IsFiniteType := by
  intro U
  obtain ⟨K, hK, M, hM⟩ := hJ' U
  rw [ideal_fittingIdealSheaf_eq_minorIdeal E p k J hJ U K hK M hM]
  exact fg_minorIdeal _ _

/-- **The Fitting ideal sheaf of a pseudo-coherent complex is supported away from an open where
it is the unit ideal**, granted a quasi-coherent ideal sheaf realizing the ideals of minors which
is the unit ideal on affine opens covering that open. This is the analogue for a complex of
[Stacks, Tag 0C3G], `AlgebraicGeometry.disjoint_support_fittingIdeal`.

The witness ideal sheaf is contained in the Fitting ideal sheaf, so the Fitting ideal sheaf is
the unit ideal on those affine opens too, and then its support avoids the open. -/
theorem disjoint_support_fittingIdealSheaf
    (E : DerivedCategory X.Modules) (p k : ℤ) (J : X.IdealSheafData)
    (hJ : ∀ (U : X.affineOpens) (K : CochainComplex X.Modules ℤ)
      (_ : Nonempty (DerivedCategory.Q.obj K ≅ E)) (M : FreeModel K U.1),
      J.ideal U ≤ minorIdeal (M.matrix p) (M.toFreeData.minorSize p k).toNat)
    (U : X.Opens) (hU : ∀ x ∈ U, ∃ V : X.affineOpens, x ∈ V.1 ∧ J.ideal V = ⊤) :
    Disjoint (U : Set X) ((fittingIdealSheaf E p k).support : Set X) := by
  refine Scheme.IdealSheafData.disjoint_support_of_forall_exists_ideal_eq_top _ U fun x hx => ?_
  obtain ⟨V, hxV, hV⟩ := hU x hx
  refine ⟨V, hxV, top_le_iff.mp ?_⟩
  rw [← hV]
  exact le_fittingIdealSheaf_of_le_minorIdeal E p k J hJ V

/-- **The Fitting ideal sheaf vanishes on an affine open where the prescribed size of the minors
exceeds the size of the matrix.** This is the second convention of [Stacks, Tag 0ESP], that the
ideal of `r × r` minors is zero when `r` exceeds `min (n_p) (n_{p+1})`, transported to the ideal
sheaf; only the inclusion `AlgebraicGeometry.ideal_fittingIdealSheaf_le` is needed. -/
theorem ideal_fittingIdealSheaf_eq_bot_of_card_lt_minorSize
    (E : DerivedCategory X.Modules) (p k : ℤ) (U : X.affineOpens)
    (K : CochainComplex X.Modules ℤ) (hK : Nonempty (DerivedCategory.Q.obj K ≅ E))
    (M : FreeModel K U.1)
    (h : (M.rank p : ℤ) < M.toFreeData.minorSize p k ∨
      (M.rank (p + 1) : ℤ) < M.toFreeData.minorSize p k) :
    (fittingIdealSheaf E p k).ideal U = ⊥ := by
  refine le_bot_iff.mp ((ideal_fittingIdealSheaf_le E p k U K hK M).trans ?_)
  rw [← M.fittingIdeal_eq p k]
  exact le_of_eq (M.toFreeData.fittingIdeal_eq_bot_of_card_lt_minorSize h)

/-- **The index of a Fitting ideal sheaf cannot be chosen freely.** On a nonempty affine open
carrying a bounded-above finite free model whose prescribed size of minors exceeds the size of
the matrix of `d_p`, the Fitting ideal sheaf vanishes, so its support contains that open and is
not disjoint from it.

For a model all of whose ranks vanish the alternating sum of the ranks above `p` is `0`, so the
hypothesis holds for every negative `k`. Disjointness of the support from an open is therefore a
statement about an index `k` tied to the ranks of the cohomology there, not about an arbitrary
index. -/
theorem not_disjoint_support_fittingIdealSheaf_of_card_lt_minorSize
    (E : DerivedCategory X.Modules) (p k : ℤ) (U : X.affineOpens)
    (K : CochainComplex X.Modules ℤ) (hK : Nonempty (DerivedCategory.Q.obj K ≅ E))
    (M : FreeModel K U.1)
    (h : (M.rank p : ℤ) < M.toFreeData.minorSize p k ∨
      (M.rank (p + 1) : ℤ) < M.toFreeData.minorSize p k)
    (hne : (U.1 : Set X).Nonempty) :
    ¬ Disjoint (U.1 : Set X) ((fittingIdealSheaf E p k).support : Set X) := by
  intro hdisj
  obtain ⟨x, hx⟩ := hne
  exact Set.disjoint_left.mp hdisj hx
    (Scheme.IdealSheafData.subset_support_of_ideal_eq_bot _ U
      (ideal_fittingIdealSheaf_eq_bot_of_card_lt_minorSize E p k U K hK M h) hx)

end

end AlgebraicGeometry

end
