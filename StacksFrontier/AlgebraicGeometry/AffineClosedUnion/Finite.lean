module

public import StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Global
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.ClosedUnion
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme

/-!
# A reduced scheme covered by finitely many affine closed subschemes is affine

This file carries the two-piece statement
`Stacks.AffineClosedUnion.isAffine_of_isClosedImmersion_union` to an arbitrary finite family,
which is the form in which [Stacks, Tag 09NL] is used in the proof of [Stacks, Tag 09NX].

The induction is *not* "the two-piece case plus induction" in the naive sense, and the extra
layer is the point of this file: the scheme-theoretic union of the tail of the family has to be
affine **and reduced** before the two-piece statement applies to it. Reducedness is arranged by
replacing each ideal sheaf by its radical, which changes neither the support nor the affineness
of the closed subscheme — a closed subscheme of an affine scheme is affine — and a finite
intersection of radical ideal sheaves is radical, so every intermediate union of the induction
is reduced by `AlgebraicGeometry.Scheme.IdealSheafData.isReduced_subscheme`. Replacing the
ideal sheaves by their radicals is harmless precisely because the hypothesis of the two-piece
statement that the induction needs is about supports.

With that, the whole family's intersection `⨅ i, (f i).ker.radical` is radical with support all
of `X`, so it is `⊥` on a reduced `X`, and `X(⊥) ≅ X`.

## Main results

* `Stacks.AffineClosedUnion.isAffine_subscheme_inf`: the scheme-theoretic union of two closed
  subschemes with affine pieces is affine as soon as it is reduced.
* `Stacks.AffineClosedUnion.isAffine_subscheme_finsetInf`: the same for a finite intersection of
  radical ideal sheaves.
* `Stacks.AffineClosedUnion.isAffine_of_isClosedImmersion_iUnion`: **the reduced case of
  [Stacks, Tag 09NL]** — a reduced scheme whose points are covered by finitely many affine
  closed subschemes is affine.

## Implementation notes

What is proved here is the case of a reduced ambient scheme, which is the case
[Stacks, Tag 09NX] uses — there 09NL is applied to `X_s` for `X` reduced, and an open subscheme
of a reduced scheme is reduced. The tag itself has no reducedness hypothesis, and the
`@[stacks 09NL]` attribute sits in
`StacksFrontier.AlgebraicGeometry.AffineClosedUnion.Unconditional`, which drops reducedness: the
reducedness of `X` is used here only through
`Stacks.AffineClosedUnion.isAffine_nilradical_subscheme_of_isClosedImmersion_iUnion`, which
holds for every `X`, and the remaining content of the tag is [Stacks, Tag 06AD] for the
thickening of the reduced induced subscheme, which
`Stacks.Thickenings.isAffine_of_isThickening` proves for every thickening.

## References

* [Stacks Project, Tag 09NL](https://stacks.math.columbia.edu/tag/09NL)
* [Stacks Project, Tag 09NX](https://stacks.math.columbia.edu/tag/09NX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace Stacks.AffineClosedUnion

variable {X : Scheme.{u}}

section Range

/-- A point of the closed subscheme cut out by `I` lies in the image of the closed subscheme cut
out by a larger `J` exactly when it lies in the support of `J`. -/
theorem mem_range_inclusion {I J : X.IdealSheafData} (h : I ≤ J) (x : I.subscheme) :
    x ∈ Set.range (inclusion h).base ↔ I.subschemeι x ∈ J.support := by
  have e : ∀ y : J.subscheme, I.subschemeι ((inclusion h).base y) = J.subschemeι y := fun y ↦ by
    rw [← Scheme.Hom.comp_apply, inclusion_subschemeι]
  constructor
  · rintro ⟨y, rfl⟩
    rw [e y]
    exact (range_subschemeι J).le ⟨y, rfl⟩
  · intro hx
    obtain ⟨y, hy⟩ := (range_subschemeι J).ge hx
    exact ⟨y, I.subschemeι.isClosedEmbedding.injective ((e y).trans hy)⟩

/-- The two closed subschemes cut out by `A` and by `B` cover the one cut out by `A ⊓ B`: that is
what makes `A ⊓ B` the scheme-theoretic union. -/
theorem range_inclusion_union (A B : X.IdealSheafData) :
    Set.range (inclusion (inf_le_left : A ⊓ B ≤ A)).base ∪
      Set.range (inclusion (inf_le_right : A ⊓ B ≤ B)).base = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  have hx : (A ⊓ B).subschemeι x ∈ (A ⊓ B).support :=
    (range_subschemeι (A ⊓ B)).le ⟨x, rfl⟩
  rw [Stacks.IdealSheafData.support_inf] at hx
  rcases hx with h | h
  · exact Or.inl ((mem_range_inclusion inf_le_left x).mpr h)
  · exact Or.inr ((mem_range_inclusion inf_le_right x).mpr h)

end Range

section Radical

/-- The radical of an ideal sheaf is its own radical. -/
theorem radical_radical (I : X.IdealSheafData) : I.radical.radical = I.radical := by
  ext U : 2
  rw [radical_ideal, radical_ideal, Ideal.radical_idem]

/-- An ideal sheaf equal to its own radical is componentwise radical. -/
theorem isRadical_ideal_of_radical_eq {J : X.IdealSheafData} (hJ : J.radical = J)
    (U : X.affineOpens) : (J.ideal U).IsRadical := by
  rw [← Ideal.radical_eq_iff, ← radical_ideal, hJ]

/-- The closed subscheme cut out by an ideal sheaf equal to its own radical is reduced. -/
theorem isReduced_subscheme_of_radical_eq {J : X.IdealSheafData} (hJ : J.radical = J) :
    IsReduced J.subscheme :=
  isReduced_subscheme J (isRadical_ideal_of_radical_eq hJ)

/-- A finite intersection of radical ideal sheaves is radical. -/
theorem radical_finsetInf {ι : Type*} (I : ι → X.IdealSheafData)
    (hrad : ∀ i, (I i).radical = I i) (s : Finset ι) : (s.inf I).radical = s.inf I := by
  refine Finset.inf_induction (p := fun J : X.IdealSheafData ↦ J.radical = J) radical_top
    (fun a ha b hb ↦ ?_) fun i _ ↦ hrad i
  rw [radical_inf, ha, hb]

/-- The support of a finite intersection of ideal sheaves is the union of the supports. -/
theorem support_finsetInf {ι : Type*} (I : ι → X.IdealSheafData) (s : Finset ι) :
    (s.inf I).support = s.sup fun i ↦ (I i).support := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.inf_empty, Finset.sup_empty, support_top]
  | insert a s _ ih =>
      rw [Finset.inf_insert, Finset.sup_insert, Stacks.IdealSheafData.support_inf, ih]

end Radical

section Induction

/-- **The scheme-theoretic union of two closed subschemes is affine once it is reduced.** This is
`Stacks.AffineClosedUnion.isAffine_of_isClosedImmersion_union` applied inside the union itself:
the two pieces are closed subschemes of it, they cover it by
`Stacks.AffineClosedUnion.range_inclusion_union`, and it is the ambient reduced scheme. -/
theorem isAffine_subscheme_inf (A B : X.IdealSheafData) [IsReduced (A ⊓ B).subscheme]
    [IsAffine A.subscheme] [IsAffine B.subscheme] : IsAffine (A ⊓ B).subscheme :=
  isAffine_of_isClosedImmersion_union (inclusion (inf_le_left : A ⊓ B ≤ A))
    (inclusion (inf_le_right : A ⊓ B ≤ B)) (range_inclusion_union A B)

/-- **The finite intersection of radical ideal sheaves with affine closed subschemes has affine
closed subscheme.** This is the induction that the two-piece statement does not give directly:
at each step the tail's union must be both affine — the inductive hypothesis — and reduced, and
reducedness is what radicality of the ideal sheaves supplies. -/
theorem isAffine_subscheme_finsetInf {ι : Type*} (I : ι → X.IdealSheafData)
    (hrad : ∀ i, (I i).radical = I i) (haff : ∀ i, IsAffine (I i).subscheme) (s : Finset ι) :
    IsAffine (s.inf I).subscheme := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.inf_empty]; infer_instance
  | insert a s _ ih =>
      rw [Finset.inf_insert]
      have hred : IsReduced (I a ⊓ s.inf I).subscheme :=
        isReduced_subscheme_of_radical_eq
          (by rw [radical_inf, hrad a, radical_finsetInf I hrad s])
      have := haff a
      exact isAffine_subscheme_inf (I a) (s.inf I)

end Induction

section Main

/-- **The reduced case of [Stacks, Tag 09NL].** A reduced scheme whose points are covered by
finitely many affine closed subschemes is affine.

The tag itself has no reducedness hypothesis; it holds without one as
`Stacks.AffineClosedUnion.isAffine_of_isClosedImmersion_iUnion_unconditional`. The
reduced case is the one [Stacks, Tag 09NX] applies. -/
theorem isAffine_of_isClosedImmersion_iUnion [IsReduced X] {ι : Type*} [Finite ι]
    {Z : ι → Scheme.{u}} (f : ∀ i, Z i ⟶ X) [∀ i, IsClosedImmersion (f i)] [∀ i, IsAffine (Z i)]
    (hcov : ⋃ i, Set.range (f i).base = Set.univ) : IsAffine X := by
  classical
  cases nonempty_fintype ι
  have hrad : ∀ i, ((f i).ker.radical).radical = (f i).ker.radical := fun i ↦ radical_radical _
  have haff : ∀ i, IsAffine ((f i).ker.radical).subscheme := fun i ↦ by
    have := isAffine_ker_subscheme (f i)
    exact isAffine_of_isAffineHom (inclusion (le_radical (f i).ker))
  have hsupp : (Finset.univ.inf fun i ↦ (f i).ker.radical).support = ⊤ := by
    rw [support_finsetInf, eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov ▸ Set.mem_univ x)
    refine Finset.le_sup (f := fun i ↦ ((f i).ker.radical).support) (Finset.mem_univ i) ?_
    rw [support_radical]
    exact (support_ker_eq_range (f i)).ge hi
  have hA := isAffine_subscheme_finsetInf (fun i ↦ (f i).ker.radical) hrad haff Finset.univ
  rw [Scheme.IdealSheafData.support_eq_top_iff.mp hsupp] at hA
  exact (IsAffine.iff_of_isIso (Scheme.IdealSheafData.subschemeι (⊥ : X.IdealSheafData))).mp hA

end Main

end Stacks.AffineClosedUnion

end
