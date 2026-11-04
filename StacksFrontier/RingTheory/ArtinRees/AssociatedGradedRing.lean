module

public import StacksFrontier.RingTheory.ArtinRees.AssociatedGraded
public import StacksFrontier.RingTheory.Filtration.AssociatedGradedAlgebra

/-!
# The Artin-Rees comparison of associated graded modules is an isomorphism of algebras

`associatedGraded_coker_equiv_of_isArtinReesConstant` compares the associated graded modules of
two nearby cokernels `N ⧸ g(M)` and `N ⧸ g'(M)` over `Gr_I(A)`. When `N` is the ring `A` itself
the two cokernels are quotient *rings*, their associated graded modules carry the multiplication
`AssociatedGraded.homogeneousMul`, and the comparison respects it — because, by `pieceEquiv_mk`,
the comparison is induced by the identity of `A`. That is what this file proves, in the bundled
form `AssociatedGraded.GradedAlgEquiv`.

## Main results

* `pieceEquiv_homogeneousMul`: the degreewise comparison of `Gr_I(A ⧸ R)` with `Gr_I(A ⧸ S)` is
  multiplicative whenever the two denominators agree, for `R` and `S` ideals.
* `pieceEquiv_homogeneousOne`: the same comparison is unital.
* `pieceEquiv_homogeneousMul_of_isArtinReesConstant`: multiplicativity under the hypotheses of
  Stacks 07VF.
* `associatedGraded_coker_algEquiv_of_isArtinReesConstant`: **Stacks 07VF for the associated
  graded algebra.** Two nearby cokernels of maps into `A` have isomorphic associated graded
  *algebras*, not merely isomorphic associated graded modules over `Gr_I(A)`.

## Implementation notes

The multiplicativity is proved first on classes of elements of `I^n` and then transported to
arbitrary homogeneous classes by `AssociatedGraded.exists_eq_mk_mkQ`; the only content is that
`R.mkQ` is multiplicative, which holds by `rfl` because the ring structure of `A ⧸ R` is defined
on representatives.

## References

* [Stacks Project, Tag 07VF](https://stacks.math.columbia.edu/tag/07VF)
* [Stacks Project, Section 15.4](https://stacks.math.columbia.edu/tag/07VD)
-/

@[expose] public section

universe u v

section

variable {A : Type u} [CommRing A]

open AssociatedGraded

/-- **The comparison of `Stacks 07VF` is multiplicative on classes.** When the two submodules of
`A` are ideals, `pieceEquiv` is induced by the identity of `A`, hence carries the product of the
classes of `z` and `w` to the product of their classes. -/
theorem pieceEquiv_homogeneousMul_mk (I R S : Ideal A) (i j : ℕ)
    (hi : (power (M := A) I (i + 1) ⊔ R).comap (power I i).subtype =
      (power (M := A) I (i + 1) ⊔ S).comap (power I i).subtype)
    (hj : (power (M := A) I (j + 1) ⊔ R).comap (power I j).subtype =
      (power (M := A) I (j + 1) ⊔ S).comap (power I j).subtype)
    (hij : (power (M := A) I (i + j + 1) ⊔ R).comap (power I (i + j)).subtype =
      (power (M := A) I (i + j + 1) ⊔ S).comap (power I (i + j)).subtype)
    (z : power (M := A) I i) (w : power (M := A) I j) :
    pieceEquiv I R S (i + j) hij
        (homogeneousMul I (mk I i ⟨R.mkQ z, mkQ_mem_power I R i z.property⟩)
          (mk I j ⟨R.mkQ w, mkQ_mem_power I R j w.property⟩)) =
      homogeneousMul I (pieceEquiv I R S i hi (mk I i ⟨R.mkQ z, mkQ_mem_power I R i z.property⟩))
        (pieceEquiv I R S j hj (mk I j ⟨R.mkQ w, mkQ_mem_power I R j w.property⟩)) := by
  rw [homogeneousMul_mk, pieceEquiv_mk, pieceEquiv_mk, homogeneousMul_mk]
  exact (pieceEquiv_mk I R S (i + j) hij ⟨z * w, mul_mem_power I z.property w.property⟩).trans
    rfl

/-- **The comparison of `Stacks 07VF` is multiplicative.** When the two submodules of `A` are
ideals, the degreewise comparison of `Gr_I(A ⧸ R)` with `Gr_I(A ⧸ S)` respects the
multiplication of the associated graded algebras. -/
theorem pieceEquiv_homogeneousMul (I R S : Ideal A) (i j : ℕ)
    (hi : (power (M := A) I (i + 1) ⊔ R).comap (power I i).subtype =
      (power (M := A) I (i + 1) ⊔ S).comap (power I i).subtype)
    (hj : (power (M := A) I (j + 1) ⊔ R).comap (power I j).subtype =
      (power (M := A) I (j + 1) ⊔ S).comap (power I j).subtype)
    (hij : (power (M := A) I (i + j + 1) ⊔ R).comap (power I (i + j)).subtype =
      (power (M := A) I (i + j + 1) ⊔ S).comap (power I (i + j)).subtype)
    (x : piece (M := A ⧸ R) I i) (y : piece (M := A ⧸ R) I j) :
    pieceEquiv I R S (i + j) hij (homogeneousMul I x y) =
      homogeneousMul I (pieceEquiv I R S i hi x) (pieceEquiv I R S j hj y) := by
  obtain ⟨z, rfl⟩ := exists_eq_mk_mkQ I R i x
  obtain ⟨w, rfl⟩ := exists_eq_mk_mkQ I R j y
  exact pieceEquiv_homogeneousMul_mk I R S i j hi hj hij z w

/-- **The comparison of `Stacks 07VF` is unital.** It carries the class of `1` in degree zero to
the class of `1` in degree zero. -/
theorem pieceEquiv_homogeneousOne (I R S : Ideal A)
    (h0 : (power (M := A) I (0 + 1) ⊔ R).comap (power I 0).subtype =
      (power (M := A) I (0 + 1) ⊔ S).comap (power I 0).subtype) :
    pieceEquiv I R S 0 h0 (homogeneousOne I) = homogeneousOne I :=
  pieceEquiv_mk I R S 0 h0 ⟨1, by rw [power_zero]; trivial⟩

/-- **Stacks 07VF for the associated graded algebra.** If `c` works in the Artin-Rees lemma for
two `A`-linear maps `g, g' : L → A` and they agree modulo `I^{c+1}`, then the degreewise
comparison of `Gr_I(A ⧸ g(L))` with `Gr_I(A ⧸ g'(L))` supplied by
`associatedGraded_coker_equiv_of_isArtinReesConstant` respects the multiplication: the two
cokernels have the same associated graded *algebra*, not merely the same associated graded
module over `Gr_I(A)`. -/
theorem pieceEquiv_homogeneousMul_of_isArtinReesConstant (I : Ideal A)
    {L : Type v} [AddCommGroup L] [Module A L] (g g' : L →ₗ[A] A) (c : ℕ)
    (hg : IsArtinReesConstant I g c) (hg' : IsArtinReesConstant I g' c)
    (hgg' : CongruentModPow I g g' (c + 1)) (i j : ℕ)
    (x : piece (M := A ⧸ LinearMap.range g) I i)
    (y : piece (M := A ⧸ LinearMap.range g) I j) :
    pieceEquiv I (LinearMap.range g) (LinearMap.range g') (i + j)
        (presentation_denominator_eq I g g' c (i + j) hg hg' hgg')
        (homogeneousMul I x y) =
      homogeneousMul I
        (pieceEquiv I (LinearMap.range g) (LinearMap.range g') i
          (presentation_denominator_eq I g g' c i hg hg' hgg') x)
        (pieceEquiv I (LinearMap.range g) (LinearMap.range g') j
          (presentation_denominator_eq I g g' c j hg hg' hgg') y) :=
  pieceEquiv_homogeneousMul I (LinearMap.range g) (LinearMap.range g') i j _ _ _ x y

/-- **Stacks 07VF for the associated graded algebra**, bundled. If `c` works in the Artin-Rees
lemma for two `A`-linear maps `g, g' : L → A` and they agree modulo `I^{c+1}`, then the two
quotient rings `A ⧸ g(L)` and `A ⧸ g'(L)` have isomorphic associated graded algebras: the
degreewise comparison induced by the identity of `A` respects the action of `Gr_I(A)`, the
multiplication and the unit. Its underlying isomorphism of associated graded modules is
`associatedGraded_coker_equiv_of_isArtinReesConstant`, recovered by
`AssociatedGraded.GradedAlgEquiv.toGradedLinearEquiv`. -/
noncomputable def associatedGraded_coker_algEquiv_of_isArtinReesConstant (I : Ideal A)
    {L : Type v} [AddCommGroup L] [Module A L] (g g' : L →ₗ[A] A) (c : ℕ)
    (hg : IsArtinReesConstant I g c) (hg' : IsArtinReesConstant I g' c)
    (hgg' : CongruentModPow I g g' (c + 1)) :
    AssociatedGraded.GradedAlgEquiv I (A ⧸ LinearMap.range g) (A ⧸ LinearMap.range g') where
  toPieceEquiv n := pieceEquiv I _ _ n (presentation_denominator_eq I g g' c n hg hg' hgg')
  map_homogeneousSMul i j a x := pieceEquiv_homogeneousSMul I _ _ i j _ _ a x
  map_homogeneousMul i j x y :=
    pieceEquiv_homogeneousMul_of_isArtinReesConstant I g g' c hg hg' hgg' i j x y
  map_homogeneousOne := pieceEquiv_homogeneousOne I _ _ _

/-- **The comparison of Stacks 07VF is induced by the identity of `A`.** It carries the class of
`z ∈ I^n` modulo `g(L)` to the class of the same `z` modulo `g'(L)`, which is `pieceEquiv_mk`.
This is more than the bundled `AssociatedGraded.GradedAlgEquiv` records, and it is what makes two
such comparisons over different ambient presentations compatible with one another along a ring map
between the presentations. -/
theorem associatedGraded_coker_algEquiv_isInducedByIdentity (I : Ideal A)
    {L : Type v} [AddCommGroup L] [Module A L] (g g' : L →ₗ[A] A) (c : ℕ)
    (hg : IsArtinReesConstant I g c) (hg' : IsArtinReesConstant I g' c)
    (hgg' : CongruentModPow I g g' (c + 1)) :
    (associatedGraded_coker_algEquiv_of_isArtinReesConstant I g g' c hg hg'
      hgg').IsInducedByIdentity :=
  fun n z => pieceEquiv_mk I (LinearMap.range g) (LinearMap.range g') n
    (presentation_denominator_eq I g g' c n hg hg' hgg') z

end

end
