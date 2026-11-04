module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CanonicalDeltaFunctor
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution

/-!
# The factorisation of [Stacks, Tag 08Q2] as a homotopy, and what any additive functor does to it

Let `A` be an abelian category and let

`K 0 ⟶ K 1 ⟶ ⋯ ⟶ K n`

be a chain of morphisms of cochain complexes in `A` with `H^i(K 0) = 0` for `i > 0` and with
`H^{-j}(f j) = 0` for `j < n`.  [Stacks, Tag 08Q2], which is `main_covariant`, says that the
composite factors in the derived category through the canonical truncation
`τ^{≤ -n}(K n) ⟶ K n`.

This file upgrades that factorisation from the derived category to a **homotopy between
morphisms of complexes**, whenever `K 0` is K-projective, and draws the consequence that matters
in practice: an additive functor `F` applied degreewise to the composite induces the zero map on
`H^i` for every `i > -n`.

That consequence is a form of right `t`-exactness, and it is the form in which right
`t`-exactness gets used: it asks nothing of `F` beyond additivity — no exactness, no total
derived functor, no `t`-structure on either side — because the factorisation it transports is a
homotopy between honest morphisms of complexes, and an additive functor carries homotopies to
homotopies.  Taking `F` to be extension of scalars gives the right `t`-exactness of
`(-) ⊗_A B` on complexes of flats; taking `F` to be a colimit over a category gives the right
`t`-exactness of `Lπ_!` on complexes of projectives.

## Main results

* `Stacks.exists_homotopy_chainComp_comp_ιTruncLE`: the factorisation of [Stacks, Tag 08Q2],
  realised as a homotopy between morphisms of complexes when `K 0` is K-projective.
* `Stacks.homologyMap_map_chainComp_eq_zero`: for every additive functor `F`, the composite
  `K 0 ⟶ K n` induces the zero map on `H^i(F(-))` for `i > -n`.

## Implementation notes

The two plumbing facts about a K-projective source — that every morphism out of it in the
derived category is the class of a morphism of complexes, and that two morphisms of complexes
out of it with the same class are homotopic — are the two halves of [Stacks, Tag 064B] and live
in `StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution` as
`CochainComplex.IsKProjective.Q_map_surjective` and
`CochainComplex.IsKProjective.nonempty_homotopy_of_Q_map_eq`.

## References

* [Stacks Project, Tag 08Q2](https://stacks.math.columbia.edu/tag/08Q2)
* [Stacks Project, Tag 064B](https://stacks.math.columbia.edu/tag/064B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]

/-- **The factorisation of [Stacks, Tag 08Q2] as a homotopy.** Let `K 0 ⟶ ⋯ ⟶ K n` be a chain of
morphisms of cochain complexes with `H^i(K 0) = 0` for `i > 0` and `H^{-j}(f j) = 0` for `j < n`,
and suppose `K 0` is K-projective. Then the composite `K 0 ⟶ K n` is *homotopic* to a morphism
factoring through the canonical truncation `τ^{≤ -n}(K n) ⟶ K n`.

`main_covariant` gives the factorisation in `D(A)`. Because `K 0` is K-projective, the factoring
morphism `D(A)`-morphism is the class of a morphism of complexes `ψ`
(`CochainComplex.IsKProjective.Q_map_surjective`), and two morphisms of complexes out of `K 0`
with the same class in `D(A)` are homotopic
(`CochainComplex.IsKProjective.nonempty_homotopy_of_Q_map_eq`). -/
theorem exists_homotopy_chainComp_comp_ιTruncLE
    (n : ℕ) (K : ℕ → CochainComplex A ℤ) (f : ∀ j, K j ⟶ K (j + 1))
    [(K 0).IsKProjective]
    (h1 : ∀ i : ℤ, 0 < i → IsZero ((K 0).homology i))
    (h2 : ∀ j : ℕ, j < n → HomologicalComplex.homologyMap (f j) (-(j : ℤ)) = 0) :
    ∃ ψ : K 0 ⟶ (K n).truncLE (-(n : ℤ)),
      Nonempty (Homotopy (chainComp K f n) (ψ ≫ (K n).ιTruncLE (-(n : ℤ)))) := by
  obtain ⟨h, hh⟩ := main_covariant n K f h1 h2
  obtain ⟨ψ, rfl⟩ := CochainComplex.IsKProjective.Q_map_surjective (K 0)
    ((K n).truncLE (-(n : ℤ))) h
  exact ⟨ψ, CochainComplex.IsKProjective.nonempty_homotopy_of_Q_map_eq
    (by rw [hh, CategoryTheory.Functor.map_comp])⟩

/-- **An additive functor kills the low homology of the composite of [Stacks, Tag 08Q2].** In the
situation of `Stacks.exists_homotopy_chainComp_comp_ιTruncLE`, let `F : A ⥤ D` be an additive
functor into an abelian category. Then the composite `K 0 ⟶ K n`, pushed through `F` degreewise,
induces the zero map on `H^i` for every `i > -n`.

This is the right `t`-exactness of `F` in the only form the argument of [Stacks, Tag 08RF]
needs, and it asks nothing of `F` but additivity: the composite is homotopic to a morphism
through `τ^{≤ -n}(K n)`, `F` carries that homotopy to a homotopy, homotopic morphisms agree on
homology, and `F` applied degreewise to a complex which is zero above degree `-n` is again zero
above degree `-n`. -/
theorem homologyMap_map_chainComp_eq_zero {D : Type*} [Category D] [Abelian D]
    (F : A ⥤ D) [F.Additive]
    (n : ℕ) (K : ℕ → CochainComplex A ℤ) (f : ∀ j, K j ⟶ K (j + 1))
    [(K 0).IsKProjective]
    (h1 : ∀ i : ℤ, 0 < i → IsZero ((K 0).homology i))
    (h2 : ∀ j : ℕ, j < n → HomologicalComplex.homologyMap (f j) (-(j : ℤ)) = 0)
    (i : ℤ) (hi : -(n : ℤ) < i) :
    HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map (chainComp K f n)) i = 0 := by
  obtain ⟨ψ, ⟨H⟩⟩ := exists_homotopy_chainComp_comp_ιTruncLE n K f h1 h2
  have hX : IsZero (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((K n).truncLE (-(n : ℤ)))).X i) :=
    IsZero.of_iso (isZero_zero D)
      (F.mapIso (((K n).truncLE (-(n : ℤ))).isZero_of_isStrictlyLE (-(n : ℤ)) i hi).isoZero ≪≫
        F.mapZeroObject)
  have hH : IsZero (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((K n).truncLE (-(n : ℤ)))).homology i) :=
    ShortComplex.isZero_homology_of_isZero_X₂ _ hX
  rw [(F.mapHomotopy H).homologyMap_eq i, CategoryTheory.Functor.map_comp,
    HomologicalComplex.homologyMap_comp,
    hH.eq_of_tgt (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) i) 0, Limits.zero_comp]

end Stacks

end
