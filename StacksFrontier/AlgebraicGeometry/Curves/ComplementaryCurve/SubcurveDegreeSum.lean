module

public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.ComponentComplementaryDegree
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.DiscreteCohomology
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionLocalStructure
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.PairwiseGenusIdentity

/-!
# The complementary degrees of the components of a genus-zero subcurve

Let `X` be a proper one-dimensional equidimensional at-worst-nodal curve over a field `k` and let
`C ⊆ X` be a reduced closed subcurve of genus zero, equidimensional of dimension one, with
irreducible components `Λ`. Then

`∑_{Z ∈ Λ} deg (Z ∩ X'_Z) + 2 h⁰(C) = deg (C ∩ X'_C) + 2 ∑_{Z ∈ Λ} h⁰(Z)`,

where `X'_W` denotes the scheme-theoretic closure of the complement of `W` in `X` and `deg`, `h⁰`
are the dimension over `k` of the ring of global functions.

This is the bookkeeping identity behind [Stacks, Tag 0E65]: it says that the average complementary
degree of the components of `C` is determined by the complementary degree of `C` itself and the
`h⁰`'s, with no reference to how the intersection points are distributed among the components.

## Main results

* `Stacks.Curves.isZero_structureSheafCohomology_of_intersection_le`: the positive-degree
  cohomology of a closed subscheme of `X` containing the intersection of a reduced subcurve with
  the closure of its complement vanishes, that intersection being a finite discrete scheme.
* `Stacks.Curves.sum_finrank_sup_complementaryCurveIdeal_eq`: the identity above.

## Implementation notes

The identity is the sum over the components of
`Stacks.Curves.finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_component`, in
which the double sum of pairwise intersection degrees appears, eliminated against
`AlgebraicGeometry.genus_finsetInf_pairwise` at genus zero; the remaining terms are collected by
`Stacks.Curves.finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_finsetInf_eq_sum`.

The vanishing of `H¹` that the genus identity needs on every intersection is supplied uniformly:
each such intersection contains the intersection of a single component with the closure of its
complement, which is discrete by Tag 0E38 (2)(a) and compact by properness, hence affine.

## References

* [Stacks Project, Tag 0E65](https://stacks.math.columbia.edu/tag/0E65)
* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]

/-- **The positive-degree cohomology of a closed subscheme of a nodal curve that contains the
intersection of a reduced subcurve with the closure of its complement vanishes.** That
intersection is discrete by Tag 0E38 (2)(a) and compact by properness, hence affine, and a closed
subscheme of it is too. -/
theorem isZero_structureSheafCohomology_of_intersection_le
    (hX_equidimensional : Equidimensional X) (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme]
    (hY_equidimensional : Equidimensional I.subscheme)
    (hY_dimension : topologicalKrullDim I.subscheme = 1)
    (J : X.IdealSheafData) (hJ : intersectionWithComplementaryCurveIdeal I ≤ J)
    (n : ℕ) (hn : 0 < n) :
    IsZero (structureSheafCohomology (J.subschemeι ≫ (X ↘ Spec (.of k))) n) := by
  have hdisc : DiscreteTopology
      ((intersectionWithComplementaryCurveIdeal I).subscheme : Type u) :=
    (isDiscrete_and_residueField_intersectionWithComplementaryCurve hX_equidimensional
      hX_dimension hX_nodal I hY_equidimensional hY_dimension).1
  have : DiscreteTopology (J.subscheme : Type u) :=
    (Scheme.IdealSheafData.inclusion hJ).isClosedEmbedding.isEmbedding.discreteTopology
  have : IsProper (J.subschemeι ≫ (X ↘ Spec (.of k))) := inferInstance
  have : CompactSpace (J.subscheme : Type u) :=
    QuasiCompact.compactSpace_of_compactSpace (J.subschemeι ≫ (X ↘ Spec (.of k)))
  exact AlgebraicGeometry.isZero_structureSheafCohomology_of_discreteTopology
    (J.subschemeι ≫ (X ↘ Spec (.of k))) n hn


/-- **The sum over the components of a genus-zero subcurve of their complementary degrees.** Let
`X` be a proper one-dimensional equidimensional at-worst-nodal curve over `k`, let `C` be a
reduced closed subcurve of genus zero, equidimensional of dimension one, and let `Λ` be the set of
irreducible components of `X` contained in `C`, each of genus zero. Then

`∑_{Z ∈ Λ} deg (Z ∩ X'_Z) + 2 h⁰(C) = deg (C ∩ X'_C) + 2 ∑_{Z ∈ Λ} h⁰(Z)`.

So the complementary degrees of the components of `C` are pinned only in the aggregate: the
identity is symmetric in how the points of `C ∩ X'_C` are distributed among the components, which
is why [Stacks, Tag 0E65] needs a symmetry input beyond the bookkeeping. -/
theorem sum_finrank_sup_complementaryCurveIdeal_eq
    (hX_equidimensional : Equidimensional X) (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) [IsReduced I.subscheme]
    (hY_equidimensional : Equidimensional I.subscheme)
    (hY_dimension : topologicalKrullDim I.subscheme = 1)
    (Λ : Finset (Set X))
    (hΛ : ∀ Z : Set X, Z ∈ Λ ↔ Z ∈ irreducibleComponents X ∧ Z ⊆ (I.support : Set X))
    (hZred : ∀ Z ∈ Λ, IsReduced (vanishingIdeal (Closeds.closure Z)).subscheme)
    (hZeq : ∀ Z ∈ Λ, Equidimensional (vanishingIdeal (Closeds.closure Z)).subscheme)
    (hZdim : ∀ Z ∈ Λ,
      topologicalKrullDim (vanishingIdeal (Closeds.closure Z)).subscheme = 1)
    (hgenus : genus (I.subschemeι ≫ (X ↘ Spec (.of k))) = 0)
    (hgenusZ : ∀ Z ∈ Λ, genus ((vanishingIdeal (Closeds.closure Z)).subschemeι ≫
      (X ↘ Spec (.of k))) = 0) :
    (∑ Z ∈ Λ, Module.finrank k (structureSheafCohomology
        ((vanishingIdeal (Closeds.closure Z) ⊔
          complementaryCurveIdeal (vanishingIdeal (Closeds.closure Z))).subschemeι ≫
            (X ↘ Spec (.of k))) 0))
      + 2 * Module.finrank k (structureSheafCohomology
          (I.subschemeι ≫ (X ↘ Spec (.of k))) 0)
      = Module.finrank k (structureSheafCohomology
          ((I ⊔ complementaryCurveIdeal I).subschemeι ≫ (X ↘ Spec (.of k))) 0)
        + 2 * ∑ Z ∈ Λ, Module.finrank k (structureSheafCohomology
            ((vanishingIdeal (Closeds.closure Z)).subschemeι ≫ (X ↘ Spec (.of k))) 0) := by
  classical
  have hunion := eq_union_irreducibleComponents hX_equidimensional hX_dimension hX_nodal I
    hY_equidimensional hY_dimension
  rw [Scheme.IdealSheafData.vanishingIdeal_iSup] at hunion
  have hI : I = Λ.inf fun Z : Set X => vanishingIdeal (Closeds.closure Z) := by
    rw [hunion, Finset.inf_eq_iInf, iInf_subtype]
    simp only [hΛ]
  -- the complement of one component inside `C` meets it in the part outside `C` plus the siblings
  have hsplit : ∀ Z ∈ Λ, Module.finrank k (structureSheafCohomology
      ((vanishingIdeal (Closeds.closure Z) ⊔
        complementaryCurveIdeal (vanishingIdeal (Closeds.closure Z))).subschemeι ≫
          (X ↘ Spec (.of k))) 0)
      = Module.finrank k (structureSheafCohomology
          ((vanishingIdeal (Closeds.closure Z) ⊔ complementaryCurveIdeal I).subschemeι ≫
            (X ↘ Spec (.of k))) 0)
        + ∑ W ∈ Λ.erase Z, Module.finrank k (structureSheafCohomology
            ((vanishingIdeal (Closeds.closure Z) ⊔
              vanishingIdeal (Closeds.closure W)).subschemeι ≫ (X ↘ Spec (.of k))) 0) :=
    fun Z hZ => finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_component
      hX_dimension hX_nodal I Λ hΛ hZ
  -- the degrees of the parts outside `C` add up to the degree of `C ∩ X'_C`
  have houter := finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_eq_sum
    hX_equidimensional hX_dimension hX_nodal I hY_equidimensional hY_dimension Λ hΛ
    inferInstance
  -- the genus identity eliminates the double sum of pairwise degrees
  have hthree : ∀ i ∈ Λ, ∀ j ∈ Λ, ∀ l ∈ Λ, i ≠ j → i ≠ l → j ≠ l →
      vanishingIdeal (Closeds.closure i) ⊔ vanishingIdeal (Closeds.closure j) ⊔
        vanishingIdeal (Closeds.closure l) = ⊤ := by
    intro i hi j hj l hl hij hil hjl
    exact sup_sup_vanishingIdeal_eq_top hX_dimension hX_nodal ((hΛ i).mp hi).1
      ((hΛ j).mp hj).1 ((hΛ l).mp hl).1 hij hil hjl
  have hint : ∀ t : Finset (Set X), t ⊆ Λ → ∀ a ∈ Λ, a ∉ t →
      IsZero (structureSheafCohomology
        (((vanishingIdeal (Closeds.closure a) ⊔
          t.inf fun Z : Set X => vanishingIdeal (Closeds.closure Z))).subschemeι ≫
            (X ↘ Spec (.of k))) 1) := by
    intro t htΛ a ha hat
    have : IsReduced (vanishingIdeal (Closeds.closure a)).subscheme := hZred a ha
    refine isZero_structureSheafCohomology_of_intersection_le hX_equidimensional hX_dimension
      hX_nodal (vanishingIdeal (Closeds.closure a)) (hZeq a ha) (hZdim a ha) _ ?_ 1 one_pos
    refine sup_le_sup_left ?_ _
    refine Finset.le_inf fun Z hZ => ?_
    have hZΛ : Z ∈ Λ := htΛ hZ
    have hne : a ≠ Z := fun h => hat (h ▸ hZ)
    refine (complementaryCurveIdeal_vanishingIdeal_eq_inf hX_nodal I Λ hΛ ha).le.trans ?_
    refine inf_le_of_right_le (Finset.inf_le (Finset.mem_erase.mpr ⟨?_, hZΛ⟩))
    exact fun h => hne h.symm
  have hgen := AlgebraicGeometry.genus_finsetInf_pairwise (X ↘ Spec (.of k))
    (fun Z : Set X => vanishingIdeal (Closeds.closure Z)) Λ hthree
    (by rw [← hI]; infer_instance) hint
  rw [← hI] at hgen
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, houter]
  have hsumgenus : ∑ Z ∈ Λ, genus ((vanishingIdeal (Closeds.closure Z)).subschemeι ≫
      (X ↘ Spec (.of k))) = 0 := Finset.sum_eq_zero hgenusZ
  rw [hsumgenus, hgenus] at hgen
  omega

end Stacks.Curves

end
