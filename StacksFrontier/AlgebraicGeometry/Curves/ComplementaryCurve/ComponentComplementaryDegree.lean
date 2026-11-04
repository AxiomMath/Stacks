module

public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionDegreeComponents
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.TripleIntersection

/-!
# The complementary degree of one component of a subcurve

Let `X` be a one-dimensional at-worst-nodal curve over a field `k`, let `C ⊆ X` be a closed
subscheme and let `Λ` be the finite set of irreducible components of `X` contained in `C`. For a
member `Z₀` of `Λ`, the scheme-theoretic closure of the complement of `Z₀` in `X` is the union of
the closure of the complement of `C` with the remaining members of `Λ`, and the three-way
intersections vanish because a node has only two branches. Hence the degree of the intersection of
`Z₀` with the closure of its own complement splits as

`deg (Z₀ ∩ X'_{Z₀}) = deg (Z₀ ∩ X'_C) + ∑_{Z ∈ Λ, Z ≠ Z₀} deg (Z₀ ∩ Z)`.

## Main results

* `Stacks.Curves.complementaryCurveIdeal_vanishingIdeal_eq_inf`: the ideal-sheaf identity
  `X'_{Z₀} = X'_C ∪ ⋃_{Z ≠ Z₀} Z`.
* `Stacks.Curves.finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_component`: the
  degree identity above.

## Implementation notes

Both sides of the ideal identity are vanishing ideals of closed sets, so it is proved by
identifying those closed sets, which is the set identity
`{Z component : Z ≠ Z₀} = {Z component : Z ∉ Λ} ∪ {Z ∈ Λ : Z ≠ Z₀}` together with
`Stacks.Curves.complementaryCurveIdeal_eq_union_irreducibleComponents` on each side.

The degree identity then needs the three-way intersections to be empty, in two forms: a point on
`Z₀`, on another member of `Λ` and on `X'_C` would have three branches
(`Stacks.Curves.sup_sup_complementaryCurveIdeal_eq_top`), and a point on `Z₀` and on two other
members of `Λ` would too — the latter is the hypothesis `hthree` here, discharged by
`Stacks.Curves.sup_sup_vanishingIdeal_eq_top`.

## References

* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
* [Stacks Project, Tag 0C47](https://stacks.math.columbia.edu/tag/0C47)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))]

/-- A finite infimum of the reduced structures on closed sets is the reduced structure on their
union. -/
theorem finsetInf_vanishingIdeal_closure (s : Finset (Set X)) :
    (s.inf fun Z => vanishingIdeal (Closeds.closure Z)) =
      vanishingIdeal (⨆ Z ∈ s, Closeds.closure Z) := by
  simp only [vanishingIdeal_iSup]
  rw [← Finset.inf_eq_iInf]

/-- Two irreducible components one of which is contained in the other are equal. -/
theorem eq_of_mem_irreducibleComponents_subset {Z W : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hW : W ∈ irreducibleComponents X) (h : Z ⊆ W) :
    Z = W :=
  le_antisymm h (hZ.2 hW.1 h)

/-- **The scheme-theoretic closure of the complement of one component of a subcurve.** For `Λ` the
set of irreducible components of `X` inside a closed subscheme `C`, and `Z₀ ∈ Λ`, the closure of
the complement of `Z₀` is the union of the closure of the complement of `C` with the other members
of `Λ`. -/
theorem complementaryCurveIdeal_vanishingIdeal_eq_inf
    (hX_nodal : HasAtWorstNodalSingularities k X) (I : X.IdealSheafData)
    (Λ : Finset (Set X))
    (hΛ : ∀ Z : Set X, Z ∈ Λ ↔ Z ∈ irreducibleComponents X ∧ Z ⊆ (I.support : Set X))
    {Z₀ : Set X} (hZ₀ : Z₀ ∈ Λ) :
    complementaryCurveIdeal (vanishingIdeal (Closeds.closure Z₀)) =
      complementaryCurveIdeal I ⊓
        (Λ.erase Z₀).inf fun Z => vanishingIdeal (Closeds.closure Z) := by
  classical
  have hZ₀comp : Z₀ ∈ irreducibleComponents X := ((hΛ Z₀).mp hZ₀).1
  have hZ₀closed : IsClosed Z₀ := isClosed_of_mem_irreducibleComponents Z₀ hZ₀comp
  have hsupp : ((vanishingIdeal (Closeds.closure Z₀)).support : Set X) = Z₀ := by
    rw [coe_support_vanishingIdeal, Closeds.coe_closure, hZ₀closed.closure_eq]
  have hnsub : ∀ C ∈ irreducibleComponents X, C ≠ Z₀ →
      ¬ C ⊆ ((vanishingIdeal (Closeds.closure Z₀)).support : Set X) := fun C hC hne h =>
    hne (eq_of_mem_irreducibleComponents_subset hC hZ₀comp (hsupp ▸ h))
  have hcomp (J : X.IdealSheafData) : complementaryCurveIdeal J =
      vanishingIdeal (⨆ C : {C : Set X // C ∈ irreducibleComponents X ∧
        ¬ C ⊆ (J.support : Set X)}, Closeds.closure C.1) :=
    complementaryCurveIdeal_eq_union_irreducibleComponents hX_nodal J
  rw [hcomp, hcomp, finsetInf_vanishingIdeal_closure, ← vanishingIdeal_sup]
  congr 1
  refine le_antisymm (iSup_le fun C => ?_)
    (sup_le (iSup_le fun C => ?_) (iSup_le fun Z => iSup_le fun hZ => ?_))
  · obtain ⟨hC, hCsub⟩ := C.2
    by_cases hmem : C.1 ∈ Λ
    · refine le_sup_of_le_right (le_iSup_of_le C.1 (le_iSup_of_le ?_ le_rfl))
      refine Finset.mem_erase.mpr ⟨?_, hmem⟩
      intro hCZ
      exact hCsub (by rw [hCZ]; exact hsupp.ge)
    · exact le_sup_of_le_left
        (le_iSup_of_le ⟨C.1, hC, fun h => hmem ((hΛ C.1).mpr ⟨hC, h⟩)⟩ le_rfl)
  · obtain ⟨hC, hCsub⟩ := C.2
    exact le_iSup_of_le ⟨C.1, hC, hnsub _ hC fun hCZ => hCsub (hCZ ▸ ((hΛ Z₀).mp hZ₀).2)⟩ le_rfl
  · obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hZ
    have hZcomp : Z ∈ irreducibleComponents X := ((hΛ Z).mp hmem).1
    exact le_iSup_of_le ⟨Z, hZcomp, hnsub Z hZcomp hne⟩ le_rfl


omit [LocallyOfFiniteType (X ↘ Spec (.of k))] in
/-- **The degree of the intersection of one component of a subcurve with the closure of its own
complement splits into the part coming from outside the subcurve and the parts coming from the
sibling components.**  For `Λ` the set of irreducible components of `X` inside a closed subscheme
`C` cut out by `I`, and `Z₀ ∈ Λ`,

`deg (Z₀ ∩ X'_{Z₀}) = deg (Z₀ ∩ X'_C) + ∑_{Z ∈ Λ, Z ≠ Z₀} deg (Z₀ ∩ Z)`.

The three-way intersections vanish because a node has only two branches: a point on `Z₀`, on a
sibling and on `X'_C` would lie on three components, and so would a point on `Z₀` and on two
siblings. -/
theorem finrank_structureSheafCohomology_zero_sup_complementaryCurveIdeal_component
    [IsProper (X ↘ Spec (.of k))]
    (hX_dimension : topologicalKrullDim X = 1)
    (hX_nodal : HasAtWorstNodalSingularities k X)
    (I : X.IdealSheafData) (Λ : Finset (Set X))
    (hΛ : ∀ Z : Set X, Z ∈ Λ ↔ Z ∈ irreducibleComponents X ∧ Z ⊆ (I.support : Set X))
    {Z₀ : Set X} (hZ₀ : Z₀ ∈ Λ) :
    Module.finrank k (structureSheafCohomology
        ((vanishingIdeal (Closeds.closure Z₀) ⊔
          complementaryCurveIdeal (vanishingIdeal (Closeds.closure Z₀))).subschemeι ≫
            (X ↘ Spec (.of k))) 0)
      = Module.finrank k (structureSheafCohomology
          ((vanishingIdeal (Closeds.closure Z₀) ⊔ complementaryCurveIdeal I).subschemeι ≫
            (X ↘ Spec (.of k))) 0)
        + ∑ Z ∈ Λ.erase Z₀, Module.finrank k (structureSheafCohomology
            ((vanishingIdeal (Closeds.closure Z₀) ⊔
              vanishingIdeal (Closeds.closure Z)).subschemeι ≫ (X ↘ Spec (.of k))) 0) := by
  classical
  have hZ₀comp : Z₀ ∈ irreducibleComponents X := ((hΛ Z₀).mp hZ₀).1
  have hZ₀sub : Z₀ ⊆ (I.support : Set X) := ((hΛ Z₀).mp hZ₀).2
  have hsib : ∀ Z ∈ Λ.erase Z₀, vanishingIdeal (Closeds.closure Z) ⊔
      (complementaryCurveIdeal I ⊔ vanishingIdeal (Closeds.closure Z₀)) = ⊤ := by
    intro Z hZ
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hZ
    have h := sup_sup_complementaryCurveIdeal_eq_top hX_dimension hX_nodal I
      ((hΛ Z).mp hmem).1 hZ₀comp hne ((hΛ Z).mp hmem).2 hZ₀sub
    rw [← h, sup_assoc, sup_comm (complementaryCurveIdeal I)]
  have hthree : ∀ Z ∈ Λ.erase Z₀, ∀ W ∈ Λ.erase Z₀, Z ≠ W →
      vanishingIdeal (Closeds.closure Z) ⊔ vanishingIdeal (Closeds.closure W) ⊔
        vanishingIdeal (Closeds.closure Z₀) = ⊤ := by
    intro Z hZ W hW hZW
    obtain ⟨hneZ, hmemZ⟩ := Finset.mem_erase.mp hZ
    obtain ⟨hneW, hmemW⟩ := Finset.mem_erase.mp hW
    exact sup_sup_vanishingIdeal_eq_top hX_dimension hX_nodal ((hΛ Z).mp hmemZ).1
      ((hΛ W).mp hmemW).1 hZ₀comp hZW hneZ hneW
  have htop : complementaryCurveIdeal I ⊔
      ((Λ.erase Z₀).inf fun Z => vanishingIdeal (Closeds.closure Z)) ⊔
        vanishingIdeal (Closeds.closure Z₀) = ⊤ := by
    have h := Scheme.IdealSheafData.finsetInf_sup_eq_top
      (fun Z : Set X => vanishingIdeal (Closeds.closure Z))
      (complementaryCurveIdeal I ⊔ vanishingIdeal (Closeds.closure Z₀)) (Λ.erase Z₀) hsib
    rw [← h, sup_comm (complementaryCurveIdeal I), ← sup_assoc]
  have hid : vanishingIdeal (Closeds.closure Z₀) ⊔
      complementaryCurveIdeal (vanishingIdeal (Closeds.closure Z₀)) =
      (vanishingIdeal (Closeds.closure Z₀) ⊔ complementaryCurveIdeal I) ⊓
        (vanishingIdeal (Closeds.closure Z₀) ⊔
          ((Λ.erase Z₀).inf fun Z => vanishingIdeal (Closeds.closure Z))) := by
    rw [complementaryCurveIdeal_vanishingIdeal_eq_inf hX_nodal I Λ hΛ hZ₀,
      sup_comm (vanishingIdeal (Closeds.closure Z₀)),
      Scheme.IdealSheafData.sup_inf_right_of_sup_sup_eq_top htop,
      sup_comm (complementaryCurveIdeal I),
      sup_comm ((Λ.erase Z₀).inf fun Z => vanishingIdeal (Closeds.closure Z))]
  have hcom : (vanishingIdeal (Closeds.closure Z₀) ⊔ complementaryCurveIdeal I) ⊔
      (vanishingIdeal (Closeds.closure Z₀) ⊔
        ((Λ.erase Z₀).inf fun Z => vanishingIdeal (Closeds.closure Z))) = ⊤ := by
    rw [sup_sup_sup_comm, sup_idem, ← htop, sup_comm (complementaryCurveIdeal I), sup_assoc,
      sup_comm (vanishingIdeal (Closeds.closure Z₀))]
    exact sup_assoc _ _ _
  rw [hid, finrank_structureSheafCohomology_zero_inf_eq_add_of_sup_eq_top k
    (X ↘ Spec (.of k)) _ _ hcom inferInstance]
  congr 1
  have hpair : ∀ Z ∈ Λ.erase Z₀, ∀ W ∈ Λ.erase Z₀, Z ≠ W →
      (vanishingIdeal (Closeds.closure Z) ⊔ vanishingIdeal (Closeds.closure Z₀)) ⊔
        (vanishingIdeal (Closeds.closure W) ⊔ vanishingIdeal (Closeds.closure Z₀)) = ⊤ := by
    intro Z hZ W hW hZW
    rw [sup_sup_sup_comm, sup_idem]
    exact hthree Z hZ W hW hZW
  rw [sup_comm (vanishingIdeal (Closeds.closure Z₀)),
    Scheme.IdealSheafData.finsetInf_sup_of_pairwise
      (fun Z : Set X => vanishingIdeal (Closeds.closure Z))
      (vanishingIdeal (Closeds.closure Z₀)) (Λ.erase Z₀) hthree,
    finrank_structureSheafCohomology_zero_finsetInf_eq_sum k (X ↘ Spec (.of k))
      (fun Z : Set X => vanishingIdeal (Closeds.closure Z) ⊔
        vanishingIdeal (Closeds.closure Z₀)) (Λ.erase Z₀) hpair
      inferInstance]
  exact Finset.sum_congr rfl fun Z _ => by rw [sup_comm]

end Stacks.Curves

end
