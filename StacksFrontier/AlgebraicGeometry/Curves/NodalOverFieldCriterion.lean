module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalUnramifiedCriterionArbitraryField
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Components

/-!
# At-worst-nodal morphisms of relative dimension one over a field

Let `k` be a field and let `X` be a `k`-scheme locally of finite type.  Then the structure
morphism `X ⟶ Spec(k)` is at-worst-nodal of relative dimension one exactly when the
singularities of `X` are at worst nodal and `X` is equidimensional of dimension one.

This is the absolute form over a field of the relative condition of Tag 0C5A, and it is what
turns the condition on the family of curves of a proper scheme over a field into the condition
on the scheme itself which part (2) of Tag 0DSY states.

## Main results

* `Stacks.Curves.forall_topologicalKrullDimAt_eq_iff_forall_irreducibleComponents` — for a
  scheme locally of finite type over a field, the local dimension is constantly `d` exactly when
  every irreducible component has dimension `d`.
* `Stacks.Curves.isAtWorstNodalOfRelativeDimensionOne_iff_hasAtWorstNodalSingularities` — the
  criterion above.

## Implementation notes

"Equidimensional of dimension one" is read, as the source reads it, as equidimensionality
together with the condition that every irreducible component have dimension one.  Both halves
are stated, although the second implies the first; asserting the dimension componentwise rather
than as `topologicalKrullDim X = 1` is what makes the statement correct for the empty scheme,
whose structure morphism is at-worst-nodal of relative dimension one while its dimension
is `⊥`.

The two conditions of the equivalence are compared conjunct by conjunct.  Being at-worst-nodal
of relative dimension one is syntomicity together with constancy at one of the local dimension
of the fibres and unramifiedness of the relative singular subscheme; over a field the fibre
through a point is the whole source
(`AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_of_field`), so the middle conjunct is
constancy of the local dimension of `X`, which is the componentwise dimension condition by
Tag 0A21 in the form
`AlgebraicGeometry.exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt`.
The remaining two conjuncts are condition (2) of Tag 0C4E, and
`Stacks.Curves.hasAtWorstNodalSingularities_iff_lci_and_unramified_relativeSingularIdeal`
exchanges them for its condition (1).  That tag asks for the dimension of `X` to be one, which
holds once `X` is nonempty; for empty `X` both sides hold, each of the four conditions involved
being a statement about all points of `X` or of a subscheme of it.

## References

* [Stacks Project, Tag 0C5A](https://stacks.math.columbia.edu/tag/0C5A)
* [Stacks Project, Tag 0C4E](https://stacks.math.columbia.edu/tag/0C4E)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 0DSY](https://stacks.math.columbia.edu/tag/0DSY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.Curves

/-- **Constant local dimension, componentwise.**  For a scheme locally of finite type over a
field the local dimension is constantly `d` exactly when every irreducible component has
dimension `d`.

By Tag 0A21 the local dimension at a point is the dimension of some irreducible component
through that point, which gives one direction at once; for the other, the local dimension at
the generic point of a component is realized by a component containing that generic point, and
such a component is the given one. -/
theorem forall_topologicalKrullDimAt_eq_iff_forall_irreducibleComponents (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (d : WithBot ℕ∞) :
    (∀ x : X, topologicalKrullDimAt X x = d) ↔
      ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = d := by
  constructor
  · intro hd W hW
    obtain ⟨Z, hZ, hηZ, hdimZ⟩ :=
      exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k X f
        hW.1.genericPoint
    have hηW : IsGenericPoint hW.1.genericPoint W :=
      hW.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents W hW)
    have hWZ : W ⊆ Z :=
      hηW ▸ closure_minimal (Set.singleton_subset_iff.mpr hηZ)
        (isClosed_of_mem_irreducibleComponents Z hZ)
    have hZW : Z = W := (hWZ.antisymm (hW.2 hZ.1 hWZ)).symm
    rw [← hZW, hdimZ, hd]
  · intro hd x
    obtain ⟨Z, hZ, -, hdimZ⟩ :=
      exists_mem_irreducibleComponents_topologicalKrullDim_eq_topologicalKrullDimAt k X f x
    rw [← hdimZ, hd Z hZ]

/-- **At-worst-nodal of relative dimension one over a field.**

Let `k` be a field and let `X` be a `k`-scheme locally of finite type.  The structure morphism
`X ⟶ Spec(k)` is at-worst-nodal of relative dimension one in the sense of Tag 0C5A exactly when
the singularities of `X` are at worst nodal and `X` is equidimensional of dimension one.

The right-hand side is condition (b) of part (2) of Tag 0DSY, with "equidimensional of dimension
one" read as equidimensionality together with the condition that every irreducible component
have dimension one. -/
theorem isAtWorstNodalOfRelativeDimensionOne_iff_hasAtWorstNodalSingularities (k : Type u)
    [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] :
    IsAtWorstNodalOfRelativeDimensionOne (X ↘ Spec (.of k)) ↔
      (HasAtWorstNodalSingularities k X ∧ Equidimensional X ∧
        ∀ Z ∈ irreducibleComponents X, topologicalKrullDim Z = (1 : WithBot ℕ∞)) := by
  set f := X ↘ Spec (.of k)
  have hfib : ∀ x : X,
      topologicalKrullDimAt (f.fiber (f.base x)) (f.asFiber x) = topologicalKrullDimAt X x :=
    fun x => topologicalKrullDimAt_fiber_eq_of_field f x
  have hB := forall_topologicalKrullDimAt_eq_iff_forall_irreducibleComponents k f
    (1 : WithBot ℕ∞)
  have hdim : Nonempty X → (∀ x : X, topologicalKrullDimAt X x = (1 : WithBot ℕ∞)) →
      topologicalKrullDim X = (1 : WithBot ℕ∞) := fun _ hrd => by
    have hloc : ∀ x : X, localKrullDim X x = (1 : WithBot ℕ∞) := fun x => by
      simpa only [← topologicalKrullDimAt_eq_localKrullDim] using hrd x
    rw [topologicalKrullDim_eq_iSup_localKrullDim]
    simp [hloc]
  constructor
  · rintro ⟨⟨hsyn, hrel⟩, hunr⟩
    have hrd : ∀ x : X, topologicalKrullDimAt X x = (1 : WithBot ℕ∞) := fun x => by
      rw [← hfib x]
      simpa using hrel x
    have hcomp := hB.mp hrd
    have hequi : Equidimensional X := fun Z hZ W hW => (hcomp Z hZ).trans (hcomp W hW).symm
    refine ⟨?_, hequi, hcomp⟩
    rcases isEmpty_or_nonempty X with hX | hX
    · exact fun x _ => hX.elim x
    · exact (hasAtWorstNodalSingularities_iff_lci_and_unramified_relativeSingularIdeal k X
        hequi (hdim hX hrd)).mpr ⟨hsyn, hunr⟩
  · rintro ⟨hnodal, hequi, hcomp⟩
    have hrd := hB.mpr hcomp
    obtain ⟨hsyn, hunr⟩ : Syntomic f ∧ Unramified ((relativeSingularIdeal f).subschemeι ≫ f) := by
      rcases isEmpty_or_nonempty X with hX | hX
      · exact ⟨fun x => hX.elim x, ⟨fun z => hX.elim ((relativeSingularIdeal f).subschemeι.base z)⟩⟩
      · exact (hasAtWorstNodalSingularities_iff_lci_and_unramified_relativeSingularIdeal k X
          hequi (hdim hX hrd)).mp hnodal
    exact ⟨⟨hsyn, fun x => by simpa using (hfib x).trans (hrd x)⟩, hunr⟩

end Stacks.Curves

end
