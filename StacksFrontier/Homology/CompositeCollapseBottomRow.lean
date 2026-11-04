module

public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import StacksFrontier.Algebra.Homology.DerivedFunctorOfAnAcyclicComplex
public import StacksFrontier.Homology.CompositeCollapse

/-!
# Collapse of the derived functor of a composite onto its bottom row

Let `P : C ⥤ D` and `G : D ⥤ E` be additive functors between abelian categories with enough
injectives in `C` and `D`, with `G` left exact. Suppose that `P` carries injective objects to
`G`-acyclic objects, and let `A : C` be an object all of whose higher right derived functors
`R ᵠ P (A)` are `G`-acyclic. Then

`R ⁿ (P ⋙ G) (A) ≅ G (R ⁿ P (A))`

for every `n`. In the language of the Grothendieck spectral sequence
`E₂^{p,q} = R ᵖ G (R ᵠ P (A)) ⇒ R ᵖ⁺ᵠ (P ⋙ G) (A)`, all terms with `p > 0` vanish and the spectral
sequence collapses onto its row `p = 0`. This is the other degenerate case of the one treated by
`Stacks.RightDerivedComp.objIsoOfAcyclicImage`, where the terms with `q > 0` vanish.

No spectral sequence is constructed. Applying `P` to an injective resolution of `A` gives a
complex `K` whose terms are `G`-acyclic (by hypothesis on `P`) and whose homology objects are the
`R ᵠ P (A)`, also `G`-acyclic. By
`CategoryTheory.Functor.rightAcyclic_cycles_and_preservesLeftHomologyOf_sc`, `G` then preserves
the homology of `K` in every degree, which is the statement.

## Main definitions

* `Stacks.RightDerivedComp.objIsoOfAcyclicHigherImages`: the isomorphism
  `R ⁿ (P ⋙ G) (A) ≅ G (R ⁿ P (A))`.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015D](https://stacks.math.columbia.edu/tag/015D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.RightDerivedComp

section BottomRow

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E] [HasInjectiveResolutions C] [EnoughInjectives D]
  (P : C ⥤ D) (G : D ⥤ E) [P.Additive] [G.Additive] [PreservesFiniteLimits G]

/-- **The derived functor of a composite collapses onto its bottom row.** If `P` carries injective
objects to `G`-acyclic objects and every `R ᵠ P (A)` is `G`-acyclic, then
`R ⁿ (P ⋙ G) (A) ≅ G (R ⁿ P (A))`.

The right-hand side is `G` applied to the homology of `P` applied to an injective resolution of
`A`; the left-hand side is the homology of `G` applied to that complex, and `G` preserves its
homology by `CategoryTheory.Functor.rightAcyclic_cycles_and_preservesLeftHomologyOf_sc`. -/
noncomputable def objIsoOfAcyclicHigherImages (A : C)
    (hinj : ∀ Z : C, Injective Z → acyclic G (P.obj Z))
    (hA : ∀ q, acyclic G ((P.rightDerived q).obj A)) (n : ℕ) :
    ((P ⋙ G).rightDerived n).obj A ≅ G.obj ((P.rightDerived n).obj A) := by
  let _ := HasDerivedCategory.standard D
  let _ := HasDerivedCategory.standard E
  let I := injectiveResolution A
  let K : CochainComplex D ℕ := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  have hX : ∀ i, G.rightAcyclic (K.X i) := fun i ↦
    (rightAcyclic_iff_acyclic G _).2 (hinj _ (I.injective i))
  have hH : ∀ i, G.rightAcyclic (K.homology i) := fun i ↦
    (rightAcyclic_iff_acyclic G _).2
      (Stacks.Cohomology.RightDerivedCoEdge.acyclic_of_iso G (I.isoRightDerivedObj P i) (hA i))
  have := (G.rightAcyclic_cycles_and_preservesLeftHomologyOf_sc K hX hH n).2
  exact I.isoRightDerivedObj (P ⋙ G) n ≪≫ (K.sc n).mapHomologyIso G ≪≫
    G.mapIso (I.isoRightDerivedObj P n).symm

end BottomRow

end Stacks.RightDerivedComp

end
