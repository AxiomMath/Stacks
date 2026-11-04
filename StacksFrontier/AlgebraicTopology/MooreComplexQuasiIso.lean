module

public import StacksFrontier.AlgebraicTopology.MooreComplex
public import StacksFrontier.LinearAlgebra.ExteriorPower.DerivedSquare

/-!
# The normalized complex is quasi-isomorphic to the Moore complex

Let `A` be an abelian category and let `V` be a simplicial object of `A`. The canonical inclusion
`N(V) ⟶ s(V)` of the normalized complex `N = normalizedMooreComplex A` into the Moore complex
`s = alternatingFaceMapComplex A` is a quasi-isomorphism: it is even a homotopy equivalence.
Equivalently, the complement `D(V)` in the functorial splitting `s(V) = N(V) ⊕ D(V)` is acyclic.

## Main results

* `AlgebraicTopology.acyclic_degenerateComplex`: for every functorial splitting `N ⊞ D ≅ s` whose
  restriction to the first summand is the canonical inclusion, each complex `D(V)` is acyclic.
* `AlgebraicTopology.quasiIso_inclusionOfMooreComplexMap_and_acyclic_degenerateComplex`: the
  inclusion `N(V) ⟶ s(V)` is a quasi-isomorphism, and every such `D(V)` is acyclic.

## References

* [Stacks, Tag 019A](https://stacks.math.columbia.edu/tag/019A)
* [Stacks, Tag 019C](https://stacks.math.columbia.edu/tag/019C)
-/

section

open CategoryTheory Limits

universe v u

namespace AlgebraicTopology

/-- A complex `L` which is a retract of `M`, through maps `j : L ⟶ M` and `p : M ⟶ L`, is acyclic
as soon as `p` kills the image of a quasi-isomorphism `i : K ⟶ M`. -/
private lemma acyclic_of_quasiIso_of_comp_eq_zero {C : Type*} [Category* C] [HasZeroMorphisms C]
    [CategoryWithHomology C] {ι : Type*} {c : ComplexShape ι} {K L M : HomologicalComplex C c}
    (i : K ⟶ M) [QuasiIso i] (j : L ⟶ M) (p : M ⟶ L) (hjp : j ≫ p = 𝟙 L) (hip : i ≫ p = 0) :
    L.Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  have hp : HomologicalComplex.homologyMap p n = 0 := by
    rw [← cancel_epi (HomologicalComplex.homologyMap i n), ← HomologicalComplex.homologyMap_comp,
      hip, HomologicalComplex.homologyMap_zero, comp_zero]
  rw [IsZero.iff_id_eq_zero, ← HomologicalComplex.homologyMap_id, ← hjp,
    HomologicalComplex.homologyMap_comp, hp, comp_zero]

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Let `D` be a functor from simplicial objects of an abelian category `A` to chain complexes and
`e : N ⊞ D ≅ s` a natural isomorphism which on the first summand is the canonical inclusion
`N ⟶ s`. Then for every simplicial object `V` of `A` the complex `D(V)` is acyclic. -/
public theorem acyclic_degenerateComplex (D : SimplicialObject A ⥤ ChainComplex A ℕ)
    (e : normalizedMooreComplex A ⊞ D ≅ alternatingFaceMapComplex A)
    (he : biprod.inl ≫ e.hom = inclusionOfMooreComplex A) (V : SimplicialObject A) :
    (D.obj V).Acyclic := by
  refine acyclic_of_quasiIso_of_comp_eq_zero (inclusionOfMooreComplexMap V)
    ((biprod.inr ≫ e.hom).app V) ((e.inv ≫ biprod.snd).app V) ?_ ?_
  · exact congrArg (fun t => t.app V)
      (show (biprod.inr ≫ e.hom) ≫ e.inv ≫ biprod.snd = 𝟙 D by simp)
  · exact congrArg (fun t => t.app V)
      (show inclusionOfMooreComplex A ≫ e.inv ≫ biprod.snd = 0 by simp [← he])

/-- Let `A` be an abelian category and let `V` be a simplicial object of `A`. The canonical
morphism of chain complexes `N(V) ⟶ s(V)` is a quasi-isomorphism, and for every functorial
splitting `e : N ⊞ D ≅ s` which on the first summand is the canonical inclusion, the complex `D(V)`
is acyclic. -/
@[stacks 019C]
public theorem quasiIso_inclusionOfMooreComplexMap_and_acyclic_degenerateComplex
    (V : SimplicialObject A) :
    QuasiIso (inclusionOfMooreComplexMap V) ∧
      ∀ (D : SimplicialObject A ⥤ ChainComplex A ℕ)
        (e : normalizedMooreComplex A ⊞ D ≅ alternatingFaceMapComplex A),
        biprod.inl ≫ e.hom = inclusionOfMooreComplex A → (D.obj V).Acyclic :=
  ⟨inferInstance, fun D e he => acyclic_degenerateComplex D e he V⟩

end AlgebraicTopology

end
