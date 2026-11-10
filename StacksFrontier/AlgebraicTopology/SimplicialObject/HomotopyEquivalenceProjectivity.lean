module

public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.Projective.Basic
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import StacksFrontier.AlgebraicTopology.SimplicialObject.ChainHomotopy

/-!
# A simplicial object homotopy equivalent to a constant one is projective

Let `A` be an abelian category and let `X` be a simplicial object of `A` all of whose terms are
projective. If `X` is homotopy equivalent, in the sense of [Stacks, Tag 019N], to the constant
simplicial object on a projective object `P`, then `X` is a **projective object of the functor
category** `SimplicialObject A`.

This is a genuine theorem about the simplicial structure, not an instance lookup: the constant
simplicial object on a projective object need not itself be projective — through the adjunction
`const ⊣ lim` its projectivity amounts to the exactness of the limit over `SimplexCategory`,
which is a kernel of two cofaces and is only left exact. What makes the statement true is
Dold–Kan: the alternating face map complex of `X` is a homotopy retract of the complex
`P` in degree zero, which is projective in `ChainComplex A ℕ`, and a homotopy retract of a
projective complex whose own terms are projective is projective; the normalized Moore complex is
a retract of the alternating face map complex, hence projective as well, and `X` is the image of
the Moore complex under the Dold–Kan equivalence.

## Main results

* `CategoryTheory.SimplicialObject.homotopyEquivalences_whiskerRight` and
  `CategoryTheory.SimplicialObject.homotopyEquivalences_comp_iso`: homotopy equivalences of
  simplicial objects are stable under whiskering with a functor and under composition with an
  isomorphism.
* `CategoryTheory.Limits.projective_sigma`: a coproduct of projective objects is projective.
* `CategoryTheory.Limits.enoughProjectives_of_isSeparating_projective`: a separating family of
  projective objects makes a category have enough projectives.
* `HomologicalComplex.projective_of_homotopyRetract` and
  `HomologicalComplex.projective_of_homotopyEquiv`: a homotopy retract of a projective complex
  is projective as soon as its own terms are.
* `ChainComplex.projective_single₀`: a projective object placed in degree zero is a projective
  chain complex.
* `CategoryTheory.SimplicialObject.projective_of_homotopyEquivalence_const`: the statement
  above.

## References

* [Stacks Project, Tag 019N](https://stacks.math.columbia.edu/tag/019N)
* [Stacks Project, Tag 019S](https://stacks.math.columbia.edu/tag/019S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial

universe v u v' u'

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- **Whiskering a homotopy equivalence of simplicial objects with a functor gives a homotopy
equivalence.** A functor carries a simplicial homotopy to a simplicial homotopy
(`CategoryTheory.SimplicialObject.Homotopy.whiskerRight`), hence the generated equivalence
relation to the generated equivalence relation. -/
theorem homotopyEquivalences_whiskerRight (F : C ⥤ D) {X Y : SimplicialObject C} {a : X ⟶ Y}
    (ha : homotopyEquivalences C a) :
    homotopyEquivalences D (Functor.whiskerRight a F) := by
  obtain ⟨b, hab, hba⟩ := ha
  refine ⟨Functor.whiskerRight b F, ?_, ?_⟩
  · simpa only [Functor.whiskerRight_comp, Functor.whiskerRight_id'] using
      Relation.EqvGen.map (fun k ↦ Functor.whiskerRight k F)
        (fun _ _ h ↦ h.map fun H ↦ H.whiskerRight F) hab
  · simpa only [Functor.whiskerRight_comp, Functor.whiskerRight_id'] using
      Relation.EqvGen.map (fun k ↦ Functor.whiskerRight k F)
        (fun _ _ h ↦ h.map fun H ↦ H.whiskerRight F) hba

/-- **Composing a homotopy equivalence of simplicial objects with an isomorphism gives a homotopy
equivalence.** -/
theorem homotopyEquivalences_comp_iso {X Y Z : SimplicialObject C} {a : X ⟶ Y}
    (ha : homotopyEquivalences C a) (e : Y ≅ Z) :
    homotopyEquivalences C (a ≫ e.hom) := by
  obtain ⟨b, hab, hba⟩ := ha
  refine ⟨e.inv ≫ b, ?_, ?_⟩
  · simpa using hab
  · simpa using
      Relation.EqvGen.map (fun k ↦ e.inv ≫ k ≫ e.hom)
        (fun _ _ h ↦ h.map fun H ↦ by
          simpa using (H.precomp e.inv).postcomp e.hom) hba

end CategoryTheory.SimplicialObject

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

/-- **A coproduct of projective objects is projective.** A lifting problem for the coproduct is
solved factor by factor. -/
lemma projective_sigma {ι : Type*} {X : ι → C} [HasCoproduct X] [∀ i, Projective (X i)] :
    Projective (∐ X) where
  factors f e _ := ⟨Sigma.desc fun i ↦ Projective.factorThru (Sigma.ι X i ≫ f) e, by cat_disch⟩

/-- **A separating family of projective objects makes a category have enough projectives.** For
an object `Z` the coproduct of one copy of `S i` for every morphism `S i ⟶ Z` is projective, and
the morphism it defines to `Z` is an epimorphism precisely because the family is separating: two
morphisms out of `Z` agreeing after it agree after every `S i ⟶ Z`. -/
lemma enoughProjectives_of_isSeparating_projective {ι : Type v} (S : ι → C)
    [∀ i, Projective (S i)] [HasCoproducts.{v} C]
    (hS : ObjectProperty.IsSeparating (ObjectProperty.ofObj S)) : EnoughProjectives C := by
  refine ⟨fun Z ↦ ?_⟩
  have : Projective (∐ fun t : Σ i, (S i ⟶ Z) ↦ S t.1) := projective_sigma
  have hepi : Epi (Sigma.desc fun t : Σ i, (S i ⟶ Z) ↦ t.2) :=
    ⟨fun a b hab ↦ hS a b fun G hG h ↦ by
      obtain ⟨i⟩ := hG
      simpa using Sigma.ι (fun t : Σ i, (S i ⟶ Z) ↦ S t.1) ⟨i, h⟩ ≫= hab⟩
  exact ⟨{ p := ∐ fun t : Σ i, (S i ⟶ Z) ↦ S t.1
           f := Sigma.desc fun t ↦ t.2
           epi := hepi }⟩

end CategoryTheory.Limits

namespace HomologicalComplex

variable {A : Type u} [Category.{v} A] [Abelian A] {ι : Type*} {c : ComplexShape ι}

attribute [local instance] CategoryTheory.Abelian.hasFiniteColimits

/-- **A homotopy retract of a projective complex is projective as soon as its own terms are.**
If `𝟙 K` is homotopic to `i ≫ p` with `P` projective and every `K.X n` projective, then a lifting
problem for `K` is solved by lifting it through `P` and correcting the difference by the null
homotopic map built from the degreewise lifts of the homotopy. -/
lemma projective_of_homotopyRetract (K P : HomologicalComplex A c)
    [∀ n, Projective (K.X n)] [Projective P] (i : K ⟶ P) (p : P ⟶ K)
    (h : Homotopy (𝟙 K) (i ≫ p)) : Projective K := by
  refine ⟨fun {E Y} f e _ ↦ ⟨i ≫ Projective.factorThru (p ≫ f) e +
    Homotopy.nullHomotopicMap (fun m n ↦ Projective.factorThru (h.hom m n ≫ f.f n) (e.f n)), ?_⟩⟩
  rw [Preadditive.add_comp, Category.assoc, Projective.factorThru_comp,
    Homotopy.nullHomotopicMap_comp]
  simp_rw [Projective.factorThru_comp]
  rw [← Homotopy.nullHomotopicMap_comp, ← h.sub_eq_nullHomotopicMap]
  simp [Preadditive.sub_comp]

/-- **A complex with projective terms homotopy equivalent to a projective complex is
projective.** -/
lemma projective_of_homotopyEquiv (K P : HomologicalComplex A c)
    [∀ n, Projective (K.X n)] [Projective P] (e : HomotopyEquiv K P) : Projective K :=
  projective_of_homotopyRetract K P e.hom e.inv e.homotopyHomInvId.symm

end HomologicalComplex

namespace ChainComplex

variable {A : Type u} [Category.{v} A] [Abelian A]

attribute [local instance] CategoryTheory.Abelian.hasFiniteColimits

/-- **A projective object placed in degree zero is a projective chain complex.** A morphism out
of `(single₀ A).obj P` is its component in degree zero, by
`ChainComplex.fromSingle₀Equiv`, so the lifting problem is the lifting problem for `P` against
the degree-zero component of the epimorphism. -/
lemma projective_single₀ (P : A) [Projective P] : Projective ((single₀ A).obj P) := by
  constructor
  intro E Y f e _
  -- the rewrite below leaves the lift typed at `((single₀ A).obj P).X 0`, where instance search
  -- does not see `P`; the instance is supplied by name
  have : Projective (((single₀ A).obj P).X 0) := inferInstanceAs (Projective P)
  refine ⟨(fromSingle₀Equiv E P).symm
    (Projective.factorThru ((fromSingle₀Equiv Y P) f) (e.f 0)), ?_⟩
  apply (fromSingle₀Equiv Y P).injective
  change ((fromSingle₀Equiv E P).symm _).f 0 ≫ e.f 0 = f.f 0
  rw [fromSingle₀Equiv_symm_apply_f_zero]
  exact Projective.factorThru_comp _ _

end ChainComplex

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]

attribute [local instance] CategoryTheory.Abelian.hasFiniteColimits

/-- **A simplicial object with projective terms homotopy equivalent to a constant one is
projective.** Let `X` be a simplicial object of an abelian category all of whose terms are
projective and let `a : X ⟶ const P` be a homotopy equivalence with `P` projective. Then `X` is
a projective object of `SimplicialObject A`.

The alternating face map complex of `a` is a homotopy equivalence of chain complexes
(`AlgebraicTopology.homotopyEquivalences_alternatingFaceMapComplex_map`) and the alternating
face map complex of a constant augmented simplicial object is homotopy equivalent to its point
in degree zero, by the extra degeneracy of
`CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy.const`; so
`HomologicalComplex.projective_of_homotopyEquiv` makes `(alternatingFaceMapComplex A).obj X`
projective. The normalized Moore complex is a retract of it
(`AlgebraicTopology.DoldKan.splitMonoInclusionOfMooreComplexMap`), hence projective, and the
Dold–Kan equivalence carries it back to `X`. -/
lemma projective_of_homotopyEquivalence_const (X : SimplicialObject A)
    [∀ n, Projective (X.obj n)] (P : A) [Projective P] (a : X ⟶ (const A).obj P)
    (ha : homotopyEquivalences A a) : Projective X := by
  have hterm (n : ℕ) : Projective (((alternatingFaceMapComplex A).obj X).X n) :=
    inferInstanceAs (Projective (X.obj (op ⦋n⦌)))
  obtain ⟨e, -⟩ := AlgebraicTopology.homotopyEquivalences_alternatingFaceMapComplex_map ha
  have := ChainComplex.projective_single₀ P
  have hK : Projective ((alternatingFaceMapComplex A).obj X) :=
    HomologicalComplex.projective_of_homotopyEquiv _ ((ChainComplex.single₀ A).obj P)
      (e.trans (Augmented.ExtraDegeneracy.const P).homotopyEquiv)
  have hR : Projective ((normalizedMooreComplex A).obj X) :=
    (Retract.mk (inclusionOfMooreComplexMap X)
      (AlgebraicTopology.DoldKan.splitMonoInclusionOfMooreComplexMap X).retraction
      (AlgebraicTopology.DoldKan.splitMonoInclusionOfMooreComplexMap X).id).projective
  have hF : Projective ((Abelian.DoldKan.equivalence (A := A)).functor.obj X) := hR
  exact Projective.of_iso ((Abelian.DoldKan.equivalence (A := A)).unitIso.app X).symm
    ((Abelian.DoldKan.equivalence (A := A)).symm.functor.projective_obj_of_projective hF)

end CategoryTheory.SimplicialObject

end
