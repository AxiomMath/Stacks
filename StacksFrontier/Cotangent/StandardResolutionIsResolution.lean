module

public import StacksFrontier.Cotangent.Resolution
public import StacksFrontier.RingTheory.Cotangent.StandardResolution
public import StacksFrontier.AlgebraicTopology.SimplicialSet.TrivialKanFibration.SimplicialAbelianGroup
public import StacksCore.Tactic.StacksAttribute
import Mathlib.Algebra.Category.AlgCat.Basic

/-!
# The standard resolution is a resolution (Stacks 08QI)

An augmentation `P• ⟶ B` of a simplicial commutative `A`-algebra is a *resolution* of `B` over
`A` when every `Pₙ` is a polynomial algebra over `A` and the underlying augmentation of simplicial
sets is a trivial Kan fibration (`CommAlgCat.IsResolution`). The standard resolution of
Stacks 08PM is one.

## Main results

* `CommAlgCat.standardResolution_isResolution`: **Stacks 08QI**, the standard resolution of a
  commutative `A`-algebra `B` is a resolution of `B` over `A`.

## Implementation notes

`CommAlgCat.IsResolution`, which carries **Stacks 08QI**, is imported from
`StacksFrontier.Cotangent.Resolution`. This file once declared it a second time under that same
name, differing only in the encoding of condition (1): the imported structure asks for
`CommAlgCat.IsPolynomialAlgebra A (P.obj n)`, taking the bundled object of `CommAlgCat A`, where
this file asked for `Algebra.IsPolynomialAlgebra A (P.obj n)`, taking its carrier with the
unbundled instances. The two are definitionally equal in both directions — each restated at the
other's argument is identified with it by `rfl` on the whole family — so the duplicate was
retired in favour of the import and `IsResolution` means exactly what it meant before. The
unbundled predicate is still the one `CommAlgCat.standardResolution_obj_isPolynomialAlgebra`
states, and it discharges the imported structure's field directly.

Condition (1) and the degreewise surjectivity of the augmentation are already available from
`StacksFrontier.RingTheory.Cotangent.StandardResolution`
(`CommAlgCat.standardResolution_obj_isPolynomialAlgebra` and
`CommAlgCat.surjective_standardResolution_augmentation`), so only the trivial Kan fibration is
proved here.

That proof instantiates the general adjunction statement **Stacks 08ND**
(`CategoryTheory.Adjunction.exists_homotopyInverse_whiskered_standardResolution`) at the
polynomial-algebra adjunction `CommAlgCat.adj A`, which yields a homotopy inverse of the
augmentation of the standard resolution whiskered with the forgetful functor, in the functor
category. Evaluating at `B` and transporting along the identification of the augmentation point
with `B` gives a homotopy equivalence of the underlying simplicial sets. The forgetful functor is
then factored as `CommAlgCat A ⥤ AlgCat A ⥤ ModuleCat A ⥤ AddCommGrpCat`, so that **Stacks 08P2**
(`AlgebraicTopology.quasiIso_alternatingFaceMapComplex_map_of_homotopyEquivalences_forget`) turns
the homotopy equivalence into a quasi-isomorphism of Moore complexes and **Stacks 08P1**
(`CategoryTheory.SimplicialObject`'s
`trivialKanFibrations_whiskerRight_forget_of_surjective_of_quasiIso`)
turns that, together with surjectivity, into the trivial Kan fibration. No `CommAlgCat`-level
version of Stacks 0G5T/08NA is needed: those two bridges are applied at `AddCommGrpCat`, where
the underlying simplicial set of the factored morphism is the same as that of the original one.

## References

* [Stacks Project, Tag 08QI](https://stacks.math.columbia.edu/tag/08QI)
-/

@[expose] public section

open CategoryTheory
open Opposite Simplicial AlgebraicTopology

universe u v

namespace CommAlgCat

/-! ### The standard resolution is a resolution -/

/-- Whiskering a homotopy equivalence of simplicial objects with a functor gives a homotopy
equivalence. -/
private theorem homotopyEquivalences_whiskerRight
    {C : Type _} [Category C] {D : Type _} [Category D] (F : C ⥤ D)
    {X Y : SimplicialObject C} {f : X ⟶ Y}
    (hf : SimplicialObject.homotopyEquivalences C f) :
    SimplicialObject.homotopyEquivalences D (Functor.whiskerRight f F) := by
  obtain ⟨g, h₁, h₂⟩ := hf
  have hm {W : SimplicialObject C} {x y : W ⟶ W}
      (h : Relation.EqvGen (fun x y : W ⟶ W => Nonempty (SimplicialObject.Homotopy x y)) x y) :
      Relation.EqvGen (fun x y : W ⋙ F ⟶ W ⋙ F => Nonempty (SimplicialObject.Homotopy x y))
        (Functor.whiskerRight x F) (Functor.whiskerRight y F) :=
    Relation.EqvGen.map (Functor.whiskerRight · F) (fun _ _ hxy => hxy.map (·.whiskerRight F)) h
  exact ⟨Functor.whiskerRight g F, by simpa [Functor.whiskerRight_comp] using hm h₁,
    by simpa [Functor.whiskerRight_comp] using hm h₂⟩

/-- Postcomposing a homotopy equivalence of simplicial objects with an isomorphism gives a
homotopy equivalence. -/
private theorem homotopyEquivalences_comp_iso
    {C : Type _} [Category C] {X Y Z : SimplicialObject C} {f : X ⟶ Y}
    (hf : SimplicialObject.homotopyEquivalences C f) (e : Y ≅ Z) :
    SimplicialObject.homotopyEquivalences C (f ≫ e.hom) := by
  obtain ⟨g, hfg, hgf⟩ := hf
  refine ⟨e.inv ≫ g, ?_, ?_⟩
  · simpa [Category.assoc] using hfg
  · have hmap : Relation.EqvGen
        (fun x y : Z ⟶ Z => Nonempty (SimplicialObject.Homotopy x y))
        (e.inv ≫ (g ≫ f) ≫ e.hom) (e.inv ≫ 𝟙 Y ≫ e.hom) :=
      Relation.EqvGen.map (fun k => e.inv ≫ k ≫ e.hom)
        (fun _ _ h => h.map (fun H => by
          simpa [Category.assoc] using (H.precomp e.inv).postcomp e.hom)) hgf
    simpa [Category.assoc] using hmap

/-- A morphism of functors is unchanged by composing it with identities on both ends and with the
right whiskering of an identity. -/
private theorem eq_id_comp_comp_whiskerRight_id
    {C : Type _} [Category C] {D : Type _} [Category D] {E : Type _} [Category E]
    {K : C ⥤ D} {F : C ⥤ E} (H : D ⥤ E) (f : F ⟶ K ⋙ H) :
    f = 𝟙 F ≫ f ≫ Functor.whiskerRight (𝟙 K) H ≫ 𝟙 (K ⋙ H) := by
  simp [Functor.whiskerRight_id']

/-- A morphism of functors is unchanged by composing it with identities on both ends and with the
right whiskering of an identity; the public form of the private lemma above. -/
alias eq_id_comp_comp_whiskerRight_id' := eq_id_comp_comp_whiskerRight_id

/-- **Stacks Project, Tag 08QI.** The standard augmented simplicial algebra of a commutative
`A`-algebra `B` is a resolution of `B` over `A`. -/
@[stacks 08QI "standard_qualifies"]
public theorem standardResolution_isResolution (A : Type u) [CommRing A]
    (B : CommAlgCat.{max u v} A) :
    IsResolution A B (standardResolution A B).left (standardResolution A B).hom := by
  classical
  let R := standardResolution.{u, v} A B
  let adjA := adj.{u, v} A
  let X := standardEndofunctor.{u, v} A
  let C := CommAlgCat.{max u v} A
  let V := forget C
  let U := free.{u, v} A
  let Z : ℕ → (C ⥤ C) := fun n => (adjA.toComonad : C ⥤ C).iterate n
  have hsurj : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective ((R.hom.app n).hom) := by
    intro n
    rw [show n = op ⦋n.unop.len⦌ by rw [SimplexCategory.mk_len]]
    exact surjective_standardResolution_augmentation A B n.unop.len
  let a := Functor.whiskerRight X.hom ((Functor.whiskeringRight C C (Type (max u v))).obj V)
  let b := Functor.whiskerRight X.hom ((Functor.whiskeringLeft (Type (max u v)) C C).obj U)
  have hND := CategoryTheory.Adjunction.exists_homotopyInverse_whiskered_standardResolution
    adjA Z
    (fun _ => rfl)
    (fun n j => Godement.face adjA.toComonad.ε n j)
    (fun n j => Godement.degeneracy adjA.toComonad.δ n j)
    rfl
    (fun n => (Godement.Prep.face_zero adjA.toComonad.ε n).trans (Category.id_comp _).symm)
    (fun n j => (Godement.Prep.face_succ adjA.toComonad.ε n j).trans (by simp))
    (fun n => (Godement.Prep.degeneracy_zero adjA.toComonad.δ n).trans
      (eq_id_comp_comp_whiskerRight_id (K := (adjA.toComonad : C ⥤ C).iterate (n + 1))
        (adjA.toComonad : C ⥤ C) (Functor.whiskerLeft (Z n) adjA.toComonad.δ)))
    (fun n j => (Godement.Prep.degeneracy_succ adjA.toComonad.δ n j).trans (by simp))
    X
    (standardEndofunctor_obj A)
    (standardEndofunctor_right A)
    (by intro n j; simpa [adjA, polynomialComonad] using standardEndofunctor_face A n j)
    (by intro n j; simpa [adjA, polynomialComonad] using standardEndofunctor_degeneracy A n j)
    (by simpa [adjA, polynomialComonad] using standardEndofunctor_augmentation A)
    a
    (fun _ => rfl)
    b
    (fun _ => rfl)
  have hEval : SimplicialObject.homotopyEquivalences (Type (max u v))
      (Functor.whiskerRight a ((evaluation C (Type (max u v))).obj B)) :=
    homotopyEquivalences_whiskerRight ((evaluation C (Type (max u v))).obj B) ⟨hND.1.choose,
      hND.1.choose_spec.1, hND.1.choose_spec.2⟩
  have hB : (X.right.obj B) = B :=
    congrArg (fun F : C ⥤ C => F.obj B) (standardEndofunctor_right A)
  let e := (SimplicialObject.const (Type (max u v))).mapIso (V.mapIso (eqToIso hB))
  have hpoint : Functor.whiskerRight a ((evaluation C (Type (max u v))).obj B) =
      Functor.whiskerRight X.hom (((evaluation C C).obj B) ⋙ V) := by
    ext n x
    rfl
  have hEq : SimplicialObject.homotopyEquivalences (Type (max u v))
      (Functor.whiskerRight R.hom V) := by
    have hmap : Functor.whiskerRight R.hom V =
        Functor.whiskerRight a ((evaluation C (Type (max u v))).obj B) ≫ e.hom := by
      ext n x
      rw [hpoint]
      show (V.map (eqToHom hB)) ((V.map ((X.hom.app n).app B)) x) =
        ((V.map ((X.hom.app n).app B)) ≫ V.map (eqToHom hB)) x
      rfl
    exact hmap.symm ▸ homotopyEquivalences_comp_iso hEval e
  let F := forget₂ C (AlgCat.{max u v} A) ⋙
    forget₂ (AlgCat.{max u v} A) (ModuleCat.{max u v} A) ⋙
    forget₂ (ModuleCat.{max u v} A) AddCommGrpCat.{max u v}
  let f := Functor.whiskerRight R.hom F
  have hforget : Functor.whiskerRight f (forget AddCommGrpCat.{max u v}) =
      Functor.whiskerRight R.hom V := by
    ext n x
    rfl
  have : QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{max u v}).map f) :=
    AlgebraicTopology.quasiIso_alternatingFaceMapComplex_map_of_homotopyEquivalences_forget
      f (hforget.symm ▸ hEq)
  have htriv :=
    SimplicialObject.trivialKanFibrations_whiskerRight_forget_of_surjective_of_quasiIso f
      (fun n y => hsurj n y)
  exact ⟨standardResolution_obj_isPolynomialAlgebra A B, hforget ▸ htriv⟩

end CommAlgCat

end
