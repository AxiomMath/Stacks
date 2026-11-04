module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcMorphismDescent

/-!
# Recognising a coproduct of algebraic spaces from a disjoint étale covering

Let `S` be a scheme contained in a big fppf site `B` and let `f i : X i ⟶ Y` be a family of
monomorphisms of algebraic spaces over `S` which is an étale covering of `Y` and whose images
in `|Y|` are pairwise disjoint. Then `Y` is the coproduct of the `X i`.

This is the recognition statement that turns a decomposition of an algebraic space into
pairwise disjoint open or locally closed pieces into the universal property of a coproduct,
and so lets a morphism out of `Y` be assembled from morphisms out of the pieces.

## Main results

* `AlgebraicGeometry.Space.isColimit_cofan_of_disjoint_etaleCovering`: a disjoint étale
  covering by monomorphisms exhibits the target as the coproduct of the sources.

## Implementation notes

The descent input is **Stacks 04P2**,
`AlgebraicGeometry.Space.existsUnique_desc_of_fpqcCovering`: an étale covering is an fpqc
covering by `AlgebraicGeometry.Space.isFpqcCovering_of_isEtaleCovering`, so a family of
morphisms out of the pieces which agrees on the fibre products descends uniquely. The two
compatibility cases are formal: on the diagonal the two projections of the fibre product of a
monomorphism with itself agree, and off the diagonal the fibre product `X i ×_Y X j` has no
points because the images of `f i` and `f j` are disjoint, so any two morphisms out of it are
equal; that last fact is proved inline, as the private helper of the same content in
`StacksFrontier/AlgebraicGeometry/Spaces/ElementaryDistinguishedSquareGluing.lean` is not visible
here.

The index type is arbitrary: nothing here needs the family to be finite or small.

## References

* [Stacks Project, Tag 04P2](https://stacks.math.columbia.edu/tag/04P2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A family of monomorphisms of algebraic spaces which is an étale covering with pairwise
disjoint images exhibits the target as their coproduct.** -/
def isColimit_cofan_of_disjoint_etaleCovering
    {I : Type v} {X : I → AlgebraicSpaces B S hS} {Y : AlgebraicSpaces B S hS}
    (f : ∀ i, X i ⟶ Y) (hm : ∀ i, Mono (f i).hom)
    (hc : IsEtaleCovering B S hS (fun i => (X i).obj) (fun i => (f i).hom))
    (hd : Pairwise fun i j => Disjoint
      (Set.range (pointsMap B S hS (X i).obj (f i).hom))
      (Set.range (pointsMap B S hS (X j).obj (f j).hom))) :
    IsColimit (Cofan.mk Y f) := by
  classical
  -- A morphism of algebraic spaces out of one with no points is unique: the empty family is an
  -- étale covering of it, so Stacks 04P2 descends the empty family of morphisms uniquely.
  have hom_ext_of_isEmpty_points {P Q : AlgebraicSpaces B S hS}
      (hP : IsEmpty (points B S hS P.obj)) (a b : P ⟶ Q) : a = b := by
    let A : Empty → AlgebraicSpaces B S hS := Empty.elim
    let i : ∀ e, A e ⟶ P := fun e => e.elim
    have hc : IsEtaleCovering B S hS (fun e => (A e).obj) (fun e => (i e).hom) := by
      refine ⟨P.property, fun e => e.elim, fun e => e.elim, ?_⟩
      ext x
      exact (hP.false x).elim
    obtain ⟨_, _, hd⟩ := existsUnique_desc_of_fpqcCovering B S hS i
      (isFpqcCovering_of_isEtaleCovering B S hS _ _ hc) Q (fun e => e.elim) (fun e => e.elim)
    exact (hd a (fun e => e.elim)).trans (hd b (fun e => e.elim)).symm
  have hdesc (s : Cofan X) : ∃! k : Y ⟶ s.pt, ∀ i, f i ≫ k = s.inj i := by
    apply existsUnique_desc_of_fpqcCovering B S hS f
      (isFpqcCovering_of_isEtaleCovering B S hS _ _ hc) s.pt s.inj
    intro i j
    by_cases hij : i = j
    · subst j
      apply ObjectProperty.hom_ext
      have := hm i
      have hp : pullback.fst (f i).hom (f i).hom = pullback.snd (f i).hom (f i).hom :=
        (cancel_mono (f i).hom).mp pullback.condition
      change pullback.fst (f i).hom (f i).hom ≫ _ = pullback.snd (f i).hom (f i).hom ≫ _
      rw [hp]
    · apply hom_ext_of_isEmpty_points
      refine ⟨fun x => ?_⟩
      have hp := congrArg (fun k => pointsMap B S hS (pullback (f i).hom (f j).hom) k x)
          (pullback.condition (f := (f i).hom) (g := (f j).hom))
      have e₁ := pointsMap_comp_apply B S hS (pullback.fst (f i).hom (f j).hom) (f i).hom x
      have e₂ := pointsMap_comp_apply B S hS (pullback.snd (f i).hom (f j).hom) (f j).hom x
      exact Set.disjoint_left.mp (hd hij) ⟨_, rfl⟩ ⟨_, e₂.symm.trans (hp.symm.trans e₁)⟩
  exact Cofan.IsColimit.mk _ (fun s => (hdesc s).choose)
    (fun s => (hdesc s).choose_spec.1) (fun s => (hdesc s).choose_spec.2)

end AlgebraicGeometry.Space

end
