module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplement

/-!
# Freeness of the symmetric group action on the complement of the diagonals, on test spaces

Let `f : U → X` be an étale and separated morphism of algebraic spaces over a scheme `S` and
let `W = U ×_X ⋯ ×_X U ∖ (all diagonals)` with `n` factors be the space `W_p` of
[Stacks, Tag 0726].  The symmetric group `S_n` acts on `W` over `X`, and that action is free.

[Stacks, Tag 0726] records freeness in the shape the site-theoretic notion of a torsor asks
for, `AlgebraicGeometry.Space.SpacesEtale.eq_one_of_comp_diagonalComplementAut`: a morphism
`φ : V ⟶ W` *of the spaces-étale site of `X`* fixed by `σ` forces `σ = 1` unless the empty
sieve covers `V`.  The quotient constructions ask for freeness on the points of `W` over test
objects that are *not* étale over `X` — the test object of [Stacks, Tag 02Z2] is an arbitrary
scheme over `S`, and the one the quotient sheaf of [Stacks, Tag 071S] is built from is
`Spec κ(w)` at a point `w`.  This file provides freeness in that shape.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.eq_one_of_comp_diagonalComplementAut_of_nonempty_points`:
  a morphism of algebraic spaces `x : T ⟶ W` from a space with a point, fixed by `σ`, forces
  `σ = 1`.

## Implementation notes

The test object is an arbitrary algebraic space over `S` rather than an object of the
spaces-étale site of `X`, and that is the whole point: the morphism `x` is a morphism of
algebraic spaces, not a morphism over `X` between spaces étale over `X`.

Freeness genuinely needs a test *object*, not a point: the action of `S_n` on the *point set*
of `W` is **not** free.  For `X = Spec k` and `U = Spec k'` with `k'/k` separable quadratic,
`W = U ×_X U ∖ Δ` is `Spec k'` with one point, which the transposition fixes — it acts there
by the nontrivial automorphism of `k'`, which is invisible to the point set.  So the argument
below stays with morphisms until the very last step, where a point of `T` is used only to
exhibit a point of `W` lying on a diagonal of `U^n`.

The step that does not survive on points is the factorisation
`AlgebraicGeometry.Space.SpacesEtale.comp_projPair_eq` of a morphism with two equal components
through the diagonal of `U ×_X U`.  It is available for a morphism of algebraic spaces because
`AlgebraicGeometry.Space.SpacesEtale.isPullback_toSpaces_prodTwo` exhibits the algebraic space
underlying `U ×_X U` as the fibre product of algebraic spaces, so its two projections are
jointly monomorphic in the category of algebraic spaces over `S`.

## References

* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- A morphism of algebraic spaces into `U^n` whose components of index `i` and `j` agree
factors through the diagonal of `U ×_X U`.  This is
`AlgebraicGeometry.Space.SpacesEtale.comp_projPair_eq` for a test object that is an algebraic
space over `S` rather than an object of the spaces-étale site of `X`: the two projections of
`U ×_X U` are jointly monomorphic because they exhibit it as a fibre product of algebraic
spaces. -/
theorem comp_toSpaces_map_projPair_eq (U : SpacesEtale B S hS X) (n : ℕ)
    {T : AlgebraicSpaces B S hS} (ψ : T ⟶ underlying B S hS X (selfProd B S hS X U n))
    (i j : Fin n)
    (h : ψ ≫ (toSpaces B S hS X).map (Pi.π (fun _ : Fin n => U) i) =
      ψ ≫ (toSpaces B S hS X).map (Pi.π (fun _ : Fin n => U) j)) :
    ψ ≫ (toSpaces B S hS X).map (projPair B S hS X U n i j) =
      (ψ ≫ (toSpaces B S hS X).map (Pi.π (fun _ : Fin n => U) i)) ≫
        (toSpaces B S hS X).map (diagTwo B S hS X U) := by
  refine (isPullback_toSpaces_prodTwo B S hS X U).hom_ext ?_ ?_
  · rw [Category.assoc, ← Functor.map_comp, projPair_comp_fst, Category.assoc,
      ← Functor.map_comp, diagTwo_comp_fst, CategoryTheory.Functor.map_id, Category.comp_id]
  · rw [Category.assoc, ← Functor.map_comp, projPair_comp_snd, Category.assoc,
      ← Functor.map_comp, diagTwo_comp_snd, CategoryTheory.Functor.map_id, Category.comp_id,
      h]

/-- **Stacks 0726, freeness of the action of `S_n` on `W`, on algebraic space test objects.**
A morphism of algebraic spaces `x : T ⟶ W` out of an algebraic space with a point, fixed by a
permutation `σ` of the factors, forces `σ = 1`.

Pick `i` with `σ⁻¹ i ≠ i`.  The composite `ψ : T ⟶ U^n` has equal components of index `i` and
`σ⁻¹ i`, so it factors through the diagonal of `U ×_X U` after projecting onto those two
factors; a point of `T` therefore produces a point of `W` lying on that diagonal, whereas the
points of `W` avoid all the diagonals. -/
theorem eq_one_of_comp_diagonalComplementAut_of_nonempty_points (U : SpacesEtale B S hS X)
    (n : ℕ) (hsep : IsSeparated B S hS U.1.hom.hom) {T : AlgebraicSpaces B S hS}
    (x : T ⟶ underlying B S hS X (diagonalComplement B S hS X U n hsep))
    (hT : Nonempty (points B S hS T.1)) (σ : Equiv.Perm (Fin n))
    (hx : x ≫ (toSpaces B S hS X).map
      (diagonalComplementAut B S hS X U n hsep σ).asIso.hom = x) :
    σ = 1 := by
  by_contra hσ
  obtain ⟨i, hi⟩ : ∃ i : Fin n, σ⁻¹ i ≠ i := by
    by_contra hall
    exact hσ (inv_eq_one.1 (Equiv.ext fun i => not_ne_iff.1 (fun h => hall ⟨i, h⟩)))
  obtain ⟨y⟩ := hT
  set ψ : T ⟶ underlying B S hS X (selfProd B S hS X U n) :=
    x ≫ (toSpaces B S hS X).map (diagonalComplementι B S hS X U n hsep) with hψ
  have hfix : ψ ≫ (toSpaces B S hS X).map (permProd U n σ) = ψ := by
    rw [hψ, Category.assoc, ← Functor.map_comp, ← diagonalComplementPerm_ι,
      Functor.map_comp, ← Category.assoc, ← diagonalComplementAut_hom, hx]
  have hπ : ψ ≫ (toSpaces B S hS X).map (Pi.π (fun _ : Fin n => U) i) =
      ψ ≫ (toSpaces B S hS X).map (Pi.π (fun _ : Fin n => U) (σ⁻¹ i)) := by
    conv_lhs => rw [← hfix]
    rw [Category.assoc, ← Functor.map_comp, permProd_π]
  have hfactor := comp_toSpaces_map_projPair_eq B S hS X U n ψ i (σ⁻¹ i) hπ
  have hmemW : pointsMap B S hS T.1 ψ.hom ∈
      {g | ∀ z, g z ∈ diagonalComplementPoints B S hS X U n} := by
    intro z
    rw [hψ]
    have hcomp : (x ≫ (toSpaces B S hS X).map
        (diagonalComplementι B S hS X U n hsep)).hom =
        x.hom ≫ ((toSpaces B S hS X).map
          (diagonalComplementι B S hS X U n hsep)).hom := rfl
    rw [hcomp, pointsMap_comp_apply]
    exact mem_diagonalComplementPoints_pointsMap_diagonalComplementι B S hS X U n hsep _
  refine (mem_diagonalComplementPoints_iff B S hS X U n _).1 (hmemW y) i (σ⁻¹ i)
    (Ne.symm hi) ?_
  show pointsMap B S hS (underlying B S hS X (selfProd B S hS X U n)).1
      ((toSpaces B S hS X).map (projPair B S hS X U n i (σ⁻¹ i))).hom
      (pointsMap B S hS T.1 ψ.hom y) ∈
    Set.range (pointsMap B S hS (underlying B S hS X U).1
      ((toSpaces B S hS X).map (diagTwo B S hS X U)).hom)
  rw [← pointsMap_comp_apply]
  have hcomp : ψ.hom ≫ ((toSpaces B S hS X).map
      (projPair B S hS X U n i (σ⁻¹ i))).hom =
      (ψ ≫ (toSpaces B S hS X).map (projPair B S hS X U n i (σ⁻¹ i))).hom := rfl
  rw [hcomp, hfactor]
  have hcomp₂ : ((ψ ≫ (toSpaces B S hS X).map (Pi.π (fun _ : Fin n => U) i)) ≫
      (toSpaces B S hS X).map (diagTwo B S hS X U)).hom =
      (ψ ≫ (toSpaces B S hS X).map (Pi.π (fun _ : Fin n => U) i)).hom ≫
        ((toSpaces B S hS X).map (diagTwo B S hS X U)).hom := rfl
  rw [hcomp₂, pointsMap_comp_apply]
  exact ⟨_, rfl⟩

end AlgebraicGeometry.Space.SpacesEtale

end
