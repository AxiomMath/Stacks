module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Function.Basic

/-!
# Compatible sequences of a tower of types

A *tower of types* is a family `T : ℕ → Type*` together with transition maps
`t n : T (n + 1) → T n`, and its compatible sequences are the subtype

`{x : ∀ n, T n // ∀ n, t n (x (n + 1)) = x n}`.

This is the shape in which an inverse limit over `ℕᵒᵖ` is written down whenever the system is
given by its successor transitions — `AlgebraicGeometry.Space.adicSectionsAt`, Mathlib's
`AdicCompletion` after `Stacks.ProZero.adicTowerSectionsEquiv`, and
`Stacks.ProZero.towerSections` are all of this form — and this file supplies the three
elementary operations on it which a comparison of two such limits needs: the map induced by a
map of towers, the equivalence induced by a levelwise equivalence of towers, and the shift of
the index by one.

No algebra is involved: the statements are about types and functions, so that they apply to the
sections of a sheaf, to a module of linear maps and to a set of isomorphisms alike.

## Main definitions

* `Stacks.SuccTower.sectionsMap` — the map of compatible sequences induced by a map of towers.
* `Stacks.SuccTower.sectionsCongr` — the equivalence induced by a levelwise equivalence of
  towers which intertwines the transition maps.
* `Stacks.SuccTower.sectionsShift` — **the index shift**: the compatible sequences of a tower
  are the compatible sequences of the tower shifted by one.

## Main results

* `Stacks.SuccTower.bijective_sectionsMap_of_congr` — **bijectivity transports across a
  levelwise equivalence of towers**: if two maps of towers correspond under levelwise
  equivalences of both the sources and the targets, and one induces a bijection on compatible
  sequences, so does the other.

## Implementation notes

The subtype is written out in every statement rather than abbreviated, so that a consumer whose
own definition of the compatible sequences is a subtype of this shape — `adicSectionsAt`, say —
can use these declarations with no transport: the two types are definitionally equal and the
induced maps are definitionally equal as well, proof irrelevance taking care of the
compatibility witnesses.

`Stacks.SuccTower.sectionsShift` needs no hypothesis at all.  Dropping the term at level `0` of
a compatible sequence loses nothing, because that term is the image of the term at level `1`; the
inverse accordingly reads the term at level `n` off the term at level `n` of the shifted
sequence, through one transition map.
-/

@[expose] public section

universe v w v' w'

namespace Stacks.SuccTower

/-! ### The map induced by a map of towers -/

/-- **A map of towers of types induces a map of their compatible sequences.**  The hypothesis is
that each square commutes: descending one level and then crossing is crossing and then
descending. -/
def sectionsMap {T : ℕ → Type v} {U : ℕ → Type w} (t : ∀ n, T (n + 1) → T n)
    (u : ∀ n, U (n + 1) → U n) (ψ : ∀ n, T n → U n)
    (hψ : ∀ (n : ℕ) (x : T (n + 1)), ψ n (t n x) = u n (ψ (n + 1) x))
    (x : { x : ∀ n, T n // ∀ n, t n (x (n + 1)) = x n }) :
    { y : ∀ n, U n // ∀ n, u n (y (n + 1)) = y n } :=
  ⟨fun n => ψ n (x.1 n),
    fun n => (hψ n (x.1 (n + 1))).symm.trans (congrArg (ψ n) (x.2 n))⟩

/-- The terms of the induced map of compatible sequences. -/
theorem sectionsMap_apply {T : ℕ → Type v} {U : ℕ → Type w} (t : ∀ n, T (n + 1) → T n)
    (u : ∀ n, U (n + 1) → U n) (ψ : ∀ n, T n → U n)
    (hψ : ∀ (n : ℕ) (x : T (n + 1)), ψ n (t n x) = u n (ψ (n + 1) x))
    (x : { x : ∀ n, T n // ∀ n, t n (x (n + 1)) = x n }) (n : ℕ) :
    (sectionsMap t u ψ hψ x).1 n = ψ n (x.1 n) := rfl

/-! ### The equivalence induced by a levelwise equivalence of towers -/

/-- **A levelwise equivalence of towers of types which intertwines the transition maps induces
an equivalence of their compatible sequences.** -/
def sectionsCongr {T : ℕ → Type v} {U : ℕ → Type w} (t : ∀ n, T (n + 1) → T n)
    (u : ∀ n, U (n + 1) → U n) (e : ∀ n, T n ≃ U n)
    (he : ∀ (n : ℕ) (x : T (n + 1)), e n (t n x) = u n (e (n + 1) x)) :
    { x : ∀ n, T n // ∀ n, t n (x (n + 1)) = x n } ≃
      { y : ∀ n, U n // ∀ n, u n (y (n + 1)) = y n } where
  toFun := sectionsMap t u (fun n => e n) he
  invFun := sectionsMap u t (fun n => (e n).symm) fun n y => (e n).injective
    (((e n).apply_symm_apply (u n y)).trans
      ((congrArg (u n) ((e (n + 1)).apply_symm_apply y)).symm.trans
        (he n ((e (n + 1)).symm y)).symm))
  left_inv x := Subtype.ext (funext fun n => (e n).symm_apply_apply (x.1 n))
  right_inv y := Subtype.ext (funext fun n => (e n).apply_symm_apply (y.1 n))

/-- The terms of `Stacks.SuccTower.sectionsCongr`. -/
theorem sectionsCongr_apply {T : ℕ → Type v} {U : ℕ → Type w} (t : ∀ n, T (n + 1) → T n)
    (u : ∀ n, U (n + 1) → U n) (e : ∀ n, T n ≃ U n)
    (he : ∀ (n : ℕ) (x : T (n + 1)), e n (t n x) = u n (e (n + 1) x))
    (x : { x : ∀ n, T n // ∀ n, t n (x (n + 1)) = x n }) (n : ℕ) :
    (sectionsCongr t u e he x).1 n = e n (x.1 n) := rfl

/-- **Bijectivity of the map of compatible sequences transports across a levelwise equivalence
of towers.**  The two maps of towers are intertwined levelwise by the equivalences `a` of the
sources and `b` of the targets, so the two induced maps of compatible sequences are conjugate;
conjugation preserves bijectivity. -/
theorem bijective_sectionsMap_of_congr {T : ℕ → Type v} {U : ℕ → Type w} {T' : ℕ → Type v'}
    {U' : ℕ → Type w'} (t : ∀ n, T (n + 1) → T n) (u : ∀ n, U (n + 1) → U n)
    (t' : ∀ n, T' (n + 1) → T' n) (u' : ∀ n, U' (n + 1) → U' n)
    (ψ : ∀ n, T n → U n) (hψ : ∀ (n : ℕ) (x : T (n + 1)), ψ n (t n x) = u n (ψ (n + 1) x))
    (ψ' : ∀ n, T' n → U' n)
    (hψ' : ∀ (n : ℕ) (x : T' (n + 1)), ψ' n (t' n x) = u' n (ψ' (n + 1) x))
    (a : ∀ n, T n ≃ T' n) (ha : ∀ (n : ℕ) (x : T (n + 1)), a n (t n x) = t' n (a (n + 1) x))
    (b : ∀ n, U n ≃ U' n) (hb : ∀ (n : ℕ) (x : U (n + 1)), b n (u n x) = u' n (b (n + 1) x))
    (hsq : ∀ (n : ℕ) (x : T n), b n (ψ n x) = ψ' n (a n x))
    (h : Function.Bijective (sectionsMap t' u' ψ' hψ')) :
    Function.Bijective (sectionsMap t u ψ hψ) := by
  have key : (sectionsCongr u u' b hb) ∘ (sectionsMap t u ψ hψ) =
      (sectionsMap t' u' ψ' hψ') ∘ (sectionsCongr t t' a ha) :=
    funext fun x => Subtype.ext (funext fun n => hsq n (x.1 n))
  have hcomp : Function.Bijective
      ((sectionsCongr u u' b hb) ∘ (sectionsMap t u ψ hψ)) := by
    rw [key]
    exact h.comp (sectionsCongr t t' a ha).bijective
  exact (Function.Bijective.of_comp_iff' (sectionsCongr u u' b hb).bijective _).1 hcomp

/-! ### The index shift -/

/-- **The compatible sequences of a tower are the compatible sequences of the tower shifted by
one.**  The term at level `0` of a compatible sequence is the image of its term at level `1`, so
dropping it loses nothing: the inverse reads the term at level `n` off the term at level `n` of
the shifted sequence, through the transition map `t n`. -/
def sectionsShift {T : ℕ → Type v} (t : ∀ n, T (n + 1) → T n) :
    { x : ∀ n, T n // ∀ n, t n (x (n + 1)) = x n } ≃
      { y : ∀ n, T (n + 1) // ∀ n, t (n + 1) (y (n + 1)) = y n } where
  toFun x := ⟨fun n => x.1 (n + 1), fun n => x.2 (n + 1)⟩
  invFun y := ⟨fun n => t n (y.1 n), fun n => congrArg (t n) (y.2 n)⟩
  left_inv x := Subtype.ext (funext fun n => x.2 n)
  right_inv y := Subtype.ext (funext fun n => y.2 n)

/-- The terms of `Stacks.SuccTower.sectionsShift`. -/
theorem sectionsShift_apply {T : ℕ → Type v} (t : ∀ n, T (n + 1) → T n)
    (x : { x : ∀ n, T n // ∀ n, t n (x (n + 1)) = x n }) (n : ℕ) :
    (sectionsShift t x).1 n = x.1 (n + 1) := rfl

end Stacks.SuccTower

end
