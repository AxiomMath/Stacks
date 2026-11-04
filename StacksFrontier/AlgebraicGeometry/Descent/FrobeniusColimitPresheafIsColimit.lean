module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ExtendScalarsSeqColimit
public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitPresheafDiagram
public import StacksFrontier.CategoryTheory.Limits.SequentialShift

/-!
# The objectwise cocone of Stacks Tag 0EXB is colimiting

Let `p` be a prime, let `X` be a scheme in characteristic `p`, write `A` for the presheaf of
rings of sections of `𝒪_X` and `φ^j : A ⟶ A` for the `j`-th power of the `p`-th power map, and
let `M` be a presheaf of `A`-modules. `AlgebraicGeometry.frobeniusPresheafCocone` is the cocone
of presheaves of `A`-modules

`j ↦ A ⊗_{φ^j, A} M`, with apex `(colim_j A) ⊗_A M`,

whose leg at `j` is the base change along the stage-`n + j` coprojection. **This file proves
that it is a colimit cocone**, which is the last mathematical input of Stacks Tag 0EXB.

## The proof

`Stacks.NoncommChangeOfRings.Presheaf.isColimitNatSeqCocone` proves exactly this for an
abstract sequential diagram of presheaves of rings `k ↦ B_k` with a colimit cocone `c` and
compatible morphisms `β_k : A ⟶ B_k`. The diagram of rings here is the Frobenius tower read on
underlying presheaves, and because the legs of 0EXB's cocone are the coprojections at stage
`n + j` rather than at stage `j`, the cocone of rings needed is the colimit cocone of that
tower **shifted by `n`** — which is again colimiting by
`CategoryTheory.Limits.isColimitWhiskerNatShift`.

## Main definitions

* `AlgebraicGeometry.frobeniusRingPresheafDiagram`: the Frobenius tower of the structure sheaf,
  read as a diagram of presheaves of rings, with
  `AlgebraicGeometry.frobeniusRingPresheafShiftedCocone` its colimit cocone shifted by `n`.

## Main results

* `AlgebraicGeometry.isColimit_frobeniusPresheafCocone`: **the objectwise cocone of Stacks Tag
  0EXB is colimiting.**

## Implementation notes

The three inputs the abstract statement asks for are each a lemma here. The compatibility of
the powers of Frobenius with a *general* transition of the tower is an induction on the index
difference, in which every comparison of morphisms of `ℕ` is `Subsingleton.elim`; it cannot be
read off the successor case alone because the algebraic diagram of base changes is a functor on
all of `ℕ`. The transition morphism of 0EXB's diagram is the base change along one Frobenius,
while the abstract statement asks for the base change along the tower's transition, and those
two morphisms are equal only by `CategoryTheory.Limits.endoSequence_map_succ`; the two base
changes are identified by `Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo_congr`. The legs
need no such step: the shifted cocone's leg at `j` is the stage-`n + j` coprojection on the
nose.

## References

* [Stacks Project, Tag 0EXB](https://stacks.math.columbia.edu/tag/0EXB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Frobenius TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (p : ℕ) [Fact p.Prime] (hX : IsInCharacteristic X p)

/-- **The Frobenius tower of the structure sheaf, read as a diagram of presheaves of rings.**
Its colimit is `AlgebraicGeometry.frobeniusRingPresheaf`, the objectwise filtered colimit
`V ↦ colim_j 𝒪_X(V)`. -/
noncomputable def frobeniusRingPresheafDiagram :
    ℕ ⥤ ((Opens (X : TopCat))ᵒᵖ ⥤ RingCat.{u}) :=
  frobeniusRingSheafDiagram X p hX ⋙
    sheafToPresheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u}

/-- A single step of the tower of presheaves of rings is Frobenius. -/
lemma frobeniusRingPresheafDiagram_map_succ (m : ℕ) :
    (frobeniusRingPresheafDiagram X p hX).map (homOfLE (Nat.le_add_right m 1)) =
      (frobeniusRingSheafHom X p hX).hom :=
  congrArg (fun t : X.ringSheafOnOpens ⟶ X.ringSheafOnOpens ↦ t.hom)
    (endoSequence_map_succ (frobeniusRingSheafHom X p hX) m)

/-- **The `j`-th power of Frobenius followed by any transition of the tower, read on presheaves
of rings, is the power at the target index.** This is the compatibility which makes the powers
of Frobenius a family of morphisms over the whole diagram, and not merely over its successor
steps: the algebraic diagram of base changes is a functor on all of `ℕ`. -/
lemma frobeniusRingSheafIter_hom_comp_frobeniusRingPresheafDiagram_map (n : ℕ) :
    ∀ {j j' : ℕ}, j ≤ j' → ∀ g : (n + j : ℕ) ⟶ (n + j' : ℕ),
      (frobeniusRingSheafIter X p hX j).hom ≫ (frobeniusRingPresheafDiagram X p hX).map g =
        (frobeniusRingSheafIter X p hX j').hom := by
  intro j j' h
  induction j', h using Nat.le_induction with
  | base =>
    intro g
    rw [Subsingleton.elim g (𝟙 (n + j)), CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  | succ j' h ih =>
    intro g
    exact comp_map_succ_step (frobeniusRingPresheafDiagram X p hX)
      (frobeniusRingSheafIter X p hX j).hom (homOfLE (Nat.add_le_add_left h n))
      (homOfLE (Nat.le_add_right (n + j') 1)) g (Subsingleton.elim _ _)
      (frobeniusRingSheafIter X p hX j').hom (ih (homOfLE (Nat.add_le_add_left h n)))
      (frobeniusRingSheafHom X p hX).hom
      (frobeniusRingPresheafDiagram_map_succ X p hX (n + j'))
      (frobeniusRingSheafIter X p hX (j' + 1)).hom
      (frobeniusRingSheafIter_hom_comp_frobeniusRingSheafHom_hom X p hX j')

/-- **The colimit cocone of the tower of presheaves of rings, shifted by `n`**: its leg at `j`
is the stage-`n + j` coprojection `𝒪_X ⟶ colim_j 𝒪_X`, which is the leg 0EXB's cocone is built
from. -/
noncomputable def frobeniusRingPresheafShiftedCocone (n : ℕ) :
    Cocone (natShift n ⋙ frobeniusRingPresheafDiagram X p hX) :=
  (colimit.cocone (frobeniusRingPresheafDiagram X p hX)).whisker (natShift n)

/-- The leg at `j` of `AlgebraicGeometry.frobeniusRingPresheafShiftedCocone` at `n` is the
coprojection `AlgebraicGeometry.frobeniusRingPresheafι` at stage `n + j`. -/
@[simp]
lemma frobeniusRingPresheafShiftedCocone_ι_app (n j : ℕ) :
    (frobeniusRingPresheafShiftedCocone X p hX n).ι.app j =
      frobeniusRingPresheafι X p hX (n + j) := rfl

/-- **Shifting the tower by `n` keeps its colimit cocone colimiting**: the shift is cofinal in
`ℕ`. -/
noncomputable def isColimitFrobeniusRingPresheafShiftedCocone (n : ℕ) :
    IsColimit (frobeniusRingPresheafShiftedCocone X p hX n) :=
  isColimitWhiskerNatShift (frobeniusRingPresheafDiagram X p hX)
    (colimit.isColimit (frobeniusRingPresheafDiagram X p hX)) n

/-- The powers of Frobenius are a family of morphisms over the shifted tower. -/
lemma frobeniusRingSheafIter_hom_comp_shifted_map (n : ℕ) {j j' : ℕ} (f : j ⟶ j') :
    (frobeniusRingSheafIter X p hX j).hom ≫
        (natShift n ⋙ frobeniusRingPresheafDiagram X p hX).map f =
      (frobeniusRingSheafIter X p hX j').hom :=
  frobeniusRingSheafIter_hom_comp_frobeniusRingPresheafDiagram_map X p hX n (leOfHom f)
    ((natShift n).map f)

/-- A single step of the shifted tower is Frobenius. -/
lemma frobeniusRingPresheafShifted_map_succ (n j : ℕ) :
    (natShift n ⋙ frobeniusRingPresheafDiagram X p hX).map (homOfLE (Nat.le_add_right j 1)) =
      (frobeniusRingSheafHom X p hX).hom := by
  rw [Functor.comp_map, Subsingleton.elim ((natShift n).map (homOfLE (Nat.le_add_right j 1)))
    (homOfLE (Nat.le_add_right (n + j) 1))]
  exact frobeniusRingPresheafDiagram_map_succ X p hX (n + j)

variable (M : PresheafOfModules.{u} X.ringSheafOnOpens.obj)

/-- **The transition morphism of 0EXB's diagram is the base change along the transition of the
shifted tower.** The two differ only in which of the two equal morphisms `𝒪_X ⟶ 𝒪_X` the base
change is taken along, and `baseChangeTo_congr` is what moves between them. -/
lemma frobeniusPresheafExtendIterMap_eq_baseChangeTo (n j : ℕ) :
    frobeniusPresheafExtendIterMap X p hX M j =
      Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo
        (frobeniusRingSheafIter X p hX j).hom
        ((natShift n ⋙ frobeniusRingPresheafDiagram X p hX).map
          (homOfLE (Nat.le_add_right j 1))) M
        (frobeniusRingSheafIter X p hX (j + 1)).hom
        (frobeniusRingSheafIter_hom_comp_shifted_map X p hX n
          (homOfLE (Nat.le_add_right j 1))) :=
  Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo_congr
    (frobeniusRingSheafIter X p hX j).hom (frobeniusRingSheafHom X p hX).hom M
    ((natShift n ⋙ frobeniusRingPresheafDiagram X p hX).map
      (homOfLE (Nat.le_add_right j 1)))
    (frobeniusRingPresheafShifted_map_succ X p hX n j).symm
    (frobeniusRingSheafIter X p hX (j + 1)).hom
    (frobeniusRingSheafIter_hom_comp_frobeniusRingSheafHom_hom X p hX j)
    (frobeniusRingSheafIter_hom_comp_shifted_map X p hX n (homOfLE (Nat.le_add_right j 1)))

/-- **The leg of 0EXB's cocone is the base change along the leg of the shifted cocone of
rings**: the shifted leg at `j` is the stage-`n + j` coprojection, which is the coprojection the
leg was built from. The two coprojections are definitionally equal, but `baseChangeTo` must not
be asked to see that — unfolding it puts the adjoint transpose in front of the unifier — so the
step is `baseChangeTo_congr` on the middle morphism instead. -/
lemma frobeniusPresheafCocone_ι_app_eq_baseChangeTo (n j : ℕ) :
    (frobeniusPresheafCocone X p hX M n).ι.app j =
      Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo
        (frobeniusRingSheafIter X p hX j).hom
        ((frobeniusRingPresheafShiftedCocone X p hX n).ι.app j) M
        (frobeniusRingPresheafι X p hX n)
        (frobeniusRingSheafIter_hom_comp_frobeniusRingPresheafι X p hX j n) :=
  (frobeniusPresheafCocone_ι_app X p hX M n j).trans
    (Stacks.NoncommChangeOfRings.Presheaf.baseChangeTo_congr
      (frobeniusRingSheafIter X p hX j).hom (frobeniusRingPresheafι X p hX (n + j)) M
      ((frobeniusRingPresheafShiftedCocone X p hX n).ι.app j)
      (frobeniusRingPresheafShiftedCocone_ι_app X p hX n j).symm
      (frobeniusRingPresheafι X p hX n)
      (frobeniusRingSheafIter_hom_comp_frobeniusRingPresheafι X p hX j n)
      (frobeniusRingSheafIter_hom_comp_frobeniusRingPresheafι X p hX j n))

/-- **The objectwise cocone of Stacks Tag 0EXB is colimiting.** Extension of scalars commutes
with the colimit of the target ring — no flatness and no commutativity — and the colimit of
rings in question is the Frobenius tower's, shifted by `n` so that its legs are the
coprojections at stage `n + j`. This is the last mathematical input of Stacks Tag 0EXB. -/
noncomputable def isColimit_frobeniusPresheafCocone (n : ℕ) :
    IsColimit (frobeniusPresheafCocone X p hX M n) :=
  Stacks.NoncommChangeOfRings.Presheaf.isColimitNatSeqCocone
    (𝔅 := natShift n ⋙ frobeniusRingPresheafDiagram X p hX)
    (c := frobeniusRingPresheafShiftedCocone X p hX n)
    (fun j ↦ (frobeniusRingSheafIter X p hX j).hom)
    (fun {_ _} f ↦ frobeniusRingSheafIter_hom_comp_shifted_map X p hX n f)
    (frobeniusRingPresheafι X p hX n)
    (fun j ↦ frobeniusRingSheafIter_hom_comp_frobeniusRingPresheafι X p hX j n)
    M (fun j ↦ frobeniusPresheafExtendIterMap X p hX M j)
    (frobeniusPresheafCocone X p hX M n).ι
    (isColimitFrobeniusRingPresheafShiftedCocone X p hX n)
    (fun j ↦ frobeniusPresheafExtendIterMap_eq_baseChangeTo X p hX M n j)
    (fun j ↦ frobeniusPresheafCocone_ι_app_eq_baseChangeTo X p hX M n j)

end AlgebraicGeometry

end
