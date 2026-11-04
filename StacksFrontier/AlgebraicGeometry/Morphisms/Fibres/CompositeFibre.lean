module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# The fibre of a composite

For `i : A ⟶ B` and `g : B ⟶ S`, the fibre of `i ≫ g` over a point of `S` maps to the fibre of
`g` over that point, and that comparison morphism exhibits the first fibre as the base change of
the second along `i`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The comparison morphism from the fibre of a composite `i ≫ g` to the fibre of `g`. -/
def fiberMapOfSourceHom {A B S : Scheme.{u}} (i : A ⟶ B) (g : B ⟶ S) (s : S) :
    (i ≫ g).fiber s ⟶ g.fiber s := by
  refine pullback.lift (pullback.fst (i ≫ g) (S.fromSpecResidueField s) ≫ i)
    (pullback.snd (i ≫ g) (S.fromSpecResidueField s)) ?_
  change pullback.fst (i ≫ g) (S.fromSpecResidueField s) ≫ (i ≫ g) = _
  exact pullback.condition

/-- The comparison morphism `AlgebraicGeometry.fiberMapOfSourceHom` is compatible with
the inclusions of the two fibres into the two total spaces. -/
theorem fiberMapOfSourceHom_fiberι {A B S : Scheme.{u}} (i : A ⟶ B) (g : B ⟶ S) (s : S) :
    fiberMapOfSourceHom i g s ≫ g.fiberι s = (i ≫ g).fiberι s ≫ i :=
  pullback.lift_fst _ _ _

/-- The comparison morphism `AlgebraicGeometry.fiberMapOfSourceHom` is compatible with
the two maps to the spectrum of the residue field. -/
theorem fiberMapOfSourceHom_fiberToSpecResidueField {A B S : Scheme.{u}} (i : A ⟶ B) (g : B ⟶ S)
    (s : S) : fiberMapOfSourceHom i g s ≫ g.fiberToSpecResidueField s =
      (i ≫ g).fiberToSpecResidueField s :=
  pullback.lift_snd _ _ _

/-- The comparison morphism `AlgebraicGeometry.fiberMapOfSourceHom` exhibits the fibre of
a composite as the base change of the fibre of its second factor along the first factor. -/
theorem fiberMapOfSourceHom_isPullback {A B S : Scheme.{u}} (i : A ⟶ B) (g : B ⟶ S) (s : S) :
    IsPullback (fiberMapOfSourceHom i g s) ((i ≫ g).fiberι s) (g.fiberι s) i := by
  refine .of_right ?_ (fiberMapOfSourceHom_fiberι i g s)
    (show IsPullback (g.fiberToSpecResidueField s) (g.fiberι s) _ g from
      (IsPullback.of_hasPullback g _).flip)
  rw [fiberMapOfSourceHom_fiberToSpecResidueField]
  exact (IsPullback.of_hasPullback _ _).flip

end AlgebraicGeometry

end
