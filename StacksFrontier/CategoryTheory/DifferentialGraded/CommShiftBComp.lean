module

public import StacksFrontier.CategoryTheory.DifferentialGraded.ExactFunctor
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.Evaluation

/-!
# The hypothesis `F(x[1]) = F(x)[1]` is stable under composition

`DGCategory.DGFunctor.CommShiftB` is the hypothesis of [Stacks, Tag 0FQF] on a
functor of differential graded categories: it commutes with the shift functors of axiom (B), on
objects, on homogeneous morphisms, and on the identifications `Hom(x, y)[n] ≅ Hom(x, y[n])`.
This file shows that a composite of two such functors is again one, so Tag 0FQF applies to a
functor presented as a composite.

That is what the derived pullback and the derived pushforward of a sheaf of differential graded
modules need: `ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` of [Stacks, Tag 0FTE] is an inverse image followed by two
extensions of scalars, and `ℳ ↦ f_*SheafHom^dg_{𝒜'}(𝒩, ℳ)` of [Stacks, Tag 0FTS] is an internal
hom followed by a direct image.

## Main results

* `DGCategory.DGFunctor.CommShiftB.comp`: the composite of two functors of
  differential graded categories commuting with the shift commutes with the shift.

## Implementation notes

The three fields are chained through the middle axiom (B) datum. The two that are `HEq`
statements need the shifted objects of the middle category to be moved along the object clause
of the first functor before the second functor is applied, which is `heq_map_of_obj_eq`: a
functor of differential graded categories carries heterogeneously equal homogeneous morphisms
over equal source and target objects to heterogeneously equal ones.

## References

* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
* [Stacks Project, Tag 09L6](https://stacks.math.columbia.edu/tag/09L6)
-/

@[expose] public section

namespace DGCategory

open CategoryTheory

universe u₁ u₂ u₃ v₁ v₂ v₃ r

variable {R : Type r} [CommRing R] {A : DGCategory.{v₁, u₁} R} {B : DGCategory.{v₂, u₂} R}
  {D : DGCategory.{v₃, u₃} R}

/-- **A functor of differential graded categories preserves heterogeneous equality of
homogeneous morphisms** over equal source and target objects. -/
theorem DGFunctor.heq_map_of_obj_eq (G : DGFunctor B D) {x x' y y' : B.Obj} {n : ℤ}
    (hx : x = x') (hy : y = y') {f : B.Hom x y n} {f' : B.Hom x' y' n} (hf : HEq f f') :
    HEq (G.map f) (G.map f') := by
  subst hx
  subst hy
  cases hf
  rfl

/-- **The composite of two functors of differential graded categories commuting with the shift
commutes with the shift**, so [Stacks, Tag 0FQF] applies to it. -/
theorem DGFunctor.CommShiftB.comp {F : DGFunctor A B} {G : DGFunctor B D} {SA : ShiftAxiomB A}
    {SB : ShiftAxiomB B} {SD : ShiftAxiomB D} (hF : F.CommShiftB SA SB)
    (hG : G.CommShiftB SB SD) : (F.comp G).CommShiftB SA SD where
  obj n x := (congrArg G.obj (hF.obj n x)).trans (hG.obj n (F.obj x))
  map n {x y _k} f :=
    (G.heq_map_of_obj_eq (hF.obj n x) (hF.obj n y) (hF.map n f)).trans (hG.map n (F.map f))
  toShift n x y k f :=
    (G.heq_map_of_obj_eq rfl (hF.obj n y) (hF.toShift n x y k f)).trans
      (hG.toShift n (F.obj x) (F.obj y) k (F.map f))

end DGCategory

end
