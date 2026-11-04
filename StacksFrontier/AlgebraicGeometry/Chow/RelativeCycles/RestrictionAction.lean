module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ActionOnCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Restriction
public import StacksCore.Tactic.StacksAttribute

/-!
# The action of a family of relative cycles commutes with restriction to opens

Let `f : X ⟶ Y` be a morphism of schemes locally of finite type over the base of a Chow
situation, let `α` be a family of `r`-cycles on the fibres of `X/Y` and let `β` be an
`e`-cycle on `Y`. The action `α ∩ β`, an `(r + e)`-cycle on `X`, is `Stacks.Chow.cap`. If
`U ⊆ X` and `V ⊆ Y` are open with `f(U) ⊆ V`, then `(α ∩ β)|_U = α|_U ∩ β|_V`.

## Main results

* `Stacks.Chow.restrictedFiberMap_asFiber` — the canonical morphism of fibres attached to a
  square of open immersions carries the canonical fibre point of a point of `U` to the
  canonical fibre point of its image in `X`.
* `Stacks.Chow.cycleGroupRestrict_cap` — restricting `α ∩ β` to `U` gives the action of the
  restricted family `α|_U` on the restricted cycle `β|_V`.

## Implementation notes

The three operations compared here already exist and are reused rather than redefined:
`Stacks.Chow.cap` for the action, `Stacks.Chow.cycleGroupRestrict` for the restriction of a
cycle to an open subscheme — which is flat pullback in relative dimension zero, Tag 02RB, by
`Stacks.Chow.cycleGroupRestrict_eq_flatPullback` — and `Stacks.Chow.restrictedFamily` for the
restriction of a family of cycles to the fibres of `U/V`. Restriction preserves the
`δ`-dimension, so both sides of the equality lie in `Z_{r + e}(U)` and no cast is needed.

The inclusions `U ⊆ X` and `V ⊆ Y` are open immersions `j` and `i`, and `f(U) ⊆ V` is recorded
by the commutative square `h : j ≫ f = fU ≫ i` exhibiting the restricted morphism `fU = f|_U`.
Local finite type of `fU` is deduced from the square by cancellation rather than assumed, and
the structure morphisms of `X` and `U` are the composites `f ≫ sY` and `fU ≫ sV`.

The fibres of `f` over `f (j x)` and over `i (fU x)` are equal but not syntactically so, and
the coefficients of `α` are transported between them along `eqToHom`;
`Stacks.Chow.restrictedFiberMap_asFiber` identifies that transport with the canonical morphism
of fibres, which is what makes the two sides comparable.

## References

* [Stacks Project, Tag 0H67](https://stacks.math.columbia.edu/tag/0H67)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-- Transport of a fibre of `f` along an equality of base points is compatible with the
inclusions of the fibres into the total space. -/
private theorem eqToHom_fiber_comp_fiberι {X Y : Scheme.{u}} (f : X ⟶ Y) {y z : Y} (h : y = z) :
    eqToHom (congrArg (fun t : Y => f.fiber t) h) ≫ f.fiberι z = f.fiberι y := by
  cases h
  rfl

/-- Transport of a family of cycles on the fibres of `f` along an equality of base points
leaves every coefficient unchanged. -/
private theorem familyCoefficient_eq_of_fiberPoint_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {r : ℕ} (α : FamilyOfCycles f r) {y z : Y} (h : y = z)
    (x : f.fiber y) :
    (α y : AlgebraicCycle (f.fiber y) ℤ) x =
      (α z : AlgebraicCycle (f.fiber z) ℤ)
        (eqToHom (congrArg (fun t : Y => f.fiber t) h) x) := by
  cases h
  rfl

/-- The morphism of fibres attached to a square `j ≫ f = fU ≫ i` of open immersions carries the
canonical point of the fibre of `fU` through `x` to the canonical point of the fibre of `f`
through `j x`, transported along the equality `f (j x) = i (fU x)` of base points. -/
theorem restrictedFiberMap_asFiber {X Y U V : Scheme.{u}} (f : X ⟶ Y) (fU : U ⟶ V)
    (j : U ⟶ X) (i : V ⟶ Y) (h : j ≫ f = fU ≫ i) (x : U) :
    restrictedFiberMap f fU j i h (fU x) (fU.asFiber x) =
      eqToHom (congrArg (fun t : Y => f.fiber t)
        (congrArg (fun g : U ⟶ Y => g x) h)) (f.asFiber (j x)) := by
  have hp : f (j x) = i (fU x) := congrArg (fun g : U ⟶ Y => g x) h
  apply (f.fiberι (i (fU x))).isEmbedding.injective
  calc
    f.fiberι (i (fU x)) (restrictedFiberMap f fU j i h (fU x) (fU.asFiber x)) =
        j (fU.fiberι (fU x) (fU.asFiber x)) :=
      congrArg (fun q : fU.fiber (fU x) ⟶ X => q (fU.asFiber x))
        (restrictedFiberMap_fiberι f fU j i h (fU x))
    _ = j x := by rw [Scheme.Hom.fiberι_asFiber]
    _ = (eqToHom (congrArg (fun t : Y => f.fiber t) hp) ≫ f.fiberι (i (fU x)))
          (f.asFiber (j x)) := by
        rw [eqToHom_fiber_comp_fiberι f hp, Scheme.Hom.fiberι_asFiber]

/-- **Stacks Project, Tag 0H67.** If `U ⊆ X` and `V ⊆ Y` are open and `f(U) ⊆ V`, then the
restriction to `U` of the cycle `α ∩ β` is `α|_U ∩ β|_V`, the cycle obtained by letting the
restriction of the family `α` to the fibres of `U/V` act on the restriction of `β` to `V`. -/
@[stacks 0H67]
theorem cycleGroupRestrict_cap (C : ChowSituation.{u}) {X Y U V : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sV : V ⟶ C.S) [LocallyOfFiniteType sV]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (fU : U ⟶ V)
    (j : U ⟶ X) [IsOpenImmersion j] (i : V ⟶ Y) [IsOpenImmersion i]
    (hi : i ≫ sY = sV) (h : j ≫ f = fU ≫ i) (r : ℕ) (e : ℤ)
    (α : FamilyOfCycles f r) (β : CycleGroup C sY e) :
    letI : LocallyOfFiniteType fU := by
      let : LocallyOfFiniteType (fU ≫ i) := h ▸ inferInstance
      exact locallyOfFiniteType_of_comp fU i
    letI : LocallyOfFiniteType (f ≫ sY) := inferInstance
    letI : LocallyOfFiniteType (fU ≫ sV) := inferInstance
    cycleGroupRestrict C (f ≫ sY) (fU ≫ sV) j
        (by rw [← Category.assoc, h, Category.assoc, hi]) ((r : ℤ) + e)
        (cap C sY f α β) =
      cap C sV fU (restrictedFamily f fU j i h r α).1
        (cycleGroupRestrict C sY sV i hi e β) := by
  let : LocallyOfFiniteType fU := by
    let : LocallyOfFiniteType (fU ≫ i) := h ▸ inferInstance
    exact locallyOfFiniteType_of_comp fU i
  let : LocallyOfFiniteType (f ≫ sY) := inferInstance
  let : LocallyOfFiniteType (fU ≫ sV) := inferInstance
  apply Subtype.ext
  ext x
  rw [cycleGroupRestrict_apply, cap_apply, cap_apply]
  simp only [capCoeff]
  have hpoint : f (j x) = i (fU x) := congrArg (fun g : U ⟶ Y => g x) h
  change β.1 (f (j x)) *
      (α (f (j x)) : AlgebraicCycle (f.fiber (f (j x))) ℤ) (f.asFiber (j x)) =
    (cycleGroupRestrict C sY sV i hi e β).1 (fU x) *
      ((restrictedFamily f fU j i h r α).1 (fU x) :
        AlgebraicCycle (fU.fiber (fU x)) ℤ) (fU.asFiber x)
  rw [cycleGroupRestrict_apply]
  have hCoeff :=
    (familyCoefficient_eq_of_fiberPoint_eq f α hpoint (f.asFiber (j x))).trans
      (congrArg (fun z => (α (i (fU x)) : AlgebraicCycle (f.fiber (i (fU x))) ℤ) z)
        (restrictedFiberMap_asFiber f fU j i h x).symm)
  rw [hCoeff, (restrictedFamily f fU j i h r α).2 (fU x) (fU.asFiber x)]
  congr 2

end Stacks.Chow

end
