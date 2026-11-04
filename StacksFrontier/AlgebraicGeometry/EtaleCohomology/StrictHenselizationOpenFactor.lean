module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationComponentLift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LocalAcyclicity.SpecializationMap

/-!
# The strict henselization lies over every open neighbourhood of its point

Let `s` be a geometric point of a scheme `S` and `U` an open subscheme of `S` containing the
image of `s`. The canonical morphism `Spec(𝒪^{sh}_{S,s}) ⟶ S` factors through `U`: the
strict henselization is local, so every point of it specializes to the closed point, whose image
is the image of `s`, and an open set is stable under generization.

This is what lets a statement about the strict henselization of an arbitrary scheme be read over
an affine open neighbourhood of the point, which is the setting of [Stacks, Tag 03Q6].

## Main results

* `AlgebraicGeometry.strictHenselizationToBase_mem` — every point of the strict henselization is
  carried into `U`.
* `AlgebraicGeometry.strictHenselizationToOpen` — the factorization through `U`, and
  `AlgebraicGeometry.strictHenselizationToOpen_ι` its defining equation.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)
  (U : S.Opens) (hU : s.hom (closedPoint s.residueField) ∈ U)

include hU in
/-- Every point of the strict henselization at `s` lies over an open subscheme containing the
image of `s`. -/
theorem strictHenselizationToBase_mem (x : strictHenselization B S hS s) :
    strictHenselizationToBase B S hS s x ∈ U := by
  have hx : x ⤳ closedPoint ↥(etaleLocalRing B S hS s) := IsLocalRing.specializes_closedPoint x
  have himage : strictHenselizationToBase B S hS s (closedPoint ↥(etaleLocalRing B S hS s)) =
      s.hom (closedPoint s.residueField) := by
    rw [← geometricPointToStrictHenselization_closedPoint B S hS s]
    exact congrArg (fun g : s.source ⟶ S => g (closedPoint s.residueField))
      (geometricPointToStrictHenselization_comp B S hS s)
  refine (hx.map (strictHenselizationToBase B S hS s).continuous).mem_open U.isOpen ?_
  rw [himage]
  exact hU

include hU in
/-- The range of the canonical morphism from the strict henselization lies in `U`. -/
theorem range_strictHenselizationToBase_subset :
    Set.range (strictHenselizationToBase B S hS s) ⊆ Set.range U.ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact strictHenselizationToBase_mem B S hS s U hU x

/-- The canonical morphism from the strict henselization at `s` factors through any open
subscheme containing the image of `s`. -/
def strictHenselizationToOpen : strictHenselization B S hS s ⟶ U :=
  IsOpenImmersion.lift U.ι (strictHenselizationToBase B S hS s)
    (range_strictHenselizationToBase_subset B S hS s U hU)

/-- The factorization `strictHenselizationToOpen` composed with the inclusion of `U` is the
canonical morphism from the strict henselization to `S`. -/
@[reassoc (attr := simp)]
theorem strictHenselizationToOpen_ι :
    strictHenselizationToOpen B S hS s U hU ≫ U.ι = strictHenselizationToBase B S hS s :=
  IsOpenImmersion.lift_fac _ _ _

end AlgebraicGeometry

end
