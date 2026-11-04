module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineStalkLegs
public import StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentStalkLinear

/-!
# The stalk legs of Stacks 0D0I, as linear equivalences

`Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOne` and
`Stacks.NaiveCotangentAffineStalkLegs.stalkLegZero` identify the stalk at `z` of the degree `-1`,
respectively degree `0`, term of `NL_{B/A}` with the conormal module, respectively the cotangent
space, of the canonical presentation of `Bₓ` over `Aₓ`.  They are recorded there as additive
equivalences, because each is a composite of a map linear over the stalk of the sheaf of rings
underlying `B` with one of the identifications of
`StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentStalk`, which are only semilinear over the
stalk `(A[B])ₓ → Bₓ` of the canonical presentation.

`StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentStalkLinear` upgrades the latter two to
linear equivalences over the stalk of the sheaf of rings underlying `B`; this file does the same
for the two legs, by composing with the first factor, which is linear for that action already
because it is the image of an isomorphism of sheaves of modules under
`AlgebraicGeometry.SheafOfModules.stalkFunctor`.

The existing additive equivalences are untouched, and the linear ones agree with them on
elements (`Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOneLinear_apply` and
`Stacks.NaiveCotangentAffineStalkLegs.stalkLegZeroLinear_apply` are `rfl`), so every statement
already proved about the additive legs applies verbatim.

## Main definitions

* `Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOneLinear` and
  `Stacks.NaiveCotangentAffineStalkLegs.stalkLegZeroLinear`: the two legs, as linear
  equivalences over the stalk of the sheaf of rings underlying `B`.

## Main results

* `Stacks.NaiveCotangentAffineStalkLegs.stalkAddEquivOfIso_smul`: the stalk of an isomorphism of
  sheaves of modules is linear over the stalk of the sheaf of rings.  This is the first factor of
  each leg; it holds because `Stacks.NaiveCotangentAffineStalkLegs.stalkAddEquivOfIso` is by
  construction the underlying additive map of a morphism in `ModuleCat`.
* `Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOne_smul` and
  `Stacks.NaiveCotangentAffineStalkLegs.stalkLegZero_smul`: the two legs are linear.  These are
  the statements the two `AddEquiv`s were missing: the previously available
  `Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOne_germ_smul` and
  `Stacks.NaiveCotangentAffineStalkLegs.stalkLegZero_germ_smul` give the same for a scalar which
  is the germ of a *section* of `B`, which is not enough to produce a linear map.
* `Stacks.NaiveCotangentAffineStalkLegs.stalkLegLinear_d`: the two linear legs carry the stalk of
  the differential of `NL_{B/A}` to the cotangent complex of the stalk extension.  Since the
  stalk of the differential is a morphism in `ModuleCat` over the same ring, this exhibits the
  stalk of `NL_{B/A}` and `NL_{Bₓ/Aₓ}` as isomorphic two-term complexes of modules over the
  stalk of `B` — Stacks 0D09 in the spelling the stalkwise criterion for Stacks 0D0I consumes.

## Implementation notes

The scalar ring is the `RingCat`-valued stalk of
`Stacks.SheafOfModules.Tensor.ringSheaf B`, for the reasons recorded in
`StacksFrontier.Topology.Sheaves.Modules.ConormalSequenceStalkTargetAction`: it is the ring
`AlgebraicGeometry.SheafOfModules.stalkFunctor` is a functor to modules over, and an action of
the `CommRingCat`-valued stalk `Bₓ` on these stalks cannot be elaborated within the heartbeat
ceiling.

**The import order matters.**  `StacksFrontier.Topology.Sheaves.Modules.NaiveCotangentStalkLinear`
must come after the module that brings in
`Stacks.Sites.Conormal.moduleStalkConormalSheaf`, since the order in which instance search
reaches that instance decides whether an action of the stalk of `B` on the stalk of a term of
`NL_{B/A}` is found immediately or only after a comparison of `B` with `A[B]` that exceeds the
heartbeat ceiling: with the two imports of this file's parent module in the other order, nine
declarations time out.

## References

* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I), of whose proof this is a
  step.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex of a morphism of sheaves of rings.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

noncomputable section

namespace Stacks.NaiveCotangentAffineStalkLegs

open Stacks.SheafOfModules Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal
open Stacks.RelativeDifferentialStalk (algebraStalk)

/-- **The stalk of an isomorphism of sheaves of modules is linear** over the stalk of the sheaf
of rings.  `Stacks.NaiveCotangentAffineStalkLegs.stalkAddEquivOfIso` forgets that, being the
underlying additive map of the image of the isomorphism under
`AlgebraicGeometry.SheafOfModules.stalkFunctor`; this recovers it. -/
theorem stalkAddEquivOfIso_smul {T : TopCat.{u}}
    {O : CategoryTheory.Sheaf (Opens.grothendieckTopology T) RingCat.{u}}
    (z : T) {M N : _root_.SheafOfModules.{u} O} (e : M ≅ N)
    (s : ToType (TopCat.Presheaf.stalk (C := RingCat.{u}) O.obj z))
    (w : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf z)) :
    stalkAddEquivOfIso z e (s • w) = s • stalkAddEquivOfIso z e w :=
  ((AlgebraicGeometry.SheafOfModules.stalkFunctor O z).mapIso e).toLinearEquiv.map_smul s w

/-- A map that is the composite of two maps commuting with the action of `s` does too. -/
private theorem smul_of_apply_eq_comp {R M N P : Type*} [SMul R M] [SMul R N] [SMul R P]
    {f : M → P} {u : M → N} {e : N → P} (hf : ∀ w, f w = e (u w))
    (hu : ∀ (s : R) w, u (s • w) = s • u w) (he : ∀ (s : R) y, e (s • y) = s • e y)
    (s : R) (w : M) : f (s • w) = s • f w := by
  rw [hf, hu, he, ← hf]

section Site

variable {T : TopCat.{u}}
  (A B : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (a : A ⟶ B) (z : T)

/-! ### The degree `-1` leg -/

/-- **The degree `-1` leg is linear** over the stalk of the sheaf of rings underlying `B`.  It is
the composite of a linear map (`Stacks.NaiveCotangentAffineStalkLegs.stalkAddEquivOfIso_smul`)
with `Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv`, which is linear by
`Stacks.SheafOfModules.naiveCotangentStalkCotangentEquiv_linear`. -/
theorem stalkLegNegOne_smul
    (s : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj z))
    (w : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
        (-1)).val.presheaf z)) :
    letI := algebraStalk a.hom z
    letI := moduleRingStalkCotangent A B a z
    stalkLegNegOne A B a z (s • w) = s • stalkLegNegOne A B a z w := by
  let := algebraStalk a.hom z
  let := moduleRingStalkCotangent A B a z
  exact smul_of_apply_eq_comp (stalkLegNegOne_apply A B a z)
    (stalkAddEquivOfIso_smul z _) (naiveCotangentStalkCotangentEquiv_linear A B a z) s w

/-- **The stalk of the degree `-1` term of `NL_{B/A}` is the conormal module of the canonical
presentation of `Bₓ` over `Aₓ`, as modules over the stalk of `B`.**  This is
`Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOne` with its linearity. -/
def stalkLegNegOneLinear :
    letI := algebraStalk a.hom z
    letI := moduleRingStalkCotangent A B a z
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
          (-1)).val.presheaf z)
      ≃ₗ[ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj z)]
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
        (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.Cotangent :=
  letI := algebraStalk a.hom z
  letI := moduleRingStalkCotangent A B a z
  (stalkLegNegOne A B a z).toLinearEquiv (stalkLegNegOne_smul A B a z)

/-- The linear degree `-1` leg agrees with `stalkLegNegOne` on elements. -/
theorem stalkLegNegOneLinear_apply
    (w : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
        (-1)).val.presheaf z)) :
    letI := algebraStalk a.hom z
    stalkLegNegOneLinear A B a z w = stalkLegNegOne A B a z w := rfl

/-! ### The degree `0` leg -/

/-- **The degree `0` leg is linear** over the stalk of the sheaf of rings underlying `B`. -/
theorem stalkLegZero_smul
    (s : ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj z))
    (w : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
        0).val.presheaf z)) :
    letI := algebraStalk a.hom z
    letI := moduleRingStalkCotangentSpace A B a z
    stalkLegZero A B a z (s • w) = s • stalkLegZero A B a z w := by
  let := algebraStalk a.hom z
  let := moduleRingStalkCotangentSpace A B a z
  exact smul_of_apply_eq_comp (stalkLegZero_apply A B a z)
    (stalkAddEquivOfIso_smul z _) (naiveCotangentStalkCotangentSpaceEquiv_linear A B a z) s w

/-- **The stalk of the degree `0` term of `NL_{B/A}` is the cotangent space of the canonical
presentation of `Bₓ` over `Aₓ`, as modules over the stalk of `B`.**  This is
`Stacks.NaiveCotangentAffineStalkLegs.stalkLegZero` with its linearity. -/
def stalkLegZeroLinear :
    letI := algebraStalk a.hom z
    letI := moduleRingStalkCotangentSpace A B a z
    ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
          0).val.presheaf z)
      ≃ₗ[ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B).obj z)]
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
        (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.CotangentSpace :=
  letI := algebraStalk a.hom z
  letI := moduleRingStalkCotangentSpace A B a z
  (stalkLegZero A B a z).toLinearEquiv (stalkLegZero_smul A B a z)

/-- The linear degree `0` leg agrees with `stalkLegZero` on elements. -/
theorem stalkLegZeroLinear_apply
    (w : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
        0).val.presheaf z)) :
    letI := algebraStalk a.hom z
    stalkLegZeroLinear A B a z w = stalkLegZero A B a z w := rfl

/-! ### The differential -/

/-- **Stacks 0D09 at the terms of `NL_{B/A}`, as an isomorphism of two-term complexes of modules
over the stalk of `B`.**  The two linear legs carry the stalk of the differential of `NL_{B/A}`
to the cotangent complex of `Algebra.Generators.self Aₓ Bₓ`, which is the differential of
`NL_{Bₓ/Aₓ}`.

The stalk of the differential is the image of the differential under
`AlgebraicGeometry.SheafOfModules.stalkFunctor`, hence a morphism of modules over the stalk of
the sheaf of rings underlying `B`, and the cotangent complex is linear for the same action
(`Stacks.SheafOfModules.moduleRingStalkCotangent`); so with
`Stacks.NaiveCotangentAffineStalkLegs.stalkLegNegOneLinear` and
`Stacks.NaiveCotangentAffineStalkLegs.stalkLegZeroLinear` all four maps of the square are linear
and this is an isomorphism of complexes.  The additive form is
`Stacks.NaiveCotangentAffineStalkLegs.stalkLeg_d`. -/
theorem stalkLegLinear_d
    (ω : ToType (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
      ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).X
        (-1)).val.presheaf z)) :
    letI := algebraStalk a.hom z
    letI := moduleRingStalkCotangent A B a z
    letI := moduleRingStalkCotangentSpace A B a z
    stalkLegZeroLinear A B a z
        (((AlgebraicGeometry.SheafOfModules.stalkFunctor
            (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} B) z).map
          ((naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology T) A B a).d
            (-1) 0)).hom ω) =
      (Algebra.Generators.self (ToType (TopCat.Presheaf.stalk A.obj z))
        (ToType (TopCat.Presheaf.stalk B.obj z))).toExtension.cotangentComplex
        (stalkLegNegOneLinear A B a z ω) := by
  let := algebraStalk a.hom z
  let := moduleRingStalkCotangent A B a z
  let := moduleRingStalkCotangentSpace A B a z
  let _ : DecidableEq (OrderDual (TopologicalSpace.OpenNhds z)) := Classical.decEq _
  exact stalkLeg_d A B a z ω

end Site

end Stacks.NaiveCotangentAffineStalkLegs

end

end
