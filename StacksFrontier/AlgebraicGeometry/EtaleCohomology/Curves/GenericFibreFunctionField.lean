module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibreStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.OrderOfVanishingPointHom

/-!
# A function on the generic fibre is a rational function, and its orders of vanishing

Let `X` be an irreducible scheme with generic point `η` and function field `K`, let
`j : Spec K ⟶ X` be the inclusion of the generic point, and let `g : U ⟶ X` be flat with `U`
irreducible. The sections of `j_* 𝐆_{m,K}` over `U` are the invertible global functions on the
generic fibre `U ×_X Spec K`, and the second map of the divisor sequence of Stacks 03RI takes
such a section to its orders of vanishing at the points of `U`. For that to mean anything the
invertible function on the generic fibre must first be read as a rational function on `U`.

It can be. The generic fibre carries a unique point over the generic point of `U`
(`Stacks.EtaleCohomology.genericFibrePoint`), and the projection `U ×_X Spec K ⟶ U` induces an
isomorphism of local rings there, so the germ at that point of a global function on the generic
fibre is an element of `K(U)`. The resulting ring homomorphism
`Stacks.EtaleCohomology.genericFibreToFunctionField` restricts along the projection to the germ
at the generic point, which is the compatibility the divisor sequence needs: a function on `U`
that is already invertible has no zeros and no poles, so the composite of the first two maps of
the sequence is zero.

## Main definitions

* `Stacks.EtaleCohomology.genericFibrePoint`: the unique point of the generic fibre of a flat
  morphism from an irreducible scheme lying over the generic point of the source.
* `Stacks.EtaleCohomology.genericFibreToFunctionField`: **a global function on the generic fibre,
  read as a rational function on `U`.**
* `Stacks.EtaleCohomology.genericFibreOrd`: the order of vanishing at a point of `U` of an
  invertible global function on the generic fibre, as a homomorphism of abelian groups.

## Main results

* `Stacks.EtaleCohomology.appTop_genericFibreToFunctionField`: the comparison restricts along the
  projection to the germ at the generic point.
* `Stacks.EtaleCohomology.genericFibreOrd_restrict_eq_zero`: **an invertible global function on
  `U` has order of vanishing zero at every point** — the composite of the first two maps of the
  divisor sequence of Stacks 03RI, read on sections over `U`.
* `Stacks.EtaleCohomology.finite_support_genericFibreOrd`: the orders of vanishing of a section
  are nonzero at only finitely many points, which is what makes the family of them a section of
  the coproduct `⨁_x i_{x,*} ℤ`.

## Implementation notes

The hypotheses are flatness of `g` and irreducibility of `U`, not étaleness and not a curve:
lifting the generalization to the generic point is all the argument uses. Irreducibility of `U`
is what makes `U` have a function field at all; for a general étale `X`-scheme the generic fibre
meets each irreducible component in its generic point, by
`Stacks.EtaleCohomology.exists_pullback_genericPointInclusion_eq_of_mem_irreducibleComponents`,
and this file is the irreducible piece of that decomposition.

The transport of the local ring along the equality of points is
`TopCat.Presheaf.stalkCongr`, which on germs is `TopCat.Presheaf.germ_stalkSpecializes`; this is
why the comparison is pinned down by its restriction along the projection rather than merely
asserted to exist.

## References

* [Stacks Project, Tag 03RI](https://stacks.math.columbia.edu/tag/03RI): the fundamental exact
  sequence, whose second map is the order of vanishing at the closed points.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section Comparison

variable {X U : Scheme.{u}} [IrreducibleSpace X] [IrreducibleSpace U] (g : U ⟶ X) [Flat g]

/-- **The generic point of the source of a flat morphism to an irreducible scheme lies over the
generic point of the target.** The whole space is the only irreducible component. -/
theorem base_genericPoint_eq_genericPoint_of_flat : g.base (genericPoint U) = genericPoint X :=
  base_eq_genericPoint_of_closure_mem_irreducibleComponents g
    (by simp [irreducibleComponents_eq_singleton, (genericPoint_spec U).def])

/-- The generic fibre of a flat morphism from an irreducible scheme carries a point over the
generic point of the source. -/
theorem exists_fst_base_eq_genericPoint :
    ∃ z : ↥(pullback g (genericPointInclusion X)),
      (pullback.fst g (genericPointInclusion X)).base z = genericPoint U := by
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g)
    (g := genericPointInclusion X) (genericPoint U)
    (IsLocalRing.closedPoint X.functionField)
    ((base_genericPoint_eq_genericPoint_of_flat g).trans (genericPointInclusion_base X _).symm)
  exact ⟨z, hz⟩

/-- **The unique point of the generic fibre lying over the generic point of `U`.** The projection
from the generic fibre is injective on points, so this is well defined by
`Stacks.EtaleCohomology.eq_genericFibrePoint`. -/
def genericFibrePoint : ↥(pullback g (genericPointInclusion X)) :=
  (exists_fst_base_eq_genericPoint g).choose

/-- The generic fibre point lies over the generic point of `U`. -/
@[simp]
theorem fst_base_genericFibrePoint :
    (pullback.fst g (genericPointInclusion X)).base (genericFibrePoint g) = genericPoint U :=
  (exists_fst_base_eq_genericPoint g).choose_spec

/-- A point of the generic fibre lying over the generic point of `U` is *the* generic fibre
point. -/
theorem eq_genericFibrePoint {z : ↥(pullback g (genericPointInclusion X))}
    (hz : (pullback.fst g (genericPointInclusion X)).base z = genericPoint U) :
    z = genericFibrePoint g :=
  injective_base_pullback_fst_genericPointInclusion X g
    (hz.trans (fst_base_genericFibrePoint g).symm)

/-- **A global function on the generic fibre, read as a rational function on `U`**: its germ at
the generic fibre point, carried across the isomorphism of local rings induced there by the
projection `U ×_X Spec K ⟶ U`. -/
def genericFibreToFunctionField :
    Γ(pullback g (genericPointInclusion X), ⊤) ⟶ U.functionField :=
  have := isIso_stalkMap_pullback_fst_genericPointInclusion X g (genericFibrePoint g)
  (pullback g (genericPointInclusion X)).presheaf.germ ⊤ (genericFibrePoint g) trivial ≫
    inv ((pullback.fst g (genericPointInclusion X)).stalkMap (genericFibrePoint g)) ≫
      (U.presheaf.stalkCongr (Inseparable.of_eq (fst_base_genericFibrePoint g))).hom

/-- **The comparison restricts along the projection to the germ at the generic point.** A global
function on `U` restricted to the generic fibre is, as a rational function on `U`, its own germ
at the generic point. This equation pins the comparison down. -/
theorem appTop_genericFibreToFunctionField :
    (pullback.fst g (genericPointInclusion X)).appTop ≫ genericFibreToFunctionField g =
      U.presheaf.germ ⊤ (genericPoint U) trivial := by
  have := isIso_stalkMap_pullback_fst_genericPointInclusion X g (genericFibrePoint g)
  have hg : ((pullback.fst g (genericPointInclusion X)).appTop ≫
        (pullback g (genericPointInclusion X)).presheaf.germ ⊤ (genericFibrePoint g) trivial) ≫
          inv ((pullback.fst g (genericPointInclusion X)).stalkMap (genericFibrePoint g)) =
      U.presheaf.germ ⊤
        ((pullback.fst g (genericPointInclusion X)).base (genericFibrePoint g)) trivial := by
    rw [IsIso.comp_inv_eq]
    exact (Scheme.Hom.germ_stalkMap (pullback.fst g (genericPointInclusion X)) ⊤
      (genericFibrePoint g) trivial).symm
  rw [genericFibreToFunctionField, ← Category.assoc, ← Category.assoc, hg]
  exact (U.presheaf.germ_stalkSpecializes (U := ⊤) trivial
    (Inseparable.of_eq (fst_base_genericFibrePoint g)).symm.specializes)

end Comparison

section Ord

variable {X U : Scheme.{u}} [IrreducibleSpace X] [IsIntegral U] [IsLocallyNoetherian U]
  (g : U ⟶ X) [Flat g]

/-- **The order of vanishing at a point of `U` of an invertible global function on the generic
fibre of `g`**, as a homomorphism of abelian groups: the function is read as a rational function
on `U` by `Stacks.EtaleCohomology.genericFibreToFunctionField` and its order of vanishing taken
there. -/
def genericFibreOrd (y : U) :
    Additive ((Γ(pullback g (genericPointInclusion X), ⊤))ˣ) →+ ℤ :=
  (Scheme.ordAddMonoidHom y).comp
    (MonoidHom.toAdditive (Units.map (genericFibreToFunctionField g).hom.toMonoidHom))

/-- `Stacks.EtaleCohomology.genericFibreOrd g y` sends a unit to the order of vanishing at `y` of
its image under `Stacks.EtaleCohomology.genericFibreToFunctionField g`. -/
@[simp]
theorem genericFibreOrd_apply (y : U)
    (a : Additive ((Γ(pullback g (genericPointInclusion X), ⊤))ˣ)) :
    genericFibreOrd g y a =
      Scheme.ord (genericFibreToFunctionField g ((Additive.toMul a : _ˣ) : _)) y :=
  rfl

/-- **An invertible global function on `U` has order of vanishing zero at every point of `U`.**
Restricted to the generic fibre it is still invertible, and as a rational function on `U` it is
the germ of an invertible global function, which has neither zeros nor poles.

This is the statement that the composite of the first two maps of the divisor sequence of
Stacks 03RI vanishes, read on sections over `U`. -/
theorem genericFibreOrd_restrict_eq_zero (y : U) (a : (Γ(U, ⊤))ˣ) :
    genericFibreOrd g y (Additive.ofMul
      (Units.map (pullback.fst g (genericPointInclusion X)).appTop.hom.toMonoidHom a)) = 0 := by
  have : Nonempty ↥(⊤ : U.Opens) := ⟨⟨genericPoint U, trivial⟩⟩
  have h : genericFibreToFunctionField g
      ((pullback.fst g (genericPointInclusion X)).appTop (a : Γ(U, ⊤))) =
      U.presheaf.germ ⊤ (genericPoint U) trivial (a : Γ(U, ⊤)) :=
    congrArg (fun φ => (CommRingCat.Hom.hom φ) (a : Γ(U, ⊤)))
      (appTop_genericFibreToFunctionField g)
  rw [genericFibreOrd_apply]
  simpa [h] using
    @Scheme.ord_of_isUnit U _ _ ⊤ ⟨⟨genericPoint U, trivial⟩⟩ _ a.isUnit y trivial

/-- **The orders of vanishing of a section are nonzero at only finitely many points of `U`.**
This is the finiteness that makes the family of components of the second map of the divisor
sequence of Stacks 03RI a section of the coproduct `⨁_x i_{x,*} ℤ`. -/
theorem finite_support_genericFibreOrd [NoetherianSpace U]
    (a : Additive ((Γ(pullback g (genericPointInclusion X), ⊤))ˣ)) :
    {y : U | genericFibreOrd g y a ≠ 0}.Finite := by
  simpa only [genericFibreOrd_apply] using Scheme.finite_support_ord (X := U)
    (genericFibreToFunctionField g ((Additive.toMul a : _ˣ) : _))

end Ord

end Stacks.EtaleCohomology

end
