module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentableULift
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Large-valued sheaves over a smaller base scheme

Let `g : V ⟶ S` be a morphism of a big fppf site. Stacks 04SG identifies algebraic spaces over
`V` with algebraic spaces over `S` equipped with a morphism to the representable algebraic space
of `V`; its presheaf-level form is `AlgebraicGeometry.smallerBasePresheafEquivalence`, for
presheaves with values in `Type u`, the universe of the schemes. Formal algebraic spaces are
sheaves with values in `Type (u + 1)` (`AlgebraicGeometry.FormalSpace.FppfSheaf`), and this file
proves the same identification for them: presheaves, and sheaves, on the big fppf site of `V`
with values in `Type (u + 1)` are the same thing as such presheaves, and sheaves, on the big fppf
site of `S` over the universe-lifted representable presheaf of `g`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.smallerBasePresheafEquivalenceULift`: the presheaf level
  equivalence, Stacks 00Y1 for the twice-localized site read through the iterated-slice
  equivalence, exactly as `AlgebraicGeometry.smallerBasePresheafEquivalence` is built.
* `AlgebraicGeometry.FormalSpace.smallerBaseSheafEquivalence`: the sheaf level equivalence
  between `AlgebraicGeometry.FormalSpace.FppfSheaf B V hV` and the presheaves on the big fppf site
  of `S` over the representable of `g` whose underlying presheaf is an fppf sheaf.

## Implementation notes

The construction is the one of `AlgebraicGeometry.smallerBasePresheafEquivalence` with the
large-valued form `CategoryTheory.OverShriek.presheafEquivalenceULift` of Stacks 00Y1 in place of
`CategoryTheory.OverShriek.presheafEquivalence`; the latter is stated for presheaves with values in
the universe of the morphisms of the site, which is `Type u` here, so it cannot be applied to
`Type (u + 1)` directly. The sheaf level statement is Mathlib's
`CategoryTheory.Equivalence.sheafCongr` for the iterated-slice equivalence, which is a dense
subsite equivalence for the localized topologies, followed by
`CategoryTheory.OverShriek.sheafEquivalenceULift`; the universe-lifted representable presheaf is a
sheaf because the big fppf topology is subcanonical.

## References

* [Stacks Project, Tag 00Y1](https://stacks.math.columbia.edu/tag/00Y1)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (V S : Scheme.{u}) (hV : B.Contains V) (hS : B.Contains S)
  (g : B.obj hV ⟶ B.obj hS)

/-- Presheaves with values in `Type (u + 1)` on the big fppf site of `V` are the same thing as
such presheaves on the big fppf site of `S` over the universe-lifted representable presheaf of
`g : V ⟶ S`: the iterated-slice equivalence identifies the big fppf site of `V` with the slice of
the big fppf site of `S` over `g`, and Stacks 00Y1, in its large-valued form, identifies
presheaves on that slice with presheaves over the representable presheaf. -/
@[sga "3 I 1.4.1" "special case", sga "3 IV 4.5.2" "special case"]
noncomputable def smallerBasePresheafEquivalenceULift :
    ((BigFppfOver B V hV)ᵒᵖ ⥤ Type (u + 1)) ≌
      Over ((uliftYoneda.{u + 1}).obj (Over.mk g) : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) :=
  ((Over.iteratedSliceEquiv (Over.mk g)).op.congrLeft (E := Type (u + 1))).symm.trans
    (OverShriek.presheafEquivalenceULift.{u + 1} (U := Over.mk g))

/-- The universe-lifted representable presheaf of an object of the big fppf site of `S` is an
fppf sheaf, the big fppf topology being subcanonical. -/
theorem isSheaf_uliftYoneda (T : BigFppfOver B S hS) :
    Presieve.IsSheaf (BigFppfOver.topology B S hS) ((uliftYoneda.{u + 1}).obj T) := by
  let _ : (BigFppfOver.topology B S hS).Subcanonical := bigFppfOver_subcanonical B S hS
  exact GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := BigFppfOver.topology B S hS) ((uliftYoneda.{u + 1}).obj T)

/-- The presheaves on the big fppf site of `S` over the universe-lifted representable presheaf of
`g : V ⟶ S` whose underlying presheaf is an fppf sheaf. -/
abbrev SheavesOverSmallerBase : Type (u + 2) :=
  (OverShriek.IsSheafLeft.{u + 1} (U := Over.mk g) (BigFppfOver.topology B S hS)).FullSubcategory

/-- **Large-valued sheaves over a smaller base.** Fppf sheaves with values in `Type (u + 1)` on the
big fppf site of `V` — the ambient category of formal algebraic spaces over `V` — are the same
thing as fppf sheaves with values in `Type (u + 1)` on the big fppf site of `S` equipped with a
morphism to the universe-lifted representable presheaf of `g : V ⟶ S`. -/
noncomputable def smallerBaseSheafEquivalence :
    FppfSheaf B V hV ≌ SheavesOverSmallerBase B V S hV hS g :=
  (Equivalence.sheafCongr ((B.topology.over (B.obj hS)).over (Over.mk g))
      (B.topology.over (Over.mk g).left) (Over.iteratedSliceEquiv (Over.mk g))
      (Type (u + 1))).symm.trans
    (OverShriek.sheafEquivalenceULift.{u + 1} (BigFppfOver.topology B S hS)
      (isSheaf_uliftYoneda B S hS (Over.mk g)))

end AlgebraicGeometry.FormalSpace

end
