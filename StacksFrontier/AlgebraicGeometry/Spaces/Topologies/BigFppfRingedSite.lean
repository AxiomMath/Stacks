module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfStructureSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# The big fppf site of an algebraic space as a ringed site

The big fppf site of an algebraic space `X` of a big fppf site of algebraic spaces carries the
sheaf of global regular functions, so it is a ringed site. This file packages that datum, the
associated sheaf of rings, and the category of sheaves of `𝒪_X`-modules on it.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.bigFppfRingedSite`: the big fppf site of `X` with its
  sheaf of global regular functions, as a ringed site.
* `AlgebraicGeometry.BigFppfSpaceSite.bigFppfRingSheaf`: the structure sheaf with its
  commutativity forgotten, as a sheaf of rings.
* `AlgebraicGeometry.BigFppfSpaceSite.BigFppfModules`: sheaves of `𝒪_X`-modules on the big
  fppf site of `X`.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
* [Stacks Project, Tag 0DBW](https://stacks.math.columbia.edu/tag/0DBW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S)

/-- The big fppf site of an algebraic space `X` of the site, together with its sheaf of global
regular functions, as a ringed site. -/
abbrev bigFppfRingedSite (X : T.Spaces) : RingedSite.{u + 1, u + 1, u + 1} where
  C := BigFppfSpaceOver T X
  J := BigFppfSpaceOver.topology T X
  O := T.structureSheaf X

/-- Composing with the forgetful functor from commutative rings to rings preserves sheaves on
the big fppf site of `X`. -/
instance hasSheafCompose_bigFppf (X : T.Spaces) :
    (BigFppfSpaceOver.topology T X).HasSheafCompose
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) :=
  (bigFppfRingedSite T X).hasSheafCompose_forget₂_ringCat

/-- The presheaf of rings of global regular functions on the algebraic spaces of the site: the
presheaf of commutative rings of global regular functions with its commutativity forgotten. -/
abbrev globalRingPresheaf : T.Spacesᵒᵖ ⥤ RingCat.{u + 1} :=
  Space.globalFunctionsPresheaf T.schemeSite S T.scheme_mem ⋙
    forget₂ CommRingCat.{u + 1} RingCat.{u + 1}

/-- The sheaf of rings of global regular functions on the big fppf site of `X`. -/
abbrev bigFppfRingSheaf (X : T.Spaces) :
    Sheaf (BigFppfSpaceOver.topology T X) RingCat.{u + 1} :=
  (Stacks.SheafOfModules.Tensor.ringSheaf (bigFppfRingedSite T X).O)

/-- Sheaves of `𝒪_X`-modules on the big fppf site of `X`. -/
abbrev BigFppfModules (X : T.Spaces) := SheafOfModules.{m} (bigFppfRingSheaf T X)

end AlgebraicGeometry.BigFppfSpaceSite

end
