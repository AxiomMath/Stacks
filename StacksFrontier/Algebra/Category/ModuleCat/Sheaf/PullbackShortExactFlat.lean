module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsShortExactFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackFlatInverseImage
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposInverseImageExact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.ExactnessOfPullback
import StacksCore.Tactic.StacksAttribute

/-! # Stacks 0G6R: pullback of a short exact sequence with flat quotient

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and let

`0 → F → G → H → 0`

be a short exact sequence of sheaves of `O_D`-modules with `H` flat.  **Stacks 0G6R** asserts
that `0 → f^*F → f^*G → f^*H → 0` is short exact as well.

## The argument

The source's proof is the factorization of the pullback of Stacks 03D6 part (2) into the
inverse image with no change of rings followed by extension of scalars,

`f^*G = O_C ⊗_{f⁻¹O_D} f⁻¹G`,

and three statements about the two factors:

* `f⁻¹` is exact, so `0 → f⁻¹F → f⁻¹G → f⁻¹H → 0` is a short exact sequence of
  `f⁻¹O_D`-modules.  This is Stacks 04JC at module level,
  `Stacks.Sheaves.RingedToposModules.shortExact_map_inverseImageModules`.
* `f⁻¹H` is a flat `f⁻¹O_D`-module.  This is the half of Stacks 05VD that the source gets from
  Stacks 03CR, `Stacks.Sheaves.RingedToposModules.isFlat_inverseImageModules_of_isFlat`.
* extension of scalars along `f♯ : f⁻¹O_D ⟶ O_C` keeps a short exact sequence with flat third
  term short exact.  This is Stacks 03EX for change of rings,
  `Stacks.Sheaves.ChangeOfRings.shortExact_map_changeOfRings`.

All three are unconditional, so Stacks 0G6R is too.

## Main results

* `Stacks.Sheaves.RingedToposModules.shortExact_map_extendScalarsFSharp`: Stacks 03EX for the
  extension of scalars along the structure map of a morphism of ringed topoi.
* `Stacks.Sheaves.RingedToposModules.shortExact_map_pullbackModules`: **Stacks 0G6R.**

## Implementation notes

**Why this is not conditional, where the earlier reduction was.**
`Stacks.Sheaves.InverseImageExactness.pullbackPreservesShortExact_of_univ` derives Stacks 0G6R
from two statements it leaves open, one of them exactness of the module inverse image.  That
reduction is written for `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`, which is
Mathlib's pullback of sheaves of modules, defined as an abstract left adjoint; identifying its
geometric factor with the inverse image of sheaves of sets is a Beck--Chevalley comparison and
is not formal.  The pullback used here is the one of Stacks 03D6 part (2),
`Stacks.Sheaves.RingedToposModules.pullbackModules`, which is *constructed* from the inverse
image of Stacks 03D2 by transporting the module structure along `f⁻¹` of the underlying sheaf
of sets.  For that pullback the comparison is definitional, which is exactly what makes
`Stacks.Sheaves.RingedToposModules.inverseImageModuleSheafIso` the identity in
each component and the exactness of the module inverse image a theorem rather than a
hypothesis.

**Universes.**  The two ringed topoi are at the shape forced by Stacks 05VD: writing
`RingedTopos.{v₁, u₁, w₁}` for morphisms, objects and sections, the target is
`RingedTopos.{v', u', max u' v'}` and the source is `RingedTopos.{v, max u v, max u v}`.  The
narrowing is inherited from `isFlat_inverseImageModules_of_isFlat`, whose own forcings are
recorded in `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackFlatInverseImage.lean`; the
change-of-rings step adds none of its own, being stated for a site whose object and section
universes agree, which the source already satisfies.  Nothing else here constrains them: the
exactness of the inverse image holds at wholly independent universes.

## References

* [Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u w v' u' w'

namespace Stacks.Sheaves.RingedToposModules

open Stacks.Sheaves.ToposPushforward (inverseImageRingSheaf)

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasSheafify X.J AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w'}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')]
  (f : RingedToposHom X Y)

/-- Extension of scalars along the structure map of a morphism of ringed topoi is additive.  It
is the change-of-rings functor of Stacks 03CZ for the comm-ring-sheaf form of `f♯`
(`extendScalarsFSharp_eq_changeOfRings`), which is additive because its composite with the
underlying-abelian-sheaf functor is a tensor product.  Without this the statements below cannot
be written: `ShortComplex.map` asks the functor to preserve zero morphisms. -/
instance extendScalarsFSharp_additive : (extendScalarsFSharp f).Additive := by
  rw [extendScalarsFSharp_eq_changeOfRings f]
  exact Stacks.FlatChangeOfRings.extendScalars_additive (fSharpCommRingSheaf f)

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  [HasSheafify Y.J AddCommGrpCat] [HasSheafify X.J (Type w)] [HasSheafify Y.J (Type w')] in
/-- **Stacks Project, Tag 03EX for the structure map of a morphism of ringed topoi.**
Extension of scalars along `f♯ : f⁻¹O_D ⟶ O_C` carries a short exact sequence of sheaves of
`f⁻¹O_D`-modules whose third term is flat to a short exact sequence of sheaves of
`O_C`-modules.

This is `Stacks.Sheaves.ChangeOfRings.shortExact_map_changeOfRings` read through
`extendScalarsFSharp_eq_changeOfRings`, which says the two spellings of extension of scalars
along `f♯` are the same functor. -/
theorem shortExact_map_extendScalarsFSharp
    (T : ShortComplex (SheafOfModules.{w}
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))))
    (hT : T.ShortExact)
    (hflat : Stacks.SheafOfModules.IsFlat (O := inverseImageStructureCommRingSheaf f) T.X₃) :
    (T.map (extendScalarsFSharp f)).ShortExact :=
  Stacks.FlatChangeOfRings.shortExact_map_extendScalars (fSharpCommRingSheaf f) T hT hflat

/-- **Stacks Project, Tag 0G6R.**  Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of
ringed topoi and let `0 → F → G → H → 0` be a short exact sequence of sheaves of `O_D`-modules
with `H` a flat `O_D`-module.  Then `0 → f^*F → f^*G → f^*H → 0` is short exact.

The pullback of Stacks 03D6 part (2) is the inverse image of Stacks 03D2 followed by extension
of scalars along `f♯`.  The inverse image is exact (Stacks 04JC) and carries `H` to a flat
`f⁻¹O_D`-module (Stacks 05VD), and extension of scalars keeps a short exact sequence with flat
third term short exact (Stacks 03EX). -/
@[stacks 0G6R, ega "IV 2.1.8" "(i), G' = O_{Y'}"]
theorem shortExact_map_pullbackModules
    (S : ShortComplex (SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hS : S.ShortExact)
    (hflat : Stacks.SheafOfModules.IsFlat (O := Y.O) S.X₃) :
    (S.map (f.pullbackModules)).ShortExact :=
  shortExact_map_extendScalarsFSharp f
    (S.map (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (shortExact_map_inverseImageModules f.toToposHom
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) S hS)
    (isFlat_inverseImageModules_of_isFlat f S.X₃ hflat)

end Stacks.Sheaves.RingedToposModules

end
