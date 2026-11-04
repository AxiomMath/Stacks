module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedTopos
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite

/-!
# Morphisms of ringed topoi

A *morphism of ringed topoi* `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` is a morphism of the
underlying topoi together with a map `f♯ : O_D ⟶ f_*O_C` of the structure sheaves. Since a
`AlgebraicGeometry.RingedTopos` carries its structure sheaf as an object of
`Sheaf J CommRingCat`, the structure map is a morphism of sheaves of commutative rings, and the
direct image it is taken into is `Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor`.

No ring lift and no adjunction are additional data: the inverse-image form
`f⁻¹O_D ⟶ O_C` of the structure map is *derived* from `f♯` through the adjunction
`Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`, and
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv` records that on underlying
sheaves of sets it is the adjunct of the underlying map of `f♯`.

## Main definitions

* `AlgebraicGeometry.RingedToposHom`: a morphism of ringed topoi.
* `AlgebraicGeometry.RingedToposHom.fSharpInverseImage`: the inverse-image form `f⁻¹O_D ⟶ O_C`
  of the structure map.

## Main results

* `AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv` (proved in
  `StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget`, not here): on
  underlying sheaves of sets, the inverse-image form of the structure map is the adjunct, under
  `f⁻¹ ⊣ f_*` for sheaves of sets, of the underlying map of `f♯`. It is named `_forget` rather
  than `_hom` because in this repository `_hom` denotes an iso's `.hom` component.

Composition of morphisms of ringed topoi — Stacks 01D3 part (3) — is
`AlgebraicGeometry.RingedToposHom.comp`, in
`StacksFrontier/Deformation/ToposThickening/Trivialization/RingedToposComp.lean`; it is downstream
because the canonical identification `g_*f_*O ≅ (g ∘ f)_*O` of iterated direct images is proved
there.

## Implementation notes

**Two other things in this development are called `RingedToposHom`, and neither is this one.**

* `Stacks.Sheaves.RingedToposModules.RingedToposHom`
  (`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/RingedToposModules.lean`) has four fields and
  its structure map lives at the `RingCat` level,
  `Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶ pushforwardRingSheaf
  toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf X.O)`; it stores the inverse-image form as
  a *field* together with the equation making the two adjunct. That is the right shape for the
  modules development, which needs both forms of the structure map at the ring level and wants them
  available without unfolding an adjunction, and which *chooses* the inverse-image form on the
  nose — `Stacks.Sheaves.RingedPoint` and
  `Stacks.Sites.FibredCategory.FibredCategorySituation.ringedProjection` both take it to be
  `𝟙 _` and state `rfl`-level lemmas about that choice. So the two structures are
  both needed and neither replaces the other.

  It is *not*, however, a stronger datum, and a statement quantifying over the one can be
  re-read as a statement quantifying over the other: its two extra fields are the adjunct of
  `fSharp` under `commRingImageAdjunction` and the proof that it is that adjunct, which are
  exactly `AlgebraicGeometry.RingedToposHom.fSharpInverseImage` and
  `AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget_homEquiv`. The resulting passage
  from the two-field structure to the four-field one is
  `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`
  (`StacksFrontier/CategoryTheory/Sites/RingedLocalization/RingedToposHomModules.lean`), and it is
  what lets the pushforward and pullback of modules of Stacks 03D6 and the adjunction of
  Stacks 03D7 be applied to a morphism of ringed topoi in the sense of Stacks 01D3 — in
  particular to `AlgebraicGeometry.Space.smallEtaleRingedToposHom`, which is what Stacks 03LU
  needs.

  There is also a passage in the other direction, even though the four-field structure's
  inverse-image form is not a priori the adjunct of a `CommRingCat`-level `fSharp`: the two
  structures are in fact equivalent. The reverse map is
  ```
  toToposHom := k.toToposHom
  fSharp := (Stacks.Sheaves.ToposPullback.fullyFaithfulForgetCommRingSheaf Y.J).preimage k.fSharp
  ```
  which typechecks because `forget₂ CommRingCat RingCat` is fully faithful on sheaves and the
  target types agree on the nose, so `fSharp` always has a unique `CommRingCat` preimage; and
  then `fSharp_adjunct` together with faithfulness of `sheafCompose (forget RingCat)` forces
  the four-field structure's `fSharpInverseImage` to be the derived adjunct after all. So the
  extra two fields carry no information, which is a *stronger* statement than the note it
  replaces, not a weaker one. (The reverse map is known to exist; that the round trip is the
  identity has not been proved.)
* `Stacks.Sheaves.LocallyRingedTopos.RingedToposHom`, the structure of Stacks Tag 04H9, has ten
  fields and carries the lift of `f⁻¹` to sheaves of rings, the identification
  `f⁻¹(O_D^*) ≅ (f⁻¹O_D)^*` and their compatibilities as *data and axioms*. That is what lets
  the Stacks 04H9 development state its cartesian squares with named corners. It assumes the
  units identification, which is the very thing Stacks 04HA sets out to exhibit, so it cannot
  be used to state 04HA.

This structure is the canonical two-field one that Stacks 01D3 part (2) defines, and it is what
Stacks 04H7 and 04HA quantify over. Its absence is the reason the other two had to be
introduced; adding it reduces the duplication rather than adding to it.

The four `GrothendieckTopology.HasSheafCompose` hypotheses are those of
`commRingImageAdjunction`, which is what makes `pushforwardCommRingFunctor` and
`inverseImageCommRingFunctor` available; they are not derived, for the reason recorded in
`Stacks.Sheaves.ToposPushforward.forgetCommRingSheaf`.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe v u w v' u' w'

namespace AlgebraicGeometry

/-- **Stacks 01D3, part (2).** A morphism of ringed topoi: a morphism of the underlying topoi
together with a map from the structure sheaf of the target to the direct image of the structure
sheaf of the source. -/
@[stacks 01D3 "part (2): morphisms of ringed topoi",
  sga "4 Vbis 1.3.2" "absolute case (D = pt)",
  sga "4 IV 13.1"]
structure RingedToposHom (X : RingedTopos.{v, u, w}) (Y : RingedTopos.{v', u', w'})
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})] where
  /-- The underlying morphism of topoi. -/
  toToposHom : MorphismOfTopoi X.Topos Y.Topos
  /-- The direct-image form of the structure morphism, `f♯ : O_D ⟶ f_*O_C`. -/
  fSharp : Y.O ⟶ (pushforwardCommRingFunctor toToposHom).obj X.O

namespace RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  (f : RingedToposHom X Y)

/-- The inverse-image form `f⁻¹O_D ⟶ O_C` of the structure map, obtained from `f♯` through the
adjunction between the inverse image and the direct image of sheaves of commutative rings. -/
noncomputable def fSharpInverseImage :
    (inverseImageCommRingFunctor f.toToposHom).obj Y.O ⟶ X.O :=
  ((commRingImageAdjunction f.toToposHom).homEquiv Y.O X.O).symm f.fSharp

end RingedToposHom

end AlgebraicGeometry
