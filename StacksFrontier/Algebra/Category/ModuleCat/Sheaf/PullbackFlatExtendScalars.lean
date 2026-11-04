module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatChangeOfRings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposCommRingImageAdjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
import StacksCore.Tactic.StacksAttribute

/-! # Flatness of a pullback: the extension-of-scalars half

Let `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and let `G` be a
sheaf of `O_D`-modules. Stacks 05VD asserts that `f^*G` is a flat `O_C`-module whenever `G` is
a flat `O_D`-module, and its proof in the source splits along the definition of the pullback
(Stacks 03D6, part (2)),

`f^*G = O_C ⊗_{f⁻¹O_D} f⁻¹G`,

into two independent steps: that `f⁻¹G` is a flat `f⁻¹O_D`-module, and that extension of
scalars preserves flatness (Stacks 05V4). This file carries out the **second** step at the
pullback, so that what remains of Stacks 05VD is exactly the first.

The mathematics of Stacks 05V4 is already formalized, as
`Stacks.FlatChangeOfRings.isFlat_extendScalars`, for the extension-of-scalars
functor `Stacks.Sheaves.ChangeOfRings.changeOfRings` of a morphism of sheaves of commutative
rings on a fixed site. The pullback of Stacks 03D6 is built instead from
`Stacks.Sheaves.RingedToposModules.extendScalarsFSharp`, which takes the structure map as a
morphism of *presheaves* of commutative rings together with sheaf conditions on the underlying
presheaves of rings. The two functors are the same functor — both are the objectwise tensor
product of Tag 03CU followed by sheafification — and this file records that identity and reads
Stacks 05V4 off through it.

## Main definitions

* `Stacks.Sheaves.RingedToposModules.inverseImageStructureCommRingSheaf`: `f⁻¹O_D`, as a sheaf
  of commutative rings on the source site. Flatness of a sheaf of modules is indexed by a sheaf
  of commutative rings, so this is what lets flatness over `f⁻¹O_D` be stated at all.
* `Stacks.Sheaves.RingedToposModules.fSharpCommRingSheaf`: the inverse-image form
  `f⁻¹O_D ⟶ O_C` of the structure map, read as a morphism of sheaves of commutative rings.

## Main results

* `Stacks.Sheaves.RingedToposModules.extendScalarsFSharp_eq_changeOfRings`: the two spellings
  of extension of scalars along `f♯` agree, by `rfl`.
* `Stacks.Sheaves.RingedToposModules.isFlat_extendScalarsFSharp`: **Stacks 05V4** for the
  extension of scalars along the structure map of a morphism of ringed topoi.
* `Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules_of_isFlat_inverseImageModules`:
  **the reduction of Stacks 05VD to its inverse-image half.** If `f⁻¹G` is flat over `f⁻¹O_D`
  then `f^*G` is flat over `O_C`.

## Implementation notes

Nothing here carries `@[stacks 05VD]`: the inverse-image half is not proved, so the tag would
be premature. The tag `05V4` is likewise left where it is proved, on
`isFlat_changeOfRings`; `isFlat_extendScalarsFSharp` is a re-spelling of it and not a second
proof.

**Every identification below is `rfl`, and that was checked before anything was written.**
Three crossings occur, and none of them needs a bridge:

* `Stacks.commRingSheafToRingSheaf (inverseImageStructureCommRingSheaf f)` and
  `Stacks.Sheaves.ToposPushforward.inverseImageRingSheaf f.toToposHom
  (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)`
  are the same sheaf of rings: the first is `sheafCompose` applied to the inverse-image sheaf
  of commutative rings, whose underlying presheaf of rings *is* the inverse-image presheaf of
  rings (`ringPresheaf_inverseImageCommRingSheaf`), and the two sheaf conditions are proofs of
  one proposition.
* `Stacks.commRingSheafToRingSheaf X.O` and `Stacks.SheafOfModules.Tensor.ringSheaf X.O` are
  the same abbreviation.
* `extendScalarsFSharp f` and `Stacks.Sheaves.ChangeOfRings.changeOfRings X.J` of the
  comm-ring-sheaf form of `f♯` unfold to the same composite.

**Universes.** Both ringed topoi keep all three of their universes free and independent:
`X : RingedTopos.{v, u, w}` and `Y : RingedTopos.{v', u', w'}`, the five parameters of Tag
05VD. The source is not pinned to `RingedTopos.{v, u, u}`: its ring and module universe need not
equal the universe of the objects of its site, and
`Stacks.Sheaves.RingedToposModules.isFlat_pullbackModules_maxSectionUniverse` applies the whole
chain at `RingedTopos.{v, u, max u v}` with the object universe free. What is assumed instead is
the `variable` block's sheafification typeclasses; see that declaration for which Mathlib
instance supplies each, and for the one — `HasWeakSheafify _ AddCommGrpCat.{w}` — whose
availability does constrain `w`.

## References

* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 05V4](https://stacks.math.columbia.edu/tag/05V4)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPushforward (inverseImageRingSheaf)

universe v u w v' u' w'

namespace Stacks.Sheaves.RingedToposModules

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  (f : RingedToposHom X Y)

/-- The inverse image `f⁻¹O_D` of the structure sheaf of the target, as a sheaf of commutative
rings on the source site. Its underlying sheaf of rings is the inverse-image sheaf of rings of
Stacks 03D2. -/
abbrev inverseImageStructureCommRingSheaf : Sheaf X.J CommRingCat.{w} :=
  Stacks.Sheaves.ToposPullback.pullbackCommRingSheaf X.J f.toToposHom.inverseImage Y.O

/-- The sheaf of rings underlying `f⁻¹O_D` read as a sheaf of commutative rings is the
inverse-image sheaf of rings, on the nose. -/
lemma commRingSheafToRingSheaf_inverseImageStructureCommRingSheaf :
    Stacks.commRingSheafToRingSheaf (inverseImageStructureCommRingSheaf f) =
      inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) :=
  rfl

/-- The inverse-image form `f⁻¹O_D ⟶ O_C` of the structure map of a morphism of ringed topoi,
read as a morphism of sheaves of commutative rings. -/
@[sga "6 0 4.4"]
def fSharpCommRingSheaf : inverseImageStructureCommRingSheaf f ⟶ X.O :=
  ⟨fSharpCommRing f⟩

variable [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Extension of scalars along the inverse-image form of the structure map, as used in the
definition of the pullback of sheaves of modules, is the change-of-rings functor of Stacks 03CZ
for the comm-ring-sheaf form of that map. Both are the objectwise tensor product of Tag 03CU
followed by sheafification, so the identity holds by `rfl`; it is recorded because the two
spellings carry their structure map in different shapes, and Stacks 05V4 is proved for the
second. -/
lemma extendScalarsFSharp_eq_changeOfRings :
    extendScalarsFSharp f =
      Stacks.FlatChangeOfRings.extendScalars (fSharpCommRingSheaf f) :=
  rfl

/-- **Stacks Project, Tag 05V4**, for the structure map of a morphism of ringed topoi:
extension of scalars along `f♯ : f⁻¹O_D ⟶ O_C` takes a flat `f⁻¹O_D`-module to a flat
`O_C`-module.

This is `Stacks.FlatChangeOfRings.isFlat_extendScalars` read through
`extendScalarsFSharp_eq_changeOfRings`; the proof of Tag 05V4 is there, not here. -/
theorem isFlat_extendScalarsFSharp
    (G : _root_.SheafOfModules.{w}
      (inverseImageRingSheaf f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hG : Stacks.SheafOfModules.IsFlat (O := inverseImageStructureCommRingSheaf f) G) :
    Stacks.SheafOfModules.IsFlat (O := X.O) ((extendScalarsFSharp f).obj G) :=
  Stacks.FlatChangeOfRings.isFlat_extendScalars (fSharpCommRingSheaf f) G hG

/-- **The reduction of Stacks 05VD to its inverse-image half.** For a morphism of ringed topoi
`(f, f♯)` and a sheaf of `O_D`-modules `G`, the pullback `f^*G` is a flat `O_C`-module as soon
as the inverse image `f⁻¹G` is a flat `f⁻¹O_D`-module.

Stacks 05VD is this together with the flatness of `f⁻¹G`, which is **not** proved here: the
pullback of Stacks 03D6 part (2) is the inverse image followed by extension of scalars, so
Stacks 05V4 — `isFlat_extendScalarsFSharp` — disposes of the second factor and leaves the
first. The source's proof takes exactly this step ("By Lemma 05V4 it suffices to prove that
`f⁻¹F` is a flat `f⁻¹O_D`-module"). -/
theorem isFlat_pullbackModules_of_isFlat_inverseImageModules
    (G : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (hG : Stacks.SheafOfModules.IsFlat (O := inverseImageStructureCommRingSheaf f)
      ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj G)) :
    Stacks.SheafOfModules.IsFlat (O := X.O) ((f.pullbackModules).obj G) :=
  isFlat_extendScalarsFSharp f _ hG

end Stacks.Sheaves.RingedToposModules

end
