module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseCorrespondence
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBase

/-!
# The absolute separation properties of an algebraic stack (Stacks 050D, parts (5)–(8))

Parts (1)–(4) of Stacks 050D read the four separation properties of an algebraic stack `𝒳` over
its base scheme `S` off the canonical 1-morphism
`AlgebraicGeometry.Stack.structureMorphism`; they are stated in
`StacksFrontier/AlgebraicGeometry/Stacks/SeparationOverBase.lean`. Parts (5)–(8), stated here, are
the *absolute* properties: `𝒳` is DM, quasi-DM, separated or quasi-separated when it is so over
the terminal scheme `Spec ℤ`, after `𝒳` has been viewed as an algebraic stack over that scheme.

That change of base is the object map of the canonical 2-categorical correspondence of
**Stacks 04X5**, `AlgebraicGeometry.Stack.algebraicStackConstructionObjEquiv`: an algebraic stack
over `S` is the same thing as an algebraic stack over `Spec ℤ` together with a 1-morphism to the
stack represented by `S`, and the absolute properties are the relative properties of the first
component of that pair.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.viewOverIntegers`: an algebraic stack over `S`, viewed
  as an algebraic stack over the terminal scheme.
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsAbsolutelyDM`: **Stacks 050D**, part (5).
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsAbsolutelyQuasiDM`: **Stacks 050D**, part (6).
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsAbsolutelySeparated`: **Stacks 050D**, part (7).
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsAbsolutelyQuasiSeparated`: **Stacks 050D**,
  part (8).

## Main results

There are no propositional results.

## Implementation notes

All five are abbreviations, for the same reason as parts (1)–(4): a client writing one of them
unfolds to the corresponding property over the terminal scheme with no bridge lemma, and the
morphism-property API of that property applies directly.

The terminal scheme `⊤_ Scheme` represents `Spec ℤ`. Its containment in the chosen big fppf site
is an explicit hypothesis `hZ`, exactly as for the absolute separation properties of an algebraic
space in `StacksFrontier/AlgebraicGeometry/Spaces/Separated.lean`: the site is an arbitrary one and
need not contain it. The unique morphism `S ⟶ Spec ℤ` is `CategoryTheory.Limits.terminal.from`,
read as a morphism of the site by the same anonymous constructor used there.

The names carry `Absolutely` because the four relative notions the source reads them off —
`AlgebraicGeometry.Stack.IsDM`, `AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiDM`,
`...IsSeparated` and `...IsQuasiSeparated` — already occupy the unqualified names, as the four
part keys (1)–(4) already occupy the `Over` ones. The convention is that of the algebraic-space
analogue `AlgebraicGeometry.Space.IsAbsolutelySeparated` (Stacks 03BS); the two are notions about
different objects and only share a leaf name.

## References

* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

/-- An algebraic stack over `S`, viewed as an algebraic stack over the terminal scheme `Spec ℤ`:
the first component of its image under the object bijection of the canonical 2-categorical
correspondence of **Stacks 04X5** for the unique morphism `S ⟶ Spec ℤ`. -/
noncomputable abbrev viewOverIntegers (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    Stack.AlgebraicStacks.{u, w} B (⊤_ Scheme.{u}) hZ :=
  (Stack.algebraicStackConstructionObjEquiv.{u, w} B S (⊤_ Scheme.{u}) hS hZ
    (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) 𝒳).1

/-- **Stacks 050D, part (5).** An algebraic stack is *DM* when it is DM over the terminal
scheme `Spec ℤ`. -/
@[stacks 050D "part (5): absolute DM"]
noncomputable abbrev IsAbsolutelyDM (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) : Prop :=
  Stack.IsDMOver B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ 𝒳)

/-- **Stacks 050D, part (6).** An algebraic stack is *quasi-DM* when it is quasi-DM over the
terminal scheme `Spec ℤ`. -/
@[stacks 050D "part (6): absolute quasi-DM"]
noncomputable abbrev IsAbsolutelyQuasiDM (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) : Prop :=
  Stack.IsQuasiDMOver B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ 𝒳)

/-- **Stacks 050D, part (7).** An algebraic stack is *separated* when it is separated over the
terminal scheme `Spec ℤ`. -/
@[stacks 050D "part (7): absolute separatedness"]
noncomputable abbrev IsAbsolutelySeparated (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) : Prop :=
  Stack.IsSeparatedOver B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ 𝒳)

/-- **Stacks 050D, part (8).** An algebraic stack is *quasi-separated* when it is quasi-separated
over the terminal scheme `Spec ℤ`. -/
@[stacks 050D "part (8): absolute quasi-separatedness"]
noncomputable abbrev IsAbsolutelyQuasiSeparated (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    Prop :=
  Stack.IsQuasiSeparatedOver B (⊤_ Scheme.{u}) hZ (viewOverIntegers B S hS hZ 𝒳)

end AlgebraicGeometry.Stack.AlgebraicStacks

namespace AlgebraicGeometry.Stack

universe u w w'

/-- **The terminal scheme lies in every big fppf site.** `Spec (ULift ℤ)` is affine, so
`Scheme.size_Spec` computes its size as `ℵ₀`, and the cutoff of a big fppf site is above `ℵ₀`. -/
theorem contains_specULiftZ (B : BigFppfSite.{u}) :
    B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ))) := by
  change (Spec (CommRingCat.of (ULift.{u} ℤ))).size < B.cutoff
  rw [Scheme.size_Spec]
  simpa using B.aleph0_lt_cutoff

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The unique morphism of a big fppf site from an object to the terminal scheme, obtained from
`AlgebraicGeometry.specULiftZIsTerminal` through full faithfulness of the site's inclusion. -/
noncomputable def toIntObject : B.obj hS ⟶ B.obj (contains_specULiftZ B) :=
  B.inclusion.preimage (specULiftZIsTerminal.from (B.inclusion.obj (B.obj hS)))

/-- **Stacks 04X6 at the terminal base.** An algebraic stack over `S`, viewed as an algebraic
stack over `Spec(ℤ)` along the unique morphism `S ⟶ Spec(ℤ)`. This is the viewing that
**Stacks 050D**, parts (5)-(8), is stated in terms of. -/
noncomputable abbrev viewOverInt (𝒳 : AlgebraicStacks.{u, w} B S hS) :
    AlgebraicStacks.{u, w'} B (Spec (CommRingCat.of (ULift.{u} ℤ))) (contains_specULiftZ B) :=
  changeBaseAlgebraicStacks.{u, w, w'} B S _ hS (contains_specULiftZ B) (toIntObject B S hS) 𝒳

/-- **Stacks 050D, part (5).** An algebraic stack is *DM* when it is DM over `Spec(ℤ)`, viewed as
an algebraic stack over `Spec(ℤ)` by **Stacks 04X6**. -/
@[stacks 050D "part (5): DM"]
noncomputable abbrev IsDMAbs (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  IsDMOver B _ (contains_specULiftZ B) (viewOverInt.{u, w, w'} B S hS 𝒳)

/-- **Stacks 050D, part (6).** An algebraic stack is *quasi-DM* when it is quasi-DM over
`Spec(ℤ)`, viewed as an algebraic stack over `Spec(ℤ)` by **Stacks 04X6**. -/
@[stacks 050D "part (6): quasi-DM"]
noncomputable abbrev IsQuasiDMAbs (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  IsQuasiDMOver B _ (contains_specULiftZ B) (viewOverInt.{u, w, w'} B S hS 𝒳)

/-- **Stacks 050D, part (7).** An algebraic stack is *separated* when it is separated over
`Spec(ℤ)`, viewed as an algebraic stack over `Spec(ℤ)` by **Stacks 04X6**. -/
@[stacks 050D "part (7): separated"]
noncomputable abbrev IsSeparatedAbs (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  IsSeparatedOver B _ (contains_specULiftZ B) (viewOverInt.{u, w, w'} B S hS 𝒳)

/-- **Stacks 050D, part (8).** An algebraic stack is *quasi-separated* when it is quasi-separated
over `Spec(ℤ)`, viewed as an algebraic stack over `Spec(ℤ)` by **Stacks 04X6**. -/
@[stacks 050D "part (8): quasi-separated"]
noncomputable abbrev IsQuasiSeparatedAbs (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  IsQuasiSeparatedOver B _ (contains_specULiftZ B) (viewOverInt.{u, w, w'} B S hS 𝒳)

end AlgebraicGeometry.Stack

end
