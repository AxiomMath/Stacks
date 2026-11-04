module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureMorphism
public import StacksFrontier.CategoryTheory.Sites.Localization.StacksAndLocalization
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# Separation axioms for morphisms of algebraic stacks (Stacks 04YW, 050D)

Let `S` be a scheme contained in a big fppf site `B`. Following Stacks 04YW, a 1-morphism
`f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` is

* *DM* when its relative diagonal `Δ_f` is unramified,
* *quasi-DM* when `Δ_f` is locally quasi-finite,
* *separated* when `Δ_f` is proper, and
* *quasi-separated* when `Δ_f` is quasi-compact and quasi-separated,

each condition being read in the sense of Properties of Stacks, Section 04XB, which `Δ_f` is
eligible for because it is representable by algebraic spaces (**Stacks 04XS**, part (1)).
Stacks 050D then reads the first four of its eight properties off the structure morphism
`p : 𝒳 ⟶ S`: `𝒳` is DM, quasi-DM, separated, respectively quasi-separated *over* `S` when `p`
is.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiDM`: **Stacks 04YW**, quasi-DM.
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsSeparated`: **Stacks 04YW**, separated.
* `AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiSeparated`: **Stacks 04YW**, quasi-separated.
* `AlgebraicGeometry.Stack.IsDMOver`, `AlgebraicGeometry.Stack.IsQuasiDMOver`,
  `AlgebraicGeometry.Stack.IsSeparatedOver`, `AlgebraicGeometry.Stack.IsQuasiSeparatedOver`:
  **Stacks 050D**, parts (1)–(4).

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_iff_forall`: the quasi-separatedness
  of Stacks 04YW, stated as the conjunction of two conditions of Stacks 04XB, is the single
  condition of Stacks 04XB whose conclusion is the conjunction.

## Implementation notes

The tag sits on the predicates in the `AlgebraicGeometry.Stack.AlgebraicStacks` namespace, which
are the notions of Stacks 04YW as properties of a 1-morphism of *algebraic stacks*. That matches
`AlgebraicGeometry.Stack.AlgebraicStacks.IsOpenImmersion` and its companions. The three Stacks
04XB predicates the axioms below are stated with —
`AlgebraicGeometry.Stack.IsQuasiCompact` (**Stacks 03HE**),
`AlgebraicGeometry.Stack.IsQuasiSeparated` (**Stacks 03HL**, part (3)) and
`AlgebraicGeometry.Stack.IsLocallyQuasiFinite` (**Stacks 03XJ**, part (1)) — are imported from
`StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedMorphism`, where they are untagged because
Stacks 04XB's general definition is already tagged, as
`AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**). The name
`AlgebraicGeometry.Stack.IsSeparated` is the Stacks 04XB notion
(`StacksFrontier.AlgebraicGeometry.Stacks.SeparatedMorphism`), so the Stacks 04YW notion of the
same English name is `AlgebraicGeometry.Stack.AlgebraicStacks.IsSeparated`; the two are different
properties of different kinds of 1-morphism and the namespace is what distinguishes them.

Part (4) of Stacks 04YW is *`Δ_f` is quasi-compact and quasi-separated*, a conjunction of two
properties of the one 1-morphism `Δ_f`. It is stated here as the conjunction of the two Stacks
04XB predicates rather than as one Stacks 04XB condition whose conclusion is a conjunction;
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_iff_forall` identifies the two
spellings, so a consumer that has destructured a single universally quantified hypothesis can
still use it.

`AlgebraicGeometry.Stack.IsDM` (**Stacks 04YW**, DM) is already formalized, in
`StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordMorphism`, and is reused rather than
restated; it carries an existential over a representability witness for `Δ_f` that those three
Stacks 04XB notions do not need, because properness, quasi-compactness, quasi-separatedness and
local quasi-finiteness are each stated by the Stacks 04XB quantifier over *all* algebraic spaces
representing a base change, which is meaningful with no witness in hand.

The structure morphism is `AlgebraicGeometry.Stack.structureMorphism`
(`StacksFrontier.AlgebraicGeometry.Stacks.StructureMorphism`), reused rather than re-coined, as the
docstring of that declaration asks. Its naturality is proved by extensionality in three layers:
the 1-morphisms of `AlgebraicGeometry.Stack.AlgebraicStacks` are based functors under two
applications of `CategoryTheory.Bicategory.InducedBicategory.mkHom`, and a based functor is
determined by its underlying functor (`CategoryTheory.BasedCategory.BasedFunctor.ext'`); the
underlying identity is then associativity of composition together with the compatibility field
of `f`.

Parts (5)–(8) of Stacks 050D — the *absolute* DM, quasi-DM, separated and quasi-separated
properties, obtained by viewing `𝒳` as an algebraic stack over `Spec(ℤ)` — are **not** proved
here. They need the object-level half of the canonical correspondence of Stacks 04X5, i.e. that
Construction A carries an algebraic stack over `S` to an algebraic stack over a smaller base.
This library has each of its four clauses separately, in
`StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBase`, but not the assembled statement, so Stacks
050D is **PARTIAL here, at its first four part keys**.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

namespace AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 04YW, quasi-DM.** A 1-morphism of algebraic stacks over `S` is *quasi-DM* when its
relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` is locally quasi-finite in the sense of Stacks
04XB. -/
@[stacks 04YW "quasi_dm"]
abbrev IsQuasiDM (f : 𝒳 ⟶ 𝒴) : Prop :=
  Stack.IsLocallyQuasiFinite B S hS
    (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)

/-- **Stacks 04YW, separated.** A 1-morphism of algebraic stacks over `S` is *separated* when its
relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` is proper in the sense of Stacks 04XB. -/
@[stacks 04YW "separated"]
abbrev IsSeparated (f : 𝒳 ⟶ 𝒴) : Prop :=
  Stack.IsProper B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)

/-- **Stacks 04YW, quasi-separated.** A 1-morphism of algebraic stacks over `S` is
*quasi-separated* when its relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` is quasi-compact and
quasi-separated, both in the sense of Stacks 04XB. -/
@[stacks 04YW "quasi_separated"]
abbrev IsQuasiSeparated (f : 𝒳 ⟶ 𝒴) : Prop :=
  Stack.IsQuasiCompact B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) ∧
    Stack.IsQuasiSeparated B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)

/-- Quasi-separatedness of Stacks 04YW, as a single condition of Stacks 04XB whose conclusion is
the conjunction of quasi-compactness and quasi-separatedness of the representing morphism of
algebraic spaces. This is the spelling obtained by introducing the Stacks 04XB data once rather
than twice; it is the same proposition as the conjunction of the two conditions. -/
theorem isQuasiSeparated_iff_forall (f : 𝒳 ⟶ 𝒴) :
    IsQuasiSeparated B S hS f ↔
      ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤
          (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.obj)
        (_hy : y ⋙ (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p =
          Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
          Nonempty (StacksRepresentableCFG.EquivalenceOver
            (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
              (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom).val.p y
              (CatFiberedInGroupoids.homFunctor
                (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)))
            (presheafOfCategories (F ⋙ typeToCat)).p) →
          (Space.IsQuasiCompact B S hS
              (algebraicSpaceMap B S hS U
                ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj
                  ⟨F, hF⟩)).hom ∧
            Space.IsQuasiSeparated B S hS
              (algebraicSpaceMap B S hS U
                ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj
                  ⟨F, hF⟩)).hom) :=
  ⟨fun h U y hy F hF hrep => ⟨h.1 U y hy F hF hrep, h.2 U y hy F hF hrep⟩,
    fun h => ⟨fun U y hy F hF hrep => (h U y hy F hF hrep).1,
      fun U y hy F hF hrep => (h U y hy F hF hrep).2⟩⟩

end AlgebraicStacks

section StructureMorphism

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 050D, part (1).** An algebraic stack over `S` is *DM over `S`* when its structure
morphism to the algebraic stack represented by `S` is DM in the sense of Stacks 04YW. -/
@[stacks 050D "part (1): DM over the base"]
noncomputable abbrev IsDMOver (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  IsDM B S hS (structureMorphism B S hS 𝒳)

/-- **Stacks 050D, part (2).** An algebraic stack over `S` is *quasi-DM over `S`* when its
structure morphism to the algebraic stack represented by `S` is quasi-DM in the sense of Stacks
04YW. -/
@[stacks 050D "part (2): quasi-DM over the base"]
noncomputable abbrev IsQuasiDMOver (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  AlgebraicStacks.IsQuasiDM B S hS (structureMorphism B S hS 𝒳)

/-- **Stacks 050D, part (3).** An algebraic stack over `S` is *separated over `S`* when its
structure morphism to the algebraic stack represented by `S` is separated in the sense of Stacks
04YW. -/
@[stacks 050D "part (3): separated over the base"]
noncomputable abbrev IsSeparatedOver (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  AlgebraicStacks.IsSeparated B S hS (structureMorphism B S hS 𝒳)

/-- **Stacks 050D, part (4).** An algebraic stack over `S` is *quasi-separated over `S`* when its
structure morphism to the algebraic stack represented by `S` is quasi-separated in the sense of
Stacks 04YW. -/
@[stacks 050D "part (4): quasi-separated over the base"]
noncomputable abbrev IsQuasiSeparatedOver (𝒳 : AlgebraicStacks.{u, w} B S hS) : Prop :=
  AlgebraicStacks.IsQuasiSeparated B S hS (structureMorphism B S hS 𝒳)

end StructureMorphism

end AlgebraicGeometry.Stack

end
