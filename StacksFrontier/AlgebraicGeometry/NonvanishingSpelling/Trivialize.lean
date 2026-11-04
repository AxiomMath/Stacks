module

public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic

/-!
# Stacks Tag 01CY, the trivialization clause, at the scheme spelling

`StacksFrontier/AlgebraicGeometry/NonvanishingTrivialize/Basic.lean` proves the trivialization
clause of Stacks Tag 01CY -- a global section of an invertible module is a basis of that module on
its nonvanishing locus -- for a **ringed space** with local stalks and a module over the
`Stacks.SheafOfModules.TensorSheafification` packaging of its structure sheaf, which is the
  spelling of the tagged statement. Every
consumer in this repository works with a **scheme** `X`, a module `M : X.Modules` and a global
section `s : Γ(M, ⊤)`. This file transports the clause to that spelling, across the identification
of `StacksFrontier/AlgebraicGeometry/NonvanishingSpelling/Basic.lean`.

## Main results

* `Stacks.NonvanishingSpelling.bijective_smul`: **the elementary content of the clause, and the
  handle the consumers want.** For every open `W` inside the nonvanishing open of `s`, the map
  `a ↦ a • s|_W` from `Γ(X, W)` to `Γ(M, W)` is bijective. Stated with Mathlib's
  `Module Γ(X, U) Γ(M, U)` instance for a scheme, not with the ringed-space substitute
  `Stacks.NonvanishingTrivialize.moduleSections` that the ringed-space spelling has to introduce.
* `Stacks.NonvanishingSpelling.existsUnique_smul_eq`: the same statement as a division. Every
  section of `M` over an open inside `X_s` is `a • s|_W` for exactly one `a : Γ(X, W)`. This is
  the ratio `t / s` that the Stacks arguments around Tag 01PS and Tag 01CV write down.
* `Stacks.NonvanishingSpelling.isIso_over_of_le` and
  `Stacks.NonvanishingSpelling.isIso_over_nonvanishingOpen`: **the clause in the shape the
  tagged statement gives it**, at the scheme spelling: the morphism `𝒪_X ⟶ M` determined by `s` is
  an isomorphism after restriction to any open inside `X_s`, in particular to `X_s` itself.
* `Stacks.NonvanishingSpelling.unitHom_app`: the morphism determined by `s` acts on sections over
  `W` by multiplication by `s|_W`. This is what connects the two shapes above, and it is the
  scheme-level restatement of `Stacks.NonvanishingTrivialize.unitHomEquiv_symm_app`.

## The route

There is nothing to prove. `Stacks.NonvanishingSpelling.nonvanishingOpen_symm_eq` identifies the
two nonvanishing opens, so every hypothesis `W ≤ X_s` at one spelling is one at the other, and the
remaining differences are definitional: `Γ(X, W)` is `X.presheaf.obj (op W)`, the two scalar
actions on `Γ(M, W)` are both `(M.val.obj (op W)).isModule`, and the restriction of a global
section along `W ⟶ ⊤` is the value at `W` of the restriction-compatible family that
`Stacks.NonvanishingSpelling.sectionsEquiv` produces. Each statement below therefore applies the
ringed-space theorem to `(sectionsEquiv X M).symm s` and lets the kernel check the spelling.

The open occurs in the *type* of the morphism whose isomorphy the clause asserts, so a rewrite of
the open inside `IsIso (φ.over U)` is a dependent one and is worth avoiding. It is avoided:
`isIso_over_of_le` is transported first, with the open appearing only in a hypothesis `U ≤ X_s`
where the identification is absorbed by `LE.le.trans_eq`, and `isIso_over_nonvanishingOpen` is
then its instance at `U = X_s`, exactly as in the ringed-space file.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01PS](https://stacks.math.columbia.edu/tag/01PS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorSheafification
open Stacks.ModuleStalk

universe u

namespace Stacks.NonvanishingSpelling

variable (X : Scheme.{u}) (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M]

/-! ### Multiplication by a nonvanishing section -/

/-- **The trivialization clause of Stacks Tag 01CY in elementary terms, at the scheme spelling.**
Over every open inside the nonvanishing open of a global section `s` of an invertible
`𝒪_X`-module on a scheme, multiplication by `s` is a bijection from `Γ(X, W)` to `Γ(M, W)`: `s`
is a basis of `M` there. The scalar action is Mathlib's `Module Γ(X, U) Γ(M, U)`. -/
theorem bijective_smul (s : Γ(M, ⊤)) {W : X.Opens}
    (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M s) :
    Function.Bijective
      fun a : Γ(X, W) => a • M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s :=
  Stacks.NonvanishingTrivialize.bijective_smul (X := X.toRingedSpace)
    (L := toSheafOfModules X M) ((sectionsEquiv X M).symm s)
    (hW.trans_eq (nonvanishingOpen_symm_eq X M s).symm)

/-- **Division by a nonvanishing section.** Over an open inside the nonvanishing open of `s`,
every section of `M` is a unique multiple of `s`; the unique scalar is the ratio `t / s`. This is
`bijective_smul` restated, and it is the form in which the Stacks arguments for ampleness use the
clause. -/
theorem existsUnique_smul_eq (s : Γ(M, ⊤)) {W : X.Opens}
    (hW : W ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M s) (t : Γ(M, W)) :
    ∃! a : Γ(X, W), a • M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s = t :=
  (bijective_smul X M s hW).existsUnique t

/-! ### The trivialization in the shape of the tagged statement -/

omit [Stacks.Ample.IsInvertibleModule X M] in
/-- The morphism `𝒪_X ⟶ M` determined by a global section `s` acts on the sections over `W` by
multiplication by `s|_W`. The scheme-level restatement of
`Stacks.NonvanishingTrivialize.unitHomEquiv_symm_app`, and the bridge between the two shapes of
the trivialization clause. Needs no invertibility: it is about the morphism, not about `X_s`. -/
theorem unitHom_app (s : Γ(M, ⊤)) (W : X.Opens) (a : Γ(X, W)) :
    ((toSheafOfModules X M).unitHomEquiv.symm ((sectionsEquiv X M).symm s)).val.app (op W) a
      = a • M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op s :=
  Stacks.NonvanishingTrivialize.unitHomEquiv_symm_app ((sectionsEquiv X M).symm s) W a

/-- **Stacks Tag 01CY, the trivialization, over an arbitrary open inside the nonvanishing
locus**, at the scheme spelling: the morphism from the structure sheaf determined by `s` becomes
an isomorphism after restriction to any open on which `s` does not vanish. -/
theorem isIso_over_of_le (s : Γ(M, ⊤)) {U : X.Opens}
    (hU : U ≤ Stacks.NonvanishingOpen.nonvanishingOpen X M s) :
    IsIso (((toSheafOfModules X M).unitHomEquiv.symm ((sectionsEquiv X M).symm s)).over U) :=
  Stacks.NonvanishingTrivialize.isIso_over_of_le (X := X.toRingedSpace)
    (L := toSheafOfModules X M) ((sectionsEquiv X M).symm s)
    (hU.trans_eq (nonvanishingOpen_symm_eq X M s).symm)

/-- **Stacks Tag 01CY, the trivialization, at the scheme spelling.** A global section of an
invertible `𝒪_X`-module on a scheme trivializes that module on its nonvanishing open: the
morphism from the structure sheaf determined by the section is an isomorphism there. -/
instance isIso_over_nonvanishingOpen (s : Γ(M, ⊤)) :
    IsIso (((toSheafOfModules X M).unitHomEquiv.symm ((sectionsEquiv X M).symm s)).over
      (Stacks.NonvanishingOpen.nonvanishingOpen X M s)) :=
  isIso_over_of_le X M s le_rfl

end Stacks.NonvanishingSpelling

end
