module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparatedQuasiSeparatedAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureMorphism

/-!
# The packaged quasi-DM condition, and that DM implies quasi-DM (Stacks 04YW, 050E)

The quasi-DM condition of an algebraic stack comes in two shapes. The one the **Stacks 04YW**
part key sits on is `AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiDM`, which says exactly what
the source says — the relative diagonal is locally quasi-finite in the sense of Stacks 04XB, with
no further conjunct. What is stated here is the *packaged* shape of that same condition, carrying
the representability of the relative diagonal as an extra conjunct and so matching
`AlgebraicGeometry.Stack.IsDM`. The two are equivalent for a 1-morphism of *algebraic* stacks,
because the representability of the diagonal is a theorem there — Stacks 04XS, part (1) — and not
part of the definition; that is why the Stacks 04YW part key sits on the witness-free condition
and not on the packaged one.

## Main definitions

* `AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiDMWithRepresentableDiagonal`: the quasi-DM
  condition of **Stacks 04YW** with the representability of the diagonal carried as a conjunct.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDMWithRepresentableDiagonal_iff_isQuasiDM`: the
  packaged shape of the quasi-DM condition and the witness-free one of Stacks 04YW are the same
  proposition for a 1-morphism of algebraic stacks.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDMWithRepresentableDiagonal_of_isDM`:
  **Stacks 050E**, that a DM 1-morphism is quasi-DM.

## Implementation notes

`IsQuasiDMWithRepresentableDiagonal` is written out **longhand** — the quantifier of Stacks 03YK
over the scheme-valued points of the 2-fibre product and the algebraic spaces representing the
base changes of the diagonal there — rather than through
`AlgebraicGeometry.Stack.HasRelativeProperty`, for the same
reason as its sibling `AlgebraicGeometry.Stack.IsDM`: `HasRelativeProperty` carries
`[P.IsStableUnderBaseChange]` and `[P.IsLocalAtTarget (Space.Topology.fppf.precoverage B S hS)]`
as instance arguments, neither of which is available for local quasi-finiteness of morphisms of
algebraic spaces in this library. Since `HasRelativeProperty` does not use either argument in its
body, the longhand quantifier is *the same proposition* carrying no hypothesis on the property,
so this definition is unconditional. Its body is that of `AlgebraicGeometry.Stack.IsDM` with
`AlgebraicGeometry.Space.IsUnramified` replaced by
`AlgebraicGeometry.Space.IsLocallyQuasiFinite` (**Stacks 03XJ**, part (1)), which is how the
source states the two conditions as well.

Stacks 050E, that DM implies quasi-DM, is proved here rather than beside its sibling key
`separated_implies_quasi_separated`, because it is a statement about the quasi-DM condition and is
proved
exactly as the source proves it: the two conditions are the *same* quantifier over the *same*
represented base changes of the relative diagonal, differing only in the property tested of the
resulting morphism of algebraic spaces, so the implication is
`AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isUnramified` (**Stacks 05W0**) applied
pointwise, with no comparison lemma between the two quantifiers.

## References

* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050E](https://stacks.math.columbia.edu/tag/050E)
* [Stacks Project, Tag 05W0](https://stacks.math.columbia.edu/tag/05W0)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 04YW, the quasi-DM condition, with the representability of the diagonal carried as
a conjunct.** A 1-morphism of algebraic stacks over `S` is *quasi-DM* when its relative diagonal
is representable by algebraic spaces and locally quasi-finite, the latter in the relative sense
of Stacks 03YK: every algebraic space representing a base change of the diagonal along a
scheme-valued point of `𝒳 ×_{f, 𝒴, f} 𝒳` has locally quasi-finite structural morphism.

This is the shape of `AlgebraicGeometry.Stack.IsDM`, which carries the same witness.
It is **untagged**: the Stacks 04YW part key *quasi_dm* sits on
`AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiDM`, the condition without that conjunct, which
is what the source states. The two are the same proposition for a 1-morphism of *algebraic*
stacks, by Stacks 04XS, part (1), which is
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDMWithRepresentableDiagonal_iff_isQuasiDM`. -/
abbrev IsQuasiDMWithRepresentableDiagonal {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) : Prop :=
  let T := Stack.twoFibreProduct.{u, u, u + 1, u, u + 1, u, u + 1} B S hS
    𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom
  let Δ := Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom
  ∃ _hΔ : Stack.IsRepresentableByAlgebraicSpaces B S hS Δ.hom,
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ T.val.obj)
      (_hy : y ⋙ T.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p T.val.p y
          (CatFiberedInGroupoids.homFunctor Δ))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsLocallyQuasiFinite B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

/-- **The packaged and the witness-free quasi-DM conditions agree.** For a 1-morphism of
*algebraic* stacks the representability of the relative diagonal by algebraic spaces is a theorem,
Stacks 04XS part (1), so carrying it as a conjunct adds nothing: the packaged condition is the
same proposition as `AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiDM`, which is the one the
Stacks 04YW part key sits on. -/
theorem isQuasiDMWithRepresentableDiagonal_iff_isQuasiDM
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) :
    IsQuasiDMWithRepresentableDiagonal B S hS f ↔ IsQuasiDM B S hS f :=
  ⟨fun h => h.elim fun _ hP => hP,
    fun h =>
      ⟨Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f, h⟩⟩

/-- **Stacks 050E.** A DM 1-morphism of algebraic stacks over `S` is quasi-DM.

Both conditions quantify over the same represented base changes of the relative diagonal and
differ only in the property tested of the resulting morphism of algebraic spaces, so the
implication is Stacks 05W0 — an unramified morphism of algebraic spaces is locally quasi-finite —
applied at each of them. -/
@[stacks 050E "dm_implies_quasi_dm"]
theorem isQuasiDMWithRepresentableDiagonal_of_isDM
    {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : Stack.IsDM B S hS f) : IsQuasiDMWithRepresentableDiagonal B S hS f :=
  Exists.imp (fun _ hrel U y hy F hF hEquiv =>
    Space.isLocallyQuasiFinite_of_isUnramified B S hS _ (hrel U y hy F hF hEquiv)) hf

end AlgebraicGeometry.Stack.AlgebraicStacks

end
