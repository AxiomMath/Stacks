module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyInvariance
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFibreProductProperties
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductUniversalProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveDiagonal
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverDiagonalBaseChange

/-!
# The separation axioms are stable under base change (Stacks 050F)

Let `f : 𝒳 ⟶ 𝒴` and `g : 𝒵 ⟶ 𝒴` be 1-morphisms of algebraic stacks over a scheme `S` contained
in a big fppf site `B`, and let `q : 𝒳 ×_𝒴 𝒵 ⟶ 𝒵` be the base change of `f` along `g`, i.e. the
second projection of the canonical 2-fibre product square. **Stacks 050F** says that each of the
four separation axioms of **Stacks 04YW** — DM, quasi-DM, separated, quasi-separated — holds for
`q` as soon as it holds for `f`.

All four axioms are conditions of Properties of Stacks, Section 04XB, on the relative diagonal,
at four different properties of morphisms of algebraic spaces over `S`. So all four are the same
statement — *a condition of Stacks 04XB on the relative diagonal is inherited by a base change* —
applied four times, and that statement is proved once here, for an arbitrary property `P` of
morphisms of algebraic spaces and with no hypothesis on `P` at all.

Its proof is the source's, in two steps. First, **Stacks 04YR** — the diagonal of a base change
is a base change of the diagonal — says that `Δ_q` is obtained from `Δ_f` by base change along
the 1-morphism `r × r : (𝒳 ×_𝒴 𝒵) ×_𝒵 (𝒳 ×_𝒴 𝒵) ⟶ 𝒳 ×_𝒴 𝒳` induced by the first projection on
both factors; this is available as the equivalence
`CategoryTheory.TwoFibreProductOver.isEquivalence_diagonalBaseChangeComparison`. Second,
**Stacks 045C** — a condition of Stacks 04XB is stable under base change — gives the condition
for the first projection of the canonical 2-fibre product square of `r × r` and `Δ_f`, and the
04YR comparison is an equivalence over the site carrying that projection to `Δ_q`, so
**Stacks 0457** for the condition of Stacks 04XB transports the conclusion across it.

## Main results

* `AlgebraicGeometry.Stack.relativeProperty_baseChange`: **Stacks 045C** for the longhand
  quantifier of Stacks 03YK, with no hypothesis on the property.
* `AlgebraicGeometry.Stack.prop_relativeDiagonal_baseChange`: a condition of Stacks 04XB on the
  relative diagonal is inherited by the relative diagonal of a base change, for an arbitrary
  property `P` of morphisms of algebraic spaces over `S`.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isDM_baseChange`: **Stacks 050F**, DM.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_baseChange`: **Stacks 050F**, quasi-DM.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_baseChange`: **Stacks 050F**, separated.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_baseChange`: **Stacks 050F**,
  quasi-separated.

## Implementation notes

`AlgebraicGeometry.Stack.prop_relativeDiagonal_baseChange` writes the condition of Stacks 04XB
out longhand rather than using `AlgebraicGeometry.Stack.HasRelativeProperty` (**Stacks 03YK**),
for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationFibreProductProperties`: that abbreviation
carries `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` and
`CategoryTheory.MorphismProperty.IsLocalAtTarget` as instance arguments, and for properness,
quasi-compactness, quasi-separatedness, local quasi-finiteness and unramifiedness of morphisms of
algebraic spaces over `S` those instances are not in the library, so a *statement* about it
cannot be elaborated at the properties the separation axioms are defined with. The two inputs are
used in their instance-free forms,
`AlgebraicGeometry.Stack.prop_baseChange_of_isTwoFibreProduct` (Stacks 045C) and
`AlgebraicGeometry.Stack.relativeProperty_of_equivalences` (Stacks 0457), neither of which needs
any hypothesis on `P`.

`AlgebraicGeometry.Stack.relativeProperty_baseChange` is that same instance-free reading of
**Stacks 045C** at an arbitrary 2-fibre product square of categories fibred in groupoids: it is
`AlgebraicGeometry.Stack.hasRelativeProperty_baseChange` with its two instance arguments dropped.
The proof uses neither of them — a scheme-valued point of `𝒵` is pushed to one of `𝒴` along `g`,
and `AlgebraicGeometry.Stack.nonempty_baseChangeEquivalenceOver` identifies the two base changes
over the site of the test scheme, so the algebraic space being tested is literally the same one on
both sides — and that is what makes the longhand quantifier transportable at the properties the
four separation axioms of Stacks 04YW are defined with.

The base change is the second projection of the canonical 2-fibre product square
`AlgebraicGeometry.Stack.AlgebraicStacks.twoFibreProductSquare`. Stating it at an arbitrary
2-fibre product square of the cospan would additionally need the equivalence
`(𝒳 ×_𝒴 𝒵) ×_𝒵 (𝒳 ×_𝒴 𝒵) ≃ R.pt ×_𝒵 R.pt` induced by the comparison `R.pt ≃ 𝒳 ×_𝒴 𝒵` of two
2-fibre products, compatibly with the two relative diagonals; that induced 1-morphism is not in
the library.

The 1-morphism `r × r` is `CategoryTheory.TwoFibreProductOver.mapDiag`, read as a 1-morphism of
algebraic stacks; it commutes with the projections to the site on the nose, which is why its
`CategoryTheory.BasedFunctor.w` field is `rfl`. The identification of the first projection of the
2-fibre product square of `(r × r, Δ_f)` with `Δ_q` across the 04YR comparison is likewise an
identity of based functors, so the 2-commutativity isomorphism fed to Stacks 0457 is
`CategoryTheory.Iso.refl`.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YR](https://stacks.math.columbia.edu/tag/04YR)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050F](https://stacks.math.columbia.edu/tag/050F)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 045C for the longhand quantifier of Stacks 03YK, with no hypothesis on the
property.** Let `P` be a property of morphisms of algebraic spaces over `S`. In a 2-fibre product
square over a cospan `g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big
fppf site of `S`, if every algebraic space representing a base change of `f` along a
scheme-valued point of `𝒴` has structural morphism with `P`, then the same holds of the
projection `R.fst` to `𝒵`.

This is `AlgebraicGeometry.Stack.hasRelativeProperty_baseChange` with its two instance arguments
dropped: a scheme-valued point of `𝒵` is pushed to one of `𝒴` along `g`, and
`AlgebraicGeometry.Stack.nonempty_baseChangeEquivalenceOver` identifies the two base changes over
the site of the test scheme, so the algebraic space being tested is literally the same one on
both sides. -/
alias relativeProperty_baseChange := prop_baseChange_of_isTwoFibreProduct

/-- **A condition of Stacks 04XB on the relative diagonal is inherited by a base change.** Let
`P` be any property of morphisms of algebraic spaces over `S`, let `f : 𝒳 ⟶ 𝒴` and `g : 𝒵 ⟶ 𝒴`
be 1-morphisms of algebraic stacks over `S`, and let `q : 𝒳 ×_𝒴 𝒵 ⟶ 𝒵` be the second projection
of the canonical 2-fibre product square. If the relative diagonal `Δ_f` satisfies the condition
of Stacks 04XB for `P`, then so does `Δ_q`.

The four clauses of Stacks 050F are the four specialisations of this statement; it has no
hypothesis on `P` at all. -/
theorem prop_relativeDiagonal_baseChange
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    {𝒳 𝒴 𝒵 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (hΔ : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (AlgebraicStacks.twoFibreProduct B S hS f f).val.val.obj)
      (_hy : y ⋙ (AlgebraicStacks.twoFibreProduct B S hS f f).val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
            (AlgebraicStacks.twoFibreProduct B S hS f f).val.val.p y
            (CatFiberedInGroupoids.homFunctor
              (AlgebraicStacks.relativeDiagonal B S hS f).hom))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤
        (AlgebraicStacks.twoFibreProduct B S hS
          (AlgebraicStacks.twoFibreProductSquare B S hS f g).snd
          (AlgebraicStacks.twoFibreProductSquare B S hS f g).snd).val.val.obj)
      (_hz : z ⋙ (AlgebraicStacks.twoFibreProduct B S hS
          (AlgebraicStacks.twoFibreProductSquare B S hS f g).snd
          (AlgebraicStacks.twoFibreProductSquare B S hS f g).snd).val.val.p
            = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (AlgebraicStacks.twoFibreProductSquare B S hS f g).pt.val.val.p
            (AlgebraicStacks.twoFibreProduct B S hS
              (AlgebraicStacks.twoFibreProductSquare B S hS f g).snd
              (AlgebraicStacks.twoFibreProductSquare B S hS f g).snd).val.val.p z
            (CatFiberedInGroupoids.homFunctor
              (AlgebraicStacks.relativeDiagonal B S hS
                (AlgebraicStacks.twoFibreProductSquare B S hS f g).snd).hom))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) := by
  classical
  set U := AlgebraicStacks.twoFibreProductSquare B S hS f g
  have hh : CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p = 𝒳.val.val.p := f.hom.hom.w
  have hs : CatFiberedInGroupoids.homFunctor g.hom ⋙ 𝒴.val.val.p = 𝒵.val.val.p := g.hom.hom.w
  let mapDiagMor : AlgebraicStacks.twoFibreProduct B S hS U.snd U.snd ⟶
      AlgebraicStacks.twoFibreProduct B S hS f f :=
    Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
      { toFunctor := TwoFibreProductOver.mapDiag hs, w := rfl })
  set K := AlgebraicStacks.twoFibreProductSquare B S hS mapDiagMor
    (AlgebraicStacks.relativeDiagonal B S hS f)
  have hK := AlgebraicStacks.isTwoFibreProduct_twoFibreProductSquare B S hS mapDiagMor
    (AlgebraicStacks.relativeDiagonal B S hS f)
  have hKfst := prop_baseChange_of_isTwoFibreProduct.{u, u, u} B S hS P 𝒳.val
    (AlgebraicStacks.twoFibreProduct B S hS f f).val
    (AlgebraicStacks.twoFibreProduct B S hS U.snd U.snd).val
    (AlgebraicStacks.relativeDiagonal B S hS f).hom mapDiagMor.hom
    (AlgebraicStacks.toCatFiberedInGroupoids B S hS K)
    (AlgebraicStacks.isTwoFibreProduct_toCatFiberedInGroupoids B S hS K hK) hΔ
  have hcmpw : TwoFibreProductOver.diagonalBaseChangeComparison hh hs ⋙ K.pt.val.val.p =
      U.pt.val.val.p :=
    TwoFibreProductOver.diagonalBaseChangeComparison_comp_structureFunctor hh hs
  let cmp : U.pt.val.val ⥤ᵇ K.pt.val.val :=
    ⟨TwoFibreProductOver.diagonalBaseChangeComparison hh hs, hcmpw⟩
  have : Functor.IsEquivalence cmp.toFunctor :=
    TwoFibreProductOver.isEquivalence_diagonalBaseChangeComparison hh hs
  have : Functor.IsEquivalence
      (BasedFunctor.id (AlgebraicStacks.twoFibreProduct B S hS U.snd U.snd).val.val).toFunctor :=
    inferInstanceAs (Functor.IsEquivalence (CategoryTheory.Functor.id _))
  exact relativeProperty_of_equivalences B S hS P
    (AlgebraicStacks.relativeDiagonal B S hS U.snd).hom.hom K.fst.hom.hom cmp
    (BasedFunctor.id _) (Iso.refl _) hKfst

namespace AlgebraicStacks

variable {𝒳 𝒴 𝒵 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)

/-- **Stacks 050F, DM.** The base change `q : 𝒳 ×_𝒴 𝒵 ⟶ 𝒵` of a Deligne–Mumford 1-morphism of
algebraic stacks over `S` is Deligne–Mumford: its relative diagonal is representable by algebraic
spaces (**Stacks 04XS**, part (1)) and unramified in the sense of Stacks 04XB, the latter because
`Δ_q` is a base change of `Δ_f`. -/
@[stacks 050F "dm"]
theorem isDM_baseChange (hf : Stack.IsDM B S hS f) :
    Stack.IsDM B S hS (twoFibreProductSquare B S hS f g).snd :=
  ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS
      (twoFibreProductSquare B S hS f g).snd,
    prop_relativeDiagonal_baseChange B S hS
      (fun _ _ m => Space.IsUnramified B S hS m.hom) f g hf.2⟩

/-- **Stacks 050F, quasi-DM.** The base change `q : 𝒳 ×_𝒴 𝒵 ⟶ 𝒵` of a quasi-DM 1-morphism of
algebraic stacks over `S` is quasi-DM: `Δ_q` is a base change of `Δ_f`, which is locally
quasi-finite in the sense of Stacks 04XB. -/
@[stacks 050F "quasi_dm"]
theorem isQuasiDM_baseChange (hf : IsQuasiDM B S hS f) :
    IsQuasiDM B S hS (twoFibreProductSquare B S hS f g).snd :=
  prop_relativeDiagonal_baseChange B S hS
    (fun _ _ m => Space.IsLocallyQuasiFinite B S hS m.hom) f g hf

/-- **Stacks 050F, separated.** The base change `q : 𝒳 ×_𝒴 𝒵 ⟶ 𝒵` of a separated 1-morphism of
algebraic stacks over `S` is separated: `Δ_q` is a base change of `Δ_f`, which is proper in the
sense of Stacks 04XB. -/
@[stacks 050F "separated"]
theorem isSeparated_baseChange (hf : IsSeparated B S hS f) :
    IsSeparated B S hS (twoFibreProductSquare B S hS f g).snd :=
  prop_relativeDiagonal_baseChange B S hS
    (fun _ _ m => Space.IsProper B S hS m.hom) f g hf

/-- **Stacks 050F, quasi-separated.** The base change `q : 𝒳 ×_𝒴 𝒵 ⟶ 𝒵` of a quasi-separated
1-morphism of algebraic stacks over `S` is quasi-separated: `Δ_q` is a base change of `Δ_f`,
which is quasi-compact and quasi-separated in the sense of Stacks 04XB. -/
@[stacks 050F "quasi_separated"]
theorem isQuasiSeparated_baseChange (hf : IsQuasiSeparated B S hS f) :
    IsQuasiSeparated B S hS (twoFibreProductSquare B S hS f g).snd :=
  ⟨prop_relativeDiagonal_baseChange B S hS
      (fun _ _ m => Space.IsQuasiCompact B S hS m.hom) f g hf.1,
    prop_relativeDiagonal_baseChange B S hS
      (fun _ _ m => Space.IsQuasiSeparated B S hS m.hom) f g hf.2⟩

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
