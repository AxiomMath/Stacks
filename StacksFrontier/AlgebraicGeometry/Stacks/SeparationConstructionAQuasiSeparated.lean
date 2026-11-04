module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactLargerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationConstructionA

/-!
# The quasi-separatedness condition of Stacks 04YW passes along Construction A

Let `g : S ⟶ S'` be a morphism of a big fppf site. Construction A of Stacks, Section 04WT views
an algebraic stack over `S` as an algebraic stack over `S'`, and Stacks 04X5 says that it is
bijective on 1-morphisms. The Deligne–Mumford and quasi-DM conditions of Stacks 04YW on a
1-morphism are preserved and reflected by that bijection
(`AlgebraicGeometry.Stack.isDM_changeBase_iff` and
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_changeBase_iff`), while the properties the
separated and quasi-separated conditions are built from pass between the two bases in one
direction only.

This file supplies the **quasi-separated** case in that one direction, which is the direction
Stacks 050L part (8) needs: from the smaller base `S` to the larger base `S'`.

As in the quasi-DM case, the proof has two halves. The comparison of the two renderings of the
relative diagonal *at the fixed base* `S'` holds at an **arbitrary** property of morphisms of
algebraic spaces, as
`AlgebraicGeometry.Stack.relativeProperty_relativeDiagonal_changeBaseHom_iff`. The other half is
the passage between the two bases, which for the every-étale-chart conditions is
`AlgebraicGeometry.Stack.hasRelativeProperty_smooth_changeBaseHom_iff`.
Quasi-separatedness of a 1-morphism of Stacks 04YW is not an every-étale-chart condition — it asks
for `AlgebraicGeometry.Space.IsQuasiCompact` and `AlgebraicGeometry.Space.IsQuasiSeparated` of the
represented base changes — so it needs its own passage, and that passage is
`AlgebraicGeometry.Space.isQuasiCompact_spacesOverSmallerBaseFunctor` together with
`AlgebraicGeometry.Space.isQuasiSeparated_spacesOverSmallerBaseFunctor`.

## Main results

* `AlgebraicGeometry.Stack.quasiSeparatedRelativeProperty_changeBaseHom`: the relative
  quasi-compact-and-quasi-separated condition of Stacks 04XB on a 1-morphism of categories fibred
  in groupoids passes from the base `S` to the larger base `S'` along Construction A.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_changeBase`: **the quasi-separated
  condition of Stacks 04YW passes along Construction A**, from the smaller base to the larger one.

## Implementation notes

The statement is an **implication and not an equivalence**, by design. The reflecting direction
would need the two space-level conditions to pass from the larger base to the smaller one along
the *same* functor, which is
`AlgebraicGeometry.Space.isQuasiCompact_spacesOverSmallerBaseFunctor_of`; part (8) needs only
the direction stated, and stating only that direction keeps the proof a single pass over the
quantifier.

The quantifiers are written out rather than taken through
`AlgebraicGeometry.Stack.HasRelativeProperty`, exactly as
`AlgebraicGeometry.Stack.relativeProperty_relativeDiagonal_changeBaseHom_iff` and
`AlgebraicGeometry.Stack.hasRelativeProperty_smooth_changeBaseHom_iff` do: that abbreviation
carries `[P.IsStableUnderBaseChange]` and `[P.IsLocalAtTarget …]` as instance arguments, which
are not provided for the conjunction of quasi-compactness and quasi-separatedness and which the
argument does not use.

Unlike the quasi-DM case no representability hypothesis is needed anywhere: the relative diagonal
of a 1-morphism of *algebraic* stacks is representable by algebraic spaces automatically
(Stacks 04XS part (1)), and the two conditions of Stacks 04XB are stated for an arbitrary
1-morphism.

## References

* [Stacks Project, Tag 03HE](https://stacks.math.columbia.edu/tag/03HE)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050L](https://stacks.math.columbia.edu/tag/050L)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- **The relative quasi-compact-and-quasi-separated condition passes to a larger base along
Construction A.** The two quantifications over scheme-valued points of the target match up by
`AlgebraicGeometry.Stack.exists_comp_p_eq_map_of_changeBase`, and on 2-fibre products by
`CategoryTheory.TwoFibreProductOver.fstEquivalenceOver_trans`, exactly as in
`AlgebraicGeometry.Stack.hasRelativeProperty_smooth_changeBaseHom_iff`; so the representing
algebraic space is the same object on both sides, living over the same scheme over `S`, and what
is left is that its structural morphism is quasi-compact and quasi-separated over `S'` as soon as
it is over `S`. That is
`AlgebraicGeometry.Space.isQuasiCompact_spacesOverSmallerBaseFunctor` together with
`AlgebraicGeometry.Space.isQuasiSeparated_spacesOverSmallerBaseFunctor`. -/
theorem quasiSeparatedRelativeProperty_changeBaseHom
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴)
    (hsmall : ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.IsQuasiCompact B S hS
            (algebraicSpaceMap B S hS U
              ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom ∧
          Space.IsQuasiSeparated B S hS
            (algebraicSpaceMap B S hS U
              ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom) :
    ∀ (U : BigFppfOver B S' hS')
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴).val.obj)
      (_hy : y ⋙ (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴).val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom)
          (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val.p
          (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴).val.p y
          (CatFiberedInGroupoids.homFunctor (changeBaseHom B S S' hS hS' g f)))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsQuasiCompact B S' hS'
          (algebraicSpaceMap B S' hS' U
            ((spacesOverSmallerBaseFunctor B U.left.1 S' U.left.2 hS' U.hom).obj
              ⟨F, hF⟩)).hom ∧
        Space.IsQuasiSeparated B S' hS'
          (algebraicSpaceMap B S' hS' U
            ((spacesOverSmallerBaseFunctor B U.left.1 S' U.left.2 hS' U.hom).obj
              ⟨F, hF⟩)).hom := by
  intro U' y hy' F hF hE'
  obtain ⟨E'⟩ := hE'
  obtain ⟨h₀, hy, hg⟩ := exists_comp_p_eq_map_of_changeBase B S S' hS hS' g 𝒴.val U' y hy'
  rw [← hg, Over.mapComp_eq] at E'
  have key := hsmall (Over.mk h₀) y hy F hF
    ⟨TwoFibreProductOver.fstEquivalenceOver_trans g hy f.hom.w E'⟩
  exact ⟨Space.isQuasiCompact_spacesOverSmallerBaseFunctor B U'.left.1 S U'.left.2 hS h₀
      S' hS' g U'.hom hg F hF key.1,
    Space.isQuasiSeparated_spacesOverSmallerBaseFunctor B U'.left.1 S U'.left.2 hS h₀
      S' hS' g U'.hom hg F hF key.2⟩

/-- **The quasi-separated condition of Stacks 04YW passes along Construction A**, from the base
`S` to the larger base `S'`: if a 1-morphism of algebraic stacks over `S` is quasi-separated, then
so is the 1-morphism over `S'` that the hom-bijection of Stacks 04X5 assigns to it.

The comparison at the fixed base `S'` is
`AlgebraicGeometry.Stack.relativeProperty_relativeDiagonal_changeBaseHom_iff` at the property
"quasi-compact and quasi-separated", and the passage between the two bases is
`AlgebraicGeometry.Stack.quasiSeparatedRelativeProperty_changeBaseHom` at the relative
diagonal. -/
theorem AlgebraicStacks.isQuasiSeparated_changeBase {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (hf : AlgebraicStacks.IsQuasiSeparated B S hS f) :
    AlgebraicStacks.IsQuasiSeparated B S' hS'
      (𝒳 := changeBaseAlgebraicStack B S S' hS hS' g 𝒳)
      (𝒴 := changeBaseAlgebraicStack B S S' hS hS' g 𝒴)
      (Bicategory.InducedBicategory.mkHom
        (algebraicStackConstructionHomEquiv B S S' hS hS' g 𝒳 𝒴 f).val) :=
  (AlgebraicStacks.isQuasiSeparated_iff_forall B S' hS' _).2
    ((relativeProperty_relativeDiagonal_changeBaseHom_iff B S S' hS hS' g
        (fun _ _ m => Space.IsQuasiCompact B S' hS' m.hom ∧
          Space.IsQuasiSeparated B S' hS' m.hom) f.hom).2
      (quasiSeparatedRelativeProperty_changeBaseHom B S S' hS hS' g
        (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)
        ((AlgebraicStacks.isQuasiSeparated_iff_forall B S hS f).1 hf)))

end AlgebraicGeometry.Stack

end
