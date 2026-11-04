module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFibreProductComparison

/-!
# The separation axioms of the comparison 1-morphism (Stacks 050H)

Let `f : 𝒳 ⟶ 𝒵`, `g : 𝒴 ⟶ 𝒵` and `h : 𝒵 ⟶ 𝒯` be 1-morphisms of algebraic stacks over a scheme
`S` in a big fppf site `B`, and let

```text
  i = AlgebraicGeometry.Stack.AlgebraicStacks.mapBase : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴
```

be the comparison 1-morphism. The module
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationFibreProductComparison` proves that `i` is a base
change of the relative diagonal `Δ_{𝒵/𝒯}`. Parts (2)–(7) of Stacks 050H
each name one of the conditions of Stacks 04XB, assert it for `Δ_{𝒵/𝒯}`, and conclude it for `i`;
so all six are the *same* statement — a condition of Stacks 04XB is stable under base change —
applied at six different properties of morphisms of algebraic spaces. That statement is proved
once here, and the six clauses are one line each.

## Main results

* `AlgebraicGeometry.Stack.prop_baseChange_of_isTwoFibreProduct`: a condition of Stacks 04XB is
  inherited by the projection of a 2-fibre product square, for an arbitrary property `P` of
  morphisms of algebraic spaces over `S` and with no hypothesis on `P` at all.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_mapBase`: **Stacks 050H**, part (2).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_mapBase`: **Stacks 050H**, part (3).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isUnramified_mapBase_of_isDM`: **Stacks 050H**,
  part (4).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyQuasiFinite_mapBase_of_isQuasiDM`:
  **Stacks 050H**, part (5).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isProper_mapBase_of_isSeparated`: **Stacks 050H**,
  part (6).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiCompactAndQuasiSeparated_mapBase`:
  **Stacks 050H**, part (7).

## Implementation notes

`AlgebraicGeometry.Stack.prop_baseChange_of_isTwoFibreProduct` is the statement of Stacks 045C
(`AlgebraicGeometry.Stack.hasRelativeProperty_baseChange`) with its two instance arguments on `P`
removed and the Stacks 04XB condition written out longhand. Both are needed, and neither
subsumes the other for the purpose at hand: `AlgebraicGeometry.Stack.HasRelativeProperty`
(**Stacks 03YK**) carries `CategoryTheory.MorphismProperty.IsStableUnderBaseChange` and
`CategoryTheory.MorphismProperty.IsLocalAtTarget` as instance arguments, as the source does,
so a *statement* about it cannot even be elaborated at a property for which those instances are
not in the library — and for properness, quasi-compactness, quasi-separatedness and local
quasi-finiteness of morphisms of algebraic spaces over `S` they are not. The conditions of
Stacks 04XB that `StacksFrontier.AlgebraicGeometry.Stacks.SeparationAxioms` and
`StacksFrontier.AlgebraicGeometry.Stacks.SeparatedMorphism` state the separation axioms with are
therefore written longhand, and this is the form of Stacks 045C that applies to them. The proof
is the one of Stacks 045C verbatim, and it uses neither instance: the two instances of the
Stacks 04XB condition have *the same* conclusion for the same algebraic space, so the only thing
to produce is the equivalence over the site that reindexes the representability witness, which is
`AlgebraicGeometry.Stack.nonempty_baseChangeEquivalenceOver`.

Part (1) of Stacks 050H is **not** proved here. Its representability half is Stacks 0302 applied
to `AlgebraicGeometry.Stack.AlgebraicStacks.mapBaseSquare`, for which the two representability
clauses of the algebraic stack conditions on `𝒵` and `𝒯` have to be unpacked and the universes of
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_baseChange` saturated; its *locally of
finite type* half needs part (2) of Stacks 04YQ, that `Δ_{𝒵/𝒯}` is locally of finite type, which
this library does not have. So **Stacks 050H is PARTIAL here, at parts (2)–(7)**.

## References

* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045C](https://stacks.math.columbia.edu/tag/045C)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w

/-- **Stacks 045C without the hypotheses on `P`.** Let `P` be any property of morphisms of
algebraic spaces over `S`. In a 2-fibre product square over a cospan `g : 𝒵 ⟶ 𝒴`, `f : 𝒳 ⟶ 𝒴` of
categories fibred in groupoids over the big fppf site of `S`, the projection to `𝒵` satisfies the
condition of Stacks 04XB for `P` as soon as `f` does.

This is `AlgebraicGeometry.Stack.hasRelativeProperty_baseChange` with the condition of Stacks
04XB written out, which is what makes it applicable to the separation axioms of Stacks 04YW: those
are stated at properties of morphisms of algebraic spaces for which the stability and locality
instances that `AlgebraicGeometry.Stack.HasRelativeProperty` asks for are not available. -/
theorem prop_baseChange_of_isTwoFibreProduct
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴) (g : 𝒵 ⟶ 𝒴)
    (R : Bicategory.TwoCommSq g f)
    (hR : Bicategory.IsTwoFibreProduct R)
    (hPf : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒵.val.obj)
      (_hz : z ⋙ 𝒵.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) R.pt.val.p 𝒵.val.p z
            (CatFiberedInGroupoids.homFunctor R.fst))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) := by
  intro U z hz F hF he
  refine hPf U (z ⋙ CatFiberedInGroupoids.homFunctor g)
    (by rw [Functor.assoc, CatFiberedInGroupoids.homFunctor_comp_p, hz]) F hF ?_
  obtain ⟨e⟩ := he
  obtain ⟨E⟩ := nonempty_baseChangeEquivalenceOver.{u, v, w} B S hS 𝒳 𝒴 𝒵 f g R hR U z hz
  exact ⟨E.symm.trans e⟩

namespace AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 𝒵 𝒯 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒵) (g : 𝒴 ⟶ 𝒵) (h : 𝒵 ⟶ 𝒯)

/-- **The transfer of a condition of Stacks 04XB from `Δ_{𝒵/𝒯}` to the comparison 1-morphism.**
This is `AlgebraicGeometry.Stack.prop_baseChange_of_isTwoFibreProduct` at the square of
`AlgebraicGeometry.Stack.AlgebraicStacks.mapBaseSquare`; parts (2)–(7) of Stacks 050H are its
six specialisations. -/
theorem prop_mapBase_of_prop_relativeDiagonal
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (twoFibreProduct B S hS h h).val.val.obj)
      (_hy : y ⋙ (twoFibreProduct B S hS h h).val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒵.val.val.p
            (twoFibreProduct B S hS h h).val.val.p y
            (CatFiberedInGroupoids.homFunctor
              (relativeDiagonal.{u, u, u + 1} B S hS 𝒵.val 𝒯.val h.hom)))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤
        (twoFibreProduct B S hS (f ≫ h) (g ≫ h)).val.val.obj)
      (_hz : z ⋙ (twoFibreProduct B S hS (f ≫ h) (g ≫ h)).val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (twoFibreProduct B S hS f g).val.val.p
            (twoFibreProduct B S hS (f ≫ h) (g ≫ h)).val.val.p z
            (CatFiberedInGroupoids.homFunctor (mapBase B S hS f g h).hom))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) :=
  prop_baseChange_of_isTwoFibreProduct.{u, u, u} B S hS P 𝒵.val
    (twoFibreProduct B S hS h h).val (twoFibreProduct B S hS (f ≫ h) (g ≫ h)).val
    (relativeDiagonal.{u, u, u + 1} B S hS 𝒵.val 𝒯.val h.hom) (mapCospan B S hS f g h).hom
    (mapBaseSquare B S hS f g h) (isTwoFibreProduct_mapBaseSquare B S hS f g h) hP

/-- **Stacks 050H, part (2).** If the relative diagonal `Δ_{𝒵/𝒯}` is quasi-separated in the sense
of Stacks 04XB, then so is the comparison 1-morphism `i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴`. -/
@[stacks 050H "part (2): quasi-separated"]
theorem isQuasiSeparated_mapBase
    (hΔ : Stack.IsQuasiSeparated.{u, u, u + 1} B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒵.val 𝒯.val h.hom)) :
    Stack.IsQuasiSeparated.{u, u, u + 1} B S hS (mapBase B S hS f g h).hom :=
  prop_mapBase_of_prop_relativeDiagonal B S hS f g h
    (fun _ _ m => Space.IsQuasiSeparated B S hS m.hom) hΔ

/-- **Stacks 050H, part (3).** If the relative diagonal `Δ_{𝒵/𝒯}` is separated in the sense of
Stacks 04XB, then so is the comparison 1-morphism `i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴`. -/
@[stacks 050H "part (3): separated"]
theorem isSeparated_mapBase
    (hΔ : Stack.IsSeparated.{u, u, u + 1} B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒵.val 𝒯.val h.hom)) :
    Stack.IsSeparated.{u, u, u + 1} B S hS (mapBase B S hS f g h).hom :=
  prop_mapBase_of_prop_relativeDiagonal B S hS f g h
    (fun _ _ m => Space.IsSeparated B S hS m.hom) hΔ

/-- **Stacks 050H, part (4).** If `h : 𝒵 ⟶ 𝒯` is Deligne–Mumford, then the comparison 1-morphism
`i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` is unramified in the sense of Stacks 04XB: `i` is a base change of
`Δ_{𝒵/𝒯}`, which is unramified by the definition of Stacks 04YW. -/
@[stacks 050H "part (4): unramified"]
theorem isUnramified_mapBase_of_isDM (hh : Stack.IsDM B S hS h) :
    ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤
        (twoFibreProduct B S hS (f ≫ h) (g ≫ h)).val.val.obj)
      (_hz : z ⋙ (twoFibreProduct B S hS (f ≫ h) (g ≫ h)).val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (twoFibreProduct B S hS f g).val.val.p
            (twoFibreProduct B S hS (f ≫ h) (g ≫ h)).val.val.p z
            (CatFiberedInGroupoids.homFunctor (mapBase B S hS f g h).hom))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.IsUnramified B S hS
          (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom :=
  prop_mapBase_of_prop_relativeDiagonal B S hS f g h
    (fun _ _ m => Space.IsUnramified B S hS m.hom) hh.2

/-- **Stacks 050H, part (5).** If `h : 𝒵 ⟶ 𝒯` is quasi-DM, then the comparison 1-morphism
`i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` is locally quasi-finite in the sense of Stacks 04XB. -/
@[stacks 050H "part (5): locally quasi-finite"]
theorem isLocallyQuasiFinite_mapBase_of_isQuasiDM (hh : IsQuasiDM B S hS h) :
    Stack.IsLocallyQuasiFinite.{u, u, u + 1} B S hS (mapBase B S hS f g h).hom :=
  prop_mapBase_of_prop_relativeDiagonal B S hS f g h
    (fun _ _ m => Space.IsLocallyQuasiFinite B S hS m.hom) hh

/-- **Stacks 050H, part (6).** If `h : 𝒵 ⟶ 𝒯` is separated, then the comparison 1-morphism
`i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` is proper in the sense of Stacks 04XB. -/
@[stacks 050H "part (6): proper"]
theorem isProper_mapBase_of_isSeparated (hh : IsSeparated B S hS h) :
    Stack.IsProper.{u, u, u + 1} B S hS (mapBase B S hS f g h).hom :=
  prop_mapBase_of_prop_relativeDiagonal B S hS f g h
    (fun _ _ m => Space.IsProper B S hS m.hom) hh

/-- **Stacks 050H, part (7).** If `h : 𝒵 ⟶ 𝒯` is quasi-separated, then the comparison 1-morphism
`i : 𝒳 ×_𝒵 𝒴 ⟶ 𝒳 ×_𝒯 𝒴` is quasi-compact and quasi-separated in the sense of Stacks 04XB. -/
@[stacks 050H "part (7): quasi-compact and quasi-separated"]
theorem isQuasiCompactAndQuasiSeparated_mapBase
    (hh : IsQuasiSeparated B S hS h) :
    Stack.IsQuasiCompact.{u, u, u + 1} B S hS (mapBase B S hS f g h).hom ∧
      Stack.IsQuasiSeparated.{u, u, u + 1} B S hS (mapBase B S hS f g h).hom :=
  ⟨prop_mapBase_of_prop_relativeDiagonal B S hS f g h
      (fun _ _ m => Space.IsQuasiCompact B S hS m.hom) hh.1,
    prop_mapBase_of_prop_relativeDiagonal B S hS f g h
      (fun _ _ m => Space.IsQuasiSeparated B S hS m.hom) hh.2⟩

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
