module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallySeparatedDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactMorphism

/-!
# Stacks 04Z0, part (2): quasi-separatedness and the first two diagonals

Let `S` be a scheme contained in a big fppf site `B` and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S`, with no representability assumption. Part (2) of Stacks 04Z0 says that
`f` is quasi-separated, in the sense of Definition 04YW, exactly when its first and second
relative diagonals `Δ_{f,1}` and `Δ_{f,2}` are quasi-compact. This file proves it.

Definition 04YW asks of a quasi-separated `f` that `Δ_{f,1}` be quasi-compact *and*
quasi-separated, in the relative sense of Properties of Stacks, Section 04XB. So the statement
splits into two halves. The first conjunct is the Section 04XB quasi-compactness of `Δ_{f,1}`,
which Stacks 050T identifies with quasi-compactness in the sense of Definition 050U — every base
change by a quasi-compact algebraic stack is a quasi-compact algebraic stack — because `Δ_{f,1}` is
representable by algebraic spaces by part (1) of Stacks 04XS. The second conjunct is the content:
Section 04XB quasi-separatedness of `Δ_{f,1}` is Section 04XB quasi-compactness of `Δ_{f,2}`,
which is part (2) of Stacks 04YZ, and 050T turns that into Definition 050U again.

## Main results

* `AlgebraicGeometry.Stack.isQuasiSeparated_iff_isQuasiCompactMorphism_diagonals`:
  **Stacks 04Z0**, part (2).
* `AlgebraicGeometry.Stack.isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated`: **Stacks 04YZ**,
  part (2) — for a 1-morphism representable by algebraic spaces, Section 04XB quasi-separatedness
  is Section 04XB quasi-compactness of the relative diagonal.
* `AlgebraicGeometry.Stack.isQuasiCompact_relativeDiagonal_baseChange_iff_isQuasiSeparated`: the
  two conditions agree after base change to a scheme-valued point of the target, which is the step
  Stacks' own proof of Stacks 04YT performs.
* `AlgebraicGeometry.Stack.isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated_representingMap`:
  the same equivalence over a *represented* base.

## Implementation notes

The three lemmas before the main result are the sibling at quasi-separatedness of
`StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE` and
`StacksFrontier.AlgebraicGeometry.Stacks.LocallySeparatedDiagonal`, and every ingredient of those
files is reused unchanged: the swap reconciliation of the two 2-fibre products `𝒴' ×_𝒴 𝒳` and
`𝒳 ×_𝒴 𝒴'`, the slice site of a scheme as an algebraic stack, and the lift of a scheme-valued
point of `𝒳 ×_{f, 𝒴, f} 𝒳` through the right-hand leg of the square of Stacks 04YR over the site.
What changes is the property of morphisms of algebraic spaces the conditions are read at: being
quasi-compact instead of being a closed immersion, hence quasi-separatedness instead of
separatedness, by part (3) of Stacks 03HL.

Being quasi-separated for a morphism of algebraic spaces *is* its relative diagonal being
quasi-compact — `AlgebraicGeometry.Space.IsQuasiSeparated` is an abbreviation for exactly that —
so the represented-base lemma is three applications and no mathematics: the bridge of Section
04XB, then `AlgebraicGeometry.Stack.representingMap_relativeDiagonal`, then that definition.

Unlike the closed-immersion and immersion siblings this file needs no property packaged privately
and no hypothesis-free form of the bridge. `AlgebraicGeometry.Space.quasiCompactProperty` carries
both instance arguments of `AlgebraicGeometry.Stack.HasRelativeProperty` — base-change stability
and fppf locality at the target, the latter being Stacks 041L composed with
`AlgebraicGeometry.Space.fppfPrecoverage_le_fpqcPrecoverage` — so
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap` applies directly, and
`AlgebraicGeometry.Space.quasiSeparatedProperty` is equally public, with Stacks 03KL and
041N behind it. That is why the three transport lemmas of Section 04XB can be applied at a public
property here where the locally-separated sibling had to package one.

The index universe of the fppf precoverage occurs only inside the instance argument of
`AlgebraicGeometry.Stack.HasRelativeProperty`, so it must be pinned where that bridge is applied:
the `have` in the represented-base lemma fixes it at `u`, and removing that `have` reports
`contains universe level metavariables`, which reads as anything but a universe problem. For the
same reason `AlgebraicGeometry.Stack.relativeDiagonal` is written `.{u, u, u + 1}` at every term
occurrence.

**The library's `AlgebraicGeometry.Stack.isQuasiSeparated_iff_isQuasiCompact_relativeDiagonal`
(Stacks 04YT, parts (1) and (2)) is not an input here**, and the module is not imported. That
theorem reads condition (1) of Stacks 04YT as Definition 04YW, while part (2) of Stacks 04Z0 needs
it read as the Section 04XB predicate — Section 04XB quasi-separatedness of `Δ_{f,1}` rather than
Definition 04YW quasi-separatedness of `Δ_{f,1}`. The two agree for a representable 1-morphism,
but only as a consequence of the equivalence proved here, so this file proves the Section 04XB
reading from the same ingredients rather than deriving it.

**The absolute 2-fibre-product form of the base-change comparison is not used**, for the reason
recorded in `StacksFrontier.AlgebraicGeometry.Stacks.SeparatedDiagonalTFAE`: it reads a relative
diagonal as a base change along the absolute diagonal of a product, which is a different cospan.
The square used is the relative one of
`StacksFrontier.AlgebraicGeometry.Stacks.DiagonalBaseChangeSquare`, with the order of its two
factors
corrected by the swap.

**Parts (1), (3) and (4) of Stacks 04Z0 are not proved here and their keys are not claimed.**
Part (1), separatedness, needs Stacks 04XW — that a universally closed morphism of algebraic
spaces is quasi-compact — and part (2) of Stacks 04YQ for an *arbitrary* 1-morphism of algebraic
stacks, which rests on Stacks 04XR; part (3), quasi-DM, needs part (5) of Stacks 04YQ; and
part (4), DM, needs part (2) of Stacks 04YQ together with Stacks 05W6. None of those five results
is available in this library.

## References

* [Stacks Project, Tag 04Z0](https://stacks.math.columbia.edu/tag/04Z0)
* [Stacks Project, Tag 04YZ](https://stacks.math.columbia.edu/tag/04YZ)
* [Stacks Project, Tag 04YT](https://stacks.math.columbia.edu/tag/04YT)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XS](https://stacks.math.columbia.edu/tag/04XS)
* [Stacks Project, Tag 03HL](https://stacks.math.columbia.edu/tag/03HL)
* [Stacks Project, Tag 041L](https://stacks.math.columbia.edu/tag/041L)
* [Stacks Project, Tag 050T](https://stacks.math.columbia.edu/tag/050T)
* [Stacks Project, Tag 050U](https://stacks.math.columbia.edu/tag/050U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section SchemePoint

variable (𝒰 𝒴' : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (f' : 𝒰 ⟶ 𝒴')
    (A H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eA : StacksRepresentableCFG.EquivalenceOver
      𝒰.val.p (presheafOfCategories (A ⋙ typeToCat)).p)
    (eH : StacksRepresentableCFG.EquivalenceOver
      𝒴'.val.p (presheafOfCategories (H ⋙ typeToCat)).p)
    (hA : IsAlgebraicSpace B S hS A) (hH : IsAlgebraicSpace B S hS H)
    [(twoFibreProductStructureFunctor B S hS 𝒰 𝒰 𝒴' f' f').IsFibered]
    (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (eT : StacksRepresentableCFG.EquivalenceOver
      (twoFibreProductStructureFunctor B S hS 𝒰 𝒰 𝒴' f' f')
      (presheafOfCategories (T ⋙ typeToCat)).p)
    (hT : IsAlgebraicSpace B S hS T)

include hA hH T eT hT in
/-- **Part (2) of Stacks 04YZ over a represented base.** Let `f' : 𝒰 ⟶ 𝒴'` be a 1-morphism of
categories fibred in groupoids over the big fppf site of `S` with `𝒰` and `𝒴'` representable by
algebraic spaces `A` and `H`, and let `h : A ⟶ H` be the morphism of algebraic spaces it induces.
Then the relative diagonal of `f'` is quasi-compact in the sense of Stacks 04XB exactly when `h`
is quasi-separated.

This is the sibling of
`AlgebraicGeometry.Stack.isClosedImmersion_relativeDiagonal_iff_isSeparated_representingMap` and
of `AlgebraicGeometry.Stack.isImmersion_relativeDiagonal_iff_isLocallySeparated_representingMap`
at quasi-separatedness, and it is cheaper than either: the bridge of Stacks 04XB at
`AlgebraicGeometry.Space.quasiCompactProperty` is
`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`, because that property has
both of its instance arguments in this library, and after
`AlgebraicGeometry.Stack.representingMap_relativeDiagonal` quasi-separatedness of `h` *is* its
relative diagonal being quasi-compact, by part (3) of Stacks 03HL. -/
theorem isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated_representingMap
    (hΔ : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒴' f').hom) :
    IsQuasiCompact B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒴' f') ↔
      Space.IsQuasiSeparated B S hS (representingMap B S hS 𝒰 𝒴' A H eA eH f') :=
  have : (Space.quasiCompactProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isQuasiCompact_isLocalAtTarget_fppf B S hS
  (hasRelativeProperty_iff_prop_representingMap B S hS
      (Space.quasiCompactProperty B S hS)
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒰 𝒴' f') hΔ A T hA hT eA eT).trans
    (prop_representingMap_relativeDiagonal_iff B S hS 𝒰 𝒴' f' A H eA eH T eT
      (Space.quasiCompactProperty B S hS) hA hH hT)

end SchemePoint

section Bridge

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.val.obj)
    (hy : y ⋙ 𝒴.val.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p 𝒴.val.val.p y
        (CatFiberedInGroupoids.homFunctor f.hom))
      (presheafOfCategories (F ⋙ typeToCat)).p)

include hF e in
/-- **The two conditions of part (2) of Stacks 04YZ agree after base change to a scheme-valued
point.** Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `y` be a scheme-valued
point of `𝒴` over `U`, and let `F` be an algebraic space over `U` representing the base change of
`f` along `y`. Then the relative diagonal of the base change `𝒳 ×_𝒴 U ⟶ U` is quasi-compact in the
sense of Stacks 04XB exactly when the structural morphism of `F`, read over `S`, is
quasi-separated.

This is the sibling of
`AlgebraicGeometry.Stack.isImmersion_relativeDiagonal_baseChange_iff_isLocallySeparated` and is
assembled the same way:
`AlgebraicGeometry.Stack.isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated_representingMap` —
the equivalence over a *represented* base — read at the base change, which is legitimate because
of the swap reconciliation
`AlgebraicGeometry.Stack.prop_representingMap_twoFibreProductFst_iff`: the base change as the
relative property of Stacks 04XB presents it has the point as its first factor, while the
base-change square for the diagonal has the source as its first factor. The representing presheaf
of the base change over `S` is the lower-shriek extension of `F`, by Stacks 03I5, and its
structural morphism is the morphism of representing presheaves induced by the projection, by
`AlgebraicGeometry.Stack.representingMap_relocalizeFibre`. -/
theorem isQuasiCompact_relativeDiagonal_baseChange_iff_isQuasiSeparated :
    IsQuasiCompact B S hS (relativeDiagonal.{u, u, u + 1} B S hS
        (twoFibreProductAlgebraicStack B S hS f
          (schemeSliceStackMap B S hS U y hy)).val
        (schemeSliceStack B S hS U).val
        (twoFibreProductSquareAlgebraicStacks B S hS f
          (schemeSliceStackMap B S hS U y hy)).snd.hom) ↔
      Space.IsQuasiSeparated B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom := by
  have hri : MorphismProperty.RespectsIso (Space.quasiSeparatedProperty B S hS) :=
    (Space.isQuasiSeparated_isStableUnderBaseChange B S hS).respectsIso
  set 𝒴' : AlgebraicStacks.{u, w} B S hS := schemeSliceStack B S hS U
  set g : 𝒴' ⟶ 𝒴 := schemeSliceStackMap B S hS U y hy
  set Q := twoFibreProductAlgebraicStack B S hS f g
  set f' := (twoFibreProductSquareAlgebraicStacks B S hS f g).snd
  set A := (OverShriek.relocalizePresheafFunctor U.hom).obj F
  have hA : IsAlgebraicSpace B S hS A :=
    isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom F hF
  set eP := relocalizeFibreEquivalence B S hS U f.hom y F e
  set eQ := (twoFibreProductSwapEquivalenceOver B S hS f.hom g.hom).symm.trans eP
  have hQrep : IsRepresentableByAlgebraicSpace B S hS Q.val := ⟨A, hA, ⟨eQ⟩⟩
  have hfrep : IsRepresentableByAlgebraicSpaces B S hS f'.hom.hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS 𝒴'.property hQrep f'.hom
  obtain ⟨T, hT, ⟨eT⟩⟩ := isRepresentableByAlgebraicSpace_twoFibreProduct B S hS
    𝒴'.val Q.val Q.val f'.hom.hom f'.hom.hom hfrep hQrep
  have hΔ : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS Q.val 𝒴'.val f'.hom).hom :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicStack.{u, w} B S hS
      (isAlgebraicStack_of_isRepresentableByAlgebraicSpace.{u, w} B S hS _ ⟨T, hT, ⟨eT⟩⟩)
      hQrep (relativeDiagonal.{u, u, u + 1} B S hS Q.val 𝒴'.val f'.hom)
  let _hfib : (twoFibreProductStructureFunctor B S hS Q.val Q.val 𝒴'.val
      f'.hom f'.hom).IsFibered :=
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
      f'.hom f'.hom).pt.property.isFibered
  refine Iff.trans (isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated_representingMap B S hS
    Q.val 𝒴'.val f'.hom A (yoneda.obj U) eQ (schemeSliceEquivalenceOver B S hS U) hA
    (isAlgebraicSpace_yoneda B S hS U) T eT hT hΔ) ?_
  refine Iff.trans (Iff.symm (prop_representingMap_twoFibreProductFst_iff B S hS f.hom g.hom A
    eP eQ (yoneda.obj U) (schemeSliceEquivalenceOver B S hS U)
    (Space.quasiSeparatedProperty B S hS) hA (isAlgebraicSpace_yoneda B S hS U))) ?_
  exact Iff.trans (Iff.of_eq (congrArg (fun k =>
      Space.quasiSeparatedProperty B S hS (ObjectProperty.homMk k :
        (⟨A, hA⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩))
      (representingMap_relocalizeFibre B S hS U f.hom y F e hy)))
    (Iff.symm (prop_algebraicSpaceMap_iff B S hS
      (Space.quasiSeparatedProperty B S hS) U F hF))

end Bridge

section Equivalence

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)

include hf in
/-- **Part (2) of Stacks 04YZ.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` which is
representable by algebraic spaces has quasi-compact relative diagonal, in the relative sense of
Stacks 04XB, exactly when `f` is quasi-separated in that same sense.

This is condition (1) of Stacks 04YT read as the Section 04XB predicate, which is how the source
states it — its proof opens *"the statements `f` is quasi-separated, `Δ_f` is quasi-compact … refer
to the notions defined in Properties of Stacks, Section 04XB"*. The library's
`AlgebraicGeometry.Stack.isQuasiSeparated_iff_isQuasiCompact_relativeDiagonal` reads condition (1)
as Definition 04YW instead, so the two are different statements; see the implementation notes.

Both directions go through the base change of `f` to a scheme-valued point, where
`AlgebraicGeometry.Stack.isQuasiCompact_relativeDiagonal_baseChange_iff_isQuasiSeparated` applies.
For the forward direction the base change of `Δ_f` is read off the square of Stacks 04YR over the
site, by Stacks 045C in the form `AlgebraicGeometry.Stack.relativeProperty_baseChange`. For the
backward direction the scheme-valued point of `𝒳 ×_{f, 𝒴, f} 𝒳` at which the condition is tested
is first lifted through the right-hand leg of that square, by
`AlgebraicGeometry.Stack.exists_schemePoint_relativeDiagonal_baseChange`. -/
theorem isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated :
    IsQuasiCompact B S hS (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom) ↔
      IsQuasiSeparated B S hS f.hom := by
  constructor
  · rintro h U y hy F hF ⟨e⟩
    refine (isQuasiCompact_relativeDiagonal_baseChange_iff_isQuasiSeparated B S hS f U y hy
      F hF e).mp ?_
    exact relativeProperty_baseChange.{u, u, u + 1} B S hS (Space.quasiCompactProperty B S hS)
      𝒳.val (twoFibreProduct B S hS 𝒴.val 𝒳.val 𝒳.val f.hom.hom f.hom.hom) _
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)
      (diagonalMapDiag B S hS f (schemeSliceStackMap B S hS U y hy))
      (diagonalBaseChangeSquare B S hS f (schemeSliceStackMap B S hS U y hy))
      (isTwoFibreProduct_diagonalBaseChangeSquare B S hS f
        (schemeSliceStackMap B S hS U y hy)) h
  · rintro h W z hz G hG ⟨eG⟩
    have hy : (z ⋙ TwoFibreProductOver.fst 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p
        f.hom.hom.toFunctor f.hom.hom.toFunctor ⋙ f.hom.hom.toFunctor) ⋙ 𝒴.val.val.p =
        Over.map W.hom :=
      (congrArg (fun k => (z ⋙ TwoFibreProductOver.fst 𝒳.val.val.p 𝒳.val.val.p 𝒴.val.val.p
          f.hom.hom.toFunctor f.hom.hom.toFunctor) ⋙ k) f.hom.hom.w).trans
        ((congrArg (fun k => z ⋙ k) TwoFibreProductOver.fst_comp_eq).trans hz)
    obtain ⟨F₀, hF₀, ⟨e₀⟩⟩ := hf W _ hy
    have hbr := (isQuasiCompact_relativeDiagonal_baseChange_iff_isQuasiSeparated B S hS f W _ hy
      F₀ hF₀ e₀).mpr (h W _ hy F₀ hF₀ ⟨e₀⟩)
    obtain ⟨zz, hzz, ⟨E⟩⟩ := exists_schemePoint_relativeDiagonal_baseChange B S hS f W z hz
      _ hy rfl
    exact hbr W zz hzz G hG ⟨E.trans eG⟩

end Equivalence

section Stacks04Z0

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 04Z0, part (2).** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` — with no
representability hypothesis — is quasi-separated, in the sense of Definition 04YW, if and only if
its first relative diagonal `Δ_{f,1} : 𝒳 ⟶ 𝒳 ×_{f, 𝒴, f} 𝒳` and its second relative diagonal
`Δ_{f,2}`, the relative diagonal of `Δ_{f,1}`, are both quasi-compact in the sense of
Definition 050U.

Definition 04YW is the conjunction, at every algebraic space representing a base change of
`Δ_{f,1}` along a scheme-valued point, of quasi-compactness and quasi-separatedness of the
structural morphism, so the left-hand side splits as Section 04XB quasi-compactness of `Δ_{f,1}`
together with Section 04XB quasi-separatedness of `Δ_{f,1}`. Part (2) of Stacks 04YZ, which is
`AlgebraicGeometry.Stack.isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated` applied to
`Δ_{f,1}`, replaces the second of those by Section 04XB quasi-compactness of `Δ_{f,2}`; and
Stacks 050T, `AlgebraicGeometry.Stack.isQuasiCompact_iff_baseChange_quasiCompact`, replaces
Section 04XB quasi-compactness of each diagonal by Definition 050U quasi-compactness, which is the
form the statement asks for. Both diagonals are representable by algebraic spaces by part (1) of
Stacks 04XS, so neither application needs a hypothesis. -/
@[stacks 04Z0 "quasi_separated"]
theorem isQuasiSeparated_iff_isQuasiCompactMorphism_diagonals (f : 𝒳 ⟶ 𝒴) :
    AlgebraicStacks.IsQuasiSeparated B S hS f ↔
      (IsQuasiCompactMorphism B S hS (relativeDiagonalAlgebraicStacks B S hS f) ∧
        IsQuasiCompactMorphism B S hS (relativeDiagonalAlgebraicStacks B S hS
          (relativeDiagonalAlgebraicStacks B S hS f))) := by
  have key : ∀ {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (g : 𝒳 ⟶ 𝒴),
      IsQuasiCompact B S hS (relativeDiagonalAlgebraicStacks B S hS g).hom ↔
        IsQuasiCompactMorphism B S hS (relativeDiagonalAlgebraicStacks B S hS g) := fun g =>
    isQuasiCompact_iff_baseChange_quasiCompact B S hS _
      (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS g)
  have h₃ := isQuasiCompact_relativeDiagonal_iff_isQuasiSeparated B S hS
    (relativeDiagonalAlgebraicStacks B S hS f)
    (isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)
  exact (and_congr (key f).symm ((key _).symm.trans h₃)).symm

end Stacks04Z0

end AlgebraicGeometry.Stack

end
