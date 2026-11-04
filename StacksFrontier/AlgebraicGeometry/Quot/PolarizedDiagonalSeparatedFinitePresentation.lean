module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedAlgebraicity.IsomSpaceAffine
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedAlgebraicity.QuasiSeparatedOfAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.LimitPreservingFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalIsomSpace

/-!
# The diagonal of `𝒫olarized`, reduced to its isomorphism spaces (Stacks 0DPT)

**Stacks 0DPT**: the diagonal `Δ : 𝒫olarized ⟶ 𝒫olarized ×_{Spec(ℤ)} 𝒫olarized` is separated and
of finite presentation. Both are read as in Properties of Stacks, Section 04XB, at
`AlgebraicGeometry.PolarizedAlgebraicity.polarizedAlgebraicStackOf B hS hT h`, the object of
Stacks 0DPU. That object takes `h`, the algebraicity of `𝒫olarized` (Quot, Theorem 0D4X).

## The argument

The base change of `Δ` along a scheme-valued point `(υ, χ, α)` over `U` is the isomorphism
space `Isom_𝒫(υ, χ) ⟶ U`
(`AlgebraicGeometry.Stack.prop_algebraicSpaceMap_relativeDiagonal_iff_isomSpace`). So
separatedness of `Δ` is separatedness of every `Isom_𝒫(υ, χ) ⟶ U`, and quasi-compactness of `Δ`
is quasi-compactness of every `Isom_𝒫(υ, χ) ⟶ U`. These are the second and the last two
paragraphs of the source's proof. Both hold because `Isom_𝒫(υ, χ)` is represented by a scheme
affine over `U`
(`AlgebraicGeometry.PolarizedAlgebraicity.isSeparated_relocalizeToYoneda_polarizedIsomSpace` and
`AlgebraicGeometry.PolarizedAlgebraicity.isQuasiCompact_relocalizeToYoneda_polarizedIsomSpace`,
from the corepresenting algebras of the proof of Stacks 0D42). This replaces the source's
comparison with `Isom_U(Y, X)` (Stacks 0DPN, 0DPP, 0DLW) and its Hilbert polynomial bound over
Noetherian bases (Stacks 0BEM, 0B9T, 0DPQ, 0DPR).

Local finite presentation is the first paragraph of the source's proof, and needs only `h`:
`𝒫olarized` is limit preserving (Stacks 0D43), so `𝒫olarized → Spec(ℤ)` is locally of finite
presentation (Stacks 0CMY,
`isLocallyOfFinitePresentation_structureMorphism_polarizedAlgebraicStackOf`), hence locally of
finite type, so its diagonal is locally of finite presentation (Stacks 0CMG). A representable
1-morphism that is locally of finite presentation is limit preserving on objects (Stacks 0CMY),
which is the condition of Stacks 04XB. This is the source's route through Stacks 0CMW and 0CMY.
Quasi-separatedness of `Δ` follows from separatedness.

## Main results

* `isLocallyOfFinitePresentation_diagonal_polarizedAlgebraicStack`: the local finite
  presentation clause, from `h`.
* `isSeparated_relativeDiagonal_polarizedAlgebraicStack_of_isSeparated_isomSpace`:
  separatedness of `Δ`, from `h` and `hsep`.
* `isQuasiCompact_relativeDiagonal_polarizedAlgebraicStack_of_isomSpace`: quasi-compactness of
  `Δ`, from `h` and `hqc`.
* `isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_polarizedAlgebraicStack_of`:
  Stacks 0DPT from `h` alone; its variant with suffix `_of_isomSpace` takes `hsep` and `hqc`.

## References

* [Stacks Project, Tag 0DPT](https://stacks.math.columbia.edu/tag/0DPT)
* [Stacks Project, Tag 0D43](https://stacks.math.columbia.edu/tag/0D43)
* [Stacks Project, Tag 0CMW](https://stacks.math.columbia.edu/tag/0CMW)
* [Stacks Project, Tag 0CMY](https://stacks.math.columbia.edu/tag/0CMY)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 0D42](https://stacks.math.columbia.edu/tag/0D42)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open PolarizedAlgebraicity

universe u w

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S) (hT : IsTerminal (B.obj hS))

/-- **The diagonal of `𝒫olarized` is locally of finite presentation**, the local finite
presentation clause of Stacks 0DPT, read as in Properties of Stacks, Section 04XB: every
algebraic space representing a base change of `Δ : 𝒫olarized ⟶ 𝒫olarized ×_{Spec(ℤ)} 𝒫olarized`
along a scheme-valued point is locally of finite presentation. Given that `𝒫olarized` is algebraic
(`h`, Quot, Theorem 0D4X), `𝒫olarized → Spec(ℤ)` is locally of finite presentation (Stacks 0D43
and 0CMY), so locally of finite type, hence its diagonal is locally of finite presentation
(Stacks 0CMG); a representable 1-morphism locally of finite presentation is limit preserving on
objects (Stacks 0CMY), which is the condition of Stacks 04XB. -/
theorem isLocallyOfFinitePresentation_diagonal_polarizedAlgebraicStack
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (polarizedStackUnconditional B hS hT).val)
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤
      (Stack.AlgebraicStacks.twoFibreProduct B S hS
        (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h))
        (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h))).val.val.obj)
    (hy : y ⋙ (Stack.AlgebraicStacks.twoFibreProduct B S hS
        (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h))
        (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h))).val.val.p =
      Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (hE : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) (polarizedAlgebraicStackOf B hS hT h).val.val.p
        (Stack.AlgebraicStacks.twoFibreProduct B S hS
          (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h))
          (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h))).val.val.p y
        (CatFiberedInGroupoids.homFunctor (Stack.AlgebraicStacks.relativeDiagonal B S hS
          (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h))).hom))
      (presheafOfCategories (F ⋙ typeToCat)).p)) :
    Space.IsLocallyOfFinitePresentation B S hS
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom := by
  let f := Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h)
  have hΔ := Stack.AlgebraicStacks.isLocallyOfFinitePresentation_relativeDiagonal B S hS
    f (Stack.AlgebraicStacks.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      (isLocallyOfFinitePresentation_structureMorphism_polarizedAlgebraicStackOf B hS hT h))
  exact (Stack.isLimitPreservingOnObjects_iff_isLocallyOfFinitePresentation B S hS
    _ _ (Stack.AlgebraicStacks.relativeDiagonal B S hS f).hom
    (Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS f)).1
    (Stack.AlgebraicStacks.isLimitPreservingOnObjects_of_isLocallyOfFinitePresentation B S
      hS _ hΔ) U y hy F hF hE

/-- **Stacks 0DPT, separatedness, from that of `Isom_𝒫(υ, χ)`.** Given that `𝒫olarized` is
algebraic (`h`, Quot, Theorem 0D4X) and that `Isom_𝒫(υ, χ) ⟶ U` is separated for every pair of
objects of `𝒫olarized` over a common `U` (`hsep`, the second paragraph of the source's proof), the
diagonal of `𝒫olarized` is separated in the sense of Stacks 04XB. -/
theorem isSeparated_relativeDiagonal_polarizedAlgebraicStack_of_isSeparated_isomSpace
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (polarizedStackUnconditional B hS hT).val)
    (hsep : ∀ (U : BigFppfOver B S hS)
      (υ χ : (polarizedStackUnconditional B hS hT).val.p.Fiber U),
      letI : (polarizedStackUnconditional B hS hT).val.p.IsFibered :=
        (polarizedStackUnconditional B hS hT).isFiberedInGroupoids.isFibered
      Space.IsSeparated B S hS (OverShriek.relocalizeToYoneda U.hom
        (Stack.isomSpace B S hS (polarizedStackUnconditional B hS hT) U υ χ))) :
    Stack.IsSeparated B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS (polarizedAlgebraicStackOf B hS hT h).val
        (Stack.schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h)).hom) := by
  intro U y hy F hF hE
  have := Space.isSeparated_respectsIso B S hS
  exact (Stack.prop_algebraicSpaceMap_relativeDiagonal_iff_isomSpace B S hS
    (@Space.IsSeparated B S hS)
    (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h))
    (Stack.faithful_schemeStack_p.{u, w} B S hS) U y hy F hF hE).2 (hsep _ _ _)

/-- **Stacks 0DPT, quasi-compactness, from that of `Isom_𝒫(υ, χ)`.** Given that `𝒫olarized` is
algebraic (`h`, Quot, Theorem 0D4X) and that `Isom_𝒫(υ, χ) ⟶ U` is quasi-compact for every pair
of objects of `𝒫olarized` over a common `U` (`hqc`, the last two paragraphs of the source's
proof), the diagonal of `𝒫olarized` is quasi-compact in the sense of Stacks 04XB. -/
theorem isQuasiCompact_relativeDiagonal_polarizedAlgebraicStack_of_isomSpace
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (polarizedStackUnconditional B hS hT).val)
    (hqc : ∀ (U : BigFppfOver B S hS)
      (υ χ : (polarizedStackUnconditional B hS hT).val.p.Fiber U),
      letI : (polarizedStackUnconditional B hS hT).val.p.IsFibered :=
        (polarizedStackUnconditional B hS hT).isFiberedInGroupoids.isFibered
      Space.IsQuasiCompact B S hS (OverShriek.relocalizeToYoneda U.hom
        (Stack.isomSpace B S hS (polarizedStackUnconditional B hS hT) U υ χ))) :
    Stack.IsQuasiCompact B S hS
      (Stack.relativeDiagonal.{u, u, u + 1} B S hS (polarizedAlgebraicStackOf B hS hT h).val
        (Stack.schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h)).hom) := by
  intro U y hy F hF hE
  have : MorphismProperty.RespectsIso (@Space.IsQuasiCompact B S hS) :=
    MorphismProperty.RespectsIso.of_respects_arrow_iso _ (fun f g e hf =>
      Space.isQuasiCompact_of_arrowIso B S hS f.hom g.hom e.hom.left e.hom.right
        e.hom.w hf)
  exact (Stack.prop_algebraicSpaceMap_relativeDiagonal_iff_isomSpace B S hS
    (@Space.IsQuasiCompact B S hS)
    (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h))
    (Stack.faithful_schemeStack_p.{u, w} B S hS) U y hy F hF hE).2 (hqc _ _ _)

/-- **Stacks 0DPT, from the isomorphism spaces.** Given that `𝒫olarized` is algebraic (`h`,
Quot, Theorem 0D4X) and that `Isom_𝒫(υ, χ) ⟶ U` is separated (`hsep`) and quasi-compact (`hqc`)
for every pair of objects of `𝒫olarized` over a common `U`, the diagonal
`Δ : 𝒫olarized ⟶ 𝒫olarized ×_{Spec(ℤ)} 𝒫olarized` is separated and of finite presentation, both
in the sense of Stacks 04XB. The local finite presentation of `Δ` is the first paragraph of the
source's proof (Stacks 0D43, 0CMW, 0CMY) and needs only `h`.

The base is any terminal object of the site, which is `Spec(ℤ)` up to unique isomorphism. -/
theorem isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_polarizedAlgebraicStack_of_isomSpace
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (polarizedStackUnconditional B hS hT).val)
    (hsep : ∀ (U : BigFppfOver B S hS)
      (υ χ : (polarizedStackUnconditional B hS hT).val.p.Fiber U),
      letI : (polarizedStackUnconditional B hS hT).val.p.IsFibered :=
        (polarizedStackUnconditional B hS hT).isFiberedInGroupoids.isFibered
      Space.IsSeparated B S hS (OverShriek.relocalizeToYoneda U.hom
        (Stack.isomSpace B S hS (polarizedStackUnconditional B hS hT) U υ χ)))
    (hqc : ∀ (U : BigFppfOver B S hS)
      (υ χ : (polarizedStackUnconditional B hS hT).val.p.Fiber U),
      letI : (polarizedStackUnconditional B hS hT).val.p.IsFibered :=
        (polarizedStackUnconditional B hS hT).isFiberedInGroupoids.isFibered
      Space.IsQuasiCompact B S hS (OverShriek.relocalizeToYoneda U.hom
        (Stack.isomSpace B S hS (polarizedStackUnconditional B hS hT) U υ χ))) :
    Stack.IsSeparated B S hS
        (Stack.relativeDiagonal.{u, u, u + 1} B S hS (polarizedAlgebraicStackOf B hS hT h).val
        (Stack.schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h)).hom) ∧
      Stack.AlgebraicStacks.IsRelativelyFinitePresentation B S hS
        (Stack.AlgebraicStacks.relativeDiagonal B S hS
          (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h))) :=
  ⟨isSeparated_relativeDiagonal_polarizedAlgebraicStack_of_isSeparated_isomSpace B hS hT h hsep,
    Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_algebraicStacks B S hS _,
    fun U y hy F hF hE =>
      ⟨isLocallyOfFinitePresentation_diagonal_polarizedAlgebraicStack B hS hT h U y hy F hF hE,
        isQuasiCompact_relativeDiagonal_polarizedAlgebraicStack_of_isomSpace B hS hT h hqc
          U y hy F hF hE,
        Space.isQuasiSeparated_of_isSeparated B S hS
          (isSeparated_relativeDiagonal_polarizedAlgebraicStack_of_isSeparated_isomSpace B hS hT h
            hsep U y hy F hF hE)⟩⟩

/-- **Stacks 0DPT, from the algebraicity of `𝒫olarized`.** Given that `𝒫olarized` is algebraic
(`h`, Quot, Theorem 0D4X), its diagonal `Δ : 𝒫olarized ⟶ 𝒫olarized ×_{Spec(ℤ)} 𝒫olarized` is
separated and of finite presentation, both in the sense of Stacks 04XB. Local finite presentation
is the first paragraph of the source's proof (Stacks 0D43, 0CMW, 0CMY). Separatedness and
quasi-compactness hold because every `Isom_𝒫(υ, χ)` is represented by a scheme affine over `U`
(from the proof of Stacks 0D42).

The base is any terminal object of the site, which is `Spec(ℤ)` up to unique isomorphism. -/
theorem isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_polarizedAlgebraicStack_of
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (polarizedStackUnconditional B hS hT).val) :
    Stack.IsSeparated B S hS
        (Stack.relativeDiagonal.{u, u, u + 1} B S hS (polarizedAlgebraicStackOf B hS hT h).val
        (Stack.schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h)).hom) ∧
      Stack.AlgebraicStacks.IsRelativelyFinitePresentation B S hS
        (Stack.AlgebraicStacks.relativeDiagonal B S hS
          (Stack.structureMorphism B S hS (polarizedAlgebraicStackOf B hS hT h))) :=
  isSeparated_and_isRelativelyFinitePresentation_relativeDiagonal_polarizedAlgebraicStack_of_isomSpace
    B hS hT h (isSeparated_relocalizeToYoneda_polarizedIsomSpace B hS hT)
    (isQuasiCompact_relocalizeToYoneda_polarizedIsomSpace B hS hT)

end AlgebraicGeometry

end
