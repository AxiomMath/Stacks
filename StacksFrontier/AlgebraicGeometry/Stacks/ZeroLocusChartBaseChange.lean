module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingSubspaceGeneralPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionOpenSourceRestriction

/-!
# The base change of a zero locus along a chart is the zero locus of the pulled-back functions

Let `f : U ⟶ 𝒳` be a 1-morphism from the algebraic stack of an algebraic space `U` to an
algebraic stack over `S`, let `c : 𝒲 ⟶ 𝒳` be another 1-morphism — in the application a smooth
surjective chart of `𝒳` — and let `P` be an algebraic space representing the 2-fibre product
`U ×_𝒳 𝒲`, with `g : P ⟶ U` the projection of **Stacks 04SW**. For a closed subspace `Z ⊆ U`
the 2-fibre product `Z ×_𝒳 𝒲` is represented by the inverse image `g⁻¹ Z ⊆ P`, and when `Z` is
the zero locus `V(f₁, …, f_r)` of finitely many global functions on `U` that inverse image is
the zero locus `V(g^*f₁, …, g^*f_r)` of the pulled-back functions, by
`AlgebraicGeometry.Space.vanishingSubfunctor_globalFunctionsMap_eq_preimage`.

This is the identification that **Stacks 06MD** needs in order to apply the flatness half of
**Stacks 06LW** on a chart: the closed-subspace equality is proved, and what is added here is the
match against the representing algebraic space of the 2-fibre product of the *zero-locus* stack.

## Main results

* `AlgebraicGeometry.Stack.isPullback_representingMap_restrictionInnerSquare`: the square of
  representing algebraic spaces of the inner square of
  `AlgebraicGeometry.Stack.restrictionInnerSquare` is cartesian.
* `AlgebraicGeometry.Stack.exists_iso_representingMap_restrictionInnerSquare_fst`: the
  representing algebraic space of `Z ×_𝒳 𝒲` is isomorphic to the inverse image `g⁻¹ Z`,
  compatibly with the inclusion into `P`.
* `AlgebraicGeometry.Stack.exists_iso_vanishingSubfunctor_chartBaseChange`: the same, for
  `Z = V(f₁, …, f_r)`, with the inverse image named as the zero locus of the pulled-back
  functions.

## How it is proved

`AlgebraicGeometry.Stack.restrictionInnerSquare` is the canonical 2-fibre product of the cospan
`(U ×_𝒳 𝒲 ⟶ U, Z ⟶ U)`, so the square of representing presheaves it induces through
**Stacks 04SW** is cartesian, by
`AlgebraicGeometry.Stack.isPullback_representingMap_of_isTwoFibreProduct`; the 1-morphism of
algebraic stacks a morphism of algebraic spaces induces reads back as that morphism, by
`AlgebraicGeometry.Stack.representingMap_associatedMap`. The inverse image of a subfunctor is
itself a fibre product of the same cospan, **Stacks 083Q**
(`CategoryTheory.Subfunctor.isPullback_preimage`), and two cartesian squares over one cospan are
uniquely isomorphic.

## Implementation notes

The isomorphism is stated for an arbitrary subfunctor `Z'` of `P` *equal* to the inverse image,
rather than for the inverse image itself, so that a consumer which knows the inverse image under
another name — here the zero locus of the pulled-back functions — gets the isomorphism onto that
name with no transport of a dependent type.

No `@[stacks]` attribute is attached: **Stacks 083Q** is the inverse-image construction and its
fibre-product characterisation, both tagged in
`StacksFrontier/AlgebraicGeometry/Spaces/SubspacePreimage.lean`, and the chapter carries no separate
assertion about the base change of a zero locus along a chart of a stack.

## References

* [Stacks Project, Tag 02XD](https://stacks.math.columbia.edu/tag/02XD)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 06LW](https://stacks.math.columbia.edu/tag/06LW)
* [Stacks Project, Tag 06MD](https://stacks.math.columbia.edu/tag/06MD)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Closed

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  (Z : Subfunctor U) (hZ : IsAlgebraicSpace B S hS Z.toFunctor)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (𝒲 : AlgebraicStacks.{u, w} B S hS) (c : 𝒲 ⟶ 𝒳)
  (P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (eP : StacksRepresentableCFG.EquivalenceOver
    (twoFibreProductSquareAlgebraicStacks B S hS c f).pt.val.val.p
    (presheafOfCategories (P ⋙ typeToCat)).p)
  (eQ : StacksRepresentableCFG.EquivalenceOver
    (restrictionSquare.{u, w} B S hS 𝒳 U Z.toFunctor hU hZ Z.ι f 𝒲 c).pt.val.val.p
    (presheafOfCategories (Q ⋙ typeToCat)).p)

/-- **The square of representing algebraic spaces of the inner square is cartesian.** The inner
square of `AlgebraicGeometry.Stack.restrictionInnerSquare` is the canonical 2-fibre product of
the cospan `(U ×_𝒳 𝒲 ⟶ U, Z ⟶ U)`, so the square of representing presheaves it induces through
**Stacks 04SW** is cartesian; the bottom edge is the inclusion `Z ⟶ U` itself, the 1-morphism of
algebraic stacks attached to a morphism of algebraic spaces reading back as that morphism. -/
theorem isPullback_representingMap_restrictionInnerSquare :
    IsPullback
      (representingMap B S hS
        (restrictionSquare.{u, w} B S hS 𝒳 U Z.toFunctor hU hZ Z.ι f 𝒲 c).pt.val
        (twoFibreProductSquareAlgebraicStacks B S hS c f).pt.val Q P eQ eP
        (restrictionInnerSquare.{u, w} B S hS 𝒳 U Z.toFunctor hU hZ Z.ι f 𝒲 c).fst.hom)
      (representingMap B S hS
        (restrictionSquare.{u, w} B S hS 𝒳 U Z.toFunctor hU hZ Z.ι f 𝒲 c).pt.val
        (algebraicSpaceStack.{u, w} B S hS Z.toFunctor hZ).val Q Z.toFunctor eQ
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (restrictionInnerSquare.{u, w} B S hS 𝒳 U Z.toFunctor hU hZ Z.ι f 𝒲 c).snd.hom)
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS c f).pt.val
        (algebraicSpaceStack.{u, w} B S hS U hU).val P U eP
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (twoFibreProductSquareAlgebraicStacks B S hS c f).snd.hom)
      Z.ι := by
  have := isPullback_representingMap_of_isTwoFibreProduct B S hS
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (twoFibreProductSquareAlgebraicStacks B S hS c f).snd.hom
      (algebraicSpaceStackMap.{u, w} B S hS hZ hU Z.ι).hom)
    P Z.toFunctor U Q Q eP (StacksRepresentableCFG.EquivalenceOver.refl _)
    (StacksRepresentableCFG.EquivalenceOver.refl _) eQ eQ
  rwa [representingMap_associatedMap B S hS Z.toFunctor U Z.ι] at this

/-- **The representing algebraic space of `Z ×_𝒳 𝒲` is the inverse image of `Z`.** The square of
representing algebraic spaces is cartesian and the inverse image of a subfunctor is a fibre
product of the same cospan (**Stacks 083Q**), so the two apexes are isomorphic over `P`.

The subfunctor is taken as an arbitrary one equal to the inverse image, so that a consumer which
has another name for it gets the isomorphism onto that name. -/
theorem exists_iso_representingMap_restrictionInnerSquare_fst (Z' : Subfunctor P)
    (hZ' : Z' = Z.preimage
      (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS c f).pt.val
        (algebraicSpaceStack.{u, w} B S hS U hU).val P U eP
        (StacksRepresentableCFG.EquivalenceOver.refl _)
        (twoFibreProductSquareAlgebraicStacks B S hS c f).snd.hom)) :
    ∃ e : Q ≅ Z'.toFunctor,
      e.hom ≫ Z'.ι =
        representingMap B S hS
          (restrictionSquare.{u, w} B S hS 𝒳 U Z.toFunctor hU hZ Z.ι f 𝒲 c).pt.val
          (twoFibreProductSquareAlgebraicStacks B S hS c f).pt.val Q P eQ eP
          (restrictionInnerSquare.{u, w} B S hS 𝒳 U Z.toFunctor hU hZ Z.ι f 𝒲 c).fst.hom := by
  subst hZ'
  have h := isPullback_representingMap_restrictionInnerSquare B S hS 𝒳 U hU Z hZ f 𝒲 c P Q eP eQ
  have h' := (Subfunctor.isPullback_preimage (representingMap B S hS
    (twoFibreProductSquareAlgebraicStacks B S hS c f).pt.val
    (algebraicSpaceStack.{u, w} B S hS U hU).val P U eP
    (StacksRepresentableCFG.EquivalenceOver.refl _)
    (twoFibreProductSquareAlgebraicStacks B S hS c f).snd.hom) Z).flip
  exact ⟨h.isoIsPullback _ _ h', IsPullback.isoIsPullback_hom_fst _ _ h h'⟩

end Closed

/-! ### The zero locus of a family of global functions -/

section ZeroLocus

variable (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (U : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hU : IsAlgebraicSpace B S hS U)
  {r : ℕ}
  (b : Fin r → (SheafOfModules.unit (Space.structureRingSheaf B S hS ⟨U, hU⟩)).sections)
  (f : algebraicSpaceStack.{u, w} B S hS U hU ⟶ 𝒳)
  (𝒲 : AlgebraicStacks.{u, w} B S hS) (c : 𝒲 ⟶ 𝒳)
  (P Q : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hP : IsAlgebraicSpace B S hS P)
  (eP : StacksRepresentableCFG.EquivalenceOver
    (twoFibreProductSquareAlgebraicStacks B S hS c f).pt.val.val.p
    (presheafOfCategories (P ⋙ typeToCat)).p)
  (eQ : StacksRepresentableCFG.EquivalenceOver
    (restrictionSquare.{u, w} B S hS 𝒳 U
      (Space.vanishingSubfunctor B S hS ⟨U, hU⟩ b).toFunctor hU
      (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ b).1
      (Space.vanishingSubfunctor B S hS ⟨U, hU⟩ b).ι f 𝒲 c).pt.val.val.p
    (presheafOfCategories (Q ⋙ typeToCat)).p)

/-- The projection `U ×_𝒳 𝒲 ⟶ U` of **Stacks 04SW**, read as a morphism of algebraic spaces. -/
abbrev chartBaseChangeSpaceProjection :
    (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨U, hU⟩ :=
  ObjectProperty.homMk
    (representingMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS c f).pt.val
      (algebraicSpaceStack.{u, w} B S hS U hU).val P U eP
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (twoFibreProductSquareAlgebraicStacks B S hS c f).snd.hom)

/-- The restrictions `g^*f₁, …, g^*f_r` to `U ×_𝒳 𝒲` of the global functions on `U`. -/
abbrev chartBaseChangeGlobalFunctions :
    Fin r → (SheafOfModules.unit (Space.structureRingSheaf B S hS ⟨P, hP⟩)).sections :=
  fun i => Space.globalFunctionsMap B S hS
    (chartBaseChangeSpaceProjection B S hS 𝒳 U hU f 𝒲 c P hP eP) (b i)

/-- **The base change of `V(f₁, …, f_r)` along a chart is the zero locus of the pulled-back
functions, on the representing algebraic space.** Let `f : U ⟶ 𝒳` be a 1-morphism from an
algebraic space to an algebraic stack over `S`, let `f₁, …, f_r` be global regular functions on
`U`, let `c : 𝒲 ⟶ 𝒳` be a 1-morphism and let `P` and `Q` be algebraic spaces representing
`U ×_𝒳 𝒲` and `V(f₁, …, f_r) ×_𝒳 𝒲`. Then `Q` is isomorphic to the zero locus
`V(g^*f₁, …, g^*f_r)` inside `P`, where `g : P ⟶ U` is the projection of **Stacks 04SW**,
compatibly with the two inclusions into `P`.

This is `AlgebraicGeometry.Stack.exists_iso_representingMap_restrictionInnerSquare_fst` fed with
`AlgebraicGeometry.Space.vanishingSubfunctor_globalFunctionsMap_eq_preimage`, the equality of
closed subspaces `V(g^*f₁, …, g^*f_r) = g⁻¹ V(f₁, …, f_r)`, which holds with no hypothesis on
`g`. -/
theorem exists_iso_vanishingSubfunctor_chartBaseChange :
    ∃ e : Q ≅ (Space.vanishingSubfunctor B S hS ⟨P, hP⟩
        (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU b f 𝒲 c P hP eP)).toFunctor,
      e.hom ≫ (Space.vanishingSubfunctor B S hS ⟨P, hP⟩
          (chartBaseChangeGlobalFunctions B S hS 𝒳 U hU b f 𝒲 c P hP eP)).ι =
        representingMap B S hS
          (restrictionSquare.{u, w} B S hS 𝒳 U
            (Space.vanishingSubfunctor B S hS ⟨U, hU⟩ b).toFunctor hU
            (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ b).1
            (Space.vanishingSubfunctor B S hS ⟨U, hU⟩ b).ι f 𝒲 c).pt.val
          (twoFibreProductSquareAlgebraicStacks B S hS c f).pt.val Q P eQ eP
          (restrictionInnerSquare.{u, w} B S hS 𝒳 U
            (Space.vanishingSubfunctor B S hS ⟨U, hU⟩ b).toFunctor hU
            (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ b).1
            (Space.vanishingSubfunctor B S hS ⟨U, hU⟩ b).ι f 𝒲 c).fst.hom :=
  exists_iso_representingMap_restrictionInnerSquare_fst B S hS 𝒳 U hU
    (Space.vanishingSubfunctor B S hS ⟨U, hU⟩ b)
    (Space.vanishingSubfunctor_isClosedSubspace B S hS ⟨U, hU⟩ b).1 f 𝒲 c P Q eP eQ _
    (Space.vanishingSubfunctor_globalFunctionsMap_eq_preimage B S hS
      (chartBaseChangeSpaceProjection B S hS 𝒳 U hU f 𝒲 c P hP eP) b)

end ZeroLocus

end AlgebraicGeometry.Stack

end
