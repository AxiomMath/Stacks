module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalLocallyOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.FieldSpectrumCoverFlat
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitenessBaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.GerbeInertiaCharacterization
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaProjectionFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaProjectionRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.ReducedUniquePointStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasScheme

/-!
# The inertia over a field cover is flat and locally of finite presentation

Let `𝒵` be an algebraic stack over `S` which admits a 1-morphism `c : Spec k ⟶ 𝒵` from the
algebraic stack of the spectrum of a field which is surjective, flat and locally of finite
presentation — condition (2) of **Stacks 06MP**. This file proves that the base change of the
forgetful 1-morphism `I_𝒵 ⟶ 𝒵` of the inertia along `c` is flat and locally of finite
presentation, that is that `𝒵` has fppf-locally flat and locally finitely presented inertia in
the sense of `AlgebraicGeometry.Stack.AlgebraicStacks.HasFlatLfpLocalInertia`.

This is the second step of the proof of **Stacks 06QK**:

* `I_𝒵 ⟶ 𝒵` is representable by algebraic spaces and locally of finite type by **Stacks 050Q**
  (`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_inertiaProjection_of_isAlgebraicStack`
  and `AlgebraicGeometry.Stack.isLocallyOfFiniteType_inertiaProjection`), both in the relative
  sense of Properties of Stacks, Section 04XB; **Stacks 06FM** for a representable 1-morphism
  turns that into local finite type in the sense of **Stacks 06FS** part (1).
* Its base change along `c` is therefore locally of finite type, by **Stacks 06FU**.
* The target of that base change is the algebraic stack of the spectrum of a field, which is
  locally Noetherian (**Stacks 04YF** in the scheme case applied to
  `AlgebraicGeometry.Stack.isLocallyNoetherian_fieldSpectrum`), so the base change is locally of
  finite presentation by **Stacks 0DQJ** part (1), which is **Stacks 06G4** part (1) for
  1-morphisms of algebraic stacks.
* It is flat because every 1-morphism to the algebraic stack of the spectrum of a field is flat
  (`AlgebraicGeometry.Stack.AlgebraicStacks.isFlat_to_fieldSpectrumStack`), a field having only
  flat modules.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isLocallyOfFiniteType_inertiaProjection`: the inertia
  projection is locally of finite type in the sense of Stacks 06FS part (1).
* `AlgebraicGeometry.Stack.AlgebraicStacks.hasFlatLfpLocalInertia_of_fieldSpectrumCover`: an
  algebraic stack with a surjective, flat, locally finitely presented 1-morphism from the
  spectrum of a field has fppf-locally flat and locally finitely presented inertia.

## Implementation notes

The fppf-local condition is phrased at the canonical 2-fibre product square of **Stacks 04T2**
over the cospan `(I_𝒵 ⟶ 𝒵, c)`, whose second projection is the base change of the inertia
projection. Stacks 06FU reads its own square over the reversed cospan, so the square is passed
to it swapped (`CategoryTheory.Bicategory.TwoCommSq.swap`), which exchanges the two projections
on the nose.

## References

* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YF](https://stacks.math.columbia.edu/tag/04YF)
* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
* [Stacks Project, Tag 06FM](https://stacks.math.columbia.edu/tag/06FM)
* [Stacks Project, Tag 06FS](https://stacks.math.columbia.edu/tag/06FS)
* [Stacks Project, Tag 06FU](https://stacks.math.columbia.edu/tag/06FU)
* [Stacks Project, Tag 06G4](https://stacks.math.columbia.edu/tag/06G4)
* [Stacks Project, Tag 06MP](https://stacks.math.columbia.edu/tag/06MP)
* [Stacks Project, Tag 06QK](https://stacks.math.columbia.edu/tag/06QK)
* [Stacks Project, Tag 0DQJ](https://stacks.math.columbia.edu/tag/0DQJ)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 050Q, local finite type of the inertia projection, in the sense of Stacks 06FS
part (1).** The forgetful 1-morphism `I_𝒳 ⟶ 𝒳` of the inertia of an algebraic stack `𝒳` over `S`
is locally of finite type as a 1-morphism of algebraic stacks.

`AlgebraicGeometry.Stack.isLocallyOfFiniteType_inertiaProjection` is the same statement in the
relative sense of Properties of Stacks, Section 04XB; the inertia projection is representable by
algebraic spaces by Stacks 050Q, so **Stacks 06FM** for a representable 1-morphism converts the
relative property into the existential smooth-diagram test, and the universal one follows because
local finite type is smooth local on the source-and-target. -/
@[stacks 050Q "local finite type of the inertia projection in the sense of Stacks 06FS part (1)"]
theorem isLocallyOfFiniteType_inertiaProjection (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) :
    IsLocallyOfFiniteType B S hS (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳) :=
  (Stack.hasPropertyOnEverySmoothDiagram_iff_some.{u, w} B S hS
      (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k)
      (Space.isSmoothLocalOnSourceAndTarget_locallyOfFiniteType B S hS)
      (Stack.inertiaAlgebraicStack B S hS 𝒳).property 𝒳.property
      (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳).hom).2
    (Stack.hasPropertyOnSomeSmoothDiagram_of_hasRelativeProperty.{u, w, u + 1} B S hS
      (fun _ _ k => Space.IsLocallyOfFiniteType B S hS k) 𝒳.property
      (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒳).hom
      (Stack.isRepresentableByAlgebraicSpaces_inertiaProjection_of_isAlgebraicStack.{u, u, u + 1, w}
        B S hS 𝒳.val 𝒳.property)
      (Stack.isLocallyOfFiniteType_inertiaProjection.{u, w} B S hS 𝒳))

/-- **The algebraic stack of the spectrum of a field is locally Noetherian.** The spectrum of a
field is a Noetherian scheme, and the identity presentation is a smooth surjective scheme atlas,
so this is **Stacks 04YF** in the scheme case. -/
theorem isLocallyNoetherianStack_fieldSpectrumStack (F : Stack.FieldSpectrum B S hS) :
    Stack.HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} => IsLocallyNoetherian T) (Stack.schemeStack.{u, w} B S hS F.base) :=
  let : ObjectProperty.IsLocal (fun T : Scheme.{u} => IsLocallyNoetherian T)
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u})) :=
    ObjectProperty.IsLocal.of_le Scheme.smoothPrecoverage_le_fppfPrecoverage
  (Stack.exists_scheme_atlas_iff_scheme.{u, w} B S hS
    (fun T : Scheme.{u} => IsLocallyNoetherian T) F.base).2
    (Stack.isLocallyNoetherian_fieldSpectrum B S hS F)

/-- **An algebraic stack covered by the spectrum of a field has fppf-locally flat and locally
finitely presented inertia.** This is the second step of the proof of **Stacks 06QK**: given a
surjective, flat, locally finitely presented 1-morphism `c : Spec k ⟶ 𝒵`, the base change
`I_𝒵 ×_𝒵 Spec k ⟶ Spec k` of the inertia projection along `c` is flat and locally of finite
presentation.

Local finite type of the inertia projection is **Stacks 050Q**, and base changes by
**Stacks 06FU**; the spectrum of a field is locally Noetherian, so **Stacks 0DQJ** part (1)
upgrades local finite type to local finite presentation. Flatness holds because every 1-morphism
into the algebraic stack of the spectrum of a field is flat. -/
theorem hasFlatLfpLocalInertia_of_fieldSpectrumCover
    (𝒵 : Stack.AlgebraicStacks.{u, w} B S hS)
    (h : Stack.HasLocallyOfFinitePresentationFlatFieldSpectrumCover B S hS 𝒵) :
    HasFlatLfpLocalInertia B S hS 𝒵 := by
  obtain ⟨F, c, hclfp, hcsurj, hcflat⟩ := h
  have hlft : IsLocallyOfFiniteType B S hS
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS
        (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒵) c).snd :=
    isLocallyOfFiniteType_baseChange B S hS
      (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒵) c
      (Stack.twoFibreProductSquareAlgebraicStacks B S hS
        (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒵) c).swap
      (Bicategory.isTwoFibreProduct_swap
        (Stack.isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS
          (Stack.inertiaProjectionAlgebraicStacks B S hS 𝒵) c))
      (isLocallyOfFiniteType_inertiaProjection.{u, w} B S hS 𝒵)
  exact ⟨Stack.schemeStack.{u, w} B S hS F.base, c, hcsurj, hcflat, hclfp,
    isFlat_to_fieldSpectrumStack.{u, w} B S hS _ F _,
    isLocallyOfFinitePresentation_of_isLocallyOfFiniteType B S hS _
      (isLocallyNoetherianStack_fieldSpectrumStack.{u, w} B S hS F) hlft⟩

end AlgebraicGeometry.Stack.AlgebraicStacks

end
