module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.GenericFlatness

/-!
# Generic flatness and finite presentation over a reduced algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site and let
`F` be an `𝒪_X`-module which is quasi-coherent of finite type on charts. If `Y` is reduced, `f`
is quasi-separated and `f` is of finite type, then there is a dense open subspace `W` of `Y`
over which the base change of `f` becomes flat and *of finite presentation*, and over which `F`
becomes flat and of finite presentation. This is Stacks 06QT.

It is the quasi-separated refinement of Stacks 06QS: that proposition already produces a dense
open over which the base change is flat, locally of finite presentation and quasi-compact, and
being of finite presentation is exactly being locally of finite presentation, quasi-compact and
quasi-separated (Stacks 03XP, part (3)). The only new input is that quasi-separatedness is
stable under base change, which is Stacks 03KL.

## Main results

* `AlgebraicGeometry.Space.exists_dense_open_genericFlatness_isFinitePresentation`:
  **Stacks 06QT**, for a general reduced algebraic space base.
* `AlgebraicGeometry.Space.exists_dense_open_genericFlatness_isFinitePresentation_of_isScheme`:
  the same statement for a base represented by an object of the site.

## Implementation notes

All four hypotheses of the source are imposed: reducedness of `Y` is
`AlgebraicGeometry.Space.HasEtaleLocalProperty` at reducedness of schemes (Stacks 03E6),
quasi-separatedness of `f` is `AlgebraicGeometry.Space.IsQuasiSeparated` (Stacks 03HL,
part (3)), finite type is `AlgebraicGeometry.Space.IsFiniteType` (Stacks 03XF), and the module
hypotheses are the chartwise `AlgebraicGeometry.Space.IsQuasicoherentOnCharts` and
`AlgebraicGeometry.Space.IsFiniteTypeOnCharts`.

Nothing is assumed beyond those: the proof is Stacks 06QS as formalized in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/GenericFlatness.lean` together with
`AlgebraicGeometry.Space.isQuasiSeparated_pullback`, which is Stacks 03KL. No statement is
carried as a hypothesis and no result is assumed, so there is no tag to declare absent.

What is proved is both conclusions about the morphism in full — flatness and finite
presentation of the base change `pullback.snd f W.ι` of `f` over `W` — and both conclusions
about the module in the pointwise form inherited from Stacks 06QS: for every point of `X` lying
over `W`, that point lies in `AlgebraicGeometry.Space.flatLocus` (Stacks 0DLR) and in
`AlgebraicGeometry.Space.finitePresentationLocus`. What is *not* proved is those two module
conclusions restated as properties of the pullback `F|_{X_W}` as a module on the algebraic space
`X_W`. That restatement needs a comparison of the chart restriction of a pullback module with
the pullback of a chart restriction, in a generality this development does not have: it is
recorded as missing under Tag 05VP in
`StacksFrontier/AlgebraicGeometry/Spaces/GeometricStalkBaseChange.lean`; what is available is the
comparison across a commuting square of charts,
`AlgebraicGeometry.Space.restrictToChartBaseChangeIso`, which is not that statement. The
pointwise form loses
nothing for a quasi-coherent module, membership of the flat locus being flatness of the
geometric stalk, and it is the rendering Stacks 0DLR and Stacks 06QS already use here.

Density of `W` is `AlgebraicGeometry.Space.IsDenseOpenSubspace`: an open subspace whose set of
points is dense in the point topology of Stacks 03BX, for which the topology instance is made
local to this file.

## References

* [Stacks Project, Tag 06QT](https://stacks.math.columbia.edu/tag/06QT)
* [Stacks Project, Tag 06QS](https://stacks.math.columbia.edu/tag/06QS)
* [Stacks Project, Tag 03XP](https://stacks.math.columbia.edu/tag/03XP)
* [Stacks Project, Tag 03KL](https://stacks.math.columbia.edu/tag/03KL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_genericFlatnessFP
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_genericFlatnessFP
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_genericFlatnessFP B S hS).has_limit _

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 06QT.** Let `f : X ⟶ Y` be a quasi-separated morphism of algebraic spaces over `S`
of finite type with `Y` reduced, and let `F` be an `𝒪_X`-module which is quasi-coherent of
finite type on charts. Then there is a dense open subspace `W` of `Y` such that the base change
of `f` over `W` is flat and of finite presentation, and such that `F` is flat over `Y` and of
finite presentation at every point of `X` lying over `W`.

This is Stacks 06QS refined by the quasi-separatedness hypothesis: that proposition gives
flatness, local finite presentation and quasi-compactness of the base change, and a base change
of a quasi-separated morphism is quasi-separated. -/
@[stacks 06QT]
theorem exists_dense_open_genericFlatness_isFinitePresentation
    (hX : IsAlgebraicSpace B S hS X) {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y)
    (hYred : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsReduced T))
    (f : X ⟶ Y) (hqs : IsQuasiSeparated B S hS f) (hf : IsFiniteType B S hS f)
    (F : Modules.{u, u} B S hS X hX)
    (hqc : IsQuasicoherentOnCharts B S hS hX F)
    (hft : IsFiniteTypeOnCharts B S hS hX F) :
    ∃ W : Subfunctor Y, IsDenseOpenSubspace B S hS hY W ∧
      IsFlat B S hS (pullback.snd f W.ι) ∧
      IsFinitePresentation B S hS (pullback.snd f W.ι) ∧
      ∀ x : points B S hS X,
        pointsMap B S hS X f x ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) →
          x ∈ flatLocus B S hS hX f F ∧
            x ∈ finitePresentationLocus B S hS hX F := by
  obtain ⟨W, hWdense, hWflat, hWlfp, hWqc, hWpt⟩ :=
    exists_dense_open_genericFlatness B S hS hX hY hYred f hf F hqc hft
  exact ⟨W, hWdense, hWflat,
    ⟨hWlfp, hWqc, isQuasiSeparated_pullback B S hS f W.ι hqs⟩, hWpt⟩

/-- **Stacks 06QT for a base represented by an object of the site.** This is the statement of
the tag for a reduced scheme base, where the identity may be taken as the surjective étale
chart witnessing reducedness. -/
@[stacks 06QT "the case of a base represented by an object of the site"]
theorem exists_dense_open_genericFlatness_isFinitePresentation_of_isScheme
    (hX : IsAlgebraicSpace B S hS X) (Z : BigFppfOver B S hS)
    [IsReduced ((BigFppfOver.toScheme B S hS).obj Z)]
    (f : X ⟶ yoneda.obj Z) (hqs : IsQuasiSeparated B S hS f) (hf : IsFiniteType B S hS f)
    (F : Modules.{u, u} B S hS X hX)
    (hqc : IsQuasicoherentOnCharts B S hS hX F)
    (hft : IsFiniteTypeOnCharts B S hS hX F) :
    ∃ W : Subfunctor (yoneda.obj Z),
      IsDenseOpenSubspace B S hS (isAlgebraicSpace_yoneda B S hS Z) W ∧
      IsFlat B S hS (pullback.snd f W.ι) ∧
      IsFinitePresentation B S hS (pullback.snd f W.ι) ∧
      ∀ x : points B S hS X,
        pointsMap B S hS X f x ∈ Set.range (pointsMap B S hS W.toFunctor W.ι) →
          x ∈ flatLocus B S hS hX f F ∧
            x ∈ finitePresentationLocus B S hS hX F :=
  exists_dense_open_genericFlatness_isFinitePresentation B S hS hX
    (isAlgebraicSpace_yoneda B S hS Z)
    (hasEtaleLocalProperty_of_representable B S hS (yoneda.obj Z)
      (fun T : Scheme.{u} => IsReduced T) Z (Iso.refl _) inferInstance) f hqs hf F hqc hft

end AlgebraicGeometry.Space

end
