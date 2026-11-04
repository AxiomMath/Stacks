module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStack
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentReindex
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativeDescentSchemeLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RelativelyPerfectHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfect

/-!
# Relatively perfect objects over a limit of algebraic spaces

In Situation 0DKU — a directed inverse system `Y = lim Yᵢ` of quasi-compact quasi-separated
algebraic spaces with affine transitions, a flat finitely presented `X₀ ⟶ Y₀`, and its base
changes `Xᵢ ⟶ Yᵢ` and `X ⟶ Y` — Stacks 0DKW asserts that the category of `Y`-perfect objects of
`D(𝒪_X)` is the colimit of the categories of `Yᵢ`-perfect objects of `D(𝒪_{Xᵢ})`, along the
derived pullbacks `Lf_{ji}^*` and `Lfᵢ^*`.  This file states that assertion.

## Main definitions

* `AlgebraicGeometry.Space.RelativeDescentSituation.isFlat_stageStructure`, ...: the base changes
  `Xᵢ ⟶ Yᵢ` and `X ⟶ Y` of `X₀ ⟶ Y₀` (`stageStructure` and `limitStructure`, in
  `RelativeDescentReindex.lean`) are flat and locally of finite presentation.
* `AlgebraicGeometry.Space.RelativeDescentSituation.IsStagePerfect` and `IsLimitPerfect`:
  `Yᵢ`-perfectness on `Xᵢ` and `Y`-perfectness on `X`, in the sense of Stacks 0DKN.
* `AlgebraicGeometry.Space.RelativeDescentSituation.RelativelyPerfectColimit`: **the assertion of
  Stacks 0DKW** for the situation, whose limit is a limit of schemes.

## Implementation notes

The colimit of the categories `D_{Yᵢ-perf}(𝒪_{Xᵢ})` along the functors `Lf_{ji}^*` has as objects
the pairs `(i, Eᵢ)`, and as morphisms from `(i, E)` to `(i, E')` the colimit over `j ≥ i` of
`Hom_{D(𝒪_{Xⱼ})}(Lf_{ji}^*E, Lf_{ji}^*E')`; two objects at different stages are compared at a
common later stage.  The assertion that `D_{Y-perf}(𝒪_X)` is that colimit is therefore the
conjunction of five clauses, as for the scheme case Stacks 0DI8
(`AlgebraicGeometry.RelativeDescentSituation.isPerfectRelativeTo_colimit`): the transition
functors and the comparison functors preserve relative perfectness, so that the colimit and the
comparison functor are defined; the comparison is full and faithful on morphisms; and it is
essentially surjective.

The derived pullback is the canonical pseudofunctor
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` (Stacks 0D6D), and a morphism at a stage
`j ≥ i` is carried to the limit through its comparison
`L(fᵢ)^* ≅ L(f_{ji})^* ⋙ L(fⱼ)^*` (`CategoryTheory.PullbackData.triangle`).

*The limit is a limit of schemes.*  In Stacks 0DKU, `Y = lim Yᵢ` and `X = lim Xᵢ` are actual
limits of algebraic spaces (Stacks 07SF).  `AlgebraicGeometry.Space.RelativeDescentSituation`
records the limit only as a limit of presheaves on the size-bounded site, which can be smaller:
for a system of spectra of fields too big for the site it is empty, and then the faithfulness
clause fails (see `AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimit`).  The
assertion is therefore stated under
`AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimit`, which restores the source's
setting.

The derived categories are the model `CategoryTheory.HasDerivedCategory.standard` at which
`AlgebraicGeometry.Space.derivedModules` and `smallEtaleDerivedPullbackData` are formed.

## References

* [Stacks Project, Tag 0DKW](https://stacks.math.columbia.edu/tag/0DKW)
* [Stacks Project, Tag 0DKU](https://stacks.math.columbia.edu/tag/0DKU)
* [Stacks Project, Tag 0DKN](https://stacks.math.columbia.edu/tag/0DKN)
* [Stacks Project, Tag 0DI8](https://stacks.math.columbia.edu/tag/0DI8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

namespace RelativeDescentSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)

/-! ### The structure morphisms of the base changes -/

/-- The transition `Yᵢ ⟶ Y₀` of the inverse system, as a morphism of algebraic spaces. -/
abbrev stageTargetToInitial (i : D.LaterIndex) : D.stageTarget i ⟶ D.initialTarget :=
  ObjectProperty.homMk (D.Y.map (homOfLE i.2).op)

/-- The projection `Y ⟶ Y₀` of the limit, as a morphism of algebraic spaces. -/
abbrev limitTargetToInitial : D.limitTarget ⟶ D.initialTarget :=
  ObjectProperty.homMk (D.limitCone.π.app (op D.i₀))

/-- The square `Xᵢ = Yᵢ ×_{Y₀} X₀`, in the category of algebraic spaces. -/
theorem isPullback_stageStructure (i : D.LaterIndex) :
    IsPullback (D.stageStructure i) (D.stageToInitial i) (D.stageTargetToInitial i)
      D.initialStructure :=
  IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) (D.stage_isPullback i.1 i.2)

/-- The square `X = Y ×_{Y₀} X₀`, in the category of algebraic spaces. -/
theorem isPullback_limitStructure :
    IsPullback D.limitStructure D.limitToInitial D.limitTargetToInitial D.initialStructure :=
  IsPullback.of_map_of_faithful (F := ObjectProperty.ι _) D.limit_isPullback

/-- A base change of `X₀ ⟶ Y₀` is flat. -/
private theorem isFlat_of_isPullback_initialStructure {X Y : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {g : X ⟶ D.initialSource} {h : Y ⟶ D.initialTarget}
    (hp : IsPullback f g h D.initialStructure) : IsFlat B S hS f.hom :=
  (isFlat_isStableUnderBaseChange B S hS).of_isPullback hp.flip
    (show IsFlat B S hS D.initialStructure.hom from D.initial_isFlat)

/-- A base change of `X₀ ⟶ Y₀` is locally of finite presentation. -/
private theorem isLocallyOfFinitePresentation_of_isPullback_initialStructure
    {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : X ⟶ D.initialSource}
    {h : Y ⟶ D.initialTarget} (hp : IsPullback f g h D.initialStructure) :
    IsLocallyOfFinitePresentation B S hS f.hom :=
  (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback hp.flip
    (show IsLocallyOfFinitePresentation B S hS D.initialStructure.hom from
      D.initial_isFinitePresentation.1)

/-- `Xᵢ ⟶ Yᵢ` is flat, as a base change of `X₀ ⟶ Y₀`. -/
theorem isFlat_stageStructure (i : D.LaterIndex) : IsFlat B S hS (D.stageStructure i).hom :=
  D.isFlat_of_isPullback_initialStructure (D.isPullback_stageStructure i)

/-- `Xᵢ ⟶ Yᵢ` is locally of finite presentation, as a base change of `X₀ ⟶ Y₀`. -/
theorem isLocallyOfFinitePresentation_stageStructure (i : D.LaterIndex) :
    IsLocallyOfFinitePresentation B S hS (D.stageStructure i).hom :=
  D.isLocallyOfFinitePresentation_of_isPullback_initialStructure (D.isPullback_stageStructure i)

/-- `X ⟶ Y` is flat, as a base change of `X₀ ⟶ Y₀`. -/
theorem isFlat_limitStructure : IsFlat B S hS D.limitStructure.hom :=
  D.isFlat_of_isPullback_initialStructure D.isPullback_limitStructure

/-- `X ⟶ Y` is locally of finite presentation, as a base change of `X₀ ⟶ Y₀`. -/
theorem isLocallyOfFinitePresentation_limitStructure :
    IsLocallyOfFinitePresentation B S hS D.limitStructure.hom :=
  D.isLocallyOfFinitePresentation_of_isPullback_initialStructure D.isPullback_limitStructure

/-! ### Relative perfectness at the stages and at the limit -/

/-- `Y`-perfectness (Stacks 0DKN) along a morphism of algebraic spaces, elaborated at a variable
morphism.  The instance arguments of `AlgebraicGeometry.Space.IsPerfectRelativeToCanonical` are
found for a variable `f`; at the structure morphisms of the situation, whose source and target
are anonymous constructors, instance search does not see through them. -/
abbrev IsPerfectAlong {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hfl : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) (E : derivedModules B S hS X) : Prop :=
  IsPerfectRelativeToCanonical.{u, u + 1, u + 1} B S hS f hfl hlfp E

/-- An object of `D(𝒪_{Xᵢ})` is `Yᵢ`-perfect (Stacks 0DKN). -/
abbrev IsStagePerfect (i : D.LaterIndex) (E : derivedModules B S hS (D.stageSource i)) : Prop :=
  IsPerfectAlong (D.stageStructure i) (D.isFlat_stageStructure i)
    (D.isLocallyOfFinitePresentation_stageStructure i) E

/-- An object of `D(𝒪_X)` is `Y`-perfect (Stacks 0DKN). -/
abbrev IsLimitPerfect (E : derivedModules B S hS D.limitSource) : Prop :=
  IsPerfectAlong D.limitStructure D.isFlat_limitStructure
    D.isLocallyOfFinitePresentation_limitStructure E

/-! ### Stacks 0DKW -/

/-- The comparison `L(fᵢ)^* ≅ L(f_{ji})^* ⋙ L(fⱼ)^*` of the derived pullbacks to the limit, for
`i ≤ j`. -/
abbrev projectionComparison {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    (smallEtaleDerivedPullbackData B S hS).pull (D.sourceProjection i) ≅
      (smallEtaleDerivedPullbackData B S hS).pull (D.sourceTransition h) ⋙
        (smallEtaleDerivedPullbackData B S hS).pull (D.sourceProjection j) :=
  (smallEtaleDerivedPullbackData B S hS).triangle (D.sourceProjection_comp_sourceTransition h)

/-- **Stacks 0DKW.** In Situation 0DKU, whose limit is a limit of schemes
(`AlgebraicGeometry.Space.RelativeDescentSituation.IsSchemeLimit`, the source's setting), the
category of `Y`-perfect objects of `D(𝒪_X)` is the colimit of the categories of `Yᵢ`-perfect
objects of `D(𝒪_{Xᵢ})`:
1. the transition functors `Lf_{ji}^*` carry `Yᵢ`-perfect objects to `Yⱼ`-perfect objects;
2. the comparison functors `Lfᵢ^*` carry `Yᵢ`-perfect objects to `Y`-perfect objects;
3. (essential surjectivity) every `Y`-perfect object of `D(𝒪_X)` is isomorphic to `Lfᵢ^*Eᵢ`
   for some stage `i` and some `Yᵢ`-perfect `Eᵢ`;
4. (fullness) for `Yᵢ`-perfect `E` and `E'`, every morphism `Lfᵢ^*E ⟶ Lfᵢ^*E'` is, through the
   comparison `L(fᵢ)^* ≅ L(f_{ji})^* ⋙ L(fⱼ)^*`, the image of a morphism
   `Lf_{ji}^*E ⟶ Lf_{ji}^*E'` at some stage `j ≥ i`;
5. (faithfulness) two morphisms `E ⟶ E'` of `Yᵢ`-perfect objects with the same image under
   `Lfᵢ^*` have the same image under `Lf_{ji}^*` for some `j ≥ i`. -/
def RelativelyPerfectColimit : Prop :=
  D.IsSchemeLimit →
  (∀ {i j : D.LaterIndex} (h : i.1 ≤ j.1) (E : derivedModules B S hS (D.stageSource i)),
      D.IsStagePerfect i E →
        D.IsStagePerfect j (((smallEtaleDerivedPullbackData B S hS).pull
          (D.sourceTransition h)).obj E)) ∧
    (∀ (i : D.LaterIndex) (E : derivedModules B S hS (D.stageSource i)),
      D.IsStagePerfect i E →
        D.IsLimitPerfect (((smallEtaleDerivedPullbackData B S hS).pull
          (D.sourceProjection i)).obj E)) ∧
    (∀ E : derivedModules B S hS D.limitSource, D.IsLimitPerfect E →
      ∃ (i : D.LaterIndex) (Eᵢ : derivedModules B S hS (D.stageSource i)),
        D.IsStagePerfect i Eᵢ ∧
          Nonempty (((smallEtaleDerivedPullbackData B S hS).pull
            (D.sourceProjection i)).obj Eᵢ ≅ E)) ∧
    (∀ (i : D.LaterIndex) (E E' : derivedModules B S hS (D.stageSource i)),
      D.IsStagePerfect i E → D.IsStagePerfect i E' →
      ∀ φ : ((smallEtaleDerivedPullbackData B S hS).pull (D.sourceProjection i)).obj E ⟶
          ((smallEtaleDerivedPullbackData B S hS).pull (D.sourceProjection i)).obj E',
        ∃ (j : D.LaterIndex) (h : i.1 ≤ j.1)
          (ψ : ((smallEtaleDerivedPullbackData B S hS).pull (D.sourceTransition h)).obj E ⟶
            ((smallEtaleDerivedPullbackData B S hS).pull (D.sourceTransition h)).obj E'),
          φ = Functor.conjHom (D.projectionComparison h) ψ) ∧
    (∀ (i : D.LaterIndex) (E E' : derivedModules B S hS (D.stageSource i)),
      D.IsStagePerfect i E → D.IsStagePerfect i E' →
      ∀ ψ ψ' : E ⟶ E',
        ((smallEtaleDerivedPullbackData B S hS).pull (D.sourceProjection i)).map ψ =
            ((smallEtaleDerivedPullbackData B S hS).pull (D.sourceProjection i)).map ψ' →
          ∃ (j : D.LaterIndex) (h : i.1 ≤ j.1),
            ((smallEtaleDerivedPullbackData B S hS).pull (D.sourceTransition h)).map ψ =
              ((smallEtaleDerivedPullbackData B S hS).pull (D.sourceTransition h)).map ψ')

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
