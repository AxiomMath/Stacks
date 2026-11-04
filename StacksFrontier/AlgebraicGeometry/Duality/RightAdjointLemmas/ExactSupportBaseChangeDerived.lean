module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportBaseChange
import all StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportBaseChange
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedInternalHom
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedPushforwardConservative

/-!
# Base change for the right adjoint of pushforward along a closed immersion

Let

```
Z' --i'--> X'
|g          |f
Z --i-----> X
```

be a square of ringed spaces with `i` and `i'` closed quotient morphisms, and let
`Lf^* : D(𝒪_X) ⥤ D(𝒪_{X'})` and `Lg^* : D(𝒪_Z) ⥤ D(𝒪_{Z'})` be derived pullback functors.
Tor independence of `Z` and `X'` over `X` gives an identification
`Ri'_* ∘ Lg^* ≅ Lf^* ∘ Ri_*` ([Stacks, Tag 0E23]); granted it, the map

`Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)`

of [Stacks, Tag 0E2K] is the transpose, under the derived adjunction `Ri'_* ⊣ R ℰom(𝒪_{Z'}, -)`
of [Stacks, Tag 0A76], of that identification followed by `Lf^*` of the counit
`Ri_* R ℰom(𝒪_Z, K) ⟶ K`.

[Stacks, Tag 0E2L] says that this map is an isomorphism if and only if the base change map

`Lf^* R SheafHom_{𝒪_X}(𝒪_Z, K) ⟶ R SheafHom_{𝒪_{X'}}(𝒪_{Z'}, Lf^*K)`

is one. Pushforward along a closed quotient morphism is exact and fully faithful, so `Ri'_*`
reflects isomorphisms, and the two sides of the map of [Stacks, Tag 0E2K] become, after `Ri'_*`,
the two sides of the base change map, by [Stacks, Tag 0E23] and [Stacks, Tag 0A77].

All names below live in the namespace `RingedSpaceModuleAdjunction.ClosedQuotientBaseChange`.

## Main definitions

* `rightAdjointBaseChangeMap` is the map `Lg^* R ℰom(𝒪_Z, K) ⟶ R ℰom(𝒪_{Z'}, Lf^*K)` of
  [Stacks, Tag 0E2K], built from an arbitrary identification `e`; `rightAdjointBaseChange`
  collects these maps into a morphism of functors. The tag itself, for a cartesian square of
  schemes with `e` supplied by [Stacks, Tag 0E23], is
  `Stacks.Duality.ExactSupportBaseChange.baseChangeSheafHomExactSupportMap`.
* `pushforwardSourceIso` and `pushforwardTargetIso` identify the pushforwards along `i'` of its
  source and target with `Lf^* R SheafHom_{𝒪_X}(𝒪_Z, K)` and
  `R SheafHom_{𝒪_{X'}}(𝒪_{Z'}, Lf^*K)`.
* `derivedSheafHomBaseChangeMap` is the resulting map
  `Lf^* R SheafHom_{𝒪_X}(𝒪_Z, K) ⟶ R SheafHom_{𝒪_{X'}}(𝒪_{Z'}, Lf^*K)`.

## Main results

* `map_rightAdjointBaseChangeMap`: the pushforward along `i'` of the map of [Stacks, Tag 0E2K]
  is `derivedSheafHomBaseChangeMap` read through those two identifications.
* `isIso_rightAdjointBaseChangeMap_iff_of_eq`: the map of [Stacks, Tag 0E2K] is an
  isomorphism if and only if any map filling that square is, and
  `isIso_rightAdjointBaseChangeMap_iff` is the case of `derivedSheafHomBaseChangeMap` itself.
  This is the source's reduction of [Stacks, Tag 0E2L] to `Ri'_*`, for an arbitrary `e`; the
  instance at a cartesian square of schemes is
  `Stacks.Duality.ExactSupportBaseChange.isIso_baseChangeSheafHomExactSupportMap_app_iff`. The tag
  itself, with the map of [Stacks, Tag 08I3], is, in the namespace
  `Stacks.Duality.ExactSupportBaseChange`,
  `isIso_baseChangeSheafHomExactSupportMap_app_iff_isIso_derivedPullbackSheafHomMap`.
* `isIso_rightAdjointBaseChangeMap_iff_isIso_map`: the map of [Stacks, Tag 0E2K] is an
  isomorphism exactly when its pushforward along `i'` is.

## Implementation notes

`R SheafHom_{𝒪_X}(𝒪_Z, K)` is read as the right derived functor of the internal Hom from the
ring sheaf `i_* 𝒪_Z`, which is the model [Stacks, Tag 0A77] is stated at in
`derivedModulePushforwardDerivedSheafHomExactSupportIso`; `𝒪_Z` in the displayed formulas always
means `i_* 𝒪_Z`, as in the source.

The commutativity and cartesianness of the square, and the Tor independence of `Z` and `X'` over
`X`, enter only through the isomorphism `Ri'_* ∘ Lg^* ≅ Lf^* ∘ Ri_*` of [Stacks, Tag 0E23],
which is a parameter `e` here, so that the construction and the comparison below are stated for
a square of ringed spaces with arbitrary functors `Lf^*` and `Lg^*`: nothing below uses any
property of them. For a cartesian square of schemes, `e` is supplied unconditionally by
[Stacks, Tag 0E23] in `Stacks.Duality.ExactSupportBaseChange.pushforwardBaseChangeIso`.

The source identifies the base change map above with the one of Cohomology,
Remark [Stacks, Tag 08I3], and omits the verification; here that identification is the hypothesis
`hψ` of `isIso_rightAdjointBaseChangeMap_iff_of_eq`. [Stacks, Tag 0E2L] with the map of
[Stacks, Tag 08I3] itself is proved in
`StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportBaseChangeInternalHom`,
by a different route (the projection formula, not [Stacks, Tag 0A77]).

## References

* [Stacks Project, Tag 0E2L](https://stacks.math.columbia.edu/tag/0E2L)
* [Stacks Project, Tag 0E2K](https://stacks.math.columbia.edu/tag/0E2K)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientBaseChange

variable (S S' : ClosedQuotientMorphismOfRingedSpaces.{u})
  (Lf : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S'.X)))
  (Lg : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.Z)) ⥤
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S'.Z)))
  (e : Lg ⋙ (modulePushforward S'.i).mapDerivedCategory ≅
    (modulePushforward S.i).mapDerivedCategory ⋙ Lf)

/-! ### The map of Stacks 0E2K -/

/-- The base change map is natural in `K`. -/
theorem rightAdjointBaseChangeMap_naturality
    {K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))} (a : K ⟶ L) :
    Lg.map (S.derivedSheafHomExactSupport.map a) ≫ rightAdjointBaseChangeMap S S' Lf Lg e L =
      rightAdjointBaseChangeMap S S' Lf Lg e K ≫
        S'.derivedSheafHomExactSupport.map (Lf.map a) := by
  simp only [rightAdjointBaseChangeMap]
  rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_right]
  congr 1
  have h := e.hom.naturality (S.derivedSheafHomExactSupport.map a)
  dsimp at h
  rw [reassoc_of% h, Category.assoc, ← Lf.map_comp, ← Lf.map_comp]
  simp

/-- The base change maps `rightAdjointBaseChangeMap`, as a morphism of functors
`R ℰom(𝒪_Z, -) ⋙ Lg^* ⟶ Lf^* ⋙ R ℰom(𝒪_{Z'}, -)` from `D(𝒪_X)` to `D(𝒪_{Z'})`. -/
def rightAdjointBaseChange :
    S.derivedSheafHomExactSupport ⋙ Lg ⟶ Lf ⋙ S'.derivedSheafHomExactSupport where
  app K := rightAdjointBaseChangeMap S S' Lf Lg e K
  naturality _ _ a := rightAdjointBaseChangeMap_naturality S S' Lf Lg e a

/-- The component of `rightAdjointBaseChange` at `K` is `rightAdjointBaseChangeMap` at `K`. -/
@[simp]
theorem rightAdjointBaseChange_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    (rightAdjointBaseChange S S' Lf Lg e).app K = rightAdjointBaseChangeMap S S' Lf Lg e K :=
  rfl

end RingedSpaceModuleAdjunction.ClosedQuotientBaseChange

end
