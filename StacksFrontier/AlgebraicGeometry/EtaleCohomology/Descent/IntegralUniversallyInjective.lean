module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.FiniteCaseTrim
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyB
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyC
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyCAlmostCocontinuous
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Descent.PropertyCPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PropertyA
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PropertyAPushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleLocallyBijective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePointUniverse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.AlmostCocontinuousFunctors
public import StacksFrontier.CategoryTheory.Sites.Topos.ExactnessOfMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective

/-!
# Direct image along an integral universally injective morphism

Let `f : X ⟶ Y` be a morphism of schemes which is integral and universally injective — a closed
immersion, for instance. This file proves [Stacks, Tag 04DX]: direct image
`f_{small, *} : Sh(X_étale) ⥤ Sh(Y_étale)` is then about as well behaved as a functor between
topoi can be. It reflects injections and surjections, preserves surjections and finite connected
colimits, is faithful, has surjective adjunction counit, and is exact on abelian sheaves; and the
base-change functor `Y_étale ⥤ X_étale`, `V ↦ X ×_Y V`, that induces it is almost cocontinuous.

## The shape of the argument

Such an `f` has all three of the properties (A), (B) and (C) isolated earlier in the chapter, and
each of the seven conclusions is read off from one of them.

Properties (A) and (B) hold for every integral morphism. Property (C) needs universal injectivity
as well, and enters through [Stacks, Tag 04DW]: integrality makes `f` universally closed and
universal injectivity makes it injective on points, so `f` is a homeomorphism onto a closed subset
of `Y`, which is the hypothesis of that lemma. Both hypotheses are stable under base change, so the
same reasoning applies to every `X ×_Y V ⟶ V` with `V` étale over `Y`; combined with closedness of
those base changes this is exactly the input of [Stacks, Tag 04DV], giving almost cocontinuity.

From there the conclusions are formal. Property (C) gives reflection of injections and surjections
by [Stacks, Tag 04DT]; property (B) gives preservation of surjections by [Stacks, Tag 04DO]; almost
cocontinuity gives preservation of connected colimits by [Stacks, Tag 04BA]. Surjectivity of the
counit and faithfulness then follow from reflection of surjections by the purely categorical
[Stacks, Tag 04D6], and exactness on abelian sheaves from preservation of surjections: direct image
is a right adjoint, hence additive and left exact, and an additive left exact functor between
abelian categories which preserves epimorphisms is exact.

For abelian sheaves, reflection of injections and surjections, surjectivity of the counit and
faithfulness are available from property (A) alone, by [Stacks, Tag 04DK].

## Main results

All of the following live in the `Stacks.EtaleCohomology` namespace and concern a morphism of
schemes `f : X ⟶ Y` that is integral and universally injective.

* `smallEtalePushforward_reflectsMonomorphisms_of_isIntegralHom_of_universallyInjective` and
  `smallEtalePushforward_reflectsEpimorphisms_of_isIntegralHom_of_universallyInjective` —
  direct image reflects injections and surjections of sheaves of sets.
* `smallEtalePushforward_preservesConnectedColimits_of_isIntegralHom_of_universallyInjective` —
  direct image preserves colimits of every connected shape, in particular pushouts and
  coequalizers.
* `smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom_of_universallyInjective` and
  `smallEtalePushforwardAb_preservesEpimorphisms_of_isIntegralHom_of_universallyInjective` —
  direct image carries surjections to surjections, on sheaves of sets and on abelian sheaves.
* `smallEtaleAdjunction_counit_epi_of_isIntegralHom_of_universallyInjective` and
  `smallEtaleAdjunctionAb_counit_epi_of_isIntegralHom_of_universallyInjective` — the counit
  `f^{-1} f_* F ⟶ F` is surjective.
* `smallEtalePushforward_faithful_of_isIntegralHom_of_universallyInjective` and
  `smallEtalePushforwardAb_faithful_of_isIntegralHom_of_universallyInjective` — direct image is
  faithful.
* `smallEtalePushforwardAb_exact_of_isIntegralHom_of_universallyInjective` — direct image of
  abelian sheaves is exact.
* `smallEtaleBaseChange_isAlmostCocontinuous_of_isIntegralHom_of_universallyInjective` — base
  change between the small étale sites is almost cocontinuous.

## Implementation notes

The coefficient universe of the set-valued statements whose proofs need sheafification —
preservation of connected colimits, surjectivity of the counit, faithfulness — is
`Type (max (u + 1) v)` with `v` free. The small étale site of `X : Scheme.{u}` has objects in
`Type (u + 1)`, so this is the range of coefficient universes in which the site is essentially
small and sheaves of sets on it can be sheafified. Reflection and preservation of surjections need
no sheafification and are stated for an arbitrary `Type v`.

Universal injectivity of a base change is extracted from the `MorphismProperty.universally`
description of the class rather than from an instance, because it is the projection
`X ×_Y V ⟶ V`, and not the morphism `f`, whose injectivity on points is wanted.

Exactness on abelian sheaves is assembled from the additive and left exact structure of a right
adjoint together with preservation of epimorphisms, which in turn is transported from the
set-valued statement along the forgetful functor: a morphism of abelian sheaves is epimorphic
exactly when it is locally surjective, and local surjectivity is detected on underlying sheaves of
sets. The identification of the underlying sheaf of sets of a direct image with the direct image of
the underlying sheaf of sets holds by definition, both being restriction along the base-change
functor.

## References

* [Stacks Project, Tag 04DX](https://stacks.math.columbia.edu/tag/04DX)
* [Stacks Project, Tag 04DK](https://stacks.math.columbia.edu/tag/04DK)
* [Stacks Project, Tag 04DM](https://stacks.math.columbia.edu/tag/04DM)
* [Stacks Project, Tag 04DO](https://stacks.math.columbia.edu/tag/04DO)
* [Stacks Project, Tag 04DR](https://stacks.math.columbia.edu/tag/04DR)
* [Stacks Project, Tag 04DT](https://stacks.math.columbia.edu/tag/04DT)
* [Stacks Project, Tag 04DV](https://stacks.math.columbia.edu/tag/04DV)
* [Stacks Project, Tag 04DW](https://stacks.math.columbia.edu/tag/04DW)
* [Stacks Project, Tag 04BA](https://stacks.math.columbia.edu/tag/04BA)
* [Stacks Project, Tag 04D6](https://stacks.math.columbia.edu/tag/04D6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology

/-! ### Properties (A), (B) and (C) -/

/-- An integral universally injective morphism of schemes is a homeomorphism onto a closed subset
of its target: integrality makes it universally closed, hence a closed map, and universal
injectivity makes it injective on points. -/
private theorem isClosedEmbedding_of_isIntegralHom_of_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] :
    Topology.IsClosedEmbedding f.base :=
  Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap f.continuous f.injective
    (Scheme.Hom.isClosedMap f)

/-- An integral universally injective morphism of schemes has property (C): every scheme étale
over the source is dominated, by a surjection over the source, by the base change of a scheme
étale over the target. -/
private theorem hasPropertyC_of_isIntegralHom_of_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] :
    HasPropertyC f :=
  hasPropertyC_of_isIntegralHom_of_isClosedEmbedding f
    (isClosedEmbedding_of_isIntegralHom_of_universallyInjective f)

/-- Every base change of an integral universally injective morphism of schemes has property (C).

Integrality is stable under base change, so the projection `X ×_Y V ⟶ V` is again integral and in
particular a closed map; universal injectivity of `f` applied to the pullback square makes that
projection injective on points. Hence it too is a homeomorphism onto a closed subset, and property
(C) follows as for `f` itself. -/
private theorem hasPropertyC_pullback_snd_of_isIntegralHom_of_universallyInjective
    {X Y V : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] (v : V ⟶ Y) :
    HasPropertyC (pullback.snd f v) :=
  hasPropertyC_of_isIntegralHom_of_isClosedEmbedding (pullback.snd f v)
    (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap (pullback.snd f v).continuous
      (UniversallyInjective.universally_injective (f := f) (pullback.fst f v) v (pullback.snd f v)
        (IsPullback.of_hasPullback f v).flip)
      (Scheme.Hom.isClosedMap _))

/-! ### Almost cocontinuity -/

/-- **Stacks Project, Tag 04DX, part (7).** For an integral universally injective morphism of
schemes `f : X ⟶ Y`, base change `Y.Etale ⥤ X.Etale`, `V ↦ X ×_Y V`, is almost cocontinuous as a
functor of small étale sites.

Every étale base change of `f` has property (C) and is a closed map, which is the hypothesis of
[Stacks, Tag 04DV]. -/
@[stacks 04DX "(7) almost cocontinuous"]
public theorem
    smallEtaleBaseChange_isAlmostCocontinuous_of_isIntegralHom_of_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] :
    IsAlmostCocontinuous (smallEtaleBaseChange f) (smallEtaleTopology Y) (smallEtaleTopology X) :=
  smallEtaleBaseChange_isAlmostCocontinuous f
    (fun v _ => hasPropertyC_pullback_snd_of_isIntegralHom_of_universallyInjective f v)
    (fun _ _ => Scheme.Hom.isClosedMap _)

/-! ### Reflecting injections and surjections -/

/-- **Stacks Project, Tag 04DX, part (1).** For an integral universally injective morphism of
schemes `f : X ⟶ Y`, direct image `f_{small, *} : Sh(X_étale) ⥤ Sh(Y_étale)` on sheaves of sets
reflects injections.

This is property (C) fed to [Stacks, Tag 04DT]. -/
@[stacks 04DX "(1) reflects injections"]
public theorem
    smallEtalePushforward_reflectsMonomorphisms_of_isIntegralHom_of_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] :
    ((smallEtaleBaseChange f).sheafPushforwardContinuous (Type v) (smallEtaleTopology Y)
      (smallEtaleTopology X)).ReflectsMonomorphisms :=
  smallEtalePushforward_reflectsMonomorphisms_of_hasPropertyC f
    (hasPropertyC_of_isIntegralHom_of_universallyInjective f)

/-- **Stacks Project, Tag 04DX, part (1).** For an integral universally injective morphism of
schemes `f : X ⟶ Y`, direct image `f_{small, *} : Sh(X_étale) ⥤ Sh(Y_étale)` on sheaves of sets
reflects surjections.

This is property (C) fed to [Stacks, Tag 04DT]. -/
@[stacks 04DX "(1) reflects surjections"]
public theorem
    smallEtalePushforward_reflectsEpimorphisms_of_isIntegralHom_of_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] :
    ((smallEtaleBaseChange f).sheafPushforwardContinuous (Type v) (smallEtaleTopology Y)
      (smallEtaleTopology X)).ReflectsEpimorphisms :=
  smallEtalePushforward_reflectsEpimorphisms_of_hasPropertyC f
    (hasPropertyC_of_isIntegralHom_of_universallyInjective f)

/-! ### Finite connected colimits -/

/-- **Stacks Project, Tag 04DX, part (2).** For an integral universally injective morphism of
schemes `f : X ⟶ Y`, direct image `f_{small, *} : Sh(X_étale) ⥤ Sh(Y_étale)` on sheaves of sets
preserves colimits of every connected shape whose colimits exist. In particular it commutes with
pushouts and coequalizers, and more generally with finite connected colimits.

This is almost cocontinuity of the base-change functor fed to [Stacks, Tag 04BA]. -/
@[stacks 04DX "(2) finite connected colimits"]
public theorem
    smallEtalePushforward_preservesConnectedColimits_of_isIntegralHom_of_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f]
    (I : Type) [SmallCategory I] [IsConnected I]
    [HasColimitsOfShape I (Type (max (u + 1) v))] :
    PreservesColimitsOfShape I
      ((smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
        (smallEtaleTopology Y) (smallEtaleTopology X)) :=
  have : (smallEtaleTopology X).WEqualsLocallyBijective (Type (max (u + 1) v)) :=
    wEqualsLocallyBijective_smallEtaleTopology_type.{v, u} X
  Functor.preservesColimitsOfShape_sheafPushforwardContinuous_of_isAlmostCocontinuous.{
      max (u + 1) v}
    (smallEtaleBaseChange f) (smallEtaleTopology Y) (smallEtaleTopology X)
    (smallEtaleBaseChange_isAlmostCocontinuous_of_isIntegralHom_of_universallyInjective f) I

/-! ### Preserving surjections -/

/-- **Stacks Project, Tag 04DX, part (3).** For an integral universally injective morphism of
schemes `f : X ⟶ Y`, direct image `f_{small, *} : Sh(X_étale) ⥤ Sh(Y_étale)` carries surjections
of sheaves of sets to surjections.

Universal injectivity is not needed here: integrality alone gives property (B), which is the
hypothesis of [Stacks, Tag 04DO]. -/
@[stacks 04DX "(3) preserves surjections"]
public theorem
    smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom_of_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] :
    ((smallEtaleBaseChange f).sheafPushforwardContinuous (Type v) (smallEtaleTopology Y)
      (smallEtaleTopology X)).PreservesEpimorphisms :=
  smallEtalePushforward_preservesEpimorphisms_of_hasPropertyB f (hasPropertyB_of_isIntegralHom f)

/-- **Stacks Project, Tag 04DX, part (3).** For an integral universally injective morphism of
schemes `f : X ⟶ Y`, direct image `f_{small, *} : Ab(X_étale) ⥤ Ab(Y_étale)` carries surjections
of abelian sheaves to surjections.

A morphism of abelian sheaves is epimorphic exactly when it is locally surjective, and local
surjectivity is a property of the underlying morphism of sheaves of sets. Since the underlying
sheaf of sets of a direct image is the direct image of the underlying sheaf of sets, the statement
reduces to its set-valued counterpart. -/
@[stacks 04DX "(3) preserves surjections"]
public theorem
    smallEtalePushforwardAb_preservesEpimorphisms_of_isIntegralHom_of_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] :
    (smallEtalePushforwardAb f).PreservesEpimorphisms := by
  refine ⟨fun {F G} φ hφ => ?_⟩
  have : Sheaf.IsLocallySurjective φ := (Sheaf.isLocallySurjective_iff_epi' Ab.{u + 1} φ).2 hφ
  have hforget : Epi ((sheafCompose (smallEtaleTopology Y) (forget Ab.{u + 1})).map
      ((smallEtalePushforwardAb f).map φ)) :=
    (smallEtalePushforward_preservesEpimorphisms_of_isIntegralHom_of_universallyInjective
      f).preserves ((sheafCompose (smallEtaleTopology X) (forget Ab.{u + 1})).map φ)
  have : Sheaf.IsLocallySurjective ((smallEtalePushforwardAb f).map φ) :=
    (Presheaf.isLocallySurjective_iff_whisker_forget (smallEtaleTopology Y) _).2
      ((Sheaf.isLocallySurjective_iff_epi _).2 hforget)
  exact Sheaf.epi_of_isLocallySurjective _

/-! ### Surjectivity of the counit, and faithfulness -/

/-- **Stacks Project, Tag 04DX, part (4).** For an integral universally injective morphism of
schemes `f : X ⟶ Y`, the counit `f^{-1} f_* F ⟶ F` of the inverse-image/direct-image adjunction is
surjective for every sheaf of sets `F` on the small étale site of `X`.

A right adjoint which reflects surjections has surjective counit, by [Stacks, Tag 04D6]; direct
image reflects surjections by part (1). -/
@[stacks 04DX "(4) surjective counit"]
public theorem smallEtaleAdjunction_counit_epi_of_isIntegralHom_of_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f]
    (F : Sheaf (smallEtaleTopology X) (Type (max (u + 1) v))) :
    Epi ((Functor.sheafAdjunctionContinuous (smallEtaleBaseChange f) (Type (max (u + 1) v))
      (smallEtaleTopology Y) (smallEtaleTopology X)).counit.app F) :=
  (exactness_properties_bundled
    (h := Functor.sheafAdjunctionContinuous (smallEtaleBaseChange f) (Type (max (u + 1) v))
      (smallEtaleTopology Y) (smallEtaleTopology X))).2.2.1
    (smallEtalePushforward_reflectsEpimorphisms_of_isIntegralHom_of_universallyInjective f) F

/-- **Stacks Project, Tag 04DX, part (4).** For an integral universally injective morphism of
schemes `f : X ⟶ Y`, the counit `f^{-1} f_* F ⟶ F` of the inverse-image/direct-image adjunction is
surjective for every abelian sheaf `F` on the small étale site of `X`.

Integrality alone gives property (A), from which this is one of the conclusions of
[Stacks, Tag 04DK]. -/
@[stacks 04DX "(4) surjective counit"]
public theorem smallEtaleAdjunctionAb_counit_epi_of_isIntegralHom_of_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f]
    (F : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    Epi ((smallEtaleAdjunctionAb f).counit.app F) :=
  (smallEtalePushforwardAb_properties_of_hasPropertyA f
    (hasPropertyA_of_isIntegralHom f)).2.2.1 F

/-- **Stacks Project, Tag 04DX, part (5).** For an integral universally injective morphism of
schemes `f : X ⟶ Y`, direct image `f_{small, *} : Sh(X_étale) ⥤ Sh(Y_étale)` on sheaves of sets is
faithful.

A right adjoint with surjective counit is faithful, by [Stacks, Tag 04D6]; the counit is surjective
by part (4). -/
@[stacks 04DX "(5) faithful"]
public theorem smallEtalePushforward_faithful_of_isIntegralHom_of_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] :
    ((smallEtaleBaseChange f).sheafPushforwardContinuous (Type (max (u + 1) v))
      (smallEtaleTopology Y) (smallEtaleTopology X)).Faithful :=
  (exactness_properties_bundled
    (h := Functor.sheafAdjunctionContinuous (smallEtaleBaseChange f) (Type (max (u + 1) v))
      (smallEtaleTopology Y) (smallEtaleTopology X))).2.1
    (smallEtaleAdjunction_counit_epi_of_isIntegralHom_of_universallyInjective.{v} f)

/-- **Stacks Project, Tag 04DX, part (5).** For an integral universally injective morphism of
schemes `f : X ⟶ Y`, direct image `f_{small, *} : Ab(X_étale) ⥤ Ab(Y_étale)` on abelian sheaves is
faithful.

Integrality alone gives property (A), from which this is one of the conclusions of
[Stacks, Tag 04DK]. -/
@[stacks 04DX "(5) faithful"]
public theorem smallEtalePushforwardAb_faithful_of_isIntegralHom_of_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] :
    (smallEtalePushforwardAb f).Faithful :=
  (smallEtalePushforwardAb_properties_of_hasPropertyA f (hasPropertyA_of_isIntegralHom f)).2.2.2

/-! ### Exactness on abelian sheaves -/

/-- **Stacks Project, Tag 04DX, part (6).** For an integral universally injective morphism of
schemes `f : X ⟶ Y`, direct image `f_{small, *} : Ab(X_étale) ⥤ Ab(Y_étale)` is an exact functor.

Direct image is a right adjoint, so it preserves finite limits and is therefore additive; it
preserves epimorphisms by part (3); and an additive functor between abelian categories which
preserves finite limits and epimorphisms preserves finite colimits as well. -/
@[stacks 04DX "(6) exact on abelian sheaves"]
public theorem smallEtalePushforwardAb_exact_of_isIntegralHom_of_universallyInjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] [UniversallyInjective f] :
    exactFunctor (Sheaf (smallEtaleTopology X) Ab.{u + 1})
      (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) (smallEtalePushforwardAb f) := by
  have : (smallEtalePushforwardAb f).IsRightAdjoint := ⟨_, ⟨smallEtaleAdjunctionAb f⟩⟩
  have : (smallEtalePushforwardAb f).Additive := Functor.additive_of_preserves_binary_products _
  have := smallEtalePushforwardAb_preservesEpimorphisms_of_isIntegralHom_of_universallyInjective f
  rw [exactFunctor_iff]
  exact ⟨inferInstance, Stacks.SheafOfModules.LocalCokernel.finiteColimits_of_finiteLimits_epi _⟩

end Stacks.EtaleCohomology

end
