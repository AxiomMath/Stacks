module

public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.DepthOneQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.HartogsExtension.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusColimitStalk
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.CoherentPushforwardCriterion.UniversallyCatenaryDimension
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtensionExistence
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.NestedImprovementComposition
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.OpenExtension


/-!
# Improving a coherent module along a closed subscheme by pushing forward from an open

Let `X` be a Noetherian scheme, let `Z ⊆ X` be stable under specialization, let `F` be a
coherent `𝒪_X`-module and let `U ⊆ X` be an open whose complement `Z' = X \ U` lies inside `Z`.
The source's construction of an improvement of `F` along `Z' ⊆ Z` is: first replace `F` by its
depth-one quotient `F'` along `Z` ([Stacks, Tag 0DX3]), then extend `F'` across `Z'` by pushing
forward from `U`, that is `F'' = j_*(F'|_U)` for `j : U → X` the inclusion.  The composite
`F → F' → F''` is the improvement, and coherence of `F''` is Kollár's criterion
[Stacks, Tag 0AWB].

## Main results

* `AlgebraicGeometry.isIso_stalkMap_unit_pullbackPushforward_of_mem` and
  `AlgebraicGeometry.depth_stalk_pushforward_restrict_eq_of_mem`: the canonical map to the
  extension of a restriction is an isomorphism on the stalk at a point of `U`, so the depth of
  the stalk is unchanged there.
* `AlgebraicGeometry.isNestedImprovement_toDepthOneQuotient_comp_unit`: the composite of the
  depth-one quotient map with the unit of the pullback--pushforward adjunction along `U.ι` is an
  improvement of `F` along `Z' ⊆ Z`, assuming the extension `j_*(F'|_U)` is coherent.
* `AlgebraicGeometry.isCoherent_pushforward_restrict_depthOneQuotient_of_universallyCatenary`:
  [Stacks, Tag 0AWB] specialised to the extension of the depth-one quotient, which supplies that
  coherence hypothesis.
* `AlgebraicGeometry.isNestedImprovement_pushforward_restrict_depthOneQuotient`: the two
  combined — the source's construction, carrying only the source's hypotheses.

## Implementation notes

Restriction to the open subscheme `U` is pullback along `U.ι` and the canonical map from a
module to the extension of its restriction is the unit of
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`, as in
`StacksFrontier/AlgebraicGeometry/LocalCohomology/ImprovingCoherentModules/OpenExtension.lean`.
The conclusion is `AlgebraicGeometry.IsNestedImprovement Z Z'`, and it is not proved clause by
clause here: composing the depth-one quotient of `F` along a specialization-stable `T` with a
depth-two extension of that quotient along a `T' ⊆ T` already gives an improvement along
`T' ⊆ T`, which is `AlgebraicGeometry.isNestedImprovement_depthOneQuotient_comp`. Only the
instantiation `T := Z`, `T' := Z'` is carried out, and the inclusion `T' ⊆ T` it needs is the
hypothesis that the complement of `U` lie in `Z`. What has to be supplied is therefore just
`AlgebraicGeometry.IsDepthTwoExtension Z'` for the unit:

* its coherence clause is the hypothesis, supplied by [Stacks, Tag 0AWB] in the second theorem;
* its stalk-isomorphism clause outside `Z'` — that is, at the points of `U` — is
  `AlgebraicGeometry.isIso_stalkMap_unit_pullbackPushforward_of_mem`, read off the unit of the
  restriction adjunction
  (`Stacks.ModuleSkyscraper.isIso_modulesStalkFunctor_map_restrictAdjunction_unit_app`);
* its depth clause on `Z'` is `AlgebraicGeometry.two_le_depth_stalk_pushforward_restrict`, which
  is [Stacks, Tag 0EY0] part (3) for an open immersion.

The dimension hypothesis of the coherence statement is kept in the exact spelling of
`AlgebraicGeometry.isCoherent_pushforward_iff_two_le_ringKrullDim_stalk_pointClosure`, so that
the criterion applies with no bridging: the subset `Z` and the choice of `U` play no role in it
beyond fixing the module whose associated points it ranges over.  The `(S₁)` hypothesis on the
formal fibres is likewise the source's, stated at the points outside the range of `U.ι`.

The module structure on a stalk is spelled out wherever a depth appears, because the stalk of an
`𝒪_X`-module is built as an abelian group and carries no such instance by default; the spelling
is the one of `AlgebraicGeometry.IsNestedImprovement`.

## References

* [Stacks Project, Tag 0DX5](https://stacks.math.columbia.edu/tag/0DX5)
* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
* [Stacks Project, Tag 0AWB](https://stacks.math.columbia.edu/tag/0AWB)
* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The canonical map `G → j_*(G|_U)` is an isomorphism on the stalk over the local ring at every
point of the open subscheme `U`.

The unit of the restriction adjunction is invertible on stalks at the points of `U`
(`Stacks.ModuleSkyscraper.isIso_modulesStalkFunctor_map_restrictAdjunction_unit_app`), and the
unit of the pullback adjunction is that unit followed by the image of the isomorphism
`Scheme.Modules.restrictFunctorIsoPullback` under the pushforward.  No hypothesis on `X` or on
`G` is used. -/
public theorem isIso_stalkMap_unit_pullbackPushforward_of_mem {X : Scheme.{u}}
    (G : X.Modules) (U : X.Opens) (x : X) (hx : x ∈ (U : Set X)) :
    IsIso (AlgebraicGeometry.SheafOfModules.stalkMap X.ringCatSheaf x
      ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app G)) := by
  -- the unit factors through the unit of the restriction adjunction and an isomorphism
  have hunit : (Scheme.Modules.restrictAdjunction U.ι).unit.app G ≫
      (Scheme.Modules.pushforward U.ι).map
          ((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app G) =
        (Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app G :=
    Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction U.ι)
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι) G
  have h₁ :=
    Stacks.ModuleSkyscraper.isIso_modulesStalkFunctor_map_restrictAdjunction_unit_app U G ⟨x, hx⟩
  have h : IsIso ((Stacks.ModuleSkyscraper.modulesStalkFunctor X x).map
      ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app G)) := by
    rw [← hunit, Functor.map_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ inferInstance
  rw [ConcreteCategory.isIso_iff_bijective] at h ⊢
  exact h

/-- The depth of the stalk is unchanged by the canonical map `G → j_*(G|_U)` at a point of the
open subscheme `U`.

The stalk map there is bijective by
`AlgebraicGeometry.isIso_stalkMap_unit_pullbackPushforward_of_mem`, hence a linear equivalence of
modules over the local ring at the point, and depth is invariant under a linear equivalence. -/
public theorem depth_stalk_pushforward_restrict_eq_of_mem {X : Scheme.{u}}
    (G : X.Modules) (U : X.Opens) (x : X) (hx : x ∈ (U : Set X)) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) G.val x
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pushforward U.ι).obj
            ((Scheme.Modules.pullback U.ι).obj G)).val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf)
        ((Scheme.Modules.pushforward U.ι).obj ((Scheme.Modules.pullback U.ι).obj G)).val x
    Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf x) =
      Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pushforward U.ι).obj
            ((Scheme.Modules.pullback U.ι).obj G)).val.presheaf x) := by
  have hbij : Function.Bijective
      (stalkMapLinear (R := X.presheaf) G.val
        ((Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pushforward U.ι).obj G).val
        ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app G).val x) :=
    (ConcreteCategory.isIso_iff_bijective _).mp
      (isIso_stalkMap_unit_pullbackPushforward_of_mem G U x hx)
  exact Module.depth_eq_depth_of_linearEquiv _ (LinearEquiv.ofBijective _ hbij)

/-- **The source's construction for [Stacks, Tag 0DX5].** Let `Z` be stable under specialization
and let `U` be an open whose complement lies in `Z`.  The depth-one quotient map of `F` along `Z`
followed by the canonical map of that quotient to the extension of its restriction to `U` is an
improvement of `F` along `(X \ U) ⊆ Z`.

This is the instantiation of `AlgebraicGeometry.isNestedImprovement_depthOneQuotient_comp`, which
composes the depth-one quotient with an arbitrary depth-two extension of it, at the depth-two
extension given by the canonical map to `j_*(F'|_U)`: that map is an isomorphism on the stalks at
the points of `U` by `AlgebraicGeometry.isIso_stalkMap_unit_pullbackPushforward_of_mem`, and its
target has depth at least two outside `U` by
`AlgebraicGeometry.two_le_depth_stalk_pushforward_restrict`, which is [Stacks, Tag 0EY0]
part (3). -/
public theorem isNestedImprovement_toDepthOneQuotient_comp_unit
    (X : Scheme.{u}) [IsNoetherian X] (Z : Set X) (hZ : StableUnderSpecialization Z)
    (F : X.Modules) [F.IsCoherent] (U : X.Opens) (hUZ : ((U : Set X))ᶜ ⊆ Z)
    [((Scheme.Modules.pushforward U.ι).obj
        ((Scheme.Modules.pullback U.ι).obj (depthOneQuotient X Z hZ F))).IsCoherent] :
    IsNestedImprovement Z ((U : Set X))ᶜ
      (toDepthOneQuotient X Z hZ F ≫
        (Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app
          (depthOneQuotient X Z hZ F)) := by
  refine isNestedImprovement_depthOneQuotient_comp X Z ((U : Set X))ᶜ hUZ hZ F _ ⟨?_, ?_, ?_⟩
  · dsimp only [Functor.comp_obj]
    infer_instance
  · exact fun x hx =>
      isIso_stalkMap_unit_pullbackPushforward_of_mem (depthOneQuotient X Z hZ F) U x
        (not_not.mp hx)
  · intro x hx
    exact two_le_depth_stalk_pushforward_restrict X (depthOneQuotient X Z hZ F) U x hx

/-- **[Stacks, Tag 0AWB] for the extension of the depth-one quotient.** On a Noetherian,
universally catenary scheme whose local rings outside `U` have `(S₁)` formal fibres, the
extension `j_*(F'|_U)` of the depth-one quotient `F'` of `F` along `Z` is coherent as soon as the
closure of each associated point of `F'|_U` has dimension at least two at each of its points
outside `U`.

This is `AlgebraicGeometry.isCoherent_pushforward_iff_two_le_ringKrullDim_stalk_pointClosure`
applied to the open immersion `U.ι` and the module `F'|_U`; the hypotheses are in the spelling
that criterion uses, so nothing is weakened or re-derived here. -/
public theorem isCoherent_pushforward_restrict_depthOneQuotient_of_universallyCatenary
    (X : Scheme.{u}) [IsNoetherian X] (Z : Set X) (hZ : StableUnderSpecialization Z)
    (F : X.Modules) [F.IsCoherent] (U : X.Opens)
    (hX : Scheme.IsUniversallyCatenary X)
    (hFibres : ∀ z : X, z ∉ U.ι.opensRange →
      ∀ q : PrimeSpectrum (X.presheaf.stalk z),
        HasSerreCondition
          (X.completedLocalRing z ⊗[X.presheaf.stalk z] q.asIdeal.ResidueField) 1)
    (hdim : ∀ x : U.toScheme,
      x ∈ Stacks.Divisors.associatedPoints
          ((Scheme.Modules.pullback U.ι).obj (depthOneQuotient X Z hZ F)) →
        ∀ y : (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({U.ι x} : Set X))).subscheme,
          (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({U.ι x} : Set X))).subschemeι y ∉ U.ι.opensRange →
          2 ≤ ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({U.ι x} : Set X))).subscheme.presheaf.stalk y)) :
    ((Scheme.Modules.pushforward U.ι).obj
      ((Scheme.Modules.pullback U.ι).obj (depthOneQuotient X Z hZ F))).IsCoherent :=
  let : (depthOneQuotient X Z hZ F).IsCoherent := (depthOneQuotient_spec X Z hZ F).1
  let : ((Scheme.Modules.pullback U.ι).obj (depthOneQuotient X Z hZ F)).IsCoherent :=
    isCoherent_pullback U.ι _
  (isCoherent_pushforward_iff_two_le_ringKrullDim_stalk_pointClosure U.ι hX hFibres).mpr hdim

/-- **[Stacks, Tag 0DX5].** On a Noetherian, universally catenary scheme whose local rings
outside `U` have `(S₁)` formal fibres, and under the dimension condition of
[Stacks, Tag 0AWB], the depth-one quotient of `F` along `Z` followed by the canonical map to the
extension of its restriction to `U` is an improvement of `F` along `(X \ U) ⊆ Z`.

This is `AlgebraicGeometry.isNestedImprovement_toDepthOneQuotient_comp_unit` with its coherence
hypothesis discharged by
`AlgebraicGeometry.isCoherent_pushforward_restrict_depthOneQuotient_of_universallyCatenary`, so
the hypotheses are exactly the source's together with the choice of `U`. -/
public theorem isNestedImprovement_pushforward_restrict_depthOneQuotient
    (X : Scheme.{u}) [IsNoetherian X] (Z : Set X) (hZ : StableUnderSpecialization Z)
    (F : X.Modules) [F.IsCoherent] (U : X.Opens) (hUZ : ((U : Set X))ᶜ ⊆ Z)
    (hX : Scheme.IsUniversallyCatenary X)
    (hFibres : ∀ z : X, z ∉ U.ι.opensRange →
      ∀ q : PrimeSpectrum (X.presheaf.stalk z),
        HasSerreCondition
          (X.completedLocalRing z ⊗[X.presheaf.stalk z] q.asIdeal.ResidueField) 1)
    (hdim : ∀ x : U.toScheme,
      x ∈ Stacks.Divisors.associatedPoints
          ((Scheme.Modules.pullback U.ι).obj (depthOneQuotient X Z hZ F)) →
        ∀ y : (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({U.ι x} : Set X))).subscheme,
          (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({U.ι x} : Set X))).subschemeι y ∉ U.ι.opensRange →
          2 ≤ ringKrullDim ((Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({U.ι x} : Set X))).subscheme.presheaf.stalk y)) :
    IsNestedImprovement Z ((U : Set X))ᶜ
      (toDepthOneQuotient X Z hZ F ≫
        (Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app
          (depthOneQuotient X Z hZ F)) :=
  let := isCoherent_pushforward_restrict_depthOneQuotient_of_universallyCatenary
    X Z hZ F U hX hFibres hdim
  isNestedImprovement_toDepthOneQuotient_comp_unit X Z hZ F U hUZ

end AlgebraicGeometry

end
