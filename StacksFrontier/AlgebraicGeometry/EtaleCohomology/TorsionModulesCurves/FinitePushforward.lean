module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.Finiteness.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SmallEtaleInverseImageModuleExact
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackSections
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison
public import StacksFrontier.Homology.CompositeCollapse
import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness of the cohomology of a direct image along a finite morphism

Let `Λ` be a ring and let `f : X ⟶ Y` be a morphism of a big étale site. For a sheaf `ℱ` of
`Λ`-modules on the small étale site of `X` whose higher direct images along `f` vanish, the
cohomology of `f_*ℱ` on `Y` agrees with the cohomology of `ℱ` on `X` in every degree; so if
`H^q_étale(X, ℱ)` is a finite `Λ`-module then so is `H^q_étale(Y, f_*ℱ)`.

## Main definitions

* `Stacks.EtaleCohomology.TorsionModules.moduleGlobalSections` — global sections of a sheaf of
  `Λ`-modules on a small étale site, i.e. sections over the final object, the convention used
  for étale cohomology in `StacksFrontier.AlgebraicGeometry.EtaleCohomology.LeraySpectralSequence`.
* `Stacks.EtaleCohomology.TorsionModules.modulePushforward` — direct image of sheaves of
  `Λ`-modules along a morphism of the big étale site.
* `Stacks.EtaleCohomology.TorsionModules.modulePushforwardCompGlobalSectionsIso` — global
  sections on the target composed with direct image are global sections on the source.

## Main results

* `Stacks.EtaleCohomology.TorsionModules.moduleCohomologyPushforwardIso` — the collapse
  isomorphism `H^q_étale(X, ℱ) ≅ H^q_étale(Y, f_*ℱ)` when `R^q f_*ℱ = 0` for `q > 0`.
* `Stacks.EtaleCohomology.TorsionModules.module_finite_cohomology_pushforward` — **Stacks Tag
  0GJD**, the transport of finiteness along that isomorphism.

## Implementation notes

**What is proved and what is assumed.** The source's proof of Tag 0GJD is two sentences: the
vanishing of `R^q f_*` for `q > 0` along a finite morphism (Proposition 03QP) makes the Leray
spectral sequence collapse (Cohomology on Sites, Lemma 0733), giving
`H^q_étale(X, ℱ) = H^q_étale(Y, f_*ℱ)`; finiteness then transports across that isomorphism.
Nothing else in the hypotheses of the source statement — that `Λ` is Noetherian, that `k` is
algebraically closed, that `X` and `Y` are separated of finite type over `k` of dimension at
most one — is used, and none of it is used here either.

Tag 03QP is **not** available in this repository: the comparison map of the stalk of a direct
image with the product of the stalks over the fibre is constructed in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/FinitePushforwardStalk.lean`, but its bijectivity
is not proved there, and part (2) of the tag — the vanishing of the higher direct images — is
nowhere in the tree. It is therefore carried as the explicit hypothesis `h03QP` of
`module_finite_cohomology_pushforward`, in its general form: universally quantified over every
morphism of the big étale site whose underlying morphism of schemes is finite, every sheaf of
`Λ`-modules on the source, and every positive degree. It is instantiated only inside the proof,
at the morphism and the sheaf of the statement.

**The collapse.** Tag 0733 is in the tree, but for modules over the structure sheaf of a ringed
topos (`StacksFrontier/CategoryTheory/Sites/Cohomology/Modules/LerayCollapse.lean`), not for
sheaves of `Λ`-modules over a fixed ring, which is what the finiteness statement is about. What
is used instead is the mechanism behind it, `Stacks.RightDerivedComp.objIso`: for `G` additive,
left exact and preserving injective objects and `A` a `G`-acyclic object,
`R^n(G ⋙ T)(A) ≅ R^n T(G A)`. Here `G` is the direct image, which is precomposition with base
change, hence left exact; it preserves injective objects because its left adjoint, the inverse
image of module sheaves, is exact by
`AlgebraicGeometry.preservesFiniteLimits_smallEtaleSheafPullback_moduleCat`. The remaining input
is the factorisation of global sections through the direct image, which is `Iso.refl` composed
with the identification of the base change of the final object as a final object, exactly as in
`AlgebraicGeometry.smallEtalePushforwardCompGlobalSectionsIso` for abelian coefficients.

## References

* [Stacks Project, Tag 0GJD](https://stacks.math.columbia.edu/tag/0GJD)
* [Stacks Project, Tag 03QP](https://stacks.math.columbia.edu/tag/03QP)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u w r

namespace Stacks.EtaleCohomology.TorsionModules

variable (B : BigEtaleSite.{u}) (Λ : Type r) [CommRing Λ]

/-- Global sections of a sheaf of `Λ`-modules on the small étale site of `X`: the sections over
the final object `X / X` of that site. This is the convention in which étale cohomology is taken
in `AlgebraicGeometry.smallEtaleGlobalSections`. -/
@[sga "4½ Arcata 1.6.5" "special case"]
abbrev moduleGlobalSections (X : B.Scheme) :
    Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ) ⥤
      ModuleCat.{max (u + 1) w} Λ :=
  (sheafSections (SmallEtale.topology B X.obj X.property)
    (ModuleCat.{max (u + 1) w} Λ)).obj (op (SmallEtale.final B X.obj X.property))

/-- Global sections of a sheaf of `Λ`-modules are additive in the sheaf. -/
instance moduleGlobalSections_additive (X : B.Scheme) :
    (moduleGlobalSections.{u, w} B Λ X).Additive where
  map_add := by intros; rfl

variable {X Y : B.Scheme} (f : X ⟶ Y)

/-- Direct image of sheaves of `Λ`-modules along `f`, for the small étale topologies:
precomposition with base change along `f`. On sections it is `(f_*ℱ)(V) = ℱ(V ×_Y X)`. -/
abbrev modulePushforward :
    Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ) ⥤
      Sheaf (SmallEtale.topology B Y.obj Y.property) (ModuleCat.{max (u + 1) w} Λ) :=
  (smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{max (u + 1) w} Λ)
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)

/-- Direct image of sheaves of `Λ`-modules is additive. -/
instance modulePushforward_additive : (modulePushforward.{u, w} B Λ f).Additive where
  map_add := by intros; rfl

/-- Sections of a direct image over an object `V` of the small étale site of `Y` are the sections
of the original sheaf over the base change `X ×_Y V`: the underlying presheaf of a direct image
is restriction along the base-change functor, so this is an identity. -/
def modulePushforwardCompSectionsIso (V : SmallEtale B Y.obj Y.property) :
    modulePushforward.{u, w} B Λ f ⋙
        (sheafSections (SmallEtale.topology B Y.obj Y.property)
          (ModuleCat.{max (u + 1) w} Λ)).obj (op V) ≅
      (sheafSections (SmallEtale.topology B X.obj X.property)
        (ModuleCat.{max (u + 1) w} Λ)).obj (op ((smallEtaleBaseChange B f).obj V)) :=
  Iso.refl _

/-- Sections over the base change `X ×_Y Y` of the final object of the small étale site of `Y`
are global sections on the small étale site of `X`: that base change is again a final object. -/
def moduleBaseChangeFinalSectionsIso :
    (sheafSections (SmallEtale.topology B X.obj X.property)
          (ModuleCat.{max (u + 1) w} Λ)).obj
        (op ((smallEtaleBaseChange B f).obj (SmallEtale.final B Y.obj Y.property))) ≅
      moduleGlobalSections.{u, w} B Λ X :=
  (sheafSections (SmallEtale.topology B X.obj X.property)
    (ModuleCat.{max (u + 1) w} Λ)).mapIso
      (((smallEtaleBaseChange_finalIsTerminal B f).uniqueUpToIso
        (SmallEtale.finalIsTerminal B X.obj X.property)).symm.op)

/-- **Global sections factor through the direct image.** Global sections of sheaves of
`Λ`-modules on the small étale site of `Y`, composed with direct image along `f`, are global
sections on the small étale site of `X`. -/
def modulePushforwardCompGlobalSectionsIso :
    modulePushforward.{u, w} B Λ f ⋙ moduleGlobalSections.{u, w} B Λ Y ≅
      moduleGlobalSections.{u, w} B Λ X :=
  modulePushforwardCompSectionsIso.{u, w} B Λ f (SmallEtale.final B Y.obj Y.property) ≪≫
    moduleBaseChangeFinalSectionsIso.{u, w} B Λ f

section Collapse

variable
  [HasSheafify (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ)]
  [HasSheafify (SmallEtale.topology B Y.obj Y.property) (ModuleCat.{max (u + 1) w} Λ)]
  [HasInjectiveResolutions
    (Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))]
  [HasInjectiveResolutions
    (Sheaf (SmallEtale.topology B Y.obj Y.property) (ModuleCat.{max (u + 1) w} Λ))]
  [(modulePushforward.{u, w} B Λ f).IsRightAdjoint]

attribute [local instance]
  AlgebraicGeometry.preservesFiniteLimits_lan_op_smallEtaleBaseChange_moduleCat
  AlgebraicGeometry.preservesFiniteLimits_smallEtaleSheafPullback_moduleCat

/-- The direct image of sheaves of `Λ`-modules is left exact: limits of sheaves are computed in
presheaves, and the direct image is precomposition with base change. -/
instance modulePushforward_preservesFiniteLimits :
    PreservesFiniteLimits (modulePushforward.{u, w} B Λ f) := by
  have : PreservesLimitsOfSize.{0, 0} (modulePushforward.{u, w} B Λ f) :=
    (Functor.sheafAdjunctionContinuous (smallEtaleBaseChange B f)
      (ModuleCat.{max (u + 1) w} Λ) (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)).rightAdjoint_preservesLimits
  exact ⟨fun _ _ _ => inferInstance⟩

/-- The direct image of sheaves of `Λ`-modules preserves injective objects: its left adjoint,
the inverse image, is left exact by
`AlgebraicGeometry.preservesFiniteLimits_smallEtaleSheafPullback_moduleCat`, hence preserves
monomorphisms. -/
@[sga "4½ Arcata 2.3.3" "more general"]
instance modulePushforward_preservesInjectiveObjects :
    (modulePushforward.{u, w} B Λ f).PreservesInjectiveObjects :=
  have : PreservesFiniteLimits ((smallEtaleBaseChange B f).sheafPullback
      (ModuleCat.{max (u + 1) w} Λ) (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property)) := inferInstance
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (Functor.sheafAdjunctionContinuous (smallEtaleBaseChange B f)
      (ModuleCat.{max (u + 1) w} Λ) (SmallEtale.topology B Y.obj Y.property)
      (SmallEtale.topology B X.obj X.property))

/-- **The collapse isomorphism** `H^q_étale(X, ℱ) ≅ H^q_étale(Y, f_*ℱ)` for a sheaf of
`Λ`-modules `ℱ` whose higher direct images along `f` vanish.

This is part (1) of Stacks 0733 for sheaves of `Λ`-modules on small étale sites. Both sides are
the degree-`q` homology of global sections on `Y` applied to the direct image of an injective
resolution of `ℱ`: that complex is an injective resolution of `f_*ℱ` because the direct image is
left exact, preserves injective objects, and is acyclic at `ℱ`; and global sections on `Y`
composed with the direct image are global sections on `X`. -/
def moduleCohomologyPushforwardIso
    (ℱ : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))
    (hℱ : ∀ q, 0 < q → IsZero (((modulePushforward.{u, w} B Λ f).rightDerived q).obj ℱ))
    (q : ℕ) :
    ((moduleGlobalSections.{u, w} B Λ X).rightDerived q).obj ℱ ≅
      ((moduleGlobalSections.{u, w} B Λ Y).rightDerived q).obj
        ((modulePushforward.{u, w} B Λ f).obj ℱ) :=
  ((_root_.ModuleSheafCohomology.rightDerivedIso
      (modulePushforwardCompGlobalSectionsIso.{u, w} B Λ f) q).app ℱ).symm ≪≫
    Stacks.RightDerivedComp.objIso (modulePushforward.{u, w} B Λ f)
      (injectiveResolution ℱ) hℱ (moduleGlobalSections.{u, w} B Λ Y) q

end Collapse

/-- **Stacks Project, Tag 0GJD**, granted Tag 03QP for sheaves of `Λ`-modules as the hypothesis
`h03QP`.

Let `Λ` be a ring, let `f : X ⟶ Y` be a morphism of a big étale site whose underlying morphism
of schemes is finite, and let `ℱ` be a sheaf of `Λ`-modules on the small étale site of `X`. If
`H^q_étale(X, ℱ)` is a finite `Λ`-module, then so is `H^q_étale(Y, f_*ℱ)`.

The hypothesis `h03QP` is the general statement of part (2) of Stacks 03QP for sheaves of
`Λ`-modules: for *every* morphism of the big étale site with finite underlying morphism of
schemes, *every* sheaf of `Λ`-modules on its source and *every* positive degree, the higher
direct image vanishes. It is a different tag from the one being proved, it quantifies over all
of its own inputs, and it is instantiated only inside the proof, at `f` and `ℱ`. Nothing about
`H^q_étale(Y, f_*ℱ)` — the conclusion — is assumed.

The remaining hypotheses of the source statement (`Λ` Noetherian, `k` algebraically closed,
`X` and `Y` separated of finite type over `k` of dimension at most one) are not needed: the
source's proof does not use them, and neither does this one. -/
@[stacks 0GJD "granted Tag 03QP for sheaves of Λ-modules, as the hypothesis h03QP"]
theorem module_finite_cohomology_pushforward
    [∀ Z : B.Scheme,
      HasSheafify (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{max (u + 1) w} Λ)]
    [∀ Z : B.Scheme, HasInjectiveResolutions
      (Sheaf (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{max (u + 1) w} Λ))]
    [∀ (Z W : B.Scheme) (g : Z ⟶ W), (modulePushforward.{u, w} B Λ g).IsRightAdjoint]
    (h03QP : ∀ (Z W : B.Scheme) (g : Z ⟶ W), IsFinite (B.inclusion.map g) →
      ∀ (𝒢 : Sheaf (SmallEtale.topology B Z.obj Z.property) (ModuleCat.{max (u + 1) w} Λ))
        (q : ℕ), 0 < q → IsZero (((modulePushforward.{u, w} B Λ g).rightDerived q).obj 𝒢))
    (hf : IsFinite (B.inclusion.map f))
    (ℱ : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{max (u + 1) w} Λ))
    (q : ℕ)
    (hfin : Module.Finite Λ (((moduleGlobalSections.{u, w} B Λ X).rightDerived q).obj ℱ)) :
    Module.Finite Λ (((moduleGlobalSections.{u, w} B Λ Y).rightDerived q).obj
      ((modulePushforward.{u, w} B Λ f).obj ℱ)) :=
  have := hfin
  Module.Finite.equiv
    (moduleCohomologyPushforwardIso.{u, w} B Λ f ℱ (h03QP X Y f hf ℱ) q).toLinearEquiv

end Stacks.EtaleCohomology.TorsionModules

end
