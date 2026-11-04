module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EndActionLiftAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.EtaleTraceIsCounit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.WeightedTrace.WeightedTraceDerived

/-!
# The adjunction `j_! ⊣ j^{-1}` on étale sheaves of `Λ`-modules

Let `j : U ⟶ X` be an étale morphism of schemes, presented as an object of the small étale site
of `X` inside a big étale site, and let `Λ` be a ring. This file constructs the inverse image of
sheaves of `Λ`-modules as the `Λ`-linear lift of the abelian inverse image, the adjunction
`j_! ⊣ j^{-1}` on étale sheaves of `Λ`-modules, and shows that its counit lifts the abelian counit
`AlgebraicGeometry.etaleFShriekAbPullbackAdjunction`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.pullbackMod`: the inverse image `f^{-1}` of sheaves of
  `Λ`-modules along a morphism of a big étale site, for an arbitrary coefficient ring, with
  `AlgebraicGeometry.SmallEtale.pullbackModForgetIso` its identification with the abelian `f^{-1}`
  on underlying abelian sheaves.
* `AlgebraicGeometry.SmallEtale.etaleFShriekModPullbackAdjunction`: the adjunction `j_! ⊣ j^{-1}`
  on étale sheaves of `Λ`-modules for an étale `j`.

## Main results

* `AlgebraicGeometry.SmallEtale.forgetModuleSheaf_map_etaleFShriekModPullbackAdjunction_counit`:
  the morphism of abelian sheaves underlying the counit of the `Λ`-linear adjunction is the counit
  of `AlgebraicGeometry.etaleFShriekAbPullbackAdjunction`.
* `AlgebraicGeometry.SmallEtale.forgetModTrace_etaleFShriekModPullbackAdjunction_counit`: the
  morphism `AlgebraicGeometry.SmallEtale.forgetModTrace` extracts from the counit is the abelian
  counit.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
* [Stacks Project, Tag 0GKH](https://stacks.math.columbia.edu/tag/0GKH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.SmallEtale

universe u v r

section Pullback

variable (B : BigEtaleSite.{u}) (Λ : Type r) [Ring Λ] {X Y : B.Scheme} (f : X ⟶ Y)

/-- **The inverse image `f^{-1}` of sheaves of `Λ`-modules on the small étale sites** along a
morphism of a big étale site, with coefficients in an arbitrary ring: the `Λ`-linear lift of the
abelian `f^{-1}` of Stacks 03Q1. The abelian sheaf underlying `f^{-1}M` is the abelian `f^{-1}`
of the abelian sheaf underlying `M`, with the `Λ`-action its image under `f^{-1}`. -/
public def pullbackMod : ModuleSheaf.{u, v, r} B Y Λ ⥤ ModuleSheaf.{u, v, r} B X Λ :=
  letI : (abPullback.{u, max v r} B f).Additive := additive_abPullback.{u, max v r} B f
  Stacks.ModuleCatLift.moduleLift.{max (u + 1) v r, r, _, _, _, _} Λ
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
    (abPullback.{u, max v r} B f)

/-- **The `Λ`-linear inverse image lifts `f^{-1}`.** Forgetting the `Λ`-module structure of
`pullbackMod` gives the abelian `f^{-1}` on underlying abelian sheaves. -/
public def pullbackModForgetIso :
    pullbackMod.{u, v, r} B Λ f ⋙ forgetModuleSheaf.{u, v, r} B X Λ ≅
      forgetModuleSheaf.{u, v, r} B Y Λ ⋙ abPullback.{u, max v r} B f :=
  letI : (abPullback.{u, max v r} B f).Additive := additive_abPullback.{u, max v r} B f
  Stacks.ModuleCatLift.moduleLiftForgetIso.{max (u + 1) v r, r, _, _, _, _} Λ
    (SmallEtale.topology B Y.obj Y.property) (SmallEtale.topology B X.obj X.property)
    (abPullback.{u, max v r} B f)

/-- The `Λ`-linear inverse image preserves finite limits. -/
public instance pullbackMod_preservesFiniteLimits :
    PreservesFiniteLimits (pullbackMod.{u, v, r} B Λ f) :=
  preservesFiniteLimits_of_forgetModPullIso.{u, v, r} B Λ f _
    (pullbackModForgetIso.{u, v, r} B Λ f)

/-- The `Λ`-linear inverse image is additive. -/
public instance pullbackMod_additive : (pullbackMod.{u, v, r} B Λ f).Additive :=
  additive_of_forgetModPullIso.{u, v, r} B Λ f _ (pullbackModForgetIso.{u, v, r} B Λ f)

/-- The `Λ`-linear inverse image preserves finite colimits. -/
public instance pullbackMod_preservesFiniteColimits :
    PreservesFiniteColimits (pullbackMod.{u, v, r} B Λ f) :=
  preservesFiniteColimits_of_forgetModPullIso.{u, v, r} B Λ f _
    (pullbackModForgetIso.{u, v, r} B Λ f)

end Pullback

section EtaleAdjunction

variable (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (U : SmallEtale B X hX)
  (Λ : Type u) [Ring Λ]

/-- **The adjunction `j_! ⊣ j^{-1}` for an étale `j`, with coefficients in a ring `Λ`.** It is
the lift of the abelian adjunction `AlgebraicGeometry.etaleFShriekAbPullbackAdjunction` of
Stacks 03S3 to sheaves of `Λ`-modules. -/
public def etaleFShriekModPullbackAdjunction :
    fShriekMod.{u, u + 1, u} B Λ U.obj.hom ⊣ pullbackMod.{u, u + 1, u} B Λ U.obj.hom :=
  letI : (fShriekFunctor.{u, u + 1} B U.obj.hom).Additive :=
    fShriekFunctor_additive.{u, u + 1} B U.obj.hom
  letI : (abPullback.{u, u + 1} B U.obj.hom).Additive :=
    additive_abPullback.{u, u + 1} B U.obj.hom
  Stacks.ModuleCatLift.moduleLiftAdjunction.{u + 1, u, _, _, _, _} Λ
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    (SmallEtale.topology B (B.obj X hX).obj (B.obj X hX).property)
    (fShriekFunctor.{u, u + 1} B U.obj.hom) (abPullback.{u, u + 1} B U.obj.hom)
    (etaleFShriekAbPullbackAdjunction B X hX U)

/-- **The counit of the `Λ`-linear adjunction lifts the abelian counit of Stacks 03S3.** The
morphism of abelian sheaves underlying the counit of
`AlgebraicGeometry.SmallEtale.etaleFShriekModPullbackAdjunction` at a sheaf of `Λ`-modules `M`
is the counit of `AlgebraicGeometry.etaleFShriekAbPullbackAdjunction` at the abelian sheaf
underlying `M`. -/
public theorem forgetModuleSheaf_map_etaleFShriekModPullbackAdjunction_counit
    (M : ModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ) :
    (forgetModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ).map
        ((etaleFShriekModPullbackAdjunction B X hX U Λ).counit.app M) =
      (etaleFShriekAbPullbackAdjunction B X hX U).counit.app
        ((forgetModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ).obj M) :=
  let : (fShriekFunctor.{u, u + 1} B U.obj.hom).Additive :=
    fShriekFunctor_additive.{u, u + 1} B U.obj.hom
  let : (abPullback.{u, u + 1} B U.obj.hom).Additive :=
    additive_abPullback.{u, u + 1} B U.obj.hom
  Stacks.ModuleCatLift.sheafCompose_map_moduleLiftAdjunction_counit_app.{u + 1, u, _, _, _, _} Λ
    (SmallEtale.topology B U.obj.left.obj U.obj.left.property)
    (SmallEtale.topology B (B.obj X hX).obj (B.obj X hX).property)
    (fShriekFunctor.{u, u + 1} B U.obj.hom) (abPullback.{u, u + 1} B U.obj.hom)
    (etaleFShriekAbPullbackAdjunction B X hX U) M

/-- The identification of the abelian sheaf underlying `j_! j^{-1}M` with `j_! j^{-1}` of the
abelian sheaf underlying `M` is the identity for the `Λ`-linear inverse image
`AlgebraicGeometry.SmallEtale.pullbackMod`. -/
public theorem forgetFShriekModPullNatIso_pullbackMod_hom_app
    (M : ModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ) :
    (forgetFShriekModPullNatIso.{u, u + 1, u} B Λ U.obj.hom
        (pullbackMod.{u, u + 1, u} B Λ U.obj.hom)
        (pullbackModForgetIso.{u, u + 1, u} B Λ U.obj.hom)).hom.app M = 𝟙 _ := by
  change (fShriekFunctor.{u, u + 1} B U.obj.hom).map
      ((pullbackModForgetIso.{u, u + 1, u} B Λ U.obj.hom).inv.app M) ≫
      (fShriekModForgetIso.{u, u + 1, u} B Λ U.obj.hom).inv.app
        ((pullbackMod.{u, u + 1, u} B Λ U.obj.hom).obj M) = 𝟙 _
  rw [show (pullbackModForgetIso.{u, u + 1, u} B Λ U.obj.hom).inv.app M = 𝟙 _ from rfl,
    show (fShriekModForgetIso.{u, u + 1, u} B Λ U.obj.hom).inv.app
      ((pullbackMod.{u, u + 1, u} B Λ U.obj.hom).obj M) = 𝟙 _ from rfl]
  exact (Category.comp_id _).trans (CategoryTheory.Functor.map_id _ _)

/-- **The counit is a trace map at `Λ`-coefficients.** The morphism of abelian sheaves which
`AlgebraicGeometry.SmallEtale.forgetModTrace` extracts from the counit of
`AlgebraicGeometry.SmallEtale.etaleFShriekModPullbackAdjunction` is the counit of the abelian
adjunction of Stacks 03S3. -/
public theorem forgetModTrace_etaleFShriekModPullbackAdjunction_counit
    (M : ModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ) :
    forgetModTrace.{u, u + 1, u} B Λ U.obj.hom (pullbackMod.{u, u + 1, u} B Λ U.obj.hom)
        (pullbackModForgetIso.{u, u + 1, u} B Λ U.obj.hom) M
        ((etaleFShriekModPullbackAdjunction B X hX U Λ).counit.app M) =
      (etaleFShriekAbPullbackAdjunction B X hX U).counit.app
        ((forgetModuleSheaf.{u, u + 1, u} B (B.obj X hX) Λ).obj M) := by
  rw [forgetModTrace, forgetFShriekModPullNatIso_pullbackMod_hom_app]
  exact (Category.id_comp _).trans
    (forgetModuleSheaf_map_etaleFShriekModPullbackAdjunction_counit B X hX U Λ M)

end EtaleAdjunction

end AlgebraicGeometry.SmallEtale

end
