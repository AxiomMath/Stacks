module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.AffineHigherDirectImage.Natural

/-!
# The comparison of [Stacks, Tag 089W] in the module-valued model, naturally in the module

For an affine morphism of schemes `f : X ⟶ S`, [Stacks, Tag 089W] identifies the cohomology of a
quasi-coherent `𝒪_X`-module with the cohomology of its direct image. This library has that
identification twice over, in two different categories:

* `Stacks.AffineCohomologyPushforward.cohomologyPushforwardIso` is an isomorphism of **functors**
  on the quasi-coherent `𝒪_X`-modules — so it is natural in the module — but it is valued in
  abelian groups, because the cohomology functor it is built from, `Hfunctor`, forgets the
  scalars;
* `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward` is valued in `Γ(S, ⊤)`-modules,
  which is the model every finiteness statement in this library is phrased in, but it is defined
  one module at a time and **has no naturality lemma.**

**This file supplies the missing link**: the natural isomorphism, read in the module-valued model
after forgetting the scalars. What makes it possible is
`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso`, which says that deriving
the module-valued global sections and then forgetting the module structure *is* the
abelian-group-valued cohomology functor `Hfunctor`; at a scheme that reads
`(Stacks.Cohomology.AffineBase.moduleGlobalSections X).rightDerived i ⋙ forget₂ ≅
Hfunctor X.ringCatSheaf ⊤ i` on the nose.

## Main definitions

* `Stacks.AffineCohomologyPushforward.cohomologyPushforwardModuleIso`: **the comparison of
  [Stacks, Tag 089W] between the module-valued cohomology functors, after forgetting the
  scalars, as an isomorphism of functors on the quasi-coherent `𝒪_X`-modules.**

## Main results

* `Stacks.AffineCohomologyPushforward.cohomologyPushforwardModuleIso_naturality`: the comparison
  commutes with the map induced on cohomology by a morphism of quasi-coherent modules. This is
  the statement that `cohomologyIsoPushforward` does not have.
* `Stacks.AffineCohomologyPushforward.cohomologyPushforwardModuleIso_hom_app_naturality`: the
  same square, at an endomorphism of a module carrying an `IsQuasicoherent` instance and read on
  elements, which is the form a consumer working in the module-valued model can apply. The
  previous item cannot be applied there directly: both of its sides are written with the
  scalar-forgetting functor and with whiskered composites applied to a full-subcategory object,
  and reconciling that with `H^i(X, F)` in one piece exhausts the heartbeat budget.

## Implementation notes

Only the scalars are forgotten, not the comparison: the two sides are the module-valued
cohomology functors, and the isomorphism is between their composites with
`forget₂ (ModuleCat Γ(·, ⊤)) AddCommGrpCat`. That is enough for the use the proof of
[Stacks, Tag 0897] part (1) makes of it — there the graded `B`-module structure on
`⨁ₙ H^p(X, Fₙ)` is transported along an additive equivalence, so the comparison is only ever
needed as a map of abelian groups, natural in the module. What is *not* supplied here is a
comparison respecting the `Γ(S, ⊤)`-actions; `cohomologyIsoPushforward` is the one that does
that, and it is the one with no naturality.

An earlier reading of the obstruction placed it in the arguments of
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward`, on the grounds that it takes a
module together with its acyclicity. It does not: both acyclicity inputs of
`Stacks.Cohomology.AffineComparison.rightDerivedCollapseIso` are supplied inside it from the
instances `[IsAffineHom f]` and `[F.IsQuasicoherent]`. The obstruction is one level down —
`rightDerivedCollapseIso` is defined at one object and carries no naturality lemma, and neither
does `rightDerivedPlusCollapseIso` or `rightDerivedFunctorPlusObjSingleIso` beneath it — so
naturalising that construction means proving naturality of the collapse from scratch. Going
through `cohomologyPushforwardIso`, which is natural by construction, avoids that entirely.

The natural isomorphism whiskered here is
`Stacks.AffineCohomologyPushforward.cohomologyPushforwardIso`. The library has a *second*
isomorphism of exactly that type, `Stacks.AffineCohomologyResolution.cohomologyPushforwardIso`,
built from a comparison of injective resolutions and carrying the two normalizations the statement of
Tag 089W asks for — its value against any augmentation-preserving comparison of resolutions, and its
degree-zero component. No lemma identifies the two, so a consumer that needs a normalization as
well as naturality should whisker the resolution-built one instead; the construction below is
the same three lines either way.

Naturality is stated for a morphism of the quasi-coherent full subcategory rather than for a
morphism of `X.Modules` between two modules carrying `IsQuasicoherent` instances. The two
statements are definitionally the same, but writing `⟨F, inferInstance⟩` for the subcategory
object makes the elaborator reduce the whole whiskered composite while checking the stated type
against the one `CategoryTheory.NatTrans.naturality` produces, and that exhausts the heartbeat
budget; a consumer holding instances applies the lemma at `ObjectProperty.homMk`, where the
expected type is already known.

## References

* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.AffineBase (moduleGlobalSections)
open Stacks.Cohomology.ModuleComparison (rightDerivedEvaluationForgetIso)

universe u

namespace Stacks.AffineCohomologyPushforward

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]

/-- **The comparison of [Stacks, Tag 089W] in the module-valued model of cohomology, natural in
the module.** For `f` affine, deriving the `Γ(X, ⊤)`-valued global sections and forgetting the
scalars agrees, as a functor on the quasi-coherent `𝒪_X`-modules, with pushing forward and then
doing the same over `S`.

The two whiskered factors are
`Stacks.Cohomology.ModuleComparison.rightDerivedEvaluationForgetIso`, which identifies the
module-valued cohomology functor with the abelian-group-valued `Hfunctor` on the nose; the
middle factor is `cohomologyPushforwardIso`, Tag 089W as an isomorphism of functors. -/
def cohomologyPushforwardModuleIso (i : ℕ) :
    ObjectProperty.ι (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf)) ⋙
        (moduleGlobalSections X).rightDerived i ⋙
          forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf)) ⋙
        Scheme.Modules.pushforward f ⋙ (moduleGlobalSections S).rightDerived i ⋙
          forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat.{u} :=
  Functor.isoWhiskerLeft _ (rightDerivedEvaluationForgetIso X.ringCatSheaf ⊤ i) ≪≫
    cohomologyPushforwardIso f i ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft (Scheme.Modules.pushforward f)
      (rightDerivedEvaluationForgetIso S.ringCatSheaf ⊤ i).symm)

/-- **The comparison of [Stacks, Tag 089W] is natural in the module, in the module-valued model
of cohomology.** For a morphism `τ` of quasi-coherent `𝒪_X`-modules, the square built from the
maps `H^i(X, τ)` and `H^i(S, f_* τ)` and the comparison commutes.

This is the statement `Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward` does not
carry; here it is the naturality of `cohomologyPushforwardModuleIso`, which holds because that
is an isomorphism of functors. -/
theorem cohomologyPushforwardModuleIso_naturality (i : ℕ)
    {F G : (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf)).FullSubcategory} (τ : F ⟶ G) :
    (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).map
          (((moduleGlobalSections X).rightDerived i).map
            ((ObjectProperty.ι (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf))).map τ)) ≫
        (cohomologyPushforwardModuleIso f i).hom.app G =
      (cohomologyPushforwardModuleIso f i).hom.app F ≫
        (forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat.{u}).map
          (((moduleGlobalSections S).rightDerived i).map
            ((Scheme.Modules.pushforward f).map
              ((ObjectProperty.ι (SheafOfModules.isQuasicoherent
                (R := X.ringCatSheaf))).map τ))) :=
  (cohomologyPushforwardModuleIso f i).hom.naturality τ

/- The forgetful functor changes neither the underlying group nor the underlying map, and
`ObjectProperty.ι` of `ObjectProperty.homMk τ` is `τ`, so each of the next two statements is a
single definitional identity. They are stated separately, with their types written out, because
the elaborator will only check them one at a time: asked to reconcile the whole naturality
equation below in one piece it exhausts the heartbeat budget, the objects on the two sides being
a whiskered composite of four functors applied to `⟨F, inferInstance⟩` on one side and
`H^i(X, F)` on the other. -/
private theorem forget₂_map_cohomology_map_ι_homMk (i : ℕ) (F : X.Modules)
    [F.IsQuasicoherent] (τ : F ⟶ F)
    (y : ↥(((moduleGlobalSections X).rightDerived i).obj F)) :
    ((forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}).map
        (((moduleGlobalSections X).rightDerived i).map
          ((ObjectProperty.ι (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf))).map
            (ObjectProperty.homMk
              (X := (⟨F, inferInstance⟩ :
                (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf)).FullSubcategory))
              (Y := ⟨F, inferInstance⟩) τ)))).hom y =
      (((moduleGlobalSections X).rightDerived i).map τ).hom y := rfl

omit [IsAffineHom f] in
private theorem forget₂_map_cohomology_map_pushforward_map_ι_homMk (i : ℕ) (F : X.Modules)
    [F.IsQuasicoherent] (τ : F ⟶ F)
    (z : ↥(((moduleGlobalSections S).rightDerived i).obj
      ((Scheme.Modules.pushforward f).obj F))) :
    ((forget₂ (ModuleCat.{u} Γ(S, ⊤)) AddCommGrpCat.{u}).map
        (((moduleGlobalSections S).rightDerived i).map ((Scheme.Modules.pushforward f).map
          ((ObjectProperty.ι (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf))).map
            (ObjectProperty.homMk
              (X := (⟨F, inferInstance⟩ :
                (SheafOfModules.isQuasicoherent (R := X.ringCatSheaf)).FullSubcategory))
              (Y := ⟨F, inferInstance⟩) τ))))).hom z =
      (((moduleGlobalSections S).rightDerived i).map
        ((Scheme.Modules.pushforward f).map τ)).hom z := rfl

/-- **[Stacks, Tag 089W] is natural in the module, read on elements of the module-valued
cohomology.** For an endomorphism `τ` of a quasi-coherent `𝒪_X`-module `F`, the comparison
carries the class of `H^i(X, τ) y` to `H^i(S, f_* τ)` of the class of `y`.

This is `cohomologyPushforwardModuleIso_naturality` with the scalar-forgetting functor stripped
from both sides, which is what a consumer working in the module-valued model needs: there the
cohomology of `F` is an object of `ModuleCat Γ(X, ⊤)`, and its elements are not presented as
elements of `(forget₂ _ _).obj` of anything.

The last step is a term-mode `Eq.trans` with the function of the `congrArg` written out, rather
than a `rw` or a `simpa` with the two bridges above: both of those ask the elaborator to
reconcile the two readings of the statement in one piece, and time out. -/
theorem cohomologyPushforwardModuleIso_hom_app_naturality (i : ℕ) (F : X.Modules)
    [F.IsQuasicoherent] (τ : F ⟶ F)
    (y : ↥(((moduleGlobalSections X).rightDerived i).obj F)) :
    ((cohomologyPushforwardModuleIso f i).hom.app ⟨F, inferInstance⟩).hom
        ((((moduleGlobalSections X).rightDerived i).map τ).hom y) =
      (((moduleGlobalSections S).rightDerived i).map
          ((Scheme.Modules.pushforward f).map τ)).hom
        (((cohomologyPushforwardModuleIso f i).hom.app ⟨F, inferInstance⟩).hom y) := by
  have h' := congrArg (fun m => m.hom) (cohomologyPushforwardModuleIso_naturality f i
    (F := ⟨F, inferInstance⟩) (G := ⟨F, inferInstance⟩) (ObjectProperty.homMk τ))
  rw [AddCommGrpCat.hom_comp, AddCommGrpCat.hom_comp] at h'
  have h'' := DFunLike.congr_fun h' y
  simp only [AddMonoidHom.coe_comp, Function.comp_apply] at h''
  exact (congrArg (fun z => ((cohomologyPushforwardModuleIso f i).hom.app
        ⟨F, inferInstance⟩).hom z)
      (forget₂_map_cohomology_map_ι_homMk i F τ y)).symm.trans
    (h''.trans (forget₂_map_cohomology_map_pushforward_map_ι_homMk f i F τ _))

end Stacks.AffineCohomologyPushforward

end
