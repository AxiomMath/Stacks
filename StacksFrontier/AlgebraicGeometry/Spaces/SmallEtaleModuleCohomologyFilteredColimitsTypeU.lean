module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomologyFilteredColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleEquiUniverseModel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyOnALargeSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SectionsOnALocallySmallSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.SmallSiteAbelianInstances
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyFilteredColimits
public import StacksFrontier.CategoryTheory.Sites.LocallyBijectiveUniverse
import all StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomologyFilteredColimits

/-!
# Filtered colimits and the cohomology of `𝒪_F`-modules at the universe of the structure rings

On a quasi-compact and quasi-separated algebraic space `F` over a scheme `S`, the cohomology of
`𝒪_F`-modules commutes with filtered colimits **at module universe `u`**, the universe of the
schemes and of the structure rings — the universe in which the quasi-coherent modules of an
algebraic space live.

`AlgebraicGeometry.Space.isIso_colimit_post_smallEtaleModuleCohomology` of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCohomologyFilteredColimits` is the same
statement at module universe `u + 1`, and its implementation notes record that `u` is
unreachable. That is wrong, and the reason it is wrong is the subject of this file: the module
universe is pinned to `max (u + 1) w` only on the *small étale site itself*, whose objects lie in
`Type (u + 1)`, and the algebraic space has an equi-universe model of that site,
`AlgebraicGeometry.Space.smallEtaleModelRingedSite`, which is an
`AlgebraicGeometry.RingedSite.{u, u, u}`. On the model Stacks 03FD is available at coefficient
universe `u`, so the one thing missing is **Stacks 073E for abelian sheaves at `Ab.{u}` on the
model**, and that is obtained from the statement at `Ab.{u + 1}` by a universe lift of the
coefficients.

## Main results

* `Stacks.Cohomology.CoefficientLowering.gammaUliftIso`: **on a small site, global sections
  commute with the universe lift of abelian groups.**
* `Stacks.Cohomology.CoefficientLowering.isIso_colimit_post_rightDerived_globalSections_of_lift`:
  **the filtered-colimit comparison for cohomology descends from a larger coefficient universe
  to the universe of a small site.**
* `Stacks.Cohomology.CoefficientLowering.isIso_colimit_post_rightDerived_globalSections_ambient`:
  the comparison travels *up* the inclusion of a dense subsite, the direction
  `…_of_isDenseSubsite` does not go.
* `AlgebraicGeometry.Space.isIso_colimit_post_rightDerived_globalSections_smallEtaleModel`:
  **Stacks 073E on the equi-universe model, at abelian coefficient universe `u`.**
* `AlgebraicGeometry.Space.isIso_colimit_post_globalModuleCohomology_smallEtaleModel`:
  **Stacks 073E at module coefficients, at module universe `u`**, on the equi-universe model.
* `AlgebraicGeometry.Space.preservesColimit_globalModuleCohomology_smallEtaleModel`: the same as
  preservation of the colimit.

## Implementation notes

*The universe lift of the coefficients.* The claim that global sections do not commute with
`AddCommGrpCat.uliftFunctor` on a site without a terminal object — recorded in the implementation
notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyOnALargeSite` — is
false on a *small* site. `CategoryTheory.Sheaf.ΓNatIsoLim` identifies `CategoryTheory.Sheaf.Γ`
with the limit over `Cᵒᵖ` of the underlying presheaf whenever the coefficients have limits of
that shape, which on a small site they do in every universe above the site; and
`CategoryTheory.preservesLimitNatIso` moves a limit-preserving functor past `lim`. No terminal
object is involved. That is `gammaUliftIso`, and the transport
`isIso_colimit_post_rightDerived_globalSections_of_lift` built on it is the pattern of the
private `isIso_colimit_post_rightDerived_sheafSections_anySize` of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomologyFilteredColimits`, read at global
sections instead of at sections over an object.

*Why some helper lemmas are restated.* `uliftFunctor_preservesInjectiveObjects`,
`preservesColimitsOfShape_of_reflective`, `hasSheafify_ab_lift` and
`ulift_preservesSheafification` are the private lemmas of that same file. They are `private`
there and are reproduced here knowingly; if that file ever makes them public these copies should
be deleted in favour of it. `whiskeringRight_preservesInjectiveObjects`,
`sheafCompose_preservesInjectiveObjects`, `sheafCompose_preservesLimitsOfShape` and
`sheafCompose_preservesColimitsOfShape` are aliases of the public lemmas of that file.
`AlgebraicGeometry.Space.evaluationRightAdjointCompIso`, private to that file too, is not
restated: it is reached by `import all`.

*Why the model.* The abelian statement has to be lowered on a site whose objects and morphisms
share a universe: `whiskeringRight_preservesInjectiveObjects` embeds a presheaf into a product
indexed by the objects of the site, and on the small étale site those lie in `Type (u + 1)` while
the coefficients would be `Ab.{u}`, where that product does not exist. The model
`AlgebraicGeometry.Space.SmallEtaleModel` has objects and morphisms both in `Type u`, so the
obstruction is absent there. Everything below therefore happens on the model, and the
`Ab.{u + 1}` statement is carried onto it first, by
`isIso_colimit_post_rightDerived_globalSections_ambient`.

*The direction of the dense-subsite transport.* The model equivalence exhibits the small étale
site as a dense subsite of its model
(`AlgebraicGeometry.Space.smallEtaleModelEquivalence_inverse_isDenseSubsite`), so
`isIso_colimit_post_rightDerived_globalSections_of_isDenseSubsite`, in the namespace
`Stacks.Cohomology.ColimitsOfCohomology`, runs the wrong way: it concludes on the subsite from the
ambient site. The opposite direction is
`isIso_colimit_post_rightDerived_globalSections_ambient` below, the same instance of
`Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_rightDerived_of_equivalences` with the
equivalence of sheaf categories inverted.

*No `@[stacks]` attribute.* [Stacks, Tag 073E] is a statement about abelian sheaves, registered in
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleCohomologyFilteredColimits` on exactly that
statement; neither the model reading nor the module reading is an enumerated part of the tag.

## References

* [Stacks Project, Tag 073E](https://stacks.math.columbia.edu/tag/073E)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED)
* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.enoughInjectives_sheaf_ab
  Stacks.Cohomology.ColimitsOfCohomology.additive_globalSections_ab

namespace Stacks.Cohomology.CoefficientLowering

universe w u v' z v₁ u₁

/-! ### Injectives and global sections on an essentially small site -/

section EssentiallySmallSite

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) [EssentiallySmall.{z} C]
  [HasSheafify J Ab.{z}]

/-- Abelian sheaves with sections at a universe at which the site is essentially small have
enough injectives, being a Grothendieck abelian category.

Stated for an essentially small site rather than a small one because the small étale site of an
algebraic space has its objects one universe above its morphisms, and this is needed there at
the universe of the morphisms. -/
theorem enoughInjectives_sheaf_essentiallySmall : EnoughInjectives (Sheaf J Ab.{z}) :=
  (Sheaf.isGrothendieckAbelian_of_essentiallySmall.{z} J Ab.{z}).enoughInjectives

omit [EssentiallySmall.{z} C] in
/-- Global sections of those sheaves is an additive functor, being a right adjoint. -/
theorem additive_globalSections_essentiallySmall [HasGlobalSectionsFunctor J Ab.{z}] :
    (Sheaf.Γ J Ab.{z}).Additive := by
  have : HasLimitsOfShape (Discrete WalkingPair) (Cᵒᵖ ⥤ Ab.{z}) :=
    functorCategoryHasLimitsOfShape
  have : HasLimitsOfShape (Discrete WalkingPair) (Sheaf J Ab.{z}) :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape (sheafToPresheaf J Ab.{z})
  exact Functor.additive_of_preserves_binary_products _

end EssentiallySmallSite

/-! ### Postcomposition with an exact functor on sheaves -/

section SheafCompose

/-- Universe lifting of abelian groups preserves injective objects: an abelian group is
injective exactly when it is injective as a `ℤ`-module, and the universe lift of modules
preserves injective modules. -/
theorem uliftFunctor_preservesInjectiveObjects :
    AddCommGrpCat.uliftFunctor.{w, u}.PreservesInjectiveObjects where
  injective_obj {M} hM := by
    apply (AddCommGrpCat.injective_as_module_iff _).mp
    have := (AddCommGrpCat.injective_as_module_iff M).mpr hM
    exact (ModuleCat.uliftFunctor.{w, u} ℤ).injective_obj (ModuleCat.of ℤ M)

/-- Postcomposition with a limit-preserving functor which preserves injective objects preserves
injective functors. -/
alias whiskeringRight_preservesInjectiveObjects :=
  AlgebraicGeometry.Space.whiskeringRight_preservesInjectiveObjects

/-- Postcomposition on sheaves with a limit-preserving functor which preserves injective objects
preserves injective sheaves. -/
alias sheafCompose_preservesInjectiveObjects :=
  AlgebraicGeometry.Space.sheafCompose_preservesInjectiveObjects

/-- A functor out of a reflective subcategory preserves colimits of a given shape as soon as
its composite with the reflector does: every object is the reflection of its image. -/
theorem preservesColimitsOfShape_of_reflective
    {P S T I : Type*} [Category* P] [Category* S] [Category* T] [Category* I]
    {L : P ⥤ S} {R : S ⥤ P} (adj : L ⊣ R) [R.Full] [R.Faithful]
    [HasColimitsOfShape I P] (G : S ⥤ T) [PreservesColimitsOfShape I (L ⋙ G)] :
    PreservesColimitsOfShape I G where
  preservesColimit {F} := by
    have := adj.leftAdjoint_preservesColimits
    let e : (F ⋙ R) ⋙ L ≅ F := Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft F (asIso adj.counit) ≪≫ Functor.rightUnitor F
    have : PreservesColimit ((F ⋙ R) ⋙ L) G :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves L (colimit.isColimit (F ⋙ R)))
        (isColimitOfPreserves (L ⋙ G) (colimit.isColimit (F ⋙ R)))
    exact preservesColimit_of_iso_diagram G e

/-- Postcomposition on sheaves with a functor preserving sheafification preserves the colimits of
a shape that the functor preserves. -/
alias sheafCompose_preservesColimitsOfShape :=
  AlgebraicGeometry.Space.sheafCompose_preservesColimitsOfShape

/-- Postcomposition on sheaves preserves the limits its functor preserves. -/
alias sheafCompose_preservesLimitsOfShape :=
  AlgebraicGeometry.Space.sheafCompose_preservesLimitsOfShape

end SheafCompose

/-! ### Sheafification, injectives and global sections above the universe of a small site -/

section SmallSite

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- Presheaves of abelian groups whose sections lie above the universe of a small site admit a
left exact sheafification. -/
theorem hasSheafify_ab_lift : HasSheafify J Ab.{max u w} :=
  have _ : EssentiallySmall.{max u w} C := essentiallySmall_lift.{w, u} C
  hasSheafify_addCommGrpCat_of_essentiallySmall.{max u w, u, u} J

attribute [local instance] hasSheafify_ab_lift

/-- Universe lifting of abelian groups preserves sheafification on a small site: the
underlying-set functor preserves limits and filtered colimits in either universe. -/
theorem ulift_preservesSheafification :
    J.PreservesSheafification AddCommGrpCat.uliftFunctor.{w, u} := by
  have : PreservesLimitsOfSize.{u, u} (forget Ab.{max u w}) :=
    preservesLimitsOfSize_shrink (forget Ab.{max u w})
  have : PreservesFilteredColimitsOfSize.{u, u} (forget Ab.{max u w}) :=
    preservesFilteredColimitsOfSize_shrink (forget Ab.{max u w})
  have (X : C) : PreservesColimitsOfShape (J.Cover X)ᵒᵖ
      (forget Ab.{max u w}) :=
    PreservesFilteredColimitsOfSize.preserves_filtered_colimits _
  exact GrothendieckTopology.instPreservesSheafification J AddCommGrpCat.uliftFunctor.{w, u}

attribute [local instance] ulift_preservesSheafification

/-- Abelian sheaves on a small site with sections above its universe have enough injectives,
being a Grothendieck abelian category. -/
theorem enoughInjectives_sheaf_lift : EnoughInjectives (Sheaf J Ab.{max u w}) :=
  (Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max u w} J Ab.{max u w}).enoughInjectives

/-- Global sections of such sheaves is an additive functor, being a right adjoint. -/
theorem additive_globalSections_lift : (Sheaf.Γ J Ab.{max u w}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **On a small site, global sections commute with the universe lift of abelian groups.**

Both sides are read as the limit of the underlying presheaf over `Cᵒᵖ`
(`CategoryTheory.Sheaf.ΓNatIsoLim`, available because a small site has limits of shape `Cᵒᵖ` in
abelian groups at every universe above it), and `AddCommGrpCat.uliftFunctor` preserves limits of
every size, so it may be moved past `lim` by `CategoryTheory.preservesLimitNatIso`.

No terminal object of the site is involved; the statement holds on every small site. -/
def gammaUliftIso :
    sheafCompose J AddCommGrpCat.uliftFunctor.{w, u} ⋙ Sheaf.Γ J Ab.{max u w} ≅
      Sheaf.Γ J Ab.{u} ⋙ AddCommGrpCat.uliftFunctor.{w, u} := by
  have eW : sheafCompose J AddCommGrpCat.uliftFunctor.{w, u} ⋙
        sheafToPresheaf J Ab.{max u w} ≅
      sheafToPresheaf J Ab.{u} ⋙
        (Functor.whiskeringRight Cᵒᵖ Ab.{u} Ab.{max u w}).obj
          AddCommGrpCat.uliftFunctor.{w, u} := Iso.refl _
  have e1 : sheafCompose J AddCommGrpCat.uliftFunctor.{w, u} ⋙ Sheaf.Γ J Ab.{max u w} ≅
      sheafToPresheaf J Ab.{u} ⋙
        ((Functor.whiskeringRight Cᵒᵖ Ab.{u} Ab.{max u w}).obj
          AddCommGrpCat.uliftFunctor.{w, u} ⋙ lim) :=
    Functor.isoWhiskerLeft _ (Sheaf.ΓNatIsoLim J Ab.{max u w}) ≪≫
      (Functor.associator (sheafCompose J AddCommGrpCat.uliftFunctor.{w, u})
        (sheafToPresheaf J Ab.{max u w}) lim).symm ≪≫
      Functor.isoWhiskerRight eW lim ≪≫ Functor.associator _ _ _
  have e2 : sheafToPresheaf J Ab.{u} ⋙
        ((Functor.whiskeringRight Cᵒᵖ Ab.{u} Ab.{max u w}).obj
          AddCommGrpCat.uliftFunctor.{w, u} ⋙ lim) ≅
      Sheaf.Γ J Ab.{u} ⋙ AddCommGrpCat.uliftFunctor.{w, u} :=
    Functor.isoWhiskerLeft _ (preservesLimitNatIso AddCommGrpCat.uliftFunctor.{w, u}).symm ≪≫
      (Functor.associator (sheafToPresheaf J Ab.{u}) lim
        AddCommGrpCat.uliftFunctor.{w, u}).symm ≪≫
      Functor.isoWhiskerRight (Sheaf.ΓNatIsoLim J Ab.{u}).symm AddCommGrpCat.uliftFunctor.{w, u}
  exact e1 ≪≫ e2

/-- **The filtered-colimit comparison for cohomology descends from a larger coefficient universe
to the universe of a small site.** If `colim_λ H^p(C, G_λ) ⟶ H^p(C, colim_λ G_λ)` is an
isomorphism for the universe lift of a filtered diagram `F` of abelian sheaves with sections in
the universe of the site, then it is an isomorphism for `F` itself.

Postcomposition with `AddCommGrpCat.uliftFunctor` is an exact functor of sheaf categories which
preserves injective objects and the colimit, so it may be moved past both
`CategoryTheory.Limits.colimit.post` and `CategoryTheory.Functor.rightDerived`; and it commutes
with global sections by `gammaUliftIso`. The lift is fully faithful, hence reflects
isomorphisms, which is what turns the lifted statement back into the original one. -/
theorem isIso_colimit_post_rightDerived_globalSections_of_lift
    [EnoughInjectives (Sheaf J Ab.{max u w})] [(Sheaf.Γ J Ab.{max u w}).Additive]
    (p : ℕ) {I : Type v'} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I Ab.{u}] [HasColimitsOfShape I Ab.{max u w}]
    (F : I ⥤ Sheaf J Ab.{u})
    (h : IsIso (colimit.post (F ⋙ sheafCompose J AddCommGrpCat.uliftFunctor.{w, u})
      ((Sheaf.Γ J Ab.{max u w}).rightDerived p))) :
    IsIso (colimit.post F ((Sheaf.Γ J Ab.{u}).rightDerived p)) := by
  let G := AddCommGrpCat.uliftFunctor.{w, u}
  have : G.PreservesInjectiveObjects := uliftFunctor_preservesInjectiveObjects
  let L := sheafCompose J G
  have : L.Additive := ⟨rfl⟩
  have : L.PreservesInjectiveObjects := sheafCompose_preservesInjectiveObjects J G
  have : PreservesFiniteLimits L :=
    ⟨fun _ _ _ ↦ sheafCompose_preservesLimitsOfShape J G⟩
  have : PreservesFiniteColimits L :=
    ⟨fun _ _ _ ↦ sheafCompose_preservesColimitsOfShape J G⟩
  have : PreservesColimitsOfShape I L := sheafCompose_preservesColimitsOfShape J G
  let H := Sheaf.Γ J Ab.{u}
  let H' := Sheaf.Γ J Ab.{max u w}
  have : IsIso (colimit.post F (L ⋙ H'.rightDerived p)) := by
    rw [← colimit.post_post]
    infer_instance
  let a : L ⋙ H'.rightDerived p ≅ H.rightDerived p ⋙ G :=
    (Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso L H' p).symm ≪≫
      Stacks.Cohomology.CompositeRightDerived.rightDerivedNatIso (gammaUliftIso.{w} J) p ≪≫
        Stacks.Cohomology.ColimitsOfCohomology.rightDerivedCompExactIso H G p
  have : IsIso (colimit.post F (H.rightDerived p ⋙ G)) :=
    Stacks.Cohomology.isIso_colimit_post_of_natIso F _ _ a
  have : IsIso (G.map (colimit.post F (H.rightDerived p))) := by
    have : IsIso (colimit.post (F ⋙ H.rightDerived p) G ≫
        G.map (colimit.post F (H.rightDerived p))) := by
      rw [colimit.post_post]
      infer_instance
    exact IsIso.of_isIso_comp_left (colimit.post (F ⋙ H.rightDerived p) G) _
  exact isIso_of_reflects_iso (colimit.post F (H.rightDerived p)) G

end SmallSite

/-! ### The comparison travels up the inclusion of a dense subsite -/

/-- **The colimit comparison for cohomology travels up the inclusion `v` of a dense subsite**:
if it is an isomorphism on the subsite `(C, J)` for the restriction of a diagram, then it is an
isomorphism on the ambient site `(D, K)` for the diagram itself.

This is `isIso_colimit_post_rightDerived_globalSections_of_isDenseSubsite`, in the namespace
`Stacks.Cohomology.ColimitsOfCohomology`, with the equivalence of sheaf categories inverted: that
statement concludes on the subsite from the ambient site. -/
theorem isIso_colimit_post_rightDerived_globalSections_ambient
    {C D : Type*} [Category* C] [Category* D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) (v : C ⥤ D)
    (A : Type*) [Category* A] [Abelian A] [v.IsDenseSubsite J K]
    [∀ X, HasLimitsOfShape (StructuredArrow X v.op) A]
    [HasSheafify J A] [HasSheafify K A]
    [HasGlobalSectionsFunctor J A] [HasGlobalSectionsFunctor K A]
    [HasInjectiveResolutions (Sheaf J A)] [HasInjectiveResolutions (Sheaf K A)]
    [(Sheaf.Γ J A).Additive] [(Sheaf.Γ K A).Additive]
    {I : Type*} [Category* I] [HasColimitsOfShape I A]
    [HasColimitsOfShape I (Sheaf J A)] [HasColimitsOfShape I (Sheaf K A)]
    (p : ℕ) (F : I ⥤ Sheaf K A)
    (hF : IsIso (colimit.post (F ⋙ v.sheafPushforwardContinuous A J K)
      ((Sheaf.Γ J A).rightDerived p))) :
    IsIso (colimit.post F ((Sheaf.Γ K A).rightDerived p)) := by
  let R := v.sheafPushforwardContinuous A J K
  let e := R.asEquivalence
  let α : e.symm.functor ⋙ Sheaf.Γ K A ≅
      Sheaf.Γ J A ⋙ (CategoryTheory.Equivalence.refl (C := A)).functor :=
    Functor.isoWhiskerLeft e.inverse
        (Stacks.Cohomology.ColimitsOfCohomology.denseSubsite_globalSectionsIso J K v A).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight e.counitIso (Sheaf.Γ J A) ≪≫
      Functor.leftUnitor _ ≪≫ (Functor.rightUnitor _).symm
  exact Stacks.Cohomology.ColimitsOfCohomology.isIso_colimit_post_rightDerived_of_equivalences
    e.symm CategoryTheory.Equivalence.refl (Sheaf.Γ J A) (Sheaf.Γ K A) α p F hF

end Stacks.Cohomology.CoefficientLowering

open Stacks.Cohomology.CoefficientLowering
open Stacks.Cohomology.ColimitsOfCohomology
  (isIso_colimit_post_rightDerived_globalSections_of_isDenseSubsite)

attribute [local instance] enoughInjectives_sheaf_essentiallySmall
  additive_globalSections_essentiallySmall

namespace AlgebraicGeometry.Space

universe w u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-! ### Stacks 073E on the equi-universe model, at abelian coefficient universe `u` -/

set_option synthInstance.maxHeartbeats 200000 in
/-- **Stacks 073E on the equi-universe model of the small étale site, at abelian coefficient
universe `u`.** On a quasi-compact and quasi-separated algebraic space, the canonical map from a
filtered colimit of cohomology groups of abelian sheaves *with sections in the universe of the
schemes* to the cohomology of the filtered colimit is an isomorphism, on the model
`AlgebraicGeometry.Space.SmallEtaleModel` of the small étale site.

The library's form of Stacks 073E,
`AlgebraicGeometry.Space.isIso_colimit_post_rightDerived_globalSections`, is at coefficient
universe `u + 1`, the universe of the objects of the small étale site. It is carried onto the
model by
`Stacks.Cohomology.CoefficientLowering.isIso_colimit_post_rightDerived_globalSections_ambient`
and then lowered to `Ab.{u}` by
`Stacks.Cohomology.CoefficientLowering.isIso_colimit_post_rightDerived_globalSections_of_lift`,
which is available because the model is a small site. -/
theorem isIso_colimit_post_rightDerived_globalSections_smallEtaleModel
    (hX : IsAlgebraicSpace B S hS F)
    (hqc : IsQuasiCompactSpace B S hS F)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (p : ℕ) {I : Type w} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I Ab.{u}] [HasColimitsOfShape I Ab.{u + 1}]
    (G : I ⥤ Sheaf (smallEtaleModelTopology B S hS F) Ab.{u}) :
    IsIso (colimit.post G
      ((Sheaf.Γ (smallEtaleModelTopology B S hS F) Ab.{u}).rightDerived p)) := by
  have : HasSheafify (smallEtaleModelTopology B S hS F) Ab.{u + 1} :=
    Stacks.Cohomology.CoefficientLowering.hasSheafify_ab_lift.{u + 1} _
  have : EnoughInjectives (Sheaf (smallEtaleModelTopology B S hS F) Ab.{u + 1}) :=
    enoughInjectives_sheaf_lift.{u + 1} _
  have : (Sheaf.Γ (smallEtaleModelTopology B S hS F) Ab.{u + 1}).Additive :=
    additive_globalSections_lift.{u + 1} _
  have : (smallEtaleModelTopology B S hS F).PreservesSheafification
      AddCommGrpCat.uliftFunctor.{u + 1, u} :=
    Stacks.Cohomology.CoefficientLowering.ulift_preservesSheafification.{u + 1} _
  refine isIso_colimit_post_rightDerived_globalSections_of_lift.{u + 1} _ p G ?_
  refine isIso_colimit_post_rightDerived_globalSections_ambient
    (SmallEtale.topology B S hS F) (smallEtaleModelTopology B S hS F)
    (smallEtaleModelEquivalence B S hS F).inverse Ab.{u + 1} p _ ?_
  exact isIso_colimit_post_rightDerived_globalSections B S hS hZ F hX hqc hqs p _

/-- **Stacks 073E at abelian coefficient universe `u`**, on the small étale site itself: on a
quasi-compact and quasi-separated algebraic space, the canonical map from a filtered colimit of
cohomology groups of abelian sheaves with sections in the universe of the schemes to the
cohomology of the filtered colimit is an isomorphism.

The statement `AlgebraicGeometry.Space.isIso_colimit_post_rightDerived_globalSections`, which is
Stacks 073E itself, is at coefficient universe `u + 1`, the universe of the *objects* of the
site; this is the same statement at the universe of its *morphisms*, obtained from
`AlgebraicGeometry.Space.isIso_colimit_post_rightDerived_globalSections_smallEtaleModel` by
coming back down the dense-subsite inclusion of the small étale site into its model. The one
instance that is not found at `Ab.{u}` is the existence of the right Kan extensions along the
inclusion; the comma categories indexing them are essentially small at `u`, because the small
étale site is (Stacks 03ED), so those limits exist in `Ab.{u}` after all. -/
theorem isIso_colimit_post_rightDerived_globalSections_typeU
    (hX : IsAlgebraicSpace B S hS F)
    (hqc : IsQuasiCompactSpace B S hS F)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (p : ℕ) {I : Type w} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I Ab.{u}] [HasColimitsOfShape I Ab.{u + 1}]
    (G : I ⥤ Sheaf (SmallEtale.topology B S hS F) Ab.{u}) :
    IsIso (colimit.post G
      ((Sheaf.Γ (SmallEtale.topology B S hS F) Ab.{u}).rightDerived p)) := by
  have (X : (SmallEtaleModel B S hS F)ᵒᵖ) :
      HasLimitsOfShape
        (StructuredArrow X (smallEtaleModelEquivalence B S hS F).inverse.op) Ab.{u} :=
    hasLimitsOfShape_of_essentiallySmall.{u} _ _
  exact isIso_colimit_post_rightDerived_globalSections_of_isDenseSubsite
    (SmallEtale.topology B S hS F) (smallEtaleModelTopology B S hS F)
    (smallEtaleModelEquivalence B S hS F).inverse Ab.{u} p G
    (isIso_colimit_post_rightDerived_globalSections_smallEtaleModel
      B S hS hZ F hX hqc hqs p _)

/-! ### Stacks 073E at module coefficients, at module universe `u` -/

variable (hF : IsAlgebraicSpace B S hS F)

/-- **Stacks 073E at module coefficients, at module universe `u`**, on the equi-universe model
of the small étale ringed site: for a filtered diagram `D` of sheaves of modules on the model,
with sections in the universe `u` of the structure rings, the comparison
`colim_i H^p(D_i) ⟶ H^p(colim_i D_i)` is an isomorphism.

The abelian input is
`AlgebraicGeometry.Space.isIso_colimit_post_rightDerived_globalSections_smallEtaleModel`, and the
crossing is Stacks 03FD in the form
`ModuleSheafCohomology.isIso_colimit_post_globalModuleCohomology`. Its coefficient universe is
the join `max u v r w` of the two universes of the site, the universe of the structure rings and
the module universe, which on the model is `u`: that is the whole gain of passing to the model,
where the statement on the small étale site itself is stuck at `u + 1`. -/
theorem isIso_colimit_post_globalModuleCohomology_smallEtaleModel
    (hqc : IsQuasiCompactSpace B S hS F)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (p : ℕ) {I : Type w} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I Ab.{u}] [HasColimitsOfShape I Ab.{u + 1}]
    (D : I ⥤ SheafOfModules.{u} (ringSheaf (smallEtaleModelRingedSite B S hS F hF).O)) :
    have := site_hasSheafify_addCommGrp.{u, u, u}
      (J := (smallEtaleModelRingedSite B S hS F hF).J)
    have := site_wEqualsLocallyBijective_addCommGrp.{u, u, u}
      (J := (smallEtaleModelRingedSite B S hS F hF).J)
    IsIso (colimit.post D (globalModuleCohomology.{u, u, u, u}
      (ringSheaf (smallEtaleModelRingedSite B S hS F hF).O) p)) :=
  ModuleSheafCohomology.isIso_colimit_post_globalModuleCohomology.{w, w, u, u, u, u}
    (smallEtaleModelRingedSite B S hS F hF).J
    (ringSheaf (smallEtaleModelRingedSite B S hS F hF).O) p D
    (isIso_colimit_post_rightDerived_globalSections_smallEtaleModel.{w, u}
      B S hS hZ F hF hqc hqs p _)

/-- **Stacks 073E at module coefficients, at module universe `u`**, as preservation of the
colimit. This is the form a consumer that needs the colimit cocone uses; the content is
`AlgebraicGeometry.Space.isIso_colimit_post_globalModuleCohomology_smallEtaleModel`. -/
theorem preservesColimit_globalModuleCohomology_smallEtaleModel
    (hqc : IsQuasiCompactSpace B S hS F)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (p : ℕ) {I : Type w} [SmallCategory I] [IsFiltered I]
    [HasColimitsOfShape I Ab.{u}] [HasColimitsOfShape I Ab.{u + 1}]
    (D : I ⥤ SheafOfModules.{u} (ringSheaf (smallEtaleModelRingedSite B S hS F hF).O)) :
    have := site_hasSheafify_addCommGrp.{u, u, u}
      (J := (smallEtaleModelRingedSite B S hS F hF).J)
    have := site_wEqualsLocallyBijective_addCommGrp.{u, u, u}
      (J := (smallEtaleModelRingedSite B S hS F hF).J)
    PreservesColimit D (globalModuleCohomology.{u, u, u, u}
      (ringSheaf (smallEtaleModelRingedSite B S hS F hF).O) p) :=
  ModuleSheafCohomology.preservesColimit_globalModuleCohomology.{w, w, u, u, u, u}
    (smallEtaleModelRingedSite B S hS F hF).J
    (ringSheaf (smallEtaleModelRingedSite B S hS F hF).O) p D
    (isIso_colimit_post_rightDerived_globalSections_smallEtaleModel.{w, u}
      B S hS hZ F hF hqc hqs p _)

end AlgebraicGeometry.Space

end
