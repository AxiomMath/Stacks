module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.DenseSubsiteDescent
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.DerivedPushforwardTwoIso
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.DerivedPushforwardToposComparison
public import StacksFrontier.CategoryTheory.Sites.Topos.RingedToposReplacement
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalencePullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositionWithEquivalence
import StacksCore.Tactic.StacksAttribute

/-!
# Derived direct image preserves derived completeness, for morphisms of ringed topoi

Let `f : (Sh(𝒞), 𝒪_X) ⟶ (Sh(𝒟), 𝒪_Y)` be a morphism of ringed topoi and let `ℐ' ⊂ 𝒪_X`,
`ℐ ⊂ 𝒪_Y` be sheaves of ideals such that `f^♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` carries `f⁻¹ℐ` into `ℐ'`.
[Stacks, Tag 099J] asserts that `Rf_*` carries `D_comp(𝒪_X, ℐ')` into `D_comp(𝒪_Y, ℐ)`. This file
proves it, for an arbitrary `AlgebraicGeometry.RingedToposHom` — an arbitrary morphism of the
underlying topoi together with `f^♯` — with `Rf_*` the unbounded derived direct image
`Stacks.Cohomology.DerivedPushforward.derivedPushforward`.

The proof is the source's: reduce to a morphism of ringed sites by [Stacks, Tag 03CR]. That tag,
as `AlgebraicGeometry.RingedToposHom.exists_twoSided_isDenseSubsite_morphismOfSites`, gives a
2-commutative square `h ∘ g ≅ e ∘ f` in which `g : X ⟶ X'` and `e : Y ⟶ Y'` are the equivalences
induced by dense subsites `v : 𝒞 ⥤ 𝒞'`, `w : 𝒟 ⥤ 𝒟'`, with structure sheaves the direct images
and identity structure maps, and `h` comes from a morphism of sites `u : 𝒟' ⥤ 𝒞'`. Then:

* the inverse of `g` is the restriction to the dense subsite, a morphism of ringed sites
  (`denseRestrictSite`), and `D(g_*)` is inverse to its derived direct image
  (`derivedPushforwardDenseRestrictMapIso`), and likewise for `e`;
* the derived direct images of the two composites of the square split, `R(e ∘ f)_* ≅ Rf_* ⋙ D(e_*)`
  and `R(h ∘ g)_* ≅ D(g_*) ⋙ Rh_*`, by
  `Stacks.Cohomology.DerivedPushforward.derivedPushforwardCompEquivIso` and
  `Stacks.Cohomology.DerivedPushforward.derivedPushforwardEquivCompIso`, and are isomorphic by the
  2-isomorphism of the square;
* so `Rf_*K` is the derived direct image along the restriction `Y' ⟶ Y` of `Rh_*(D(g_*)K)`, and
  the Milnor condition at a section `s` of `ℐ` is carried along three morphisms of ringed sites:
  up from `Y` to `Y'` and from `Y'` to `X'` by the ringed-sites case
  (`AlgebraicGeometry.RingedSite.isDerivedCompleteAtSection_derivedPushforward`), and down from
  `X'` to `X` by its converse along a dense subsite
  (`AlgebraicGeometry.RingedSite.isDerivedCompleteAtSection_of_derivedPushforward_iso`);
* the sections met on the way lie in `ℐ'`: that is the hypothesis on `f^♯` carried across the
  square (`pushforward_comp_forgetFSharp`, `mem_of_square`).

## Main results

* `AlgebraicGeometry.RingedToposHom.derivedPushforward_isDerivedComplete`: **Tag 099J**.

## Implementation notes

*The hypothesis on the ideals* is stated literally: the composite of the inverse image of the
inclusion `ℐ ↪ 𝒪_Y` with the inverse-image form `f^♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map
(`AlgebraicGeometry.RingedToposHom.fSharpInverseImage`) factors through `ℐ' ↪ 𝒪_X`, as a map of
sheaves of sets. Since `f⁻¹` is left exact, `f⁻¹ℐ` is a subsheaf of `f⁻¹𝒪_Y`, so this is the
condition that `f^♯` carry `f⁻¹ℐ` into `ℐ'`.

*Universes.* The two ringed topoi are `RingedTopos.{u, u, u}`: sites that are small categories,
with sheaves of sets and of rings in the universe of the site. This is the universe of a site in
the source, and the one at which [Stacks, Tag 03CR] is available.

## References

* [Stacks Project, Tag 099J](https://stacks.math.columbia.edu/tag/099J)
* [Stacks Project, Tag 03CR](https://stacks.math.columbia.edu/tag/03CR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.RingedToposHom

attribute [local instance] HasDerivedCategory.standard

/-! The direct image of sheaves of modules is additive (`pushforwardModules_additive`), but
instance search does not find that instance for the replacement ringed topoi below: they are
`abbrev`s for structure literals, whose fields reduce away under the reducible transparency of the
discrimination tree. The four instances below key on the literal forms. -/

/-- Additivity of the direct image, between two ringed topoi. -/
local instance additive_pushforwardModules {A B : RingedTopos.{u, u, u}}
    (k : RingedToposHom.{u, u, u, u, u, u} A B) :
    (pushforwardModules.{u, u, u, u, u, u} k).Additive :=
  pushforwardModules_additive.{u, u, u, u, u, u} k

/-- Additivity of the direct image, into a ringed topos given as a structure literal. -/
local instance additive_pushforwardModules_lit₂ {A : RingedTopos.{u, u, u}} {C₂ : Type u}
    [SmallCategory C₂] {J₂ : GrothendieckTopology C₂} {O₂ : Sheaf J₂ CommRingCat.{u}}
    (k : RingedToposHom.{u, u, u, u, u, u} A ⟨C₂, J₂, O₂⟩) :
    (pushforwardModules.{u, u, u, u, u, u} k).Additive :=
  pushforwardModules_additive.{u, u, u, u, u, u} k

/-- Additivity of the direct image, out of a ringed topos given as a structure literal. -/
local instance additive_pushforwardModules_lit₁ {B : RingedTopos.{u, u, u}} {C₁ : Type u}
    [SmallCategory C₁] {J₁ : GrothendieckTopology C₁} {O₁ : Sheaf J₁ CommRingCat.{u}}
    (k : RingedToposHom.{u, u, u, u, u, u} ⟨C₁, J₁, O₁⟩ B) :
    (pushforwardModules.{u, u, u, u, u, u} k).Additive :=
  pushforwardModules_additive.{u, u, u, u, u, u} k

/-- Additivity of the direct image, between two ringed topoi given as structure literals. -/
local instance additive_pushforwardModules_lit {C₁ : Type u} [SmallCategory C₁]
    {J₁ : GrothendieckTopology C₁} {O₁ : Sheaf J₁ CommRingCat.{u}} {C₂ : Type u}
    [SmallCategory C₂] {J₂ : GrothendieckTopology C₂} {O₂ : Sheaf J₂ CommRingCat.{u}}
    (k : RingedToposHom.{u, u, u, u, u, u} ⟨C₁, J₁, O₁⟩ ⟨C₂, J₂, O₂⟩) :
    (pushforwardModules.{u, u, u, u, u, u} k).Additive :=
  pushforwardModules_additive.{u, u, u, u, u, u} k

section DenseReplacement

variable (X : RingedTopos.{u, u, u}) {C' : Type u} [SmallCategory C']
  (J' : GrothendieckTopology C') (v : X.C ⥤ C') [v.IsDenseSubsite X.J J']

/-- The ringed topos on a site containing `X.C` as a dense subsite, with structure sheaf the
direct image of that of `X`. -/
abbrev denseReplacement : RingedTopos.{u, u, u} where
  C := C'
  J := J'
  O := (Functor.IsDenseSubsite.morphismOfTopoi X.J J' v).pushforwardRing.obj X.O

/-- The equivalence of ringed topoi `X ⟶ denseReplacement X J' v`, with identity structure map. -/
abbrev denseReplacementHom : RingedToposHom X (denseReplacement X J' v) where
  toToposHom := Functor.IsDenseSubsite.morphismOfTopoi X.J J' v
  fSharp := 𝟙 _

/-- The direct image of sheaves of sets along the replacement equivalence is an equivalence. -/
instance : (denseReplacementHom X J' v).toToposHom.pushforward.IsEquivalence :=
  Functor.IsDenseSubsite.morphismOfTopoi_pushforward_isEquivalence X.J J' v

/-- The structure map of the replacement equivalence is an isomorphism. -/
instance : IsIso (denseReplacementHom X J' v).fSharp :=
  inferInstanceAs (IsIso (𝟙 _))

/-- The inverse of the replacement equivalence. -/
abbrev denseReplacementInv : RingedToposHom (denseReplacement X J' v) X :=
  inverse.{u, u, u, u, u, u} (denseReplacementHom X J' v)

/-- The structure map of the inverse of the replacement equivalence is an isomorphism. -/
instance : IsIso (denseReplacementInv X J' v).fSharp := by
  show IsIso (inv (denseReplacementHom X J' v).fSharpInverseImage)
  infer_instance

/-- The structure map of the restriction morphism, `𝒪_X ⟶ v_*𝒪_{X'}`. -/
def denseRestrictSharp :
    X.O ⟶ (v.sheafPushforwardContinuous CommRingCat.{u} X.J J').obj
      (denseReplacement X J' v).O :=
  (denseReplacementInv X J' v).fSharp ≫
    (restrictionCommRingIso X.J J' v (denseReplacement X J' v).O).hom

/-- The structure map of the restriction morphism is an isomorphism. -/
instance : IsIso (denseRestrictSharp X J' v) :=
  IsIso.comp_isIso' (inferInstance : IsIso (denseReplacementInv X J' v).fSharp)
    (Iso.isIso_hom (restrictionCommRingIso X.J J' v (denseReplacement X J' v).O))

/-- Restriction to the dense subsite, as a morphism of ringed sites. -/
abbrev denseRestrictSite : RingedSite.Hom (denseReplacement X J' v).toRingedSite X.toRingedSite :=
  RingedSite.denseRestrictHom X.toRingedSite (denseReplacement X J' v).toRingedSite v
    (denseRestrictSharp X J' v)

/-- On underlying sheaves of sets, the structure map of the restriction morphism is that of the
inverse of the replacement equivalence. -/
theorem forget_map_denseRestrictSharp :
    (sheafCompose X.J (forget CommRingCat.{u})).map (denseRestrictSharp X J' v) =
      (sheafCompose X.J (forget CommRingCat.{u})).map (denseReplacementInv X J' v).fSharp :=
  (Functor.map_comp _ _ _).trans (Category.comp_id _)

/-- The inverse of the replacement equivalence is the restriction to the dense subsite. -/
def inverseTwoIsoDenseRestrict :
    TwoIso.{u, u, u, u, u, u} (A := denseReplacement X J' v) (B := X)
      (denseReplacementInv X J' v) (denseRestrictSite X J' v).ringedToposHom where
  e := Iso.refl (v.sheafPushforwardContinuous (Type u) X.J J')
  commutes := (Category.comp_id _).trans
    ((forget_map_denseRestrictSharp X J' v).symm.trans
      (RingedSite.Hom.forgetFSharp_ringedToposHom (denseRestrictSite X J' v)).symm)

/-- The structure map of the restriction morphism, as a map of sheaves of rings, is an
isomorphism. -/
instance : IsIso (denseRestrictSite X J' v).toRingedToposSiteHom.fSharpRing := by
  show IsIso ((sheafCompose X.J (forget₂ CommRingCat.{u} RingCat.{u})).map
    (denseRestrictSharp X J' v))
  infer_instance

/-- The direct image of sheaves of modules along the inverse of the replacement equivalence is the
direct image along the dense-subsite restriction. -/
def pushforwardModulesDenseReplacementInvIso :
    pushforwardModules.{u, u, u, u, u, u} (denseReplacementInv X J' v) ≅
      (denseRestrictSite X J' v).toRingedToposSiteHom.pushforwardTopos :=
  (inverseTwoIsoDenseRestrict X J' v).pushforwardModulesIso ≪≫
    (denseRestrictSite X J' v).pushforwardToposIso

/-- The direct image of sheaves of modules along the inverse of the replacement equivalence is an
equivalence. -/
instance : (pushforwardModules.{u, u, u, u, u, u} (denseReplacementInv X J' v)).IsEquivalence :=
  have := RingedSite.isEquivalence_pushforwardTopos X.toRingedSite
    (denseReplacement X J' v).toRingedSite v (denseRestrictSharp X J' v)
  Functor.isEquivalence_of_iso (pushforwardModulesDenseReplacementInvIso X J' v).symm

/-- The direct image of sheaves of modules along the round trip `X' ⟶ X ⟶ X'` is the identity. -/
def pushforwardModulesRoundTripIso :
    𝟭 _ ≅ pushforwardModules.{u, u, u, u, u, u}
      (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} (denseReplacementHom X J' v)
        (denseReplacementInv X J' v)) :=
  pushforwardModulesIsoId.{u, u, u} _
    (inverseImageCompPushforwardIsoId.{u, u, u, u, u, u} (denseReplacementHom X J' v))
    (forgetRing_map_comp_inverse_fSharp.{u, u, u, u, u, u} (denseReplacementHom X J' v))

/-- The direct image of sheaves of modules along the replacement equivalence is an equivalence. -/
instance : (pushforwardModules.{u, u, u, u, u, u} (denseReplacementHom X J' v)).IsEquivalence := by
  let E := (pushforwardModules.{u, u, u, u, u, u} (denseReplacementInv X J' v)).asEquivalence
  let i : E.functor ⋙ pushforwardModules.{u, u, u, u, u, u} (denseReplacementHom X J' v) ≅ 𝟭 _ :=
    (pushforwardModulesCompIso.{u, u, u, u, u, u, u, u, u} _ _).symm ≪≫
      (pushforwardModulesRoundTripIso X J' v).symm
  let j : pushforwardModules.{u, u, u, u, u, u} (denseReplacementHom X J' v) ≅ E.inverse :=
    (Functor.leftUnitor _).symm ≪≫ Functor.isoWhiskerRight E.counitIso.symm _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft E.inverse i ≪≫ Functor.rightUnitor _
  exact Functor.isEquivalence_of_iso j.symm

/-- The derived direct image along the round trip `X' ⟶ X ⟶ X'` is the identity. -/
def derivedPushforwardRoundTripIso :
    Stacks.Cohomology.DerivedPushforward.derivedPushforward.{u, u, u, u, u, u}
      (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} (denseReplacementHom X J' v)
        (denseReplacementInv X J' v)) ≅ 𝟭 _ :=
  Stacks.Cohomology.DerivedPushforward.derivedPushforwardIsoIdOfSelf _
    (inverseImageCompPushforwardIsoId.{u, u, u, u, u, u} (denseReplacementHom X J' v))
    (forgetRing_map_comp_inverse_fSharp.{u, u, u, u, u, u} (denseReplacementHom X J' v))

/-- The derived direct image along the inverse of the replacement equivalence is the derived
direct image along the dense-subsite restriction, in its site-presented form. -/
def derivedPushforwardDenseReplacementInvIso :
    Stacks.Cohomology.DerivedPushforward.derivedPushforward.{u, u, u, u, u, u}
        (denseReplacementInv X J' v) ≅
      Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward.{u}
        (denseRestrictSite X J' v).toRingedToposSiteHom :=
  (inverseTwoIsoDenseRestrict X J' v).derivedPushforwardIso ≪≫
    (denseRestrictSite X J' v).derivedPushforwardToposIso

/-- **Restricting back a complex pushed to the replacement returns it.** The derived direct
image along the round trip `X' ⟶ X ⟶ X'` is the identity and factors as `R(g⁻¹)_*` followed by
`D(g_*)`; since `D(g_*)` is an equivalence, the other composite is the identity too. -/
def derivedPushforwardDenseRestrictMapIso
    (K : DerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O))) :
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward.{u}
        (denseRestrictSite X J' v).toRingedToposSiteHom).obj
      ((pushforwardModules.{u, u, u, u, u, u} (denseReplacementHom X J' v)).mapDerivedCategory.obj
        K) ≅ K := by
  let G := (pushforwardModules.{u, u, u, u, u, u} (denseReplacementHom X J' v)).mapDerivedCategory
  have : G.IsEquivalence := Stacks.DerivedFunctor.isEquivalence_mapDerivedCategory
    (pushforwardModules.{u, u, u, u, u, u} (denseReplacementHom X J' v))
  let F := Stacks.Cohomology.DerivedPushforward.derivedPushforward.{u, u, u, u, u, u}
    (denseReplacementInv X J' v)
  let i : F ⋙ G ≅ 𝟭 _ :=
    (Stacks.Cohomology.DerivedPushforward.derivedPushforwardCompEquivIso
      (denseReplacementInv X J' v) (denseReplacementHom X J' v)).symm ≪≫
      derivedPushforwardRoundTripIso X J' v
  exact (derivedPushforwardDenseReplacementInvIso X J' v).symm.app (G.obj K) ≪≫
    G.preimageIso (i.app (G.obj K))

end DenseReplacement

section Chase

/-- On underlying sheaves of sets, the structure map of the dense-subsite restriction is a section
of the counit of the replacement equivalence. -/
theorem forget_denseRestrictSharp_comp_counit (X : RingedTopos.{u, u, u}) {C' : Type u}
    [SmallCategory C'] (J' : GrothendieckTopology C') (v : X.C ⥤ C') [v.IsDenseSubsite X.J J'] :
    (sheafCompose X.J (forget CommRingCat.{u})).map (denseRestrictSharp X J' v) ≫
      (denseReplacementHom X J' v).toToposHom.adj.counit.app (X.forgetRing.obj X.O) = 𝟙 _ := by
  have h1 : X.forgetRing.map (denseReplacementHom X J' v).fSharpInverseImage =
      (denseReplacementHom X J' v).toToposHom.adj.counit.app (X.forgetRing.obj X.O) := by
    refine (fSharpInverseImage_forget.{u, u, u, u, u, u} _).trans ?_
    exact (congrArg (fun k => k ≫ _)
      (((congrArg _ (CategoryTheory.Functor.map_id _ _)).trans
        (CategoryTheory.Functor.map_id _ _)))).trans (Category.id_comp _)
  calc (sheafCompose X.J (forget CommRingCat.{u})).map (denseRestrictSharp X J' v) ≫
        (denseReplacementHom X J' v).toToposHom.adj.counit.app (X.forgetRing.obj X.O)
      = X.forgetRing.map (inv (denseReplacementHom X J' v).fSharpInverseImage) ≫
          X.forgetRing.map (denseReplacementHom X J' v).fSharpInverseImage := by
        rw [forget_map_denseRestrictSharp, h1]; rfl
    _ = 𝟙 _ := by
        rw [← CategoryTheory.Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- Membership in a sheaf of ideals is lying in the image of its inclusion, on sections. -/
theorem mem_submodule_iff_exists {Z : RingedSite.{u, u, u}}
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))) (U : Z.C)
    (s : (Stacks.SheafOfModules.Tensor.ringSheaf Z.O).obj.obj (op U)) :
    s ∈ I.toSubmodule.obj (op U) ↔
      ∃ y, ((Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)).map I.ι).hom.app
        (op U) y = s :=
  ⟨fun h => ⟨⟨s, h⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩

/-- Equal morphisms of sheaves of sets agree on sections. -/
private theorem hom_app_apply_congr {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {A B : Sheaf J (Type u)} {f g : A ⟶ B} (h : f = g) (U : Cᵒᵖ) (x : A.obj.obj U) :
    f.hom.app U x = g.hom.app U x :=
  h ▸ rfl

section Square

variable {X Y : RingedTopos.{u, u, u}} (f : RingedToposHom.{u, u, u, u, u, u} X Y)
  {C' : Type u} [SmallCategory C'] (J' : GrothendieckTopology C') (v : X.C ⥤ C')
  [v.IsDenseSubsite X.J J']
  {D' : Type u} [SmallCategory D'] (K' : GrothendieckTopology D') (w : Y.C ⥤ D')
  [w.IsDenseSubsite Y.J K']
  (hs : RingedSite.Hom (denseReplacement X J' v).toRingedSite
    (denseReplacement Y K' w).toRingedSite)
  (τ : TwoIso.{u, u, u, u, u, u} (A := X) (B := denseReplacement Y K' w)
    (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} (Y := denseReplacement X J' v)
      hs.ringedToposHom (denseReplacementHom X J' v))
    (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} (denseReplacementHom Y K' w) f))

/-- **The square on structure maps.** Restricted along `e_*` of a map `ι` into `𝒪_Y` through
which `f^♯` factors as `ψ` followed by `f_*ι'`, the structure map of the middle morphism of the
square factors through `(h ∘ g)_*ι'`. -/
theorem pushforward_comp_forgetFSharp {A : Y.Topos} {A' : X.Topos}
    (ι : A ⟶ Y.forgetRing.obj Y.O) (ι' : A' ⟶ X.forgetRing.obj X.O)
    (ψ : A ⟶ f.toToposHom.pushforward.obj A')
    (hψ : ι ≫ forgetFSharp f = ψ ≫ f.toToposHom.pushforward.map ι') :
    (denseReplacementHom Y K' w).toToposHom.pushforward.map ι ≫
        forgetFSharp hs.ringedToposHom =
      (denseReplacementHom Y K' w).toToposHom.pushforward.map ψ ≫ τ.e.inv.app A' ≫
        (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} (Y := denseReplacement X J' v)
          hs.ringedToposHom (denseReplacementHom X J' v)).toToposHom.pushforward.map ι' := by
  have hg : forgetFSharp (denseReplacementHom X J' v) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  have he : forgetFSharp (denseReplacementHom Y K' w) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  have h3 : forgetFSharp (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u}
      (Y := denseReplacement X J' v) hs.ringedToposHom (denseReplacementHom X J' v)) =
      forgetFSharp hs.ringedToposHom :=
    (forgetFSharp_comp.{u, u, u, u, u, u, u, u, u} (B := denseReplacement X J' v)
      hs.ringedToposHom (denseReplacementHom X J' v)).trans
      ((congrArg (fun k => forgetFSharp hs.ringedToposHom ≫ k)
        ((congrArg (fun k => hs.ringedToposHom.toToposHom.pushforward.map k) hg).trans
          (CategoryTheory.Functor.map_id _ _))).trans (Category.comp_id _))
  have h4 : forgetFSharp (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u}
      (denseReplacementHom Y K' w) f) =
      (denseReplacementHom Y K' w).toToposHom.pushforward.map (forgetFSharp f) :=
    (forgetFSharp_comp.{u, u, u, u, u, u, u, u, u} (denseReplacementHom Y K' w) f).trans
      ((congrArg (fun k => k ≫ _) he).trans (Category.id_comp _))
  have h5 : forgetFSharp hs.ringedToposHom ≫ τ.e.hom.app (X.forgetRing.obj X.O) =
      (denseReplacementHom Y K' w).toToposHom.pushforward.map (forgetFSharp f) :=
    (congrArg (fun k => k ≫ τ.e.hom.app (X.forgetRing.obj X.O)) h3).symm.trans
      (τ.commutes.trans h4)
  have h2 : forgetFSharp hs.ringedToposHom =
      (denseReplacementHom Y K' w).toToposHom.pushforward.map (forgetFSharp f) ≫
        τ.e.inv.app (X.forgetRing.obj X.O) :=
    (Iso.eq_comp_inv (τ.e.app (X.forgetRing.obj X.O))).mpr h5
  let E := (denseReplacementHom Y K' w).toToposHom.pushforward
  let τO := τ.e.inv.app (X.forgetRing.obj X.O)
  have hE : E.map ι ≫ E.map (forgetFSharp f) =
      E.map ψ ≫ E.map (f.toToposHom.pushforward.map ι') := by
    rw [← E.map_comp, hψ, E.map_comp]
  exact (congrArg (E.map ι ≫ ·) h2).trans <|
    (Category.assoc (E.map ι) (E.map (forgetFSharp f)) τO).symm.trans <|
      (congrArg (· ≫ τO) hE).trans <|
        (Category.assoc (E.map ψ) (E.map (f.toToposHom.pushforward.map ι')) τO).trans <|
          congrArg (E.map ψ ≫ ·) (τ.e.inv.naturality ι')

include τ in
/-- **The ideal condition across the square, on sections.** A section `s` of `ℐ` over `W`, carried
to `𝒪_{X'}` over `u(w(W))` by the structure maps of the restriction `Y' ⟶ Y` and of the middle
morphism, restricts along `a : v(U) ⟶ u(w(W))` to the image under the structure map of the
restriction `X' ⟶ X` of a section of `ℐ'` over `U`. -/
theorem mem_of_square
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))))
    (I' : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))))
    (ψ : (Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))).obj I.toSheafOfModules ⟶
      f.toToposHom.pushforward.obj
        ((Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))).obj
          I'.toSheafOfModules))
    (hψ : (Sheaf.moduleSheafFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))).map I.ι ≫
        forgetFSharp f =
      ψ ≫ f.toToposHom.pushforward.map
        ((Sheaf.moduleSheafFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))).map I'.ι))
    (W : Y.C) (s : ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O)).obj.obj (op W))
    (hsI : s ∈ I.toSubmodule.obj (op W)) (U : X.C) (a : v.obj U ⟶ hs.u.obj (w.obj W))
    (t : ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O)).obj.obj (op U))
    (ht : RingedSite.fSharpSection (denseRestrictSite X J' v) U t =
      (Stacks.SheafOfModules.Tensor.ringSheaf (denseReplacement X J' v).toRingedSite.O).obj.map a.op
        (RingedSite.fSharpSection hs (w.obj W)
          (RingedSite.fSharpSection (denseRestrictSite Y K' w) W s))) :
    t ∈ I'.toSubmodule.obj (op U) := by
  obtain ⟨y, rfl⟩ := (mem_submodule_iff_exists I W s).1 hsI
  refine (mem_submodule_iff_exists I' U t).2 ?_
  let ι := (Sheaf.moduleSheafFunctor
    ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))).map I.ι
  let ι' := (Sheaf.moduleSheafFunctor
    ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))).map I'.ι
  let e := denseReplacementHom Y K' w
  let g := denseReplacementHom X J' v
  let cY := e.toToposHom.adj.counit
  let cX := g.toToposHom.adj.counit
  let z := (inv (cY.app ((Sheaf.moduleSheafFunctor
    ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))).obj I.toSheafOfModules))).hom.app
      (op W) y
  have hz : (cY.app _).hom.app (op W) z = y :=
    hom_app_apply_congr (IsIso.inv_hom_id (cY.app _)) _ _
  have hαY : ∀ x, (cY.app (Y.forgetRing.obj Y.O)).hom.app (op W)
      (((sheafCompose Y.J (forget CommRingCat.{u})).map (denseRestrictSharp Y K' w)).hom.app
        (op W) x) = x :=
    hom_app_apply_congr (forget_denseRestrictSharp_comp_counit Y K' w) _
  have hinjY : ∀ x x', (cY.app (Y.forgetRing.obj Y.O)).hom.app (op W) x =
      (cY.app (Y.forgetRing.obj Y.O)).hom.app (op W) x' → x = x' := by
    intro x x' hxx
    exact (hom_app_apply_congr (IsIso.hom_inv_id (cY.app (Y.forgetRing.obj Y.O))) _ x).symm.trans
      ((congrArg ((inv (cY.app (Y.forgetRing.obj Y.O))).hom.app (op W)) hxx).trans
        (hom_app_apply_congr (IsIso.hom_inv_id (cY.app (Y.forgetRing.obj Y.O))) _ x'))
  have hσ₀ : RingedSite.fSharpSection (denseRestrictSite Y K' w) W (ι.hom.app (op W) y) =
      (e.toToposHom.pushforward.map ι).hom.app (op (w.obj W)) z := by
    refine hinjY _ _ ((hαY _).trans ?_)
    exact (congrArg (ι.hom.app (op W)) hz).symm.trans
      (hom_app_apply_congr (cY.naturality ι) _ z).symm
  have hsq := hom_app_apply_congr
    (pushforward_comp_forgetFSharp f J' v K' w hs τ ι ι' ψ hψ) (op (w.obj W)) z
  let q := (τ.e.inv.app ((Sheaf.moduleSheafFunctor
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))).obj I'.toSheafOfModules)).hom.app
        (op (w.obj W))
    ((e.toToposHom.pushforward.map ψ).hom.app (op (w.obj W)) z)
  have hσ : RingedSite.fSharpSection hs (w.obj W)
      (RingedSite.fSharpSection (denseRestrictSite Y K' w) W (ι.hom.app (op W) y)) =
      (g.toToposHom.pushforward.map ι').hom.app (op (hs.u.obj (w.obj W))) q :=
    (congrArg (RingedSite.fSharpSection hs (w.obj W)) hσ₀).trans hsq
  let q' := (g.toToposHom.pushforward.obj ((Sheaf.moduleSheafFunctor
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))).obj I'.toSheafOfModules)).obj.map
        a.op q
  have hres : (Stacks.SheafOfModules.Tensor.ringSheaf
      (denseReplacement X J' v).toRingedSite.O).obj.map a.op
      ((g.toToposHom.pushforward.map ι').hom.app (op (hs.u.obj (w.obj W))) q) =
      (g.toToposHom.pushforward.map ι').hom.app (op (v.obj U)) q' :=
    (congrArg (fun k => k q) ((g.toToposHom.pushforward.map ι').hom.naturality a.op)).symm
  refine ⟨(cX.app _).hom.app (op U) q', ?_⟩
  have hαX := hom_app_apply_congr (forget_denseRestrictSharp_comp_counit X J' v) (op U) t
  have hnX := hom_app_apply_congr (cX.naturality ι') (op U) q'
  exact hnX.symm.trans (Eq.trans (congrArg ((cX.app (X.forgetRing.obj X.O)).hom.app (op U))
    (ht.trans ((congrArg _ hσ).trans hres)).symm) hαX)

end Square

end Chase

section Statement

variable {X Y : RingedTopos.{u, u, u}}

/-- The direct-image form of the hypothesis on the ideals: if `f⁻¹ι ≫ f^♯ = φ ≫ ι'`, then the
inclusion `ℐ ↪ 𝒪_Y` followed by `𝒪_Y ⟶ f_*𝒪_X` is the transpose of `φ` followed by `f_*ι'`. -/
theorem ι_comp_forgetFSharp_eq_homEquiv_comp (f : RingedToposHom.{u, u, u, u, u, u} X Y)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))))
    (I' : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))))
    (φ : f.toToposHom.inverseImage.obj
        ((Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))).obj
          I.toSheafOfModules) ⟶
        (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))).obj
          I'.toSheafOfModules)
    (hφ : f.toToposHom.inverseImage.map
          ((Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))).map I.ι) ≫
        X.forgetRing.map f.fSharpInverseImage =
      φ ≫ (Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))).map I'.ι) :
    (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))).map I.ι ≫
      forgetFSharp f = f.toToposHom.adj.homEquiv _ _ φ ≫ f.toToposHom.pushforward.map
        ((Sheaf.moduleSheafFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))).map I'.ι) := by
  have h1 : forgetFSharp f = f.toToposHom.adj.homEquiv (Y.forgetRing.obj Y.O)
      (X.forgetRing.obj X.O) (X.forgetRing.map f.fSharpInverseImage) :=
    ((congrArg (f.toToposHom.adj.homEquiv (Y.forgetRing.obj Y.O) (X.forgetRing.obj X.O))
      (fSharpInverseImage_forget_homEquiv.{u, u, u, u, u, u} f)).trans
      (Equiv.apply_symm_apply _ _)).symm
  exact (congrArg (fun k => (Sheaf.moduleSheafFunctor
      ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))).map I.ι ≫ k) h1).trans
    ((f.toToposHom.adj.homEquiv_naturality_left (X' := (Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))).obj I.toSheafOfModules)
        (X := Y.forgetRing.obj Y.O) (Y := X.forgetRing.obj X.O)
        ((Sheaf.moduleSheafFunctor
          ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))).map I.ι)
        (X.forgetRing.map f.fSharpInverseImage)).symm.trans
      ((congrArg (f.toToposHom.adj.homEquiv _ (X.forgetRing.obj X.O)) hφ).trans
        (f.toToposHom.adj.homEquiv_naturality_right φ
          ((Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))).map I'.ι))))

/-- **[Stacks, Tag 099J].** Let `f : (Sh(𝒞), 𝒪_X) ⟶ (Sh(𝒟), 𝒪_Y)` be a morphism of ringed topoi
and let `ℐ' ⊂ 𝒪_X` and `ℐ ⊂ 𝒪_Y` be sheaves of ideals such that `f^♯` sends `f⁻¹ℐ` into `ℐ'`, that
is, such that the composite `f⁻¹ℐ ⟶ f⁻¹𝒪_Y ⟶ 𝒪_X` of the inverse image of the inclusion with the
structure map factors through `ℐ' ⊂ 𝒪_X`. Then `Rf_*` sends `D_comp(𝒪_X, ℐ')` into
`D_comp(𝒪_Y, ℐ)`.

The proof reduces to morphisms of ringed sites by [Stacks, Tag 03CR]; see the module
docstring. -/
@[stacks 099J]
theorem derivedPushforward_isDerivedComplete (f : RingedToposHom.{u, u, u, u, u, u} X Y)
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))))
    (I' : SheafOfModules.Submodule
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))))
    (hI : ∃ φ : f.toToposHom.inverseImage.obj
        ((Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))).obj
          I.toSheafOfModules) ⟶
        (Sheaf.moduleSheafFunctor ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))).obj
          I'.toSheafOfModules,
      f.toToposHom.inverseImage.map
          ((Sheaf.moduleSheafFunctor
            ((Stacks.SheafOfModules.Tensor.ringSheaf Y.toRingedSite.O))).map I.ι) ≫
        X.forgetRing.map f.fSharpInverseImage =
      φ ≫ (Sheaf.moduleSheafFunctor
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.toRingedSite.O))).map I'.ι)
    (K : DerivedCategory
      (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)))
    (hK : RingedSite.IsDerivedComplete.{u, u, u, u} X.toRingedSite I' K) :
    RingedSite.IsDerivedComplete.{u, u, u, u} Y.toRingedSite I
      ((Stacks.Cohomology.DerivedPushforward.derivedPushforward.{u, u, u, u, u, u} f).obj K) := by
  obtain ⟨φ, hφ⟩ := hI
  obtain ⟨C', instC', J', D', instD', K', v, w, u, instv, instw, -, -, -, -, -, -, -, hu, hsq⟩ :=
    exists_twoSided_isDenseSubsite_morphismOfSites X Y f
      (fun z : PEmpty.{u + 1} ↦ z.elim) (fun z : PEmpty.{u + 1} ↦ z.elim)
  obtain ⟨-, -, -, -, ⟨h₀, hsh⟩, hh, ⟨τ₀⟩⟩ := hsq
  change h₀ = hu.morphismOfTopoi at hh
  subst hh
  have := hu.isContinuous
  let hs : RingedSite.Hom (denseReplacement X J' v).toRingedSite
      (denseReplacement Y K' w).toRingedSite :=
    { u := u, isMorphismOfSites := hu
      fsharp := hsh ≫ (restrictionCommRingIso K' J' u (denseReplacement X J' v).O).hom }
  have hhs : RingedToposHom.mk.{u, u, u, u, u, u} (X := denseReplacement X J' v)
      (Y := denseReplacement Y K' w) hu.morphismOfTopoi hsh = hs.ringedToposHom := by
    unfold RingedSite.Hom.ringedToposHom; congr 1
  have τ : TwoIso.{u, u, u, u, u, u} (A := X) (B := denseReplacement Y K' w)
      (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} (Y := denseReplacement X J' v)
        hs.ringedToposHom (denseReplacementHom X J' v))
      (RingedToposHom.comp.{u, u, u, u, u, u, u, u, u} (denseReplacementHom Y K' w) f) :=
    hhs ▸ τ₀
  rw [RingedSite.isDerivedComplete_iff_forall_isDerivedCompleteAtSection] at hK ⊢
  intro W s hsI
  let N := (pushforwardModules.{u, u, u, u, u, u}
    (denseReplacementHom X J' v)).mapDerivedCategory.obj K
  let L := (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward.{u}
    hs.toRingedToposSiteHom).obj N
  let c : (pushforwardModules.{u, u, u, u, u, u}
      (denseReplacementHom Y K' w)).mapDerivedCategory.obj
      ((Stacks.Cohomology.DerivedPushforward.derivedPushforward.{u, u, u, u, u, u} f).obj K) ≅ L :=
    ((Stacks.Cohomology.DerivedPushforward.derivedPushforwardCompEquivIso f
        (denseReplacementHom Y K' w)).app K).symm ≪≫
      (τ.derivedPushforwardIso.app K).symm ≪≫
      (Stacks.Cohomology.DerivedPushforward.derivedPushforwardEquivCompIso
        (denseReplacementHom X J' v) hs.ringedToposHom).app K ≪≫
      hs.derivedPushforwardToposIso.app N
  let ε : (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward.{u}
      (denseRestrictSite Y K' w).toRingedToposSiteHom).obj L ≅
      (Stacks.Cohomology.DerivedPushforward.derivedPushforward.{u, u, u, u, u, u} f).obj K :=
    (Stacks.Cohomology.DerivedPullbackPushforwardAdjunction.derivedPushforward.{u}
      (denseRestrictSite Y K' w).toRingedToposSiteHom).mapIso c.symm ≪≫
      derivedPushforwardDenseRestrictMapIso Y K' w _
  refine RingedSite.isDerivedCompleteAtSection_of_iso _ ε W s ?_
  refine RingedSite.isDerivedCompleteAtSection_derivedPushforward (denseRestrictSite Y K' w)
    W L s ?_
  refine RingedSite.isDerivedCompleteAtSection_derivedPushforward hs (w.obj W) N _ ?_
  refine RingedSite.isDerivedCompleteAtSection_of_derivedPushforward_iso X.toRingedSite
    (denseReplacement X J' v).toRingedSite v (denseRestrictSharp X J' v) N K
    (derivedPushforwardDenseRestrictMapIso X J' v K) _ _ ?_
  intro U a t ht
  exact hK U t (mem_of_square f J' v K' w hs τ I I' _
    (ι_comp_forgetFSharp_eq_homEquiv_comp f I I' φ hφ) W s hsI U a t ht)

end Statement

end AlgebraicGeometry.RingedToposHom

end

