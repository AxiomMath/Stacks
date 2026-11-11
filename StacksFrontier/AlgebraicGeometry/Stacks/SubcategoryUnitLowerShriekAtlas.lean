module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximationLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSiteFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalPropertyAtlasBridges
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryUnitLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteCohomologyAtlas

/-!
# `g_!O_{𝒳'} = O_𝒳` for the lisse-étale and the flat-fppf site (Stacks 078A)

Let `𝒳` be an algebraic stack and let `g : (Sh(𝒳'), O_{𝒳'}) ⟶ (Sh(𝒳), O_𝒳)` be the morphism of
ringed topoi of the lisse-étale site `𝒳' = 𝒳_{lisse,étale}` inside `𝒳_étale`, or of the flat-fppf
site `𝒳' = 𝒳_{flat,fppf}` inside `𝒳_fppf` (**Stacks 0788**). **Stacks 078A** asserts that the
canonical map `g_!O_{𝒳'} ⟶ O_𝒳`, the transpose under `g_! ⊣ g^*` (**Stacks 0789**) of the
identification `O_{𝒳'} = g^{-1}O_𝒳`, is an isomorphism. This file proves both parts with no
hypothesis beyond `𝒳` being an algebraic stack.

## The proof

By `AlgebraicGeometry.Stack.isIso_subsiteUnitLowerShriekMap` the canonical map is an isomorphism
as soon as restriction along `g` is bijective on morphisms out of `O_𝒳`. A morphism out of `O_𝒳`
is a global section, and the pullback `g^*` is, up to restriction of scalars along two
isomorphisms of sheaves of rings, restriction of sheaves of modules along the inclusion
(`Stacks.Sheaves.ToposPullback.restrictionModuleIso` and
`Stacks.Sheaves.RingedToposModules.RingedToposHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso`).
So the hypothesis reduces to the statement that **restriction of global sections along the
inclusion `𝒳' ⊆ 𝒳` is bijective for every sheaf of sets on `𝒳`**:

`Γ(𝒳_τ, ℱ) = Γ(𝒳'_τ, g⁻¹ℱ)`,

which is `AlgebraicGeometry.Stack.isIso_subsiteUnitLowerShriekMap_of_bijective_sectionsPrecomp`.

That statement is the degree-zero case of the cohomology comparison of **Stacks 07AK**, and it is
proved here from the descent along representable covers of
`StacksFrontier/CategoryTheory/Sites/Cohomology/CoverDescent/Cohomology.lean`, applied as in
`AlgebraicGeometry.Stack.subsiteCohomologyIsoOfAtlas` to the class
`AlgebraicGeometry.Stack.SmoothOverAtlas` of a smooth surjective presentation of `𝒳` whose
distinguished object lies in `𝒳'`: global sections of `ℱ` are morphisms out of the final
presheaf, and `Stacks.Sites.CoverDescent.restrictHom_bijective_of_mem` says restriction is
bijective on those.

This replaces the local argument of the source — refining a function on `V` through `U × 𝐀¹`, and
pushing a vanishing function into the vanishing locus of a coordinate — by its sheaf-theoretic
core: the source's argument is exactly the verification that the presheaf `V ↦ colim_{V → U} *`
of components of the arrows from `V` into `𝒳'` has trivial sheafification, i.e. that the final
presheaf is covered by representables of `𝒳'` with fibre products again so covered, and that is
what the representable-cover class records.

## Main results

* `Stacks.Sites.CoverDescent.bijective_sectionsPrecomp_of_bijective_restrictHom`: restriction of
  global sections along a functor is bijective as soon as restriction of morphisms out of a final
  presheaf is.
* `CategoryTheory.NatIso.bijective_map_of_bijective`: bijectivity of a functor on the morphisms
  between two objects is invariant under isomorphism of functors.
* `AlgebraicGeometry.Stack.isIso_subsiteUnitLowerShriekMap_of_bijective_sectionsPrecomp`: for a
  continuous and cocontinuous full subsite, the canonical map `g_!O_{𝒳'} ⟶ O_𝒳` is an
  isomorphism as soon as restriction of global sections of sheaves of sets is bijective.
* `AlgebraicGeometry.Stack.bijective_sectionsPrecomp_of_atlas`: restriction of global sections of
  sheaves of sets along a full subcategory satisfying the two conditions of Stacks 07AK is
  bijective, at the universe of the sheaves of sets on `𝒳`, and
  `AlgebraicGeometry.Stack.bijective_sectionsPrecomp_of_atlas_ulift` at the universe of the
  schemes.
* `AlgebraicGeometry.Stack.LisseEtale.isIso_unitLowerShriekMap_algebraicStack`: **Stacks 078A
  (1)**.
* `AlgebraicGeometry.Stack.FlatFppf.isIso_unitLowerShriekMap_algebraicStack`: **Stacks 078A
  (2)**.

## Implementation notes

The functor `g_!` here is the lower shriek on sheaves of modules of Stacks 0789, the left adjoint
of `g^*`: `AlgebraicGeometry.Stack.subsiteModuleLowerShriek`, which at the two subsites is
`AlgebraicGeometry.Stack.LisseEtale.moduleLowerShriek` and
`AlgebraicGeometry.Stack.FlatFppf.moduleLowerShriek`. So the statement is about that functor.
That it agrees with `g_!` on abelian sheaves is the separate assertion of Stacks 0789 and is not
used: Stacks 078A is a statement about the module-theoretic `g_!`, and the source's proof
computes `g_!O_{𝒳'}` through the abelian presentation only to identify it, which the universal
property does here directly.

Essential smallness of the category underlying `𝒳`, which the construction of the ringed topoi
needs to sheafify at the universe of the schemes, is the instance
`AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`.

## References

* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 078A](https://stacks.math.columbia.edu/tag/078A)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.RingedToposModules Stacks.Sites.CoverDescent

namespace Stacks.Sites.CoverDescent

universe t w v u₁ u₂

variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D] (u : D ⥤ C)

/-- **Global sections along a functor, from morphisms out of a final presheaf.** Let `P` be a
presheaf on `C` all of whose values are singletons, so that morphisms `P ⟶ F` are the global
sections of `F`. If restriction along `u` is bijective on morphisms `P ⟶ F`, then restriction of
global sections `Γ(C, F) ⟶ Γ(D, u^p F)` is bijective. -/
theorem bijective_sectionsPrecomp_of_bijective_restrictHom (P F : Cᵒᵖ ⥤ Type w)
    (hP : ∀ y, Unique (P.obj y)) (h : Function.Bijective (restrictHom u P F)) :
    Function.Bijective (u.op.sectionsPrecomp (P := F)) := by
  refine ⟨fun s s' hss' ↦ ?_, fun t ↦ ?_⟩
  · let φ : F.sections → (P ⟶ F) := fun s ↦
      { app := fun y ↦ TypeCat.ofHom fun _ ↦ s.val y
        naturality := fun y y' g ↦ by ext; exact (s.property g).symm }
    have hφ : φ s = φ s' := h.1 <| by
      ext y a
      exact congrArg (fun r ↦ r.val y) hss'
    ext y
    exact congrArg (fun ψ : P ⟶ F ↦ ψ.app y (hP y).default) hφ
  · obtain ⟨ψ, hψ⟩ := h.2
      { app := fun y ↦ TypeCat.ofHom fun _ ↦ t.val y
        naturality := fun y y' g ↦ by ext; exact (t.property g).symm }
    refine ⟨⟨fun y ↦ ψ.app y (hP y).default, fun {y y'} g ↦ ?_⟩, ?_⟩
    · have hn := NatTrans.naturality_apply ψ g (hP y).default
      rw [← hn]
      exact congrArg (ψ.app y') ((hP y').uniq _)
    · ext y
      exact congrArg (fun χ : u.op ⋙ P ⟶ u.op ⋙ F ↦ χ.app y (hP (u.op.obj y)).default) hψ

/-- Global sections of `F ⋙ uliftFunctor` are those of `F`. -/
private def sectionsUliftEquiv {J : Type*} [Category J] (F : J ⥤ Type t) :
    F.sections ≃ (F ⋙ uliftFunctor.{w}).sections where
  toFun s := ⟨fun y ↦ ULift.up (s.val y), fun g ↦ congrArg ULift.up (s.property g)⟩
  invFun s := ⟨fun y ↦ (s.val y).down, fun g ↦ congrArg ULift.down (s.property g)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Restriction of global sections is insensitive to lifting the universe.** If restriction of
global sections along `G` is bijective for `F ⋙ uliftFunctor`, it is bijective for `F`. -/
theorem bijective_sectionsPrecomp_of_uliftFunctor {E : Type*} [Category E] {E' : Type*}
    [Category E'] (G : E' ⥤ E) (F : E ⥤ Type t)
    (h : Function.Bijective (G.sectionsPrecomp (P := F ⋙ uliftFunctor.{w}))) :
    Function.Bijective (G.sectionsPrecomp (P := F)) :=
  ((sectionsUliftEquiv.{_, w} (G ⋙ F)).bijective.of_comp_iff' _).1
    (h.comp (sectionsUliftEquiv.{_, w} F).bijective)

end Stacks.Sites.CoverDescent

namespace AlgebraicGeometry.Stack

universe u v w t

/-! ### Bijectivity on morphisms along isomorphic functors -/

/-- **Bijectivity of a functor on the morphisms between two objects only depends on the functor
up to isomorphism**: if `F ≅ G` and `G` is bijective on `X ⟶ Y`, so is `F`, the two maps
differing by composition with the components of the isomorphism. -/
theorem _root_.CategoryTheory.NatIso.bijective_map_of_bijective {C : Type*} [Category C]
    {D : Type*} [Category D] {F G : C ⥤ D} (e : F ≅ G) (X Y : C)
    (h : Function.Bijective (G.map : (X ⟶ Y) → (G.obj X ⟶ G.obj Y))) :
    Function.Bijective (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) := by
  have hfac : (F.map : (X ⟶ Y) → (F.obj X ⟶ F.obj Y)) =
      (fun z ↦ e.hom.app X ≫ z ≫ e.inv.app Y) ∘ G.map := by
    funext x
    simp
  rw [hfac]
  exact Function.Bijective.comp
    ⟨fun _ _ h ↦ by simpa using h, fun z ↦ ⟨e.inv.app X ≫ z ≫ e.hom.app Y, by simp⟩⟩ h

/-! ### Reduction to global sections of sheaves of sets -/

section Subsite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) (P : ObjectProperty X)
  [EssentiallySmall.{u} X]
  [P.ι.IsContinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]
  [P.ι.IsCocontinuous (subsiteTopology B S hS p τ P) (associatedTopology B S hS p τ)]

/-- **`g_!O_{𝒳'} = O_𝒳` from the comparison of global sections.** For a continuous and
cocontinuous full subsite of the site of **Stacks 06TP**, the canonical map
`g_!O_{𝒳'} ⟶ O_𝒳` of **Stacks 078A** is an isomorphism as soon as restriction of global sections
along the inclusion is bijective for every sheaf of sets on `𝒳`.

The pullback `g^*` is restriction of sheaves of modules along the inclusion followed by
restriction of scalars along two isomorphisms of sheaves of rings, so restriction along `g` on
morphisms out of `O_𝒳` is, up to composition with isomorphisms and an equivalence, restriction of
global sections of the underlying sheaf of sets (`SheafOfModules.pushforwardSections_unitHomEquiv`
at the identity structure map). This discharges the hypothesis of
`AlgebraicGeometry.Stack.isIso_subsiteUnitLowerShriekMap`. -/
theorem isIso_subsiteUnitLowerShriekMap_of_bijective_sectionsPrecomp
    (hsec : ∀ F : Xᵒᵖ ⥤ Type u, Presieve.IsSheaf (associatedTopology B S hS p τ) F →
      Function.Bijective (P.ι.op.sectionsPrecomp (P := F))) :
    IsIso (subsiteUnitLowerShriekMap B S hS p hp τ hτ P) := by
  refine isIso_subsiteUnitLowerShriekMap B S hS p hp τ hτ P fun T ↦ ?_
  let f := subsiteRingedToposHom B S hS p hp τ hτ P
  let O := Stacks.SheafOfModules.Tensor.ringSheaf (associatedRingedTopos B S hS p hp τ hτ).O
  have := isIso_fSharpInverseImage_subsiteRingedToposHom B S hS p hp τ hτ P
  have : IsIso f.toModulesHom.fSharpInverseImage := RingedToposHom.isIso_fSharpInverseImageRing f
  -- `g^*` is restriction followed by two restrictions of scalars along isomorphisms
  let ρ := Functor.isoWhiskerRight
      (Stacks.Sheaves.ToposPullback.restrictionModuleIso (subsiteTopology B S hS p τ P)
        (associatedTopology B S hS p τ) P.ι O)
      (extendScalarsFSharp f.toModulesHom) ≪≫
    Functor.isoWhiskerLeft _
      f.toModulesHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso
  let R₀ := Stacks.Sheaves.ToposPullback.restrictionModules (subsiteTopology B S hS p τ P)
    (associatedTopology B S hS p τ) P.ι O
  let e₁ := Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
    (Stacks.Sheaves.ToposPullback.restrictionRingIso (subsiteTopology B S hS p τ P)
      (associatedTopology B S hS p τ) P.ι O).symm
  let e₂ := Stacks.Sheaves.RingedPoint.restrictScalarsEquivalenceOfIso
    (asIso f.toModulesHom.fSharpInverseImage)
  let Λ := e₁.functor ⋙ e₂.functor
  have hΛ : Λ.FullyFaithful := e₁.fullyFaithfulFunctor.comp e₂.fullyFaithfulFunctor
  let i₀ := SheafOfModules.unitToPushforwardObjUnit
    (𝟙 ((P.ι.sheafPushforwardContinuous RingCat.{u} (subsiteTopology B S hS p τ P)
      (associatedTopology B S hS p τ)).obj O))
  have : IsIso i₀ := Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit _
  -- precomposition with an isomorphism is bijective
  have hpre : ∀ {A A' A'' : SheafOfModules.{u}
      ((P.ι.sheafPushforwardContinuous RingCat.{u} (subsiteTopology B S hS p τ P)
        (associatedTopology B S hS p τ)).obj O)} (i : A ⟶ A') [IsIso i],
      Function.Bijective fun y : A' ⟶ A'' ↦ i ≫ y := fun i _ ↦
    ⟨fun _ _ h ↦ (cancel_epi i).1 h, fun z ↦ ⟨inv i ≫ z, by simp⟩⟩
  -- restriction of morphisms out of `O_𝒳` along the inclusion is bijective
  have hR₀ : Function.Bijective fun x : SheafOfModules.unit O ⟶ T ↦ R₀.map x := by
    have hT : Presieve.IsSheaf (associatedTopology B S hS p τ)
        (T.val.presheaf ⋙ forget AddCommGrpCat) :=
      (isSheaf_iff_isSheaf_of_type _ _).1
        ((sheafCompose (associatedTopology B S hS p τ) (forget AddCommGrpCat.{u})).obj
          ⟨T.val.presheaf, T.isSheaf⟩).property
    have hps : Function.Bijective (SheafOfModules.pushforwardSections
        (𝟙 ((P.ι.sheafPushforwardContinuous RingCat.{u} (subsiteTopology B S hS p τ P)
          (associatedTopology B S hS p τ)).obj O)) (M := T)) :=
      hsec _ hT
    have hcomm : ((R₀.obj T).unitHomEquiv ∘ fun x : SheafOfModules.unit O ⟶ T ↦
        i₀ ≫ R₀.map x) = SheafOfModules.pushforwardSections _ ∘ T.unitHomEquiv :=
      funext fun x ↦ (SheafOfModules.pushforwardSections_unitHomEquiv _ x).symm
    have h₀ : Function.Bijective fun x : SheafOfModules.unit O ⟶ T ↦ i₀ ≫ R₀.map x :=
      ((R₀.obj T).unitHomEquiv.bijective.of_comp_iff' _).1
        (hcomm ▸ hps.comp T.unitHomEquiv.bijective)
    exact ((hpre i₀).of_comp_iff' _).1 h₀
  -- transport along `g^* ≅ Λ ∘ R₀`
  exact NatIso.bijective_map_of_bijective (F := subsiteModulePullback B S hS p hp τ hτ P)
    (G := R₀ ⋙ Λ) ρ _ _ ((hΛ.map_bijective _ _).comp (f := R₀.map) hR₀)

end Subsite

/-! ### Global sections along a full subcategory containing a presentation -/

section Atlas

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : AlgebraicStacks.{u, t} B S hS} {U₀ : BigFppfOver B S hS}
  (a : schemeStack.{u, t} B S hS U₀ ⟶ 𝒳) {τ : SiteKind} {P : ObjectProperty 𝒳.val.val.obj}
  (hcl : IsClosedUnderSitePullback B S hS 𝒳.val.val.p P τ)
  (hasm : AlgebraicStacks.IsSmooth B S hS a) (hasurj : IsSurjective B S hS a)
  (hx : P ((CatFiberedInGroupoids.homFunctor a.hom).obj (Over.mk (𝟙 U₀))))

include hcl hasm hasurj hx

/-- **Global sections along a full subcategory satisfying the conditions of Stacks 07AK.** Let
`𝒳` be an algebraic stack, `τ` the étale or the fppf topology, and `𝒳' ⊆ 𝒳` a full subcategory
closed under the pullbacks `τ` calls for and containing the distinguished object of a smooth
surjective presentation `a : (Sch/U₀) ⟶ 𝒳`. Then for every sheaf of sets `ℱ` on `𝒳_τ`
restriction of global sections

`Γ(𝒳_τ, ℱ) ⟶ Γ(𝒳'_τ, ℱ|_{𝒳'})`

is bijective. This is the degree-zero case of the cohomology comparison of **Stacks 07AK**, and
the input of **Stacks 078A**.

Global sections are morphisms out of the final presheaf `Ψ(𝟭)`, which belongs to the class
`AlgebraicGeometry.Stack.SmoothOverAtlas` of `a`; that class is closed under representable covers
by objects of `𝒳'` (`AlgebraicGeometry.Stack.isClosedUnderRepresentableCovers_smoothOverAtlas`),
and on a member of such a class restriction of morphisms into a sheaf is bijective
(`Stacks.Sites.CoverDescent.restrictHom_bijective_of_mem`). -/
theorem bijective_sectionsPrecomp_of_atlas (F : 𝒳.val.val.objᵒᵖ ⥤ Type (u + 1))
    (hF : Presieve.IsSheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) F) :
    Function.Bijective (P.ι.op.sectionsPrecomp (P := F)) := by
  have := isContinuous_ι_associatedTopology_of_isClosedUnderSitePullback B S hS
    𝒳.val.val.p P τ 𝒳.val.isFiberedInGroupoids hcl
  have h𝔎 := isClosedUnderRepresentableCovers_smoothOverAtlas a τ P hcl hasm hasurj hx
  have hF₀ : SmoothOverAtlas 𝒳 a (componentPresheaf (𝟭 𝒳.val.val.obj)) := Or.inl rfl
  exact bijective_sectionsPrecomp_of_bijective_restrictHom P.ι _ F componentPresheafIdUnique
    (restrictHom_bijective_of_mem _ h𝔎 hF₀ F hF)

/-- **Global sections along a full subcategory satisfying the conditions of Stacks 07AK, at the
universe of the schemes.** The form of
`AlgebraicGeometry.Stack.bijective_sectionsPrecomp_of_atlas` for sheaves of sets with values in
`Type u`, the universe in which the sections of the structure sheaf and of sheaves of modules on
`𝒳` live; it follows by lifting the sheaf to `Type (u + 1)`. -/
theorem bijective_sectionsPrecomp_of_atlas_ulift (F : 𝒳.val.val.objᵒᵖ ⥤ Type u)
    (hF : Presieve.IsSheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) F) :
    Function.Bijective (P.ι.op.sectionsPrecomp (P := F)) :=
  bijective_sectionsPrecomp_of_uliftFunctor.{u, u + 1} P.ι.op F
    (bijective_sectionsPrecomp_of_atlas a hcl hasm hasurj hx _
      ((Presieve.isSheaf_comp_uliftFunctor_iff _).2 hF))

end Atlas

/-! ### The lisse-étale site -/

namespace LisseEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, t} B S hS)

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- **Restriction of global sections to the lisse-étale site is bijective.** For every sheaf of
sets `ℱ` on `𝒳_étale` of an algebraic stack, `Γ(𝒳_étale, ℱ) = Γ(𝒳_{lisse,étale}, g⁻¹ℱ)`: the
smooth objects are closed under the morphisms lying over smooth morphisms of schemes, and they
contain the distinguished object of any smooth surjective presentation of `𝒳`. -/
theorem bijective_sectionsPrecomp_inclusion (F : 𝒳.val.val.objᵒᵖ ⥤ Type u)
    (hF : Presieve.IsSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B)) F) :
    Function.Bijective
      ((smoothObject.{u, t} B S hS 𝒳).ι.op.sectionsPrecomp (P := F)) := by
  obtain ⟨U₀, a, hasm, hasurj⟩ := exists_smooth_surjective_schemeStack.{u, t} B S hS 𝒳
  exact bijective_sectionsPrecomp_of_atlas_ulift a
    (Or.inl ⟨rfl, fun f hf hy ↦ closedUnderSmoothMorphisms.{u, t} B S hS 𝒳 f hf hy⟩) hasm hasurj
    (smoothObject_map.{u, t} B S hS a hasm ⟨_, smoothObject_schemeStack_id.{u, t} B S hS U₀⟩)
    F hF

/-- **Stacks 078A (1)**: `g_!O_{𝒳_{lisse,étale}} = O_𝒳` for every algebraic stack `𝒳`. The
canonical map from the lower shriek, along the morphism of ringed topoi
`g : (Sh(𝒳_{lisse,étale}), O_{𝒳_{lisse,étale}}) ⟶ (Sh(𝒳_étale), O_𝒳)` of **Stacks 0788**, of
the structure sheaf of the lisse-étale site to the structure sheaf of `𝒳` — the transpose under
the adjunction `g_! ⊣ g^*` of **Stacks 0789** (1) of the identification
`O_{𝒳_{lisse,étale}} = g^{-1}O_𝒳` — is an isomorphism. -/
@[stacks 078A "part (1): `g_!O_{𝒳_{lisse,étale}} = O_𝒳` for every algebraic stack `𝒳`"]
theorem isIso_unitLowerShriekMap_algebraicStack : IsIso (unitLowerShriekMap.{u, t} B S hS 𝒳) :=
  isIso_subsiteUnitLowerShriekMap_of_bijective_sectionsPrecomp B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B)
    (smoothObject.{u, t} B S hS 𝒳) (bijective_sectionsPrecomp_inclusion B S hS 𝒳)

end LisseEtale

/-! ### The flat-fppf site -/

namespace FlatFppf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, t} B S hS)

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- **Restriction of global sections to the flat-fppf site is bijective.** For every sheaf of
sets `ℱ` on `𝒳_fppf` of an algebraic stack, `Γ(𝒳_fppf, ℱ) = Γ(𝒳_{flat,fppf}, g⁻¹ℱ)`: the flat
objects are closed under the morphisms lying over flat, locally finitely presented morphisms of
schemes, and they contain the distinguished object of any smooth surjective presentation of
`𝒳`. -/
theorem bijective_sectionsPrecomp_inclusion (F : 𝒳.val.val.objᵒᵖ ⥤ Type u)
    (hF : Presieve.IsSheaf (associatedTopology B S hS 𝒳.val.val.p B.topology) F) :
    Function.Bijective ((objectProperty B S hS 𝒳).ι.op.sectionsPrecomp (P := F)) := by
  obtain ⟨U₀, a, hasm, hasurj⟩ := exists_smooth_surjective_schemeStack.{u, t} B S hS 𝒳
  exact bijective_sectionsPrecomp_of_atlas_ulift a
    (Or.inr ⟨rfl, fun f hf hlfp hy ↦ closedUnderFlatMorphisms B S hS 𝒳 f hf hlfp hy⟩) hasm hasurj
    (flatObject_map B S hS a (AlgebraicStacks.isFlat_of_isSmooth B S hS a hasm)
      ⟨_, AlgebraicStacks.isFlat_of_isSmooth B S hS _
        (smoothObject_schemeStack_id.{u, t} B S hS U₀)⟩)
    F hF

/-- **Stacks 078A (2)**: `g_!O_{𝒳_{flat,fppf}} = O_𝒳` for every algebraic stack `𝒳`. The
canonical map from the lower shriek, along the morphism of ringed topoi
`g : (Sh(𝒳_{flat,fppf}), O_{𝒳_{flat,fppf}}) ⟶ (Sh(𝒳_fppf), O_𝒳)` of **Stacks 0788**, of the
structure sheaf of the flat-fppf site to the structure sheaf of `𝒳` — the transpose under the
adjunction `g_! ⊣ g^*` of **Stacks 0789** (2) of the identification
`O_{𝒳_{flat,fppf}} = g^{-1}O_𝒳` — is an isomorphism. -/
@[stacks 078A "part (2): `g_!O_{𝒳_{flat,fppf}} = O_𝒳` for every algebraic stack `𝒳`"]
theorem isIso_unitLowerShriekMap_algebraicStack : IsIso (unitLowerShriekMap B S hS 𝒳) :=
  isIso_subsiteUnitLowerShriekMap_of_bijective_sectionsPrecomp B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids B.topology le_rfl (objectProperty B S hS 𝒳)
    (bijective_sectionsPrecomp_inclusion B S hS 𝒳)

end FlatFppf

end AlgebraicGeometry.Stack

end
