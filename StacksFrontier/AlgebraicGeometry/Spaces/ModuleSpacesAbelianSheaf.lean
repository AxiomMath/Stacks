module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleDirectImageAbelianSheafUlift

/-!
# The abelian sheaf of an `𝒪_Y`-module on the spaces-étale site

An `𝒪_Y`-module `M` of this development lives on the small étale site of the algebraic space
`Y`.  The direct image `f_*M` along `f : Y ⟶ X` is built by transporting `M` to the spaces-étale
site of `Y` through the inverse of the comparison equivalence of Stacks 03G1, restricting along
spaces-étale base change (the direct image of Stacks 03G2, part (1)), and coming back along the
comparison for `X`.  A statement about the sections of `f_*M` therefore reads, one step in, as a
statement about the abelian sheaf `M^{sp}` on the spaces-étale site of `Y` that the first step
produces.  This file names that abelian sheaf and records, on sections, its two relations: to `M`
itself, and to `f_*M`.

## Main definitions

* `AlgebraicGeometry.Space.moduleSpacesAbelianSheaf`: the abelian sheaf `M^{sp}` on the
  spaces-étale site of `Y` underlying the inverse image of `M` along the inverse of the
  comparison equivalence of Stacks 03G1.  Its sheaf of sets is the image of the sheaf of sets of
  `M` under that inverse, on the nose
  (`AlgebraicGeometry.Space.sheafCompose_obj_moduleSpacesAbelianSheaf_obj`).
* `AlgebraicGeometry.Space.moduleSpacesAbelianSheafRestrictionIso`: `M^{sp}` restricted back
  along the comparison functor is the abelian sheaf underlying `M`.
* `AlgebraicGeometry.Space.modulePushforwardSpacesAbelianSheafIso`: the abelian sheaf
  underlying `f_*M` is `M^{sp}` restricted along spaces-étale base change and then along the
  comparison functor of `X`.

## Main results

* `AlgebraicGeometry.Space.moduleSpacesAbelianSheafRestrictionIso_hom_app_apply`: on sections,
  the first comparison is the counit of the comparison equivalence of sheaves of sets.
* `AlgebraicGeometry.Space.modulePushforwardSpacesAbelianSheafIso_hom_app_apply`: on sections,
  the second comparison is the identity.

## Implementation notes

Each comparison is a chain of isomorphisms of which one or two links are inverses obtained from
`asIso`, and such an inverse does not reduce.  So the identifications on sections are not `rfl`:
each is proved link by link, through the underlying-sheaf-of-sets lemmas of the links (such as
`Stacks.Sheaves.ToposPullback.moduleSheafFunctor_map_pullbackModuleCompObjIso_hom`), at abstract
sites and transporting functors.

The concrete statements are obtained from the abstract ones in a form that keeps the concrete
isomorphism a *variable*: each abstract lemma used at a concrete site takes an isomorphism `e`
together with an equation `e = …` naming its construction, and is applied at the concrete
isomorphism with `rfl`.  Applying the abstract lemma at the construction directly instead leaves
the kernel to compare two spellings of the same component whose implicit objects differ — a
composite of functors against the functor it unfolds to, the small étale topology against the
topology of the small étale ringed site — and that comparison exhausts its budget,
while the equation `e = …` is checked at once.

## References

* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback

namespace Stacks.Sheaves.ToposPullback

universe ww vv uu vv' uu' vv'' uu''

section Underlying

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww})]

/-- If a functor sends a component of an isomorphism of functors to the forward map of an
isomorphism `k`, then it sends the inverse component to the inverse map of `k`. -/
private theorem map_inv_app_eq_of_map_hom_app_eq {A B Z : Type*} [Category A] [Category B]
    [Category Z] {F G : A ⥤ B} (e : F ≅ G) (P : B ⥤ Z) (M : A)
    (k : P.obj (F.obj M) ≅ P.obj (G.obj M))
    (h : P.map (e.hom.app M) = k.hom) : P.map (e.inv.app M) = k.inv :=
  Iso.inv_ext (f := P.mapIso (e.app M)) ((congrArg (· ≫ k.inv) h).trans k.hom_inv_id)

/-- The compatibility `Stacks.Sheaves.ToposPullback.pullbackModuleCompToSheafIso` of Stacks 03D1
with the forgetful functor, read on underlying sheaves of sets, is the comparison `ε` of the
transporting functor with restriction: every other link of it is the identity on sections. -/
theorem sheafCompose_map_pullbackModuleCompToSheafIso_hom_app (G : C ⥤ D) [G.IsContinuous J K]
    (O : Sheaf K RingCat.{ww}) (Φ : Sheaf K (Type ww) ⥤ Sheaf J (Type ww))
    [PreservesFiniteProducts Φ] (ε : Φ ≅ G.sheafPushforwardContinuous (Type ww) J K)
    (M : SheafOfModules.{ww} O) :
    (sheafCompose J (forget AddCommGrpCat.{ww})).map
        ((pullbackModuleCompToSheafIso J K G O Φ ε).hom.app M) =
      ε.hom.app (Sheaf.moduleSheaf O M) :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- The inverse of `Stacks.Sheaves.ToposPullback.pullbackModuleCompToSheafIso`, read on underlying
sheaves of sets, is the inverse of the comparison `ε`.  The inverse is obtained from `asIso` and
does not reduce, so this is derived from the forward statement rather than computed. -/
theorem sheafCompose_map_pullbackModuleCompToSheafIso_inv_app (G : C ⥤ D) [G.IsContinuous J K]
    (O : Sheaf K RingCat.{ww}) (Φ : Sheaf K (Type ww) ⥤ Sheaf J (Type ww))
    [PreservesFiniteProducts Φ] (ε : Φ ≅ G.sheafPushforwardContinuous (Type ww) J K)
    (M : SheafOfModules.{ww} O) :
    (sheafCompose J (forget AddCommGrpCat.{ww})).map
        ((pullbackModuleCompToSheafIso J K G O Φ ε).inv.app M) =
      ε.inv.app (Sheaf.moduleSheaf O M) :=
  map_inv_app_eq_of_map_hom_app_eq (pullbackModuleCompToSheafIso J K G O Φ ε)
    (sheafCompose J (forget AddCommGrpCat.{ww})) M (ε.app (Sheaf.moduleSheaf O M))
    (sheafCompose_map_pullbackModuleCompToSheafIso_hom_app J K G O Φ ε M)

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The underlying morphism of sheaves of sets of a component of a composite of isomorphisms of
functors into abelian sheaves is the composite of the underlying morphisms. -/
theorem sheafCompose_map_trans_hom_app {𝒜 : Type uu''} [Category.{vv''} 𝒜]
    {F G H : 𝒜 ⥤ Sheaf J AddCommGrpCat.{ww}} (e : F ≅ G) (e' : G ≅ H) (X : 𝒜) :
    (sheafCompose J (forget AddCommGrpCat.{ww})).map ((e ≪≫ e').hom.app X) =
      (sheafCompose J (forget AddCommGrpCat.{ww})).map (e.hom.app X) ≫
        (sheafCompose J (forget AddCommGrpCat.{ww})).map (e'.hom.app X) :=
  Functor.map_comp _ _ _

omit [J.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})] in
/-- The isomorphism `Stacks.Sheaves.ToposPullback.compRestrictScalarsToSheafIso` absorbing a
restriction of scalars has identity components. -/
theorem compRestrictScalarsToSheafIso_hom_app {R R' : Sheaf J RingCat.{ww}}
    {𝒜 : Type uu''} [Category.{vv''} 𝒜] (B : 𝒜 ⥤ SheafOfModules.{ww} R') (a : R ⟶ R') (X : 𝒜) :
    (compRestrictScalarsToSheafIso B a).hom.app X = 𝟙 _ := by
  rfl

omit [J.HasSheafCompose (forget RingCat.{ww})] in
/-- The isomorphism `Stacks.Sheaves.ToposPullback.compRestrictScalarsToSheafIso` disappears from a
composite of underlying morphisms of sheaves of sets.

It is stated as a cancellation rather than as an identity morphism because the two sides of the
component agree only after unfolding the restriction of scalars; in this form no identity
morphism is left whose object has to be matched against the next factor. -/
theorem sheafCompose_map_compRestrictScalarsToSheafIso_hom_app_comp {R R' : Sheaf J RingCat.{ww}}
    {𝒜 : Type uu''} [Category.{vv''} 𝒜] (B : 𝒜 ⥤ SheafOfModules.{ww} R') (a : R ⟶ R') (X : 𝒜)
    {Z : Sheaf J (Type ww)}
    (h : (sheafCompose J (forget AddCommGrpCat.{ww})).obj
      ((B ⋙ SheafOfModules.toSheaf.{ww} R').obj X) ⟶ Z) :
    (sheafCompose J (forget AddCommGrpCat.{ww})).map
        ((compRestrictScalarsToSheafIso B a).hom.app X) ≫ h = h :=
  rfl

/-- The comparison `Stacks.Sheaves.ToposPullback.pullbackModuleCompIso` of iterated inverse
images of modules is the identity on underlying sheaves of sets. -/
theorem sheafCompose_map_toSheaf_map_pullbackModuleCompIso_hom_app
    {E : Type uu''} [Category.{vv''} E]
    {L : GrothendieckTopology E} [L.HasSheafCompose (forget RingCat.{ww})]
    [L.HasSheafCompose (forget AddCommGrpCat.{ww})]
    (Φ : Sheaf K (Type ww) ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
    (Ψ : Sheaf L (Type ww) ⥤ Sheaf K (Type ww)) [PreservesFiniteProducts Ψ]
    (R : Sheaf L RingCat.{ww}) (M : SheafOfModules.{ww} R) :
    (sheafCompose J (forget AddCommGrpCat.{ww})).map
        ((SheafOfModules.toSheaf.{ww} (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R))).map
          ((pullbackModuleCompIso J K Φ Ψ R).hom.app M)) = 𝟙 _ :=
  moduleSheafFunctor_map_pullbackModuleCompObjIso_hom J K Φ Ψ R M

/-- The inverse of the comparison `Stacks.Sheaves.ToposPullback.pullbackModuleCompIso` is the
identity on underlying sheaves of sets.  The inverse is obtained from `asIso` and does not reduce,
so this is derived from the forward statement. -/
theorem sheafCompose_map_toSheaf_map_pullbackModuleCompIso_inv_app
    {E : Type uu''} [Category.{vv''} E]
    {L : GrothendieckTopology E} [L.HasSheafCompose (forget RingCat.{ww})]
    [L.HasSheafCompose (forget AddCommGrpCat.{ww})]
    (Φ : Sheaf K (Type ww) ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
    (Ψ : Sheaf L (Type ww) ⥤ Sheaf K (Type ww)) [PreservesFiniteProducts Ψ]
    (R : Sheaf L RingCat.{ww}) (M : SheafOfModules.{ww} R) :
    (sheafCompose J (forget AddCommGrpCat.{ww})).map
        ((SheafOfModules.toSheaf.{ww} (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R))).map
          ((pullbackModuleCompIso J K Φ Ψ R).inv.app M)) = 𝟙 _ :=
  map_inv_app_eq_of_map_hom_app_eq (pullbackModuleCompIso J K Φ Ψ R)
    (SheafOfModules.toSheaf.{ww} (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R)) ⋙
      sheafCompose J (forget AddCommGrpCat.{ww})) M (Iso.refl _)
    (sheafCompose_map_toSheaf_map_pullbackModuleCompIso_hom_app J K Φ Ψ R M)

/-- **The compatibility for a section of a restriction functor is, on sheaves of sets, the
section's comparison.**  The isomorphism
`Stacks.Sheaves.ToposPullback.pullbackModuleSectionToSheafIso` built from
`ε : Φ ⋙ G.sheafPushforwardContinuous … ≅ 𝟭`, read on underlying sheaves of sets, is the
component of `ε` at the sheaf of sets underlying the module: every other link of it is the
identity on sections. -/
theorem sheafCompose_map_pullbackModuleSectionToSheafIso_hom_app (G : C ⥤ D) [G.IsContinuous J K]
    (O : Sheaf J RingCat.{ww}) (Φ : Sheaf J (Type ww) ⥤ Sheaf K (Type ww))
    [PreservesFiniteProducts Φ]
    (ε : Φ ⋙ G.sheafPushforwardContinuous (Type ww) J K ≅ 𝟭 (Sheaf J (Type ww)))
    (M : SheafOfModules.{ww} O) :
    (sheafCompose J (forget AddCommGrpCat.{ww})).map
        ((pullbackModuleSectionToSheafIso J K G O Φ ε).hom.app M) =
      ε.hom.app (Sheaf.moduleSheaf O M) := by
  have h1 := sheafCompose_map_pullbackModuleCompToSheafIso_inv_app J K G
    (pullbackRingSheaf K Φ O) (G.sheafPushforwardContinuous (Type ww) J K) (Iso.refl _)
    ((pullbackModuleFunctor K Φ O).obj M)
  simp only [Iso.refl_inv, NatTrans.id_app] at h1
  simp only [pullbackModuleSectionToSheafIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Functor.associator_inv_app,
    compRestrictScalarsToSheafIso_hom_app, h1]
  exact Sheaf.hom_ext_sections fun _ _ ↦ rfl

/-- `Stacks.Sheaves.ToposPullback.sheafCompose_map_pullbackModuleSectionToSheafIso_hom_app` for an
isomorphism given together with an equation naming it as
`Stacks.Sheaves.ToposPullback.pullbackModuleSectionToSheafIso`.  This is the form to apply at a
concrete isomorphism, with `rfl` for the equation; see the implementation notes. -/
theorem sheafCompose_map_hom_app_of_eq_pullbackModuleSectionToSheafIso (G : C ⥤ D)
    [G.IsContinuous J K] (O : Sheaf J RingCat.{ww}) (Φ : Sheaf J (Type ww) ⥤ Sheaf K (Type ww))
    [PreservesFiniteProducts Φ]
    (ε : Φ ⋙ G.sheafPushforwardContinuous (Type ww) J K ≅ 𝟭 (Sheaf J (Type ww)))
    (e : pullbackModuleFunctor K Φ O ⋙ SheafOfModules.toSheaf.{ww} (pullbackRingSheaf K Φ O) ⋙
        G.sheafPushforwardContinuous AddCommGrpCat.{ww} J K ≅ SheafOfModules.toSheaf.{ww} O)
    (he : e = pullbackModuleSectionToSheafIso J K G O Φ ε) (M : SheafOfModules.{ww} O) :
    (sheafCompose J (forget AddCommGrpCat.{ww})).map (e.hom.app M) =
      ε.hom.app (Sheaf.moduleSheaf O M) := by
  subst he
  exact sheafCompose_map_pullbackModuleSectionToSheafIso_hom_app J K G O Φ ε M

/-- `Stacks.Sheaves.ToposPullback.sheafCompose_map_pullbackModuleCompToSheafIso_hom_app` for an
isomorphism given together with an equation naming it as
`Stacks.Sheaves.ToposPullback.pullbackModuleCompToSheafIso`, to be applied at a concrete
isomorphism with `rfl`. -/
theorem sheafCompose_map_hom_app_of_eq_pullbackModuleCompToSheafIso (G : C ⥤ D)
    [G.IsContinuous J K] (O : Sheaf K RingCat.{ww}) (Φ : Sheaf K (Type ww) ⥤ Sheaf J (Type ww))
    [PreservesFiniteProducts Φ] (ε : Φ ≅ G.sheafPushforwardContinuous (Type ww) J K)
    (e : pullbackModuleFunctor J Φ O ⋙ SheafOfModules.toSheaf.{ww} (pullbackRingSheaf J Φ O) ≅
      SheafOfModules.toSheaf.{ww} O ⋙ G.sheafPushforwardContinuous AddCommGrpCat.{ww} J K)
    (he : e = pullbackModuleCompToSheafIso J K G O Φ ε) (M : SheafOfModules.{ww} O) :
    (sheafCompose J (forget AddCommGrpCat.{ww})).map (e.hom.app M) =
      ε.hom.app (Sheaf.moduleSheaf O M) := by
  subst he
  exact sheafCompose_map_pullbackModuleCompToSheafIso_hom_app J K G O Φ ε M

omit [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})] in
/-- Restriction of abelian sheaves along a continuous functor, read on underlying sheaves of
sets, is restriction of sheaves of sets: on morphisms, on the nose. -/
theorem sheafCompose_map_sheafPushforwardContinuous_map (G : C ⥤ D) [G.IsContinuous J K]
    {F F' : Sheaf K AddCommGrpCat.{ww}} (g : F ⟶ F') :
    (sheafCompose J (forget AddCommGrpCat.{ww})).map
        ((G.sheafPushforwardContinuous AddCommGrpCat.{ww} J K).map g) =
      (G.sheafPushforwardContinuous (Type ww) J K).map
        ((sheafCompose K (forget AddCommGrpCat.{ww})).map g) :=
  rfl

end Underlying

section Comp

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  {E : Type uu''} [Category.{vv''} E]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) {L : GrothendieckTopology E}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww})]
  [L.HasSheafCompose (forget RingCat.{ww})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [L.HasSheafCompose (forget AddCommGrpCat.{ww})]
  (Φ : Sheaf K (Type ww) ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  (Ψ : Sheaf L (Type ww) ⥤ Sheaf K (Type ww)) [PreservesFiniteProducts Ψ]
  (Φa : Sheaf K AddCommGrpCat.{ww} ⥤ Sheaf J AddCommGrpCat.{ww})

/-- **The compatibility of Stacks 03D1 with the forgetful functor for a composite, from the
compatibility for its outer factor**, after a restriction of scalars.  For transporting functors
`Ψ` and `Φ` and a comparison `hΦ` for `Φ`, the abelian sheaf underlying the inverse image of a
module along `Ψ ⋙ Φ`, with scalars restricted along any `a`, is the image under `Φa` of the
abelian sheaf underlying the inverse image along `Ψ` alone.

This is `Stacks.Sheaves.ToposPullback.pullbackModuleToSheafIsoComp` stopped before its comparison
for the inner factor, so that the inner inverse image is kept as it is. -/
def pullbackModuleRestrictScalarsToSheafIsoComp
    (hΦ : ∀ O : Sheaf K RingCat.{ww},
      pullbackModuleFunctor J Φ O ⋙ SheafOfModules.toSheaf.{ww} (pullbackRingSheaf J Φ O) ≅
        SheafOfModules.toSheaf.{ww} O ⋙ Φa)
    (R : Sheaf L RingCat.{ww}) {R₀ : Sheaf J RingCat.{ww}}
    (a : R₀ ⟶ pullbackRingSheaf J (Ψ ⋙ Φ) R) :
    (pullbackModuleFunctor J (Ψ ⋙ Φ) R ⋙ SheafOfModules.restrictScalars a) ⋙
        SheafOfModules.toSheaf.{ww} R₀ ≅
      pullbackModuleFunctor K Ψ R ⋙ SheafOfModules.toSheaf.{ww} (pullbackRingSheaf K Ψ R) ⋙ Φa :=
  compRestrictScalarsToSheafIso (pullbackModuleFunctor J (Ψ ⋙ Φ) R) a ≪≫
    (Functor.isoWhiskerRight (pullbackModuleCompIso J K Φ Ψ R)
        (SheafOfModules.toSheaf.{ww}
          (pullbackRingSheaf J Φ (pullbackRingSheaf K Ψ R)))).symm ≪≫
    Functor.isoWhiskerLeft (pullbackModuleFunctor K Ψ R) (hΦ (pullbackRingSheaf K Ψ R))

/-- `Stacks.Sheaves.ToposPullback.pullbackModuleRestrictScalarsToSheafIsoComp` is, on underlying
sheaves of sets, the outer comparison `hΦ`: the restriction of scalars and the comparison of
iterated inverse images are the identity on sections.  Stated for an isomorphism given together
with an equation naming it, to be applied at a concrete isomorphism with `rfl`. -/
theorem sheafCompose_map_hom_app_of_eq_pullbackModuleRestrictScalarsToSheafIsoComp
    (hΦ : ∀ O : Sheaf K RingCat.{ww},
      pullbackModuleFunctor J Φ O ⋙ SheafOfModules.toSheaf.{ww} (pullbackRingSheaf J Φ O) ≅
        SheafOfModules.toSheaf.{ww} O ⋙ Φa)
    (R : Sheaf L RingCat.{ww}) {R₀ : Sheaf J RingCat.{ww}}
    (a : R₀ ⟶ pullbackRingSheaf J (Ψ ⋙ Φ) R)
    (e : (pullbackModuleFunctor J (Ψ ⋙ Φ) R ⋙ SheafOfModules.restrictScalars a) ⋙
        SheafOfModules.toSheaf.{ww} R₀ ≅
      pullbackModuleFunctor K Ψ R ⋙ SheafOfModules.toSheaf.{ww} (pullbackRingSheaf K Ψ R) ⋙ Φa)
    (he : e = pullbackModuleRestrictScalarsToSheafIsoComp J K Φ Ψ Φa hΦ R a)
    (M : SheafOfModules.{ww} R) :
    (sheafCompose J (forget AddCommGrpCat.{ww})).map (e.hom.app M) =
      (sheafCompose J (forget AddCommGrpCat.{ww})).map
        ((hΦ (pullbackRingSheaf K Ψ R)).hom.app ((pullbackModuleFunctor K Ψ R).obj M)) := by
  subst he
  refine (sheafCompose_map_trans_hom_app J _ _ M).trans ?_
  refine (sheafCompose_map_compRestrictScalarsToSheafIso_hom_app_comp J _ a M _).trans ?_
  refine (sheafCompose_map_trans_hom_app J _ _ M).trans ?_
  exact (congrArg (· ≫ _)
    (sheafCompose_map_toSheaf_map_pullbackModuleCompIso_inv_app J K Φ Ψ R M)).trans
    (Category.id_comp _)

/-- `Stacks.Sheaves.ToposPullback.pullbackModuleToSheafIsoComp` is, on underlying sheaves of
sets, the outer comparison `hΦ` followed by the image under `Φa` of the inner comparison `hΨ`.
Stated for an isomorphism given together with an equation naming it, to be applied at a concrete
isomorphism with `rfl`. -/
theorem sheafCompose_map_hom_app_of_eq_pullbackModuleToSheafIsoComp
    (Ψa : Sheaf L AddCommGrpCat.{ww} ⥤ Sheaf K AddCommGrpCat.{ww})
    (hΦ : ∀ O : Sheaf K RingCat.{ww},
      pullbackModuleFunctor J Φ O ⋙ SheafOfModules.toSheaf.{ww} (pullbackRingSheaf J Φ O) ≅
        SheafOfModules.toSheaf.{ww} O ⋙ Φa)
    (hΨ : ∀ R : Sheaf L RingCat.{ww},
      pullbackModuleFunctor K Ψ R ⋙ SheafOfModules.toSheaf.{ww} (pullbackRingSheaf K Ψ R) ≅
        SheafOfModules.toSheaf.{ww} R ⋙ Ψa)
    (R : Sheaf L RingCat.{ww})
    (e : pullbackModuleFunctor J (Ψ ⋙ Φ) R ⋙
        SheafOfModules.toSheaf.{ww} (pullbackRingSheaf J (Ψ ⋙ Φ) R) ≅
      SheafOfModules.toSheaf.{ww} R ⋙ Ψa ⋙ Φa)
    (he : e = pullbackModuleToSheafIsoComp J K L Φ Ψ Φa Ψa hΦ hΨ R)
    (M : SheafOfModules.{ww} R) :
    (sheafCompose J (forget AddCommGrpCat.{ww})).map (e.hom.app M) =
      (sheafCompose J (forget AddCommGrpCat.{ww})).map
          ((hΦ (pullbackRingSheaf K Ψ R)).hom.app ((pullbackModuleFunctor K Ψ R).obj M)) ≫
        (sheafCompose J (forget AddCommGrpCat.{ww})).map (Φa.map ((hΨ R).hom.app M)) := by
  subst he
  refine (sheafCompose_map_trans_hom_app J _ _ M).trans ?_
  refine (congrArg (· ≫ _)
    (sheafCompose_map_toSheaf_map_pullbackModuleCompIso_inv_app J K Φ Ψ R M)).trans
    ((Category.id_comp _).trans ?_)
  exact sheafCompose_map_trans_hom_app J _ _ M

end Comp

end Stacks.Sheaves.ToposPullback

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The abelian sheaf of an `𝒪_Y`-module on the spaces-étale site.**  The abelian sheaf
underlying the inverse image of an `𝒪_Y`-module along the inverse of the comparison equivalence
of Stacks 03G1, a sheaf on the spaces-étale site of `Y`.

This is the first step of the direct image `AlgebraicGeometry.Space.modulePushforward`: its
sections over the image of an étale chart of `Y` are the sections of the module there
(`AlgebraicGeometry.Space.moduleSpacesAbelianSheafRestrictionIso_hom_app_apply`), and its
restriction along base change computes the direct image
(`AlgebraicGeometry.Space.modulePushforwardSpacesAbelianSheafIso`). -/
def moduleSpacesAbelianSheaf (Y : AlgebraicSpaces B S hS) :
    Modules.{u, u} B S hS Y.1 Y.2 ⥤ Sheaf (SpacesEtale.topology B S hS Y) AddCommGrpCat.{u} :=
  pullbackModuleFunctor.{u, u, u + 1, u + 1, u, u + 1} (SpacesEtale.topology B S hS Y)
      (smallEtaleComparisonRestriction B S hS Y).inv (structureRingSheaf B S hS Y) ⋙
    SheafOfModules.toSheaf.{u} _

/-- The sheaf of sets underlying `AlgebraicGeometry.Space.moduleSpacesAbelianSheaf` is the image
of the sheaf of sets underlying the module under the inverse of the comparison equivalence, on
the nose. -/
theorem sheafCompose_obj_moduleSpacesAbelianSheaf_obj (Y : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (sheafCompose (SpacesEtale.topology B S hS Y) (forget AddCommGrpCat.{u})).obj
        ((moduleSpacesAbelianSheaf B S hS Y).obj M) =
      (smallEtaleComparisonRestriction B S hS Y).inv.obj
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M) :=
  rfl

/-- The sections of `AlgebraicGeometry.Space.moduleSpacesAbelianSheaf` over an object of the
spaces-étale site are the sections there of the image of the sheaf of sets underlying the module
under the inverse of the comparison equivalence, on the nose. -/
theorem moduleSpacesAbelianSheaf_obj_obj_obj (Y : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (W : (SpacesEtale B S hS Y)ᵒᵖ) :
    (((moduleSpacesAbelianSheaf B S hS Y).obj M).obj.obj W : Type u) =
      ((smallEtaleComparisonRestriction B S hS Y).inv.obj
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).obj.obj W :=
  rfl

/-- **Restricting back recovers the module.**  The abelian sheaf
`AlgebraicGeometry.Space.moduleSpacesAbelianSheaf`, restricted along the comparison functor of
Stacks 03G1, is the abelian sheaf underlying the module.  It is
`Stacks.Sheaves.ToposPullback.pullbackModuleSectionToSheafIso` at the counit of the comparison
equivalence. -/
def moduleSpacesAbelianSheafRestrictionIso (Y : AlgebraicSpaces B S hS) :
    moduleSpacesAbelianSheaf B S hS Y ⋙
        (comparisonFunctor B S hS Y).sheafPushforwardContinuous AddCommGrpCat.{u}
          (SmallEtale.topology B S hS Y.1) (SpacesEtale.topology B S hS Y) ≅
      SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS Y) :=
  pullbackModuleSectionToSheafIso (SmallEtale.topology B S hS Y.1)
    (SpacesEtale.topology B S hS Y) (comparisonFunctor B S hS Y) (structureRingSheaf B S hS Y)
    (smallEtaleComparisonRestriction B S hS Y).inv
    (smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso

/-- On underlying sheaves of sets,
`AlgebraicGeometry.Space.moduleSpacesAbelianSheafRestrictionIso` is the counit of the comparison
equivalence of sheaves of sets. -/
theorem sheafCompose_map_moduleSpacesAbelianSheafRestrictionIso_hom_app
    (Y : AlgebraicSpaces B S hS) (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (sheafCompose (SmallEtale.topology B S hS Y.1) (forget AddCommGrpCat.{u})).map
        ((moduleSpacesAbelianSheafRestrictionIso B S hS Y).hom.app M) =
      (smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.hom.app
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M) :=
  sheafCompose_map_hom_app_of_eq_pullbackModuleSectionToSheafIso (SmallEtale.topology B S hS Y.1)
    (SpacesEtale.topology B S hS Y) (comparisonFunctor B S hS Y) (structureRingSheaf B S hS Y)
    (smallEtaleComparisonRestriction B S hS Y).inv
    (smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso
    (moduleSpacesAbelianSheafRestrictionIso B S hS Y) rfl M

/-- **On sections, restricting back is the counit of the comparison equivalence.**  A section of
`AlgebraicGeometry.Space.moduleSpacesAbelianSheaf` over the image of an étale chart `W` of `Y` is
sent by `AlgebraicGeometry.Space.moduleSpacesAbelianSheafRestrictionIso` to its image under the
counit of the comparison equivalence of sheaves of sets, at the sheaf of sets underlying the
module. -/
lemma moduleSpacesAbelianSheafRestrictionIso_hom_app_apply (Y : AlgebraicSpaces B S hS)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (W : SmallEtale B S hS Y.1)
    (x : ((moduleSpacesAbelianSheaf B S hS Y).obj M).obj.obj
      (Opposite.op ((comparisonFunctor B S hS Y).obj W))) :
    ((moduleSpacesAbelianSheafRestrictionIso B S hS Y).hom.app M).hom.app (Opposite.op W) x =
      ((smallEtaleComparisonRestriction B S hS Y).asEquivalence.counitIso.hom.app
        (Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS Y) M)).hom.app
          (Opposite.op W) x :=
  congrArg (fun m ↦ m.hom.app (Opposite.op W) x)
    (sheafCompose_map_moduleSpacesAbelianSheafRestrictionIso_hom_app B S hS Y M)

/-- **The abelian sheaf underlying a direct image, one step in.**  For `f : Y ⟶ X`, the abelian
sheaf underlying the direct image `f_*M` of Stacks 03LU is the abelian sheaf
`AlgebraicGeometry.Space.moduleSpacesAbelianSheaf` of `M`, restricted along spaces-étale base
change (the direct image of Stacks 03G2, part (1)) and then along the comparison functor of
Stacks 03G1 for `X`.

This is `AlgebraicGeometry.Space.modulePushforwardOfStructureMapCompToSheafIso` stopped before
its last factor: the inverse of the comparison equivalence for `Y` is not traded for the inverse
of the abelian equivalence but kept inside `AlgebraicGeometry.Space.moduleSpacesAbelianSheaf`. -/
def modulePushforwardSpacesAbelianSheafIso {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) :
    modulePushforward B S hS f ⋙ SheafOfModules.toSheaf.{u} (structureRingSheaf B S hS X) ≅
      moduleSpacesAbelianSheaf B S hS Y ⋙
        (spacesBaseChange B S hS f).functor.sheafPushforwardContinuous AddCommGrpCat.{u}
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y) ⋙
        (comparisonFunctor B S hS X).sheafPushforwardContinuous AddCommGrpCat.{u}
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X) :=
  pullbackModuleRestrictScalarsToSheafIsoComp (SmallEtale.topology B S hS X.1)
    (SpacesEtale.topology B S hS Y)
    ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y) ⋙
      smallEtaleComparisonRestriction B S hS X)
    (smallEtaleComparisonRestriction B S hS Y).inv
    ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous AddCommGrpCat.{u}
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y) ⋙
        (comparisonFunctor B S hS X).sheafPushforwardContinuous AddCommGrpCat.{u}
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X))
    (spacesBaseChangeComparisonCompToSheafIso B S hS f) (structureRingSheaf B S hS Y)
    (structureSharp B S hS f)

/-- The compatibility `AlgebraicGeometry.Space.spacesBaseChangeComparisonCompToSheafIso` for the
two restriction factors of the direct image is the identity on underlying sheaves of sets. -/
theorem sheafCompose_map_spacesBaseChangeComparisonCompToSheafIso_hom_app
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (O : Sheaf (SpacesEtale.topology B S hS Y) RingCat.{u})
    (N : SheafOfModules.{u} O) :
    (sheafCompose (SmallEtale.topology B S hS X.1) (forget AddCommGrpCat.{u})).map
        ((spacesBaseChangeComparisonCompToSheafIso B S hS f O).hom.app N) =
      𝟙 _ := by
  refine (sheafCompose_map_hom_app_of_eq_pullbackModuleToSheafIsoComp
    (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)
    (smallEtaleComparisonRestriction B S hS X)
    ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y))
    ((comparisonFunctor B S hS X).sheafPushforwardContinuous AddCommGrpCat.{u}
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X))
    ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous AddCommGrpCat.{u}
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y))
    (comparisonRestrictionCompToSheafIso B S hS) (spacesBaseChangeCompToSheafIso B S hS f) O
    (spacesBaseChangeComparisonCompToSheafIso B S hS f O) rfl N).trans ?_
  have e1 := sheafCompose_map_hom_app_of_eq_pullbackModuleCompToSheafIso
      (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)
      (comparisonFunctor B S hS X)
      (pullbackRingSheaf.{u, u, u + 1, u + 1, u + 1, u + 1} (SpacesEtale.topology B S hS X)
        ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)) O)
      (smallEtaleComparisonRestriction B S hS X) (Iso.refl _)
      (comparisonRestrictionCompToSheafIso B S hS _) rfl
      ((pullbackModuleFunctor.{u, u, u + 1, u + 1, u + 1, u + 1} (SpacesEtale.topology B S hS X)
        ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)) O).obj N)
  have e2 := sheafCompose_map_sheafPushforwardContinuous_map (SmallEtale.topology B S hS X.1)
      (SpacesEtale.topology B S hS X) (comparisonFunctor B S hS X)
      ((spacesBaseChangeCompToSheafIso B S hS f O).hom.app N)
  have e3 := sheafCompose_map_hom_app_of_eq_pullbackModuleCompToSheafIso
        (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)
        (spacesBaseChange B S hS f).functor O
        ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y)) (Iso.refl _)
        (spacesBaseChangeCompToSheafIso B S hS f O) rfl N
  have e4 := e2.trans (congrArg (smallEtaleComparisonRestriction B S hS X).map e3)
  have e5 := congrArg₂ (· ≫ ·) e1 e4
  refine e5.trans ?_
  exact (Category.id_comp _).trans (CategoryTheory.Functor.map_id _ _)

/-- On underlying sheaves of sets,
`AlgebraicGeometry.Space.modulePushforwardSpacesAbelianSheafIso` is
`AlgebraicGeometry.Space.spacesBaseChangeComparisonCompToSheafIso` at the transported module: the
restriction of scalars along `f♯` and the comparison of iterated inverse images are the identity
on sections. -/
theorem sheafCompose_map_modulePushforwardSpacesAbelianSheafIso_hom_app_eq
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (sheafCompose (SmallEtale.topology B S hS X.1) (forget AddCommGrpCat.{u})).map
        ((modulePushforwardSpacesAbelianSheafIso B S hS f).hom.app M) =
      (sheafCompose (SmallEtale.topology B S hS X.1) (forget AddCommGrpCat.{u})).map
        ((spacesBaseChangeComparisonCompToSheafIso B S hS f
          (pullbackRingSheaf.{u, u, u + 1, u + 1, u, u + 1} (SpacesEtale.topology B S hS Y)
            (smallEtaleComparisonRestriction B S hS Y).inv (structureRingSheaf B S hS Y))).hom.app
          ((pullbackModuleFunctor.{u, u, u + 1, u + 1, u, u + 1} (SpacesEtale.topology B S hS Y)
            (smallEtaleComparisonRestriction B S hS Y).inv (structureRingSheaf B S hS Y)).obj M)) :=
  sheafCompose_map_hom_app_of_eq_pullbackModuleRestrictScalarsToSheafIsoComp
    (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS Y)
    ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous (Type u)
        (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y) ⋙
      smallEtaleComparisonRestriction B S hS X)
    (smallEtaleComparisonRestriction B S hS Y).inv
    ((spacesBaseChange B S hS f).functor.sheafPushforwardContinuous AddCommGrpCat.{u}
          (SpacesEtale.topology B S hS X) (SpacesEtale.topology B S hS Y) ⋙
        (comparisonFunctor B S hS X).sheafPushforwardContinuous AddCommGrpCat.{u}
          (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X))
    (spacesBaseChangeComparisonCompToSheafIso B S hS f) (structureRingSheaf B S hS Y)
    (structureSharp B S hS f) (modulePushforwardSpacesAbelianSheafIso B S hS f) rfl M

/-- `AlgebraicGeometry.Space.modulePushforwardSpacesAbelianSheafIso` is the identity on
underlying sheaves of sets. -/
theorem sheafCompose_map_modulePushforwardSpacesAbelianSheafIso_hom_app
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (sheafCompose (SmallEtale.topology B S hS X.1) (forget AddCommGrpCat.{u})).map
        ((modulePushforwardSpacesAbelianSheafIso B S hS f).hom.app M) = 𝟙 _ :=
  (sheafCompose_map_modulePushforwardSpacesAbelianSheafIso_hom_app_eq B S hS f M).trans
    (sheafCompose_map_spacesBaseChangeComparisonCompToSheafIso_hom_app B S hS f _ _)

/-- **On sections, the direct image comparison is the identity.**  A section of `f_*M` over an
étale chart `U` of `X` is sent by `AlgebraicGeometry.Space.modulePushforwardSpacesAbelianSheafIso`
to itself, read as a section of `AlgebraicGeometry.Space.moduleSpacesAbelianSheaf` over the base
change of `U`. -/
lemma modulePushforwardSpacesAbelianSheafIso_hom_app_apply
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (U : SmallEtale B S hS X.1)
    (t : ((modulePushforward B S hS f).obj M).val.obj (Opposite.op U)) :
    ((modulePushforwardSpacesAbelianSheafIso B S hS f).hom.app M).hom.app (Opposite.op U) t = t :=
  congrArg (fun m ↦ m.hom.app (Opposite.op U) t)
    (sheafCompose_map_modulePushforwardSpacesAbelianSheafIso_hom_app B S hS f M)

end AlgebraicGeometry.Space

end
