module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullOnFree
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.QuasiCompactObjects
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasiCompactCoproductSections
public import StacksFrontier.CategoryTheory.Sites.QuasiCompact.ModuleSections

/-!
# The unit of the associated-module adjunction at a free module

`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullOnFree` reduces
`AlgebraicGeometry.BigFppfOver.IsFullOnFree`, the one input of Stacks 03DX (1) that
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EssentialImage` leaves as a hypothesis,
to surjectivity of the unit `𝓕 ⟶ (𝓕^a)|_{S_Zar}` on global sections at every free `𝒪_S`-module.
This file proves that surjectivity — indeed bijectivity — when `S` is quasi-compact.

The argument is the one Stacks gives for 03DX, read through Stacks 0935.  Write `T` for a
terminal object of the source site and `F` for the underlying functor of sites.  Global sections
of a sheaf of modules on a site with a terminal object are its sections at that object
(`Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal`), so the map in question is the
value at `T` of the morphism

`free I ⟶ (pushforward φ).obj (free I)`

obtained from the unit at `free I` followed by the identification of the pullback of a free
module with a free module.  That morphism carries the `i`-th inclusion `𝒪 ⟶ ⊕_I 𝒪` upstairs to
the `i`-th inclusion downstairs, composed with the comparison of structure sheaves
(`SheafOfModules.ιFree_comp_unit_app_free_comp` below).  So at `T` it is a morphism between two
cofans of copies of the same abelian group, and when `T` and `F.obj T` are quasi-compact objects
of their sites both cofans are colimiting by Stacks 0935 — whence the morphism is an
isomorphism, the comparison of structure sheaves at `T` being one.

## Main results

* `SheafOfModules.ιFree_comp_unit_app_free_comp`: the unit at `free I`, followed by the
  identification of the pullback of a free module with a free module, carries the `i`-th
  inclusion of `free I` to the comparison of structure sheaves followed by the pushforward of
  the `i`-th inclusion.
* `SheafOfModules.isIso_toSheaf_map_unit_app_free_app`: the same statement at an *arbitrary*
  quasi-compact object of the source site, in the form of an isomorphism on sections there.
  This is what applies at each member of a basis of opens of a scheme.
* `SheafOfModules.bijective_sectionsMap_unit_free`: the unit of the pullback–pushforward
  adjunction at a free module is bijective on global sections, provided the source site has a
  terminal object which is quasi-compact there and whose image is quasi-compact downstairs, and
  the comparison of structure sheaves is an isomorphism at that object.
* `AlgebraicGeometry.BigFppfOver.isFullOnFree_of_compactSpace`:
  `AlgebraicGeometry.BigFppfOver.IsFullOnFree` holds for a quasi-compact `S`.
* `AlgebraicGeometry.BigFppfOver`
  `.exists_isQuasicoherent_iso_associatedModule_of_cokernelFree_of_compactSpace`: the local step
  of the essential surjectivity half of Stacks 03DX (1), for `τ = fppf` and quasi-compact `S`,
  with no remaining hypothesis.

## Implementation notes

Quasi-compactness of `S` is used twice and is not removable from this argument: it is what makes
the global sections of `⊕_I 𝒪` the direct sum of `I` copies of the global functions, on both
sites at once.  For a general `S` the two sides are still equal — the restriction of the big
sheaf to the small Zariski site is a Zariski sheaf agreeing with `⊕_I 𝒪_S` on every affine open —
but exhibiting that needs a local-on-the-base comparison which is not developed here.  So
`AlgebraicGeometry.BigFppfOver.IsFullOnFree` is discharged only under `CompactSpace ↥S`, and
`AlgebraicGeometry.BigFppfOver.exists_isQuasicoherent_iso_associatedModule_of_cokernelFree`
keeps its hypothesis.

Nothing here is tagged.  The statement of Stacks 03DX (1) is an equivalence of categories, of
which this supplies one input to one half: full faithfulness is Stacks 0GN7 and the
globalization of the local step is the appeal to the effectivity of descent, Stacks 023T.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0GN7](https://stacks.math.columbia.edu/tag/0GN7)
* [Stacks Project, Tag 0935](https://stacks.math.columbia.edu/tag/0935)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂ u

/-- A morphism between the points of two colimiting cofans of constant diagrams which is
compatible with the inclusions through an isomorphism of the diagrams is an isomorphism. -/
private theorem CategoryTheory.Limits.isIso_of_isColimit_cofan {A : Type u₁} [Category.{v₁} A]
    {I : Type u} {X Y : A} {c : Cofan (fun _ : I => X)} {d : Cofan (fun _ : I => Y)}
    (hc : IsColimit c) (hd : IsColimit d) (g : X ⟶ Y) [IsIso g] (f : c.pt ⟶ d.pt)
    (hf : ∀ i, c.inj i ≫ f = g ≫ d.inj i) : IsIso f := by
  refine ⟨Cofan.IsColimit.desc hd (fun i => inv g ≫ c.inj i), ?_, ?_⟩
  · exact Cofan.IsColimit.hom_ext hc _ _ fun i => by
      rw [Category.comp_id, ← Category.assoc, hf i, Category.assoc,
        Cofan.IsColimit.fac hd, IsIso.hom_inv_id_assoc]
  · exact Cofan.IsColimit.hom_ext hd _ _ fun i => by
      rw [Category.comp_id, ← Category.assoc, Cofan.IsColimit.fac hd, Category.assoc, hf i,
        IsIso.inv_hom_id_assoc]

namespace SheafOfModules

section SectionsAt

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- The abelian group of sections of a sheaf of modules at an object of the site, as a functor.
This is the functor Stacks 0935 is about. -/
private noncomputable abbrev sectionsAt (R : Sheaf J RingCat.{u}) (T : C) :
    SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
  toSheaf.{u} R ⋙ (sheafSections J AddCommGrpCat.{u}).obj (op T)

/-- Global sections at a terminal object are natural in the sheaf of modules. -/
private theorem sectionsEquivOfTerminal_sectionsMap {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R} {T : C} (hT : IsTerminal T) (f : M ⟶ N) (s : M.sections) :
    Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal N hT (sectionsMap f s)
      = (sectionsAt R T).map f
        (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M hT s) := rfl

/-- A morphism of sheaves of modules is bijective on global sections as soon as it is bijective
on sections at a terminal object. -/
private theorem bijective_sectionsMap_of_bijective_map {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R} {T : C} (hT : IsTerminal T) (f : M ⟶ N)
    (hf : Function.Bijective ((sectionsAt R T).map f)) :
    Function.Bijective (sectionsMap f) := by
  have h : ⇑(Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal N hT) ∘
        (sectionsMap f)
      = ⇑((sectionsAt R T).map f) ∘
        ⇑(Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M hT) :=
    funext fun s => sectionsEquivOfTerminal_sectionsMap hT f s
  have h2 : Function.Bijective
      (⇑(Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal N hT) ∘
        (sectionsMap f)) := by
    rw [h]
    exact hf.comp
      (Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal M hT).bijective
  exact (Equiv.comp_bijective _ _).mp h2

/-- A functor out of sheaves of modules preserving coproducts sends the cofan of inclusions of a
free module to a colimit cofan. -/
private noncomputable def isColimitCofanMapFree {R : Sheaf J RingCat.{u}}
    (E : SheafOfModules.{u} R ⥤ AddCommGrpCat.{u}) (I : Type u)
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [PreservesColimitsOfShape (Discrete I) E] :
    IsColimit (Cofan.mk (E.obj (free (R := R) I)) fun i => E.map (ιFree i)) :=
  (Cofan.isColimitMapCoconeEquiv E _ (freeCofan I)) (isColimitOfPreserves E (isColimitFreeCofan I))

/-- An isomorphism of sheaves of modules is bijective on global sections. -/
private theorem bijective_sectionsMap_of_isIso {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R} (u : M ⟶ N) (hu : IsIso u) :
    Function.Bijective (sectionsMap u) :=
  let := hu
  ⟨Function.LeftInverse.injective (g := sectionsMap (inv u)) fun s => by
      rw [← sectionsMap_comp, IsIso.hom_inv_id, sectionsMap_id],
    surjective_sectionsMap_of_isIso u hu⟩

end SectionsAt

section Unit

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  [(SheafOfModules.pushforward.{u} φ).IsRightAdjoint]
  [HasWeakSheafify J AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [F.Final]

/-- **The unit at a free module, summand by summand.**  Composing the unit of the
pullback–pushforward adjunction at `free I` with the pushforward of the identification of the
pullback of `free I` with `free I` gives a morphism `free I ⟶ (pushforward φ).obj (free I)`
which carries the `i`-th inclusion of `free I` to the comparison of structure sheaves followed
by the pushforward of the `i`-th inclusion. -/
public theorem ιFree_comp_unit_app_free_comp (I : Type u) (i : I) :
    ιFree i ≫ (pullbackPushforwardAdjunction.{u} φ).unit.app (free (R := S) I) ≫
        (pushforward.{u} φ).map (pullbackObjFreeIso φ I).hom
      = unitToPushforwardObjUnit φ ≫ (pushforward.{u} φ).map (ιFree i) := by
  have hnat := (pullbackPushforwardAdjunction.{u} φ).unit.naturality
    (ιFree (R := S) (I := I) i)
  simp only [Functor.id_map, Functor.comp_map] at hnat
  rw [← Category.assoc, hnat, Category.assoc, ← Functor.map_comp,
    pullback_map_ιFree_comp_pullbackObjFreeIso_hom φ i, Functor.map_comp, ← Category.assoc]
  congr 1
  rw [← pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit φ,
    Adjunction.homEquiv_unit]

/-- **Stacks 0935, applied to the unit at a free module.**  At a terminal object `T` of the
source site which is a quasi-compact object there and whose image is a quasi-compact object
downstairs, the unit at `free I` followed by the identification of the pullback of a free module
with a free module is an isomorphism on sections, provided the comparison of structure sheaves is
an isomorphism at `T`.

Both sides are cofans of `I` copies of the sections of the structure sheaf at `T`, colimiting by
Stacks 0935, and the morphism between them is a morphism of cofans by
`SheafOfModules.ιFree_comp_unit_app_free_comp`. -/
private theorem isIso_sectionsAt_map_unit_app_free_comp (T : C)
    (hTqc : J.IsQuasiCompactObject T) (hFT : K.IsQuasiCompactObject (F.obj T))
    (hφ : IsIso (φ.hom.app (op T))) (I : Type u) :
    IsIso ((sectionsAt S T).map
      ((pullbackPushforwardAdjunction.{u} φ).unit.app (free (R := S) I) ≫
        (pushforward.{u} φ).map (pullbackObjFreeIso φ I).hom)) := by
  have hE : PreservesColimitsOfShape (Discrete I) (sectionsAt S T) :=
    Stacks.Sites.sheafOfModules_sections_preserves_coproducts J S T hTqc I
  have hG : PreservesColimitsOfShape (Discrete I) (pushforward.{u} φ ⋙ sectionsAt S T) :=
    Stacks.Sites.sheafOfModules_sections_preserves_coproducts K R (F.obj T) hFT I
  have hiso : IsIso ((sectionsAt S T).map (unitToPushforwardObjUnit φ)) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ConcreteCategory.bijective_of_isIso (φ.hom.app (op T))
  have key : ∀ i : I, (sectionsAt S T).map (ιFree (R := S) (I := I) i) ≫
      (sectionsAt S T).map
        ((pullbackPushforwardAdjunction.{u} φ).unit.app (free (R := S) I) ≫
          (pushforward.{u} φ).map (pullbackObjFreeIso φ I).hom)
      = (sectionsAt S T).map (unitToPushforwardObjUnit φ) ≫
        (pushforward.{u} φ ⋙ sectionsAt S T).map (ιFree (R := R) (I := I) i) := by
    intro i
    rw [← Functor.map_comp, ιFree_comp_unit_app_free_comp φ I i]
    exact (sectionsAt S T).map_comp _ _
  exact isIso_of_isColimit_cofan (isColimitCofanMapFree (sectionsAt S T) I)
    (isColimitCofanMapFree (pushforward.{u} φ ⋙ sectionsAt S T) I)
    ((sectionsAt S T).map (unitToPushforwardObjUnit φ)) _ key

/-- **The unit of the pullback–pushforward adjunction is an isomorphism on sections at a
quasi-compact object, at a free module.**  No terminal object is involved: `T` is an arbitrary
object of the source site which is quasi-compact there, whose image is quasi-compact downstairs
and at which the comparison of structure sheaves is an isomorphism.

This is the form in which the argument applies at every member of a basis of opens of a scheme,
which is what makes the conclusion local on the base rather than a statement about global
sections only. -/
public theorem isIso_toSheaf_map_unit_app_free_app (T : C)
    (hTqc : J.IsQuasiCompactObject T) (hFT : K.IsQuasiCompactObject (F.obj T))
    (hφ : IsIso (φ.hom.app (op T))) (I : Type u) :
    IsIso ((((toSheaf.{u} S).map
      ((pullbackPushforwardAdjunction.{u} φ).unit.app (free (R := S) I))).hom.app (op T))) := by
  have hb : IsIso ((sectionsAt S T).map
      ((pushforward.{u} φ).map (pullbackObjFreeIso φ I).hom)) :=
    Functor.map_isIso _ _
  have hcomp : IsIso ((((toSheaf.{u} S).map
      ((pullbackPushforwardAdjunction.{u} φ).unit.app (free (R := S) I))).hom.app (op T)) ≫
      (sectionsAt S T).map ((pushforward.{u} φ).map (pullbackObjFreeIso φ I).hom)) := by
    have h := isIso_sectionsAt_map_unit_app_free_comp φ T hTqc hFT hφ I
    rw [Functor.map_comp] at h
    exact h
  exact IsIso.of_isIso_comp_right _ ((sectionsAt S T).map
    ((pushforward.{u} φ).map (pullbackObjFreeIso φ I).hom))

/-- **The unit of the pullback–pushforward adjunction is bijective on global sections at a free
module.**  The source site is assumed to have a terminal object which is a quasi-compact object
there and whose image is a quasi-compact object downstairs, and the comparison of structure
sheaves is assumed to be an isomorphism at that object. -/
public theorem bijective_sectionsMap_unit_free (T : C) (hT : IsTerminal T)
    (hTqc : J.IsQuasiCompactObject T) (hFT : K.IsQuasiCompactObject (F.obj T))
    (hφ : IsIso (φ.hom.app (op T))) (I : Type u) :
    Function.Bijective (sectionsMap
      ((pullbackPushforwardAdjunction.{u} φ).unit.app (free (R := S) I))) := by
  have h : Function.Bijective (sectionsMap
      ((pullbackPushforwardAdjunction.{u} φ).unit.app (free (R := S) I) ≫
        (pushforward.{u} φ).map (pullbackObjFreeIso φ I).hom)) := by
    have := isIso_sectionsAt_map_unit_app_free_comp φ T hTqc hFT hφ I
    exact bijective_sectionsMap_of_bijective_map hT _
      (ConcreteCategory.bijective_of_isIso _)
  have hmap : Function.Bijective (sectionsMap
      ((pushforward.{u} φ).map (pullbackObjFreeIso φ I).hom)) :=
    bijective_sectionsMap_of_isIso _ (Functor.map_isIso _ _)
  exact (hmap.of_comp_iff' _).mp h

end Unit

end SheafOfModules

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison of structure sheaves along the inclusion of the small Zariski site of `S` is
an isomorphism at every open of `S`: over `U` it is the identification of the sections of `𝒪_S`
over `U` with the global functions of the open subscheme `U`. -/
public theorem isIso_structureMap_hom_app (U : (S.Opens)ᵒᵖ) :
    IsIso ((structureMap B S hS).hom.app U) := by
  rw [structureMap_hom_app]
  exact Functor.map_isIso _ _

/-- The top open of a quasi-compact `S`, as an object of the big fppf site of `S`, is a
quasi-compact object of that site. -/
public theorem isQuasiCompactObject_opensToBig_top (hcomp : CompactSpace S) :
    (topology B S hS).IsQuasiCompactObject ((opensToBig B S hS).obj ⊤) := by
  have := hcomp
  exact isQuasiCompactObject_of_compactSpace B S hS _
    (isCompact_iff_compactSpace.mp (by simpa using isCompact_univ (X := ↥S)))

/-- The top open of a quasi-compact scheme is a quasi-compact object of its small Zariski
site. -/
public theorem _root_.AlgebraicGeometry.Scheme.isQuasiCompactObject_top (X : Scheme.{u})
    (hcomp : CompactSpace X) :
    (Opens.grothendieckTopology ↥X).IsQuasiCompactObject (⊤ : X.Opens) := by
  have := hcomp
  exact Stacks.SheafOfModules.isQuasiCompactObject_of_isCompact (X := TopCat.of ↥X) ⊤
    (by simpa using isCompact_univ (X := ↥X))

/-- **The unit of the associated-module adjunction is bijective on global sections at a free
module, for quasi-compact `S`.**  This is the statement
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullOnFree` reduces
`AlgebraicGeometry.BigFppfOver.IsFullOnFree` to. -/
public theorem bijective_sectionsMap_unit_free (hcomp : CompactSpace S) (I : Type u) :
    Function.Bijective (SheafOfModules.sectionsMap
      ((associatedModuleAdjunction B S hS).unit.app
        (SheafOfModules.free (R := S.ringCatSheaf) I))) :=
  SheafOfModules.bijective_sectionsMap_unit_free (structureMap B S hS) ⊤ isTerminalTop
    (Scheme.isQuasiCompactObject_top S hcomp)
    (isQuasiCompactObject_opensToBig_top B S hS hcomp)
    (isIso_structureMap_hom_app B S hS (op ⊤)) I

/-- **Fullness of `𝓕 ↦ 𝓕^a` on free modules, for quasi-compact `S`.**  Every morphism between
the associated modules of two free `𝒪_S`-modules is the associated morphism of a morphism of
free `𝒪_S`-modules.  This is the restriction to free modules of Stacks 0GN7, and the input of
Stacks 03DX (1) that
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EssentialImage` leaves open. -/
public theorem isFullOnFree_of_compactSpace (hcomp : CompactSpace S) : IsFullOnFree B S hS :=
  isFullOnFree_of_surjective_sectionsMap_unit B S hS
    fun I => (bijective_sectionsMap_unit_free B S hS hcomp I).2

/-- **Stacks 03DX (1), essential surjectivity, local step, for `τ = fppf` and quasi-compact
`S`.**  A sheaf of modules on the big fppf site of a quasi-compact `S` presented as a cokernel
`⊕_{i ∈ I₂} 𝒪 ⟶ ⊕_{i ∈ I₁} 𝒪 ⟶ 𝒢 ⟶ 0` is the associated module of a quasi-coherent
`𝒪_S`-module.  This is
`AlgebraicGeometry.BigFppfOver.exists_isQuasicoherent_iso_associatedModule_of_cokernelFree` with
its hypothesis discharged. -/
public theorem exists_isQuasicoherent_iso_associatedModule_of_cokernelFree_of_compactSpace
    (hcomp : CompactSpace S) {I₁ I₂ : Type u}
    (α : SheafOfModules.free (R := structureSheaf B S hS) I₂ ⟶ SheafOfModules.free I₁)
    {G : SheafOfModules.{u} (structureSheaf B S hS)}
    {π : SheafOfModules.free (R := structureSheaf B S hS) I₁ ⟶ G} (hπ : α ≫ π = 0)
    (hc : IsColimit (CokernelCofork.ofπ π hπ)) :
    ∃ G' : S.Modules, G'.IsQuasicoherent ∧
      Nonempty ((associatedModule B S hS).obj G' ≅ G) :=
  exists_isQuasicoherent_iso_associatedModule_of_cokernelFree B S hS
    (isFullOnFree_of_compactSpace B S hS hcomp) α hπ hc

end AlgebraicGeometry.BigFppfOver

end
