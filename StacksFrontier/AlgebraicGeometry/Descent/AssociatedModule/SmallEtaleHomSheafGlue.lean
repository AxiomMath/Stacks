module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomSections
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleEssentialImage

/-!
# Gluing morphisms of modules on the small étale site out of the internal hom

Stacks 03EM says that the internal hom `𝓗om_𝒪(𝓕, 𝒢)` of a sheaf of modules is again a sheaf.  On
a site whose objects cover the final object this turns into a gluing principle: a compatible
family of local morphisms `𝓕|_{X i} ⟶ 𝒢|_{X i}` extends uniquely to `𝓕 ⟶ 𝒢`, and a compatible
family of local isomorphisms is an isomorphism.  **This file supplies that principle on the small
étale site of a scheme**, and reads off from it the last paragraph of the proof of
Stacks 03DX (2) at `τ = étale`: a quasi-coherent `𝒪_S`-module `𝓕` together with isomorphisms
`𝓕^a|_{X i} ≅ 𝒢|_{X i}` agreeing over the products `X i × X j` exhibits `𝒢` as an `𝓕^a`.

Compatibility is Mathlib's `CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible`, which
quantifies over every object mapping into two members of the family; the source of Stacks 03DX
instead checks the agreement over the fibre products `X i ×_S X j`, which on the small étale site
are the binary products of the site, every object of it being étale over `S`.  The two conditions
agree because every pair of morphisms into two members factors through their product.

## Main definitions

* `AlgebraicGeometry.SmallEtale.commStructurePresheaf`: the structure sheaf of the small étale
  site of `S`, valued in commutative rings.
* `AlgebraicGeometry.SmallEtale.homPresheaf` and `AlgebraicGeometry.SmallEtale.sheafHom`: the
  internal hom of Stacks 04TT on the small étale site, and its sheaf form.

## Main results

* `AlgebraicGeometry.SmallEtale.homPresheaf_isSheaf`: **Stacks 03EM on the small étale site.**
* `AlgebraicGeometry.SmallEtale.existsUnique_hom_of_isCompatible` and
  `AlgebraicGeometry.SmallEtale.exists_iso_of_isCompatible`: local morphisms, respectively local
  isomorphisms, on a family covering the final object glue.
* `AlgebraicGeometry.SmallEtale.isCompatible_of_forall_memberProd`: a family of local morphisms
  agreeing over the products of two members is a compatible family.
* `AlgebraicGeometry.SmallEtale.isIso_of_forall_isIso_restrFun`: a morphism of sheaves of modules
  on `S_étale` whose restrictions to the members of a family covering the final object are
  isomorphisms is an isomorphism.
* `AlgebraicGeometry.SmallEtale.essImage_associatedModule_of_isCompatible` and
  `AlgebraicGeometry.SmallEtale.essImage_associatedModule_of_forall_memberProd`: **the
  Stacks 03EM step of Stacks 03DX (2) at `τ = étale`**, with no hypothesis.

## Implementation notes

Nothing here carries a `stacks` attribute.  Stacks 03EM is tagged on the general-site statement
`internalHom_isSheaf`, which is what is instantiated below, and the statements about Stacks 03DX
are a step of its proof and not a clause of it: essential surjectivity of `𝓕 ↦ 𝓕^a` still needs
the quasi-coherent `𝓕` and the local isomorphisms to be produced, which is where descent enters.

The commutative-ring-valued structure presheaf is spelled so that forgetting commutativity
returns `AlgebraicGeometry.SmallEtale.structureSheaf` on the nose, `oforget_commStructurePresheaf`
being `rfl`; `AlgebraicGeometry.SmallEtale.commRingStructurePresheaf` of the étale-cohomology
development is the same presheaf written through `AlgebraicGeometry.SmallEtale.toScheme`, for
which that identification needs a rewriting step and no module could be transported for free.

The module universe of the internal hom is `u + 1`: its sections over an object are the morphisms
on the localization of the site there, and those are indexed by the objects of the small étale
site, which form a `Type (u + 1)`.

## References

* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
* [Stacks Project, Tag 04TT](https://stacks.math.columbia.edu/tag/04TT)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The internal hom on the small étale site -/

/-- **The structure sheaf of the small étale site of `S`, valued in commutative rings.**  An
object is sent to the ring of global functions on its underlying scheme. -/
public noncomputable abbrev commStructurePresheaf : (SmallEtale B S hS)ᵒᵖ ⥤ CommRingCat.{u} :=
  ((inclusion B S hS ⋙ Over.post B.inclusion) ⋙ Over.forget S).op ⋙ Scheme.Γ

/-- Forgetting commutativity returns the structure sheaf of the small étale site on the nose, so
a module over the one is a module over the other with no comparison map. -/
public theorem oforget_commStructurePresheaf :
    Oforget (commStructurePresheaf B S hS) = (structureSheaf B S hS).obj := rfl

/-- **The internal hom `𝓗om_𝒪(F, G)` on the small étale site of `S`** (Stacks 04TT): the presheaf
whose sections over `T` are the `𝒪|_T`-linear maps `F|_T ⟶ G|_T` on the localization at `T`. -/
public noncomputable abbrev homPresheaf
    (F G : PresheafOfModules.{u} (structureSheaf B S hS).obj) :
    PresheafOfModules.{u + 1} (structureSheaf B S hS).obj :=
  internalHom (commStructurePresheaf B S hS) F G

/-- **Stacks 03EM on the small étale site of a scheme.**  For a presheaf of modules `F` and a
*sheaf* of modules `G` on `S_étale`, the internal hom `𝓗om_𝒪(F, G)` is a sheaf. -/
public theorem homPresheaf_isSheaf (F : PresheafOfModules.{u} (structureSheaf B S hS).obj)
    (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    Presheaf.IsSheaf (topology B S hS) (homPresheaf B S hS F G.val).presheaf :=
  internalHom_isSheaf (commStructurePresheaf B S hS) F G.val G.isSheaf

/-- **`SheafHom(F, G)` on the small étale site of `S`**, as a sheaf of modules.  Its module
universe is one above that of `F` and `G`; see the module docstring. -/
public noncomputable def sheafHom (F G : SheafOfModules.{u} (structureSheaf B S hS)) :
    SheafOfModules.{u + 1} (structureSheaf B S hS) where
  val := homPresheaf B S hS F.val G.val
  isSheaf := homPresheaf_isSheaf B S hS F.val G

/-- Stacks 03EM on the small étale site, read on the underlying presheaf of types of sections.
This is the shape the gluing statements consume. -/
public theorem homPresheaf_isSheaf_forget
    (F : PresheafOfModules.{u} (structureSheaf B S hS).obj)
    (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    Presheaf.IsSheaf (topology B S hS)
      ((homPresheaf B S hS F G.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
  Presheaf.isSheaf_comp_of_isSheaf _ _ _ (homPresheaf_isSheaf B S hS F G)

/-! ### Gluing local morphisms and local isomorphisms -/

/-- **Morphisms into a sheaf of modules glue over a family covering the final object of
`S_étale`.**  Local morphisms `α i : F|_{X i} ⟶ G|_{X i}` agreeing after relocalization to any
common refinement come from a unique morphism `F ⟶ G`. -/
public theorem existsUnique_hom_of_isCompatible
    (F : PresheafOfModules.{u} (structureSheaf B S hS).obj)
    (G : SheafOfModules.{u} (structureSheaf B S hS))
    {I : Type w} {X : I → SmallEtale B S hS} (hX : (topology B S hS).CoversTop X)
    {α : Presheaf.FamilyOfElementsOnObjects
      ((homPresheaf B S hS F G.val).presheaf ⋙ CategoryTheory.forget _) X}
    (hα : α.IsCompatible) :
    ∃! φ : F ⟶ G.val,
      ∀ i, (restrFun (commStructurePresheaf B S hS) (X i)).map φ = α i :=
  _root_.existsUnique_hom_of_isCompatible (commStructurePresheaf B S hS) F G.val hX
    (homPresheaf_isSheaf_forget B S hS F G) hα

/-- **Local isomorphisms glue to an isomorphism of sheaves of modules on `S_étale`.**  This is the
sentence "the sheaf property of `SheafHom` assembles the local isomorphisms into a global one" of
the proof of Stacks 03DX, on the small étale site. -/
public theorem exists_iso_of_isCompatible (F G : SheafOfModules.{u} (structureSheaf B S hS))
    {I : Type w} {X : I → SmallEtale B S hS} (hX : (topology B S hS).CoversTop X)
    (e : ∀ i, (restrFun (commStructurePresheaf B S hS) (X i)).obj F.val ≅
      (restrFun (commStructurePresheaf B S hS) (X i)).obj G.val)
    (he : Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (F := (homPresheaf B S hS F.val G.val).presheaf ⋙ CategoryTheory.forget _)
      (fun i => (e i).hom)) :
    ∃ φ : F ≅ G,
      ∀ i, (restrFun (commStructurePresheaf B S hS) (X i)).map φ.hom.val = (e i).hom := by
  obtain ⟨φ, hφ⟩ := _root_.exists_iso_of_isCompatible (commStructurePresheaf B S hS) F.val
    G.val hX F.isSheaf G.isSheaf e he
  exact ⟨(SheafOfModules.fullyFaithfulForget _).preimageIso φ, hφ⟩

/-! ### Compatibility checked on the products of two members -/

/-- **The product `X i × X j` of two members of a family of objects of `S_étale`.**  Every object
of the small étale site is étale over `S`, so this product is the fibre product `X i ×_S X j` over
which the source of Stacks 03DX checks the agreement of the local isomorphisms. -/
public noncomputable abbrev memberProd {I : Type w} (X : I → SmallEtale B S hS) (i j : I) :
    SmallEtale B S hS :=
  X i ⨯ X j

/-- **Every pair of morphisms into two members of the family factors through their product.** -/
public theorem exists_hom_memberProd {I : Type w} (X : I → SmallEtale B S hS)
    {Z : SmallEtale B S hS} {i j : I} (f : Z ⟶ X i) (g : Z ⟶ X j) :
    ∃ m : Z ⟶ memberProd B S hS X i j,
      f = m ≫ prod.fst ∧ g = m ≫ prod.snd :=
  ⟨prod.lift f g, (prod.lift_fst f g).symm, (prod.lift_snd f g).symm⟩

/-- **The agreement of a family of local morphisms over the products `X i × X j` is
compatibility.**  Every pair of morphisms into two members of the family factors through their
product, and relocalization of internal-hom sections is functorial. -/
public theorem isCompatible_of_forall_memberProd
    (F G : PresheafOfModules.{u} (Oforget (commStructurePresheaf B S hS))) {I : Type w}
    (X : I → SmallEtale B S hS)
    (α : ∀ i, (restrFun (commStructurePresheaf B S hS) (X i)).obj F ⟶
      (restrFun (commStructurePresheaf B S hS) (X i)).obj G)
    (hα : ∀ i j, homRestr (commStructurePresheaf B S hS) F G
          (prod.fst : memberProd B S hS X i j ⟶ X i) (α i) =
        homRestr (commStructurePresheaf B S hS) F G
          (prod.snd : memberProd B S hS X i j ⟶ X j) (α j)) :
    Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (F := (internalHom (commStructurePresheaf B S hS) F G).presheaf ⋙
        CategoryTheory.forget _) α := by
  intro Z i j f g
  obtain ⟨m, hf, hg⟩ := exists_hom_memberProd B S hS X f g
  rw [internalHomForget_map_apply, internalHomForget_map_apply, hf, hg, homRestr_comp,
    homRestr_comp, hα i j]

/-- **The restrictions of a global morphism are a compatible family**, for every family of
objects: relocalizing the restriction of a morphism returns its restriction. -/
public theorem isCompatible_restrFun_map
    (F G : PresheafOfModules.{u} (Oforget (commStructurePresheaf B S hS))) {I : Type w}
    (X : I → SmallEtale B S hS) (ψ : F ⟶ G) :
    Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (F := (internalHom (commStructurePresheaf B S hS) F G).presheaf ⋙
        CategoryTheory.forget _)
      (fun i => (restrFun (commStructurePresheaf B S hS) (X i)).map ψ) := by
  intro Z i j f g
  rw [internalHomForget_map_apply, internalHomForget_map_apply]
  rfl

/-- **Being an isomorphism is local on a family covering the final object of `S_étale`.**  A
morphism of sheaves of modules whose restriction to each member of such a family is an
isomorphism is itself an isomorphism.

The restrictions of a global morphism are automatically a compatible family, so Stacks 03EM glues
them to an isomorphism, and its uniqueness clause identifies that isomorphism with the given
morphism. -/
public theorem isIso_of_forall_isIso_restrFun
    {F G : SheafOfModules.{u} (structureSheaf B S hS)} (φ : F ⟶ G) {I : Type w}
    {X : I → SmallEtale B S hS} (hX : (topology B S hS).CoversTop X)
    (h : ∀ i, IsIso ((restrFun (commStructurePresheaf B S hS) (X i)).map φ.val)) :
    IsIso φ := by
  have hcomp : Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (F := (homPresheaf B S hS F.val G.val).presheaf ⋙ CategoryTheory.forget _)
      (fun i => (restrFun (commStructurePresheaf B S hS) (X i)).map φ.val) :=
    isCompatible_restrFun_map B S hS _ _ X φ.val
  obtain ⟨ψ, hψ⟩ := exists_iso_of_isCompatible B S hS F G hX
    (fun i => asIso ((restrFun (commStructurePresheaf B S hS) (X i)).map φ.val)) hcomp
  obtain ⟨χ, -, hu⟩ := existsUnique_hom_of_isCompatible B S hS F.val G hX hcomp
  have hval : φ.val = ψ.hom.val := (hu _ fun _ => rfl).trans (hu _ hψ).symm
  have hφ : φ = ψ.hom := SheafOfModules.Hom.ext hval
  rw [hφ]
  infer_instance

/-! ### The Stacks 03EM step of Stacks 03DX (2) at `τ = étale` -/

/-- **The Stacks 03EM step of Stacks 03DX (2) at `τ = étale`**, with no hypothesis.  A
quasi-coherent `𝒪_S`-module `𝓕` together with a *compatible* family of isomorphisms
`𝓕^a|_{X i} ≅ 𝒢|_{X i}` on a family of objects covering the final object of `S_étale` exhibits
`𝒢` in the essential image of `𝓕 ↦ 𝓕^a`. -/
public theorem essImage_associatedModule_of_isCompatible
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {I : Type w}
    {X : I → SmallEtale B S hS} (hX : (topology B S hS).CoversTop X) (𝓕 : S.Modules)
    (h𝓕 : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) 𝓕)
    (e : ∀ i, (restrFun (commStructurePresheaf B S hS) (X i)).obj
        ((associatedModule B S hS).obj 𝓕).val ≅
      (restrFun (commStructurePresheaf B S hS) (X i)).obj G.val)
    (he : Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (F := (homPresheaf B S hS ((associatedModule B S hS).obj 𝓕).val G.val).presheaf ⋙
        CategoryTheory.forget _) (fun i => (e i).hom)) :
    (associatedModuleQcoh B S hS).essImage G := by
  obtain ⟨φ, -⟩ :=
    exists_iso_of_isCompatible B S hS ((associatedModule B S hS).obj 𝓕) G hX e he
  exact ⟨⟨𝓕, h𝓕⟩, ⟨φ⟩⟩

/-- **The Stacks 03EM step of Stacks 03DX (2) at `τ = étale`, with compatibility checked where
the source checks it**, with no hypothesis: over the fibre products `X i ×_S X j`, which are the
binary products of the small étale site. -/
public theorem essImage_associatedModule_of_forall_memberProd
    (G : SheafOfModules.{u} (structureSheaf B S hS)) {I : Type w}
    (X : I → SmallEtale B S hS) (hX : (topology B S hS).CoversTop X) (𝓕 : S.Modules)
    (h𝓕 : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) 𝓕)
    (e : ∀ i, (restrFun (commStructurePresheaf B S hS) (X i)).obj
        ((associatedModule B S hS).obj 𝓕).val ≅
      (restrFun (commStructurePresheaf B S hS) (X i)).obj G.val)
    (he : ∀ i j, homRestr (commStructurePresheaf B S hS)
          ((associatedModule B S hS).obj 𝓕).val G.val
          (prod.fst : memberProd B S hS X i j ⟶ X i) (e i).hom =
        homRestr (commStructurePresheaf B S hS) ((associatedModule B S hS).obj 𝓕).val G.val
          (prod.snd : memberProd B S hS X i j ⟶ X j) (e j).hom) :
    (associatedModuleQcoh B S hS).essImage G :=
  essImage_associatedModule_of_isCompatible B S hS G hX 𝓕 h𝓕 e
    (isCompatible_of_forall_memberProd B S hS _ _ X _ he)

end AlgebraicGeometry.SmallEtale

end
