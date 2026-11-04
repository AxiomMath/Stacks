module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Group.Shrink
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSubsiteModules
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineSubsite

/-!
# Sheaves of modules on `Cris(X/S)` and on its affine subsite, at the universe of the site

Fix a global crystalline situation `(p, (S, I, γ), X)` at universe level `u`.  The affine
crystalline site `AffineCris(X/S)` is a dense subsite of the small crystalline site `Cris(X/S)`
(`instIsDenseSubsiteAffineι`), and Mathlib's Comparison Lemma turns this into an equivalence of
categories of abelian sheaves only at the raised coefficient universe `u + 1`
(`affineAbelianSheafEquiv`): it needs limits over the large comma categories
`StructuredArrow X (affineι S).op`, whose objects live in `Type (u + 1)`.

This file proves the Comparison Lemma at the universe `u` itself, the universe of the sections of
the structure sheaf `𝒪_{X/S}`, and deduces the comparison of sheaves of `𝒪_{X/S}`-modules with
sheaves of modules over the restricted structure sheaf on `AffineCris(X/S)`.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `shrinkPresheaf`, `shrinkPresheafULiftIso` — a presheaf of abelian groups in
  `AddCommGrpCat.{u + 1}` with `u`-small sections, shrunk to `AddCommGrpCat.{u}`, and the
  identification of its universe lift with the original presheaf.
* `small_sections_of_small_affine` — an abelian sheaf on `Cris(X/S)` whose sections over the
  affine objects are `u`-small has `u`-small sections over every object.
* `instIsEquivalenceAffineSheafPushforward` — **restriction of abelian sheaves with coefficients
  in `AddCommGrpCat.{u}` along `AffineCris(X/S) ⥤ Cris(X/S)` is an equivalence.**
* `affineModuleEquivalence` — **sheaves of `𝒪_{X/S}`-modules with sections in `Type u` are
  sheaves of modules over the restriction of `𝒪_{X/S}` to `AffineCris(X/S)`**, by restriction.
* `affineModuleEquivalenceInverseObjRestrictionIso` — the restriction of the extension of a
  sheaf of modules on `AffineCris(X/S)` is that sheaf of modules.

## Implementation notes

Full faithfulness of the restriction holds for any dense subsite and is Mathlib's; the work is
essential surjectivity at the universe `u`.  An abelian sheaf `N` on `AffineCris(X/S)` with
values in `AddCommGrpCat.{u}` is lifted to `AddCommGrpCat.{u + 1}`, extended to `Cris(X/S)` by
the Comparison Lemma at `u + 1`, and the extension `G'` is shrunk back.  Shrinking needs each
group of sections `G'(B)` to be `u`-small: the restrictions of `B` to an affine open around each
point of its ambient scheme cover `B`, and they are indexed by the points of that scheme, a type
in `Type u`, so separation embeds `G'(B)` in a `u`-indexed product of groups isomorphic to
sections of `N` lifted to `Type (u + 1)`.  The shrunk presheaf is a sheaf because its universe
lift is isomorphic to `G'` and the universe lift of abelian groups, being fully faithful,
reflects limits.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

section ShrinkPresheaf

variable {C : Type*} [Category* C]

/-- A presheaf of abelian groups in `AddCommGrpCat.{u + 1}` whose groups of sections are
`u`-small, shrunk to a presheaf with values in `AddCommGrpCat.{u}`. -/
noncomputable def shrinkPresheaf (G : C ⥤ AddCommGrpCat.{u + 1})
    [∀ U, Small.{u} (G.obj U)] : C ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (Shrink.{u} (G.obj U))
  map f := AddCommGrpCat.ofHom ((Shrink.addEquiv.symm.toAddMonoidHom.comp (G.map f).hom).comp
    Shrink.addEquiv.toAddMonoidHom)
  map_id U := by ext x; simp
  map_comp f g := by ext x; simp

/-- The universe lift of the shrunk presheaf `shrinkPresheaf G` is the presheaf `G`. -/
noncomputable def shrinkPresheafULiftIso (G : C ⥤ AddCommGrpCat.{u + 1})
    [∀ U, Small.{u} (G.obj U)] :
    shrinkPresheaf G ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} ≅ G :=
  NatIso.ofComponents (fun U ↦ (AddEquiv.ulift.trans Shrink.addEquiv).toAddCommGrpIso)
    (fun f ↦ by
      ext x
      change Shrink.addEquiv (ULift.down (ULift.up (Shrink.addEquiv.symm
        ((G.map f).hom (Shrink.addEquiv x.down))))) = (G.map f).hom (Shrink.addEquiv x.down)
      exact Shrink.addEquiv.apply_symm_apply _)

end ShrinkPresheaf

variable (S : GlobalCrystallineSituation.{u})

/-- **The sections of an abelian sheaf on `Cris(X/S)` are `u`-small as soon as its sections over
the affine objects are.**  The restrictions of an object `B` to an affine open around each point
of its ambient scheme cover `B`, so by separation the sections over `B` embed in the product of
the sections over these restrictions, a product of `u`-small groups indexed by the points of the
ambient scheme. -/
theorem small_sections_of_small_affine (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (hG : ∀ Y : AffineCrystallineThickening S, Small.{u} (G.obj.obj (op ((affineι S).obj Y))))
    (B : CrystallineThickening S) : Small.{u} (G.obj.obj (op B)) := by
  classical
  have hpt : ∀ x : B.obj.thickening.target.scheme,
      ∃ W : B.obj.thickening.target.scheme.Opens, IsAffineOpen W ∧ x ∈ W := fun x ↦ by
    obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    exact ⟨W, hW, hxW⟩
  choose W hW hxW using hpt
  let V : ULift.{u + 1} B.obj.thickening.target.scheme → B.obj.thickening.target.scheme.Opens :=
    fun x ↦ W x.down
  have hcov : Sieve.generate (B.restrictOpenCover V).presieve₀ ∈ smallTopology S B :=
    smallZariskiCovering_mem_smallTopology S _
      (CrystallineThickening.isZariskiCovering_restrictOpenCover B V
        fun x ↦ ⟨ULift.up x, hxW x⟩)
  let φ : G.obj.obj (op B) → ∀ x : ULift.{u + 1} B.obj.thickening.target.scheme,
      G.obj.obj (op ((affineι S).obj
        (AffineCrystallineThickening.restrictOpen B (hW x.down)))) :=
    fun s x ↦ G.obj.map (B.restrictOpenHom (V x)).op s
  have hφ : Function.Injective φ := by
    intro s t hst
    have hsh := (isSheaf_iff_isSheaf_of_type _ _).1
      ((sheafCompose (smallTopology S)
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G).property
    refine (Presieve.isSeparatedFor_iff_generate.2 (hsh.isSeparated _ hcov)).ext ?_
    rintro _ _ ⟨x⟩
    exact congr_fun hst x
  have : ∀ x : ULift.{u + 1} B.obj.thickening.target.scheme, Small.{u} (G.obj.obj (op
      ((affineι S).obj (AffineCrystallineThickening.restrictOpen B (hW x.down))))) :=
    fun x ↦ hG _
  exact small_of_injective hφ

/-- **Restriction of abelian sheaves with values in `AddCommGrpCat.{u}` from `Cris(X/S)` to
`AffineCris(X/S)` is essentially surjective.**  An abelian sheaf on `AffineCris(X/S)` is lifted
to the coefficient universe `u + 1`, extended to `Cris(X/S)` by the Comparison Lemma there, and
the extension, whose sections are `u`-small by `small_sections_of_small_affine`, is shrunk back
to the universe `u`. -/
instance instEssSurjAffineSheafPushforward :
    ((affineι S).sheafPushforwardContinuous AddCommGrpCat.{u}
      (affineTopology S) (smallTopology S)).EssSurj where
  mem_essImage N := by
    let F := (affineι S).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (affineTopology S) (smallTopology S)
    let N' := (sheafCompose (affineTopology S) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj N
    let G' := F.objPreimage N'
    let e : (affineι S).op ⋙ G'.obj ≅ N.obj ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} :=
      (sheafToPresheaf _ _).mapIso (F.objObjPreimageIso N')
    have hsmall : ∀ U, Small.{u} (G'.obj.obj U) := fun U ↦
      small_sections_of_small_affine S G'
        (fun Y ↦ small_map (β := ULift.{u + 1} (N.obj.obj (op Y)))
          (e.app (op Y)).addCommGroupIsoToAddEquiv.toEquiv) U.unop
    let G := shrinkPresheaf G'.obj
    let eU := shrinkPresheafULiftIso G'.obj
    have hG : Presheaf.IsSheaf (smallTopology S) G :=
      Presheaf.isSheaf_of_isSheaf_comp _ _ AddCommGrpCat.uliftFunctor.{u + 1, u}
        ((Presheaf.isSheaf_of_iso_iff eU).2 G'.property)
    let W := (Functor.whiskeringRight (AffineCrystallineThickening S)ᵒᵖ _ _).obj
      AddCommGrpCat.uliftFunctor.{u + 1, u}
    let eW : W.obj ((affineι S).op ⋙ G) ≅ W.obj N.obj :=
      Functor.isoWhiskerLeft (affineι S).op eU ≪≫ e
    let eG : (affineι S).op ⋙ G ≅ N.obj :=
      (AddCommGrpCat.uliftFunctorFullyFaithful.{u, u + 1}.whiskeringRight
        (AffineCrystallineThickening S)ᵒᵖ).preimageIso (X := (affineι S).op ⋙ G) (Y := N.obj) eW
    exact ⟨⟨G, hG⟩, ⟨(fullyFaithfulSheafToPresheaf _ _).preimageIso eG⟩⟩

/-- **The Comparison Lemma for `Cris(X/S)` and `AffineCris(X/S)` at the universe `u`**:
restriction of abelian sheaves with values in `AddCommGrpCat.{u}` along the inclusion
`AffineCris(X/S) ⥤ Cris(X/S)` is an equivalence.  Full faithfulness holds for every dense
subsite; essential surjectivity is `instEssSurjAffineSheafPushforward`. -/
instance instIsEquivalenceAffineSheafPushforward :
    ((affineι S).sheafPushforwardContinuous AddCommGrpCat.{u}
      (affineTopology S) (smallTopology S)).IsEquivalence :=
  Functor.IsEquivalence.mk

/-- **Sheaves of `𝒪_{X/S}`-modules on `Cris(X/S)` are sheaves of modules on `AffineCris(X/S)`**
over the restriction of the structure sheaf, the equivalence being restriction along the
inclusion, at the module universe `u` of the sections of `𝒪_{X/S}`. -/
noncomputable def affineModuleEquivalence :
    SheafOfModules.{u} (structureSheaf S) ≌
      SheafOfModules.{u} (Stacks.DenseSubsiteModules.ringRestriction
        (affineTopology S) (smallTopology S) (affineι S) (structureSheaf S)) :=
  Stacks.DenseSubsiteModules.moduleRestrictionEquivalence (affineTopology S) (smallTopology S)
    (affineι S) (structureSheaf S)

/-- The functor of `affineModuleEquivalence` is restriction of sheaves of modules along the
inclusion `AffineCris(X/S) ⥤ Cris(X/S)`. -/
theorem affineModuleEquivalence_functor :
    (affineModuleEquivalence S).functor =
      Stacks.DenseSubsiteModules.moduleRestriction (affineTopology S) (smallTopology S)
        (affineι S) (structureSheaf S) :=
  rfl

/-- The restriction to `AffineCris(X/S)` of the extension to `Cris(X/S)` of a sheaf of modules
`N` on `AffineCris(X/S)` is `N`. -/
noncomputable def affineModuleEquivalenceInverseObjRestrictionIso
    (N : SheafOfModules.{u} (Stacks.DenseSubsiteModules.ringRestriction
      (affineTopology S) (smallTopology S) (affineι S) (structureSheaf S))) :
    (Stacks.DenseSubsiteModules.moduleRestriction (affineTopology S) (smallTopology S)
      (affineι S) (structureSheaf S)).obj ((affineModuleEquivalence S).inverse.obj N) ≅ N :=
  (affineModuleEquivalence S).counitIso.app N

/-- A sheaf of `𝒪_{X/S}`-modules `M` on `Cris(X/S)` is the extension of its restriction to
`AffineCris(X/S)`. -/
noncomputable def affineModuleEquivalenceRestrictionInverseObjIso
    (M : SheafOfModules.{u} (structureSheaf S)) :
    M ≅ (affineModuleEquivalence S).inverse.obj
      ((Stacks.DenseSubsiteModules.moduleRestriction (affineTopology S) (smallTopology S)
        (affineι S) (structureSheaf S)).obj M) :=
  (affineModuleEquivalence S).unitIso.app M

end Crystalline.GlobalCrystallineSituation.SmallSite

end
