module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Cohomology is unchanged by pullback along a morphism to a bigger site

This is Stacks project Lemma Tag `03YU` ("Cohomology on Sites", Lemma 21.7.2),
under the hypotheses of Sites Tag `03A4` (`sites-lemma-bigger-site`).

We work with sites `C` and `D` and a functor `u : C \to D` (called `F` in the
Lean code, following the Mathlib naming convention for the functor inducing
morphisms of sites).  The functor `u` is assumed to satisfy the *bigger-site
hypotheses*:
  (a) `u` is cocontinuous;
  (b) `u` is continuous;
  (c) `u` is fully faithful;
  (d) fibre products (pullbacks) exist in `C` and `u` commutes with them;
  (e) there exist final objects `e_C` of `C` and `e_D` of `D` with
      `u(e_C) = e_D`.

Under these hypotheses `u` induces a triple of adjoint functors on abelian
sheaves
  `g_!    = u.sheafPullback`                (left adjoint, `f^{-1}`),
  `g^{-1} = u.sheafPushforwardContinuous`   (the pullback of abelian sheaves),
  `g_*    = u.sheafPushforwardCocontinuous` (right adjoint),
with adjunctions `g_! \dashv g^{-1}` (`sheafAdjunctionContinuous`) and
`g^{-1} \dashv g_*` (`sheafAdjunctionCocontinuous`).  In particular `g^{-1}` is
*exact* (it has both a left and a right adjoint, Stacks Tag `00XO`/`03A4`), and
`g_! = f^{-1}` is exact as well (Stacks Tag `03A4`).

The main statements assert that `g^{-1}` does not change cohomology, both at the
level of the bounded-below derived category and at the level of the individual
cohomology groups:
  `R\Gamma(C, g^{-1} F) \cong R\Gamma(D, F)`     and  `H^p(C, g^{-1} F) \cong H^p(D, F)`
    (Statement 1, over the whole site)
  `R\Gamma(U, g^{-1} F) \cong R\Gamma(u(U), F)`  and  `H^p(U, g^{-1} F) \cong H^p(u(U), F)`
    (Statement 2, over an object `U`)
naturally in `F` (Statement 3).  The heart of the proof (Statement 4) is that:
  (1) the sections functors agree, `\Gamma(U, g^{-1} F) = \Gamma(u(U), F)`, coming
      from `g^{-1} F (U) = F (u(U))` (and over the whole site from hypothesis (e),
      since `\Gamma(C, -)` is sections at the terminal object);
  (2) `g^{-1}` carries injective abelian sheaves to injective abelian sheaves,
      because it is the right adjoint of the exact functor `g_! = f^{-1}`.

## Conventions / formalization choices

* All sheaves of abelian groups are valued in `Ab` (the category of abelian
  groups, `= AddCommGrp`).  We take the sites `C, D` to be small categories.
* The "bigger-site hypotheses" are bundled below as a `variable` block of
  typeclass / data assumptions.  Hypotheses (a)-(e) are recorded directly.  The
  Stacks-project *consequences* of (a)-(e) that Mathlib does not yet derive
  automatically -- namely that `g^{-1}` admits the (exact) left adjoint
  `g_! = f^{-1}` and the right adjoint `g_*`, i.e. that `g^{-1}` is exact, and
  that `g_! = f^{-1}` is exact -- are recorded as the typeclass hypotheses
    `[(F.sheafPushforwardContinuous Ab J K).IsRightAdjoint]`     (existence of `g_!`),
    `[\forall P, F.op.HasPointwiseRightKanExtension P]`          (existence of `g_*`),
    `[(F.sheafPullback Ab J K).PreservesMonomorphisms]`          (exactness of `g_!`).
  These are precisely the Lean-side packaging of the Stacks-project facts
  (Tags `00XO`, `00XS`, `03A4`); from them the *exactness of* `g^{-1}` (both
  `PreservesFiniteLimits` and `PreservesFiniteColimits`), its additivity, and the
  *preservation of injectives* by `g^{-1}` are all **derived** below (they are
  not assumed).
* `\Gamma(U, -) : Sheaf J Ab \to Ab` is the sections functor over an object `U`,
  `(sheafSections J Ab).obj (op U)`.
* `\Gamma(C, -) : Sheaf J Ab \to Ab` is the global sections over the site, the
  limit over `Cᵒᵖ` of the underlying presheaf, i.e. `Mor_{PSh}(e, -)` with `e`
  the terminal presheaf (`siteSections`).  When `C` has a terminal object `e_C`
  this agrees with `\Gamma(e_C, -)` (`siteSections_iso_sections`).
* `H^p(U, -) = R^p \Gamma(U, -)` is the `p`-th right derived functor of
  `\Gamma(U, -)` (`cohomology`); likewise `H^p(C, -) = R^p \Gamma(C, -)`
  (`siteCohomology`).
* `R\Gamma(U, -)` (resp. `R\Gamma(C, -)`) is modelled as the right-derived functor
  to the homotopy category of bounded-below cochain complexes
  `K^+(Ab) = HomotopyCategory Ab (ComplexShape.up ℕ)`, the standard
  injective-resolution model of the bounded-below derived category `D^+(\mathbf Z)`
  for objects of `Ab`; this is `RGamma` (resp. `RGammaSite`).  Applying the
  homology functor `H^p` recovers `H^p` from `R\Gamma`.

## Note on the formalization of the Main Statement(s)

Each cohomology-comparison statement is accompanied by a *canonical*
natural-isomorphism `def` (e.g. `derivedObjectIso`, `cohomologyObjectIso`,
`derivedSiteIso`, `cohomologySiteIso`) realising the isomorphism explicitly as an
isomorphism of functors `Sheaf K Ab ⥤ D^+(\mathbf Z)` (resp. `Sheaf K Ab ⥤ Ab`);
the `theorem` versions then record the corresponding existence statements (which
are exactly Statements 1-3, naturally in the sheaf).
-/

open CategoryTheory Limits Opposite

universe v u

namespace Stacks.Cohomology.CompositeRightDerived

/-! ## Generic homological algebra input

The mathematical heart of Statement 4 ⇒ Statements 1-2 is the following general
fact: if `L : C ⥤ D` is an *exact* functor between abelian categories with
enough injectives that moreover *preserves injective objects*, then for any
additive `G : D ⥤ E` the right derived functor of the composite `L ⋙ G` is the
composite of `L` with the right derived functor of `G`:
  `(L ⋙ G).rightDerived n ≅ L ⋙ G.rightDerived n`,
both at the level of cohomology groups (`compRightDerivedNatIso`) and at the
level of the bounded-below derived category modelled in `K^+`
(`compRightDerivedToHomotopyCategoryNatIso`).  This is because `L` carries an
injective resolution of `X` to an injective resolution of `L X`, so both sides
are computed by the same complex. -/

/-- An exact functor `L` preserving injectives sends an injective resolution of
`X` to an injective resolution of `L X`. -/
noncomputable def mapInjRes {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (L : C ⥤ D) [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [L.PreservesInjectiveObjects] {X : C} (I : InjectiveResolution X) :
    InjectiveResolution (L.obj X) where
  cocomplex := (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  injective := fun n => by
    have : Injective (I.cocomplex.X n) := I.injective n
    exact L.injective_obj (I.cocomplex.X n)
  hasHomology := by
    have := L.preservesHomologyOfExact; intro i; infer_instance
  ι := (HomologicalComplex.singleMapHomologicalComplex L (ComplexShape.up ℕ) 0).inv.app X ≫
    (L.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι
  quasiIso := by
    have := L.preservesHomologyOfExact
    have : QuasiIso ((L.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι) := inferInstance
    infer_instance

/-- The right derived functor of a natural isomorphism is a natural
isomorphism (cohomology-group level). -/
noncomputable def rightDerivedNatIso {C D : Type*} [Category C] [Category D] [Abelian C]
    [HasInjectiveResolutions C] [Abelian D] {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ≅ G) (n : ℕ) : F.rightDerived n ≅ G.rightDerived n where
  hom := NatTrans.rightDerived α.hom n
  inv := NatTrans.rightDerived α.inv n
  hom_inv_id := by rw [← NatTrans.rightDerived_comp, α.hom_inv_id, NatTrans.rightDerived_id]
  inv_hom_id := by rw [← NatTrans.rightDerived_comp, α.inv_hom_id, NatTrans.rightDerived_id]

/-- The right derived functor of a natural isomorphism is a natural isomorphism
(derived-category / homotopy-category level). -/
noncomputable def rightDerivedToHomotopyCategoryNatIso {C D : Type*} [Category C] [Category D]
    [Abelian C] [HasInjectiveResolutions C] [Abelian D] {F G : C ⥤ D} [F.Additive] [G.Additive]
    (α : F ≅ G) : F.rightDerivedToHomotopyCategory ≅ G.rightDerivedToHomotopyCategory where
  hom := NatTrans.rightDerivedToHomotopyCategory α.hom
  inv := NatTrans.rightDerivedToHomotopyCategory α.inv
  hom_inv_id := by
    rw [← NatTrans.rightDerivedToHomotopyCategory_comp, α.hom_inv_id,
      NatTrans.rightDerivedToHomotopyCategory_id]
  inv_hom_id := by
    rw [← NatTrans.rightDerivedToHomotopyCategory_comp, α.inv_hom_id,
      NatTrans.rightDerivedToHomotopyCategory_id]

/-- **Composite right-derived functor (cohomology-group level).** For `L : C ⥤ D`
exact and preserving injective objects, and `G : D ⥤ E` additive,
`(L ⋙ G).rightDerived n ≅ L ⋙ G.rightDerived n`, naturally.  This is the
homological-algebra engine behind Statements 1-2 of the problem (Stacks Tag
`015Z` applied to `L = g^{-1}`). -/
noncomputable def compRightDerivedNatIso {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [HasInjectiveResolutions C] [Abelian D] [HasInjectiveResolutions D] [Abelian E]
    (L : C ⥤ D) (G : D ⥤ E) [L.Additive] [G.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] [L.PreservesInjectiveObjects]
    (n : ℕ) :
    (L ⋙ G).rightDerived n ≅ L ⋙ G.rightDerived n :=
  NatIso.ofComponents
    (fun X =>
      let I := injectiveResolution X
      (I.isoRightDerivedObj (L ⋙ G) n) ≪≫ (eqToIso rfl) ≪≫
        ((mapInjRes L I).isoRightDerivedObj G n).symm)
    (by
      intro X Y f
      set IX := injectiveResolution X
      set IY := injectiveResolution Y
      set φ : IX.cocomplex ⟶ IY.cocomplex := InjectiveResolution.desc f IY IX
      have hcompC : IX.ι.f 0 ≫ φ.f 0 = f ≫ IY.ι.f 0 := by
        have h0 := HomologicalComplex.congr_hom (InjectiveResolution.desc_commutes f IY IX) 0
        rwa [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
          CochainComplex.single₀_map_f_zero] at h0
      set ψ : (mapInjRes L IX).cocomplex ⟶ (mapInjRes L IY).cocomplex :=
        (L.mapHomologicalComplex (ComplexShape.up ℕ)).map φ with hψ
      have hcompD : (mapInjRes L IX).ι.f 0 ≫ ψ.f 0 = L.map f ≫ (mapInjRes L IY).ι.f 0 := by
        have e1 : (mapInjRes L IX).ι.f 0 = L.map (IX.ι.f 0) := by dsimp [mapInjRes]; simp
        have e2 : (mapInjRes L IY).ι.f 0 = L.map (IY.ι.f 0) := by dsimp [mapInjRes]; simp
        have e3 : ψ.f 0 = L.map (φ.f 0) := by simp [hψ]
        rw [e1, e2, e3, ← L.map_comp, ← L.map_comp, hcompC]
      have hL := InjectiveResolution.isoRightDerivedObj_hom_naturality f IX IY φ hcompC (L ⋙ G) n
      have hR := InjectiveResolution.isoRightDerivedObj_inv_naturality (L.map f)
        (mapInjRes L IX) (mapInjRes L IY) ψ hcompD G n
      simp only [eqToIso_refl, Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Category.id_comp,
        Functor.comp_map, Category.assoc]
      rw [← Category.assoc, hL, Category.assoc, hR]
      rfl)

/-- **Composite right-derived functor (derived-category level).** The same
identification `(L ⋙ G).rightDerivedToHomotopyCategory ≅ L ⋙
G.rightDerivedToHomotopyCategory` for the right-derived functors into the
homotopy category `K^+`, the injective-resolution model of `D^+(\mathbf Z)`. -/
noncomputable def compRightDerivedToHomotopyCategoryNatIso {C D E : Type*}
    [Category C] [Category D] [Category E]
    [Abelian C] [HasInjectiveResolutions C] [Abelian D] [HasInjectiveResolutions D] [Abelian E]
    (L : C ⥤ D) (G : D ⥤ E) [L.Additive] [G.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] [L.PreservesInjectiveObjects] :
    (L ⋙ G).rightDerivedToHomotopyCategory ≅ L ⋙ G.rightDerivedToHomotopyCategory :=
  NatIso.ofComponents
    (fun X =>
      let I := injectiveResolution X
      (I.isoRightDerivedToHomotopyCategoryObj (L ⋙ G)) ≪≫ (eqToIso rfl) ≪≫
        ((mapInjRes L I).isoRightDerivedToHomotopyCategoryObj G).symm)
    (by
      intro X Y f
      simp only [eqToIso_refl, Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, Category.id_comp,
        Functor.comp_map]
      set IX := injectiveResolution X with hIX
      set IY := injectiveResolution Y with hIY
      set φ : IX.cocomplex ⟶ IY.cocomplex := InjectiveResolution.desc f IY IX with hφ
      have hcompC : IX.ι.f 0 ≫ φ.f 0 = f ≫ IY.ι.f 0 := by
        have h := InjectiveResolution.desc_commutes f IY IX
        have h0 := HomologicalComplex.congr_hom h 0
        rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
          CochainComplex.single₀_map_f_zero] at h0
        exact h0
      set ψ : (mapInjRes L IX).cocomplex ⟶ (mapInjRes L IY).cocomplex :=
        (L.mapHomologicalComplex (ComplexShape.up ℕ)).map φ with hψ
      have hcompD : (mapInjRes L IX).ι.f 0 ≫ ψ.f 0 = L.map f ≫ (mapInjRes L IY).ι.f 0 := by
        have e1 : (mapInjRes L IX).ι.f 0 = L.map (IX.ι.f 0) := by dsimp [mapInjRes]; simp
        have e2 : (mapInjRes L IY).ι.f 0 = L.map (IY.ι.f 0) := by dsimp [mapInjRes]; simp
        have e3 : ψ.f 0 = L.map (φ.f 0) := by simp [hψ]
        rw [e1, e2, e3, ← L.map_comp, ← L.map_comp, hcompC]
      have hL := InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_hom_naturality
        f IX IY φ hcompC (L ⋙ G)
      have hR := InjectiveResolution.isoRightDerivedToHomotopyCategoryObj_inv_naturality (L.map f)
        (mapInjRes L IX) (mapInjRes L IY) ψ hcompD G
      rw [← Category.assoc, hL, Category.assoc, Category.assoc, hR]
      congr 1)

/-! ## Setup: sites, abelian sheaves, sections functors -/

variable {C : Type u} [SmallCategory C] {D : Type u} [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (F : C ⥤ D)

/-! ### Main Definition(s) -/

/-- The sections functor `\Gamma(U, -) : Sheaf J Ab \to Ab` over an object `U`. -/
noncomputable def sections (J : GrothendieckTopology C) (U : C) :
    Sheaf J (Ab.{u}) ⥤ Ab.{u} :=
  (sheafSections J _).obj (op U)

/-- The sections functor over an object is additive: addition of morphisms of sheaves is
computed componentwise, so `\Gamma(U, -)` preserves it on the nose. -/
instance (J : GrothendieckTopology C) (U : C) : (sections J U).Additive where
  map_add := by intro X Y f g; rfl

/-- `lim : (Cᵒᵖ ⥤ Ab) ⥤ Ab` is additive (it preserves binary products). -/
noncomputable instance limAb_additive :
    (lim : (Cᵒᵖ ⥤ Ab.{u}) ⥤ Ab.{u}).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The global sections functor over the site,
`\Gamma(C, -) : Sheaf J Ab \to Ab`, given by the limit over `Cᵒᵖ` of the
underlying presheaf.  This is `Mor_{PSh}(e, -)` with `e` the terminal
presheaf. -/
@[sga "4½ Arcata 1.6.5"]
noncomputable def siteSections (J : GrothendieckTopology C) :
    Sheaf J (Ab.{u}) ⥤ Ab.{u} :=
  sheafToPresheaf J _ ⋙ lim

/-- The global sections functor over the site is additive, being the composite of the additive
`sheafToPresheaf` with the additive `lim`. -/
instance siteSections_additive (J : GrothendieckTopology C) :
    (siteSections J).Additive := by
  unfold siteSections; infer_instance

/-- **Correctness of `siteSections`.** When the site has a terminal object `e_C`,
global sections over the site agree with the sections over `e_C`: the natural
isomorphism `\Gamma(C, -) \cong \Gamma(e_C, -)` coming from the fact that `op e_C`
is initial in `Cᵒᵖ`, so the limit is computed there. -/
noncomputable def siteSections_iso_sections (J : GrothendieckTopology C) (eC : C)
    (heC : IsTerminal eC) : siteSections J ≅ sections J eC :=
  NatIso.ofComponents
    (fun X => limit.isoLimitCone
      ⟨_, limitOfDiagramInitial (initialOpOfTerminal heC) ((sheafToPresheaf J _).obj X)⟩)
    (by
      intro X Y f
      change limMap _ ≫ limit.π _ (op eC) = limit.π _ (op eC) ≫ _
      exact limMap_π _ _)

/-- The `p`-th cohomology functor over an object,
`H^p(U, -) = R^p \Gamma(U, -) : Sheaf J Ab \to Ab`. -/
@[stacks 071C "the functor H^i(U, -) = R^i Γ(U, -)"]
noncomputable def cohomology (J : GrothendieckTopology C) (U : C) (p : ℕ) :
    Sheaf J (Ab.{u}) ⥤ Ab.{u} :=
  (sections J U).rightDerived p

/-- **Stacks Project, Tag 071E.** The `p`-th cohomology functor over the whole site,
`H^p(C, -) = R^p \Gamma(C, -) : Sheaf J Ab \to Ab`.

This is the definition the tag's displayed equation makes: the global sections functor here is
`Γ(C, -) = Mor_{PSh(C)}(e, -)` of [Stacks Project, Tag 071D], and the tag's own gloss of the
equation is "in other words, it is the `i`-th right derived functor of the global sections
functor". The computation of it from a chosen injective resolution is
`Stacks.Cohomology.SiteSections.siteCohomologyIso`. -/
@[stacks 071E "the functor H^i(C, -) = R^i Γ(C, -), the tag's \"in other words\"",
  sga "4½ Arcata 1.6.5"]
noncomputable def siteCohomology (J : GrothendieckTopology C) (p : ℕ) :
    Sheaf J (Ab.{u}) ⥤ Ab.{u} :=
  (siteSections J).rightDerived p

/-- The derived-category-level cohomology `R\Gamma(U, -)`: the right-derived
functor of `\Gamma(U, -)` into the homotopy category of bounded-below cochain
complexes `K^+(Ab)` (the injective-resolution model of `D^+(\mathbf Z)`). -/
noncomputable def RGamma (J : GrothendieckTopology C) (U : C) :
    Sheaf J (Ab.{u}) ⥤ HomotopyCategory (Ab.{u}) (ComplexShape.up ℕ) :=
  (sections J U).rightDerivedToHomotopyCategory

/-- The derived-category-level global cohomology `R\Gamma(C, -)` over the whole
site. -/
noncomputable def RGammaSite (J : GrothendieckTopology C) :
    Sheaf J (Ab.{u}) ⥤ HomotopyCategory (Ab.{u}) (ComplexShape.up ℕ) :=
  (siteSections J).rightDerivedToHomotopyCategory

/-! ## The bigger-site hypotheses

We bundle hypotheses (a)-(e) as typeclass / data assumptions, together with the
Mathlib-side packaging of their Stacks-project consequences on abelian sheaves
(see the conventions in the header). -/

section MainStatements

variable
  -- (b) `u` is continuous, (a) `u` is cocontinuous, (c) `u` is fully faithful:
  [F.IsContinuous J K] [F.IsCocontinuous J K] [F.Full] [F.Faithful]
  -- (d) fibre products exist in `C` and `u` commutes with them:
  [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
  -- Stacks-project consequences (Tags `00XO`/`00XS`/`03A4`), as Lean hypotheses:
  --   existence of the left adjoint `g_! = f^{-1}`,
  [(F.sheafPushforwardContinuous (Ab.{u}) J K).IsRightAdjoint]
  --   existence of the right adjoint `g_*`,
  [∀ (P : Cᵒᵖ ⥤ Ab.{u}), F.op.HasPointwiseRightKanExtension P]
  --   exactness of `g_! = f^{-1}`:
  [(F.sheafPullback (Ab.{u}) J K).PreservesMonomorphisms]

/-- `g^{-1} : Sheaf K Ab \to Sheaf J Ab`, the pullback of abelian sheaves
(`f_* = g^{-1}` in the notation of the problem). -/
noncomputable def gInvAb : Sheaf K (Ab.{u}) ⥤ Sheaf J (Ab.{u}) :=
  F.sheafPushforwardContinuous (Ab.{u}) J K

/-- `g_! = f^{-1} : Sheaf J Ab \to Sheaf K Ab`, the left adjoint of `g^{-1}`. -/
noncomputable def gLowerAb : Sheaf J (Ab.{u}) ⥤ Sheaf K (Ab.{u}) :=
  F.sheafPullback (Ab.{u}) J K

/-- `g_! = f^{-1}` preserves monomorphisms: this is the exactness of `g_!`, assumed above as a
hypothesis on `F.sheafPullback` and transported to the abbreviation `gLowerAb`. -/
instance : (gLowerAb J K F).PreservesMonomorphisms := by
  unfold gLowerAb; infer_instance

/-- The adjunction `g_! \dashv g^{-1}` (Stacks Tag `03A4` / `00XS`). -/
noncomputable def gAdjunction : gLowerAb J K F ⊣ gInvAb J K F :=
  F.sheafAdjunctionContinuous (Ab.{u}) J K

/-- The adjunction `g^{-1} \dashv g_*` (Stacks Tag `00XO`). -/
noncomputable def gAdjunctionCocont :
    gInvAb J K F ⊣ F.sheafPushforwardCocontinuous (Ab.{u}) J K :=
  F.sheafAdjunctionCocontinuous (Ab.{u}) J K

/-- **`g^{-1}` is exact:** it preserves finite colimits, being a left adjoint
(of `g_*`).  This is Stacks Tag `00XO`. -/
noncomputable instance gInvAb_preservesFiniteColimits :
    PreservesFiniteColimits (gInvAb J K F) :=
  haveI : PreservesColimitsOfSize.{0, 0} (gInvAb J K F) :=
    (gAdjunctionCocont J K F).leftAdjoint_preservesColimits
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- **`g^{-1}` is exact:** it preserves finite limits, being a right adjoint
(of `g_!`). -/
noncomputable instance gInvAb_preservesFiniteLimits :
    PreservesFiniteLimits (gInvAb J K F) :=
  haveI : PreservesLimitsOfSize.{0, 0} (gInvAb J K F) :=
    (gAdjunction J K F).rightAdjoint_preservesLimits
  PreservesLimitsOfSize.preservesFiniteLimits _

/-- `g^{-1}` is additive (it preserves finite products, being exact). -/
instance gInvAb_additive : (gInvAb J K F).Additive :=
  Functor.additive_of_preserves_binary_products _

/-! ### Statement 4(2): `g^{-1}` preserves injectives.

`g^{-1}` is the right adjoint of `g_! = f^{-1}`, and under the bigger-site
hypotheses `g_!` is exact (in particular it preserves monomorphisms); hence
`g^{-1}` sends injective abelian sheaves to injective abelian sheaves
(Stacks Tag `015Z`). -/
omit [F.IsCocontinuous J K] [F.Full] [F.Faithful] [HasPullbacks C]
  [PreservesLimitsOfShape WalkingCospan F]
  [∀ (P : Cᵒᵖ ⥤ Ab.{u}), F.op.HasPointwiseRightKanExtension P] in
/-- **`g^{-1}` preserves injective objects.** It is the right adjoint of `g_! = f^{-1}`, which
preserves monomorphisms, so it carries injective abelian sheaves to injective abelian sheaves
(Stacks Tag `015Z`). -/
theorem gInvAb_preservesInjectiveObjects :
    (gInvAb J K F).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (gAdjunction J K F)

noncomputable instance : (gInvAb J K F).PreservesInjectiveObjects :=
  gInvAb_preservesInjectiveObjects J K F

/-! ### Statement 4(1): the sections functors agree.

For every object `U` of `C`, precomposing the sections functor `\Gamma(U, -)` over
the site `J` with `g^{-1}` gives the sections functor `\Gamma(u(U), -)` over the
site `K`.  This is *definitionally* true, because the underlying presheaf of
`g^{-1} G` is `G ∘ uᵒᵖ`, so `g^{-1} G (U) = G (u(U))`. -/
omit [F.IsCocontinuous J K] [F.Full] [F.Faithful] [HasPullbacks C]
  [PreservesLimitsOfShape WalkingCospan F]
  [(F.sheafPushforwardContinuous (Ab.{u}) J K).IsRightAdjoint]
  [∀ (P : Cᵒᵖ ⥤ Ab.{u}), F.op.HasPointwiseRightKanExtension P]
  [(F.sheafPullback (Ab.{u}) J K).PreservesMonomorphisms] in
/-- **The sections functors agree.** Precomposing the sections functor `\Gamma(U, -)` over the
site `J` with `g^{-1}` gives the sections functor `\Gamma(u(U), -)` over `K`. This is an equality
of functors, not merely an isomorphism, because the underlying presheaf of `g^{-1} G` is
`G ∘ uᵒᵖ`, so `g^{-1} G (U) = G (u(U))`. -/
theorem sections_comp_gInvAb (U : C) :
    gInvAb J K F ⋙ sections J U = sections K (F.obj U) :=
  rfl

/-- Statement 4(1), as a natural isomorphism of functors (the form used for the
functoriality of Statement 3 at the level of sections over an object). -/
noncomputable def sectionsCompGInvIso (U : C) :
    gInvAb J K F ⋙ sections J U ≅ sections K (F.obj U) :=
  Iso.refl _

/-- Statement 4(1), global part: given a terminal object `e_C` of `C` and a
terminal object `e_D` of `D` with `u(e_C) = e_D`, the global sections over `C`
of `g^{-1} F` agree with the global sections over `D` of `F`.  Since
`\Gamma(C, -) \cong \Gamma(e_C, -)` and `\Gamma(D, -) \cong \Gamma(e_D, -)`
(terminal objects), and `g^{-1} F(e_C) = F(u(e_C)) = F(e_D)`, this is a natural
isomorphism `g^{-1} ⋙ \Gamma(C, -) \cong \Gamma(D, -)`. -/
noncomputable def siteSectionsCompGInvIso (eC : C) (eD : D) (heC : IsTerminal eC)
    (heD : IsTerminal eD) (hu : F.obj eC = eD) :
    gInvAb J K F ⋙ siteSections J ≅ siteSections K :=
  (Functor.isoWhiskerLeft (gInvAb J K F) (siteSections_iso_sections J eC heC)) ≪≫
  (eqToIso (sections_comp_gInvAb J K F eC)) ≪≫
  (eqToIso (by rw [hu])) ≪≫
  (siteSections_iso_sections K eD heD).symm

/-! ## Canonical isomorphisms realising the Main Statement(s)

The following four `def`s realise the cohomology comparisons of Statements 1-2
as *canonical* natural isomorphisms of functors (so the canonical/naturality
data of Statement 3 is available as a usable structure).  The `theorem`
versions stated afterwards are the corresponding existence statements (the Main
Statement(s) proper). -/

/-- Statement 2, derived-category level (canonical iso):
`R\Gamma(U, g^{-1} -) \cong R\Gamma(u(U), -)` as a canonical natural isomorphism of
functors `Sheaf K Ab ⥤ D^+(\mathbf Z)` (modelled in `K^+(Ab)`). -/
noncomputable def derivedObjectIso (U : C) :
    gInvAb J K F ⋙ RGamma J U ≅ RGamma K (F.obj U) :=
  (compRightDerivedToHomotopyCategoryNatIso (gInvAb J K F) (sections J U)).symm ≪≫
    rightDerivedToHomotopyCategoryNatIso (eqToIso (sections_comp_gInvAb J K F U))

/-- Statement 2, cohomology-group level (canonical iso):
`H^p(U, g^{-1} -) \cong H^p(u(U), -)` as a canonical natural isomorphism of functors
`Sheaf K Ab ⥤ Ab`. -/
noncomputable def cohomologyObjectIso (U : C) (p : ℕ) :
    gInvAb J K F ⋙ cohomology J U p ≅ cohomology K (F.obj U) p :=
  (compRightDerivedNatIso (gInvAb J K F) (sections J U) p).symm ≪≫
    rightDerivedNatIso (eqToIso (sections_comp_gInvAb J K F U)) p

/-- Statement 1, derived-category level (canonical iso):
`R\Gamma(C, g^{-1} -) \cong R\Gamma(D, -)` as a canonical natural isomorphism of
functors `Sheaf K Ab ⥤ D^+(\mathbf Z)`, using the terminal-object data of
hypothesis (e). -/
noncomputable def derivedSiteIso (eC : C) (eD : D) (heC : IsTerminal eC)
    (heD : IsTerminal eD) (hu : F.obj eC = eD) :
    gInvAb J K F ⋙ RGammaSite J ≅ RGammaSite K :=
  (compRightDerivedToHomotopyCategoryNatIso (gInvAb J K F) (siteSections J)).symm ≪≫
    rightDerivedToHomotopyCategoryNatIso (siteSectionsCompGInvIso J K F eC eD heC heD hu)

/-- Statement 1, cohomology-group level (canonical iso):
`H^p(C, g^{-1} -) \cong H^p(D, -)`, with site cohomology computed via the terminal
objects `e_C, e_D` (hypothesis (e)), as a canonical natural isomorphism of
functors `Sheaf K Ab ⥤ Ab`. -/
noncomputable def cohomologySiteIso (eC : C) (eD : D) (heC : IsTerminal eC)
    (heD : IsTerminal eD) (hu : F.obj eC = eD) (p : ℕ) :
    gInvAb J K F ⋙ siteCohomology J p ≅ siteCohomology K p :=
  (compRightDerivedNatIso (gInvAb J K F) (siteSections J) p).symm ≪≫
    rightDerivedNatIso (siteSectionsCompGInvIso J K F eC eD heC heD hu) p

/-! ## Main Statement(s)

The Main Statement(s), recorded as `theorem`s asserting the existence of the
canonical natural isomorphisms above. -/

omit [F.Full] [F.Faithful] [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F] in
/-- **Statement 2 (cohomology over an object), derived-category level.**
For every object `U` of `C` there is a canonical isomorphism in `D^+(\mathbf Z)`
`R\Gamma(U, g^{-1}\mathcal F) \cong R\Gamma(u(U), \mathcal F)`, functorially (i.e.
as a natural isomorphism of functors `Sheaf K Ab ⥤ D^+(\mathbf Z)`).  Witnessed
canonically by `derivedObjectIso`. -/
@[stacks 03YU "RΓ(U, g⁻¹F) ≅ RΓ(u(U), F)"]
theorem statement2_derived (U : C) :
    Nonempty (gInvAb J K F ⋙ RGamma J U ≅ RGamma K (F.obj U)) :=
  ⟨derivedObjectIso J K F U⟩

omit [F.Full] [F.Faithful] [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F] in
/-- **Statement 2 (cohomology over an object), cohomology-group level.**
For every object `U` of `C` and every `p`, a natural isomorphism of functors
`Sheaf K Ab ⥤ Ab`, `H^p(U, g^{-1} -) \cong H^p(u(U), -)`.  Witnessed canonically by
`cohomologyObjectIso`. -/
@[stacks 03YU "Hᵖ(U, g⁻¹F) ≅ Hᵖ(u(U), F)"]
theorem statement2_cohomology (U : C) (p : ℕ) :
    Nonempty (gInvAb J K F ⋙ cohomology J U p ≅ cohomology K (F.obj U) p) :=
  ⟨cohomologyObjectIso J K F U p⟩

omit [F.Full] [F.Faithful] [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F] in
/-- **Statement 1 (cohomology over the whole site), derived-category level.**
For terminal objects `e_C` of `C` and `e_D` of `D` with `u(e_C) = e_D`
(hypothesis (e)), a canonical isomorphism in `D^+(\mathbf Z)`
`R\Gamma(C, g^{-1}\mathcal F) \cong R\Gamma(D, \mathcal F)`, functorially.
Witnessed canonically by `derivedSiteIso`. -/
@[stacks 03YU "RΓ(C, g⁻¹F) ≅ RΓ(D, F)"]
theorem statement1_derived (eC : C) (eD : D) (heC : IsTerminal eC)
    (heD : IsTerminal eD) (hu : F.obj eC = eD) :
    Nonempty (gInvAb J K F ⋙ RGammaSite J ≅ RGammaSite K) :=
  ⟨derivedSiteIso J K F eC eD heC heD hu⟩

omit [F.Full] [F.Faithful] [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F] in
/-- **Statement 1 (cohomology over the whole site), cohomology-group level.**
For terminal objects `e_C` of `C` and `e_D` of `D` with `u(e_C) = e_D`
(hypothesis (e)) and every `p`, a natural isomorphism of functors
`Sheaf K Ab ⥤ Ab`, `H^p(C, g^{-1} -) \cong H^p(D, -)`.  Witnessed canonically by
`cohomologySiteIso`. -/
@[stacks 03YU "Hᵖ(C, g⁻¹F) ≅ Hᵖ(D, F)"]
theorem statement1_cohomology (eC : C) (eD : D) (heC : IsTerminal eC)
    (heD : IsTerminal eD) (hu : F.obj eC = eD) (p : ℕ) :
    Nonempty (gInvAb J K F ⋙ siteCohomology J p ≅ siteCohomology K p) :=
  ⟨cohomologySiteIso J K F eC eD heC heD hu p⟩

omit [F.IsCocontinuous J K] [F.Full] [F.Faithful] [HasPullbacks C] [PreservesLimitsOfShape
    WalkingCospan F] [∀ (P : Cᵒᵖ ⥤ Ab), F.op.HasPointwiseRightKanExtension P] in
/-- **Statement 4(2) (key lemma: preservation of injectives).**
`g^{-1}` carries injective abelian sheaves to injective abelian sheaves. -/
alias statement4_preservesInjectives := gInvAb_preservesInjectiveObjects

/-! ### Statement 3 (functoriality).

All the isomorphisms above are *natural transformations of functors*
(`Sheaf K Ab ⥤ D^+(\mathbf Z)`, resp. `Sheaf K Ab ⥤ Ab`): this is built into the
very statements `derivedSiteIso`, `derivedObjectIso`, `cohomologySiteIso`,
`cohomologyObjectIso`, `sectionsCompGInvIso` and `siteSectionsCompGInvIso`, each
of which is an isomorphism of functors, and is reflected in the `theorem`s above
(whose conclusions are isomorphisms of functors, i.e. natural isomorphisms). -/

end MainStatements

end Stacks.Cohomology.CompositeRightDerived
