module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.AffineQuasicoherentSheaf
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineModuleComparison

/-!
# Sheaves of modules on `CRIS(X/S)` and on `CRIS_aff(X/S)`, at the universe of the site

Fix a global crystalline situation `(p, (S, I, γ), X)` at universe level `u`.  The full
subcategory `CRIS_aff(X/S)` of the big crystalline site on the objects with affine ambient scheme
is a dense subsite (`Crystalline.GlobalCrystallineSituation.instIsDenseSubsiteBigAffineι`).
Mathlib's Comparison Lemma gives an equivalence of categories of abelian sheaves only at the
coefficient universe `u + 1`; this file proves it at the universe `u` of the sections of the
structure sheaf, exactly as
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineModuleComparison.lean` does for the
small site, and deduces the comparison of sheaves of `𝒪_{X/S}`-modules.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.BigAffine`.

* `small_sections_of_small_affine` — an abelian sheaf on `CRIS(X/S)` whose sections over the
  objects with affine ambient scheme are `u`-small has `u`-small sections over every object.
* `instIsEquivalenceSheafPushforward` — restriction of abelian sheaves with coefficients in
  `AddCommGrpCat.{u}` along `CRIS_aff(X/S) ⥤ CRIS(X/S)` is an equivalence.
* `moduleEquivalence` — **sheaves of `𝒪_{X/S}`-modules on `CRIS(X/S)` are sheaves of modules over
  the restricted structure sheaf on `CRIS_aff(X/S)`**, by restriction.
* `moduleEquivalenceInverseObjRestrictionIso` — the restriction of the extension of a sheaf of
  modules on `CRIS_aff(X/S)` is that sheaf of modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Crystalline.GlobalCrystallineSituation.BigAffine

open SmallSite

variable (S : GlobalCrystallineSituation.{u})

/-- **The sections of an abelian sheaf on `CRIS(X/S)` are `u`-small as soon as its sections over
the objects with affine ambient scheme are.**  The restrictions of an object `B` to an affine open
around each point of its ambient scheme cover `B`, so by separation the sections over `B` embed in
a product, indexed by the points of the ambient scheme, of `u`-small groups. -/
theorem small_sections_of_small_affine (G : Sheaf (topology S) AddCommGrpCat.{u + 1})
    (hG : ∀ Y : BigAffineThickening S, Small.{u} (G.obj.obj (op ((bigAffineι S).obj Y))))
    (B : Thickening S) : Small.{u} (G.obj.obj (op B)) := by
  classical
  have hpt : ∀ x : B.thickening.target.scheme,
      ∃ W : B.thickening.target.scheme.Opens, IsAffineOpen W ∧ x ∈ W := fun x ↦ by
    obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    exact ⟨W, hW, hxW⟩
  choose W hW hxW using hpt
  let V : ULift.{u + 1} B.thickening.target.scheme → B.thickening.target.scheme.Opens :=
    fun x ↦ W x.down
  have hcov : Sieve.generate (B.restrictOpenCover V).presieve₀ ∈ topology S B :=
    zariskiCovering_mem_topology S _
      (Thickening.isZariskiCovering_restrictOpenCover B V fun x ↦ ⟨ULift.up x, hxW x⟩)
  let φ : G.obj.obj (op B) → ∀ x : ULift.{u + 1} B.thickening.target.scheme,
      G.obj.obj (op ((bigAffineι S).obj
        (BigAffineThickening.restrictOpen B (hW x.down)))) :=
    fun s x ↦ G.obj.map (B.restrictOpenHom (V x)).op s
  have hφ : Function.Injective φ := by
    intro s t hst
    have hsh := (isSheaf_iff_isSheaf_of_type _ _).1
      ((sheafCompose (topology S) (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G).property
    refine (Presieve.isSeparatedFor_iff_generate.2 (hsh.isSeparated _ hcov)).ext ?_
    rintro _ _ ⟨x⟩
    exact congr_fun hst x
  have : ∀ x : ULift.{u + 1} B.thickening.target.scheme, Small.{u} (G.obj.obj (op
      ((bigAffineι S).obj (BigAffineThickening.restrictOpen B (hW x.down))))) :=
    fun x ↦ hG _
  exact small_of_injective hφ

/-- **Restriction of abelian sheaves with values in `AddCommGrpCat.{u}` from `CRIS(X/S)` to
`CRIS_aff(X/S)` is essentially surjective.**  A sheaf on `CRIS_aff(X/S)` is lifted to the universe
`u + 1`, extended by the Comparison Lemma there, and the extension, whose sections are `u`-small
by `small_sections_of_small_affine`, is shrunk back to the universe `u`. -/
instance instEssSurjSheafPushforward :
    ((bigAffineι S).sheafPushforwardContinuous AddCommGrpCat.{u}
      (bigAffineTopology S) (topology S)).EssSurj where
  mem_essImage N := by
    let F := (bigAffineι S).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (bigAffineTopology S) (topology S)
    let N' := (sheafCompose (bigAffineTopology S) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj N
    let G' := F.objPreimage N'
    let e : (bigAffineι S).op ⋙ G'.obj ≅ N.obj ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} :=
      (sheafToPresheaf _ _).mapIso (F.objObjPreimageIso N')
    have hsmall : ∀ U, Small.{u} (G'.obj.obj U) := fun U ↦
      small_sections_of_small_affine S G'
        (fun Y ↦ small_map (β := ULift.{u + 1} (N.obj.obj (op Y)))
          (e.app (op Y)).addCommGroupIsoToAddEquiv.toEquiv) U.unop
    let G := shrinkPresheaf G'.obj
    let eU := shrinkPresheafULiftIso G'.obj
    have hG : Presheaf.IsSheaf (topology S) G :=
      Presheaf.isSheaf_of_isSheaf_comp _ _ AddCommGrpCat.uliftFunctor.{u + 1, u}
        ((Presheaf.isSheaf_of_iso_iff eU).2 G'.property)
    let W := (Functor.whiskeringRight (BigAffineThickening S)ᵒᵖ _ _).obj
      AddCommGrpCat.uliftFunctor.{u + 1, u}
    let eW : W.obj ((bigAffineι S).op ⋙ G) ≅ W.obj N.obj :=
      Functor.isoWhiskerLeft (bigAffineι S).op eU ≪≫ e
    let eG : (bigAffineι S).op ⋙ G ≅ N.obj :=
      (AddCommGrpCat.uliftFunctorFullyFaithful.{u, u + 1}.whiskeringRight
        (BigAffineThickening S)ᵒᵖ).preimageIso (X := (bigAffineι S).op ⋙ G) (Y := N.obj) eW
    exact ⟨⟨G, hG⟩, ⟨(fullyFaithfulSheafToPresheaf _ _).preimageIso eG⟩⟩

/-- **The Comparison Lemma for `CRIS(X/S)` and `CRIS_aff(X/S)` at the universe `u`.** -/
instance instIsEquivalenceSheafPushforward :
    ((bigAffineι S).sheafPushforwardContinuous AddCommGrpCat.{u}
      (bigAffineTopology S) (topology S)).IsEquivalence :=
  Functor.IsEquivalence.mk

/-- **Sheaves of `𝒪_{X/S}`-modules on `CRIS(X/S)` are sheaves of modules on `CRIS_aff(X/S)`**
over the restriction of the structure sheaf, the equivalence being restriction along the
inclusion, at the module universe `u`. -/
noncomputable def moduleEquivalence :
    SheafOfModules.{u} (crystallineStructureSheaf S) ≌ SheafOfModules.{u} (structureSheaf S) :=
  Stacks.DenseSubsiteModules.moduleRestrictionEquivalence (bigAffineTopology S) (topology S)
    (bigAffineι S) (crystallineStructureSheaf S)

/-- The functor of `moduleEquivalence` is restriction along the inclusion. -/
theorem moduleEquivalence_functor :
    (moduleEquivalence S).functor =
      Stacks.DenseSubsiteModules.moduleRestriction (bigAffineTopology S) (topology S)
        (bigAffineι S) (crystallineStructureSheaf S) :=
  rfl

/-- The restriction to `CRIS_aff(X/S)` of the extension of a sheaf of modules `N` on
`CRIS_aff(X/S)` is `N`. -/
noncomputable def moduleEquivalenceInverseObjRestrictionIso
    (N : SheafOfModules.{u} (structureSheaf S)) :
    (Stacks.DenseSubsiteModules.moduleRestriction (bigAffineTopology S) (topology S)
      (bigAffineι S) (crystallineStructureSheaf S)).obj ((moduleEquivalence S).inverse.obj N) ≅
        N :=
  (moduleEquivalence S).counitIso.app N

end Crystalline.GlobalCrystallineSituation.BigAffine

end
