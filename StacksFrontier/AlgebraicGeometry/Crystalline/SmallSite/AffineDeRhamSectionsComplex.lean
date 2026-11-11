module

public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FormsRestrictionLocalizes
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.QuasicoherentImpliesLocal

/-!
# The sections of the de Rham complex of a crystal over an affine-over-affine object

Fix a global crystalline situation `(p, (S, I, γ), X)` of [Stacks, Tag 07MF] and a crystal in
quasi-coherent `𝒪_{X/S}`-modules `F` on the small crystalline site `Cris(X/S)`, with its de Rham
complex `K = F ⊗ Ω^•_{X/S}` of [Stacks, Proposition 60.23.1, Tag 07LM]
(`...SmallSite.crystalDeRhamSheafData`).  Over an affine-over-affine object `B` of `Cris(X/S)` —
ambient scheme affine, lying over an affine open of the base — the sections of `K` are the
explicit complex

`F(B) → F(B) ⊗ Ω¹_{X/S}(B) → F(B) ⊗ ⋀² Ω¹_{X/S}(B) → ⋯`

whose differentials are the extensions `m ⊗ ω ↦ ∇(m) ∧ ω + m ⊗ d ω` of the canonical connection
(`...SmallSite.AffineConnection.extDiff`).  This module builds that complex, its transition maps
`m ⊗ ω ↦ k^* m ⊗ k^* ω` along the morphisms of the affine-over-affine subsite, the identification
of the sections of `K` with it (the sheafification unit is bijective on the sections over such an
object, by the first equality of the proof of [Stacks, Tag 07LF]), and its consequence: a
restriction map `K^•(B') → K^•(B)` of sections of the de Rham complex is a quasi-isomorphism as
soon as the corresponding map of explicit complexes is one.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `affineDeRhamSectionsComplex hF B` — the complex `F(B) ⊗ ⋀^• Ω_{X/S}(B)`, as a `ℕ`-indexed
  cochain complex of abelian groups.
* `affineDeRhamSectionsMap hF k` — its transition map along a morphism `k : B ⟶ B'` of the
  affine-over-affine subsite.
* `affineDeRhamSectionsIso hF B` — the sections over `B` of the `ℕ`-indexed de Rham complex of
  `F` are `affineDeRhamSectionsComplex hF B`, lifted to the coefficient universe.

## Main results

* `affineDeRhamSectionsIso_naturality` — the identification carries the restriction maps of the
  de Rham complex to `affineDeRhamSectionsMap`.
* `quasiIso_natComplex_restriction`, `quasiIso_complex_restriction` — if
  `affineDeRhamSectionsMap hF k` is a quasi-isomorphism, so is the restriction map along `k` of
  the sections of the de Rham complex, `ℕ`-indexed or `ℤ`-indexed.

Along the way, `CategoryTheory.Functor.mapHomologicalComplexExtendIso` says that a functor
preserving zero morphisms commutes with the extension of complexes along an embedding of complex
shapes, naturally in the functor.

Nothing here says when `affineDeRhamSectionsMap hF k` is a quasi-isomorphism.

## References

* [Stacks Project, Proposition 60.23.1, Tag 07LM](https://stacks.math.columbia.edu/tag/07LM)
* [Stacks Project, Lemma 60.22.1, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry TensorProduct

universe u

noncomputable section

/-! ### Functors commute with the extension of complexes -/

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroObject C]
  [HasZeroMorphisms D] [HasZeroObject D] {ι ι' : Type*} {c : ComplexShape ι}
  {c' : ComplexShape ι'} (G : C ⥤ D) [G.PreservesZeroMorphisms] (K : HomologicalComplex C c)

/-- The terms of the extension of a complex, before and after applying a functor preserving
zero morphisms: the identity on the terms of `K`, and `G(0) ≅ 0` elsewhere. -/
def mapExtendXIso : ∀ o : Option ι,
    G.obj (HomologicalComplex.extend.X K o) ≅
      HomologicalComplex.extend.X ((G.mapHomologicalComplex c).obj K) o
  | some _ => Iso.refl _
  | none => G.mapZeroObject

/-- The identification of the terms commutes with the differentials of the extensions. -/
theorem mapExtendXIso_hom_comp_d (o o' : Option ι) :
    (G.mapExtendXIso K o).hom ≫
        HomologicalComplex.extend.d ((G.mapHomologicalComplex c).obj K) o o' =
      G.map (HomologicalComplex.extend.d K o o') ≫ (G.mapExtendXIso K o').hom := by
  match o, o' with
  | none, _ => simp [HomologicalComplex.extend.d]
  | some _, none => simp [HomologicalComplex.extend.d]
  | some a, some b =>
      change 𝟙 _ ≫ G.map (K.d a b) = G.map (K.d a b) ≫ 𝟙 _
      exact (Category.id_comp _).trans (Category.comp_id _).symm

/-- **A functor preserving zero morphisms commutes with the extension of complexes** along an
embedding of complex shapes. -/
def mapHomologicalComplexExtendIso (e : c.Embedding c') :
    (G.mapHomologicalComplex c').obj (K.extend e) ≅
      ((G.mapHomologicalComplex c).obj K).extend e :=
  HomologicalComplex.Hom.isoOfComponents (fun i' ↦ G.mapExtendXIso K (e.r i'))
    (fun i' j' _ ↦ G.mapExtendXIso_hom_comp_d K (e.r i') (e.r j'))

variable {G} {H : C ⥤ D} [H.PreservesZeroMorphisms] (α : G ⟶ H)

/-- The identification of the terms is natural in the functor. -/
theorem app_comp_mapExtendXIso_hom (o : Option ι) :
    α.app (HomologicalComplex.extend.X K o) ≫ (H.mapExtendXIso K o).hom =
      (G.mapExtendXIso K o).hom ≫
        HomologicalComplex.extend.mapX ((NatTrans.mapHomologicalComplex α c).app K) o := by
  match o with
  | none => exact (HomologicalComplex.extend.isZero_X _ rfl).eq_of_tgt _ _
  | some a =>
      change α.app (K.X a) ≫ 𝟙 _ = 𝟙 _ ≫ α.app (K.X a)
      exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **The commutation of functors with the extension of complexes is natural in the functor.** -/
theorem mapHomologicalComplexExtendIso_hom_naturality (e : c.Embedding c') :
    (NatTrans.mapHomologicalComplex α c').app (K.extend e) ≫
        (H.mapHomologicalComplexExtendIso K e).hom =
      (G.mapHomologicalComplexExtendIso K e).hom ≫
        HomologicalComplex.extendMap ((NatTrans.mapHomologicalComplex α c).app K) e := by
  ext i'
  exact app_comp_mapExtendXIso_hom K α (e.r i')

end CategoryTheory.Functor

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open AffineConnection AffineOverAffineCrystallineThickening

variable {S : GlobalCrystallineSituation.{u}} {F : SheafOfModules.{u} (structureSheaf S)}
  (hF : F.IsQuasicoherentOnSite)

/-! ### The explicit complex over an affine-over-affine object -/

/-- **The sections of the de Rham complex of `F` over an affine-over-affine object `B`**, as the
explicit complex `F(B) ⊗ ⋀^• Ω_{X/S}(B)` whose differentials are the extensions
`m ⊗ ω ↦ ∇(m) ∧ ω + m ⊗ d ω` of the canonical connection; they compose to zero because the
connection is integrable. -/
def affineDeRhamSectionsComplex (B : AffineOverAffineCrystallineThickening S) :
    CochainComplex AddCommGrpCat.{u} ℕ :=
  CochainComplex.of
    (fun a ↦ AddCommGrpCat.of (F.val.obj (op B.obj) ⊗[GlobalCrystallineSituation.crysFormRing S
      B.obj.obj] ⋀[GlobalCrystallineSituation.crysFormRing S B.obj.obj]^a
        ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj.obj))))
    (fun a ↦ AddCommGrpCat.ofHom (extDiff B.top_le_preimage_baseOpen B.isAffineOpen_baseOpen
      (bijective_crysExtensionSectionsMap_affine hF B) a))
    (fun a ↦ by
      ext x
      exact extDiff_comp_extDiff _ _ _ (injective_crysSecondExtensionSectionsMap_affine hF B) a x)

/-- The differentials of the explicit complex are the extensions of the canonical connection. -/
theorem affineDeRhamSectionsComplex_d (B : AffineOverAffineCrystallineThickening S) (a : ℕ) :
    (affineDeRhamSectionsComplex hF B).d a (a + 1) =
      AddCommGrpCat.ofHom (extDiff B.top_le_preimage_baseOpen B.isAffineOpen_baseOpen
        (bijective_crysExtensionSectionsMap_affine hF B) a) := by
  unfold affineDeRhamSectionsComplex
  apply CochainComplex.of_d

/-- **The transition map of the explicit complex along a morphism `k : B ⟶ B'`** of the
affine-over-affine subsite, `m ⊗ ω ↦ k^* m ⊗ k^* ω` in every degree; it commutes with the
differentials because the canonical connection is natural. -/
def affineDeRhamSectionsMap {B B' : AffineOverAffineCrystallineThickening S} (k : B ⟶ B') :
    affineDeRhamSectionsComplex hF B' ⟶ affineDeRhamSectionsComplex hF B :=
  CochainComplex.ofHom
    (fun a ↦ AddCommGrpCat.ofHom (restrictForms F k.hom a))
    (fun a ↦ by
      rw [affineDeRhamSectionsComplex_d, affineDeRhamSectionsComplex_d]
      ext x
      exact (extDiff_naturality B.top_le_preimage_baseOpen B.isAffineOpen_baseOpen
        B'.top_le_preimage_baseOpen B'.isAffineOpen_baseOpen
        (bijective_crysExtensionSectionsMap_affine hF B)
        (bijective_crysExtensionSectionsMap_affine hF B') k.hom a x))

/-- The degree-`a` component of the transition map is `m ⊗ ω ↦ k^* m ⊗ k^* ω`. -/
@[simp]
theorem affineDeRhamSectionsMap_f {B B' : AffineOverAffineCrystallineThickening S} (k : B ⟶ B')
    (a : ℕ) :
    (affineDeRhamSectionsMap hF k).f a = AddCommGrpCat.ofHom (restrictForms F k.hom a) :=
  rfl

/-! ### The sections of the de Rham complex over an affine-over-affine object -/

/-- The map from the explicit sections to the sections of the sheaf `F ⊗ Ω^a_{X/S}`: the inverse
of the identification of the presheaf sections, followed by the sheafification unit. -/
def affineDeRhamSectionsToSheaf (B : AffineOverAffineCrystallineThickening S) (a : ℕ) :
    ULift.{u + 1} (F.val.obj (op B.obj) ⊗[GlobalCrystallineSituation.crysFormRing S B.obj.obj]
        ⋀[GlobalCrystallineSituation.crysFormRing S B.obj.obj]^a
          ↥((GlobalCrystallineSituation.crysDifferentials S).obj (op B.obj.obj))) →+
      (tensorDifferentialFormsSheaf F a).obj.obj (op B.obj) :=
  (toSheafify (smallTopology S) (tensorFormsULift F a)).app (op B.obj) |>.hom.comp
    ((AddEquiv.ulift.symm.toAddMonoidHom.comp
      (tensorFormsSectionsEquiv F a B.obj).symm.toAddMonoidHom).comp
        AddEquiv.ulift.toAddMonoidHom)

include hF in
/-- The map from the explicit sections to the sections of the sheaf is bijective: over an
affine-over-affine object the sheafification unit of `F ⊗ Ω^a_{X/S}` is bijective on sections. -/
theorem bijective_affineDeRhamSectionsToSheaf (B : AffineOverAffineCrystallineThickening S)
    (a : ℕ) : Function.Bijective (affineDeRhamSectionsToSheaf (F := F) B a) :=
  (bijective_toSheafify_app_tensorDifferentialFormsPresheaf_of_isAffine
      B.top_le_preimage_baseOpen B.isAffineOpen_baseOpen
      (isLocallyQuasiCoherent_of_isQuasicoherentOnSite F hF)).comp
    ((AddEquiv.ulift.symm.bijective.comp (tensorFormsSectionsEquiv F a B.obj).symm.bijective).comp
      AddEquiv.ulift.bijective)

/-- The degreewise identification of the explicit sections with the sections of the sheaf. -/
def affineDeRhamSectionsXIso (B : AffineOverAffineCrystallineThickening S) (a : ℕ) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.obj ((affineDeRhamSectionsComplex hF B).X a) ≅
      (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op B.obj)).obj ((crystalDeRhamSheafData hF).natComplex.X a) :=
  (AddEquiv.ofBijective (affineDeRhamSectionsToSheaf B a)
    (bijective_affineDeRhamSectionsToSheaf hF B a)).toAddCommGrpIso

/-- The degreewise identification on an element. -/
theorem affineDeRhamSectionsXIso_hom_apply (B : AffineOverAffineCrystallineThickening S) (a : ℕ)
    (x : AddCommGrpCat.uliftFunctor.{u + 1, u}.obj ((affineDeRhamSectionsComplex hF B).X a)) :
    (affineDeRhamSectionsXIso hF B a).hom x =
      (toSheafify (smallTopology S) (tensorFormsULift F a)).app (op B.obj)
        (ULift.up ((tensorFormsSectionsEquiv F a B.obj).symm x.down)) :=
  rfl

/-- The degreewise identification commutes with the differentials. -/
theorem affineDeRhamSectionsXIso_hom_comp_d (B : AffineOverAffineCrystallineThickening S)
    (a : ℕ) :
    (affineDeRhamSectionsXIso hF B a).hom ≫
        (((sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
          (evaluation _ _).obj (op B.obj)).mapHomologicalComplex _).obj
            (crystalDeRhamSheafData hF).natComplex).d a (a + 1) =
      (((AddCommGrpCat.uliftFunctor.{u + 1, u}).mapHomologicalComplex _).obj
          (affineDeRhamSectionsComplex hF B)).d a (a + 1) ≫
        (affineDeRhamSectionsXIso hF B (a + 1)).hom := by
  have hd : (crystalDeRhamSheafData hF).natComplex.d a (a + 1) = crystalDeRhamDifferential hF a :=
    by unfold CrystalDeRhamSheafData.natComplex; apply CochainComplex.of_d
  rw [Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_obj_d, hd,
    affineDeRhamSectionsComplex_d]
  ext x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    affineDeRhamSectionsXIso_hom_apply, affineDeRhamSectionsXIso_hom_apply]
  refine (crystalDeRhamDifferential_app_toSheafify hF a B _).trans ?_
  refine congrArg (fun y ↦ (toSheafify (smallTopology S) (tensorFormsULift F (a + 1))).app
    (op B.obj) (ULift.up y)) ?_
  exact congrArg (tensorFormsSectionsEquiv F (a + 1) B.obj).symm
    (congrArg (extDiff B.top_le_preimage_baseOpen B.isAffineOpen_baseOpen
        (bijective_crysExtensionSectionsMap_affine hF B) a)
      ((tensorFormsSectionsEquiv F a B.obj).apply_symm_apply x.down))

/-- **The sections over an affine-over-affine object `B` of the de Rham complex of `F` are the
explicit complex `F(B) ⊗ ⋀^• Ω_{X/S}(B)`**, lifted to the coefficient universe: degreewise the
sheafification unit, bijective over `B`, composed with the identification of the presheaf
sections. -/
def affineDeRhamSectionsIso (B : AffineOverAffineCrystallineThickening S) :
    ((sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1} ⋙
        (evaluation _ _).obj (op B.obj)).mapHomologicalComplex _).obj
        (crystalDeRhamSheafData hF).natComplex ≅
      (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex _).obj
        (affineDeRhamSectionsComplex hF B) :=
  (HomologicalComplex.Hom.isoOfComponents (affineDeRhamSectionsXIso hF B) (fun a b h ↦ by
    obtain rfl : a + 1 = b := h
    exact affineDeRhamSectionsXIso_hom_comp_d hF B a)).symm

/-- The degree-`a` component of the inverse of `affineDeRhamSectionsIso`. -/
theorem affineDeRhamSectionsIso_inv_f (B : AffineOverAffineCrystallineThickening S) (a : ℕ) :
    (affineDeRhamSectionsIso hF B).inv.f a = (affineDeRhamSectionsXIso hF B a).hom :=
  rfl

/-- **The identification of the sections is natural**: it carries the restriction map of the
de Rham complex along a morphism `k : B ⟶ B'` of the affine-over-affine subsite to the transition
map `affineDeRhamSectionsMap hF k` of the explicit complexes. -/
theorem affineDeRhamSectionsIso_naturality {B B' : AffineOverAffineCrystallineThickening S}
    (k : B ⟶ B') :
    (NatTrans.mapHomologicalComplex (Functor.whiskerLeft
        (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1})
          ((evaluation _ _).map k.hom.op)) (ComplexShape.up ℕ)).app
        (crystalDeRhamSheafData hF).natComplex ≫ (affineDeRhamSectionsIso hF B).hom =
      (affineDeRhamSectionsIso hF B').hom ≫
        (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex _).map
          (affineDeRhamSectionsMap hF k) := by
  have h : (affineDeRhamSectionsIso hF B').inv ≫
      (NatTrans.mapHomologicalComplex (Functor.whiskerLeft
        (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1})
          ((evaluation _ _).map k.hom.op)) (ComplexShape.up ℕ)).app
        (crystalDeRhamSheafData hF).natComplex =
      (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex _).map
          (affineDeRhamSectionsMap hF k) ≫ (affineDeRhamSectionsIso hF B).inv := by
    ext a x
    simp only [HomologicalComplex.comp_f, affineDeRhamSectionsIso_inv_f,
      NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplex_map_f,
      ConcreteCategory.comp_apply]
    rw [affineDeRhamSectionsXIso_hom_apply, affineDeRhamSectionsXIso_hom_apply]
    refine (NatTrans.naturality_apply (toSheafify (smallTopology S) (tensorFormsULift F a))
      k.hom.op _).symm.trans ?_
    refine congrArg (fun y ↦ (toSheafify (smallTopology S) (tensorFormsULift F a)).app
      (op B.obj) (ULift.up y)) ?_
    refine (AddEquiv.eq_symm_apply _).mpr ?_
    exact tensorFormsSectionsEquiv_map F k.hom a x.down
  rw [← cancel_epi (affineDeRhamSectionsIso hF B').inv, Iso.inv_hom_id_assoc, ← Category.assoc,
    h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-! ### Quasi-isomorphisms of the sections -/

/-- **A restriction map of the sections of the `ℕ`-indexed de Rham complex is a
quasi-isomorphism** along a morphism `k : B ⟶ B'` of the affine-over-affine subsite, as soon as
the transition map of the explicit complexes is one. -/
theorem quasiIso_natComplex_restriction {B B' : AffineOverAffineCrystallineThickening S}
    (k : B ⟶ B') (hk : QuasiIso (affineDeRhamSectionsMap hF k)) :
    QuasiIso ((NatTrans.mapHomologicalComplex (Functor.whiskerLeft
        (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1})
          ((evaluation _ _).map k.hom.op)) (ComplexShape.up ℕ)).app
        (crystalDeRhamSheafData hF).natComplex) := by
  have : QuasiIso ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex _).map
      (affineDeRhamSectionsMap hF k)) :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ _).mpr hk
  rw [← quasiIso_iff_comp_right _ (affineDeRhamSectionsIso hF B).hom,
    affineDeRhamSectionsIso_naturality]
  infer_instance

/-- **A restriction map `K^•(B') → K^•(B)` of the sections of the de Rham complex `K` of `F` is a
quasi-isomorphism** along a morphism `k : B ⟶ B'` of the affine-over-affine subsite, as soon as
the transition map of the explicit complexes `F(B') ⊗ ⋀^• Ω_{X/S}(B') → F(B) ⊗ ⋀^• Ω_{X/S}(B)`
is one.  Here `K` is the `ℤ`-indexed complex, the extension by zero of the `ℕ`-indexed one, and
taking sections commutes with that extension. -/
theorem quasiIso_complex_restriction {B B' : AffineOverAffineCrystallineThickening S}
    (k : B ⟶ B') (hk : QuasiIso (affineDeRhamSectionsMap hF k)) :
    QuasiIso ((NatTrans.mapHomologicalComplex (Functor.whiskerLeft
        (sheafToPresheaf (smallTopology S) AddCommGrpCat.{u + 1})
          ((evaluation _ _).map k.hom.op)) (ComplexShape.up ℤ)).app
        (crystalDeRhamSheafData hF).complex) := by
  have hN := quasiIso_natComplex_restriction hF k hk
  refine (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk
    (Functor.mapHomologicalComplexExtendIso _ (crystalDeRhamSheafData hF).natComplex
      ComplexShape.embeddingUpNat)
    (Functor.mapHomologicalComplexExtendIso _ (crystalDeRhamSheafData hF).natComplex
      ComplexShape.embeddingUpNat)
    (Functor.mapHomologicalComplexExtendIso_hom_naturality _ _ _).symm)).mpr ?_
  exact (HomologicalComplex.quasiIso_extendMap_iff _ _).mpr hN

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
