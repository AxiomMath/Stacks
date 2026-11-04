module

public import StacksFrontier.AlgebraicGeometry.CoefficientNat.Sections
public import StacksFrontier.Algebra.Homology.Embedding.UpNatZero

/-!
# The absolute Čech complex of [Stacks, Tag 01XL] is a resolution

Let `X` be a scheme, let `𝒰` be a finite affine open covering of `X` given by an affine open
cover `T`, and let `ℱ` be a quasi-coherent `𝒪_X`-module.  The absolute Čech complex
`𝔠 ⁼(𝒰, ℱ)` of [Stacks, Tag 01XL] is the Čech complex, over the site `Over X`, of the
coefficient presheaf `A ↦ (A.hom)_* (A.hom)^* ℱ`.  [Stacks, Tag 02FU] says that the
augmentation `ℱ ⟶ 𝔠 ⁼(𝒰, ℱ)` is a quasi-isomorphism, and is proved in this repository for the
Čech complex over the site `X.Opens` of open sets, with the universe-enlarged coefficients
`Stacks.CechTotalComplex.CoveringResolution.cechDiagram`.

This file crosses between the two descriptions and transports the resolution, finishing with a
natural quasi-isomorphism `ℱ[0] ⟶ 𝔠 ⁼(𝒰, ℱ)` of `ℤ`-indexed complexes.

## Main results

* `absoluteCechOpensPresheafIso`: **the coefficient presheaves agree** — the coefficient
  presheaf of [Stacks, Tag 01XL] restricted to the open sets of `X` is the Čech diagram of
  [Stacks, Tag 02FU], naturally in the open set and in the quasi-coherent module.
* `absoluteCechComplexCoveringIso`: consequently the absolute Čech complex of
  [Stacks, Tag 01XL] is the Čech complex of [Stacks, Tag 02FU] for the family of open ranges of
  the affine open cover.
* `quasiIso_augOpens_app`: the augmentation of [Stacks, Tag 02FU], with the universe enlargement
  removed, is a quasi-isomorphism.
* `singleExtendIso`: the extension along `ComplexShape.embeddingUpNat` of a complex concentrated
  in degree `0` is the `ℤ`-indexed complex concentrated in degree `0`, naturally in the object.
* `absoluteCechAugZ` and `quasiIso_absoluteCechAugZ_app`: **the augmentation
  `ℱ[0] ⟶ 𝔠 ⁼(𝒰, ℱ)` of `ℤ`-indexed complexes is a quasi-isomorphism**, naturally in the
  quasi-coherent module.

## Implementation notes

The comparison of coefficient presheaves at a *fixed* open set is
`Stacks.Tag01XLCoefficientIso.pullbackPushforwardInfIso`; what is proved here is its naturality
in the open set, `pullbackPushforwardInfIso_naturality`.  Both sides of that square become
presheaf restriction maps once the inverse image is replaced by restriction along the open
immersion, which is `Stacks.Tag01XLCoefficientNat.relativeUnit_app_app` for the
[Stacks, Tag 01XL] side and two `rfl`s for the [Stacks, Tag 02FU] side; the lattice of open sets
is thin, so the two composites of restriction maps agree.

Several identifications that hold by `rfl` are stated as separate one-line lemmas rather than
used inline.  The reason is cost, not taste: the single `rfl` identifying
`((absoluteCechOpensPresheaf X).obj F).map g` with its `relativeUnit'` spelling exceeds the
kernel's default budget, while the three steps it factors into — `absoluteCechOpensPresheaf_map`,
`absoluteCechPresheaf_obj_map` and `relativeMonad_map_opensOver` — each fit comfortably.  For the
same reason the associativity rearrangements in the naturality proofs are applied as terms rather
than through `rw`, which cannot see past the two definitionally equal spellings of the category
of `𝒪_X`-modules.

## References

* [Stacks Project, Tag 01XL](https://stacks.math.columbia.edu/tag/01XL)
* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace Stacks.CechSiteChange

open Stacks.Tag01XLCoefficientIso Stacks.Tag01XLCoefficientNat
open Stacks.CechTotalComplex.CoveringResolution

variable {X : Scheme.{u}}

/-! ### The restriction maps of the coefficient system, transported -/

/-- **The restriction map of the coefficient system of [Stacks, Tag 01XL], on sections**, for a
factorisation `u ≫ b = a` of open immersions:  conjugated by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` it is the presheaf restriction map
`ℱ(b ''ᵁ b ⁻¹ᵁ U) ⟶ ℱ(a ''ᵁ a ⁻¹ᵁ U)`. -/
theorem relativeUnit'_conj_app_app {Y Z : Scheme.{u}} (u : Y ⟶ Z) (b : Z ⟶ X) (a : Y ⟶ X)
    (hw : u ≫ b = a) [IsOpenImmersion u] [IsOpenImmersion b] [IsOpenImmersion a]
    (M : X.Modules) (U : X.Opens) (k : a ''ᵁ (a ⁻¹ᵁ U) ≤ b ''ᵁ (b ⁻¹ᵁ U)) :
    ((pushforward b).map ((restrictFunctorIsoPullback b).hom.app M)).app U ≫
        ((Stacks.AlgebraicGeometry.RelativeCech.relativeUnit' u b a hw).app M).app U =
      M.presheaf.map (homOfLE k).op ≫
        ((pushforward a).map ((restrictFunctorIsoPullback a).hom.app M)).app U := by
  subst hw
  have h1 : Stacks.AlgebraicGeometry.RelativeCech.relativeUnit' u b (u ≫ b) rfl =
      Stacks.AlgebraicGeometry.RelativeCech.relativeUnit u b := Category.comp_id _
  rw [h1, relativeUnit_app_app u b M U]
  rfl

/-! ### The Čech diagram of [Stacks, Tag 02FU] at a scheme -/

/-- **The Čech diagram of [Stacks, Tag 02FU] at a scheme**: the open set `V` is sent to the
direct image of the restriction of a module sheaf to `V`, contravariantly in `V`.  The type is
written with `X.Modules` so that every morphism below is formed in that category. -/
noncomputable def cechDiagramOpens (X : Scheme.{u}) : X.Modules ⥤ ((X.Opens)ᵒᵖ ⥤ X.Modules) :=
  cechDiagram.{u, u, u, u} X.carrier X.ringCatSheaf

/-- The direct image of the restriction of a module sheaf to a fixed open set, with no universe
enlargement, at a scheme. -/
noncomputable def infDirectImageOpens (X : Scheme.{u}) (V : X.Opens) : X.Modules ⥤ X.Modules :=
  infDirectImage.{u, u, u} X.carrier X.ringCatSheaf V

/-- The universe enlargement of [Stacks, Tag 02FU], inserted: at the equal universes of a scheme
it is an isomorphism onto the value of the Čech diagram at the open set. -/
noncomputable def infUliftCompare (X : Scheme.{u}) (V : X.Opens) (M : X.Modules) :
    (infDirectImageOpens X V).obj M ⟶ ((cechDiagramOpens X).obj M).obj (op V) :=
  (infPushforwardFunctorIso.{u, u, u, u} X.carrier X.ringCatSheaf V).inv.app M

/-- The direct image of the restriction along the inclusion of an open subscheme, compared with
the direct image of the restriction to the open set. -/
noncomputable def restrictInfCompare (X : Scheme.{u}) (V : X.Opens) (M : X.Modules) :
    (pushforward V.ι).obj ((restrictFunctor V.ι).obj M) ⟶ (infDirectImageOpens X V).obj M :=
  (restrictPushforwardInfIso X V).hom.app M

/-- **The coefficient comparison at one open set, with the inverse image replaced by
restriction**:  `(V.ι)_* (V.ι)^* ℱ` against the value at `V` of the Čech diagram of
[Stacks, Tag 02FU]. -/
noncomputable def coeffCompare (X : Scheme.{u}) (V : X.Opens) (M : X.Modules) :
    (pushforward V.ι).obj ((restrictFunctor V.ι).obj M) ⟶
      ((cechDiagramOpens X).obj M).obj (op V) :=
  restrictInfCompare X V M ≫ infUliftCompare X V M

/-- The coefficient comparison of `Stacks.Tag01XLCoefficientIso.pullbackPushforwardInfIso`, with
the inverse image replaced by restriction, is `coeffCompare`. -/
theorem restrict_comp_pullbackPushforwardInfIso (X : Scheme.{u}) (V : X.Opens) (M : X.Modules) :
    (pushforward V.ι).map ((restrictFunctorIsoPullback V.ι).hom.app M) ≫
        (pullbackPushforwardInfIso X V).hom.app M = coeffCompare X V M := by
  have e : (pullbackPushforwardInfIso X V).hom.app M =
      (pushforward V.ι).map ((restrictFunctorIsoPullback V.ι).inv.app M) ≫
        coeffCompare X V M := rfl
  rw [e]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans (congrArg (fun z => z ≫ coeffCompare X V M) ?_) (Category.id_comp _)
  exact ((pushforward V.ι).map_comp _ _).symm.trans
    ((congrArg (pushforward V.ι).map ((restrictFunctorIsoPullback V.ι).hom_inv_id_app M)).trans
      (CategoryTheory.Functor.map_id _ _))

/-- `restrict_comp_pullbackPushforwardInfIso`, on sections over an open set. -/
theorem restrict_comp_pullbackPushforwardInfIso_app (X : Scheme.{u}) (V : X.Opens)
    (M : X.Modules) (U : X.Opens) :
    ((pushforward V.ι).map ((restrictFunctorIsoPullback V.ι).hom.app M)).app U ≫
        Scheme.Modules.Hom.app (X := X) ((pullbackPushforwardInfIso X V).hom.app M) U =
      (coeffCompare X V M).app U :=
  congrArg (fun z => Scheme.Modules.Hom.app (X := X) z U)
    (restrict_comp_pullbackPushforwardInfIso X V M)

/-- The coefficient comparison on sections is restriction along `V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U ⊓ V`,
followed by the universe enlargement. -/
theorem coeffCompare_app (X : Scheme.{u}) (V : X.Opens) (M : X.Modules) (U : X.Opens) :
    (coeffCompare X V M).app U =
      M.presheaf.map (eqToHom (image_preimage_ι X V U).symm).op ≫
        (infUliftCompare X V M).app U :=
  rfl

/-- The universe enlargement commutes with the restriction maps of the Čech diagram:  on
sections both are a presheaf restriction map wrapped in a `ULift`. -/
theorem infUliftCompare_naturality (X : Scheme.{u}) {V W : X.Opens} (hle : V ≤ W)
    (M : X.Modules) (U : X.Opens) :
    (infUliftCompare X W M).app U ≫
        (((cechDiagramOpens X).obj M).map (homOfLE hle).op).app U =
      M.presheaf.map (homOfLE (inf_le_inf_left U hle)).op ≫ (infUliftCompare X V M).app U :=
  rfl

/-- The image of the preimage of an open set is monotone in the open subscheme. -/
theorem image_preimage_mono (X : Scheme.{u}) {V W : X.Opens} (hle : V ≤ W) (U : X.Opens) :
    V.ι ''ᵁ (V.ι ⁻¹ᵁ U) ≤ W.ι ''ᵁ (W.ι ⁻¹ᵁ U) := by
  rw [image_preimage_ι, image_preimage_ι]
  exact inf_le_inf_left U hle

/-- The intersection with the smaller open subscheme lies inside the image of the preimage under
the inclusion of the larger one. -/
theorem inf_le_image_preimage (X : Scheme.{u}) {V W : X.Opens} (hle : V ≤ W) (U : X.Opens) :
    U ⊓ V ≤ W.ι ''ᵁ (W.ι ⁻¹ᵁ U) := by
  rw [image_preimage_ι]
  exact inf_le_inf_left U hle

/-- **The coefficient comparison is natural in the open set**, on sections:  all four maps of the
square are presheaf restriction maps, and the lattice of open sets is thin. -/
theorem coeffCompare_naturality (X : Scheme.{u}) {V W : X.Opens} (hle : V ≤ W) (M : X.Modules)
    (U : X.Opens) :
    M.presheaf.map (homOfLE (image_preimage_mono X hle U)).op ≫ (coeffCompare X V M).app U =
      (coeffCompare X W M).app U ≫
        (((cechDiagramOpens X).obj M).map (homOfLE hle).op).app U := by
  rw [coeffCompare_app X V M U, coeffCompare_app X W M U]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans (congrArg (fun z => z ≫ (infUliftCompare X V M).app U)
    (thin_map_comp₂ M.presheaf _ _ (homOfLE (inf_le_image_preimage X hle U)).op)) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (fun z => M.presheaf.map
      (eqToHom (image_preimage_ι X W U).symm).op ≫ z) (infUliftCompare_naturality X hle M U))
  exact (congrArg (fun z => z ≫ (infUliftCompare X V M).app U)
    (thin_map_comp₂ M.presheaf _ _ _).symm).trans (Category.assoc _ _ _)

/-- The comparison of restriction along an open immersion with the inverse image, pushed forward:
an isomorphism, by which the two descriptions of the coefficient system are conjugate. -/
noncomputable def restrictPushforwardIsoPullback (X : Scheme.{u}) (W : X.Opens)
    (M : X.Modules) :
    (pushforward W.ι).obj ((restrictFunctor W.ι).obj M) ⟶
      (pushforward W.ι).obj ((Scheme.Modules.pullback W.ι).obj M) :=
  (pushforward W.ι).map ((restrictFunctorIsoPullback W.ι).hom.app M)

/-- **The coefficient comparison of [Stacks, Tag 01XL] against [Stacks, Tag 02FU] is natural in
the open set.**  Both sides are conjugated by `restrictPushforwardIsoPullback`, after which the
square is `coeffCompare_naturality`. -/
theorem pullbackPushforwardInfIso_naturality (X : Scheme.{u}) {V W : X.Opens} (hle : V ≤ W)
    (M : X.Modules) :
    (Stacks.AlgebraicGeometry.RelativeCech.relativeUnit' (X.homOfLE hle) W.ι V.ι
          (X.homOfLE_ι hle)).app M ≫ (pullbackPushforwardInfIso X V).hom.app M =
      (pullbackPushforwardInfIso X W).hom.app M ≫
        ((cechDiagramOpens X).obj M).map (homOfLE hle).op := by
  have hiso : IsIso (restrictPushforwardIsoPullback X W M) :=
    inferInstanceAs (IsIso ((pushforward W.ι).map ((restrictFunctorIsoPullback W.ι).hom.app M)))
  refine (cancel_epi (restrictPushforwardIsoPullback X W M)).mp ?_
  refine Scheme.Modules.hom_ext _ _ fun U => ?_
  refine (Scheme.Modules.Hom.comp_app _ _).trans ?_
  refine Eq.trans (congrArg (fun z => (restrictPushforwardIsoPullback X W M).app U ≫ z)
    (Scheme.Modules.Hom.comp_app _ _)) ?_
  refine Eq.trans ?_ (Scheme.Modules.Hom.comp_app _ _).symm
  refine Eq.trans ?_ (congrArg (fun z => (restrictPushforwardIsoPullback X W M).app U ≫ z)
    (Scheme.Modules.Hom.comp_app _ _)).symm
  refine ((Category.assoc _ _ _).symm.trans ?_).trans (Category.assoc _ _ _)
  refine Eq.trans (congrArg (fun z => z ≫ Scheme.Modules.Hom.app (X := X)
      ((pullbackPushforwardInfIso X V).hom.app M) U)
    (relativeUnit'_conj_app_app (X.homOfLE hle) W.ι V.ι (X.homOfLE_ι hle) M U
      (image_preimage_mono X hle U))) ?_
  refine (Category.assoc _ _ _).trans ?_
  refine Eq.trans (congrArg (fun z =>
      M.presheaf.map (homOfLE (image_preimage_mono X hle U)).op ≫ z)
    (restrict_comp_pullbackPushforwardInfIso_app X V M U)) ?_
  exact (coeffCompare_naturality X hle M U).trans
    (congrArg (fun z => z ≫ (((cechDiagramOpens X).obj M).map (homOfLE hle).op).app U)
      (restrict_comp_pullbackPushforwardInfIso_app X W M U).symm)

/-! ### The coefficient presheaves agree -/

/-- The restriction maps of the coefficient presheaf of [Stacks, Tag 01XL] over the site of open
sets are those of the presheaf of monads along `opensOver`. -/
theorem absoluteCechOpensPresheaf_map (X : Scheme.{u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    {A B : (X.Opens)ᵒᵖ} (g : A ⟶ B) :
    ((Stacks.CechSiteChange.absoluteCechOpensPresheaf X).obj F).map g =
      ((Stacks.AlgebraicGeometry.CechPushforwardComplex.absoluteCechPresheaf X).obj F).map
        ((opensOver X).op.map g) :=
  rfl

/-- The restriction maps of the absolute Čech coefficient presheaf are the components of the
presheaf of monads. -/
theorem absoluteCechPresheaf_obj_map (X : Scheme.{u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    {A B : (Over X)ᵒᵖ} (ψ : A ⟶ B) :
    ((Stacks.AlgebraicGeometry.CechPushforwardComplex.absoluteCechPresheaf X).obj F).map ψ =
      ((Stacks.AlgebraicGeometry.RelativeCech.relativeMonad X).map ψ).app F.obj :=
  rfl

/-- The presheaf of monads, along an inclusion of open sets, is the canonical restriction map of
the coefficient system. -/
theorem relativeMonad_map_opensOver (X : Scheme.{u}) {A B : (X.Opens)ᵒᵖ} (g : A ⟶ B) :
    (Stacks.AlgebraicGeometry.RelativeCech.relativeMonad X).map ((opensOver X).op.map g) =
      Stacks.AlgebraicGeometry.RelativeCech.relativeUnit' (X.homOfLE (leOfHom g.unop))
        A.unop.ι B.unop.ι (X.homOfLE_ι (leOfHom g.unop)) :=
  rfl

/-- The restriction maps of the coefficient presheaf of [Stacks, Tag 01XL] over the site of open
sets, written out. -/
theorem absoluteCechOpensPresheaf_obj_map (X : Scheme.{u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    {A B : (X.Opens)ᵒᵖ} (g : A ⟶ B) :
    ((Stacks.CechSiteChange.absoluteCechOpensPresheaf X).obj F).map g =
      (Stacks.AlgebraicGeometry.RelativeCech.relativeUnit' (X.homOfLE (leOfHom g.unop))
        A.unop.ι B.unop.ι (X.homOfLE_ι (leOfHom g.unop))).app F.obj :=
  (absoluteCechOpensPresheaf_map X F g).trans
    ((absoluteCechPresheaf_obj_map X F ((opensOver X).op.map g)).trans
      (congrArg (fun z => z.app F.obj) (relativeMonad_map_opensOver X g)))

/-- The naturality in the open set of the coefficient comparison, in the form the isomorphism of
presheaves consumes. -/
theorem absoluteCechOpensPresheafIsoApp_naturality (X : Scheme.{u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
    {A B : (X.Opens)ᵒᵖ} (g : A ⟶ B) :
    ((Stacks.CechSiteChange.absoluteCechOpensPresheaf X).obj F).map g ≫
        ((pullbackPushforwardInfIso X B.unop).app F.obj).hom =
      ((pullbackPushforwardInfIso X A.unop).app F.obj).hom ≫
        ((cechDiagramOpens X).obj F.obj).map g := by
  refine Eq.trans (congrArg (fun z => z ≫
    ((pullbackPushforwardInfIso X B.unop).app F.obj).hom)
    (absoluteCechOpensPresheaf_obj_map X F g)) ?_
  exact pullbackPushforwardInfIso_naturality X (leOfHom g.unop) F.obj

/-- **At a fixed quasi-coherent module, the coefficient presheaf of [Stacks, Tag 01XL] over the
site of open sets is the Čech diagram of [Stacks, Tag 02FU].** -/
noncomputable def absoluteCechOpensPresheafIsoApp (X : Scheme.{u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (Stacks.CechSiteChange.absoluteCechOpensPresheaf X).obj F ≅
      (cechDiagramOpens X).obj F.obj :=
  NatIso.ofComponents (fun A => (pullbackPushforwardInfIso X A.unop).app F.obj)
    (fun {_ _} g => absoluteCechOpensPresheafIsoApp_naturality X F g)

/-- The restriction maps in the quasi-coherent module of the coefficient presheaf of
[Stacks, Tag 01XL] over the site of open sets. -/
theorem absoluteCechOpensPresheaf_map_app (X : Scheme.{u})
    {F G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory} (φ : F ⟶ G)
    (A : (X.Opens)ᵒᵖ) :
    ((Stacks.CechSiteChange.absoluteCechOpensPresheaf X).map φ).app A =
      (Scheme.Modules.pullback A.unop.ι ⋙ pushforward A.unop.ι).map
        ((ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf)).map φ) :=
  rfl

/-- The action on morphisms of the Čech diagram of [Stacks, Tag 02FU], at one open set. -/
theorem cechDiagramOpens_map_app (X : Scheme.{u})
    {F G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory} (φ : F ⟶ G)
    (A : (X.Opens)ᵒᵖ) :
    ((ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        cechDiagramOpens X).map φ).app A =
      (infPushforwardFunctor.{u, u, u, u} X.carrier X.ringCatSheaf A.unop).map
        ((ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf)).map φ) :=
  rfl

/-- The naturality in the quasi-coherent module of the coefficient comparison. -/
theorem absoluteCechOpensPresheafIso_naturality (X : Scheme.{u})
    {F G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory} (φ : F ⟶ G)
    (A : (X.Opens)ᵒᵖ) :
    ((Stacks.CechSiteChange.absoluteCechOpensPresheaf X).map φ).app A ≫
        ((pullbackPushforwardInfIso X A.unop).app G.obj).hom =
      ((pullbackPushforwardInfIso X A.unop).app F.obj).hom ≫
        ((ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
          cechDiagramOpens X).map φ).app A :=
  (congrArg (fun z => z ≫ ((pullbackPushforwardInfIso X A.unop).app G.obj).hom)
      (absoluteCechOpensPresheaf_map_app X φ A)).trans
    (((pullbackPushforwardInfIso X A.unop).hom.naturality
        ((ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf)).map φ)).trans
      (congrArg (fun z => ((pullbackPushforwardInfIso X A.unop).app F.obj).hom ≫ z)
        (cechDiagramOpens_map_app X φ A).symm))

/-- **The coefficient presheaf of [Stacks, Tag 01XL] over the site of open sets is the Čech
diagram of [Stacks, Tag 02FU]**, naturally in the open set and in the quasi-coherent module. -/
noncomputable def absoluteCechOpensPresheafIso (X : Scheme.{u}) :
    Stacks.CechSiteChange.absoluteCechOpensPresheaf X ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙ cechDiagramOpens X :=
  NatIso.ofComponents (absoluteCechOpensPresheafIsoApp X)
    (fun {_ _} φ => NatTrans.ext (funext fun A =>
      absoluteCechOpensPresheafIso_naturality X φ A))

/-! ### The Čech complexes agree -/

/-- **The Čech complex of [Stacks, Tag 02FU] at a scheme**, for a family of open sets. -/
noncomputable def coveringComplexOpens (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens) :
    X.Modules ⥤ CochainComplex X.Modules ℕ :=
  cechDiagramOpens X ⋙ CategoryTheory.cechComplexFunctor U

/-- **The absolute Čech complex of [Stacks, Tag 01XL] is the Čech complex of
[Stacks, Tag 02FU]** for the family of open ranges of the affine open cover, naturally in the
quasi-coherent module. -/
noncomputable def absoluteCechComplexCoveringIso (X : Scheme.{u})
    (T : X.AffineOpenCover.{u, u}) :
    Stacks.AlgebraicGeometry.CechPushforwardComplex.absoluteCechPresheaf X ⋙
        CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i)) ≅
      ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        coveringComplexOpens X (fun i ↦ (T.f i).opensRange) :=
  absoluteCechComplexOpensIso X T ≪≫
    Functor.isoWhiskerRight (absoluteCechOpensPresheafIso X)
      (CategoryTheory.cechComplexFunctor (fun i ↦ (T.f i).opensRange))

/-! ### The augmentation, with the universe enlargement removed -/

/-- The universe enlargement of [Stacks, Tag 02FU] at a scheme. -/
noncomputable def moduleUniverseLiftOpens (X : Scheme.{u}) : X.Modules ⥤ X.Modules :=
  Stacks.CechTotalComplex.CoveringResolution.moduleUniverseLift.{u, u, u, u} X.carrier
    X.ringCatSheaf

/-- At the equal universes of a scheme the universe enlargement is the identity functor. -/
noncomputable def moduleUniverseLiftOpensIso (X : Scheme.{u}) :
    moduleUniverseLiftOpens X ≅ 𝟭 X.Modules :=
  Stacks.Tag01XLCoefficientIso.moduleUniverseLiftIso.{u, u, u, u} X.carrier X.ringCatSheaf

/-- The augmentation of [Stacks, Tag 02FU] at a scheme. -/
noncomputable def augmentationNatTransOpens (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens) :
    moduleUniverseLiftOpens X ⋙ HomologicalComplex.single X.Modules (ComplexShape.up ℕ) 0 ⟶
      coveringComplexOpens X U :=
  Stacks.AlgebraicGeometry.CoveringResolution.augmentationNatTrans.{u, u, u, u} X.carrier
    X.ringCatSheaf U

/-- **[Stacks, Tag 02FU] at a scheme**: the augmentation of the Čech complex of an open covering
is a quasi-isomorphism. -/
theorem quasiIso_augmentationNatTransOpens (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) (M : X.Modules) :
    QuasiIso ((augmentationNatTransOpens X U).app M) :=
  Stacks.AlgebraicGeometry.CoveringResolutionQuasiIso.quasiIso_augmentationNatTrans.{u, u, u, u}
    X.carrier X.ringCatSheaf U M hU

/-- **The augmentation of [Stacks, Tag 02FU] with the universe enlargement removed**: a natural
transformation from a module sheaf placed in degree zero to the Čech complex of the covering. -/
noncomputable def augOpens (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens) :
    HomologicalComplex.single X.Modules (ComplexShape.up ℕ) 0 ⟶ coveringComplexOpens X U :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (moduleUniverseLiftOpensIso X).inv
      (HomologicalComplex.single X.Modules (ComplexShape.up ℕ) 0) ≫
    augmentationNatTransOpens X U

/-- The components of `augOpens`. -/
theorem augOpens_app (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens) (M : X.Modules) :
    (augOpens X U).app M =
      (HomologicalComplex.single X.Modules (ComplexShape.up ℕ) 0).map
          ((moduleUniverseLiftOpensIso X).inv.app M) ≫
        (augmentationNatTransOpens X U).app M :=
  Category.id_comp _

/-- **The augmentation with the universe enlargement removed is a quasi-isomorphism.** -/
theorem quasiIso_augOpens_app (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (hU : ⨆ i, U i = ⊤) (M : X.Modules) :
    QuasiIso ((augOpens X U).app M) := by
  have hq := quasiIso_augmentationNatTransOpens X U hU M
  rw [augOpens_app X U M]
  infer_instance

/-! ### The augmentation of the absolute Čech resolution of [Stacks, Tag 01XL] -/

/-- **The augmentation `ℱ ⟶ 𝔠 ⁼(𝒰, ℱ)` of the absolute Čech resolution of
[Stacks, Tag 01XL]**, as an `ℕ`-indexed natural transformation. -/
noncomputable def absoluteCechAug (X : Scheme.{u}) (T : X.AffineOpenCover.{u, u}) :
    ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        HomologicalComplex.single X.Modules (ComplexShape.up ℕ) 0 ⟶
      Stacks.AlgebraicGeometry.CechPushforwardComplex.absoluteCechPresheaf X ⋙
        CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i)) :=
  Functor.whiskerLeft (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))
      (augOpens X (fun i ↦ (T.f i).opensRange)) ≫
    (absoluteCechComplexCoveringIso X T).inv

/-- The components of `absoluteCechAug`. -/
theorem absoluteCechAug_app (X : Scheme.{u}) (T : X.AffineOpenCover.{u, u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (absoluteCechAug X T).app F =
      (augOpens X (fun i ↦ (T.f i).opensRange)).app F.obj ≫
        (absoluteCechComplexCoveringIso X T).inv.app F :=
  rfl

/-- **[Stacks, Tag 02FU] in the site of [Stacks, Tag 01XL]**: the augmentation of the absolute
Čech resolution is a quasi-isomorphism. -/
theorem quasiIso_absoluteCechAug_app (X : Scheme.{u}) (T : X.AffineOpenCover.{u, u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    QuasiIso ((absoluteCechAug X T).app F) := by
  have hq := quasiIso_augOpens_app X (fun i ↦ (T.f i).opensRange)
    (iSup_affineOpenCover_opensRange X T) F.obj
  rw [absoluteCechAug_app X T F]
  infer_instance

/-! ### Passing to `ℤ`-indexed complexes -/

/-- The extension functor acts on morphisms by `HomologicalComplex.extendMap`. -/
theorem extendFunctor_map (X : Scheme.{u}) {K L : CochainComplex X.Modules ℕ} (φ : K ⟶ L) :
    (ComplexShape.embeddingUpNat.extendFunctor X.Modules).map φ =
      HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat :=
  rfl

/-- The augmentation extended along `ComplexShape.embeddingUpNat`. -/
noncomputable def absoluteCechAugExtend (X : Scheme.{u}) (T : X.AffineOpenCover.{u, u}) :
    (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        HomologicalComplex.single X.Modules (ComplexShape.up ℕ) 0) ⋙
        ComplexShape.embeddingUpNat.extendFunctor X.Modules ⟶
      (Stacks.AlgebraicGeometry.CechPushforwardComplex.absoluteCechPresheaf X ⋙
          CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))) ⋙
        ComplexShape.embeddingUpNat.extendFunctor X.Modules :=
  Functor.whiskerRight (absoluteCechAug X T) (ComplexShape.embeddingUpNat.extendFunctor X.Modules)

/-- Extending a quasi-isomorphism along an embedding of complex shapes gives a
quasi-isomorphism. -/
theorem quasiIso_absoluteCechAugExtend_app (X : Scheme.{u}) (T : X.AffineOpenCover.{u, u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    QuasiIso ((absoluteCechAugExtend X T).app F) := by
  have hq := quasiIso_absoluteCechAug_app X T F
  exact inferInstanceAs (QuasiIso (HomologicalComplex.extendMap ((absoluteCechAug X T).app F)
    ComplexShape.embeddingUpNat))

/-- A composite of four morphisms conjugated by isomorphisms, stated where no scheme data
occurs so that the rearrangement is checked on variables. -/
theorem comp_iso_conj {C : Type*} [Category* C] {W A M N NS NE MZ NZ : C}
    (a : W ⟶ A) (p : A ⟶ M) (f : M ⟶ N) (Q : NS ≅ N) (B : NE ≅ NS) (R : MZ ≅ M) (S : NZ ≅ N) :
    (a ≫ p ≫ (f ≫ Q.inv) ≫ B.inv) ≫ (B.hom ≫ Q.hom ≫ S.inv) =
      (a ≫ p ≫ R.inv) ≫ (R.hom ≫ f ≫ S.inv) := by
  simp

/-- **The extension of a complex concentrated in degree zero is the `ℤ`-indexed complex
concentrated in degree zero**, naturally in the object. -/
noncomputable def singleExtendIso (X : Scheme.{u}) :
    HomologicalComplex.single X.Modules (ComplexShape.up ℕ) 0 ⋙
        ComplexShape.embeddingUpNat.extendFunctor X.Modules ≅
      HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0 :=
  NatIso.ofComponents
    (fun M => HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0
      ComplexShape.embeddingUpNat_f_zero)
    (fun {M N} f => by
      refine HomologicalComplex.to_single_hom_ext (j := 0) ?_
      rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Functor.comp_map,
        extendFunctor_map, HomologicalComplex.extendMap_f _ ComplexShape.embeddingUpNat
          ComplexShape.embeddingUpNat_f_zero,
        HomologicalComplex.extendSingleIso_hom_f, HomologicalComplex.extendSingleIso_hom_f,
        HomologicalComplex.single_map_f_self, HomologicalComplex.single_map_f_self]
      exact comp_iso_conj
        (((HomologicalComplex.single X.Modules (ComplexShape.up ℕ) 0).obj M).extendXIso
          ComplexShape.embeddingUpNat ComplexShape.embeddingUpNat_f_zero).hom
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 M).hom f
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 N)
        (((HomologicalComplex.single X.Modules (ComplexShape.up ℕ) 0).obj N).extendXIso
          ComplexShape.embeddingUpNat ComplexShape.embeddingUpNat_f_zero)
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M)
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N))

/-- **The augmentation `ℱ[0] ⟶ 𝔠 ⁼(𝒰, ℱ)` of [Stacks, Tag 01XL], as a natural transformation of
`ℤ`-indexed complexes of `𝒪_X`-modules.** -/
noncomputable def absoluteCechAugZ (X : Scheme.{u}) (T : X.AffineOpenCover.{u, u}) :
    ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf) ⋙
        HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0 ⟶
      (Stacks.AlgebraicGeometry.CechPushforwardComplex.absoluteCechPresheaf X ⋙
          CategoryTheory.cechComplexFunctor (fun i ↦ Over.mk (T.f i))) ⋙
        ComplexShape.embeddingUpNat.extendFunctor X.Modules :=
  (Functor.isoWhiskerLeft (ObjectProperty.ι (SheafOfModules.isQuasicoherent X.ringCatSheaf))
      (singleExtendIso X)).inv ≫ absoluteCechAugExtend X T

/-- The components of `absoluteCechAugZ`. -/
theorem absoluteCechAugZ_app (X : Scheme.{u}) (T : X.AffineOpenCover.{u, u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    (absoluteCechAugZ X T).app F =
      ((singleExtendIso X).app F.obj).inv ≫ (absoluteCechAugExtend X T).app F :=
  rfl

/-- **[Stacks, Tag 02FU] for the absolute Čech resolution of [Stacks, Tag 01XL]**: the
augmentation `ℱ[0] ⟶ 𝔠 ⁼(𝒰, ℱ)` of `ℤ`-indexed complexes is a quasi-isomorphism. -/
theorem quasiIso_absoluteCechAugZ_app (X : Scheme.{u}) (T : X.AffineOpenCover.{u, u})
    (F : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    QuasiIso ((absoluteCechAugZ X T).app F) := by
  have hq := quasiIso_absoluteCechAugExtend_app X T F
  rw [absoluteCechAugZ_app X T F]
  infer_instance

end Stacks.CechSiteChange

end
