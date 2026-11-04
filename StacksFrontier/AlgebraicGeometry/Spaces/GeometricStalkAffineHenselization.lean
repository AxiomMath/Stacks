module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedSectionsHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkCohomologyMapAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineAssociatedModuleStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UnitEndomorphismStalk

/-!
# The geometric stalk ring of an affine representable space

Let `U` be an object of the big fppf site over `S` with affine underlying scheme and ring of
global functions `A`, and let `x̄` be a geometric point of `yoneda.obj U`. The ring map
`A ⟶ 𝒪_{x̄}` through which `A` acts on the geometric stalk of `A^~` is the germ map: an element
`a ∈ A` acts on `A^~ ≅ 𝒪` as multiplication by the global function `a`, and an endomorphism of
`𝒪` acts on its stalk by the germ of its value at `1`.

## Main results

* `AlgebraicGeometry.Space.representedAffineStalkRingHom_eq_germ`: the structure map
  `AlgebraicGeometry.Space.representedAffineGlobalStalkRingHom` is the germ map
  `AlgebraicGeometry.Space.representedStalkGerm`.
* `AlgebraicGeometry.Space.pointStalkRingEquiv_representedAffineGlobalStalkRingHom`: read in the
  étale local ring, it is the germ at the identity neighbourhood.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)

/-- The chart of the small étale site of `yoneda.obj U` over which the sections functor of an
affine `U` is evaluated: the whole of the scheme underlying `U`, as an open subscheme. -/
noncomputable abbrev representedAffineTopChart : SmallEtale B S hS (yoneda.obj U) :=
  (representedSmallEtaleEquivalence B S hS U).inverse.obj
    (_root_.AlgebraicGeometry.SmallEtale.opensObj (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property ⊤)

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]

/-- Multiplication by `a` on `N`, after the associated module and the sections functor, is
multiplication by `a`. -/
theorem representedAffineSections_map_associated_smul
    (N : ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (representedAffineSections B S hS U).map
        ((representedAffineAssociated B S hS U).map (a • 𝟙 N)) =
      a • 𝟙 ((representedAffineSections B S hS U).obj
        ((representedAffineAssociated B S hS U).obj N)) := by
  have h := (representedAffineAssociatedAdjunction B S hS U).unit.naturality (a • 𝟙 N)
  rw [← Iso.cancel_iso_hom_left
      (asIso ((representedAffineAssociatedAdjunction B S hS U).unit.app N)),
    asIso_hom]
  refine (h.symm.trans ?_)
  rw [Functor.id_map]
  ext y
  simp

/-- The image of a global function on `U` in the structure sheaf over the top chart. -/
noncomputable def representedAffineTopChartSection (a : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (smallEtaleRingSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).val.obj
      (op (representedAffineTopChart B S hS U)) :=
  ((structurePresheaf B S hS (yoneda.obj U)).map
    (toSelfChart B S hS U (representedAffineTopChart B S hS U)).op).hom a

/-- The action of a section of the ring sheaf on a section of a sheaf of modules. -/
def sheafSectionSmul {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} (F : SheafOfModules.{u} R) (V : C) (r : R.val.obj (op V))
    (t : F.val.obj (op V)) : F.val.obj (op V) := r • t

/-- `Γ(U) ⟶ Γ(Spec Γ(U)) ⟶ Γ(U)` is the identity. -/
theorem toSpecΓ_app_top_ΓSpecIso_inv (a : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    (((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom.app ⊤).hom
      ((Scheme.ΓSpecIso Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).inv.hom a) = a := by
  rw [Scheme.isoSpec_hom]
  show ((Scheme.ΓSpecIso _).inv ≫ Scheme.Hom.appTop _).hom a = a
  rw [Scheme.toSpecΓ_appTop, Iso.inv_hom_id]
  rfl

/-- The image of a global function in the étale structure sheaf over the top chart, through the
action of `Γ(U)` on the sections functor, is its restriction along the morphism to the self
chart. -/
theorem structureMap_app_top_eq (a : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    ((_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).hom.app (op ⊤)).hom
    ((((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom.app ⊤).hom
      ((Scheme.ΓSpecIso Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)).inv.hom a)) =
      representedAffineTopChartSection B S hS U a := by
  rw [toSpecΓ_app_top_ΓSpecIso_inv, SmallEtale.structureMap_hom_app]
  show _ = ((⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens).ι.appTop).hom a
  simp only [Scheme.Opens.topIso_inv, Scheme.Opens.ι_appTop]
  rfl

/-- An endomorphism of an `𝒪`-module acting on the sections functor as multiplication by `a`
acts on sections over the top chart as multiplication by the image of `a`. -/
private theorem app_topChart_of_sections_map_eq_smul
    {F : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)} (φ : F ⟶ F)
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    (hφ : (representedAffineSections B S hS U).map φ = a • 𝟙 _)
    (t : F.val.obj (op (representedAffineTopChart B S hS U))) :
    (φ.val.app (op (representedAffineTopChart B S hS U))).hom t =
      sheafSectionSmul
        (R := smallEtaleRingSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
        F (representedAffineTopChart B S hS U) (representedAffineTopChartSection B S hS U a) t := by
  have h := ConcreteCategory.congr_hom hφ (show (representedAffineSections B S hS U).obj F from t)
  refine h.trans ?_
  rw [← structureMap_app_top_eq]
  rfl

/-- The image of a global function over the top chart is its restriction to the open subscheme
`⊤`. -/
theorem representedAffineTopChartSection_eq (a : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    representedAffineTopChartSection B S hS U a =
      (Scheme.Opens.topIso (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens)).inv.hom a := by
  rw [← structureMap_app_top_eq, toSpecΓ_app_top_ΓSpecIso_inv, SmallEtale.structureMap_hom_app]
  rfl

/-- Restriction of global functions to the top chart is injective. -/
theorem representedAffineTopChartSection_injective :
    Function.Injective (representedAffineTopChartSection B S hS U) := by
  intro a b h
  rw [representedAffineTopChartSection_eq, representedAffineTopChartSection_eq] at h
  have h1 : ∀ c, (Scheme.Opens.topIso (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens)).hom.hom
      ((Scheme.Opens.topIso (⊤ : ((BigFppfOver.toScheme B S hS).obj U).Opens)).inv.hom c) = c :=
    fun c => by rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  rw [← h1 a, ← h1 b, h]

/-- An endomorphism `φ` of an `𝒪`-module isomorphic to `𝒪`, acting on sections as multiplication
by `a`, transported to `𝒪`, has value `a` at `1` over the self chart. -/
theorem conj_app_selfChart_one_of_sections_map_eq_smul
    {F : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)}
    (e : F ≅ structureModule ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) (φ : F ⟶ F)
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
    (hφ : (representedAffineSections B S hS U).map φ = a • 𝟙 _) :
    ((e.inv ≫ φ ≫ e.hom).val.app (op (selfChart B S hS U))).hom
      (1 : (smallEtaleRingSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).val.obj
        (op (selfChart B S hS U))) = a := by
  have hV : ((e.inv ≫ φ ≫ e.hom).val.app (op (representedAffineTopChart B S hS U))).hom
      (1 : (smallEtaleRingSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).val.obj
        (op (representedAffineTopChart B S hS U))) =
      representedAffineTopChartSection B S hS U a := by
    have key : ∀ y : F.val.obj (op (representedAffineTopChart B S hS U)),
        (e.hom.val.app (op (representedAffineTopChart B S hS U))).hom
          ((φ.val.app (op (representedAffineTopChart B S hS U))).hom y) =
        sheafSectionSmul
          (R := smallEtaleRingSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U))
          (structureModule ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
          (representedAffineTopChart B S hS U) (representedAffineTopChartSection B S hS U a)
          ((e.hom.val.app (op (representedAffineTopChart B S hS U))).hom y) := fun y => by
      rw [app_topChart_of_sections_map_eq_smul B S hS U φ a hφ]
      exact (e.hom.val.app (op (representedAffineTopChart B S hS U))).hom.map_smul _ _
    have hinv : ∀ y : (structureModule ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).val.obj
        (op (representedAffineTopChart B S hS U)),
        (e.hom.val.app (op (representedAffineTopChart B S hS U))).hom
          ((e.inv.val.app (op (representedAffineTopChart B S hS U))).hom y) = y := fun y => by
      have := congrArg (fun f => (f.val.app (op (representedAffineTopChart B S hS U))).hom y)
        e.inv_hom_id
      exact this
    refine (key _).trans ?_
    refine (congrArg (sheafSectionSmul (R := smallEtaleRingSheaf B S hS (yoneda.obj U)
      (isAlgebraicSpace_yoneda B S hS U))
          (structureModule ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
          (representedAffineTopChart B S hS U) (representedAffineTopChartSection B S hS U a))
      (hinv _)).trans ?_
    exact mul_one (representedAffineTopChartSection B S hS U a)
  have hnat := PresheafOfModules.naturality_apply (e.inv ≫ φ ≫ e.hom).val
    (toSelfChart B S hS U (representedAffineTopChart B S hS U)).op
    (1 : (smallEtaleRingSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).val.obj
      (op (selfChart B S hS U)))
  apply representedAffineTopChartSection_injective B S hS U
  refine Eq.trans ?_ hV
  refine hnat.symm.trans (congrArg ((e.inv ≫ φ ≫ e.hom).val.app
    (op (representedAffineTopChart B S hS U))).hom ?_)
  exact map_one
    ((smallEtaleRingSheaf B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)).val.map
      (toSelfChart B S hS U (representedAffineTopChart B S hS U)).op).hom

/-- Conjugating a scalar endomorphism by a retraction. -/
private theorem comp_smul_id_comp {R : Type u} [CommRing R] {X Y : ModuleCat.{u} R}
    (f : X ⟶ Y) (g : Y ⟶ X) (c : R) (h : f ≫ g = 𝟙 X) : f ≫ (c • 𝟙 Y) ≫ g = c • 𝟙 X := by
  rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, h]

/-- **The structure map of the stalk of `A^~` is the germ map.** -/
theorem representedAffineStalkRingHom_eq_germ (x : GeometricPoint B S hS (yoneda.obj U)) :
    representedAffineGlobalStalkRingHom B S hS U x = (representedStalkGerm B S hS U x).hom := by
  ext a
  set e := representedAffineAssociatedObjUnitIso B S hS U
  set φ := (representedAffineAssociated B S hS U).map
    (a • 𝟙 (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)))
  have h1 := conj_app_selfChart_one_of_sections_map_eq_smul B S hS U e φ a
    (representedAffineSections_map_associated_smul B S hS U _ a)
  have hfib := Stacks.sheafModuleFiberOfCommRing_map_unit
    (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
    (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O
    (e.inv ≫ φ ≫ e.hom) (selfChart B S hS U) (selfChartFiberPoint B S hS U x)
  have h1' : ((e.inv ≫ φ ≫ e.hom).val.app (op (selfChart B S hS U))).hom
      (1 : (Stacks.commRingSheafToRingSheaf (smallEtaleRingedTopos B S hS
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O).obj.obj
          (op (selfChart B S hS U))) = a :=
    h1
  replace hfib := hfib.trans (congrArg (fun c => Stacks.ringStalkGerm
    (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
    (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O
    (selfChart B S hS U) (selfChartFiberPoint B S hS U x) c • 𝟙 _) h1')
  have hφ : φ = e.hom ≫ (e.inv ≫ φ ≫ e.hom) ≫ e.inv := by simp
  have hT : (Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O).map φ =
      Stacks.ringStalkGerm
        (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
        (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O
        (selfChart B S hS U) (selfChartFiberPoint B S hS U x) a • 𝟙 _ := by
    set F := Stacks.sheafModuleFiberOfCommRing
      (etaleSitePoint B S hS (yoneda.obj U) x (isAlgebraicSpace_yoneda B S hS U))
      (smallEtaleRingedTopos B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩).O
    refine (congrArg _ hφ).trans ((F.map_comp _ _).trans
      ((congrArg (_ ≫ ·) (F.map_comp _ _)).trans
        ((congrArg (fun t => F.map e.hom ≫ t ≫ F.map e.inv) hfib).trans ?_)))
    exact comp_smul_id_comp _ _ _
      ((F.map_comp _ _).symm.trans ((congrArg F.map e.hom_inv_id).trans (F.map_id _)))
  exact representedAffineStalkScalar_unique B S hS U x
    ((representedAffineStalk_map_smul_id_unit' B S hS U x a).symm.trans hT)

/-- **The structure map of the stalk of `A^~`, in the étale local ring**: the germ of a global
function at the identity neighbourhood of `x̄`. -/
theorem pointStalkRingEquiv_representedAffineGlobalStalkRingHom
    (x : GeometricPoint B S hS (yoneda.obj U))
    (a : Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) :
    pointStalkRingEquiv B S hS ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ x
        (representedAffineGlobalStalkRingHom B S hS U x a) =
      etaleLocalRingGerm B S hS (yoneda.obj U) x (op (selfNeighborhood B S hS U x)) a := by
  rw [representedAffineStalkRingHom_eq_germ]
  exact pointStalkRingEquiv_germ_neighborhood B S hS
    ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ x (selfNeighborhood B S hS U x) a

end AlgebraicGeometry.Space

end
