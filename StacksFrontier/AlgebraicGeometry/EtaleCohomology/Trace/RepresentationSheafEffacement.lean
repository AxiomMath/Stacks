module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleCohomologyForget
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleExtForgetPullback
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FirstCohomologyKilling.FiniteEtaleCover
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.DerivedGlobalSectionsCohomology

/-!
# Killing étale cohomology classes of sheaves of modules by finite covers

The étale cohomology of a sheaf `G` of `Λ`-modules, the right derived functors of global
sections, is the sheaf cohomology `Sheaf.H` of its underlying abelian sheaf, as an isomorphism of
functors (`Stacks.EtaleCohomology.etaleModuleCohomologyIsoFunctorH`). Through it the statement
`ext_comp_mk₀_map_unit_eq_zero_of_restriction` for abelian sheaves — a class on `P` whose
restriction to `Y ×_X P` vanishes dies under the inverse image of the unit `A ⟶ π_* π⁻¹ A` of a
finite `π : Y ⟶ X` — passes to sheaves of modules over an arbitrary ring `Λ`.

## Main results

* `Stacks.EtaleCohomology.etaleModuleCohomologyIsoFunctorH` — `H^q_Λ(Z, G) ≅ Sheaf.H(Z, U G, q)`.
* `Stacks.EtaleCohomology.rightDerived_map_apply_eq_zero_iff` — a morphism kills a class iff the
  underlying abelian morphism kills the abelian class.
* `Stacks.EtaleCohomology.etaleModuleUnderlyingAbelianInverseImageIsoOfRing` and its unit
  compatibility — inverse image commutes with forgetting the module structure, over any ring.
* `Stacks.EtaleCohomology.rightDerived_map_inverseImage_unit_eq_zero` — the killing statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-- `Ext` of abelian sheaves on the small étale site at its object universe, pinned: the general
instance is indexed by `max (u + 1) v`, and instance search cannot solve
`max (u + 1) ?v = u + 1`. -/
local instance (priority := 3000) hasExt_smallEtale_objectUniverse'
    (Y : Scheme.{u}) : HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  haveI : IsGrothendieckAbelian.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse Y
  CategoryTheory.IsGrothendieckAbelian.hasExt _

section Forget

variable {Z : Scheme.{u}} (Λ : Type) [Ring Λ]

/-- **Étale cohomology of a sheaf of `Λ`-modules is the sheaf cohomology of its underlying
abelian sheaf**, as an isomorphism of functors: the right derived functors of `Γ` commute with
forgetting the `Λ`-module structure (`etaleModuleCohomologyForgetIso`), and on abelian sheaves
they are `Ext` out of the constant sheaf `ℤ`
(`Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH`). -/
def etaleModuleCohomologyIsoFunctorH (q : ℕ) :
    (etaleModuleGlobalSections.{u, 0} Λ Z).rightDerived q ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ≅
      etaleModuleUnderlyingAbelian Z Λ ⋙
        Sheaf.functorH.{u + 1, u + 1, u, u + 1} Z.smallEtaleTopology q :=
  etaleModuleCohomologyForgetIso.{u, 0} Λ Z q ≪≫
    Functor.isoWhiskerLeft _
      (Stacks.Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u + 1, u, u + 1}
        Z.smallEtaleTopology q)

/-- A morphism of sheaves of `Λ`-modules kills a cohomology class exactly when the morphism of
underlying abelian sheaves kills the corresponding class of `Sheaf.H`. -/
theorem rightDerived_map_apply_eq_zero_iff {G G' : EtaleModules.{u, 0} Λ Z} (φ : G ⟶ G')
    (q : ℕ) (x : ((etaleModuleGlobalSections.{u, 0} Λ Z).rightDerived q).obj G) :
    ((etaleModuleGlobalSections.{u, 0} Λ Z).rightDerived q).map φ x = 0 ↔
      ((etaleModuleCohomologyIsoFunctorH Λ q).hom.app G x).comp
        (Ext.mk₀ ((etaleModuleUnderlyingAbelian Z Λ).map φ)) (add_zero q) = 0 := by
  have h := ConcreteCategory.congr_hom ((etaleModuleCohomologyIsoFunctorH Λ q).hom.naturality φ) x
  have hinj := (ConcreteCategory.bijective_of_isIso
    ((etaleModuleCohomologyIsoFunctorH Λ q).hom.app G')).1
  change (etaleModuleCohomologyIsoFunctorH Λ q).hom.app G'
    (((etaleModuleGlobalSections.{u, 0} Λ Z).rightDerived q).map φ x) = _ at h
  refine ⟨fun hx => ?_, fun hx => hinj ?_⟩
  · rw [hx, map_zero] at h
    exact h.symm
  · rw [h, map_zero]
    exact hx

end Forget

section Pullback

/-- Postcomposition with the forgetful functor carries sheaves of modules over a ring to abelian
sheaves. -/
local instance hasSheafCompose_forget₂_ofRing (Λ : Type) [Ring Λ] (Z : Scheme.{u}) :
    Z.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  ModuleSheaf.hasSheafCompose_forget₂.{u + 1} Λ Z.smallEtaleTopology

/-- Sheafification commutes with forgetting the module structure over a ring. -/
local instance preservesSheafification_forget₂_ofRing (Λ : Type) [Ring Λ] (Z : Scheme.{u}) :
    Z.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
  ModuleSheaf.preservesSheafification_forget₂.{u + 1} Λ Z.smallEtaleTopology

/-- Forgetting the module structure over a ring preserves the left Kan extensions defining
inverse image: the comma categories are filtered, and the forgetful functor preserves filtered
colimits. -/
local instance preservesLeftKanExtensions_forget₂_ofRing (Λ : Type) [Ring Λ] {X Y : Scheme.{u}}
    (g : Y ⟶ X) : (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).PreservesLeftKanExtensions
      (smallEtaleBaseChange g).op := by
  intro P
  have hfil : ∀ V : Y.Etaleᵒᵖ,
      IsFiltered (CostructuredArrow (smallEtaleBaseChange g).op V) := fun V =>
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (smallEtaleBaseChange g) V.unop)
  have : PreservesFilteredColimitsOfSize.{u, u + 1}
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} _
  infer_instance

/-- **Inverse image commutes with forgetting the module structure**, over any ring `Λ`:
`g^{-1}(U M) ≅ U(g^{-1} M)`. This is `etaleModuleUnderlyingAbelianInverseImageIso` without the
commutativity of `Λ`, which its argument does not use. -/
def etaleModuleUnderlyingAbelianInverseImageIsoOfRing (Λ : Type) [Ring Λ] {X Y : Scheme.{u}}
    (g : Y ⟶ X) :
    etaleModuleUnderlyingAbelian X Λ ⋙ etaleAbelianInverseImage.{u, 0} g ≅
      etaleModuleInverseImage.{u, 0} Λ g ⋙ etaleModuleUnderlyingAbelian Y Λ :=
  Functor.isoWhiskerLeft _ (Functor.sheafPullbackConstruction.sheafPullbackIso
      (smallEtaleBaseChange g) AddCommGrpCat.{u + 1} X.smallEtaleTopology
      Y.smallEtaleTopology).symm ≪≫
    asIso (coefficientSheafPullbackTwoSquare (smallEtaleBaseChange g) X.smallEtaleTopology
      Y.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).natTrans

/-- **The comparison matches the units**, over any ring `Λ`: the underlying abelian map of the
unit of `g^{-1} ⊣ g_*` on modules is the unit on abelian sheaves followed by `g_*` of the
comparison `etaleModuleUnderlyingAbelianInverseImageIsoOfRing`. -/
theorem etaleModuleUnderlyingAbelianInverseImageIsoOfRing_unit (Λ : Type) [Ring Λ]
    {X Y : Scheme.{u}} (g : Y ⟶ X) (M : EtaleModules.{u, 0} Λ X) :
    (etaleModuleUnderlyingAbelian X Λ).map ((etaleModuleInverseImageAdj.{u, 0} Λ g).unit.app M) =
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} g).unit.app
          ((etaleModuleUnderlyingAbelian X Λ).obj M) ≫
        ((smallEtaleBaseChange g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          X.smallEtaleTopology Y.smallEtaleTopology).map
          ((etaleModuleUnderlyingAbelianInverseImageIsoOfRing Λ g).hom.app M) := by
  suffices key : (etaleModuleUnderlyingAbelian X Λ).map
      ((etaleModuleInverseImageAdj.{u, 0} Λ g).unit.app M) =
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange g)
          AddCommGrpCat.{u + 1} X.smallEtaleTopology Y.smallEtaleTopology).unit.app
          ((etaleModuleUnderlyingAbelian X Λ).obj M) ≫
        ((smallEtaleBaseChange g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          X.smallEtaleTopology Y.smallEtaleTopology).map
          ((etaleModuleUnderlyingAbelianInverseImageIsoOfRing Λ g).hom.app M) from key
  have h1 := coefficientSheafPullbackTwoSquare_unit (smallEtaleBaseChange g) X.smallEtaleTopology
    Y.smallEtaleTopology (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) M
  have h2 := Adjunction.unit_leftAdjointUniq_hom_app
    ((smallEtaleBaseChange g).sheafAdjunctionContinuous AddCommGrpCat.{u + 1}
      X.smallEtaleTopology Y.smallEtaleTopology)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange g)
      AddCommGrpCat.{u + 1} X.smallEtaleTopology Y.smallEtaleTopology)
    ((etaleModuleUnderlyingAbelian X Λ).obj M)
  refine h1.trans ?_
  simp only [etaleModuleUnderlyingAbelianInverseImageIsoOfRing, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom, asIso_hom,
    Functor.map_comp, ← h2, Category.assoc]
  simp only [Functor.sheafPullbackConstruction.sheafPullbackIso, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end Pullback

section Killing

variable (Λ : Type) [Ring Λ] {P X Y : Scheme.{u}} (i' : P ⟶ X)

/-- The class of `Sheaf.H(P, i'⁻¹ U G)` attached to a class of `H^q_Λ(P, i'^* G)`: read the
class on the underlying abelian sheaf (`etaleModuleCohomologyIsoFunctorH`) and move it along the
comparison `i'⁻¹ U G ≅ U i'^* G`. -/
def inverseImageSheafHClass (G : EtaleModules.{u, 0} Λ X) (q : ℕ)
    (x : ((etaleModuleGlobalSections.{u, 0} Λ P).rightDerived q).obj
      ((etaleModuleInverseImage.{u, 0} Λ i').obj G)) :
    Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} i').obj
      ((etaleModuleUnderlyingAbelian X Λ).obj G)) q :=
  ((etaleModuleCohomologyIsoFunctorH Λ q).hom.app _ x).comp
    (Ext.mk₀ ((etaleModuleUnderlyingAbelianInverseImageIsoOfRing Λ i').inv.app G)) (add_zero q)

/-- Postcomposing an `Ext` class with a threefold composite of morphisms, one at a time. -/
private lemma ext_comp_mk₀_comp_comp {𝒞 : Type*} [Category* 𝒞] [Abelian 𝒞] {_ : HasExt.{u + 1} 𝒞}
    {A B C D E : 𝒞} {q : ℕ} (x : Ext.{u + 1} A B q) (a : B ⟶ C) (b : C ⟶ D) (r : D ⟶ E) :
    x.comp (Ext.mk₀ (a ≫ b ≫ r)) (add_zero q) =
      ((x.comp (Ext.mk₀ a) (add_zero q)).comp (Ext.mk₀ b) (add_zero q)).comp (Ext.mk₀ r)
        (add_zero q) := by
  simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Category.assoc]

/-- The underlying abelian map of `i'^*` of the unit `G ⟶ π_* π^* G` is the inverse image of the
abelian unit, up to the comparisons `etaleModuleUnderlyingAbelianInverseImageIsoOfRing`. -/
theorem underlyingAbelian_map_inverseImage_unit (π : Y ⟶ X) (G : EtaleModules.{u, 0} Λ X) :
    (etaleModuleUnderlyingAbelian P Λ).map ((etaleModuleInverseImage.{u, 0} Λ i').map
        ((etaleModuleInverseImageAdj.{u, 0} Λ π).unit.app G)) =
      (etaleModuleUnderlyingAbelianInverseImageIsoOfRing Λ i').inv.app G ≫
        (etaleAbelianInverseImage.{u, 0} i').map
          ((etaleAbelianInverseImageDirectImageAdj.{u, 0} π).unit.app
            ((etaleModuleUnderlyingAbelian X Λ).obj G)) ≫
        (etaleAbelianInverseImage.{u, 0} i').map
          (((smallEtaleBaseChange π).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            X.smallEtaleTopology Y.smallEtaleTopology).map
            ((etaleModuleUnderlyingAbelianInverseImageIsoOfRing Λ π).hom.app G)) ≫
        (etaleModuleUnderlyingAbelianInverseImageIsoOfRing Λ i').hom.app
          ((etaleModuleDirectImage.{u, 0} Λ π).obj
            ((etaleModuleInverseImage.{u, 0} Λ π).obj G)) := by
  let c := etaleModuleUnderlyingAbelianInverseImageIsoOfRing Λ i'
  let η :
      G ⟶ (etaleModuleDirectImage.{u, 0} Λ π).obj ((etaleModuleInverseImage.{u, 0} Λ π).obj G) :=
    (etaleModuleInverseImageAdj.{u, 0} Λ π).unit.app G
  have h₁ : (etaleAbelianInverseImage.{u, 0} i').map ((etaleModuleUnderlyingAbelian X Λ).map η) ≫
      c.hom.app
        ((etaleModuleDirectImage.{u, 0} Λ π).obj ((etaleModuleInverseImage.{u, 0} Λ π).obj G)) =
        c.hom.app G ≫
        (etaleModuleUnderlyingAbelian P Λ).map ((etaleModuleInverseImage.{u, 0} Λ i').map η) :=
    c.hom.naturality η
  have h₂ : (etaleModuleUnderlyingAbelian X Λ).map η =
      (etaleAbelianInverseImageDirectImageAdj.{u, 0} π).unit.app
          ((etaleModuleUnderlyingAbelian X Λ).obj G) ≫
        ((smallEtaleBaseChange π).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
          X.smallEtaleTopology Y.smallEtaleTopology).map
          ((etaleModuleUnderlyingAbelianInverseImageIsoOfRing Λ π).hom.app G) :=
    etaleModuleUnderlyingAbelianInverseImageIsoOfRing_unit Λ π G
  show (etaleModuleUnderlyingAbelian P Λ).map ((etaleModuleInverseImage.{u, 0} Λ i').map η) = _
  have h₃ : (etaleAbelianInverseImage.{u, 0} i').map ((etaleModuleUnderlyingAbelian X Λ).map η) =
      (etaleAbelianInverseImage.{u, 0} i').map
          ((etaleAbelianInverseImageDirectImageAdj.{u, 0} π).unit.app
            ((etaleModuleUnderlyingAbelian X Λ).obj G)) ≫
        (etaleAbelianInverseImage.{u, 0} i').map
          (((smallEtaleBaseChange π).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
            X.smallEtaleTopology Y.smallEtaleTopology).map
            ((etaleModuleUnderlyingAbelianInverseImageIsoOfRing Λ π).hom.app G)) := by
    rw [h₂]
    exact (etaleAbelianInverseImage.{u, 0} i').map_comp _ _
  rw [← cancel_epi (c.hom.app G), ← h₁, h₃, Iso.hom_inv_id_app_assoc]
  exact Category.assoc _ _ _

/-- **A class whose restriction to a finite cover vanishes dies under the inverse image of the
unit of the cover**, for sheaves of `Λ`-modules over any ring `Λ`. Let `i' : P ⟶ X` be a morphism
of schemes, `π : Y ⟶ X` a finite morphism and `G` a sheaf of `Λ`-modules on `X`. If the abelian
class of `x ∈ H^q(P, i'^* G)` restricts to zero on `Y ×_X P`, then `x` dies under `i'^*` of the
unit `G ⟶ π_* π^* G`.

This is `ext_comp_mk₀_map_unit_eq_zero_of_restriction` (abelian sheaves), read through the
forgetful functor: the underlying abelian map of the unit of modules is the abelian unit followed
by an isomorphism (`etaleModuleUnderlyingAbelianInverseImageIsoOfRing_unit`). -/
theorem rightDerived_map_inverseImage_unit_eq_zero (π : Y ⟶ X) [IsFinite π]
    (G : EtaleModules.{u, 0} Λ X) {q : ℕ}
    (x : ((etaleModuleGlobalSections.{u, 0} Λ P).rightDerived q).obj
      ((etaleModuleInverseImage.{u, 0} Λ i').obj G))
    (hx : etaleCohomologyRestrictionMap.{u, 0, u + 1} (pullback.snd π i') _ q
      (inverseImageSheafHClass Λ i' G q x) = 0) :
    ((etaleModuleGlobalSections.{u, 0} Λ P).rightDerived q).map
      ((etaleModuleInverseImage.{u, 0} Λ i').map
        ((etaleModuleInverseImageAdj.{u, 0} Λ π).unit.app G)) x = 0 := by
  rw [rightDerived_map_apply_eq_zero_iff]
  have hkill := ext_comp_mk₀_map_unit_eq_zero_of_restriction i' π
    ((etaleModuleUnderlyingAbelian X Λ).obj G) (inverseImageSheafHClass Λ i' G q x) hx
  rw [underlyingAbelian_map_inverseImage_unit]
  refine (ext_comp_mk₀_comp_comp _ _ _ _).trans ?_
  exact (congrArg (fun z => Ext.comp z _ (add_zero q)) hkill).trans (Ext.zero_comp _ _ _ _ _)

end Killing

end Stacks.EtaleCohomology

end
