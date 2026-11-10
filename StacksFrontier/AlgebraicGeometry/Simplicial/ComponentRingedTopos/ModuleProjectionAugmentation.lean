module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleProjection
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleResolutionDerivedTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatSingleTensorNaturality
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianDerivedRealization
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedCompIsoNaturality

/-!
# The adjunct of the projection map of Stacks 0D9E (2) against the augmentation

Let `S` be a simplicial-site situation (Stacks 09WE), `O` a sheaf of commutative rings on its
total site, and `g_n` the inclusion of the degree-`n` component. The augmentation
`ε : g_{n!}O_n ⟶ O` is the counit of `g_{n!} ⊣ g_n^*` at the structure sheaf. The canonical map
`a_K : K_n ⟶ (g_{n!}O_n ⊗^L_O K)_n` of Stacks 0D9E (2) — the adjunct of the projection map —
followed by the restriction of `ε ⊗^L_O K` and the unit constraint `O ⊗^L_O K ≅ K`, is a map
`θ_K : K_n ⟶ K_n`. This file proves that **`θ_K` is an isomorphism**.

On sheaves the composite is `x ↦ ε(η(1)) ⊗ x` read through the comparison of Stacks 03EL, and the
triangle identity `η ≫ g_n^*ε = 𝟙` makes it the inverse left unitor followed by the inverse of
the comparison of Stacks 03EL: an isomorphism. On derived categories the composite is the derived
functor of that sheaf-level isomorphism, read through the compositor of derived functors and
through the identification of `O ⊗^L_O -` with the derived functor of `O ⊗_O -`.

This is the module form of the identification, in the proof of Stacks 0D9S, of the structural
map `X₀ ⟶ K` of the Postnikov system of Stacks 0D9Q with the counit of `Lg_{0!} ⊣ Lg_0^*`: the
structural map is `ε ⊗^L_O K` followed by the unit constraint, and `θ_K` measures how far that is
from the counit.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentModuleLowerShriekUnitAugmentation`: the
  augmentation `g_{n!}O_n ⟶ O`.
* `CategoryTheory.SimplicialSiteSituation.moduleAugmentationDerived`: the map
  `g_{n!}O_n ⊗^L_O K ⟶ K`, the derived tensor product with the augmentation followed by the unit
  constraint.

## Main results

* `CategoryTheory.SimplicialSiteSituation.componentModuleProjectionAdjunct_comp_map_augmentation`:
  the sheaf-level adjunct followed by the augmentation is the inverse left unitor followed by the
  inverse of the comparison of Stacks 03EL.
* `CategoryTheory.SimplicialSiteSituation.isIso_componentModuleProjectionAdjunctDerived_comp_map`:
  **`θ_K` is an isomorphism.**

## References

* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 0D9E](https://stacks.math.columbia.edu/tag/0D9E)
* [Stacks Project, Tag 0D9Q](https://stacks.math.columbia.edu/tag/0D9Q)
* [Stacks Project, Tag 0D9S](https://stacks.math.columbia.edu/tag/0D9S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules.Tensor

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local instance] hasSheafifyTotal
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat hasWeakSheafifyComponent
  wEqualsLocallyBijectiveComponent HasDerivedCategory.standard

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})
  (n : SimplexCategory)

/-- **The augmentation `g_{n!}O_n ⟶ O`**: the counit of `g_{n!} ⊣ g_n^*` at the structure sheaf,
the restriction of the structure sheaf to the component being the structure sheaf of the
component. -/
abbrev componentModuleLowerShriekUnitAugmentation :
    S.componentModuleLowerShriekUnit O n ⟶ SheafOfModules.unit (S.totalRingSheaf O) :=
  (S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).counit.app
    (SheafOfModules.unit (S.totalRingSheaf O))

/-- The unit of `g_{n!} ⊣ g_n^*` at the structure sheaf of the component, followed by the
restriction of the augmentation, is the identity: the triangle identity. -/
theorem unit_comp_map_componentModuleLowerShriekUnitAugmentation :
    (S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).unit.app
        (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)) ≫
      (S.componentModulesRestriction O n).map (S.componentModuleLowerShriekUnitAugmentation O n) =
    𝟙 _ :=
  (S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).right_triangle_components
    (SheafOfModules.unit (S.totalRingSheaf O))

/-- **Naturality of Stacks 03EL at the component inclusion in its first variable alone.** The
companion of `…componentRestrictionTensorIso_inv_naturality_right`. -/
theorem componentRestrictionTensorIso_inv_naturality_left {A B : (S.totalRingedTopos O).Modules}
    (f : A ⟶ B) (M : (S.totalRingedTopos O).Modules) :
    ((sheafTensor (S.componentRingedTopos O n).O).map
          ((S.componentModulesRestriction O n).map f)).app
        ((S.componentModulesRestriction O n).obj M) ≫
      (S.componentRestrictionTensorIso O n).inv.app (B, M) =
    (S.componentRestrictionTensorIso O n).inv.app (A, M) ≫
      (S.componentModulesRestriction O n).map
        (((sheafTensor (S.totalRingedTopos O).O).map f).app M) := by
  have e₁ : (Functor.uncurry.obj (sheafTensor (S.componentRingedTopos O n).O)).map
        (((S.componentModulesRestriction O n).prod
          (S.componentModulesRestriction O n)).map ((f, 𝟙 M) : (A, M) ⟶ (B, M))) =
      ((sheafTensor (S.componentRingedTopos O n).O).map
          ((S.componentModulesRestriction O n).map f)).app
        ((S.componentModulesRestriction O n).obj M) := by
    change _ ≫ ((sheafTensor (S.componentRingedTopos O n).O).obj _).map
        ((S.componentModulesRestriction O n).map (𝟙 M)) = _
    simp only [Functor.map_id, Category.comp_id]
    rfl
  have e₂ : (Functor.uncurry.obj (sheafTensor (S.totalRingedTopos O).O)).map
        ((f, 𝟙 M) : (A, M) ⟶ (B, M)) =
      ((sheafTensor (S.totalRingedTopos O).O).map f).app M := by
    change _ ≫ ((sheafTensor (S.totalRingedTopos O).O).obj _).map (𝟙 M) = _
    simp only [Functor.map_id, Category.comp_id]
  have h := (S.componentRestrictionTensorIso O n).inv.naturality
    (X := (A, M)) (Y := (B, M)) (f, 𝟙 M)
  simpa only [Functor.comp_map, e₁, e₂] using h

/-- A section cancelled against its retraction in the middle of a composite, over abstract
morphisms: stated abstractly because the composites it is applied to are not type-correct at the
transparency a rewrite builds its motive at. -/
private theorem cancel_section_comp {D : Type*} [Category D] {P Q R X Y : D}
    (l : P ⟶ Q) (t : Q ⟶ R) (s : R ⟶ Q) (m : R ⟶ X) (g : X ⟶ Y) (m' : Q ⟶ Y)
    (hnat : s ≫ m' = m ≫ g) (h : t ≫ s = 𝟙 Q) : (l ≫ t) ≫ m ≫ g = l ≫ m' := by
  rw [← hnat, Category.assoc, ← Category.assoc t, h, Category.id_comp]

/-- **The sheaf-level adjunct of the projection map of Stacks 0D9E (2), followed by the
augmentation**, is the inverse left unitor of the component followed by the inverse of the
comparison of Stacks 03EL at the structure sheaf: the adjunct tensors the unit
`O_n ⟶ g_n^*g_{n!}O_n` into the module, and the augmentation undoes it by the triangle
identity. -/
theorem componentModuleProjectionAdjunct_comp_map_augmentation
    (M : (S.totalRingedTopos O).Modules) :
    (S.componentModuleProjectionAdjunct O n).app M ≫
        (S.componentModulesRestriction O n).map
          (((sheafTensor (S.totalRingedTopos O).O).map
            (S.componentModuleLowerShriekUnitAugmentation O n)).app M) =
      (S.componentModuleUnitTensorLeftUnitor O n).inv.app
          ((S.componentModulesRestriction O n).obj M) ≫
        (S.componentRestrictionTensorIso O n).inv.app
          (SheafOfModules.unit (S.totalRingSheaf O), M) := by
  have hnat := S.componentRestrictionTensorIso_inv_naturality_left O n
    (S.componentModuleLowerShriekUnitAugmentation O n) M
  have htri : ((sheafTensor (S.componentRingedTopos O n).O).map
          ((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).unit.app
            (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)))).app
        ((S.componentModulesRestriction O n).obj M) ≫
      ((sheafTensor (S.componentRingedTopos O n).O).map
          ((S.componentModulesRestriction O n).map
            (S.componentModuleLowerShriekUnitAugmentation O n))).app
        ((S.componentModulesRestriction O n).obj M) = 𝟙 _ :=
    (NatTrans.comp_app _ _ _).symm.trans ((congrArg (fun k => k.app
        ((S.componentModulesRestriction O n).obj M))
      (((sheafTensor (S.componentRingedTopos O n).O).map_comp _ _).symm.trans
        ((congrArg (sheafTensor (S.componentRingedTopos O n).O).map
          (S.unit_comp_map_componentModuleLowerShriekUnitAugmentation O n)).trans
          ((sheafTensor (S.componentRingedTopos O n).O).map_id _)))).trans
      (NatTrans.id_app _ _))
  have happ : (S.componentModuleProjectionAdjunct O n).app M =
      ((S.componentModuleUnitTensorLeftUnitor O n).inv.app
          ((S.componentModulesRestriction O n).obj M) ≫
        ((sheafTensor (S.componentRingedTopos O n).O).map
            ((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).unit.app
              (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)))).app
          ((S.componentModulesRestriction O n).obj M)) ≫
        (S.componentRestrictionTensorIso O n).inv.app
          (S.componentModuleLowerShriekUnit O n, M) := rfl
  exact (congrArg (fun k => k ≫ (S.componentModulesRestriction O n).map
      (((sheafTensor (S.totalRingedTopos O).O).map
        (S.componentModuleLowerShriekUnitAugmentation O n)).app M)) happ).trans
    (cancel_section_comp
      ((S.componentModuleUnitTensorLeftUnitor O n).inv.app
        ((S.componentModulesRestriction O n).obj M))
      (((sheafTensor (S.componentRingedTopos O n).O).map
          ((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).unit.app
            (SheafOfModules.unit (S.componentRingSheaf (S.totalRingSheaf O) n)))).app
        ((S.componentModulesRestriction O n).obj M))
      (((sheafTensor (S.componentRingedTopos O n).O).map
          ((S.componentModulesRestriction O n).map
            (S.componentModuleLowerShriekUnitAugmentation O n))).app
        ((S.componentModulesRestriction O n).obj M))
      ((S.componentRestrictionTensorIso O n).inv.app (S.componentModuleLowerShriekUnit O n, M))
      ((S.componentModulesRestriction O n).map
        (((sheafTensor (S.totalRingedTopos O).O).map
          (S.componentModuleLowerShriekUnitAugmentation O n)).app M))
      ((S.componentRestrictionTensorIso O n).inv.app (SheafOfModules.unit (S.totalRingSheaf O), M))
      hnat htri)

/-- The sheaf-level adjunct of the projection map of Stacks 0D9E (2), followed by the
augmentation tensored into the module, is a natural isomorphism. -/
instance isIso_componentModuleProjectionAdjunct_comp_whiskerRight :
    IsIso (S.componentModuleProjectionAdjunct O n ≫
      Functor.whiskerRight ((sheafTensor (S.totalRingedTopos O).O).map
        (S.componentModuleLowerShriekUnitAugmentation O n))
        (S.componentModulesRestriction O n)) := by
  have h : ∀ M, IsIso ((S.componentModuleProjectionAdjunct O n ≫
      Functor.whiskerRight ((sheafTensor (S.totalRingedTopos O).O).map
        (S.componentModuleLowerShriekUnitAugmentation O n))
        (S.componentModulesRestriction O n)).app M) := fun M => by
    rw [NatTrans.comp_app, Functor.whiskerRight_app,
      S.componentModuleProjectionAdjunct_comp_map_augmentation O n M]
    exact IsIso.comp_isIso' inferInstance
      (inferInstanceAs (IsIso ((S.componentRestrictionTensorIso O n).app
        (SheafOfModules.unit (S.totalRingSheaf O), M)).inv))
  exact NatIso.isIso_of_isIso_app _

/-- The derived functor of a natural isomorphism of exact functors is an isomorphism. -/
theorem isIso_derivedNatTrans {A B : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [Category B] [Abelian B] [HasDerivedCategory B] (F G : A ⥤ B) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (α : F ⟶ G) [hα : IsIso α] :
    IsIso (derivedNatTrans F G α) :=
  ⟨derivedNatTrans G F (inv α),
    by rw [← derivedNatTrans_comp, IsIso.hom_inv_id, derivedNatTrans_id],
    by rw [← derivedNatTrans_comp, IsIso.inv_hom_id, derivedNatTrans_id]⟩

/-- Two isomorphisms intertwining two maps intertwine them inversely too. -/
private theorem inv_comp_eq_comp_inv {D : Type*} [Category D] {A B C E : D} (eL : A ≅ B)
    (eU : C ≅ E) (x : A ⟶ C) (y : B ⟶ E) (h : x ≫ eU.hom = eL.hom ≫ y) :
    eL.inv ≫ x = y ≫ eU.inv := by
  rw [Iso.eq_comp_inv, Category.assoc, h, Iso.inv_hom_id_assoc]

/-- A functor applied to an identity between two-fold composites, extended by a third factor. -/
private theorem map_comp_comp_of_eq {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {A B E U F : C} {x : A ⟶ B} {y : B ⟶ E} {u : A ⟶ U} {v : U ⟶ E} (z : E ⟶ F)
    (h : x ≫ y = u ≫ v) : G.map x ≫ G.map (y ≫ z) = G.map u ≫ G.map v ≫ G.map z := by
  rw [← G.map_comp, ← G.map_comp, ← G.map_comp, ← Category.assoc, h, Category.assoc]

/-- The reassociation that assembles the adjunct of the projection map followed by the
augmentation: four facts about abstract morphisms, applied by `exact` because the composites are
not type-correct at the transparency a rewrite builds its motive at. -/
private theorem assemble_four {D : Type*} [Category D] {P Q R U V W Z : D}
    (a : P ⟶ Q) (c : Q ⟶ R) (g₁ : R ⟶ U) (gx : U ⟶ V) (g₂ : R ⟶ W) (gy : W ⟶ V) (w : Q ⟶ Z)
    (c' : Z ⟶ W) (θ : P ⟶ Z) (h₂ : g₁ ≫ gx = g₂ ≫ gy) (h₃ : c ≫ g₂ = w ≫ c') (h₄ : a ≫ w = θ) :
    (a ≫ c ≫ g₁) ≫ gx = θ ≫ c' ≫ gy := by
  rw [Category.assoc, Category.assoc, h₂, ← Category.assoc c, h₃, ← h₄]
  simp only [Category.assoc]

/-- `assemble_four`, concluding invertibility. -/
private theorem isIso_assemble_four {D : Type*} [Category D] {P Q R U V W Z : D}
    (a : P ⟶ Q) (c : Q ⟶ R) (g₁ : R ⟶ U) (gx : U ⟶ V) (g₂ : R ⟶ W) (gy : W ⟶ V) (w : Q ⟶ Z)
    (c' : Z ⟶ W) (θ : P ⟶ Z) (h₂ : g₁ ≫ gx = g₂ ≫ gy) (h₃ : c ≫ g₂ = w ≫ c') (h₄ : a ≫ w = θ)
    (hθ : IsIso θ) (hc' : IsIso c') (hgy : IsIso gy) : IsIso ((a ≫ c ≫ g₁) ≫ gx) := by
  rw [assemble_four a c g₁ gx g₂ gy w c' θ h₂ h₃ h₄]
  infer_instance

/-- **The adjunct of the projection map of Stacks 0D9E (2), followed by the augmentation, is an
isomorphism.** For an object `K` of `D(O)`, the transpose along `Lg_{n!} ⊣ Lg_n^*` of the
projection map `g_{n!}K_n ⟶ g_{n!}O_n ⊗^L_O K` followed by the derived tensor product with the
augmentation `g_{n!}O_n ⟶ O` and the unit constraint `O ⊗^L_O K ≅ K` is an automorphism of
`K_n`.

That transpose is the derived functor of the sheaf-level composite of
`componentModuleProjectionAdjunct_comp_map_augmentation`, read through the compositor of derived
functors and through the identification of `O ⊗^L_O -` with the derived functor of `O ⊗_O -`
(`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.flatSingleTensorIso`), whose naturality in
the flat module (`…flatSingleTensorIso_naturality`) moves the augmentation from the derived tensor
product to the sheaf level; the sheaf-level composite is an isomorphism. -/
theorem isIso_homEquiv_moduleProjection_comp_augmentation
    (hflat : ∀ (m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    IsIso (((S.componentModuleLowerShriekDerivedAdjunction O n hflat).homEquiv _ K)
      (S.moduleProjection O n hflat K ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).tensor.map
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).map
              (S.componentModuleLowerShriekUnitAugmentation O n))).app K ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).leftUnitIso
          (totalRingedSite O) K).hom)) := by
  have hU : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := (S.totalRingedTopos O).O)
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O)) :=
    Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit (Y := totalRingedSite O)
  let := Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.preservesFiniteLimits_sheafTensorObj
    (S.totalRingedTopos O).O _ hU
  let :=
    Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.preservesFiniteColimits_sheafTensorObj
      (S.totalRingedTopos O).O _ hU
  let : ((sheafTensor (S.totalRingedTopos O).O).obj (SheafOfModules.unit
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O))).Additive :=
    Functor.additive_of_preserves_binary_products _
  have hA := NatTrans.congr_app
    (Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.flatSingleTensorIso_naturality
      (S.totalRingedTopos O).O (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O)
      (S.isFlat_componentModuleLowerShriek_unit O n) hU
      (S.componentModuleLowerShriekUnitAugmentation O n)) K
  simp only [NatTrans.comp_app] at hA
  have hA' := inv_comp_eq_comp_inv
    ((Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.flatSingleTensorIso
      (S.totalRingedTopos O).O (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O)
      _ (S.isFlat_componentModuleLowerShriek_unit O n)).app K)
    ((Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.flatSingleTensorIso
      (S.totalRingedTopos O).O (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O)
      _ hU).app K) _ _ hA
  have hC := NatTrans.congr_app (derivedCompIso_refl_hom_whiskerRight
    (S.componentModuleLowerShriekUnitTensor O n)
    ((sheafTensor (S.totalRingedTopos O).O).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O)))
    (S.componentModulesRestriction O n)
    ((sheafTensor (S.totalRingedTopos O).O).map
      (S.componentModuleLowerShriekUnitAugmentation O n))) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hC
  have hD := NatTrans.congr_app (derivedNatTrans_comp (S.componentModulesRestriction O n)
    (S.componentModuleLowerShriekUnitTensor O n ⋙ S.componentModulesRestriction O n)
    ((sheafTensor (S.totalRingedTopos O).O).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O)) ⋙
      S.componentModulesRestriction O n)
    (S.componentModuleProjectionAdjunct O n)
    (Functor.whiskerRight ((sheafTensor (S.totalRingedTopos O).O).map
      (S.componentModuleLowerShriekUnitAugmentation O n)) (S.componentModulesRestriction O n))) K
  simp only [NatTrans.comp_app] at hD
  have h₀ : ((S.componentModuleLowerShriekDerivedAdjunction O n hflat).homEquiv _ K)
      (S.moduleProjection O n hflat K ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).tensor.map
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).map
              (S.componentModuleLowerShriekUnitAugmentation O n))).app K ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).leftUnitIso
          (totalRingedSite O) K).hom) =
      S.componentModuleProjectionAdjunctDerived O n K ≫
        (S.derivedComponentModuleRestriction O n).map
          (((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).tensor.map
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).map
                (S.componentModuleLowerShriekUnitAugmentation O n))).app K ≫
          ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).leftUnitIso
            (totalRingedSite O) K).hom) :=
    ((S.componentModuleLowerShriekDerivedAdjunction O n hflat).homEquiv_naturality_right _ _).trans
      (congrArg (fun k => k ≫ _) (Equiv.apply_symm_apply _ _))
  rw [h₀]
  have h₂ := map_comp_comp_of_eq (S.derivedComponentModuleRestriction O n)
    (((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).leftUnitIso
      (totalRingedSite O) K).hom) hA'
  have : IsIso (derivedNatTrans (S.componentModulesRestriction O n)
      ((sheafTensor (S.totalRingedTopos O).O).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (S.totalRingedTopos O).O)) ⋙
        S.componentModulesRestriction O n)
      (S.componentModuleProjectionAdjunct O n ≫
        Functor.whiskerRight ((sheafTensor (S.totalRingedTopos O).O).map
          (S.componentModuleLowerShriekUnitAugmentation O n))
          (S.componentModulesRestriction O n))) :=
    isIso_derivedNatTrans _ _ _
      (hα := S.isIso_componentModuleProjectionAdjunct_comp_whiskerRight O n)
  exact isIso_assemble_four _ _ _ _ _ _ _ _ _ h₂ hC.symm hD.symm
    (NatIso.isIso_app_of_isIso _ K) (NatIso.isIso_app_of_isIso _ K)
    (IsIso.comp_isIso' (Iso.isIso_hom ((S.derivedComponentModuleRestriction O n).mapIso
        ((Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.flatSingleTensorIso
          (S.totalRingedTopos O).O (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O)
          _ hU).app K).symm))
      (Iso.isIso_hom ((S.derivedComponentModuleRestriction O n).mapIso
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).leftUnitIso
          (totalRingedSite O) K))))

/-- **`isIso_homEquiv_moduleProjection_comp_augmentation` for any map transposing to the
identity.** A map `a : g_{n!}O_n ⟶ O` whose transpose along `g_{n!} ⊣ g_n^*` is the identity is the
augmentation, so the transpose of the projection map followed by `a ⊗^L_O K` and the unit
constraint is an isomorphism. -/
theorem isIso_homEquiv_moduleProjection_comp_of_homEquiv_eq_id
    (hflat : ∀ (m : SimplexCategory) (φ : n ⟶ m), (S.transitionRingedToposHom O φ).IsFlat)
    (a : S.componentModuleLowerShriekUnit O n ⟶ SheafOfModules.unit (S.totalRingSheaf O))
    (ha : (S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).homEquiv _ _ a = 𝟙 _)
    (K : DerivedCategory (S.totalRingedTopos O).Modules) :
    IsIso (((S.componentModuleLowerShriekDerivedAdjunction O n hflat).homEquiv _ K)
      (S.moduleProjection O n hflat K ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).tensor.map
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} O)) 0).map
              a)).app K ≫
        ((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct O).leftUnitIso
          (totalRingedSite O) K).hom)) := by
  obtain rfl : a = S.componentModuleLowerShriekUnitAugmentation O n :=
    (((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).homEquiv _
        _).symm_apply_apply a).symm.trans
      ((congrArg ((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).homEquiv
        _ _).symm ha).trans
      (((S.componentModuleLowerShriekAdjunction (S.totalRingSheaf O) n).homEquiv_counit _ _ _).trans
        ((congrArg (fun k => k ≫ _) (Functor.map_id _ _)).trans (Category.id_comp _))))
  exact S.isIso_homEquiv_moduleProjection_comp_augmentation O n hflat K

end CategoryTheory.SimplicialSiteSituation

end
