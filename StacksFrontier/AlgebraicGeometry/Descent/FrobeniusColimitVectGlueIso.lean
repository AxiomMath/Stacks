module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectGlueCover

/-!
# Glueing isomorphisms of restrictions in the fibre product of Tag 0EXD

Let `p` be a prime and let `q ≫ b = e ≫ z` be a commutative square of schemes in characteristic
`p`.  Two objects `S, S'` of the categorical fibre product
`colim_F Vect(Z) ×_{colim_F Vect(E)} colim_F Vect(X')` whose restrictions to the members of an
open cover of `X` are isomorphic, compatibly on the pairwise intersections, are isomorphic.  This
is the glueing of morphisms in the Zariski glueing step of the essential surjectivity half of
[Stacks, Tag 0EXD].

## Main results

* `AlgebraicGeometry.existsUnique_frobeniusColimitPullback_map_eq_of_inf`: morphisms of
  transitions along the members of an open cover, agreeing on pairwise intersections after the
  triangle comparisons, glue uniquely.
* `AlgebraicGeometry.nonempty_iso_of_frobeniusColimitLocRestrict`: **the glueing of
  isomorphisms**.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Frobenius

universe u

namespace Stacks.SheafOfModules

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} {M N : _root_.SheafOfModules.{u} R}

/-- Two morphisms over `V₁` and `V₂` whose slice restrictions to `V₁₂ ≤ V₁, V₂` agree, as
morphisms over `V₁₂`, have the same components at every open below `V₁₂`. -/
theorem val_app_eq_of_overMap_eq {V₁ V₂ V₁₂ W' : Opens X} (h₁ : V₁₂ ≤ V₁) (h₂ : V₁₂ ≤ V₂)
    (φ₁ : M.over V₁ ⟶ N.over V₁) (φ₂ : M.over V₂ ⟶ N.over V₂)
    (h : @Eq (M.over V₁₂ ⟶ N.over V₁₂) ((_root_.SheafOfModules.overMap R (homOfLE h₁)).map φ₁)
      ((_root_.SheafOfModules.overMap R (homOfLE h₂)).map φ₂))
    (h' : W' ≤ V₁₂) (hW₁ : W' ≤ V₁) (hW₂ : W' ≤ V₂) :
    φ₁.val.app (op (Over.mk (homOfLE hW₁))) = φ₂.val.app (op (Over.mk (homOfLE hW₂))) :=
  congrArg (fun t : M.over V₁₂ ⟶ N.over V₁₂ => t.val.app (op (Over.mk (homOfLE h')))) h

end Stacks.SheafOfModules

namespace AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

/-! ### Glueing morphisms of transitions over an open cover -/

section GlueHom

variable (Y : Scheme.{u}) (hY : IsInCharacteristic Y p)

/-- Two morphisms of transitions along the inclusions of `V₁` and `V₂` which agree over
`V₁ ⊓ V₂` after the triangle comparisons come from morphisms of slice restrictions agreeing over
`V₁ ⊓ V₂`. -/
theorem frobeniusColimitPullbackHomEquivOver_symm_overMap_inf (V₁ V₂ : Y.Opens)
    {M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf Y p hY)}
    (ψ₁ : (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p V₁.ι
          (isInCharacteristic_toScheme hY V₁) hY)).obj M ⟶
        (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p V₁.ι
          (isInCharacteristic_toScheme hY V₁) hY)).obj N)
    (ψ₂ : (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p V₂.ι
          (isInCharacteristic_toScheme hY V₂) hY)).obj M ⟶
        (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p V₂.ι
          (isInCharacteristic_toScheme hY V₂) hY)).obj N)
    (h : (frobeniusColimitPullbackTriangleIso p (Y.homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁))
          V₁.ι (V₁ ⊓ V₂).ι (isInCharacteristic_toScheme hY _)
          (isInCharacteristic_toScheme hY _) hY (Scheme.homOfLE_ι Y _)).inv.app M ≫
        (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p
          (Y.homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)) (isInCharacteristic_toScheme hY _)
          (isInCharacteristic_toScheme hY _))).map ψ₁ ≫
        (frobeniusColimitPullbackTriangleIso p (Y.homOfLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁))
          V₁.ι (V₁ ⊓ V₂).ι (isInCharacteristic_toScheme hY _)
          (isInCharacteristic_toScheme hY _) hY (Scheme.homOfLE_ι Y _)).hom.app N =
      (frobeniusColimitPullbackTriangleIso p (Y.homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂))
          V₂.ι (V₁ ⊓ V₂).ι (isInCharacteristic_toScheme hY _)
          (isInCharacteristic_toScheme hY _) hY (Scheme.homOfLE_ι Y _)).inv.app M ≫
        (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p
          (Y.homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)) (isInCharacteristic_toScheme hY _)
          (isInCharacteristic_toScheme hY _))).map ψ₂ ≫
        (frobeniusColimitPullbackTriangleIso p (Y.homOfLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂))
          V₂.ι (V₁ ⊓ V₂).ι (isInCharacteristic_toScheme hY _)
          (isInCharacteristic_toScheme hY _) hY (Scheme.homOfLE_ι Y _)).hom.app N)
    {W' : Y.Opens} (h₁ : W' ≤ V₁) (h₂ : W' ≤ V₂) :
    ((frobeniusColimitPullbackHomEquivOver Y p hY V₁
        (isInCharacteristic_toScheme hY V₁) M N).symm ψ₁).val.app (op (Over.mk (homOfLE h₁))) =
      ((frobeniusColimitPullbackHomEquivOver Y p hY V₂
        (isInCharacteristic_toScheme hY V₂) M N).symm ψ₂).val.app
          (op (Over.mk (homOfLE h₂))) := by
  have e₁ := frobeniusColimitPullbackHomEquivOver_overMap Y p hY
    (inf_le_left : V₁ ⊓ V₂ ≤ V₁) (isInCharacteristic_toScheme hY _)
    (isInCharacteristic_toScheme hY _)
    ((frobeniusColimitPullbackHomEquivOver Y p hY V₁
      (isInCharacteristic_toScheme hY V₁) M N).symm ψ₁)
  have e₂ := frobeniusColimitPullbackHomEquivOver_overMap Y p hY
    (inf_le_right : V₁ ⊓ V₂ ≤ V₂) (isInCharacteristic_toScheme hY _)
    (isInCharacteristic_toScheme hY _)
    ((frobeniusColimitPullbackHomEquivOver Y p hY V₂
      (isInCharacteristic_toScheme hY V₂) M N).symm ψ₂)
  rw [Equiv.apply_symm_apply] at e₁ e₂
  have key := (frobeniusColimitPullbackHomEquivOver Y p hY (V₁ ⊓ V₂)
    (isInCharacteristic_toScheme hY _) M N).injective (e₁.trans (h.trans e₂.symm))
  exact Stacks.SheafOfModules.val_app_eq_of_overMap_eq _ _ _ _ key (le_inf h₁ h₂) h₁ h₂

/-- **Morphisms of transitions along the members of an open cover glue**, as soon as they agree
over each pairwise intersection after the triangle comparisons of the inclusions. -/
theorem existsUnique_frobeniusColimitPullback_map_eq_of_inf {J : Type u} (W : J → Y.Opens)
    (hW : ⨆ j, W j = ⊤)
    {M N : _root_.SheafOfModules.{u} (frobeniusColimitRingSheaf Y p hY)}
    (ψ : ∀ j, (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p (W j).ι
          (isInCharacteristic_toScheme hY (W j)) hY)).obj M ⟶
        (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p (W j).ι
          (isInCharacteristic_toScheme hY (W j)) hY)).obj N)
    (hψ : ∀ j k,
      (frobeniusColimitPullbackTriangleIso p (Y.homOfLE (inf_le_left : W j ⊓ W k ≤ W j))
          (W j).ι (W j ⊓ W k).ι (isInCharacteristic_toScheme hY _)
          (isInCharacteristic_toScheme hY _) hY (Scheme.homOfLE_ι Y _)).inv.app M ≫
        (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p
          (Y.homOfLE (inf_le_left : W j ⊓ W k ≤ W j)) (isInCharacteristic_toScheme hY _)
          (isInCharacteristic_toScheme hY _))).map (ψ j) ≫
        (frobeniusColimitPullbackTriangleIso p (Y.homOfLE (inf_le_left : W j ⊓ W k ≤ W j))
          (W j).ι (W j ⊓ W k).ι (isInCharacteristic_toScheme hY _)
          (isInCharacteristic_toScheme hY _) hY (Scheme.homOfLE_ι Y _)).hom.app N =
      (frobeniusColimitPullbackTriangleIso p (Y.homOfLE (inf_le_right : W j ⊓ W k ≤ W k))
          (W k).ι (W j ⊓ W k).ι (isInCharacteristic_toScheme hY _)
          (isInCharacteristic_toScheme hY _) hY (Scheme.homOfLE_ι Y _)).inv.app M ≫
        (_root_.SheafOfModules.pullback.{u} (frobeniusColimitStructureSheafHom p
          (Y.homOfLE (inf_le_right : W j ⊓ W k ≤ W k)) (isInCharacteristic_toScheme hY _)
          (isInCharacteristic_toScheme hY _))).map (ψ k) ≫
        (frobeniusColimitPullbackTriangleIso p (Y.homOfLE (inf_le_right : W j ⊓ W k ≤ W k))
          (W k).ι (W j ⊓ W k).ι (isInCharacteristic_toScheme hY _)
          (isInCharacteristic_toScheme hY _) hY (Scheme.homOfLE_ι Y _)).hom.app N) :
    ∃! χ : M ⟶ N, ∀ j, (_root_.SheafOfModules.pullback.{u}
      (frobeniusColimitStructureSheafHom p (W j).ι
        (isInCharacteristic_toScheme hY (W j)) hY)).map χ = ψ j := by
  refine existsUnique_frobeniusColimitPullback_map_eq Y p hY W hW
    (fun j => (frobeniusColimitPullbackHomEquivOver Y p hY (W j)
      (isInCharacteristic_toScheme hY (W j)) M N).symm (ψ j)) ψ
    (fun j => Equiv.apply_symm_apply _ _) (fun i j W' hi hj => ?_)
  exact frobeniusColimitPullbackHomEquivOver_symm_overMap_inf p Y hY (W i) (W j) (ψ i) (ψ j)
    (hψ i j) hi hj

/-- The inverse triangle comparison on the finite locally free modules, read on the underlying
sheaves of modules. -/
theorem frobeniusColimitVectorBundlesPullbackTriangleIso_inv_app_hom {R S T : Scheme.{u}}
    (f : R ⟶ S) (g : S ⟶ T) (fg : R ⟶ T) (hR : IsInCharacteristic R p)
    (hS : IsInCharacteristic S p) (hT : IsInCharacteristic T p) (w : f ≫ g = fg)
    (M : frobeniusColimitVectorBundles T p hT) :
    ((frobeniusColimitVectorBundlesPullbackTriangleIso p f g fg hR hS hT w).inv.app M).hom =
      (frobeniusColimitPullbackTriangleIso p f g fg hR hS hT w).inv.app M.obj := by
  subst w
  rw [frobeniusColimitVectorBundlesPullbackTriangleIso_rfl,
    frobeniusColimitPullbackTriangleIso_rfl,
    frobeniusColimitVectorBundlesPullbackComp_inv_app_hom]

/-- **Morphisms of transitions of finite locally free modules along the members of an open cover
glue**, as soon as they agree over each pairwise intersection after the triangle comparisons. -/
theorem existsUnique_frobeniusColimitVectorBundlesPullback_map_eq_of_inf {J : Type u}
    (W : J → Y.Opens) (hW : ⨆ j, W j = ⊤) {M N : frobeniusColimitVectorBundles Y p hY}
    (ψ : ∀ j, (frobeniusColimitVectorBundlesPullback p (W j).ι
          (isInCharacteristic_toScheme hY (W j)) hY).obj M ⟶
        (frobeniusColimitVectorBundlesPullback p (W j).ι
          (isInCharacteristic_toScheme hY (W j)) hY).obj N)
    (hψ : ∀ j k,
      (frobeniusColimitVectorBundlesPullbackTriangleIso p
          (Y.homOfLE (inf_le_left : W j ⊓ W k ≤ W j))
          (W j).ι (W j ⊓ W k).ι (isInCharacteristic_toScheme hY _)
          (isInCharacteristic_toScheme hY _) hY (Scheme.homOfLE_ι Y _)).inv.app M ≫
        (frobeniusColimitVectorBundlesPullback p (Y.homOfLE (inf_le_left : W j ⊓ W k ≤ W j))
          (isInCharacteristic_toScheme hY _) (isInCharacteristic_toScheme hY _)).map (ψ j) ≫
        (frobeniusColimitVectorBundlesPullbackTriangleIso p
          (Y.homOfLE (inf_le_left : W j ⊓ W k ≤ W j))
          (W j).ι (W j ⊓ W k).ι (isInCharacteristic_toScheme hY _)
          (isInCharacteristic_toScheme hY _) hY (Scheme.homOfLE_ι Y _)).hom.app N =
      (frobeniusColimitVectorBundlesPullbackTriangleIso p
          (Y.homOfLE (inf_le_right : W j ⊓ W k ≤ W k))
          (W k).ι (W j ⊓ W k).ι (isInCharacteristic_toScheme hY _)
          (isInCharacteristic_toScheme hY _) hY (Scheme.homOfLE_ι Y _)).inv.app M ≫
        (frobeniusColimitVectorBundlesPullback p (Y.homOfLE (inf_le_right : W j ⊓ W k ≤ W k))
          (isInCharacteristic_toScheme hY _) (isInCharacteristic_toScheme hY _)).map (ψ k) ≫
        (frobeniusColimitVectorBundlesPullbackTriangleIso p
          (Y.homOfLE (inf_le_right : W j ⊓ W k ≤ W k))
          (W k).ι (W j ⊓ W k).ι (isInCharacteristic_toScheme hY _)
          (isInCharacteristic_toScheme hY _) hY (Scheme.homOfLE_ι Y _)).hom.app N) :
    ∃! χ : M ⟶ N, ∀ j, (frobeniusColimitVectorBundlesPullback p (W j).ι
      (isInCharacteristic_toScheme hY (W j)) hY).map χ = ψ j := by
  obtain ⟨χ, hχ, hu⟩ := existsUnique_frobeniusColimitPullback_map_eq_of_inf p Y hY W hW
    (M := M.obj) (N := N.obj) (fun j => (ψ j).hom) (fun j k => by
      have h := congrArg (fun f => f.hom) (hψ j k)
      simp only [ObjectProperty.FullSubcategory.comp_hom,
        frobeniusColimitVectorBundlesPullbackTriangleIso_hom_app_hom,
        frobeniusColimitVectorBundlesPullbackTriangleIso_inv_app_hom,
        frobeniusColimitVectorBundlesPullback_map_hom] at h
      exact h)
  exact ⟨ObjectProperty.homMk χ, fun j => ObjectProperty.hom_ext _ (hχ j),
    fun χ' hχ' => ObjectProperty.hom_ext _ (hu χ'.hom fun j => congrArg (fun f => f.hom) (hχ' j))⟩

end GlueHom

/-! ### Abstract bookkeeping -/

section Abstract

variable {C D : Type*} [Category C] [Category D]

/-- Two morphisms inverse to equal morphisms are equal. -/
theorem eq_of_comp_eq_id_of_comp_eq_id {X Y : C} {a : X ⟶ Y} {x x' : Y ⟶ X}
    (h₁ : a ≫ x = 𝟙 _) (h₂ : x' ≫ a = 𝟙 _) : x = x' :=
  calc x = 𝟙 _ ≫ x := (Category.id_comp x).symm
    _ = (x' ≫ a) ≫ x := by rw [h₂]
    _ = x' := by rw [Category.assoc, h₁, Category.comp_id]

variable {CZ CX' CE CW CX'W CD : Type*} [Category CZ] [Category CX'] [Category CE]
  [Category CW] [Category CX'W] [Category CD]

/-- The compatibility over the exceptional corner of a glued morphism of the categorical fibre
product, read after restriction to a member of the cover: an abstract statement, with the
transition functors and the two square comparisons as variables. -/
theorem map_comp_iso_eq_of_restrict (Fe : CZ ⥤ CE) (Fq : CX' ⥤ CE) (P : CE ⥤ CD)
    (Fz : CZ ⥤ CW) (Fb : CX' ⥤ CX'W) (Fe' : CW ⥤ CD) (Fq' : CX'W ⥤ CD)
    (σZ : Fe ⋙ P ≅ Fz ⋙ Fe') (σX : Fq ⋙ P ≅ Fb ⋙ Fq')
    {A A' : CZ} {B B' : CX'} (i : Fe.obj A ≅ Fq.obj B) (i' : Fe.obj A' ≅ Fq.obj B')
    (χ₁ : A ⟶ A') (χ₂ : B ⟶ B')
    (h : Fe'.map (Fz.map χ₁) ≫
        ((σZ.app A').symm ≪≫ P.mapIso i' ≪≫ σX.app B').hom =
      ((σZ.app A).symm ≪≫ P.mapIso i ≪≫ σX.app B).hom ≫ Fq'.map (Fb.map χ₂)) :
    P.map (Fe.map χ₁ ≫ i'.hom) = P.map (i.hom ≫ Fq.map χ₂) := by
  have n₁ := σZ.hom.naturality χ₁
  have n₂ := σX.hom.naturality χ₂
  simp only [Functor.comp_map] at n₁ n₂
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.mapIso_hom] at h
  have e₁ : P.map (Fe.map χ₁) = σZ.hom.app A ≫ Fe'.map (Fz.map χ₁) ≫ σZ.inv.app A' := by
    rw [← reassoc_of% n₁, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have e₂ : P.map (Fq.map χ₂) = σX.hom.app B ≫ Fq'.map (Fb.map χ₂) ≫ σX.inv.app B' := by
    rw [← reassoc_of% n₂, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  rw [Functor.map_comp, Functor.map_comp, e₁, e₂]
  have h' := congrArg (fun t => σZ.hom.app A ≫ t ≫ σX.inv.app B') h
  simp only [Category.assoc, Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc, Functor.comp_obj,
    Category.comp_id] at h'
  simpa only [Category.assoc] using h'

end Abstract

/-- **Morphisms of finite locally free modules are determined by their transitions along the
members of an open cover.** -/
theorem frobeniusColimitVectorBundlesPullback_map_injective (Y : Scheme.{u})
    (hY : IsInCharacteristic Y p) {J : Type u} (W : J → Y.Opens) (hW : ⨆ j, W j = ⊤)
    {M N : frobeniusColimitVectorBundles Y p hY} (f g : M ⟶ N)
    (h : ∀ j, (frobeniusColimitVectorBundlesPullback p (W j).ι
      (isInCharacteristic_toScheme hY (W j)) hY).map f =
      (frobeniusColimitVectorBundlesPullback p (W j).ι
        (isInCharacteristic_toScheme hY (W j)) hY).map g) : f = g :=
  ObjectProperty.hom_ext _ (frobeniusColimitPullback_map_injective p Y hY W hW f.hom g.hom
    fun j => congrArg (fun t => t.hom) (h j))

/-! ### Glueing isomorphisms of restrictions -/

section GlueIso

variable {X X' Z E : Scheme.{u}}
  (b : X' ⟶ X) (z : Z ⟶ X) (q : E ⟶ X') (e : E ⟶ Z)
  (hX : IsInCharacteristic X p) (hX' : IsInCharacteristic X' p)
  (hZ : IsInCharacteristic Z p) (hE : IsInCharacteristic E p) (hw : q ≫ b = e ≫ z)

/-- Preimages of a cover of the target under a morphism of schemes cover the source. -/
private theorem iSup_preimage_eq_top {A B : Scheme.{u}} (f : A ⟶ B) {J : Type*} (V : J → B.Opens)
    (hV : ⨆ j, V j = ⊤) : ⨆ j, f ⁻¹ᵁ V j = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, hV, Scheme.Hom.preimage_top]

/-- The centre component of the restriction of a morphism to a smaller open. -/
theorem frobeniusColimitLocResHom_fst {U U' : X.Opens} (h : U' ≤ U)
    {S S' : CategoricalPullback (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p q hE hX')}
    (α : (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U).obj S ⟶
      (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U).obj S') :
    (frobeniusColimitLocResHom p b z q e hX' hZ hE hw h α).fst =
      (frobeniusColimitVectorBundlesPullbackTriangleIso p (Z.homOfLE (z.preimage_mono h))
          (z ⁻¹ᵁ U).ι (z ⁻¹ᵁ U').ι (isInCharacteristic_toScheme hZ _)
          (isInCharacteristic_toScheme hZ _) hZ (Scheme.homOfLE_ι _ _)).inv.app S.fst ≫
        (frobeniusColimitVectorBundlesPullback p (Z.homOfLE (z.preimage_mono h))
          (isInCharacteristic_toScheme hZ _) (isInCharacteristic_toScheme hZ _)).map α.fst ≫
        (frobeniusColimitVectorBundlesPullbackTriangleIso p (Z.homOfLE (z.preimage_mono h))
          (z ⁻¹ᵁ U).ι (z ⁻¹ᵁ U').ι (isInCharacteristic_toScheme hZ _)
          (isInCharacteristic_toScheme hZ _) hZ (Scheme.homOfLE_ι _ _)).hom.app S'.fst :=
  rfl

/-- The modification component of the restriction of a morphism to a smaller open. -/
theorem frobeniusColimitLocResHom_snd {U U' : X.Opens} (h : U' ≤ U)
    {S S' : CategoricalPullback (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p q hE hX')}
    (α : (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U).obj S ⟶
      (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw U).obj S') :
    (frobeniusColimitLocResHom p b z q e hX' hZ hE hw h α).snd =
      (frobeniusColimitVectorBundlesPullbackTriangleIso p (X'.homOfLE (b.preimage_mono h))
          (b ⁻¹ᵁ U).ι (b ⁻¹ᵁ U').ι (isInCharacteristic_toScheme hX' _)
          (isInCharacteristic_toScheme hX' _) hX' (Scheme.homOfLE_ι _ _)).inv.app S.snd ≫
        (frobeniusColimitVectorBundlesPullback p (X'.homOfLE (b.preimage_mono h))
          (isInCharacteristic_toScheme hX' _) (isInCharacteristic_toScheme hX' _)).map α.snd ≫
        (frobeniusColimitVectorBundlesPullbackTriangleIso p (X'.homOfLE (b.preimage_mono h))
          (b ⁻¹ᵁ U).ι (b ⁻¹ᵁ U').ι (isInCharacteristic_toScheme hX' _)
          (isInCharacteristic_toScheme hX' _) hX' (Scheme.homOfLE_ι _ _)).hom.app S'.snd :=
  rfl

variable {J : Type u} (V : J → X.Opens) (hV : ⨆ j, V j = ⊤)
  (S S' : CategoricalPullback (frobeniusColimitVectorBundlesPullback p e hE hZ)
      (frobeniusColimitVectorBundlesPullback p q hE hX'))

include hV in
/-- **The centre components of compatible morphisms of restrictions glue.** -/
theorem exists_frobeniusColimitLocRestrict_fst_glue
    (α : ∀ j, (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw (V j)).obj S ⟶
      (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw (V j)).obj S')
    (hα : ∀ j k, frobeniusColimitLocResHom p b z q e hX' hZ hE hw
        (inf_le_left : V j ⊓ V k ≤ V j) (α j) =
      frobeniusColimitLocResHom p b z q e hX' hZ hE hw
        (inf_le_right : V j ⊓ V k ≤ V k) (α k)) :
    ∃ χ : S.fst ⟶ S'.fst, ∀ j, (frobeniusColimitVectorBundlesPullback p (z ⁻¹ᵁ V j).ι
      (isInCharacteristic_toScheme hZ _) hZ).map χ = (α j).fst := by
  obtain ⟨χ, hχ, -⟩ := existsUnique_frobeniusColimitVectorBundlesPullback_map_eq_of_inf p Z hZ
    (fun j => z ⁻¹ᵁ V j) (iSup_preimage_eq_top z V hV) (fun j => (α j).fst) (fun j k => by
      have h := congrArg CategoricalPullback.Hom.fst (hα j k)
      rw [frobeniusColimitLocResHom_fst, frobeniusColimitLocResHom_fst] at h
      exact h)
  exact ⟨χ, hχ⟩

include hV in
/-- **The modification components of compatible morphisms of restrictions glue.** -/
theorem exists_frobeniusColimitLocRestrict_snd_glue
    (α : ∀ j, (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw (V j)).obj S ⟶
      (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw (V j)).obj S')
    (hα : ∀ j k, frobeniusColimitLocResHom p b z q e hX' hZ hE hw
        (inf_le_left : V j ⊓ V k ≤ V j) (α j) =
      frobeniusColimitLocResHom p b z q e hX' hZ hE hw
        (inf_le_right : V j ⊓ V k ≤ V k) (α k)) :
    ∃ χ : S.snd ⟶ S'.snd, ∀ j, (frobeniusColimitVectorBundlesPullback p (b ⁻¹ᵁ V j).ι
      (isInCharacteristic_toScheme hX' _) hX').map χ = (α j).snd := by
  obtain ⟨χ, hχ, -⟩ := existsUnique_frobeniusColimitVectorBundlesPullback_map_eq_of_inf p X' hX'
    (fun j => b ⁻¹ᵁ V j) (iSup_preimage_eq_top b V hV) (fun j => (α j).snd) (fun j k => by
      have h := congrArg CategoricalPullback.Hom.snd (hα j k)
      rw [frobeniusColimitLocResHom_snd, frobeniusColimitLocResHom_snd] at h
      exact h)
  exact ⟨χ, hχ⟩

include hV in
/-- **The glued components are compatible with the structural isomorphisms**: the compatibility
over the exceptional corner holds after restriction to each member of the cover of `E`, where it
is the compatibility of the local morphisms. -/
theorem frobeniusColimitLocRestrict_glue_w
    (α : ∀ j, (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw (V j)).obj S ⟶
      (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw (V j)).obj S')
    (χ₁ : S.fst ⟶ S'.fst) (χ₂ : S.snd ⟶ S'.snd)
    (h₁ : ∀ j, (frobeniusColimitVectorBundlesPullback p (z ⁻¹ᵁ V j).ι
      (isInCharacteristic_toScheme hZ _) hZ).map χ₁ = (α j).fst)
    (h₂ : ∀ j, (frobeniusColimitVectorBundlesPullback p (b ⁻¹ᵁ V j).ι
      (isInCharacteristic_toScheme hX' _) hX').map χ₂ = (α j).snd) :
    (frobeniusColimitVectorBundlesPullback p e hE hZ).map χ₁ ≫ S'.iso.hom =
      S.iso.hom ≫ (frobeniusColimitVectorBundlesPullback p q hE hX').map χ₂ := by
  refine frobeniusColimitVectorBundlesPullback_map_injective p E hE (fun j => e ⁻¹ᵁ z ⁻¹ᵁ V j)
    (iSup_preimage_eq_top e _ (iSup_preimage_eq_top z V hV)) _ _ fun j => ?_
  have hw' := (α j).w
  rw [← h₁ j, ← h₂ j] at hw'
  exact map_comp_iso_eq_of_restrict _ _ _ _ _ _ _ _ _ S.iso S'.iso χ₁ χ₂ hw'

include hV in
/-- **Isomorphisms of the restrictions of two objects of the categorical fibre product of
[Stacks, Tag 0EXD] to the members of an open cover of the base, agreeing on the pairwise
intersections, glue to an isomorphism.** -/
theorem nonempty_iso_of_frobeniusColimitLocRestrict
    (ι : ∀ j, (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw (V j)).obj S ≅
      (frobeniusColimitLocRestrict p b z q e hX' hZ hE hw (V j)).obj S')
    (hι : ∀ j k, frobeniusColimitLocResHom p b z q e hX' hZ hE hw
        (inf_le_left : V j ⊓ V k ≤ V j) (ι j).hom =
      frobeniusColimitLocResHom p b z q e hX' hZ hE hw
        (inf_le_right : V j ⊓ V k ≤ V k) (ι k).hom) :
    Nonempty (S ≅ S') := by
  have hι' : ∀ j k, frobeniusColimitLocResHom p b z q e hX' hZ hE hw
      (inf_le_left : V j ⊓ V k ≤ V j) (ι j).inv =
      frobeniusColimitLocResHom p b z q e hX' hZ hE hw
        (inf_le_right : V j ⊓ V k ≤ V k) (ι k).inv := fun j k =>
    eq_of_comp_eq_id_of_comp_eq_id
      (by rw [← frobeniusColimitLocResHom_comp, Iso.hom_inv_id, frobeniusColimitLocResHom_id])
      (by rw [hι j k, ← frobeniusColimitLocResHom_comp, Iso.inv_hom_id,
        frobeniusColimitLocResHom_id])
  have hWZ := iSup_preimage_eq_top z V hV
  have hWX := iSup_preimage_eq_top b V hV
  obtain ⟨χ₁, h₁⟩ := exists_frobeniusColimitLocRestrict_fst_glue p b z q e hX' hZ hE hw V hV S S'
    (fun j => (ι j).hom) hι
  obtain ⟨χ₁', h₁'⟩ := exists_frobeniusColimitLocRestrict_fst_glue p b z q e hX' hZ hE hw V hV S' S
    (fun j => (ι j).inv) hι'
  obtain ⟨χ₂, h₂⟩ := exists_frobeniusColimitLocRestrict_snd_glue p b z q e hX' hZ hE hw V hV S S'
    (fun j => (ι j).hom) hι
  obtain ⟨χ₂', h₂'⟩ := exists_frobeniusColimitLocRestrict_snd_glue p b z q e hX' hZ hE hw V hV S' S
    (fun j => (ι j).inv) hι'
  refine ⟨CategoricalPullback.mkIso
    { hom := χ₁, inv := χ₁'
      hom_inv_id := frobeniusColimitVectorBundlesPullback_map_injective p Z hZ _ hWZ _ _ fun j => by
        rw [Functor.map_comp, h₁ j, h₁' j, CategoryTheory.Functor.map_id]
        exact congrArg CategoricalPullback.Hom.fst (ι j).hom_inv_id
      inv_hom_id := frobeniusColimitVectorBundlesPullback_map_injective p Z hZ _ hWZ _ _ fun j => by
        rw [Functor.map_comp, h₁ j, h₁' j, CategoryTheory.Functor.map_id]
        exact congrArg CategoricalPullback.Hom.fst (ι j).inv_hom_id }
    { hom := χ₂, inv := χ₂'
      hom_inv_id := frobeniusColimitVectorBundlesPullback_map_injective p X' hX' _ hWX _ _
        fun j => by
          rw [Functor.map_comp, h₂ j, h₂' j, CategoryTheory.Functor.map_id]
          exact congrArg CategoricalPullback.Hom.snd (ι j).hom_inv_id
      inv_hom_id := frobeniusColimitVectorBundlesPullback_map_injective p X' hX' _ hWX _ _
        fun j => by
          rw [Functor.map_comp, h₂ j, h₂' j, CategoryTheory.Functor.map_id]
          exact congrArg CategoricalPullback.Hom.snd (ι j).inv_hom_id }
    (frobeniusColimitLocRestrict_glue_w p b z q e hX' hZ hE hw V hV S S' (fun j => (ι j).hom)
      χ₁ χ₂ h₁ h₂)⟩

end GlueIso

end AlgebraicGeometry

end
