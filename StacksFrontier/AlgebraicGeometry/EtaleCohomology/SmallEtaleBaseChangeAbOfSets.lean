module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PushforwardBaseChangeUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleBaseChangeAbFinite

/-!
# The abelian base change map from the base change map of sheaves of sets

For a commutative square

```
X' ←-h-  Y
|f'      |e
S  ←-g-  T
```

of schemes there are two underived base change maps `(f')⁻¹ g_* ⟶ h_* e⁻¹` on the small étale
sites: `Stacks.EtaleCohomology.smallEtaleSetBaseChange`, on sheaves of sets, and
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb`, on abelian sheaves, which is the one the
higher-direct-image development of [Stacks, Tag 0F02] uses. This file proves that the abelian map
is invertible as soon as the set-valued map is, with no condition on the square, and deduces
[Stacks, Tag 0EYS] for abelian sheaves.

## Main definitions

* `Stacks.EtaleCohomology.compositeDirectImageCell` — the identification `e_* g_* ≅ h_* f_*` of
  the composite direct images around a square of functors of sites, at any coefficients, as a
  2-square. The base change maps of both coefficient categories are its mates.

## Main results

* `Stacks.EtaleCohomology.compositeDirectImageCell_app_sheafCompose` — the identification
  commutes with a change of coefficients.
* `Stacks.EtaleCohomology.isIso_mateEquiv_symm_compositeDirectImageCell_of_sheafCompose` — the
  mate of the identification transports along a change of coefficients `Φ : A ⥤ B` for which
  composition with `Φ` reflects isomorphisms: if the base change map is invertible at
  coefficients in `B`, it is invertible at coefficients in `A`.
* `Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isIso_smallEtaleSetBaseChange` — the
  abelian base change map is invertible as soon as the base change map of sheaves of sets is.
* `Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_flat_geometricallyReduced` —
  **[Stacks, Tag 0EYS] for abelian sheaves**: for a cartesian square whose left vertical morphism
  is flat, locally of finite presentation and has geometrically reduced fibres, the base change
  map `f⁻¹ g_* 𝓕 ⟶ h_* e⁻¹ 𝓕` is an isomorphism for every abelian sheaf `𝓕` on `T_étale`.

## Implementation notes

Both maps are mates of the identification `e_* g_* ≅ h_* (f')_*` of the composite direct images,
in two coefficient categories. They are compared with
`Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms`, through composition with
the forgetful functor of abelian groups. That functor reflects isomorphisms. It commutes with
direct image on the nose. It commutes with inverse image by
`Stacks.EtaleCohomology.coefficientPullbackTwoSquare`, whose mate is the identity
(`Stacks.EtaleCohomology.mateEquiv_coefficientPullbackTwoSquare`). The cube identity this needs
is `compositeDirectImageCell_app_sheafCompose`.

The transport and the cube identity are stated for an arbitrary square of functors of sites and
instantiated at the small étale sites. Stated directly at the small étale sites, the kernel
check of the cube identity does not finish within the default budget: it unfolds the base change
functors of étale schemes when comparing components.

The abelian map is the mate taken along `Stacks.EtaleCohomology.smallEtaleAdjunctionAb`, whose
left adjoint is Mathlib's abstract inverse image, and the set-valued map along
`Stacks.EtaleCohomology.smallEtaleInverseImageAdjunction`. The transport runs along the explicit
construction `CategoryTheory.Functor.sheafPullbackConstruction`; left adjoints of the same direct
image are related by `Stacks.CategoryTheory.isIso_mateEquiv_symm_of_leftAdjointUniq`.

## References

* [Stacks Project, Tag 0EYS](https://stacks.math.columbia.edu/tag/0EYS)
* [Stacks Project, Tag 0F02](https://stacks.math.columbia.edu/tag/0F02)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

section Pushforward

variable {C D E : Type*} [Category* C] [Category* D] [Category* E] {F : C ⥤ D} {G : D ⥤ E}
  {FG : C ⥤ E} (eFG : F ⋙ G ≅ FG) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (L : GrothendieckTopology E) [F.IsContinuous J K] [G.IsContinuous K L] [FG.IsContinuous J L]
  {A B : Type*} [Category* A] [Category* B] (Φ : A ⥤ B) [J.HasSheafCompose Φ]
  [K.HasSheafCompose Φ] [L.HasSheafCompose Φ]

omit [K.HasSheafCompose Φ] in
/-- The composition isomorphism of direct images commutes with a change of coefficients. -/
private theorem sheafPushforwardContinuousComp'_hom_app_sheafCompose (P : Sheaf L A) :
    (Functor.sheafPushforwardContinuousComp' eFG B J K L).hom.app ((sheafCompose L Φ).obj P) =
      (sheafCompose J Φ).map ((Functor.sheafPushforwardContinuousComp' eFG A J K L).hom.app P) :=
  by ext; simp; rfl

omit [K.HasSheafCompose Φ] in
/-- The inverse composition isomorphism of direct images commutes with a change of
coefficients. -/
private theorem sheafPushforwardContinuousComp'_inv_app_sheafCompose (P : Sheaf L A) :
    (Functor.sheafPushforwardContinuousComp' eFG B J K L).inv.app ((sheafCompose L Φ).obj P) =
      (sheafCompose J Φ).map ((Functor.sheafPushforwardContinuousComp' eFG A J K L).inv.app P) :=
  by ext; simp; rfl

end Pushforward

/-! ### The identification of composite direct images, for an arbitrary family of sites -/

section Cell

variable {CS CT CX CY : Type*} [Category* CS] [Category* CT] [Category* CX] [Category* CY]
  (JS : GrothendieckTopology CS) (JT : GrothendieckTopology CT) (JX : GrothendieckTopology CX)
  (JY : GrothendieckTopology CY) (ug : CS ⥤ CT) (uf : CS ⥤ CX) (ue : CT ⥤ CY) (uh : CX ⥤ CY)
  [ug.IsContinuous JS JT] [uf.IsContinuous JS JX] [ue.IsContinuous JT JY]
  [uh.IsContinuous JX JY] {ι : Type*} (uk : ι → (CS ⥤ CY)) [∀ i, (uk i).IsContinuous JS JY]
  {i₁ i₂ : ι} (αeg : ug ⋙ ue ≅ uk i₁) (αhf : uf ⋙ uh ≅ uk i₂) (hi : i₁ = i₂)

/-- **The identification `e_* g_* ≅ h_* f_*` of composite direct images** around a square of
functors of sites `ug ⋙ ue ≅ uk i₁` and `uf ⋙ uh ≅ uk i₂` with `i₁ = i₂`, at coefficients in
`A`, as a 2-square. -/
def compositeDirectImageCell (A : Type*) [Category* A] :
    TwoSquare (ue.sheafPushforwardContinuous A JT JY) (uh.sheafPushforwardContinuous A JX JY)
      (ug.sheafPushforwardContinuous A JS JT) (uf.sheafPushforwardContinuous A JS JX) :=
  TwoSquare.mk _ _ _ _ ((Functor.sheafPushforwardContinuousComp' αeg A JS JT JY).hom ≫
    eqToHom (congrArg (fun i ↦ (uk i).sheafPushforwardContinuous A JS JY) hi) ≫
    (Functor.sheafPushforwardContinuousComp' αhf A JS JX JY).inv)

variable {A B : Type*} [Category* A] [Category* B] (Φ : A ⥤ B) [JS.HasSheafCompose Φ]
  [JT.HasSheafCompose Φ] [JX.HasSheafCompose Φ] [JY.HasSheafCompose Φ]

omit [JT.HasSheafCompose Φ] [JX.HasSheafCompose Φ] in
/-- **The identification of composite direct images commutes with a change of coefficients.** -/
theorem compositeDirectImageCell_app_sheafCompose (P : Sheaf JY A) :
    (compositeDirectImageCell JS JT JX JY ug uf ue uh uk αeg αhf hi B).natTrans.app
        ((sheafCompose JY Φ).obj P) =
      (sheafCompose JS Φ).map
        ((compositeDirectImageCell JS JT JX JY ug uf ue uh uk αeg αhf hi A).natTrans.app P) := by
  subst hi
  simp only [compositeDirectImageCell, TwoSquare.natTrans, TwoSquare.mk, eqToHom_refl,
    Category.id_comp, NatTrans.comp_app, Functor.map_comp]
  rw [sheafPushforwardContinuousComp'_hom_app_sheafCompose,
    sheafPushforwardContinuousComp'_inv_app_sheafCompose]
  rfl

section Transport

variable [HasWeakSheafify JY A] [HasWeakSheafify JY B] [HasWeakSheafify JX A]
  [HasWeakSheafify JX B] [∀ P : CTᵒᵖ ⥤ A, ue.op.HasLeftKanExtension P]
  [∀ P : CTᵒᵖ ⥤ B, ue.op.HasLeftKanExtension P] [∀ P : CSᵒᵖ ⥤ A, uf.op.HasLeftKanExtension P]
  [∀ P : CSᵒᵖ ⥤ B, uf.op.HasLeftKanExtension P] [Φ.PreservesLeftKanExtensions ue.op]
  [Φ.PreservesLeftKanExtensions uf.op] [JY.PreservesSheafification Φ]
  [JX.PreservesSheafification Φ] [(sheafCompose JX Φ).ReflectsIsomorphisms]

/-- Direct image commutes with a change of coefficients on the nose. -/
private abbrev pushforwardSheafCompose {C D : Type*} [Category* C] [Category* D] (v : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [v.IsContinuous J K]
    [J.HasSheafCompose Φ] [K.HasSheafCompose Φ] :
    v.sheafPushforwardContinuous A J K ⋙ sheafCompose J Φ ⟶
      sheafCompose K Φ ⋙ v.sheafPushforwardContinuous B J K :=
  𝟙 _

private instance {C D : Type*} [Category* C] [Category* D] (v : C ⥤ D)
    (J : GrothendieckTopology C) (K : GrothendieckTopology D) [v.IsContinuous J K]
    [J.HasSheafCompose Φ] [K.HasSheafCompose Φ] : IsIso (pushforwardSheafCompose Φ v J K) :=
  ⟨⟨𝟙 _, Category.comp_id _, Category.comp_id _⟩⟩

include Φ in
/-- **The mate of the identification of composite direct images transports along a change of
coefficients that reflects isomorphisms.** If its mate, the base change map, is invertible at
coefficients in `B`, it is invertible at coefficients in `A`; the inverse images are those of
`CategoryTheory.Functor.sheafPullbackConstruction`. -/
theorem isIso_mateEquiv_symm_compositeDirectImageCell_of_sheafCompose
    (h : IsIso ((mateEquiv (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous ue B JT JY)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf B JS JX)).symm
      (compositeDirectImageCell JS JT JX JY ug uf ue uh uk αeg αhf hi B)).natTrans) :
    IsIso ((mateEquiv (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous ue A JT JY)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf A JS JX)).symm
      (compositeDirectImageCell JS JT JX JY ug uf ue uh uk αeg αhf hi A)).natTrans := by
  refine Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous ue A JT JY)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf A JS JX)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous ue B JT JY)
    (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous uf B JS JX)
    (coefficientPullbackTwoSquare ue JT JY Φ) (coefficientPullbackTwoSquare uf JS JX Φ)
    (pushforwardSheafCompose Φ ug JS JT) (inv (pushforwardSheafCompose Φ uh JX JY))
    (compositeDirectImageCell JS JT JX JY ug uf ue uh uk αeg αhf hi A)
    (compositeDirectImageCell JS JT JX JY ug uf ue uh uk αeg αhf hi B) ?_
  simp only [mateEquiv_coefficientPullbackTwoSquare]
  refine TwoSquare.ext _ _ fun P => ?_
  rw [AlgebraicGeometry.SmallEtale.ts_whiskerLeft_app,
    AlgebraicGeometry.SmallEtale.ts_whiskerRight_app,
    AlgebraicGeometry.SmallEtale.ts_vComp_app, AlgebraicGeometry.SmallEtale.ts_vComp_app]
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ ?_))
  have E := congrArg (fun φ ↦ φ.hom.app U)
    (compositeDirectImageCell_app_sheafCompose JS JT JX JY ug uf ue uh uk αeg αhf hi Φ P)
  have E' : (𝟙 _ ≫ 𝟙 _ ≫
      ((compositeDirectImageCell JS JT JX JY ug uf ue uh uk αeg αhf hi B).natTrans.app
        ((sheafCompose JY Φ).obj P)).hom.app U) ≫ 𝟙 _ =
      Φ.map (((compositeDirectImageCell JS JT JX JY ug uf ue uh uk αeg αhf hi A).natTrans.app
        P).hom.app U) ≫ 𝟙 _ := by
    simpa using E
  rw [IsIso.inv_eq_of_hom_inv_id (Category.comp_id (pushforwardSheafCompose Φ uh JX JY))]
  exact E'

end Transport

end Cell

section Bridge

/-- The inverse-image/direct-image adjunction for abelian sheaves on the small étale sites, with
the inverse image given by the explicit Kan extension and sheafification. -/
private abbrev constructionAdjAb {X Y : Scheme.{u}} (k : X ⟶ Y) :
    Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange k) Ab.{u + 1}
        (smallEtaleTopology Y) (smallEtaleTopology X) ⊣
      (smallEtaleBaseChange k).sheafPushforwardContinuous Ab.{u + 1}
        (smallEtaleTopology Y) (smallEtaleTopology X) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

/-- The inverse-image/direct-image adjunction for sheaves of sets on the small étale sites, with
the inverse image given by the explicit Kan extension and sheafification. -/
private abbrev constructionAdjSet {X Y : Scheme.{u}} (k : X ⟶ Y) :
    Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange k) (Type (u + 1))
        (smallEtaleTopology Y) (smallEtaleTopology X) ⊣
      (smallEtaleBaseChange k).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology Y) (smallEtaleTopology X) :=
  Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)

/-- The identification of the two composite direct images around the square, for abelian
sheaves. -/
private abbrev cellAb (w : h ≫ f' = e ≫ g) :=
  compositeDirectImageCell (smallEtaleTopology S) (smallEtaleTopology T) (smallEtaleTopology X')
    (smallEtaleTopology Y) (smallEtaleBaseChange g) (smallEtaleBaseChange f')
    (smallEtaleBaseChange e) (smallEtaleBaseChange h) (fun k : Y ⟶ S ↦ smallEtaleBaseChange k)
    (smallEtaleBaseChangeComp e g).symm (smallEtaleBaseChangeComp h f').symm w.symm Ab.{u + 1}

/-- The identification of the two composite direct images around the square, for sheaves of
sets. -/
private abbrev cellSet (w : h ≫ f' = e ≫ g) :=
  compositeDirectImageCell (smallEtaleTopology S) (smallEtaleTopology T) (smallEtaleTopology X')
    (smallEtaleTopology Y) (smallEtaleBaseChange g) (smallEtaleBaseChange f')
    (smallEtaleBaseChange e) (smallEtaleBaseChange h) (fun k : Y ⟶ S ↦ smallEtaleBaseChange k)
    (smallEtaleBaseChangeComp e g).symm (smallEtaleBaseChangeComp h f').symm w.symm (Type (u + 1))

/-- The base change map of sheaves of sets is the mate of `cellSet`. -/
private theorem isIso_smallEtaleSetMate (w : h ≫ f' = e ≫ g)
    (hsets : ∀ F, IsIso ((smallEtaleSetBaseChange.{u, 0} e h g f' w.symm).app F)) :
    IsIso ((mateEquiv (smallEtaleInverseImageAdjunction.{u, 0} e)
      (smallEtaleInverseImageAdjunction.{u, 0} f')).symm (cellSet f' g h e w)).natTrans := by
  rw [show ((mateEquiv (smallEtaleInverseImageAdjunction.{u, 0} e)
      (smallEtaleInverseImageAdjunction.{u, 0} f')).symm (cellSet f' g h e w)).natTrans =
      smallEtaleSetBaseChange.{u, 0} e h g f' w.symm from rfl]
  exact NatIso.isIso_of_isIso_app _

/-- The mate of the identification of composite direct images of sheaves of sets, along the
explicit inverse images, is invertible as soon as the base change map of sheaves of sets is. -/
private theorem isIso_constructionSet (w : h ≫ f' = e ≫ g)
    (hsets : ∀ F, IsIso ((smallEtaleSetBaseChange.{u, 0} e h g f' w.symm).app F)) :
    IsIso ((mateEquiv (constructionAdjSet e) (constructionAdjSet f')).symm
      (cellSet f' g h e w)).natTrans :=
  Stacks.CategoryTheory.isIso_mateEquiv_symm_of_leftAdjointUniq (constructionAdjSet e)
    (smallEtaleInverseImageAdjunction.{u, 0} e) (constructionAdjSet f')
    (smallEtaleInverseImageAdjunction.{u, 0} f') _ (isIso_smallEtaleSetMate f' g h e w hsets)

/-- **The abelian base change map is invertible as soon as the base change map of sheaves of
sets is.** No condition is placed on the commutative square. -/
public theorem isIso_smallEtaleBaseChangeAb_of_isIso_smallEtaleSetBaseChange
    (w : h ≫ f' = e ≫ g)
    (hsets : ∀ F, IsIso ((smallEtaleSetBaseChange.{u, 0} e h g f' w.symm).app F)) :
    IsIso (smallEtaleBaseChangeAb f' g h e w) := by
  rw [show smallEtaleBaseChangeAb f' g h e w =
      ((mateEquiv (smallEtaleAdjunctionAb e) (smallEtaleAdjunctionAb f')).symm
        (cellAb f' g h e w)).natTrans from
    Stacks.Cohomology.BaseChange.mate_eq_mateEquiv_symm _ _ _ _ _]
  exact Stacks.CategoryTheory.isIso_mateEquiv_symm_of_leftAdjointUniq
    (smallEtaleAdjunctionAb e) (constructionAdjAb e) (smallEtaleAdjunctionAb f')
    (constructionAdjAb f') _
    (isIso_mateEquiv_symm_compositeDirectImageCell_of_sheafCompose
      (Φ := CategoryTheory.forget Ab.{u + 1}) _ _ _ _ _ _ _ _ _ _ _ _
      (isIso_constructionSet f' g h e w hsets))

end Bridge

section Flat

variable {X Y S T : Scheme.{u}}

/-- **Stacks Project, Tag 0EYS, for abelian sheaves.** In a cartesian square of schemes whose
left vertical morphism `f : X ⟶ S` is flat, locally of finite presentation and has
geometrically reduced fibres, the base change map `f⁻¹ g_* 𝓕 ⟶ h_* e⁻¹ 𝓕` is an isomorphism for
every abelian sheaf `𝓕` on the small étale site of `T`. The map is
`Stacks.EtaleCohomology.smallEtaleBaseChangeAb`, the underived base change map of
[Stacks, Tag 0F02]. It is invertible because the base change map of sheaves of sets is
(`Stacks.EtaleCohomology.isIso_smallEtaleSetBaseChange_of_flat_geometricallyReduced`), by
`Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isIso_smallEtaleSetBaseChange`. -/
@[stacks 0EYS "for abelian sheaves, at the comparison `smallEtaleBaseChangeAb` of \
[Stacks, Tag 0F02]; no residual hypothesis. The statement for sheaves of sets is \
`isIso_smallEtaleSetBaseChange_of_flat_geometricallyReduced`, and the abelian map is invertible \
as soon as the set-valued one is, by \
`isIso_smallEtaleBaseChangeAb_of_isIso_smallEtaleSetBaseChange`."]
public theorem isIso_smallEtaleBaseChangeAb_of_flat_geometricallyReduced (f : X ⟶ S)
    (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S) (sq : IsPullback h e f g)
    [Flat f] [LocallyOfFinitePresentation f] [GeometricallyReduced f] :
    IsIso (smallEtaleBaseChangeAb f g h e sq.w) :=
  isIso_smallEtaleBaseChangeAb_of_isIso_smallEtaleSetBaseChange f g h e sq.w fun F ↦
    isIso_smallEtaleSetBaseChange_of_flat_geometricallyReduced.{u, 0} f h e g sq F

end Flat

end Stacks.EtaleCohomology

end
