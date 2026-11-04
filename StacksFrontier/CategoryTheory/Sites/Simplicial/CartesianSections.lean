module

public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Cartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialSemiRepresentableSite

/-!
# Cartesian sheaves on the total site of a simplicial semi-representable object, on sections

Let `(C, J)` be a site and let `K` be a simplicial object of `SR(C)`. A sheaf on the total site
of `C/K` is cartesian when every canonical transition `f_φ⁻¹ Fₘ ⟶ Fₙ` is an isomorphism of
sheaves on the component site. This file reads that condition on *sections*: it says that
restriction along every cross-fibre arrow of the total category is bijective.

The two readings are not the same statement a priori: the inverse image `f_φ⁻¹` of the morphism
of topoi of a cocontinuous functor is the *sheafified* restriction, so the transition being
invertible says only that the restriction map on sections is a local isomorphism. They do agree
here because the transition functor `C/K_n ⥤ C/K_m` is continuous as well as cocontinuous, by
Stacks 0D85, so that no sheafification occurs.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable.componentOverMap_isContinuous''`: the transition
  functor of a simplex map is continuous for the component topologies, by Stacks 0D85.
* `CategoryTheory.CocontinuousSimplicialSite.isIso_map_ιNatTrans_of_isIso_fiberTransition`: in
  case (B) of a simplicial-site situation whose transition functor is continuous, an invertible
  transition of Stacks 09WF means that restriction along the cross-fibre arrows is bijective on
  sections.
* `CategoryTheory.SimplicialSemiRepresentable.isIso_map_ιNatTrans_of_isCartesianSheaf`:
  restriction along a cross-fibre arrow of the total category is bijective on the sections of a
  cartesian sheaf.

## Implementation notes

The comparison of the two adjunctions with the same right adjoint `f_{φ*}` — the one of the
morphism of topoi, whose left adjoint is the sheafified restriction, and
`CategoryTheory.Functor.sheafAdjunctionCocontinuous`, whose left adjoint is plain restriction —
is `CategoryTheory.Adjunction.leftAdjointUniq`, and
`CategoryTheory.Adjunction.leftAdjointUniq_hom_app_comp_homEquiv_symm''` says that transposing
along one of them is transposing along the other up to that isomorphism. The transpose along
`sheafAdjunctionCocontinuous` is the transpose along the Kan-extension adjunction of presheaves,
which `CategoryTheory.SimplicialSiteSituation.restrictTransition_inr_app` computes to be exactly
restriction along the cross-fibre arrow.

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
* [Stacks Project, Tag 0D85](https://stacks.math.columbia.edu/tag/0D85)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory

namespace CocontinuousSimplicialSite

open SimplicialSiteSituation

/-- **Stacks 09WF read on sections, in case (B).** If the transition functor of a simplex map is
continuous as well as cocontinuous, then the transition between the restrictions of a total-site
sheaf is invertible exactly when restriction along the cross-fibre arrows of the total category
is bijective. This is the direction that is used. -/
theorem isIso_map_ιNatTrans_of_isIso_fiberTransition (D : CocontinuousSimplicialSite.{u})
    {m n : SimplexCategory} (φ : m ⟶ n)
    [((D.underlying.map φ.op).toFunctor).IsContinuous
      ((⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      ((⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}).componentTopology m)]
    (F : Sheaf (⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}).totalTopology (Type u))
    (hF : IsIso ((fiberTransition (⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}) φ).app F))
    (U : D.underlying.obj (op n)) :
    IsIso (F.obj.map ((Grothendieck.ιNatTrans (F := D.underlying) φ.op).app U).op) := by
  let : ((D.underlying.map φ.op).toFunctor).IsCocontinuous
      ((⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      ((⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}).componentTopology m) := D.isCocontinuous φ.op
  set adj₂ := ((D.underlying.map φ.op).toFunctor).sheafAdjunctionCocontinuous (Type u)
    ((⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}).componentTopology n)
    ((⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}).componentTopology m) with hadj₂
  have h₂ : IsIso ((adj₂.homEquiv _ _).symm
      ((restrictTransition (⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}) φ).app F)) :=
    (Adjunction.isIso_homEquiv_symm_iff
      ((⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}).transitionMorphism φ).adj adj₂ _).1 hF
  have h₄ : ((adj₂.homEquiv _ _).symm
        ((restrictTransition (⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}) φ).app F)).hom =
      ((((D.underlying.map φ.op).toFunctor).op.ranAdjunction (Type u)).homEquiv _ _).symm
        ((restrictTransition (⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}) φ).app F).hom := by
    refine (Equiv.eq_symm_apply _).2 ?_
    refine (Functor.sheafAdjunctionCocontinuous_homEquiv_apply_hom _ _ _ _ _).symm.trans ?_
    exact Sheaf.hom_ext_iff.1 ((adj₂.homEquiv _ _).apply_symm_apply _)
  obtain ⟨g, hg₁, hg₂⟩ := h₂.out
  have h₅ : IsIso ((((adj₂.homEquiv _ _).symm
      ((restrictTransition (⟨Sum.inr D⟩ : SimplicialSiteSituation.{u}) φ).app F)).hom).app
      (op U)) :=
    ⟨⟨g.hom.app (op U), congrArg (fun z ↦ z.app (op U)) (Sheaf.hom_ext_iff.1 hg₁),
      congrArg (fun z ↦ z.app (op U)) (Sheaf.hom_ext_iff.1 hg₂)⟩⟩
  have h₆ := (congrArg (fun z ↦ z.app (op U)) h₄).trans
    (restrictTransition_inr_app D φ F U)
  rwa [h₆] at h₅

end CocontinuousSimplicialSite

namespace SimplicialSemiRepresentable

open SemiRepresentable SimplicialSiteSituation

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (K : SimplicialObject (FormalCoproduct.{u} C))

/-- **Stacks 0D85.** The transition functor of a simplex map is continuous for the topologies
generated by the covering families of the two degrees. -/
instance componentOverMap_isContinuous'' {m n : SimplexCategoryᵒᵖ} (φ : m ⟶ n) :
    (componentOverMap (K.map φ)).IsContinuous (topologyOfCoverings (sliceCoverings J K m))
      (topologyOfCoverings (sliceCoverings J K n)) := by
  rw [topologyOfCoverings_sliceCoverings, topologyOfCoverings_sliceCoverings]
  exact LocalizationSites.relocalizationFunctor_isContinuous (transitionSites J K φ)

/-- The componentwise localization functor reflects isomorphisms: a morphism of `C/L` is
invertible as soon as the morphism of `C` underlying it is. -/
instance componentOverForget_reflectsIsomorphisms (L : FormalCoproduct.{u} C) :
    (componentOverForget L).ReflectsIsomorphisms where
  reflects {A B} f hf := by
    cases f with
    | @mk i A B g =>
      have : IsIso ((Over.forget (L.obj i)).map g) := hf
      have : IsIso g := isIso_of_reflects_iso g (Over.forget (L.obj i))
      exact Functor.map_isIso
        (CategoryTheory.Sigma.incl (C := fun j : L.I ↦ Over (L.obj j)) i) g

/-- The image in `C` of a morphism of the total category is the image of its fibre component
under the localization functor of the target degree. -/
theorem totalForget_map {X Y : Grothendieck (slices K)} (ψ : X ⟶ Y) :
    (totalForget K).map ψ = (sliceForget K Y.base).map ψ.fiber := by
  have hmap : (totalForget K).map ψ =
      (eqToHom (totalForget_fib_eq K ψ.base)).app X.fiber ≫
        (sliceForget K Y.base).map ψ.fiber := rfl
  have h1 : (eqToHom (totalForget_fib_eq K ψ.base)).app X.fiber = 𝟙 _ :=
    (eqToHom_app _ _).trans (eqToHom_refl _ _)
  exact hmap.trans
    ((congrArg (fun z ↦ z ≫ (sliceForget K Y.base).map ψ.fiber) h1).trans (Category.id_comp _))

/-- A morphism of the total category whose image in `C` is invertible has invertible fibre
component. -/
theorem isIso_fiber_of_isIso_totalForget_map {X Y : Grothendieck (slices K)} (ψ : X ⟶ Y)
    (h : IsIso ((totalForget K).map ψ)) : IsIso ψ.fiber := by
  rw [totalForget_map] at h
  have : IsIso ((componentOverForget (K.obj Y.base)).map ψ.fiber) := h
  exact (componentOverForget_reflectsIsomorphisms (K.obj Y.base)).reflects ψ.fiber

variable [J.toCoverage.HasPullbacks]

/-- The transition functor of a simplex map is continuous for the component topologies of the
simplicial site of a simplicial semi-representable object. -/
instance componentOverMap_isContinuous' {m n : SimplexCategory} (φ : m ⟶ n) :
    (componentOverMap (K.map φ.op)).IsContinuous ((situation J K).componentTopology n)
      ((situation J K).componentTopology m) :=
  componentOverMap_isContinuous'' J K φ.op

/-- **Cartesianness, read on sections.** For a cartesian sheaf on the total site, restriction
along a cross-fibre arrow of the total category is a bijection. -/
theorem isIso_map_ιNatTrans_of_isCartesianSheaf
    (F : Sheaf (situation J K).totalTopology (Type u))
    (hF : (situation J K).IsCartesianSheaf F) {m n : SimplexCategory} (φ : m ⟶ n)
    (U : ComponentOver (K.obj (op n))) :
    IsIso (F.obj.map ((Grothendieck.ιNatTrans (F := slices K) φ.op).app U).op) := by
  let : (((simplicialSite J K).underlying.map φ.op).toFunctor).IsContinuous
      ((⟨Sum.inr (simplicialSite J K)⟩ : SimplicialSiteSituation.{u}).componentTopology n)
      ((⟨Sum.inr (simplicialSite J K)⟩ : SimplicialSiteSituation.{u}).componentTopology m) :=
    componentOverMap_isContinuous' J K φ
  exact CocontinuousSimplicialSite.isIso_map_ιNatTrans_of_isIso_fiberTransition
    (simplicialSite J K) φ F (hF φ) U

/-- **Cartesianness, read on sections, for an arbitrary arrow.** For a cartesian sheaf on the
total site, restriction along an arrow of the total category whose image in `C` is invertible is
a bijection. -/
theorem isIso_map_of_isIso_totalForget_map
    (F : Sheaf (situation J K).totalTopology (Type u))
    (hF : (situation J K).IsCartesianSheaf F) {X Y : Grothendieck (slices K)} (ψ : X ⟶ Y)
    (h : IsIso ((totalForget K).map ψ)) : IsIso (F.obj.map ψ.op) := by
  have : IsIso ψ.fiber := isIso_fiber_of_isIso_totalForget_map K ψ h
  have h₂ : IsIso (F.obj.map ((Grothendieck.ιNatTrans (F := slices K) ψ.base).app X.fiber).op) :=
    isIso_map_ιNatTrans_of_isCartesianSheaf J K F hF ψ.base.unop X.fiber
  have hdecomp : ψ = (Grothendieck.ιNatTrans (F := slices K) ψ.base).app X.fiber ≫
      (Grothendieck.ι (slices K) Y.base).map ψ.fiber :=
    (Grothendieck.ιNatTrans_app_comp_ι_map ψ.base ψ.fiber).symm
  have key : F.obj.map ψ.op =
      F.obj.map ((Grothendieck.ι (slices K) Y.base).map ψ.fiber).op ≫
        F.obj.map ((Grothendieck.ιNatTrans (F := slices K) ψ.base).app X.fiber).op :=
    (congrArg (fun z ↦ F.obj.map (Quiver.Hom.op z)) hdecomp).trans (F.obj.map_comp _ _)
  have h₃ : IsIso ((Grothendieck.ι (slices K) Y.base).map ψ.fiber) := inferInstance
  have h₄ : IsIso (((Grothendieck.ι (slices K) Y.base).map ψ.fiber).op) := inferInstance
  have h₅ : IsIso (F.obj.map ((Grothendieck.ι (slices K) Y.base).map ψ.fiber).op) :=
    @Functor.map_isIso _ _ _ _ _ _ F.obj _ h₄
  rw [key]
  exact IsIso.comp_isIso' h₅ h₂

end SimplicialSemiRepresentable

end CategoryTheory

end
