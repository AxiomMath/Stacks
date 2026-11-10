module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AppSiteClosedImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# Fibre products on the site of ind-étale affines

The objects of the small pro-étale site of a scheme `X` which are affine and have ind-étale ring
of global sections are closed under fibre products, so the site `X_app` has fibre products and
they are computed in the small pro-étale site. Base change along a morphism of affine schemes
preserves them.

The ring of global sections of a fibre product `U ×_W U'` of affine objects is the pushout of
the rings of global sections, and that pushout is ind-étale over the ring of global sections of
`X`: the structure map of `U` over `W` is ind-étale because both are ind-étale over `X`, the
pushout of an ind-étale algebra is ind-étale, and ind-étale algebras compose.

## Main results

* `CommRingCat.ind_underObj_comp` and `CommRingCat.ind_underObj_pushout_comp` — composition of
  ind-étale algebras and the ind-étaleness of the pushout of two ind-étale algebras over a
  common ind-étale one, in the under-category spelling.
* `AlgebraicGeometry.ProEtale.isAppSmall_pullback` — a fibre product of affine objects with
  ind-étale rings of global sections is again one; hence the instances
  `CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.ProEtale.AppSmallProetale X)` and
  `CategoryTheory.CreatesLimitsOfShape CategoryTheory.Limits.WalkingCospan
  (AlgebraicGeometry.ProEtale.AppSmallProetale.inclusion X)`.
* `AlgebraicGeometry.ProEtale.appProetaleBaseChange_preservesPullbacks` — base change along a
  morphism of affine schemes preserves fibre products.

## Implementation notes

The fibre product of two affine objects is identified with the spectrum of the pushout of the
rings of global sections by `AlgebraicGeometry.ProEtale.isPullback_specMap_pushout_appTop`,
which is where the affineness of the three objects is used; everything about the structure
morphism to `X` is then read off from the resulting isomorphism on global sections. The base
scheme `X` itself is not assumed affine.

Closure under fibre products is recorded as
`CategoryTheory.ObjectProperty.IsClosedUnderLimitsOfShape` for `WalkingCospan`, which supplies
both the fibre products of the subcategory and the fact that its inclusion creates them.
Preservation by base change is deduced from the equality of base change followed by the
inclusions with slice pullback after the inclusions, since slice pullback is a right adjoint and
the inclusions reflect limits.

## References

* [Stacks Project, Tag 098X](https://stacks.math.columbia.edu/tag/098X)
* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CommRingCat

/-- **Ind-étale algebras compose.** If `B` is ind-étale over `A` and `C` is ind-étale over `B`,
then `C` is ind-étale over `A`, in the spelling by object properties of under categories. -/
public theorem ind_underObj_comp {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hf : ObjectProperty.ind.{u} (CommRingCat.etale.{u}.underObj (X := A)) (Under.mk f))
    (hg : ObjectProperty.ind.{u} (CommRingCat.etale.{u}.underObj (X := B)) (Under.mk g)) :
    ObjectProperty.ind.{u} (CommRingCat.etale.{u}.underObj (X := A)) (Under.mk (f ≫ g)) := by
  let : Algebra A B := f.hom.toAlgebra
  let : Algebra B C := g.hom.toAlgebra
  let : Algebra A C := (f ≫ g).hom.toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  exact (@AlgebraicGeometry.ProEtale.indEtale_iff_ind_underObj A C _ _ _).mp
    (StacksDraft.indEtale_comp
      ((@AlgebraicGeometry.ProEtale.indEtale_iff_ind_underObj A B _ _ _).mpr hf)
      ((@AlgebraicGeometry.ProEtale.indEtale_iff_ind_underObj B C _ _ _).mpr hg))

/-- **The pushout of two ind-étale algebras over a common ind-étale one is ind-étale.** Let
`A → D` be ind-étale and let `D → C` and `D → C'` be maps whose composites with `A → D` are
ind-étale. Then the pushout of `C` and `C'` over `D` is ind-étale over `A`. -/
public theorem ind_underObj_pushout_comp {A D C C' : CommRingCat.{u}} (α : A ⟶ D) (p : D ⟶ C)
    (q : D ⟶ C')
    (hD : ObjectProperty.ind.{u} (CommRingCat.etale.{u}.underObj (X := A)) (Under.mk α))
    (hC : ObjectProperty.ind.{u} (CommRingCat.etale.{u}.underObj (X := A)) (Under.mk (α ≫ p)))
    (hC' : ObjectProperty.ind.{u} (CommRingCat.etale.{u}.underObj (X := A)) (Under.mk (α ≫ q))) :
    ObjectProperty.ind.{u} (CommRingCat.etale.{u}.underObj (X := A))
      (Under.mk (α ≫ q ≫ pushout.inr p q)) := by
  have h1 : ObjectProperty.ind.{u} (CommRingCat.etale.{u}.underObj (X := D)) (Under.mk p) :=
    CommRingCat.ind_etale_of_comp α p hD hC
  have h2 : ObjectProperty.ind.{u} (CommRingCat.etale.{u}.underObj (X := C'))
      (Under.mk (pushout.inr p q)) :=
    MorphismProperty.ind_underObj_pushout q h1
  rw [← Category.assoc]
  exact ind_underObj_comp _ _ hC' h2

end CommRingCat

namespace AlgebraicGeometry.ProEtale

/-- A fibre product of affine schemes over an affine scheme is affine, and its ring of global
sections is the pushout of the rings of global sections compatibly with the structure morphism
to an ambient scheme `X`. -/
private theorem isAffine_and_exists_iso_pushout_appTop {X SU SU' SW L : Scheme.{u}}
    [IsAffine SU] [IsAffine SU'] [IsAffine SW] (sW : SW ⟶ X) (sU' : SU' ⟶ X) (a : SU ⟶ SW)
    (b : SU' ⟶ SW) (hb : b ≫ sW = sU') (hL : L ⟶ X) (π : L ⟶ SU) (ρ : L ⟶ SU')
    (hpb : IsPullback π ρ a b) (hρ : ρ ≫ sU' = hL) :
    IsAffine L ∧ ∃ ε : (pushout a.appTop b.appTop : CommRingCat.{u}) ≅ Γ(L, ⊤),
      (sU'.appTop ≫ pushout.inr a.appTop b.appTop) ≫ ε.hom = hL.appTop := by
  subst hb
  have h2 := isPullback_specMap_pushout_appTop b a
  let e : Spec (pushout a.appTop b.appTop) ≅ L := h2.isoPullback ≪≫ hpb.isoPullback.symm
  have hcomp : e.hom ≫ hL =
      Spec.map (pushout.inr a.appTop b.appTop) ≫ SU'.isoSpec.inv ≫ b ≫ sW := by
    rw [← hρ]
    change (h2.isoPullback.hom ≫ hpb.isoPullback.inv) ≫ ρ ≫ b ≫ sW = _
    rw [Category.assoc, ← Category.assoc hpb.isoPullback.inv ρ, hpb.isoPullback_inv_snd,
      ← Category.assoc, h2.isoPullback_hom_snd, Category.assoc]
  have key : hL.appTop ≫ e.hom.appTop =
      (b ≫ sW).appTop ≫ pushout.inr a.appTop b.appTop ≫ (Scheme.ΓSpecIso _).inv := by
    rw [← Scheme.Hom.comp_appTop, hcomp, Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
      Stacks.RelativeSpec.isoSpec_inv_appTop, Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality]
  refine ⟨IsAffine.of_isIso e.inv, ⟨{ hom := (Scheme.ΓSpecIso _).inv ≫ e.inv.appTop
                                      inv := e.hom.appTop ≫ (Scheme.ΓSpecIso _).hom
                                      hom_inv_id := ?_
                                      inv_hom_id := ?_ }, ?_⟩⟩
  · rw [Category.assoc, ← Category.assoc e.inv.appTop, ← Scheme.Hom.comp_appTop, e.hom_inv_id]
    simp
  · rw [Category.assoc, ← Category.assoc _ _ e.inv.appTop, (Scheme.ΓSpecIso _).hom_inv_id,
      Category.id_comp, ← Scheme.Hom.comp_appTop, e.inv_hom_id]
    rfl
  · change ((b ≫ sW).appTop ≫ pushout.inr a.appTop b.appTop) ≫
      (Scheme.ΓSpecIso _).inv ≫ e.inv.appTop = hL.appTop
    rw [Category.assoc, ← Category.assoc (pushout.inr a.appTop b.appTop), ← Category.assoc,
      ← key, Category.assoc, ← Scheme.Hom.comp_appTop, e.inv_hom_id]
    simp

/-- **Fibre products of ind-étale affine objects.** A fibre product, taken in the small
pro-étale site of `X`, of two objects which are affine with ind-étale ring of global sections
over an object of the same kind is again affine with ind-étale ring of global sections. -/
public theorem isAppSmall_pullback {X : Scheme.{u}} {U U' W : X.ProEt} (f : U ⟶ W) (g : U' ⟶ W)
    (hU : IsAppSmall X U) (hU' : IsAppSmall X U') (hW : IsAppSmall X W) :
    IsAppSmall X (pullback f g) := by
  have iU : IsAffine U.left := hU.1
  have iU' : IsAffine U'.left := hU'.1
  have iW : IsAffine W.left := hW.1
  have jU : IsAffine ((𝟭 Scheme.{u}).obj U.left) := hU.1
  have jU' : IsAffine ((𝟭 Scheme.{u}).obj U'.left) := hU'.1
  have jW : IsAffine ((𝟭 Scheme.{u}).obj W.left) := hW.1
  have hind : ∀ {V : X.ProEt} (h : V ⟶ W), IsAppSmall X V →
      ObjectProperty.ind.{u} (CommRingCat.etale.{u}.underObj (X := Γ(X, ⊤)))
        (Under.mk (W.hom.appTop ≫ h.left.appTop)) := fun {V} h hV ↦ by
    rw [← Scheme.Hom.comp_appTop, MorphismProperty.Over.w h]
    exact (@indEtale_iff_ind_underObj _ _ _ _ V.hom.appTop.hom.toAlgebra).mp hV.2
  have hpb : IsPullback (pullback.fst f g).left (pullback.snd f g).left f.left g.left :=
    (IsPullback.of_hasPullback f g).map (Scheme.ProEt.forget X ⋙ Over.forget X)
  obtain ⟨haff, ε, hε⟩ := isAffine_and_exists_iso_pushout_appTop W.hom U'.hom f.left g.left
    (MorphismProperty.Over.w g) (pullback f g).hom _ _ hpb
    (MorphismProperty.Over.w (pullback.snd f g))
  have hwi : ObjectProperty.ind.{u} (CommRingCat.etale.{u}.underObj (X := Γ(X, ⊤)))
      (Under.mk W.hom.appTop) :=
    (@indEtale_iff_ind_underObj _ _ _ _ W.hom.appTop.hom.toAlgebra).mp hW.2
  have hP : ObjectProperty.ind.{u} (CommRingCat.etale.{u}.underObj (X := Γ(X, ⊤)))
      (Under.mk (U'.hom.appTop ≫ pushout.inr f.left.appTop g.left.appTop)) := by
    rw [← MorphismProperty.Over.w g, Scheme.Hom.comp_appTop, Category.assoc]
    exact CommRingCat.ind_underObj_pushout_comp W.hom.appTop f.left.appTop g.left.appTop
      hwi (hind f hU) (hind g hU')
  refine ⟨haff, ?_⟩
  let : Algebra Γ(X, ⊤) (pushout f.left.appTop g.left.appTop :) :=
    (U'.hom.appTop ≫ pushout.inr f.left.appTop g.left.appTop).hom.toAlgebra
  let : Algebra Γ(X, ⊤) Γ((pullback f g).left, ⊤) := (pullback f g).hom.appTop.hom.toAlgebra
  have hind : StacksDraft.IndEtale Γ(X, ⊤) (pushout f.left.appTop g.left.appTop :) :=
    (@indEtale_iff_ind_underObj _ _ _ _ _).mpr hP
  refine StacksDraft.indEtale_of_equiv (RingEquiv.refl Γ(X, ⊤))
    ε.commRingCatIsoToRingEquiv (fun a ↦ ?_) hind
  exact congrArg (fun φ : Γ(X, ⊤) ⟶ _ ↦ φ.hom a) hε

/-- The objects of the small pro-étale site of `X` which are affine with ind-étale ring of
global sections are closed under fibre products. -/
instance isClosedUnderLimitsOfShape_walkingCospan (X : Scheme.{u}) :
    (IsAppSmall X).IsClosedUnderLimitsOfShape WalkingCospan :=
  .mk' (by
    rintro _ ⟨F, hF⟩
    exact (IsAppSmall X).prop_of_iso (HasLimit.isoOfNatIso (diagramIsoCospan F)).symm
      (isAppSmall_pullback (F.map WalkingCospan.Hom.inl) (F.map WalkingCospan.Hom.inr)
        (hF _) (hF _) (hF _)))

/-- **Stacks 09BK, continuity of the base change functor: fibre products.** For a morphism
`i : Z ⟶ X` of affine schemes the functor `U ↦ U ×_X Z` from `X_app` to `Z_app` preserves fibre
products, which is the second half of continuity in the sense of the Stacks Project. -/
@[stacks 09BK "the base change functor is continuous"]
public noncomputable instance appProetaleBaseChange_preservesPullbacks {X Z : Scheme.{u}}
    [IsAffine X] [IsAffine Z] (i : Z ⟶ X) :
    PreservesLimitsOfShape WalkingCospan (appProetaleBaseChange i) where
  preservesLimit {K} := by
    have h : PreservesLimit K (appProetaleBaseChange i ⋙
        (AppSmallProetale.inclusion Z ⋙ Scheme.ProEt.forget Z)) := by
      rw [show appProetaleBaseChange i ⋙ (AppSmallProetale.inclusion Z ⋙ Scheme.ProEt.forget Z) =
        (AppSmallProetale.inclusion X ⋙ Scheme.ProEt.forget X) ⋙ Over.pullback i from rfl]
      infer_instance
    exact preservesLimit_of_reflects_of_preserves _
      (AppSmallProetale.inclusion Z ⋙ Scheme.ProEt.forget Z)

end AlgebraicGeometry.ProEtale

end
