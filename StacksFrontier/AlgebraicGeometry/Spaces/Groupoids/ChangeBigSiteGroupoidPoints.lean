module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.ChangeBigSiteSections
public import StacksFrontier.Deformation.Groupoid.Restriction

/-!
# The groupoid of points is unchanged by enlarging the big fppf site

Let `B` be a big fppf site contained in a larger one `B'`, let `S` be a scheme of `B`, let `G`
be a groupoid in algebraic spaces over an algebraic space over `S` for `B`, and let `f` be the
morphism of sites determined by the localized inclusion `i`. The inverse image
`(f⁻¹U, f⁻¹R, f⁻¹s, f⁻¹t, f⁻¹c)` of `G` has, at a test object `i T` coming from the smaller
site, the same groupoid of points as `G` has at `T`: the transport of sections identifies
`U(T)` with `(f⁻¹U)(i T)` and `R(T)` with `(f⁻¹R)(i T)`, compatibly with source, target and
composition.

Compatibility with composition is the only point requiring an argument. The composition of the
inverse-image groupoid is the inverse image of the composition read through the comparison of
the two chosen fibre products, so the claim is that this comparison agrees with the transport
of sections; both sides are sections of the inverse image of a fibre product, which stays
cartesian, so they are compared on the two projections.

## Main definitions

* `AlgebraicGeometry.changeBigSiteGroupoidHom`: the morphism of groupoids in presheaves from
  `G` to the restriction of its inverse image along the localized inclusion.

## Main results

* `AlgebraicGeometry.changeBigSiteCompComparison_app_composable`: the comparison of the two
  chosen fibre products agrees with the transport of sections.
* `AlgebraicGeometry.changeBigSiteGroupoidHom_compose`: the transport of sections carries the
  composition of `G` at `T` to the composition of its inverse image at `i T`.

## References

* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044P](https://stacks.math.columbia.edu/tag/044P)
* [Stacks Project, Tag 04W1](https://stacks.math.columbia.edu/tag/04W1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Deformation

namespace AlgebraicGeometry

universe u

/-- The Yoneda transpose of the image of a section under a morphism of presheaves is the
transpose of the section followed by that morphism. -/
private theorem yonedaEquiv_symm_app {C : BigFppfSite.{u}} {S₀ : Scheme.{u}}
    {hS₀ : C.Contains S₀} {F H : (BigFppfOver C S₀ hS₀)ᵒᵖ ⥤ Type u} (α : F ⟶ H)
    {T : BigFppfOver C S₀ hS₀} (x : F.obj (op T)) :
    yonedaEquiv.symm (α.app (op T) x) = yonedaEquiv.symm x ≫ α := by
  apply yonedaEquiv.injective
  rw [Equiv.apply_symm_apply, yonedaEquiv_comp, Equiv.apply_symm_apply]

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) {Bs : AlgebraicSpaces B S hS}
  (G : GroupoidInAlgebraicSpaces B S hS Bs)

/-- **The comparison of the two chosen fibre products agrees with the transport of sections.**
A composable pair of sections of the arrow space at `T` and its transport to `i T` present the
same section of the inverse image of the chosen fibre product of the source and target maps. -/
theorem changeBigSiteCompComparison_app_composable (T : BigFppfOver B S hS)
    (p : (Deformation.composableArrows G.objects.obj G.arrows.obj
      G.source.hom G.target.hom).obj (op T))
    (p' : (Deformation.composableArrows
      ((changeBigSite B B' h S hS).obj G.objects).obj
      ((changeBigSite B B' h S hS).obj G.arrows).obj
      ((changeBigSite B B' h S hS).map G.source).hom
      ((changeBigSite B B' h S hS).map G.target).hom).obj
      (op ((inclusionOver h S hS).obj T)))
    (hfst : p'.1.1 = changeBigSiteSectionEquiv B B' h S hS G.arrows T p.1.1)
    (hsnd : p'.1.2 = changeBigSiteSectionEquiv B B' h S hS G.arrows T p.1.2) :
    (changeBigSiteCompComparison B B' h S hS G).hom.app
        (op ((inclusionOver h S hS).obj T))
        ((composableToPullback ((changeBigSite B B' h S hS).map G.source).hom
          ((changeBigSite B B' h S hS).map G.target).hom).app _ p') =
      changeBigSiteSectionEquiv B B' h S hS
        (AlgebraicSpaces.fiberProduct B S hS G.source G.target) T
        ((composableToPullback G.source.hom G.target.hom).app (op T) p) := by
  have hpb := isPullback_hom_map_fibreProduct_changeBigSite B B' h S hS G.source G.target
  have key : ∀ (π : AlgebraicSpaces.fiberProduct B S hS G.source G.target ⟶ G.arrows)
      (π' : AlgebraicSpaces.fiberProduct B' S (largerContains h hS)
        ((changeBigSite B B' h S hS).map G.source)
        ((changeBigSite B B' h S hS).map G.target) ⟶
        (changeBigSite B B' h S hS).obj G.arrows),
      changeBigSiteCompComparison B B' h S hS G ≫
          (changeBigSite B B' h S hS).map π = π' →
      ∀ (c : (Deformation.composableArrows G.objects.obj G.arrows.obj
        G.source.hom G.target.hom) ⟶ G.arrows.obj),
      composableToPullback G.source.hom G.target.hom ≫ π.hom = c →
      ∀ (c' : (Deformation.composableArrows
        ((changeBigSite B B' h S hS).obj G.objects).obj
        ((changeBigSite B B' h S hS).obj G.arrows).obj
        ((changeBigSite B B' h S hS).map G.source).hom
        ((changeBigSite B B' h S hS).map G.target).hom) ⟶
        ((changeBigSite B B' h S hS).obj G.arrows).obj),
      composableToPullback ((changeBigSite B B' h S hS).map G.source).hom
        ((changeBigSite B B' h S hS).map G.target).hom ≫ π'.hom = c' →
      c'.app (op ((inclusionOver h S hS).obj T)) p' =
        changeBigSiteSectionEquiv B B' h S hS G.arrows T (c.app (op T) p) →
      ((changeBigSite B B' h S hS).map π).hom.app (op ((inclusionOver h S hS).obj T))
          ((changeBigSiteCompComparison B B' h S hS G).hom.app _
            ((composableToPullback ((changeBigSite B B' h S hS).map G.source).hom
              ((changeBigSite B B' h S hS).map G.target).hom).app _ p')) =
        ((changeBigSite B B' h S hS).map π).hom.app (op ((inclusionOver h S hS).obj T))
          (changeBigSiteSectionEquiv B B' h S hS
            (AlgebraicSpaces.fiberProduct B S hS G.source G.target) T
            ((composableToPullback G.source.hom G.target.hom).app (op T) p)) := by
    intro π π' hcomm c hc c' hc' hpp
    have hL : ((changeBigSite B B' h S hS).map π).hom.app
          (op ((inclusionOver h S hS).obj T))
          ((changeBigSiteCompComparison B B' h S hS G).hom.app _
            ((composableToPullback ((changeBigSite B B' h S hS).map G.source).hom
              ((changeBigSite B B' h S hS).map G.target).hom).app _ p')) =
        c'.app (op ((inclusionOver h S hS).obj T)) p' := by
      subst hc'
      exact natTrans_app_congr (congrArg (fun k => k.hom) hcomm) _ _
    have hR : ((changeBigSite B B' h S hS).map π).hom.app
          (op ((inclusionOver h S hS).obj T))
          (changeBigSiteSectionEquiv B B' h S hS
            (AlgebraicSpaces.fiberProduct B S hS G.source G.target) T
            ((composableToPullback G.source.hom G.target.hom).app (op T) p)) =
        changeBigSiteSectionEquiv B B' h S hS G.arrows T (c.app (op T) p) := by
      subst hc
      exact (changeBigSiteSectionEquiv_map B B' h S hS π T _).symm
    rw [hL, hR, hpp]
  refine yonedaEquiv.symm.injective (hpb.hom_ext ?_ ?_)
  · exact (yonedaEquiv_symm_app _ _).symm.trans
      ((congrArg yonedaEquiv.symm
        (key _ _ (changeBigSiteCompComparison_comp_fst B B' h S hS G)
          (composableFst _ _) (composableToPullback_comp_pullbackFst _ _)
          (composableFst _ _) (composableToPullback_comp_pullbackFst _ _) hfst)).trans
        (yonedaEquiv_symm_app _ _))
  · exact (yonedaEquiv_symm_app _ _).symm.trans
      ((congrArg yonedaEquiv.symm
        (key _ _ (changeBigSiteCompComparison_comp_snd B B' h S hS G)
          (composableSnd _ _) (composableToPullback_comp_pullbackSnd _ _)
          (composableSnd _ _) (composableToPullback_comp_pullbackSnd _ _) hsnd)).trans
        (yonedaEquiv_symm_app _ _))

/-- The transport of sections carries the source of `G` at `T` to the source of its inverse
image at `i T`. -/
theorem changeBigSiteGroupoidHom_source (T : (BigFppfOver B S hS)ᵒᵖ)
    (a : G.toGroupoidInFunctors.arrows.obj T) :
    ((changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors.restrict
          (inclusionOver h S hS).op).source.app T
        (changeBigSiteSectionEquiv B B' h S hS G.arrows T.unop a) =
      changeBigSiteSectionEquiv B B' h S hS G.objects T.unop
        (G.toGroupoidInFunctors.source.app T a) :=
  (changeBigSiteSectionEquiv_map B B' h S hS G.source T.unop a).symm

/-- The transport of sections carries the target of `G` at `T` to the target of its inverse
image at `i T`. -/
theorem changeBigSiteGroupoidHom_target (T : (BigFppfOver B S hS)ᵒᵖ)
    (a : G.toGroupoidInFunctors.arrows.obj T) :
    ((changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors.restrict
          (inclusionOver h S hS).op).target.app T
        (changeBigSiteSectionEquiv B B' h S hS G.arrows T.unop a) =
      changeBigSiteSectionEquiv B B' h S hS G.objects T.unop
        (G.toGroupoidInFunctors.target.app T a) :=
  (changeBigSiteSectionEquiv_map B B' h S hS G.target T.unop a).symm

/-- **The transport of sections carries the composition of `G` at `T` to the composition of its
inverse image at `i T`.** -/
theorem changeBigSiteGroupoidHom_compose (T : (BigFppfOver B S hS)ᵒᵖ)
    (a b : G.toGroupoidInFunctors.arrows.obj T)
    (hab : G.toGroupoidInFunctors.source.app T a = G.toGroupoidInFunctors.target.app T b) :
    ((changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors.restrict
        (inclusionOver h S hS).op).compose T
      (changeBigSiteSectionEquiv B B' h S hS G.arrows T.unop a)
      (changeBigSiteSectionEquiv B B' h S hS G.arrows T.unop b)
      ((changeBigSiteGroupoidHom_source B B' h S hS G T a).trans
        ((congrArg (changeBigSiteSectionEquiv B B' h S hS G.objects T.unop) hab).trans
          (changeBigSiteGroupoidHom_target B B' h S hS G T b).symm)) =
      changeBigSiteSectionEquiv B B' h S hS G.arrows T.unop
        (G.toGroupoidInFunctors.compose T a b hab) := by
  have hc := changeBigSiteCompComparison_app_composable B B' h S hS G T.unop ⟨(a, b), hab⟩
    ⟨(changeBigSiteSectionEquiv B B' h S hS G.arrows T.unop a,
      changeBigSiteSectionEquiv B B' h S hS G.arrows T.unop b),
      ((changeBigSiteGroupoidHom_source B B' h S hS G T a).trans
        ((congrArg (changeBigSiteSectionEquiv B B' h S hS G.objects T.unop) hab).trans
          (changeBigSiteGroupoidHom_target B B' h S hS G T b).symm))⟩ rfl rfl
  exact (congrArg (((changeBigSite B B' h S hS).map G.comp).hom.app
      (op ((inclusionOver h S hS).obj T.unop))) hc).trans
    ((changeBigSiteSectionEquiv_map B B' h S hS G.comp T.unop _).symm)

/-- **The groupoid of points is unchanged by enlarging the big fppf site.** The transport of
sections is a morphism from the groupoid in presheaves of `G` to the restriction along the
localized inclusion of the groupoid in presheaves of the inverse image of `G`. -/
def changeBigSiteGroupoidHom :
    GroupoidInFunctors.Hom G.toGroupoidInFunctors
      ((changeBigSiteGroupoid B B' h S hS G).toGroupoidInFunctors.restrict
        (inclusionOver h S hS).op) where
  mapObjects := (changeBigSitePresheafIso B B' h S hS G.objects).hom
  mapArrows := (changeBigSitePresheafIso B B' h S hS G.arrows).hom
  map_source := changeBigSiteGroupoidHom_source B B' h S hS G
  map_target := changeBigSiteGroupoidHom_target B B' h S hS G
  map_comp := changeBigSiteGroupoidHom_compose B B' h S hS G
  map_id := Space.mapIdentityOfMapComp _ _
    (changeBigSiteGroupoidHom_source B B' h S hS G)
    (changeBigSiteGroupoidHom_target B B' h S hS G)
    (changeBigSiteGroupoidHom_compose B B' h S hS G)

end AlgebraicGeometry

end
