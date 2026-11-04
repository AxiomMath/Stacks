module

public import StacksFrontier.AlgebraicGeometry.Spaces.BeauvilleLaszloGlueingAffineFull

/-!
# The glueing triple of the spectrum of a glued algebra (Stacks 0F9Q)

Fix a Beauville--Laszlo glueing pair, write `X = Spec R`, `U = Spec R_f`, `X' = Spec R'` and
`U' = Spec R'_f`, and let `G` be a glueing functor of Stacks 0F9N for the resulting square. The
essential surjectivity half of Stacks 0F9Q produces, from a cartesian glueing triple `Z` with
affine components, an affine `R`-algebra `A` glued out of the two outer components, and then has
to see that the triple of `Spec A` is `Z`. This module proves that last step: for an `R`-algebra
`A` whose two base changes are the two outer components of `Z`, compatibly with the glueing
isomorphism of `Z`, the triple `G.functor.obj (Spec A)` is isomorphic to `Z`.

## Main results

* `BeauvilleLaszlo.Space.nonempty_glueingDataIso`: **the triple of the glued algebra is the given
  triple.** Its input is exactly what the Beauville--Laszlo theorem for algebras
  (`BeauvilleLaszlo.exists_glued_of_cartesianDatum`) returns: two pushout squares exhibiting
  `A₁` and `A'` as the base changes of `A`, and the compatibility of the glued algebra with the
  glueing isomorphism of `Z` read as an isomorphism of `R'_f`-algebras.

## Implementation notes

The glueing isomorphism of `Z` is transported to an isomorphism
`BeauvilleLaszlo.Space.glueingPsi` of `R'_f`-algebras between the two base changes of the outer
components, and `BeauvilleLaszlo.Space.heartEq` is the compatibility of the two outer
identifications with the two glueing isomorphisms that
`BeauvilleLaszlo.Space.glueingDataIsoMk_of_compare` asks for. Both sides of that compatibility
are morphisms out of a representable algebraic space, so
`BeauvilleLaszlo.Space.hom_ext_of_section_comp` reduces it to an equality of tautological
points, and `BeauvilleLaszlo.Space.twoStepBaseChangeIso_inv_app_id_left` computes both of
them: neither side is ever transported across the two routes `U' → U → X` and `U' → X' → X` of
the square, which is what keeps the comparison away from the associativity of composition in the
site.

The comparison of the two iterated base changes is the cast along the equality of objects that
the commutativity of the square provides, but the equality is never named: it is introduced by
`obtain` in `BeauvilleLaszlo.Space.exists_cast_of_square`, so that every statement which
mentions the comparison mentions an opaque morphism. A cast along a named equality of the two
iterated base changes is an `Eq.rec` whose weak head normal form the kernel will attempt, and
the K-like reduction of that `Eq.rec` has to decide whether the two iterated base changes are
definitionally equal; they are not — they differ exactly by the commutativity of the square —
and that reduction does not terminate.

For the same reason the hypotheses carrying the glueing isomorphism are written as binders of
the declarations that use them rather than as section variables introduced with `include`: a
section variable whose type mentions one of the definitions of this module is re-elaborated for
every declaration that includes it, and that re-elaboration raises an internal exception: the
declaration is then sealed with an unproved placeholder and no error is reported at all.

## References

* [Stacks Project, Tag 0BP2](https://stacks.math.columbia.edu/tag/0BP2)
* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9P](https://stacks.math.columbia.edu/tag/0F9P)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u v₁ v₂ v₃

namespace BeauvilleLaszlo.Space

/-! ### Isomorphisms of spectra inside the site -/

section SiteIso

variable {R₀ : Type u} [CommRing R₀] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of R₀)))

/-- Two `R₀`-algebra maps with the same `Spec` are equal. -/
private theorem algHom_eq_of_spec_map_eq {A₁ A₂ : Type u} [CommRing A₁] [Algebra R₀ A₁]
    [CommRing A₂] [Algebra R₀ A₂] (φ ψ : A₁ →ₐ[R₀] A₂)
    (h : Spec.map (CommRingCat.ofHom φ.toRingHom) = Spec.map (CommRingCat.ofHom ψ.toRingHom)) :
    φ = ψ :=
  AlgHom.ext fun x => by
    simpa using DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (Spec.map_injective h)) x

/-- The hom dictionary of `AlgebraicGeometry.Space.specSiteHomEquiv` is anti-multiplicative. -/
theorem specSiteHomEquiv_comp {A₁ A₂ A₃ : Type u} [CommRing A₁] [Algebra R₀ A₁]
    [CommRing A₂] [Algebra R₀ A₂] [CommRing A₃] [Algebra R₀ A₃]
    (hA₁ : B.Contains (Spec (.of A₁))) (hA₂ : B.Contains (Spec (.of A₂)))
    (hA₃ : B.Contains (Spec (.of A₃)))
    (w : AlgebraicGeometry.Space.specSite B hS hA₁ ⟶ AlgebraicGeometry.Space.specSite B hS hA₂)
    (w' : AlgebraicGeometry.Space.specSite B hS hA₂ ⟶
      AlgebraicGeometry.Space.specSite B hS hA₃) :
    AlgebraicGeometry.Space.specSiteHomEquiv B hS hA₁ hA₃ (w ≫ w') =
      (AlgebraicGeometry.Space.specSiteHomEquiv B hS hA₁ hA₂ w).comp
        (AlgebraicGeometry.Space.specSiteHomEquiv B hS hA₂ hA₃ w') := by
  have h4 : (BigFppfOver.toScheme B (Spec (.of R₀)) hS).map (w ≫ w') =
      (BigFppfOver.toScheme B (Spec (.of R₀)) hS).map w ≫
        (BigFppfOver.toScheme B (Spec (.of R₀)) hS).map w' := Functor.map_comp _ _ _
  rw [AlgebraicGeometry.Space.specSiteHomEquiv_apply_eq B hS hA₁ hA₃,
    AlgebraicGeometry.Space.specSiteHomEquiv_apply_eq B hS hA₁ hA₂,
    AlgebraicGeometry.Space.specSiteHomEquiv_apply_eq B hS hA₂ hA₃] at h4
  exact algHom_eq_of_spec_map_eq _ _ (h4.trans (Spec.map_comp _ _).symm)

/-- The hom dictionary of `AlgebraicGeometry.Space.specSiteHomEquiv` sends the identity to the
identity. -/
theorem specSiteHomEquiv_id {A₁ : Type u} [CommRing A₁] [Algebra R₀ A₁]
    (hA₁ : B.Contains (Spec (.of A₁))) :
    AlgebraicGeometry.Space.specSiteHomEquiv B hS hA₁ hA₁
        (𝟙 (AlgebraicGeometry.Space.specSite B hS hA₁)) = AlgHom.id R₀ A₁ := by
  have h4 : (BigFppfOver.toScheme B (Spec (.of R₀)) hS).map
      (𝟙 (AlgebraicGeometry.Space.specSite B hS hA₁)) = 𝟙 _ :=
    CategoryTheory.Functor.map_id _ _
  rw [AlgebraicGeometry.Space.specSiteHomEquiv_apply_eq B hS hA₁ hA₁] at h4
  exact algHom_eq_of_spec_map_eq _ _ (h4.trans (Spec.map_id _).symm)

/-- **An isomorphism of the site between the spectra of two `R₀`-algebras is `Spec` of an
isomorphism of `R₀`-algebras.** -/
noncomputable def specSiteAlgEquivOfIso {A₁ A₂ : Type u} [CommRing A₁] [Algebra R₀ A₁]
    [CommRing A₂] [Algebra R₀ A₂]
    (hA₁ : B.Contains (Spec (.of A₁))) (hA₂ : B.Contains (Spec (.of A₂)))
    (e : AlgebraicGeometry.Space.specSite B hS hA₁ ≅
      AlgebraicGeometry.Space.specSite B hS hA₂) :
    A₂ ≃ₐ[R₀] A₁ :=
  AlgEquiv.ofAlgHom (AlgebraicGeometry.Space.specSiteHomEquiv B hS hA₁ hA₂ e.hom)
    (AlgebraicGeometry.Space.specSiteHomEquiv B hS hA₂ hA₁ e.inv)
    (by rw [← specSiteHomEquiv_comp, e.hom_inv_id, specSiteHomEquiv_id])
    (by rw [← specSiteHomEquiv_comp, e.inv_hom_id, specSiteHomEquiv_id])

/-- The underlying morphism of schemes of the forward direction of an isomorphism of the site is
`Spec` of the algebra isomorphism it comes from. -/
theorem toScheme_map_hom_eq_specSiteAlgEquivOfIso {A₁ A₂ : Type u} [CommRing A₁]
    [Algebra R₀ A₁] [CommRing A₂] [Algebra R₀ A₂]
    (hA₁ : B.Contains (Spec (.of A₁))) (hA₂ : B.Contains (Spec (.of A₂)))
    (e : AlgebraicGeometry.Space.specSite B hS hA₁ ≅
      AlgebraicGeometry.Space.specSite B hS hA₂) :
    (BigFppfOver.toScheme B (Spec (.of R₀)) hS).map e.hom =
      Spec.map (CommRingCat.ofHom (specSiteAlgEquivOfIso B hS hA₁ hA₂ e).toAlgHom.toRingHom) :=
  AlgebraicGeometry.Space.specSiteHomEquiv_apply_eq B hS hA₁ hA₂ e.hom

end SiteIso

/-- **An isomorphism of representable algebraic spaces comes from an isomorphism of the site.**
-/
noncomputable def siteIsoOfSpaceIso (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {W W' : BigFppfOver B S hS}
    (hW : IsAlgebraicSpace B S hS (yoneda.obj W))
    (hW' : IsAlgebraicSpace B S hS (yoneda.obj W'))
    (e : spaceOfSite B S hS W hW ≅ spaceOfSite B S hS W' hW') : W ≅ W' :=
  (schemeSpaceFunctor B S hS).preimageIso e

/-- The isomorphism of algebraic spaces `BeauvilleLaszlo.Space.siteIsoOfSpaceIso` comes from. -/
theorem schemeSpaceMap_siteIsoOfSpaceIso_hom (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {W W' : BigFppfOver B S hS}
    (hW : IsAlgebraicSpace B S hS (yoneda.obj W))
    (hW' : IsAlgebraicSpace B S hS (yoneda.obj W'))
    (e : spaceOfSite B S hS W hW ≅ spaceOfSite B S hS W' hW') :
    schemeSpaceMap (siteIsoOfSpaceIso B S hS hW hW' e).hom = e.hom :=
  (schemeSpaceFunctor B S hS).map_preimage e.hom

/-- A cast of objects of a full subcategory of presheaves acts on sections as a cast of
types. -/
theorem eqToHom_app_eq_cast {C : Type v₁} [Category.{v₂} C]
    {P : ObjectProperty (Cᵒᵖ ⥤ Type v₃)} {F₁ F₂ : P.FullSubcategory} (p : F₁ = F₂) (V : Cᵒᵖ)
    (t : F₁.obj.obj V) :
    (eqToHom p).hom.app V t =
      cast (congrArg (fun G : P.FullSubcategory => G.obj.obj V) p) t := by
  cases p
  rfl

/-- A section of the algebraic space of an object of the site, cast along an equality of the
objects it is a section over, is read as the same morphism of the site up to the induced cast. -/
theorem schemeSpaceIso_hom_app_cast_left {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {W X₁ X₂ : BigFppfOver B S hS} (q : X₁ = X₂)
    (h : (schemeSpace W).obj.obj (Opposite.op X₁) = (schemeSpace W).obj.obj (Opposite.op X₂))
    (t : (schemeSpace W).obj.obj (Opposite.op X₁)) :
    ((schemeSpaceIso W).hom.app (Opposite.op X₂) (cast h t)).left =
      eqToHom (congrArg CategoryTheory.Over.left q).symm ≫
        ((schemeSpaceIso W).hom.app (Opposite.op X₁) t).left := by
  subst q
  simp

/-- A canonical cast between the two iterated base changes of a representable algebraic space
along the two sides of a commutative square does not change the underlying morphism of schemes
of a section, read through `AlgebraicGeometry.schemeSpaceIso`. -/
theorem eqToHom_baseChange_two_app_left (B : BigFppfSite.{u}) (X S₁ S₂ T : Scheme.{u})
    (hX : B.Contains X) (hU : B.Contains S₁) (hX' : B.Contains S₂) (hU' : B.Contains T)
    (gU : B.obj hU' ⟶ B.obj hU) (jU : B.obj hU ⟶ B.obj hX)
    (gX' : B.obj hU' ⟶ B.obj hX') (jX' : B.obj hX' ⟶ B.obj hX)
    (hk : gU ≫ jU = gX' ≫ jX')
    (W : BigFppfOver B X hX) (hW : IsAlgebraicSpace B X hX (yoneda.obj W))
    (V : BigFppfOver B T hU')
    (p : (baseChange B T S₁ hU' hU gU).obj
        ((baseChange B S₁ X hU hX jU).obj (spaceOfSite B X hX W hW)) =
      (baseChange B T S₂ hU' hX' gX').obj
        ((baseChange B S₂ X hX' hX jX').obj (spaceOfSite B X hX W hW)))
    (t : ((baseChange B T S₁ hU' hU gU).obj
      ((baseChange B S₁ X hU hX jU).obj (spaceOfSite B X hX W hW))).obj.obj
      (Opposite.op V)) :
    ((schemeSpaceIso W).hom.app
        (Opposite.op ((CategoryTheory.Over.map jX').obj ((CategoryTheory.Over.map gX').obj V)))
        (((eqToHom p).hom.app (Opposite.op V)) t)).left =
      ((schemeSpaceIso W).hom.app
        (Opposite.op ((CategoryTheory.Over.map jU).obj ((CategoryTheory.Over.map gU).obj V)))
        t).left := by
  have hq : (CategoryTheory.Over.map jU).obj ((CategoryTheory.Over.map gU).obj V) =
      (CategoryTheory.Over.map jX').obj ((CategoryTheory.Over.map gX').obj V) := by
    change CategoryTheory.Over.mk ((V.hom ≫ gU) ≫ jU) =
      CategoryTheory.Over.mk ((V.hom ≫ gX') ≫ jX')
    exact congrArg CategoryTheory.Over.mk (by rw [Category.assoc, hk, Category.assoc])
  refine (congrArg (fun z ↦ ((schemeSpaceIso W).hom.app
      (Opposite.op ((CategoryTheory.Over.map jX').obj ((CategoryTheory.Over.map gX').obj V)))
      z).left) (eqToHom_app_eq_cast p (Opposite.op V) t)).trans ?_
  refine Eq.trans (schemeSpaceIso_hom_app_cast_left hq _ t) ?_
  simp

/-- **The cast between the two iterated base changes of a representable affine algebraic space
does not move the underlying morphism of schemes of a section.** This is
`BeauvilleLaszlo.Space.eqToHom_baseChange_two_app_left` with the algebraic space written as
`BeauvilleLaszlo.Space.specSpace`, which is the spelling every statement below uses. The two
spellings are identified here, where nothing else is in scope: asking the kernel to identify
them anywhere a cast between the two iterated base changes is also present makes it attempt the
reduction of that cast, which it does not finish. -/
theorem eqToHom_baseChange_two_specSpace_app_left {R₀ A : Type u} [CommRing R₀]
    [CommRing A] [Algebra R₀ A] (B : BigFppfSite.{u}) (S₁ S₂ T : Scheme.{u})
    (hX : B.Contains (Spec (.of R₀))) (hU : B.Contains S₁) (hX' : B.Contains S₂)
    (hU' : B.Contains T) (hA : B.Contains (Spec (.of A)))
    (gU : B.obj hU' ⟶ B.obj hU) (jU : B.obj hU ⟶ B.obj hX)
    (gX' : B.obj hU' ⟶ B.obj hX') (jX' : B.obj hX' ⟶ B.obj hX)
    (hk : gU ≫ jU = gX' ≫ jX') (V : BigFppfOver B T hU')
    (p : (baseChange B T S₁ hU' hU gU).obj
        ((baseChange B S₁ (Spec (.of R₀)) hU hX jU).obj (specSpace B hX hA)) =
      (baseChange B T S₂ hU' hX' gX').obj
        ((baseChange B S₂ (Spec (.of R₀)) hX' hX jX').obj (specSpace B hX hA)))
    (t : ((baseChange B T S₁ hU' hU gU).obj
      ((baseChange B S₁ (Spec (.of R₀)) hU hX jU).obj (specSpace B hX hA))).obj.obj
      (Opposite.op V)) :
    ((schemeSpaceIso (AlgebraicGeometry.Space.specSite B hX hA)).hom.app
        (Opposite.op ((CategoryTheory.Over.map jX').obj ((CategoryTheory.Over.map gX').obj V)))
        (((eqToHom p).hom.app (Opposite.op V)) t)).left =
      ((schemeSpaceIso (AlgebraicGeometry.Space.specSite B hX hA)).hom.app
        (Opposite.op ((CategoryTheory.Over.map jU).obj ((CategoryTheory.Over.map gU).obj V)))
        t).left :=
  eqToHom_baseChange_two_app_left B (Spec (.of R₀)) S₁ S₂ T hX hU hX' hU' gU jU gX' jX' hk
    (AlgebraicGeometry.Space.specSite B hX hA)
    (isAlgebraicSpace_yoneda B (Spec (.of R₀)) hX _) V p t

/-! ### Comparison of a glueing triple with affine components -/

section Assembly

variable {R S₁ S₂ T : Type u} [CommRing R] [CommRing S₁] [CommRing S₂] [CommRing T]
  [Algebra R S₁] [Algebra R S₂] [Algebra S₁ T] [Algebra S₂ T]
  {A A₁ A' C₁ C₂ : Type u} [CommRing A] [CommRing A₁] [CommRing A'] [CommRing C₁] [CommRing C₂]
  [Algebra R A] [Algebra S₁ A₁] [Algebra S₂ A'] [Algebra T C₁] [Algebra T C₂]
  [Algebra A A₁] [Algebra A A'] [Algebra A₁ C₁] [Algebra A' C₂]
  (B : BigFppfSite.{u}) (hX : B.Contains (Spec (.of R)))
  (hU : B.Contains (Spec (.of S₁))) (hX' : B.Contains (Spec (.of S₂)))
  (hU' : B.Contains (Spec (.of T)))
  (hA : B.Contains (Spec (.of A))) (hA₁ : B.Contains (Spec (.of A₁)))
  (hA' : B.Contains (Spec (.of A'))) (hC₁ : B.Contains (Spec (.of C₁)))
  (hC₂ : B.Contains (Spec (.of C₂)))
  (hp₂ : IsPushout (CommRingCat.ofHom (algebraMap S₁ A₁)) (CommRingCat.ofHom (algebraMap S₁ T))
    (CommRingCat.ofHom (algebraMap A₁ C₁)) (CommRingCat.ofHom (algebraMap T C₁)))
  (hp₄ : IsPushout (CommRingCat.ofHom (algebraMap S₂ A')) (CommRingCat.ofHom (algebraMap S₂ T))
    (CommRingCat.ofHom (algebraMap A' C₂)) (CommRingCat.ofHom (algebraMap T C₂)))
  (Z : GlueingData B (Spec (.of T)) (Spec (.of S₁)) (Spec (.of S₂)) hU' hU hX'
    (AlgebraicGeometry.Space.specSite B hU hU').hom
    (AlgebraicGeometry.Space.specSite B hX' hU').hom)
  (eV : (overU B (Spec (.of T)) (Spec (.of S₁)) (Spec (.of S₂)) hU' hU hX'
      (AlgebraicGeometry.Space.specSite B hU hU').hom
      (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj Z ≅
    spaceOfSite B (Spec (.of S₁)) hU (AlgebraicGeometry.Space.specSite B hU hA₁)
      (isAlgebraicSpace_yoneda B (Spec (.of S₁)) hU _))
  (eW : (overX' B (Spec (.of T)) (Spec (.of S₁)) (Spec (.of S₂)) hU' hU hX'
      (AlgebraicGeometry.Space.specSite B hU hU').hom
      (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj Z ≅
    spaceOfSite B (Spec (.of S₂)) hX' (AlgebraicGeometry.Space.specSite B hX' hA')
      (isAlgebraicSpace_yoneda B (Spec (.of S₂)) hX' _))

/-- The identification of the restriction to `Spec T` of the `Spec S₁`-component of `Z` with the
representable `Spec C₁`. -/
noncomputable def kappaOne :
    (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
        (AlgebraicGeometry.Space.specSite B hU hU').hom).obj
      ((overU B (Spec (.of T)) (Spec (.of S₁)) (Spec (.of S₂)) hU' hU hX'
        (AlgebraicGeometry.Space.specSite B hU hU').hom
        (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj Z) ≅
      spaceOfSite B (Spec (.of T)) hU' (AlgebraicGeometry.Space.specSite B hU' hC₁)
        (isAlgebraicSpace_yoneda B (Spec (.of T)) hU' _) :=
  (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
      (AlgebraicGeometry.Space.specSite B hU hU').hom).mapIso eV ≪≫
    specSpaceBaseChangeIso B hU hU' (algebraMap A₁ C₁) hp₂ hA₁ hC₁

/-- The identification of the restriction to `Spec T` of the `Spec S₂`-component of `Z` with the
representable `Spec C₂`. -/
noncomputable def kappaTwo :
    (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
        (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
      ((overX' B (Spec (.of T)) (Spec (.of S₁)) (Spec (.of S₂)) hU' hU hX'
        (AlgebraicGeometry.Space.specSite B hU hU').hom
        (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj Z) ≅
      spaceOfSite B (Spec (.of T)) hU' (AlgebraicGeometry.Space.specSite B hU' hC₂)
        (isAlgebraicSpace_yoneda B (Spec (.of T)) hU' _) :=
  (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
      (AlgebraicGeometry.Space.specSite B hX' hU').hom).mapIso eW ≪≫
    specSpaceBaseChangeIso B hX' hU' (algebraMap A' C₂) hp₄ hA' hC₂

/-- The glueing isomorphism of `Z`, read through the two presentations as an isomorphism of
representables over `Spec T`. -/
noncomputable def chiIso :
    spaceOfSite B (Spec (.of T)) hU' (AlgebraicGeometry.Space.specSite B hU' hC₁)
        (isAlgebraicSpace_yoneda B (Spec (.of T)) hU' _) ≅
      spaceOfSite B (Spec (.of T)) hU' (AlgebraicGeometry.Space.specSite B hU' hC₂)
        (isAlgebraicSpace_yoneda B (Spec (.of T)) hU' _) :=
  haveI : IsIso Z.1.left.hom := Z.2.1
  haveI : IsIso Z.1.hom := Z.2.2
  (kappaOne (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁) (hC₁ := hC₁)
      (hp₂ := hp₂) (Z := Z) (eV := eV)).symm ≪≫
    (asIso Z.1.left.hom).symm ≪≫ asIso Z.1.hom ≪≫
      kappaTwo (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA' := hA') (hC₂ := hC₂)
        (hp₄ := hp₄) (Z := Z) (eW := eW)

/-- The isomorphism of the site underlying `BeauvilleLaszlo.Space.chiIso`. -/
noncomputable def chiSiteIso :
    AlgebraicGeometry.Space.specSite B hU' hC₁ ≅ AlgebraicGeometry.Space.specSite B hU' hC₂ :=
  siteIsoOfSpaceIso B (Spec (.of T)) hU' _ _
    (chiIso (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁) (hA' := hA')
      (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄) (Z := Z) (eV := eV) (eW := eW))

/-- **The glueing isomorphism of `Z` as an isomorphism of `T`-algebras `C₂ ≃ C₁`.** -/
noncomputable def glueingPsi : C₂ ≃ₐ[T] C₁ :=
  specSiteAlgEquivOfIso B hU' hC₁ hC₂
    (chiSiteIso (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁) (hA' := hA')
      (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄) (Z := Z) (eV := eV) (eW := eW))

/-- Restriction of a section of a two-step base change of a representable algebraic space is
composition with the underlying morphism of schemes, once the section is read as a morphism of
the site through `AlgebraicGeometry.schemeSpaceIso`. -/
theorem baseChange_two_map_left (B : BigFppfSite.{u}) (S₀ S S' : Scheme.{u})
    (h₀ : B.Contains S₀) (hS : B.Contains S) (hS' : B.Contains S')
    (k₁ : B.obj hS ⟶ B.obj h₀) (k₂ : B.obj hS' ⟶ B.obj hS)
    (W : BigFppfOver B S₀ h₀) (hW : IsAlgebraicSpace B S₀ h₀ (yoneda.obj W))
    {V V' : BigFppfOver B S' hS'} (s : V' ⟶ V)
    (t : ((baseChange B S' S hS' hS k₂).obj
      ((baseChange B S S₀ hS h₀ k₁).obj (spaceOfSite B S₀ h₀ W hW))).obj.obj
      (Opposite.op V)) :
    ((schemeSpaceIso W).hom.app
        (Opposite.op ((CategoryTheory.Over.map k₁).obj ((CategoryTheory.Over.map k₂).obj V')))
        ((((baseChange B S' S hS' hS k₂).obj
          ((baseChange B S S₀ hS h₀ k₁).obj (spaceOfSite B S₀ h₀ W hW))).obj.map
        (Opposite.op s)) t)).left =
      s.left ≫ ((schemeSpaceIso W).hom.app
        (Opposite.op ((CategoryTheory.Over.map k₁).obj ((CategoryTheory.Over.map k₂).obj V)))
        t).left :=
  congrArg CategoryTheory.Over.Hom.left (NatTrans.naturality_apply (schemeSpaceIso W).hom
    ((CategoryTheory.Over.map k₁).map ((CategoryTheory.Over.map k₂).map s)).op t :)

/-- `BeauvilleLaszlo.Space.chiIso` is induced by the underlying isomorphism of the site. -/
theorem chiIso_hom_eq :
    (chiIso (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁)
      (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄)
      (Z := Z) (eV := eV) (eW := eW)).hom =
      schemeSpaceMap (chiSiteIso (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁)
        (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄)
        (Z := Z) (eV := eV) (eW := eW)).hom :=
  (schemeSpaceMap_siteIsoOfSpaceIso_hom B (Spec (.of T)) hU' _ _
    (chiIso (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁)
      (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄)
      (Z := Z) (eV := eV) (eW := eW))).symm

/-- The morphism of schemes underlying `BeauvilleLaszlo.Space.chiSiteIso` is `Spec` of
`BeauvilleLaszlo.Space.glueingPsi`. -/
theorem chiSiteIso_hom_left :
    (chiSiteIso (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁) (hA' := hA')
      (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄) (Z := Z) (eV := eV) (eW := eW)).hom.left =
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
        (glueingPsi (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁) (hA' := hA')
          (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄) (Z := Z) (eV := eV)
          (eW := eW)).toAlgHom.toRingHom)) : B.obj hC₁ ⟶ B.obj hC₂) :=
  ObjectProperty.hom_ext _
    (toScheme_map_hom_eq_specSiteAlgEquivOfIso B hU' hC₁ hC₂
      (chiSiteIso (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁) (hA' := hA')
        (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄) (Z := Z) (eV := eV) (eW := eW)))

omit [Algebra R S₁] in
/-- The projection to `Spec A` of the glueing isomorphism of `Z` composed with the second
base-change identification: the tautological point of the composite, read as a morphism of the
site, has underlying morphism of schemes `Spec` of `A → A₁ → C₁`. -/
theorem chi_comp_twoStep_inv_left
    (hp₃ : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R S₂))
      (CommRingCat.ofHom (algebraMap A A')) (CommRingCat.ofHom (algebraMap S₂ A')))
    (he : ∀ x : A, glueingPsi (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁)
        (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄)
        (Z := Z) (eV := eV) (eW := eW)
        (algebraMap A' C₂ (algebraMap A A' x)) =
      algebraMap A₁ C₁ (algebraMap A A₁ x)) :
    ((schemeSpaceIso (AlgebraicGeometry.Space.specSite B hX hA)).hom.app
        (Opposite.op ((CategoryTheory.Over.map
          (AlgebraicGeometry.Space.specSite B hX hX').hom).obj
          ((CategoryTheory.Over.map (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
            (AlgebraicGeometry.Space.specSite B hU' hC₁))))
        (schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hC₁) _
          ((chiIso (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁)
            (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄)
            (Z := Z) (eV := eV) (eW := eW)).hom ≫
            (twoStepBaseChangeIso B hX hX' hU' hA hA' hC₂ (algebraMap A A') (algebraMap A' C₂)
              hp₃ hp₄).inv))).left =
      (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
        ((algebraMap A₁ C₁).comp (algebraMap A A₁)))) : B.obj hC₁ ⟶ B.obj hA) := by
  have hpt := (congrArg (fun φ ↦ schemeSpacePointEquiv
      (AlgebraicGeometry.Space.specSite B hU' hC₁) _
      (φ ≫ (twoStepBaseChangeIso B hX hX' hU' hA hA' hC₂ (algebraMap A A') (algebraMap A' C₂)
        hp₃ hp₄).inv)) (chiIso_hom_eq (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁)
      (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄)
      (Z := Z) (eV := eV) (eW := eW))).trans
    (schemeSpacePointEquiv_schemeSpaceMap_comp
      (chiSiteIso (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁)
      (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄)
      (Z := Z) (eV := eV) (eW := eW)).hom
      (twoStepBaseChangeIso B hX hX' hU' hA hA' hC₂ (algebraMap A A') (algebraMap A' C₂)
        hp₃ hp₄).inv)
  refine (congrArg (fun z ↦ ((schemeSpaceIso (AlgebraicGeometry.Space.specSite B hX hA)).hom.app
      (Opposite.op ((CategoryTheory.Over.map
        (AlgebraicGeometry.Space.specSite B hX hX').hom).obj
        ((CategoryTheory.Over.map (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
          (AlgebraicGeometry.Space.specSite B hU' hC₁)))) z).left) hpt).trans ?_
  refine (baseChange_two_map_left B _ _ _ hX hX' hU' _ _ _
    (isAlgebraicSpace_yoneda _ _ _ _) _ _).trans ?_
  refine (congrArg₂ (· ≫ ·)
    (chiSiteIso_hom_left (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁)
      (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄)
      (Z := Z) (eV := eV) (eW := eW))
    (twoStepBaseChangeIso_inv_app_id_left B hX hX' hU' hA hA' hC₂
      (algebraMap A A') (algebraMap A' C₂) hp₃ hp₄)).trans ?_
  apply ObjectProperty.hom_ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun x => by simpa using he x)

/-! ### The cast between the two routes of the square -/

section Cast

variable
  (hp₁ : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R S₁))
    (CommRingCat.ofHom (algebraMap A A₁)) (CommRingCat.ofHom (algebraMap S₁ A₁)))
  (hp₃ : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R S₂))
    (CommRingCat.ofHom (algebraMap A A')) (CommRingCat.ofHom (algebraMap S₂ A')))
  (hcomm : (AlgebraicGeometry.Space.specSite B hU hU').hom ≫
      (AlgebraicGeometry.Space.specSite B hX hU).hom =
    (AlgebraicGeometry.Space.specSite B hX' hU').hom ≫
      (AlgebraicGeometry.Space.specSite B hX hX').hom)
  (p : (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
        (AlgebraicGeometry.Space.specSite B hU hU').hom).obj
      ((baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
        (AlgebraicGeometry.Space.specSite B hX hU).hom).obj
        (specSpace B hX hA)) =
    (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
        (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
      ((baseChange B (Spec (.of S₂)) (Spec (.of R)) hX' hX
        (AlgebraicGeometry.Space.specSite B hX hX').hom).obj
        (specSpace B hX hA)))

include hcomm in
/-- **The canonical cast carries the tautological point of one presentation of the base change
of `Spec A` to `Spec T` to the tautological point of the other.** Both sections project to
`Spec` of `A → A₁ → C₁`: the one on the left because the cast does not move the underlying
morphism of schemes and
`BeauvilleLaszlo.Space.twoStepBaseChangeIso_inv_app_id_left` computes it, the one on the right
by `BeauvilleLaszlo.Space.chi_comp_twoStep_inv_left`, which is where the glueing isomorphism of
`Z` and the compatibility `he` enter. -/
theorem castSectionEq
    (he : ∀ x : A, glueingPsi (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁)
        (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄)
        (Z := Z) (eV := eV) (eW := eW) (algebraMap A' C₂ (algebraMap A A' x)) =
      algebraMap A₁ C₁ (algebraMap A A₁ x))
    :
    (eqToHom p).hom.app (Opposite.op (AlgebraicGeometry.Space.specSite B hU' hC₁))
        (schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hC₁) _
          (twoStepBaseChangeIso B hX hU hU' hA hA₁ hC₁ (algebraMap A A₁) (algebraMap A₁ C₁)
          hp₁ hp₂).inv) =
      (twoStepBaseChangeIso B hX hX' hU' hA hA' hC₂ (algebraMap A A') (algebraMap A' C₂)
          hp₃ hp₄).inv.hom.app (Opposite.op (AlgebraicGeometry.Space.specSite B hU' hC₁))
        (schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hC₁) _
          (chiIso (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁)
            (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄)
            (Z := Z) (eV := eV) (eW := eW)).hom) :=
  ((schemeSpaceIso (AlgebraicGeometry.Space.specSite B hX hA)).app
      (Opposite.op ((CategoryTheory.Over.map
        (AlgebraicGeometry.Space.specSite B hX hX').hom).obj
        ((CategoryTheory.Over.map (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
          (AlgebraicGeometry.Space.specSite B hU' hC₁))))).toEquiv.injective <|
  Over.OverMorphism.ext
    (((eqToHom_baseChange_two_specSpace_app_left B (Spec (.of S₁)) (Spec (.of S₂))
        (Spec (.of T)) hX hU hX' hU' hA _ _ _ _ hcomm
        (AlgebraicGeometry.Space.specSite B hU' hC₁) p _).trans
      (twoStepBaseChangeIso_inv_app_id_left B hX hU hU' hA hA₁ hC₁
        (algebraMap A A₁) (algebraMap A₁ C₁) hp₁ hp₂)).trans <|
      (chi_comp_twoStep_inv_left (B := B) (hU := hU) (hX' := hX') (hU' := hU')
        (hA₁ := hA₁) (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄)
        (Z := Z) (eV := eV) (eW := eW) (hX := hX) (hA := hA) (hp₃ := hp₃) (he := he)).symm.trans
      (congrArg (fun z ↦ ((schemeSpaceIso (AlgebraicGeometry.Space.specSite B hX hA)).hom.app
        (Opposite.op ((CategoryTheory.Over.map
          (AlgebraicGeometry.Space.specSite B hX hX').hom).obj
          ((CategoryTheory.Over.map (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
            (AlgebraicGeometry.Space.specSite B hU' hC₁)))) z).left)
        (schemeSpacePointEquiv_comp _ _)))

end Cast

/-! ### The heart of the argument -/

section Heart

variable
  (hp₁ : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R S₁))
    (CommRingCat.ofHom (algebraMap A A₁)) (CommRingCat.ofHom (algebraMap S₁ A₁)))
  (hp₃ : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R S₂))
    (CommRingCat.ofHom (algebraMap A A')) (CommRingCat.ofHom (algebraMap S₂ A')))
  (kappa : (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
        (AlgebraicGeometry.Space.specSite B hU hU').hom).obj
      ((baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
        (AlgebraicGeometry.Space.specSite B hX hU).hom).obj
        (specSpace B hX hA)) ⟶
    (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
        (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
      ((baseChange B (Spec (.of S₂)) (Spec (.of R)) hX' hX
        (AlgebraicGeometry.Space.specSite B hX hX').hom).obj
        (specSpace B hX hA)))

/-- The glueing isomorphism of `Z` followed by the inverse of the second base-change
identification is the inverse of the first one followed by the comparison `kappa`. -/
theorem chiKeyEq
    (hsec : kappa.hom.app (Opposite.op (AlgebraicGeometry.Space.specSite B hU' hC₁))
          (schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hC₁) _
          (twoStepBaseChangeIso B hX hU hU' hA hA₁ hC₁ (algebraMap A A₁) (algebraMap A₁ C₁)
            hp₁ hp₂).inv) =
        (twoStepBaseChangeIso B hX hX' hU' hA hA' hC₂ (algebraMap A A') (algebraMap A' C₂)
            hp₃ hp₄).inv.hom.app (Opposite.op (AlgebraicGeometry.Space.specSite B hU' hC₁))
          (schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hC₁) _
          (chiIso (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁)
              (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄)
              (Z := Z) (eV := eV) (eW := eW)).hom))
    :
    (chiIso (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁) (hA' := hA')
          (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄)
          (Z := Z) (eV := eV) (eW := eW)).hom ≫
        (twoStepBaseChangeIso B hX hX' hU' hA hA' hC₂ (algebraMap A A')
          (algebraMap A' C₂) hp₃ hp₄).inv =
      (twoStepBaseChangeIso B hX hU hU' hA hA₁ hC₁ (algebraMap A A₁)
          (algebraMap A₁ C₁) hp₁ hp₂).inv ≫ kappa :=
  hom_ext_of_section_comp B (Spec (.of T)) hU'
    (AlgebraicGeometry.Space.specSite B hU' hC₁) _ _ _ _ hsec.symm

/-- **The heart of the essential-surjectivity argument.** The glueing isomorphism of `Z`,
transported to the two representables `Spec C₁` and `Spec C₂`, is the comparison `kappa` of the
two presentations of the base change of `Spec A` to `Spec T`. -/
theorem heartEq
    (hsec : kappa.hom.app (Opposite.op (AlgebraicGeometry.Space.specSite B hU' hC₁))
          (schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hC₁) _
          (twoStepBaseChangeIso B hX hU hU' hA hA₁ hC₁ (algebraMap A A₁) (algebraMap A₁ C₁)
            hp₁ hp₂).inv) =
        (twoStepBaseChangeIso B hX hX' hU' hA hA' hC₂ (algebraMap A A') (algebraMap A' C₂)
            hp₃ hp₄).inv.hom.app (Opposite.op (AlgebraicGeometry.Space.specSite B hU' hC₁))
          (schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hC₁) _
          (chiIso (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁)
              (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄)
              (Z := Z) (eV := eV) (eW := eW)).hom))
    :
    (twoStepBaseChangeIso B hX hU hU' hA hA₁ hC₁ (algebraMap A A₁)
          (algebraMap A₁ C₁) hp₁ hp₂).hom ≫
        (chiIso (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁) (hA' := hA')
          (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄)
          (Z := Z) (eV := eV) (eW := eW)).hom =
      kappa ≫
        (twoStepBaseChangeIso B hX hX' hU' hA hA' hC₂ (algebraMap A A')
          (algebraMap A' C₂) hp₃ hp₄).hom := by
  have hkey := chiKeyEq (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁)
    (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄) (Z := Z)
    (eV := eV) (eW := eW) (hX := hX) (hA := hA) (hp₁ := hp₁) (hp₃ := hp₃)
    (kappa := kappa) (hsec := hsec)
  rw [Iso.comp_inv_eq] at hkey
  rw [hkey, Category.assoc, Iso.hom_inv_id_assoc]

end Heart

/-! ### The triple of the glued algebra -/

section Iso

variable
  (hp₁ : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R S₁))
    (CommRingCat.ofHom (algebraMap A A₁)) (CommRingCat.ofHom (algebraMap S₁ A₁)))
  (hp₃ : IsPushout (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R S₂))
    (CommRingCat.ofHom (algebraMap A A')) (CommRingCat.ofHom (algebraMap S₂ A')))
  (hcomm : (AlgebraicGeometry.Space.specSite B hU hU').hom ≫
      (AlgebraicGeometry.Space.specSite B hX hU).hom =
    (AlgebraicGeometry.Space.specSite B hX' hU').hom ≫
      (AlgebraicGeometry.Space.specSite B hX hX').hom)
  (G : GlueingFunctorSpec B (Spec (.of T)) (Spec (.of S₁)) (Spec (.of S₂)) (Spec (.of R))
    hU' hU hX' hX (AlgebraicGeometry.Space.specSite B hU hU').hom
    (AlgebraicGeometry.Space.specSite B hX' hU').hom
    (AlgebraicGeometry.Space.specSite B hX hU).hom
    (AlgebraicGeometry.Space.specSite B hX hX').hom hcomm)

/-- The identification of the `Spec S₁`-component of the triple of `Spec A` with that of `Z`:
the first is the base change of `Spec A` along `Spec S₁ → Spec R`, hence `Spec A₁`, and the
second is `Spec A₁` by the given presentation. -/
noncomputable def isoU :
    (overU B (Spec (.of T)) (Spec (.of S₁)) (Spec (.of S₂)) hU' hU hX'
        (AlgebraicGeometry.Space.specSite B hU hU').hom
        (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
      (G.functor.obj (specSpace B hX hA)) ≅
      (overU B (Spec (.of T)) (Spec (.of S₁)) (Spec (.of S₂)) hU' hU hX'
        (AlgebraicGeometry.Space.specSite B hU hU').hom
        (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj Z :=
  G.overUIso.app (specSpace B hX hA) ≪≫
    specSpaceBaseChangeIso B hX hU (algebraMap A A₁) hp₁ hA hA₁ ≪≫ eV.symm

/-- The identification of the `Spec S₂`-component of the triple of `Spec A` with that of `Z`. -/
noncomputable def isoX' :
    (overX' B (Spec (.of T)) (Spec (.of S₁)) (Spec (.of S₂)) hU' hU hX'
        (AlgebraicGeometry.Space.specSite B hU hU').hom
        (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
      (G.functor.obj (specSpace B hX hA)) ≅
      (overX' B (Spec (.of T)) (Spec (.of S₁)) (Spec (.of S₂)) hU' hU hX'
        (AlgebraicGeometry.Space.specSite B hU hU').hom
        (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj Z :=
  G.overX'Iso.app (specSpace B hX hA) ≪≫
    specSpaceBaseChangeIso B hX hX' (algebraMap A A') hp₃ hA hA' ≪≫ eW.symm

/-- The restriction to `Spec T` of `BeauvilleLaszlo.Space.isoU`, read through the two-step base
change of `Spec A` on one side and `BeauvilleLaszlo.Space.kappaOne` on the other. -/
theorem baseChange_isoU_hom :
    (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
          (AlgebraicGeometry.Space.specSite B hU hU').hom).map
        (isoU (B := B) (hX := hX) (hU := hU) (hX' := hX') (hU' := hU') (hA := hA) (hA₁ := hA₁)
          (Z := Z) (eV := eV) (hp₁ := hp₁) (hcomm := hcomm) (G := G)).hom =
      (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
          (AlgebraicGeometry.Space.specSite B hU hU').hom).map
          (G.overUIso.hom.app (specSpace B hX hA)) ≫
        (twoStepBaseChangeIso B hX hU hU' hA hA₁ hC₁ (algebraMap A A₁)
          (algebraMap A₁ C₁) hp₁ hp₂).hom ≫
          (kappaOne (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁) (hC₁ := hC₁)
            (hp₂ := hp₂) (Z := Z) (eV := eV)).inv := by
  simp only [isoU, twoStepBaseChangeIso, kappaOne, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  simp

/-- The restriction to `Spec T` of `BeauvilleLaszlo.Space.isoX'`, read through the two-step base
change of `Spec A` on one side and `BeauvilleLaszlo.Space.kappaTwo` on the other. -/
theorem baseChange_isoX'_hom :
    (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
          (AlgebraicGeometry.Space.specSite B hX' hU').hom).map
        (isoX' (B := B) (hX := hX) (hU := hU) (hX' := hX') (hU' := hU') (hA := hA) (hA' := hA')
          (Z := Z) (eW := eW) (hp₃ := hp₃) (hcomm := hcomm) (G := G)).hom =
      (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
          (AlgebraicGeometry.Space.specSite B hX' hU').hom).map
          (G.overX'Iso.hom.app (specSpace B hX hA)) ≫
        (twoStepBaseChangeIso B hX hX' hU' hA hA' hC₂ (algebraMap A A')
          (algebraMap A' C₂) hp₃ hp₄).hom ≫
          (kappaTwo (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA' := hA') (hC₂ := hC₂)
            (hp₄ := hp₄) (Z := Z) (eW := eW)).inv := by
  simp only [isoX', twoStepBaseChangeIso, kappaTwo, Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp, Category.assoc]
  simp

/-- The glueing isomorphism of `Z`, conjugated to the two representables, is
`BeauvilleLaszlo.Space.chiIso`; that is what `chiIso` was built to be. -/
theorem glueingDataCompare_eq_chiIso :
    (glueingDataCompare B (Spec (.of T)) (Spec (.of S₁)) (Spec (.of S₂)) hU' hU hX'
        (AlgebraicGeometry.Space.specSite B hU hU').hom
        (AlgebraicGeometry.Space.specSite B hX' hU').hom Z).hom =
      (kappaOne (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁) (hC₁ := hC₁)
          (hp₂ := hp₂) (Z := Z) (eV := eV)).hom ≫
        (chiIso (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁) (hA' := hA')
            (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄)
            (Z := Z) (eV := eV) (eW := eW)).hom ≫
          (kappaTwo (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA' := hA') (hC₂ := hC₂)
            (hp₄ := hp₄) (Z := Z) (eW := eW)).inv := by
  simp only [chiIso, glueingDataCompare, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, Iso.hom_inv_id_assoc]
  simp

include hcomm in
/-- **The glueing isomorphism of the triple of `Spec A` is the cast between the two routes of
the square**, once the two outer components are identified with the two base changes. This is
`BeauvilleLaszlo.Space.functor_obj_toU_comp_eq_toX'_comp` with the glueing isomorphism in
front. -/
theorem compare_functor_obj_comp :
    (glueingDataCompare B (Spec (.of T)) (Spec (.of S₁)) (Spec (.of S₂)) hU' hU hX'
          (AlgebraicGeometry.Space.specSite B hU hU').hom
          (AlgebraicGeometry.Space.specSite B hX' hU').hom
          (G.functor.obj (specSpace B hX hA))).hom ≫
        (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
            (AlgebraicGeometry.Space.specSite B hX' hU').hom).map
          (G.overX'Iso.hom.app (specSpace B hX hA)) =
      (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
            (AlgebraicGeometry.Space.specSite B hU hU').hom).map
          (G.overUIso.hom.app (specSpace B hX hA)) ≫
        eqToHom (baseChange_square_obj_eq B (Spec (.of T)) (Spec (.of S₁)) (Spec (.of S₂))
          (Spec (.of R)) hU' hU hX' hX _ _ _ _ hcomm (specSpace B hX hA)) := by
  have : IsIso (G.functor.obj (specSpace B hX hA)).1.left.hom :=
    (G.functor.obj (specSpace B hX hA)).2.1
  simp only [glueingDataCompare, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, IsIso.inv_comp_eq]
  exact (functor_obj_toU_comp_eq_toX'_comp B (Spec (.of T)) (Spec (.of S₁)) (Spec (.of S₂))
    (Spec (.of R)) hU' hU hX' hX _ _ _ _ G (specSpace B hX hA)).symm

/-! The comparison of the two presentations of the base change of `Spec A` to `Spec T` is taken
abstractly, together with the two facts about it the assembly needs: that it carries one
tautological point to the other, and that it is the glueing isomorphism of the triple of
`Spec A`. Both are supplied by the canonical cast, but keeping it abstract here keeps it out of
every proof below — the two objects it compares are not definitionally equal, so any demand for
its weak head normal form is a reduction the kernel cannot complete. -/

variable
  (kappa : (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
        (AlgebraicGeometry.Space.specSite B hU hU').hom).obj
      ((baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
        (AlgebraicGeometry.Space.specSite B hX hU).hom).obj
        (specSpace B hX hA)) ⟶
    (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
        (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
      ((baseChange B (Spec (.of S₂)) (Spec (.of R)) hX' hX
        (AlgebraicGeometry.Space.specSite B hX hX').hom).obj
        (specSpace B hX hA)))

/-- **The triple of a cartesian datum is the triple of the glued algebra.** The two outer
components are identified with those of `Z` by `BeauvilleLaszlo.Space.isoU` and
`BeauvilleLaszlo.Space.isoX'`, and `BeauvilleLaszlo.Space.heartEq` is exactly the compatibility
of those two identifications with the two glueing isomorphisms that
`BeauvilleLaszlo.Space.glueingDataIsoMk_of_compare` asks for. -/
noncomputable def glueingDataIsoOfGlued
    (hsec : kappa.hom.app (Opposite.op (AlgebraicGeometry.Space.specSite B hU' hC₁))
          (schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hC₁) _
          (twoStepBaseChangeIso B hX hU hU' hA hA₁ hC₁ (algebraMap A A₁) (algebraMap A₁ C₁)
            hp₁ hp₂).inv) =
        (twoStepBaseChangeIso B hX hX' hU' hA hA' hC₂ (algebraMap A A') (algebraMap A' C₂)
            hp₃ hp₄).inv.hom.app (Opposite.op (AlgebraicGeometry.Space.specSite B hU' hC₁))
          (schemeSpacePointEquiv (AlgebraicGeometry.Space.specSite B hU' hC₁) _
          (chiIso (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁)
              (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄)
              (Z := Z) (eV := eV) (eW := eW)).hom))
    (hD : (glueingDataCompare B (Spec (.of T)) (Spec (.of S₁)) (Spec (.of S₂)) hU' hU hX'
            (AlgebraicGeometry.Space.specSite B hU hU').hom
            (AlgebraicGeometry.Space.specSite B hX' hU').hom
            (G.functor.obj (specSpace B hX hA))).hom ≫
          (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
              (AlgebraicGeometry.Space.specSite B hX' hU').hom).map
            (G.overX'Iso.hom.app (specSpace B hX hA)) =
        (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
              (AlgebraicGeometry.Space.specSite B hU hU').hom).map
            (G.overUIso.hom.app (specSpace B hX hA)) ≫ kappa)
    :
    G.functor.obj (specSpace B hX hA) ≅ Z := by
  refine glueingDataIsoMk_of_compare B (Spec (.of T)) (Spec (.of S₁)) (Spec (.of S₂))
    hU' hU hX' _ _
    (isoU (B := B) (hX := hX) (hU := hU) (hX' := hX') (hU' := hU') (hA := hA) (hA₁ := hA₁)
      (Z := Z) (eV := eV) (hp₁ := hp₁) (hcomm := hcomm) (G := G))
    (isoX' (B := B) (hX := hX) (hU := hU) (hX' := hX') (hU' := hU') (hA := hA) (hA' := hA')
      (Z := Z) (eW := eW) (hp₃ := hp₃) (hcomm := hcomm) (G := G)) ?_
  have hkey := heartEq (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁)
    (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄) (Z := Z)
    (eV := eV) (eW := eW) (hX := hX) (hA := hA) (hp₁ := hp₁) (hp₃ := hp₃)
    (kappa := kappa) (hsec := hsec)
  rw [glueingDataCompare_eq_chiIso (hA₁ := hA₁) (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂)
      (hp₂ := hp₂) (hp₄ := hp₄) (eV := eV) (eW := eW),
    baseChange_isoU_hom (hC₁ := hC₁) (hp₂ := hp₂),
    baseChange_isoX'_hom (hC₂ := hC₂) (hp₄ := hp₄)]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  have hkey₂ := congrArg (fun t ↦ t ≫ (kappaTwo (B := B) (hU := hU) (hX' := hX') (hU' := hU')
    (hA' := hA') (hC₂ := hC₂) (hp₄ := hp₄) (Z := Z) (eW := eW)).inv) hkey
  have hD₂ := congrArg (fun t ↦ t ≫ (twoStepBaseChangeIso B hX hX' hU' hA hA' hC₂
      (algebraMap A A') (algebraMap A' C₂) hp₃ hp₄).hom ≫
    (kappaTwo (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA' := hA') (hC₂ := hC₂)
      (hp₄ := hp₄) (Z := Z) (eW := eW)).inv) hD
  simp only [Category.assoc] at hkey₂ hD₂
  rw [hkey₂]
  exact hD₂

/-! The comparison of the two iterated base changes is the cast along the equality of objects
that the commutativity of the square provides. That equality is introduced below by `obtain`,
so that it is an *unspecified* proof wherever the comparison is formed. This is what keeps the
argument away from a reduction the kernel cannot complete: a cast along a named equality of the
two iterated base changes is an `Eq.rec` whose weak head normal form the kernel will attempt,
and the K-like reduction of that `Eq.rec` has to decide whether the two iterated base changes
are definitionally equal. They are not — they differ exactly by `hcomm` — and that reduction does
not terminate. -/

include hcomm in
/-- **The equality of the two iterated base changes of `Spec A`, together with the fact that the
cast along it is the glueing isomorphism of the triple of `Spec A`.** -/
theorem exists_cast_of_square :
    ∃ p : (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
          (AlgebraicGeometry.Space.specSite B hU hU').hom).obj
        ((baseChange B (Spec (.of S₁)) (Spec (.of R)) hU hX
          (AlgebraicGeometry.Space.specSite B hX hU).hom).obj (specSpace B hX hA)) =
      (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
          (AlgebraicGeometry.Space.specSite B hX' hU').hom).obj
        ((baseChange B (Spec (.of S₂)) (Spec (.of R)) hX' hX
          (AlgebraicGeometry.Space.specSite B hX hX').hom).obj (specSpace B hX hA)),
      (glueingDataCompare B (Spec (.of T)) (Spec (.of S₁)) (Spec (.of S₂)) hU' hU hX'
            (AlgebraicGeometry.Space.specSite B hU hU').hom
            (AlgebraicGeometry.Space.specSite B hX' hU').hom
            (G.functor.obj (specSpace B hX hA))).hom ≫
          (baseChange B (Spec (.of T)) (Spec (.of S₂)) hU' hX'
              (AlgebraicGeometry.Space.specSite B hX' hU').hom).map
            (G.overX'Iso.hom.app (specSpace B hX hA)) =
        (baseChange B (Spec (.of T)) (Spec (.of S₁)) hU' hU
              (AlgebraicGeometry.Space.specSite B hU hU').hom).map
            (G.overUIso.hom.app (specSpace B hX hA)) ≫ eqToHom p :=
  ⟨baseChange_square_obj_eq B (Spec (.of T)) (Spec (.of S₁)) (Spec (.of S₂))
      (Spec (.of R)) hU' hU hX' hX _ _ _ _ hcomm (specSpace B hX hA),
    compare_functor_obj_comp B hX hU hX' hU' hA hcomm G⟩

include hp₁ hp₃ in
/-- **The triple of a cartesian datum is isomorphic to the triple of the glued algebra.** The
two outer components are identified with those of `Z` by `BeauvilleLaszlo.Space.isoU` and
`BeauvilleLaszlo.Space.isoX'`, the comparison of the two iterated base changes is taken from
`BeauvilleLaszlo.Space.exists_cast_of_square`, and the compatibility of the identifications with
the two glueing isomorphisms is `BeauvilleLaszlo.Space.heartEq` through
`BeauvilleLaszlo.Space.castSectionEq`. -/
theorem nonempty_glueingDataIso
    (he : ∀ x : A, glueingPsi (B := B) (hU := hU) (hX' := hX') (hU' := hU') (hA₁ := hA₁)
        (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂) (hp₂ := hp₂) (hp₄ := hp₄)
        (Z := Z) (eV := eV) (eW := eW) (algebraMap A' C₂ (algebraMap A A' x)) =
      algebraMap A₁ C₁ (algebraMap A A₁ x)) :
    Nonempty (G.functor.obj (specSpace B hX hA) ≅ Z) := by
  obtain ⟨p, hp⟩ := exists_cast_of_square B hX hU hX' hU' hA hcomm G
  exact ⟨glueingDataIsoOfGlued (B := B) (hX := hX) (hU := hU) (hX' := hX') (hU' := hU')
    (hA := hA) (hA₁ := hA₁) (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂)
    (hp₂ := hp₂) (hp₄ := hp₄) (Z := Z) (eV := eV) (eW := eW)
    (hp₁ := hp₁) (hp₃ := hp₃) (hcomm := hcomm) (G := G) (kappa := eqToHom p)
    (hsec := castSectionEq (B := B) (hX := hX) (hU := hU) (hX' := hX') (hU' := hU')
    (hA := hA) (hA₁ := hA₁) (hA' := hA') (hC₁ := hC₁) (hC₂ := hC₂)
    (hp₂ := hp₂) (hp₄ := hp₄) (Z := Z) (eV := eV) (eW := eW)
    (hp₁ := hp₁) (hp₃ := hp₃) (hcomm := hcomm) (he := he) (p := p)) (hD := hp)⟩

end Iso

end Assembly

end BeauvilleLaszlo.Space

end

