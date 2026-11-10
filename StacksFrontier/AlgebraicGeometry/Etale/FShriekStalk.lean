module

public import StacksFrontier.AlgebraicGeometry.Etale.FiniteSupport
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# The direct image with compact support, and its stalks

Let `f : X ⟶ Y` be a morphism of a big étale site which is locally quasi-finite as a morphism
of schemes. The *direct image with compact support* `f_! F` of an abelian sheaf `F` on the
small étale site of `X` is the sheafification of the finite-support direct image presheaf
`f_{p!} F` of Stacks 0F6M. Sheafification does not change the stalk of a presheaf at a
geometric point, so the stalk of `f_! F` is the stalk of `f_{p!} F`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.fShriekFunctor` — the functor `f_!` on abelian étale sheaves.
* `AlgebraicGeometry.etaleStalkSheafificationMap` — the map on stalks induced by the
  sheafification unit, with `AlgebraicGeometry.etaleStalkSheafificationIso` the inverse
  isomorphism and `AlgebraicGeometry.etaleStalkFShriekFunctorIso` its instance for `f_!`.

## Main results

* `AlgebraicGeometry.isIso_etaleStalk_map_toSheafify` — the map a sheafification unit induces
  on stalks at a geometric point is an isomorphism, so the stalk of `f_! F` is the stalk of
  `f_{p!} F`. `AlgebraicGeometry.etaleStalkSheafificationIso_inv` and
  `AlgebraicGeometry.colimit_ι_comp_etaleStalkSheafificationMap` pin down that isomorphism and
  its effect on a germ.

## Implementation notes

The invariance of a stalk under sheafification is not proved here: by
`AlgebraicGeometry.etaleStalk_eq_presheafFiber` the stalk at a geometric point is the fibre of
the point `AlgebraicGeometry.geometricPointSitePoint` of the small étale site, and Mathlib's
theory of points of a site already knows that a fibre functor inverts the sheafification unit. The
content of the lemmas below is that the colimit comparison map written with the étale
neighbourhood diagram *is* that fibre map, which holds definitionally.

The coefficient universe of `AlgebraicGeometry.SmallEtale.fShriekFunctor` is `max (u + 1) v`
for the scheme universe `u`. That cutoff is load-bearing rather than cosmetic: it is what makes
the index `AlgebraicGeometry.SmallEtale.FiniteSupport` of the colimit defining `f_{p!}` small,
and what supplies sheafification on the small étale site through essential smallness. The
general-purpose statements about stalks leave the coefficient category and its universes free.

This `f_!` is the one of Stacks 0F6R, for a locally quasi-finite morphism, built from sections
with finite support. It is *not*
`AlgebraicGeometry.SmallEtale.fShriekSubsheaf` of
`StacksFrontier.AlgebraicGeometry.Etale.FShriekSubsheaf`, which is the `f_!` of Stacks 0F4X for a
morphism locally of finite type, cut out of `f_*` by properness of supports.

## References

* [Stacks Project, Tag 0F6R](https://stacks.math.columbia.edu/tag/0F6R)
* [Stacks Project, Tag 0F5F](https://stacks.math.columbia.edu/tag/0F5F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace AlgebraicGeometry

section Sheafification

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- Abelian sheafification is available on the chosen small étale site as soon as the
coefficient universe is large enough for the site to be essentially small in it. -/
public instance (priority := low) hasSheafify_smallEtaleTopology
    [EssentiallySmall.{w} (SmallEtale B S hS)] :
    HasSheafify (SmallEtale.topology B S hS) AddCommGrpCat.{w} :=
  hasSheafifyEssentiallySmallSite.{_, _, _, _, w} _ _

variable {A : Type v} [Category.{w} A] [HasColimitsOfSize.{u, u} A] [HasProducts.{u} A]
  [HasWeakSheafify (SmallEtale.topology B S hS) A]

/-- The map on stalks induced by the sheafification unit of a presheaf on the small étale
site. -/
public abbrev etaleStalkSheafificationMap (P : (SmallEtale B S hS)ᵒᵖ ⥤ A) :
    etaleStalk B S hS s P ⟶
      etaleStalk B S hS s ((presheafToSheaf (SmallEtale.topology B S hS) A).obj P).obj :=
  colim.map (Functor.whiskerLeft (Functor.Elements.π (geometricPointFiber B S hS s)).op
    (toSheafify (SmallEtale.topology B S hS) P))

/-- Sheafification does not change the stalk of a presheaf at a geometric point: the map it
induces on stalks is an isomorphism. This is the fibre functor of
`AlgebraicGeometry.geometricPointSitePoint` inverting the sheafification unit. -/
public instance isIso_etaleStalk_map_toSheafify (P : (SmallEtale B S hS)ᵒᵖ ⥤ A) :
    IsIso (etaleStalkSheafificationMap B S hS s P) :=
  inferInstanceAs (IsIso ((geometricPointSitePoint B S hS s).presheafFiber.map
    (toSheafify (SmallEtale.topology B S hS) P)))

/-- The stalk of the sheafification of a presheaf on the small étale site at a geometric point
is the stalk of the presheaf. -/
public def etaleStalkSheafificationIso (P : (SmallEtale B S hS)ᵒᵖ ⥤ A) :
    etaleStalk B S hS s ((presheafToSheaf (SmallEtale.topology B S hS) A).obj P).obj ≅
      etaleStalk B S hS s P :=
  (asIso (etaleStalkSheafificationMap B S hS s P)).symm

/-- The inverse of `etaleStalkSheafificationIso` is the map on stalks induced by the
sheafification unit. -/
@[simp]
public lemma etaleStalkSheafificationIso_inv (P : (SmallEtale B S hS)ᵒᵖ ⥤ A) :
    (etaleStalkSheafificationIso B S hS s P).inv =
      etaleStalkSheafificationMap B S hS s P :=
  rfl

/-- The map on stalks induced by the sheafification unit, followed by the forward map of
`etaleStalkSheafificationIso`, is the identity. -/
@[simp]
public lemma etaleStalkSheafificationMap_comp_iso_hom (P : (SmallEtale B S hS)ᵒᵖ ⥤ A) :
    etaleStalkSheafificationMap B S hS s P ≫
      (etaleStalkSheafificationIso B S hS s P).hom = 𝟙 _ :=
  (etaleStalkSheafificationIso B S hS s P).inv_hom_id

omit [HasProducts.{u} A] in
/-- The germ at a geometric point of a section of the sheafification of a presheaf, computed
through the comparison of the two stalks. -/
public lemma colimit_ι_comp_etaleStalkSheafificationMap (P : (SmallEtale B S hS)ᵒᵖ ⥤ A)
    (U : (geometricPointFiber B S hS s).Elementsᵒᵖ) :
    colimit.ι ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙ P) U ≫
        etaleStalkSheafificationMap B S hS s P =
      (toSheafify (SmallEtale.topology B S hS) P).app (op U.unop.1) ≫
        colimit.ι ((Functor.Elements.π (geometricPointFiber B S hS s)).op ⋙
          ((presheafToSheaf (SmallEtale.topology B S hS) A).obj P).obj) U :=
  colimit.ι_map _ U

end Sheafification

namespace SmallEtale

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
  [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

/-- **Stacks 0F6R.** The direct image with compact support `f_!` of a locally quasi-finite
morphism, on abelian sheaves on the small étale sites: the sheafification of the finite-support
direct image presheaf `f_{p!}` of Stacks 0F6M. -/
@[stacks 0F6R, implicit_reducible]
public def fShriekFunctor :
    Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v} ⥤
      Sheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v} :=
  (finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1 ⋙
    presheafToSheaf (SmallEtale.topology B Y.obj Y.property) AddCommGrpCat.{max (u + 1) v}

/-- The stalk of `f_! F` at a geometric point of `Y` is the stalk of the finite-support direct
image presheaf `f_{p!} F`. -/
public def etaleStalkFShriekFunctorIso (s : GeometricPoint Y.obj)
    (F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{max (u + 1) v}) :
    etaleStalk B Y.obj Y.property s ((fShriekFunctor.{u, v} B f).obj F).obj ≅
      etaleStalk B Y.obj Y.property s
        ((finiteSupportPushforward.{u, max (u + 1) v} B f (fun _ => inferInstance)).1.obj F) :=
  etaleStalkSheafificationIso B Y.obj Y.property s _

end SmallEtale

end AlgebraicGeometry

end
