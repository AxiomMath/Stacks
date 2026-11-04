module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleSitePostcomposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty

/-!
# The spaces-étale site of a formal algebraic space as a category of formal spaces

Let `S` be a scheme contained in a big fppf site `B`, and let `X` be a formal algebraic space
over `S` with reduction `X_red`. The site `X_{spaces, étale}` is, by definition (Stacks 0DEA,
part (2)), the spaces-étale site of `X_red`, whose objects are the algebraic spaces étale over
`X_red`. Stacks 0DEG identifies that site with the category `C` whose objects are the morphisms
`φ : U ⟶ X` of formal algebraic spaces which are representable by algebraic spaces and étale.

The comparison functor is the one the source writes down: `(U ⟶ X) ↦ U ×_X X_red`. Here it is
built in the equivalent form `(U ⟶ X) ↦ (U_red ⟶ X_red)`, because the fibre product
`U ×_X X_red` *is* a reduction of `U` (Stacks 0GB7, available in this library as
`AlgebraicGeometry.FormalSpace.isReduction_pullback_reduction_of_smooth`, an étale morphism
being smooth), so a reduction of `U` exists as soon as one of `X` does, and the induced
morphism of reductions `U_red ⟶ X_red` is étale by Stacks 0DED. Functoriality is then the
functoriality of `AlgebraicGeometry.FormalSpace.Reduction.map`, and no naturality has to be
checked by hand.

## What is proved and what is assumed

Proved without hypotheses beyond the reduction of `X`:

* a formal algebraic space representable étale over `X` has a reduction, namely its fibre
  product with `X_red` over `X`, and the square exhibiting it is cartesian;
* the comparison functor `C ⥤ X_{spaces, étale}` exists.

Assumed, as the two explicit hypotheses `hhom` and `hess` of
`AlgebraicGeometry.FormalSpace.spacesEtaleComparison_isEquivalence`: that the comparison functor
is bijective on morphisms, and that every algebraic space étale over `X_red` is in its essential
image. These are exactly the two verifications the source omits — it says "we omit the
verification that `U_{V, ψ} ⟶ X` is representable by algebraic spaces and étale" and "we omit
the verification that the constructions are mutually inverse to each other". Stated in the
vocabulary of this file, what is needed is:

* **(hess)** for every algebraic space `V` over `S` and every étale morphism `ψ : V ⟶ X_red`,
  a formal algebraic space `U` over `S` and a morphism `φ : U ⟶ X` representable by algebraic
  spaces and étale, together with a reduction of `U` whose induced morphism to `X_red` is
  isomorphic to `ψ` over `X_red`. This is the source's construction of `U_{V, ψ}` as a
  functor on `(Sch/S)_{fppf}`, together with the omitted verification that it is representable
  by algebraic spaces and étale over `X`.
* **(hhom)** for `φ : U ⟶ X` and `φ' : U' ⟶ X` representable by algebraic spaces and étale,
  with `U` and `U'` formal algebraic spaces, the map from the morphisms `U ⟶ U'` over `X` to
  the morphisms `U_red ⟶ U'_red` over `X_red` is bijective. This is the lifting of morphisms
  along the thickening `X_red ⟶ X` against an étale target, i.e. the content of the source's
  "mutually inverse".

## The reduction is a given

The reduction of `X` is read as a *given*, bundled by
`AlgebraicGeometry.FormalSpace.Reduction`, exactly as in
`StacksFrontier/AlgebraicGeometry/FormalSpace/EtaleSite.lean`, where the sites of Stacks 0DEA are
defined; one always exists, by Stacks 0AIN —
`AlgebraicGeometry.FormalSpace.exists_isReduction_of_isFormalAlgebraicSpace`. The source
statement of Stacks 0DEG is about `X_{spaces, étale}`, which is defined only once a reduction
is given, so this is no weakening. The reduction of the objects of `C` is constructed here.

## Main definitions

* `AlgebraicGeometry.FormalSpace.RepresentableEtaleFormalSpacesOver` is the category of
  Stacks 0DEG: the formal algebraic spaces over `X` whose structure morphism is representable
  by algebraic spaces and étale, as a full subcategory of the slice of the fppf sheaves over
  `X`, so that its morphisms are the commuting triangles over `X`.
* `AlgebraicGeometry.FormalSpace.spacesEtaleComparison` is the comparison functor to
  `X_{spaces, étale}`, sending `φ : U ⟶ X` to the induced morphism of reductions.

## Main results

* `AlgebraicGeometry.FormalSpace.nonempty_reduction_of_isRepresentableEtale`: a formal
  algebraic space representable étale over `X` has a reduction.
* `AlgebraicGeometry.FormalSpace.isPullback_inclusion_liftSheafMap_map`: the reduction of such
  a space is the fibre product with `X_red`, which is the source's description of the
  comparison functor.
* `AlgebraicGeometry.FormalSpace.Reduction.iso_hom_comp_map`: the comparison functor does not
  depend on the choice of a reduction for each object.
* `AlgebraicGeometry.FormalSpace.essSurj_spacesEtaleComparison_of_exists_reduction` supplies
  the hypothesis `hess` below from a statement that does not mention the chosen reductions,
  which is the form the source's construction of `U_{V, ψ}` would produce.
* `AlgebraicGeometry.FormalSpace.spacesEtaleComparison_isEquivalence`: **Stacks 0DEG**, on the
  two hypotheses above.

## Implementation notes

The reduction of an object of `C` is produced from the fibre product `U ×_X X_red` by descending
its value universe: a formal algebraic space is a sheaf of `Type (u + 1)` while an algebraic
space is a presheaf of `Type u`, and
`AlgebraicGeometry.Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift` provides the
`Type u` model. The reduction condition is then not transported along the resulting isomorphism;
instead Stacks 0GB7 is applied a second time, to the cartesian square obtained from that
isomorphism, which avoids a transport lemma for
`AlgebraicGeometry.FormalSpace.IsReduction`.

The passage from "representable by algebraic spaces and étale" to the smoothness hypothesis of
Stacks 0GB7 is `hasPropertyULift_smooth_of_isRepresentableEtale`, an étale morphism of schemes
being smooth.

Which reduction of an object of `C` is used does not matter: any two are canonically isomorphic
by `AlgebraicGeometry.FormalSpace.Reduction.iso`, and the comparison functor is defined from a
choice of one for each object, made by `Classical.choice` because the statement proved here for
the objects of `C` is a `Nonempty`.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0DEA](https://stacks.math.columbia.edu/tag/0DEA)
* [Stacks Project, Tag 0DED](https://stacks.math.columbia.edu/tag/0DED)
* [Stacks Project, Tag 0DEG](https://stacks.math.columbia.edu/tag/0DEG)
* [Stacks Project, Tag 0GB7](https://stacks.math.columbia.edu/tag/0GB7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### From representable étale to representable smooth -/

/-- A morphism of fppf sheaves on the big fppf site of `S` which is representable by algebraic
spaces and étale is smooth in the sense of Stacks 03XZ, an étale morphism of schemes being
smooth. This is the hypothesis under which Stacks 0GB7 describes the reduction of the source. -/
private theorem hasPropertyULift_smooth_of_isRepresentableEtale {X Y : FppfSheaf B S hS}
    {f : X ⟶ Y} (hf : IsRepresentableEtale B S hS f) :
    Space.HasPropertyULift.{u + 1} B S hS (Space.smoothPropertyULift.{u + 1} B S hS)
      f.hom hf.1 := fun U ξ ↦
  holdsOnEveryEtaleChartULift_of_isEtaleULift_over_site B S hS
    (@AlgebraicGeometry.Smooth.{u} : MorphismProperty Scheme.{u})
    (fun k hk ↦ by have : Etale k := hk; infer_instance) _ (hf.2 U ξ)

/-! ### The reduction of a formal algebraic space representable étale over `X` -/

variable {B S hS}

/-- A formal algebraic space `U` over `S` carrying a morphism `φ : U ⟶ X` to a formal algebraic
space with a reduction, representable by algebraic spaces and étale, has a reduction itself: the
fibre product `U ×_X X_red` is one by Stacks 0GB7, an étale morphism being smooth, and its value
universe descends to that of the algebraic spaces.

This is how the objects of the category of Stacks 0DEG acquire the reductions that the
comparison functor is built from, directly from the given reduction of `X` rather than through
Stacks 0AIN. -/
theorem nonempty_reduction_of_isRepresentableEtale {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X) {U : FppfSheaf B S hS}
    (hU : IsFormalAlgebraicSpace B S hS U) {φ : U ⟶ X}
    (hφ : IsRepresentableEtale B S hS φ) : Nonempty (Reduction B S hS U) := by
  have hsmooth := hasPropertyULift_smooth_of_isRepresentableEtale B S hS hφ
  have key {W : FppfSheaf B S hS} {p : W ⟶ U} {q} (sq : IsPullback p q φ R.inclusion) :=
    isReduction_pullback_reduction_of_smooth B S hS hU hX hφ.1 hsmooth R.isReduction sq
  obtain ⟨F', hF', ⟨e⟩⟩ :=
    Space.exists_comp_uliftFunctor_iso_of_isAlgebraicSpaceULift B S hS
      (key (IsPullback.of_hasPullback φ R.inclusion)).algebraic
  set V : AlgebraicSpaces B S hS := ⟨F', hF'⟩
  set ê : liftSheaf B S hS V ≅ pullback φ R.inclusion := ObjectProperty.isoMk _ e
  have hsq : IsPullback (ê.hom ≫ pullback.fst φ R.inclusion)
      (ê.hom ≫ pullback.snd φ R.inclusion) φ R.inclusion :=
    IsPullback.of_iso_pullback
      ⟨by rw [Category.assoc, Category.assoc, pullback.condition]⟩ ê rfl rfl
  exact ⟨⟨V, ê.hom ≫ pullback.fst φ R.inclusion, key hsq⟩⟩

/-- The reduction of a formal algebraic space `U` representable étale over `X` is the fibre
product `U ×_X X_red`: the square formed by the inclusion of the reduction of `U`, the induced
morphism of reductions and the inclusion of the reduction of `X` is cartesian. This is the
description of the comparison functor that the source gives, `(U ⟶ X) ↦ U ×_X X_red`.

The comparison morphism from the reduction of `U` to the fibre product is an isomorphism by
Stacks 0GB7, the morphism being smooth as it is étale. -/
theorem isPullback_inclusion_liftSheafMap_map {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X) {U : FppfSheaf B S hS}
    (hU : IsFormalAlgebraicSpace B S hS U) {φ : U ⟶ X} (hφ : IsRepresentableEtale B S hS φ)
    (RU : Reduction B S hS U) :
    IsPullback RU.inclusion (liftSheafMap B S hS (RU.map R φ)) φ R.inclusion := by
  have hsmooth := hasPropertyULift_smooth_of_isRepresentableEtale B S hS hφ
  have sq : IsPullback (pullback.fst φ R.inclusion) (pullback.snd φ R.inclusion) φ
      R.inclusion := IsPullback.of_hasPullback φ R.inclusion
  have hw : liftSheafMap B S hS (RU.map R φ) ≫ R.inclusion = RU.inclusion ≫ φ :=
    RU.liftSheafMap_map R φ
  have hiso : IsIso (sq.lift RU.inclusion (liftSheafMap B S hS (RU.map R φ)) hw.symm) :=
    isIso_of_isReduction_of_isPullback_of_smooth B S hS hU hX hφ.1 hsmooth RU.isReduction
      R.isReduction sq (sq.lift_fst _ _ _)
  exact IsPullback.of_iso_pullback ⟨hw.symm⟩
    (asIso (sq.lift RU.inclusion (liftSheafMap B S hS (RU.map R φ)) hw.symm))
    (sq.lift_fst _ _ _) (sq.lift_snd _ _ _)

/-! ### Stacks 0DEG: the category of the formal algebraic spaces representable étale over `X` -/

/-- The objects of the category of Stacks 0DEG, as a property of the objects of the slice of the
fppf sheaves over `X`: a formal algebraic space over `S` whose structure morphism to `X` is
representable by algebraic spaces and étale. -/
abbrev IsRepresentableEtaleFormalSpaceOver (X : FppfSheaf B S hS) : ObjectProperty (Over X) :=
  fun U ↦ IsFormalAlgebraicSpace B S hS U.left ∧ IsRepresentableEtale B S hS U.hom

/-- The category of Stacks 0DEG: the morphisms `φ : U ⟶ X` of formal algebraic spaces over `S`
which are representable by algebraic spaces and étale. It is a full subcategory of the slice of
the fppf sheaves over `X`, so its morphisms are the commuting triangles over `X`, which is what
the source asks for. -/
abbrev RepresentableEtaleFormalSpacesOver (X : FppfSheaf B S hS) :=
  (IsRepresentableEtaleFormalSpaceOver X).FullSubcategory

/-- A reduction of an object of the category of Stacks 0DEG, chosen for each object. Any two
reductions are canonically isomorphic by `AlgebraicGeometry.FormalSpace.Reduction.iso`, so
nothing depends on the choice; it is made by `Classical.choice` because
`AlgebraicGeometry.FormalSpace.nonempty_reduction_of_isRepresentableEtale` is only an
existence statement. -/
def objReduction {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    (R : Reduction B S hS X) (U : RepresentableEtaleFormalSpacesOver X) :
    Reduction B S hS U.obj.left :=
  (nonempty_reduction_of_isRepresentableEtale hX R U.property.1 U.property.2).some

/-- The comparison functor of Stacks 0DEG, from the category of the formal algebraic spaces
representable étale over `X` to `X_{spaces, étale}`, which is the spaces-étale site of `X_red`
by Stacks 0DEA: it sends `φ : U ⟶ X` to the induced morphism of reductions `U_red ⟶ X_red`,
which is étale by Stacks 0DED and is the second projection of `U ×_X X_red ⟶ X_red` by
`AlgebraicGeometry.FormalSpace.isPullback_inclusion_liftSheafMap_map`, i.e. the functor the
source writes down.

Functoriality is the functoriality of `AlgebraicGeometry.FormalSpace.Reduction.map`: a triangle
over `X` induces a triangle over `X_red` by
`AlgebraicGeometry.FormalSpace.Reduction.map_comp`. -/
def spacesEtaleComparison {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    (R : Reduction B S hS X) : RepresentableEtaleFormalSpacesOver X ⥤ R.SpacesEtale where
  obj U := ⟨Over.mk ((objReduction hX R U).map R U.obj.hom),
    Reduction.isEtale_map U.property.1 hX (objReduction hX R U) R U.obj.hom
      U.property.2.1 U.property.2.2⟩
  map {U U'} f := ObjectProperty.homMk (Over.homMk
    ((objReduction hX R U).map (objReduction hX R U') f.hom.left)
    (show (objReduction hX R U).map (objReduction hX R U') f.hom.left ≫
          (objReduction hX R U').map R U'.obj.hom =
        (objReduction hX R U).map R U.obj.hom by
      rw [Reduction.map_comp, Over.w f.hom]))
  map_id U := by
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
    exact Reduction.map_id (objReduction hX R U)
  map_comp {U U' U''} f g := by
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
    exact (Reduction.map_comp (objReduction hX R U) (objReduction hX R U')
      (objReduction hX R U'') f.hom.left g.hom.left).symm

/-- The canonical isomorphism between two reductions of `U` commutes with the morphisms they
induce to the reduction of `X`, so the comparison functor does not depend on the choice of a
reduction for each object. -/
theorem Reduction.iso_hom_comp_map {X U : FppfSheaf B S hS} (RU RU' : Reduction B S hS U)
    (R : Reduction B S hS X) (φ : U ⟶ X) :
    (RU.iso RU').hom ≫ RU'.map R φ = RU.map R φ := by
  have hmap := Reduction.map_comp RU RU' R (𝟙 U) φ
  rwa [Category.id_comp] at hmap

/-- Essential surjectivity of the comparison functor in a form that does not mention the chosen
reductions: it suffices that every object `ψ : V ⟶ X_red` of `X_{spaces, étale}` be, up to
isomorphism over `X_red`, the morphism of reductions induced by some morphism `φ : U ⟶ X` of
formal algebraic spaces which is representable by algebraic spaces and étale. This is the shape
in which the source's construction of the quasi-inverse `U_{V, ψ}` would supply the hypothesis
`hess` of `AlgebraicGeometry.FormalSpace.spacesEtaleComparison_isEquivalence`. -/
theorem essSurj_spacesEtaleComparison_of_exists_reduction {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X)
    (h : ∀ V : R.SpacesEtale, ∃ (U : FppfSheaf B S hS) (φ : U ⟶ X)
      (_ : IsFormalAlgebraicSpace B S hS U) (_ : IsRepresentableEtale B S hS φ)
      (RU : Reduction B S hS U) (e : RU.space ≅ V.obj.left),
      e.hom ≫ V.obj.hom = RU.map R φ) :
    (spacesEtaleComparison hX R).EssSurj where
  mem_essImage V := by
    obtain ⟨U, φ, hU, hφ, RU, e, he⟩ := h V
    refine ⟨⟨Over.mk φ, hU, hφ⟩, ⟨ObjectProperty.isoMk _ (Over.isoMk
      (show ((spacesEtaleComparison hX R).obj ⟨Over.mk φ, hU, hφ⟩).obj.left ≅ V.obj.left from
        (objReduction hX R ⟨Over.mk φ, hU, hφ⟩).iso RU ≪≫ e) ?_)⟩⟩
    change (((objReduction hX R ⟨Over.mk φ, hU, hφ⟩).iso RU).hom ≫ e.hom) ≫ V.obj.hom =
      (objReduction hX R ⟨Over.mk φ, hU, hφ⟩).map R φ
    rw [Category.assoc, he]
    exact Reduction.iso_hom_comp_map _ RU R φ

/-- The comparison functor from the category of the formal algebraic spaces representable étale
over a formal algebraic space `X` to `X_{spaces, étale}` is an equivalence of categories.

Two hypotheses are carried, and they are exactly the two verifications the source omits.
`hhom` is bijectivity on morphisms, which is the source's "we omit the verification that the
constructions are mutually inverse to each other": it amounts to lifting a morphism over `X`
along the thickening `X_red ⟶ X` against an étale target. `hess` is essential surjectivity,
which is the source's construction of the quasi-inverse `U_{V, ψ}` together with its "we omit
the verification that `U_{V, ψ} ⟶ X` is representable by algebraic spaces and étale". The
reduction of `X` is a given as well, which is no weakening: `X_{spaces, étale}` is defined, in
Stacks 0DEA, only for a formal algebraic space with a given reduction, and Stacks 0AIN supplies
one. -/
@[stacks 0DEG "the equivalence; bijectivity on morphisms and essential surjectivity — the two
  verifications the source omits — are hypotheses, and the equivalence is read against a given
  reduction of `X`, which Stacks 0AIN supplies"]
theorem spacesEtaleComparison_isEquivalence {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) (R : Reduction B S hS X)
    (hhom : ∀ U U' : RepresentableEtaleFormalSpacesOver X,
      Function.Bijective fun f : U ⟶ U' ↦ (spacesEtaleComparison hX R).map f)
    (hess : ∀ V : R.SpacesEtale, ∃ U : RepresentableEtaleFormalSpacesOver X,
      Nonempty ((spacesEtaleComparison hX R).obj U ≅ V)) :
    (spacesEtaleComparison hX R).IsEquivalence where
  faithful := ⟨fun {U U'} ↦ (hhom U U').1⟩
  full := ⟨fun {U U'} ↦ (hhom U U').2⟩
  essSurj := ⟨hess⟩

end AlgebraicGeometry.FormalSpace

end
