module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.ResidueField.Basic

/-!
# Change of field for the predeformation category of a point

Let `x₀` be an object of a category `𝒳` over the schemes over `S` lying over `Spec k`, let `l/k`
be a finite extension of the residue field, and let `x_{l,0}` be a restriction of `x₀` to
`Spec l`. An object of the category `(𝓕_{𝒳,k,x₀})_{l/k}` obtained from the predeformation
category of `x₀` by change of residue field is a deformation of `x₀` over `A ×_l k`, for `A` an
Artinian local `Λ`-algebra with residue field `l`; restricting it along `Spec A ⟶ Spec (A ×_l k)`
gives a deformation of `x_{l,0}` over `A`. This file builds the resulting canonical functor
`(𝓕_{𝒳,k,x₀})_{l/k} ⥤ 𝓕_{𝒳,l,x_{l,0}}` over `𝒞_{Λ,l}`.

## Main definitions

* `Deformation.Artin.changeOfFieldMap` — the first projection `A ×_l k ⟶ A`, transported along an
  identification of the base of a deformation with a comparison algebra.
* `Deformation.Artin.changeOfFieldRestriction` — the restricting arrow of `𝒳`, a chosen cartesian
  arrow over `Spec A ⟶ Spec (A ×_l k)`.
* `Deformation.Artin.restrictionDeformation` — the restricted deformation of `x_{l,0}`.
* `Deformation.Artin.changeOfFieldFunctor` — the canonical functor.

## Main results

* `Deformation.Artin.changeOfFieldFunctor_objects` and
  `Deformation.Artin.changeOfFieldFunctor_morphisms` describe the functor on objects and on
  morphisms, so that it is the canonical one and not an arbitrary functor.
* `Deformation.Artin.changeOfFieldFunctor_projection_comm` — the functor lies over `𝒞_{Λ,l}`.

## Implementation notes

The ambient base category is the category `Over S` of all schemes over `S`, which is the one the
predeformation category of Tag 07T4 is built over, and the restriction is taken with respect to a
choice of pullbacks for the functor to `Over S`: this is the pullback functor the source chooses.
Only the fact that the arrow `x_{l,0} ⟶ x₀` lies over `Spec l ⟶ Spec k` is used, so `x_{l,0}` is
not required to be a cartesian restriction of `x₀`.

The square of rings `l`, `A`, `k`, `A ×_l k` is a fibre product by construction of the comparison
functor of Tag 07W8; the two commutation identities it yields,
`Deformation.Artin.changeOfFieldMap_comp_algebraMap` and
`Deformation.Artin.residueMap_comp_changeOfFieldMap`, are the only ring-theoretic input, and the
rest of the construction is the universal property of a strongly cartesian arrow.

Both predeformation categories are described through the characterizing structure
`Deformation.Artin.PredeformationConstruction`, so the construction uses only the interface of
Tag 07T4 and not the particular model built there. That the two categories are cofibred in
groupoids over `𝒞_{Λ,l}` is `Deformation.changeOfFieldsProjection_isCofiberedInGroupoids` on the
source side and `Deformation.Artin.predeformationCategory_isPredeformationCategory` on the target
side; what is added here is the functor between them over `𝒞_{Λ,l}`.

### No unrestricted `@[stacks 07WX]`

One restriction is recorded in the attribute strings: the hypothesis is that `𝒳` is fibred in
groupoids over the category of *all* `S`-schemes (a choice of pullbacks for `q : 𝒳 ⥤ Over S`),
whereas the source asks only that `𝒳` be fibred in groupoids over the big fppf site
`(Sch/S)_{fppf}`. Transporting the construction to the site requires placing `Spec A` in the
chosen site, which is where the finite-type hypotheses on `k` of Tags 07T3 and 07WP enter.

That is not a deferred step but a different hypothesis. A site-fibred category presents itself
over the category of all `S`-schemes as `p ⋙ Over.post B.inclusion`, and
`Deformation.Artin.not_isFiberedInGroupoids_comp_post` in
`StacksFrontier/Deformation/Artin/ChangeOfField/SiteFibrednessObstruction.lean` shows that composite
is never fibred in groupoids over `Over S`, while
`Deformation.Artin.not_nonempty_choiceOfPullbacks_comp_post` shows it has no choice of pullbacks
there. Since `changeOfFieldFunctor` below is parameterized by such a choice of pullbacks, it has
no site-presented instance, and the construction has to be re-derived over the site rather than
transported.

That re-derivation is `StacksFrontier/Deformation/Artin/ChangeOfField/SiteRestriction.lean`, which
carries Tag 07WX with no restriction: `Deformation.Artin.Site.changeOfFieldFunctor` and
`Deformation.Artin.Site.changeOfFieldFunctor_isEquivalence` take a category fibred in groupoids
over the big fppf site and condition (RS) in the site form `Deformation.Artin.SatisfiesRS` of
Tag 07WP, and produce the cartesian arrows inside the site. The construction below is the same
mathematics over the category of all `S`-schemes, and the two share the predeformation categories
of Tag 07T4.

The second assertion of the source — that the functor is an equivalence when `𝒳` satisfies (RS)
— is `Deformation.Artin.changeOfFieldFunctor_isEquivalence` in
`StacksFrontier/Deformation/Artin/ChangeOfField/Equivalence.lean`. It uses condition (RS) in the
form `Deformation.Artin.SatisfiesRSOver` matching the ambient category above, rather than the
site form `Deformation.Artin.SatisfiesRS` of Tag 07WP; its geometric input, that
`Spec (A ×_l k)` is the pushout of `Spec k` and `Spec A` along `Spec l`, is
`Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective` (Tag 0ET0), the residue map
`A ⟶ l` being surjective.

## References

* [Stacks Project, Tag 07WX](https://stacks.math.columbia.edu/tag/07WX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing

namespace Deformation.Artin

universe u v w

-- `Fiber` and `Fiber.fiberInclusion` are plain `def`s, so goals mentioning an object of a fibre
-- or its image in `𝒳` are not type-correct at `implicit` transparency.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

/-! ### The ring map underlying a change of field -/

section AlgebraMap

variable (T : Deformation.ChangeOfFieldsSituation.{u, u, u})
  {A : ArtinianLocalAlgCat.{u, u, u} T.Λ T.k} {C C' : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}

/-- The first projection `A ×_l k ⟶ A` of a comparison algebra, pulled back along an
identification `e` of the base of a deformation with that comparison algebra. -/
public def changeOfFieldMap
    (e : A ⟶ (Deformation.comparisonFunctor T).functor.obj C) : A →+* C :=
  (RingHom.pullbackFst (Deformation.residueMap T C) (algebraMap T.k T.l)).comp
    (((Deformation.comparisonFunctor T).pullbackEquiv C).toRingHom.comp e.hom.toRingHom)

/-- The change-of-field map sends `a` to the first component of the image of `a` in the fibre
product `C ×_l k`. -/
theorem changeOfFieldMap_apply
    (e : A ⟶ (Deformation.comparisonFunctor T).functor.obj C) (a : A) :
    changeOfFieldMap T e a =
      (((Deformation.comparisonFunctor T).pullbackEquiv C) (e.hom a)).val.1 := rfl

/-- The change-of-field map is a map of `Λ`-algebras. -/
theorem changeOfFieldMap_comp_algebraMap
    (e : A ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    (changeOfFieldMap T e).comp (algebraMap T.Λ A) = algebraMap T.Λ C := by
  ext a
  show (((Deformation.comparisonFunctor T).pullbackEquiv C)
    (e.hom (algebraMap T.Λ A a))).val.1 = _
  rw [e.hom.commutes a]
  exact (Deformation.comparisonFunctor T).algebraMap_fst C a

/-- The residue map of an object of `𝒞_{Λ,l}` is a map of `Λ`-algebras. -/
theorem residueMap_comp_algebraMap :
    (Deformation.residueMap T C).comp (algebraMap T.Λ C) = algebraMap T.Λ T.l := by
  ext a
  show C.residueEquiv (residue C (algebraMap T.Λ C a)) = algebraMap T.Λ T.l a
  calc
    C.residueEquiv (residue C (algebraMap T.Λ C a)) =
        C.residueEquiv (algebraMap C (ResidueField C) (algebraMap T.Λ C a)) := by
      rw [ResidueField.algebraMap_eq]
    _ = C.residueEquiv (algebraMap T.Λ (ResidueField C) a) := by
      rw [IsScalarTower.algebraMap_apply T.Λ C (ResidueField C) a]
    _ = algebraMap T.Λ T.l a := C.residueEquiv.commutes a

/-- The change of field is compatible with the residue maps: the square of `Spec`'s of
`l`, `A`, `k` and `A ×_l k` commutes. -/
theorem residueMap_comp_changeOfFieldMap
    (e : A ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    (Deformation.residueMap T C).comp (changeOfFieldMap T e) =
      (algebraMap T.k T.l).comp (residueMap A) := by
  ext a
  have hsnd : (((Deformation.comparisonFunctor T).pullbackEquiv C) (e.hom a)).val.2 =
      residueMap A a :=
    ((Deformation.comparisonFunctor T).residue_snd C (e.hom a)).symm.trans (e.residue_comm a)
  have hprop : Deformation.residueMap T C
      (((Deformation.comparisonFunctor T).pullbackEquiv C) (e.hom a)).val.1 =
      algebraMap T.k T.l
        (((Deformation.comparisonFunctor T).pullbackEquiv C) (e.hom a)).val.2 :=
    (((Deformation.comparisonFunctor T).pullbackEquiv C) (e.hom a)).property
  show Deformation.residueMap T C
      (((Deformation.comparisonFunctor T).pullbackEquiv C) (e.hom a)).val.1 = _
  rw [hprop, hsnd]
  rfl

/-- A morphism of `𝒞_{Λ,l}` is compatible with the residue maps. -/
theorem residueMap_comp_hom (h : C ⟶ C') :
    (Deformation.residueMap T C').comp h.hom.toRingHom = Deformation.residueMap T C := by
  ext a
  exact h.residue_comm a

/-- The change-of-field maps are natural in the deformation and the algebra. -/
theorem changeOfFieldMap_naturality {A' : ArtinianLocalAlgCat.{u, u, u} T.Λ T.k}
    (e : A ⟶ (Deformation.comparisonFunctor T).functor.obj C)
    (e' : A' ⟶ (Deformation.comparisonFunctor T).functor.obj C')
    (g : A ⟶ A') (h : C ⟶ C')
    (hcomm : g ≫ e' = e ≫ (Deformation.comparisonFunctor T).functor.map h) :
    (changeOfFieldMap T e').comp g.hom.toRingHom =
      h.hom.toRingHom.comp (changeOfFieldMap T e) := by
  ext a
  have hstep : e'.hom (g.hom a) =
      ((Deformation.comparisonFunctor T).functor.map h).hom (e.hom a) :=
    congrArg (fun m : A ⟶ (Deformation.comparisonFunctor T).functor.obj C' => m.hom a) hcomm
  show (((Deformation.comparisonFunctor T).pullbackEquiv C') (e'.hom (g.hom a))).val.1 = _
  rw [hstep]
  exact (Deformation.comparisonFunctor T).map_fst h (e.hom a)

end AlgebraMap

/-! ### Reading a morphism off a conjugated equation -/

section Transport

variable {C : Type*} [Category C]

/-- Reading off a morphism from a conjugated equation. -/
theorem eq_of_eqToHom_conj {W W' Z Z' : C} (hW : W = W') (hZ : Z = Z') {f : W ⟶ Z}
    {g : W' ⟶ Z'} (h : eqToHom hW.symm ≫ f ≫ eqToHom hZ = g) :
    f = eqToHom hW ≫ g ≫ eqToHom hZ.symm := by
  subst hW
  subst hZ
  simpa using h

end Transport

/-! ### Restriction of a deformation along a finite extension of the residue field -/

section Restriction

variable (T : Deformation.ChangeOfFieldsSituation.{u, u, u})
variable {S : Scheme.{u}} (iΛ : Spec (.of T.Λ) ⟶ S)
variable {X : Type v} [Category.{w} X] {q : X ⥤ Over S}
variable {x₀ xₗ : X}
variable {hx₀ : q.obj x₀ = Over.mk
  (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ)}
variable (hxₗ : q.obj xₗ = Over.mk
  (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ))

/-- The structure map of `Spec (A ×_l k)` factors the structure map of `Spec A`. -/
theorem specMap_changeOfFieldMap_comp
    {A : ArtinianLocalAlgCat.{u, u, u} T.Λ T.k} {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : A ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    Spec.map (CommRingCat.ofHom (changeOfFieldMap T e)) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ A)) ≫ iΛ) =
      Spec.map (CommRingCat.ofHom (algebraMap T.Λ C)) ≫ iΛ := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    changeOfFieldMap_comp_algebraMap]

/-- The structure map of `Spec l` factors through the structure map of `Spec C`. -/
theorem specMap_residueMap_comp (C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l) :
    Spec.map (CommRingCat.ofHom (Deformation.residueMap T C)) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ C)) ≫ iΛ) =
      Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    residueMap_comp_algebraMap]

/-- The base map `Spec C ⟶ Spec A` of the restriction, as an arrow of `Over S` into the image of
the deformed point. -/
def changeOfFieldRestrictionBaseMap (d : DeformationObject iΛ q x₀ hx₀)
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : d.algebra ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ C)) ≫ iΛ) : Over S) ⟶
      q.obj d.point :=
  Over.homMk (V := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ d.algebra)) ≫ iΛ))
      (Spec.map (CommRingCat.ofHom (changeOfFieldMap T e)))
      (specMap_changeOfFieldMap_comp T iΛ e) ≫ eqToHom d.base.symm

/-- The underlying morphism of schemes of the base map of the restriction is the spectrum of the
change-of-field map. -/
theorem restrictionBaseMap_left (d : DeformationObject iΛ q x₀ hx₀)
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : d.algebra ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    (changeOfFieldRestrictionBaseMap T iΛ d e).left =
      Spec.map (CommRingCat.ofHom (changeOfFieldMap T e)) ≫
        eqToHom (congrArg Over.left d.base).symm := by
  simp [changeOfFieldRestrictionBaseMap]

/-- The arrow `Spec l ⟶ Spec C` over `S` through which the distinguished point of the restricted
deformation category maps. -/
def restrictionResidueMap (C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l) :
    q.obj xₗ ⟶ (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ C)) ≫ iΛ) : Over S) :=
  eqToHom hxₗ ≫ Over.homMk (Spec.map (CommRingCat.ofHom (Deformation.residueMap T C)))
    (specMap_residueMap_comp T iΛ C)

/-- The underlying morphism of schemes of the distinguished arrow from `Spec l` is the spectrum
of the residue map. -/
theorem restrictionResidueMap_left (C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l) :
    (restrictionResidueMap T iΛ hxₗ C).left =
      eqToHom (congrArg Over.left hxₗ) ≫
        Spec.map (CommRingCat.ofHom (Deformation.residueMap T C)) := by
  simp [restrictionResidueMap]

variable {η : xₗ ⟶ x₀}
variable (hη : eqToHom (congrArg Over.left hxₗ).symm ≫ (q.map η).left ≫
  eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
variable (c : q.ChoiceOfPullbacks)

/-- The chosen residue map of an object of `𝒞_{Λ,l}` is the residue map used by the
predeformation category over `l`. -/
theorem deformation_residueMap_eq (C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l) :
    Deformation.residueMap T C = residueMap C := rfl

/-- The square of spectra of `l`, `C`, `k` and `A` attached to a change of field commutes. -/
@[reassoc]
theorem specMap_changeOfFieldMap_square (A : ArtinianLocalAlgCat.{u, u, u} T.Λ T.k)
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : A ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)) ≫
        Spec.map (CommRingCat.ofHom (residueMap A)) =
      Spec.map (CommRingCat.ofHom (Deformation.residueMap T C)) ≫
        Spec.map (CommRingCat.ofHom (changeOfFieldMap T e)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    residueMap_comp_changeOfFieldMap]

/-- The point of the restricted deformation: the chosen pullback of the deformed point along
`Spec C ⟶ Spec A`. -/
def restrictionFiberObj (d : DeformationObject iΛ q x₀ hx₀)
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : d.algebra ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    q.Fiber (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ C)) ≫ iΛ)) :=
  c.obj (changeOfFieldRestrictionBaseMap T iΛ d e) ⟨d.point, rfl⟩

/-- The restricting arrow of `𝒳`: the chosen cartesian arrow over `Spec C ⟶ Spec A`. -/
def changeOfFieldRestriction (d : DeformationObject iΛ q x₀ hx₀)
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : d.algebra ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    (restrictionFiberObj T iΛ c d e).val ⟶ d.point :=
  c.map (changeOfFieldRestrictionBaseMap T iΛ d e) ⟨d.point, rfl⟩

/-- The restricting arrow is strongly cartesian over the base map of the restriction. -/
theorem changeOfFieldRestriction_isStronglyCartesian (d : DeformationObject iΛ q x₀ hx₀)
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : d.algebra ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    q.IsStronglyCartesian (changeOfFieldRestrictionBaseMap T iΛ d e)
      (changeOfFieldRestriction T iΛ c d e) :=
  c.isStronglyCartesian _ _

/-- Two arrows into the restricted point lying over the same arrow of `Over S` are equal if they
agree after the restricting arrow. -/
private theorem restriction_arrow_ext (d : DeformationObject iΛ q x₀ hx₀)
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : d.algebra ⟶ (Deformation.comparisonFunctor T).functor.obj C) {y : X}
    {φ : q.obj y ⟶ (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ C)) ≫ iΛ) : Over S)}
    {f f' : y ⟶ (restrictionFiberObj T iΛ c d e).val} (hf : q.IsHomLift φ f)
    (hf' : q.IsHomLift φ f')
    (h : f ≫ changeOfFieldRestriction T iΛ c d e = f' ≫ changeOfFieldRestriction T iΛ c d e) :
    f = f' :=
  haveI := changeOfFieldRestriction_isStronglyCartesian T iΛ c d e
  Functor.IsStronglyCartesian.ext q (changeOfFieldRestrictionBaseMap T iΛ d e)
    (changeOfFieldRestriction T iΛ c d e) φ h

include hη in
/-- The arrow from the distinguished point to a deformation, read through the restriction. -/
theorem restriction_base_fac (d : DeformationObject iΛ q x₀ hx₀)
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : d.algebra ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    q.map (η ≫ d.arrow) =
      restrictionResidueMap T iΛ hxₗ C ≫ changeOfFieldRestrictionBaseMap T iΛ d e := by
  apply Over.OverMorphism.ext
  have hη' := eq_of_eqToHom_conj (congrArg Over.left hxₗ) (congrArg Over.left hx₀) hη
  have hd := eq_of_eqToHom_conj (congrArg Over.left hx₀) (congrArg Over.left d.base) d.arrow_base
  rw [q.map_comp, Over.comp_left, Over.comp_left, restrictionBaseMap_left,
    restrictionResidueMap_left, hη', hd]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    ← specMap_changeOfFieldMap_square_assoc]

include hη in
/-- The arrow of the restricted deformation, obtained from the universal property of the
restricting arrow. -/
def changeOfFieldArrow (d : DeformationObject iΛ q x₀ hx₀)
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : d.algebra ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    xₗ ⟶ (restrictionFiberObj T iΛ c d e).val :=
  haveI := changeOfFieldRestriction_isStronglyCartesian T iΛ c d e
  Functor.IsStronglyCartesian.map q (changeOfFieldRestrictionBaseMap T iΛ d e)
    (changeOfFieldRestriction T iΛ c d e)
    (restriction_base_fac T iΛ hxₗ hη d e) (η ≫ d.arrow)

include hη in
/-- The arrow of the restricted deformation lies over the distinguished arrow from `Spec l`. -/
theorem changeOfFieldArrow_isHomLift (d : DeformationObject iΛ q x₀ hx₀)
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : d.algebra ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    q.IsHomLift (restrictionResidueMap T iΛ hxₗ C)
      (changeOfFieldArrow T iΛ hxₗ hη c d e) :=
  have := changeOfFieldRestriction_isStronglyCartesian T iΛ c d e
  Functor.IsStronglyCartesian.map_isHomLift q _ _ _ _

include hη in
/-- The arrow of the restricted deformation, followed by the restricting arrow, is the composite
of `η` with the arrow of the given deformation. -/
theorem changeOfFieldArrow_fac (d : DeformationObject iΛ q x₀ hx₀)
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : d.algebra ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    changeOfFieldArrow T iΛ hxₗ hη c d e ≫
        changeOfFieldRestriction T iΛ c d e = η ≫ d.arrow :=
  have := changeOfFieldRestriction_isStronglyCartesian T iΛ c d e
  Functor.IsStronglyCartesian.fac q _ _ _ _

include hη in
/-- The image in `Over S` of the arrow of the restricted deformation is the distinguished arrow
from `Spec l`, up to the identification of the base of the restricted point. -/
theorem changeOfFieldArrow_map (d : DeformationObject iΛ q x₀ hx₀)
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : d.algebra ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    q.map (changeOfFieldArrow T iΛ hxₗ hη c d e) =
      restrictionResidueMap T iΛ hxₗ C ≫
        eqToHom (restrictionFiberObj T iΛ c d e).property.symm := by
  have := changeOfFieldArrow_isHomLift T iΛ hxₗ hη c d e
  rw [CategoryTheory.IsHomLift.fac' q (restrictionResidueMap T iΛ hxₗ C)
    (changeOfFieldArrow T iΛ hxₗ hη c d e)]
  simp

include hη in
/-- The restriction of a deformation of `x₀` over `A ×_l k` to a deformation of `x_{l,0}`
over `A`. -/
@[implicit_reducible]
def restrictionDeformation (d : DeformationObject iΛ q x₀ hx₀)
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : d.algebra ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    DeformationObject iΛ q xₗ hxₗ where
  algebra := C
  point := (restrictionFiberObj T iΛ c d e).val
  arrow := changeOfFieldArrow T iΛ hxₗ hη c d e
  base := (restrictionFiberObj T iΛ c d e).property
  arrow_base := by
    have := changeOfFieldArrow_isHomLift T iΛ hxₗ hη c d e
    have hfac := CategoryTheory.IsHomLift.fac' q (restrictionResidueMap T iΛ hxₗ C)
      (changeOfFieldArrow T iΛ hxₗ hη c d e)
    rw [hfac]
    simp [Over.comp_left, restrictionResidueMap_left, deformation_residueMap_eq]

include hη in
/-- The restricted deformation lies over the algebra `C`. -/
@[simp]
theorem restrictionDeformation_algebra (d : DeformationObject iΛ q x₀ hx₀)
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : d.algebra ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    (restrictionDeformation T iΛ hxₗ hη c d e).algebra = C := rfl

include hη in
/-- The point of the restricted deformation is the chosen pullback of the deformed point. -/
@[simp]
theorem restrictionDeformation_point (d : DeformationObject iΛ q x₀ hx₀)
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : d.algebra ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    (restrictionDeformation T iΛ hxₗ hη c d e).point =
      (restrictionFiberObj T iΛ c d e).val := rfl

include hη in
/-- The arrow of the restricted deformation is `changeOfFieldArrow`. -/
@[simp]
theorem restrictionDeformation_arrow (d : DeformationObject iΛ q x₀ hx₀)
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : d.algebra ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    (restrictionDeformation T iΛ hxₗ hη c d e).arrow =
      changeOfFieldArrow T iΛ hxₗ hη c d e := rfl

/-- The structure map of `Spec C'` factors through a morphism `C ⟶ C'` of `𝒞_{Λ,l}`. -/
theorem specMap_hom_comp {C C' : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l} (h : C ⟶ C') :
    Spec.map (CommRingCat.ofHom h.hom.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap T.Λ C)) ≫ iΛ) =
      Spec.map (CommRingCat.ofHom (algebraMap T.Λ C')) ≫ iΛ := by
  have hcomm : h.hom.toRingHom.comp (algebraMap T.Λ C) = algebraMap T.Λ C' :=
    RingHom.ext fun a => h.hom.commutes a
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomm]

/-- The spectrum of a morphism of `𝒞_{Λ,l}`, as an arrow of `Over S`. -/
def algebraBaseMap {C C' : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l} (h : C ⟶ C') :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ C')) ≫ iΛ) : Over S) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ C)) ≫ iΛ) :=
  Over.homMk (Spec.map (CommRingCat.ofHom h.hom.toRingHom)) (specMap_hom_comp T iΛ h)

/-- The underlying morphism of schemes of `algebraBaseMap` is the spectrum of the ring map. -/
@[simp]
theorem algebraBaseMap_left {C C' : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l} (h : C ⟶ C') :
    (algebraBaseMap T iΛ h).left = Spec.map (CommRingCat.ofHom h.hom.toRingHom) := rfl

/-- The spectrum of an identity morphism of `𝒞_{Λ,l}` is an identity. -/
@[simp]
theorem algebraBaseMap_id (C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l) :
    algebraBaseMap T iΛ (𝟙 C) =
      𝟙 (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap T.Λ C)) ≫ iΛ) : Over S) := by
  apply Over.OverMorphism.ext
  rw [algebraBaseMap_left]
  show Spec.map (CommRingCat.ofHom (RingHom.id C)) = _
  rw [CommRingCat.ofHom_id, Spec.map_id]
  rfl

/-- The spectrum of a composite of morphisms of `𝒞_{Λ,l}` is the composite in the reverse order. -/
theorem algebraBaseMap_comp {C C' C'' : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (h : C ⟶ C') (h' : C' ⟶ C'') :
    algebraBaseMap T iΛ (h ≫ h') = algebraBaseMap T iΛ h' ≫ algebraBaseMap T iΛ h := by
  apply Over.OverMorphism.ext
  rw [algebraBaseMap_left, Over.comp_left, algebraBaseMap_left, algebraBaseMap_left,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The distinguished arrow from `Spec l` is compatible with change of the base algebra. -/
@[reassoc]
theorem restrictionResidueMap_comp {C C' : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l} (h : C ⟶ C') :
    restrictionResidueMap T iΛ hxₗ C' ≫ algebraBaseMap T iΛ h =
      restrictionResidueMap T iΛ hxₗ C := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, algebraBaseMap_left, restrictionResidueMap_left,
    restrictionResidueMap_left, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    residueMap_comp_hom]

/-- The restricting arrow lies over the base map of the restriction. -/
theorem changeOfFieldRestriction_map (d : DeformationObject iΛ q x₀ hx₀)
    {C : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : d.algebra ⟶ (Deformation.comparisonFunctor T).functor.obj C) :
    q.map (changeOfFieldRestriction T iΛ c d e) =
      eqToHom (restrictionFiberObj T iΛ c d e).property ≫
        changeOfFieldRestrictionBaseMap T iΛ d e := by
  have := changeOfFieldRestriction_isStronglyCartesian T iΛ c d e
  have hfac := CategoryTheory.IsHomLift.fac' q (changeOfFieldRestrictionBaseMap T iΛ d e)
    (changeOfFieldRestriction T iΛ c d e)
  rw [hfac]
  simp

/-- The naturality square of the change-of-field maps, read on spectra. -/
@[reassoc]
theorem specMap_changeOfFieldMap_naturality
    {A A' : ArtinianLocalAlgCat.{u, u, u} T.Λ T.k}
    {C C' : ArtinianLocalAlgCat.{u, u, u} T.Λ T.l}
    (e : A ⟶ (Deformation.comparisonFunctor T).functor.obj C)
    (e' : A' ⟶ (Deformation.comparisonFunctor T).functor.obj C')
    (g : A ⟶ A') (h : C ⟶ C')
    (hcomm : g ≫ e' = e ≫ (Deformation.comparisonFunctor T).functor.map h) :
    Spec.map (CommRingCat.ofHom (changeOfFieldMap T e')) ≫
        Spec.map (CommRingCat.ofHom g.hom.toRingHom) =
      Spec.map (CommRingCat.ofHom h.hom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (changeOfFieldMap T e)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    changeOfFieldMap_naturality T e e' g h hcomm]

end Restriction

/-! ### The canonical functor -/

section Functor

variable (T : Deformation.ChangeOfFieldsSituation.{u, u, u})
variable {S : Scheme.{u}} (iΛ : Spec (.of T.Λ) ⟶ S)
variable {X : Type v} [Category.{w} X] {q : X ⥤ Over S}
variable {x₀ xₗ : X}
variable {hx₀ : q.obj x₀ = Over.mk
  (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ)}
variable (hxₗ : q.obj xₗ = Over.mk
  (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ))
variable {η : xₗ ⟶ x₀}
variable (hη : eqToHom (congrArg Over.left hxₗ).symm ≫ (q.map η).left ≫
  eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
variable (c : q.ChoiceOfPullbacks)
variable (D : PredeformationConstruction iΛ q x₀ hx₀)

/-- The category structure on the carrier of the predeformation category of `x₀`. -/
local instance : Category.{max u w} D.carrier := D.category

/-- The identification of the base of the deformation underlying an object of the
change-of-fields category with the corresponding comparison algebra. -/
def changeOfFieldIso (a : Deformation.ChangeOfFieldsCategory T D.projection) :
    (D.objects a.fst).algebra ⟶ (Deformation.comparisonFunctor T).functor.obj a.snd :=
  eqToHom (D.object_projection a.fst).symm ≫ a.iso.hom

/-- The identifications `changeOfFieldIso` are natural with respect to morphisms of the
change-of-fields category. -/
theorem changeOfFieldIso_naturality
    {a b : Deformation.ChangeOfFieldsCategory T D.projection} (f : a ⟶ b) :
    (D.morphisms a.fst b.fst f.fst).ringHom ≫ changeOfFieldIso T iΛ D b =
      changeOfFieldIso T iΛ D a ≫
        (Deformation.comparisonFunctor T).functor.map f.snd := by
  rw [← D.morphism_projection f.fst]
  simp only [changeOfFieldIso, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  rw [f.w]

/-- The restricting arrow of the source of a morphism, composed with the reversed arrow of that
morphism, lies over the base map of the restricting arrow of its target. -/
theorem changeOfFieldMorphism_base_fac
    {a b : Deformation.ChangeOfFieldsCategory T D.projection} (f : a ⟶ b) :
    q.map (changeOfFieldRestriction T iΛ c (D.objects b.fst) (changeOfFieldIso T iΛ D b) ≫
        (D.morphisms a.fst b.fst f.fst).arrow) =
      (eqToHom (restrictionFiberObj T iΛ c (D.objects b.fst)
            (changeOfFieldIso T iΛ D b)).property ≫ algebraBaseMap T iΛ f.snd) ≫
        changeOfFieldRestrictionBaseMap T iΛ (D.objects a.fst) (changeOfFieldIso T iΛ D a) := by
  apply Over.OverMorphism.ext
  have hm := eq_of_eqToHom_conj (congrArg Over.left (D.objects b.fst).base)
    (congrArg Over.left (D.objects a.fst).base) (D.morphisms a.fst b.fst f.fst).arrow_base
  rw [q.map_comp, changeOfFieldRestriction_map]
  simp only [Over.comp_left, Over.eqToHom_left, restrictionBaseMap_left, algebraBaseMap_left,
    Category.assoc]
  rw [hm]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [specMap_changeOfFieldMap_naturality_assoc T (changeOfFieldIso T iΛ D a)
    (changeOfFieldIso T iΛ D b) (D.morphisms a.fst b.fst f.fst).ringHom f.snd
    (changeOfFieldIso_naturality T iΛ D f)]

/-- The reversed arrow of `𝒳` underlying the image of a morphism of the change-of-fields
category: the unique lift of the base map of `𝒞_{Λ,l}` through the restricting arrow. -/
def changeOfFieldMorphismArrow
    {a b : Deformation.ChangeOfFieldsCategory T D.projection} (f : a ⟶ b) :
    (restrictionFiberObj T iΛ c (D.objects b.fst) (changeOfFieldIso T iΛ D b)).val ⟶
      (restrictionFiberObj T iΛ c (D.objects a.fst) (changeOfFieldIso T iΛ D a)).val :=
  haveI := changeOfFieldRestriction_isStronglyCartesian T iΛ c (D.objects a.fst)
    (changeOfFieldIso T iΛ D a)
  Functor.IsStronglyCartesian.map q
    (changeOfFieldRestrictionBaseMap T iΛ (D.objects a.fst) (changeOfFieldIso T iΛ D a))
    (changeOfFieldRestriction T iΛ c (D.objects a.fst) (changeOfFieldIso T iΛ D a))
    (changeOfFieldMorphism_base_fac T iΛ c D f)
    (changeOfFieldRestriction T iΛ c (D.objects b.fst) (changeOfFieldIso T iΛ D b) ≫
      (D.morphisms a.fst b.fst f.fst).arrow)

/-- The arrow `changeOfFieldMorphismArrow f` lies over the spectrum of the arrow of `𝒞_{Λ,l}`
underlying `f`. -/
theorem changeOfFieldMorphismArrow_isHomLift
    {a b : Deformation.ChangeOfFieldsCategory T D.projection} (f : a ⟶ b) :
    q.IsHomLift (eqToHom (restrictionFiberObj T iΛ c (D.objects b.fst)
          (changeOfFieldIso T iΛ D b)).property ≫ algebraBaseMap T iΛ f.snd)
      (changeOfFieldMorphismArrow T iΛ c D f) :=
  have := changeOfFieldRestriction_isStronglyCartesian T iΛ c (D.objects a.fst)
    (changeOfFieldIso T iΛ D a)
  Functor.IsStronglyCartesian.map_isHomLift q _ _ _ _

/-- The arrow `changeOfFieldMorphismArrow f`, followed by the restricting arrow of the source of
`f`, is the restricting arrow of the target followed by the reversed arrow of `f`. -/
theorem changeOfFieldMorphismArrow_fac
    {a b : Deformation.ChangeOfFieldsCategory T D.projection} (f : a ⟶ b) :
    changeOfFieldMorphismArrow T iΛ c D f ≫
        changeOfFieldRestriction T iΛ c (D.objects a.fst) (changeOfFieldIso T iΛ D a) =
      changeOfFieldRestriction T iΛ c (D.objects b.fst) (changeOfFieldIso T iΛ D b) ≫
        (D.morphisms a.fst b.fst f.fst).arrow :=
  have := changeOfFieldRestriction_isStronglyCartesian T iΛ c (D.objects a.fst)
    (changeOfFieldIso T iΛ D a)
  Functor.IsStronglyCartesian.fac q _ _ _ _

/-- The image in `Over S` of `changeOfFieldMorphismArrow f` is the spectrum of the arrow of
`𝒞_{Λ,l}` underlying `f`, up to the identifications of the bases of the restricted points. -/
theorem changeOfFieldMorphismArrow_map
    {a b : Deformation.ChangeOfFieldsCategory T D.projection} (f : a ⟶ b) :
    q.map (changeOfFieldMorphismArrow T iΛ c D f) =
      eqToHom (restrictionFiberObj T iΛ c (D.objects b.fst)
          (changeOfFieldIso T iΛ D b)).property ≫ algebraBaseMap T iΛ f.snd ≫
        eqToHom (restrictionFiberObj T iΛ c (D.objects a.fst)
          (changeOfFieldIso T iΛ D a)).property.symm := by
  have := changeOfFieldMorphismArrow_isHomLift T iΛ c D f
  rw [CategoryTheory.IsHomLift.fac' q (eqToHom (restrictionFiberObj T iΛ c (D.objects b.fst)
    (changeOfFieldIso T iΛ D b)).property ≫ algebraBaseMap T iΛ f.snd)
    (changeOfFieldMorphismArrow T iΛ c D f)]
  simp

/-- The arrow `changeOfFieldMorphismArrow` of an identity morphism is an identity. -/
theorem changeOfFieldMorphismArrow_id (a : Deformation.ChangeOfFieldsCategory T D.projection) :
    changeOfFieldMorphismArrow T iΛ c D (𝟙 a) =
      𝟙 (restrictionFiberObj T iΛ c (D.objects a.fst) (changeOfFieldIso T iΛ D a)).val := by
  refine restriction_arrow_ext T iΛ c (D.objects a.fst) (changeOfFieldIso T iΛ D a)
    (changeOfFieldMorphismArrow_isHomLift T iΛ c D (𝟙 a)) ?_ ?_
  · refine CategoryTheory.IsHomLift.of_fac' q _ _ rfl
      (restrictionFiberObj T iΛ c (D.objects a.fst) (changeOfFieldIso T iΛ D a)).property ?_
    simp [CategoricalPullback.id_snd]
  rw [changeOfFieldMorphismArrow_fac, Category.id_comp]
  show _ ≫ (D.morphisms a.fst a.fst (𝟙 a.fst)).arrow = _
  rw [D.reversed_identity, Category.comp_id]

/-- The arrow `changeOfFieldMorphismArrow` of a composite is the composite in the reverse
order. -/
theorem changeOfFieldMorphismArrow_comp
    {a b b' : Deformation.ChangeOfFieldsCategory T D.projection} (f : a ⟶ b) (g : b ⟶ b') :
    changeOfFieldMorphismArrow T iΛ c D (f ≫ g) =
      changeOfFieldMorphismArrow T iΛ c D g ≫ changeOfFieldMorphismArrow T iΛ c D f := by
  refine restriction_arrow_ext T iΛ c (D.objects a.fst) (changeOfFieldIso T iΛ D a)
    (changeOfFieldMorphismArrow_isHomLift T iΛ c D (f ≫ g)) ?_ ?_
  · refine CategoryTheory.IsHomLift.of_fac' q _ _ rfl
      (restrictionFiberObj T iΛ c (D.objects a.fst) (changeOfFieldIso T iΛ D a)).property ?_
    rw [q.map_comp, changeOfFieldMorphismArrow_map, changeOfFieldMorphismArrow_map,
      CategoricalPullback.comp_snd, algebraBaseMap_comp]
    simp
  rw [changeOfFieldMorphismArrow_fac, Category.assoc, changeOfFieldMorphismArrow_fac,
    ← Category.assoc, changeOfFieldMorphismArrow_fac, Category.assoc]
  show _ ≫ (D.morphisms a.fst b'.fst (f.fst ≫ g.fst)).arrow = _
  rw [D.reversed_composition]

end Functor

/-! ### The functor of predeformation categories -/

section Construction

variable (T : Deformation.ChangeOfFieldsSituation.{u, u, u})
variable {S : Scheme.{u}} (iΛ : Spec (.of T.Λ) ⟶ S)
variable {X : Type v} [Category.{w} X] {q : X ⥤ Over S}
variable {x₀ xₗ : X}
variable {hx₀ : q.obj x₀ = Over.mk
  (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.k)) ≫ iΛ)}
variable (hxₗ : q.obj xₗ = Over.mk
  (Spec.map (CommRingCat.ofHom (algebraMap T.Λ T.l)) ≫ iΛ))
variable {η : xₗ ⟶ x₀}
variable (hη : eqToHom (congrArg Over.left hxₗ).symm ≫ (q.map η).left ≫
  eqToHom (congrArg Over.left hx₀) = Spec.map (CommRingCat.ofHom (algebraMap T.k T.l)))
variable (c : q.ChoiceOfPullbacks)
variable (D : PredeformationConstruction iΛ q x₀ hx₀)
variable (E : PredeformationConstruction iΛ q xₗ hxₗ)

/-- The category structure on the carrier of the predeformation category of `x₀`. -/
local instance : Category.{max u w} D.carrier := D.category
/-- The category structure on the carrier of the predeformation category of `x_{l,0}`. -/
local instance : Category.{max u w} E.carrier := E.category

/-- The arrow of `𝒞_Λ` of an identity morphism of deformations is an identity. -/
theorem predeformationMorphism_ringHom_id (z : E.carrier) :
    (E.morphisms z z (𝟙 z)).ringHom = 𝟙 (E.objects z).algebra := by
  have h := E.morphism_projection (f := 𝟙 z)
  simpa using h.symm

/-- The arrow of `𝒞_Λ` of a composite of morphisms of deformations is the composite. -/
theorem predeformationMorphism_ringHom_comp {z₁ z₂ z₃ : E.carrier} (f : z₁ ⟶ z₂)
    (g : z₂ ⟶ z₃) :
    (E.morphisms z₁ z₃ (f ≫ g)).ringHom =
      (E.morphisms z₁ z₂ f).ringHom ≫ (E.morphisms z₂ z₃ g).ringHom := by
  have h := E.morphism_projection (f := f ≫ g)
  have hf := E.morphism_projection (f := f)
  have hg := E.morphism_projection (f := g)
  simp only [CategoryTheory.Functor.map_comp] at h
  rw [← h, ← hf, ← hg]
  simp

include hη in
/-- The image of a morphism of the change-of-fields category, as a morphism of deformations
of `x_{l,0}`. -/
def changeOfFieldDeformationMorphism
    {a b : Deformation.ChangeOfFieldsCategory T D.projection} (f : a ⟶ b) :
    DeformationMorphism iΛ q xₗ hxₗ
      (restrictionDeformation T iΛ hxₗ hη c (D.objects a.fst) (changeOfFieldIso T iΛ D a))
      (restrictionDeformation T iΛ hxₗ hη c (D.objects b.fst) (changeOfFieldIso T iΛ D b)) where
  ringHom := f.snd
  arrow := changeOfFieldMorphismArrow T iΛ c D f
  triangle := by
    have hsc := changeOfFieldRestriction_isStronglyCartesian T iΛ c (D.objects a.fst)
      (changeOfFieldIso T iΛ D a)
    have h₁ := changeOfFieldArrow_isHomLift T iΛ hxₗ hη c (D.objects a.fst)
      (changeOfFieldIso T iΛ D a)
    have h₂ : q.IsHomLift (restrictionResidueMap T iΛ hxₗ a.snd)
        (changeOfFieldArrow T iΛ hxₗ hη c (D.objects b.fst) (changeOfFieldIso T iΛ D b) ≫
          changeOfFieldMorphismArrow T iΛ c D f) := by
      refine CategoryTheory.IsHomLift.of_fac' q _ _ rfl
        (restrictionFiberObj T iΛ c (D.objects a.fst) (changeOfFieldIso T iΛ D a)).property ?_
      rw [q.map_comp, changeOfFieldArrow_map, changeOfFieldMorphismArrow_map]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
        restrictionResidueMap_comp_assoc]
    rw [restrictionDeformation_arrow, restrictionDeformation_arrow]
    refine Functor.IsStronglyCartesian.ext q
      (changeOfFieldRestrictionBaseMap T iΛ (D.objects a.fst) (changeOfFieldIso T iΛ D a))
      (changeOfFieldRestriction T iΛ c (D.objects a.fst) (changeOfFieldIso T iΛ D a))
      (restrictionResidueMap T iΛ hxₗ a.snd) ?_
    rw [Category.assoc, changeOfFieldMorphismArrow_fac, ← Category.assoc,
      changeOfFieldArrow_fac, changeOfFieldArrow_fac, Category.assoc,
      (D.morphisms a.fst b.fst f.fst).triangle]
  arrow_base := by
    rw [changeOfFieldMorphismArrow_map]
    simp

include hη in
/-- The arrow of `𝒞_{Λ,l}` of `changeOfFieldDeformationMorphism f` is that of `f`. -/
@[simp]
theorem changeOfFieldDeformationMorphism_ringHom
    {a b : Deformation.ChangeOfFieldsCategory T D.projection} (f : a ⟶ b) :
    (changeOfFieldDeformationMorphism T iΛ hxₗ hη c D f).ringHom = f.snd := rfl

include hη in
/-- The arrow of `𝒳` of `changeOfFieldDeformationMorphism f` is `changeOfFieldMorphismArrow f`. -/
@[simp]
theorem changeOfFieldDeformationMorphism_arrow
    {a b : Deformation.ChangeOfFieldsCategory T D.projection} (f : a ⟶ b) :
    (changeOfFieldDeformationMorphism T iΛ hxₗ hη c D f).arrow =
      changeOfFieldMorphismArrow T iΛ c D f := rfl

include hη in
/-- **Stacks Project, Tag 07WX.** The canonical functor from the change of residue field of the
predeformation category of `x₀` to the predeformation category of its restriction `x_{l,0}`. -/
@[stacks 07WX "the canonical functor; the ambient base category is the category of all \
S-schemes rather than the big fppf site", implicit_reducible]
def changeOfFieldFunctor :
    Deformation.ChangeOfFieldsCategory T D.projection ⥤ E.carrier where
  obj a := E.objects.symm
    (restrictionDeformation T iΛ hxₗ hη c (D.objects a.fst) (changeOfFieldIso T iΛ D a))
  map {a b} f := (E.morphisms _ _).symm (transportDeformationMorphism
    (E.objects.apply_symm_apply _) (E.objects.apply_symm_apply _)
    (changeOfFieldDeformationMorphism T iΛ hxₗ hη c D f))
  map_id a := by
    rw [Equiv.symm_apply_eq]
    apply DeformationMorphism.ext_of_components
    · rw [transportDeformationMorphism_ringHom, predeformationMorphism_ringHom_id]
      simp [CategoricalPullback.id_snd]
    · rw [transportDeformationMorphism_arrow, E.reversed_identity,
        changeOfFieldDeformationMorphism_arrow, changeOfFieldMorphismArrow_id]
      simp
  map_comp {a b b'} f g := by
    rw [Equiv.symm_apply_eq]
    apply DeformationMorphism.ext_of_components
    · rw [transportDeformationMorphism_ringHom, predeformationMorphism_ringHom_comp]
      simp only [Equiv.apply_symm_apply, transportDeformationMorphism_ringHom]
      simp [CategoricalPullback.comp_snd]
    · rw [transportDeformationMorphism_arrow, E.reversed_composition]
      simp only [Equiv.apply_symm_apply, transportDeformationMorphism_arrow,
        changeOfFieldDeformationMorphism_arrow, changeOfFieldMorphismArrow_comp]
      simp

include hη in
/-- The functor sends an object of the change-of-fields category to the restriction of the
deformation it carries. -/
theorem changeOfFieldFunctor_objects
    (a : Deformation.ChangeOfFieldsCategory T D.projection) :
    E.objects ((changeOfFieldFunctor T iΛ hxₗ hη c D E).obj a) =
      restrictionDeformation T iΛ hxₗ hη c (D.objects a.fst) (changeOfFieldIso T iΛ D a) :=
  E.objects.apply_symm_apply _

include hη in
/-- The functor sends a morphism to the unique lift of its arrow of `𝒞_{Λ,l}` through the
restricting arrows. -/
theorem changeOfFieldFunctor_morphisms
    {a b : Deformation.ChangeOfFieldsCategory T D.projection} (f : a ⟶ b) :
    E.morphisms _ _ ((changeOfFieldFunctor T iΛ hxₗ hη c D E).map f) =
      transportDeformationMorphism (E.objects.apply_symm_apply _)
        (E.objects.apply_symm_apply _) (changeOfFieldDeformationMorphism T iΛ hxₗ hη c D f) :=
  (E.morphisms _ _).apply_symm_apply _

/-- The projection of the change-of-fields category sends an object to its Artinian local
algebra with residue field `l`. -/
theorem changeOfFieldsProjection_obj
    (a : Deformation.ChangeOfFieldsCategory T D.projection) :
    (Deformation.changeOfFieldsProjection T D.projection).obj a = a.snd := rfl

/-- The projection of the change-of-fields category sends a morphism to its arrow of
`𝒞_{Λ,l}`. -/
theorem changeOfFieldsProjection_map
    {a b : Deformation.ChangeOfFieldsCategory T D.projection} (f : a ⟶ b) :
    (Deformation.changeOfFieldsProjection T D.projection).map f = f.snd := rfl

include hη in
/-- The functor is compatible with the projections on objects. -/
theorem changeOfFieldFunctor_projection_obj
    (a : Deformation.ChangeOfFieldsCategory T D.projection) :
    E.projection.obj ((changeOfFieldFunctor T iΛ hxₗ hη c D E).obj a) =
      (Deformation.changeOfFieldsProjection T D.projection).obj a := by
  rw [E.object_projection, changeOfFieldFunctor_objects, restrictionDeformation_algebra,
    changeOfFieldsProjection_obj]

include hη in
/-- **Stacks Project, Tag 07WX.** The canonical functor is a functor of categories over
`𝒞_{Λ,l}`. -/
@[stacks 07WX "the canonical functor lies over 𝒞_{Λ,l}; the ambient base category is the \
category of all S-schemes rather than the big fppf site"]
theorem changeOfFieldFunctor_projection_comm :
    changeOfFieldFunctor T iΛ hxₗ hη c D E ⋙ E.projection =
      Deformation.changeOfFieldsProjection T D.projection := by
  refine CategoryTheory.Functor.ext
    (h_obj := changeOfFieldFunctor_projection_obj T iΛ hxₗ hη c D E)
    (h_map := fun a b f => ?_)
  have ht := eq_of_eqToHom_conj (E.object_projection _) (E.object_projection _)
    (E.morphism_projection (f := (changeOfFieldFunctor T iΛ hxₗ hη c D E).map f))
  rw [CategoryTheory.Functor.comp_map, ht, changeOfFieldFunctor_morphisms,
    transportDeformationMorphism_ringHom, changeOfFieldDeformationMorphism_ringHom,
    changeOfFieldsProjection_map]
  simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
  rfl

end Construction

end Deformation.Artin

end
