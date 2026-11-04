module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeCriterion
public import StacksFrontier.CategoryTheory.TwoYoneda.OverBase
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# Scheme-valued points of an algebraic stack, and the link of a valuative square

Let `B` be a big fppf site containing a scheme `S` and let `U` be an object of the big fppf site
of `S`, that is a scheme over `S` belonging to `B`. This file sets up the dictionary between the
two ways a scheme-valued point of a category fibred in groupoids `𝒴` over the site of `S` can be
presented:

* as a 1-morphism `schemeFibredCategory B S hS U ⟶ 𝒴.val` of categories fibred in groupoids over
  the site of `S`, which is what a `AlgebraicGeometry.Stack.ValuativeSquare` carries; and
* as a functor `(Sch/U)_{fppf} ⥤ 𝒴.val.obj` strictly over `CategoryTheory.Over.map U.hom`, which
  is what `AlgebraicGeometry.Stack.IsRepresentableByAlgebraicSpaces` quantifies over.

`AlgebraicGeometry.Stack.sitePointOfSchemePoint` goes from the first presentation to the second,
and `AlgebraicGeometry.Stack.sitePointOfSchemePoint_compatible` says that the result is strictly
over `CategoryTheory.Over.map U.hom`.

The file also defines a morphism of the site read as a 1-morphism
(`AlgebraicGeometry.Stack.schemeMorphism`), and the *link* of a valuative square: the morphism of
`𝒴` from the image of the generic point to the value of the special point at the unit object,
obtained by inverting the filling 2-morphism and composing with the image of the canonical arrow
to the unit object.

## Main definitions

* `AlgebraicGeometry.Stack.siteOver`: the big fppf site of the scheme underlying an object of the
  big fppf site of `S`.
* `AlgebraicGeometry.Stack.schemeMorphism`: a morphism of the site, as a 1-morphism of the
  categories fibred in groupoids it represents.
* `AlgebraicGeometry.Stack.sitePointOfSchemePoint`: a scheme-valued point, read as a functor on
  the site over `U`.
* `AlgebraicGeometry.Stack.pointLink`: the link of a valuative square.
* `AlgebraicGeometry.Stack.dominatingGenericObject` and
  `AlgebraicGeometry.Stack.dominatingSpecialObject`: the two spectra of a dominating extension, as
  objects of the big fppf site of `S`.
* `AlgebraicGeometry.Stack.outerSquare`: the valuative square of the outer rectangle cut out by a
  dominating extension.

## Main results

* `AlgebraicGeometry.Stack.schemeMorphism_eq_of_canonical`: a 1-morphism whose underlying functor
  is `CategoryTheory.Over.map r` *is* `schemeMorphism r`.
* `AlgebraicGeometry.Stack.sitePointOfSchemePoint_compatible`: the point produced by
  `sitePointOfSchemePoint` is strictly over `CategoryTheory.Over.map U.hom`.
* `AlgebraicGeometry.Stack.pointLink_lift`: the link lies over the canonical map of the square.
* `AlgebraicGeometry.Stack.outerSquare_pointLink`: the link of the outer rectangle cut out by a
  dominating extension, computed from the link of the square.

## Implementation notes

`schemeMorphism` is `CategoryTheory.BasedFunctor.overMap` packaged as a 1-morphism of the
2-category of categories fibred in groupoids. The canonical arrow `a ⟶ 1_U` of a slice is spelled
`CategoryTheory.Over.mkIdTerminal.from a` throughout.

## References

* [Stacks Project, Tag 0CLK](https://stacks.math.columbia.edu/tag/0CLK)
* [Stacks Project, Tag 02ZW](https://stacks.math.columbia.edu/tag/02ZW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.BasedFunctor.comp CategoryTheory.Bicategory.InducedBicategory

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} {hS : B.Contains S}

/-- The big fppf site of the scheme underlying an object of the big fppf site of `S`. -/
abbrev siteOver (U : BigFppfOver B S hS) := BigFppfOver B U.left.1 U.left.2

/-- A morphism `r : U ⟶ V` of the big fppf site of `S`, read as a 1-morphism of the categories
fibred in groupoids the two objects represent. -/
def schemeMorphism {U V : BigFppfOver B S hS} (r : U ⟶ V) :
    schemeFibredCategory B S hS U ⟶ schemeFibredCategory B S hS V :=
  Bicategory.InducedBicategory.mkHom (BasedFunctor.overMap r)

/-- The underlying functor of `schemeMorphism r` is `CategoryTheory.Over.map r`. -/
@[simp]
theorem schemeMorphism_hom_toFunctor {U V : BigFppfOver B S hS} (r : U ⟶ V) :
    (schemeMorphism B r).hom.toFunctor = Over.map r :=
  rfl

/-- A 1-morphism of the categories fibred in groupoids represented by two objects of the site is
`schemeMorphism r` as soon as its underlying functor is `CategoryTheory.Over.map r`. -/
theorem schemeMorphism_eq_of_canonical {U V : BigFppfOver B S hS} (r : U ⟶ V)
    (j : schemeFibredCategory B S hS U ⟶ schemeFibredCategory B S hS V)
    (hj : j.hom.toFunctor = Over.map r) : j = schemeMorphism B r :=
  Bicategory.InducedBicategory.hom_ext (BasedCategory.BasedFunctor.ext' hj)

/-- `schemeMorphism` is functorial. -/
theorem schemeMorphism_comp {U V W : BigFppfOver B S hS} (r : U ⟶ V) (s : V ⟶ W) :
    schemeMorphism B r ≫ schemeMorphism B s = schemeMorphism B (r ≫ s) :=
  schemeMorphism_eq_of_canonical B (r ≫ s) _ (Over.mapComp_eq r s).symm

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- A scheme-valued point of `𝒴` at an object `U` of the big fppf site of `S`, read as a functor
on the big fppf site of the scheme underlying `U`.

The two sites are related by `CategoryTheory.Over.iteratedSliceBackward`, which identifies the
site over the scheme `U.left.1` with the slice of the site of `S` over `U`. -/
def sitePointOfSchemePoint (U : BigFppfOver B S hS)
    (y : schemeFibredCategory B S hS U ⟶ 𝒴.val) : siteOver B U ⥤ 𝒴.val.val.obj :=
  Over.iteratedSliceBackward U ⋙ CatFiberedInGroupoids.homFunctor y

/-- The functor attached to a scheme-valued point by
`AlgebraicGeometry.Stack.sitePointOfSchemePoint` is strictly over the restriction functor
`CategoryTheory.Over.map U.hom` along `U`. -/
theorem sitePointOfSchemePoint_compatible (U : BigFppfOver B S hS)
    (y : schemeFibredCategory B S hS U ⟶ 𝒴.val) :
    sitePointOfSchemePoint B U y ⋙ 𝒴.val.val.p = Over.map U.hom := by
  have hy : CatFiberedInGroupoids.homFunctor y ⋙ 𝒴.val.val.p = Over.forget U := y.hom.w
  exact (congrArg (Over.iteratedSliceBackward U ⋙ ·) hy).trans (Over.iteratedSliceBackward_forget U)

variable {f : 𝒳 ⟶ 𝒴}

/-- The *link* of a valuative square: the morphism of `𝒴` from the image under `f` of the value
of the generic point at the unit object to the value of the special point at the unit object.

It is the inverse of the filling 2-morphism at the unit object — invertible because the fibres of
`𝒴` are groupoids and the component lies over an identity — followed by the image under the
special point of the canonical arrow to the unit object. -/
noncomputable def pointLink (q : ValuativeSquare B S hS f) :
    f.hom.hom.obj (q.x.hom.obj (Over.mk (𝟙 _))) ⟶ q.y.hom.obj (Over.mk (𝟙 _)) :=
  (@asIso _ _ _ _ (q.γ.hom.app (Over.mk (𝟙 _)))
      (Functor.isIso_of_fiber_isGroupoid
        (𝒴.val.isFiberedInGroupoids.fiber_isGroupoid _) (q.γ.hom.app (Over.mk (𝟙 _)))
        (q.γ.hom.isHomLift' (Over.mk (𝟙 _))))).inv ≫
    q.y.hom.map (Over.mkIdTerminal.from (q.j.hom.obj (Over.mk (𝟙 _))))

/-- The spectrum of the extended fraction field of a dominating extension, as an object of the big
fppf site of `S`. -/
noncomputable abbrev dominatingGenericObject {q : ValuativeSquare B S hS f}
    (e : q.DominatingExtension) : BigFppfOver B S hS :=
  siteObject B S hS e.field_mem (Spec.map (CommRingCat.ofHom (algebraMap e.R' e.K')) ≫
    Spec.map (CommRingCat.ofHom e.ringMap) ≫ q.base)

/-- The spectrum of the dominating valuation ring of a dominating extension, as an object of the
big fppf site of `S`. -/
noncomputable abbrev dominatingSpecialObject {q : ValuativeSquare B S hS f}
    (e : q.DominatingExtension) : BigFppfOver B S hS :=
  siteObject B S hS e.ring_mem (Spec.map (CommRingCat.ofHom e.ringMap) ≫ q.base)

/-- The filling 2-morphism of a valuative square is invertible at the unit object. -/
private theorem isIso_gamma_app (q : ValuativeSquare B S hS f) :
    IsIso (q.γ.hom.app (Over.mk (𝟙 _))) :=
  Functor.isIso_of_fiber_isGroupoid (𝒴.val.isFiberedInGroupoids.fiber_isGroupoid _) _
    (q.γ.hom.isHomLift' _)

/-- The link of a valuative square lies over the canonical map from the generic point to the
spectrum of the valuation ring. -/
theorem pointLink_lift (q : ValuativeSquare B S hS f) :
    𝒴.val.val.p.IsHomLift q.genericMap (pointLink B q) := by
  let K := siteObject B S hS q.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)
  have hiso := isIso_gamma_app B q (𝒴 := 𝒴)
  have hγ : 𝒴.val.val.p.IsHomLift (𝟙 K) (q.γ.hom.app (Over.mk (𝟙 K))) :=
    q.γ.hom.isHomLift' (Over.mk (𝟙 K))
  have hinv : 𝒴.val.val.p.IsHomLift (𝟙 K) (@inv _ _ _ _ (q.γ.hom.app (Over.mk (𝟙 K))) hiso) :=
    IsHomLift.lift_id_inv_isIso 𝒴.val.val.p K (q.γ.hom.app (Over.mk (𝟙 K)))
  have hterm : 𝒴.val.val.p.IsHomLift q.genericMap
      (q.y.hom.map (Over.mkIdTerminal.from (q.j.hom.obj (Over.mk (𝟙 K))))) :=
    Functor.TwoYoneda.isHomLift_map_from_mkIdTerminal_of_eq
      𝒴.val.val.p q.genericMap (H := q.y.hom) _
      (Functor.congr_obj q.j_canonical (Over.mk (𝟙 K)))
  exact @IsHomLift.comp_lift_id_left _ _ _ _ 𝒴.val.val.p _ _ _ _ _ q.genericMap _ hterm
    (@inv _ _ _ _ (q.γ.hom.app (Over.mk (𝟙 K))) hiso) hinv

/-- The valuative square of the outer rectangle cut out by a dominating extension: the extended
valuation ring with the extended generic and special points and the pasted 2-morphism. -/
noncomputable def outerSquare (q : ValuativeSquare B S hS f) (e : q.DominatingExtension) :
    ValuativeSquare B S hS f where
  R := e.R'
  K := e.K'
  ring_mem := e.ring_mem
  field_mem := e.field_mem
  base := Spec.map (CommRingCat.ofHom e.ringMap) ≫ q.base
  genericMap := e.genericMap
  genericMap_left := e.genericMap_left
  j := e.j
  j_canonical := e.j_canonical
  x := e.k ≫ q.x
  y := e.a ≫ q.y
  γ := e.inducedGamma

attribute [local implicit_reducible] outerSquare

/-- **The link of the outer rectangle of a dominating extension, computed from the link of the
square.** Composing the filling 2-morphism of the outer square at the unit object with the image
under `f` of the restriction of the generic point and then with the link of `q` is the same as
restricting along the canonical arrows of the two slices of the extension. -/
theorem outerSquare_pointLink (q : ValuativeSquare B S hS f) (e : q.DominatingExtension) :
    (outerSquare B q e).γ.hom.app (Over.mk (𝟙 _)) ≫
        f.hom.hom.map (q.x.hom.map
          (Over.mkIdTerminal.from (e.k.hom.obj (Over.mk (𝟙 _))))) ≫ pointLink B q =
      (outerSquare B q e).y.hom.map
          (Over.mkIdTerminal.from (e.j.hom.obj (Over.mk (𝟙 _)))) ≫
        q.y.hom.map (Over.mkIdTerminal.from (e.a.hom.obj (Over.mk (𝟙 _)))) := by
  let u := Over.mk (𝟙 (siteObject B S hS q.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)))
  let z := Over.mk (𝟙 (siteObject B S hS e.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap e.R' e.K')) ≫
      Spec.map (CommRingCat.ofHom e.ringMap) ≫ q.base)))
  have hiso := isIso_gamma_app B q (𝒴 := 𝒴)
  have hn := q.γ.hom.toNatTrans.naturality (Over.mkIdTerminal.from (e.k.hom.obj z))
  change q.y.hom.map (q.j.hom.map (Over.mkIdTerminal.from (e.k.hom.obj z))) ≫
      q.γ.hom.app u =
    q.γ.hom.app (e.k.hom.obj z) ≫
      f.hom.hom.map (q.x.hom.map (Over.mkIdTerminal.from (e.k.hom.obj z))) at hn
  show (𝟙 _ ≫ q.y.hom.map (e.commute.hom.app z) ≫ 𝟙 _ ≫
      q.γ.hom.app (e.k.hom.obj z) ≫ 𝟙 _) ≫ _ ≫
      (@inv _ _ _ _ (q.γ.hom.app u) hiso ≫ _) = _
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  rw [← Category.assoc (q.γ.hom.app _) _ _, ← hn]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [← q.y.hom.toFunctor.map_comp, ← q.y.hom.toFunctor.map_comp]
  show q.y.hom.map _ = q.y.hom.map _ ≫ q.y.hom.map _
  rw [← q.y.hom.toFunctor.map_comp]
  congr 1
  exact Over.mkIdTerminal.hom_ext _ _

end AlgebraicGeometry.Stack

end
