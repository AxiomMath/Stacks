module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RestrictFreeIsoComp

/-!
# The structure-sheaf comparison of a restriction is pseudo-functorial

`AlgebraicGeometry.Scheme.Modules.restrictUnitIso` identifies the restriction of the structure
sheaf along an open immersion with the structure sheaf.  For a composite of two open immersions
there are two such identifications of the restriction along the composite -- the one for the
composite, and the iterated one read through `AlgebraicGeometry.restrictCompIso` -- and Mathlib
proves no coherence for `restrictUnitIso` at all.  This file proves they agree, and thereby
discharges the hypothesis of
`Stacks.Modules.restrictFreeIso_inv_comp_restrictCompIso_hom_of_unit`, making the
pseudo-functoriality of the free comparison unconditional for every index type.

## The route

On sections over an open `W` the component of `restrictUnitIso` along `f` is the inverse-image
comparison `AlgebraicGeometry.Scheme.Hom.appIso` of `f` at `W`, by definition -- the module
structure is carried along the two forgetful functors, so the two sides are the same map and the
identification is by `rfl`.  The statement therefore reduces to the pseudo-functoriality of
`appIso`, which Mathlib does not state either but which follows from
`AlgebraicGeometry.Scheme.Hom.appIso_hom'`, presenting `appIso` as an
`AlgebraicGeometry.Scheme.Hom.appLE`, together with
`AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`.

## Implementation notes

**The restriction maps of the comparison are parameters, not `eqToHom`s.**  The component of
`AlgebraicGeometry.restrictCompIso` is a composite of two restriction maps of the presheaf, each
an `eqToHom` chosen by `AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr` and
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`.  Stating the coherence of `appIso` with
one `eqToHom` of its own makes it unusable: the two eqToHom composites agree only by thinness of
the category of opens, not definitionally, so `exact congr(… x)` fails on the components.  Taking
the restriction maps as arbitrary morphisms instead -- the idiom of
`AlgebraicGeometry.restrictLocal_app` -- lets the consumer's own maps be unified against them, and
`Subsingleton.elim` puts them back into `eqToHom` form inside the proof.  This is why
`Stacks.Modules.map_comp_map_comp_appIso_hom_comp_appIso_hom` takes two such maps and an
intermediate open.

**Reading the coherence on the inverses is term mode.**  `simp` makes no progress on a goal about
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`, and `rw` cannot find `Epi` of an isomorphism's
forward map there, both for the reason recorded in
`StacksFrontier/AlgebraicGeometry/FiniteLocallyFree/RestrictFreeIsoComp.lean`:  the sheaf of rings of
a scheme unfolds to the one `CategoryTheory.SheafOfModules` asks for only at default transparency.
The inverse form is therefore obtained by `Iso.ext`, `congrArg Iso.inv` and the associativity of
composition applied by hand.

## Main results

* `Stacks.Modules.restrictCompIso_hom_comp_restrictUnitIso`: **the structure-sheaf comparison of a
  restriction is pseudo-functorial.**
* `Stacks.Modules.restrictUnitIso_inv_comp_restrictCompIso_hom`: the same read on the other side of
  the isomorphisms, which is the form the free statement consumes.
* `Stacks.Modules.restrictFreeIso_inv_comp_restrictCompIso_hom`: **the free comparison of a
  restriction is pseudo-functorial**, with no hypothesis, for an arbitrary index type.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules (restrictFunctor)

universe u

namespace Stacks.Modules

variable {T' T S : Scheme.{u}} (h : T' ⟶ T) (g : T ⟶ S) [IsOpenImmersion h] [IsOpenImmersion g]
  {k : T' ⟶ S} (hk : h ≫ g = k) [IsOpenImmersion k]

include hk in
/-- The image of an open under a composite of two open immersions is the iterated image. -/
theorem image_image_eq_image (W : T'.Opens) : g ''ᵁ (h ''ᵁ W) = k ''ᵁ W := by
  subst hk; simp

include hk in
/-- **The inverse-image comparison of a composite of open immersions is the iterated one**, read
through an arbitrary restriction map of the presheaf between the two presentations of the image.

Presenting each `AlgebraicGeometry.Scheme.Hom.appIso` as an
`AlgebraicGeometry.Scheme.Hom.appLE` by `AlgebraicGeometry.Scheme.Hom.appIso_hom'` turns the
statement into `AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE`, the restriction map being absorbed
into the `appLE`.  The restriction map is a parameter and is identified
with the canonical `eqToHom` by thinness of the category of opens. -/
theorem map_comp_appIso_hom_comp_appIso_hom (W : T'.Opens)
    (a : op (k ''ᵁ W) ⟶ op (g ''ᵁ (h ''ᵁ W))) :
    S.presheaf.map a ≫ (g.appIso (h ''ᵁ W)).hom ≫ (h.appIso W).hom = (k.appIso W).hom := by
  obtain rfl : a = eqToHom (congrArg op (image_image_eq_image h g hk W)).symm :=
    Subsingleton.elim _ _
  subst hk
  simp [Scheme.Hom.appIso_hom']

include hk in
/-- `Stacks.Modules.map_comp_appIso_hom_comp_appIso_hom` with the restriction map split in two, the
shape in which the component of `AlgebraicGeometry.restrictCompIso` presents it:  that component is
the restriction map of `AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr` followed by the one
of `AlgebraicGeometry.Scheme.Modules.restrictFunctorComp`, through an intermediate open. -/
theorem map_comp_map_comp_appIso_hom_comp_appIso_hom (W : T'.Opens) {A : (S.Opens)ᵒᵖ}
    (p : op (k ''ᵁ W) ⟶ A) (q : A ⟶ op (g ''ᵁ (h ''ᵁ W))) :
    S.presheaf.map p ≫ S.presheaf.map q ≫ (g.appIso (h ''ᵁ W)).hom ≫ (h.appIso W).hom =
      (k.appIso W).hom :=
  ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (g.appIso (h ''ᵁ W)).hom ≫ (h.appIso W).hom)
      (S.presheaf.map_comp p q).symm)).trans
    (map_comp_appIso_hom_comp_appIso_hom h g hk W (p ≫ q))

include hk in
/-- **The structure-sheaf comparison of a restriction is pseudo-functorial.**  Comparing the
restriction along the composite with the iterated restriction and then identifying the structure
sheaf at each of the two stages is identifying it once, for the composite.

Each component of `AlgebraicGeometry.Scheme.Modules.restrictUnitIso` is an
`AlgebraicGeometry.Scheme.Hom.appIso` by `rfl`, and each component of
`AlgebraicGeometry.restrictCompIso` is a pair of restriction maps of the presheaf, so this is
`Stacks.Modules.map_comp_map_comp_appIso_hom_comp_appIso_hom` evaluated at a section. -/
theorem restrictCompIso_hom_comp_restrictUnitIso :
    (AlgebraicGeometry.restrictCompIso h g hk (SheafOfModules.unit S.ringCatSheaf)).hom ≫
        (restrictFunctor h).map (Scheme.Modules.restrictUnitIso g).hom ≫
        (Scheme.Modules.restrictUnitIso h).hom =
      (Scheme.Modules.restrictUnitIso k).hom := by
  ext W x
  exact congr($(map_comp_map_comp_appIso_hom_comp_appIso_hom h g hk W _ _) x)

include hk in
/-- `Stacks.Modules.restrictCompIso_hom_comp_restrictUnitIso` read on the other side of the
isomorphisms, which is the form
`Stacks.Modules.restrictFreeIso_inv_comp_restrictCompIso_hom_of_unit` asks for. -/
theorem restrictUnitIso_inv_comp_restrictCompIso_hom :
    (Scheme.Modules.restrictUnitIso k).inv ≫
        (AlgebraicGeometry.restrictCompIso h g hk
          (SheafOfModules.unit S.ringCatSheaf)).hom =
      (Scheme.Modules.restrictUnitIso h).inv ≫
        (restrictFunctor h).map (Scheme.Modules.restrictUnitIso g).inv := by
  have hE : (AlgebraicGeometry.restrictCompIso h g hk
        (SheafOfModules.unit S.ringCatSheaf) ≪≫
      (restrictFunctor h).mapIso (Scheme.Modules.restrictUnitIso g) ≪≫
      Scheme.Modules.restrictUnitIso h) = Scheme.Modules.restrictUnitIso k :=
    Iso.ext (restrictCompIso_hom_comp_restrictUnitIso h g hk)
  have h3 : ((Scheme.Modules.restrictUnitIso h).inv ≫
        (restrictFunctor h).map (Scheme.Modules.restrictUnitIso g).inv) ≫
      (AlgebraicGeometry.restrictCompIso h g hk
        (SheafOfModules.unit S.ringCatSheaf)).inv =
      (Scheme.Modules.restrictUnitIso k).inv :=
    congrArg Iso.inv hE
  refine (congrArg
    (· ≫ (AlgebraicGeometry.restrictCompIso h g hk
      (SheafOfModules.unit S.ringCatSheaf)).hom) h3.symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg
    (((Scheme.Modules.restrictUnitIso h).inv ≫
      (restrictFunctor h).map (Scheme.Modules.restrictUnitIso g).inv) ≫ ·)
      (Iso.inv_hom_id _)).trans ?_
  exact Category.comp_id _

include hk in
/-- **The free comparison of a restriction is pseudo-functorial.**  For open immersions `h` and `g`
composing to `k`, the comparison of the restriction along `k` of the free `𝒪_S`-module on `I` with
the free `𝒪_{T'}`-module on `I` is the iterated comparison, read through
`AlgebraicGeometry.restrictCompIso`.

This is `Stacks.Modules.restrictFreeIso_inv_comp_restrictCompIso_hom_of_unit` with its hypothesis
discharged by `Stacks.Modules.restrictUnitIso_inv_comp_restrictCompIso_hom`. -/
theorem restrictFreeIso_inv_comp_restrictCompIso_hom (I : Type u) :
    (restrictFreeIso k I).inv ≫
        (AlgebraicGeometry.restrictCompIso h g hk
          (SheafOfModules.free (R := S.ringCatSheaf) I)).hom =
      (restrictFreeIso h I).inv ≫
        (restrictFunctor h).map (restrictFreeIso g I).inv :=
  restrictFreeIso_inv_comp_restrictCompIso_hom_of_unit h g hk I
    (restrictUnitIso_inv_comp_restrictCompIso_hom h g hk)

end Stacks.Modules

end
