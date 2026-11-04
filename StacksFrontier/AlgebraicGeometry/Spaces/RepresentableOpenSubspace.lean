module

public import Mathlib.CategoryTheory.Subfunctor.Image
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCover

/-!
# The range of a representable open immersion from a scheme

Let `F` be a presheaf on the big fppf site of `S` and let `g : h_T ⟶ F` be a morphism from the
representable presheaf of an object `T` of that site which is an open immersion in the sense of
Stacks 02YU part (1): representable, with every represented base change an open immersion of
schemes. Then the image subfunctor of `g` is an open subspace of `F` in the sense of Stacks 02YU
part (2), and it is representable — by `T` itself.

This is how a Zariski-style covering of a presheaf by representable open pieces is turned into a
family of open subspaces: one produces the pieces as morphisms `h_{T_i} ⟶ F` and needs them as
*subobjects* of `F`.

## Main results

* `AlgebraicGeometry.Space.isOpenSubspace_range_of_isOpenImmersion`: the image subfunctor is an
  open subspace.
* `AlgebraicGeometry.Space.isRepresentable_range_of_isOpenImmersion`: the image subfunctor is
  representable.

## Implementation notes

An open immersion of schemes is a monomorphism, and both `CategoryTheory.Over.forget` and the
inclusion of the big fppf site's schemes into all schemes reflect monomorphisms, so the
inverse-image property lies below the monomorphisms of the site; hence `g` is a monomorphism of
presheaves by `CategoryTheory.MorphismProperty.presheaf_mono_of_le` and
`CategoryTheory.Subfunctor.toRange` is an isomorphism. Everything else is transport along that
isomorphism: `h_T` is an algebraic space by Stacks 025Z, and the inclusion of the image is `g`
precomposed with it.

## References

* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 025Z](https://stacks.math.columbia.edu/tag/025Z)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ F)

-- Monomorphy of a relative open immersion of presheaves is
-- `AlgebraicGeometry.Space.mono_of_presheaf_isOpenImmersion` in
-- `StacksFrontier.AlgebraicGeometry.Spaces.OpenCover`, which this module imports.

/-- The representable presheaf of `T` is isomorphic to the image subfunctor of a representable
open immersion `g : h_T ⟶ F`, by `CategoryTheory.Subfunctor.toRange`. -/
noncomputable def rangeIsoOfIsOpenImmersion (hg : IsOpenImmersion B S hS g) :
    yoneda.obj T ≅ (Subfunctor.range g).toFunctor :=
  have _ : Mono g := mono_of_presheaf_isOpenImmersion hg
  asIso (Subfunctor.toRange g)

/-- **The image of a representable open immersion from a scheme is representable**, by the object
of the big fppf site it comes from. -/
theorem isRepresentable_range_of_isOpenImmersion (hg : IsOpenImmersion B S hS g) :
    (Subfunctor.range g).toFunctor.IsRepresentable :=
  isRepresentable_of_natIso _ (rangeIsoOfIsOpenImmersion T g hg)

/-- **Stacks 02YU part (2) for the image of a representable open immersion from a scheme.** The
image subfunctor of an open immersion `g : h_T ⟶ F` is an open subspace of `F`: it is an
algebraic space because it is isomorphic to the representable algebraic space of `T`, and its
inclusion into `F` is `g` read through that isomorphism. -/
theorem isOpenSubspace_range_of_isOpenImmersion (hg : IsOpenImmersion B S hS g) :
    IsOpenSubspace B S hS (Subfunctor.range g) := by
  set e := rangeIsoOfIsOpenImmersion T g hg
  refine ⟨isAlgebraicSpace_of_iso B S hS e.symm (isAlgebraicSpace_yoneda B S hS T), ?_⟩
  have hfac : e.inv ≫ g = (Subfunctor.range g).ι := by
    have := e.inv_hom_id_assoc (Subfunctor.range g).ι
    rwa [show e.hom ≫ (Subfunctor.range g).ι = g from Subfunctor.toRange_ι g] at this
  have hopen : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (e.inv ≫ g) :=
    MorphismProperty.RespectsIso.precomp _ e.inv g hg
  rwa [hfac] at hopen

end AlgebraicGeometry.Space

end
