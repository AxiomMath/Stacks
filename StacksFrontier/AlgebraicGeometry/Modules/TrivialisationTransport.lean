module

public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.GenericFreeNeighbourhood

/-!
# Transporting a trivialisation of a module along an open immersion

A module on a scheme is trivialised over an open in two interchangeable ways: as an isomorphism
of `AlgebraicGeometry.Scheme.Modules.restrict` along the inclusion of the open with the free
module on the open subscheme, or as an isomorphism of `SheafOfModules.over` with the free module
over the sliced structure sheaf. The first is what a computation on an affine chart produces; the
second is what `AlgebraicGeometry.FreeNearFibreGeneric` asks for. This file supplies the passage
from the first to the second, and the transport of a trivialisation found on an open of the
source of an open immersion to the image of that open.

## Main results

* `AlgebraicGeometry.overIsoOfRestrictIso`: a trivialisation of the restriction along `U.ι` is a
  trivialisation of `SheafOfModules.over`. This is the converse of
  `Stacks.AlgebraicGeometry.IrreducibleDevissage.restrictFunctorIsoOfOverIso`.
* `AlgebraicGeometry.nonempty_over_image_iso_free_of_pullback_restrict_iso_free`: a
  trivialisation of the pullback of a module along an open immersion `j`, over an open `V` of the
  source, is a trivialisation of the module itself over the image `j ''ᵁ V`.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules.overEquiv` is an equivalence, hence fully faithful, so an
isomorphism between the images of two modules under its functor is the image of a unique
isomorphism: that is what `CategoryTheory.Functor.preimageIso` extracts, and it is the whole
content of `AlgebraicGeometry.overIsoOfRestrictIso` once
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` and
`Stacks.AlgebraicGeometry.IrreducibleDevissage.freeOverEquivIso` have put the two sides in that
shape.

The transport along an open immersion `j` factors `V.ι ≫ j` as `(j.isoImage V).inv` followed by
`(j ''ᵁ V).ι` (`AlgebraicGeometry.Scheme.Hom.isoImage_inv_ι`). Restriction along the first factor
carries a free module to a free module with the same index
(`restrictFunctor_obj_free_iso`), so nothing has to be inverted: the chain of natural
isomorphisms `restrictFunctorCongr`, `restrictFunctorComp` and `restrictFunctorIsoPullback` is
read in one direction only.

## References

* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry

/-- **A trivialisation of the restriction along `U.ι` is a trivialisation of
`SheafOfModules.over`.** This is the converse of
`Stacks.AlgebraicGeometry.IrreducibleDevissage.restrictFunctorIsoOfOverIso`.

`AlgebraicGeometry.Scheme.Modules.overEquiv` is an equivalence, hence fully faithful; applying
its functor to the two sides of the conclusion and comparing them with
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` and
`Stacks.AlgebraicGeometry.IrreducibleDevissage.freeOverEquivIso` gives exactly the given
isomorphism, and `CategoryTheory.Functor.preimageIso` takes it back. -/
public def overIsoOfRestrictIso {Z : Scheme.{u}} (U : Z.Opens) (I : Type u) (G : Z.Modules)
    (eG : (Scheme.Modules.restrictFunctor U.ι).obj G ≅
      SheafOfModules.free.{u} (R := (U : Scheme).ringCatSheaf) I) :
    G.over U ≅ SheafOfModules.free.{u} (R := Z.ringCatSheaf.over U) I :=
  (Scheme.Modules.overEquiv U).functor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app G ≪≫ eG ≪≫
      Stacks.AlgebraicGeometry.IrreducibleDevissage.freeOverEquivIso Z U I)

/-- **A trivialisation of the restriction of a pullback, transported to the image.** Let
`j : Y ⟶ Z` be an open immersion, `G` a module on `Z` and `V` an open of `Y`. A trivialisation of
`j^* G` restricted to `V` is a trivialisation of `G` over the image `j ''ᵁ V`.

The inclusion of the image factors as `(j.isoImage V).inv ≫ V.ι ≫ j`, so restricting `G` along it
is restricting first along `V.ι ≫ j` — which is `j^* G` restricted to `V`, by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` — and then along an isomorphism,
which carries the free module to the free module on the same index. -/
public theorem nonempty_over_image_iso_free_of_pullback_restrict_iso_free
    {Y Z : Scheme.{u}} (j : Y ⟶ Z) [IsOpenImmersion j] (G : Z.Modules) (V : Y.Opens) (I : Type u)
    (e : ((Scheme.Modules.pullback j).obj G).restrict V.ι ≅
      SheafOfModules.free.{u} (R := (V : Scheme).ringCatSheaf) I) :
    Nonempty (G.over (j ''ᵁ V) ≅
      SheafOfModules.free.{u} (R := Z.ringCatSheaf.over (j ''ᵁ V)) I) := by
  set ψ : (j ''ᵁ V).toScheme ⟶ V.toScheme := (j.isoImage V).inv with hψ
  have : IsOpenImmersion ψ := by rw [hψ]; infer_instance
  have hfac : (j ''ᵁ V).ι = ψ ≫ V.ι ≫ j := (Scheme.Hom.isoImage_inv_ι j V).symm
  refine ⟨overIsoOfRestrictIso (j ''ᵁ V) I G ?_⟩
  exact (Scheme.Modules.restrictFunctorCongr hfac).app G ≪≫
    (Scheme.Modules.restrictFunctorComp ψ (V.ι ≫ j)).app G ≪≫
    (Scheme.Modules.restrictFunctor ψ).mapIso
      ((Scheme.Modules.restrictFunctorComp V.ι j).app G ≪≫
        (Scheme.Modules.restrictFunctor V.ι).mapIso
          ((Scheme.Modules.restrictFunctorIsoPullback j).app G) ≪≫ e) ≪≫
    restrictFunctor_obj_free_iso ψ I

end AlgebraicGeometry

end
