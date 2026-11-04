module

public import StacksFrontier.AlgebraicGeometry.PushforwardColimits.Gamma

/-!
# Direct image between affine schemes commutes with colimits of quasi-coherent modules

`Stacks.AlgebraicGeometry.PushforwardColimits.preservesColimit_pushforward_specMap` is the
statement for a morphism of the form `Spec.map φ`.  This file conjugates it with
`AlgebraicGeometry.Scheme.isoSpec` to get the statement for an arbitrary morphism between affine
schemes.  The conjugation needs that the direct image along an *isomorphism* of schemes is an
equivalence of categories of modules, which is proved here and is of independent use.

## Main definitions

* `Stacks.AlgebraicGeometry.PushforwardColimits.pushforwardEquiv`: the direct image along an
  isomorphism of schemes, as an equivalence between the categories of modules.

## Main results

* `Stacks.AlgebraicGeometry.PushforwardColimits.isEquivalence_pushforward_of_isIso`: the direct
  image along an isomorphism of schemes is an equivalence; in particular it preserves all
  colimits and all limits.
* `Stacks.AlgebraicGeometry.PushforwardColimits.preservesColimit_pushforward_of_isAffine`: the
  direct image along a morphism between affine schemes preserves the colimit of a diagram of
  quasi-coherent modules.

## Implementation notes

The equivalence is `CategoryTheory.Equivalence.mk`, which adjusts the unit so that no coherence
has to be proved: the two composites of the direct images along `e.hom` and `e.inv` are
isomorphic to the identity functors by `AlgebraicGeometry.Scheme.Modules.pushforwardComp`,
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr` and
`AlgebraicGeometry.Scheme.Modules.pushforwardId`, and that is all that is supplied.

The factorisation of an arbitrary morphism of affine schemes is the one used by
`Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_pushforward_of_isAffine`, namely
`g = Y.isoSpec.hom ≫ (Spec.map g.appTop ≫ Z.isoSpec.inv)`; the quasi-coherence of the diagram
transported to `Spec Γ(Y, ⊤)` is
`Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_pushforward_of_isIso`.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe v₂ u₂ u

noncomputable section

namespace Stacks.AlgebraicGeometry.PushforwardColimits

variable {Y Z : Scheme.{u}}

/-! ### Direct image along an isomorphism of schemes -/

/-- For an isomorphism `e : Y ≅ Z` of schemes, the direct image along `e.hom` followed by the
direct image along `e.inv` is the identity. -/
def pushforwardCompHomInv (e : Y ≅ Z) :
    Scheme.Modules.pushforward e.hom ⋙ Scheme.Modules.pushforward e.inv ≅ 𝟭 Y.Modules :=
  Scheme.Modules.pushforwardComp e.hom e.inv ≪≫
    Scheme.Modules.pushforwardCongr e.hom_inv_id ≪≫ Scheme.Modules.pushforwardId Y

/-- For an isomorphism `e : Y ≅ Z` of schemes, the direct image along `e.inv` followed by the
direct image along `e.hom` is the identity. -/
def pushforwardCompInvHom (e : Y ≅ Z) :
    Scheme.Modules.pushforward e.inv ⋙ Scheme.Modules.pushforward e.hom ≅ 𝟭 Z.Modules :=
  Scheme.Modules.pushforwardComp e.inv e.hom ≪≫
    Scheme.Modules.pushforwardCongr e.inv_hom_id ≪≫ Scheme.Modules.pushforwardId Z

/-- **The direct image along an isomorphism of schemes is an equivalence** between the categories
of modules, with quasi-inverse the direct image along the inverse isomorphism. -/
def pushforwardEquiv (e : Y ≅ Z) : Y.Modules ≌ Z.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward e.hom)
    (Scheme.Modules.pushforward e.inv)
    (pushforwardCompHomInv e).symm (pushforwardCompInvHom e)

/-- The direct image along an invertible morphism of schemes is an equivalence.  In particular it
preserves all colimits. -/
instance isEquivalence_pushforward_of_isIso (g : Y ⟶ Z) [IsIso g] :
    (Scheme.Modules.pushforward g).IsEquivalence :=
  (pushforwardEquiv (asIso g)).isEquivalence_functor

/-! ### Direct image between affine schemes -/

variable {K : Type u₂} [Category.{v₂} K] [HasColimitsOfShape K AddCommGrpCat.{u}]
  [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
  [∀ W : Scheme.{u}, HasColimitsOfShape K W.Modules]

/-- **The direct image along a morphism of affine schemes preserves colimits of quasi-coherent
modules.**  The morphism is factored as an isomorphism, a morphism of spectra and an
isomorphism; the two isomorphisms contribute equivalences and the middle factor is
`preservesColimit_pushforward_specMap`. -/
theorem preservesColimit_pushforward_of_isAffine [IsAffine Y] [IsAffine Z] (g : Y ⟶ Z)
    {D : K ⥤ Y.Modules} (hD : ∀ k, (D.obj k).IsQuasicoherent) :
    PreservesColimit D (Scheme.Modules.pushforward g) := by
  have key : g = Y.isoSpec.hom ≫ (Spec.map g.appTop ≫ Z.isoSpec.inv) := by
    rw [Scheme.isoSpec_inv_naturality, Iso.hom_inv_id_assoc]
  have e : Scheme.Modules.pushforward g ≅
      Scheme.Modules.pushforward Y.isoSpec.hom ⋙
        (Scheme.Modules.pushforward (Spec.map g.appTop) ⋙
          Scheme.Modules.pushforward Z.isoSpec.inv) :=
    Scheme.Modules.pushforwardCongr key ≪≫ (Scheme.Modules.pushforwardComp _ _).symm ≪≫
      Functor.isoWhiskerLeft _ (Scheme.Modules.pushforwardComp _ _).symm
  have hD1 : ∀ k, ((D ⋙ Scheme.Modules.pushforward Y.isoSpec.hom).obj k).IsQuasicoherent :=
    fun k ↦
      have := hD k
      AffinePushforward.isQuasicoherent_pushforward_of_isIso Y.isoSpec (D.obj k)
  have hmid : PreservesColimit (D ⋙ Scheme.Modules.pushforward Y.isoSpec.hom)
      (Scheme.Modules.pushforward (Spec.map g.appTop)) :=
    preservesColimit_pushforward_specMap g.appTop hD1
  have hcomp : PreservesColimit D
      (Scheme.Modules.pushforward Y.isoSpec.hom ⋙
        (Scheme.Modules.pushforward (Spec.map g.appTop) ⋙
          Scheme.Modules.pushforward Z.isoSpec.inv)) :=
    inferInstance
  exact preservesColimit_of_natIso D e.symm

end Stacks.AlgebraicGeometry.PushforwardColimits

end

end
