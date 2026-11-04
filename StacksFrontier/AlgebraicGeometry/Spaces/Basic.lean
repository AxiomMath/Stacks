module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Algebraic spaces over a scheme

An *algebraic space* over a scheme `S` contained in a big fppf site `B` is a presheaf of
sets on the big fppf site of `S` which is a sheaf, has representable diagonal, and admits a
surjective étale morphism from a representable presheaf.

The scheme over the base is an object of the slice site
`AlgebraicGeometry.BigFppfOver B S hS`, so `S`-schemes and the size cutoff of `B` are both
recorded in the ambient category rather than in the predicate. Representability of the
diagonal and of the atlas is relative to the Yoneda embedding of that slice, in the sense
of `CategoryTheory.Functor.relativelyRepresentable`. Surjectivity and étaleness of the
atlas are expressed with `CategoryTheory.MorphismProperty.presheaf`, which tests the
property after every representable base change; the properties so tested are the inverse
images along `AlgebraicGeometry.BigFppfOver.toScheme` of Mathlib's
`AlgebraicGeometry.Surjective` and `AlgebraicGeometry.Etale`. Consequently a user may apply
the `exists_atlas` field either to the atlas itself or to any of its represented pullbacks.

## Main definitions

* `AlgebraicGeometry.IsAlgebraicSpace` is the property of a presheaf on the big fppf site
  of `S` that it is an algebraic space over `S`.

## Main results

There are no propositional results. The projections of
`AlgebraicGeometry.IsAlgebraicSpace` give its sheaf condition, its representable diagonal,
and its surjective étale scheme atlas.

## References

* [Stacks Project, Tag 025Y](https://stacks.math.columbia.edu/tag/025Y)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The product of a sheaf on the big fppf site with itself is a sheaf. -/
public theorem isSheaf_prod_self (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (F ⨯ F) := by
  let Fs : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨F, hF⟩
  exact Sheaf.isSheaf_of_isLimit (F := pair Fs Fs)
    (E := (Cone.postcompose (pairComp Fs Fs (sheafToPresheaf _ (Type u))).inv).obj
      (BinaryFan.mk (prod.fst (X := Fs.obj) (Y := Fs.obj)) prod.snd))
    ((IsLimit.postcomposeInvEquiv _ _).symm (prodIsProd Fs.obj Fs.obj))

/-- Being an affine morphism of schemes is Zariski-local at the target.  Mathlib proves the
affine-property version and derives this from it, but instance search cannot connect the two
without being told which affine property to use. -/
@[sga "3 XIX 5.13" "Reduction step"]
public theorem isZariskiLocalAtTarget_isAffineHom :
    IsZariskiLocalAtTarget (@IsAffineHom.{u} : MorphismProperty Scheme.{u}) :=
  @HasAffineProperty.instIsZariskiLocalAtTarget _ _ instHasAffinePropertyIsAffineHomIsAffine

/-- Transporting a subfunctor along an equality and then including it is the original
inclusion. -/
public lemma subfunctor_eqToHom_ι {C : Type*} [Category C] {F : C ⥤ Type*}
    {G H : Subfunctor F} (e : G = H) :
    eqToHom (congrArg Subfunctor.toFunctor e) ≫ H.ι = G.ι := by
  cases e
  simp

/-- Étale morphisms of schemes are stable under composition.  Mathlib proves the stronger
`MorphismProperty.IsMultiplicative` for them but does not expose this half as an instance. -/
@[sga "1 I 4.6"]
public instance etale_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition (@Etale.{u}) :=
  (inferInstance : MorphismProperty.IsMultiplicative (@Etale.{u})).toIsStableUnderComposition

/-- Étale morphisms of schemes are invariant under isomorphism, by Mathlib's stability under
base change. -/
public instance etale_respectsIso :
    MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- **Stacks 025Y.** A presheaf of sets on the big fppf site of `S` is an *algebraic space*
over `S` when it is an fppf sheaf, has representable diagonal, and admits a surjective
étale morphism from a representable presheaf. -/
@[stacks 025Y]
structure IsAlgebraicSpace (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) : Prop where
  /-- The fppf sheaf condition. -/
  isSheaf : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F
  /-- Representability of the diagonal. -/
  diagonal_representable : yoneda.relativelyRepresentable (diag F)
  /-- A scheme atlas, surjective and étale after every representable base change. -/
  exists_atlas : ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f

end AlgebraicGeometry

end
