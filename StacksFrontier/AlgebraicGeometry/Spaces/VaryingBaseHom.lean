module

public import Mathlib.CategoryTheory.Comma.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace

/-!
# Morphisms of algebraic spaces over varying schemes (Stacks 04U8)

For algebraic spaces `X` and `Y` over schemes `U` and `V` in the big fppf site of `S`, a
morphism of pairs is a commutative square. Stacks 04U8 classifies such squares by a map
`U ⟶ V` of base schemes together with a map over `U` from `X` to the base change of `Y`.

This file carries the hom-set equation itself. The vocabulary it is phrased in — a scheme as
an algebraic space, the induced map of algebraic spaces, and the structure map of a comma
object read as a morphism of algebraic spaces — is already defined in
`StacksFrontier/AlgebraicGeometry/Spaces/SchemeAsSpace.lean`
(`AlgebraicGeometry.schemeSpace`, `.schemeSpaceMap`, `.commaHomAsSpaceMap`) and is imported
rather than restated.

## Main definitions

* `AlgebraicGeometry.pullbackOver`: the base change of an algebraic space along a map of its
  base scheme, as an object of the slice over the source scheme.

## Main results

* `AlgebraicGeometry.spaceHomEquivPullbackHom`: **Stacks 04U8**, the hom-set equation.

## Implementation notes

All algebraic spaces are presheaves on the one fixed big fppf site of `S`; the varying-base
category is the comma category of the inclusion of algebraic spaces over
`CategoryTheory.yoneda`, and the fibre product is the one in the category of algebraic spaces
(Stacks 02X2, `AlgebraicGeometry.AlgebraicSpaces.fiberProduct`), whose cartesian square is
`AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct`. The right-hand hom is taken in
the slice over `U`.

The equivalence is returned as a subtype: it is specified to retain the base map and to
recover the given map of spaces by projection from the pullback. Those two conditions are what
characterize the canonical correspondence rather than an arbitrary bijection of hom-sets, so
the bare `Equiv` is not the tagged statement.

The tag sits on `AlgebraicGeometry.spaceHomEquivPullbackHom` alone. `pullbackOver` and the
three imported definitions are the vocabulary the equation is phrased in, not part of its
content, so they are left untagged.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 04U8](https://stacks.math.columbia.edu/tag/04U8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The base change of `C` along a map to its base, as an object over the
source scheme. -/
noncomputable def pullbackOver
    (A C : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤
        (BigFppfOver B S hS)ᵒᵖ ⥤ Type u))
    (g : A.right ⟶ C.right) : Over (schemeSpace A.right) :=
  Over.mk (ObjectProperty.homMk
    (pullback.fst (schemeSpaceMap g).hom C.hom) :
    AlgebraicSpaces.fiberProduct B S hS (schemeSpaceMap g)
      (ObjectProperty.homMk C.hom) ⟶ schemeSpace A.right)

/-- The hom-set equation for algebraic spaces over varying representable bases. -/
@[stacks 04U8]
noncomputable def spaceHomEquivPullbackHom
    (A C : Comma
      (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F))
      (yoneda : BigFppfOver B S hS ⥤
        (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)) :
    { e : (A ⟶ C) ≃
        Σ g : A.right ⟶ C.right,
          (Over.mk (ObjectProperty.homMk A.hom : A.left ⟶
            schemeSpace A.right) ⟶ pullbackOver A C g) //
      ∀ m : A ⟶ C, (e m).1 = m.right ∧
        ((e m).2).left ≫
          (ObjectProperty.homMk
            (pullback.snd (schemeSpaceMap (e m).1).hom C.hom) :
              AlgebraicSpaces.fiberProduct B S hS
                (schemeSpaceMap (e m).1) (ObjectProperty.homMk C.hom) ⟶
                C.left) = m.left } := by
  let aMap : A.left ⟶ schemeSpace A.right := commaHomAsSpaceMap A
  let hpb (g : A.right ⟶ C.right) :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS (schemeSpaceMap g) (commaHomAsSpaceMap C)
  let fstMap (g : A.right ⟶ C.right) : (pullbackOver A C g).left ⟶ schemeSpace A.right :=
    ObjectProperty.homMk (pullback.fst (schemeSpaceMap g).hom (commaHomAsSpaceMap C).hom)
  let sndMap (g : A.right ⟶ C.right) : (pullbackOver A C g).left ⟶ C.left :=
    ObjectProperty.homMk (pullback.snd (schemeSpaceMap g).hom (commaHomAsSpaceMap C).hom)
  have compatible (m : A ⟶ C) :
      aMap ≫ schemeSpaceMap m.right = m.left ≫ commaHomAsSpaceMap C := by
    apply ObjectProperty.hom_ext
    change A.hom ≫ yoneda.map m.right = m.left.hom ≫ C.hom
    simpa [schemeSpaceMap, schemeSpace, aMap, commaHomAsSpaceMap] using m.w.symm
  let liftMap (m : A ⟶ C) : A.left ⟶ (pullbackOver A C m.right).left :=
    (hpb m.right).lift aMap m.left (compatible m)
  have liftSnd (m : A ⟶ C) : liftMap m ≫ sndMap m.right = m.left :=
    (hpb m.right).lift_snd _ _ (compatible m)
  let toFun (m : A ⟶ C) : Σ g : A.right ⟶ C.right, (Over.mk aMap ⟶ pullbackOver A C g) :=
    ⟨m.right, Over.homMk (liftMap m)
      ((hpb m.right).lift_fst _ _ (compatible m))⟩
  let invFun (z : Σ g : A.right ⟶ C.right, (Over.mk aMap ⟶ pullbackOver A C g)) : A ⟶ C :=
    ⟨z.2.left ≫ sndMap z.1, z.1, by
      have heq : z.2.left ≫ fstMap z.1 ≫ schemeSpaceMap z.1 =
          z.2.left ≫ sndMap z.1 ≫ commaHomAsSpaceMap C :=
        z.2.left ≫= (hpb z.1).w
      have hbase : aMap ≫ schemeSpaceMap z.1 = z.2.left ≫ sndMap z.1 ≫ commaHomAsSpaceMap C :=
        calc
          aMap ≫ schemeSpaceMap z.1 = (z.2.left ≫ fstMap z.1) ≫ schemeSpaceMap z.1 :=
            (congrArg (· ≫ schemeSpaceMap z.1) (Over.w z.2)).symm
          _ = z.2.left ≫ sndMap z.1 ≫ commaHomAsSpaceMap C := by
            simpa using heq
      have hh := (congrArg (·.hom) hbase).symm
      change (z.2.left ≫ sndMap z.1).hom ≫ C.hom = A.hom ≫ yoneda.map z.1 at hh ⊢
      simpa [schemeSpaceMap, schemeSpace, sndMap, commaHomAsSpaceMap] using hh⟩
  let e : (A ⟶ C) ≃ Σ g : A.right ⟶ C.right, (Over.mk aMap ⟶ pullbackOver A C g) :=
    { toFun := toFun
      invFun := invFun
      left_inv := fun m => Comma.hom_ext _ _ (liftSnd m) rfl
      right_inv := by
        rintro ⟨g, k⟩
        dsimp [toFun, invFun]
        refine Sigma.ext rfl (heq_of_eq ?_)
        apply Over.OverMorphism.ext
        apply (hpb g).hom_ext
        · change (hpb g).lift aMap (k.left ≫ sndMap g) _ ≫ fstMap g = k.left ≫ fstMap g
          exact ((hpb g).lift_fst _ _ _).trans (Over.w k).symm
        · change (hpb g).lift aMap (k.left ≫ sndMap g) _ ≫ sndMap g = k.left ≫ sndMap g
          exact (hpb g).lift_snd _ _ _ }
  exact ⟨e, fun m => ⟨rfl, liftSnd m⟩⟩

end AlgebraicGeometry

end
