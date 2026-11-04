module

public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedDirectImageAlgebraFactorization

/-!
# The base-change comparison of a direct-image algebra

Let `g : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `Z` be an algebraic space over `X` with structure morphism `f`, and let `W` be an
algebraic space over `Y` with structure morphism `f'`, together with a morphism `p : W ⟶ Z`
making

```
W ⟶ Z
↓f'   ↓f
Y ⟶ X
```

commute.  `AlgebraicGeometry.Space.pushforwardSquareMap` is the comparison
`f_* 𝒪_Z ⟶ g_* (f'_* 𝒪_W)` that `p` induces on direct images.  This file transposes it across
the inverse-image/direct-image adjunction of sheaves of commutative rings, producing the
*base-change comparison*

`g⁻¹ (f_* 𝒪_Z) ⟶ f'_* 𝒪_W`,

and shows that transposing back returns `pushforwardSquareMap`, which pins the comparison down
uniquely.  It then extends scalars along `g♯ : g⁻¹𝒪_X ⟶ 𝒪_Y`, giving the comparison of
`𝒪_Y`-algebras

`g^* (f_* 𝒪_Z) = 𝒪_Y ⊗_{g⁻¹𝒪_X} g⁻¹ (f_* 𝒪_Z) ⟶ f'_* 𝒪_W`

whose being an isomorphism is the base-change clause of Stacks 081V.  This file builds the map,
shows that it is canonical and respects the algebra structures, with no anti-equivalence of
Stacks 081V assumed; that it is an isomorphism is
`AlgebraicGeometry.Space.isIso_affineOverBaseChangeAlgebraHom`, downstream.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardSquareBaseChangeMap` is the base-change comparison
  `g⁻¹ (f_* 𝒪_Z) ⟶ f'_* 𝒪_W` attached to a commutative square, as the adjunct of
  `AlgebraicGeometry.Space.pushforwardSquareMap`.
* `AlgebraicGeometry.Space.pushforwardBaseChangeMap` is its value at the base change
  `AlgebraicGeometry.Space.affineOverBaseChange` of an algebraic space affine over `X`.
* `AlgebraicGeometry.Space.baseChangeAlgebraHom` is the comparison of `𝒪_Y`-algebras
  `g^* (f_* 𝒪_Z) ⟶ f'_* 𝒪_W` obtained from it by extension of scalars.

## Main results

* `AlgebraicGeometry.Space.pushforwardSquareBaseChangeMap_canonical`: the adjunct of the
  base-change comparison is `AlgebraicGeometry.Space.pushforwardSquareMap`.
* `AlgebraicGeometry.Space.eq_pushforwardSquareBaseChangeMap`: that property determines it, so
  "the" base-change comparison is a definite description rather than a choice.
* `AlgebraicGeometry.Space.inverseImage_fSharp_comp_pushforwardSquareBaseChangeMap`: the
  base-change comparison carries the inverse image of the structure map of `f` to the
  inverse-image form of the structure map of `g` followed by that of `f'`.  This is the
  transpose of `AlgebraicGeometry.Space.fSharp_comp_pushforwardSquareMap`, and it is what lets
  the comparison be extended to the algebra pullback.
* `AlgebraicGeometry.Space.pushforwardBaseChangeMap_canonical`: the same canonicity at the
  geometric base change of an algebraic space affine over `X`.

## Implementation notes

`AlgebraicGeometry.Space.pushforwardSquareBaseChangeMap` and
`AlgebraicGeometry.Space.pushforwardBaseChangeMap_canonical` have exactly the types of the
fields of those names of `AlgebraicGeometry.Space.BaseChangeCompatibility`, with the
`affineBaseChange` field read as `AlgebraicGeometry.Space.affineOverBaseChange`; that structure
carries them as data because they had not been constructed.  Three further fields of it —
`algebraPullback`, `algebraPullbackMap` and `algebraPullback_isPushout` — are constructed in
`StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullback`, and three more —
`affineBaseChange` at an object, `affineBaseChange_projection` and
`affineBaseChange_isPullback` — in
`StacksFrontier.AlgebraicGeometry.Spaces.BoundedDirectImageAlgebraFactorization`.  Nothing here
hypothesises an anti-equivalence, so nothing here is weakened by the size obstruction of
`AlgebraicGeometry.Space.not_nonempty_affineAlgebraAntiEquivalence_of_hasNonzeroAffineChart`.

The adjunction is `Stacks.Sheaves.ToposPushforward.commRingImageAdjunction`, the same one
through which `AlgebraicGeometry.RingedToposHom.fSharpInverseImage` is the adjunct of `f♯`; that
definitional identity is why
`AlgebraicGeometry.Space.inverseImage_fSharp_comp_pushforwardSquareBaseChangeMap` follows from
`AlgebraicGeometry.Space.fSharp_comp_pushforwardSquareMap` by the two naturality squares of the
adjunction and nothing else.

The hypothesis of the algebra comparison is stated with
`AlgebraicGeometry.Space.ringSheafPullback` and
`AlgebraicGeometry.Space.structurePullbackMap`, the spellings that
`AlgebraicGeometry.Space.algebraPullback_isPushout` presents its pushout at, rather than with
`Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor` and
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage`, which are the same maps by definition but
not by syntax.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The comparison attached to a commutative square -/

/-- **The base-change comparison `g⁻¹ (f_* 𝒪_Z) ⟶ f'_* 𝒪_W` of a commutative square**

```
W ⟶ Z
↓f'   ↓f
Y ⟶ X
```

over `g : Y ⟶ X`, with top projection `p : W ⟶ Z`: the adjunct of the direct-image comparison
`AlgebraicGeometry.Space.pushforwardSquareMap` across the inverse-image/direct-image adjunction
of sheaves of commutative rings on the small étale sites.

This has the type of the `pushforwardBaseChangeMap` field of
`AlgebraicGeometry.Space.BaseChangeCompatibility` for an arbitrary square, and needs no
anti-equivalence of Stacks 081V and no base-change compatibility. -/
def pushforwardSquareBaseChangeMap (g : Y ⟶ X) (Z : Over X) (W : Over Y)
    (p : W.left ⟶ Z.left) (hw : p ≫ Z.hom = W.hom ≫ g) :
    (inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS g).toToposHom).obj
        (pushforwardAlgebra B S hS Z).right ⟶
      (pushforwardAlgebra B S hS W).right :=
  ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
      (pushforwardAlgebra B S hS Z).right
      (pushforwardAlgebra B S hS W).right).symm
    (pushforwardSquareMap B S hS g Z W p hw)

/-- **The base-change comparison is adjoint to the direct-image comparison of the square.**
Transposing `AlgebraicGeometry.Space.pushforwardSquareBaseChangeMap` back across the adjunction
returns `AlgebraicGeometry.Space.pushforwardSquareMap`.

This is the `pushforwardBaseChangeMap_canonical` field of
`AlgebraicGeometry.Space.BaseChangeCompatibility` for an arbitrary square. -/
theorem pushforwardSquareBaseChangeMap_canonical (g : Y ⟶ X) (Z : Over X) (W : Over Y)
    (p : W.left ⟶ Z.left) (hw : p ≫ Z.hom = W.hom ≫ g) :
    (commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
        (pushforwardAlgebra B S hS Z).right
        (pushforwardAlgebra B S hS W).right
        (pushforwardSquareBaseChangeMap B S hS g Z W p hw) =
      pushforwardSquareMap B S hS g Z W p hw :=
  Equiv.apply_symm_apply _ _

/-- **Being adjoint to the direct-image comparison determines the base-change comparison**, the
adjunction being a bijection on morphisms.  So `AlgebraicGeometry.Space.pushforwardSquareMap`
is "the" base-change comparison of the square, a definite description rather than a choice. -/
theorem eq_pushforwardSquareBaseChangeMap (g : Y ⟶ X) (Z : Over X) (W : Over Y)
    (p : W.left ⟶ Z.left) (hw : p ≫ Z.hom = W.hom ≫ g)
    (φ : (inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
            (smallEtaleRingedToposHom B S hS g).toToposHom).obj
          (pushforwardAlgebra B S hS Z).right ⟶
        (pushforwardAlgebra B S hS W).right)
    (hφ : (commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
        (pushforwardAlgebra B S hS Z).right
        (pushforwardAlgebra B S hS W).right φ =
      pushforwardSquareMap B S hS g Z W p hw) :
    φ = pushforwardSquareBaseChangeMap B S hS g Z W p hw :=
  ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
      (pushforwardAlgebra B S hS Z).right
      (pushforwardAlgebra B S hS W).right).injective
    (hφ.trans (pushforwardSquareBaseChangeMap_canonical B S hS g Z W p hw).symm)

/-! ### The comparison respects the algebra structures -/

/-- **The base-change comparison is a map of algebras over the inverse image of `𝒪_X`.**  The
inverse image of the structure map `f♯ : 𝒪_X ⟶ f_* 𝒪_Z`, followed by the base-change
comparison, is the inverse-image form `g♯ : g⁻¹𝒪_X ⟶ 𝒪_Y` of the structure map of `g` followed
by the structure map `f'♯ : 𝒪_Y ⟶ f'_* 𝒪_W`.

This is the transpose of `AlgebraicGeometry.Space.fSharp_comp_pushforwardSquareMap`: the two
naturality squares of the adjunction carry each side to a side of that equation, the right-hand
one using that `AlgebraicGeometry.RingedToposHom.fSharpInverseImage` is by definition the
adjunct of `f♯`.

It is the compatibility that `AlgebraicGeometry.Space.algebraPullback_isPushout` consumes, so
it is what makes `AlgebraicGeometry.Space.baseChangeAlgebraHom` exist. -/
theorem inverseImage_fSharp_comp_pushforwardSquareBaseChangeMap (g : Y ⟶ X) (Z : Over X)
    (W : Over Y) (p : W.left ⟶ Z.left) (hw : p ≫ Z.hom = W.hom ≫ g) :
    (ringSheafPullback B S hS g).map (pushforwardAlgebra B S hS Z).hom ≫
        pushforwardSquareBaseChangeMap B S hS g Z W p hw =
      structurePullbackMap B S hS g ≫ (pushforwardAlgebra B S hS W).hom := by
  have key :
      ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv _ _)
          ((inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
                (smallEtaleRingedToposHom B S hS g).toToposHom).map
              (pushforwardAlgebra B S hS Z).hom ≫
            pushforwardSquareBaseChangeMap B S hS g Z W p hw) =
        ((commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv _ _)
          (((commRingImageAdjunction
                  (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv _ _).symm
              (smallEtaleRingedToposHom B S hS g).fSharp ≫
            (pushforwardAlgebra B S hS W).hom) := by
    rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
      pushforwardSquareBaseChangeMap_canonical, Equiv.apply_symm_apply]
    exact fSharp_comp_pushforwardSquareMap B S hS g Z W p hw
  exact ((commRingImageAdjunction
    (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv _ _).injective key

/-- **The base-change comparison of `𝒪_Y`-algebras**

`g^* (f_* 𝒪_Z) = 𝒪_Y ⊗_{g⁻¹𝒪_X} g⁻¹ (f_* 𝒪_Z) ⟶ f'_* 𝒪_W`,

obtained from `AlgebraicGeometry.Space.pushforwardSquareBaseChangeMap` by extension of scalars
along `g♯`: algebra pullback is a pushout, by
`AlgebraicGeometry.Space.algebraPullback_isPushout`, and the base-change comparison together
with the structure map of `f'` is a cocone on it, by
`AlgebraicGeometry.Space.inverseImage_fSharp_comp_pushforwardSquareBaseChangeMap`.

For the geometric base change of an algebraic space affine over `X` this is an isomorphism, by
`AlgebraicGeometry.Space.isIso_affineOverBaseChangeAlgebraHom`; for an arbitrary commutative
square it need not be. -/
def baseChangeAlgebraHom (g : Y ⟶ X) (Z : Over X) (W : Over Y) (p : W.left ⟶ Z.left)
    (hw : p ≫ Z.hom = W.hom ≫ g) :
    ((algebraPullback B S hS g).obj (pushforwardAlgebra B S hS Z)).right ⟶
      (pushforwardAlgebra B S hS W).right :=
  (algebraPullback_isPushout B S hS g (pushforwardAlgebra B S hS Z)).desc
    (pushforwardSquareBaseChangeMap B S hS g Z W p hw)
    (pushforwardAlgebra B S hS W).hom
    (inverseImage_fSharp_comp_pushforwardSquareBaseChangeMap B S hS g Z W p hw)

/-- The algebra comparison restricts on the inverse image of `f_* 𝒪_Z` to the base-change
comparison. -/
theorem algebraPullbackMap_comp_baseChangeAlgebraHom (g : Y ⟶ X) (Z : Over X) (W : Over Y)
    (p : W.left ⟶ Z.left) (hw : p ≫ Z.hom = W.hom ≫ g) :
    (algebraPullbackMap B S hS g).app (pushforwardAlgebra B S hS Z) ≫
        baseChangeAlgebraHom B S hS g Z W p hw =
      pushforwardSquareBaseChangeMap B S hS g Z W p hw :=
  IsPushout.inl_desc _ _ _ _

/-- **The algebra comparison is a map of `𝒪_Y`-algebras**: precomposing it with the structure
map of the algebra pullback gives the structure map `f'♯ : 𝒪_Y ⟶ f'_* 𝒪_W`. -/
theorem baseChangeAlgebraHom_structure (g : Y ⟶ X) (Z : Over X) (W : Over Y)
    (p : W.left ⟶ Z.left) (hw : p ≫ Z.hom = W.hom ≫ g) :
    ((algebraPullback B S hS g).obj (pushforwardAlgebra B S hS Z)).hom ≫
        baseChangeAlgebraHom B S hS g Z W p hw =
      (pushforwardAlgebra B S hS W).hom :=
  IsPushout.inr_desc _ _ _ _

/-- The algebra comparison as a morphism of algebra sheaves. -/
def baseChangeAlgebraSheafHom (g : Y ⟶ X) (Z : Over X) (W : Over Y) (p : W.left ⟶ Z.left)
    (hw : p ≫ Z.hom = W.hom ≫ g) :
    (algebraPullback B S hS g).obj (pushforwardAlgebra B S hS Z) ⟶
      pushforwardAlgebra B S hS W :=
  AlgebraSheaf.ofHomMap (baseChangeAlgebraHom B S hS g Z W p hw)
    (baseChangeAlgebraHom_structure B S hS g Z W p hw)

/-! ### The comparison at the geometric base change -/

/-- **The base-change comparison at the base change `Y ×_X Z` of an algebraic space `Z` affine
over `X`**: the value of `AlgebraicGeometry.Space.pushforwardSquareBaseChangeMap` at the
cartesian square of `AlgebraicGeometry.Space.affineOverBaseChange`.

This has the type of the `pushforwardBaseChangeMap` field of
`AlgebraicGeometry.Space.BaseChangeCompatibility` with its `affineBaseChange` field read as
`AlgebraicGeometry.Space.affineOverBaseChange`, and needs no anti-equivalence of Stacks 081V. -/
def pushforwardBaseChangeMap (g : Y ⟶ X) (Z : AffineOver B S hS X) :
    (inverseImageCommRingFunctor.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS g).toToposHom).obj
        (pushforwardAlgebra B S hS Z.obj).right ⟶
      (pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).right :=
  pushforwardSquareBaseChangeMap B S hS g Z.obj (affineOverBaseChange B S hS g Z).obj
    (affineOverBaseChangeProjection B S hS g Z)
    (affineOverBaseChange_isPullback B S hS g Z).w

/-- **The base-change comparison at the geometric base change is adjoint to the map induced by
the cartesian projection on structure sheaves.**

This is the `pushforwardBaseChangeMap_canonical` field of
`AlgebraicGeometry.Space.BaseChangeCompatibility` with its `affineBaseChange`,
`affineBaseChange_projection` and `affineBaseChange_isPullback` fields read as
`AlgebraicGeometry.Space.affineOverBaseChange`,
`AlgebraicGeometry.Space.affineOverBaseChangeProjection` and
`AlgebraicGeometry.Space.affineOverBaseChange_isPullback`. -/
theorem pushforwardBaseChangeMap_canonical (g : Y ⟶ X) (Z : AffineOver B S hS X) :
    (commRingImageAdjunction (smallEtaleRingedToposHom B S hS g).toToposHom).homEquiv
        (pushforwardAlgebra B S hS Z.obj).right
        (pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj).right
        (pushforwardBaseChangeMap B S hS g Z) =
      pushforwardSquareMap B S hS g Z.obj (affineOverBaseChange B S hS g Z).obj
        (affineOverBaseChangeProjection B S hS g Z)
        (affineOverBaseChange_isPullback B S hS g Z).w :=
  pushforwardSquareBaseChangeMap_canonical B S hS g Z.obj _ _ _

/-- **The base-change comparison of `𝒪_Y`-algebras at the geometric base change**

`g^* (f_* 𝒪_Z) ⟶ (Y ×_X Z ⟶ Y)_* 𝒪_{Y ×_X Z}`

for `Z` affine over `X`.  It is an isomorphism, the base-change clause of Stacks 081V:
`AlgebraicGeometry.Space.isIso_affineOverBaseChangeAlgebraHom`. -/
def affineOverBaseChangeAlgebraHom (g : Y ⟶ X) (Z : AffineOver B S hS X) :
    (algebraPullback B S hS g).obj (pushforwardAlgebra B S hS Z.obj) ⟶
      pushforwardAlgebra B S hS (affineOverBaseChange B S hS g Z).obj :=
  baseChangeAlgebraSheafHom B S hS g Z.obj (affineOverBaseChange B S hS g Z).obj
    (affineOverBaseChangeProjection B S hS g Z)
    (affineOverBaseChange_isPullback B S hS g Z).w

end AlgebraicGeometry.Space

end
