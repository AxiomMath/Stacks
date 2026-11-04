module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHomInverseImage
public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftDifferenceRingSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.ThickeningSharpLiftBaseAgreement

/-!
# The derivation attached to a linear map kills the functions read from the ambient base

Let `W₀ ⊆ W` be a closed subspace of an algebraic space over a scheme `S` with inclusion
`j : W₀ ⟶ W`, let `qb : W ⟶ Bas` and let `b : W₀ ⟶ Bas₀` be a morphism fitting a commutative
square `j ≫ qb = b ≫ iB` over a morphism `iB : Bas₀ ⟶ Bas`.  Let `e₀ : Xx ⟶ W₀` and let
`θ : e₀^*Ω_{W₀/Bas₀} ⟶ C` be an `𝒪_{Xx}`-linear map.

The `𝒪_{Bas₀}`-derivation `D = d_{W₀/Bas₀} ∘ θ` attached to `θ` by
Equation [Stacks Project, Tag 0619] kills the values of `b^♯`, which is the field `d_app` of that
equation.  This file records what that says about the functions read from the **ambient** base
`Bas` along `qb`: those are, on the small étale site of `W₀`, values of `b^♯` too, by the square,
so `D` kills them as well.

That is the one geometric input of the existence clause of [Stacks Project, Tag 04D0] in
comorphism form: it is exactly the hypothesis under which the morphism of charts attached to the
moved solution of the lifting problem is a morphism over `Bas`
(`AlgebraicGeometry.Space.exists_hom_of_thickeningLiftRingSheaf`).

## Main results

* `AlgebraicGeometry.Space.app_structureSharpInverseImage_square`: **[Stacks Project, Tag 03G8]
  for a commuting square, read on a section** — the identification `p⁻¹f⁻¹𝒪_Y ≅ g⁻¹q⁻¹𝒪_Y`
  carries the one composite structure map to the other.
* `AlgebraicGeometry.Space.derivationFamilyOfHom_app_inverseImage_eq_zero`: **the derivation
  attached to `θ` kills every regular function read from the ambient base `Bas` along `qb`.**

## Implementation notes

`AlgebraicGeometry.Space.app_structureSharpInverseImage_square` is the generic square; the
groupoid instance of [Stacks Project, Tag 0CKE] proves the same statement at its own square
(`AlgebraicGeometry.GroupoidInAlgebraicSpaces.app_structureSharpInverseImage_square`, with
`iB` the inclusion of the thickened base).

The square is kept with a general `iB : Bas₀ ⟶ Bas` rather than specialized to an identity: the
two situations in which this is used are [Stacks Project, Tag 04D0], where the base of the
differentials is the base of the thickenings and `iB` is an identity, and
[Stacks Project, Tag 0CKE], where it is the inclusion of a first order thickening of the base.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the structure map.
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618), the difference of two
  lifts.
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619), the derivation attached
  to a linear map.
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0), the tag whose existence
  clause this is an input of.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sites Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Stacks 03G8 for a commuting square, on a section -/

section Square

variable {U V X Y : AlgebraicSpaces B S hS}

/-- **[Stacks Project, Tag 03G8] for a commuting square, read on a section.**  For
`p ≫ f = g ≫ q` the identification `p⁻¹f⁻¹𝒪_Y ≅ g⁻¹q⁻¹𝒪_Y` of
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_squareInverseImageRingIso` carries the
composite structure map through `q` and `g` to the composite structure map through `f` and `p`.

This is
`AlgebraicGeometry.Space.smallEtaleRingedToposHom_squareInverseImageRingIso_fSharpInverseImage`
evaluated at a section. -/
theorem app_structureSharpInverseImage_square {p : U ⟶ X} {f : X ⟶ Y} {g : U ⟶ V} {q : V ⟶ Y}
    (h : p ≫ f = g ≫ q) (A : (SmallEtale B S hS U.1)ᵒᵖ)
    (w : ToType (((smallEtaleInverseImageRing B S hS p).obj
      (inverseImageStructureSheaf B S hS f)).obj.obj A)) :
    (structureSharpInverseImage B S hS g).hom.app A
        (((smallEtaleInverseImageRing B S hS g).map
            (structureSharpInverseImage B S hS q)).hom.app A
          ((smallEtaleRingedToposHom_squareInverseImageRingIso B S hS h).hom.hom.app A w)) =
      (structureSharpInverseImage B S hS p).hom.app A
        (((smallEtaleInverseImageRing B S hS p).map
            (structureSharpInverseImage B S hS f)).hom.app A w) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (congrArg (fun m : (smallEtaleInverseImageRing B S hS p).obj
            (inverseImageStructureSheaf B S hS f) ⟶
          (smallEtaleRingedTopos B S hS U).O ↦ m.hom)
        (smallEtaleRingedToposHom_squareInverseImageRingIso_fSharpInverseImage B S hS h))
      A)
    w

end Square

/-! ### The derivation kills the functions read from the ambient base -/

section Vanishing

variable {W Bas Bas₀ : AlgebraicSpaces B S hS} (W₀ : ClosedSubspaces B S hS W.1)
  (qb : W ⟶ Bas) (iB : Bas₀ ⟶ Bas)
  (b : (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS) ⟶ Bas₀)
  (hsq : subspaceInclusion B S hS W W₀ ≫ qb = b ≫ iB)
  {Xx : AlgebraicSpaces B S hS}
  (e₀ : Xx ⟶ (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS))
  (Cm : Modules.{u, u} B S hS Xx.1 Xx.2)
  (θ : (modulePullback B S hS e₀).obj (sheafOfDifferentials B S hS b) ⟶ Cm)

include hsq in
/-- **The derivation attached to `θ` kills every regular function read from the ambient base
`Bas` along `qb`.**

A section of `j⁻¹(qb⁻¹𝒪_{Bas})` is carried by `j^♯` to a value of `b^♯ : b⁻¹𝒪_{Bas₀} ⟶ 𝒪_{W₀}`:
the two readings of the pullback — along `j ≫ qb` and along `b ≫ iB` — are identified by the
commutative square, which is
`AlgebraicGeometry.Space.app_structureSharpInverseImage_square`.  And the derivation attached to
`θ` kills the values of `b^♯`, which is the field `d_app` of Equation
[Stacks Project, Tag 0619]. -/
theorem derivationFamilyOfHom_app_inverseImage_eq_zero
    (A : (SmallEtale B S hS (⟨W₀.1.toFunctor, W₀.2.1⟩ : AlgebraicSpaces B S hS).1)ᵒᵖ)
    (x : ToType (((smallEtaleInverseImageRing B S hS
        (subspaceInclusion B S hS W W₀)).obj
      (inverseImageStructureSheaf B S hS qb)).obj.obj A)) :
    derivationFamilyOfHom B S hS b e₀ Cm θ A
        ((structureSharpRingInverseImage B S hS
            (subspaceInclusion B S hS W W₀)).hom.app A
          (((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
              (subspaceInclusion B S hS W W₀))).map
            (structureSharpRingInverseImage B S hS qb)).hom.app A x)) = 0 := by
  have hval : (structureSharpRingInverseImage B S hS
        (subspaceInclusion B S hS W W₀)).hom.app A
      (((inverseImageRingFunctor (smallToposMorphismTypeU B S hS
          (subspaceInclusion B S hS W W₀))).map
        (structureSharpRingInverseImage B S hS qb)).hom.app A x) =
      (structureSharpInverseImage B S hS b).hom.app A
        (((smallEtaleInverseImageRing B S hS b).map
            (structureSharpInverseImage B S hS iB)).hom.app A
          ((smallEtaleRingedToposHom_squareInverseImageRingIso B S hS hsq).hom.hom.app A x)) :=
    (congrArg (fun z ↦ (structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀)).hom.app A z)
        (app_inverseImage_structureSharpRingInverseImage B S hS
          (subspaceInclusion B S hS W W₀) qb A x)).trans
      ((structureSharpRingInverseImage_app B S hS
            (subspaceInclusion B S hS W W₀) A _).trans
        (app_structureSharpInverseImage_square B S hS hsq A x).symm)
  rw [hval]
  exact derivationFamilyOfHom_app B S hS b e₀ Cm θ A _

end Vanishing

end AlgebraicGeometry.Space

end
