module

public import StacksFrontier.Deformation.RestrictedRepresentable
public import StacksFrontier.Deformation.TangentSpace.Derivations

/-!
# The tangent map of a morphism of prorepresentable functors

Let `f : R ⟶ S` be a morphism of complete local `Λ`-algebras with residue field `k`, and put
`F = underline R|_{𝒞_Λ}` and `G = underline S|_{𝒞_Λ}` for the two restricted representable
functors. Precomposition with `f` is a transformation of functors `G ⟶ F`, so it induces a
`k`-linear map `TG ⟶ TF` on tangent spaces. Under the canonical identifications
`TF = Der_Λ(R, k)` and `TG = Der_Λ(S, k)` of Stacks 06IC, that map is restriction of
derivations along `f`:

    TG = Der_Λ(S, k) ⟶ Der_Λ(R, k) = TF.

## Main definitions

* `Deformation.tangentSpaceMap`: the `k`-linear map on derivation spaces induced
  contravariantly by `f`.
* `Deformation.tangentSpaceMapArtinian`: the same map read on the tangent spaces themselves,
  that is on the values of the restricted representable functors at the dual numbers.

## Main results

* `Deformation.tangentSpaceMap_apply`: the induced map is precomposition with `f`, that is
  the restriction `Der_Λ(S, k) → Der_Λ(R, k)`.
* `Deformation.tangentSpaceMapArtinian_apply`: on a tangent vector, the induced map is
  precomposition with `f` in `𝒞_Λ`-points, that is `x ↦ f ≫ x`.

## References

* [Stacks Project, Tag 06ST](https://stacks.math.columbia.edu/tag/06ST)
-/

@[expose] public section

open CategoryTheory

namespace Deformation

universe u v w

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

add_to_stacks 06ST "the transformation of functors induced by a map of representing algebras"
  Deformation.restrictedCoyonedaMap

add_to_stacks 06ST "naturality of the square-zero-point description of the tangent space"
  Deformation.squareZeroPointsDerivationsEquiv_precomp

add_to_stacks 06ST "naturality of the identification of the tangent space with derivations"
  Deformation.tangentSpaceDerivationsLinearEquiv_precomp

/-- The `k`-linear map on tangent spaces induced contravariantly by a morphism `f : R ⟶ S` of
complete local `Λ`-algebras, written on derivation spaces: it sends a `Λ`-derivation `S → k` to
its restriction along `f`. -/
@[stacks 06ST "linear tangent map"]
noncomputable def tangentSpaceMap
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S) :
    letI : Algebra S k := (residueHom S).toRingHom.toAlgebra
    letI : Algebra R k := (residueHom R).toRingHom.toAlgebra
    Derivation Λ S k →ₗ[k] Derivation Λ R k := by
  letI : Algebra R S := f.hom.toRingHom.toAlgebra
  letI : IsScalarTower Λ R S := IsScalarTower.of_algebraMap_eq fun r => (f.hom.commutes r).symm
  letI : Algebra S k := (residueHom S).toRingHom.toAlgebra
  letI : Algebra R k := (residueHom R).toRingHom.toAlgebra
  letI : IsScalarTower R S k := IsScalarTower.of_algebraMap_eq fun r => (f.residue_comm r).symm
  exact { toFun := fun d => d.compAlgebraMap R, map_add' := by intros; rfl
          map_smul' := by intros; rfl }

/-- Under the canonical identification of the tangent space with a space of derivations, the
induced tangent map is precomposition with the morphism of representing algebras. -/
@[stacks 06ST "action on derivations"]
theorem tangentSpaceMap_apply
    {R S : CompleteLocalAlgCat.{u, v, w} Λ k} (f : R ⟶ S)
    (d : letI : Algebra S k := (residueHom S).toRingHom.toAlgebra
      Derivation Λ S k) (r : R) :
    tangentSpaceMap f d r = d (f.hom r) := rfl

/-- The induced map on the tangent spaces themselves, the values of the two restricted
representable functors at the dual numbers: `tangentSpaceMap` transported along the canonical
identification with derivation spaces. -/
@[stacks 06ST "linear tangent map on Artinian tangent spaces"]
noncomputable def tangentSpaceMapArtinian
    {R S : CompleteLocalAlgCat.{u, max v w, w} Λ k} (f : R ⟶ S) :
    tangentSpaceArtinian Λ k (restrictedCoyoneda S) →ₗ[k]
      tangentSpaceArtinian Λ k (restrictedCoyoneda R) :=
  (tangentSpaceDerivationsLinearEquiv R).symm.toLinearMap.comp
    ((tangentSpaceMap f).comp (tangentSpaceDerivationsLinearEquiv S).toLinearMap)

/-- On a tangent vector, that is on a `k[ε]`-point of the functor represented by `S`, the
induced tangent map is precomposition with the morphism of representing algebras. -/
@[stacks 06ST "action on Artinian tangent vectors"]
theorem tangentSpaceMapArtinian_apply
    {R S : CompleteLocalAlgCat.{u, max v w, w} Λ k} (f : R ⟶ S)
    (x : tangentSpaceArtinian Λ k (restrictedCoyoneda S)) :
    tangentSpaceMapArtinian f x = f ≫ x := by
  let : Algebra R k := (residueHom R).toRingHom.toAlgebra
  apply (tangentSpaceDerivationsLinearEquiv R).injective
  ext r
  simpa [tangentSpaceMapArtinian, tangentSpaceMap_apply] using
    (tangentSpaceDerivationsLinearEquiv_precomp R S f x r).symm

end Deformation

end
