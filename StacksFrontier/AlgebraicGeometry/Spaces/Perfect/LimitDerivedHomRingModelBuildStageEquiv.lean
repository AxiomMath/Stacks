module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineQuasicoherentDerivedBaseChange
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction

/-!
# The homomorphism groups of a derived pullback between represented affine spaces

Let `g : U' ⟶ U` be a morphism of the big fppf site over `S` whose source and target have affine
underlying schemes, with `R = Γ(U, 𝒪)` and `R' = Γ(U', 𝒪)` the rings of global functions and
`Φ_R : D(R) ⥤ D(𝒪_{h_U})` the derived associated-module functor of Stacks 08H1.  For objects
`M`, `N` of `D(R)`,

`Hom_{D(𝒪_{h_{U'}})}(Lg^*(Φ_R M), Lg^*(Φ_R N)) ≃ Hom_{D(R')}(M ⊗^𝐋_R R', N ⊗^𝐋_R R')`.

The bijection is a *conjugation* by the affine base change isomorphism
`AlgebraicGeometry.Space.representedAffineDerivedBaseChangeIso` of Stacks 06YY — which is
invertible with no flatness hypothesis on `g` — followed by the full faithfulness of `Φ_{R'}`.

## Where this is used

The field
`AlgebraicGeometry.Space.DescentSituation.RingModel.stageEquiv` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/LimitDerivedHom.lean` asks for a bijection between
the homomorphism group of a stage of Situation 09RH and a homomorphism group of complexes of
modules over one fixed ring.  Over an affine stage the first half of such a bijection is the
statement above: it moves `Hom_{D(𝒪_{X_i})}(E_i, K_i)` to the derived category of modules over
the ring of that stage, leaving only the change of rings down to the fixed base ring.  Being a
conjugation is what makes it insensitive to the unit by which the affine base change
isomorphisms compose around a square
(`AlgebraicGeometry.Space.exists_representedAffineToposDerivedBaseChange_compat`), by
`CategoryTheory.Iso.inv_comp_comp_hom_trans_eq_of_natIso`.

## Main definitions

* `AlgebraicGeometry.Space.representedAffineDerivedPullbackHomEquiv`.

## References

* [Stacks Project, Tag 08H1](https://stacks.math.columbia.edu/tag/08H1)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 09RI](https://stacks.math.columbia.edu/tag/09RI)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {U' U : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  (g : U' ⟶ U)

/-- **The homomorphism groups of a derived pullback between represented affine spaces are
homomorphism groups of modules.**  For `g : U' ⟶ U` with affine underlying schemes and `M`, `N`
in `D(R)`, `R = Γ(U, 𝒪)`,

`Hom_{D(𝒪_{h_{U'}})}(Lg^*(Φ_R M), Lg^*(Φ_R N)) ≃ Hom_{D(R')}(M ⊗^𝐋_R R', N ⊗^𝐋_R R')`,

by conjugation with `AlgebraicGeometry.Space.representedAffineDerivedBaseChangeIso` followed by
the full faithfulness of the derived associated-module functor at `U'`. -/
def representedAffineDerivedPullbackHomEquiv
    (M N : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) :
    ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((representedAffineDerivedAssociated B S hS U).obj M) ⟶
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((representedAffineDerivedAssociated B S hS U).obj N)) ≃
      ((representedAffineDerivedExtension B S hS g).functor.obj M ⟶
        (representedAffineDerivedExtension B S hS g).functor.obj N) :=
  (Iso.homCongr ((representedAffineDerivedBaseChangeIso B S hS g).app M)
        ((representedAffineDerivedBaseChangeIso B S hS g).app N)).trans
    (representedAffineDerivedAssociatedFullyFaithful B S hS U').homEquiv.symm

/-- **The chosen derived extension of scalars along `g` is left adjoint to derived restriction of
scalars**, Stacks 0GMT at the model
`AlgebraicGeometry.Space.representedAffineDerivedExtension`: that model carries the
total-left-derived universal property, which is all
`CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction` asks of it. -/
def representedAffineDerivedExtensionAdjunction :
    (representedAffineDerivedExtension B S hS g).functor ⊣
      (ModuleCat.restrictScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategory :=
  @CochainComplex.DerivedExtensionScalars.derivedExtensionScalarsAdjunction.{u, u, u} _ _ _ _
    (representedAffineCommRingCatHom B S hS g).hom _ _
    (representedAffineDerivedExtension B S hS g).functor
    (representedAffineDerivedExtension B S hS g).comparison
    (representedAffineDerivedExtension B S hS g).isLeftDerived

/-- **The homomorphism groups of a derived pullback between represented affine spaces are
homomorphism groups over the ring of the *target*.**  For `g : U' ⟶ U` with affine underlying
schemes and `M`, `N` in `D(R)`, `R = Γ(U, 𝒪)`, `R' = Γ(U', 𝒪)`,

`Hom_{D(𝒪_{h_{U'}})}(Lg^*(Φ_R M), Lg^*(Φ_R N)) ≃ Hom_{D(R)}(M, N ⊗^𝐋_R R')`,

the second group being taken over `R` with `N ⊗^𝐋_R R'` read through derived restriction of
scalars.  This is
`AlgebraicGeometry.Space.representedAffineDerivedPullbackHomEquiv` followed by Stacks 0GMT.

It is the shape `AlgebraicGeometry.Space.DescentSituation.RingModel.stageEquiv` asks for: the
first argument stays over the fixed ring `R` while only the second argument varies with the
stage. -/
def representedAffineDerivedPullbackHomEquivBase
    (M N : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) :
    ((smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((representedAffineDerivedAssociated B S hS U).obj M) ⟶
        (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g)).obj
          ((representedAffineDerivedAssociated B S hS U).obj N)) ≃
      (M ⟶ (ModuleCat.restrictScalars.{u, u, u}
        (representedAffineCommRingCatHom B S hS g).hom).mapDerivedCategory.obj
          ((representedAffineDerivedExtension B S hS g).functor.obj N)) :=
  (representedAffineDerivedPullbackHomEquiv B S hS g M N).trans
    ((representedAffineDerivedExtensionAdjunction B S hS g).homEquiv M _)

end AlgebraicGeometry.Space

end
