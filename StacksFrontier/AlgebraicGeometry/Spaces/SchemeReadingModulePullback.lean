module

public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeReadingOfModule

/-!
# The reading of an inverse image of modules on a scheme over the source

Let `g : X' ⟶ X` be a morphism of algebraic spaces over `S` and `ℰ` a quasi-coherent
`𝒪_X`-module. For an object `T` of the big fppf site with a morphism `ψ : T ⟶ X'`, the reading
of `g^*ℰ` along `ψ` and the reading of `ℰ` along `ψ ≫ g`
(`AlgebraicGeometry.Space.schemeReading`) are two quasi-coherent modules on the scheme
underlying `T`, identified by the comparison `ψ^*g^*ℰ ≅ (ψ ≫ g)^*ℰ` of iterated inverse images
(Stacks 03LU). This file records that identification and its **compatibility with the
comparisons of readings along morphisms `k : T' ⟶ T`**
(`AlgebraicGeometry.Space.schemeReadingPullbackIso`): pulling back the identification at `T`
along `k` and comparing, or comparing and then identifying at `T'`, give the same isomorphism.
It is the associativity of the comparisons of iterated inverse images,
`AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackComparison_trans`, transported through the
naturality of the base change of the Zariski reading.

## Main definitions

* `AlgebraicGeometry.Space.schemeReadingModulePullbackIso`: the identification
  `(g^*ℰ)_T ≅ ℰ_T` of the readings along `ψ` and `ψ ≫ g`.

## Main results

* `AlgebraicGeometry.Space.schemeReadingModulePullbackIso_naturality`: its compatibility with the
  comparisons of readings along a morphism of the site.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X X' : AlgebraicSpaces B S hS} (g : X' ⟶ X) (E : Modules.{u, u} B S hS X.1 X.2)

/-- **The reading of an inverse image is the reading along the composite**: for
`ψ : T ⟶ X'`, the reading of `g^*ℰ` along `ψ` is the reading of `ℰ` along `ψ ≫ g`, through the
comparison `ψ^*g^*ℰ ≅ (ψ ≫ g)^*ℰ` of iterated inverse images. -/
def schemeReadingModulePullbackIso {T : BigFppfOver B S hS}
    (ψ : representedAlgebraicSpace B S hS T ⟶ X') :
    schemeReading ((modulePullback B S hS g).obj E) ψ ≅ schemeReading E (ψ ≫ g) :=
  (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T) T.left.property).mapIso
    ((representedSmallEtaleModuleEquivalence B S hS T).inverse.mapIso
      (QuasiCoherentDescent.pullbackComparison B S hS ψ g (ψ ≫ g) rfl E).symm)

variable (hE : E.IsQuasicoherentOnSite)

include hE in
/-- The inverse image of a quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherentOnSite_modulePullback_obj_of_isQuasicoherentOnSite :
    ((modulePullback B S hS g).obj E).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g E hE

section Naturality

attribute [local implicit_reducible] AlgebraicGeometry.Space.smallEtaleRingedSite

/-- **The identification of the readings of `g^*ℰ` and `ℰ` is compatible with the comparisons
of readings.** For `k : T' ⟶ T` over `X'`, with `ψ : T ⟶ X'` and `ψ' : T' ⟶ X'`, pulling back the
identification at `T` along `k` and then comparing the readings of `ℰ` along `k` is comparing
the readings of `g^*ℰ` along `k` and then identifying at `T'`. -/
theorem schemeReadingModulePullbackIso_naturality {T' T : BigFppfOver B S hS} (k : T' ⟶ T)
    {ψ : representedAlgebraicSpace B S hS T ⟶ X'} {ψ' : representedAlgebraicSpace B S hS T' ⟶ X'}
    (w : representedSpaceMap B S hS k ≫ ψ = ψ')
    (wg : representedSpaceMap B S hS k ≫ (ψ ≫ g) = ψ' ≫ g) :
    (Scheme.Modules.pullback
          (_root_.AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) k.left)).mapIso
        (schemeReadingModulePullbackIso g E ψ) ≪≫ schemeReadingPullbackIso E hE k wg =
      schemeReadingPullbackIso ((modulePullback B S hS g).obj E)
          (isQuasicoherentOnSite_modulePullback_obj_of_isQuasicoherentOnSite g E hE) k w ≪≫
        schemeReadingModulePullbackIso g E ψ' := by
  have key := congrArg Iso.symm (QuasiCoherentDescent.pullbackComparison_trans B S hS
    (representedSpaceMap B S hS k) ψ g (ψ ≫ g) rfl ψ' w (ψ' ≫ g) wg rfl E)
  rw [Iso.trans_symm, Iso.trans_symm, ← Functor.mapIso_symm] at key
  have h2 := congrArg (fun e => (SmallEtale.restrictModule (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj T') T'.left.property).mapIso
    ((representedSmallEtaleModuleEquivalence B S hS T').inverse.mapIso e)) key
  simp only [Functor.mapIso_trans] at h2
  have hnat := representedZariskiModulePullbackIso_naturality_iso B S hS k
    (relativelyRepresentable_yoneda_map B S hS k)
    (isQuasicoherentOnSite_modulePullback_schemeReading _
      (isQuasicoherentOnSite_modulePullback_obj_of_isQuasicoherentOnSite g E hE) ψ)
    (isQuasicoherentOnSite_modulePullback_schemeReading E hE (ψ ≫ g))
    (QuasiCoherentDescent.pullbackComparison B S hS ψ g (ψ ≫ g) rfl E).symm
  rw [schemeReadingPullbackIso_eq, schemeReadingPullbackIso_eq]
  unfold schemeReadingModulePullbackIso
  rw [← Iso.trans_assoc, hnat, Iso.trans_assoc, h2, Iso.trans_assoc]

end Naturality

end AlgebraicGeometry.Space

end
