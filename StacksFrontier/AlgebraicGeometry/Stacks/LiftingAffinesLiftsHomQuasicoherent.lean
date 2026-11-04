module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAutomorphismScalars
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSiteTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSheavesProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeSmooth
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftCartesianTarget

/-!
# The sheaf `SheafHom(Δ^*Ω_{I/U'}, 𝒞_{U/U'})` of a smooth lift is quasi-coherent

Let `ξ = (U, U', a, i, x', α)` be a smooth lift of an étale open of `W` along a first order
thickening (Stacks 0CJP) and `I' = U' ×_{x', 𝒳', x'} U'` its self-intersection, with first
projection `p' : I' ⟶ U'` and diagonal `Δ`. The automorphisms of `ξ` over the identity are the
`𝒪_U`-linear maps `Δ^*Ω_{I/U'} ⟶ 𝒞_{U/U'}`
(`AlgebraicGeometry.Stack.EtaleSmoothLift.LiftsActingGroup`, equation 0CKH of the proof of
Stacks 0CKG). This file shows that the sheaf of such maps, the internal Hom of Stacks 03EM on the
small étale site of `U ≅ i(U)`, is quasi-coherent, the quasi-coherence half of the proof of
Stacks 0CKG (2):

* `Ω_{I/U'} = Ω_{I/U}` (`AlgebraicGeometry.Space.cartesianDifferentialsIso`), and `I ⟶ U` is a
  base change of `p'`, smooth when `p'` is, so `Ω_{I/U}` is finite locally free by Stacks 0CK5
  (`AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_sheafOfDifferentials_of_isSmooth`), hence of
  finite presentation, and so is its inverse image `Δ^*Ω_{I/U'}` (Stacks 03DO (7));
* `𝒞_{U/U'}` is quasi-coherent (Stacks 04CN,
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_conormalModule`);
* Stacks 03M1 (6) (`AlgebraicGeometry.Space.isQuasicoherentOnSite_internalHomSheafSmall`).

## Main definitions

* `AlgebraicGeometry.Stack.EtaleSmoothLift.liftsSource`, `liftsTarget`: the two modules
  `Δ^*Ω_{I/U'}` and `𝒞_{U/U'}` on `i(U)`, between which `LiftsActingGroup` is the group of maps.

## Main results

* `AlgebraicGeometry.Stack.EtaleSmoothLift.isQuasicoherentOnSite_liftsHom`.

## References

* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
* [Stacks Project, Tag 0CK5](https://stacks.math.columbia.edu/tag/0CK5)
* [Stacks Project, Tag 04CN](https://stacks.math.columbia.edu/tag/04CN)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Stack.EtaleSmoothLift

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)
  (ξ : EtaleSmoothLift B S hS ι hι W x hx)

/-- **`Δ^*Ω_{I/U'}`**, the source of the parameters of the automorphisms of `ξ`. -/
abbrev liftsSource :=
  (Space.modulePullback B S hS (liftsProjection hι₁ ξ ≫ diagonalRestriction hι₁ ξ)).obj
    (liftsDifferentials hι₁ ξ)

/-- **`𝒞_{U/U'}`**, the target of the parameters of the automorphisms of `ξ`. -/
abbrev liftsTarget :=
  Space.conormalModule B S hS
    ((Space.SpacesEtale.toSpaces B S hS ξ.ambient).obj (Space.SpacesEtale.final B S hS ξ.ambient))
    (liftsZ hι₁ ξ)

/-- The group `LiftsActingGroup hι₁ ξ` is the group of morphisms `Δ^*Ω_{I/U'} ⟶ 𝒞_{U/U'}`. -/
theorem liftsActingGroup_eq : LiftsActingGroup hι₁ ξ = (liftsSource hι₁ ξ ⟶ liftsTarget hι₁ ξ) :=
  rfl

/-- `Δ^*Ω_{I/U'}` is of finite presentation when `p' : I' ⟶ U'` is smooth. -/
theorem isFinitePresentationOnSite_liftsSource
    (hp : Space.IsSmooth B S hS ξ.selfIntersection.fst.hom) :
    (liftsSource hι₁ ξ).IsFinitePresentationOnSite := by
  have hsq := Subfunctor.isPullback_preimage ξ.selfIntersection.fst.hom (baseSubspace hι₁ ξ).1
  have hsm : Space.IsSmooth B S hS
      (Space.preimageProjection B S hS ξ.selfIntersection.fst (baseSubspace hι₁ ξ)).hom :=
    Space.isSmooth_of_isPullback hsq
      (Space.isClosedSubspace_preimage B S hS _ _ ξ.ambient.2 ξ.selfIntersection.pt.2
        (baseSubspace hι₁ ξ).2).1 ξ.selfIntersection.pt.2 (baseSubspace hι₁ ξ).2.1 ξ.ambient.2 hp
  have hfree : SheafOfModules.IsFiniteLocallyFreeOnSite (liftsDifferentials hι₁ ξ) :=
    SheafOfModules.IsFiniteLocallyFreeOnSite.of_iso
      (Space.cartesianDifferentialsIso B S hS (baseSubspace hι₁ ξ) ξ.selfIntersection.fst
        (isFirstOrderThickening_preimage_fst hι₁ ξ).1).symm
      (Space.isFiniteLocallyFreeOnSite_sheafOfDifferentials_of_isSmooth B S hS _ hsm)
  exact Space.isFinitePresentationOnSite_modulePullback B S hS _ _
    (SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite hfree)

/-- **The sheaf `SheafHom(Δ^*Ω_{I/U'}, 𝒞_{U/U'})` on the small étale site of `i(U)` is
quasi-coherent** when `p' : I' ⟶ U'` is smooth (Stacks 0CKG (2), the quasi-coherence input). -/
theorem isQuasicoherentOnSite_liftsHom (hp : Space.IsSmooth B S hS ξ.selfIntersection.fst.hom) :
    letI := Space.smallEtaleRingedSite_essentiallySmall B S hS (liftsZSpace hι₁ ξ).1
      (liftsZSpace hι₁ ξ).2
    (RingedSite.internalHomSheafSmall
      (Space.smallEtaleRingedSite B S hS (liftsZSpace hι₁ ξ).1 (liftsZSpace hι₁ ξ).2)
      (liftsSource hι₁ ξ) (liftsTarget hι₁ ξ)).IsQuasicoherentOnSite := by
  have := isFinitePresentationOnSite_liftsSource hι₁ ξ hp
  exact Space.isQuasicoherentOnSite_internalHomSheafSmall B S hS _ _ _ _ inferInstance
    (Space.isQuasicoherentOnSite_conormalModule B S hS _ _) inferInstance

end AlgebraicGeometry.Stack.EtaleSmoothLift
