module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedVersality.PolarizedOverDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedVersality.PolarizedOverRSStar
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedVersality.PolarizedTowerLimit
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedDiagonal
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedLimitPreservingProof
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedRSStar
public import StacksFrontier.Deformation.Artin.Versality.OpennessOfVersality
public import StacksFrontier.Deformation.Artin.Versality.OpennessTransfer
public import StacksFrontier.RingTheory.Noetherian.ULift

/-!
# Openness of versality for the stack of polarized schemes

The stack in groupoids `𝒫olarized` satisfies openness of versality over `Spec(ℤ)`. Over a
Noetherian base scheme `S`, the same holds for the stack `S-𝒫olarized` of Remark 0D1N
(`AlgebraicGeometry.PolarizedVersality.PolarizedOver.stack`: polarized families with a morphism of
their base to `S`, over the big fppf site of `S`).

## Main results

* `AlgebraicGeometry.hasOpenVersality_polarizedStackUnconditional`: openness of versality for
  `𝒫olarized` over `Spec(ℤ)`.
* `AlgebraicGeometry.hasOpenVersality_polarizedOverNoetherian`: openness of versality for
  `S-𝒫olarized` over a Noetherian scheme `S`.

## Implementation notes

Openness of versality is stated as `Deformation.Artin.HasOpenVersality` of the structure functor
composed with `Over.post B.inclusion`, the body of Stacks 07XQ written out: the predicate
`Deformation.Artin.IsOpenVersality` also asks the structure functor to be fibred in groupoids over
all schemes over the base, which fails over a bounded big fppf site.

## References

* [Stacks Project, Tag 0D4V](https://stacks.math.columbia.edu/tag/0D4V)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
* [Stacks Project, Tag 0D1N](https://stacks.math.columbia.edu/tag/0D1N)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Deformation.Artin

namespace AlgebraicGeometry

/-- The stack in groupoids `𝒫olarized` of polarized proper flat families of finite presentation
(Stacks 0D1M), over the big fppf site of `Spec(ℤ)`, satisfies openness of versality: if an object
over a scheme `U` locally of finite type over `Spec(ℤ)` is versal at a finite type point `u₀`, it
is versal at every finite type point of an open neighbourhood of `u₀`. -/
@[stacks 0D4V "openness of versality for `𝒫olarized` over `Spec(ℤ)`"]
theorem hasOpenVersality_polarizedStackUnconditional (B : BigFppfSite.{u})
    (hZ : B.Contains (Spec (CommRingCat.of (ULift.{u} ℤ)))) :
    HasOpenVersality
      ((polarizedStackUnconditional B hZ (isTerminal_obj_specULiftZ B hZ)).val.p ⋙
        Over.post B.inclusion) :=
  isOpenVersality_of_isSquareZeroEffective B _ hZ _
    (hasRepresentableDiagonal_polarizedStackUnconditional B hZ _)
    (satisfiesRSStar_polarizedSliceProjection B hZ _)
    (isLimitPreservingPolarizedUnconditional B hZ _)
    (PolarizedVersality.Polarized.isSquareZeroEffective_polarizedSliceProjection B hZ _)

/-- For a Noetherian scheme `S`, the stack `S-𝒫olarized` of Remark 0D1N — polarized proper flat
families of finite presentation together with a morphism of their base to `S` — over the big fppf
site of `S` satisfies openness of versality: if an object over a scheme `U` locally of finite type
over `S` is versal at a finite type point `u₀`, it is versal at every finite type point of an open
neighbourhood of `u₀`. -/
@[stacks 0D4V "openness of versality for `S-𝒫olarized` over a Noetherian base scheme `S`"]
theorem hasOpenVersality_polarizedOverNoetherian (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) [IsNoetherian S] :
    HasOpenVersality
      ((PolarizedVersality.PolarizedOver.stack B S hS).val.p ⋙ Over.post B.inclusion) :=
  isOpenVersality_of_isSquareZeroEffective B S hS _
    (PolarizedVersality.PolarizedOver.hasRepresentableDiagonal_stack B S hS)
    (PolarizedVersality.PolarizedOver.satisfiesRSStar_projection B S hS)
    (PolarizedVersality.PolarizedOver.isLimitPreserving_stack B S hS)
    (PolarizedVersality.PolarizedOver.isSquareZeroEffective_projection B S hS)

end AlgebraicGeometry

end
