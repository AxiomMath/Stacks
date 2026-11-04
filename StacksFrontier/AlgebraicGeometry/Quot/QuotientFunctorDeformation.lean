module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorRelativeSquare
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientLiftBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientLiftQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatOverToposFlat
public import StacksFrontier.Deformation.ToposThickening.RelativeBaseFlatness

/-!
# Deformations of quotients (Stacks 0CZV)

In Situation 082M with `F` flat over `B`, let `T ⊂ T'` be a first order thickening of schemes over
`B`. The thickening `X_T ⊂ X_{T'}` and its relative square place the deformation theory of
quotients of Remarks 0CZU and 0CZV in the setting of ringed topoi: flatness over the base is
flatness over the relative base, and the elements of `Q_{F/X/B}(T')` lifting a given element of
`Q_{F/X/B}(T)` are the topos lifts.

## Main results

* `AlgebraicGeometry.Space.isFlatOver_iff_isFlat_relBaseRight`: flatness over `Y` is flatness
  over the relative base `(X, p⁻¹𝒪_Y)`.
* `AlgebraicGeometry.Space.QuotientSituation.mem_quotients_and_quotientPullback_eq_iff`: the
  lifts in `Q_{F/X/B}(T')` with quasi-coherent quotient are the topos lifts.

## References

* [Stacks Project, Tag 0CZU](https://stacks.math.columbia.edu/tag/0CZU)
* [Stacks Project, Tag 0CZV](https://stacks.math.columbia.edu/tag/0CZV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Deformation.ToposThickening

universe u

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
-- Sheafification instances at a free module universe make the search for `Mono` of an
-- isomorphism stall on a universe constraint.
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Flatness over the base, read on the relative square**: a quasi-coherent `𝒪_X`-module is
flat over `Y` exactly when it is flat over `f̃' = (id, p^♯) : X ⟶ (X, p⁻¹𝒪_Y)`. -/
theorem isFlatOver_iff_isFlat_relBaseRight {X Y : AlgebraicSpaces B S hS} (p : X ⟶ Y)
    (G : Modules.{u, u} B S hS X.1 X.2) [G.IsQuasicoherentOnSite] :
    IsFlatOver B S hS X.2 p.hom G ↔
      AlgebraicGeometry.SheafOfModules.IsFlat
        ((SheafOfModules.restrictScalars
          ((sheafCompose (smallEtaleRingedTopos B S hS X).J
            (forget₂ CommRingCat.{u} RingCat.{u})).map
            (relBaseRight (smallEtaleRingedToposHom B S hS p)).fSharpInverseImage)).obj G) :=
  (isFlatOver_iff_isFlat_restrictScalars B S hS p G).trans
    (isFlat_restrictScalars_relBaseRight_iff (smallEtaleRingedToposHom B S hS p) G).symm

namespace QuotientSituation

variable (D : QuotientSituation B S hS) {T T' : SchemesOver D.Y} (h : T ⟶ T')

/-- **The quotients of `F_{T'}` restricting to a given quotient of `F_T` are the topos lifts**
(Remark 0CZU): for a subobject `𝒦' ⊂ F_{T'}` with quasi-coherent quotient, `𝒦'` defines an
element of `Q_{F/X/B}(T')` lifting `𝒦 ∈ Q_{F/X/B}(T)` exactly when it is a lift of the quotient
`F_T ⟶ F_T/𝒦` along the thickening `X_T ⟶ X_{T'}` over the relative square. -/
theorem mem_quotients_and_quotientPullback_eq_iff (K : Subobject (D.baseChangeModule T))
    (K' : Subobject (D.baseChangeModule T'))
    (hqc : (D.quotientModule T' K').IsQuasicoherentOnSite) :
    (K' ∈ D.quotients T' ∧ D.quotientPullback h K' = K) ↔
      IsQuotientLift (smallEtaleRingedToposHom B S hS (D.relativeMap h))
        (relBaseRight (smallEtaleRingedToposHom B S hS (D.projection T')))
        (D.baseChangeModule T') ((Subobject.map (D.restrictBaseChangeModuleIso h).inv).obj K)
        K' := by
  have := hqc
  have hfl := isFlatOver_iff_isFlat_relBaseRight (D.projection T') (D.quotientModule T' K')
  have hpb := D.quotientPullback_eq_iff h K' K
  unfold IsQuotientLift
  constructor
  · rintro ⟨⟨_, hf⟩, hp⟩
    exact ⟨hfl.1 hf, hpb.1 hp⟩
  · rintro ⟨hf, hp⟩
    exact ⟨⟨hqc, hfl.2 hf⟩, hpb.2 hp⟩

end QuotientSituation

end AlgebraicGeometry.Space

end
