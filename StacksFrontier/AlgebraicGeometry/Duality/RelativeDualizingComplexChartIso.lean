module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexAffineSections
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexChartOpens
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineSectionsComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessTensor

/-!
# Two relative dualizing complexes agree on every chart

Let `f : X ⟶ S` be flat and locally of finite presentation and let `(K, ξ)` and `(L, η)` be
relative dualizing complexes for `f` (Stacks 0E2T). Over an affine open `U ⊆ X` lying over an
affine open `V ⊆ S`, the complexes `RΓ(U, K)` and `RΓ(U, L)` are relative dualizing complexes for
`Γ(S, V) → Γ(X, U)` (Stacks 0E2U), hence isomorphic (Stacks 0E2D). On the affine scheme `U` an
object with quasi-coherent cohomology is the complex associated to its derived sections
(Stacks 06Z0), so `K|_U ≅ L|_U`. This is the first sentence of the proof of Stacks 0E2W.

## Main results

* `Scheme.Hom.IsRelativeDualizingComplex.nonempty_iso_restrict_of_mem_chartOpens`: the
  restrictions of `K` and `L` to a chart are isomorphic.

## References

* [Stacks Project, Lemma 48.28.4 (Tag 0E2W)](https://stacks.math.columbia.edu/tag/0E2W)
* [Stacks Project, Lemma 48.28.2 (Tag 0E2U)](https://stacks.math.columbia.edu/tag/0E2U)
* [Stacks Project, Lemma 47.27.3 (Tag 0E2D)](https://stacks.math.columbia.edu/tag/0E2D)
* [Stacks Project, Lemma 36.3.5 (Tag 06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex

variable {X S : Scheme.{u}} {f : X ⟶ S} [Flat f] [LocallyOfFinitePresentation f]

/-- **Two relative dualizing complexes are isomorphic on every chart.** If `(K, ξ)` and `(L, η)`
are relative dualizing complexes for `f` and `U` is an affine open of `X` mapping into an affine
open of `S`, then the derived pullbacks of `K` and `L` along `U ⟶ X` are isomorphic. -/
theorem nonempty_iso_restrict_of_mem_chartOpens {D : DiagonalOpen f}
    {K L : DerivedCategory X.Modules} {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    {η : D.diagonalObject ⟶ D.derivedPullbackProj L}
    (hK : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ)
    (hL : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D L η)
    {U : X.Opens} (hU : U ∈ chartOpens f) :
    Nonempty ((derivedPullback U.ι.toLRSHom.toShHom).obj K ≅
      (derivedPullback U.ι.toLRSHom.toShHom).obj L) := by
  obtain ⟨hUa, V, hV, hUV⟩ := hU
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Module.Flat Γ(S, V) Γ(X, U) := moduleFlat_appLE f hV hUa hUV rfl
  let : Algebra.FinitePresentation Γ(S, V) Γ(X, U) :=
    algebraFinitePresentation_appLE f hV hUa hUV rfl
  obtain ⟨eA⟩ := Dualizing.IsRelativeDualizingComplex.nonempty_iso
    (hK.isRelativeDualizingComplex_derivedSections hUa hV hUV)
    (hL.isRelativeDualizingComplex_derivedSections hUa hV hUV)
  have hqK := isQuasicoherentDerived_of_isPseudoCoherent X K hK.isPerfectRelativeTo.1
  have hqL := isQuasicoherentDerived_of_isPseudoCoherent X L hL.isPerfectRelativeTo.1
  obtain ⟨tK⟩ := hUa.nonempty_iso_derivedTilde_derivedSectionsSpec K hqK
  obtain ⟨tL⟩ := hUa.nonempty_iso_derivedTilde_derivedSectionsSpec L hqL
  obtain ⟨sK⟩ := hUa.nonempty_iso_derivedSectionsSpec K
  obtain ⟨sL⟩ := hUa.nonempty_iso_derivedSectionsSpec L
  let G := (tilde.functor Γ(X, U)).mapDerivedCategory ⋙
    (Scheme.Modules.pushforward hUa.isoSpec.inv).mapDerivedCategory
  let r := Scheme.Modules.derivedRestrictIsoDerivedPullback U.ι
  exact ⟨(r.app K).symm ≪≫ tK ≪≫ G.mapIso (sK ≪≫ eA ≪≫ sL.symm) ≪≫ tL.symm ≪≫ r.app L⟩

end AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex

end
