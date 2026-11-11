module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeUnitSingle
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Composition
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ProjectionFormulaDischarged
import StacksCore.Tactic.StacksAttribute

/-!
# Composition of Fourier-Mukai functors

Let `S` be a scheme and let `X`, `Y`, `Z` be schemes over `S` whose structure morphisms are
quasi-compact and quasi-separated.  Let `K ∈ D_QCoh(𝒪_{X ×_S Y})` and
`K' ∈ D_QCoh(𝒪_{Y ×_S Z})`.  If `X` and `Z` are tor independent over `S` and `Y ⟶ S` is flat,
then `Φ_{K'} ∘ Φ_K ≅ Φ_{K''}` as functors `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Z)`, where
`K'' = R pr_{13,*}(L pr_{12}^* K ⊗^𝐋 L pr_{23}^* K')` on `X ×_S Z`.

## Main results

* `AlgebraicGeometry.quasiCoherentFourierMukaiCompNatIso`: **[Stacks, Tag 0FYS]**, the natural
  isomorphism `Φ_{K'} ∘ Φ_K ≅ Φ_{K''}`.

The chain of comparisons is `AlgebraicGeometry.quasiCoherentFourierMukaiComp`; its two Stacks
inputs are discharged here by `AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent`
([Stacks, Tag 08IB]) and `AlgebraicGeometry.projectionFormulaIsIsoOnQuasicoherent`
([Stacks, Tag 08EU]).  The convolution kernel `K''` is
`AlgebraicGeometry.fourierMukaiConvolution`, and its cohomology sheaves are quasi-coherent by
`AlgebraicGeometry.isQuasicoherent_homology_fourierMukaiConvolution`, so `K''` lies in
`D_QCoh(𝒪_{X ×_S Z})` as the source asserts.

## References

* [Stacks Project, Tag 0FYS](https://stacks.math.columbia.edu/tag/0FYS)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S)
  [QuasiCompact f] [QuasiSeparated f] [QuasiCompact g] [QuasiSeparated g]
  [QuasiCompact h] [QuasiSeparated h]

/-- **[Stacks, Tag 0FYS].**  Let `S` be a scheme and let `X`, `Y`, `Z` be schemes over `S`
with `f : X ⟶ S`, `g : Y ⟶ S` and `h : Z ⟶ S` quasi-compact and quasi-separated.  Let `K` on
`X ×_S Y` and `K'` on `Y ×_S Z` have quasi-coherent cohomology sheaves, and consider the
Fourier-Mukai functors `Φ_K : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` and
`Φ_{K'} : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_Z)`.  If `X` and `Z` are tor independent over `S` and `g` is
flat, then `Φ_{K'} ∘ Φ_K ≅ Φ_{K''}` naturally, where
`K'' = R pr_{13,*}(L pr_{12}^* K ⊗^𝐋 L pr_{23}^* K')` on `X ×_S Z`, a complex in
`D_QCoh(𝒪_{X ×_S Z})`.

The source writes the conclusion as an equality; the two functors are built from derived
functors, determined up to canonical isomorphism, so the statement is a natural isomorphism.
Derived base change ([Stacks, Tag 08IB]) and the projection formula ([Stacks, Tag 08EU]) enter
through their proofs `AlgebraicGeometry.derivedBaseChangeIsIsoOnQuasicoherent` and
`AlgebraicGeometry.projectionFormulaIsIsoOnQuasicoherent`. -/
@[stacks 0FYS "composition of Fourier-Mukai functors, Phi_{K'} ∘ Phi_K ≅ Phi_{K''} as a \
  natural isomorphism of functors D_QCoh(O_X) to D_QCoh(O_Z), the source's equality of \
  functors; with Stacks 08IB and 08EU discharged by their proofs", no_expose]
def quasiCoherentFourierMukaiCompNatIso [Flat g] (htor : TorIndependent f h)
    {K : DerivedCategory (pullback f g).Modules}
    (hK : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (pullback f g).Modules j).obj
      K).IsQuasicoherent)
    {K' : DerivedCategory (pullback g h).Modules}
    (hK' : ∀ j : ℤ, ((DerivedCategory.homologyFunctor (pullback g h).Modules j).obj
      K').IsQuasicoherent) :
    quasiCoherentFourierMukai f g K hK ⋙ quasiCoherentFourierMukai g h K' hK' ≅
      quasiCoherentFourierMukai f h (fourierMukaiConvolution f g h K K')
        (isQuasicoherent_homology_fourierMukaiConvolution f g h hK hK') :=
  quasiCoherentFourierMukaiComp f g h derivedBaseChangeIsIsoOnQuasicoherent
    projectionFormulaIsIsoOnQuasicoherent htor hK hK'

end AlgebraicGeometry

end
