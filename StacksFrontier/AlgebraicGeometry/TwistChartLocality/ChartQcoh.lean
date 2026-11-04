module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjGradedRing.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcQuasicoherent
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.AwayChart
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic

/-!
# The inverse image of a twisting sheaf along a chart spectrum is quasi-coherent

The twisting sheaves `ProjectiveSpectrum.Proj.twistingSheaf 𝒜 n` on `AlgebraicGeometry.Proj 𝒜`
are quasi-coherent as objects of `(AlgebraicGeometry.Proj 𝒜).Modules`, and so are their inverse
images along the chart morphisms `AlgebraicGeometry.Proj.awayι`, which are open immersions.

## Main results

* `Stacks.AlgebraicGeometry.TwistChartLocality.isQuasicoherent_twistingSheaf`: the twisting sheaf
  is quasi-coherent as an object of `(AlgebraicGeometry.Proj 𝒜).Modules`.
* `Stacks.AlgebraicGeometry.TwistChartLocality.isQuasicoherent_pullback_awayι_twistingSheaf`: the
  inverse image of the twisting sheaf along a chart spectrum is quasi-coherent.

## References

* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01MB](https://stacks.math.columbia.edu/tag/01MB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj

namespace Stacks.AlgebraicGeometry.TwistChartLocality

universe u w

variable {A : Type u} {σ : Type w} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The twisting sheaf `𝒪(n)` on `Proj 𝒜` is quasi-coherent as an object of
`(AlgebraicGeometry.Proj 𝒜).Modules`. -/
public theorem isQuasicoherent_twistingSheaf (n : ℤ) :
    (show (AlgebraicGeometry.Proj 𝒜).Modules from
      ProjectiveSpectrum.Proj.twistingSheaf 𝒜 n).IsQuasicoherent :=
  inferInstanceAs (SheafOfModules.IsQuasicoherent.{u, u, u}
    (ProjectiveSpectrum.Proj.twistingSheaf 𝒜 n))

/-- The inverse image of the twisting sheaf `𝒪(n)` along the chart morphism
`AlgebraicGeometry.Proj.awayι 𝒜 f hf hd` is quasi-coherent. -/
public theorem isQuasicoherent_pullback_awayι_twistingSheaf {d : ℕ} (hd : 0 < d) {f : A}
    (hf : f ∈ 𝒜 d) (n : ℤ) :
    ((Scheme.Modules.pullback (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)).obj
      (show (AlgebraicGeometry.Proj 𝒜).Modules from
        ProjectiveSpectrum.Proj.twistingSheaf 𝒜 n)).IsQuasicoherent := by
  have := isQuasicoherent_twistingSheaf 𝒜 n
  exact Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion _ _

end Stacks.AlgebraicGeometry.TwistChartLocality

end
