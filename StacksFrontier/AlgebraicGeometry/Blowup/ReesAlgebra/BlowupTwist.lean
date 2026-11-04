module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.TwistAmple
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjTwistTransition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twisting sheaf of a blowup

Let `X` be a scheme and `ℐ ⊆ 𝒪_X` a quasi-coherent sheaf of ideals, and let `b : X' ⟶ X` be the
blowup of `X` in `ℐ`, the relative `Proj` of the Rees algebra `⨁_{d ≥ 0} ℐ^d`. The twisting
sheaf `𝒪_{X'}(n)` is the `n`-th twisting sheaf of that relative `Proj`, glued from the absolute
twisting sheaves of the charts along the transition datum
`Stacks.RelativeProj.Situation.twistTransition`.

With that datum in hand the invertibility of `𝒪_{X'}(n)` and the relative ampleness of
`𝒪_{X'}(1)` over a centre of finite type hold outright.

## Main definitions

* `AlgebraicGeometry.blowUpTwist`: `𝒪_{X'}(n)`.

## Main results

* `AlgebraicGeometry.blowUpTwistChartIso`: `𝒪_{X'}(n)` restricts on the chart over an affine open
  of the base to the absolute twisting sheaf `𝒪(n)` of the `Proj` of the Rees algebra there.
* `AlgebraicGeometry.isInvertibleModule_blowUpTwist`: **`𝒪_{X'}(n)` is invertible**, for every `n`
  and with no finiteness hypothesis on `ℐ`.
* `AlgebraicGeometry.isRelativelyAmple_blowUpTwist`: **`𝒪_{X'}(1)` is a `b`-relatively ample
  invertible sheaf** when `ℐ` is of finite type.
* `AlgebraicGeometry.exists_isInvertibleModule_isRelativelyAmple_blowUpTwist`: the two together,
  part (2) of Stacks tag 02NS.

## References

* [Stacks Project, Tag 02NS](https://stacks.math.columbia.edu/tag/02NS)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open Stacks.RelativeProj

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- **The `n`-th twisting sheaf `𝒪_{X'}(n)` of a blowup**: the `n`-th twisting sheaf of the
relative projective spectrum of the Rees algebra of the centre. -/
public def blowUpTwist (n : ℤ) : (blowUp I).Modules :=
  Situation.twistSheaf (reesSituation I) n

/-- `𝒪_{X'}(n)` restricts on the chart over an affine open `W` of the base to the absolute
twisting sheaf `𝒪(n)` of the `Proj` of the Rees algebra of `ℐ(W)`. -/
public def blowUpTwistChartIso (n : ℤ) (W : X.affineOpens) :
    (blowUpTwist I n).restrict (Situation.relativeProjChart (reesSituation I) W) ≅
      Situation.twistChart (reesSituation I) n W :=
  Situation.twistSheafChartIso (reesSituation I) n W

/-- **The twisting sheaf of a blowup is invertible**, for every `n` and with no finiteness
hypothesis on the centre. -/
public instance isInvertibleModule_blowUpTwist (n : ℤ) :
    Stacks.Ample.IsInvertibleModule (blowUp I) (blowUpTwist I n) :=
  isInvertibleModule_twist_reesSituation I ((reesSituation I).twistTransition n)

/-- **`𝒪_{X'}(1)` is a relatively ample invertible sheaf for the blowup morphism** when the
centre is a quasi-coherent sheaf of ideals of finite type. -/
public theorem isRelativelyAmple_blowUpTwist (hI : I.IsFiniteType) :
    Stacks.RelativeAmple.IsRelativelyAmple (blowUpToBase I) (blowUpTwist I 1) :=
  isRelativelyAmple_twist_reesSituation I hI ((reesSituation I).twistTransition 1)

/-- **Stacks Project, Tag 02NS, part (2).** Let `ℐ ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals of
finite type and `b : X' ⟶ X` the blowup of `X` in `ℐ`. Then `𝒪_{X'}(1)` is a `b`-relatively
ample invertible sheaf: it is invertible, and with that invertibility it is ample relative to `b`
in the sense of Tag 01VH.

Invertibility is stated, not presupposed: it is the witness of the existential, and the relative
ampleness that follows is read with it. The twist `𝒪_{X'}(1)` is `AlgebraicGeometry.blowUpTwist`,
the twisting sheaf of the relative `Proj` of the Rees algebra glued along the transition datum
`Stacks.RelativeProj.Situation.twistTransition`. -/
@[stacks 02NS "part (2): `𝒪_{X'}(1)` is a `b`-relatively ample invertible sheaf",
  ega "II 4.6.18" "special case",
  ega "III 2.3.4" "(i), special case"]
public theorem exists_isInvertibleModule_isRelativelyAmple_blowUpTwist (hI : I.IsFiniteType) :
    ∃ _ : Stacks.Ample.IsInvertibleModule (blowUp I) (blowUpTwist I 1),
      Stacks.RelativeAmple.IsRelativelyAmple (blowUpToBase I) (blowUpTwist I 1) :=
  ⟨isInvertibleModule_blowUpTwist I 1, isRelativelyAmple_blowUpTwist I hI⟩

end AlgebraicGeometry

end
