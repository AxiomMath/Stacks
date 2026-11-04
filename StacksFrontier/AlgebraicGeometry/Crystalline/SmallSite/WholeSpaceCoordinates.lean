module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.WholeSpaceCosimplicialModule

/-!
# The coordinates of the degree zero of the cosimplicial envelope of the whole space

In the situation of [Stacks, Proposition 60.20.1, Tag 07JN], let `P = A[x_c : c ∈ C] → C` be the
presentation `Crystalline.canonicalPresentation`. We define the images `x_c ∈ E(0)` of its
variables in the divided power envelope `E(0)` of the degree zero.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.SmallSite.wsCoordinate`: the coordinate `x_c` of `E(0)`.

## References

* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry Simplicial

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [WholeSpacePresentation S hp]
  [IsAffine S.X] [IsAffine S.S.scheme]

/-- The coordinate `x_c` of the degree zero `E(0)` of the cosimplicial envelope: the image of the
variable `x_c` of `P = A[x_c : c ∈ C]`, in the single tensor factor of `P^{⊗ 1}`. -/
def wsCoordinate (c : wholeSpaceIndex S hp) : (wholeSpaceDPAlgebra hp).carrier 0 :=
  (tensorPowerEnvelope (affineSituation S hp)
    (wholeSpacePresentation S hp) 0).algebraMap.toRingHom
      (MvPolynomial.X ((0 : Fin 1), c))

end Crystalline.GlobalCrystallineSituation.SmallSite
