module

public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.VectorBundleAffineSpaceBundle
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ConormalAlgebraQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.EffectiveCartierConormalSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeNormalBundleIso
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The normal cone of an effective Cartier divisor is locally of finite type over the divisor

Let `D ⊆ X` be an effective Cartier divisor. Its normal cone `C_DX = Spec_D(𝒞_{D/X,*})` is the
total space of the conormal line bundle: the canonical morphism `C_DX ⟶ N_DX` of
[Stacks, Tag 0637] is an isomorphism, and `N_DX = Spec_D(Sym(𝒞_{D/X}))` with `𝒞_{D/X}`
invertible, hence finite locally free of rank one. The projection of the vector bundle of a
finite locally free module is locally of finite type, and therefore so is `C_DX ⟶ D`.

## Main results

* `Stacks.Conormal.isFiniteLocallyFreeOfRank_conormalSheafDegreeOne`: `𝒞_{D/X}` is finite
  locally free of rank one.
* `Stacks.Conormal.locallyOfFiniteType_normalConeToBase`: `C_DX ⟶ D` is locally of finite type.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Conormal

variable {X : Scheme.{u}} (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]

/-- **The conormal sheaf of an effective Cartier divisor is finite locally free of rank one**: it
is invertible, and an invertible module on a scheme is finite locally free of rank one. -/
@[ega "IV 19.1.3" "special case", sga "6 X 7.1" "special case"]
instance isFiniteLocallyFreeOfRank_conormalSheafDegreeOne :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (conormalSheafDegreeOne D.subschemeι) 1 :=
  Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible D.subscheme
    (conormalSheafDegreeOne D.subschemeι)
    (isInvertible_conormalSheafDegreeOne_of_isEffectiveCartierDivisor D)

/-- **The normal cone of an effective Cartier divisor is locally of finite type over the
divisor.** It is isomorphic over `D` to the vector bundle of the conormal sheaf, which is finite
locally free of rank one. -/
instance locallyOfFiniteType_normalConeToBase :
    LocallyOfFiniteType (normalConeToBase D.subschemeι) := by
  have := isIso_normalConeToNormalBundle_of_isEffectiveCartierDivisor D
  have := Stacks.Chow.locallyOfFiniteType_vectorBundleToBase
    (conormalSheafDegreeOne D.subschemeι) 1
  rw [← normalConeToNormalBundle_toBase]
  infer_instance

end Stacks.Conormal

end
