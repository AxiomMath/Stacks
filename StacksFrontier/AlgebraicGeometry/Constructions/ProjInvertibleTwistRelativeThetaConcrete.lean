module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeThetaGlobal
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeAbsCompare

/-!
# Tag 02NC's `θ`, glued

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `ℒ` an invertible `𝒪_S`-module,
`ℬ` the twist of `𝒜` by `ℒ`, `P = Proj_S(𝒜)`, `P' = Proj_S(ℬ)` and `g : P ⟶ P'` the canonical
isomorphism over `S`. The integer twists of `P'` and the target `⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`
transported to `P'` are two sets of twist data over the basis of affine opens trivializing `ℒ`,
the second through the absolute comparison of twists over each member
(`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.absTwistCompare`). Their glued isomorphism
`Φ` carries the homogeneous sections of `ℬ` to the *multiply* map, and its inverse image along `g`
is Tag 02NC's `θ`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.absTwistCompare`: the absolute comparison of
  twists over a member of the trivializing basis, as the datum the glueing consumes.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.twistThetaPhi`: the glued identification of
  `⨁_n 𝒪_{P'}(n)` with the transported target.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.twistTheta`: **Tag 02NC's
  `θ : g^*(⨁_n 𝒪_{P'}(n)) ≅ ⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`**, an isomorphism of sheaves of `ℤ`-graded
  algebras.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.twistThetaIso`: its component
  `θ_n : g^*𝒪_{P'}(n) ≅ 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.twistThetaPhi_psi`: `Φ` carries the
  homogeneous-section map of `P'` to the *multiply* map.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.twistTheta_squareAt`: **the square of
  clause (2)** for `θ`, over every open of the base.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist
open Stacks.AlgebraicGeometry.RelativeProjTwists
open Stacks.AlgebraicGeometry.AffineOpenTensorSections

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]
  (𝒜 : SheafGradedAlgebra S)

/-- **The absolute comparison of twists over a member of the trivializing basis**, as the datum the
glueing of `θ` consumes. -/
def absTwistCompare (V : trivializingOpens L) : AbsTwistCompare L 𝒜 V where
  iso := absTwistIso L 𝒜 V
  mul := absTwistIso_mul L 𝒜 V
  deg := isDegCompat_absTwistIso L 𝒜 V

/-- **The glued identification of `⨁_n 𝒪_{P'}(n)` with the target `⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`
transported to `P'`**: the comparison of the two sets of twist data over the trivializing basis. -/
def twistThetaPhi : Tag07ZGTwist.twistAlgebra (twist 𝒜 L) ≅ transportedTarget L 𝒜 :=
  TwistExistenceBasis.glueAlgIso (isBasis_trivializingOpens L) (fun _ h => h.1)
    (TwistExistenceBasis.BasisTwistData.ofTwistData
      (GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)))
    (targetTwistData L 𝒜 (absTwistCompare L 𝒜))

/-- The components of the glued identification are the glued isomorphisms of Tag 01NR's
comparison. -/
theorem twistThetaPhi_hom_app (n : ℤ) :
    (twistThetaPhi L 𝒜).hom.app n =
      (TwistExistenceBasis.glueIso (isBasis_trivializingOpens L) (fun _ h => h.1)
        (TwistExistenceBasis.BasisTwistData.ofTwistData (𝔅 := trivializingOpens L)
          (GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)))
        (targetTwistData L 𝒜 (absTwistCompare L 𝒜)) n).hom :=
  TwistExistenceBasis.glueAlgIso_hom_app _ _ _ _ n

/-- **The glued identification carries the homogeneous-section map of `P'` to the *multiply*
map**, transported to `P'`. -/
theorem twistThetaPhi_psi (k : ℕ) :
    (GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ k ≫
        (Scheme.Modules.pushforward (relativeProj (twist 𝒜 L)).toBase).map
          ((twistThetaPhi L 𝒜).hom.app k) =
      transportedPsi L 𝒜 k :=
  by
  rw [twistThetaPhi_hom_app]
  exact TwistExistenceBasis.glueIso_psi (isBasis_trivializingOpens L) (fun _ h => h.1)
    (TwistExistenceBasis.BasisTwistData.ofTwistData (𝔅 := trivializingOpens L)
      (GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)))
    (targetTwistData L 𝒜 (absTwistCompare L 𝒜)) k

/-- **Tag 02NC's `θ : g^*(⨁_n 𝒪_{P'}(n)) ≅ ⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`**, an isomorphism of sheaves
of `ℤ`-graded algebras on `P = Proj_S(𝒜)`. -/
def twistTheta :
    Stacks.RingedSpace.pullbackGradedAlgebra (relativeTwistHom L 𝒜).toLRSHom.toShHom
        (Tag07ZGTwist.twistAlgebra (twist 𝒜 L)) ≅ targetAlgebra L 𝒜 :=
  globalTheta L 𝒜 (twistThetaPhi L 𝒜)

/-- **The component `θ_n : g^*𝒪_{P'}(n) ≅ 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` of Tag 02NC's `θ`.** -/
def twistThetaIso (n : ℤ) :
    (Scheme.Modules.pullback (relativeTwistHom L 𝒜)).obj
        (Tag07ZGTwist.relativeTwist (twist 𝒜 L) n) ≅
      tensorMod (Tag07ZGTwist.relativeTwist 𝒜 n)
        ((Scheme.Modules.pullback (relativeProj 𝒜).toBase).obj (tpMod L n)) :=
  globalThetaIso L 𝒜 (twistThetaPhi L 𝒜) n

/-- The components of `twistTheta` are the `twistThetaIso`. -/
theorem twistTheta_hom_app (n : ℤ) :
    (twistTheta L 𝒜).hom.app n = (twistThetaIso L 𝒜 n).hom := rfl

/-- `θ` preserves the unit. -/
theorem twistTheta_hom_app_zero_one (W : (relativeProj 𝒜).scheme.Opensᵒᵖ) :
    ((twistTheta L 𝒜).hom.app 0).val.app W
        ((Stacks.RingedSpace.pullbackGradedAlgebra (relativeTwistHom L 𝒜).toLRSHom.toShHom
          (Tag07ZGTwist.twistAlgebra (twist 𝒜 L))).one.eval W) =
      (targetAlgebra L 𝒜).one.eval W :=
  globalTheta_hom_app_zero_one L 𝒜 (twistThetaPhi L 𝒜) W

/-- **`θ_k` carries the homogeneous section of `b ∈ ℬ_k(V)` to the *multiply* map applied to
`b`**, over every open `V` of the base. -/
theorem twistTheta_thetaSections (k : ℕ) (V : S.Opens)
    (b : ((twist 𝒜 L).piece (k : ℤ)).val.obj (op V)) :
    RelativeTwistSections.thetaSections (relativeProj 𝒜).toBase
        (relativeProj (twist 𝒜 L)).toBase (relativeTwistHom L 𝒜)
        (relativeTwistHom_comp_toBase L 𝒜) (twistThetaIso L 𝒜 k).hom V
        (((GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ k).val.app (op V) b) =
      (RelativeTwistSections.multiplyHom (relativeProj 𝒜).toBase
          (An := 𝒜.piece (k : ℤ)) (Ln := tpMod L (k : ℤ))
          ((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ k)).val.app (op V) b :=
  globalTheta_thetaSections L 𝒜 (twistThetaPhi L 𝒜) (twistThetaPhi_psi L 𝒜) k V b

/-- **The square of clause (2) of Tag 02NC for `θ`**, over every open of the base. -/
theorem twistTheta_squareAt (k : ℕ) (V : S.Opens) :
    RelativeTwistSections.SquareAt (relativeProj 𝒜).toBase (relativeProj (twist 𝒜 L)).toBase
      (relativeTwistHom L 𝒜) (relativeTwistHom_comp_toBase L 𝒜)
      (An := 𝒜.piece (k : ℤ)) (Ln := tpMod L (k : ℤ))
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ k)
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ k)
      (twistThetaIso L 𝒜 k).hom V :=
  globalTheta_squareAt L 𝒜 (twistThetaPhi L 𝒜) (twistThetaPhi_psi L 𝒜) k V

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
