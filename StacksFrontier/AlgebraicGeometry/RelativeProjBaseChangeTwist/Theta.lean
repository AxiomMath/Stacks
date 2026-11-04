module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBaseChangeTwist.BasisData
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.GradedAlgebraPullbackComp

/-!
# Base change of relative Proj and of its twists

For a quasi-coherent graded `𝒪_S`-algebra `A` and a morphism `g : S' ⟶ S`, the canonical
isomorphism `r : Proj_{S'}(g^*A) ≅ S' ×_S Proj_S(A)` and the isomorphism of `ℤ`-graded algebras
`θ : r^* pr₂^* (⨁_d 𝒪(d)) ≅ ⨁_d 𝒪_{Proj_{S'}(g^*A)}(d)`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.baseChangeTheta`: the isomorphism `θ`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.relativeProj_baseChange_twist`.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry Limits
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.Tag07ZGTwist

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

section Generic

variable {P' Q P : Scheme.{u}} (r : P' ⟶ Q) (pr : Q ⟶ P) (f : P' ⟶ P) (hf : r ≫ pr = f)
  (G : SheafOfModules.GradedAlgebra.{u, u} (Stacks.RingedSpace.structureRingSheaf P.toRingedSpace))
  {T : RelativeProjTwists.SchemeGradedAlgebra P'}

/-- An isomorphism out of `f^*G`, read as an isomorphism out of `r^*pr^*G` for `r ≫ pr = f`:
the pseudofunctoriality isomorphism of the inverse image of graded algebras, then `f^*G`. -/
def thetaOfComp (θ' : pbAlgS f G ≅ T) :
    pbAlgS r (Stacks.RingedSpace.pullbackGradedAlgebra pr.toLRSHom.toShHom G) ≅ T :=
  (GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso G r pr ≪≫
    GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso G hf) ≪≫ θ'

end Generic

variable {S S' : Scheme.{u}} (A : SheafGradedAlgebra S) (g : S' ⟶ S)

/-- **The isomorphism `θ : r^* pr₂^* (⨁_d 𝒪_{Proj_S(A)}(d)) ≅ ⨁_d 𝒪_{Proj_{S'}(g^*A)}(d)`** of
`ℤ`-graded algebras on `Proj_{S'}(g^*A)`. -/
def baseChangeTheta :
    pbAlgS (baseChangeIso A g).hom
        (Stacks.RingedSpace.pullbackGradedAlgebra
          (pullback.snd g
            (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase).toLRSHom.toShHom
          (twistAlgebra A)) ≅
      twistAlgebra (A.pullback g) :=
  thetaOfComp (baseChangeIso A g).hom
    (pullback.snd g (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase)
    (baseChangeHom A g) (baseChangeIso_hom_snd A g) (twistAlgebra A) (pulledTwistIso A g)

/-- **Stacks Project, Tag 01O3.** Let `S` be a scheme, `A` a quasi-coherent sheaf of graded
`𝒪_S`-algebras and `g : S' → S` a morphism of schemes. The canonical isomorphism
`r : Proj_{S'}(g^*A) ≅ S' ×_S Proj_S(A)` (`baseChangeIso`) lies over `S'` and has second
component the base change `Proj_{S'}(g^*A) → Proj_S(A)`, and `θ` (`baseChangeTheta`) is an
isomorphism of `ℤ`-graded algebras
`r^* pr₂^* (⨁_d 𝒪_{Proj_S(A)}(d)) ≅ ⨁_d 𝒪_{Proj_{S'}(g^*A)}(d)`, which preserves the unit. -/
@[stacks 01O3 "the canonical isomorphism r : Proj_S'(g^*A) -> S' x_S Proj_S(A) over S', and the \
isomorphism theta : r^* pr_2^* ((+)_d O(d)) -> (+)_d O_{Proj_S'(g^*A)}(d) of Z-graded algebras, \
preserving the unit"]
theorem relativeProj_baseChange_twist :
    (baseChangeIso A g).hom ≫
          pullback.fst g (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase =
        (Stacks.AlgebraicGeometry.RelativeProj.relativeProj (A.pullback g)).toBase ∧
      (baseChangeIso A g).hom ≫
          pullback.snd g (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase =
        baseChangeHom A g ∧
      ∀ U, ((baseChangeTheta A g).hom.app 0).val.app U
          ((pbAlgS (baseChangeIso A g).hom
            (Stacks.RingedSpace.pullbackGradedAlgebra
              (pullback.snd g
                (Stacks.AlgebraicGeometry.RelativeProj.relativeProj A).toBase).toLRSHom.toShHom
              (twistAlgebra A))).one.eval U) =
        (twistAlgebra (A.pullback g)).one.eval U :=
  ⟨baseChangeIso_hom_fst A g, baseChangeIso_hom_snd A g,
    fun U => SheafOfModules.GradedAlgebra.iso_hom_app_one_eval (baseChangeTheta A g) U⟩

end Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

end
