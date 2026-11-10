module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeThetaConcrete
public import StacksFrontier.AlgebraicGeometry.TwistExistence.BasisUnique
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.PullbackAlongIsoInverse
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeSectionsSheaf

/-!
# Tag 02NC's `θ` is canonical

The `θ` of clause (1) of Tag 02NC is the inverse image along `g` of the glued identification
`Φ : ⨁_n 𝒪_{P'}(n) ≅ ⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` (the target transported to `P'`), and the glueing
runs over sections of `ℒ` chosen over the members of the trivializing basis. This file shows
that nothing chosen survives: `Φ` is the **only** homomorphism of sheaves of graded algebras
between these two which carries the homogeneous sections of `ℬ` to the *multiply* map of
clause (2). So `θ` is the inverse image along `g` of the unique such identification, and `θ`
itself is the only homomorphism of graded algebras satisfying clause (2).

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.eq_twistThetaPhi_hom`: **`Φ` is the only
  homomorphism of graded algebras carrying the homogeneous sections of `ℬ` to the multiply map.**
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.globalTheta_eq_twistTheta`: `θ` is the
  inverse image of every isomorphism of graded algebras doing so.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.eq_twistTheta_hom` and `eq_twistTheta`:
  **`θ` is the only homomorphism (isomorphism) of graded algebras
  `g^*(⨁_n 𝒪_{P'}(n)) ⟶ ⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` satisfying clause (2).** A homomorphism out of
  `g^*` is the pullback of its restriction back to `P'`
  (`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.pullbackInvHom_restrictBack`), and clause (2)
  for it is the compatibility of that restriction with the homogeneous sections.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.eq_twistTheta_hom_of_squareAt`: the same, with
  clause (2) on pure tensors, as the source states it.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.GradedAlgebraTwist

universe u

namespace Stacks.AlgebraicGeometry.RelativeInvertibleTwist

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]
  (𝒜 : SheafGradedAlgebra S)

/-- **The glued identification is the only homomorphism of sheaves of graded algebras
`⨁_n 𝒪_{P'}(n) ⟶ (⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n})|_{P'}` carrying the homogeneous-section map of `P'` to
the *multiply* map**, transported to `P'`. No trivializing section enters the statement. -/
theorem eq_twistThetaPhi_hom
    {f : Tag07ZGTwist.twistAlgebra (twist 𝒜 L) ⟶ transportedTarget L 𝒜}
    (hf : ∀ k : ℕ, (GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ k ≫
      (Scheme.Modules.pushforward (relativeProj (twist 𝒜 L)).toBase).map (f.app k) =
        transportedPsi L 𝒜 k) :
    f = (twistThetaPhi L 𝒜).hom :=
  SheafOfModules.GradedAlgebra.Hom.ext fun n =>
    (TwistExistenceBasis.app_eq_glueIso_hom (D := TwistExistenceBasis.BasisTwistData.ofTwistData
        (𝔅 := trivializingOpens L) (GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)))
      (E := targetTwistData L 𝒜 (absTwistCompare L 𝒜)) (f := f)
      (isBasis_trivializingOpens L) (fun _ h => h.1) hf n).trans
    (twistThetaPhi_hom_app L 𝒜 n).symm

/-- **The glued identification is the only isomorphism of graded algebras carrying the
homogeneous-section map of `P'` to the multiply map.** -/
theorem eq_twistThetaPhi {Φ : Tag07ZGTwist.twistAlgebra (twist 𝒜 L) ≅ transportedTarget L 𝒜}
    (hΦ : ∀ k : ℕ, (GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ k ≫
      (Scheme.Modules.pushforward (relativeProj (twist 𝒜 L)).toBase).map (Φ.hom.app k) =
        transportedPsi L 𝒜 k) :
    Φ = twistThetaPhi L 𝒜 :=
  Iso.ext (eq_twistThetaPhi_hom L 𝒜 hΦ)

/-- **Tag 02NC's `θ` is canonical**: it is the inverse image along `g` of every isomorphism of
graded algebras `⨁_n 𝒪_{P'}(n) ≅ (⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n})|_{P'}` carrying the homogeneous-section
map of `P'` to the *multiply* map — and there is exactly one such isomorphism. -/
theorem globalTheta_eq_twistTheta
    {Φ : Tag07ZGTwist.twistAlgebra (twist 𝒜 L) ≅ transportedTarget L 𝒜}
    (hΦ : ∀ k : ℕ, (GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ k ≫
      (Scheme.Modules.pushforward (relativeProj (twist 𝒜 L)).toBase).map (Φ.hom.app k) =
        transportedPsi L 𝒜 k) :
    globalTheta L 𝒜 Φ = twistTheta L 𝒜 :=
  congrArg (globalTheta L 𝒜) (eq_twistThetaPhi L 𝒜 hΦ)

/-- **Tag 02NC's `θ` is the only homomorphism of sheaves of graded algebras
`g^*(⨁_n 𝒪_{P'}(n)) ⟶ ⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` satisfying clause (2)**: if `α` carries, for every
open `V` of the base and every degree `k`, the section of `𝒪_{P'}(k)` over `π'^{-1}V` given by
`b ∈ ℬ_k(V)` to the *multiply* map applied to `b`, then `α = θ`. Nothing chosen enters the
statement. -/
theorem eq_twistTheta_hom
    {α : Stacks.RingedSpace.pullbackGradedAlgebra (relativeTwistHom L 𝒜).toLRSHom.toShHom
        (Tag07ZGTwist.twistAlgebra (twist 𝒜 L)) ⟶ targetAlgebra L 𝒜}
    (hα : ∀ (k : ℕ) (V : S.Opens) (b : ((twist 𝒜 L).piece (k : ℤ)).val.obj (op V)),
      RelativeTwistSections.thetaSections (relativeProj 𝒜).toBase
          (relativeProj (twist 𝒜 L)).toBase (relativeTwistHom L 𝒜)
          (relativeTwistHom_comp_toBase L 𝒜) (α.app (k : ℤ)) V
          (((GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ k).val.app (op V) b) =
        (RelativeTwistSections.multiplyHom (relativeProj 𝒜).toBase
            (An := 𝒜.piece (k : ℤ)) (Ln := tpMod L (k : ℤ))
            ((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ k)).val.app (op V) b) :
    α = (twistTheta L 𝒜).hom := by
  have hrb : ∀ k : ℕ, (GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ k ≫
      (Scheme.Modules.pushforward (relativeProj (twist 𝒜 L)).toBase).map
        ((restrictBack (relativeTwistIso L 𝒜) α).app k) = transportedPsi L 𝒜 k := by
    intro k
    refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
      ModuleCat.hom_ext (LinearMap.ext fun b => ?_))
    obtain ⟨V⟩ := V
    have hle : (relativeTwistIso L 𝒜).hom ''ᵁ ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ V) ≤
        (relativeProj 𝒜).toBase ⁻¹ᵁ V := by
      rintro _ ⟨x, hx, rfl⟩
      change ((relativeTwistIso L 𝒜).hom ≫ (relativeProj 𝒜).toBase) x ∈ V
      rw [relativeTwistIso_hom_comp_toBase]
      exact hx
    change ((restrictBack (relativeTwistIso L 𝒜) α).app k).val.app
        (op ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ V))
        (((GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ k).val.app (op V) b) =
      (transportedPsi L 𝒜 k).val.app (op V) b
    refine (restrictBack_app (relativeTwistIso L 𝒜) α k _ _).trans ?_
    refine Eq.trans ?_ (transportedPsi_app L 𝒜 k V hle b).symm
    refine Eq.trans ?_ (congrArg (((targetAlgebra L 𝒜).piece (k : ℤ)).val.map
      (homOfLE hle).op) (hα k V b))
    exact (PresheafOfModules.map_map_eq_map ((targetAlgebra L 𝒜).piece (k : ℤ)).val
      (homOfLE (RelativeTwistSections.preimage_preimage_eq (relativeProj 𝒜).toBase
        (relativeProj (twist 𝒜 L)).toBase (relativeTwistHom L 𝒜)
        (relativeTwistHom_comp_toBase L 𝒜) V).ge).op (homOfLE hle).op _ _).symm
  refine (pullbackInvHom_restrictBack (relativeTwistIso L 𝒜) α).symm.trans ?_
  exact congrArg (pullbackInvHom (relativeTwistIso L 𝒜)) (eq_twistThetaPhi_hom L 𝒜 hrb)

/-- **Tag 02NC's `θ` is the only isomorphism of sheaves of graded algebras
`g^*(⨁_n 𝒪_{P'}(n)) ≅ ⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` satisfying clause (2).** -/
theorem eq_twistTheta
    {θ : Stacks.RingedSpace.pullbackGradedAlgebra (relativeTwistHom L 𝒜).toLRSHom.toShHom
        (Tag07ZGTwist.twistAlgebra (twist 𝒜 L)) ≅ targetAlgebra L 𝒜}
    (hθ : ∀ (k : ℕ) (V : S.Opens) (b : ((twist 𝒜 L).piece (k : ℤ)).val.obj (op V)),
      RelativeTwistSections.thetaSections (relativeProj 𝒜).toBase
          (relativeProj (twist 𝒜 L)).toBase (relativeTwistHom L 𝒜)
          (relativeTwistHom_comp_toBase L 𝒜) (θ.hom.app (k : ℤ)) V
          (((GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ k).val.app (op V) b) =
        (RelativeTwistSections.multiplyHom (relativeProj 𝒜).toBase
            (An := 𝒜.piece (k : ℤ)) (Ln := tpMod L (k : ℤ))
            ((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ k)).val.app (op V) b) :
    θ = twistTheta L 𝒜 :=
  Iso.ext (eq_twistTheta_hom L 𝒜 hθ)

/-- **Tag 02NC's `θ` is the only homomorphism of sheaves of graded algebras
`g^*(⨁_n 𝒪_{P'}(n)) ⟶ ⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` making the squares of clause (2) commute**, in the
form the source states them: on pure tensors `a ⊗ l` with `a ∈ 𝒜_n(V)`, `l ∈ ℒ^{⊗ n}(V)`, for
every open `V` of the base and every `n`. -/
theorem eq_twistTheta_hom_of_squareAt
    {α : Stacks.RingedSpace.pullbackGradedAlgebra (relativeTwistHom L 𝒜).toLRSHom.toShHom
        (Tag07ZGTwist.twistAlgebra (twist 𝒜 L)) ⟶ targetAlgebra L 𝒜}
    (hα : ∀ (n : ℕ) (V : S.Opens),
      RelativeTwistSections.SquareAt (relativeProj 𝒜).toBase (relativeProj (twist 𝒜 L)).toBase
        (relativeTwistHom L 𝒜) (relativeTwistHom_comp_toBase L 𝒜)
        (An := 𝒜.piece (n : ℤ)) (Ln := tpMod L (n : ℤ))
        ((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ n)
        ((GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ n) (α.app (n : ℤ)) V) :
    α = (twistTheta L 𝒜).hom :=
  eq_twistTheta_hom L 𝒜 fun k V b =>
    RelativeTwistSections.thetaSections_eq_multiplyHom_of_squareAt (relativeProj 𝒜).toBase
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ k) (relativeProj (twist 𝒜 L)).toBase
      (relativeTwistHom L 𝒜) (relativeTwistHom_comp_toBase L 𝒜)
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ k) (α.app (k : ℤ)) (hα k) V b

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
