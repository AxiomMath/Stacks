module

public import StacksFrontier.AlgebraicGeometry.PullbackTensor.PullbackAlongIso
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjInvertibleTwistRelativeSections

/-!
# Tag 02NC's `θ` over `Proj_S(𝒜)`, from an identification over `Proj_S(ℬ)`

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `ℒ` an invertible `𝒪_S`-module,
`ℬ` the twist of `𝒜` by `ℒ`, `P = Proj_S(𝒜)`, `P' = Proj_S(ℬ)` and `g : P ⟶ P'` the canonical
isomorphism over `S`. Clause (1) of Tag 02NC is an isomorphism of `ℤ`-graded algebras
`θ : g^*(⨁_n 𝒪_{P'}(n)) ⟶ ⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`.

This file produces `θ` from an isomorphism `Φ` of sheaves of graded algebras on `P'` between
`⨁_n 𝒪_{P'}(n)` and the target `⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` transported to `P'`
(`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.transportedTarget`): `θ` is the inverse image
of `Φ` along `g`. When `Φ` carries the homogeneous sections of `ℬ` to the *multiply* map of
clause (2), the square of clause (2) commutes over every open of the base.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.globalTheta`: **`θ`, as an isomorphism of
  sheaves of `ℤ`-graded algebras on `P`.**
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.globalThetaIso`: its component
  `θ_n : g^*𝒪_{P'}(n) ≅ 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`.

## Main results

* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.globalTheta_hom_app_zero_one`: `θ` preserves
  the unit, as every isomorphism of sheaves of graded algebras does
  (`Stacks.AlgebraicGeometry.RelativeInvertibleTwist.iso_hom_app_zero_one`).
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.globalThetaIso_unit`: `θ_n` on the image of
  a section of `𝒪_{P'}(n)`.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.globalTheta_thetaSections`: `θ_k` carries the
  homogeneous section of `b ∈ ℬ_k(V)` to the *multiply* map applied to `b`.
* `Stacks.AlgebraicGeometry.RelativeInvertibleTwist.globalTheta_squareAt`: **the square of
  clause (2)** over every open of the base.

## References

* [Stacks Project, Tag 02NC](https://stacks.math.columbia.edu/tag/02NC)
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

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

variable {S : Scheme.{u}} (L : S.Modules)
  [Stacks.SheafOfModules.IsInvertible S.sheaf.obj S.ringCatSheaf.property L]
  (𝒜 : SheafGradedAlgebra S)
  (Φ : Tag07ZGTwist.twistAlgebra (twist 𝒜 L) ≅ transportedTarget L 𝒜)

/-- **Tag 02NC's `θ : g^*(⨁_n 𝒪_{P'}(n)) ≅ ⨁_n 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}`**, as an isomorphism of
sheaves of `ℤ`-graded algebras on `P = Proj_S(𝒜)`: the inverse image along `g` of `Φ`. -/
def globalTheta :
    Stacks.RingedSpace.pullbackGradedAlgebra (relativeTwistHom L 𝒜).toLRSHom.toShHom
        (Tag07ZGTwist.twistAlgebra (twist 𝒜 L)) ≅ targetAlgebra L 𝒜 :=
  pullbackInvIso (relativeTwistIso L 𝒜) Φ

/-- **The component `θ_n : g^*𝒪_{P'}(n) ≅ 𝒪_P(n) ⊗ π^*ℒ^{⊗ n}` of Tag 02NC's `θ`.** -/
def globalThetaIso (n : ℤ) :
    (Scheme.Modules.pullback (relativeTwistHom L 𝒜)).obj
        (Tag07ZGTwist.relativeTwist (twist 𝒜 L) n) ≅
      tensorMod (Tag07ZGTwist.relativeTwist 𝒜 n)
        ((Scheme.Modules.pullback (relativeProj 𝒜).toBase).obj (tpMod L n)) where
  hom := (globalTheta L 𝒜 Φ).hom.app n
  inv := (globalTheta L 𝒜 Φ).inv.app n
  hom_inv_id := congrArg (fun φ => SheafOfModules.GradedAlgebra.Hom.app φ n)
    (globalTheta L 𝒜 Φ).hom_inv_id
  inv_hom_id := congrArg (fun φ => SheafOfModules.GradedAlgebra.Hom.app φ n)
    (globalTheta L 𝒜 Φ).inv_hom_id

/-- The forward map of `θ_n` is the degree-`n` component of the forward map of `θ`. -/
theorem globalThetaIso_hom (n : ℤ) :
    (globalThetaIso L 𝒜 Φ n).hom = (globalTheta L 𝒜 Φ).hom.app n := rfl

/-- **An isomorphism of sheaves of graded algebras preserves the unit.** Its component in degree
zero is multiplicative and bijective on sections, so the image of `1` is a left identity for every
section, in particular for `1`. -/
theorem iso_hom_app_zero_one {X : Scheme.{u}} {A B : SchemeGradedAlgebra X} (e : A ≅ B)
    (W : X.Opensᵒᵖ) : (e.hom.app 0).val.app W (A.one.eval W) = B.one.eval W := by
  have hx : (e.hom.app 0).val.app W ((e.inv.app 0).val.app W (B.one.eval W)) = B.one.eval W :=
    congrArg (fun φ => φ.val.app W (B.one.eval W))
      (congrArg (fun φ => SheafOfModules.GradedAlgebra.Hom.app φ 0) e.inv_hom_id)
  refine (eq_of_heq (B.mul_one 0 W ((e.hom.app 0).val.app W (A.one.eval W)))).symm.trans ?_
  refine (congrArg (fun z => (B.mul 0 0).app W ((e.hom.app 0).val.app W (A.one.eval W)) z)
    hx.symm).trans ?_
  refine (e.hom.map_mul 0 0 W (A.one.eval W)
    ((e.inv.app 0).val.app W (B.one.eval W))).symm.trans ?_
  exact (congrArg ((e.hom.app 0).val.app W)
    (eq_of_heq (A.one_mul 0 W ((e.inv.app 0).val.app W (B.one.eval W))))).trans hx

/-- **Tag 02NC's `θ` preserves the unit**: it is an isomorphism of unital `ℤ`-graded algebras. -/
theorem globalTheta_hom_app_zero_one (W : (relativeProj 𝒜).scheme.Opensᵒᵖ) :
    ((globalTheta L 𝒜 Φ).hom.app 0).val.app W
        ((Stacks.RingedSpace.pullbackGradedAlgebra (relativeTwistHom L 𝒜).toLRSHom.toShHom
          (Tag07ZGTwist.twistAlgebra (twist 𝒜 L))).one.eval W) =
      (targetAlgebra L 𝒜).one.eval W :=
  iso_hom_app_zero_one (globalTheta L 𝒜 Φ) W

/-- **`θ_n` on the image of a section of `𝒪_{P'}(n)`**: the restriction of its image under `Φ`. -/
theorem globalThetaIso_unit (n : ℤ) (U : (relativeProj (twist 𝒜 L)).scheme.Opens)
    (s : (Tag07ZGTwist.relativeTwist (twist 𝒜 L) n).val.obj (op U)) :
    (globalThetaIso L 𝒜 Φ n).hom.val.app (op (relativeTwistHom L 𝒜 ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction (relativeTwistHom L 𝒜)).unit.app
          (Tag07ZGTwist.relativeTwist (twist 𝒜 L) n)).val.app (op U) s) =
      ((targetAlgebra L 𝒜).piece n).val.map
        (homOfLE (inv_preimage_le_image (relativeTwistIso L 𝒜) U)).op
        ((Φ.hom.app n).val.app (op U) s) :=
  pullbackInvIso_unit (relativeTwistIso L 𝒜) Φ n U s

/-- **`θ_k` carries the homogeneous section of `b ∈ ℬ_k(V)` to the *multiply* map applied to
`b`**, over every open `V` of the base, once `Φ` carries the homogeneous-section map of `P'` to the
*multiply* map transported to `P'`. -/
theorem globalTheta_thetaSections
    (hΦ : ∀ k : ℕ, (GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ k ≫
      (Scheme.Modules.pushforward (relativeProj (twist 𝒜 L)).toBase).map (Φ.hom.app k) =
        transportedPsi L 𝒜 k)
    (k : ℕ) (V : S.Opens) (b : ((twist 𝒜 L).piece (k : ℤ)).val.obj (op V)) :
    RelativeTwistSections.thetaSections (relativeProj 𝒜).toBase
        (relativeProj (twist 𝒜 L)).toBase (relativeTwistHom L 𝒜)
        (relativeTwistHom_comp_toBase L 𝒜) (globalThetaIso L 𝒜 Φ k).hom V
        (((GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ k).val.app (op V) b) =
      (RelativeTwistSections.multiplyHom (relativeProj 𝒜).toBase
          (An := 𝒜.piece (k : ℤ)) (Ln := tpMod L (k : ℤ))
          ((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ k)).val.app (op V) b := by
  have hle : (relativeTwistIso L 𝒜).hom ''ᵁ ((relativeProj (twist 𝒜 L)).toBase ⁻¹ᵁ V) ≤
      (relativeProj 𝒜).toBase ⁻¹ᵁ V := by
    rintro _ ⟨x, hx, rfl⟩
    change ((relativeTwistIso L 𝒜).hom ≫ (relativeProj 𝒜).toBase) x ∈ V
    rw [relativeTwistIso_hom_comp_toBase]
    exact hx
  change ((targetAlgebra L 𝒜).piece (k : ℤ)).val.map _
      ((globalThetaIso L 𝒜 Φ k).hom.val.app _
        (((Scheme.Modules.pullbackPushforwardAdjunction (relativeTwistHom L 𝒜)).unit.app
          (Tag07ZGTwist.relativeTwist (twist 𝒜 L) k)).val.app _ _)) = _
  refine (congrArg (((targetAlgebra L 𝒜).piece (k : ℤ)).val.map _)
    (globalThetaIso_unit L 𝒜 Φ (k : ℤ) _ _)).trans ?_
  refine (congrArg (fun z => ((targetAlgebra L 𝒜).piece (k : ℤ)).val.map _
    (((targetAlgebra L 𝒜).piece (k : ℤ)).val.map _ z))
    ((congrArg (fun φ => φ.val.app (op V) b) (hΦ k)).trans
      (transportedPsi_app L 𝒜 k V hle b))).trans ?_
  have key : ∀ {P Q R : (relativeProj 𝒜).scheme.Opens} (i : op P ⟶ op Q) (j : op Q ⟶ op R)
      (l : op R ⟶ op P) (z : ((targetAlgebra L 𝒜).piece (k : ℤ)).val.obj (op P)),
      ((targetAlgebra L 𝒜).piece (k : ℤ)).val.map l
          (((targetAlgebra L 𝒜).piece (k : ℤ)).val.map j
            (((targetAlgebra L 𝒜).piece (k : ℤ)).val.map i z)) = z := by
    intro P Q R i j l z
    refine (congrArg (((targetAlgebra L 𝒜).piece (k : ℤ)).val.map l)
      (PresheafOfModules.map_map_eq_map _ i j (i ≫ j) z)).trans ?_
    refine (PresheafOfModules.map_map_eq_map _ (i ≫ j) l (𝟙 _) z).trans ?_
    exact congrArg (fun f => f z) (congrArg (fun f => ConcreteCategory.hom f)
      (((targetAlgebra L 𝒜).piece (k : ℤ)).val.map_id _))
  exact key _ _ _ _

/-- **The square of clause (2) of Tag 02NC for `θ`**, over every open of the base, once `Φ`
carries the homogeneous-section map of `P'` to the *multiply* map transported to `P'`. -/
theorem globalTheta_squareAt
    (hΦ : ∀ k : ℕ, (GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ k ≫
      (Scheme.Modules.pushforward (relativeProj (twist 𝒜 L)).toBase).map (Φ.hom.app k) =
        transportedPsi L 𝒜 k)
    (k : ℕ) (V : S.Opens) :
    RelativeTwistSections.SquareAt (relativeProj 𝒜).toBase (relativeProj (twist 𝒜 L)).toBase
      (relativeTwistHom L 𝒜) (relativeTwistHom_comp_toBase L 𝒜)
      (An := 𝒜.piece (k : ℤ)) (Ln := tpMod L (k : ℤ))
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ k)
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ k)
      (globalThetaIso L 𝒜 Φ k).hom V :=
  RelativeTwistSections.squareAt_of_multiplyHom (relativeProj 𝒜).toBase
    ((GluedTwistAlgebra.twistDataOfGradedAlgebra 𝒜).ψ k) (relativeProj (twist 𝒜 L)).toBase
    (relativeTwistHom L 𝒜) (relativeTwistHom_comp_toBase L 𝒜)
    ((GluedTwistAlgebra.twistDataOfGradedAlgebra (twist 𝒜 L)).ψ k)
    (globalThetaIso L 𝒜 Φ k).hom (globalTheta_thetaSections L 𝒜 Φ hΦ k) V

end Stacks.AlgebraicGeometry.RelativeInvertibleTwist

end
