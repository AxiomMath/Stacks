module

public import StacksFrontier.AlgebraicGeometry.Duality.AffineVanishing.UpperBounds
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedFunctorAmplitudeUnbounded
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck

/-!
# The upper cohomological bound on an algebraic space, at an arbitrary abelian target

Let `S` be a scheme of a big fppf site, let `X` be an algebraic space over `S`, let
`F : Mod(𝒪_X) ⥤ T` be an additive functor into **any** abelian category `T` with exact countable
products, and let `(RF, α)` be a total right derived functor of `F` on the unbounded derived
category `D(𝒪_X)`.  Suppose the higher right derived functors `R^pF` vanish on quasi-coherent
modules in every degree `p ≥ N`.  Then `RF` carries an object of `D_QCoh(𝒪_X)` living in degrees
`≤ b` to an object living in degrees `≤ b + N - 1`.

This is the statement of
`AlgebraicGeometry.Space.isLE_rightDerived_obj_of_isLE` with its target `AddCommGrpCat` replaced
by an arbitrary abelian `T`.  The intended application is the *module*-valued derived
pushforward, where `T` is `AlgebraicGeometry.Space.Modules` of a second algebraic space.

## Main results

* `AlgebraicGeometry.Space.isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus`: the upper
  bound `b + N - 1` for an object of `D_QCoh(𝒪_X)` living in degrees `≤ b`, at an arbitrary
  abelian target with exact countable products.

## Implementation notes

*No `stacks` attribute is claimed.*  The content is the upper bound of [Stacks, Tag 08D4] part
(3) — registered for a scheme as
`AlgebraicGeometry.isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus` — read for an
algebraic space, where the corresponding source statement is [Stacks, Tag 08F7] assertion (3).
Tag 08D4 is a statement about schemes, and Tag 08F7 is already registered on the spaces side, at
`AlgebraicGeometry.Space.isZero_homology_rightDerived_of_isZero_gt_unbounded` for the upper bound
of assertion (3) and at
`AlgebraicGeometry.Space.isIso_homologyFunctor_map_rightDerived_truncGE_unbounded` for assertion
(2).  This file is a target-generalized engine for those two registrations, not a further
registration of either clause, so it carries no tag.

*What is mirrored and what is substituted.*  The proof is the scheme-side proof of
`AlgebraicGeometry.isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus` verbatim in
structure: the canonical truncation triangle `τ_{≤ b-1}E ⟶ E ⟶ τ_{≥ b}E` reduces the claim to
its third vertex, concentrated in degree `b` and so covered by the vanishing hypothesis, and to
its first vertex, where the one-degree-worse bound `b - 1 + N` is supplied by the
`E = R lim τ_{≥ -n}E` argument.  Every ingredient of that argument from
`Stacks.SmallDerivedCategory` and `Stacks.Injectives` is already generic in the abelian source
and target and is used unchanged.  The one scheme-only input,
`AlgebraicGeometry.isDerivedLimit_truncGETower`, is replaced by its spaces analogue
`AlgebraicGeometry.Space.isDerivedLimit_truncGETower_modules` ([Stacks, Tag 08F6]), and
`AlgebraicGeometry.containsZero_isQuasicoherent` by the general
`SheafOfModules.isQuasicoherentOnSite_containsZero`.

*Why the bound is not obtained from the `AddCommGrpCat` statement.*  The sharper spaces-side
argument of
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentDerivedFunctorAmplitudeUnbounded.lean` kills
the `R¹ lim` term of the Milnor sequence through a Mittag-Leffler condition, which is a statement
about *surjectivity* of the transition maps and so is tied to `AddCommGrpCat`.  At an arbitrary
target the degree lost by `Stacks.SmallDerivedCategory.isLE_of_isDerivedLimit` is recovered
instead by running the limit argument on the truncation `τ_{≤ b-1}E` and reading the degree `b`
part off the truncation triangle, which is exactly the scheme-side argument.

*Instances at the module universe of the structure rings.*  `Modules.{u, u}` is `SheafOfModules`
at a module universe below the universe `u + 1` of the objects of the site, so instance search
for `HasProductsOfShape ℕ`, `EnoughInjectives` or `IsGrothendieckAbelian` there stalls on a
universe constraint.  The universe-pinned
`AlgebraicGeometry.Space.hasProductsOfShape_nat_modules_ringUniverse`,
`AlgebraicGeometry.Space.enoughInjectives_modules_ringUniverse`,
`AlgebraicGeometry.Space.isGrothendieckAbelian_modules_ringUniverse` and
`AlgebraicGeometry.Space.hasProduct_truncGETower_modules` are therefore registered as local
instances, and `attribute [local instance 5000] SheafOfModules.instAbelian` is needed for the
same reason, exactly as in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentDerivedFunctorAmplitudeUnbounded.lean`.  The
object property of quasi-coherence is introduced as a local definition `P` in the proof rather
than as a declaration of its own: the copy `qcohU` of that file is `private`, and a second
top-level copy of it would be a duplicate declaration.

## References

* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 08F7](https://stacks.math.columbia.edu/tag/08F7)
* [Stacks Project, Tag 08F6](https://stacks.math.columbia.edu/tag/08F6)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.DerivedLimit Stacks.SmallDerivedCategory

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasProductsOfShape_nat_modules_ringUniverse
attribute [local instance] enoughInjectives_modules_ringUniverse
attribute [local instance] isGrothendieckAbelian_modules_ringUniverse
attribute [local instance] hasProduct_truncGETower_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-- **The upper bound of [Stacks, Tag 08D4] part (3) for an algebraic space, at an arbitrary
abelian target.** Let `X` be an algebraic space over a scheme `S`, let `F` be an additive functor
from the `𝒪_X`-modules to an abelian category `T` with exact countable products, let `F` preserve
countable products and let `(RF, alpha)` be a total right derived functor of `F` on `D(𝒪_X)`.
Suppose the higher right derived functors `R^pF` vanish on every quasi-coherent module in every
degree `p ≥ N`. If an object `E` of `D(𝒪_X)` has quasi-coherent cohomology sheaves and lives in
degrees `≤ b`, then `RF(E)` lives in degrees `≤ b + N - 1`.

The canonical truncation triangle `τ_{≤ b-1}E ⟶ E ⟶ τ_{≥ b}E` reduces the claim to its third
vertex, concentrated in degree `b` and so covered by the vanishing hypothesis, and to its first
vertex, where the bound `b - 1 + N` — one worse, which is why the triangle is used — is supplied
by the `E = R lim τ_{≥ -n}E` argument: `E` is the derived limit of its truncations from below
([Stacks, Tag 08F6], `AlgebraicGeometry.Space.isDerivedLimit_truncGETower_modules`), `RF`
carries that derived limit to a derived limit ([Stacks, Tag 08U1]), each `RF(τ_{≥ -n}E)` lives in
degrees `≤ b + N - 1` because `τ_{≥ -n}E` is bounded, and a derived limit of such a tower lives
in degrees `≤ b + N`.

No `stacks` attribute: see the implementation notes of this file. -/
theorem isLE_rightDerivedFunctor_obj_of_isZero_rightDerivedPlus
    {T : Type*} [Category* T] [Abelian T] [HasDerivedCategory T]
    [HasProductsOfShape ℕ T] [HasExactLimitsOfShape (Discrete ℕ) T]
    (F : Modules.{u, u} B S hS X hX ⥤ T) [F.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) F]
    (RF : DerivedCategory (Modules.{u, u} B S hS X hX) ⥤ DerivedCategory T)
    (alpha : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor alpha
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X hX) (ComplexShape.up ℤ))]
    (N : ℕ)
    (hRF : ∀ M : Modules.{u, u} B S hS X hX, M.IsQuasicoherentOnSite →
      ∀ p : ℤ, (N : ℤ) ≤ p → IsZero ((F.rightDerivedPlus p).obj M))
    (E : DerivedCategory (Modules.{u, u} B S hS X hX))
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X hX) i).obj E).IsQuasicoherentOnSite)
    (b : ℤ) (hE : E.IsLE b) : (RF.obj E).IsLE (b + (N : ℤ) - 1) := by
  let P : ObjectProperty (Modules.{u, u} B S hS X hX) :=
    SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O)
  have hP : P.ContainsZero :=
    SheafOfModules.isQuasicoherentOnSite_containsZero
  let _ := Functor.IsRightDerivedFunctor.commShift RF alpha
    (HomotopyCategory.quasiIso (Modules.{u, u} B S hS X hX) (ComplexShape.up ℤ)) ℤ
  have : RF.IsTriangulated :=
    Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor F RF alpha
  have hcomp := Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective
    F RF alpha Stacks.Perfect.CechAugmentation.exists_isKInjective_quasiIso
  have : HasProductsOfShape ℕ (DerivedCategory T) :=
    Stacks.DerivedProducts.hasProductsOfShape_nat
  have hSingle : ∀ M : Modules.{u, u} B S hS X hX, P M → ∀ n : ℤ,
      (RF.obj ((DerivedCategory.singleFunctor
        (Modules.{u, u} B S hS X hX) n).obj M)).IsLE (n + ((N : ℤ) - 1)) :=
    fun M hM n ↦ isLE_obj_singleFunctor_obj F RF alpha hcomp M ((N : ℤ) - 1)
      (fun p hp ↦ hRF M hM p (by omega)) n
  have hweak : ∀ K : DerivedCategory (Modules.{u, u} B S hS X hX),
      (∀ i : ℤ, P ((DerivedCategory.homologyFunctor
          (Modules.{u, u} B S hS X hX) i).obj K)) →
      ∀ c : ℤ, K.IsLE c → (RF.obj K).IsLE (c + (N : ℤ)) := by
    intro K hK c hc
    obtain ⟨p, hp⟩ := isDerivedLimit_truncGETower_modules B S hS X hX K hK
    obtain ⟨hp', δ, hδ⟩ := Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor
      F RF alpha (truncGETower (Modules.{u, u} B S hS X hX) K) K p hp
    let := hp'
    have hlim' : IsDerivedLimit
        (truncGETower (Modules.{u, u} B S hS X hX) K ⋙ RF) (RF.obj K) := ⟨_, δ, hδ⟩
    have hbound : ∀ n : ℕ,
        ((truncGETower (Modules.{u, u} B S hS X hX) K ⋙ RF).obj ⟨n⟩).IsLE
          (c + ((N : ℤ) - 1)) := by
      intro n
      change (RF.obj ((truncGETower (Modules.{u, u} B S hS X hX) K).obj ⟨n⟩)).IsLE _
      rw [truncGETower_obj]
      exact isLE_obj_of_isGE_of_isLE (P) RF ((N : ℤ) - 1) hSingle _
        (prop_homologyFunctor_truncGE_obj (P) K hK (-(n : ℤ))) (-(n : ℤ)) c
    have h := isLE_of_isDerivedLimit
      (truncGETower (Modules.{u, u} B S hS X hX) K ⋙ RF) (RF.obj K) hlim'
      (c + ((N : ℤ) - 1)) hbound
    convert h using 1
    omega
  let Tri := (DerivedCategory.TStructure.t.triangleLEGE (b - 1) b (by omega)).obj E
  have hTri := DerivedCategory.TStructure.t.triangleLEGE_distinguished (b - 1) b (by omega) E
  have h₁ : (RF.obj Tri.obj₁).IsLE (b + (N : ℤ) - 1) := by
    have hLE : Tri.obj₁.IsLE (b - 1) := by
      change ((DerivedCategory.TStructure.t.truncLE (b - 1)).obj E).IsLE (b - 1)
      infer_instance
    have h := hweak Tri.obj₁
      (prop_homologyFunctor_truncLE_obj (P) E hcoh (b - 1)) (b - 1) hLE
    convert h using 1
    omega
  have h₃ : (RF.obj Tri.obj₃).IsLE (b + (N : ℤ) - 1) := by
    have h₃a : Tri.obj₃.IsGE b := by
      change ((DerivedCategory.TStructure.t.truncGE b).obj E).IsGE b
      infer_instance
    have h₃b : Tri.obj₃.IsLE b := by
      change ((DerivedCategory.TStructure.t.truncGE b).obj E).IsLE b
      infer_instance
    have h := isLE_obj_of_isGE_of_isLE_self (P) RF
      ((N : ℤ) - 1) hSingle Tri.obj₃
      (prop_homologyFunctor_truncGE_obj (P) E hcoh b) b
    convert h using 1
    omega
  exact DerivedCategory.TStructure.t.isLE₂ (RF.mapTriangle.obj Tri)
    (RF.map_distinguished Tri hTri) (b + (N : ℤ) - 1) h₁ h₃

end AlgebraicGeometry.Space

end
