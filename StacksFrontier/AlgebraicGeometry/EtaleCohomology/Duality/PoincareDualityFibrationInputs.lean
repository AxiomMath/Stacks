module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.PoincareDualityCoreStrongInduction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopLowerShriekTraceExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.TopLowerShriekTrace

/-!
# The inputs of the fibration step of Poincaré duality

Let `k` be an algebraically closed field, `ℓ` a prime invertible in `k` and `Λ = ℤ/ℓ`. The
fibration step of Poincaré duality (`Stacks.EtaleCohomology.PoincareDualityFibrationStep`) passes
from Poincaré duality in dimensions `≤ d` to duality on a dense open of a smooth `W` of dimension
`d + 1`, which is an elementary fibration `f : U → S` over a smooth affine `S` of dimension `d`.
Writing `K = Rf_! Λ_U`, the cohomology `H^*_c(U) = H^*_c(S, K)`, and relative duality for curves
identifies `H^j(U, Λ) = Ext^j_U(Λ, Λ)` with `Hom(K, Λ_S[j - 2])`; so duality on `U` is duality
on `S` for the complex `K`, which has `R⁰ = 0`, `R¹` lisse and `R² ≅ Λ_S`, and follows by the
five lemma from duality on `S` for lisse sheaves. The following statements are the geometric
inputs of that argument, each a theorem of étale cohomology stated here as a proposition:

* `Stacks.EtaleCohomology.CohomologicalDimensionInput`: `Ext^q_X(F, G) = 0` for `q > 2 dim X`,
  `F` locally constant of finite type, on a separated scheme of finite type over `k` (for `F = Λ`
  this is `H^q(X, G) = 0` for `q > 2 dim X`; for affine `X` the sharper Artin vanishing is
  [Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V));
* `Stacks.EtaleCohomology.RelativeCurveDualityInput`: relative Poincaré duality for an elementary
  fibration, `y ↦ t_f[j] ∘ Rf_!(y)` is bijective `Ext^j_U(Λ, Λ) → Hom(Rf_! Λ_U, Λ_S[j - 2])`
  for the top-degree trace `t_f` (`Stacks.EtaleCohomology.lowerShriekTopTrace`);
* `Stacks.EtaleCohomology.LowerShriekLowDegreeInput`: `R⁰f_! Λ = 0` and `R¹f_! Λ` is locally
  constant of finite type, for an elementary fibration;
* `Stacks.EtaleCohomology.LisseDualityOfUnitInput`: Poincaré duality at `Λ` in dimensions `≤ d`
  gives Poincaré duality with locally constant coefficients on every smooth irreducible `S` of
  dimension `d` and every compactification of `S` (the non-proper analogue of
  `Stacks.EtaleCohomology.isDualityPerfect_of_isFiniteTypeLocallyConstant_of_smooth_proper`).

All four are stated over an algebraically closed field `k`, the setting of the fibration step;
over a field which is not separably closed the first one is false (for `X = Spec k`,
`H¹(k, ℤ/ℓ)` need not vanish).

They are part of the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

The statements on `Rf_!` consume the standard model `HasDerivedCategory.standard` of the derived
category, in which `Rf_!` is defined, as a local instance.

## Main definitions

* `Stacks.EtaleCohomology.CohomologicalDimensionInput`.
* `Stacks.EtaleCohomology.RelativeCurveDualityInput`.
* `Stacks.EtaleCohomology.LowerShriekLowDegreeInput`.
* `Stacks.EtaleCohomology.LisseDualityOfUnitInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open Stacks.EtaleCohomology.ExtensionTorsor

universe u

namespace Stacks.EtaleCohomology

variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [IsAlgClosed k]

/-- **Cohomological dimension of a variety, with locally constant coefficients in the source**:
for `k` algebraically closed and `X` separated, quasi-compact and locally of finite type over `k`
with `dim X ≤ n`, a locally constant sheaf of finite type `F` and any sheaf `G` of `ℤ/ℓ`-modules
on `X_ét`, `Ext^q_X(F, G) = H^q(X, 𝓗om(F, G)) = 0` for `q > 2n`. -/
def CohomologicalDimensionInput : Prop :=
  ∀ (X : Scheme.{u}) (p : X ⟶ Spec (.of k)) [LocallyOfFiniteType p] [IsSeparated p]
    [CompactSpace X] (n : ℕ), topologicalKrullDim X ≤ n →
    ∀ (F G : EtaleModules.{u, 0} (ZMod ℓ) X),
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) X.smallEtaleTopology F →
      ∀ q : ℕ, 2 * n < q → Subsingleton (Ext F G q)

section Fibration

attribute [local instance] HasDerivedCategory.standard

/-- **Relative Poincaré duality for an elementary fibration.** Let `f : U → S` be an elementary
fibration over `S` affine and smooth over `k`, with `ℓ` invertible in `k`, `j_f` a compactification
of `f` whose fibres have dimension at most one and `ν : R²f_!(f⁻¹ -) ≅ 𝟭` (for instance
`Stacks.EtaleCohomology.relativeTraceOfElementaryFibration`), with top-degree trace
`t_f : Rf_!(f⁻¹ Λ_S) ⟶ Λ_S[-2]` (`Stacks.EtaleCohomology.lowerShriekTopTrace`). Then for every
`m` the map `y ↦ t_f[m] ∘ Rf_!(y)`,
`Ext^m_U(f⁻¹ Λ_S, f⁻¹ Λ_S) → Hom_{D(S)}(Rf_!(f⁻¹ Λ_S), Λ_S[m - 2])`, is bijective
(`Rf_* Λ ≅ R𝓗om(Rf_! Λ, Λ)[-2]` on global sections). -/
def RelativeCurveDualityInput : Prop :=
  IsUnit (ℓ : k) → ∀ (U S : Scheme.{u}) (q : S ⟶ Spec (.of k)) (f : U ⟶ S) (e : ℕ)
    [SmoothOfRelativeDimension e q] [IsAffine S], IsElementaryFibration f →
    ∀ (jf : CompactificationOf (Over.mk f))
      (hf : ∀ y : S, topologicalKrullDim (jf.toBase.fiber y) ≤ 1)
      (ν : etaleModuleInverseImage.{u, 0} (ZMod ℓ) f ⋙ DerivedCategory.Plus.singleFunctor _ 0 ⋙
        derivedLowerShriek.{u, 0} f jf (ZMod ℓ) ⋙ DerivedCategory.Plus.homologyFunctor _ 2 ≅
          𝟭 (EtaleModules.{u, 0} (ZMod ℓ) S))
      (m : ℕ) (c : ℤ) (h₁ : -2 + (m : ℤ) = c),
      Function.Bijective (fun y : Ext ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj
          (unitSheaf (X := S) ℓ)) ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj
            (unitSheaf (X := S) ℓ)) m =>
        ((Stacks.TopTruncationExt.extPlus y).map
            (derivedLowerShriek.{u, 0} f jf (ZMod ℓ) ⋙ DerivedCategory.Plus.ι)).comp
          (lowerShriekTopTrace f jf ℓ hf ν (unitSheaf (X := S) ℓ)) h₁)

/-- **The low-degree direct images with compact support of an elementary fibration**: for an
elementary fibration `f : U → S` over `S` affine and smooth over `k`, `ℓ` invertible in `k`, and
any compactification `j_f` of `f`, `R⁰f_! Λ = 0` (the fibres are affine curves) and `R¹f_! Λ` is
locally constant of finite type. -/
def LowerShriekLowDegreeInput : Prop :=
  IsUnit (ℓ : k) → ∀ (U S : Scheme.{u}) (q : S ⟶ Spec (.of k)) (f : U ⟶ S) (e : ℕ)
    [SmoothOfRelativeDimension e q] [IsAffine S], IsElementaryFibration f →
    ∀ jf : CompactificationOf (Over.mk f),
      IsZero ((DerivedCategory.Plus.homologyFunctor _ 0).obj
        ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ))))) ∧
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) S.smallEtaleTopology
        ((DerivedCategory.Plus.homologyFunctor _ 1).obj
          ((derivedLowerShriek.{u, 0} f jf (ZMod ℓ)).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((etaleModuleInverseImage.{u, 0} (ZMod ℓ) f).obj (unitSheaf (X := S) ℓ)))))

end Fibration

/-- **Poincaré duality with locally constant coefficients on a smooth variety, from the constant
case**: for `ℓ` invertible in `k`, if Poincaré duality at `Λ` holds in relative dimensions `≤ d`
(`Stacks.EtaleCohomology.UnitPoincareDualityUpTo`), then for every smooth irreducible `S` of
relative dimension `d` with noetherian underlying space, every compactification `j : S → S̄` of
dimension at most `d`, every injective trace `τ` on `H^{2d}_c(S)` and every locally constant sheaf
of finite type `F` on `S`, duality holds at `j_! F`:
`H^i_c(S, F) × Ext^{2d-i}_S(F, Λ) → H^{2d}_c(S) → Λ` is perfect. -/
def LisseDualityOfUnitInput : Prop :=
  IsUnit (ℓ : k) → ∀ d : ℕ, UnitPoincareDualityUpTo ℓ k d →
    ∀ (S : Scheme.{u}) (q : S ⟶ Spec (.of k)) [SmoothOfRelativeDimension d q]
      [TopologicalSpace.NoetherianSpace S] [IrreducibleSpace S]
      (jS : CompactificationOf (Over.mk q)), topologicalKrullDim jS.space ≤ d →
      ∀ (τ : Ext (unitSheaf (X := jS.space) ℓ)
        ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jS.immersion).obj (unitSheaf (X := S) ℓ))
          (2 * d) →+ ZMod ℓ), Function.Injective τ →
      ∀ F : EtaleModules.{u, 0} (ZMod ℓ) S,
        Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod ℓ) S.smallEtaleTopology F →
        Ext.IsDualityPerfect (unitSheaf (X := jS.space) ℓ)
          ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jS.immersion).obj (unitSheaf (X := S) ℓ))
          (2 * d) τ ((etaleModuleExtensionByZero.{u, 0} (ZMod ℓ) jS.immersion).obj F)

end Stacks.EtaleCohomology

end
