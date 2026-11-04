module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SmoothAffineCurveCompactSupportZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageTopGysinMorphism
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Relative cohomological purity along an étale divisor of a smooth relative curve

Let `W` be smooth over a field `k`, `g : U ⟶ W` smooth of relative dimension one, `i : Z ⟶ U` a
closed immersion with `Z = V(f)` and `Z ⟶ W` finite étale, and `j : U° ⟶ U` the open complement.
For a locally constant sheaf `H` of finite type of `ℤ/N`-modules on `U`, `N` invertible in `k`,
cohomological purity in codimension one (SGA 4 XVI 3.7, Milne, *Étale cohomology* VI.5) says

* `(P0)` the unit `H ⟶ j_* j⁻¹ H` is an isomorphism;
* `(P1)` `R¹ j_*(j⁻¹ H) ≅ i_*(i⁻¹ H)(-1)`; it is stated for the levels of a lisse ℓ-adic sheaf
  `G`, as an isomorphism of towers of `ℤ_ℓ`-sheaves with `i_*` of the levels of the twist
  `tw Z (i⁻¹ G)` (the Tate twist `𝓗om(μ_{ℓⁿ⁺¹}, -)` on the levels);
* `(P2)` `R^q j_*(j⁻¹ H) = 0` for `q ≥ 2`;
* `(BC1)` the formation of `R¹ j_*(j⁻¹ H)` commutes with base change along any `W' ⟶ W` with
  `W'` smooth over a field: the degree-one cohomology of the derived base change map
  `u⁻¹ R j_* ⟶ R j'_* u°⁻¹` (`Stacks.EtaleCohomology.etaleModuleDerivedBaseChange`) at
  `j⁻¹ H` is an isomorphism. This is the naturality of the canonical isomorphism of `(P1)`
  under pullback, read through the base change of `i_*` along the finite `i`.

This file states these four facts as one proposition
(`Stacks.EtaleCohomology.RelativeCurvePurityInput B ℓ tw`), and the trace property of the twist
as another (`Stacks.EtaleCohomology.LAdicTwistInput B ℓ tw`).

## Main definitions

* `Stacks.EtaleCohomology.RelativeCurvePuritySheafInput`: the sheaf-level statements `(P0)`, `(P2)`
  and `(BC1)`.
* `Stacks.EtaleCohomology.RelativeCurvePurityLAdicInput`: the ℓ-adic tower form of `(P1)` for the
  twist `tw`.
* `Stacks.EtaleCohomology.RelativeCurvePurityInput`: the conjunction of the two.
* `Stacks.EtaleCohomology.LAdicTwistInput`: `tw` preserves lisse sheaves and multiplies the
  Frobenius traces at a closed point `x` by powers of `#κ(x)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

-- `AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives` has a free universe; with it in scope
-- the instance problems `EnoughInjectives (EtaleModules Λ X)` get stuck on a universe constraint.
attribute [-instance] AlgebraicGeometry.Scheme.etaleSheaves_enoughInjectives

/-- The locally constant sheaves of finite type of `ℤ/N`-modules on `X_étale`. -/
abbrev lccModules (X : Scheme.{u}) (N : ℕ) : ObjectProperty (EtaleModules.{u, 0} (ZMod N) X) :=
  fun H => Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant (ZMod N) X.smallEtaleTopology H

section Pieces

variable (N : ℕ) {U Z U₀ : Scheme.{u}} (i : Z ⟶ U) (j : U₀ ⟶ U) [IsOpenImmersion j]

/-- `(P0)`: the unit `H ⟶ j_* j⁻¹ H` is an isomorphism on locally constant sheaves of finite
type. -/
def PurityUnitIso : Prop :=
  ∀ H : EtaleModules.{u, 0} (ZMod N) U, lccModules U N H →
    IsIso ((etaleModuleRestrictionDirectImageAdj.{u, 0} (ZMod N) j).unit.app H)

/-- `(P2)`: `R^q j_*(j⁻¹ H) = 0` for `q ≥ 2` and `H` locally constant of finite type. -/
def PurityHigherDirectImageVanishing : Prop :=
  ∀ H : EtaleModules.{u, 0} (ZMod N) U, lccModules U N H → ∀ q : ℕ, 2 ≤ q →
    IsZero (((etaleModuleDirectImage.{u, 0} (ZMod N) j).rightDerived q).obj
      ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj H))

/-- `(BC1)` at one cartesian square: the degree-one cohomology of the derived base change map
`u⁻¹ R j_* ⟶ R j'_* u₀⁻¹` at `j⁻¹ H` is an isomorphism for `H` locally constant of finite type. -/
def PurityFirstBaseChangeIso {U' U₀' : Scheme.{u}} (u' : U' ⟶ U) (j' : U₀' ⟶ U')
    [IsOpenImmersion j'] (u₀ : U₀' ⟶ U₀) (sq : IsPullback u₀ j' j u') : Prop :=
  ∀ H : EtaleModules.{u, 0} (ZMod N) U, lccModules U N H →
    IsIso ((DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, 0} (ZMod N) U') 1).map
      ((etaleModuleDerivedBaseChange.{u, 0} (ZMod N) j j' u' u₀ sq.w.symm).app
        ((DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} (ZMod N) U₀) 0).obj
          ((etaleModuleRestriction.{u, 0} (ZMod N) j).obj H))))

end Pieces

/-- **The sheaf-level part of relative purity**: `(P0)`, `(P2)` and `(BC1)`, for `g : U ⟶ W` smooth
of relative dimension one over `W` smooth over a field `k`, a closed immersion `i : Z ⟶ U` with
`Z = V(f)` and `Z ⟶ W` finite étale, `j : U₀ ⟶ U` the open complement, and `N` invertible in `k`;
`(BC1)` along every `W' ⟶ W` with `W'` smooth over a field. -/
def RelativeCurvePuritySheafInput : Prop :=
  ∀ (k : Type u) [Field k] (N : ℕ), IsUnit (N : k) →
  ∀ (U W Z U₀ : Scheme.{u}) (pW : W ⟶ Spec (.of k)) [Smooth pW] (g : U ⟶ W)
    [SmoothOfRelativeDimension 1 g] (i : Z ⟶ U) [IsClosedImmersion i] [IsFinite (i ≫ g)]
    [Etale (i ≫ g)] (f : Γ(U, ⊤)), Set.range i.base = U.zeroLocus {f} →
  ∀ (j : U₀ ⟶ U) [IsOpenImmersion j], Set.range j.base = (Set.range i.base)ᶜ →
    PurityUnitIso N j ∧ PurityHigherDirectImageVanishing N j ∧
    ∀ (k' : Type u) [Field k'] (W' U' U₀' : Scheme.{u}) (pW' : W' ⟶ Spec (.of k')) [Smooth pW']
      (uW : W' ⟶ W) (u' : U' ⟶ U) (g' : U' ⟶ W'), IsPullback u' g' g uW →
      ∀ (j' : U₀' ⟶ U') [IsOpenImmersion j'] (u₀ : U₀' ⟶ U₀) (sq : IsPullback u₀ j' j u'),
        PurityFirstBaseChangeIso N j u' j' u₀ sq

section LAdic

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **The ℓ-adic tower form of `(P1)`**, with the twist `tw` of ℓ-adic sheaves: for a lisse `G`
on `U` (in the setting of `Stacks.EtaleCohomology.RelativeCurvePuritySheafInput`, with `ℓ`
invertible in `k`), the tower `n ↦ R¹ j_*(j⁻¹ Gₙ)` of `ℤ_ℓ`-sheaves is `i_*` of the tower of
levels of the twist `tw Z (i⁻¹ G)`. -/
def RelativeCurvePurityLAdicInput
    (tw : ∀ (X : B.Scheme) [IsNoetherian X.1], LAdicSheaf.{u, u + 1} B X ℓ →
      LAdicSheaf.{u, u + 1} B X ℓ) : Prop :=
  ∀ (k : Type u) [Field k], IsUnit (ℓ : k) →
  ∀ (U W Z : B.Scheme) [IsNoetherian U.1] [IsNoetherian Z.1] (U₀ : Scheme.{u})
    (pW : W.1 ⟶ Spec (.of k)) [Smooth pW] (g : U ⟶ W)
    [SmoothOfRelativeDimension 1 (B.inclusion.map g)] (i : Z ⟶ U)
    [IsClosedImmersion (B.inclusion.map i)] [IsFinite (B.inclusion.map (i ≫ g))]
    [Etale (B.inclusion.map (i ≫ g))] (f : Γ(B.inclusion.obj U, ⊤)),
    Set.range (B.inclusion.map i).base = (B.inclusion.obj U).zeroLocus {f} →
  ∀ (j : U₀ ⟶ U.1) [IsOpenImmersion j], Set.range j.base = (Set.range (B.inclusion.map i).base)ᶜ →
  ∀ G : LAdicSheaf.{u, u + 1} B U ℓ, G.IsLisse →
    Nonempty (LAdicSheaf.padicTower B U ℓ G ⋙ etaleModuleRestriction.{u, 0} ℤ_[ℓ] j ⋙
        (etaleModuleDirectImage.{u, 0} ℤ_[ℓ] j).rightDerived 1 ≅
      LAdicSheaf.padicTower B Z ℓ (tw Z (LAdicSheaf.inverseImage i G)) ⋙
        etaleModuleDirectImage.{u, 0} ℤ_[ℓ] (B.inclusion.map i))

/-- **Relative cohomological purity along an étale divisor of a smooth relative curve**, with the
twist `tw`: the sheaf-level part `(P0)`, `(P2)`, `(BC1)`
(`Stacks.EtaleCohomology.RelativeCurvePuritySheafInput`) and the ℓ-adic tower form of `(P1)`
(`Stacks.EtaleCohomology.RelativeCurvePurityLAdicInput`). -/
def RelativeCurvePurityInput
    (tw : ∀ (X : B.Scheme) [IsNoetherian X.1], LAdicSheaf.{u, u + 1} B X ℓ →
      LAdicSheaf.{u, u + 1} B X ℓ) : Prop :=
  RelativeCurvePuritySheafInput.{u} ∧ RelativeCurvePurityLAdicInput B ℓ tw

/-- **The ℓ-adic Tate twist `F ↦ F(-1)`, as one proposition** about an operation `tw` on ℓ-adic
sheaves: on a Noetherian `X` locally of finite type over a finite field `k` of characteristic
prime to `ℓ`, `tw X F` is lisse for `F` lisse, and its Frobenius traces at a closed point `x` are
`#κ(x) ^ m` times those of `F`. -/
def LAdicTwistInput (tw : ∀ (X : B.Scheme) [IsNoetherian X.1], LAdicSheaf.{u, u + 1} B X ℓ →
    LAdicSheaf.{u, u + 1} B X ℓ) : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (p n : ℕ) [Fact p.Prime] [CharP k p],
    Fintype.card k = p ^ n → ℓ ≠ p → ∀ (X : B.Scheme) [IsNoetherian X.1]
    (fX : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fX] (F : LAdicSheaf.{u, u + 1} B X ℓ),
    F.IsLisse → (tw X F).IsLisse ∧ ∀ (x : closedPoints X.1) (m : ℕ),
      LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ (tw X F) x.1
          (finite_residueField fX x.1 x.2) ^ m) =
        (Nat.card (X.1.residueField x.1) : ℚ_[ℓ]) ^ m *
          LinearMap.trace ℚ_[ℓ] _ (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1
            (finite_residueField fX x.1 x.2) ^ m)

end LAdic

end Stacks.EtaleCohomology

end
