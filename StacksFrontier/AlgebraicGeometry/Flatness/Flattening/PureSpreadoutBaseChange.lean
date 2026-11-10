module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.PureSpreadoutLocalizedFibre

/-!
# The base change of the pure spreadout of Stacks 0AT8

Stacks 0AT8 produces, for every prime `𝔭` of the base ring of the situation of Stacks 0AT6, a
finitely generated ideal `I` of the local ring `A_𝔭` inside its maximal ideal such that the base
change of the situation to `A_𝔭 ⧸ I` carries a pure spreadout. The base-change half of that
conclusion is
`AlgebraicGeometry.FinitelyPresentedLocalizedModuleSituation.localQuotientBaseChange`; this file
treats the pure-spreadout half.

## Main results

* `AlgebraicGeometry.PureSpreadout.nonempty_of_isLocalizedModule_away`: given an element `t` of
  the situation's multiplicative subset, an algebra `C` exhibiting the localization away from `t`,
  a finitely presented `C`-module `M` which is projective over the base and small relative to the
  universe of the situation's module, and a map from a module whose localizations at `t` and at
  the whole multiplicative subset are `M` and the situation's module, there is a pure spreadout.
* `AlgebraicGeometry.FinitelyPresentedLocalizedModuleSituation.exists_fg_ideal_fibre_free`:
  over a local ring of the base, an element `s` of the multiplicative subset such that every
  element of the multiplicative subset acts injectively on the closed fibre of the module localized
  at `s`, and a finitely generated ideal `I` making the base change of that module free.
* `AlgebraicGeometry.FinitelyPresentedLocalizedModuleSituation`'s
  `exists_isLocalizedModule_localQuotientBaseChange`: the module of a local quotient base change
  of the situation is the localization, at the base-changed multiplicative subset, of the base
  change of a module whose localization is the situation's module. Its general form is
  `Stacks.Flatness.exists_isLocalizedModule_tensorProduct`.
* The same namespace's `isPushout_algebraLocalizationBaseChangeAlgebra`
  exhibits the algebra of a local quotient base change as the pushout, over the local ring `A_𝔭`
  of the base, of the quotient map against the base change of the algebra to `A_𝔭`, for the
  algebra structures `algebraLocalizationBase`, `algebraLocalizationAlgebra` and
  `algebraLocalizationBaseChangeAlgebra`.
* `Stacks.Flatness.finitePresentation_tensorProduct` and
  `Stacks.Flatness.small_tensorProduct_of_finitePresentation`: the base change of a finitely
  presented module is finitely presented, and small relative to the universe of a small algebra.

## Implementation notes

`nonempty_of_isLocalizedModule_away` takes **every** ring, module and map as a variable, and the
situation `Y` as well. That is deliberate: the algebra structure of the situation's localization
over `C` has to be *constructed* (from the invertibility of `t`), and a constructed instance on a
concrete tensor product does not match the instance that `TensorProduct`'s own
`isScalarTower_left` builds, so a statement mixing the two does not elaborate. With `Y.Bₛ` and
`Y.N` opaque there are no competing instances and every ascription goes through. The same choice
keeps the elaboration cheap: `Module.FinitePresentation C (C ⊗[Y.B] N)` written out in the
presence of a dozen local instances from a `LocalQuotientBaseChange` is a `whnf` timeout, while
the same fact stated at variables (`Stacks.Flatness.finitePresentation_tensorProduct`) and applied
as a term is free.

In `exists_fg_ideal_fibre_free` the element of the multiplicative subset is a preimage `s'` in the
situation's own multiplicative subset: the image of `s'` in the algebra of any base change of the
situation lies in that base change's multiplicative subset.

## References

* [Stacks Project, Tag 0AT8](https://stacks.math.columbia.edu/tag/0AT8)
* [Stacks Project, Tag 0AT6](https://stacks.math.columbia.edu/tag/0AT6)
-/

@[expose] public section

open TensorProduct

universe u v u₁ u₂ u₃ u₄ u₅ v₁ v₂ v₃ v₄ w w'

/-- The base change of a finitely presented module along a ring map is finitely presented. -/
theorem Stacks.Flatness.finitePresentation_tensorProduct (B : Type u) [CommRing B] (C : Type v)
    [CommRing C] [Algebra B C] (N : Type w) [AddCommGroup N] [Module B N]
    [Module.FinitePresentation B N] : Module.FinitePresentation C (C ⊗[B] N) :=
  FinitePresentation.of_isBaseChange _ (TensorProduct.isBaseChange B N C)

/-- **A localization of modules base changes.** Let `Bs` be a localization of `B` at `S`, let `B'`
be a `B`-algebra and `Bs'` a localization of `B'` at the image of `S`, and let `N'` be the base
change to `Bs'` of a module `N` that is itself the localization at `S` of a `B`-module `N₀`. Then
`N'` is the localization at the image of `S` of the base change `B' ⊗[B] N₀`. -/
theorem Stacks.Flatness.exists_isLocalizedModule_tensorProduct
    {B : Type u} [CommRing B] (S : Submonoid B) (Bs : Type*) [CommRing Bs] [Algebra B Bs]
    [IsLocalization S Bs] (B' : Type*) [CommRing B'] [Algebra B B'] (Bs' : Type*) [CommRing Bs']
    [Algebra B' Bs'] [Algebra B Bs'] [IsScalarTower B B' Bs'] [Algebra Bs Bs']
    [IsScalarTower B Bs Bs'] [IsLocalization (S.map (algebraMap B B')) Bs']
    {N₀ : Type w} [AddCommGroup N₀] [Module B N₀]
    {N : Type*} [AddCommGroup N] [Module B N] [Module Bs N] [IsScalarTower B Bs N]
    (φ : N₀ →ₗ[B] N) [IsLocalizedModule S φ]
    {N' : Type*} [AddCommGroup N'] [Module B N'] [Module B' N'] [Module Bs N'] [Module Bs' N']
    [IsScalarTower B B' N'] [IsScalarTower B Bs N'] [IsScalarTower Bs Bs' N']
    [IsScalarTower B' Bs' N'] [IsScalarTower B Bs' N']
    (θ : N →ₗ[Bs] N') (hθ : IsBaseChange Bs' θ) :
    ∃ ψ : (B' ⊗[B] N₀) →ₗ[B'] N', IsLocalizedModule (S.map (algebraMap B B')) ψ := by
  have hmk : IsBaseChange B' (TensorProduct.mk B B' N₀ 1) := TensorProduct.isBaseChange B N₀ B'
  refine ⟨hmk.lift ((θ.restrictScalars B).comp φ), ?_⟩
  refine (isLocalizedModule_iff_isBaseChange (S.map (algebraMap B B')) Bs' _).mpr (hmk.of_comp ?_)
  rw [hmk.lift_comp]
  exact (IsLocalizedModule.isBaseChange S Bs φ).comp hθ

/-- The base change of a finitely presented module along an algebra small relative to a universe
is itself small relative to that universe. -/
theorem Stacks.Flatness.small_tensorProduct_of_finitePresentation (B : Type u) [CommRing B]
    (C : Type v) [CommRing C] [Algebra B C] [Small.{u₁} C] (N : Type w) [AddCommGroup N]
    [Module B N] [Module.FinitePresentation B N] : Small.{u₁} (C ⊗[B] N) :=
  have := Stacks.Flatness.finitePresentation_tensorProduct B C N
  Stacks.Flatness.small_of_module_finite_of_small C (C ⊗[B] N)

namespace AlgebraicGeometry

namespace PureSpreadout

variable (Y : FinitelyPresentedLocalizedModuleSituation.{v₁, v₂, v₃, v₄})

/-- Every power of an element of the multiplicative subset is a unit in the localization. -/
theorem isUnit_algebraMap_powers {t : Y.B} (ht : t ∈ Y.S) (y : Submonoid.powers t) :
    IsUnit (algebraMap Y.B Y.Bₛ (y : Y.B)) :=
  IsLocalization.map_units Y.Bₛ (⟨(y : Y.B), Submonoid.powers_le.2 ht y.2⟩ : Y.S)

variable {t : Y.B} (C : Type v₂) [CommRing C] [Algebra Y.B C] [IsLocalization.Away t C]

/-- **The affine open of Stacks 0AT8 contains the localized spectrum.** The localization of the
situation is an algebra over the coordinate ring of the open cut out by an element of the
multiplicative subset, because that element is already invertible in the localization. -/
@[instance_reducible]
noncomputable def algebraAwayLocalized (ht : t ∈ Y.S) : Algebra C Y.Bₛ :=
  (IsLocalization.lift (M := Submonoid.powers t) (S := C)
    (isUnit_algebraMap_powers Y ht)).toAlgebra

/-- The factorization of the localization map through the coordinate ring of the affine open is a
tower. -/
theorem isScalarTower_algebraAwayLocalized (ht : t ∈ Y.S) :
    letI := algebraAwayLocalized Y C ht
    IsScalarTower Y.B C Y.Bₛ := by
  let := algebraAwayLocalized Y C ht
  exact IsScalarTower.of_algebraMap_eq'
    (IsLocalization.lift_comp (isUnit_algebraMap_powers Y ht)).symm

variable [Algebra Y.A C] [IsScalarTower Y.A Y.B C]

/-- **A pure spreadout from a localization away from one element.** Let `t` be an element of the
situation's multiplicative subset, let `C` exhibit the localization of the algebra away from `t`,
and let `M` be a finitely presented `C`-module which is projective over the base ring and small
relative to the universe of the situation's module. If `M` is the localization at the powers of
`t` of a module whose localization at the whole multiplicative subset is the situation's module,
and every element of the multiplicative subset acts injectively on the closed fibre of `M`, then
the situation has a pure spreadout, for an arbitrary test-module universe `u₅`. -/
theorem nonempty_of_isLocalizedModule_away [IsLocalRing Y.A] (ht : t ∈ Y.S)
    (M : Type w) [AddCommGroup M] [Module C M] [Module Y.B M] [Module Y.A M]
    [IsScalarTower Y.B C M] [IsScalarTower Y.A C M] [Small.{v₄} M]
    [Module.FinitePresentation C M] [Module.Projective Y.A M]
    (N₀ : Type w') [AddCommGroup N₀] [Module Y.B N₀]
    (φ : N₀ →ₗ[Y.B] Y.N) [IsLocalizedModule Y.S φ]
    (f : N₀ →ₗ[Y.B] M) [IsLocalizedModule (Submonoid.powers t) f]
    (hfib : ∀ u ∈ Y.S, ∀ y : M,
      u • y ∈ IsLocalRing.maximalIdeal Y.A • (⊤ : Submodule Y.A M) →
        y ∈ IsLocalRing.maximalIdeal Y.A • (⊤ : Submodule Y.A M)) :
    Nonempty (PureSpreadout.{v₁, v₂, v₃, v₄, u₅} Y) := by
  let _iaC := algebraAwayLocalized Y C ht
  have _itC := isScalarTower_algebraAwayLocalized Y C ht
  let _imC : Module C Y.N := Module.compHom Y.N (algebraMap C Y.Bₛ)
  have _itCN : IsScalarTower C Y.Bₛ Y.N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have _itBCN : IsScalarTower Y.B C Y.N := by
    refine IsScalarTower.of_algebraMap_smul fun r x => ?_
    change (algebraMap C Y.Bₛ (algebraMap Y.B C r)) • x = _
    rw [← IsScalarTower.algebraMap_apply Y.B C Y.Bₛ]
    rfl
  have _itAC : IsScalarTower Y.A C Y.Bₛ := IsScalarTower.to₁₃₄ Y.A Y.B C Y.Bₛ
  have _itACN : IsScalarTower Y.A C Y.N := by
    refine IsScalarTower.of_algebraMap_smul fun r x => ?_
    change (algebraMap C Y.Bₛ (algebraMap Y.A C r)) • x = _
    rw [← IsScalarTower.algebraMap_apply Y.A C Y.Bₛ]
    rfl
  have hunits : ∀ x : Submonoid.powers t,
      IsUnit ((algebraMap Y.B (Module.End Y.B Y.N)) (x : Y.B)) := fun x =>
    IsLocalizedModule.map_units φ ⟨(x : Y.B), Submonoid.powers_le.2 ht x.2⟩
  let g₀ := IsLocalizedModule.lift (Submonoid.powers t) f φ hunits
  have hg₀ : g₀ ∘ₗ f = φ := IsLocalizedModule.lift_comp (Submonoid.powers t) f φ hunits
  let g := LinearMap.extendScalarsOfIsLocalization (Submonoid.powers t) C g₀
  have hgr : g.restrictScalars Y.B = g₀ :=
    LinearMap.restrictScalars_extendScalarsOfIsLocalization (Submonoid.powers t) C g₀
  have _iloc : IsLocalizedModule Y.S (g.restrictScalars Y.B ∘ₗ f) := by
    rw [hgr, hg₀]
    infer_instance
  have _iloc2 : IsLocalizedModule Y.S (g.restrictScalars Y.B) :=
    IsLocalizedModule.of_comp_of_le (Submonoid.powers_le.2 ht) f (g.restrictScalars Y.B)
  exact nonempty_of_small Y t C M g hfib

end PureSpreadout

namespace FinitelyPresentedLocalizedModuleSituation

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})

/-- **Step 1 of the proof of Stacks 0AT8 for a local quotient base change.** The module of the
base-changed situation is the localization, at the base-changed multiplicative subset, of the base
change of the module step 1 produces. -/
theorem exists_isLocalizedModule_localQuotientBaseChange
    {p : Ideal X.A} [p.IsPrime] {I : Ideal (Localization.AtPrime p)}
    {Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂, max u₁ u₃, max u₁ (max u₃ u₄)}}
    (hbc : LocalQuotientBaseChange X Y p I)
    (N₀ : Type u₂) [AddCommGroup N₀] [Module X.B N₀]
    (φ₀ : N₀ →ₗ[X.B] X.N) [IsLocalizedModule X.S φ₀] :
    letI := hbc.algebraB
    ∃ ψ : (Y.B ⊗[X.B] N₀) →ₗ[Y.B] Y.N,
      IsLocalizedModule (X.S.map (algebraMap X.B Y.B)) ψ := by
  let := hbc.algebraB
  let := hbc.algebraLocalized
  let := hbc.algebraBLocalized
  have := hbc.towerBLocalized
  have := hbc.towerBBaseLocalized
  let := hbc.moduleLocalized
  have := hbc.towerLocalizedModule
  have _loc : IsLocalization (X.S.map (algebraMap X.B Y.B)) Y.Bₛ := by
    rw [← hbc.submonoid_eq_map]
    exact Y.isLocalization
  let _mBN : Module X.B Y.N := Module.compHom Y.N (algebraMap X.B Y.Bₛ)
  have _tBsN : IsScalarTower X.B Y.Bₛ Y.N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have _tBBN : IsScalarTower X.B Y.B Y.N := by
    refine IsScalarTower.of_algebraMap_smul fun r x => ?_
    rw [← IsScalarTower.algebraMap_smul Y.Bₛ (algebraMap X.B Y.B r) x,
      ← IsScalarTower.algebraMap_apply X.B Y.B Y.Bₛ]
    rfl
  have _tBBsN : IsScalarTower X.B X.Bₛ Y.N := by
    refine IsScalarTower.of_algebraMap_smul fun r x => ?_
    rw [← IsScalarTower.algebraMap_smul Y.Bₛ (algebraMap X.B X.Bₛ r) x,
      ← IsScalarTower.algebraMap_apply X.B X.Bₛ Y.Bₛ]
    rfl
  exact Stacks.Flatness.exists_isLocalizedModule_tensorProduct X.S X.Bₛ Y.B Y.Bₛ φ₀
    hbc.moduleMap hbc.moduleBaseChange

section LocalQuotient

variable {p : Ideal X.A} [p.IsPrime] {I : Ideal (Localization.AtPrime p)}
  {Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂, max u₁ u₃, max u₁ (max u₃ u₄)}}
  (hbc : LocalQuotientBaseChange X Y p I)

/-- The local ring of the base at the prime acts on the base ring of a local quotient base change,
through the quotient map and the structure's identification of that base ring. -/
@[instance_reducible]
noncomputable def algebraLocalizationBase : Algebra (Localization.AtPrime p) Y.A :=
  ((hbc.baseEquiv.symm.toRingHom).comp (Ideal.Quotient.mk I)).toAlgebra

/-- The base ring of a local quotient base change is an algebra over the base through the local
ring at the prime. -/
theorem isScalarTower_algebraLocalizationBase :
    letI := hbc.algebraBase
    letI := X.algebraLocalizationBase hbc
    IsScalarTower X.A (Localization.AtPrime p) Y.A := by
  let := hbc.algebraBase
  let := X.algebraLocalizationBase hbc
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  change _ = hbc.baseEquiv.symm (Ideal.Quotient.mk I
    (algebraMap X.A (Localization.AtPrime p) x))
  rw [← hbc.baseEquiv_algebraMap, RingEquiv.symm_apply_apply]

/-- The algebra of a local quotient base change is an algebra over the local ring at the prime. -/
@[instance_reducible]
noncomputable def algebraLocalizationAlgebra : Algebra (Localization.AtPrime p) Y.B :=
  letI := X.algebraLocalizationBase hbc
  ((algebraMap Y.A Y.B).comp (algebraMap (Localization.AtPrime p) Y.A)).toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- **The algebra of a local quotient base change receives the base change to the local ring.**
The map `A_𝔭 ⊗_A B → Y.B` is the one `AlgHom.liftEquiv` produces out of `B → Y.B`. -/
@[instance_reducible]
noncomputable def algebraLocalizationBaseChangeAlgebra :
    Algebra ((Localization.AtPrime p) ⊗[X.A] X.B) Y.B :=
  letI := hbc.algebraBase
  letI := hbc.algebraB
  letI := hbc.algebraAB'
  haveI := hbc.towerAB
  letI := X.algebraLocalizationBase hbc
  letI := X.algebraLocalizationAlgebra hbc
  haveI : IsScalarTower (Localization.AtPrime p) Y.A Y.B := IsScalarTower.of_algebraMap_eq' rfl
  haveI := X.isScalarTower_algebraLocalizationBase hbc
  haveI := hbc.towerBaseB
  haveI : IsScalarTower X.A (Localization.AtPrime p) Y.B :=
    IsScalarTower.to₁₂₄ X.A (Localization.AtPrime p) Y.A Y.B
  ((IsScalarTower.toAlgHom X.A X.B Y.B).liftEquiv X.A (Localization.AtPrime p) X.B
    Y.B).toRingHom.toAlgebra

/-- The scalar towers on the algebra of a local quotient base change: through `Y.A`, through `A_𝔭`
over `X.A`, and through the base change `A_𝔭 ⊗_A B` over `A_𝔭` and over `X.B`. -/
private theorem isScalarTower_algebraLocalizationBaseChangeAlgebra_aux :
    letI := hbc.algebraBase
    letI := hbc.algebraB
    letI := hbc.algebraAB'
    letI := X.algebraLocalizationBase hbc
    letI := X.algebraLocalizationAlgebra hbc
    letI := X.algebraLocalizationBaseChangeAlgebra hbc
    IsScalarTower (Localization.AtPrime p) Y.A Y.B ∧
      IsScalarTower X.A (Localization.AtPrime p) Y.B ∧
      IsScalarTower (Localization.AtPrime p) ((Localization.AtPrime p) ⊗[X.A] X.B) Y.B ∧
      IsScalarTower X.B ((Localization.AtPrime p) ⊗[X.A] X.B) Y.B := by
  let := hbc.algebraBase
  let := hbc.algebraB
  let := hbc.algebraAB'
  have := hbc.towerAB
  have := hbc.towerBaseB
  let := X.algebraLocalizationBase hbc
  have := X.isScalarTower_algebraLocalizationBase hbc
  let := X.algebraLocalizationAlgebra hbc
  have _tAAB : IsScalarTower (Localization.AtPrime p) Y.A Y.B :=
    IsScalarTower.of_algebraMap_eq' rfl
  have _tXAB : IsScalarTower X.A (Localization.AtPrime p) Y.B :=
    IsScalarTower.to₁₂₄ X.A (Localization.AtPrime p) Y.A Y.B
  let := X.algebraLocalizationBaseChangeAlgebra hbc
  refine ⟨_tAAB, _tXAB, ?_, ?_⟩ <;> refine IsScalarTower.of_algebraMap_eq fun x => ?_
  · change _ = ((IsScalarTower.toAlgHom X.A X.B Y.B).liftEquiv X.A (Localization.AtPrime p) X.B
      Y.B) (algebraMap (Localization.AtPrime p) ((Localization.AtPrime p) ⊗[X.A] X.B) x)
    rw [Algebra.TensorProduct.algebraMap_apply, AlgHom.liftEquiv_tmul]
    simp [Algebra.smul_def]
  · change _ = ((IsScalarTower.toAlgHom X.A X.B Y.B).liftEquiv X.A (Localization.AtPrime p) X.B
      Y.B) ((1 : Localization.AtPrime p) ⊗ₜ[X.A] x)
    rw [AlgHom.liftEquiv_tmul, one_smul]
    rfl

/-- **The algebra of a local quotient base change is the pushout along the quotient.** Over the
local ring `A_𝔭` of the base, `Y.B` is `Y.A ⊗_{A_𝔭} (A_𝔭 ⊗_A B)`. -/
theorem isScalarTower_algebraLocalizationBaseChangeAlgebra :
    letI := X.algebraLocalizationBase hbc
    letI := X.algebraLocalizationAlgebra hbc
    letI := X.algebraLocalizationBaseChangeAlgebra hbc
    IsScalarTower (Localization.AtPrime p) ((Localization.AtPrime p) ⊗[X.A] X.B) Y.B :=
  (X.isScalarTower_algebraLocalizationBaseChangeAlgebra_aux hbc).2.2.1

/-- The algebra of a local quotient base change receives the original algebra through the base
change to the local ring at the prime. -/
theorem isScalarTower_algebraLocalizationBaseChangeAlgebra' :
    letI := hbc.algebraB
    letI := X.algebraLocalizationBase hbc
    letI := X.algebraLocalizationAlgebra hbc
    letI := X.algebraLocalizationBaseChangeAlgebra hbc
    IsScalarTower X.B ((Localization.AtPrime p) ⊗[X.A] X.B) Y.B :=
  (X.isScalarTower_algebraLocalizationBaseChangeAlgebra_aux hbc).2.2.2

/-- **The algebra of a local quotient base change is the pushout along the quotient.** -/
theorem isPushout_algebraLocalizationBaseChangeAlgebra :
    letI := hbc.algebraBase
    letI := X.algebraLocalizationBase hbc
    letI := X.algebraLocalizationAlgebra hbc
    letI := X.algebraLocalizationBaseChangeAlgebra hbc
    haveI := X.isScalarTower_algebraLocalizationBaseChangeAlgebra hbc
    haveI : IsScalarTower (Localization.AtPrime p) Y.A Y.B :=
      IsScalarTower.of_algebraMap_eq' rfl
    Algebra.IsPushout (Localization.AtPrime p) Y.A
      ((Localization.AtPrime p) ⊗[X.A] X.B) Y.B := by
  let := hbc.algebraBase
  let := hbc.algebraB
  let := hbc.algebraAB'
  have := hbc.towerAB
  have := hbc.towerBaseB
  let := X.algebraLocalizationBase hbc
  have := X.isScalarTower_algebraLocalizationBase hbc
  let := X.algebraLocalizationAlgebra hbc
  obtain ⟨_tAAB, _tXAB, _tLB, _tBB⟩ :=
    X.isScalarTower_algebraLocalizationBaseChangeAlgebra_aux hbc
  let := X.algebraLocalizationBaseChangeAlgebra hbc
  have _tAAB2 : IsScalarTower X.A ((Localization.AtPrime p) ⊗[X.A] X.B) Y.B :=
    IsScalarTower.to₁₃₄ X.A (Localization.AtPrime p) ((Localization.AtPrime p) ⊗[X.A] X.B) Y.B
  exact (Algebra.IsPushout.comp_iff X.A (Localization.AtPrime p) X.B
    ((Localization.AtPrime p) ⊗[X.A] X.B) (T := Y.A) (T' := Y.B)).mp hbc.algebraPushout

end LocalQuotient

/-- **Steps 2, 3 and 4 of the proof of Stacks 0AT8, over a local ring of the base.** Let `A₁` be a
local `A`-algebra and let `N₀` be a finitely presented `B`-module — the module step 1 produces.
Then there is an element `s'` of the multiplicative subset and a finitely generated ideal `I`
inside the maximal ideal of `A₁` such that, writing `C₁` for the localization of `A₁ ⊗_A B` away
from the image of `s'` and `M₁ = C₁ ⊗_B N₀`:

* every element of the multiplicative subset acts injectively on the closed fibre `M₁ ⧸ 𝔪 M₁`;
* `(A₁ ⧸ I) ⊗_{A₁} M₁` is a free `A₁ ⧸ I`-module. -/
theorem exists_fg_ideal_fibre_free (A₁ : Type u₁) [CommRing A₁] [Algebra X.A A₁] [IsLocalRing A₁]
    (N₀ : Type u₂) [AddCommGroup N₀] [Module X.B N₀] [Module.FinitePresentation X.B N₀] :
    ∃ s' ∈ X.S, ∃ I : Ideal A₁, I.FG ∧ I ≤ IsLocalRing.maximalIdeal A₁ ∧
      (∀ u ∈ X.S,
        ∀ y : Localization.Away (algebraMap X.B (A₁ ⊗[X.A] X.B) s') ⊗[X.B] N₀,
        algebraMap X.B (A₁ ⊗[X.A] X.B) u • y ∈ IsLocalRing.maximalIdeal A₁ • (⊤ : Submodule A₁ _) →
          y ∈ IsLocalRing.maximalIdeal A₁ • (⊤ : Submodule A₁ _)) ∧
      Module.Free (A₁ ⧸ I)
        ((A₁ ⧸ I) ⊗[A₁] (Localization.Away (algebraMap X.B (A₁ ⊗[X.A] X.B) s') ⊗[X.B] N₀)) := by
  have _noeth : IsNoetherianRing ((A₁ ⊗[X.A] X.B) ⧸
      Ideal.map (algebraMap A₁ (A₁ ⊗[X.A] X.B)) (IsLocalRing.maximalIdeal A₁)) :=
    isNoetherianRing_quotient_map_maximalIdeal (A₁ ⊗[X.A] X.B)
  obtain ⟨s, hsS, habs⟩ := exists_mem_smul_mem_smul_top_of_isNoetherianRing_quotient
    (B := A₁ ⊗[X.A] X.B)
    (Ideal.map (algebraMap A₁ (A₁ ⊗[X.A] X.B)) (IsLocalRing.maximalIdeal A₁))
    (X.S.map (algebraMap X.B (A₁ ⊗[X.A] X.B)))
    ((A₁ ⊗[X.A] X.B) ⊗[X.B] N₀)
  obtain ⟨s', hs', rfl⟩ := hsS
  refine ⟨s', hs', ?_⟩
  have habsm : ∀ u ∈ X.S.map (algebraMap X.B (A₁ ⊗[X.A] X.B)),
      ∀ n : (A₁ ⊗[X.A] X.B) ⊗[X.B] N₀,
      u • n ∈ IsLocalRing.maximalIdeal A₁ •
          (⊤ : Submodule A₁ ((A₁ ⊗[X.A] X.B) ⊗[X.B] N₀)) →
        algebraMap X.B (A₁ ⊗[X.A] X.B) s' • n ∈ IsLocalRing.maximalIdeal A₁ •
          (⊤ : Submodule A₁ ((A₁ ⊗[X.A] X.B) ⊗[X.B] N₀)) := by
    intro u hu n hn
    rw [PureSpreadout.mem_maximalIdeal_smul_top_iff (S := A₁ ⊗[X.A] X.B)] at hn ⊢
    exact habs u hu n hn
  have _fpC : Algebra.FinitePresentation A₁
      (Localization.Away (algebraMap X.B (A₁ ⊗[X.A] X.B) s')) :=
    Algebra.FinitePresentation.of_isLocalization_away A₁ (A₁ ⊗[X.A] X.B)
      (algebraMap X.B (A₁ ⊗[X.A] X.B) s')
      (Localization.Away (algebraMap X.B (A₁ ⊗[X.A] X.B) s'))
  have _fpM := Stacks.Flatness.finitePresentation_tensorProduct X.B
    (Localization.Away (algebraMap X.B (A₁ ⊗[X.A] X.B) s')) N₀
  obtain ⟨I, hIfg, hIle, hfree⟩ :=
    Stacks.Flatness.exists_fg_ideal_le_maximalIdeal_free_tensorProduct_of_universe
      (A := A₁) (Localization.Away (algebraMap X.B (A₁ ⊗[X.A] X.B) s'))
      (Localization.Away (algebraMap X.B (A₁ ⊗[X.A] X.B) s') ⊗[X.B] N₀)
  refine ⟨I, hIfg, hIle, fun u hu y hy => ?_, hfree⟩
  exact PureSpreadout.fibre_smul_maximalIdeal_mem_of_absorbing
    (A := A₁) (B := A₁ ⊗[X.A] X.B) (X.S.map (algebraMap X.B (A₁ ⊗[X.A] X.B)))
    (N₀ := (A₁ ⊗[X.A] X.B) ⊗[X.B] N₀)
    (M₁ := Localization.Away (algebraMap X.B (A₁ ⊗[X.A] X.B) s') ⊗[X.B] N₀)
    (Submonoid.mem_map_of_mem _ hs') habsm
    (TensorProduct.AlgebraTensorModule.rTensor X.B N₀
      (Algebra.linearMap (A₁ ⊗[X.A] X.B)
        (Localization.Away (algebraMap X.B (A₁ ⊗[X.A] X.B) s'))))
    (Submonoid.mem_map_of_mem _ hu) y hy

end FinitelyPresentedLocalizedModuleSituation

end AlgebraicGeometry

end
