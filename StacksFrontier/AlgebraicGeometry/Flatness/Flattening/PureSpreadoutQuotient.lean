module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.PureSpreadoutBaseChange

/-!
# The pure spreadout after base change to a local quotient: Stacks 0AT8

Stacks 0AT8 asserts that the situation of Stacks 0AT6 acquires a pure spreadout after base change
to a suitable finitely generated quotient of each local ring of the base ring. The base-change half
of the conclusion is
`AlgebraicGeometry.FinitelyPresentedLocalizedModuleSituation.localQuotientBaseChange`, steps 1 to 4
of the proof are the same namespace's `exists_fg_ideal_fibre_free`, and the final assembly is
`AlgebraicGeometry.PureSpreadout.nonempty_of_isLocalizedModule_away`. This file supplies step 5 —
the transport of the spreadout data along the quotient map — and concludes Stacks 0AT8 and, with
it, Stacks 0AT9.

## Main results

* `AlgebraicGeometry.FinitelyPresentedLocalizedModuleSituation`'s
  `exists_fg_ideal_localQuotientBaseChange_pureSpreadout` is **Stacks 0AT8**. The test-module
  universe of the universal injectivity packaged in the pure spreadout is left **free**, so the
  statement instantiates at any test universe.
* `AlgebraicGeometry.universallyInjective_of_rTensor_residueField_injective` is **Stacks 0AT9**:
  the `hAT8` hypothesis of
  `AlgebraicGeometry.universallyInjective_of_rTensor_residueField_injective_of_pureSpreadout` is
  discharged by instantiating 0AT8 at the test universe that binder pins.
* `AlgebraicGeometry.universallyInjective_of_flat_of_fibres` is the same statement for an
  unbundled finitely presented localized module whose source and target live in independent
  universes.
* The same namespace's `nonempty_pureSpreadout_baseChange_quotient` is step 5 itself: from the
  element `s'` of the multiplicative subset, the finitely generated ideal `I` inside the maximal
  ideal, the closed-fibre condition over the local ring and the freeness of the base change that
  steps 2 to 4 provide, together with the localization datum of step 1 over the base-changed
  situation, it builds the pure spreadout of `X.baseChange (A₁ ⧸ I)`.
* `Stacks.Flatness.isPushout_baseChangeTower`, `Stacks.Flatness.isPushout_comp_of_isPushout` and
  `Stacks.Flatness.isLocalization_away_tensorProduct` are the three general facts about base change
  that step 5 rests on: `R ⊗[A] B` is the base change to `R` of `A₁ ⊗[A] B` over `A₁`, a
  localization base change composed with an iterated base change is again a base change, and an
  away localization base changes.
* `Stacks.Flatness.projective_of_free_tensorProduct` and
  `Stacks.Flatness.fibre_smul_mem_of_quotient` are the two obligations of
  `AlgebraicGeometry.PureSpreadout.nonempty_of_isLocalizedModule_away` that step 5 has to
  discharge: the projectivity of the spreadout module over the quotient, and the closed-fibre
  condition there.

## Implementation notes

The coordinate ring of the affine open is taken to be `C = ((A₁ ⧸ I) ⊗[A] B) ⊗[A₁ ⊗[A] B] C₁`, the
base change along the quotient map of the away localization `C₁` that step 4 works with. That
choice makes two of the three structural facts free — `Algebra ((A₁ ⧸ I) ⊗[A] B) C` is the tensor
product's own left algebra, and `IsLocalization.Away` of the image of `s'` is
`IsLocalization.tensor` after rewriting `Submonoid.map` of a monoid of powers into the powers of
the image — while the third, the pushout square `Algebra.IsPushout A₁ (A₁ ⧸ I) C₁ C` that
identifies `C` with `(A₁ ⧸ I) ⊗[A₁] C₁`, is `Algebra.IsPushout.comp_iff` applied twice.

Every `Algebra` structure on `C` that step 5 needs is **found by instance search**: with
`Algebra A₁ ((A₁ ⧸ I) ⊗[A] B)` available, `Algebra.TensorProduct.leftAlgebra` supplies
`Algebra A₁ C` as well. Building them by hand instead — as `RingHom.toAlgebra` of a composite
through `(A₁ ⧸ I) ⊗[A] B` — produces structures whose `toSMul` is *not* the `SMul` that search
finds on a tensor product, and every subsequent `IsScalarTower` goal then fails to elaborate. Only
`IsScalarTower A₁ ((A₁ ⧸ I) ⊗[A] B) C` has to be proved, and it is proved on tensors rather than
through `algebraMap`s, for the same reason.

The transport to the base-changed situation `Y = X.baseChange (A₁ ⧸ I)` is split off into
`nonempty_pureSpreadout_baseChange_quotient_aux`, whose coordinate ring `C` is a **variable**. Two
things force the split. Instance search does not see through `baseChange`, so each structure on `C`
has to be re-introduced at the `(X.baseChange (A₁ ⧸ I)).B` spelling by `letI`; written out at the
concrete `C` those `letI`s exhaust the elaboration budget, while at a variable `C` they are cheap.
And `Algebra X.B (X.baseChange A').B` must be a *named* local instance
(`algebraBaseChangeAlgebra`) rather than a `letI` in the statement: a term-level `letI` inlines its
value, so the instance appearing in the statement of the localization datum would not be the one a
`letI` in the proof introduces, and `Module (X.baseChange A').B ((X.baseChange A').B ⊗[X.B] N₀)`
would not be found.

The closed-fibre condition is carried from `C₁` to `C` by
`AlgebraicGeometry.fibre_smul_mem_of_surjective` along the base-change map
`C₁ ⊗[B] N₀ → C ⊗[B] N₀`, whose surjectivity and kernel are computed by identifying it, through
`quotientSpreadoutEquiv`, with the quotient map `M₁ → M₁ ⧸ I M₁` that
`TensorProduct.quotTensorEquivQuotSMul` provides; `I ≤ 𝔪` is what makes that kernel small enough.
The monoid acting is the multiplicative subset `X.S` itself, taken as a type, since the hypothesis
is only available for its elements.

## References

* [Stacks Project, Tag 0AT6](https://stacks.math.columbia.edu/tag/0AT6)
* [Stacks Project, Tag 0AT8](https://stacks.math.columbia.edu/tag/0AT8)
* [Stacks Project, Tag 0AT9](https://stacks.math.columbia.edu/tag/0AT9)
-/

@[expose] public section

open TensorProduct

universe u v w w' u₁ u₂ u₃ u₄ u₅ u₆

namespace Stacks.Flatness

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Away

/-- **An away localization base changes.** If `C₁` is the localization of `B₁` away from `x` and
`B₂` is any `B₁`-algebra, then `B₂ ⊗[B₁] C₁` is the localization of `B₂` away from the image
of `x`. -/
theorem isLocalization_away_tensorProduct {B₁ : Type u} [CommRing B₁] (x : B₁)
    (C₁ : Type v) [CommRing C₁] [Algebra B₁ C₁] [IsLocalization.Away x C₁]
    (B₂ : Type w) [CommRing B₂] [Algebra B₁ B₂] :
    IsLocalization.Away (algebraMap B₁ B₂ x) (B₂ ⊗[B₁] C₁) := by
  have h : Algebra.algebraMapSubmonoid B₂ (Submonoid.powers x) =
      Submonoid.powers (algebraMap B₁ B₂ x) := Submonoid.map_powers _ _
  have := IsLocalization.tensor (R := B₁) (S := B₂) C₁ (Submonoid.powers x)
  rwa [h] at this

end Away

section Tower

variable (A : Type u) [CommRing A] (A₁ : Type v) [CommRing A₁] [Algebra A A₁]
  (R : Type w) [CommRing R] [Algebra A₁ R] [Algebra A R] [IsScalarTower A A₁ R]
  (B : Type w') [CommRing B] [Algebra A B]

/-- The map `A₁ ⊗[A] B → R ⊗[A] B` induced by an `A₁`-algebra `R`. -/
noncomputable def baseChangeTowerAlgHom : (A₁ ⊗[A] B) →ₐ[A] (R ⊗[A] B) :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A₁ R) (AlgHom.id A B)

/-- `R ⊗[A] B` is an algebra over `A₁ ⊗[A] B`. -/
@[instance_reducible]
noncomputable def algebraBaseChangeTower : Algebra (A₁ ⊗[A] B) (R ⊗[A] B) :=
  (baseChangeTowerAlgHom A A₁ R B).toRingHom.toAlgebra

attribute [local instance] algebraBaseChangeTower

/-- `A₁` reaches `R ⊗[A] B` through `A₁ ⊗[A] B`. -/
theorem isScalarTower_baseChangeTower_left : IsScalarTower A₁ (A₁ ⊗[A] B) (R ⊗[A] B) := by
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  change _ = baseChangeTowerAlgHom A A₁ R B (algebraMap A₁ (A₁ ⊗[A] B) x)
  rw [Algebra.TensorProduct.algebraMap_apply]
  change _ = (algebraMap A₁ R x) ⊗ₜ[A] (1 : B)
  rw [← Algebra.TensorProduct.algebraMap_apply]

/-- `B` reaches `R ⊗[A] B` through `A₁ ⊗[A] B`. -/
theorem isScalarTower_baseChangeTower_right : IsScalarTower B (A₁ ⊗[A] B) (R ⊗[A] B) := by
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  change _ = baseChangeTowerAlgHom A A₁ R B ((1 : A₁) ⊗ₜ[A] x)
  simp [baseChangeTowerAlgHom, RingHom.algebraMap_toAlgebra]

attribute [local instance] isScalarTower_baseChangeTower_left isScalarTower_baseChangeTower_right

/-- `A` reaches `R ⊗[A] B` through `A₁ ⊗[A] B`. -/
theorem isScalarTower_baseChangeTower_base : IsScalarTower A (A₁ ⊗[A] B) (R ⊗[A] B) :=
  IsScalarTower.to₁₃₄ A A₁ (A₁ ⊗[A] B) (R ⊗[A] B)

attribute [local instance] isScalarTower_baseChangeTower_base

/-- **Iterated base change.** `R ⊗[A] B` is the base change to `R` of `A₁ ⊗[A] B` over `A₁`. -/
theorem isPushout_baseChangeTower : Algebra.IsPushout A₁ R (A₁ ⊗[A] B) (R ⊗[A] B) :=
  (Algebra.IsPushout.comp_iff A A₁ B (A₁ ⊗[A] B) (T := R) (T' := R ⊗[A] B)).mp inferInstance

end Tower

section Compose

variable (A₁ : Type*) [CommRing A₁] (R : Type*) [CommRing R] [Algebra A₁ R]
  (B₁ : Type*) [CommRing B₁] [Algebra A₁ B₁]
  (B₂ : Type*) [CommRing B₂] [Algebra B₁ B₂] [Algebra A₁ B₂] [Algebra R B₂]
  [IsScalarTower A₁ B₁ B₂] [IsScalarTower A₁ R B₂]
  (C₁ : Type*) [CommRing C₁] [Algebra B₁ C₁] [Algebra A₁ C₁] [IsScalarTower A₁ B₁ C₁]
  (C : Type*) [CommRing C] [Algebra B₂ C] [Algebra C₁ C] [Algebra B₁ C] [Algebra A₁ C]
  [Algebra R C] [IsScalarTower A₁ C₁ C] [IsScalarTower B₁ C₁ C] [IsScalarTower B₁ B₂ C]
  [IsScalarTower A₁ R C] [IsScalarTower A₁ B₂ C] [IsScalarTower R B₂ C]

/-- A localization base change composed with an iterated base change is again a base change: if
`B₂ = R ⊗[A₁] B₁` and `C = B₂ ⊗[B₁] C₁`, then `C = R ⊗[A₁] C₁`. -/
theorem isPushout_comp_of_isPushout [Algebra.IsPushout A₁ R B₁ B₂]
    [Algebra.IsPushout B₁ B₂ C₁ C] : Algebra.IsPushout A₁ R C₁ C := by
  have hb : Algebra.IsPushout A₁ B₁ R B₂ := (Algebra.IsPushout.comm _ _ _ _).mp inferInstance
  have h : Algebra.IsPushout B₁ C₁ B₂ C := (Algebra.IsPushout.comm _ _ _ _).mp inferInstance
  have := (Algebra.IsPushout.comp_iff A₁ B₁ R B₂ (T := C₁) (T' := C)).mpr h
  exact (Algebra.IsPushout.comm _ _ _ _).mpr this

end Compose

section Quotient

variable (A₁ : Type*) [CommRing A₁] (I : Ideal A₁)
  (D : Type*) [CommRing D]
  (C₁ : Type*) [CommRing C₁] [Algebra A₁ C₁] [Algebra D C₁]
  (C : Type*) [CommRing C] [Algebra C₁ C] [Algebra A₁ C] [Algebra D C]
  [Algebra (A₁ ⧸ I) C] [IsScalarTower A₁ C₁ C] [IsScalarTower D C₁ C]
  [IsScalarTower A₁ (A₁ ⧸ I) C] [Algebra.IsPushout A₁ (A₁ ⧸ I) C₁ C]
  (N₀ : Type*) [AddCommGroup N₀] [Module D N₀]

/-- The spreadout module over the quotient `A₁ ⧸ I`, identified with the base change along
`A₁ → A₁ ⧸ I` of the spreadout module over `A₁`. -/
noncomputable def quotientSpreadoutEquiv :
    ((A₁ ⧸ I) ⊗[A₁] (C₁ ⊗[D] N₀)) ≃ₗ[A₁] (C ⊗[D] N₀) :=
  ((Algebra.IsPushout.cancelBaseChange A₁ (A₁ ⧸ I) C₁ C (C₁ ⊗[D] N₀)).symm.restrictScalars
    A₁).trans ((AlgebraTensorModule.cancelBaseChange D C₁ C C N₀).restrictScalars A₁)

/-- The identification of the spreadout module over the quotient carries `1 ⊗ m` to the image of
`m` under the base-change map. -/
theorem quotientSpreadoutEquiv_one_tmul (m : C₁ ⊗[D] N₀) :
    quotientSpreadoutEquiv A₁ I D C₁ C N₀ (1 ⊗ₜ[A₁] m) =
      AlgebraTensorModule.rTensor D N₀ (Algebra.linearMap C₁ C) m := by
  have h1 : (Algebra.IsPushout.cancelBaseChange A₁ (A₁ ⧸ I) C₁ C (C₁ ⊗[D] N₀)).symm
      (1 ⊗ₜ[A₁] m) = (1 : C) ⊗ₜ[C₁] m :=
    (LinearEquiv.symm_apply_eq _).mpr
      (Algebra.IsPushout.cancelBaseChange_tmul A₁ (A₁ ⧸ I) C₁ C (C₁ ⊗[D] N₀) m).symm
  have h2 : ∀ z : C₁ ⊗[D] N₀, (AlgebraTensorModule.cancelBaseChange D C₁ C C N₀)
      ((1 : C) ⊗ₜ[C₁] z) = AlgebraTensorModule.rTensor D N₀ (Algebra.linearMap C₁ C) z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul c n => simp [Algebra.smul_def]
  change (AlgebraTensorModule.cancelBaseChange D C₁ C C N₀)
    ((Algebra.IsPushout.cancelBaseChange A₁ (A₁ ⧸ I) C₁ C (C₁ ⊗[D] N₀)).symm (1 ⊗ₜ[A₁] m)) = _
  rw [h1, h2]

/-- **The base-change map of spreadout modules is the quotient by `I`**: it is surjective, and its
kernel is `I • ⊤`. -/
theorem surjective_rTensor_algebraMap :
    Function.Surjective
      (AlgebraTensorModule.rTensor D N₀ (Algebra.linearMap C₁ C) : _ → C ⊗[D] N₀) ∧
    LinearMap.ker ((AlgebraTensorModule.rTensor D N₀
        (Algebra.linearMap C₁ C)).restrictScalars A₁) = I • (⊤ : Submodule A₁ (C₁ ⊗[D] N₀)) := by
  set e := quotientSpreadoutEquiv A₁ I D C₁ C N₀ with he
  set k := TensorProduct.quotTensorEquivQuotSMul (R := A₁) (C₁ ⊗[D] N₀) I with hk
  constructor
  · intro z
    obtain ⟨m, hm⟩ := (I • (⊤ : Submodule A₁ (C₁ ⊗[D] N₀))).mkQ_surjective (k (e.symm z))
    refine ⟨m, ?_⟩
    rw [← quotientSpreadoutEquiv_one_tmul A₁ I D C₁ C N₀ m, ← he, ← e.eq_symm_apply]
    refine k.injective ?_
    rw [TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
    exact hm
  · ext m
    rw [LinearMap.mem_ker]
    change (AlgebraTensorModule.rTensor D N₀ (Algebra.linearMap C₁ C)) m = 0 ↔ _
    rw [← quotientSpreadoutEquiv_one_tmul A₁ I D C₁ C N₀ m, ← he, e.map_eq_zero_iff,
      ← (Submodule.Quotient.mk_eq_zero (I • (⊤ : Submodule A₁ (C₁ ⊗[D] N₀)))),
      ← TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul (R := A₁) I m, ← hk,
      k.map_eq_zero_iff]

/-- **The closed-fibre condition descends to the quotient.** If every element of a multiplicative
subset of `D` acts injectively on the closed fibre of `C₁ ⊗[D] N₀` over the local ring `A₁`, and
`C` is the base change of `C₁` along `A₁ → A₁ ⧸ I` for an ideal `I` inside the maximal ideal, then
the same holds for `C ⊗[D] N₀`. -/
theorem fibre_smul_mem_of_quotient [IsLocalRing A₁] (hI : I ≤ IsLocalRing.maximalIdeal A₁)
    (S : Submonoid D)
    (h : ∀ u ∈ S, ∀ y : C₁ ⊗[D] N₀,
      u • y ∈ IsLocalRing.maximalIdeal A₁ • (⊤ : Submodule A₁ (C₁ ⊗[D] N₀)) →
        y ∈ IsLocalRing.maximalIdeal A₁ • (⊤ : Submodule A₁ (C₁ ⊗[D] N₀))) :
    ∀ u ∈ S, ∀ y : C ⊗[D] N₀,
      u • y ∈ IsLocalRing.maximalIdeal A₁ • (⊤ : Submodule A₁ (C ⊗[D] N₀)) →
        y ∈ IsLocalRing.maximalIdeal A₁ • (⊤ : Submodule A₁ (C ⊗[D] N₀)) := by
  obtain ⟨hsurj, hker⟩ := surjective_rTensor_algebraMap A₁ I D C₁ C N₀
  intro u hu y hy
  refine AlgebraicGeometry.fibre_smul_mem_of_surjective (IsLocalRing.maximalIdeal A₁)
    ((AlgebraTensorModule.rTensor D N₀ (Algebra.linearMap C₁ C)).restrictScalars A₁)
    hsurj ?_ (T := S) ?_ ?_ ⟨u, hu⟩ y ?_
  · rw [hker]
    exact Submodule.smul_mono_left hI
  · intro s x
    rw [Submonoid.smul_def, Submonoid.smul_def]
    exact ((AlgebraTensorModule.rTensor D N₀
      (Algebra.linearMap C₁ C)).restrictScalars D).map_smul (s : D) x
  · intro s x hx
    exact h (s : D) s.2 x (by rwa [← Submonoid.smul_def])
  · rwa [Submonoid.smul_def]

/-- **Projectivity of the spreadout module over the quotient**, transported from the freeness of
the base change over the local ring. -/
theorem projective_of_free_tensorProduct
    (hfree : Module.Free (A₁ ⧸ I) ((A₁ ⧸ I) ⊗[A₁] (C₁ ⊗[D] N₀))) :
    Module.Projective (A₁ ⧸ I) (C ⊗[D] N₀) :=
  have := hfree
  Module.Projective.of_equiv
    (((Algebra.IsPushout.cancelBaseChange A₁ (A₁ ⧸ I) C₁ C (C₁ ⊗[D] N₀)).symm).trans
      ((AlgebraTensorModule.cancelBaseChange D C₁ C C N₀).restrictScalars (A₁ ⧸ I)))

end Quotient

end Stacks.Flatness

namespace AlgebraicGeometry

namespace FinitelyPresentedLocalizedModuleSituation

open Stacks.Flatness

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})

/-- The algebra of a base-changed situation is an algebra over the original one. This is
`Algebra.TensorProduct.rightAlgebra`, named at the `X.baseChange A'` spelling because instance
search does not see through `baseChange`. -/
@[instance_reducible]
noncomputable def algebraBaseChangeAlgebra (A' : Type u₁) [CommRing A'] [Algebra X.A A'] :
    Algebra X.B (X.baseChange A').B :=
  inferInstanceAs (Algebra X.B (A' ⊗[X.A] X.B))

attribute [local instance] algebraBaseChangeAlgebra

noncomputable section

/-- **The transport of step 5 of the proof of Stacks 0AT8 to the base-changed situation.** Given
the coordinate ring `C` of the affine open, the projectivity of the spreadout module `C ⊗[B] N₀`
over the quotient, the closed-fibre condition for it, and the localization datum of step 1 over the
base-changed situation, the base-changed situation has a pure spreadout.

Every structure on `C` is restated at the `(X.baseChange (A₁ ⧸ I)).B` spelling, because instance
search does not see through `baseChange`; `C` is kept a variable so that doing so stays cheap. -/
theorem nonempty_pureSpreadout_baseChange_quotient_aux
    (A₁ : Type u₁) [CommRing A₁] [Algebra X.A A₁] [IsLocalRing A₁] (I : Ideal A₁)
    [IsLocalRing (A₁ ⧸ I)]
    (N₀ : Type u₂) [AddCommGroup N₀] [Module X.B N₀]
    {s' : X.B} (hs' : s' ∈ X.S)
    (C : Type (max u₁ u₂)) [CommRing C] [Algebra ((A₁ ⧸ I) ⊗[X.A] X.B) C]
    [Algebra (A₁ ⧸ I) C] [Algebra A₁ C] [Algebra X.B C]
    [IsScalarTower (A₁ ⧸ I) ((A₁ ⧸ I) ⊗[X.A] X.B) C]
    [IsScalarTower X.B ((A₁ ⧸ I) ⊗[X.A] X.B) C] [IsScalarTower A₁ (A₁ ⧸ I) C]
    [IsLocalization.Away (algebraMap X.B ((A₁ ⧸ I) ⊗[X.A] X.B) s') C]
    [Small.{max u₁ (max u₃ u₄)} (C ⊗[X.B] N₀)] [Module.FinitePresentation C (C ⊗[X.B] N₀)]
    (hproj : Module.Projective (A₁ ⧸ I) (C ⊗[X.B] N₀))
    (hfib : ∀ u ∈ X.S, ∀ y : C ⊗[X.B] N₀,
      u • y ∈ IsLocalRing.maximalIdeal A₁ • (⊤ : Submodule A₁ (C ⊗[X.B] N₀)) →
        y ∈ IsLocalRing.maximalIdeal A₁ • (⊤ : Submodule A₁ (C ⊗[X.B] N₀)))
    (ψ : ((X.baseChange (A₁ ⧸ I)).B ⊗[X.B] N₀) →ₗ[(X.baseChange (A₁ ⧸ I)).B]
      (X.baseChange (A₁ ⧸ I)).N)
    (hψ : IsLocalizedModule (X.baseChange (A₁ ⧸ I)).S ψ) :
    Nonempty (PureSpreadout.{u₁, max u₁ u₂, max u₁ u₃, max u₁ (max u₃ u₄), u₅}
      (X.baseChange (A₁ ⧸ I))) := by
  let _jB : Algebra (X.baseChange (A₁ ⧸ I)).B C :=
    inferInstanceAs (Algebra ((A₁ ⧸ I) ⊗[X.A] X.B) C)
  let _jA : Algebra (X.baseChange (A₁ ⧸ I)).A C := inferInstanceAs (Algebra (A₁ ⧸ I) C)
  have _jtAB : IsScalarTower (X.baseChange (A₁ ⧸ I)).A (X.baseChange (A₁ ⧸ I)).B C :=
    inferInstanceAs (IsScalarTower (A₁ ⧸ I) ((A₁ ⧸ I) ⊗[X.A] X.B) C)
  have _jXBC : IsScalarTower X.B (X.baseChange (A₁ ⧸ I)).B C :=
    inferInstanceAs (IsScalarTower X.B ((A₁ ⧸ I) ⊗[X.A] X.B) C)
  have _jLR : IsLocalRing (X.baseChange (A₁ ⧸ I)).A := inferInstanceAs (IsLocalRing (A₁ ⧸ I))
  have _jloc : IsLocalization.Away (algebraMap X.B (X.baseChange (A₁ ⧸ I)).B s') C :=
    inferInstanceAs (IsLocalization.Away (algebraMap X.B ((A₁ ⧸ I) ⊗[X.A] X.B) s') C)
  let _jMB : Module (X.baseChange (A₁ ⧸ I)).B (C ⊗[X.B] N₀) :=
    inferInstanceAs (Module ((A₁ ⧸ I) ⊗[X.A] X.B) (C ⊗[X.B] N₀))
  let _jMA : Module (X.baseChange (A₁ ⧸ I)).A (C ⊗[X.B] N₀) :=
    inferInstanceAs (Module (A₁ ⧸ I) (C ⊗[X.B] N₀))
  have _jtBCM : IsScalarTower (X.baseChange (A₁ ⧸ I)).B C (C ⊗[X.B] N₀) :=
    inferInstanceAs (IsScalarTower ((A₁ ⧸ I) ⊗[X.A] X.B) C (C ⊗[X.B] N₀))
  have _jtACM : IsScalarTower (X.baseChange (A₁ ⧸ I)).A C (C ⊗[X.B] N₀) :=
    inferInstanceAs (IsScalarTower (A₁ ⧸ I) C (C ⊗[X.B] N₀))
  have _jXBM : IsScalarTower X.B (X.baseChange (A₁ ⧸ I)).B (C ⊗[X.B] N₀) :=
    inferInstanceAs (IsScalarTower X.B ((A₁ ⧸ I) ⊗[X.A] X.B) (C ⊗[X.B] N₀))
  have _jproj : Module.Projective (X.baseChange (A₁ ⧸ I)).A (C ⊗[X.B] N₀) := hproj
  have _tARM : IsScalarTower A₁ (A₁ ⧸ I) (C ⊗[X.B] N₀) :=
    IsScalarTower.of_tower_algebra A₁ (A₁ ⧸ I) C (C ⊗[X.B] N₀)
  have _jf : IsLocalizedModule
      (Submonoid.powers (algebraMap X.B (X.baseChange (A₁ ⧸ I)).B s'))
      (AlgebraTensorModule.rTensor X.B N₀ (Algebra.linearMap (X.baseChange (A₁ ⧸ I)).B C)) :=
    have : IsLocalizedModule
        (Submonoid.powers (algebraMap X.B (X.baseChange (A₁ ⧸ I)).B s'))
        (Algebra.linearMap (X.baseChange (A₁ ⧸ I)).B C) :=
      (isLocalizedModule_iff_isLocalization' _ _).mpr _jloc
    IsLocalizedModule.rTensor (R := X.B) (X.baseChange (A₁ ⧸ I)).B
      (Submonoid.powers (algebraMap X.B (X.baseChange (A₁ ⧸ I)).B s')) (N := N₀)
      (Algebra.linearMap (X.baseChange (A₁ ⧸ I)).B C)
  have := hψ
  have ht : algebraMap X.B (X.baseChange (A₁ ⧸ I)).B s' ∈ (X.baseChange (A₁ ⧸ I)).S :=
    Submonoid.mem_map_of_mem (algebraMap X.B ((A₁ ⧸ I) ⊗[X.A] X.B)) hs'
  refine PureSpreadout.nonempty_of_isLocalizedModule_away (X.baseChange (A₁ ⧸ I)) C ht
    (C ⊗[X.B] N₀) ((X.baseChange (A₁ ⧸ I)).B ⊗[X.B] N₀) ψ
    (AlgebraTensorModule.rTensor X.B N₀ (Algebra.linearMap (X.baseChange (A₁ ⧸ I)).B C)) ?_
  intro u hu y hy
  have hu2 : u ∈ X.S.map (algebraMap X.B ((A₁ ⧸ I) ⊗[X.A] X.B)) := hu
  obtain ⟨u', hu', rfl⟩ := hu2
  have hy' : algebraMap X.B ((A₁ ⧸ I) ⊗[X.A] X.B) u' • y ∈
      IsLocalRing.maximalIdeal (A₁ ⧸ I) • (⊤ : Submodule (A₁ ⧸ I) (C ⊗[X.B] N₀)) := hy
  change y ∈ IsLocalRing.maximalIdeal (A₁ ⧸ I) • (⊤ : Submodule (A₁ ⧸ I) (C ⊗[X.B] N₀))
  refine (PureSpreadout.mem_maximalIdeal_smul_top_quotient_iff I y).mpr (hfib u' hu' y ?_)
  rw [← IsScalarTower.algebraMap_smul ((A₁ ⧸ I) ⊗[X.A] X.B) u' y]
  exact (PureSpreadout.mem_maximalIdeal_smul_top_quotient_iff I _).mp hy'

/-- **Step 5 of the proof of Stacks 0AT8.** Let `A₁` be a local `A`-algebra, `I` a finitely
generated ideal inside its maximal ideal, `N₀` the finitely presented `B`-module of step 1, `s'`
the element of the multiplicative subset of step 2 and `C₁` the localization of `A₁ ⊗_A B` away
from its image. If every element of the multiplicative subset acts injectively on the closed fibre
of `C₁ ⊗_B N₀` and the base change of that module to `A₁ ⧸ I` is free, then the base change of the
situation to `A₁ ⧸ I` has a pure spreadout.

The coordinate ring of the affine open is the base change `((A₁ ⧸ I) ⊗_A B) ⊗_{A₁ ⊗_A B} C₁` of
`C₁` along the quotient map; `Stacks.Flatness.isPushout_comp_of_isPushout` identifies it with
`(A₁ ⧸ I) ⊗_{A₁} C₁`, which is what carries step 4's freeness and step 3's closed-fibre condition
across. -/
theorem nonempty_pureSpreadout_baseChange_quotient
    (A₁ : Type u₁) [CommRing A₁] [Algebra X.A A₁] [IsLocalRing A₁] (I : Ideal A₁)
    (hIle : I ≤ IsLocalRing.maximalIdeal A₁) [IsLocalRing (A₁ ⧸ I)]
    (N₀ : Type u₂) [AddCommGroup N₀] [Module X.B N₀] [Module.FinitePresentation X.B N₀]
    {s' : X.B} (hs' : s' ∈ X.S)
    (C₁ : Type (max u₁ u₂)) [CommRing C₁] [Algebra (A₁ ⊗[X.A] X.B) C₁]
    [Algebra A₁ C₁] [Algebra X.B C₁]
    [IsScalarTower A₁ (A₁ ⊗[X.A] X.B) C₁] [IsScalarTower X.B (A₁ ⊗[X.A] X.B) C₁]
    [IsLocalization.Away (algebraMap X.B (A₁ ⊗[X.A] X.B) s') C₁]
    (hfib₁ : ∀ u ∈ X.S, ∀ y : C₁ ⊗[X.B] N₀,
      algebraMap X.B (A₁ ⊗[X.A] X.B) u • y ∈
          IsLocalRing.maximalIdeal A₁ • (⊤ : Submodule A₁ (C₁ ⊗[X.B] N₀)) →
        y ∈ IsLocalRing.maximalIdeal A₁ • (⊤ : Submodule A₁ (C₁ ⊗[X.B] N₀)))
    (hfree : Module.Free (A₁ ⧸ I) ((A₁ ⧸ I) ⊗[A₁] (C₁ ⊗[X.B] N₀)))
    (ψ : ((X.baseChange (A₁ ⧸ I)).B ⊗[X.B] N₀) →ₗ[(X.baseChange (A₁ ⧸ I)).B]
      (X.baseChange (A₁ ⧸ I)).N)
    (hψ : IsLocalizedModule (X.baseChange (A₁ ⧸ I)).S ψ) :
    Nonempty (PureSpreadout.{u₁, max u₁ u₂, max u₁ u₃, max u₁ (max u₃ u₄), u₅}
      (X.baseChange (A₁ ⧸ I))) := by
  -- the algebra `A₁ ⊗[X.A] X.B → (A₁ ⧸ I) ⊗[X.A] X.B` and its pushout square
  let _iB : Algebra (A₁ ⊗[X.A] X.B) ((A₁ ⧸ I) ⊗[X.A] X.B) :=
    algebraBaseChangeTower X.A A₁ (A₁ ⧸ I) X.B
  have _tB1 := isScalarTower_baseChangeTower_left X.A A₁ (A₁ ⧸ I) X.B
  have _tB2 := isScalarTower_baseChangeTower_right X.A A₁ (A₁ ⧸ I) X.B
  have _tB3 := isScalarTower_baseChangeTower_base X.A A₁ (A₁ ⧸ I) X.B
  have _pB := isPushout_baseChangeTower X.A A₁ (A₁ ⧸ I) X.B
  -- the scalar towers on the coordinate ring of the affine open
  have _tAC : IsScalarTower A₁ ((A₁ ⧸ I) ⊗[X.A] X.B)
      (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁) := by
    refine ⟨fun x y z => ?_⟩
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => simp only [smul_add, ha, hb]
    | tmul b c => simp only [TensorProduct.smul_tmul', smul_assoc]
  have _tARC : IsScalarTower A₁ (A₁ ⧸ I) (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁) :=
    IsScalarTower.to₁₂₄ A₁ (A₁ ⧸ I) ((A₁ ⧸ I) ⊗[X.A] X.B)
      (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁)
  have _tAB₁C : IsScalarTower A₁ (A₁ ⊗[X.A] X.B)
      (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁) :=
    IsScalarTower.to₁₂₄ A₁ (A₁ ⊗[X.A] X.B) ((A₁ ⧸ I) ⊗[X.A] X.B)
      (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁)
  have _tBB₁C : IsScalarTower X.B (A₁ ⊗[X.A] X.B)
      (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁) :=
    IsScalarTower.to₁₂₄ X.B (A₁ ⊗[X.A] X.B) ((A₁ ⧸ I) ⊗[X.A] X.B)
      (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁)
  have _tAC₁C : IsScalarTower A₁ C₁ (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁) :=
    IsScalarTower.to₁₃₄ A₁ (A₁ ⊗[X.A] X.B) C₁
      (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁)
  have _tBC₁C : IsScalarTower X.B C₁ (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁) :=
    IsScalarTower.to₁₃₄ X.B (A₁ ⊗[X.A] X.B) C₁
      (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁)
  have _pC : Algebra.IsPushout A₁ (A₁ ⧸ I) C₁
      (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁) :=
    isPushout_comp_of_isPushout A₁ (A₁ ⧸ I) (A₁ ⊗[X.A] X.B) ((A₁ ⧸ I) ⊗[X.A] X.B) C₁
      (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁)
  -- the coordinate ring is the localization of `(A₁ ⧸ I) ⊗[X.A] X.B` away from the image of `s'`
  have _iloc : IsLocalization.Away (algebraMap X.B ((A₁ ⧸ I) ⊗[X.A] X.B) s')
      (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁) := by
    have h := isLocalization_away_tensorProduct (algebraMap X.B (A₁ ⊗[X.A] X.B) s') C₁
      ((A₁ ⧸ I) ⊗[X.A] X.B)
    rwa [← IsScalarTower.algebraMap_apply X.B (A₁ ⊗[X.A] X.B) ((A₁ ⧸ I) ⊗[X.A] X.B) s'] at h
  -- finiteness and smallness of the spreadout module
  have _fpB₂ : Algebra.FinitePresentation (A₁ ⧸ I) ((A₁ ⧸ I) ⊗[X.A] X.B) :=
    Algebra.FinitePresentation.baseChange _
  have _fpC : Algebra.FinitePresentation (A₁ ⧸ I)
      (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁) :=
    Algebra.FinitePresentation.of_isLocalization_away (A₁ ⧸ I) ((A₁ ⧸ I) ⊗[X.A] X.B)
      (algebraMap X.B ((A₁ ⧸ I) ⊗[X.A] X.B) s')
      (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁)
  have _smC : Small.{u₁} (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁) :=
    Stacks.Flatness.small_of_algebra_finitePresentation (A₁ ⧸ I) _
  have _fpM := Stacks.Flatness.finitePresentation_tensorProduct X.B
    (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁) N₀
  have _smM₀ : Small.{u₁} ((((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁) ⊗[X.B] N₀) :=
    Stacks.Flatness.small_tensorProduct_of_finitePresentation X.B
      (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁) N₀
  have _smM : Small.{max u₁ (max u₃ u₄)}
      ((((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁) ⊗[X.B] N₀) :=
    small_lift.{max u₁ u₂, max u₃ u₄, u₁} _
  -- projectivity and the closed-fibre condition over the quotient
  have _proj := projective_of_free_tensorProduct A₁ I X.B C₁
    (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁) N₀ hfree
  have hfibA : ∀ u ∈ X.S, ∀ y : C₁ ⊗[X.B] N₀,
      u • y ∈ IsLocalRing.maximalIdeal A₁ • (⊤ : Submodule A₁ (C₁ ⊗[X.B] N₀)) →
        y ∈ IsLocalRing.maximalIdeal A₁ • (⊤ : Submodule A₁ (C₁ ⊗[X.B] N₀)) := by
    intro u hu y hy
    refine hfib₁ u hu y ?_
    rwa [IsScalarTower.algebraMap_smul]
  have hfibC := fibre_smul_mem_of_quotient A₁ I X.B C₁
    (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁) N₀ hIle X.S hfibA
  exact X.nonempty_pureSpreadout_baseChange_quotient_aux A₁ I N₀ hs'
    (((A₁ ⧸ I) ⊗[X.A] X.B) ⊗[A₁ ⊗[X.A] X.B] C₁) _proj hfibC ψ hψ

/-- **Stacks Project, Tag 0AT8.** In the standing situation of Stacks 0AT6, for every prime `𝔭` of
the base ring there is a finitely generated ideal `I` of the local ring `A_𝔭`, contained in the
extension of `𝔭`, such that the base change of the situation to `A_𝔭 ⧸ I` carries a pure spreadout.

The test-module universe of the universal injectivity packaged in the pure spreadout is left free,
so the statement instantiates at any test universe. -/
@[stacks 0AT8]
theorem exists_fg_ideal_localQuotientBaseChange_pureSpreadout (p : Ideal X.A) [p.IsPrime] :
    ∃ I : Ideal (Localization.AtPrime p), I.FG ∧
      I ≤ p.map (algebraMap X.A (Localization.AtPrime p)) ∧
      ∃ Y : FinitelyPresentedLocalizedModuleSituation.{u₁, max u₁ u₂, max u₁ u₃,
          max u₁ (max u₃ u₄)},
        Nonempty (LocalQuotientBaseChange X Y p I) ∧
          Nonempty (PureSpreadout.{u₁, max u₁ u₂, max u₁ u₃, max u₁ (max u₃ u₄), u₅} Y) := by
  obtain ⟨N₀, _, _, φ₀, _, _⟩ := PureSpreadout.exists_finitePresentation_isLocalizedModule X
  obtain ⟨s', hs', I, hIfg, hIle, hfib₁, hfree⟩ :=
    X.exists_fg_ideal_fibre_free (Localization.AtPrime p) N₀
  refine ⟨I, hIfg, ?_, X.baseChange (Localization.AtPrime p ⧸ I),
    ⟨X.localQuotientBaseChange p I⟩, ?_⟩
  · rwa [IsLocalization.AtPrime.map_eq_maximalIdeal p (Localization.AtPrime p)]
  have hIproper : I ≠ ⊤ := fun htop =>
    (IsLocalRing.maximalIdeal.isMaximal (Localization.AtPrime p)).ne_top
      (top_le_iff.mp (htop ▸ hIle))
  have : Nontrivial (Localization.AtPrime p ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hIproper
  have : IsLocalRing (Localization.AtPrime p ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  obtain ⟨ψ, hψ⟩ :=
    X.exists_isLocalizedModule_localQuotientBaseChange (X.localQuotientBaseChange p I) N₀ φ₀
  exact X.nonempty_pureSpreadout_baseChange_quotient (Localization.AtPrime p) I hIle N₀ hs'
    (Localization.Away (algebraMap X.B (Localization.AtPrime p ⊗[X.A] X.B) s')) hfib₁ hfree ψ hψ

end

end FinitelyPresentedLocalizedModuleSituation

/-- **Stacks Project, Tag 0AT9**, unconditionally. In the finitely presented localized-module
situation, a linear map between flat modules which is injective on every residue-field fibre is
universally injective.

This is `AlgebraicGeometry.universallyInjective_of_rTensor_residueField_injective_of_pureSpreadout`
with its `hAT8` hypothesis discharged by Stacks 0AT8, instantiated at the test-module universe that
binder pins. -/
@[stacks 0AT9]
theorem universallyInjective_of_rTensor_residueField_injective
    (X : FinitelyPresentedLocalizedModuleSituation.{u₁, u₂, u₃, u₄})
    {M : Type u₄} [AddCommGroup M] [Module X.A M]
    [Module.Flat X.A X.N] [Module.Flat X.A M]
    (u : X.N →ₗ[X.A] M)
    (hu : ∀ (p : Ideal X.A) [p.IsPrime],
      Function.Injective (u.rTensor p.ResidueField)) :
    UniversallyInjective u :=
  universallyInjective_of_rTensor_residueField_injective_of_pureSpreadout X
    (fun p _ => X.exists_fg_ideal_localQuotientBaseChange_pureSpreadout p) u hu

/-- **Stacks 0AT9 unbundled, with the universes of its consumers.** In the finitely presented
localized situation with flat source and flat target, injectivity on every residue-field fibre
gives universal injectivity tested in an arbitrary universe.

This is `AlgebraicGeometry.universallyInjective_of_rTensor_residueField_injective` stated for
an unbundled finitely presented localized module rather than for a
`FinitelyPresentedLocalizedModuleSituation`, with the module and its target in independent
universes; they are `ULift`ed to their join to assemble the situation, and the resulting
injectivity is transported back along those lifts. -/
theorem universallyInjective_of_flat_of_fibres
    {R : Type u₁} {B₀ : Type u₂} {B : Type u₃} {N : Type u₄} {M : Type u₆}
    [CommRing R] [CommRing B₀] [CommRing B]
    [Algebra R B₀] [Algebra B₀ B] [Algebra R B] [IsScalarTower R B₀ B]
    [Algebra.FinitePresentation R B₀] (W : Submonoid B₀) [IsLocalization W B]
    [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]
    [Module.FinitePresentation B N] [Module.Flat R N]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    (f : N →ₗ[R] M)
    (hf : ∀ (p : Ideal R) [p.IsPrime], Function.Injective (f.rTensor p.ResidueField)) :
    UniversallyInjectivePoly.{_, u₅} f := by
  let N' := ULift.{max u₅ u₁ u₂ u₃ u₄ u₆} N
  let M' := ULift.{max u₅ u₁ u₂ u₃ u₄ u₆} M
  let eNB : N' ≃ₗ[B] N := ULift.moduleEquiv
  let : Module.FinitePresentation B N' := Module.FinitePresentation.of_equiv eNB.symm
  let X : FinitelyPresentedLocalizedModuleSituation := {
    A := R, B := B₀, Bₛ := B, N := N', S := W }
  let : Module R X.N := X.moduleBase
  let eN : X.N ≃ₗ[R] N := {
    toFun := ULift.down
    invFun := ULift.up
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := by
      intro r n
      change (algebraMap B₀ B (algebraMap R B₀ r)) • n.down = r • n.down
      rw [← IsScalarTower.algebraMap_apply R B₀ B, IsScalarTower.algebraMap_smul] }
  let eM : M' ≃ₗ[R] M := ULift.moduleEquiv
  let : Module.Flat R X.N := Module.Flat.of_linearEquiv eN
  let : Module.Flat R M' := Module.Flat.of_linearEquiv eM
  let f' := eM.symm.toLinearMap ∘ₗ f ∘ₗ eN.toLinearMap
  have hf' : ∀ (p : Ideal R) [p.IsPrime], Function.Injective (f'.rTensor p.ResidueField) := by
    intro p hp
    change Function.Injective (((eM.symm.toLinearMap ∘ₗ f) ∘ₗ eN.toLinearMap).rTensor _)
    rw [LinearMap.rTensor_comp, LinearMap.rTensor_comp]
    exact (eM.symm.rTensor _).injective.comp ((hf p).comp (eN.rTensor _).injective)
  have h := universallyInjective_of_rTensor_residueField_injective X f' hf'
  intro Q _ _
  let Q' := ULift.{max u₅ u₁ u₂ u₃ u₄ u₆} Q
  let eQ : Q ≃ₗ[R] Q' := ULift.moduleEquiv.symm
  apply (injective_rTensor_iff_of_equiv f eQ).mpr
  have hcomm : f'.rTensor Q' ∘ₗ (eN.symm.rTensor Q').toLinearMap =
      (eM.symm.rTensor Q').toLinearMap ∘ₗ f.rTensor Q' := by
    ext n q
    simp [f']
  have hinj := (h Q').comp (eN.symm.rTensor Q').injective
  change Function.Injective (f'.rTensor Q' ∘ₗ (eN.symm.rTensor Q').toLinearMap) at hinj
  rw [hcomm] at hinj
  exact fun x y hxy => hinj (congrArg (eM.symm.rTensor Q') hxy)

end AlgebraicGeometry

end
