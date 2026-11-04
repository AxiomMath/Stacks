module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizeAffine
public import StacksFrontier.RingTheory.AdicCompletion.TorsionBaseChangeDescent
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The transition-image equality descends from the chart ring `B` to `A`

The route of [Stacks, Tag 0EHK] proves its stabilisation of transition images over the completed
chart ring `B = (A_f)^∧_{I A_f}`, because that is the only ring over which the cocone of the route
has a *finite* vertex
(`Stacks.Algebraization.finite_adicCompletion_limit_localizedModuleFunctor_of_isFiniteModuleModel`).
What the consumer
`Stacks.Algebraization.isEssentiallyConstantModFiniteLength_dualizingExtSystem_of_chart` asks for
is the same equality over `A`, in the `Submodule.localized₀` spelling. This file is that descent.

It runs in two steps, neither of which uses faithful flatness of `A_f → B` — and none is
available, the closed point having been removed.

* `B` to `A_f` is `Stacks.range_eq_range_of_baseChange_adicCompletion`: the target of the two maps
  is annihilated by a power of `I`, and on such a module the unit of the base change along the
  `I`-adic completion is bijective. See the module docstring of
  `StacksFrontier.RingTheory.AdicCompletion.TorsionBaseChangeDescent`.
* `A_f` to the `Submodule.localized₀` form over `A` is Mathlib's
  `LinearMap.range_localizedMap_eq_localized₀_range`, which identifies the localization of an
  image with the image of the localized map, together with
  `Submodule.restrictScalars_localized'`.

## Main definitions

* `Stacks.Algebraization.localizedMapAway` — the localization away from `f` of an `A`-linear map,
  as an `A_f`-linear map. Its clause is
  `Stacks.Algebraization.localizedMapAway_apply`.

## Main results

* `Stacks.Algebraization.pow_smul_top_localizedModule_eq_bot` and
  `Stacks.Algebraization.isIPowerTorsion_localizedModule_away` — the torsion hypothesis of the
  descent, in the shape the systems of [Stacks, Tag 0EHK] carry it (`Iᵏ • ⊤ = ⊥`) and in the
  shape `Stacks.range_eq_range_of_baseChange_adicCompletion` wants it (`IsIPowerTorsion`).
* `Stacks.Algebraization.localized₀_range_eq_of_range_baseChange_adicCompletion` — the descent for
  one pair of maps.
* `Stacks.Algebraization.exists_localized₀_range_transitionMap_eq_of_baseChange` — the descent for
  the whole stabilisation statement of a system, which is the shape
  `Stacks.Algebraization.isEssentiallyConstantModFiniteLength_dualizingExtSystem_of_chart`
  consumes one chart at a time.

## Implementation notes

The chart ring is spelled `Localization (Submonoid.powers f)` and not `Localization.Away f`, and
the completed chart ring is spelled out rather than taken from `Stacks.Rig.CompletedAway`. That is
deliberate: the other declarations of this route
(`Stacks.Algebraization.finite_adicCompletion_limit_localizedModuleFunctor_of_isFiniteModuleModel`,
`Stacks.Algebraization.localizedModuleFunctorAdicQuotientNatIso`) use the first spelling, and the
goals of the route are not syntactically rewritable across the two even where they are defeq.

The annihilation hypothesis is left as `Iᵏ • ⊤ = ⊥` at the ring `A`, rather than as
`IsIPowerTorsion` over `A_f`, because that is the form the terms of the `Ext` system of the route
carry it in (`Stacks.Algebraization.smul_top_dualizingExtSystem_eq_bot`). The conversion is
`Stacks.Algebraization.isIPowerTorsion_of_smul_top_eq_bot`, whose extension `S` is taken to be
`A_f` here, so the ideal of the conclusion is already the extended one.

## References

* [Stacks Project, Tag 0EHK](https://stacks.math.columbia.edu/tag/0EHK), the consumer.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped Pointwise

universe u

namespace Stacks.Algebraization

variable {A : Type u} [CommRing A]

/-- **The localization away from `f` of an `A`-linear map, as an `A_f`-linear map.** Mathlib's
`IsLocalizedModule.map` produces only an `A`-linear map between the two localized modules; it is
`A_f`-linear by `LinearMap.extendScalarsOfIsLocalization`, which is what
`Stacks.range_eq_range_of_baseChange_adicCompletion` needs at the ring `A_f`. Its underlying
function is unchanged, by `Stacks.Algebraization.localizedMapAway_apply`. -/
public def localizedMapAway (f : A) {X Y : Type u} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] (g : X →ₗ[A] Y) :
    LocalizedModule (Submonoid.powers f) X →ₗ[Localization (Submonoid.powers f)]
      LocalizedModule (Submonoid.powers f) Y :=
  (IsLocalizedModule.map (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) X)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) Y) g).extendScalarsOfIsLocalization
    (Submonoid.powers f) (Localization (Submonoid.powers f))

/-- **The clause of `Stacks.Algebraization.localizedMapAway`**: extending the scalars does not
change the function, so the `A_f`-linear map is the `A`-linear `IsLocalizedModule.map`. -/
public theorem localizedMapAway_apply (f : A) {X Y : Type u} [AddCommGroup X] [Module A X]
    [AddCommGroup Y] [Module A Y] (g : X →ₗ[A] Y)
    (x : LocalizedModule (Submonoid.powers f) X) :
    localizedMapAway f g x =
      IsLocalizedModule.map (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) X)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) Y) g x := rfl

/-- **The range of `Stacks.Algebraization.localizedMapAway` is the localization of the range.**
`LinearMap.range_localizedMap_eq_localized₀_range` read through
`Submodule.restrictScalars_localized'`: the `A_f`-submodule range of the `A_f`-linear localized
map, restricted to `A`, is `Submodule.localized₀` of the range. -/
public theorem restrictScalars_range_localizedMapAway (f : A) {X Y : Type u} [AddCommGroup X]
    [Module A X] [AddCommGroup Y] [Module A Y] (g : X →ₗ[A] Y) :
    (LinearMap.range (localizedMapAway f g)).restrictScalars A =
      Submodule.localized₀ (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) Y) (LinearMap.range g) := by
  rw [← LinearMap.range_localizedMap_eq_localized₀_range (Submonoid.powers f)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) X)
      (LocalizedModule.mkLinearMap (Submonoid.powers f) Y) g]
  rfl

/-- **Annihilation by a power of `I` passes to a localization.** Every element of the localized
module is a fraction `y / s`, and `Iᵏ` kills `y`. In the submodule calculus this is
`Submodule.localized₀_smul` with `Submodule.localized₀_top` and `Submodule.localized₀_bot`, the
same three steps that
`Stacks.Algebraization.isAdicModuleSystem_localizedModuleFunctor_of_isFiniteModuleModel` takes to
compute the kernel of a localized transition map. -/
public theorem pow_smul_top_localizedModule_eq_bot (I : Ideal A) (f : A) {Y : Type u}
    [AddCommGroup Y] [Module A Y] {k : ℕ}
    (hY : I ^ k • (⊤ : Submodule A Y) = ⊥) :
    I ^ k • (⊤ : Submodule A (LocalizedModule (Submonoid.powers f) Y)) = ⊥ := by
  have h := Submodule.localized₀_smul (Submonoid.powers f)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) Y) ⊤ (I ^ k)
  rw [hY, Submodule.localized₀_bot, Submodule.localized₀_top] at h
  exact h.symm

/-- **The torsion hypothesis of the descent, at the chart ring.** A module annihilated by `Iᵏ`
over `A` localizes to a module annihilated by `Iᵏ`, hence is `I A_f`-power torsion over `A_f`.
This is the hypothesis `hY` of `Stacks.range_eq_range_of_baseChange_adicCompletion` at the ring
`A_f`, and the conversion from the `Iᵏ • ⊤ = ⊥` shape that the module docstring of
`StacksFrontier.RingTheory.AdicCompletion.TorsionBaseChangeDescent` records as not restated
there. -/
public theorem isIPowerTorsion_localizedModule_away (I : Ideal A) (f : A) {Y : Type u}
    [AddCommGroup Y] [Module A Y] {k : ℕ}
    (hY : I ^ k • (⊤ : Submodule A Y) = ⊥) :
    IsIPowerTorsion (Localization (Submonoid.powers f))
      (LocalizedModule (Submonoid.powers f) Y)
      (I.map (algebraMap A (Localization (Submonoid.powers f)))) :=
  isIPowerTorsion_of_smul_top_eq_bot I k (pow_smul_top_localizedModule_eq_bot I f hY)

/-- **The descent of an equality of images from the completed chart ring to `A`.** Let `A` be
Noetherian, `f ∈ A`, and let `u : X₁ → Y` and `v : X₂ → Y` be `A`-linear with `Y` annihilated by
`Iᵏ`. If the two localized maps have equal images after base change to
`B = (A_f)^∧_{I A_f}`, then their images have the same localization away from `f`.

**No faithful flatness of `A_f → B` is involved**, and none is available on the route of
[Stacks, Tag 0EHK]: the chart is a chart of the *punctured* spectrum. What is used is that `Y_f`
is `I A_f`-power torsion, by
`Stacks.Algebraization.isIPowerTorsion_localizedModule_away`, and on such a module the unit of the
base change along the `I`-adic completion is bijective. -/
public theorem localized₀_range_eq_of_range_baseChange_adicCompletion [IsNoetherianRing A]
    (I : Ideal A) (f : A) {X₁ X₂ Y : Type u} [AddCommGroup X₁] [Module A X₁]
    [AddCommGroup X₂] [Module A X₂] [AddCommGroup Y] [Module A Y] {k : ℕ}
    (hY : I ^ k • (⊤ : Submodule A Y) = ⊥)
    (u : X₁ →ₗ[A] Y) (v : X₂ →ₗ[A] Y)
    (h : LinearMap.range ((localizedMapAway f u).baseChange
          (AdicCompletion (I.map (algebraMap A (Localization (Submonoid.powers f))))
            (Localization (Submonoid.powers f)))) =
        LinearMap.range ((localizedMapAway f v).baseChange
          (AdicCompletion (I.map (algebraMap A (Localization (Submonoid.powers f))))
            (Localization (Submonoid.powers f))))) :
    Submodule.localized₀ (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) Y) (LinearMap.range u) =
      Submodule.localized₀ (Submonoid.powers f)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) Y) (LinearMap.range v) := by
  have : IsNoetherianRing (Localization (Submonoid.powers f)) :=
    IsLocalization.isNoetherianRing (Submonoid.powers f) _ inferInstance
  have key := Stacks.range_eq_range_of_baseChange_adicCompletion
    (I.map (algebraMap A (Localization (Submonoid.powers f))))
    (isIPowerTorsion_localizedModule_away I f hY) (localizedMapAway f u) (localizedMapAway f v) h
  rw [← restrictScalars_range_localizedMapAway, ← restrictScalars_range_localizedMapAway, key]

/-- **The descent of the whole stabilisation statement of a system.** For a system `G` of
`A`-modules whose terms are annihilated by powers of `I`, the stabilisation of the transition
images over `B = (A_f)^∧_{I A_f}` gives the stabilisation of their localizations away from `f`
over `A`, with the same index `a`.

The conclusion is the hypothesis `himg` of
`Stacks.Algebraization.isEssentiallyConstantModFiniteLength_dualizingExtSystem_of_chart` at one
chart, read at `G = Stacks.Algebraization.dualizingExtSystem M ω i`, whose terms carry the
annihilation hypothesis by `Stacks.Algebraization.smul_top_dualizingExtSystem_eq_bot`. -/
public theorem exists_localized₀_range_transitionMap_eq_of_baseChange [IsNoetherianRing A]
    (I : Ideal A) (f : A) (G : ℕ ⥤ ModuleCat.{u} A)
    (hann : ∀ n : ℕ, ∃ k : ℕ, I ^ k • (⊤ : Submodule A (G.obj n)) = ⊥)
    (h : ∃ a : ℕ, ∀ (m : ℕ) (hm : a ≤ m), ∃ k : ℕ, ∀ (n : ℕ) (hmn : m ≤ n), k ≤ n →
      LinearMap.range ((localizedMapAway f (G.map (homOfLE hmn)).hom).baseChange
          (AdicCompletion (I.map (algebraMap A (Localization (Submonoid.powers f))))
            (Localization (Submonoid.powers f)))) =
        LinearMap.range ((localizedMapAway f (G.map (homOfLE (hm.trans hmn))).hom).baseChange
          (AdicCompletion (I.map (algebraMap A (Localization (Submonoid.powers f))))
            (Localization (Submonoid.powers f))))) :
    ∃ a : ℕ, ∀ (m : ℕ) (hm : a ≤ m), ∃ k : ℕ, ∀ (n : ℕ) (hmn : m ≤ n), k ≤ n →
      Submodule.localized₀ (Submonoid.powers f)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) (G.obj n))
          (LinearMap.range ((G.map (homOfLE hmn)).hom)) =
        Submodule.localized₀ (Submonoid.powers f)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) (G.obj n))
          (LinearMap.range ((G.map (homOfLE (hm.trans hmn))).hom)) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, fun m hm => ?_⟩
  obtain ⟨k, hk⟩ := ha m hm
  refine ⟨k, fun n hmn hkn => ?_⟩
  obtain ⟨c, hc⟩ := hann n
  exact localized₀_range_eq_of_range_baseChange_adicCompletion I f hc _ _ (hk n hmn hkn)

end Stacks.Algebraization

end
