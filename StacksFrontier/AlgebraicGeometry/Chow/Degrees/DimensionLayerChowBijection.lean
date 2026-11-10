module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ChowToWideLayerGeneral
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerChowComparison

/-!
# Chow groups as K-groups of dimension layers

Let `(S, δ)` be as in Situation 02QL and let `X` be a scheme locally of finite type over `S`.
Tag 02SC asserts that the map

`CH_k(X) ⟶ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`

of Tag 0FDS (here `Stacks.Chow.chowToWideLayerHom`) is a bijection from `CH_k(X)` onto the image
`B_k(X)` (here `Stacks.Chow.coherentDimensionLayerImage`) of the map
`K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) ⟶ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`.

The proof is the source's. By Tag 02S9 the group `Z_k(X)` is identified with
`K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` compatibly with the map of Tag 0FDS, which makes the image of that
map exactly `B_k(X)`. For injectivity, an element of `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` dying in
`K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` lifts to `K₀(Coh_{≤k}(X))` (Homology, Lemma 02MX (1)), and a
class of `K₀(Coh_{≤k}(X))` dying in the wide layer has rationally trivial cycle: that is
`Stacks.Chow.layerChowClass_eq_zero_of_layerWideningClass_eq_zero`, proved through Homology,
Lemma 02MX (2) and Tag 02SB.

## Main results

* `Stacks.Chow.chowToWideLayerHom_injective_and_range` — **Stacks 02SC**: the map of Tag 0FDS is
  injective with image `B_k(X)`.
* `Stacks.Chow.chowGroupAddEquivDimensionLayerImage` — the resulting isomorphism
  `CH_k(X) ≃ B_k(X)`.

## References

* [Stacks Project, Tag 02MX](https://stacks.math.columbia.edu/tag/02MX)
* [Stacks Project, Tag 02S9](https://stacks.math.columbia.edu/tag/02S9)
* [Stacks Project, Tag 02SB](https://stacks.math.columbia.edu/tag/02SB)
* [Stacks Project, Tag 02SC](https://stacks.math.columbia.edu/tag/02SC)
* [Stacks Project, Tag 0FDS](https://stacks.math.columbia.edu/tag/0FDS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace KZero

/-- The comparison homomorphism `K₀ ⟶ GrothendieckGroup` is a left inverse of
`KZero.ofGrothendieckGroup`. -/
theorem toGrothendieckGroup_ofGrothendieckGroup {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    (y : GrothendieckGroup 𝒜) : toGrothendieckGroup (ofGrothendieckGroup y) = y :=
  DFunLike.congr_fun (GrothendieckGroup.hom_ext
    (φ := toGrothendieckGroup.comp ofGrothendieckGroup) (ψ := AddMonoidHom.id _)
    fun X ↦ by simp) y

end KZero

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-- The homomorphism `K₀(Coh_{≤k}(X)) ⟶ CH_k(X)`, `[A] ↦ [[A]_k]`, factors through
`K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X))` and the cycle class map of Tag 02S9. -/
theorem layerChowClass_eq_comp (C : ChowSituation.{u}) (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (k : ℤ) :
    layerChowClass C sX k =
      (QuotientAddGroup.mk' (rationalEquivalences C sX k)).comp
        ((dimensionLayerCycleHom C sX k).comp (KZero.toGrothendieckGroup.comp
          (KZero.map (lowerDimensionClass C sX (k - 1) k).isoModSerre.Q))) :=
  KZero.hom_ext fun A ↦ by
    rw [layerChowClass_mk, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
      AddMonoidHom.comp_apply, KZero.map_mk, KZero.toGrothendieckGroup_mk,
      dimensionLayerCycleHom_of]
    rfl

/-- **Stacks 02SC.** Let `X` be locally of finite type over `(S, δ)`. The map
`CH_k(X) ⟶ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))` of Tag 0FDS is injective, and its image is the image
`B_k(X)` of `K₀(Coh_{≤k}(X)/Coh_{≤k-1}(X)) ⟶ K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`; that is, it
induces a bijection from `CH_k(X)` onto `B_k(X)`. -/
@[stacks 02SC]
theorem chowToWideLayerHom_injective_and_range (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (k : ℤ) :
    Function.Injective (chowToWideLayerHom C sX k) ∧
      (chowToWideLayerHom C sX k).range = coherentDimensionLayerImage C sX k := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun q hq ↦ ?_, le_antisymm ?_ ?_⟩
  · obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
    rw [chowToWideLayerHom_mk] at hq
    obtain ⟨a, ha⟩ := KZero.surjective_map_localization (lowerDimensionClass C sX (k - 1) k)
      (lowerDimensionClass C sX (k - 1) k).isoModSerre.Q
      (KZero.ofGrothendieckGroup (cycleDimensionLayerHom C sX k c))
    have hw : layerWideningClass C sX k a = 0 := by
      rw [layerWideningClass, AddMonoidHom.comp_apply, ha]
      exact hq
    have h := layerChowClass_eq_zero_of_layerWideningClass_eq_zero C sX k a hw
    rw [layerChowClass_eq_comp, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply,
      AddMonoidHom.comp_apply, ha, KZero.toGrothendieckGroup_ofGrothendieckGroup,
      dimensionLayerCycleHom_cycleDimensionLayerHom] at h
    exact h
  · rintro _ ⟨q, rfl⟩
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
    exact ⟨_, (chowToWideLayerHom_mk C sX k c).symm⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨c, hc⟩ := (cycleGroupAddEquivDimensionLayer C sX k).surjective
      (KZero.toGrothendieckGroup x)
    refine ⟨QuotientAddGroup.mk' (rationalEquivalences C sX k) c, ?_⟩
    rw [chowToWideLayerHom_mk]
    change coherentDimensionLayerHom C sX k
      (KZero.ofGrothendieckGroup (cycleGroupAddEquivDimensionLayer C sX k c)) = _
    rw [hc, KZero.ofGrothendieckGroup_toGrothendieckGroup]

/-- **Stacks 02SC**, as an isomorphism: the map of Tag 0FDS identifies `CH_k(X)` with the subgroup
`B_k(X)` of `K₀(Coh_{≤k+1}(X)/Coh_{≤k-1}(X))`. -/
def chowGroupAddEquivDimensionLayerImage (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (k : ℤ) :
    chowGroup C sX k ≃+ coherentDimensionLayerImage C sX k :=
  (AddMonoidHom.ofInjective (f := chowToWideLayerHom C sX k)
    (chowToWideLayerHom_injective_and_range C sX k).1).trans
    (AddEquiv.addSubgroupCongr (chowToWideLayerHom_injective_and_range C sX k).2)

/-- The isomorphism `CH_k(X) ≃ B_k(X)` is the map of Tag 0FDS. -/
@[simp]
theorem coe_chowGroupAddEquivDimensionLayerImage_apply (C : ChowSituation.{u}) (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (k : ℤ) (q : chowGroup C sX k) :
    (chowGroupAddEquivDimensionLayerImage C sX k q : coherentDimensionKZero C sX (k - 1) (k + 1)) =
      chowToWideLayerHom C sX k q :=
  rfl

end Stacks.Chow

end
