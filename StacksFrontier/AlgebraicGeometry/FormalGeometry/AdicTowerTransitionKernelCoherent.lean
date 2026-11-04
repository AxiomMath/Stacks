module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentSubquotients.Abelian
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AdicTowerTransitionKernel
public import StacksFrontier.RingTheory.Noetherian.NilpotentKernel

/-!
# Coherence of the transition kernels of a cartesian adic tower

`StacksFrontier/AlgebraicGeometry/FormalGeometry/AdicTowerTransitionKernel.lean` builds
`𝓕ₙ = Ker(𝒪_{X_{n+1}} ⟶ 𝒪_{Xₙ})` as a quasi-coherent `𝒪_{X₀}`-module. The second paragraph of
the proof of [Stacks, Tag 089A] asserts that it is *coherent*, which is what this file proves.

The source leaves the reason implicit; it is that every member of the tower is a locally
Noetherian scheme. Only `X₀` is given as such — `q₀ : X₀ ⟶ S₀` is proper, hence locally of
finite type over the Noetherian `S₀ = Spec (A / I)` — and `Xₙ ⟶ Sₙ` is not assumed to be of
finite type for `n > 0`. What makes `X_{n+1}` locally Noetherian all the same is that `X₀` is a
*thickening* of it with finitely generated nilpotent ideal: on an affine open `U` of `X_{n+1}`
the map `Γ(X_{n+1}, U) ⟶ Γ(X₀, incl ⁻¹ᵁ U)` is surjective with kernel the extension of the
ideal of `S₀` in `A / I ^ (n + 2)` (`Stacks.AdicTower.ideal_ker_incl`), which is finitely
generated because `A / I ^ (n + 2)` is Noetherian and whose `(n + 2)`-nd power vanishes
(`Stacks.AdicTower.pow_ker_appTop_thickeningIncl`). That is exactly the hypothesis of
`isNoetherianRing_of_surjective_fg_nilpotent_ker`.

With that, `𝓕ₙ` is coherent upstairs — a kernel of a map of coherent `𝒪_{X_{n+1}}`-modules, the
structure sheaf and the direct image of `𝒪_{Xₙ}` along the finite morphism `tₙ` — and the
inverse image of a coherent module along `X₀ ⟶ X_{n+1}` is coherent because `X₀` is locally
Noetherian.

## Main results

* `Stacks.AdicTower.isLocallyNoetherian_tower`: every `Xₙ` is locally Noetherian.
* `Stacks.AdicTower.isCoherent_transitionIdeal`: `Ker(𝒪_{X_{n+1}} ⟶ 𝒪_{Xₙ})` is a coherent
  `𝒪_{X_{n+1}}`-module.
* `Stacks.AdicTower.isCoherent_transitionKernel`: **`𝓕ₙ` is a coherent `𝒪_{X₀}`-module**, the
  conclusion of the first half of the second paragraph of the proof of [Stacks, Tag 089A].

## References

* [Stacks Project, Tag 089A](https://stacks.math.columbia.edu/tag/089A)
* [Stacks Project, Tag 01Y0](https://stacks.math.columbia.edu/tag/01Y0)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.AdicTower

variable {A : Type u} [CommRing A] {I : Ideal A} {Xn : ℕ → Scheme.{u}}
  (q : ∀ n, Xn n ⟶ adicThickening A I n) (t : ∀ n, Xn n ⟶ Xn (n + 1))
  (hcart : ∀ n, IsPullback (t n) (q n) (q (n + 1)) (adicThickeningSucc A I n))

/-! ### Local Noetherianity of the tower -/

/-- **The closed member of the tower is locally Noetherian**, being proper — hence locally of
finite type — over the Noetherian affine scheme `S₀ = Spec (A / I)`. -/
lemma isLocallyNoetherian_zero [IsNoetherianRing A] [IsProper (q 0)] :
    IsLocallyNoetherian (Xn 0) :=
  LocallyOfFiniteType.isLocallyNoetherian (q 0)

/-- The ring of the affine base `S_{n+1}` is Noetherian. -/
lemma isNoetherianRing_sections_adicThickening [IsNoetherianRing A] (n : ℕ) :
    IsNoetherianRing Γ(adicThickening A I n, ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

include hcart in
/-- **Every member of the tower is locally Noetherian.** On an affine open of `X_{n+1}` the
sections surject onto the sections of the locally Noetherian `X₀` with a finitely generated
nilpotent kernel, so `isNoetherianRing_of_surjective_fg_nilpotent_ker` applies. -/
lemma isLocallyNoetherian_succ [IsNoetherianRing A] [IsProper (q 0)] (n : ℕ) :
    IsLocallyNoetherian (Xn (n + 1)) := by
  have : IsLocallyNoetherian (Xn 0) := isLocallyNoetherian_zero q
  have : IsClosedImmersion (incl t (n + 1)) := isClosedImmersion_incl q t hcart (n + 1)
  have : IsNoetherianRing Γ(adicThickening A I (n + 1), ⊤) :=
    isNoetherianRing_sections_adicThickening (n + 1)
  refine ⟨fun U => ?_⟩
  have : IsNoetherianRing Γ(Xn 0, incl t (n + 1) ⁻¹ᵁ (U : (Xn (n + 1)).Opens)) :=
    IsLocallyNoetherian.component_noetherian ⟨_, U.2.preimage _⟩
  have hker : RingHom.ker ((incl t (n + 1)).app (U : (Xn (n + 1)).Opens)).hom =
      (RingHom.ker (thickeningIncl A I (n + 1)).appTop.hom).map (baseAppLE q n U).hom := by
    rw [← ideal_ker_incl q t hcart n U, Scheme.Hom.ker_apply]
  refine isNoetherianRing_of_surjective_fg_nilpotent_ker
    ((incl t (n + 1)).app (U : (Xn (n + 1)).Opens)).hom
    (Scheme.Hom.app_surjective _ _ U.2) ?_ ?_
  · rw [hker]
    exact Ideal.FG.map (Ideal.fg_of_isNoetherianRing _) _
  · refine ⟨n + 2, ?_⟩
    rw [Ideal.zero_eq_bot, hker, ← Ideal.map_pow, pow_ker_appTop_thickeningIncl, Ideal.map_bot]

include hcart in
/-- **Every member of the tower is locally Noetherian.** -/
lemma isLocallyNoetherian_tower [IsNoetherianRing A] [IsProper (q 0)] :
    ∀ n : ℕ, IsLocallyNoetherian (Xn n)
  | 0 => isLocallyNoetherian_zero q
  | n + 1 => isLocallyNoetherian_succ q t hcart n

/-! ### Coherence -/

include hcart in
/-- **The transition ideal sheaf is coherent on `X_{n+1}`.** It is the kernel of the comorphism
`𝒪_{X_{n+1}} ⟶ (tₙ)_* 𝒪_{Xₙ}`, a map of coherent modules on a locally Noetherian scheme: the
structure sheaf is coherent, and the direct image of the coherent `𝒪_{Xₙ}` along the finite
morphism `tₙ` is coherent by [Stacks, Tag 01Y6]. -/
lemma isCoherent_transitionIdeal [IsNoetherianRing A] [IsProper (q 0)] (n : ℕ) :
    (transitionIdeal t n).IsCoherent := by
  have : IsLocallyNoetherian (Xn (n + 1)) := isLocallyNoetherian_succ q t hcart n
  have : IsLocallyNoetherian (Xn n) := isLocallyNoetherian_tower q t hcart n
  have : IsClosedImmersion (t n) := isClosedImmersion_transition q t hcart n
  have : (SheafOfModules.unit (Xn (n + 1)).ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent (Xn (n + 1))
  have : (SheafOfModules.unit (Xn n).ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent (Xn n)
  have : ((SheafOfModules.pushforward (Scheme.Hom.toRingCatSheafHom (t n))).obj
      (SheafOfModules.unit (Xn n).ringCatSheaf)).IsCoherent :=
    Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite
      (t n) (SheafOfModules.unit (Xn n).ringCatSheaf)
  exact AlgebraicGeometry.isCoherent_kernel
    (SheafOfModules.unitToPushforwardObjUnit (t n).toRingCatSheafHom)

include hcart in
/-- **`𝓕ₙ` is a coherent `𝒪_{X₀}`-module.** This is the conclusion of the first half of the
second paragraph of the proof of [Stacks, Tag 089A]: the transition kernel is coherent upstairs
and annihilated by the ideal of `X₀`, so its inverse image on the locally Noetherian `X₀` is
coherent. -/
lemma isCoherent_transitionKernel [IsNoetherianRing A] [IsProper (q 0)] (n : ℕ) :
    (transitionKernel t n).IsCoherent := by
  have : IsLocallyNoetherian (Xn 0) := isLocallyNoetherian_zero q
  have : (transitionIdeal t n).IsCoherent := isCoherent_transitionIdeal q t hcart n
  exact AlgebraicGeometry.isCoherent_pullback (incl t (n + 1)) (transitionIdeal t n)

end Stacks.AdicTower

end
