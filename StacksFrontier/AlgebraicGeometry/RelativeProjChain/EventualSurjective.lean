module

public import StacksFrontier.AlgebraicGeometry.ProjMapData.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistCompare.Twist
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Order.Filter.AtTopBot.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Graded homomorphisms surjective in all large degrees

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings which is surjective on
homogeneous components of all sufficiently large degree. This file proves the two assertions of
Tag 01N1 that concern the morphism of schemes alone: the domain of definition
`U(ψ) ⊆ Proj ℬ` is the whole of `Proj ℬ`, and the induced morphism `U(ψ) ⟶ Proj 𝒜` is a closed
immersion.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjChain.surjective_awayMap_of_eventually_surjective`: the
  induced map `𝒜_{(f)} → ℬ_{(ψ f)}` of degree-zero homogeneous localizations is surjective for
  every homogeneous `f` of positive degree. This is the engine of the file.
* `Stacks.AlgebraicGeometry.RelativeProjChain.mapDomain_eq_top_of_eventually_surjective`:
  Tag 01N1 part (1), `U(ψ) = ⊤`.
* `Stacks.AlgebraicGeometry.RelativeProjChain.isClosedImmersion_mapHom_of_eventually_surjective`
  and its bundled companion
  `isClosedImmersion_projMapData_hom_of_eventually_surjective` in the same namespace:
  Tag 01N1 part (2), the induced morphism is a closed immersion, stated both for
  `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom` and for the underlying morphism of Tag 01MY's
  bundle `Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData`.

## Implementation notes

Eventual surjectivity is strictly weaker than surjectivity, and both results genuinely need the
weaker hypothesis: already `𝒜` concentrated in degree zero and `ℬ = k[y]/(y^N)` has every large
degree of `ℬ` zero while `ψ` is surjective in no positive degree, so
`Stacks.AlgebraicGeometry.ProjShared.mapDomain_eq_top_of_surjective` does not apply. The route is
the same in both cases and consists of one power trick: a homogeneous element of positive degree
`m` has its `k`-th power in degree `k * m`, which exceeds any bound once `k` is large, so the
power is in the image even when the element is not.

The same remark explains why Mathlib's `AlgebraicGeometry.Proj.map` is unavailable here. That
construction needs the *plain* inclusion of the irrelevant ideal of `ℬ` in the image of the
irrelevant ideal of `𝒜`, and in the example just given that inclusion fails while `U(ψ) = ⊤`
holds; `U(ψ) = ⊤` is equivalent only to the *radical* inclusion, by
`Stacks.AlgebraicGeometry.ProjShared.mapDomain_eq_top_iff_irrelevant_le_radical`. Everything is
therefore phrased for `Stacks.AlgebraicGeometry.ProjTwistChain.mapHom`, the morphism built by
gluing over the standard opens of the domain of definition.

The closed immersion is obtained from `IsZariskiLocalAtTarget`, on the cover of `Proj 𝒜` by the
standard opens `D₊(f)` of the homogeneous elements of positive degree, which is where
`Stacks.AlgebraicGeometry.ProjShared.exists_homogeneous_pos_notMem` enters. Over `D₊(f)` the
morphism is identified with the map of affine schemes attached to `𝒜_{(f)} → ℬ_{(ψ f)}` through
`Stacks.AlgebraicGeometry.ProjTwistChain.homOfLE_mapHom` and
`Stacks.AlgebraicGeometry.ProjTwistChain.mapHom_preimage_basicOpen`, and the identification is
checked after composing with the mono `D₊(f).ι` rather than by unfolding the gluing.

Two elaboration points. The degree of a homogeneous element is an implicit argument of
`AlgebraicGeometry.Proj.awayι` and `AlgebraicGeometry.Proj.basicOpenIsoSpec`, inferred from the
membership proof, so the degree is kept as a single free variable throughout and the same pair of
hypotheses `hf`, `hd` is handed to every occurrence: two syntactically different degrees are
equal by proof irrelevance but will not unify under `rw`. And the comparison between the
restriction of the domain of definition to a standard open and that standard open itself is
`AlgebraicGeometry.Scheme.Opens.isoOfLE`, whose direction is from the restriction to the open; it
is composed with `AlgebraicGeometry.Scheme.isoOfEq` on the inverse image, since
`mapHom ⁻¹ᵁ D₊(f)` and that restriction are equal opens rather than identical ones.

Both rings live in the single universe `u`, forced because `Proj ℬ ⟶ Proj 𝒜` must be a morphism
of `Scheme.{u}`; the two `SetLike` carriers are independent. No transparency attribute is needed
in this file: nothing here crosses the twisting sheaf's index category.

## What is not done

Tag 01N1's third assertion — that the comparison maps on all twists are isomorphisms when `𝒜` is
generated in degree one over `𝒜 0` — is not proved. It is a statement about
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistMap`, not about the morphism of schemes, and is
untouched here. Surjectivity of those comparison maps, Tag 01N0's twist assertion, is likewise
untouched.

## References

* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public section

open AlgebraicGeometry HomogeneousLocalization TopologicalSpace CategoryTheory Filter
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain

namespace Stacks.AlgebraicGeometry.RelativeProjChain

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-! ### Lifting homogeneous elements of large degree -/

omit [GradedRing 𝒜] [GradedRing ℬ] in
/-- Surjectivity in degree `d` as a statement about elements of `B` rather than about the
additive map between homogeneous components. -/
public theorem exists_mem_map_eq (ψ : 𝒜 →+*ᵍ ℬ) {N : ℕ}
    (hN : ∀ d, N ≤ d → Function.Surjective (GradedRingHom.gradedAddHom ψ d))
    {d : ℕ} (hd : N ≤ d) {g : B} (hg : g ∈ ℬ d) :
    ∃ a, a ∈ 𝒜 d ∧ ψ a = g := by
  obtain ⟨⟨a, ha⟩, hae⟩ := hN d hd ⟨g, hg⟩
  refine ⟨a, ha, ?_⟩
  have := congrArg Subtype.val hae
  rwa [GradedRingHom.gradedAddHom_apply_coe] at this

/-- A positive degree repeated at least `N` times is at least `N`. -/
private theorem le_smul_of_pos {N k d : ℕ} (hk : N ≤ k) (hd : 0 < d) : N ≤ k • d :=
  hk.trans (Nat.le_mul_of_pos_right k hd)

/-! ### Surjectivity on degree-zero localizations -/

/-- The map `𝒜_{(f)} → ℬ_{(ψ f)}` of degree-zero homogeneous localizations is surjective for
every homogeneous `f` of positive degree.

A fraction `b / (ψ f) ^ n` is rewritten as `b * (ψ f) ^ k / (ψ f) ^ (n + k)` with `n + k` large
enough that `ℬ ((n + k) * deg f)` is in the image, which is possible precisely because the degree
of `f` is positive. -/
public theorem surjective_awayMap_of_eventually_surjective (ψ : 𝒜 →+*ᵍ ℬ) {N : ℕ}
    (hN : ∀ d, N ≤ d → Function.Surjective (GradedRingHom.gradedAddHom ψ d))
    {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) :
    Function.Surjective (Away.map ψ f) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (ψ.map_mem hf) z
  have hlarge : N ≤ (n + N) • d := le_smul_of_pos (Nat.le_add_left N n) hd
  have hbk : b * (ψ f) ^ N ∈ ℬ ((n + N) • d) := by
    rw [add_smul]
    exact SetLike.mul_mem_graded hb (SetLike.pow_mem_graded N (ψ.map_mem hf))
  obtain ⟨a, ha, hae⟩ := exists_mem_map_eq 𝒜 ℬ ψ hN hlarge hbk
  refine ⟨Away.mk 𝒜 hf (n + N) a ha, ?_⟩
  rw [Away.map_mk ψ f hf (n + N) a ha]
  refine HomogeneousLocalization.val_injective _ ?_
  simp only [Away.val_mk, hae]
  rw [Localization.mk_eq_mk_iff]
  exact Localization.r_of_eq (by simp only [GradedRingHom.coe_toRingHom]; ring)

/-! ### The domain of definition and the closed immersion -/

omit [GradedRing 𝒜] in
/-- **Stacks 01N1 (1)**: a graded ring homomorphism surjective in all sufficiently large degrees
is defined on the whole of `Proj ℬ`.

A point of `Proj ℬ` omits some homogeneous `g` of positive degree `m`; a large power `g ^ k` is
homogeneous of degree `k * m`, is still omitted because the point is prime, and is in the image
of `ψ`. -/
@[stacks 01N1 "part (1): the domain is all of Proj", stacks 01N0 "domain"]
public theorem mapDomain_eq_top_of_eventually_surjective (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : ∀ᶠ d : ℕ in atTop, Function.Surjective (GradedRingHom.gradedAddHom ψ d)) :
    mapDomain 𝒜 ℬ ψ = ⊤ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hψ
  refine top_le_iff.mp fun y _ => (mem_mapDomain_iff 𝒜 ℬ ψ y).mpr ?_
  obtain ⟨m, g, hm, hg, hgy⟩ := exists_homogeneous_pos_notMem ℬ y
  have hlarge : N ≤ (N + 1) • m := le_smul_of_pos (Nat.le_succ N) hm
  have hpow : g ^ (N + 1) ∈ ℬ ((N + 1) • m) := SetLike.pow_mem_graded _ hg
  obtain ⟨a, ha, hae⟩ := exists_mem_map_eq 𝒜 ℬ ψ hN hlarge hpow
  refine ⟨(N + 1) • m, a, ?_, ha, ?_⟩
  · simpa only [smul_eq_mul] using Nat.mul_pos (Nat.succ_pos N) hm
  · rw [hae]
    exact fun hmem => hgy (y.isPrime.mem_of_pow_mem (N + 1) hmem)

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- The restriction of the domain of definition to a standard open of `Proj ℬ`, compared with
that standard open itself, is the inclusion. -/
@[reassoc]
public theorem isoOfLE_hom_homOfLE (ψ : 𝒜 →+*ᵍ ℬ) {d : ℕ} (hd : 0 < d) {f : A}
    (hf : f ∈ 𝒜 d) :
    (Scheme.Opens.isoOfLE (basicOpen_le_mapDomain 𝒜 ℬ ψ hd hf)).hom ≫
        (AlgebraicGeometry.Proj ℬ).homOfLE (basicOpen_le_mapDomain 𝒜 ℬ ψ hd hf) =
      ((mapDomain 𝒜 ℬ ψ).ι ⁻¹ᵁ Proj.basicOpen ℬ (ψ f)).ι := by
  rw [← cancel_mono (mapDomain 𝒜 ℬ ψ).ι, Category.assoc, Scheme.homOfLE_ι,
    Scheme.Opens.isoOfLE_hom_ι]

/-- Over the standard open `D₊(f)` the morphism induced by `ψ` is, up to the canonical
isomorphisms, the morphism of affine schemes attached to `𝒜_{(f)} → ℬ_{(ψ f)}`. -/
public theorem morphismRestrict_mapHom_eq (ψ : 𝒜 →+*ᵍ ℬ) {d : ℕ} (hd : 0 < d) {f : A}
    (hf : f ∈ 𝒜 d) :
    mapHom 𝒜 ℬ ψ ∣_ Proj.basicOpen 𝒜 f =
      ((mapDomain 𝒜 ℬ ψ).toScheme.isoOfEq
          (mapHom_preimage_basicOpen 𝒜 ℬ ψ f d hf hd)).hom ≫
        (Scheme.Opens.isoOfLE (basicOpen_le_mapDomain 𝒜 ℬ ψ hd hf)).hom ≫
        (Proj.basicOpenIsoSpec ℬ (ψ f) (mem_of_mem 𝒜 ℬ ψ hf) hd).hom ≫
        Spec.map (CommRingCat.ofHom (Away.map ψ f)) ≫
        (Proj.basicOpenIsoSpec 𝒜 f hf hd).inv := by
  rw [← cancel_mono (Proj.basicOpen 𝒜 f).ι, morphismRestrict_ι]
  simp only [Category.assoc, Proj.basicOpenIsoSpec_inv_ι, Proj.basicOpenIsoSpec_hom]
  rw [show Proj.basicOpenToSpec ℬ (ψ f) ≫ Spec.map (CommRingCat.ofHom (Away.map ψ f)) ≫
      Proj.awayι 𝒜 f hf hd = mapAwayHom 𝒜 ℬ ψ hd hf from rfl,
    ← homOfLE_mapHom 𝒜 ℬ ψ hd hf, isoOfLE_hom_homOfLE_assoc 𝒜 ℬ ψ hd hf,
    Scheme.isoOfEq_hom_ι_assoc]

/-- **Stacks 01N1 (2)**: a graded ring homomorphism surjective in all sufficiently large degrees
induces a closed immersion on its domain of definition.

Being a closed immersion is local at the target, and over `D₊(f)` the morphism is the map of
affine schemes attached to the surjection `𝒜_{(f)} → ℬ_{(ψ f)}`. -/
@[ega "II 2.9.2" "(i)"]
public theorem isClosedImmersion_mapHom_of_eventually_surjective (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : ∀ᶠ d : ℕ in atTop, Function.Surjective (GradedRingHom.gradedAddHom ψ d)) :
    IsClosedImmersion (mapHom 𝒜 ℬ ψ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hψ
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict fun x => ?_
  obtain ⟨d, f, hd, hf, hfx⟩ := exists_homogeneous_pos_notMem 𝒜 x
  refine ⟨Proj.basicOpen 𝒜 f, (Proj.mem_basicOpen 𝒜 f x).mpr hfx, ?_⟩
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Away.map ψ f))) :=
    IsClosedImmersion.spec_of_surjective _
      (surjective_awayMap_of_eventually_surjective 𝒜 ℬ ψ hN hd hf)
  rw [morphismRestrict_mapHom_eq 𝒜 ℬ ψ hd hf]
  infer_instance

/-- **Stacks 01N1 (2)** on Tag 01MY's bundle: the underlying morphism of
`Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData` is a closed immersion. This is the form
the statements of the chain quantify over, and it is the previous result unchanged, since the
bundle's morphism is `mapHom` by definition. -/
@[stacks 01N1 "part (2): the closed immersion", stacks 01N0 "closed_immersion"]
public theorem isClosedImmersion_projMapData_hom_of_eventually_surjective (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : ∀ᶠ d : ℕ in atTop, Function.Surjective (GradedRingHom.gradedAddHom ψ d)) :
    IsClosedImmersion (ProjTwistCompare.projMapData 𝒜 ℬ ψ).hom := by
  rw [ProjTwistCompare.projMapData_hom 𝒜 ℬ ψ]
  exact isClosedImmersion_mapHom_of_eventually_surjective 𝒜 ℬ ψ hψ

end Stacks.AlgebraicGeometry.RelativeProjChain

end
