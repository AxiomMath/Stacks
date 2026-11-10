module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import StacksFrontier.AlgebraicGeometry.ProjTwistEpi.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistTheta.DegreeSection
public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.EventualSurjective

/-!
# Graded homomorphisms bijective in all large degrees

Let `ψ : 𝒜 →+*ᵍ ℬ` be a homomorphism of nonnegatively graded rings whose map `𝒜 d → ℬ d` on
homogeneous components is bijective for all sufficiently large `d`. This file proves the three
assertions of Stacks 07ZE: the domain of definition `U(ψ)` is all of `Proj ℬ`, the induced
morphism `U(ψ) ⟶ Proj 𝒜` is an isomorphism, and Tag 01MY's comparison map `θ n` on the `n`-th
twist is an isomorphism for every `n : ℤ`.

Only eventual bijectivity is assumed, never generation in degree one; this is what distinguishes
07ZE from Stacks 01N1, whose third assertion
(`Stacks.AlgebraicGeometry.ProjTwistMono.isIso_projMapData_twistMap`) does assume generation in
degree one and is therefore not available here.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjChain.injective_awayMap_of_eventually_bijective` and
  `isIso_ofHom_awayMap_of_eventually_bijective`: the induced map
  `𝒜_{(f)} → ℬ_{(ψ f)}` of degree-zero homogeneous localizations is bijective for every
  homogeneous `f` of positive degree.
* `Stacks.AlgebraicGeometry.RelativeProjChain.mapDomain_eq_top_of_eventually_bijective`:
  **assertion (1)**, `U(ψ) = Proj ℬ`.
* `Stacks.AlgebraicGeometry.RelativeProjChain.isIso_mapHom_of_eventually_bijective` and
  `isIso_projMapData_hom_of_eventually_bijective`: **assertion (2)**, the induced morphism of
  schemes is an isomorphism.
* `Stacks.AlgebraicGeometry.RelativeProjChain.isIso_projMapData_twistMap_of_eventually_bijective`:
  **assertion (3)**, every comparison map on twists is an isomorphism.

## The route

Assertion (1) is Stacks 01N1's first assertion, which needs only eventual surjectivity.

Assertion (2) is local at the target. Over a standard open `D₊(f)` with `f` homogeneous of
positive degree the morphism is, up to canonical isomorphisms, `Spec` of the map
`𝒜_{(f)} → ℬ_{(ψ f)}`
(`Stacks.AlgebraicGeometry.RelativeProjChain.morphismRestrict_mapHom_eq`), so it suffices that
that ring map is bijective. Surjectivity is `surjective_awayMap_of_eventually_surjective`;
injectivity is proved here, by clearing denominators: two fractions `a / f^k` and `b / f^l` with
equal images agree after multiplying by a large power of `f`, and injectivity in the resulting
large degree is the hypothesis.

Assertion (3) combines an epimorphism with a monomorphism. `θ n` is an epimorphism with no
generation hypothesis, by Stacks 01N0
(`Stacks.AlgebraicGeometry.ProjTwistEpi.epi_projMapData_twistMap_of_eventually_surjective`). For
the monomorphism, `θ n` is by construction the inverse adjoint transpose of its adjoint form
`Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap`, whose sections are *concrete*:
over `U` it sends a family of homogeneous fractions `(a_x)` to `(ψ a / ψ s)`. So the monomorphism
is proved on the adjoint form, where it is the statement that a section killed fibrewise by `ψ`
vanishes, and transported across the adjunction by
`Stacks.AlgebraicGeometry.ProjTwistTheta.unit_comp_map_twistMap` — legitimate because assertion
(2) makes the unit of the pullback–pushforward adjunction an isomorphism.

## Implementation notes

The fibrewise vanishing step, `mk_eq_zero_of_map_mk_eq_zero`, is the only place eventual
bijectivity is used for assertion (3), and it is pure commutative algebra: if `ψ m` dies in the
localization of `B` at a homogeneous prime `y`, then some `b ∉ y` kills it, hence so does a
homogeneous component `c` of `b`; multiplying `c` by a power of a positive-degree element omitted
by `y` lifts it to an element `v` of `A` of arbitrarily large degree, which is omitted by the
contracted prime and kills `m` because `ψ (v * m) = 0` in a degree where `ψ` is injective.

Working through the adjoint form, rather than through `θ n` itself, is what keeps this file free
of the tensor-product machinery of Tag 01CD: the alternative — testing `θ n` on global sections
attached to homogeneous elements — needs the comparison between the pullback of a tensor product
and the tensor product of the pullbacks in order to multiply a section by the degree-section of a
denominator, and the multiplicativity of `θ`.

Both rings live in the single universe `u`, forced because `Proj ℬ ⟶ Proj 𝒜` must be a morphism
of `Scheme.{u}`; the two `SetLike` carriers are independent.

## References

* [Stacks Project, Tag 07ZE](https://stacks.math.columbia.edu/tag/07ZE)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N0](https://stacks.math.columbia.edu/tag/01N0)
* [Stacks Project, Tag 01N1](https://stacks.math.columbia.edu/tag/01N1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousLocalization TopologicalSpace CategoryTheory Filter Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare Stacks.AlgebraicGeometry.ProjTwistTheta

namespace Stacks.AlgebraicGeometry.RelativeProjChain

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u w w'

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-! ### The maps of degree-zero homogeneous localizations -/

/-- **A graded homomorphism bijective in all large degrees is injective on degree-zero
homogeneous localizations.** Two fractions with the same denominator `f^•` and equal images are
equal after multiplying numerators by a power of `f` large enough that the hypothesis applies in
the resulting degree. -/
public theorem injective_awayMap_of_eventually_bijective (ψ : 𝒜 →+*ᵍ ℬ) {N : ℕ}
    (hN : ∀ d, N ≤ d → Function.Bijective (GradedRingHom.gradedAddHom ψ d))
    {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) :
    Function.Injective (Away.map ψ f) := by
  intro x y hxy
  obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf x
  obtain ⟨l, b, hb, rfl⟩ := Away.mk_surjective 𝒜 hf y
  apply HomogeneousLocalization.val_injective
  have hval := congrArg HomogeneousLocalization.val hxy
  simp only [Away.map_mk, Away.val_mk] at hval
  rw [Localization.mk_eq_mk'] at hval
  obtain ⟨c, hc⟩ := (IsLocalization.eq (S := Localization.Away (ψ f))).mp hval
  obtain ⟨j, hj⟩ := c.2
  rw [← hj] at hc
  have hone : 1 ≤ d := hd
  have hm : N ≤ (j + N + l + k) * d := by nlinarith
  have hmem : ∀ p q : ℕ, ∀ c : A, c ∈ 𝒜 (p * d) →
      f ^ (j + N) * (f ^ q * c) ∈ 𝒜 ((j + N + q + p) * d) := fun p q c hc => by
    simpa [nsmul_eq_mul, Nat.add_mul, add_assoc, add_comm, add_left_comm, mul_assoc] using
      SetLike.mul_mem_graded (SetLike.pow_mem_graded (j + N) hf)
        (SetLike.mul_mem_graded (SetLike.pow_mem_graded q hf) hc)
  have hu := hmem k l a ha
  have hv := hmem l k b hb
  have himg : ψ (f ^ (j + N) * (f ^ l * a)) = ψ (f ^ (j + N) * (f ^ k * b)) := by
    simpa [map_mul, pow_add, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun z : B => (ψ f) ^ N * z) hc
  have hsub : (⟨f ^ (j + N) * (f ^ l * a), hu⟩ : 𝒜 ((j + N + l + k) * d)) =
      ⟨f ^ (j + N) * (f ^ k * b), by rwa [add_right_comm]⟩ :=
    (hN _ hm).injective (Subtype.ext himg)
  let pk : Submonoid.powers f := ⟨f ^ k, ⟨k, rfl⟩⟩
  let pl : Submonoid.powers f := ⟨f ^ l, ⟨l, rfl⟩⟩
  have hloc : Localization.mk a pk = Localization.mk b pl := by
    rw [Localization.mk_eq_mk']
    refine (IsLocalization.eq (S := Localization.Away f)).2 ⟨⟨f ^ (j + N), j + N, rfl⟩, ?_⟩
    simpa [pk, pl, mul_assoc, mul_left_comm, mul_comm] using congrArg Subtype.val hsub
  simpa [Away.val_mk, pk, pl] using hloc

/-- **The map of degree-zero homogeneous localizations is an isomorphism of rings** when `ψ` is
bijective in all large degrees and `f` is homogeneous of positive degree. -/
public theorem isIso_ofHom_awayMap_of_eventually_bijective (ψ : 𝒜 →+*ᵍ ℬ) {N : ℕ}
    (hN : ∀ d, N ≤ d → Function.Bijective (GradedRingHom.gradedAddHom ψ d))
    {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) :
    IsIso (CommRingCat.ofHom (Away.map ψ f)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨injective_awayMap_of_eventually_bijective 𝒜 ℬ ψ hN hd hf,
    surjective_awayMap_of_eventually_surjective 𝒜 ℬ ψ
      (fun e he => (hN e he).surjective) hd hf⟩

/-! ### Assertion (1): the domain of definition is everything -/

omit [GradedRing 𝒜] in
/-- **Stacks 07ZE (1)**: a graded homomorphism bijective in all large degrees is defined on all
of `Proj ℬ`. Only surjectivity is used, so this is Stacks 01N1's first assertion. -/
@[stacks 07ZE "part (1), the domain is all of Proj B"]
public theorem mapDomain_eq_top_of_eventually_bijective (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : ∀ᶠ d : ℕ in atTop, Function.Bijective (GradedRingHom.gradedAddHom ψ d)) :
    mapDomain 𝒜 ℬ ψ = ⊤ :=
  mapDomain_eq_top_of_eventually_surjective 𝒜 ℬ ψ (hψ.mono fun _ h => h.surjective)

/-! ### Assertion (2): the induced morphism of schemes is an isomorphism -/

/-- **Stacks 07ZE (2)**: a graded homomorphism bijective in all large degrees induces an
isomorphism `U(ψ) ⟶ Proj 𝒜`.

Being an isomorphism is local at the target, and over the standard open `D₊(f)` the morphism is
`Spec` of the isomorphism `𝒜_{(f)} → ℬ_{(ψ f)}` up to canonical isomorphisms. -/
public theorem isIso_mapHom_of_eventually_bijective (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : ∀ᶠ d : ℕ in atTop, Function.Bijective (GradedRingHom.gradedAddHom ψ d)) :
    IsIso (mapHom 𝒜 ℬ ψ) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hψ
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := MorphismProperty.isomorphisms Scheme) fun x => ?_
  obtain ⟨d, f, hd, hf, hfx⟩ := exists_homogeneous_pos_notMem 𝒜 x
  refine ⟨Proj.basicOpen 𝒜 f, (Proj.mem_basicOpen 𝒜 f x).mpr hfx, ?_⟩
  have : IsIso (CommRingCat.ofHom (Away.map ψ f)) :=
    isIso_ofHom_awayMap_of_eventually_bijective 𝒜 ℬ ψ hN hd hf
  rw [MorphismProperty.isomorphisms.iff, morphismRestrict_mapHom_eq 𝒜 ℬ ψ hd hf]
  infer_instance

/-- **Stacks 07ZE (2)** on Tag 01MY's bundle: the underlying morphism of
`Stacks.AlgebraicGeometry.ProjTwistCompare.projMapData` is an isomorphism. This is the form the
statements of the chain quantify over, and it is the previous result unchanged, since the bundle's
morphism is `mapHom` by definition. -/
@[stacks 07ZE "part (2), the projective-spectrum morphism is an isomorphism"]
public theorem isIso_projMapData_hom_of_eventually_bijective (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : ∀ᶠ d : ℕ in atTop, Function.Bijective (GradedRingHom.gradedAddHom ψ d)) :
    IsIso (ProjTwistCompare.projMapData 𝒜 ℬ ψ).hom := by
  rw [ProjTwistCompare.projMapData_hom 𝒜 ℬ ψ]
  exact isIso_mapHom_of_eventually_bijective 𝒜 ℬ ψ hψ

/-! ### Fractions with denominator one -/

section Fractions

variable {R : Type*} [CommRing R] {S : Submonoid R}

/-- A fraction of a commutative ring vanishes exactly when some element of the submonoid kills
its numerator; in particular whether it vanishes does not depend on the denominator. -/
public theorem mk_eq_zero_iff_exists_mul_eq_zero (m : R) (s : S) :
    LocalizedModule.mk m s = (0 : LocalizedModule S R) ↔ ∃ u : S, (u : R) * m = 0 := by
  rw [show (0 : LocalizedModule S R) = LocalizedModule.mk 0 s from
    (LocalizedModule.zero_mk s).symm, LocalizedModule.mk_eq]
  simp only [Submonoid.smul_def, smul_eq_mul, smul_zero]
  refine ⟨fun ⟨u, hu⟩ => ⟨u * s, ?_⟩, fun ⟨u, hu⟩ => ⟨u, ?_⟩⟩
  · rwa [Submonoid.coe_mul, mul_assoc]
  · rw [mul_left_comm, hu, mul_zero]

/-- A fraction that vanishes also vanishes after its denominator is cleared. -/
public theorem mk_one_eq_zero_of_mk_eq_zero (m : R) (s : S)
    (h : LocalizedModule.mk m s = (0 : LocalizedModule S R)) :
    LocalizedModule.mk m (1 : S) = 0 :=
  (mk_eq_zero_iff_exists_mul_eq_zero m 1).mpr
    ((mk_eq_zero_iff_exists_mul_eq_zero m s).mp h)

/-- A numerator that vanishes with denominator one vanishes with any denominator. -/
public theorem mk_eq_zero_of_mk_one_eq_zero (m : R) (s : S)
    (h : LocalizedModule.mk m (1 : S) = (0 : LocalizedModule S R)) :
    LocalizedModule.mk m s = 0 :=
  (mk_eq_zero_iff_exists_mul_eq_zero m s).mpr
    ((mk_eq_zero_iff_exists_mul_eq_zero m 1).mp h)

end Fractions

/-! ### The fibrewise vanishing step -/

/-- **A homogeneous element killed by `ψ` in a fibre of `Proj ℬ` is killed in the corresponding
fibre of `Proj 𝒜`**, when `ψ` is bijective in all large degrees and the homogeneous prime at the
point of `Proj 𝒜` is the `ψ`-contraction of the one at the point of `Proj ℬ`.

Some `b ∉ y` kills `ψ m`, hence so does one of its homogeneous components `c`. Multiplying `c` by
a high power of a positive-degree element omitted by `y` puts it in a degree where `ψ` is
bijective, so it lifts to `v ∈ A`; that `v` is omitted by `x`, and `ψ (v * m) = 0` in a degree
where `ψ` is injective, so `v * m = 0`. -/
public theorem mk_eq_zero_of_map_mk_eq_zero (ψ : 𝒜 →+*ᵍ ℬ) {N : ℕ}
    (hN : ∀ d, N ≤ d → Function.Bijective (GradedRingHom.gradedAddHom ψ d))
    (x : ProjectiveSpectrum 𝒜) (y : ProjectiveSpectrum ℬ)
    (hxy : x.asHomogeneousIdeal = y.asHomogeneousIdeal.comap ψ)
    {m : A} {k : ℕ} (hm : m ∈ 𝒜 k)
    (hz : LocalizedModule.mk (ψ m) (1 : y.asHomogeneousIdeal.toIdeal.primeCompl) = 0) :
    LocalizedModule.mk m (1 : x.asHomogeneousIdeal.toIdeal.primeCompl) = 0 := by
  classical
  have hmem : ∀ a : A, a ∈ x.asHomogeneousIdeal ↔ ψ a ∈ y.asHomogeneousIdeal := by
    intro a
    rw [hxy]
    rfl
  obtain ⟨d, f, hd, hf, hfx⟩ := exists_homogeneous_pos_notMem 𝒜 x
  have hfy : ψ f ∉ y.asHomogeneousIdeal := fun h => hfx ((hmem f).mpr h)
  obtain ⟨b, hb0⟩ := (mk_eq_zero_iff_exists_mul_eq_zero _ _).mp hz
  obtain ⟨e, he⟩ : ∃ e : ℕ, (DirectSum.decompose ℬ (b : B) e : B) ∉ y.asHomogeneousIdeal := by
    by_contra! h
    exact b.2 (y.asHomogeneousIdeal.isHomogeneous.mem_iff.mpr h)
  have hc0 : ((DirectSum.decompose ℬ (b : B) e : ℬ e) : B) * ψ m = 0 :=
    (DirectSum.coe_decompose_mul_add_of_right_mem ℬ (i := e) (a := (b : B))
      (ψ.map_mem hm)).symm.trans
      ((congrArg (fun z : B => (DirectSum.decompose ℬ z (e + k) : B)) hb0).trans (by simp))
  have hl : N ≤ e + (N + 1) * d := by nlinarith
  have hc : ((DirectSum.decompose ℬ (b : B) e : ℬ e) : B) * ψ f ^ (N + 1) ∈
      ℬ (e + (N + 1) * d) :=
    SetLike.mul_mem_graded (DirectSum.decompose ℬ (b : B) e).2
      (SetLike.pow_mem_graded (N + 1) (ψ.map_mem hf))
  obtain ⟨v, hv⟩ := (hN _ hl).surjective ⟨_, hc⟩
  have hv' : ψ (v : A) = ((DirectSum.decompose ℬ (b : B) e : ℬ e) : B) * ψ f ^ (N + 1) :=
    congrArg Subtype.val hv
  have hvx : (v : A) ∉ x.asHomogeneousIdeal := by
    intro h
    have hvy := (hmem v).mp h
    rw [hv'] at hvy
    exact (y.isPrime.mem_or_mem hvy).elim he
      (fun h => hfy (y.isPrime.mem_of_pow_mem _ h))
  have hva : (v : A) * m = 0 := by
    have hmul : (v : A) * m ∈ 𝒜 (e + (N + 1) * d + k) := SetLike.mul_mem_graded v.2 hm
    have hmap : ψ ((v : A) * m) = 0 := by
      rw [map_mul, hv', mul_right_comm, hc0, zero_mul]
    exact congrArg Subtype.val ((hN _ (by omega)).injective (a₁ := ⟨_, hmul⟩)
      (a₂ := ⟨0, zero_mem _⟩) (Subtype.ext (by simpa using hmap)))
  exact (mk_eq_zero_iff_exists_mul_eq_zero _ _).mpr ⟨⟨v, hvx⟩, hva⟩

/-! ### Assertion (3): the comparison maps on twists -/

/-- The unit of the pullback–pushforward adjunction at an isomorphism of schemes is an
isomorphism. Over an open `V` the unit of the *restriction* adjunction is restriction along
`f ''ᵁ (f ⁻¹ᵁ V) ⟶ V`, which is an identity when `f` is surjective; the pullback unit is that one
composed with the comparison of restriction and pullback. -/
public theorem isIso_pullbackPushforwardAdjunction_unit_app {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] (M : Y.Modules) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  have hsurj : Function.Surjective f.base :=
    (ConcreteCategory.bijective_of_isIso f.base).surjective
  have : IsIso ((Scheme.Modules.restrictAdjunction f).unit.app M) := by
    rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro V
    rw [Scheme.Modules.restrictAdjunction_unit_app_app]
    have hv : f ''ᵁ (f ⁻¹ᵁ V) = V := by
      ext z
      refine ⟨fun hz => ?_, fun hz => ?_⟩
      · obtain ⟨w, hw, rfl⟩ := hz
        exact hw
      · obtain ⟨w, rfl⟩ := hsurj z
        exact ⟨w, hz, rfl⟩
    have : IsIso (homOfLE (f.image_preimage_le V) : f ''ᵁ (f ⁻¹ᵁ V) ⟶ V) :=
      homOfLE_isIso_of_eq _ hv
    exact Functor.map_isIso M.presheaf (homOfLE (f.image_preimage_le V)).op
  rw [← restrictUnit_comp_map_restrictFunctorIsoPullback f M]
  infer_instance

/-- **The adjoint form of the comparison map on twists is injective on sections** when `ψ` is
bijective in all large degrees and the induced morphism of schemes is surjective.

A section of `𝒪_{Proj 𝒜}(n)` is locally a homogeneous fraction `m / s`, and the comparison sends
it to `ψ m / ψ s`. Surjectivity provides, above each point `x` of `Proj 𝒜`, a point of `U(ψ)` at
which the comparison may be read, so the hypothesis gives `ψ m / ψ s = 0` there; clearing
denominators and applying `mk_eq_zero_of_map_mk_eq_zero` makes `m / s` vanish at `x`. -/
public theorem eq_zero_of_fibreMap_eq_zero (ψ : 𝒜 →+*ᵍ ℬ) {N : ℕ}
    (hN : ∀ d, N ≤ d → Function.Bijective (GradedRingHom.gradedAddHom ψ d))
    (n : ℤ) (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (a : (twistingSheaf 𝒜 n).val.obj (op U)) (x : ↥(unop (op U)))
    {y : ProjectiveSpectrum ℬ}
    (hxy : (x.1 : ProjectiveSpectrum 𝒜).asHomogeneousIdeal = y.asHomogeneousIdeal.comap ψ)
    (hval : fibreMap 𝒜 ℬ ψ x.1 y hxy (a.1 x) = 0) :
    a.1 x = 0 := by
  obtain ⟨V, hxV, i, k, m, s, hm, hs, hns, heq⟩ := a.2 x
  have hsx : s ∉ (x.1 : ProjectiveSpectrum 𝒜).asHomogeneousIdeal := hns ⟨x.1, hxV⟩
  have hax : a.1 x = LocalizedModule.mk m ⟨s, hsx⟩ := heq ⟨x.1, hxV⟩
  have hψs : ψ s ∉ y.asHomogeneousIdeal := fun h => hsx (by rwa [hxy])
  have hψvanish := (fibreMap_mk 𝒜 ℬ ψ x.1 y hxy m s hsx hψs).symm.trans
    ((congrArg (fibreMap 𝒜 ℬ ψ x.1 y hxy) hax).symm.trans hval)
  refine hax.trans ?_
  by_cases hk : 0 ≤ (k : ℤ) + n
  · have hmk : m ∈ 𝒜 ((k : ℤ) + n).toNat := by
      simpa [twistGrading, integerGrading, hk] using hm
    exact mk_eq_zero_of_mk_one_eq_zero m ⟨s, hsx⟩
      (mk_eq_zero_of_map_mk_eq_zero 𝒜 ℬ ψ hN x.1 y hxy hmk
        (mk_one_eq_zero_of_mk_eq_zero (ψ m) ⟨ψ s, hψs⟩ hψvanish))
  · rw [show m = 0 by simpa [twistGrading, integerGrading, hk] using hm, LocalizedModule.zero_mk]

/-- **The adjoint form of the comparison map on twists has trivial kernel on sections** when `ψ`
is bijective in all large degrees and the induced morphism of schemes is surjective: surjectivity
puts every point of `Proj 𝒜` in the image, where `eq_zero_of_fibreMap_eq_zero` applies. -/
public theorem eq_zero_of_twistPushforwardMap_app_eq_zero (ψ : 𝒜 →+*ᵍ ℬ) {N : ℕ}
    (hN : ∀ d, N ≤ d → Function.Bijective (GradedRingHom.gradedAddHom ψ d))
    (hsurj : Function.Surjective (mapHom 𝒜 ℬ ψ).base)
    (n : ℤ) (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (a : (twistingSheaf 𝒜 n).val.obj (op U))
    (ha : ((twistPushforwardMap 𝒜 ℬ ψ n).val.app (op U)).hom' a = 0) : a = 0 := by
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨z₀, hz₀⟩ := hsurj x.1
  have hzU : z₀ ∈ mapHom 𝒜 ℬ ψ ⁻¹ᵁ U := by
    change (mapHom 𝒜 ℬ ψ).base z₀ ∈ U
    rw [hz₀]
    exact x.2
  set zz : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U)) :=
    ⟨z₀.1, mem_image_of_mem 𝒜 ℬ ψ z₀ hzU⟩
  have hval : twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ zz)
      (a.1 ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ zz), liftPt_mem 𝒜 ℬ ψ zz⟩) = 0 :=
    (twistPushforwardMap_app_val 𝒜 ℬ ψ n (op U) a zz).symm.trans
      (congrArg (fun t : (twistingSheaf ℬ n).val.obj
        (op ((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))) => t.1 zz) ha)
  have hpt : (⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ zz), liftPt_mem 𝒜 ℬ ψ zz⟩ :
      ↥(unop (op U))) = x := Subtype.ext hz₀
  rw [← hpt]
  exact eq_zero_of_fibreMap_eq_zero 𝒜 ℬ ψ hN n U a
    ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ zz), liftPt_mem 𝒜 ℬ ψ zz⟩
    (basePoint_asHomogeneousIdeal 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ zz)) hval

/-- **Stacks 07ZE (3)**: a graded homomorphism bijective in all large degrees makes Tag 01MY's
comparison map on the `n`-th twist an isomorphism, for every `n : ℤ`.

The map is an epimorphism by Stacks 01N0, and a monomorphism because its adjoint form is
injective on sections and the unit of the adjunction is an isomorphism by assertion (2). -/
@[stacks 07ZE "part (3), the maps on twists are isomorphisms"]
public theorem isIso_projMapData_twistMap_of_eventually_bijective (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : ∀ᶠ d : ℕ in atTop, Function.Bijective (GradedRingHom.gradedAddHom ψ d))
    (n : ℤ) :
    IsIso ((ProjTwistCompare.projMapData 𝒜 ℬ ψ).twistMap n) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hψ
  have hepi : Epi (twistMap 𝒜 ℬ ψ n) :=
    ProjTwistEpi.epi_twistMap_of_eventually_surjective 𝒜 ℬ ψ
      (hψ.mono fun _ h => h.surjective) n
  have hhom : IsIso (mapHom 𝒜 ℬ ψ) := isIso_mapHom_of_eventually_bijective 𝒜 ℬ ψ hψ
  have hsurj : Function.Surjective (mapHom 𝒜 ℬ ψ).base :=
    (ConcreteCategory.bijective_of_isIso (mapHom 𝒜 ℬ ψ).base).surjective
  have hmonoAdj : Mono (twistPushforwardMap 𝒜 ℬ ψ n) := by
    apply (SheafOfModules.forget _).mono_of_mono_map
    apply PresheafOfModules.mono_of_injective
    intro W p q hpq
    have hz : ((twistPushforwardMap 𝒜 ℬ ψ n).val.app W).hom' (p - q) = 0 :=
      (map_sub ((twistPushforwardMap 𝒜 ℬ ψ n).val.app W).hom' p q).trans
        (sub_eq_zero.mpr hpq)
    exact sub_eq_zero.mp (eq_zero_of_twistPushforwardMap_app_eq_zero 𝒜 ℬ ψ hN hsurj n W.unop
      (p - q) hz)
  have hunit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).unit.app
      (twistingSheaf 𝒜 n)) :=
    isIso_pullbackPushforwardAdjunction_unit_app (mapHom 𝒜 ℬ ψ) (twistingSheaf 𝒜 n)
  have hmonoComp : Mono ((Scheme.Modules.pullbackPushforwardAdjunction (mapHom 𝒜 ℬ ψ)).unit.app
      (twistingSheaf 𝒜 n) ≫
        (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).map (twistMap 𝒜 ℬ ψ n)) := by
    have hisoApp : IsIso ((Scheme.Modules.restrictFunctorIsoPullback
        (mapDomain 𝒜 ℬ ψ).ι).hom.app (twistingSheaf ℬ n)) :=
      ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).app
        (twistingSheaf ℬ n)).isIso_hom
    have hisoPush : IsIso ((Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).map
        ((Scheme.Modules.restrictFunctorIsoPullback (mapDomain 𝒜 ℬ ψ).ι).hom.app
          (twistingSheaf ℬ n))) :=
      Functor.map_isIso _ _
    rw [unit_comp_map_twistMap 𝒜 ℬ ψ n]
    exact mono_comp' hmonoAdj (IsIso.mono_of_iso _)
  have : Mono (twistMap 𝒜 ℬ ψ n) :=
    (Scheme.Modules.pushforward (mapHom 𝒜 ℬ ψ)).mono_of_mono_map
      ((mono_comp_iff_of_isIso _ _).mp hmonoComp)
  rw [ProjTwistCompare.projMapData_twistMap 𝒜 ℬ ψ n]
  exact isIso_of_mono_of_epi (twistMap 𝒜 ℬ ψ n)

end Stacks.AlgebraicGeometry.RelativeProjChain

end
