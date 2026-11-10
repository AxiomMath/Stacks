module

public import StacksFrontier.AlgebraicGeometry.Curves.RelativeCurveEtaleDivisor
public import StacksFrontier.RingTheory.Etale.SeparatingDivisorFibre
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# The étale divisor of a family of smooth curves, as a closed subscheme over opens of the base

Let `g : U ⟶ W` be smooth of relative dimension one and affine, with `W` integral and locally
noetherian over a field of characteristic `p`. The étale divisor of
`AlgebraicGeometry.exists_etale_divisor_of_smoothOfRelativeDimension_one` on a chart
`W₀ = Spec A`, `g⁻¹ W₀ = Spec B` (`a ≠ 0` in `A`, `t ∈ B`, `h ∈ A[X]` monic of positive degree,
`B_a ⧸ (h(t))` finite étale over `A_a`, every element of `B` times a power of `a` integral over
`A[X]` through `t`) is the closed subscheme `Z = Spec (B_a ⧸ (h(t)))` of `U_a = g⁻¹ W_a`,
`W_a = D(a)`, with underlying set `S ⊆ U`.

Over every open `V' ⊆ W_a`, with `g' : U' ⟶ V'` the base change of `g`, its base change
`Z' ⊆ U'` is a closed subscheme with `Z' = V(f')` for a function `f'` on `U'` (the restriction of
`h(t)`), finite étale over `V'` (a base change of `Spec (B_a ⧸ (h(t))) ⟶ Spec A_a`), and it meets
every irreducible component with two points of every geometric fibre `U'_w̄` of `g'`: such a
component is `V(P)` for a prime `P` of `Ω ⊗_A B` with `dim (Ω ⊗_A B) ⧸ P ≥ 1`, and `Ω ⊗_A B` is
finite over `Ω[X]` through `1 ⊗ t` (`a` is a unit in `Ω`), so some prime `Q ⊇ P` contains
`1 ⊗ h(t)` (`Polynomial.exists_isPrime_le_one_tmul_aeval_mem`). The fibres of `S ⟶ W` are finite.

This is the divisor along which the Gysin map of `R² g_!` is taken in the reduction of the weight
bound of Weil II ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `AlgebraicGeometry.exists_etale_divisor_pullback_of_smoothOfRelativeDimension_one`.
-/

public section

open CategoryTheory CategoryTheory.Limits Polynomial TensorProduct

universe u

namespace AlgebraicGeometry

/-- A point of an affine chart `Spec B ⟶ U` over which a basic open `Spec B_s ⟶ U` sits, lying in
`D(s)` and in `V(r)`, is the image of a point of `V(r|_{D(s)}) ⊆ Spec B_s`. -/
private lemma mem_image_zeroLocus_of_fromSpec {U : Scheme.{u}} {U₀ : U.Opens}
    (hU₀ : IsAffineOpen U₀) (s r : Γ(U, U₀)) (Q : Spec Γ(U, U₀)) (hr : r ∈ Q.asIdeal)
    (hQ : hU₀.fromSpec.base Q ∈ U.basicOpen s) :
    hU₀.fromSpec.base Q ∈ (hU₀.basicOpen s).fromSpec.base ''
      PrimeSpectrum.zeroLocus {algebraMap Γ(U, U₀) Γ(U, U.basicOpen s) r} := by
  have hQ' : hU₀.fromSpec.base Q ∈ Set.range (hU₀.basicOpen s).fromSpec.base := by
    rwa [(hU₀.basicOpen s).range_fromSpec]
  obtain ⟨Q₁, hQ₁⟩ := hQ'
  refine ⟨Q₁, ?_, hQ₁⟩
  have hmap := hU₀.map_fromSpec (hU₀.basicOpen s) (homOfLE (U.basicOpen_le s)).op
  have hinj : PrimeSpectrum.comap (algebraMap Γ(U, U₀) Γ(U, U.basicOpen s)) Q₁ = Q := by
    apply hU₀.fromSpec.isOpenEmbedding.injective
    rw [← hQ₁, ← hmap]
    rfl
  exact Set.singleton_subset_iff.mpr
    (hinj ▸ hr : r ∈ (PrimeSpectrum.comap (algebraMap Γ(U, U₀) Γ(U, U.basicOpen s)) Q₁).asIdeal)

/-- A pullback square over `g` factors through a pullback chart square of `g` along monos. -/
private lemma isPullback_of_lift_chart {X Y U W U' V' : Scheme.{u}} {gs : X ⟶ Y} {fU : X ⟶ U}
    {fW : Y ⟶ W} {g : U ⟶ W} [Mono fW] (hchart : IsPullback gs fU fW g) {jU : U' ⟶ U}
    {jV : V' ⟶ W} {g' : U' ⟶ V'} (hpb : IsPullback jU g' g jV) {jUs : U' ⟶ X} {jVs : V' ⟶ Y}
    (hjU : jUs ≫ fU = jU) (hjV : jVs ≫ fW = jV) : IsPullback jUs g' gs jVs := by
  refine IsPullback.of_right (by rwa [hjU, hjV]) ?_ hchart.flip
  rw [← cancel_mono fW, Category.assoc, Category.assoc, hjV, hchart.w, ← Category.assoc, hjU,
    hpb.w]

/-- **The étale divisor of a family of smooth curves over the opens of the base.** For
`g : U ⟶ W` smooth of relative dimension one and affine, `W` integral and locally noetherian over
a field of characteristic `p`, and a point `u` of `U`, there are a nonempty open `W_a ⊆ W` and a
set `S ⊆ U` with finite fibres over `W` such that over every open `V' ⊆ W_a`, with `g' : U' ⟶ V'`
the base change of `g`, there are a closed immersion `i' : Z' ⟶ U'` with image the preimage of `S`
and the zero locus of a function `f'` on `U'`, `i' ≫ g'` finite étale, and `Z'` meeting every
irreducible component with two points of every geometric fibre of `g'`. -/
theorem exists_etale_divisor_pullback_of_smoothOfRelativeDimension_one {U W : Scheme.{u}}
    (g : U ⟶ W) [SmoothOfRelativeDimension 1 g] [IsAffineHom g] [LocallyOfFiniteType g]
    [IsLocallyNoetherian W] [IsIntegral W] (k : Type u) [Field k] (p : ℕ) [Fact p.Prime]
    [CharP k p] (fW : W ⟶ Spec (.of k)) (u : U) :
    ∃ (Wa : W.Opens) (S : Set U), (Wa : Set W).Nonempty ∧
      (∀ w : W, {z | z ∈ S ∧ g.base z = w}.Finite) ∧
      ∀ {V' U' : Scheme.{u}} (jV : V' ⟶ W) (jU : U' ⟶ U) (g' : U' ⟶ V') [IsOpenImmersion jV],
        Set.range jV.base ⊆ Wa → IsPullback jU g' g jV →
        ∃ (Z' : Scheme.{u}) (i' : Z' ⟶ U') (f : Γ(U', ⊤)), IsClosedImmersion i' ∧
          IsFinite (i' ≫ g') ∧ Etale (i' ≫ g') ∧
          Set.range i'.base = U'.zeroLocus {f} ∧ Set.range i'.base = jU.base ⁻¹' S ∧
          ∀ (Ω : Type u) [Field Ω] (w : Spec (.of Ω) ⟶ V') (C : Set (pullback g' w : Scheme.{u})),
            C ∈ irreducibleComponents _ → (∃ x ∈ C, ∃ y ∈ C, x ≠ y) →
            (C ∩ (pullback.fst g' w).base ⁻¹' Set.range i'.base).Nonempty := by
  classical
  obtain ⟨W₀, -, a, t, h, ha, hmon, hdeg, hint, hEt⟩ :=
    exists_etale_divisor_of_smoothOfRelativeDimension_one g k p fW u
  let : Algebra Γ(W, W₀) Γ(U, g ⁻¹ᵁ W₀) := (g.appLE W₀ (g ⁻¹ᵁ W₀) le_rfl).hom.toAlgebra
  have hW₀ : IsAffineOpen (W₀ : W.Opens) := W₀.2
  have hU₀ : IsAffineOpen (g ⁻¹ᵁ W₀) := hW₀.preimage g
  have : Algebra.FiniteType Γ(W, W₀) Γ(U, g ⁻¹ᵁ W₀) :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) g inferInstance W₀
      ⟨g ⁻¹ᵁ W₀, hU₀⟩ le_rfl
  -- the basic opens `W_a = D(a)` and `U_a = g⁻¹ W_a = D(a|_{g⁻¹ W₀})`
  set s : Γ(U, g ⁻¹ᵁ W₀) := algebraMap Γ(W, W₀) Γ(U, g ⁻¹ᵁ W₀) a with hs
  set Wa : W.Opens := W.basicOpen a with hWa_def
  set Ua : U.Opens := U.basicOpen s with hUa_def
  have hWa : IsAffineOpen Wa := hW₀.basicOpen a
  have hUa : IsAffineOpen Ua := hU₀.basicOpen s
  have hpre : g ⁻¹ᵁ Wa = Ua := by
    rw [hWa_def, Scheme.preimage_basicOpen, hUa_def, hs, Scheme.Hom.app_eq_appLE]
    rfl
  have hle : Ua ≤ g ⁻¹ᵁ Wa := hpre.ge
  have : IsLocalization.Away a Γ(W, Wa) := hW₀.isLocalization_basicOpen a
  have : IsLocalization (Algebra.algebraMapSubmonoid Γ(U, g ⁻¹ᵁ W₀) (Submonoid.powers a))
      Γ(U, Ua) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact hU₀.isLocalization_basicOpen s
  let : Algebra Γ(W, Wa) Γ(U, Ua) := (g.appLE Wa Ua hle).hom.toAlgebra
  let : Algebra Γ(W, W₀) Γ(U, Ua) :=
    ((algebraMap Γ(U, g ⁻¹ᵁ W₀) Γ(U, Ua)).comp (algebraMap Γ(W, W₀) Γ(U, g ⁻¹ᵁ W₀))).toAlgebra
  have : IsScalarTower Γ(W, W₀) Γ(U, g ⁻¹ᵁ W₀) Γ(U, Ua) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Γ(W, W₀) Γ(W, Wa) Γ(U, Ua) := IsScalarTower.of_algebraMap_eq fun x => by
    change _ = (g.appLE Wa Ua hle).hom ((W.presheaf.map (homOfLE (W.basicOpen_le a)).op).hom x)
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
    change (U.presheaf.map (homOfLE (U.basicOpen_le s)).op).hom
      ((g.appLE W₀ (g ⁻¹ᵁ W₀) le_rfl).hom x) = _
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  obtain ⟨hEt', hFin'⟩ := hEt Γ(W, Wa) Γ(U, Ua)
  -- the divisor `Z = Spec (B_a ⧸ (h(t)))`
  set r : Γ(U, g ⁻¹ᵁ W₀) := aeval t h with hr_def
  set I : Ideal Γ(U, Ua) := Ideal.span {algebraMap Γ(U, g ⁻¹ᵁ W₀) Γ(U, Ua) r} with hI
  let iZs : Spec (.of (Γ(U, Ua) ⧸ I)) ⟶ Spec Γ(U, Ua) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let gs : Spec Γ(U, Ua) ⟶ Spec Γ(W, Wa) := Spec.map (g.appLE Wa Ua hle)
  have hπs : iZs ≫ gs = Spec.map (CommRingCat.ofHom (algebraMap Γ(W, Wa) (Γ(U, Ua) ⧸ I))) := by
    rw [← Spec.map_comp]
    rfl
  have hπfin : IsFinite (iZs ≫ gs) := by
    rw [hπs, IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr hFin'
  have hπet : Etale (iZs ≫ gs) := by
    rw [hπs, HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr hEt'
  -- the chart square over `W_a`
  have hchart : IsPullback gs hUa.fromSpec hWa.fromSpec g :=
    IsOpenImmersion.isPullback gs hUa.fromSpec hWa.fromSpec g
      (IsAffineOpen.SpecMap_appLE_fromSpec g hWa hUa hle).symm
      (by rw [hWa.opensRange_fromSpec, hUa.opensRange_fromSpec, hpre])
  -- the chart square over `W₀`
  let g₀ : Spec Γ(U, g ⁻¹ᵁ W₀) ⟶ Spec Γ(W, W₀) := Spec.map (g.appLE W₀ (g ⁻¹ᵁ W₀) le_rfl)
  have hchart₀ : IsPullback g₀ hU₀.fromSpec hW₀.fromSpec g :=
    IsOpenImmersion.isPullback g₀ hU₀.fromSpec hW₀.fromSpec g
      (IsAffineOpen.SpecMap_appLE_fromSpec g hW₀ hU₀ le_rfl).symm
      (by rw [hW₀.opensRange_fromSpec, hU₀.opensRange_fromSpec])
  -- the set `S`
  set tq : Γ(U, Ua) := algebraMap Γ(U, g ⁻¹ᵁ W₀) Γ(U, Ua) r with htq
  have hZ0 : Set.range iZs.base = PrimeSpectrum.zeroLocus {tq} := by
    change Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I)) = _
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, hI, PrimeSpectrum.zeroLocus_span]
  let S : Set U := hUa.fromSpec.base '' PrimeSpectrum.zeroLocus {tq}
  refine ⟨Wa, S, ?_, ?_, ?_⟩
  · -- `W_a` is nonempty since `a ≠ 0` and `W` is integral
    exact Set.nonempty_iff_ne_empty.mpr fun hne =>
      ha ((basicOpen_eq_bot_iff a).mp (SetLike.coe_injective hne))
  · -- finite fibres
    intro w
    have hfin : ((iZs ≫ gs).base ⁻¹' (hWa.fromSpec.base ⁻¹' {w})).Finite :=
      (iZs ≫ gs).finite_preimage
        ((Set.finite_singleton w).preimage hWa.fromSpec.isOpenEmbedding.injective.injOn)
    refine (hfin.image (iZs ≫ hUa.fromSpec).base).subset ?_
    rintro _ ⟨⟨_, hq, rfl⟩, hw⟩
    rw [← hZ0] at hq
    obtain ⟨q, rfl⟩ := hq
    refine ⟨q, ?_, rfl⟩
    change hWa.fromSpec.base (gs.base (iZs.base q)) = w
    rw [← hw]
    change (iZs ≫ gs ≫ hWa.fromSpec).base q = (iZs ≫ hUa.fromSpec ≫ g).base q
    rw [hchart.w]
  intro V' U' jV jU g' _ hrange hpb
  have : IsOpenImmersion jU := MorphismProperty.of_isPullback hpb.flip inferInstance
  have hrangeU : Set.range jU.base ⊆ Ua := by
    rintro _ ⟨y, rfl⟩
    rw [← hpre]
    change g.base (jU.base y) ∈ Wa
    rw [← Scheme.Hom.comp_apply, hpb.w, Scheme.Hom.comp_apply]
    exact hrange ⟨_, rfl⟩
  -- factor `jV` and `jU` through the charts over `W_a`
  let jVs : V' ⟶ Spec Γ(W, Wa) := IsOpenImmersion.lift hWa.fromSpec jV
    (by rwa [hWa.range_fromSpec])
  let jUs : U' ⟶ Spec Γ(U, Ua) := IsOpenImmersion.lift hUa.fromSpec jU
    (by rwa [hUa.range_fromSpec])
  have hjVs : jVs ≫ hWa.fromSpec = jV := IsOpenImmersion.lift_fac _ _ _
  have hjUs : jUs ≫ hUa.fromSpec = jU := IsOpenImmersion.lift_fac _ _ _
  have hleft : IsPullback jUs g' gs jVs := isPullback_of_lift_chart hchart hpb hjUs hjVs
  -- the divisor over `V'`
  let Z' := pullback iZs jUs
  let i' : Z' ⟶ U' := pullback.snd iZs jUs
  have hsq : IsPullback (pullback.fst iZs jUs) (i' ≫ g') (iZs ≫ gs) jVs :=
    (IsPullback.of_hasPullback iZs jUs).paste_vert hleft
  have hrange_i : Set.range i'.base = jU.base ⁻¹' S := by
    rw [Scheme.Pullback.range_snd, hZ0, ← hjUs]
    ext y
    simp only [Set.mem_preimage, S, Scheme.Hom.comp_apply]
    exact (hUa.fromSpec.isOpenEmbedding.injective.mem_set_image).symm
  -- the function `f'`, the restriction of `h(t)` to `U'`
  have hleU : (⊤ : U'.Opens) ≤ jU ⁻¹ᵁ Ua := fun y _ => hrangeU ⟨y, rfl⟩
  let f : Γ(U', ⊤) := (jU.appLE Ua ⊤ hleU).hom tq
  have hS : S = U.zeroLocus {tq} ∩ Ua := hUa.fromSpec_image_zeroLocus _
  have hzero : U'.zeroLocus {f} = jU.base ⁻¹' S := by
    rw [hS, Set.preimage_inter, Set.preimage_eq_univ_iff.mpr hrangeU, Set.inter_univ,
      Scheme.preimage_zeroLocus]
    simp only [Set.image_singleton, f, Scheme.Hom.appLE]
    rw [CommRingCat.hom_comp, RingHom.comp_apply]
    have := U'.zeroLocus_map hleU {(jU.app Ua).hom tq}
    rw [Set.image_singleton] at this
    rw [this]
    simp
  refine ⟨Z', i', f, inferInstance, MorphismProperty.of_isPullback hsq hπfin,
    MorphismProperty.of_isPullback hsq hπet, hrange_i.trans hzero.symm, hrange_i, ?_⟩
  -- the geometric fibres
  intro Ω _ w C hC hxy
  let jV₀ : V' ⟶ Spec Γ(W, W₀) := IsOpenImmersion.lift hW₀.fromSpec jV
    (by rw [hW₀.range_fromSpec]; exact hrange.trans (W.basicOpen_le a))
  let jU₀ : U' ⟶ Spec Γ(U, g ⁻¹ᵁ W₀) := IsOpenImmersion.lift hU₀.fromSpec jU
    (by rw [hU₀.range_fromSpec]; exact hrangeU.trans (U.basicOpen_le s))
  have hjV₀ : jV₀ ≫ hW₀.fromSpec = jV := IsOpenImmersion.lift_fac _ _ _
  have hjU₀ : jU₀ ≫ hU₀.fromSpec = jU := IsOpenImmersion.lift_fac _ _ _
  have hleft₀ : IsPullback jU₀ g' g₀ jV₀ := isPullback_of_lift_chart hchart₀ hpb hjU₀ hjV₀
  -- the ring map `A ⟶ Ω` of the geometric point
  let φ : CommRingCat.of Γ(W, W₀) ⟶ CommRingCat.of Ω := Spec.preimage (w ≫ jV₀)
  let : Algebra Γ(W, W₀) Ω := φ.hom.toAlgebra
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap Γ(W, W₀) Ω)) = w ≫ jV₀ := Spec.map_preimage _
  -- `a` is a unit in `Ω`, as the geometric point lies over `W_a`
  have hunit : IsUnit (algebraMap Γ(W, W₀) Ω a) := by
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    let pt : Spec (.of Ω) := ⟨⊥, Ideal.isPrime_bot⟩
    have e1 : Spec.map (CommRingCat.ofHom (algebraMap Γ(W, W₀) Ω)) ≫ hW₀.fromSpec = w ≫ jV := by
      rw [hφ, Category.assoc, hjV₀]
    have hmem : (Spec.map (CommRingCat.ofHom (algebraMap Γ(W, W₀) Ω)) ≫ hW₀.fromSpec).base pt ∈
        Wa := by
      rw [e1]
      exact hrange ⟨w.base pt, rfl⟩
    have hb := hW₀.fromSpec_preimage_basicOpen a
    have : (Spec.map (CommRingCat.ofHom (algebraMap Γ(W, W₀) Ω))).base pt ∈
        hW₀.fromSpec ⁻¹ᵁ W.basicOpen a := hmem
    rw [hb] at this
    have h4 : a ∉ ((Spec.map (CommRingCat.ofHom (algebraMap Γ(W, W₀) Ω))).base pt).asIdeal :=
      this
    exact h4 (by
      change algebraMap Γ(W, W₀) Ω a ∈ (⊥ : Ideal Ω)
      rw [h0]
      exact Submodule.zero_mem _)
  -- the fibre is `Spec (Ω ⊗_A B)`
  have hX : IsPullback (pullback.fst g' w ≫ jU₀) (pullback.snd g' w)
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(W, W₀) Γ(U, g ⁻¹ᵁ W₀))))
      (Spec.map (CommRingCat.ofHom (algebraMap Γ(W, W₀) Ω))) := by
    rw [hφ]
    exact (IsPullback.of_hasPullback g' w).paste_horiz hleft₀
  have hT := (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct Γ(W, W₀) Ω Γ(U, g ⁻¹ᵁ W₀))).flip
  let e := hX.isoIsPullback _ _ hT
  have he : e.hom ≫ Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight.toRingHom :
        Γ(U, g ⁻¹ᵁ W₀) →+* Ω ⊗[Γ(W, W₀)] Γ(U, g ⁻¹ᵁ W₀))) =
      pullback.fst g' w ≫ jU₀ :=
    hX.isoIsPullback_hom_fst _ _ hT
  -- a generic point of `C`, and a second point of `C`
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hC.1 (isClosed_of_mem_irreducibleComponents C hC)
  obtain ⟨z, hzC, hzξ⟩ : ∃ z ∈ C, z ≠ ξ := by
    obtain ⟨x, hx, y, hy, hne⟩ := hxy
    rcases eq_or_ne x ξ with rfl | hxξ
    · exact ⟨y, hy, hne.symm⟩
    · exact ⟨x, hx, hxξ⟩
  have hspec : ξ ⤳ z := hξ.specializes hzC
  set P : PrimeSpectrum (Ω ⊗[Γ(W, W₀)] Γ(U, g ⁻¹ᵁ W₀)) := e.hom.base ξ with hP
  have hPz : P < e.hom.base z := by
    refine lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes _ _).mpr
      (hspec.map e.hom.base.hom.continuous)) fun heq =>
        hzξ ((Scheme.homeoOfIso e).injective heq).symm
  have hdim : 1 ≤ ringKrullDim ((Ω ⊗[Γ(W, W₀)] Γ(U, g ⁻¹ᵁ W₀)) ⧸ P.asIdeal) := by
    rw [ringKrullDim_quotient, Order.one_le_krullDim_iff]
    exact ⟨⟨P, fun _ hx => hx⟩, ⟨e.hom.base z, fun _ hx => hPz.le hx⟩, Subtype.mk_lt_mk.mpr hPz⟩
  obtain ⟨Q, hQ, hPQ, hmem⟩ := Polynomial.exists_isPrime_le_one_tmul_aeval_mem a t hunit hint
    hmon hdeg P.asIdeal hdim
  let q : PrimeSpectrum (Ω ⊗[Γ(W, W₀)] Γ(U, g ⁻¹ᵁ W₀)) := ⟨Q, hQ⟩
  have he' : e.inv ≫ pullback.fst g' w ≫ jU = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight.toRingHom :
        Γ(U, g ⁻¹ᵁ W₀) →+* Ω ⊗[Γ(W, W₀)] Γ(U, g ⁻¹ᵁ W₀))) ≫ hU₀.fromSpec := by
    rw [← hjU₀, ← Category.assoc (pullback.fst g' w) jU₀, ← he, Category.assoc,
      Iso.inv_hom_id_assoc]
  have key : jU.base ((pullback.fst g' w).base (e.inv.base q)) =
      hU₀.fromSpec.base ((Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom :
          Γ(U, g ⁻¹ᵁ W₀) →+* Ω ⊗[Γ(W, W₀)] Γ(U, g ⁻¹ᵁ W₀)))).base q) :=
    congrArg (fun m => m.base q) he'
  refine ⟨e.inv.base q, ?_, ?_⟩
  · -- the point lies on `C`
    rw [← hξ.def, ← specializes_iff_mem_closure]
    have hPq := ((PrimeSpectrum.le_iff_specializes P q).mp hPQ).map e.inv.base.hom.continuous
    rwa [hP, Scheme.hom_inv_apply] at hPq
  · -- and over `S`
    change (pullback.fst g' w).base (e.inv.base q) ∈ Set.range i'.base
    rw [hrange_i]
    change jU.base ((pullback.fst g' w).base (e.inv.base q)) ∈ S
    have hmemU := hrangeU ⟨(pullback.fst g' w).base (e.inv.base q), rfl⟩
    rw [key] at hmemU ⊢
    exact mem_image_zeroLocus_of_fromSpec hU₀ s r _ hmem hmemU

end AlgebraicGeometry
