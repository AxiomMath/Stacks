module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.AffineLineConstantCompactSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportShortExactMonoEpi
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSheafCohomologyLinear

/-!
# `H²_c(𝔸¹_k̄, M)` has as many elements as `M`

Let `k` be a finite field, `Λ` a finite commutative ring in which `#k` is invertible, `k̄` an
algebraically closed extension of `k` and `M` a finite `Λ`-module. Then `H²_c(𝔸¹_k̄, M)` (for any
compactification of `𝔸¹_k`) has `#M` elements.

Since `Hⁱ_c(𝔸¹_k̄, -)` vanishes on finite modules for `i ≠ 2`
(`Stacks.EtaleCohomology.subsingleton_compactSupportSheafCohomology_constantSheaf_affineLine`),
the long exact sequence makes `H²_c(𝔸¹_k̄, -)` exact on short exact sequences of finite modules,
so `#H²_c` is multiplicative in them. The count then follows by dévissage from
`#H²_c(𝔸¹_k̄, ℤ/ℓ) = ℓ`
(`Stacks.EtaleCohomology.natCard_compactSupportSheafCohomology_two_unitSheaf_affineLine`):
over `ℤ/ℓ` along lines, for modules killed by a prime through restriction of scalars, and in
general along `0 → pM → M → M/pM → 0`. This is the size of the stalk of `H²(R f_! Λ)`,
`f : 𝔸¹_k ⟶ Spec k`, in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.natCard_compactSupportSheafCohomology_two_of_shortExact`.
* `Stacks.EtaleCohomology.natCard_compactSupportSheafCohomology_two_constantSheaf_affineLine_zmod`.
* `Stacks.EtaleCohomology.natCard_compactSupportSheafCohomology_two_constantSheaf_affineLine`.

## Implementation notes

`Stacks.EtaleCohomology.compactSupportSheafCohomology` lives in the standard model
`HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section ShortExact

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **`#H²_c` is multiplicative on a short exact sequence `0 → G₁ → G₂ → G₃ → 0` of sheaves** with
`H¹_c(X_k̄, G₃) = 0` and `H³_c(X_k̄, G₁) = 0`: then `0 → H²_c(G₁) → H²_c(G₂) → H²_c(G₃) → 0` is
exact. -/
theorem natCard_compactSupportSheafCohomology_two_of_shortExact
    {T : ShortComplex (EtaleModules.{u, 0} Λ X)} (hT : T.ShortExact)
    (h₁ : Subsingleton ((compactSupportSheafCohomology Λ f j kbar 1).obj T.X₃))
    (h₃ : Subsingleton ((compactSupportSheafCohomology Λ f j kbar 3).obj T.X₁)) :
    Nat.card ((compactSupportSheafCohomology Λ f j kbar 2).obj T.X₂) =
      Nat.card ((compactSupportSheafCohomology Λ f j kbar 2).obj T.X₁) *
        Nat.card ((compactSupportSheafCohomology Λ f j kbar 2).obj T.X₃) := by
  let S := T.map (HomologicalComplex.single (EtaleModules.{u, 0} Λ X) (ComplexShape.up ℤ) 0)
  have hS : S.ShortExact := hT.map_of_exact _
  have p₁ : CochainComplex.plus _ S.X₁ := ⟨0, (inferInstance : CochainComplex.IsStrictlyGE
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj T.X₁) 0)⟩
  have p₂ : CochainComplex.plus _ S.X₂ := ⟨0, (inferInstance : CochainComplex.IsStrictlyGE
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj T.X₂) 0)⟩
  have p₃ : CochainComplex.plus _ S.X₃ := ⟨0, (inferInstance : CochainComplex.IsStrictlyGE
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj T.X₃) 0)⟩
  let H := compactSupportSheafCohomology Λ f j kbar 2
  have hinj : Function.Injective (H.map T.f).hom :=
    (ModuleCat.mono_iff_injective _).1 (mono_homology_compactSupportFrobeniusFunctor_map_f Λ f j
      kbar hS p₁ p₂ p₃ 1 2 (by norm_num) (@ModuleCat.isZero_of_subsingleton _ _ _ h₁))
  have hsurj : Function.Surjective (H.map T.g).hom :=
    (ModuleCat.epi_iff_surjective _).1 (epi_homology_compactSupportFrobeniusFunctor_map_g Λ f j
      kbar hS p₁ p₂ p₃ 2 3 (by norm_num) (@ModuleCat.isZero_of_subsingleton _ _ _ h₃))
  have hex : Function.Exact (H.map T.f).hom (H.map T.g).hom :=
    exact_homology_compactSupportFrobeniusFunctor_map Λ f j kbar hS p₁ p₂ p₃ 2
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.range (H.map T.f).hom), mul_comm,
    ← hex.linearMap_ker_eq,
    Nat.card_congr (LinearMap.quotKerEquivOfSurjective _ hsurj).toEquiv,
    hex.linearMap_ker_eq, ← Nat.card_congr (LinearEquiv.ofInjective _ hinj).toEquiv, mul_comm]

end ShortExact

section ZMod

/-- The constant sheaf functor on `𝔸¹_k` preserves finite colimits. -/
private theorem preservesFiniteColimits_affineLineConstantSheaf (k : Type u) [Field k]
    (Λ : Type) [Ring Λ] : PreservesFiniteColimits (affineLineConstantSheaf k Λ) :=
  have := (constantSheafAdj (Spec (.of k[X])).smallEtaleTopology (ModuleCat.{u + 1} Λ)
    (isTerminalEtaleMkId (Spec (.of k[X])))).leftAdjoint_preservesColimits
  inferInstance

/-- `#H²_c(𝔸¹_k̄, M) = #M` for a subsingleton module `M`: both sets are singletons. -/
private theorem natCard_compactSupportSheafCohomology_two_affineLine_of_subsingleton
    (k : Type u) [Field k] {Λ : Type} [CommRing Λ] (kbar : Type u) [Field kbar]
    [Algebra k kbar] (j : CompactificationOf (Over.mk (affineLineStructureMap k)))
    (M : ModuleCat.{u + 1} Λ) [Subsingleton M] :
    Nat.card ((compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar 2).obj
      ((affineLineConstantSheaf k Λ).obj M)) = Nat.card M := by
  let H := compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar 2
  have := ModuleCat.subsingleton_of_isZero
    (@Functor.map_isZero _ _ _ _ _ _ H (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ H
      (compactSupportSheafCohomology_additive Λ (affineLineStructureMap k) j kbar 2)) _
      (Functor.map_isZero (affineLineConstantSheaf k Λ) (ModuleCat.isZero_of_subsingleton M)))
  rw [Nat.card_unique, Nat.card_unique]

variable (k : Type u) [Field k] [Fintype k] (kbar : Type u) [Field kbar] [Algebra k kbar]
  [IsAlgClosed kbar] {ℓ : ℕ} [Fact ℓ.Prime]

/-- **`#H²_c(𝔸¹_k̄, M) = #M` for a finite `ℤ/ℓ`-module `M`**, `ℓ` invertible in `k̄`: by induction
on `#M`, a nonzero `M` being an extension of a smaller module by a line. -/
theorem natCard_compactSupportSheafCohomology_two_constantSheaf_affineLine_zmod
    (hℓ : IsUnit (ℓ : kbar)) (j : CompactificationOf (Over.mk (affineLineStructureMap k)))
    (M : ModuleCat.{u + 1} (ZMod ℓ)) [Finite M] :
    Nat.card ((compactSupportSheafCohomology (ZMod ℓ) (affineLineStructureMap k) j kbar 2).obj
      ((affineLineConstantSheaf k (ZMod ℓ)).obj M)) = Nat.card M := by
  let H := compactSupportSheafCohomology (ZMod ℓ) (affineLineStructureMap k) j kbar 2
  let F := affineLineConstantSheaf k (ZMod ℓ)
  have := preservesFiniteColimits_affineLineConstantSheaf k (ZMod ℓ)
  suffices h : ∀ (n : ℕ) (M : ModuleCat.{u + 1} (ZMod ℓ)) [Finite M], Nat.card M = n →
      Nat.card (H.obj (F.obj M)) = Nat.card M from h _ M rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ hn
  by_cases hM : Nontrivial M
  · obtain ⟨v, hv⟩ := exists_ne (0 : M)
    let : Fintype M := Fintype.ofFinite M
    let S := Submodule.span (ZMod ℓ) {v}
    let N₁ := ModuleCat.of (ZMod ℓ) S
    let N₂ := ModuleCat.of (ZMod ℓ) (M ⧸ S)
    have : Finite N₂ := inferInstanceAs (Finite (M ⧸ S))
    have : Finite N₁ := inferInstanceAs (Finite S)
    let eS : (ZMod ℓ) ≃ₗ[ZMod ℓ] S := LinearEquiv.toSpanNonzeroSingleton (ZMod ℓ) M v hv
    let e₁ : N₁ ≅ (ModuleCat.of (ZMod ℓ) (ULift.{u + 1} (ZMod ℓ))) :=
      (ULift.moduleEquiv.trans eS).symm.toModuleIso
    have hS : Nat.card S = ℓ := by
      rw [← Nat.card_congr eS.toEquiv, Nat.card_zmod]
    have h₁ : Nat.card (H.obj (F.obj N₁)) = ℓ :=
      (Nat.card_congr (H.mapIso (F.mapIso e₁)).toLinearEquiv.toEquiv).trans
        (natCard_compactSupportSheafCohomology_two_unitSheaf_affineLine k kbar hℓ j)
    have hcard : Nat.card N₂ < n := by
      rw [← hn]
      have hS0 : S ≠ ⊥ := fun h => hv (by
        have : v ∈ S := Submodule.mem_span_singleton_self v
        rw [h, Submodule.mem_bot] at this
        exact this)
      have := Submodule.card_eq_card_quotient_mul_card S
      show Nat.card (M ⧸ S) < Nat.card M
      have hS1 : 1 < Nat.card S := by
        have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS0
        exact Finite.one_lt_card
      have hpos : 0 < Nat.card (M ⧸ S) := Nat.card_pos
      nlinarith
    have h₃ : Nat.card (H.obj (F.obj N₂)) = Nat.card N₂ := ih _ hcard N₂ rfl
    let T := ModuleCat.shortComplexOfCompEqZero S.subtype S.mkQ (by ext; simp)
    have hT : T.ShortExact := ModuleCat.shortComplex_shortExact T (LinearMap.exact_subtype_mkQ S)
      S.injective_subtype S.mkQ_surjective
    have hc := natCard_compactSupportSheafCohomology_two_of_shortExact (ZMod ℓ)
      (affineLineStructureMap k) j kbar (hT.map_of_exact F)
      (subsingleton_compactSupportSheafCohomology_constantSheaf_affineLine_zmod k kbar hℓ j 1
        (by norm_num) N₂)
      (subsingleton_compactSupportSheafCohomology_constantSheaf_affineLine_zmod k kbar hℓ j 3
        (by norm_num) N₁)
    have hc' : Nat.card (H.obj (F.obj T.X₂)) =
        Nat.card (H.obj (F.obj N₁)) * Nat.card (H.obj (F.obj N₂)) := hc
    show Nat.card (H.obj (F.obj T.X₂)) = Nat.card M
    rw [hc', h₁, h₃, Submodule.card_eq_card_quotient_mul_card S, hS, mul_comm]
  · rw [not_nontrivial_iff_subsingleton] at hM
    exact natCard_compactSupportSheafCohomology_two_affineLine_of_subsingleton k kbar j M

end ZMod

section General

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ]
  (kbar : Type u) [Field kbar] [Algebra k kbar] [IsAlgClosed kbar]

/-- **`#H²_c(𝔸¹_k̄, M) = #M`** for a finite `Λ`-module `M` killed by a prime `ℓ` invertible in
`k̄`: restriction of scalars to `ℤ/ℓ`. -/
theorem natCard_compactSupportSheafCohomology_two_constantSheaf_affineLine_of_prime (ℓ : ℕ)
    [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : kbar))
    (j : CompactificationOf (Over.mk (affineLineStructureMap k)))
    (M : ModuleCat.{u + 1} Λ) [Finite M] (hM : ∀ v : M, ℓ • v = 0) :
    Nat.card ((compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar 2).obj
      ((affineLineConstantSheaf k Λ).obj M)) = Nat.card M := by
  let : Module (ZMod ℓ) M := AddCommGroup.zmodModule hM
  obtain ⟨e⟩ := nonempty_equiv_compactSupportSheafCohomology_constantSheaf_zmod k Λ kbar ℓ j 2 M
  have : Finite (ModuleCat.of (ZMod ℓ) M) := inferInstanceAs (Finite M)
  exact (Nat.card_congr e).trans
    (natCard_compactSupportSheafCohomology_two_constantSheaf_affineLine_zmod k kbar hℓ j
      (ModuleCat.of (ZMod ℓ) M))

include kbar in
/-- **`#H²_c(𝔸¹_k̄, M) = #M`** for every finite `Λ`-module `M`, `#k` invertible in `Λ`: by
induction on `#M`, through `0 → pM → M → M/pM → 0` for a prime `p ∣ #M`. -/
theorem natCard_compactSupportSheafCohomology_two_constantSheaf_affineLine
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk (affineLineStructureMap k)))
    (M : ModuleCat.{u + 1} Λ) [Finite M] :
    Nat.card ((compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar 2).obj
      ((affineLineConstantSheaf k Λ).obj M)) = Nat.card M := by
  let H := compactSupportSheafCohomology Λ (affineLineStructureMap k) j kbar 2
  let F := affineLineConstantSheaf k Λ
  have := preservesFiniteColimits_affineLineConstantSheaf k Λ
  suffices h : ∀ (n : ℕ) (M : ModuleCat.{u + 1} Λ) [Finite M], Nat.card M = n →
      Nat.card (H.obj (F.obj M)) = Nat.card M from h _ M rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ hn
  by_cases hM : Nat.card M ≤ 1
  · have : Subsingleton M := (Finite.card_le_one_iff_subsingleton).1 hM
    exact natCard_compactSupportSheafCohomology_two_affineLine_of_subsingleton k kbar j M
  · let : Fintype M := Fintype.ofFinite M
    let p := (Nat.card M).minFac
    have hpp : p.Prime := Nat.minFac_prime (by omega)
    have : Fact p.Prime := ⟨hpp⟩
    obtain ⟨v₀, hv₀⟩ := exists_prime_addOrderOf_dvd_card (G := M) p
      (by rw [← Nat.card_eq_fintype_card]; exact Nat.minFac_dvd _)
    have hv₀0 : v₀ ≠ 0 := fun h => by
      rw [h, addOrderOf_zero] at hv₀
      exact hpp.one_lt.ne hv₀
    have hpv₀ : p • v₀ = 0 := hv₀ ▸ addOrderOf_nsmul_eq_zero v₀
    have hpk : ¬ p ∣ Fintype.card k := fun ⟨c, hc⟩ => hv₀0 <| by
      have h1 : (Fintype.card k : Λ) • v₀ = 0 := by
        rw [Nat.cast_smul_eq_nsmul, hc, mul_nsmul, hpv₀, nsmul_zero]
      exact (hq.smul_eq_zero).1 h1
    let f : M →ₗ[Λ] M := p • LinearMap.id
    let S := LinearMap.range f
    let T := multiplesShortComplex Λ p M
    have : Finite T.X₁ := inferInstanceAs (Finite S)
    have : Finite T.X₃ := inferInstanceAs (Finite (M ⧸ S))
    have hnotsurj : ¬ Function.Surjective f := fun hs => hv₀0 <|
      (Finite.injective_iff_surjective.2 hs) (by
        show p • v₀ = p • 0
        rw [hpv₀, nsmul_zero])
    obtain ⟨x, hx⟩ : ∃ x, x ∉ S := by
      by_contra h
      push Not at h
      exact hnotsurj h
    have hcard : Nat.card T.X₁ < n := hn ▸ Finite.card_subtype_lt hx
    have h₁ : Nat.card (H.obj (F.obj T.X₁)) = Nat.card T.X₁ := ih _ hcard T.X₁ rfl
    have h₃ : Nat.card (H.obj (F.obj T.X₃)) = Nat.card T.X₃ :=
      natCard_compactSupportSheafCohomology_two_constantSheaf_affineLine_of_prime k Λ kbar p
        (isUnit_natCast_of_not_dvd_card k kbar p hpk) j T.X₃ fun w => by
          obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective S w
          rw [← Submodule.Quotient.mk_smul]
          exact (Submodule.Quotient.mk_eq_zero S).2 ⟨y, rfl⟩
    have hc := natCard_compactSupportSheafCohomology_two_of_shortExact Λ
      (affineLineStructureMap k) j kbar ((multiplesShortComplex_shortExact Λ p M).map_of_exact F)
      (subsingleton_compactSupportSheafCohomology_constantSheaf_affineLine k Λ kbar hq j 1
        (by norm_num) T.X₃)
      (subsingleton_compactSupportSheafCohomology_constantSheaf_affineLine k Λ kbar hq j 3
        (by norm_num) T.X₁)
    have hc' : Nat.card (H.obj (F.obj T.X₂)) =
        Nat.card (H.obj (F.obj T.X₁)) * Nat.card (H.obj (F.obj T.X₃)) := hc
    show Nat.card (H.obj (F.obj T.X₂)) = Nat.card M
    rw [hc', h₁, h₃, Submodule.card_eq_card_quotient_mul_card S, mul_comm]

end General

end Stacks.EtaleCohomology

end
