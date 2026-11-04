module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FreeNearFibreGeneric
public import StacksFrontier.AlgebraicGeometry.Modules.TrivialisationTransport
public import StacksFrontier.AlgebraicGeometry.StrictTransform.AffineChartFibreGenericPoint
public import StacksFrontier.AlgebraicGeometry.StrictTransform.AffineChartSections
public import StacksFrontier.AlgebraicGeometry.StrictTransform.QuotientModelBaseChangeChart

/-!
# The blowup half of [Stacks, Tag 0811] over an affine base

Let `f : X ⟶ S` be a morphism of affine schemes with `Γ(S, ⊤) ⟶ Γ(X, ⊤)` flat of finite
presentation and with geometrically integral fibres, let `F` be a quasi-coherent module on `X`
presented as `M^~`, and let `t : Γ(S, ⊤)` and `r : ℕ` be such that `M` is free of rank `r` at
every extended prime away from `t`. This file produces an ideal sheaf `ℐ` of finite type on `S`,
supported exactly on `V(t)`, such that the strict transform of `F` along the blowup of `S` in `ℐ`
is free of finite rank near the generic point of every fibre of
`X ×_S Bl_ℐ(S) ⟶ Bl_ℐ(S)`. That is the hypothesis
`AlgebraicGeometry.FreeNearFibreGeneric` out of which the two conclusions of [Stacks, Tag 0811]
are read off.

## Main results

* `Stacks.StrictTransform.freeNearFibreGeneric_blowUp_of_affine`: the statement above.
* `Stacks.StrictTransform.coe_support_ofIdealTop_of_forall_isPrime`: the support of the ideal
  sheaf produced there is the complement of the basic open of `t`, which is the form a consumer
  of the ideal sheaf wants.

## Implementation notes

The scheme-level [Stacks, Tag 0810] is
`Stacks.StrictTransform.exists_fg_ideal_forall_chartFreeOfRank`: it produces a finitely generated
ideal `I ⊆ Γ(S, ⊤)` with `V(t) = V(I)` such that for every `a ∈ I` and every prime `q'` of the
affine blowup algebra `Γ(S, ⊤)[I/a]` the predicate `Stacks.StrictTransform.ChartFreeOfRank` holds
for the chart algebra `B = Γ(X, ⊤) ⊗_{Γ(S,⊤)} Γ(S, ⊤)[I/a]` and the extension `q'B`. The ideal
sheaf is `AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop I`, and the charts the predicate
speaks about are produced by `Stacks.StrictTransform.blowUpQuotientBaseChangeChart`.

What has to be checked is that the prime of `B` at which the predicate gives a trivialisation is
the point of the base change under consideration. Writing `z = j w` for the chart `j` of the base
change over the blowup chart through the image of `z` — this is possible by
`Stacks.StrictTransform.range_affineBaseChangeChartMap` — the prime `P` of `B` lies over the
prime `q'` of the blowup chart below it, so it contains `q'B`; and `q'B` is itself a prime lying
over `q'` (`Ideal.isPrime_map_includeRight_of_geometricallyIntegral_fibres`), so the point it
defines lies in the same fibre as `z`, hence in the closure of `z` by the genericity hypothesis,
hence in the closure of `w` because `j` is an open embedding. In `Spec B` that containment is
`P ≤ q'B`, so `P = q'B` and the trivialisation is one at `w`.

The last step pushes that trivialisation, which lives on a basic open of the chart, forward to an
open of the base change containing `z`: that is
`AlgebraicGeometry.nonempty_over_image_iso_free_of_pullback_restrict_iso_free`.

The `Γ(S, ⊤)`-algebra structure on `Γ(X, ⊤)` is assumed as an instance together with the
identification `halg` of its structure map with `f.appTop`, as in [Stacks, Tag 0810]; the charts
are built with `f.appTop.hom.toAlgebra`. The two are *equal*, by `toAlgebra_algebraMap`, and the
proofs below substitute one for the other at the outset rather than carrying a comparison.

## References

* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 0810](https://stacks.math.columbia.edu/tag/0810)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.StrictTransform

/-- **The universally quantified conclusion of [Stacks, Tag 0810] gives freeness near the generic
points of the fibres.** Let `ℐ` be an ideal sheaf on the affine scheme `S` whose ideal of global
sections is `I`, and suppose that for every `a ∈ I` and every prime `q'` of `Γ(S, ⊤)[I/a]` the
strict transform of `F` is free of rank `r` near the generic point of the fibre of the chart
`Spec (Γ(X, ⊤) ⊗_{Γ(S,⊤)} Γ(S, ⊤)[I/a])` over `q'`, in the sense of
`Stacks.StrictTransform.ChartFreeOfRank`. Then the strict transform of `F` along the blowup of
`S` in `ℐ` is free of finite rank near the generic point of every fibre of the projection.

The blowup charts cover `Bl_ℐ(S)` and the charts of the base change over them cover `X ×_S
Bl_ℐ(S)`, so a point `z` generic in its fibre is `j w` for one of those charts; the prime
corresponding to `w` is then identified with the extension of the prime below it, which is the
prime at which the hypothesis speaks. -/
private theorem freeNearFibreGeneric_of_forall_chartFreeOfRank {X S : Scheme.{u}} [IsAffine X]
    [IsAffine S] (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent] (M : ModuleCat.{u} Γ(X, ⊤))
    (r : ℕ) [Algebra Γ(S, ⊤) Γ(X, ⊤)]
    (halg : (algebraMap Γ(S, ⊤) Γ(X, ⊤) : Γ(S, ⊤) →+* Γ(X, ⊤)) = f.appTop.hom)
    [Module.Flat Γ(S, ⊤) Γ(X, ⊤)]
    (hfibre : ∀ (q : Ideal Γ(S, ⊤)) (hq : q.IsPrime),
      letI := hq
      Algebra.IsGeometricallyIntegral q.ResidueField (q.Fiber Γ(X, ⊤)))
    (ℐ : S.IdealSheafData) (I : Ideal Γ(S, ⊤))
    (hid : ℐ.ideal ⟨⊤, isAffineOpen_top S⟩ = I)
    (hchart : ∀ (a : Γ(S, ⊤)) (ha : a ∈ I),
      letI : Fact (a ∈ I) := ⟨ha⟩
      ∀ q' : Ideal (Blowup I a), q'.IsPrime →
        ChartFreeOfRank f F M (CommRingCat.of (Γ(X, ⊤) ⊗[Γ(S, ⊤)] Blowup I a))
          (CommRingCat.ofHom (algebraMap Γ(X, ⊤) (Γ(X, ⊤) ⊗[Γ(S, ⊤)] Blowup I a)))
          (algebraMap Γ(X, ⊤) (Γ(X, ⊤) ⊗[Γ(S, ⊤)] Blowup I a) (f.appTop.hom a)) r
          (Ideal.map Algebra.TensorProduct.includeRight q')) :
    AlgebraicGeometry.FreeNearFibreGeneric (pullback.snd f (blowUpToBase ℐ))
      (sheaf f (blowUpToBase ℐ) (exceptionalIdeal ℐ) F) := by
  subst hid
  obtain rfl : RingHom.toAlgebra f.appTop.hom = ‹Algebra Γ(S, ⊤) Γ(X, ⊤)› :=
    halg ▸ toAlgebra_algebraMap
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have : IsAffineHom (Scheme.Opens.ι (exceptionalIdeal ℐ).support.compl) :=
    Stacks.Divisors.isAffineHom_compl_of_isEffectiveCartierDivisor _
      (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal ℐ)
  intro z hz
  -- Step 1: a blowup chart through the image of `z`.
  obtain ⟨a, t', ht'⟩ := exists_blowUpQuotientChartOfIdeal_preimage ℐ
    (pullback.snd f (blowUpToBase ℐ) z)
  let : Fact ((a : Γ(S, ⊤)) ∈ ℐ.ideal ⟨⊤, isAffineOpen_top S⟩) := ⟨a.2⟩
  set T := Blowup (ℐ.ideal ⟨⊤, isAffineOpen_top S⟩) (a : Γ(S, ⊤))
  set B := Γ(X, ⊤) ⊗[Γ(S, ⊤)] T
  let : Algebra T B := Algebra.TensorProduct.rightAlgebra
  set j := blowUpQuotientBaseChangeChart f ℐ (a : Γ(S, ⊤))
  have : IsOpenImmersion j := isOpenImmersion_blowUpQuotientBaseChangeChart f ℐ (a : Γ(S, ⊤))
  -- Step 2: `z` is in the range of the chart of the base change over it.
  have hrange : Set.range j.base = (pullback.snd f (blowUpToBase ℐ)).base ⁻¹'
      Set.range (blowUpQuotientChartOfIdeal ℐ (a : Γ(S, ⊤))).base :=
    range_affineBaseChangeChartMap f (blowUpToBase ℐ) T (blowUpQuotientChartOfIdeal ℐ _) _
  obtain ⟨w, hw⟩ : z ∈ Set.range j.base := by
    rw [hrange]
    exact ⟨t', ht'⟩
  -- Step 3: `w` lies over the prime `t'` of the blowup chart.
  have hsnd := blowUpQuotientBaseChangeChart_snd f ℐ (a : Γ(S, ⊤))
  set ι : T →ₐ[Γ(S, ⊤)] B := Algebra.TensorProduct.includeRight
  set φ : CommRingCat.of T ⟶ CommRingCat.of B := CommRingCat.ofHom ι.toRingHom
  have hover : ∀ v : Spec (CommRingCat.of B),
      pullback.snd f (blowUpToBase ℐ) (j v) =
        blowUpQuotientChartOfIdeal ℐ (a : Γ(S, ⊤)) (Spec.map φ v) := fun v ↦ by
    have := congrArg (fun m : Spec (CommRingCat.of B) ⟶ blowUp ℐ => m v) hsnd
    simpa only [Scheme.Hom.comp_apply] using this
  have hmapw : Spec.map φ w = t' :=
    (blowUpQuotientChartOfIdeal ℐ (a : Γ(S, ⊤))).isOpenEmbedding.injective <| by
      rw [← hover w, hw, ht']
  have hcomapw : Ideal.comap (algebraMap T B) w.asIdeal = t'.asIdeal :=
    congrArg PrimeSpectrum.asIdeal hmapw
  -- Step 4: the extension of `t'` is contained in `w`.
  have hq' : t'.asIdeal.IsPrime := t'.isPrime
  have hle : Ideal.map ι t'.asIdeal ≤ w.asIdeal :=
    Ideal.map_includeRight_le_of_comap_eq t'.asIdeal w.asIdeal hcomapw
  -- Step 5: the extension of `t'` is itself a prime of the same fibre, hence equals `w`.
  have hQ : (Ideal.map ι t'.asIdeal).IsPrime :=
    Ideal.isPrime_map_includeRight_of_geometricallyIntegral_fibres hfibre t'.asIdeal
  set v₂ : Spec (CommRingCat.of B) :=
    ⟨Ideal.map ι t'.asIdeal, hQ⟩
  have hmapv₂ : Spec.map φ v₂ = t' := PrimeSpectrum.ext
    (Ideal.comap_map_includeRight_of_geometricallyIntegral_fibres hfibre t'.asIdeal)
  have hfibrev₂ : pullback.snd f (blowUpToBase ℐ) (j v₂) =
      pullback.snd f (blowUpToBase ℐ) z := by
    rw [hover v₂, hmapv₂, ht']
  have hclos : j v₂ ∈ closure ({z} : Set (baseChange f (blowUpToBase ℐ))) := hz hfibrev₂
  have hpre : (j.base : Spec (CommRingCat.of B) → baseChange f (blowUpToBase ℐ)) ⁻¹'
      ({j.base w} : Set (baseChange f (blowUpToBase ℐ))) = {w} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun hv ↦ j.isOpenEmbedding.injective hv, fun hv ↦ by rw [hv]⟩
  have hclos' : v₂ ∈ closure ({w} : Set (Spec (CommRingCat.of B))) := by
    rw [← hpre, ← j.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      j.base.hom.continuous]
    show j v₂ ∈ closure ({j.base w} : Set (baseChange f (blowUpToBase ℐ)))
    rwa [hw]
  have hge : w.asIdeal ≤ Ideal.map ι t'.asIdeal :=
    (PrimeSpectrum.le_iff_mem_closure (R := B) w v₂).mpr hclos'
  have hPQ : Ideal.map ι t'.asIdeal =
      w.asIdeal := le_antisymm hle hge
  -- Step 6: the trivialisation of [Stacks, Tag 0810] at that prime.
  obtain ⟨g, hg, ⟨etriv⟩⟩ := hchart (a : Γ(S, ⊤)) a.2 t'.asIdeal hq' (blowUpToBase ℐ)
    (exceptionalIdeal ℐ) j (blowUpQuotientBaseChangeChart_fst f ℐ (a : Γ(S, ⊤)))
    (preimage_exceptionalPreimage_blowUpQuotientBaseChangeChart f ℐ (a : Γ(S, ⊤)))
  rw [hPQ] at hg
  -- Step 7: transport it to an open of the base change containing `z`.
  refine ⟨j ''ᵁ specBasicOpen B g, r, ?_, ?_⟩
  · rw [← hw]
    exact (Scheme.Hom.apply_mem_image_iff j).mpr hg
  · exact nonempty_over_image_iso_free_of_pullback_restrict_iso_free j
      (sheaf f (blowUpToBase ℐ) (exceptionalIdeal ℐ) F) (specBasicOpen B g) _ etriv

/-- **The affine case of the blowup half of [Stacks, Tag 0811].** Let `S` be an affine scheme,
`X` an affine scheme over it with `Γ(S, ⊤) ⟶ Γ(X, ⊤)` flat and of finite presentation with
geometrically integral fibres, let `F` be a quasi-coherent module on `X` presented as `M^~` with
`M` finite over `Γ(X, ⊤)`, let `t : Γ(S, ⊤)` and `r : ℕ`, and assume `M` is finitely presented
after inverting `t` and free of rank `r` at every extended prime `qΓ(X, ⊤)` with `t ∉ q`. Then
there is an ideal sheaf `ℐ` on `S` of finite type, supported exactly on `V(t)`, such that the
strict transform of `F` of [Stacks, Tag 080D] along the blowup of `S` in `ℐ` is free of finite
rank near the generic point of every fibre of `X ×_S Bl_ℐ(S) ⟶ Bl_ℐ(S)`.

The hypotheses are those of the scheme-level [Stacks, Tag 0810],
`Stacks.StrictTransform.exists_fg_ideal_forall_chartFreeOfRank`, and the ideal sheaf is the one
attached to the ideal that statement produces. Freeness near the generic points of the fibres is
the hypothesis `AlgebraicGeometry.FreeNearFibreGeneric` of
`AlgebraicGeometry.exists_opens_isFiniteLocallyFree_surjective_of_freeNearFibreGeneric`, which is
the conclusion [Stacks, Tag 0811] states. -/
public theorem freeNearFibreGeneric_blowUp_of_affine
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] (M : ModuleCat.{u} Γ(X, ⊤))
    (e : F ≅ (Scheme.Modules.pullback X.isoSpec.hom).obj (tilde M))
    [Algebra Γ(S, ⊤) Γ(X, ⊤)]
    (halg : (algebraMap Γ(S, ⊤) Γ(X, ⊤) : Γ(S, ⊤) →+* Γ(X, ⊤)) = f.appTop.hom)
    [Algebra.FinitePresentation Γ(S, ⊤) Γ(X, ⊤)] [Module.Flat Γ(S, ⊤) Γ(X, ⊤)]
    [Module.Finite Γ(X, ⊤) M] (t : Γ(S, ⊤)) (r : ℕ)
    (hfibre : ∀ (q : Ideal Γ(S, ⊤)) (hq : q.IsPrime),
      letI := hq
      Algebra.IsGeometricallyIntegral q.ResidueField (q.Fiber Γ(X, ⊤)))
    (hfp : Module.FinitePresentation (Localization.Away (algebraMap Γ(S, ⊤) Γ(X, ⊤) t))
      (LocalizedModule (Submonoid.powers (algebraMap Γ(S, ⊤) Γ(X, ⊤) t)) M))
    (hrank : ∀ (q : Ideal Γ(S, ⊤)) (hq : q.IsPrime), t ∉ q →
      letI := hq
      let 𝔮 := Ideal.map (algebraMap Γ(S, ⊤) Γ(X, ⊤)) q
      ∀ h𝔮 : 𝔮.IsPrime,
        letI := h𝔮
        Nonempty (LocalizedModule 𝔮.primeCompl M ≃ₗ[Localization 𝔮.primeCompl]
          (Fin r → Localization 𝔮.primeCompl))) :
    ∃ ℐ : S.IdealSheafData, Scheme.IdealSheafData.IsFiniteType ℐ ∧
      (∀ q : Ideal Γ(S, ⊤), q.IsPrime →
        (t ∈ q ↔ ℐ.ideal ⟨⊤, isAffineOpen_top S⟩ ≤ q)) ∧
      AlgebraicGeometry.FreeNearFibreGeneric (Limits.pullback.snd f (blowUpToBase ℐ))
        (Stacks.StrictTransform.sheaf f (blowUpToBase ℐ) (exceptionalIdeal ℐ) F) := by
  obtain ⟨I, hIfg, hIsupp, hchart⟩ :=
    exists_fg_ideal_forall_chartFreeOfRank f F M e halg t r hfibre hfp hrank
  have hid : (Scheme.IdealSheafData.ofIdealTop I).ideal ⟨⊤, isAffineOpen_top S⟩ = I := by
    simp
  refine ⟨Scheme.IdealSheafData.ofIdealTop I, fun U ↦ ?_, fun q hq ↦ ?_,
    freeNearFibreGeneric_of_forall_chartFreeOfRank f F M r halg hfibre _ I hid hchart⟩
  · rw [Scheme.IdealSheafData.ofIdealTop_ideal]
    exact hIfg.map _
  · rw [hid]
    exact hIsupp q hq

/-- **The support of the ideal sheaf attached to an ideal with `V(t) = V(I)`.** If an ideal `I`
of the global sections of an affine scheme is contained in exactly the primes containing `t`,
the support of the ideal sheaf it defines is the complement of the basic open of `t`.

This is the form in which the ideal sheaf of
`Stacks.StrictTransform.freeNearFibreGeneric_blowUp_of_affine` is consumed. -/
public theorem coe_support_ofIdealTop_of_forall_isPrime {S : Scheme.{u}} [IsAffine S]
    (t : Γ(S, ⊤)) (I : Ideal Γ(S, ⊤))
    (hI : ∀ q : Ideal Γ(S, ⊤), q.IsPrime → (t ∈ q ↔ I ≤ q)) :
    ((Scheme.IdealSheafData.ofIdealTop I).support : Set S) =
      ((S.basicOpen t : S.Opens) : Set S)ᶜ := by
  have hrad : t ∈ I.radical := by
    rw [Ideal.radical_eq_sInf]
    exact Submodule.mem_sInf.mpr fun q hq ↦ (hI q hq.2).mpr hq.1
  have hrad' : I ≤ (Ideal.span {t}).radical := fun b hb ↦ by
    rw [Ideal.radical_eq_sInf]
    exact Submodule.mem_sInf.mpr fun q hq ↦
      (hI q hq.2).mp (hq.1 (Ideal.mem_span_singleton_self t)) hb
  rw [Scheme.IdealSheafData.coe_support_ofIdealTop]
  ext x
  rw [Set.mem_compl_iff, Scheme.mem_zeroLocus_iff]
  refine ⟨fun hx hxt ↦ ?_, fun hx b hb hxb ↦ ?_⟩
  · obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hrad
    exact hx (t ^ n) hn ((S.mem_basicOpen_top (t ^ n) x).mpr
      (by simpa only [map_pow] using ((S.mem_basicOpen_top t x).mp hxt).pow n))
  · obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp (hrad' hb)
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hn
    have hbu : IsUnit ((S.presheaf.germ ⊤ x trivial).hom (b ^ n)) := by
      simpa only [map_pow] using ((S.mem_basicOpen_top b x).mp hxb).pow n
    rw [hc, map_mul] at hbu
    exact hx ((S.mem_basicOpen_top t x).mpr (isUnit_of_mul_isUnit_left hbu))

end Stacks.StrictTransform

end
