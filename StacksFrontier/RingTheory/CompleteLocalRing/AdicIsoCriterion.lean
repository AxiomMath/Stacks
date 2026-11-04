module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import StacksFrontier.RingTheory.CompleteLocalRing.Noetherian

/-!
# Recognising an isomorphism from its adic truncations

Let `f : R →+* A` be a ring map and `I` an ideal of `R` such that `R` is `I`-adically
complete. If `f` induces a bijection `R / Iⁿ → A / Iⁿ A` for every `n`, and `A` is
`I A`-adically separated, then `f` itself is bijective.

This is the commutative-algebra step that the Stacks proof of
[Stacks, Tag 0AQH](https://stacks.math.columbia.edu/tag/0AQH) compresses into the sentence
*"Since `𝒪_{T,t}` maps injectively into its completion we conclude `R = 𝒪_{T,t}`"*: there
`R` is a Noetherian complete local ring, `A = 𝒪_{T,t}` is the local ring of a locally
Noetherian scheme at a point, and the truncation bijections come from two morphisms
`Spec R → X` agreeing on every `Spec (R / mⁿ)`. The separatedness hypothesis on `A` is
automatic in that situation, which is what
`RingHom.bijective_of_bijective_quotientMap_pow_of_isLocalRing` records.

## Main results

* `RingHom.bijective_of_mem_map_pow`: the criterion with the truncation bijections taken
  apart into a surjectivity and an injectivity statement modulo `Iⁿ`.
* `RingHom.bijective_of_bijective_quotientMap_pow`: the criterion with the hypothesis in its
  recognisable form, bijectivity of `Ideal.quotientMap` at every `n`.
* `RingHom.bijective_of_bijective_quotientMap_pow_of_isLocalRing`: the same for `A`
  Noetherian local, where separatedness of `A` is automatic.
* `RingHom.bijective_of_bijective_quotientMap_maximalIdeal_pow`: the form used by the
  injectivity half of Stacks 0AQH, with `R` a Noetherian complete local ring, `I` its
  maximal ideal and `f` a local homomorphism.
* `RingHom.exists_rightInverse_of_compatible_quotientHom`: a compatible family of ring maps
  `A → R / Iⁿ` splitting `φ : R → A` modulo `Iⁿ` assembles into a genuine retraction
  `A → R` of `φ`. This is the variant the injectivity half of Stacks 0AQH actually needs:
  it produces the section directly and requires neither separatedness of `A` nor the
  truncation maps to be bijective.

## Implementation notes

Surjectivity is proved by building an `I`-adic Cauchy sequence in `R`: a preimage `rₙ` of
`a` modulo `Iⁿ A` has `rₙ - rₘ ∈ Iᵐ` for `m ≤ n` by the injectivity hypothesis, so `rₙ` has
a limit `L` by precompleteness of `R`, and `a - f L ∈ Iⁿ A` for every `n`, whence `a = f L`
by separatedness of `A`. Injectivity uses only the injectivity hypothesis and separatedness
of `R`. Neither half needs `A` to be Noetherian, local, or an `R`-algebra; `A` carries no
`Module R` structure here and is separated as a module over itself.

`RingHom.exists_rightInverse_of_compatible_quotientHom` does not build that sequence by
hand: the compatible family is assembled by `AdicCompletion.liftRingHom` into a ring map
`A →+* AdicCompletion I R`, and `AdicCompletion.of_bijective_iff` turns completeness of `R`
into the ring isomorphism `R ≃+* AdicCompletion I R` used to land it back in `R`. The
identity `χ ∘ φ = id` is then checked on every `AdicCompletion.evalₐ`, by
`AdicCompletion.ext_evalₐ`.

The `IsHausdorff (I.map f) A` hypothesis is stated for the ideal `I.map f` rather than for
`I A` through an `Algebra R A` instance, so that the criterion applies to a bare ring map.
`Ideal.map_pow` identifies `(Iⁿ).map f` with `(I.map f)ⁿ`, which is why a single
separatedness hypothesis covers every `n`.

The truncation hypothesis is spelled exactly as in
`Stacks.AdicCompletion.adicCompletionMap_bijective_of_quotientMap_bijective`
(`StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties`), which from the same hypothesis
concludes that the induced map of *adic completions* is bijective. That lemma does not subsume
the results here and is not subsumed by them: composing it with
`AdicCompletion.of_bijective_iff` would need `IsAdicComplete (I.map f) A`, completeness of
the target, whereas the hypothesis below is only separatedness. That weaker hypothesis is
the one available in Stacks 0AQH, where the target is the local ring of a locally Noetherian
scheme at a point and is not complete.
-/

@[expose] public section

universe u v

/-- **The adic truncation criterion, hypotheses taken apart.** Let `f : R →+* A` with `R`
`I`-adically complete and `A` separated for `I.map f`. If every element of `A` agrees with
an element of the image of `f` modulo `Iⁿ A`, and `f` reflects membership in `Iⁿ`, then `f`
is bijective. -/
theorem RingHom.bijective_of_mem_map_pow {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    {I : Ideal R} (f : R →+* A) [IsAdicComplete I R] [IsHausdorff (I.map f) A]
    (hsurj : ∀ (n : ℕ) (a : A), ∃ r : R, a - f r ∈ (I ^ n).map f)
    (hinj : ∀ (n : ℕ) (r : R), f r ∈ (I ^ n).map f → r ∈ I ^ n) :
    Function.Bijective f := by
  refine ⟨fun x y hxy => ?_, fun a => ?_⟩
  · refine sub_eq_zero.1 <| (‹IsAdicComplete I R›.toIsHausdorff).haus (x - y) fun n => ?_
    simpa [SModEq.sub_mem] using hinj n _ (by simp [map_sub, hxy])
  · choose r hr using fun n => hsurj n a
    have hcauchy : ∀ {m n : ℕ}, m ≤ n → r m ≡ r n [SMOD I ^ m • (⊤ : Submodule R R)] := by
      intro m n hmn
      have hdiff : f (r n - r m) ∈ (I ^ m).map f := by
        simpa [map_sub, sub_sub_cancel_left] using
          sub_mem (hr m) (Ideal.map_mono (Ideal.pow_le_pow_right hmn) (hr n))
      simpa [SModEq.sub_mem] using (I ^ m).neg_mem (hinj m _ hdiff)
    obtain ⟨L, hL⟩ := (‹IsAdicComplete I R›.toIsPrecomplete).prec hcauchy
    refine ⟨L, (sub_eq_zero.1 <| (‹IsHausdorff (I.map f) A›).haus (a - f L) fun n => ?_).symm⟩
    have h3 : f (r n - L) ∈ (I ^ n).map f :=
      Ideal.mem_map_of_mem f (by simpa [SModEq.sub_mem] using hL n)
    simpa [SModEq.sub_mem, ← Ideal.map_pow, map_sub] using add_mem (hr n) h3

/-- **The adic truncation criterion.** A ring map out of an `I`-adically complete ring into
an `I.map f`-adically separated ring is bijective as soon as all its truncations
`R / Iⁿ → A / Iⁿ A` are bijective. -/
theorem RingHom.bijective_of_bijective_quotientMap_pow {R : Type u} {A : Type v} [CommRing R]
    [CommRing A] {I : Ideal R} (f : R →+* A) [IsAdicComplete I R] [IsHausdorff (I.map f) A]
    (h : ∀ n : ℕ,
      Function.Bijective (Ideal.quotientMap ((I ^ n).map f) f Ideal.le_comap_map)) :
    Function.Bijective f := by
  refine RingHom.bijective_of_mem_map_pow (I := I) f (fun n a => ?_) fun n x hx => ?_
  · obtain ⟨y, hy⟩ := (h n).2 (Ideal.Quotient.mk ((I ^ n).map f) a)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective (I := I ^ n) y
    refine ⟨r, ?_⟩
    have : (Ideal.Quotient.mk ((I ^ n).map f)) (f r) =
        (Ideal.Quotient.mk ((I ^ n).map f)) a := by
      simpa [Ideal.quotientMap_mk] using hy
    simpa [Ideal.Quotient.eq, sub_eq_zero] using this.symm
  · have hx0 : Ideal.quotientMap ((I ^ n).map f) f Ideal.le_comap_map
        ((Ideal.Quotient.mk (I ^ n)) x) = 0 := by
      simpa [Ideal.quotientMap_mk, Ideal.Quotient.eq_zero_iff_mem] using hx
    have : (Ideal.Quotient.mk (I ^ n)) x = 0 := by
      refine (h n).1 ?_
      simpa using hx0
    simpa [Ideal.Quotient.eq_zero_iff_mem] using this

/-- **The adic truncation criterion for a Noetherian local target.** When `A` is Noetherian
local and `I A` is a proper ideal of `A`, separatedness of `A` is automatic by Krull's
intersection theorem, so bijectivity of all truncations `R / Iⁿ → A / Iⁿ A` already forces
`f` to be bijective. -/
theorem RingHom.bijective_of_bijective_quotientMap_pow_of_isLocalRing {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] {I : Ideal R} (f : R →+* A) [IsAdicComplete I R]
    [IsNoetherianRing A] [IsLocalRing A] (hne : I.map f ≠ ⊤)
    (h : ∀ n : ℕ,
      Function.Bijective (Ideal.quotientMap ((I ^ n).map f) f Ideal.le_comap_map)) :
    Function.Bijective f := by
  have : IsHausdorff (I.map f) A := IsHausdorff.of_isLocalRing (I.map f) A hne
  exact RingHom.bijective_of_bijective_quotientMap_pow f h

/-- **The form used by the injectivity half of Stacks 0AQH.** Let `R` be a Noetherian
complete local ring with maximal ideal `m`, let `A` be a Noetherian local ring and let
`f : R →+* A` be a local homomorphism. If `f` induces a bijection `R / mⁿ → A / mⁿ A` for
every `n`, then `f` is bijective. -/
theorem RingHom.bijective_of_bijective_quotientMap_maximalIdeal_pow {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] (hR : IsNoetherianCompleteLocalRing R) [IsNoetherianRing A]
    [IsLocalRing A] (f : R →+* A)
    (hlocal : Ideal.map f (@IsLocalRing.maximalIdeal R _ hR.isLocal) ≤
      IsLocalRing.maximalIdeal A)
    (h : ∀ n : ℕ, Function.Bijective (Ideal.quotientMap
      (Ideal.map f ((@IsLocalRing.maximalIdeal R _ hR.isLocal) ^ n)) f Ideal.le_comap_map)) :
    Function.Bijective f := by
  have := hR.isLocal
  have := hR.isComplete
  refine RingHom.bijective_of_bijective_quotientMap_pow_of_isLocalRing f ?_ h
  exact fun htop => (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    (top_le_iff.1 (htop.ge.trans hlocal))

/-- **Assembling a retraction from its adic truncations.** Let `R` be `I`-adically complete
and `φ : R →+* A`. A family of ring maps `ψ n : A →+* R / Iⁿ`, compatible with the
truncation maps `R / Iⁿ → R / Iᵐ` and splitting `φ` modulo every `Iⁿ`, assembles into a ring
map `χ : A →+* R` with `χ ∘ φ = id`.

This is the step that produces the section in the injectivity half of
[Stacks, Tag 0AQH](https://stacks.math.columbia.edu/tag/0AQH). There `A` is the ring of an
affine open neighbourhood of the closed point in the monomorphism
`T = Spec R ×_{X ×_S X, Δ} X → Spec R`, `φ` is its structure map, and the `ψ n` come from
the morphisms `Spec (R / mⁿ) → T` witnessing that the two points of `X` agree on every
truncation; compatibility of the `ψ n` is exactly what the monomorphism hypothesis supplies.
Unlike the criterion above it needs no separatedness of `A`, no Noetherian hypothesis, and
no bijectivity of the truncation maps — only their compatibility. -/
theorem RingHom.exists_rightInverse_of_compatible_quotientHom {R : Type u} {A : Type v}
    [CommRing R] [CommRing A] {I : Ideal R} [IsAdicComplete I R] (φ : R →+* A)
    (ψ : ∀ n : ℕ, A →+* R ⧸ I ^ n)
    (hcompat : ∀ {m n : ℕ} (hle : m ≤ n), (Ideal.Quotient.factorPow I hle).comp (ψ n) = ψ m)
    (hsec : ∀ n : ℕ, (ψ n).comp φ = Ideal.Quotient.mk (I ^ n)) :
    ∃ χ : A →+* R, χ.comp φ = RingHom.id R := by
  let e : R ≃+* AdicCompletion I R :=
    RingEquiv.ofBijective (algebraMap R (AdicCompletion I R))
      (AdicCompletion.of_bijective_iff.2 ‹IsAdicComplete I R›)
  refine ⟨(e.symm : AdicCompletion I R →+* R).comp
    (AdicCompletion.liftRingHom I ψ hcompat), ?_⟩
  ext x
  have key : AdicCompletion.liftRingHom I ψ hcompat (φ x) = e x :=
    AdicCompletion.ext_evalₐ fun n => (AdicCompletion.evalₐ_liftRingHom I ψ hcompat n (φ x)).trans
      (congr($(hsec n) x).trans (AdicCompletion.evalₐ_of I n x).symm)
  simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, key,
    RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]

end
