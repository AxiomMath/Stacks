module

public import Mathlib.RingTheory.Support
public import StacksCore.Algebra.Module.LocalizedModule.Submodule
public import StacksCore.LinearAlgebra.Quotient.Basic
public import StacksCore.RingTheory.Localization.Ideal

/-! # Spreading a vanishing or a surjection out from `S` to a single element

Stacks tag 0GLX says that generators of `S⁻¹(M/IM)` generate `M_f` for some `f ∈ S + I`. Its
footnote records two special cases, of which the first, `I = 0`, is proved here: if `x₁, …, x_r`
generate `S⁻¹M` then they generate `M_f` for some `f ∈ S`.

Mathlib already has both statements for the particular submonoid `S = p.primeCompl`, in
`Mathlib.RingTheory.Support`: `LocalizedModule.exists_subsingleton_away` and
`Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective`. Neither uses
anything about primality, and what is needed for 0GLX is the arbitrary-submonoid version, so both
are generalized here. The prime-complement statements are the case `S := p.primeCompl`.

The route is worth recording, because it is not the one the Stacks proof takes. Stacks argues
directly on generators: write each generator of `M` as an `S⁻¹R`-combination of the `xⱼ` in
`S⁻¹M`, clear denominators, and multiply the resulting elements of `S` together. That argument is
also where the published proof goes wrong — comment #10017 observes that an equality in `S⁻¹M`
does not give the same equality in `M_s`, and repairs it with a second element of `S`. Going
through the cokernel instead avoids the step altogether: surjectivity after localizing is
vanishing of the localized cokernel, by
`LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker`,
and a finite module killed by `S` is killed by a single product of finitely many elements of `S`.
So there is nothing here to repair, and the finite-family bookkeeping happens once, in
`LocalizedModule.exists_mem_subsingleton_away`.

The general case is proved here too, and takes a different route from the tag's. Stacks localizes
twice — at some `s ∈ S`, then at some `g ∈ 1 + I_s` — and glues the two into `f = ss' + is`, a
step it leaves as "details omitted". Localizing **once**, at `T = S + I`, avoids the gluing
entirely: `T` is a submonoid absorbing `I`, so `I` is Jacobson downstairs and Nakayama applies
over `T` directly. That also explains the shape of the answer — `S + I` is precisely the
submonoid over which `I` becomes Jacobson, not an ad-hoc combination.

Consequently the general case leans on Stacks 00DV **(4)** over `T`, not (7) over `R`. Note it
strictly generalizes our 00DV (7): taking `S = ⊥` recovers `f ∈ 1 + I`. Part (7) is kept as it
stands, since it carries its own tag and states its conclusion as `r - 1 ∈ I`.
-/

@[expose] public section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

lemma smul_eq_zero_of_mem_annihilator {r : R} (h : r ∈ Module.annihilator R M) (m : M) :
    r • m = 0 := Module.mem_annihilator.1 h m

/-- If a finite module `M` dies after localizing at `S`, it already dies after localizing at a
single `f ∈ S`.

The arbitrary-submonoid form of `LocalizedModule.exists_subsingleton_away`, which is the case
`S := p.primeCompl`. Finiteness is what makes it work: each of finitely many generators is killed
by some element of `S`, and their product kills all of them at once. -/
theorem LocalizedModule.exists_mem_subsingleton_away (S : Submonoid R) [Module.Finite R M]
    (h : Subsingleton (LocalizedModule S M)) :
    ∃ f ∈ S, Subsingleton (LocalizedModule.Away f M) := by
  obtain ⟨s, hs⟩ := ‹Module.Finite R M›
  rw [IsLocalizedModule.subsingleton_iff S (LocalizedModule.mkLinearMap S M)] at h
  choose r hrS hr0 using h
  refine ⟨s.prod r, S.prod_mem fun m _ ↦ hrS _, (IsLocalizedModule.subsingleton_iff
    (Submonoid.powers (s.prod r)) (LocalizedModule.mkLinearMap _ M)).2 fun m ↦
    ⟨_, Submonoid.mem_powers _, smul_eq_zero_of_mem_annihilator ?_ m⟩⟩
  rw [← Submodule.annihilator_top, ← hs]
  refine Submodule.mem_annihilator_span _ _|>.2 fun ⟨n, hn⟩ ↦ ?_
  rw [(Finset.dvd_prod_of_mem r hn).choose_spec, mul_comm, mul_smul, hr0, smul_zero]

/-- **Stacks 0GLX, special case (I) `I = 0`**: if `φ` becomes surjective after localizing at `S`,
it is already surjective after localizing at a single `f ∈ S`.

Taking `φ` to be `(a₁, …, a_r) ↦ ∑ aⱼxⱼ` recovers the footnote's wording: if `x₁, …, x_r`
generate `S⁻¹M`, then they generate `M_f` for some `f ∈ S`.

The arbitrary-submonoid form of
`Module.exists_localizedMap_away_surjective_of_localizedMap_atPrime_surjective`, and it needs only
`Module.Finite` on the target — `Module.FinitePresentation`, which the bijective analogue
`exists_bijective_map_powers` requires, is not needed for surjectivity alone. -/
@[stacks 0GLX "the footnote's special case (I), `I = 0`; for the general statement see
  `Submodule.exists_mem_addIdeal_and_span_image_eq_top` below"]
theorem Module.exists_localizedMap_away_surjective_of_localizedMap_surjective
    {N : Type*} [AddCommGroup N] [Module R N]
    (S : Submonoid R) [Module.Finite R M] (φ : N →ₗ[R] M)
    (hφ : Function.Surjective (LocalizedModule.map S φ)) :
    ∃ f ∈ S, Function.Surjective (LocalizedModule.map (Submonoid.powers f) φ) := by
  simp_rw [φ.localizedMap_surjective_iff_subsingleton_localized_coker] at hφ ⊢
  exact LocalizedModule.exists_mem_subsingleton_away S hφ

/-! ### The general case of 0GLX -/

/-- A localization of a quotient `M ⧸ N` vanishes exactly when every element of `M` is carried
into `N` by some element of the submonoid.

This is the vanishing criterion the whole of 0GLX runs on: it is what converts between "`s`
spans a localization" (via `Submodule.span_image_eq_top_iff`, at `N := span R s`) and "a
localized quotient is trivial" (via `LocalizedModule.exists_mem_subsingleton_away`). -/
theorem Submodule.subsingleton_iff_forall_exists_smul_mem {Q : Type*} [AddCommGroup Q]
    [Module R Q] (p : Submonoid R) (N : Submodule R M) (g : (M ⧸ N) →ₗ[R] Q)
    [IsLocalizedModule p g] :
    Subsingleton Q ↔ ∀ m : M, ∃ t : p, (t : R) • m ∈ N := by
  rw [IsLocalizedModule.subsingleton_iff p g, (Submodule.Quotient.mk_surjective N).forall]
  simp [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]

/-- **Stacks 0GLX, special case (I) `I = 0`**, as a statement about spans: if every element of a
finite `M` is carried into `span R s` by some element of `S`, then `s` spans `M_f` for a single
`f ∈ S`.

This is the span reading of `Module.exists_localizedMap_away_surjective_of_localizedMap_surjective`
above, and it is the form the general case consumes. It goes through the quotient `M ⧸ span R s`
rather than through a linear-combination map out of a free module, which avoids building the free
module at all. -/
theorem Submodule.exists_mem_and_span_image_eq_top (S : Submonoid R) [Module.Finite R M]
    (s : Set M) (h : ∀ m : M, ∃ t : S, (t : R) • m ∈ Submodule.span R s) :
    ∃ f ∈ S, ∀ {Rf Mf : Type*} [CommRing Rf] [Algebra R Rf]
      [IsLocalization (Submonoid.powers f) Rf] [AddCommGroup Mf] [Module R Mf] [Module Rf Mf]
      [IsScalarTower R Rf Mf] (g : M →ₗ[R] Mf) [IsLocalizedModule (Submonoid.powers f) g],
      Submodule.span Rf (g '' s) = ⊤ := by
  have hsub : Subsingleton (LocalizedModule S (M ⧸ Submodule.span R s)) :=
    (Submodule.subsingleton_iff_forall_exists_smul_mem S _ (LocalizedModule.mkLinearMap S _)).2 h
  obtain ⟨f, hfS, hf⟩ := LocalizedModule.exists_mem_subsingleton_away S hsub
  refine ⟨f, hfS, fun {Rf Mf} _ _ _ _ _ _ _ g _ ↦ ?_⟩
  rw [Submodule.span_image_eq_top_iff Rf (Submonoid.powers f) g]
  exact (Submodule.subsingleton_iff_forall_exists_smul_mem (Submonoid.powers f) _
    (LocalizedModule.mkLinearMap _ _)).1 hf

/-- **Nakayama over `S + I`**: if `s` spans the localization of `M ⧸ IM` at `T = S + I`, then it
already spans the localization of `M` itself.

This is the mathematical heart of 0GLX, and the only step that uses anything about `S + I`.
Three rewrites reduce it to Mathlib's Nakayama: `Submodule.image_toLocalizedQuotient'` says the
two routes to the localized quotient agree, `Submodule.span_image_mkQ_eq_top_iff` trades the
quotient for a `⊔`, and `Submodule.localized'_smul_top` identifies the localized `I • ⊤` as the
extended ideal. What is left is exactly the hypothesis of 00DV (4), whose Jacobson side condition
`Ideal.map_addIdeal_le_ringJacobson` supplies. -/
theorem Submodule.span_image_eq_top_of_span_image_toLocalizedQuotient'_eq_top
    (S : Submonoid R) (I : Ideal R) [Module.Finite R M] (s : Set M)
    {A Mt : Type*} [CommRing A] [Algebra R A] [IsLocalization (S.addIdeal I) A]
    [AddCommGroup Mt] [Module R Mt] [Module A Mt] [IsScalarTower R A Mt]
    (fM : M →ₗ[R] Mt) [IsLocalizedModule (S.addIdeal I) fM]
    (h : Submodule.span A ((I • (⊤ : Submodule R M)).toLocalizedQuotient' A (S.addIdeal I) fM ''
      (Submodule.Quotient.mk '' s)) = ⊤) :
    Submodule.span A (fM '' s) = ⊤ := by
  have : Module.Finite A Mt := Module.Finite.of_isLocalizedModule (S.addIdeal I) fM
  rw [Submodule.image_toLocalizedQuotient', Submodule.span_image_mkQ_eq_top_iff,
    Submodule.localized'_smul_top, sup_comm] at h
  exact top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot
    (Module.finite_def.mp inferInstance)
    (by rw [Ideal.jacobson_bot]; exact Ideal.map_addIdeal_le_ringJacobson S I A) h.ge)

/-- **Stacks 0GLX**: if `s` generates `S⁻¹(M/IM)` and `M` is finite, then `s` generates `M_f`
for some `f ∈ S + I`.

The proof does not follow the Stacks argument, which localizes twice — first at some `s ∈ S`,
then at some `g ∈ 1 + I_s` via Nakayama — and then glues the two into a single `f = ss' + is`,
a step the tag leaves as "details omitted". Instead it localizes **once**, at `T = S + I`.

That works because `T` is a submonoid (`Submonoid.addIdeal`) which absorbs `I` under addition,
so `I` lands in the Jacobson radical of `T⁻¹R` (`Ideal.map_addIdeal_le_ringJacobson`) and
Nakayama applies over `T` directly. Concretely: enlarge the hypothesis from `S` to `T`
(`Submodule.span_image_eq_top_iff` at both ends), strip the quotient, apply 00DV (4)
(`Submodule.le_of_le_smul_of_le_jacobson_bot`) to get that `s` spans `T⁻¹M`, then descend to a
single `f ∈ T` by the `I = 0` case above. `S + I` is not an ad-hoc answer: it is exactly the
submonoid over which `I` becomes Jacobson.

Stated against arbitrary localization witnesses; see
`Submodule.exists_mem_addIdeal_and_span_image_mkLinearMap_eq_top` for the concrete reading. The
hypothesis is phrased over `S⁻¹R` rather than the tag's `S⁻¹(R/I)`; spans agree along the
surjection `S⁻¹R ↠ S⁻¹(R/I)`, so this is a simplification and not a weakening. As in 00DV (7),
`s` need not be finite — only `M` — and the tag's `x₁, …, x_r` is `s := Set.range x`. -/
@[stacks 0GLX]
theorem Submodule.exists_mem_addIdeal_and_span_image_eq_top
    (S : Submonoid R) (I : Ideal R) [Module.Finite R M] (s : Set M)
    {Rₛ Qₛ : Type*} [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
    [AddCommGroup Qₛ] [Module R Qₛ] [Module Rₛ Qₛ] [IsScalarTower R Rₛ Qₛ]
    (fQ : (M ⧸ I • (⊤ : Submodule R M)) →ₗ[R] Qₛ) [IsLocalizedModule S fQ]
    (hs : Submodule.span Rₛ (fQ '' (Submodule.Quotient.mk '' s)) = ⊤) :
    ∃ f ∈ S.addIdeal I, ∀ {Rf Mf : Type*} [CommRing Rf] [Algebra R Rf]
      [IsLocalization (Submonoid.powers f) Rf] [AddCommGroup Mf] [Module R Mf] [Module Rf Mf]
      [IsScalarTower R Rf Mf] (g : M →ₗ[R] Mf) [IsLocalizedModule (Submonoid.powers f) g],
      Submodule.span Rf (g '' s) = ⊤ := by
  refine Submodule.exists_mem_and_span_image_eq_top (S.addIdeal I) s ?_
  set T := S.addIdeal I
  set fM := LocalizedModule.mkLinearMap T M
  -- Enlarge the hypothesis from `S` to `T`, then run Nakayama over `T`, then descend to one `f`.
  rw [← Submodule.span_image_eq_top_iff (Localization T) T fM]
  refine Submodule.span_image_eq_top_of_span_image_toLocalizedQuotient'_eq_top S I s fM ?_
  exact (Submodule.span_image_eq_top_iff (Localization T) T _ _).2 fun q =>
    let ⟨σ, hσ⟩ := (Submodule.span_image_eq_top_iff Rₛ S fQ _).1 hs q
    ⟨⟨σ, S.le_addIdeal I σ.2⟩, hσ⟩

/-- **Stacks 0GLX**, in the concrete `LocalizedModule` model: the tag's literal `M_f`. -/
@[stacks 0GLX]
theorem Submodule.exists_mem_addIdeal_and_span_image_mkLinearMap_eq_top
    (S : Submonoid R) (I : Ideal R) [Module.Finite R M] (s : Set M)
    (hs : Submodule.span (Localization S)
      (LocalizedModule.mkLinearMap S (M ⧸ I • (⊤ : Submodule R M)) ''
        (Submodule.Quotient.mk '' s)) = ⊤) :
    ∃ f ∈ S.addIdeal I, Submodule.span (Localization (Submonoid.powers f))
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M '' s) = ⊤ := by
  obtain ⟨f, hf, h⟩ := Submodule.exists_mem_addIdeal_and_span_image_eq_top S I s
    (LocalizedModule.mkLinearMap S _) hs
  exact ⟨f, hf, h (LocalizedModule.mkLinearMap _ _)⟩
