module

public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Ideal
public import StacksFrontier.AlgebraicGeometry.Flatness.EssentialFinitePresentation
public import StacksFrontier.RingTheory.Flat.FibreCriterionNilpotent
public import StacksFrontier.RingTheory.EssentialFiniteness.Composition
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.FlatTensorProduct

/-!
# Associated primes of the closed fibre, at an arbitrary prime of a flat base change

Let `R` be a local ring, let `R → S` be a ring map essentially of finite presentation, let `N`
be an `S`-module finitely presented over `S` and flat over `R`, and let `M` be an `R`-module.
For a prime `q` of `S` lying over the maximal ideal of `R`, this file proves that
`q ∈ WeakAss_S(N ⊗_R M)` forces `q` to be an associated prime — in the strict sense of
[Stacks, Tag 00LA] — of the closed fibre `N / 𝔪_R N`.  Since `R` is local the residue field
`κ(𝔪_R)` is `R / 𝔪_R`, so the fibre ring of [Stacks, Tag 05IG] is `S / 𝔪_R S` and the fibre
module is `N / 𝔪_R N`;  the statement proved here is therefore the fibre clause
`𝔮 ∈ WeakAss_S(M ⊗_R N) ⟹ 𝔮-bar ∈ Ass_{S-bar}(N-bar)` of that tag, with no hypothesis that `S`
be local.

`StacksFrontier/RingTheory/Ideal/WeaklyAssociatedPrime/FlatTensorProduct.lean` proves the same
clause for `S` local and `q` its maximal ideal.  The passage to a general `q` is a localization:
`S_q` is local, `R → S_q` is again essentially of finite presentation, `N_q` is finitely
presented over `S_q` and still flat over `R`, and the closed fibre of `N_q` is the localization
of the closed fibre of `N`.  What the localization costs is the descent of the *conclusion*:
knowing that `q S_q` annihilates an element of `(N / 𝔪_R N)_q` exactly, one must produce an
element of `N / 𝔪_R N` whose annihilator is `q` on the nose.  Denominators are cleared one
generator at a time, which is possible because `S / 𝔪_R S` is Noetherian, so `q` is generated
modulo `𝔪_R S` by finitely many of its elements:  if `g₁, …, g_k` are such generators and `h`
is a witness upstairs, then `u_i g_i h = 0` for some `u_i ∉ q`, and `y = (u₁ ⋯ u_k) • h` is
annihilated by all of `q` while surviving in the localization, so `Ann_S(y) = q`.

Combining with the contraction clause of
`Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_comap_tensorProduct` gives the full
forward implication of [Stacks, Tag 05IG] at an arbitrary prime of `S`.  The converse
implication is not proved:  it needs `N` to be projective over `R`, which the source reaches
only through the étale-local structure theorem [Stacks, Tag 05ID].

## Main results

* `Module.Flat.of_isLocalizedModule_tower`:  flatness over a base ring survives localization at
  a multiplicative subset of an intermediate algebra.
* `Stacks.WeaklyAssociatedPrimes.comap_eq_maximalIdeal_of_map_maximalIdeal_le`:  a prime of `S`
  containing `𝔪_R S` lies over `𝔪_R`.
* `isAssociatedPrimeStacks_quotient_of_isWeaklyAssociatedPrime_tensorProduct`, in
  `Stacks.WeaklyAssociatedPrimes`:  the fibre clause of [Stacks, Tag 05IG] at an arbitrary prime
  of `S`.
* `isWeaklyAssociatedPrime_maximalIdeal_and_isAssociatedPrimeStacks_fibre`, in the same
  namespace, and its variant `..._of_fg`:  the forward implication of [Stacks, Tag 05IG] at an
  arbitrary prime of `S`, with the contraction clause included.
* `finite_isWeaklyAssociatedPrime_map_maximalIdeal_le`, in the same namespace:  over a local
  base, only finitely many primes of `S` containing `𝔪_R S` are weakly associated to `N`.
* `finite_weaklyAssociatedPrimes_of_flat_of_finitePresentation`, in the same namespace:  a
  finitely presented module flat over the base has only finitely many weakly associated primes
  as soon as the base does.  This is the finiteness consequence of the inclusion `⊆` of
  [Stacks, Tag 05IJ] together with [Stacks, Tag 05AF].

## The finiteness statement

The last result is the shape in which Tags 05IJ and 05AF are used by the proof of
[Stacks, Tag 05IK]:  for `R → S` of finite presentation and `N` a finitely presented `S`-module
flat over `R`, finiteness of `WeakAss_R(R)` implies finiteness of `WeakAss_S(N)`.  The argument
is the one of the source, with `M = R`, so that `N ⊗_R M = N`:

* the contraction clause `isWeaklyAssociatedPrime_comap_tensorProduct` sends `WeakAss_S(N)` into
  `WeakAss_R(R)`, which cuts the problem into the fibres over the finitely many `𝔭` there;
* over a fixed `𝔭` the base is replaced by `R_𝔭` and `S` by `S_Σ`, the localization of `S` at the
  image of `R ∖ 𝔭`;  this is a finitely presented `R_𝔭`-algebra (it is `R_𝔭 ⊗_R S` up to a
  localization at units), the module `N_Σ` is finitely presented over it and flat over `R_𝔭`, and
  the primes of `S` over `𝔭` correspond to the primes of `S_Σ` containing `𝔪_{R_𝔭} S_Σ`;
* `isAssociatedPrimeStacks_quotient_of_isWeaklyAssociatedPrime_tensorProduct` puts each such
  prime in `Ass_{S_Σ}(N_Σ / 𝔪 N_Σ)`, hence — the closed fibre ring being of finite type over the
  residue field `κ(𝔭)`, so Noetherian — in the finite set `associatedPrimes` of the closed fibre
  over the closed fibre ring.  That is [Stacks, Tag 05AF], in its algebra form
  [Stacks, Tag 00LC].

The hypotheses are finite *presentation*, where [Stacks, Tag 05IJ] asks only for finite type:  the
fibre clause of Tag 05IG rests on the universal injectivity of [Stacks, Tag 05DF], which is
proved by a limit argument needing finite presentation.  The source reduces the finite type case
to it through the étale-local structure theorem [Stacks, Tag 05I5]; that reduction is not carried
out here.

## Implementation notes

The tensor product is written `N ⊗[R] M` with the flat module on the left, as in
`StacksFrontier/RingTheory/Ideal/WeaklyAssociatedPrime/FlatTensorProduct.lean`, because the
`S`-module structure that `Mathlib` puts on a tensor product comes from the left factor.  Stacks
writes the same module as `M ⊗_R N`.

`R`, `S`, `N` and `M` live in independent universes, as they do in the local statement of
`FlatTensorProduct.lean` which is localized here.  The independence matters for the finiteness
statement, where the base is replaced by a localization of `R` — in the universe of `R` — while
the algebra is replaced by a localization of `S`.

The closed fibre is spelled `N ⧸ 𝔪_R S • ⊤`, a quotient of `N` by an `S`-submodule, and its
localization is identified with `N_q ⧸ 𝔪_R S_q • ⊤` through `Submodule.localized'`:
`Submodule.localized'_smul` turns the localization of `𝔪_R S • ⊤` into `(𝔪_R S)S_q • ⊤`, and
`IsLocalizedModule.toLocalizedQuotient'` provides the localization map on the quotients.  That
`S_q ⧸ 𝔪_R S_q` is Noetherian comes from the same reading at the level of rings, where
`Mathlib` supplies
`IsLocalization (Algebra.algebraMapSubmonoid (S ⧸ I) q.primeCompl) (S_q ⧸ I S_q)` directly.

Finiteness of the closed fibre over the closed-fibre ring is *derived* from
`Module.FinitePresentation S N` here, rather than assumed as it is in
`FlatTensorProduct.lean`;  `Module.Finite.of_restrictScalars_finite` does it, so the hypothesis
list is shorter than that of the local statement being generalized.

## References

* [Stacks Project, Tag 00LA](https://stacks.math.columbia.edu/tag/00LA)
* [Stacks Project, Tag 00LC](https://stacks.math.columbia.edu/tag/00LC)
* [Stacks Project, Tag 0547](https://stacks.math.columbia.edu/tag/0547)
* [Stacks Project, Tag 05AF](https://stacks.math.columbia.edu/tag/05AF)
* [Stacks Project, Tag 05DF](https://stacks.math.columbia.edu/tag/05DF)
* [Stacks Project, Tag 05I5](https://stacks.math.columbia.edu/tag/05I5)
* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
* [Stacks Project, Tag 05II](https://stacks.math.columbia.edu/tag/05II)
* [Stacks Project, Tag 05IJ](https://stacks.math.columbia.edu/tag/05IJ)
* [Stacks Project, Tag 05IK](https://stacks.math.columbia.edu/tag/05IK)
-/

@[expose] public section

open TensorProduct

universe u v w t

/-- Flatness over a base ring survives localization at a multiplicative subset of an
intermediate algebra:  if `N` is an `S`-module flat over `R` and `T ⊆ S` is a submonoid, then
the localization `T⁻¹N` is again flat over `R`. -/
theorem Module.Flat.of_isLocalizedModule_tower
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    {N : Type w} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
    [Module.Flat R N] (T : Submonoid S) {N' : Type t} [AddCommGroup N'] [Module S N']
    [Module R N'] [IsScalarTower R S N'] (g : N →ₗ[S] N') [IsLocalizedModule T g] :
    Module.Flat R N' := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro X Y _ _ _ _ f hf
  have h1 : Function.Injective (TensorProduct.AlgebraTensorModule.lTensor S N f) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := N) f hf
  have h2 := IsLocalizedModule.map_injective T
    (TensorProduct.AlgebraTensorModule.rTensor R X g)
    (TensorProduct.AlgebraTensorModule.rTensor R Y g)
    (TensorProduct.AlgebraTensorModule.lTensor S N f) h1
  rw [IsLocalizedModule.map_lTensor] at h2
  intro a b hab
  exact h2 (by simpa using hab)

namespace Stacks.WeaklyAssociatedPrimes

open IsLocalRing

section Localized

variable {S : Type v} [CommRing S]
  {N : Type w} [AddCommGroup N] [Module S N]

/-- Localizing the submodule `IN` of `N` at a submonoid `T ⊆ S` gives the submodule
`(IS_T)(T⁻¹N)` of `T⁻¹N`. -/
private theorem localized'_ideal_smul_top (T : Submonoid S) (I : Ideal S) :
    Submodule.localized' (Localization T) T (LocalizedModule.mkLinearMap T N)
        (I • (⊤ : Submodule S N))
      = Ideal.map (algebraMap S (Localization T)) I •
          (⊤ : Submodule (Localization T) (LocalizedModule T N)) := by
  rw [Submodule.localized'_smul, Submodule.localized'_top]
  congr 1
  rw [Submodule.localized'_eq_span]
  rfl

/-- Reading the localization of `IN` as `(IS_T)(T⁻¹N)`. -/
private noncomputable def quotLocalizedEquiv (T : Submonoid S) (I : Ideal S) :
    (LocalizedModule T N ⧸ Submodule.localized' (Localization T) T
        (LocalizedModule.mkLinearMap T N) (I • (⊤ : Submodule S N))) ≃ₗ[S]
      (LocalizedModule T N ⧸ (Ideal.map (algebraMap S (Localization T)) I •
        (⊤ : Submodule (Localization T) (LocalizedModule T N)))) :=
  (Submodule.quotEquivOfEq _ _ (localized'_ideal_smul_top T I)).restrictScalars S

/-- The quotient `T⁻¹N / (IS_T)(T⁻¹N)` is the localization at `T` of `N / IN`. -/
private theorem exists_isLocalizedModule_quot (T : Submonoid S) (I : Ideal S) :
    ∃ θ : (N ⧸ (I • (⊤ : Submodule S N))) →ₗ[S]
        (LocalizedModule T N ⧸ (Ideal.map (algebraMap S (Localization T)) I •
          (⊤ : Submodule (Localization T) (LocalizedModule T N)))),
      IsLocalizedModule T θ :=
  ⟨_, IsLocalizedModule.of_linearEquiv T
    (Submodule.toLocalizedQuotient' (Localization T) T (LocalizedModule.mkLinearMap T N)
      (I • (⊤ : Submodule S N)))
    (quotLocalizedEquiv T I)⟩

/-- The scalars of `S` act on `N / IN` through `S / I`. -/
private instance isScalarTower_quotient (I : Ideal S) :
    IsScalarTower S (S ⧸ I) (N ⧸ (I • (⊤ : Submodule S N))) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- A finite module stays finite on the fibre:  `N / IN` is a finite `S / I`-module. -/
private instance moduleFinite_quotient (I : Ideal S) [Module.Finite S N] :
    Module.Finite (S ⧸ I) (N ⧸ (I • (⊤ : Submodule S N))) :=
  Module.Finite.of_restrictScalars_finite S (S ⧸ I) _

/-- An ideal annihilates the quotient it is divided out of. -/
private theorem smul_eq_zero_of_mem_ideal {I : Ideal S} {a : S} (ha : a ∈ I)
    (x : N ⧸ (I • (⊤ : Submodule S N))) : a • x = 0 := by
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.smul_mem_smul ha Submodule.mem_top)

end Localized

/-- A prime `q` containing an ideal `I` for which `S / I` is Noetherian is generated modulo `I`
by finitely many of its own elements. -/
private theorem exists_finset_subset_le_sup_span {S : Type v} [CommRing S] (I : Ideal S)
    [IsNoetherianRing (S ⧸ I)] (q : Ideal S) (hIq : I ≤ q) :
    ∃ G : Finset S, (∀ g ∈ G, g ∈ q) ∧ q ≤ I ⊔ Ideal.span (G : Set S) := by
  classical
  obtain ⟨T, hT⟩ := IsNoetherian.noetherian (q.map (Ideal.Quotient.mk I))
  have hex : ∀ t ∈ T, ∃ s : S, s ∈ q ∧ Ideal.Quotient.mk I s = t := fun t ht =>
    (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp
      (hT ▸ Ideal.subset_span ht)
  choose! σ hσq hσ using hex
  refine ⟨T.image σ, Finset.forall_mem_image.mpr hσq, ?_⟩
  have hGimg : (Ideal.Quotient.mk I) '' (↑(T.image σ) : Set S) = (↑T : Set (S ⧸ I)) := by
    rw [Finset.coe_image, Set.image_image]
    exact (Set.image_congr hσ).trans (Set.image_id' _)
  have h2 : q.map (Ideal.Quotient.mk I) ≤
      Ideal.map (Ideal.Quotient.mk I) (I ⊔ Ideal.span (↑(T.image σ) : Set S)) := by
    rw [Ideal.map_sup, Ideal.map_span, hGimg]
    exact le_sup_of_le_right hT.ge
  have h3 := Ideal.comap_mono (f := Ideal.Quotient.mk I) h2
  rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hIq,
    sup_eq_left.mpr (le_sup_left : I ≤ _)] at h3

/-- Weak association of a prime to a module only depends on the module up to isomorphism. -/
private theorem isWeaklyAssociatedPrime_of_linearEquiv {A : Type*} [CommRing A]
    {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (e : X ≃ₗ[A] Y) {p : Ideal A} (h : IsWeaklyAssociatedPrime A X p) :
    IsWeaklyAssociatedPrime A Y p := by
  obtain ⟨x, hx⟩ := h
  refine ⟨e x, ?_⟩
  have hann : (A ∙ e x).annihilator = (A ∙ x).annihilator := by
    ext r
    simp only [Submodule.mem_annihilator_span_singleton, ← e.map_smul,
      map_eq_zero_iff _ e.injective]
  rwa [hann]

/-- Association of a prime to a module only depends on the module up to isomorphism. -/
private theorem isAssociatedPrimeStacks_of_linearEquiv {A : Type*} [CommRing A]
    {X Y : Type*} [AddCommGroup X] [Module A X] [AddCommGroup Y] [Module A Y]
    (e : X ≃ₗ[A] Y) {p : Ideal A} (h : IsAssociatedPrimeStacks A X p) :
    IsAssociatedPrimeStacks A Y p := by
  obtain ⟨hp, x, hx⟩ := h
  refine ⟨hp, e x, ?_⟩
  rw [← hx]
  ext r
  simp only [Submodule.mem_colon_span_singleton, Submodule.mem_bot, ← e.map_smul,
    map_eq_zero_iff _ e.injective]

private theorem mem_of_smul_smul_eq_zero_of_colon_eq_maximalIdeal {S : Type v} [CommRing S]
    {P Q : Type*} [AddCommGroup P] [Module S P] [AddCommGroup Q] [Module S Q]
    {q : Ideal S} [q.IsPrime] [Module (Localization.AtPrime q) Q]
    [IsScalarTower S (Localization.AtPrime q) Q] (θ : P →ₗ[S] Q) {h : P}
    (hann : (⊥ : Submodule (Localization.AtPrime q) Q).colon
      (Submodule.span (Localization.AtPrime q) {θ h}) = maximalIdeal (Localization.AtPrime q))
    {v : S} (hvq : v ∉ q) {r : S} (hr0 : r • v • h = 0) : r ∈ q := by
  have hmem : algebraMap S (Localization.AtPrime q) (r * v) ∈
      maximalIdeal (Localization.AtPrime q) := by
    rw [← hann, Submodule.mem_colon_span_singleton, Submodule.mem_bot, algebraMap_smul,
      mul_smul, ← map_smul, ← map_smul, hr0, map_zero]
  rw [map_mul] at hmem
  rcases (maximalIdeal.isMaximal (Localization.AtPrime q)).isPrime.mem_or_mem hmem with h₁ | h₂
  · exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q _).mp h₁
  · exact absurd ((IsLocalization.AtPrime.to_map_mem_maximal_iff _ q _).mp h₂) hvq

/-- Strict association descends along a localization at a prime `q`: if `q S_q` is associated
to `P_q` and an ideal `I ≤ q` with `S / I` Noetherian kills `P`, then `q` is associated to `P`. -/
theorem isAssociatedPrimeStacks_of_isLocalizedModule_atPrime {S : Type v} [CommRing S]
    {P Q : Type*} [AddCommGroup P] [Module S P] [AddCommGroup Q] [Module S Q]
    {q : Ideal S} [q.IsPrime] [Module (Localization.AtPrime q) Q]
    [IsScalarTower S (Localization.AtPrime q) Q] (I : Ideal S) [IsNoetherianRing (S ⧸ I)]
    (hIq : I ≤ q) (hI : ∀ a ∈ I, ∀ x : P, a • x = 0) (θ : P →ₗ[S] Q)
    [IsLocalizedModule q.primeCompl θ]
    (hQ : IsAssociatedPrimeStacks (Localization.AtPrime q) Q (maximalIdeal _)) :
    IsAssociatedPrimeStacks S P q := by
  classical
  obtain ⟨-, x, hx⟩ := hQ
  obtain ⟨⟨h, s⟩, hs0⟩ := IsLocalizedModule.surj q.primeCompl θ x
  have hs : (s : S) • x = θ h := hs0
  have hspan : (Localization.AtPrime q ∙ θ h) = (Localization.AtPrime q ∙ x) := by
    rw [← hs, ← algebraMap_smul (Localization.AtPrime q) (s : S) x]
    exact Submodule.span_singleton_smul_eq (IsLocalization.map_units _ s) x
  rw [← hspan] at hx
  obtain ⟨G, hGq, hqG⟩ := exists_finset_subset_le_sup_span I q hIq
  have hkill : ∀ g ∈ G, ∃ u : q.primeCompl, (u : S) • (g • h) = 0 := by
    intro g hg
    refine (IsLocalizedModule.eq_zero_iff q.primeCompl θ).mp ?_
    rw [map_smul]
    have hgB : algebraMap S (Localization.AtPrime q) g ∈
        maximalIdeal (Localization.AtPrime q) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q _).mpr (hGq g hg)
    rw [← hx] at hgB
    have hz := Submodule.mem_colon_span_singleton.mp hgB
    rw [Submodule.mem_bot] at hz
    rwa [← algebraMap_smul (Localization.AtPrime q) g (θ h)]
  choose! u hu using hkill
  set v : S := ∏ g ∈ G, (u g : S) with hv
  have hvq : v ∉ q := fun hmem => by
    obtain ⟨g, hg, hgq⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact (u g).2 hgq
  refine ⟨inferInstance, v • h, le_antisymm (fun r hr => ?_) (hqG.trans (sup_le ?_ ?_))⟩
  · exact mem_of_smul_smul_eq_zero_of_colon_eq_maximalIdeal θ hx hvq (by
      simpa only [Submodule.mem_colon_span_singleton, Submodule.mem_bot] using hr)
  · exact fun a ha => Submodule.mem_colon_span_singleton.mpr ((Submodule.mem_bot _).mpr (hI a ha _))
  · rw [Ideal.span_le]
    intro g hg
    refine Submodule.mem_colon_span_singleton.mpr ?_
    rw [Submodule.mem_bot]
    obtain ⟨c, hc⟩ : (u g : S) ∣ v := by
      rw [hv]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_coe.mp hg)
    rw [smul_smul, hc, show g * ((u g : S) * c) = c * ((u g : S) * g) by ring, mul_smul,
      ← smul_smul, hu g (Finset.mem_coe.mp hg), smul_zero]

section GeneralPrime

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [Algebra R S]
  {N : Type w} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]
  {M : Type t} [AddCommGroup M] [Module R M]

/-- Localizing at a prime lying over the maximal ideal of a local base keeps the structure
map local. -/
private theorem isLocalHom_algebraMap_atPrime (q : Ideal S) [q.IsPrime]
    (hIq : Ideal.map (algebraMap R S) (maximalIdeal R) ≤ q) :
    IsLocalHom (algebraMap R (Localization.AtPrime q)) := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have h1 : algebraMap R S a ∈ q :=
    hIq (Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal a).mpr hna))
  have h2 : algebraMap R (Localization.AtPrime q) a ∈ maximalIdeal (Localization.AtPrime q) := by
    rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime q)]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q _).mpr h1
  exact (IsLocalRing.mem_maximalIdeal _).mp h2 ha

/-- A prime of `S` containing `𝔪_R S` contracts to the maximal ideal of the local ring `R`. -/
theorem comap_eq_maximalIdeal_of_map_maximalIdeal_le (q : Ideal S) [q.IsPrime]
    (hIq : Ideal.map (algebraMap R S) (maximalIdeal R) ≤ q) :
    q.comap (algebraMap R S) = maximalIdeal R :=
  ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_isPrime (algebraMap R S) q).ne_top
    fun _ ha => hIq (Ideal.mem_map_of_mem _ ha)).symm

/-- **The fibre clause of [Stacks, Tag 05IG] at an arbitrary prime of `S`.**  Let `R` be a local
ring, let `R → S` be essentially of finite presentation with `S / 𝔪_R S` Noetherian, let `N` be
an `S`-module finitely presented over `S` and flat over `R`, and let `M` be an `R`-module.  If a
prime `q` of `S` containing `𝔪_R S` is weakly associated to `N ⊗[R] M`, then `q` is an
associated prime — in the strict sense of [Stacks, Tag 00LA] — of the closed fibre `N / 𝔪_R N`.

This is the implication `𝔮 ∈ WeakAss_S(M ⊗_R N) ⟹ 𝔮-bar ∈ Ass_{S-bar}(N-bar)` of Tag 05IG read
after localizing `R` at `𝔭` only:  the residue field `κ(𝔪_R)` is `R / 𝔪_R`, so the fibre ring is
the quotient `S / 𝔪_R S` and the fibre module is `N / 𝔪_R N`.

`isAssociatedPrimeStacks_maximalIdeal_quotient_of_isWeaklyAssociatedPrime_tensorProduct`
is the case of `S` local and `q = 𝔪_S`;  this statement is obtained from it by localizing `S` at
`q` and descending the conclusion, which is where the Noetherian hypothesis on the fibre ring is
used a second time, to make `q` finitely generated modulo `𝔪_R S`. -/
theorem isAssociatedPrimeStacks_quotient_of_isWeaklyAssociatedPrime_tensorProduct
    [Module.FinitePresentation S N] [Module.Flat R N]
    [IsNoetherianRing (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation)
    {q : Ideal S} [q.IsPrime]
    (hIq : Ideal.map (algebraMap R S) (maximalIdeal R) ≤ q)
    (hq : IsWeaklyAssociatedPrime S (N ⊗[R] M) q) :
    IsAssociatedPrimeStacks S
      (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N))) q := by
  classical
  have hIB : Ideal.map (algebraMap R (Localization.AtPrime q)) (maximalIdeal R) =
      Ideal.map (algebraMap S (Localization.AtPrime q))
        (Ideal.map (algebraMap R S) (maximalIdeal R)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have : IsLocalHom (algebraMap R (Localization.AtPrime q)) :=
    isLocalHom_algebraMap_atPrime q hIq
  have : Module.Flat R (LocalizedModule q.primeCompl N) :=
    Module.Flat.of_isLocalizedModule_tower q.primeCompl
      (LocalizedModule.mkLinearMap q.primeCompl N)
  have : IsNoetherianRing (Localization.AtPrime q ⧸
      Ideal.map (algebraMap R (Localization.AtPrime q)) (maximalIdeal R)) := by
    rw [hIB]
    exact IsLocalization.isNoetherianRing
      (Algebra.algebraMapSubmonoid (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))
        q.primeCompl) _ inferInstance
  have hRB : (algebraMap R (Localization.AtPrime q)).EssentiallyOfFinitePresentation := by
    rw [IsScalarTower.algebraMap_eq R S (Localization.AtPrime q)]
    exact essFinitePresentation_comp hS
      (RingHom.EssentiallyOfFinitePresentation.of_isLocalization (C := S) q.primeCompl)
  have hqB : IsWeaklyAssociatedPrime (Localization.AtPrime q)
      (LocalizedModule q.primeCompl N ⊗[R] M)
      (maximalIdeal (Localization.AtPrime q)) :=
    isWeaklyAssociatedPrime_of_linearEquiv
      ((IsLocalizedModule.linearEquiv q.primeCompl
        (LocalizedModule.mkLinearMap q.primeCompl (N ⊗[R] M))
        (TensorProduct.AlgebraTensorModule.rTensor R M
          (LocalizedModule.mkLinearMap q.primeCompl N))).extendScalarsOfIsLocalization
            q.primeCompl (Localization.AtPrime q))
      ((weaklyAssociated_iff_localization (M := N ⊗[R] M) q).mp hq)
  have hB' := isAssociatedPrimeStacks_maximalIdeal_quotient_of_isWeaklyAssociatedPrime_tensorProduct
    (R := R) (S := Localization.AtPrime q) (N := LocalizedModule q.primeCompl N) (M := M)
    hRB hqB
  obtain ⟨θ, hθ⟩ := exists_isLocalizedModule_quot (N := N) q.primeCompl
    (Ideal.map (algebraMap R S) (maximalIdeal R))
  exact isAssociatedPrimeStacks_of_isLocalizedModule_atPrime
    (Ideal.map (algebraMap R S) (maximalIdeal R)) hIq (fun _ ha => smul_eq_zero_of_mem_ideal ha)
    θ (isAssociatedPrimeStacks_of_linearEquiv (Submodule.quotEquivOfEq _ _ (by rw [hIB])) hB')

/-- **The implication `⟹` of [Stacks, Tag 05IG] at an arbitrary prime of `S`.**  If a prime `q`
of `S` containing `𝔪_R S` is weakly associated to `N ⊗[R] M`, then the maximal ideal of `R` —
which is the contraction of `q` — is weakly associated to `M`, and `q` is associated to the
closed fibre `N / 𝔪_R N`.

The two conjuncts are
`isWeaklyAssociatedPrime_comap_tensorProduct` and
`isAssociatedPrimeStacks_quotient_of_isWeaklyAssociatedPrime_tensorProduct`;
only the first uses the finiteness of `WeakAss_R(M)`.  The converse implication of Tag 05IG is
not proved:  it needs `N` to be projective over `R`, for which the source invokes the
étale-local structure theorem [Stacks, Tag 05ID]. -/
theorem isWeaklyAssociatedPrime_maximalIdeal_and_isAssociatedPrimeStacks_fibre
    [Module.FinitePresentation S N] [Module.Flat R N]
    [IsNoetherianRing (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation)
    (hfin : (weaklyAssociatedPrimes R M).Finite) {q : Ideal S} [q.IsPrime]
    (hIq : Ideal.map (algebraMap R S) (maximalIdeal R) ≤ q)
    (hq : IsWeaklyAssociatedPrime S (N ⊗[R] M) q) :
    IsWeaklyAssociatedPrime R M (maximalIdeal R) ∧
      IsAssociatedPrimeStacks S
        (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N))) q :=
  ⟨comap_eq_maximalIdeal_of_map_maximalIdeal_le q hIq ▸
      isWeaklyAssociatedPrime_comap_tensorProduct hfin hq,
    isAssociatedPrimeStacks_quotient_of_isWeaklyAssociatedPrime_tensorProduct hS hIq hq⟩

/-- Both clauses of the forward implication, at an arbitrary prime, with the finiteness
hypothesis on `WeakAss_R(M)` traded for finite generation of the maximal ideal of `R`. -/
theorem isWeaklyAssociatedPrime_maximalIdeal_and_isAssociatedPrimeStacks_fibre_of_fg
    [Module.FinitePresentation S N] [Module.Flat R N]
    [IsNoetherianRing (S ⧸ Ideal.map (algebraMap R S) (maximalIdeal R))]
    (hS : (algebraMap R S).EssentiallyOfFinitePresentation)
    (hfg : (maximalIdeal R).FG) {q : Ideal S} [q.IsPrime]
    (hIq : Ideal.map (algebraMap R S) (maximalIdeal R) ≤ q)
    (hq : IsWeaklyAssociatedPrime S (N ⊗[R] M) q) :
    IsWeaklyAssociatedPrime R M (maximalIdeal R) ∧
      IsAssociatedPrimeStacks S
        (N ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) • (⊤ : Submodule S N))) q := by
  refine ⟨?_, isAssociatedPrimeStacks_quotient_of_isWeaklyAssociatedPrime_tensorProduct hS hIq hq⟩
  have hcomap := comap_eq_maximalIdeal_of_map_maximalIdeal_le (R := R) q hIq
  exact hcomap ▸ isWeaklyAssociatedPrime_comap_tensorProduct_of_fg hq (hcomap ▸ hfg)

end GeneralPrime

section Finiteness

/-- The closed fibre ring of a finite type algebra over a local ring is Noetherian:  it is of
finite type over the residue field. -/
private theorem isNoetherianRing_quotient_map_maximalIdeal
    {A : Type*} [CommRing A] [IsLocalRing A] {B : Type*} [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] :
    IsNoetherianRing (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) := by
  set I : Ideal B := Ideal.map (algebraMap A B) (maximalIdeal A)
  have hker : ∀ a ∈ maximalIdeal A, algebraMap A (B ⧸ I) a = 0 := by
    intro a ha
    change Ideal.Quotient.mk I (algebraMap A B a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)
  have : Algebra.FiniteType A (B ⧸ I) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ A I) Ideal.Quotient.mk_surjective
  let : Algebra (ResidueField A) (B ⧸ I) :=
    (Ideal.Quotient.lift (maximalIdeal A) (algebraMap A (B ⧸ I)) hker).toAlgebra
  have : IsScalarTower A (ResidueField A) (B ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Algebra.FiniteType (ResidueField A) (B ⧸ I) :=
    Algebra.FiniteType.of_restrictScalars_finiteType A (ResidueField A) (B ⧸ I)
  exact Algebra.FiniteType.isNoetherianRing (ResidueField A) (B ⧸ I)

/-- Strict association passes to the quotient by an ideal contained in the prime, for a module
on which that ideal acts through the quotient. -/
private theorem isAssociatedPrimeStacks_quotient_ring {B : Type*} [CommRing B]
    {F : Type*} [AddCommGroup F] [Module B F] {I : Ideal B}
    [Module (B ⧸ I) F] [IsScalarTower B (B ⧸ I) F]
    {J : Ideal B} (hIJ : I ≤ J) (h : IsAssociatedPrimeStacks B F J) :
    IsAssociatedPrimeStacks (B ⧸ I) F (Ideal.map (Ideal.Quotient.mk I) J) := by
  obtain ⟨hJ, y, hy⟩ := h
  refine ⟨Ideal.isPrime_map_quotientMk_of_isPrime hIJ, y, ?_⟩
  ext b
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [Submodule.mem_colon_span_singleton, Submodule.mem_bot, ← Ideal.mem_comap,
    Ideal.comap_map_mk hIJ, ← Ideal.Quotient.algebraMap_eq, IsScalarTower.algebraMap_smul]
  simpa only [Submodule.mem_colon_span_singleton, Submodule.mem_bot] using SetLike.ext_iff.mp hy s

/-- A prime which is exactly the annihilator of an element is in particular the radical of that
annihilator, so it is an associated prime in Mathlib's sense. -/
private theorem mem_associatedPrimes_of_isAssociatedPrimeStacks {A : Type*} [CommRing A]
    {M : Type*} [AddCommGroup M] [Module A M] {p : Ideal A}
    (h : IsAssociatedPrimeStacks A M p) : p ∈ associatedPrimes A M := by
  obtain ⟨hp, m, hm⟩ := h
  rw [Submodule.colon_span] at hm
  exact ⟨hp, m, by rw [hm, hp.radical]⟩

/-- **Finiteness of the weakly associated primes over the closed point.**  Let `A` be a local
ring, let `A → B` be of finite type and essentially of finite presentation, and let `N` be a
`B`-module finitely presented over `B` and flat over `A`.  Then only finitely many primes of `B`
containing `𝔪_A B` are weakly associated to `N`.

By `isAssociatedPrimeStacks_quotient_of_isWeaklyAssociatedPrime_tensorProduct`, applied with
`M = A` so that `N ⊗[A] A = N`, each such prime is an associated prime — in the strict sense of
[Stacks, Tag 00LA] — of the closed fibre `N / 𝔪_A N`.  Its image in the closed fibre ring
`B / 𝔪_A B` is therefore an associated prime of the closed fibre there, and that ring is
Noetherian with the closed fibre finite over it, so there are finitely many such images
([Stacks, Tag 00LC]);  a prime containing `𝔪_A B` is recovered from its image. -/
theorem finite_isWeaklyAssociatedPrime_map_maximalIdeal_le
    {A : Type u} [CommRing A] [IsLocalRing A] {B : Type v} [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (hAB : (algebraMap A B).EssentiallyOfFinitePresentation)
    {N : Type w} [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
    [Module.FinitePresentation B N] [Module.Flat A N] :
    {J : Ideal B | IsWeaklyAssociatedPrime B N J ∧
      Ideal.map (algebraMap A B) (maximalIdeal A) ≤ J}.Finite := by
  classical
  set I : Ideal B := Ideal.map (algebraMap A B) (maximalIdeal A)
  have : IsNoetherianRing (B ⧸ I) := isNoetherianRing_quotient_map_maximalIdeal
  have hfin : (associatedPrimes (B ⧸ I) (N ⧸ (I • (⊤ : Submodule B N)))).Finite :=
    associatedPrimes.finite _ _
  refine Set.Finite.of_finite_image (f := fun J : Ideal B => Ideal.map (Ideal.Quotient.mk I) J)
    (hfin.subset ?_) ?_
  · rintro K ⟨J, ⟨hJw, hJI⟩, rfl⟩
    have hJp : J.IsPrime := hJw.isPrime B N
    have hwt : IsWeaklyAssociatedPrime B (N ⊗[A] A) J :=
      isWeaklyAssociatedPrime_of_linearEquiv
        (TensorProduct.AlgebraTensorModule.rid A B N).symm hJw
    have hass : IsAssociatedPrimeStacks B (N ⧸ (I • (⊤ : Submodule B N))) J :=
      isAssociatedPrimeStacks_quotient_of_isWeaklyAssociatedPrime_tensorProduct hAB hJI hwt
    exact mem_associatedPrimes_of_isAssociatedPrimeStacks
      (isAssociatedPrimeStacks_quotient_ring hJI hass)
  · intro J₁ h₁ J₂ h₂ heq
    have h := congrArg (Ideal.comap (Ideal.Quotient.mk I)) heq
    rwa [Ideal.comap_map_mk h₁.2, Ideal.comap_map_mk h₂.2] at h

section Localized

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
  {N : Type w} [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- The localization `S_Σ` of `S` at the image of `R ∖ 𝔭` is of finite type over `R_𝔭`, and the
structure map `R_𝔭 → S_Σ` is essentially of finite presentation.

Both come from the identification of `S_Σ` with the base change `R_𝔭 ⊗_R S`, which is of finite
presentation over `R_𝔭`:  the canonical map from that base change to `S_Σ` exhibits `S_Σ` as a
localization of it at a submonoid of units, hence is an isomorphism. -/
private theorem finiteType_and_essentiallyOfFinitePresentation_localization
    [Algebra.FinitePresentation R S] (p : Ideal R) [p.IsPrime] :
    Algebra.FiniteType (Localization.AtPrime p)
        (Localization (Algebra.algebraMapSubmonoid S p.primeCompl)) ∧
      RingHom.EssentiallyOfFinitePresentation (algebraMap (Localization.AtPrime p)
        (Localization (Algebra.algebraMapSubmonoid S p.primeCompl))) := by
  set A := Localization.AtPrime p
  set Sig := Algebra.algebraMapSubmonoid S p.primeCompl
  set B := Localization Sig
  let C := A ⊗[R] S
  let : Algebra S C := Algebra.TensorProduct.rightAlgebra
  have : IsLocalization Sig C := IsLocalization.tensorRight A p.primeCompl
  let φ : C →ₐ[A] B := Algebra.TensorProduct.lift (Algebra.ofId A B)
    (IsScalarTower.toAlgHom R S B) fun _ _ => Commute.all _ _
  let : Algebra C B := φ.toRingHom.toAlgebra
  have : IsScalarTower S C B := IsScalarTower.of_algebraMap_eq fun s => by
    change _ = φ (1 ⊗ₜ s)
    rw [Algebra.TensorProduct.lift_tmul]
    simp
  have : IsScalarTower A C B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  have hloc := IsLocalization.isLocalization_of_submonoid_le C B Sig Sig le_rfl
  have hunit : Submonoid.map (algebraMap S C) Sig ≤ IsUnit.submonoid C := by
    rintro _ ⟨s, hs, rfl⟩
    exact IsLocalization.map_units C ⟨s, hs⟩
  let e : C ≃ₐ[C] B := IsLocalization.atUnits C _ hunit
  have : Algebra.FinitePresentation A C := Algebra.FinitePresentation.baseChange A
  exact ⟨Algebra.FiniteType.of_surjective (e.restrictScalars A).toAlgHom e.surjective,
    RingHom.EssentiallyOfFinitePresentation.of_isLocalization (C := C)
      (Submonoid.map (algebraMap S C) Sig)⟩

/-- A prime of `S` weakly associated to `N` and disjoint from `Σ` extends to a prime of `S_Σ`
weakly associated to `N_Σ` ([Stacks, Tag 05C9]). -/
theorem isWeaklyAssociatedPrime_map_localization_of_disjoint (Sig : Submonoid S) {q : Ideal S}
    (hq : IsWeaklyAssociatedPrime S N q) (hdisj : Disjoint (Sig : Set S) (q : Set S)) :
    IsWeaklyAssociatedPrime (Localization Sig) (LocalizedModule Sig N)
      (Ideal.map (algebraMap S (Localization Sig)) q) := by
  have hqp : q.IsPrime := hq.isPrime S N
  have hrange : (⟨q, hqp⟩ : PrimeSpectrum S) ∈ Set.range (localizationComap Sig) := by
    rw [PrimeSpectrum.localization_comap_range (Localization Sig) Sig]
    exact hdisj
  obtain ⟨P, hP, hPeq⟩ : (⟨q, hqp⟩ : PrimeSpectrum S) ∈
      localizationComap Sig '' weakAss (Localization Sig) (LocalizedModule Sig N) := by
    rw [← weakAss_localizedModule_eq_image Sig,
      ← weakAss_inter_image_eq_weakAss_localizedModule Sig]
    exact ⟨hq, hrange⟩
  have hPq : P.asIdeal.comap (algebraMap S (Localization Sig)) = q :=
    congrArg PrimeSpectrum.asIdeal hPeq
  have hmapP : Ideal.map (algebraMap S (Localization Sig)) q = P.asIdeal := by
    rw [← hPq]
    exact IsLocalization.map_under Sig (Localization Sig) P.asIdeal
  rwa [hmapP]

/-- Only finitely many primes of `S` weakly associated to `N` lie over a given prime `𝔭` of `R`.

Localizing `R` at `𝔭` and `S` at the image of `R ∖ 𝔭` turns this into
`finite_isWeaklyAssociatedPrime_map_maximalIdeal_le`:  the primes of `S` lying over `𝔭`
correspond to the primes of `S_Σ` containing `𝔪_{R_𝔭} S_Σ`, weak association is preserved by that
correspondence ([Stacks, Tag 05C9]), and `N_Σ` is finitely presented over `S_Σ` and flat over
`R_𝔭`. -/
private theorem finite_isWeaklyAssociatedPrime_comap_eq
    [Algebra.FinitePresentation R S] [Module.FinitePresentation S N] [Module.Flat R N]
    (p : Ideal R) [p.IsPrime] :
    {q : Ideal S | IsWeaklyAssociatedPrime S N q ∧ q.comap (algebraMap R S) = p}.Finite := by
  classical
  obtain ⟨hft, hefp⟩ := finiteType_and_essentiallyOfFinitePresentation_localization (S := S) p
  set Sig := Algebra.algebraMapSubmonoid S p.primeCompl
  let : Module (Localization.AtPrime p) (LocalizedModule Sig N) :=
    Module.compHom _ (algebraMap (Localization.AtPrime p) (Localization Sig))
  have : IsScalarTower (Localization.AtPrime p) (Localization Sig) (LocalizedModule Sig N) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R (Localization.AtPrime p) (LocalizedModule Sig N) :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      change (algebraMap (Localization.AtPrime p) (Localization Sig)
        (algebraMap R (Localization.AtPrime p) r)) • x = r • x
      rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime p) (Localization Sig),
        IsScalarTower.algebraMap_apply R S (Localization Sig),
        IsScalarTower.algebraMap_smul, algebraMap_smul]
  have : Module.Flat R (LocalizedModule Sig N) :=
    Module.Flat.of_isLocalizedModule_tower Sig (LocalizedModule.mkLinearMap Sig N)
  have : Module.Flat (Localization.AtPrime p) (LocalizedModule Sig N) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl
      (LocalizedModule Sig N)).mpr ‹_›
  have : Algebra.FiniteType (Localization.AtPrime p) (Localization Sig) := hft
  have hdisj : ∀ q : Ideal S, q.comap (algebraMap R S) = p →
      Disjoint (Sig : Set S) (q : Set S) := by
    intro q hq
    rw [Set.disjoint_left]
    rintro x ⟨r, hr, rfl⟩ hx
    exact hr (hq ▸ Ideal.mem_comap.mpr hx)
  have hunder : ∀ q : Ideal S, q.IsPrime → q.comap (algebraMap R S) = p →
      Ideal.comap (algebraMap S (Localization Sig))
        (Ideal.map (algebraMap S (Localization Sig)) q) = q := fun q hqp hq =>
    IsLocalization.under_map_of_isPrime_disjoint Sig (Localization Sig) hqp (hdisj q hq)
  refine Set.Finite.of_finite_image
    (f := fun q : Ideal S => Ideal.map (algebraMap S (Localization Sig)) q)
    ((finite_isWeaklyAssociatedPrime_map_maximalIdeal_le (N := LocalizedModule Sig N)
      hefp).subset ?_) ?_
  · rintro K ⟨q, ⟨hq, hqp'⟩, rfl⟩
    dsimp only
    refine ⟨isWeaklyAssociatedPrime_map_localization_of_disjoint Sig hq (hdisj q hqp'), ?_⟩
    have h1 : Ideal.map (algebraMap (Localization.AtPrime p) (Localization Sig))
        (maximalIdeal (Localization.AtPrime p)) =
        Ideal.map (algebraMap S (Localization Sig)) (Ideal.map (algebraMap R S) p) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map,
        ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
    rw [h1]
    exact Ideal.map_mono (Ideal.map_le_iff_le_comap.mpr hqp'.ge)
  · intro q₁ h₁ q₂ h₂ heq
    have h := congrArg (Ideal.comap (algebraMap S (Localization Sig))) heq
    rwa [hunder q₁ (h₁.1.isPrime S N) h₁.2, hunder q₂ (h₂.1.isPrime S N) h₂.2] at h

/-- **Finitely many weakly associated primes, for a finitely presented flat module.**  Let
`R → S` be a ring map of finite presentation and let `N` be a finitely presented `S`-module which
is flat as an `R`-module.  If `R` has only finitely many weakly associated primes, then so
does `N`.

This is the finiteness consequence of the inclusion `⊆` of [Stacks, Tag 05IJ] together with
[Stacks, Tag 05AF], in the composite shape in which the proof of [Stacks, Tag 05IK] uses the two:
the contraction clause of `isWeaklyAssociatedPrime_comap_tensorProduct`, applied with `M = R`,
spreads `WeakAss_S(N)` over the finitely many primes of `WeakAss_R(R)`, and the fibre over each
of them is finite by `finite_isWeaklyAssociatedPrime_comap_eq`.

The hypotheses are finite presentation, where Tag 05IJ asks only for finite type;  see the
section "The finiteness statement" of the module documentation. -/
theorem finite_weaklyAssociatedPrimes_of_flat_of_finitePresentation
    [Algebra.FinitePresentation R S] [Module.FinitePresentation S N] [Module.Flat R N]
    (hR : (weaklyAssociatedPrimes R R).Finite) : (weaklyAssociatedPrimes S N).Finite := by
  have hcover : weaklyAssociatedPrimes S N ⊆
      ⋃ p ∈ weaklyAssociatedPrimes R R,
        {q : Ideal S | IsWeaklyAssociatedPrime S N q ∧ q.comap (algebraMap R S) = p} := by
    intro q hq
    have hcon : IsWeaklyAssociatedPrime R R (q.comap (algebraMap R S)) :=
      isWeaklyAssociatedPrime_comap_tensorProduct (N := N) (M := R) hR
        (isWeaklyAssociatedPrime_of_linearEquiv
          (TensorProduct.AlgebraTensorModule.rid R S N).symm hq)
    exact Set.mem_biUnion hcon ⟨hq, rfl⟩
  refine (hR.biUnion fun p hp => ?_).subset hcover
  have : p.IsPrime := hp.isPrime R R
  exact finite_isWeaklyAssociatedPrime_comap_eq (N := N) p

end Localized

end Finiteness

end Stacks.WeaklyAssociatedPrimes

end
