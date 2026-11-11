module

public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.RingTheory.Flat.Localization

/-!
# Flatness and localization over an algebra

Let `R → A` be a ring map and `M` an `A`-module. Localizing `M` at a submonoid of `A` preserves
flatness over `R`, and flatness of `M` over `R` can be read off from localizations of `M`:

* at elements `g₁, …, gₘ` generating the unit ideal of `A` (each `M_{gᵢ}` flat over `R`);
* at all primes `𝔮` of `A` (each `M_𝔮` flat over `R_𝔭`, with `𝔭 = R ∩ 𝔮`);
* at all maximal ideals `𝔪` of `A` (each `M_𝔪` flat over `R_𝔭`, with `𝔭 = R ∩ 𝔪`).

## Main results

* `flat_of_isLocalizedModule_of_flat_tower`: if `M` is `R`-flat and `M → M'` is a localization of
  `A`-modules at a submonoid of `A`, then `M'` is `R`-flat.
* `flat_iff_forall_flat_localizedModule_away`: Stacks 00HT (5).
* `flat_iff_forall_flat_localizedModule_atPrime_comap`: Stacks 00HT (6).
* `flat_iff_forall_flat_localizedModule_atMaximal_comap`: Stacks 00HT (7).

## References

* [Stacks Project, Tag 00HT](https://stacks.math.columbia.edu/tag/00HT)
-/

@[expose] public section

open Module TensorProduct

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A]

/-- Let `R → A` be a ring map and `S ⊆ A` a submonoid. If `M` is an `R`-flat `A`-module and
`g : M → M'` is a localization of `A`-modules at `S`, then `M'` is `R`-flat: the map
`N ⊗_R M' → P ⊗_R M'` induced by an injection `N → P` is the localization at `S` of the injective
map `N ⊗_R M → P ⊗_R M`. -/
theorem flat_of_isLocalizedModule_of_flat_tower (S : Submonoid A)
    {M : Type*} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    {M' : Type*} [AddCommGroup M'] [Module R M'] [Module A M'] [IsScalarTower R A M']
    (g : M →ₗ[A] M') [IsLocalizedModule S g] [Module.Flat R M] :
    Module.Flat R M' := by
  rw [Module.Flat.iff_lTensor_injectiveₛ]
  intro P _ _ N
  have h1 : Function.Injective (AlgebraTensorModule.lTensor A M N.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  rw [← AlgebraTensorModule.coe_lTensor (A := A),
    ← IsLocalizedModule.map_lTensor (S := S) (f := N.subtype) (g := g)]
  exact IsLocalizedModule.map_injective S _ _ _ h1

/-- Stacks 00HT (5). Let `R → A` be a ring map, `M` an `A`-module and `g₁, …, gₘ ∈ A` elements
generating the unit ideal of `A`. Then `M` is flat over `R` if and only if each localization
`M_{gᵢ}` is flat over `R`. -/
@[stacks 00HT "(5)"]
theorem flat_iff_forall_flat_localizedModule_away
    (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    {m : ℕ} (g : Fin m → A) (hg : Ideal.span (Set.range g) = ⊤) :
    Module.Flat R M ↔ ∀ i, Module.Flat R (LocalizedModule.Away (g i) M) := by
  refine ⟨fun _ i ↦ flat_of_isLocalizedModule_of_flat_tower (Submonoid.powers (g i))
    (LocalizedModule.mkLinearMap (Submonoid.powers (g i)) M), fun h ↦ ?_⟩
  refine Module.flat_of_isLocalized_span A M (Set.range g) hg
    (fun r ↦ LocalizedModule.Away r.1 M)
    (fun r ↦ LocalizedModule.mkLinearMap (Submonoid.powers r.1) M) fun r ↦ ?_
  obtain ⟨_, i, rfl⟩ := r
  exact h i

/-- For a prime `𝔮` of `A` over `𝔭 = R ∩ 𝔮`, with `M_𝔮` an `R_𝔭`-module through `R_𝔭 → A_𝔮`, if
`M` is `R`-flat then `M_𝔮` is `R_𝔭`-flat. -/
theorem flat_localizedModule_atPrime_comap_of_flat
    (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.Flat R M] (Q : Ideal A) [Q.IsPrime] :
    letI : (Q.comap (algebraMap R A)).IsPrime := Ideal.comap_isPrime _ _
    letI : Q.LiesOver (Q.comap (algebraMap R A)) := ⟨rfl⟩
    letI : Algebra (Localization.AtPrime (Q.comap (algebraMap R A)))
                   (Localization.AtPrime Q) :=
      Localization.AtPrime.algebraOfLiesOver _ _
    letI : Module (Localization.AtPrime (Q.comap (algebraMap R A)))
                  (LocalizedModule.AtPrime Q M) :=
      Module.compHom _ (algebraMap _ (Localization.AtPrime Q))
    Module.Flat (Localization.AtPrime (Q.comap (algebraMap R A)))
      (LocalizedModule.AtPrime Q M) := by
  have : (Q.comap (algebraMap R A)).IsPrime := Ideal.comap_isPrime _ _
  have : Q.LiesOver (Q.comap (algebraMap R A)) := ⟨rfl⟩
  let : Algebra (Localization.AtPrime (Q.comap (algebraMap R A)))
                 (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver _ _
  let : Module (Localization.AtPrime (Q.comap (algebraMap R A)))
                (LocalizedModule.AtPrime Q M) :=
    Module.compHom _ (algebraMap _ (Localization.AtPrime Q))
  have : IsScalarTower R (Localization.AtPrime (Q.comap (algebraMap R A)))
      (LocalizedModule.AtPrime Q M) := by
    refine IsScalarTower.of_algebraMap_smul fun r x ↦ ?_
    change (algebraMap (Localization.AtPrime (Q.comap (algebraMap R A)))
        (Localization.AtPrime Q)) ((algebraMap R (Localization.AtPrime (Q.comap (algebraMap R A))))
          r) • x = r • x
    rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime (Q.comap (algebraMap R A)))
        (Localization.AtPrime Q) r, IsScalarTower.algebraMap_smul]
  have : Module.Flat R (LocalizedModule.AtPrime Q M) :=
    flat_of_isLocalizedModule_of_flat_tower Q.primeCompl
      (LocalizedModule.mkLinearMap Q.primeCompl M)
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime (Q.comap (algebraMap R A)))
    (Q.comap (algebraMap R A)).primeCompl (LocalizedModule.AtPrime Q M)).mpr this

/-- Stacks 00HT (6). Let `R → A` be a ring map and `M` an `A`-module. Then `M` is flat over `R` if
and only if `M_𝔮` is flat over `R_𝔭`, with `𝔭 = R ∩ 𝔮`, for every prime `𝔮` of `A`. The reverse
implication is `flat_of_flat_atPrime`. -/
@[stacks 00HT "(6)"]
theorem flat_iff_forall_flat_localizedModule_atPrime_comap
    (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] :
    Module.Flat R M ↔ ∀ (Q : Ideal A) (_ : Q.IsPrime),
        letI : (Q.comap (algebraMap R A)).IsPrime := Ideal.comap_isPrime _ _
        letI : Q.LiesOver (Q.comap (algebraMap R A)) := ⟨rfl⟩
        letI : Algebra (Localization.AtPrime (Q.comap (algebraMap R A)))
                       (Localization.AtPrime Q) :=
          Localization.AtPrime.algebraOfLiesOver _ _
        letI : Module (Localization.AtPrime (Q.comap (algebraMap R A)))
                      (LocalizedModule.AtPrime Q M) :=
          Module.compHom _ (algebraMap _ (Localization.AtPrime Q))
        Module.Flat
          (Localization.AtPrime (Q.comap (algebraMap R A)))
          (LocalizedModule.AtPrime Q M) :=
  ⟨fun _ Q _ ↦ flat_localizedModule_atPrime_comap_of_flat M Q, flat_of_flat_atPrime M⟩

/-- Stacks 00HT (7). Let `R → A` be a ring map and `M` an `A`-module. Then `M` is flat over `R` if
and only if `M_𝔪` is flat over `R_𝔭`, with `𝔭 = R ∩ 𝔪`, for every maximal ideal `𝔪` of `A`. The
reverse implication is `flat_of_flat_localizedModule_maximal`. -/
@[stacks 00HT "(7)"]
theorem flat_iff_forall_flat_localizedModule_atMaximal_comap
    (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] :
    Module.Flat R M ↔ ∀ (m : Ideal A) (_ : m.IsMaximal),
        letI : m.IsPrime := Ideal.IsMaximal.isPrime ‹_›
        letI : (m.comap (algebraMap R A)).IsPrime := Ideal.comap_isPrime _ _
        letI : m.LiesOver (m.comap (algebraMap R A)) := ⟨rfl⟩
        letI : Algebra (Localization.AtPrime (m.comap (algebraMap R A)))
                       (Localization.AtPrime m) :=
          Localization.AtPrime.algebraOfLiesOver _ _
        letI : Module (Localization.AtPrime (m.comap (algebraMap R A)))
                      (LocalizedModule.AtPrime m M) :=
          Module.compHom _ (algebraMap _ (Localization.AtPrime m))
        Module.Flat
          (Localization.AtPrime (m.comap (algebraMap R A)))
          (LocalizedModule.AtPrime m M) := by
  refine ⟨fun _ m hm ↦ ?_, flat_of_flat_localizedModule_maximal M⟩
  have : m.IsPrime := hm.isPrime
  exact flat_localizedModule_atPrime_comap_of_flat M m
