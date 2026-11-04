module

public import StacksFrontier.RingTheory.Branches.Completion.GeometricallyNormalFormalFibres
public import StacksFrontier.RingTheory.Branches.Completion.HenselizationToCompletion
import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.MinimalPrimesDirectLimit

@[expose] public section

/-!
# Branch counts of the completion of a local ring

Let `A` be a Noetherian local ring with completion `Â` and henselization `Aʰ`. The branch count
of `A` equals that of `Â` exactly when every minimal prime of `Aʰ` stays radically prime in `Â`;
completion decreases neither the ordinary nor the geometric branch count, and in dimension one
it changes neither of them.

## Main results

* `isNoetherianRing_of_isHenselization`: a henselization of a Noetherian local ring is
  Noetherian.
* `exists_ringEquiv_adicCompletion_of_isHenselization`: the completion of `A` is the completion
  of `Aʰ`, compatibly with the maps out of `A`.
* `numberOfBranches_eq_completion_iff_radical_map_minimalPrime_isPrime`: the branch counts of `A`
  and `Â` agree if and only if the radical of the extension of every minimal prime of `Aʰ` is
  prime.
* `numberOfBranches_le_and_numberOfGeometricBranches_le_completion`: contraction along
  `Aʰ → Â` is surjective on minimal primes, `Â ⊗[Aʰ] Aˢʰ` is a strict henselization of `Â`, and
  completion decreases neither the ordinary nor the geometric branch count.
* `numberOfBranches_and_numberOfGeometricBranches_eq_adicCompletion_of_dimension_one`: in
  dimension one, completion changes neither the ordinary nor the geometric branch count.

## References

* [The Stacks Project, Tag 0C29](https://stacks.math.columbia.edu/tag/0C29)
* [The Stacks Project, Tag 0C28](https://stacks.math.columbia.edu/tag/0C28)
* [The Stacks Project, Tag 0C2D](https://stacks.math.columbia.edu/tag/0C2D)
-/

universe u v w x y

open Topology
open IsLocalRing
open scoped TensorProduct

open CategoryTheory CategoryTheory.Limits

private theorem encard_eq_iff_injOn_of_finite_of_surjOn {α β : Type*} {s : Set α} {t : Set β}
    (hs : s.Finite) (ht : t.Finite) (f : α → β) (hm : Set.MapsTo f s t)
    (hf : Set.SurjOn f s t) :
    s.encard = t.encard ↔ Set.InjOn f s := by
  classical
  let sf := hs.toFinset
  let tf := ht.toFinset
  rw [hs.encard_eq_coe_toFinset_card, ht.encard_eq_coe_toFinset_card]
  constructor
  · intro hcard
    simpa [sf] using Finset.injOn_of_surjOn_of_card_le (s := sf) (t := tf) f
      (by simpa [sf, tf] using hm) (by simpa [sf, tf] using hf) (by simpa [sf, tf] using hcard.le)
  · intro hinj
    exact_mod_cast Finset.card_nbij (s := sf) (t := tf) f
      (by simpa [sf, tf] using hm) (by simpa [sf, tf] using hinj) (by simpa [sf, tf] using hf)

/-- Along a flat map whose contraction is surjective on minimal primes, the radical of the
extension of a minimal prime is prime exactly when that minimal prime has a single preimage. -/
private theorem radical_map_isPrime_iff_fiber_subsingleton
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hflat : f.Flat)
    (q : Ideal R) (hq : q ∈ minimalPrimes R)
    (hsurj : Set.SurjOn (fun Q ↦ Ideal.comap f Q) (minimalPrimes S) (minimalPrimes R)) :
    (Ideal.map f q).radical.IsPrime ↔
      ∀ Q₁ ∈ minimalPrimes S, ∀ Q₂ ∈ minimalPrimes S,
        Ideal.comap f Q₁ = q → Ideal.comap f Q₂ = q → Q₁ = Q₂ := by
  let : Algebra R S := f.toAlgebra
  have : Module.Flat R S := hflat
  have hgd : Algebra.HasGoingDown R S := Algebra.HasGoingDown.of_flat
  have hminimal (Q : Ideal S) (hQ : Q ∈ minimalPrimes S)
      (hcomap : Ideal.comap f Q = q) :
      Minimal (fun P : Ideal S ↦ P.IsPrime ∧ Ideal.map f q ≤ P) Q := by
    refine ⟨⟨hQ.isPrime, Ideal.map_le_iff_le_comap.mpr hcomap.symm.le⟩, fun P hP hPQ ↦ ?_⟩
    have : P.IsPrime := hP.1
    obtain ⟨Q₀, hQ₀, hQ₀P⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := P) bot_le
    have hQ₀Q : Q₀ ≤ Q := hQ₀P.trans hPQ
    have hQQ₀ : Q ≤ Q₀ := hQ.right ⟨hQ₀.isPrime, bot_le⟩ hQ₀Q
    exact hQQ₀.trans hQ₀P
  constructor
  · intro hrad Q₁ hQ₁ Q₂ hQ₂ hc₁ hc₂
    have hmin₁ := hminimal Q₁ hQ₁ hc₁
    have hmin₂ := hminimal Q₂ hQ₂ hc₂
    have hrle₁ : (Ideal.map f q).radical ≤ Q₁ :=
      (Ideal.IsPrime.radical_le_iff hQ₁.isPrime).mpr hmin₁.1.2
    have hrle₂ : (Ideal.map f q).radical ≤ Q₂ :=
      (Ideal.IsPrime.radical_le_iff hQ₂.isPrime).mpr hmin₂.1.2
    have h₁ : Q₁ = (Ideal.map f q).radical :=
      le_antisymm (hmin₁.2 ⟨hrad, Ideal.le_radical⟩ hrle₁) hrle₁
    have h₂ : Q₂ = (Ideal.map f q).radical :=
      le_antisymm (hmin₂.2 ⟨hrad, Ideal.le_radical⟩ hrle₂) hrle₂
    exact h₁.trans h₂.symm
  · intro hfiber
    obtain ⟨Q, hQ, hQc⟩ := hsurj hq
    have hminQ := hminimal Q hQ hQc
    have heq : (Ideal.map f q).radical = Q := by
      apply le_antisymm
      · exact (Ideal.IsPrime.radical_le_iff hQ.isPrime).mpr hminQ.1.2
      · rw [Ideal.radical_eq_sInf]
        refine le_sInf fun P hP ↦ ?_
        have : P.IsPrime := hP.2
        have : q.IsPrime := hq.isPrime
        have : P.LiesOver (Ideal.comap f P) := ⟨rfl⟩
        have hqle : q ≤ Ideal.comap f P := Ideal.map_le_iff_le_comap.mp hP.1
        obtain ⟨Q₀, hQ₀P, hQ₀prime, hQ₀over⟩ :=
          P.exists_ideal_le_liesOver_of_le (p := q) (q := Ideal.comap f P) hqle
        obtain ⟨Qmin, hQmin, hQminle⟩ :=
          Ideal.exists_minimalPrimes_le (I := ⊥) (J := Q₀) bot_le
        have hcomapQmin : Ideal.comap f Qmin = q := by
          have hle : Ideal.comap f Qmin ≤ q :=
            (Ideal.comap_mono hQminle).trans_eq hQ₀over.over.symm
          exact le_antisymm hle (hq.right ⟨hQmin.isPrime.comap f, bot_le⟩ hle)
        exact (hfiber Qmin hQmin Q hQ hcomapQmin hQc).symm ▸ hQminle.trans hQ₀P
    rw [heq]
    exact hQ.isPrime

private theorem surjOn_minimalPrimes_of_flat_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hflat : f.Flat) (hinj : Function.Injective f) :
    Set.SurjOn (fun Q ↦ Ideal.comap f Q) (minimalPrimes S) (minimalPrimes R) := by
  intro q hq
  obtain ⟨P, hPprime, hPc⟩ :=
    Ideal.exists_comap_eq_of_mem_minimalPrimes_of_injective hinj q hq
  obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := P) bot_le
  refine ⟨Q, hQ, ?_⟩
  have hQc := comap_mem_minimalPrimes_of_flat f hflat hQ
  have hle : Ideal.comap f Q ≤ q := (Ideal.comap_mono hQP).trans_eq hPc
  exact le_antisymm hle (hq.right ⟨hQc.isPrime, bot_le⟩ hle)

/-- A henselian local ring is its own henselization. -/
public theorem isHenselization_self (R : Type u) [CommRing R]
    [HenselianLocalRing R] : IsHenselization R (ResidueField R) R := by
  have het : (CommAlgCat.etale.{u} R) (CommAlgCat.of R R) := by
    show Algebra.Etale R R
    infer_instance
  exact IsHenselization.of_ind_etale.{u, u, u} inferInstance
    (CategoryTheory.ObjectProperty.le_ind (CommAlgCat.etale.{u} R) (CommAlgCat.of R R) het)
    ⟨RingEquiv.refl _, by intro x; simp⟩

/-- The completion of a local ring with finitely generated maximal ideal is henselian local. -/
public theorem henselianLocalRing_adicCompletion
    (A : Type u) [CommRing A] [IsLocalRing A] (fg : (maximalIdeal A).FG) :
    HenselianLocalRing (AdicCompletion (maximalIdeal A) A) := by
  let : IsLocalRing (AdicCompletion (maximalIdeal A) A) :=
    AdicCompletion.isLocalRing_of_fg fg
  have hcomplete : IsAdicComplete
      (maximalIdeal (AdicCompletion (maximalIdeal A) A))
      (AdicCompletion (maximalIdeal A) A) := AdicCompletion.isAdicComplete_of_fg fg
  exact ⟨fun g hg a ha ha' ↦
    (IsAdicComplete.henselianRing _ _).is_henselian g hg a ha
      (ha'.map (Ideal.Quotient.mk _))⟩

/-- Noetherianness descends along a faithfully flat algebra. -/
private theorem isNoetherianRing_of_faithfullyFlat (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Module.FaithfullyFlat R S] [IsNoetherianRing S] : IsNoetherianRing R := by
  have hS : WellFoundedGT (Submodule S S) := isNoetherian_iff'.mp (isNoetherianRing_iff.mp ‹_›)
  rw [isNoetherianRing_iff, isNoetherian_iff', wellFoundedGT_iff_monotone_chain_condition]
  intro a
  obtain ⟨n, hn⟩ := (wellFoundedGT_iff_monotone_chain_condition (α := Ideal S)).mp hS
    ⟨fun m => Ideal.map (algebraMap R S) (a m), fun i j hij => Ideal.map_mono (a.monotone hij)⟩
  exact ⟨n, fun m hm => Ideal.map_injective_of_faithfullyFlat (hn m hm)⟩

/-- A henselization of a Noetherian local ring is Noetherian. -/
@[ega "IV 18.6.6" "(v)", sga "4 VIII 4.1"]
public theorem isNoetherianRing_of_isHenselization
    (A : Type u) (Ah : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsHenselization A (ResidueField A) Ah] : IsNoetherianRing Ah := by
  obtain ⟨f⟩ := exists_algHom_adicCompletion_of_isHenselization A Ah
  have hflat : f.toRingHom.Flat := flat_of_isHenselization_algHom f
  have hlocal : IsLocalHom f.toRingHom := isLocalHom_of_isHenselization_algHom f
  let : Algebra Ah (AdicCompletion (maximalIdeal A) A) := f.toRingHom.toAlgebra
  have : Module.Flat Ah (AdicCompletion (maximalIdeal A) A) := hflat
  have : IsLocalHom (algebraMap Ah (AdicCompletion (maximalIdeal A) A)) := hlocal
  have : Module.FaithfullyFlat Ah (AdicCompletion (maximalIdeal A) A) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact isNoetherianRing_of_faithfullyFlat Ah (AdicCompletion (maximalIdeal A) A)

/-- For a Noetherian local ring `A` with henselization `Aʰ`, the completion `Â` is the completion
of `Aʰ`, compatibly with the two canonical maps out of `A`. -/
@[ega "IV 18.6.6" "(iv) for Noetherian A"]
public theorem exists_ringEquiv_adicCompletion_of_isHenselization
    (A Ah : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsHenselization A (ResidueField A) Ah] :
    ∃ e : AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal Ah) Ah,
      ∀ x : A, e (algebraMap A (AdicCompletion (maximalIdeal A) A) x) =
        algebraMap Ah (AdicCompletion (maximalIdeal Ah) Ah) (algebraMap A Ah x) := by
  have hmA : (maximalIdeal A).FG := (maximalIdeal A).fg_of_isNoetherianRing
  have h1 : (maximalIdeal A).map (algebraMap A Ah) = maximalIdeal Ah :=
    IsHenselization.map_maximalIdeal (R := A) (L := ResidueField A)
  have hmh : (maximalIdeal Ah).FG := by rw [← h1]; exact hmA.map _
  let : IsLocalRing (AdicCompletion (maximalIdeal Ah) Ah) :=
    AdicCompletion.isLocalRing_of_fg hmh
  have : IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal Ah) Ah))
      (AdicCompletion (maximalIdeal Ah) Ah) := AdicCompletion.isAdicComplete_of_fg hmh
  have : IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal A) A))
      (AdicCompletion (maximalIdeal A) A) := AdicCompletion.isAdicComplete_of_fg hmA
  have : IsAdicComplete (maximalIdeal A) (AdicCompletion (maximalIdeal A) A) :=
    AdicCompletion.isAdicComplete hmA
  have : IsAdicComplete (maximalIdeal Ah) (AdicCompletion (maximalIdeal Ah) Ah) :=
    AdicCompletion.isAdicComplete hmh
  have : IsLocalHom (algebraMap A Ah) := IsHenselization.isLocalHom (L := ResidueField A)
  have : IsLocalHom (algebraMap Ah (AdicCompletion (maximalIdeal Ah) Ah)) :=
    AdicCompletion.algebraMap_isLocalHom_of_fg hmh
  have : IsScalarTower A Ah (AdicCompletion (maximalIdeal Ah) Ah) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocalHom (algebraMap A (AdicCompletion (maximalIdeal Ah) Ah)) := by
    rw [IsScalarTower.algebraMap_eq A Ah (AdicCompletion (maximalIdeal Ah) Ah)]; infer_instance
  have hmax_hat : maximalIdeal (AdicCompletion (maximalIdeal A) A) =
      (maximalIdeal A).map (algebraMap A (AdicCompletion (maximalIdeal A) A)) :=
    AdicCompletion.maximalIdeal_eq_map_of_fg hmA
  have hmax_hh : maximalIdeal (AdicCompletion (maximalIdeal Ah) Ah) =
      (maximalIdeal Ah).map (algebraMap Ah (AdicCompletion (maximalIdeal Ah) Ah)) :=
    AdicCompletion.maximalIdeal_eq_map_of_fg hmh
  obtain ⟨f⟩ := exists_algHom_adicCompletion_of_isHenselization A Ah
  have hfK : (maximalIdeal Ah).map f.toRingHom ≤
      maximalIdeal (AdicCompletion (maximalIdeal A) A) := by
    rw [← h1, Ideal.map_map, hmax_hat]
    exact le_of_eq (congrArg (fun g : A →+* AdicCompletion (maximalIdeal A) A =>
      (maximalIdeal A).map g) f.comp_algebraMap)
  obtain ⟨v, hv⟩ := exists_algHom_adicCompletion_of_map_le (maximalIdeal Ah)
    (maximalIdeal (AdicCompletion (maximalIdeal A) A)) f hfK
  have huKeq : (maximalIdeal A).map
      (algebraMap A (AdicCompletion (maximalIdeal Ah) Ah)) =
      maximalIdeal (AdicCompletion (maximalIdeal Ah) Ah) := by
    rw [IsScalarTower.algebraMap_eq A Ah (AdicCompletion (maximalIdeal Ah) Ah),
      ← Ideal.map_map, h1]
    exact hmax_hh.symm
  obtain ⟨u, hu⟩ := exists_algHom_adicCompletion_of_map_le (maximalIdeal A)
    (maximalIdeal (AdicCompletion (maximalIdeal Ah) Ah))
    (Algebra.ofId A (AdicCompletion (maximalIdeal Ah) Ah)) (le_of_eq huKeq)
  have hvu : v.comp u = AlgHom.id A (AdicCompletion (maximalIdeal A) A) :=
    algHom_ext_adicCompletion (maximalIdeal A) hmA _ _
  have : HenselianLocalRing (AdicCompletion (maximalIdeal Ah) Ah) :=
    henselianLocalRing_adicCompletion Ah hmh
  have hun := HenselianLocalRing.indEtaleAlgHom_unique
    (R := A) (Rh := Ah) (Sh := AdicCompletion (maximalIdeal Ah) Ah)
    (IsHenselization.ind_etale (R := A) (L := ResidueField A) (Rh := Ah))
    (IsHenselization.residueField_map_bijective (R := A) (Rh := Ah)).2
  have hloc (g : Ah →ₐ[A] AdicCompletion (maximalIdeal Ah) Ah) : IsLocalHom g :=
    ⟨(isLocalHom_of_isHenselization_algHom g).map_nonunit⟩
  have h_uf : u.comp f = IsScalarTower.toAlgHom A Ah
      (AdicCompletion (maximalIdeal Ah) Ah) := (hun _ (hloc _)).trans (hun _ (hloc _)).symm
  have huv : ∀ y : AdicCompletion (maximalIdeal Ah) Ah, u (v y) = y := by
    have hw : ({ (u.comp v).toRingHom with
        commutes' := fun x => by
          show u (v (algebraMap Ah (AdicCompletion (maximalIdeal Ah) Ah) x)) = _
          rw [hv x]
          exact congrArg (fun k : Ah →ₐ[A] AdicCompletion (maximalIdeal Ah) Ah => k x) h_uf } :
        AdicCompletion (maximalIdeal Ah) Ah →ₐ[Ah] AdicCompletion (maximalIdeal Ah) Ah) =
        AlgHom.id Ah (AdicCompletion (maximalIdeal Ah) Ah) :=
      algHom_ext_adicCompletion (maximalIdeal Ah) hmh _ _
    intro y
    exact congrArg (fun k : AdicCompletion (maximalIdeal Ah) Ah →ₐ[Ah]
      AdicCompletion (maximalIdeal Ah) Ah => k y) hw
  refine ⟨(AlgEquiv.ofAlgHom u v (AlgHom.ext huv) hvu).toRingEquiv, fun x => ?_⟩
  show u (algebraMap A (AdicCompletion (maximalIdeal A) A) x) = _
  rw [hu x]
  exact IsScalarTower.algebraMap_apply A Ah (AdicCompletion (maximalIdeal Ah) Ah) x

/-- An `A`-algebra map from a henselization of `A` to the completion `Â` is flat, and contraction
along it is surjective on minimal primes. -/
private theorem flat_and_surjOn_minimalPrimes_of_isHenselization_algHom
    (A Ah : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah] [IsHenselization A (ResidueField A) Ah]
    (f : Ah →ₐ[A] AdicCompletion (maximalIdeal A) A) :
    f.toRingHom.Flat ∧ Set.SurjOn (fun Q ↦ Ideal.comap f.toRingHom Q)
      (minimalPrimes (AdicCompletion (maximalIdeal A) A)) (minimalPrimes Ah) := by
  have hflat : f.toRingHom.Flat := flat_of_isHenselization_algHom f
  let : Algebra Ah (AdicCompletion (maximalIdeal A) A) := f.toRingHom.toAlgebra
  have : Module.Flat Ah (AdicCompletion (maximalIdeal A) A) := hflat
  have : IsLocalHom (algebraMap Ah (AdicCompletion (maximalIdeal A) A)) :=
    isLocalHom_of_isHenselization_algHom f
  have : Module.FaithfullyFlat Ah (AdicCompletion (maximalIdeal A) A) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact ⟨hflat, surjOn_minimalPrimes_of_flat_injective f.toRingHom hflat
    (FaithfulSMul.algebraMap_injective Ah (AdicCompletion (maximalIdeal A) A))⟩

/-- A Noetherian local ring and its completion have the same number of branches if and only if
the radical of the extension of every minimal prime of a henselization to the completion is
prime. -/
@[stacks 0C29]
theorem numberOfBranches_eq_completion_iff_radical_map_minimalPrime_isPrime
    (A Ah : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsHenselization A (ResidueField A) Ah] :
    let Ahat := AdicCompletion (maximalIdeal A) A
    ∃ hAhatLocal : IsLocalRing Ahat,
      letI : IsLocalRing Ahat := hAhatLocal
      ∃ hAhatMapLocal : IsLocalHom (algebraMap A Ahat),
        letI : IsLocalHom (algebraMap A Ahat) := hAhatMapLocal
        ∃ f : Ah →+* Ahat,
          (∀ x : A, f (algebraMap A Ah x) = algebraMap A Ahat x) ∧
          ∃ hAhatHenselization : IsHenselization Ahat (ResidueField Ahat) Ahat,
            letI : IsHenselization Ahat (ResidueField Ahat) Ahat := hAhatHenselization
            (numberOfBranches A Ah =
                numberOfBranches Ahat Ahat ↔
              ∀ q ∈ minimalPrimes Ah, (Ideal.map f q).radical.IsPrime) := by
  classical
  dsimp only
  obtain ⟨f⟩ := exists_algHom_adicCompletion_of_isHenselization A Ah
  obtain ⟨hflat, hsurj⟩ := flat_and_surjOn_minimalPrimes_of_isHenselization_algHom A Ah f
  have : HenselianLocalRing (AdicCompletion (maximalIdeal A) A) :=
    henselianLocalRing_adicCompletion A (maximalIdeal A).fg_of_isNoetherianRing
  refine ⟨inferInstance,
    AdicCompletion.algebraMap_isLocalHom_of_fg (maximalIdeal A).fg_of_isNoetherianRing,
    f.toRingHom, f.commutes,
    isHenselization_self (AdicCompletion (maximalIdeal A) A), ?_⟩
  have hAhatfin : (minimalPrimes (AdicCompletion (maximalIdeal A) A)).Finite :=
    minimalPrimes.finite_of_isNoetherianRing _
  have hAhfin : (minimalPrimes Ah).Finite := (hAhatfin.image _).subset hsurj
  rw [numberOfBranches, numberOfBranches, eq_comm,
    encard_eq_iff_injOn_of_finite_of_surjOn hAhatfin hAhfin _
      (fun _ hQ ↦ comap_mem_minimalPrimes_of_flat f.toRingHom hflat hQ) hsurj]
  constructor
  · intro hinjOn q hq
    rw [radical_map_isPrime_iff_fiber_subsingleton f.toRingHom hflat q hq hsurj]
    intro Q₁ hQ₁ Q₂ hQ₂ hc₁ hc₂
    exact hinjOn hQ₁ hQ₂ (hc₁.trans hc₂.symm)
  · intro hprime Q₁ hQ₁ Q₂ hQ₂ hc
    have hq := comap_mem_minimalPrimes_of_flat f.toRingHom hflat hQ₁
    exact (radical_map_isPrime_iff_fiber_subsingleton f.toRingHom hflat _ hq hsurj).mp
      (hprime _ hq) Q₁ hQ₁ Q₂ hQ₂ rfl hc.symm

private theorem encard_le_of_surjOn {α β : Type*} [Nonempty α] [Nonempty β]
    {s : Set α} {t : Set β} (f : α → β) (h : Set.SurjOn f s t) : t.encard ≤ s.encard := by
  let g := Function.invFunOn f s
  have hr : Set.RightInvOn g f t := h.rightInvOn_invFunOn
  apply Set.encard_le_encard_of_injOn (f := g)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := h hy
    exact Function.invFunOn_apply_mem hx
  · intro y hy z hz heq
    apply_fun f at heq
    simpa only [hr hy, hr hz] using heq

/-- A henselization with respect to one separable closure of the residue field is a
henselization with respect to any other. -/
private theorem isHenselization_of_isSepClosure
    {R : Type u} [CommRing R] [IsLocalRing R]
    (L : Type v) [Field L] [Algebra (ResidueField R) L] [IsSepClosure (ResidueField R) L]
    (M : Type*) [Field M] [Algebra (ResidueField R) M] [IsSepClosure (ResidueField R) M]
    {Rh : Type*} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [IsHenselization R L Rh] : IsHenselization R M Rh where
  henselian := IsHenselization.henselian (R := R) (L := L)
  ind_etale := IsHenselization.ind_etale (R := R) (L := L) (Rh := Rh)
  exists_residueFieldEquiv := by
    obtain ⟨e, he⟩ := IsHenselization.exists_residueFieldEquiv (R := R) (L := L) (Rh := Rh)
    refine ⟨(IsSepClosure.equiv (ResidueField R) M L).toRingEquiv.trans e, fun x => ?_⟩
    rw [RingEquiv.trans_apply]
    show e ((IsSepClosure.equiv (ResidueField R) M L)
      (algebraMap (ResidueField R) M (residue R x))) = _
    rw [AlgEquiv.commutes]
    exact he x

/-- `IsHenselization` transfers along an isomorphism of algebras over the base. -/
private theorem isHenselization_of_algEquiv {R : Type u} [CommRing R] [IsLocalRing R]
    {L : Type v} [Field L] [Algebra (ResidueField R) L]
    {S T : Type u} [CommRing S] [IsLocalRing S] [Algebra R S] [IsHenselization R L S]
    [CommRing T] [IsLocalRing T] [Algebra R T] (e : S ≃ₐ[R] T) : IsHenselization R L T where
  henselian := by
    have : HenselianLocalRing S := IsHenselization.henselian (R := R) (L := L)
    exact Stacks.Henselian.henselianLocalRing_of_ringEquiv e.toRingEquiv
  ind_etale := ((CommAlgCat.etale.{u} R).ind.{u}).prop_of_iso
    (CommAlgCat.isoMk (ULift.algEquiv.trans (e.trans ULift.algEquiv.symm) :
      ULift.{u} S ≃ₐ[R] ULift.{u} T))
    (IsHenselization.ind_etale (R := R) (L := L) (Rh := S))
  exists_residueFieldEquiv := by
    have : IsLocalHom e.toRingEquiv.toRingHom :=
      isLocalHom_of_leftInverse e.symm.toRingEquiv e.toRingEquiv.left_inv
    have hsurj : Function.Surjective (ResidueField.map e.toRingEquiv.toRingHom) := by
      intro y
      obtain ⟨t, rfl⟩ := residue_surjective y
      obtain ⟨s, rfl⟩ := e.surjective t
      exact ⟨residue S s, ResidueField.map_residue _ s⟩
    let e' : ResidueField S ≃+* ResidueField T :=
      RingEquiv.ofBijective _ ⟨RingHom.injective _, hsurj⟩
    obtain ⟨eS, heS⟩ := IsHenselization.exists_residueFieldEquiv (R := R) (L := L) (Rh := S)
    refine ⟨eS.trans e', fun x => ?_⟩
    rw [RingEquiv.trans_apply, heS x]
    show ResidueField.map e.toRingEquiv.toRingHom (residue S (algebraMap R S x)) = _
    rw [ResidueField.map_residue]
    exact congrArg (residue T) (e.commutes x)

/-- A separable closure of the residue field of `A` is one of the residue field of `Â`. -/
private theorem exists_algebra_residueField_adicCompletion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (κsep : Type v) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep] :
    ∃ alg : Algebra (ResidueField (AdicCompletion (maximalIdeal A) A)) κsep,
      letI := alg
      (∀ x : ResidueField A,
          algebraMap (ResidueField (AdicCompletion (maximalIdeal A) A)) κsep
            (ResidueField.map (algebraMap A (AdicCompletion (maximalIdeal A) A)) x) =
            algebraMap (ResidueField A) κsep x) ∧
        IsSepClosure (ResidueField (AdicCompletion (maximalIdeal A) A)) κsep := by
  let B := AdicCompletion (maximalIdeal A) A
  let eB : ResidueField A ≃ₐ[A] ResidueField B := residueFieldAlgEquiv_completion A
  let alg : Algebra (ResidueField B) κsep :=
    ((algebraMap (ResidueField A) κsep).comp eB.symm.toRingHom).toAlgebra
  refine ⟨alg, fun x => ?_, ?_⟩
  · show algebraMap (ResidueField A) κsep (eB.symm (eB x)) = _
    rw [eB.symm_apply_apply]
  · let : Algebra (ResidueField B) (ResidueField A) := eB.symm.toRingHom.toAlgebra
    let eBase : ResidueField B ≃ₐ[ResidueField B] ResidueField A :=
      { eB.symm.toRingEquiv with commutes' := fun _ => rfl }
    let : Algebra.IsSeparable (ResidueField B) (ResidueField A) :=
      AlgEquiv.Algebra.isSeparable eBase
    let : IsScalarTower (ResidueField B) (ResidueField A) κsep :=
      IsScalarTower.of_algebraMap_eq' rfl
    exact ⟨IsSepClosure.sep_closed (ResidueField A),
      Algebra.IsSeparable.trans (ResidueField B) (ResidueField A) κsep⟩

/-- For a Noetherian local ring `A` with henselization `Aʰ` and strict henselization `Aˢʰ`, there
is a map `Aʰ → Â` along which contraction is surjective on minimal primes, `Â ⊗[Aʰ] Aˢʰ` is a
strict henselization of `Â`, and completion decreases neither the number of branches nor the
number of geometric branches. -/
@[stacks 0C28]
theorem numberOfBranches_le_and_numberOfGeometricBranches_le_completion
    (A Ah Ash : Type u)
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsHenselization A (ResidueField A) Ah]
    (κsep : Type v) [Field κsep] [Algebra (ResidueField A) κsep]
    [IsSepClosure (ResidueField A) κsep]
    [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash] [Algebra Ah Ash]
    [IsScalarTower A Ah Ash] [IsHenselization A κsep Ash]
    [IsLocalHom (algebraMap Ah Ash)] :
    let Ahat := AdicCompletion (maximalIdeal A) A
    ∃ hAhatLocal : IsLocalRing Ahat,
      letI : IsLocalRing Ahat := hAhatLocal
      ∃ hAhatMapLocal : IsLocalHom (algebraMap A Ahat),
        letI : IsLocalHom (algebraMap A Ahat) := hAhatMapLocal
        ∃ f : Ah →+* Ahat,
          (∀ x : A, f (algebraMap A Ah x) = algebraMap A Ahat x) ∧
          Set.SurjOn (fun q => Ideal.comap f q) (minimalPrimes Ahat) (minimalPrimes Ah) ∧
          letI : Algebra Ah Ahat := f.toAlgebra
          ∃ hAhatHenselization : IsHenselization Ahat (ResidueField Ahat) Ahat,
            letI : IsHenselization Ahat (ResidueField Ahat) Ahat := hAhatHenselization
            numberOfBranches A Ah ≤ numberOfBranches Ahat Ahat ∧
            ∃ algKhat : Algebra (ResidueField Ahat) κsep,
              letI : Algebra (ResidueField Ahat) κsep := algKhat
              (∀ x : ResidueField A,
                algebraMap (ResidueField Ahat) κsep
                    (ResidueField.map (algebraMap A Ahat) x) =
                  algebraMap (ResidueField A) κsep x) ∧
              ∃ hKsep : IsSepClosure (ResidueField Ahat) κsep,
                letI : IsSepClosure (ResidueField Ahat) κsep := hKsep
                ∃ hTensorLocal : IsLocalRing (Ahat ⊗[Ah] Ash),
                  letI : IsLocalRing (Ahat ⊗[Ah] Ash) := hTensorLocal
                  ∃ hTensorHenselization : IsHenselization Ahat κsep (Ahat ⊗[Ah] Ash),
                    letI : IsHenselization Ahat κsep (Ahat ⊗[Ah] Ash) := hTensorHenselization
                    numberOfGeometricBranches A κsep Ash ≤
                      numberOfGeometricBranches Ahat κsep (Ahat ⊗[Ah] Ash) := by
  dsimp only
  obtain ⟨f⟩ := exists_algHom_adicCompletion_of_isHenselization A Ah
  obtain ⟨hflat, hsurj⟩ := flat_and_surjOn_minimalPrimes_of_isHenselization_algHom A Ah f
  let : Algebra Ah (AdicCompletion (maximalIdeal A) A) := f.toRingHom.toAlgebra
  have htower : IsScalarTower A Ah (AdicCompletion (maximalIdeal A) A) :=
    IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  have : Module.Flat Ah (AdicCompletion (maximalIdeal A) A) := hflat
  have hhensB : HenselianLocalRing (AdicCompletion (maximalIdeal A) A) :=
    henselianLocalRing_adicCompletion A (maximalIdeal A).fg_of_isNoetherianRing
  refine ⟨inferInstance,
    AdicCompletion.algebraMap_isLocalHom_of_fg (maximalIdeal A).fg_of_isNoetherianRing,
    f.toRingHom, f.commutes, hsurj,
    isHenselization_self (AdicCompletion (maximalIdeal A) A), ?_⟩
  refine ⟨encard_le_of_surjOn _ hsurj, ?_⟩
  obtain ⟨algK, hcompat, hKsep⟩ := exists_algebra_residueField_adicCompletion A κsep
  refine ⟨algK, hcompat, hKsep, ?_⟩
  let : Algebra (ResidueField (AdicCompletion (maximalIdeal A) A)) κsep := algK
  have : IsSepClosure (ResidueField (AdicCompletion (maximalIdeal A) A)) κsep := hKsep
  have : IsHenselization (AdicCompletion (maximalIdeal A) A)
      (ResidueField (AdicCompletion (maximalIdeal A) A)) (AdicCompletion (maximalIdeal A) A) :=
    isHenselization_self (AdicCompletion (maximalIdeal A) A)
  obtain ⟨Bsh, hBshRing, hBshLocal, hBBsh, -, -, -, hBshHens, -, hBshInd, -, eBsh0⟩ :=
    IsLocalRing.exists_strictHenselization (AdicCompletion (maximalIdeal A) A)
      (AdicCompletion (maximalIdeal A) A)
      (IsHenselization.ind_etale_of_universe_le
        (R := AdicCompletion (maximalIdeal A) A)
        (L := ResidueField (AdicCompletion (maximalIdeal A) A))
        (Rh := AdicCompletion (maximalIdeal A) A))
      (IsHenselization.residueField_map_bijective
        (R := AdicCompletion (maximalIdeal A) A)
        (Rh := AdicCompletion (maximalIdeal A) A)).2
      (SeparableClosure (ResidueField (AdicCompletion (maximalIdeal A) A)))
  let : CommRing Bsh := hBshRing
  let : IsLocalRing Bsh := hBshLocal
  let : Algebra (AdicCompletion (maximalIdeal A) A) Bsh := hBBsh
  let : IsHenselization (AdicCompletion (maximalIdeal A) A)
      (SeparableClosure (ResidueField (AdicCompletion (maximalIdeal A) A))) Bsh :=
    IsHenselization.of_ind_etale hBshHens hBshInd eBsh0
  have : IsHenselization (AdicCompletion (maximalIdeal A) A) κsep Bsh :=
    isHenselization_of_isSepClosure
      (SeparableClosure (ResidueField (AdicCompletion (maximalIdeal A) A))) κsep
  let : Algebra A Bsh :=
    ((algebraMap (AdicCompletion (maximalIdeal A) A) Bsh).comp
      (algebraMap A (AdicCompletion (maximalIdeal A) A))).toAlgebra
  have : IsScalarTower A (AdicCompletion (maximalIdeal A) A) Bsh :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra Ah Bsh :=
    ((algebraMap (AdicCompletion (maximalIdeal A) A) Bsh).comp
      (algebraMap Ah (AdicCompletion (maximalIdeal A) A))).toAlgebra
  have : IsScalarTower Ah (AdicCompletion (maximalIdeal A) A) Bsh :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A Ah Bsh := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap (AdicCompletion (maximalIdeal A) A) Bsh
        (algebraMap A (AdicCompletion (maximalIdeal A) A) x) = _
    rw [IsScalarTower.algebraMap_apply A Ah (AdicCompletion (maximalIdeal A) A) x]
    rfl
  obtain ⟨eRsh, heRsh⟩ :=
    IsHenselization.exists_residueFieldEquiv (R := A) (L := κsep) (Rh := Ash)
  obtain ⟨eSsh, heSsh⟩ :=
    IsHenselization.exists_residueFieldEquiv
      (R := AdicCompletion (maximalIdeal A) A) (L := κsep) (Rh := Bsh)
  obtain ⟨g, hgLocal, -, ebc, hebc⟩ :=
    IsLocalRing.IsHenselization.exists_algEquiv_tensorProduct_strictHenselization
      (Rp := A) (Sq := AdicCompletion (maximalIdeal A) A) (Rh := Ah)
      (Sh := AdicCompletion (maximalIdeal A) A) (Rsh := Ash) (Ssh := Bsh) (ksep := κsep)
      (AdicCompletion.residueField_map_bijective A) hcompat eRsh heRsh eSsh heSsh
  have hTensorLocal : IsLocalRing (AdicCompletion (maximalIdeal A) A ⊗[Ah] Ash) :=
    ebc.toRingEquiv.isLocalRing
  let : IsLocalRing (AdicCompletion (maximalIdeal A) A ⊗[Ah] Ash) := hTensorLocal
  refine ⟨hTensorLocal, isHenselization_of_algEquiv ebc, ?_⟩
  let gR : Ash →ₐ[Ah] AdicCompletion (maximalIdeal A) A ⊗[Ah] Ash :=
    Algebra.TensorProduct.includeRight
  let : Algebra Ash (AdicCompletion (maximalIdeal A) A ⊗[Ah] Ash) := gR.toRingHom.toAlgebra
  have hflatT : Module.Flat Ash (AdicCompletion (maximalIdeal A) A ⊗[Ah] Ash) := by
    let swap : (AdicCompletion (maximalIdeal A) A ⊗[Ah] Ash) ≃ₐ[Ash]
        (Ash ⊗[Ah] AdicCompletion (maximalIdeal A) A) :=
      AlgEquiv.ofRingEquiv
        (f := (Algebra.TensorProduct.comm Ah
          (AdicCompletion (maximalIdeal A) A) Ash).toRingEquiv)
        (fun x => DFunLike.congr_fun
          (Algebra.TensorProduct.comm_comp_includeRight Ah
            (AdicCompletion (maximalIdeal A) A) Ash) x)
    exact Module.Flat.of_linearEquiv swap.toLinearEquiv
  have hebcLocal : IsLocalHom ebc.toRingEquiv.toRingHom :=
    isLocalHom_of_leftInverse ebc.symm.toRingEquiv ebc.toRingEquiv.left_inv
  have : IsLocalHom (algebraMap Ash (AdicCompletion (maximalIdeal A) A ⊗[Ah] Ash)) := by
    have hcomp : algebraMap Ash (AdicCompletion (maximalIdeal A) A ⊗[Ah] Ash) =
        ebc.toRingEquiv.toRingHom.comp g.toRingHom := RingHom.ext fun a => (hebc a).symm
    have : IsLocalHom g.toRingHom := ⟨hgLocal.map_nonunit⟩
    rw [hcomp]
    exact RingHom.isLocalHom_comp _ _
  have : Module.FaithfullyFlat Ash (AdicCompletion (maximalIdeal A) A ⊗[Ah] Ash) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinjT : Function.Injective
      (algebraMap Ash (AdicCompletion (maximalIdeal A) A ⊗[Ah] Ash)) :=
    FaithfulSMul.algebraMap_injective Ash _
  exact encard_le_of_surjOn _
    (surjOn_minimalPrimes_of_flat_injective _ hflatT hinjT)

/-- A minimal prime of a one-dimensional Noetherian local ring cuts out a one-dimensional
component. -/
private theorem ringKrullDim_quotient_minimalPrime_eq_one
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : ringKrullDim R = 1) (q : Ideal R) (hq : q ∈ minimalPrimes R) :
    ringKrullDim (R ⧸ q) = 1 := by
  let : q.IsPrime := hq.isPrime
  have hq_height : q.height = 0 := Ideal.height_eq_zero_iff.mpr hq
  have hq_not_maximal : ¬ q.IsMaximal := by
    intro hqmax
    have hq_eq : q = maximalIdeal R := IsLocalRing.eq_maximalIdeal hqmax
    have hmax_height : (maximalIdeal R).height = 1 := by
      exact_mod_cast IsLocalRing.maximalIdeal_height_eq_ringKrullDim.trans hR
    rw [hq_eq, hmax_height] at hq_height
    exact one_ne_zero hq_height
  apply le_antisymm ((ringKrullDim_quotient_le q).trans_eq hR)
  have hpos : (0 : WithBot ℕ∞) < ringKrullDim (R ⧸ q) := by
    apply lt_of_not_ge
    intro hle
    have hzero : Ring.KrullDimLE 0 (R ⧸ q) := Ring.krullDimLE_iff.mpr hle
    have hall :=
      Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mp hzero
    exact hq_not_maximal (hall q (by
      rw [Ideal.minimalPrimes_eq_subsingleton_self]
      exact Set.mem_singleton q))
  exact_mod_cast (Order.succ_le_of_lt hpos)

/-- Two henselizations of the same local ring with isomorphic residue extensions are isomorphic
as algebras over it. The two henselizations lie in universes independent of each other and of
that of the base. -/
@[ega "IV 18.6.6" "more general"]
public theorem exists_algEquiv_of_isHenselization_independentUniverses
    (R : Type u) (H : Type x) (H' : Type y) [CommRing R] [IsLocalRing R]
    [CommRing H] [IsLocalRing H] [Algebra R H]
    [CommRing H'] [IsLocalRing H'] [Algebra R H']
    (L : Type v) (L' : Type w) [Field L] [Field L']
    [Algebra (ResidueField R) L] [Algebra (ResidueField R) L']
    [IsHenselization R L H] [IsHenselization R L' H']
    (e : L ≃ₐ[ResidueField R] L') : Nonempty (H ≃ₐ[R] H') := by
  let : HenselianLocalRing H := IsHenselization.henselian (R := R) (L := L)
  let : HenselianLocalRing H' := IsHenselization.henselian (R := R) (L := L')
  obtain ⟨i, hi⟩ := IsHenselization.exists_residueFieldEquiv (R := R) (L := L) (Rh := H)
  obtain ⟨i', hi'⟩ := IsHenselization.exists_residueFieldEquiv (R := R) (L := L') (Rh := H')
  obtain ⟨f, -⟩ := IsLocalRing.IsHenselization.exists_algEquiv_of_residueFieldEquiv
    (IsHenselization.ind_etale (R := R) (L := L) (Rh := H))
    (IsHenselization.ind_etale (R := R) (L := L') (Rh := H'))
    i (e.toRingEquiv.trans i') fun r => by
      rw [← hi r, ← hi' r, i.symm_apply_apply, RingEquiv.symm_trans_apply,
        i'.symm_apply_apply]
      exact (e.symm.commutes (residue R r)).symm
  exact ⟨f⟩

/-- Two henselizations of the same local ring with isomorphic residue extensions are isomorphic
as algebras over it, for the base and both henselizations in one universe. -/
public theorem exists_algEquiv_of_isHenselization
    (R H H' : Type u) [CommRing R] [IsLocalRing R]
    [CommRing H] [IsLocalRing H] [Algebra R H]
    [CommRing H'] [IsLocalRing H'] [Algebra R H']
    (L : Type v) (L' : Type w) [Field L] [Field L']
    [Algebra (ResidueField R) L] [Algebra (ResidueField R) L']
    [IsHenselization R L H] [IsHenselization R L' H']
    (e : L ≃ₐ[ResidueField R] L') : Nonempty (H ≃ₐ[R] H') :=
  exists_algEquiv_of_isHenselization_independentUniverses R H H' L L' e

/-- Isomorphic rings have the same number of minimal primes. -/
public theorem encard_minimalPrimes_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : (minimalPrimes R).encard = (minimalPrimes S).encard := by
  have he : RingHom.ker e.toRingHom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot e.toRingHom).mp e.injective
  have himage : minimalPrimes S = Ideal.map e.toRingHom '' minimalPrimes R := by
    simpa [he] using
      Ideal.minimalPrimes_map_of_surjective (f := e.toRingHom) e.surjective (⊥ : Ideal R)
  rw [himage]
  symm
  apply Set.InjOn.encard_image
  intro I _ J _ h
  simpa only [Ideal.comap_map_of_surjective e.toRingHom e.surjective,
    Ideal.comap_bot_of_injective e.toRingHom e.injective, sup_bot_eq] using
    congrArg (Ideal.comap e.toRingHom) h

/-- A one-dimensional henselian Noetherian local ring has as many minimal primes as its
completion. -/
private theorem encard_minimalPrimes_eq_completion
    (R : Type u) [CommRing R] [IsNoetherianRing R] [HenselianLocalRing R]
    (hdim : ringKrullDim R = 1) :
    (minimalPrimes R).encard =
      (minimalPrimes (AdicCompletion (maximalIdeal R) R)).encard := by
  let : IsHenselization R (ResidueField R) R := isHenselization_self R
  let S := AdicCompletion (maximalIdeal R) R
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  let f : R →+* S := algebraMap R S
  obtain ⟨g, hg, hq⟩ :=
    exists_minimalPrime_henselization_radical_map_eq_of_quotient_dimension_one R R
  have hgf : g = f := RingHom.ext fun x => hg x
  subst g
  have hdimS : ringKrullDim S = 1 :=
    (_root_.ringKrullDim_adicCompletion_maximalIdeal (A := R)).symm.trans hdim
  have hrepr (q : Ideal S) (hqmin : q ∈ minimalPrimes S) :
      q = (Ideal.map f (q.comap f)).radical := by
    obtain ⟨p, hp, hpq⟩ := hq q hqmin
      (ringKrullDim_quotient_minimalPrime_eq_one hdimS q hqmin)
    have : p.IsPrime := hp.isPrime
    have hcp : q.comap f = p := by
      rw [hpq, Ideal.comap_radical]
      show (Ideal.comap (algebraMap R S) (Ideal.map (algebraMap R S) p)).radical = p
      rw [Ideal.comap_map_eq_self_of_faithfullyFlat, hp.isPrime.radical]
    rw [hcp, hpq]
  have hflat : f.Flat := inferInstanceAs (Module.Flat R S)
  have hsurj : Set.SurjOn (Ideal.comap f) (minimalPrimes S) (minimalPrimes R) :=
    surjOn_minimalPrimes_of_flat_injective f hflat (AdicCompletion.of_injective (maximalIdeal R) R)
  have hmaps : Set.MapsTo (Ideal.comap f) (minimalPrimes S) (minimalPrimes R) :=
    fun _ hQ ↦ comap_mem_minimalPrimes_of_flat f hflat hQ
  have hinj : Set.InjOn (Ideal.comap f) (minimalPrimes S) := by
    intro q hq q' hq' hc
    rw [hrepr q hq, hrepr q' hq', hc]
  rw [← hmaps.image_subset.antisymm hsurj, hinj.encard_image]

/-- Completion preserves the ordinary and the geometric number of branches of a one-dimensional
Noetherian local ring. -/
@[stacks 0C2D]
theorem numberOfBranches_and_numberOfGeometricBranches_eq_adicCompletion_of_dimension_one
    (A Ah AhatH Ash AhatSh : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsHenselization A (ResidueField A) Ah]
    [CommRing AhatH] [IsLocalRing AhatH]
    [Algebra (AdicCompletion (maximalIdeal A) A) AhatH]
    [IsHenselization (AdicCompletion (maximalIdeal A) A)
      (ResidueField (AdicCompletion (maximalIdeal A) A)) AhatH]
    (ksep : Type v) [Field ksep] [Algebra (ResidueField A) ksep]
    [IsSepClosure (ResidueField A) ksep]
    [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash] [IsHenselization A ksep Ash]
    (khatsep : Type w) [Field khatsep]
    [Algebra (ResidueField (AdicCompletion (maximalIdeal A) A)) khatsep]
    [IsSepClosure (ResidueField (AdicCompletion (maximalIdeal A) A)) khatsep]
    [CommRing AhatSh] [IsLocalRing AhatSh]
    [Algebra (AdicCompletion (maximalIdeal A) A) AhatSh]
    [IsHenselization (AdicCompletion (maximalIdeal A) A) khatsep AhatSh]
    (hdim : ringKrullDim A = 1) :
    numberOfBranches A Ah =
        numberOfBranches (AdicCompletion (maximalIdeal A) A) AhatH ∧
      numberOfGeometricBranches A ksep Ash =
        numberOfGeometricBranches
          (AdicCompletion (maximalIdeal A) A) khatsep AhatSh := by
  let Ahat := AdicCompletion (maximalIdeal A) A
  have : HenselianLocalRing Ah := IsHenselization.henselian A (ResidueField A)
  have : HenselianLocalRing Ash := IsHenselization.henselian A ksep
  have : IsLocalHom (algebraMap A Ah) := IsHenselization.isLocalHom (L := ResidueField A)
  have : IsLocalHom (algebraMap A Ash) := IsHenselization.isLocalHom (L := ksep)
  have hind := IsHenselization.ind_etale (R := A) (L := ResidueField A) (Rh := Ah)
  have hbij := (IsHenselization.residueField_map_bijective (R := A) (Rh := Ah)).2
  let f : Ah →ₐ[A] Ash := HenselianLocalRing.indEtaleAlgHom (R := A) (Rh := Ah) (Sh := Ash)
    hind hbij
  have hf : IsLocalHom f :=
    HenselianLocalRing.isLocalHom_indEtaleAlgHom (R := A) (Rh := Ah) (Sh := Ash) hind hbij
  let : Algebra Ah Ash := f.toRingHom.toAlgebra
  have : IsScalarTower A Ah Ash := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  have : IsLocalHom (algebraMap Ah Ash) := ⟨hf.map_nonunit⟩
  have hprops := isNoetherianRing_iff_henselizations_and_completion_properties.{u, v, u}
    A Ah Ash ksep
  have : IsNoetherianRing Ah := hprops.1.1.mp inferInstance
  have : IsNoetherianRing Ash := hprops.1.2.mp inferInstance
  have hdims := ringKrullDim_eq_henselization_eq_strictHenselization A Ah Ash ksep
  have hdimAh : ringKrullDim Ah = 1 := hdims.1.symm.trans hdim
  have hdimAsh : ringKrullDim Ash = 1 := hdims.2.symm.trans hdimAh
  obtain ⟨hAhatLocal, _, _, _, _, _, _, e, _, _, _, _, hbase⟩ := hprops.2 inferInstance
  let : IsLocalRing Ahat := hAhatLocal
  have : HenselianLocalRing Ahat :=
    henselianLocalRing_adicCompletion A (maximalIdeal A).fg_of_isNoetherianRing
  have : IsHenselization Ahat (ResidueField Ahat) Ahat := isHenselization_self Ahat
  obtain ⟨eH⟩ := exists_algEquiv_of_isHenselization Ahat Ahat AhatH
    (ResidueField Ahat) (ResidueField Ahat) AlgEquiv.refl
  constructor
  · show (minimalPrimes Ah).encard = (minimalPrimes AhatH).encard
    exact (encard_minimalPrimes_eq_completion Ah hdimAh).trans
      ((encard_minimalPrimes_eq_of_ringEquiv e.symm).trans
        (encard_minimalPrimes_eq_of_ringEquiv eH.toRingEquiv))
  · let : Algebra Ah Ahat :=
      (e.symm.toRingHom.comp (algebraMap Ah (AdicCompletion (maximalIdeal Ah) Ah))).toAlgebra
    obtain ⟨_, algKhat, _, hKsep, hTensorLocal, hTensorHenselization, ef, _⟩ := hbase
    let : Algebra (ResidueField Ahat) ksep := algKhat
    have : IsSepClosure (ResidueField Ahat) ksep := hKsep
    let T := Ahat ⊗[Ah] Ash
    let : IsLocalRing T := hTensorLocal
    have : IsHenselization Ahat ksep T := hTensorHenselization
    have : HenselianLocalRing T := IsHenselization.henselian Ahat ksep
    have : IsNoetherianRing T :=
      (isNoetherianRing_iff_henselizations Ahat Ahat T ksep).2.mp inferInstance
    have hdimAhat : ringKrullDim Ahat = 1 :=
      (_root_.ringKrullDim_adicCompletion_maximalIdeal (A := A)).symm.trans hdim
    have hdimT : ringKrullDim T = 1 :=
      (ringKrullDim_eq_henselization_eq_strictHenselization
        Ahat Ahat T ksep).2.symm.trans hdimAhat
    obtain ⟨eT⟩ := exists_algEquiv_of_isHenselization Ahat T AhatSh ksep khatsep
      (IsSepClosure.equiv (ResidueField Ahat) ksep khatsep)
    show (minimalPrimes Ash).encard = (minimalPrimes AhatSh).encard
    exact (encard_minimalPrimes_eq_completion Ash hdimAsh).trans
      ((encard_minimalPrimes_eq_of_ringEquiv ef.symm).trans
        ((encard_minimalPrimes_eq_completion T hdimT).symm.trans
          (encard_minimalPrimes_eq_of_ringEquiv eT.toRingEquiv)))


end
