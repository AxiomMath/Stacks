module

public import StacksFrontier.RingTheory.Etale.PushoutLift.Descent
public import StacksFrontier.RingTheory.Etale.PushoutLift.Auxiliary
public import StacksFrontier.RingTheory.Etale.Lifting
public import Mathlib.RingTheory.Ideal.Prod
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.TensorProduct.Pi
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.Prod

/-!
# Stacks 0ALT: a pushout argument

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `J ⊆ A` a nilpotent ideal. Write `A₀ = A ⧸ J`
and, for a finite type `A`-algebra `C`, `C₀ = C ⧸ J C`. Given a finite type `A₀`-algebra `B₀`
sitting in a commutative diagram

```
C  --->  C₀  =  C ⧸ JC
          ^
          |
         B₀
          ^
          |
A  --->  A₀  =  A ⧸ J
```

such that `Spec C → Spec A` is étale over `Spec A \ V(I)`, such that `Spec B₀ → Spec A₀` is étale
over `Spec A₀ \ V(I A₀)`, and such that `B₀ → C₀` is étale and induces an isomorphism
`B₀ ⧸ I B₀ = C₀ ⧸ I C₀`, the diagram can be filled in: there is a finite type `A`-algebra `B` with
`B ⧸ JB = B₀`, with `B → C` étale, and with `Spec B → Spec A` étale over `Spec A \ V(I)`
(`Stacks.Etale.exists_finiteType_etale_lift`). This is Stacks 0ALT.

## Proof

The source glues `Spec C` to the étale lift of `Spec B₀ \ V(I B₀)` along their common open part,
in the category of algebraic spaces, and recognises the result as affine. We give the ring-level
version of this argument.

Write `I = (g₁, …, gᵣ)`. The ring map `B₀ → Γ₀ = C₀ × ∏ᵢ (B₀)_{gᵢ}` is étale and faithfully flat
(the first factor covers `V(I B₀)`, the others its complement), and `Γ₀` lifts to the
`A`-algebra `Γ = C × L`, where `L` is the étale lift of `∏ᵢ (B₀)_{gᵢ}` along `A → A₀`
(Stacks 04D1); `Γ` is étale over `Spec A \ V(I)`. The Čech groupoid `Γ₀ ⇉ Γ₀ ⊗[B₀] Γ₀` lifts to an
effective groupoid `Γ ⇉ Δ` (`Stacks.Etale.PushoutLift.exists_effective_groupoid`): this is the
pushout of the source, presented by its étale chart `Γ`, together with the affineness of finite
order thickenings of affine spaces (`Module.Descent.SquareZero.isEffective_of_pow_eq_bot`). The
ring `B` of the thickening is the descent of `Γ` (`Stacks.Etale.PushoutLift.exists_thickening`):
`B → Γ` is étale and faithfully flat, and `B ⧸ J B = B₀`. Then `B → C` is étale as `C` is a
factor of `Γ`, `B` is of finite type because `B₀` is and `J` is nilpotent, and `B` is étale over
`Spec A \ V(I)` by faithfully flat descent from `Γ`
(`Stacks.Etale.PushoutLift.etale_away_of_faithfullyFlat`).

## Implementation notes

The statement has the shape of `Stacks.Etale.exists_finiteType_etale_lift_of_isNilpotent`: the
diagram is encoded by scalar tower instances, `A₀` and `C₀` are literal quotients, "étale over
`Spec A \ V(I)`" is stated pointwise with `Algebra.IsEtaleAt`, and the isomorphism
`B₀ ⧸ I B₀ = C₀ ⧸ I C₀` is bijectivity of the corresponding `Ideal.quotientMap`.

## References

* [Stacks Project, Tag 0ALT](https://stacks.math.columbia.edu/tag/0ALT)
* [Stacks Project, Tag 04D1](https://stacks.math.columbia.edu/tag/04D1)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
-/

@[expose] public section

open TensorProduct

universe u

namespace Stacks.Etale.PushoutLift

section Setup

/-- From pointwise étaleness at the primes avoiding an element, étaleness of the localization. -/
theorem formallyEtale_away_of_forall {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {f : S} (h : ∀ q : Ideal S, ∀ _ : q.IsPrime, f ∉ q → Algebra.IsEtaleAt R q) :
    Algebra.FormallyEtale R (Localization.Away f) :=
  Algebra.basicOpen_subset_etaleLocus_iff.mp fun q hq => h q.asIdeal q.isPrime hq

/-- A prime of `B₀` containing `I B₀` lies under a prime of `C₀` when `B₀ ⧸ I B₀ → C₀ ⧸ I C₀` is
bijective. -/
theorem exists_isPrime_comap_eq_of_map_le {A B₀ C₀ : Type*} [CommRing A] [CommRing B₀]
    [CommRing C₀] [Algebra A B₀] [Algebra A C₀] [Algebra B₀ C₀] [IsScalarTower A B₀ C₀]
    (I : Ideal A)
    (hsurjC : ∀ c : C₀, ∃ b : B₀, c - algebraMap B₀ C₀ b ∈ I.map (algebraMap A C₀))
    (hinjC : ∀ b : B₀, algebraMap B₀ C₀ b ∈ I.map (algebraMap A C₀) →
      b ∈ I.map (algebraMap A B₀))
    (p : Ideal B₀) [p.IsPrime] (hp : I.map (algebraMap A B₀) ≤ p) :
    ∃ P : Ideal C₀, P.IsPrime ∧ P.comap (algebraMap B₀ C₀) = p := by
  have hf : Function.Surjective
      ((Ideal.Quotient.mk (I.map (algebraMap A C₀))).comp (algebraMap B₀ C₀)) := fun y => by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨b, hb⟩ := hsurjC c
    refine ⟨b, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq, ← neg_sub]
    exact neg_mem hb
  have hker : RingHom.ker ((Ideal.Quotient.mk (I.map (algebraMap A C₀))).comp
      (algebraMap B₀ C₀)) ≤ p := fun b hb =>
    hp (hinjC b (Ideal.Quotient.eq_zero_iff_mem.mp (RingHom.mem_ker.mp hb)))
  have := Ideal.map_isPrime_of_surjective hf hker
  refine ⟨(p.map ((Ideal.Quotient.mk (I.map (algebraMap A C₀))).comp (algebraMap B₀ C₀))).comap
    (Ideal.Quotient.mk _), Ideal.comap_isPrime _ _, ?_⟩
  rw [Ideal.comap_comap, Ideal.comap_map_of_surjective' _ hf, sup_eq_left.mpr hker]

/-- Some generator of `I` lies outside a prime `q` that does not contain `I`. -/
private theorem exists_notMem_of_span_eq {R : Type*} [CommRing R] {n : ℕ} {g : Fin n → R}
    {I q : Ideal R} (hg : Ideal.span (Set.range g) = I) (h : ¬ I ≤ q) : ∃ i, g i ∉ q := by
  by_contra! h'
  exact h (hg ▸ Ideal.span_le.mpr (Set.range_subset_iff.mpr h'))

/-- **The chart `C₀ × ∏ᵢ (B₀)_{gᵢ}` is faithfully flat over `B₀`.** -/
theorem faithfullyFlat_prod_away {A B₀ C₀ : Type u} [CommRing A] [CommRing B₀] [CommRing C₀]
    [Algebra A B₀] [Algebra A C₀] [Algebra B₀ C₀] [IsScalarTower A B₀ C₀] [Module.Flat B₀ C₀]
    (I : Ideal A) {n : ℕ} (g : Fin n → A) (hI : Ideal.span (Set.range g) = I)
    (hsurjC : ∀ c : C₀, ∃ b : B₀, c - algebraMap B₀ C₀ b ∈ I.map (algebraMap A C₀))
    (hinjC : ∀ b : B₀, algebraMap B₀ C₀ b ∈ I.map (algebraMap A C₀) →
      b ∈ I.map (algebraMap A B₀)) :
    Module.FaithfullyFlat B₀ (C₀ × ∀ i, Localization.Away (algebraMap A B₀ (g i))) := by
  classical
  set L₀ := ∀ i, Localization.Away (algebraMap A B₀ (g i))
  have : Module.Flat B₀ L₀ := inferInstance
  have : Module.Flat B₀ (C₀ × L₀) := Module.Flat.prod
  refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_
  by_cases hp : I.map (algebraMap A B₀) ≤ p.asIdeal
  · obtain ⟨P, hP, hPp⟩ := exists_isPrime_comap_eq_of_map_le I hsurjC hinjC p.asIdeal hp
    refine ⟨⟨P.comap (RingHom.fst C₀ L₀), Ideal.comap_isPrime _ _⟩, ?_⟩
    ext1
    show Ideal.comap (algebraMap B₀ (C₀ × L₀)) (P.comap (RingHom.fst C₀ L₀)) = p.asIdeal
    rw [Ideal.comap_comap]
    exact hPp
  · obtain ⟨i, hi⟩ : ∃ i, g i ∉ p.asIdeal.comap (algebraMap A B₀) :=
      exists_notMem_of_span_eq hI (mt Ideal.map_le_iff_le_comap.mpr hp)
    set f := algebraMap A B₀ (g i)
    have hd : Disjoint (Submonoid.powers f : Set B₀) p.asIdeal := by
      rw [Set.disjoint_left]
      rintro _ ⟨k, rfl⟩ hk
      exact hi (p.isPrime.mem_of_pow_mem k hk)
    have hQ := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f)
      (Localization.Away f) p.asIdeal p.isPrime hd
    have hQp := IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers f)
      (Localization.Away f) p.isPrime hd
    let Q : Ideal (C₀ × L₀) := ((p.asIdeal.map (algebraMap B₀ (Localization.Away f))).comap
      (Pi.evalRingHom (fun i => Localization.Away (algebraMap A B₀ (g i))) i)).comap
        (RingHom.snd C₀ L₀)
    refine ⟨⟨Q, Ideal.comap_isPrime _ _⟩, ?_⟩
    ext1
    show Ideal.comap (algebraMap B₀ (C₀ × L₀)) (Ideal.comap (RingHom.snd C₀ L₀)
      (Ideal.comap (Pi.evalRingHom (fun i => Localization.Away (algebraMap A B₀ (g i))) i)
        (p.asIdeal.map (algebraMap B₀ (Localization.Away f))))) = p.asIdeal
    rw [Ideal.comap_comap, Ideal.comap_comap]
    exact hQp

/-- **The chart `C × L` is étale over `Spec A \ V(I)`**, in the base change form. -/
theorem formallyEtale_tensorProduct_prod {A C L : Type u} [CommRing A] [CommRing C] [CommRing L]
    [Algebra A C] [Algebra A L] [Algebra.FormallyEtale A L] (I : Ideal A)
    (hC : ∀ x ∈ I, Algebra.FormallyEtale A (Localization.Away (algebraMap A C x)))
    (T : Type u) [CommRing T] [Algebra A T] (hT : I.map (algebraMap A T) = ⊤) :
    Algebra.FormallyEtale T (T ⊗[A] (C × L)) := by
  have : Algebra.FormallyEtale T (T ⊗[A] C) := formallyEtale_tensorProduct_of_map_eq_top I hC hT
  have := formallyEtale_prod T (T ⊗[A] C) (T ⊗[A] L)
  exact Algebra.FormallyEtale.of_equiv (Algebra.TensorProduct.prodRight A T T C L).symm

/-- **The localizations of the chart `C × L` at elements of `I` are étale.** -/
theorem etale_away_prod {A C L : Type u} [CommRing A] [CommRing C] [CommRing L]
    [Algebra A C] [Algebra A L] [Algebra.Etale A L] (x : A)
    (hC : Algebra.Etale A (Localization.Away (algebraMap A C x))) :
    Algebra.Etale A (Localization.Away (algebraMap A (C × L) x)) := by
  set Cx := Localization.Away (algebraMap A C x)
  set Lx := Localization.Away (algebraMap A L x)
  let : Algebra (C × L) (Cx × Lx) :=
    (RingHom.prodMap (algebraMap C Cx) (algebraMap L Lx)).toAlgebra
  have hloc := isLocalizationAway_prod (S' := Cx) (T' := Lx) (algebraMap A C x) (algebraMap A L x)
  have hx : algebraMap A (C × L) x = (algebraMap A C x, algebraMap A L x) := rfl
  rw [← hx] at hloc
  have : IsScalarTower A (C × L) (Cx × Lx) := IsScalarTower.of_algebraMap_eq fun a => by
    show (algebraMap A Cx a, algebraMap A Lx a) =
      (algebraMap C Cx (algebraMap A C a), algebraMap L Lx (algebraMap A L a))
    rw [IsScalarTower.algebraMap_apply A C Cx, IsScalarTower.algebraMap_apply A L Lx]
  have := etale_prod A Cx Lx
  exact Algebra.Etale.of_equiv
    ((IsLocalization.algEquiv (Submonoid.powers (algebraMap A (C × L) x))
      (Cx × Lx) (Localization.Away (algebraMap A (C × L) x))).restrictScalars A)

/-- Bijectivity of `B₀ ⧸ 𝔟 → C₀ ⧸ 𝔟 C₀`, stated elementwise. -/
theorem forall_sub_mem_and_mem_of_bijective_quotientMap {B₀ C₀ : Type*} [CommRing B₀]
    [CommRing C₀] [Algebra B₀ C₀] (𝔟 : Ideal B₀)
    (h : Function.Bijective (Ideal.quotientMap (𝔟.map (algebraMap B₀ C₀)) (algebraMap B₀ C₀)
      Ideal.le_comap_map)) :
    (∀ c : C₀, ∃ b : B₀, c - algebraMap B₀ C₀ b ∈ 𝔟.map (algebraMap B₀ C₀)) ∧
      ∀ b : B₀, algebraMap B₀ C₀ b ∈ 𝔟.map (algebraMap B₀ C₀) → b ∈ 𝔟 := by
  refine ⟨fun c => ?_, fun b hb => ?_⟩
  · obtain ⟨z, hz⟩ := h.2 (Ideal.Quotient.mk _ c)
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    refine ⟨b, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at hz
    rw [← neg_sub]
    exact neg_mem hz
  · rw [← Ideal.Quotient.eq_zero_iff_mem]
    refine h.1 ?_
    rw [Ideal.quotientMap_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact hb

/-- The extension of an ideal to a product of algebras is the product of its extensions. -/
theorem map_algebraMap_prod {A X Y : Type*} [CommRing A] [CommRing X] [CommRing Y] [Algebra A X]
    [Algebra A Y] (𝔞 : Ideal A) :
    𝔞.map (algebraMap A (X × Y)) = (𝔞.map (algebraMap A X)).prod (𝔞.map (algebraMap A Y)) := by
  rw [Ideal.ideal_prod_eq (𝔞.map (algebraMap A (X × Y))), Ideal.map_map, Ideal.map_map]
  rfl

/-- The kernel of a product of two reductions modulo `J` is `J` times the product. -/
theorem ker_prodMap_eq_map {A C L C₀ L₀ : Type*} [CommRing A] [CommRing C] [CommRing L]
    [CommRing C₀] [CommRing L₀] [Algebra A C] [Algebra A L] (J : Ideal A) (f : C →+* C₀)
    (φ : L →+* L₀) (hf : RingHom.ker f = J.map (algebraMap A C))
    (hφ : RingHom.ker φ = J.map (algebraMap A L)) :
    RingHom.ker (f.prodMap φ) = J.map (algebraMap A (C × L)) := by
  rw [map_algebraMap_prod, ← hf, ← hφ]
  ext ⟨c, l⟩
  rw [RingHom.mem_ker, Ideal.mem_prod, RingHom.mem_ker, RingHom.mem_ker]
  exact Prod.mk_eq_zero

/-- An ideal generates the unit ideal of `∏ᵢ (B₀)_{gᵢ}` when it contains every `gᵢ`. -/
theorem map_algebraMap_pi_away_eq_top {A B₀ : Type*} [CommRing A] [CommRing B₀] [Algebra A B₀]
    {I : Ideal A} {n : ℕ} {g : Fin n → A} (hg : ∀ i, g i ∈ I) :
    I.map (algebraMap A (∀ i, Localization.Away (algebraMap A B₀ (g i)))) = ⊤ := by
  refine eq_top_of_forall_map_eval _ fun i => ?_
  rw [Ideal.map_map]
  refine Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (hg i)) ?_
  show IsUnit (algebraMap A (Localization.Away (algebraMap A B₀ (g i))) (g i))
  rw [IsScalarTower.algebraMap_apply A B₀ (Localization.Away (algebraMap A B₀ (g i)))]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The elementwise form of `B₀ ⧸ I B₀ ≅ C₀ ⧸ I C₀` passes to `C₀ × L₀` when `I L₀ = ⊤`. -/
theorem forall_sub_mem_and_mem_prod {A B₀ C₀ L₀ : Type*} [CommRing A] [CommRing B₀]
    [CommRing C₀] [CommRing L₀] [Algebra A B₀] [Algebra A C₀] [Algebra A L₀] [Algebra B₀ C₀]
    [Algebra B₀ L₀] (I : Ideal A) (hL : I.map (algebraMap A L₀) = ⊤)
    (hsurjC : ∀ c : C₀, ∃ b : B₀, c - algebraMap B₀ C₀ b ∈ I.map (algebraMap A C₀))
    (hinjC : ∀ b : B₀, algebraMap B₀ C₀ b ∈ I.map (algebraMap A C₀) →
      b ∈ I.map (algebraMap A B₀)) :
    (∀ y : C₀ × L₀, ∃ b : B₀,
      y - algebraMap B₀ (C₀ × L₀) b ∈ I.map (algebraMap A (C₀ × L₀))) ∧
    ∀ b : B₀, algebraMap B₀ (C₀ × L₀) b ∈ I.map (algebraMap A (C₀ × L₀)) →
      b ∈ I.map (algebraMap A B₀) := by
  refine ⟨fun y => ?_, fun b hb => hinjC b ?_⟩
  · obtain ⟨b, hb⟩ := hsurjC y.1
    refine ⟨b, ?_⟩
    rw [map_algebraMap_prod, Ideal.mem_prod, hL]
    exact ⟨hb, Submodule.mem_top⟩
  · rw [map_algebraMap_prod, Ideal.mem_prod] at hb
    exact hb.1

/-- A finitely presented algebra whose localizations at generators of `I` are étale is étale at
every prime not containing `I`. -/
theorem isEtaleAt_of_etale_away {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FinitePresentation A B] {I : Ideal A} {n : ℕ} {g : Fin n → A}
    (hg : Ideal.span (Set.range g) = I)
    (h : ∀ i, Algebra.Etale A (Localization.Away (algebraMap A B (g i)))) :
    ∀ q : Ideal B, ∀ _ : q.IsPrime, ¬ I ≤ q.comap (algebraMap A B) → Algebra.IsEtaleAt A q := by
  intro q hq hIq
  obtain ⟨i, hi⟩ := exists_notMem_of_span_eq hg hIq
  exact Algebra.basicOpen_subset_etaleLocus_iff_etale.mpr (h i)
    (show (⟨q, hq⟩ : PrimeSpectrum B) ∈ PrimeSpectrum.basicOpen (algebraMap A B (g i)) from hi)

/-- An algebra étale at every prime not containing `I` is étale after inverting an element of
`I`. -/
theorem etale_away_of_isEtaleAt {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    [Algebra.FinitePresentation A C] {I : Ideal A}
    (hC : ∀ q : Ideal C, ∀ _ : q.IsPrime, ¬ I ≤ q.comap (algebraMap A C) →
      Algebra.IsEtaleAt A q) {x : A} (hx : x ∈ I) :
    Algebra.Etale A (Localization.Away (algebraMap A C x)) :=
  Algebra.basicOpen_subset_etaleLocus_iff_etale.mp fun q hq =>
    hC q.asIdeal q.isPrime fun hle => hq (hle hx)

/-- An `A ⧸ J`-algebra étale at every prime not containing `I (A ⧸ J)` is étale after inverting
an element of `I`. -/
theorem etale_away_quotient_of_isEtaleAt {A B₀ : Type*} [CommRing A] [CommRing B₀] {I J : Ideal A}
    [Algebra A B₀] [Algebra (A ⧸ J) B₀] [IsScalarTower A (A ⧸ J) B₀]
    [Algebra.FinitePresentation (A ⧸ J) B₀]
    (hB₀ : ∀ q : Ideal B₀, ∀ _ : q.IsPrime,
      ¬ I.map (Ideal.Quotient.mk J) ≤ q.comap (algebraMap (A ⧸ J) B₀) →
        Algebra.IsEtaleAt (A ⧸ J) q) {x : A} (hx : x ∈ I) :
    Algebra.Etale (A ⧸ J) (Localization.Away (algebraMap A B₀ x)) := by
  refine Algebra.basicOpen_subset_etaleLocus_iff_etale.mp fun q hq => ?_
  refine hB₀ q.asIdeal q.isPrime fun hle => hq ?_
  have := hle (Ideal.mem_map_of_mem (Ideal.Quotient.mk J) hx)
  rwa [Ideal.mem_comap, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply] at this

/-- Bijectivity of `B₀ ⧸ I B₀ → C₀ ⧸ I C₀` for an `A ⧸ J`-algebra `B₀`, stated elementwise. -/
theorem forall_sub_mem_and_mem_of_bijective_quotientMap_mk {A B₀ C₀ : Type*} [CommRing A]
    [CommRing B₀] [CommRing C₀] (I J : Ideal A) [Algebra A B₀] [Algebra (A ⧸ J) B₀]
    [IsScalarTower A (A ⧸ J) B₀] [Algebra A C₀] [Algebra B₀ C₀] [IsScalarTower A B₀ C₀]
    (hmod : Function.Bijective (Ideal.quotientMap
      (((I.map (Ideal.Quotient.mk J)).map (algebraMap (A ⧸ J) B₀)).map (algebraMap B₀ C₀))
      (algebraMap B₀ C₀) Ideal.le_comap_map)) :
    (∀ c : C₀, ∃ b : B₀, c - algebraMap B₀ C₀ b ∈ I.map (algebraMap A C₀)) ∧
      ∀ b : B₀, algebraMap B₀ C₀ b ∈ I.map (algebraMap A C₀) → b ∈ I.map (algebraMap A B₀) := by
  have hIB : ((I.map (Ideal.Quotient.mk J)).map (algebraMap (A ⧸ J) B₀)) =
      I.map (algebraMap A B₀) := by
    rw [Ideal.map_map, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  have hIC : (I.map (algebraMap A B₀)).map (algebraMap B₀ C₀) = I.map (algebraMap A C₀) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  obtain ⟨hsurjC, hinjC⟩ := forall_sub_mem_and_mem_of_bijective_quotientMap _ hmod
  rw [hIB, hIC] at hsurjC hinjC
  exact ⟨hsurjC, hinjC⟩

/-- The reduction `C × L → C₀ × L₀` of the chart is surjective with kernel `J (C × L)`. -/
theorem surjective_prodMap_and_ker_eq {A C L L₀ : Type*} [CommRing A] [CommRing C] [CommRing L]
    [CommRing L₀] [Algebra A C] [Algebra A L] [Algebra A L₀] (J : Ideal A) (ψ : L →ₐ[A] L₀)
    (hψ : Function.Surjective ψ)
    (hker : RingHom.ker (ψ : L →+* L₀) =
      (RingHom.ker (algebraMap A (A ⧸ J))).map (algebraMap A L)) :
    Function.Surjective ((algebraMap C (C ⧸ J.map (algebraMap A C))).prodMap (ψ : L →+* L₀)) ∧
      RingHom.ker ((algebraMap C (C ⧸ J.map (algebraMap A C))).prodMap (ψ : L →+* L₀)) =
        J.map (algebraMap A (C × L)) := by
  refine ⟨?_, ker_prodMap_eq_map J _ _ Ideal.mk_ker
    (by rw [hker, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker])⟩
  rintro ⟨c, l⟩
  obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨l', rfl⟩ := hψ l
  exact ⟨(c', l'), rfl⟩

/-- The product of an `A`-tower `A → C → C₀` with an `A`-algebra map `L → L₀` is an `A`-tower. -/
theorem isScalarTower_prodMap {A C L C₀ L₀ : Type*} [CommRing A] [CommRing C] [CommRing L]
    [CommRing C₀] [CommRing L₀] [Algebra A C] [Algebra A L] [Algebra A C₀] [Algebra A L₀]
    [Algebra C C₀] [IsScalarTower A C C₀] [Algebra (C × L) (C₀ × L₀)] (ψ : L →ₐ[A] L₀)
    (h : algebraMap (C × L) (C₀ × L₀) = (algebraMap C C₀).prodMap (ψ : L →+* L₀)) :
    IsScalarTower A (C × L) (C₀ × L₀) := IsScalarTower.of_algebraMap_eq fun a => by
  rw [h]
  show (algebraMap A C₀ a, algebraMap A L₀ a) = _
  rw [IsScalarTower.algebraMap_apply A C C₀]
  exact Prod.ext rfl (ψ.commutes a).symm

/-- An algebra structure on `C` through the first factor of `C × L` is an `A`-tower. -/
theorem isScalarTower_of_algebraMap_eq_fst_comp {A B C L : Type*} [CommRing A] [CommRing B]
    [CommRing C] [CommRing L] [Algebra A B] [Algebra A C] [Algebra A L] [Algebra B C]
    [Algebra B (C × L)] [IsScalarTower A B (C × L)]
    (h : algebraMap B C = (RingHom.fst C L).comp (algebraMap B (C × L))) :
    IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a => by
  rw [h, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  rfl

/-- A factor of an étale algebra is étale. -/
theorem etale_of_algebraMap_eq_fst_comp {B C L : Type*} [CommRing B] [CommRing C] [CommRing L]
    [Algebra B C] [Algebra B (C × L)] [Algebra.Etale B (C × L)]
    (h : algebraMap B C = (RingHom.fst C L).comp (algebraMap B (C × L))) :
    Algebra.Etale B C := by
  let : Algebra (C × L) C := (RingHom.fst C L).toAlgebra
  have : IsScalarTower B (C × L) C := IsScalarTower.of_algebraMap_eq fun x => DFunLike.congr_fun h x
  have : Algebra.Etale (C × L) C := inferInstance
  exact Algebra.Etale.comp B (C × L) C

end Setup

end Stacks.Etale.PushoutLift

namespace Stacks.Etale

open PushoutLift

/-- **Stacks 0ALT.** Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `J ⊆ A` a nilpotent
ideal, and consider a commutative diagram of finite type ring maps

```
C  --->  C ⧸ JC
          ^
         B₀
          ^
A  --->  A ⧸ J
```

such that `Spec C → Spec A` is étale over `Spec A \ V(I)`, such that `Spec B₀ → Spec (A ⧸ J)` is
étale over `Spec (A ⧸ J) \ V(I (A ⧸ J))`, and such that `B₀ → C ⧸ JC` is étale and induces an
isomorphism `B₀ ⧸ I B₀ = (C ⧸ JC) ⧸ I (C ⧸ JC)`. Then the diagram can be filled in: there are a
finite type `A`-algebra `B`, an `A`-algebra map `B → C` which is étale, and an isomorphism
`B ⧸ JB ≅ B₀` compatible with the maps to `C ⧸ JC`, such that `Spec B → Spec A` is étale over
`Spec A \ V(I)`. -/
@[stacks 0ALT]
theorem exists_finiteType_etale_lift
    (A C B₀ : Type u) [CommRing A] [CommRing C] [CommRing B₀]
    [IsNoetherianRing A] [Algebra A C] [Algebra.FiniteType A C]
    (I J : Ideal A) (hJ : IsNilpotent J)
    [Algebra A B₀] [Algebra (A ⧸ J) B₀] [IsScalarTower A (A ⧸ J) B₀]
    [Algebra.FiniteType (A ⧸ J) B₀]
    [Algebra (A ⧸ J) (C ⧸ J.map (algebraMap A C))]
    [IsScalarTower A (A ⧸ J) (C ⧸ J.map (algebraMap A C))]
    [Algebra B₀ (C ⧸ J.map (algebraMap A C))]
    [IsScalarTower (A ⧸ J) B₀ (C ⧸ J.map (algebraMap A C))]
    [Algebra.Etale B₀ (C ⧸ J.map (algebraMap A C))]
    (hC : ∀ q : Ideal C, ∀ _ : q.IsPrime, ¬ I ≤ q.comap (algebraMap A C) →
      Algebra.IsEtaleAt A q)
    (hB₀ : ∀ q : Ideal B₀, ∀ _ : q.IsPrime,
      ¬ I.map (Ideal.Quotient.mk J) ≤ q.comap (algebraMap (A ⧸ J) B₀) →
        Algebra.IsEtaleAt (A ⧸ J) q)
    (hmod : Function.Bijective (Ideal.quotientMap
      (((I.map (Ideal.Quotient.mk J)).map (algebraMap (A ⧸ J) B₀)).map
        (algebraMap B₀ (C ⧸ J.map (algebraMap A C))))
      (algebraMap B₀ (C ⧸ J.map (algebraMap A C))) Ideal.le_comap_map)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.FiniteType A B)
      (_ : Algebra B C) (_ : IsScalarTower A B C) (_ : Algebra.Etale B C)
      (e : (B ⧸ J.map (algebraMap A B)) ≃ₐ[A] B₀),
      (∀ q : Ideal B, ∀ _ : q.IsPrime, ¬ I ≤ q.comap (algebraMap A B) →
        Algebra.IsEtaleAt A q) ∧
      ∀ b : B, algebraMap B₀ (C ⧸ J.map (algebraMap A C))
            (e (Ideal.Quotient.mk (J.map (algebraMap A B)) b)) =
          Ideal.Quotient.mk (J.map (algebraMap A C)) (algebraMap B C b) := by
  classical
  set C₀ := C ⧸ J.map (algebraMap A C)
  have htower : IsScalarTower A B₀ C₀ := by
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    rw [IsScalarTower.algebraMap_apply A (A ⧸ J) C₀, IsScalarTower.algebraMap_apply A (A ⧸ J) B₀,
      IsScalarTower.algebraMap_apply (A ⧸ J) B₀ C₀]
  have : Algebra.FinitePresentation A C := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.FinitePresentation (A ⧸ J) B₀ :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    ((isNoetherianRing_iff_ideal_fg A).mp inferInstance I)
  have hgI : ∀ i, g i ∈ I := fun i => hg ▸ Ideal.subset_span ⟨i, rfl⟩
  have hBx : ∀ i, Algebra.Etale (A ⧸ J) (Localization.Away (algebraMap A B₀ (g i))) :=
    fun i => etale_away_quotient_of_isEtaleAt hB₀ (hgI i)
  obtain ⟨hsurjC, hinjC⟩ := forall_sub_mem_and_mem_of_bijective_quotientMap_mk I J hmod
  set L₀ := ∀ i, Localization.Away (algebraMap A B₀ (g i))
  obtain ⟨L, _, _, hL, ψL, hψL, hkerL⟩ :=
    etale_lift_along_surjection A (A ⧸ J) L₀ Ideal.Quotient.mk_surjective
  let : Algebra (C × L) (C₀ × L₀) :=
    (RingHom.prodMap (algebraMap C C₀) (ψL : L →+* L₀)).toAlgebra
  have : IsScalarTower A (C × L) (C₀ × L₀) := isScalarTower_prodMap ψL rfl
  obtain ⟨hΓ₀, hΓ₀ker⟩ : Function.Surjective (algebraMap (C × L) (C₀ × L₀)) ∧
      RingHom.ker (algebraMap (C × L) (C₀ × L₀)) = J.map (algebraMap A (C × L)) :=
    surjective_prodMap_and_ker_eq (C := C) J ψL hψL hkerL
  have : Algebra.Etale B₀ (C₀ × L₀) := etale_prod B₀ C₀ L₀
  have : Module.FaithfullyFlat B₀ (C₀ × L₀) := faithfullyFlat_prod_away I g hg hsurjC hinjC
  have hΓU : ∀ (T : Type u) [CommRing T] [Algebra A T], I.map (algebraMap A T) = ⊤ →
      Algebra.FormallyEtale T (T ⊗[A] (C × L)) :=
    fun T _ _ hT => formallyEtale_tensorProduct_prod I
      (fun _ hx => (etale_away_of_isEtaleAt hC hx).formallyEtale) T hT
  have hI := forall_sub_mem_and_mem_prod (L₀ := L₀) I (map_algebraMap_pi_away_eq_top hgI)
    hsurjC hinjC
  obtain ⟨Δ, _, _, hΔ, ψ, s, hψ, hψker, hsψ, hsA, heff⟩ :=
    exists_effective_groupoid I J hJ (B₀ := B₀) hΓ₀ hΓ₀ker hΓU hI.1 hI.2
  obtain ⟨B, _, _, _, _, π, hπ, hπker, hπcomp, hBet, hBff⟩ :=
    exists_thickening J hΓ₀ hΓ₀ker ψ s hψker hsψ hsA heff
  let : Algebra B C := ((RingHom.fst C L).comp (algebraMap B (C × L))).toAlgebra
  have : IsScalarTower A B C := isScalarTower_of_algebraMap_eq_fst_comp (L := L) rfl
  have hBC : Algebra.Etale B C := etale_of_algebraMap_eq_fst_comp (L := L) rfl
  have : Algebra.FiniteType A B₀ :=
    Algebra.FiniteType.trans (S := A ⧸ J) inferInstance inferInstance
  have hBft : Algebra.FiniteType A B := finiteType_of_surjective_of_ker hJ π hπ hπker
  have : Algebra.FinitePresentation A B := Algebra.FinitePresentation.of_finiteType.mp hBft
  let e : (B ⧸ J.map (algebraMap A B)) ≃ₐ[A] B₀ :=
    (Ideal.quotientEquivAlgOfEq A hπker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hπ)
  exact ⟨B, inferInstance, inferInstance, hBft, inferInstance, inferInstance, hBC, e,
    isEtaleAt_of_etale_away hg fun i => etale_away_of_faithfullyFlat (Γ := C × L) (g i)
      (etale_away_prod (g i) (etale_away_of_isEtaleAt hC (hgI i))),
    fun b => congrArg Prod.fst (hπcomp b)⟩

end Stacks.Etale

end
