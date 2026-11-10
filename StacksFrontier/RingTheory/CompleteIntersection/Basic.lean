module


public import Mathlib.RingTheory.Ideal.Height
public import StacksFrontier.RingTheory.CompleteIntersection.Defs
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Localizations of complete intersections over a field

Let `k` be a field and let `S` be a finite type `k`-algebra, that is, a commutative `k`-algebra
admitting a surjection of `k`-algebras `k[x₁, …, xₙ] ↠ S` for some `n ≥ 0`, equivalently
`S ≅ k[x₁, …, xₙ] / I`; in Lean, `Algebra.FiniteType k S`. Then `S` is a *global complete
intersection* over `k` if either `S` is the zero ring or there are `n, c ≥ 0` and an isomorphism
of `k`-algebras `S ≅ k[x₁, …, xₙ] / (f₁, …, f_c)` with `dim S = n - c`, and a *local complete
intersection* over `k` if there is a family `(gᵢ)` of elements of `S` with `Spec S = ⋃ᵢ D(gᵢ)`
each of whose localizations `S_{gᵢ}` is a global complete intersection over `k`. These are
`IsGlobalCompleteIntersection` and `IsLocalCompleteIntersection`, Stacks Definition 10.135.1.

Here `S_g` is the localization `S[g⁻¹]` at `{1, g, g², …}` (`Localization.Away g`), `Spec S` is
the prime spectrum, `D(g) = {p ∈ Spec S | g ∉ p}` is the standard open subset
(`PrimeSpectrum.basicOpen g`), and `dim S` is the Krull dimension `ringKrullDim S`.

Both notions are stable under inverting one element `g ∈ S`. For the global one, a presentation
of `S` by `n` variables and `c` relations gives one of `S_g` by `n + 1` variables and `c + 1`
relations, the new pair being an inverse of `g` and the relation making it one, so that the
difference `n - c` is unchanged; the content is that the dimension does not drop, which comes
from the equidimensionality of `k[x₁, …, xₙ]` together with the fact that a nonempty basic open
of the spectrum of a Jacobson ring contains a closed point. The local one follows by localizing
a covering family.

## Main results

* `isGlobalCompleteIntersection_localization` and `isLocalCompleteIntersection_localization`:
  a localization `S_g` of a global (respectively local) complete intersection over `k` is again
  one. This is Stacks Lemma 10.135.2.
* `gci_transport` and `lci_transport`: both notions are invariant under isomorphism of
  `k`-algebras.
* `localCompleteIntersection_cover_iff`: the covering condition of
  `IsLocalCompleteIntersection`, phrased there as generation of the unit ideal, says exactly that
  the basic opens `D(g)` cover the spectrum.
* `IsGlobalCompleteIntersection.finiteType`: a global complete intersection over `k` is of finite
  type over `k`.

## Implementation notes

Finite type-ness of `S` is not a hypothesis of the localization theorems: a global complete
intersection over `k` is of finite type over `k` (`IsGlobalCompleteIntersection.finiteType`).

## References

* [Stacks 00S9](https://stacks.math.columbia.edu/tag/00S9), Definition 10.135.1.
* [Stacks 00SA](https://stacks.math.columbia.edu/tag/00SA), Lemma 10.135.2.
-/

@[expose] public section

variable (k : Type*) [Field k]

/-- A global complete intersection over `k` is of finite type over `k`. -/
theorem IsGlobalCompleteIntersection.finiteType {A : Type*} [CommRing A] [Algebra k A]
    (hA : IsGlobalCompleteIntersection k A) : Algebra.FiniteType k A := by
  rcases hA with hsub | ⟨n, c, f, e, -, -⟩
  · have := hsub
    exact Module.Finite.finiteType A
  · exact Algebra.FiniteType.of_surjective e.symm.toAlgHom e.symm.surjective

/-- Inverting one element adds one variable and one relation to a presentation: if `S` is
presented over `k` by `n` variables and `c` relations, `S ≃ₐ[k] k[x₁, …, xₙ]/(f₁, …, f_c)`, then
for any `g ∈ S` the localization `S_g` is presented by `n + 1` variables and `c + 1` relations,
`S_g ≃ₐ[k] k[x₁, …, x_{n+1}]/(f₁, …, f_c, x_{n+1}·g' − 1)` with `g'` a preimage of `g`. -/
theorem gci_localization_presentation
    (S : Type*) [CommRing S] [Algebra k S] (g : S)
    (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) k)
    (e : S ≃ₐ[k] (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f))) :
    ∃ f' : Fin (c + 1) → MvPolynomial (Fin (n + 1)) k,
      Nonempty (Localization.Away g ≃ₐ[k]
        (MvPolynomial (Fin (n + 1)) k ⧸ Ideal.span (Set.range f'))) := by
  classical
  let Pnaive : Algebra.Presentation k (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f))
      (Fin n) (Fin c) := Algebra.Presentation.naive (v := f)
  let P : Algebra.Presentation k S (Fin n) (Fin c) := Pnaive.ofAlgEquiv e.symm
  let Q : Algebra.Presentation S (Localization.Away g) Unit Unit :=
    Algebra.Presentation.localizationAway (Localization.Away g) g
  let QP : Algebra.Presentation k (Localization.Away g) (Unit ⊕ Fin n) (Unit ⊕ Fin c) := Q.comp P
  let eι : (Unit ⊕ Fin n) ≃ Fin (n + 1) :=
    (Equiv.sumCongr finOneEquiv.symm (Equiv.refl (Fin n))).trans
      (finSumFinEquiv.trans (finCongr (by omega)))
  let eσ : (Unit ⊕ Fin c) ≃ Fin (c + 1) :=
    (Equiv.sumCongr finOneEquiv.symm (Equiv.refl (Fin c))).trans
      (finSumFinEquiv.trans (finCongr (by omega)))
  let ren : MvPolynomial (Unit ⊕ Fin n) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k :=
    MvPolynomial.renameEquiv k eι
  refine ⟨fun i => ren (QP.relation (eσ.symm i)), ⟨?_⟩⟩
  let qe : QP.Quotient ≃ₐ[k] Localization.Away g := QP.quotientEquiv.restrictScalars k
  let s2 : QP.Quotient ≃ₐ[k]
      (MvPolynomial (Unit ⊕ Fin n) k ⧸ Ideal.span (Set.range QP.relation)) :=
    Ideal.quotientEquivAlgOfEq k QP.span_range_relation_eq_ker.symm
  have hmap : Ideal.span (Set.range (fun i => ren (QP.relation (eσ.symm i))))
      = Ideal.map ren.toAlgHom.toRingHom (Ideal.span (Set.range QP.relation)) := by
    rw [Ideal.map_span]
    congr 1
    rw [show (fun i => ren (QP.relation (eσ.symm i)))
          = (fun x => ren (QP.relation x)) ∘ eσ.symm from rfl, Set.range_comp,
        eσ.symm.surjective.range_eq, Set.image_univ, ← Set.range_comp]
    rfl
  let s3 : (MvPolynomial (Unit ⊕ Fin n) k ⧸ Ideal.span (Set.range QP.relation)) ≃ₐ[k]
      (MvPolynomial (Fin (n + 1)) k ⧸
        Ideal.span (Set.range (fun i => ren (QP.relation (eσ.symm i))))) :=
    Ideal.quotientEquivAlg _ _ ren hmap
  exact (qe.symm.trans s2).trans s3

/-- Every maximal ideal of `k[x₁, …, xₙ]` has height `n`. -/
@[ega "IV 5.5.3" "special case"]
theorem mvpoly_maximal_height (n : ℕ) :
    ∀ (M : Ideal (MvPolynomial (Fin n) k)), M.IsMaximal → M.height = (n : ℕ∞) := by
  induction n with
  | zero =>
    intro M hM
    have h : M.height ≤ ringKrullDim (MvPolynomial (Fin 0) k) :=
      Ideal.height_le_ringKrullDim_of_ne_top hM.ne_top
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field] at h
    norm_num at h
    simpa using h
  | succ n ih =>
    intro M hM
    set R := MvPolynomial (Fin n) k
    let eqv : MvPolynomial (Fin (n + 1)) k ≃ₐ[k] Polynomial R := MvPolynomial.finSuccEquiv k n
    let P : Ideal (Polynomial R) := M.map eqv.toRingEquiv
    have hPheight : P.height = M.height := RingEquiv.height_map eqv.toRingEquiv M
    have hPmax : P.IsMaximal := Ideal.map_isMaximal_of_equiv eqv.toRingEquiv
    set p : Ideal R := P.comap (Polynomial.C : R →+* Polynomial R) with hp
    have hpmax : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have hlo : P.LiesOver p := ⟨by rw [hp]; rfl⟩
    have hformula : P.height = p.height + 1 := Polynomial.height_eq_height_add_one p P
    have hpn : p.height = (n : ℕ∞) := ih p hpmax
    rw [← hPheight, hformula, hpn]; push_cast; ring

/-- A nonempty `D(G) ∩ V(I)` in the spectrum of a Jacobson ring contains a maximal point:
if `R` is a Jacobson ring, `I` an ideal, `G ∈ R`, and there is a prime `Q₀ ⊇ I` with `G ∉ Q₀`
(so the locally closed set `V(I) ∩ D(G)` of `Spec R` is nonempty), then there is a *maximal*
ideal `M ⊇ I` with `G ∉ M`. -/
theorem jacobson_exists_maximal_avoiding
    (R : Type*) [CommRing R] [IsJacobsonRing R] (I : Ideal R) (G : R)
    (Q₀ : Ideal R) (hQ₀ : Q₀.IsPrime) (hIQ : I ≤ Q₀) (hGQ : G ∉ Q₀) :
    ∃ M : Ideal R, M.IsMaximal ∧ I ≤ M ∧ G ∉ M := by
  let x₀ : PrimeSpectrum R := ⟨Q₀, hQ₀⟩
  let Z : Set (PrimeSpectrum R) := PrimeSpectrum.zeroLocus I ∩ (PrimeSpectrum.basicOpen G : Set _)
  have hZne : Z.Nonempty := ⟨x₀, (PrimeSpectrum.mem_zeroLocus _ _).mpr hIQ, hGQ⟩
  have hZlc : IsLocallyClosed Z :=
    (PrimeSpectrum.isClosed_zeroLocus (I : Set R)).isLocallyClosed.inter
      (PrimeSpectrum.basicOpen G).isOpen.isLocallyClosed
  obtain ⟨x, hxZ, hxcl⟩ := nonempty_inter_closedPoints hZne hZlc
  refine ⟨x.asIdeal, ?_, (PrimeSpectrum.mem_zeroLocus _ _).mp hxZ.left, hxZ.right⟩
  rw [← PrimeSpectrum.isClosed_singleton_iff_isMaximal]; exact hxcl

/-- A nonzero localization `S_g` of a global complete intersection `S ≅ k[x₁, …, xₙ]/(f₁, …, f_c)`
over `k` has `dim (S_g) ≥ n - c`. -/
theorem gci_localization_dim_ge
    (S : Type*) [CommRing S] [Algebra k S] [Algebra.FiniteType k S] (g : S)
    (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) k)
    (e : S ≃ₐ[k] (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)))
    (hne : ¬ Subsingleton (Localization.Away g)) :
    ((n - c : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (Localization.Away g) := by
  classical
  let mk : MvPolynomial (Fin n) k →+* (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) :=
    Ideal.Quotient.mk (Ideal.span (Set.range f))
  have hker : RingHom.ker mk = Ideal.span (Set.range f) := Ideal.mk_ker
  have : Nontrivial (Localization.Away g) := not_subsingleton_iff_nontrivial.mp hne
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (Localization.Away g)
  set 𝔮₀ : Ideal S := 𝔪.comap (algebraMap S (Localization.Away g))
  have h𝔮₀p : 𝔮₀.IsPrime := h𝔪.isPrime.comap _
  have hg𝔮₀ : g ∉ 𝔮₀ := by
    intro hmem
    have hunit : IsUnit (algebraMap S (Localization.Away g) g) :=
      IsLocalization.Away.algebraMap_isUnit g
    have hmem' : algebraMap S (Localization.Away g) g ∈ 𝔪 := hmem
    exact h𝔪.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem' hunit)
  let φ : MvPolynomial (Fin n) k →+* S := (e.symm.toRingHom).comp mk
  obtain ⟨G, hG⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span (Set.range f)) (e g)
  have hφG : φ G = g := by
    change e.symm.toRingHom (mk G) = g
    rw [show mk G = e g from hG]
    exact e.symm_apply_apply g
  set Q₀ : Ideal (MvPolynomial (Fin n) k) := 𝔮₀.comap φ with hQ₀def
  have hQ₀p : Q₀.IsPrime := h𝔮₀p.comap _
  have hkerle : Ideal.span (Set.range f) ≤ Q₀ := by
    rw [hQ₀def, Ideal.span_le]
    rintro x ⟨i, rfl⟩
    change φ (f i) ∈ 𝔮₀
    have hfi : φ (f i) = 0 := by
      change e.symm.toRingHom (mk (f i)) = 0
      have : mk (f i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
      rw [this]; simp
    rw [hfi]; exact 𝔮₀.zero_mem
  have hGQ₀ : G ∉ Q₀ := by
    rw [hQ₀def]; intro hmem; exact hg𝔮₀ (by rw [← hφG]; exact hmem)
  obtain ⟨M, hMmax, hMsub, hGM⟩ :=
    jacobson_exists_maximal_avoiding (MvPolynomial (Fin n) k)
      (Ideal.span (Set.range f)) G Q₀ hQ₀p hkerle hGQ₀
  have hsub : Set.range f ⊆ (M : Set (MvPolynomial (Fin n) k)) :=
    fun x hx => hMsub (Ideal.subset_span hx)
  have hMh : M.height = (n : ℕ∞) := mvpoly_maximal_height k n M hMmax
  have hkerle2 : RingHom.ker mk ≤ M := by
    rw [hker]; exact hMsub
  set MT : Ideal (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)) := M.map mk with hMT
  have hcut : ((n - c : ℕ) : ℕ∞) ≤ MT.height := by
    have hk := Ideal.height_le_height_add_encard_of_subset (Set.range f) hsub
    have henc : (Set.range f).encard ≤ (c : ℕ∞) := by
      calc (Set.range f).encard ≤ (Set.univ : Set (Fin c)).encard := by
              rw [← Set.image_univ]; exact Set.encard_image_le f Set.univ
          _ = (c : ℕ∞) := by rw [Set.encard_univ]; simp
    rw [hMh] at hk
    have hnc : (n : ℕ∞) ≤ MT.height + (c : ℕ∞) := le_trans hk (add_le_add_right henc _)
    cases hh : MT.height with
    | top => exact le_top
    | coe m => rw [hh] at hnc; norm_cast at hnc ⊢; omega
  have hMTmax : MT.IsMaximal := by
    rw [hMT]
    exact Ideal.IsMaximal.map_of_surjective_of_ker_le (f := mk) Ideal.Quotient.mk_surjective hkerle2
  have hMTp : MT.IsPrime := hMTmax.isPrime
  set 𝔮 : Ideal S := MT.comap e.toRingEquiv with h𝔮
  have h𝔮p : 𝔮.IsPrime := hMTp.comap _
  have h𝔮h : 𝔮.height = MT.height := RingEquiv.height_comap e.toRingEquiv MT
  have hg𝔮 : g ∉ 𝔮 := by
    rw [h𝔮]; intro hmem
    have hegMT : e g ∈ MT := hmem
    have hmkG : mk G ∈ M.map mk := by rw [hG]; exact hegMT
    have hGmem : G ∈ M := by
      rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective mk Ideal.Quotient.mk_surjective,
          show Ideal.comap mk ⊥ = RingHom.ker mk from rfl, hker] at hmkG
      rcases Submodule.mem_sup.mp hmkG with ⟨a, ha, b, hb, hab⟩
      rw [show G = a + b from hab.symm]; exact M.add_mem ha (hMsub hb)
    exact hGM hGmem
  have hdisj : Disjoint (Submonoid.powers g : Set S) (𝔮 : Set S) := by
    rw [Set.disjoint_left]
    rintro x ⟨m, rfl⟩ hx
    exact hg𝔮 (h𝔮p.mem_of_pow_mem _ hx)
  have hmaph : (𝔮.map (algebraMap S (Localization.Away g))).height = 𝔮.height :=
    IsLocalization.height_map_of_disjoint (Submonoid.powers g) 𝔮 hdisj
  have hmapp : (𝔮.map (algebraMap S (Localization.Away g))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g) (Localization.Away g) 𝔮 h𝔮p
        hdisj
  have hfinal : (𝔮.map (algebraMap S (Localization.Away g))).height ≤ ringKrullDim
      (Localization.Away g) :=
    Ideal.height_le_ringKrullDim_of_ne_top hmapp.ne_top
  have hge : ((n - c : ℕ) : ℕ∞) ≤ (𝔮.map (algebraMap S (Localization.Away g))).height := by
    rw [hmaph, h𝔮h]; exact hcut
  calc ((n - c : ℕ) : WithBot ℕ∞)
      = ((((n - c : ℕ) : ℕ∞)) : WithBot ℕ∞) := by norm_cast
    _ ≤ (((𝔮.map (algebraMap S (Localization.Away g))).height : ℕ∞) : WithBot ℕ∞) := by
        exact_mod_cast hge
    _ ≤ ringKrullDim (Localization.Away g) := hfinal

/-- A nonzero localization `S_g` of a global complete intersection `S ≅ k[x₁, …, xₙ]/(f₁, …, f_c)`
over `k` with `dim S = n - c` again has dimension `n - c`. -/
theorem gci_localization_dim
    (S : Type*) [CommRing S] [Algebra k S] [Algebra.FiniteType k S] (g : S)
    (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) k)
    (e : S ≃ₐ[k] (MvPolynomial (Fin n) k ⧸ Ideal.span (Set.range f)))
    (hdim : ringKrullDim S = ((n - c : ℕ) : WithBot ℕ∞))
    (hne : ¬ Subsingleton (Localization.Away g)) :
    ringKrullDim (Localization.Away g) = ((n - c : ℕ) : WithBot ℕ∞) := by
  refine le_antisymm ?_ (gci_localization_dim_ge k S g n c f e hne)
  have hmono : StrictMono
      (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
    have hinj : Function.Injective
        (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) :=
      PrimeSpectrum.localization_comap_injective (Localization.Away g) (Submonoid.powers g)
    refine fun x y hxy => lt_of_le_of_ne ?_ (fun h => (ne_of_lt hxy) (hinj h))
    exact Ideal.comap_mono hxy.le
  calc ringKrullDim (Localization.Away g)
      = Order.krullDim (PrimeSpectrum (Localization.Away g)) := rfl
    _ ≤ Order.krullDim (PrimeSpectrum S) := Order.krullDim_le_of_strictMono _ hmono
    _ = ringKrullDim S := rfl
    _ = ((n - c : ℕ) : WithBot ℕ∞) := hdim

/-- Being a global complete intersection over `k` is invariant under isomorphism of `k`-algebras:
if `A ≃ₐ[k] B` and `A` is a global complete intersection over `k`, then so is `B`. -/
theorem gci_transport {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] B) (hA : IsGlobalCompleteIntersection k A) :
    IsGlobalCompleteIntersection k B := by
  rcases hA with hsub | ⟨n, c, f, eA, hcn, hdim⟩
  · exact Or.inl (e.toEquiv.symm.subsingleton)
  · exact Or.inr ⟨n, c, f, e.symm.trans eA, hcn,
      (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm.trans hdim⟩

/-- Being a local complete intersection over `k` is invariant under isomorphism of `k`-algebras:
if `A ≃ₐ[k] B` and `A` is a local complete intersection over `k`, then so is `B`. -/
theorem lci_transport {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] B) (hA : IsLocalCompleteIntersection k A) :
    IsLocalCompleteIntersection k B := by
  obtain ⟨t, ht, hgci⟩ := hA
  refine ⟨e '' t, by rw [← Ideal.map_span, ht, Ideal.map_top], ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  exact gci_transport k (IsLocalization.algEquivOfAlgEquiv (A := k) (R := A) (P := B)
    (S := Localization.Away a) (Q := Localization.Away (e a))
    (M := Submonoid.powers a) (T := Submonoid.powers (e a)) e
    (Submonoid.map_powers (e : A ≃+* B).toMonoidHom a)) (hgci a ha)

/-- Let `k` be a field, `S` a `k`-algebra and `g ∈ S`. If `S` is a global complete intersection
over `k`, then so is the localization `S_g`. This is Stacks 00SA (1). -/
theorem isGlobalCompleteIntersection_localization
    (S : Type*) [CommRing S] [Algebra k S] (g : S)
    (hS : IsGlobalCompleteIntersection k S) :
    IsGlobalCompleteIntersection k (Localization.Away g) := by
  have := hS.finiteType
  by_cases hsub : Subsingleton (Localization.Away g)
  · exact Or.inl hsub
  · rcases hS with hSsub | ⟨n, c, f, e, hcn, hdim⟩
    · exact absurd (by have := hSsub; infer_instance) hsub
    · obtain ⟨f', ⟨e'⟩⟩ := gci_localization_presentation k S g n c f e
      refine Or.inr ⟨n + 1, c + 1, f', e', by omega, ?_⟩
      rw [gci_localization_dim k S g n c f e hdim hsub]
      congr 1
      omega

/-- Let `k` be a field, `S` a `k`-algebra and `g ∈ S`. If `S` is a local complete intersection
over `k`, then so is the localization `S_g`. This is Stacks 00SA (2). -/
theorem isLocalCompleteIntersection_localization
    (S : Type*) [CommRing S] [Algebra k S] (g : S)
    (hS : IsLocalCompleteIntersection k S) :
    IsLocalCompleteIntersection k (Localization.Away g) := by
  obtain ⟨s, hspan, hgci⟩ := hS
  refine ⟨(algebraMap S (Localization.Away g)) '' s, ?_, ?_⟩
  · rw [← Ideal.map_span, hspan, Ideal.map_top]
  · rintro gi' ⟨gi, hgi, rfl⟩
    have hgci_gi : IsGlobalCompleteIntersection k (Localization.Away gi) := hgci gi hgi
    have hB : IsGlobalCompleteIntersection k
        (Localization.Away ((algebraMap S (Localization.Away gi)) g)) :=
      isGlobalCompleteIntersection_localization k (Localization.Away gi)
        ((algebraMap S (Localization.Away gi)) g) hgci_gi
    have hBloc : IsLocalization (Submonoid.powers (g * gi))
        (Localization.Away ((algebraMap S (Localization.Away gi)) g)) := by
      rw [mul_comm g gi]
      exact (inferInstance :
        IsLocalization.Away (gi * g) (Localization.Away ((algebraMap S (Localization.Away gi)) g)))
    let iso : Localization.Away ((algebraMap S (Localization.Away gi)) g) ≃ₐ[k]
        Localization.Away ((algebraMap S (Localization.Away g)) gi) :=
      (IsLocalization.algEquiv (Submonoid.powers (g * gi))
        (Localization.Away ((algebraMap S (Localization.Away gi)) g))
        (Localization.Away ((algebraMap S (Localization.Away g)) gi))).restrictScalars k
    exact gci_transport k iso hB
