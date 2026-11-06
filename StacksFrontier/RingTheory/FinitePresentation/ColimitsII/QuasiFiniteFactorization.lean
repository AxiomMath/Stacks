module

public import StacksFrontier.RingTheory.FinitePresentation.ColimitsII.FaithfullyFlatModel
public import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-finite faithfully flat refinements of ring maps of finite presentation

This file proves Lemma 034Z.


**Lemma 034Z.** A faithfully flat ring map `R → S` of finite presentation factors as
`R → S → S'` with `R → S'` quasi-finite, faithfully flat and of finite presentation. By Lemma 034Y
and base change (Lemma 00PP) one may assume `R` Noetherian. Given a prime `𝔭` of `R`, the set `W`
of primes of `S` with Cohen–Macaulay fibre ring is open and meets the fibre over `𝔭`
(Lemmas 00RH, 00RI, 00HQ), so it contains a prime `𝔮` over `𝔭` which is a closed point of the
fibre. Lift a maximal regular sequence of the Cohen–Macaulay local ring `S_𝔮/𝔭S_𝔮`, of length
`d = dim S_𝔮/𝔭S_𝔮`, to `f₁, …, f_d ∈ 𝔮` and put `S'' = S/(f₁, …, f_d)`. The image `𝔮''` of `𝔮`
is a closed point of its fibre, and a generic one because `S_𝔮/(𝔭, f₁, …, f_d)` has dimension
zero; hence it is isolated and `R → S''` is quasi-finite at `𝔮''` (Lemma 00PK). By Lemma 00MG
the localization `S''_{𝔮''}` is flat over `R_𝔭`. By openness of the flat locus (Theorem 00RC) and
of the quasi-finite locus (Lemma 00QA) some `S''_g`, `g ∉ 𝔮''`, is flat and quasi-finite over
`R`, and its image in `Spec R` is an open neighbourhood of `𝔭` (Proposition 00I1). A finite
product of such rings, one for each member of a finite subcover of the quasi-compact space
`Spec R`, is faithfully flat.

## Main results

* `Algebra.exists_quasiFinite_faithfullyFlat_finitePresentation`: Lemma 034Z.
* `Algebra.exists_quasiFinite_flat_finitePresentation_mem_range`: over a Noetherian base, every
  prime in the image of a flat ring map `R → S` of finite presentation is in the image of an
  `S`-algebra which is quasi-finite, flat and of finite presentation over `R`.

## Implementation notes

In Lemma 034Z the commutative triangle is the data `R → S → S'` with `IsScalarTower R S S'`,
and quasi-finiteness is `Algebra.QuasiFinite`, which omits the finite type clause of Definition
00PL; the finite type condition is part of finite presentation. The source replaces `S` by a
product of principal localizations on which every fibre ring is Cohen–Macaulay before choosing a
prime maximal in its fibre; here the prime is chosen directly in the Cohen–Macaulay locus, as a
closed point of the open subset it cuts out in the fibre, a finite type scheme over a field.

## References

* [Stacks Project, Tag 034Z](https://stacks.math.columbia.edu/tag/034Z)
-/

@[expose] public section

universe u

open scoped TensorProduct

/-! ### Stacks 034Z -/

/-- The fibre of a finite type algebra over `p` is of finite type and Jacobson over `κ(p)`. -/
private theorem finiteType_and_isJacobsonRing_fiber {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime] :
    Algebra.FiniteType p.ResidueField (p.Fiber S) ∧ IsJacobsonRing (p.Fiber S) := by
  have : Algebra.FiniteType p.ResidueField (p.Fiber S) := by
    unfold Ideal.Fiber; infer_instance
  exact ⟨this, isJacobsonRing_of_finiteType (A := p.ResidueField)⟩

open PrimeSpectrum in
/-- Let `R → S` be of finite type, `p` a prime of `R` and `W ⊆ Spec S` an open set meeting the
fibre over `p`. Then `W` contains a prime `q` over `p` which is maximal among the primes of `S`
over `p`: the fibre is the spectrum of the Jacobson ring `κ(p) ⊗_R S`, so its nonempty open
subset `W ∩ Spec(κ(p) ⊗_R S)` contains a closed point. -/
theorem PrimeSpectrum.exists_mem_forall_eq_of_le_of_comap_eq {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [Algebra.FiniteType R S] (p : PrimeSpectrum R)
    {W : Set (PrimeSpectrum S)} (hW : IsOpen W)
    (hne : ∃ q ∈ W, comap (algebraMap R S) q = p) :
    ∃ q ∈ W, comap (algebraMap R S) q = p ∧
      ∀ Q : PrimeSpectrum S, comap (algebraMap R S) Q = p → q ≤ Q → Q = q := by
  obtain ⟨q₀, hq₀W, hq₀⟩ := hne
  let F := comap (algebraMap R S) ⁻¹' {p}
  let e := preimageHomeomorphFiber R S p
  obtain ⟨_, _⟩ := finiteType_and_isJacobsonRing_fiber (S := S) p.asIdeal
  let U : Set F := (↑) ⁻¹' W
  have hU : IsOpen U := hW.preimage continuous_subtype_val
  have hV : IsOpen (e '' U) := e.isOpenMap _ hU
  obtain ⟨x, ⟨y, hyU, rfl⟩, hx⟩ :=
    nonempty_inter_closedPoints (Z := e '' U) ⟨e ⟨q₀, hq₀⟩, ⟨q₀, hq₀⟩, hq₀W, rfl⟩ hV.isLocallyClosed
  refine ⟨y.1, hyU, y.2, fun Q hQ hle => ?_⟩
  have hmax : (e y).asIdeal.IsMaximal := (isClosed_singleton_iff_isMaximal _).mp hx
  have hle' : e y ≤ e (⟨Q, hQ⟩ : F) :=
    (preimageOrderIsoFiber R S p).monotone (show y ≤ (⟨Q, hQ⟩ : F) from hle)
  have heq : e y = e (⟨Q, hQ⟩ : F) :=
    PrimeSpectrum.ext (hmax.eq_of_le (e (⟨Q, hQ⟩ : F)).2.ne_top hle')
  exact congrArg Subtype.val (e.injective heq).symm

open IsLocalRing in
/-- Let `A` be a Cohen–Macaulay Noetherian local ring and `φ : S → A` a ring map such that every
element of `A` is a unit multiple of an element of the image of `φ`, e.g. a localization of a
quotient of `S`. Then there are `a₁, …, a_d ∈ S` whose images lie in the maximal ideal of `A`,
form a regular sequence in `A`, and cut out a quotient `A/(φ(a₁), …, φ(a_d))` of dimension `0`. -/
theorem Module.IsMaximalCohenMacaulay.exists_isRegular_map_ringKrullDim_quotient_eq_zero
    {S A : Type*} [CommRing S] [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (hA : Module.IsMaximalCohenMacaulay A A) (φ : S →+* A)
    (hφ : ∀ b : A, ∃ a : S, ∃ u : A, IsUnit u ∧ φ a = b * u) :
    ∃ as : List S, (∀ a ∈ as, φ a ∈ maximalIdeal A) ∧
      RingTheory.Sequence.IsRegular A (as.map φ) ∧
      ringKrullDim (A ⧸ Ideal.ofList (as.map φ)) = 0 := by
  have h02JN := hA.isRegular_iff_ringKrullDim_add_length_eq_ringKrullDim
  obtain ⟨ys, hysm, hys, hlen⟩ := ((h02JN [] (by simp)).2
    (RingTheory.Sequence.IsRegular.nil A A)).1
  simp only [List.nil_append] at hys hlen
  choose a u hu ha using hφ
  refine ⟨ys.map a, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    rw [ha]
    exact Ideal.mul_mem_right _ _ (hysm y hy)
  have hmap : (ys.map a).map φ = ys.map fun y => y * u y := by
    rw [List.map_map]; exact List.map_congr_left fun y _ => ha y
  have hideal : Ideal.ofList (ys.map fun y => y * u y) = Ideal.ofList ys := by
    apply le_antisymm
    · refine Ideal.span_le.mpr fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span hy)
    · refine Ideal.span_le.mpr fun y hy => ?_
      have : y = y * u y * ↑(hu y).unit⁻¹ := by simp [mul_assoc]
      rw [this]
      exact Ideal.mul_mem_right _ _
        (Ideal.subset_span (List.mem_map_of_mem (f := fun y => y * u y) hy))
  rw [hmap, hideal]
  have hlen' : ((ys.map fun y => y * u y).length : WithBot ℕ∞) = ys.length := by simp
  have hm : ∀ x ∈ ys.map (fun y => y * u y), x ∈ maximalIdeal A := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact Ideal.mul_mem_right _ _ (hysm y hy)
  have hdim := (h02JN ys hysm).1.mp hys
  refine ⟨(h02JN _ hm).1.mpr (by rw [hideal, hlen']; exact hdim), ?_⟩
  rw [← hlen] at hdim
  have : Nontrivial (A ⧸ Ideal.ofList ys) := by
    refine Ideal.Quotient.nontrivial_iff.mpr fun h => hys.top_ne_smul ?_
    rw [h, smul_eq_mul, Ideal.top_mul]
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ Ideal.ofList ys) :=
    ringKrullDim_nonneg_of_nontrivial
  obtain ⟨y, hy⟩ := WithBot.ne_bot_iff_exists.mp (ne_bot_of_le_ne_bot
    WithBot.coe_ne_bot h0)
  rw [← hy] at hdim ⊢
  have h' : y + (ys.length : ℕ∞) = 0 + (ys.length : ℕ∞) := by
    rw [zero_add]; exact_mod_cast hdim
  have := WithTop.add_right_cancel (ENat.natCast_ne_top _) h'
  rw [this]; rfl

open IsLocalRing in
/-- Let `q` be a prime of an `R`-algebra `S` over `𝔭 = R ∩ q` and let `a₁, …, a_d ∈ S` be such
that the quotient of the fibre ring `S_q/𝔭S_q` by the images of the `aᵢ` has dimension `0`. Then
`q` is the only prime `Q ⊆ q` of `S` containing `𝔭S` and all the `aᵢ`. The fibre ring is spelled
as the localization of `S/𝔭S` at the image of `q`, as in Lemma 00RH. -/
theorem Ideal.eq_of_le_of_ringKrullDim_quotient_localization_eq_zero {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (q : Ideal S) [q.IsPrime] (as : List S)
    (h : ringKrullDim (Localization.AtPrime
        (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))) ⧸
      Ideal.ofList (as.map (algebraMap S (Localization.AtPrime
        (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))))))) = 0)
    (Q : Ideal S) [Q.IsPrime] (hIQ : (q.under R).map (algebraMap R S) ≤ Q)
    (has : Ideal.ofList as ≤ Q) (hQq : Q ≤ q) : Q = q := by
  set I := (q.under R).map (algebraMap R S)
  set qb := q.map (Ideal.Quotient.mk I)
  set A := Localization.AtPrime qb
  set K := Ideal.ofList (as.map (algebraMap S A))
  have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ Q := by rwa [Ideal.mk_ker]
  have hQb : (Q.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hdisj : Disjoint (qb.primeCompl : Set (S ⧸ I)) (Q.map (Ideal.Quotient.mk I)) := by
    rw [Set.disjoint_left]
    intro x hx hxQ
    exact hx (Ideal.map_mono hQq hxQ)
  set J := (Q.map (Ideal.Quotient.mk I)).map (algebraMap (S ⧸ I) A)
  have hJ : J.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint qb.primeCompl A _ hQb hdisj
  have hJc : J.comap (algebraMap _ A) = Q.map (Ideal.Quotient.mk I) :=
    IsLocalization.under_map_of_isPrime_disjoint _ A hQb hdisj
  have hKJ : K ≤ J := by
    refine Ideal.span_le.mpr fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    rw [IsScalarTower.algebraMap_apply S (S ⧸ I) A]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (has (Ideal.subset_span ha)))
  have : Ring.KrullDimLE 0 (A ⧸ K) := Ring.krullDimLE_iff.mpr (by rw [h]; rfl)
  have : (J.map (Ideal.Quotient.mk K)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have : (J.map (Ideal.Quotient.mk K)).IsMaximal := Ideal.isMaximal_of_isPrime (R := A ⧸ K) _
  have hJmax : J.IsMaximal := by
    rw [← Ideal.comap_map_mk hKJ]
    exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hJm : J = maximalIdeal A := IsLocalRing.eq_maximalIdeal hJmax
  have hQ : Q.map (Ideal.Quotient.mk I) = qb := by
    rw [← hJc, hJm]
    exact IsLocalization.AtPrime.under_maximalIdeal A qb
  have hIq : I ≤ q := Ideal.map_comap_le
  rw [← Ideal.comap_map_mk hIQ, hQ, Ideal.comap_map_mk hIq]

/-- For `I ≤ q`, `S_q/I S_q` is the localization of `S/I` at the image of `q`. -/
private theorem isLocalization_primeCompl_map_quotient_mk {S : Type*} [CommRing S]
    (q : Ideal S) [q.IsPrime] (I : Ideal S) (hIq : I ≤ q)
    [(q.map (Ideal.Quotient.mk I)).IsPrime] :
    IsLocalization (q.map (Ideal.Quotient.mk I)).primeCompl
      (Localization.AtPrime q ⧸ I.map (algebraMap S (Localization.AtPrime q))) := by
  have : (q.map (Ideal.Quotient.mk I)).LiesOver q := ⟨by
    change q = (q.map (Ideal.Quotient.mk I)).comap (algebraMap S (S ⧸ I))
    rw [Ideal.Quotient.algebraMap_eq, Ideal.comap_map_mk hIq]⟩
  exact Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective
    (q.map (Ideal.Quotient.mk I)) q Ideal.Quotient.mk_surjective ▸ inferInstance

open IsLocalRing in
/-- Let `q` be a prime of an `R`-algebra `S` over `𝔭 = R ∩ q`. A sequence of elements of `S`
which is regular in the fibre ring `S_q/𝔭S_q`, spelled as the localization of `S/𝔭S` at the image
of `q` (Lemma 00RH), is regular in `S_q/𝔪S_q`, `𝔪` the maximal ideal of `R_𝔭` (Lemma 00MG). -/
theorem RingTheory.Sequence.IsRegular.map_quotient_maximalIdeal_localization {R S : Type*}
    [CommRing R] [CommRing S] [Algebra R S] (q : Ideal S) [q.IsPrime] (as : List S)
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime
        (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))))
      (as.map (algebraMap S (Localization.AtPrime
        (q.map (Ideal.Quotient.mk ((q.under R).map (algebraMap R S)))))))) :
    let _ := Localization.AtPrime.algebraOfLiesOver (q.under R) q
    RingTheory.Sequence.IsRegular (Localization.AtPrime q ⧸
        (maximalIdeal (Localization.AtPrime (q.under R))).map
          (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)))
      ((as.map (algebraMap S (Localization.AtPrime q))).map (Ideal.Quotient.mk
        ((maximalIdeal (Localization.AtPrime (q.under R))).map
          (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q))))) := by
  let _ := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  set p := q.under R
  set I := p.map (algebraMap R S)
  set qb := q.map (Ideal.Quotient.mk I)
  have hIq : I ≤ q := Ideal.map_comap_le
  have := isLocalization_primeCompl_map_quotient_mk q I hIq
  let e₁ := IsLocalization.algEquiv qb.primeCompl (Localization.AtPrime qb)
    (Localization.AtPrime q ⧸ I.map (algebraMap S (Localization.AtPrime q)))
  have hideal : I.map (algebraMap S (Localization.AtPrime q)) =
      (maximalIdeal (Localization.AtPrime p)).map
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  let e := e₁.toRingEquiv.trans (Ideal.quotEquivOfEq hideal)
  have he : ∀ a : S, e (algebraMap S (Localization.AtPrime qb) a) =
      Ideal.Quotient.mk _ (algebraMap S (Localization.AtPrime q) a) := by
    intro a
    rw [IsScalarTower.algebraMap_apply S (S ⧸ I) (Localization.AtPrime qb)]
    simp only [e, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
      AlgEquiv.commutes]
    rfl
  refine (AddEquiv.isRegular_congr (e := e.toAddEquiv) ?_).mp hreg
  rw [List.map_map, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun a _ x => ?_
  simp only [smul_eq_mul, RingEquiv.toAddEquiv_eq_coe, RingEquiv.coe_toAddEquiv, map_mul,
    Function.comp_apply]
  rw [he]

open IsLocalRing in
/-- Let `R` be Noetherian, `S` a flat `R`-algebra of finite type and `q` a prime of `S` over
`𝔭 = R ∩ q`. If `a₁, …, a_d ∈ S` map to a regular sequence in `S_q/𝔪S_q`, `𝔪` the maximal ideal
of `R_𝔭`, then `S_q/(a₁, …, a_d)` is flat over `R_𝔭`. This is Lemma 00MG. -/
@[ega "IV 11.3.8" "(c), special case"]
theorem Module.Flat.quotient_ofList_localization_of_isRegular {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [Module.Flat R S] [Algebra.FiniteType R S]
    (q : Ideal S) [q.IsPrime] (as : List S) :
    let _ := Localization.AtPrime.algebraOfLiesOver (q.under R) q
    RingTheory.Sequence.IsRegular (Localization.AtPrime q ⧸
        (maximalIdeal (Localization.AtPrime (q.under R))).map
          (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)))
      ((as.map (algebraMap S (Localization.AtPrime q))).map (Ideal.Quotient.mk
        ((maximalIdeal (Localization.AtPrime (q.under R))).map
          (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q))))) →
    Module.Flat (Localization.AtPrime (q.under R))
      (Localization.AtPrime q ⧸ Ideal.ofList (as.map (algebraMap S (Localization.AtPrime q)))) := by
  intro _ hreg
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  have : IsLocalHom (algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  have h := (Module.Flat.isRegular_and_flat_quotient_ofList_take_of_isRegular_maximalIdeal
    hreg).2 (as.map (algebraMap S (Localization.AtPrime q))).length
  rwa [List.take_length] at h

/-- Let `q` be a prime of an `R`-algebra `S` containing `a₁, …, a_d`, with `𝔭 = R ∩ q`. If
`S_q/(a₁, …, a_d)` is flat over `R_𝔭`, then the localization of `S/(a₁, …, a_d)` at the image of
`q` is flat over `R`. -/
theorem Module.Flat.localizedModule_quotient_ofList {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (q : Ideal S) [q.IsPrime] (as : List S) (has : Ideal.ofList as ≤ q)
    [(q.map (Ideal.Quotient.mk (Ideal.ofList as))).IsPrime]
    (hflat : letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
      Module.Flat (Localization.AtPrime (q.under R))
        (Localization.AtPrime q ⧸ Ideal.ofList (as.map (algebraMap S (Localization.AtPrime q))))) :
    Module.Flat R (LocalizedModule.AtPrime (q.map (Ideal.Quotient.mk (Ideal.ofList as)))
      (S ⧸ Ideal.ofList as)) := by
  let _ := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  set J := Ideal.ofList as
  set qq := q.map (Ideal.Quotient.mk J)
  set T := Localization.AtPrime q ⧸ J.map (algebraMap S (Localization.AtPrime q))
  have : IsLocalization qq.primeCompl T := isLocalization_primeCompl_map_quotient_mk q J has
  let e := IsLocalizedModule.iso qq.primeCompl (Algebra.linearMap (S ⧸ J) T)
  have hT : J.map (algebraMap S (Localization.AtPrime q)) =
      Ideal.ofList (as.map (algebraMap S (Localization.AtPrime q))) := Ideal.map_ofList _ _
  have : Module.Flat (Localization.AtPrime (q.under R)) T := by
    show Module.Flat _ (Localization.AtPrime q ⧸ J.map _)
    rwa [hT]
  have : IsScalarTower R (S ⧸ J) T := .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R S (S ⧸ J), IsScalarTower.algebraMap_apply R S T]
    rfl
  have : IsScalarTower R (S ⧸ J) (LocalizedModule qq.primeCompl (S ⧸ J)) := inferInstance
  have : Module.Flat R T := Module.Flat.trans R (Localization.AtPrime (q.under R)) T
  exact Module.Flat.of_linearEquiv (e.restrictScalars R)

open PrimeSpectrum in
/-- Let `R → S` be of finite type and `q` a prime of `S` which is both maximal and minimal among
the primes of `S` with the same image in `Spec R`. Then `R → S` is quasi-finite at `q`: the point
`q` is closed and stable under generalization in its fibre, the spectrum of the Noetherian
Jacobson ring `κ(𝔭) ⊗_R S`, hence isolated. -/
theorem Algebra.QuasiFiniteAt.of_forall_eq_of_comap_eq {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] (q : PrimeSpectrum S)
    (hmax : ∀ Q : PrimeSpectrum S,
      comap (algebraMap R S) Q = comap (algebraMap R S) q → q ≤ Q → Q = q)
    (hmin : ∀ Q : PrimeSpectrum S,
      comap (algebraMap R S) Q = comap (algebraMap R S) q → Q ≤ q → Q = q) :
    Algebra.QuasiFiniteAt R q.asIdeal := by
  rw [Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber]
  set p := comap (algebraMap R S) q
  set F := comap (algebraMap R S) ⁻¹' {p}
  let e := preimageHomeomorphFiber R S p
  let o := preimageOrderIsoFiber R S p
  obtain ⟨_, _⟩ := finiteType_and_isJacobsonRing_fiber (S := S) p.asIdeal
  have : IsNoetherianRing (p.asIdeal.Fiber S) :=
    Algebra.FiniteType.isNoetherianRing p.asIdeal.ResidueField _
  set x : F := ⟨q, rfl⟩
  rw [← e.isOpen_image, Set.image_singleton]
  refine ((isOpen_singleton_tfae_of_isNoetherian_of_isJacobsonRing (e x)).out 1 3).mpr
    (And.intro ?_ ?_)
  · rw [isClosed_singleton_iff_isMaximal]
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ (e x).2.ne_top
    have h1 : x ≤ o.symm ⟨M, hM.isPrime⟩ := by
      rwa [← o.le_iff_le, o.apply_symm_apply]
    have h2 : o.symm ⟨M, hM.isPrime⟩ = x :=
      Subtype.ext (hmax _ (o.symm ⟨M, hM.isPrime⟩).2 h1)
    have h3 : (⟨M, hM.isPrime⟩ : PrimeSpectrum _) = e x := by
      rw [← h2]; exact (o.apply_symm_apply _).symm
    rwa [← h3]
  · intro a b hba ha
    rw [Set.mem_singleton_iff] at ha ⊢
    subst ha
    rw [← le_iff_specializes] at hba
    have h1 : o.symm b ≤ x := by
      rwa [← o.le_iff_le, o.apply_symm_apply]
    have h2 : o.symm b = x := Subtype.ext (hmin _ (o.symm b).2 h1)
    rw [← h2]; exact (o.apply_symm_apply _).symm

/-- Let `R → T` be of finite type and `g ∈ T` such that `T_Q` is flat over `R` and `R → T` is
quasi-finite at `Q` for every prime `Q` of the principal open `D(g)`. Then `T_g` is flat and
quasi-finite over `R`. -/
theorem Localization.Away.flat_and_quasiFinite_of_forall {R T : Type*} [CommRing R] [CommRing T]
    [Algebra R T] [Algebra.FiniteType R T] (g : T)
    (hflat : ∀ Q : PrimeSpectrum T, g ∉ Q.asIdeal →
      Module.Flat R (LocalizedModule.AtPrime Q.asIdeal T))
    (hqf : ∀ Q : PrimeSpectrum T, g ∉ Q.asIdeal → Algebra.QuasiFiniteAt R Q.asIdeal) :
    Module.Flat R (Localization.Away g) ∧ Algebra.QuasiFinite R (Localization.Away g) := by
  have key : ∀ (P : Ideal (Localization.Away g)) [P.IsPrime],
      g ∉ P.comap (algebraMap T (Localization.Away g)) := by
    intro P _ hg
    exact (‹P.IsPrime›.ne_top) (Ideal.eq_top_of_isUnit_mem _ hg
      (IsLocalization.Away.algebraMap_isUnit g))
  refine ⟨?_, ?_⟩
  · refine Module.flat_of_isLocalized_maximal (Localization.Away g) (Localization.Away g)
      (fun P _ => Localization.AtPrime P) (fun P _ => Algebra.linearMap _ _) fun P _ => ?_
    set P' := P.comap (algebraMap T (Localization.Away g))
    have := hflat ⟨P', inferInstance⟩ (key P)
    let e := IsLocalizedModule.iso P'.primeCompl
      (Algebra.linearMap T (Localization.AtPrime P))
    exact Module.Flat.of_linearEquiv (e.symm.restrictScalars R)
  · have : Algebra.FinitePresentation T (Localization.Away g) :=
      IsLocalization.Away.finitePresentation g
    have : Algebra.FiniteType R (Localization.Away g) := .trans (S := T) inferInstance inferInstance
    refine Algebra.QuasiFinite.iff_finite_comap_preimage_singleton.mpr fun p => ?_
    have : CompactSpace (PrimeSpectrum.comap (algebraMap R (Localization.Away g)) ⁻¹' {p}) :=
      (PrimeSpectrum.preimageHomeomorphFiber R _ p).symm.compactSpace
    have : DiscreteTopology (PrimeSpectrum.comap (algebraMap R (Localization.Away g)) ⁻¹' {p}) := by
      refine discreteTopology_iff_isOpen_singleton.mpr fun ⟨x, hx⟩ => ?_
      rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
      subst hx
      set Q' := x.asIdeal.comap (algebraMap T (Localization.Away g))
      have := hqf ⟨Q', inferInstance⟩ (key x.asIdeal)
      have : Algebra.QuasiFiniteAt R x.asIdeal :=
        (Algebra.QuasiFinite.iff_of_algEquiv
          ((IsLocalization.localizationLocalizationAtPrimeIsoLocalization _
            x.asIdeal).restrictScalars R)).mp this
      exact (Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber x).mp this
    have := finite_of_compact_of_discrete
      (X := PrimeSpectrum.comap (algebraMap R (Localization.Away g)) ⁻¹' {p})
    exact Set.toFinite _

open PrimeSpectrum IsLocalRing in
/-- Let `R` be Noetherian, `R → S` flat of finite presentation and `𝔭` a prime of `R` in the image
of `Spec S → Spec R`. Then there is an `S`-algebra `S'` which is quasi-finite, flat and of finite
presentation over `R` and whose spectrum has `𝔭` in its image. This is the local step of Lemma
034Z; `S'` is `(S/(a₁, …, a_d))_g` for `a₁, …, a_d` lifting a maximal regular sequence of the
Cohen–Macaulay fibre ring at a suitable prime over `𝔭`. -/
theorem Algebra.exists_quasiFinite_flat_finitePresentation_mem_range {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [Module.Flat R S]
    [Algebra.FinitePresentation R S] (p : PrimeSpectrum R)
    (hp : p ∈ Set.range (comap (algebraMap R S))) :
    ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra R S') (_ : Algebra S S')
      (_ : IsScalarTower R S S'), Algebra.QuasiFinite R S' ∧ Module.Flat R S' ∧
        Algebra.FinitePresentation R S' ∧ p ∈ Set.range (comap (algebraMap R S')) := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  obtain ⟨hWo, hWd⟩ := Algebra.isOpen_setOf_isMaximalCohenMacaulay_fiber_and_dense_fiber R S
  obtain ⟨q₀, hq₀⟩ := hp
  have : Nonempty (comap (algebraMap R S) ⁻¹' {p}) := ⟨⟨q₀, hq₀⟩⟩
  obtain ⟨⟨q₁, hq₁⟩, hq₁W⟩ := (hWd p).nonempty
  obtain ⟨q, hqW, hqp, hqmax⟩ :=
    PrimeSpectrum.exists_mem_forall_eq_of_le_of_comap_eq p hWo ⟨q₁, hq₁W, hq₁⟩
  have hCM := hqW
  simp only [Set.mem_ofPred_eq] at hCM
  set I := (q.asIdeal.under R).map (algebraMap R S)
  set qb := q.asIdeal.map (Ideal.Quotient.mk I)
  have hIq : I ≤ q.asIdeal := Ideal.map_comap_le
  have : IsNoetherianRing (Localization.AtPrime qb) :=
    IsLocalization.isNoetherianRing qb.primeCompl _ inferInstance
  obtain ⟨as, hasm, hreg, hdim⟩ := hCM.exists_isRegular_map_ringKrullDim_quotient_eq_zero
    (algebraMap S (Localization.AtPrime qb)) fun b => by
      obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj qb.primeCompl b
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨a, algebraMap (S ⧸ I) (Localization.AtPrime qb) s, IsLocalization.map_units _ s,
        by rw [IsScalarTower.algebraMap_apply S (S ⧸ I),
          Ideal.Quotient.algebraMap_eq]; exact hx.symm⟩
  set J := Ideal.ofList as
  have hJq : J ≤ q.asIdeal := by
    refine Ideal.span_le.mpr fun a ha => ?_
    have h := hasm a ha
    rw [IsScalarTower.algebraMap_apply S (S ⧸ I),
      IsLocalization.AtPrime.to_map_mem_maximal_iff _ qb] at h
    rw [← Ideal.comap_map_mk hIq]
    exact h
  have hflatp := Module.Flat.quotient_ofList_localization_of_isRegular q.asIdeal as
    (RingTheory.Sequence.IsRegular.map_quotient_maximalIdeal_localization q.asIdeal as hreg)
  have hqq : (q.asIdeal.map (Ideal.Quotient.mk J)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hflat'' := Module.Flat.localizedModule_quotient_ofList q.asIdeal as hJq hflatp
  let q'' : PrimeSpectrum (S ⧸ J) := ⟨_, hqq⟩
  have hcomap : ∀ Q : PrimeSpectrum (S ⧸ J), comap (algebraMap R (S ⧸ J)) Q =
      comap (algebraMap R S) (comap (Ideal.Quotient.mk J) Q) := fun Q => by
    rw [← comap_comp_apply]; rfl
  have hq''c : comap (Ideal.Quotient.mk J) q'' = q := PrimeSpectrum.ext (Ideal.comap_map_mk hJq)
  have hback : ∀ Q : PrimeSpectrum (S ⧸ J), comap (Ideal.Quotient.mk J) Q = q → Q = q'' := by
    intro Q h
    refine PrimeSpectrum.ext ?_
    have h' : Q.asIdeal.comap (Ideal.Quotient.mk J) = q.asIdeal :=
      congrArg PrimeSpectrum.asIdeal h
    rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q.asIdeal, h']
  have hQ'p : ∀ Q : PrimeSpectrum (S ⧸ J), comap (algebraMap R (S ⧸ J)) Q =
      comap (algebraMap R (S ⧸ J)) q'' →
        comap (algebraMap R S) (comap (Ideal.Quotient.mk J) Q) = p :=
    fun Q hQ => by rw [← hcomap, hQ, hcomap, hq''c, hqp]
  have hqf'' : Algebra.QuasiFiniteAt R q''.asIdeal := by
    refine Algebra.QuasiFiniteAt.of_forall_eq_of_comap_eq q'' (fun Q hQ hle => ?_)
      (fun Q hQ hle => ?_)
    · refine hback Q (hqmax _ (hQ'p Q hQ) ?_)
      rw [← hq''c]; exact Ideal.comap_mono (f := Ideal.Quotient.mk J) hle
    · refine hback Q (PrimeSpectrum.ext ?_)
      have hQ'p := hQ'p Q hQ
      refine Ideal.eq_of_le_of_ringKrullDim_quotient_localization_eq_zero q.asIdeal as hdim _
        ?_ ?_ ?_
      · refine Ideal.map_le_iff_le_comap.mpr ?_
        exact (congrArg PrimeSpectrum.asIdeal (hqp.trans hQ'p.symm)).le
      · intro x hx
        show Ideal.Quotient.mk J x ∈ Q.asIdeal
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
        exact Q.asIdeal.zero_mem
      · rw [← hq''c]; exact Ideal.comap_mono (f := Ideal.Quotient.mk J) hle
  have : Algebra.FinitePresentation R (S ⧸ J) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (List.finite_toSet as))
  have hU := (Module.isOpen_setOf_flat_localizedModule_atPrime (R := R) (S := S ⧸ J)
    (M := S ⧸ J)).inter (isOpen_quasiFiniteLocus R (S ⧸ J))
  obtain ⟨_, ⟨g, rfl⟩, hgq, hgU⟩ :=
    isTopologicalBasis_basic_opens.exists_subset_of_mem_open
      (show q'' ∈ {Q : PrimeSpectrum (S ⧸ J) |
        Module.Flat R (LocalizedModule.AtPrime Q.asIdeal (S ⧸ J))} ∩ quasiFiniteLocus R (S ⧸ J)
        from ⟨hflat'', hqf''⟩) hU
  obtain ⟨hfl, hqfl⟩ := Localization.Away.flat_and_quasiFinite_of_forall g
    (fun Q hQ => (hgU hQ).1) (fun Q hQ => (hgU hQ).2)
  refine ⟨Localization.Away g, inferInstance, inferInstance, inferInstance, inferInstance, hqfl,
    hfl, inferInstance, ?_⟩
  have hdisj : Disjoint (Submonoid.powers g : Set (S ⧸ J)) q''.asIdeal := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hgq (q''.2.mem_of_pow_mem n hn)
  have hP := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers g)
    (Localization.Away g) q''.asIdeal q''.2 hdisj
  refine ⟨⟨_, hP⟩, ?_⟩
  have h1 : comap (algebraMap (S ⧸ J) (Localization.Away g)) ⟨_, hP⟩ = q'' :=
    PrimeSpectrum.ext (IsLocalization.under_map_of_isPrime_disjoint _ _ q''.2 hdisj)
  rw [IsScalarTower.algebraMap_eq R (S ⧸ J) (Localization.Away g), comap_comp_apply, h1,
    hcomap, hq''c, hqp]

open PrimeSpectrum in
/-- Lemma 034Z over a Noetherian base: a faithfully flat ring map `R → S` of finite presentation
with `R` Noetherian factors through `R → S'` quasi-finite, faithfully flat and of finite
presentation; `S'` is a finite product of the rings of
`Algebra.exists_quasiFinite_flat_finitePresentation_mem_range`. -/
theorem Algebra.exists_quasiFinite_faithfullyFlat_finitePresentation_of_isNoetherianRing
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R]
    [Module.FaithfullyFlat R S] [Algebra.FinitePresentation R S] :
    ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra R S') (_ : Algebra S S')
      (_ : IsScalarTower R S S'), Algebra.QuasiFinite R S' ∧ Module.FaithfullyFlat R S' ∧
        Algebra.FinitePresentation R S' := by
  classical
  choose T _ _ _ _ hqf hfl hfp hmem using fun p : PrimeSpectrum R =>
    Algebra.exists_quasiFinite_flat_finitePresentation_mem_range (S := S) p
      (PrimeSpectrum.comap_surjective_of_faithfullyFlat p)
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover
    (fun p => Set.range (comap (algebraMap R (T p)))) fun p =>
      (primeSpectrum_comap_isOpenMap_of_flat_of_finitePresentation R (T p)).isOpen_range.mem_nhds
        (hmem p)
  refine ⟨(i : t) → T i, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_,
    inferInstance⟩
  · refine ⟨fun P _ => ?_⟩
    exact Module.Finite.equiv (_root_.TensorProduct.piRight R P.ResidueField P.ResidueField
      fun i : t => T i).symm
  · have : Module.Flat R ((i : t) → T i) :=
      Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := R)
        (M := fun i : t => T i)).symm
    refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_
    obtain ⟨i, hi, hpi⟩ := Set.mem_iUnion₂.mp (ht.ge (show p ∈ (⊤ : Set _) from trivial))
    obtain ⟨Q, hQ⟩ := hpi
    exact ⟨comap (Pi.evalRingHom (fun j : t => T j) ⟨i, hi⟩) Q, by
      rw [← comap_comp_apply]; exact hQ⟩

/-- **Stacks 034Z.** Let `R → S` be a faithfully flat ring map of finite presentation. Then there
is an `S`-algebra `S'` such that `R → S'` is quasi-finite, faithfully flat and of finite
presentation. -/
@[stacks 034Z "The commutative triangle is the data `R → S → S'` with `IsScalarTower R S S'`;
quasi-finiteness (Definition 00PL) is `Algebra.QuasiFinite`, which omits the finite type clause of
the source's definition, supplied here by `Algebra.FinitePresentation`. `S'` lives in the universe
of `R` and `S`.", ega "IV 17.16.2" "affine case"]
theorem Algebra.exists_quasiFinite_faithfullyFlat_finitePresentation
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [Algebra.FinitePresentation R S] :
    ∃ (S' : Type u) (_ : CommRing S') (_ : Algebra R S') (_ : Algebra S S')
      (_ : IsScalarTower R S S'), Algebra.QuasiFinite R S' ∧ Module.FaithfullyFlat R S' ∧
        Algebra.FinitePresentation R S' := by
  obtain ⟨R₀, S₀, _, _, _, _, _, _, _, _, _, _, _, _, _, hpush⟩ :=
    Algebra.exists_faithfullyFlat_finitePresentation_model (R := ℤ) (A := R) (B := S)
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  obtain ⟨T₀, _, _, _, _, _, _, _⟩ :=
    Algebra.exists_quasiFinite_faithfullyFlat_finitePresentation_of_isNoetherianRing
      (R := R₀) (S := S₀)
  let φ : S →ₐ[R] R ⊗[R₀] T₀ :=
    (Algebra.TensorProduct.map (AlgHom.id R R) (IsScalarTower.toAlgHom R₀ S₀ T₀)).comp
      hpush.equiv.symm.toAlgHom
  let _ : Algebra S (R ⊗[R₀] T₀) := φ.toRingHom.toAlgebra
  have : IsScalarTower R S (R ⊗[R₀] T₀) := .of_algebraMap_eq fun r => (φ.commutes r).symm
  exact ⟨R ⊗[R₀] T₀, inferInstance, inferInstance, inferInstance, this, inferInstance,
    inferInstance, inferInstance⟩
