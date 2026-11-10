module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.TotallySplit

/-!
# Lifting units and idempotents along étale maps

Let `A` be a commutative ring and `I` an ideal of `A`. Units and idempotents of `A ⧸ I` lift to
units and idempotents of an étale `A`-algebra `A'` for which the induced map `A ⧸ I → A' ⧸ IA'`
is an isomorphism.

## Main results

* `IsIdempotentElem.eq_of_isUnit_sub_one_add`: two idempotents `a`, `b` with `a - 1 + b` a unit
  are equal.
* `Ideal.quotientMap_bijective_of_lift`: the map `A ⧸ I → A' ⧸ IA'` induced by `φ : A →+* A'` is
  bijective as soon as `φ` admits a retraction `A' → A ⧸ I` compatible with the quotient by `IA'`.
* `Algebra.exists_etale_bijective_quotientMap_isIdempotentElem`: an idempotent of `A ⧸ I` lifts to
  an idempotent of an étale `A`-algebra `A'` with `A ⧸ I → A' ⧸ IA'` bijective.
* `Algebra.exists_etale_bijective_quotientMap_isUnit`: a unit of `A ⧸ I` lifts to a unit of an
  étale `A`-algebra `A'` with `A ⧸ I → A' ⧸ IA'` bijective.
* `exists_etale_lift_of_finite_disjoint_open_cover`: a finite disjoint open covering of
  `Spec (A ⧸ I)` lifts to one of `Spec A'` for such an `A'`.

## References

* [Stacks: Tag 07LX](https://stacks.math.columbia.edu/tag/07LX)
* [Stacks: Tag 07LY](https://stacks.math.columbia.edu/tag/07LY)
* [Stacks: Tag 07LZ](https://stacks.math.columbia.edu/tag/07LZ)
-/

@[expose] public section

universe u

/-- Two idempotents `a`, `b` of a commutative ring with `a - 1 + b` a unit are equal. -/
theorem IsIdempotentElem.eq_of_isUnit_sub_one_add {R : Type*} [CommRing R] {a b : R}
    (ha : IsIdempotentElem a) (hb : IsIdempotentElem b) (hu : IsUnit (a - 1 + b)) : a = b :=
  hu.mul_left_injective (by linear_combination ha.eq - hb.eq)

/-- If `φ : A →+* B` admits a retraction `g : B →+* A ⧸ I` that is compatible with the quotient
by `I.map φ`, then the induced map `A ⧸ I → B ⧸ I.map φ` is bijective. -/
theorem Ideal.quotientMap_bijective_of_lift {A B : Type*} [CommRing A] [CommRing B] {I : Ideal A}
    (φ : A →+* B) (g : B →+* A ⧸ I) (hg : ∀ a, g (φ a) = Ideal.Quotient.mk I a)
    (hq : ∀ b, Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map (g b)
      = Ideal.Quotient.mk (I.map φ) b) :
    Function.Bijective (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map) := by
  have hker : I.map φ ≤ RingHom.ker g :=
    Ideal.map_le_iff_le_comap.mpr fun a ha => by
      simpa [RingHom.mem_ker, hg a, Ideal.Quotient.eq_zero_iff_mem] using ha
  refine Function.bijective_iff_has_inverse.mpr
    ⟨Ideal.Quotient.lift _ g fun a ha => RingHom.mem_ker.mp (hker ha), ?_, ?_⟩
  · intro y
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.quotientMap_mk, Ideal.Quotient.lift_mk, hg a]
  · intro z
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [Ideal.Quotient.lift_mk, hq w]

/-- **Stacks 07LY**.
For an ideal `I` of `A` and an idempotent `e` of `A ⧸ I`, there is an étale `A`-algebra `A'` such
that the induced map `A ⧸ I → A' ⧸ IA'` is bijective, together with an idempotent `e'` of `A'`
whose class in `A' ⧸ IA'` is the image of `e`. -/
@[stacks 07LY]
theorem Algebra.exists_etale_bijective_quotientMap_isIdempotentElem {A : Type u} [CommRing A]
    (I : Ideal A) (e : A ⧸ I) (he : IsIdempotentElem e) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (e' : A'),
      Algebra.Etale A A' ∧ IsIdempotentElem e' ∧
      Function.Bijective
        (Ideal.quotientMap (I.map (algebraMap A A')) (algebraMap A A') Ideal.le_comap_map) ∧
      Ideal.Quotient.mk (I.map (algebraMap A A')) e' =
        Ideal.quotientMap (I.map (algebraMap A A')) (algebraMap A A') Ideal.le_comap_map e := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective e
  let P : StandardEtalePair A :=
    ⟨Polynomial.X ^ 2 - Polynomial.X,
      Polynomial.monic_X_pow_sub (lt_of_le_of_lt Polynomial.degree_X_le (by decide)),
      Polynomial.X - 1 + Polynomial.C x,
      ⟨Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.X), -4, 0, by
        simp only [pow_zero, Polynomial.derivative_sub, Polynomial.derivative_X_pow,
          Polynomial.derivative_X, Nat.cast_ofNat, map_ofNat]
        ring⟩⟩
  have hX : IsIdempotentElem P.X := by
    simpa [P, sub_eq_zero, sq, IsIdempotentElem] using P.hasMap_X.1
  have hmap : P.HasMap (Ideal.Quotient.mk I x) :=
    ⟨by simpa [P, sub_eq_zero, sq] using he.eq,
      IsUnit.of_mul_eq_one (Ideal.Quotient.mk I x - 1 + Ideal.Quotient.mk I x) <| by
        simp only [P, map_add, map_sub, Polynomial.aeval_X, map_one, Polynomial.aeval_C,
          Ideal.Quotient.algebraMap_eq]
        linear_combination 4 * he.eq⟩
  set J := I.map (algebraMap A P.Ring)
  set Q := Ideal.quotientMap J (algebraMap A P.Ring) Ideal.le_comap_map
  have hQe : Q (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J P.X :=
    (hX.map _).eq_of_isUnit_sub_one_add (he.map Q) (by
      simpa [Q, P] using P.hasMap_X.2.map (Ideal.Quotient.mk J)) |>.symm
  have hFG : (Ideal.quotientMapₐ J (Algebra.ofId A P.Ring) Ideal.le_comap_map).comp
      (P.lift _ hmap) = Ideal.Quotient.mkₐ A J :=
    P.hom_ext (by rw [AlgHom.comp_apply, P.lift_X]; exact hQe)
  exact ⟨P.Ring, inferInstance, inferInstance, P.X, inferInstance, hX,
    Ideal.quotientMap_bijective_of_lift (algebraMap A P.Ring) (P.lift _ hmap).toRingHom
      (P.lift _ hmap).commutes (AlgHom.congr_fun hFG), hQe.symm⟩

/-- **Stacks 07LX**.
For an ideal `I` of `A` and a unit `u` of `A ⧸ I`, there is an étale `A`-algebra `A'` such that
the induced map `A ⧸ I → A' ⧸ IA'` is bijective, together with a unit `u'` of `A'` whose class in
`A' ⧸ IA'` is the image of `u`. -/
@[stacks 07LX]
theorem Algebra.exists_etale_bijective_quotientMap_isUnit {A : Type u} [CommRing A] (I : Ideal A)
    (u : A ⧸ I) (hu : IsUnit u) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (u' : A'),
      Algebra.Etale A A' ∧ IsUnit u' ∧
      Function.Bijective
        (Ideal.quotientMap (I.map (algebraMap A A')) (algebraMap A A') Ideal.le_comap_map) ∧
      Ideal.Quotient.mk (I.map (algebraMap A A')) u' =
        Ideal.quotientMap (I.map (algebraMap A A')) (algebraMap A A') Ideal.le_comap_map u := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective u
  refine ⟨Localization.Away f, inferInstance, inferInstance, algebraMap A _ f, inferInstance,
    IsLocalization.Away.algebraMap_isUnit f, ?_, (Ideal.quotientMap_mk ..).symm⟩
  let g : Localization.Away f →+* A ⧸ I := IsLocalization.Away.lift f hu
  have hg (a : A) : g (algebraMap A _ a) = Ideal.Quotient.mk I a := IsLocalization.lift_eq _ a
  have key : (Ideal.quotientMap (I.map (algebraMap A (Localization.Away f)))
      (algebraMap A (Localization.Away f)) Ideal.le_comap_map).comp g
      = Ideal.Quotient.mk (I.map (algebraMap A (Localization.Away f))) :=
    IsLocalization.ringHom_ext (Submonoid.powers f) <| by
      ext a
      simp only [RingHom.comp_apply, hg a, Ideal.quotientMap_mk]
  exact Ideal.quotientMap_bijective_of_lift (algebraMap A (Localization.Away f)) g hg
    (RingHom.congr_fun key)

/-! ### Lifting a finite disjoint open covering of `Spec (A ⧸ I)`

An open and closed subset of a prime spectrum is cut out by an idempotent, so a finite disjoint
open covering of `Spec (A ⧸ I)` is the same data as a complete orthogonal family of idempotents
of `A ⧸ I`. Lifting the family one member at a time by
`Algebra.exists_etale_bijective_quotientMap_isIdempotentElem` above, then orthogonalizing the
lifts, produces the covering of `Spec A'`.
-/

universe v

private lemma member_isClopen_of_finite_disjoint_open_cover
    {X : Type*} [TopologicalSpace X] {J : Type*} [Finite J]
    (U : J → Set X) (hU_open : ∀ j, IsOpen (U j))
    (hU_disjoint : Pairwise fun i j ↦ Disjoint (U i) (U j))
    (hU_cover : ⋃ j, U j = Set.univ) (j : J) : IsClopen (U j) := by
  refine ⟨?_, hU_open j⟩
  apply isOpen_compl_iff.mp
  have hc : (U j)ᶜ = ⋃ i : {i : J // i ≠ j}, U i := by
    ext x
    refine ⟨fun hx ↦ ?_, fun hx hj ↦ ?_⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU_cover ▸ Set.mem_univ x : x ∈ ⋃ i, U i)
      exact Set.mem_iUnion.mpr ⟨⟨i, fun h ↦ hx (h ▸ hi)⟩, hi⟩
    · obtain ⟨⟨i, hij⟩, hi⟩ := Set.mem_iUnion.mp hx
      exact (Set.disjoint_left.mp (hU_disjoint hij)) hi hj
  rw [hc]
  exact isOpen_iUnion fun i ↦ hU_open i

private lemma preimage_basicOpen_comap
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    PrimeSpectrum.comap f ⁻¹' (PrimeSpectrum.basicOpen x : Set _) =
      (PrimeSpectrum.basicOpen (f x) : Set _) := by
  ext p
  rfl

/-- The quotient map for `g ∘ f` is the composite of those for `f` and `g`, up to the identification
of `Ideal.map g (Ideal.map f I)` with `Ideal.map (g.comp f) I`. -/
private lemma exists_quotientMap_comp_eq
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (I : Ideal A) (f : A →+* B) (g : B →+* C) :
    ∃ E : C ⧸ Ideal.map g (Ideal.map f I) ≃+* C ⧸ Ideal.map (g.comp f) I,
      (∀ y, E (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ y) ∧
      Ideal.quotientMap (Ideal.map (g.comp f) I) (g.comp f) Ideal.le_comap_map =
        E.toRingHom.comp
          ((Ideal.quotientMap (Ideal.map g (Ideal.map f I)) g Ideal.le_comap_map).comp
            (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map)) :=
  ⟨(Ideal.quotientEquivAlgOfEq ℤ (by rw [Ideal.map_map])).toRingEquiv, fun _ ↦ rfl, by ext x; rfl⟩

private lemma quotientMap_comp_bijective
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (I : Ideal A) (f : A →+* B) (g : B →+* C)
    (hf : Function.Bijective
      (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map))
    (hg : Function.Bijective
      (Ideal.quotientMap (Ideal.map g (Ideal.map f I)) g Ideal.le_comap_map)) :
    Function.Bijective
      (Ideal.quotientMap (Ideal.map (g.comp f) I) (g.comp f) Ideal.le_comap_map) := by
  obtain ⟨E, -, heq⟩ := exists_quotientMap_comp_eq I f g
  rw [heq]
  exact E.bijective.comp (hg.comp hf)

private lemma lift_idempotent_family
    {A : Type u} [CommRing A] (I : Ideal A) {J : Type v} [Finite J]
    (e : J → A ⧸ I) (he : ∀ j, IsIdempotentElem (e j)) :
    ∃ (A' : Type u) (_ : CommRing A') (f : A →+* A') (e' : J → A'),
      f.Etale ∧
      Function.Bijective
        (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map) ∧
      (∀ j, IsIdempotentElem (e' j)) ∧
      ∀ j, Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map (e j) =
        Ideal.Quotient.mk (Ideal.map f I) (e' j) := by
  classical
  induction J using Finite.induction_empty_option generalizing A with
  | of_equiv hJK ih =>
      obtain ⟨A', inst, f, e', hf, hq, he', hlift⟩ :=
        ih I (e ∘ hJK) (fun j ↦ he (hJK j))
      exact ⟨A', inst, f, fun j ↦ e' (hJK.symm j), hf, hq,
        fun j ↦ he' (hJK.symm j), fun j ↦ by simpa using hlift (hJK.symm j)⟩
  | h_empty =>
      refine ⟨A, inferInstance, RingHom.id A, fun j ↦ j.elim, ?_, ?_,
        fun j ↦ j.elim, fun j ↦ j.elim⟩
      · exact RingHom.Etale.of_bijective Function.bijective_id
      · constructor
        · apply Ideal.quotientMap_injective'
          simp
        · intro x
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
          exact ⟨Ideal.Quotient.mk I x, rfl⟩
  | @h_option J _ ih =>
      obtain ⟨B, instB, instAlgB, b, hbEt, hb, hqf, hbf'⟩ :=
        Algebra.exists_etale_bijective_quotientMap_isIdempotentElem I (e none) (he none)
      let f : A →+* B := algebraMap A B
      have hf : f.Etale := RingHom.etale_algebraMap.mpr hbEt
      have hbf : Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map (e none) =
          Ideal.Quotient.mk (Ideal.map f I) b := hbf'.symm
      let IB := Ideal.map f I
      let qf := Ideal.quotientMap IB f Ideal.le_comap_map
      obtain ⟨C, instC, g, c, hg, hqg, hc, hcg⟩ :=
        ih IB (fun j ↦ qf (e (some j))) (fun j ↦ (he (some j)).map qf)
      let IC := Ideal.map g IB
      let qg := Ideal.quotientMap IC g Ideal.le_comap_map
      refine ⟨C, instC, g.comp f,
        fun j ↦ Option.elim j (g b) c,
        RingHom.Etale.stableUnderComposition f g hf hg,
        quotientMap_comp_bijective I f g hqf hqg, ?_, ?_⟩
      · intro j
        cases j with
        | none => exact hb.map g
        | some j => exact hc j
      · intro j
        obtain ⟨E, hE, heq⟩ := exists_quotientMap_comp_eq I f g
        cases j with
        | none =>
          have hh : qg (qf (e none)) = Ideal.Quotient.mk IC (g b) := by
            rw [hbf]
            rfl
          rw [heq, RingHom.comp_apply, ← hE]
          exact congrArg E hh
        | some j =>
          rw [heq, RingHom.comp_apply, ← hE]
          exact congrArg E (hcg j)

private lemma orthogonalize_lifts
    {R S : Type*} [CommRing R] [CommRing S] (q : R →+* S)
    {J : Type v} [Finite J] (e : J → S) (d : J → R)
    (he : OrthogonalIdempotents e) (hd : ∀ j, IsIdempotentElem (d j))
    (hqd : ∀ j, q (d j) = e j) :
    ∃ d' : J → R, OrthogonalIdempotents d' ∧ ∀ j, q (d' j) = e j := by
  classical
  induction J using Finite.induction_empty_option with
  | of_equiv hJK ih =>
      obtain ⟨d', hd', hmap⟩ := ih (e ∘ hJK) (d ∘ hJK)
        ((OrthogonalIdempotents.equiv hJK).mpr he) (fun j ↦ hd (hJK j))
        (fun j ↦ hqd (hJK j))
      exact ⟨d' ∘ hJK.symm, (OrthogonalIdempotents.equiv hJK.symm).mpr hd',
        fun j ↦ by simpa using hmap (hJK.symm j)⟩
  | h_empty => exact ⟨fun j ↦ j.elim, ⟨fun j ↦ j.elim, fun i ↦ i.elim⟩, fun j ↦ j.elim⟩
  | @h_option J _ ih =>
      have het : OrthogonalIdempotents (e ∘ some) :=
        he.embedding ⟨some, Option.some_injective J⟩
      obtain ⟨d', hd', hmap⟩ := ih (e ∘ some) (d ∘ some) het
        (fun j ↦ hd (some j)) (fun j ↦ hqd (some j))
      let s : R := ∑ j, d' j
      let x : R := d none * (1 - s)
      have hs : IsIdempotentElem s := hd'.isIdempotentElem_sum
      have hx : IsIdempotentElem x := (hd none).mul hs.one_sub
      have hxs : x * s = 0 := by
        dsimp [x]
        rw [mul_assoc, sub_mul, one_mul, hs.eq, sub_self, mul_zero]
      have hsx : s * x = 0 := (mul_comm s x).trans hxs
      refine ⟨fun j ↦ Option.elim j x d', hd'.option x hx hxs hsx, ?_⟩
      intro j
      cases j with
      | none =>
          dsimp [x, s]
          rw [map_mul, map_sub, map_one, hqd, map_sum]
          simp_rw [hmap]
          rw [mul_sub, mul_one]
          have hz : e none * ∑ j, (e ∘ some) j = 0 := by
            rw [Finset.mul_sum]
            simp [he.mul_eq]
          rw [hz, sub_zero]
      | some j => exact hmap j

private lemma complete_lifts_of_nonempty
    {R S : Type*} [CommRing R] [CommRing S] (q : R →+* S)
    {J : Type v} [Fintype J] [Nonempty J] (e : J → S) (d : J → R)
    (he : CompleteOrthogonalIdempotents e) (hd : ∀ j, IsIdempotentElem (d j))
    (hqd : ∀ j, q (d j) = e j) :
    ∃ d' : J → R, CompleteOrthogonalIdempotents d' ∧ ∀ j, q (d' j) = e j := by
  classical
  let j₀ : J := Classical.arbitrary J
  let K := {j : J // j ≠ j₀}
  obtain ⟨dK, hdK, hmapK⟩ := orthogonalize_lifts q (fun k : K ↦ e k) (fun k : K ↦ d k)
    (he.toOrthogonalIdempotents.embedding ⟨Subtype.val, Subtype.val_injective⟩)
    (fun k ↦ hd k) (fun k ↦ hqd k)
  let x := 1 - ∑ k : K, dK k
  let E : Option K ≃ J := Equiv.optionSubtypeNe j₀
  let dO : Option K → R := fun t ↦ Option.elim t x dK
  let d' : J → R := dO ∘ E.symm
  refine ⟨d', ?_, ?_⟩
  · exact (CompleteOrthogonalIdempotents.equiv E.symm).mpr
      (@CompleteOrthogonalIdempotents.option R _ K dK _ hdK)
  · intro j
    obtain ⟨t, rfl⟩ := E.surjective j
    cases t with
    | none =>
      dsimp [d']
      rw [E.symm_apply_apply]
      change q x = e j₀
      dsimp [x]
      rw [map_sub, map_one, map_sum]
      simp_rw [hmapK]
      rw [← he.complete]
      have hsume : ∑ k : K, e k = ∑ j ∈ Finset.univ.erase j₀, e j := by
        symm
        apply Finset.sum_subtype
        intro j
        simp
      rw [hsume, ← Finset.sum_erase_add Finset.univ e (Finset.mem_univ j₀)]
      ring
    | some k =>
      dsimp [d']
      rw [E.symm_apply_apply]
      change q (dK k) = e k
      exact hmapK k

/-- **Stacks 07LZ.** A finite disjoint open covering of `Spec(A ⧸ I)` lifts to a finite disjoint
open covering after an étale extension `A → A'` inducing an isomorphism modulo `I`. -/
@[stacks 07LZ]
theorem exists_etale_lift_of_finite_disjoint_open_cover
    {A : Type u} [CommRing A] (I : Ideal A) {J : Type v} [Finite J]
    (U : J → Set (PrimeSpectrum (A ⧸ I)))
    (hU_open : ∀ j, IsOpen (U j))
    (hU_disjoint : Pairwise fun i j ↦ Disjoint (U i) (U j))
    (hU_cover : ⋃ j, U j = Set.univ) :
    ∃ (A' : Type u) (_ : CommRing A') (f : A →+* A')
      (U' : J → Set (PrimeSpectrum A')),
      f.Etale ∧
      Function.Bijective
        (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map) ∧
      (∀ j, IsOpen (U' j)) ∧
      (Pairwise fun i j ↦ Disjoint (U' i) (U' j)) ∧
      (⋃ j, U' j = Set.univ) ∧
      ∀ j,
        PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.map f I)) ⁻¹' U' j =
          PrimeSpectrum.comap
            (Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map) ⁻¹' U j := by
  classical
  choose e he hUe using fun j ↦
    PrimeSpectrum.isClopen_iff.mp
      (member_isClopen_of_finite_disjoint_open_cover U hU_open hU_disjoint hU_cover j)
  let := Fintype.ofFinite J
  have heO : OrthogonalIdempotents e := by
    refine ⟨he, ?_⟩
    intro i j hij
    apply IsIdempotentElem.eq_zero_of_isNilpotent ((he i).mul (he j))
    rw [← PrimeSpectrum.basicOpen_eq_bot_iff, PrimeSpectrum.basicOpen_mul]
    apply SetLike.coe_injective
    simpa [← hUe i, ← hUe j] using Set.disjoint_iff_inter_eq_empty.mp (hU_disjoint hij)
  have heC : CompleteOrthogonalIdempotents e := by
    refine ⟨heO, ?_⟩
    let s := ∑ j, e j
    have hs : IsIdempotentElem s := heO.isIdempotentElem_sum
    have hn : IsNilpotent (1 - s) := by
      rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
      apply SetLike.coe_injective
      ext p
      simp only [TopologicalSpace.Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      intro hp
      have hpcover : p ∈ ⋃ j, U j := by rw [hU_cover]; trivial
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hpcover
      have hej : e j ∉ p.asIdeal := by simpa [hUe j] using hj
      have hz : e j * (1 - s) = 0 := by
        rw [mul_sub, mul_one, heO.mul_sum_of_mem (Finset.mem_univ j), sub_self]
      exact hp ((p.2.mem_or_mem (hz ▸ p.asIdeal.zero_mem)).resolve_left hej)
    exact (sub_eq_zero.mp (hs.one_sub.eq_zero_of_isNilpotent hn)).symm
  cases isEmpty_or_nonempty J with
  | inl hJ =>
    have hspec : IsEmpty (PrimeSpectrum (A ⧸ I)) :=
      ⟨fun p ↦ by simpa using (hU_cover ▸ Set.mem_univ p : p ∈ ⋃ j, U j)⟩
    have : Subsingleton (A ⧸ I) := PrimeSpectrum.isEmpty_iff_subsingleton.mp hspec
    exact ⟨A ⧸ I, inferInstance, algebraMap A (A ⧸ I), fun j ↦ isEmptyElim j,
      RingHom.etale_algebraMap.mpr inferInstance,
      ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨default, Subsingleton.elim _ _⟩⟩,
      fun j ↦ isEmptyElim j, fun i ↦ isEmptyElim i, Set.eq_univ_of_forall isEmptyElim,
      fun j ↦ isEmptyElim j⟩
  | inr hJ =>
    obtain ⟨A', inst, f, d, hf, hq, hd, hlift⟩ := lift_idempotent_family I e he
    let q := Ideal.quotientMap (Ideal.map f I) f Ideal.le_comap_map
    obtain ⟨e', he', he'lift⟩ := complete_lifts_of_nonempty
      (Ideal.Quotient.mk (Ideal.map f I)) (q ∘ e) d (heC.map q) hd
        (fun j ↦ (hlift j).symm)
    refine ⟨A', inst, f, fun j ↦ PrimeSpectrum.basicOpen (e' j), hf, hq,
      fun j ↦ (PrimeSpectrum.basicOpen (e' j)).2, ?_, ?_, ?_⟩
    · exact fun i j hij ↦ Set.disjoint_left.mpr fun p hi hj ↦
        hj ((p.2.mem_or_mem (by simp [he'.mul_eq, hij])).resolve_left hi)
    · refine Set.eq_univ_of_forall fun p ↦ ?_
      by_contra hp
      simp only [Set.mem_iUnion, not_exists] at hp
      have : (1 : A') ∈ p.asIdeal := he'.complete ▸ p.asIdeal.sum_mem fun j _ ↦ by
        simpa [PrimeSpectrum.mem_basicOpen] using hp j
      exact p.2.ne_top ((Ideal.eq_top_iff_one p.asIdeal).mpr this)
    · intro j
      rw [hUe j, preimage_basicOpen_comap, preimage_basicOpen_comap]
      simp only [Function.comp_apply] at he'lift
      rw [he'lift j]
