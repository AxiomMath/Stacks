module

public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing.AssociatedGraded
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Noetherianity of the associated-graded module

Given generators `a : Fin t → S` of an ideal `J` with `S ⧸ J` Noetherian, the associated-graded
module `grModule S J = ⨁ₙ J^n/J^{n+1}` is a Noetherian module over
`P = MvPolynomial (Fin t) (S ⧸ J)` (`grModule_noetherian`). The lemmas that follow compute the
action of a monomial of `P` on a homogeneous leading-form class and read off its degree-`N`
component as an explicit `S`-multiple (`component_smul_lof`).
-/

@[expose] public section


open AdicCompletion

/-- The degree of `single i b + μ` is `b` plus the degree of `μ`. -/
private lemma sum_single_add_eq {t : ℕ} (i : Fin t) (b : ℕ) (μ : Fin t →₀ ℕ) :
    ((Finsupp.single i b + μ).sum fun _ e => e) = b + (μ.sum fun _ e => e) := by
  rw [Finsupp.sum_add_index (by intros; rfl) (by intros; rfl), Finsupp.sum_single_index rfl]

/-- The monomial `a^(single i b + μ)` equals `a i ^ b * a^μ`. -/
private lemma prod_pow_single_add {S : Type*} [CommRing S] {t : ℕ} (a : Fin t → S) (i : Fin t)
    (b : ℕ) (μ : Fin t →₀ ℕ) :
    (∏ k, a k ^ (Finsupp.single i b + μ) k) = a i ^ b * ∏ k, a k ^ μ k := by
  simp_rw [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single i]
  · rw [Finsupp.single_eq_same]
  · intro k _ hk; rw [Finsupp.single_eq_of_ne (Ne.symm hk).symm, pow_zero]
  · simp

/-- `a^μ = ∏ i, a i ^ μ i` lies in `J^|μ|`. -/
private lemma prod_pow_mem_pow {S : Type*} [CommRing S] {J : Ideal S} {t : ℕ} {a : Fin t → S}
    (ha : J = Ideal.span (Set.range a)) (μ : Fin t →₀ ℕ) :
    (∏ i, a i ^ μ i) ∈ (J ^ (μ.sum fun _ e => e) : Ideal S) := by
  rw [star_pow_eq_span_monomials _ J t a ha (μ.sum fun _ e => e)]
  exact Ideal.subset_span ⟨μ, rfl, rfl⟩

/-- Multiplying an element of `J^k` by an element of `J^n` gives an element of `J^(n+k)`. -/
private lemma mul_mem_pow_add {S : Type*} [CommRing S] {J : Ideal S} {n k : ℕ} {x w : S}
    (hx : x ∈ (J ^ k : Ideal S)) (hw : w ∈ (J ^ n : Ideal S)) :
    x * w ∈ (J ^ (n + k) : Ideal S) := by
  rw [pow_add, mul_comm (J ^ n)]
  exact Ideal.mul_mem_mul hx hw

/-- The associated-graded module `grModule S J = ⨁ₙ J^n/J^{n+1}` is a Noetherian module over
`P = MvPolynomial (Fin t) (S ⧸ J)` when `S ⧸ J` is Noetherian.  Indeed `P` is Noetherian by
the Hilbert basis theorem, and `grModule S J` is generated over `P` by the single degree-`0`
element `1 + J`, because `J^n` is spanned by the degree-`n` monomials in the generators
(`star_pow_eq_span_monomials`). -/
@[sga "5 V 5.1.6" "special case"]
lemma grModule_noetherian (S : Type*) [CommRing S] (J : Ideal S) (t : ℕ) (a : Fin t → S)
    (ha : J = Ideal.span (Set.range a)) (hquot : IsNoetherianRing (S ⧸ J)) :
    letI := grModulePModule S J t a ha
    IsNoetherian (MvPolynomial (Fin t) (S ⧸ J)) (grModule S J) := by
  let := grModulePModule S J t a ha
  have : IsNoetherianRing (MvPolynomial (Fin t) (S ⧸ J)) := MvPolynomial.isNoetherianRing
  -- the degree-0 generator: class of (1 : S) in grPiece 0
  set g : grModule S J :=
    (DirectSum.lof S ℕ (fun n => grPiece S J n) 0
      (grMk S J 0 ⟨1, by simp⟩) : grModule S J) with hg
  -- abbreviation for the polynomial ring
  set P := MvPolynomial (Fin t) (S ⧸ J)
  -- the homogeneous-injection, typed into `grModule S J` so the `P`-action is found
  let lf : ∀ (n : ℕ), grPiece S J n → grModule S J :=
    fun n x => (DirectSum.lof S ℕ (fun n => grPiece S J n) n x : grModule S J)
  -- action of X i on a homogeneous leading-form class
  have hXsmul : ∀ (i : Fin t) (m : ℕ) (x : grPiece S J m),
      (MvPolynomial.X i : P) • (lf m x) =
        lf (m + 1) (grShift S J 1 (a i) (mulA_hai S J t a ha i) m x) := by
    intro i m x
    show (MvPolynomial.X i : P) • (lf m x) = lf (m + 1) (grShift S J 1 (a i) (mulA_hai S J t a ha
        i) m x)
    show grModuleRingHom S J t a ha (MvPolynomial.X i)
        (DirectSum.lof S ℕ (fun n => grPiece S J n) m x)
      = (DirectSum.lof S ℕ (fun n => grPiece S J n) (m + 1)
          (grShift S J 1 (a i) (mulA_hai S J t a ha i) m x))
    rw [show grModuleRingHom S J t a ha (MvPolynomial.X i)
          (DirectSum.lof S ℕ (fun n => grPiece S J n) m x)
        = mulA S J t a ha i (DirectSum.lof S ℕ (fun n => grPiece S J n) m x) from
        grModule_X_smul S J t a ha i _]
    rw [mulA_lof S J t a ha i m x]
  -- the S⧸J-scalar action commutes with lf
  have hlf_smul : ∀ (c : S ⧸ J) (n : ℕ) (x : grPiece S J n), c • (lf n x) = lf n (c • x) := by
    intro c n x
    show c • (DirectSum.lof S ℕ (fun n => grPiece S J n) n x : grModule S J)
      = (DirectSum.lof S ℕ (fun n => grPiece S J n) n (c • x) : grModule S J)
    have heq : (DirectSum.lof S ℕ (fun n => grPiece S J n) n x : grModule S J)
        = DirectSum.lof (S ⧸ J) ℕ (fun n => grPiece S J n) n x := rfl
    have heq2 : (DirectSum.lof S ℕ (fun n => grPiece S J n) n (c • x) : grModule S J)
        = DirectSum.lof (S ⧸ J) ℕ (fun n => grPiece S J n) n (c • x) := rfl
    rw [heq, heq2, ← LinearMap.map_smul]
  have hlf_zero : ∀ n, lf n (grMk S J n 0) ∈ Submodule.span P {g} := fun n => by
    simp [lf, grMk]
  have hlf_add : ∀ (n : ℕ) (x y : (J ^ n : Ideal S)),
      lf n (grMk S J n x) ∈ Submodule.span P {g} → lf n (grMk S J n y) ∈ Submodule.span P {g} →
      lf n (grMk S J n (x + y)) ∈ Submodule.span P {g} := fun n x y hx hy => by
    have : lf n (grMk S J n (x + y)) = lf n (grMk S J n x) + lf n (grMk S J n y) := by
      simp [lf, grMk]
    rw [this]
    exact Submodule.add_mem _ hx hy
  have hai : ∀ i, a i ∈ J := fun i => by simpa using mulA_hai S J t a ha i
  -- the X i-step: multiplying the underlying element by a i, going up one degree,
  -- preserves membership in span P {g}
  have hstep : ∀ (i : Fin t) (n : ℕ) (w : (J ^ n : Ideal S)),
      lf n (grMk S J n w) ∈ Submodule.span P {g} →
      lf (n + 1) (grMk S J (n + 1) ⟨a i * w, mul_mem_pow_add (mulA_hai S J t a ha i) w.2⟩)
        ∈ Submodule.span P {g} := by
    intro i n w hw
    have hkey : lf (n + 1) (grMk S J (n + 1) ⟨a i * w, mul_mem_pow_add (mulA_hai S J t a ha i) w.2⟩)
        = (MvPolynomial.X i : P) • (lf n (grMk S J n w)) := by
      rw [hXsmul i n (grMk S J n w), grShift_grMk S J 1 n (a i) (mulA_hai S J t a ha i) w]
    rw [hkey]
    exact Submodule.smul_mem _ _ hw
  -- multiplying by an S-scalar r is the action of C (mk r)
  have hSsmul : ∀ (n : ℕ) (r : S) (v : (J ^ n : Ideal S)),
      lf n (grMk S J n ⟨r * v, by
        have : r • (v : S) ∈ (J ^ n : Ideal S) := (J ^ n : Ideal S).smul_mem r v.property
        simpa [smul_eq_mul] using this⟩)
        = (MvPolynomial.C (Ideal.Quotient.mk J r) : P) • lf n (grMk S J n v) := by
    intro n r v
    have hv : (⟨r * v, by
        have : r • (v : S) ∈ (J ^ n : Ideal S) := (J ^ n : Ideal S).smul_mem r v.property
        simpa [smul_eq_mul] using this⟩ : (J ^ n : Ideal S)) = r • v := by
      ext; simp [smul_eq_mul]
    rw [hv]
    show lf n (grMk S J n (r • v)) = _
    have hrs : grMk S J n (r • v) = (Ideal.Quotient.mk J r) • grMk S J n v := by
      unfold grMk; rw [Submodule.Quotient.mk_smul, grPiece_smul_mk]
    rw [hrs, ← hlf_smul, grModule_C_smul S J t a ha]
  -- multiplying the underlying element by an arbitrary c ∈ J preserves span-membership
  have hJfac : ∀ (n : ℕ) (u : (J ^ n : Ideal S)),
      lf n (grMk S J n u) ∈ Submodule.span P {g} →
      ∀ (c : S) (hc : c ∈ J) (hcu : c * (u : S) ∈ (J ^ (n + 1) : Ideal S)),
        lf (n + 1) (grMk S J (n + 1) ⟨c * u, hcu⟩) ∈ Submodule.span P {g} := by
    intro n u hu c hc
    have hmulu : ∀ y ∈ Ideal.span (Set.range a), y * (u : S) ∈ (J ^ (n + 1) : Ideal S) :=
      fun y hy => mul_mem_pow_add (by rwa [pow_one, ha]) u.2
    rw [ha] at hc
    refine Submodule.span_induction
      (p := fun c (_ : c ∈ Ideal.span (Set.range a)) =>
        ∀ (hcu : c * (u : S) ∈ (J ^ (n + 1) : Ideal S)),
          lf (n + 1) (grMk S J (n + 1) ⟨c * u, hcu⟩) ∈ Submodule.span P {g})
      ?_ ?_ ?_ ?_ hc
    · -- generators a i
      rintro y ⟨i, rfl⟩ hcu
      have := hstep i n u hu
      convert this using 3
    · -- zero
      intro hcu
      have : (⟨(0:S) * u, hcu⟩ : (J ^ (n+1) : Ideal S)) = 0 := by ext; simp
      rw [this]
      exact hlf_zero _
    · -- add
      intro y z hy hz hyih hzih hcu
      have hsplit : (⟨(y + z) * u, hcu⟩ : (J ^ (n+1) : Ideal S))
          = ⟨y * u, hmulu y hy⟩ + ⟨z * u, hmulu z hz⟩ := by ext; simp [add_mul]
      rw [hsplit]
      exact hlf_add _ _ _ (hyih _) (hzih _)
    · -- smul
      intro r y hy hyih hcu
      have hyu := hmulu y hy
      have heqv : (⟨(r • y) * u, hcu⟩ : (J ^ (n+1) : Ideal S))
          = ⟨r * ((⟨y * u, hyu⟩ : (J ^ (n+1) : Ideal S)) : S), by
              simpa [mul_assoc] using (J ^ (n+1) : Ideal S).mul_mem_left r hyu⟩ := by
        ext; simp [smul_eq_mul]; ring
      rw [heqv]
      rw [hSsmul (n + 1) r ⟨y * u, hyu⟩]
      exact Submodule.smul_mem _ _ (hyih hyu)
  -- congruence: equal degrees and equal underlying values give equal span-membership
  have hcong : ∀ (n n' : ℕ) (hn : n = n') (v : (J ^ n : Ideal S)) (v' : (J ^ n' : Ideal S)),
      (v : S) = (v' : S) →
      lf n (grMk S J n v) ∈ Submodule.span P {g} →
      lf n' (grMk S J n' v') ∈ Submodule.span P {g} := by
    intro n n' hn v v' hv hmem
    subst hn
    have : v = v' := Subtype.ext hv
    rwa [this] at hmem
  -- multiplying by a power a i ^ b lifts span-membership up b degrees
  have hpow : ∀ (i : Fin t) (b : ℕ) (n : ℕ) (w : (J ^ n : Ideal S)),
      lf n (grMk S J n w) ∈ Submodule.span P {g} →
      ∀ (hbw : (a i) ^ b * (w : S) ∈ (J ^ (n + b) : Ideal S)),
        lf (n + b) (grMk S J (n + b) ⟨(a i) ^ b * w, hbw⟩) ∈ Submodule.span P {g} := by
    intro i b
    induction b with
    | zero =>
      intro n w hw hbw
      refine hcong n (n + 0) (by ring) w ⟨(a i) ^ 0 * w, hbw⟩ ?_ hw
      simp
    | succ b ih =>
      intro n w hw hbw
      have haib : (a i) ^ b * (w : S) ∈ (J ^ (n + b) : Ideal S) :=
        mul_mem_pow_add (Ideal.pow_mem_pow (hai i) b) w.2
      have hstepres := hstep i (n + b) ⟨(a i) ^ b * w, haib⟩ (ih n w hw haib)
      refine hcong (n + b + 1) (n + (b + 1)) (by ring) _ _ ?_ hstepres
      simp [pow_succ]; ring
  -- monomial action: a^μ-class at degree |μ| lies in span P {g}
  have hmon : ∀ (μ : Fin t →₀ ℕ) (n : ℕ) (hn : (μ.sum fun _ e => e) = n)
      (hmem : (∏ i, a i ^ μ i) ∈ (J ^ n : Ideal S)),
      lf n (grMk S J n ⟨∏ i, a i ^ μ i, hmem⟩) ∈ Submodule.span P {g} := by
    intro μ
    induction μ using Finsupp.induction with
    | zero =>
      intro n hn hmem
      have hdeg : ((0 : Fin t →₀ ℕ).sum fun _ e => e) = 0 := by simp
      rw [hdeg] at hn
      refine hcong 0 n hn ⟨1, by simp⟩ _ ?_ ?_
      · simp
      · have hg1 : lf 0 (grMk S J 0 ⟨1, by simp⟩) = g := by rw [hg]
        rw [hg1]; exact Submodule.mem_span_singleton_self g
    | single_add i b μ' hi hb ih =>
      intro n hn hmem
      have hμ'mem := prod_pow_mem_pow ha μ'
      have ihres := ih (μ'.sum fun _ e => e) rfl hμ'mem
      have hbw := mul_mem_pow_add (Ideal.pow_mem_pow (hai i) b) hμ'mem
      have hpowres := hpow i b (μ'.sum fun _ e => e) ⟨∏ k, a k ^ μ' k, hμ'mem⟩ ihres hbw
      refine hcong ((μ'.sum fun _ e => e) + b) n ?_ _ _ ?_ hpowres
      · rw [← hn, sum_single_add_eq]; ring
      · simp only []; rw [prod_pow_single_add]
  -- spanning of each degree piece, by induction over star_pow's span structure
  have hpiece : ∀ (n : ℕ) (w : (J ^ n : Ideal S)),
      lf n (grMk S J n w) ∈ Submodule.span P {g} := by
    intro n w
    have hwspan : (w : S) ∈ Ideal.span ((fun μ : Fin t →₀ ℕ => ∏ i, a i ^ μ i) ''
        {μ : Fin t →₀ ℕ | (μ.sum fun _ e => e) = n}) := by
      rw [← star_pow_eq_span_monomials S J t a ha n]; exact w.property
    refine Submodule.span_induction
      (p := fun v (_ : v ∈ Ideal.span ((fun μ : Fin t →₀ ℕ => ∏ i, a i ^ μ i) ''
          {μ : Fin t →₀ ℕ | (μ.sum fun _ e => e) = n})) =>
        ∀ (hv : v ∈ (J ^ n : Ideal S)),
          lf n (grMk S J n ⟨v, hv⟩) ∈ Submodule.span P {g})
      ?_ ?_ ?_ ?_ hwspan w.property
    · -- generators a^μ with |μ| = n
      rintro v ⟨μ, hμ, rfl⟩ hv
      simp only [Set.mem_ofPred_eq] at hμ
      exact hmon μ n hμ hv
    · -- zero
      intro hv
      have : (⟨(0:S), hv⟩ : (J ^ n : Ideal S)) = 0 := by ext; rfl
      rw [this]
      show lf n (grMk S J n 0) ∈ _
      have h0 : grMk S J n 0 = 0 := by unfold grMk; simp
      rw [h0]
      show (DirectSum.lof S ℕ (fun n => grPiece S J n) n 0 : grModule S J) ∈ _
      rw [_root_.map_zero]; exact Submodule.zero_mem _
    · -- add
      intro x y hx hy hxih hyih hv
      have hxmem : x ∈ (J ^ n : Ideal S) := by
        rw [star_pow_eq_span_monomials S J t a ha n]; exact hx
      have hymem : y ∈ (J ^ n : Ideal S) := by
        rw [star_pow_eq_span_monomials S J t a ha n]; exact hy
      have hsplit : (⟨x + y, hv⟩ : (J ^ n : Ideal S)) = ⟨x, hxmem⟩ + ⟨y, hymem⟩ := by ext; simp
      rw [hsplit]
      show lf n (grMk S J n (⟨x, hxmem⟩ + ⟨y, hymem⟩)) ∈ _
      have hgadd : grMk S J n (⟨x, hxmem⟩ + ⟨y, hymem⟩)
          = grMk S J n ⟨x, hxmem⟩ + grMk S J n ⟨y, hymem⟩ := by
        unfold grMk; rw [Submodule.Quotient.mk_add]
      rw [hgadd]
      show (DirectSum.lof S ℕ (fun n => grPiece S J n) n
          (grMk S J n ⟨x, hxmem⟩ + grMk S J n ⟨y, hymem⟩) : grModule S J) ∈ _
      rw [map_add]
      exact Submodule.add_mem _ (hxih hxmem) (hyih hymem)
    · -- smul
      intro r v hv hvih hrv
      have hvmem : v ∈ (J ^ n : Ideal S) := by
        rw [star_pow_eq_span_monomials S J t a ha n]; exact hv
      have heqv : (⟨r • v, hrv⟩ : (J ^ n : Ideal S))
          = ⟨r * ((⟨v, hvmem⟩ : (J ^ n : Ideal S)) : S), by
              simpa [smul_eq_mul] using ((J ^ n : Ideal S).smul_mem r hvmem)⟩ := by
        ext; simp [smul_eq_mul]
      rw [heqv, hSsmul n r ⟨v, hvmem⟩]
      exact Submodule.smul_mem _ _ (hvih hvmem)
  -- conclude: span P {g} = ⊤
  have hspan : Submodule.span P {g} = ⊤ := by
    rw [eq_top_iff]
    intro y _
    refine DirectSum.induction_on y ?_ ?_ ?_
    · exact Submodule.zero_mem _
    · intro n x
      induction x using Submodule.Quotient.induction_on with
      | _ z =>
        show (DirectSum.lof S ℕ (fun n => grPiece S J n) n (grMk S J n z) : grModule S J)
            ∈ Submodule.span P {g}
        exact hpiece n z
    · intro p q hp hq
      exact Submodule.add_mem _ hp hq
  -- finite ⟹ noetherian (P is Noetherian)
  have : Module.Finite P (grModule S J) := ⟨⟨{g}, by simpa using hspan⟩⟩
  infer_instance

/-! ### The monomial shift and the action of a monomial on a homogeneous class

The monomial shift `σ_μ : grPiece S J m → grPiece S J (m + |μ|)` is multiplication by
`a^μ = ∏ i, a i ^ μ i` on leading forms; the lemmas below compute the action of a monomial
of `P = MvPolynomial (Fin t) (S ⧸ J)` on a homogeneous leading-form class, and read off the
degree-`N` component of such an action as an explicit `S`-multiple. -/

/-- `a^μ = ∏ i, a i ^ μ i` lies in `J^|μ|`. -/
lemma aMon_mem_pow (S : Type*) [CommRing S] (J : Ideal S) (t : ℕ) (a : Fin t → S)
    (ha : J = Ideal.span (Set.range a)) (μ : Fin t →₀ ℕ) :
    (∏ i, a i ^ μ i) ∈ (J ^ (μ.sum fun _ e => e) : Ideal S) := by
  exact prod_pow_mem_pow ha μ

/-- Congruence for homogeneous lifted classes across propositionally-equal degrees
and equal underlying values. -/
lemma lof_grMk_congr (S : Type*) [CommRing S] (J : Ideal S) (n n' : ℕ) (hn : n = n')
    (v : (J ^ n : Ideal S)) (v' : (J ^ n' : Ideal S)) (hv : (v : S) = (v' : S)) :
    DirectSum.lof S ℕ (fun k => grPiece S J k) n (grMk S J n v)
      = DirectSum.lof S ℕ (fun k => grPiece S J k) n' (grMk S J n' v') := by
  subst hn
  have : v = v' := Subtype.ext hv
  rw [this]

/-- Iterating `mulA i` (= multiplication by `a i`) `b` times on a homogeneous
lifted class multiplies the underlying value by `a i ^ b` and raises the degree
by `b`. -/
lemma mulA_pow_lof_grMk (S : Type*) [CommRing S] (J : Ideal S) (t : ℕ) (a : Fin t → S)
    (ha : J = Ideal.span (Set.range a)) (i : Fin t) (b : ℕ) (m : ℕ) (z : (J ^ m : Ideal S)) :
    ((mulA' S J t a ha i) ^ b) (DirectSum.lof S ℕ (fun n => grPiece S J n) m (grMk S J m z))
      = DirectSum.lof S ℕ (fun n => grPiece S J n) (m + b)
          (grMk S J (m + b) ⟨a i ^ b * z, by
            rw [pow_add, mul_comm (J ^ m)]
            exact Ideal.mul_mem_mul (by
              have hai : a i ∈ J ^ 1 := mulA_hai S J t a ha i
              have : a i ^ b ∈ (J ^ 1) ^ b := Ideal.pow_mem_pow hai b
              rwa [← pow_mul, one_mul] at this) z.2⟩) := by
  induction b generalizing m z with
  | zero =>
    simp only [pow_zero, Module.End.one_apply]
    refine lof_grMk_congr S J _ _ (by ring) _ _ ?_
    show (z : S) = 1 * z
    rw [one_mul]
  | succ b ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    rw [mulA'_apply, mulA_lof, grShift_grMk]
    refine lof_grMk_congr S J _ _ (by ring) _ _ ?_
    show a i * (a i ^ b * (z : S)) = a i ^ (b + 1) * z
    rw [pow_succ]; ring

/-- Monomial action on a homogeneous lifted leading-form class: the monoid-hom
`mulAMonoidHom μ` applied to `lof m (grMk z)` multiplies the underlying value by
`a^μ` and shifts the degree up by `|μ|`. -/
lemma mulAMonoidHom_lof_grMk (S : Type*) [CommRing S] (J : Ideal S) (t : ℕ) (a : Fin t → S)
    (ha : J = Ideal.span (Set.range a)) (μ : Fin t →₀ ℕ) (m : ℕ) (z : (J ^ m : Ideal S)) :
    mulAMonoidHom S J t a ha (Multiplicative.ofAdd μ)
        (DirectSum.lof S ℕ (fun n => grPiece S J n) m (grMk S J m z))
      = DirectSum.lof S ℕ (fun n => grPiece S J n) (m + (μ.sum fun _ e => e))
          (grMk S J (m + (μ.sum fun _ e => e)) ⟨(∏ i, a i ^ μ i) * z, by
            rw [pow_add, mul_comm (J ^ m)]
            exact Ideal.mul_mem_mul (aMon_mem_pow S J t a ha μ) z.2⟩) := by
  classical
  induction μ using Finsupp.induction generalizing m z with
  | zero =>
    simp only [ofAdd_zero, map_one, Module.End.one_apply, Finsupp.sum_zero_index]
    refine lof_grMk_congr S J _ _ rfl _ _ ?_
    show (z : S) = (∏ i, a i ^ (0 : Fin t →₀ ℕ) i) * z
    simp
  | single_add i b μ' hi hb ih =>
    -- split the monoid-hom
    have hsplit : mulAMonoidHom S J t a ha (Multiplicative.ofAdd (Finsupp.single i b + μ'))
        = ((mulA' S J t a ha i) ^ b) * mulAMonoidHom S J t a ha (Multiplicative.ofAdd μ') := by
      rw [show (Multiplicative.ofAdd (Finsupp.single i b + μ'))
            = Multiplicative.ofAdd (Finsupp.single i b) * Multiplicative.ofAdd μ' from rfl,
        map_mul]
      congr 1
      have hbpow : (Multiplicative.ofAdd (Finsupp.single i b : Fin t →₀ ℕ))
          = (Multiplicative.ofAdd (Finsupp.single i 1)) ^ b := by
        rw [← ofAdd_nsmul]
        congr 1
        ext j
        simp [Finsupp.smul_single]
      rw [hbpow, map_pow, mulAMonoidHom_single]
    rw [hsplit, Module.End.mul_apply, ih]
    rw [mulA_pow_lof_grMk]
    -- assemble degree and value
    refine lof_grMk_congr S J _ _ ?_ _ _ ?_
    · rw [sum_single_add_eq]; ring
    · show a i ^ b * ((∏ k, a k ^ μ' k) * (z : S)) = (∏ k, a k ^ (Finsupp.single i b + μ') k) * z
      rw [prod_pow_single_add]; ring

/-- Action of a single monomial `monomial μ c` of `P = MvPolynomial (Fin t)(S⧸J)`
on a homogeneous lifted leading-form class. -/
lemma monomial_smul_lof_grMk (S : Type*) [CommRing S] (J : Ideal S) (t : ℕ) (a : Fin t → S)
    (ha : J = Ideal.span (Set.range a)) (μ : Fin t →₀ ℕ) (c : S ⧸ J) (m : ℕ)
    (z : (J ^ m : Ideal S)) :
    grModuleRingHom S J t a ha (MvPolynomial.monomial μ c)
        (DirectSum.lof S ℕ (fun n => grPiece S J n) m (grMk S J m z))
      = DirectSum.lof S ℕ (fun n => grPiece S J n) (m + (μ.sum fun _ e => e))
          (c • grMk S J (m + (μ.sum fun _ e => e)) ⟨(∏ i, a i ^ μ i) * z, by
            rw [pow_add, mul_comm (J ^ m)]
            exact Ideal.mul_mem_mul (aMon_mem_pow S J t a ha μ) z.2⟩) := by
  have hmon : (MvPolynomial.monomial μ c : MvPolynomial (Fin t) (S ⧸ J))
      = AddMonoidAlgebra.single μ c := rfl
  rw [hmon, grModuleRingHom, AddMonoidAlgebra.liftNCRingHom_single]
  show (algebraMap (S ⧸ J) (Module.End (S ⧸ J) (grModule S J)) c)
      (mulAMonoidHom S J t a ha (Multiplicative.ofAdd μ)
        (DirectSum.lof S ℕ (fun n => grPiece S J n) m (grMk S J m z))) = _
  rw [mulAMonoidHom_lof_grMk, Module.algebraMap_end_apply]
  -- now `c • lof (m+|μ|) (grMk ...) = lof (m+|μ|) (c • grMk ...)`
  set D := m + (μ.sum fun _ e => e) with hD
  set w : (J ^ D : Ideal S) := ⟨(∏ i, a i ^ μ i) * z, by
    rw [hD, pow_add, mul_comm (J ^ m)]
    exact Ideal.mul_mem_mul (aMon_mem_pow S J t a ha μ) z.property⟩ with hw
  show c • (DirectSum.lof S ℕ (fun n => grPiece S J n) D (grMk S J D w) : grModule S J)
    = (DirectSum.lof S ℕ (fun n => grPiece S J n) D (c • grMk S J D w) : grModule S J)
  have heq1 : (DirectSum.lof S ℕ (fun n => grPiece S J n) D (grMk S J D w) : grModule S J)
      = DirectSum.lof (S ⧸ J) ℕ (fun n => grPiece S J n) D (grMk S J D w) := rfl
  have heq2 : (DirectSum.lof S ℕ (fun n => grPiece S J n) D (c • grMk S J D w) : grModule S J)
      = DirectSum.lof (S ⧸ J) ℕ (fun n => grPiece S J n) D (c • grMk S J D w) := rfl
  rw [heq1, heq2, ← LinearMap.map_smul]

/-- If `s ∈ J^(N-m)` and `w ∈ J^m` then `s * w ∈ J^N` (uniformly, handling both
`m ≤ N` via `J^(N-m)·J^m = J^N`, and `m > N` via `J^m ≤ J^N`). -/
lemma mul_pow_sub_mem (S : Type*) [CommRing S] (J : Ideal S) (N m : ℕ) (s w : S)
    (hs : s ∈ (J ^ (N - m) : Ideal S)) (hw : w ∈ (J ^ m : Ideal S)) :
    s * w ∈ (J ^ N : Ideal S) := by
  rcases le_total m N with hmN | hmN
  · have : s * w ∈ (J ^ (N - m)) * (J ^ m) := Ideal.mul_mem_mul hs hw
    rwa [← pow_add, Nat.sub_add_cancel hmN] at this
  · have hwN : w ∈ (J ^ N : Ideal S) := Ideal.pow_le_pow_right hmN hw
    have : s • w ∈ (J ^ N : Ideal S) := (J ^ N : Ideal S).smul_mem s hwN
    simpa [smul_eq_mul] using this

/-- **Degree-`N` component of a polynomial action on a homogeneous lifted class.**
For any `p : MvPolynomial (Fin t)(S⧸J)`, the degree-`N` homogeneous component of
`p • (lof m (grMk w))` is the leading-form class of `s * w` for some `s ∈ J^(N-m)`.
(When `m > N`, or when `p` contributes nothing in degree `N`, take `s = 0`.) This is
the per-degree read-off, proved by `MvPolynomial` induction: monomials shift degree
by `|μ|` (`monomial_smul_lof_grMk`), `component` selects the degree-matching ones,
and the coefficient lifts to `s := s' * a^μ ∈ J^(N-m)`. -/
lemma component_smul_lof (S : Type*) [CommRing S] (J : Ideal S) (t : ℕ) (a : Fin t → S)
    (ha : J = Ideal.span (Set.range a)) (N m : ℕ) (w : (J ^ m : Ideal S))
    (p : MvPolynomial (Fin t) (S ⧸ J)) :
    ∃ (s : S) (hs : s ∈ (J ^ (N - m) : Ideal S)),
      DirectSum.component S ℕ (fun n => grPiece S J n) N
          (grModuleRingHom S J t a ha p
            (DirectSum.lof S ℕ (fun n => grPiece S J n) m (grMk S J m w)))
        = grMk S J N ⟨s * w, mul_pow_sub_mem S J N m s w hs w.2⟩ := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial μ c =>
    rw [monomial_smul_lof_grMk]
    by_cases hcase : m + (μ.sum fun _ e => e) = N
    · -- degree matches: component is `c • grMk⟨a^μ w⟩`
      subst hcase
      -- lift c
      obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
      have hsmem : c' * (∏ i, a i ^ μ i) ∈ (J ^ ((m + (μ.sum fun _ e => e)) - m) : Ideal S) := by
        rw [Nat.add_sub_cancel_left]
        exact (J ^ (μ.sum fun _ e => e) : Ideal S).mul_mem_left c' (aMon_mem_pow S J t a ha μ)
      refine ⟨c' * ∏ i, a i ^ μ i, hsmem, ?_⟩
      -- the component equals the leading-form of `(c' a^μ) w`
      rw [DirectSum.component.lof_self]
      show (Ideal.Quotient.mk J c') • grMk S J (m + (μ.sum fun _ e => e))
          ⟨(∏ i, a i ^ μ i) * (w : S), _⟩ = _
      rw [grPiece_smul_mk]
      unfold grMk
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      ext
      show c' • ((∏ i, a i ^ μ i) * (w : S)) = (c' * ∏ i, a i ^ μ i) * w
      rw [smul_eq_mul]; ring
    · -- degree mismatch: component is 0, take s = 0
      refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [DirectSum.component.of, dite_eq_right hcase]
      unfold grMk
      rw [eq_comm, Submodule.Quotient.mk_eq_zero]
      simp only [Submodule.mem_comap]
      show (0 : S) * (w : S) ∈ (J ^ (N + 1) : Ideal S)
      rw [zero_mul]; exact Submodule.zero_mem _
  | add p q hp hq =>
    obtain ⟨sp, hsp, hep⟩ := hp
    obtain ⟨sq, hsq, heq⟩ := hq
    refine ⟨sp + sq, Submodule.add_mem _ hsp hsq, ?_⟩
    rw [map_add, LinearMap.add_apply, map_add, hep, heq]
    unfold grMk
    rw [← Submodule.Quotient.mk_add]
    congr 1
    ext
    show sp * (w : S) + sq * w = (sp + sq) * w
    rw [add_mul]

/-- If the degree-`N` leading form of `x` is the sum of those of the `y k`, then
`x - ∑ k, y k ∈ J^(N+1)`. -/
lemma sub_sum_mem_of_grMk_eq_sum (S : Type*) [CommRing S] (J : Ideal S) (N : ℕ) {ι : Type*}
    (s : Finset ι) (x : (J ^ N : Ideal S)) (y : ι → (J ^ N : Ideal S))
    (h : grMk S J N x = ∑ k ∈ s, grMk S J N (y k)) :
    (x : S) - ∑ k ∈ s, (y k : S) ∈ J ^ (N + 1) := by
  have h' : grMk S J N x = grMk S J N (∑ k ∈ s, y k) := h.trans (map_sum (Submodule.mkQ _) y s).symm
  unfold grMk at h'
  rw [Submodule.Quotient.eq, Submodule.mem_comap, map_sub, map_sum] at h'
  simpa using h'

end
