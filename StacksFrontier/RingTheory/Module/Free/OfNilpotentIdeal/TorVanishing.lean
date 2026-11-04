module

public import StacksFrontier.RingTheory.Module.Free.OfNilpotentIdeal.MultiplicationMaps

/-!
# Freeness modulo a nilpotent ideal: vanishing of `Tor₁^R(R/I, M)`

Presentation independence of `Tor₁` via the snake lemma, and the vanishing of
`Tor₁^R(N, M)` for an `I`-torsion module `N`, given a basis of `M/IM` over `R/I` and the
injectivity of `I ⊗_R M → M` (`tor_one_quot_ker_eq_bot`).
-/

@[expose] public section

namespace Stacks.FreeOfNilpotentIdeal

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-! ### The right flank: `Tor₁^S(N, M̄) = 0`

With the `S = R ⧸ I`-module structure on the `I`-torsion module `N`, supplied by
`moduleQuotOfSmulEqBot` together with `isScalarTower_of_smul_eq_bot`, take the canonical
`S`-free resolution `0 → L → Q → N → 0` with `Q = N →₀ S`,
`q = Finsupp.linearCombination S id` and `L = ker q`. The `S`-linear inclusion
`λ = L.subtype` is injective, so by flat base change, using `S`-flatness of
`M̄ = (R⧸I)⊗[R]M`, the `R`-linear map `rTensor M (λ.restrictScalars R)` is injective, that
is, `Tor₁^S(N, M̄) = 0`.

This is not stated as a standalone declaration: unifying the `S`-module structure on `N`
coming from the reducible `moduleQuotOfSmulEqBot` against the `restrictScalars` in the goal
is too costly under `backward.isDefEq.respectTransparency false`. The two infrastructure
pieces it rests on are `moduleQuotOfSmulEqBot` and `isScalarTower_of_smul_eq_bot` above.
-/

/-- Pullback of a presentation along a lift: for `q ∘ₗ s = p` with `ι` injective and
`ι, q` exact, `ker p` maps to `A` by some `σ` with `ι ∘ₗ σ = s ∘ₗ subtype`, and
`0 → ker p → P × A → B → 0` is exact, with `(y, a) ↦ s y - ι a`. -/
private theorem exists_pullback_exact {P A B Nn : Type*}
    [AddCommGroup P] [Module R P] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup Nn] [Module R Nn]
    (p : P →ₗ[R] Nn) (hp : Function.Surjective p)
    (ι : A →ₗ[R] B) (q : B →ₗ[R] Nn) (hιq : Function.Exact ι q) (hι : Function.Injective ι)
    (s : P →ₗ[R] B) (hs : q ∘ₗ s = p) :
    ∃ σ : LinearMap.ker p →ₗ[R] A, ι ∘ₗ σ = s ∘ₗ (LinearMap.ker p).subtype ∧
      Function.Exact (LinearMap.prod (LinearMap.ker p).subtype σ)
        (s ∘ₗ LinearMap.fst R P A - ι ∘ₗ LinearMap.snd R P A) ∧
      Function.Surjective (s ∘ₗ LinearMap.fst R P A - ι ∘ₗ LinearMap.snd R P A) := by
  have hsp : ∀ y, q (s y) = p y := LinearMap.congr_fun hs
  have hcod : ∀ k : LinearMap.ker p, s k ∈ LinearMap.range ι := fun k =>
    (hιq _).mp (by rw [hsp]; exact LinearMap.mem_ker.mp k.2)
  set σ : LinearMap.ker p →ₗ[R] A := (LinearEquiv.ofInjective ι hι).symm.toLinearMap ∘ₗ
    ((s ∘ₗ (LinearMap.ker p).subtype).codRestrict (LinearMap.range ι) hcod) with hσdef
  have hσ : ι ∘ₗ σ = s ∘ₗ (LinearMap.ker p).subtype := by
    ext k
    exact congrArg Subtype.val ((LinearEquiv.ofInjective ι hι).apply_symm_apply ⟨s k, hcod k⟩)
  have hσp : ∀ w, ι (σ w) = s w := LinearMap.congr_fun hσ
  have hsurj : Function.Surjective (s ∘ₗ LinearMap.fst R P A - ι ∘ₗ LinearMap.snd R P A) := by
    intro c
    obtain ⟨y, hy⟩ := hp (q c)
    obtain ⟨a, ha⟩ := (hιq (c - s y)).mp (by rw [map_sub, hsp, hy, sub_self])
    exact ⟨(y, -a), by simp [ha]⟩
  refine ⟨σ, hσ, ?_, hsurj⟩
  rw [LinearMap.exact_iff]
  apply le_antisymm
  · rintro ⟨y, a⟩ hx
    simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.fst_apply, LinearMap.snd_apply, sub_eq_zero] at hx
    have hpy : y ∈ LinearMap.ker p := by
      rw [LinearMap.mem_ker, ← hsp, hx]
      exact hιq.apply_apply_eq_zero a
    exact ⟨⟨y, hpy⟩, Prod.ext rfl (hι ((hσp _).trans hx))⟩
  · rintro _ ⟨w, rfl⟩
    simp [hσp]

/-- **Abstract dimension-shift / Tor presentation-independence (the homological core of (B)).**
Given a commuting ladder of `R`-modules with exact rows sharing the same quotient `Nn`
```
0 → K → P → Nn → 0     (κ, p; p surjective)
0 → A → B → Nn → 0     (ι, q; q surjective)
```
and vertical maps `s : P → B`, `t : K → A` making the squares commute (`q ∘ s = p`, `ι ∘ t = s ∘
κ`),
with `ι` injective: if `rTensor M κ` is injective then `rTensor M ι` is injective.

This is exactly the statement that `Tor₁^R(Nn, M)` is independent of the presentation of `Nn`
(here computed against an `R`-free presentation `P` on the top, vs. the inclusion `ι` on the
bottom).
The proof is the snake lemma applied to the `M`-tensored ladder: both tensored rows are right-exact
(`rTensor_exact`), the comparison `(rt, rs, id)` covers `id_{Nn ⊗ M}`, and the snake exactness at
`coker rt` and at `ker rs` (with `ker id = coker id = 0`) together with injectivity of `rκ` force
`ker rι = ⊥`. -/
theorem rTensor_inj_of_comparison
    {K P A B Nn : Type*}
    [AddCommGroup K] [Module R K] [AddCommGroup P] [Module R P]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup Nn] [Module R Nn]
    (κ : K →ₗ[R] P) (p : P →ₗ[R] Nn)
    (ι : A →ₗ[R] B) (q : B →ₗ[R] Nn)
    (hκp : Function.Exact κ p) (hp : Function.Surjective p)
    (hιq : Function.Exact ι q)
    (hι : Function.Injective ι)
    (s : P →ₗ[R] B)
    (hs : q ∘ₗ s = p)
    (hκinj : Function.Injective (LinearMap.rTensor M κ)) :
    Function.Injective (LinearMap.rTensor M ι) := by
  -- Clean proof: reduce to a MORPHISM OF SHORT
  -- EXACT SEQUENCES and use naturality of the `· ⊗ M` connecting map.
  -- Replace the right-exact top row `K → P → Nn` by the genuine SES `0 → K' → P → Nn → 0`
  -- with `K' := ker p`, `j := K'.subtype`.  `κ` corestricts to a surjection `e : K ↠ K'` with
  -- `κ = j ∘ₗ e`; since `rκ = rj ∘ₗ rE` with `rE` surjective and `rκ` injective, `rj` is
  -- injective.
  -- The lift `s` restricts to `σ : K' → A` (using `q ∘ₗ s = p` and `ker q = range ι`), giving a
  -- morphism of short exact sequences `(σ, s, id)`.  Naturality of the connecting map then forces
  -- `δ_bot = (σ⊗id) ∘ δ_top` and `rj` injective ⟺ `δ_top = 0`, hence `δ_bot = 0` and
  -- `ker rι = im δ_bot = 0`.
  classical
  set K' := LinearMap.ker p with hK'
  set j : K' →ₗ[R] P := K'.subtype with hj
  have hjp : Function.Exact j p := LinearMap.exact_subtype_ker_map p
  -- `e : K ↠ K'` corestriction of `κ`; `j ∘ₗ e = κ`, `e` surjective.
  have hκrange : ∀ y : K, κ y ∈ K' := hκp.apply_apply_eq_zero
  set e : K →ₗ[R] K' := κ.codRestrict K' hκrange with he
  have hje : j ∘ₗ e = κ := by ext y; rfl
  have he_surj : Function.Surjective e := by
    intro w
    have hw : (w : P) ∈ LinearMap.range κ := by
      rw [← hκp.linearMap_ker_eq]
      exact w.property
    obtain ⟨y, hy⟩ := hw
    exact ⟨y, Subtype.ext hy⟩
  -- STEP 1: `rTensor M j` is injective.
  set rκ := LinearMap.rTensor M κ with hrκ
  set rj := LinearMap.rTensor M j with hrj
  set rE := LinearMap.rTensor M e with hrE
  have hrE_surj : Function.Surjective rE := LinearMap.rTensor_surjective M he_surj
  have hcomp : rκ = rj ∘ₗ rE := by rw [hrκ, hrj, hrE, ← LinearMap.rTensor_comp, hje]
  have hrj_inj : Function.Injective rj := by
    intro a b hab
    obtain ⟨a', rfl⟩ := hrE_surj a
    obtain ⟨b', rfl⟩ := hrE_surj b
    have heq : rκ a' = rκ b' := by rw [hcomp]; exact hab
    rw [hκinj heq]
  -- STEP 2: the morphism of short exact sequences `(σ, s, id)` makes the LEFT square a PULLBACK,
  -- yielding the short exact sequence  `0 → K' --⟨j,σ⟩--> P × A --[s,-ι]--> B → 0`.
  obtain ⟨σ, hσ, hexact, hsurj⟩ := exists_pullback_exact p hp ι q hιq hι s hs
  set Φ : K' →ₗ[R] (P × A) := LinearMap.prod j σ with hΦ
  set Ψ : (P × A) →ₗ[R] B := s ∘ₗ LinearMap.fst R P A - ι ∘ₗ LinearMap.snd R P A with hΨ
  -- STEP 3: tensoring with
  -- `M` is right-exact, so `ker (rTensor M Ψ) = range (rTensor M Φ)`.  For `z` with `rι z = 0`,
  -- `Z := (inr ⊗ id) z` lies in `ker (rTensor M Ψ)` (since `Ψ ∘ₗ inr = -ι`), hence `Z = (Φ ⊗ id)
  -- w`;
  -- applying `fst ⊗ id` gives `rj w = 0`, so `w = 0` (STEP 1), and applying `snd ⊗ id` gives `z =
  -- 0`.
  have hTexact : Function.Exact (LinearMap.rTensor M Φ) (LinearMap.rTensor M Ψ) :=
    rTensor_exact M hexact hsurj
  rw [injective_iff_map_eq_zero]
  intro z hz
  set Z : TensorProduct R (P × A) M := LinearMap.rTensor M (LinearMap.inr R P A) z with hZ
  have hΨinr : Ψ ∘ₗ LinearMap.inr R P A = -ι := by
    rw [hΨ]
    ext a
    simp []
  have hZker : LinearMap.rTensor M Ψ Z = 0 := by
    rw [hZ, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hΨinr,
      LinearMap.rTensor_neg, LinearMap.neg_apply, hz, neg_zero]
  obtain ⟨w, hw⟩ := (hTexact Z).mp hZker
  have hfstΦ : LinearMap.fst R P A ∘ₗ Φ = j := by
    rw [hΦ]
    ext k
    simp
  have hjw : LinearMap.rTensor M j w = 0 := by
    have heqw : LinearMap.rTensor M (LinearMap.fst R P A) (LinearMap.rTensor M Φ w)
        = LinearMap.rTensor M (LinearMap.fst R P A) Z := by rw [hw]
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hfstΦ] at heqw
    rw [heqw, hZ, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp,
      LinearMap.fst_comp_inr, LinearMap.rTensor_zero, LinearMap.zero_apply]
  have hw0 : w = 0 := hrj_inj (by rw [hjw, map_zero])
  have hsndΦ : LinearMap.snd R P A ∘ₗ Φ = σ := by
    rw [hΦ]
    ext k
    simp
  have hzeq : z = LinearMap.rTensor M σ w := by
    have heqw : LinearMap.rTensor M (LinearMap.snd R P A) (LinearMap.rTensor M Φ w)
        = LinearMap.rTensor M (LinearMap.snd R P A) Z := by rw [hw]
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hsndΦ] at heqw
    rw [hZ, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, LinearMap.snd_comp_inr,
      LinearMap.rTensor_id, LinearMap.id_apply] at heqw
    exact heqw.symm
  rw [hzeq, hw0, map_zero]

/-- **`rTensor M (I.subtype)` is injective**, equivalently `Tor₁^R(R/I, M) = 0`. This is the
hypothesis `hTor` (injectivity of `torMul I`) re-expressed: `torMul I = lid ∘ rTensor M I.subtype`.
-/
theorem rTensor_subtype_ideal_injective (I : Ideal R)
    (hTor : Function.Injective (torMul (M := M) I)) :
    Function.Injective (LinearMap.rTensor M (Submodule.subtype I)) := by
  have hfac : torMul (M := M) I
      = (TensorProduct.lid R M).toLinearMap ∘ₗ LinearMap.rTensor M (Submodule.subtype I) := by
    apply TensorProduct.ext'
    intro a m
    simp [torMul_tmul, LinearMap.rTensor_tmul]
  intro x y hxy
  apply hTor
  rw [hfac]
  simp only [LinearMap.comp_apply]
  rw [hxy]

/-- **`rTensor M` of a coordinatewise (`Finsupp.mapRange`) map is injective** when the map
itself is `rTensor M`-injective. Used to lift `Tor₁^R(R/I,M) = 0` to `Tor₁^R(Q, M) = 0` for
`Q = N →₀ (R/I)`, the `R`-free presentation `0 → (N →₀ I) → (N →₀ R) → Q → 0`. -/
theorem rTensor_mapRange_injective {ι : Type*} {A B : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    (f : A →ₗ[R] B) (hf : Function.Injective (LinearMap.rTensor M f)) :
    Function.Injective (LinearMap.rTensor M (Finsupp.mapRange.linearMap (α := ι) f)) := by
  classical
  set eA := TensorProduct.finsuppLeft R R A M ι with heA
  set eB := TensorProduct.finsuppLeft R R B M ι with heB
  have hnat : (eB.toLinearMap ∘ₗ LinearMap.rTensor M (Finsupp.mapRange.linearMap (α := ι) f))
      = (Finsupp.mapRange.linearMap (LinearMap.rTensor M f)) ∘ₗ eA.toLinearMap := by
    apply TensorProduct.ext'
    intro p m
    apply Finsupp.ext
    intro i
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearMap.rTensor_tmul, heB, heA, TensorProduct.finsuppLeft_apply_tmul,
      TensorProduct.finsuppLeft_apply_tmul]
    simp only [Finsupp.mapRange.linearMap_apply]
    rw [Finsupp.mapRange_apply, Finsupp.sum_apply, Finsupp.sum_apply]
    simp only [Finsupp.single_apply]
    rw [Finsupp.sum_mapRange_index (by simp)]
    simp only [Finsupp.sum, map_sum]
    congr 1
    ext j
    by_cases h : j = i <;> simp [h, LinearMap.rTensor_tmul]
  have hmr : Function.Injective (Finsupp.mapRange.linearMap (α := ι) (LinearMap.rTensor M f)) := by
    intro u v huv
    refine Finsupp.ext fun i => ?_
    have := congrArg (fun g => g i) huv
    simp only [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply] at this
    exact hf this
  intro a b hab
  apply eA.injective
  apply hmr
  exact (LinearMap.congr_fun hnat a).symm.trans
    ((congrArg eB hab).trans (LinearMap.congr_fun hnat b))

/-- **Exactness of the `Finsupp.mapRange`-tensored `(★_R)` row**: tensoring the `R`-module SES
`0 → I → R → R/I → 0` levelwise by `ι →₀ (-)` is exact at the middle. -/
theorem exact_mapRange_subtype_mkQ {ι : Type*} (I : Ideal R) :
    Function.Exact (Finsupp.mapRange.linearMap (α := ι) (Submodule.subtype I))
      (Finsupp.mapRange.linearMap (α := ι) (Submodule.mkQ I)) := by
  classical
  rw [LinearMap.exact_iff]
  ext f
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hf
    have hmem : ∀ n, f n ∈ I := by
      intro n
      have : (Finsupp.mapRange.linearMap (Submodule.mkQ I) f) n = 0 := by rw [hf]; simp
      rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply] at this
      rwa [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    refine ⟨Finsupp.mk f.support (fun n => ⟨f n, hmem n⟩) (by
      intro n
      simp only [Finsupp.mem_support_iff, ne_eq, Submodule.mk_eq_zero]), ?_⟩
    refine Finsupp.ext fun n => ?_
    rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
    rfl
  · rintro ⟨g, rfl⟩
    refine Finsupp.ext fun n => ?_
    rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
    simp only [Finsupp.coe_zero, Pi.zero_apply]
    rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
    show Submodule.mkQ I (g n : R) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact (g n).property

/-- **Base-change injectivity for the inclusion of `ker qS`** where `qS : Q →ₗ[R⧸I] N` is any
`R⧸I`-linear map from an `R⧸I`-module `Q` (also an `R`-module, scalar tower) under flatness of
`M̄ = (R⧸I) ⊗ M`. This is the "LEFT flank" of the change-of-rings comparison, packaged with an
ABSTRACT `Q` so that the costly `whnf` unification of `rTensor_injective_of_flat_baseChange`'s
`restrictScalars` conclusion never has to unfold a concrete `Finsupp.linearCombination`. -/
theorem rTensor_ker_baseChange_injective
    (I : Ideal R) [Module.Flat (R ⧸ I) (TensorProduct R (R ⧸ I) M)]
    {N : Type*} [AddCommGroup N] [Module R N] [Module (R ⧸ I) N] [IsScalarTower R (R ⧸ I) N]
    {Q : Type*} [AddCommGroup Q] [Module (R ⧸ I) Q] [Module R Q] [IsScalarTower R (R ⧸ I) Q]
    (qS : Q →ₗ[R ⧸ I] N) :
    Function.Injective (LinearMap.rTensor M
      (((LinearMap.ker qS).subtype).restrictScalars R)) := by
  set L := LinearMap.ker qS with hL
  have hlamSinj : Function.Injective (L.subtype) := Subtype.coe_injective
  exact rTensor_injective_of_flat_baseChange (M := M) (I := I) (K := ↥L) (F := Q)
    (φ := L.subtype) hlamSinj

-- this proof's elaboration needs more than the default heartbeat budget
/-- **Mapping-cone splice for change-of-rings `Tor₁` vanishing (abstract form).**
Given an `R`-module `N` with a projective presentation `p : P → N`, an `R⧸I`-derived presentation
`0 → L →[lamR] Q →[qR] N → 0` whose inclusion `lamR` is `rTensor M`-injective (LEFT flank), and an
`R`-free/projective presentation `Ktop →[κtop] Ptop →[ctop] Q → 0` of `Q` with `κtop`
`rTensor M`-injective (RIGHT flank), the kernel inclusion `(ker p).subtype` is `rTensor
M`-injective.
The argument builds the mapping-cone SES `0 → ker p → P × L → Q → 0` of the projective lift
`P → Q` and feeds it, together with the free presentation of `Q`, to `rTensor_inj_of_comparison`.

`Q`, `L`, `Ktop`, `Ptop` are kept ABSTRACT (not `set` to `Finsupp` defs) so the costly defeq /
`whnf` unification inside `rTensor_inj_of_comparison` never unfolds a concrete
`Finsupp.linearCombination`. -/
theorem tor_one_quot_ker_eq_bot_splice
    {N : Type*} [AddCommGroup N] [Module R N]
    {P : Type*} [AddCommGroup P] [Module R P] [Module.Projective R P]
    (p : P →ₗ[R] N) (hp : Function.Surjective p)
    {Q : Type*} [AddCommGroup Q] [Module R Q]
    (qR : Q →ₗ[R] N) (hqR : Function.Surjective qR)
    {L : Type*} [AddCommGroup L] [Module R L]
    (lamR : L →ₗ[R] Q) (hlamR_exact : Function.Exact lamR qR)
    (hlamR_inj : Function.Injective lamR)
    (hlamR_rinj : Function.Injective (LinearMap.rTensor M lamR))
    {Ktop Ptop : Type*} [AddCommGroup Ktop] [Module R Ktop]
    [AddCommGroup Ptop] [Module R Ptop] [Module.Projective R Ptop]
    (κtop : Ktop →ₗ[R] Ptop) (ctop : Ptop →ₗ[R] Q)
    (hκtop_exact : Function.Exact κtop ctop) (hctop_surj : Function.Surjective ctop)
    (hκtop_rinj : Function.Injective (LinearMap.rTensor M κtop)) :
    Function.Injective (LinearMap.rTensor M (LinearMap.ker p).subtype) := by
  classical
  set K := LinearMap.ker p with hK
  set κ : K →ₗ[R] P := K.subtype with hκ
  obtain ⟨sPQ, hsPQ⟩ := Module.projective_lifting_property qR p hqR
  obtain ⟨tKL, htKLeq, hexact, hψ_surj⟩ :=
    exists_pullback_exact p hp lamR qR hlamR_exact hlamR_inj sPQ hsPQ
  set φ : K →ₗ[R] (P × L) := LinearMap.prod κ tKL with hφ
  set ψ : (P × L) →ₗ[R] Q := sPQ ∘ₗ LinearMap.fst R P L - lamR ∘ₗ LinearMap.snd R P L with hψ
  have hφinj : Function.Injective φ := by
    intro a c hac
    have : κ a = κ c := by have := congrArg (LinearMap.fst R P L) hac; simpa [hφ] using this
    exact Subtype.val_injective this
  obtain ⟨sLift, hsLift⟩ := Module.projective_lifting_property ψ ctop hψ_surj
  have hφ_rinj : Function.Injective (LinearMap.rTensor M φ) :=
    rTensor_inj_of_comparison (M := M) κtop ctop φ ψ hκtop_exact hctop_surj hexact
      hφinj sLift hsLift hκtop_rinj
  rw [injective_iff_map_eq_zero]
  intro z hz
  have htz : LinearMap.rTensor M tKL z = 0 := by
    apply hlamR_rinj
    rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, htKLeq, LinearMap.rTensor_comp,
      LinearMap.comp_apply, hz, map_zero, map_zero]
  have hφz : LinearMap.rTensor M φ z = 0 := by
    set w := LinearMap.rTensor M φ z with hw
    have hfst : LinearMap.rTensor M (LinearMap.fst R P L) w = 0 := by
      rw [hw, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
      have : LinearMap.fst R P L ∘ₗ φ = κ := by rw [hφ]; ext k; simp
      rw [this, hz]
    have hsnd : LinearMap.rTensor M (LinearMap.snd R P L) w = 0 := by
      rw [hw, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp]
      have : LinearMap.snd R P L ∘ₗ φ = tKL := by rw [hφ]; ext k; simp
      rw [this, htz]
    have hid : (LinearMap.inl R P L ∘ₗ LinearMap.fst R P L
        + LinearMap.inr R P L ∘ₗ LinearMap.snd R P L : (P × L) →ₗ[R] (P × L)) = LinearMap.id := by
      ext z <;> simp
    have hwe : w = LinearMap.rTensor M (LinearMap.inl R P L)
          (LinearMap.rTensor M (LinearMap.fst R P L) w)
        + LinearMap.rTensor M (LinearMap.inr R P L)
          (LinearMap.rTensor M (LinearMap.snd R P L) w) := by
      conv_lhs => rw [← LinearMap.id_apply (R := R) w, ← LinearMap.rTensor_id, ← hid]
      rw [LinearMap.rTensor_add, LinearMap.add_apply, LinearMap.rTensor_comp,
          LinearMap.rTensor_comp,
        LinearMap.comp_apply, LinearMap.comp_apply]
    rw [hwe, hfst, hsnd, map_zero, map_zero, add_zero]
  exact hφ_rinj (by rw [hφz, map_zero])

-- this proof's elaboration needs more than the default heartbeat budget
/-- **(C-ii) The change-of-rings snake: `ker (rTensor M κ) = ⊥`** for the `R`-free presentation
`0 → ker p → P → N → 0` of an `R/I`-module `N` (`I • ⊤ = ⊥` on `N`).

This is the genuine homological core (the local criterion of flatness, Stacks 00MK), realized by a
hand-built snake on the columns given by the column map `τ = torMul I : I ⊗ M → M` over the
`M`-tensored presentation. Informal proof (read the
"Summary of the formalization obligations", lines ~321–333; the clean obligations are):

- the rows `K⊗(I⊗M) → P⊗(I⊗M) → N⊗(I⊗M) → 0` and `K⊗M → P⊗M → N⊗M → 0` are exact
  (`rTensor_exact` + `rTensor_surjective`), where `K := ker p`, `κ := K.subtype`;
- the `P`-column `0 → P⊗(I⊗M) → P⊗M → P⊗(M/IM) → 0` is SHORT exact: left-injective by
  `tor_one_quot_pColumn_injective`, exact in the middle and right by right-exactness of `P⊗(-)` on
  `0 → I⊗M →[τ] M → M/IM → 0`;
- the `N`-column map `c_N : N⊗M → N⊗(M/IM)` is an ISO because `I•N = ⊥`
  (`quotTensorEquivQuotSMul` / `cancelBaseChange`; the kernel `im(lTensor N τ)` lands in
  `I•(N⊗M)=0`);
- the snake exact fragment `N⊗(I⊗M) →∂ ker ρ → Tor₁^S(N,M/IM)` has its right flank `0` by FLATNESS
  of `M/IM` over `S = R/I` (`flat_quotTensor_of_basis I b`, via
  `rTensor_injective_of_flat_baseChange`)
  and its left flank `im ∂ = N ⊗_S ker(torMul I) = N ⊗_S 0 = 0` by `hTor`. Hence `ker ρ = ⊥`. -/
theorem tor_one_quot_ker_eq_bot
    {A : Type*} (I : Ideal R)
    (b : Module.Basis A (R ⧸ I) (M ⧸ smul (M := M) I))
    (hTor : Function.Injective (torMul (M := M) I))
    {N : Type*} [AddCommGroup N] [Module R N]
    (hN : I • (⊤ : Submodule R N) = ⊥)
    {P : Type*} [AddCommGroup P] [Module R P] [Module.Free R P]
    (p : P →ₗ[R] N) (hp : Function.Surjective p) :
    Function.Injective (LinearMap.rTensor M (LinearMap.ker p).subtype) := by
  -- PROOF (local criterion of flatness 00MK), via the change-of-rings principle realized WITHOUT a
  -- snake, by the presentation-independence lemma `rTensor_inj_of_comparison`:
  --  • `N` is an `S = R/I`-module (`I • ⊤ = ⊥`); take its `S`-free presentation
  --    `0 → L → Q → N → 0`, `Q := N →₀ S`. `M̄ := M/IM` is `S`-flat (basis `b`), so
  --    `rTensor M (λ_R)` is injective (`rTensor_injective_of_flat_baseChange`) — the LEFT flank.
  --  • `Q ≅ ⨁_N S` has `Tor₁^R(Q,M) = 0` (each summand is `S` with `Tor₁^R(S,M)=ker(torMul I)=0`
  --    by `hTor`): the `R`-free presentation `0 → (N→₀I) → (N→₀R) → Q → 0` has
  --    `rTensor M (mapRange I.subtype)` injective (`rTensor_mapRange_injective` +
  --    `rTensor_subtype_ideal_injective`) — the RIGHT flank.
  --  • Splice: build the mapping-cone SES `0 → K → P × L → Q → 0` of the comparison `P → Q`
  --    (lift of `id_N`, `P` projective). Its left map `φ = ⟨κ, tKL⟩` has `rTensor M φ`
  --    injective by
  --    `rTensor_inj_of_comparison` against the `R`-free presentation of `Q` (RIGHT flank). For
  --    `z ∈ ker(rTensor M κ)`, the LEFT flank forces `rTensor M tKL z = 0`, hence `rTensor M φ z =
  -- 0`,
  --    hence `z = 0`.
  classical
  let : Module (R ⧸ I) N := moduleQuotOfSmulEqBot I hN
  have : IsScalarTower R (R ⧸ I) N := isScalarTower_of_smul_eq_bot I hN
  have : Module.Flat (R ⧸ I) (TensorProduct R (R ⧸ I) M) := flat_quotTensor_of_basis I b
  have : Module.Projective R P := Module.Projective.of_free
  -- `S = R⧸I`-free presentation of `N`:  `Q = N →₀ S`,  `qS : Q → N`,  `L = ker qS`,  `lamR`.
  set Q := N →₀ (R ⧸ I) with hQ
  set qS : Q →ₗ[R ⧸ I] N := Finsupp.linearCombination (R ⧸ I) id with hqS
  have hqS_surj : Function.Surjective qS := fun n =>
    ⟨Finsupp.single n 1, by rw [hqS, Finsupp.linearCombination_single]; simp⟩
  set qR : Q →ₗ[R] N := qS.restrictScalars R with hqR
  have hqR_surj : Function.Surjective qR := hqS_surj
  set L := LinearMap.ker qS with hL
  set lamR : ↥L →ₗ[R] Q := (L.subtype).restrictScalars R with hlamR
  have hlamR_inj : Function.Injective lamR := by
    rw [hlamR, LinearMap.coe_restrictScalars]
    exact Subtype.coe_injective
  -- LEFT flank: `rTensor M lamR` injective, by `M̄` being `S`-flat (base change).
  have hlamR_rinj : Function.Injective (LinearMap.rTensor M lamR) := by
    rw [hlamR]
    exact rTensor_ker_baseChange_injective (M := M) I qS
  -- `range lamR = ker qR` (the `S`- and `R`-kernels coincide as subsets), so the row is exact.
  have hlamR_exact : Function.Exact lamR qR := by
    have h := LinearMap.exact_subtype_ker_map qS
    rw [hlamR, hqR]
    intro q
    simpa only [LinearMap.coe_restrictScalars] using h q
  -- RIGHT flank: the `R`-free presentation `0 → (N →₀ I) → (N →₀ R) → Q → 0` of `Q`, with
  -- `rTensor M (mapRange I.subtype)` injective (`Tor₁^R(Q,M) = 0`, from `hTor`).
  set κtop : (N →₀ I) →ₗ[R] (N →₀ R) := Finsupp.mapRange.linearMap (Submodule.subtype I) with hκtop
  set ctop : (N →₀ R) →ₗ[R] Q := Finsupp.mapRange.linearMap (Submodule.mkQ I) with hctop
  have : Module.Projective R (N →₀ R) := Module.Projective.of_free
  have hκtop_exact : Function.Exact κtop ctop := exact_mapRange_subtype_mkQ I
  have hctop_surj : Function.Surjective ctop :=
    Finsupp.mapRange_surjective _ (map_zero _) (Submodule.mkQ_surjective I)
  have hκtop_rinj : Function.Injective (LinearMap.rTensor M κtop) :=
    rTensor_mapRange_injective _ (rTensor_subtype_ideal_injective I hTor)
  -- Splice the two presentations (mapping-cone comparison); abstract `Q`/`L` keep `whnf` cheap.
  apply tor_one_quot_ker_eq_bot_splice (M := M) (Q := Q) (L := ↥L) (P := P) (N := N)
    p hp qR hqR_surj lamR hlamR_exact hlamR_inj hlamR_rinj κtop ctop hκtop_exact hctop_surj
    hκtop_rinj

/-- `Tor₁^R(R/I, M)` vanishes, in the form that `I ⊗_R M → M` is injective, for the module
`M` presented by the basis `b` of `M/IM` over `R/I`. -/
alias tor_one_quot_eq_zero := Stacks.FreeOfNilpotentIdeal.tor_one_quot_ker_eq_bot

end Stacks.FreeOfNilpotentIdeal
