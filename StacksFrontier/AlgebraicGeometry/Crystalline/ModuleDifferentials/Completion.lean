module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRham
public import StacksFrontier.RingTheory.AdicCompletion.QuotPow
public import StacksFrontier.RingTheory.DividedPowers.Extend
public import StacksFrontier.RingTheory.DividedPowers.Ring
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Functoriality

/-!
# Divided power differentials and `p`-adic completion

Let `A → B` be a ring map, let an ideal `J` of `B` carry divided powers `δ`, and let `p` be a
prime which is nilpotent modulo `J`.  Then `pᵉ B` lies in `J` and is stable under its divided
powers for all large `e`, so the quotients `B / pᵉ B` carry divided powers and their modules of
divided power differentials form an inverse system.

The limit of that system is canonically the `p`-adic completion of `Ω_{B/A, δ}`, and also the
`p`-adic completion of the divided power differentials of the `p`-adic completion of `B`.  Both
identifications are produced here, in a single structure recording the two equivalences together
with their projections to every level.

## Main definitions

* `Crystalline.QuotientDifferentialsSystem` — the inverse system of divided power differentials
  of the sufficiently deep quotients, reindexed so that its index set is all of `ℕ`.
* `Crystalline.quotientSystemOfLevels` — such a system, from a level beyond which the quotient
  divided powers exist.
* `Crystalline.DifferentialsCompletionComparison` — the two canonical equivalences from adic
  completions to the limit of that system, with their level formulas.
* `Crystalline.quotientDifferentials` — `Ω_{B_e/A, δ̄}`, the divided power differentials of
  `B_e = B / pᵉ B`.

## Main results

* `Crystalline.dividedPowerDifferentialsCompletionComparison` — the comparison exists.
* `Crystalline.exists_dividedPowerDifferentialsCompletionEquiv` — the displayed equality of the
  source, with no reference to the comparison structure: the inverse system of the
  `Ω_{B_e/A, δ̄}`, its levelwise identification with the towers of quotients of the two adic
  completions, and the resulting isomorphism of those two completions.

## Implementation notes

The sufficiently deep part of the system is reindexed by `e ↦ cutoff + e`, so that the system is
a functor out of `ℕᵒᵖ` and its limit is the ordinary categorical limit in additive commutative
groups.  The two other limits of the source are Mathlib's `AdicCompletion`, and the transition
maps of their systems are `AdicCompletion.transitionMap`.

An inverse system is carried as a structure rather than constructed, because the transition maps
are only pinned down by their effect on universal divided power differentials and that is all any
consumer uses; `Crystalline.quotientSystemOfLevels` produces one.  The equivalences are likewise
specified by their projections at every level together with formulas on universal differentials.

## References

* [Stacks Project, Lemma 60.20.1, Tag 07KK](https://stacks.math.columbia.edu/tag/07KK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace Crystalline

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable (J : Ideal B) (delta : DividedPowers J) (p : ℕ)

/-- Evaluating an element of an adic completion at a level and then pushing down agrees with
evaluating it at the lower level. -/
public theorem factor_eval_completion {R : Type*} [CommRing R] (I : Ideal R)
    {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right h) (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  have H := x.property h
  have hm : I ^ m • (⊤ : Ideal R) ≤ I ^ m := by simp
  have hn : I ^ n • (⊤ : Ideal R) ≤ I ^ n := by simp
  rw [← AdicCompletion.factor_eval_eq_evalₐ I x hn,
    ← AdicCompletion.factor_eval_eq_evalₐ I x hm]
  change Ideal.Quotient.factor _ (Submodule.factor hn (x.val n)) = Submodule.factor hm (x.val m)
  rw [← H]
  generalize x.val n = z
  induction z using Submodule.Quotient.induction_on with | _ z => rfl

/-- The `n`-th power of the `p`-adic ideal of an adic completion is the kernel of evaluation at
level `n`. -/
public theorem pAdicIdeal_eq_ker_eval (n : ℕ) :
    DividedPowers.pAdicIdeal (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p ^ n =
      RingHom.ker (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := B) p) n).toRingHom := by
  let I := DividedPowers.pAdicIdeal (A := B) p
  let C := AdicCompletion I B
  have hm : I.map (algebraMap B C) = DividedPowers.pAdicIdeal (A := C) p := by
    simp [I, DividedPowers.pAdicIdeal, Ideal.map_span]
  have he := AdicCompletion.pow_smul_top_eq_ker_eval (M := B) (n := n)
    (Submodule.fg_span_singleton (p : B))
  have hr : (DividedPowers.pAdicIdeal (A := C) p ^ n).restrictScalars B =
      I ^ n • (⊤ : Submodule B C) := by
    rw [← hm, ← Ideal.map_pow]
    simp
  ext x
  change x ∈ (DividedPowers.pAdicIdeal (A := C) p ^ n).restrictScalars B ↔ _
  rw [hr, he]
  change AdicCompletion.eval I B n x = 0 ↔ AdicCompletion.evalₐ I n x = 0
  change AdicCompletion.eval I B n x = 0 ↔
    (Ideal.quotientEquivAlgOfEq B (show I ^ n • (⊤ : Ideal B) = I ^ n by simp))
      (AdicCompletion.eval I B n x) = 0
  let e := Ideal.quotientEquivAlgOfEq B
    (show I ^ n • (⊤ : Ideal B) = I ^ n by simp)
  exact ⟨fun h ↦ h ▸ e.map_zero, fun h ↦ e.injective (h.trans e.map_zero.symm)⟩

/-- Beyond the nilpotency exponent, evaluation at level `n` followed by the projection to `B / J`
is the canonical map from the completion to `B / J`. -/
private theorem factor_evalₐ_eq_completionToQuotient
    (hp : IsNilpotent (Ideal.Quotient.mk J (p : B))) {n : ℕ}
    (hN : DividedPowers.nilpotencyExponent J p hp ≤ n) (x : AdicCompletion
      (DividedPowers.pAdicIdeal (A := B) p) B) :
    Ideal.Quotient.factor ((Ideal.pow_le_pow_right hN).trans
        (DividedPowers.pAdicIdeal_pow_nilpotencyExponent_le J p hp))
      (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := B) p) n x) =
    DividedPowers.completionToQuotient J p hp x := by
  change _ = Ideal.Quotient.factor
    (DividedPowers.pAdicIdeal_pow_nilpotencyExponent_le J p hp) (AdicCompletion.evalₐ _ _ x)
  rw [← factor_eval_completion _ hN x, Ideal.Quotient.factor_comp_apply]

/-- Evaluation at level `n` carries the divided power ideal of the completion onto the divided
power ideal of the level-`n` quotient. -/
public theorem completionIdeal_map_eval
    (hp : IsNilpotent (Ideal.Quotient.mk J (p : B))) (n : ℕ)
    (hn : DividedPowers.pAdicIdeal (A := B) p ^ n ≤ J)
    (hN : DividedPowers.nilpotencyExponent J p hp ≤ n) :
    (DividedPowers.completionIdeal J p hp).map
      (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := B) p) n).toRingHom =
      J.map (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := B) p ^ n)) := by
  let I := DividedPowers.pAdicIdeal (A := B) p
  rw [← Ideal.Quotient.factor_ker hn]
  apply le_antisymm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro x hx
    change Ideal.Quotient.factor hn (AdicCompletion.evalₐ I n x) = 0
    rwa [factor_evalₐ_eq_completionToQuotient J p hp hN x]
  · intro x hx
    obtain ⟨y, rfl⟩ := AdicCompletion.surjective_evalₐ I n x
    apply Ideal.mem_map_of_mem
    change DividedPowers.completionToQuotient J p hp y = 0
    rwa [← factor_evalₐ_eq_completionToQuotient J p hp hN y]

/-- Beyond the nilpotency exponent, the kernel of evaluation at level `n` is contained in the
divided power ideal of the completion. -/
public theorem ker_eval_le_completionIdeal
    (hp : IsNilpotent (Ideal.Quotient.mk J (p : B))) (n : ℕ)
    (hN : DividedPowers.nilpotencyExponent J p hp ≤ n) :
    RingHom.ker (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := B) p) n).toRingHom ≤
      DividedPowers.completionIdeal J p hp := by
  intro x hx
  change DividedPowers.completionToQuotient J p hp x = 0
  rw [← factor_evalₐ_eq_completionToQuotient J p hp hN x]
  change AdicCompletion.evalₐ _ n x = 0 at hx
  rw [hx]
  simp

/-- The transition maps of an adic system compose. -/
public theorem transitionMap_trans {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (I : Ideal R) {i j k : ℕ} (h : i ≤ j) (h' : j ≤ k)
    (x : M ⧸ I ^ k • (⊤ : Submodule R M)) :
    AdicCompletion.transitionMap I M h (AdicCompletion.transitionMap I M h' x) =
      AdicCompletion.transitionMap I M (h.trans h') x := by
  induction x using Submodule.Quotient.induction_on with | _ x => rfl

/-- An adic completion is the limit of any inverse system of additive groups which is levelwise
equivalent to the cofinal part of its own system of quotients, by an equivalence whose
projections are the given level equivalences. -/
public noncomputable def completionLimitEquiv
    {R M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) (N : ℕ) (F : ℕᵒᵖ ⥤ AddCommGrpCat.{v})
    (E : ∀ n, (M ⧸ I ^ (N + n) • (⊤ : Submodule R M)) ≃+ F.obj (Opposite.op n))
    (hE : ∀ {m n} (h : m ≤ n) x,
      F.map (homOfLE h).op (E n x) =
        E m (AdicCompletion.transitionMap I M (Nat.add_le_add_left h N) x)) :
    { L : AdicCompletion I M ≃+ (limit F : AddCommGrpCat.{v}) //
      ∀ n x, limit.π F (Opposite.op n) (L x) = E n (AdicCompletion.eval I M (N + n) x) } := by
  let c : Cone F := {
    pt := AddCommGrpCat.of (AdicCompletion I M)
    π := {
      app n := AddCommGrpCat.ofHom
        ((E n.unop).toAddMonoidHom.comp (AdicCompletion.eval I M (N + n.unop)).toAddMonoidHom)
      naturality := by
        intro n m f
        ext x
        change E m.unop (AdicCompletion.eval I M (N + m.unop) x) =
          F.map f (E n.unop (AdicCompletion.eval I M (N + n.unop) x))
        have hf : f = (homOfLE (leOfHom f.unop)).op := Subsingleton.elim _ _
        rw [hf, hE]
        exact congrArg (E m.unop) (x.property _).symm } }
  let L : AdicCompletion I M →+ (limit F : AddCommGrpCat.{v}) := (limit.lift F c).hom
  have hL (n : ℕ) (x : AdicCompletion I M) :
      limit.π F (Opposite.op n) (L x) = E n (AdicCompletion.eval I M (N + n) x) :=
    ConcreteCategory.congr_hom (limit.lift_π c (Opposite.op n)) x
  have hinj : Function.Injective L := by
    intro x y h
    apply AdicCompletion.ext
    intro n
    have H := congrArg (fun z ↦ limit.π F (Opposite.op n) z) h
    rw [hL, hL] at H
    have H' := (E n).injective H
    have H'' := congrArg (AdicCompletion.transitionMap I M (Nat.le_add_left n N)) H'
    simpa only [AdicCompletion.eval_apply, AdicCompletion.transitionMap_comp_eval_apply] using H''
  have hsurj : Function.Surjective L := by
    intro y
    let t (n : ℕ) := (E n).symm (limit.π F (Opposite.op n) y)
    have ht {m n : ℕ} (h : m ≤ n) :
        AdicCompletion.transitionMap I M (Nat.add_le_add_left h N) (t n) = t m := by
      apply (E m).injective
      rw [← hE]
      · simp only [t, AddEquiv.apply_symm_apply]
        exact ConcreteCategory.congr_hom (limit.w F (homOfLE h).op) y
    let x : AdicCompletion I M := ⟨fun n ↦
      AdicCompletion.transitionMap I M (Nat.le_add_left n N) (t n), by
        intro m n h
        dsimp only
        rw [transitionMap_trans, ← ht h, transitionMap_trans]⟩
    refine ⟨x, ?_⟩
    apply Concrete.limit_ext F
    intro n
    obtain ⟨n⟩ := n
    rw [hL]
    change E n (AdicCompletion.transitionMap I M (Nat.le_add_left (N + n) N) (t (N + n))) = _
    rw [ht (Nat.le_add_left n N)]
    exact (E n).apply_symm_apply _
  exact ⟨AddEquiv.ofBijective L ⟨hinj, hsurj⟩, hL⟩

/-- Levelwise comparison equivalences built from a factored pair of divided power morphisms are
compatible with the transition maps of the two adic systems. -/
public theorem comparison_transition
    {C D : Type*} [CommRing C] [CommRing D] [Algebra A C] [Algebra A D]
    {K : Ideal C} {L : Ideal D} (epsilon : DividedPowers K) (zeta : DividedPowers L)
    (f : B →ₐ[A] C) (g : C →ₐ[A] D) (k : B →ₐ[A] D)
    (hf : delta.IsDPMorphism epsilon f.toRingHom)
    (hg : epsilon.IsDPMorphism zeta g.toRingHom)
    (hk : delta.IsDPMorphism zeta k.toRingHom) (hcomp : g.comp f = k)
    (I : Ideal B) {m n : ℕ} (hmn : m ≤ n)
    (E : (dividedPowerDifferentials (A := A) delta ⧸ I ^ n •
      (⊤ : Submodule B (dividedPowerDifferentials (A := A) delta))) ≃+
        dividedPowerDifferentials (A := A) epsilon)
    (F : (dividedPowerDifferentials (A := A) delta ⧸ I ^ m •
      (⊤ : Submodule B (dividedPowerDifferentials (A := A) delta))) ≃+
        dividedPowerDifferentials (A := A) zeta)
    (hE : ∀ x, E (Submodule.Quotient.mk x) =
      mapDifferentialsOfDPMorphism (J := J) (delta := delta) epsilon f hf x)
    (hF : ∀ x, F (Submodule.Quotient.mk x) =
      mapDifferentialsOfDPMorphism (J := J) (delta := delta) zeta k hk x)
    (x : dividedPowerDifferentials (A := A) delta ⧸ I ^ n •
      (⊤ : Submodule B (dividedPowerDifferentials (A := A) delta))) :
    mapDifferentialsOfDPMorphism (J := K) (delta := epsilon) zeta g hg (E x) =
      F (AdicCompletion.transitionMap I _ hmn x) := by
  induction x using Submodule.Quotient.induction_on with | _ x =>
    change _ = F (Submodule.Quotient.mk x)
    rw [hE, hF]
    have H := mapDifferentialsOfDPMorphism_comp (J := J) (delta := delta)
      epsilon zeta f g hf hg
    have Hx := DFunLike.congr_fun H x
    simpa only [hcomp, AddMonoidHom.comp_apply] using Hx

/-- A canonical inverse system of divided power differentials of the quotients
`B / p ^ (cutoff + e) B`. The formula on universal differentials determines each transition
map. -/
public structure QuotientDifferentialsSystem where
  /-- A level after which the quotient divided powers exist. -/
  cutoff : ℕ
  /-- Above the cutoff, `p ^ e B` is contained in the divided power ideal and is stable under
  its divided powers. -/
  level : ∀ e, cutoff ≤ e →
    (DividedPowers.pAdicIdeal (A := B) p ^ e ≤ J) ∧
      delta.IsSubDPIdeal (DividedPowers.pAdicIdeal (A := B) p ^ e)
  /-- The transition on divided power differentials from level `cutoff + e'` to level
  `cutoff + e`. -/
  transition {e e' : ℕ} (h : e ≤ e') :
    dividedPowerDifferentials (A := A)
        (DividedPowers.quotientDividedPowers J delta p (cutoff + e')
          (level (cutoff + e') (Nat.le_add_right cutoff e')).1
          (level (cutoff + e') (Nat.le_add_right cutoff e')).2) →+
      dividedPowerDifferentials (A := A)
        (DividedPowers.quotientDividedPowers J delta p (cutoff + e)
          (level (cutoff + e) (Nat.le_add_right cutoff e)).1
          (level (cutoff + e) (Nat.le_add_right cutoff e)).2)
  /-- A transition sends a universal differential to the corresponding differential below. -/
  transition_d {e e' : ℕ} (h : e ≤ e') (b : B) :
    transition h
        (dividedPowerDifferential (A := A)
          (DividedPowers.quotientDividedPowers J delta p (cutoff + e')
            (level (cutoff + e') (Nat.le_add_right cutoff e')).1
            (level (cutoff + e') (Nat.le_add_right cutoff e')).2)
          (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := B) p ^ (cutoff + e')) b)) =
      dividedPowerDifferential (A := A)
        (DividedPowers.quotientDividedPowers J delta p (cutoff + e)
          (level (cutoff + e) (Nat.le_add_right cutoff e)).1
          (level (cutoff + e) (Nat.le_add_right cutoff e)).2)
        (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := B) p ^ (cutoff + e)) b)
  /-- The transition at a fixed level is the identity. -/
  transition_id (e : ℕ) : transition (le_refl e) = AddMonoidHom.id _
  /-- The transition maps compose. -/
  transition_comp {e e' e'' : ℕ} (h : e ≤ e') (h' : e' ≤ e'') :
    (transition h).comp (transition h') = transition (h.trans h')

namespace QuotientDifferentialsSystem

/-- The term at index `e` of the reindexed quotient-differentials system. -/
public noncomputable abbrev term
    (S : QuotientDifferentialsSystem (A := A) J delta p) (e : ℕ) : Type v :=
  dividedPowerDifferentials (A := A)
    (DividedPowers.quotientDividedPowers J delta p (S.cutoff + e)
      (S.level (S.cutoff + e) (Nat.le_add_right S.cutoff e)).1
      (S.level (S.cutoff + e) (Nat.le_add_right S.cutoff e)).2)

/-- The quotient-differentials inverse system as a functor to additive commutative groups. -/
public noncomputable def functor
    (S : QuotientDifferentialsSystem (A := A) J delta p) : ℕᵒᵖ ⥤ AddCommGrpCat where
  obj e := AddCommGrpCat.of (term (A := A) J delta p S e.unop)
  map f := AddCommGrpCat.ofHom (S.transition (leOfHom f.unop))
  map_id e := by
    ext x
    exact DFunLike.congr_fun (S.transition_id e.unop) x
  map_comp f g := by
    ext x
    exact DFunLike.congr_fun
      (S.transition_comp (leOfHom g.unop) (leOfHom f.unop)).symm x

end QuotientDifferentialsSystem

/-- The inverse system of divided power differentials of the quotients `B / p^e B`, assembled from
a level beyond which those quotients carry divided powers. -/
public noncomputable def quotientSystemOfLevels
    (N : ℕ) (levels : ∀ e, N ≤ e →
      (DividedPowers.pAdicIdeal (A := B) p ^ e ≤ J) ∧
        delta.IsSubDPIdeal (DividedPowers.pAdicIdeal (A := B) p ^ e)) :
    QuotientDifferentialsSystem (A := A) J delta p := by
  classical
  refine {
    cutoff := N
    level := levels
    transition := ?_
    transition_d := ?_
    transition_id := ?_
    transition_comp := ?_ }
  · intro e e' h
    let m := N + e
    let n := N + e'
    let K₁ := DividedPowers.pAdicIdeal (A := B) p ^ n
    let K₂ := DividedPowers.pAdicIdeal (A := B) p ^ m
    have hK : K₁ ≤ K₂ := by
      dsimp [K₁, K₂]
      exact Ideal.pow_le_pow_right (Nat.add_le_add_left h N)
    have hn := levels n (by dsimp [n]; exact Nat.le_add_right N e')
    have hm := levels m (by dsimp [m]; exact Nat.le_add_right N e)
    let d₁ := DividedPowers.quotientDividedPowers J delta p n hn.1 hn.2
    let d₂ := DividedPowers.quotientDividedPowers J delta p m hm.1 hm.2
    let f : B ⧸ K₁ →ₐ[A] B ⧸ K₂ := Ideal.Quotient.factorₐ A hK
    have hf : DividedPowers.IsDPMorphism d₁ d₂ f.toRingHom := by
      simpa [d₁, d₂, f, DividedPowers.quotientDividedPowers] using
        (quotientFactor_isDPMorphism (J := J) (delta := delta)
          hK hn.1 hm.1 hn.2 hm.2)
    exact mapDifferentialsOfDPMorphism (A := A) (B := B ⧸ K₁)
      (J := Ideal.map (Ideal.Quotient.mk K₁) J) (delta := d₁)
      d₂ f hf
  · intro e e' h b
    let m := N + e
    let n := N + e'
    let K₁ := DividedPowers.pAdicIdeal (A := B) p ^ n
    let K₂ := DividedPowers.pAdicIdeal (A := B) p ^ m
    have hK : K₁ ≤ K₂ := by
      dsimp [K₁, K₂]
      exact Ideal.pow_le_pow_right (Nat.add_le_add_left h N)
    have hn := levels n (by dsimp [n]; exact Nat.le_add_right N e')
    have hm := levels m (by dsimp [m]; exact Nat.le_add_right N e)
    let d₁ := DividedPowers.quotientDividedPowers J delta p n hn.1 hn.2
    let d₂ := DividedPowers.quotientDividedPowers J delta p m hm.1 hm.2
    let f : B ⧸ K₁ →ₐ[A] B ⧸ K₂ := Ideal.Quotient.factorₐ A hK
    have hf : DividedPowers.IsDPMorphism d₁ d₂ f.toRingHom := by
      simpa [d₁, d₂, f, DividedPowers.quotientDividedPowers] using
        (quotientFactor_isDPMorphism (J := J) (delta := delta)
          hK hn.1 hm.1 hn.2 hm.2)
    change mapDifferentialsOfDPMorphism (A := A) (B := B ⧸ K₁)
      (J := Ideal.map (Ideal.Quotient.mk K₁) J) (delta := d₁)
      d₂ f hf
      (dividedPowerDifferential (A := A) d₁ (Ideal.Quotient.mk K₁ b)) = _
    rw [mapDifferentialsOfDPMorphism_d]
    simp [m, K₂, d₂, f]
  · intro e
    let m := N + e
    let K := DividedPowers.pAdicIdeal (A := B) p ^ m
    have hm := levels m (by dsimp [m]; exact Nat.le_add_right N e)
    let d := DividedPowers.quotientDividedPowers J delta p m hm.1 hm.2
    change mapDifferentialsOfDPMorphism (A := A) (B := B ⧸ K)
      (J := Ideal.map (Ideal.Quotient.mk K) J) (delta := d)
      d (Ideal.Quotient.factorₐ A (le_rfl : K ≤ K)) _ = AddMonoidHom.id _
    have hfac : Ideal.Quotient.factorₐ A (le_rfl : K ≤ K) =
        AlgHom.id A (B ⧸ K) := by
      ext x
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp
    have hf : d.IsDPMorphism d
        (Ideal.Quotient.factorₐ A (le_rfl : K ≤ K)).toRingHom := by
      rw [hfac]
      have hr : (AlgHom.id A (B ⧸ K)).toRingHom =
          (DividedPowers.DPMorphism.id d).toRingHom := by
        ext x
        rfl
      rw [hr]
      exact (DividedPowers.DPMorphism.id d).isDPMorphism
    change mapDifferentialsOfDPMorphism (A := A) (B := B ⧸ K)
      (J := Ideal.map (Ideal.Quotient.mk K) J) (delta := d)
      d (Ideal.Quotient.factorₐ A (le_rfl : K ≤ K)) hf = AddMonoidHom.id _
    simpa [hfac] using mapDifferentialsOfDPMorphism_id (A := A) (B := B ⧸ K)
      (J := Ideal.map (Ideal.Quotient.mk K) J) (delta := d)
  · intro e e' e'' h h'
    let m := N + e
    let n := N + e'
    let k := N + e''
    let K₁ := DividedPowers.pAdicIdeal (A := B) p ^ m
    let K₂ := DividedPowers.pAdicIdeal (A := B) p ^ n
    let K₃ := DividedPowers.pAdicIdeal (A := B) p ^ k
    have h₁₂ : K₂ ≤ K₁ := by
      dsimp [K₁, K₂]
      exact Ideal.pow_le_pow_right (Nat.add_le_add_left h N)
    have h₂₃ : K₃ ≤ K₂ := by
      dsimp [K₂, K₃]
      exact Ideal.pow_le_pow_right (Nat.add_le_add_left h' N)
    have h₁₃ : K₃ ≤ K₁ := h₂₃.trans h₁₂
    have hm := levels m (by dsimp [m]; exact Nat.le_add_right N e)
    have hn := levels n (by dsimp [n]; exact Nat.le_add_right N e')
    have hk := levels k (by dsimp [k]; exact Nat.le_add_right N e'')
    let d₁ := DividedPowers.quotientDividedPowers J delta p m hm.1 hm.2
    let d₂ := DividedPowers.quotientDividedPowers J delta p n hn.1 hn.2
    let d₃ := DividedPowers.quotientDividedPowers J delta p k hk.1 hk.2
    let f : B ⧸ K₃ →ₐ[A] B ⧸ K₂ := Ideal.Quotient.factorₐ A h₂₃
    let g : B ⧸ K₂ →ₐ[A] B ⧸ K₁ := Ideal.Quotient.factorₐ A h₁₂
    have hf : DividedPowers.IsDPMorphism d₃ d₂ f.toRingHom := by
      simpa [d₂, d₃, f, DividedPowers.quotientDividedPowers] using
        (quotientFactor_isDPMorphism (J := J) (delta := delta)
          h₂₃ hk.1 hn.1 hk.2 hn.2)
    have hg : DividedPowers.IsDPMorphism d₂ d₁ g.toRingHom := by
      simpa [d₁, d₂, g, DividedPowers.quotientDividedPowers] using
        (quotientFactor_isDPMorphism (J := J) (delta := delta)
          h₁₂ hn.1 hm.1 hn.2 hm.2)
    have hcomp := mapDifferentialsOfDPMorphism_comp (A := A) (B := B ⧸ K₃)
      (J := Ideal.map (Ideal.Quotient.mk K₃) J) (delta := d₃) d₂ d₁ f g hf hg
    simpa [m, n, k, K₁, K₂, K₃, d₁, d₂, d₃, f, g,
      Ideal.Quotient.factorₐ_apply] using hcomp


/-- The canonical comparison of the three inverse limits in Stacks Project, Tag 07KK. -/
public structure DifferentialsCompletionComparison
    (hp : IsNilpotent (Ideal.Quotient.mk J (p : B))) where
  /-- The inverse system of differentials of sufficiently deep quotients. -/
  quotientSystem : QuotientDifferentialsSystem (A := A) J delta p
  /-- The finite-level comparison
  `Ω_(B/A,δ) / p ^ e Ω_(B/A,δ) ≃ Ω_(B_e/A,δ̄)`. -/
  fromOriginalAt (e : ℕ) :
    differentialsModPow (A := A) J delta p (quotientSystem.cutoff + e) ≃ₗ[B]
      QuotientDifferentialsSystem.term (A := A) J delta p quotientSystem e
  /-- The original-ring comparison is induced by `B → B_e` on universal differentials. -/
  fromOriginalAt_d (e : ℕ) (b : B) :
    fromOriginalAt e
        (Submodule.Quotient.mk (dividedPowerDifferential (A := A) delta b)) =
      dividedPowerDifferential (A := A)
        (DividedPowers.quotientDividedPowers J delta p (quotientSystem.cutoff + e)
          (quotientSystem.level _ (Nat.le_add_right quotientSystem.cutoff e)).1
          (quotientSystem.level _ (Nat.le_add_right quotientSystem.cutoff e)).2)
        (Ideal.Quotient.mk
          (DividedPowers.pAdicIdeal (A := B) p ^ (quotientSystem.cutoff + e)) b)
  /-- The original-ring finite-level comparisons commute with Mathlib's adic transition maps. -/
  fromOriginalAt_transition {e e' : ℕ} (h : e ≤ e')
      (omega : differentialsModPow (A := A) J delta p (quotientSystem.cutoff + e')) :
    quotientSystem.transition h (fromOriginalAt e' omega) =
      fromOriginalAt e
        (AdicCompletion.transitionMap (DividedPowers.pAdicIdeal (A := B) p)
          (dividedPowerDifferentials (A := A) delta)
          (Nat.add_le_add_left h quotientSystem.cutoff) omega)
  /-- The finite-level comparison
  `Ω_(B̂/A,δ̂) / p ^ e Ω_(B̂/A,δ̂) ≃ Ω_(B_e/A,δ̄)`. -/
  fromCompletionAt (e : ℕ) :
    completedDifferentialsModPow (A := A) J delta p hp (quotientSystem.cutoff + e) ≃+
      QuotientDifferentialsSystem.term (A := A) J delta p quotientSystem e
  /-- The completed-ring comparison is induced by the projection `B̂ → B_e`. -/
  fromCompletionAt_d (e : ℕ)
      (b : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) :
    fromCompletionAt e
        (Submodule.Quotient.mk
          (dividedPowerDifferential (A := A)
            (DividedPowers.completedDividedPowers J delta p hp).1 b)) =
      dividedPowerDifferential (A := A)
        (DividedPowers.quotientDividedPowers J delta p (quotientSystem.cutoff + e)
          (quotientSystem.level _ (Nat.le_add_right quotientSystem.cutoff e)).1
          (quotientSystem.level _ (Nat.le_add_right quotientSystem.cutoff e)).2)
        (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := B) p)
          (quotientSystem.cutoff + e) b)
  /-- The completed-ring comparison is semilinear for the projection `B̂ → B_e`. -/
  fromCompletionAt_smul (e : ℕ)
      (b : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
      (omega : completedDifferentialsModPow (A := A) J delta p hp
        (quotientSystem.cutoff + e)) :
    fromCompletionAt e (b • omega) =
      AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := B) p)
          (quotientSystem.cutoff + e) b • fromCompletionAt e omega
  /-- The completed-ring finite-level comparisons commute with adic transition maps. -/
  fromCompletionAt_transition {e e' : ℕ} (h : e ≤ e')
      (omega : completedDifferentialsModPow (A := A) J delta p hp
        (quotientSystem.cutoff + e')) :
    quotientSystem.transition h (fromCompletionAt e' omega) =
      fromCompletionAt e
        (AdicCompletion.transitionMap
          (DividedPowers.pAdicIdeal
            (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p)
          (dividedPowerDifferentials (A := A)
            (DividedPowers.completedDividedPowers J delta p hp).1)
          (Nat.add_le_add_left h quotientSystem.cutoff) omega)
  /-- The middle inverse limit is canonically the limit of the quotient-differentials system. -/
  fromOriginalLimit :
    AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
        (dividedPowerDifferentials (A := A) delta) ≃+
      ((limit (QuotientDifferentialsSystem.functor (A := A) J delta p quotientSystem) :
        AddCommGrpCat) : Type v)
  /-- The preceding equivalence commutes with every limit projection. -/
  fromOriginalLimit_projection (e : ℕ)
      (omega : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
        (dividedPowerDifferentials (A := A) delta)) :
    limit.π (QuotientDifferentialsSystem.functor (A := A) J delta p quotientSystem)
        (Opposite.op e)
        (fromOriginalLimit omega) =
      fromOriginalAt e
        (AdicCompletion.eval (DividedPowers.pAdicIdeal (A := B) p)
          (dividedPowerDifferentials (A := A) delta)
          (quotientSystem.cutoff + e) omega)
  /-- The last inverse limit is canonically the limit of the quotient-differentials system. -/
  fromCompletionLimit :
    AdicCompletion
        (DividedPowers.pAdicIdeal
          (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p)
        (dividedPowerDifferentials (A := A)
          (DividedPowers.completedDividedPowers J delta p hp).1) ≃+
      ((limit (QuotientDifferentialsSystem.functor (A := A) J delta p quotientSystem) :
        AddCommGrpCat) : Type v)
  /-- The preceding equivalence commutes with every limit projection. -/
  fromCompletionLimit_projection (e : ℕ)
      (omega : AdicCompletion
        (DividedPowers.pAdicIdeal
          (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p)
        (dividedPowerDifferentials (A := A)
          (DividedPowers.completedDividedPowers J delta p hp).1)) :
    limit.π (QuotientDifferentialsSystem.functor (A := A) J delta p quotientSystem)
        (Opposite.op e)
        (fromCompletionLimit omega) =
      fromCompletionAt e
        (AdicCompletion.eval
          (DividedPowers.pAdicIdeal
            (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p)
          (dividedPowerDifferentials (A := A)
            (DividedPowers.completedDividedPowers J delta p hp).1)
          (quotientSystem.cutoff + e) omega)

/-- **The comparison of [Stacks, Lemma 60.20.1, Tag 07KK], with the `ℤ_(p)`-algebra structure
carried by `B`.**  This is `Crystalline.dividedPowerDifferentialsCompletionComparison` with its
hypothesis that the base `A` is a `ℤ_(p)`-algebra replaced by the weaker one that `B` is; that is
all the construction uses, and it is what a base which is not itself a `ℤ_(p)`-algebra, such as
the base of a divided power envelope in which `p` is only nilpotent modulo the divided power
ideal, can supply. -/
public noncomputable def dividedPowerDifferentialsCompletionComparisonOfAlgebra
    [Fact p.Prime] [Algebra (DividedPowers.IntegersAtPrime p) B]
    (hp : IsNilpotent (Ideal.Quotient.mk J (p : B))) :
    DifferentialsCompletionComparison (A := A) (B := B) J delta p hp := by
  classical
  have hex := DividedPowers.eventually_isDividedPowerCompletionLimit.{v, v} J delta p hp
  let N₀ := hex.choose
  let levels₀ := hex.choose_spec.choose
  have hlim := hex.choose_spec.choose_spec
  let N := max N₀ (DividedPowers.nilpotencyExponent J p hp)
  let levels : ∀ n, N ≤ n →
      (DividedPowers.pAdicIdeal (A := B) p ^ n ≤ J) ∧
        delta.IsSubDPIdeal (DividedPowers.pAdicIdeal (A := B) p ^ n) :=
    fun n hn ↦ levels₀ n ((le_max_left _ _).trans hn)
  let S := quotientSystemOfLevels (A := A) J delta p N levels
  let I := DividedPowers.pAdicIdeal (A := B) p
  let C := AdicCompletion I B
  let Ih := DividedPowers.pAdicIdeal (A := C) p
  let Jh := DividedPowers.completionIdeal J p hp
  let dh := (DividedPowers.completedDividedPowers J delta p hp).val
  let dq (e : ℕ) := DividedPowers.quotientDividedPowers J delta p (N + e)
    (levels (N + e) (Nat.le_add_right N e)).1
    (levels (N + e) (Nat.le_add_right N e)).2
  let q (e : ℕ) : B →ₐ[A] B ⧸ I ^ (N + e) := Ideal.Quotient.mkₐ A _
  have hq (e : ℕ) : delta.IsDPMorphism (dq e) (q e).toRingHom :=
    DividedPowers.Quotient.isDPMorphism delta _
  let f (e : ℕ) : C →ₐ[A] B ⧸ I ^ (N + e) :=
    (AdicCompletion.evalₐ I (N + e)).restrictScalars A
  have hf (e : ℕ) : dh.IsDPMorphism (dq e) (f e).toRingHom :=
    hlim.1 (N + e) ((le_max_left _ _).trans (Nat.le_add_right N e))
  let O (e : ℕ) := differentialsQuotientEquiv (A := A) J delta (I ^ (N + e))
    (levels (N + e) (Nat.le_add_right N e)).2
    (fun b hb ↦ dividedPowerDifferential_mem_pAdicPow (A := A) J delta p (N + e) hb)
  have hO (e : ℕ) (x : dividedPowerDifferentials (A := A) delta) :
      (O e).val (Submodule.Quotient.mk x) =
        mapDifferentialsOfDPMorphism (J := J) (delta := delta) (dq e) (q e) (hq e) x :=
    differentialsQuotientEquiv_mk (A := A) J delta _ _ _ x
  let H (e : ℕ) := differentialsSurjectionEquiv (A := A) Jh dh (dq e) (f e) (hf e)
    (AdicCompletion.surjective_evalₐ I (N + e))
    (completionIdeal_map_eval J p hp (N + e) (levels _ (Nat.le_add_right N e)).1
      ((le_max_right _ _).trans (Nat.le_add_right N e)))
    (Ih ^ (N + e)) (pAdicIdeal_eq_ker_eval (B := B) p (N + e))
    (by rw [pAdicIdeal_eq_ker_eval (B := B) p (N + e)]
        exact ker_eval_le_completionIdeal J p hp (N + e)
          ((le_max_right _ _).trans (Nat.le_add_right N e)))
    (fun b hb ↦ by
      exact dividedPowerDifferential_mem_pAdicPow (A := A) Jh dh p (N + e) hb)
  have hOt {e e' : ℕ} (h : e ≤ e') (x : differentialsModPow (A := A) J delta p (N + e')) :
      S.transition h ((O e').val x) =
        (O e).val (AdicCompletion.transitionMap I _ (Nat.add_le_add_left h N) x) := by
    let g : (B ⧸ I ^ (N + e')) →ₐ[A] B ⧸ I ^ (N + e) :=
      Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (Nat.add_le_add_left h N))
    have hg : (dq e').IsDPMorphism (dq e) g.toRingHom :=
      quotientFactor_isDPMorphism (J := J) (delta := delta)
        (Ideal.pow_le_pow_right (Nat.add_le_add_left h N))
        (levels (N + e') (Nat.le_add_right N e')).1
        (levels (N + e) (Nat.le_add_right N e)).1
        (levels (N + e') (Nat.le_add_right N e')).2
        (levels (N + e) (Nat.le_add_right N e)).2
    change mapDifferentialsOfDPMorphism (J := _) (delta := dq e') (dq e) g hg _ = _
    exact comparison_transition (J := J) (delta := delta) (dq e') (dq e) (q e') g (q e)
      (hq e') hg (hq e) (by ext b; rfl) I (Nat.add_le_add_left h N)
      (O e').val.toAddEquiv (O e).val.toAddEquiv (hO e') (hO e) x
  have hHt {e e' : ℕ} (h : e ≤ e')
      (x : completedDifferentialsModPow (A := A) J delta p hp (N + e')) :
      S.transition h ((H e').val x) =
        (H e).val (AdicCompletion.transitionMap Ih _ (Nat.add_le_add_left h N) x) := by
    let g : (B ⧸ I ^ (N + e')) →ₐ[A] B ⧸ I ^ (N + e) :=
      Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (Nat.add_le_add_left h N))
    have hg : (dq e').IsDPMorphism (dq e) g.toRingHom :=
      quotientFactor_isDPMorphism (J := J) (delta := delta)
        (Ideal.pow_le_pow_right (Nat.add_le_add_left h N))
        (levels (N + e') (Nat.le_add_right N e')).1
        (levels (N + e) (Nat.le_add_right N e)).1
        (levels (N + e') (Nat.le_add_right N e')).2
        (levels (N + e) (Nat.le_add_right N e)).2
    have hcomp : g.comp (f e') = f e := by
      ext b
      exact factor_eval_completion I (Nat.add_le_add_left h N) b
    change mapDifferentialsOfDPMorphism (J := _) (delta := dq e') (dq e) g hg _ = _
    exact comparison_transition (J := Jh) (delta := dh) (dq e') (dq e) (f e') g (f e)
      (hf e') hg (hf e) hcomp Ih (Nat.add_le_add_left h N)
      (H e').val (H e).val (H e').property (H e).property x
  let LO := completionLimitEquiv I N (QuotientDifferentialsSystem.functor J delta p S)
    (fun e ↦ (O e).val.toAddEquiv) (fun h x ↦ hOt h x)
  let LH := completionLimitEquiv Ih N (QuotientDifferentialsSystem.functor J delta p S)
    (fun e ↦ (H e).val) (fun h x ↦ hHt h x)
  refine {
    quotientSystem := S
    fromOriginalAt := fun e ↦ (O e).val
    fromOriginalAt_d := fun e b ↦ (O e).property b
    fromOriginalAt_transition := hOt
    fromCompletionAt := fun e ↦ (H e).val
    fromCompletionAt_d := ?_
    fromCompletionAt_smul := ?_
    fromCompletionAt_transition := hHt
    fromOriginalLimit := LO.val
    fromOriginalLimit_projection := LO.property
    fromCompletionLimit := LH.val
    fromCompletionLimit_projection := LH.property }
  · intro e b
    change (H e).val (Submodule.Quotient.mk (dividedPowerDifferential (A := A) dh b)) = _
    rw [(H e).property]
    exact mapDifferentialsOfDPMorphism_d (J := Jh) (delta := dh) (dq e) (f e) (hf e) b
  · intro e b x
    induction x using Submodule.Quotient.induction_on with | _ x =>
      change (H e).val (Submodule.Quotient.mk (b • x)) =
        f e b • (H e).val (Submodule.Quotient.mk x)
      rw [(H e).property, (H e).property]
      exact mapDifferentialsOfDPMorphism_smul (J := Jh) (delta := dh) (dq e) (f e) (hf e) b x

/-- The comparison of [Stacks, Lemma 60.20.1, Tag 07KK] exists: the inverse limits of divided
power differentials of the finite quotients, of the original ring modulo powers of `p`, and of
the completed ring modulo powers of `p` are canonically equivalent.  The equalities this asserts
are written out, free of this structure, in
`Crystalline.exists_dividedPowerDifferentialsCompletionEquiv`. -/
public noncomputable def dividedPowerDifferentialsCompletionComparison
    [Fact p.Prime] [Algebra (DividedPowers.IntegersAtPrime p) A]
    (hp : IsNilpotent (Ideal.Quotient.mk J (p : B))) :
    DifferentialsCompletionComparison (A := A) (B := B) J delta p hp :=
  letI : Algebra (DividedPowers.IntegersAtPrime p) B :=
    ((algebraMap A B).comp (algebraMap (DividedPowers.IntegersAtPrime p) A)).toAlgebra
  dividedPowerDifferentialsCompletionComparisonOfAlgebra J delta p hp

/-- `Ω_{B_e/A, δ̄}`: the module of divided power differentials of the quotient `B_e = B / pᵉ B`,
for the divided powers `δ̄` that `δ` induces on it once `pᵉ B` lies in `J` and is stable under
the divided power operations of `δ`. -/
public noncomputable abbrev quotientDifferentials (e : ℕ)
    (hle : DividedPowers.pAdicIdeal (A := B) p ^ e ≤ J)
    (hsub : delta.IsSubDPIdeal (DividedPowers.pAdicIdeal (A := B) p ^ e)) : Type v :=
  dividedPowerDifferentials (A := A)
    (DividedPowers.quotientDividedPowers J delta p e hle hsub)

/-- Let `A → B` be a ring map, let `(J, δ)` be a divided power structure on `B`, let `p` be
prime, let `A` be a `ℤ_(p)`-algebra and let `p` be nilpotent in `B / J`.  Then
`lim_e Ω_{B_e/A, δ̄} = lim_e Ω_{B/A, δ} / pᵉ Ω_{B/A, δ}
  = lim_e Ω_{B^∧/A, δ^∧} / pᵉ Ω_{B^∧/A, δ^∧}`.

The conclusion is written out here, with no reference to
`Crystalline.DifferentialsCompletionComparison`.  Beyond a level `N`, each `pᵉ B` lies in `J` and
is stable under the divided powers of `δ` (`level`), so `B_e = B / pᵉ B` carries divided powers
`δ̄` and the modules `Ω_{B_e/A, δ̄} = Crystalline.quotientDifferentials ..` form an inverse system
whose transition maps are those induced on universal differentials (`transition`, and the first
conjunct).  The second and third limits are Mathlib's `AdicCompletion`s of `Ω_{B/A, δ}` and of
`Ω_{B^∧/A, δ^∧}`; `fromOriginal` and `fromCompletion` identify every level of their towers of
quotients with that system, compatibly with all three families of transition maps, which is the
first equality in the strong form of an isomorphism of inverse systems.  `limitEquiv` is the
isomorphism of the second limit with the third that results, and the last conjunct says its
component at each level `N + e` is `fromOriginal` followed by the inverse of `fromCompletion`. -/
@[stacks 07KK,
  stacks 07J9 "the identification of the inverse limits that defines Ω_D, the case B = D",
  stacks 07L0 "the same identification of the limits, read at the divided power envelope D(n)"]
public theorem exists_dividedPowerDifferentialsCompletionEquiv
    [Fact p.Prime] [Algebra (DividedPowers.IntegersAtPrime p) A]
    (hp : IsNilpotent (Ideal.Quotient.mk J (p : B))) :
    ∃ (N : ℕ)
      (level : ∀ e, N ≤ e → (DividedPowers.pAdicIdeal (A := B) p ^ e ≤ J) ∧
        delta.IsSubDPIdeal (DividedPowers.pAdicIdeal (A := B) p ^ e))
      (transition : ∀ e e' : ℕ, e ≤ e' →
        quotientDifferentials (A := A) J delta p (N + e')
            (level _ (Nat.le_add_right N e')).1 (level _ (Nat.le_add_right N e')).2 →+
          quotientDifferentials (A := A) J delta p (N + e)
            (level _ (Nat.le_add_right N e)).1 (level _ (Nat.le_add_right N e)).2)
      (fromOriginal : ∀ e : ℕ, differentialsModPow (A := A) J delta p (N + e) ≃ₗ[B]
        quotientDifferentials (A := A) J delta p (N + e)
          (level _ (Nat.le_add_right N e)).1 (level _ (Nat.le_add_right N e)).2)
      (fromCompletion : ∀ e : ℕ,
        completedDifferentialsModPow (A := A) J delta p hp (N + e) ≃+
          quotientDifferentials (A := A) J delta p (N + e)
            (level _ (Nat.le_add_right N e)).1 (level _ (Nat.le_add_right N e)).2)
      (limitEquiv : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
            (dividedPowerDifferentials (A := A) delta) ≃+
          AdicCompletion
            (DividedPowers.pAdicIdeal
              (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p)
            (dividedPowerDifferentials (A := A)
              (DividedPowers.completedDividedPowers J delta p hp).1)),
      (∀ (e e' : ℕ) (h : e ≤ e') (b : B),
          transition e e' h
              (dividedPowerDifferential (A := A)
                (DividedPowers.quotientDividedPowers J delta p (N + e')
                  (level _ (Nat.le_add_right N e')).1 (level _ (Nat.le_add_right N e')).2)
                (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := B) p ^ (N + e')) b)) =
            dividedPowerDifferential (A := A)
              (DividedPowers.quotientDividedPowers J delta p (N + e)
                (level _ (Nat.le_add_right N e)).1 (level _ (Nat.le_add_right N e)).2)
              (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := B) p ^ (N + e)) b)) ∧
      (∀ (e : ℕ) (b : B),
          fromOriginal e
              (Submodule.Quotient.mk (dividedPowerDifferential (A := A) delta b)) =
            dividedPowerDifferential (A := A)
              (DividedPowers.quotientDividedPowers J delta p (N + e)
                (level _ (Nat.le_add_right N e)).1 (level _ (Nat.le_add_right N e)).2)
              (Ideal.Quotient.mk (DividedPowers.pAdicIdeal (A := B) p ^ (N + e)) b)) ∧
      (∀ (e e' : ℕ) (h : e ≤ e')
          (omega : differentialsModPow (A := A) J delta p (N + e')),
          transition e e' h (fromOriginal e' omega) =
            fromOriginal e
              (AdicCompletion.transitionMap (DividedPowers.pAdicIdeal (A := B) p)
                (dividedPowerDifferentials (A := A) delta)
                (Nat.add_le_add_left h N) omega)) ∧
      (∀ (e : ℕ) (b : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B),
          fromCompletion e
              (Submodule.Quotient.mk
                (dividedPowerDifferential (A := A)
                  (DividedPowers.completedDividedPowers J delta p hp).1 b)) =
            dividedPowerDifferential (A := A)
              (DividedPowers.quotientDividedPowers J delta p (N + e)
                (level _ (Nat.le_add_right N e)).1 (level _ (Nat.le_add_right N e)).2)
              (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := B) p) (N + e) b)) ∧
      (∀ (e : ℕ) (b : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
          (omega : completedDifferentialsModPow (A := A) J delta p hp (N + e)),
          fromCompletion e (b • omega) =
            AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := B) p) (N + e) b •
              fromCompletion e omega) ∧
      (∀ (e e' : ℕ) (h : e ≤ e')
          (omega : completedDifferentialsModPow (A := A) J delta p hp (N + e')),
          transition e e' h (fromCompletion e' omega) =
            fromCompletion e
              (AdicCompletion.transitionMap
                (DividedPowers.pAdicIdeal
                  (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p)
                (dividedPowerDifferentials (A := A)
                  (DividedPowers.completedDividedPowers J delta p hp).1)
                (Nat.add_le_add_left h N) omega)) ∧
      (∀ (e : ℕ) (omega : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p)
            (dividedPowerDifferentials (A := A) delta)),
          fromCompletion e
              (AdicCompletion.eval
                (DividedPowers.pAdicIdeal
                  (A := AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B) p)
                (dividedPowerDifferentials (A := A)
                  (DividedPowers.completedDividedPowers J delta p hp).1)
                (N + e) (limitEquiv omega)) =
            fromOriginal e
              (AdicCompletion.eval (DividedPowers.pAdicIdeal (A := B) p)
                (dividedPowerDifferentials (A := A) delta) (N + e) omega)) := by
  have cmp := dividedPowerDifferentialsCompletionComparison (A := A) J delta p hp
  refine ⟨cmp.quotientSystem.cutoff, cmp.quotientSystem.level,
    fun _ _ h ↦ cmp.quotientSystem.transition h, cmp.fromOriginalAt, cmp.fromCompletionAt,
    cmp.fromOriginalLimit.trans cmp.fromCompletionLimit.symm,
    fun _ _ h b ↦ cmp.quotientSystem.transition_d h b, cmp.fromOriginalAt_d,
    fun _ _ h omega ↦ cmp.fromOriginalAt_transition h omega, cmp.fromCompletionAt_d,
    cmp.fromCompletionAt_smul,
    fun _ _ h omega ↦ cmp.fromCompletionAt_transition h omega, ?_⟩
  intro e omega
  have h1 := cmp.fromCompletionLimit_projection e
    (cmp.fromCompletionLimit.symm (cmp.fromOriginalLimit omega))
  rw [cmp.fromCompletionLimit.apply_symm_apply] at h1
  exact h1.symm.trans (cmp.fromOriginalLimit_projection e omega)

end Crystalline

end
