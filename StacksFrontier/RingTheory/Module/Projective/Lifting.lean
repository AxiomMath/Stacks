module

public import StacksFrontier.RingTheory.Smooth.Lifting
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v

/-!
# Lifting projective modules along nilpotent ideals

Let `R` be a ring and `I ⊆ R` a two-sided ideal. This file proves:

* **Stacks 07LV.** If `I` is nilpotent, every projective `R ⧸ I`-module `Q` is the reduction of a
  projective `R`-module: there is a projective `R`-module `P` with `P/IP ≅ Q`.
* **Stacks 0D47.** If `R` is commutative and `I` is locally nilpotent, every finite projective
  `R ⧸ I`-module is the reduction of a finite projective `R`-module.
* **Stacks 0H7M.** If `R` is commutative, `I ∩ J = 0`, and `P/IP`, `P/JP` are projective over
  `R ⧸ I`, `R ⧸ J`, then `P` is projective.

The first two are one argument. Write `F` for the free `R`-module on a generating set of `Q` and
`F/IF` for its reduction. Projectivity of `Q` splits the surjection `F/IF ↠ Q`, which produces a
projector `e = s ∘ π` of `F/IF` with image `Q`. Since `F` is projective the reduction map
`End_R(F) → End_{R ⧸ I}(F/IF)` is surjective, and its kernel — the endomorphisms of `F` with image
inside `IF` — is nil: when `Iⁿ = 0` the `n`-th power of such an endomorphism has image inside
`IⁿF = 0`, and when `I` is only locally nilpotent but `F` is finite, the image lies in `JF` for a
finitely generated, hence nilpotent, ideal `J ⊆ I`. So `e` lifts to a genuine idempotent `p` of
`End_R(F)` (Mathlib's `exists_isIdempotentElem_eq_of_ker_isNilpotent`), and `P = im p` is a
direct summand of `F`, hence projective, with `P/IP ≅ Q`.

## Main results

* `Module.exists_projective_quotient_smul_top_linearEquiv_of_isNilpotent`: Stacks 07LV.
* `lift_finite_projective_of_locallyNilpotent`: Stacks 0D47.
* `projective_of_projective_quotient_inter_zero`: Stacks 0H7M.

## Implementation notes

The isomorphism `P/IP ≅ Q` is proved formally rather than by comparing the two direct sum
decompositions: the inclusion `ι : P → F` and the retraction `ρ : F → P` cut out by `p` satisfy
`ρ ∘ ι = id` and `ι ∘ ρ = p`, so their reductions satisfy `ρ̄ ∘ ι̅ = id` and `ι̅ ∘ ρ̄ = s ∘ π`, and
`π ∘ ι̅` and `ρ̄ ∘ s` are mutually inverse by four rewrites. This is `rangeQuotEquivOfSplit`.

`reduceModIdeal` is `LinearMap.reduceModIdeal` for a two-sided ideal of a possibly
noncommutative ring: Mathlib's version is stated over a `CommRing`, where the reduction is
moreover linear in the map, which is meaningless here because `M →ₗ[R] N` carries no `R`-action.
Only its additivity is needed, in the form of the ring homomorphism `reduceEndHom` on
endomorphism rings, which is what an idempotent gets lifted along.

Stacks 07LV is stated in the source for a commutative ring, but neither the statement nor its
proof uses commutativity, so it is stated for a ring `R` and a two-sided ideal `I`. The lifted
module is produced together with its algebraic structure, as an existential over a type in
`Type (max u v)`, because it is a direct summand of the free `R`-module on `Q`. Nilpotency of `I`
cannot be dropped: for `R = ℤ` and `I = (6)` the `ℤ ⧸ 6ℤ`-module `ℤ ⧸ 2ℤ` is projective, while a
projective — hence free — `ℤ`-module `P` has `P/6P` of cardinality a power of `6`, or infinite.

## References

* [StacksProject 07LV](https://stacks.math.columbia.edu/tag/07LV)
* [StacksProject 0D47](https://stacks.math.columbia.edu/tag/0D47)
* [StacksProject 0H7M](https://stacks.math.columbia.edu/tag/0H7M)

## Tags

projective module, nilpotent ideal, lifting idempotents
-/

/-! ## Reduction of endomorphisms modulo a two-sided ideal -/

section Reduction

variable {R : Type*} [Ring R] {I : Ideal R} [I.IsTwoSided]
  {M : Type*} [AddCommGroup M] [Module R M]
  {N : Type*} [AddCommGroup N] [Module R N]
  {P : Type*} [AddCommGroup P] [Module R P]

/-- On `M ⧸ I • ⊤` the class of `r` acts as `r` does. -/
private theorem mk_smul (r : R) (x : M ⧸ I • (⊤ : Submodule R M)) :
    Ideal.Quotient.mk I r • x = r • x := rfl

omit [I.IsTwoSided] in
private theorem map_smul_top_le (f : M →ₗ[R] N) :
    Submodule.map f (I • (⊤ : Submodule R M)) ≤ I • (⊤ : Submodule R N) := by
  rw [Submodule.map_smul'']
  exact smul_mono_right _ le_top

/-- The `R ⧸ I`-linear map `M/IM → N/IN` induced by an `R`-linear map `f : M → N`. This is
`LinearMap.reduceModIdeal` for a two-sided ideal of a possibly noncommutative ring. -/
private def reduceModIdeal (f : M →ₗ[R] N) :
    (M ⧸ I • (⊤ : Submodule R M)) →ₗ[R ⧸ I] N ⧸ I • (⊤ : Submodule R N) where
  toFun := Submodule.mapQ _ _ f (Submodule.map_le_iff_le_comap.mp (map_smul_top_le f))
  map_add' := map_add _
  map_smul' c x := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact (Submodule.mapQ _ _ f (Submodule.map_le_iff_le_comap.mp (map_smul_top_le f))).map_smul r x

private theorem reduceModIdeal_mk (f : M →ₗ[R] N) (x : M) :
    reduceModIdeal (I := I) f (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (f x) : N ⧸ I • (⊤ : Submodule R N)) := rfl

private theorem reduceModIdeal_id :
    reduceModIdeal (I := I) (LinearMap.id : M →ₗ[R] M) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

private theorem reduceModIdeal_comp (g : N →ₗ[R] P) (f : M →ₗ[R] N) :
    reduceModIdeal (I := I) (g ∘ₗ f) = reduceModIdeal g ∘ₗ reduceModIdeal f := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

private theorem reduceModIdeal_surjective {f : M →ₗ[R] N} (hf : Function.Surjective f) :
    Function.Surjective (reduceModIdeal (I := I) f) := by
  intro y
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨w, rfl⟩ := hf v
  exact ⟨Submodule.Quotient.mk w, rfl⟩

private theorem reduceModIdeal_add (f g : M →ₗ[R] N) :
    reduceModIdeal (I := I) (f + g) = reduceModIdeal f + reduceModIdeal g := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

/-- Reduction modulo `I` as a ring homomorphism `End_R(M) → End_{R ⧸ I}(M/IM)`. -/
private def reduceEndHom (I : Ideal R) [I.IsTwoSided] (M : Type*) [AddCommGroup M] [Module R M] :
    Module.End R M →+* Module.End (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) where
  toFun f := reduceModIdeal f
  map_one' := reduceModIdeal_id
  map_mul' f g := reduceModIdeal_comp f g
  map_zero' := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rfl
  map_add' f g := reduceModIdeal_add f g

private theorem reduceEndHom_apply (f : Module.End R M) :
    reduceEndHom I M f = reduceModIdeal f := rfl

end Reduction

section Nilpotent

variable {R : Type*} [Ring R] {I : Ideal R} {M : Type*} [AddCommGroup M] [Module R M]

/-- An endomorphism with image inside `I • ⊤` has `k`-th power with image inside `I ^ k • ⊤`. -/
private theorem range_pow_le (φ : Module.End R M)
    (h : LinearMap.range φ ≤ I • (⊤ : Submodule R M)) (k : ℕ) :
    LinearMap.range (φ ^ k) ≤ I ^ k • (⊤ : Submodule R M) := by
  induction k with
  | zero => rw [pow_zero, Submodule.pow_zero, Ideal.one_eq_top, Submodule.top_smul]; exact le_top
  | succ k ih =>
    have hcomp : φ ^ (k + 1) = φ ∘ₗ (φ ^ k) := by rw [pow_succ']; rfl
    rw [hcomp, LinearMap.range_comp]
    calc Submodule.map φ (LinearMap.range (φ ^ k))
        ≤ Submodule.map φ (I ^ k • (⊤ : Submodule R M)) := Submodule.map_mono ih
      _ = I ^ k • Submodule.map φ ⊤ := Submodule.map_smul'' _ _ _
      _ = I ^ k • LinearMap.range φ := by rw [Submodule.map_top]
      _ ≤ I ^ k • (I • (⊤ : Submodule R M)) := smul_mono_right _ h
      _ = (I ^ k * I) • (⊤ : Submodule R M) := (Submodule.smul_assoc _ _ _).symm
      _ = I ^ (k + 1) • (⊤ : Submodule R M) := rfl

/-- An endomorphism with image inside `I • ⊤` is nilpotent when `I ^ n = 0`. -/
private theorem isNilpotent_of_range_le {n : ℕ} (hn : I ^ n = ⊥) (φ : Module.End R M)
    (h : LinearMap.range φ ≤ I • (⊤ : Submodule R M)) : IsNilpotent φ := by
  refine ⟨n, LinearMap.range_eq_bot.mp (le_bot_iff.mp ?_)⟩
  simpa [hn] using range_pow_le φ h n

/-- An endomorphism of a finite module over a commutative ring with image inside `I • ⊤` is
nilpotent when `I` is locally nilpotent: its image lies in `J • ⊤` for the finitely generated
ideal `J ⊆ I` generated by the coefficients expressing the images of a finite generating family,
and such a `J` is nilpotent. -/
private theorem isNilpotent_of_range_le_of_isLocallyNilpotent {R : Type*} [CommRing R]
    {I : Ideal R} (hI : I.IsLocallyNilpotent) {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (φ : Module.End R M) (h : LinearMap.range φ ≤ I • (⊤ : Submodule R M)) :
    IsNilpotent φ := by
  classical
  obtain ⟨k, v, hv⟩ := Module.Finite.exists_fin (R := R) (M := M)
  have hmem : ∀ j, φ (v j) ∈ I • Submodule.span R (Set.range v) := fun j => by
    rw [hv]
    exact h ⟨v j, rfl⟩
  choose a haI hsum using fun j => (Submodule.mem_ideal_smul_span_iff_exists_sum I v _).mp (hmem j)
  set J : Ideal R := Ideal.span (Set.range fun q : Fin k × Fin k => a q.1 q.2)
  have hJ : IsNilpotent J := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical (Submodule.fg_span (Set.finite_range _))).mpr ?_
    rw [Ideal.span_le]
    rintro _ ⟨q, rfl⟩
    exact hI _ (haI q.1 q.2)
  obtain ⟨n, hn⟩ := hJ
  refine isNilpotent_of_range_le hn φ ?_
  rw [LinearMap.range_eq_map, ← hv, Submodule.map_span, Submodule.span_le, ← Set.range_comp]
  rintro _ ⟨j, rfl⟩
  rw [SetLike.mem_coe, Function.comp_apply]
  exact (Submodule.mem_ideal_smul_span_iff_exists_sum J v _).mpr
    ⟨a j, fun i => Ideal.subset_span ⟨(j, i), rfl⟩, hsum j⟩

end Nilpotent

section Lifting

variable {R : Type*} [Ring R] {I : Ideal R} [I.IsTwoSided]
  {F : Type*} [AddCommGroup F] [Module R F]

/-- Every endomorphism of `F/IF` is the reduction of an endomorphism of `F`, when `F` is
projective. -/
private theorem reduceEndHom_surjective [Module.Projective R F] :
    Function.Surjective (reduceEndHom I F) := by
  intro e
  let g : F →ₗ[R] (F ⧸ I • (⊤ : Submodule R F)) :=
    { toFun := fun x => e (Submodule.Quotient.mk x)
      map_add' := fun x y => map_add e (Submodule.Quotient.mk x) (Submodule.Quotient.mk y)
      map_smul' := fun r x => e.map_smul (Ideal.Quotient.mk I r) (Submodule.Quotient.mk x) }
  obtain ⟨p, hp⟩ :=
    Module.projective_lifting_property (Submodule.mkQ _) g (Submodule.mkQ_surjective _)
  refine ⟨p, LinearMap.ext fun x => ?_⟩
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact DFunLike.congr_fun hp y

/-- **Lifting a projector along a nil kernel.** If `F` is a projective `R`-module and every
endomorphism of `F` with image inside `IF` is nilpotent, every idempotent of `End_{R ⧸ I}(F/IF)`
is the reduction of an idempotent of `End_R(F)`. -/
private theorem exists_isIdempotentElem_reduceEndHom_eq [Module.Projective R F]
    (hnil : ∀ φ : Module.End R F, LinearMap.range φ ≤ I • (⊤ : Submodule R F) → IsNilpotent φ)
    {e : Module.End (R ⧸ I) (F ⧸ I • (⊤ : Submodule R F))} (he : IsIdempotentElem e) :
    ∃ p : Module.End R F, IsIdempotentElem p ∧ reduceEndHom I F p = e := by
  refine exists_isIdempotentElem_eq_of_ker_isNilpotent (reduceEndHom I F) (fun φ hφ => ?_) e
    (reduceEndHom_surjective e) he
  refine hnil φ ?_
  rintro y ⟨x, rfl⟩
  refine (Submodule.Quotient.mk_eq_zero _).mp ?_
  have h0 : reduceModIdeal (I := I) φ = 0 := RingHom.mem_ker.mp hφ
  exact (reduceModIdeal_mk (I := I) φ x).symm.trans (LinearMap.congr_fun h0 _)

end Lifting

section Summand

variable {R : Type*} [Ring R] {I : Ideal R} [I.IsTwoSided]
  {F : Type*} [AddCommGroup F] [Module R F] {Q : Type*} [AddCommGroup Q] [Module (R ⧸ I) Q]

/-- The retraction onto the image of an idempotent endomorphism splits the inclusion. -/
private theorem rangeRestrict_comp_subtype_of_isIdempotentElem {p : Module.End R F}
    (hp : IsIdempotentElem p) :
    p.rangeRestrict ∘ₗ (LinearMap.range p).subtype = LinearMap.id :=
  LinearMap.ext fun x =>
    Subtype.ext ((LinearMap.IsIdempotentElem.isProj_range p hp).map_id x.1 x.2)

/-- The image of an idempotent endomorphism of a projective module is projective. -/
private theorem projective_range_of_isIdempotentElem [Module.Projective R F]
    {p : Module.End R F} (hp : IsIdempotentElem p) :
    Module.Projective R (LinearMap.range p) :=
  Module.Projective.of_split (LinearMap.range p).subtype p.rangeRestrict
    (rangeRestrict_comp_subtype_of_isIdempotentElem hp)

/-- **The summand cut out by a projector reduces to the summand cut out by its reduction.** If
`p` is an idempotent endomorphism of `F` whose reduction is split as `s ∘ π` by a pair of maps
between `F/IF` and `Q`, then `(im p)/I(im p) ≅ Q`. -/
private noncomputable def rangeQuotEquivOfSplit {p : Module.End R F} (hp : IsIdempotentElem p)
    (s : Q →ₗ[R ⧸ I] F ⧸ I • (⊤ : Submodule R F))
    (π : (F ⧸ I • (⊤ : Submodule R F)) →ₗ[R ⧸ I] Q) (hsπ : π ∘ₗ s = LinearMap.id)
    (hps : s ∘ₗ π = reduceEndHom I F p) :
    (LinearMap.range p ⧸ I • (⊤ : Submodule R (LinearMap.range p))) ≃ₗ[R ⧸ I] Q := by
  have hρι := rangeRestrict_comp_subtype_of_isIdempotentElem hp
  have hιρ : (LinearMap.range p).subtype ∘ₗ p.rangeRestrict = p := rfl
  have key : ∀ x, reduceModIdeal (LinearMap.range p).subtype (reduceModIdeal p.rangeRestrict x) =
      s (π x) := fun x => LinearMap.congr_fun
    (((reduceModIdeal_comp (I := I) _ _).symm.trans (by rw [hιρ, reduceEndHom_apply])).trans
      hps.symm) x
  have key' : ∀ x, reduceModIdeal p.rangeRestrict
      (reduceModIdeal (I := I) (LinearMap.range p).subtype x) = x := fun x =>
    LinearMap.congr_fun (((reduceModIdeal_comp (I := I) _ _).symm.trans
      (by rw [hρι, reduceModIdeal_id])) : _ = LinearMap.id) x
  have hsπ' : ∀ q, π (s q) = q := LinearMap.congr_fun hsπ
  refine LinearEquiv.ofLinearMap (π ∘ₗ reduceModIdeal (LinearMap.range p).subtype)
    (reduceModIdeal p.rangeRestrict ∘ₗ s) (LinearMap.ext fun q => ?_) (LinearMap.ext fun y => ?_)
  · change π (reduceModIdeal _ (reduceModIdeal _ (s q))) = q
    rw [key, hsπ', hsπ']
  · change reduceModIdeal _ (s (π (reduceModIdeal _ y))) = y
    rw [← key, key', key']

end Summand

/-! ## The lifting argument -/

section Construction

variable {R : Type*} [Ring R] {I : Ideal R} [I.IsTwoSided]
  {Q : Type*} [AddCommGroup Q] [Module (R ⧸ I) Q]

/-- A family `s` spanning the `R ⧸ I`-module `Q` gives a surjection `(ι →₀ R)/I(ι →₀ R) ↠ Q`,
the reduction of the tautological map `ι →₀ R → Q` sending the basis vector `i` to `s i`. -/
private theorem exists_surjective_of_span {ι : Type*} (s : ι → Q)
    (hs : Submodule.span (R ⧸ I) (Set.range s) = ⊤) :
    ∃ π : ((ι →₀ R) ⧸ I • (⊤ : Submodule R (ι →₀ R))) →ₗ[R ⧸ I] Q, Function.Surjective π := by
  -- `Q` is an `R`-module through `R → R ⧸ I`
  let _ : Module R Q := Module.compHom Q (Ideal.Quotient.mk I)
  have hQ : ∀ (r : R) (q : Q), Ideal.Quotient.mk I r • q = r • q := fun _ _ => rfl
  let π₀ : (ι →₀ R) →ₗ[R] Q := Finsupp.linearCombination R s
  have hker : I • (⊤ : Submodule R (ι →₀ R)) ≤ LinearMap.ker π₀ := by
    intro x hx
    refine Submodule.smul_induction_on hx (fun r hr y _ => ?_)
      (fun a b ha hb => (LinearMap.ker π₀).add_mem ha hb)
    simp only [LinearMap.mem_ker, map_smul]
    rw [← hQ, Ideal.Quotient.eq_zero_iff_mem.mpr hr, zero_smul]
  let π : ((ι →₀ R) ⧸ I • (⊤ : Submodule R (ι →₀ R))) →ₗ[R ⧸ I] Q :=
    { toFun := Submodule.liftQ _ π₀ hker
      map_add' := map_add _
      map_smul' := fun c x => by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        exact (Submodule.liftQ _ π₀ hker).map_smul r x }
  refine ⟨π, LinearMap.range_eq_top.mp (top_le_iff.mp (hs ▸ Submodule.span_le.mpr ?_))⟩
  rintro _ ⟨i, rfl⟩
  exact ⟨Submodule.Quotient.mk (Finsupp.single i 1), by simp [π, π₀]⟩

/-- **The lifting argument.** Let `F` be a projective `R`-module such that every endomorphism of
`F` with image inside `IF` is nilpotent, and let `π : F/IF ↠ Q` be a surjection onto a projective
`R ⧸ I`-module. Then there is an idempotent `p` of `End_R(F)` with `(im p)/I(im p) ≅ Q`. -/
private theorem exists_isIdempotentElem_rangeQuotEquiv [Module.Projective (R ⧸ I) Q]
    {F : Type*} [AddCommGroup F] [Module R F] [Module.Projective R F]
    (hnil : ∀ φ : Module.End R F, LinearMap.range φ ≤ I • (⊤ : Submodule R F) → IsNilpotent φ)
    (π : (F ⧸ I • (⊤ : Submodule R F)) →ₗ[R ⧸ I] Q) (hπ : Function.Surjective π) :
    ∃ p : Module.End R F, IsIdempotentElem p ∧
      Nonempty ((LinearMap.range p ⧸ I • (⊤ : Submodule R (LinearMap.range p))) ≃ₗ[R ⧸ I] Q) := by
  -- projectivity of `Q` splits `π`, giving a projector of `F/IF` with image `Q`
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  have hsπ : ∀ q, π (s q) = q := LinearMap.congr_fun hs
  have hidem : IsIdempotentElem (s ∘ₗ π) := by
    refine LinearMap.ext fun x => ?_
    simp only [Module.End.mul_apply, LinearMap.comp_apply, hsπ]
  -- which lifts to a projector of `F` because the kernel of the reduction is nil
  obtain ⟨p, hp, hpe⟩ := exists_isIdempotentElem_reduceEndHom_eq hnil hidem
  exact ⟨p, hp, ⟨rangeQuotEquivOfSplit hp s π hs hpe.symm⟩⟩

end Construction

/-- **Stacks 07LV.** Let `R` be a ring, let `I ⊆ R` be a nilpotent two-sided ideal and let `Q` be
a projective `R ⧸ I`-module. Then there is a projective `R`-module `P` together with an
isomorphism `P/IP ≅ Q` of `R ⧸ I`-modules. -/
@[stacks 07LV, sga "5 XV 3.Lemma3" "(ii), existence"]
public theorem Module.exists_projective_quotient_smul_top_linearEquiv_of_isNilpotent
    {R : Type u} [Ring R] {I : Ideal R} [I.IsTwoSided] {Q : Type v} [AddCommGroup Q]
    [Module (R ⧸ I) Q] [Module.Projective (R ⧸ I) Q] (hI : IsNilpotent I) :
    ∃ (P : Type (max u v)) (_ : AddCommGroup P) (_ : Module R P),
      Module.Projective R P ∧ Nonempty ((P ⧸ I • (⊤ : Submodule R P)) ≃ₗ[R ⧸ I] Q) := by
  obtain ⟨n, hn⟩ := hI
  obtain ⟨π, hπ⟩ := exists_surjective_of_span (I := I) (id : Q → Q) (by simp)
  obtain ⟨p, hp, he⟩ :=
    exists_isIdempotentElem_rangeQuotEquiv (fun φ => isNilpotent_of_range_le hn φ) π hπ
  exact ⟨LinearMap.range p, inferInstance, inferInstance, projective_range_of_isIdempotentElem hp,
    he⟩

/-- **Stacks Tag 0D47 (Lemma 10.77.6).**
Let `R` be a commutative ring and `I ⊆ R` a locally nilpotent ideal. Let `Pbar` be a
finite projective `R/I`-module. Then there exists a finite projective `R`-module `P`
together with an isomorphism of `R/I`-modules `P / I P ≅ Pbar`. -/
@[stacks 0D47, sga "5 XV 3.Lemma3" "(ii) existence, finite"]
theorem lift_finite_projective_of_locallyNilpotent
    {R : Type u} [CommRing R] (I : Ideal R)
    (hI : I.IsLocallyNilpotent)
    (Pbar : Type u) [AddCommGroup Pbar] [Module (R ⧸ I) Pbar]
    [Module.Finite (R ⧸ I) Pbar] [Module.Projective (R ⧸ I) Pbar] :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module R P),
      Module.Finite R P ∧ Module.Projective R P ∧
      Nonempty ((P ⧸ (I • (⊤ : Submodule R P))) ≃ₗ[R ⧸ I] Pbar) := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R ⧸ I) (M := Pbar)
  obtain ⟨π, hπ⟩ := exists_surjective_of_span s hs
  obtain ⟨p, hp, he⟩ := exists_isIdempotentElem_rangeQuotEquiv
    (fun φ => isNilpotent_of_range_le_of_isLocallyNilpotent hI φ) π hπ
  exact ⟨LinearMap.range p, inferInstance, inferInstance, Module.Finite.range p,
    projective_range_of_isIdempotentElem hp, he⟩

/-! ## Stacks 0H7M: projectivity from projectivity modulo two ideals with zero intersection

Fix the free module `F = P →₀ R` with its canonical surjection `p : F →ₗ[R] P`, namely
`Finsupp.linearCombination R id`. The whole proof reduces to producing an `R`-linear map
`h : P →ₗ[R] F` such that, writing `a := p ∘ₗ h`, for every `x : P`

  (1) `x - a x ∈ I • ⊤`  and  (2) `x - a x ∈ J • ⊤`.

Given such an `h`, set `b := id - a : P →ₗ[R] P`, so that (1) says `b x ∈ I • ⊤` and (2) says
`b x ∈ J • ⊤`. Then `b ∘ b` lands in `(J * I) • ⊤ ⊆ (I ⊓ J) • ⊤ = ⊥`, so `b ∘ b = 0`; hence
`a = id - b` is invertible with inverse `id + b`, and `p ∘ₗ (h ∘ₗ (id + b)) = id`. Therefore
`P` is a retract of the free, hence projective, module `F`, so `P` is projective.

The heart of the matter is the existence of `h`, which is `exists_lift_id_mod_I_and_J`. Its
proof is the Stacks gluing argument, and is in turn decomposed into `exists_section_mod`,
which sections the surjection `F/KF → P/KP` using projectivity of `P/KP`, and
`free_glue_of_inf_eq_bot`, the fibre-product (Mayer–Vietoris) isomorphism
`F ≅ F/JF ×_{F/(I+J)F} F/IF`, valid for free `F` when `I ⊓ J = ⊥`.
-/

open Classical in
/-- Sectioning a quotient surjection using projectivity. For an ideal `K` with `P/KP`
projective over `R/K`, the canonical `R/K`-linear surjection `p̄K : F/KF → P/KP` induced by a
surjection `p : F →ₗ[R] P` admits an `R/K`-linear section. Composing that section with the
projection `P → P/KP` gives an `R`-linear map `σ : P →ₗ[R] F/KF` lifting the identity of
`P/KP`, i.e. `p̄K (σ x) = [x]_K` for every `x : P`.

Note that `σ` lands in the *quotient* `F/KF` and not in `F`: an honest lift to `F` need not
exist for a single ideal `K`, which is exactly why both `I` and `J` are needed, and is handled
by the gluing lemma `exists_lift_id_mod_I_and_J`.

The argument runs as follows.
* Since `p : F →ₗ[R] P` is surjective, so is the induced `R/K`-linear map
  `p̄K := Submodule.mapQ (K•⊤_F) (K•⊤_P) p _ : F/KF → P/KP`: it hits every `[p w]`, and `[v]`
  for `v : P` is `[p w]` for any `w` with `p w = v`.
* Since `P/KP` is projective over `R/K`, the lifting property applied to the surjection `p̄K`
  and the identity `P/KP → P/KP` gives an `R/K`-linear `s : P/KP →ₗ[R/K] F/KF` with
  `p̄K ∘ₗ s = id`.
* Restricting scalars of `s` to `R` and precomposing with the `R`-linear projection
  `mkQ_P : P → P/KP` gives `σ := (s.restrictScalars R) ∘ₗ (Submodule.mkQ _)`, which satisfies
  `p̄K (σ x) = p̄K (s [x]) = [x]`. -/
private theorem exists_section_mod
    (R : Type*) [CommRing R] (K : Ideal R)
    (P : Type*) [AddCommGroup P] [Module R P]
    (F : Type*) [AddCommGroup F] [Module R F]
    (p : F →ₗ[R] P) (hp : Function.Surjective p)
    (hK : Module.Projective (R ⧸ K) (P ⧸ (K • (⊤ : Submodule R P)))) :
    ∃ σ : P →ₗ[R] (F ⧸ (K • (⊤ : Submodule R F))),
      ∀ x : P, (Submodule.mapQ (K • (⊤ : Submodule R F)) (K • (⊤ : Submodule R P)) p
                  (Submodule.map_le_iff_le_comap.mp (map_smul_top_le p))) (σ x)
                = Submodule.mkQ (K • (⊤ : Submodule R P)) x := by
  -- Build `p̄ = mapQ ... p` and show it is surjective; the lifting property over `R ⧸ K` then
  -- gives `s` with `p̄ ∘ s = id`, and `σ = s ∘ₗ mkQ_P` restricted to `R`-scalars is the
  -- required section.
  set KF := K • (⊤ : Submodule R F)
  set KP := K • (⊤ : Submodule R P)
  let pbar : (F ⧸ KF) →ₗ[R ⧸ K] (P ⧸ KP) := reduceModIdeal p
  have hpbar_surj : Function.Surjective pbar := reduceModIdeal_surjective hp
  obtain ⟨s, hs⟩ := Module.projective_lifting_property pbar LinearMap.id hpbar_surj
  exact ⟨s.restrictScalars R ∘ₗ Submodule.mkQ KP,
    fun x => LinearMap.congr_fun hs (Submodule.mkQ KP x)⟩

open Classical in
/-- The gluing half of the free Mayer–Vietoris (fibre-product) isomorphism. If `F` is a free
`R`-module and `I ⊓ J = ⊥`, the canonical `R`-linear map `F → (F/IF) ×[F/(I+J)F] (F/JF)` into
the fibre product is an isomorphism: for any `aI : F/IF` and `aJ : F/JF` having the same image
in `F/(I+J)F` there is a unique `w : F` with `mkQ_I w = aI` and `mkQ_J w = aJ`.

Injectivity is the statement that the kernel `IF ⊓ JF` of `F → F/IF × F/JF` vanishes: for free
`F = R^{(B)}` one has `IF = I^{(B)}` and `JF = J^{(B)}`, so
`IF ⊓ JF = (I ⊓ J)^{(B)} = ⊥`. This is the only place freeness is used, and it is recorded
separately as `inf_smul_top_eq_bot`.

Surjectivity is what is proved here, and it needs no hypothesis on `I + J`. Given `aI` and `aJ`
agreeing in `F/(I+J)F`, lift them to `wI, wJ : F` with `mkQ_I wI = aI` and `mkQ_J wJ = aJ`.
Agreement means `wI - wJ ∈ (I+J)F = IF + JF`, since `(I+J) • ⊤ = I • ⊤ + J • ⊤`. Write
`wI - wJ = u + v` with `u ∈ IF` and `v ∈ JF`, and put `w := wI - u = wJ + v`. Then
`w ≡ wI (mod IF)`, so `mkQ_I w = aI`, and `w ≡ wJ (mod JF)`, so `mkQ_J w = aJ`. -/
private theorem free_glue_of_inf_eq_bot
    (R : Type*) [CommRing R] (I J : Ideal R)
    (F : Type*) [AddCommGroup F] [Module R F]
    (aI aJ : F)
    (hagree : aI - aJ ∈ (I • (⊤ : Submodule R F)) + (J • (⊤ : Submodule R F))) :
    ∃ w : F, w - aI ∈ I • (⊤ : Submodule R F) ∧ w - aJ ∈ J • (⊤ : Submodule R F) := by
  rw [Submodule.add_eq_sup, Submodule.mem_sup] at hagree
  obtain ⟨u, hu, v, hv, huv⟩ := hagree
  refine ⟨aI - u, ?_, ?_⟩
  · rw [show (aI - u) - aI = -u by abel]
    exact (I • (⊤ : Submodule R F)).neg_mem hu
  · rw [show (aI - u) - aJ = v by rw [sub_right_comm, ← huv]; abel]
    exact hv

open Classical in
/-- For a free `R`-module `F` and ideals with `I ⊓ J = ⊥`, one has `(I • ⊤) ⊓ (J • ⊤) = ⊥` in
`F`. This is the injectivity, or uniqueness, half of `free_glue_of_inf_eq_bot`, and it is where
freeness of `F` is used.

Since `F` is free, `F ≅ R^{(B)}` and `K • ⊤_F ≅ K^{(B)}` coordinatewise for any ideal `K`.
Intersections are computed coordinatewise, so `(I • ⊤) ⊓ (J • ⊤) ≅ (I ⊓ J)^{(B)} = ⊥`. Written
out in terms of a basis of `F`, membership in `K • ⊤` implies that each coordinate lies in
`K`. -/
private theorem inf_smul_top_eq_bot
    (R : Type*) [CommRing R] (I J : Ideal R) (hIJ : I ⊓ J = ⊥)
    (F : Type*) [AddCommGroup F] [Module R F] [Module.Free R F] :
    (I • (⊤ : Submodule R F)) ⊓ (J • (⊤ : Submodule R F)) = ⊥ := by
  -- Work in the coordinates of a chosen basis of `F`: membership in `K • ⊤` forces every
  -- coordinate to lie in `K`, so an element of `(I • ⊤) ⊓ (J • ⊤)` has all coordinates in
  -- `I ⊓ J = ⊥` and is therefore zero.
  classical
  set b := Module.Free.chooseBasis R F with hb
  have key : ∀ (K : Ideal R) (x : F), x ∈ K • (⊤ : Submodule R F) →
      ∀ i, b.repr x i ∈ K := by
    intro K x hx i
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr n hn
      rw [map_smul, Finsupp.smul_apply]
      exact Ideal.mul_mem_right _ _ hr
    · intro y z hy hz
      rw [map_add, Finsupp.add_apply]
      exact Ideal.add_mem _ hy hz
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxI, hxJ⟩ := hx
  rw [Submodule.mem_bot]
  apply b.ext_elem
  intro i
  rw [map_zero, Finsupp.zero_apply]
  have hI : b.repr x i ∈ I := key I x hxI i
  have hJ : b.repr x i ∈ J := key J x hxJ i
  have hmem : b.repr x i ∈ I ⊓ J := ⟨hI, hJ⟩
  rw [hIJ] at hmem
  rwa [Ideal.mem_bot] at hmem

open Classical in
/-- The adjustment step, which is the analytic heart of the gluing. Given a section `σI` of the
surjection `p` modulo `I`, projectivity of `P/JP` over `R/J` yields a section `σJ` modulo `J`
that *agrees with `σI` modulo `I+J`*: for every `x` there are lifts `wI` of `σI x` and `wJ` of
`σJ x` to `F` with `wI - wJ ∈ I • ⊤ + J • ⊤`.

This is the Stacks step of lifting `g : P/JP → F/JF` through the fibre product `q`, using
projectivity of `P/JP`, so as to agree with `f` modulo `I+J`.

The proof is carried out over the base ring `S = R ⧸ J`, using the `S`-modules `F̄ = F/JF` and
`P̄ = P/JP` together with their further quotients `G = F̄/(Ī • ⊤)` and `Q = P̄/(Ī • ⊤)`, where
`Ī = I.map (Quotient.mk J)`. These form the fibre product `T = G ×_Q P̄`, and `δ : P̄ → T` is
lifted through the surjection `q : F̄ → T` using projectivity of `P̄`. No hypothesis on
`I ⊓ J` is needed for this step. -/
private theorem exists_section_mod_agree
    (R : Type*) [CommRing R] (I J : Ideal R)
    (P : Type*) [AddCommGroup P] [Module R P]
    (F : Type*) [AddCommGroup F] [Module R F]
    (p : F →ₗ[R] P) (hp : Function.Surjective p)
    (hJ : Module.Projective (R ⧸ J) (P ⧸ (J • (⊤ : Submodule R P))))
    (hpsubI : I • (⊤ : Submodule R F) ≤ Submodule.comap p (I • (⊤ : Submodule R P)))
    (hpsubJ : J • (⊤ : Submodule R F) ≤ Submodule.comap p (J • (⊤ : Submodule R P)))
    (σI : P →ₗ[R] (F ⧸ (I • (⊤ : Submodule R F))))
    (hσI : ∀ x, (Submodule.mapQ (I • (⊤ : Submodule R F)) (I • (⊤ : Submodule R P)) p hpsubI) (σI x)
              = Submodule.mkQ (I • (⊤ : Submodule R P)) x) :
    ∃ σJ : P →ₗ[R] (F ⧸ (J • (⊤ : Submodule R F))),
      (∀ x, (Submodule.mapQ (J • (⊤ : Submodule R F)) (J • (⊤ : Submodule R P)) p hpsubJ) (σJ x)
            = Submodule.mkQ (J • (⊤ : Submodule R P)) x) ∧
      (∀ x, ∃ wI wJ : F,
        Submodule.mkQ (I • (⊤ : Submodule R F)) wI = σI x ∧
        Submodule.mkQ (J • (⊤ : Submodule R F)) wJ = σJ x ∧
        wI - wJ ∈ (I • (⊤ : Submodule R F)) + (J • (⊤ : Submodule R F))) := by
  set Fbar := F ⧸ (J • (⊤ : Submodule R F)) with hFbar
  set Pbar := P ⧸ (J • (⊤ : Submodule R P)) with hPbar
  set Ibar : Ideal (R ⧸ J) := I.map (Ideal.Quotient.mk J) with hIbar
  set NF : Submodule (R ⧸ J) Fbar := Ibar • (⊤ : Submodule (R ⧸ J) Fbar) with hNF
  set NP : Submodule (R ⧸ J) Pbar := Ibar • (⊤ : Submodule (R ⧸ J) Pbar) with hNP
  set G := Fbar ⧸ NF with hG
  set Q := Pbar ⧸ NP with hQ
  -- R/J-linear surjection p̄ : F̄ → P̄.
  let pbar : Fbar →ₗ[R ⧸ J] Pbar := reduceModIdeal p
  have hpbar_apply : ∀ w : F, pbar (Submodule.mkQ _ w) = Submodule.mkQ _ (p w) := fun w => rfl
  have hpbar_surj : Function.Surjective pbar := reduceModIdeal_surjective hp
  let etaF : Fbar →ₗ[R ⧸ J] G := Submodule.mkQ NF
  let etaP : Pbar →ₗ[R ⧸ J] Q := Submodule.mkQ NP
  -- `pbar` carries `NF` into `NP`, so it descends to `p̄G : G → Q`: it is `R/J`-linear and
  -- `Ī • ⊤` is `Ī` times everything, so `pbar (Ī • ⊤) ⊆ Ī • ⊤`.
  have hmap : NP = Submodule.map pbar NF := by
    rw [hNP, hNF, Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hpbar_surj]
  have hpbarN : NF ≤ Submodule.comap pbar NP := Submodule.map_le_iff_le_comap.mp hmap.ge
  let pbarG : G →ₗ[R ⧸ J] Q := Submodule.mapQ NF NP pbar hpbarN
  -- Fibre product T = ker(pbarG∘fst - etaP∘snd) ≤ G × P̄.
  let Tmap : (G × Pbar) →ₗ[R ⧸ J] Q :=
    pbarG ∘ₗ (LinearMap.fst (R ⧸ J) G Pbar) - etaP ∘ₗ (LinearMap.snd (R ⧸ J) G Pbar)
  set T : Submodule (R ⧸ J) (G × Pbar) := LinearMap.ker Tmap with hT
  -- Naturality: `pbarG (etaF w) = etaP (pbar w)`, i.e. `(etaF w, pbar w) ∈ T`. Since `pbarG`,
  -- `etaF` and `etaP` are all `mapQ`/`mkQ` maps, `pbarG (mkQ w) = mkQ (pbar w)` holds by
  -- definitional unfolding.
  have hqmem : ∀ w : Fbar, (etaF w, pbar w) ∈ T := by
    intro w
    rw [hT, LinearMap.mem_ker]
    change (pbarG ∘ₗ (LinearMap.fst (R ⧸ J) G Pbar) - etaP ∘ₗ (LinearMap.snd (R ⧸ J) G Pbar))
        (etaF w, pbar w) = 0
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
      LinearMap.snd_apply, sub_eq_zero]
    rfl
  let q : Fbar →ₗ[R ⧸ J] T := LinearMap.codRestrict T ((etaF).prod pbar) hqmem
  -- `q` is surjective, which is the main computation. Given `(c, y) ∈ T`, pick `w₀` with
  -- `etaF w₀ = c`, possible as `etaF` is a quotient map. Then `y - pbar w₀ ∈ ker etaP = NP`,
  -- which is `Ī • ⊤`, so it is a finite sum `Σ ρ(aₖ) • ȳₖ`; lifting each `ȳₖ` along `pbar`
  -- and setting `w := w₀ + Σ ρ(aₖ) • w̄ₖ` gives `pbar w = y` and `etaF w = c`, because each
  -- `ρ(aₖ)` lies in `Ī` and hence kills `G`.
  have hq_surj : Function.Surjective q := by
    rintro ⟨⟨c, y⟩, ht⟩
    -- ht : Tmap (c, y) = 0, i.e. pbarG c = etaP y
    have hcy : pbarG c = etaP y := by
      rw [LinearMap.mem_ker] at ht
      simpa only [Tmap, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply,
        LinearMap.snd_apply, sub_eq_zero] using ht
    -- Step 1: etaF surjective
    obtain ⟨w₀, hw₀⟩ := Submodule.mkQ_surjective NF c
    -- Step 2: etaP (y - pbar w₀) = 0
    have hpbarG_etaF : ∀ w : Fbar, pbarG (etaF w) = etaP (pbar w) := fun _ => rfl
    have hkereta : y - pbar w₀ ∈ NP := by
      rw [← Submodule.ker_mkQ NP, LinearMap.mem_ker]
      change etaP (y - pbar w₀) = 0
      rw [map_sub, ← hpbarG_etaF, hw₀, hcy]
      simp
    -- Step 4: get n ∈ NF with pbar n = y - pbar w₀
    rw [hmap, Submodule.mem_map] at hkereta
    obtain ⟨n, hn_mem, hn⟩ := hkereta
    refine ⟨w₀ + n, ?_⟩
    apply Subtype.ext
    change ((etaF).prod pbar) (w₀ + n) = (c, y)
    rw [LinearMap.prod_apply]
    apply Prod.ext
    · -- etaF (w₀ + n) = c
      change etaF (w₀ + n) = c
      rw [map_add, hw₀]
      have hetaFn : etaF n = 0 := by
        rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
        exact hn_mem
      simp only [etaF] at hetaFn ⊢
      rw [hetaFn, add_zero]
    · -- pbar (w₀ + n) = y
      change pbar (w₀ + n) = y
      rw [map_add, hn]
      abel
  -- Comparison map etaFI : F/IF →ₗ[R] G with etaFI ∘ mkQ_I = etaF ∘ mkQ_J.
  let etaF_comp : F →ₗ[R] G := (etaF.restrictScalars R) ∘ₗ Submodule.mkQ (J • (⊤ : Submodule R F))
  -- `etaF_comp` kills `I • ⊤_F`: for `a ∈ I` and `m ∈ F` one has
  -- `etaF_comp (a • m) = ρ(a) • etaF (mkQ_J m)`, and `ρ(a)` lies in `Ī`, which annihilates
  -- `G`.
  have hkerI : I • (⊤ : Submodule R F) ≤ LinearMap.ker etaF_comp := by
    refine Submodule.smul_le.mpr ?_
    intro a ha x _
    rw [LinearMap.mem_ker]
    change Submodule.mkQ NF (Submodule.mkQ (J • (⊤ : Submodule R F)) (a • x)) = 0
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
    have hrho : (Ideal.Quotient.mk J a) ∈ Ibar := Ideal.mem_map_of_mem _ ha
    have hsmem : (Ideal.Quotient.mk J a) • Submodule.mkQ (J • (⊤ : Submodule R F)) x ∈ NF :=
      Submodule.smul_mem_smul hrho Submodule.mem_top
    have htower : Submodule.mkQ (J • (⊤ : Submodule R F)) (a • x)
        = (Ideal.Quotient.mk J a) • Submodule.mkQ (J • (⊤ : Submodule R F)) x := by
      rw [(Submodule.mkQ (J • (⊤ : Submodule R F))).map_smul_of_tower a x]; rfl
    rw [htower]
    exact hsmem
  let etaFI : (F ⧸ (I • (⊤ : Submodule R F))) →ₗ[R] G := Submodule.liftQ _ etaF_comp hkerI
  -- δ₁ : P̄ → G, the descent of etaFI ∘ σI (R-linear; kills JP).
  let delta1comp : P →ₗ[R] G := etaFI ∘ₗ σI
  -- `delta1comp` kills `J • ⊤_P`: as `σI` is `R`-linear it maps `J • ⊤_P` into `J • (F/IF)`,
  -- and `etaFI` of that lies in `J • G = 0`, since `G` is an `R/J`-module and so `J` acts as
  -- zero on it.
  have hkerJ : J • (⊤ : Submodule R P) ≤ LinearMap.ker delta1comp := by
    -- J annihilates G as an R-module (G is an R/J-module via restriction of scalars).
    have hJann : ∀ (a : R), a ∈ J → ∀ g : G, a • g = 0 := by
      intro a ha g
      induction g using Quotient.ind with
      | _ z =>
        induction z using Quotient.ind with
        | _ w =>
          -- a • [[w]] = [[a • w]], and a • w ∈ J • ⊤_F so [a • w]_J = 0
          have hJw : a • w ∈ (J • (⊤ : Submodule R F)) :=
            Submodule.smul_mem_smul ha Submodule.mem_top
          have hzero : Submodule.mkQ (J • (⊤ : Submodule R F)) (a • w) = 0 := by
            rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
            exact hJw
          change a • (Submodule.mkQ NF (Submodule.mkQ (J • (⊤ : Submodule R F)) w))
              = (0 : G)
          rw [← (Submodule.mkQ NF).map_smul_of_tower,
            ← (Submodule.mkQ (J • (⊤ : Submodule R F))).map_smul_of_tower, hzero]
          simp
    refine Submodule.smul_le.mpr ?_
    intro a ha x _
    rw [LinearMap.mem_ker, map_smul]
    exact hJann a ha (delta1comp x)
  -- Repackage delta1 as R/J-linear (it descends through P/JP = P̄).
  let delta1 : Pbar →ₗ[R ⧸ J] G :=
    { toFun := Submodule.liftQ _ delta1comp hkerJ
      map_add' := map_add _
      map_smul' := by
        intro c m
        induction c using Quotient.ind with
        | _ r => induction m using Quotient.ind with
          | _ z =>
            change (Submodule.liftQ _ delta1comp hkerJ) (Submodule.mkQ _ (r • z))
                = (Ideal.Quotient.mk J r) • (Submodule.liftQ _ delta1comp hkerJ) (Submodule.mkQ _ z)
            -- `R/J`-linearity of `delta1`: `liftQ _ _ _ (mkQ z) = delta1comp z`, then
            -- `delta1comp (r • z) = r • delta1comp z` by linearity, and the `R/J`-scalar
            -- action of `mk J r` on `G` is definitionally the `R`-scalar action of `r`.
            rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.liftQ_apply,
              Submodule.liftQ_apply, map_smul]
            rfl }
  -- `δ x̄ = (delta1 x̄, x̄)` lands in `T`, by the section property of `σI`. It suffices to
  -- check this for `x̄ = mkQ_J m`, i.e. that `pbarG (delta1 (mkQ_J m)) = etaP (mkQ_J m)`. The
  -- left side is `pbarG (etaFI (σI m)) = etaPI (p̄I (σI m))` by naturality, `p̄I (σI m)` is
  -- `mkQ_I m` by the section property, and `etaPI (mkQ_I m) = etaP (mkQ_J m)`.
  have hdmem : ∀ y : Pbar, (delta1 y, y) ∈ T := by
    intro y
    rw [hT, LinearMap.mem_ker]
    have hgoal : pbarG (delta1 y) = etaP y := by
      induction y using Quotient.ind with
      | _ m =>
        change pbarG (delta1 (Submodule.mkQ _ m)) = etaP (Submodule.mkQ _ m)
        -- delta1 (mkQ_J m) = etaFI (σI m)
        have hd1 : delta1 (Submodule.mkQ (J • (⊤ : Submodule R P)) m) = etaFI (σI m) := rfl
        rw [hd1]
        -- pick a lift wI of σI m
        obtain ⟨wI, hwI⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R F)) (σI m)
        have hetaFI : etaFI (σI m) = etaF (Submodule.mkQ (J • (⊤ : Submodule R F)) wI) := by
          rw [← hwI]; rfl
        rw [hetaFI]
        -- naturality: pbarG (etaF w) = etaP (pbar w)
        have hnat : pbarG (etaF (Submodule.mkQ (J • (⊤ : Submodule R F)) wI))
            = etaP (pbar (Submodule.mkQ (J • (⊤ : Submodule R F)) wI)) := rfl
        rw [hnat, hpbar_apply]
        -- now goal: etaP (mkQ_J (p wI)) = etaP (mkQ_J m)
        -- it suffices mkQ_J (p wI - m) ∈ NP
        -- From hσI and hwI: mkQ_I (p wI) = mkQ_I m, i.e. p wI - m ∈ I•⊤_P
        have hIeq : (Submodule.mapQ (I • (⊤ : Submodule R F)) (I • (⊤ : Submodule R P)) p hpsubI)
            (Submodule.mkQ (I • (⊤ : Submodule R F)) wI) = Submodule.mkQ (I • (⊤ : Submodule R
                P)) m := by
          rw [hwI]; exact hσI m
        -- (mapQ ... p ...) (mkQ wI) = mkQ (p wI) by rfl
        have hIeq2 : Submodule.mkQ (I • (⊤ : Submodule R P)) (p wI)
            = Submodule.mkQ (I • (⊤ : Submodule R P)) m := hIeq
        -- hIeq2 : mkQ_I (p wI) = mkQ_I m
        have hmemIP : p wI - m ∈ (I • (⊤ : Submodule R P)) := by
          rw [← Submodule.ker_mkQ (I • (⊤ : Submodule R P)), LinearMap.mem_ker, map_sub,
              sub_eq_zero]
          exact hIeq2
        -- so mkQ_J (p wI - m) ∈ NP = Ibar • ⊤
        have hmemNP : Submodule.mkQ (J • (⊤ : Submodule R P)) (p wI - m) ∈ NP := by
          refine Submodule.smul_induction_on hmemIP ?_ ?_
          · intro r hr n _
            rw [hNP, hIbar, map_smul]
            change (Ideal.Quotient.mk J r) • Submodule.mkQ (J • (⊤ : Submodule R P)) n
                ∈ Ibar • (⊤ : Submodule (R ⧸ J) Pbar)
            exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top
          · intro a b ha hb
            rw [map_add]
            exact Submodule.add_mem _ ha hb
        -- conclude etaP equality
        change etaP (Submodule.mkQ (J • (⊤ : Submodule R P)) (p wI))
            = etaP (Submodule.mkQ (J • (⊤ : Submodule R P)) m)
        rw [← sub_eq_zero, ← map_sub, ← map_sub]
        rw [← LinearMap.mem_ker, show LinearMap.ker etaP = NP from Submodule.ker_mkQ NP]
        exact hmemNP
    change (pbarG ∘ₗ (LinearMap.fst (R ⧸ J) G Pbar) - etaP ∘ₗ (LinearMap.snd (R ⧸ J) G Pbar))
        (delta1 y, y) = 0
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply,
      sub_eq_zero]
    exact hgoal
  let delta : Pbar →ₗ[R ⧸ J] T := LinearMap.codRestrict T (delta1.prod LinearMap.id) hdmem
  -- Lift δ through the surjection q using projectivity of P̄ = P/JP over R/J.
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q delta hq_surj
  -- σJ := (s restricted to R) ∘ mkQ_J : P → F̄.
  let σJ : P →ₗ[R] Fbar := (s.restrictScalars R) ∘ₗ Submodule.mkQ (J • (⊤ : Submodule R P))
  refine ⟨σJ, ?_, ?_⟩
  · -- The section property modulo `J`. Here `σJ x = s (mkQ_J x)`, and since `pr₂ ∘ q = pbar`
    -- and `pr₂ ∘ δ = id`, the `P̄`-component of `q (s (mkQ_J x)) = δ (mkQ_J x)` reads
    -- `pbar (σJ x) = mkQ_J x`, where `pbar = mapQ J p hpsubJ`.
    exact fun x ↦ congrArg (fun t ↦ t.1.2) (LinearMap.congr_fun hs (Submodule.mkQ _ x))
  · -- Agreement modulo `I+J`. The `G`-component of `q (s (mkQ_J x)) = δ (mkQ_J x)` gives
    -- `etaF (σJ x) = delta1 (mkQ_J x) = etaFI (σI x)`. Choose any lifts `wJ` of `σJ x` and
    -- `wI` of `σI x`. Since `etaFI ∘ mkQ_I = etaF ∘ mkQ_J`, the equation
    -- `etaF (mkQ_J wJ) = etaFI (mkQ_I wI)` unfolds to `mkQ_NF (mkQ_J wJ) = mkQ_NF (mkQ_J wI)`,
    -- i.e. `mkQ_J (wI - wJ) ∈ NF = Ī • ⊤`. Pulling back along `mkQ_J` gives
    -- `wI - wJ ∈ I • ⊤ + J • ⊤`, the preimage of `Ī • (F/JF)` being `(I+J) • ⊤_F`.
    intro x
    have hGeq : etaF (σJ x) = etaFI (σI x) :=
      congrArg (fun t ↦ t.1.1) (LinearMap.congr_fun hs (Submodule.mkQ _ x))
    -- choose lifts
    obtain ⟨wJ, hwJ⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule R F)) (σJ x)
    obtain ⟨wI, hwI⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule R F)) (σI x)
    refine ⟨wI, wJ, hwI, hwJ, ?_⟩
    -- From hGeq: etaF (mkQ_J wJ) = etaFI (mkQ_I wI). Both = mkQ_NF (mkQ_J ·).
    -- etaFI (mkQ_I wI) = etaF_comp wI = etaF (mkQ_J wI)
    have hetaFI_wI : etaFI (σI x) = etaF (Submodule.mkQ (J • (⊤ : Submodule R F)) wI) := by
      rw [← hwI]; rfl
    rw [← hwJ, hetaFI_wI] at hGeq
    -- hGeq : etaF (mkQ_J wJ) = etaF (mkQ_J wI), i.e. mkQ_NF (mkQ_J wJ) = mkQ_NF (mkQ_J wI)
    -- so mkQ_J (wI - wJ) ∈ NF
    have hmemNF : Submodule.mkQ (J • (⊤ : Submodule R F)) (wI - wJ) ∈ NF := by
      rw [← Submodule.ker_mkQ NF, LinearMap.mem_ker, map_sub]
      change etaF (Submodule.mkQ (J • (⊤ : Submodule R F)) wI)
          - etaF (Submodule.mkQ (J • (⊤ : Submodule R F)) wJ) = 0
      rw [← hGeq]; abel
    -- Now translate: mkQ_J (wI - wJ) ∈ Ī•⊤ ⟹ wI - wJ ∈ I•⊤ + J•⊤
    set z := wI - wJ
    have hImg : Submodule.mkQ (J • (⊤ : Submodule R F)) z
        ∈ Submodule.map (Submodule.mkQ (J • (⊤ : Submodule R F))) (I • (⊤ : Submodule R F)) := by
      rw [hNF, hIbar] at hmemNF
      refine Submodule.smul_induction_on hmemNF ?_ ?_
      · intro c hc m _
        induction c using Quotient.ind with
        | _ r =>
          induction m using Quotient.ind with
          | _ w =>
            rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hc
            obtain ⟨i, hi, hir⟩ := hc
            rw [← hir]
            change Submodule.mkQ (J • (⊤ : Submodule R F)) (i • w)
                ∈ Submodule.map (Submodule.mkQ (J • (⊤ : Submodule R F))) (I • (⊤ : Submodule R F))
            exact Submodule.mem_map_of_mem (Submodule.smul_mem_smul hi Submodule.mem_top)
      · intro a b ha hb
        exact Submodule.add_mem _ ha hb
    rw [Submodule.mem_map] at hImg
    obtain ⟨u, hu, huz⟩ := hImg
    have hsub : z - u ∈ (J • (⊤ : Submodule R F)) := by
      rw [← Submodule.ker_mkQ (J • (⊤ : Submodule R F)), LinearMap.mem_ker, map_sub, sub_eq_zero]
      exact huz.symm
    rw [show z = u + (z - u) by abel]
    exact Submodule.add_mem_sup hu hsub

open Classical in
/-- Existence of the lift `h`, the heart of Lemma 0H7M. Given `I ⊓ J = ⊥`, a free `F` with a
surjection `p : F →ₗ[R] P`, and projectivity of `P/IP` over `R/I` and of `P/JP` over `R/J`,
there is `h : P →ₗ[R] F` such that for all `x` the element `x - p (h x)` lies in both `I • ⊤`
and `J • ⊤`.

The Stacks gluing argument runs in four steps.
1. Sectioning modulo `I` gives an `R`-linear `σI : P → F/IF` with `p̄I (σI x) = [x]_I`, so that
   choosing any lift recovers `x` modulo `IP`.
2. Projectivity of `P/JP` gives a section modulo `J` adjusted to agree with `σI` modulo `I+J`:
   form the surjection `q : F/JF → (F/(I+J)F) ×_{P/(I+J)P} (P/JP)` and lift the element
   `(image of σI in F/(I+J)F, id)` through `q`. This yields `σJ : P → F/JF` with
   `p̄J (σJ x) = [x]_J` and `σI x ≡ σJ x (mod (I+J)F)` for all `x`.
3. For each `x` the residues `σI x ∈ F/IF` and `σJ x ∈ F/JF` agree in `F/(I+J)F`; lifting both
   to `F` and applying `free_glue_of_inf_eq_bot` gives a well-defined `h x : F` with
   `h x ≡ (lift of σI x) (mod IF)` and `≡ (lift of σJ x) (mod JF)`. Linearity of `x ↦ h x`
   comes from uniqueness (`inf_smul_top_eq_bot`): `h` is the composite of the `R`-linear pair
   `(σI, σJ) : P → fibre product` with the inverse of the gluing isomorphism.
4. Finally `x - p (h x) ∈ I • ⊤`: since `h x ≡ (lift of σI x) (mod IF)` and `p(IF) ⊆ IP`, we
   get `p (h x) ≡ p (lift of σI x) (mod IP)`, and by step 1
   `p (lift of σI x) ≡ x (mod IP)`. Symmetrically for `J`, using step 2. -/
private theorem exists_lift_id_mod_I_and_J
    (R : Type*) [CommRing R] (I J : Ideal R) (hIJ : I ⊓ J = ⊥)
    (P : Type*) [AddCommGroup P] [Module R P]
    (F : Type*) [AddCommGroup F] [Module R F] [Module.Free R F]
    (p : F →ₗ[R] P) (hp : Function.Surjective p)
    (hI : Module.Projective (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))))
    (hJ : Module.Projective (R ⧸ J) (P ⧸ (J • (⊤ : Submodule R P)))) :
    ∃ h : P →ₗ[R] F,
      (∀ x, (LinearMap.id - p ∘ₗ h : P →ₗ[R] P) x ∈ I • (⊤ : Submodule R P)) ∧
      (∀ x, (LinearMap.id - p ∘ₗ h : P →ₗ[R] P) x ∈ J • (⊤ : Submodule R P)) := by
  -- The lift is assembled from `exists_section_mod` for `I` and for `J`, the
  -- agreement-modulo-`(I+J)` adjustment coming from projectivity of `P/JP`, and
  -- `free_glue_of_inf_eq_bot` together with `inf_smul_top_eq_bot` for the gluing isomorphism.
  -- First, `p` maps `K • ⊤_F` into `K • ⊤_P`.
  have hpsub : ∀ K : Ideal R,
      K • (⊤ : Submodule R F) ≤ Submodule.comap p (K • (⊤ : Submodule R P)) := fun K =>
    Submodule.map_le_iff_le_comap.mp (map_smul_top_le p)
  -- σI from section mod I.
  obtain ⟨σI, hσI⟩ := exists_section_mod R I P F p hp hI
  -- The agreement adjustment: produce `σJ` that is a section modulo `J` and whose lifts agree
  -- with those of `σI` modulo `(I+J)F`. This is the Stacks lift `g : P/JP → F/JF` through the
  -- fibre product `q`, using projectivity of `P/JP`.
  obtain ⟨σJ, hσJ, hagree⟩ := exists_section_mod_agree R I J P F p hp hJ (hpsub I) (hpsub J) σI hσI
  -- The gluing: build the `R`-linear `h` from injectivity of `Φ = (mkQ_IF).prod (mkQ_JF)`,
  -- whose kernel is `IF ⊓ JF = ⊥` by `inf_smul_top_eq_bot`, together with surjectivity onto
  -- agreeing pairs, by `free_glue_of_inf_eq_bot`.
  obtain ⟨h, hhI, hhJ⟩ :
      ∃ h : P →ₗ[R] F,
        (∀ x, Submodule.mkQ (I • (⊤ : Submodule R F)) (h x) = σI x) ∧
        (∀ x, Submodule.mkQ (J • (⊤ : Submodule R F)) (h x) = σJ x) := by
    set Φ : F →ₗ[R] (F ⧸ (I • (⊤ : Submodule R F))) × (F ⧸ (J • (⊤ : Submodule R F))) :=
      (Submodule.mkQ _).prod (Submodule.mkQ _) with hΦ
    have hker : LinearMap.ker Φ = ⊥ := by
      rw [hΦ, LinearMap.ker_prod]
      simp only [Submodule.ker_mkQ]
      exact inf_smul_top_eq_bot R I J hIJ F
    have hinj : Function.Injective Φ := LinearMap.ker_eq_bot.mp hker
    set g : P →ₗ[R] (F ⧸ (I • (⊤ : Submodule R F))) × (F ⧸ (J • (⊤ : Submodule R F))) :=
      σI.prod σJ with hg
    have hsub : ∀ x, g x ∈ LinearMap.range Φ := by
      intro x
      obtain ⟨wI, wJ, hwI, hwJ, hd⟩ := hagree x
      obtain ⟨w, hwwI, hwwJ⟩ := free_glue_of_inf_eq_bot R I J F wI wJ hd
      refine ⟨w, ?_⟩
      rw [hΦ, hg]
      apply Prod.ext
      · change (Submodule.mkQ _) w = σI x
        refine Eq.trans ?_ hwI
        simp only [Submodule.mkQ_apply]
        exact (Submodule.Quotient.eq _).mpr hwwI
      · change (Submodule.mkQ _) w = σJ x
        refine Eq.trans ?_ hwJ
        simp only [Submodule.mkQ_apply]
        exact (Submodule.Quotient.eq _).mpr hwwJ
    set e : F ≃ₗ[R] (LinearMap.range Φ) := LinearEquiv.ofInjective Φ hinj with he
    set g' : P →ₗ[R] (LinearMap.range Φ) :=
      LinearMap.codRestrict (LinearMap.range Φ) g hsub with hg'
    set h : P →ₗ[R] F := e.symm.toLinearMap.comp g' with hh
    have hΦh : ∀ x, Φ (h x) = g x := fun x => by
      change Φ (e.symm (g' x)) = g x
      exact congrArg Subtype.val (e.apply_symm_apply (g' x))
    exact ⟨h, fun x => by simpa [hΦ, hg] using congrArg Prod.fst (hΦh x),
      fun x => by simpa [hΦ, hg] using congrArg Prod.snd (hΦh x)⟩
  -- Membership: `x - p (h x)` lies in `K • ⊤` for each of `I` and `J`.
  have hmem : ∀ (K : Ideal R) (σ : P →ₗ[R] (F ⧸ (K • (⊤ : Submodule R F)))),
      (∀ x, Submodule.mapQ _ _ p (hpsub K) (σ x) = Submodule.mkQ (K • (⊤ : Submodule R P)) x) →
      (∀ x, Submodule.mkQ (K • (⊤ : Submodule R F)) (h x) = σ x) →
      ∀ x, (LinearMap.id - p ∘ₗ h : P →ₗ[R] P) x ∈ K • (⊤ : Submodule R P) := by
    intro K σ hσ hh x
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
    have key : Submodule.mkQ (K • (⊤ : Submodule R P)) (p (h x))
             = Submodule.mkQ (K • (⊤ : Submodule R P)) x := by
      have h1 := hσ x
      rw [← hh x] at h1
      rw [Submodule.mkQ_apply, Submodule.mapQ_apply] at h1
      simpa [Submodule.mkQ_apply] using h1
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply] at key
    rw [key]
    simp
  exact ⟨h, hmem I σI hσI hhI, hmem J σJ hσJ hhJ⟩

/-- Stacks Tag 0H7M, Lemma 10.77.8: if $I \cap J = 0$ and both $P/IP$ (as an
$R/I$-module) and $P/JP$ (as an $R/J$-module) are projective, then $P$ is a
projective $R$-module. -/
@[stacks 0H7M]
theorem projective_of_projective_quotient_inter_zero
    (R : Type*) [CommRing R] (I J : Ideal R) (hIJ : I ⊓ J = ⊥)
    (P : Type*) [AddCommGroup P] [Module R P]
    (hI : Module.Projective (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P))))
    (hJ : Module.Projective (R ⧸ J) (P ⧸ (J • (⊤ : Submodule R P)))) :
    Module.Projective R P := by
  classical
  -- Free module with the canonical surjection onto `P`.
  set F : Type _ := P →₀ R with hF
  set p : F →ₗ[R] P := Finsupp.linearCombination R (id : P → P) with hp
  have hpsurj : Function.Surjective p := by
    intro x
    refine ⟨Finsupp.single x 1, ?_⟩
    rw [hp, Finsupp.linearCombination_single]
    simp
  -- The heart of the proof: construct a map `h : P → F` such that `p ∘ h` is
  -- the identity modulo `I` and modulo `J`.  (See `exists_lift_id_mod_I_and_J`.)
  obtain ⟨h, hmemI, hmemJ⟩ :
      ∃ h : P →ₗ[R] F,
        (∀ x, (LinearMap.id - p ∘ₗ h : P →ₗ[R] P) x ∈ I • (⊤ : Submodule R P)) ∧
        (∀ x, (LinearMap.id - p ∘ₗ h : P →ₗ[R] P) x ∈ J • (⊤ : Submodule R P)) :=
    exists_lift_id_mod_I_and_J R I J hIJ P F p hpsurj hI hJ
  -- The automorphism argument: `b := id - p∘h` squares to zero, so `p∘h` is an
  -- isomorphism and `p` splits, making `P` a retract of the free module `F`.
  set b : P →ₗ[R] P := LinearMap.id - p ∘ₗ h with hb
  have hbb : b ∘ₗ b = 0 := by
    apply LinearMap.ext
    intro x
    have hmap : Submodule.map b (J • (⊤ : Submodule R P)) ≤ (J * I) • ⊤ := by
      rw [Submodule.map_smul'' J ⊤ b, Submodule.mul_smul]
      apply Submodule.smul_mono (le_refl J)
      intro y hy
      simp only [Submodule.mem_map] at hy
      obtain ⟨z, _, rfl⟩ := hy
      exact hmemI z
    have hJI : (J * I) • (⊤ : Submodule R P) = ⊥ := by
      have hle : J * I ≤ I ⊓ J := by
        rw [mul_comm]
        exact Ideal.mul_le_inf
      rw [hIJ, le_bot_iff] at hle
      rw [hle]
      simp
    have hb2 := hmap (Submodule.mem_map_of_mem (hmemJ x))
    rw [hJI] at hb2
    simpa using hb2
  have hinv : p ∘ₗ (h ∘ₗ (LinearMap.id + b)) = LinearMap.id := by
    have hph : p ∘ₗ h = LinearMap.id - b := by
      rw [hb]
      ext x
      simp
    rw [← LinearMap.comp_assoc, hph]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.id_apply,
      map_add]
    have hbbx : b (b x) = 0 := by simpa using LinearMap.congr_fun hbb x
    rw [hbbx]
    abel
  exact Module.Projective.of_split (h ∘ₗ (LinearMap.id + b)) p hinv
