module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.Algebra.Prod
public import Mathlib.Order.Fin.Basic

/-!
# Fibre products of one algebra with a sequence of algebras

Let `R₀` be a `Λ`-algebra and, for every `k : ℕ`, let `φ k : R₀ → A k` and `f k : A' k → A k`
be maps of `Λ`-algebras. The `n`-th *stage* is the iterated fibre product
`R₀ ×_{A 0} A' 0 ×_{A 1} A' 1 ⋯ ×_{A (n-1)} A' (n-1)`, realised as the subalgebra of
`R₀ × Π k < n, A' k` of the tuples `(r, a')` with `φ k r = f k (a' k)`; the *limit* is the
subalgebra of `R₀ × Π k, A' k` cut out by the same equations. The stages form an inverse system
indexed by `ℕᵒᵖ` whose limit is the limit algebra, and each stage is the fibre product of the
previous one with `A' n` over `A n`.

When every `f k` is surjective with square-zero kernel, the transition maps of the system are
surjective with square-zero kernel. This is the inverse system of rings in the proof of
Stacks 0CXU.

## Main definitions

* `Stacks.CompatibleTuples.stage`, `Stacks.CompatibleTuples.limit`: the stages and the limit.
* `Stacks.CompatibleTuples.diagram`, `Stacks.CompatibleTuples.cone`: the inverse system of the
  stages in `CommAlgCat Λ`, and the cone of the limit over it.

## Main results

* `Stacks.CompatibleTuples.isLimitCone`: the cone of the limit is a limit cone.
* `Stacks.CompatibleTuples.isPullback_stage_succ`: the stage `n + 1` is the fibre product of the
  stage `n` and `A' n` over `A n`.
* `Stacks.CompatibleTuples.surjective_restrict`, `Stacks.CompatibleTuples.ker_restrict_sq`:
  surjectivity and square-zero kernels of the transition maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CommRingCat

/-- **A commutative square of rings whose two maps out of the apex jointly separate points and
realise every compatible pair is a pullback square.** -/
theorem isPullback_of_bijective {P R T Q : Type u} [CommRing P] [CommRing R] [CommRing T]
    [CommRing Q] (a : P →+* R) (b : P →+* T) (f : R →+* Q) (g : T →+* Q)
    (hcomm : f.comp a = g.comp b)
    (hinj : ∀ x y : P, a x = a y → b x = b y → x = y)
    (hsurj : ∀ (r : R) (t : T), f r = g t → ∃ x : P, a x = r ∧ b x = t) :
    IsPullback (CommRingCat.ofHom a) (CommRingCat.ofHom b) (CommRingCat.ofHom f)
      (CommRingCat.ofHom g) := by
  let L := RingHom.eqLocus (f.comp (RingHom.fst R T)) (g.comp (RingHom.snd R T))
  let ψ : P →+* L := RingHom.codRestrict (a.prod b) L (fun x =>
    show f (a x) = g (b x) from RingHom.congr_fun hcomm x)
  have hψ : Function.Bijective ψ := by
    refine ⟨fun x y h => hinj x y ?_ ?_, fun z => ?_⟩
    · exact congrArg (fun z : L => (z : R × T).1) h
    · exact congrArg (fun z : L => (z : R × T).2) h
    · obtain ⟨x, hx1, hx2⟩ := hsurj (z : R × T).1 (z : R × T).2 z.2
      exact ⟨x, Subtype.ext (Prod.ext hx1 hx2)⟩
  let e : CommRingCat.of P ≅ CommRingCat.of L := (RingEquiv.ofBijective ψ hψ).toCommRingCatIso
  refine IsPullback.of_iso (IsPullback.of_isLimit
    (CommRingCat.pullbackConeIsLimit (CommRingCat.ofHom f) (CommRingCat.ofHom g))) e.symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · ext z
    obtain ⟨x, rfl⟩ := hψ.2 z
    change (ψ x : R × T).1 = a ((RingEquiv.ofBijective ψ hψ).symm (RingEquiv.ofBijective ψ hψ x))
    rw [RingEquiv.symm_apply_apply]
    rfl
  · ext z
    obtain ⟨x, rfl⟩ := hψ.2 z
    change (ψ x : R × T).2 = b ((RingEquiv.ofBijective ψ hψ).symm (RingEquiv.ofBijective ψ hψ x))
    rw [RingEquiv.symm_apply_apply]
    rfl
  · simp
  · simp

end CommRingCat

namespace Stacks.CompatibleTuples

variable {Λ R₀ : Type u} [CommRing Λ] [CommRing R₀] [Algebra Λ R₀]
  {A A' : ℕ → Type u} [∀ n, CommRing (A n)] [∀ n, CommRing (A' n)] [∀ n, Algebra Λ (A n)]
  [∀ n, Algebra Λ (A' n)] (φ : ∀ n, R₀ →ₐ[Λ] A n) (f : ∀ n, A' n →ₐ[Λ] A n)

/-- The `n`-th stage: the tuples `(r, a')` of `R₀ × Π k < n, A' k` with `φ k r = f k (a' k)`. -/
def stage (n : ℕ) : Subalgebra Λ (R₀ × Π k : Fin n, A' k) where
  carrier := {p | ∀ k : Fin n, φ k p.1 = f k (p.2 k)}
  mul_mem' {p q} hp hq k := by
    change φ k (p.1 * q.1) = f k (p.2 k * q.2 k)
    rw [map_mul, map_mul, hp k, hq k]
  add_mem' {p q} hp hq k := by
    change φ k (p.1 + q.1) = f k (p.2 k + q.2 k)
    rw [map_add, map_add, hp k, hq k]
  algebraMap_mem' l k := by
    change φ k (algebraMap Λ R₀ l) = f k (algebraMap Λ (A' k) l)
    rw [AlgHom.commutes, AlgHom.commutes]

/-- The limit: the tuples `(r, a')` of `R₀ × Π k, A' k` with `φ k r = f k (a' k)`. -/
def limit : Subalgebra Λ (R₀ × Π k : ℕ, A' k) where
  carrier := {p | ∀ k : ℕ, φ k p.1 = f k (p.2 k)}
  mul_mem' {p q} hp hq k := by
    change φ k (p.1 * q.1) = f k (p.2 k * q.2 k)
    rw [map_mul, map_mul, hp k, hq k]
  add_mem' {p q} hp hq k := by
    change φ k (p.1 + q.1) = f k (p.2 k + q.2 k)
    rw [map_add, map_add, hp k, hq k]
  algebraMap_mem' l k := by
    change φ k (algebraMap Λ R₀ l) = f k (algebraMap Λ (A' k) l)
    rw [AlgHom.commutes, AlgHom.commutes]

/-- The ring structure of a stage, fixed once so that every later use of a stage sees the same
instance. -/
instance stageCommRing (n : ℕ) : CommRing (stage φ f n) := Subalgebra.toCommRing _

/-- The semiring structure of a stage, the one underlying `Stacks.CompatibleTuples.stageCommRing`.
-/
instance stageSemiring (n : ℕ) : Semiring (stage φ f n) :=
  (stageCommRing φ f n).toCommSemiring.toSemiring

/-- The `Λ`-algebra structure of a stage. -/
instance stageAlgebra (n : ℕ) : Algebra Λ (stage φ f n) := Subalgebra.algebra _

/-- The ring structure of the limit, fixed once so that every later use of it sees the same
instance. -/
instance limitCommRing : CommRing (limit φ f) := Subalgebra.toCommRing _

/-- The semiring structure of the limit, the one underlying
`Stacks.CompatibleTuples.limitCommRing`. -/
instance limitSemiring : Semiring (limit φ f) := (limitCommRing φ f).toCommSemiring.toSemiring

/-- The `Λ`-algebra structure of the limit. -/
instance limitAlgebra : Algebra Λ (limit φ f) := Subalgebra.algebra _

/-- The projection of a stage to `R₀`. -/
def stageFst (n : ℕ) : stage φ f n →ₐ[Λ] R₀ :=
  (AlgHom.fst Λ R₀ (Π k : Fin n, A' k)).comp (stage φ f n).val

/-- The projection of the stage `n + 1` to its last factor `A' n`. -/
def stageLast (n : ℕ) : stage φ f (n + 1) →ₐ[Λ] A' n :=
  (Pi.evalAlgHom Λ (fun k : Fin (n + 1) => A' k) (Fin.last n)).comp
    ((AlgHom.snd Λ R₀ (Π k : Fin (n + 1), A' k)).comp (stage φ f (n + 1)).val)

/-- The projection of the limit to `R₀`. -/
def limitFst : limit φ f →ₐ[Λ] R₀ :=
  (AlgHom.fst Λ R₀ (Π k : ℕ, A' k)).comp (limit φ f).val

/-- The projection of the limit to the factor `A' n`. -/
def limitEval (n : ℕ) : limit φ f →ₐ[Λ] A' n :=
  (Pi.evalAlgHom Λ A' n).comp ((AlgHom.snd Λ R₀ (Π k : ℕ, A' k)).comp (limit φ f).val)

/-- The transition map from a later stage to an earlier one: forget the last factors. -/
def restrict {m n : ℕ} (h : n ≤ m) : stage φ f m →ₐ[Λ] stage φ f n :=
  AlgHom.codRestrict
    ((AlgHom.prod (AlgHom.fst Λ R₀ (Π k : Fin m, A' k))
      (AlgHom.pi fun k : Fin n => Pi.evalAlgHom Λ (fun k : Fin m => A' k) (Fin.castLE h k) |>.comp
        (AlgHom.snd Λ R₀ (Π k : Fin m, A' k)))).comp (stage φ f m).val)
    (stage φ f n) (fun p k => p.2 (Fin.castLE h k))

/-- The projection of the limit to a stage. -/
def proj (n : ℕ) : limit φ f →ₐ[Λ] stage φ f n :=
  AlgHom.codRestrict
    ((AlgHom.prod (AlgHom.fst Λ R₀ (Π k : ℕ, A' k))
      (AlgHom.pi fun k : Fin n => Pi.evalAlgHom Λ A' (k : ℕ) |>.comp
        (AlgHom.snd Λ R₀ (Π k : ℕ, A' k)))).comp (limit φ f).val)
    (stage φ f n) (fun p k => p.2 k)

/-- The `R₀`-component of the restriction of a tuple is its `R₀`-component. -/
@[simp]
theorem restrict_apply_fst {m n : ℕ} (h : n ≤ m) (p : stage φ f m) :
    (restrict φ f h p : R₀ × Π k : Fin n, A' k).1 = (p : R₀ × Π k : Fin m, A' k).1 := rfl

/-- The `k`-th factor of the restriction of a tuple is its `k`-th factor. -/
@[simp]
theorem restrict_apply_snd {m n : ℕ} (h : n ≤ m) (p : stage φ f m) (k : Fin n) :
    (restrict φ f h p : R₀ × Π k : Fin n, A' k).2 k =
      (p : R₀ × Π k : Fin m, A' k).2 (Fin.castLE h k) := rfl

/-- The `R₀`-component of the projection of a tuple of the limit is its `R₀`-component. -/
@[simp]
theorem proj_apply_fst (n : ℕ) (p : limit φ f) :
    (proj φ f n p : R₀ × Π k : Fin n, A' k).1 = (p : R₀ × Π k : ℕ, A' k).1 := rfl

/-- The `k`-th factor of the projection of a tuple of the limit is its `k`-th factor. -/
@[simp]
theorem proj_apply_snd (n : ℕ) (p : limit φ f) (k : Fin n) :
    (proj φ f n p : R₀ × Π k : Fin n, A' k).2 k = (p : R₀ × Π k : ℕ, A' k).2 k := rfl

/-- The transition map from a stage to itself is the identity. -/
theorem restrict_refl (n : ℕ) : restrict φ f (le_refl n) = AlgHom.id Λ _ :=
  AlgHom.ext fun _ => Subtype.ext (Prod.ext rfl (funext fun _ => rfl))

/-- The transition maps compose: restricting from `l` to `m` and then to `n` is restricting from
`l` to `n`. -/
theorem restrict_comp {l m n : ℕ} (h₁ : n ≤ m) (h₂ : m ≤ l) :
    (restrict φ f h₁).comp (restrict φ f h₂) = restrict φ f (h₁.trans h₂) :=
  AlgHom.ext fun _ => Subtype.ext (Prod.ext rfl (funext fun _ => rfl))

/-- The projections of the limit commute with the transition maps. -/
theorem restrict_comp_proj {m n : ℕ} (h : n ≤ m) :
    (restrict φ f h).comp (proj φ f m) = proj φ f n :=
  AlgHom.ext fun _ => Subtype.ext (Prod.ext rfl (funext fun _ => rfl))

/-- The transition maps commute with the projections to `R₀`. -/
theorem stageFst_comp_restrict {m n : ℕ} (h : n ≤ m) :
    (stageFst φ f n).comp (restrict φ f h) = stageFst φ f m := rfl

/-- The projection of the limit to a stage, followed by the projection to `R₀`, is the projection
of the limit to `R₀`. -/
theorem stageFst_comp_proj (n : ℕ) : (stageFst φ f n).comp (proj φ f n) = limitFst φ f := rfl

/-- The projection of the limit to the stage `n + 1`, followed by the projection to its last
factor, is the projection of the limit to `A' n`. -/
theorem stageLast_comp_proj (n : ℕ) :
    (stageLast φ f n).comp (proj φ f (n + 1)) = limitEval φ f n := rfl

/-- The compatibility of the last factor of a stage with `R₀`. -/
theorem comp_stageLast (n : ℕ) :
    (φ n).comp ((stageFst φ f n).comp (restrict φ f (Nat.le_succ n))) =
      (f n).comp (stageLast φ f n) := by
  ext p
  exact p.2 (Fin.last n)

/-- The compatibility of a factor of the limit with `R₀`. -/
theorem comp_limitEval (n : ℕ) : (φ n).comp (limitFst φ f) = (f n).comp (limitEval φ f n) := by
  ext p
  exact p.2 n

/-- The stage `0` is `R₀`. -/
theorem bijective_stageFst_zero : Function.Bijective (stageFst φ f 0) := by
  refine ⟨fun p q h => Subtype.ext (Prod.ext h (funext fun k => k.elim0)), fun r => ?_⟩
  exact ⟨⟨(r, fun k => k.elim0), fun k => k.elim0⟩, rfl⟩

/-- The stage `0`, identified with `R₀`. -/
def stageZeroEquiv : stage φ f 0 ≃ₐ[Λ] R₀ :=
  AlgEquiv.ofBijective (stageFst φ f 0) (bijective_stageFst_zero φ f)

/-- The projection of the stage `0` to `R₀` is a left inverse of the inverse of
`Stacks.CompatibleTuples.stageZeroEquiv`. -/
theorem stageFst_comp_stageZeroEquiv_symm :
    (stageFst φ f 0).comp (stageZeroEquiv φ f).symm.toAlgHom = AlgHom.id Λ R₀ :=
  AlgHom.ext fun r => (stageZeroEquiv φ f).apply_symm_apply r

/-! ### The inverse system and its limit -/

/-- The inverse system of the stages, in `CommAlgCat Λ`. -/
def diagram : ℕᵒᵖ ⥤ CommAlgCat.{u} Λ where
  obj n := .of Λ (stage φ f n.unop)
  map {_ _} g := CommAlgCat.ofHom (restrict φ f (leOfHom g.unop))
  map_id n := CommAlgCat.hom_ext (restrict_refl φ f n.unop)
  map_comp g g' := CommAlgCat.hom_ext (restrict_comp φ f (leOfHom g'.unop) (leOfHom g.unop)).symm

/-- The cone of the limit over the inverse system of the stages. -/
def cone : Cone (diagram φ f) where
  pt := .of Λ (limit φ f)
  π :=
    { app := fun n => CommAlgCat.ofHom (proj φ f n.unop)
      naturality := fun _ _ g => CommAlgCat.hom_ext (restrict_comp_proj φ f (leOfHom g.unop)).symm }

/-- The map to the limit from a cone over the stages. -/
def liftHom (s : Cone (diagram φ f)) : s.pt →ₐ[Λ] limit φ f :=
  AlgHom.codRestrict
    (AlgHom.prod ((stageFst φ f 0).comp (s.π.app (op 0)).hom)
      (AlgHom.pi fun k => (stageLast φ f k).comp (s.π.app (op (k + 1))).hom))
    (limit φ f) (fun x k => by
      change φ k (stageFst φ f 0 ((s.π.app (op 0)).hom x)) =
        f k (stageLast φ f k ((s.π.app (op (k + 1))).hom x))
      have h' : (restrict φ f (Nat.zero_le (k + 1)))
          (((s.π.app (op (k + 1))).hom x : stage φ f (k + 1))) =
          ((s.π.app (op 0)).hom x : stage φ f 0) :=
        (congrArg (fun g => g.hom x) (s.π.naturality (homOfLE (Nat.zero_le (k + 1))).op)).symm
      rw [← h']
      exact ((s.π.app (op (k + 1))).hom x : stage φ f (k + 1)).2 (Fin.last k))

/-- Two elements of a stage are equal if their `R₀`-components and all their factors agree. -/
theorem stage_ext {n : ℕ} {p q : stage φ f n}
    (h1 : (p : R₀ × Π k : Fin n, A' k).1 = (q : R₀ × Π k : Fin n, A' k).1)
    (h2 : ∀ k, (p : R₀ × Π k : Fin n, A' k).2 k = (q : R₀ × Π k : Fin n, A' k).2 k) : p = q :=
  Subtype.ext (Prod.ext h1 (funext h2))

/-- Two elements of the limit are equal if their `R₀`-components and all their factors agree. -/
theorem limit_ext {p q : limit φ f}
    (h1 : (p : R₀ × Π k : ℕ, A' k).1 = (q : R₀ × Π k : ℕ, A' k).1)
    (h2 : ∀ k, (p : R₀ × Π k : ℕ, A' k).2 k = (q : R₀ × Π k : ℕ, A' k).2 k) : p = q :=
  Subtype.ext (Prod.ext h1 (funext h2))

/-- The restriction of a cone over the stages, read at two stages. -/
theorem cone_restrict (s : Cone (diagram φ f)) {m n : ℕ} (h : n ≤ m) (x : s.pt) :
    restrict φ f h ((s.π.app (op m)).hom x) = (s.π.app (op n)).hom x :=
  (congrArg (fun g => g.hom x) (s.π.naturality (homOfLE h).op)).symm

/-- **The cone of the limit is a limit cone.** -/
def isLimitCone : IsLimit (cone φ f) where
  lift s := CommAlgCat.ofHom (liftHom φ f s)
  fac s n := by
    apply CommAlgCat.hom_ext
    ext x : 1
    refine stage_ext φ f ?_ (fun k => ?_)
    · change stageFst φ f 0 ((s.π.app (op 0)).hom x) = stageFst φ f n.unop ((s.π.app n).hom x)
      rw [← cone_restrict φ f s (Nat.zero_le n.unop) x]
      rfl
    · change stageLast φ f k ((s.π.app (op (k + 1))).hom x) = ((s.π.app n).hom x).1.2 k
      rw [← cone_restrict φ f s (Nat.succ_le_of_lt k.2) x]
      rfl
  uniq s m hm := by
    apply CommAlgCat.hom_ext
    ext x : 1
    refine limit_ext φ f ?_ (fun k => ?_)
    · exact congrArg (fun g : s.pt ⟶ (diagram φ f).obj (op 0) =>
        (g.hom x : stage φ f 0).1.1) (hm (op 0))
    · exact congrArg (fun g : s.pt ⟶ (diagram φ f).obj (op (k + 1)) =>
        (g.hom x : stage φ f (k + 1)).1.2 (Fin.last k)) (hm (op (k + 1)))

/-! ### The fibre product squares -/

/-- **The stage `n + 1` is the fibre product of the stage `n` and `A' n` over `A n`.** -/
theorem isPullback_stage_succ (n : ℕ) :
    IsPullback (CommRingCat.ofHom (restrict φ f (Nat.le_succ n)).toRingHom)
      (CommRingCat.ofHom (stageLast φ f n).toRingHom)
      (CommRingCat.ofHom ((φ n).comp (stageFst φ f n)).toRingHom)
      (CommRingCat.ofHom (f n).toRingHom) := by
  refine CommRingCat.isPullback_of_bijective _ _ _ _ ?_ ?_ ?_
  · exact congrArg AlgHom.toRingHom (comp_stageLast φ f n)
  · intro p q h1 h2
    refine stage_ext φ f (congrArg (fun z : stage φ f n => z.1.1) h1 :) (fun k => ?_)
    induction k using Fin.lastCases with
    | last => exact h2
    | cast k => exact congrArg (fun z : stage φ f n => z.1.2 k) h1
  · intro r t h
    refine ⟨⟨(r.1.1, Fin.snoc (α := fun k : Fin (n + 1) => A' k) r.1.2 t),
      fun k => ?_⟩, ?_, ?_⟩
    · induction k using Fin.lastCases with
      | last =>
        change φ n r.1.1 = f n (Fin.snoc (α := fun k : Fin (n + 1) => A' k)
          r.1.2 t (Fin.last n))
        rwa [Fin.snoc_last]
      | cast k =>
        change φ k r.1.1 = f k (Fin.snoc (α := fun k : Fin (n + 1) => A' k)
          r.1.2 t (Fin.castSucc k))
        rw [Fin.snoc_castSucc]
        exact r.2 k
    · refine stage_ext φ f rfl (fun k => ?_)
      change Fin.snoc (α := fun k : Fin (n + 1) => A' k) r.1.2 t (Fin.castSucc k) = _
      rw [Fin.snoc_castSucc]
    · change Fin.snoc (α := fun k : Fin (n + 1) => A' k) r.1.2 t (Fin.last n) = t
      rw [Fin.snoc_last]

/-! ### Surjectivity and square-zero kernels -/

variable {φ f}

/-- A tuple of a stage extends to a compatible sequence, when every `f k` is surjective. -/
private theorem exists_compatible_extension (hf : ∀ k, Function.Surjective (f k)) {n : ℕ}
    (q : stage φ f n) :
    ∃ a : Π k : ℕ, A' k, (∀ k, φ k q.1.1 = f k (a k)) ∧ ∀ k : Fin n, a k = q.1.2 k := by
  classical
  refine ⟨fun k => if hk : k < n then q.1.2 ⟨k, hk⟩ else (hf k (φ k q.1.1)).choose,
    fun k => ?_, fun k => ?_⟩
  · by_cases hk : k < n
    · simp only [hk, ↓reduceDIte]
      exact q.2 ⟨k, hk⟩
    · simp only [hk, ↓reduceDIte]
      exact (hf k (φ k q.1.1)).choose_spec.symm
  · simp only [k.2, ↓reduceDIte]

/-- **The transition maps are surjective** as soon as every `f k` is. -/
theorem surjective_restrict (hf : ∀ k, Function.Surjective (f k)) {m n : ℕ} (h : n ≤ m) :
    Function.Surjective (restrict φ f h) := fun q => by
  obtain ⟨a, ha, hq⟩ := exists_compatible_extension hf q
  exact ⟨⟨(q.1.1, fun k => a k), fun k => ha k⟩, stage_ext φ f rfl fun k => hq k⟩

/-- **The projections of the limit to the stages are surjective** as soon as every `f k` is. -/
theorem surjective_proj (hf : ∀ k, Function.Surjective (f k)) (n : ℕ) :
    Function.Surjective (proj φ f n) := fun q => by
  obtain ⟨a, ha, hq⟩ := exists_compatible_extension hf q
  exact ⟨⟨(q.1.1, a), ha⟩, stage_ext φ f rfl hq⟩

/-- **The projection of the limit to `R₀` is surjective** as soon as every `f k` is. -/
theorem surjective_limitFst (hf : ∀ k, Function.Surjective (f k)) :
    Function.Surjective (limitFst φ f) := fun r =>
  ⟨⟨(r, fun k => (hf k (φ k r)).choose), fun k => (hf k (φ k r)).choose_spec.symm⟩, rfl⟩

/-- The product of two elements in the kernel of a map with square-zero kernel vanishes. -/
private theorem mul_eq_zero_of_ker_sq {B C : Type u} [CommRing B] [CommRing C] {g : B →+* C}
    (hker : RingHom.ker g ^ 2 = ⊥) {a b : B} (ha : g a = 0) (hb : g b = 0) : a * b = 0 := by
  have := Ideal.mul_mem_mul (RingHom.mem_ker.2 ha) (RingHom.mem_ker.2 hb)
  rwa [← pow_two, hker, Ideal.mem_bot] at this

/-- **The transition maps have square-zero kernels** as soon as every `f k` has. -/
theorem ker_restrict_sq (hker : ∀ k, RingHom.ker (f k).toRingHom ^ 2 = ⊥) {m n : ℕ}
    (h : n ≤ m) : RingHom.ker (restrict φ f h).toRingHom ^ 2 = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [pow_two]
  refine Ideal.mul_le.2 fun a ha b hb => ?_
  have ha1 : a.1.1 = 0 := congrArg (fun z : stage φ f n => z.1.1) (ha : restrict φ f h a = 0)
  have hb1 : b.1.1 = 0 := congrArg (fun z : stage φ f n => z.1.1) (hb : restrict φ f h b = 0)
  refine Ideal.mem_bot.2 (stage_ext φ f ?_ (fun k => ?_))
  · change a.1.1 * b.1.1 = 0
    rw [ha1, zero_mul]
  · exact mul_eq_zero_of_ker_sq (hker k) (by change f k _ = 0; rw [← a.2 k, ha1, map_zero])
      (by change f k _ = 0; rw [← b.2 k, hb1, map_zero])

/-- **The projection of the limit to `R₀` has square-zero kernel** as soon as every `f k` has. -/
theorem ker_limitFst_sq (hker : ∀ k, RingHom.ker (f k).toRingHom ^ 2 = ⊥) :
    RingHom.ker (limitFst φ f).toRingHom ^ 2 = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [pow_two]
  refine Ideal.mul_le.2 fun a ha b hb => ?_
  have ha1 : a.1.1 = 0 := ha
  have hb1 : b.1.1 = 0 := hb
  refine Ideal.mem_bot.2 (limit_ext φ f ?_ (fun k => ?_))
  · change a.1.1 * b.1.1 = 0
    rw [ha1, zero_mul]
  · exact mul_eq_zero_of_ker_sq (hker k) (by change f k _ = 0; rw [← a.2 k, ha1, map_zero])
      (by change f k _ = 0; rw [← b.2 k, hb1, map_zero])

end Stacks.CompatibleTuples

end
