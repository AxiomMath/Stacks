module

public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
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
public import Mathlib.Tactic.ENatToNat
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

@[expose] public section

universe w v u

/-!
# Projective dimension along a well-ordered filtration

Let `R` be a ring and let `A` be an `R`-module which is the union of a family of submodules
`N e`, monotone in a well-ordered index set `E`. Auslander's theorem says that the projective
dimension of `A` is bounded by the projective dimensions of the graded pieces
`N e / ⨆ e' < e, N e'`. This file proves it in the form of Tag 0D1U.

The proof is by induction on `n`, the bound on the graded pieces, and the three cases `0`, `1` and
`m + 2` are genuinely different. For `n = 0` all graded pieces vanish, so `N e = ⊥` for every `e`
by transfinite induction and `A` is zero. For `n = 1` all graded pieces are projective, so each
projection `N e → N e / ⨆ e' < e, N e'` has a section, and the induced map from the direct sum of
the graded pieces to `A` is bijective: surjective by transfinite induction, and injective because
the largest index occurring in a nonzero element of the direct sum survives in its graded piece.
A direct sum of projectives is projective. For `n = m + 2` write `A` as a quotient of the free
module `F` on the underlying set of `A`, let `π : F → A` be the projection, and filter `F` by the
spans `F e` of the basis vectors indexed by `N e`. Then `π` carries `F e` onto `N e`, the graded
piece `F e / ⨆ e' < e, F e'` is free on the basis vectors indexed by the elements of `N e` outside
`⨆ e' < e, N e'`, and the graded pieces of the induced filtration of `Ker π` sit in short exact
sequences `0 → Ker π ∩ F e / … → F e / … → N e / … → 0`, hence have projective dimension `< m + 1`.
By induction `Ker π` has projective dimension `< m + 1`, and `0 → Ker π → F → A → 0` gives the
bound `m + 2` for `A`.

## Main results

* `Stacks.ProjectiveDimension.FiltrationBound.solution`: Stacks 0D1U, projective dimension is
  bounded along a monotone filtration by the projective dimensions of the graded pieces.

## Implementation notes

Four lemmas carry the mathematics, and the three cases of the induction are assembled from them.

`iSup_le_of_le_biSup_lt_sup` is the transfinite induction, in the only form it is ever used, and
at the generality it holds: an element `p` of a complete lattice which absorbs every `N e` modulo
the earlier stages of the filtration lies above `⨆ e, N e`. Both the case `n = 0` (with `p = ⊥`)
and the surjectivity half of the case `n = 1` (with `p` the range of the map out of the direct
sum) are that lemma applied once.

`injective_toModule_of_mem_biSup_lt` is the injectivity half of the case `n = 1`, and it is where
the well-ordering does its second piece of work: a family of maps `τ e : P e → A` landing in `N e`
and injective modulo `⨆ e' < e, N e'` induces an injective map on `⨁ e, P e`, because in a nonzero
element the component at the largest index of the support cannot be cancelled by the others, all of
which lie in earlier stages. Neither monotonicity of `N` nor surjectivity of anything is needed.

`hasProjectiveDimensionLT_gradedKer` records the exact sequence of graded pieces attached to a
linear map `f` and a pair of nested submodules `a₂ ≤ a₁` of its source: writing `k = Ker f`, the
sequence
`0 → (a₁ ∩ k)/(a₂ ∩ k) → a₁/a₂ → f(a₁)/f(a₂) → 0`
is short exact, the left-hand term being read as a quotient of submodules of `↥k`, which is the
shape the induction consumes. Its three exactness obligations are the `grMap` API — `grMap` being
the map on graded pieces induced by `f` — each stated under the weakest hypothesis that gives it:
`grMap_surjective` needs `f` to carry `a₁` onto `b₁`, `grMap_injective` needs only
`f x ∈ b₂ → x ∈ a₂` on `a₁` (not injectivity of `f`), and `grMap_ker_subtype_exact` needs `f` to
carry `a₂` onto `b₂`.

`mem_biSup_lt` turns membership in `⨆ e' < e, N e'` into membership in a single `N e'`, the family
being a chain; the possibility that no `e'` is `< e` is why its conclusion is a disjunction with
`x = 0`. It is what makes `Submodule.submoduleOf` commute with `⨆ e' < e`, so that the filtration
induced on a submodule has the graded pieces the induction expects.

The free module used in the inductive step is `A →₀ Shrink.{v} R`, the free module on the
underlying set of `A` with values in a small copy of `R`; this is what keeps it in the universe
`v` of `ModuleCat.{v} R`, and is Mathlib's own choice in `ModuleCat.enoughProjectives`. Only the
basis and the fact that the basis vector at `a` maps to `a` are used, so the argument is written
against an abstract basis, through `map_span_image` and `iSup_span_image_eq_top`.

## References

* [Stacks Project, Tag 0D1U](https://stacks.math.columbia.edu/tag/0D1U)
-/

namespace Stacks.ProjectiveDimension.FiltrationBound

open CategoryTheory Module Submodule



variable {R : Type u} [Ring R]

section Bounds

variable {A : Type v} [AddCommGroup A] [Module R A]

/-- A projective module has projective dimension `< n + 1`. -/
private lemma hasProjectiveDimensionLT_of_projective {M : ModuleCat.{v} R} [Projective M] (n : ℕ) :
    HasProjectiveDimensionLT M (n + 1) :=
  have := projective_iff_hasProjectiveDimensionLT_one.1 ‹Projective M›
  hasProjectiveDimensionLT_of_ge M 1 (n + 1) (by lia)

/-- A module with no nonzero submodule is zero, so it has projective dimension `< n` for every
`n` — including `n = 0`. -/
private lemma hasProjectiveDimensionLT_of_top_eq_bot (h : (⊤ : Submodule R A) = ⊥) (n : ℕ) :
    HasProjectiveDimensionLT (ModuleCat.of R A) n :=
  have h0 : Limits.IsZero (ModuleCat.of R A) := ModuleCat.isZero_iff_subsingleton.2
    ((Submodule.subsingleton_iff R).1 (subsingleton_of_bot_eq_top h.symm))
  have := h0.hasProjectiveDimensionLT_zero
  hasProjectiveDimensionLT_of_ge _ 0 n (by lia)

end Bounds

section Graded

variable {A B : Type v} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

/-- Membership in `p.submoduleOf q`, unfolded: the side condition `grMap` asks of an inclusion. -/
private lemma subtype_mem_of_mem_submoduleOf {p q : Submodule R A} :
    ∀ x ∈ p.submoduleOf q, q.subtype x ∈ p := fun _ hx => hx

/-- The side condition `grMap` asks of `f`, read off from `f` mapping `a` onto `b`. -/
private lemma mem_of_map_eq {f : A →ₗ[R] B} {a : Submodule R A} {b : Submodule R B}
    (hb : a.map f = b) : ∀ x ∈ a, f x ∈ b := fun _ hx => hb ▸ Submodule.mem_map_of_mem hx

/-- The map `a₁ / a₂ → b₁ / b₂` on graded pieces induced by a linear map `f` mapping `a₁` into
`b₁` and `a₂` into `b₂`. -/
private noncomputable def grMap (f : A →ₗ[R] B) {a₁ a₂ : Submodule R A} {b₁ b₂ : Submodule R B}
    (h₁ : ∀ x ∈ a₁, f x ∈ b₁) (h₂ : ∀ x ∈ a₂, f x ∈ b₂) :
    (↥a₁ ⧸ a₂.submoduleOf a₁) →ₗ[R] (↥b₁ ⧸ b₂.submoduleOf b₁) :=
  Submodule.mapQ _ _ (f.restrict h₁) (fun x hx => h₂ x.1 hx)

private lemma grMap_mk (f : A →ₗ[R] B) {a₁ a₂ : Submodule R A} {b₁ b₂ : Submodule R B}
    (h₁ : ∀ x ∈ a₁, f x ∈ b₁) (h₂ : ∀ x ∈ a₂, f x ∈ b₂) (x : ↥a₁) :
    grMap f h₁ h₂ (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ⟨f x, h₁ x x.2⟩ := rfl

/-- `grMap f` is surjective as soon as `f` carries `a₁` onto `b₁`. -/
private lemma grMap_surjective (f : A →ₗ[R] B) {a₁ a₂ : Submodule R A} {b₁ b₂ : Submodule R B}
    (h₁ : ∀ x ∈ a₁, f x ∈ b₁) (h₂ : ∀ x ∈ a₂, f x ∈ b₂) (hb₁ : a₁.map f = b₁) :
    Function.Surjective (grMap f h₁ h₂) := by
  intro q
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨z, hz, hfz⟩ := show (y : B) ∈ a₁.map f from hb₁ ▸ y.2
  refine ⟨Submodule.Quotient.mk ⟨z, hz⟩, ?_⟩
  rw [grMap_mk, Submodule.mkQ_apply]
  exact congrArg _ (Subtype.ext hfz)

/-- `grMap f` is injective as soon as `f` reflects `a₂` out of `b₂` on `a₁`; injectivity of `f`
itself is not needed. -/
private lemma grMap_injective (f : A →ₗ[R] B) {a₁ a₂ : Submodule R A} {b₁ b₂ : Submodule R B}
    (h₁ : ∀ x ∈ a₁, f x ∈ b₁) (h₂ : ∀ x ∈ a₂, f x ∈ b₂)
    (hinj : ∀ x ∈ a₁, f x ∈ b₂ → x ∈ a₂) : Function.Injective (grMap f h₁ h₂) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro q hq
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  rw [LinearMap.mem_ker, Submodule.mkQ_apply, grMap_mk, Submodule.Quotient.mk_eq_zero] at hq
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hinj _ x.2 hq

/-- The graded pieces of `Ker f` are exactly the kernel of the map on graded pieces induced by
`f`: an `x ∈ a₁` with `f x ∈ b₂ = f(a₂)` differs from an element of `a₂` by an element of
`a₁ ∩ Ker f`. -/
private lemma grMap_ker_subtype_exact (f : A →ₗ[R] B) {a₁ a₂ : Submodule R A} (h21 : a₂ ≤ a₁)
    {b₁ b₂ : Submodule R B} (h₁ : ∀ x ∈ a₁, f x ∈ b₁) (h₂ : ∀ x ∈ a₂, f x ∈ b₂)
    (hb₂ : a₂.map f = b₂) :
    Function.Exact (grMap (LinearMap.ker f).subtype
        (subtype_mem_of_mem_submoduleOf (p := a₁)) (subtype_mem_of_mem_submoduleOf (p := a₂)))
      (grMap f h₁ h₂) := by
  refine fun q => ⟨fun hq => ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
    rw [Submodule.mkQ_apply, grMap_mk, Submodule.Quotient.mk_eq_zero] at hq
    obtain ⟨z, hz, hfz⟩ := show f (x : A) ∈ a₂.map f from hb₂ ▸ hq
    have hker : (x : A) - z ∈ LinearMap.ker f := by simp [LinearMap.mem_ker, hfz]
    refine ⟨Submodule.Quotient.mk ⟨⟨(x : A) - z, hker⟩, sub_mem x.2 (h21 hz)⟩, ?_⟩
    rw [grMap_mk, Submodule.mkQ_apply]
    refine (Submodule.Quotient.eq _).2 ?_
    change ((x : A) - z) - (x : A) ∈ a₂
    simpa using neg_mem hz
  · rintro ⟨p, rfl⟩
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ p
    rw [Submodule.mkQ_apply, grMap_mk, grMap_mk]
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    change f ((y : ↥(LinearMap.ker f)) : A) ∈ b₂
    rw [LinearMap.mem_ker.1 y.1.2]
    exact zero_mem _

/-- The graded pieces of the filtration induced on `Ker f` by a pair of nested submodules
`a₂ ≤ a₁` of the source of `f`: they sit in a short exact sequence with the graded piece
`a₁ / a₂` and the graded piece `f(a₁) / f(a₂)` of the image. -/
private lemma hasProjectiveDimensionLT_gradedKer (f : A →ₗ[R] B) {a₁ a₂ : Submodule R A}
    (h21 : a₂ ≤ a₁) {b₁ b₂ : Submodule R B} (hb₁ : a₁.map f = b₁) (hb₂ : a₂.map f = b₂) (m : ℕ)
    (H₂ : HasProjectiveDimensionLT (ModuleCat.of R (↥a₁ ⧸ a₂.submoduleOf a₁)) m)
    (H₃ : HasProjectiveDimensionLT (ModuleCat.of R (↥b₁ ⧸ b₂.submoduleOf b₁)) (m + 1)) :
    HasProjectiveDimensionLT (ModuleCat.of R (↥(a₁.submoduleOf (LinearMap.ker f)) ⧸
      (a₂.submoduleOf (LinearMap.ker f)).submoduleOf (a₁.submoduleOf (LinearMap.ker f)))) m := by
  have hexact := grMap_ker_subtype_exact f h21 (mem_of_map_eq hb₁) (mem_of_map_eq hb₂) hb₂
  let S : ShortComplex (ModuleCat.{v} R) :=
    { X₁ := ModuleCat.of R (↥(a₁.submoduleOf (LinearMap.ker f)) ⧸
        (a₂.submoduleOf (LinearMap.ker f)).submoduleOf (a₁.submoduleOf (LinearMap.ker f)))
      X₂ := ModuleCat.of R (↥a₁ ⧸ a₂.submoduleOf a₁)
      X₃ := ModuleCat.of R (↥b₁ ⧸ b₂.submoduleOf b₁)
      f := ModuleCat.ofHom (grMap (LinearMap.ker f).subtype
        (subtype_mem_of_mem_submoduleOf (p := a₁)) (subtype_mem_of_mem_submoduleOf (p := a₂)))
      g := ModuleCat.ofHom (grMap f (mem_of_map_eq hb₁) (mem_of_map_eq hb₂))
      zero := by
        ext x
        simpa using hexact.apply_apply_eq_zero (Submodule.Quotient.mk x) }
  refine (ModuleCat.shortComplex_shortExact S hexact ?_ ?_).hasProjectiveDimensionLT_X₁ m H₂ H₃
  · exact grMap_injective _ (subtype_mem_of_mem_submoduleOf (p := a₁))
      (subtype_mem_of_mem_submoduleOf (p := a₂)) fun _ _ h => h
  · exact grMap_surjective f (mem_of_map_eq hb₁) (mem_of_map_eq hb₂) hb₁

end Graded

section Chain

variable {E : Type w} [LinearOrder E] {A : Type v} [AddCommGroup A] [Module R A]

private lemma biSup_lt_eq_iSup_subtype (N : E → Submodule R A) (e : E) :
    (⨆ e' < e, N e') = ⨆ i : {e' : E // e' < e}, N i.1 :=
  le_antisymm (iSup₂_le fun e' he' => le_iSup (fun i : {e' : E // e' < e} => N i.1) ⟨e', he'⟩)
    (iSup_le fun i => le_iSup₂_of_le i.1 i.2 le_rfl)

/-- An element of `⨆ e' < e, N e'`, for a chain `N`, lies in a single `N e'` with `e' < e` —
unless it is zero and no index is `< e`. -/
private lemma mem_biSup_lt {N : E → Submodule R A} (hN : Monotone N) {e : E} {x : A}
    (hx : x ∈ ⨆ e' < e, N e') : x = 0 ∨ ∃ e' < e, x ∈ N e' := by
  rw [biSup_lt_eq_iSup_subtype] at hx
  rcases isEmpty_or_nonempty {e' : E // e' < e} with h | h
  · left
    rw [iSup_of_empty, Submodule.mem_bot] at hx
    exact hx
  · right
    obtain ⟨i, hi⟩ := (Submodule.mem_iSup_of_directed _
      (Monotone.directed_le (f := fun i : {e' : E // e' < e} => N i.1)
        (fun a c hac => hN hac))).1 hx
    exact ⟨i.1, i.2, hi⟩

private lemma submoduleOf_biSup_lt {N : E → Submodule R A} (hN : Monotone N)
    (q : Submodule R A) (e : E) :
    (⨆ e' < e, N e').submoduleOf q = ⨆ e' < e, (N e').submoduleOf q := by
  refine le_antisymm (fun x hx => ?_)
    (iSup₂_le fun e' he' => Submodule.comap_mono (le_iSup₂_of_le e' he' le_rfl))
  rcases mem_biSup_lt hN (show (x : A) ∈ ⨆ e' < e, N e' from hx) with h | ⟨e', he', hmem⟩
  · rw [show x = 0 from Subtype.ext h]
    exact zero_mem _
  · exact Submodule.mem_iSup_of_mem e' (Submodule.mem_iSup_of_mem he' hmem)

private lemma exists_mem_of_iSup_eq_top [Nonempty E] {N : E → Submodule R A} (hN : Monotone N)
    (htop : ⨆ e, N e = ⊤) (x : A) : ∃ e, x ∈ N e :=
  (Submodule.mem_iSup_of_directed N hN.directed_le).1 (htop ▸ Submodule.mem_top)

private lemma submoduleOf_iSup_eq_top [Nonempty E] {N : E → Submodule R A} (hN : Monotone N)
    (htop : ⨆ e, N e = ⊤) (q : Submodule R A) :
    (⨆ e, (N e).submoduleOf q) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨e, he⟩ := exists_mem_of_iSup_eq_top hN htop (x : A)
  exact Submodule.mem_iSup_of_mem e he

end Chain

section Filtration

variable {α : Type*} [CompleteLattice α] {E : Type w} [LT E] [WellFoundedLT E]

/-- **Transfinite induction along a filtration.** An element `p` of a complete lattice which
absorbs every `N e` modulo the earlier stages of the filtration lies above the whole of
`⨆ e, N e`. Only well-foundedness of `<` on the index is used: `N` need not be monotone, and the
order on the index need not be linear. -/
private lemma iSup_le_of_le_biSup_lt_sup {N : E → α} {p : α}
    (h : ∀ e, N e ≤ (⨆ e' < e, N e') ⊔ p) : ⨆ e, N e ≤ p := by
  refine iSup_le fun e => ?_
  induction e using WellFoundedLT.induction with
  | _ e ih => exact (h e).trans (sup_le (iSup₂_le fun e' he' => ih e' he') le_rfl)

end Filtration

section FreeGraded

variable {E : Type w} {F : Type v} [AddCommGroup F] [Module R F]
    {A : Type v} [AddCommGroup A] [Module R A]

private lemma span_image_iUnion {ι : Type*} (b : ι → F) (S : E → Set ι) :
    Submodule.span R (b '' ⋃ e, S e) = ⨆ e, Submodule.span R (b '' S e) := by
  simp only [Set.image_iUnion, Submodule.span_iUnion]

private lemma span_image_biUnion_lt [LT E] {ι : Type*} (b : ι → F) (S : E → Set ι) (e : E) :
    Submodule.span R (b '' ⋃ e' < e, S e') = ⨆ e' < e, Submodule.span R (b '' S e') := by
  simp only [Set.image_iUnion, Submodule.span_iUnion]

/-- A family of subsets of the index type covering it spans the whole free module. -/
private lemma iSup_span_image_eq_top {ι : Type*} (b : Module.Basis ι R F) (S : E → Set ι)
    (hS : ⋃ e, S e = Set.univ) : (⨆ e, Submodule.span R (b '' S e)) = ⊤ := by
  rw [← span_image_iUnion, hS, Set.image_univ, b.span_eq]

/-- A linear map `π` with `π (b a) = a` carries the span of the basis vectors indexed by a set `s`
onto the span of `s`. -/
private lemma map_span_image {b : A → F} (π : F →ₗ[R] A) (hπ : ∀ a, π (b a) = a) (s : Set A) :
    Submodule.map π (Submodule.span R (b '' s)) = Submodule.span R s := by
  rw [Submodule.map_span, Set.image_image]
  simp [hπ]

/-- A quotient of a projective module admitting a retraction of the projection is projective. -/
private lemma projective_quotient_of_retraction {a c : Submodule R F}
    [Module.Projective R ↥a] (ρ : F →ₗ[R] F) (hρa : ∀ x ∈ a, ρ x ∈ a)
    (hρc : ∀ x ∈ c, ρ x = 0) (hρid : ∀ x ∈ a, x - ρ x ∈ c) :
    Module.Projective R (↥a ⧸ c.submoduleOf a) := by
  have hker : c.submoduleOf a ≤ LinearMap.ker (ρ.restrict hρa) := by
    intro x hx
    exact LinearMap.mem_ker.2 (Subtype.ext (hρc _ hx))
  refine Module.Projective.of_split (Submodule.liftQ _ (ρ.restrict hρa) hker)
    (c.submoduleOf a).mkQ (LinearMap.ext fun q => ?_)
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ q
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    Submodule.liftQ_apply, LinearMap.id_coe, id_eq]
  refine (Submodule.Quotient.eq _).2 ?_
  change ρ (x : F) - (x : F) ∈ c
  simpa using neg_mem (hρid _ x.2)

/-- For a basis `b` and subsets `s`, `t` of the index type, the quotient of the span of the basis
vectors indexed by `s` by the span of those indexed by `t` is projective: it is free on `s \ t`. -/
private lemma projective_quotient_span_image {ι : Type*} (b : Module.Basis ι R F) (s t : Set ι) :
    Module.Projective R (↥(Submodule.span R (b '' s)) ⧸
      (Submodule.span R (b '' t)).submoduleOf (Submodule.span R (b '' s))) := by
  classical
  have : Module.Projective R ↥(Submodule.span R (b '' s)) := by
    have hli : LinearIndependent R (fun i : ↥s => b i.1) :=
      b.linearIndependent.comp _ Subtype.val_injective
    rw [Set.image_eq_range]
    exact Module.Projective.of_basis (Module.Basis.span hli)
  have key {u : Set ι} {p : Submodule R F} (g : F →ₗ[R] F) (h : ∀ i ∈ u, g (b i) ∈ p) :
      ∀ x ∈ Submodule.span R (b '' u), g x ∈ p := fun x hx =>
    Submodule.map_span_le _ _ _ |>.2 (by rintro _ ⟨i, hi, rfl⟩; exact h i hi) ⟨x, hx, rfl⟩
  refine projective_quotient_of_retraction (b.constr ℕ fun i => if i ∈ t then 0 else b i)
    (fun x hx => key _ (fun i hi => ?_) x hx) (fun x hx => key (p := ⊥) _ (fun i hi => ?_) x hx)
    (fun x hx => ?_)
  · by_cases h : i ∈ t
    · simp [b.constr_basis, h]
    · simpa [b.constr_basis, h] using Submodule.subset_span (Set.mem_image_of_mem _ hi)
  · simp [b.constr_basis, hi]
  · refine key (LinearMap.id - b.constr ℕ fun i => if i ∈ t then 0 else b i) (fun i hi => ?_) x hx
    by_cases h : i ∈ t
    · simpa [b.constr_basis, h] using Submodule.subset_span (Set.mem_image_of_mem _ h)
    · simp [b.constr_basis, h]

/-- The graded pieces of the filtration of a free module by the spans of the basis vectors indexed
by a monotone family of subsets of the index type are projective. -/
private lemma projective_gradedPiece_span_image [LinearOrder E] {ι : Type*}
    (b : Module.Basis ι R F) (S : E → Set ι) (e : E) :
    Module.Projective R (↥(Submodule.span R (b '' S e)) ⧸
      (⨆ e' < e, Submodule.span R (b '' S e')).submoduleOf (Submodule.span R (b '' S e))) := by
  rw [← span_image_biUnion_lt]
  exact projective_quotient_span_image b (S e) _

end FreeGraded

section Projective

variable {E : Type w} [LinearOrder E] [WellFoundedLT E] {A : Type v} [AddCommGroup A] [Module R A]

omit [WellFoundedLT E] in
/-- A family of maps `τ e` landing in `N e` and injective modulo `⨆ e' < e, N e'` induces an
injective map out of the direct sum: in a nonzero element the component at the largest index of
the support survives, all the others lying in earlier stages of the filtration. -/
private lemma injective_toModule_of_mem_biSup_lt {P : E → Type v} [∀ e, AddCommGroup (P e)]
    [∀ e, Module R (P e)] {N : E → Submodule R A} (τ : ∀ e, P e →ₗ[R] A)
    (hmem : ∀ e (p : P e), τ e p ∈ N e)
    (hinj : ∀ e (p : P e), τ e p ∈ ⨆ e' < e, N e' → p = 0) :
    Function.Injective (DirectSum.toModule R E A τ) := by
  classical
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  rw [LinearMap.mem_ker] at hx
  by_contra hx0
  have hs : x.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    simpa [DFinsupp.support_eq_empty] using hx0
  set em := x.support.max' hs with hem
  have hemmem : em ∈ x.support := x.support.max'_mem hs
  have hsum : ∑ e ∈ x.support, τ e (x e) = 0 := by
    rw [← hx]
    conv_rhs => rw [← DFinsupp.sum_single (f := x)]
    rw [DFinsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun e _ => (DirectSum.toModule_lof R e (x e)).symm
  refine DFinsupp.mem_support_iff.1 hemmem (hinj em (x em) ?_)
  have hneg : τ em (x em) = -∑ e ∈ x.support.erase em, τ e (x e) := by
    rw [eq_neg_iff_add_eq_zero, add_comm, Finset.sum_erase_add _ _ hemmem]
    exact hsum
  rw [hneg]
  refine neg_mem (Submodule.sum_mem _ fun e he => ?_)
  have hlt : e < em := lt_of_le_of_ne (Finset.le_max' _ _ (Finset.mem_of_mem_erase he))
    (Finset.ne_of_mem_erase he)
  exact Submodule.mem_iSup_of_mem e (Submodule.mem_iSup_of_mem hlt (hmem e (x e)))

/-- **Auslander, base case.** A module which is the union of a family of submodules indexed by a
well-ordered type whose graded pieces are all projective is projective: the sections of the
projections assemble into an isomorphism from the direct sum of the graded pieces. Monotonicity of
the family is not needed, the graded piece at `e` being read as a quotient of `N e` by the part of
`⨆ e' < e, N e'` that lies in it. -/
private lemma projective_of_iSup_eq_top {N : E → Submodule R A}
    (htop : ⨆ e, N e = ⊤)
    (hproj : ∀ e, Module.Projective R (↥(N e) ⧸ (⨆ e' < e, N e').submoduleOf (N e))) :
    Module.Projective R A := by
  have hex : ∀ e, ∃ σ : (↥(N e) ⧸ (⨆ e' < e, N e').submoduleOf (N e)) →ₗ[R] ↥(N e),
      ((⨆ e' < e, N e').submoduleOf (N e)).mkQ ∘ₗ σ = LinearMap.id := fun e =>
    have := hproj e
    Module.projective_lifting_property _ LinearMap.id (Submodule.mkQ_surjective _)
  choose σ hσ using hex
  let τ : (e : E) → (↥(N e) ⧸ (⨆ e' < e, N e').submoduleOf (N e)) →ₗ[R] A :=
    fun e => (N e).subtype ∘ₗ σ e
  have hmkσ : ∀ (e : E) (q : ↥(N e) ⧸ (⨆ e' < e, N e').submoduleOf (N e)),
      ((⨆ e' < e, N e').submoduleOf (N e)).mkQ (σ e q) = q :=
    fun e q => by simpa using LinearMap.congr_fun (hσ e) q
  have hψlof : ∀ (e : E) (q : ↥(N e) ⧸ (⨆ e' < e, N e').submoduleOf (N e)),
      DirectSum.toModule R E A τ (DirectSum.lof R E _ e q) = τ e q := fun e q =>
    DirectSum.toModule_lof (M := fun e => ↥(N e) ⧸ (⨆ e' < e, N e').submoduleOf (N e)) R e q
  have hinj : Function.Injective (DirectSum.toModule R E A τ) :=
    injective_toModule_of_mem_biSup_lt τ (fun e q => (σ e q).2) fun e q hq => by
      rw [← hmkσ e q, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact hq
  have hsurj : Function.Surjective (DirectSum.toModule R E A τ) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← htop]
    refine iSup_le_of_le_biSup_lt_sup fun e x hx => ?_
    have h1 : x - (σ e (Submodule.Quotient.mk ⟨x, hx⟩) : A) ∈ ⨆ e' < e, N e' := by
      have h0 : (⟨x, hx⟩ : ↥(N e)) - σ e (Submodule.Quotient.mk ⟨x, hx⟩) ∈
          (⨆ e' < e, N e').submoduleOf (N e) := by
        rw [← Submodule.Quotient.eq]
        exact (hmkσ e _).symm
      simpa [Submodule.submoduleOf] using h0
    have h2 : (σ e (Submodule.Quotient.mk ⟨x, hx⟩) : A) ∈
        LinearMap.range (DirectSum.toModule R E A τ) := ⟨DirectSum.lof R E _ e _, hψlof e _⟩
    simpa using add_mem (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)
  have : ∀ e, Module.Projective R (↥(N e) ⧸ (⨆ e' < e, N e').submoduleOf (N e)) := hproj
  exact Module.Projective.of_equiv' (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩)

end Projective

section Main

variable [Small.{v} R] {E : Type w} [LinearOrder E] [WellFoundedLT E] [Nonempty E]

/-- **Auslander's theorem**, in the form the induction needs: the ambient module is an arbitrary
`R`-module in `Type v`, and the index type is fixed. -/
private theorem hasProjectiveDimensionLT_of_monotone :
    ∀ (n : ℕ) (A : Type v) [AddCommGroup A] [Module R A] (N : E → Submodule R A),
      Monotone N → (⨆ e, N e = ⊤) →
      (∀ e, HasProjectiveDimensionLT
        (ModuleCat.of R (↥(N e) ⧸ (⨆ e' < e, N e').submoduleOf (N e))) n) →
      HasProjectiveDimensionLT (ModuleCat.of R A) n := by
  intro n
  induction n with
  | zero =>
    intro A _ _ N _hN htop hgr
    refine hasProjectiveDimensionLT_of_top_eq_bot (le_bot_iff.1 ?_) 0
    rw [← htop]
    refine iSup_le_of_le_biSup_lt_sup fun e => le_sup_of_le_left ?_
    have h2 := hgr e
    rw [hasProjectiveDimensionLT_zero_iff_isZero, ModuleCat.isZero_iff_subsingleton,
      Submodule.Quotient.subsingleton_iff] at h2
    simpa only [Submodule.submoduleOf, Submodule.comap_subtype_eq_top] using h2
  | succ n ih =>
    obtain _ | m := n
    · intro A _ _ N _hN htop hgr
      have : Module.Projective R A := projective_of_iSup_eq_top htop fun e =>
        (IsProjective.iff_projective _).2 (projective_iff_hasProjectiveDimensionLT_one.2 (hgr e))
      infer_instance
    · intro A _ _ N hN htop hgr
      let b : Module.Basis A R (A →₀ Shrink.{v} R) :=
        ⟨Finsupp.mapRange.linearEquiv (Shrink.linearEquiv.{v} R R)⟩
      let π : (A →₀ Shrink.{v} R) →ₗ[R] A := b.constr ℕ id
      have hπb : ∀ a : A, π (b a) = a := fun a => b.constr_basis ℕ id a
      have hFmono : Monotone (fun e => Submodule.span R (b '' (N e : Set A))) :=
        fun _ _ h => Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.2 (hN h)))
      have hFtop := iSup_span_image_eq_top b (fun e => (N e : Set A))
        (Set.eq_univ_of_forall fun a => Set.mem_iUnion.2 (exists_mem_of_iSup_eq_top hN htop a))
      have : Module.Projective R (A →₀ Shrink.{v} R) := Module.Projective.of_basis b
      have hK : HasProjectiveDimensionLT (ModuleCat.of R ↥(LinearMap.ker π)) (m + 1) := by
        refine ih ↥(LinearMap.ker π)
          (fun e => (Submodule.span R (b '' (N e : Set A))).submoduleOf (LinearMap.ker π))
          (fun _ _ h => Submodule.comap_mono (hFmono h))
          (submoduleOf_iSup_eq_top hFmono hFtop _) fun e => ?_
        rw [← submoduleOf_biSup_lt hFmono (LinearMap.ker π) e]
        refine hasProjectiveDimensionLT_gradedKer π (iSup₂_le fun e' he' => hFmono he'.le)
          ((map_span_image π hπb _).trans (N e).span_eq) ?_ (m + 1) ?_ (hgr e)
        · rw [← span_image_biUnion_lt, map_span_image π hπb]
          simp only [Submodule.span_iUnion, Submodule.span_eq]
        · have := projective_gradedPiece_span_image b (fun e => (N e : Set A)) e
          exact hasProjectiveDimensionLT_of_projective m
      exact (LinearMap.shortExact_shortComplexKer
        (fun a => ⟨b a, hπb a⟩)).hasProjectiveDimensionLT_X₃ (m + 1) hK
          (hasProjectiveDimensionLT_of_projective (m + 1))

end Main

/-- If `M` is the union `⨆ e, N e = ⊤` of a monotone family of submodules indexed by a
well-ordered type and every graded piece `N e ⧸ ⨆ e' < e, N e'` has projective dimension
`< n`, then so does `M`. -/
public theorem solution {R : Type u} [Ring R]
    [Small.{v} R] {M : ModuleCat.{v} R} {E : Type w} [LinearOrder E] [WellFoundedLT E]
    (N : E → Submodule R M) (hN : Monotone N) (hNtop : ⨆ e, N e = ⊤) (n : ℕ)
    (hquot : ∀ e, HasProjectiveDimensionLT
      (ModuleCat.of R (↥(N e) ⧸ (⨆ e' < e, N e').submoduleOf (N e))) n) :
    HasProjectiveDimensionLT M n := by
  rcases isEmpty_or_nonempty E with hE | hE
  · exact hasProjectiveDimensionLT_of_top_eq_bot (by rw [← hNtop, iSup_of_empty]) n
  · exact hasProjectiveDimensionLT_of_monotone n ↥M N hN hNtop hquot

end Stacks.ProjectiveDimension.FiltrationBound

/-!
# Projective dimension along a well-ordered filtration

Let `R` be a ring and let `M` be an `R`-module written as a union `M = ⋃_{e ∈ E} M_e` of submodules
which increase along a well-ordered index set `E`. The *graded pieces* of such a filtration are the
quotients `M_e / ⋃_{e' < e} M_{e'}`, and the theorem of this file, due to Auslander, is that they
control the projective dimension of `M`: if every graded piece has projective dimension `< n`, then
so does `M`. The proof is by induction on `n`. For the bottom case the graded pieces are
projective, a section `M_e / ⋃_{e' < e} M_{e'} → M_e` of each projection assembles into
an isomorphism `⨁_e M_e / ⋃_{e' < e} M_{e'} ≅ M` (injectivity by looking at the largest
index occurring in a nonzero element, surjectivity by transfinite induction), and a
direct sum of projectives is projective (Tag 065Q). For the inductive step one puts the
free module `F_e` on the underlying set of `M_e` over `M_e`, so that the kernels `K_e`
form a filtration of `K = ⋃_e K_e` with
`0 → K_e / ⋃_{e' < e} K_{e'} → F_e / ⋃_{e' < e} F_{e'} → M_e / ⋃_{e' < e} M_{e'} → 0`
short exact and the middle term free; the graded pieces of `K` therefore have projective dimension
one less (Tag 065S), so `K` does by induction, and `0 → K → F → M → 0` gives the bound for `M`.

The main application is that the global dimension of `R` is computed by the cyclic modules `R/I`
(Tag 065T): a well-ordering of a set of generators of `M` filters `M` by submodules whose graded
pieces are cyclic.

## Main results

* `ModuleCat.hasProjectiveDimensionLT_of_monotone_of_iSup_eq_top`: a module exhausted by a monotone
  family of submodules indexed by a well-ordered type has projective dimension `< n` as soon as all
  the graded pieces of that family do.

## Implementation notes

The source's family of "submodules well-ordered by inclusion" is spelled as a `Monotone` family
`N : E → Submodule R M` over a type `E` with `[LinearOrder E] [WellFoundedLT E]`, that is, over a
well-ordered index set. This is no restriction: a set of submodules well ordered by inclusion is
indexed monotonically by itself, and conversely the image of a monotone family over a well-ordered
type is well ordered by inclusion. `Monotone N` is moreover exactly the hypothesis the statement
uses, since over a linear order `⨆ e' < e, N e' ≤ N e` for all `e` is equivalent to it. The union
`M = ⋃_e M_e` is `⨆ e, N e = ⊤`; over a nonempty index this is the source's set-theoretic union,
by `Submodule.mem_iSup_of_directed`, and over an empty one both readings say that `M` is zero.

The graded piece at `e` is `↥(N e) ⧸ (⨆ e' < e, N e').submoduleOf (N e)`, where
`Submodule.submoduleOf p q = p.comap q.subtype` views `p` inside `q`; monotonicity gives
`⨆ e' < e, N e' ≤ N e`, so this is the source's quotient `M_e / ⋃_{e' < e} M_{e'}` and not merely a
quotient by an intersection.

The conclusion is indexed by `HasProjectiveDimensionLT M n` rather than by the source's `≤ n`,
as in Tag 065R and as everywhere in Mathlib's `CategoryTheory.Abelian.Projective.Dimension`, since
`HasProjectiveDimensionLE M n` is by definition `HasProjectiveDimensionLT M (n + 1)`: the source's
statement is the case `n + 1`, and the extra case `n = 0` is the true statement that a module
exhausted by such a filtration with vanishing graded pieces is itself zero (each `N e` is `⊥` by
transfinite induction). Because it holds for every `n`, the statement also gives the inequality
`projectiveDimension M ≤ ⨆ e, projectiveDimension (M_e / ⋃_{e' < e} M_{e'})` in `WithBot ℕ∞`, by
`CategoryTheory.projectiveDimension_lt_iff`, the value `⊥` of the supremum being the case `n = 0`;
so no generality is lost against the supremum form used to define the global dimension (Tag 00O6).

A family that does not exhaust `M` is covered by applying the statement to the module
`↥(⨆ e, N e)` and the family `fun e ↦ (N e).submoduleOf (⨆ e, N e)`, whose graded pieces agree with
those of `N` under `Submodule.submoduleOfEquivOfLe`.

`Small.{v} R` is what makes `ModuleCat.{v} R` have enough projectives, by free modules on sets in
`Type v` — the resolutions the proof builds; it is automatic when the module lives in `R`'s own
universe, which is the convention of Tags 00O6 and 065T, so those are the case `v = u`. The source
works with commutative rings, but neither the statement nor the argument uses commutativity, so
only `[Ring R]` is assumed, `ModuleCat R` being the left modules.

Faithfulness to the source. (1) No hypothesis is idle: `hNtop` is what makes the conclusion about
`M` rather than about `⨆ e, N e` (without it the constant family `⊥` satisfies everything over any
`M`), `hN` is what puts `⨆ e' < e, N e'` inside `N e` and so makes the graded pieces the
source's quotients, `hquot` is the source's assumption, and the well-ordering of `E` is what the
transfinite induction consumes. (2) The scalars and the base are the source's: the submodules are
`R`-submodules of the `R`-module `M` and the projective dimensions are those of `ModuleCat R`, with
no localization or quotient of `R` substituted. (3) The source names no canonical map; what it does
name is pinned — the union as the equation `⨆ e, N e = ⊤` of submodules of `M`, and each graded
piece as the quotient of `N e` by the actual `⨆ e' < e, N e'`, not by an abstract colimit. (4) The
instantiation is not degenerate: for `E = ℕ` and `N k` the span of the first `k` basis vectors of
`M = ⨁_{i : ℕ} R` the graded pieces are `R` or `0`, and the case `n = 1` says that this countable
direct sum is projective; and Tag 065T instantiates it with `E` a well-ordering of a set of
generators of an arbitrary module, where the graded pieces are the cyclic modules `R/I`.

## References

* [Stacks Project, Tag 0D1U](https://stacks.math.columbia.edu/tag/0D1U)
* M. Auslander, *On the dimension of modules and algebras. III. Global dimension*,
  Nagoya Math. J. **9** (1955), 67-77 — the source's `\cite{Auslander}`, where the argument is.
-/

@[expose] public section



open CategoryTheory in
/-- **Stacks 0D1U.** Let `R` be a ring and let `M` be an `R`-module which is the union
`⨆ e, N e = ⊤` of a monotone family of submodules `N` indexed by a well-ordered type `E`. If each
graded piece `N e ⧸ ⨆ e' < e, N e'` has projective dimension `< n`, then so does `M`. -/
@[stacks 0D1U "Indexed by `HasProjectiveDimensionLT _ n`, so that the source's `≤ n` is the case
`n + 1`; the source's well-ordered family of submodules is a `Monotone` family over a type with
`[LinearOrder E] [WellFoundedLT E]`, its union is `⨆ e, N e = ⊤`, and the graded piece at `e` is
`↥(N e) ⧸ (⨆ e' < e, N e').submoduleOf (N e)`. See the module docstring."]
public theorem ModuleCat.hasProjectiveDimensionLT_of_monotone_of_iSup_eq_top {R : Type u} [Ring R]
    [Small.{v} R] {M : ModuleCat.{v} R} {E : Type w} [LinearOrder E] [WellFoundedLT E]
    (N : E → Submodule R M) (hN : Monotone N) (hNtop : ⨆ e, N e = ⊤) (n : ℕ)
    (hquot : ∀ e, HasProjectiveDimensionLT
      (ModuleCat.of R (↥(N e) ⧸ (⨆ e' < e, N e').submoduleOf (N e))) n) :
    HasProjectiveDimensionLT M n :=
  Stacks.ProjectiveDimension.FiltrationBound.solution N hN hNtop n hquot

end
