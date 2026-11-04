module

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
public import StacksFrontier.SetTheory.Cardinal.SizeBound

/-!
# Size-bounded `G`-sets

## Closure properties of the size-bounded `G`-sets (Stacks 000V)

Fix a group `G`. A `G`-set is a type `S` with `[MulAction G S]`, and `G-Sets` is the
category of `G`-sets and `G`-equivariant maps. Stacks 000V is phrased in terms of the von
Neumann cumulative hierarchy `V_α` and the full subcategory `G-Sets_α ⊆ G-Sets` of `G`-sets
lying in `V_α`. Mathlib has no cumulative hierarchy, and the ordinal `α` of Stacks 000U
enters only through its consequences, so "`S` is an object of `G-Sets_α`" is modelled here
by the cardinal-arithmetic invariant that drives the omitted proof.

### Main definitions

* `gsetSize G S`, the size function of Stacks 000T: `size S = max {ℵ₀, #G, #S}`.
* `AdmissibleBound G κ`, the three properties of a cutoff cardinal `κ` extracted from
  Stacks 000U: `max {ℵ₀, #G} < κ`, closure under `lam ↦ lam ^ ℵ₀`, and uncountable
  cofinality of `κ.ord`.
* `Sk G κ S`, the model of "`S` is an object of `G-Sets_α`": `size S < κ`.

### Main results

* `Sk_leftRegular`: the left regular `G`-set `{}_G G` lies below the cutoff — clause (1).
* `Sk_prod`, `Sk_sum`, `Sk_fibreProduct`, `Sk_pushout`, `Sk_sigma`, `Sk_pi`: closure under
  binary products and coproducts, fibre products, pushouts and at-most-countable products
  and coproducts — clause (2).
* `Sk_subtype`: closure under `G`-stable subsets — clause (3).

Every `Sk` claim unfolds to `max (max ℵ₀ #G) #S < κ`, which `max_lt` splits into condition
`B1` and a bound `#S < κ` on the underlying type. So each statement below reduces, through
`Sk_of_mk_lt`, to a cardinality estimate for the underlying type; the group actions and the
maps in the diagrams play no role in it.

The *existence* of a cutoff, which is Stacks 000U, is `exists_admissibleBound` below.

## A size cutoff for the category of `G`-sets (Stacks 000U)

Let `G` be a group. Stacks 000U fixes, for a given set `S₀` of `G`-sets, a limit ordinal
`α` such that the full subcategory `G-Sets_α ⊆ G-Sets` of `G`-sets lying in `V_α`

1. contains `S₀` together with the left regular `G`-set `{}_G G`;
2. is closed under passing to any `G`-set of size at most `Bound(size S) = size(S) ^ ℵ₀`
   for `S ∈ G-Sets_α`;
3. has all countable limits and colimits, computed as in `G-Sets`.

### Modelling `G-Sets_α`

We use the modelling already fixed for Stacks 000V above:
`size S = max {ℵ₀, |G|, |S|}` is `gsetSize G S`, and "`S` is an object of `G-Sets_α`" is
`Sk G κ S`, that is `gsetSize G S < κ` for a cutoff cardinal `κ`. That part records the
three properties of the cutoff it needs as `AdmissibleBound G κ` and derives clause (3)
from them, but leaves the *existence* of a cutoff — which is what Stacks 000U asserts —
unproved. This part supplies it, so that every statement of Stacks 000V applies to an
actual cardinal.

Since `gsetSize G S` depends on the `G`-set `S` only through its underlying type, the
statements below are about families of types; no group action is needed to formulate or to
prove them.

### Main results

* `exists_admissibleBound`: for every family `S₀` of `G`-sets there is an admissible cutoff
  `κ` — a strong limit cardinal of uncountable cofinality above `max {ℵ₀, |G|}` and above
  the sizes of the members of `S₀`. This is clauses (1) and (2), the latter also isolated
  as `Sk_of_le_power_aleph0`; clause (3) is then Stacks 000V (`Sk_pi`, `Sk_sigma`,
  `Sk_subtype`, `Sk_fibreProduct`, `Sk_pushout`, `Sk_prod`, `Sk_sum`), which take exactly
  an `AdmissibleBound` as their hypothesis.

The source's proof is "omitted, similar to but easier than the proof of Lemma 000J". The
construction here is indeed the one used for Stacks 000J, in
`StacksFrontier.AlgebraicGeometry.Size.Cutoff`: a beth number at a limit index shifted by `ω₁`.
Easier, because the bound function is `Bound(κ) = κ ^ ℵ₀` rather than
`max {κ ^ ℵ₀, κ⁺}`, and the size of a `G`-set is just the cardinality of its underlying
type.
-/

@[expose] public section

universe u

open Cardinal

/-- The size of a `G`-set `S` in the sense of Stacks 000T: `size S = max {ℵ₀, #G, #S}`. It
depends on `S` only through its underlying type. -/
noncomputable def gsetSize (G : Type u) (S : Type u) : Cardinal.{u} :=
  max (max ℵ₀ #G) #S

/-- An admissible bound for `G` is a cutoff cardinal `κ` carrying the three properties of
the limit ordinal `α` of Stacks 000U that Stacks 000V actually uses. -/
structure AdmissibleBound (G : Type u) (κ : Cardinal.{u}) : Prop where
  /-- (B1) the base size `max {ℵ₀, #G}` lies below the cutoff. -/
  B1 : max ℵ₀ #G < κ
  /-- (B2) the cutoff is closed under the Stacks bound function `Bound lam = lam ^ ℵ₀`. -/
  B2 : ∀ lam : Cardinal.{u}, lam < κ → lam ^ ℵ₀ < κ
  /-- (B3) the cutoff has uncountable cofinality. -/
  B3 : ℵ₀ < κ.ord.cof

/-- The model of "the `G`-set `S` is (isomorphic to) an object of `G-Sets_α`": the size of
`S` lies below the cutoff `κ`. -/
def Sk (G : Type u) (κ : Cardinal.{u}) (S : Type u) : Prop :=
  gsetSize G S < κ

/-- The left regular `G`-set `{}_G G` is the type `G` with `G` acting on itself by left
multiplication, i.e. the canonical `MulAction G G`. -/
example (G : Type u) [Group G] : MulAction G G := inferInstance

/-- `Sk G κ S` holds as soon as the underlying cardinal `#S` is below `κ`: the `max {ℵ₀, #G}`
part of the size is below `κ` by `B1`. -/
theorem Sk_of_mk_lt {G : Type u} {κ : Cardinal.{u}} {S : Type u}
    (hκ : AdmissibleBound G κ) (h : #S < κ) : Sk G κ S :=
  max_lt hκ.B1 h

/-- `ℵ₀` lies below an admissible bound, being the left factor of `B1`. -/
theorem aleph0_lt_of_admissibleBound {G : Type u} {κ : Cardinal.{u}} (hκ : AdmissibleBound G κ) :
    ℵ₀ < κ :=
  (le_max_left _ _).trans_lt hκ.B1

/-- From `Sk G κ S` extract the bound `#S < κ` on the underlying type. -/
theorem mk_lt_of_Sk {G : Type u} {κ : Cardinal.{u}} {S : Type u}
    (h : Sk G κ S) : #S < κ :=
  (le_max_right _ _).trans_lt h

/-- If `S` and `T` lie below the cutoff, so does `S × T`. -/
private theorem mk_prod_lt_of_Sk {G : Type u} {κ : Cardinal.{u}} {S T : Type u}
    (hκ : AdmissibleBound G κ) (hS : Sk G κ S) (hT : Sk G κ T) : #(S × T) < κ := by
  rw [← Cardinal.mul_def]
  exact (Cardinal.mul_le_max _ _).trans_lt <|
    max_lt (max_lt (mk_lt_of_Sk hS) (mk_lt_of_Sk hT)) (aleph0_lt_of_admissibleBound hκ)

/-- If `S` and `T` lie below the cutoff, so does `S ⊕ T`. -/
private theorem mk_sum_lt_of_Sk {G : Type u} {κ : Cardinal.{u}} {S T : Type u}
    (hκ : AdmissibleBound G κ) (hS : Sk G κ S) (hT : Sk G κ T) : #(S ⊕ T) < κ := by
  simp only [mk_sum, lift_id]
  exact (Cardinal.add_le_max _ _).trans_lt <|
    max_lt (max_lt (mk_lt_of_Sk hS) (mk_lt_of_Sk hT)) (aleph0_lt_of_admissibleBound hκ)

/-- A supremum of at most countably many cardinals `#(S i)` below the cutoff is below it. -/
private theorem iSup_mk_lt_of_Sk {G : Type u} {κ : Cardinal.{u}} {ι : Type u}
    (hκ : AdmissibleBound G κ) (hι : #ι ≤ ℵ₀) {S : ι → Type u} (hS : ∀ i, Sk G κ (S i)) :
    (⨆ i, #(S i)) < κ :=
  iSup_lt_of_lt_cof_ord (hι.trans_lt hκ.B3) fun i => mk_lt_of_Sk (hS i)

/-- **Stacks 000V (1)**. The left regular `G`-set `{}_G G` is an object of `G-Sets_α`, since
its size is `max {ℵ₀, #G}`, which is below the cutoff by `B1`. -/
@[stacks 000V "(1)"]
theorem Sk_leftRegular (G : Type u) [Group G] (κ : Cardinal.{u})
    (hκ : AdmissibleBound G κ) :
    Sk G κ G :=
  Sk_of_mk_lt hκ ((le_max_right _ _).trans_lt hκ.B1)

/-- **Stacks 000V (2)**. The product `S × T` of two `G`-sets below the cutoff, with the
diagonal `G`-action, is again below it: `#(S × T) = #S * #T ≤ max {max {#S, #T}, ℵ₀} < κ`. -/
@[stacks 000V "(2)"]
theorem Sk_prod (G : Type u) [Group G] (κ : Cardinal.{u})
    (hκ : AdmissibleBound G κ) (S T : Type u) [MulAction G S] [MulAction G T]
    (hS : Sk G κ S) (hT : Sk G κ T) :
    Sk G κ (S × T) :=
  Sk_of_mk_lt hκ (mk_prod_lt_of_Sk hκ hS hT)

/-- **Stacks 000V (2)**. The coproduct `S ⊕ T` of two `G`-sets below the cutoff, with the
disjoint-union `G`-action, is again below it:
`#(S ⊕ T) = #S + #T ≤ max {max {#S, #T}, ℵ₀} < κ`. -/
@[stacks 000V "(2)"]
theorem Sk_sum (G : Type u) [Group G] (κ : Cardinal.{u})
    (hκ : AdmissibleBound G κ) (S T : Type u) [MulAction G S] [MulAction G T]
    (hS : Sk G κ S) (hT : Sk G κ T) :
    Sk G κ (S ⊕ T) :=
  Sk_of_mk_lt hκ (mk_sum_lt_of_Sk hκ hS hT)

/-- **Stacks 000V (2)**. For `G`-sets `S`, `T`, `R` below the cutoff and equivariant maps
`f : S → R`, `h : T → R`, the fibre product `S ×_R T = {p : S × T // f p.1 = h p.2}` is
below the cutoff, being a subtype of `S × T`. -/
@[stacks 000V "(2)"]
theorem Sk_fibreProduct (G : Type u) [Group G] (κ : Cardinal.{u})
    (hκ : AdmissibleBound G κ) (S T R : Type u)
    [MulAction G S] [MulAction G T] [MulAction G R]
    (hS : Sk G κ S) (hT : Sk G κ T)
    (f : S → R) (h : T → R) :
    Sk G κ { p : S × T // f p.1 = h p.2 } :=
  Sk_of_mk_lt hκ <| (mk_subtype_le _).trans_lt (mk_prod_lt_of_Sk hκ hS hT)

/-- **Stacks 000V (2)**. For `G`-sets `S`, `T`, `R` below the cutoff and equivariant maps
`f : R → S`, `h : R → T`, the pushout of `S ← R → T` is below the cutoff, being a quotient
of `S ⊕ T`. The pushout is modelled as the quotient of `S ⊕ T` by the equivalence relation
generated by `inl (f r) ~ inr (h r)`. -/
@[stacks 000V "(2)"]
theorem Sk_pushout (G : Type u) [Group G] (κ : Cardinal.{u})
    (hκ : AdmissibleBound G κ) (S T R : Type u)
    [MulAction G S] [MulAction G T] [MulAction G R]
    (hS : Sk G κ S) (hT : Sk G κ T)
    (f : R → S) (h : R → T) :
    Sk G κ
      (Quotient
        (Relation.EqvGen.setoid
          (fun a b : S ⊕ T =>
            ∃ r : R, a = Sum.inl (f r) ∧ b = Sum.inr (h r)))) :=
  Sk_of_mk_lt hκ <| mk_quotient_le.trans_lt (mk_sum_lt_of_Sk hκ hS hT)

/-- **Stacks 000V (2)**. For an at-most-countable index type `ι` and a family of `G`-sets
`S i` below the cutoff, the coproduct `Σ i, S i` with the fibrewise `G`-action is below the
cutoff: `#(Σ i, S i) = Σ i, #(S i) ≤ #ι * ⨆ i, #(S i)`, and a supremum of at most `ℵ₀` many
cardinals below `κ` is below `κ` because `κ.ord` has uncountable cofinality (`B3`). -/
@[stacks 000V "(2)"]
theorem Sk_sigma (G : Type u) [Group G] (κ : Cardinal.{u})
    (hκ : AdmissibleBound G κ) (ι : Type u) (hι : #ι ≤ ℵ₀)
    (S : ι → Type u) [∀ i, MulAction G (S i)] (hS : ∀ i, Sk G κ (S i)) :
    Sk G κ (Σ i, S i) :=
  Sk_of_mk_lt hκ <| by
    have ha := aleph0_lt_of_admissibleBound hκ
    have hsup := iSup_mk_lt_of_Sk hκ hι hS
    rw [mk_sigma]
    exact (sum_le_mk_mul_iSup _).trans_lt <| (Cardinal.mul_le_max _ _).trans_lt <|
      max_lt (max_lt (hι.trans_lt ha) hsup) ha

/-- **Stacks 000V (2)**. For an at-most-countable index type `ι` and a family of `G`-sets
`S i` below the cutoff, the product `Π i, S i` with the pointwise `G`-action is below the
cutoff: writing `s = ⨆ i, #(S i)`, which is below `κ` by `B3`, one has
`#(Π i, S i) = Π i, #(S i) ≤ s ^ #ι ≤ s ^ ℵ₀ < κ` by `B2`. If `s = 0` the bound is instead
the trivial `s ^ #ι ≤ 1 < ℵ₀ < κ`. -/
@[stacks 000V "(2)"]
theorem Sk_pi (G : Type u) [Group G] (κ : Cardinal.{u})
    (hκ : AdmissibleBound G κ) (ι : Type u) (hι : #ι ≤ ℵ₀)
    (S : ι → Type u) [∀ i, MulAction G (S i)] (hS : ∀ i, Sk G κ (S i)) :
    Sk G κ (∀ i, S i) :=
  Sk_of_mk_lt hκ <| by
    rw [mk_pi]
    set s := ⨆ i, #(S i)
    have hs : s < κ := iSup_mk_lt_of_Sk hκ hι hS
    have h1 : Cardinal.prod (fun i => #(S i)) ≤ s ^ #ι := by
      rw [← Cardinal.prod_const']
      exact Cardinal.prod_le_prod _ _ fun i => le_ciSup Cardinal.bddAbove_of_small i
    by_cases hz : s = 0
    · refine (h1.trans ?_).trans_lt (one_lt_aleph0.trans (aleph0_lt_of_admissibleBound hκ))
      rw [hz]
      exact Cardinal.zero_power_le _
    · exact (h1.trans (Cardinal.power_le_power_left hz hι)).trans_lt (hκ.B2 s hs)

/-- **Stacks 000V (3)**. For a `G`-set `U` below the cutoff and a `G`-stable subset `O ⊆ U`,
the induced `G`-set on `{x : U // x ∈ O}` is below the cutoff, being a subtype of `U`. -/
@[stacks 000V "(3)"]
theorem Sk_subtype (G : Type u) [Group G] (κ : Cardinal.{u})
    (hκ : AdmissibleBound G κ) (U : Type u) [MulAction G U]
    (hU : Sk G κ U) (O : Set U) :
    Sk G κ { x : U // x ∈ O } :=
  Sk_of_mk_lt hκ ((mk_subtype_le _).trans_lt (mk_lt_of_Sk hU))

/-- **Stacks 000U (2).** For an admissible cutoff `κ`, if `S` is an object of `G-Sets_α`
and `T` is a `G`-set with `size T ≤ Bound(size S) = size(S) ^ ℵ₀`, then `T` is an object of
`G-Sets_α`. This is condition `B2` of `AdmissibleBound` read through `Sk`. -/
@[stacks 000U "(2)"]
theorem Sk_of_le_power_aleph0 {G : Type u} {κ : Cardinal.{u}} (hκ : AdmissibleBound G κ)
    {S T : Type u} (hS : Sk G κ S) (hT : gsetSize G T ≤ gsetSize G S ^ ℵ₀) : Sk G κ T :=
  lt_of_le_of_lt hT (hκ.B2 _ hS)

/-- **Stacks 000U.** For every group `G` and every family `S₀` of `G`-sets there is a
cardinal `κ` which is an admissible cutoff for `G` and for which every member of `S₀`, as
well as the left regular `G`-set `{}_G G`, is an object of `G-Sets_α`; moreover `G-Sets_α`
is closed under `G`-sets of size at most `Bound` of the size of one of its objects.

`Cardinal.IsStrongPrelimit κ` records that `κ` is a limit cardinal, the counterpart of the
source's "`α` is a limit ordinal"; it is also what gives condition `B2` of
`AdmissibleBound`. -/
@[stacks 000U]
theorem exists_admissibleBound (G : Type u) {ι : Type u} (S₀ : ι → Type u) :
    ∃ κ : Cardinal.{u}, Cardinal.IsStrongPrelimit κ ∧ AdmissibleBound G κ ∧
      Sk G κ G ∧ (∀ i, Sk G κ (S₀ i)) ∧
      ∀ S T : Type u, Sk G κ S → gsetSize G T ≤ gsetSize G S ^ ℵ₀ → Sk G κ T := by
  obtain ⟨κ, hμ, hsl, hcof⟩ :=
    Cardinal.exists_isStrongPrelimit_gt_of_aleph0_lt_cof
      (max (max ℵ₀ #G) (⨆ i, #(S₀ i)))
  have hbase : max ℵ₀ #G < κ := lt_of_le_of_lt (le_max_left _ _) hμ
  have hκ0 : ℵ₀ < κ := lt_of_le_of_lt (le_max_left _ _) hbase
  have hB : AdmissibleBound G κ :=
    { B1 := hbase
      B2 := fun _ h => Cardinal.power_aleph0_lt_of_isStrongPrelimit hκ0 hsl h
      B3 := hcof }
  refine ⟨κ, hsl, hB, Sk_of_mk_lt hB (lt_of_le_of_lt (le_max_right _ _) hbase),
    fun i => Sk_of_mk_lt hB ?_, fun _ _ hS hT => Sk_of_le_power_aleph0 hB hS hT⟩
  exact lt_of_le_of_lt
    (le_trans (le_ciSup (f := fun i => #(S₀ i)) Cardinal.bddAbove_of_small i)
      (le_max_right _ _)) hμ
