module

public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.CategoryTheory.Sites.Pretopology
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.UnitInterval
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-compact objects and finite refinements of coverings

Stacks tag 0D05.  For an object `U` of a site presented by a pretopology compare three
properties: (1) `U` is quasi-compact — every covering of `U` is refined by a covering whose
refinement map has finite image (tag 090H); (2) every covering of `U` is refined by a covering
with finitely many arrows; (3) every covering of `U` contains a finite sub-presieve which is
still a covering.  Then (3) ⇒ (2) ⇒ (1), and neither converse holds.  Both counterexamples are
sites of opens of `[0,1]`, whose lattice of opens is atomless: this is what makes the covering
families "contains every rung of a chain of proper opens" stable under pullback.  An increasing
chain separates (2) from (3); a decreasing chain, whose maximal rung dominates the admissible
covers, separates (1) from (2).
-/

@[expose] public section

open CategoryTheory

namespace StacksProblem

variable {C : Type*} [Category C] [Limits.HasPullbacks C]

/-- The underlying *set of arrows* of a presieve `S` with target `U`, presented
as a set of dependent pairs `(Y, f : Y ⟶ U)`. -/
def Presieve.arrowSet {U : C} (S : Presieve U) : Set (Σ Y : C, Y ⟶ U) :=
  { p | S p.2 }

/-- `V` *refines* `S`: every arrow `g : W ⟶ U` of `V` factors through some arrow
`f : Y ⟶ U` of `S`, i.e. there is `h : W ⟶ Y` with `h ≫ f = g`. -/
def Refines {U : C} (V S : Presieve U) : Prop :=
  ∀ ⦃W : C⦄ (g : W ⟶ U), V g → ∃ (Y : C) (f : Y ⟶ U) (h : W ⟶ Y), S f ∧ h ≫ f = g

/-- **Definition 1 (Quasi-compact — Stacks 090H).** `U` is *quasi-compact* if for
every covering `S` of `U` there is a covering `V` of `U` together with a finite
set `F` of arrows of `S` (the finite image of the refinement map) such that every
arrow `g` of `V` factors through some arrow of `F`. -/
@[sga "4 IV 8.7" "more general", sga "4 IX 1.2", sga "4 VI 1.1", sga "6 II 2.1.1"]
def IsQuasiCompact (K : Pretopology C) (U : C) : Prop :=
  ∀ S ∈ K.coverings U, ∃ V ∈ K.coverings U, ∃ F : Set (Σ Y : C, Y ⟶ U),
    F.Finite ∧ (∀ p ∈ F, S p.2) ∧
    (∀ ⦃W : C⦄ (g : W ⟶ U), V g →
      ∃ p ∈ F, ∃ h : W ⟶ p.1, h ≫ p.2 = g)

/-- **Definition 2 (Finite refinement property — Stacks 0D05(2)).** `U` has the
*finite refinement property* if every covering `S` of `U` admits a covering `V`
of `U` whose set of arrows is finite and which refines `S`. -/
def HasFiniteRefinement (K : Pretopology C) (U : C) : Prop :=
  ∀ S ∈ K.coverings U, ∃ V ∈ K.coverings U,
    (Presieve.arrowSet V).Finite ∧ Refines V S

/-- **Definition 3 (Finite subcovering property — Stacks 0D05(3)).** `U` has the
*finite subcovering property* if every covering `S` of `U` contains a finite
sub-presieve `T ≤ S` which is itself a covering of `U`. -/
@[sga "4 IV 8.7" "more general"]
def HasFiniteSubcovering (K : Pretopology C) (U : C) : Prop :=
  ∀ S ∈ K.coverings U, ∃ T : Presieve U, T ≤ S ∧
    (Presieve.arrowSet T).Finite ∧ T ∈ K.coverings U

/-- **Statement (A) — (3) ⇒ (2).** If `U` has the finite subcovering property,
then `U` has the finite refinement property. -/
@[stacks 0D05 "(3)⇒(2)"]
theorem finiteSubcovering_imp_finiteRefinement
    (K : Pretopology C) (U : C) (h : HasFiniteSubcovering K U) :
    HasFiniteRefinement K U := by
  intro S hS
  obtain ⟨T, hTS, hTfin, hTcov⟩ := h S hS
  exact ⟨T, hTcov, hTfin, fun W g hg => ⟨W, g, 𝟙 W, @hTS W g hg, Category.id_comp g⟩⟩

/-- **Statement (B) — (2) ⇒ (1).** If `U` has the finite refinement property,
then `U` is quasi-compact. -/
@[stacks 0D05 "(2)⇒(1)"]
theorem finiteRefinement_imp_quasiCompact
    (K : Pretopology C) (U : C) (h : HasFiniteRefinement K U) :
    IsQuasiCompact K U := by
  intro S hS
  obtain ⟨V, hVcov, hVfin, hVref⟩ := h S hS
  classical
  -- Name, for each arrow `g` of `V`, an arrow `fw g hg` of `S` that `g` factors through.
  choose Yw fw hw hSw hfacw using hVref
  let wit : (Σ Y : C, Y ⟶ U) → (Σ Y : C, Y ⟶ U) := fun p =>
    if hp : V p.2 then ⟨Yw p.2 hp, fw p.2 hp⟩ else p
  refine ⟨V, hVcov, wit '' (Presieve.arrowSet V), ?_, ?_, ?_⟩
  · exact hVfin.image wit
  · -- every element of the image is an arrow of S
    rintro p ⟨q, hq, rfl⟩
    have hVq : V q.2 := hq
    rw [show wit q = ⟨Yw q.2 hVq, fw q.2 hVq⟩ by simp [wit, hVq]]
    exact hSw q.2 hVq
  · -- every arrow g of V factors through some element of F
    intro W g hg
    refine ⟨wit ⟨W, g⟩, ⟨⟨W, g⟩, hg, rfl⟩, ?_⟩
    rw [show wit ⟨W, g⟩ = ⟨Yw g hg, fw g hg⟩ by simp [wit, hg]]
    exact ⟨hw g hg, hfacw g hg⟩

/-! ## Shared witness space for the counterexamples (C) and (D).

Both counterexamples live on the opens of the **closed unit interval**
`unitInterval = ↑(Set.Icc (0:ℝ) 1)`.  This is the literal Stacks `[0,1]` example.  It is
**compact** (`CompactSpace unitInterval`, from `isCompact_Icc`) and, crucially,
**atomless / perfect** (`PerfectSpace unitInterval`): it has no isolated points, so every
nonempty open is infinite and the lattice of opens has no atoms.  This atomlessness
is exactly what makes the `pullbacks` axiom satisfiable for the "infinite covers ∪
identity" cover set: restricting an infinite open cover along an open subobject can
no longer collapse it to a finite non-identity presieve (a nonempty open never
shrinks to a single atom), which is precisely why Stacks uses `[0,1]` and why the
space `OnePoint ℕ` does not work.

We package the opens as a `def WObj` carrying a *universe-polymorphic* thin-category
instance (morphisms `ULift (PLift (· ≤ ·))`), so that it provides a witness category at
the morphism universe demanded by the (universe-polymorphic) existential statements
`exists_*`.  Objects are literally `Opens unitInterval`, so all order/lattice facts about
opens apply verbatim. -/

open TopologicalSpace Limits

universe v

/-- The witness category for (C) and (D): opens of `unitInterval` (`= [0,1]`). -/
@[implicit_reducible]
def WObj : Type := Opens unitInterval

/-- `WObj` carries the complete lattice of opens of `unitInterval`, so `⊓`, `⊔`, `⊥` and `⊤`
on it are intersection, union, `∅` and the whole space.  All the order-theoretic covering
conditions of the two witness sites are stated in this lattice. -/
instance : CompleteLattice WObj := inferInstanceAs (CompleteLattice (Opens unitInterval))

/-- A universe-polymorphic thin category on the poset of opens. -/
instance wcat : Category.{v, 0} WObj where
  Hom A B := ULift.{v} (PLift (A ≤ B))
  id A := ⟨⟨le_refl A⟩⟩
  comp f g := ⟨⟨le_trans f.down.down g.down.down⟩⟩

/-- `WObj` is a *thin* category: an arrow carries no data beyond the inequality `A ≤ B`, so
any two parallel arrows are equal.  Every cone, cocone and pretopology-axiom coherence in the
two witness sites is discharged by `Subsingleton.elim` through this instance. -/
instance wThin (A B : WObj) : Subsingleton (A ⟶ B) :=
  ⟨fun (f g : ULift.{_} (PLift (A ≤ B))) => by obtain ⟨⟨_⟩⟩ := f; obtain ⟨⟨_⟩⟩ := g; rfl⟩

/-- The arrow witnessing `A ≤ B`. -/
def wHomOfLE {A B : WObj} (h : A ≤ B) : A ⟶ B := ⟨⟨h⟩⟩

/-- The order relation underlying an arrow. -/
theorem wLeOfHom {A B : WObj} (f : A ⟶ B) : A ≤ B := f.down.down

/-- `WObj` has pullbacks: the pullback of a cospan is the meet of its two non-tip
objects (the thin category is a meet-semilattice). -/
noncomputable instance : HasPullbacks WObj := by
  refine ⟨fun F => ?_⟩
  refine HasLimit.mk { cone := ?_, isLimit := ?_ }
  · refine { pt := F.obj WalkingCospan.left ⊓ F.obj WalkingCospan.right, π := ?_ }
    refine { app := fun j => ?_, naturality := fun _ _ _ => Subsingleton.elim _ _ }
    match j with
    | none => exact wHomOfLE (le_trans inf_le_left (wLeOfHom (F.map WalkingCospan.Hom.inl)))
    | some WalkingPair.left => exact wHomOfLE inf_le_left
    | some WalkingPair.right => exact wHomOfLE inf_le_right
  · exact { lift := fun s => wHomOfLE (le_inf (wLeOfHom (s.π.app (some WalkingPair.left)))
              (wLeOfHom (s.π.app (some WalkingPair.right))))
            fac := fun _ _ => Subsingleton.elim _ _
            uniq := fun _ _ _ => Subsingleton.elim _ _ }

/-- The unique arrow out of the empty open (`⊥` is the initial object of the poset). -/
noncomputable def botArrow (W : WObj) : (⊥ : WObj) ⟶ W := wHomOfLE bot_le

/-- A presieve `S` on `W` *covers* `W` if the supremum of its source opens equals `W`
(the honest open-cover condition). -/
def Covers {W : WObj} (S : Presieve W) : Prop :=
  sSup { Y : WObj | ∃ (f : Y ⟶ W), S f } = W

/-! ### (C) witness site: (1) ⇏ (2).

The (C) construction is defined further below (after the shared kernel lemmas
`pullback_eq_inf` / `dSrc_pullbackArrows`), since it reuses that pullback=meet bridge.
See the section "### (C) witness site [REDESIGNED]" near the end of the file. -/

/-! ### (D) witness site: (2) ⇏ (3).  [REDESIGNED — order-theoretic, pullback-closed]

Same space `WObj = Opens unitInterval`.  The previous "contains `dS0`" disjunct was
**unsound** (it is not closed under pullback; counterexample `V = (1/4, 3/4)`).  We replace
it with the *pullback-closed* condition (D3) below, expressed purely **order-theoretically**
in terms of the SET OF SOURCES of a presieve.

In this thin category a presieve `S : Presieve W` is determined by its set of sources
`{ Y | ∃ f : Y ⟶ W, S f }`.  `dSrc S Y` says "the (unique) arrow `Y ⟶ W` belongs to `S`".
The three covering disjuncts are:
* (D1) `dSrc S ⊥`  — contains the empty-open arrow `⊥ ⟶ W`;
* (D2) `dSrc S W`  — contains the identity/iso arrow `W ⟶ W`;
* (D3) `∀ n, dSrc S (dOpen n ⊓ W)` — contains all the meets `dOpen n ⊓ W`.
At `W = ⊤` this last is `∀ n, dSrc S (dOpen n)` (since `dOpen n ⊓ ⊤ = dOpen n`), i.e. it
contains the whole chain `dS0`.  This is exactly the set of sources of
`pullbackArrows (W ⟶ ⊤) dS0`, hence pullback-stable by the meet identity
`(dOpen n ⊓ X) ⊓ Y = dOpen n ⊓ Y` for `Y ≤ X`. -/

/-- An increasing chain of proper opens of `unitInterval`: `dOpen n` is the open
`{x | (x:ℝ) < 1 - 1/(n+2)}`.  Each is a nonempty proper open (it contains `0`, omits `1`),
the chain is increasing in `n`, and the map `n ↦ dOpen n` is injective (so the family is
infinite). -/
def dOpen (n : ℕ) : WObj :=
  show Opens unitInterval from
    ⟨{x : unitInterval | (x : ℝ) < 1 - 1 / (n + 2)},
      isOpen_lt continuous_subtype_val continuous_const⟩

/-- Membership in `dOpen n` is the defining strict inequality. -/
theorem mem_dOpen_carrier {n : ℕ} {z : unitInterval} :
    z ∈ (show Opens unitInterval from dOpen n).carrier ↔ (z : ℝ) < 1 - 1 / ((n : ℝ) + 2) :=
  Iff.rfl

/-- "`S` has source `Y`": the unique arrow `Y ⟶ W` of the thin category belongs to `S`. -/
def dSrc {W : WObj} (S : Presieve W) (Y : WObj) : Prop := ∃ f : Y ⟶ W, S f

/-- The distinguished infinite cover of `⊤` by the increasing chain `dOpen`. -/
def dS0 : Presieve (⊤ : WObj) := Presieve.ofArrows dOpen (fun _ => wHomOfLE le_top)

/-- Coverings of the (D) site (order-theoretic, pullback-closed): a presieve `S` on `W`
covers iff it (D1) contains `⊥ ⟶ W`, or (D2) contains `W ⟶ W`, or (D3) contains the meet
`dOpen n ⊓ W` for every `n`. -/
def dCoverings (W : WObj) : Set (Presieve W) :=
  { S | dSrc S ⊥ }
    ∪ { S | dSrc S W }
    ∪ { S | ∀ n, dSrc S (dOpen n ⊓ W) }

/-! #### Key analytic / categorical kernel lemmas for (D).

These package the only nontrivial facts. They are split out as named lemmas so the three
pretopology axioms reduce to bookkeeping over `dSrc`. -/

/-- The threshold `1 - 1/(n+2)` of the chains `dOpen` and `eOpen` is monotone. -/
private theorem one_sub_one_div_nat_add_two_mono {m n : ℕ} (h : m ≤ n) :
    (1 : ℝ) - 1 / ((m : ℝ) + 2) ≤ 1 - 1 / ((n : ℝ) + 2) := by
  have : (m : ℝ) ≤ n := by exact_mod_cast h
  gcongr

/-- `dOpen` is monotone (the chain is increasing): `m ≤ n → dOpen m ≤ dOpen n`. -/
theorem dOpen_mono {m n : ℕ} (h : m ≤ n) : dOpen m ≤ dOpen n := fun _ hx =>
  lt_of_lt_of_le hx (one_sub_one_div_nat_add_two_mono h)

/-- The chain meet identity: `dOpen m ⊓ dOpen n = dOpen (min m n)`. -/
theorem dOpen_inf (m n : ℕ) : dOpen m ⊓ dOpen n = dOpen (min m n) := by
  -- from `dOpen_mono`: the smaller index gives the smaller open, so the meet is it.
  rcases le_total m n with hmn | hmn
  · rw [min_eq_left hmn, inf_eq_left]
    exact dOpen_mono hmn
  · rw [min_eq_right hmn, inf_eq_right]
    exact dOpen_mono hmn

/-- Two opens of `unitInterval` differ if a point lies in one and not in the other. -/
private theorem opens_ne_of_mem_of_not_mem {U V : WObj} {x : unitInterval}
    (hU : x ∈ (show Opens unitInterval from U).carrier)
    (hV : x ∉ (show Opens unitInterval from V).carrier) : U ≠ V := by
  rintro rfl
  exact hV hU

/-- `dOpen n` is a nonempty proper open: `dOpen n ≠ ⊥` and `dOpen n ≠ ⊤`. -/
theorem dOpen_ne_bot (n : ℕ) : dOpen n ≠ ⊥ :=
  opens_ne_of_mem_of_not_mem (x := 0) (mem_dOpen_carrier.mpr (by
    have := one_sub_one_div_nat_add_two_mono (Nat.zero_le n)
    norm_num at this ⊢
    linarith)) id

/-- `dOpen n` is a *proper* open: `dOpen n ≠ ⊤`, because `1` is omitted (`1 - 1/(n+2) < 1`).
This is what rules out the (D2) disjunct for a finite sub-presieve of the chain cover `dS0` in
`dSite_not_finiteSubcovering`. -/
theorem dOpen_ne_top (n : ℕ) : dOpen n ≠ ⊤ :=
  (opens_ne_of_mem_of_not_mem (x := 1) (U := ⊤) (V := dOpen n) trivial fun h => by
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have : (1 : ℝ) < 1 - 1 / ((n : ℝ) + 2) := mem_dOpen_carrier.mp h
    linarith).symm

/-- The threshold `1 - 1/(n+2)` of the chains `dOpen` and `eOpen` lies in `[0,1]`. -/
theorem one_sub_one_div_nat_add_two_mem_Icc (n : ℕ) :
    (1 : ℝ) - 1 / ((n : ℝ) + 2) ∈ Set.Icc (0 : ℝ) 1 := by
  have h₁ : 1 / ((n : ℝ) + 2) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h₂ : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  constructor <;> linarith

/-- The threshold `1 - 1/(n+2)` of the chains `dOpen` and `eOpen` is strictly increasing. -/
theorem one_sub_one_div_nat_add_two_strictMono :
    StrictMono fun n : ℕ => (1 : ℝ) - 1 / ((n : ℝ) + 2) := by
  intro a b hab
  dsimp only
  have hab' : (a : ℝ) + 2 < (b : ℝ) + 2 := by
    have : (a : ℝ) < b := by exact_mod_cast hab
    linarith
  have := one_div_lt_one_div_of_lt (by positivity : (0 : ℝ) < (a : ℝ) + 2) hab'
  linarith

/-- `n ↦ dOpen n` is injective; hence the family of sources of `dS0` is infinite. -/
theorem dOpen_injective : Function.Injective dOpen := by
  intro m n hmn
  by_contra hne
  wlog hlt : m < n generalizing m n
  · exact this hmn.symm (Ne.symm hne) (by omega)
  exact opens_ne_of_mem_of_not_mem (x := ⟨_, one_sub_one_div_nat_add_two_mem_Icc m⟩)
    (mem_dOpen_carrier.mpr (one_sub_one_div_nat_add_two_strictMono hlt))
    (fun hc => lt_irrefl _ (mem_dOpen_carrier.mp hc)) hmn.symm

/-- In the thin meet-semilattice `WObj` the pullback of a cospan is the meet of the two
non-tip objects.  This is not definitional (the bespoke `HasPullbacks` instance routes
through `HasLimit.mk`), so it is proved by antisymmetry. -/
theorem pullback_eq_inf {X Y Z' : WObj} (g : Z' ⟶ X) (f : Y ⟶ X) :
    pullback g f = Z' ⊓ Y := by
  apply le_antisymm
  · exact le_inf (wLeOfHom (pullback.fst g f)) (wLeOfHom (pullback.snd g f))
  · exact wLeOfHom (pullback.lift (wHomOfLE inf_le_left) (wHomOfLE inf_le_right)
      (Subsingleton.elim _ _))

/-- **Kernel pullback-source lemma (Lemma P).**  In the thin meet-semilattice `WObj`, the
set of sources of `pullbackArrows f S` (for `f : Y ⟶ X`) is `{ Z ⊓ Y | Z source of S }`:
`dSrc (pullbackArrows f S) Z ↔ ∃ Z', dSrc S Z' ∧ Z = Z' ⊓ Y`.  This is the bridge between
Mathlib's categorical `pullbackArrows`/`pullback` and the meet `⊓`; it uses the bespoke
`HasPullbacks WObj` instance (pullback object = meet) plus thinness. -/
theorem dSrc_pullbackArrows {X Y : WObj} (f : Y ⟶ X) (S : Presieve X)
    [S.HasPullbacks f] (Z : WObj) :
    dSrc (Presieve.pullbackArrows f S) Z ↔ ∃ Z', dSrc S Z' ∧ Z = Z' ⊓ Y := by
  constructor
  · rintro ⟨a, ha⟩
    cases ha with
    | mk Z' g hSg =>
      exact ⟨Z', ⟨g, hSg⟩, pullback_eq_inf g f⟩
  · rintro ⟨Z', ⟨g, hSg⟩, rfl⟩
    rw [← pullback_eq_inf g f]
    exact ⟨pullback.snd g f, Presieve.pullbackArrows.mk Z' g hSg⟩

/-- The (D) pretopology. -/
noncomputable def dSite : Pretopology WObj where
  coverings := dCoverings
  has_isos := by
    -- An iso `f : Y ⟶ X` in the thin poset forces `Y = X`; `singleton f` has source `X`,
    -- so (D2) `dSrc (singleton f) X` holds.
    intro X Y f inst
    obtain rfl : Y = X := le_antisymm (wLeOfHom f) (wLeOfHom (inv f))
    exact Or.inl (Or.inr ⟨f, Presieve.singleton.mk⟩)
  pullbacks := by
    -- For `S ∈ dCoverings X`, `f : Y ⟶ X`, show `pullbackArrows f S ∈ dCoverings Y` by
    -- cases on the disjunct, using `dSrc_pullbackArrows`:
    --  (D1) `dSrc S ⊥` ⇒ `dSrc (pb) (⊥ ⊓ Y = ⊥)` ⇒ (D1) for Y.
    --  (D2) `dSrc S X` ⇒ `dSrc (pb) (X ⊓ Y = Y)` (since `Y ≤ X`) ⇒ (D2) for Y.
    --  (D3) `∀n, dSrc S (dOpen n ⊓ X)` ⇒ `dSrc (pb) ((dOpen n ⊓ X) ⊓ Y = dOpen n ⊓ Y)`
    --       (meet assoc/comm + `X ⊓ Y = Y`) ⇒ (D3) for Y.
    intro X Y f S hS
    have : S.HasPullbacks f := ⟨fun _ => inferInstance⟩
    have hYX : Y ≤ X := wLeOfHom f
    rcases hS with (h1 | h2) | h3
    · -- (D1): dSrc S ⊥
      refine Or.inl (Or.inl ?_)
      refine (dSrc_pullbackArrows f S ⊥).mpr ⟨⊥, h1, ?_⟩
      rw [bot_inf_eq]
    · -- (D2): dSrc S X
      refine Or.inl (Or.inr ?_)
      refine (dSrc_pullbackArrows f S Y).mpr ⟨X, h2, ?_⟩
      rw [inf_eq_right.mpr hYX]
    · -- (D3): ∀ n, dSrc S (dOpen n ⊓ X)
      refine Or.inr ?_
      intro n
      refine (dSrc_pullbackArrows f S (dOpen n ⊓ Y)).mpr ⟨dOpen n ⊓ X, h3 n, ?_⟩
      rw [inf_assoc, inf_eq_right.mpr hYX]
  transitive := by
    -- For `S ∈ dCoverings X` and `Ti f ∈ dCoverings (src f)`, show `S.bind Ti ∈ dCoverings X`.
    -- Key sub-lemma: every covering of `⊥` has source `⊥` (all 3 disjuncts force `⊥`).
    -- (D1) of S: bind through `⊥⟶X` arrow and the `⊥`-source of `Ti(⊥⟶X)` ⇒ (D1).
    -- (D2) of S: `Ti (X⟶X)` composes via `𝟙 X` keeping its disjunct ⇒ same disjunct.
    -- (D3) of S: for each `n`, `Ti (f_n)` on `W_n = dOpen n ⊓ X`; if any is (D1) ⇒ global (D1);
    --   else each contributes `dOpen n ⊓ X ∈ σ(bind)` (using `dOpen_inf`, pick `m ≥ n`) ⇒ (D3).
    intro X S Ti hS hTi
    -- KEY LEMMA: a source `Z` of an inner cover `Ti f hf` is a source of `S.bind Ti`.
    have key : ∀ {Yobj : WObj} (farr : Yobj ⟶ X) (hf : S farr) {Z : WObj},
        dSrc (Ti farr hf) Z → dSrc (S.bind Ti) Z := by
      rintro Yobj farr hf Z ⟨h, hh⟩
      exact ⟨h ≫ farr, Yobj, h, farr, hf, hh, rfl⟩
    -- Sub-lemma: every covering of ⊥ has source ⊥.
    have botCover : ∀ {T : Presieve (⊥ : WObj)}, T ∈ dCoverings ⊥ → dSrc T ⊥ := by
      intro T hT
      rcases hT with (h1 | h2) | h3
      · exact h1
      · exact h2
      · have := h3 0
        rwa [inf_bot_eq] at this
    rcases hS with (hS1 | hS2) | hS3
    · -- (D1) of S: dSrc S ⊥, arrow f : ⊥ ⟶ X
      obtain ⟨farr, hf⟩ := hS1
      exact Or.inl (Or.inl (key farr hf (botCover (hTi farr hf))))
    · -- (D2) of S: dSrc S X, arrow f : X ⟶ X
      obtain ⟨farr, hf⟩ := hS2
      have hcov : Ti farr hf ∈ dCoverings X := hTi farr hf
      rcases hcov with (hc1 | hc2) | hc3
      · -- inner (D1): source ⊥ ⇒ bind (D1)
        exact Or.inl (Or.inl (key farr hf hc1))
      · -- inner (D2): source X ⇒ bind (D2)
        exact Or.inl (Or.inr (key farr hf hc2))
      · -- inner (D3): sources dOpen n ⊓ X ⇒ bind (D3)
        exact Or.inr (fun n => key farr hf (hc3 n))
    · -- (D3) of S: ∀ n, dSrc S (dOpen n ⊓ X)
      classical
      by_cases hany : ∃ n, dSrc (Ti (hS3 n).choose (hS3 n).choose_spec) ⊥
      · -- some inner cover has source ⊥ ⇒ bind (D1)
        obtain ⟨n, hn⟩ := hany
        exact Or.inl (Or.inl (key (hS3 n).choose (hS3 n).choose_spec hn))
      · -- otherwise: for each n, extract dOpen n ⊓ X as a bind source ⇒ bind (D3)
        refine Or.inr (fun n => ?_)
        set fn := (hS3 n).choose
        have hSfn : S fn := (hS3 n).choose_spec
        -- fn : dOpen n ⊓ X ⟶ X
        have hcov : Ti fn hSfn ∈ dCoverings (dOpen n ⊓ X) := hTi fn hSfn
        rcases hcov with (hc1 | hc2) | hc3
        · -- inner (D1): source ⊥ — contradicts hany
          exact absurd ⟨n, hc1⟩ hany
        · -- inner (D2): source (dOpen n ⊓ X) itself
          exact key fn hSfn hc2
        · -- inner (D3): sources dOpen k ⊓ (dOpen n ⊓ X); take k = n
          have hcn := hc3 n
          have heq : dOpen n ⊓ (dOpen n ⊓ X) = dOpen n ⊓ X := by
            rw [← inf_assoc, inf_idem]
          rw [heq] at hcn
          exact key fn hSfn hcn

/-- **(D) sub-lemma 1 — the finite refinement property holds at `⊤`.**

`V := {⊥ ⟶ ⊤}` is a covering (D1) with a single arrow.  Every covering `S` of `⊤` is
nonempty (each disjunct provides an arrow), and `⊥ ⟶ ⊤` factors through any arrow
`f : Y ⟶ ⊤` of `S` via `⊥ ⟶ Y` (then `Subsingleton (⊥ ⟶ ⊤)`).  So `V` refines `S`. -/
theorem dSite_finiteRefinement : HasFiniteRefinement dSite (⊤ : WObj) := by
  -- take `V := Presieve.singleton (botArrow ⊤)`; (D1) membership = `dSrc V ⊥` via the arrow
  -- itself; singleton arrowSet finite; refines via nonemptiness of `S` + `Subsingleton`.
  intro S hS
  refine ⟨Presieve.singleton (botArrow ⊤), ?_, ?_, ?_⟩
  · exact Or.inl (Or.inl ⟨botArrow ⊤, Presieve.singleton.mk⟩)
  · have : Presieve.arrowSet (Presieve.singleton (botArrow ⊤))
        ⊆ {(⟨⊥, botArrow ⊤⟩ : Σ Y : WObj, Y ⟶ (⊤ : WObj))} := by
      rintro ⟨Y, f⟩ hf
      have hf' : Presieve.singleton (botArrow ⊤) f := hf
      cases hf' with
      | mk => simp
    exact (Set.finite_singleton _).subset this
  · intro W g hg
    have hg' : Presieve.singleton (botArrow ⊤) g := hg
    cases hg' with
    | mk =>
      have hne : ∃ (Y : WObj) (f : Y ⟶ (⊤ : WObj)), S f := by
        rcases hS with (h1 | h2) | h3
        · obtain ⟨f, hf⟩ := h1
          exact ⟨⊥, f, hf⟩
        · obtain ⟨f, hf⟩ := h2
          exact ⟨⊤, f, hf⟩
        · obtain ⟨f, hf⟩ := h3 0
          exact ⟨dOpen 0 ⊓ ⊤, f, hf⟩
      obtain ⟨Y, f, hf⟩ := hne
      exact ⟨Y, f, wHomOfLE bot_le, hf, Subsingleton.elim _ _⟩

/-- The coverings of `dSite` are `dCoverings`. -/
theorem dSite_coverings : dSite.coverings = dCoverings :=
  rfl

/-- A presieve having a source at every term of an injective sequence of opens has infinitely
many arrows. -/
theorem arrowSet_infinite_of_forall_dSrc {X : WObj} {T : Presieve X} {u : ℕ → WObj}
    (hu : Function.Injective u) (h : ∀ n, dSrc T (u n)) : (Presieve.arrowSet T).Infinite :=
  Set.infinite_of_injective_forall_mem
    (f := fun n => (⟨u n, (h n).choose⟩ : Σ Y : WObj, Y ⟶ X))
    (fun _ _ hab => hu (congrArg Sigma.fst hab)) fun n => (h n).choose_spec

/-- The presieve of arrows `u n ⟶ ⊤` has the source `u n ⊓ ⊤` for every `n`. -/
private theorem dSrc_ofArrows_inf_top (u : ℕ → WObj) (n : ℕ) :
    dSrc (Presieve.ofArrows u fun _ => wHomOfLE le_top) (u n ⊓ ⊤) := by
  rw [inf_top_eq]
  exact ⟨wHomOfLE le_top, Presieve.ofArrows.mk n⟩

/-- A presieve on `⊤` with sources `u n ⊓ ⊤` for an injective sequence `u` has infinitely
many arrows. -/
private theorem arrowSet_infinite_of_forall_dSrc_inf_top {T : Presieve (⊤ : WObj)}
    {u : ℕ → WObj} (hu : Function.Injective u) (h : ∀ n, dSrc T (u n ⊓ ⊤)) :
    (Presieve.arrowSet T).Infinite :=
  arrowSet_infinite_of_forall_dSrc hu fun n => by simpa only [inf_top_eq] using h n

/-- **(D) sub-lemma 2 — failure of the finite subcovering property at `⊤`.**

`dS0 ∈ dCoverings ⊤` (D3, since `dOpen n ⊓ ⊤ = dOpen n` is a source of `dS0`).  Any finite
`T ≤ dS0` has sources among `{dOpen n}` (nonempty proper opens), so fails (D1) (`dOpen n ≠ ⊥`),
fails (D2) (`dOpen n ≠ ⊤`), and fails (D3) (D3 at `⊤` needs all `dOpen n` as sources, but
`T` finite + `dOpen` injective ⇒ only finitely many). -/
theorem dSite_not_finiteSubcovering : ¬ HasFiniteSubcovering dSite (⊤ : WObj) := by
  intro h
  classical
  -- `dS0 ∈ dCoverings ⊤` via the third disjunct (D3): every `dOpen n ⊓ ⊤ = dOpen n`
  -- is a source of `dS0`, witnessed by `wHomOfLE le_top`.
  have hmem : dS0 ∈ dSite.coverings (⊤ : WObj) := by
    rw [dSite_coverings]
    exact Or.inr (dSrc_ofArrows_inf_top dOpen)
  obtain ⟨T, hTS, hTfin, hTcov⟩ := h dS0 hmem
  -- KEY: every source `Y` of `T` is some `dOpen n`.
  have hsrc : ∀ {Y : WObj}, dSrc T Y → ∃ n, Y = dOpen n := by
    rintro Y ⟨f, hf⟩
    have hf0 : dS0 f := @hTS Y f hf
    cases hf0 with
    | mk n => exact ⟨n, rfl⟩
  rcases hTcov with (hc1 | hc2) | hc3
  · -- (D1): source ⊥ = dOpen n, contradiction.
    obtain ⟨n, hn⟩ := hsrc hc1
    exact dOpen_ne_bot n hn.symm
  · -- (D2): source ⊤ = dOpen n, contradiction.
    obtain ⟨n, hn⟩ := hsrc hc2
    exact dOpen_ne_top n hn.symm
  · exact arrowSet_infinite_of_forall_dSrc_inf_top dOpen_injective hc3 hTfin

/-- **Statement (D) — (2) ⇏ (3).** There exists a site (`C`, `K`, `U`) such that
`U` has the finite refinement property but does not have the finite subcovering
property. -/
@[stacks 0D05 "(2)⇏(3)"]
theorem exists_finiteRefinement_not_finiteSubcovering :
    ∃ (C : Type) (_ : Category C) (_ : Limits.HasPullbacks C)
      (K : Pretopology C) (U : C), HasFiniteRefinement K U ∧ ¬ HasFiniteSubcovering K U :=
  ⟨WObj, inferInstance, inferInstance, dSite, ⊤,
    dSite_finiteRefinement, dSite_not_finiteSubcovering⟩

/-! ### (C) witness site [REDESIGNED — order-theoretic, pullback-closed, DECREASING chain].

The earlier (C) `cCoverings = {𝟙} ∪ {infinite honest covers}` was **unsound**: `pullbacks`
fails for it (pulling an infinite cover back along
a non-dense open collapses it to a finite non-trivial presieve, exactly the (D) pathology).

We mirror the proven (D) order-theoretic design, but with a **DECREASING** chain `eOpen`
and a **UNIVERSAL** rung condition.  The two single-chain failure modes are:
* increasing chain + universal `∀n` ⟹ no finite refinement but quasi-compactness FAILS
  (admissible covers cofinal in a chain with no top; no finite `F` dominates);
* decreasing chain + existential `∃n` ⟹ quasi-compact but the singleton `{eOpen n → ⊤}` is
  a finite refinement (so ¬finite-refinement fails).
The reconciliation is **decreasing chain + universal `∀n`**: the chain has a MAXIMUM
`eOpen 0` that dominates an admissible down-set (giving a finite `F = {eOpen 0 ⟶ ⊤}` for
quasi-compactness), while the universal condition forces every admissible cover to contain
the infinitely many distinct `eOpen n`, so no FINITE covering is admissible except the
trivial `{𝟙 ⊤}` — which cannot refine the chain cover `{eOpen n}` (would need `⊤ ≤ eOpen n`).
-/

/-- A **decreasing** chain of proper opens of `unitInterval`: `eOpen n` is the open
`{x | (x:ℝ) > 1 - 1/(n+2)}`.  The threshold `1 - 1/(n+2)` increases to `1`, so the opens
SHRINK: `eOpen 0 = {x > 1/2} ⊋ eOpen 1 = {x > 2/3} ⊋ …`.  Hence `eOpen 0` is the MAXIMUM of
the chain.  Each is nonempty (contains `1`) and proper (omits `0`), and `n ↦ eOpen n` is
injective (so the family is infinite). -/
def eOpen (n : ℕ) : WObj :=
  show Opens unitInterval from
    ⟨{x : unitInterval | (x : ℝ) > 1 - 1 / (n + 2)},
      isOpen_lt continuous_const continuous_subtype_val⟩

/-- Membership in `eOpen n` is the defining strict inequality. -/
theorem mem_eOpen_carrier {n : ℕ} {z : unitInterval} :
    z ∈ (show Opens unitInterval from eOpen n).carrier ↔ (z : ℝ) > 1 - 1 / ((n : ℝ) + 2) :=
  Iff.rfl

/-- `eOpen` is antitone (the chain decreases): `m ≤ n → eOpen n ≤ eOpen m`. -/
theorem eOpen_antitone {m n : ℕ} (h : m ≤ n) : eOpen n ≤ eOpen m := fun _ hx =>
  lt_of_le_of_lt (one_sub_one_div_nat_add_two_mono h) hx

/-- `eOpen 0` is the maximum of the chain: `eOpen n ≤ eOpen 0`. -/
theorem eOpen_le_zero (n : ℕ) : eOpen n ≤ eOpen 0 := eOpen_antitone (Nat.zero_le n)

/-- The chain meet identity: `eOpen m ⊓ eOpen n = eOpen (max m n)` (the smaller open). -/
theorem eOpen_inf (m n : ℕ) : eOpen m ⊓ eOpen n = eOpen (max m n) := by
  rcases le_total m n with hmn | hmn
  · rw [max_eq_right hmn, inf_eq_right]
    exact eOpen_antitone hmn
  · rw [max_eq_left hmn, inf_eq_left]
    exact eOpen_antitone hmn

/-- `eOpen 0` absorbs any chain meet: `eOpen 0 ⊓ eOpen n = eOpen n`. -/
theorem eOpen_zero_inf (n : ℕ) : eOpen 0 ⊓ eOpen n = eOpen n :=
  inf_eq_right.mpr (eOpen_le_zero n)

/-- `eOpen n` is nonempty: `eOpen n ≠ ⊥` (it contains `1`, since `1 > 1 - 1/(n+2)`). -/
theorem eOpen_ne_bot (n : ℕ) : eOpen n ≠ ⊥ :=
  opens_ne_of_mem_of_not_mem (x := 1) (mem_eOpen_carrier.mpr (by
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have : ((1 : unitInterval) : ℝ) = 1 := rfl
    linarith)) id

/-- `eOpen n` is proper: `eOpen n ≠ ⊤` (it omits `0`, since `0 > 1 - 1/(n+2)` is false). -/
theorem eOpen_ne_top (n : ℕ) : eOpen n ≠ ⊤ :=
  (opens_ne_of_mem_of_not_mem (x := 0) (U := ⊤) (V := eOpen n) trivial fun h =>
    not_lt.mpr (one_sub_one_div_nat_add_two_mem_Icc n).1 (mem_eOpen_carrier.mp h)).symm

/-- `n ↦ eOpen n` is injective (the thresholds `1 - 1/(n+2)` are strictly increasing). -/
theorem eOpen_injective : Function.Injective eOpen := by
  intro m n hmn
  by_contra hne
  wlog hlt : m < n generalizing m n
  · exact this hmn.symm (Ne.symm hne) (by omega)
  exact opens_ne_of_mem_of_not_mem (x := ⟨_, one_sub_one_div_nat_add_two_mem_Icc n⟩)
    (mem_eOpen_carrier.mpr (one_sub_one_div_nat_add_two_strictMono hlt))
    (fun hc => lt_irrefl _ (mem_eOpen_carrier.mp hc)) hmn

/-- The distinguished infinite cover of `⊤` by the decreasing chain `eOpen`. -/
def cS0 : Presieve (⊤ : WObj) := Presieve.ofArrows eOpen (fun _ => wHomOfLE le_top)

/-- Coverings of the (C) site (order-theoretic, pullback-closed): a presieve `S` on `W`
covers iff it (C2) contains the identity `W ⟶ W`, or (C3) contains every meet
`eOpen n ⊓ W`.  (Reuses `dSrc` for "has source".) -/
def cCoverings (W : WObj) : Set (Presieve W) :=
  { S | dSrc S W }
    ∪ { S | ∀ n, dSrc S (eOpen n ⊓ W) }

/-- The (C) pretopology. -/
noncomputable def cSite : Pretopology WObj where
  coverings := cCoverings
  has_isos := by
    -- iso `f : Y ⟶ X` ⇒ `Y = X` ⇒ `{f}` has source `X` ⇒ (C2). Identical to `dSite`.
    intro X Y f inst
    obtain rfl : Y = X := le_antisymm (wLeOfHom f) (wLeOfHom (inv f))
    exact Or.inl ⟨f, Presieve.singleton.mk⟩
  pullbacks := by
    -- mirror `dSite.pullbacks`: cases on the (C2)/(C3) disjunct, apply `dSrc_pullbackArrows`
    -- + the meet identities `X ⊓ Y = Y` (Y ≤ X) and `(eOpen n ⊓ X) ⊓ Y = eOpen n ⊓ Y`.
    intro X Y f S hS
    have : S.HasPullbacks f := ⟨fun _ => inferInstance⟩
    have hYX : Y ≤ X := wLeOfHom f
    rcases hS with h2 | h3
    · -- (C2): dSrc S X
      refine Or.inl ?_
      refine (dSrc_pullbackArrows f S Y).mpr ⟨X, h2, ?_⟩
      rw [inf_eq_right.mpr hYX]
    · -- (C3): ∀ n, dSrc S (eOpen n ⊓ X)
      refine Or.inr ?_
      intro n
      refine (dSrc_pullbackArrows f S (eOpen n ⊓ Y)).mpr ⟨eOpen n ⊓ X, h3 n, ?_⟩
      rw [inf_assoc, inf_eq_right.mpr hYX]
  transitive := by
    -- mirror `dSite.transitive` but SIMPLER: no ⊥-disjunct / `botCover` needed, because an
    -- inner (C)-cover of `eOpen n ⊓ X` always yields `eOpen n ⊓ X` as a bind source.
    intro X S Ti hS hTi
    have key : ∀ {Yobj : WObj} (farr : Yobj ⟶ X) (hf : S farr) {Z : WObj},
        dSrc (Ti farr hf) Z → dSrc (S.bind Ti) Z := by
      rintro Yobj farr hf Z ⟨h, hh⟩
      exact ⟨h ≫ farr, Yobj, h, farr, hf, hh, rfl⟩
    rcases hS with hS2 | hS3
    · -- (C2) of S: arrow farr : X ⟶ X
      obtain ⟨farr, hf⟩ := hS2
      have hcov : Ti farr hf ∈ cCoverings X := hTi farr hf
      rcases hcov with hc2 | hc3
      · exact Or.inl (key farr hf hc2)
      · exact Or.inr (fun n => key farr hf (hc3 n))
    · -- (C3) of S: ∀ n, dSrc S (eOpen n ⊓ X)
      refine Or.inr (fun n => ?_)
      set fn := (hS3 n).choose
      have hSfn : S fn := (hS3 n).choose_spec
      have hcov : Ti fn hSfn ∈ cCoverings (eOpen n ⊓ X) := hTi fn hSfn
      rcases hcov with hc2 | hc3
      · -- inner (C2): source `eOpen n ⊓ X` itself
        exact key fn hSfn hc2
      · -- inner (C3): sources `eOpen k ⊓ (eOpen n ⊓ X)`; take `k = 0` (eOpen 0 max)
        have hcn := hc3 0
        have heq : eOpen 0 ⊓ (eOpen n ⊓ X) = eOpen n ⊓ X := by
          rw [← inf_assoc, eOpen_zero_inf]
        rw [heq] at hcn
        exact key fn hSfn hcn

/-- **(C) sub-lemma 1 — quasi-compactness of `⊤`.**

Definition 1 only needs a covering `V` and a FINITE set `F` of arrows of `S` such that
every arrow of `V` factors through `F`; `V` may be infinite and `F` need not cover.  For a
(C3) cover `S` (containing every `eOpen n`), the MAXIMUM rung `eOpen 0` dominates: take
`F = {eOpen 0 ⟶ ⊤}` and `V := {g | source g ≤ eOpen 0}`; `V` is admissible (C3) because
`eOpen n ≤ eOpen 0` for all `n`, and every arrow of `V` factors through `eOpen 0 ⟶ ⊤`. -/
theorem cSite_quasiCompact : IsQuasiCompact cSite (⊤ : WObj) := by
  intro S hS
  -- `V := {g : Y ⟶ ⊤ | Y ≤ eOpen 0}` as a presieve.
  rcases hS with h2 | h3
  · -- (C2): S contains 𝟙_⊤. Take V = {𝟙_⊤}, F = {⟨⊤, the arrow⟩}.
    obtain ⟨f0, hf0⟩ := h2
    refine ⟨Presieve.singleton (𝟙 (⊤ : WObj)), Or.inl ⟨𝟙 (⊤ : WObj), Presieve.singleton.mk⟩,
      {⟨(⊤ : WObj), f0⟩}, Set.finite_singleton _, ?_, ?_⟩
    · rintro _ rfl
      exact hf0
    · intro W g hg
      have hg' : Presieve.singleton (𝟙 (⊤ : WObj)) g := hg
      cases hg' with
      | mk =>
        exact ⟨⟨(⊤ : WObj), f0⟩, Set.mem_singleton _, 𝟙 _, Subsingleton.elim _ _⟩
  · -- (C3): S contains every eOpen n. f0 : eOpen 0 ⊟ ⊤ ⟶ ⊤ is the dominating arrow.
    -- Transport the source `eOpen 0 ⊓ ⊤` to `eOpen 0` first.
    have h3' : dSrc S (eOpen 0) := by simpa only [inf_top_eq] using h3 0
    obtain ⟨f0, hf0⟩ := h3'
    -- V := presieve with source-set {Y | Y ≤ eOpen 0}
    refine ⟨(fun {Y} _ => Y ≤ eOpen 0), ?_, {⟨eOpen 0, f0⟩}, Set.finite_singleton _, ?_, ?_⟩
    · -- V ∈ cCoverings ⊤ via (C3): for each n, eOpen n ⊓ ⊤ = eOpen n ≤ eOpen 0 is a source.
      refine Or.inr (fun n => ?_)
      rw [inf_top_eq]
      exact ⟨wHomOfLE le_top, eOpen_le_zero n⟩
    · -- F ⊆ arrows(S)
      rintro _ rfl
      exact hf0
    · -- every arrow of V factors through f0
      intro W g hgV
      -- hgV : W ≤ eOpen 0
      exact ⟨⟨eOpen 0, f0⟩, Set.mem_singleton _, wHomOfLE hgV, Subsingleton.elim _ _⟩

/-- The coverings of `cSite` are `cCoverings`. -/
theorem cSite_coverings : cSite.coverings = cCoverings :=
  rfl

/-- **(C) sub-lemma 2 — failure of the finite refinement property at `⊤`.**

`cS0` (sources exactly `{eOpen n}`) is a (C3) cover.  A finite covering `V` cannot be (C3)
(that needs the infinitely many distinct `eOpen n` as sources), so it is (C2), containing
`𝟙 ⊤`; refining `cS0` forces `⊤ ≤ eOpen n` for some `n`, contradicting `eOpen_ne_top`. -/
theorem cSite_not_finiteRefinement : ¬ HasFiniteRefinement cSite (⊤ : WObj) := by
  intro h
  classical
  -- cS0 ∈ cCoverings ⊤ via (C3).
  have hmem : cS0 ∈ cSite.coverings (⊤ : WObj) := by
    rw [cSite_coverings]
    exact Or.inr (dSrc_ofArrows_inf_top eOpen)
  obtain ⟨V, hVcov, hVfin, hVref⟩ := h cS0 hmem
  -- V finite ⇒ V is NOT (C3) (which needs infinitely many distinct sources) ⇒ V is (C2).
  have hV2 : dSrc V (⊤ : WObj) := by
    rcases hVcov with h2 | h3
    · exact h2
    · -- (C3): every eOpen n ⊓ ⊤ = eOpen n is a source ⇒ arrowSet V infinite, contradiction.
      exact (arrowSet_infinite_of_forall_dSrc_inf_top eOpen_injective h3 hVfin).elim
  -- V contains 𝟙_⊤; refine it through cS0 ⇒ ⊤ ≤ eOpen n ⇒ contradiction.
  obtain ⟨f, hf⟩ := hV2
  obtain ⟨Y, fS, hh, hScov, -⟩ := hVref f hf
  cases hScov with
  | mk n => exact eOpen_ne_top n (top_le_iff.mp (wLeOfHom hh))

/-- **Statement (C) — (1) ⇏ (2).** There exists a site (`C`, `K`, `U`) such that
`U` is quasi-compact but does not have the finite refinement property. -/
@[stacks 0D05 "(1)⇏(2)"]
theorem exists_quasiCompact_not_finiteRefinement :
    ∃ (C : Type) (_ : Category C) (_ : Limits.HasPullbacks C)
      (K : Pretopology C) (U : C), IsQuasiCompact K U ∧ ¬ HasFiniteRefinement K U :=
  ⟨WObj, inferInstance, inferInstance, cSite, ⊤,
    cSite_quasiCompact, cSite_not_finiteRefinement⟩

end StacksProblem
