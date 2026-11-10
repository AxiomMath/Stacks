module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Abelian.Pseudoelements
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Order.SuccPred.Int
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Ring.Basic
public import StacksFrontier.Algebra.Homology.Resolution.Defs.ProjectiveResolution
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Bounded-above complexes of projectives: vanishing and homotopy lifting

Cohomology of complexes with a projective resolution ([Stacks, Tag 0645]), maps from bounded-above
complexes of projectives into acyclic complexes are null-homotopic ([Stacks, Tag 0647]), and
lifting along maps that are isomorphisms on high cohomology up to homotopy ([Stacks, Tag 064E]).
-/

section

@[expose] public section

/-
# Problem Description

Throughout, `A` is an abelian category and a *complex* `K^•` of `A` is a cochain
complex
  `... → K^{n-1} → K^n → K^{n+1} → ...`,  `n ∈ ℤ`,
indexed by the integers, with `d_K^n ∘ d_K^{n-1} = 0` for all `n`.  Its `n`-th
cohomology object is `H^n(K^•) = Ker(d_K^n) / Im(d_K^{n-1})`.

This is Stacks Tag 0645 (Lemma 13.19.2): for a complex `K^•` of an abelian
category `A`,

1. If `K^•` has a projective resolution (Stacks Tag 0644, Definition 13.19.1),
   then `H^n(K^•) = 0` for `n ≫ 0`.

2. If `H^n(K^•) = 0` for `n ≫ 0`, then there exists a quasi-isomorphism
   `L^• → K^•` with `L^•` bounded above.

## Notes and Interpretation

- The two parts are independent claims about the single complex `K^•`; part (2)
  is NOT a converse asserting the existence of a projective resolution -- it only
  asserts the existence of a quasi-isomorphism from some bounded-above complex.

- "`n ≫ 0`" means "for all sufficiently large `n`": there exists a threshold `N`
  beyond which the stated property holds for every `n ≥ N`.

- A zero object/morphism is understood in the sense of the abelian category `A`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Stacks.ProjectiveResolution.CohomologyVanishing

-- A complex of `A` is modeled as a cochain complex `CochainComplex A ℤ`, i.e. a
-- `HomologicalComplex A (ComplexShape.up ℤ)`.  A morphism of complexes is a
-- morphism in this category, which automatically packages the family of maps
-- `α^n : L^n → K^n` together with the commutation with differentials.
-- The `n`-th cohomology object is `K.homology n` (which exists since an abelian
-- category has all homology).

variable {A : Type*} [Category A] [Abelian A]

-- Main Definition(s)

/-- **Definition 2 (Bounded above complex).**  A complex `L^•` is *bounded above*
if there exists an integer `N` such that `L^n = 0` (a zero object) for all
`n > N`. -/
def IsBoundedAboveComplex (L : CochainComplex A ℤ) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, N < n → IsZero (L.X n)

/-- **Definition 3 (Vanishing for `n ≫ 0`).**  The phrase
"`H^n(K^•) = 0` for `n ≫ 0`" means: there exists an integer `N` such that
`H^n(K^•)` is a zero object for all `n ≥ N`. -/
def CohomologyVanishesForLargeN (K : CochainComplex A ℤ) : Prop :=
  ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K.homology n)

/-- **Definition 4 (Projective resolution of a complex).**  (Stacks Tag 0644,
Definition 13.19.1.)  A *projective resolution* of a complex `K^•` is a complex
`P^•` together with a morphism of complexes `α : P^• → K^•` such that:
1. `P^•` is bounded above;
2. each `P^n` is a projective object of `A`;
3. `α` is a quasi-isomorphism.

(`QuasiIso α` is Definition 1: the induced maps on cohomology `H^n(α)` are
isomorphisms for every `n`.  Note that the data of a `CochainComplex` morphism
`α : P ⟶ K` already encodes the family `α^n : P^n → K^n` commuting with the
differentials.) -/
structure IsProjectiveResolution (K : CochainComplex A ℤ) where
  /-- The bounded-above complex of projectives. -/
  P : CochainComplex A ℤ
  /-- The morphism of complexes `P^• → K^•`. -/
  α : P ⟶ K
  /-- `P^•` is bounded above. -/
  boundedAbove : IsBoundedAboveComplex P
  /-- Each `P^n` is projective. -/
  projective : ∀ n : ℤ, Projective (P.X n)
  /-- `α` is a quasi-isomorphism. -/
  quasiIso : QuasiIso α

-- Main Statement(s)

/-- **Stacks Tag 0645, Lemma 13.19.2, part (1).**  If `K^•` has a projective
resolution, then `H^n(K^•) = 0` for `n ≫ 0`. -/
@[stacks 0645 "(1)"]
theorem cohomology_vanishes_of_isProjectiveResolution
    (K : CochainComplex A ℤ) (h : IsProjectiveResolution K) :
    CohomologyVanishesForLargeN K := by
  obtain ⟨N, hN⟩ := h.boundedAbove
  refine ⟨N + 1, fun n hn => ?_⟩
  -- `P.X n` is a zero object since `N < n`.
  have hPzero : IsZero (h.P.X n) := hN n (by omega)
  -- Hence `H^n(P) = 0`.
  have hPhom : IsZero (h.P.homology n) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    rw [HomologicalComplex.exactAt_iff]
    exact ShortComplex.exact_of_isZero_X₂ _ hPzero
  -- The quasi-isomorphism `α` induces an isomorphism on homology.
  have : QuasiIso h.α := h.quasiIso
  have hiso : IsIso (HomologicalComplex.homologyMap h.α n) :=
    instIsIsoHomologyMapOfQuasiIsoAt h.α n
  exact hPhom.of_iso (asIso (HomologicalComplex.homologyMap h.α n)).symm

/-- **Stacks Tag 0645, Lemma 13.19.2, part (2).**  If `H^n(K^•) = 0` for
`n ≫ 0`, then there exists a quasi-isomorphism `L^• → K^•` with `L^•` bounded
above. -/
@[stacks 0645 "(2)"]
theorem exists_boundedAbove_quasiIso_of_cohomologyVanishes
    (K : CochainComplex A ℤ) (h : CohomologyVanishesForLargeN K) :
    ∃ (L : CochainComplex A ℤ) (f : L ⟶ K), IsBoundedAboveComplex L ∧ QuasiIso f := by
  obtain ⟨N, hN⟩ := h
  set M : ℤ := N - 1 with hM
  -- `K` is bounded above (in the cohomological sense `IsLE`) by `M`:
  -- for `i > M = N - 1`, i.e. `i ≥ N`, the cohomology vanishes.
  have hLE : K.IsLE M := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact hN i (by omega)
  -- Take `L` to be the canonical truncation `τ_{≤M} K`, which is bounded above,
  -- together with the inclusion `ιTruncLE`, which is a quasi-isomorphism since
  -- `K.IsLE M`.
  refine ⟨K.truncLE M, K.ιTruncLE M, ?_, ?_⟩
  · exact ⟨M, fun n hn => CochainComplex.isZero_of_isStrictlyLE (K.truncLE M) M n hn⟩
  · rw [CochainComplex.quasiIso_ιTruncLE_iff]
    exact hLE

end Stacks.ProjectiveResolution.CohomologyVanishing

end

end

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Throughout, `A` denotes an abelian category, and complexes are cochain complexes
indexed by `Z` (objects `X^i` for `i in Z` with differentials `d^i : X^i -> X^{i+1}`
satisfying `d^{i+1} \circ d^i = 0`). In Mathlib these are `CochainComplex C Z` where
`C` is an `Abelian` category.

This is Stacks Tag 0647, Lemma 13.19.4: Let `A` be an abelian category. Let
`K^*` be an acyclic complex, and let `P^*` be a complex that is bounded above and
consists of projective objects. Then any morphism of complexes `f : P^* -> K^*`
is homotopic to zero.
-/

open CategoryTheory

/-- Exactness at `i` of a complex gives exactness of the short complex `K^{i-1} → K^i → K^{i+1}`. -/
private theorem sc'_exact_of_exactAt {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ) (i : ℤ) (h : K.ExactAt i) : (K.sc' (i-1) i (i+1)).Exact :=
  (K.exactAt_iff' (i-1) i (i+1) (by simp) (by simp)).1 h

/-- The cocycle condition for `f.f p - d ≫ s` reduces to a relation at degree `p + 1`. -/
private theorem sub_comp_d_eq_comp_sub {C : Type*} [Category C] [Abelian C]
    {P K : CochainComplex C ℤ} (f : P ⟶ K) (p : ℤ) (s : P.X (p + 1) ⟶ K.X p) :
    (f.f p - P.d p (p+1) ≫ s) ≫ K.d p (p+1)
      = P.d p (p+1) ≫ (f.f (p+1) - s ≫ K.d p (p+1)) := by
  simp [Preadditive.sub_comp]

namespace ProjAcyclic

variable {C : Type*} [Category C] [Abelian C]
  (P K : CochainComplex C ℤ) (n : ℤ)
  (hProj : ∀ i : ℤ, Projective (P.X i))
  (hK : HomologicalComplex.Acyclic K)
  (f : P ⟶ K)

include hK in
/-- The relevant short complex `K^{i-1} → K^i → K^{i+1}` is exact, by acyclicity. -/
theorem exactAt (i : ℤ) : (K.sc' (i-1) i (i+1)).Exact := by
  exact sc'_exact_of_exactAt K i (hK i)

open Classical in
/-- The homotopy map at degree `i`, built by descending recursion: it is `0` above
the bound `n`, and below the bound it lifts `f.f i - d_P ≫ φ(i+1)` through the
epimorphism onto the kernel using projectivity of `P.X i`. -/
noncomputable def φ (i : ℤ) : P.X i ⟶ K.X (i-1) :=
  if hi : n < i then 0
  else by
    haveI := hProj i
    let prev : P.X (i+1) ⟶ K.X i :=
      φ (i+1) ≫ eqToHom (by rw [show i + 1 - 1 = i from by omega])
    let g : P.X i ⟶ K.X i := f.f i - P.d i (i+1) ≫ prev
    exact
      if hg2 : g ≫ K.d i (i+1) = 0 then
        (exactAt K hK i).liftFromProjective g hg2
      else 0
  termination_by (n + 1 - i).toNat
  decreasing_by omega

/-- The "previous" homotopy map appearing in the recursion at degree `i`. -/
noncomputable def prev (i : ℤ) : P.X (i+1) ⟶ K.X i :=
  φ P K n hProj hK f (i+1) ≫ eqToHom (by rw [show i + 1 - 1 = i from by omega])

/-- The map `g i := f.f i - d_P ≫ φ(i+1)`, which is the value `φ i` lifts. -/
noncomputable def gg (i : ℤ) : P.X i ⟶ K.X i :=
  f.f i - P.d i (i+1) ≫ prev P K n hProj hK f i

/-- `φ` vanishes above the bound. -/
lemma φ_eq_zero (i : ℤ) (hi : n < i) : φ P K n hProj hK f i = 0 := by
  rw [φ, dite_eq_left hi]

open Classical in
/-- Unfolding `φ` below the bound. -/
lemma φ_eq_dite (i : ℤ) (hi : ¬ n < i) :
    φ P K n hProj hK f i =
      (haveI := hProj i
       if hg2 : gg P K n hProj hK f i ≫ K.d i (i+1) = 0 then
        (exactAt K hK i).liftFromProjective (gg P K n hProj hK f i) hg2
      else 0) := by
  conv_lhs => rw [φ]
  rw [dite_eq_right hi]
  rfl

/-- `prev i ≫ d_K = φ(i+1) ≫ d_K`, eliminating the `eqToHom` cast. -/
lemma prev_comp_d (i : ℤ) :
    prev P K n hProj hK f i ≫ K.d i (i+1)
      = φ P K n hProj hK f (i+1) ≫ K.d ((i+1)-1) (i+1) := by
  rw [prev, Category.assoc, HomologicalComplex.eqToHom_comp_d K (by simp) (by simp)]

/-- The main homotopy identity: `φ i ≫ d_K = gg i`. Proved by descending strong
induction on the bound. -/
lemma phi_spec [hP : P.IsStrictlyLE n] (i : ℤ) :
    φ P K n hProj hK f i ≫ K.d (i-1) i = gg P K n hProj hK f i := by
  -- strong induction on the distance above i to n+1
  suffices H : ∀ m : ℕ, ∀ j : ℤ, (n + 1 - j).toNat = m →
      φ P K n hProj hK f j ≫ K.d (j-1) j = gg P K n hProj hK f j by
    exact H _ i rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro j hm
    by_cases hj : n < j
    · -- above the bound: both sides vanish since P.X j is zero
      have hPzero : Limits.IsZero (P.X j) := CochainComplex.isZero_of_isStrictlyLE P n j hj
      have h1 : φ P K n hProj hK f j ≫ K.d (j-1) j = 0 := by
        rw [hPzero.eq_zero_of_src (φ P K n hProj hK f j), Limits.zero_comp]
      have h2 : gg P K n hProj hK f j = 0 := hPzero.eq_zero_of_src _
      rw [h1, h2]
    · -- below the bound: use liftFromProjective and the inductive hypothesis at j+1
      have hmeas : (n + 1 - (j+1)).toNat < m := by omega
      have IH1 : φ P K n hProj hK f (j+1) ≫ K.d ((j+1)-1) (j+1)
          = gg P K n hProj hK f (j+1) := IH _ hmeas (j+1) rfl
      -- vanishing condition
      have hvanish : gg P K n hProj hK f j ≫ K.d j (j+1) = 0 := by
        rw [gg, sub_comp_d_eq_comp_sub, prev_comp_d, IH1, gg]
        simp
      -- now φ j is the lift
      rw [φ_eq_dite P K n hProj hK f j hj, dite_eq_left hvanish]
      exact (exactAt K hK j).liftFromProjective_comp (gg P K n hProj hK f j) hvanish

end ProjAcyclic

open CategoryTheory

/-- Let `K` be an acyclic complex and `P` a bounded above complex of projective objects. Then
every morphism of complexes `f : P ⟶ K` is homotopic to zero. -/
@[stacks 0647,
  sga "6 I 4.1" "special case",
  sga "6 II 1.1" "c)",
  sga "6 II 1.2" "1.2 d), special case"]
theorem projective_into_acyclic_is_zero
    {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C]
    (P K : CochainComplex C ℤ)
    (n : ℤ) (hP : P.IsStrictlyLE n)
    (hProj : ∀ i : ℤ, CategoryTheory.Projective (P.X i))
    (hK : HomologicalComplex.Acyclic K)
    (f : P ⟶ K) : Nonempty (Homotopy f 0) := by
  have := hP
  -- Assemble the homotopy from the maps φ. The homotopy map h^i : P.X i ⟶ K.X (i-1)
  -- is φ i. In `Homotopy f 0` the field `hom i j : P.X i ⟶ K.X j` is meaningful
  -- only when `Rel j i`, i.e. `j + 1 = i` (so `j = i - 1`); there we put
  -- `φ i` transported along `K.X (i-1) ≅ K.X j`, and `0` otherwise.
  refine ⟨{
    hom := fun i j =>
      if h : j + 1 = i then
        ProjAcyclic.φ P K n hProj hK f i ≫ (K.XIsoOfEq (show i - 1 = j by omega)).hom
      else 0
    zero := fun i j h => dite_eq_right h
    comm := fun i => by
      -- f.f i = dNext i hom + prevD i hom + (0).f i.
      -- dNext i hom = P.d i (i+1) ≫ hom (i+1) i ;  prevD i hom = hom i (i-1) ≫ K.d (i-1) i.
      rw [dNext_eq _ (show (ComplexShape.up ℤ).Rel i (i+1) by simp),
          prevD_eq _ (show (ComplexShape.up ℤ).Rel (i-1) i by simp)]
      -- Simplify the two `hom` applications: both dite conditions hold.
      rw [dite_eq_left (show i + 1 = i + 1 from rfl), dite_eq_left (show (i-1) + 1 = i by omega)]
      -- Replace the `XIsoOfEq` casts with `eqToHom`.
      simp only [HomologicalComplex.zero_f, add_zero,
        show (K.XIsoOfEq (show (i+1) - 1 = i by omega)).hom
            = eqToHom (by rw [show (i+1) - 1 = i by omega]) from by
              simp [HomologicalComplex.XIsoOfEq],
        show (K.XIsoOfEq (show i - 1 = i - 1 from rfl)).hom = 𝟙 (K.X (i-1)) from by
              simp]
      -- First term is `P.d i (i+1) ≫ prev i`; second is `φ i ≫ K.d (i-1) i = gg i`.
      rw [show ProjAcyclic.φ P K n hProj hK f (i+1) ≫ eqToHom (by rw [show (i+1) - 1 = i by omega])
            = ProjAcyclic.prev P K n hProj hK f i from rfl,
          Category.comp_id,
          ProjAcyclic.phi_spec P K n hProj hK f i,
          ProjAcyclic.gg]
      -- Now: f.f i = P.d i (i+1) ≫ prev i + (f.f i - P.d i (i+1) ≫ prev i)
      abel
  }⟩

end

end

section

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Stacks Tag 064E.

Throughout, `A` denotes an abelian category, and all complexes are cochain
complexes of objects of `A` indexed by `Z` (the differential `d^i` raises degree
by one, `d^i : X^i -> X^{i+1}`, with `d^{i+1} . d^i = 0`).

Theorem. Let `A` be an abelian category. Let `β : P^• → L^•` and
`α : E^• → L^•` be maps of complexes in `A`. Let `n ∈ Z`. Assume:
1. `P^•` is a bounded complex of projectives and `P^i = 0` for all `i < n`;
2. the induced map on cohomology `H^i(α) : H^i(E^•) → H^i(L^•)` is an
   isomorphism for every `i > n`, and is an epimorphism for `i = n`.
Then there exists a map of complexes `γ : P^• → E^•` such that `α . γ` and `β`
are homotopic, i.e. `α . γ ≃ β`.
-/

-- Background and context (as comments):
--
-- * Indexing convention. The Stacks project uses cohomological (upper) indexing
--   with differentials of degree `+1`; this matches Mathlib's `CochainComplex A ℤ`
--   (a `HomologicalComplex` with `ComplexShape.up ℤ`), where the `i`-th cohomology
--   object is `HomologicalComplex.homology` in degree `i` and the induced map on
--   cohomology is `HomologicalComplex.homologyMap`.
--
-- * Projective object. An object `P` of `A` is projective if `Hom(P, -)` sends
--   epimorphisms to surjections; this is `CategoryTheory.Projective`.
--
-- * Bounded complex of projectives. Each `P^i` is projective and `P^i = 0` for all
--   but finitely many `i`. We encode "each term projective" by `hProj`, and
--   "bounded above" by `hBddAbove`. The hypothesis `P^i = 0` for `i < n`
--   (`hBelow`) already supplies boundedness below; together with `hBddAbove` it
--   gives finitely many nonzero terms, all in degrees `≥ n`.
--
-- * "`H^i(α)` is an isomorphism" means the induced map on cohomology has a
--   two-sided inverse (`CategoryTheory.IsIso`); "epimorphism for `i = n`" means it
--   is an epimorphism (`CategoryTheory.Epi`).
--
-- * Homotopy. Two maps of complexes `f, g : X^• → Y^•` are homotopic if there is a
--   family `s^i : X^i → Y^{i-1}` with `f^i - g^i = d_Y^{i-1} . s^i + s^{i+1} . d_X^i`.
--   This is Mathlib's `Homotopy`. Since the statement asserts only the existence of
--   a homotopy (which is data), we wrap it in `Nonempty`.

open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex

variable {A : Type*} [Category A] [Abelian A]

/-- Comparison theorem (null-homotopy form). A chain map `f : P ⟶ C` of cochain
complexes over an abelian category, where `P` is a bounded-below complex of
projectives (each `P.X i` projective, `P.X i = 0` for `i < n`, and bounded above)
and `C` is acyclic in degrees `≥ n` (`IsZero (C.homology i)` for `i ≥ n`), is
null-homotopic.

The homotopy `s^i : P^i → C^{i-1}` is built by descending induction on the degree:
for `i < n`, `P^i = 0` forces `s^i = 0`; for `i ≥ n`, the difference
`g^i := f^i - d_P^i ≫ s^{i+1}` is a cocycle (lands in `ker d_C^i`), and by
acyclicity `ker d_C^i = im d_C^{i-1}`, so it lifts through the boundary epi using
projectivity of `P^i` (`ShortComplex.Exact.liftFromProjective`). Assembling the
`s^i` into a cochain `z : Cochain P C (-1)` yields `δ (-1) 0 z = Cochain.ofHom f`,
i.e. a homotopy `f ≃ 0`. -/
@[sga "6 I 4.1" "special case",
  sga "6 II 1.1" "c), special case",
  sga "6 II 1.2" "1.2 d), special case"]
theorem null_homotopic_of_projective_acyclic
    (P C : CochainComplex A ℤ) (f : P ⟶ C) (n : ℤ)
    (hProj : ∀ i, Projective (P.X i))
    (hac : ∀ i : ℤ, n ≤ i → IsZero (C.homology i))
    (hBelow : ∀ i, i < n → IsZero (P.X i))
    (hBddAbove : ∃ b : ℤ, ∀ i, b < i → IsZero (P.X i)) :
    Nonempty (Homotopy f 0) := by
  classical
  -- The single inductive lift step: given the homotopy terms `snext = s^{p+1}`
  -- and `snextnext = s^{p+2}` satisfying the tail relation at `p+1`, produce
  -- `sp = s^p : P^p → C^{p-1}` satisfying the relation at `p`. For `p ≥ n` use
  -- acyclicity + projectivity (`ShortComplex.Exact.liftFromProjective`); for
  -- `p < n` take `sp = 0` since `P^p = 0`.
  have zero_rel : ∀ (q : ℤ), IsZero (P.X q) → ∀ (a : P.X q ⟶ C.X (q - 1))
      (b : P.X (q + 1) ⟶ C.X q), f.f q = a ≫ C.d (q - 1) q + P.d q (q + 1) ≫ b := by
    intro q hPz a b
    rw [hPz.eq_of_src (f.f q) 0, hPz.eq_of_src (P.d q (q + 1)) 0, hPz.eq_of_src a 0]
    simp
  have step : ∀ (p : ℤ),
      ∀ (snext : P.X (p+1) ⟶ C.X p) (snextnext : P.X (p+2) ⟶ C.X (p+1)),
      f.f (p+1) = snext ≫ C.d p (p+1) + P.d (p+1) (p+2) ≫ snextnext →
      { sp : P.X p ⟶ C.X (p-1) // f.f p = sp ≫ C.d (p-1) p + P.d p (p+1) ≫ snext } := by
    intro p snext snextnext hRnext
    by_cases hp : n ≤ p
    · have := hProj p
      set g : P.X p ⟶ C.X p := f.f p - P.d p (p+1) ≫ snext with hg
      have hexact : (C.sc' (p-1) p (p+1)).Exact := sc'_exact_of_exactAt C p
        ((HomologicalComplex.exactAt_iff_isZero_homology C p).2 (hac p hp))
      have hSg : (C.sc' (p-1) p (p+1)).g = C.d p (p+1) := by
        simp [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      have hSf : (C.sc' (p-1) p (p+1)).f = C.d (p-1) p := by
        simp [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor']
      have hgcocyc : g ≫ (C.sc' (p-1) p (p+1)).g = 0 := by
        rw [hSg, hg, sub_comp_d_eq_comp_sub, hRnext]
        simp
      refine ⟨hexact.liftFromProjective g hgcocyc, ?_⟩
      have hlift := hexact.liftFromProjective_comp g hgcocyc
      rw [hSf] at hlift
      have hfp : f.f p = g + P.d p (p+1) ≫ snext := by rw [hg]; abel
      rw [hfp]; congr 1; exact hlift.symm
    · have hPz : IsZero (P.X p) := hBelow p (not_le.mp hp)
      exact ⟨0, zero_rel p hPz _ _⟩
  -- Assemble the per-degree `step` into a global homotopy family `s` defined on
  -- all degrees, satisfying the homotopy relation everywhere. The family is built
  -- by descending recursion: above the bounded-above threshold `s = 0`; each
  -- `step` lowers the floor by one. `eqToHom` transports `s (q+1) : P.X (q+1) ⟶
  -- C.X ((q+1)-1)` to the codomain `C.X q` needed to compose with `P.d q (q+1)`.
  -- SUBGOAL hFamily: produce the global homotopy family with its relation.
  -- SANITY CHECK PASSED: descending recursion from bounded-above base `B+1` down to
  -- floor `n` via `step`; below `n`, `P.X q = 0` makes the relation hold vacuously.
  have hFamily : ∃ s : ∀ q : ℤ, P.X q ⟶ C.X (q - 1), ∀ q : ℤ,
      f.f q = s q ≫ C.d (q - 1) q
        + P.d q (q + 1) ≫ (s (q + 1) ≫ eqToHom (by rw [show q + 1 - 1 = q from by omega])) := by
    obtain ⟨b, hb⟩ := hBddAbove
    set B : ℤ := max b (n - 1) with hB
    have hBz : ∀ i, B < i → IsZero (P.X i) :=
      fun i hi => hb i (lt_of_le_of_lt (le_max_left b (n-1)) hi)
    -- The relation R s q, exactly matching the goal (with eqToHom on s (q+1)).
    let R : (∀ q : ℤ, P.X q ⟶ C.X (q - 1)) → ℤ → Prop :=
      fun s q => f.f q = s q ≫ C.d (q - 1) q
        + P.d q (q + 1) ≫ (s (q + 1) ≫ eqToHom (by rw [show q + 1 - 1 = q from by omega]))
    let T : ℤ → Type _ :=
      fun d => { s : ∀ q : ℤ, P.X q ⟶ C.X (q - 1) // ∀ q : ℤ, d ≤ q → R s q }
    -- builder: from T (d+1) produce T d
    have buildT : ∀ (d : ℤ), T (d + 1) → T d := by
      intro d t
      obtain ⟨s, hs⟩ := t
      -- relation at d+1 (in `step` form)
      have hRnext : f.f (d + 1) = (s (d+1) ≫ eqToHom (by rw [show d + 1 - 1 = d from by omega]))
          ≫ C.d d (d+1) + P.d (d+1) (d+2)
            ≫ (s (d+2) ≫ eqToHom (by rw [show d + 2 - 1 = d + 1 from by omega])) := by
        have h := hs (d+1) (le_refl _)
        simp only [R] at h
        rw [h]
        congr 1
        · -- first summand
          rw [Category.assoc]
          congr 1
          exact (HomologicalComplex.eqToHom_comp_d C (by simp) (by simp)).symm
        · -- second summand: indices d+1+1 vs d+2 differ
          have key : ∀ (j : ℤ) (hj : d + 1 + 1 = j),
              P.d (d+1) (d+1+1) ≫ (s (d+1+1) ≫ eqToHom (show C.X (d+1+1-1) = C.X (d+1) by rw [show
                  d+1+1-1 = d+1 from by omega]))
                = P.d (d+1) j ≫ (s j ≫ eqToHom (show C.X (j-1) = C.X (d+1) by rw [← hj]; rw [show
                    d+1+1-1 = d+1 from by omega])) := by
            intro j hj; subst hj; rfl
          rw [key (d+2) (by omega)]
      obtain ⟨sp, hsp⟩ := step d (s (d+1) ≫ eqToHom (by rw [show d + 1 - 1 = d from by omega]))
        (s (d+2) ≫ eqToHom (by rw [show d + 2 - 1 = d + 1 from by omega])) hRnext
      refine ⟨fun q => if d + 1 ≤ q then s q else
          if h : q = d then eqToHom (by rw [h]) ≫ sp ≫ eqToHom (by rw [h]) else 0, ?_⟩
      intro q hq
      rcases eq_or_lt_of_le hq with h | h
      · -- q = d
        subst h
        simp only [R]
        rw [ite_eq_right (show ¬ (d + 1 ≤ d) by omega), ite_eq_left (show d + 1 ≤ d + 1 by omega),
          dite_eq_left True.intro]
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        exact hsp
      · -- q ≥ d+1
        have hq1 : d + 1 ≤ q := by omega
        have hq2 : d + 1 ≤ q + 1 := by omega
        have e1 : (if d + 1 ≤ q then s q else
            if h : q = d then eqToHom (by rw [h]) ≫ sp ≫ eqToHom (by rw [h]) else 0) = s q := by
          rw [ite_eq_left hq1]
        have e2 : (if d + 1 ≤ q + 1 then s (q+1) else
            if h : q + 1 = d then eqToHom (by rw [h]) ≫ sp ≫ eqToHom (by rw [h]) else 0)
            = s (q+1) := by rw [ite_eq_left hq2]
        simp only [R]
        rw [e1, e2]
        exact hs q hq1
    -- base case: T (B+1) with zero family
    have hBase : T (B + 1) := by
      refine ⟨fun _ => 0, ?_⟩
      intro q hq
      exact zero_rel q (hBz q (by omega)) _ _
    -- descend by Nat induction
    have descend : ∀ k : ℕ, T (B + 1 - k) := by
      intro k
      induction k with
      | zero => simpa using hBase
      | succ m ih =>
          have ht : T (B + 1 - m) := ih
          have hb2 : T ((B + 1 - (m + 1 : ℕ)) + 1) := by
            have e : (B + 1 - (m + 1 : ℕ)) + 1 = B + 1 - m := by push_cast; omega
            rw [e]; exact ht
          exact buildT (B + 1 - (m + 1 : ℕ)) hb2
    -- choose k so that B+1-k ≤ n
    set k : ℕ := (B + 1 - n).toNat with hk
    obtain ⟨s, hs'⟩ := descend k
    have hkle : B + 1 - k ≤ n := by
      rw [hk]
      omega
    refine ⟨s, ?_⟩
    intro q
    by_cases hqn : n ≤ q
    · exact hs' q (by omega)
    · -- q < n : P.X q = 0, relation holds vacuously
      exact zero_rel q (hBelow q (not_le.mp hqn)) _ _
  -- SUBGOAL hAssemble: from the global homotopy family `s` with its relation,
  -- build the cochain `z : Cochain P C (-1)` (`z.v p q hpq` from `s p` plus an
  -- `eqToHom` transport across `p - 1 = q`) and show `δ (-1) 0 z = Cochain.ofHom f`
  -- via `HomComplex.δ_v` (matching `s q ≫ d` and `d ≫ s (q+1)` summands); then
  -- `Nonempty (Homotopy f 0)` follows from `(Cochain.equivHomotopy f 0).symm`.
  obtain ⟨s, hs⟩ := hFamily
  let z : Cochain P C (-1) :=
    Cochain.mk (fun p q hpq => s p ≫ eqToHom (by rw [show p - 1 = q from by omega]))
  refine ⟨(Cochain.equivHomotopy f 0).symm ⟨z, ?_⟩⟩
  rw [Cochain.ofHom_zero, add_zero]
  apply Cochain.ext
  intro p q hpq
  obtain rfl : q = p := by omega
  rw [δ_v (-1) 0 (by omega) z q q hpq (q - 1) (q + 1) (by omega) (by omega)]
  rw [Cochain.ofHom_v, Cochain.mk_v, Cochain.mk_v]
  rw [hs q]
  simp only [Int.negOnePow_zero, one_smul, eqToHom_refl, Category.comp_id]


-- Main Statement(s)

/-- Stacks Tag 064E. Let `β : P^• → L^•` and `α : E^• → L^•` be maps of cochain
complexes in an abelian category `A`, and `n : ℤ`. Assume `P^•` is a bounded
complex of projectives with `P^i = 0` for `i < n`, and that `H^i(α)` is an
isomorphism for `i > n` and an epimorphism for `i = n`. Then there is a chain map
`γ : P^• → E^•` with `α ∘ γ` homotopic to `β`. -/
@[stacks 064E, sga "6 II 1.1" "c), special case"]
theorem exists_lift_homotopy_of_projective (P E L : CochainComplex A ℤ)
    (β : P ⟶ L) (α : E ⟶ L) (n : ℤ)
    (hProj : ∀ i, Projective (P.X i))
    (hBddAbove : ∃ b : ℤ, ∀ i, b < i → IsZero (P.X i))
    (hBelow : ∀ i, i < n → IsZero (P.X i))
    (hIso : ∀ i, n < i → IsIso (HomologicalComplex.homologyMap α i))
    (hEpi : Epi (HomologicalComplex.homologyMap α n)) :
    ∃ γ : P ⟶ E, Nonempty (Homotopy (γ ≫ α) β) := by
  classical
  -- Step 1: the cohomology of the cone vanishes in degrees `≥ n`.
  -- SUBLEMMA (hCone_acyclic). Rigorous argument:
  --   Let `C = mappingCone α`. Mathlib gives a distinguished triangle
  --   `E → L → C → E[1]` (the mapping-cone triangle for `α`), hence a long exact
  --   homology sequence; concretely, for each `i` there is an exact sequence
  --     H^i(E) --H^i(α)--> H^i(L) --H^i(inr)--> H^i(C)
  --                 --∂--> H^{i+1}(E) --H^{i+1}(α)--> H^{i+1}(L).
  --   In an abelian category `H^i(C) = 0` iff the incoming map `H^i(L) → H^i(C)`
  --   is zero AND the outgoing map `H^i(C) → H^{i+1}(E)` is zero, which by
  --   exactness happens iff `H^i(α)` is epi and `H^{i+1}(α)` is mono.
  --   For `i ≥ n`: `H^i(α)` is epi — it is iso for `i > n` (hIso) and epi at
  --   `i = n` (hEpi); and `H^{i+1}(α)` is iso (since `i+1 > n`), hence mono.
  --   Therefore `H^i(C) = 0` for all `i ≥ n`.
  -- STRATEGY for formal phase: use Mathlib's mapping-cone homology API. Key API:
  --   `CochainComplex.mappingCone.triangle α` is distinguished
  --   (`CochainComplex.mappingCone.triangle_distinguished`), and the homology
  --   LES of a distinguished triangle in `D(A)` / via
  --   `HomologicalComplex` long exact sequences. Alternatively use the
  --   short/long exact homology sequence machinery
  --   (`CategoryTheory.ShortComplex`, `HomologicalComplex.homologySequence`) for
  --   the cone. The cleanest path may be: the cone's homology sits in the LES of
  --   the cone triangle (`mappingCone.homology_...`), then
  --   `IsZero.of_epi_of_isIso`-style reasoning. Decompose further into:
  --     (a) `H^i(inr) = 0` for `i ≥ n` (from `H^i(α)` epi via exactness), and
  --     (b) connecting map `H^i(C) → H^{i+1}(E)` zero (from `H^{i+1}(α)` mono),
  --   then conclude `IsZero (C.homology i)` from these two vanishings + exactness.
  -- SANITY CHECK PASSED: cone is `E^{i+1} ⊕ L^i` (Mathlib convention, `inl` degree -1),
  -- so the LES puts `H^i(C)` between `H^i(L)` and `H^{i+1}(E)`; the `n ≤ i` bound is
  -- exactly aligned (mono requirement lands at `i+1 > n`). No counterexample.
  have hCone_acyclic : ∀ i : ℤ, n ≤ i →
      IsZero ((CochainComplex.mappingCone α).homology i) := by
    set F := HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) 0 with hF
    set Q := HomotopyCategory.quotient A (ComplexShape.up ℤ) with hQ
    have transfer : ∀ m : ℤ, (F.shift m).map ((CochainComplex.mappingCone.triangleh α).mor₁)
        = (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) m).hom.app E ≫
          (HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) m).map α ≫
          (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) m).inv.app L := by
      intro m
      have nat := (HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) m).hom.naturality α
      have h0 : (Q ⋙ HomotopyCategory.homologyFunctor A (ComplexShape.up ℤ) m).map α
          = (F.shift m).map ((CochainComplex.mappingCone.triangleh α).mor₁) := rfl
      rw [← h0, ← Category.assoc, ← nat, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    have transfer_epi : ∀ m : ℤ, Epi (HomologicalComplex.homologyMap α m) →
        Epi ((F.shift m).map ((CochainComplex.mappingCone.triangleh α).mor₁)) := by
      intro m hm
      have : Epi ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) m).map α) := hm
      rw [transfer]
      infer_instance
    have transfer_iso : ∀ m : ℤ, IsIso (HomologicalComplex.homologyMap α m) →
        IsIso ((F.shift m).map ((CochainComplex.mappingCone.triangleh α).mor₁)) := by
      intro m hm
      have : IsIso ((HomologicalComplex.homologyFunctor A (ComplexShape.up ℤ) m).map α) := hm
      rw [transfer]
      infer_instance
    intro i hi
    set T := CochainComplex.mappingCone.triangleh α with hT
    have hdist : T ∈ Pretriangulated.distinguishedTriangles :=
        HomotopyCategory.mappingCone_triangleh_distinguished α
    have hmor1_epi : Epi ((F.shift i).map T.mor₁) := by
      apply transfer_epi
      rcases lt_or_eq_of_le hi with h | h
      · have := hIso i h; infer_instance
      · rw [← h]; exact hEpi
    have hmor1_iso : IsIso ((F.shift (i+1)).map T.mor₁) := transfer_iso (i+1) (hIso (i+1) (by
        omega))
    have hδ0 : F.homologySequenceδ T i (i+1) (by omega) = 0 := by
      rw [← F.homologySequence_mono_shift_map_mor₁_iff T hdist i (i+1) (by omega)]
      have := hmor1_iso; infer_instance
    have hmor2_epi : Epi ((F.shift i).map T.mor₂) := by
      rw [F.homologySequence_epi_shift_map_mor₂_iff T hdist i (i+1) (by omega)]
      exact hδ0
    have e2 := F.homologySequence_exact₂ T hdist i
    have : Epi ((F.shift i).map T.mor₁) := hmor1_epi
    have hmor2_zero : (F.shift i).map T.mor₂ = 0 := (ShortComplex.Exact.epi_f_iff e2).mp hmor1_epi
    have := hmor2_epi
    have hzero : IsZero ((F.shift i).obj T.obj₃) :=
      IsZero.of_epi_eq_zero ((F.shift i).map T.mor₂) hmor2_zero
    set fac := HomotopyCategory.homologyFunctorFactors A (ComplexShape.up ℤ) i with hfac
    have hiso3 : (F.shift i).obj T.obj₃ ≅ (CochainComplex.mappingCone α).homology i :=
      fac.app (CochainComplex.mappingCone α)
    exact hzero.of_iso hiso3.symm
  -- Step 2: the composite `β ≫ inr : P → C` is null-homotopic, because `P` is a
  -- bounded-below complex of projectives and `C` is acyclic in degrees `≥ n`.
  -- SUBLEMMA (hNull). Rigorous argument:
  --   `f := β ≫ inr : P → C`. The complex `P` is a complex of projectives with
  --   `P^i = 0` for `i < n` (hBelow, hProj), so `P` is bounded below (concentrated
  --   in degrees `≥ n`). The cone `C` is acyclic in degrees `≥ n` (hCone_acyclic).
  --   Standard homological algebra: a chain map from a bounded-below complex of
  --   projectives `P` (concentrated in degrees `≥ n`) into a complex `C` that is
  --   exact (acyclic) in all degrees `≥ n` is null-homotopic. Construct the
  --   homotopy `s^i : P^i → C^{i-1}` by descending induction on the degree using
  --   projectivity: for `i < n`, `P^i = 0` so `s^i = 0`. For `i ≥ n`, given
  --   `s^{i+1}` already chosen so that `f^{i+1} - d_C s^{i+1} - s^{i+2} d_P` (the
  --   tail relation) holds, set `g^i := f^i - s^{i+1} ∘ d_P^i : P^i → C^i`; one
  --   checks `g^i` is a cocycle landing in `ker d_C^i = im d_C^{i-1}` (uses
  --   acyclicity of `C` at degree `i ≥ n`, i.e. `H^i(C) = 0`, equivalently the
  --   cycles = boundaries), and lifts through the epi `Z^{i-1}(C) ↠ B^i(C)` to
  --   `s^i : P^i → C^{i-1}` using projectivity of `P^i` (hProj). The recursion is
  --   well-founded because `P` is bounded below.
  -- STRATEGY for formal phase: this is the "comparison theorem for projective
  -- resolutions"-style lifting. Look for Mathlib API on null-homotopy of maps out
  -- of bounded-below projective complexes into acyclic complexes — e.g.
  --   `CochainComplex` / `HomologicalComplex` homotopy-category lemmas, or the
  --   `ProjectiveResolution` / `liftf` machinery generalized. If no single lemma
  --   exists, decompose into: (i) acyclicity ⇒ `C` is exact at each degree ≥ n
  --   (`HomologicalComplex.exactAt`), and (ii) an inductive construction of the
  --   homotopy via `Projective.factorThru` over the epi onto boundaries. This
  --   leaf likely needs its own multi-step decomposition in the formal phase.
  -- SANITY CHECK PASSED: standard projective-comparison null-homotopy; range of
  -- acyclicity (degrees ≥ n) matches range where `P` is nonzero, no off-by-one.
  have hNull : Nonempty (Homotopy (β ≫ CochainComplex.mappingCone.inr α) 0) :=
    null_homotopic_of_projective_acyclic P (CochainComplex.mappingCone α)
      (β ≫ CochainComplex.mappingCone.inr α) n hProj hCone_acyclic hBelow hBddAbove
  -- Step 3: extract from the null-homotopy of `β ≫ inr` a lift `γ : P → E`
  -- together with a homotopy `α ∘ γ ≃ β`, using the structure of the cone.
  obtain ⟨H⟩ := hNull
  obtain ⟨z, hz⟩ := (Cochain.equivHomotopy _ _) H
  simp only [Cochain.ofHom_zero, add_zero] at hz
  have hδz : δ (-1) 0 z = Cochain.ofHom (β ≫ CochainComplex.mappingCone.inr α) := hz.symm
  set fst : Cochain (CochainComplex.mappingCone α) E 1 :=
    (CochainComplex.mappingCone.fst α : Cochain (CochainComplex.mappingCone α) E 1) with hfst
  set snd : Cochain (CochainComplex.mappingCone α) L 0 := CochainComplex.mappingCone.snd α with hsnd
  have hγδ : δ 0 1 (z.comp fst (by omega)) = 0 := by
    rw [δ_comp z fst (by omega) 0 2 1 (by omega) (by omega) (by omega)]
    rw [Cocycle.δ_eq_zero]
    rw [Cochain.comp_zero, zero_add]
    rw [hδz]
    rw [Cochain.ofHom_comp]
    rw [Cochain.comp_assoc (Cochain.ofHom β) (Cochain.ofHom (CochainComplex.mappingCone.inr α)) fst
      (show (0:ℤ)+0=0 by omega) (show (0:ℤ)+1=1 by omega) (show (0:ℤ)+0+1=1 by omega)]
    rw [CochainComplex.mappingCone.inr_fst]
    rw [Cochain.comp_zero]
    simp
  let γc : Cocycle P E 0 := Cocycle.mk (z.comp fst (by omega)) 1 (by omega) hγδ
  refine ⟨Cocycle.homOf γc, ⟨?_⟩⟩
  refine (Cochain.equivHomotopy _ _).symm ⟨-(z.comp snd (by omega)), ?_⟩
  rw [Cochain.ofHom_comp, Cocycle.cochain_ofHom_homOf_eq_coe]
  have hγc : (γc : Cochain P E 0) = z.comp fst (by omega) := rfl
  rw [hγc]
  rw [δ_neg]
  rw [δ_comp z snd (by omega) 0 1 0 (show (-1:ℤ)+1=0 by omega) (show (-1:ℤ)+1=0 by omega)
    (show (0:ℤ)+1=1 by omega)]
  rw [CochainComplex.mappingCone.δ_snd]
  rw [hδz]
  rw [Cochain.comp_neg, Cochain.ofHom_comp,
    Cochain.comp_assoc (Cochain.ofHom β) (Cochain.ofHom (CochainComplex.mappingCone.inr α)) snd
      (show (0:ℤ)+0=0 by omega) (show (0:ℤ)+0=0 by omega) (show (0:ℤ)+0+0=0 by omega),
    CochainComplex.mappingCone.inr_snd, Cochain.comp_id]
  rw [← Cochain.comp_assoc z fst (Cochain.ofHom α)
      (show (-1:ℤ)+1=0 by omega) (show (1:ℤ)+0=1 by omega) (show (-1:ℤ)+1+0=0 by omega)]
  simp only [Int.negOnePow_zero, one_smul, hfst]
  abel

end

end
