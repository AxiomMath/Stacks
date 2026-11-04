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
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Int.SuccPred
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.Ring.Basic
public import StacksFrontier.Algebra.Homology.Resolution.Defs.ProjectiveResolution
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Projective resolutions of complexes: resolution data

The complex `A[0]`, projective resolutions of objects ([Stacks, Tag 0646] (1)), the data
`EpiResData` of an epimorphic projective resolution, and its descending-recursion construction
`ExistsEpiResDataAux`.
-/

section

@[expose] public section

/-
# Problem Description

(Stacks, Lemma 13.19.3, Tag 0646.)

Let `A` be an abelian category. We work with cochain complexes
`K^• = (K^n, d_K^n)` indexed by `ℤ`, with differentials `d_K^n : K^n → K^{n+1}`
satisfying `d_K^{n+1} ∘ d_K^n = 0`. The cohomology objects are
`H^n(K^•) = Ker(d_K^n) / Im(d_K^{n-1})`.
A morphism of complexes is a *quasi-isomorphism* if it induces isomorphisms on all
cohomology objects.

We assume `A` has enough projectives. Then:

* Statement 1: every object `A` has a projective resolution.
* Statement 2: every complex `K^•` with `H^n(K^•) = 0` for `n ≫ 0` has a
  projective resolution by a bounded-above complex of projectives.
* Statement 3: every complex `K^•` with `K^n = 0` for `n > a` admits a
  projective resolution `α : P^• → K^•` with `P^n = 0` for `n > a` and with each
  component `α^n` an epimorphism.
-/

-- ## Background and context
--
-- Definition 1 (Projective object): `P` is projective if `Hom(P, -)` is exact;
--   in Mathlib this is `CategoryTheory.Projective`.
-- Definition 2 (Enough projectives): for every object `A` there is a projective
--   `P` with an epimorphism `P → A`; in Mathlib this is
--   `CategoryTheory.EnoughProjectives`.
--
-- We use cochain complexes indexed by `ℤ`, i.e. `CochainComplex C ℤ`
-- (`HomologicalComplex C (ComplexShape.up ℤ)`). For such a complex, the
-- cohomology object `H^n` is `HomologicalComplex.homology`, and a morphism `f`
-- is a quasi-isomorphism iff `CategoryTheory.QuasiIso f` holds. The boundedness
-- condition `K^n = 0` for `n > a` is `CochainComplex.IsStrictlyLE K a`, which
-- unfolds to `∀ i, a < i → IsZero (K.X i)` (see `CochainComplex.isStrictlyLE_iff`).

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace ProjectiveResolutionLemma

variable {C : Type*} [Category C] [Abelian C]

-- ## Main Definition(s)

/-- The complex `A[0]`: the object `A` placed in cohomological degree `0`. -/
@[sga "4½ Fonctions_L 1.11" "degree 0"]
noncomputable def single₀ (A : C) : CochainComplex C ℤ :=
  (HomologicalComplex.single C (ComplexShape.up ℤ) 0).obj A

/-- A cochain complex concentrated in degree `0` with `X 0 ≅ A` is isomorphic to `single₀ A`. -/
noncomputable def isoSingleOfConc (K : CochainComplex C ℤ) (A : C)
    (h0 : K.X 0 ≅ A) (hne : ∀ i : ℤ, i ≠ 0 → IsZero (K.X i)) :
    K ≅ single₀ A := by
  refine HomologicalComplex.Hom.isoOfComponents (fun i => ?_) ?_
  · by_cases hi : i = 0
    · subst hi
      exact h0.trans (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 A).symm
    · exact (hne i hi).iso (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 A i hi)
  · intro i j hij
    by_cases hi : i = 0
    · have hj : j ≠ 0 := by
        simp only [ComplexShape.up_Rel] at hij; omega
      apply (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 A j hj).eq_of_tgt
    · apply (hne i hi).eq_of_src

/-- **Definition 4 (Projective resolution of a complex).**
A projective resolution of a cochain complex `K^•`, bounded above by `a`, is a
cochain complex `P^•` together with a quasi-isomorphism `α : P^• → K^•` such that:
1. `P^•` is bounded above (`P^n = 0` for `n > a`), encoded by `IsStrictlyLE a`;
2. each `P^n` is a projective object;
3. `α` is a quasi-isomorphism.

The bound `a` is carried as a parameter so that the boundedness statements of
Statements 1 and 3 can be phrased precisely; for a "bounded above" resolution in
the sense of Definition 4 one simply asks for *some* `a` with this structure. -/
structure ProjectiveResolutionComplex (K : CochainComplex C ℤ) (a : ℤ) where
  /-- The complex `P^•` of projectives. -/
  complex : CochainComplex C ℤ
  /-- Each component `P^n` is a projective object. -/
  projective : ∀ n, Projective (complex.X n)
  /-- `P^•` is bounded above: `P^n = 0` for `n > a`. -/
  boundedAbove : complex.IsStrictlyLE a
  /-- The structure morphism `α : P^• → K^•`. -/
  α : complex ⟶ K
  /-- `α` is a quasi-isomorphism. -/
  quasiIso : QuasiIso α

-- ## Main Statement(s)

/-- **Statement 1.**
If `A` has enough projectives, then every object `A` of `A` has a projective
resolution in the sense of Definition 3: there is a complex `P^•` of projectives
with `P^n = 0` for `n > 0` and a quasi-isomorphism `P^• → A[0]`. Viewing the
resolution as a projective resolution (Definition 4) of the complex `A[0]` with
upper bound `0` captures exactly conditions (1)–(4) of Definition 3. -/
@[stacks 0646 "(1)",
  sga "2 VIII 1.4" "special case",
  sga "4½ Etat_0 3.1.9" "Part 1, special case",
  sga "4½ Etat_0 3.2.3" "partial"]
theorem statement1 [EnoughProjectives C] (A : C) :
    Nonempty (ProjectiveResolutionComplex (single₀ A) 0) := by
  let P := ProjectiveResolution.of A
  let E := P.complex.extend ComplexShape.embeddingDownNat
  have ext_zero : ∀ (L : ChainComplex C ℕ) (i : ℤ), 0 < i →
      IsZero ((L.extend ComplexShape.embeddingDownNat).X i) := by
    intro L i hi
    apply HomologicalComplex.isZero_extend_X
    intro k
    rw [show ComplexShape.embeddingDownNat.f k = -(k : ℤ) from rfl]; omega
  have ext_iso : ∀ (L : ChainComplex C ℕ) (i : ℤ), i ≤ 0 →
      Nonempty ((L.extend ComplexShape.embeddingDownNat).X i ≅ L.X i.natAbs) := by
    intro L i hi
    refine ⟨HomologicalComplex.extendXIso _ ComplexShape.embeddingDownNat (i := i.natAbs) ?_⟩
    rw [show ComplexShape.embeddingDownNat.f i.natAbs = -(i.natAbs : ℤ) from rfl]; omega
  have singleIso : (((ChainComplex.single₀ C).obj A).extend ComplexShape.embeddingDownNat)
      ≅ single₀ A := by
    apply isoSingleOfConc
    · exact (ext_iso _ 0 le_rfl).some
    · intro i hi
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · exact IsZero.of_iso (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 A
          i.natAbs (by omega)) (ext_iso _ i hlt.le).some
      · exact ext_zero _ i hgt
  let map : E ⟶ single₀ A :=
    HomologicalComplex.extendMap P.π ComplexShape.embeddingDownNat ≫ singleIso.hom
  refine ⟨{
    complex := E
    projective := ?_
    boundedAbove := ?_
    α := map
    quasiIso := ?_ }⟩
  · intro i
    by_cases hi : i ≤ 0
    · exact Projective.of_iso (ext_iso _ i hi).some.symm (P.projective i.natAbs)
    · exact (ext_zero _ i (not_le.mp hi)).projective
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => ext_zero _ i hi
  · have h1 : QuasiIso (HomologicalComplex.extendMap P.π ComplexShape.embeddingDownNat) :=
      inferInstance
    have h2 : QuasiIso singleIso.hom := inferInstance
    show QuasiIso (HomologicalComplex.extendMap P.π ComplexShape.embeddingDownNat ≫ singleIso.hom)
    infer_instance

/-! ## Decomposition of Statements 2 and 3 into sub-lemmas

The two open statements are reduced to named sub-lemmas below.

* `statement3` (core construction) is reduced to:
  - `lift_to_pullback` : the single-degree "term-by-term" lift engine — enough
    projectives lets us projectively cover a pullback;
  - `exists_epiResolution_of_strictlyLE` : the full descending-induction
    construction packaged as the existence of the resolution data.
  In fact `statement3` is *definitionally* `exists_epiResolution_of_strictlyLE`,
  so the real mathematical content lives in that lemma and in `lift_to_pullback`,
  which drives its inductive step.

* `statement2` (reduction) is reduced to:
  - `exists_strictlyLE_quasiIso` : a complex with cohomology vanishing in high
    degrees receives a quasi-isomorphism from a strictly-bounded-above complex
    (the canonical-truncation lemma, Stacks 13.19.2 / Tag 0645);
  - `statement3` applied to that bounded complex, composing the resolution with
    the truncation quasi-iso. -/

/-- **Term-by-term lift engine** (drives the inductive step of Statement 3).

In an abelian category with enough projectives, given `f : A ⟶ B` and an
epimorphism `g : E ⟶ B`, there is a projective object `Q` together with an
epimorphism `q : Q ⟶ A` and a map `r : Q ⟶ E` making the square commute
(`q ≫ f = r ≫ g`). Equivalently: project a chosen projective onto the pullback
`A ×_B E` (which surjects onto `A` because `g`, hence the pullback projection to
`A`, is an epimorphism), so `Q ↠ A ×_B E ↠ A`.

This is the dual of the term-by-term step used to build injective resolutions of
a complex (Stacks 13.18.3 / Tag 013K). At degree `n` of the resolution we apply
it with `f = d_K^n` precomposed appropriately and `g` the already-built map onto
the relevant cycles, obtaining the projective `P^n`, the component `α^n` (the epi
`q`, ensuring `α^n` is surjective) and the differential `d_P^n` (from `r`). -/
theorem lift_to_pullback [EnoughProjectives C] {A B E : C} (f : A ⟶ B) (g : E ⟶ B)
    [Epi g] :
    ∃ (Q : C) (_ : Projective Q) (q : Q ⟶ A) (r : Q ⟶ E),
      Epi q ∧ q ≫ f = r ≫ g := by
  -- PROOF SKETCH (one paragraph, directly closable in the formal phase):
  -- Form the pullback `A ×_B E` of `f` and `g` (`Limits.pullback f g` exists in
  -- an abelian category). Its projection `fst : A ×_B E ⟶ A` is an epimorphism
  -- because `g` is and epis are stable under pullback in an abelian category
  -- (`Limits.pullback.fst_of_mono`-style; here use that `g` epi ⇒ `pullback.fst`
  -- epi, lemma `CategoryTheory.Abelian.epi_pullback_of_epi` / pullback of an epi
  -- along any map is epi: `Limits.pullback.fst` epi instance under `Epi g`).
  -- Now take `Q := Projective.over (A ×_B E)` with `π := Projective.π (A ×_B E)`
  -- (epi, `Q` projective). Set `q := π ≫ pullback.fst` (epi ∘ epi = epi) and
  -- `r := π ≫ pullback.snd`. The pullback condition
  -- `pullback.fst ≫ f = pullback.snd ≫ g` (`Limits.pullback.condition`) gives,
  -- after composing with `π`, exactly `q ≫ f = r ≫ g`.
  -- Mathlib: `Limits.pullback`, `Limits.pullback.fst/snd/condition`,
  -- `Projective.over`, `Projective.π`, the `Epi` pullback-stability instance.
  -- The relevant epi-stability lemma is
  -- `CategoryTheory.Abelian.epi_pullback_of_epi_g :
  --    [Epi g] → Epi (pullback.fst f g)` (verified to exist).
  -- DIRECTLY CLOSABLE: `exact ⟨Projective.over (pullback f g), inferInstance,
  --   Projective.π _ ≫ pullback.fst f g, Projective.π _ ≫ pullback.snd f g,
  --   inferInstance, by rw [Category.assoc, Category.assoc, pullback.condition]⟩`
  --   (a complete proof along these lines was confirmed to compile during the
  --   sanity check).
  -- SANITY CHECK PASSED
  exact ⟨Projective.over (pullback f g), inferInstance,
    Projective.π _ ≫ pullback.fst f g, Projective.π _ ≫ pullback.snd f g,
    inferInstance, by rw [Category.assoc, Category.assoc, pullback.condition]⟩

/-- **Lift engine, epi-onto-pullback form** (Obligation 1 of the §6 plan).

The strengthened form of `lift_to_pullback`: instead of merely producing an epi
`q : Q ⟶ A` and a compatible `r : Q ⟶ E`, we produce a projective `Q` with an
epimorphism `π : Q ⟶ pullback f g` *onto the pullback object itself*. Composing
`π` with the pullback projections recovers `lift_to_pullback`, but the
"epi onto the pullback" shape is the genuinely needed workhorse for the
cocycle-surjectivity arguments (§2.1 and §4 of the informal proof), where one
pulls back this epi along a map into the pullback. -/
theorem lift_to_pullback' [EnoughProjectives C] {A B E : C} (f : A ⟶ B) (g : E ⟶ B)
    [Epi g] :
    ∃ (Q : C) (_ : Projective Q) (π : Q ⟶ pullback f g), Epi π := by
  have : Epi (pullback.fst f g) := inferInstance
  exact ⟨Projective.over (pullback f g), inferInstance, Projective.π _, inferInstance⟩

/-- Bundled resolution data for `K` bounded above by `a`: a ℤ-indexed family of projective
objects `P^n`, vanishing for `n > a`, with differentials `d n : P^n ⟶ P^{n+1}` and component
maps `α n : P^n ⟶ K^n` forming a chain map, together with the pointwise invariants needed to
assemble a `ProjectiveResolutionComplex`. -/
structure EpiResData (K : CochainComplex C ℤ) (a : ℤ) where
  /-- The objects `P^n`. -/
  X : ℤ → C
  /-- Each `P^n` is projective. -/
  proj : ∀ n, Projective (X n)
  /-- `P^n = 0` for `n > a` (boundedness). -/
  zero : ∀ n, a < n → IsZero (X n)
  /-- The differentials `d_P^n : P^n ⟶ P^{n+1}`. -/
  d : ∀ n, X n ⟶ X (n + 1)
  /-- `d ≫ d = 0`. -/
  dd : ∀ n, d n ≫ d (n + 1) = 0
  /-- The component maps `α^n : P^n ⟶ K^n`. -/
  α : ∀ n, X n ⟶ K.X n
  /-- Chain-map condition `α^n ≫ d_K^n = d_P^n ≫ α^{n+1}`. -/
  comm : ∀ n, α n ≫ K.d n (n + 1) = d n ≫ α (n + 1)
  /-- Each component `α^n` is an epimorphism. -/
  epiα : ∀ n, Epi (α n)
  -- ## Cocycle invariant (needed for the quasi-isomorphism).
  -- A degreewise-epi chain map is NOT a quasi-iso in general (counterexample: `K = 0`,
  -- `P` a non-acyclic complex of projectives). The recursion additionally maintains the
  -- "epi onto cocycles" + "pullback-surjectivity" invariant (C'), recorded here.
  /-- The cocycle object `Z_P^n = ker(d_P^n)`. -/
  ZP : ℤ → C
  /-- The inclusion of cocycles `Z_P^n ↪ P^n`. -/
  jZP : ∀ n, ZP n ⟶ X n
  /-- `jZP` is a monomorphism. -/
  hjZP : ∀ n, Mono (jZP n)
  /-- `jZP n ≫ d_P^n = 0` (cocycles are killed by `d`). -/
  hjd : ∀ n, jZP n ≫ d n = 0
  /-- Kernel universal property: `Z_P^n` IS the kernel of `d_P^n`. -/
  ker : ∀ n {T : C} (u : T ⟶ X n), u ≫ d n = 0 → ∃! v : T ⟶ ZP n, v ≫ jZP n = u
  /-- The induced cocycle map `β^n : Z_P^n ⟶ Z_K^n`. -/
  αZ : ∀ n, ZP n ⟶ K.cycles n
  /-- **(B)** `β^n` is an epimorphism (surjectivity onto cocycles). -/
  epiαZ : ∀ n, Epi (αZ n)
  /-- Compatibility `C(n)`: `β^n` is `α^n` restricted to cocycles. -/
  hαZ : ∀ n, jZP n ≫ α n = αZ n ≫ K.iCycles n
  /-- **(C')/Lemma 1' (the pullback-surjectivity invariant), as an epimorphism.**
  The map `P^n ⟶ Z_P^{n+1} ×_{Z_K^{n+1}} K^n` into the pullback of `β^{n+1}` and
  `d̄_K^n = K.toCycles n (n+1)`, whose first component is the corestriction
  `d̄_P^n` of `d_P^n` to cocycles (`d̄_P^n ≫ jZP (n+1) = d_P^n`) and whose second
  component is `α^n`, is an **epimorphism**. This is exactly what the
  projective-cover-of-pullback step supplies. Stored as: there is a map
  `dbarP n : X n ⟶ ZP (n+1)` with `dbarP n ≫ jZP (n+1) = d n` (corestriction),
  a commuting square `dbarP n ≫ αZ (n+1) = α n ≫ K.toCycles n (n+1)`, and the
  induced map into the pullback is epi. From this, the pseudoelement lift used in
  the monomorphism half of the homology comparison follows via
  `Pseudoelement.pseudo_surjective_of_epi`. -/
  dbarP : ∀ n, X n ⟶ ZP (n + 1)
  hdbarP : ∀ n, dbarP n ≫ jZP (n + 1) = d n
  hdbarP_sq : ∀ n, dbarP n ≫ αZ (n + 1) = α n ≫ K.toCycles n (n + 1)
  /-- The induced map `(d̄_P^n, α^n) : P^n ⟶ pullback (β^{n+1}) (d̄_K^n)` is epi. -/
  epiToPb : ∀ n, Epi (pullback.lift (dbarP n) (α n) (hdbarP_sq n) :
    X n ⟶ pullback (αZ (n + 1)) (K.toCycles n (n + 1)))

/- Auxiliary development for `exists_epiResData`: the descending recursion of
Stacks 0646(3), packaged as a per-degree state `St` together with the single
inductive `step` (driven by projective covers of pullbacks) and the assembly of
the resulting tower `tw` into the total ℤ-indexed family. -/
namespace ExistsEpiResDataAux

/-- The per-degree state of the descending recursion at cohomological degree `m`:
the projective object `P = P^m` with its component `α : P^m ⟶ K^m` (epi), the
differential `d : P^m ⟶ P^{m+1}` together with the *next* differential `dnext`
(so that `d ≫ dnext = 0`), and the cocycle data `(ZP, jZP, αZ)` recording that
`ZP = ker d^m` maps onto the cocycles `Z_K^m` via the epi `αZ` (`= β^m`). -/
structure St (K : CochainComplex C ℤ) (m : ℤ) where
  /-- The object `P^m`. -/
  P : C
  /-- `P^m` is projective. -/
  hP : Projective P
  /-- The object `P^{m+1}`. -/
  Pnext : C
  /-- The differential `d^m : P^m ⟶ P^{m+1}`. -/
  d : P ⟶ Pnext
  /-- The object `P^{m+2}`. -/
  NextNext : C
  /-- The differential `d^{m+1} : P^{m+1} ⟶ P^{m+2}`. -/
  dnext : Pnext ⟶ NextNext
  dd : d ≫ dnext = 0
  /-- The component `α^m : P^m ⟶ K^m`. -/
  α : P ⟶ K.X m
  /-- The component `α^{m+1} : P^{m+1} ⟶ K^{m+1}`. -/
  αnext : Pnext ⟶ K.X (m+1)
  comm : α ≫ K.d m (m+1) = d ≫ αnext
  /-- `α^m` is an epimorphism. -/
  epiα : Epi α
  /-- The cocycle object `Z_P^m = ker d^m`. -/
  ZP : C
  /-- The inclusion `Z_P^m ⟶ P^m`. -/
  jZP : ZP ⟶ P
  /-- The inclusion `Z_P^m ⟶ P^m` is a monomorphism. -/
  hjZP : Mono jZP
  hjd : jZP ≫ d = 0
  ker : ∀ {T : C} (u : T ⟶ P), u ≫ d = 0 → ∃! v : T ⟶ ZP, v ≫ jZP = u
  /-- The induced map on cocycles `β^m : Z_P^m ⟶ Z_K^m`. -/
  αZ : ZP ⟶ K.cycles m
  /-- `β^m` is an epimorphism. -/
  epiαZ : Epi αZ
  hαZ : jZP ≫ α = αZ ≫ K.iCycles m

/-- The corestriction `d̄_K^m : K^m ⟶ Z_K^{m+1}` of the differential to cocycles. -/
noncomputable def dbar (K : CochainComplex C ℤ) (m : ℤ) : K.X m ⟶ K.cycles (m+1) :=
  K.liftCycles (K.d m (m+1)) (m+1+1) (by simp) (by simp)

/-- `d̄_K^m` followed by the inclusion of cocycles is the differential `d_K^m`. -/
lemma dbar_i (K : CochainComplex C ℤ) (m : ℤ) :
    dbar K m ≫ K.iCycles (m+1) = K.d m (m+1) := K.liftCycles_i _ _ _ _

/-- The inclusion of cocycles `Z_K^m ⟶ K^m` followed by `d̄_K^m` is zero. -/
lemma iCycles_dbar (K : CochainComplex C ℤ) (m : ℤ) :
    K.iCycles m ≫ dbar K m = 0 := by
  rw [← cancel_mono (K.iCycles (m+1)), Category.assoc, dbar_i, zero_comp]
  exact K.iCycles_d m (m+1)

/-- If `K^m` is zero, then so is the cocycle object `Z_K^m`. -/
lemma cycles_isZero (K : CochainComplex C ℤ) (m : ℤ) (h : IsZero (K.X m)) :
    IsZero (K.cycles m) := by
  rw [IsZero.iff_id_eq_zero, ← cancel_mono (K.iCycles m)]
  apply h.eq_of_tgt

omit [Abelian C] in
/-- Every morphism into a zero object is an epimorphism. -/
lemma epi_of_isZero_tgt {Z W : C} (hW : IsZero W) (f : Z ⟶ W) : Epi f :=
  ⟨fun g h _ => hW.eq_of_src g h⟩

/-- The base (zero) state in degrees `m > a`, where `K^m = 0`. -/
noncomputable def zeroSt (K : CochainComplex C ℤ) (m : ℤ)
    (h1 : IsZero (K.X m)) : St K m where
  P := K.X m
  hP := h1.projective
  Pnext := K.X (m+1)
  d := K.d m (m+1)
  NextNext := K.X (m+1+1)
  dnext := K.d (m+1) (m+1+1)
  dd := K.d_comp_d m (m+1) (m+1+1)
  α := 𝟙 _
  αnext := 𝟙 _
  comm := by simp
  epiα := epi_of_isZero_tgt h1 _
  ZP := K.cycles m
  jZP := K.iCycles m
  hjZP := inferInstance
  hjd := K.iCycles_d m (m+1)
  ker := by
    intro T u hu
    refine ⟨K.liftCycles u (m+1) (by simp) hu, K.liftCycles_i _ _ _ _, ?_⟩
    intro y _; apply (cycles_isZero K m h1).eq_of_tgt
  αZ := 𝟙 _
  epiαZ := epi_of_isZero_tgt (cycles_isZero K m h1) _
  hαZ := by simp

variable [EnoughProjectives C]

/-- The inductive step: from the state at degree `m+1`, build the state at degree
`m` using a projective cover of the pullback `K^m ×_{Z_K^{m+1}} Z_P^{m+1}`.
The epimorphism of the induced cocycle map `αZ = β^m` is the hardest sub-fact
(§2.1 of the informal proof). -/
noncomputable def step (K : CochainComplex C ℤ) (m : ℤ) (S : St K (m + 1)) : St K m := by
  classical
  haveI := S.epiαZ
  haveI : Epi (pullback.fst (dbar K m) S.αZ) := inferInstance
  set Pb := pullback (dbar K m) S.αZ with hPb
  set Pm := Projective.over Pb with hPm
  set π : Pm ⟶ Pb := Projective.π Pb with hπ
  haveI : Epi π := inferInstance
  set d : Pm ⟶ S.P := (π ≫ pullback.snd _ _) ≫ S.jZP with hd_def
  set α : Pm ⟶ K.X m := π ≫ pullback.fst _ _ with hα_def
  have hpb : pullback.fst (dbar K m) S.αZ ≫ dbar K m
      = pullback.snd (dbar K m) S.αZ ≫ S.αZ := pullback.condition
  have hcomm : α ≫ K.d m (m+1) = d ≫ S.α := by
    have lhs : α ≫ K.d m (m+1) = π ≫ (pullback.fst _ _ ≫ dbar K m) ≫ K.iCycles (m+1) := by
      rw [hα_def, ← dbar_i K m]; simp only [Category.assoc]
    have rhs : d ≫ S.α = π ≫ (pullback.snd _ _ ≫ S.αZ) ≫ K.iCycles (m+1) := by
      rw [hd_def]; simp only [Category.assoc]; rw [S.hαZ]
    rw [lhs, rhs, hpb]
  have hker_cond : (kernel.ι d ≫ α) ≫ K.d m (m+1) = 0 := by
    rw [Category.assoc, hcomm, ← Category.assoc, kernel.condition, zero_comp]
  set αZnew : kernel d ⟶ K.cycles m :=
    K.liftCycles (kernel.ι d ≫ α) (m+1) (by simp) hker_cond with hαZnew
  have hαZnew_i : αZnew ≫ K.iCycles m = kernel.ι d ≫ α := K.liftCycles_i _ _ _ _
  have hepiαZnew : Epi αZnew := by
    have hcomp : K.iCycles m ≫ dbar K m = (0 : K.cycles m ⟶ S.ZP) ≫ S.αZ := by
      rw [iCycles_dbar, zero_comp]
    set γ : K.cycles m ⟶ Pb := pullback.lift (K.iCycles m) 0 hcomp with hγ
    have hγfst : γ ≫ pullback.fst _ _ = K.iCycles m := pullback.lift_fst _ _ _
    have hγsnd : γ ≫ pullback.snd _ _ = 0 := pullback.lift_snd _ _ _
    have : Epi (pullback.snd π γ) := Abelian.epi_pullback_of_epi_f π γ
    set t : pullback π γ ⟶ K.cycles m := pullback.snd π γ with ht
    set t' : pullback π γ ⟶ Pm := pullback.fst π γ with ht'
    have hsq : t' ≫ π = t ≫ γ := pullback.condition
    have ht'α : t' ≫ α = t ≫ K.iCycles m := by
      rw [hα_def, ← Category.assoc, hsq, Category.assoc, hγfst]
    have ht'snd : t' ≫ (π ≫ pullback.snd _ _) = 0 := by
      rw [← Category.assoc, hsq, Category.assoc, hγsnd, comp_zero]
    have ht'd : t' ≫ d = 0 := by
      rw [hd_def, ← Category.assoc, ht'snd, zero_comp]
    obtain ⟨v, hv⟩ := kernel.lift' d t' ht'd
    have key : (v ≫ αZnew) ≫ K.iCycles m = t ≫ K.iCycles m := by
      rw [Category.assoc, hαZnew_i, ← Category.assoc, hv, ht'α]
    have hvβ : v ≫ αZnew = t := (cancel_mono (K.iCycles m)).mp key
    have : Epi (v ≫ αZnew) := hvβ ▸ (inferInstance : Epi t)
    exact epi_of_epi v αZnew
  exact
    { P := Pm
      hP := hPm ▸ inferInstance
      Pnext := S.P
      d := d
      NextNext := S.Pnext
      dnext := S.d
      dd := by rw [hd_def, Category.assoc, S.hjd, comp_zero]
      α := α
      αnext := S.α
      comm := hcomm
      epiα := by rw [hα_def]; exact epi_comp _ _
      ZP := kernel d
      jZP := kernel.ι d
      hjZP := inferInstance
      hjd := kernel.condition d
      ker := by
        intro T u hu
        refine ⟨kernel.lift _ u hu, kernel.lift_ι _ _ _, ?_⟩
        intro y hy
        apply (cancel_mono (kernel.ι d)).mp
        rw [kernel.lift_ι]; exact hy
      αZ := αZnew
      epiαZ := hepiαZnew
      hαZ := (hαZnew_i).symm }

/-- The next object of `step K m S` is the object `P` of `S`. -/
lemma step_Pnext (K : CochainComplex C ℤ) (m : ℤ) (S : St K (m + 1)) :
    (step K m S).Pnext = S.P := rfl

/-- The next component of `step K m S` is the component `α` of `S`. -/
lemma step_αnext (K : CochainComplex C ℤ) (m : ℤ) (S : St K (m + 1)) :
    (step K m S).αnext = S.α := rfl

/-- The next differential of `step K m S` is the differential `d` of `S`. -/
lemma step_dnext (K : CochainComplex C ℤ) (m : ℤ) (S : St K (m + 1)) :
    HEq (step K m S).dnext S.d := HEq.rfl

variable (K : CochainComplex C ℤ) (a : ℤ) (hK : K.IsStrictlyLE a)

/-- The full tower: the per-degree state at every `m : ℤ`, by descending recursion
(`zeroSt` for `m > a`, `step` otherwise). -/
noncomputable def tw (m : ℤ) : St K m :=
  if hm : a < m then
    zeroSt K m ((CochainComplex.isStrictlyLE_iff K a).mp hK m hm)
  else
    step K m (tw (m+1))
termination_by (a + 1 - m).toNat
decreasing_by
  simp_wf
  omega

/-- For `m > a`, the tower in degree `m` is the zero state. -/
lemma tw_eq_zero (m : ℤ) (hm : a < m) :
    tw K a hK m = zeroSt K m ((CochainComplex.isStrictlyLE_iff K a).mp hK m hm) := by
  rw [tw]; simp [hm]

/-- For `m ≤ a`, the tower in degree `m` is `step` applied to the tower in degree `m + 1`. -/
lemma tw_eq_step (m : ℤ) (hm : ¬ a < m) :
    tw K a hK m = step K m (tw K a hK (m+1)) := by
  rw [tw]; simp [hm]

/-- For `m > a`, the object `P^m` of the tower is zero. -/
lemma tw_P_isZero (m : ℤ) (hm : a < m) : IsZero ((tw K a hK m).P) := by
  rw [tw_eq_zero K a hK m hm]
  exact (CochainComplex.isStrictlyLE_iff K a).mp hK m hm

/-- The next object of the tower in degree `m` is the object of the tower in degree `m + 1`. -/
lemma coh (m : ℤ) : (tw K a hK m).Pnext = (tw K a hK (m+1)).P := by
  by_cases hm : a < m
  · rw [tw_eq_zero K a hK m hm, tw_eq_zero K a hK (m+1) (by omega)]; rfl
  · rw [tw_eq_step K a hK m hm, step_Pnext]

/-- The next object of the tower in degree `m + 1` is the object `NextNext` of the tower in
degree `m`. -/
lemma cohNN (m : ℤ) : (tw K a hK (m+1)).Pnext = (tw K a hK m).NextNext := by
  by_cases hm : a < m
  · rw [tw_eq_zero K a hK m hm, tw_eq_zero K a hK (m+1) (by omega)]; rfl
  · rw [tw_eq_step K a hK m hm]; rfl

/-- The next component of the tower in degree `m` agrees, heterogeneously, with the component
of the tower in degree `m + 1`. -/
lemma cohα_heq (m : ℤ) : HEq (tw K a hK m).αnext (tw K a hK (m+1)).α := by
  by_cases hm : a < m
  · rw [tw_eq_zero K a hK m hm, tw_eq_zero K a hK (m+1) (by omega)]; exact HEq.rfl
  · rw [tw_eq_step K a hK m hm, step_αnext]; exact HEq.rfl

/-- The next differential of the tower in degree `m` agrees, heterogeneously, with the
differential of the tower in degree `m + 1`. -/
lemma cohd_heq (m : ℤ) : HEq (tw K a hK m).dnext (tw K a hK (m+1)).d := by
  by_cases hm : a < m
  · rw [tw_eq_zero K a hK m hm, tw_eq_zero K a hK (m+1) (by omega)]; exact HEq.rfl
  · rw [tw_eq_step K a hK m hm]; exact step_dnext ..

omit [Abelian C] [EnoughProjectives C] in
/-- Heterogeneously equal morphisms `f : A ⟶ B` and `g : A' ⟶ B'` satisfy
`f = eqToHom hA ≫ g ≫ eqToHom hB.symm`. -/
lemma heq_to_eqToHom {A B A' B' : C} (hA : A = A') (hB : B = B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : HEq f g) : f = eqToHom hA ≫ g ≫ eqToHom hB.symm := by
  subst hA; subst hB
  simp only [heq_eq_eq, eqToHom_refl, Category.comp_id, Category.id_comp] at h ⊢
  exact h

/-- The total ℤ-indexed family of objects extracted from the tower. -/
noncomputable def Xfun (n : ℤ) : C := (tw K a hK n).P
/-- The total ℤ-indexed family of differentials (with the codomain transported). -/
noncomputable def dfun (n : ℤ) : Xfun K a hK n ⟶ Xfun K a hK (n+1) :=
  (tw K a hK n).d ≫ eqToHom (coh K a hK n)
/-- The total ℤ-indexed family of components `α^n`. -/
noncomputable def αfun (n : ℤ) : Xfun K a hK n ⟶ K.X n := (tw K a hK n).α

/-- The next differential of the tower in degree `n` is the differential of the tower in
degree `n + 1`, transported along `coh` and `cohNN`. -/
lemma dnext_eq (n : ℤ) :
    (tw K a hK n).dnext
      = eqToHom (coh K a hK n) ≫ (tw K a hK (n+1)).d ≫ eqToHom (cohNN K a hK n) :=
  heq_to_eqToHom (coh K a hK n) (cohNN K a hK n).symm _ _ (cohd_heq K a hK n)

/-- Consecutive differentials of the total family compose to zero. -/
lemma dd_fun (n : ℤ) : dfun K a hK n ≫ dfun K a hK (n+1) = 0 := by
  have hdd := (tw K a hK n).dd
  rw [dnext_eq] at hdd
  rw [dfun, dfun]
  have key : (tw K a hK n).d ≫ eqToHom (coh K a hK n) ≫ (tw K a hK (n+1)).d = 0 := by
    have := hdd
    simp only [← Category.assoc] at this ⊢
    rw [← cancel_mono (eqToHom (cohNN K a hK n))]
    simpa using this
  calc ((tw K a hK n).d ≫ eqToHom (coh K a hK n)) ≫ (tw K a hK (n+1)).d ≫ eqToHom (coh K a hK (n+1))
      = ((tw K a hK n).d ≫ eqToHom (coh K a hK n) ≫ (tw K a hK (n+1)).d) ≫ eqToHom (coh K a hK
          (n+1)) := by
        simp only [Category.assoc]
    _ = 0 := by rw [key, zero_comp]

/-- The components `α^n` commute with the differentials: `α^n ≫ d_K^n = d_P^n ≫ α^{n+1}`. -/
lemma comm_fun (n : ℤ) :
    αfun K a hK n ≫ K.d n (n+1) = dfun K a hK n ≫ αfun K a hK (n+1) := by
  have hc := (tw K a hK n).comm
  have hα : (tw K a hK n).αnext = eqToHom (coh K a hK n) ≫ (tw K a hK (n+1)).α :=
    by simpa using heq_to_eqToHom (coh K a hK n) rfl _ _ (cohα_heq K a hK n)
  rw [hα] at hc
  rw [← Category.assoc] at hc
  simp only [αfun, dfun]
  exact hc

/-! ### Cocycle-invariant extractors (for the strengthened `EpiResData`) -/

/-- The total ℤ-indexed family of cocycle objects `Z_P^n = ker(d_P^n)`. -/
noncomputable def ZPfun (n : ℤ) : C := (tw K a hK n).ZP
/-- The cocycle inclusion `Z_P^n ↪ P^n`. -/
noncomputable def jZPfun (n : ℤ) : ZPfun K a hK n ⟶ Xfun K a hK n := (tw K a hK n).jZP
/-- The induced cocycle map `β^n : Z_P^n ⟶ Z_K^n`. -/
noncomputable def αZfun (n : ℤ) : ZPfun K a hK n ⟶ K.cycles n := (tw K a hK n).αZ

/-- The cocycle inclusion `Z_P^n ⟶ P^n` is a monomorphism. -/
lemma hjZP_fun (n : ℤ) : Mono (jZPfun K a hK n) := (tw K a hK n).hjZP

/-- The cocycle inclusion `Z_P^n ⟶ P^n` followed by `d_P^n` is zero. -/
lemma hjd_fun (n : ℤ) : jZPfun K a hK n ≫ dfun K a hK n = 0 := by
  rw [jZPfun, dfun]
  show (tw K a hK n).jZP ≫ ((tw K a hK n).d ≫ eqToHom (coh K a hK n)) = 0
  rw [← Category.assoc, (tw K a hK n).hjd, zero_comp]

-- Works around the isDefEq-transparency change: `simp`/`rw` on morphisms whose
-- (co)domains are only defeq to the unfolded `tw`/`dfun` objects now fail to match.
set_option backward.isDefEq.respectTransparency false in
/-- `Z_P^n` is a kernel of `d_P^n`: every `u : T ⟶ P^n` with `u ≫ d_P^n = 0` factors uniquely
through the cocycle inclusion. -/
lemma ker_fun (n : ℤ) {T : C} (u : T ⟶ Xfun K a hK n) (hu : u ≫ dfun K a hK n = 0) :
    ∃! v : T ⟶ ZPfun K a hK n, v ≫ jZPfun K a hK n = u := by
  have hu' : u ≫ (tw K a hK n).d = 0 := by
    rw [← cancel_mono (eqToHom (coh K a hK n))]
    simpa [dfun] using hu
  simpa [ZPfun, jZPfun] using (tw K a hK n).ker u hu'

/-- The cocycle map `β^n : Z_P^n ⟶ Z_K^n` is an epimorphism. -/
lemma epiαZ_fun (n : ℤ) : Epi (αZfun K a hK n) := (tw K a hK n).epiαZ

/-- The cocycle map `β^n` is compatible with `α^n` and the cocycle inclusions. -/
lemma hαZ_fun (n : ℤ) :
    jZPfun K a hK n ≫ αfun K a hK n = αZfun K a hK n ≫ K.iCycles n :=
  (tw K a hK n).hαZ

/-- The corestriction `d̄_P^n : P^n ⟶ Z_P^{n+1}` of `d_P^n` to cocycles. -/
noncomputable def dbarPfun (n : ℤ) : Xfun K a hK n ⟶ ZPfun K a hK (n + 1) :=
  (ker_fun K a hK (n + 1) (dfun K a hK n)
    (by rw [dd_fun])).choose

/-- `d̄_P^n` followed by the cocycle inclusion is `d_P^n`. -/
lemma hdbarP_fun (n : ℤ) :
    dbarPfun K a hK n ≫ jZPfun K a hK (n + 1) = dfun K a hK n :=
  (ker_fun K a hK (n + 1) (dfun K a hK n) (by rw [dd_fun])).choose_spec.1

/-- The commuting square `d̄_P^n ≫ β^{n+1} = α^n ≫ d̄_K^n`. Follows from `comm_fun`
(chain-map) and the compatibilities `hαZ_fun`, `dbar_i`, plus `cancel_mono iCycles`.
PROOF SKETCH: both sides composed with `K.iCycles (n+1)` agree:
  LHS ≫ iCycles = d̄_P^n ≫ β^{n+1} ≫ iCycles = d̄_P^n ≫ (jZP(n+1) ≫ α(n+1))  [hαZ_fun rev]
              = (d̄_P^n ≫ jZP(n+1)) ≫ α(n+1) = dfun n ≫ α(n+1)            [hdbarP_fun]
  RHS ≫ iCycles = α^n ≫ d̄_K^n ≫ iCycles = α^n ≫ K.d n (n+1)               [dbar_i / toCycles_i]
              = dfun n ≫ α(n+1)                                            [comm_fun]
Then cancel the mono `K.iCycles (n+1)`. NOTE `K.toCycles n (n+1) ≫ K.iCycles (n+1) = K.d n (n+1)`
is `K.toCycles_i` (or `dbar_i`). -/
lemma hdbarP_sq_fun (n : ℤ) :
    dbarPfun K a hK n ≫ αZfun K a hK (n + 1)
      = αfun K a hK n ≫ K.toCycles n (n + 1) := by
  rw [← cancel_mono (K.iCycles (n + 1))]
  rw [Category.assoc, Category.assoc]
  rw [HomologicalComplex.toCycles_i]
  rw [← hαZ_fun K a hK (n + 1)]
  rw [← Category.assoc, hdbarP_fun K a hK n]
  rw [comm_fun K a hK n]

set_option maxHeartbeats 1600000 in
-- this proof's elaboration needs more than the default heartbeat budget
set_option synthInstance.maxHeartbeats 800000 in
-- Works around the isDefEq-transparency change: `rw`/`rfl` steps on morphisms whose
-- (co)domains are only defeq to the unfolded objects now fail to match.
set_option backward.isDefEq.respectTransparency false in
/-- **The pullback-surjectivity epimorphism** (the genuinely new content, field (C')).
The induced map `(d̄_P^n, α^n) : P^n ⟶ pullback`
is epi. In the step regime this is essentially the epi `π : Projective.over Pb ↠ Pb`
combined with the identification of `(d̄_P^n, α^n)` with `π` (up to the kernel
corestriction). In the base regime `a < n` it is epi onto a zero/degenerate pullback.
PROOF SKETCH: case on `a < n` via `tw_eq_zero` / `tw_eq_step`. In the step case,
unfold `step` (degree `m = n`): there `α = π ≫ pullback.fst`, `d = (π ≫ pullback.snd) ≫ jZP`,
so `dbarP` corestricts to `π ≫ pullback.snd`, and `(dbarP, α)` into the pullback is
`π` followed by the canonical iso of pullbacks, hence epi since `π` is epi. -/
-- SANITY CHECK PASSED (TRUE, no counterexample): in the step regime `(d̄_P^n,α^n)`
-- equals `π ≫ (pullbackSymmetry _ _).hom` (π the projective-cover epi), hence epi;
-- in the base regime `a < n` both source `P^n` and the target pullback are zero,
-- so the map is epi by `epi_of_isZero_tgt`.
lemma epiToPb_fun (n : ℤ) :
    Epi (pullback.lift (dbarPfun K a hK n) (αfun K a hK n) (hdbarP_sq_fun K a hK n) :
      Xfun K a hK n ⟶ pullback (αZfun K a hK (n + 1)) (K.toCycles n (n + 1))) := by
  by_cases hn : a < n
  · -- BASE CASE: target pullback is zero.
    apply epi_of_isZero_tgt
    -- Show the pullback object is zero.
    have hKn : IsZero (K.X n) := (CochainComplex.isStrictlyLE_iff K a).mp hK n hn
    have hZP : IsZero (ZPfun K a hK (n + 1)) := by
      rw [ZPfun, tw_eq_zero K a hK (n+1) (by omega)]
      show IsZero (K.cycles (n+1))
      exact cycles_isZero K (n+1) ((CochainComplex.isStrictlyLE_iff K a).mp hK (n+1) (by omega))
    rw [IsZero.iff_id_eq_zero]
    apply pullback.hom_ext
    · rw [zero_comp]
      apply hZP.eq_of_tgt
    · rw [zero_comp]
      apply hKn.eq_of_tgt
  · -- STEP CASE
    set S := tw K a hK (n+1) with hS
    -- identify K.toCycles n (n+1) with dbar K n
    have hdbar_eq : K.toCycles n (n + 1) = dbar K n := by
      rw [← cancel_mono (K.iCycles (n+1)), HomologicalComplex.toCycles_i, dbar_i]
    -- the step regime gives tw n = step K n S
    have htw : tw K a hK n = step K n S := tw_eq_step K a hK n hn
    -- αZfun (n+1) = S.αZ definitionally
    have hαZ_eq : αZfun K a hK (n+1) = S.αZ := rfl
    -- domain identification
    have hdom : Xfun K a hK n = (step K n S).P := by rw [Xfun, htw]
    -- Pb is the step pullback; bind as a local to keep instance search away from `tw`
    set Pb : C := pullback (dbar K n) S.αZ with hPb
    have hdomPb : Xfun K a hK n = Projective.over Pb := hdom
    have hepiπ : Epi (Projective.π Pb) := Projective.π_epi Pb
    let e : Xfun K a hK n ⟶ Pb := eqToHom hdomPb ≫ Projective.π Pb
    have he : e = eqToHom hdomPb ≫ Projective.π Pb := rfl
    have : Epi e := by rw [he]; exact epi_comp _ _
    -- dfun n in step regime equals eqToHom ≫ (step).d
    have hd_heq : HEq (tw K a hK n).d (step K n S).d := by rw [htw]
    have hcod : (tw K a hK n).Pnext = (step K n S).Pnext := by rw [htw]
    have hdfun_step : dfun K a hK n = eqToHom hdomPb ≫ (step K n S).d := by
      have heq : (tw K a hK n).d
          = eqToHom hdomPb ≫ (step K n S).d ≫ eqToHom hcod.symm :=
        heq_to_eqToHom hdomPb hcod _ _ hd_heq
      rw [dfun, heq, Category.assoc, Category.assoc, eqToHom_trans]
      congr 1
      exact Category.comp_id _
    -- identify αfun n = e ≫ pullback.fst
    have hα_heq : HEq (tw K a hK n).α (step K n S).α := by rw [htw]
    have hαf : αfun K a hK n = e ≫ pullback.fst (dbar K n) S.αZ := by
      rw [αfun, he, Category.assoc]
      have heq : (tw K a hK n).α = eqToHom hdomPb ≫ (step K n S).α ≫ eqToHom (rfl : K.X n = K.X
          n).symm :=
        heq_to_eqToHom hdomPb rfl _ _ hα_heq
      rw [heq]
      simp only [eqToHom_refl, Category.comp_id]
      rfl
    -- dbarPfun n = e ≫ pullback.snd
    have hmono : Mono (jZPfun K a hK (n+1)) := hjZP_fun K a hK (n+1)
    have hjZPeq : jZPfun K a hK (n+1) = S.jZP := rfl
    have hdf : dbarPfun K a hK n = e ≫ pullback.snd (dbar K n) S.αZ := by
      have hstepd : (step K n S).d = (Projective.π Pb
        ≫ pullback.snd (dbar K n) S.αZ) ≫ S.jZP := rfl
      have hrhs : (e ≫ pullback.snd (dbar K n) S.αZ) ≫ jZPfun K a hK (n+1)
          = dfun K a hK n := by
        rw [hjZPeq, hdfun_step, hstepd, he]
        simp only [Category.assoc]
      exact (cancel_mono (jZPfun K a hK (n+1))).mp
        ((hdbarP_fun K a hK n).trans hrhs.symm)
    -- `(d̄_P^n, α^n)` is `e` followed by the swap isomorphism of the pullbacks
    have hLeq : pullback.lift (dbarPfun K a hK n) (αfun K a hK n) (hdbarP_sq_fun K a hK n)
        = e ≫ (pullbackSymmetry (dbar K n) S.αZ).hom ≫
          (pullback.congrHom hαZ_eq.symm hdbar_eq.symm).hom := by
      apply pullback.hom_ext
      · simpa using hdf
      · simpa using hαf
    rw [hLeq]
    infer_instance

end ExistsEpiResDataAux

end ProjectiveResolutionLemma

end

end
