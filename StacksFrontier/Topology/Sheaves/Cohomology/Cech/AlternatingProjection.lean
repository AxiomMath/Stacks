module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Fin.Parity
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.GroupTheory.Perm.Fin
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-
# Problem Description

Stacks Project, Tags 01FJ / 01FK (ordered vs. alternating Cech complexes).

Let `X` be a topological space, `F` an abelian presheaf on `X` (a contravariant functor
from the opens of `X` to abelian groups, with restriction maps depending only on the
inclusion of opens), and `U : I -> Opens X` an open covering indexed by a *totally
ordered* set `I`.  For a tuple `(i_0, ..., i_p)` one writes
`U_{i_0 ... i_p} = U_{i_0} cap ... cap U_{i_p}` for the (p+1)-fold intersection.

The Cech complex is `C^p(U, F) = prod_{(i_0,...,i_p)} F(U_{i_0...i_p})` with differential
  `d(s)_{i_0...i_{p+1}} = sum_{j=0}^{p+1} (-1)^j s_{i_0...^i_j...i_{p+1}}|_{U_{i_0...i_{p+1}}}.
  (*)`
The alternating subcomplex `C^p_alt` consists of cochains vanishing on tuples with a
repeated index and antisymmetric under transposing two entries.  The ordered complex
`C^p_ord = prod_{i_0<...<i_p} F(U_{i_0...i_p})` is indexed by strictly increasing tuples,
with the same differential `(*)`.

There is a comparison map `c : C^.._ord -> C^..`, `c(s)_{i_0...i_p} = 0` if some index
repeats, and `= sgn(sigma) s_{i_{sigma(0)}...i_{sigma(p)}}` where `sigma` sorts the indices
into increasing order; it is an isomorphism onto `C^.._alt` (Tag 01FJ).  The projection
`pi : C^.. -> C^.._ord`, `pi(s)_{i_0...i_p} = s_{i_0...i_p}` for `i_0 < ... < i_p`, forgets
all but the strictly increasing components.

## Main Statement(s) (Tag 01FK)

1. `pi : C^.. -> C^.._ord` is a morphism of complexes: `pi . d = d . pi`.
2. The restriction `pi : C^.._alt -> C^.._ord` is an isomorphism of complexes.
3. This isomorphism is a left inverse to `c`: `pi . c = id` on `C^.._ord`.

## Modelling choice

The data is modelled by an *actual* abelian presheaf on the opens of a topological space
`X`: for each open `V` an abelian group `F.obj V`, and for each inclusion `U <= V` a
restriction homomorphism `F.res : F.obj V ->+ F.obj U`, depending only on the inclusion
(presheaf functoriality `res_id`, `res_comp`).  The index family is `U : I -> Opens X`,
and the group attached to a tuple `t : Fin n -> I` is `F.obj (tupleOpen U t)` where
`tupleOpen U t = inf_k U (t k)` is the genuine open intersection.  Because restriction
maps depend only on inclusions of opens, two reindexings of a tuple inducing the same
intersection induce the *same* restriction map; in particular repeated-index identities
hold faithfully (this is the key correctness requirement for the Cech identities).
-/

open TopologicalSpace

-- Main Definition(s)

/-- An abelian presheaf on `X`: a contravariant functor from the opens of `X` to abelian
groups.  The restriction map `res h : F.obj V ->+ F.obj U` for an inclusion `h : U <= V`
depends only on the inclusion of opens (presheaf functoriality `res_id` / `res_comp`),
so equal open subsets receive equal groups and equal restriction maps. -/
@[sga "3 I 2.1.1" "special case"]
structure AbelianPresheaf (X : Type*) [TopologicalSpace X] where
  /-- The group of sections `F(U)` over an open `U`. -/
  obj : Opens X → Type*
  /-- The abelian group structure on `F(U)`. -/
  group : ∀ U, AddCommGroup (obj U)
  /-- The restriction homomorphism `F(V) →+ F(U)` along an inclusion `U ≤ V`. -/
  res : ∀ {U V : Opens X}, U ≤ V → (obj V →+ obj U)
  res_id : ∀ (U : Opens X), res (le_refl U) = AddMonoidHom.id (obj U)
  res_comp : ∀ {U V W : Opens X} (hUV : U ≤ V) (hVW : V ≤ W),
      (res hUV).comp (res hVW) = res (hUV.trans hVW)

attribute [instance] AbelianPresheaf.group

variable {X : Type*} [TopologicalSpace X] {I : Type*} [LinearOrder I]

/-- The open intersection `U_{t 0} cap ... cap U_{t (n-1)}` attached to a tuple `t`. -/
@[sga "4½ Arcata 6.1"]
def tupleOpen (U : I → Opens X) {n : ℕ} (t : Fin n → I) : Opens X := ⨅ k, U (t k)

omit [LinearOrder I] in
/-- A reindexing `φ` shrinks the intersection: `U_t <= U_{t∘φ}`.  (The image set of `t∘φ`
is contained in that of `t`, so its intersection is larger.)  Because the restriction map
only depends on this inclusion, it is independent of the particular `φ`. -/
theorem tupleOpen_le (U : I → Opens X) {m n : ℕ} (t : Fin n → I) (φ : Fin m → Fin n) :
    tupleOpen U t ≤ tupleOpen U (t ∘ φ) :=
  le_iInf fun k => iInf_le (fun j => U (t j)) (φ k)

/-- Restriction along a reindexing `φ : Fin m → Fin n`, from the group attached to the
coarser tuple `t ∘ φ` to the group attached to `t`.  Since `F.res` depends only on the
inclusion of opens, two reindexings producing the same pair of intersections give the
*same* map; this is precisely what makes the repeated-index Cech identities valid. -/
def AbelianPresheaf.tres (F : AbelianPresheaf X) (U : I → Opens X) {m n : ℕ}
    (φ : Fin m → Fin n) (t : Fin n → I) :
    F.obj (tupleOpen U (t ∘ φ)) →+ F.obj (tupleOpen U t) :=
  F.res (tupleOpen_le U t φ)

omit [LinearOrder I] in
/-- Restriction maps depend only on the inclusion of opens (which is a `Prop`), so any two
restriction maps between the same opens coincide. -/
theorem AbelianPresheaf.res_irrel (F : AbelianPresheaf X) {U V : Opens X} (h₁ h₂ : U ≤ V) :
    F.res h₁ = F.res h₂ :=
  rfl

omit [LinearOrder I] in
/-- Composition of restrictions: `res (along U≤V) ∘ res (along V≤W) = res (along U≤W)`,
applied pointwise. -/
theorem AbelianPresheaf.res_res (F : AbelianPresheaf X) {U V W : Opens X}
    (hUV : U ≤ V) (hVW : V ≤ W) (x : F.obj W) :
    F.res hUV (F.res hVW x) = F.res (hUV.trans hVW) x := by
  rw [← AddMonoidHom.comp_apply, F.res_comp]

omit [LinearOrder I] in
/-- Composition of two reindexing restrictions equals the single reindexing restriction
for the composite, applied pointwise. -/
theorem AbelianPresheaf.tres_tres (F : AbelianPresheaf X) (U : I → Opens X) {l m n : ℕ}
    (φ : Fin m → Fin n) (ψ : Fin l → Fin m) (t : Fin n → I)
    (x : F.obj (tupleOpen U (t ∘ φ ∘ ψ))) :
    F.tres U φ t (F.tres U ψ (t ∘ φ) x) = F.tres U (φ ∘ ψ) t x := by
  unfold AbelianPresheaf.tres
  rw [F.res_res]
  rfl


omit [LinearOrder I] in
/-- If two reindexings `φ, ψ` of the tuple `t` induce the *same* sub-tuple `t ∘ φ = t ∘ ψ`
(hence the same intersection open), the corresponding restriction maps agree, after
transporting the source element along the equality of opens. -/
theorem AbelianPresheaf.tres_congr (F : AbelianPresheaf X) (U : I → Opens X) {m n : ℕ}
    (φ ψ : Fin m → Fin n) (t : Fin n → I) (h : t ∘ φ = t ∘ ψ)
    (x : F.obj (tupleOpen U (t ∘ φ))) (y : F.obj (tupleOpen U (t ∘ ψ)))
    (hxy : HEq x y) :
    F.tres U φ t x = F.tres U ψ t y := by
  -- The source opens are equal; transport along that equality.
  unfold AbelianPresheaf.tres
  have ho : tupleOpen U (t ∘ φ) = tupleOpen U (t ∘ ψ) := congrArg (tupleOpen U) h
  have key : ∀ (V : Opens X) (hV : tupleOpen U (t ∘ φ) = V)
      (hle : tupleOpen U t ≤ V) (z : F.obj V),
      HEq x z → F.res (tupleOpen_le U t φ) x = F.res hle z := by
    intro V hV
    subst hV
    intro hle z hxz
    obtain rfl : x = z := eq_of_heq hxz
    congr 1
  exact key (tupleOpen U (t ∘ ψ)) ho (tupleOpen_le U t ψ) y hxy

/-- **Definition 1.** The Cech `p`-cochains:
`C^p(U, F) = prod_{(i_0,...,i_p)} F(U_{i_0...i_p})`. -/
@[sga "4 V 2.4.3" "partial"]
abbrev CechCochain (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ) : Type _ :=
  ∀ t : Fin (p+1) → I, F.obj (tupleOpen U t)

/-- The Cech `p`-cochains form an abelian group under componentwise addition. -/
instance (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ) :
    AddCommGroup (CechCochain F U p) := by unfold CechCochain; infer_instance

/-- Strictly increasing `(p+1)`-tuples of indices `i_0 < ... < i_p`. -/
abbrev OrdTuple (I : Type*) [LinearOrder I] (p : ℕ) : Type _ :=
  {t : Fin (p+1) → I // StrictMono t}

/-- The `j`-th face of a strictly increasing tuple, omitting the `j`-th index; it is again
strictly increasing. -/
abbrev OrdTuple.face {p : ℕ} (t : OrdTuple I (p + 1)) (j : Fin (p + 2)) : OrdTuple I p :=
  ⟨t.1 ∘ Fin.succAbove j, t.2.comp (Fin.strictMono_succAbove j)⟩

/-- **Definition 3.** The ordered Cech `p`-cochains:
`C^p_ord(U, F) = prod_{i_0<...<i_p} F(U_{i_0...i_p})`. -/
@[ega "III 6.6.4" "partial"]
abbrev CechCochainOrd (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ) : Type _ :=
  ∀ t : OrdTuple I p, F.obj (tupleOpen U t.1)

/-- The ordered Cech `p`-cochains form an abelian group under componentwise addition. -/
instance (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ) :
    AddCommGroup (CechCochainOrd F U p) := by unfold CechCochainOrd; infer_instance

/-- **Definition 1, differential.** The Cech differential `d : C^p → C^{p+1}`,
`d(s)_t = sum_j (-1)^j s_{t∘δ_j}|_t`, where `δ_j = Fin.succAbove j` omits the `j`-th
index. -/
@[sga "4 V 2.4.3" "Differential C^p(U"]
noncomputable def cechDiff (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ) :
    CechCochain F U p →+ CechCochain F U (p+1) where
  toFun s := fun t => ∑ j : Fin (p+2),
    (-1 : ℤ) ^ (j : ℕ) • F.tres U (Fin.succAbove j) t (s (t ∘ Fin.succAbove j))
  map_zero' := by funext t; simp
  map_add' s₁ s₂ := by funext t; simp [Finset.sum_add_distrib]

/-- **Definition 3, differential.** The ordered Cech differential
`d : C^p_ord → C^{p+1}_ord`, given by the same formula `(*)` (the faces of a strictly
increasing tuple are strictly increasing). -/
noncomputable def cechDiffOrd (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ) :
    CechCochainOrd F U p →+ CechCochainOrd F U (p+1) where
  toFun s := fun t => ∑ j : Fin (p+2),
    (-1 : ℤ) ^ (j : ℕ) • F.tres U (Fin.succAbove j) t.1 (s (t.face j))
  map_zero' := by funext t; simp
  map_add' s₁ s₂ := by funext t; simp [Finset.sum_add_distrib]

/-- **Definition 5.** The projection `π : C^• → C^•_ord`: forget all components except
those indexed by strictly increasing tuples. -/
def cechProj (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ) :
    CechCochain F U p →+ CechCochainOrd F U p where
  toFun s := fun t => s t.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- For an injective tuple, the sorting permutation `Tuple.sort t` makes `t ∘ sort t`
strictly monotone (its strictly increasing rearrangement). -/
theorem strictMono_comp_sort {n : ℕ} (t : Fin n → I) (h : Function.Injective t) :
    StrictMono (t ∘ Tuple.sort t) :=
  (Tuple.monotone_sort t).strictMono_of_injective (h.comp (Tuple.sort t).injective)

/-- **Definition 4.** The comparison map `c : C^•_ord → C^•`.  On a tuple `t`: `0` if `t`
repeats an index; otherwise `sgn(σ) • s_{sorted}`, where `σ = Tuple.sort t` sorts the
indices into strictly increasing order, the value of `s` at the sorted tuple `t ∘ σ`
being transported to `F.obj (tupleOpen U t)` along the restriction `F.tres U σ`. -/
noncomputable def cechComp (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ) :
    CechCochainOrd F U p →+ CechCochain F U p where
  toFun s := fun t =>
    if h : Function.Injective t then
      (Equiv.Perm.sign (Tuple.sort t) : ℤ) •
        F.tres U (Tuple.sort t) t (s ⟨t ∘ Tuple.sort t, strictMono_comp_sort t h⟩)
    else 0
  map_zero' := by funext t; by_cases h : Function.Injective t <;> simp [h]
  map_add' s₁ s₂ := by
    funext t
    by_cases h : Function.Injective t
    · simp only [Pi.add_apply, dite_eq_left h, map_add, smul_add]
    · simp only [Pi.add_apply, dite_eq_right h, add_zero]

/-- On an injective tuple, `c(s)_t` is the signed restriction of `s` at the sorted tuple. -/
theorem cechComp_apply_of_injective (F : AbelianPresheaf X) (U : I → Opens X) {p : ℕ}
    (s : CechCochainOrd F U p) {t : Fin (p + 1) → I} (h : Function.Injective t) :
    cechComp F U p s t = (Equiv.Perm.sign (Tuple.sort t) : ℤ) •
      F.tres U (Tuple.sort t) t (s ⟨t ∘ Tuple.sort t, strictMono_comp_sort t h⟩) :=
  dite_eq_left h

/-- On a tuple with a repeated index, `c(s)_t = 0`. -/
theorem cechComp_apply_of_not_injective (F : AbelianPresheaf X) (U : I → Opens X) {p : ℕ}
    (s : CechCochainOrd F U p) {t : Fin (p + 1) → I} (h : ¬ Function.Injective t) :
    cechComp F U p s t = 0 :=
  dite_eq_right h

/-- **Definition 2.** The alternating Cech cochains, as an additive subgroup of all
cochains: those `s` that vanish on tuples with a repeated index and that are antisymmetric,
i.e. for every permutation `σ` of the `p+1` indices, transporting the `(t∘σ)`-component
along the restriction `F.tres U σ` yields `sgn(σ)` times the `t`-component.  (Equivalently:
zero on tuples with a repeat, and transposing two entries negates the component.)  This
realizes `C^p_alt` as an honest subobject of `C^p`. -/
@[ega "0 12.1.2", ega "0 12.4.5" "Bidegree components"]
def CechCochainAlt (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ) :
    AddSubgroup (CechCochain F U p) where
  carrier := {s | (∀ t : Fin (p+1) → I, ¬ Function.Injective t → s t = 0) ∧
    (∀ (t : Fin (p+1) → I) (σ : Equiv.Perm (Fin (p+1))),
      F.tres U σ t (s (t ∘ σ)) = (Equiv.Perm.sign σ : ℤ) • s t)}
  zero_mem' := ⟨fun t _ => rfl, fun t σ => by simp⟩
  add_mem' {a b} ha hb := by
    refine ⟨fun t ht => by rw [Pi.add_apply, ha.1 t ht, hb.1 t ht, add_zero], fun t σ => ?_⟩
    change F.tres U σ t ((a + b) (t ∘ σ)) = _
    rw [Pi.add_apply, map_add, ha.2 t σ, hb.2 t σ, ← smul_add, ← Pi.add_apply]
  neg_mem' {a} ha := by
    refine ⟨fun t ht => by rw [Pi.neg_apply, ha.1 t ht, neg_zero], fun t σ => ?_⟩
    change F.tres U σ t ((-a) (t ∘ σ)) = _
    rw [Pi.neg_apply, map_neg, ha.2 t σ, ← smul_neg, ← Pi.neg_apply]

/-- The alternating Cech `p`-cochains form an abelian group, as a subgroup of all
cochains. -/
instance (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ) :
    AddCommGroup (CechCochainAlt F U p) := by infer_instance

/-- Sorting permutation of a reindexed tuple: `sort (t ∘ τ) = τ⁻¹ * sort t` for injective
`t`.  (Both rearrange `t` to the same strictly increasing tuple.) -/
theorem sort_comp_perm {n : ℕ} (t : Fin n → I) (τ : Equiv.Perm (Fin n))
    (h : Function.Injective t) :
    Tuple.sort (t ∘ τ) = τ⁻¹ * Tuple.sort t := by
  have key : (t ∘ ⇑τ) ∘ ⇑(Tuple.sort (t ∘ ⇑τ)) = t ∘ ⇑(Tuple.sort t) :=
    Tuple.comp_perm_comp_sort_eq_comp_sort
  have hperm : τ * Tuple.sort (t ∘ ⇑τ) = Tuple.sort t :=
    Equiv.coe_fn_injective (funext fun i => h (congrFun key i))
  rw [← hperm]
  group

/-- Sign of the sorting permutation of a reindexed tuple.  From
`sort (t ∘ τ) = τ⁻¹ * sort t` (`sort_comp_perm`) and multiplicativity of `sign`,
`sgn(sort(t∘τ)) = sgn(τ⁻¹)·sgn(sort t) = sgn(τ)·sgn(sort t)` (signs are ±1, so
`sgn(τ⁻¹) = sgn(τ)`). -/
theorem sign_sort_comp_perm {n : ℕ} (t : Fin n → I) (τ : Equiv.Perm (Fin n))
    (h : Function.Injective t) :
    (Equiv.Perm.sign (Tuple.sort (t ∘ ⇑τ)) : ℤ)
      = (Equiv.Perm.sign τ : ℤ) * (Equiv.Perm.sign (Tuple.sort t) : ℤ) := by
  rw [sort_comp_perm t τ h, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
  push_cast
  ring

/-- Antisymmetry of the comparison map on an injective tuple:
`F.tres U τ t (c(s)_{t∘τ}) = sgn(τ) • c(s)_t`. -/
theorem tres_cechComp_comp_perm (F : AbelianPresheaf X) (U : I → Opens X) {p : ℕ}
    (s : CechCochainOrd F U p) {t : Fin (p + 1) → I} (hinj : Function.Injective t)
    (τ : Equiv.Perm (Fin (p + 1))) :
    F.tres U τ t (cechComp F U p s (t ∘ τ)) = (Equiv.Perm.sign τ : ℤ) • cechComp F U p s t := by
  -- INFORMAL ARGUMENT (rigorous, gap-free):
  -- Goal: `F.tres U τ t (sgn₁ • F.tres U (sort(t∘τ)) (t∘τ) (s⟨(t∘τ)∘sort(t∘τ)⟩))`
  --       `= sgn(τ) • sgn₂ • F.tres U (sort t) t (s⟨t∘sort t⟩)`
  --   with sgn₁ = sgn(sort(t∘τ)), sgn₂ = sgn(sort t).
  -- (1) `F.tres U τ t` is an `AddMonoidHom`, so it commutes with the ℤ-scalar:
  --     `map_zsmul` pulls `sgn₁` to the front.
  -- (2) Compose the two restrictions: `F.tres U τ t (F.tres U (sort(t∘τ)) (t∘τ) x)`
  --     `= F.tres U (τ ∘ sort(t∘τ)) t x` by `tres_tres` (here φ=τ, ψ=sort(t∘τ),
  --     inner tuple t∘τ; the source open matches because (t∘τ)∘sort(t∘τ)=t∘(τ∘sort(t∘τ))).
  -- (3) `sort_comp_perm t τ hinj : sort(t∘τ) = τ⁻¹ * sort t`, so as plain functions
  --     `τ ∘ sort(t∘τ) = τ ∘ (τ⁻¹ ∘ sort t) = sort t`, and the sorted subtuple
  --     `(t∘τ)∘sort(t∘τ) = t∘(τ⁻¹*sort t reindexed) = t∘sort t`.  Hence
  --     `s⟨(t∘τ)∘sort(t∘τ)⟩` and `s⟨t∘sort t⟩` are `s` of the SAME OrdTuple value
  --     (equal first components ⇒ `Subtype.ext`), and `F.tres U (τ∘sort(t∘τ)) t`
  --     equals `F.tres U (sort t) t` by `tres_congr` (same reindexed tuple, HEq
  --     transport).  So LHS = `sgn₁ • F.tres U (sort t) t (s⟨t∘sort t⟩)`.
  -- (4) Sign reconciliation: `sgn₁ = sgn(sort(t∘τ)) = sgn(τ⁻¹ * sort t)`
  --     `= sgn(τ⁻¹) * sgn(sort t) = sgn(τ) * sgn(sort t) = sgn(τ) • sgn₂`
  --     (`Equiv.Perm.sign_mul`, `Equiv.Perm.sign_inv`).  This is exactly the RHS
  --     scalar, finishing the proof.
  -- DECOMPOSITION into named lemmas (proved below): `cechComp_tres_compose`
  -- packages steps (1)-(3); `sign_sort_comp_perm` packages step (4).
  have hinj' : Function.Injective (t ∘ τ) := hinj.comp τ.injective
  have hfun : ⇑τ ∘ ⇑(Tuple.sort (t ∘ ⇑τ)) = ⇑(Tuple.sort t) := by
    rw [sort_comp_perm t τ hinj]
    funext i
    simp only [Function.comp_apply, Equiv.Perm.coe_mul, Equiv.Perm.coe_inv,
      Equiv.apply_symm_apply]
  have htup : (t ∘ ⇑τ) ∘ ⇑(Tuple.sort (t ∘ ⇑τ)) = t ∘ ⇑(Tuple.sort t) := by
    rw [Function.comp_assoc, hfun]
  rw [cechComp_apply_of_injective F U s hinj', cechComp_apply_of_injective F U s hinj, map_zsmul,
    sign_sort_comp_perm t τ hinj, mul_smul, F.tres_tres]
  congr 2
  refine F.tres_congr U (⇑τ ∘ ⇑(Tuple.sort (t ∘ ⇑τ))) (⇑(Tuple.sort t)) t ?_ _ _ ?_
  · rw [← Function.comp_assoc, htup]
  · exact congr_arg_heq s (Subtype.ext htup)

/-- **Definition 4 (target).** The comparison map lands in the alternating subcomplex
(Statement 2, part a): `c(s)` is an alternating cochain for every ordered cochain `s`. -/
theorem isAlt_cechComp (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ)
    (s : CechCochainOrd F U p) : cechComp F U p s ∈ CechCochainAlt F U p := by
  refine ⟨fun t ht => cechComp_apply_of_not_injective F U s ht, fun t τ => ?_⟩
  by_cases hinj : Function.Injective t
  · exact tres_cechComp_comp_perm F U s hinj τ
  have hinj' : ¬ Function.Injective (t ∘ τ) := fun hc =>
    hinj (by simpa [Function.comp_assoc] using hc.comp τ⁻¹.injective)
  change F.tres U τ t (cechComp F U p s (t ∘ τ)) = (Equiv.Perm.sign τ : ℤ) • cechComp F U p s t
  rw [cechComp_apply_of_not_injective F U s hinj', cechComp_apply_of_not_injective F U s hinj,
    map_zero, smul_zero]

/-- The comparison map regarded as a map into the alternating subgroup. -/
noncomputable def cechCompAlt (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ) :
    CechCochainOrd F U p →+ CechCochainAlt F U p :=
  (cechComp F U p).codRestrict (CechCochainAlt F U p) (isAlt_cechComp F U p)

/-- **Definition 5 (restricted).** The projection restricted to the alternating
subcomplex, `π : C^•_alt → C^•_ord`. -/
def cechProjAlt (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ) :
    CechCochainAlt F U p →+ CechCochainOrd F U p :=
  (cechProj F U p).comp (CechCochainAlt F U p).subtype

-- Auxiliary facts that the complexes are genuine complexes / subcomplexes.

/-- The simplicial face-pairing `(k, j) ↦ (k.succAbove j, j.predAbove k)` cancels a signed double
sum over faces whose terms are invariant under the pairing; this is the core of `d ∘ d = 0`. -/
theorem sum_neg_one_pow_smul_eq_zero_of_succAbove_predAbove {M : Type*} [AddCommGroup M]
    {p : ℕ} (g : Fin (p + 3) → Fin (p + 2) → M)
    (hg : ∀ k j, g k j = g (k.succAbove j) (j.predAbove k)) :
    ∑ x : Fin (p+3) × Fin (p+2), ((-1 : ℤ) ^ (x.1 : ℕ) * (-1) ^ (x.2 : ℕ)) • g x.1 x.2 = 0 := by
  apply Finset.sum_involution
    (g := fun (x : Fin (p+3) × Fin (p+2)) _ => (Fin.succAbove x.1 x.2, Fin.predAbove x.2 x.1))
  · rintro ⟨k, j⟩ _
    simp only
    rw [hg k j, show ((-1 : ℤ) ^ (↑(k.succAbove j) : ℕ) * (-1 : ℤ) ^ (↑(j.predAbove k) : ℕ))
        = -((-1 : ℤ) ^ (↑k : ℕ) * (-1 : ℤ) ^ (↑j : ℕ)) by
      rw [← pow_add, ← pow_add, Fin.neg_one_pow_succAbove_add_predAbove], neg_smul,
      add_neg_cancel]
  · rintro ⟨k, j⟩ _ _
    simp only [ne_eq, Prod.mk.injEq, not_and]
    exact fun h => absurd h (Fin.succAbove_ne k j)
  · exact fun _ _ => Finset.mem_univ _
  · rintro ⟨k, j⟩ _
    simp only
    rw [Fin.succAbove_succAbove_predAbove, Fin.predAbove_predAbove_succAbove]

/-- The two double faces `δ_k ∘ δ_j` and `δ_{k.succAbove j} ∘ δ_{j.predAbove k}` of a tuple
agree. -/
theorem comp_succAbove_succAbove_predAbove {α : Type*} {p : ℕ} (t : Fin (p + 3) → α)
    (k : Fin (p + 3)) (j : Fin (p + 2)) :
    t ∘ (Fin.succAbove k ∘ Fin.succAbove j)
      = t ∘ (Fin.succAbove (k.succAbove j) ∘ Fin.succAbove (j.predAbove k)) :=
  congrArg (t ∘ ·) (funext fun i => (Fin.succAbove_succAbove_succAbove_predAbove k j i).symm)

/-- The double sum of iterated face restrictions of a family `c` of sections vanishes, provided
`c` is invariant (up to `HEq`) under the face pairing; this is the core of `d ∘ d = 0`. -/
private theorem sum_sum_tres_succAbove_eq_zero {J : Type*} (F : AbelianPresheaf X)
    (U : J → Opens X) {p : ℕ} (t : Fin (p + 3) → J)
    (c : ∀ (k : Fin (p + 3)) (j : Fin (p + 2)),
      F.obj (tupleOpen U ((t ∘ Fin.succAbove k) ∘ Fin.succAbove j)))
    (hc : ∀ k j, HEq (c k j) (c (k.succAbove j) (j.predAbove k))) :
    ∑ k : Fin (p+3), (-1 : ℤ) ^ (k : ℕ) • F.tres U (Fin.succAbove k) t
      (∑ j : Fin (p+2), (-1 : ℤ) ^ (j : ℕ) •
        F.tres U (Fin.succAbove j) (t ∘ Fin.succAbove k) (c k j)) = 0 := by
  have hinner : ∀ k : Fin (p+3), (-1 : ℤ) ^ (k : ℕ) • F.tres U (Fin.succAbove k) t
      (∑ j : Fin (p+2), (-1 : ℤ) ^ (j : ℕ) •
        F.tres U (Fin.succAbove j) (t ∘ Fin.succAbove k) (c k j))
      = ∑ j : Fin (p+2), ((-1 : ℤ) ^ (k : ℕ) * (-1 : ℤ) ^ (j : ℕ)) •
          F.tres U (Fin.succAbove k ∘ Fin.succAbove j) t (c k j) := by
    intro k
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_zsmul, smul_smul, F.tres_tres]
  rw [Finset.sum_congr rfl (fun k _ => hinner k), ← Fintype.sum_prod_type']
  refine sum_neg_one_pow_smul_eq_zero_of_succAbove_predAbove
    (fun k j => F.tres U (Fin.succAbove k ∘ Fin.succAbove j) t (c k j)) fun k j => ?_
  exact F.tres_congr U _ _ t (comp_succAbove_succAbove_predAbove t k j) _ _ (hc k j)

omit [LinearOrder I] in
/-- `d ∘ d = 0` for the full Cech complex, so `C^•(U, F)` is a complex. -/
theorem cechDiff_comp_cechDiff (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ) :
    (cechDiff F U (p+1)).comp (cechDiff F U p) = 0 := by
  ext s t
  exact sum_sum_tres_succAbove_eq_zero F U t
    (fun k j => s ((t ∘ Fin.succAbove k) ∘ Fin.succAbove j))
    fun k j => congr_arg_heq s (comp_succAbove_succAbove_predAbove t k j)

/-- `d ∘ d = 0` for the ordered Cech complex, so `C^•_ord(U, F)` is a complex. -/
theorem cechDiffOrd_comp_cechDiffOrd (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ) :
    (cechDiffOrd F U (p+1)).comp (cechDiffOrd F U p) = 0 := by
  ext s t
  exact sum_sum_tres_succAbove_eq_zero F U t.1 (fun k j => s ((t.face k).face j))
    fun k j => congr_arg_heq s (Subtype.ext (comp_succAbove_succAbove_predAbove t.1 k j))

/-- The key combinatorial fact: a permutation `σ` of `Fin (p+2)` commutes with the `j`-th
face up to an induced permutation `σ_j` of the remaining `p+1` coordinates.  For each `j`
there is a permutation `σ_j : Perm (Fin (p+1))` with
`Fin.succAbove (σ j) ∘ σ_j = σ ∘ Fin.succAbove j` (as functions `Fin (p+1) → Fin (p+2)`)
and `sgn σ_j = (-1)^(σ j) · sgn σ · (-1)^j`.  It is built by conjugating `σ` by the
cycle ranges of `j` and `σ j` (which carry the pivot to `0`), then restricting to the
nonzero subtype via `x ↦ x.succ`. -/
theorem succAbove_perm_aux {p : ℕ} (σ : Equiv.Perm (Fin (p + 2))) (j : Fin (p + 2)) :
    ∃ σj : Equiv.Perm (Fin (p+1)),
      (∀ x : Fin (p+1), Fin.succAbove (σ j) (σj x) = σ (Fin.succAbove j x)) ∧
      (Equiv.Perm.sign σj : ℤ)
        = (-1)^((σ j : Fin (p+2)) : ℕ) * (Equiv.Perm.sign σ : ℤ) * (-1)^((j : Fin (p+2)) : ℕ) := by
  set Φ : Equiv.Perm (Fin (p+2)) := (σ j).cycleRange * σ * (j.cycleRange)⁻¹ with hΦ
  have hΦ0 : Φ 0 = 0 := by
    have h1 : (j.cycleRange)⁻¹ 0 = j := by
      rw [← Fin.cycleRange_self j]
      simp
    simp only [hΦ, Equiv.Perm.coe_mul, Function.comp_apply, h1, Fin.cycleRange_self]
  have hΦne : ∀ y : Fin (p+2), (Φ y ≠ 0) ↔ (y ≠ 0) := fun y =>
    ⟨fun hy hy0 => hy (hy0 ▸ hΦ0), fun hy hy0 => hy (Φ.injective (hy0.trans hΦ0.symm))⟩
  set σj : Equiv.Perm (Fin (p+1)) :=
    (⟨ fun x => ⟨x.succ, Fin.succ_ne_zero x⟩, fun y => y.1.pred y.2,
      fun x => by simp, fun y => by ext; simp ⟩ :
        Fin (p+1) ≃ {y : Fin (p+2) // y ≠ 0}).permCongr.symm (Φ.subtypePerm hΦne) with hσj
  have hσjsucc : ∀ x : Fin (p+1), (σj x).succ = Φ (x.succ) := by
    intro x
    simp only [hσj, Equiv.permCongr_symm, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Equiv.Perm.subtypePerm_apply]
    rw [Fin.succ_pred]
  refine ⟨σj, ?_, ?_⟩
  · intro x
    have hsj : Fin.succAbove (σ j) (σj x) = (σ j).cycleRange.symm (σj x).succ := by
      rw [← Fin.cycleRange_succAbove (σ j) (σj x)]
      simp
    have hjx : Fin.succAbove j x = j.cycleRange.symm x.succ := by
      rw [← Fin.cycleRange_succAbove j x]
      simp
    rw [hsj, hσjsucc x, hΦ]
    simp only [Equiv.Perm.coe_mul, Function.comp_apply]
    rw [Equiv.symm_apply_apply, hjx]
    rfl
  · have e12 : Equiv.Perm.sign σj = Equiv.Perm.sign Φ := by
      rw [hσj, Equiv.permCongr_symm, Equiv.Perm.sign_permCongr]
      apply Equiv.Perm.sign_subtypePerm
      exact fun x hx h0 => hx (h0 ▸ hΦ0)
    have e3 : Equiv.Perm.sign Φ
        = Equiv.Perm.sign (σ j).cycleRange * Equiv.Perm.sign σ
          * Equiv.Perm.sign (j.cycleRange)⁻¹ := by
      rw [hΦ, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul]
    rw [e12, e3, Fin.sign_cycleRange, Equiv.Perm.sign_inv, Fin.sign_cycleRange]
    push_cast
    ring

/-- A power of `-1` multiplied by itself is `1`. -/
private theorem neg_one_pow_mul_neg_one_pow (n : ℕ) : (-1 : ℤ) ^ n * (-1) ^ n = 1 := by
  rw [← mul_pow]
  norm_num

omit [LinearOrder I] in
/-- If `t a = t b` for some `a < b`, then `(d s)_t = 0` for an alternating cochain `s`: the faces
away from `a, b` repeat an index, and the `a`-th and `b`-th faces cancel. -/
theorem cechDiff_apply_eq_zero_of_lt_of_eq (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ)
    (s : CechCochain F U p)
    (hzero : ∀ t : Fin (p+1) → I, ¬ Function.Injective t → s t = 0)
    (halt : ∀ (t : Fin (p+1) → I) (σ : Equiv.Perm (Fin (p+1))),
      F.tres U σ t (s (t ∘ σ)) = (Equiv.Perm.sign σ : ℤ) • s t)
    (t : Fin (p+2) → I) {a b : Fin (p+2)} (hlt : a < b) (hval : t a = t b) :
    cechDiff F U p s t = 0 := by
  have hab : a ≠ b := hlt.ne
  change (∑ j : Fin (p+2),
      (-1 : ℤ) ^ (j : ℕ) • F.tres U (Fin.succAbove j) t (s (t ∘ Fin.succAbove j))) = 0
  have hvanish : ∀ j ∈ (Finset.univ : Finset (Fin (p+2))), j ∉ ({a, b} : Finset (Fin (p+2))) →
      (-1 : ℤ) ^ (j : ℕ) • F.tres U (Fin.succAbove j) t (s (t ∘ Fin.succAbove j)) = 0 := by
    intro j _ hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    obtain ⟨ka, hka⟩ := Fin.exists_succAbove_eq (Ne.symm hj.1)
    obtain ⟨kb, hkb⟩ := Fin.exists_succAbove_eq (Ne.symm hj.2)
    have hni : ¬ Function.Injective (t ∘ Fin.succAbove j) := by
      rw [Function.not_injective_iff]
      exact ⟨ka, kb, by simp only [Function.comp_apply, hka, hkb, hval],
        fun h => hab (by rw [← hka, ← hkb, h])⟩
    rw [hzero _ hni, map_zero, smul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ ({a, b} : Finset (Fin (p+2)))) hvanish,
    Finset.sum_pair hab]
  obtain ⟨ρ, hρ, hsignρ⟩ := succAbove_perm_aux (Equiv.swap a b) b
  rw [Equiv.swap_apply_right] at hρ hsignρ
  have htswap : ∀ y : Fin (p+2), t (Equiv.swap a b y) = t y := by
    intro y
    rcases eq_or_ne y a with rfl | hya
    · rw [Equiv.swap_apply_left]
      exact hval.symm
    rcases eq_or_ne y b with rfl | hyb
    · rw [Equiv.swap_apply_right]
      exact hval
    rw [Equiv.swap_apply_of_ne_of_ne hya hyb]
  have hfun : (t ∘ Fin.succAbove a) ∘ ⇑ρ = t ∘ Fin.succAbove b := by
    funext x
    simp only [Function.comp_apply, hρ, htswap]
  have hH := congrArg (F.tres U (Fin.succAbove a) t) (halt (t ∘ Fin.succAbove a) ρ)
  rw [F.tres_tres, map_zsmul] at hH
  have hYb : F.tres U (Fin.succAbove b) t (s (t ∘ Fin.succAbove b))
      = (Equiv.Perm.sign ρ : ℤ) • F.tres U (Fin.succAbove a) t (s (t ∘ Fin.succAbove a)) := by
    rw [← hH]
    exact (F.tres_congr U (Fin.succAbove a ∘ ⇑ρ) (Fin.succAbove b) t hfun _ _
      (congr_arg_heq s hfun)).symm
  have hc : (-1 : ℤ) ^ (a : ℕ) + (-1) ^ (b : ℕ) * (Equiv.Perm.sign ρ : ℤ) = 0 := by
    rw [hsignρ, Equiv.Perm.sign_swap hab]
    push_cast
    rw [show (-1 : ℤ) ^ (b : ℕ) * ((-1) ^ (a : ℕ) * -1 * (-1) ^ (b : ℕ))
        = -((-1) ^ (a : ℕ) * ((-1) ^ (b : ℕ) * (-1) ^ (b : ℕ))) by ring,
      neg_one_pow_mul_neg_one_pow, mul_one,
      add_neg_cancel]
  rw [hYb, smul_smul, ← add_smul, hc, zero_smul]

omit [LinearOrder I] in
/-- Vanishing part of "alternating cochains form a subcomplex": if `t` is not injective
then `(d s)_t = 0`. -/
theorem cechDiff_apply_eq_zero_of_not_injective (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ)
    (s : CechCochain F U p)
    (hzero : ∀ t : Fin (p+1) → I, ¬ Function.Injective t → s t = 0)
    (halt : ∀ (t : Fin (p+1) → I) (σ : Equiv.Perm (Fin (p+1))),
      F.tres U σ t (s (t ∘ σ)) = (Equiv.Perm.sign σ : ℤ) • s t)
    (t : Fin (p+2) → I) (ht : ¬ Function.Injective t) :
    cechDiff F U p s t = 0 := by
  obtain ⟨a, b, hval, hne⟩ := Function.not_injective_iff.mp ht
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact cechDiff_apply_eq_zero_of_lt_of_eq F U p s hzero halt t hlt hval
  · exact cechDiff_apply_eq_zero_of_lt_of_eq F U p s hzero halt t hgt hval.symm

omit [LinearOrder I] in
/-- The `j`-th summand of `(d s)_{t∘σ}`, restricted along `σ`, is `sgn σ` times the
`σ j`-th summand of `(d s)_t`, for an antisymmetric cochain `s`. -/
theorem tres_cechDiff_summand_perm (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ)
    (s : CechCochain F U p)
    (halt : ∀ (t : Fin (p + 1) → I) (σ : Equiv.Perm (Fin (p + 1))),
      F.tres U σ t (s (t ∘ σ)) = (Equiv.Perm.sign σ : ℤ) • s t)
    (t : Fin (p + 2) → I) (σ : Equiv.Perm (Fin (p + 2))) (j : Fin (p + 2)) :
    F.tres U σ t ((-1 : ℤ) ^ (j : ℕ) •
        F.tres U (Fin.succAbove j) (t ∘ σ) (s ((t ∘ σ) ∘ Fin.succAbove j)))
      = (Equiv.Perm.sign σ : ℤ) • ((-1 : ℤ) ^ ((σ j : Fin (p + 2)) : ℕ) •
        F.tres U (Fin.succAbove (σ j)) t (s (t ∘ Fin.succAbove (σ j)))) := by
  obtain ⟨σj, hfun, hsign⟩ := succAbove_perm_aux σ j
  have harg : (t ∘ σ) ∘ Fin.succAbove j = (t ∘ Fin.succAbove (σ j)) ∘ σj := by
    funext x
    simp only [Function.comp_apply, hfun]
  rw [map_zsmul, F.tres_tres, F.tres_congr U (⇑σ ∘ Fin.succAbove j) (Fin.succAbove (σ j) ∘ ⇑σj)
    t harg (s ((t ∘ σ) ∘ Fin.succAbove j)) (s ((t ∘ Fin.succAbove (σ j)) ∘ ⇑σj))
    (congr_arg_heq s harg), ← F.tres_tres, halt (t ∘ Fin.succAbove (σ j)) σj,
    map_zsmul, smul_smul, hsign, smul_smul]
  congr 1
  rw [show (-1 : ℤ) ^ (j : ℕ) * ((-1) ^ ((σ j : Fin (p + 2)) : ℕ) * (Equiv.Perm.sign σ : ℤ) *
      (-1) ^ (j : ℕ)) = ((-1) ^ (j : ℕ) * (-1) ^ (j : ℕ)) *
      ((Equiv.Perm.sign σ : ℤ) * (-1) ^ ((σ j : Fin (p + 2)) : ℕ)) by ring,
    neg_one_pow_mul_neg_one_pow, one_mul]

omit [LinearOrder I] in
/-- Antisymmetry part of "alternating cochains form a subcomplex": for any tuple `t` and
permutation `σ`, `F.tres U σ t ((d s)_{t∘σ}) = sgn σ • (d s)_t`. -/
theorem cechDiff_apply_perm (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ)
    (s : CechCochain F U p)
    (halt : ∀ (t : Fin (p + 1) → I) (σ : Equiv.Perm (Fin (p + 1))),
      F.tres U σ t (s (t ∘ σ)) = (Equiv.Perm.sign σ : ℤ) • s t)
    (t : Fin (p + 2) → I) (σ : Equiv.Perm (Fin (p + 2))) :
    F.tres U σ t ((cechDiff F U p s) (t ∘ σ)) = (Equiv.Perm.sign σ : ℤ) • (cechDiff F U p s) t := by
  change F.tres U σ t (∑ j : Fin (p+2),
      (-1 : ℤ) ^ (j : ℕ) • F.tres U (Fin.succAbove j) (t ∘ σ) (s ((t ∘ σ) ∘ Fin.succAbove j)))
    = (Equiv.Perm.sign σ : ℤ) • ∑ j : Fin (p+2),
      (-1 : ℤ) ^ (j : ℕ) • F.tres U (Fin.succAbove j) t (s (t ∘ Fin.succAbove j))
  rw [map_sum, Finset.smul_sum]
  exact Fintype.sum_equiv σ _ _ fun j => tres_cechDiff_summand_perm F U p s halt t σ j

omit [LinearOrder I] in
/-- The differential preserves the alternating subcomplex: `d` maps alternating cochains
to alternating cochains, so `C^•_alt(U, F)` is a subcomplex of `C^•(U, F)`. -/
@[ega "0 12.1.2" "partial"]
theorem cechDiff_mem_alt (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ)
    (s : CechCochain F U p) (hs : s ∈ CechCochainAlt F U p) :
    cechDiff F U p s ∈ CechCochainAlt F U (p+1) :=
  -- INFORMAL ARGUMENT ("alternating cochains form a subcomplex").  Write `s ∈ alt` as
  -- `⟨hzero, halt⟩`: `hzero : ∀ t, ¬Injective t → s t = 0` and
  -- `halt : ∀ t σ, F.tres U σ t (s (t∘σ)) = sgn σ • s t`.  We must verify the two
  -- membership conditions for `d s` (recall `(d s)_t = Σ_j (-1)^j • F.tres U δ_j t (s (t∘δ_j))`,
  -- δ_j = succAbove j, t : Fin (p+2) → I).
  --
  -- (a) VANISHING: if `t` is not injective, pick `a ≠ b` with `t a = t b`; WLOG `a < b`.
  --     • For every `j ∉ {a, b}` the face `t∘δ_j` still contains both repeated entries
  --       (δ_j omits only index j), hence is non-injective, so `s (t∘δ_j) = 0` by `hzero`,
  --       killing that summand.
  --     • The two surviving summands `j = a` and `j = b` cancel: the faces `t∘δ_a` and
  --       `t∘δ_b` are the SAME tuple up to the order in which the (now single) duplicated
  --       value sits, i.e. `t∘δ_b = (t∘δ_a)∘ρ` for the cyclic/transposition reindexing ρ
  --       on `Fin (p+1)` with `sgn ρ = (-1)^(b-a-1)`.  Applying `halt` to that ρ and the
  --       `tres`/sign bookkeeping (`tres_tres`, `tres_congr`) shows the `j=a` and `j=b`
  --       terms are negatives of each other, because `(-1)^a · (-1)^(b-a-1) = -(-1)^b`.
  --       Hence the whole sum is 0.  This is `cechDiff_apply_eq_zero_of_not_injective`.
  --
  -- (b) ANTISYMMETRY: fix `t : Fin (p+2) → I` and `σ : Perm (Fin (p+2))`.  Need
  --     `F.tres U σ t ((d s)_{t∘σ}) = sgn σ • (d s)_t`.  Expand `(d s)_{t∘σ}` as a sum over
  --     `j`, push `F.tres U σ t` inside (additive + ℤ-linear) and compose restrictions by
  --     `tres_tres`.  The key combinatorial fact is that a permutation commutes with faces
  --     up to an induced permutation: for each `j` there is `j' = σ⁻¹-image position` and an
  --     induced permutation `σ_j : Perm (Fin (p+1))` with `σ ∘ δ_j = δ_{σ.(j)} ∘ σ_j` (the
  --     standard `Fin.succAbove` / `Equiv.Perm.decomposeFin`-style identity), satisfying
  --     `(-1)^j · sgn σ_j = sgn σ · (-1)^{σ.(j)}`.  Reindexing the sum over `j` by this
  --     bijection and applying `halt` to `σ_j` on each face turns
  --     `F.tres U σ t (s ((t∘σ)∘δ_j))` into `sgn σ • (-1)^{shift} • F.tres U δ_{σ.j} t (s
  -- (t∘δ_{σ.j}))`,
  --     reassembling to `sgn σ • (d s)_t`.  This is `cechDiff_apply_perm`.
  --
  -- DECOMPOSITION: the two conditions are isolated as the named sub-lemmas
  -- `cechDiff_apply_eq_zero_of_not_injective` (part a) and `cechDiff_apply_perm` (part b),
  -- each carrying its own open goal for the formal phase.  Here we only assemble them into the
  -- `CechCochainAlt` membership pair.
  ⟨cechDiff_apply_eq_zero_of_not_injective F U p s hs.1 hs.2, cechDiff_apply_perm F U p s hs.2⟩

/-- The differential on the alternating subcomplex `d : C^p_alt → C^{p+1}_alt`. -/
@[ega "0 12.1.2", ega "0 12.4.5" "partial"]
noncomputable def cechDiffAlt (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ) :
    CechCochainAlt F U p →+ CechCochainAlt F U (p+1) :=
  ((cechDiff F U p).comp (CechCochainAlt F U p).subtype).codRestrict
    (CechCochainAlt F U (p+1)) (fun s => cechDiff_mem_alt F U p s.1 s.2)

-- Main Statement(s) (Stacks Lemma 20.23.4, Tag 01FK)

/-- **Statement 1.** The projection `π : C^• → C^•_ord` is a morphism of complexes: each
`π` in degree `p` is a homomorphism of abelian groups (built into `cechProj`) and it
commutes with the differentials, `π ∘ d = d ∘ π`. -/
@[stacks 01FK "(1)"]
theorem cechProj_comp_cechDiff (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ) :
    (cechProj F U (p+1)).comp (cechDiff F U p)
      = (cechDiffOrd F U p).comp (cechProj F U p) := by
  ext s t
  rfl

/-- **Statement 3 (left inverse).** `π` is a left inverse to the comparison map `c`:
`π ∘ c = id` on the ordered complex.  (For a strictly increasing tuple the sorting
permutation is the identity, so `c(s)` agrees with `s` there.) -/
@[stacks 01FK "(3)"]
theorem cechProj_comp_cechComp (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ) :
    (cechProj F U p).comp (cechComp F U p) = AddMonoidHom.id (CechCochainOrd F U p) := by
  ext s t
  change cechComp F U p s t.1 = s t
  rw [cechComp_apply_of_injective F U s t.2.injective]
  -- Generalize over the sorting permutation and its strict-mono witness, then `subst`.
  have key : ∀ (σ : Equiv.Perm (Fin (p+1))), σ = Equiv.refl _ →
      ∀ (h : StrictMono (t.1 ∘ σ)),
      (Equiv.Perm.sign σ : ℤ) • F.tres U (⇑σ) t.1 (s ⟨t.1 ∘ σ, h⟩) = s t := by
    rintro σ rfl h
    rw [Equiv.Perm.sign_refl, Units.val_one, one_smul]
    have e1 : F.tres U (⇑(Equiv.refl (Fin (p+1))) : Fin (p+1) → Fin (p+1)) t.1
        = AddMonoidHom.id _ := by
      unfold AbelianPresheaf.tres
      exact F.res_id _
    rw [e1]
    rfl
  exact key _ (Tuple.sort_eq_refl_iff_monotone.2 t.2.monotone) _

/-- **Statement 2 (the inverse identity).** On the alternating subcomplex, `c ∘ π = id`:
an alternating cochain is determined by its strictly increasing components.  Combined with
Statement 3 (`π ∘ c = id`) this shows the restriction `π : C^•_alt → C^•_ord` is bijective
in each degree, with two-sided inverse `c`. -/
theorem cechComp_cechProj_of_isAlt (F : AbelianPresheaf X) (U : I → Opens X) {p : ℕ}
    (s : CechCochain F U p) (hs : s ∈ CechCochainAlt F U p) :
    cechComp F U p (cechProj F U p s) = s := by
  obtain ⟨hzero, halt⟩ := hs
  funext t
  by_cases hinj : Function.Injective t
  · rw [cechComp_apply_of_injective F U _ hinj]
    change (Equiv.Perm.sign (Tuple.sort t) : ℤ) •
        F.tres U (Tuple.sort t) t (s (t ∘ Tuple.sort t)) = s t
    rw [halt t (Tuple.sort t), smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one,
      one_smul]
  · rw [cechComp_apply_of_not_injective F U _ hinj, hzero t hinj]

/-- **Statement 2.** The restriction of the projection to the alternating subcomplex,
`π : C^•_alt → C^•_ord`, is an *isomorphism* of abelian groups in each degree, with inverse
the comparison map `c`.  (Together with Statement 2 below — that this isomorphism commutes
with the differentials — this is the asserted isomorphism of complexes.) -/
@[stacks 01FK "(2)"]
noncomputable def cechProjAltEquiv (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ) :
    CechCochainAlt F U p ≃+ CechCochainOrd F U p where
  toFun := cechProjAlt F U p
  invFun := cechCompAlt F U p
  left_inv s := Subtype.ext (cechComp_cechProj_of_isAlt F U s.1 s.2)
  right_inv := DFunLike.congr_fun (cechProj_comp_cechComp F U p)
  map_add' a b := by rw [map_add]

/-- **Statement 2 (isomorphism of complexes).** The isomorphism `π : C^•_alt → C^•_ord`
commutes with the differentials, hence is an isomorphism of complexes.  Equivalently, the
comparison map `c : C^•_ord → C^•_alt` is a morphism of complexes (`c ∘ d_ord = d_alt ∘ c`),
exhibiting `c` as the inverse morphism of complexes. -/
@[stacks 01FK "(2)"]
theorem cechProjAlt_comp_cechDiffAlt (F : AbelianPresheaf X) (U : I → Opens X) (p : ℕ) :
    (cechProjAlt F U (p+1)).comp (cechDiffAlt F U p)
      = (cechDiffOrd F U p).comp (cechProjAlt F U p) := by
  ext s t
  rfl
