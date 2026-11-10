module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Henselian local rings and the strict henselization

Throughout, all rings are commutative with unit. A *local ring* is a ring `R`
with a unique maximal ideal `m_R`; we write `κ_R = R / m_R` for its residue
field. For a polynomial `f ∈ R[T]` we write `f̄ ∈ κ_R[T]` for its reduction and
`f'` for its formal derivative.

* Definition 1 (Henselian local ring): a local ring `R` is *henselian* if for
  every monic `f ∈ R[T]` and every simple root `a₀ ∈ κ_R` of `f̄`
  (i.e. `f̄(a₀) = 0` and `f̄'(a₀) ≠ 0`) there is `a ∈ R` with `f(a) = 0` and
  `ā = a₀`.
* Definition 2 (Strictly henselian local ring): a henselian local ring whose
  residue field `κ_R` is separably algebraically closed.
* Definition 3 (Local homomorphism): a ring map `φ : R → S` of local rings with
  `φ(m_R) ⊆ m_S`.
* Definition 4 (Directed colimit along local homomorphisms): the colimit
  `R = colim_i R_i` of a directed system of local rings whose transition maps
  are local homomorphisms.

## Theorem (Stacks Tag 04GI)

Let `(I, ≤)` be a directed partially ordered set and let `(R_i, φ_{ii'})` be a
directed system of local rings in which every transition map is a local
homomorphism, with colimit `R = colim_i R_i`. Then:

1. (Locality.) `R` is a local ring, with `m_R = colim_i m_i`
   (`= ⋃_i φ_i(m_i)`), each structure map `φ_i` is local, and
   `κ_R = colim_i κ_i`.
2. (Henselian case.) If each `R_i` is henselian, then `R` is henselian.
3. (Strictly henselian case.) If each `R_i` is strictly henselian, then `R` is
   strictly henselian.

Succinctly: a filtered colimit of (strictly) henselian local rings along local
homomorphisms is (strictly) henselian.
-/

@[expose] public section

/-
## Notes on the formalization

* Mathlib's `HenselianLocalRing R` is exactly Definition 1 (it extends
  `IsLocalRing R`); `IsSepClosed κ` is "separably algebraically closed", so a
  *strictly henselian* local ring is `HenselianLocalRing R` together with
  `IsSepClosed (IsLocalRing.ResidueField R)`.
* A "directed system of local rings along local homomorphisms" is modelled by:
  a directed nonempty preorder `ι`, a family `G : ι → Type*` of local commutative
  rings, bundled ring homomorphisms `f i j h : G i →+* G j` for `i ≤ j` forming a
  `DirectedSystem`, and the hypothesis `hlocal` that each `f i j h` is a local
  homomorphism (`IsLocalHom`).
* The colimit is `Ring.DirectLimit`, which over a directed nonempty preorder is
  the filtered colimit of the rings; the structure maps are `Ring.DirectLimit.of`.
* Following the convention in the Stacks notes, we phrase the theorem over a
  directed poset, which is the standard setting; the general filtered version
  follows by cofinality (Stacks Tag 0032).
* `part1_isLocalRing` (locality of `R`) is needed even to *state* that `R` has a
  residue field; we therefore supply it via `letI` in the later statements.
-/

open IsLocalRing

-- Main Definition(s): the directed system of local rings along local homs.
variable {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
  (G : ι → Type*) [(i : ι) → CommRing (G i)] [(i : ι) → IsLocalRing (G i)]
  (f : (i j : ι) → i ≤ j → (G i →+* G j))
  [DirectedSystem G (fun i j h => (f i j h : G i → G j))]
  (hlocal : ∀ i j (h : i ≤ j), IsLocalHom (f i j h))

/-- The colimit ring `R = colim_i R_i`. -/
@[ega "0 1.4.5" "more general"]
noncomputable abbrev colimitRing : Type _ :=
  Ring.DirectLimit G (fun i j h => (f i j h : G i → G j))

/-- The structure map `φ_i : R_i → R` into the colimit. -/
@[ega "0 1.4.5" "more general", ega "0 10.3.1.3"]
noncomputable abbrev colimitOf (i : ι) : G i →+* colimitRing G f :=
  Ring.DirectLimit.of G (fun i j h => (f i j h : G i → G j)) i

/-- The induced transition maps on residue fields, `φ̄_{ij} : κ_i → κ_j`. -/
noncomputable def residueTransition (i j : ι) (h : i ≤ j) :
    ResidueField (G i) →+* ResidueField (G j) :=
  letI := hlocal i j h
  ResidueField.map (f i j h)

include hlocal

/-!
## Reusable colimit facts

The colimit `R = Ring.DirectLimit G (f …)` over a nonempty directed preorder is
the *filtered* colimit of the `G i`. We record the two structural facts that the
whole proof rests on, both supplied by Mathlib's `Ring.DirectLimit` API:

* every element of `R` is `colimitOf G f i x` for some index `i` and `x : G i`
  (`Ring.DirectLimit.exists_of`); and
* if `colimitOf G f i x = 0` then already `f i j h x = 0` at some later stage `j`
  (`Ring.DirectLimit.of.zero_exact`).

From the second fact we get the central lemma `colimit_isUnit_descend`: a unit of
`R` of the form `colimitOf G f i x` is already a unit at some finite stage. This
is what makes the colimit local (Stacks 04GI / 04GH).
-/

omit [∀ (i : ι), IsLocalRing (G i)] hlocal in
/-- **(Key descent lemma.)** If the image `φ_i(x)` of `x : G i` is a unit in the
colimit `R`, then `f i j h x` is a unit in `G j` for some `j ≥ i`.

*Argument.* `IsUnit (φ_i x)` gives some `w : R` with `φ_i x * w = 1`. By
`Ring.DirectLimit.exists_of`, `w = φ_j y` for some `j, y`. Choose `k ≥ i, j`
(directedness) and let `x' := f i k _ x`, `y' := f j k _ y`; by `of_f`,
`φ_k x' = φ_i x` and `φ_k y' = φ_j y`, so `φ_k (x' * y') = φ_i x * φ_j y = 1 =
φ_k 1`, whence `φ_k (x' * y' - 1) = 0`. `Ring.DirectLimit.of.zero_exact` yields
`l ≥ k` with `f k l _ (x' * y' - 1) = 0`, i.e. `f i l _ x * f j l _ y = 1` in
`G l` (transition maps are ring homs, `DirectedSystem.map_map` composes them).
Hence `f i l _ x` is a unit in `G l`, with witness `l ≥ i`. -/
theorem colimit_isUnit_descend (i : ι) (x : G i)
    (hu : IsUnit (colimitOf G f i x)) :
    ∃ (j : ι) (h : i ≤ j), IsUnit (f i j h x) := by
  obtain ⟨u, hu⟩ := hu
  set w : colimitRing G f := u.inv with hw
  have hxw : colimitOf G f i x * w = 1 := by
    rw [hw, ← hu]; exact u.val_inv
  obtain ⟨j, y, hjy⟩ := Ring.DirectLimit.exists_of w
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  -- representatives at stage `k`
  set x' : G k := f i k hik x with hx'
  set y' : G k := f j k hjk y with hy'
  -- `φ_k (x' * y') = 1`
  have hk1 : colimitOf G f k (x' * y') = 1 := by
    rw [map_mul, hx', hy', Ring.DirectLimit.of_f, Ring.DirectLimit.of_f, hjy, hxw]
  -- hence `φ_k (x' * y' - 1) = 0`
  have hk0 : colimitOf G f k (x' * y' - 1) = 0 := by
    rw [map_sub, hk1, map_one, sub_self]
  obtain ⟨l, hkl, hl⟩ := Ring.DirectLimit.of.zero_exact hk0
  refine ⟨l, le_trans hik hkl, ?_⟩
  -- `f k l _ (x' * y' - 1) = 0` means `f k l _ x' * f k l _ y' = 1`
  rw [map_sub, map_mul, map_one, sub_eq_zero] at hl
  -- compose transition maps
  have e1 : f k l hkl x' = f i l (le_trans hik hkl) x := by
    rw [hx']; exact DirectedSystem.map_map (f := fun i j h => (f i j h : G i → G j)) hik hkl x
  have e2 : f k l hkl y' = f j l (le_trans hjk hkl) y := by
    rw [hy']; exact DirectedSystem.map_map (f := fun i j h => (f i j h : G i → G j)) hjk hkl y
  have hprod : f i l (le_trans hik hkl) x * f j l (le_trans hjk hkl) y = 1 := by
    rw [← e1, ← e2, hl]
  exact IsUnit.of_mul_eq_one (f j l (le_trans hjk hkl) y) hprod

omit hlocal in
/-- **(Nontriviality of the colimit.)** `R = colim_i R_i` is nontrivial.

*Argument.* Fix any index `i` (`ι` is nonempty). If `(1 : R) = 0` then
`φ_i (1) = φ_i (0)`, i.e. `φ_i (1 - 0) = φ_i 1 = 0`; by
`Ring.DirectLimit.of.zero_exact` some `f i j h 1 = 0` in `G j`. But ring homs
preserve `1`, so `1 = 0` in `G j`, contradicting that the local ring `G j` is
nontrivial (`one_ne_zero`). -/
theorem colimit_nontrivial : Nontrivial (colimitRing G f) := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  refine ⟨0, 1, fun heq => ?_⟩
  have h1 : colimitOf G f i 1 = 0 := by
    rw [map_one, ← heq]
  obtain ⟨j, hij, hl⟩ := Ring.DirectLimit.of.zero_exact h1
  rw [map_one] at hl
  exact one_ne_zero hl

-- Main Statement(s)

/-- **Part 1 (Locality).** The colimit `R = colim_i R_i` of a directed system of
local rings along local homomorphisms is again a local ring.

*Argument.* Use `IsLocalRing.of_nonunits_add`: `R` is nontrivial
(`colimit_nontrivial`), and the nonunits of `R` are closed under addition. Let
`a, b` be nonunits of `R`. Write `a = φ_i x`, `b = φ_j y`
(`Ring.DirectLimit.exists_of`), push to a common `k ≥ i, j` so that
`a = φ_k x'`, `b = φ_k y'` with `x' = f i k _ x`, `y' = f j k _ y` (`of_f`). Then
`x'` and `y'` are nonunits of the *local* ring `G k`: if `x'` were a unit then
`a = φ_k x'` would be a unit of `R` (ring homs preserve units), contradiction;
likewise for `y'`. By locality of `G k`, the nonunits `m_k` of `G k` are closed
under addition, so `x' + y' ∈ m_k`, i.e. `x' + y'` is a nonunit of `G k`. Finally
`a + b = φ_k (x' + y')`; if `a + b` were a unit of `R`, then by
`colimit_isUnit_descend` some `f k l _ (x' + y')` would be a unit of `G l`, and
since `f k l _` is a *local* homomorphism (`hlocal`), pulling back the unit
(`IsUnit.of_map`) makes `x' + y'` a unit of `G k` — contradiction. Hence `a + b`
is a nonunit. -/
@[ega "0 10.3.1.3" "A' is a local ring",
  ega "IV 18.6.14" "Clause (i)",
  ega "IV 18.8.6" "partial",
  sga "3 V 4.1.2" "partial"]
theorem part1_isLocalRing : IsLocalRing (colimitRing G f) := by
  let := colimit_nontrivial G f
  apply IsLocalRing.of_nonunits_add
  intro a b ha hb
  -- descend `a, b` to a common stage `k`, show the representatives are nonunits
  -- of the local ring `G k`, conclude `x' + y'` is a nonunit there, and lift the
  -- nonunit back to `R` via `colimit_isUnit_descend` + locality of `f k l`.
  obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of a
  obtain ⟨j, y, rfl⟩ := Ring.DirectLimit.exists_of b
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  set x' : G k := f i k hik x with hx'
  set y' : G k := f j k hjk y with hy'
  -- the representatives equal `a` and `b` in the colimit
  have hax : colimitOf G f k x' = colimitOf G f i x := by
    rw [hx']; exact Ring.DirectLimit.of_f hik x
  have hby : colimitOf G f k y' = colimitOf G f j y := by
    rw [hy']; exact Ring.DirectLimit.of_f hjk y
  -- `x'` is a nonunit of `G k`
  have hx'nu : x' ∈ nonunits (G k) := by
    rw [mem_nonunits_iff]
    exact fun hux => (mem_nonunits_iff.mp ha) (hax ▸ hux.map (colimitOf G f k))
  have hy'nu : y' ∈ nonunits (G k) := by
    rw [mem_nonunits_iff]
    exact fun huy => (mem_nonunits_iff.mp hb) (hby ▸ huy.map (colimitOf G f k))
  -- nonunits of the local ring `G k` are closed under addition (via maximal ideal)
  have hsum : x' + y' ∈ nonunits (G k) := by
    rw [← IsLocalRing.mem_maximalIdeal] at hx'nu hy'nu ⊢
    exact Ideal.add_mem _ hx'nu hy'nu
  -- `a + b = colimitOf G f k (x' + y')`
  have hab : colimitOf G f i x + colimitOf G f j y = colimitOf G f k (x' + y') := by
    rw [map_add, hax, hby]
  -- conclude `a + b` is a nonunit
  rw [mem_nonunits_iff, hab]
  intro hu
  obtain ⟨l, hkl, hl⟩ := colimit_isUnit_descend G f k (x' + y') hu
  let := hlocal k l hkl
  exact (mem_nonunits_iff.mp hsum) (IsUnit.of_map (f k l hkl) (x' + y') hl)

-- `[∀ i, IsLocalRing (G i)]` is used only via instance synthesis in the proof (through
-- `part1_isLocalRing`); the section-var linter is a false positive here.
/-- **Part 1 (Local structure maps).** Each structure map `φ_i : R_i → R` is a
local homomorphism.

*Argument.* `IsLocalHom (φ_i)` means: if `φ_i x` is a unit of `R` then `x` is a
unit of `G i`. By `colimit_isUnit_descend`, `φ_i x` a unit gives `j ≥ i` with
`f i j h x` a unit of `G j`. Since `f i j h` is a *local* homomorphism
(`hlocal i j h`), `IsUnit.of_map` makes `x` a unit of `G i`. -/
@[ega "IV 18.8.6" "the structural map w"]
theorem part1_of_isLocalHom (i : ι) :
    letI := part1_isLocalRing G f hlocal
    IsLocalHom (colimitOf G f i) := by
  let := part1_isLocalRing G f hlocal
  refine ⟨fun x hx => ?_⟩
  -- `colimit_isUnit_descend` gives a stage `j` where `f i j h x` is a unit;
  -- `hlocal i j h` (a local hom) pulls the unit back to `x : G i`.
  obtain ⟨j, hij, hu⟩ := colimit_isUnit_descend G f i x hx
  let := hlocal i j hij
  exact IsUnit.of_map (f i j hij) x hu

/-- **Part 1 (Maximal ideal as a colimit).** An element of `R` lies in the
maximal ideal `m_R` iff it is the image of an element of some `m_i`; equivalently
`m_R = ⋃_i φ_i(m_i) = colim_i m_i`.

*Argument.* `z ∈ m_R ↔ z` is a nonunit of `R` (`IsLocalRing.mem_maximalIdeal` /
`mem_nonunits_iff`); likewise `x ∈ m_i ↔ x` is a nonunit of `G i`.

(⟹) `z` nonunit. Write `z = φ_i x` (`Ring.DirectLimit.exists_of`). Then `x` is a
nonunit of `G i`: otherwise `x` is a unit and `z = φ_i x` would be a unit of `R`.
So `i, x` witness the right side.

(⟸) Given `φ_i x = z` with `x ∈ m_i` (so `x` a nonunit of `G i`), suppose `z`
were a unit of `R`. By `part1_of_isLocalHom`, `φ_i` is a local homomorphism, so
`IsUnit.of_map` makes `x` a unit of `G i` — contradiction. Hence `z` is a nonunit,
i.e. `z ∈ m_R`. -/
@[ega "0 10.3.1.3" "m' = lim m_λ", ega "IV 5.13.3" "(i), special case", sga "3 V 4.1.2" "partial"]
theorem part1_mem_maximalIdeal (z : colimitRing G f) :
    letI := part1_isLocalRing G f hlocal
    z ∈ maximalIdeal (colimitRing G f) ↔
      ∃ (i : ι) (x : G i), colimitOf G f i x = z ∧ x ∈ maximalIdeal (G i) := by
  let := part1_isLocalRing G f hlocal
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  constructor
  · -- forward: a nonunit `z` is `φ_i x` with `x` a nonunit of `G i`
    intro hz
    obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of z
    refine ⟨i, x, rfl, ?_⟩
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact fun hux => hz (hux.map (colimitOf G f i))
  · -- backward: `φ_i (nonunit)` is a nonunit, since `φ_i` is local
    rintro ⟨i, x, rfl, hx⟩ hu
    obtain ⟨j, hij, hju⟩ := colimit_isUnit_descend G f i x hu
    let := hlocal i j hij
    exact hx (IsUnit.of_map (f i j hij) x hju)

/-- The residue-field transition maps `φ̄_{ij}` form a directed system. -/
private theorem residueTransition_directedSystem :
    DirectedSystem (fun i => ResidueField (G i))
      (fun i j h => (residueTransition G f hlocal i j h : ResidueField (G i) → ResidueField (G
          j))) := by
  have _ : Nonempty ι := inferInstance
  have _ : IsDirected ι (· ≤ ·) := inferInstance
  refine ⟨?_, ?_⟩
  · intro i x
    obtain ⟨y, rfl⟩ := residue_surjective x
    let := hlocal i i (le_refl i)
    change residueTransition G f hlocal i i (le_refl i) (residue (G i) y) = residue (G i) y
    rw [residueTransition, ResidueField.map_residue]
    congr 1
    exact DirectedSystem.map_self (f := fun i j h => (f i j h : G i → G j)) y
  · intro i j k hij hjk x
    obtain ⟨y, rfl⟩ := residue_surjective x
    let := hlocal k j hij
    let := hlocal j i hjk
    let := hlocal k i (le_trans hij hjk)
    change residueTransition G f hlocal j i hjk (residueTransition G f hlocal k j hij (residue (G
        k) y))
      = residueTransition G f hlocal k i (le_trans hij hjk) (residue (G k) y)
    rw [residueTransition, residueTransition, residueTransition,
      ResidueField.map_residue, ResidueField.map_residue, ResidueField.map_residue]
    congr 1
    exact DirectedSystem.map_map (f := fun i j h => (f i j h : G i → G j)) hij hjk y

/-- **Part 1 (Residue field as a colimit).** The residue field of `R` is the
colimit of the residue fields: `κ_R ≃ colim_i κ_i`, the colimit being taken along
the induced transition maps `φ̄_{ij}`.

*Argument.* Write `K := colim_i κ_i` for the right-hand `Ring.DirectLimit`. Each
structure map `φ_i : G i → R` is local (`part1_of_isLocalHom`), so it induces a
ring homomorphism on residue fields `ψ_i := ResidueField.map (φ_i) : κ_i → κ_R`.
These are compatible with the transition maps: for `i ≤ j`,
`ψ_j ∘ φ̄_{ij} = ψ_i`, because `φ_j ∘ f i j h = φ_i` (`Ring.DirectLimit.of_f`) and
`ResidueField.map` is functorial (`ResidueField.map_comp`). Hence by the
universal property `Ring.DirectLimit.lift` they assemble into a ring hom
`Φ : K → κ_R` with `Φ (of i u) = ψ_i u`.

`Φ` is bijective, so `Φ.symm`/`RingEquiv.ofBijective Φ` gives the desired
`κ_R ≃+* K` (we provide `(RingEquiv.ofBijective Φ hΦ).symm`):

* **Surjective.** Every element of `κ_R = R / m_R` is `residue R z` for some
  `z : R` (`IsLocalRing.residue_surjective`). Write `z = φ_i x`
  (`Ring.DirectLimit.exists_of`); then
  `residue R z = residue R (φ_i x) = ψ_i (residue (G i) x) = Φ (of i (residue x))`
  (using `ResidueField.map_residue`), so `residue R z` is in the range of `Φ`.

* **Injective.** `K` is nontrivial: it is a `Ring.DirectLimit` of the nontrivial
  fields `κ_i` along the injective field maps `φ̄_{ij}`, and `of i (1) ≠ 0` (the
  same `of.zero_exact` argument as `colimit_nontrivial`, using that `κ_i` is a
  field hence `1 ≠ 0`). A ring homomorphism out of a field (here `Φ : K → κ_R`
  with `K` a field — `Field.DirectLimit.field` makes the colimit of fields a
  field) into a nonzero ring is injective (`RingHom.injective`, valid since the
  domain `K` is a field / `DivisionRing`). -/
@[ega "0 10.3.1.3" "partial", sga "3 V 4.1.2" "partial"]
theorem part1_residueField_colimit :
    letI := part1_isLocalRing G f hlocal
    Nonempty (ResidueField (colimitRing G f) ≃+*
      Ring.DirectLimit (fun i => ResidueField (G i))
        (fun i j h =>
          (residueTransition G f hlocal i j h : ResidueField (G i) → ResidueField (G j)))) := by
  let := part1_isLocalRing G f hlocal
  let : ∀ i, IsLocalHom (colimitOf G f i) := part1_of_isLocalHom G f hlocal
  -- the maps ψ_i = ResidueField.map (colimitOf G f i)
  set ψ : (i : ι) → ResidueField (G i) →+* ResidueField (colimitRing G f) :=
    fun i => ResidueField.map (colimitOf G f i) with hψ
  -- compatibility
  have hcompat : ∀ (i j : ι) (hij : i ≤ j) (x : ResidueField (G i)),
      (ψ j) (residueTransition G f hlocal i j hij x) = (ψ i) x := by
    intro i j hij x
    let := hlocal i j hij
    obtain ⟨y, rfl⟩ := residue_surjective x
    change (ResidueField.map (colimitOf G f j)) (residueTransition G f hlocal i j hij (residue (G
        i) y))
      = (ResidueField.map (colimitOf G f i)) (residue (G i) y)
    rw [residueTransition, ResidueField.map_residue, ResidueField.map_residue,
      ResidueField.map_residue]
    congr 1
    exact Ring.DirectLimit.of_f hij y
  -- the lifted map Φ : K → κ_R
  set Φ : Ring.DirectLimit (fun i => ResidueField (G i))
      (fun i j h => (residueTransition G f hlocal i j h : ResidueField (G i) → ResidueField (G j)))
      →+* ResidueField (colimitRing G f) :=
    Ring.DirectLimit.lift (fun i => ResidueField (G i))
      (fun i j h => (residueTransition G f hlocal i j h : ResidueField (G i) → ResidueField (G j)))
      _ ψ hcompat with hΦ
  -- K is a field, hence the lift is injective
  have hds := residueTransition_directedSystem G f hlocal
  let : Field (Ring.DirectLimit (fun i => ResidueField (G i))
      (fun i j h => (residueTransition G f hlocal i j h : ResidueField (G i) → ResidueField (G
          j)))) :=
    Field.DirectLimit.field (fun i => ResidueField (G i)) (residueTransition G f hlocal)
  have hinj : Function.Injective Φ := Φ.injective
  -- surjectivity
  have hsurj : Function.Surjective Φ := by
    intro w
    obtain ⟨z, rfl⟩ := residue_surjective w
    obtain ⟨i, x, rfl⟩ := Ring.DirectLimit.exists_of z
    refine ⟨Ring.DirectLimit.of _ _ i (residue (G i) x), ?_⟩
    rw [hΦ, Ring.DirectLimit.lift_of]
    change ResidueField.map (colimitOf G f i) (residue (G i) x) = residue _ (colimitOf G f i x)
    rw [ResidueField.map_residue]
  exact ⟨(RingEquiv.ofBijective Φ ⟨hinj, hsurj⟩).symm⟩

-- this proof's elaboration needs more than the default heartbeat budget
open Polynomial in
/-- **Part 2 (Henselian case).** If each `R_i` is henselian, then the colimit `R`
is henselian.

*Argument (Stacks 04GI, the essential new content).* We verify the
`HenselianLocalRing.is_henselian` clause for `R` (locality is
`part1_isLocalRing`). Let `g : R[X]` be monic, `a₀ : R` with `g.eval a₀ ∈ m_R`
and `IsUnit (g.derivative.eval a₀)`; we must find `a : R` with `g.IsRoot a` and
`a - a₀ ∈ m_R`.

1. **Descend the data to a finite stage.** Since `R[X]` is the filtered colimit
   of the `G i[X]`, `Ring.DirectLimit.Polynomial.exists_of` gives an index and a
   polynomial mapping to `g`; arranging it to be *monic of the same degree*
   (possible after enlarging the index: the leading coefficient of any preimage
   maps to `1 = leadingCoeff g`, so `colimit_isUnit_descend`/`of.zero_exact`
   makes it `1` at a later stage, or one truncates to the correct degree and
   sets the top coefficient to `1`). Also descend `a₀ = φ_k b₀`
   (`Ring.DirectLimit.exists_of`). Push polynomial and point to a common index
   `k`, obtaining a monic `p : G k[X]` with `p.map (φ_k) = g` and `b₀ : G k`
   with `φ_k b₀ = a₀`.

2. **The hypotheses descend.** Evaluation commutes with `map`:
   `φ_k (p.eval b₀) = g.eval a₀` and `φ_k (p.derivative.eval b₀) =
   g.derivative.eval a₀` (`Polynomial.eval_map`, `Polynomial.derivative_map`).
   * `g.derivative.eval a₀` is a unit, so `φ_k (p.derivative.eval b₀)` is a unit;
     by `colimit_isUnit_descend` it becomes a unit `p'.eval ... ` at some `l ≥ k`;
     push `p, b₀` forward to `l` (so WLOG `k = l`) to get
     `IsUnit (p.derivative.eval b₀)` in `G k`.
   * `g.eval a₀ ∈ m_R` means `φ_k (p.eval b₀)` is a nonunit of `R`; if
     `p.eval b₀` were a unit of `G k`, its image `φ_k (p.eval b₀)` would be a
     unit of `R` — contradiction. So `p.eval b₀ ∈ m_k`.

3. **Apply henselianness of `G k`.** `hhens k` gives `c : G k` with
   `p.IsRoot c` (`p.eval c = 0`) and `c - b₀ ∈ m_k`.

4. **Push the root forward.** Set `a := φ_k c`. Then
   `g.eval a = (p.map φ_k).eval (φ_k c) = φ_k (p.eval c) = φ_k 0 = 0`
   (`Polynomial.eval_map` + `eval₂` is a ring hom), so `g.IsRoot a`. And
   `a - a₀ = φ_k c - φ_k b₀ = φ_k (c - b₀)`, which lies in `m_R` because
   `c - b₀ ∈ m_k` and `φ_k` is local (`part1_mem_maximalIdeal` ⟸, or
   `IsLocalRing.map_nonunit`). -/
@[stacks 04GI "henselian", ega "IV 18.6.14"]
theorem part2_henselian (hhens : ∀ i, HenselianLocalRing (G i)) :
    HenselianLocalRing (colimitRing G f) := by
  let := part1_isLocalRing G f hlocal
  refine { __ := part1_isLocalRing G f hlocal, is_henselian := ?_ }
  intro g hg a₀ hev hder
  classical
  obtain ⟨k₀, p₀, hp₀⟩ := Ring.DirectLimit.Polynomial.exists_of (f' := f) g
  set n := g.natDegree with hn
  set pm : (G k₀)[X] := (∑ i ∈ Finset.range n, (monomial i) (p₀.coeff i)) + (X : (G k₀)[X])^n with
      hpm
  have hpm_monic : pm.Monic := by
    rw [hpm, add_comm]
    apply monic_X_pow_add
    apply lt_of_le_of_lt (degree_sum_le _ _)
    apply (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).mpr
    intro i hi
    rw [Finset.mem_range] at hi
    calc (monomial i (p₀.coeff i)).degree ≤ (i : WithBot ℕ) := degree_monomial_le _ _
      _ < (n : WithBot ℕ) := by exact_mod_cast hi
  have hpm_map : map (colimitOf G f k₀) pm = g := by
    rw [hpm, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sum]
    have hcoeff : ∀ i, (colimitOf G f k₀) (p₀.coeff i) = g.coeff i := by
      intro i; rw [← coeff_map, hp₀]
    simp only [Polynomial.map_monomial, hcoeff]
    conv_rhs => rw [g.as_sum_range, ← hn, Finset.sum_range_succ]
    congr 1
    rw [X_pow_eq_monomial]
    congr 1
    have : g.coeff n = g.leadingCoeff := by rw [Polynomial.leadingCoeff, hn]
    rw [this, hg.leadingCoeff]
  obtain ⟨k₁, b₁, hb₁⟩ := Ring.DirectLimit.exists_of a₀
  obtain ⟨k, hk0, hk1⟩ := directed_of (· ≤ ·) k₀ k₁
  have hevalx : ∀ (m : ι) (q : (G m)[X]) (b : G m), colimitOf G f m b = a₀ →
      colimitOf G f m (q.eval b) = (q.map (colimitOf G f m)).eval a₀ := by
    intro m q b hb
    rw [eval_map, ← hb, eval₂_at_apply]
  -- pushing a polynomial forward along `f` does not change its image in the colimit
  have hpush : ∀ {m n : ι} (h : m ≤ n) (q : (G m)[X]),
      (q.map (f m n h)).map (colimitOf G f n) = q.map (colimitOf G f m) := fun h q => by
    rw [Polynomial.map_map]
    congr 1
    ext x
    exact Ring.DirectLimit.of_f h x
  set p : (G k)[X] := pm.map (f k₀ k hk0) with hp
  set b₀ : G k := f k₁ k hk1 b₁ with hb0
  have hp_monic : p.Monic := hpm_monic.map _
  have hp_map : map (colimitOf G f k) p = g := by rw [hp, hpush, hpm_map]
  have hb_map : colimitOf G f k b₀ = a₀ := by
    rw [hb0]; rw [Ring.DirectLimit.of_f hk1 b₁, hb₁]
  have hderc : IsUnit (colimitOf G f k ((derivative p).eval b₀)) := by
    rw [hevalx k _ b₀ hb_map, ← derivative_map, hp_map]
    exact hder
  obtain ⟨l, hkl, hul⟩ := colimit_isUnit_descend G f k ((derivative p).eval b₀) hderc
  set pl : (G l)[X] := p.map (f k l hkl) with hpl
  set b₀l : G l := f k l hkl b₀ with hb0l
  have hpl_monic : pl.Monic := hp_monic.map _
  have hpl_map : map (colimitOf G f l) pl = g := by rw [hpl, hpush, hp_map]
  have hb0l_map : colimitOf G f l b₀l = a₀ := by
    rw [hb0l, Ring.DirectLimit.of_f hkl b₀, hb_map]
  have hderul : IsUnit ((derivative pl).eval b₀l) := by
    have he : (derivative pl).eval b₀l = f k l hkl ((derivative p).eval b₀) := by
      rw [hpl, derivative_map, hb0l, eval_map, eval₂_at_apply]
    rw [he]; exact hul
  let := part1_of_isLocalHom G f hlocal l
  have : HenselianLocalRing (G l) := hhens l
  have hevA : pl.eval b₀l ∈ maximalIdeal (G l) := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have huc : IsUnit (g.eval a₀) := by
      have hmu := hu.map (colimitOf G f l)
      rwa [hevalx l pl b₀l hb0l_map, hpl_map] at hmu
    exact (mem_maximalIdeal _).mp hev huc
  obtain ⟨c, hroot, hcb⟩ := HenselianLocalRing.is_henselian pl hpl_monic b₀l hevA hderul
  refine ⟨colimitOf G f l c, ?_, ?_⟩
  · have he : g.eval (colimitOf G f l c) = colimitOf G f l (pl.eval c) := by
      rw [← hpl_map, eval_map, eval₂_at_apply]
    rw [Polynomial.IsRoot.def, he, hroot, map_zero]
  · rw [← hb0l_map, ← map_sub]
    exact map_nonunit (colimitOf G f l) (c - b₀l) hcb

-- this proof's elaboration needs more than the default heartbeat budget
open Polynomial in
/-- **Part 3 (Strictly henselian case).** If each `R_i` is strictly henselian
(henselian with separably closed residue field), then the colimit `R` is strictly
henselian: it is henselian and its residue field is separably closed.

*Argument.* The henselian conjunct is exactly `part2_henselian G f hlocal hhens`.
For separable-closedness of `κ_R`: by `part1_residueField_colimit`,
`κ_R ≃+* colim_i κ_i`, and `IsSepClosed` transports across a ring isomorphism
(`IsSepClosed` is preserved by `RingEquiv`, e.g. via `RingEquiv.isSepClosed` /
pulling separable polynomials back and forth). So it suffices that
`K := colim_i κ_i` is separably closed. Use `IsSepClosed.of_exists_root`: let
`q : K[X]` be monic, irreducible and separable; we find a root.
`Ring.DirectLimit.Polynomial.exists_of` descends `q` to `q_i : κ_i[X]` with
`q_i.map (of i) = q` at some stage `i`; `q` separable forces (after enlarging `i`)
`q_i` separable and of positive degree. Since `κ_i` is separably closed
(`hsep i`), `IsSepClosed.exists_root` gives a root `r ∈ κ_i` of `q_i`; its image
`of i r ∈ K` is a root of `q` (`Polynomial.eval_map`/`eval₂` hom + `of_f`). Hence
`K` is separably closed, and so is `κ_R`. -/
@[stacks 04GI "strictly henselian", ega "IV 18.8.18" "i)"]
theorem part3_strictlyHenselian
    (hhens : ∀ i, HenselianLocalRing (G i))
    (hsep : ∀ i, IsSepClosed (ResidueField (G i))) :
    letI := part1_isLocalRing G f hlocal
    HenselianLocalRing (colimitRing G f) ∧
      IsSepClosed (ResidueField (colimitRing G f)) := by
  let := part1_isLocalRing G f hlocal
  refine ⟨part2_henselian G f hlocal hhens, ?_⟩
  -- Transport `IsSepClosed` across the iso `κ_R ≃+* colim κ_i`
  -- (`part1_residueField_colimit`); reduce to: a filtered colimit of separably
  -- closed fields is separably closed, proved via `IsSepClosed.of_exists_root`
  -- + `Ring.DirectLimit.Polynomial.exists_of` + `IsSepClosed.exists_root` at a
  -- finite stage (`hsep i`), pushing the root forward by `of i`.
  classical
  let : ∀ i, IsLocalHom (colimitOf G f i) := part1_of_isLocalHom G f hlocal
  -- Build the `DirectedSystem` instance on the residue-field system (needed for
  -- `Field.DirectLimit.field`).
  have hds := residueTransition_directedSystem G f hlocal
  -- `K := colim_i κ_i` is a field.
  let : Field (Ring.DirectLimit (fun i => ResidueField (G i))
      (fun i j h => (residueTransition G f hlocal i j h : ResidueField (G i) → ResidueField (G
          j)))) :=
    Field.DirectLimit.field (fun i => ResidueField (G i)) (residueTransition G f hlocal)
  -- **Step A: `K` is separably closed.**
  have hKsep : IsSepClosed (Ring.DirectLimit (fun i => ResidueField (G i))
      (fun i j h => (residueTransition G f hlocal i j h : ResidueField (G i) → ResidueField (G
          j)))) := by
    apply IsSepClosed.of_exists_root
    intro q hqmonic hqirr hqsep
    -- descend `q` to a stage `i`
    obtain ⟨i, qi, hqi⟩ := Ring.DirectLimit.Polynomial.exists_of (f' := residueTransition G f
        hlocal) q
    -- `qi` is separable: its image is separable, and separability descends along
    -- `map` since `Ring.DirectLimit.of` is a field hom (use that the map is
    -- injective). We instead get `qi.Separable` directly from `q.Separable`
    -- by transporting along the injective ring hom `of i`.
    set ofi : ResidueField (G i) →+* (Ring.DirectLimit (fun i => ResidueField (G i))
        (fun i j h => (residueTransition G f hlocal i j h : ResidueField (G i) → ResidueField (G
            j)))) :=
      Ring.DirectLimit.of (fun i => ResidueField (G i))
        (fun i j h => (residueTransition G f hlocal i j h : ResidueField (G i) → ResidueField (G
            j))) i
        with hofi
    have hqideg : qi.degree ≠ 0 := by
      intro h0
      have : q.degree = 0 := by
        rw [← hqi, degree_map_eq_of_injective ofi.injective, h0]
      exact hqirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr this)
    have hqisep : qi.Separable := by
      have : (qi.map ofi).Separable := hqi ▸ hqsep
      exact (Polynomial.separable_map ofi).mp this
    -- `κ_i` is separably closed, so `qi` has a root
    have := hsep i
    obtain ⟨r, hr⟩ := IsSepClosed.exists_root qi hqideg hqisep
    refine ⟨ofi r, ?_⟩
    rw [← hqi, eval_map, eval₂_at_apply, hr.eq_zero, map_zero]
  -- **Step B: transport `IsSepClosed` from `K` to `κ_R` along `e.symm`.**
  obtain ⟨e⟩ := part1_residueField_colimit G f hlocal
  -- `e : κ_R ≃+* K`, so `e.symm : K ≃+* κ_R`.
  apply IsSepClosed.of_exists_root
  intro p hpmonic hpirr hpsep
  set e' : Ring.DirectLimit (fun i => ResidueField (G i))
      (fun i j h => (residueTransition G f hlocal i j h : ResidueField (G i) → ResidueField (G j)))
      ≃+* ResidueField (colimitRing G f) := e.symm with he'
  -- pull `p` back to `K` via `e'.symm = e`
  set q : (Ring.DirectLimit (fun i => ResidueField (G i))
      (fun i j h => (residueTransition G f hlocal i j h : ResidueField (G i) → ResidueField (G
          j))))[X] :=
    p.map (e'.symm : ResidueField (colimitRing G f) →+*
      Ring.DirectLimit (fun i => ResidueField (G i))
        (fun i j h => (residueTransition G f hlocal i j h : ResidueField (G i) → ResidueField (G
            j)))) with hq
  have hqsep : q.Separable := hpsep.map
  have hqdeg : q.degree ≠ 0 := by
    rw [hq, degree_map_eq_of_injective e'.symm.injective]
    exact fun h => hpirr.not_isUnit (Polynomial.isUnit_iff_degree_eq_zero.mpr h)
  obtain ⟨r, hr⟩ := IsSepClosed.exists_root q hqdeg hqsep
  refine ⟨e' r, ?_⟩
  have hpq : p = q.map (e' : _ →+* ResidueField (colimitRing G f)) := by
    rw [hq, Polynomial.map_map]
    have hcomp : (e' : Ring.DirectLimit (fun i => ResidueField (G i))
        (fun i j h => (residueTransition G f hlocal i j h : ResidueField (G i) → ResidueField (G
            j)))
        →+* ResidueField (colimitRing G f)).comp
        (e'.symm : ResidueField (colimitRing G f) →+*
          Ring.DirectLimit (fun i => ResidueField (G i))
            (fun i j h => (residueTransition G f hlocal i j h : ResidueField (G i) → ResidueField
                (G j))))
        = RingHom.id (ResidueField (colimitRing G f)) := by
      ext x
      simp only [RingHom.comp_apply, RingHom.id_apply, RingHom.coe_coe,
        RingEquiv.apply_symm_apply]
    rw [hcomp, Polynomial.map_id]
  rw [Polynomial.IsRoot.def] at hr
  calc eval (e' r) p = eval (e' r) (q.map (e' : _ →+* ResidueField (colimitRing G
      f))) := by rw [hpq]
    _ = eval₂ (e' : _ →+* ResidueField (colimitRing G f)) (e' r) q := by rw [eval_map]
    _ = (e' : _ →+* ResidueField (colimitRing G f)) (eval r q) := eval₂_at_apply _ r
    _ = 0 := by rw [hr, map_zero]
