module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyColimit
public import StacksFrontier.CategoryTheory.Triangulated.PostnikovSystems

/-!
# Postnikov systems for an infinite complex, and their totalization

A Postnikov system (`CategoryTheory.Triangulated.PostnikovSystem`) is attached to a complex of
finite length. An infinite complex `⋯ ⟶ X₂ ⟶ X₁ ⟶ X₀` in a pretriangulated category has instead
a *sequential* Postnikov system: objects `Y₀, Y₁, …` with `Y₀ ≅ X₀` and distinguished triangles
`Yₙ₊₁ ⟶ Xₙ₊₁ ⟶ Yₙ ⟶ Yₙ₊₁⟦1⟧` whose composition `Xₙ₊₁ ⟶ Yₙ ⟶ Xₙ` is the differential. The
connecting morphisms assemble the shifted objects into a system `n ↦ Yₙ⟦n⟧` over `ℕ`, and the
derived colimit of that system is the totalization of the infinite complex.

Such a system exists as soon as the compositions of the complex vanish and every
`Hom(Xᵢ⟦t⟧, Xⱼ)` with `t > 0` vanishes: each finite truncation has a Postnikov system by Stacks
0D83, any two Postnikov systems over the same complex are isomorphic, and the isomorphisms
between the system of one truncation and the restriction of the system of the next let one glue
the last objects of all the truncations into a single sequence.

The totalization is computed when the complex is *split and contractible* in a suitable sense.
If the complex carries morphisms `hₙ : Xₙ ⟶ Xₙ₊₁` and a retraction `ε : X₀ ⟶ A`, `s : A ⟶ X₀` of
`A` with `ε ∘ s = 1` and `1 = ε s + h₀ d₀`, `1 = dₙ hₙ + hₙ₊₁ dₙ₊₁`, then — under a vanishing
hypothesis making the lifts unique enough — the system `n ↦ Yₙ⟦n⟧` becomes a split tower over
`A`: morphisms `rₙ : Yₙ⟦n⟧ ⟶ A` and `sₙ : A ⟶ Yₙ⟦n⟧` with `sₙ rₙ = 1` and transition map
`rₙ ≫ sₙ₊₁`. The telescope map of such a tower is a split idempotent complement, so `A` is its
derived colimit; hence the totalization of the complex is `A`. The hypotheses of that statement
are exactly what an extra degeneracy on an augmented simplicial object supplies to the
alternating face map complex.

## Main definitions

* `CategoryTheory.Triangulated.SequentialPostnikovSystem`: the system of objects `Yₙ` and
  triangles attached to an infinite complex, with `.truncate` its restriction to a finite
  truncation and `.map` its image under a triangulated functor.
* `CategoryTheory.Triangulated.SequentialPostnikovSystem.sequence`: the system `n ↦ Yₙ⟦n⟧` over
  `ℕ`, whose derived colimit is the totalization.
* `CategoryTheory.Triangulated.telescopeMap`: the endomorphism `1 - fₙ` of `∐ Fₙ` whose cofibre
  is the derived colimit of `F`.

## Main results

* `CategoryTheory.Triangulated.nonempty_sequentialPostnikovSystem`: existence of a sequential
  Postnikov system for a complex whose compositions and whose positively shifted `Hom`-groups
  vanish.
* `CategoryTheory.Triangulated.SequentialPostnikovSystem.exists_iso`: two sequential Postnikov
  systems over isomorphic complexes are isomorphic, compatibly with all the structure morphisms;
  `.sequenceIso` and `.sequenceMapIso` transport the comparison to the systems `n ↦ Yₙ⟦n⟧`.
* `CategoryTheory.Triangulated.exists_isHomotopyColimit`: a system over `ℕ` whose direct sum
  exists has a derived colimit.
* `CategoryTheory.Triangulated.split_telescope_distinguished`: the telescope triangle of a split
  tower over `A` has `A` as its cofibre, so `A` is the derived colimit of the tower.
* `CategoryTheory.Triangulated.SequentialPostnikovSystem.split_sequence`: a contraction of the
  complex onto `A` makes the system `n ↦ Yₙ⟦n⟧` a split tower over `A`.
* `CategoryTheory.Triangulated.exists_iso_of_split_restriction`: consequently the image of the
  totalization under a triangulated functor is `A`, compatibly with the map out of `X₀`.
* `CategoryTheory.Triangulated.extraDegeneracy_contraction`: an extra degeneracy on an augmented
  simplicial object contracts its alternating face map complex onto the augmentation.

## Implementation notes

Postnikov systems are finite, so the sequential system is not a Postnikov system for anything;
`SequentialPostnikovSystem.truncate` produces the finite system of each truncation, and the
existence proof runs the other way, choosing a Postnikov system for every truncation length and
gluing. The gluing uses `CategoryTheory.Triangulated.PostnikovSystem.exists_iso` at the identity
isomorphism of complexes, which is where the vanishing hypothesis is spent a second time.

Vanishing hypotheses are stated as "every morphism of this type is zero", with natural-number
shifts, as that is the form in which a caller holds them; `hom_shift_int_eq_zero_of_nat` converts
to the integer shifts that `PostnikovSystem` asks for.

`split_telescope_distinguished` is proved by exhibiting the telescope map as the first morphism
of the direct-sum triangle of `∐ Fₙ` and `A`: the truncated sums `∑_{j<n} sⱼ ≫ ιⱼ` of the
splittings assemble a section of the telescope map modulo the retraction, and the resulting pair
of morphisms is an isomorphism `∐ Fₙ ≅ (∐ Fₙ) ⊞ A` carrying one triangle to the other.

*On `Functor.ofSequence` and transparency.* `Functor.ofSequence` is semireducible, so
`P.sequence.obj n` and `(P.obj n)⟦n⟧` are definitionally equal but not unifiable by `rw`, and a
tactic block that mixes the two spellings fails with "the target expression is not type-correct
under the `implicit` transparency level". Nothing here forces that defeq inside a tactic block.
The transition map is named with its type written out, `sequenceStep`, and the two spellings are
bridged by two lemmas: `sequence_obj`, which is `rfl`, and `sequence_map_succ`, which is *not* —
it is Mathlib's `Functor.ofSequence_map_homOfLE_succ`, proved by induction on the index. So
`split_sequence` states all six of its inputs with no occurrence of `P.sequence` at all and
transports each one once, by `rw [P.sequence_map_succ]` followed by `exact`, which discharges the
remaining defeq at default transparency. One conversion point, rather than defeq in the middle of
a tactic block.

Two further spelling devices appear for the same reason. A naturality square that `rw` cannot
fire on is stated as a private lemma *in the spelling its call site has* — with the iterated
shift written `(u⟦1⟧')⟦n⟧'` rather than `(shiftFunctor 1 ⋙ shiftFunctor n).map u` — and proved by
the `naturality` field as a bare term, which type-checks at default transparency; that is what
`shiftFunctorAdd'_hom_naturality_succ` and its three companions are for. And where a shift index
reaches a lemma as the cast `((0 : ℕ) : ℤ)` rather than as `(0 : ℤ)`, the statement is written
with the cast and the proof is the term about `(0 : ℤ)`, as in
`shiftFunctorZero_naturality_natCast` and `commShiftIso_zero_hom_app_comp`. None of this needs
a transparency-relaxing rewrite, nor a compatibility option, and reintroducing either would be a
regression.

## References

* [Stacks Project, Tag 0D83](https://stacks.math.columbia.edu/tag/0D83)
* [Stacks Project, Tag 090Z](https://stacks.math.columbia.edu/tag/090Z)
* [Stacks Project, Tag 0D9I](https://stacks.math.columbia.edu/tag/0D9I)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Pretriangulated
open scoped Simplicial

universe v u v' u'

namespace CategoryTheory.Triangulated

/-! ### Comparisons of iterated shifts

The two lemmas of this section are naturality squares for `shiftFunctorAdd'` and
`shiftFunctorZero`, written with the composite of shifts spelled as an iterated application and
with the shift index spelled as a cast natural number. Both are the corresponding `naturality`
field, which has the composite spelled as a functor composition and the index in normal form;
stating them here lets the proofs below rewrite with them, which they cannot do with the
`naturality` field itself. -/

section Shifts

variable {D : Type u} [Category.{v} D] [HasShift D ℤ]

/-- Naturality of the comparison `Z⟦n + 1⟧ ≅ (Z⟦1⟧)⟦n⟧`, with the iterated shift spelled as an
iterated application of `shiftFunctor`. -/
private theorem shiftFunctorAdd'_hom_naturality_succ {Z W : D} (n : ℕ) (u : Z ⟶ W) :
    u⟦((n + 1 : ℕ) : ℤ)⟧' ≫
        (shiftFunctorAdd' D 1 (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)).hom.app W =
      (shiftFunctorAdd' D 1 (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)).hom.app Z ≫
        ((u⟦(1 : ℤ)⟧')⟦(n : ℤ)⟧') :=
  (shiftFunctorAdd' D 1 (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)).hom.naturality u

/-- Naturality of the inverse comparison `(Z⟦1⟧)⟦n⟧ ≅ Z⟦n + 1⟧`, with the iterated shift
spelled as an iterated application of `shiftFunctor`. -/
private theorem shiftFunctorAdd'_inv_naturality_succ {Z W : D} (n : ℕ) (u : Z ⟶ W) :
    ((u⟦(1 : ℤ)⟧')⟦(n : ℤ)⟧') ≫
        (shiftFunctorAdd' D 1 (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)).inv.app W =
      (shiftFunctorAdd' D 1 (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)).inv.app Z ≫
        u⟦((n + 1 : ℕ) : ℤ)⟧' :=
  (shiftFunctorAdd' D 1 (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)).inv.naturality u

/-- Naturality of the comparison `Z⟦0⟧ ≅ Z`, with the shift index spelled as the cast of the
natural number `0`. -/
private theorem shiftFunctorZero_naturality_natCast {Z W : D} (u : Z ⟶ W) :
    (shiftFunctor D ((0 : ℕ) : ℤ)).map u ≫ (shiftFunctorZero D ℤ).hom.app W =
      (shiftFunctorZero D ℤ).hom.app Z ≫ u :=
  (shiftFunctorZero D ℤ).hom.naturality u

/-- Naturality of the inverse comparison `Z ≅ Z⟦0⟧`, with the shift index spelled as the cast of
the natural number `0`. -/
private theorem shiftFunctorZero_inv_naturality_natCast {Z W : D} (u : Z ⟶ W) :
    u ≫ (shiftFunctorZero D ℤ).inv.app W =
      (shiftFunctorZero D ℤ).inv.app Z ≫ (shiftFunctor D ((0 : ℕ) : ℤ)).map u :=
  (shiftFunctorZero D ℤ).inv.naturality u

end Shifts

/-! ### Sequential Postnikov systems -/

section Defs

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ t : ℤ, (shiftFunctor D t).Additive] [Pretriangulated D]

/-- A **sequential Postnikov system** for an infinite complex `⋯ ⟶ X₂ ⟶ X₁ ⟶ X₀`, the morphisms
of the complex being `d n : X (n + 1) ⟶ X n`: objects `Y₀, Y₁, …` together with morphisms
`π n : Yₙ ⟶ Xₙ` of which `π 0` is an isomorphism, and distinguished triangles
`Yₙ₊₁ ⟶ Xₙ₊₁ ⟶ Yₙ ⟶ Yₙ₊₁⟦1⟧` in which the composition `Xₙ₊₁ ⟶ Yₙ ⟶ Xₙ` is `d n`. -/
public structure SequentialPostnikovSystem (X : ℕ → D) (d : ∀ n, X (n + 1) ⟶ X n) where
  /-- the objects `Yₙ` of the system -/
  obj : ℕ → D
  /-- the morphisms `Yₙ ⟶ Xₙ` to the terms of the complex -/
  π : ∀ n, obj n ⟶ X n
  /-- the morphism `Y₀ ⟶ X₀` is an isomorphism -/
  isIso_π_zero : IsIso (π 0) := by infer_instance
  /-- the morphisms `Xₙ₊₁ ⟶ Yₙ` -/
  p : ∀ n, X (n + 1) ⟶ obj n
  /-- the connecting morphisms `Yₙ ⟶ Yₙ₊₁⟦1⟧` -/
  δ : ∀ n, obj n ⟶ (obj (n + 1))⟦(1 : ℤ)⟧
  /-- the triangles `Yₙ₊₁ ⟶ Xₙ₊₁ ⟶ Yₙ ⟶ Yₙ₊₁⟦1⟧` are distinguished -/
  distinguished : ∀ n, Triangle.mk (π (n + 1)) (p n) (δ n) ∈ distTriang D
  /-- the composition `Xₙ₊₁ ⟶ Yₙ ⟶ Xₙ` is the morphism `d n` of the complex -/
  p_comp_π : ∀ n, p n ≫ π n = d n

attribute [instance] SequentialPostnikovSystem.isIso_π_zero

omit [HasZeroObject D] [∀ t : ℤ, (shiftFunctor D t).Additive] [Pretriangulated D] in
/-- A vanishing hypothesis stated for natural-number shifts holds for every positive integer
shift. -/
private theorem hom_shift_int_eq_zero_of_nat {A B : D}
    (h : ∀ t : ℕ, 0 < t → ∀ f : A⟦(t : ℤ)⟧ ⟶ B, f = 0)
    (t : ℤ) (ht : 0 < t) (f : A⟦t⟧ ⟶ B) : f = 0 := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt ht)
  exact h n (by omega) f

/-- Dropping the last object of a Postnikov system for a truncation of an infinite complex gives
a Postnikov system for the shorter truncation. -/
private def truncatePostnikovSystem {X : ℕ → D} {d : ∀ n, X (n + 1) ⟶ X n} {n : ℕ}
    (P : PostnikovSystem (fun i : Fin (n + 2) => X i.val) (fun i : Fin (n + 1) => d i.val)) :
    PostnikovSystem (fun i : Fin (n + 1) => X i.val) (fun i : Fin n => d i.val) where
  obj i := P.obj i.castSucc
  π i := P.π i.castSucc
  isIso_π_zero := P.isIso_π_zero
  p i := P.p i.castSucc
  δ i := P.δ i.castSucc
  distinguished i := P.distinguished i.castSucc
  p_comp_π i := P.p_comp_π i.castSucc

/-- **An infinite complex whose compositions vanish and whose positively shifted `Hom`-groups
vanish carries a sequential Postnikov system.** Each finite truncation has one by Stacks 0D83;
the system of the truncation of length `n` and the restriction of the system of the truncation of
length `n + 1` are isomorphic, again by Stacks 0D83, and transporting along those isomorphisms
glues the last objects into one sequence. -/
public theorem nonempty_sequentialPostnikovSystem (X : ℕ → D) (d : ∀ n, X (n + 1) ⟶ X n)
    (hd : ∀ n, d (n + 1) ≫ d n = 0)
    (h : ∀ i j t : ℕ, 0 < t → ∀ f : (X i)⟦(t : ℤ)⟧ ⟶ X j, f = 0) :
    Nonempty (SequentialPostnikovSystem X d) := by
  have hP (n : ℕ) : Nonempty (PostnikovSystem
      (fun i : Fin (n + 1) => X i.val) (fun i : Fin n => d i.val)) := by
    apply nonempty_postnikovSystem_of_hom_shift_eq_zero
    · intro i _
      exact hd i.val
    · intro i j hij f
      exact hom_shift_int_eq_zero_of_nat (h i.val j.val) _ (by omega) f
  let P n := Classical.choice (hP n)
  have he (n : ℕ) : ∃ e : ∀ i, (P n).obj i ≅ (P (n + 1)).obj i.castSucc,
      ∀ i, (e i).hom ≫ (P (n + 1)).π i.castSucc = (P n).π i := by
    obtain ⟨e, he, _, _⟩ := PostnikovSystem.exists_iso
      (fun i j hij f => hom_shift_int_eq_zero_of_nat (h i.val j.val) _ (by omega) f)
      (P n) (truncatePostnikovSystem (P (n + 1)))
      (fun _ => Iso.refl _) (fun _ => by simp)
    exact ⟨e, fun i => by
      simpa only [truncatePostnikovSystem, Category.comp_id, Iso.refl_hom] using he i⟩
  choose e he using he
  refine ⟨{
    obj := fun n => (P n).obj (Fin.last n)
    π := fun n => (P n).π (Fin.last n)
    isIso_π_zero := (P 0).isIso_π_zero
    p := fun n => (P (n + 1)).p (Fin.last n) ≫ (e n (Fin.last n)).inv
    δ := fun n => (e n (Fin.last n)).hom ≫ (P (n + 1)).δ (Fin.last n)
    distinguished := ?_
    p_comp_π := ?_ }⟩
  · intro n
    refine isomorphic_distinguished _ ((P (n + 1)).distinguished (Fin.last n)) _ ?_
    exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (e n (Fin.last n))
      (by simp) (by simp) (by simp)
  · intro n
    rw [← he n (Fin.last n)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    exact (P (n + 1)).p_comp_π (Fin.last n)

/-- The transition morphism `Yₙ⟦n⟧ ⟶ Yₙ₊₁⟦n + 1⟧` of the system
`CategoryTheory.Triangulated.SequentialPostnikovSystem.sequence`: the connecting morphism of the
`n`-th triangle shifted by `n`, read through the comparison of iterated shifts. -/
public noncomputable def SequentialPostnikovSystem.sequenceStep {X : ℕ → D}
    {d : ∀ n, X (n + 1) ⟶ X n} (P : SequentialPostnikovSystem X d) (n : ℕ) :
    (P.obj n)⟦(n : ℤ)⟧ ⟶ (P.obj (n + 1))⟦((n + 1 : ℕ) : ℤ)⟧ :=
  (P.δ n)⟦(n : ℤ)⟧' ≫
    ((shiftFunctorAdd' D 1 (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)).app (P.obj (n + 1))).inv

/-- The system `n ↦ Yₙ⟦n⟧` over `ℕ`, with transition maps the connecting morphisms of the
system shifted by `n`. Its derived colimit is the totalization of the complex. -/
public noncomputable def SequentialPostnikovSystem.sequence {X : ℕ → D} {d : ∀ n, X (n + 1) ⟶ X n}
    (P : SequentialPostnikovSystem X d) : ℕ ⥤ D :=
  Functor.ofSequence P.sequenceStep

/-- The objects of `CategoryTheory.Triangulated.SequentialPostnikovSystem.sequence` are the
shifted objects of the system. Stated so that a goal can be rewritten out of the
`Functor.ofSequence` spelling, which is opaque to `rw`. -/
@[simp] public theorem SequentialPostnikovSystem.sequence_obj {X : ℕ → D}
    {d : ∀ n, X (n + 1) ⟶ X n} (P : SequentialPostnikovSystem X d) (n : ℕ) :
    P.sequence.obj n = (P.obj n)⟦(n : ℤ)⟧ :=
  rfl

/-- The transition maps of `CategoryTheory.Triangulated.SequentialPostnikovSystem.sequence`
are `CategoryTheory.Triangulated.SequentialPostnikovSystem.sequenceStep`. -/
@[simp] public theorem SequentialPostnikovSystem.sequence_map_succ {X : ℕ → D}
    {d : ∀ n, X (n + 1) ⟶ X n} (P : SequentialPostnikovSystem X d) (n : ℕ) :
    P.sequence.map (homOfLE (Nat.le_succ n)) = P.sequenceStep n :=
  Functor.ofSequence_map_homOfLE_succ P.sequenceStep n

section Comparison

/-- The Postnikov system of the truncation of length `n` cut out of a sequential system. -/
public def SequentialPostnikovSystem.truncate {X : ℕ → D} {d : ∀ n, X (n + 1) ⟶ X n}
    (P : SequentialPostnikovSystem X d) (n : ℕ) :
    PostnikovSystem (fun i : Fin (n + 1) => X i.val) (fun i : Fin n => d i.val) where
  obj i := P.obj i.val
  π i := P.π i.val
  isIso_π_zero := P.isIso_π_zero
  p i := P.p i.val
  δ i := P.δ i.val
  distinguished i := P.distinguished i.val
  p_comp_π i := P.p_comp_π i.val

/-- The objects of a sequential Postnikov system inherit the vanishing of the `Hom`-groups out of
a shifted object from the terms of the complex. -/
public theorem SequentialPostnikovSystem.hom_shift_obj_eq_zero {X : ℕ → D}
    {d : ∀ n, X (n + 1) ⟶ X n} (P : SequentialPostnikovSystem X d) (A : D)
    (hA : ∀ (n t : ℕ), 0 < t → ∀ f : A⟦(t : ℤ)⟧ ⟶ X n, f = 0) (j : ℕ) :
    ∀ f : A⟦(1 : ℤ)⟧ ⟶ P.obj j, f = 0 := by
  have h := (PostnikovSystem.hom_shift_obj_eq_zero_and_exists_hom
    (fun _ : Fin (j + 3) => A) (fun _ : Fin (j + 2) => 0) (P.truncate (j + 2))
    (fun i k _ f => hom_shift_int_eq_zero_of_nat (hA k.val) _ (by omega) f)).1
    (Fin.last (j + 2)) ⟨j, by omega⟩ (by simp)
  change ∀ f : A⟦((j + 2 : ℕ) : ℤ) - (j : ℤ) - 1⟧ ⟶ P.obj j, f = 0 at h
  have ht : ((j + 2 : ℕ) : ℤ) - (j : ℤ) - 1 = 1 := by omega
  rw [ht] at h
  exact h

omit [HasZeroObject D] [Pretriangulated D] in
/-- Vanishing of `Hom(A⟦1⟧, B)` gives vanishing of `Hom(A, B⟦-1⟧)`. -/
private theorem hom_to_neg_shift_eq_zero {A B : D}
    (h : ∀ f : A⟦(1 : ℤ)⟧ ⟶ B, f = 0) (f : A ⟶ B⟦(-1 : ℤ)⟧) : f = 0 := by
  apply (shiftFunctor D (1 : ℤ)).map_injective
  rw [Functor.map_zero,
    ← cancel_mono ((shiftFunctorCompIsoId D (-1) (1 : ℤ) (by ring)).app B).hom, zero_comp,
    h (f⟦(1 : ℤ)⟧' ≫ ((shiftFunctorCompIsoId D (-1) (1 : ℤ) (by ring)).app B).hom)]

/-- Under the vanishing hypothesis, a morphism into `Yⱼ` is determined by its composition with
`Yⱼ ⟶ Xⱼ`. -/
public theorem SequentialPostnikovSystem.hom_ext_π {X : ℕ → D} {d : ∀ n, X (n + 1) ⟶ X n}
    (P : SequentialPostnikovSystem X d) (A : D)
    (hA : ∀ (n t : ℕ), 0 < t → ∀ f : A⟦(t : ℤ)⟧ ⟶ X n, f = 0)
    (j : ℕ) {f g : A ⟶ P.obj j} (h : f ≫ P.π j = g ≫ P.π j) : f = g := by
  cases j with
  | zero => exact (cancel_mono (P.π 0)).1 h
  | succ j =>
    obtain ⟨c, hc⟩ := (Triangle.mk (P.π (j + 1)) (P.p j) (P.δ j)).invRotate.coyoneda_exact₂
      (inv_rot_of_distTriang _ (P.distinguished j)) (f - g)
      (by
        show (f - g) ≫ P.π (j + 1) = 0
        rw [Preadditive.sub_comp, h, sub_self])
    have hz : c = 0 := hom_to_neg_shift_eq_zero (P.hom_shift_obj_eq_zero A hA j) c
    have h0 : f - g = 0 := hc.trans (by rw [hz]; exact zero_comp)
    exact sub_eq_zero.mp h0

/-- **Two sequential Postnikov systems over isomorphic complexes are isomorphic.** The
comparison is built one triangle at a time: `Y₀ ≅ Y'₀` because both map isomorphically to the
isomorphic `X₀` and `X'₀`, and the comparison at stage `n + 1` is produced by TR3 from the
comparison at stage `n` together with `Xₙ₊₁ ≅ X'ₙ₊₁`. -/
public theorem SequentialPostnikovSystem.exists_iso {X X' : ℕ → D}
    {d : ∀ n, X (n + 1) ⟶ X n} {d' : ∀ n, X' (n + 1) ⟶ X' n}
    (P : SequentialPostnikovSystem X d) (P' : SequentialPostnikovSystem X' d')
    (h : ∀ (i j t : ℕ), 0 < t → ∀ f : (X i)⟦(t : ℤ)⟧ ⟶ X' j, f = 0)
    (e : ∀ n, X n ≅ X' n) (he : ∀ n, d n ≫ (e n).hom = (e (n + 1)).hom ≫ d' n) :
    ∃ γ : ∀ n, P.obj n ≅ P'.obj n,
      (∀ n, (γ n).hom ≫ P'.π n = P.π n ≫ (e n).hom) ∧
      (∀ n, P.p n ≫ (γ n).hom = (e (n + 1)).hom ≫ P'.p n) ∧
      (∀ n, P.δ n ≫ (γ (n + 1)).hom⟦(1 : ℤ)⟧' = (γ n).hom ≫ P'.δ n) := by
  let B n := {g : P.obj n ≅ P'.obj n // g.hom ≫ P'.π n = P.π n ≫ (e n).hom}
  have hp (n : ℕ) (g : B n) : P.p n ≫ g.val.hom = (e (n + 1)).hom ≫ P'.p n := by
    apply P'.hom_ext_π (X (n + 1)) (h (n + 1)) n
    rw [Category.assoc, g.property, ← Category.assoc, P.p_comp_π, Category.assoc,
      P'.p_comp_π, he]
  have step (n : ℕ) (g : B n) : ∃ g' : B (n + 1),
      P.δ n ≫ g'.val.hom⟦(1 : ℤ)⟧' = g.val.hom ≫ P'.δ n := by
    obtain ⟨a, ha, hδ⟩ := complete_distinguished_triangle_morphism₁
      (Triangle.mk (P.π (n + 1)) (P.p n) (P.δ n))
      (Triangle.mk (P'.π (n + 1)) (P'.p n) (P'.δ n))
      (P.distinguished n) (P'.distinguished n) (e (n + 1)).hom g.val.hom (hp n g)
    have : IsIso a := isIso₁_of_isIso₂₃
      (T := Triangle.mk (P.π (n + 1)) (P.p n) (P.δ n))
      (T' := Triangle.mk (P'.π (n + 1)) (P'.p n) (P'.δ n))
      { hom₁ := a, hom₂ := (e (n + 1)).hom, hom₃ := g.val.hom,
        comm₁ := ha, comm₂ := hp n g, comm₃ := hδ }
      (P.distinguished n) (P'.distinguished n) inferInstance inferInstance
    exact ⟨⟨asIso a, ha.symm⟩, hδ⟩
  let g₀ : B 0 := ⟨asIso (P.π 0) ≪≫ e 0 ≪≫ (asIso (P'.π 0)).symm, by simp⟩
  let g : ∀ n, B n := Nat.rec g₀ (fun n a => (step n a).choose)
  exact ⟨fun n => (g n).val, fun n => (g n).property, fun n => hp n (g n),
    fun n => (step n (g n)).choose_spec⟩

/-- A comparison of two sequential Postnikov systems compatible with the connecting morphisms
induces an isomorphism of the systems `n ↦ Yₙ⟦n⟧`. -/
private theorem sequenceStep_naturality {X X' : ℕ → D}
    {d : ∀ n, X (n + 1) ⟶ X n} {d' : ∀ n, X' (n + 1) ⟶ X' n}
    (P : SequentialPostnikovSystem X d) (P' : SequentialPostnikovSystem X' d')
    (e : ∀ n, P.obj n ≅ P'.obj n)
    (he : ∀ n, P.δ n ≫ (e (n + 1)).hom⟦(1 : ℤ)⟧' = (e n).hom ≫ P'.δ n) (n : ℕ) :
    P.sequenceStep n ≫ ((e (n + 1)).hom)⟦((n + 1 : ℕ) : ℤ)⟧' =
      ((e n).hom)⟦(n : ℤ)⟧' ≫ P'.sequenceStep n := by
  dsimp only [SequentialPostnikovSystem.sequenceStep]
  rw [Iso.app_inv, Iso.app_inv, Category.assoc,
    ← shiftFunctorAdd'_inv_naturality_succ n ((e (n + 1)).hom),
    ← Functor.map_comp_assoc, he, Functor.map_comp, Category.assoc]

/-- A comparison of two sequential Postnikov systems compatible with the connecting morphisms
induces an isomorphism of the systems `n ↦ Yₙ⟦n⟧`. -/
public noncomputable def SequentialPostnikovSystem.sequenceIso {X X' : ℕ → D}
    {d : ∀ n, X (n + 1) ⟶ X n} {d' : ∀ n, X' (n + 1) ⟶ X' n}
    (P : SequentialPostnikovSystem X d) (P' : SequentialPostnikovSystem X' d')
    (e : ∀ n, P.obj n ≅ P'.obj n)
    (he : ∀ n, P.δ n ≫ (e (n + 1)).hom⟦(1 : ℤ)⟧' = (e n).hom ≫ P'.δ n) :
    P.sequence ≅ P'.sequence :=
  NatIso.ofComponents (fun n => (shiftFunctor D (n : ℤ)).mapIso (e n))
    (fun {_ _} f => (NatTrans.ofSequence
      (F := P.sequence) (G := P'.sequence) (fun n => (e n).hom⟦(n : ℤ)⟧')
      (fun n => by
        rw [SequentialPostnikovSystem.sequence_map_succ,
          SequentialPostnikovSystem.sequence_map_succ]
        exact sequenceStep_naturality P P' e he n)).naturality f)

end Comparison

end Defs

/-! ### The image of a sequential Postnikov system under a triangulated functor -/

section Map

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ t : ℤ, (shiftFunctor C t).Additive] [Pretriangulated C]
variable {D : Type u'} [Category.{v'} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ t : ℤ, (shiftFunctor D t).Additive] [Pretriangulated D]

/-- A triangulated functor carries a sequential Postnikov system to a sequential Postnikov
system for the image complex. -/
public def SequentialPostnikovSystem.map {X : ℕ → C} {d : ∀ n, X (n + 1) ⟶ X n}
    (P : SequentialPostnikovSystem X d) (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
    [F.IsTriangulated] :
    SequentialPostnikovSystem (fun n => F.obj (X n)) (fun n => F.map (d n)) where
  obj n := F.obj (P.obj n)
  π n := F.map (P.π n)
  isIso_π_zero := inferInstanceAs (IsIso (F.map (P.π 0)))
  p n := F.map (P.p n)
  δ n := F.map (P.δ n) ≫ (F.commShiftIso (1 : ℤ)).hom.app (P.obj (n + 1))
  distinguished n := F.map_distinguished _ (P.distinguished n)
  p_comp_π n := by rw [← F.map_comp, P.p_comp_π]

private theorem map_sequenceStep {X : ℕ → C} {d : ∀ n, X (n + 1) ⟶ X n}
    (P : SequentialPostnikovSystem X d) (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
    [F.IsTriangulated] (n : ℕ) :
    F.map (P.sequenceStep n) ≫ (F.commShiftIso ((n + 1 : ℕ) : ℤ)).hom.app (P.obj (n + 1)) =
      (F.commShiftIso (n : ℤ)).hom.app (P.obj n) ≫ (P.map F).sequenceStep n := by
  have hnat := (F.commShiftIso (n : ℤ)).hom.naturality (P.δ n)
  simp only [Functor.comp_map] at hnat
  simp only [SequentialPostnikovSystem.sequenceStep, SequentialPostnikovSystem.map,
    Iso.app_inv, Functor.map_comp, Category.assoc]
  rw [F.commShiftIso_add' (show (1 : ℤ) + (n : ℤ) = ((n + 1 : ℕ) : ℤ) by omega)]
  simp only [Functor.CommShift.isoAdd'_hom_app, Functor.comp_obj, ← F.map_comp_assoc,
    Iso.inv_hom_id_app]
  rw [Category.comp_id, reassoc_of% hnat]

/-- The image under a triangulated functor of the system `n ↦ Yₙ⟦n⟧` of a sequential Postnikov
system is the corresponding system of the image system. -/
public noncomputable def SequentialPostnikovSystem.sequenceMapIso {X : ℕ → C}
    {d : ∀ n, X (n + 1) ⟶ X n}
    (P : SequentialPostnikovSystem X d) (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
    [F.IsTriangulated] :
    P.sequence ⋙ F ≅ (P.map F).sequence :=
  NatIso.ofComponents (fun n => (F.commShiftIso (n : ℤ)).app (P.obj n))
    (fun {_ _} f => (NatTrans.ofSequence
      (F := P.sequence ⋙ F) (G := (P.map F).sequence)
      (fun n => (F.commShiftIso (n : ℤ)).hom.app (P.obj n))
      (fun n => by
        rw [Functor.comp_map, SequentialPostnikovSystem.sequence_map_succ,
          SequentialPostnikovSystem.sequence_map_succ]
        exact map_sequenceStep P F n)).naturality f)

/-- The components of
`CategoryTheory.Triangulated.SequentialPostnikovSystem.sequenceMapIso` are the commutation
isomorphisms of `F` with the shifts. -/
@[simp] public theorem SequentialPostnikovSystem.sequenceMapIso_hom_app {X : ℕ → C}
    {d : ∀ n, X (n + 1) ⟶ X n} (P : SequentialPostnikovSystem X d) (F : C ⥤ D) [F.Additive]
    [F.CommShift ℤ] [F.IsTriangulated] (n : ℕ) :
    (P.sequenceMapIso F).hom.app n = (F.commShiftIso (n : ℤ)).hom.app (P.obj n) :=
  rfl

end Map

/-! ### The telescope map and derived colimits -/

section Telescope

variable {D : Type u} [Category.{v} D] [Preadditive D]

/-- The **telescope map** `1 - fₙ` of a system `F : ℕ ⥤ D`: the endomorphism of `∐ Fₙ` which on
the `n`-th summand is `ιₙ - fₙ ≫ ιₙ₊₁`. Its cofibre is the derived colimit of `F`. -/
public noncomputable def telescopeMap (F : ℕ ⥤ D) [HasCoproduct F.obj] : ∐ F.obj ⟶ ∐ F.obj :=
  Sigma.desc fun n => Sigma.ι F.obj n - F.map (homOfLE (Nat.le_succ n)) ≫ Sigma.ι F.obj (n + 1)

end Telescope

section TelescopeTriangulated

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ t : ℤ, (shiftFunctor D t).Additive] [Pretriangulated D]

/-- **A system over `ℕ` whose direct sum exists has a derived colimit**: complete its telescope
map to a distinguished triangle. -/
public theorem exists_isHomotopyColimit (F : ℕ ⥤ D) [HasCoproduct F.obj] :
    ∃ K, IsHomotopyColimit F K := by
  obtain ⟨K, p, q, h⟩ := distinguished_cocone_triangle (telescopeMap F)
  exact ⟨K, p, q, h⟩

/-- **A map out of the bottom of a tower of distinguished triangles extends to the derived
colimit of the tower.**

Let `F : ℕ ⥤ D` be a system whose transition `Fₙ ⟶ Fₙ₊₁` is the second map of a distinguished
triangle `Wₙ ⟶ Fₙ ⟶ Fₙ₊₁ ⟶ Wₙ⟦1⟧`, and let `K` be a derived colimit of `F`, presented by the
distinguished triangle `∐ Fₙ ⟶ ∐ Fₙ ⟶ K ⟶ (∐ Fₙ)⟦1⟧` whose first map is the telescope map. A
map `a : F₀ ⟶ K'` whose composition with `W₀ ⟶ F₀` vanishes, in a situation where every
`Hom(Wₙ, K')` with `n > 0` vanishes, extends step by step up the tower: contravariant exactness
of the `n`-th triangle lifts the map on `Fₙ` to a map on `Fₙ₊₁`, the obstruction being a map
`Wₙ ⟶ K'`, which is the hypothesis at `n = 0` and is zero above. The resulting compatible family
is annihilated by the telescope map, so it factors through `K`.

This is the construction step of Stacks 0D9K and Stacks 0D9S, in which `Fₙ = Yₙ[n]` and
`Wₙ = Xₙ₊₁[n]` for the Postnikov system of Stacks 0D9I, respectively Stacks 0D9Q. -/
public theorem exists_hom_of_telescope (F : ℕ ⥤ D) [HasCoproduct F.obj]
    (W : ℕ → D) (w : ∀ n, W n ⟶ F.obj n) (r : ∀ n, F.obj (n + 1) ⟶ (W n)⟦(1 : ℤ)⟧)
    (hW : ∀ n, Triangle.mk (w n) (F.map (homOfLE (Nat.le_succ n))) (r n) ∈ distTriang D)
    {K K' : D} (p : ∐ F.obj ⟶ K) (q : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧)
    (hK : Triangle.mk (telescopeMap F) p q ∈ distTriang D)
    (a : F.obj 0 ⟶ K') (ha : w 0 ≫ a = 0)
    (hvanish : ∀ n : ℕ, 0 < n → ∀ g : W n ⟶ K', g = 0) :
    ∃ γ : K ⟶ K', Sigma.ι F.obj 0 ≫ p ≫ γ = a := by
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : F.obj 1 ⟶ K', F.map (homOfLE (Nat.le_succ 0)) ≫ c₁ = a := by
    obtain ⟨g, hg⟩ := (Triangle.mk (w 0) (F.map (homOfLE (Nat.le_succ 0))) (r 0)).yoneda_exact₂
      (hW 0) a ha
    exact ⟨g, hg.symm⟩
  have hstep : ∀ (n : ℕ) (c : F.obj (n + 1) ⟶ K'),
      ∃ c' : F.obj (n + 2) ⟶ K', F.map (homOfLE (Nat.le_succ (n + 1))) ≫ c' = c := by
    intro n c
    obtain ⟨g, hg⟩ :=
      (Triangle.mk (w (n + 1)) (F.map (homOfLE (Nat.le_succ (n + 1)))) (r (n + 1))).yoneda_exact₂
        (hW (n + 1)) c (hvanish (n + 1) n.succ_pos _)
    exact ⟨g, hg.symm⟩
  choose lift hlift using hstep
  set d : ∀ n : ℕ, F.obj (n + 1) ⟶ K' :=
    fun n => Nat.rec (motive := fun k => F.obj (k + 1) ⟶ K') c₁ (fun k e => lift k e) n with hd
  set c : ∀ n : ℕ, F.obj n ⟶ K' :=
    fun n => Nat.casesOn (motive := fun k => F.obj k ⟶ K') n a d with hc
  have hcomp : ∀ n : ℕ, F.map (homOfLE (Nat.le_succ n)) ≫ c (n + 1) = c n := by
    intro n
    cases n with
    | zero => exact hc₁
    | succ k => exact hlift k (d k)
  have htel : telescopeMap F ≫ Sigma.desc c = 0 := by
    refine Sigma.hom_ext _ _ fun n => ?_
    rw [← Category.assoc, telescopeMap, Limits.colimit.ι_desc]
    simp only [Cofan.mk_pt, Cofan.mk_ι_app, Preadditive.sub_comp, Category.assoc,
      Limits.colimit.ι_desc, comp_zero]
    rw [hcomp n, sub_self]
  obtain ⟨γ, hγ⟩ := (Triangle.mk (telescopeMap F) p q).yoneda_exact₂ hK (Sigma.desc c) htel
  refine ⟨γ, ?_⟩
  have h₀ : Sigma.ι F.obj 0 ≫ Sigma.desc c = a := Limits.colimit.ι_desc _ _
  rw [hγ] at h₀
  exact h₀

/-- **The derived colimit of a split tower is its base.** If the transition maps of `F` factor as
`rₙ ≫ sₙ₊₁` through an object `A` with `sₙ ≫ rₙ = 1`, then the telescope map of `F` fits into a
distinguished triangle with third object `A` and zero connecting morphism: the telescope map is
the first morphism of the direct-sum triangle of `∐ Fₙ` and `A` read through an isomorphism
`∐ Fₙ ≅ (∐ Fₙ) ⊞ A`. -/
public theorem split_telescope_distinguished (F : ℕ ⥤ D) [HasCoproduct F.obj] (A : D)
    (r : ∀ n, F.obj n ⟶ A) (s : ∀ n, A ⟶ F.obj n) (hs : ∀ n, s n ≫ r n = 𝟙 A)
    (ht : ∀ n, F.map (homOfLE (Nat.le_succ n)) = r n ≫ s (n + 1)) :
    Triangle.mk (telescopeMap F) (Sigma.desc r) 0 ∈ distTriang D := by
  let a (n : ℕ) : A ⟶ ∐ F.obj := s n ≫ Sigma.ι F.obj n
  let v : ∐ F.obj ⟶ ∐ F.obj := Sigma.desc fun n =>
    Sigma.ι F.obj n - r n ≫ a n - r n ≫ ∑ j ∈ Finset.range n, a j
  let p : ∐ F.obj ⟶ A := Sigma.desc r
  have hav (n : ℕ) : a n ≫ v = - ∑ j ∈ Finset.range n, a j := by
    dsimp only [a, v]
    simp only [Category.assoc, Sigma.ι_desc, Preadditive.comp_sub, reassoc_of% (hs n)]
    abel
  have htl (n : ℕ) : a n ≫ telescopeMap F = a n - a (n + 1) := by
    dsimp only [a, telescopeMap]
    simp only [Category.assoc, Sigma.ι_desc, Preadditive.comp_sub, ht, reassoc_of% (hs n)]
  have hsum (n : ℕ) : (∑ j ∈ Finset.range n, a j) ≫ telescopeMap F = a 0 - a n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, Preadditive.add_comp, ih, htl]
      abel
  have hlv : telescopeMap F ≫ v = 𝟙 _ := by
    refine Sigma.hom_ext _ _ fun n => ?_
    simp only [telescopeMap, Sigma.ι_desc_assoc, Preadditive.sub_comp, ht, Category.assoc,
      Category.comp_id]
    rw [← Category.assoc (s (n + 1)) (Sigma.ι F.obj (n + 1)) v]
    show (Sigma.ι F.obj n ≫ v) - r n ≫ (a (n + 1) ≫ v) = _
    rw [hav]
    simp only [v, Sigma.ι_desc, Finset.sum_range_succ, Preadditive.comp_neg,
      Preadditive.comp_add]
    abel
  have hvl : v ≫ telescopeMap F + p ≫ a 0 = 𝟙 _ := by
    refine Sigma.hom_ext _ _ fun n => ?_
    simp only [Preadditive.comp_add, v, p, Sigma.ι_desc_assoc, Preadditive.sub_comp,
      Category.assoc, htl, hsum, Preadditive.comp_sub, Category.comp_id]
    simp only [telescopeMap, Sigma.ι_desc, ht, Category.assoc]
    show (Sigma.ι F.obj n - r n ≫ a (n + 1)) - (r n ≫ a n - r n ≫ a (n + 1)) -
      (r n ≫ a 0 - r n ≫ a n) + r n ≫ a 0 = _
    abel
  have hlp : telescopeMap F ≫ p = 0 := by
    refine Sigma.hom_ext _ _ fun n => ?_
    simp only [telescopeMap, p, Sigma.ι_desc_assoc, Preadditive.sub_comp, ht, Category.assoc,
      Sigma.ι_desc, hs, Category.comp_id, sub_self, comp_zero]
  have hip : a 0 ≫ p = 𝟙 A := by simp [a, p, hs]
  have hiv : a 0 ≫ v = 0 := by simpa using hav 0
  let e : ∐ F.obj ≅ (∐ F.obj) ⊞ A :=
    { hom := biprod.lift v p
      inv := biprod.desc (telescopeMap F) (a 0)
      hom_inv_id := by simpa only [biprod.lift_desc] using hvl
      inv_hom_id := by
        apply biprod.hom_ext' <;> apply biprod.hom_ext <;>
          simp [Category.assoc, hlv, hlp, hip, hiv] }
  refine isomorphic_distinguished _ (binaryBiproductTriangle_distinguished (∐ F.obj) A) _ ?_
  refine Triangle.isoMk _ _ (Iso.refl _) e (Iso.refl _) ?_ ?_ ?_
  · show telescopeMap F ≫ biprod.lift v p = 𝟙 (∐ F.obj) ≫ biprod.inl
    rw [Category.id_comp]
    refine biprod.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, biprod.lift_fst, hlv, biprod.inl_fst]
    · rw [Category.assoc, biprod.lift_snd, hlp, biprod.inl_snd]
  · show Sigma.desc r ≫ 𝟙 A = biprod.lift v p ≫ biprod.snd
    rw [Category.comp_id, biprod.lift_snd]
  · show (0 : A ⟶ (∐ F.obj)⟦(1 : ℤ)⟧) ≫ (𝟙 (∐ F.obj))⟦(1 : ℤ)⟧' = 𝟙 A ≫ 0
    rw [zero_comp, comp_zero]

/-- Two telescope triangles over isomorphic systems have isomorphic cofibres, compatibly with
the morphisms out of the direct sums. -/
public theorem exists_iso_homotopyColimit [HasCoproductsOfShape ℕ D] {F G : ℕ ⥤ D} (e : F ≅ G)
    {K K' : D} {p : ∐ F.obj ⟶ K} {q : K ⟶ (∐ F.obj)⟦(1 : ℤ)⟧}
    {p' : ∐ G.obj ⟶ K'} {q' : K' ⟶ (∐ G.obj)⟦(1 : ℤ)⟧}
    (h : Triangle.mk (telescopeMap F) p q ∈ distTriang D)
    (h' : Triangle.mk (telescopeMap G) p' q' ∈ distTriang D) :
    ∃ γ : K ≅ K', p ≫ γ.hom = (Sigma.mapIso fun n => e.app n).hom ≫ p' := by
  let s := Sigma.mapIso fun n => e.app n
  have hs : telescopeMap F ≫ s.hom = s.hom ≫ telescopeMap G := by
    refine Sigma.hom_ext _ _ fun n => ?_
    simp only [telescopeMap, s, Sigma.ι_mapIso_hom_assoc, Sigma.ι_mapIso_hom,
      Sigma.ι_desc_assoc, Sigma.ι_desc, Preadditive.sub_comp, Preadditive.comp_sub,
      Category.assoc, Iso.app_hom]
    rw [e.hom.naturality_assoc]
  obtain ⟨f, _, hf⟩ := exists_iso_of_arrow_iso _ _ h h' (Arrow.isoMk s s hs.symm)
  refine ⟨Triangle.π₃.mapIso f, ?_⟩
  have hh := f.hom.comm₂
  rw [hf] at hh
  exact hh

end TelescopeTriangulated

/-! ### Contracting the complex -/

section Contraction

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ t : ℤ, (shiftFunctor D t).Additive] [Pretriangulated D]

omit [HasZeroObject D] [HasShift D ℤ] [∀ t : ℤ, (shiftFunctor D t).Additive]
  [Pretriangulated D] in
/-- Given a system `F` over `ℕ`, a retraction of `F 0` onto `A` whose kernel is killed by the
first transition map, and the exactness properties the triangles of a Postnikov system supply,
the retraction propagates to every stage: morphisms `rₙ : Fₙ ⟶ A` and `sₙ : A ⟶ Fₙ` with
`sₙ ≫ rₙ = 1`, `fₙ ≫ rₙ₊₁ = rₙ` and `fₙ = rₙ ≫ sₙ₊₁`. -/
private theorem exists_split_sequence_of_contraction (F : ℕ ⥤ D) (A : D) (C E : ℕ → D)
    (π : ∀ n, F.obj n ⟶ C n) (p : ∀ n, E n ⟶ F.obj n) (h : ∀ n, C n ⟶ E n)
    (hp : ∀ n, p n ≫ F.map (homOfLE (Nat.le_succ n)) = 0)
    (hc : ∀ n, (𝟙 _ - π (n + 1) ≫ h (n + 1) ≫ p (n + 1)) ≫ π (n + 1) = 0)
    (hker : ∀ (n : ℕ) (f : F.obj (n + 1) ⟶ F.obj (n + 1)), f ≫ π (n + 1) = 0 →
      ∃ a : F.obj (n + 1) ⟶ F.obj n, a ≫ F.map (homOfLE (Nat.le_succ n)) = f)
    (hext : ∀ (n : ℕ) (f : F.obj n ⟶ A), p n ≫ f = 0 →
      ∃ g : F.obj (n + 1) ⟶ A, F.map (homOfLE (Nat.le_succ n)) ≫ g = f)
    (hHom : ∀ n, ∀ f : E (n + 1) ⟶ A, f = 0)
    (r₀ : F.obj 0 ⟶ A) (s₀ : A ⟶ F.obj 0) (hs₀ : s₀ ≫ r₀ = 𝟙 A) (hp₀ : p 0 ≫ r₀ = 0)
    (ht₀ : F.map (homOfLE (Nat.le_succ 0)) = r₀ ≫ s₀ ≫ F.map (homOfLE (Nat.le_succ 0))) :
    ∃ (r : ∀ n, F.obj n ⟶ A) (s : ∀ n, A ⟶ F.obj n),
      r 0 = r₀ ∧ s 0 = s₀ ∧ (∀ n, s n ≫ r n = 𝟙 A) ∧
      (∀ n, F.map (homOfLE (Nat.le_succ n)) ≫ r (n + 1) = r n) ∧
      (∀ n, F.map (homOfLE (Nat.le_succ n)) = r n ≫ s (n + 1)) := by
  let B (n : ℕ) := {rs : (F.obj n ⟶ A) × (A ⟶ F.obj n) //
    rs.2 ≫ rs.1 = 𝟙 A ∧ p n ≫ rs.1 = 0 ∧
      F.map (homOfLE (Nat.le_succ n)) = rs.1 ≫ rs.2 ≫ F.map (homOfLE (Nat.le_succ n))}
  have step (n : ℕ) (b : B n) : ∃ b' : B (n + 1),
      F.map (homOfLE (Nat.le_succ n)) ≫ b'.val.1 = b.val.1 ∧
      b'.val.2 = b.val.2 ≫ F.map (homOfLE (Nat.le_succ n)) := by
    obtain ⟨r', hr'⟩ := hext n b.val.1 b.property.2.1
    let s' := b.val.2 ≫ F.map (homOfLE (Nat.le_succ n))
    have hs' : s' ≫ r' = 𝟙 A := by simp only [s', Category.assoc, hr', b.property.1]
    let e := 𝟙 _ - π (n + 1) ≫ h (n + 1) ≫ p (n + 1)
    obtain ⟨a, ha⟩ := hker n e (hc n)
    have her : e ≫ r' = r' := by
      simp [e, Preadditive.sub_comp, Category.assoc, hHom n (p (n + 1) ≫ r')]
    have he : e = r' ≫ s' := by
      have hea : e = (a ≫ b.val.1) ≫ s' := by
        rw [← ha]
        calc a ≫ F.map (homOfLE (Nat.le_succ n))
            = a ≫ (b.val.1 ≫ b.val.2 ≫ F.map (homOfLE (Nat.le_succ n))) :=
              congrArg (a ≫ ·) b.property.2.2
          _ = _ := by simp only [s', Category.assoc]
      have har : a ≫ b.val.1 = r' := by
        calc a ≫ b.val.1 = ((a ≫ b.val.1) ≫ s') ≫ r' := by
              rw [Category.assoc, hs', Category.comp_id]
          _ = r' := by rw [← hea, her]
      rw [hea, har]
    have ht' : F.map (homOfLE (Nat.le_succ (n + 1))) =
        r' ≫ s' ≫ F.map (homOfLE (Nat.le_succ (n + 1))) := by
      rw [← Category.assoc, ← he]
      simp [e, Preadditive.sub_comp, Category.assoc, hp]
    exact ⟨⟨(r', s'), hs', hHom n _, ht'⟩, hr', rfl⟩
  let b₀ : B 0 := ⟨(r₀, s₀), hs₀, hp₀, ht₀⟩
  let b : ∀ n, B n := Nat.rec b₀ (fun n b => (step n b).choose)
  refine ⟨fun n => (b n).val.1, fun n => (b n).val.2, rfl, rfl, fun n => (b n).property.1,
    fun n => (step n (b n)).choose_spec.1, fun n => ?_⟩
  show F.map (homOfLE (Nat.le_succ n)) = (b n).val.1 ≫ ((step n (b n)).choose).val.2
  rw [(step n (b n)).choose_spec.2]
  exact (b n).property.2.2

end Contraction

section Exactness

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]
variable {D : Type u'} [Category.{v'} D] [HasZeroMorphisms D]

/-- An exactness statement of `Hom(-, A)` type, valid for every object of `C`, transports along
an essentially surjective, fully faithful functor. -/
private theorem map_yoneda_exact (F : C ⥤ D) [F.Full] [F.Faithful] [F.EssSurj]
    [F.PreservesZeroMorphisms] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : ∀ (A : C) (a : Y ⟶ A), f ≫ a = 0 → ∃ b, a = g ≫ b)
    (A : D) (a : F.obj Y ⟶ A) (ha : F.map f ≫ a = 0) : ∃ b, a = F.map g ≫ b := by
  let e := F.objObjPreimageIso A
  let a' := F.preimage (a ≫ e.inv)
  have ha' : f ≫ a' = 0 := by
    apply F.map_injective
    simp only [Functor.map_comp, a', Functor.map_preimage, Functor.map_zero, ← Category.assoc,
      ha, zero_comp]
  obtain ⟨b, hb⟩ := h _ a' ha'
  refine ⟨F.map b ≫ e.hom, ?_⟩
  have hh := congrArg (F.map) hb
  simp only [a', Functor.map_preimage, Functor.map_comp] at hh
  rw [← Category.assoc, ← hh]
  simp

/-- An exactness statement of `Hom(A, -)` type, valid for every object of `C`, transports along
an essentially surjective, fully faithful functor. -/
private theorem map_coyoneda_exact (F : C ⥤ D) [F.Full] [F.Faithful] [F.EssSurj]
    [F.PreservesZeroMorphisms] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : ∀ (A : C) (a : A ⟶ Y), a ≫ g = 0 → ∃ b, a = b ≫ f)
    (A : D) (a : A ⟶ F.obj Y) (ha : a ≫ F.map g = 0) : ∃ b, a = b ≫ F.map f := by
  let e := F.objObjPreimageIso A
  let a' := F.preimage (e.hom ≫ a)
  have ha' : a' ≫ g = 0 := by
    apply F.map_injective
    simp only [Functor.map_comp, a', Functor.map_preimage, Functor.map_zero, Category.assoc,
      ha, comp_zero]
  obtain ⟨b, hb⟩ := h _ a' ha'
  refine ⟨e.inv ≫ F.map b, ?_⟩
  have hh := congrArg (F.map) hb
  simp only [a', Functor.map_preimage, Functor.map_comp] at hh
  rw [Category.assoc, ← hh]
  simp

end Exactness

/-! ### Splitting the system of a contracted complex -/

section Split

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ t : ℤ, (shiftFunctor D t).Additive] [Pretriangulated D]

/-- **A contraction of the complex splits the system `n ↦ Yₙ⟦n⟧` over its base.** Given a
retraction `ε : X₀ ⟶ A`, `s : A ⟶ X₀` with `ε ∘ s = 1` and a contracting homotopy `h` with
`ε s + h₀ d₀ = 1` and `dₙ hₙ + hₙ₊₁ dₙ₊₁ = 1`, and given that every morphism
`Xₙ₊₂⟦n + 1⟧ ⟶ A` vanishes, the system `n ↦ Yₙ⟦n⟧` of a sequential Postnikov system for the
complex carries morphisms `rₙ`, `sₙ` to and from `A` splitting its transition maps.

The homotopy makes `Hom(Yₙ⟦n⟧, A)` propagate along the triangles of the system, and the
vanishing hypothesis makes the propagated morphisms unique enough to assemble. -/
public theorem SequentialPostnikovSystem.split_sequence {X : ℕ → D} {d : ∀ n, X (n + 1) ⟶ X n}
    (P : SequentialPostnikovSystem X d) (A : D) (ε : X 0 ⟶ A) (s : A ⟶ X 0)
    (h : ∀ n, X n ⟶ X (n + 1)) (hs : s ≫ ε = 𝟙 A) (hd : d 0 ≫ ε = 0)
    (h₀ : ε ≫ s + h 0 ≫ d 0 = 𝟙 _) (hh : ∀ n, d n ≫ h n + h (n + 1) ≫ d (n + 1) = 𝟙 _)
    (hHom : ∀ n, ∀ f : (X (n + 2))⟦((n + 1 : ℕ) : ℤ)⟧ ⟶ A, f = 0) :
    ∃ (r : ∀ n, P.sequence.obj n ⟶ A) (s' : ∀ n, A ⟶ P.sequence.obj n),
      r 0 = (shiftFunctorZero D ℤ).hom.app (P.obj 0) ≫ P.π 0 ≫ ε ∧
      (∀ n, s' n ≫ r n = 𝟙 A) ∧
      (∀ n, P.sequence.map (homOfLE (Nat.le_succ n)) = r n ≫ s' (n + 1)) := by
  let π : ∀ n : ℕ, (P.obj n)⟦(n : ℤ)⟧ ⟶ (X n)⟦(n : ℤ)⟧ := fun n => (P.π n)⟦(n : ℤ)⟧'
  let p : ∀ n : ℕ, (X (n + 1))⟦(n : ℤ)⟧ ⟶ (P.obj n)⟦(n : ℤ)⟧ := fun n => (P.p n)⟦(n : ℤ)⟧'
  let a (n : ℕ) := (shiftFunctorAdd' D 1 (n : ℤ) ((n + 1 : ℕ) : ℤ) (by omega)).app (P.obj (n + 1))
  -- The four exactness inputs, each stated with no occurrence of `P.sequence`.
  have hp (n : ℕ) : p n ≫ P.sequenceStep n = 0 := by
    have hz : P.p n ≫ P.δ n = 0 := comp_distTriang_mor_zero₂₃ _ (P.distinguished n)
    dsimp only [p, SequentialPostnikovSystem.sequenceStep]
    rw [← Category.assoc, ← Functor.map_comp, hz, Functor.map_zero, zero_comp]
  have hc (n : ℕ) :
      (𝟙 _ - π (n + 1) ≫ (h (n + 1))⟦((n + 1 : ℕ) : ℤ)⟧' ≫ p (n + 1)) ≫ π (n + 1) = 0 := by
    dsimp only [π, p]
    simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc, ← Functor.map_comp,
      P.p_comp_π]
    have hc' : P.π (n + 1) ≫ (h (n + 1) ≫ d (n + 1)) = P.π (n + 1) := by
      have hπd : P.π (n + 1) ≫ d n = 0 := by
        have hz : P.π (n + 1) ≫ P.p n = 0 := comp_distTriang_mor_zero₁₂ _ (P.distinguished n)
        rw [← P.p_comp_π n, ← Category.assoc, hz, zero_comp]
      simpa only [Preadditive.comp_add, ← Category.assoc, hπd, zero_comp, zero_add,
        Category.comp_id] using congrArg (P.π (n + 1) ≫ ·) (hh n)
    rw [hc', sub_self]
  have hker (n : ℕ) (f : (P.obj (n + 1))⟦((n + 1 : ℕ) : ℤ)⟧ ⟶ (P.obj (n + 1))⟦((n + 1 : ℕ) : ℤ)⟧)
      (hf : f ≫ π (n + 1) = 0) :
      ∃ b : (P.obj (n + 1))⟦((n + 1 : ℕ) : ℤ)⟧ ⟶ (P.obj n)⟦(n : ℤ)⟧,
        b ≫ P.sequenceStep n = f := by
    obtain ⟨b, hb⟩ := map_coyoneda_exact (shiftFunctor D (n : ℤ)) (P.δ n) ((P.π (n + 1))⟦(1 : ℤ)⟧')
      (fun _ f hf => (Triangle.mk (P.π (n + 1)) (P.p n) (P.δ n)).coyoneda_exact₁
        (P.distinguished n) f hf) _ (f ≫ (a n).hom) (by
          dsimp only [a]
          rw [Iso.app_hom, Category.assoc,
            ← shiftFunctorAdd'_hom_naturality_succ n (P.π (n + 1)), ← Category.assoc, hf,
            zero_comp])
    refine ⟨b, ?_⟩
    dsimp only [SequentialPostnikovSystem.sequenceStep]
    rw [← Category.assoc, ← hb, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hext (n : ℕ) (f : (P.obj n)⟦(n : ℤ)⟧ ⟶ A) (hf : p n ≫ f = 0) :
      ∃ g : (P.obj (n + 1))⟦((n + 1 : ℕ) : ℤ)⟧ ⟶ A, P.sequenceStep n ≫ g = f := by
    obtain ⟨g, hg⟩ := map_yoneda_exact (shiftFunctor D (n : ℤ)) (P.p n) (P.δ n)
      (fun _ f hf => (Triangle.mk (P.π (n + 1)) (P.p n) (P.δ n)).yoneda_exact₃
        (P.distinguished n) f hf) A f hf
    refine ⟨(a n).hom ≫ g, ?_⟩
    dsimp only [SequentialPostnikovSystem.sequenceStep]
    rw [Category.assoc, Iso.inv_hom_id_assoc, ← hg]
  -- The retraction at stage `0`.
  let e : (P.obj 0)⟦((0 : ℕ) : ℤ)⟧ ≅ X 0 :=
    (shiftFunctorZero D ℤ).app (P.obj 0) ≪≫ asIso (P.π 0)
  let r₀ : (P.obj 0)⟦((0 : ℕ) : ℤ)⟧ ⟶ A := e.hom ≫ ε
  let s₀ : A ⟶ (P.obj 0)⟦((0 : ℕ) : ℤ)⟧ := s ≫ e.inv
  have hs₀ : s₀ ≫ r₀ = 𝟙 A := by simp only [s₀, r₀, Category.assoc, Iso.inv_hom_id_assoc, hs]
  have hp₀ : p 0 ≫ r₀ = 0 := by
    dsimp only [p, r₀, e]
    rw [Iso.trans_hom, Iso.app_hom, asIso_hom, Category.assoc,
      reassoc_of% (shiftFunctorZero_naturality_natCast (P.p 0)), ← Category.assoc (P.p 0),
      P.p_comp_π, hd, comp_zero]
  have ht₀ : P.sequenceStep 0 = r₀ ≫ s₀ ≫ P.sequenceStep 0 := by
    have he : d 0 ≫ e.inv = (shiftFunctorZero D ℤ).inv.app (X 1) ≫ p 0 := by
      dsimp only [e, p]
      rw [← P.p_comp_π 0, Iso.trans_inv, Iso.app_inv, asIso_inv, Category.assoc,
        IsIso.hom_inv_id_assoc]
      exact shiftFunctorZero_inv_naturality_natCast (P.p 0)
    have hp₀' : d 0 ≫ e.inv ≫ P.sequenceStep 0 = 0 := by
      rw [← Category.assoc, he, Category.assoc, hp 0, comp_zero]
    have h₀' := congrArg (fun f => e.hom ≫ f ≫ e.inv ≫ P.sequenceStep 0) h₀
    simpa only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, hp₀', comp_zero,
      add_zero, Iso.hom_inv_id_assoc, Category.id_comp, r₀, s₀] using h₀'.symm
  -- Transport the four inputs and the stage-`0` data to the `P.sequence` spelling.
  have hp' : ∀ n, p n ≫ P.sequence.map (homOfLE (Nat.le_succ n)) = 0 := fun n => by
    rw [P.sequence_map_succ]; exact hp n
  have hker' : ∀ (n : ℕ) (f : P.sequence.obj (n + 1) ⟶ P.sequence.obj (n + 1)),
      f ≫ π (n + 1) = 0 → ∃ b : P.sequence.obj (n + 1) ⟶ P.sequence.obj n,
        b ≫ P.sequence.map (homOfLE (Nat.le_succ n)) = f := fun n f hf =>
    (hker n f hf).imp fun b hb => by rw [P.sequence_map_succ]; exact hb
  have hext' : ∀ (n : ℕ) (f : P.sequence.obj n ⟶ A), p n ≫ f = 0 →
      ∃ g : P.sequence.obj (n + 1) ⟶ A,
        P.sequence.map (homOfLE (Nat.le_succ n)) ≫ g = f := fun n f hf =>
    (hext n f hf).imp fun g hg => by rw [P.sequence_map_succ]; exact hg
  have ht₀' : P.sequence.map (homOfLE (Nat.le_succ 0)) =
      r₀ ≫ s₀ ≫ P.sequence.map (homOfLE (Nat.le_succ 0)) := by
    rw [P.sequence_map_succ]; exact ht₀
  obtain ⟨r, s', hr, _, hsr, _, ht'⟩ := exists_split_sequence_of_contraction P.sequence A
    (fun n => (X n)⟦(n : ℤ)⟧) (fun n => (X (n + 1))⟦(n : ℤ)⟧) π p (fun n => (h n)⟦(n : ℤ)⟧')
    hp' hc hker' hext' hHom r₀ s₀ hs₀ hp₀ ht₀'
  refine ⟨r, s', ?_, hsr, ht'⟩
  rw [hr]
  dsimp only [r₀, e]
  rw [Iso.trans_hom, Iso.app_hom, asIso_hom, Category.assoc]

end Split

/-! ### Comparing the totalization with the base of a contraction -/

section Comparison

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ t : ℤ, (shiftFunctor C t).Additive] [Pretriangulated C]
variable {D : Type u'} [Category.{v'} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ t : ℤ, (shiftFunctor D t).Additive] [Pretriangulated D]

omit [HasZeroObject C] [HasShift C ℤ] [∀ t : ℤ, (shiftFunctor C t).Additive]
  [Pretriangulated C] [HasZeroObject D] [HasShift D ℤ]
  [∀ t : ℤ, (shiftFunctor D t).Additive] [Pretriangulated D] in
/-- An additive functor carries the telescope map of a system to the telescope map of the image
system, through the comparison of the direct sums. -/
private theorem telescopeMap_sigmaComparison (F : C ⥤ D) [F.Additive] (X : ℕ ⥤ C)
    [HasCoproduct X.obj] [h : HasCoproduct (X ⋙ F).obj] :
    letI : HasCoproduct (fun n => F.obj (X.obj n)) := h
    telescopeMap (X ⋙ F) ≫ sigmaComparison F X.obj =
      sigmaComparison F X.obj ≫ F.map (telescopeMap X) := by
  let _ : HasCoproduct (fun n => F.obj (X.obj n)) := h
  have hι (n : ℕ) : Sigma.ι (X ⋙ F).obj n ≫ sigmaComparison F X.obj = F.map (Sigma.ι X.obj n) :=
    ι_comp_sigmaComparison F X.obj n
  refine Sigma.hom_ext _ _ fun n => ?_
  simp only [telescopeMap, Sigma.ι_desc_assoc, Preadditive.sub_comp, Category.assoc, hι,
    reassoc_of% (hι n), Functor.comp_map, ← F.map_comp, Sigma.ι_desc, Functor.map_sub]

omit [HasZeroObject C] [Preadditive C] [∀ t : ℤ, (shiftFunctor C t).Additive]
  [Pretriangulated C] [HasZeroObject D] [Preadditive D]
  [∀ t : ℤ, (shiftFunctor D t).Additive] [Pretriangulated D] in
/-- The comparison of a functor with the zero shift: `F` applied to the identification
`Z⟦0⟧ ≅ Z` is the commutation isomorphism of `F` with the zero shift followed by that
identification in the target. Stated with the shift index spelled as the cast of the natural
number `0`, which is the form the splitting at stage `0` produces. -/
private theorem commShiftIso_zero_hom_app_comp (F : C ⥤ D) [F.CommShift ℤ] (Z : C) :
    (F.commShiftIso (0 : ℤ)).hom.app Z ≫ (shiftFunctorZero D ℤ).hom.app (F.obj Z) =
      F.map ((shiftFunctorZero C ℤ).hom.app Z) := by
  rw [F.commShiftIso_zero]
  simp [Functor.CommShift.isoZero_hom_app]

/-- The image under a triangulated functor of a telescope triangle is a telescope triangle for
the image system. -/
public theorem homotopyColimit_map_distinguished (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
    [F.IsTriangulated] (X : ℕ ⥤ C) [HasCoproduct X.obj] [hX : HasCoproduct (X ⋙ F).obj]
    [PreservesColimit (Discrete.functor X.obj) F] {K : C} (p : ∐ X.obj ⟶ K)
    (q : K ⟶ (∐ X.obj)⟦(1 : ℤ)⟧) (h : Triangle.mk (telescopeMap X) p q ∈ distTriang C) :
    letI : HasCoproduct (fun n => F.obj (X.obj n)) := hX
    ∃ q', Triangle.mk (telescopeMap (X ⋙ F)) (sigmaComparison F X.obj ≫ F.map p) q' ∈
      distTriang D := by
  have hXF : HasCoproduct (fun n => F.obj (X.obj n)) := hX
  refine ⟨F.map q ≫ (F.commShiftIso (1 : ℤ)).hom.app (∐ X.obj) ≫
    ((PreservesCoproduct.iso F X.obj).hom)⟦(1 : ℤ)⟧', ?_⟩
  refine isomorphic_distinguished _ (F.map_distinguished _ h) _
    (Triangle.isoMk _ _ (PreservesCoproduct.iso F X.obj).symm
      (PreservesCoproduct.iso F X.obj).symm (Iso.refl _)
      (telescopeMap_sigmaComparison F X) ?_ ?_)
  · show (sigmaComparison F X.obj ≫ F.map p) ≫ 𝟙 (F.obj K) =
      sigmaComparison F X.obj ≫ F.map p
    rw [Category.comp_id]
  · show (F.map q ≫ (F.commShiftIso (1 : ℤ)).hom.app (∐ X.obj) ≫
        ((PreservesCoproduct.iso F X.obj).hom)⟦(1 : ℤ)⟧') ≫
        ((PreservesCoproduct.iso F X.obj).inv)⟦(1 : ℤ)⟧' =
      𝟙 (F.obj K) ≫ F.map q ≫ (F.commShiftIso (1 : ℤ)).hom.app (∐ X.obj)
    rw [Category.id_comp, Category.assoc, Category.assoc, ← Functor.map_comp,
      Iso.hom_inv_id, Functor.map_id]
    simp

/-- **The image of the totalization is the base of a contraction of the image complex.** Let `K`
be the cofibre of the telescope map of the system `n ↦ Yₙ⟦n⟧` of a sequential Postnikov system,
with `i : X₀ ⟶ K` the induced morphism, and let `F` be a triangulated functor preserving
countable direct sums. If the image system `n ↦ F(Yₙ)⟦n⟧` splits over an object `A` compatibly
with `ε : F X₀ ⟶ A`, then `F K ≅ A` by an isomorphism carrying `F i` to `ε`. -/
public theorem exists_iso_of_split_restriction [HasCoproductsOfShape ℕ C]
    [HasCoproductsOfShape ℕ D] {X : ℕ → C} {d : ∀ n, X (n + 1) ⟶ X n}
    (P : SequentialPostnikovSystem X d) (F : C ⥤ D) [F.Additive] [F.CommShift ℤ]
    [F.IsTriangulated] [PreservesColimitsOfShape (Discrete ℕ) F] {K : C}
    (p : ∐ P.sequence.obj ⟶ K) (q : K ⟶ (∐ P.sequence.obj)⟦(1 : ℤ)⟧)
    (hK : Triangle.mk (telescopeMap P.sequence) p q ∈ distTriang C) (i : X 0 ⟶ K)
    (hi : P.π 0 ≫ i =
      (shiftFunctorZero C ℤ).inv.app (P.obj 0) ≫ Sigma.ι P.sequence.obj 0 ≫ p)
    (A : D) (ε : F.obj (X 0) ⟶ A) (r : ∀ n, (P.map F).sequence.obj n ⟶ A)
    (s : ∀ n, A ⟶ (P.map F).sequence.obj n)
    (hr : r 0 = (shiftFunctorZero D ℤ).hom.app (F.obj (P.obj 0)) ≫ F.map (P.π 0) ≫ ε)
    (hs : ∀ n, s n ≫ r n = 𝟙 A)
    (ht : ∀ n, (P.map F).sequence.map (homOfLE (Nat.le_succ n)) = r n ≫ s (n + 1)) :
    ∃ γ : F.obj K ≅ A, F.map i ≫ γ.hom = ε := by
  let e := P.sequenceMapIso F
  let r' (n : ℕ) := (e.app n).hom ≫ r n
  let s' (n : ℕ) := s n ≫ (e.app n).inv
  have hs' (n : ℕ) : s' n ≫ r' n = 𝟙 A := by
    simp only [r', s', Iso.app_hom, Iso.app_inv, Category.assoc, Iso.inv_hom_id_app_assoc, hs]
  have ht' (n : ℕ) : (P.sequence ⋙ F).map (homOfLE (Nat.le_succ n)) = r' n ≫ s' (n + 1) := by
    apply (cancel_mono (e.app (n + 1)).hom).1
    simp only [r', s', Category.assoc, Category.comp_id, Iso.app_hom, Iso.app_inv,
      e.hom.naturality, ht, Iso.inv_hom_id_app]
  obtain ⟨q', hq'⟩ := homotopyColimit_map_distinguished F P.sequence p q hK
  obtain ⟨γ, hγ⟩ := exists_iso_homotopyColimit (Iso.refl (P.sequence ⋙ F)) hq'
    (split_telescope_distinguished (P.sequence ⋙ F) A r' s' hs' ht')
  have hγ' : (sigmaComparison F P.sequence.obj ≫ F.map p) ≫ γ.hom = Sigma.desc r' := by
    rw [hγ]
    refine Sigma.hom_ext _ _ fun n => ?_
    simp only [Sigma.ι_mapIso_hom_assoc, Iso.app_hom, Iso.refl_hom, NatTrans.id_app,
      Category.id_comp]
  have hι : F.map (Sigma.ι P.sequence.obj 0 ≫ p) ≫ γ.hom = r' 0 := by
    rw [F.map_comp, Category.assoc, ← ι_comp_sigmaComparison F P.sequence.obj 0,
      Category.assoc, ← Category.assoc (sigmaComparison F P.sequence.obj), hγ',
      Sigma.ι_desc]
  have key : (F.commShiftIso (((0 : ℕ)) : ℤ)).hom.app (P.obj 0) ≫
      (shiftFunctorZero D ℤ).hom.app (F.obj (P.obj 0)) =
      F.map ((shiftFunctorZero C ℤ).hom.app (P.obj 0)) :=
    commShiftIso_zero_hom_app_comp F (P.obj 0)
  have hr₀ : r' 0 =
      F.map ((shiftFunctorZero C ℤ).hom.app (P.obj 0)) ≫ F.map (P.π 0) ≫ ε := by
    simp only [r', hr, e, SequentialPostnikovSystem.sequenceMapIso_hom_app, Iso.app_hom]
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ F.map (P.π 0) ≫ ε) key)
  refine ⟨γ, ?_⟩
  apply (cancel_epi (F.map (P.π 0))).1
  have hiγ : F.map (P.π 0) ≫ F.map i ≫ γ.hom =
      F.map ((shiftFunctorZero C ℤ).inv.app (P.obj 0)) ≫ r' 0 := by
    rw [← F.map_comp_assoc, hi, F.map_comp, Category.assoc]
    exact congrArg (F.map ((shiftFunctorZero C ℤ).inv.app (P.obj 0)) ≫ ·) hι
  rw [hiγ, hr₀, ← F.map_comp_assoc]
  simp

end Comparison

/-! ### Nullity of a map out of the totalization

The nullity criterion of Stacks 0D9J and 0D9R in its sequential form: a map out of a derived
colimit of the system `n ↦ Yₙ⟦n⟧` which annihilates every map out of `Y₀⟦0⟧` vanishes as
soon as every map out of `Xₙ⟦n⟧` and out of `Xₙ⟦n + 1⟧` does. -/

section Nullity

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ t : ℤ, (shiftFunctor D t).Additive] [Pretriangulated D]

omit [HasZeroObject D] [Pretriangulated D] in
/-- A morphism is zero as soon as one of its shifts is: the shift functors are faithful. -/
private theorem eq_zero_of_shift_map_eq_zero {A B : D} (t : ℤ) (g : A ⟶ B)
    (h : (shiftFunctor D t).map g = 0) : g = 0 :=
  (shiftFunctor D t).map_injective (by rw [h, Functor.map_zero])

omit [HasZeroObject D] [Pretriangulated D] in
/-- The comparison `A[n + 1] ≅ (A[1])[n]` of iterated shifts, in the form in which the transition
map of a sequential Postnikov system uses it. -/
private abbrev succShiftIso (A : D) (n : ℕ) :
    (shiftFunctor D ((n + 1 : ℕ) : ℤ)).obj A ≅
      (shiftFunctor D (n : ℤ)).obj ((shiftFunctor D (1 : ℤ)).obj A) :=
  (shiftFunctorAdd' D 1 (n : ℤ) ((n + 1 : ℕ) : ℤ) (by push_cast; ring)).app A

variable {X : ℕ → D} {d : ∀ n, X (n + 1) ⟶ X n}

/-- **The inductive step.** A morphism out of `Yₙ₊₁[n + 1]` which is killed by the transition
`Yₙ[n] ⟶ Yₙ₊₁[n + 1]` factors through `Xₙ₊₁[n + 1]`, hence vanishes when every morphism out of
`Xₙ₊₁[n + 1]` does. The factorisation is the two-fold rotation of the `n`-th triangle of the
system, shifted by `n`. -/
private theorem hom_eq_zero_of_sequenceStep (P : SequentialPostnikovSystem X d) {L : D} (n : ℕ)
    (hX : ∀ g : (shiftFunctor D ((n + 1 : ℕ) : ℤ)).obj (X (n + 1)) ⟶ L, g = 0)
    (g : (shiftFunctor D ((n + 1 : ℕ) : ℤ)).obj (P.obj (n + 1)) ⟶ L)
    (hg : P.sequenceStep n ≫ g = 0) : g = 0 := by
  have hrot := rot_of_distTriang _ (rot_of_distTriang _ (P.distinguished n))
  have hex : ∀ (Z : D) (u : (shiftFunctor D (1 : ℤ)).obj (P.obj (n + 1)) ⟶ Z),
      P.δ n ≫ u = 0 →
      ∃ u' : (shiftFunctor D (1 : ℤ)).obj (X (n + 1)) ⟶ Z,
        u = (-((shiftFunctor D (1 : ℤ)).map (P.π (n + 1)))) ≫ u' :=
    fun Z u hu => Triangle.yoneda_exact₂ _ hrot u hu
  have hg' : (shiftFunctor D (n : ℤ)).map (P.δ n) ≫ (succShiftIso (P.obj (n + 1)) n).inv ≫ g
      = 0 := by
    rw [← Category.assoc]
    exact hg
  obtain ⟨u', hu'⟩ := map_yoneda_exact (shiftFunctor D (n : ℤ)) (P.δ n)
    (-((shiftFunctor D (1 : ℤ)).map (P.π (n + 1))))
    hex L ((succShiftIso (P.obj (n + 1)) n).inv ≫ g) hg'
  have hu'0 : u' = 0 :=
    (cancel_epi (succShiftIso (X (n + 1)) n).hom).mp (by rw [comp_zero]; exact hX _)
  exact (cancel_epi (succShiftIso (P.obj (n + 1)) n).inv).mp
    (by rw [comp_zero, hu', hu'0, comp_zero])

/-- **The base case.** A morphism out of `Y₀[0]` vanishes once every morphism out of `X₀[0]`
does, because `Y₀ ⟶ X₀` is an isomorphism. -/
private theorem hom_zero_eq_zero (P : SequentialPostnikovSystem X d) {L : D}
    (hX : ∀ g : (shiftFunctor D ((0 : ℕ) : ℤ)).obj (X 0) ⟶ L, g = 0)
    (g : (shiftFunctor D ((0 : ℕ) : ℤ)).obj (P.obj 0) ⟶ L) : g = 0 :=
  (cancel_epi (inv ((shiftFunctor D ((0 : ℕ) : ℤ)).map (P.π 0)))).mp
    (by rw [comp_zero]; exact hX _)

/-- The inductive step in the spelling of the system `n ↦ Yₙ[n]`. -/
private theorem hom_eq_zero_of_sequence_map (P : SequentialPostnikovSystem X d) {L : D} (n : ℕ)
    (hX : ∀ g : (shiftFunctor D ((n + 1 : ℕ) : ℤ)).obj (X (n + 1)) ⟶ L, g = 0)
    (g : P.sequence.obj (n + 1) ⟶ L)
    (hg : P.sequence.map (homOfLE (Nat.le_succ n)) ≫ g = 0) : g = 0 := by
  rw [P.sequence_map_succ] at hg
  exact hom_eq_zero_of_sequenceStep P n hX g hg

/-- **Every morphism `Yₙ[n] ⟶ L` vanishes** once every morphism `Xₙ[n] ⟶ L` does. The case
`n = 0` is the isomorphism `Y₀ ≅ X₀` of the system, and the inductive step is the triangle
`Yₙ[n] ⟶ Yₙ₊₁[n + 1] ⟶ Xₙ₊₁[n + 1] ⟶ Yₙ[n + 1]`. -/
theorem SequentialPostnikovSystem.hom_sequence_eq_zero (P : SequentialPostnikovSystem X d)
    {L : D} (hX : ∀ n : ℕ, ∀ g : (shiftFunctor D (n : ℤ)).obj (X n) ⟶ L, g = 0) :
    ∀ (n : ℕ) (g : P.sequence.obj n ⟶ L), g = 0 := by
  intro n
  induction n with
  | zero => exact fun g ↦ hom_zero_eq_zero P (hX 0) g
  | succ n ih =>
      intro g
      exact hom_eq_zero_of_sequence_map P n (hX (n + 1)) g
        (ih (P.sequence.map (homOfLE (Nat.le_succ n)) ≫ g))

/-- **The nullity criterion of Stacks 0D9J and 0D9R, in pure triangulated form.** Let `Yₙ` be a
sequential Postnikov system for a complex `⋯ ⟶ X₂ ⟶ X₁ ⟶ X₀` in a pretriangulated category and
let `K` be a derived colimit of the tower `Yₙ[n]`. If `Hom(Xₙ[n], K') = 0` for `n > 0` and
`Hom(Xₙ[n + 1], K') = 0` for every `n`, then a morphism `f : K ⟶ K'` annihilating every morphism
out of `Y₀[0]` is zero.

The proof is the source's: an induction along the triangles of the system shows that `f`
annihilates every coprojection `Yₙ[n] ⟶ K` of the telescope triangle, so `f` factors through
`(⨁ Yₙ[n])[1]`; a second induction, for the target `K'[-1]`, shows that every morphism out of
`(⨁ Yₙ[n])[1]` vanishes. -/
theorem SequentialPostnikovSystem.eq_zero_of_isHomotopyColimit
    (P : SequentialPostnikovSystem X d) [HasCoproduct P.sequence.obj] {K K' : D}
    (hcolim : IsHomotopyColimit P.sequence K)
    (hX : ∀ n : ℕ, 0 < n → ∀ g : (shiftFunctor D (n : ℤ)).obj (X n) ⟶ K', g = 0)
    (hX' : ∀ n : ℕ, ∀ g : (shiftFunctor D ((n : ℤ) + 1)).obj (X n) ⟶ K', g = 0)
    {f : K ⟶ K'} (hf : ∀ c : P.sequence.obj 0 ⟶ K, c ≫ f = 0) :
    f = 0 := by
  obtain ⟨p, q, hT⟩ := hcolim
  -- The coprojections of the telescope triangle are compatible with the transitions.
  have hp : (Sigma.desc fun m ↦ Sigma.ι P.sequence.obj m -
      P.sequence.map (homOfLE (Nat.le_succ m)) ≫ Sigma.ι P.sequence.obj (m + 1)) ≫ p = 0 :=
    comp_distTriang_mor_zero₁₂ _ hT
  have hι : ∀ m : ℕ, Sigma.ι P.sequence.obj m ≫ p =
      P.sequence.map (homOfLE (Nat.le_succ m)) ≫ Sigma.ι P.sequence.obj (m + 1) ≫ p := by
    intro m
    have h1 : Sigma.ι P.sequence.obj m ≫ (Sigma.desc fun m' ↦ Sigma.ι P.sequence.obj m' -
        P.sequence.map (homOfLE (Nat.le_succ m')) ≫ Sigma.ι P.sequence.obj (m' + 1)) ≫ p = 0 := by
      rw [hp, comp_zero]
    rw [← Category.assoc, Sigma.ι_desc, Preadditive.sub_comp, Category.assoc, sub_eq_zero] at h1
    exact h1
  -- First induction: `f` annihilates every coprojection.
  have hstep : ∀ n : ℕ, (Sigma.ι P.sequence.obj n ≫ p) ≫ f = 0 := by
    intro n
    induction n with
    | zero => exact hf _
    | succ n ih =>
        refine hom_eq_zero_of_sequence_map P n (hX (n + 1) (Nat.succ_pos n)) _ ?_
        rw [← Category.assoc, ← hι n]
        exact ih
  have hpf : p ≫ f = 0 := by
    refine Sigma.hom_ext _ _ fun n ↦ ?_
    rw [comp_zero, ← Category.assoc]
    exact hstep n
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ hT f hpf
  -- Second induction, for the target `K'[-1]`: every morphism out of `Yₙ[n]` vanishes.
  have hXneg : ∀ n : ℕ, ∀ h : (shiftFunctor D (n : ℤ)).obj (X n) ⟶
      (shiftFunctor D (-1 : ℤ)).obj K', h = 0 := by
    intro n h
    refine hom_to_neg_shift_eq_zero (fun u => ?_) h
    exact (cancel_epi ((shiftFunctorAdd' D (n : ℤ) 1 ((n : ℤ) + 1) rfl).app (X n)).hom).mp
      (by rw [comp_zero]; exact hX' n _)
  have hzero := P.hom_sequence_eq_zero hXneg
  -- Hence every morphism out of `(⨁ Yₙ[n])[1]` vanishes, and `f = q ≫ g = 0`.
  have hgzero : g = 0 := by
    refine eq_zero_of_shift_map_eq_zero (-1 : ℤ) g ?_
    refine (cancel_epi ((shiftFunctorCompIsoId D (1 : ℤ) (-1) (by omega)).app
      (∐ P.sequence.obj)).inv).mp ?_
    rw [comp_zero]
    refine Sigma.hom_ext _ _ fun n ↦ ?_
    rw [comp_zero, ← Category.assoc]
    exact hzero n _
  rw [hg, hgzero, comp_zero]

end Nullity

/-! ### Extra degeneracies contract the alternating face map complex -/

section ExtraDegeneracy

open AlgebraicTopology

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D]

omit [HasZeroObject D] in
/-- **An extra degeneracy contracts the alternating face map complex.** For an augmented
simplicial object `X` with an extra degeneracy, the differential `d` of the alternating face map
complex of `X.left` satisfies `d₀ ∘ ε = 0`, `ε ∘ s' + s₀ ∘ d₀ = 1` and
`dₙ ∘ sₙ + sₙ₊₁ ∘ dₙ₊₁ = 1`, where `ε` is the augmentation in degree zero. These are exactly the
hypotheses of `CategoryTheory.Triangulated.SequentialPostnikovSystem.split_sequence`. -/
public theorem extraDegeneracy_contraction (X : SimplicialObject.Augmented D)
    (ed : X.ExtraDegeneracy) :
    let d := AlternatingFaceMapComplex.objD X.left
    d 0 ≫ X.hom.app (Opposite.op ⦋0⦌) = 0 ∧
      (X.hom.app (Opposite.op ⦋0⦌) ≫ ed.s' : X.left _⦋0⦌ ⟶ X.left _⦋0⦌) + ed.s 0 ≫ d 0 = 𝟙 _ ∧
      ∀ n, d n ≫ ed.s n + ed.s (n + 1) ≫ d (n + 1) = 𝟙 _ := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · rw [AlternatingFaceMapComplex.objD, Fin.sum_univ_two, Fin.val_zero, pow_zero, one_smul,
      Fin.val_one, pow_one, neg_smul, one_smul, Preadditive.add_comp, Preadditive.neg_comp,
      SimplicialObject.δ_naturality, SimplicialObject.δ_naturality]
    exact add_neg_cancel _
  · show _ + ed.s 0 ≫ (∑ j : Fin 2, (-1 : ℤ) ^ (j : ℕ) • X.left.δ j) = _
    rw [Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
      Preadditive.comp_add, Preadditive.comp_neg, ed.s_comp_δ₀, ed.s₀_comp_δ₁]
    abel
  · intro n
    simp only [AlternatingFaceMapComplex.objD, Preadditive.sum_comp, Preadditive.comp_sum,
      Preadditive.zsmul_comp, Preadditive.comp_zsmul]
    rw [Fin.sum_univ_succ (n := n + 2)]
    simp only [Fin.val_zero, pow_zero, one_smul, ed.s_comp_δ₀, Fin.val_succ, pow_succ,
      ed.s_comp_δ, mul_neg_one, neg_smul, Finset.sum_neg_distrib]
    abel

end ExtraDegeneracy

end CategoryTheory.Triangulated

end
