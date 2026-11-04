module

public import StacksFrontier.AlgebraicGeometry.NoetherianApproximation.OpenModel

/-!
# Pairs of a stage and a subalgebra of the ring at that stage

Let `F : K ⥤ CommRingCat` be a diagram of commutative rings over a preorder `K`, and let `P`
single out distinguished `ℤ`-subalgebras of each ring `F.obj k`. This file constructs the
preorder of pairs `(k, A)` with `A` a distinguished subalgebra of `F.obj k`, where
`(k, A) ≤ (k', A')` exactly when `k ≤ k'` and the transition `F.obj k → F.obj k'` carries `A`
into `A'`. The projection to `K` has cofinal image as soon as every stage carries a distinguished
subalgebra, and the preorder is directed as soon as `K` is directed and the distinguished
subalgebras are finitely generated and cofinal among the finitely generated subalgebras at each
stage. For the finite-type open models of Tag 01Z7 this is the index of the inverse system in
Tag 07RN.

## Main definitions

* `Stacks.StageSubalgebra`: the type of pairs of a stage and a distinguished subalgebra there.
* `Stacks.StageSubalgebra.transport`: the image of a subalgebra under a transition map.
* `Stacks.StageSubalgebra.instPreorder`: the order on pairs described above.
* `Stacks.StageSubalgebra.proj`: the monotone projection to the stages.

## Main results

* `Stacks.StageSubalgebra.exists_le_proj`: the projection has cofinal image when every stage
  carries a distinguished subalgebra.
* `Stacks.StageSubalgebra.isDirected`: the pairs are directed when the stages are directed and
  the distinguished subalgebras are finitely generated and cofinal among finitely generated
  subalgebras.
* `Stacks.StageSubalgebra.nonempty_isFiniteTypeOpenModel` and
  `Stacks.StageSubalgebra.isDirected_isFiniteTypeOpenModel`: for the finite-type open models of
  Tag 01Z7, the pairs form a nonempty directed preorder.

## Implementation notes

A subalgebra is transported along `h : k ≤ k'` as its image under the `ℤ`-algebra map underlying
`F.map (CategoryTheory.homOfLE h)`. Since the morphisms of a preorder form a subsingleton, the
choice of inequality proof is irrelevant, and reflexivity and transitivity of the order reduce to
`Subalgebra.map_id` and `Subalgebra.map_map`.

## What is NOT done here

The index is built, but the *diagram* over it is not: nothing here produces the inverse system
of schemes `V_i ⊔_{W_i} Spec A`, its cone, or an inhabitant of
`AlgebraicGeometry.Scheme.FiniteTypeApproximation`.  In particular the functor sending a pair to
the spectrum of its subalgebra is not built, and neither is the compatibility of the images of
the open immersions of Tag 01Z7 with the transition morphisms, which is what the cartesianness
condition of the structure needs.  Tag 07RN is not proved and no tag attribute is attached to
anything in this file.

## References

* [Stacks Project, Tag 07RN](https://stacks.math.columbia.edu/tag/07RN)
* [Stacks Project, Tag 01Z7](https://stacks.math.columbia.edu/tag/01Z7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks

variable {K : Type u} [Preorder K] (F : K ⥤ CommRingCat.{u})
  (P : ∀ k : K, Subalgebra ℤ (F.obj k) → Prop)

/-- The type of pairs of a stage `k` together with a distinguished subalgebra of the ring
`F.obj k`. -/
def StageSubalgebra : Type u := Σ k : K, {A : Subalgebra ℤ (F.obj k) // P k A}

namespace StageSubalgebra

variable {F P}

/-- The image of a subalgebra under a transition morphism of the diagram of rings. -/
def transport {k k' : K} (h : k ≤ k') (A : Subalgebra ℤ (F.obj k)) :
    Subalgebra ℤ (F.obj k') :=
  A.map (F.map (homOfLE h)).hom.toIntAlgHom

/-- Transport along `k ≤ k` is the identity. -/
lemma transport_rfl {k : K} (A : Subalgebra ℤ (F.obj k)) : transport (le_refl k) A = A := by
  rw [transport, Subsingleton.elim (homOfLE (le_refl k)) (𝟙 k), F.map_id]
  exact Subalgebra.map_id A

/-- Transport along `k ≤ k'` followed by transport along `k' ≤ k''` is transport along
`k ≤ k''`. -/
lemma transport_transport {k k' k'' : K} (h : k ≤ k') (h' : k' ≤ k'')
    (A : Subalgebra ℤ (F.obj k)) :
    transport h' (transport h A) = transport (h.trans h') A := by
  rw [transport, transport, transport, Subalgebra.map_map,
    Subsingleton.elim (homOfLE (h.trans h')) (homOfLE h ≫ homOfLE h'), F.map_comp]
  rfl

/-- Transport is monotone in the subalgebra. -/
lemma transport_mono {k k' : K} (h : k ≤ k') {A B : Subalgebra ℤ (F.obj k)} (hAB : A ≤ B) :
    transport h A ≤ transport h B :=
  Subalgebra.map_mono hAB

/-- The order on the index: a later stage whose subalgebra absorbs the image of the earlier
one. -/
instance instPreorder : Preorder (StageSubalgebra F P) where
  le j j' := ∃ h : j.1 ≤ j'.1, transport h j.2.1 ≤ j'.2.1
  le_refl j := ⟨le_rfl, (transport_rfl j.2.1).le⟩
  le_trans := by
    rintro j j' j'' ⟨h, hA⟩ ⟨h', hA'⟩
    refine ⟨h.trans h', ?_⟩
    rw [← transport_transport h h']
    exact (transport_mono h' hA).trans hA'

/-- `j ≤ j'` if and only if the stage of `j` is at most that of `j'` and the transport of the
subalgebra of `j` is contained in the subalgebra of `j'`. -/
lemma le_iff {j j' : StageSubalgebra F P} :
    j ≤ j' ↔ ∃ h : j.1 ≤ j'.1, transport h j.2.1 ≤ j'.2.1 := Iff.rfl

/-- The projection of the index of pairs to the stages. -/
def proj : StageSubalgebra F P →o K where
  toFun j := j.1
  monotone' _ _ h := h.1

/-- The projection of a pair is its stage. -/
@[simp] lemma proj_apply (j : StageSubalgebra F P) : proj j = j.1 := rfl

/-- The projection to the stages has cofinal image as soon as every stage carries a
distinguished subalgebra. -/
lemma exists_le_proj (hne : ∀ k, ∃ A, P k A) (k : K) :
    ∃ j : StageSubalgebra F P, k ≤ proj j :=
  (hne k).elim fun A hA ↦ ⟨⟨k, A, hA⟩, le_rfl⟩

/-- The type of pairs is nonempty when `K` is nonempty and every stage carries a distinguished
subalgebra. -/
lemma nonempty [Nonempty K] (hne : ∀ k, ∃ A, P k A) : Nonempty (StageSubalgebra F P) :=
  (exists_le_proj hne (Classical.arbitrary K)).elim fun j _ ↦ ⟨j⟩

/-- The pairs are directed as soon as the stages are directed and the distinguished subalgebras
are finitely generated and cofinal among the finitely generated subalgebras at each stage. -/
lemma isDirected [IsDirected K (· ≤ ·)]
    (hfg : ∀ (k : K) (A : Subalgebra ℤ (F.obj k)), P k A → A.FG)
    (hcof : ∀ (k : K) (C : Subalgebra ℤ (F.obj k)), C.FG → ∃ A, P k A ∧ C ≤ A) :
    IsDirected (StageSubalgebra F P) (· ≤ ·) := by
  refine ⟨fun j j' ↦ ?_⟩
  obtain ⟨k, hk, hk'⟩ := directed_of (· ≤ ·) j.1 j'.1
  obtain ⟨A, hA, hAle⟩ := hcof k (transport hk j.2.1 ⊔ transport hk' j'.2.1)
    (((hfg _ _ j.2.2).map _).sup ((hfg _ _ j'.2.2).map _))
  exact ⟨⟨k, A, hA⟩, ⟨hk, le_sup_left.trans hAle⟩, ⟨hk', le_sup_right.trans hAle⟩⟩

/-! ### Finite-type open models -/

section OpenModel

open AlgebraicGeometry
open Stacks.FiniteTypeOpenModel (IsOpenModel exists_openModel)

variable {W : K → Scheme.{u}} (f : ∀ k, W k ⟶ Spec (.of (F.obj k)))
  [∀ k, LocallyOfFiniteType (terminal.from (W k))]
  [∀ k, QuasiCompact (terminal.from (W k))] [∀ k, IsOpenImmersion (f k)]

/-- The pairs of a stage `k` and a finite-type open model of `f k` form a nonempty type when `K`
is nonempty. -/
lemma nonempty_isFiniteTypeOpenModel [Nonempty K] :
    Nonempty (StageSubalgebra F fun k A ↦ IsOpenModel (f k) A) :=
  nonempty fun k ↦ exists_openModel (f k)

/-- The pairs of a stage `k` and a finite-type open model of `f k` are directed when `K` is
directed. -/
lemma isDirected_isFiniteTypeOpenModel [IsDirected K (· ≤ ·)] :
    IsDirected (StageSubalgebra F fun k A ↦ IsOpenModel (f k) A) (· ≤ ·) :=
  isDirected (fun _ _ hA ↦ hA.1) fun k C hC ↦ exists_isFiniteTypeOpenModel_ge (f k) C hC

end OpenModel

end StageSubalgebra

end Stacks
