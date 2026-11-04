module

import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.ExtremalEpi
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import StacksFrontier.CategoryTheory.EssentiallyConstant.Biproducts
import StacksFrontier.CategoryTheory.EssentiallyConstant.Cofinal
import StacksFrontier.CategoryTheory.EssentiallyConstant.Operations
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegreeHom
import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Essentially constant systems

An inverse system in a category `𝒞` is a functor `A : J ⥤ 𝒞` on a cofiltered index category `J`
(for a directed set `I` one takes `J = Iᵒᵖ`, so that a transition morphism `A_{j'} ⟶ A_j` is the
image of an arrow `j' ⟶ j`). Being *essentially constant* is a property of the pro-object such a
system represents, so it is essential constancy (Stacks 05PU) of the opposite diagram
`A.op : Jᵒᵖ ⥤ 𝒞ᵒᵖ`, as in Stacks 05PV. This file collects what happens to that notion in a
pre-triangulated category and in the derived category of an abelian category.

In a pre-triangulated category essential constancy is a purely additive phenomenon: a system is
essentially constant exactly when, past some index, it splits as the direct sum of a constant
system and one that is *essentially zero* (Stacks 0G39). For an inverse system of distinguished
triangles `A_j ⟶ B_j ⟶ C_j ⟶ A_j[1]` it is a two-out-of-three property, and the three values
assemble into a distinguished triangle receiving a morphism from one of the terms of the system
(Stacks 0G3A); when the third terms are pro-zero the maps `A_j ⟶ B_j` are an isomorphism of
pro-objects (Stacks 0G3C).

In the derived category `D(𝒜)` of an abelian category both questions can be tested on cohomology,
as long as the cohomology of the system is supported in a fixed bounded range of degrees: such a
system is essentially constant as soon as each system `(H^i(A_j))_j` is, and then
`H^i` of its value is the value of `(H^i(A_j))_j` (Stacks 0G3B); and an inverse system of maps
`A_j ⟶ B_j` is an isomorphism of pro-objects as soon as each `H^i(A_j) ⟶ H^i(B_j)` is
(Stacks 0G3D).

## Main results

* `CategoryTheory.Pretriangulated.isEssentiallyConstant_op_iff_exists_iso_const_biprod`:
  Stacks 0G39, the splitting criterion.
* `CategoryTheory.Pretriangulated.isEssentiallyConstant_op_π₂_and_exists_limit_triangle`:
  Stacks 0G3A, two-out-of-three for an inverse system of distinguished triangles.
* `CategoryTheory.Pretriangulated.exists_proInverse_mor₁_of_proZero_π₃`: Stacks 0G3C, a
  pro-isomorphism from a system of distinguished triangles with pro-zero third terms.
* `DerivedCategory.isEssentiallyConstant_op_and_exists_limit_cone_of_homology`: Stacks 0G3B,
  essential constancy in `D(𝒜)` tested on cohomology.
* `DerivedCategory.exists_proInverse_of_proInverse_homology`: Stacks 0G3D, a pro-isomorphism in
  `D(𝒜)` detected on cohomology.

## Implementation notes

The indices `j ≥ n` of the sources are the objects of `Over n`, the category of objects of `J`
equipped with a morphism to `n`; for `J = Iᵒᵖ` a preorder this is the set `{j // n ≤ j}` with its
induced order, and a system restricted to those indices is `Over.forget n ⋙ A`. This is the
reading of "for all `j ≥ n`" that makes sense for an arbitrary cofiltered index category, which is
why none of the statements is restricted to systems indexed by a directed set.

"`A_n ⟶ A` induces an isomorphism `lim_{j ≥ n} A_j ⟶ A`" is stated as: there is a cone on the
restricted system *with apex `A`* which is a limit cone and whose leg at the index `n` is split by
the given morphism `A_n ⟶ A`. This is equivalent to the sources' phrasing — given such a cone, the
map from any limit to `A` induced by `A_n ⟶ A` is transported to the split leg, hence is an
isomorphism; conversely a limit cone can be transported along the comparison isomorphism — and it
pins the map without carrying a `HasLimit` side condition. Since
`CategoryTheory.Limits.IsLimit` is data rather than a proposition, such a clause reads
`Nonempty (IsLimit …)`. In Stacks 0G3B the cohomological clause is that *the same* cone, pushed
forward by `H^i`, is again a limit cone, which is stronger than the existence of some limit cone
with apex `H^i(X)`: it identifies the comparison map with `H^i(φ)`.

Being an isomorphism of pro-objects is spelled out as the data of a single morphism inverting a
transition morphism in both directions, and pro-vanishing as the existence, below every index, of
a vanishing transition morphism, in the form Stacks 0G3C states them. This puts no size condition
on the index category, whereas going through
morphisms of pro-objects (Stacks 05PX) and the criterion of Stacks 0G2X — that composition with
`α.app j` is a bijection `colim_j Hom(B_j, X) ⟶ colim_j Hom(A_j, X)` — would constrain the
universe of `J` against that of the ambient category.

Only a pre-triangulated category is assumed where the sources say triangulated: the proofs use
TR1, TR3, the splitting of a morphism with a section (Stacks 05QT, 05QU) and the long exact
sequences of a distinguished triangle, never the octahedron axiom. The pointwise splittings of
Stacks 0G39 are assembled by hand rather than by
`CategoryTheory.Idempotents.functor_category_isIdempotentComplete`, because a pre-triangulated
category need not be idempotent complete: only idempotents of the special form `𝟙 - r ≫ s` with
`s ≫ r = 𝟙` are known to split, which is the case at hand.

Stacks 0G3B and 0G3D take the two bounds `a` and `b` on the degrees as explicit arguments rather
than existentially quantified, and drop the sources' condition `a ≤ b`, which is never used (for
`b < a` the hypotheses say that all the objects are zero). The vanishing is spelled
`i < a ∨ b < i` rather than `i ∉ Set.Icc a b`, which is the form a caller can use directly. In
Stacks 0G3D the passage to a chain, i.e. to the index category `ℕᵒᵖ`, is what makes the system of
cones of the maps `α_j` available: the cone of a morphism is not functorial, so there is no system
of triangles over `J` itself, whereas over `ℕᵒᵖ` the triangles and the morphisms between them can
be chosen one step at a time (`CategoryTheory.Functor.ofOpSequence`). Nothing is lost: the
conclusion at an index is an existence statement about a refinement of it.

## References

* [Stacks Project, Tag 0G39](https://stacks.math.columbia.edu/tag/0G39) (Lemma 13.42.1),
  [Tag 0G3A](https://stacks.math.columbia.edu/tag/0G3A) (Lemma 13.42.2),
  [Tag 0G3B](https://stacks.math.columbia.edu/tag/0G3B) (Lemma 13.42.3),
  [Tag 0G3C](https://stacks.math.columbia.edu/tag/0G3C) (Lemma 13.42.4) and
  [Tag 0G3D](https://stacks.math.columbia.edu/tag/0G3D) (Lemma 13.42.5). The source omits the
  proof of the converse in 0G39. Essential constancy is Tag 05PU, Tag 05PV for systems.
-/

@[expose] public section

universe w v u v' u'

namespace CategoryTheory

open Limits Opposite EssentiallyConstantInd

/-! ### Generalities on essentially constant systems -/

section EssConst

variable {K : Type u} [Category.{v} K] {C : Type u'} [Category.{v'} C]

/-- Essential constancy is transported along an isomorphism of functors. -/
private theorem isEssentiallyConstant_of_natIso {M N : K ⥤ C} (e : M ≅ N)
    (h : IsEssentiallyConstantInd M) : IsEssentiallyConstantInd N := by
  obtain ⟨t, i₀, r, h⟩ := h
  exact ⟨_, _, _, h.precompose e.symm⟩

/-- A cone whose leg at one index is split by a morphism `r`, and which cofinally factors the
transition morphisms of the diagram through `r`, is a limit cone.

This is `EssentiallyConstantInd.IsEssentiallyConstantWith.isColimit` read in `Cᵒᵖ`: the
opposite cocone `c.op` carries the same three data, and `c.op.unop` is `c`, so no transport
along an isomorphism of cones is needed. Stated for an arbitrary diagram, with no assumption on
the index category. -/
private noncomputable def isLimitOfSplitLegOfCofinal {F : K ⥤ C} (c : Cone F) {k₀ : K}
    (r : F.obj k₀ ⟶ c.pt) (hr : c.π.app k₀ ≫ r = 𝟙 c.pt)
    (hcof : ∀ k : K, ∃ (k' : K) (a : k' ⟶ k) (b : k' ⟶ k₀),
      F.map a = F.map b ≫ r ≫ c.π.app k) :
    IsLimit c :=
  isLimitConeUnopOfCocone F.op (c := c.op)
    (IsEssentiallyConstantWith.isColimit (r := r.op)
      ⟨by simpa using congrArg Quiver.Hom.op hr, fun j => by
        obtain ⟨k', a, b, h⟩ := hcof j.unop
        exact ⟨op k', b.op, a.op, by simpa using congrArg Quiver.Hom.op h⟩⟩)

end EssConst

/-! ### Pro-zero systems and pro-inverses -/

section ProObjects

variable {J : Type u} [Category.{v} J] {𝒞 : Type u'} [Category.{v'} 𝒞] {A B : J ⥤ 𝒞}

/-- An inverse system is *pro-zero* when every index admits an arrow along which the transition
morphism vanishes: Stacks 05PU(2) written out, and the hypothesis of Stacks 0G3C. -/
@[sga "2 II Lemma9"]
private def IsProZero [HasZeroMorphisms 𝒞] (M : J ⥤ 𝒞) : Prop :=
  ∀ j : J, ∃ (k : J) (g : k ⟶ j), M.map g = 0

/-- `HasProInverse α f` says that the arrow `f : k ⟶ j` inverts the morphism `α : A ⟶ B` of
inverse systems: a single morphism `s : B_k ⟶ A_j` has the transition morphisms of `A` and of `B`
along `f` as its two round trips with `α`. That every index admits such an arrow is the assertion
that `α` is an isomorphism of pro-objects, in the form Stacks 0G3C states it. -/
private def HasProInverse (α : A ⟶ B) {k j : J} (f : k ⟶ j) : Prop :=
  ∃ s : B.obj k ⟶ A.obj j, α.app k ≫ s = A.map f ∧ s ≫ α.app j = B.map f

/-- Refining the source of an arrow preserves the existence of a pro-inverse. -/
private lemma HasProInverse.comp_left {α : A ⟶ B} {k j : J} {f : k ⟶ j}
    (h : HasProInverse α f) {k' : J} (p : k' ⟶ k) : HasProInverse α (p ≫ f) := by
  obtain ⟨s, h₁, h₂⟩ := h
  refine ⟨B.map p ≫ s, ?_, ?_⟩
  · rw [← Category.assoc, ← α.naturality p, Category.assoc, h₁, ← A.map_comp]
  · rw [Category.assoc, h₂, ← B.map_comp]

/-- Composing an arrow with a further transition preserves the existence of a pro-inverse. -/
private lemma HasProInverse.comp_right {α : A ⟶ B} {k j : J} {f : k ⟶ j}
    (h : HasProInverse α f) {j' : J} (t : j ⟶ j') : HasProInverse α (f ≫ t) := by
  obtain ⟨s, h₁, h₂⟩ := h
  refine ⟨s ≫ A.map t, ?_, ?_⟩
  · rw [← Category.assoc, h₁, ← A.map_comp]
  · rw [Category.assoc, α.naturality t, ← Category.assoc, h₂, ← B.map_comp]

/-- In a degree where the two systems vanish, every arrow is a pro-inverse: the zero morphism. -/
private lemma hasProInverse_of_isZero [HasZeroMorphisms 𝒞] {α : A ⟶ B} {k j : J} (f : k ⟶ j)
    (hA : IsZero (A.obj j)) (hB : IsZero (B.obj k)) : HasProInverse α f :=
  ⟨0, hA.eq_of_tgt _ _, hB.eq_of_src _ _⟩

/-- Every index admits a refinement which is a pro-inverse for the `m` members `β i`,
`a ≤ i < a + m`, of a family of morphisms of inverse systems. -/
private lemma exists_refinement_of_lt {A' B' : ℤ → (J ⥤ 𝒞)} (β : ∀ i : ℤ, A' i ⟶ B' i) (a : ℤ)
    (hH : ∀ (i : ℤ) (j : J), ∃ (k : J) (f : k ⟶ j), HasProInverse (β i) f) (m : ℕ) (j : J) :
    ∃ (k : J) (f : k ⟶ j), ∀ i : ℤ, a ≤ i → i < a + m → HasProInverse (β i) f := by
  induction m with
  | zero => exact ⟨j, 𝟙 j, fun i h₁ h₂ => by simp at h₂; omega⟩
  | succ m ih =>
      obtain ⟨k, f, hf⟩ := ih
      obtain ⟨k', f', hf'⟩ := hH (a + m) k
      refine ⟨k', f' ≫ f, fun i h₁ h₂ => ?_⟩
      rcases lt_or_ge i (a + m) with h | h
      · exact (hf i h₁ h).comp_left f'
      · obtain rfl : i = a + m := by push_cast at h₂ ⊢; omega
        exact hf'.comp_right f

/-- Every index admits a refinement which is a pro-inverse for a family `β i` of morphisms of
inverse systems in *every* degree `i`, as soon as it is one in each of the finitely many degrees
where the systems do not vanish. -/
private lemma exists_refinement [HasZeroMorphisms 𝒞] {A' B' : ℤ → (J ⥤ 𝒞)}
    (β : ∀ i : ℤ, A' i ⟶ B' i) (a b : ℤ)
    (hA : ∀ i : ℤ, i < a ∨ b < i → ∀ j : J, IsZero ((A' i).obj j))
    (hB : ∀ i : ℤ, i < a ∨ b < i → ∀ j : J, IsZero ((B' i).obj j))
    (hH : ∀ (i : ℤ) (j : J), ∃ (k : J) (f : k ⟶ j), HasProInverse (β i) f) (j : J) :
    ∃ (k : J) (f : k ⟶ j), ∀ i : ℤ, HasProInverse (β i) f := by
  obtain ⟨k, f, hf⟩ := exists_refinement_of_lt β a hH (b + 1 - a).toNat j
  refine ⟨k, f, fun i => ?_⟩
  rcases lt_or_ge i a with h | h
  · exact hasProInverse_of_isZero f (hA i (Or.inl h) j) (hB i (Or.inl h) k)
  · rcases lt_or_ge b i with h' | h'
    · exact hasProInverse_of_isZero f (hA i (Or.inr h') j) (hB i (Or.inr h') k)
    · exact hf i h (by omega)

/-- A relation on the morphisms of `J` which refines every index gives a chain of refinements
starting at any given index. -/
private lemma exists_seq_of_forall_exists (R : ∀ k j : J, (k ⟶ j) → Prop)
    (hR : ∀ j : J, ∃ (k : J) (g : k ⟶ j), R k j g) (j₀ : J) :
    ∃ (c : ℕ → J) (g : ∀ n : ℕ, c (n + 1) ⟶ c n), c 0 = j₀ ∧ ∀ n : ℕ, R _ _ (g n) := by
  choose F G hG using hR
  exact ⟨fun n => Nat.rec (motive := fun _ => J) j₀ (fun _ p => F p) n, fun n => G _, rfl,
    fun n => hG _⟩

end ProObjects

section EssentiallyConstant

variable {J : Type u} [Category.{v} J]

/-- A pro-zero inverse system is essentially constant, with value a zero object. -/
private lemma isEssentiallyConstant_op_of_isProZero [IsCofiltered J] {𝒞 : Type u'}
    [Category.{v'} 𝒞] [HasZeroMorphisms 𝒞] [HasZeroObject 𝒞] (M : J ⥤ 𝒞) (hM : IsProZero M) :
    IsEssentiallyConstantInd M.op := by
  obtain ⟨j₀⟩ := IsCofiltered.nonempty (C := J)
  obtain ⟨O, hO⟩ := ‹HasZeroObject 𝒞›.zero
  refine ⟨Cocone.mk (op O) { app := fun _ => 0, naturality := by intros; simp }, op j₀, 0, ?_, ?_⟩
  · simpa using ((IsZero.iff_id_eq_zero _).1 hO.op).symm
  · intro j
    obtain ⟨k₀, g, hg⟩ := hM j.unop
    obtain ⟨W, p, q, -⟩ := IsCofilteredOrEmpty.cone_objs k₀ j₀
    refine ⟨op W, q.op, (p ≫ g).op, ?_⟩
    simp [hg]

/-- A system all of whose objects are zero is essentially constant as a pro-object. -/
private lemma isEssentiallyConstant_op_of_isZero [IsCofiltered J] {𝒞 : Type u'}
    [Category.{v'} 𝒞] [HasZeroMorphisms 𝒞] [HasZeroObject 𝒞] {M : J ⥤ 𝒞}
    (h : ∀ j, IsZero (M.obj j)) : IsEssentiallyConstantInd M.op :=
  isEssentiallyConstant_op_of_isProZero M fun j => ⟨j, 𝟙 j, (h j).eq_of_src _ _⟩

end EssentiallyConstant

/-! ### Essential constancy of a pro-object, as cone data -/

section Witnesses

variable {J : Type u} [Category.{v} J] {D : Type u'} [Category.{v'} D]

/-- The datum making a diagram `M : J ⥤ 𝒟` an essentially constant pro-object with value `X`:
a cone with apex `X`, a retraction `M_n ⟶ X` of the leg at `n`, and the cofinality clause
saying that every transition morphism into `M_j` factors, further down, through `X`. This is
`IsEssentiallyConstantInd M.op` read in `𝒟` rather than in `𝒟ᵒᵖ`. -/
private structure Witness (M : J ⥤ D) (X : D) (n : J) where
  /-- The legs of the cone. -/
  leg (j : J) : X ⟶ M.obj j
  /-- The cone condition. -/
  leg_map {j j' : J} (u : j' ⟶ j) : leg j' ≫ M.map u = leg j
  /-- The retraction at the index `n`. -/
  ret : M.obj n ⟶ X
  /-- The retraction splits the leg at `n`. -/
  leg_ret : leg n ≫ ret = 𝟙 X
  /-- Cofinally, the transition morphisms factor through `X`. -/
  cofinal (j : J) : ∃ (k : J) (u : k ⟶ j) (v : k ⟶ n),
    M.map u = M.map v ≫ ret ≫ leg j

namespace Witness

variable {M : J ⥤ D} {X : D} {n : J}

/-- A leg of the cone absorbs a transition morphism into `n` followed by the retraction. -/
private theorem leg_comp_ret (w : Witness M X n) {W : D} {m : J} (f : m ⟶ n) (t : X ⟶ W) :
    w.leg m ≫ M.map f ≫ w.ret ≫ t = t := by
  rw [← Category.assoc (w.leg m), w.leg_map f, ← Category.assoc, w.leg_ret, Category.id_comp]

/-- The comparison `Hom(X, W) ⟶ colim_j Hom(M_j, W)` is surjective, elementwise. -/
private theorem surj (w : Witness M X n) (W : D) (j : J) (g : M.obj j ⟶ W) :
    ∃ (h : X ⟶ W) (k : J) (u : k ⟶ j) (v : k ⟶ n), M.map u ≫ g = M.map v ≫ w.ret ≫ h := by
  obtain ⟨k, u, v, hk⟩ := w.cofinal j
  exact ⟨w.leg j ≫ g, k, u, v, by rw [hk]; simp only [Category.assoc]⟩

/-- The comparison `Hom(X, W) ⟶ colim_j Hom(M_j, W)` is injective, elementwise. -/
private theorem inj (w : Witness M X n) {W : D} {h h' : X ⟶ W} {k : J} (u v : k ⟶ n)
    (hyp : M.map u ≫ w.ret ≫ h = M.map v ≫ w.ret ≫ h') : h = h' :=
  calc h = w.leg k ≫ M.map u ≫ w.ret ≫ h := (w.leg_comp_ret u h).symm
    _ = w.leg k ≫ M.map v ≫ w.ret ≫ h' := by rw [hyp]
    _ = h' := w.leg_comp_ret v h'

/-- Essential constancy of `M` as a pro-object is the same data as a `Witness`. -/
private theorem isEssentiallyConstant (w : Witness M X n) : IsEssentiallyConstantInd M.op := by
  refine ⟨Cocone.mk (op X) { app := fun j => (w.leg j.unop).op, naturality := ?_ }, op n,
    w.ret.op, ?_, ?_⟩
  · intro j j' u
    apply Quiver.Hom.unop_inj
    simpa using w.leg_map u.unop
  · apply Quiver.Hom.unop_inj
    simpa using w.leg_ret
  · intro j
    obtain ⟨k, u, v, hk⟩ := w.cofinal j.unop
    refine ⟨op k, v.op, u.op, ?_⟩
    apply Quiver.Hom.unop_inj
    simpa using hk

/-- Every essentially constant pro-object carries a `Witness`. -/
private theorem exists_witness {M : J ⥤ D} (h : IsEssentiallyConstantInd M.op) :
    ∃ (X : D) (n : J), Nonempty (Witness M X n) := by
  obtain ⟨t, i₀, b, hb, hcof⟩ := h
  refine ⟨t.pt.unop, i₀.unop, ⟨{ leg := fun j => (t.ι.app (op j)).unop
                                 leg_map := ?_
                                 ret := b.unop
                                 leg_ret := ?_
                                 cofinal := ?_ }⟩⟩
  · intro j j' u
    have := t.ι.naturality u.op
    simpa using congrArg Quiver.Hom.unop this
  · simpa using congrArg Quiver.Hom.unop hb
  · intro j
    obtain ⟨k, v, u, hk⟩ := hcof (op j)
    exact ⟨k.unop, u.unop, v.unop, by simpa using congrArg Quiver.Hom.unop hk⟩

/-- The index of a `Witness` can be moved further down the cofiltered index category. -/
private def transport [IsCofiltered J] (w : Witness M X n) {m : J} (g : m ⟶ n) :
    Witness M X m where
  leg := w.leg
  leg_map := w.leg_map
  ret := M.map g ≫ w.ret
  leg_ret := by rw [← Category.assoc, w.leg_map g, w.leg_ret]
  cofinal j := by
    obtain ⟨k, u, v, hk⟩ := w.cofinal j
    refine ⟨IsCofiltered.eq (IsCofiltered.minToLeft k m ≫ v) (IsCofiltered.minToRight k m ≫ g),
      IsCofiltered.eqHom _ _ ≫ IsCofiltered.minToLeft k m ≫ u,
      IsCofiltered.eqHom _ _ ≫ IsCofiltered.minToRight k m, ?_⟩
    have he := IsCofiltered.eq_condition (IsCofiltered.minToLeft k m ≫ v)
      (IsCofiltered.minToRight k m ≫ g)
    calc M.map (IsCofiltered.eqHom _ _ ≫ IsCofiltered.minToLeft k m ≫ u)
        = M.map (IsCofiltered.eqHom _ _ ≫ IsCofiltered.minToLeft k m) ≫ M.map u := by
          simp only [Functor.map_comp, Category.assoc]
      _ = M.map (IsCofiltered.eqHom _ _ ≫ IsCofiltered.minToLeft k m ≫ v) ≫ w.ret ≫ w.leg j := by
          rw [hk]; simp only [Functor.map_comp, Category.assoc]
      _ = M.map (IsCofiltered.eqHom _ _ ≫ IsCofiltered.minToRight k m ≫ g) ≫ w.ret ≫ w.leg j := by
          rw [he]
      _ = M.map (IsCofiltered.eqHom _ _ ≫ IsCofiltered.minToRight k m) ≫
            (M.map g ≫ w.ret) ≫ w.leg j := by
          simp only [Functor.map_comp, Category.assoc]

/-- The image of a `Witness` under a functor. -/
private def mapFunctor {E : Type*} [Category E] (w : Witness M X n) (F : D ⥤ E) :
    Witness (M ⋙ F) (F.obj X) n where
  leg j := F.map (w.leg j)
  leg_map u := by
    dsimp only [Functor.comp_map]
    rw [← F.map_comp, w.leg_map]
  ret := F.map w.ret
  leg_ret := by rw [← F.map_comp, w.leg_ret, F.map_id]
  cofinal j := by
    obtain ⟨k, u, v, hk⟩ := w.cofinal j
    refine ⟨k, u, v, ?_⟩
    dsimp only [Functor.comp_map]
    rw [show M.map u = M.map v ≫ w.ret ≫ w.leg j from hk, F.map_comp, F.map_comp]

/-- Cofinality of a `Witness` read inside `Over n`. -/
private theorem cofinal_over [IsCofiltered J] (w : Witness M X n) (j : Over n) :
    ∃ (k : Over n) (u : k ⟶ j), M.map u.left = M.map k.hom ≫ w.ret ≫ w.leg j.left := by
  obtain ⟨k, u, v, hk⟩ := w.cofinal j.left
  have he := IsCofiltered.eq_condition (u ≫ j.hom) v
  refine ⟨Over.mk (IsCofiltered.eqHom (u ≫ j.hom) v ≫ u ≫ j.hom),
    Over.homMk (IsCofiltered.eqHom (u ≫ j.hom) v ≫ u) (by simp), ?_⟩
  have hh : (Over.mk (IsCofiltered.eqHom (u ≫ j.hom) v ≫ u ≫ j.hom)).hom =
      IsCofiltered.eqHom (u ≫ j.hom) v ≫ v := by
    simpa only [Over.mk_hom, Category.assoc] using he
  rw [hh]
  simp only [Over.homMk_left, Functor.map_comp, Category.assoc, hk]

/-- The cone on the diagram restricted to the indices `j ≥ n`, with apex the value `X`. -/
private def restrictedCone (w : Witness M X n) : Cone (Over.forget n ⋙ M) where
  pt := X
  π := { app := fun j => w.leg j.left
         naturality := fun j j' u => by
          dsimp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_map,
            Over.forget_map]
          rw [Category.id_comp, w.leg_map u.left] }

/-- The cofinality clause of a `Witness`, read on the indices `j ≥ n`. -/
private theorem cofinal_restricted [IsCofiltered J] (w : Witness M X n) (j : Over n) :
    ∃ (k : Over n) (u : k ⟶ j) (v : k ⟶ Over.mk (𝟙 n)),
      (Over.forget n ⋙ M).map u = (Over.forget n ⋙ M).map v ≫ w.ret ≫ w.leg j.left := by
  obtain ⟨k, u, hk⟩ := w.cofinal_over j
  exact ⟨k, u, Over.homMk k.hom (by simp), hk⟩

/-- The restricted cone is a limit cone: uniqueness comes from the retraction at `n`, and the
factorisation from the cofinality clause. -/
private noncomputable def isLimitRestrictedCone [IsCofiltered J] (w : Witness M X n) :
    IsLimit (restrictedCone w) :=
  isLimitOfSplitLegOfCofinal (k₀ := Over.mk (𝟙 n)) _ w.ret w.leg_ret w.cofinal_restricted

/-- Conversely, elementwise bijectivity of `Hom(X, W) ⟶ colim_j Hom(M_j, W)` rebuilds the
essential-constancy datum, with the given morphism as retraction. -/
private theorem exists_witness_of_hom_bijective [IsCofiltered J] {M : J ⥤ D} {X : D} {n : J}
    (s : M.obj n ⟶ X)
    (hsurj : ∀ (W : D) (j : J) (g : M.obj j ⟶ W), ∃ (h : X ⟶ W) (k : J) (u : k ⟶ j) (v : k ⟶ n),
      M.map u ≫ g = M.map v ≫ s ≫ h)
    (hinj : ∀ (W : D) (h h' : X ⟶ W) (k : J) (u v : k ⟶ n),
      M.map u ≫ s ≫ h = M.map v ≫ s ≫ h' → h = h') :
    ∃ w : Witness M X n, w.ret = s := by
  have hex : ∀ j : J, ∃ (h : X ⟶ M.obj j) (k : J) (u : k ⟶ j) (v : k ⟶ n),
      M.map u = M.map v ≫ s ≫ h := by
    intro j
    obtain ⟨h, k, u, v, hh⟩ := hsurj (M.obj j) j (𝟙 _)
    exact ⟨h, k, u, v, by simpa using hh⟩
  choose leg k u v hleg using hex
  have uniq : ∀ (j : J) (h h' : X ⟶ M.obj j),
      (∃ (k' : J) (u' : k' ⟶ j) (v' : k' ⟶ n), M.map u' = M.map v' ≫ s ≫ h) →
      (∃ (k' : J) (u' : k' ⟶ j) (v' : k' ⟶ n), M.map u' = M.map v' ≫ s ≫ h') → h = h' := by
    rintro j h h' ⟨k₁, u₁, v₁, h₁⟩ ⟨k₂, u₂, v₂, h₂⟩
    obtain ⟨e, w₀, hw₀⟩ : ∃ (e : J) (w₀ : e ⟶ IsCofiltered.min k₁ k₂),
        w₀ ≫ IsCofiltered.minToLeft k₁ k₂ ≫ u₁ = w₀ ≫ IsCofiltered.minToRight k₁ k₂ ≫ u₂ :=
      IsCofilteredOrEmpty.cone_maps _ _
    refine hinj _ h h' e (w₀ ≫ IsCofiltered.minToLeft k₁ k₂ ≫ v₁)
      (w₀ ≫ IsCofiltered.minToRight k₁ k₂ ≫ v₂) ?_
    have key : M.map (w₀ ≫ IsCofiltered.minToLeft k₁ k₂ ≫ u₁)
        = M.map (w₀ ≫ IsCofiltered.minToRight k₁ k₂ ≫ u₂) := by rw [hw₀]
    simp only [Functor.map_comp] at key
    rw [h₁, h₂] at key
    simp only [Functor.map_comp, Category.assoc] at key ⊢
    exact key
  refine ⟨{ leg := leg
            leg_map := ?_
            ret := s
            leg_ret := ?_
            cofinal := ?_ }, rfl⟩
  · intro j j' w'
    refine uniq j (leg j' ≫ M.map w') (leg j) ⟨k j', u j' ≫ w', v j', ?_⟩ ⟨k j, u j, v j, hleg j⟩
    rw [M.map_comp, hleg j', Category.assoc, Category.assoc]
  · refine hinj _ (leg n ≫ s) (𝟙 X) _ (v n) (u n) ?_
    rw [Category.comp_id, hleg n]
    simp only [Category.assoc]
  · intro j
    exact ⟨k j, u j, v j, hleg j⟩

end Witness

end Witnesses

namespace Pretriangulated

/-! ## Stacks 0G39: splitting off the constant part

### Split complements of a retract in a preadditive category -/

section Preadditive

variable {C : Type*} [Category C] [Preadditive C] {A X Z : C} {r : A ⟶ X} {s : X ⟶ A}
  {i : Z ⟶ A} {e : A ⟶ Z}

/-- A morphism into `A` that the retraction `r` kills is fixed by the complementary idempotent
`e ≫ i = 𝟙 A - r ≫ s`. -/
private lemma comp_complement (hei : e ≫ i = 𝟙 A - r ≫ s) {W : C} {g : W ⟶ A}
    (hg : g ≫ r = 0) : g ≫ e ≫ i = g := by
  rw [hei, Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hg, zero_comp, sub_zero]

/-- Dually, a morphism out of `A` that kills the section `s` is fixed by the complementary
idempotent `e ≫ i = 𝟙 A - r ≫ s`. -/
private lemma complement_comp (hei : e ≫ i = 𝟙 A - r ≫ s) {W : C} {g : A ⟶ W}
    (hg : s ≫ g = 0) : (e ≫ i) ≫ g = g := by
  rw [hei, Preadditive.sub_comp, Category.id_comp, Category.assoc, hg, comp_zero, sub_zero]

/-- The inclusion of the complement is killed by the retraction. -/
private lemma complement_comp_retraction (hsr : s ≫ r = 𝟙 X) (hie : i ≫ e = 𝟙 Z)
    (hei : e ≫ i = 𝟙 A - r ≫ s) : i ≫ r = 0 := by
  have h : (e ≫ i) ≫ r = 0 := by
    rw [hei, Preadditive.sub_comp, Category.id_comp, Category.assoc, hsr, Category.comp_id,
      sub_self]
  calc i ≫ r = i ≫ (e ≫ i) ≫ r := by
        rw [← Category.assoc, ← Category.assoc, hie, Category.id_comp]
    _ = 0 := by rw [h, comp_zero]

/-- The section of the retract is killed by the projection to the complement. -/
private lemma section_comp_projection (hsr : s ≫ r = 𝟙 X) (hie : i ≫ e = 𝟙 Z)
    (hei : e ≫ i = 𝟙 A - r ≫ s) : s ≫ e = 0 := by
  have h : s ≫ e ≫ i = 0 := by
    rw [hei, Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hsr, Category.id_comp,
      sub_self]
  calc s ≫ e = (s ≫ e ≫ i) ≫ e := by
        rw [Category.assoc, Category.assoc, hie, Category.comp_id]
    _ = 0 := by rw [h, zero_comp]

/-- A retract `s, r` of `X` in `A` whose complementary idempotent splits as `i, e` exhibits `A`
as the biproduct of `X` and the complement `Z`. -/
private noncomputable def isoBiprodOfComplement [HasBinaryBiproduct X Z] (r : A ⟶ X) (s : X ⟶ A)
    (i : Z ⟶ A) (e : A ⟶ Z) (hsr : s ≫ r = 𝟙 X) (hie : i ≫ e = 𝟙 Z)
    (hei : e ≫ i = 𝟙 A - r ≫ s) : A ≅ X ⊞ Z :=
  biprod.uniqueUpToIso X Z <| isBinaryBilimitOfTotal
    { pt := A
      fst := r
      snd := e
      inl := s
      inr := i
      inl_fst := hsr
      inl_snd := section_comp_projection hsr hie hei
      inr_fst := complement_comp_retraction hsr hie hei
      inr_snd := hie }
    (by change r ≫ s + e ≫ i = 𝟙 A; rw [hei]; abel)

/-- Conversely, a decomposition `A ≅ X ⊞ Z` is a retract of `X` and a retract of `Z` in `A`
satisfying the total identity. -/
private lemma exists_total_of_iso_biprod [HasBinaryBiproduct X Z] (ε : A ≅ X ⊞ Z) :
    ∃ (r : A ⟶ X) (s : X ⟶ A) (e : A ⟶ Z) (i : Z ⟶ A),
      s ≫ r = 𝟙 X ∧ i ≫ e = 𝟙 Z ∧ r ≫ s + e ≫ i = 𝟙 A := by
  refine ⟨ε.hom ≫ biprod.fst, biprod.inl ≫ ε.inv, ε.hom ≫ biprod.snd, biprod.inr ≫ ε.inv,
    by simp, by simp, ?_⟩
  rw [Category.assoc, Category.assoc, ← Category.assoc biprod.fst, ← Category.assoc biprod.snd,
    ← Preadditive.comp_add, ← Preadditive.add_comp, biprod.total, Category.id_comp, ε.hom_inv_id]

end Preadditive

/-! ### Transition morphisms of a decomposition of diagrams -/

section Decomposition

variable {K : Type*} [Category K] {C : Type*} [Category C] [Preadditive C] {F G Z : K ⥤ C}

/-- **The observation both directions of Stacks 0G39 rest on.** Let a diagram `F` decompose as
`G ⊞ Z`, recorded by structure morphisms `R, S, π, ι` with `ι ≫ π = 𝟙 Z` and the total identity
`R ≫ S + π ≫ ι = 𝟙 F`. Then a transition morphism of the complement `Z` vanishes exactly when
the corresponding transition morphism of `F` factors through the summand `G`.

Naturality expands `F.map u` as `R_{j'} ≫ G.map u ≫ S_j + π_{j'} ≫ Z.map u ≫ ι_j`; the retraction
`ι ≫ π = 𝟙 Z` is what makes the second summand detect `Z.map u`. -/
private lemma complement_map_eq_zero_iff (R : F ⟶ G) (S : G ⟶ F) (π : F ⟶ Z) (ι : Z ⟶ F)
    (hιπ : ι ≫ π = 𝟙 Z) (htotal : R ≫ S + π ≫ ι = 𝟙 F) {j' j : K} (u : j' ⟶ j) :
    Z.map u = 0 ↔ F.map u = R.app j' ≫ G.map u ≫ S.app j := by
  have key : F.map u = R.app j' ≫ G.map u ≫ S.app j + π.app j' ≫ Z.map u ≫ ι.app j := by
    have h : R.app j' ≫ S.app j' + π.app j' ≫ ι.app j' = 𝟙 (F.obj j') := by
      simpa using NatTrans.congr_app htotal j'
    calc F.map u = (R.app j' ≫ S.app j' + π.app j' ≫ ι.app j') ≫ F.map u := by
          rw [h, Category.id_comp]
      _ = R.app j' ≫ S.app j' ≫ F.map u + π.app j' ≫ ι.app j' ≫ F.map u := by
          simp only [Preadditive.add_comp, Category.assoc]
      _ = _ := by rw [← S.naturality u, ← ι.naturality u]
  refine ⟨fun hu => by rw [key, hu, zero_comp, comp_zero, add_zero], fun hu => ?_⟩
  have h1 : ι.app j' ≫ π.app j' = 𝟙 (Z.obj j') := by simpa using NatTrans.congr_app hιπ j'
  have h2 : ι.app j ≫ π.app j = 𝟙 (Z.obj j) := by simpa using NatTrans.congr_app hιπ j
  have h0 : π.app j' ≫ Z.map u ≫ ι.app j = 0 := by
    refine add_left_cancel (a := R.app j' ≫ G.map u ≫ S.app j) ?_
    rw [add_zero]
    exact key.symm.trans hu
  calc Z.map u = (ι.app j' ≫ π.app j') ≫ Z.map u ≫ (ι.app j ≫ π.app j) := by
        rw [h1, h2, Category.id_comp, Category.comp_id]
    _ = ι.app j' ≫ (π.app j' ≫ Z.map u ≫ ι.app j) ≫ π.app j := by simp only [Category.assoc]
    _ = 0 := by rw [h0, zero_comp, comp_zero]

end Decomposition

/-! ### Weak idempotent completeness of a pre-triangulated category -/

section Idempotents

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- In a pre-triangulated category a morphism `r` with a section `s` has a complement: the
complementary idempotent `𝟙 A - r ≫ s` splits. The complement is the first term `Z` of a
distinguished triangle `Z ⟶ A ⟶ X ⟶ Z[1]` given by TR1.

This is Stacks 05QT for the retraction at hand, read as a statement about idempotents. The
section forces the connecting morphism to vanish and `𝟙 A - r ≫ s` composes to zero with `r`, so
it factors through `Z ⟶ A` by the exactness of `Hom(-, ·)` on the triangle
(`CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₂`); that the factorisation is a
splitting is then Mathlib's `CategoryTheory.Pretriangulated.binaryBiproductData`. -/
private lemma exists_complement_of_section {A X : D} (r : A ⟶ X) (s : X ⟶ A)
    (hsr : s ≫ r = 𝟙 X) :
    ∃ (Z : D) (i : Z ⟶ A) (e : A ⟶ Z), i ≫ e = 𝟙 Z ∧ e ≫ i = 𝟙 A - r ≫ s := by
  obtain ⟨Z, i, h, hT⟩ := distinguished_cocone_triangle₁ r
  have hrh : r ≫ h = 0 := comp_distTriang_mor_zero₂₃ _ hT
  have hh : h = 0 := by rw [← Category.id_comp h, ← hsr, Category.assoc, hrh, comp_zero]
  obtain ⟨e, he⟩ := Triangle.coyoneda_exact₂ _ hT (𝟙 A - r ≫ s) (by simp [hsr])
  rw [Triangle.mk_mor₁] at he
  exact ⟨Z, i, e, (binaryBiproductData _ hT hh s hsr e
    (by change e ≫ i + r ≫ s = 𝟙 A; rw [← he]; abel)).bicone.inl_fst, he.symm⟩

/-- **The hard part of Stacks 0G39.** A retract of a diagram in a pre-triangulated category
splits off as a direct summand, *functorially*: if `S : G ⟶ F` has a retraction `R`, then
`F ≅ G ⊞ Z` for a diagram `Z`, and a transition morphism of `Z` vanishes as soon as the
corresponding transition morphism of `F` factors through the retract.

The complement is `j ↦ Z_j` for a pointwise complement `Z_j` from `exists_complement_of_section`,
with transition morphisms `i_j ≫ F.map u ≫ e_{j'}`; that this is a functor and that `i` and `e`
are natural are the two halves of the absorption principle `comp_complement`,
`complement_comp`. -/
private lemma exists_iso_biprod_of_natTrans_section {K : Type*} [Category K] {F G : K ⥤ D}
    (R : F ⟶ G) (S : G ⟶ F) (hSR : S ≫ R = 𝟙 G) :
    ∃ (Z : K ⥤ D) (_ : F ≅ G ⊞ Z), ∀ ⦃j' j : K⦄ (u : j' ⟶ j),
      F.map u = R.app j' ≫ G.map u ≫ S.app j → Z.map u = 0 := by
  have hSR' : ∀ j : K, S.app j ≫ R.app j = 𝟙 (G.obj j) := fun j => by
    simpa using NatTrans.congr_app hSR j
  choose Zo ii ee hie hei using
    fun j : K => exists_complement_of_section (R.app j) (S.app j) (hSR' j)
  have hir : ∀ j : K, ii j ≫ R.app j = 0 := fun j =>
    complement_comp_retraction (hSR' j) (hie j) (hei j)
  have hse : ∀ j : K, S.app j ≫ ee j = 0 := fun j =>
    section_comp_projection (hSR' j) (hie j) (hei j)
  have habs : ∀ {j j' : K} (u : j ⟶ j'), ii j ≫ F.map u ≫ ee j' ≫ ii j' = ii j ≫ F.map u := by
    intro j j' u
    rw [← Category.assoc]
    exact comp_complement (hei j') (by
      rw [Category.assoc, R.naturality u, ← Category.assoc, hir j, zero_comp])
  have habs' : ∀ {j j' : K} (u : j ⟶ j'),
      (ee j ≫ ii j) ≫ F.map u ≫ ee j' = F.map u ≫ ee j' := fun {j j'} u =>
    complement_comp (hei j) (by
      rw [← Category.assoc, ← S.naturality u, Category.assoc, hse j', comp_zero])
  let Z : K ⥤ D :=
    { obj := Zo
      map := fun {j j'} u => ii j ≫ F.map u ≫ ee j'
      map_id := fun j => by simp [hie j]
      map_comp := fun {j₁ j₂ j₃} u v => by
        rw [F.map_comp]
        calc ii j₁ ≫ (F.map u ≫ F.map v) ≫ ee j₃
            = (ii j₁ ≫ F.map u ≫ ee j₂ ≫ ii j₂) ≫ F.map v ≫ ee j₃ := by
              rw [habs u]; simp
          _ = (ii j₁ ≫ F.map u ≫ ee j₂) ≫ ii j₂ ≫ F.map v ≫ ee j₃ := by simp }
  let ι : Z ⟶ F :=
    { app := ii
      naturality := fun j j' u => by
        show (ii j ≫ F.map u ≫ ee j') ≫ ii j' = ii j ≫ F.map u
        simp only [Category.assoc]
        exact habs u }
  let π : F ⟶ Z :=
    { app := ee
      naturality := fun j j' u => by
        show F.map u ≫ ee j' = ee j ≫ ii j ≫ F.map u ≫ ee j'
        rw [← Category.assoc (ee j) (ii j), habs' u] }
  have hιπ : ι ≫ π = 𝟙 Z := by
    ext j
    exact hie j
  have hπι : π ≫ ι = 𝟙 F - R ≫ S := by
    ext j
    show ee j ≫ ii j = (𝟙 F - R ≫ S).app j
    rw [NatTrans.app_sub]
    simpa using hei j
  exact ⟨Z, isoBiprodOfComplement R S ι π hSR hιπ hπι,
    fun _ _ u => (complement_map_eq_zero_iff R S π ι hιπ (by rw [hπι]; abel) u).2⟩

end Idempotents

/-! ### Stacks 0G39 -/

section Main

variable {J : Type u} [Category.{v} J] {D : Type u'} [Category.{v'} D]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- A diagram which is a constant diagram plus an essentially zero one is essentially constant
as a pro-object: the legs of the constant summand form a cone, its projections retract them, and
the cofinality clause is `complement_map_eq_zero_iff` read left to right. -/
private lemma isEssentiallyConstant_op_of_iso_const_biprod {K : Type*} [Category K]
    [IsCofiltered K] {F : K ⥤ D} {X : D} {Z : K ⥤ D}
    (ε : F ≅ (Functor.const K).obj X ⊞ Z)
    (hZ : ∀ j : K, ∃ (j' : K) (u : j' ⟶ j), Z.map u = 0) : IsEssentiallyConstantInd F.op := by
  obtain ⟨R, S, π, ι, hSR, hιπ, htotal⟩ := exists_total_of_iso_biprod ε
  obtain ⟨k₀⟩ := IsCofiltered.nonempty (C := K)
  refine Witness.isEssentiallyConstant
    { leg := S.app
      leg_map := fun u => (Cone.mk X S).w u
      ret := R.app k₀
      leg_ret := NatTrans.congr_app hSR k₀
      cofinal := fun j => ?_ }
  obtain ⟨j', u, hu⟩ := hZ j
  refine ⟨IsCofiltered.min j' k₀, IsCofiltered.minToLeft j' k₀ ≫ u,
    IsCofiltered.minToRight j' k₀, ?_⟩
  have h0 : Z.map (IsCofiltered.minToLeft j' k₀ ≫ u) = 0 := by rw [Z.map_comp, hu, comp_zero]
  rw [(complement_map_eq_zero_iff R S π ι hιπ htotal _).1 h0]
  simp [← Category.assoc, R.naturality]

/-- The forward direction of Stacks 0G39: a `Witness` for essential constancy of the pro-object
`(A_j)` splits the restricted system `Over.forget i ⋙ A` as the constant system on the value
together with an essentially zero system.

The retract of the restricted system is `S.app j = w.leg j.left` with retraction
`R.app j = A.map j.hom ≫ w.ret`, and the vanishing clause is what the cofinality clause of the
`Witness` feeds to `exists_iso_biprod_of_natTrans_section`, after equalizing `u ≫ j.hom` with `v`
so that the transition morphism lives over `i`. -/
private lemma exists_iso_const_biprod_of_witness [IsCofiltered J] (A : J ⥤ D) {X : D} {i : J}
    (w : Witness A X i) :
    ∃ (Z : Over i ⥤ D) (_ : Over.forget i ⋙ A ≅ (Functor.const (Over i)).obj X ⊞ Z),
      ∀ j : Over i, ∃ (j' : Over i) (u : j' ⟶ j), Z.map u = 0 := by
  let F : Over i ⥤ D := Over.forget i ⋙ A
  let G : Over i ⥤ D := (Functor.const (Over i)).obj X
  let R : F ⟶ G :=
    { app := fun j => A.map j.hom ≫ w.ret
      naturality := fun j j' u => by
        show A.map u.left ≫ A.map j'.hom ≫ w.ret = (A.map j.hom ≫ w.ret) ≫ 𝟙 X
        rw [Category.comp_id, ← Category.assoc, ← A.map_comp, Over.w] }
  let S : G ⟶ F :=
    { app := fun j => w.leg j.left
      naturality := fun j j' u => by
        show 𝟙 X ≫ w.leg j'.left = w.leg j.left ≫ A.map u.left
        rw [Category.id_comp, w.leg_map u.left] }
  have hSR : S ≫ R = 𝟙 G := by
    ext j
    show w.leg j.left ≫ A.map j.hom ≫ w.ret = 𝟙 X
    rw [← Category.assoc, w.leg_map, w.leg_ret]
  obtain ⟨Z, ε, hvan⟩ := exists_iso_biprod_of_natTrans_section R S hSR
  refine ⟨Z, ε, fun j => ?_⟩
  obtain ⟨k, u, v, huv⟩ := w.cofinal j.left
  obtain ⟨m, p, hp⟩ := IsCofilteredOrEmpty.cone_maps (u ≫ j.hom) v
  refine ⟨Over.mk (p ≫ v), Over.homMk (p ≫ u) (by simpa using hp), hvan _ ?_⟩
  show A.map (p ≫ u) = (A.map (p ≫ v) ≫ w.ret) ≫ 𝟙 X ≫ w.leg j.left
  rw [A.map_comp, A.map_comp, huv, Category.id_comp]
  simp only [Category.assoc]

/-- **Stacks 0G39**. An inverse system `A : J ⥤ 𝒟` in a pre-triangulated category, indexed by a
cofiltered category `J`, is essentially constant as a pro-object (Stacks 05PU for `A.op`) if and
only if there are an index `i`, an object `X` and an inverse system `Z : Over i ⥤ 𝒟` on the
indices `j ≥ i` such that

* `A_j ≅ X ⊞ Z_j` naturally in `j ≥ i` — so the transition morphisms respect the decomposition
  and are the identity on `X` — and
* for every `j ≥ i` there are `j' ≥ j` and a transition morphism `Z_{j'} ⟶ Z_j` equal to zero.

The value of the essentially constant system is then `X`. -/
@[stacks 0G39]
public theorem isEssentiallyConstant_op_iff_exists_iso_const_biprod [IsCofiltered J] (A : J ⥤ D) :
    IsEssentiallyConstantInd A.op ↔
      ∃ (i : J) (X : D) (Z : Over i ⥤ D)
        (_ : Over.forget i ⋙ A ≅ (Functor.const (Over i)).obj X ⊞ Z),
        ∀ j : Over i, ∃ (j' : Over i) (u : j' ⟶ j), Z.map u = 0 := by
  refine ⟨fun h => ?_, fun ⟨i, X, Z, ε, hZ⟩ => ?_⟩
  · obtain ⟨X, i, ⟨w⟩⟩ := Witness.exists_witness h
    obtain ⟨Z, ε, hZ⟩ := exists_iso_const_biprod_of_witness A w
    exact ⟨i, X, Z, ε, hZ⟩
  · exact essentiallyConstant_of_comp_final (Over.forget i).op A.op
      (isEssentiallyConstant_op_of_iso_const_biprod ε hZ)

end Main

/-! ## Stacks 0G3A: two out of three for a system of distinguished triangles

### Commutative squares of a morphism of triangles -/

section Squares

variable {D : Type u'} [Category.{v'} D] [HasShift D ℤ]

/-- The connecting morphism of a triangle read through a morphism of triangles whose third
component is split by an idempotent `rC ≫ lC` of the target's third term: this is the
compatibility that makes the value triangle of an inverse system receive a morphism from one of
its terms. -/
private theorem mor₃_comp_shift_map_of_idem {X Y : Triangle D} (ψ : X ⟶ Y) {A C : D}
    (rA : Y.obj₁ ⟶ A) (rC : Y.obj₃ ⟶ C) (lC : C ⟶ Y.obj₃)
    (h : ψ.hom₃ ≫ rC ≫ lC = ψ.hom₃) :
    X.mor₃ ≫ (ψ.hom₁ ≫ rA)⟦(1 : ℤ)⟧' = (ψ.hom₃ ≫ rC) ≫ lC ≫ Y.mor₃ ≫ rA⟦(1 : ℤ)⟧' :=
  calc X.mor₃ ≫ (ψ.hom₁ ≫ rA)⟦(1 : ℤ)⟧'
      = X.mor₃ ≫ ψ.hom₁⟦(1 : ℤ)⟧' ≫ rA⟦(1 : ℤ)⟧' := by rw [Functor.map_comp]
    _ = ψ.hom₃ ≫ Y.mor₃ ≫ rA⟦(1 : ℤ)⟧' := ψ.comm₃_assoc _
    _ = (ψ.hom₃ ≫ rC ≫ lC) ≫ Y.mor₃ ≫ rA⟦(1 : ℤ)⟧' := by rw [h]
    _ = (ψ.hom₃ ≫ rC) ≫ lC ≫ Y.mor₃ ≫ rA⟦(1 : ℤ)⟧' := by simp only [Category.assoc]

end Squares

section Triangles

variable {J : Type u} [Category.{v} J] {D : Type u'} [Category.{v'} D]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Exactness of `Hom(-, X)` at the FIRST term of a distinguished triangle: a morphism out of
`T.obj₁` whose shift kills the connecting morphism factors through `T.mor₁`.

The missing sibling of `CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂` and
`...yoneda_exact₃`, stated in their shape (`f = T.mor₁ ≫ g`, `X` implicit) so that it can be read
against them; Mathlib has the contravariant sequence only from the second term on, and the
covariant one in all three spots (`Triangle.coyoneda_exact₁`). -/
private theorem yoneda_exact₁ {T : Triangle D} (hT : T ∈ distTriang D) {X : D}
    (f : T.obj₁ ⟶ X) (hf : T.mor₃ ≫ f⟦(1 : ℤ)⟧' = 0) : ∃ g : T.obj₂ ⟶ X, f = T.mor₁ ≫ g := by
  have hrot : Triangle.mk T.mor₂ T.mor₃ (-(T.mor₁⟦(1 : ℤ)⟧')) ∈ distTriang D :=
    rot_of_distTriang _ hT
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ hrot (f⟦(1 : ℤ)⟧') hf
  refine ⟨(shiftFunctor D (1 : ℤ)).preimage (-g), (shiftFunctor D (1 : ℤ)).map_injective ?_⟩
  rw [Functor.map_comp, Functor.map_preimage, hg]
  simp only [Triangle.mk_mor₃, Preadditive.comp_neg, Preadditive.neg_comp]

/-- **The five lemma, surjectivity half.** For an inverse system of distinguished triangles whose
systems of first and third terms are essentially constant with values `S.obj₁`, `S.obj₃` at a
common index `n`, and a morphism of triangles `φ : T_n ⟶ S` inducing the two retractions, the
comparison `Hom(S.obj₂, W) ⟶ colim_j Hom(B_j, W)` is surjective. -/
private theorem key_surj [IsCofiltered J] (T : J ⥤ Triangle D)
    (hT : ∀ j, T.obj j ∈ distTriang D) {n : J} (S : Triangle D) (hS : S ∈ distTriang D)
    (wA : Witness (T ⋙ Triangle.π₁) S.obj₁ n) (wC : Witness (T ⋙ Triangle.π₃) S.obj₃ n)
    (φ : T.obj n ⟶ S) (hφ₁ : φ.hom₁ = wA.ret) (hφ₃ : φ.hom₃ = wC.ret) :
    ∀ (W : D) (j : J) (g : (T.obj j).obj₂ ⟶ W),
      ∃ (h : S.obj₂ ⟶ W) (k : J) (u : k ⟶ j) (v : k ⟶ n),
        (T.map u).hom₂ ≫ g = (T.map v).hom₂ ≫ φ.hom₂ ≫ h := by
  intro W j g
  obtain ⟨h₁, k₁, u₁, v₁, hh₁⟩ := wA.surj W j ((T.obj j).mor₁ ≫ g)
  -- Read the retraction as `φ.hom₁` throughout: the two are equal, and `φ.hom₁` is the
  -- component of a morphism of triangles, so the commutation lemmas apply to it directly.
  have hh₁' : (T.map u₁).hom₁ ≫ (T.obj j).mor₁ ≫ g = (T.map v₁).hom₁ ≫ φ.hom₁ ≫ h₁ := by
    rw [hφ₁]; exact hh₁
  have hh₁s : (T.map u₁).hom₁⟦(1 : ℤ)⟧' ≫ (T.obj j).mor₁⟦(1 : ℤ)⟧' ≫ g⟦(1 : ℤ)⟧'
      = (T.map v₁).hom₁⟦(1 : ℤ)⟧' ≫ φ.hom₁⟦(1 : ℤ)⟧' ≫ h₁⟦(1 : ℤ)⟧' := by
    simpa only [Functor.map_comp] using congrArg (shiftFunctor D (1 : ℤ)).map hh₁'
  -- The connecting morphism of `S` kills `h₁`.
  have hδ : S.mor₃ ≫ h₁⟦(1 : ℤ)⟧' = 0 := by
    have step : (T.map v₁).hom₃ ≫ wC.ret ≫ S.mor₃ ≫ h₁⟦(1 : ℤ)⟧' = 0 :=
      calc (T.map v₁).hom₃ ≫ wC.ret ≫ S.mor₃ ≫ h₁⟦(1 : ℤ)⟧'
          = (T.map v₁).hom₃ ≫ φ.hom₃ ≫ S.mor₃ ≫ h₁⟦(1 : ℤ)⟧' := by rw [hφ₃]
        _ = (T.obj k₁).mor₃ ≫ (T.map v₁).hom₁⟦(1 : ℤ)⟧' ≫ φ.hom₁⟦(1 : ℤ)⟧' ≫ h₁⟦(1 : ℤ)⟧' := by
              rw [← φ.comm₃_assoc, ← (T.map v₁).comm₃_assoc]
        _ = (T.obj k₁).mor₃ ≫ (T.map u₁).hom₁⟦(1 : ℤ)⟧' ≫ (T.obj j).mor₁⟦(1 : ℤ)⟧' ≫ g⟦(1 : ℤ)⟧'
              := by rw [hh₁s]
        _ = (T.map u₁).hom₃ ≫ (T.obj j).mor₃ ≫ (T.obj j).mor₁⟦(1 : ℤ)⟧' ≫ g⟦(1 : ℤ)⟧' :=
              (T.map u₁).comm₃_assoc _
        _ = 0 := by
              rw [← Category.assoc ((T.obj j).mor₃), comp_distTriang_mor_zero₃₁ _ (hT j),
                zero_comp, comp_zero]
    exact wC.inj v₁ v₁ (by rwa [comp_zero, comp_zero])
  -- Hence `h₁` lifts along `S.mor₁` to some `x : S.obj₂ ⟶ W`.
  obtain ⟨x, hx⟩ := yoneda_exact₁ hS h₁ hδ
  -- `x` answers the question after correction by a morphism factoring through `S.obj₃`.
  have hζ : (T.obj k₁).mor₁ ≫ ((T.map u₁).hom₂ ≫ g - (T.map v₁).hom₂ ≫ φ.hom₂ ≫ x) = 0 := by
    rw [Preadditive.comp_sub, sub_eq_zero]
    calc (T.obj k₁).mor₁ ≫ (T.map u₁).hom₂ ≫ g
        = (T.map u₁).hom₁ ≫ (T.obj j).mor₁ ≫ g := (T.map u₁).comm₁_assoc g
      _ = (T.map v₁).hom₁ ≫ φ.hom₁ ≫ h₁ := hh₁'
      _ = (T.map v₁).hom₁ ≫ φ.hom₁ ≫ S.mor₁ ≫ x := by rw [← hx]
      _ = (T.map v₁).hom₁ ≫ (T.obj n).mor₁ ≫ φ.hom₂ ≫ x := by rw [← φ.comm₁_assoc]
      _ = (T.obj k₁).mor₁ ≫ (T.map v₁).hom₂ ≫ φ.hom₂ ≫ x := ((T.map v₁).comm₁_assoc _).symm
  obtain ⟨ζ, hζ'⟩ := Triangle.yoneda_exact₂ _ (hT k₁) _ hζ
  obtain ⟨h₂, k₂, u₂, v₂, hh₂⟩ := wC.surj W k₁ ζ
  have hh₂' : (T.map u₂).hom₃ ≫ ζ = (T.map v₂).hom₃ ≫ wC.ret ≫ h₂ := hh₂
  obtain ⟨e, p, hp⟩ : ∃ (e : J) (p : e ⟶ k₁),
      (T.map p).hom₃ ≫ ζ = (T.map (p ≫ v₁)).hom₃ ≫ wC.ret ≫ h₂ := by
    obtain ⟨e, w₀, hw₀⟩ := IsCofilteredOrEmpty.cone_maps (u₂ ≫ v₁) v₂
    refine ⟨e, w₀ ≫ u₂, ?_⟩
    calc (T.map (w₀ ≫ u₂)).hom₃ ≫ ζ
        = (T.map w₀).hom₃ ≫ (T.map u₂).hom₃ ≫ ζ := by rw [T.map_comp, comp_hom₃_assoc]
      _ = (T.map w₀).hom₃ ≫ (T.map v₂).hom₃ ≫ wC.ret ≫ h₂ := by rw [hh₂']
      _ = (T.map (w₀ ≫ v₂)).hom₃ ≫ wC.ret ≫ h₂ := by rw [T.map_comp, comp_hom₃_assoc]
      _ = (T.map ((w₀ ≫ u₂) ≫ v₁)).hom₃ ≫ wC.ret ≫ h₂ := by rw [Category.assoc, hw₀]
  refine ⟨x + S.mor₂ ≫ h₂, e, p ≫ u₁, p ≫ v₁, ?_⟩
  rw [Preadditive.comp_add, Preadditive.comp_add, ← sub_eq_iff_eq_add']
  calc (T.map (p ≫ u₁)).hom₂ ≫ g - (T.map (p ≫ v₁)).hom₂ ≫ φ.hom₂ ≫ x
      = (T.map p).hom₂ ≫ ((T.map u₁).hom₂ ≫ g - (T.map v₁).hom₂ ≫ φ.hom₂ ≫ x) := by
        rw [Preadditive.comp_sub, T.map_comp, T.map_comp, comp_hom₂_assoc, comp_hom₂_assoc]
    _ = (T.map p).hom₂ ≫ (T.obj k₁).mor₂ ≫ ζ := by rw [hζ']
    _ = (T.obj e).mor₂ ≫ (T.map p).hom₃ ≫ ζ := ((T.map p).comm₂_assoc ζ).symm
    _ = (T.obj e).mor₂ ≫ (T.map (p ≫ v₁)).hom₃ ≫ wC.ret ≫ h₂ := by rw [hp]
    _ = (T.map (p ≫ v₁)).hom₂ ≫ (T.obj n).mor₂ ≫ wC.ret ≫ h₂ := (T.map (p ≫ v₁)).comm₂_assoc _
    _ = (T.map (p ≫ v₁)).hom₂ ≫ φ.hom₂ ≫ S.mor₂ ≫ h₂ := by rw [← hφ₃, ← φ.comm₂_assoc]

/-- **The five lemma, injectivity half, at zero.** In the situation of `key_surj`, a morphism out
of `S.obj₂` which dies on some `B_k` is zero. -/
private theorem key_zero (T : J ⥤ Triangle D)
    (hT : ∀ j, T.obj j ∈ distTriang D) {n : J} (S : Triangle D) (hS : S ∈ distTriang D)
    (wA : Witness (T ⋙ Triangle.π₁) S.obj₁ n) (wC : Witness (T ⋙ Triangle.π₃) S.obj₃ n)
    (φ : T.obj n ⟶ S) (hφ₁ : φ.hom₁ = wA.ret) (hφ₃ : φ.hom₃ = wC.ret)
    {W : D} (h : S.obj₂ ⟶ W) {k : J} (q : k ⟶ n)
    (hq : (T.map q).hom₂ ≫ φ.hom₂ ≫ h = 0) : h = 0 := by
  have ha : S.mor₁ ≫ h = 0 := by
    have key : (T.map q).hom₁ ≫ wA.ret ≫ S.mor₁ ≫ h = 0 :=
      calc (T.map q).hom₁ ≫ wA.ret ≫ S.mor₁ ≫ h
          = (T.map q).hom₁ ≫ φ.hom₁ ≫ S.mor₁ ≫ h := by rw [hφ₁]
        _ = (T.map q).hom₁ ≫ (T.obj n).mor₁ ≫ φ.hom₂ ≫ h := by rw [← φ.comm₁_assoc]
        _ = (T.obj k).mor₁ ≫ (T.map q).hom₂ ≫ φ.hom₂ ≫ h := ((T.map q).comm₁_assoc _).symm
        _ = 0 := by rw [hq, comp_zero]
    exact wA.inj q q (by rwa [comp_zero, comp_zero])
  obtain ⟨y, hy⟩ := Triangle.yoneda_exact₂ _ hS h ha
  have hc : (T.obj k).mor₂ ≫ (T.map q).hom₃ ≫ wC.ret ≫ y = 0 :=
    calc (T.obj k).mor₂ ≫ (T.map q).hom₃ ≫ wC.ret ≫ y
        = (T.map q).hom₂ ≫ (T.obj n).mor₂ ≫ wC.ret ≫ y := (T.map q).comm₂_assoc _
      _ = (T.map q).hom₂ ≫ (T.obj n).mor₂ ≫ φ.hom₃ ≫ y := by rw [hφ₃]
      _ = (T.map q).hom₂ ≫ φ.hom₂ ≫ S.mor₂ ≫ y := by rw [φ.comm₂_assoc]
      _ = (T.map q).hom₂ ≫ φ.hom₂ ≫ h := by rw [hy]
      _ = 0 := hq
  obtain ⟨z, hz⟩ := Triangle.yoneda_exact₃ _ (hT k) ((T.map q).hom₃ ≫ wC.ret ≫ y) hc
  obtain ⟨z', k₃, u₃, v₃, hz'⟩ := (wA.mapFunctor (shiftFunctor D (1 : ℤ))).surj W k z
  have hz'' : (T.map u₃).hom₁⟦(1 : ℤ)⟧' ≫ z
      = (T.map v₃).hom₁⟦(1 : ℤ)⟧' ≫ φ.hom₁⟦(1 : ℤ)⟧' ≫ z' := by rw [hφ₁]; exact hz'
  have hf : y = S.mor₃ ≫ z' := by
    refine wC.inj (u₃ ≫ q) v₃ ?_
    calc (T.map (u₃ ≫ q)).hom₃ ≫ wC.ret ≫ y
        = (T.map u₃).hom₃ ≫ (T.map q).hom₃ ≫ wC.ret ≫ y := by
          rw [T.map_comp, comp_hom₃_assoc]
      _ = (T.map u₃).hom₃ ≫ (T.obj k).mor₃ ≫ z := by rw [hz]
      _ = (T.obj k₃).mor₃ ≫ (T.map u₃).hom₁⟦(1 : ℤ)⟧' ≫ z := ((T.map u₃).comm₃_assoc z).symm
      _ = (T.obj k₃).mor₃ ≫ (T.map v₃).hom₁⟦(1 : ℤ)⟧' ≫ φ.hom₁⟦(1 : ℤ)⟧' ≫ z' := by rw [hz'']
      _ = (T.map v₃).hom₃ ≫ (T.obj n).mor₃ ≫ φ.hom₁⟦(1 : ℤ)⟧' ≫ z' := (T.map v₃).comm₃_assoc _
      _ = (T.map v₃).hom₃ ≫ φ.hom₃ ≫ S.mor₃ ≫ z' := by rw [φ.comm₃_assoc]
      _ = (T.map v₃).hom₃ ≫ wC.ret ≫ S.mor₃ ≫ z' := by rw [hφ₃]
  rw [hy, hf, ← Category.assoc, comp_distTriang_mor_zero₂₃ _ hS, zero_comp]

/-- **The five lemma, injectivity half.** In the situation of `key_surj`, the comparison
`Hom(S.obj₂, W) ⟶ colim_j Hom(B_j, W)` is injective: two morphisms out of `S.obj₂` that agree
after restriction to some `B_k` are equal. -/
private theorem key_inj [IsCofiltered J] (T : J ⥤ Triangle D)
    (hT : ∀ j, T.obj j ∈ distTriang D) {n : J} (S : Triangle D) (hS : S ∈ distTriang D)
    (wA : Witness (T ⋙ Triangle.π₁) S.obj₁ n) (wC : Witness (T ⋙ Triangle.π₃) S.obj₃ n)
    (φ : T.obj n ⟶ S) (hφ₁ : φ.hom₁ = wA.ret) (hφ₃ : φ.hom₃ = wC.ret) :
    ∀ (W : D) (h h' : S.obj₂ ⟶ W) (k : J) (u v : k ⟶ n),
      (T.map u).hom₂ ≫ φ.hom₂ ≫ h = (T.map v).hom₂ ≫ φ.hom₂ ≫ h' → h = h' := by
  intro W h h' k u v huv
  obtain ⟨e, w₀, hw₀⟩ := IsCofilteredOrEmpty.cone_maps u v
  have hzero : (T.map (w₀ ≫ u)).hom₂ ≫ φ.hom₂ ≫ (h - h') = 0 := by
    have e₁ : (T.map (w₀ ≫ u)).hom₂ ≫ φ.hom₂ ≫ h
        = (T.map w₀).hom₂ ≫ (T.map u).hom₂ ≫ φ.hom₂ ≫ h := by
      rw [T.map_comp, comp_hom₂_assoc]
    have e₂ : (T.map (w₀ ≫ u)).hom₂ ≫ φ.hom₂ ≫ h'
        = (T.map w₀).hom₂ ≫ (T.map v).hom₂ ≫ φ.hom₂ ≫ h' := by
      rw [hw₀, T.map_comp, comp_hom₂_assoc]
    rw [Preadditive.comp_sub, Preadditive.comp_sub, e₁, e₂, huv, sub_self]
  have := key_zero T hT S hS wA wC φ hφ₁ hφ₃ (h - h') (w₀ ≫ u) hzero
  rwa [sub_eq_zero] at this

omit [Preadditive D] [HasZeroObject D] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] in
/-- The two systems can be moved to a common index at which the connecting morphism `δ` of the
prospective value triangle is compatible with the two retractions. The idempotent
`C_{n₀} ⟶ C ⟶ C_{n₀}` cofinally splits the transition morphisms, and any index at which it does
so works. -/
private theorem exists_witnesses_compat [IsCofiltered J] (T : J ⥤ Triangle D)
    (h₁ : IsEssentiallyConstantInd (T ⋙ Triangle.π₁).op)
    (h₃ : IsEssentiallyConstantInd (T ⋙ Triangle.π₃).op) :
    ∃ (A C : D) (δ : C ⟶ A⟦(1 : ℤ)⟧) (n : J),
      Nonempty (Σ' (wA : Witness (T ⋙ Triangle.π₁) A n) (wC : Witness (T ⋙ Triangle.π₃) C n),
        (T.obj n).mor₃ ≫ wA.ret⟦(1 : ℤ)⟧' = wC.ret ≫ δ) := by
  obtain ⟨A, nA, ⟨wA₀⟩⟩ := Witness.exists_witness h₁
  obtain ⟨C, nC, ⟨wC₀⟩⟩ := Witness.exists_witness h₃
  obtain ⟨n₀, ⟨wA₁, wC₁⟩⟩ : ∃ n₀ : J,
      Nonempty (Witness (T ⋙ Triangle.π₁) A n₀ × Witness (T ⋙ Triangle.π₃) C n₀) :=
    ⟨IsCofiltered.min nA nC, ⟨wA₀.transport (IsCofiltered.minToLeft nA nC),
      wC₀.transport (IsCofiltered.minToRight nA nC)⟩⟩
  obtain ⟨m, u, v, hu⟩ := wC₁.cofinal n₀
  have hR : wC₁.ret ≫ wC₁.leg n₀ ≫ wC₁.ret ≫ wC₁.leg n₀ = wC₁.ret ≫ wC₁.leg n₀ := by
    rw [← Category.assoc (wC₁.leg n₀), wC₁.leg_ret, Category.id_comp]
  have hidem : (T ⋙ Triangle.π₃).map u ≫ wC₁.ret ≫ wC₁.leg n₀ = (T ⋙ Triangle.π₃).map u := by
    conv_lhs => rw [hu]
    rw [Category.assoc, Category.assoc, hR, ← hu]
  exact ⟨A, C, wC₁.leg n₀ ≫ (T.obj n₀).mor₃ ≫ wA₁.ret⟦(1 : ℤ)⟧', m,
    ⟨wA₁.transport u, wC₁.transport u,
      mor₃_comp_shift_map_of_idem (T.map u) wA₁.ret wC₁.ret (wC₁.leg n₀) hidem⟩⟩

end Triangles

section Main

variable {J : Type u} [Category.{v} J] {D : Type u'} [Category.{v'} D]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- **Stacks 0G3A**. Let `T : J ⥤ Triangle 𝒟` be an inverse system of distinguished triangles
`A_j ⟶ B_j ⟶ C_j ⟶ A_j[1]` in a pre-triangulated category, indexed by a cofiltered category `J`.
If `(A_j)` and `(C_j)` are essentially constant as pro-objects (Stacks 05PU for the opposite
diagrams), then so is `(B_j)`, and there are an index `n`, a distinguished triangle
`S = (A ⟶ B ⟶ C ⟶ A[1])` of the values and a morphism of triangles `φ : T_n ⟶ S` which induces
an isomorphism `lim_{j ≥ n} A_j ⟶ A`, and similarly for `B` and `C`: for each of the three terms
there is a limit cone on the system restricted to the indices `j ≥ n` (the objects of `Over n`)
whose apex is that term of `S` and whose leg at `n` is split by the corresponding component of
`φ`. -/
@[stacks 0G3A]
public theorem isEssentiallyConstant_op_π₂_and_exists_limit_triangle [IsCofiltered J]
    (T : J ⥤ Triangle D) (hT : ∀ j, T.obj j ∈ distTriang D)
    (h₁ : IsEssentiallyConstantInd (T ⋙ Triangle.π₁).op)
    (h₃ : IsEssentiallyConstantInd (T ⋙ Triangle.π₃).op) :
    IsEssentiallyConstantInd (T ⋙ Triangle.π₂).op ∧
      ∃ (n : J) (S : Triangle D) (_ : S ∈ distTriang D) (φ : T.obj n ⟶ S)
        (πA : (Functor.const (Over n)).obj S.obj₁ ⟶ Over.forget n ⋙ T ⋙ Triangle.π₁)
        (πB : (Functor.const (Over n)).obj S.obj₂ ⟶ Over.forget n ⋙ T ⋙ Triangle.π₂)
        (πC : (Functor.const (Over n)).obj S.obj₃ ⟶ Over.forget n ⋙ T ⋙ Triangle.π₃),
        (πA.app (Over.mk (𝟙 n)) ≫ φ.hom₁ = 𝟙 S.obj₁ ∧ Nonempty (IsLimit (Cone.mk _ πA))) ∧
        (πB.app (Over.mk (𝟙 n)) ≫ φ.hom₂ = 𝟙 S.obj₂ ∧ Nonempty (IsLimit (Cone.mk _ πB))) ∧
        (πC.app (Over.mk (𝟙 n)) ≫ φ.hom₃ = 𝟙 S.obj₃ ∧ Nonempty (IsLimit (Cone.mk _ πC))) := by
  obtain ⟨A, C, δ, n, ⟨wA, wC, hcomm⟩⟩ := exists_witnesses_compat T h₁ h₃
  obtain ⟨B, f, g, hS⟩ := distinguished_cocone_triangle₂ δ
  obtain ⟨b, hb₁, hb₂⟩ := complete_distinguished_triangle_morphism₂ (T.obj n)
    (Triangle.mk f g δ) (hT n) hS wA.ret wC.ret hcomm
  obtain ⟨φ, hφ₁, hφ₃⟩ : ∃ φ : T.obj n ⟶ Triangle.mk f g δ,
      φ.hom₁ = wA.ret ∧ φ.hom₃ = wC.ret :=
    ⟨Triangle.homMk _ _ wA.ret b wC.ret hb₁ hb₂ hcomm, rfl, rfl⟩
  obtain ⟨wB, hwB⟩ := Witness.exists_witness_of_hom_bijective (M := T ⋙ Triangle.π₂) φ.hom₂
    (key_surj T hT _ hS wA wC φ hφ₁ hφ₃) (key_inj T hT _ hS wA wC φ hφ₁ hφ₃)
  refine ⟨wB.isEssentiallyConstant, n, Triangle.mk f g δ, hS, φ,
    (Witness.restrictedCone wA).π, (Witness.restrictedCone wB).π, (Witness.restrictedCone wC).π,
    ⟨?_, ⟨Witness.isLimitRestrictedCone wA⟩⟩, ⟨?_, ⟨Witness.isLimitRestrictedCone wB⟩⟩,
    ⟨?_, ⟨Witness.isLimitRestrictedCone wC⟩⟩⟩
  · rw [hφ₁]; exact wA.leg_ret
  · rw [← hwB]; exact wB.leg_ret
  · rw [hφ₃]; exact wC.leg_ret

end Main

/-! ## Stacks 0G3C: a pro-isomorphism from pro-zero third terms -/

variable {J : Type u} [Category.{v} J] {D : Type u'} [Category.{v'} D]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/-- Precomposition with `ψ.hom₂` cancels the ambiguity of a factorization through `T'.mor₁`: if
`T'` is distinguished and `ψ : T ⟶ T'` has vanishing third component, then two morphisms out of
`T'.obj₂` that agree after `T'.mor₁` already agree after `ψ.hom₂`.

Exactness of `Hom(-, X)` at the second term writes the difference `u - v` as `T'.mor₂ ≫ t`, which
`ψ.hom₂` kills because `ψ.hom₂ ≫ T'.mor₂ = T.mor₂ ≫ ψ.hom₃ = 0`. -/
private theorem hom₂_comp_eq_of_mor₁_comp_eq {T T' : Triangle D} (hT' : T' ∈ distTriang D)
    {ψ : T ⟶ T'} (hψ : ψ.hom₃ = 0) {X : D} {u v : T'.obj₂ ⟶ X}
    (h : T'.mor₁ ≫ u = T'.mor₁ ≫ v) : ψ.hom₂ ≫ u = ψ.hom₂ ≫ v := by
  rw [← sub_eq_zero, ← Preadditive.comp_sub]
  obtain ⟨t, ht⟩ :=
    Triangle.yoneda_exact₂ _ hT' (u - v) (by rw [Preadditive.comp_sub, h, sub_self])
  rw [ht, ← ψ.comm₂_assoc, hψ, zero_comp, comp_zero]

/-- **The content of Stacks 0G3C, index-free.** Let `T ⟶ T' ⟶ T''` be composable morphisms of
triangles with `T'` distinguished, and assume that both have vanishing third component. Then
`T.obj₂ ⟶ T''.obj₁` inverts `T''.mor₁` up to the two given morphisms: there is
`s : T.obj₂ ⟶ T''.obj₁` with `T.mor₁ ≫ s = ψ.hom₁ ≫ φ.hom₁` and
`s ≫ T''.mor₁ = ψ.hom₂ ≫ φ.hom₂`.

Since `T'.mor₃ ≫ φ.hom₁⟦1⟧' = φ.hom₃ ≫ T''.mor₃ = 0`, the morphism `φ.hom₁` factors as
`T'.mor₁ ≫ s` by `yoneda_exact₁`; that `s` already satisfies the first identity, and it satisfies
the second one after precomposition with `ψ.hom₂` by `hom₂_comp_eq_of_mor₁_comp_eq`. -/
private theorem exists_inverse_mor₁_of_hom₃_eq_zero {T T' T'' : Triangle D}
    (hT' : T' ∈ distTriang D) (ψ : T ⟶ T') (φ : T' ⟶ T'')
    (hψ : ψ.hom₃ = 0) (hφ : φ.hom₃ = 0) :
    ∃ s : T.obj₂ ⟶ T''.obj₁,
      T.mor₁ ≫ s = ψ.hom₁ ≫ φ.hom₁ ∧ s ≫ T''.mor₁ = ψ.hom₂ ≫ φ.hom₂ := by
  obtain ⟨s, hs⟩ := yoneda_exact₁ hT' φ.hom₁ (by rw [φ.comm₃, hφ, zero_comp])
  exact ⟨ψ.hom₂ ≫ s, by rw [ψ.comm₁_assoc, ← hs], (Category.assoc _ _ _).trans
    (hom₂_comp_eq_of_mor₁_comp_eq hT' hψ (by rw [φ.comm₁, hs, Category.assoc]))⟩

/-- **Stacks 0G3C**. Let `T : J ⥤ Triangle 𝒟` be an inverse system of distinguished triangles
`A_j ⟶ B_j ⟶ C_j ⟶ A_j[1]` in a pre-triangulated category, indexed by a cofiltered category `J`.
If the inverse system `(C_j)` of third terms is pro-zero, i.e. every index admits an arrow along
which the transition morphism of third terms vanishes, then the morphisms `A_j ⟶ B_j` determine
an isomorphism of pro-objects between `(A_j)` and `(B_j)`: for every index `j` there are an arrow
`f : k ⟶ j` and a morphism `s : B_k ⟶ A_j` such that `A_k ⟶ B_k ⟶ A_j` is the transition morphism
`A_k ⟶ A_j` and `B_k ⟶ A_j ⟶ B_j` is the transition morphism `B_k ⟶ B_j`. -/
@[stacks 0G3C]
public theorem exists_proInverse_mor₁_of_proZero_π₃ [IsCofiltered J]
    (T : J ⥤ Triangle D) (hT : ∀ j, T.obj j ∈ distTriang D)
    (h₃ : ∀ j : J, ∃ (k : J) (f : k ⟶ j), (T.map f).hom₃ = 0) (j : J) :
    ∃ (k : J) (f : k ⟶ j) (s : (T.obj k).obj₂ ⟶ (T.obj j).obj₁),
      (T.obj k).mor₁ ≫ s = (T.map f).hom₁ ∧ s ≫ (T.obj j).mor₁ = (T.map f).hom₂ := by
  obtain ⟨k, f, hf⟩ := h₃ j
  obtain ⟨k', f', hf'⟩ := h₃ k
  obtain ⟨s, hs₁, hs₂⟩ :=
    exists_inverse_mor₁_of_hom₃_eq_zero (hT k) (T.map f') (T.map f) hf' hf
  exact ⟨k', f' ≫ f, s, by rw [hs₁, T.map_comp, comp_hom₁], by rw [hs₂, T.map_comp, comp_hom₂]⟩

end Pretriangulated

end CategoryTheory

namespace DerivedCategory

open CategoryTheory Limits Pretriangulated DerivedCategory.TStructure
  CategoryTheory.EssentiallyConstantInd

/-! ## Stacks 0G3B: essential constancy in `D(𝒜)`, tested on cohomology

### Truncation and cohomology -/

section Trunc

variable {𝒜 : Type u'} [Category.{v'} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- The cohomology in degree `i < n` of a system and of its `< n`-truncation agree. -/
private noncomputable def truncLTCompHomologyIso {K : Type u} [Category.{v} K]
    (M : K ⥤ DerivedCategory 𝒜) (i n : ℤ) (hi : i < n) :
    (M ⋙ t.truncLT n) ⋙ homologyFunctor 𝒜 i ≅ M ⋙ homologyFunctor 𝒜 i :=
  NatIso.ofComponents
    (fun j => @asIso _ _ _ _ ((homologyFunctor 𝒜 i).map ((t.truncLTι n).app (M.obj j)))
      (isIso_homologyFunctor_map_truncLTι n i hi (M.obj j)))
    (fun {j j'} f => by
      dsimp
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      simp)

/-- The cohomology in degree `i ≥ n` of a system and of its `≥ n`-truncation agree. -/
private noncomputable def truncGECompHomologyIso {K : Type u} [Category.{v} K]
    (M : K ⥤ DerivedCategory 𝒜) (i n : ℤ) (hi : n ≤ i) :
    M ⋙ homologyFunctor 𝒜 i ≅ (M ⋙ t.truncGE n) ⋙ homologyFunctor 𝒜 i :=
  NatIso.ofComponents
    (fun j => @asIso _ _ _ _ ((homologyFunctor 𝒜 i).map ((t.truncGEπ n).app (M.obj j)))
      (isIso_homologyFunctor_map_truncGEπ n i hi (M.obj j)))
    (fun {j j'} f => by
      dsimp
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      simp)

end Trunc

/-! ### Systems concentrated in a single degree -/

section Single

variable {𝒜 : Type u'} [Category.{v'} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]




/-- A system of objects of `D(𝒜)` concentrated in the single degree `a` is essentially constant
as a pro-object as soon as its system of `H^a` is: it is the `singleFunctor` of that system. -/
private theorem isEssentiallyConstant_op_of_isLE_of_isGE {J : Type u} [Category.{v} J]
    (B : J ⥤ DerivedCategory 𝒜) (a : ℤ)
    (hLE : ∀ j, t.IsLE (B.obj j) a) (hGE : ∀ j, t.IsGE (B.obj j) a)
    (hH : IsEssentiallyConstantInd (B ⋙ homologyFunctor 𝒜 a).op) :
    IsEssentiallyConstantInd B.op :=
  isEssentiallyConstant_of_natIso (NatIso.op (isoCompSingleFunctorOfIsLEOfIsGE B a hLE hGE))
    (hH.op_comp (singleFunctor 𝒜 a))

end Single

/-! ### Stacks 0G3B -/

section Main

variable {J : Type u} [Category.{v} J] {𝒜 : Type u'} [Category.{v'} 𝒜] [Abelian 𝒜]
  [HasDerivedCategory.{w} 𝒜]

/-- Induction on the width of the interval of degrees: a system whose cohomology is concentrated
in `[a, a + m - 1]` and whose cohomology systems are essentially constant is essentially
constant. -/
private theorem isEssentiallyConstant_op_of_homology [IsCofiltered J] (m : ℕ) :
    ∀ (a : ℤ) (A : J ⥤ DerivedCategory 𝒜),
      (∀ (i : ℤ), i < a ∨ a + (m : ℤ) ≤ i →
        ∀ j : J, IsZero ((homologyFunctor 𝒜 i).obj (A.obj j))) →
      (∀ i : ℤ, IsEssentiallyConstantInd (A ⋙ homologyFunctor 𝒜 i).op) →
      IsEssentiallyConstantInd A.op := by
  induction m with
  | zero =>
    intro a A hA _
    refine isEssentiallyConstant_op_of_isZero (fun j => ?_)
    have : t.IsLE (A.obj j) (a - 1) :=
      (DerivedCategory.isLE_iff _ _).mpr (fun i hi => hA i (Or.inr (by push_cast; omega)) j)
    have : t.IsGE (A.obj j) a :=
      (DerivedCategory.isGE_iff _ _).mpr (fun i hi => hA i (Or.inl hi) j)
    exact t.isZero (A.obj j) (a - 1) a (by omega)
  | succ m ih =>
    intro a A hA hH
    have hGE : ∀ j : J, t.IsGE (A.obj j) a := fun j =>
      (DerivedCategory.isGE_iff _ _).mpr (fun i hi => hA i (Or.inl hi) j)
    have hT : ∀ j, (A ⋙ t.triangleLTGE (a + 1)).obj j ∈ distTriang (DerivedCategory 𝒜) :=
      fun j => t.triangleLTGE_distinguished _ _
    have h₁ : IsEssentiallyConstantInd
        ((A ⋙ t.triangleLTGE (a + 1)) ⋙ Triangle.π₁).op := by
      show IsEssentiallyConstantInd (A ⋙ t.truncLT (a + 1)).op
      refine isEssentiallyConstant_op_of_isLE_of_isGE _ a
        (fun j => t.isLE_truncLT_obj (A.obj j) (a + 1) a (by omega)) (fun j => ?_) ?_
      · have := hGE j
        exact inferInstanceAs (t.IsGE ((t.truncLT (a + 1)).obj (A.obj j)) a)
      · exact isEssentiallyConstant_of_natIso
          (NatIso.op (truncLTCompHomologyIso A a (a + 1) (by omega))) (hH a)
    have h₃ : IsEssentiallyConstantInd
        ((A ⋙ t.triangleLTGE (a + 1)) ⋙ Triangle.π₃).op := by
      show IsEssentiallyConstantInd (A ⋙ t.truncGE (a + 1)).op
      refine ih (a + 1) (A ⋙ t.truncGE (a + 1)) (fun i hi j => ?_) (fun i => ?_)
      · rcases hi with hi | hi
        · exact isZero_of_isGE ((t.truncGE (a + 1)).obj (A.obj j)) (a + 1) i hi
        · exact IsZero.of_iso (hA i (Or.inr (by push_cast at hi ⊢; omega)) j)
            ((truncGECompHomologyIso A i (a + 1) (by omega)).app j).symm
      · rcases lt_or_ge i (a + 1) with hi | hi
        · exact isEssentiallyConstant_op_of_isZero
            (fun j => isZero_of_isGE ((t.truncGE (a + 1)).obj (A.obj j)) (a + 1) i hi)
        · exact isEssentiallyConstant_of_natIso
            (NatIso.op (truncGECompHomologyIso A i (a + 1) hi).symm) (hH i)
    exact (CategoryTheory.Pretriangulated.isEssentiallyConstant_op_π₂_and_exists_limit_triangle
      (A ⋙ t.triangleLTGE (a + 1)) hT h₁ h₃).1

end Main

section

variable {J : Type u} [Category.{v} J] {𝒜 : Type u'} [Category.{v'} 𝒜] [Abelian 𝒜]
  [HasDerivedCategory 𝒜]

/-- Let `A : J ⥤ D(𝒜)` be an inverse system in the derived category of an abelian category, indexed
by a cofiltered category `J`. Assume `H^i(A_j) = 0` for every `j` and every `i` outside an interval
`[a, b]`, and that each inverse system `(H^i(A_j))_j` of `𝒜` is essentially constant (Stacks 05PU
for the opposite diagram). Then `(A_j)` is essentially constant: besides
`IsEssentiallyConstantInd A.op`, there are an index `n`, an object `X`, a morphism `φ : A_n ⟶ X`
and a limit cone with apex `X` on the system restricted to the indices `j ≥ n` (the objects of
`Over n`) whose leg at `n` is split by `φ`; and for every `i` the image of that cone under `H^i` is
again a limit cone, i.e. `H^i(X)` is the value of the essentially constant system `(H^i(A_j))_j`.
-/
@[stacks 0G3B]
public theorem isEssentiallyConstant_op_and_exists_limit_cone_of_homology
    [IsCofiltered J] (A : J ⥤ DerivedCategory 𝒜) (a b : ℤ)
    (hA : ∀ (i : ℤ), i < a ∨ b < i → ∀ j : J, IsZero ((homologyFunctor 𝒜 i).obj (A.obj j)))
    (hH : ∀ i : ℤ, IsEssentiallyConstantInd (A ⋙ homologyFunctor 𝒜 i).op) :
    IsEssentiallyConstantInd A.op ∧
      ∃ (n : J) (X : DerivedCategory 𝒜) (φ : A.obj n ⟶ X)
        (π : (Functor.const (Over n)).obj X ⟶ Over.forget n ⋙ A),
        π.app (Over.mk (𝟙 n)) ≫ φ = 𝟙 X ∧ Nonempty (IsLimit (Cone.mk X π)) ∧
        ∀ i : ℤ, Nonempty (IsLimit ((homologyFunctor 𝒜 i).mapCone (Cone.mk X π))) := by
  have hess : IsEssentiallyConstantInd A.op := by
    refine isEssentiallyConstant_op_of_homology (b + 1 - a).toNat a A (fun i hi j => hA i ?_ j) hH
    exact hi.imp id fun hi => by omega
  obtain ⟨X, n, ⟨w⟩⟩ := Witness.exists_witness hess
  refine ⟨hess, n, X, w.ret, (Witness.restrictedCone w).π, w.leg_ret,
    ⟨Witness.isLimitRestrictedCone w⟩, fun i => ?_⟩
  exact ⟨Witness.isLimitRestrictedCone (w.mapFunctor (homologyFunctor 𝒜 i))⟩

end

/-! ## Stacks 0G3D: a pro-isomorphism in `D(𝒜)`, detected on cohomology

### Pro-zero systems in the derived category -/

section

variable {J : Type u} [Category.{v} J]

variable {𝒜 : Type u'} [Category.{v'} 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]

/-- An object of the derived category whose cohomology vanishes in every degree is zero. -/
private lemma isZero_of_forall_isZero_homology (X : DerivedCategory 𝒜)
    (h : ∀ i : ℤ, IsZero ((homologyFunctor 𝒜 i).obj X)) : IsZero X := by
  have hiso : IsIso (0 : X ⟶ X) := by
    rw [DerivedCategory.isIso_iff]
    intro n
    have h0 : (homologyFunctor 𝒜 n).map (0 : X ⟶ X) = 𝟙 _ := by
      rw [Functor.map_zero]
      exact (h n).eq_of_src _ _
    rw [h0]
    infer_instance
  rw [IsZero.iff_id_eq_zero]
  have h1 := IsIso.hom_inv_id (0 : X ⟶ X)
  rw [zero_comp] at h1
  exact h1.symm

/-- An essentially constant inverse system in the derived category whose cohomology is pro-zero
in every degree is itself pro-zero. -/
private lemma isProZero_of_isEssentiallyConstant_op (C : J ⥤ DerivedCategory 𝒜)
    (hC : IsEssentiallyConstantInd C.op) (hH : ∀ i : ℤ, IsProZero (C ⋙ homologyFunctor 𝒜 i)) :
    IsProZero C := by
  obtain ⟨t, i₀, b, hab, hfac⟩ := hC
  have hab' : (t.ι.app i₀).unop ≫ b.unop = 𝟙 t.pt.unop := by
    simpa using congrArg Quiver.Hom.unop hab
  have hX : IsZero t.pt.unop := by
    apply isZero_of_forall_isZero_homology
    intro i
    obtain ⟨k₀, g, hg⟩ := hH i i₀.unop
    have hg' : (homologyFunctor 𝒜 i).map (C.map g) = 0 := hg
    have hnat : (t.ι.app (Opposite.op k₀)).unop ≫ C.map g = (t.ι.app i₀).unop := by
      simpa using congrArg Quiver.Hom.unop (t.ι.naturality (Quiver.Hom.op g))
    have hid : 𝟙 t.pt.unop = (t.ι.app (Opposite.op k₀)).unop ≫ C.map g ≫ b.unop := by
      rw [← Category.assoc, hnat, hab']
    rw [IsZero.iff_id_eq_zero]
    have hz : (homologyFunctor 𝒜 i).map (𝟙 t.pt.unop) = 0 := by rw [hid]; simp [hg']
    simpa using hz
  intro j
  obtain ⟨k, v, u, huv⟩ := hfac (Opposite.op j)
  refine ⟨k.unop, u.unop, ?_⟩
  have h := congrArg Quiver.Hom.unop huv
  simp only [Quiver.Hom.unop_op, unop_comp, Functor.op_map] at h
  simpa [hX.eq_zero_of_tgt b.unop] using h

end

/-! ### The vanishing along a chain of triangles -/

section Triangles

variable {𝒜 : Type u'} [Category.{v'} 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]

/-- The third term of a distinguished triangle has no cohomology in a degree where the second
term has none and the first term has none in the next degree: exactness of the homology sequence
at `H^i(C)`. -/
private lemma isZero_homology_obj₃ (T : Triangle (DerivedCategory 𝒜))
    (hT : T ∈ distTriang (DerivedCategory 𝒜)) (i : ℤ)
    (h₂ : IsZero ((homologyFunctor 𝒜 i).obj T.obj₂))
    (h₁ : IsZero ((homologyFunctor 𝒜 (i + 1)).obj T.obj₁)) :
    IsZero ((homologyFunctor 𝒜 i).obj T.obj₃) :=
  ((homologyFunctor 𝒜 0).homologySequence_exact₃ T hT i (i + 1) rfl).isZero_of_both_isZero h₂ h₁

/-- **The vanishing which is the content of Stacks 0G3D.** Let `u : T ⟶ T'` and `v : T' ⟶ T''` be
two consecutive morphisms of distinguished triangles. If `H^{p+1}(u.hom₁)` factors through
`H^{p+1}(T.mor₁)` and `H^p(v.hom₂)` factors through `H^p(T''.mor₁)` — the two factorizations a
pro-inverse on cohomology provides — then the composite of the third terms vanishes on `H^p`.

Indeed `H^p(u.hom₃)` is killed by the connecting morphism `δ_{T'}`, because by naturality of `δ`
it is `δ_T` followed by `H^{p+1}(u.hom₁)`, hence by `δ_T ≫ H^{p+1}(T.mor₁) = 0`; and
`H^p(v.hom₃)` kills the image of `H^p(T'.mor₂)`, because by `v.comm₂` that image is
`H^p(v.hom₂) ≫ H^p(T''.mor₂)`, hence a factor of `H^p(T''.mor₁ ≫ T''.mor₂) = 0`. Exactness of
the homology sequence at `H^p(T'.obj₃)` turns the two vanishings into the assertion. -/
private lemma homology_map_hom₃_comp_eq_zero {T T' T'' : Triangle (DerivedCategory 𝒜)}
    (hT : T ∈ distTriang (DerivedCategory 𝒜)) (hT' : T' ∈ distTriang (DerivedCategory 𝒜))
    (hT'' : T'' ∈ distTriang (DerivedCategory 𝒜)) (u : T ⟶ T') (v : T' ⟶ T'') (p : ℤ)
    (h₁ : ∃ t, (homologyFunctor 𝒜 (p + 1)).map T.mor₁ ≫ t =
      (homologyFunctor 𝒜 (p + 1)).map u.hom₁)
    (h₂ : ∃ s, s ≫ (homologyFunctor 𝒜 p).map T''.mor₁ = (homologyFunctor 𝒜 p).map v.hom₂) :
    (homologyFunctor 𝒜 p).map u.hom₃ ≫ (homologyFunctor 𝒜 p).map v.hom₃ = 0 := by
  obtain ⟨t, ht⟩ : ∃ t, ((homologyFunctor 𝒜 0).shift (p + 1)).map T.mor₁ ≫ t =
    ((homologyFunctor 𝒜 0).shift (p + 1)).map u.hom₁ := h₁
  obtain ⟨s, hs⟩ : ∃ s, s ≫ ((homologyFunctor 𝒜 0).shift p).map T''.mor₁ =
    ((homologyFunctor 𝒜 0).shift p).map v.hom₂ := h₂
  have hδ : ((homologyFunctor 𝒜 0).shift p).map u.hom₃ ≫
      (homologyFunctor 𝒜 0).homologySequenceδ T' p (p + 1) rfl = 0 := by
    rw [Functor.homologySequenceδ_naturality (homologyFunctor 𝒜 0) u p (p + 1) rfl, ← ht,
      ← Category.assoc, Functor.homologySequenceδ_comp (homologyFunctor 𝒜 0) _ hT p (p + 1) rfl,
      zero_comp]
  have hmor₂ : ((homologyFunctor 𝒜 0).shift p).map T'.mor₂ ≫
      ((homologyFunctor 𝒜 0).shift p).map v.hom₃ = 0 := by
    rw [← Functor.map_comp, v.comm₂, Functor.map_comp, ← hs, Category.assoc, ← Functor.map_comp,
      comp_distTriang_mor_zero₁₂ _ hT'', Functor.map_zero, comp_zero]
  exact ((homologyFunctor 𝒜 0).homologySequence_exact₃ T' hT' p (p + 1)
    rfl).comp_eq_zero hδ hmor₂

end Triangles

section Sequences

variable {D : Type u} [Category.{v} D] [HasShift D ℤ]

/-- **The system of triangles built by TR3 along a chain.** Let `α : A ⟶ B` be a morphism of
inverse systems indexed by `ℕᵒᵖ`, let `Triangle.mk (α.app ⟨n⟩) (m₂ n) (m₃ n)` be a cone on each
`α.app ⟨n⟩`, and let the morphisms of triangles `φ n` be the one-step transitions of `A` and of
`B` on the first two terms. Then *every* transition morphism of the inverse system of triangles
they assemble into is the transition morphism of `A`, resp. of `B`, on the first two terms.

This is the naturality of a transformation with identity components, which
`CategoryTheory.NatTrans.ofOpSequence` builds out of the one-step squares; the comparison is made
in `D × D`, which treats the two terms at once. -/
private lemma ofOpSequence_map_hom₁_hom₂ {A B : ℕᵒᵖ ⥤ D} (α : A ⟶ B) {Z : ℕ → D}
    {m₂ : ∀ n : ℕ, B.obj (Opposite.op n) ⟶ Z n}
    {m₃ : ∀ n : ℕ, Z n ⟶ (A.obj (Opposite.op n))⟦(1 : ℤ)⟧}
    (φ : ∀ n : ℕ, Triangle.mk (α.app (Opposite.op (n + 1))) (m₂ (n + 1)) (m₃ (n + 1)) ⟶
      Triangle.mk (α.app (Opposite.op n)) (m₂ n) (m₃ n))
    (hφ₁ : ∀ n : ℕ, (φ n).hom₁ = A.map (homOfLE (n.le_add_right 1)).op)
    (hφ₂ : ∀ n : ℕ, (φ n).hom₂ = B.map (homOfLE (n.le_add_right 1)).op)
    {n₁ n₂ : ℕᵒᵖ} (f : n₁ ⟶ n₂) :
    ((Functor.ofOpSequence (X := fun n => Triangle.mk (α.app (Opposite.op n)) (m₂ n) (m₃ n))
        φ).map f).hom₁ = A.map f ∧
      ((Functor.ofOpSequence (X := fun n => Triangle.mk (α.app (Opposite.op n)) (m₂ n) (m₃ n))
        φ).map f).hom₂ = B.map f := by
  have h := (NatTrans.ofOpSequence (G := A.prod' B)
    (F := Functor.ofOpSequence (X := fun n => Triangle.mk (α.app (Opposite.op n)) (m₂ n) (m₃ n)) φ
      ⋙ Triangle.π₁.prod' Triangle.π₂) (fun _ => 𝟙 _) (fun n => by
        refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
        rw [Functor.comp_map, Functor.ofOpSequence_map_homOfLE_succ]
        exact Prod.ext (hφ₁ n) (hφ₂ n))).naturality f
  have h' := (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))
  exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩

end Sequences

/-! ### Stacks 0G3D -/

section Chain

variable {𝒜 : Type u'} [Category.{v'} 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]

/-- **Stacks 0G3D for a chain**, which is the form the source states. Let `α : A ⟶ B` be a
morphism of inverse systems indexed by `ℕᵒᵖ` in `D(𝒜)`, with cohomology concentrated in `[a, b]`,
and assume that in every degree the one-step transitions have a pro-inverse on cohomology. Then
the index `0` has a refinement which is a pro-inverse of `α`. -/
private lemma exists_proInverse_of_seq {A B : ℕᵒᵖ ⥤ DerivedCategory 𝒜} (α : A ⟶ B) (a b : ℤ)
    (hA : ∀ i : ℤ, i < a ∨ b < i → ∀ n : ℕᵒᵖ, IsZero ((homologyFunctor 𝒜 i).obj (A.obj n)))
    (hB : ∀ i : ℤ, i < a ∨ b < i → ∀ n : ℕᵒᵖ, IsZero ((homologyFunctor 𝒜 i).obj (B.obj n)))
    (hP : ∀ (i : ℤ) (n : ℕ), HasProInverse (Functor.whiskerRight α (homologyFunctor 𝒜 i))
      (homOfLE (n.le_add_right 1)).op) :
    ∃ (k : ℕᵒᵖ) (f : k ⟶ Opposite.op 0), HasProInverse α f := by
  obtain ⟨Z, m₂, m₃, hdist⟩ :
      ∃ (Z : ℕ → DerivedCategory 𝒜) (m₂ : ∀ n : ℕ, B.obj (Opposite.op n) ⟶ Z n)
        (m₃ : ∀ n : ℕ, Z n ⟶ (A.obj (Opposite.op n))⟦(1 : ℤ)⟧),
        ∀ n : ℕ, Triangle.mk (α.app (Opposite.op n)) (m₂ n) (m₃ n) ∈
          distTriang (DerivedCategory 𝒜) := by
    choose Z m₂ m₃ h using fun n : ℕ => distinguished_cocone_triangle (α.app (Opposite.op n))
    exact ⟨Z, m₂, m₃, h⟩
  obtain ⟨φ, hφ₁, hφ₂⟩ :
      ∃ φ : ∀ n : ℕ, Triangle.mk (α.app (Opposite.op (n + 1))) (m₂ (n + 1)) (m₃ (n + 1)) ⟶
          Triangle.mk (α.app (Opposite.op n)) (m₂ n) (m₃ n),
        (∀ n : ℕ, (φ n).hom₁ = A.map (homOfLE (n.le_add_right 1)).op) ∧
          (∀ n : ℕ, (φ n).hom₂ = B.map (homOfLE (n.le_add_right 1)).op) := by
    have h : ∀ n : ℕ, ∃ ψ : Triangle.mk (α.app (Opposite.op (n + 1))) (m₂ (n + 1)) (m₃ (n + 1)) ⟶
        Triangle.mk (α.app (Opposite.op n)) (m₂ n) (m₃ n),
        ψ.hom₁ = A.map (homOfLE (n.le_add_right 1)).op ∧
          ψ.hom₂ = B.map (homOfLE (n.le_add_right 1)).op := by
      intro n
      obtain ⟨w, hw₂, hw₃⟩ := complete_distinguished_triangle_morphism _ _ (hdist (n + 1))
        (hdist n) (A.map (homOfLE (n.le_add_right 1)).op)
        (B.map (homOfLE (n.le_add_right 1)).op) (α.naturality _).symm
      exact ⟨Triangle.homMk _ _ _ _ w (α.naturality _).symm hw₂ hw₃, rfl, rfl⟩
    choose φ h₁ h₂ using h
    exact ⟨φ, h₁, h₂⟩
  let T : ℕᵒᵖ ⥤ Triangle (DerivedCategory 𝒜) :=
    Functor.ofOpSequence (X := fun n => Triangle.mk (α.app (Opposite.op n)) (m₂ n) (m₃ n)) φ
  have hom₁ : ∀ {n₁ n₂ : ℕᵒᵖ} (f : n₁ ⟶ n₂), (T.map f).hom₁ = A.map f :=
    fun f => (ofOpSequence_map_hom₁_hom₂ α φ hφ₁ hφ₂ f).1
  have hom₂ : ∀ {n₁ n₂ : ℕᵒᵖ} (f : n₁ ⟶ n₂), (T.map f).hom₂ = B.map f :=
    fun f => (ofOpSequence_map_hom₁_hom₂ α φ hφ₁ hφ₂ f).2
  have hC₃ : ∀ p : ℤ, IsProZero ((T ⋙ Triangle.π₃) ⋙ homologyFunctor 𝒜 p) := by
    intro p n
    obtain ⟨n₀, rfl⟩ : ∃ n₀ : ℕ, n = Opposite.op n₀ := ⟨n.unop, rfl⟩
    obtain ⟨s, -, hs⟩ := hP p n₀
    obtain ⟨t, ht, -⟩ := hP (p + 1) (n₀ + 1)
    refine ⟨Opposite.op (n₀ + 1 + 1), (homOfLE ((n₀ + 1).le_add_right 1)).op ≫
      (homOfLE (n₀.le_add_right 1)).op, ?_⟩
    rw [Functor.map_comp]
    exact homology_map_hom₃_comp_eq_zero (hdist _) (hdist _) (hdist _) _ _ p
      ⟨t, by rw [hom₁]; exact ht⟩ ⟨s, by rw [hom₂]; exact hs⟩
  obtain ⟨hEC, -⟩ := DerivedCategory.isEssentiallyConstant_op_and_exists_limit_cone_of_homology
    (T ⋙ Triangle.π₃) (a - 1) b
    (fun i hi n => isZero_homology_obj₃ _ (hdist n.unop) i (hB i (by omega) n)
      (hA (i + 1) (by omega) n))
    (fun i => isEssentiallyConstant_op_of_isProZero _ (hC₃ i))
  obtain ⟨k, f, s, hs₁, hs₂⟩ := exists_proInverse_mor₁_of_proZero_π₃ T (fun n => hdist n.unop)
    (isProZero_of_isEssentiallyConstant_op (T ⋙ Triangle.π₃) hEC hC₃) (Opposite.op 0)
  exact ⟨k, f, s, hs₁.trans (hom₁ f), hs₂.trans (hom₂ f)⟩

end Chain

section Main

variable {J : Type u} [Category.{v} J] {𝒜 : Type u'} [Category.{v'} 𝒜] [Abelian 𝒜]
  [HasDerivedCategory 𝒜]

/-- **Stacks 0G3D**. Let `α : A ⟶ B` be an inverse system of maps `A_j ⟶ B_j` of the derived
category of an abelian category, indexed by a cofiltered category `J`. Assume `H^i(A_j) = 0` and
`H^i(B_j) = 0` for every `j` and every `i` outside an interval `[a, b]`, and that for every `i`
the maps `H^i(A_j) ⟶ H^i(B_j)` are an isomorphism of pro-objects of `𝒜`, i.e. every index `j`
admits an arrow `f : k ⟶ j` and a morphism `H^i(B_k) ⟶ H^i(A_j)` whose two round trips are the
transition morphisms. Then the maps `A_j ⟶ B_j` determine an isomorphism of pro-objects between
`(A_j)` and `(B_j)`: for every index `j` there are an arrow `f : k ⟶ j` and a morphism
`s : B_k ⟶ A_j` such that `A_k ⟶ B_k ⟶ A_j` is the transition morphism `A_k ⟶ A_j` and
`B_k ⟶ A_j ⟶ B_j` is the transition morphism `B_k ⟶ B_j`. -/
@[stacks 0G3D]
public theorem exists_proInverse_of_proInverse_homology [IsCofiltered J]
    {A B : J ⥤ DerivedCategory 𝒜} (α : A ⟶ B) (a b : ℤ)
    (hA : ∀ i : ℤ, i < a ∨ b < i → ∀ j : J, IsZero ((homologyFunctor 𝒜 i).obj (A.obj j)))
    (hB : ∀ i : ℤ, i < a ∨ b < i → ∀ j : J, IsZero ((homologyFunctor 𝒜 i).obj (B.obj j)))
    (hH : ∀ (i : ℤ) (j : J), ∃ (k : J) (f : k ⟶ j)
      (s : (homologyFunctor 𝒜 i).obj (B.obj k) ⟶ (homologyFunctor 𝒜 i).obj (A.obj j)),
      (homologyFunctor 𝒜 i).map (α.app k) ≫ s = (homologyFunctor 𝒜 i).map (A.map f) ∧
        s ≫ (homologyFunctor 𝒜 i).map (α.app j) = (homologyFunctor 𝒜 i).map (B.map f))
    (j : J) :
    ∃ (k : J) (f : k ⟶ j) (s : B.obj k ⟶ A.obj j),
      α.app k ≫ s = A.map f ∧ s ≫ α.app j = B.map f := by
  obtain ⟨c, g, rfl, hg⟩ := exists_seq_of_forall_exists
    (fun _ _ f => ∀ i : ℤ, HasProInverse (Functor.whiskerRight α (homologyFunctor 𝒜 i)) f)
    (fun j' => exists_refinement (fun i => Functor.whiskerRight α (homologyFunctor 𝒜 i)) a b
      hA hB hH j') j
  obtain ⟨k, f, s, hs₁, hs₂⟩ := exists_proInverse_of_seq
    (Functor.whiskerLeft (Functor.ofOpSequence g) α) a b
    (fun i hi n => hA i hi (c n.unop)) (fun i hi n => hB i hi (c n.unop)) (fun i n => by
      have h := hg n i
      rw [← Functor.ofOpSequence_map_homOfLE_succ g n] at h
      exact h)
  exact ⟨c k.unop, (Functor.ofOpSequence g).map f, s, hs₁, hs₂⟩

end Main

end DerivedCategory

end
