module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceSums
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Finite direct sums of coherent sheaves of modules on a site, and the zero sheaf

Stacks 01BY (3) says that kernels, cokernels and *finite direct sums* of coherent sheaves of
modules are coherent.  Over a ringed site, where the predicate is
`SheafOfModules.IsCoherentOnSite` (Stacks 03DL(8)), the kernel clause is
`Stacks.SheafOfModules.isCoherentOnSite_kerObj`, the cokernel clause is
`Stacks.SheafOfModules.isCoherentOnSite_cokernel`, and the direct sum clause exists for *two*
summands (`Stacks.SheafOfModules.isCoherentOnSite_of_split`) and for a finite family of *copies
of one* sheaf (`Stacks.SheafOfModules.isCoherentOnSite_sigmaConst`).  This file proves the clause
for an arbitrary finite family, and proves coherence of a zero sheaf of modules outright.

## Main results

* `Stacks.SheafOfModules.isFiniteType_presheaf_of_isZero`: the underlying presheaf of modules of
  a zero sheaf of modules is of finite type.
* `Stacks.SheafOfModules.isFiniteType_relations_of_isZero`: the sheaf of relations among a finite
  family of sections of a zero sheaf of modules is of finite type.
* `Stacks.SheafOfModules.isCoherentOnSite_zero`: **a zero sheaf of modules on a site is
  coherent**, with no further input.
* `Stacks.SheafOfModules.isCoherentOnSite_coprodFin`: **a coproduct of a family of coherent
  sheaves of modules indexed by `Fin n` is coherent.**
* `Stacks.SheafOfModules.isCoherentOnSite_sigma`: the same for a family indexed by an arbitrary
  finite type, in an arbitrary universe.

## Implementation notes

**The induction needs nothing but the total identity.**  `isCoherentOnSite_of_split` is stated
for a sheaf of modules carrying four maps satisfying `fst ≫ inl + snd ≫ inr = 𝟙` and uses no
other biproduct identity, so the inductive step is the splitting of `∐_{Fin (n+1)} M` into its
zeroth summand and `∐_{Fin n} (M ∘ Fin.succ)`, whose four structure maps are `Sigma.desc` of
families defined by `Fin.cases`, together with that one equation.  Mathlib has no decomposition
of a coproduct over `Fin (n + 1)` — `Mathlib/CategoryTheory/Limits/Shapes/Biproducts.lean` has
nothing for `Fin` — and
`Fin.cases` is used in place of a comparison along `Fin.succ`, which keeps every `eqToHom` out of
the construction.  Note also that biproducts of shape `Fin n` do *not* synthesize in
`SheafOfModules`, while coproducts of that shape do, so the file is written with `∐`, not `⨁`.

**The family is not assumed constant**, which is what Stacks 01BY (3) actually asserts and what
the two-summand clause already allows: `isCoherentOnSite_of_split` takes two different sheaves of
modules, so the induction carries a family `M : Fin n → SheafOfModules R` at no extra cost.  The
index type of `isCoherentOnSite_sigma` lives in an arbitrary universe, since it enters only
through an equivalence with `Fin n`.

**The zero case is not the trivial one, and it needs no auxiliary coherent sheaf.**  Condition
(1) of coherence for a zero sheaf is the empty generating family.  Condition (2) is *not*
vacuous: the sheaf of relations among a finite family of sections of a zero sheaf is the whole
presheaf of coefficient tuples, since the linear combination map lands in a zero module, and what
has to be exhibited is a finite generating family for that — the standard tuples
`Pi.single j 1` over every object of the slice site.  The coefficient computation goes through
`relations_coe_sum` and `relations_coe_restrict`, and the membership proof is isolated in
`zeroRelation` so that it is elaborated once: written inline it makes the goal fail to be
type-correct at `implicit` transparency, a failure that recurs throughout this development.

The coproduct results are at module universe equal to the ring universe, as
`isCoherentOnSite_of_split` is: the splitting mixes summands by maps of sheaves of modules, which
requires their universes to agree.  The zero results are at an arbitrary module universe.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules

universe u v w m

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- Every section of a zero sheaf of modules vanishes. -/
theorem eq_zero_of_isZero {Z : SheafOfModules.{m} R} (hZ : IsZero Z) (X : Cᵒᵖ)
    (x : Z.val.obj X) : x = 0 := by
  have h : (𝟙 Z : Z ⟶ Z).val.app X x = (0 : Z ⟶ Z).val.app X x := by
    rw [hZ.eq_of_src (𝟙 Z) 0]
  have h0 : (0 : Z ⟶ Z).val.app X x = 0 := by
    change (0 : Z.val ⟶ Z.val).app X x = 0
    simp
  simpa [h0] using h

/-- The family of all objects of a site covers the final object. -/
private theorem coversTop_id (J : GrothendieckTopology C) : J.CoversTop (id : C → C) := fun X ↦
  J.covering_of_eq_top (Sieve.id_mem_iff_eq_top.mp
    ((Sieve.mem_ofObjects_iff (id : C → C) (𝟙 X)).2 ⟨X, ⟨𝟙 X⟩⟩))

/-- The underlying presheaf of modules of a zero sheaf of modules is of finite type: the empty
family generates it. -/
theorem isFiniteType_presheaf_of_isZero {Z : SheafOfModules.{m} R} (hZ : IsZero Z) :
    PresheafOfModules.IsFiniteType J Z.val := by
  refine isFiniteType_presheaf_of_coversTop id (coversTop_id J) (fun W ↦ ⟨0, Fin.elim0, ?_⟩)
  intro V f t
  refine ⟨⊤, J.top_mem V, fun W' g _ ↦ ⟨Fin.elim0, ?_⟩⟩
  exact (Finset.sum_empty).trans (eq_zero_of_isZero hZ _ _).symm

/-- Every coefficient tuple is a relation among a finite family of sections of a zero sheaf of
modules, because the module of sections it would have to combine to is itself zero. -/
private def zeroRelation {Z : SheafOfModules.{m} R} (hZ : IsZero Z) {U : C} {n : ℕ}
    (s : Fin n → Z.val.obj (op U)) (V : (Over U)ᵒᵖ)
    (a : Fin n → R.obj.obj (op V.unop.left)) :
    (PresheafOfModules.relations Z.val s).obj V :=
  ⟨a, eq_zero_of_isZero hZ _ _⟩

private theorem zeroRelation_val {Z : SheafOfModules.{m} R} (hZ : IsZero Z) {U : C} {n : ℕ}
    (s : Fin n → Z.val.obj (op U)) (V : (Over U)ᵒᵖ)
    (a : Fin n → R.obj.obj (op V.unop.left)) (j : Fin n) :
    (zeroRelation hZ s V a).val j = a j := rfl

/-- **The sheaf of relations among a finite family of sections of a zero sheaf of modules is of
finite type.**  It is the whole presheaf of coefficient tuples — the linear combination map lands
in a zero module, so every tuple is a relation — and the standard tuples `Pi.single j 1` generate
it over every object of the slice site. -/
theorem isFiniteType_relations_of_isZero {Z : SheafOfModules.{m} R} (hZ : IsZero Z) (U : C)
    (n : ℕ) (s : Fin n → Z.val.obj (op U)) :
    PresheafOfModules.IsFiniteType (J.over U) (PresheafOfModules.relations Z.val s) := by
  classical
  refine isFiniteType_presheaf_of_coversTop id (coversTop_id _) fun W ↦ ?_
  refine ⟨n, fun l ↦ zeroRelation hZ s _ (Pi.single l 1), fun V f x ↦ ?_⟩
  refine ⟨⊤, (J.over U).top_mem V, fun W' g _ ↦ ?_⟩
  obtain ⟨xv, hxv⟩ := x
  refine ⟨fun l ↦ R.obj.map g.left.op (xv l), Subtype.ext (funext fun j ↦ ?_)⟩
  rw [relations_coe_sum]
  refine (Finset.sum_eq_single j (fun l _ hlj ↦ ?_)
    (fun hj ↦ absurd (Finset.mem_univ j) hj)).trans ?_
  · rw [relations_coe_restrict, zeroRelation_val, Pi.single_eq_of_ne (Ne.symm hlj), map_zero,
      mul_zero]
  · rw [relations_coe_restrict, zeroRelation_val, Pi.single_eq_same, map_one, mul_one]
    rfl

/-- **A zero sheaf of modules on a site is coherent.**  Both clauses are proved outright, so no
other coherent sheaf of modules is needed as an input. -/
theorem isCoherentOnSite_zero {Z : SheafOfModules.{m} R} (hZ : IsZero Z) :
    SheafOfModules.IsCoherentOnSite Z :=
  ⟨isFiniteType_presheaf_of_isZero hZ, isFiniteType_relations_of_isZero hZ⟩

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasColimitsOfShape (Discrete (Fin n))` on sheaves of modules
/-- Coproducts of shape `Fin n` of sheaves of modules.  Instance search finds this, but only
past the default `synthInstance.maxHeartbeats`, so it is synthesized once here and made a local
instance. -/
private theorem hasColimitsOfShape_discrete_fin [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] (n : ℕ) :
    HasColimitsOfShape (Discrete (Fin n)) (SheafOfModules.{w} R) :=
  inferInstance

attribute [local instance] hasColimitsOfShape_discrete_fin

section Coproducts

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The projection of `∐_{Fin (n+1)} M` onto its zeroth summand. -/
private noncomputable def splitFst {n : ℕ} (M : Fin (n + 1) → SheafOfModules.{w} R) :
    (∐ M) ⟶ M 0 :=
  Sigma.desc (Fin.cases (𝟙 (M 0)) (fun k ↦ (0 : M k.succ ⟶ M 0)))

/-- The projection of `∐_{Fin (n+1)} M` onto the coproduct of its remaining summands. -/
private noncomputable def splitSnd {n : ℕ} (M : Fin (n + 1) → SheafOfModules.{w} R) :
    (∐ M) ⟶ ∐ (fun k : Fin n ↦ M k.succ) :=
  Sigma.desc (Fin.cases 0 (fun k ↦ Sigma.ι (fun k : Fin n ↦ M k.succ) k))

/-- The inclusion of the coproduct of the summands after the zeroth one. -/
private noncomputable def splitInr {n : ℕ} (M : Fin (n + 1) → SheafOfModules.{w} R) :
    (∐ fun k : Fin n ↦ M k.succ) ⟶ ∐ M :=
  Sigma.desc (fun k ↦ Sigma.ι M k.succ)

/-- The total identity of the splitting of `∐_{Fin (n+1)} M` into its zeroth summand and the
coproduct of the others.  It is the only identity `isCoherentOnSite_of_split` consumes. -/
private theorem splitTotal {n : ℕ} (M : Fin (n + 1) → SheafOfModules.{w} R) :
    splitFst M ≫ Sigma.ι M 0 + splitSnd M ≫ splitInr M = 𝟙 _ := by
  refine Sigma.hom_ext _ _ fun j ↦ ?_
  rw [Preadditive.comp_add, Category.comp_id]
  refine Fin.cases ?_ ?_ j
  · simp [splitFst, splitSnd]
  · intro k
    simp [splitFst, splitSnd, splitInr]

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for the finite coproducts `∐ M` of sheaves of modules
/-- **Stacks Project, Tag 01BY (3), for a finite direct sum, on a site.**  A coproduct of
finitely many coherent sheaves of modules on a site is coherent.

The induction splits off the zeroth summand and appeals to
`isCoherentOnSite_of_split`; the base case is the empty coproduct, which is a zero object and is
coherent by `isCoherentOnSite_of_isZero`. -/
@[ega "0 5.3.2" "more general"]
theorem isCoherentOnSite_coprodFin : ∀ (n : ℕ) (M : Fin n → SheafOfModules.{w} R),
    (∀ i, SheafOfModules.IsCoherentOnSite (M i)) →
      SheafOfModules.IsCoherentOnSite (∐ M)
  | 0, _, _ => isCoherentOnSite_zero (by
      rw [IsZero.iff_id_eq_zero]
      exact Sigma.hom_ext _ _ fun j ↦ j.elim0)
  | n + 1, M, hM =>
      isCoherentOnSite_of_split (splitFst M) (splitSnd M) (Sigma.ι M 0) (splitInr M)
        (fun X x ↦ by
          let ev : ((∐ M) ⟶ (∐ M)) →+ (∐ M).val.obj X :=
            { toFun := fun f ↦ f.val.app X x
              map_zero' := rfl
              map_add' := fun _ _ ↦ rfl }
          exact (map_add ev (splitFst M ≫ Sigma.ι M 0) (splitSnd M ≫ splitInr M)).symm.trans
            (congrArg ev (splitTotal M)))
        (hM 0) (isCoherentOnSite_coprodFin n (fun k ↦ M k.succ) fun k ↦ hM k.succ)

/-- **Stacks Project, Tag 01BY (3), for a finite direct sum, on a site**, for a family indexed
by an arbitrary finite type: the index type is transported to `Fin n` by
`CategoryTheory.Limits.Sigma.whiskerEquiv`, whose comparison isomorphisms are the identities
because the family is reindexed rather than changed. -/
theorem isCoherentOnSite_sigma {I : Type*} [Finite I] (M : I → SheafOfModules.{w} R)
    [HasCoproduct M] (hM : ∀ i, SheafOfModules.IsCoherentOnSite (M i)) :
    SheafOfModules.IsCoherentOnSite (∐ M) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  exact isCoherentOnSite_of_iso
    (Sigma.whiskerEquiv e.symm (fun k ↦ Iso.refl (M (e.symm k))))
    (isCoherentOnSite_coprodFin n (fun k ↦ M (e.symm k)) fun k ↦ hM _)

end Coproducts

section Products

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks Project, Tag 01BY (3), for a finite direct product, on a site.**  A product of
finitely many coherent sheaves of modules on a site is coherent.

A finite product in a preadditive category with finite products is a biproduct, hence
isomorphic to the corresponding coproduct, and
`Stacks.SheafOfModules.isCoherentOnSite_coprodFin` applies to that.  The binary case is
`Stacks.SheafOfModules.isCoherentOnSite_prod`, which goes through `biprod` instead. -/
theorem isCoherentOnSite_piFin [HasFiniteProducts (SheafOfModules.{w} R)] {n : ℕ}
    (M : Fin n → SheafOfModules.{w} R)
    (hM : ∀ i, SheafOfModules.IsCoherentOnSite (M i)) :
    SheafOfModules.IsCoherentOnSite (∏ᶜ M) :=
  have : HasFiniteBiproducts (SheafOfModules.{w} R) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  isCoherentOnSite_of_iso
    ((biproduct.isoCoproduct M).symm ≪≫ biproduct.isoProduct M)
    (isCoherentOnSite_coprodFin n M hM)

end Products

end Stacks.SheafOfModules

end
