module

public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
import StacksCore.Tactic.StacksAttribute

/-! # The connecting morphism of a degreewise split sequence of cochain complexes

Stacks tags 011J, 011K and 011L. Given a complex `0 → A^• → B^• → C^• → 0` of cochain complexes
together with splittings `B^n = A^n ⊕ C^n` compatible with its maps, the family
`π^{n+1} ∘ d_B^n ∘ s^n` defines a morphism of complexes `δ : C^• → A[1]^•` (011J), the map it
induces on cohomology is the connecting map of the long exact sequence of 0117 (011K), and `δ`
depends on the splittings only up to homotopy (011L).

For 011L, "a second choice of splittings" is a second `ShortComplex.Splitting` in each degree, and
the morphisms `hⁿ` and `gⁿ` it is written in terms of are the differences of the two sections and
of the two retractions. Those are `ShortComplex.Splitting.sectionSub` and `retractionSub`, defined
here rather than beside `Splitting` upstream because nothing outside 011L uses them; they are
stated for a bare short complex, since neither the complex structure nor `ℤ` plays any role.

The `(-1)^k` of 0117 has a small echo here. Part (1) says `gⁿ = -hⁿ`, and part (2) is a homotopy
built from `g`, not from `h`. Those two facts are the same fact: reading a `0`-cochain
`C^• ⟶ A^•` as a `(-1)`-cochain `C^• ⟶ A[1]^•` conjugates `Cochain.δ` by `(-1)^1`, and that is
exactly the sign separating `g` from `h`.

The hypotheses of 011J match. The Stacks project asks only for an additive category and a
*complex* of complexes -- not a short exact sequence -- and Mathlib likewise asks for
`Preadditive` and a `ShortComplex`, with the splittings supplying whatever exactness is needed
degreewise. Mathlib's underlying cochain is `(σ p).s ≫ S.X₂.d p q ≫ (σ q).r`, which is the Stacks
formula read in diagrammatic order, `r` being its name for the projection `π`. For 011K the Stacks
project adds that `A` is abelian, and here the short exact sequence has to be supplied explicitly:
Mathlib's `homOfDegreewiseSplit` never asks for it, so `S.ShortExact` is a hypothesis of 011K
rather than something inherited from the setup.

The chain-complex twins of 011J and 011L are 011D and 011F, in
`StacksCore.Algebra.Homology.HomotopyCategory.ChainDegreewiseSplit`. They share no proof with this
file: the `Cochain`/`Cocycle` tower underneath `homOfDegreewiseSplit` has its `ComplexShape.up ℤ`
index convention built into `Triplet`, so none of it can even be *typed* for chain complexes.
There `δ(s)` is built directly as a `HomologicalComplex.Hom`, which is all `Cocycle.homOf` amounts
to anyway. Tag 011E, the chain twin of 011K, is still a gap -- see that file's docstring for what
it waits on.
-/

@[expose] public section

open CategoryTheory Category ComplexShape Limits HomologicalComplex CochainComplex

universe v u

add_to_stacks 011J "the morphism `δ : C^• → A[1]^•` itself."
  CochainComplex.homOfDegreewiseSplit

add_to_stacks 011J "its components, `δ^n = π^{n+1} ∘ d_B^n ∘ s^n` read in diagrammatic order."
  CochainComplex.homOfDegreewiseSplit_f

namespace CategoryTheory.ShortComplex.Splitting

variable {C : Type u} [Category.{v} C] [Preadditive C] {S : ShortComplex C} (σ σ' : S.Splitting)

/-- The morphism `h : X₃ ⟶ X₁` by which the sections of two splittings differ; `σ'.s = σ.s + h ≫ f`
by `s_eq_add_sectionSub`, and it is the only such morphism by `sectionSub_unique`. -/
def sectionSub : S.X₃ ⟶ S.X₁ := (σ'.s - σ.s) ≫ σ.r

/-- The morphism `g : X₃ ⟶ X₁` by which the retractions of two splittings differ;
`σ'.r = σ.r + g_ ≫ g` by `r_eq_add_retractionSub`, and it is the only such morphism by
`retractionSub_unique`. -/
def retractionSub : S.X₃ ⟶ S.X₁ := σ.s ≫ (σ'.r - σ.r)

lemma s_eq_add_sectionSub : σ'.s = σ.s + sectionSub σ σ' ≫ S.f := by
  simp [sectionSub, σ.r_f, Preadditive.sub_comp, Preadditive.comp_sub]

lemma r_eq_add_retractionSub : σ'.r = σ.r + S.g ≫ retractionSub σ σ' := by
  simp [retractionSub, σ.g_s_assoc, Preadditive.sub_comp, Preadditive.comp_sub, σ'.f_r]

lemma sectionSub_unique (h : S.X₃ ⟶ S.X₁) (hh : σ'.s = σ.s + h ≫ S.f) : h = sectionSub σ σ' := by
  rw [sectionSub, hh, add_sub_cancel_left, assoc, σ.f_r, comp_id]

lemma retractionSub_unique (g : S.X₃ ⟶ S.X₁) (hg : σ'.r = σ.r + S.g ≫ g) :
    g = retractionSub σ σ' := by
  rw [retractionSub, hg, add_sub_cancel_left, ← assoc, σ.s_g, id_comp]

/-- **Stacks 011L**, part (1), for a single short complex: the two difference morphisms of a pair
of splittings are negatives of each other. The Stacks proof is the one used here: `σ'.s ≫ σ'.r = 0`
expands to `g + h`. -/
lemma retractionSub_eq_neg_sectionSub : retractionSub σ σ' = -sectionSub σ σ' := by
  have h := σ'.s_r
  rw [s_eq_add_sectionSub σ σ', r_eq_add_retractionSub σ σ'] at h
  simp only [Preadditive.add_comp, Preadditive.comp_add, assoc, σ.s_r, σ.s_g_assoc, σ.f_r, comp_id,
    S.zero_assoc, zero_comp, comp_zero, add_zero, zero_add] at h
  exact eq_neg_of_add_eq_zero_right h

end CategoryTheory.ShortComplex.Splitting

namespace CochainComplex

open HomComplex CategoryTheory.ShortComplex.Splitting

section

variable {C : Type u} [Category.{v} C] [Preadditive C]
  (S : ShortComplex (CochainComplex C ℤ))
  (σ σ' : ∀ n, (S.map (eval C (up ℤ) n)).Splitting)

/-- The family `hⁿ : Cⁿ ⟶ Aⁿ` of Stacks 011L, with `(s')ⁿ = sⁿ + αⁿ ∘ hⁿ`. -/
def sectionSubHom (n : ℤ) : S.X₃.X n ⟶ S.X₁.X n := sectionSub (σ n) (σ' n)

/-- The family `gⁿ : Cⁿ ⟶ Aⁿ` of Stacks 011L, with `(π')ⁿ = πⁿ + gⁿ ∘ βⁿ`. -/
def retractionSubHom (n : ℤ) : S.X₃.X n ⟶ S.X₁.X n := retractionSub (σ n) (σ' n)

/-- **Stacks 011L**, part (1): `gⁿ = -hⁿ`. -/
@[stacks 011L "(1)"]
lemma retractionSubHom_eq_neg (n : ℤ) : retractionSubHom S σ σ' n = -sectionSubHom S σ σ' n :=
  retractionSub_eq_neg_sectionSub _ _

set_option allowUnsafeReducibility true in
attribute [local instance_reducible] HomologicalComplex.eval in
attribute [local reducible] ShortComplex.map in
/-- The two connecting cochains of 011J differ by `δ` of the degree-`0` cochain built from the
`hⁿ`. This is the whole computational content of 011L(2); everything after it is bookkeeping
about the shift. -/
lemma cocycleOfDegreewiseSplit_sub :
    (cocycleOfDegreewiseSplit S σ').1 - (cocycleOfDegreewiseSplit S σ).1
      = δ 0 1 (Cochain.ofHoms (sectionSubHom S σ σ')) := by
  ext p q hpq
  obtain rfl : q = p + 1 := by lia
  have hsg := fun n => (σ n).s_g
  have hfr := fun n => (σ n).f_r
  have hz := fun n => (S.map (eval C (up ℤ) n)).zero
  have hs := fun n => s_eq_add_sectionSub (σ n) (σ' n)
  have hr := fun n => r_eq_add_retractionSub (σ n) (σ' n)
  have hneg := fun n => retractionSub_eq_neg_sectionSub (σ n) (σ' n)
  -- put the splitting identities and the goal into the same spelling of `S.Xₖ.X n`
  simp only [HomologicalComplex.eval_map]
    at hsg hfr hz hs hr ⊢
  have hsg' : ∀ (n : ℤ) {X : C} (u : S.X₃.X n ⟶ X), (σ n).s ≫ S.g.f n ≫ u = u := by
    intro n _ u; rw [← Category.assoc, hsg n, Category.id_comp]
  have hz' : ∀ (n : ℤ) {X : C} (u : S.X₃.X n ⟶ X), S.f.f n ≫ S.g.f n ≫ u = 0 := by
    intro n _ u; rw [← Category.assoc, hz n, zero_comp]
  rw [δ_v 0 1 (by lia) _ p (p + 1) rfl p (p + 1) (by lia) rfl]
  simp only [sectionSubHom, Cochain.ofHoms_v, Cochain.sub_v, cocycleOfDegreewiseSplit,
    Cocycle.mk_coe, Cochain.mk_v, hs, hr, hneg, Preadditive.add_comp, Preadditive.comp_add,
    Preadditive.comp_neg, Category.assoc, S.f.comm_assoc, ← S.g.comm_assoc, hfr, hsg', hz',
    comp_zero, Int.negOnePow_one, Units.neg_smul, one_smul, add_zero]
  -- the identity left by `hfr` sits at `(eval C (up ℤ) (p+1)).obj S.X₁`, not at the spelling
  -- `S.X₁.X (p+1)` that `S.X₁.d p (p+1)` lands in, so `comp_id` cannot fire until `eval` unfolds
  dsimp only [HomologicalComplex.eval]
  rw [Category.comp_id]
  abel

lemma ofHom_homOfDegreewiseSplit (τ : ∀ n, (S.map (eval C (up ℤ) n)).Splitting) :
    Cochain.ofHom (homOfDegreewiseSplit S τ)
      = (cocycleOfDegreewiseSplit S τ).1.rightShift 1 0 (zero_add 1) := by
  simp [homOfDegreewiseSplit]

/-- **Stacks 011L**, part (2): the family `gⁿ` is a homotopy between the two connecting morphisms
`δ, δ' : C^• ⟶ A[1]^•` of tag 011J.

Part (1) is what makes this true with `g` rather than `h`: passing a `0`-cochain `C^• ⟶ A^•` to a
`(-1)`-cochain `C^• ⟶ A[1]^•` conjugates `δ` by `Cochain.δ_rightShift`'s `(-1)^1`, and that sign
is exactly the one relating `g` to `h`. -/
@[stacks 011L "(2)"]
noncomputable def homotopyHomOfDegreewiseSplit :
    Homotopy (homOfDegreewiseSplit S σ') (homOfDegreewiseSplit S σ) :=
  (Cochain.equivHomotopy _ _).symm
    ⟨(Cochain.ofHoms (retractionSubHom S σ σ')).rightShift 1 (-1) (by lia), by
      rw [ofHom_homOfDegreewiseSplit, ofHom_homOfDegreewiseSplit,
        Cochain.δ_rightShift _ 1 (-1) 0 (by lia) 1 (by lia)]
      have hofHoms : Cochain.ofHoms (retractionSubHom S σ σ')
          = -Cochain.ofHoms (sectionSubHom S σ σ') := by
        ext p
        simp [retractionSubHom_eq_neg]
      rw [hofHoms, δ_neg, Cochain.rightShift_neg, ← cocycleOfDegreewiseSplit_sub, sub_eq_add_neg,
        Cochain.rightShift_add, Cochain.rightShift_neg]
      simp⟩

end

variable {C : Type u} [Category.{v} C] [Abelian C]

/- The statement below mixes two spellings of the same objects, and without these the two sides
never unify: `Functor.shiftIso`, `homologyFunctor` and `Functor.shift` stand between
`H^i(S.X₁⟦1⟧)` and the shifted homology functor, while `eval` and `ShortComplex.map` stand
between `(S.map (eval _ n)).X₃` — the type of the splitting's own fields — and `S.X₃.X n`.
Together they replace the two `set_option backward.*` that Mathlib carries on the analogous
declarations in this file. `ShortComplex.map` needs full `reducible` rather than
`implicit_reducible`, because it has to be visible to `simp`'s term indexing and not merely to
unification. `eval` needs `allowUnsafeReducibility`: Mathlib marks it `@[implicit_reducible]`,
and raising that to `instance_reducible` counts as an unsafe change of status. -/
attribute [local implicit_reducible] Functor.shiftIso homologyFunctor Functor.shift in
set_option allowUnsafeReducibility true in
attribute [local instance_reducible] HomologicalComplex.eval in
attribute [local reducible] ShortComplex.map in
/-- **Stacks 011K.** The morphism `δ : C^• → A[1]^•` attached to a degreewise split short exact
sequence induces on cohomology exactly the connecting map of the long exact sequence of 0117,
under the identification `H^i(A[1]^•) = H^{i+1}(A^•)` of tag 011H.

The proof is a diagram chase on the tautological cycle: `δ_eq` computes the connecting map from
any lift of a cycle of `C^•` along `B^• → C^•`, the splitting provides that lift as `(σ i).s`, and
`liftCycles_shift_homologyπ` moves the result across the shift identification. -/
@[stacks 011K]
theorem homologyMap_homOfDegreewiseSplit (S : ShortComplex (CochainComplex C ℤ))
    (σ : ∀ n, (S.map (eval C (up ℤ) n)).Splitting) (hS : S.ShortExact)
    (i j : ℤ) (hij : (up ℤ).Rel i j) (h : 1 + i = j) :
    HomologicalComplex.homologyMap (homOfDegreewiseSplit S σ) i ≫
        ((homologyFunctor C (up ℤ) 0).shiftIso 1 i j h).hom.app S.X₁ =
      hS.δ i j hij := by
  have hnext : (up ℤ).next i = j := (up ℤ).next_eq' hij
  have hnextj : (up ℤ).next j = j + 1 := by simp
  -- The splitting identities, read at `S.Xₖ.X n` rather than at `(S.map (eval _ n)).Xₖ`.
  have hs : (σ i).s ≫ S.g.f i = 𝟙 (S.X₃.X i) := (σ i).s_g
  have hr : (σ j).r ≫ S.f.f j = 𝟙 (S.X₂.X j) - S.g.f j ≫ (σ j).s := (σ j).r_f
  -- We chase the tautological cycle of `S.X₃` in degree `i`, which is `iCycles` itself.
  have hlift : S.X₃.liftCycles (S.X₃.iCycles i) j hnext (by simp) = 𝟙 _ := by
    rw [← cancel_mono (S.X₃.iCycles i)]; simp
  -- `(σ i).s` lifts it along `S.g` ...
  have hx₂ : (S.X₃.iCycles i ≫ (σ i).s) ≫ S.g.f i = S.X₃.iCycles i := by
    rw [Category.assoc, hs, comp_id]
  -- ... and `(σ j).r` retracts `d` of that lift back into `S.X₁`, the second term of `r_f`
  -- vanishing because `S.g` is a chain map and we started from a cycle.
  have hx₁ : (S.X₃.iCycles i ≫ (σ i).s ≫ S.X₂.d i j ≫ (σ j).r) ≫ S.f.f j
      = (S.X₃.iCycles i ≫ (σ i).s) ≫ S.X₂.d i j := by
    rw [Category.assoc, Category.assoc, Category.assoc, hr, Preadditive.comp_sub, comp_id,
      ← S.g.comm_assoc]
    simp only [Preadditive.comp_sub]
    rw [reassoc_of% hs]
    -- `eval` is only `instance_reducible` above, so `simp` needs it named to reach `iCycles_d`.
    simp [eval]
  -- So `δ_eq` evaluates the connecting map on that cycle.
  have hδ := hS.δ_eq i j hij (S.X₃.iCycles i) (by simp)
    (S.X₃.iCycles i ≫ (σ i).s) hx₂
    (S.X₃.iCycles i ≫ (σ i).s ≫ S.X₂.d i j ≫ (σ j).r) hx₁ (j + 1) hnextj
  rw [hlift, id_comp] at hδ
  -- Both sides are maps out of `H^i(S.X₃)`, so it is enough to compare them after `homologyπ`.
  rw [← cancel_epi (S.X₃.homologyπ i), hδ]
  conv_lhs => rw [← id_comp (S.X₃.homologyπ i), ← hlift]
  rw [Category.assoc, homologyπ_naturality_assoc, liftCycles_comp_cyclesMap_assoc]
  conv_lhs => rw [← Category.assoc]
  rw [liftCycles_shift_homologyπ (i' := j) (hi' := h) (j' := j + 1) (hj' := hnextj)]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  -- What is left is that the two cocycles of `S.X₁` agree.
  obtain rfl : j = i + 1 := hij.symm
  simp [homOfDegreewiseSplit_f, cocycleOfDegreewiseSplit, Functor.shift,
    Functor.ShiftSequence.sequence, homologyFunctor]

end CochainComplex
