module

public import StacksCore.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksCore.Algebra.Homology.HomotopyCategory.Shift

/-! # The connecting morphism of a degreewise split sequence of chain complexes

Stacks tags 011D, 011E and 011F, the chain-complex twins of 011J, 011K and 011L. Given a complex
`0 → A_• → B_• → C_• → 0` of chain complexes together with splittings `B_n = A_n ⊕ C_n` compatible
with its maps, the family `π_{n-1} ∘ d_{B,n} ∘ s_n` defines a morphism of complexes
`δ : C_• → A[-1]_•` (011D), the map it induces on homology is the connecting map of the long exact
sequence of 0111 (011E), and `δ` depends on the splittings only up to homotopy (011F).

011E is stated through `ChainComplex.homologyShiftIso` rather than through `Functor.shiftIso`,
which would require a `(homologyFunctor C (down ℤ) 0).ShiftSequence ℤ` instance that the chain
side does not have. Registering one is possible, but it buys only spelling parity with the cochain
twin 011K -- `ChainComplex.shiftIso` (011B) already is the natural isomorphism the statement
wants. The single lemma 011E rests on is `ChainComplex.liftCycles_homologyπ_homologyShiftIso`, the
chain twin of `CochainComplex.liftCycles_shift_homologyπ`.

Nothing of Mathlib's cochain construction can be reused. `CochainComplex.homOfDegreewiseSplit` is
built on the `CochainComplex.HomComplex` tower -- `Cochain`, `Cocycle`, `Cochain.δ`,
`Cochain.rightShift` -- whose index convention `p + n = q` is `ComplexShape.up ℤ` by construction,
and which has no chain analogue. That tower is however pure bookkeeping: `Cocycle.homOf` shows
that a `0`-cocycle *is* a `HomologicalComplex.Hom`, so on the chain side `δ` is built directly as
one, and no intermediate cocycle-like object is introduced. The mathematical content is a single
identity, the Stacks proof's first display, isolated here as
`homOfDegreewiseSplit_f_comp_f`.

The minus sign at the end of the Stacks proof of 011D does not survive into the Lean statement:
it is exactly the `(-1)^{-1}` of `ChainComplex.shiftFunctor` (011A), so `δ` satisfies the chain-map
condition on the nose, with no sign in its components. Without the `(-1)^k` of 011A the tag would
be false as stated, exactly as for 011C.

## The spelling of the splittings

A degreewise splitting is a `(S.map (eval C (down ℤ) n)).Splitting`, so its fields `s` and `r` are
typed at `(S.map (eval C (down ℤ) n)).X₃` and friends, whereas everything else in sight is typed
at `S.X₃.X n`. The two are definitionally equal but not syntactically equal, and the mismatch
lands in the *middle object* of every composition built from them, where no type ascription can
reach it; `Category.assoc` then fails to fire. The cochain half of this file works around it with
`attribute [local reducible] ShortComplex.map` under `set_option allowUnsafeReducibility true`.

Here the fix is instead `sectionHom` and `retractionHom`: thin definitions whose *declared* type
is the good spelling. Because they are declared, the good spelling is what the elaborator writes
into every composition, and their identities (`sectionHom_g`, `f_retractionHom`, `retractionHom_f`,
`mono_f_f`, ...) transfer from `ShortComplex.Splitting` by plain definitional unfolding, with no
tactic at all. This costs two definitions and buys 011D, 011E and 011F with zero `set_option` and
zero `erw` -- where the cochain half of this family needs `allowUnsafeReducibility`. The device
does not reach everywhere: `ShortComplex.liftCycles` takes the offending spelling in the *type of
an argument*, which no declared type can respell, so
`ChainComplex.liftCycles_homologyπ_homologyShiftIso` still needs one scoped
`implicit_reducible`.
-/

@[expose] public section

open CategoryTheory Category ComplexShape Limits HomologicalComplex
open CategoryTheory.ShortComplex.Splitting

universe v u

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The differential of the `(-1)`-shift, with the sign of 011A discharged and every index in the
`- 1` spelling that `ComplexShape.down` normalises to. The `(-1 : ℤˣ) • _` of
`shiftFunctor_obj_d'` is not syntactically a negation, so this has to be rewritten before any
step that expects to see `-d`. -/
lemma shiftFunctor_neg_one_obj_d (K : ChainComplex C ℤ) (i j : ℤ) :
    (K⟦(-1 : ℤ)⟧).d i j = -K.d (i - 1) (j - 1) := by
  rw [shiftFunctor_obj_d', show (-1 : ℤ).negOnePow = -1 from rfl, Units.neg_smul, one_smul]
  rfl

variable (S : ShortComplex (ChainComplex C ℤ))
  (σ σ' : ∀ n, (S.map (eval C (down ℤ) n)).Splitting)

/-! ## The splittings, respelled -/

/-- The section `s_n : C_n ⟶ B_n` of a degreewise splitting, declared at the spelling
`S.X₃.X n ⟶ S.X₂.X n`. -/
def sectionHom (n : ℤ) : S.X₃.X n ⟶ S.X₂.X n := (σ n).s

/-- The projection `π_n : B_n ⟶ A_n` of a degreewise splitting, declared at the spelling
`S.X₂.X n ⟶ S.X₁.X n`; this is the `π_n` that Stacks 011D obtains from 010G. -/
def retractionHom (n : ℤ) : S.X₂.X n ⟶ S.X₁.X n := (σ n).r

/-- The composite `A_n → B_n → C_n` vanishes, degreewise. -/
@[reassoc (attr := simp)]
lemma f_f_comp_g_f (n : ℤ) : S.f.f n ≫ S.g.f n = 0 := (S.map (eval C (down ℤ) n)).zero

/-- `s_n` is a section of `B_n → C_n`. -/
@[reassoc (attr := simp)]
lemma sectionHom_g (n : ℤ) : sectionHom S σ n ≫ S.g.f n = 𝟙 _ := (σ n).s_g

/-- `π_n` is a retraction of `A_n → B_n`. -/
@[reassoc (attr := simp)]
lemma f_retractionHom (n : ℤ) : S.f.f n ≫ retractionHom S σ n = 𝟙 _ := (σ n).f_r

/-- `π_n ∘ s_n = 0`. -/
@[reassoc (attr := simp)]
lemma sectionHom_retractionHom (n : ℤ) : sectionHom S σ n ≫ retractionHom S σ n = 0 := (σ n).s_r

/-- `i_n ∘ π_n = id - s_n ∘ q_n`, the identity the Stacks proof of 011D opens with, read in
diagrammatic order. -/
@[reassoc]
lemma retractionHom_f (n : ℤ) :
    retractionHom S σ n ≫ S.f.f n = 𝟙 _ - S.g.f n ≫ sectionHom S σ n := (σ n).r_f

/-- The defining identity of a splitting, degreewise. -/
lemma retractionHom_f_add_g_sectionHom (n : ℤ) :
    retractionHom S σ n ≫ S.f.f n + S.g.f n ≫ sectionHom S σ n = 𝟙 _ := (σ n).id

include σ in
/-- A degreewise splitting makes each `A_n → B_n` a monomorphism; this is the one place the
Stacks proof of 011D uses exactness, and it is free from the splitting. -/
lemma mono_f_f (n : ℤ) : Mono (S.f.f n) := (σ n).mono_f

include σ in
/-- A degreewise splitting makes each `B_n → C_n` an epimorphism. -/
lemma epi_g_f (n : ℤ) : Epi (S.g.f n) := (σ n).epi_g

/-! ## Tag 011D -/

/-- **Stacks 011D.** The morphism of complexes `δ(s) : C_• ⟶ A[-1]_•` attached to a degreewise
split complex of chain complexes, with components `π_{n-1} ∘ d_{B,n} ∘ s_n` read in diagrammatic
order.

As for its cochain twin 011J, no exactness is needed: the splittings supply degreewise whatever
the Stacks statement asks of the short exact sequence, so the hypotheses are `Preadditive` and a
`ShortComplex`. The Stacks proof's trailing minus is supplied by `d_{A[-1]} = -d_A`, which is the
`k = -1` case of the `(-1)^k` of 011A. -/
@[stacks 011D "the morphism `δ(s) : C_• → A[-1]_•` itself."]
def homOfDegreewiseSplit : S.X₃ ⟶ S.X₁⟦(-1 : ℤ)⟧ where
  f n := sectionHom S σ n ≫ S.X₂.d n (n - 1) ≫ retractionHom S σ (n - 1)
  comm' i j (hij : j + 1 = i) := by
    obtain rfl : j = i - 1 := by lia
    have := mono_f_f S σ (i - 1 - 1)
    rw [shiftFunctor_neg_one_obj_d, ← cancel_mono (S.f.f (i - 1 - 1))]
    simp only [assoc, Preadditive.comp_neg, Preadditive.neg_comp, ← S.f.comm (i - 1) (i - 1 - 1),
      retractionHom_f, retractionHom_f_assoc, Preadditive.comp_sub, Preadditive.sub_comp,
      comp_id, id_comp, d_comp_d, d_comp_d_assoc, zero_comp, sub_zero, zero_sub,
      neg_neg, ← S.g.comm_assoc, sectionHom_g_assoc]

/-- The components of `δ(s)`, `δ(s)_n = π_{n-1} ∘ d_{B,n} ∘ s_n`. Writing the definition at the
index `n - 1`, which is what `(ComplexShape.down ℤ).next` normalises to, makes this hold by `rfl`
with no `XIsoOfEq` in sight. -/
@[stacks 011D "its components, `δ(s)_n = π_{n-1} ∘ d_{B,n} ∘ s_n`.", simp]
lemma homOfDegreewiseSplit_f (n : ℤ) :
    (homOfDegreewiseSplit S σ).f n
      = sectionHom S σ n ≫ S.X₂.d n (n - 1) ≫ retractionHom S σ (n - 1) := rfl

/-- The first displayed equation of the Stacks proof of 011D,
`i_{n-1} ∘ π_{n-1} ∘ d_{B,n} ∘ s_n = d_{B,n} ∘ s_n - s_{n-1} ∘ d_{C,n}`.

This says that `δ(s)_n`, pushed into `B_{n-1}`, is `d_B ∘ s` corrected by a term that vanishes on
cycles, which is exactly the hypothesis `x₁ ∘ i = x₂ ∘ d` of `ShortComplex.ShortExact.δ_eq`. It is
therefore the form in which 011E consumes 011D. -/
@[reassoc]
lemma homOfDegreewiseSplit_f_comp_f (n : ℤ) :
    (homOfDegreewiseSplit S σ).f n ≫ S.f.f (n - 1)
      = sectionHom S σ n ≫ S.X₂.d n (n - 1) - S.X₃.d n (n - 1) ≫ sectionHom S σ (n - 1) := by
  rw [homOfDegreewiseSplit_f]
  simp only [assoc, retractionHom_f, Preadditive.comp_sub, comp_id, ← S.g.comm_assoc,
    sectionHom_g_assoc]

/-! ## Tag 011F: dependence on the splittings -/

/-- The family `h_n : C_n ⟶ A_n` of Stacks 011F, with `s'_n = s_n + i_n ∘ h_n`. -/
def sectionSubHom (n : ℤ) : S.X₃.X n ⟶ S.X₁.X n := sectionSub (σ n) (σ' n)

/-- The family `g_n : C_n ⟶ A_n` by which the two projections differ, with
`π'_n = π_n + g_n ∘ q_n`. -/
def retractionSubHom (n : ℤ) : S.X₃.X n ⟶ S.X₁.X n := retractionSub (σ n) (σ' n)

/-- `s'_n = s_n + i_n ∘ h_n`, which is the sentence of Stacks 011F defining `h`; `h` is unique by
`ShortComplex.Splitting.sectionSub_unique`. -/
lemma sectionHom_eq_add (n : ℤ) :
    sectionHom S σ' n = sectionHom S σ n + sectionSubHom S σ σ' n ≫ S.f.f n :=
  s_eq_add_sectionSub (σ n) (σ' n)

/-- `π'_n = π_n + g_n ∘ q_n`. -/
lemma retractionHom_eq_add (n : ℤ) :
    retractionHom S σ' n = retractionHom S σ n + S.g.f n ≫ retractionSubHom S σ σ' n :=
  r_eq_add_retractionSub (σ n) (σ' n)

/-- `g_n = -h_n`, the chain-complex reading of 011L(1). -/
lemma retractionSubHom_eq_neg (n : ℤ) :
    retractionSubHom S σ σ' n = -sectionSubHom S σ σ' n :=
  retractionSub_eq_neg_sectionSub (σ n) (σ' n)

/-- The two connecting morphisms of 011D differ, degreewise, by
`d_{C,n} ∘ h_{n-1} - h_n ∘ d_{A,n}`. This is the whole computational content of 011F; everything
after it is bookkeeping about the shift.

Note that both sides are stated at `(S.X₁⟦(-1 : ℤ)⟧).X n` rather than at `S.X₁.X (n - 1)`, so that
they match the `Homotopy` goal below without any respelling step. -/
lemma homOfDegreewiseSplit_f_sub (n : ℤ) :
    (homOfDegreewiseSplit S σ).f n - (homOfDegreewiseSplit S σ').f n
      = S.X₃.d n (n - 1) ≫ sectionSubHom S σ σ' (n - 1)
        - sectionSubHom S σ σ' n ≫ S.X₁.d n (n - 1) := by
  simp only [homOfDegreewiseSplit_f, sectionHom_eq_add S σ σ', retractionHom_eq_add S σ σ',
    retractionSubHom_eq_neg, Preadditive.add_comp, Preadditive.comp_add, Preadditive.comp_neg,
    assoc, ← S.g.comm_assoc, sectionHom_g_assoc, S.f.comm_assoc, f_retractionHom, comp_id,
    f_f_comp_g_f_assoc, zero_comp, comp_zero, add_zero]
  abel

/-- **Stacks 011F.** The family `h_n : C_n ⟶ A_n = A[-1]_{n+1}` is a homotopy between the
morphisms `δ(s)` and `δ(s')` of 011D attached to two choices of splittings.

Unlike its cochain twin 011L, this is stated with `h` and not with `g = -h`: a homotopy of chain
complexes has components `C_n ⟶ D_{n+1}`, and going from `D = A` to `D = A[-1]` shifts by `-1`
rather than by `+1`, which is the other sign. Concretely, `prevD` pairs `h_n` with
`d_{A[-1],n+1} = -d_{A,n}`, and that minus is what turns 011L's `g` into 011F's `h`. -/
@[stacks 011F]
def homotopyHomOfDegreewiseSplit :
    Homotopy (homOfDegreewiseSplit S σ) (homOfDegreewiseSplit S σ') where
  hom i j := if hij : i = j - 1 then
      sectionSubHom S σ σ' i ≫ (S.X₁.XIsoOfEq hij).hom else 0
  zero i j hij := dite_eq_right (fun h => hij (show i + 1 = j by lia))
  comm i := by
    rw [dNext_eq _ (show (down ℤ).Rel i (i - 1) by simp),
      prevD_eq _ (show (down ℤ).Rel (i + 1) i by simp),
      dite_eq_left (rfl : i - 1 = i - 1), dite_eq_left (show i = i + 1 - 1 by lia),
      shiftFunctor_neg_one_obj_d]
    have key := homOfDegreewiseSplit_f_sub S σ σ' i
    rw [sub_eq_iff_eq_add] at key
    simp only [XIsoOfEq_rfl, Iso.refl_hom, comp_id, assoc, Preadditive.comp_neg,
      XIsoOfEq_hom_comp_d]
    rw [key]
    abel

/-- The components of the homotopy of 011F are the `h_n`, up to the identification
`A[-1]_{n+1} = A_n`. -/
@[simp]
lemma homotopyHomOfDegreewiseSplit_hom (i j : ℤ) (hij : i = j - 1) :
    (homotopyHomOfDegreewiseSplit S σ σ').hom i j
      = sectionSubHom S σ σ' i ≫ (S.X₁.XIsoOfEq hij).hom :=
  dite_eq_left hij

section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **Stacks 011E.** The map `H_i(δ(s)) : H_i(C_•) ⟶ H_i(A[-1]_•) = H_{i-1}(A_•)` induced by the
morphism `δ(s)` of 011D is the connecting morphism of the long exact homology sequence of 0111.

There is no sign: the identification of 011B is the unsigned re-indexing, because the `(-1)^k` of
the shift sits on the outer two terms of the short complex and homology is cut out by the middle
one. The opposite convention is not merely unproved but false — it forces every such connecting
map to be `2`-torsion.

The identification is taken through `ChainComplex.homologyShiftIso` rather than through
`Functor.shiftIso`, which would need a `(homologyFunctor C (ComplexShape.down ℤ) 0).ShiftSequence ℤ`
instance that the chain side does not have. Registering one is possible but buys only spelling
parity with the cochain twin 011K: `ChainComplex.shiftIso` already *is* the natural isomorphism
the statement wants. -/
@[stacks 011E]
theorem homologyMap_homOfDegreewiseSplit (S : ShortComplex (ChainComplex C ℤ))
    (σ : ∀ n, (S.map (eval C (down ℤ) n)).Splitting) (hS : S.ShortExact)
    (i j : ℤ) (hij : (down ℤ).Rel i j) (h : i + -1 = j) :
    HomologicalComplex.homologyMap (homOfDegreewiseSplit S σ) i ≫
        (homologyShiftIso S.X₁ (-1) i j h).hom =
      hS.δ i j hij := by
  obtain rfl : j = i - 1 := by lia
  have hnext : (down ℤ).next i = i - 1 := (down ℤ).next_eq' hij
  -- We chase the tautological cycle of `S.X₃` in degree `i`, which is `iCycles` itself.
  have hlift : S.X₃.liftCycles (S.X₃.iCycles i) (i - 1) hnext (by simp) = 𝟙 _ := by
    rw [← cancel_mono (S.X₃.iCycles i)]; simp
  -- `s_i` lifts it along `S.g` ...
  have hx₂ : (S.X₃.iCycles i ≫ sectionHom S σ i) ≫ S.g.f i = S.X₃.iCycles i := by
    rw [assoc, sectionHom_g, comp_id]
  -- ... and `δ(s)_i` is the resulting element of `S.X₁`, by the first display of the 011D proof.
  have hx₁ : (S.X₃.iCycles i ≫ (homOfDegreewiseSplit S σ).f i) ≫ S.f.f (i - 1)
      = (S.X₃.iCycles i ≫ sectionHom S σ i) ≫ S.X₂.d i (i - 1) := by
    rw [assoc, homOfDegreewiseSplit_f_comp_f, Preadditive.comp_sub, assoc]
    simp
  -- So `δ_eq` evaluates the connecting map on that cycle.
  have hδ := hS.δ_eq i (i - 1) hij (S.X₃.iCycles i) (by simp)
    (S.X₃.iCycles i ≫ sectionHom S σ i) hx₂
    (S.X₃.iCycles i ≫ (homOfDegreewiseSplit S σ).f i) hx₁ (i - 1 - 1) (by simp)
  rw [hlift, id_comp] at hδ
  -- Both sides are maps out of `H_i(S.X₃)`, so it is enough to compare them after `homologyπ`.
  rw [← cancel_epi (S.X₃.homologyπ i), hδ]
  conv_lhs => rw [← id_comp (S.X₃.homologyπ i), ← hlift]
  rw [assoc, homologyπ_naturality_assoc, liftCycles_comp_cyclesMap_assoc,
    liftCycles_homologyπ_homologyShiftIso (i' := i - 1) (hi' := h) (j' := i - 1 - 1)
      (hj' := by simp)]
  -- What is left is that the two cycles of `S.X₁` agree.
  congr 1
  rw [← cancel_mono (S.X₁.iCycles (i - 1)), liftCycles_i, liftCycles_i]
  exact comp_id _

end

end ChainComplex
