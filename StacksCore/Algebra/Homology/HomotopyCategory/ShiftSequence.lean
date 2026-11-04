module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.Refinements
import StacksCore.Tactic.StacksAttribute

/-! # Cohomology of a shifted cochain complex, and the shifted connecting map

Stacks tag 011H, the identification `H^{i+k}(A^•) = H^i(A[k]^•)` coming from `A^{i+k} = A[k]^i`,
and the third clause of tag 0117, which asserts that the long exact cohomology sequence is
compatible with shifts *as in* that identification. The chain-complex twin of 011H, tag 011B, is
in `StacksCore.Algebra.Homology.HomotopyCategory.Shift`.

The Stacks project stresses that no signs enter the identification 011H, and Mathlib agrees. The
shift does multiply differentials by `(-1)^k` (tag 011G), and that sign duly appears on the outer
two terms of `CochainComplex.shiftShortComplexFunctorIso`; but the middle term, which is what cuts
out homology as a subquotient, is the unsigned `HomologicalComplex.XIsoOfEq`. So the induced map
on homology is the plain re-indexing.

Note the direction. Mathlib's `shiftIso C k i i' (h : k + i = i')` has
`hom.app K : H^i(A[k]^•) ⟶ H^{i'}(A^•)`, whereas the Stacks project writes the arrow the other
way, `H^{i+k}(A^•) → H^i(A[k]^•)`. That is `.inv`. Being an isomorphism it carries the tag either
way, since an identification has no preferred direction.

**The 0117 clause is not sign-free, although the Stacks project's wording suggests it is.** Its
proof says only "compatibility with shifts is immediate from the definitions". But the shift
signs differentials while the identification above does not, so the long exact sequence of `A[k]`
and the reindexed long exact sequence of `A` agree on the two functorial maps and differ by
`(-1)^k` on the connecting map — that is `shiftIso_hom_app_comp_δ` below. The sign enters in one
place only: `S.f` is a monomorphism, so the witness in `ShortComplex.ShortExact.δ_eq` is unique,
and the witness for the shifted sequence is `(-1)^k` times the witness for the original.
-/

@[expose] public section

open CategoryTheory Category Limits ComplexShape HomologicalComplex

universe v u

add_to_stacks 011H "the identification itself, as an isomorphism of functors; the Stacks arrow
`H^{i+k}(A^•) → H^i(A[k]^•)` is its `.inv` component."
  CochainComplex.ShiftSequence.shiftIso

add_to_stacks 011H "that the identification really is the plain re-indexing: it is the map induced
on homology by an isomorphism of short complexes whose middle component is unsigned."
  CochainComplex.ShiftSequence.shiftIso_hom_app

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Transporting a cocycle across the shift identification turns the shifted differential into
`(-1)^n` times the unshifted one. -/
lemma d_shift_transport (K : CochainComplex C ℤ) {A : C} (n i j i' j' : ℤ)
    (hi' : i' = i + n) (hj' : j' = j + n) (f : A ⟶ (K⟦n⟧).X i) :
    (f ≫ (K.shiftFunctorObjXIso n i i' hi').hom) ≫ K.d i' j'
      = n.negOnePow • ((f ≫ (K⟦n⟧).d i j) ≫ (K.shiftFunctorObjXIso n j j' hj').hom) := by
  subst hi' hj'
  change A ⟶ K.X (i + n) at f
  simp [smul_smul]

/-- The sign in `d_shift_transport` is invisible to a cocycle: the transport of a cocycle is a
cocycle. -/
lemma d_shift_transport_eq_zero (K : CochainComplex C ℤ) {A : C} (n i j i' j' : ℤ)
    (hi' : i' = i + n) (hj' : j' = j + n) (f : A ⟶ (K⟦n⟧).X i) (hf : f ≫ (K⟦n⟧).d i j = 0) :
    (f ≫ (K.shiftFunctorObjXIso n i i' hi').hom) ≫ K.d i' j' = 0 := by
  rw [d_shift_transport K n i j i' j' hi' hj' f, hf, zero_comp, smul_zero]

-- attribute [local implicit_reducible] Functor.shift homologyFunctor in
/-- Transporting across the shift identification is natural in the complex, and unsigned. -/
lemma map_shift_transport {K L : CochainComplex C ℤ} (φ : K ⟶ L) {A : C} (n i i' : ℤ)
    (hi' : i' = i + n) (f : A ⟶ (K⟦n⟧).X i) :
    (f ≫ (K.shiftFunctorObjXIso n i i' hi').hom) ≫ φ.f i'
      = (f ≫ (φ⟦n⟧').f i) ≫ (L.shiftFunctorObjXIso n i i' hi').hom := by
  subst hi'
  change A ⟶ K.X (i + n) at f
  simp

/-- `liftCycles` is homogeneous for the action of units on cocycles. -/
lemma liftCycles_units_smul (K : CochainComplex C ℤ) {A : C} (u : ℤˣ) (n m : ℤ)
    (hm : (up ℤ).next n = m) (w : A ⟶ K.X n) (hw : w ≫ K.d n m = 0)
    (hw' : (u • w) ≫ K.d n m = 0) :
    K.liftCycles (u • w) m hm hw' = u • K.liftCycles w m hm hw := by
  rw [← cancel_mono (K.iCycles n)]
  simp [Linear.units_smul_comp]

attribute [local implicit_reducible] Functor.shift homologyFunctor in
/-- The identification of tag 011H sends the cohomology class of a cocycle of `K⟦n⟧` to the class
of its transport to `K`. This is Mathlib's `liftCycles_shift_homologyπ` with the identification
turned round to the direction every use below wants. -/
@[reassoc]
lemma liftCycles_homologyπ_shiftIso_hom_app (K : CochainComplex C ℤ) {A : C} {n i : ℤ}
    (f : A ⟶ (K⟦n⟧).X i) (j : ℤ) (hj : (up ℤ).next i = j) (hf : f ≫ (K⟦n⟧).d i j = 0)
    (i' : ℤ) (hi' : n + i = i') (j' : ℤ) (hj' : (up ℤ).next i' = j')
    (hf' : (f ≫ (K.shiftFunctorObjXIso n i i' (by lia)).hom) ≫ K.d i' j' = 0) :
    (K⟦n⟧).liftCycles f j hj hf ≫ (K⟦n⟧).homologyπ i ≫
        ((homologyFunctor C (up ℤ) 0).shiftIso n i i' hi').hom.app K =
      K.liftCycles (f ≫ (K.shiftFunctorObjXIso n i i' (by lia)).hom) j' hj' hf' ≫
        K.homologyπ i' := by
  rw [K.liftCycles_shift_homologyπ_assoc f j hj hf i' hi' j' hj', Iso.inv_hom_id_app]
  -- the identity is at `((homologyFunctor C (up ℤ) 0).shift i').obj K`, which is `K.homology i'`
  -- only once those three definitions are unfolded; until then `comp_id` cannot fire
  dsimp only [Functor.shift, Functor.ShiftSequence.sequence, homologyFunctor]
  rw [Category.comp_id]

/-- `ShortComplex.ShortExact.δ_eq` for `S`, read off from witnesses living on the shifted sequence
`S⟦k⟧`: transporting the witnesses of `δ` for `S⟦k⟧` gives witnesses of `δ` for `S`, except that
the one in `S.X₁` picks up `(-1)^k`.

This is where the sign of `shiftIso_hom_app_comp_δ` is born, and it is forced: `S.f` is a
monomorphism, so the `S.X₁`-witness is unique, and `d_shift_transport` says that transporting the
`S.X₂`-witness across the shift multiplies the differential by `(-1)^k`. -/
private lemma δ_eq_of_shift (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact) (k i j : ℤ)
    (hij' : (up ℤ).Rel (i + k) (j + k)) {A : C}
    (x₃ : A ⟶ (S.X₃⟦k⟧).X i) (hx₃ : x₃ ≫ (S.X₃⟦k⟧).d i j = 0)
    (x₂ : A ⟶ (S.X₂⟦k⟧).X i) (hx₂ : x₂ ≫ (S.g⟦k⟧').f i = x₃)
    (x₁ : A ⟶ (S.X₁⟦k⟧).X j) (hx₁ : x₁ ≫ (S.f⟦k⟧').f j = x₂ ≫ (S.X₂⟦k⟧).d i j)
    (hx₁z : x₁ ≫ (S.X₁⟦k⟧).d j (j + 1) = 0) :
    S.X₃.liftCycles (x₃ ≫ (S.X₃.shiftFunctorObjXIso k i (i + k) rfl).hom) (j + k)
          ((up ℤ).next_eq' hij')
          (S.X₃.d_shift_transport_eq_zero k i j (i + k) (j + k) rfl rfl x₃ hx₃) ≫
        S.X₃.homologyπ (i + k) ≫ hS.δ (i + k) (j + k) hij' =
      k.negOnePow • (S.X₁.liftCycles (x₁ ≫ (S.X₁.shiftFunctorObjXIso k j (j + k) rfl).hom)
            (j + k + 1) (by simp)
            (S.X₁.d_shift_transport_eq_zero k j (j + 1) (j + k) (j + k + 1) rfl (by lia)
              x₁ hx₁z) ≫
          S.X₁.homologyπ (j + k)) := by
  have hz := S.X₁.d_shift_transport_eq_zero k j (j + 1) (j + k) (j + k + 1) rfl (by lia) x₁ hx₁z
  have hx₂' : (x₂ ≫ (S.X₂.shiftFunctorObjXIso k i (i + k) rfl).hom) ≫ S.g.f (i + k)
      = x₃ ≫ (S.X₃.shiftFunctorObjXIso k i (i + k) rfl).hom := by
    rw [map_shift_transport S.g k i (i + k) rfl, hx₂]
  have hx₁' : (k.negOnePow • (x₁ ≫ (S.X₁.shiftFunctorObjXIso k j (j + k) rfl).hom)) ≫
        S.f.f (j + k)
      = (x₂ ≫ (S.X₂.shiftFunctorObjXIso k i (i + k) rfl).hom) ≫ S.X₂.d (i + k) (j + k) := by
    rw [Linear.units_smul_comp, map_shift_transport S.f k j (j + k) rfl, hx₁,
      d_shift_transport S.X₂ k i j (i + k) (j + k) rfl rfl]
  rw [hS.δ_eq (i + k) (j + k) hij' _ _ _ hx₂' _ hx₁' (j + k + 1) (by simp),
    liftCycles_units_smul S.X₁ k.negOnePow (j + k) (j + k + 1) (by simp) _ hz,
    Linear.units_smul_comp]

attribute [local implicit_reducible] Functor.shift homologyFunctor in
set_option allowUnsafeReducibility true in
attribute [local reducible] ShortComplex.map in
/-- **Stacks 0117**, third clause: the long exact cohomology sequence is compatible with shifts,
in the sense of the identification `H^{i+k}(A^•) = H^i(A[k]^•)` of Definition 12.14.8 (tag 011H).

The two functorial maps of the sequence are unsigned, but the connecting map picks up `(-1)^k`.
The Stacks project's proof says "compatibility with shifts is immediate from the definitions" and
records no sign; with its own conventions there is one, because 011G shifts differentials by
`(-1)^k` while the 011H identification is the plain unsigned re-indexing. `δ_eq_of_shift` is where
that sign appears.

`shiftIso_hom_app_comp_δ'` is the same statement with the short exactness of the shifted sequence
derived rather than assumed. -/
@[stacks 0117 "third clause, compatibility with shifts; note the `(-1)^k`, which the Stacks
wording does not lead one to expect"]
theorem shiftIso_hom_app_comp_δ (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (k i j i' j' : ℤ) (hij : (up ℤ).Rel i j) (hij' : (up ℤ).Rel i' j')
    (hi' : k + i = i') (hj' : k + j = j')
    (hS' : (S.map (CategoryTheory.shiftFunctor (CochainComplex C ℤ) k)).ShortExact) :
    ((homologyFunctor C (up ℤ) 0).shiftIso k i i' hi').hom.app S.X₃ ≫ hS.δ i' j' hij' =
      k.negOnePow • (hS'.δ i j hij ≫
        ((homologyFunctor C (up ℤ) 0).shiftIso k j j' hj').hom.app S.X₁) := by
  obtain rfl : i' = i + k := by lia
  obtain rfl : j' = j + k := by lia
  have hdeg := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 hS'
  have hepi : Epi ((S.g⟦k⟧').f i) := (hdeg i).epi_g
  have hmonoj := (hdeg j).mono_f
  have hmono1 : Mono ((S.f⟦k⟧').f (j + 1)) := (hdeg (j + 1)).mono_f
  /- The witnesses that `ShortComplex.ShortExact.δ_eq` asks for, for the shifted sequence: a
  refinement `ϖ` of the tautological cocycle of `S.X₃⟦k⟧` in degree `i` along the degreewise
  epimorphism `S.g⟦k⟧'`, its lift `x₂` to `S.X₂⟦k⟧`, and the lift `x₁` of `x₂ ≫ d` to
  `S.X₁⟦k⟧`. -/
  obtain ⟨A, ϖ, hϖ, x₂, hx₂⟩ :=
    surjective_up_to_refinements_of_epi ((S.g⟦k⟧').f i) ((S.X₃⟦k⟧).iCycles i)
  set x₃ := ϖ ≫ (S.X₃⟦k⟧).iCycles i with hx₃def
  have hx₃ : x₃ ≫ (S.X₃⟦k⟧).d i j = 0 := by rw [hx₃def, Category.assoc, iCycles_d, comp_zero]
  have hx₂d : (x₂ ≫ (S.X₂⟦k⟧).d i j) ≫ (S.g⟦k⟧').f j = 0 := by
    rw [Category.assoc, ← (S.g⟦k⟧').comm i j, ← reassoc_of% hx₂, hx₃]
  obtain ⟨x₁, hx₁⟩ : ∃ x₁ : A ⟶ (S.X₁⟦k⟧).X j, x₁ ≫ (S.f⟦k⟧').f j = x₂ ≫ (S.X₂⟦k⟧).d i j :=
    (hdeg j).exact.lift' (x₂ ≫ (S.X₂⟦k⟧).d i j) hx₂d
  have hx₁z : x₁ ≫ (S.X₁⟦k⟧).d j (j + 1) = 0 := by
    rw [← cancel_mono ((S.f⟦k⟧').f (j + 1)), Category.assoc, ← (S.f⟦k⟧').comm j (j + 1),
      reassoc_of% hx₁, d_comp_d, comp_zero, zero_comp]
  -- Both sides are maps out of `H^i(S.X₃⟦k⟧)`, and `ϖ ≫ homologyπ i` is an epimorphism onto it.
  have hlift : (S.X₃⟦k⟧).liftCycles x₃ j ((up ℤ).next_eq' hij) hx₃ = ϖ := by
    rw [← cancel_mono ((S.X₃⟦k⟧).iCycles i), liftCycles_i, hx₃def]
  refine (cancel_epi (ϖ ≫ (S.X₃⟦k⟧).homologyπ i)).1 ?_
  rw [← hlift]
  simp only [Linear.comp_units_smul, Category.assoc]
  rw [-- left: move the class down to `S.X₃`, then read off `δ` of `S` — and with it the sign
    S.X₃.liftCycles_homologyπ_shiftIso_hom_app_assoc x₃ j ((up ℤ).next_eq' hij) hx₃ (i + k) hi'
      (j + k) ((up ℤ).next_eq' hij')
      (S.X₃.d_shift_transport_eq_zero k i j (i + k) (j + k) rfl rfl x₃ hx₃),
    δ_eq_of_shift S hS k i j hij' x₃ hx₃ x₂ hx₂.symm x₁ hx₁ hx₁z,
    -- right: read off `δ` of `S⟦k⟧`, then move the class down to `S.X₁`
    reassoc_of% (hS'.δ_eq i j hij x₃ hx₃ x₂ hx₂.symm x₁ hx₁ (j + 1) (next ℤ j)),
    S.X₁.liftCycles_homologyπ_shiftIso_hom_app x₁ (j + 1) (next ℤ j) hx₁z (j + k) hj' (j + k + 1)
      (next ℤ (j + k)) (S.X₁.d_shift_transport_eq_zero k j (j + 1) (j + k) (j + k + 1) rfl (by lia)
        x₁ hx₁z)]

/-- **Stacks 0117**, third clause, with the short exactness of the shifted sequence produced
internally rather than assumed. -/
@[stacks 0117 "third clause, self-contained form"]
lemma shiftIso_hom_app_comp_δ' (S : ShortComplex (CochainComplex C ℤ)) (hS : S.ShortExact)
    (k i j i' j' : ℤ) (hij : (up ℤ).Rel i j) (hij' : (up ℤ).Rel i' j')
    (hi' : k + i = i') (hj' : k + j = j') :
    ((homologyFunctor C (up ℤ) 0).shiftIso k i i' hi').hom.app S.X₃ ≫ hS.δ i' j' hij' =
      k.negOnePow •
        ((hS.map_of_exact (CategoryTheory.shiftFunctor (CochainComplex C ℤ) k)).δ i j hij ≫
          ((homologyFunctor C (up ℤ) 0).shiftIso k j j' hj').hom.app S.X₁) :=
  shiftIso_hom_app_comp_δ S hS k i j i' j' hij hij' hi' hj' _

end CochainComplex
