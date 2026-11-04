module

public import StacksFrontier.AlgebraicGeometry.GradedSectionRing.Evaluation
public import StacksFrontier.AlgebraicGeometry.TensorPowerCoherence.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Commutativity of the graded ring of sections of an invertible sheaf

`StacksFrontier/AlgebraicGeometry/GradedSectionRing/` builds the graded ring
`Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L^{⊗ n})` of [Stacks, Tag 01CV] out of the multiplication
isomorphisms `L^{⊗ a} ⊗ L^{⊗ b} ≅ L^{⊗ (a + b)}` of a `Stacks.Monoidal.PowerSystem`, and proves
everything Tag 01CV asserts **except commutativity**, which it carries as an explicit hypothesis

  `hβ : ∀ a b, (β_ (S.obj a) (S.obj b)).hom ≫ (S.mulIso b a).hom
                 = (S.mulIso a b).hom ≫ eqToHom …`,

the commutativity constraint of [Stacks, Tag 01CU]. This file discharges that hypothesis.

The constraint is not a formal consequence of the symmetric monoidal axioms — an invertible
object of a general symmetric monoidal category satisfies only `β ≫ β = 𝟙`, and the odd line in
super vector spaces has `β = -𝟙`. What is formal is the passage from the single degree `(1, 1)`
to every pair: the braiding of `L^{⊗ a}` with `L^{⊗ b}` is a block transposition, and a block
transposition built from trivial elementary transpositions is trivial. That induction is run here
with `Stacks.Monoidal.IntPower.comm_step_iff` — the hexagon step already proved for the
integer-indexed multiplication of
`StacksFrontier/AlgebraicGeometry/TensorPowerCoherence/IntPowerSystem.lean` — against the
associativity `Stacks.Monoidal.PowerSystem.mulIso_assoc` of the `PowerSystem` multiplication.

The degree `(1, 1)` input is `β_ L L = 𝟙`, which for an invertible sheaf of modules is the
unconditional `Stacks.SheafOfModules.Invertible.braiding_self_hom_eq_id`
(`StacksFrontier/AlgebraicGeometry/TensorPowerCoherence/BraidingSelf.lean`). So the sheaf-level
conclusions below are unconditional.

## Main definitions

* `Stacks.Monoidal.PowerSystem.mulIsoAt`: the multiplication isomorphism with its target
  exponent named by an arbitrary witness of `a + b = t`. Comparing `mulIso a b` with
  `mulIso b a` otherwise needs a transport at every step of the induction; naming the target
  removes it, exactly as `Stacks.Monoidal.IntPower.mulAt` does for the integer-indexed
  multiplication.
* `Stacks.SheafOfModules.Invertible.oneTensorInverse`: a tensor inverse of `L^{⊗ 1}`, which is
  what makes tensoring on the right by `L^{⊗ 1}` faithful.
* `Stacks.SheafOfModules.Invertible.homGradedCommRingOfInvertible`: **the associated graded ring
  `Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L^{⊗ n})` of [Stacks, Tag 01CV]** — the commutative graded ring
  structure of `GradedSectionRing/Ring.lean` with its hypothesis discharged.

## Main results

* `Stacks.Monoidal.PowerSystem.mulIsoAt_assoc`: associativity in the `mulIsoAt` form.
* `Stacks.Monoidal.PowerSystem.mulIsoAt_comm`: **the multiplication isomorphisms of a power
  system in a symmetric monoidal category are commutative**, given that the braiding of the
  first power with itself is the identity and that tensoring on the right by it is faithful.
* `Stacks.SheafOfModules.Invertible.tensorPowerMulIso_comm`: **the commutativity constraint of
  Tag 01CU for the tensor powers of an invertible sheaf of modules, unconditionally** — in
  exactly the shape `Stacks.Monoidal.PowerSystem.sectionMul_comm`,
  `Stacks.Monoidal.PowerSystem.gradedCommRing` and
  `Stacks.SheafOfModules.Invertible.homGradedCommRing` take as a hypothesis.
* `Stacks.SheafOfModules.Invertible.sectionMul_comm_of_invertible`: **the multiplication of
  global sections of the tensor powers is commutative**, unconditionally.
* `Stacks.SheafOfModules.Invertible.exists_aeval_eq_of_isHomogeneous_of_invertible` and
  `exists_sections_aeval_eq_of_isHomogeneous_of_invertible`: **a homogeneous polynomial of degree
  `d` with integer coefficients, evaluated at global sections of `L^{⊗ N}`, is a global section
  of `L^{⊗ (d N)}` — unconditionally.** `GradedSectionRing/Evaluation.lean` states these with the
  commutativity constraint as a hypothesis, because that file is upstream of this one; it is
  discharged here. This is the construction by which [Stacks, Tag 09NV] and
  [Stacks, Tag 0E21] turn a homogeneous polynomial into a section of a tensor power, so it is
  the one place where the first clause of Tag 01CV feeds into those tags.

## Implementation notes

**Why this is not a second copy of `IntPower.mulAt_comm`.** That theorem is about the
integer-indexed multiplication `Stacks.Monoidal.IntPower.mul`, defined by a two-sided recursion
over `ℤ`; the graded ring is built on `Stacks.Monoidal.PowerSystem.mulIso`, a structural
recursion over `ℕ`. The two agree where both are defined, but identifying them means
transporting along `((a + b : ℕ) : ℤ) = (a : ℤ) + (b : ℤ)` at every index of the induction. The
induction itself is four lines of bookkeeping over the generic hexagon step `comm_step_iff`,
which is shared, so the shared content is reused and only the indexing is redone.

**The faithfulness hypothesis is used only in the unused direction.** `comm_step_iff` is an
`iff`, and its `mpr` is what needs `(tensorRight Z).Faithful`; the induction below uses only
`mp`. The instance is nevertheless a hypothesis of the lemma, so it is supplied — for sheaves of
modules from a tensor inverse of `L^{⊗ 1}` through
`Stacks.SheafOfModules.Invertible.cancel_tensor_right`.

**The first clause of Tag 01CV is claimed here; the second is not.** Besides the commutative
graded ring structure, the tag asks for the graded ring to be the ring of *global sections*.
That second condition is `homToSection_sectionMul` of `GradedSectionRing/Ring.lean`, which is
proved and unconditional, so with the commutativity constraint discharged below nothing is
outstanding for the tag's first displayed object and `homGradedCommRingOfInvertible` carries
`@[stacks 01CV "associated graded ring"]`.

What is still withheld is the tag's *second* displayed object, the graded `Γ_*(X, L)`-module
`Γ_*(X, L, F) = ⨁_{n ∈ ℤ} Γ(X, F ⊗ L^{⊗ n})`.
`StacksFrontier/AlgebraicGeometry/GradedSectionsModule/Basic.lean` builds its non-negative
part, graded by `ℕ`, which is strictly weaker than the tag's `ℤ`-grading; so that file carries
no attribute and neither does anything here on its behalf.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
-/

@[expose] public section

universe v u w

open CategoryTheory MonoidalCategory BraidedCategory

namespace Stacks.Monoidal.PowerSystem

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (S : PowerSystem C)

/-- The multiplication isomorphism of a power system, with its target exponent named by an
arbitrary witness of `a + b = t`. This is the form the commutativity induction is run in:
comparing `mulIso a b` with `mulIso b a` otherwise needs a transport along `a + b = b + a` at
every step. -/
noncomputable def mulIsoAt (a b t : ℕ) (h : a + b = t) : S.obj a ⊗ S.obj b ≅ S.obj t :=
  S.mulIso a b ≪≫ eqToIso (congrArg S.obj h)

/-- For the witness `rfl : a + b = a + b`, `mulIsoAt a b (a + b)` is `mulIso a b`. -/
@[simp]
theorem mulIsoAt_rfl (a b : ℕ) : S.mulIsoAt a b (a + b) rfl = S.mulIso a b := by
  simp [mulIsoAt]

/-- **Associativity of the multiplication isomorphisms, in the `mulIsoAt` form.** -/
theorem mulIsoAt_assoc (a b c ab bc t : ℕ) (hab : a + b = ab) (hbc : b + c = bc)
    (ht : ab + c = t) :
    ((S.mulIsoAt a b ab hab).hom ▷ S.obj c) ≫ (S.mulIsoAt ab c t ht).hom =
      (α_ (S.obj a) (S.obj b) (S.obj c)).hom ≫
        (S.obj a ◁ (S.mulIsoAt b c bc hbc).hom) ≫ (S.mulIsoAt a bc t (by omega)).hom := by
  subst hab
  subst hbc
  subst ht
  simp only [mulIsoAt, Iso.trans_hom, eqToIso.hom, eqToHom_refl, Category.comp_id]
  simpa only [Category.assoc] using S.mulIso_assoc a b c

/-- In degree `(a, 0)` the multiplication isomorphism is the right unitor. -/
theorem mulIsoAt_zero_right_hom (a : ℕ) :
    (S.mulIsoAt a 0 a (Nat.add_zero a)).hom =
      (S.obj a ◁ S.objZeroIso.hom) ≫ (ρ_ (S.obj a)).hom := by
  simp only [mulIsoAt, mulIso_zero, Iso.trans_hom, whiskerLeftIso_hom, eqToIso.hom,
    eqToHom_refl, Category.comp_id]

/-- In degree `(0, b)` the multiplication isomorphism is the left unitor. -/
theorem mulIsoAt_zero_left_hom (b : ℕ) :
    (S.mulIsoAt 0 b b (Nat.zero_add b)).hom =
      (S.objZeroIso.hom ▷ S.obj b) ≫ (λ_ (S.obj b)).hom := by
  simp only [mulIsoAt, Iso.trans_hom, eqToIso.hom]
  rw [S.mulIso_zeroLeft b]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

section Comm

variable [SymmetricCategory C] [(MonoidalCategory.tensorRight (S.obj 1)).Faithful]

/-- **The multiplication isomorphisms of a power system are commutative**, given that the
braiding of the first power with itself is the identity. That hypothesis is the commutativity
constraint in degree `(1, 1)` and is not a formal consequence of the symmetric monoidal axioms;
everything else is the hexagon, through `Stacks.Monoidal.IntPower.comm_step_iff`. -/
theorem mulIsoAt_comm (hb : (β_ (S.obj 1) (S.obj 1)) = Iso.refl _) (a b t : ℕ)
    (ht : a + b = t) :
    (S.mulIsoAt a b t ht).hom =
      (β_ (S.obj a) (S.obj b)).hom ≫ (S.mulIsoAt b a t (by omega)).hom := by
  let Q (a b : ℕ) : Prop := ∀ (t : ℕ) (ht : a + b = t),
    (S.mulIsoAt a b t ht).hom =
      (β_ (S.obj a) (S.obj b)).hom ≫ (S.mulIsoAt b a t (by omega)).hom
  have hz (n : ℕ) : Q n 0 := by
    intro t ht
    have ht' : t = n := by omega
    subst ht'
    rw [S.mulIsoAt_zero_right_hom, S.mulIsoAt_zero_left_hom,
      ← BraidedCategory.braiding_naturality_right_assoc, braiding_leftUnitor]
  have hs (a b : ℕ) (hc : Q a 1) (h : Q a b) : Q a (b + 1) := by
    have he := Stacks.Monoidal.IntPower.comm_step_iff
      (S.mulIsoAt a b (a + b) rfl)
      (S.mulIsoAt b a (a + b) (by omega))
      (S.mulIsoAt a 1 (a + 1) rfl)
      (S.mulIsoAt 1 a (a + 1) (by omega))
      (S.mulIsoAt b 1 (b + 1) rfl)
      (S.mulIsoAt (a + b) 1 (a + b + 1) rfl)
      (S.mulIsoAt b (a + 1) (a + b + 1) (by omega))
      (S.mulIsoAt a (b + 1) (a + b + 1) (by omega))
      (S.mulIsoAt (b + 1) a (a + b + 1) (by omega))
      (S.mulIsoAt_assoc a b 1 (a + b) (b + 1) (a + b + 1) rfl rfl rfl)
      (S.mulIsoAt_assoc b a 1 (a + b) (a + 1) (a + b + 1) (by omega) rfl rfl)
      (S.mulIsoAt_assoc b 1 a (b + 1) (a + 1) (a + b + 1) rfl (by omega) (by omega))
      (hc (a + 1) rfl)
    intro t ht
    have ht' : t = a + b + 1 := by omega
    subst ht'
    exact he.mp (h (a + b) rfl)
  have h11 : Q 1 1 := by
    intro t ht
    rw [hb, Iso.refl_hom, Category.id_comp]
  have h1 (b : ℕ) : Q 1 b := by
    induction b with
    | zero => exact hz 1
    | succ k ih => exact hs 1 k h11 ih
  have hn1 (n : ℕ) : Q n 1 := by
    intro t ht
    have h := h1 n t (by omega)
    have hh : (β_ (S.obj n) (S.obj 1)).hom ≫ (S.mulIsoAt 1 n t (by omega)).hom
        = (S.mulIsoAt n 1 t ht).hom := by
      rw [h, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
    exact hh.symm
  have hall (a b : ℕ) : Q a b := by
    induction b with
    | zero => exact hz a
    | succ k ih => exact hs a k (hn1 a) ih
  exact hall a b t ht

/-- **The commutativity constraint of Tag 01CU for a power system**, in exactly the shape
`Stacks.Monoidal.PowerSystem.sectionMul_comm` and
`Stacks.Monoidal.PowerSystem.gradedCommRing` take as a hypothesis. -/
theorem mulIso_comm (hb : (β_ (S.obj 1) (S.obj 1)) = Iso.refl _) (a b : ℕ) :
    (β_ (S.obj a) (S.obj b)).hom ≫ (S.mulIso b a).hom
      = (S.mulIso a b).hom ≫ eqToHom (congrArg S.obj (Nat.add_comm a b)) := by
  have h := S.mulIsoAt_comm hb a b (a + b) rfl
  rw [S.mulIsoAt_rfl] at h
  rw [mulIsoAt] at h
  simp only [Iso.trans_hom, eqToIso.hom] at h
  rw [h]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

end Comm

end Stacks.Monoidal.PowerSystem

namespace Stacks.SheafOfModules.Invertible

attribute [local instance] Stacks.SheafOfModules.monoidalCategory
  Stacks.SheafOfModules.braidedCategory Stacks.SheafOfModules.symmetricCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  (L : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
  [AlgebraicGeometry.SheafOfModules.IsInvertible O hO L]

/-- A tensor inverse of the first tensor power: `L^{⊗ 1} ⊗ L^{⊗ -1} ≅ 𝟙`. The first power is
identified with `L` by `tensorPowerOneIso`, the factors are swapped by the braiding, and the
successor comparison in degree `-1` lands in `L^{⊗ 0}`, which is the tensor unit on the nose. -/
noncomputable def oneTensorInverse :
    tensorPower O hO L (1 : ℤ) ⊗ tensorPower O hO L (-1 : ℤ)
      ≅ 𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
        hO)) :=
  whiskerRightIso (tensorPowerOneIso O hO L) _ ≪≫ β_ _ _ ≪≫
    Stacks.SheafOfModules.tensorObjIso O hO _ _ ≪≫
    tensorPowerSuccIso O hO L (-1 : ℤ) ≪≫
    tensorPowerReindex O hO L (by ring : (-1 : ℤ) + 1 = 0)

/-- Tensoring on the right by the first tensor power of an invertible sheaf of modules is
faithful: it has a tensor inverse. -/
theorem faithful_tensorRight_obj_one :
    (MonoidalCategory.tensorRight ((tensorPowerSystem O hO L).obj 1)).Faithful :=
  ⟨fun {_ _ _ _} h => cancel_tensor_right (oneTensorInverse O hO L) _ _ h⟩

/-- The braiding of the first tensor power with itself is the identity. This is
`braiding_self_hom_eq_id` at `L^{⊗ 1}`, which is invertible. -/
theorem braiding_obj_one_eq_refl :
    (β_ ((tensorPowerSystem O hO L).obj 1)
      ((tensorPowerSystem O hO L).obj 1)) = Iso.refl _ := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible O hO
      ((tensorPowerSystem O hO L).obj 1) :=
    tensorPower_isInvertible O hO L 1
  exact Iso.ext (braiding_self_hom_eq_id O hO _)

/-- **The commutativity constraint of [Stacks, Tag 01CU] for the multiplication isomorphisms of
the tensor powers of an invertible sheaf of modules, unconditionally.** This is the hypothesis
`hβ` of `Stacks.SheafOfModules.Invertible.sectionMul_comm`,
`Stacks.Monoidal.PowerSystem.gradedCommRing` and
`Stacks.SheafOfModules.Invertible.homGradedCommRing`. -/
theorem tensorPowerMulIso_comm (a b : ℕ) :
    (β_ (tensorPower O hO L (a : ℤ)) (tensorPower O hO L (b : ℤ))).hom
        ≫ (tensorPowerMulIso O hO L b a).hom
      = (tensorPowerMulIso O hO L a b).hom
        ≫ eqToHom (congrArg (fun k : ℕ => tensorPower O hO L (k : ℤ)) (Nat.add_comm a b)) :=
  let := faithful_tensorRight_obj_one O hO L
  (tensorPowerSystem O hO L).mulIso_comm
    (braiding_obj_one_eq_refl O hO L) a b

/-- **The multiplication of global sections of the tensor powers of an invertible sheaf of
modules is commutative**, unconditionally: the multiplicative half of [Stacks, Tag 01CV] that
`GradedSectionRing/Basic.lean` could only state with the constraint as a hypothesis. -/
theorem sectionMul_comm_of_invertible {a b : ℕ}
    (s : (tensorPower O hO L (a : ℤ)).sections) (t : (tensorPower O hO L (b : ℤ)).sections) :
    sectionMul O hO L s t = sectionsCongr O hO L (Nat.add_comm b a) (sectionMul O hO L t s) :=
  sectionMul_comm O hO L (tensorPowerMulIso_comm O hO L) s t

/-- **Stacks Project, Tag 01CV: the associated graded ring
`Γ_*(X, L) = ⨁_{n ≥ 0} Γ(X, L^{⊗ n})` of an invertible sheaf of modules.** This is the
commutative graded ring on the morphism groups `𝟙 ⟶ L^{⊗ n}`, with the commutativity constraint
of Tag 01CU discharged by `tensorPowerMulIso_comm` above, so it is unconditional.

The direct sum itself needs no declaration of ours: Mathlib's `DirectSum.commRing` turns a
`DirectSum.GCommRing` on the family into a commutative ring on `⨁ n : ℕ, (𝟙 ⟶ L^{⊗ n})`, the
tensor unit *is* the structure sheaf on the nose (`Stacks.SheafOfModules.tensorUnit_eq`) so the
summands are the global sections the tag names, and
`Stacks.SheafOfModules.Invertible.homToSection_sectionMul` identifies the multiplication with
the one already defined on `PresheafOfModules.sections`. This declaration alone is therefore the
covering set of the tag's first displayed object; the tag's second one, the `ℤ`-graded module
`Γ_*(X, L, F)`, is not claimed — see the implementation notes. -/
@[instance_reducible,
  stacks 01CV "associated graded ring",
  ega "II 4.5.1" "S = ⊕Γ(X,L^⊗n)",
  ega "III 2.1.1" "(2.1.1.1)",
  ega "II 2.6.1" "graded ring Γ_•(O_X)",
  ega "0 5.4.6" "graded ring Γ•(L)"]
noncomputable def homGradedCommRingOfInvertible :
    DirectSum.GCommRing (fun n : ℕ =>
      (𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
        hO))
        ⟶ tensorPower O hO L (n : ℤ))) :=
  homGradedCommRing O hO L (tensorPowerMulIso_comm O hO L)

/-- **A homogeneous polynomial of degree `d` with integer coefficients, evaluated at global
sections of `L^{⊗ N}`, is a global section of `L^{⊗ (d N)}` — unconditionally.** This is
`Stacks.SheafOfModules.Invertible.exists_aeval_eq_of_isHomogeneous` with its commutativity
hypothesis discharged by `tensorPowerMulIso_comm`; `GradedSectionRing/Evaluation.lean` states it
with the hypothesis because that file is upstream of this one. -/
theorem exists_aeval_eq_of_isHomogeneous_of_invertible {σ : Type*} {N : ℕ}
    (x : σ → (𝟙_ (_root_.SheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      ⟶ tensorPower O hO L (N : ℤ)))
    {P : MvPolynomial σ ℤ} {d : ℕ} (hP : P.IsHomogeneous d) :
    letI := homGradedCommRingOfInvertible O hO L
    ∃ t : 𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
      hO))
        ⟶ tensorPower O hO L ((d * N : ℕ) : ℤ),
      DirectSum.of (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ⟶ tensorPower O hO L (n
            : ℤ)) (d * N) t =
        MvPolynomial.aeval (fun i => DirectSum.of (fun n : ℕ =>
          𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
            hO))
            ⟶ tensorPower O hO L (n : ℤ)) N (x i)) P :=
  exists_aeval_eq_of_isHomogeneous O hO L (tensorPowerMulIso_comm O hO L) x hP

/-- The same as `exists_aeval_eq_of_isHomogeneous_of_invertible`, with the global sections spelled
as `PresheafOfModules.sections` rather than as morphisms out of the tensor unit. -/
theorem exists_sections_aeval_eq_of_isHomogeneous_of_invertible {σ : Type*} {N : ℕ}
    (s : σ → (tensorPower O hO L (N : ℤ)).sections)
    {P : MvPolynomial σ ℤ} {d : ℕ} (hP : P.IsHomogeneous d) :
    letI := homGradedCommRingOfInvertible O hO L
    ∃ t : (tensorPower O hO L ((d * N : ℕ) : ℤ)).sections,
      DirectSum.of (fun n : ℕ => 𝟙_ (_root_.SheafOfModules.{w}
          (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO)) ⟶ tensorPower O hO L (n
            : ℤ)) (d * N)
            (sectionToHom O hO L t) =
        MvPolynomial.aeval (fun i => DirectSum.of (fun n : ℕ =>
          𝟙_ (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O
            hO))
            ⟶ tensorPower O hO L (n : ℤ)) N (sectionToHom O hO L (s i))) P :=
  exists_sections_aeval_eq_of_isHomogeneous O hO L (tensorPowerMulIso_comm O hO L) s hP

end Stacks.SheafOfModules.Invertible

end
