module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Ring.NegOnePow

/-!
# A degree-lowering derivation of a sheafified graded algebra

Let `A` be a graded algebra of presheaves of modules on the family `P`, let `α` be a locally
bijective map of presheaves of rings, and let `A.sheafify α` be the sheafified graded algebra of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification`.
This file sheafifies a
*degree-lowering family* `dPre n : P n ⟶ P (n - 1)`:

* the sheafified family `Stacks.GradedAlgebra.sheafifyD` is the sheafification functor applied
  degreewise;
* **the graded Leibniz rule transfers** (`sheafifyD_mul`): both sides of the Leibniz identity are
  sections of a sheaf, both commute with restriction, and both agree on the unit-images of local
  sections, so the identity holds for *arbitrary* local sections of the sheafified pieces and not
  only for those that lift;
* if the presheaf family squares to zero, the sheafified one assembles into a `ℤ`-indexed chain
  complex of sheaves of modules whose degree-`n` term is the degree-`n` piece **on the nose**
  (`sheafifyChain`, `sheafifyChain_X`, `sheafifyChain_d`).

Those are the fields `d`, `d_mul`, `chain`, `chain_X` and `chain_d` of
`Stacks.RegularSequence.KoszulChainData`, for a graded algebra that is a sheafification. The
remaining field, the value on a degree-one generator, is a statement about the generator and is
proved where the generator is; `sheafifyD_unit` is what it reduces to.

## Main definitions

* `Stacks.GradedAlgebra.sheafifyD`: the sheafification of a degree-lowering family.
* `Stacks.GradedAlgebra.sheafifyDRel`: the same family re-indexed as the differential of a
  `ℤ`-indexed chain complex, i.e. defined on every pair of degrees and zero off the relation of
  `ComplexShape.down ℤ`.
* `Stacks.GradedAlgebra.sheafifyChain`: **the chain complex**.

## Main results

* `Stacks.GradedAlgebra.sheafifyD_unit` and `sheafifyD_lift`: the sheafified family on unit-images
  and on local lifts. These are the exact analogues of
  `Stacks.GradedAlgebra.sheafifyGen_unit` and `sheafifyGen_lift`.
* `Stacks.GradedAlgebra.sheafifyD_mul`: **the graded Leibniz rule transfers to the
  sheafification.**
* `Stacks.GradedAlgebra.sheafifyChain_X` and `sheafifyChain_d`: the complex has the homogeneous
  pieces as its terms and `sheafifyD` as its differential.

## Implementation notes

What is forced and what is chosen.

* **The Leibniz rule cannot be transported, only extended.** A section of a sheafified piece is
  only *locally* the unit-image of a section of the presheaf piece, so the identity on unit-images
  does not immediately give the identity. What makes it give it is that every operation occurring
  in the identity commutes with restriction — the graded multiplication by
  `Stacks.GradedAlgebra.sheafify_mul_restrict`, the differential by naturality of a morphism of
  sheaves of modules, and the degree transports by `Stacks.degCast_map` — together with
  separatedness of the target. This is the same argument, through the same lemma
  `sheafifyMul_restrict`, that `Stacks.GradedAlgebra.sheafify` uses for its own associativity and
  unit laws.
* **The three restriction computations are term-mode `Eq.trans` chains, not `rw` sequences.** The
  two spellings of a section of a presheaf of modules — `(P n).obj X` and
  `((toPresheaf R₀).obj (P n)).obj X` — are the same type with `AddCommMonoid` instances that are
  not syntactically equal, and `Stacks.liftSieve` produces its lifts in the second spelling while
  `sheafify_mul_restrict` consumes them in the first. A rewrite inside such a mixed goal is
  refused as not type-correct at `implicit` transparency; `Eq.trans` and `congrArg` are checked at
  full transparency and go through. This is the obstruction already recorded in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulStalkComplexIso`.
* **The differential of the complex carries its transport on the right.** `sheafifyDRel i j` is
  `sheafifyD i` followed by a transport `piece (i - 1) = piece j`; the `dite` is only on whether
  the two degrees are related at all. `Stacks.GradedAlgebra.comp_eqToHom_comp` moves that
  transport past the next differential, so square-zeroness of the complex is square-zeroness of
  the family, which is functoriality of sheafification applied to the presheaf-level one.
* No `@[stacks]` attribute. Nothing here is a statement of the Stacks Project: this is the
  sheafification step of a construction whose input and output are both stated elsewhere.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
-/

@[expose] public section

open CategoryTheory Opposite PresheafOfModules

universe v u t a

namespace Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}]
  {P : ℤ → PresheafOfModules.{a} R₀} (A : GradedAlgebra P)

/-! ### Moving a degree transport past a degree-lowering family -/

omit [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{a}] [HasWeakSheafify J AddCommGrpCat.{a}] in
/-- A degree transport between two degree-lowering morphisms moves to the far side. This is what
turns square-zeroness of a family `d n : X n ⟶ X (n - 1)` into square-zeroness of the
differential of the associated chain complex. -/
theorem comp_eqToHom_comp {X : ℤ → SheafOfModules.{a} R} (d : ∀ n : ℤ, X n ⟶ X (n - 1))
    {i j : ℤ} (h : i - 1 = j) :
    d i ≫ eqToHom (congrArg X h) ≫ d j =
      d i ≫ d (i - 1) ≫ eqToHom (congrArg X (by rw [h] : i - 1 - 1 = j - 1)) := by
  subst h; simp

/-! ### The sheafified family -/

/-- **The sheafification of a degree-lowering family** of morphisms of presheaves of modules: the
sheafification functor, applied degreewise. -/
noncomputable def sheafifyD (dPre : ∀ n : ℤ, P n ⟶ P (n - 1)) (n : ℤ) :
    (A.sheafify α).piece n ⟶ (A.sheafify α).piece (n - 1) :=
  (sheafification α).map (dPre n)

variable (dPre : ∀ n : ℤ, P n ⟶ P (n - 1))

/-- The sheafified family on the unit-image of a local section of the presheaf piece. -/
theorem sheafifyD_unit (n : ℤ) (X : Cᵒᵖ) (x : (P n).obj X) :
    (A.sheafifyD α dPre n).val.app X (Hom.app (sheafifyUnit α (P n)) X x) =
      Hom.app (sheafifyUnit α (P (n - 1))) X (Hom.app (dPre n) X x) :=
  PresheafOfModules.unit_naturality_apply (dPre n) X x

/-- A local lift of a local section gives a local lift of its image under the sheafified
family. -/
theorem sheafifyD_lift (n : ℤ) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (b : ((A.sheafify α).piece n).val.obj X) (x : (P n).obj Y)
    (hx : Hom.app (sheafifyUnit α (P n)) Y x = ((A.sheafify α).piece n).val.map f b) :
    Hom.app (sheafifyUnit α (P (n - 1))) Y (Hom.app (dPre n) Y x) =
      ((A.sheafify α).piece (n - 1)).val.map f ((A.sheafifyD α dPre n).val.app X b) :=
  ((A.sheafifyD_unit α dPre n Y x).symm.trans
      (congrArg ((A.sheafifyD α dPre n).val.app Y) hx)).trans
    (naturality_apply (A.sheafifyD α dPre n).val f b)

/-! ### The graded Leibniz rule -/

/-- Restricting a degree transport of a section is the transport of its local lift. -/
private theorem restrict_degCast_unit {s t : ℤ} (h : s = t) {U Y : Cᵒᵖ} (f : U ⟶ Y)
    (z : ((A.sheafify α).piece s).val.obj U) (z₀ : (P s).obj Y)
    (hz : Hom.app (sheafifyUnit α (P s)) Y z₀ = ((A.sheafify α).piece s).val.map f z) :
    ((A.sheafify α).piece t).val.map f
        (Stacks.degCast (F := fun q : ℤ => ((((A.sheafify α).piece q).val.obj U : Type a))) h z) =
      Hom.app (sheafifyUnit α (P t)) Y
        (Stacks.degCast (F := fun q : ℤ => ((P q).obj Y : Type a)) h z₀) := by
  subst h
  exact hz.symm

/-- **The graded Leibniz rule transfers to the sheafification.** If the degree-lowering family
satisfies the Leibniz rule on the sections of the presheaf pieces, the sheafified family satisfies
it on *arbitrary* local sections of the sheafified pieces. Both sides commute with restriction and
agree on the unit-images of local sections, and the target is separated. -/
theorem sheafifyD_mul
    (hd : ∀ (n m : ℤ) (X : Cᵒᵖ) (x : (P n).obj X) (y : (P m).obj X),
      Hom.app (dPre (n + m)) X ((A.mul n m).app X x y) =
        Stacks.degCast (F := fun q : ℤ => ((P q).obj X : Type a))
            (by ring : (n - 1) + m = n + m - 1)
            ((A.mul (n - 1) m).app X (Hom.app (dPre n) X x) y) +
          (Int.negOnePow n : ℤ) •
            Stacks.degCast (F := fun q : ℤ => ((P q).obj X : Type a))
              (by ring : n + (m - 1) = n + m - 1)
              ((A.mul n (m - 1)).app X x (Hom.app (dPre m) X y)))
    (n m : ℤ) (U : Cᵒᵖ) (a : ((A.sheafify α).piece n).val.obj U)
    (b : ((A.sheafify α).piece m).val.obj U) :
    (A.sheafifyD α dPre (n + m)).val.app U (((A.sheafify α).mul n m).app U a b) =
      Stacks.degCast (F := fun q : ℤ => ((((A.sheafify α).piece q).val.obj U : Type a)))
          (by ring : (n - 1) + m = n + m - 1)
          (((A.sheafify α).mul (n - 1) m).app U
            ((A.sheafifyD α dPre n).val.app U a) b) +
        (Int.negOnePow n : ℤ) •
          Stacks.degCast (F := fun q : ℤ => ((((A.sheafify α).piece q).val.obj U : Type a)))
            (by ring : n + (m - 1) = n + m - 1)
            (((A.sheafify α).mul n (m - 1)).app U a
              ((A.sheafifyD α dPre m).val.app U b)) := by
  refine Stacks.eq_of_isSeparated ((A.sheafify α).piece (n + m - 1))
    (J.intersection_covering (liftSieve_mem α (P n) a) (liftSieve_mem α (P m) b)) ?_
  rintro Y f ⟨⟨a₀, ha₀⟩, ⟨b₀, hb₀⟩⟩
  have ha : Hom.app (sheafifyUnit α (P n)) (op Y) a₀ =
    ((A.sheafify α).piece n).val.map f.op a := ha₀
  have hb : Hom.app (sheafifyUnit α (P m)) (op Y) b₀ =
    ((A.sheafify α).piece m).val.map f.op b := hb₀
  have hL : ((A.sheafify α).piece (n + m - 1)).val.map f.op
        ((A.sheafifyD α dPre (n + m)).val.app U (((A.sheafify α).mul n m).app U a b)) =
      Hom.app (sheafifyUnit α (P (n + m - 1))) (op Y)
        (Hom.app (dPre (n + m)) (op Y) ((A.mul n m).app (op Y) a₀ b₀)) :=
    ((naturality_apply (A.sheafifyD α dPre (n + m)).val f.op _).symm.trans
      (congrArg ((A.sheafifyD α dPre (n + m)).val.app (op Y))
        (A.sheafify_mul_restrict α n m f.op a b a₀ b₀ ha hb))).trans
      (A.sheafifyD_unit α dPre (n + m) (op Y) _)
  have hR₁ := A.restrict_degCast_unit α (by ring : (n - 1) + m = n + m - 1) f.op
    (((A.sheafify α).mul (n - 1) m).app U ((A.sheafifyD α dPre n).val.app U a) b)
    ((A.mul (n - 1) m).app (op Y) (Hom.app (dPre n) (op Y) a₀) b₀)
    (A.sheafify_mul_restrict α (n - 1) m f.op _ b (Hom.app (dPre n) (op Y) a₀) b₀
      (A.sheafifyD_lift α dPre n f.op a a₀ ha) hb).symm
  have hR₂ := A.restrict_degCast_unit α (by ring : n + (m - 1) = n + m - 1) f.op
    (((A.sheafify α).mul n (m - 1)).app U a ((A.sheafifyD α dPre m).val.app U b))
    ((A.mul n (m - 1)).app (op Y) a₀ (Hom.app (dPre m) (op Y) b₀))
    (A.sheafify_mul_restrict α n (m - 1) f.op a _ a₀ (Hom.app (dPre m) (op Y) b₀) ha
      (A.sheafifyD_lift α dPre m f.op b b₀ hb)).symm
  rw [hL, map_add, map_zsmul, hR₁, hR₂, hd n m (op Y) a₀ b₀, map_add, map_zsmul]
  rfl

/-! ### The chain complex -/

/-- The sheafified family, re-indexed as the differential of a `ℤ`-indexed chain complex: it is
`Stacks.GradedAlgebra.sheafifyD` followed by the transport `piece (i - 1) = piece j` when the two
degrees are related by `ComplexShape.down ℤ`, and zero otherwise. -/
noncomputable def sheafifyDRel (i j : ℤ) :
    (A.sheafify α).piece i ⟶ (A.sheafify α).piece j :=
  if h : j + 1 = i then
    A.sheafifyD α dPre i ≫
      eqToHom (congrArg (A.sheafify α).piece (by omega : i - 1 = j))
  else 0

/-- `Stacks.GradedAlgebra.sheafifyDRel` vanishes between degrees not related by
`ComplexShape.down ℤ`. -/
theorem sheafifyDRel_eq_zero {i j : ℤ} (h : ¬ j + 1 = i) :
    A.sheafifyDRel α dPre i j = 0 :=
  dite_eq_right_of_eq_false (eq_false h)

/-- From degree `n` to degree `n - 1`, `Stacks.GradedAlgebra.sheafifyDRel` is
`Stacks.GradedAlgebra.sheafifyD`. -/
theorem sheafifyDRel_self (n : ℤ) :
    A.sheafifyDRel α dPre n (n - 1) = A.sheafifyD α dPre n := by
  rw [sheafifyDRel,
    dite_eq_left_of_eq_true (eq_true (by omega : n - 1 + 1 = n))]
  simp

/-- **The chain complex of a square-zero degree-lowering family on a sheafified graded algebra.**
Its degree-`n` term is the degree-`n` homogeneous piece on the nose. -/
noncomputable def sheafifyChain (hsq : ∀ n : ℤ, dPre n ≫ dPre (n - 1) = 0) :
    ChainComplex (SheafOfModules.{a} R) ℤ where
  X n := (A.sheafify α).piece n
  d := A.sheafifyDRel α dPre
  shape _ _ h := A.sheafifyDRel_eq_zero α dPre h
  d_comp_d' i j k hij hjk := by
    have hij₀ : j + 1 = i := hij
    have hjk₀ : k + 1 = j := hjk
    have hij' : i - 1 = j := by omega
    have hzero : A.sheafifyD α dPre i ≫ A.sheafifyD α dPre (i - 1) = 0 := by
      rw [show A.sheafifyD α dPre i ≫ A.sheafifyD α dPre (i - 1) =
          (sheafification α).map (dPre i ≫ dPre (i - 1)) from (Functor.map_comp _ _ _).symm,
        hsq i]
      simp
      rfl
    rw [sheafifyDRel, dite_eq_left_of_eq_true (eq_true hij₀),
      sheafifyDRel, dite_eq_left_of_eq_true (eq_true hjk₀), Category.assoc,
      ← Category.assoc (eqToHom _) (A.sheafifyD α dPre j) _,
      ← Category.assoc (A.sheafifyD α dPre i) _ _,
      comp_eqToHom_comp (A.sheafifyD α dPre) hij',
      ← Category.assoc (A.sheafifyD α dPre i) (A.sheafifyD α dPre (i - 1)) _,
      hzero]
    simp

/-- The degree-`n` term of `Stacks.GradedAlgebra.sheafifyChain` is the degree-`n` homogeneous
piece of the sheafified graded algebra. -/
theorem sheafifyChain_X (hsq : ∀ n : ℤ, dPre n ≫ dPre (n - 1) = 0) (n : ℤ) :
    (A.sheafifyChain α dPre hsq).X n = (A.sheafify α).piece n := rfl

/-- Up to the identifications `Stacks.GradedAlgebra.sheafifyChain_X`, the differential of
`Stacks.GradedAlgebra.sheafifyChain` from degree `n` to degree `n - 1` is
`Stacks.GradedAlgebra.sheafifyD`. -/
theorem sheafifyChain_d (hsq : ∀ n : ℤ, dPre n ≫ dPre (n - 1) = 0) (n : ℤ) :
    eqToHom (A.sheafifyChain_X α dPre hsq n).symm ≫
        (A.sheafifyChain α dPre hsq).d n (n - 1) ≫
          eqToHom (A.sheafifyChain_X α dPre hsq (n - 1)) =
      A.sheafifyD α dPre n := by
  exact (Category.id_comp (A.sheafifyDRel α dPre n (n - 1) ≫
      𝟙 ((A.sheafify α).piece (n - 1)))).trans
    ((Category.comp_id (A.sheafifyDRel α dPre n (n - 1))).trans
      (A.sheafifyDRel_self α dPre n))

end Stacks.GradedAlgebra

end
