module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DualOrthogonal
public import StacksFrontier.Algebra.DifferentialGraded.Module.ProductHomotopy
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyI
public import StacksCore.Tactic.StacksAttribute

/-! # Modules with property (I) are orthogonal to the acyclic modules

Let `(A, d)` be a differential graded algebra and let `I` be a right differential graded
`A`-module with property (I). Then `Hom_{K(A, d)}(N, I) = 0` for every acyclic differential
graded `A`-module `N`; that is, `I` lies in the right orthogonal of the acyclic objects of the
homotopy category. This is Stacks Tag 09KS, and it is what makes the modules with property (I)
the collection to which the construction of the right derived functors is applied.

## Main results

* `DifferentialGradedModule.rightOrthogonal_acyclic_productDualShifts`: a product of shifts of
  the graded dual of the algebra is orthogonal on the right to the acyclic modules.
* `DifferentialGradedModule.rightOrthogonal_acyclic_of_propertyI`: Stacks Tag 09KS.

## Implementation notes

The proof is the assembly of three parts, each of which lives elsewhere. A shift of `A^∨` is
orthogonal on the right to the acyclic modules
(`DifferentialGradedModule.rightOrthogonal_acyclic_shift_dualRegularModule`, the consequence of
Tag 09K4 drawn in `Module/DualOrthogonal.lean`); orthogonality passes to a product
(`DifferentialGradedModule.rightOrthogonal_acyclic_of_product`), which gives it for the graded
pieces of a property-(I) filtration, since those are products of shifts of `A^∨`; and
orthogonality passes from the graded pieces to the filtered module
(`DifferentialGradedModule.rightOrthogonal_acyclic_of_completeFiltration`), which is the
telescope argument of Tag 09KR carried out on homotopies.

*The product presentation.* `DifferentialGradedModule.productDualShifts` is defined as the
graded dual of a direct sum of shifts of the algebra, `∏ᵢ A^∨[kᵢ] = (⨁ᵢ A[-kᵢ])^∨`, rather than
as a categorical product, because the object representing the categorical product is `private`.
The projections onto the factors are therefore constructed here, by restricting a character of
the direct sum to a summand, and the two elementwise properties characterizing a product —
joint injectivity and degreewise joint surjectivity — are proved from the universal properties
of a direct sum: an element of `⨁ᵢ A` is the finite sum of its one-coordinate parts, and a
family of characters of the summands assembles into a character of the sum by
`DirectSum.toAddMonoid`.

The statement is about a module *equipped with* a property-(I) filtration rather than one merely
admitting one, which is how `DifferentialGradedModule.PropertyIFiltration` presents the notion;
the two differ only by `Nonempty`, and Tag 09KU produces the structure itself.

As everywhere in this chapter's differential graded interface, the base ring, the algebra and
the modules all live in a single universe `u`, following Stacks Tag 09JJ.
The Stacks source is universe-polymorphic in the algebra and the module separately.

## References

* [Stacks Project, Tag 09KS](https://stacks.math.columbia.edu/tag/09KS)
-/

@[expose] public noncomputable section

open CategoryTheory DifferentialGraded MulOpposite
open scoped DirectSum

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

section ProductDualShifts

variable {ι : Type u} [DecidableEq ι] (k : ι → ℤ)

/-! ### The projections of a product of shifts of the dual

The module `productDualShifts A k` is the graded dual of `⨁ᵢ A[-kᵢ]`; its projection onto the
`i`-th factor `A^∨[kᵢ]` restricts a character of the direct sum to the `i`-th summand. -/

/-- The left differential graded module whose dual is `∏ᵢ A^∨[kᵢ]`. -/
private abbrev base (A : DifferentialGradedAlgebra R) : LeftModule A :=
  LeftModule.directSumShifts A fun i => -k i

/-- An element of the direct sum, read as a dependent function on the index set. -/
private abbrev toSum (z : (base k A).M) : ⨁ _ : ι, A.A := z

/-- The one-coordinate injection of the `i`-th summand. -/
private abbrev inc (i : ι) : A.A →+ (⨁ _ : ι, A.A) := DirectSum.of (fun _ : ι => A.A) i

/-- The left action of the algebra on a one-coordinate element is multiplication in that
coordinate. -/
private theorem smul_inc (a : A.A) (i : ι) (b : A.A) :
    a • inc (ι := ι) (A := A) i b = inc (ι := ι) (A := A) i (a * b) := by
  exact (DFinsupp.single_smul (ι := ι) (β := fun _ => A.A) (i := i) a b).symm

/-- The action of the base ring on a one-coordinate element is its action in that
coordinate. -/
private theorem rsmul_inc (r : R) (i : ι) (b : A.A) :
    r • inc (ι := ι) (A := A) i b = inc (ι := ι) (A := A) i (r • b) := by
  exact (DFinsupp.single_smul (ι := ι) (β := fun _ => A.A) (i := i) r b).symm

/-- The differential of the direct sum of shifts acts on a one-coordinate element by the
differential of the algebra in that coordinate, with no sign. -/
private theorem d_inc (i : ι) (a : A.A) :
    toSum k ((base k A).d (inc (ι := ι) (A := A) i a)) = inc (ι := ι) (A := A) i (A.d a) := by
  refine DirectSum.ext fun j => ?_
  rw [show toSum k ((base k A).d (inc (ι := ι) (A := A) i a)) j
      = ((DFinsupp.mapRange.linearMap fun _ : ι => A.d)
          (inc (ι := ι) (A := A) i a)) j from rfl,
    LeftModule.mapRange_d_apply]
  by_cases h : j = i
  · subst h
    rw [DirectSum.of_eq_same, DirectSum.of_eq_same]
  · rw [DirectSum.of_eq_of_ne _ _ _ h, DirectSum.of_eq_of_ne _ _ _ h, map_zero]

/-- A one-coordinate element whose coordinate is homogeneous of degree `p` is homogeneous of
degree `p + kᵢ` in `⨁ⱼ A[-kⱼ]`. -/
private theorem inc_mem (i : ι) {p : ℤ} {a : A.A} (ha : a ∈ A.grading p) :
    inc (ι := ι) (A := A) i a ∈ (base k A).grading (p + k i) := by
  rw [LeftModule.mem_directSumShifts_grading]
  intro j
  by_cases h : j = i
  · subst h
    rw [DirectSum.of_eq_same, show p + k j + -k j = p by ring]
    exact ha
  · rw [DirectSum.of_eq_of_ne _ _ _ h]
    exact Submodule.zero_mem _

/-- A character of `⨁ᵢ A` that kills every one-coordinate element kills everything, because
every element of the direct sum is the finite sum of its one-coordinate parts. -/
private theorem apply_eq_zero_of_inc (l : CharacterModule (base k A).M) (z : (base k A).M)
    (h : ∀ i : ι, l (inc (ι := ι) (A := A) i (toSum k z i)) = 0) : l z = 0 := by
  classical
  calc l z = l (∑ i ∈ DFinsupp.support (toSum k z), inc (ι := ι) (A := A) i (toSum k z i)) := by
        rw [DirectSum.sum_support_of (toSum k z)]
    _ = ∑ i ∈ DFinsupp.support (toSum k z), l (inc (ι := ι) (A := A) i (toSum k z i)) :=
        map_sum _ _ _
    _ = 0 := Finset.sum_eq_zero fun i _ => h i

/-- The character of `A` obtained from a character of `⨁ᵢ A` by restricting to the `i`-th
summand. -/
private def projChar (i : ι) (l : CharacterModule (⨁ _ : ι, A.A)) : CharacterModule A.A :=
  l.comp (inc (A := A) i)

/-- The restriction of a character to a summand, evaluated. -/
private theorem projChar_apply (i : ι) (l : CharacterModule (⨁ _ : ι, A.A)) (a : A.A) :
    projChar i l a = l (inc (ι := ι) (A := A) i a) := rfl

/-- Restricting to a summand sends the degree-`n` piece of `(⨁ᵢ A[-kᵢ])^∨` into the degree-`n`
piece of `A^∨[kᵢ]`, which is the degree-`n + kᵢ` piece of `A^∨`. -/
private theorem projChar_mem_dualPiece (i : ι) {n : ℤ}
    {l : CharacterModule (⨁ _ : ι, A.A)} (hl : l ∈ LeftModule.dualPiece (base k A) n) :
    projChar i l ∈ LeftModule.dualPiece (LeftModule.regular A) (n + k i) := by
  intro p hp a ha
  rw [projChar_apply]
  exact hl (p + k i) (by omega) _ (inc_mem k i ha)

/-- Restricting to a summand preserves the graded dual. -/
private theorem projChar_mem_dualCarrier (i : ι) {l : CharacterModule (⨁ _ : ι, A.A)}
    (hl : l ∈ LeftModule.dualCarrier (base k A)) :
    projChar i l ∈ LeftModule.dualCarrier (LeftModule.regular A) := by
  induction hl using Submodule.iSup_induction' with
  | mem n y hy =>
      exact Submodule.mem_iSup_of_mem (n + k i) (projChar_mem_dualPiece k i hy)
  | zero =>
      rw [show projChar (A := A) i 0 = 0 from CharacterModule.ext _ fun _ => rfl]
      exact Submodule.zero_mem _
  | add y z _ _ ihy ihz =>
      rw [show projChar (A := A) i (y + z) = projChar i y + projChar i z from
        CharacterModule.ext _ fun _ => rfl]
      exact Submodule.add_mem _ ihy ihz

/-- Restriction to a summand intertwines the two dual differentials, up to the sign of the
shift: the degree of a one-coordinate element of `⨁ᵢ A[-kᵢ]` exceeds that of its coordinate
by `kᵢ`, and the two Koszul signs differ by exactly `(-1)^{kᵢ}`. -/
private theorem projChar_dualD0 (i : ι) (l : CharacterModule (base k A).M) :
    projChar i (LeftModule.dualD0 (base k A) l)
      = ((k i).negOnePow : ℤ) • LeftModule.dualD0 (LeftModule.regular A) (projChar i l) := by
  refine CharacterModule.ext _ fun a => ?_
  refine LeftModule.induction_homogeneous (M := LeftModule.regular A)
    (p := fun b => projChar i (LeftModule.dualD0 (base k A) l) b
      = (((k i).negOnePow : ℤ) • LeftModule.dualD0 (LeftModule.regular A) (projChar i l)) b) a
    (fun p b hb => ?_) (by simp) (fun b c hb hc => by
      simp only [map_add, hb, hc])
  have hL : projChar i (LeftModule.dualD0 (base k A) l) b
      = ((p + k i).negOnePow : ℤ) • l (inc (ι := ι) (A := A) i (A.d b)) := by
    rw [projChar_apply,
      show LeftModule.dualD0 (base k A) l (inc (ι := ι) (A := A) i b)
          = l (LeftModule.signedDifferential (base k A) (inc (ι := ι) (A := A) i b)) from rfl,
      LeftModule.signedDifferential_apply_mem (base k A) (inc_mem k i hb), map_zsmul]
    congr 2
    exact d_inc k i b
  have hR : (((k i).negOnePow : ℤ) •
        LeftModule.dualD0 (LeftModule.regular A) (projChar i l)) b
      = (((k i).negOnePow : ℤ) * (p.negOnePow : ℤ)) • l (inc (ι := ι) (A := A) i (A.d b)) := by
    rw [show (((k i).negOnePow : ℤ) •
          LeftModule.dualD0 (LeftModule.regular A) (projChar i l)) b
        = ((k i).negOnePow : ℤ) •
          (LeftModule.dualD0 (LeftModule.regular A) (projChar i l)) b from rfl,
      show LeftModule.dualD0 (LeftModule.regular A) (projChar i l) b
          = projChar i l (LeftModule.signedDifferential (LeftModule.regular A) b) from rfl,
      LeftModule.signedDifferential_apply_mem (LeftModule.regular A) hb, projChar_apply,
      map_zsmul, map_zsmul, smul_smul]
  rw [hL, hR]
  congr 1
  rw [show p + k i = k i + p by ring, Int.negOnePow_add, Units.val_mul]

/-- The projection of `∏ᵢ A^∨[kᵢ]` onto its `i`-th factor. -/
private def proj (i : ι) : productDualShifts A k ⟶ shift (dualRegularModule A) (k i) where
  toFun :=
    { toFun := fun x => ⟨projChar i (Subtype.val x), projChar_mem_dualCarrier k i x.2⟩
      map_add' := fun _ _ => Subtype.ext (CharacterModule.ext _ fun _ => rfl)
      map_smul' := fun r x => Subtype.ext (CharacterModule.ext _ fun a => by
        change (Subtype.val x) (r • inc (ι := ι) (A := A) i a)
          = (Subtype.val x) (inc (ι := ι) (A := A) i (r • a))
        rw [rsmul_inc]) }
  map_smul x a := Subtype.ext (CharacterModule.ext _ fun b => by
    change (Subtype.val x) (a • inc (ι := ι) (A := A) i b)
      = (Subtype.val x) (inc (ι := ι) (A := A) i (a * b))
    rw [smul_inc])
  map_grading _ _ hx := projChar_mem_dualPiece k i (Submodule.mem_inducedGrading.mp hx)
  map_d := LinearMap.ext fun x => Subtype.ext (projChar_dualD0 k i (Subtype.val x))

/-- The projection, computed on the underlying characters. -/
private theorem proj_val (i : ι) (x : (productDualShifts A k).M) (a : A.A) :
    Subtype.val ((proj k i).toFun x) a = Subtype.val x (inc (ι := ι) (A := A) i a) := rfl

/-- **A product of shifts of the graded dual is orthogonal on the right to the acyclic
modules.** -/
theorem rightOrthogonal_acyclic_productDualShifts (A : DifferentialGradedAlgebra R)
    {ι : Type u} [DecidableEq ι] (k : ι → ℤ) :
    (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj (productDualShifts A k)) := by
  classical
  refine rightOrthogonal_acyclic_of_product (proj k) ?_ ?_
    fun i => rightOrthogonal_acyclic_shift_dualRegularModule A (k i)
  · -- the projections are jointly injective
    intro x hx
    refine Subtype.ext (CharacterModule.ext _ fun z => ?_)
    refine apply_eq_zero_of_inc k (Subtype.val x) z fun i => ?_
    have h0 : Subtype.val ((proj k i).toFun x) = 0 := congrArg Subtype.val (hx i)
    exact DFunLike.congr_fun h0 (toSum k z i)
  · -- a family of homogeneous elements of degree `n` has a homogeneous preimage
    intro n q hq
    have hassembled : ∀ (i : ι) (a : A.A),
        (DirectSum.toAddMonoid fun j => (Subtype.val (q j) : A.A →+ _))
            (inc (ι := ι) (A := A) i a) = Subtype.val (q i) a :=
      fun i a =>
        DirectSum.toAddMonoid_of (fun j => (Subtype.val (q j) : A.A →+ _)) i a
    have hmem : (DirectSum.toAddMonoid fun j => (Subtype.val (q j) : A.A →+ _))
        ∈ LeftModule.dualPiece (base k A) n := by
      intro m hm z hz
      refine apply_eq_zero_of_inc k _ z fun i => ?_
      have hqi : Subtype.val (q i) ∈ LeftModule.dualPiece (LeftModule.regular A) (n + k i) :=
        Submodule.mem_inducedGrading.mp (hq i)
      have hzi := (LeftModule.mem_directSumShifts_grading (fun j => -k j) m z).mp hz i
      rw [show m + -k i = m - k i by ring] at hzi
      exact (hassembled i (toSum k z i)).trans (hqi (m - k i) (by omega) _ hzi)
    refine ⟨⟨DirectSum.toAddMonoid fun j => (Subtype.val (q j) : A.A →+ _),
      Submodule.mem_iSup_of_mem n hmem⟩, Submodule.mem_inducedGrading.mpr hmem, fun i => ?_⟩
    refine Subtype.ext (CharacterModule.ext _ fun a => ?_)
    exact (proj_val k i _ a).trans (hassembled i a)

end ProductDualShifts

/-- **Stacks 09KS.** A right differential graded module with property (I) is orthogonal on the
right to the acyclic objects of the homotopy category: every morphism of `K(A, d)` from an
acyclic differential graded module into it vanishes. -/
@[stacks 09KS]
theorem rightOrthogonal_acyclic_of_propertyI {I : DifferentialGradedModule A}
    (F : PropertyIFiltration I) :
    (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj I) :=
  rightOrthogonal_acyclic_of_completeFiltration F.F
    (fun i => @productDualShifts _ _ A _ (F.quotientDecidableEq i) (F.quotientShift i))
    F.ι F.incl F.quotientMap F.injective F.incl_comp F.admissible F.quotient_surjective
    F.quotient_ker F.top_surjective F.separated F.complete
    fun i => @rightOrthogonal_acyclic_productDualShifts _ _ A _
      (F.quotientDecidableEq i) (F.quotientShift i)

end DifferentialGradedModule

end
