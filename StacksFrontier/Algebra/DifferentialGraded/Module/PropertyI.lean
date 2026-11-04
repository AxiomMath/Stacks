module

public import StacksFrontier.Algebra.DifferentialGraded.NativeCover
public import StacksFrontier.Algebra.DifferentialGraded.Module.Admissible
public import StacksFrontier.Algebra.DifferentialGraded.Module.CharacterDual
public import StacksFrontier.Algebra.DifferentialGraded.Module.PropertyP
public import StacksFrontier.Algebra.DifferentialGraded.Module.Shift
public import StacksCore.Tactic.StacksAttribute

/-! # Property (I) for differential graded modules

Let `(A, d)` be a differential graded algebra. A right differential graded `A`-module `I` has
*property (I)* (Stacks 09KQ) when it carries an exhaustive decreasing filtration

`I = F₀ I ⊇ F₁ I ⊇ F₂ I ⊇ ⋯ ⊇ 0`

by differential graded submodules such that `I = lim I / Fₚ I`, the maps
`I / F_{i+1} I → I / Fᵢ I` are admissible epimorphisms, and the successive quotients
`Fᵢ I / F_{i+1} I` are products of shifts `A^∨[k]` of the graded dual of the algebra.

This file defines the filtration data and the products of shifts of `A^∨` that its graded
pieces are required to be. It is the dual of
`StacksFrontier/Algebra/DifferentialGraded/Module/PropertyP.lean`, which does the same for
property (P), and it is the interface across which the two halves of Stacks 09LI meet: Tag 09KU
produces a quasi-isomorphism from an arbitrary module into one carrying such a filtration, and
Tag 09KS shows that such a module is orthogonal on the right to the acyclic modules. Composing
the two supplies the hypothesis of
`DifferentialGradedModule.isRightDerivable_of_exists_quasiIso_rightOrthogonal`.

## Main definitions

* `DifferentialGraded.LeftModule.directSumShifts`: the direct sum `⨁ᵢ A[jᵢ]` of shifts of the
  algebra, as a *left* differential graded `A`-module.
* `DifferentialGradedModule.productDualShifts`: the product `∏ᵢ A^∨[kᵢ]` of shifts of the
  graded dual of the algebra, as a differential graded `A`-module.
* `DifferentialGradedModule.PropertyIFiltration`: the data of a filtration exhibiting
  property (I).

## Main results

* `DifferentialGradedModule.productDualShifts_separated` and
  `DifferentialGradedModule.productDualShifts_lift`: `∏ᵢ A^∨[kᵢ]` satisfies the elementwise
  universal property of a degreewise product — a point is determined by its components, and a
  family of homogeneous components of a common degree is realized.

## Implementation notes

*The product of shifts of `A^∨` is presented as the dual of a direct sum of shifts of `A`.*
The graded dual turns direct sums into products — `(⨁ᵢ Xᵢ)^∨ = ∏ᵢ Xᵢ^∨`, because a character of
a direct sum is a family of characters — and `(A[j])^∨ = A^∨[-j]`. The latter is an equality of
degree-`n` pieces, of carriers and of differentials: a degree-`n` character of `A[j]` is
supported on `A^{j-n}`, which is the support of a degree-`n` character of `A^∨[-j]`; and both
differentials act on a character supported in degree `j - n - 1` by `-(-1)^n (· ∘ d_A)`, the
right-handed shift's sign `(-1)^j` cancelling against the parity operator's `(-1)^{j-n-1}`.
Formalizing that identification as an isomorphism of differential graded modules is a named
follow-up, `dualShift_iso`, and is not done here: the two carriers are submodules of the same
character module but of types that agree only under default-transparency unfolding, so the
identity map between them is awkward to write and no consumer needs it yet. Granting it,

`(⨁ᵢ A[-kᵢ])^∨ = ∏ᵢ A^∨[kᵢ]`,

which is the definition taken here.

`DifferentialGradedModule A` does have all `Type u`-indexed
products (`DifferentialGradedModule.instHasProducts`), formed degreewise, and `∏ᶜ` of the shifts
would be the more direct reading of Stacks 09KQ. A nameable such object now exists —
`DifferentialGradedModule.product` (`Module/Product.lean`), with elementwise projections and
`product.mem_grading_iff` — so the obstruction recorded here previously, that the representing
object was `private` in both of its copies, no longer applies.

The form below is nevertheless kept, because it is the one both halves of Stacks 09LI can
compute with directly. Replacing it by `product (fun i => …)` is a worthwhile dedup but not a
docstring fix: it still needs the unproved `dualShift_iso` (`(M[c])^∨ ≅ (M^∨)[-c]`) to match the
shifts up. Identifying this form with `∏ᶜ` abstractly is the separate statement
`productDualShifts_isLimit`, not proved here; `product.isLimit` now supplies the limit side of
it, so what remains is only the comparison.

*The unbundled algebra is borrowed, not rebuilt.* `directSumShifts` obtains its direct-sum
decomposition from `DifferentialGraded.NativeCover.ShiftSum.isInternal_gradingSub`, which is stated
  for the
unbundled encoding of `StacksFrontier/Algebra/DifferentialGraded/Basic.lean`; the translation of a
bundled `DifferentialGradedAlgebra` into that encoding is
`DifferentialGradedModule.Unbundled.algebra` of `Module/PropertyP.lean`, which is why this file
imports it.

*The left shift carries no sign.* For a right differential graded module the Leibniz rule
`d(x·a) = d(x)·a + (-1)^{deg x} x·d(a)` has a sign depending on the degree of the *module*
element, which forces `d_{M[k]} = (-1)^k d_M`. For a left module the rule is
`d(a·x) = d(a)·x + (-1)^{deg a} a·d(x)`, whose sign does not involve the degree of `x`, so the
shift of a left module has the *same* differential. That is why `directSumShifts` below has a
componentwise `A.d` with no sign, unlike its right-handed namesake in `Module/PropertyP.lean`.

*The filtration is presented by its stages, not by its quotients.* Property (I) is stated in
Stacks in terms of the quotients `I / Fᵢ I`; the structure below records the stages `Fᵢ I`
together with injections `Fᵢ I ⟶ I`, which carry the same information and are what the
construction of Tag 09KU produces directly. The two conditions that mention the quotients are
recorded elementwise instead:

* `I = F₀ I` is `top_surjective`;
* `⋂ᵢ Fᵢ I = 0` — injectivity of `I → lim I / Fᵢ I` — is `separated`;
* surjectivity of `I → lim I / Fᵢ I` is `complete`, stated *in each degree*, because the limit
  is taken in differential graded modules and limits there are degreewise. A compatible family
  in `lim I / Fᵢ I` of degree `n` is a sequence `xᵢ` of degree-`n` elements of `I` with
  `x_{i+1} - xᵢ ∈ Fᵢ I`, and `complete` produces the element of `I` it is the image of.

*Condition (2) is recorded in a different — and stronger — form than Stacks states it, and
this is deliberate.* Stacks 09KQ(2) asks that the maps `I / F_{i+1} I → I / Fᵢ I` be admissible
epimorphisms. The field `admissible` below asks instead that the inclusions `F_{i+1} I → Fᵢ I`
be admissible monomorphisms, i.e. that each stage be a graded direct summand of the previous
one. The two are not formally equivalent: the first says the graded sequence
`0 → Fᵢ/F_{i+1} → I/F_{i+1} → I/Fᵢ → 0` splits, the second that
`0 → F_{i+1} → Fᵢ → Fᵢ/F_{i+1} → 0` does.

Three reasons for the choice. In Stacks both are consequences of condition (3) via Tag 09K2
(a graded-injective submodule is an admissible one), so neither is really an extra hypothesis
there; Tag 09K2 is formalized only as
`Stacks.DifferentialGradedModule.AdmissibleMono.admissibleMono_of_gradedInjective`, over an
unrelated encoding of differential graded modules, so here one of them must be recorded as data.
The construction of Tag 09KU produces the chosen one directly and not the other: its filtration of
`I = ∏ⱼ Iⱼ[-j]` by the sub-products `F_{2i} I = ∏_{j ≥ i} Iⱼ[-j]` is split as a graded module by
projecting onto the complementary factors. And the chosen one is what the consumer needs: Tag
09KS filters each `I / Fᵢ I` finitely with graded pieces `Fⱼ / F_{j+1}`, and `F_{j+1} / Fᵢ →
Fⱼ / Fᵢ` inherits a graded splitting from `Fⱼ = F_{j+1} ⊕ Cⱼ` because `Fᵢ ⊆ F_{j+1}`.

The consequence to be aware of is that `PropertyIFiltration` is a slightly *stronger* notion
than Stacks' property (I). That makes Tag 09KU (which constructs one) a stronger statement and
Tag 09KS (which consumes one) a weaker one, and it leaves the composite they are wanted for —
the hypothesis of
`DifferentialGradedModule.isRightDerivable_of_exists_quasiIso_rightOrthogonal`, namely that
every module admits a quasi-isomorphism into one orthogonal on the right to the acyclics —
exactly as strong as Stacks'. Nothing downstream of that composite sees the difference.

## References

* [Stacks Project, Tag 09KQ](https://stacks.math.columbia.edu/tag/09KQ)
* [Stacks Project, Tag 0FQD](https://stacks.math.columbia.edu/tag/0FQD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped DirectSum

universe u

namespace DifferentialGraded.LeftModule

variable {R : Type u} [CommRing R]

variable {A : DifferentialGradedAlgebra.{u, u} R}

/-- The componentwise differential on `⨁ᵢ A` acts componentwise. -/
theorem mapRange_d_apply {ι : Type u} (x : ⨁ _ : ι, A.A) (i : ι) :
    (DFinsupp.mapRange.linearMap (fun _ : ι => A.d) x) i = A.d (x i) :=
  DFinsupp.mapRange_apply _ (fun _ => map_zero A.d) x i

/-- `⨁ᵢ A[jᵢ]`, the direct sum of shifts of the algebra, as a *left* differential graded
`A`-module: the underlying left module is `⨁ᵢ A`, an element is homogeneous of degree `n` when
its `i`-th component lies in `A^{n + jᵢ}`, and the differential acts componentwise by `d_A`
with no sign (see the implementation note above). -/
@[implicit_reducible]
def directSumShifts (A : DifferentialGradedAlgebra.{u, u} R) {ι : Type u} [DecidableEq ι]
    (j : ι → ℤ) : LeftModule A where
  M := ⨁ _ : ι, A.A
  grading := DifferentialGraded.NativeCover.ShiftSum.gradingSub R A.A A.grading ι j
  decomposition := DirectSum.IsInternal.chooseDecomposition _
    (DifferentialGraded.NativeCover.ShiftSum.isInternal_gradingSub R A.A A.grading
      (DifferentialGraded.NativeCover.Native.algebra (DifferentialGradedModule.Unbundled.algebra A)
        (DifferentialGradedModule.Unbundled.algebra_isLawful A)) ι j)
  isScalarTower := IsScalarTower.of_algebraMap_smul (fun r x => DirectSum.ext fun i => by
    rw [DirectSum.smul_apply, DirectSum.smul_apply, Algebra.algebraMap_eq_smul_one,
      smul_eq_mul, smul_mul_assoc, one_mul])
  smul_mem := by
    intro m n a x ha hx i
    rw [DirectSum.smul_apply, show m + n + j i = m + (n + j i) by omega]
    exact SetLike.mul_mem_graded ha (hx i)
  d := DFinsupp.mapRange.linearMap (fun _ : ι => A.d)
  d_comp_d := by
    refine LinearMap.ext fun x => DirectSum.ext fun i => ?_
    rw [LinearMap.comp_apply, mapRange_d_apply, mapRange_d_apply]
    simpa using LinearMap.congr_fun A.d_comp_d (x i)
  d_mem := by
    intro n x hx i
    rw [mapRange_d_apply, show n + 1 + j i = n + j i + 1 by omega]
    exact A.d_mem (n + j i) (x i) (hx i)
  leibniz := by
    intro m n a x ha hx
    refine DirectSum.ext fun i => ?_
    simp only [DirectSum.add_apply, DirectSum.smul_apply]
    exact A.leibniz m (n + j i) a (x i) ha (hx i)

/-- Membership in the degree-`n` piece of a direct sum of shifts is componentwise. -/
theorem mem_directSumShifts_grading {ι : Type u} [DecidableEq ι] (j : ι → ℤ) (n : ℤ)
    (x : ⨁ _ : ι, A.A) :
    x ∈ (directSumShifts A j).grading n ↔ ∀ i, x i ∈ A.grading (n + j i) := Iff.rfl

end DifferentialGraded.LeftModule

namespace DifferentialGradedModule

open DifferentialGraded.LeftModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-- The product `∏ᵢ A^∨[kᵢ]` of shifts of the graded dual of the algebra, presented as the
graded dual of the direct sum `⨁ᵢ A[-kᵢ]` of shifts of the algebra. Its degree-`n` part is the
group of characters of `⨁ᵢ A^{-n-kᵢ}`, which is `∏ᵢ (A^∨)^{n + kᵢ}`. -/
def productDualShifts (A : DifferentialGradedAlgebra.{u, u} R) {ι : Type u} [DecidableEq ι]
    (k : ι → ℤ) : DifferentialGradedModule.{u, u, u} A :=
  DifferentialGraded.LeftModule.dual
    (DifferentialGraded.LeftModule.directSumShifts A fun i => -k i)

/-! ### `∏ᵢ A^∨[kᵢ]` really is a product -/

/-- The `i`-th component of a point of `∏ᵢ A^∨[kᵢ]`: the character of `A` obtained by
restricting the underlying character along the inclusion of the `i`-th summand. -/
def productDualShiftsComp {ι : Type u} [DecidableEq ι] {k : ι → ℤ}
    (x : (productDualShifts A k).M) (i : ι) : CharacterModule A.A :=
  (dualChar x).comp (DirectSum.lof R ι (fun _ : ι => A.A) i).toAddMonoidHom

/-- The `i`-th component of `x` evaluated at `a` is the underlying character of `x` evaluated
at the image of `a` in the `i`-th summand. -/
@[simp] theorem productDualShiftsComp_apply {ι : Type u} [DecidableEq ι] {k : ι → ℤ}
    (x : (productDualShifts A k).M) (i : ι) (a : A.A) :
    productDualShiftsComp x i a = dualChar x (DirectSum.lof R ι (fun _ : ι => A.A) i a) := rfl

/-- An additive map out of `⨁ᵢ A` is the sum of its values on the summands. -/
private theorem addMonoidHom_directSum_eq_sum {ι : Type u} [DecidableEq ι]
    [∀ x : A.A, Decidable (x ≠ 0)] {G : Type*} [AddCommMonoid G]
    (l : (⨁ _ : ι, A.A) →+ G) (s : ⨁ _ : ι, A.A) :
    l s = ∑ i ∈ DFinsupp.support s, l (DirectSum.lof R ι (fun _ : ι => A.A) i (s i)) := by
  conv_lhs => rw [show s = DFinsupp.sum s DFinsupp.single from (DFinsupp.sum_single).symm]
  rw [DFinsupp.sum, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [DirectSum.lof_eq_of]; rfl

/-- **A point of `∏ᵢ A^∨[kᵢ]` is determined by its components.** The summands generate the
direct sum, so a character killing each of them is zero. -/
theorem productDualShifts_separated {ι : Type u} [DecidableEq ι] {k : ι → ℤ}
    (x : (productDualShifts A k).M) (h : ∀ i, productDualShiftsComp x i = 0) : x = 0 := by
  classical
  have key : ∀ s : ⨁ _ : ι, A.A, dualChar x s = 0 := fun s => by
    refine (addMonoidHom_directSum_eq_sum (dualChar x) s).trans ?_
    refine Finset.sum_eq_zero fun i _ => ?_
    exact (productDualShiftsComp_apply x i (s i)).symm.trans (by rw [h i]; rfl)
  refine dualChar_injective ?_
  ext s
  exact (key s).trans rfl

open scoped Classical in
/-- A character of `⨁ᵢ A` is the sum of its values on the summands. -/
theorem char_directSum_eq_sum {ι : Type u} [DecidableEq ι]
    (l : CharacterModule (⨁ _ : ι, A.A)) (s : ⨁ _ : ι, A.A) :
    l s = ∑ i ∈ DFinsupp.support s, l (DirectSum.lof R ι (fun _ : ι => A.A) i (s i)) :=
  addMonoidHom_directSum_eq_sum l s

/-- **A family of characters assembles into a point of the product.** If the `i`-th character of
`A` is supported in degree `-(n + kᵢ)`, the family is the family of components of a homogeneous
element of degree `n` of `∏ᵢ A^∨[kᵢ]`. -/
theorem productDualShifts_lift {ι : Type u} [DecidableEq ι] (k : ι → ℤ) (n : ℤ)
    (q : ι → CharacterModule A.A)
    (hq : ∀ i, q i ∈ dualPiece (regular A) (n + k i)) :
    ∃ x : (productDualShifts A k).M, x ∈ (productDualShifts A k).grading n ∧
      ∀ i, productDualShiftsComp x i = q i := by
  classical
  let l : CharacterModule (⨁ _ : ι, A.A) :=
    DFinsupp.sumAddHom (fun i => (q i : A.A →+ AddCircle (1 : ℚ)))
  have hlapply : ∀ (i : ι) (a : A.A), l (DirectSum.lof R ι (fun _ : ι => A.A) i a) = q i a := by
    intro i a
    rw [DirectSum.lof_eq_of]
    exact DFinsupp.sumAddHom_single (fun i => (q i : A.A →+ AddCircle (1 : ℚ))) i a
  have hpiece : l ∈ dualPiece
      (DifferentialGraded.LeftModule.directSumShifts A fun i => -k i) n := by
    intro m hm (s : ⨁ _ : ι, A.A) hs
    rw [char_directSum_eq_sum l s]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hlapply i (s i)]
    exact hq i (m + -k i) (by omega) (s i) (hs i)
  refine ⟨dualOf l (Submodule.mem_iSup_of_mem n hpiece), mem_dual_grading.mpr hpiece,
    fun i => ?_⟩
  ext a
  exact hlapply i a

/-- A *property-(I) filtration* of a right differential graded `A`-module `I` (Stacks 09KQ): an
exhaustive decreasing filtration `I = F 0 ⊇ F 1 ⊇ ⋯` by differential graded submodules whose
inclusions are admissible monomorphisms, which is separated and complete, and whose successive
quotients are products of shifts of `A^∨`.

The stages are presented by injective homomorphisms `ι i : F i ⟶ I` rather than as submodules,
and the graded pieces by surjective homomorphisms out of `F i` onto products of shifts of `A^∨`
whose kernel is the next stage. -/
structure PropertyIFiltration (I : DifferentialGradedModule.{u, u, u} A) where
  /-- The stages `F i` of the decreasing filtration. -/
  F : ℕ → DifferentialGradedModule.{u, u, u} A
  /-- The embedding of the `i`-th stage into the filtered module. -/
  ι : ∀ i, Hom (F i) I
  /-- Each stage embeds. -/
  injective : ∀ i, Function.Injective (ι i).toFun
  /-- The transition inclusion `F (i + 1) ⟶ F i`. -/
  incl : ∀ i, Hom (F (i + 1)) (F i)
  /-- The transition inclusions are compatible with the embeddings into `I`. -/
  incl_comp : ∀ i x, (ι i).toFun ((incl i).toFun x) = (ι (i + 1)).toFun x
  /-- Property (I)(2): every transition inclusion is an admissible monomorphism. -/
  admissible : ∀ i, IsAdmissibleMono (incl i)
  /-- The filtration starts at the whole module: `I = F 0 I`. -/
  top_surjective : Function.Surjective (ι 0).toFun
  /-- Property (I)(1), separatedness: `⋂ᵢ F i I = 0`, i.e. `I → lim I / F i I` is injective. -/
  separated : ∀ x : I.M, (∀ i, ∃ y, (ι i).toFun y = x) → x = 0
  /-- Property (I)(1), completeness: in each degree, `I → lim I / F i I` is surjective. -/
  complete : ∀ (n : ℤ) (x : ℕ → I.M), (∀ i, x i ∈ I.grading n) →
    (∀ i, ∃ y, y ∈ (F i).grading n ∧ x (i + 1) - x i = (ι i).toFun y) →
    ∃ z, z ∈ I.grading n ∧ ∀ i, ∃ y, y ∈ (F i).grading n ∧ z - x i = (ι i).toFun y
  /-- The factors of the `i`-th graded piece `F i I / F (i + 1) I`. -/
  quotientIndex : ℕ → Type u
  /-- Decidable equality of the factors, needed to form their direct sum. -/
  quotientDecidableEq : ∀ i, DecidableEq (quotientIndex i)
  /-- The shift attached to each factor of the `i`-th graded piece. -/
  quotientShift : ∀ i, quotientIndex i → ℤ
  /-- Property (I)(3): the projection of `F i` onto its graded piece. -/
  quotientMap : ∀ i,
    Hom (F i) (@productDualShifts _ _ A _ (quotientDecidableEq i) (quotientShift i))
  /-- The projection onto the `i`-th graded piece is surjective. -/
  quotient_surjective : ∀ i, Function.Surjective (quotientMap i).toFun
  /-- Its kernel is the next stage, so the graded piece really is `F i / F (i + 1)`. -/
  quotient_ker : ∀ i, LinearMap.ker (quotientMap i).toFun = LinearMap.range (incl i).toFun

namespace PropertyIFiltration

variable {I : DifferentialGradedModule.{u, u, u} A} (F : PropertyIFiltration I)

/-- The transition inclusions of a property-(I) filtration are injective. -/
theorem incl_injective (i : ℕ) : Function.Injective (F.incl i).toFun :=
  (F.admissible i).injective

/-- An element of the `i`-th stage dies in the `i`-th graded piece exactly when it comes from
the `(i + 1)`-st stage. -/
theorem quotientMap_eq_zero_iff (i : ℕ) (x : (F.F i).M) :
    (F.quotientMap i).toFun x = 0 ↔ ∃ y, (F.incl i).toFun y = x := by
  rw [← LinearMap.mem_ker, F.quotient_ker i]
  exact LinearMap.mem_range

/-- The bottom stage of a property-(I) filtration *is* the filtered module. -/
theorem bottom_bijective : Function.Bijective (F.ι 0).toFun :=
  ⟨F.injective 0, F.top_surjective⟩

end PropertyIFiltration

end DifferentialGradedModule

end
