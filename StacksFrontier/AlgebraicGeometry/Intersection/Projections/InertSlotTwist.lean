module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModulePoints
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TripleTautologicalGerm
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic

/-!
# `𝒪(1,1)` on a scheme over two projective spaces, as `𝒪(1,1,1)` with an inert third slot

The classifying morphism of Tag 0B1S needs an invertible module on a scheme carrying *two*
morphisms to projective spaces, together with global sections of it bilinear in a pair of
degree-one forms: the parametrisation
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEnd` of
`StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionParametrisation` is bilinear in
`(f, f')`, so the coordinates of its value are sections of `𝒪(1,1)` on `X × Y × 𝔸(…)`.

The library has the one-slot pullback section
`AlgebraicGeometry.ProjectiveSpaceOfModule.pullbackTautSection` and the three-slot package
`AlgebraicGeometry.ProjectiveSpaceOfModule.tripleTaut`, and nothing in between. Writing the
two-slot package as a one-slot deletion of the three-slot one would duplicate the whole germ
calculus — the trilinearity, the normalisation of each slot against a reference vector, the sum
formula and the vanishing criterion — which is the duplication the three-slot package was
factored out to remove.

So no two-slot package is written. Instead the third slot is made **inert**: take `M₃` to be the
ground field as a module over itself, and `p₃` the structure morphism followed by the unique
point of `𝐏(k)`. Then

* `𝒪(1,1,1)` for `(p₁, p₂, p₃)` is an invertible module on the scheme, by the three-slot
  package, and is the `𝒪(1,1)` wanted — there is no need to *identify* it with a tensor of two
  pullbacks, because nothing downstream asks for that: the classifying morphism
  `Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.morphismOfGeneratingSections` asks
  only for an invertible module and a linear map into its global sections;
* `tripleTautSection a b 1` is **bilinear** in `(a, b)`, by two of the three trilinearity
  lemmas; and
* the third slot never obstructs: the degree-one form `1 : k` avoids the homogeneous prime at
  the unique point of `𝐏(k)`, so the third conjunct of the nonvanishing criterion and the third
  ratio of the germ formula are discharged once and for all.

The unique point of `𝐏(k)` and the value of a morphism onto it are not new either: they are
`AlgebraicGeometry.ProjectiveSpaceOfModule.pointOfDual` and
`AlgebraicGeometry.ProjectiveSpaceOfModule.pointOfDual_base` of
`StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceOfModulePoints`, for an arbitrary
module and an arbitrary functional taking the value one. So neither the identification of `𝐏(k)`
with `Spec k` nor a separate computation of the value of the inert slot has to be made: the
former is not needed at all, and the latter is that lemma.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.onePoint`: the `k`-valued point of `𝐏(k)` cut out by
  the identity functional.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.inertSlot`: the inert third projection
  `T ⟶ 𝐏(k)` attached to a structure morphism `T ⟶ Spec k`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.pairTaut` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.pairTautSection`: `𝒪(1,1)` and its bilinear
  sections, as abbreviations for the three-slot ones with the inert slot in place — so that every
  lemma about the three-slot package applies to them unchanged.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.pairTautGlobal`: the same sections read as *global*
  sections `Γ(𝒪(1,1), ⊤)`, which is the spelling the classifying morphism consumes. Also an
  abbreviation, for the value over `⊤` of the family, so the bilinearity lemmas below apply to it
  unchanged; the bridge it realises is `Stacks.NonvanishingSpelling.sectionsEquiv`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.inertSlot_comp` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.inertSlot_base`: the inert slot lies over `Spec k`
  and is constant at the unique point of `𝐏(k)`. These are the two hypotheses `h₃` and `e₃` that
  the three-slot germ calculus asks of a third projection.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.ι_one_notMem_inertSlot`: the inert slot's form never
  vanishes.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingLocus_pairTautSection_iff`: a tensor
  of two tautological sections is nonvanishing exactly where both degree-one forms avoid the two
  homogeneous primes.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.pairTautSection_eval_add_one`,
  `AlgebraicGeometry.ProjectiveSpaceOfModule.pairTautSection_eval_add_two`,
  `AlgebraicGeometry.ProjectiveSpaceOfModule.pairTautSection_eval_top_smul_one` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.pairTautSection_eval_top_smul_two`: bilinearity.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.pairGerm_sum_sub_smul_mem` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingLocus_pair_iff_of_germ_sub_smul_mem`:
  the germ formula for a signed sum of tensors and the vanishing criterion, with the third ratio
  gone.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isInvertibleModule_pairTaut` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingOpen_pairTautGlobal_iff`: the
  invertibility and the nonvanishing criterion at the scheme spelling, which is what the
  classifying morphism asks for. The instance crosses the same syntactic gap as
  `Stacks.NonvanishingSpelling.isInvertible_toRingedSpace`, and the criterion is the locus
  identification of that file, which holds because the two stalk-module structures are equal.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open Stacks.SheafOfModules Stacks.SheafOfModules.TensorStalkRingedSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

/-! ### The unique point of `𝐏(k)` and the inert slot -/

section Inert

variable (k : Type u) [Field k]

/-- **The identity is a nonzero functional on the ground field as a module over itself.** -/
public theorem dualId_ne_zero : (LinearMap.id : Module.Dual k k) ≠ 0 := by
  intro h
  exact one_ne_zero (α := k) (by simpa using LinearMap.congr_fun h (1 : k))

/-- The identity functional takes the value one at `1`. -/
public theorem dualId_apply_one : (LinearMap.id : Module.Dual k k) (1 : k) = 1 := rfl

/-- **The `k`-valued point of `𝐏(k)` cut out by the identity functional.** The projective space
of a one-dimensional module has a single point, and this is it, as a morphism from `Spec k`. -/
public def onePoint : Spec (.of k) ⟶ projectiveSpaceOfModule k k :=
  pointOfDual k k (LinearMap.id : Module.Dual k k) (dualId_apply_one k)

/-- The unique point of `𝐏(k)` is a point over `Spec k`. -/
public theorem onePoint_comp :
    onePoint k ≫ projectiveSpaceOfModuleToSpec k k = 𝟙 _ :=
  pointOfDual_comp k k (LinearMap.id : Module.Dual k k) (dualId_apply_one k)

/-- The unique point of `𝐏(k)` is the point the identity functional cuts out. -/
public theorem onePoint_base (a : Spec (.of k)) :
    (onePoint k).base a =
      linearFunctionalPoint k k (LinearMap.id : Module.Dual k k) (dualId_ne_zero k) :=
  pointOfDual_base k k (LinearMap.id : Module.Dual k k) (dualId_ne_zero k)
    (dualId_apply_one k) a

variable {T : Scheme.{u}} (τ : T ⟶ Spec (.of k))

/-- **The inert third projection**: the structure morphism followed by the unique point of
`𝐏(k)`. Its only role is to let the three-slot tautological package stand in for a two-slot one,
and it is inert in the sense that its degree-one form `1 : k` vanishes nowhere. -/
public def inertSlot : T ⟶ projectiveSpaceOfModule k k := τ ≫ onePoint k

/-- **The inert slot lies over `Spec k`** — the hypothesis `h₃` of the three-slot germ
calculus. -/
public theorem inertSlot_comp :
    inertSlot k τ ≫ projectiveSpaceOfModuleToSpec k k = τ := by
  rw [inertSlot, Category.assoc, onePoint_comp, Category.comp_id]

/-- **The inert slot is constant at the unique point of `𝐏(k)`** — the hypothesis `e₃` of the
three-slot germ calculus, at every point of `T` at once. -/
public theorem inertSlot_base (t : T) :
    (inertSlot k τ).base t =
      linearFunctionalPoint k k (LinearMap.id : Module.Dual k k) (dualId_ne_zero k) :=
  onePoint_base k (τ.base t)

/-- **The inert slot's form vanishes nowhere.** The degree-one form `1 : k` avoids the
homogeneous prime at the unique point of `𝐏(k)`, because the identity functional does not kill
`1`. -/
public theorem ι_one_notMem_inertSlot (t : T) :
    SymmetricAlgebra.ι k k (1 : k) ∉ ((inertSlot k τ).base t).asHomogeneousIdeal := by
  change SymmetricAlgebra.ι k k (1 : k) ∉
    ((onePoint k).base (τ.base t)).asHomogeneousIdeal
  rw [onePoint, ι_mem_pointOfDual_iff k k (LinearMap.id : Module.Dual k k)
    (dualId_apply_one k) (τ.base t) (1 : k), dualId_apply_one k]
  exact one_ne_zero

end Inert

/-! ### `𝒪(1,1)` and its bilinear sections -/

section Pair

variable (k M₁ M₂ : Type u) [Field k]
  [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂]
  {T : Scheme.{u}} (p₁ : T ⟶ projectiveSpaceOfModule k M₁)
  (p₂ : T ⟶ projectiveSpaceOfModule k M₂) (τ : T ⟶ Spec (.of k))

attribute [local instance] isInvertible_tautologicalModule
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- **The invertible module `𝒪(1,1) = p₁^* 𝒪(1) ⊗ p₂^* 𝒪(1)`** on a scheme carrying two
morphisms to projective spaces, realised as `𝒪(1,1,1)` with the inert third slot. It is an
abbreviation and not a definition, so that every lemma about `𝒪(1,1,1)` applies to it with no
restatement. -/
public abbrev pairTaut : T.Modules := tripleTaut k M₁ M₂ k p₁ p₂ (inertSlot k τ)

/-- **`𝒪(1,1)` is invertible.** -/
public theorem isInvertible_pairTaut :
    Stacks.SheafOfModules.IsInvertible T.presheaf
      (structureSheafRing T.toRingedSpace).property (pairTaut k M₁ M₂ p₁ p₂ τ) :=
  isInvertible_tripleTaut k M₁ M₂ k p₁ p₂ (inertSlot k τ)

/-- **The tensor `p₁^*(ι a) ⊗ p₂^*(ι b)` of two tautological sections**, a global section of
`𝒪(1,1)`: the three-slot tensor with the inert slot's form `1 : k` in the third place. -/
public abbrev pairTautSection (a : M₁) (b : M₂) : (pairTaut k M₁ M₂ p₁ p₂ τ).sections :=
  tripleTautSection k M₁ M₂ k p₁ p₂ (inertSlot k τ) a b (1 : k)

/-- **A tensor of two tautological sections is nonvanishing at a point exactly when both
degree-one forms avoid the homogeneous primes of the two projections** of that point. The third
conjunct of the three-slot criterion is discharged by
`AlgebraicGeometry.ProjectiveSpaceOfModule.ι_one_notMem_inertSlot`. -/
public theorem mem_nonvanishingLocus_pairTautSection_iff (a : M₁) (b : M₂) (t : T) :
    t ∈ Stacks.SheafOfModules.nonvanishingLocus (X := T.toRingedSpace)
        (pairTaut k M₁ M₂ p₁ p₂ τ) (pairTautSection k M₁ M₂ p₁ p₂ τ a b) ↔
      SymmetricAlgebra.ι k M₁ a ∉ (p₁.base t).asHomogeneousIdeal ∧
        SymmetricAlgebra.ι k M₂ b ∉ (p₂.base t).asHomogeneousIdeal := by
  rw [mem_nonvanishingLocus_tripleTautSection_iff k M₁ M₂ k p₁ p₂ (inertSlot k τ) a b (1 : k) t]
  exact and_congr_right fun _ => and_iff_left (ι_one_notMem_inertSlot k τ t)

/-! #### Bilinearity -/

/-- **The tensor is additive in its first vector.** -/
public theorem pairTautSection_eval_add_one (a a' : M₁) (b : M₂) (U : (Opens ↥T)ᵒᵖ) :
    (pairTautSection k M₁ M₂ p₁ p₂ τ (a + a') b).eval U =
      (pairTautSection k M₁ M₂ p₁ p₂ τ a b).eval U +
        (pairTautSection k M₁ M₂ p₁ p₂ τ a' b).eval U :=
  tripleTautSection_eval_add_one k M₁ M₂ k p₁ p₂ (inertSlot k τ) a a' b (1 : k) U

/-- **The tensor is additive in its second vector.** -/
public theorem pairTautSection_eval_add_two (a : M₁) (b b' : M₂) (U : (Opens ↥T)ᵒᵖ) :
    (pairTautSection k M₁ M₂ p₁ p₂ τ a (b + b')).eval U =
      (pairTautSection k M₁ M₂ p₁ p₂ τ a b).eval U +
        (pairTautSection k M₁ M₂ p₁ p₂ τ a b').eval U :=
  tripleTautSection_eval_add_two k M₁ M₂ k p₁ p₂ (inertSlot k τ) a b b' (1 : k) U

/-- **The tensor is `k`-homogeneous in its first vector**, over the top open. -/
public theorem pairTautSection_eval_top_smul_one
    (h₁ : p₁ ≫ projectiveSpaceOfModuleToSpec k M₁ = τ) (r : k) (a : M₁) (b : M₂) :
    (pairTautSection k M₁ M₂ p₁ p₂ τ (r • a) b).eval (op ⊤) =
      scalarTop k τ r • (pairTautSection k M₁ M₂ p₁ p₂ τ a b).eval (op ⊤) :=
  tripleTautSection_eval_top_smul_one k M₁ M₂ k p₁ p₂ (inertSlot k τ) τ h₁ r a b (1 : k)

/-- **The tensor is `k`-homogeneous in its second vector**, over the top open. -/
public theorem pairTautSection_eval_top_smul_two
    (h₂ : p₂ ≫ projectiveSpaceOfModuleToSpec k M₂ = τ) (r : k) (a : M₁) (b : M₂) :
    (pairTautSection k M₁ M₂ p₁ p₂ τ a (r • b)).eval (op ⊤) =
      scalarTop k τ r • (pairTautSection k M₁ M₂ p₁ p₂ τ a b).eval (op ⊤) :=
  tripleTautSection_eval_top_smul_two k M₁ M₂ k p₁ p₂ (inertSlot k τ) τ h₂ r a b (1 : k)

end Pair

/-! ### The germ of a section of `𝒪(1,1)` -/

section PairGerm

variable (k M₁ M₂ : Type u) [Field k]
  [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂]
  {T : Scheme.{u}} (p₁ : T ⟶ projectiveSpaceOfModule k M₁)
  (p₂ : T ⟶ projectiveSpaceOfModule k M₂) (τ : T ⟶ Spec (.of k))

attribute [local instance] isInvertible_tautologicalModule
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- `𝒪(1,1)` retyped as a sheaf of modules over the structure sheaf of `T` read as a ringed
space. -/
public abbrev pairSh : _root_.SheafOfModules.{u} (structureSheafRing T.toRingedSpace) :=
  tripleSh k M₁ M₂ k p₁ p₂ (inertSlot k τ)

/-- **The germ at a point of the tensor of two tautological sections.** -/
public abbrev pairGerm (t : T) (a : M₁) (b : M₂) :
    grpStalk T.toRingedSpace (pairSh k M₁ M₂ p₁ p₂ τ).val t :=
  tripleGerm k M₁ M₂ k p₁ p₂ (inertSlot k τ) t a b (1 : k)

/-- The submodule `𝔪ₜ · 𝒪(1,1)ₜ` of the stalk at `t`. -/
public abbrev pairMax (t : T) :
    Submodule (ringStalk T.toRingedSpace t)
      (grpStalk T.toRingedSpace (pairSh k M₁ M₂ p₁ p₂ τ).val t) :=
  tripleMax k M₁ M₂ k p₁ p₂ (inertSlot k τ) t

variable (t : T) (f₁ : Module.Dual k M₁) (hf₁ : f₁ ≠ 0)
  (e₁ : p₁.base t = linearFunctionalPoint k M₁ f₁ hf₁)
  (f₂ : Module.Dual k M₂) (hf₂ : f₂ ≠ 0)
  (e₂ : p₂.base t = linearFunctionalPoint k M₂ f₂ hf₂)
  (h₁ : p₁ ≫ projectiveSpaceOfModuleToSpec k M₁ = τ)
  (h₂ : p₂ ≫ projectiveSpaceOfModuleToSpec k M₂ = τ)

include e₁ e₂ h₁ h₂ in
/-- **The germ formula for a signed sum of tensors of two tautological sections.** A `2 × 2`
minor of a pair of rows is such a sum, one term per basis vector of whichever factor the bilinear
entry is expanded in. The third ratio of the three-slot formula is `1`, the inert slot's form
being `1 : k` and its functional the identity. -/
public theorem pairGerm_sum_sub_smul_mem {ι : Type*} [Fintype ι] (a₀ : M₁) (ha₀ : f₁ a₀ ≠ 0)
    (b₀ : M₂) (hb₀ : f₂ b₀ ≠ 0) (A₁ A₂ : ι → M₁) (B₁ B₂ : ι → M₂) :
    (∑ i, (pairGerm k M₁ M₂ p₁ p₂ τ t (A₁ i) (B₁ i) -
        pairGerm k M₁ M₂ p₁ p₂ τ t (A₂ i) (B₂ i))) -
        scalarGerm k τ t
            (∑ i, (f₁ (A₁ i) / f₁ a₀ * (f₂ (B₁ i) / f₂ b₀) -
              f₁ (A₂ i) / f₁ a₀ * (f₂ (B₂ i) / f₂ b₀))) •
          pairGerm k M₁ M₂ p₁ p₂ τ t a₀ b₀ ∈ pairMax k M₁ M₂ p₁ p₂ τ t := by
  have h := tripleGerm_sum_sub_smul_mem k M₁ M₂ k p₁ p₂ (inertSlot k τ) t f₁ hf₁ e₁ f₂ hf₂ e₂
    (LinearMap.id : Module.Dual k k) (dualId_ne_zero k) (inertSlot_base k τ t) τ h₁ h₂
    (inertSlot_comp k τ) a₀ ha₀ b₀ hb₀ (1 : k) one_ne_zero
    A₁ A₂ B₁ B₂ (fun _ => (1 : k)) (fun _ => (1 : k))
  simpa [dualId_apply_one] using h

include e₁ e₂ in
/-- **The vanishing criterion for a global section of `𝒪(1,1)`.** A section whose germ at `t` is,
modulo `𝔪ₜ · 𝒪(1,1)ₜ`, the scalar `D / (f₁ a₀ · f₂ b₀)` times the germ of the reference tensor is
nonvanishing at `t` exactly when `D ≠ 0`. -/
public theorem mem_nonvanishingLocus_pair_iff_of_germ_sub_smul_mem (a₀ : M₁) (ha₀ : f₁ a₀ ≠ 0)
    (b₀ : M₂) (hb₀ : f₂ b₀ ≠ 0) (S : (pairTaut k M₁ M₂ p₁ p₂ τ).sections) (D : k)
    (hS : grpGerm T.toRingedSpace (pairSh k M₁ M₂ p₁ p₂ τ).val t ⊤ (Opens.mem_top t)
            (S.eval (op ⊤)) -
          scalarGerm k τ t (D / (f₁ a₀ * f₂ b₀)) • pairGerm k M₁ M₂ p₁ p₂ τ t a₀ b₀ ∈
        pairMax k M₁ M₂ p₁ p₂ τ t) :
    t ∈ Stacks.SheafOfModules.nonvanishingLocus (X := T.toRingedSpace)
        (pairTaut k M₁ M₂ p₁ p₂ τ) S ↔ D ≠ 0 := by
  refine mem_nonvanishingLocus_iff_of_germ_sub_smul_mem k M₁ M₂ k p₁ p₂ (inertSlot k τ) t
    f₁ hf₁ e₁ f₂ hf₂ e₂ (LinearMap.id : Module.Dual k k) (dualId_ne_zero k)
    (inertSlot_base k τ t) τ a₀ ha₀ b₀ hb₀ (1 : k) one_ne_zero S D ?_
  simpa [dualId_apply_one] using hS

end PairGerm

/-! ### `𝒪(1,1)` at the spelling the classifying morphism consumes -/

section PairGlobal

variable (k M₁ M₂ : Type u) [Field k]
  [AddCommGroup M₁] [Module k M₁] [AddCommGroup M₂] [Module k M₂]
  {T : Scheme.{u}} (p₁ : T ⟶ projectiveSpaceOfModule k M₁)
  (p₂ : T ⟶ projectiveSpaceOfModule k M₂) (τ : T ⟶ Spec (.of k))

attribute [local instance] isInvertible_tautologicalModule
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-- **`𝒪(1,1)` is invertible in the scheme spelling.** `Stacks.Ample.IsInvertibleModule` is an
abbreviation for the same `IsInvertible` as
`AlgebraicGeometry.ProjectiveSpaceOfModule.isInvertible_pairTaut` proves, with the sheaf
condition supplied as a different — and propositionally irrelevant — term; instance search is
syntactic and does not cross that gap on its own, exactly as recorded for
`Stacks.NonvanishingSpelling.isInvertible_toRingedSpace`. This instance crosses it once, and it is
what lets `Stacks.NonvanishingOpen.nonvanishingOpen` and
`Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.morphismOfGeneratingSections` be
applied to `𝒪(1,1)`. -/
public instance isInvertibleModule_pairTaut :
    Stacks.Ample.IsInvertibleModule T (pairTaut k M₁ M₂ p₁ p₂ τ) :=
  isInvertible_pairTaut k M₁ M₂ p₁ p₂ τ

/-- **The tensor of two tautological sections as a global section of `𝒪(1,1)`**, which is the
spelling `Stacks.AlgebraicGeometry.ProjectiveSpaceGeneratingSections.morphismOfGeneratingSections`
consumes. It is the value over `⊤` of the restriction-compatible family
`AlgebraicGeometry.ProjectiveSpaceOfModule.pairTautSection`, which is the bridge
`Stacks.NonvanishingSpelling.sectionsEquiv`; an abbreviation, so that the bilinearity lemmas
stated at `.eval (op ⊤)` apply to it with no restatement. -/
public abbrev pairTautGlobal (a : M₁) (b : M₂) : Γ(pairTaut k M₁ M₂ p₁ p₂ τ, ⊤) :=
  (pairTautSection k M₁ M₂ p₁ p₂ τ a b).eval (op ⊤)

/-- **The nonvanishing open of a tensor of two tautological sections**, at the scheme spelling: it
is the locus where both degree-one forms avoid the homogeneous primes of the two projections. This
is `AlgebraicGeometry.ProjectiveSpaceOfModule.mem_nonvanishingLocus_pairTautSection_iff` carried
across `Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq`, the two loci being equal because
the two stalk-module structures are. -/
public theorem mem_nonvanishingOpen_pairTautGlobal_iff (a : M₁) (b : M₂) (t : T) :
    t ∈ Stacks.NonvanishingOpen.nonvanishingOpen T (pairTaut k M₁ M₂ p₁ p₂ τ)
        (pairTautGlobal k M₁ M₂ p₁ p₂ τ a b) ↔
      SymmetricAlgebra.ι k M₁ a ∉ (p₁.base t).asHomogeneousIdeal ∧
        SymmetricAlgebra.ι k M₂ b ∉ (p₂.base t).asHomogeneousIdeal := by
  have h := Set.ext_iff.mp (Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq T
    (pairTaut k M₁ M₂ p₁ p₂ τ) (pairTautSection k M₁ M₂ p₁ p₂ τ a b)) t
  exact h.symm.trans (mem_nonvanishingLocus_pairTautSection_iff k M₁ M₂ p₁ p₂ τ a b t)

end PairGlobal

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
