module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence
public import StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic

/-!
# The contraction of an iterated pullback is monoidal

Let `f : X' ⟶ X` and `f' : X'' ⟶ X'` be morphisms of ringed spaces.
`Stacks.PullbackPseudofunctor.modulePullbackCompIso` is the canonical isomorphism
`(f' ≫ f)^* ≅ f'^* ∘ f^*` of pullback functors on sheaves of modules, and its components are
the comparison map `Stacks.Sheaves.RingedSpaceDifferentials.modulePullbackComparison`. That
file characterises the comparison by its adjoint description and proves it invertible and
natural, and it records that it says nothing about *sections* and nothing about the monoidal
structure.

This file supplies both. The comparison carries the pullback-unit image of a local section to
the iterated pullback-unit image, and it is compatible with the comparison of Stacks 01CD and
with the structure-sheaf comparison: writing `c` for the first and `u` for the second,

    (f' ≫ f)^*(A ⊗ B) ──c──> (f' ≫ f)^*A ⊗ (f' ≫ f)^*B
           │                               │
         θ_{A ⊗ B}                     θ_A ⊗ θ_B
           v                               v
     f'^*(f^*(A ⊗ B)) ──f'^*(c)≫c──> f'^*f^*A ⊗ f'^*f^*B

commutes, and so does the corresponding triangle for the unit object. In other words `θ` is a
monoidal natural isomorphism from `f^*` followed by `f'^*` to `(f' ≫ f)^*`, for the monoidal
structure of `Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal`.

## Main definitions

* `Stacks.PullbackCompMonoidal.comparison`: **the comparison `(f' ≫ f)^*M ⟶ f'^*(f^*M)`**,
  retyped at the `Stacks.RingedSpace.structureRingSheaf` spelling of the category of sheaves of
  modules, which is the spelling the monoidal structure of Tag 01CA is stated for.
* `Stacks.PullbackCompMonoidal.comparisonIso`: the same, as an isomorphism.

## Main results

* `Stacks.PullbackCompMonoidal.comparison_pullbackUnit`: **the comparison on a pullback-unit
  image**, `θ(ι_{f' ≫ f}(m)) = ι_{f'}(ι_f(m))`.
* `Stacks.PullbackCompMonoidal.comparison_tensor`: **the comparison is compatible with the
  comparison of Stacks 01CD.**
* `Stacks.PullbackCompMonoidal.comparison_unit`: **the comparison is compatible with the
  structure-sheaf comparison.**

## Implementation notes

The two spellings of the category of sheaves of modules on a ringed space —
`structureSheafRing X` and `Stacks.RingedSpace.structureRingSheaf X` — are
equal by `rfl` (`Stacks.RingedSpace.structureRingSheaf_eq_ringSheaf`) and are not syntactically
equal. `Stacks.PullbackPseudofunctor` is stated in the first, the monoidal structure of Tag
01CA in the second, so a statement mixing them is not type-correct at `implicit` transparency
and `rw` refuses any goal containing it, reporting a pattern rather than the cause. The cure
prescribed in this directory is a `def` with an **ascribed** type: `comparison` is the
comparison ascribed at the `pullbackFunctor` spelling, every statement below is written with
it, and the crossing happens once, inside a proof given by `:=`, which is defeq-tolerant.

For the same reason the two coherence proofs state their intermediate steps as `have`s **at the
index `(opensMap (f' ≫ f)).op.obj U`** and discharge them by terms rather than by `rw`. That
index and the iterated `(opensMap f').op.obj ((opensMap f).op.obj U)` are also `rfl`-equal and
not syntactically equal, so the section formulas of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorCoherence`, which are indexed by a
single pullback, do not match a goal written at the composite. Rewriting the index directly is
not available: the sections of a sheaf of modules depend on it, so the motive of such a rewrite
is not type-correct.

Both coherences are proved on local sections, through
`Stacks.PullbackTensorCoherence.pullback_hom_ext` and `pullback_tensor_hom_ext`: a morphism out
of a pullback is determined by its values on the pullback-unit images, and out of a pullback of
a tensor product by its values on those of the local pure tensors. This is what
`comparison_pullbackUnit` is for, and it is why no tensorator of a monoidal functor appears in
any proof here.

## Not done here

* No universe generality beyond `RingedSpace.{u, u}`: everything inherits the restriction of
  `StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace`, forced by Mathlib's
  `PresheafOfModules.instIsRightAdjointPushforward`.
* The coherences are stated for the pair (`pullbackTensorComparison`,
  `pullbackUnitComparison`), i.e. for the monoidal structure
  `Stacks.PullbackTensorCoherence.pullbackComparisonMonoidal`, and not for
  `Stacks.PullbackGradedAlgebra.pullbackStrictMonoidal`, the monoidal structure on the same
  functor assembled through the localization bridge. That is a matter of spelling rather than a
  gap, because the two structures are identified: the tensorators in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStrictTensorator`, where
  `Stacks.PullbackStrictTensorator.delta_pullbackStrictMonoidal_eq` says the oplax tensorator of
  `pullbackStrictMonoidal` is `pullbackTensorComparison` and `mu_pullbackStrictMonoidal_eq`
  gives the lax one as its inverse; and the unit morphisms in
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackStrictUnit`, by
  `Stacks.PullbackStrictUnit.epsilon_pullbackFunctor` and
  `pullbackUnitComparison_comp_pullbackOne`. So the statements here do transport both to the
  multiplication `Stacks.PullbackGradedAlgebra.pullbackMul` and to the global unit
  `Stacks.PullbackGradedAlgebra.pullbackOne` of a pulled-back sheaf of graded algebras:
  `Stacks.AlgebraicGeometry.ProjRepresentsF1.mulSheaf_pullbackGradedAlgebra` is the closed form
  of that multiplication which the first identification yields, and
  `StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadruplePullback` and
  `StacksFrontier.AlgebraicGeometry.TwistTensor.PsiLegVeroneseMultiplicative` are what consume the
  two halves.
* No associativity or unitality coherence for the comparison itself, i.e. nothing relating the
  comparisons of a triple composite or of a composite with an identity.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry TopologicalSpace
open Stacks.RingedSpace Stacks.PullbackTensorCoherence
open RingedSpaceModuleAdjunction

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

universe u

namespace Stacks.PullbackCompMonoidal

variable {X X' X'' : RingedSpace.{u, u}} (f : X' ⟶ X) (f' : X'' ⟶ X')

/-- **The comparison `(f' ≫ f)^*M ⟶ f'^*(f^*M)`** of
`Stacks.Sheaves.RingedSpaceDifferentials.modulePullbackComparison`, retyped so that its source
and target are spelled with `Stacks.RingedSpace.pullbackFunctor`, which is the spelling the
monoidal structure of Tag 01CA is stated for. -/
def comparison (M : SheafOfModules.{u} (structureRingSheaf X)) :
    (pullbackFunctor (f' ≫ f)).obj M ⟶
      (pullbackFunctor f').obj ((pullbackFunctor f).obj M) :=
  Stacks.Sheaves.RingedSpaceDifferentials.modulePullbackComparison f f' M

/-- The comparison `(f' ≫ f)^*M ⟶ f'^*(f^*M)` is an isomorphism. -/
instance isIso_comparison (M : SheafOfModules.{u} (structureRingSheaf X)) :
    IsIso (comparison f f' M) :=
  Stacks.PullbackPseudofunctor.isIso_modulePullbackComparison f f' M

/-- The comparison `(f' ≫ f)^*M ≅ f'^*(f^*M)`, as an isomorphism. -/
def comparisonIso (M : SheafOfModules.{u} (structureRingSheaf X)) :
    (pullbackFunctor (f' ≫ f)).obj M ≅
      (pullbackFunctor f').obj ((pullbackFunctor f).obj M) :=
  asIso (comparison f f' M)

/-- The forward morphism of `comparisonIso` is `comparison`. -/
@[simp] theorem comparisonIso_hom (M : SheafOfModules.{u} (structureRingSheaf X)) :
    (comparisonIso f f' M).hom = comparison f f' M := rfl

/-- Naturality of the comparison in the sheaf of modules. -/
theorem comparison_naturality {M N : SheafOfModules.{u} (structureRingSheaf X)} (φ : M ⟶ N) :
    comparison f f' M ≫ (pullbackFunctor f').map ((pullbackFunctor f).map φ) =
      (pullbackFunctor (f' ≫ f)).map φ ≫ comparison f f' N :=
  Stacks.PullbackPseudofunctor.modulePullbackComparison_naturality f f' φ

/-- **The comparison on a pullback-unit image**: it carries the pullback-unit image along
`f' ≫ f` of a local section to the iterated pullback-unit image along `f` and then `f'`.

This is the adjoint description of the comparison, read on local sections. -/
theorem comparison_pullbackUnit (M : SheafOfModules.{u} (structureRingSheaf X))
    (U : (Opens X.carrier)ᵒᵖ) (m : M.val.obj U) :
    (ConcreteCategory.hom ((comparison f f' M).val.app ((opensMap (f' ≫ f)).op.obj U)))
        (pullbackUnit (f' ≫ f) M U m) =
      pullbackUnit f' ((pullbackFunctor f).obj M) ((opensMap f).op.obj U)
        (pullbackUnit f M U m) := by
  have h := Stacks.PullbackPseudofunctor.unit_comp_map_modulePullbackCompIso_hom_app f f' M
  rw [Stacks.PullbackPseudofunctor.modulePullbackCompIso_hom_app f f' M] at h
  exact congrArg (fun φ => (ConcreteCategory.hom (φ.val.app U)) m) h

/-- Naturality of the pullback-unit image along `f'`, read at the index of the composite
`f' ≫ f`. -/
private theorem map_pullbackUnit_comp_index {M N : SheafOfModules.{u} (structureRingSheaf X')}
    (g : M ⟶ N) (U : (Opens X.carrier)ᵒᵖ) (x : M.val.obj ((opensMap f).op.obj U)) :
    (ConcreteCategory.hom (((pullbackFunctor f').map g).val.app ((opensMap (f' ≫ f)).op.obj U)))
        (pullbackUnit f' M ((opensMap f).op.obj U) x) =
      pullbackUnit f' N ((opensMap f).op.obj U) (ConcreteCategory.hom (g.val.app _) x) :=
  pullbackUnit_naturality f' g _ x

/-- **The comparison is compatible with the comparison of Stacks 01CD.** Contracting the
iterated pullback of a tensor product and then splitting the product agrees with splitting the
product first and contracting each factor. -/
theorem comparison_tensor (A B : SheafOfModules.{u} (structureRingSheaf X)) :
    comparison f f' (A ⊗ B) ≫ (pullbackFunctor f').map (pullbackTensorComparison f A B) ≫
        pullbackTensorComparison f' ((pullbackFunctor f).obj A)
          ((pullbackFunctor f).obj B) =
      pullbackTensorComparison (f' ≫ f) A B ≫
        (comparison f f' A ⊗ₘ comparison f f' B) := by
  refine pullback_tensor_hom_ext (f' ≫ f) (fun U a b => ?_)
  rw [SheafOfModules.comp_val_app_apply, SheafOfModules.comp_val_app_apply,
    SheafOfModules.comp_val_app_apply, pullbackTensorComparison_pullbackUnit,
    tensorHom_tmul, comparison_pullbackUnit, comparison_pullbackUnit,
    comparison_pullbackUnit, map_pullbackUnit_comp_index, pullbackTensorComparison_pullbackUnit]
  exact pullbackTensorComparison_pullbackUnit f' ((pullbackFunctor f).obj A)
    ((pullbackFunctor f).obj B) ((opensMap f).op.obj U) (pullbackUnit f A U a)
    (pullbackUnit f B U b)

/-- **The comparison is compatible with the structure-sheaf comparison.** Contracting the
iterated pullback of the unit object and then comparing twice with the structure sheaf agrees
with comparing once along the composite. -/
theorem comparison_unit :
    comparison f f' (𝟙_ (SheafOfModules.{u} (structureRingSheaf X))) ≫
        (pullbackFunctor f').map (pullbackUnitComparison f) ≫ pullbackUnitComparison f' =
      pullbackUnitComparison (f' ≫ f) := by
  refine pullback_hom_ext (f' ≫ f) (fun U r => ?_)
  rw [SheafOfModules.comp_val_app_apply, SheafOfModules.comp_val_app_apply,
    comparison_pullbackUnit, map_pullbackUnit_comp_index, pullbackUnitComparison_pullbackUnit f U r,
    pullbackUnitComparison_pullbackUnit (f' ≫ f) U r]
  exact pullbackUnitComparison_pullbackUnit f' ((opensMap f).op.obj U) (sharp f U r)

end Stacks.PullbackCompMonoidal

end
