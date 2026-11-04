module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleAbelian

/-!
# The pullback of right differential graded modules is additive

Let `f` be a morphism of ringed sites and let `φ : A' ⟶ f_*A` be a semilinear homomorphism of
sheaves of differential graded algebras. The pullback `f^*` of right differential graded
`A'`-modules is additive on morphisms, so it carries a biproduct of right differential graded
`A'`-modules to a biproduct of right differential graded `A`-modules.

## Main results

* `SheafOfModules.DifferentialGradedModule.PullbackData.map_add` and `map_zero`: the pullback of
  a morphism is additive in the morphism.
* `SheafOfModules.DifferentialGradedModule.PullbackData.functor_additive`: the pullback functor
  is additive.

## Implementation notes

Only the universal property of the unit is used, not a construction of the pullback: the sum of
the two pullbacks of morphisms satisfies the factorisation that characterises the pullback of
the sum, because postcomposition of a semilinear map with a morphism and precomposition of one
with a morphism are both additive on local sections. In particular no continuity hypothesis on
the underlying functor of sites is needed, and the direct image does not appear.

## References

* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a a' m m' v u v' u'

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  {u : C' ⥤ C} {σ : R'.obj ⟶ u.op ⋙ R.obj} {A : DifferentialGradedAlgebra.{t, a} R}
  {A' : DifferentialGradedAlgebra.{t, a'} R'}
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A}

namespace PullbackData

variable (PD : PullbackData.{t, a, m, v, u, a', m', v', u'} φ)
  {M M₂ : DifferentialGradedModule.{t, a', m'} A'}

/-- The pullback of a sum of morphisms of right differential graded modules is the sum of the
pullbacks. -/
theorem map_add (g g' : M ⟶ M₂) : PD.map (g + g') = PD.map g + PD.map g' :=
  ((PD.isPullback M).uniq _ _ (SemilinearHom.ext fun i V x ↦ by
    have e : ∀ h : M ⟶ M₂,
        homSections ((PD.map h).toHomologicalComplex.f i) (u.op.obj V) ((PD.unit M).app i V x) =
          (PD.unit M₂).app i V (homSections (h.toHomologicalComplex.f i) V x) :=
      fun h ↦ congrArg (fun θ : SemilinearHom φ M (PD.obj M₂) ↦ θ.app i V x)
        (PD.unit_postcomp_map h)
    show homSections ((PD.map g + PD.map g').toHomologicalComplex.f i) (u.op.obj V)
        ((PD.unit M).app i V x) =
      (PD.unit M₂).app i V (homSections ((g + g').toHomologicalComplex.f i) V x)
    rw [add_f, homSections_add, e g, e g', add_f, homSections_add]
    exact (((PD.unit M₂).app i V).map_add _ _).symm)).symm

/-- The pullback of the zero morphism of right differential graded modules is zero. -/
theorem map_zero : PD.map (0 : M ⟶ M₂) = 0 :=
  ((PD.isPullback M).uniq _ _ (SemilinearHom.ext fun i V x ↦ by
    show homSections ((0 : PD.obj M ⟶ PD.obj M₂).toHomologicalComplex.f i) (u.op.obj V)
        ((PD.unit M).app i V x) =
      (PD.unit M₂).app i V (homSections ((0 : M ⟶ M₂).toHomologicalComplex.f i) V x)
    rw [zero_f, homSections_zero, zero_f, homSections_zero]
    exact (((PD.unit M₂).app i V).map_zero).symm)).symm

/-- **The pullback functor of right differential graded modules is additive**, so it carries a
biproduct to a biproduct. -/
instance functor_additive : PD.functor.Additive where
  map_add {_ _ g g'} := PD.map_add g g'

end PullbackData

end DifferentialGradedModule

end SheafOfModules
