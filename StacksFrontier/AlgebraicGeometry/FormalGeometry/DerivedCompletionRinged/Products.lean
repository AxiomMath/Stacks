module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Basic
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.RestrictionOfComplexes
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation

/-!
# The derived-completeness predicate on a ringed site is inhabited

`AlgebraicGeometry.RingedSite.IsDerivedComplete` ([Stacks, Tag 0999]) asks, besides the
condition `T(K|_U, f) = 0`, for additivity and exactness of restriction to the slice site and for
countable products in the derived category of sheaves of modules on that slice site. The
countable products are supplied by
`Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules`, with no exactness
hypothesis on the countable products of sheaves of modules, and every zero object of `D(𝒪)` is
derived complete along every ideal sheaf. So the predicate is inhabited.

## Main results

* `AlgebraicGeometry.RingedSite.hasProductsOfShape_nat_derivedCategory_over` — the countable
  products of the derived category over a slice site, in the spelling the Tag 0999 predicate
  asks for.
* `AlgebraicGeometry.RingedSite.isDerivedComplete_of_isZero` — a zero object is derived
  complete.

## Implementation notes

The statements are at `HasDerivedCategory.standard`, the model at which `IsDerivedComplete` is
defined.

The coefficient universe of the ringed site is taken to be `max u v`, as in [Stacks, Tag 099F]
itself. At a general coefficient universe `r` the ambient `Abelian (SheafOfModules 𝒪)` instance
is not found, because the one available is stated at the module universe `max u v r w`.

No `@[stacks]` attribute is attached. Tag 0999 is already carried by the predicate itself, and
Tag 099F is not proved here.

## References

* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 099F](https://stacks.math.columbia.edu/tag/099F)
* [Stacks Project, Tag 0BK6](https://stacks.math.columbia.edu/tag/0BK6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped IsMulCommutative

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, max u v}) (U : X.C)

/-- Countable products in the derived category of sheaves of modules on the slice site of a
ringed site at an object. -/
theorem hasProductsOfShape_nat_derivedCategory_over :
    HasProductsOfShape ℕ
      (DerivedCategory
        (SheafOfModules.{max u v w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))) :=
  Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules _

/-- **A zero object is derived complete along every ideal sheaf.** In particular the
derived-completeness predicate of [Stacks, Tag 0999] is inhabited. -/
theorem isDerivedComplete_of_isZero
    (I : SheafOfModules.Submodule
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {K : DerivedCategory (SheafOfModules.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hK : IsZero K) :
    IsDerivedComplete.{u, v, max u v, max u v} X I K := by
  intro V f _
  let RV := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V
  let A := SheafOfModules.{max u v} RV
  let : Linear (CatCenter A) A := Linear.ofRingMorphism (RingHom.id (CatCenter A))
  let : ∀ W : (Over V)ᵒᵖ, IsMulCommutative (RV.obj.obj W) := fun W ↦ by
    show IsMulCommutative (X.O.obj.obj (op W.unop.left))
    infer_instance
  have hLim : PreservesFiniteLimits
      (SheafOfModules.overFunctor.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits V
  have hColim : PreservesFiniteColimits
      (SheafOfModules.overFunctor.{max u v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits V
  have hProd : HasProductsOfShape ℕ (DerivedCategory A) :=
    hasProductsOfShape_nat_derivedCategory_over.{u, v, max u v} X V
  refine ⟨inferInstance, hLim, hColim, hProd, isDerivedCompleteAt_of_isNilpotent ⟨1, ?_⟩⟩
  have hz : IsZero ((SheafOfModules.overFunctor.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.obj K) :=
    Functor.map_isZero _ hK
  have h1 : (1 : End ((SheafOfModules.overFunctor.{max u v}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.obj K)) = 0 :=
    End.homEquiv.injective (hz.eq_of_src _ _)
  rw [pow_one, h1, smul_zero]

end AlgebraicGeometry.RingedSite

end
