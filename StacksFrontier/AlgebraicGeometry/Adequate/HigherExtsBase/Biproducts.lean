module

public import StacksFrontier.AlgebraicGeometry.Adequate.HigherExtsBase.AdequateCategory
public import StacksFrontier.CategoryTheory.Limits.KernelBiproduct

/-!
# Biproducts of adequate functors

The adequate module-valued functors on the commutative `A`-algebras are closed under finite
products. Together with the zero functor and closure under kernels and cokernels this makes the
full subcategory of adequate functors abelian, so that it has all finite limits and colimits —
in particular the pushouts used to test injectivity of an object.

## Main definitions

* `AdequateFunctor.moduleExtensionBiprodIso` — the extension of a direct sum of two `A`-modules
  is the biproduct of their extensions.

## Main results

* `AdequateFunctor.isAdequate_biprod` — the biproduct of two adequate functors is adequate.
* `AdequateFunctor.adequate_isClosedUnderBinaryProducts` and
  `AdequateFunctor.adequate_isClosedUnderFiniteProducts` — the resulting closure properties,
  from which Mathlib's `CategoryTheory.ObjectProperty.instAbelianFullSubcategory` makes the
  adequate functors an abelian category.

## Implementation notes

A kernel presentation `F ≅ ker(α)` of the first functor and `G ≅ ker(β)` of the second present
`F ⊞ G` as the kernel of `biprod.map α β`, by
`CategoryTheory.Limits.kernelBiprodMapIso`. The source and the target of that map are biproducts
of module extensions, hence extensions of direct sums, hence adequate; so the kernel is adequate
by [Stacks, Tag 06V3].

This is the finite case of [Stacks, Tag 06V4], which asserts adequacy of arbitrary direct sums
and of arbitrary colimits of adequate functors; only the finite biproducts are proved here, and
the tag is therefore not claimed.

Binary biproducts of module-valued functors are supplied as a direct instance reducing to
`PresheafOfModules.hasLimitsOfShape`, for the reason recorded at
`AdequateFunctor.hasKernel_presheafOfModules`: reached through the abelian structure the
instance search is quadratic in the ambient `HasLimit` instances and times out at the
independent universes used for module-valued functors.

## References

* [Stacks Project, Tag 06V3](https://stacks.math.columbia.edu/tag/06V3)
* [Stacks Project, Tag 06V4](https://stacks.math.columbia.edu/tag/06V4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AdequateFunctor

variable (A : Type u) [CommRing A]

/-- Binary biproducts of module-valued functors. Supplied as a direct instance reducing to
`PresheafOfModules.hasLimitsOfShape`: reached instead through the abelian structure, the search
is quadratic in the ambient `HasLimit` instances and times out at the independent universes used
for module-valued functors. -/
public instance hasBinaryBiproducts_moduleValuedFunctor :
    HasBinaryBiproducts (ModuleValuedFunctor.{w, v} A) :=
  haveI : HasBinaryProducts (ModuleValuedFunctor.{w, v} A) :=
    PresheafOfModules.hasLimitsOfShape _ _
  HasBinaryBiproducts.of_hasBinaryProducts

/-- The extension of a direct sum of two `A`-modules is the biproduct of their extensions:
extension of scalars is additive and preserves finite colimits, hence preserves binary
biproducts. -/
public noncomputable def moduleExtensionBiprodIso (M N : ModuleCat.{max u v w} A) :
    (moduleExtensionFunctor.{max u v w, v} A).obj (M ⊞ N) ≅
      (moduleExtensionFunctor.{max u v w, v} A).obj M ⊞
        (moduleExtensionFunctor.{max u v w, v} A).obj N :=
  letI : PreservesBinaryBiproducts (moduleExtensionFunctor.{max u v w, v} A) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  Functor.mapBiprod _ _ _

/-- The biproduct of two module extensions is adequate, being the extension of the direct sum. -/
public lemma isAdequate_biprod_moduleExtension (M N : ModuleCat.{max u v w} A) :
    IsAdequate (𝟭 _) ((moduleExtensionFunctor.{max u v w, v} A).obj M ⊞
      (moduleExtensionFunctor.{max u v w, v} A).obj N :
        ModuleValuedFunctor.{max u v w, v} A) :=
  IsAdequate.of_iso (isAdequate_moduleExtension (M ⊞ N))
    (moduleExtensionBiprodIso.{u, v, w} A M N).symm

/-- The biproduct of two adequate functors is adequate: kernel presentations of the two factors
present the biproduct as the kernel of the biproduct of the two presenting maps, whose source and
target are biproducts of module extensions. -/
public lemma isAdequate_biprod {F G : ModuleValuedFunctor.{max u v w, v} A}
    (hF : IsAdequate (𝟭 _) F) (hG : IsAdequate (𝟭 _) G) :
    IsAdequate (𝟭 _) (F ⊞ G) := by
  obtain ⟨M₁, N₁, α, ⟨eF⟩⟩ := (isAdequate_iff F).mp hF
  obtain ⟨M₂, N₂, β, ⟨eG⟩⟩ := (isAdequate_iff G).mp hG
  exact IsAdequate.of_iso (isAdequate_kernel (biprod.map α β)
    (isAdequate_biprod_moduleExtension.{u, v, w} A M₁ M₂)
    (isAdequate_biprod_moduleExtension.{u, v, w} A N₁ N₂))
    (biprod.mapIso eF eG ≪≫ kernelBiprodMapIso α β)

/-- Adequacy is stable under binary products, which in a preadditive category are the binary
biproducts. -/
public instance adequate_isClosedUnderBinaryProducts :
    (adequate.{u, v, max u v w} A).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    refine (adequate.{u, v, max u v w} A).prop_of_iso ?_
      (IsAdequate.of_iso (isAdequate_biprod.{u, v, w} A
        (p.prop_diag_obj (.mk .left)) (p.prop_diag_obj (.mk .right)))
        (biprod.isoProd _ _).symm)
    exact IsLimit.conePointUniqueUpToIso (prodIsProd _ _)
      ((IsLimit.postcomposeHomEquiv (diagramIsoPair p.diag) _).2 p.isLimit)

/-- Adequacy is stable under finite products: it is stable under binary products and the zero
functor is adequate. -/
public instance adequate_isClosedUnderFiniteProducts :
    (adequate.{u, v, max u v w} A).IsClosedUnderFiniteProducts :=
  .mk'

end AdequateFunctor

end
