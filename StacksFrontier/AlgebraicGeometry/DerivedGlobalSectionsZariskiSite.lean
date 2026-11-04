module

public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerived
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EvaluationConservative
public import StacksFrontier.Homology.PseudoCoherent.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Derived global sections on the small Zariski site, and over the base ring

Let `X` be a scheme over a ring `A`, by `f : X ⟶ Spec A`.  There are two unbounded right derived
functors of global sections on `X` in this development, and they are not the same functor:

* `Stacks.DerivedFunctor.totalRightDerived (SheafOfModules.evaluation X.ringCatSheaf (op ⊤))`,
  the derived functor of evaluation at the final object `⊤` of the small Zariski site of `X`,
  with values in `D(Γ(X, 𝒪_X))`.  This is the shape in which derived sections over an *object of
  a site* occur — `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedSections` at
  `AlgebraicGeometry.Scheme.zariskiRingedSite`, and the right-hand side of the module-valued
  clause of Stacks 0D6H at `ε`,
  `AlgebraicGeometry.SmallEtale.derivedModuleSectionsRestrictModuleIso`.
* `AlgebraicGeometry.derivedGlobalSectionsOver f`, with values in `D(A)`.  This is the shape in
  which `RΓ` occurs on the *ringed space*, and it is the one the affine comparisons use:
  `AlgebraicGeometry.derivedGlobalSectionsQuasicoherent` is built from
  `AlgebraicGeometry.derivedGlobalSectionsOver (𝟙 (Spec R))`.

This file crosses between them.  The two underived functors are built from the same raw material
— `AlgebraicGeometry.globalSectionsOver` *is* `SheafOfModules.evaluation X.ringCatSheaf (op ⊤)`
followed by the restriction of scalars along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`, by `rfl` — so what
has to be crossed is only the passage from a derived functor to the derived functor of a
postcomposition, and that is
`Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso`: restriction of
scalars is exact, so deriving evaluation and then applying it is deriving the composite.

## Main results

* `AlgebraicGeometry.derivedGlobalSectionsOverEvaluationIso`: for any scheme `X` over `A`,
  derived evaluation at the final object of the small Zariski site of `X`, followed by
  restriction of scalars to `A`, is `A`-linear derived global sections.

## Implementation notes

**The restriction of scalars cannot be dropped**, and it is not an artefact of the universe
bookkeeping: the two functors land in the derived categories of modules over two different
rings, `Γ(X, 𝒪_X)` and `A`, and the comparison between them is restriction of scalars along the
structure morphism.  For `f = 𝟙 (Spec A)`, which is the case
`AlgebraicGeometry.derivedGlobalSectionsQuasicoherent` is about, that ring map is the inverse of
`AlgebraicGeometry.Scheme.ΓSpecIso` and so an isomorphism — but an isomorphism of rings, not an
equality, and the two module categories are therefore equivalent and not equal.

*Why the three instances below are declared by hand.* The target of
`SheafOfModules.evaluation X.ringCatSheaf (op ⊤)` is `ModuleCat ↑(X.ringCatSheaf.obj.obj (op ⊤))`,
whose ring is the `RingCat`-valued section ring, whereas `ModuleCat.restrictScalars` is applied
to a homomorphism whose target is the `CommRingCat`-valued `Γ(X, ⊤)`.  The two are definitionally
equal — which is why `AlgebraicGeometry.globalSectionsOver` composes them at all — but their
`Ring` instances, hence their `CategoryTheory.Preadditive` instances, are not the same *terms*,
and instance search does not unfold far enough to see it.  So Mathlib's additivity and exactness
instances for restriction of scalars, which are stated at the spelling of their own ring
arguments, do not fire at the spelling the composite forces.  They are therefore re-registered
here at that spelling, with no new content: additivity is `rfl`, as it is for
`AlgebraicGeometry.globalSectionsOver` itself, and the two exactness instances are
`StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits` and
`...restrictScalars_preservesFiniteColimits` read at the other spelling.  They are *not* local
instances: a file that composes `derivedGlobalSectionsOverEvaluationIso` with the clause of
Stacks 0D6H at `ε` needs them too, and the composition fails without them.

*The model of the derived category.* `attribute [local instance 10000] HasDerivedCategory.standard`
puts every derived category here at `CategoryTheory.HasDerivedCategory.standard`, which is the
model `StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalenceStandard.lean` and the
pseudo-coherence files use.  The priority is `10000` and not the default for the reason recorded
in that file: the import closure carries the *global* `HasDerivedCategory` instances of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean`, and a global instance beats a
default-priority local attribute.

## References

* [Stacks Project, Tag 0D6H](https://stacks.math.columbia.edu/tag/0D6H)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry

universe u

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- Restriction of scalars to the base ring `A` along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(X, 𝒪_X)`, read at
the `RingCat`-valued spelling of the section ring that the evaluation functor of the small
Zariski site lands in.  This is the second factor of `AlgebraicGeometry.globalSectionsOver`. -/
instance restrictScalarsAppTop_additive :
    (ModuleCat.restrictScalars.{u} (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom) :
        ModuleCat.{u} ↑(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))) ⥤
          ModuleCat.{u} A).Additive where
  map_add := rfl

/-- Restriction of scalars along the structure morphism preserves finite limits, at the spelling
of the section ring that the evaluation functor of the small Zariski site lands in. -/
instance restrictScalarsAppTop_preservesFiniteLimits :
    PreservesFiniteLimits
      (ModuleCat.restrictScalars.{u} (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom) :
        ModuleCat.{u} ↑(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))) ⥤ ModuleCat.{u} A) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteLimits _

/-- Restriction of scalars along the structure morphism preserves finite colimits, at the
spelling of the section ring that the evaluation functor of the small Zariski site lands in. -/
instance restrictScalarsAppTop_preservesFiniteColimits :
    PreservesFiniteColimits
      (ModuleCat.restrictScalars.{u} (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom) :
        ModuleCat.{u} ↑(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))) ⥤ ModuleCat.{u} A) :=
  StacksDraft.PseudoCoherence.restrictScalars_preservesFiniteColimits _

/-- **Derived sections at the final object of the small Zariski site are derived global
sections over the base ring.**  For a scheme `X` over a ring `A`, the unbounded right derived
functor of evaluation at `⊤` on the small Zariski site of `X`, followed by restriction of
scalars to `A`, is `A`-linear unbounded derived global sections `RΓ(X, -) : D(𝒪_X) ⥤ D(A)`:

`R(Γ(⊤, -)) ⋙ (-)|_A ≅ RΓ(X, -)`.

The underived identity is `rfl`: `AlgebraicGeometry.globalSectionsOver` is evaluation at `⊤`
followed by that restriction of scalars.  So the content is only that a total right derived
functor postcomposed with an exact functor derives the composite, which is
`Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso`; restriction
of scalars is exact. -/
def derivedGlobalSectionsOverEvaluationIso :
    Stacks.DerivedFunctor.totalRightDerived
        (SheafOfModules.evaluation.{u} X.ringCatSheaf (op (⊤ : X.Opens))) ⋙
        (ModuleCat.restrictScalars.{u}
            (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom) :
          ModuleCat.{u} ↑(X.ringCatSheaf.obj.obj (op (⊤ : X.Opens))) ⥤
            ModuleCat.{u} A).mapDerivedCategory ≅
      derivedGlobalSectionsOver f :=
  Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso _ _

end AlgebraicGeometry

end
