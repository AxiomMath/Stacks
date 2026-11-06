module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.LocalizationComparison

/-!
# Collapsing the derived functor of a composite along an exact functor with acyclic values

Let `F : 𝒜 ⥤ ℬ` be an exact additive functor and `G : ℬ ⥤ 𝒞` an additive functor. The right
derived functors of the composite split,

`Rⁿ(G ∘ F) ≅ F ⋙ Rⁿ G`,

as soon as `F` carries injective objects of `𝒜` to objects that are *right acyclic* for `G`.
That hypothesis is strictly weaker than asking `F` to preserve injective objects, which is what
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` assumes: an injective object is
right acyclic for every additive functor, so preservation of injectives implies acyclicity of
the values, and the converse fails. The weaker hypothesis is the one available for the
pushforward of sheaves of modules, where [Stacks, Tag 01EX] part (2) gives acyclicity of `f_*I`
for the sections functor while `f_*` genuinely does not preserve injectives.

## Main results

* `Stacks.Cohomology.AcyclicCollapse.isIso_derivedComposition`: the canonical comparison
  `R(G ∘ F) ⟶ RG ∘ RF` of [Stacks, Tag 05T2] on the bounded below derived categories is
  invertible under the acyclicity hypothesis. This is [Stacks, Tag 015M] read off its criterion.
* `Stacks.Cohomology.AcyclicCollapse.rightDerivedCompIsoOfAcyclic`: the resulting splitting
  `(F ⋙ G).rightDerived n ≅ F ⋙ G.rightDerived n` for Mathlib's `ℕ`-indexed right derived
  functors.

## Implementation notes

Exactness of `F` is used exactly once, to identify `RF` with `F`: the unit
`F.rightDerivedFunctorPlusUnith` of the bounded below right derived functor is invertible for an
exact functor (`Stacks.Cohomology.HigherDirectImage.isIso_rightDerivedFunctorPlusUnit`), so
`RF` carries an object placed in degree zero to `F` of it placed in degree zero. Without
exactness the same acyclicity hypothesis still gives the invertibility of the comparison
`R(G ∘ F) ⟶ RG ∘ RF`, which is `isIso_derivedComposition` below; it is the degreewise splitting
that needs `RF = F`.

The passage between the derived-category convention `rightDerivedPlus` and the
injective-resolution convention `rightDerived` is
`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard`.

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.AcyclicCollapse

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A B D : Type*} [Category* A] [Category* B] [Category* D]
  [Abelian A] [Abelian B] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B]
  (F : A ⥤ B) (G : B ⥤ D) [F.Additive] [G.Additive]

/-- **The canonical comparison is invertible when `F` sends injectives to `G`-acyclic objects.**
This is the criterion of [Stacks, Tag 015M], `Functor.isIso_iff_rightAcyclic_obj_injective`,
applied to the comparison pinned by `CategoryTheory.Functor.rightComparisonUnit`. No exactness
of `F` is needed. -/
theorem isIso_derivedComposition
    (hac : ∀ I : A, Injective I → G.rightAcyclic (F.obj I)) :
    IsIso (Functor.rightDerivedFunctorPlusComp F G) :=
  (Functor.isIso_iff_rightAcyclic_obj_injective _ _ (Functor.rightDerivedFunctorPlusComp F G)
    (Functor.rightDerivedFunctorPlusComp_fac F G)).2 hac

/-- **The bounded below right derived functor of an exact `F` carries an object placed in degree
zero to `F` of it placed in degree zero.** -/
noncomputable def singleFunctorIso [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    DerivedCategory.Plus.singleFunctor A 0 ⋙ F.rightDerivedFunctorPlus ≅
      F ⋙ DerivedCategory.Plus.singleFunctor B 0 :=
  have : F.PreservesHomology := Functor.preservesHomologyOfExact F
  have : IsIso F.rightDerivedFunctorPlusUnith :=
    Stacks.Cohomology.HigherDirectImage.isIso_rightDerivedFunctorPlusUnit F
  Functor.isoWhiskerRight (Functor.singleFunctorPlusIsoCompQh 0) F.rightDerivedFunctorPlus ≪≫
    Functor.isoWhiskerLeft (HomotopyCategory.Plus.singleFunctor A 0)
      (asIso F.rightDerivedFunctorPlusUnith).symm ≪≫
    Functor.mapSingleFunctorCompQhIso F

/-- **The derived functor of a composite splits along an exact functor with `G`-acyclic values
on injectives.** For `F` exact and additive carrying every injective object to an object right
acyclic for the additive `G`, the `n`-th right derived functor of `G ∘ F` is `F` followed by the
`n`-th right derived functor of `G`. -/
noncomputable def rightDerivedCompIsoOfAcyclic
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (hac : ∀ I : A, Injective I → G.rightAcyclic (F.obj I)) (n : ℕ) :
    (F ⋙ G).rightDerived n ≅ F ⋙ G.rightDerived n :=
  have _ : IsIso (Functor.rightDerivedFunctorPlusComp F G) := isIso_derivedComposition F G hac
  (Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard (F ⋙ G) n).symm ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor A 0)
      (Functor.isoWhiskerRight (asIso (Functor.rightDerivedFunctorPlusComp F G))
        (DerivedCategory.Plus.homologyFunctor D (n : ℤ))) ≪≫
    Functor.isoWhiskerRight (singleFunctorIso F)
      (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor D (n : ℤ)) ≪≫
    Functor.isoWhiskerLeft F
      (Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard G n)

end Stacks.Cohomology.AcyclicCollapse

end
