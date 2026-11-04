module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedLowerShriekUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatFppfDerivedConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleDerivedLowerShriek
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteGlobalCohomologyAtlas
import StacksCore.Tactic.StacksAttribute

/-!
# `Lg_! ℤ = ℤ` for the lisse-étale and the flat-fppf site

Let `𝒳` be an algebraic stack. **Stacks 0H0Z** asserts `Lg_! ℤ = ℤ` both for the derived lower
shriek `Lg_! : D(𝒳_{lisse,étale}) ⟶ D(𝒳_{étale})` of **Stacks 07AS** part (1) and for
`Lg_! : D(𝒳_{flat,fppf}) ⟶ D(𝒳_{fppf})` of part (3). Both are proved here, for every algebraic
stack and with nothing assumed.

The statement is proved in the form that pins down the map: the counit of the derived adjunction
`Lg_! ⊣ g⁻¹` is invertible at the constant sheaf `ℤ` in degree zero. Restriction carries the
constant sheaf to the constant sheaf, so the source of that counit is `Lg_!` of the constant sheaf
`ℤ` of the subsite, and the counit is the canonical comparison `Lg_! ℤ ⟶ ℤ`. The isomorphisms
`Lg_!(ℤ[0]) ≅ ℤ[0]` themselves are recorded as
`AlgebraicGeometry.Stack.LisseEtale.derivedAbelianLowerShriekConstantSheafIso` and
`AlgebraicGeometry.Stack.FlatFppf.derivedAbelianLowerShriekConstantSheafIso`.

## The proof

The site-independent argument is
`Stacks.Cohomology.DerivedLowerShriek.isIso_counit_app_single_constantSheaf`: for a left adjoint
`L` of an exact restriction `R` on unbounded derived categories with invertible unit, the counit is
invertible at `ℤ[0]` as soon as `R` identifies cohomology in every degree. Its inputs are:

* the derived adjunction and the invertibility of its unit, which are Stacks 07AS (1) and (3)
  with nothing assumed — `AlgebraicGeometry.Stack.LisseEtale.derivedAbelianLowerShriekAdjunction`,
  `AlgebraicGeometry.Stack.LisseEtale.isIso_derivedAbelianLowerShriekAdjunction_unit`,
  `AlgebraicGeometry.Stack.FlatFppf.derivedAbelianLowerShriekFunctorAdjunction` and
  `AlgebraicGeometry.Stack.FlatFppf.isIso_derivedAbelianLowerShriekAdjunction_unit` at the proved
  acyclicity statement `AlgebraicGeometry.Stack.FlatFppf.abelianLowerShriekAcyclic`;
* the cohomology comparison of Stacks 07AK in every degree, with both of its hypotheses
  discharged: `AlgebraicGeometry.Stack.LisseEtale.globalCohomologyIso` and
  `AlgebraicGeometry.Stack.FlatFppf.globalCohomologyIso`.

The cohomology comparison is where the atlas enters, and so this replaces the source's reduction
along a presentation (Stacks 06XD, 06XH and 07AV) by the dévissage along Čech resolutions that
proves Stacks 07AK in `SubsiteCohomologyAtlas.lean`. In particular neither the comparison
`g_!ℤ = ℤ` of ordinary sheaves nor the global acyclicity of restricted injectives is a hypothesis
here: the two data `hunit` and `hacyclic` of
`AlgebraicGeometry.Stack.FlatFppf.isIso_derivedAbelianLowerShriekAdjunction_counit_constantSheaf`
are both proved, as the two conclusions of the cover descent at the final presheaf.

## Main results

* `LisseEtale.isIso_derivedAbelianLowerShriekAdjunction_counit_constantSheaf`:
  `Lg_! ℤ = ℤ` for Stacks 07AS (1), as invertibility of the counit.
* `FlatFppf.isIso_derivedAbelianLowerShriekFunctorAdjunction_counit_constantSheaf`:
  `Lg_! ℤ = ℤ` for Stacks 07AS (3), as invertibility of the counit.
* `AlgebraicGeometry.Stack.LisseEtale.derivedAbelianLowerShriekConstantSheafIso` and
  `AlgebraicGeometry.Stack.FlatFppf.derivedAbelianLowerShriekConstantSheafIso`: the isomorphisms
  `Lg_!(ℤ[0]) ≅ ℤ[0]`.
* `AlgebraicGeometry.Stack.derivedAbelianLowerShriek_constantSheaf`: **Stacks 0H0Z**, both cases
  together.

## References

* [Stacks Project, Tag 0H0Z](https://stacks.math.columbia.edu/tag/0H0Z)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 07AK](https://stacks.math.columbia.edu/tag/07AK)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)

attribute [local instance] HasDerivedCategory.standard

/-- An exact functor between abelian categories is additive and preserves finite limits and
colimits. -/
private theorem additive_and_preservesFinite_of_exact {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] {F : C ⥤ D} (hF : exactFunctor C D F) :
    F.Additive ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
  ⟨exactFunctor_le_additiveFunctor _ _ _ hF, ((exactFunctor_iff _).mp hF).1,
    ((exactFunctor_iff _).mp hF).2⟩

namespace FlatFppf

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- **`Lg_! ℤ = ℤ` for the `Lg_!` of Stacks 07AS (3), for every algebraic stack.** The counit of
the derived adjunction `Lg_! ⊣ g⁻¹` of the flat-fppf site is invertible at the constant sheaf `ℤ`
of `𝒳_{fppf}` in degree zero. Its source is `Lg_!` of `g⁻¹ℤ`, which is the constant sheaf of the
flat-fppf site by `AlgebraicGeometry.Stack.FlatFppf.restriction_constantSheafIso`, so this says
that the canonical comparison `Lg_! ℤ ⟶ ℤ` is an isomorphism.

This is
`AlgebraicGeometry.Stack.FlatFppf.isIso_derivedAbelianLowerShriekAdjunction_counit_constantSheaf`
with both of its data proved, through the unconditional cohomology comparison
`AlgebraicGeometry.Stack.FlatFppf.globalCohomologyIso`. -/
theorem isIso_derivedAbelianLowerShriekFunctorAdjunction_counit_constantSheaf :
    IsIso ((derivedAbelianLowerShriekFunctorAdjunction B S hS 𝒳).counit.app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ))))) := by
  obtain ⟨_, _, _⟩ := additive_and_preservesFinite_of_exact (abelianRestriction_exact B S hS 𝒳)
  exact Stacks.Cohomology.DerivedLowerShriek.isIso_counit_app_single_constantSheaf
    (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳)
    (abelianInverseImage B S hS 𝒳 flatClosure) _
    (derivedAbelianLowerShriekFunctorAdjunction B S hS 𝒳)
    (isIso_derivedAbelianLowerShriekAdjunction_unit B S hS 𝒳
      (abelianLowerShriekAcyclic B S hS 𝒳))
    (fun n => globalCohomologyIso B S hS 𝒳 n)

/-- **`Lg_! ℤ ≅ ℤ` for the `Lg_!` of Stacks 07AS (3)**: the derived lower shriek of the constant
sheaf `ℤ` of the flat-fppf site, in degree zero, is the constant sheaf `ℤ` of `𝒳_{fppf}` in degree
zero. The isomorphism is the counit of `Lg_! ⊣ g⁻¹` at `ℤ[0]`, invertible by
`FlatFppf.isIso_derivedAbelianLowerShriekFunctorAdjunction_counit_constantSheaf`,
read through `g⁻¹ℤ ≅ ℤ`. -/
def derivedAbelianLowerShriekConstantSheafIso :
    (derivedAbelianLowerShriekFunctor B S hS 𝒳).obj ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  haveI := isIso_derivedAbelianLowerShriekFunctorAdjunction_counit_constantSheaf B S hS 𝒳
  (derivedAbelianLowerShriekFunctor B S hS 𝒳).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso (restriction_constantSheafIso B S hS 𝒳) ≪≫
        (((Stacks.Cohomology.DerivedLowerShriek.abelianRestriction.{u + 1}
          (inclusionTopology B S hS 𝒳) (fppfTopology B S hS 𝒳)
          (objectProperty B S hS 𝒳).ι).mapDerivedCategorySingleFunctor 0).app
          ((constantSheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).symm) ≪≫
    asIso ((derivedAbelianLowerShriekFunctorAdjunction B S hS 𝒳).counit.app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))))

end FlatFppf

namespace LisseEtale

attribute [local instance] isContinuous_inclusion' isCocontinuous_inclusion'

/-- **`Lg_! ℤ = ℤ` for the `Lg_!` of Stacks 07AS (1), for every algebraic stack.** The counit of
the derived adjunction `Lg_! ⊣ g⁻¹` of the lisse-étale site is invertible at the constant sheaf
`ℤ` of `𝒳_{étale}` in degree zero. Its source is `Lg_!` of `g⁻¹ℤ`, which is the constant sheaf of
the lisse-étale site by `AlgebraicGeometry.Stack.LisseEtale.restriction_constantSheafIso`, so
this says that the canonical comparison `Lg_! ℤ ⟶ ℤ` is an isomorphism.

The inputs are the derived adjunction of Stacks 07AS (1) with its invertible unit, and the
unconditional cohomology comparison
`AlgebraicGeometry.Stack.LisseEtale.globalCohomologyIso` of Stacks 07AK. -/
theorem isIso_derivedAbelianLowerShriekAdjunction_counit_constantSheaf :
    IsIso ((derivedAbelianLowerShriekAdjunction.{u, w} B S hS 𝒳).counit.app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
            AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))))) := by
  obtain ⟨_, _, _⟩ :=
    additive_and_preservesFinite_of_exact (abelianRestriction_exact.{u, w} B S hS 𝒳)
  exact Stacks.Cohomology.DerivedLowerShriek.isIso_counit_app_single_constantSheaf
    (inclusionTopology.{u, w} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    (abelianInverseImage.{u, w} B S hS 𝒳 (closedUnderSmoothMorphisms.{u, w} B S hS 𝒳)) _
    (derivedAbelianLowerShriekAdjunction.{u, w} B S hS 𝒳)
    (isIso_derivedAbelianLowerShriekAdjunction_unit.{u, w} B S hS 𝒳)
    (fun n => globalCohomologyIso B S hS 𝒳 n)

/-- **Restriction to the lisse-étale site carries the constant sheaf `ℤ` to the constant sheaf
`ℤ`**: the instance of `Stacks.Cohomology.DerivedLowerShriek.restriction_constantSheafIso` at the
inclusion of the smooth objects. It identifies the source of the counit at `ℤ_𝒳[0]` with
`Lg_! ℤ_{𝒳_{lisse,étale}}`. -/
def restriction_constantSheafIso :
    (constantSheaf (inclusionTopology.{u, w} B S hS 𝒳) AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ≅
      (subsiteRestriction B S hS 𝒳.val.val.p (etaleTopology B)
          (smoothObject.{u, w} B S hS 𝒳)).obj
        ((constantSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
          AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  Stacks.Cohomology.DerivedLowerShriek.restriction_constantSheafIso
    (smoothObject.{u, w} B S hS 𝒳).ι (inclusionTopology.{u, w} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
    AddCommGrpCat.{u + 1} (AddCommGrpCat.of (ULift.{u + 1} ℤ))

/-- **`Lg_! ℤ ≅ ℤ` for the `Lg_!` of Stacks 07AS (1)**: the derived lower shriek of the constant
sheaf `ℤ` of the lisse-étale site, in degree zero, is the constant sheaf `ℤ` of `𝒳_{étale}` in
degree zero. The isomorphism is the counit of `Lg_! ⊣ g⁻¹` at `ℤ[0]`, invertible by
`LisseEtale.isIso_derivedAbelianLowerShriekAdjunction_counit_constantSheaf`,
read through `g⁻¹ℤ ≅ ℤ`. -/
def derivedAbelianLowerShriekConstantSheafIso :
    (derivedAbelianLowerShriek.{u, w} B S hS 𝒳).obj ((DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (inclusionTopology.{u, w} B S hS 𝒳) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
          AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ))) :=
  haveI := isIso_derivedAbelianLowerShriekAdjunction_counit_constantSheaf.{u, w} B S hS 𝒳
  (derivedAbelianLowerShriek.{u, w} B S hS 𝒳).mapIso
      ((DerivedCategory.singleFunctor _ 0).mapIso (restriction_constantSheafIso B S hS 𝒳) ≪≫
        (((Stacks.Cohomology.DerivedLowerShriek.abelianRestriction.{u + 1}
          (inclusionTopology.{u, w} B S hS 𝒳)
          (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
          (smoothObject.{u, w} B S hS 𝒳).ι).mapDerivedCategorySingleFunctor 0).app
          ((constantSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
            AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).symm) ≪≫
    asIso ((derivedAbelianLowerShriekAdjunction.{u, w} B S hS 𝒳).counit.app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
            AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))))

end LisseEtale

/-- **Stacks 0H0Z.** Let `𝒳` be an algebraic stack. Then `Lg_! ℤ = ℤ`, both for the `Lg_!` of
Stacks 07AS part (1) — `D(𝒳_{lisse,étale}) ⟶ D(𝒳_{étale})` — and for the `Lg_!` of part (3) —
`D(𝒳_{flat,fppf}) ⟶ D(𝒳_{fppf})`.

For each of the two sites the statement has two clauses: the derived lower shriek of the constant
sheaf `ℤ` of the subsite in degree zero is isomorphic to the constant sheaf `ℤ` of `𝒳` in degree
zero, and the canonical map realizing this — the counit of `Lg_! ⊣ g⁻¹` at `ℤ[0]`, whose source is
`Lg_!(g⁻¹ℤ) = Lg_! ℤ` — is an isomorphism. Nothing is assumed beyond `𝒳` being algebraic. -/
@[stacks 0H0Z "both cases of the statement, for every algebraic stack and with nothing assumed: \
the `Lg_!` of 07AS part (1) (lisse-étale) and of 07AS part (3) (flat-fppf). For each, the first \
clause is `Lg_!(ℤ[0]) ≅ ℤ[0]` and the second is invertibility of the canonical map, the counit of \
`Lg_! ⊣ g⁻¹` at `ℤ[0]`. Both `Lg_!` are the unconditional ones of 07AS (1) and (3); the \
cohomology comparison of 07AK that the proof runs on is the unconditional \
`AlgebraicGeometry.Stack.LisseEtale.globalCohomologyIso` resp. \
`AlgebraicGeometry.Stack.FlatFppf.globalCohomologyIso`, so neither `g_!ℤ = ℤ` nor the \
acyclicity of 0D6X is a hypothesis"]
theorem derivedAbelianLowerShriek_constantSheaf :
    (Nonempty ((LisseEtale.derivedAbelianLowerShriek.{u, w} B S hS 𝒳).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (LisseEtale.inclusionTopology.{u, w} B S hS 𝒳)
            AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
          AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) ∧
      IsIso ((LisseEtale.derivedAbelianLowerShriekAdjunction.{u, w} B S hS 𝒳).counit.app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))
            AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))))) ∧
    (Nonempty ((FlatFppf.derivedAbelianLowerShriekFunctor B S hS 𝒳).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (FlatFppf.inclusionTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) ≅
      (DerivedCategory.singleFunctor _ 0).obj
        ((constantSheaf (FlatFppf.fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).obj
          (AddCommGrpCat.of (ULift.{u + 1} ℤ)))) ∧
      IsIso ((FlatFppf.derivedAbelianLowerShriekFunctorAdjunction B S hS 𝒳).counit.app
        ((DerivedCategory.singleFunctor _ 0).obj
          ((constantSheaf (FlatFppf.fppfTopology B S hS 𝒳) AddCommGrpCat.{u + 1}).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))))) :=
  ⟨⟨⟨LisseEtale.derivedAbelianLowerShriekConstantSheafIso B S hS 𝒳⟩,
      LisseEtale.isIso_derivedAbelianLowerShriekAdjunction_counit_constantSheaf B S hS 𝒳⟩,
    ⟨⟨FlatFppf.derivedAbelianLowerShriekConstantSheafIso B S hS 𝒳⟩,
      FlatFppf.isIso_derivedAbelianLowerShriekFunctorAdjunction_counit_constantSheaf B S hS 𝒳⟩⟩

end AlgebraicGeometry.Stack

end
