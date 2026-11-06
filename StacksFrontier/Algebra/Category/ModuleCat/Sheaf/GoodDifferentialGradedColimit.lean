module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedModule
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedFlatColimit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedForgetColimits
public import StacksFrontier.Algebra.Homology.AcyclicColimitCocone
public import StacksCore.Tactic.StacksAttribute

/-!
# Colimits of good differential graded modules

Let `(C, O)` be a ringed site and let `A` be a sheaf of differential graded `O`-algebras on it.
An arbitrary direct sum of good right differential graded `A`-modules is good, and a filtered
colimit of good right differential graded `A`-modules is good. Both are instances of one
statement: the conditions defining goodness pass to a colimit along any shape whose colimits of
sheaves of modules are exact.

K-flatness is the new content: `- ⊗_A N` lands in complexes of `O`-modules, and the statement
needed is that it commutes with the colimit *as a complex*. It does, degreewise, because
forgetting the differential of a right differential graded module is a left adjoint and because
degree `n` of the relative tensor product of graded modules commutes with colimits; a complex is
a colimit as soon as it is one in every degree. A colimit of acyclic complexes along a shape with
exact colimits is then acyclic.

## Main results

* `SheafOfModules.RelativeTensor.isColimit_dgTensorFunctor_mapCocone`: **`- ⊗_A N` carries a
  colimit cocone of right differential graded modules to a colimit cocone of complexes of
  `O`-modules.**
* `SheafOfModules.RelativeTensor.isKFlat_of_isColimit`: **a colimit of K-flat right differential
  graded modules is K-flat**, with
  `SheafOfModules.RelativeTensor.isKFlat_of_isColimitCofan` and
  `SheafOfModules.RelativeTensor.isKFlat_of_isColimit_isFiltered` for direct sums and filtered
  colimits.
* `SheafOfModules.DifferentialGradedModule.isGradedFlat_and_isKFlat_of_isColimit`: flatness of
  the underlying graded module and K-flatness pass together to a colimit.
* `SheafOfModules.DifferentialGradedModule.isGoodCocontinuousBaseChange_of_isColimitCofan` and
  `isGoodCocontinuousBaseChange_of_isColimit_isFiltered`: **an arbitrary direct sum of good
  right differential graded modules is good, and a filtered colimit of good right differential
  graded modules is good**, in the sense of
  `SheafOfModules.DifferentialGradedModule.IsGoodCocontinuousBaseChange`.

## Implementation notes

The flatness statements target `SheafOfModules.RelativeTensor.IsGradedFlat` and
`SheafOfModules.RelativeTensor.IsKFlat`, which are conditions (1) and (2) in the definition of a
good module and are shared verbatim by `SheafOfModules.DifferentialGradedModule.IsGood`,
`SheafOfModules.DifferentialGradedModule.IsGoodCocontinuousBaseChange` and
`SheafOfModules.IsGoodToposBaseChange`, so they serve all three.

Tag 0FSD at the definition of Tag 0FSA, `SheafOfModules.IsGoodToposBaseChange`, is
`SheafOfModules.isGoodToposBaseChange_of_isColimitCofan` and
`isGoodToposBaseChange_of_isColimit_isFiltered` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodDifferentialGradedToposDirectSum.lean`. The two
goodness statements of this file are the same two arguments at the auxiliary variant, for the
consumers stated against it.

The goodness statement targets `IsGoodCocontinuousBaseChange` and not `IsGood`: condition (3) of
`IsGood` quantifies over every pullback, including ones which do not commute with colimits, and
for such a pullback the pullback of a colimit is not a colimit, so there is nothing to transport
the flatness of the summands along. The whole point of
`IsGoodCocontinuousBaseChange` is to quantify condition (3) over the pullbacks that do commute
with colimits, which is exactly the hypothesis this argument consumes.

That hypothesis need not be assumed, though, and
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GoodDifferentialGradedSiteColimit.lean` does not
assume it: along a morphism of ringed *sites* the pullback is the left adjoint of the direct
image, so it preserves every colimit, and the two statements of this file hold there for a
goodness whose condition (3) ranges over all such base changes with no condition on the pullback.

The two goodness statements are specialisations of
`isGradedFlat_and_isKFlat_of_isColimit` to a discrete and to a filtered index category rather
than one statement for an arbitrary shape. Exactness of the colimits is needed at the second
ringed site of condition (3) as well as at the first, and that site is quantified over inside
the predicate, so the hypothesis cannot be imposed on it; for a discrete index category it is
AB4 and for a filtered one it is AB5, and both hold at every site.

The index category of the colimit lies in the module universe, and the module universe of the
second ringed site of condition (3) is the same as that of the first. Both are forced by
`SheafOfModules.RelativeTensor.preservesColimitsOfSize_gradedTensorDegree_of_sheafify`, which
is available for colimits of shapes small relative to the module universe and no larger: the
colimit at the second site is indexed by the same category as the colimit at the first, so that
category has to be small relative to the second module universe too.

## References

* [Stacks Project, Tag 0FSD](https://stacks.math.columbia.edu/tag/0FSD)
* [Stacks Project, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ)
* [Stacks Project, Tag 079B](https://stacks.math.columbia.edu/tag/079B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u v₁ u₁

namespace SheafOfModules

/-- Coproducts of sheaves of modules, indexed in the module universe. Instance search times out
looking for them through the `Discrete` shape, so they are taken from `HasColimitsOfSize`. -/
local instance (priority := high) hasColimitsOfShape_discrete_GoodDifferentialGradedColimit {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    (R : Sheaf J RingCat.{t}) (K : Type m) :
    HasColimitsOfShape (Discrete K) (SheafOfModules.{m} R) :=
  (inferInstance : HasColimitsOfSize.{m, m} (SheafOfModules.{m} R)).has_colimits_of_shape _

namespace RelativeTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

section

variable {D : Type m} [Category.{m} D]

/-- **The relative tensor product `- ⊗_A N` carries a colimit cocone of right differential
graded modules to a colimit cocone of complexes of `O`-modules.** A cocone of complexes is
colimiting as soon as it is in every degree, and in degree `n` the functor is the composite of
forgetting the differential, a left adjoint, with degree `n` of the relative tensor product of
graded modules. -/
@[stacks 0FSD "the relative tensor product with a fixed left differential graded module \
commutes, as a functor to complexes, with the colimits of right differential graded modules"]
noncomputable def isColimit_dgTensorFunctor_mapCocone
    (N : LeftDifferentialGradedModule.{t, m, m} A) {K : D ⥤ DifferentialGradedModule.{t, m, m} A}
    {c : Cocone K} (hc : IsColimit c) : IsColimit ((dgTensorFunctor N).mapCocone c) := by
  refine HomologicalComplex.isColimitOfEval _ _ fun n ↦ ?_
  have := (preservesColimitsOfSize_gradedTensorDegree_of_sheafify
    (gN N) n).preservesColimitsOfShape (J := D)
  exact isColimitOfPreserves (forgetToGradedModule A ⋙ gradedTensorDegree (gN N) n) hc

variable [HasColimitsOfShape D (SheafOfModules.{m} (toRingCat J Osharp))]
  [HasExactColimitsOfShape D (SheafOfModules.{m} (toRingCat J Osharp))]

/-- **A colimit of K-flat right differential graded modules is K-flat**, along any shape whose
colimits of sheaves of modules are exact. -/
@[stacks 0FSD "a colimit of K-flat right differential graded modules is K-flat, the K-flatness \
half of the lemma, for an index category whose colimits of sheaves of modules are exact"]
theorem isKFlat_of_isColimit {K : D ⥤ DifferentialGradedModule.{t, m, m} A} {c : Cocone K}
    (hc : IsColimit c) (hK : ∀ d : D, IsKFlat (K.obj d)) : IsKFlat c.pt := fun N hN ↦
  HomologicalComplex.acyclic_of_isColimit (isColimit_dgTensorFunctor_mapCocone N hc)
    fun d ↦ hK d N hN

end

/-- **An arbitrary direct sum of K-flat right differential graded modules is K-flat.** -/
@[stacks 0FSD "an arbitrary direct sum of K-flat right differential graded modules is K-flat, \
the K-flatness half of the direct sum clause"]
theorem isKFlat_of_isColimitCofan {ι : Type m} {P : ι → DifferentialGradedModule.{t, m, m} A}
    {c : Cofan P} (hc : IsColimit c) (hP : ∀ i, IsKFlat (P i)) : IsKFlat c.pt := by
  have := ab4OfSize.{t, m} (toRingCat J Osharp)
  exact isKFlat_of_isColimit hc fun d ↦ hP d.as

/-- **A filtered colimit of K-flat right differential graded modules is K-flat.** -/
@[stacks 0FSD "a filtered colimit of K-flat right differential graded modules is K-flat, the \
K-flatness half of the filtered colimit clause"]
theorem isKFlat_of_isColimit_isFiltered {D : Type m} [SmallCategory D] [IsFiltered D]
    {K : D ⥤ DifferentialGradedModule.{t, m, m} A} {c : Cocone K} (hc : IsColimit c)
    (hK : ∀ d : D, IsKFlat (K.obj d)) : IsKFlat c.pt :=
  isKFlat_of_isColimit hc hK

end RelativeTensor

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {A : DifferentialGradedAlgebra.{t, m} (toRingCat J Osharp)}

/-- Flatness of the underlying graded module and K-flatness pass together to a colimit of right
differential graded modules, along any shape whose colimits of sheaves of modules are exact.
This is the conjunction that appears both as conditions (1) and (2) of
`IsGoodCocontinuousBaseChange` and as its condition (3) after a base change. -/
@[stacks 0FSD "flatness of the underlying graded module and K-flatness pass to a colimit of \
right differential graded modules, for an index category whose colimits of sheaves of modules \
are exact"]
theorem isGradedFlat_and_isKFlat_of_isColimit {D : Type m} [Category.{m} D]
    [HasColimitsOfShape D (SheafOfModules.{m} (toRingCat J Osharp))]
    [HasExactColimitsOfShape D (SheafOfModules.{m} (toRingCat J Osharp))]
    {K : D ⥤ DifferentialGradedModule.{t, m, m} A} {c : Cocone K} (hc : IsColimit c)
    (hK : ∀ d : D, RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded (K.obj d)) ∧
      RelativeTensor.IsKFlat (K.obj d)) :
    RelativeTensor.IsGradedFlat (GradedModule.ofDifferentialGraded c.pt) ∧
      RelativeTensor.IsKFlat c.pt :=
  ⟨RelativeTensor.isGradedFlat_of_isColimit (K := K ⋙ forgetToGradedModule A)
      (c := (forgetToGradedModule A).mapCocone c)
      (isColimitOfPreserves (forgetToGradedModule A) hc) fun d ↦ (hK d).1,
    RelativeTensor.isKFlat_of_isColimit hc fun d ↦ (hK d).2⟩

/-- **An arbitrary direct sum of good right differential graded modules is good**, goodness
being taken in the sense of `IsGoodCocontinuousBaseChange`.

Conditions (1) and (2) for the direct sum are the colimit statements of the file, applied to the
coproduct cocone. For condition (3), the pullback commutes with the colimit, so the pullbacks of
the summands form a coproduct cocone with the pullback of the direct sum as its point; the
summands' own condition (3) says that those pullbacks are flat and K-flat, and the colimit
statements apply again, at the second ringed site.

Goodness is the auxiliary `IsGoodCocontinuousBaseChange`, so this is not Tag 0FSD; that tag is
registered on the same statement at `SheafOfModules.IsGoodToposBaseChange`, the definition of
Tag 0FSA, in `GoodDifferentialGradedToposDirectSum.lean`. -/
theorem isGoodCocontinuousBaseChange_of_isColimitCofan {ι : Type m}
    {P : ι → DifferentialGradedModule.{t, m, m} A} {c : Cofan P} (hc : IsColimit c)
    (hP : ∀ i, IsGoodCocontinuousBaseChange.{t, m, v, u, m, v₁, u₁} (P i)) :
    IsGoodCocontinuousBaseChange.{t, m, v, u, m, v₁, u₁} c.pt := by
  have := ab4OfSize.{t, m} (toRingCat J Osharp)
  have h₁ := isGradedFlat_and_isKFlat_of_isColimit hc
    fun i ↦ ⟨(hP i.as).isGradedFlat, (hP i.as).isKFlat⟩
  refine ⟨h₁.1, h₁.2, ?_⟩
  intro C₁ _ J₁ _ _ _ Osharp₁ u σ A₁ φ PD hPD
  have := ab4OfSize.{t, m} (toRingCat J₁ Osharp₁)
  have := hPD.preservesColimitsOfShape (J := Discrete ι)
  exact isGradedFlat_and_isKFlat_of_isColimit (c := PD.functor.mapCocone c)
    (isColimitOfPreserves PD.functor hc) fun i ↦ (hP i.as).baseChange u σ A₁ φ PD hPD

/-- **A filtered colimit of good right differential graded modules is good**, goodness being
taken in the sense of `IsGoodCocontinuousBaseChange`. The argument is that of
`isGoodCocontinuousBaseChange_of_isColimitCofan`, with AB5 in place of AB4. Goodness is the
auxiliary `IsGoodCocontinuousBaseChange`, so this is not Tag 0FSD; that tag is registered on the
same statement at `SheafOfModules.IsGoodToposBaseChange`, the definition of Tag 0FSA, in
`GoodDifferentialGradedToposDirectSum.lean`. -/
theorem isGoodCocontinuousBaseChange_of_isColimit_isFiltered {D : Type m} [SmallCategory D]
    [IsFiltered D] {K : D ⥤ DifferentialGradedModule.{t, m, m} A} {c : Cocone K}
    (hc : IsColimit c)
    (hK : ∀ d : D, IsGoodCocontinuousBaseChange.{t, m, v, u, m, v₁, u₁} (K.obj d)) :
    IsGoodCocontinuousBaseChange.{t, m, v, u, m, v₁, u₁} c.pt := by
  have h₁ := isGradedFlat_and_isKFlat_of_isColimit hc
    fun d ↦ ⟨(hK d).isGradedFlat, (hK d).isKFlat⟩
  refine ⟨h₁.1, h₁.2, ?_⟩
  intro C₁ _ J₁ _ _ _ Osharp₁ u σ A₁ φ PD hPD
  have := hPD.preservesColimitsOfShape (J := D)
  exact isGradedFlat_and_isKFlat_of_isColimit (c := PD.functor.mapCocone c)
    (isColimitOfPreserves PD.functor hc) fun d ↦ (hK d).baseChange u σ A₁ φ PD hPD

end DifferentialGradedModule

end SheafOfModules
