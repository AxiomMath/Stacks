module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelativeTensorBifunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorRightPreColimits
public import StacksFrontier.CategoryTheory.Limits.FunctorCategory.ShortExactColimit
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksCore.Tactic.StacksAttribute

/-!
# Colimits of flat graded modules

Let `O` be a sheaf of commutative rings on a site and let `A` be a sheaf of graded `O`-algebras.
A right graded `A`-module `P` is flat when `N ↦ P ⊗_A N` carries short exact sequences of left
graded `A`-modules to short exact sequences in each degree. This file shows that flatness passes
to a colimit of right graded modules, along any shape whose colimits of sheaves of modules are
exact, and specialises this to arbitrary direct sums and to filtered colimits.

The two ingredients are already available: degree `n` of `- ⊗_A N` commutes with the colimits of
right graded modules, and tensoring with a homomorphism of left graded modules is natural in the
right graded module. The second makes the three colimits the three terms of one short complex of
functors on the index category, and exactness of the colimit then applies.

## Main results

* `SheafOfModules.ab4OfSize`: **arbitrary direct sums of sheaves of modules are exact.**
* `SheafOfModules.RelativeTensor.isGradedFlat_of_isColimit`: **a colimit of flat right graded
  modules is flat**, along a shape whose colimits of sheaves of modules are exact.
* `SheafOfModules.RelativeTensor.isGradedFlat_of_isColimitCofan` and
  `SheafOfModules.RelativeTensor.isGradedFlat_of_isColimit_isFiltered`: **an arbitrary direct
  sum of flat right graded modules is flat**, and **a filtered colimit of flat right graded
  modules is flat**.

## Implementation notes

The statements are about `SheafOfModules.RelativeTensor.IsGradedFlat`, which is condition (1) in
the definition of a good differential graded module and is common to
`SheafOfModules.DifferentialGradedModule.IsGood` and to
`SheafOfModules.DifferentialGradedModule.IsGoodCocontinuousBaseChange`; they therefore serve
both predicates.

Exactness of the colimits is a hypothesis on the index category rather than derived from AB4 or
AB5 inside the proof, so that the general statement covers both specialisations. The direct-sum
case is AB4 for sheaves of modules, which follows from AB5 because the category has finite
biproducts and finite limits; the filtered case is AB5 itself.

The index category lies in the module universe. This is forced by the colimit-preservation
statement for degree `n` of the relative tensor product, which is proved at that size and no
larger.

## References

* [Stacks Project, Tag 0FSD](https://stacks.math.columbia.edu/tag/0FSD)
* [Stacks Project, Tag 0FR2](https://stacks.math.columbia.edu/tag/0FR2)
* [Stacks Project, Tag 079B](https://stacks.math.columbia.edu/tag/079B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t m v u

namespace SheafOfModules

/-- Coproducts of sheaves of modules, indexed in the module universe. Instance search times out
looking for them through the `Discrete` shape, so they are taken from `HasColimitsOfSize`. -/
local instance (priority := high) hasColimitsOfShape_discrete_GradedFlatColimit {C : Type u}
    [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    (R : Sheaf J RingCat.{t}) (K : Type m) :
    HasColimitsOfShape (Discrete K) (SheafOfModules.{m} R) :=
  (inferInstance : HasColimitsOfSize.{m, m} (SheafOfModules.{m} R)).has_colimits_of_shape _

/-- **Arbitrary direct sums of sheaves of modules are exact.** Sheaves of modules have finite
biproducts and finite limits, so AB4 follows from AB5. -/
theorem ab4OfSize {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    (R : Sheaf J RingCat.{t}) : AB4OfSize.{m} (SheafOfModules.{m} R) := by
  have : HasFilteredColimitsOfSize.{m, m} (SheafOfModules.{m} R) :=
    ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
  have : HasFiniteBiproducts (SheafOfModules.{m} R) := HasFiniteBiproducts.of_hasFiniteProducts
  exact AB4.of_AB5 _

namespace RelativeTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{m}] [HasSheafify J AddCommGrpCat.{m}]
  {A : GradedAlgebra.{t, m} (toRingCat J Osharp)}

section

variable {D : Type m} [Category.{m} D]
  [HasColimitsOfShape D (SheafOfModules.{m} (toRingCat J Osharp))]
  [HasExactColimitsOfShape D (SheafOfModules.{m} (toRingCat J Osharp))]

/-- **A colimit of flat right graded modules is flat**, along any shape whose colimits of
sheaves of modules are exact. -/
@[stacks 0FSD "a colimit of flat right graded modules is flat, the graded-flatness half of the \
lemma, for an index category whose colimits of sheaves of modules are exact"]
theorem isGradedFlat_of_isColimit {K : D ⥤ GradedModule.{t, m, m} A} {c : Cocone K}
    (hc : IsColimit c) (hK : ∀ d : D, IsGradedFlat (K.obj d)) : IsGradedFlat c.pt := by
  intro N₁ N₂ N₃ u w huw hN n
  have key : ∀ d : D, ∃ h : gradedTensorMap (K.obj d) u n ≫ gradedTensorMap (K.obj d) w n = 0,
      (ShortComplex.mk (gradedTensorMap (K.obj d) u n)
        (gradedTensorMap (K.obj d) w n) h).ShortExact :=
    fun d ↦ hK d N₁ N₂ N₃ u w huw hN n
  have hzero : ∀ d : D, gradedTensorMap (K.obj d) u n ≫ gradedTensorMap (K.obj d) w n = 0 :=
    fun d ↦ (key d).elim fun h _ ↦ h
  let S : ShortComplex (D ⥤ SheafOfModules.{m} (toRingCat J Osharp)) :=
    ShortComplex.mk (Functor.whiskerLeft K (gradedTensorDegreeNatTrans u n))
      (Functor.whiskerLeft K (gradedTensorDegreeNatTrans w n)) (NatTrans.ext (funext hzero))
  have hSE : ∀ d : D,
      (S.map ((CategoryTheory.evaluation D
        (SheafOfModules.{m} (toRingCat J Osharp))).obj d)).ShortExact :=
    fun d ↦ (key d).elim fun _ h ↦ h
  have hpres : ∀ N : LeftGradedModule.{t, m, m} A,
      PreservesColimitsOfShape D (gradedTensorDegree N n) := fun N ↦
    (preservesColimitsOfSize_gradedTensorDegree_of_sheafify N n).preservesColimitsOfShape
  let c₁ := (gradedTensorDegree N₁ n).mapCocone c
  let c₂ := (gradedTensorDegree N₂ n).mapCocone c
  let c₃ := (gradedTensorDegree N₃ n).mapCocone c
  have hc₁ : IsColimit c₁ := have := hpres N₁; isColimitOfPreserves _ hc
  have hc₂ : IsColimit c₂ := have := hpres N₂; isColimitOfPreserves _ hc
  have hc₃ : IsColimit c₃ := have := hpres N₃; isColimitOfPreserves _ hc
  have hu : ∀ d : D, c₁.ι.app d ≫ gradedTensorMap c.pt u n =
      S.f.app d ≫ c₂.ι.app d := fun d ↦
    gradedTensorMapRight_gradedTensorMap (c.ι.app d) u n
  have hw : ∀ d : D, c₂.ι.app d ≫ gradedTensorMap c.pt w n =
      S.g.app d ≫ c₃.ι.app d := fun d ↦
    gradedTensorMapRight_gradedTensorMap (c.ι.app d) w n
  exact ⟨(colim.mapShortComplex S hc₁ c₂ c₃ (gradedTensorMap c.pt u n)
      (gradedTensorMap c.pt w n) hu hw).zero,
    colim.shortExact_mapShortComplex hSE hc₁ hc₂ hc₃ _ _ hu hw⟩

end

/-- **An arbitrary direct sum of flat right graded modules is flat.** -/
@[stacks 0FSD "an arbitrary direct sum of flat right graded modules is flat, the \
graded-flatness half of the direct sum clause"]
theorem isGradedFlat_of_isColimitCofan {ι : Type m} {P : ι → GradedModule.{t, m, m} A}
    {c : Cofan P} (hc : IsColimit c) (hP : ∀ i, IsGradedFlat (P i)) : IsGradedFlat c.pt := by
  have := ab4OfSize.{t, m} (toRingCat J Osharp)
  exact isGradedFlat_of_isColimit hc fun d ↦ hP d.as

/-- **A filtered colimit of flat right graded modules is flat.** -/
@[stacks 0FSD "a filtered colimit of flat right graded modules is flat, the graded-flatness \
half of the filtered colimit clause"]
theorem isGradedFlat_of_isColimit_isFiltered {D : Type m} [SmallCategory D] [IsFiltered D]
    {K : D ⥤ GradedModule.{t, m, m} A} {c : Cocone K} (hc : IsColimit c)
    (hK : ∀ d : D, IsGradedFlat (K.obj d)) : IsGradedFlat c.pt :=
  isGradedFlat_of_isColimit hc hK

end RelativeTensor

end SheafOfModules
