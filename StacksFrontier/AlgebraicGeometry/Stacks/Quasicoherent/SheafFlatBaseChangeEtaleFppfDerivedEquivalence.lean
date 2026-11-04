module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.KernelColocalizationQuotientAlongExactFunctor
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.EtaleFppfDerivedEquivalenceOfAffineVanishing
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticSemiorthogonalDecompositionOfClass
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeFppfWeakSerreAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeWeakSerreEtaleModules

/-!
# Stacks 07B8: `D_QCoh(𝒪_𝒳)` computed on the étale site

Let `𝒳` be an algebraic stack and abbreviate `𝒫_𝒳 = Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)`, where
`LQCoh^fbc(𝒪_𝒳)` is the class of modules which are locally quasi-coherent (**Stacks 06WJ**) and
have the flat base change property of **Stacks 0762**, read with the pullback of sheaves of
Stacks 06WC. The comparison morphism `ε : 𝒳_fppf ⟶ 𝒳_étale` induces a commutative diagram

```
D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⟶ D_{LQCoh^fbc}(𝒪_𝒳) ⟶ D(𝒪_𝒳)
          ↑ ε^*                          ↑ ε^*            ↑ ε^*
 D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳)        ⟶ D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) ⟶ D(𝒳_étale, 𝒪_𝒳)
```

whose left two vertical arrows are equivalences of triangulated categories, and hence an
equivalence

`D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) / D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳) ≌ D_QCoh(𝒪_𝒳)`.

This is **Stacks 07B8**, proved here with no hypothesis for the classes of the source. The
right-hand vertical arrow is `AlgebraicGeometry.Stack.epsilonPullbackDerived`.

## The argument

As in the source, the middle vertical arrow is an equivalence by **Stacks 07A8**
(`AlgebraicGeometry.Stack.isEquivalence_epsilonPullbackDerivedLift_of_vanishing`) with
`𝒜 = LQCoh^fbc(𝒪_𝒳)` and `ℬ` the objects over affine schemes. Its conditions (1) and (2):
`LQCoh^fbc(𝒪_𝒳)` is a weak Serre subcategory of `Mod(𝒪_𝒳)` (**Stacks 0771** (2),
`AlgebraicGeometry.Stack.isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppfModules`) and
its image under `ε_*` is `LQCoh^fbc(𝒳_étale, 𝒪_𝒳)`, because a module of the latter is a sheaf for
the fppf topology (**Stacks 0771** (1),
`AlgebraicGeometry.Stack.isSheaf_fppf_of_isLocallyQuasicoherentWithSheafFlatBaseChange`) and the
two classes are conditions on the same underlying presheaf of modules
(`AlgebraicGeometry.Stack.locallyQuasicoherentSheafFlatBaseChangeEtale_iff_imageOfLE`). Condition
(3) is the Zariski covering of a scheme by affines, and condition (4) is the vanishing of the
higher fppf cohomology of a module of `LQCoh^fbc(𝒪_𝒳)` over an affine object (Descent,
**Stacks 0756**;
`AlgebraicGeometry.Stack.isZero_rightDerived_evaluation_of_sheafFlatBaseChange_algebraicStack`).

The verification the source omits — that the equivalence matches the complexes with parasitic
cohomology — holds because for a module `M` of `LQCoh^fbc(𝒳_étale, 𝒪_𝒳)`, `ε^*M` is `M` read as
an fppf module, and being parasitic (**Stacks 0773**) is a condition on the sections of the
underlying presheaf (`AlgebraicGeometry.Stack.parasitic_etale_iff_parasitic_epsilonPullback`).
The left vertical arrow and the equivalence of the Verdier quotients then follow formally,
`DerivedCategory.KernelColocalization.isEquivalence_mapDerivedCategoryLift_inter` and
`DerivedCategory.KernelColocalization.quotientEquivalenceOfExactFunctor`.

`D_QCoh(𝒪_𝒳)` is the Verdier quotient of **Stacks 07B6**,
`AlgebraicGeometry.Stack.ParasiticQuotient.quotient` at `LQCoh^fbc(𝒪_𝒳)`.

## Main definitions

* `AlgebraicGeometry.Stack.epsilonPullbackDerivedSheafFlatBaseChange`: the middle vertical arrow.
* `AlgebraicGeometry.Stack.epsilonPullbackDerivedParasiticSheafFlatBaseChange`: the left vertical
  arrow.
* `AlgebraicGeometry.Stack.derivedCategoryQuasicoherentEtaleSheafFlatBaseChangeEquivalence`: the
  final equivalence.

## Main results

* `AlgebraicGeometry.Stack.epsilonPullbackDerivedSheafFlatBaseChange_rightSquare` and
  `AlgebraicGeometry.Stack.epsilonPullbackDerivedSheafFlatBaseChange_leftSquare`: the two squares
  commute.
* `AlgebraicGeometry.Stack.isEquivalence_epsilonPullbackDerivedSheafFlatBaseChange` and
  `AlgebraicGeometry.Stack.isEquivalence_epsilonPullbackDerivedParasiticSheafFlatBaseChange`: the
  left two vertical arrows are equivalences of triangulated categories.

## References

* [Stacks Project, Tag 07B8](https://stacks.math.columbia.edu/tag/07B8)
* [Stacks Project, Tag 07A8](https://stacks.math.columbia.edu/tag/07A8)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0756](https://stacks.math.columbia.edu/tag/0756)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 07B6](https://stacks.math.columbia.edu/tag/07B6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.CompareTopologies DerivedCategory.KernelColocalization

universe u w t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

attribute [local instance] hasSheafify_associatedTopology_algebraicStack
  wEqualsLocallyBijective_associatedTopology_algebraicStack

section Modules

/-- `LQCoh^fbc(𝒳_étale, 𝒪_𝒳)` is a weak Serre class, via the étale associated topology. -/
private theorem isWeakSerreClass_lqcohEtale_aux :
    (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳).IsWeakSerreClass :=
  have := hasSheafify_etaleAssociatedTopology B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
  have := wEqualsLocallyBijective_etaleAssociatedTopology B S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids
  isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChange B E h S hS 𝒳.val.val.p
    𝒳.val.isFiberedInGroupoids

/-- **`LQCoh^fbc(𝒳_étale, 𝒪_𝒳)` is the image of `LQCoh^fbc(𝒪_𝒳)` under `ε_*`.** A module of the
former is a sheaf for the fppf topology (Stacks 0771 (1)), and read as an fppf module it lies in
`LQCoh^fbc(𝒪_𝒳)`, the two classes being conditions on the same underlying presheaf of modules;
conversely `ε_*` does not change that presheaf. -/
theorem locallyQuasicoherentSheafFlatBaseChangeEtale_iff_imageOfLE (N : etaleModules B S hS 𝒳) :
    locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳 N ↔
      imageOfLE (etaleTopologyLeFppf B S hS 𝒳)
        (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf)
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) N := by
  have := isWeakSerreClass_lqcohEtale_aux B E h S hS 𝒳
  exact ⟨fun hN ↦ ⟨⟨N.val, isSheaf_fppf_of_isLocallyQuasicoherentWithSheafFlatBaseChange B E h S hS
      𝒳.val.val.p 𝒳.val.isFiberedInGroupoids N.val hN⟩, hN, ⟨Iso.refl _⟩⟩,
    fun ⟨_, hM, ⟨e⟩⟩ ↦
      (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳).prop_of_iso e hM⟩

/-- **`ε^*` matches the parasitic modules on `LQCoh^fbc(𝒳_étale, 𝒪_𝒳)`.** For `M` in
`LQCoh^fbc(𝒳_étale, 𝒪_𝒳)`, `ε^*M` is `M` read as an fppf module, which it is by Stacks 0771 (1),
and being parasitic is a condition on the sections of the underlying presheaf of modules. -/
theorem parasitic_etale_iff_parasitic_epsilonPullback (M : etaleModules B S hS 𝒳)
    (hM : locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳 M) :
    parasiticModules.{u, w, u} B S hS 𝒳 .etale M ↔
      parasiticModules.{u, w, u} B S hS 𝒳 .fppf ((epsilonPullback B S hS 𝒳).obj M) := by
  let M' : fppfModules B S hS 𝒳 :=
    ⟨M.val, isSheaf_fppf_of_isLocallyQuasicoherentWithSheafFlatBaseChange
      B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids M.val hM⟩
  let e : (epsilonPullback B S hS 𝒳).obj M ≅ M' :=
    SheafOfModules.sheafifyOfLEObjOfLEIso (etaleTopologyLeFppf B S hS 𝒳)
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids .fppf) M'
  exact ⟨(parasiticModules.{u, w, u} B S hS 𝒳 .fppf).prop_of_iso e.symm,
    (parasiticModules.{u, w, u} B S hS 𝒳 .fppf).prop_of_iso e⟩

/-- `ε^*` carries `LQCoh^fbc(𝒳_étale, 𝒪_𝒳)` into `LQCoh^fbc(𝒪_𝒳)`. -/
theorem locallyQuasicoherentSheafFlatBaseChange_epsilonPullback_obj {N : etaleModules B S hS 𝒳}
    (hN : locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳 N) :
    lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳
      ((epsilonPullback B S hS 𝒳).obj N) :=
  prop_epsilonPullback_obj_of_imageOfLE B S hS 𝒳 _ _
    (locallyQuasicoherentSheafFlatBaseChangeEtale_iff_imageOfLE B E h S hS 𝒳) hN

end Modules

section Derived

variable [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]
  [HasDerivedCategory.{t} (etaleModules B S hS 𝒳)]

/-- **Stacks 07B8, the middle vertical arrow of the diagram**,

`ε^* : D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) ⥤ D_{LQCoh^fbc}(𝒪_𝒳)`,

with `LQCoh^fbc` read with the flat base change property of Stacks 0762 for the pullback of
sheaves: the corestriction of `ε^*` on the ambient derived categories. -/
@[stacks 07B8 "the middle vertical arrow ε^* : D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) ⥤ \
  D_{LQCoh^fbc}(𝒪_𝒳) of the diagram, for LQCoh^fbc with the flat base change property of \
  Stacks 0762 read with the pullback of sheaves"]
abbrev epsilonPullbackDerivedSheafFlatBaseChange :
    (DerivedCategoryB.derivedCategoryB
        (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)).FullSubcategory :=
  DerivedCategoryB.mapDerivedCategoryLift (epsilonPullback B S hS 𝒳)
    (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳)
    (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)
    (fun _ hN ↦ locallyQuasicoherentSheafFlatBaseChange_epsilonPullback_obj B E h S hS 𝒳 hN)

/-- **Stacks 07B8, the left vertical arrow of the diagram**,

`ε^* : D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳) ⥤ D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`,

with `LQCoh^fbc` read with the flat base change property of Stacks 0762 for the pullback of
sheaves: the corestriction of `ε^*` on the ambient derived categories. -/
@[stacks 07B8 "the left vertical arrow ε^* : D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳) ⥤ \
  D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) of the diagram, for LQCoh^fbc with the flat base change \
  property of Stacks 0762 read with the pullback of sheaves"]
abbrev epsilonPullbackDerivedParasiticSheafFlatBaseChange :
    (derivedInter (parasiticModules.{u, w, u} B S hS 𝒳 .etale)
        (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳)).FullSubcategory ⥤
      (derivedInter (parasiticModules.{u, w, u} B S hS 𝒳 .fppf)
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)).FullSubcategory :=
  mapDerivedCategoryLiftInter (epsilonPullback B S hS 𝒳)
    (parasiticModules.{u, w, u} B S hS 𝒳 .etale)
    (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳)
    (parasiticModules.{u, w, u} B S hS 𝒳 .fppf)
    (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)
    (fun _ hN ↦ locallyQuasicoherentSheafFlatBaseChange_epsilonPullback_obj B E h S hS 𝒳 hN)
    (parasitic_etale_iff_parasitic_epsilonPullback B E h S hS 𝒳)

/-- **Stacks 07B8, the right-hand square of the diagram commutes**: the inclusion
`D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) ⊆ D(𝒳_étale, 𝒪_𝒳)` followed by `ε^*` is `ε^*` followed by the
inclusion `D_{LQCoh^fbc}(𝒪_𝒳) ⊆ D(𝒪_𝒳)`, as an equality of functors. -/
@[stacks 07B8 "the right-hand square of the diagram, for LQCoh^fbc with the flat base change \
  property of Stacks 0762 read with the pullback of sheaves"]
theorem epsilonPullbackDerivedSheafFlatBaseChange_rightSquare :
    (DerivedCategoryB.derivedCategoryB
        (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳)).ι ⋙
        epsilonPullbackDerived B S hS 𝒳 =
      epsilonPullbackDerivedSheafFlatBaseChange B E h S hS 𝒳 ⋙
        (DerivedCategoryB.derivedCategoryB
          (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)).ι :=
  rfl

omit [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)] in
/-- The lower-left horizontal arrow of the diagram of **Stacks 07B8**:
`D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳) ⊆ D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳)`. -/
theorem derivedParasiticSheafFlatBaseChangeEtale_le :
    derivedInter (parasiticModules.{u, w, u} B S hS 𝒳 .etale)
        (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳) ≤
      DerivedCategoryB.derivedCategoryB
        (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳) :=
  fun _ hK n ↦ (hK n).2

omit [HasDerivedCategory.{t} (etaleModules B S hS 𝒳)] in
/-- The upper-left horizontal arrow of the diagram of **Stacks 07B8**:
`D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⊆ D_{LQCoh^fbc}(𝒪_𝒳)`. -/
theorem derivedParasiticSheafFlatBaseChange_le :
    derivedInter (parasiticModules.{u, w, u} B S hS 𝒳 .fppf)
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) ≤
      DerivedCategoryB.derivedCategoryB
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) :=
  fun _ hK n ↦ (hK n).2

/-- **Stacks 07B8, the left-hand square of the diagram commutes**: the inclusion
`D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳) ⊆ D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳)` followed by `ε^*` is `ε^*` followed by
the inclusion `D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳) ⊆ D_{LQCoh^fbc}(𝒪_𝒳)`, as an equality of
functors. -/
@[stacks 07B8 "the left-hand square of the diagram, for LQCoh^fbc with the flat base change \
  property of Stacks 0762 read with the pullback of sheaves"]
theorem epsilonPullbackDerivedSheafFlatBaseChange_leftSquare :
    ObjectProperty.ιOfLE (derivedParasiticSheafFlatBaseChangeEtale_le B E h S hS 𝒳) ⋙
        epsilonPullbackDerivedSheafFlatBaseChange B E h S hS 𝒳 =
      epsilonPullbackDerivedParasiticSheafFlatBaseChange B E h S hS 𝒳 ⋙
        ObjectProperty.ιOfLE (derivedParasiticSheafFlatBaseChange_le B E h S hS 𝒳) :=
  rfl

end Derived

section Moreover

attribute [local instance] enoughInjectives_fppfModules
  Stacks.Cohomology.AcyclicCover.evaluation_additive

variable [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]
  [HasDerivedCategory.{t} (etaleModules B S hS 𝒳)]

omit [HasDerivedCategory.{t} (fppfModules B S hS 𝒳)]
  [HasDerivedCategory.{t} (etaleModules B S hS 𝒳)] in
/-- `LQCoh^fbc(𝒳_étale, 𝒪_𝒳)` is a weak Serre subcategory of `Mod(𝒳_étale, 𝒪_𝒳)` (Stacks 0771 (2)
for the étale site,
`AlgebraicGeometry.Stack.isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChange`), read on the
étale site of the algebraic stack. -/
theorem isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeEtaleModules :
    (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳).IsWeakSerreClass :=
  isWeakSerreClass_lqcohEtale_aux B E h S hS 𝒳

attribute [local instance] isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeEtaleModules

/-- The middle vertical arrow is an equivalence: **Stacks 07A8** applied with `𝒜 = LQCoh^fbc(𝒪_𝒳)`
and `ℬ` the objects over affine schemes, whose conditions are Stacks 0771 (2)
(`AlgebraicGeometry.Stack.isWeakSerreClass_locallyQuasicoherentSheafFlatBaseChangeFppfModules`),
Stacks 0771 (1)
(`AlgebraicGeometry.Stack.locallyQuasicoherentSheafFlatBaseChangeEtale_iff_imageOfLE`), the Zariski
covering of a scheme by affines and Descent, Stacks 0756
(`AlgebraicGeometry.Stack.isZero_rightDerived_evaluation_of_sheafFlatBaseChange_algebraicStack`).
-/
instance isEquivalence_epsilonPullbackDerivedSheafFlatBaseChange_functor :
    (epsilonPullbackDerivedSheafFlatBaseChange B E h S hS 𝒳).IsEquivalence :=
  isEquivalence_epsilonPullbackDerivedLift_of_vanishing B S hS 𝒳
    (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)
    (fun F hF x hx n hn ↦ isZero_rightDerived_evaluation_of_sheafFlatBaseChange_algebraicStack
      B E h S hS 𝒳 F hF x hx n hn)
    (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳)
    (locallyQuasicoherentSheafFlatBaseChangeEtale_iff_imageOfLE B E h S hS 𝒳)

/-- **Stacks 07B8, the middle vertical arrow is an equivalence of triangulated categories**:

`ε^* : D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) ⥤ D_{LQCoh^fbc}(𝒪_𝒳)`

is an equivalence, and it is a triangulated functor for the triangulated structures of the two
strictly full triangulated subcategories, `LQCoh^fbc` being a weak Serre subcategory on both
sites. -/
@[stacks 07B8 "the middle vertical arrow is an equivalence of triangulated categories, for \
  LQCoh^fbc with the flat base change property of Stacks 0762 read with the pullback of sheaves"]
theorem isEquivalence_epsilonPullbackDerivedSheafFlatBaseChange :
    (epsilonPullbackDerivedSheafFlatBaseChange B E h S hS 𝒳).IsEquivalence ∧
      (epsilonPullbackDerivedSheafFlatBaseChange B E h S hS 𝒳).IsTriangulated :=
  ⟨inferInstance, inferInstance⟩

/-- The left vertical arrow is an equivalence: the restriction of the middle one, which matches
the complexes with parasitic cohomology
(`AlgebraicGeometry.Stack.parasitic_etale_iff_parasitic_epsilonPullback`). -/
instance isEquivalence_epsilonPullbackDerivedParasiticSheafFlatBaseChange_functor :
    (epsilonPullbackDerivedParasiticSheafFlatBaseChange B E h S hS 𝒳).IsEquivalence :=
  isEquivalence_mapDerivedCategoryLift_inter (epsilonPullback B S hS 𝒳)
    (parasiticModules.{u, w, u} B S hS 𝒳 .etale)
    (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳)
    (parasiticModules.{u, w, u} B S hS 𝒳 .fppf)
    (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)
    (fun _ hN ↦ locallyQuasicoherentSheafFlatBaseChange_epsilonPullback_obj B E h S hS 𝒳 hN)
    (parasitic_etale_iff_parasitic_epsilonPullback B E h S hS 𝒳)

/-- **`𝒫_𝒳` is a weak Serre subcategory of `Mod(𝒳_étale, 𝒪_𝒳)`.** On `LQCoh^fbc(𝒳_étale, 𝒪_𝒳)`
a module is parasitic exactly when its image under the exact functor `ε^*` is, so `𝒫_𝒳` is the
intersection of `LQCoh^fbc(𝒳_étale, 𝒪_𝒳)` with the inverse image under `ε^*` of the weak Serre
subcategory `Parasitic(𝒪_𝒳) ∩ LQCoh^fbc(𝒪_𝒳)` of `Mod(𝒪_𝒳)`. -/
instance isWeakSerreClass_parasiticInfSheafFlatBaseChangeEtale :
    (parasiticModules.{u, w, u} B S hS 𝒳 .etale ⊓
      locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳).IsWeakSerreClass := by
  have heq : parasiticModules.{u, w, u} B S hS 𝒳 .etale ⊓
      locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳 =
    locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳 ⊓
      (parasiticModules.{u, w, u} B S hS 𝒳 .fppf ⊓
        lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳).inverseImage
          (epsilonPullback B S hS 𝒳) := by
    funext M
    exact propext
      ⟨fun ⟨hP, hL⟩ ↦ ⟨hL, (parasitic_etale_iff_parasitic_epsilonPullback B E h S hS 𝒳 M hL).1 hP,
          locallyQuasicoherentSheafFlatBaseChange_epsilonPullback_obj B E h S hS 𝒳 hL⟩,
        fun ⟨hL, hP, _⟩ ↦
          ⟨(parasitic_etale_iff_parasitic_epsilonPullback B E h S hS 𝒳 M hL).2 hP, hL⟩⟩
  rw [heq]
  infer_instance

/-- **Stacks 07B8, the left vertical arrow is an equivalence of triangulated categories**:

`ε^* : D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳) ⥤ D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)`

is an equivalence, and it is a triangulated functor, `Parasitic ∩ LQCoh^fbc` being a weak Serre
subcategory on both sites. This includes the verification the source omits, that the
equivalence of the middle arrow matches the complexes with parasitic cohomology sheaves. -/
@[stacks 07B8 "the left vertical arrow is an equivalence of triangulated categories, for \
  LQCoh^fbc with the flat base change property of Stacks 0762 read with the pullback of sheaves"]
theorem isEquivalence_epsilonPullbackDerivedParasiticSheafFlatBaseChange :
    (epsilonPullbackDerivedParasiticSheafFlatBaseChange B E h S hS 𝒳).IsEquivalence ∧
      (epsilonPullbackDerivedParasiticSheafFlatBaseChange B E h S hS 𝒳).IsTriangulated :=
  ⟨inferInstance, inferInstance⟩

/-- **Stacks 07B8, the last assertion**: the equivalence

`D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) / D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳) ≌ D_QCoh(𝒪_𝒳)`

induced by `ε^*`, where `D_QCoh(𝒪_𝒳)` is the Verdier quotient
`D_{LQCoh^fbc}(𝒪_𝒳) / D_{Parasitic ∩ LQCoh^fbc}(𝒪_𝒳)` of **Stacks 07B6**,
`AlgebraicGeometry.Stack.ParasiticQuotient.quotient`. The middle vertical arrow is an equivalence
matching the classes of morphisms the two Verdier quotients invert, because it matches the
complexes with parasitic cohomology; see
`DerivedCategory.KernelColocalization.quotientEquivalenceOfExactFunctor`. That it is induced by
`ε^*` is `toQuotientCompDerivedCategoryQuasicoherentEtaleSheafFlatBaseChangeEquivalenceIso`. -/
@[stacks 07B8 "the last assertion: the induced equivalence \
  D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) / D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳) ≌ D_QCoh(𝒪_𝒳), for LQCoh^fbc with the \
  flat base change property of Stacks 0762 read with the pullback of sheaves"]
def derivedCategoryQuasicoherentEtaleSheafFlatBaseChangeEquivalence :
    quotient (parasiticModules.{u, w, u} B S hS 𝒳 .etale)
        (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳) ≌
      ParasiticQuotient.quotient B S hS 𝒳
        (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) :=
  quotientEquivalenceOfExactFunctor (epsilonPullback B S hS 𝒳)
    (parasiticModules.{u, w, u} B S hS 𝒳 .etale)
    (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳)
    (parasiticModules.{u, w, u} B S hS 𝒳 .fppf)
    (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)
    (fun _ hN ↦ locallyQuasicoherentSheafFlatBaseChange_epsilonPullback_obj B E h S hS 𝒳 hN)
    (parasitic_etale_iff_parasitic_epsilonPullback B E h S hS 𝒳)

/-- The equivalence of **Stacks 07B8** is induced by `ε^*`: the quotient functor onto
`D_{LQCoh^fbc}(𝒳_étale, 𝒪_𝒳) / D_{𝒫_𝒳}(𝒳_étale, 𝒪_𝒳)` followed by it is the middle vertical
arrow followed by the quotient functor onto `D_QCoh(𝒪_𝒳)`. -/
def toQuotientCompDerivedCategoryQuasicoherentEtaleSheafFlatBaseChangeEquivalenceIso :
    toQuotient (parasiticModules.{u, w, u} B S hS 𝒳 .etale)
        (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳) ⋙
        (derivedCategoryQuasicoherentEtaleSheafFlatBaseChangeEquivalence B E h S hS 𝒳).functor ≅
      epsilonPullbackDerivedSheafFlatBaseChange B E h S hS 𝒳 ⋙
        ParasiticQuotient.toQuotient B S hS 𝒳
          (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳) :=
  toQuotientCompQuotientEquivalenceOfExactFunctorIso (epsilonPullback B S hS 𝒳)
    (parasiticModules.{u, w, u} B S hS 𝒳 .etale)
    (locallyQuasicoherentSheafFlatBaseChangeEtaleModules B E h S hS 𝒳)
    (parasiticModules.{u, w, u} B S hS 𝒳 .fppf)
    (lqcohSheafFbcFppfModules.{u, _, u} B E h S hS 𝒳)
    (fun _ hN ↦ locallyQuasicoherentSheafFlatBaseChange_epsilonPullback_obj B E h S hS 𝒳 hN)
    (parasitic_etale_iff_parasitic_epsilonPullback B E h S hS 𝒳)

end Moreover

end AlgebraicGeometry.Stack

end
