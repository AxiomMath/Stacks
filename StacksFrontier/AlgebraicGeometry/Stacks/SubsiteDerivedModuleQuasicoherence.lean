module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.Coherence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageSmoothLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteDerivedModuleBaseChange

/-!
# The weak Serre step of Stacks 07B3, for a complex representing `Lg_! H`

Let `𝒳` be an algebraic stack and let `g` be the morphism of ringed topoi of **Stacks 0788**,
from the lisse-étale site of `𝒳` to its big étale site in case (1) and from the flat-fppf site to
the big fppf site in case (2). **Stacks 07B3** says that for a quasi-coherent module `H` on the
subsite and every `p ∈ ℤ` the sheaf `H^p(Lg_! H)` is locally quasi-coherent (**Stacks 06WJ**) and
has the flat base change property (**Stacks 0762**) on `𝒳`, that is, lies in
`LQCoh^fbc(𝒪_𝒳)`.

**Stacks 07B3** itself is proved, with no hypothesis beyond the quasi-coherence of `H` and for the
derived lower shriek `Lg_!` constructed in this library (**Stacks 07AS** (2) and (4)), by
`LisseEtale.isLocallyQuasicoherentWithSheafFlatBaseChange_homology_derivedModuleLowerShriek`
(part (1)) and
`FlatFppf.locallyQuasicoherentSheafFlatBaseChange_homology_derivedModuleLowerShriek`
(part (2)), both in the namespace `AlgebraicGeometry.Stack`, in the files
`Quasicoherent/LisseEtaleDerivedModuleLowerShriekSheafFlatBaseChange.lean` and
`Quasicoherent/FlatFppfDerivedModuleLowerShriekSheafFlatBaseChange.lean` of this directory.
Those read the flat base change property with the pullback of *sheaves*, as the source does.

This file isolates the last paragraph of the source proof in an abstract form: if a functor `Lg`
sends `H` to an object represented by a complex `K` whose terms lie in a weak Serre class, then
so does every cohomology object. The class used here is the presheaf-level one,
`AlgebraicGeometry.Stack.locallyQuasicoherentFlatBaseChangeRule`, whose flat base change property
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertyUnivLE` asks the comparison map to be an
isomorphism of *presheaves*. That reading is strictly stronger than **Stacks 0762** and fails for
some quasi-coherent modules (see
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SheafFlatBaseChangeProperty.lean`), so the
hypothesis `hqc` below does not hold in general; the results here are not a form of Stacks 07B3.

The hypotheses: `Lg`, `H` and `K` are arbitrary; `hK` and `e` say that `Lg H` is represented by a
complex whose terms are quasi-coherent (**Stacks 03DL**); `hserre` says the presheaf-level class
is a weak Serre subcategory; and `hqc` says that it contains every quasi-coherent module.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.isLocallyQuasicoherent_homology_derivedModuleLowerShriek`
  and `AlgebraicGeometry.Stack.LisseEtale.hasFlatBaseChange_homology_derivedModuleLowerShriek`:
  the lisse-étale case, its two halves.
* `AlgebraicGeometry.Stack.FlatFppf.isLocallyQuasicoherent_homology_derivedModuleLowerShriek` and
  `AlgebraicGeometry.Stack.FlatFppf.hasFlatBaseChange_homology_derivedModuleLowerShriek`:
  the flat-fppf case, its two halves.
* `locallyQuasicoherentFlatBaseChange_homology_derivedModuleLowerShriek` in each of the two
  namespaces: the two halves of each case at once.

## Implementation notes

The sheaves of modules have sections in `Type (u + 1)`, as in
`StacksFrontier/AlgebraicGeometry/Stacks/SubsiteDerivedModuleBaseChange.lean`: the two sites have
objects in `Type (u + 1)` and morphisms in `Type u`, and the module universe has to dominate both
for `Mod(𝒪)` to be Grothendieck abelian. The flat base change property is therefore read through
`AlgebraicGeometry.Stack.HasFlatBaseChangePropertyUnivLE`, whose module universe is free, rather
than through `AlgebraicGeometry.Stack.HasFlatBaseChangeProperty`, which the comparison map of
**Stacks 06WC** pins to `Type u`.

In the flat-fppf case the two predicates are conditions on the étale site, as in the source,
while `Lg_!` lands on the fppf site. No coarsening is needed to state them: the underlying
presheaf of rings of `AlgebraicGeometry.Stack.ringStructureSheafCore` does not depend on the
topology, only its sheaf condition does, so an fppf sheaf of modules has the same underlying
presheaf of modules over the same presheaf of rings as an étale one.

## References

* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0788](https://stacks.math.columbia.edu/tag/0788)
* [Stacks Project, Tag 0789](https://stacks.math.columbia.edu/tag/0789)
* [Stacks Project, Tag 07AS](https://stacks.math.columbia.edu/tag/07AS)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w dA dA'

/-- The `p`-th cohomology of an object isomorphic to `Q K` lies in a weak Serre class containing
the terms of `K`. -/
private theorem prop_homology_of_iso_Q {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : ObjectProperty C) [P.IsWeakSerreClass] (K : CochainComplex C ℤ)
    (hK : ∀ m, P (K.X m)) {X : DerivedCategory C} (e : X ≅ DerivedCategory.Q.obj K) (p : ℤ) :
    P ((DerivedCategory.homologyFunctor C p).obj X) :=
  P.prop_of_iso (((DerivedCategory.homologyFunctor C p).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors C p).app K).symm)
    (ObjectProperty.prop_homology P K p hK)

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-! ### The lisse-étale site -/

namespace LisseEtale

attribute [local instance] hasSheafify_associatedTopology_of_category_succ
  wEqualsLocallyBijective_associatedTopology_of_category_succ

variable
  [HasDerivedCategory.{dA} (_root_.SheafOfModules.{u + 1}
    (ambientRingStructureSheaf B S hS 𝒳))]
  [HasDerivedCategory.{dA'} (_root_.SheafOfModules.{u + 1}
    (subsiteRingStructureSheaf B S hS 𝒳))]
  (Lg : DerivedCategory (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
  (H : _root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
  (K : CochainComplex
    (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) ℤ)

/-- The weak Serre step of **Stacks 07B3**, lisse-étale case, both halves: if `Lg H` is
represented by a complex `K` with quasi-coherent terms, the presheaf-level class
`locallyQuasicoherentFlatBaseChangeRule` is weak Serre (`hserre`) and contains every
quasi-coherent module (`hqc`), then every cohomology sheaf of `Lg H` lies in that class. -/
theorem locallyQuasicoherentFlatBaseChange_homology_derivedModuleLowerShriek
    (_hH : H.IsQuasicoherentOnSite)
    (hserre : StackEtaleModuleRule.IsWeakSerre.{u, w} B S hS
      (locallyQuasicoherentFlatBaseChangeRule B E h S hS))
    (hqc : ∀ F : _root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳),
      F.IsQuasicoherentOnSite → locallyQuasicoherentFlatBaseChangeRule B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids F.val)
    (hK : ∀ m : ℤ, (K.X m).IsQuasicoherentOnSite)
    (e : Lg.obj ((DerivedCategory.singleFunctor _ 0).obj H) ≅ DerivedCategory.Q.obj K)
    (p : ℤ) :
    locallyQuasicoherentFlatBaseChangeRule B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      ((DerivedCategory.homologyFunctor _ p).obj
        (Lg.obj ((DerivedCategory.singleFunctor _ 0).obj H))).val := by
  have := hserre 𝒳
  exact prop_homology_of_iso_Q
    (fun F => locallyQuasicoherentFlatBaseChangeRule B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F.val) K (fun m => hqc (K.X m) (hK m)) e p

/-- The local quasi-coherence half of
`LisseEtale.locallyQuasicoherentFlatBaseChange_homology_derivedModuleLowerShriek`. -/
theorem isLocallyQuasicoherent_homology_derivedModuleLowerShriek
    (hH : H.IsQuasicoherentOnSite)
    (hserre : StackEtaleModuleRule.IsWeakSerre.{u, w} B S hS
      (locallyQuasicoherentFlatBaseChangeRule B E h S hS))
    (hqc : ∀ F : _root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳),
      F.IsQuasicoherentOnSite → locallyQuasicoherentFlatBaseChangeRule B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids F.val)
    (hK : ∀ m : ℤ, (K.X m).IsQuasicoherentOnSite)
    (e : Lg.obj ((DerivedCategory.singleFunctor _ 0).obj H) ≅ DerivedCategory.Q.obj K)
    (p : ℤ) :
    IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      ((DerivedCategory.homologyFunctor _ p).obj
        (Lg.obj ((DerivedCategory.singleFunctor _ 0).obj H))).val :=
  (locallyQuasicoherentFlatBaseChange_homology_derivedModuleLowerShriek B E h S hS 𝒳 Lg H K
    hH hserre hqc hK e p).1

/-- The presheaf-level flat base change half of
`LisseEtale.locallyQuasicoherentFlatBaseChange_homology_derivedModuleLowerShriek`. -/
theorem hasFlatBaseChange_homology_derivedModuleLowerShriek
    (hH : H.IsQuasicoherentOnSite)
    (hserre : StackEtaleModuleRule.IsWeakSerre.{u, w} B S hS
      (locallyQuasicoherentFlatBaseChangeRule B E h S hS))
    (hqc : ∀ F : _root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳),
      F.IsQuasicoherentOnSite → locallyQuasicoherentFlatBaseChangeRule B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids F.val)
    (hK : ∀ m : ℤ, (K.X m).IsQuasicoherentOnSite)
    (e : Lg.obj ((DerivedCategory.singleFunctor _ 0).obj H) ≅ DerivedCategory.Q.obj K)
    (p : ℤ) :
    HasFlatBaseChangePropertyUnivLE B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B)
      ((DerivedCategory.homologyFunctor _ p).obj
        (Lg.obj ((DerivedCategory.singleFunctor _ 0).obj H))).val :=
  (locallyQuasicoherentFlatBaseChange_homology_derivedModuleLowerShriek B E h S hS 𝒳 Lg H K
    hH hserre hqc hK e p).2

end LisseEtale

/-! ### The flat-fppf site -/

namespace FlatFppf

attribute [local instance] GrothendieckTopology.hasSheafify_addCommGrpCat
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

variable
  [HasDerivedCategory.{dA} (_root_.SheafOfModules.{u + 1}
    (ambientRingStructureSheaf B S hS 𝒳))]
  [HasDerivedCategory.{dA'} (_root_.SheafOfModules.{u + 1}
    (subsiteRingStructureSheaf B S hS 𝒳))]
  (Lg : DerivedCategory (_root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳)) ⥤
    DerivedCategory (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)))
  (H : _root_.SheafOfModules.{u + 1} (subsiteRingStructureSheaf B S hS 𝒳))
  (K : CochainComplex
    (_root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳)) ℤ)

/-- The weak Serre step of **Stacks 07B3**, flat-fppf case, both halves: if `Lg H` is
represented by a complex `K` with quasi-coherent terms, the presheaf-level class
`locallyQuasicoherentFlatBaseChangeRule` is weak Serre in `Mod(𝒪_𝒳)` (`hserre`) and contains
every quasi-coherent module (`hqc`), then every cohomology sheaf of `Lg H` lies in that class. -/
theorem locallyQuasicoherentFlatBaseChange_homology_derivedModuleLowerShriek
    (_hH : H.IsQuasicoherentOnSite)
    (hserre : ObjectProperty.IsWeakSerreClass
      (C := _root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
      (fun F => locallyQuasicoherentFlatBaseChangeRule B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids F.val))
    (hqc : ∀ F : _root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳),
      F.IsQuasicoherentOnSite → locallyQuasicoherentFlatBaseChangeRule B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids F.val)
    (hK : ∀ m : ℤ, (K.X m).IsQuasicoherentOnSite)
    (e : Lg.obj ((DerivedCategory.singleFunctor _ 0).obj H) ≅ DerivedCategory.Q.obj K)
    (p : ℤ) :
    locallyQuasicoherentFlatBaseChangeRule B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      ((DerivedCategory.homologyFunctor _ p).obj
        (Lg.obj ((DerivedCategory.singleFunctor _ 0).obj H))).val := by
  have := hserre
  exact prop_homology_of_iso_Q
    (fun F => locallyQuasicoherentFlatBaseChangeRule B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F.val) K (fun m => hqc (K.X m) (hK m)) e p

/-- The local quasi-coherence half of
`FlatFppf.locallyQuasicoherentFlatBaseChange_homology_derivedModuleLowerShriek`. -/
theorem isLocallyQuasicoherent_homology_derivedModuleLowerShriek
    (hH : H.IsQuasicoherentOnSite)
    (hserre : ObjectProperty.IsWeakSerreClass
      (C := _root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
      (fun F => locallyQuasicoherentFlatBaseChangeRule B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids F.val))
    (hqc : ∀ F : _root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳),
      F.IsQuasicoherentOnSite → locallyQuasicoherentFlatBaseChangeRule B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids F.val)
    (hK : ∀ m : ℤ, (K.X m).IsQuasicoherentOnSite)
    (e : Lg.obj ((DerivedCategory.singleFunctor _ 0).obj H) ≅ DerivedCategory.Q.obj K)
    (p : ℤ) :
    IsLocallyQuasicoherent B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      ((DerivedCategory.homologyFunctor _ p).obj
        (Lg.obj ((DerivedCategory.singleFunctor _ 0).obj H))).val :=
  (locallyQuasicoherentFlatBaseChange_homology_derivedModuleLowerShriek B E h S hS 𝒳 Lg H K
    hH hserre hqc hK e p).1

/-- The presheaf-level flat base change half of
`FlatFppf.locallyQuasicoherentFlatBaseChange_homology_derivedModuleLowerShriek`. -/
theorem hasFlatBaseChange_homology_derivedModuleLowerShriek
    (hH : H.IsQuasicoherentOnSite)
    (hserre : ObjectProperty.IsWeakSerreClass
      (C := _root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳))
      (fun F => locallyQuasicoherentFlatBaseChangeRule B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids F.val))
    (hqc : ∀ F : _root_.SheafOfModules.{u + 1} (ambientRingStructureSheaf B S hS 𝒳),
      F.IsQuasicoherentOnSite → locallyQuasicoherentFlatBaseChangeRule B E h S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids F.val)
    (hK : ∀ m : ℤ, (K.X m).IsQuasicoherentOnSite)
    (e : Lg.obj ((DerivedCategory.singleFunctor _ 0).obj H) ≅ DerivedCategory.Q.obj K)
    (p : ℤ) :
    HasFlatBaseChangePropertyUnivLE B E h S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B)
      ((DerivedCategory.homologyFunctor _ p).obj
        (Lg.obj ((DerivedCategory.singleFunctor _ 0).obj H))).val :=
  (locallyQuasicoherentFlatBaseChange_homology_derivedModuleLowerShriek B E h S hS 𝒳 Lg H K
    hH hserre hqc hK e p).2

end FlatFppf

end AlgebraicGeometry.Stack

end
