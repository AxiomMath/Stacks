module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.Coherence
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageSmoothLocalCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteDerivedModuleBaseChange

/-!
# Quasi-coherence of the cohomology of `Lg_!` (Stacks 07B3)

Let `𝒳` be an algebraic stack and let `g` be the morphism of ringed topoi of **Stacks 0788**,
from the lisse-étale site of `𝒳` to its big étale site in case (1) and from the flat-fppf site to
the big fppf site in case (2). **Stacks 07B3** says that for a quasi-coherent module `H` on the
subsite and every `p ∈ ℤ` the sheaf `H^p(Lg_! H)` is locally quasi-coherent (**Stacks 06WJ**) and
has the flat base change property (**Stacks 0762**) on `𝒳`, that is, lies in
`LQCoh^fbc(𝒪_𝒳)`.

The last paragraph of the source proof is what is carried out here. The source computes `Lg_! H`,
in the case of a global presentation over an affine base, as the complex `𝒪_𝒳 ⊗_A F_•` attached to
a free resolution `F_•` of the corresponding module, and then concludes by **Stacks 0771**
part (2), which says that `LQCoh^fbc(𝒪_𝒳)` is a weak Serre subcategory of both
`Mod(𝒪_𝒳)` and `Mod(𝒳_étale, 𝒪_𝒳)`: the cohomology of a complex whose terms lie in a weak Serre
subcategory lies in it.

## What is carried as a hypothesis, and why

*The functor `Lg_!`.* Nothing in this library constructs the unbounded total left derived functor
of the module-level lower shriek `g_!` of **Stacks 0789** on either subsite; only `g_!` itself is
available, and only the abelian-sheaf `Lg_!` of **Stacks 07AS** part (3). So `Lg_!` is carried as
data, exactly as in
`StacksFrontier/AlgebraicGeometry/Stacks/SubsiteDerivedModuleBaseChange.lean`; it stands for
**Stacks 07AS** parts (2) and (4) on sheaves of modules.

*The weak Serre condition.* `hserre` is **Stacks 0771** part (2). For the lisse-étale case it is
the half about `Mod(𝒳_étale, 𝒪_𝒳)`, named as a condition on a rule in the sense of
**Stacks 076Z**, the spelling already used by **Stacks 0765** and **Stacks 075Z**; for
the flat-fppf case it is the half about `Mod(𝒪_𝒳)`, written out on the fppf site. Only part (3)
of **Stacks 0771** is proved in this library.

*The representing complex.* `hK` and `e` say that `Lg_! H` is represented by a complex `K` whose
terms are quasi-coherent (**Stacks 03DL**). This is the computation of `Lg_! H` from a free
resolution that the source performs before citing **Stacks 0771**; it is a statement about the
*terms* of `K`, and the content proved here is the passage from those terms to the cohomology
objects. The reduction of the general case to the affine one with a global presentation, by
**Stacks 07AQ** and **Stacks 07AV**, is not carried out.

*Quasi-coherent modules lie in `LQCoh^fbc`.* `hqc` is **Stacks 06WK**, which this library does not
have in any form; it is what turns the quasi-coherence of the terms of `K` into membership in the
weak Serre subcategory.

## Main results

* `AlgebraicGeometry.Stack.LisseEtale.isLocallyQuasicoherent_homology_derivedModuleLowerShriek`
  and `AlgebraicGeometry.Stack.LisseEtale.hasFlatBaseChange_homology_derivedModuleLowerShriek`:
  **Stacks 07B3** part (1), its two halves.
* `AlgebraicGeometry.Stack.FlatFppf.isLocallyQuasicoherent_homology_derivedModuleLowerShriek` and
  `AlgebraicGeometry.Stack.FlatFppf.hasFlatBaseChange_homology_derivedModuleLowerShriek`:
  **Stacks 07B3** part (2), its two halves.
* `locallyQuasicoherentFlatBaseChange_homology_derivedModuleLowerShriek` in each of the two
  namespaces: the two halves of each part at once, as membership in `LQCoh^fbc(𝒪_𝒳)`.

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

/-- **Stacks 07B3 part (1), both halves at once**: for a quasi-coherent module `H` on the
lisse-étale site of `𝒳`, every cohomology sheaf of `Lg_! H` lies in `LQCoh^fbc(𝒪_𝒳)`, granted
**Stacks 0771** part (2), **Stacks 06WK**, and a representation of `Lg_! H` by a complex with
quasi-coherent terms. -/
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

/-- **Stacks 07B3 part (1), local quasi-coherence**: for a quasi-coherent module `H` on the
lisse-étale site of `𝒳`, every cohomology sheaf of `Lg_! H` is locally quasi-coherent. -/
@[stacks 07B3 "part (1), the local quasi-coherence half: for a quasi-coherent module `H` on the \
lisse-étale site of an algebraic stack `𝒳` and every `p`, the sheaf `H^p(Lg_! H)` is locally \
quasi-coherent (Stacks 06WJ) on `𝒳`, read at section universe `u + 1`. Three hypotheses are \
carried. `Lg` is the functor `Lg_!` itself, carried as data because this library constructs no \
unbounded total left derived functor of the module-level `g_!` of Stacks 0789 (1); it stands for \
Stacks 07AS (2) and (4) on sheaves of modules, and is carried in the same shape as in \
StacksFrontier/AlgebraicGeometry/Stacks/SubsiteDerivedModuleBaseChange.lean. `hserre` is \
Stacks 0771 part (2), the half saying that LQCoh^fbc is a weak Serre subcategory of \
Mod(𝒳_étale, 𝒪_𝒳); only part (3) of Stacks 0771 is proved here. `hK` and `e` say that `Lg_! H` \
is represented by a complex whose TERMS are quasi-coherent (Stacks 03DL), which is the \
computation of `Lg_! H` from a free resolution that the source performs before citing \
Stacks 0771, and `hqc` is Stacks 06WK, that a quasi-coherent module lies in LQCoh^fbc, which \
this library does not have in any form; the reduction of the general case to the affine case \
with a global presentation, by Stacks 07AQ and Stacks 07AV, is not carried out. The \
quasi-coherence hypothesis on `H` is the source's and is unweakened"]
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

/-- **Stacks 07B3 part (1), the flat base change property**: for a quasi-coherent module `H` on
the lisse-étale site of `𝒳`, every cohomology sheaf of `Lg_! H` has the flat base change
property. -/
@[stacks 07B3 "part (1), the flat base change half: for a quasi-coherent module `H` on the \
lisse-étale site of an algebraic stack `𝒳` and every `p`, the sheaf `H^p(Lg_! H)` has the flat \
base change property (Stacks 0762) on `𝒳`, read at section universe `u + 1` through \
HasFlatBaseChangePropertyUnivLE, the comparison map of Stacks 06WC pinning the other spelling to \
Type u. The same three hypotheses are carried as for the local quasi-coherence half. `Lg` is \
`Lg_!` carried as data, standing for Stacks 07AS (2) and (4) on sheaves of modules, no unbounded \
total left derived functor of the module-level `g_!` of Stacks 0789 (1) being constructed here. \
`hserre` is Stacks 0771 part (2) for Mod(𝒳_étale, 𝒪_𝒳); only part (3) of Stacks 0771 is proved \
here. `hK` and `e` say that `Lg_! H` is represented by a complex whose TERMS lie in LQCoh^fbc, \
the source's computation of `Lg_! H` from a free resolution; the reduction of the general case to \
the affine case with a global presentation, by Stacks 07AQ and Stacks 07AV, is not carried out. \
The quasi-coherence hypothesis on `H` is the source's and is unweakened"]
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

/-- **Stacks 07B3 part (2), both halves at once**: for a quasi-coherent module `H` on the
flat-fppf site of `𝒳`, every cohomology sheaf of `Lg_! H` lies in `LQCoh^fbc(𝒪_𝒳)`, granted
**Stacks 0771** part (2) for `Mod(𝒪_𝒳)`, **Stacks 06WK**, and a representation of `Lg_! H` by a
complex with quasi-coherent terms. -/
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

/-- **Stacks 07B3 part (2), local quasi-coherence**: for a quasi-coherent module `H` on the
flat-fppf site of `𝒳`, every cohomology sheaf of `Lg_! H` is locally quasi-coherent. -/
@[stacks 07B3 "part (2), the local quasi-coherence half: for a quasi-coherent module `H` on the \
flat-fppf site of an algebraic stack `𝒳` and every `p`, the sheaf `H^p(Lg_! H)` is locally \
quasi-coherent (Stacks 06WJ) on `𝒳`, read at section universe `u + 1`. Three hypotheses are \
carried. `Lg` is the functor `Lg_!` itself, carried as data because this library constructs no \
unbounded total left derived functor of the module-level `g_!` of Stacks 0789 (2); it stands for \
Stacks 07AS (2) and (4) on sheaves of modules, and is carried in the same shape as in \
StacksFrontier/AlgebraicGeometry/Stacks/SubsiteDerivedModuleBaseChange.lean. `hserre` is \
Stacks 0771 part (2), the half saying that LQCoh^fbc is a weak Serre subcategory of Mod(𝒪_𝒳), \
written out on the fppf site; only part (3) of Stacks 0771 is proved here. `hK` and `e` say that \
`Lg_! H` is represented by a complex whose TERMS lie in LQCoh^fbc, which is the computation of \
`Lg_! H` from a free resolution that the source performs before citing Stacks 0771; the \
reduction of the general case to the affine case with a global presentation, by Stacks 07AQ and \
Stacks 07AV, is not carried out. The quasi-coherence hypothesis on `H` is the source's and is \
unweakened"]
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

/-- **Stacks 07B3 part (2), the flat base change property**: for a quasi-coherent module `H` on
the flat-fppf site of `𝒳`, every cohomology sheaf of `Lg_! H` has the flat base change
property. -/
@[stacks 07B3 "part (2), the flat base change half: for a quasi-coherent module `H` on the \
flat-fppf site of an algebraic stack `𝒳` and every `p`, the sheaf `H^p(Lg_! H)` has the flat \
base change property (Stacks 0762) on `𝒳`, read at section universe `u + 1` through \
HasFlatBaseChangePropertyUnivLE, the comparison map of Stacks 06WC pinning the other spelling to \
Type u. The same three hypotheses are carried as for the local quasi-coherence half. `Lg` is \
`Lg_!` carried as data, standing for Stacks 07AS (2) and (4) on sheaves of modules, no unbounded \
total left derived functor of the module-level `g_!` of Stacks 0789 (2) being constructed here. \
`hserre` is Stacks 0771 part (2) for Mod(𝒪_𝒳), written out on the fppf site; only part (3) of \
Stacks 0771 is proved here. `hK` and `e` say that `Lg_! H` is represented by a complex whose \
TERMS are quasi-coherent (Stacks 03DL), the source's computation of `Lg_! H` from a free \
resolution, and `hqc` is Stacks 06WK, that a quasi-coherent module lies in LQCoh^fbc, which this \
library does not have in any form; the reduction of the general case to the affine case with a \
global presentation, by Stacks 07AQ and Stacks 07AV, is not carried out. The \
quasi-coherence hypothesis on `H` is the source's and is \
unweakened"]
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
