module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCategorySections
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualGlobalSections

/-!
# Detecting boundedness above with a perfect generator

Let `X` be a quasi-compact, quasi-separated scheme, let `G` be a perfect object of `D(𝒪_X)`
generating `D_QCoh(𝒪_X)`, and let `E` be an object of `D_QCoh(𝒪_X)`. Boundedness above of `E`
is detected by eventual vanishing, as `i → ∞`, of any of the groups `Hom(G⟦-i⟧, E)`,
`Ext^i(G, E)`, `H^i(X, G^∨ ⊗^L E)`, and by boundedness above of `RHom_X(G, E)` and of
`RΓ(X, G^∨ ⊗^L E)`.

Three of the clause equivalences of that statement are proved here. The eventual vanishing of
`Hom(G⟦-i⟧, E)` agrees with that of `Ext^i(G, E)`, by the adjunction between the shifts
`⟦-i⟧ ⊣ ⟦i⟧`. The eventual vanishing of `Ext^i(G, E)` agrees with that of
`H^i(X, G^∨ ⊗^L E)`, because the two groups are the same: the duality identification
`H⁰(X, M ⊗^L G^∨) ≅ Hom(G, M)` at `M = E⟦i⟧` turns the second into the first, the shift passing
through the derived tensor product and `RΓ(X, -)`. And the eventual vanishing of
`H^i(X, G^∨ ⊗^L E)` agrees with membership of `RΓ(X, G^∨ ⊗^L E)` in `D⁻(ℤ)`, by the description
of the bounded-above derived category of an abelian category by its cohomology. Together the
three make `Hom(G⟦-i⟧, E)`, `Ext^i(G, E)`, `H^i(X, G^∨ ⊗^L E)` and `RΓ(X, G^∨ ⊗^L E) ∈ D⁻(ℤ)`
a single block of equivalent conditions.

## Main results

* `Stacks.SheafOfModules.subsingleton_ext_iff_isZero_homology_derivedTensorDual_of_isPerfect`:
  in each single degree `i`, the group `Ext^i_X(G, E)` vanishes exactly when
  `H^i(X, G^∨ ⊗^L E)` does.
* `Stacks.SheafOfModules.eventually_subsingleton_shiftedHom_iff_ext_atTop`: eventual vanishing
  of `Hom(G⟦-i⟧, E)` and of `Ext^i(G, E)` are the same condition.
* `Stacks.SheafOfModules.eventually_subsingleton_ext_iff_isZero_homology_atTop`: eventual
  vanishing of `Ext^i(G, E)` and of `H^i(X, G^∨ ⊗^L E)` are the same condition.
* `Stacks.SheafOfModules.minus_derivedGlobalSections_derivedTensor_derivedDual_iff`:
  `RΓ(X, G^∨ ⊗^L E)` lies in `D⁻(ℤ)` exactly when `H^i(X, G^∨ ⊗^L E)` vanishes for `i ≫ 0`.

## Implementation notes

The hypotheses of the source statement — quasi-compactness and quasi-separatedness of `X`,
perfectness of `G`, generation of `D_QCoh(𝒪_X)` by `G`, and quasi-coherence of the cohomology
of `E` — are carried on all three clause equivalences although only perfectness of `G` is used
by one of them: they are the hypotheses under which the source asserts the equivalence of all
its conditions, and the two conditions of each result are the source's conditions. No hypothesis
beyond the source's is carried.

Generation of `D_QCoh(𝒪_X)` by `G` is spelled out as the hypothesis that an object of
`D(𝒪_X)` with quasi-coherent cohomology receiving only zero morphisms from the shifts of `G`
is zero. Vanishing of a group of morphisms is `Subsingleton`, and `D⁻(ℤ)` is the object
property `minus` of the canonical t-structure on `D(AddCommGrpCat)`.

The degree-by-degree identification of `Ext^i_X(G, E)` with `H^i(X, G^∨ ⊗^L E)` is proved here
in the form `subsingleton_ext_iff_isZero_homology_derivedTensorDual_of_isPerfect`, which takes
no hypothesis but perfectness of `G`: the duality map of Stacks 08I1 is invertible for a perfect
object by `Stacks.SheafOfModules.bijective_derivedTensorDualGlobalSectionsMap_of_isPerfect`, the
fourth assertion of Stacks 08DQ.

The full statement of Stacks 0GEN, all seven conditions equivalent, is
`Stacks.SheafOfModules.tfae_minus_of_isPerfect_generator` in
`StacksFrontier.AlgebraicGeometry.Perfect.DetectingBoundednessGenerator`, which builds on the
clause equivalences of this module.

## References

* [Stacks Project, Proposition 36.40.5 (Tag 0GEN)](https://stacks.math.columbia.edu/tag/0GEN)
* [Stacks Project, Tag 05RU](https://stacks.math.columbia.edu/tag/05RU)
* [Stacks Project, Lemma 20.50.5 (Tag 08DQ)](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.Cohomology.ModuleSections

namespace Stacks.SheafOfModules

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}}
  [HasSheafify (Opens.grothendieckTopology X.toPresheafedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.toPresheafedSpace.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}]

/-- Eventual vanishing, as `i → ∞`, is invariant under a degreewise equivalence of conditions. -/
private theorem exists_forall_ge_congr {P Q : ℤ → Prop} (h : ∀ i, P i ↔ Q i) :
    (∃ N : ℤ, ∀ i, N ≤ i → P i) ↔ ∃ N : ℤ, ∀ i, N ≤ i → Q i :=
  exists_congr fun _ => forall₂_congr fun i _ => h i

/-- **Stacks 0GEN, conditions (2) and (3).** For a perfect generator `G` of `D_QCoh(𝒪_X)` on a
quasi-compact, quasi-separated scheme and an object `E` of `D_QCoh(𝒪_X)`, the groups
`Hom_{D(𝒪_X)}(G⟦-i⟧, E)` vanish for `i ≫ 0` exactly when the groups `Ext^i_X(G, E)` do.

The two conditions hold of the same `i`, because `⟦-i⟧` is left adjoint to `⟦i⟧`. -/
theorem eventually_subsingleton_shiftedHom_iff_ext_atTop
    (_hqc : CompactSpace X) (_hqs : QuasiSeparatedSpace X)
    (G E : DerivedCategory (StructureSheafModules X.sheaf))
    (_hG : (ringedSite X.sheaf).IsPerfect G)
    (_hgen : ∀ K : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
          (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent) →
        (∀ (n : ℤ) (f : G⟦n⟧ ⟶ K), f = 0) → IsZero K)
    (_hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj E).IsQuasicoherent) :
    (∃ N : ℤ, ∀ i, N ≤ i → Subsingleton (G⟦-i⟧ ⟶ E)) ↔
      ∃ N : ℤ, ∀ i, N ≤ i → Subsingleton (DerivedCategory.Ext G E i) :=
  exists_forall_ge_congr fun i =>
    ((shiftEquiv' (DerivedCategory (StructureSheafModules X.sheaf)) (-i) i
      (neg_add_cancel i)).toAdjunction.homEquiv G E).subsingleton_congr

variable
  [(Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} X.sheaf)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)]

/-- **Stacks 0GEN, conditions (5) and (6).** For a perfect generator `G` of `D_QCoh(𝒪_X)` on a
quasi-compact, quasi-separated scheme and an object `E` of `D_QCoh(𝒪_X)`, the cohomology groups
`H^i(X, G^∨ ⊗^L_{𝒪_X} E)` vanish for `i ≫ 0` exactly when `RΓ(X, G^∨ ⊗^L_{𝒪_X} E)` lies in
`D⁻(ℤ)`.

This is the description of the bounded-above derived category by its cohomology, applied to the
single object `RΓ(X, G^∨ ⊗^L_{𝒪_X} E)` of `D(AddCommGrpCat)`. -/
theorem minus_derivedGlobalSections_derivedTensor_derivedDual_iff
    (_hqc : CompactSpace X) (_hqs : QuasiSeparatedSpace X)
    (G E : DerivedCategory (StructureSheafModules X.sheaf))
    (_hG : (ringedSite X.sheaf).IsPerfect G)
    (_hgen : ∀ K : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
          (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent) →
        (∀ (n : ℤ) (f : G⟦n⟧ ⟶ K), f = 0) → IsZero K)
    (_hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj E).IsQuasicoherent) :
    (DerivedCategory.TStructure.t (C := AddCommGrpCat.{u})).minus
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
          (((derivedTensor X.sheaf).obj E).obj (derivedDual X.sheaf G))) ↔
      ∃ N : ℤ, ∀ n, N ≤ n → IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
          (((derivedTensor X.sheaf).obj E).obj (derivedDual X.sheaf G)))) :=
  DerivedCategory.minus_iff _

variable [∀ V : Opens X.toPresheafedSpace.carrier,
    HasSheafify ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V)
      AddCommGrpCat.{u}]
  [∀ V : Opens X.toPresheafedSpace.carrier,
    ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V).WEqualsLocallyBijective
      AddCommGrpCat.{u}]
  [∀ V : Opens X.toPresheafedSpace.carrier,
    HasWeakSheafify ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V)
      AddCommGrpCat.{u}]

/-- **Stacks 0GEN, conditions (3) and (5), in a single degree.** For a perfect object `G` of
`D(𝒪_X)` and any object `E`, the group `Ext^i_X(G, E)` vanishes exactly when the cohomology
group `H^i(X, G^∨ ⊗^L_{𝒪_X} E)` does, the two being the same group.

Stacks 08DQ identifies `H⁰(X, M ⊗^L_{𝒪_X} G^∨)` with `Hom(G, M)` for a perfect `G`, and at
`M = E⟦i⟧` the left side becomes `H^i(X, G^∨ ⊗^L_{𝒪_X} E)` because tensoring with `G^∨` and
`RΓ(X, -)` are triangulated, hence commute with the shift, and `H⁰` of an `i`-fold shift is
`H^i`. -/
theorem subsingleton_ext_iff_isZero_homology_derivedTensorDual_of_isPerfect
    (G E : DerivedCategory (StructureSheafModules X.sheaf))
    (hG : (ringedSite X.sheaf).IsPerfect G) (i : ℤ) :
    Subsingleton (DerivedCategory.Ext G E i) ↔
      IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
          (((derivedTensor X.sheaf).obj E).obj (derivedDual X.sheaf G)))) := by
  let _ : ((derivedTensor X.sheaf).flip.obj (derivedDual X.sheaf G)).CommShift ℤ :=
    (canonicalDerivedTensorProduct (ringedSite X.sheaf)).commShift_left (derivedDual X.sheaf G)
  let shiftIso := (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
      ((derivedModuleGlobalSections (ringedSite X.sheaf)).mapIso
        ((((derivedTensor X.sheaf).flip.obj (derivedDual X.sheaf G)).commShiftIso i).app E)) ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
        (((derivedModuleGlobalSections (ringedSite X.sheaf)).commShiftIso i).app
          (((derivedTensor X.sheaf).obj E).obj (derivedDual X.sheaf G))) ≪≫
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).isoShift i).app
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
          (((derivedTensor X.sheaf).obj E).obj (derivedDual X.sheaf G)))
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact ((Equiv.ofBijective _ (bijective_derivedTensorDualGlobalSectionsMap_of_isPerfect
    X.sheaf G (E⟦i⟧) hG)).symm.trans (Equiv.ofBijective _
      (ConcreteCategory.bijective_of_isIso shiftIso.hom))).subsingleton_congr

/-- **Stacks 0GEN, conditions (3) and (5).** For a perfect generator `G` of `D_QCoh(𝒪_X)` on a
quasi-compact, quasi-separated scheme and an object `E` of `D_QCoh(𝒪_X)`, the groups
`Ext^i_X(G, E)` vanish for `i ≫ 0` exactly when the cohomology groups
`H^i(X, G^∨ ⊗^L_{𝒪_X} E)` do.

The two conditions hold of the same `i`, by
`subsingleton_ext_iff_isZero_homology_derivedTensorDual_of_isPerfect`. -/
theorem eventually_subsingleton_ext_iff_isZero_homology_atTop
    (_hqc : CompactSpace X) (_hqs : QuasiSeparatedSpace X)
    (G E : DerivedCategory (StructureSheafModules X.sheaf))
    (hG : (ringedSite X.sheaf).IsPerfect G)
    (_hgen : ∀ K : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
          (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent) →
        (∀ (n : ℤ) (f : G⟦n⟧ ⟶ K), f = 0) → IsZero K)
    (_hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj E).IsQuasicoherent) :
    (∃ N : ℤ, ∀ i, N ≤ i → Subsingleton (DerivedCategory.Ext G E i)) ↔
      ∃ N : ℤ, ∀ n, N ≤ n → IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
          (((derivedTensor X.sheaf).obj E).obj (derivedDual X.sheaf G)))) :=
  exists_forall_ge_congr fun i =>
    subsingleton_ext_iff_isZero_homology_derivedTensorDual_of_isPerfect G E hG i

end Stacks.SheafOfModules

end
