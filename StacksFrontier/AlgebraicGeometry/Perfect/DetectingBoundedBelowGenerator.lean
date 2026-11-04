module

public import Mathlib.CategoryTheory.Functor.Derived.RightDerivedCommShift
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedCategorySections
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorDual
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDual

/-!
# Detecting boundedness below with a perfect generator

Let `X` be a quasi-compact, quasi-separated scheme, let `G` be a perfect object of `D(𝒪_X)`
generating `D_QCoh(𝒪_X)`, and let `E` be an object of `D_QCoh(𝒪_X)`. Boundedness below of `E`
is detected by eventual vanishing, as `i → -∞`, of any of the groups `Hom(G⟦-i⟧, E)`,
`Ext^i(G, E)`, `H^i(X, G^∨ ⊗^L E)`, and by boundedness below of `RHom_X(G, E)` and of
`RΓ(X, G^∨ ⊗^L E)`.

Three of the clause equivalences of that statement are proved here. The eventual vanishing of
`Hom(G⟦-i⟧, E)` agrees with that of `Ext^i(G, E)`, by the adjunction between the shifts
`⟦-i⟧ ⊣ ⟦i⟧`. The eventual vanishing of `Ext^i(G, E)` agrees with that of
`H^i(X, G^∨ ⊗^L E)`, because the two groups are the same: the duality identification
`H⁰(X, M ⊗^L G^∨) ≅ Hom(G, M)` at `M = E⟦i⟧` turns the second into the first, the shift passing
through the derived tensor product and `RΓ(X, -)`. And the eventual vanishing of
`H^i(X, G^∨ ⊗^L E)` agrees with membership of `RΓ(X, G^∨ ⊗^L E)` in `D⁺(ℤ)`, by the description
of the bounded-below derived category of an abelian category by its cohomology. Together the
three make `Hom(G⟦-i⟧, E)`, `Ext^i(G, E)`, `H^i(X, G^∨ ⊗^L E)` and `RΓ(X, G^∨ ⊗^L E) ∈ D⁺(ℤ)`
a single block of equivalent conditions.

## Main results

* `Stacks.SheafOfModules.eventually_subsingleton_shiftedHom_iff_ext`: eventual vanishing of
  `Hom(G⟦-i⟧, E)` and of `Ext^i(G, E)` are the same condition.
* `Stacks.SheafOfModules.eventually_subsingleton_ext_iff_isZero_homology_derivedTensorDual`:
  eventual vanishing of `Ext^i(G, E)` and of `H^i(X, G^∨ ⊗^L E)` are the same condition.
* `Stacks.SheafOfModules.plus_derivedGlobalSections_derivedTensor_derivedDual_iff`:
  `RΓ(X, G^∨ ⊗^L E)` lies in `D⁺(ℤ)` exactly when `H^i(X, G^∨ ⊗^L E)` vanishes for `i ≪ 0`.

## Implementation notes

The hypotheses of the source statement — quasi-compactness and quasi-separatedness of `X`,
perfectness of `G`, generation of `D_QCoh(𝒪_X)` by `G`, and quasi-coherence of the cohomology
of `E` — are carried on all three results although no clause equivalence uses them: they are
the hypotheses under which the source asserts the equivalence of all its conditions, and the
two conditions of each result are the source's conditions.

Generation of `D_QCoh(𝒪_X)` by `G` is spelled out as the hypothesis that an object of
`D(𝒪_X)` with quasi-coherent cohomology receiving only zero morphisms from the shifts of `G`
is zero. Vanishing of a group of morphisms is `Subsingleton`, and `D⁺(ℤ)` is the object
property `plus` of the canonical t-structure on `D(AddCommGrpCat)`.

The duality identification is used in the form in which the library has it: the canonical map
`M ⊗^L_{𝒪_X} G^∨ ⟶ RSheafHom(G, M)` of Stacks 08I1 is taken as a hypothesis to be invertible,
at every shift `M = E⟦i⟧` of `E`, exactly as
`Stacks.SheafOfModules.bijective_derivedTensorDualGlobalSectionsMap` takes it. Perfectness of
`G` is what the source uses to get that invertibility, and the library does not yet have that
implication; so it is an explicit hypothesis rather than a consequence of `_hG`.

The remaining clause equivalences of the source are not available: identifying
`H^i(RHom_X(G, E))` with `Ext^i(G, E)` needs the derived internal Hom to commute with the shift
in its second variable, and the derived internal Hom of this development has no such
compatibility.

## References

* [Stacks Project, Proposition 36.40.6 (Tag 0GEQ)](https://stacks.math.columbia.edu/tag/0GEQ)
* [Stacks Project, Tag 05RU](https://stacks.math.columbia.edu/tag/05RU)
* [Stacks Project, Tag 08DQ](https://stacks.math.columbia.edu/tag/08DQ)
* [Stacks Project, Tag 08I1](https://stacks.math.columbia.edu/tag/08I1)
* [Stacks Project, Tag 08DK](https://stacks.math.columbia.edu/tag/08DK)
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

/-- **Stacks 0GEQ, conditions (2) and (3).** For a perfect generator `G` of `D_QCoh(𝒪_X)` on a
quasi-compact, quasi-separated scheme and an object `E` of `D_QCoh(𝒪_X)`, the groups
`Hom_{D(𝒪_X)}(G⟦-i⟧, E)` vanish for `i ≪ 0` exactly when the groups `Ext^i_X(G, E)` do.

The two conditions hold of the same `i`, because `⟦-i⟧` is left adjoint to `⟦i⟧`. -/
@[stacks 0GEQ "conditions (2) and (3): eventual vanishing of Hom(G[-i], E) and of Ext^i(G, E)"]
theorem eventually_subsingleton_shiftedHom_iff_ext
    (_hqc : CompactSpace X) (_hqs : QuasiSeparatedSpace X)
    (G E : DerivedCategory (StructureSheafModules X.sheaf))
    (_hG : (ringedSite X.sheaf).IsPerfect G)
    (_hgen : ∀ K : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
          (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent) →
        (∀ (n : ℤ) (f : G⟦n⟧ ⟶ K), f = 0) → IsZero K)
    (_hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj E).IsQuasicoherent) :
    (∃ N : ℤ, ∀ i ≤ N, Subsingleton (G⟦-i⟧ ⟶ E)) ↔
      ∃ N : ℤ, ∀ i ≤ N, Subsingleton (DerivedCategory.Ext G E i) := by
  have key : ∀ i : ℤ, Subsingleton (G⟦-i⟧ ⟶ E) ↔ Subsingleton (DerivedCategory.Ext G E i) :=
    fun i => (((shiftEquiv' (DerivedCategory (StructureSheafModules X.sheaf)) (-i) i
      (by omega)).toAdjunction.homEquiv G E)).subsingleton_congr
  exact exists_congr fun _ => forall₂_congr fun i _ => key i

variable
  [(Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive]
  [∀ A, ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} X.sheaf)) (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor X.sheaf) (ComplexShape.up ℤ)]

/-- **Stacks 0GEQ, conditions (5) and (6).** For a perfect generator `G` of `D_QCoh(𝒪_X)` on a
quasi-compact, quasi-separated scheme and an object `E` of `D_QCoh(𝒪_X)`, the cohomology groups
`H^i(X, G^∨ ⊗^L_{𝒪_X} E)` vanish for `i ≪ 0` exactly when `RΓ(X, G^∨ ⊗^L_{𝒪_X} E)` lies in
`D⁺(ℤ)`.

This is the description of the bounded-below derived category by its cohomology, applied to the
single object `RΓ(X, G^∨ ⊗^L_{𝒪_X} E)` of `D(AddCommGrpCat)`. -/
@[stacks 0GEQ "conditions (5) and (6): eventual vanishing of H^i(X, G^vee ⊗ E) and membership
of RGamma(X, G^vee ⊗ E) in D^+(Z)"]
theorem plus_derivedGlobalSections_derivedTensor_derivedDual_iff
    (_hqc : CompactSpace X) (_hqs : QuasiSeparatedSpace X)
    (G E : DerivedCategory (StructureSheafModules X.sheaf))
    (_hG : (ringedSite X.sheaf).IsPerfect G)
    (_hgen : ∀ K : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
          (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent) →
        (∀ (n : ℤ) (f : G⟦n⟧ ⟶ K), f = 0) → IsZero K)
    (_hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj E).IsQuasicoherent) :
    (DerivedCategory.TStructure.t (C := AddCommGrpCat.{u})).plus
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
          (((derivedTensor X.sheaf).obj E).obj (derivedDual X.sheaf G))) ↔
      ∃ N : ℤ, ∀ n ≤ N, IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
          (((derivedTensor X.sheaf).obj E).obj (derivedDual X.sheaf G)))) :=
  DerivedCategory.plus_iff _

private theorem subsingleton_ext_iff_isZero_homology_aux
    (G E : DerivedCategory (StructureSheafModules X.sheaf)) (i : ℤ)
    (h : IsIso (derivedTensorDualToSheafHom X.sheaf G (E⟦i⟧))) :
    Subsingleton (DerivedCategory.Ext G E i) ↔
      IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
          (((derivedTensor X.sheaf).obj E).obj (derivedDual X.sheaf G)))) := by
  have hbij : Function.Bijective (derivedTensorDualGlobalSectionsMap X.sheaf G (E⟦i⟧)) := by
    let z := (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).mapIso
      ((derivedModuleGlobalSections (ringedSite X.sheaf)).mapIso
        (@asIso _ _ _ _ (derivedTensorDualToSheafHom X.sheaf G (E⟦i⟧)) h))
    have hz : Function.Bijective (fun w => z.hom w) := ConcreteCategory.bijective_of_isIso z.hom
    exact (derivedSheafHomGlobalSectionsEquiv X.sheaf G (E⟦i⟧)).bijective.comp hz
  letI : ((derivedTensor X.sheaf).flip.obj (derivedDual X.sheaf G)).CommShift ℤ :=
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
  have hshift : Function.Bijective (fun w => shiftIso.hom w) :=
    ConcreteCategory.bijective_of_isIso shiftIso.hom
  rw [AddCommGrpCat.isZero_iff_subsingleton]
  exact (((Equiv.ofBijective _ hbij).symm).trans (Equiv.ofBijective _ hshift)).subsingleton_congr

/-- **Stacks 0GEQ, conditions (3) and (5).** For a perfect generator `G` of `D_QCoh(𝒪_X)` on a
quasi-compact, quasi-separated scheme and an object `E` of `D_QCoh(𝒪_X)`, the groups
`Ext^i_X(G, E)` vanish for `i ≪ 0` exactly when the cohomology groups
`H^i(X, G^∨ ⊗^L_{𝒪_X} E)` do, granted that the canonical map
`E⟦i⟧ ⊗^L_{𝒪_X} G^∨ ⟶ RSheafHom(G, E⟦i⟧)` of Stacks 08I1 is invertible for every `i`.

The two conditions hold of the same `i`, because `Ext^i_X(G, E)` and `H^i(X, G^∨ ⊗^L_{𝒪_X} E)`
are the same group: Stacks 08DQ identifies `H⁰(X, M ⊗^L_{𝒪_X} G^∨)` with `Hom(G, M)`, and at
`M = E⟦i⟧` the left side becomes `H^i(X, G^∨ ⊗^L_{𝒪_X} E)` because tensoring with `G^∨` and
`RΓ(X, -)` are triangulated, hence commute with the shift, and `H⁰` of an `i`-fold shift is
`H^i`. -/
@[stacks 0GEQ "conditions (3) and (5): eventual vanishing of Ext^i(G, E) and of
H^i(X, G^vee ⊗ E), granted the 08I1 map E[i] ⊗ G^vee ⟶ RSheafHom(G, E[i]) invertible for all i"]
theorem eventually_subsingleton_ext_iff_isZero_homology_derivedTensorDual
    (_hqc : CompactSpace X) (_hqs : QuasiSeparatedSpace X)
    (G E : DerivedCategory (StructureSheafModules X.sheaf))
    (_hG : (ringedSite X.sheaf).IsPerfect G)
    (_hgen : ∀ K : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
          (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent) →
        (∀ (n : ℤ) (f : G⟦n⟧ ⟶ K), f = 0) → IsZero K)
    (_hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj E).IsQuasicoherent)
    (h08I1 : ∀ i : ℤ, IsIso (derivedTensorDualToSheafHom X.sheaf G (E⟦i⟧))) :
    (∃ N : ℤ, ∀ i ≤ N, Subsingleton (DerivedCategory.Ext G E i)) ↔
      ∃ N : ℤ, ∀ n ≤ N, IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).obj
        ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
          (((derivedTensor X.sheaf).obj E).obj (derivedDual X.sheaf G)))) :=
  exists_congr fun _ => forall₂_congr fun i _ =>
    subsingleton_ext_iff_isZero_homology_aux G E i (h08I1 i)

end Stacks.SheafOfModules

end
