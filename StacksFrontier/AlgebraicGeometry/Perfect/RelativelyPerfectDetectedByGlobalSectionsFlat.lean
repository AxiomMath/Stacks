module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectDetectedByGlobalSections
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.ExtFinitenessGlobalSectionsForget
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeAbsolute
public import StacksFrontier.Homology.Perfect.Saturation
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualTensorHom

/-!
# Perfectness of the derived global sections of the perfect twists: the flat case

Companion of `StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectDetectedByGlobalSections`.
For `X` separated, of finite presentation and flat over a ring `A`, and `K ∈ D_QCoh(𝒪_X)` whose
perfect twists have perfect derived global sections:

* `AlgebraicGeometry.eventually_subsingleton_ext_of_derivedGlobalSections_isPerfect_of_flat`: the
  vanishing of `Ext^i_X(G, K)` and of `Hom(G⟦-i⟧, K)` for `i ≪ 0` against a perfect generator `G`,
  with quasi-compactness and quasi-separatedness of `X` derived from the morphism to `Spec(A)` and
  the invertibility of the map of Stacks 08I1 derived from perfectness of `G`
  (`Stacks.SheafOfModules.isIso_derivedTensorDualToSheafHom_of_isPerfect`, Stacks 08DQ);
* `AlgebraicGeometry.exists_isPerfect_mapDerivedCategory_of_isPerfect_derivedGlobalSectionsOver`:
  the `A`-linear perfectness hypothesis implies the `D(Ab)`-valued one.

Both are inputs of Stacks 0GET itself, which is
`AlgebraicGeometry.Scheme.Hom.isRelativelyPerfect_of_isPerfect_derivedGlobalSectionsOver_tensor`
in `StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFromGlobalSections`.

## References

* [Stacks Project, Tag 0GET](https://stacks.math.columbia.edu/tag/0GET)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.ModuleSections
open Stacks.SheafOfModules

namespace AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

section Objective

variable {A : Type u} [CommRing A] {X : Scheme.{u}}
  [HasSheafify (Opens.grothendieckTopology X.toPresheafedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X.toPresheafedSpace.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [(Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} X.sheaf)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
      (ComplexShape.up ℤ)]

/-- **The vanishing against a perfect generator, in the flat case.** The base statement
`AlgebraicGeometry.eventually_subsingleton_ext_of_derivedGlobalSections_isPerfect` with its
quasi-compactness and quasi-separatedness binders derived from the morphism to `Spec(A)` and its
Stacks 08I1 binder derived from perfectness of `G` by Stacks 08DQ. -/
public theorem eventually_subsingleton_ext_of_derivedGlobalSections_isPerfect_of_flat
    [∀ V : Opens X.toPresheafedSpace.carrier,
      HasSheafify ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V)
        AddCommGrpCat.{u}]
    [∀ V : Opens X.toPresheafedSpace.carrier,
      ((Opens.grothendieckTopology X.toPresheafedSpace.carrier).over V).WEqualsLocallyBijective
        AddCommGrpCat.{u}]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsSeparated f] [QuasiCompact f] [Flat f]
    [LocallyOfFinitePresentation f]
    (G K : DerivedCategory (StructureSheafModules X.sheaf))
    (hG : (ringedSite X.sheaf).IsPerfect G)
    (hGdual : (ringedSite X.sheaf).IsPerfect (derivedDual X.sheaf G))
    (hgen : ∀ L : DerivedCategory (StructureSheafModules X.sheaf),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor
          (StructureSheafModules X.sheaf) i).obj L).IsQuasicoherent) →
        (∀ (n : ℤ) (g : G⟦n⟧ ⟶ L), g = 0) → IsZero L)
    (hK : ∀ i : ℤ, ((DerivedCategory.homologyFunctor
      (StructureSheafModules X.sheaf) i).obj K).IsQuasicoherent)
    (hperf : ∀ E : DerivedCategory (StructureSheafModules X.sheaf),
      (ringedSite X.sheaf).IsPerfect E →
        ∃ M : DerivedCategory (ModuleCat.{u} A), StacksDraft.Perfect.IsPerfect M ∧
          Nonempty ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj
              (((derivedTensor X.sheaf).obj K).obj E) ≅
            (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapDerivedCategory.obj M)) :
    (∃ N : ℤ, ∀ i ≤ N, Subsingleton (DerivedCategory.Ext G K i)) ∧
      ∃ N : ℤ, ∀ i ≤ N, Subsingleton (G⟦-i⟧ ⟶ K) :=
  eventually_subsingleton_ext_of_derivedGlobalSections_isPerfect f
    (QuasiCompact.compactSpace_of_compactSpace f) (quasiSeparatedSpace_of_quasiSeparated f)
    G K hG hGdual hgen hK
    (fun i => isIso_derivedTensorDualToSheafHom_of_isPerfect X.sheaf G (K⟦i⟧) hG) hperf

omit [(Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Tensor.ringSheaf.{u, u, u} X.sheaf)) ℤ),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Tensor.sheafTensor.{u, u, u, u, u} X.sheaf)
      (ComplexShape.up ℤ)] in
/-- **The `A`-linear perfectness hypothesis implies the one the vanishing above takes.** If the
`A`-linear derived global sections `RΓ(X, T)` of an object `T` of `D(𝒪_X)` are a perfect object
of `D(A)`, then there is a perfect object of `D(A)` whose underlying object of `D(Ab)` is
isomorphic to the abelian-group-valued derived global sections of `T` — namely `RΓ(X, T)`
itself, the isomorphism being
`Stacks.AlgebraicGeometry.ProperSupportCoherent.derivedGlobalSectionsOverForgetIso`.

So the hypothesis of Stacks 0GET, stated in `D(A)`, implies the `D(Ab)`-valued hypothesis of
`AlgebraicGeometry.eventually_subsingleton_ext_of_derivedGlobalSections_isPerfect`. -/
public theorem exists_isPerfect_mapDerivedCategory_of_isPerfect_derivedGlobalSectionsOver
    (f : X ⟶ Spec (CommRingCat.of A))
    (T : DerivedCategory (StructureSheafModules X.sheaf))
    (h : StacksDraft.Perfect.IsPerfect ((derivedGlobalSectionsOver f).obj T)) :
    ∃ M : DerivedCategory (ModuleCat.{u} A), StacksDraft.Perfect.IsPerfect M ∧
      Nonempty ((derivedModuleGlobalSections (ringedSite X.sheaf)).obj T ≅
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapDerivedCategory.obj M) :=
  ⟨_, h, ⟨((Stacks.AlgebraicGeometry.ProperSupportCoherent.derivedGlobalSectionsOverForgetIso
    f).app T).symm⟩⟩

end Objective

end AlgebraicGeometry

end
