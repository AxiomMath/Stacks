module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.SiteEquivalenceDerivedTensorTransport
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentModuleUniverse
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.Defs

/-!
# Quasi-coherent cohomology of total tensor complexes along an equivalence of ringed sites

Let `e : C' ≌ C` be an equivalence of sites and `𝒪` a sheaf of commutative rings on `C`, and let
`Φ` be the reindexing of `𝒪`-modules along `e`.  This file transports along `Φ` the assertion

> for every K-flat complex `P` and every complex `L` of modules, both with quasi-coherent
> cohomology sheaves, the total tensor complex `Tot(P ⊗ L)` has quasi-coherent cohomology sheaves

from the ringed site `(C', 𝒪|_{C'})` to `(C, 𝒪)`.  Every ingredient is a transport along an
equivalence that is already in the tree:

* `Φ` carries K-flat complexes to K-flat complexes,
  `CochainComplex.KFlatBifunctor.kFlat_map_of_equivalence`;
* `Φ` carries `Tot(P ⊗ L)` to `Tot(ΦP ⊗ ΦL)`, `CochainComplex.KFlatBifunctor.transportComplexIso`,
  through the tensor comparison of Stacks 01CU,
  `Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso`;
* `Φ` is exact, so it commutes with cohomology;
* `Φ` preserves and reflects quasi-coherence, Stacks 03DM for the clause 03DL (6),
  `Stacks.SheafOfModules.isQuasicoherentOnSite_reindex` and
  `Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex'`.

## Main results

* `isQuasicoherentOnSite_homology_tensorComplex_of_reindex`: if `Tot(P ⊗ L)` has quasi-coherent
  cohomology sheaves for all such `P` and `L` on `(C', 𝒪|_{C'})`, then the same holds on `(C, 𝒪)`.

## References

* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.KFlatBifunctor

universe w v u

namespace Stacks.SheafOfModules.SiteEquivalenceDerivedTensor

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {J : GrothendieckTopology C} (J' : GrothendieckTopology C')
  (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  [e.functor.IsCocontinuous J' J] [hdense : e.inverse.IsDenseSubsite J J']
  (O : Sheaf J CommRingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J' AddCommGrpCat.{w}] [J'.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [(Tensor.sheafTensor.{u, v, w} O).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, v, w} O).obj M).Additive]
  [∀ (K L : CochainComplex (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Tensor.sheafTensor.{u, v, w} O) (ComplexShape.up ℤ)]
  [(Tensor.sheafTensor.{u, v, w} (reindexCommRingGeneral J' e O)).Additive]
  [∀ M, ((Tensor.sheafTensor.{u, v, w} (reindexCommRingGeneral J' e O)).obj M).Additive]
  [∀ (K L : CochainComplex
      (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} (reindexCommRingGeneral J' e O))) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Tensor.sheafTensor.{u, v, w} (reindexCommRingGeneral J' e O)) (ComplexShape.up ℤ)]

/-- **Quasi-coherent cohomology of total tensor complexes transports along an equivalence of
ringed sites.**  Suppose that on `(C', 𝒪|_{C'})` the total tensor complex of a K-flat complex and
an arbitrary complex, both with quasi-coherent cohomology sheaves, has quasi-coherent cohomology
sheaves.  Then the same holds on `(C, 𝒪)`.

The reindexing `Φ` along `e` keeps `P` K-flat, carries `Tot(P ⊗ L)` to `Tot(ΦP ⊗ ΦL)`, commutes
with cohomology, and preserves and reflects quasi-coherence. -/
theorem isQuasicoherentOnSite_homology_tensorComplex_of_reindex
    (h : ∀ P L : CochainComplex
        (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} (reindexCommRingGeneral J' e O))) ℤ,
      IsKFlat (reindexCommRingGeneral J' e O) P →
      (∀ n : ℤ, ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).obj
        P).IsQuasicoherentOnSite) →
      (∀ n : ℤ, ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).obj
        L).IsQuasicoherentOnSite) →
      ∀ n : ℤ, ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).obj
        (((Tensor.tensorComplex (reindexCommRingGeneral J' e O)).obj P).obj
          L)).IsQuasicoherentOnSite)
    (P L : CochainComplex (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O)) ℤ)
    (hP : IsKFlat O P)
    (hPq : ∀ n : ℤ, ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).obj
      P).IsQuasicoherentOnSite)
    (hLq : ∀ n : ℤ, ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).obj
      L).IsQuasicoherentOnSite)
    (n : ℤ) :
    ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).obj
      (((Tensor.tensorComplex O).obj P).obj L)).IsQuasicoherentOnSite := by
  let Φ := (reindexMod J' e O).functor
  let ε := TensorPower.whiskerTensorSheafIso (J' := J') O.val (Tensor.ringSheaf.{u, v, w} O).cond
    e.functor
  have hε₁ := fun {a a'} (f : a ⟶ a') N => reindexTensorIso_naturality_left J' e O f N
  have hε₂ := fun M {b b'} (g : b ⟶ b') => reindexTensorIso_naturality_right J' e O M g
  let := fun K L => hasTotal_mapBicomplex_of_equivalence (Tensor.sheafTensor.{u, v, w} O)
    (Tensor.sheafTensor.{u, v, w} (reindexCommRingGeneral J' e O)) (reindexMod J' e O)
    ε hε₁ hε₂ K L
  have hKFlat : IsKFlat (reindexCommRingGeneral J' e O)
      ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
    kFlat_map_of_equivalence (Tensor.sheafTensor.{u, v, w} O)
      (Tensor.sheafTensor.{u, v, w} (reindexCommRingGeneral J' e O)) (reindexMod J' e O)
      ε hε₁ hε₂ P hP
  have hq : ∀ (M : CochainComplex (_root_.SheafOfModules.{w} (Tensor.ringSheaf.{u, v, w} O)) ℤ),
      (∀ n : ℤ, ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).obj
        M).IsQuasicoherentOnSite) →
      ∀ n : ℤ, ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).obj
        ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)).IsQuasicoherentOnSite :=
    fun M hM n =>
      have := hM n
      _root_.SheafOfModules.IsQuasicoherentOnSite.of_iso
        ((StacksDraft.PseudoCoherence.mapHomologicalComplexCompHomologyFunctorIso Φ n).app M).symm
        (isQuasicoherentOnSite_reindex e (Tensor.ringSheaf.{u, v, w} O) _)
  have key := h _ _ hKFlat (hq P hPq) (hq L hLq) n
  have hΦ : ((Φ.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).obj
        (((Tensor.tensorComplex O).obj P).obj L)).IsQuasicoherentOnSite :=
    _root_.SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso
        (transportComplexIso (Tensor.sheafTensor.{u, v, w} O)
          (Tensor.sheafTensor.{u, v, w} (reindexCommRingGeneral J' e O)) Φ Φ Φ
          ε hε₁ hε₂ P L).symm) key
  exact isQuasicoherentOnSite_of_reindex' e (Tensor.ringSheaf.{u, v, w} O) _
    (_root_.SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((StacksDraft.PseudoCoherence.mapHomologicalComplexCompHomologyFunctorIso Φ n).app _) hΦ)

end Stacks.SheafOfModules.SiteEquivalenceDerivedTensor

end
