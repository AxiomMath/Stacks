module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.DerivedQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleTorAmplitudeOnQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeFinitePresentationInstances
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.TorAmplitudeChartSliceTests
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.SiteEquivalenceDerivedTensorTransport
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.ModuleEquivalenceTransport
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 08IL: Tor amplitude on a quasi-separated algebraic space is tested on `QCoh(𝒪_X)`

Let `X` be a quasi-separated algebraic space, `E` an object of `D_QCoh(𝒪_X)` and `a ≤ b`.  Then
`E` has Tor amplitude in `[a, b]` if and only if `Hⁱ(E ⊗^L_{𝒪_X} ℱ) = 0` for `i ∉ [a, b]` and
every quasi-coherent `𝒪_X`-module `ℱ`.  The implication (1) ⟹ (2) is
`AlgebraicGeometry.Space.hasTorAmplitudeOnQuasicoherent_of_hasTorAmplitude`; this file proves the
converse and registers the equivalence.

## Main results

* `AlgebraicGeometry.Space.hasTorAmplitude_over_of_isZero_sliceTensor`: on the slice of the small
  étale site at an étale chart with affine scheme, the quasi-coherent Tor tests of an object with
  quasi-coherent cohomology give Tor amplitude.  This is the representable case.
* `AlgebraicGeometry.Space.hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent_ofSlices`: the
  converse of Stacks 08IL, given derived categories on the slices at the hom universe of `X`'s.
* `AlgebraicGeometry.Space.hasTorAmplitude_iff_hasTorAmplitudeOnQuasicoherent`: **Stacks 08IL.**

## Implementation notes

The source's proof is followed.

1. *Restriction to an affine chart.*  For an étale chart `W` with affine scheme, condition (2) on
   `X` gives the quasi-coherent Tor tests of `E|_W` on the slice `X_étale/W`, by Stacks 03M9 and
   0HAP: `AlgebraicGeometry.Space.isZero_homology_sliceTensor_of_hasTorAmplitudeOnQuasicoherent`.
2. *The representable case.*  The slice is the small étale site of the scheme `W₀` of the chart
   (Stacks 04M0 after 03ED, `AlgebraicGeometry.Space.chartSchemeIdentification`, with the two
   structure sheaves equal on the nose).  Reindexing along it carries the tensor product to the
   tensor product (Stacks 01CU) and quasi-coherence to quasi-coherence (Stacks 03DM), so the Tor
   tests cross it by
   `Stacks.SheafOfModules.DerivedTensorProduct.isZero_homology_tensor_single_iff_of_equivalence`,
   and on the small étale site of the affine scheme `W₀` the quasi-coherent tests give Tor
   amplitude: `AlgebraicGeometry.SmallEtale.hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent`
   (Stacks 071Q, 08H8, 08EA, 08HF).
3. *Descent.*  The affine charts cover the final object
   (`AlgebraicGeometry.Space.SmallEtale.coversTop_affineCharts`), and Tor amplitude in a fixed
   interval descends along a covering family
   (`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_coversTop`).

**The derived category of `X`.**  The statement is made, like the implication (1) ⟹ (2), for an
arbitrary `HasDerivedCategory.{d}` instance on `Mod(𝒪_X)` and an arbitrary derived tensor product
datum `T`.  The descent of step 3 compares `X` with its slices at the *same* hom universe `d`, and
for an arbitrary `d` no derived category of the slices exists to compare with.  So the converse is
first proved with the derived categories of the slices given
(`hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent_ofSlices`), then applied at
`CategoryTheory.HasDerivedCategory.standard` everywhere, and carried to the given instance along
the identity of `Mod(𝒪_X)`: two derived categories of one abelian category, with two derived
tensor product data, see the same Tor tests
(`Stacks.SheafOfModules.DerivedTensorProduct.isZero_homology_tensor_single_iff_of_equivalence` at
the identity equivalence).

**The hypothesis `a ≤ b`** of the source is not assumed: no step uses it, as in the scheme
case Stacks 08EA (`AlgebraicGeometry.hasTorAmplitude_iff_hasTorAmplitudeOnQuasicoherent`), so the
statement holds for every pair `a, b` and in particular for `a ≤ b`.

**Quasi-separatedness** is the absolute notion of Stacks 03BS,
`AlgebraicGeometry.Space.IsAbsolutelyQuasiSeparated`, which is what "quasi-separated algebraic
space" means in the source; it is used only to make the charts `W → X` quasi-compact.

## References

* [Stacks Project, Lemma 75.13.8 (Tag 08IL)](https://stacks.math.columbia.edu/tag/08IL)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 0HAP](https://stacks.math.columbia.edu/tag/0HAP)
* [Stacks Project, Tag 071Q](https://stacks.math.columbia.edu/tag/071Q)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
* [Stacks Project, Tag 08EA](https://stacks.math.columbia.edu/tag/08EA)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

-- `moduleSheavesAbelian` is stated at a module universe `max u v w` which elaboration cannot
-- solve for at the small étale sites here; the abelian structure meant is Mathlib's.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

open Stacks.SheafOfModules (DerivedTensorProduct)
open Stacks.SheafOfModules.DerivedTensorProduct Stacks.SheafOfModules

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The representable case, on the slice at an affine chart -/

/-- Every object of a derived category of modules is isomorphic to a K-flat complex. -/
private theorem exists_isKFlat_iso {X : RingedSite.{u + 1, u, u}}
    [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} X.O).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} X.O).obj M).Additive]
    [∀ (K L : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ),
      HomologicalComplex.HasMapBifunctor K L
        (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u} X.O) (ComplexShape.up ℤ)]
    [HasDerivedCategory.{d} (RingedSite.Modules.{u + 1, u, u} X)]
    (E : RingedSite.DerivedModules.{u + 1, u, u, d} X) :
    ∃ (K : CochainComplex (RingedSite.Modules.{u + 1, u, u} X) ℤ) (_ : IsKFlat X.O K),
      Nonempty (DerivedCategory.Q.obj K ≅ E) := by
  obtain ⟨K, pr, hK, hqi⟩ := Stacks.SheafOfModules.KFlatResolution.exists_kFlat_quasiIso_ofSize
    X.O (DerivedCategory.Q.objPreimage E)
  have _ := hqi
  exact ⟨K, hK, ⟨asIso (DerivedCategory.Q.map pr) ≪≫ DerivedCategory.Q.objObjPreimageIso E⟩⟩

section Slice

-- `ResolutionByExtensionsByZero.instAbelian` names the abelian structure of `Mod(𝒪)` a second
-- way, which is compared with Mathlib's by unfolding, and that does not terminate in budget on
-- the small étale site of a scheme.
attribute [-instance] Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian

variable (X : AlgebraicSpaces B S hS) (W : (smallEtaleRingedSite B S hS X.1 X.2).C)
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    ((smallEtaleRingedSite B S hS X.1 X.2).over W).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    ((smallEtaleRingedSite B S hS X.1 X.2).over W).O).obj M).Additive]
  [∀ (K L : CochainComplex
      (RingedSite.Modules.{u + 1, u, u} ((smallEtaleRingedSite B S hS X.1 X.2).over W)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((smallEtaleRingedSite B S hS X.1 X.2).over W).O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d}
    (RingedSite.Modules.{u + 1, u, u} ((smallEtaleRingedSite B S hS X.1 X.2).over W))]

/-- The inverse of the chart-scheme identification is a dense subsite inclusion, for the topology
of the small étale ringed site of the chart's scheme. -/
instance isDenseSubsite_chartSchemeIdentification_inverse' :
    (chartSchemeIdentification B S hS X W).inverse.IsDenseSubsite
      ((smallEtaleRingedSite B S hS X.1 X.2).over W).J
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS X W))
        (chartOverObject B S hS X W).left.property).J :=
  isDenseSubsite_chartSchemeIdentification_inverse B S hS X W

/-- **The representable case of Stacks 08IL, on the slice at an affine chart.**  Let `W` be an
étale chart of the algebraic space `X` whose scheme is affine, and let `E_W` be an object of the
derived category of the slice `X_étale/W` with quasi-coherent cohomology sheaves.  If
`Hⁱ(E_W ⊗^L_{T_W} 𝒢[0]) = 0` for every `i ∉ [a, b]` and every quasi-coherent module `𝒢` on the
slice, then `E_W` has Tor amplitude in `[a, b]`.

The slice is the small étale site of the affine scheme `W₀` of the chart, by the chart-scheme
identification, along which tensor products, quasi-coherence and so Tor tests transport; on the
small étale site of `W₀` this is
`AlgebraicGeometry.SmallEtale.hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent`. -/
theorem hasTorAmplitude_over_of_isZero_sliceTensor (hW : IsAffine (chartScheme W))
    (TW : DerivedTensorProduct.{u + 1, u, u, d} ((smallEtaleRingedSite B S hS X.1 X.2).over W))
    (EW : RingedSite.DerivedModules.{u + 1, u, u, d} ((smallEtaleRingedSite B S hS X.1 X.2).over W))
    (a b : ℤ)
    (hqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (RingedSite.Modules.{u + 1, u, u}
      ((smallEtaleRingedSite B S hS X.1 X.2).over W)) n).obj EW).IsQuasicoherentOnSite)
    (htest : ∀ G : RingedSite.Modules.{u + 1, u, u} ((smallEtaleRingedSite B S hS X.1 X.2).over W),
      G.IsQuasicoherentOnSite → ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj
          ((TW.tensor.obj EW).obj ((DerivedCategory.singleFunctor _ 0).obj G)))) :
    HasTorAmplitude TW EW a b := by
  have := hasSheafify_chartSlice B S hS X W
  have := hasWeakSheafify_chartSlice B S hS X W
  have := wEqualsLocallyBijective_chartSlice B S hS X W
  have := isDenseSubsite_chartSchemeIdentification_inverse' B S hS X W
  let : HasDerivedCategory.{u + 1} (RingedSite.Modules
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS X W))
        (chartOverObject B S hS X W).left.property)) :=
    HasDerivedCategory.standard _
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS X W)) := hW
  let Φ : RingedSite.Modules.{u + 1, u, u} ((smallEtaleRingedSite B S hS X.1 X.2).over W) ≌
      RingedSite.Modules (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS X W))
        (chartOverObject B S hS X W).left.property) :=
    SiteEquivalenceDerivedTensor.reindexMod (chartSchemeTopology B S hS X W)
      (chartSchemeIdentification B S hS X W) ((smallEtaleRingedSite B S hS X.1 X.2).over W).O
  have : Φ.functor.Additive := Φ.functor.additive_of_preserves_binary_products
  let ε : ∀ a b : RingedSite.Modules ((smallEtaleRingedSite B S hS X.1 X.2).over W),
      Φ.functor.obj
          (((Tensor.sheafTensor ((smallEtaleRingedSite B S hS X.1 X.2).over W).O).obj a).obj b) ≅
        ((Tensor.sheafTensor
          (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS X W))
            (chartOverObject B S hS X W).left.property).O).obj (Φ.functor.obj a)).obj
          (Φ.functor.obj b) := fun a b =>
    TensorPower.whiskerTensorSheafIso (J' := chartSchemeTopology B S hS X W)
      ((smallEtaleRingedSite B S hS X.1 X.2).over W).O.val
      (Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over W).O).cond
      (chartSchemeIdentification B S hS X W).functor a b
  have hε₁ : ∀ {a a' : RingedSite.Modules ((smallEtaleRingedSite B S hS X.1 X.2).over W)}
      (f : a ⟶ a') (b : RingedSite.Modules ((smallEtaleRingedSite B S hS X.1 X.2).over W)),
      Φ.functor.map
          (((Tensor.sheafTensor ((smallEtaleRingedSite B S hS X.1 X.2).over W).O).map f).app b) ≫
          (ε a' b).hom =
        (ε a b).hom ≫ ((Tensor.sheafTensor
          (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS X W))
            (chartOverObject B S hS X W).left.property).O).map (Φ.functor.map f)).app
          (Φ.functor.obj b) :=
    fun f b => SiteEquivalenceDerivedTensor.reindexTensorIso_naturality_left
      (chartSchemeTopology B S hS X W) (chartSchemeIdentification B S hS X W)
      ((smallEtaleRingedSite B S hS X.1 X.2).over W).O f b
  have hε₂ : ∀ (a : RingedSite.Modules ((smallEtaleRingedSite B S hS X.1 X.2).over W))
      {b b' : RingedSite.Modules ((smallEtaleRingedSite B S hS X.1 X.2).over W)} (g : b ⟶ b'),
      Φ.functor.map
          (((Tensor.sheafTensor ((smallEtaleRingedSite B S hS X.1 X.2).over W).O).obj a).map g) ≫
          (ε a b').hom =
        (ε a b).hom ≫ ((Tensor.sheafTensor
          (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS X W))
            (chartOverObject B S hS X W).left.property).O).obj (Φ.functor.obj a)).map
          (Φ.functor.map g) :=
    fun a _ _ g => SiteEquivalenceDerivedTensor.reindexTensorIso_naturality_right
      (chartSchemeTopology B S hS X W) (chartSchemeIdentification B S hS X W)
      ((smallEtaleRingedSite B S hS X.1 X.2).over W).O a g
  -- Quasi-coherence crosses the identification in both directions.
  have hΦ : ∀ M : RingedSite.Modules ((smallEtaleRingedSite B S hS X.1 X.2).over W),
      (Φ.functor.obj M).IsQuasicoherentOnSite ↔ M.IsQuasicoherentOnSite := fun M =>
    isQuasicoherentOnSite_reindex_iff (chartSchemeIdentification B S hS X W)
      (Tensor.ringSheaf ((smallEtaleRingedSite B S hS X.1 X.2).over W).O) M
  let TC : DerivedTensorProduct.{u + 1, u, u, u + 1}
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS X W))
        (chartOverObject B S hS X W).left.property) :=
    canonicalDerivedTensorProduct
      (_root_.AlgebraicGeometry.smallEtaleRingedSite (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS X W))
        (chartOverObject B S hS X W).left.property)
  obtain ⟨K, hK, ⟨eK⟩⟩ := exists_isKFlat_iso EW
  refine (hasTorAmplitude_iff_of_equivalence Φ ε hε₁ hε₂ TW TC K hK EW eK a b).2 ?_
  refine _root_.AlgebraicGeometry.SmallEtale.hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS X W))
    (chartOverObject B S hS X W).left.property TC (Φ.functor.mapDerivedCategory.obj EW) a b
    (fun n => ?_) (fun G hG i hi => ?_)
  · exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((Functor.mapDerivedCategoryHomologyIso Φ.functor n).app EW).symm ((hΦ _).2 (hqc n))
  · have hG' : (Φ.inverse.obj G).IsQuasicoherentOnSite :=
      (hΦ _).1 (SheafOfModules.IsQuasicoherentOnSite.of_iso (Φ.counitIso.app G).symm hG)
    exact ((isZero_homology_tensor_single_iff_of_equivalence Φ ε hε₁ hε₂ TW TC K hK EW eK
      (Φ.inverse.obj G) i).1 (htest _ hG' i hi)).of_iso
        ((DerivedCategory.homologyFunctor _ i).mapIso ((TC.tensor.obj _).mapIso
          ((DerivedCategory.singleFunctor _ 0).mapIso (Φ.counitIso.app G))).symm)

end Slice

/-! ### The converse of Stacks 08IL -/

section Converse

/-- Local equivalences on a slice of the small étale site of an algebraic space are the locally
bijective morphisms, at the spelling of the ringed site's topology. -/
instance wEqualsLocallyBijective_smallEtaleRingedSite_J_over (X : AlgebraicSpaces B S hS) :
    ∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
      ((smallEtaleRingedSite B S hS X.1 X.2).J.over U).WEqualsLocallyBijective
        AddCommGrpCat.{u} := by
  change ∀ U : SmallEtale B S hS X.1,
    ((SmallEtale.topology B S hS X.1).over U).WEqualsLocallyBijective AddCommGrpCat.{u}
  infer_instance

variable {X : AlgebraicSpaces B S hS}
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS X.1 X.2).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS X.1 X.2).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS X.1 X.2).O)
      (ComplexShape.up ℤ)]
  [hT₁ : ∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
    (Stacks.SheafOfModules.Tensor.sheafTensor.{max (u + 1) u, u, u, u, u}
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).O).Additive]
  [hT₂ : ∀ (U : (smallEtaleRingedSite B S hS X.1 X.2).C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{max (u + 1) u, u, u, u, u}
      ((smallEtaleRingedSite B S hS X.1 X.2).over U).O).obj M).Additive]
  [hT₃ : ∀ (U : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (K L : CochainComplex
      (RingedSite.Modules.{max (u + 1) u, u, u} ((smallEtaleRingedSite B S hS X.1 X.2).over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{max (u + 1) u, u, u, u, u}
        ((smallEtaleRingedSite B S hS X.1 X.2).over U).O)
      (ComplexShape.up ℤ)]
  [hDX : HasDerivedCategory.{d} (Modules.{u, u} B S hS X.1 X.2)]
  [hSliceDerived : ∀ U : (smallEtaleRingedSite B S hS X.1 X.2).C,
    HasDerivedCategory.{d}
      (RingedSite.Modules.{max (u + 1) u, u, u} ((smallEtaleRingedSite B S hS X.1 X.2).over U))]

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  RingedSite.sliceHasDerivedCategory Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS X.1 X.2).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS X.1 X.2).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS X.1 X.2).O)
      (ComplexShape.up ℤ)] hT₁ hT₂ hT₃ in
/-- Restriction to a slice preserves quasi-coherence of the cohomology sheaves: restriction is
exact, so it commutes with cohomology, and the restriction of a quasi-coherent module is
quasi-coherent. -/
theorem isQuasicoherentOnSite_homology_derivedRestriction
    (E : RingedSite.DerivedModules.{u + 1, u, u, d} (smallEtaleRingedSite B S hS X.1 X.2))
    (hqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) n).obj
      E).IsQuasicoherentOnSite)
    (W : (smallEtaleRingedSite B S hS X.1 X.2).C) (n : ℤ) :
    ((DerivedCategory.homologyFunctor
      (RingedSite.Modules.{u + 1, u, u} ((smallEtaleRingedSite B S hS X.1 X.2).over W)) n).obj
        ((RingedSite.derivedRestriction.{u + 1, u, u, d} _ W).obj E)).IsQuasicoherentOnSite := by
  let : Abelian (SheafOfModules.{u}
      ((Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).over W)) :=
    inferInstanceAs (Abelian (RingedSite.Modules ((smallEtaleRingedSite B S hS X.1 X.2).over W)))
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((Functor.mapDerivedCategoryHomologyIso
      (SheafOfModules.overFunctor (Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
        W) n).app E).symm
    (Stacks.SheafOfModules.isQuasicoherent_over _ (hqc n) W)

/-- **The converse of Stacks 08IL, given derived categories of the slices.**  Let `X` be a
quasi-separated algebraic space and `E` an object of `D(𝒪_X)` with quasi-coherent cohomology
sheaves.  If `Hⁱ(E ⊗^L_T ℱ[0]) = 0` for every `i ∉ [a, b]` and every quasi-coherent
`𝒪_X`-module `ℱ`, then `E` has Tor amplitude in `[a, b]`.

The affine charts cover the final object; on each, the quasi-coherent tests restrict
(`AlgebraicGeometry.Space.isZero_homology_sliceTensor_of_hasTorAmplitudeOnQuasicoherent`) and
give Tor amplitude (`AlgebraicGeometry.Space.hasTorAmplitude_over_of_isZero_sliceTensor`), and
Tor amplitude descends along the covering
(`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_coversTop`).  The derived
categories of the slices, at the hom universe of the derived category of `X`, are what the
descent compares with. -/
theorem hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent_ofSlices
    (hZ : B.Contains (⊤_ Scheme.{u})) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (T : DerivedTensorProduct.{u + 1, u, u, d} (smallEtaleRingedSite B S hS X.1 X.2))
    (E : RingedSite.DerivedModules.{u + 1, u, u, d} (smallEtaleRingedSite B S hS X.1 X.2))
    (a b : ℤ)
    (hqc : ∀ n : ℤ, ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) n).obj
      E).IsQuasicoherentOnSite)
    (h : HasTorAmplitudeOnQuasicoherent B S hS X.2 T E a b) :
    HasTorAmplitude T E a b := by
  have := smallEtaleRingedSite_essentiallySmall B S hS X.1 X.2
  refine hasTorAmplitude_of_coversTop (smallEtaleRingedSite B S hS X.1 X.2) T
    (fun U => canonicalDerivedTensorProduct _) (SmallEtale.coversTop_affineCharts B S hS X.1)
    E a b fun W => ?_
  have := hT₁ W.1
  have := hT₂ W.1
  have := hT₃ W.1
  let := hSliceDerived W.1
  refine hasTorAmplitude_over_of_isZero_sliceTensor B S hS X W.1 W.2 _ _ a b (fun n => ?_)
    (fun G hG i hi => isZero_homology_sliceTensor_of_hasTorAmplitudeOnQuasicoherent B S hS hZ
      hqs T E a b h W.1 W.2 _ G hG i hi)
  exact isQuasicoherentOnSite_homology_derivedRestriction B S hS E hqc W.1 n

end Converse

/-! ### Stacks 08IL -/

section Registered

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
  [instD : HasDerivedCategory.{d} (Modules.{u, u} B S hS F hF)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS F hF).O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
    (smallEtaleRingedSite B S hS F hF).O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules.{u, u} B S hS F hF) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        (smallEtaleRingedSite B S hS F hF).O)
      (ComplexShape.up ℤ)]

/-- **Stacks 08IL.**  Let `X` be a quasi-separated algebraic space over `S`, let `E` be an object
of `D_QCoh(𝒪_X)`, and let `T` be a derived tensor product on `D(𝒪_X)`.  The following are
equivalent:

1. `E` has Tor amplitude in `[a, b]`;
2. `Hⁱ(E ⊗^L_{𝒪_X} ℱ) = 0` for `i ∉ [a, b]` and every quasi-coherent `𝒪_X`-module `ℱ`.

The source assumes `a ≤ b`; neither direction uses it, as in the scheme case Stacks 08EA, so it is
not assumed.  (1) ⟹ (2) is
`AlgebraicGeometry.Space.hasTorAmplitudeOnQuasicoherent_of_hasTorAmplitude`.  For (2) ⟹ (1) the
converse `AlgebraicGeometry.Space.hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent_ofSlices` is
applied at the standard derived categories of `X` and of its slices, and carried to the given
derived category of `X` and the given datum `T` along the identity of `Mod(𝒪_X)`, which carries
Tor tests to Tor tests
(`Stacks.SheafOfModules.DerivedTensorProduct.isZero_homology_tensor_single_iff_of_equivalence`). -/
@[stacks 08IL]
theorem hasTorAmplitude_iff_hasTorAmplitudeOnQuasicoherent
    (hZ : B.Contains (⊤_ Scheme.{u})) (hqs : IsAbsolutelyQuasiSeparated B S hS hZ F)
    (T : DerivedTensorProduct.{u + 1, u, u, d} (smallEtaleRingedSite B S hS F hF))
    (E : RingedSite.DerivedModules.{u + 1, u, u, d} (smallEtaleRingedSite B S hS F hF))
    (hE : DerivedCategoryB.derivedCategoryB
      (_root_.SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) E)
    (a b : ℤ) :
    HasTorAmplitude T E a b ↔ HasTorAmplitudeOnQuasicoherent B S hS hF T E a b := by
  refine ⟨hasTorAmplitudeOnQuasicoherent_of_hasTorAmplitude B S hS hF T E a b, fun h => ?_⟩
  obtain ⟨K, hK, ⟨eK⟩⟩ := exists_isKFlat_iso E
  let : ∀ U : (smallEtaleRingedSite B S hS F hF).C,
      HasDerivedCategory.{u + 1}
        (RingedSite.Modules.{u + 1, u, u} ((smallEtaleRingedSite B S hS F hF).over U)) :=
    fun _ => HasDerivedCategory.standard _
  let e : Modules.{u, u} B S hS F hF ≌ Modules.{u, u} B S hS F hF :=
    CategoryTheory.Equivalence.refl
  let ε : ∀ a b : RingedSite.Modules (smallEtaleRingedSite B S hS F hF),
      e.functor.obj (((Tensor.sheafTensor (smallEtaleRingedSite B S hS F hF).O).obj a).obj b) ≅
        ((Tensor.sheafTensor (smallEtaleRingedSite B S hS F hF).O).obj (e.functor.obj a)).obj
          (e.functor.obj b) := fun _ _ => Iso.refl _
  have hε₁ : ∀ {a a' : RingedSite.Modules (smallEtaleRingedSite B S hS F hF)} (f : a ⟶ a')
      (b : RingedSite.Modules (smallEtaleRingedSite B S hS F hF)),
      e.functor.map (((Tensor.sheafTensor (smallEtaleRingedSite B S hS F hF).O).map f).app b) ≫
          (ε a' b).hom =
        (ε a b).hom ≫ ((Tensor.sheafTensor (smallEtaleRingedSite B S hS F hF).O).map
          (e.functor.map f)).app (e.functor.obj b) :=
    fun _ _ => (Category.comp_id _).trans (Category.id_comp _).symm
  have hε₂ : ∀ (a : RingedSite.Modules (smallEtaleRingedSite B S hS F hF))
      {b b' : RingedSite.Modules (smallEtaleRingedSite B S hS F hF)} (g : b ⟶ b'),
      e.functor.map (((Tensor.sheafTensor (smallEtaleRingedSite B S hS F hF).O).obj a).map g) ≫
          (ε a b').hom =
        (ε a b).hom ≫ ((Tensor.sheafTensor (smallEtaleRingedSite B S hS F hF).O).obj
          (e.functor.obj a)).map (e.functor.map g) :=
    fun _ _ _ _ => (Category.comp_id _).trans (Category.id_comp _).symm
  let std : HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS F hF) :=
    HasDerivedCategory.standard _
  let T₀ := @canonicalDerivedTensorProduct.{u + 1, u, u + 1} (smallEtaleRingedSite B S hS F hF)
    _ _ _ _ _ std
  have : e.functor.Additive := e.functor.additive_of_preserves_binary_products
  refine (hasTorAmplitude_iff_of_equivalence (hDX := instD) (hDX' := std) e ε hε₁ hε₂ T T₀
    K hK E eK a b).2 ?_
  refine hasTorAmplitude_of_hasTorAmplitudeOnQuasicoherent_ofSlices B S hS (X := ⟨F, hF⟩)
    (hDX := std) hZ hqs T₀ _ a b (fun n => ?_) (fun M hM i hi => ?_)
  · exact SheafOfModules.IsQuasicoherentOnSite.of_iso
      (homologyMapDerivedCategoryIso (hDX := instD) (hDX' := std) e E n).symm (hE n)
  · exact (isZero_homology_tensor_single_iff_of_equivalence (hDX := instD) (hDX' := std)
      e ε hε₁ hε₂ T T₀ K hK E eK M i).1 (h M hM i hi)

end Registered

end AlgebraicGeometry.Space


end
