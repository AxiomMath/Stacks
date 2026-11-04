module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentTensorComplex
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeFinitePresentationInstances
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleBinaryProducts
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExtensionByZeroTensorOfEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.SiteEquivalenceQuasicoherentTensorComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.Restriction
import StacksCore.Tactic.StacksAttribute

/-!
# `D_QCoh(𝒪_X)` is closed under the derived tensor product

Let `X` be an algebraic space over a scheme `S`.  Stacks 08F5 asserts that for objects `K`, `L`
of `D_QCoh(𝒪_X)` the derived tensor product `K ⊗^𝐋_{𝒪_X} L` lies in `D_QCoh(𝒪_X)`.  This file
proves it for arbitrary, unbounded `K` and `L`, and for an arbitrary derived tensor product
datum on the small étale ringed site of `X`.

## The proof

It is the source's.  Representing `K` by a K-flat complex `P` (Stacks 06YS) and `L` by any
complex `L'`, the K-flat comparison of the derived tensor product identifies `K ⊗^𝐋 L` with
`Tot(P ⊗ L')`, so it suffices to show that `Tot(P ⊗ L')` has quasi-coherent cohomology sheaves.

1. *Étale localization.*  Quasi-coherence of a module on `X_étale` is tested on the slices of
   `X_étale` at its étale charts, `AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_forall_over`
   (Stacks 03M0).  Restriction to a slice is exact, commutes with the total tensor complex
   (`AlgebraicGeometry.RingedSite.tensorComplexOverIso`), keeps `P` K-flat (Stacks 0E8K,
   `Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall.kFlat_restrictionComplex`) and keeps
   the cohomology sheaves quasi-coherent; this is the source's `φ^*(K ⊗^𝐋 L) = φ^*K ⊗^𝐋 φ^*L`
   together with Stacks 08F2.
2. *From the chart to the scheme.*  The slice of `X_étale` at a chart is the small étale site of
   the scheme underlying the chart, with the same structure sheaf
   (`AlgebraicGeometry.Space.chartSchemeIdentification`, Stacks 04M0 after 03ED), and the
   assertion transports along that equivalence of ringed sites by
   `SiteEquivalenceDerivedTensor.isQuasicoherentOnSite_homology_tensorComplex_of_reindex` in
   `Stacks.SheafOfModules`.
3. *The case of a scheme.*  On the small étale site of a scheme it is
   `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_homology_tensorComplex`, which goes
   through the comparison with the Zariski site, Stacks 071Q, and Derived Categories of Schemes,
   Lemma 36.3.9 (Stacks 08DX).

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_tensorComplex_chart`: the assertion on
  the slice of `X_étale` at an étale chart.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_tensorComplex`: the assertion on
  `X_étale`, for complexes.
* `AlgebraicGeometry.Space.derivedQuasicoherent_derivedTensor`: **Stacks 08F5**, for an
  arbitrary derived tensor product datum on the small étale ringed site.
* `AlgebraicGeometry.Space.derivedQuasicoherent_canonicalDerivedTensor`: the same for the
  canonical derived tensor product of Stacks 06YU.

## References

* [Stacks Project, Tag 08F5](https://stacks.math.columbia.edu/tag/08F5)
* [Stacks Project, Tag 08F2](https://stacks.math.columbia.edu/tag/08F2)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
* [Stacks Project, Tag 0E8K](https://stacks.math.columbia.edu/tag/0E8K)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 08DX](https://stacks.math.columbia.edu/tag/08DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The slice of `X_étale` at an étale chart -/

section Chart

variable (U : AlgebraicSpaces B S hS) (W : (smallEtaleRingedSite B S hS U.1 U.2).C)

/-- The slice of the small étale ringed site of `U` at the chart `W`. -/
abbrev chartSlice : RingedSite.{u + 1, u, u} := (smallEtaleRingedSite B S hS U.1 U.2).over W

/-- Local bijectivity of the weak equivalences on the slice at a chart. -/
instance wEqualsLocallyBijective_chartSlice' :
    (chartSlice B S hS U W).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  wEqualsLocallyBijective_chartSlice B S hS U W

/-- **The case of a chart.**  On the slice of the small étale site of an algebraic space at an
étale chart, the total tensor complex of a K-flat complex and an arbitrary complex, both with
quasi-coherent cohomology sheaves, has quasi-coherent cohomology sheaves. -/
theorem isQuasicoherentOnSite_homology_tensorComplex_chart
    (P L : CochainComplex (RingedSite.Modules.{u + 1, u, u} (chartSlice B S hS U W)) ℤ)
    (hP : Stacks.SheafOfModules.IsKFlat (chartSlice B S hS U W).O P)
    (hPq : ∀ n : ℤ, ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).obj
      P).IsQuasicoherentOnSite)
    (hLq : ∀ n : ℤ, ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).obj
      L).IsQuasicoherentOnSite)
    (n : ℤ) :
    ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).obj
      (((Stacks.SheafOfModules.Tensor.tensorComplex (chartSlice B S hS U W).O).obj P).obj
        L)).IsQuasicoherentOnSite :=
  have : HasSheafify ((smallEtaleRingedSite B S hS U.1 U.2).over W).J AddCommGrpCat.{u} :=
    hasSheafify_chartSlice B S hS U W
  have : ((smallEtaleRingedSite B S hS U.1 U.2).over W).J.WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
    wEqualsLocallyBijective_chartSlice B S hS U W
  open Stacks.SheafOfModules.SiteEquivalenceDerivedTensor in
  isQuasicoherentOnSite_homology_tensorComplex_of_reindex
    (chartSchemeTopology B S hS U W) (chartSchemeIdentification B S hS U W)
    (hdense := isDenseSubsite_chartSchemeIdentification_inverse B S hS U W)
    (chartSlice B S hS U W).O
    (fun P' L' hP' hP'q hL'q m =>
      SmallEtale.isQuasicoherentOnSite_homology_tensorComplex (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj (chartOverObject B S hS U W))
        (chartOverObject B S hS U W).left.property P' L' hP' hP'q hL'q m)
    P L hP hPq hLq n

end Chart

/-! ### The small étale site of an algebraic space -/

section Space

variable (U : AlgebraicSpaces B S hS)

open Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall (restriction restrictionComplex)

/-- Restriction to a slice is left exact (Stacks 04IX). -/
local instance preservesFiniteLimits_restriction (W : (smallEtaleRingedSite B S hS U.1 U.2).C) :
    PreservesFiniteLimits (restriction (smallEtaleRingedSite B S hS U.1 U.2) W) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits W

/-- Restriction to a slice is right exact (Stacks 04IX). -/
local instance preservesFiniteColimits_restriction (W : (smallEtaleRingedSite B S hS U.1 U.2).C) :
    PreservesFiniteColimits (restriction (smallEtaleRingedSite B S hS U.1 U.2) W) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits W

/-- The small étale site of an algebraic space is essentially small. -/
local instance essentiallySmall_smallEtaleRingedSite :
    EssentiallySmall.{u} (smallEtaleRingedSite B S hS U.1 U.2).C :=
  smallEtaleRingedSite_essentiallySmall B S hS U.1 U.2

/-- **The total tensor complex of a K-flat complex and an arbitrary complex with quasi-coherent
cohomology sheaves on `X_étale` has quasi-coherent cohomology sheaves.**

Quasi-coherence is tested on the slices at the étale charts (Stacks 03M0); restriction to a slice
is exact, commutes with the total tensor complex and keeps `P` K-flat (Stacks 0E8K), and on a
slice the assertion is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_tensorComplex_chart`. -/
theorem isQuasicoherentOnSite_homology_tensorComplex
    (P L : CochainComplex (Modules.{u, u} B S hS U.1 U.2) ℤ)
    (hP : Stacks.SheafOfModules.IsKFlat (smallEtaleRingedSite B S hS U.1 U.2).O P)
    (hPq : ∀ n : ℤ, ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).obj
      P).IsQuasicoherentOnSite)
    (hLq : ∀ n : ℤ, ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).obj
      L).IsQuasicoherentOnSite)
    (n : ℤ) :
    ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).obj
      (((Stacks.SheafOfModules.Tensor.tensorComplex
        (smallEtaleRingedSite B S hS U.1 U.2).O).obj P).obj L)).IsQuasicoherentOnSite := by
  refine (isQuasicoherentOnSite_iff_forall_over B S hS U.1 U.2 _).2 fun W => ?_
  let X := smallEtaleRingedSite B S hS U.1 U.2
  have hres : ∀ (M : CochainComplex (Modules.{u, u} B S hS U.1 U.2) ℤ) (m : ℤ),
      ((restriction X W).obj ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) m).obj
        M)) ≅
        (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) m).obj
          ((restrictionComplex X W).obj M) := fun M m =>
    ((StacksDraft.PseudoCoherence.mapHomologicalComplexCompHomologyFunctorIso
      (restriction X W) m).app M).symm
  have hq : ∀ (M : CochainComplex (Modules.{u, u} B S hS U.1 U.2) ℤ),
      (∀ m : ℤ, ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) m).obj
        M).IsQuasicoherentOnSite) →
      ∀ m : ℤ, ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) m).obj
        ((restrictionComplex X W).obj M)).IsQuasicoherentOnSite := fun M hM m =>
    SheafOfModules.IsQuasicoherentOnSite.of_iso (hres M m)
      (Stacks.SheafOfModules.isQuasicoherent_over _ (hM m) W)
  have key := isQuasicoherentOnSite_homology_tensorComplex_chart B S hS U W
    ((restrictionComplex X W).obj P) ((restrictionComplex X W).obj L)
    (Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall.kFlat_restrictionComplex X W P hP)
    (hq P hPq) (hq L hLq) n
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((hres _ n) ≪≫ (HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).mapIso
      (RingedSite.tensorComplexOverIso X W P L)).symm key

end Space

/-! ### Stacks 08F5 -/

section Derived

attribute [local instance] HasDerivedCategory.standard

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)

/-- **Stacks 08F5.**  Let `X` be an algebraic space over a scheme `S`.  For objects `K`, `L` of
`D_QCoh(𝒪_X)` the derived tensor product `K ⊗^𝐋_{𝒪_X} L` is in `D_QCoh(𝒪_X)`.

Here `𝒪_X`-modules are the sheaves of modules on the small étale ringed site of `X`,
`D_QCoh(𝒪_X)` is `AlgebraicGeometry.Space.QuasicoherentDerivedCategory` of Stacks 071X, the full
subcategory of the unbounded derived category on the objects with quasi-coherent cohomology
sheaves, and `⊗^𝐋_{𝒪_X}` is an arbitrary derived tensor product datum `T` on that ringed site —
for instance the canonical one, `Stacks.SheafOfModules.canonicalDerivedTensorProduct` of
Stacks 06YU.  `K` and `L` are arbitrary objects of `D_QCoh(𝒪_X)`, with no boundedness.

The proof represents `K` by a K-flat complex `P` (Stacks 06YS) and `L` by any complex `L'`, so
that `K ⊗^𝐋 L ≅ Q(Tot(P ⊗ L'))` by the K-flat comparison of `T`, and concludes by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_homology_tensorComplex`; see the module docstring. -/
@[stacks 08F5]
theorem derivedQuasicoherent_derivedTensor
    (T : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS F hF))
    (K L : QuasicoherentDerivedCategory.{u, u} B S hS F hF) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
      ((T.tensor.obj K.obj).obj L.obj) := by
  intro n
  obtain ⟨P, p, hP, hqis⟩ := Stacks.SheafOfModules.exists_kFlat_quasiIso
    (smallEtaleRingedSite B S hS F hF) (DerivedCategory.Q.objPreimage K.obj)
  have hiso := (DerivedCategory.isIso_Q_map_iff_quasiIso
    (C := RingedSite.Modules.{u + 1, u, u} (smallEtaleRingedSite B S hS F hF)) p).2 hqis
  let eK : DerivedCategory.Q.obj P ≅ K.obj :=
    @asIso _ _ _ _ (DerivedCategory.Q.map p) hiso ≪≫ DerivedCategory.Q.objObjPreimageIso K.obj
  let L' := DerivedCategory.Q.objPreimage L.obj
  let eL : DerivedCategory.Q.obj L' ≅ L.obj := DerivedCategory.Q.objObjPreimageIso L.obj
  have hq : ∀ (M : CochainComplex (RingedSite.Modules.{u + 1, u, u}
        (smallEtaleRingedSite B S hS F hF)) ℤ)
      (E : QuasicoherentDerivedCategory.{u, u} B S hS F hF), (DerivedCategory.Q.obj M ≅ E.obj) →
      ∀ m : ℤ, ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) m).obj
        M).IsQuasicoherentOnSite := fun M E e m =>
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((DerivedCategory.homologyFunctor _ m).mapIso e.symm ≪≫
        (DerivedCategory.homologyFunctorFactors _ m).app M) (E.property m)
  have key := isQuasicoherentOnSite_homology_tensorComplex B S hS ⟨F, hF⟩ P L' hP
    (hq P K eK) (hq L' L eL) n
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (((DerivedCategory.homologyFunctorFactors _ n).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ n).mapIso
        ((T.comparisonLeft P L' hP).symm ≪≫ (T.tensor.mapIso eK).app _ ≪≫
          (T.tensor.obj K.obj).mapIso eL)) key

/-- Stacks 08F5 for the canonical derived tensor product
`Stacks.SheafOfModules.canonicalDerivedTensorProduct` of Stacks 06YU on the small étale ringed
site of `X`: `AlgebraicGeometry.Space.derivedQuasicoherent_derivedTensor` at that datum. -/
theorem derivedQuasicoherent_canonicalDerivedTensor
    (K L : QuasicoherentDerivedCategory.{u, u} B S hS F hF) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
      (((Stacks.SheafOfModules.canonicalDerivedTensorProduct.{u + 1, u, u + 1}
        (smallEtaleRingedSite B S hS F hF)).tensor.obj K.obj).obj L.obj) :=
  derivedQuasicoherent_derivedTensor B S hS hF _ K L

end Derived

end AlgebraicGeometry.Space

end
