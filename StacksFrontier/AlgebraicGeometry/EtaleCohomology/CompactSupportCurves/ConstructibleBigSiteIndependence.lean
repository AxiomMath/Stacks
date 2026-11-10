module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantWeakSerre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.WeakSerre.FiniteTypeLocallyConstant
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Support.AffineLifting
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BoundedSiteBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.CoefficientHypotheses
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ImmersionCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LocallyClosedStratum
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage

/-!
# Constructibility of sheaves of `Λ`-modules does not depend on the big étale site

`Stacks.EtaleCohomology.IsConstructibleEtaleModule` reads a sheaf of `Λ`-modules on Mathlib's
small étale site of `X` on the small étale site of Tag 021B of one chosen big étale site,
`AlgebraicGeometry.BigEtaleSite.containing X`. This file shows that any other big étale site
containing `X` gives the same notion, and deduces that extension by zero along a quasi-compact
open immersion into a quasi-compact quasi-separated scheme preserves constructibility
([Stacks, Tag 03S8], for an open immersion), in the model `EtaleModules Λ X`.

## Main definitions

* `Stacks.EtaleCohomology.etaleModuleToBoundedSiteInverseImageIso`: inverse image along a
  morphism `f : T ⟶ S` of a big étale site commutes with the passage from Mathlib's small étale
  site to the small étale site of Tag 021B.
* `AlgebraicGeometry.ConstructibleStratification.changeSite`: a constructible stratification
  read in a second big étale site containing the same scheme, with the same strata.

## Main results

* `Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_sheafPullback_etaleModuleToBoundedSite_iff`:
  local constancy of finite type of an inverse image is the same in the two models.
* `Stacks.EtaleCohomology.isConstructibleModuleSheaf_etaleModuleToBoundedSite_iff`: two big étale
  sites containing `X` give the same constructible sheaves of `Λ`-modules.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_iff_isConstructibleModuleSheaf`: the
  predicate `IsConstructibleEtaleModule` can be read in any big étale site containing `X`.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_etaleModuleExtensionByZero`: extension by
  zero along a quasi-compact open immersion into a quasi-compact quasi-separated scheme preserves
  constructibility.

## Implementation notes

A constructible stratification of an affine open of `X` in one big étale site has strata immersed
in `X`; an immersed scheme is a closed subscheme of an open subscheme, so it lies below every
cardinal bound `X` lies below, and the same strata form a stratification in any other big étale
site containing `X`. On each stratum the two inverse images correspond under the equivalences of
`AlgebraicGeometry.SmallEtale.sheafEquiv`
(`AlgebraicGeometry.SmallEtale.sheafEquivPullbackBaseChangeIso`), and local constancy of finite
type is the same in the two models
(`Stacks.EtaleCohomology.isFiniteTypeLocallyConstantModuleSheaf_etaleModuleToBoundedSite_iff`).

For extension by zero along `ι : U ⟶ X`, `X` is covered by the two constructible locally closed
pieces `ι(U)` and its closed complement, Tag 09YR: the inverse image of `ι_! ℱ` to `U` is `ℱ`
and its inverse image to the complement is zero.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 03S8](https://stacks.math.columbia.edu/tag/03S8)
* [Stacks Project, Tag 09YR](https://stacks.math.columbia.edu/tag/09YR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

/-- The source of an immersion into an object of `Sch_κ` is an object of `Sch_κ`: it is a closed
subscheme of an open subscheme of the target. -/
theorem AlgebraicGeometry.Scheme.size_lt_of_isImmersion {κ : Cardinal.{u}} {P X : Scheme.{u}}
    (g : P ⟶ X) [IsImmersion g] (h : X.size < κ) : P.size < κ :=
  Scheme.size_lt_of_isClosedImmersion g.liftCoborder
    (Scheme.size_lt_of_isOpenImmersion g.coborderRange.ι h)

namespace AlgebraicGeometry.ConstructibleStratification

variable {B : BigEtaleSite.{u}} {X : Scheme.{u}} {hX : B.Contains X} {U : X.Opens}

/-- A constructible stratification in the big étale site `B` read in a second big étale site
`B'` containing `X`: the strata are the same schemes, which lie in `B'` because they are immersed
in `X`, with the same immersions. -/
def changeSite (s : ConstructibleStratification B (B.obj X hX) U) (B' : BigEtaleSite.{u})
    (hX' : B'.Contains X) : ConstructibleStratification B' (B'.obj X hX') U where
  n := s.n
  piece i := B'.obj (B.inclusion.obj (s.piece i))
    (have := s.isImmersion i; Scheme.size_lt_of_isImmersion (B.inclusion.map (s.inclusion i)) hX')
  inclusion i := B'.inclusion.preimage (B.inclusion.map (s.inclusion i))
  isImmersion i := by rw [Functor.map_preimage]; exact s.isImmersion i
  contained i := by rw [Functor.map_preimage]; exact s.contained i
  constructible i := by rw [Functor.map_preimage]; exact s.constructible i
  pairwise_disjoint i j hij := by
    rw [Functor.map_preimage, Functor.map_preimage]; exact s.pairwise_disjoint i j hij
  covers := by simp only [Functor.map_preimage]; exact s.covers

/-- The immersions of the strata of `s.changeSite B' hX'` are, as morphisms of schemes, the
immersions of the strata of `s`. -/
@[simp]
theorem map_changeSite_inclusion (s : ConstructibleStratification B (B.obj X hX) U)
    (B' : BigEtaleSite.{u}) (hX' : B'.Contains X) (i : Fin s.n) :
    B'.inclusion.map ((s.changeSite B' hX').inclusion i) = B.inclusion.map (s.inclusion i) :=
  Functor.map_preimage _ _

end AlgebraicGeometry.ConstructibleStratification

namespace Stacks.EtaleCohomology

attribute [local instance] SmallEtale.isRightAdjointPushforward_moduleCat
  SmallEtale.hasWeakSheafifyOver_moduleCat moduleCat_hasLimitsOfSize

variable (Λ : Type r) [CommRing Λ]

/-- **Inverse image commutes with the passage to the small étale site of Tag 021B.** For a
morphism `f : T ⟶ S` of a big étale site `B` and a sheaf `G` of `Λ`-modules on Mathlib's small
étale site of `S`, the inverse image along `f` on the sites of Tag 021B of the transport of `G` is
the transport of the inverse image of `G` along the underlying morphism of schemes. -/
def etaleModuleToBoundedSiteInverseImageIso (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S)
    (G : EtaleModules.{u, r} Λ S.obj) :
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPullback (ModuleCat.{max (u + 1) r} Λ)
        (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)).obj
        ((etaleModuleToBoundedSite Λ B S.property).obj G) ≅
      (etaleModuleToBoundedSite Λ B T.property).obj
        ((etaleModuleInverseImage.{u, r} Λ (B.inclusion.map f)).obj G) :=
  let ES := SmallEtale.sheafEquiv B S.obj S.property (ModuleCat.{max (u + 1) r} Λ)
  let ET := SmallEtale.sheafEquiv B T.obj T.property (ModuleCat.{max (u + 1) r} Λ)
  let e := SmallEtale.sheafEquivPullbackBaseChangeIso B f (ModuleCat.{max (u + 1) r} Λ)
    (etaleModuleInverseImageAdj.{u, r} Λ (B.inclusion.map f))
    (Functor.sheafAdjunctionContinuous (AlgebraicGeometry.smallEtaleBaseChange B f)
      (ModuleCat.{max (u + 1) r} Λ) (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property))
  ET.unitIso.app _ ≪≫ ET.inverse.mapIso (e.app (ES.inverse.obj G)).symm ≪≫
    ET.inverse.mapIso ((etaleModuleInverseImage.{u, r} Λ (B.inclusion.map f)).mapIso
      (ES.counitIso.app G))

/-- **Local constancy of finite type of an inverse image is the same in the two models.** -/
theorem isFiniteTypeLocallyConstant_sheafPullback_etaleModuleToBoundedSite_iff
    (B : BigEtaleSite.{u}) {S T : B.Scheme} (f : T ⟶ S) (G : EtaleModules.{u, r} Λ S.obj) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ (SmallEtale.topology B T.obj T.property)
        (((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPullback
          (ModuleCat.{max (u + 1) r} Λ) (SmallEtale.topology B S.obj S.property)
          (SmallEtale.topology B T.obj T.property)).obj
          ((etaleModuleToBoundedSite Λ B S.property).obj G)) ↔
      Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r}
        T.obj.smallEtaleTopology Λ
          ((etaleModuleInverseImage.{u, r} Λ (B.inclusion.map f)).obj G) := by
  rw [← isFiniteTypeLocallyConstantModuleSheaf_etaleModuleToBoundedSite_iff Λ B T.property]
  exact ⟨fun h ↦ Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ
      (etaleModuleToBoundedSiteInverseImageIso Λ B f G) h,
    fun h ↦ Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ
      (etaleModuleToBoundedSiteInverseImageIso Λ B f G).symm h⟩

/-- One direction of `isConstructibleModuleSheaf_etaleModuleToBoundedSite_iff`. -/
private theorem isConstructibleModuleSheaf_etaleModuleToBoundedSite_of
    {X : Scheme.{u}} (B B' : BigEtaleSite.{u}) (hX : B.Contains X) (hX' : B'.Contains X)
    (G : EtaleModules.{u, r} Λ X)
    (h : IsConstructibleModuleSheaf B (B.obj X hX) Λ ((etaleModuleToBoundedSite Λ B hX).obj G)) :
    IsConstructibleModuleSheaf B' (B'.obj X hX') Λ
      ((etaleModuleToBoundedSite Λ B' hX').obj G) := by
  intro U
  obtain ⟨s, hs⟩ := h U
  refine ⟨s.changeSite B' hX', fun i ↦ ?_⟩
  have hi := (isFiniteTypeLocallyConstant_sheafPullback_etaleModuleToBoundedSite_iff Λ B
    (s.inclusion i) G).1 (hs i)
  refine (isFiniteTypeLocallyConstant_sheafPullback_etaleModuleToBoundedSite_iff Λ B'
    ((s.changeSite B' hX').inclusion i) G).2 ?_
  rw [← ConstructibleStratification.map_changeSite_inclusion s B' hX' i] at hi
  exact hi

/-- **Constructibility does not depend on the big étale site.** For two big étale sites `B` and
`B'` containing `X`, a sheaf of `Λ`-modules on Mathlib's small étale site of `X` is constructible
on the small étale site of Tag 021B of `B` exactly when it is on that of `B'`. -/
theorem isConstructibleModuleSheaf_etaleModuleToBoundedSite_iff {X : Scheme.{u}}
    (B B' : BigEtaleSite.{u}) (hX : B.Contains X) (hX' : B'.Contains X)
    (G : EtaleModules.{u, r} Λ X) :
    IsConstructibleModuleSheaf B (B.obj X hX) Λ ((etaleModuleToBoundedSite Λ B hX).obj G) ↔
      IsConstructibleModuleSheaf B' (B'.obj X hX') Λ
        ((etaleModuleToBoundedSite Λ B' hX').obj G) :=
  ⟨isConstructibleModuleSheaf_etaleModuleToBoundedSite_of Λ B B' hX hX' G,
    isConstructibleModuleSheaf_etaleModuleToBoundedSite_of Λ B' B hX' hX G⟩

/-- **`IsConstructibleEtaleModule` can be read in any big étale site containing `X`.** -/
theorem isConstructibleEtaleModule_iff_isConstructibleModuleSheaf {X : Scheme.{u}}
    (B : BigEtaleSite.{u}) (hX : B.Contains X) (F : EtaleModules.{u, r} Λ X) :
    IsConstructibleEtaleModule Λ F ↔
      IsConstructibleModuleSheaf B (B.obj X hX) Λ ((etaleModuleToBoundedSite Λ B hX).obj F) :=
  isConstructibleModuleSheaf_etaleModuleToBoundedSite_iff Λ _ B _ hX F

/-- **Extension by zero along an open immersion preserves constructibility** ([Stacks, Tag 03S8]
for an open immersion), in the model `EtaleModules Λ X`. Let `Λ` be Noetherian, `X` quasi-compact
and quasi-separated, and `ι : U ⟶ X` an open immersion with `U` quasi-compact. If `ℱ` is a
constructible sheaf of `Λ`-modules on `U_étale`, then `ι_! ℱ` is constructible on `X_étale`.

The image of `ι` and its closed complement are constructible locally closed pieces covering `X`,
so Tag 09YR applies: the inverse image of `ι_! ℱ` to `U` is `ℱ`, and its inverse image to the
complement is zero. -/
theorem isConstructibleEtaleModule_etaleModuleExtensionByZero [IsNoetherianRing Λ]
    {U X : Scheme.{u}} (ι : U ⟶ X) [IsOpenImmersion ι] [CompactSpace U] [CompactSpace X]
    [QuasiSeparatedSpace X] (F : EtaleModules.{u, r} Λ U) (hF : IsConstructibleEtaleModule Λ F) :
    IsConstructibleEtaleModule Λ ((etaleModuleExtensionByZero.{u, r} Λ ι).obj F) := by
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  have hU : B.Contains U := Scheme.size_lt_of_isOpenImmersion ι hX
  let Xb := B.obj X hX
  let Ub := B.obj U hU
  let ιb : Ub ⟶ Xb := B.inclusion.preimage ι
  have hιb : B.inclusion.map ιb = ι := Functor.map_preimage _ _
  have hopen : IsOpen (Set.range ι.base) := ι.isOpenEmbedding.isOpen_range
  have hCl : IsLocallyClosed (Set.range ι.base)ᶜ := hopen.isClosed_compl.isLocallyClosed
  let Cb := B.locallyClosedObj Xb hCl
  let cb : Cb ⟶ Xb := B.locallyClosedHom Xb hCl
  have hcr : Set.range (B.inclusion.map cb).base = (Set.range ι.base)ᶜ :=
    B.range_locallyClosedHom Xb hCl
  have hcons : Topology.IsConstructible (Set.range ι.base) :=
    (isCompact_range ι.base.hom.continuous).isConstructible hopen
  have : CompactSpace Xb.obj := ‹CompactSpace X›
  have : QuasiSeparatedSpace Xb.obj := ‹QuasiSeparatedSpace X›
  have : HasSheafify (SmallEtale.topology B Cb.obj Cb.property) (ModuleCat.{max (u + 1) r} Λ) :=
    SmallEtale.hasSheafify_moduleCat.{u, r, max (u + 1) r} B Cb Λ
  refine (isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B hX _).2 ?_
  refine isConstructibleModuleSheaf_of_constructible_immersion_cover B Xb Λ _
    (fun b : Bool ↦ match b with | true => Ub | false => Cb)
    (fun b : Bool ↦ match b with | true => ιb | false => cb) ?_ ?_ ?_ ?_
  · intro b
    cases b
    · exact B.isImmersion_map_locallyClosedHom Xb hCl
    · change IsImmersion (B.inclusion.map ιb)
      rw [hιb]
      infer_instance
  · intro b
    cases b
    · change Topology.IsConstructible (Set.range (B.inclusion.map cb).base)
      rw [hcr]
      exact hcons.compl
    · change Topology.IsConstructible (Set.range (B.inclusion.map ιb).base)
      rw [hιb]
      exact hcons
  · refine (Set.eq_univ_of_forall fun x ↦ ?_).symm
    by_cases hx : x ∈ Set.range ι.base
    · refine Set.mem_iUnion.2 ⟨true, ?_⟩
      change x ∈ Set.range (B.inclusion.map ιb).base
      rw [hιb]
      exact hx
    · refine Set.mem_iUnion.2 ⟨false, ?_⟩
      change x ∈ Set.range (B.inclusion.map cb).base
      rw [hcr]
      exact hx
  · intro b
    cases b
    · refine isConstructibleModuleSheaf_congr B Λ Cb
        (etaleModuleToBoundedSiteInverseImageIso Λ B cb _).symm ?_
      have hij : Set.range ι.base = (Set.range (B.inclusion.map cb).base)ᶜ := by
        rw [hcr, compl_compl]
      have hz := isZero_etaleModuleInverseImage_extensionByZero Λ (B.inclusion.map cb) ι hij F
      have hz' := (etaleModuleToBoundedSite Λ B Cb.property).map_isZero hz
      exact isConstructibleModuleSheaf_congr B Λ Cb hz'.isoZero.symm
        (isConstructibleModuleSheaf_zero B Cb Λ)
    · refine isConstructibleModuleSheaf_congr B Λ Ub
        (etaleModuleToBoundedSiteInverseImageIso Λ B ιb _).symm ?_
      let e : (etaleModuleInverseImage.{u, r} Λ (B.inclusion.map ιb)).obj
          ((etaleModuleExtensionByZero.{u, r} Λ ι).obj F) ≅ F :=
        eqToIso (congrArg (fun g : U ⟶ X ↦ (etaleModuleInverseImage.{u, r} Λ g).obj
            ((etaleModuleExtensionByZero.{u, r} Λ ι).obj F)) hιb) ≪≫
          (etaleModuleInverseImageRestrictionIso.{u, r} Λ ι).app _ ≪≫
          (asIso ((etaleModuleExtensionByZeroAdj.{u, r} Λ ι).unit.app F)).symm
      exact isConstructibleModuleSheaf_congr B Λ Ub
        ((etaleModuleToBoundedSite Λ B hU).mapIso e).symm
        ((isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B hU F).1 hF)

end Stacks.EtaleCohomology

end
