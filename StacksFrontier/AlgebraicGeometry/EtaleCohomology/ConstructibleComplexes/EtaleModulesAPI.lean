module
public import StacksCore.Algebra.Homology.SpectralSequence.Tower
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLimitsSets
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ImmersionCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GlobalSectionsClosed.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Support.AffineLifting
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleBaseChange

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportCurves.ConstructibleBigSiteIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ZariskiDescent
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.BoundedComplexes
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructible sheaves of `Λ`-modules in the model `EtaleModules Λ X`: inverse image, locality

`Stacks.EtaleCohomology.IsConstructibleEtaleModule` is constructibility (Tag 03RW part (3)) of a
sheaf of `Λ`-modules on Mathlib's small étale site, read on the small étale site of Tag 021B of a
big étale site containing the scheme; by
`Stacks.EtaleCohomology.isConstructibleEtaleModule_iff_isConstructibleModuleSheaf` any big étale
site containing the scheme may be used. This file transports to the model `EtaleModules Λ X` the
basic stability properties proved for `AlgebraicGeometry.IsConstructibleModuleSheaf`, for a
Noetherian ring `Λ`.

## Main results

* `Stacks.EtaleCohomology.isConstructibleEtaleModule_etaleModuleInverseImage`: Tag 095G, the
  inverse image along an arbitrary morphism of schemes of a constructible sheaf is constructible;
  `isConstructibleEtaleModule_etaleModuleRestriction` is the case of restriction along an étale
  morphism.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_iff_forall_etaleModuleRestriction`:
  Tag 095F, constructibility is local for the Zariski topology.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_of_constructible_immersion_cover`: Tag 09YR,
  on a quasi-compact quasi-separated scheme constructibility may be checked on the members of a
  finite cover by constructible locally closed subschemes.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_of_isOpen_isClosed` and
  `Stacks.EtaleCohomology.isConstructibleEtaleModule_of_isOpenImmersion_of_isClosedImmersion`: a
  sheaf constructible on a quasi-compact open and on a closed subscheme with complementary support
  is constructible.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_etaleModuleDirectImage_of_isClosedImmersion`:
  direct image along a closed immersion with quasi-compact open complement preserves
  constructibility.
* `Stacks.EtaleCohomology.isConstructibleEtaleModule_constantSheaf`: the constant sheaf on a
  finite `Λ`-module is constructible.

## Implementation notes

Each statement is proved by passing to a big étale site containing all the schemes involved, the
canonical one `AlgebraicGeometry.BigEtaleSite.ofSet` of the finite set of these schemes, or
`AlgebraicGeometry.BigEtaleSite.containing X` when the other schemes are immersed in `X`;
inverse image commutes with this passage by
`Stacks.EtaleCohomology.etaleModuleToBoundedSiteInverseImageIso`.

## References

* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
* [Stacks Project, Tag 095F](https://stacks.math.columbia.edu/tag/095F)
* [Stacks Project, Tag 09YR](https://stacks.math.columbia.edu/tag/09YR)
* [Stacks Project, Tag 095R](https://stacks.math.columbia.edu/tag/095R)
* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] SmallEtale.isRightAdjointPushforward_moduleCat
  SmallEtale.hasWeakSheafifyOver_moduleCat moduleCat_hasLimitsOfSize

variable (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ]

/-- Inverse image along two equal morphisms gives isomorphic sheaves. -/
private def etaleModuleInverseImageObjCongr {X X' : Scheme.{u}} {g g' : X' ⟶ X} (h : g = g')
    (F : EtaleModules.{u, r} Λ X) :
    (etaleModuleInverseImage.{u, r} Λ g).obj F ≅ (etaleModuleInverseImage.{u, r} Λ g').obj F :=
  eqToIso (congrArg (fun g : X' ⟶ X ↦ (etaleModuleInverseImage.{u, r} Λ g).obj F) h)

omit [IsNoetherianRing Λ] in
/-- Constructibility of the inverse image along a morphism `g` of a big étale site `B`, read in
`B`, is constructibility of the inverse image in the model `EtaleModules`. -/
private theorem isConstructibleEtaleModule_etaleModuleInverseImage_iff_of_bigSite
    (B : BigEtaleSite.{u}) {S T : B.Scheme} (g : T ⟶ S) (F : EtaleModules.{u, r} Λ S.obj) :
    IsConstructibleEtaleModule Λ ((etaleModuleInverseImage.{u, r} Λ (B.inclusion.map g)).obj F) ↔
      IsConstructibleModuleSheaf B T Λ
        (((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPullback (ModuleCat.{max (u + 1) r} Λ)
          (SmallEtale.topology B S.obj S.property) (SmallEtale.topology B T.obj T.property)).obj
          ((etaleModuleToBoundedSite Λ B S.property).obj F)) := by
  rw [isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B T.property]
  exact ⟨isConstructibleModuleSheaf_congr B Λ T
      (etaleModuleToBoundedSiteInverseImageIso Λ B g F).symm,
    isConstructibleModuleSheaf_congr B Λ T (etaleModuleToBoundedSiteInverseImageIso Λ B g F)⟩

/-- **[Stacks, Tag 095G], in the model `EtaleModules`.** Let `Λ` be a Noetherian ring and
`g : X' ⟶ X` a morphism of schemes. The inverse image `g⁻¹ ℱ` of a constructible sheaf `ℱ` of
`Λ`-modules on `X_étale` is constructible. -/
theorem isConstructibleEtaleModule_etaleModuleInverseImage {X X' : Scheme.{u}} (g : X' ⟶ X)
    (F : EtaleModules.{u, r} Λ X) (hF : IsConstructibleEtaleModule Λ F) :
    IsConstructibleEtaleModule Λ ((etaleModuleInverseImage.{u, r} Λ g).obj F) := by
  let B := BigEtaleSite.ofSet ({X, X'} : Set Scheme.{u})
  have hX : B.Contains X := BigEtaleSite.contains_ofSet _ (by simp)
  have hX' : B.Contains X' := BigEtaleSite.contains_ofSet _ (by simp)
  let gb : B.obj X' hX' ⟶ B.obj X hX := B.inclusion.preimage g
  have hgb : B.inclusion.map gb = g := Functor.map_preimage _ _
  exact (IsConstructibleEtaleModule Λ).prop_of_iso (etaleModuleInverseImageObjCongr Λ hgb F)
    ((isConstructibleEtaleModule_etaleModuleInverseImage_iff_of_bigSite Λ B gb F).2
      (isConstructibleModuleSheaf_pullback B Λ gb _
        ((isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B hX F).1 hF)))

/-- **[Stacks, Tag 095G], restriction along an étale morphism.** For an étale morphism
`j : U ⟶ X` the restriction `ℱ|_U` of a constructible sheaf `ℱ` of `Λ`-modules is constructible. -/
theorem isConstructibleEtaleModule_etaleModuleRestriction {U X : Scheme.{u}} (j : U ⟶ X)
    [Etale j] (F : EtaleModules.{u, r} Λ X) (hF : IsConstructibleEtaleModule Λ F) :
    IsConstructibleEtaleModule Λ ((etaleModuleRestriction.{u, r} Λ j).obj F) :=
  (IsConstructibleEtaleModule Λ).prop_of_iso
    ((etaleModuleInverseImageRestrictionIso.{u, r} Λ j).app F)
    (isConstructibleEtaleModule_etaleModuleInverseImage Λ j F hF)

/-- **[Stacks, Tag 095F], in the model `EtaleModules`.** Let `Λ` be a Noetherian ring and let
`j k : U k ⟶ X` be open immersions whose images cover `X`. A sheaf `ℱ` of `Λ`-modules on `X_étale`
is constructible if and only if every restriction `ℱ|_{U k}` is. -/
theorem isConstructibleEtaleModule_iff_forall_etaleModuleRestriction {X : Scheme.{u}}
    (F : EtaleModules.{u, r} Λ X) {I : Type*} (U : I → Scheme.{u}) (j : ∀ k, U k ⟶ X)
    [∀ k, IsOpenImmersion (j k)] (hcover : ⋃ k, Set.range (j k).base = Set.univ) :
    IsConstructibleEtaleModule Λ F ↔
      ∀ k, IsConstructibleEtaleModule Λ ((etaleModuleRestriction.{u, r} Λ (j k)).obj F) := by
  refine ⟨fun hF k ↦ isConstructibleEtaleModule_etaleModuleRestriction Λ (j k) F hF,
    fun hloc ↦ ?_⟩
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  have hU : ∀ k, B.Contains (U k) := fun k ↦ Scheme.size_lt_of_isOpenImmersion (j k) hX
  let jb : ∀ k, B.obj (U k) (hU k) ⟶ B.obj X hX := fun k ↦ B.inclusion.preimage (j k)
  have hjb : ∀ k, B.inclusion.map (jb k) = j k := fun k ↦ Functor.map_preimage _ _
  refine (isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B hX F).2 ?_
  refine isConstructibleModuleSheaf_of_openCover B Λ (B.obj X hX) _ (fun k ↦ B.obj (U k) (hU k))
    jb (fun k ↦ by rw [hjb]; infer_instance) ?_ fun k ↦ ?_
  · simpa only [hjb] using hcover.symm
  · refine (isConstructibleEtaleModule_etaleModuleInverseImage_iff_of_bigSite Λ B (jb k) F).1 ?_
    refine (IsConstructibleEtaleModule Λ).prop_of_iso ?_ (hloc k)
    exact ((etaleModuleInverseImageRestrictionIso.{u, r} Λ (j k)).app F).symm ≪≫
      etaleModuleInverseImageObjCongr Λ (hjb k).symm F

/-- **[Stacks, Tag 095F], for a cover by opens.** Let `Λ` be a Noetherian ring and let `U k` be
opens of `X` covering `X`. A sheaf `ℱ` of `Λ`-modules on `X_étale` is constructible if and only if
every restriction `ℱ|_{U k}` is. -/
theorem isConstructibleEtaleModule_iff_forall_etaleModuleRestriction_opens {X : Scheme.{u}}
    (F : EtaleModules.{u, r} Λ X) {I : Type*} (U : I → X.Opens) (hU : ⨆ k, U k = ⊤) :
    IsConstructibleEtaleModule Λ F ↔
      ∀ k, IsConstructibleEtaleModule Λ ((etaleModuleRestriction.{u, r} Λ (U k).ι).obj F) :=
  isConstructibleEtaleModule_iff_forall_etaleModuleRestriction Λ F (fun k ↦ (U k : Scheme.{u}))
    (fun k ↦ (U k).ι) (by
      simp only [Scheme.Opens.range_ι, ← TopologicalSpace.Opens.coe_iSup, hU,
        TopologicalSpace.Opens.coe_top])

/-- **[Stacks, Tag 09YR], in the model `EtaleModules`.** Let `Λ` be a Noetherian ring and `X` a
quasi-compact quasi-separated scheme, and let `j i : T i ⟶ X` be immersions with constructible
images covering `X`. A sheaf `ℱ` of `Λ`-modules on `X_étale` all of whose inverse images
`(j i)⁻¹ ℱ` are constructible is constructible. -/
theorem isConstructibleEtaleModule_of_constructible_immersion_cover {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (F : EtaleModules.{u, r} Λ X) {I : Type*}
    (T : I → Scheme.{u}) (j : ∀ i, T i ⟶ X) [∀ i, IsImmersion (j i)]
    (hc : ∀ i, Topology.IsConstructible (Set.range (j i).base))
    (hcover : ⋃ i, Set.range (j i).base = Set.univ)
    (hF : ∀ i, IsConstructibleEtaleModule Λ ((etaleModuleInverseImage.{u, r} Λ (j i)).obj F)) :
    IsConstructibleEtaleModule Λ F := by
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  have hT : ∀ i, B.Contains (T i) := fun i ↦ Scheme.size_lt_of_isImmersion (j i) hX
  let jb : ∀ i, B.obj (T i) (hT i) ⟶ B.obj X hX := fun i ↦ B.inclusion.preimage (j i)
  have hjb : ∀ i, B.inclusion.map (jb i) = j i := fun i ↦ Functor.map_preimage _ _
  have : CompactSpace (B.obj X hX).obj := ‹CompactSpace X›
  have : QuasiSeparatedSpace (B.obj X hX).obj := ‹QuasiSeparatedSpace X›
  refine (isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B hX F).2 ?_
  refine isConstructibleModuleSheaf_of_constructible_immersion_cover B (B.obj X hX) Λ _
    (fun i ↦ B.obj (T i) (hT i)) jb (fun i ↦ by rw [hjb]; infer_instance)
    (fun i ↦ by rw [hjb]; exact hc i) (by simpa only [hjb] using hcover.symm) fun i ↦ ?_
  refine (isConstructibleEtaleModule_etaleModuleInverseImage_iff_of_bigSite Λ B (jb i) F).1 ?_
  exact (IsConstructibleEtaleModule Λ).prop_of_iso
    (etaleModuleInverseImageObjCongr Λ (hjb i).symm F) (hF i)

/-- Constructibility from that of the restriction to a quasi-compact open subscheme and of the
inverse image to its closed complement. -/
private theorem isConstructibleEtaleModule_of_open_closed_aux {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (F : EtaleModules.{u, r} Λ X) {U Z : Scheme.{u}}
    (jU : U ⟶ X) [IsOpenImmersion jU] [CompactSpace U] (i : Z ⟶ X) [IsClosedImmersion i]
    (hij : Set.range jU.base = (Set.range i.base)ᶜ)
    (hFU : IsConstructibleEtaleModule Λ ((etaleModuleRestriction.{u, r} Λ jU).obj F))
    (hFZ : IsConstructibleEtaleModule Λ ((etaleModuleInverseImage.{u, r} Λ i).obj F)) :
    IsConstructibleEtaleModule Λ F := by
  have hcons : Topology.IsConstructible (Set.range jU.base) :=
    (isCompact_range jU.base.hom.continuous).isConstructible jU.isOpenEmbedding.isOpen_range
  let T : Bool → Scheme.{u} := fun b ↦ match b with | true => U | false => Z
  let j : ∀ b, T b ⟶ X := fun b ↦ match b with | true => jU | false => i
  have : ∀ b, IsImmersion (j b)
    | true => inferInstanceAs (IsImmersion jU)
    | false => inferInstanceAs (IsImmersion i)
  refine isConstructibleEtaleModule_of_constructible_immersion_cover Λ F T j (fun b ↦ ?_) ?_
    (fun b ↦ ?_)
  · cases b
    · show Topology.IsConstructible (Set.range i.base)
      rw [← compl_compl (Set.range i.base), ← hij]
      exact hcons.compl
    · exact hcons
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    by_cases hx : x ∈ Set.range jU.base
    · exact Set.mem_iUnion.2 ⟨true, hx⟩
    · refine Set.mem_iUnion.2 ⟨false, ?_⟩
      show x ∈ Set.range i.base
      rw [hij, Set.mem_compl_iff, not_not] at hx
      exact hx
  · cases b
    · exact hFZ
    · exact (IsConstructibleEtaleModule Λ).prop_of_iso
        ((etaleModuleInverseImageRestrictionIso.{u, r} Λ jU).app F).symm hFU

/-- **Constructibility on an open and on its closed complement.** Let `Λ` be a Noetherian ring,
`X` a quasi-compact quasi-separated scheme, `U` a quasi-compact open of `X` and `i : Z ⟶ X` a
closed immersion with image the complement of `U`. A sheaf `ℱ` of `Λ`-modules on `X_étale` whose
restriction `ℱ|_U` and inverse image `i⁻¹ ℱ` are constructible is constructible. -/
theorem isConstructibleEtaleModule_of_isOpen_isClosed {X : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (F : EtaleModules.{u, r} Λ X) (U : X.Opens)
    (hU : IsCompact (U : Set X)) {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (hZ : Set.range i.base = (U : Set X)ᶜ)
    (hFU : IsConstructibleEtaleModule Λ ((etaleModuleRestriction.{u, r} Λ U.ι).obj F))
    (hFZ : IsConstructibleEtaleModule Λ ((etaleModuleInverseImage.{u, r} Λ i).obj F)) :
    IsConstructibleEtaleModule Λ F := by
  have : CompactSpace U := isCompact_iff_compactSpace.1 hU
  exact isConstructibleEtaleModule_of_open_closed_aux Λ F U.ι i
    (by rw [Scheme.Opens.range_ι, hZ, compl_compl]) hFU hFZ

/-- **Constructibility on an open subscheme and on its closed complement.** Let `Λ` be a
Noetherian ring, `X` a quasi-compact quasi-separated scheme, `jU : U ⟶ X` an open immersion with
`U` quasi-compact and `i : Z ⟶ X` a closed immersion whose image is the complement of the image of
`jU`. A sheaf `ℱ` of `Λ`-modules on `X_étale` whose restriction to `U` and inverse image to `Z`
are constructible is constructible. -/
theorem isConstructibleEtaleModule_of_isOpenImmersion_of_isClosedImmersion {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (F : EtaleModules.{u, r} Λ X) {U Z : Scheme.{u}}
    (jU : U ⟶ X) [IsOpenImmersion jU] [CompactSpace U] (i : Z ⟶ X) [IsClosedImmersion i]
    (hij : Set.range jU.base = (Set.range i.base)ᶜ)
    (hFU : IsConstructibleEtaleModule Λ ((etaleModuleRestriction.{u, r} Λ jU).obj F))
    (hFZ : IsConstructibleEtaleModule Λ ((etaleModuleInverseImage.{u, r} Λ i).obj F)) :
    IsConstructibleEtaleModule Λ F :=
  isConstructibleEtaleModule_of_open_closed_aux Λ F jU i hij hFU hFZ

/-- **Direct image along a closed immersion preserves constructibility** (the case of a closed
immersion of Tag 095R). Let `Λ` be a Noetherian ring, `X` a quasi-compact quasi-separated scheme
and `i : Z ⟶ X` a closed immersion whose open complement is quasi-compact (for instance a closed
immersion of finite presentation). If `ℱ` is a constructible sheaf of `Λ`-modules on `Z_étale`,
then `i_* ℱ` is constructible on `X_étale`: its inverse image to `Z` is `ℱ` and its restriction to
the complement is zero. -/
@[sga "4 IX 2.14" "(i), special case"]
theorem isConstructibleEtaleModule_etaleModuleDirectImage_of_isClosedImmersion {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (hi : IsCompact (Set.range i.base)ᶜ) (F : EtaleModules.{u, r} Λ Z)
    (hF : IsConstructibleEtaleModule Λ F) :
    IsConstructibleEtaleModule Λ ((etaleModuleDirectImage.{u, r} Λ i).obj F) := by
  let U : X.Opens := ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hdisj : Disjoint (Set.range i.base) (Set.range U.ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact disjoint_compl_right
  refine isConstructibleEtaleModule_of_isOpen_isClosed Λ _ U hi i (by simp [U]) ?_ ?_
  · exact (IsConstructibleEtaleModule Λ).prop_of_isZero
      (isZero_etaleModuleRestriction_etaleModuleDirectImage_of_disjoint Λ i U.ι hdisj F)
  · have := (etaleModuleDirectImageFullyFaithful.{u, r} Λ i).full
    have := (etaleModuleDirectImageFullyFaithful.{u, r} Λ i).faithful
    exact (IsConstructibleEtaleModule Λ).prop_of_iso
      (asIso ((etaleModuleInverseImageAdj.{u, r} Λ i).counit.app F)).symm hF

/-- **The constant sheaf on a finite module is constructible.** For a Noetherian ring `Λ` and a
finite `Λ`-module `E`, the constant sheaf `E̲` of `Λ`-modules on `X_étale` is constructible: it
is locally constant of finite type, already over `X` itself. -/
theorem isConstructibleEtaleModule_constantSheaf (X : Scheme.{u})
    (E : ModuleCat.{max (u + 1) r} Λ) [Module.Finite Λ E] :
    IsConstructibleEtaleModule Λ
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).obj E) := by
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  refine isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant B (B.obj X hX) Λ _ ?_
  refine (isFiniteTypeLocallyConstantModuleSheaf_etaleModuleToBoundedSite_iff Λ B hX _).2 ?_
  exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_of_constant
    X.smallEtaleTopology Λ (E := E) (inferInstanceAs (Module.Finite Λ E)) (Iso.refl _)

end Stacks.EtaleCohomology

end
