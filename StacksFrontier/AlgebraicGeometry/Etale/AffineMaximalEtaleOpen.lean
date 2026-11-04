module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import StacksFrontier.AlgebraicGeometry.Etale.AffineOfCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamificationLocus.Induction
public import StacksFrontier.AlgebraicGeometry.LocalSchemesFpqcCover.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.LocalizationBaseChange
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import
  StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.HartshorneLichtenbaumExcellent
public import StacksFrontier.RingTheory.LocalCohomology.CohomologicalDimension.Localization
public import StacksFrontier.RingTheory.LocalCohomology.DimensionBoundUnconditional
public import StacksFrontier.RingTheory.LocalCohomology.VanishingTFAE.HighBoundTFAE
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.VanishingTransfer
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Affineness of the complement of the ramification locus

Let `Y` be an excellent regular scheme over a field, let `f : X ⟶ Y` be of finite type with `X`
normal, and let `V ⊆ X` be the largest open on which `f` is étale. [Stacks, Tag 0ECD] asserts
that the inclusion `V ⟶ X` is affine. This file carries out the source's proof.

## Main results

* `AlgebraicGeometry.MaximalEtaleOpen.isAffineHom_maximalEtaleOpen`: [Stacks, Tag 0ECD].

## The structure of the proof

*Reduction to the local rings of `X`* ([Stacks, Tag 01Z6]). For `X` locally Noetherian, an open
`V` has affine inclusion as soon as its preimage in `Spec 𝒪_{X,x}` is affine for every `x`:
`Spec 𝒪_{X,x}` is the limit of the affine open neighbourhoods of `x`, so an affine preimage there
comes from an affine preimage in one such neighbourhood.

*Induction on `d = dim 𝒪_{Y,f x}`.* If `x ∈ V` there is nothing to prove. Otherwise choose an
affine open `W ∋ x` mapping into an affine open of `Y` and missing the finitely many points of
`V` over `y = f x` (the fibres of an étale morphism are discrete), and base change `W` to
`Spec A`, `A = 𝒪_{Y,y}`. The base change `T` is affine, and the preimage `U` of `V` in `T` is the
maximal étale open of `T ⟶ Spec A` ([Stacks, Tag 0476]), is quasi-compact, and lies over the
punctured spectrum of `A`. Its map to the punctured spectrum is affine: the points of the
punctured spectrum have local rings of smaller dimension, so the induction hypothesis applies to
the points of `T` over them. It remains to see that `U` is affine.

*The case `d ≤ 1`.* The punctured spectrum of `A` is affine ([Stacks, Tag 0BCR]), hence so is
`U`.

*The case `d ≥ 2`.* By [Stacks, Tag 0ECC] it suffices that `Hⁿ(U, 𝒪_U) = 0` for `n ≥ d - 1`.
Writing `T = Spec C` and `U = Spec C ∖ V(I)`, this is the bound `cd(C, I) ≤ d - 1` on the
cohomological dimension ([Stacks, Tag 0DX7]), which is checked at every localization `C_𝔭`
([Stacks, Tag 0DXB]). If `𝔭 ∈ U` the ideal becomes the unit ideal. If the generic point of
`Spec C_𝔭` is not in `U` the ideal becomes zero. Otherwise `U` is dense near `𝔭`, so
`dim C_𝔭 ≤ dim A_{f(𝔭)} ≤ d` by the dimension formula ([Stacks, Tag 02JU]) applied along an étale
generization; then `cd ≤ dim C_𝔭` ([Stacks, Tag 0DXC]) settles `dim C_𝔭 ≤ 1`, and for
`dim C_𝔭 ≥ 2` purity of the ramification locus ([Stacks, Tag 0EA4],
`AlgebraicGeometry.etaleAt_of_etaleAt_codimensionOne`) produces a non-étale point of codimension
one specializing to `𝔭`, so that `V(I C_𝔭)` has positive dimension and Hartshorne–Lichtenbaum
vanishing ([Stacks, Tag 0EB7]) for the excellent normal local ring `C_𝔭` gives
`cd < dim C_𝔭 ≤ d`.

## Implementation notes

The base is a regular scheme in the sense of `AlgebraicGeometry.IsRegular` ([Stacks, Tag 02IS]),
excellent in the sense that every point has an affine open neighbourhood whose ring of sections is
excellent (the definition of an excellent scheme), and over a field through a chosen morphism to
`Spec k`. "Finite type" is `LocallyOfFiniteType` together with `QuasiCompact`; the argument is
local on `X` and never uses quasi-compactness. The maximal étale open is the greatest element of
the set of opens `U` with `U.ι ≫ f` étale.

The punctured spectrum of `A` appears as `Stacks.LocalCohomology.complementZeroLocus A 𝔪`
throughout, and is identified with `Stacks.LocalCohomology.puncturedSpectrum`, the name
[Stacks, Tag 0ECC] is stated with, only where that tag is applied.

## References

* [Stacks Project, Tag 0ECD](https://stacks.math.columbia.edu/tag/0ECD)
* [Stacks Project, Tag 0ECC](https://stacks.math.columbia.edu/tag/0ECC)
* [Stacks Project, Tag 0EA4](https://stacks.math.columbia.edu/tag/0EA4)
* [Stacks Project, Tag 0EB7](https://stacks.math.columbia.edu/tag/0EB7)
* [Stacks Project, Tag 01Z6](https://stacks.math.columbia.edu/tag/01Z6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.LocalCohomology

universe u

namespace AlgebraicGeometry.MaximalEtaleOpen

private theorem exists_nhd_isAffineOpen_preimage_of_affine_stalk_preimage
    {X : Scheme.{u}} [IsAffine X] (V : X.Opens) (hV : IsCompact (V : Set X))
    (x : X) (hx : IsAffineOpen ((X.fromSpecStalk x) ⁻¹ᵁ V)) :
    ∃ (W₀ : X.Opens) (_ : x ∈ W₀), IsAffineOpen (Spec.map
      (X.presheaf.map (homOfLE le_top : W₀ ⟶ ⊤).op) ⁻¹ᵁ ((isAffineOpen_top X).fromSpec ⁻¹ᵁ V)) := by
  let G := (OpenNhds.inclusion x).op ⋙ X.presheaf
  let cR : Cocone G := {
    pt := X.presheaf.stalk x
    ι := {
      app := fun i => X.presheaf.germ i.unop.1 x i.unop.2
      naturality := fun i j f => X.presheaf.germ_res' f x j.unop.2 } }
  have hcR : IsColimit cR :=
    IsColimit.ofIsoColimit (colimit.isColimit G) (Cocone.ext (Iso.refl _) fun _ => rfl)
  let D := G.op ⋙ Scheme.Spec
  let c : Cone D := Scheme.Spec.mapCone cR.op
  have hc : IsLimit c := isLimitOfPreserves Scheme.Spec hcR.op
  let i₀ : (OpenNhds x)ᵒᵖᵒᵖ := op (op ⟨⊤, trivial⟩)
  let e : D.obj i₀ ⟶ X := (isAffineOpen_top X).fromSpec
  let U : (D.obj i₀).Opens := e ⁻¹ᵁ V
  have : IsAffineHom e := isAffineHom_of_isAffine (X := Spec Γ(X, ⊤)) e
  have hU : IsCompact (U : Set (D.obj i₀)) :=
    QuasiCompact.isCompact_preimage (f := e) V V.isOpen hV
  have hcomp : c.π.app i₀ ≫ e = X.fromSpecStalk x :=
    (isAffineOpen_top X).fromSpecStalk_eq_fromSpecStalk trivial
  have hpre : c.π.app i₀ ⁻¹ᵁ U = X.fromSpecStalk x ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, hcomp]
  have : IsAffine (opensCone D c i₀ U).pt := by
    show IsAffineOpen (c.π.app i₀ ⁻¹ᵁ U)
    rwa [hpre]
  have : ∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f) := by
    intro i j f
    dsimp [D]
    infer_instance
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := by
    intro i
    dsimp [D]
    infer_instance
  have : ∀ j, CompactSpace ((opensDiagram D i₀ U).obj j) := by
    intro j
    exact isCompact_iff_compactSpace.mp
      (QuasiCompact.isCompact_preimage (f := D.map j.hom) U U.isOpen hU)
  have : ∀ j, QuasiSeparatedSpace ((opensDiagram D i₀ U).obj j) := by
    intro j
    exact (isQuasiSeparated_iff_quasiSeparatedSpace _
      (D.map j.hom ⁻¹ᵁ U).isOpen).mp (.of_quasiSeparatedSpace _)
  obtain ⟨j, hj⟩ := Scheme.exists_isAffine_of_isLimit _ _
    (isLimitOpensCone D c hc i₀ U)
  exact ⟨_, j.left.unop.unop.2, (hj : IsAffineOpen (D.map j.hom ⁻¹ᵁ U))⟩

private theorem isAffineOpen_ι_preimage_of_fromSpec_preimage {X : Scheme.{u}}
    (V : X.Opens) {W : X.Opens} (hW : IsAffineOpen W)
    (h : IsAffineOpen (hW.fromSpec ⁻¹ᵁ V)) : IsAffineOpen (V.ι ⁻¹ᵁ W) := by
  have hi := h.image_of_isOpenImmersion hW.fromSpec
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf,
    IsAffineOpen.opensRange_fromSpec] at hi
  apply V.ι.isAffineOpen_iff_of_isOpenImmersion.mp
  rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]

private theorem exists_affine_preimage_neighborhood_of_affine_stalk_preimage
    {X : Scheme.{u}} [IsAffine X] (V : X.Opens) (hV : IsCompact (V : Set X))
    (x : X) (hx : IsAffineOpen ((X.fromSpecStalk x) ⁻¹ᵁ V)) :
    ∃ W : X.Opens, x ∈ W ∧ IsAffineOpen W ∧ IsAffineOpen (V.ι ⁻¹ᵁ W) := by
  obtain ⟨W₀, hxW₀, hW₀⟩ := exists_nhd_isAffineOpen_preimage_of_affine_stalk_preimage V hV x hx
  obtain ⟨W, hW, hxW, hWW₀⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := W₀) hxW₀
  have hWV := hW₀.preimage (Spec.map (X.presheaf.map (homOfLE (show W ≤ W₀ from hWW₀)).op))
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, ← Spec.map_comp,
    ← Functor.map_comp, (isAffineOpen_top X).map_fromSpec hW] at hWV
  exact ⟨W, hxW, hW, isAffineOpen_ι_preimage_of_fromSpec_preimage V hW hWV⟩

private theorem isAffineOpen_stalk_preimage_of_flat_preimmersion
    {X' X : Scheme.{u}} (j : X' ⟶ X) [Flat j] [IsPreimmersion j]
    (V : X.Opens) (x' : X')
    (h : IsAffineOpen (X.fromSpecStalk (j x') ⁻¹ᵁ V)) :
    IsAffineOpen (X'.fromSpecStalk x' ⁻¹ᵁ (j ⁻¹ᵁ V)) := by
  have : IsIso (j.stalkMap x') := isIso_stalkMap_of_flat_isPreimmersion j x'
  have hi := h.preimage (Spec.map (j.stalkMap x'))
  rwa [← Scheme.Hom.comp_preimage, Scheme.SpecMap_stalkMap_fromSpecStalk j] at hi

private theorem isAffineHom_of_affine_stalk_preimages
    {X : Scheme.{u}} [IsLocallyNoetherian X] (V : X.Opens)
    (h : ∀ x : X, IsAffineOpen (X.fromSpecStalk x ⁻¹ᵁ V)) : IsAffineHom V.ι := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro x
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (U := ⊤) (x := x) (by trivial)
  have : IsAffine U.toScheme := hU
  have : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : NoetherianSpace U.toScheme := noetherianSpace_of_isAffineOpen U hU
  let xU : U.toScheme := ⟨x, hxU⟩
  let VU : U.toScheme.Opens := U.ι ⁻¹ᵁ V
  have hVU : IsCompact (VU : Set U.toScheme) :=
    NoetherianSpace.isCompact _
  have hstalk : IsAffineOpen (U.toScheme.fromSpecStalk xU ⁻¹ᵁ VU) :=
    isAffineOpen_stalk_preimage_of_flat_preimmersion U.ι V xU (h _)
  obtain ⟨W, hxW, hW, hVW⟩ :=
    exists_affine_preimage_neighborhood_of_affine_stalk_preimage VU hVU xU hstalk
  let W' := U.ι ''ᵁ W
  have hW' : IsAffineOpen W' := hW.image_of_isOpenImmersion U.ι
  have hxW' : x ∈ W' := ⟨xU, hxW, rfl⟩
  have hinf : IsAffineOpen (VU ⊓ W) := by
    have hi := hVW.image_of_isOpenImmersion VU.ι
    rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] at hi
  have himage : U.ι ''ᵁ (VU ⊓ W) = V ⊓ W' := by
    ext z
    constructor
    · rintro ⟨y, ⟨hyV, hyW⟩, rfl⟩
      exact ⟨hyV, ⟨y, hyW, rfl⟩⟩
    · rintro ⟨hzV, y, hyW, rfl⟩
      exact ⟨y, ⟨hzV, hyW⟩, rfl⟩
  refine ⟨W', hxW', hW', ?_⟩
  apply V.ι.isAffineOpen_iff_of_isOpenImmersion.mp
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, ← himage]
  exact hinf.image_of_isOpenImmersion U.ι

private theorem isAffineOpen_preimage_of_isAffineHom_inclusion
    {T X : Scheme.{u}} [IsAffine T] (g : T ⟶ X) (V : X.Opens) [IsAffineHom V.ι] :
    IsAffineOpen (g ⁻¹ᵁ V) := by
  have : IsAffineHom (g ⁻¹ᵁ V).ι :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_morphismRestrict g V) inferInstance
  exact isAffine_of_isAffineHom (g ⁻¹ᵁ V).ι

private theorem etaleAt_iff_mem_maximalEtaleOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Opens)
    (hV : IsGreatest {U : X.Opens | Etale (U.ι ≫ f)} V) (x : X) :
    EtaleAt f x ↔ x ∈ V := by
  rw [etaleAt_iff_exists_open]
  exact ⟨fun ⟨_, hxU, hU⟩ => hV.2 hU hxU, fun hx => ⟨V, hx, hV.1⟩⟩

/-- Étaleness of `V ↪ X ⟶ Y` passes to the preimage of `V` under an open immersion `j`. -/
private theorem etale_preimage_ι_comp_of_isOpenImmersion
    {X Y X' : Scheme.{u}} (f : X ⟶ Y) (j : X' ⟶ X) [IsOpenImmersion j]
    (V : X.Opens) (hV : Etale (V.ι ≫ f)) : Etale ((j ⁻¹ᵁ V).ι ≫ (j ≫ f)) := by
  have : Etale (j.resLE V (j ⁻¹ᵁ V) le_rfl ≫ (V.ι ≫ f)) := inferInstance
  simpa only [← Category.assoc, Scheme.Hom.resLE_comp_ι] using this

private theorem isGreatest_etaleOpen_preimage_of_isOpenImmersion
    {X Y X' : Scheme.{u}} (f : X ⟶ Y) (j : X' ⟶ X) [IsOpenImmersion j]
    (V : X.Opens) (hV : IsGreatest {U : X.Opens | Etale (U.ι ≫ f)} V) :
    IsGreatest {U : X'.Opens | Etale (U.ι ≫ (j ≫ f))} (j ⁻¹ᵁ V) := by
  constructor
  · exact etale_preimage_ι_comp_of_isOpenImmersion f j V hV.1
  · intro U hU x hx
    have hxEt := (etaleAt_iff_exists_open (j ≫ f) x).2 ⟨U, hx, hU⟩
    exact (etaleAt_iff_mem_maximalEtaleOpen f V hV (j x)).mp
      (etaleAt_of_open_precomp j f x hxEt)

private theorem isAffineOpen_of_local_domain_krullDimLE_one
    (A : Type u) [CommRing A] [IsLocalRing A] [IsDomain A] [Ring.KrullDimLE 1 A]
    (U : (Spec (.of A)).Opens) (hU : IsLocalRing.closedPoint A ∉ U) :
    IsAffineOpen U := by
  change (⊤ : PrimeSpectrum A) ∉ U at hU
  apply IsAffineOpen.of_subsingleton
  intro p hp q hq
  rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top p with hp0 | hp1
  · rcases IsLocalRing.Ring.KrullDimLE.eq_bot_or_eq_top q with hq0 | hq1
    · exact hp0.trans hq0.symm
    · exact (hU (hq1 ▸ hq)).elim
  · exact (hU (hp1 ▸ hp)).elim

private theorem normal_stalk_isNormalRingPropForm
    {X : Scheme.{u}} [IsNormal X] (x : X) :
    IsNormalRing (X.presheaf.stalk x) := by
  have : IsDomain (X.presheaf.stalk x) := IsNormal.stalk_isDomain x
  have : IsIntegrallyClosed (X.presheaf.stalk x) := IsNormal.stalk_normal x
  exact IsNormalRing.of_isIntegrallyClosed _

private theorem isExcellent_stalk_of_exists_affineOpen
    (X : Scheme.{u}) (hX : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ IsExcellent Γ(X, U))
    (x : X) : IsExcellent (X.presheaf.stalk x) := by
  obtain ⟨⟨U, hU⟩, hxU, hUex⟩ := hX x
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
  have : Algebra.EssFiniteType Γ(X, U) (X.presheaf.stalk x) :=
    Algebra.EssFiniteType.of_isLocalization (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
  exact (isQuasiExcellent_and_isExcellent_of_essFiniteType
    (R := Γ(X, U)) (S := X.presheaf.stalk x)).2 hUex

private theorem isExcellent_stalk_of_locallyOfFiniteType
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hY : ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧ IsExcellent Γ(Y, U)) (x : X) :
    IsExcellent (X.presheaf.stalk x) := by
  let := (f.stalkMap x).hom.toAlgebra
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  exact (isQuasiExcellent_and_isExcellent_of_essFiniteType
    (R := Y.presheaf.stalk (f x)) (S := X.presheaf.stalk x)).2
      (isExcellent_stalk_of_exists_affineOpen Y hY (f x))

private noncomputable abbrev algebraStalkOfOverField
    {Y : Scheme.{u}} (k : Type u) [Field k]
    (g : Y ⟶ Spec (.of k)) (y : Y) :
    Algebra k (Y.presheaf.stalk y) :=
  let : Algebra k ((Spec (.of k)).presheaf.stalk (g y)) :=
    StructureSheaf.stalkAlgebra k (g y)
  ((g.stalkMap y).hom.comp
    (algebraMap k ((Spec (.of k)).presheaf.stalk (g y)))).toAlgebra

private theorem isExcellent_of_commRingCatIso
    {R S : CommRingCat.{u}} (e' : R ≅ S) (hR : IsExcellent R) : IsExcellent S := by
  let e := e'.commRingCatIsoToRingEquiv
  let : Algebra R S := e.toRingHom.toAlgebra
  have : Algebra.EssFiniteType R S := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact e.finite.to_finiteType.essFiniteType
  exact (isQuasiExcellent_and_isExcellent_of_essFiniteType
    (R := R) (S := S)).2 hR

private theorem isZero_cohomologyOverBase_of_isZero_Hgroup
    (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (F : X.Modules) (n : ℕ)
    (h : IsZero (Hgroup X.ringCatSheaf ⊤ n F)) :
    IsZero (Stacks.LocalCohomology.cohomologyOverBase A f F n) := by
  have h' := (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
    X.ringCatSheaf ⊤ n F).2 h
  unfold Stacks.LocalCohomology.cohomologyOverBase
  have hs : Subsingleton
      (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived n).obj F) :=
    ModuleCat.isZero_iff_subsingleton.mp h'
  exact ModuleCat.isZero_iff_subsingleton.mpr hs

private theorem hgroup_isZero_of_cohomologicalDimension_le
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) (d : ℤ)
    (hdpos : 0 < d) (hcd : Stacks.LocalCohomology.cohomologicalDimension A I hI ≤ d)
    (F : (complementZeroLocus A I : Scheme).Modules)
    (hF : F.IsQuasicoherent) (n : ℕ) (hn : d ≤ (n : ℤ)) :
    IsZero (Hgroup (complementZeroLocus A I : Scheme).ringCatSheaf ⊤ n F) := by
  have hd1 : (1 : ℤ) ≤ d := by omega
  exact Stacks.LocalCohomology.isZero_hgroup_complement_of_isZero_localCohomologyModule_self
    A I hI d hd1 (fun i hi => (Stacks.LocalCohomology.isLocalCohomologyBound_cohomologicalDimension
      A I hI).2 i (lt_of_le_of_lt hcd hi)) F hF n hn

/-- A point lies in the punctured spectrum of a local ring iff it is not the closed point. -/
private theorem mem_complementZeroLocus_maximalIdeal_iff
    (A : Type u) [CommRing A] [IsLocalRing A] (p : PrimeSpectrum A) :
    p ∈ complementZeroLocus A (IsLocalRing.maximalIdeal A) ↔ p ≠ IsLocalRing.closedPoint A := by
  change p ∈ (PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal A : Set A))ᶜ ↔ _
  rw [PrimeSpectrum.zeroLocus_eq_singleton]
  rfl

private theorem complementZeroLocus_maximalIdeal_eq (A : Type u) [CommRing A] [IsLocalRing A] :
    complementZeroLocus A (IsLocalRing.maximalIdeal A) =
      Stacks.LocalCohomology.puncturedSpectrum (CommRingCat.of A) := by
  ext p
  exact mem_complementZeroLocus_maximalIdeal_iff A p

private theorem isAffine_of_etale_over_open_eq_punctured_of_cohomology_vanishing
    (A k : Type u) [CommRing A] [IsRegularLocalRing A] [Field k] [Algebra k A]
    {V : Scheme.{u}} (f : V ⟶ Spec (.of A)) [Etale f] [QuasiCompact f]
    (P : (Spec (.of A)).Opens) (hP : P = Stacks.LocalCohomology.puncturedSpectrum (.of A))
    (g : V ⟶ (P : Scheme)) [IsAffineHom g] (hg : g ≫ P.ι = f)
    (hvanish : ∀ n : ℕ, ((ringKrullDim A).unbotD 0).toNat - 1 ≤ n →
      IsZero (Stacks.LocalCohomology.cohomologyOverBase A f
        (SheafOfModules.unit V.ringCatSheaf) n)) :
    IsAffine V := by
  subst hP
  exact Stacks.PuncturedSpectrum.isAffine_of_cohomologyOverBase_vanishing A k f g hg hvanish

private theorem isAffine_of_etale_over_regularLocal_complement_of_cohomology_vanishing
    (A k : Type u) [CommRing A] [IsRegularLocalRing A] [Field k] [Algebra k A]
    {V : Scheme.{u}} (f : V ⟶ Spec (.of A)) [Etale f] [QuasiCompact f]
    (g : V ⟶ (complementZeroLocus A (IsLocalRing.maximalIdeal A) : Scheme)) [IsAffineHom g]
    (hg : g ≫ (complementZeroLocus A (IsLocalRing.maximalIdeal A)).ι = f)
    (hvanish : ∀ n : ℕ, ((ringKrullDim A).unbotD 0).toNat - 1 ≤ n →
      IsZero (Stacks.LocalCohomology.cohomologyOverBase A f
        (SheafOfModules.unit V.ringCatSheaf) n)) :
    IsAffine V :=
  isAffine_of_etale_over_open_eq_punctured_of_cohomology_vanishing A k f _
    (complementZeroLocus_maximalIdeal_eq A) g hg hvanish

private theorem isAffine_of_etale_over_regularLocal_complement_of_Hgroup_vanishing
    (A k : Type u) [CommRing A] [IsRegularLocalRing A] [Field k] [Algebra k A]
    {V : Scheme.{u}} (f : V ⟶ Spec (.of A)) [Etale f] [QuasiCompact f]
    (g : V ⟶ (complementZeroLocus A
      (IsLocalRing.maximalIdeal A) : Scheme)) [IsAffineHom g]
    (hg : g ≫ (complementZeroLocus A
      (IsLocalRing.maximalIdeal A)).ι = f)
    (hgroup : ∀ n : ℕ, ((ringKrullDim A).unbotD 0).toNat - 1 ≤ n →
      IsZero (Hgroup V.ringCatSheaf ⊤ n (SheafOfModules.unit V.ringCatSheaf))) :
    IsAffine V := by
  apply isAffine_of_etale_over_regularLocal_complement_of_cohomology_vanishing
    A k f g hg
  intro n hn
  exact isZero_cohomologyOverBase_of_isZero_Hgroup A f
    (SheafOfModules.unit V.ringCatSheaf) n (hgroup n hn)

private theorem complementZeroLocus_vanishingIdeal_compl
    (A : Type u) [CommRing A] (U : (Spec (.of A)).Opens) :
    (⟨(PrimeSpectrum.zeroLocus
      (PrimeSpectrum.vanishingIdeal (U : Set (Spec (.of A)))ᶜ : Set A))ᶜ,
      (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩ : (Spec (.of A)).Opens) = U := by
  apply SetLike.coe_injective
  show (PrimeSpectrum.zeroLocus
    (PrimeSpectrum.vanishingIdeal (U : Set (Spec (.of A)))ᶜ : Set A))ᶜ =
      (U : Set (Spec (.of A)))
  have h : PrimeSpectrum.zeroLocus
      (PrimeSpectrum.vanishingIdeal (U : Set (Spec (.of A)))ᶜ : Set A) =
        (U : Set (Spec (.of A)))ᶜ :=
    (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure _).trans
      U.isOpen.isClosed_compl.closure_eq
  exact (congrArg compl h).trans (compl_compl _)

private theorem isRegularLocalRing_localizationAtPrime
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (p : PrimeSpectrum A) :
    IsRegularLocalRing (Localization.AtPrime p.asIdeal) := by
  have : IsRegularRing A :=
    ((IsLocalRing.isRegularRing_tfae (R := A)).out 1 3).mp
      (inferInstance : IsRegularLocalRing A)
  infer_instance

private theorem isExcellent_stalk_of_flat_preimmersion
    {X' X : Scheme.{u}} (j : X' ⟶ X) [Flat j] [IsPreimmersion j]
    (hX : ∀ x : X, IsExcellent (X.presheaf.stalk x)) (z : X') :
    IsExcellent (X'.presheaf.stalk z) := by
  have : IsIso (j.stalkMap z) := isIso_stalkMap_of_flat_isPreimmersion j z
  exact isExcellent_of_commRingCatIso (asIso (j.stalkMap z)) (hX (j z))

private theorem isAffineHom_restriction_of_stalk_preimages
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Y)
    (P : Y.Opens) (V : X.Opens)
    (h : ∀ z : X, z ∈ f ⁻¹ᵁ P →
      IsAffineOpen (X.fromSpecStalk z ⁻¹ᵁ V)) :
    IsAffineHom (((f ⁻¹ᵁ P).ι ⁻¹ᵁ V).ι) := by
  let U := f ⁻¹ᵁ P
  exact isAffineHom_of_affine_stalk_preimages _ fun z =>
    isAffineOpen_stalk_preimage_of_flat_preimmersion U.ι V z (h (U.ι z) z.2)

private theorem isNormal_pullback_fromSpecStalk
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNormal X] (y : Y) :
    IsNormal (pullback f (Y.fromSpecStalk y)) := by
  have : Flat (Y.fromSpecStalk y) := inferInstance
  exact isNormal_of_flat_preimmersion (pullback.fst f (Y.fromSpecStalk y))

/-- The two projections of a pullback of schemes agree on points. -/
private theorem apply_pullback_fst_eq_apply_pullback_snd
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (t : (pullback f g : Scheme.{u})) :
    f (pullback.fst f g t) = g (pullback.snd f g t) := by
  simpa only [Scheme.Hom.comp_apply] using
    congrArg (fun r : pullback f g ⟶ Z => r t) pullback.condition

private theorem isAffineHom_pullback_open_over_punctured_target_of_stalk_affine
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (V : X.Opens) (y : Y)
    (h : ∀ t : (pullback f (Y.fromSpecStalk y) : Scheme.{u}),
      t ∈ (pullback.snd f (Y.fromSpecStalk y)) ⁻¹ᵁ
        complementZeroLocus (Y.presheaf.stalk y)
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) →
      IsAffineOpen
        (X.fromSpecStalk ((pullback.fst f (Y.fromSpecStalk y)) t) ⁻¹ᵁ V)) :
    IsAffineHom
      ((((pullback.snd f (Y.fromSpecStalk y)) ⁻¹ᵁ
        complementZeroLocus (Y.presheaf.stalk y)
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))).ι) ⁻¹ᵁ
        ((pullback.fst f (Y.fromSpecStalk y)) ⁻¹ᵁ V)).ι := by
  let A := Y.presheaf.stalk y
  let b := Y.fromSpecStalk y
  let T := pullback f b
  let p : T ⟶ X := pullback.fst f b
  let q : T ⟶ Spec (.of A) := pullback.snd f b
  let P := complementZeroLocus A (IsLocalRing.maximalIdeal A)
  let U := p ⁻¹ᵁ V
  have : Flat b := inferInstance
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian q
  exact isAffineHom_restriction_of_stalk_preimages q P U fun t ht =>
    isAffineOpen_stalk_preimage_of_flat_preimmersion p V t (h t ht)

private theorem isGreatest_etaleOpen_preimage_of_flat_base
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (h : IsPullback g' f' f g)
    [LocallyOfFinitePresentation f] [Flat g]
    (V : X.Opens) (hV : IsGreatest {U : X.Opens | Etale (U.ι ≫ f)} V) :
    IsGreatest {U : X'.Opens | Etale (U.ι ≫ f')} (g' ⁻¹ᵁ V) := by
  have hmem (x' : X') : EtaleAt f' x' ↔ g' x' ∈ V := by
    rw [← etaleAt_iff_mem_maximalEtaleOpen f V hV]
    exact Set.ext_iff.mp (setOf_etaleAt_eq_preimage_of_isPullback h (Or.inr ‹Flat g›)) x'
  constructor
  · apply (etale_iff_forall_etaleAt _).mpr
    intro x'
    obtain ⟨U, hxU, hU⟩ := (etaleAt_iff_exists_open f' x'.1).mp ((hmem x'.1).mpr x'.2)
    have : Etale (U.ι ≫ f') := hU
    let W := (g' ⁻¹ᵁ V).ι ⁻¹ᵁ U
    refine (etaleAt_iff_exists_open _ x').mpr ⟨W, hxU, ?_⟩
    have heq : W.ι ≫ ((g' ⁻¹ᵁ V).ι ≫ f') =
        ((g' ⁻¹ᵁ V).ι.resLE U W le_rfl) ≫ (U.ι ≫ f') := by
      rw [Scheme.Hom.resLE_comp_ι_assoc]
    rw [heq]
    infer_instance
  · intro U hU x' hx'
    exact (hmem x').mp ((etaleAt_iff_exists_open f' x').mpr ⟨U, hx', hU⟩)

private theorem formallyUnramified_stalkMap_of_etaleAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (h : EtaleAt f x) :
    (f.stalkMap x).hom.FormallyUnramified := by
  obtain ⟨U, hxU, hU⟩ := (etaleAt_iff_exists_open f x).mp h
  have : Etale (U.ι ≫ f) := hU
  let xU : U.toScheme := ⟨x, hxU⟩
  have hh := FormallyUnramified.stalkMap (U.ι ≫ f) xU
  have heq : (U.ι ≫ f).stalkMap xU ≫ inv (U.ι.stalkMap xU) = f.stalkMap x := by
    rw [Scheme.Hom.stalkMap_comp]
    show (f.stalkMap x ≫ U.ι.stalkMap xU) ≫ inv (U.ι.stalkMap xU) = f.stalkMap x
    exact (Category.assoc _ _ _).trans ((congrArg (fun k => f.stalkMap x ≫ k)
      (IsIso.hom_inv_id (U.ι.stalkMap xU))).trans (Category.comp_id _))
  have hcomp : ((U.ι ≫ f).stalkMap xU ≫ inv (U.ι.stalkMap xU)).hom.FormallyUnramified := by
    rw [CommRingCat.hom_comp]
    exact hh.comp (RingHom.FormallyUnramified.of_surjective
      (ConcreteCategory.bijective_of_isIso (inv (U.ι.stalkMap xU))).2)
  exact heq ▸ hcomp

private theorem isClosed_singleton_in_fiber_of_quasiFiniteAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (y : Y) (z : f ⁻¹' {y}) (hz : f.QuasiFiniteAt z.1) :
    IsClosed ({z} : Set (f ⁻¹' {y})) := by
  obtain ⟨z, hzfy⟩ := z
  change f z = y at hzfy
  subst y
  have hcl : IsClosed ({f.asFiber z} : Set (f.fiber (f z))) :=
    (hz.isClopen_singleton_asFiber f).1
  have hcl' := (f.fiberHomeo (f z)).isClosed_image.mpr hcl
  simpa only [Set.image_singleton, Scheme.Hom.asFiber,
    Homeomorph.apply_symm_apply] using hcl'

private theorem exists_punctured_target_map_of_no_closed_fiber
    {X : Scheme.{u}} (A : Type u) [CommRing A] [IsLocalRing A]
    (f : X ⟶ Spec (.of A)) (V : X.Opens)
    (h : ∀ z : X, z ∈ V → f z ≠ IsLocalRing.closedPoint A) :
    ∃ g : V.toScheme ⟶
      (complementZeroLocus A (IsLocalRing.maximalIdeal A) : Scheme),
      g ≫ (complementZeroLocus A (IsLocalRing.maximalIdeal A)).ι = V.ι ≫ f := by
  let P := complementZeroLocus A (IsLocalRing.maximalIdeal A)
  have hsubset : Set.range (V.ι ≫ f) ⊆ Set.range P.ι := by
    rintro q ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact (mem_complementZeroLocus_maximalIdeal_iff A _).mpr (h (V.ι z) z.2)
  exact ⟨_, IsOpenImmersion.lift_fac P.ι (V.ι ≫ f) hsubset⟩

private theorem isAffineHom_punctured_target_of_affine_open_restriction
    {X : Scheme.{u}} [IsAffine X] (A : Type u) [CommRing A] [IsLocalRing A]
    (f : X ⟶ Spec (.of A)) (V : X.Opens)
    (g : V.toScheme ⟶
      (complementZeroLocus A (IsLocalRing.maximalIdeal A) : Scheme))
    (hg : g ≫ (complementZeroLocus A (IsLocalRing.maximalIdeal A)).ι = V.ι ≫ f)
    (hAffine : IsAffineHom
      (((f ⁻¹ᵁ complementZeroLocus A (IsLocalRing.maximalIdeal A)).ι) ⁻¹ᵁ V).ι) :
    IsAffineHom g := by
  let P := complementZeroLocus A (IsLocalRing.maximalIdeal A)
  let U := f ⁻¹ᵁ P
  have hVU : V ≤ U := by
    intro z hz
    have heq := congrArg (fun k : V.toScheme ⟶ Spec (.of A) => k ⟨z, hz⟩) hg
    change P.ι (g ⟨z, hz⟩) = f z at heq
    show f z ∈ P
    rw [← heq]
    exact (g ⟨z, hz⟩).2
  let e := Scheme.Opens.isoOfLE hVU
  have : IsAffineHom f := inferInstance
  have : IsAffineHom (f ∣_ P) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f P).flip inferInstance
  have : IsAffineHom (e.inv ≫ (U.ι ⁻¹ᵁ V).ι) := by
    have : IsAffineHom (U.ι ⁻¹ᵁ V).ι := hAffine
    infer_instance
  have heq : e.inv ≫ (U.ι ⁻¹ᵁ V).ι ≫ (f ∣_ P) = g := by
    apply (cancel_mono P.ι).1
    have he : e.inv ≫ (U.ι ⁻¹ᵁ V).ι ≫ U.ι = V.ι :=
      Scheme.Opens.isoOfLE_inv_ι hVU
    calc
      (e.inv ≫ (U.ι ⁻¹ᵁ V).ι ≫ (f ∣_ P)) ≫ P.ι =
          (e.inv ≫ (U.ι ⁻¹ᵁ V).ι ≫ U.ι) ≫ f := by
        simp only [Category.assoc, morphismRestrict_ι, U]
      _ = g ≫ P.ι := by rw [he, hg]
  rw [← heq]
  infer_instance

private theorem finite_etale_points_over
    {X Y : Scheme.{u}} [NoetherianSpace X] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (V : X.Opens)
    (hV : Etale (V.ι ≫ f)) (y : Y) :
    {x : X | x ∈ V ∧ f x = y}.Finite := by
  let fV := V.ι ≫ f
  have : Etale fV := hV
  have : LocallyOfFiniteType fV := by
    dsimp [fV]
    infer_instance
  have hqf (z : V.toScheme) : fV.QuasiFiniteAt z :=
    (AlgebraicGeometry.quasiFiniteAt_of_etaleAt fV z ((etale_iff_forall_etaleAt fV).mp hV z)).2
  have : LocallyQuasiFinite fV := by
    apply (Scheme.Hom.quasiFiniteLocus_eq_top_iff fV).mp
    ext z
    exact ⟨fun _ => trivial, fun _ => Scheme.Hom.mem_quasiFiniteLocus.mpr (hqf z)⟩
  have : NoetherianSpace V.toScheme := by
    show NoetherianSpace (V : Set X)
    infer_instance
  have : QuasiCompact fV := inferInstance
  have hfinite := Scheme.Hom.finite_preimage_singleton fV y
  have hset : V.ι '' (fV ⁻¹' {y}) = {x : X | x ∈ V ∧ f x = y} := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.2, hz⟩
    · rintro ⟨hx, hxy⟩
      exact ⟨⟨x, hx⟩, hxy, rfl⟩
  rw [← hset]
  exact hfinite.image V.ι

private theorem exists_affine_open_avoiding_etale_fiber
    {X Y : Scheme.{u}} [NoetherianSpace X] (f : X ⟶ Y)
    [LocallyOfFiniteType f] (V : X.Opens)
    (hV : IsGreatest {U : X.Opens | Etale (U.ι ≫ f)} V)
    (x : X) (hx : x ∉ V) :
    ∃ W : X.Opens, x ∈ W ∧ IsAffineOpen W ∧
      ∀ z : X, z ∈ W → f z = f x → z ∉ V := by
  let F : Set X := {z | z ∈ V ∧ f z = f x}
  have hF : F.Finite := finite_etale_points_over f V hV.1 (f x)
  let T : Set (f ⁻¹' {f x}) := Subtype.val ⁻¹' F
  have hT : T.Finite := hF.preimage Subtype.val_injective.injOn
  have hTclosed : IsClosed T := by
    have hclosed (z : f ⁻¹' {f x}) (hz : z ∈ T) :
        IsClosed ({z} : Set (f ⁻¹' {f x})) := by
      have hzV : z.1 ∈ V := hz.1
      exact isClosed_singleton_in_fiber_of_quasiFiniteAt f (f x) z
        (AlgebraicGeometry.quasiFiniteAt_of_etaleAt f z.1
          ((etaleAt_iff_mem_maximalEtaleOpen f V hV z.1).mpr hzV)).2
    have hclosedUnion : IsClosed (⋃ z ∈ T, ({z} : Set (f ⁻¹' {f x}))) :=
      hT.isClosed_biUnion hclosed
    convert hclosedUnion using 1
    ext z
    simp
  obtain ⟨W₀, hW₀, hpre⟩ := isOpen_induced_iff.mp hTclosed.isOpen_compl
  let W : X.Opens := ⟨W₀, hW₀⟩
  have hxW : x ∈ W := by
    have hnot : (⟨x, rfl⟩ : f ⁻¹' {f x}) ∈ Tᶜ := by
      simpa only [T, F, Set.mem_compl_iff, Set.mem_preimage,
        Set.mem_ofPred_eq, not_and, not_true_eq_false, false_implies] using hx
    have hmem : (⟨x, rfl⟩ : f ⁻¹' {f x}) ∈ Subtype.val ⁻¹' W₀ := by
      rw [hpre]
      exact hnot
    exact hmem
  obtain ⟨W', hW', hxW', hW'W⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := W) hxW
  refine ⟨W', hxW', hW', ?_⟩
  intro z hzW' hzfy hzV
  have hzT : (⟨z, hzfy⟩ : f ⁻¹' {f x}) ∈ T := ⟨hzV, hzfy⟩
  have hzW₀ : z ∈ W₀ := hW'W hzW'
  have hznot : (⟨z, hzfy⟩ : f ⁻¹' {f x}) ∈ Tᶜ := by
    rw [← hpre]
    exact hzW₀
  exact hznot hzT

private theorem functionFieldMap_formallyUnramified_of_etaleAt_genericPoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f]
    (h : EtaleAt f (genericPoint X)) :
    (dominantFunctionFieldMap f).FormallyUnramified := by
  have hcast (y : Y) (hy : f (genericPoint X) = y) :
      ((hy ▸ f.stalkMap (genericPoint X)) :
        Y.presheaf.stalk y ⟶ X.presheaf.stalk (genericPoint X)).hom.FormallyUnramified := by
    subst y
    exact formallyUnramified_stalkMap_of_etaleAt f _ h
  exact hcast _ _

private theorem functionFieldMap_essFiniteType
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f]
    [LocallyOfFiniteType f] : (dominantFunctionFieldMap f).EssFiniteType := by
  have hcast (y : Y) (hy : f (genericPoint X) = y) :
      ((hy ▸ f.stalkMap (genericPoint X)) :
        Y.presheaf.stalk y ⟶ X.presheaf.stalk (genericPoint X)).hom.EssFiniteType := by
    subst y
    exact LocallyOfFiniteType.stalkMap f _
  exact hcast _ _

private theorem localDimension_le_of_etaleAt_genericPoint
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y] [IsDominant f]
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    (h : EtaleAt f (genericPoint X)) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ ringKrullDim (Y.presheaf.stalk (f x)) := by
  let := (dominantFunctionFieldMap f).toAlgebra
  have : Algebra.FormallyUnramified Y.functionField X.functionField :=
    functionFieldMap_formallyUnramified_of_etaleAt_genericPoint f h
  have : Algebra.EssFiniteType Y.functionField X.functionField :=
    functionFieldMap_essFiniteType f
  have : Module.Finite Y.functionField X.functionField :=
    Algebra.FormallyUnramified.finite_of_free Y.functionField X.functionField
  have htrdeg : Algebra.trdeg Y.functionField X.functionField = 0 := trdeg_eq_zero
  let := (f.residueFieldMap x).hom.toAlgebra
  have hdim := AlgebraicGeometry.localDimension_add_trdeg_le f x
  dsimp only at hdim
  rw [htrdeg, map_zero, WithBot.coe_zero, add_zero] at hdim
  exact le_trans (le_add_of_nonneg_right (WithBot.coe_le_coe.mpr bot_le)) hdim

private theorem isDominant_of_exists_etaleAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IrreducibleSpace Y]
    (x : X) (hx : EtaleAt f x) : IsDominant f := by
  obtain ⟨U, hxU, hU⟩ := (etaleAt_iff_exists_open f x).mp hx
  have : Etale (U.ι ≫ f) := hU
  have : IsDominant (U.ι ≫ f) := by
    constructor
    exact (U.ι ≫ f).isOpenMap.isOpen_range.dense ⟨(U.ι ≫ f) ⟨x, hxU⟩, Set.mem_range_self _⟩
  exact IsDominant.of_comp U.ι f

private theorem localDimension_le_of_nonempty_etale_open
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    (V : X.Opens) (hV : Etale (V.ι ≫ f))
    (hne : (V : Set X).Nonempty) (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤
      ringKrullDim (Y.presheaf.stalk (f x)) := by
  have hgenV : genericPoint X ∈ V :=
    (genericPoint_spec X).mem_open_set_iff V.isOpen |>.mpr (by simpa using hne)
  have hgen : EtaleAt f (genericPoint X) :=
    (etaleAt_iff_exists_open f (genericPoint X)).mpr ⟨V, hgenV, hV⟩
  have : IsDominant f := isDominant_of_exists_etaleAt f _ hgen
  exact localDimension_le_of_etaleAt_genericPoint f hgen x

private theorem exists_isAffineOpen_isIntegral_mem
    (X : Scheme.{u}) [IsLocallyNoetherian X] [IsNormal X] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧ IsIntegral U.toScheme := by
  have hfinite (U : X.Opens) (hU : IsCompact (U : Set X)) :
      (irreducibleComponents U).Finite := by
    have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
    have : IsNoetherian U.toScheme := ⟨⟩
    exact finite_irreducibleComponents_of_isNoetherian
  obtain ⟨ι, Z, hN, hI, ⟨e⟩⟩ :=
    (AlgebraicGeometry.isNormal_iff_exists_iso_coproduct hfinite).mp inferInstance
  let z : Σ i, Z i := (sigmaMk Z).symm (e.hom x)
  let j : Z z.1 ⟶ X := Sigma.ι Z z.1 ≫ e.inv
  have hj : j z.2 = x := by
    show (Sigma.ι Z z.1 ≫ e.inv) z.2 = x
    rw [Scheme.Hom.comp_apply]
    have hz : Sigma.ι Z z.1 z.2 = e.hom x := by
      rw [← sigmaMk_mk]
      exact (sigmaMk Z).apply_symm_apply (e.hom x)
    rw [hz]
    show (e.hom ≫ e.inv) x = x
    rw [e.hom_inv_id]
    rfl
  have : IsOpenImmersion j := by dsimp [j]; infer_instance
  have : IsIntegral (Z z.1) := hI z.1
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := Z z.1) (U := ⊤) (x := z.2) (by trivial)
  have : Nonempty U.toScheme := ⟨⟨z.2, hzU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  refine ⟨j ''ᵁ U, ⟨z.2, hzU, hj⟩, hU.image_of_isOpenImmersion j, ?_⟩
  exact IsIntegral.of_isIso (j.isoImage U).hom

private theorem isAffine_pullback_of_comp_mono
    {W B Y S : Scheme.{u}} [IsAffine W] [IsAffine B] [IsAffine S]
    (f : W ⟶ B) (g : S ⟶ B) (i : B ⟶ Y) [Mono i] :
    IsAffine (pullback (f ≫ i) (g ≫ i)) := by
  have : IsAffine (pullback f g) := inferInstance
  have hp : IsPullback (pullback.fst f g) (pullback.snd f g)
      (f ≫ i) (g ≫ i) :=
    IsPullback.of_isLimit (pullbackIsPullbackOfCompMono f g i)
  exact IsAffine.of_isIso hp.isoPullback.inv

private theorem isAffine_pullback_of_affine_source_over_target_stalk
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (W : X.Opens) (hW : IsAffineOpen W)
    (B : Y.Opens) (hB : IsAffineOpen B)
    (hWB : W ≤ f ⁻¹ᵁ B) (hyB : y ∈ B) :
    IsAffine (pullback (W.ι ≫ f) (Y.fromSpecStalk y)) := by
  have : IsAffine W.toScheme := hW
  have : IsAffine B.toScheme := hB
  have hf : Set.range (W.ι ≫ f) ⊆ Set.range B.ι := by
    rintro z ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hWB w.2
  have htop : Y.fromSpecStalk y ⁻¹ᵁ B = ⊤ :=
    Scheme.preimage_eq_top_of_closedPoint_mem (f := Y.fromSpecStalk y)
      (by simpa only [Scheme.fromSpecStalk_closedPoint] using hyB)
  have hg : Set.range (Y.fromSpecStalk y) ⊆ Set.range B.ι := by
    rintro z ⟨q, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hq : q ∈ Y.fromSpecStalk y ⁻¹ᵁ B := by rw [htop]; trivial
    exact hq
  let fB : W.toScheme ⟶ B.toScheme :=
    IsOpenImmersion.lift B.ι (W.ι ≫ f) hf
  let gB : Spec (Y.presheaf.stalk y) ⟶ B.toScheme :=
    IsOpenImmersion.lift B.ι (Y.fromSpecStalk y) hg
  have hfB : fB ≫ B.ι = W.ι ≫ f :=
    IsOpenImmersion.lift_fac B.ι (W.ι ≫ f) hf
  have hgB : gB ≫ B.ι = Y.fromSpecStalk y :=
    IsOpenImmersion.lift_fac B.ι (Y.fromSpecStalk y) hg
  simpa only [hfB, hgB] using
    isAffine_pullback_of_comp_mono fB gB B.ι

private theorem exists_affine_open_avoiding_etale_fiber_in_target_open
    {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (V : X.Opens) (hV : IsGreatest {U : X.Opens | Etale (U.ι ≫ f)} V)
    (x : X) (hx : x ∉ V) (B : Y.Opens) (hxy : f x ∈ B) :
    ∃ W : X.Opens, x ∈ W ∧ IsAffineOpen W ∧ W ≤ f ⁻¹ᵁ B ∧
      ∀ z : X, z ∈ W → f z = f x → z ∉ V := by
  obtain ⟨W₀, hW₀, hx₀, hWB⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := f ⁻¹ᵁ B) hxy
  let f₀ : W₀.toScheme ⟶ Y := W₀.ι ≫ f
  let V₀ : W₀.toScheme.Opens := W₀.ι ⁻¹ᵁ V
  let x₀ : W₀.toScheme := ⟨x, hx₀⟩
  have : IsNoetherianRing Γ(X, W₀) :=
    IsLocallyNoetherian.component_noetherian ⟨W₀, hW₀⟩
  have : NoetherianSpace W₀.toScheme := noetherianSpace_of_isAffineOpen W₀ hW₀
  have : LocallyOfFiniteType f₀ := inferInstance
  obtain ⟨W₁, hx₁, hW₁, hAvoid⟩ :=
    exists_affine_open_avoiding_etale_fiber f₀ V₀
      (isGreatest_etaleOpen_preimage_of_isOpenImmersion f W₀.ι V hV)
      x₀ hx
  let W : X.Opens := W₀.ι ''ᵁ W₁
  refine ⟨W, ⟨x₀, hx₁, rfl⟩, hW₁.image_of_isOpenImmersion W₀.ι, ?_, ?_⟩
  · rintro z ⟨z₀, hz₀, rfl⟩
    exact hWB z₀.2
  · rintro z ⟨z₀, hz₀, rfl⟩ hzfx hzV
    exact hAvoid z₀ hz₀ hzfx hzV

private theorem one_le_ringKrullDim_quotient_of_nonmaximal_prime
    (A : Type u) [CommRing A] [IsLocalRing A] (I : Ideal A)
    (p : PrimeSpectrum A) (hp : I ≤ p.asIdeal)
    (hne : p ≠ IsLocalRing.closedPoint A) :
    1 ≤ ringKrullDim (A ⧸ I) := by
  rw [ringKrullDim_quotient]
  apply Order.one_le_krullDim_iff.mpr
  have hpm : p ≤ IsLocalRing.closedPoint A := le_top
  refine ⟨⟨p, hp⟩, ⟨IsLocalRing.closedPoint A, hp.trans hpm⟩, ?_⟩
  show p < IsLocalRing.closedPoint A
  exact lt_top_iff_ne_top.mpr hne

private theorem vanishingIdeal_compl_map_eq_bot_of_generic_not_mem
    (C : Type u) [CommRing C]
    (U : (Spec (.of C)).Opens) (p : PrimeSpectrum C)
    [IsDomain (Localization.AtPrime p.asIdeal)]
    (h : PrimeSpectrum.comap
      (algebraMap C (Localization.AtPrime p.asIdeal))
        (⊥ : PrimeSpectrum (Localization.AtPrime p.asIdeal)) ∉ U) :
    (PrimeSpectrum.vanishingIdeal (U : Set (Spec (.of C)))ᶜ).map
      (algebraMap C (Localization.AtPrime p.asIdeal)) = ⊥ := by
  let B := Localization.AtPrime p.asIdeal
  let φ := algebraMap C B
  have hI : PrimeSpectrum.vanishingIdeal
      (U : Set (Spec (.of C)))ᶜ ≤
      (PrimeSpectrum.comap φ (⊥ : PrimeSpectrum B)).asIdeal :=
    PrimeSpectrum.subset_zeroLocus_vanishingIdeal _ h
  exact bot_unique (Ideal.map_le_iff_le_comap.mpr hI)

private theorem one_le_ringKrullDim_quotient_localization_of_prime_lt
    (A : Type u) [CommRing A] (I : Ideal A)
    (p q : PrimeSpectrum A) (hq : I ≤ q.asIdeal) (hqp : q < p) :
    1 ≤ ringKrullDim ((Localization.AtPrime p.asIdeal) ⧸
      I.map (algebraMap A (Localization.AtPrime p.asIdeal))) := by
  let B := Localization.AtPrime p.asIdeal
  let e := IsLocalization.AtPrime.primeSpectrumOrderIso B p.asIdeal
  let r : PrimeSpectrum B := e.symm ⟨q, hqp.le⟩
  have hr : PrimeSpectrum.comap (algebraMap A B) r = q :=
    congrArg Subtype.val (e.apply_symm_apply ⟨q, hqp.le⟩)
  apply one_le_ringKrullDim_quotient_of_nonmaximal_prime B _ r
  · rw [Ideal.map_le_iff_le_comap]
    exact hq.trans_eq (congrArg PrimeSpectrum.asIdeal hr).symm
  · intro heq
    apply hqp.ne
    rw [← hr, heq]
    apply PrimeSpectrum.ext
    exact IsLocalization.AtPrime.under_maximalIdeal B p.asIdeal

private theorem local_dimension_lt_of_strict_specialization
    (Y : Scheme.{u}) [IsLocallyNoetherian Y]
    (y' y : Y) (hsp : Specializes y' y) (hne : y' ≠ y)
    (d : ℕ) (hd : ringKrullDim (Y.presheaf.stalk y) = (d : WithBot ℕ∞)) :
    ∃ n : ℕ, ringKrullDim (Y.presheaf.stalk y') = (n : WithBot ℕ∞) ∧
      n + 1 ≤ d := by
  have hlt : y < y' := by
    constructor
    · exact (Scheme.le_iff_specializes).mpr hsp
    · intro hrev
      exact hne (Inseparable.eq (Specializes.antisymm hsp
        ((Scheme.le_iff_specializes).mp hrev)))
  obtain ⟨n, hn⟩ :=
    Stacks.ApproximationProperty.exists_natCast_eq_ringKrullDim (Y.presheaf.stalk y')
  have hdy : Order.coheight y = (d : ℕ∞) :=
    WithBot.coe_inj.mp ((ringKrullDim_stalk_eq_coheight y).symm.trans hd)
  have hdy' : Order.coheight y' = (n : ℕ∞) :=
    WithBot.coe_inj.mp ((ringKrullDim_stalk_eq_coheight y').symm.trans hn)
  refine ⟨n, hn, ?_⟩
  have hco := Order.coheight_add_one_le hlt
  rw [hdy', hdy] at hco
  exact_mod_cast hco

private theorem target_stalk_dimension_lt_of_punctured_stalk
    (Y : Scheme.{u}) [IsLocallyNoetherian Y] (y : Y)
    (d : ℕ) (hd : ringKrullDim (Y.presheaf.stalk y) =
      (d : WithBot ℕ∞))
    (q : Spec (Y.presheaf.stalk y))
    (hq : q ∈ complementZeroLocus (Y.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))) :
    ∃ n : ℕ,
      ringKrullDim (Y.presheaf.stalk (Y.fromSpecStalk y q)) =
        (n : WithBot ℕ∞) ∧ n < d := by
  have hqne := (mem_complementZeroLocus_maximalIdeal_iff _ q).mp hq
  have hsp : Specializes (Y.fromSpecStalk y q) y := by
    have hmem : Y.fromSpecStalk y q ∈ Set.range (Y.fromSpecStalk y) := ⟨q, rfl⟩
    rw [Scheme.range_fromSpecStalk] at hmem
    exact hmem
  have hne : Y.fromSpecStalk y q ≠ y := by
    intro heq
    apply hqne
    apply (inferInstance : IsPreimmersion (Y.fromSpecStalk y)).isEmbedding.injective
    simpa only [Scheme.fromSpecStalk_closedPoint] using heq
  obtain ⟨n, hn, hnd⟩ :=
    local_dimension_lt_of_strict_specialization Y (Y.fromSpecStalk y q) y
      hsp hne d hd
  exact ⟨n, hn, Nat.lt_of_succ_le hnd⟩

private theorem isAffineHom_pullback_open_over_punctured_target_of_smaller_stalks
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (V : X.Opens)
    (y : Y) (d : ℕ)
    (hd : ringKrullDim (Y.presheaf.stalk y) = (d : WithBot ℕ∞))
    (h : ∀ (z : X) (n : ℕ),
      ringKrullDim (Y.presheaf.stalk (f z)) = (n : WithBot ℕ∞) →
      n < d → IsAffineOpen (X.fromSpecStalk z ⁻¹ᵁ V)) :
    IsAffineHom
      ((((pullback.snd f (Y.fromSpecStalk y)) ⁻¹ᵁ
        complementZeroLocus (Y.presheaf.stalk y)
          (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))).ι) ⁻¹ᵁ
        ((pullback.fst f (Y.fromSpecStalk y)) ⁻¹ᵁ V)).ι := by
  apply isAffineHom_pullback_open_over_punctured_target_of_stalk_affine f V y
  intro t ht
  obtain ⟨n, hn, hnd⟩ :=
    target_stalk_dimension_lt_of_punctured_stalk Y y d hd
      ((pullback.snd f (Y.fromSpecStalk y)) t) ht
  exact h _ n (apply_pullback_fst_eq_apply_pullback_snd f (Y.fromSpecStalk y) t ▸ hn) hnd

private theorem localDimension_lt_of_nonclosedPoint
    (A : Type u) [CommRing A] [IsLocalRing A]
    (d : ℕ) (hd : ringKrullDim A = (d : WithBot ℕ∞))
    (p : PrimeSpectrum A) (hp : p ≠ IsLocalRing.closedPoint A) :
    ∃ n : ℕ, ringKrullDim (Localization.AtPrime p.asIdeal) =
      (n : WithBot ℕ∞) ∧ n + 1 ≤ d := by
  have hmax : (IsLocalRing.maximalIdeal A).height = (d : ℕ∞) :=
    WithBot.coe_inj.mp (IsLocalRing.maximalIdeal_height_eq_ringKrullDim.trans hd)
  have : (IsLocalRing.maximalIdeal A).FiniteHeight := by
    apply (Ideal.finiteHeight_iff _).mpr
    right
    rw [hmax]
    simp
  have hlt : p.asIdeal.height < (IsLocalRing.maximalIdeal A).height :=
    Ideal.height_strict_mono_of_isPrime_of_isPrime
      (show p.asIdeal < IsLocalRing.maximalIdeal A from
        lt_top_iff_ne_top.mpr hp)
  have hlt' : p.asIdeal.height < (d : ℕ∞) := hmax ▸ hlt
  have hfinite : p.asIdeal.height ≠ ⊤ := ne_top_of_lt hlt'
  lift p.asIdeal.height to ℕ using hfinite with n hn
  refine ⟨n, ?_, ?_⟩
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal
      (Localization.AtPrime p.asIdeal), ← hn]
    rfl
  · exact Nat.succ_le_of_lt (by exact_mod_cast hlt')

private theorem local_dimension_bound_of_local_ring
    (C : Type u) [CommRing C] [IsLocalRing C]
    (dC d : ℕ) (hdC : ringKrullDim C = (dC : WithBot ℕ∞))
    (hdCd : dC ≤ d) :
    ∀ q : PrimeSpectrum C,
      ∃ n : ℕ, ringKrullDim (Localization.AtPrime q.asIdeal) =
        (n : WithBot ℕ∞) ∧ n ≤ d := by
  intro q
  by_cases hq : q = IsLocalRing.closedPoint C
  · subst q
    refine ⟨dC, ?_, hdCd⟩
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height
      (IsLocalRing.closedPoint C).asIdeal
      (Localization.AtPrime (IsLocalRing.closedPoint C).asIdeal)]
    exact IsLocalRing.maximalIdeal_height_eq_ringKrullDim.trans hdC
  · obtain ⟨n, hn, hndC⟩ := localDimension_lt_of_nonclosedPoint C dC hdC q hq
    exact ⟨n, hn, (Nat.le_succ n).trans (hndC.trans hdCd)⟩

private theorem localDimension_le_of_etale_generization
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormal X] [IsIntegral Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (V : X.Opens) (hV : Etale (V.ι ≫ f))
    (x w : X) (hw : w ∈ V) (hsp : Specializes w x) :
    ringKrullDim (X.presheaf.stalk x) ≤
      ringKrullDim (Y.presheaf.stalk (f x)) := by
  obtain ⟨W, hxW, hW, hWi⟩ := exists_isAffineOpen_isIntegral_mem X x
  have hwW : w ∈ W := hsp.mem_open W.isOpen hxW
  let xW : W.toScheme := ⟨x, hxW⟩
  let VW : W.toScheme.Opens := W.ι ⁻¹ᵁ V
  have hVW := etale_preimage_ι_comp_of_isOpenImmersion f W.ι V hV
  have hne : (VW : Set W.toScheme).Nonempty := ⟨⟨w, hwW⟩, hw⟩
  have hdim := localDimension_le_of_nonempty_etale_open (W.ι ≫ f) VW hVW hne xW
  have : Flat W.ι := inferInstance
  have : IsIso (W.ι.stalkMap xW) :=
    isIso_stalkMap_of_flat_isPreimmersion W.ι xW
  have heq : ringKrullDim (X.presheaf.stalk x) =
      ringKrullDim (W.toScheme.presheaf.stalk xW) :=
    ringKrullDim_eq_of_ringEquiv
      (asIso (W.ι.stalkMap xW)).commRingCatIsoToRingEquiv
  rw [heq]
  exact hdim

private theorem quasiCompact_restrict_of_noetherianSpace
    {S T : Scheme.{u}} [NoetherianSpace S] (f : S ⟶ T)
    [QuasiCompact f] (U : S.Opens) : QuasiCompact (U.ι ≫ f) := by
  have : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set S)
  infer_instance

private theorem isGreatest_etaleOpen_affineNeighborhood_baseChange
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f]
    (V : X.Opens) (hV : IsGreatest {U : X.Opens | Etale (U.ι ≫ f)} V)
    (W : X.Opens) (y : Y) :
    IsGreatest
      {U : (pullback (W.ι ≫ f) (Y.fromSpecStalk y)).Opens |
        Etale (U.ι ≫ pullback.snd (W.ι ≫ f) (Y.fromSpecStalk y))}
      (pullback.fst (W.ι ≫ f) (Y.fromSpecStalk y) ⁻¹ᵁ
        (W.ι ⁻¹ᵁ V)) := by
  have : Flat (Y.fromSpecStalk y) := inferInstance
  have : LocallyOfFinitePresentation (W.ι ≫ f) := inferInstance
  exact isGreatest_etaleOpen_preimage_of_flat_base
    (W.ι ≫ f) (Y.fromSpecStalk y)
    (pullback.fst (W.ι ≫ f) (Y.fromSpecStalk y))
    (pullback.snd (W.ι ≫ f) (Y.fromSpecStalk y))
    (IsPullback.of_hasPullback (W.ι ≫ f) (Y.fromSpecStalk y))
    (W.ι ⁻¹ᵁ V)
    (isGreatest_etaleOpen_preimage_of_isOpenImmersion f W.ι V hV)

private theorem etale_and_quasiCompact_baseChanged_maximalOpen
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (V : X.Opens)
    (hV : IsGreatest {U : X.Opens | Etale (U.ι ≫ f)} V)
    (W : X.Opens) (hW : IsAffineOpen W) (y : Y)
    (B : Y.Opens) (hB : IsAffineOpen B) (hyB : y ∈ B)
    (hWB : W ≤ f ⁻¹ᵁ B) :
    let f₀ := W.ι ≫ f
    let q := pullback.snd f₀ (Y.fromSpecStalk y)
    let U := pullback.fst f₀ (Y.fromSpecStalk y) ⁻¹ᵁ (W.ι ⁻¹ᵁ V)
    Etale (U.ι ≫ q) ∧ QuasiCompact (U.ι ≫ q) := by
  dsimp only
  let f₀ : W.toScheme ⟶ Y := W.ι ≫ f
  let T := pullback f₀ (Y.fromSpecStalk y)
  let q : T ⟶ Spec (CommRingCat.of (Y.presheaf.stalk y)) :=
    pullback.snd f₀ (Y.fromSpecStalk y)
  let U : T.Opens :=
    pullback.fst f₀ (Y.fromSpecStalk y) ⁻¹ᵁ (W.ι ⁻¹ᵁ V)
  have : LocallyOfFinitePresentation f := inferInstance
  have hEtale := (isGreatest_etaleOpen_affineNeighborhood_baseChange
    f V hV W y).1
  have : IsAffine T :=
    isAffine_pullback_of_affine_source_over_target_stalk f y W hW B hB hWB hyB
  have : LocallyOfFiniteType f₀ := inferInstance
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherianRing Γ(T, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top T⟩
  have : NoetherianSpace T := noetherianSpace_of_isAffine
  have : QuasiCompact q := inferInstance
  exact ⟨hEtale, quasiCompact_restrict_of_noetherianSpace q U⟩

private theorem isExcellent_stalk_affineNeighborhood_baseChange
    {X Y : Scheme.{u}}
    (f : X ⟶ Y) (W : X.Opens) (y : Y)
    (hExcellent : ∀ x : X, IsExcellent (X.presheaf.stalk x))
    (t : (pullback (W.ι ≫ f) (Y.fromSpecStalk y) : Scheme.{u})) :
    IsExcellent
      ((pullback (W.ι ≫ f) (Y.fromSpecStalk y)).presheaf.stalk t) := by
  have : Flat (Y.fromSpecStalk y) := inferInstance
  have hExcellentW : ∀ z : W.toScheme,
      IsExcellent (W.toScheme.presheaf.stalk z) :=
    isExcellent_stalk_of_flat_preimmersion W.ι hExcellent
  exact isExcellent_stalk_of_flat_preimmersion
    (pullback.fst (W.ι ≫ f) (Y.fromSpecStalk y)) hExcellentW t

private theorem isExcellent_localization_of_affine_scheme_stalks
    (S : Scheme.{u}) [IsAffine S]
    (hExcellent : ∀ s : S, IsExcellent (S.presheaf.stalk s))
    (p : PrimeSpectrum Γ(S, ⊤)) :
    IsExcellent (Localization.AtPrime p.asIdeal) := by
  have hSpec : IsExcellent
      ((Spec (CommRingCat.of Γ(S, ⊤))).presheaf.stalk p) :=
    isExcellent_stalk_of_flat_preimmersion S.isoSpec.inv hExcellent p
  exact isExcellent_of_commRingCatIso (Spec.stalkIso (CommRingCat.of Γ(S, ⊤)) p) hSpec

private theorem isNormal_localization_of_affine_normal_scheme
    (S : Scheme.{u}) [IsAffine S] [IsNormal S]
    (p : PrimeSpectrum Γ(S, ⊤)) :
    IsNormalRing (Localization.AtPrime p.asIdeal) := by
  have : IsNormal (Spec (CommRingCat.of Γ(S, ⊤))) :=
    isNormal_of_flat_preimmersion S.isoSpec.inv
  let e := (Spec.stalkIso (CommRingCat.of Γ(S, ⊤))
    p).commRingCatIsoToRingEquiv
  let hNorm : IsNormal (Spec (CommRingCat.of Γ(S, ⊤))) :=
    inferInstance
  have : IsDomain ((Spec (CommRingCat.of Γ(S, ⊤))).presheaf.stalk p) :=
    hNorm.stalk_isDomain p
  have : IsIntegrallyClosed
      ((Spec (CommRingCat.of Γ(S, ⊤))).presheaf.stalk p) :=
    hNorm.stalk_normal p
  have : IsDomain (Localization.AtPrime p.asIdeal) :=
    Function.Injective.isDomain e.symm.toRingHom e.symm.injective
  have : IsIntegrallyClosed (Localization.AtPrime p.asIdeal) :=
    IsIntegrallyClosed.of_equiv e
  exact IsNormalRing.of_isIntegrallyClosed _

private theorem exists_affineHom_map_etaleOpen_to_punctured_target
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [LocallyOfFiniteType f] (V W : X.Opens)
    (hW : IsAffineOpen W) (y : Y)
    (B : Y.Opens) (hB : IsAffineOpen B) (hyB : y ∈ B)
    (hWB : W ≤ f ⁻¹ᵁ B)
    (hAvoid : ∀ z : X, z ∈ W → f z = y → z ∉ V)
    (d : ℕ) (hd : ringKrullDim (Y.presheaf.stalk y) =
      (d : WithBot ℕ∞))
    (hsmall : ∀ (z : W.toScheme) (n : ℕ),
      ringKrullDim (Y.presheaf.stalk ((W.ι ≫ f) z)) =
        (n : WithBot ℕ∞) →
      n < d →
      IsAffineOpen
        (W.toScheme.fromSpecStalk z ⁻¹ᵁ (W.ι ⁻¹ᵁ V))) :
    let f₀ := W.ι ≫ f
    let U := pullback.fst f₀ (Y.fromSpecStalk y) ⁻¹ᵁ
      (W.ι ⁻¹ᵁ V)
    ∃ g : U.toScheme ⟶
      (complementZeroLocus (Y.presheaf.stalk y)
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) : Scheme),
      g ≫ (complementZeroLocus (Y.presheaf.stalk y)
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))).ι =
        U.ι ≫ pullback.snd f₀ (Y.fromSpecStalk y) ∧
      IsAffineHom g := by
  dsimp only
  let f₀ : W.toScheme ⟶ Y := W.ι ≫ f
  let T := pullback f₀ (Y.fromSpecStalk y)
  let q : T ⟶ Spec (CommRingCat.of (Y.presheaf.stalk y)) :=
    pullback.snd f₀ (Y.fromSpecStalk y)
  let U : T.Opens :=
    (pullback.fst f₀ (Y.fromSpecStalk y)) ⁻¹ᵁ (W.ι ⁻¹ᵁ V)
  have : IsAffine T :=
    isAffine_pullback_of_affine_source_over_target_stalk f y W hW B hB hWB hyB
  have : LocallyOfFiniteType f₀ := inferInstance
  have : IsLocallyNoetherian T :=
    LocallyOfFiniteType.isLocallyNoetherian q
  have hAway (z : T) (hz : z ∈ U) :
      q z ≠ IsLocalRing.closedPoint (Y.presheaf.stalk y) := by
    intro heq
    have hcomm := apply_pullback_fst_eq_apply_pullback_snd f₀ (Y.fromSpecStalk y) z
    have hy : f (W.ι ((pullback.fst f₀ (Y.fromSpecStalk y)) z)) = y := by
      simpa only [f₀, q, heq, Scheme.fromSpecStalk_closedPoint,
        Scheme.Hom.comp_apply] using hcomm
    exact hAvoid _ ((pullback.fst f₀ (Y.fromSpecStalk y)) z).2 hy hz
  obtain ⟨g, hg⟩ :=
    exists_punctured_target_map_of_no_closed_fiber
      (Y.presheaf.stalk y) q U hAway
  have hAffine :
      IsAffineHom
        ((((pullback.snd f₀ (Y.fromSpecStalk y)) ⁻¹ᵁ
          complementZeroLocus (Y.presheaf.stalk y)
            (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))).ι) ⁻¹ᵁ
          U).ι :=
    isAffineHom_pullback_open_over_punctured_target_of_smaller_stalks
      f₀ (W.ι ⁻¹ᵁ V) y d hd hsmall
  refine ⟨g, hg, ?_⟩
  exact isAffineHom_punctured_target_of_affine_open_restriction
    (Y.presheaf.stalk y) q U g hg hAffine


private theorem exists_nonEtale_codimensionOne_specialization
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] (x : X)
    (hX : IsNormalRing (X.presheaf.stalk x))
    (hY : IsRegularLocalRing (Y.presheaf.stalk (f x)))
    (hpositive : 1 ≤ ringKrullDim (X.presheaf.stalk x))
    (hNotEtale : ¬ EtaleAt f x) :
    ∃ x' : X, Specializes x' x ∧
      ringKrullDim (X.presheaf.stalk x') = 1 ∧
      ¬ EtaleAt f x' := by
  by_contra h
  push Not at h
  exact hNotEtale (AlgebraicGeometry.etaleAt_of_etaleAt_codimensionOne f x hX hY hpositive
    fun x' hspec hdim => h x' hspec hdim)

private theorem one_le_quotient_localization_of_nonEtale_point
    (C : Type u) [CommRing C] [IsNoetherianRing C]
    {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : Spec (.of C) ⟶ Y) [LocallyOfFiniteType f]
    [IsNormal (Spec (.of C))]
    (hYregular : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (V : (Spec (.of C)).Opens)
    (hV : IsGreatest {U : (Spec (.of C)).Opens | Etale (U.ι ≫ f)} V)
    (x : PrimeSpectrum C) (hx : x ∉ V)
    (hdim : 1 < ringKrullDim ((Spec (.of C)).presheaf.stalk x)) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim
      ((Localization.AtPrime x.asIdeal) ⧸
        (PrimeSpectrum.vanishingIdeal (V : Set (Spec (.of C)))ᶜ).map
          (algebraMap C (Localization.AtPrime x.asIdeal))) := by
  have hnot : ¬ EtaleAt f x := fun het => hx ((etaleAt_iff_mem_maximalEtaleOpen f V hV x).mp het)
  obtain ⟨x', hsp, hdimx', hnot'⟩ :=
    exists_nonEtale_codimensionOne_specialization f x
      (normal_stalk_isNormalRingPropForm (X := Spec (.of C)) x)
      (hYregular (f x)) hdim.le hnot
  have hx'V : x' ∉ V := fun hx'V =>
    hnot' ((etaleAt_iff_mem_maximalEtaleOpen f V hV x').mpr hx'V)
  have hneq : x' ≠ x := fun heq => hdim.ne' (heq ▸ hdimx')
  have hlt : (show PrimeSpectrum C from x') < x :=
    lt_of_le_of_ne ((PrimeSpectrum.le_iff_specializes x' x).mpr hsp) hneq
  exact one_le_ringKrullDim_quotient_localization_of_prime_lt C
    (PrimeSpectrum.vanishingIdeal (V : Set (Spec (.of C)))ᶜ) x x'
    (PrimeSpectrum.subset_zeroLocus_vanishingIdeal _ hx'V) hlt

private theorem cohomologicalDimension_le_sub_one_maximalEtaleOpen
    (A C : Type u) [CommRing A] [IsRegularLocalRing A]
    [CommRing C] [IsNoetherianRing C]
    [IsNormal (Spec (.of C))]
    (f : Spec (.of C) ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (U : (Spec (.of C)).Opens)
    (hU : IsGreatest {W : (Spec (.of C)).Opens | Etale (W.ι ≫ f)} U)
    (hExcellent : ∀ p : PrimeSpectrum C,
      IsExcellent (Localization.AtPrime p.asIdeal))
    (hNormal : ∀ p : PrimeSpectrum C,
      IsNormalRing (Localization.AtPrime p.asIdeal))
    (d : ℕ) (hd : 2 ≤ d) (hAdim : ringKrullDim A = (d : WithBot ℕ∞)) :
    Stacks.LocalCohomology.cohomologicalDimension C
      (PrimeSpectrum.vanishingIdeal (U : Set (Spec (.of C)))ᶜ)
      (Ideal.fg_of_isNoetherianRing _) ≤ (d : ℤ) - 1 := by
  classical
  let I := PrimeSpectrum.vanishingIdeal (U : Set (Spec (.of C)))ᶜ
  apply cohomologicalDimension_le_of_forall_localization_le C I
    (Ideal.fg_of_isNoetherianRing I) ((d : ℤ) - 1) (by omega)
  intro p
  let B := Localization.AtPrime p.asIdeal
  let J := I.map (algebraMap C B)
  let hJ : J.FG := (Ideal.fg_of_isNoetherianRing I).map (algebraMap C B)
  show Stacks.LocalCohomology.cohomologicalDimension B J hJ ≤ (d : ℤ) - 1
  let e := (Spec.stalkIso (CommRingCat.of C) p).commRingCatIsoToRingEquiv
  have : IsDomain ((Spec (.of C)).presheaf.stalk p) :=
    IsNormal.stalk_isDomain (X := Spec (.of C)) p
  have : IsDomain B := Function.Injective.isDomain e.symm.toRingHom e.symm.injective
  by_cases hp : p ∈ U
  · have hUI : complementZeroLocus C I = U := complementZeroLocus_vanishingIdeal_compl C U
    have hp' : p ∈ complementZeroLocus C I := by rwa [hUI]
    have hnot : ¬ I ≤ p.asIdeal := hp'
    obtain ⟨a, ha, han⟩ := SetLike.not_le_iff_exists.mp hnot
    have htop : J = ⊤ := Ideal.eq_top_of_isUnit_mem J
      (Ideal.mem_map_of_mem _ ha) (IsLocalization.map_units B (⟨a, han⟩ : p.asIdeal.primeCompl))
    have hzero : Stacks.LocalCohomology.cohomologicalDimension B J hJ ≤ 0 :=
      cohomologicalDimension_le_zero_of_isClopen_zeroLocus B J hJ (by
        rw [htop]; simpa using isClopen_empty (X := PrimeSpectrum B))
    omega
  · let w : PrimeSpectrum C := PrimeSpectrum.comap (algebraMap C B) ⊥
    by_cases hw : w ∈ U
    · have hwp : w ≤ p :=
        ((IsLocalization.AtPrime.primeSpectrumOrderIso B p.asIdeal) ⊥).2
      have : IsDomain A := IsRegularLocalRing.isDomain A
      have hdim := localDimension_le_of_etale_generization f U hU.1 p w hw
        ((PrimeSpectrum.le_iff_specializes w p).mp hwp)
      obtain ⟨m, hm, hmd⟩ := local_dimension_bound_of_local_ring A d d hAdim le_rfl (f p)
      have htarget : ringKrullDim ((Spec (.of A)).presheaf.stalk (f p)) =
          (m : WithBot ℕ∞) :=
        (ringKrullDim_eq_of_ringEquiv
          (Spec.stalkIso (CommRingCat.of A) (f p)).commRingCatIsoToRingEquiv).trans hm
      obtain ⟨n, hn⟩ := Stacks.ApproximationProperty.exists_natCast_eq_ringKrullDim B
      have hsource : ringKrullDim ((Spec (.of C)).presheaf.stalk p) =
          (n : WithBot ℕ∞) := (ringKrullDim_eq_of_ringEquiv e).trans hn
      rw [hsource, htarget] at hdim
      have hnd : n ≤ d := (by exact_mod_cast hdim : n ≤ m).trans hmd
      by_cases hnsmall : n ≤ 1
      · have hle := cohomologicalDimension_le_of_isLocalRing B J hJ n hn.le
        omega
      · have hregular (q : Spec (.of A)) :
            IsRegularLocalRing ((Spec (.of A)).presheaf.stalk q) := by
          have := isRegularLocalRing_localizationAtPrime A q
          exact IsRegularLocalRing.of_ringEquiv
            (Spec.stalkIso (CommRingCat.of A) q).commRingCatIsoToRingEquiv.symm
        have hpositive := one_le_quotient_localization_of_nonEtale_point C f
          hregular U hU p hp (by rw [hsource]; exact_mod_cast (by omega : 1 < n))
        have hlt := cohomologicalDimension_lt_of_isExcellent_of_isNormalRing B
          (hExcellent p) (hNormal p) n hn J hpositive
        change Stacks.LocalCohomology.cohomologicalDimension B J hJ < (n : ℤ) at hlt
        omega
    · have hbot : J = ⊥ := vanishingIdeal_compl_map_eq_bot_of_generic_not_mem C U p hw
      have hzero : Stacks.LocalCohomology.cohomologicalDimension B J hJ ≤ 0 :=
        cohomologicalDimension_le_zero_of_isClopen_zeroLocus B J hJ (by
          rw [hbot]; simpa using isClopen_univ (X := PrimeSpectrum B))
      omega

private theorem isAffineOpen_maximalEtaleOpen_of_affine_over_punctured_base
    (A k : Type u) [CommRing A] [IsRegularLocalRing A]
    [Field k] [Algebra k A]
    {X : Scheme.{u}} [IsAffine X] [IsLocallyNoetherian X] [IsNormal X]
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (V : X.Opens) (hV : IsGreatest {W : X.Opens | Etale (W.ι ≫ f)} V)
    [QuasiCompact (V.ι ≫ f)]
    (hExcellent : ∀ x : X, IsExcellent (X.presheaf.stalk x))
    (g : V.toScheme ⟶ (complementZeroLocus A (IsLocalRing.maximalIdeal A)).toScheme)
    [IsAffineHom g]
    (hg : g ≫ (complementZeroLocus A (IsLocalRing.maximalIdeal A)).ι = V.ι ≫ f)
    (d : ℕ) (hd : 2 ≤ d) (hAdim : ringKrullDim A = (d : WithBot ℕ∞)) :
    IsAffineOpen V := by
  let C := Γ(X, ⊤)
  have : IsNoetherianRing C := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let j := X.isoSpec.inv
  let U : (Spec (.of C)).Opens := j ⁻¹ᵁ V
  let f' := j ≫ f
  let e : U.toScheme ⟶ V.toScheme := j ∣_ V
  have : IsIso e := by dsimp [e, j]; infer_instance
  have he : e ≫ V.ι = U.ι ≫ j := morphismRestrict_ι j V
  have hU := isGreatest_etaleOpen_preimage_of_isOpenImmersion f j V hV
  have : IsNormal (Spec (.of C)) := isNormal_of_flat_preimmersion j
  have hcd := cohomologicalDimension_le_sub_one_maximalEtaleOpen A C f' U hU
    (isExcellent_localization_of_affine_scheme_stalks X hExcellent)
    (isNormal_localization_of_affine_normal_scheme X) d hd hAdim
  have hEt : Etale (V.ι ≫ f) := hV.1
  have heF : e ≫ (V.ι ≫ f) = U.ι ≫ f' := by rw [← Category.assoc, he]; rfl
  have : Etale (U.ι ≫ f') := by rw [← heF]; infer_instance
  have : QuasiCompact (U.ι ≫ f') := by rw [← heF]; infer_instance
  have hUaff : IsAffine U.toScheme := by
    apply isAffine_of_etale_over_regularLocal_complement_of_Hgroup_vanishing
      A k (U.ι ≫ f') (e ≫ g) (by rw [Category.assoc, hg, heF])
    intro n hn
    let I := PrimeSpectrum.vanishingIdeal (U : Set (Spec (.of C)))ᶜ
    have hUI : complementZeroLocus C I = U := complementZeroLocus_vanishingIdeal_compl C U
    have hqc :
        (SheafOfModules.unit (complementZeroLocus C I).toScheme.ringCatSheaf).IsQuasicoherent := by
      let S := (complementZeroLocus C I).toScheme
      let eUnit : SheafOfModules.free (R := S.ringCatSheaf) PUnit.{u + 1} ≅
          SheafOfModules.unit S.ringCatSheaf :=
        Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit S.ringCatSheaf)
      exact (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso eUnit inferInstance
    have hn' : (d : ℤ) - 1 ≤ (n : ℤ) := by
      rw [hAdim] at hn
      norm_num at hn
      omega
    have hv := hgroup_isZero_of_cohomologicalDimension_le C I
      (Ideal.fg_of_isNoetherianRing I) ((d : ℤ) - 1) (by omega) hcd
      (SheafOfModules.unit (complementZeroLocus C I).toScheme.ringCatSheaf) hqc n hn'
    rwa [hUI] at hv
  exact (IsAffine.iff_of_isIso e).mp hUaff

private theorem isAffine_complementZeroLocus_maximalIdeal_of_ringKrullDim_le_one
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (h : ringKrullDim A ≤ 1) :
    IsAffine (complementZeroLocus A (IsLocalRing.maximalIdeal A)).toScheme := by
  have : IsDomain A := IsRegularLocalRing.isDomain A
  have : Ring.KrullDimLE 1 A := Ring.krullDimLE_iff.mpr (by exact_mod_cast h)
  exact isAffineOpen_of_local_domain_krullDimLE_one A _
    fun h => (mem_complementZeroLocus_maximalIdeal_iff A _).mp h rfl

private theorem isAffineOpen_fromSpecStalk_preimage_of_isAffineHom_baseChange
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V W : X.Opens) (x : X) (hxW : x ∈ W)
    (hU : IsAffineHom (pullback.fst (W.ι ≫ f) (Y.fromSpecStalk (f x)) ⁻¹ᵁ (W.ι ⁻¹ᵁ V)).ι) :
    IsAffineOpen (X.fromSpecStalk x ⁻¹ᵁ V) := by
  let f₀ := W.ι ≫ f
  let T := pullback f₀ (Y.fromSpecStalk (f x))
  let p : T ⟶ W.toScheme := pullback.fst f₀ (Y.fromSpecStalk (f x))
  let U : T.Opens := p ⁻¹ᵁ (W.ι ⁻¹ᵁ V)
  have : IsAffineHom U.ι := hU
  let xW : W.toScheme := ⟨x, hxW⟩
  let a : Spec (W.toScheme.presheaf.stalk xW) ⟶ T :=
    pullback.lift (W.toScheme.fromSpecStalk xW)
      (Spec.map (f₀.stalkMap xW)) (Scheme.SpecMap_stalkMap_fromSpecStalk f₀).symm
  have ha := isAffineOpen_preimage_of_isAffineHom_inclusion a U
  change IsAffineOpen (a ⁻¹ᵁ (p ⁻¹ᵁ (W.ι ⁻¹ᵁ V))) at ha
  have hafst : a ≫ p = W.toScheme.fromSpecStalk xW := pullback.lift_fst _ _ _
  rw [← Scheme.Hom.comp_preimage, hafst] at ha
  have heq : Spec.map (W.ι.stalkMap xW) ⁻¹ᵁ (X.fromSpecStalk x ⁻¹ᵁ V) =
      W.toScheme.fromSpecStalk xW ⁻¹ᵁ (W.ι ⁻¹ᵁ V) := by
    show (Spec.map (W.ι.stalkMap xW) ≫ X.fromSpecStalk (W.ι xW)) ⁻¹ᵁ V =
      (W.toScheme.fromSpecStalk xW ≫ W.ι) ⁻¹ᵁ V
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk]
  have hpre : IsAffineOpen (Spec.map (W.ι.stalkMap xW) ⁻¹ᵁ (X.fromSpecStalk x ⁻¹ᵁ V)) := by
    rwa [heq]
  have hi := hpre.preimage (inv (Spec.map (W.ι.stalkMap xW)))
  rw [← Scheme.Hom.comp_preimage, IsIso.inv_hom_id] at hi
  simpa [xW] using hi

private theorem isAffineOpen_stalk_maximalEtaleOpen
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsNormal X]
    (f : X ⟶ Y) [LocallyOfFiniteType f]
    (hY : ∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y))
    (hExcellent : ∀ x : X, IsExcellent (X.presheaf.stalk x))
    (k : Type u) [Field k] (g : Y ⟶ Spec (.of k))
    (V : X.Opens) (hV : IsGreatest {U : X.Opens | Etale (U.ι ≫ f)} V)
    (x : X) : IsAffineOpen (X.fromSpecStalk x ⁻¹ᵁ V) := by
  classical
  have hAll : ∀ d : ℕ, ∀ x : X,
      ringKrullDim (Y.presheaf.stalk (f x)) = (d : WithBot ℕ∞) →
      IsAffineOpen (X.fromSpecStalk x ⁻¹ᵁ V) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro x hdim
      by_cases hx : x ∈ V
      · have htop : X.fromSpecStalk x ⁻¹ᵁ V = ⊤ :=
          Scheme.preimage_eq_top_of_closedPoint_mem (f := X.fromSpecStalk x)
            (by simpa only [Scheme.fromSpecStalk_closedPoint] using hx)
        rw [htop]
        exact isAffineOpen_top _
      · obtain ⟨B, hB, hyB, -⟩ := exists_isAffineOpen_mem_and_subset
          (X := Y) (U := ⊤) (x := f x) (by trivial)
        obtain ⟨W, hxW, hW, hWB, hAvoid⟩ :=
          exists_affine_open_avoiding_etale_fiber_in_target_open
            f V hV x hx B hyB
        let A := Y.presheaf.stalk (f x)
        have : IsRegularLocalRing A := hY (f x)
        let : Algebra k A := algebraStalkOfOverField k g (f x)
        let f₀ := W.ι ≫ f
        let T := pullback f₀ (Y.fromSpecStalk (f x))
        let q : T ⟶ Spec (.of A) := pullback.snd f₀ (Y.fromSpecStalk (f x))
        let p : T ⟶ W.toScheme := pullback.fst f₀ (Y.fromSpecStalk (f x))
        let U : T.Opens := p ⁻¹ᵁ (W.ι ⁻¹ᵁ V)
        have : IsAffine T :=
          isAffine_pullback_of_affine_source_over_target_stalk f (f x) W hW B hB hWB hyB
        have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian q
        have : IsNormal W.toScheme := isNormal_of_flat_preimmersion W.ι
        have : IsNormal T := isNormal_pullback_fromSpecStalk f₀ (f x)
        have : LocallyOfFinitePresentation f := inferInstance
        have hU := isGreatest_etaleOpen_affineNeighborhood_baseChange f V hV W (f x)
        obtain ⟨hEt, hQC⟩ := etale_and_quasiCompact_baseChanged_maximalOpen
          f V hV W hW (f x) B hB hyB hWB
        have : Etale (U.ι ≫ q) := hEt
        have : QuasiCompact (U.ι ≫ q) := hQC
        obtain ⟨gP, hgP, hgAff⟩ := exists_affineHom_map_etaleOpen_to_punctured_target
          f V W hW (f x) B hB hyB hWB hAvoid d hdim (by
            intro z n hn hnd
            exact isAffineOpen_stalk_preimage_of_flat_preimmersion W.ι V z
              (ih n hnd (W.ι z) hn))
        have : IsAffineHom gP := hgAff
        have hAffineU : IsAffine U.toScheme := by
          by_cases hd : 2 ≤ d
          · exact isAffineOpen_maximalEtaleOpen_of_affine_over_punctured_base A k q U hU
              (fun t => isExcellent_stalk_affineNeighborhood_baseChange
                f W (f x) hExcellent t) gP hgP d hd hdim
          · have := isAffine_complementZeroLocus_maximalIdeal_of_ringKrullDim_le_one A (by
              rw [hdim]; exact_mod_cast (by omega : d ≤ 1))
            exact isAffine_of_isAffineHom gP
        have : IsAffineHom U.ι := inferInstance
        exact isAffineOpen_fromSpecStalk_preimage_of_isAffineHom_baseChange f V W x hxW this
  obtain ⟨d, hd⟩ :=
    Stacks.ApproximationProperty.exists_natCast_eq_ringKrullDim (Y.presheaf.stalk (f x))
  exact hAll d x hd

/-- **Stacks Project, Tag 0ECD.** Let `Y` be an excellent regular scheme over a field `k`, let
`f : X ⟶ Y` be a morphism of finite type with `X` normal, and let `V ⊆ X` be the maximal open
subscheme on which `f` is étale. Then the inclusion `V ⟶ X` is affine.

`Y` regular is `AlgebraicGeometry.IsRegular` ([Stacks, Tag 02IS]); `Y` excellent is the existence
around every point of an affine open neighbourhood whose ring of sections is excellent, which is
the definition of an excellent scheme; `Y` over a field is a morphism `g : Y ⟶ Spec k`; finite
type is `LocallyOfFiniteType` with `QuasiCompact`; `X` normal is `AlgebraicGeometry.IsNormal`
([Stacks, Tag 033I]); and "the maximal open subscheme where `f` is étale" is an open `V` that is
the greatest element of the set of opens `U` with `U.ι ≫ f` étale. The proof uses purity of the
ramification locus, `AlgebraicGeometry.etaleAt_of_etaleAt_codimensionOne` ([Stacks, Tag 0EA4]),
and [Stacks, Tag 0ECC], `Stacks.PuncturedSpectrum.isAffine_of_cohomologyOverBase_vanishing`; see
the module documentation. Quasi-compactness of `f` is not used by the argument. -/
@[stacks 0ECD, ega "IV 21.12.14" "special case"]
theorem isAffineHom_maximalEtaleOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsNormal X]
    (hYregular : IsRegular Y)
    (hYexcellent : ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧ IsExcellent Γ(Y, U))
    (k : Type u) [Field k] (g : Y ⟶ Spec (.of k))
    (V : X.Opens) (hV : IsGreatest {U : X.Opens | Etale (U.ι ≫ f)} V) :
    IsAffineHom V.ι := by
  have hY := ((AlgebraicGeometry.isRegular_tfae Y).out 1 2).mp hYregular
  have : IsLocallyNoetherian Y := hY.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact isAffineHom_of_affine_stalk_preimages V (isAffineOpen_stalk_maximalEtaleOpen f hY.2
    (isExcellent_stalk_of_locallyOfFiniteType f hYexcellent) k g V hV)

end AlgebraicGeometry.MaximalEtaleOpen

end
