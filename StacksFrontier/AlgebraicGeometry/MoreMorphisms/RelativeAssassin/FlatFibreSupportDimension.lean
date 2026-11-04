module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.MinimalSupport
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.ClosureRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.RingTheory.Support.GoingDown
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType
public import StacksFrontier.Topology.Sheaves.Modules.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections

/-!
# Dimension of the support of a flat module on the fibres

Let `f : X ⟶ S` be locally of finite type with `S` irreducible of generic point `η`, and let `F`
be a quasi-coherent `𝒪_X`-module of finite type which is flat over `S`. If the support of `F` on
the generic fibre has dimension at most `r`, then so does its support on every fibre.

## Main results

* `Stacks.RelativeAssassin.topologicalKrullDim_supp_fiber_le_of_generic` bounds the dimension of
  the support of the module on every fibre by its bound on the generic fibre.

## Implementation notes

The module on a fibre is its pullback along the canonical immersion of the fibre into `X`; its
support carries the subspace topology and its dimension is the topological Krull dimension, with
values in `WithBot ℕ∞`. The lifting of a point of the support against the base is the going-down
property of the support map of a finite flat module, Tag 080T, read on a pair of affine opens.

## References

* [Stacks Project, Tag 0H3X](https://stacks.math.columbia.edu/tag/0H3X)
* [Stacks Project, Tag 080T](https://stacks.math.columbia.edu/tag/080T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.RelativeAssassin

/-- Being of finite type is invariant under isomorphism of modules on a scheme. -/
private lemma isFiniteType_of_modules_iso {X : Scheme.{u}} {F G : X.Modules}
    (e : F ≅ G) [hF : SheafOfModules.IsFiniteType.{u, u, u} F] :
    SheafOfModules.IsFiniteType.{u, u, u} G := by
  obtain ⟨σ, hσ⟩ : ∃ σ : F.LocalGeneratorsData.{u, u, u, u},
      SheafOfModules.LocalGeneratorsData.IsFiniteType.{u, u, u, u} σ :=
    hF.exists_localGeneratorsData
  let τ : G.LocalGeneratorsData.{u, u, u, u} := {
    I := σ.I
    X := σ.X
    coversTop := σ.coversTop
    generators i :=
      (σ.generators i).ofEpi ((SheafOfModules.overFunctor X.ringCatSheaf (σ.X i)).mapIso e).hom
  }
  exact SheafOfModules.IsFiniteType.mk.{u, u, u}
    ⟨τ, SheafOfModules.LocalGeneratorsData.IsFiniteType.mk.{u, u, u, u} fun i => by
      have := hσ.isFiniteType i
      infer_instance⟩

/-- A quasi-coherent module of finite type on an affine scheme has a finite module of global
sections. -/
private lemma moduleFinite_of_isQuasicoherent_isFiniteType (R : CommRingCat.{u})
    (F : (Spec R).Modules) [F.IsQuasicoherent] [F.IsFiniteType] :
    Module.Finite (↑R) (AlgebraicGeometry.moduleSpecΓFunctor.obj F) :=
  (AlgebraicGeometry.tilde_isFiniteType_iff _).mp
    (isFiniteType_of_modules_iso (asIso F.fromTildeΓ).symm)

/-- The sections of a quasi-coherent module of finite type over an affine open form a finite
module over the ring of functions on that open. -/
private lemma moduleFinite_sections {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (U : X.affineOpens) :
    Module.Finite Γ(X, U.1) Γ(F, U.1) := by
  let f := U.2.fromSpec
  have : IsOpenImmersion f := U.2.isOpenImmersion_fromSpec
  let G := F.restrict f
  have : G.IsQuasicoherent := Scheme.Modules.isQuasicoherent_restrictFunctor f F
  have : ((Scheme.Modules.pullback f).obj F).IsFiniteType :=
    AlgebraicGeometry.SheafOfModules.pullback_isFiniteType f.toLRSHom.toShHom F
  have : G.IsFiniteType :=
    isFiniteType_of_modules_iso ((Scheme.Modules.restrictFunctorIsoPullback f).app F).symm
  have : Module.Finite Γ(X, U.1) Γ(G, ⊤) :=
    moduleFinite_of_isQuasicoherent_isFiniteType (CommRingCat.of Γ(X, U.1)) G
  exact Module.Finite.of_surjective (affineSectionsLinearEquiv F U.2).toLinearMap
    (affineSectionsLinearEquiv F U.2).surjective

/-- **Going down for the sections of a flat module.** On affine opens `U ≤ f ⁻¹ᵁ V`, the prime of
a point `x` of the support generalizes to a prime of the support of the sections lying over the
prime of a generalization `η ∈ V` of `f x`. -/
private theorem exists_le_primeIdealOf_mem_support
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (hF : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F)
    {U : X.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V)
    (hVU : U ≤ f ⁻¹ᵁ V) {η : S} (hηV : η ∈ V) {x : X} (hxU : x ∈ U)
    (hx : x ∈ SheafOfModules.supp F) (hηx : η ⤳ f x) :
    ∃ q : PrimeSpectrum Γ(X, U), q ∈ Module.support Γ(X, U) Γ(F, U) ∧
      q ≤ hU.primeIdealOf ⟨x, hxU⟩ ∧
      PrimeSpectrum.comap (f.appLE V U hVU).hom q = hV.primeIdealOf ⟨η, hηV⟩ := by
  classical
  let A := Γ(S, V)
  let B := Γ(X, U)
  let N := Γ(F, U)
  let φ := (f.appLE V U hVU).hom
  let : Algebra A B := φ.toAlgebra
  let : Module A N := Module.compHom N φ
  have : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hcrit : ∀ (W : X.Opens), IsAffineOpen W → ∀ (Z : S.Opens),
      IsAffineOpen Z → ∀ (hWZ : W ≤ f ⁻¹ᵁ Z),
        let : Module Γ(S, Z) Γ(F, W) :=
          Module.compHom Γ(F, W) (f.appLE Z W hWZ).hom
        Module.Flat Γ(S, Z) Γ(F, W) :=
    ((AlgebraicGeometry.isFlatOver_tfae f F).out 1 2).mp hF
  let q' := hU.primeIdealOf ⟨x, hxU⟩
  have hq' : q' ∈ Module.support B N :=
    (AlgebraicGeometry.Scheme.Modules.mem_support_sections_iff_mem_supp F ⟨U, hU⟩ x hxU).mpr hx
  have hq'p : PrimeSpectrum.comap φ q' = hV.primeIdealOf ⟨f x, hVU hxU⟩ :=
    IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hVU hxU
  let pη := hV.primeIdealOf ⟨η, hηV⟩
  have : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  have hspec : pη ⤳ hV.primeIdealOf ⟨f x, hVU hxU⟩ := by
    apply hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp
    simpa [pη, hV.fromSpec_primeIdealOf] using hηx
  have hbase : pη ⤳ suppMap (R := A) (S := B) (N := N) ⟨q', hq'⟩ := by
    show pη ⤳ PrimeSpectrum.comap φ q'
    rwa [hq'p]
  have : Module.Flat A N := hcrit U hU V hV hVU
  have : Module.Finite B N := moduleFinite_sections F ⟨U, hU⟩
  obtain ⟨qsub, hqsub, hqmap⟩ :=
    generalizingMap_suppMap (R := A) (S := B) (N := N) (a := ⟨q', hq'⟩) (b := pη) hbase
  refine ⟨qsub.1, qsub.2, (PrimeSpectrum.le_iff_specializes _ _).mpr
    ((subtype_specializes_iff qsub ⟨q', hq'⟩).mp hqsub), ?_⟩
  change PrimeSpectrum.comap (algebraMap A B) qsub.1 = pη at hqmap
  show PrimeSpectrum.comap φ qsub.1 = pη
  simpa [A, B, RingHom.algebraMap_toAlgebra φ] using hqmap

/-- **Going down for the support of a flat module.** For a quasi-coherent module of finite type
flat over an irreducible base, every point of the support is a specialization of a point of the
support lying over the generic point of the base. -/
private theorem exists_generalization_in_supp
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] (hF : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F)
    [IrreducibleSpace S] (η : S) (hη : IsGenericPoint η Set.univ)
    (x : X) (hx : x ∈ SheafOfModules.supp F) :
    ∃ y : X, y ⤳ x ∧ f y = η ∧ y ∈ SheafOfModules.supp F := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hsV (f ⁻¹ᵁ V).2
  have hηx : η ⤳ f x := hη.specializes (Set.mem_univ (f x))
  have hηV : η ∈ V := hηx.mem_open V.2 hsV
  obtain ⟨q, hqN, hqle, hcomap⟩ :=
    exists_le_primeIdealOf_mem_support f F hF hU hV hVU hηV hxU hx hηx
  let y := hU.fromSpec q
  have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  have hyU : y ∈ U := by
    rw [← hU.opensRange_fromSpec]
    exact ⟨q, rfl⟩
  have hqdef : hU.primeIdealOf ⟨y, hyU⟩ = q := by
    apply hU.fromSpec.isOpenEmbedding.injective
    rw [hU.fromSpec_primeIdealOf]
  have hprime : hV.primeIdealOf ⟨f y, hVU hyU⟩ = hV.primeIdealOf ⟨η, hηV⟩ := by
    rw [← hcomap, ← hqdef]
    exact (IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hVU hyU).symm
  have hxdef : hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) = x :=
    hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  refine ⟨y, ?_, ?_, ?_⟩
  · rw [← hxdef]
    exact (PrimeSpectrum.le_iff_specializes _ _).mp hqle |>.map hU.fromSpec.continuous
  · exact (hV.fromSpec_primeIdealOf ⟨f y, hVU hyU⟩).symm.trans
      ((congrArg hV.fromSpec hprime).trans (hV.fromSpec_primeIdealOf ⟨η, hηV⟩))
  · rw [← SheafOfModules.supp_eq_moduleSheaf_supp (F := F)]
    exact (AlgebraicGeometry.Scheme.Modules.mem_support_sections_iff_mem_supp F ⟨U, hU⟩ y hyU).mp
      (by rwa [hqdef])

/-- A point of a fibre maps to the point the fibre is taken over. -/
private lemma fiberι_point_maps_to_base {X S : Scheme.{u}}
    (f : X ⟶ S) (s : S) (x : f.fiber s) :
    f (f.fiberι s x) = s := by
  simpa [Scheme.Hom.comp_apply] using
    congrArg (fun k : f.fiber s ⟶ S => k x) (Scheme.Hom.fiber_fac f s)

/-- Two embedded spaces compare in dimension when the range of one is contained in the range of
the other. -/
private theorem topologicalKrullDim_le_of_range_subset
    {A B X : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X]
    (eA : A → X) (eB : B → X)
    (hA : Topology.IsEmbedding eA) (hB : Topology.IsEmbedding eB)
    (hsub : Set.range eA ⊆ Set.range eB) :
    topologicalKrullDim A ≤ topologicalKrullDim B := by
  calc
    topologicalKrullDim A = topologicalKrullDim (Set.range eA) :=
      IsHomeomorph.topologicalKrullDim_eq _ hA.toHomeomorph.isHomeomorph
    _ ≤ topologicalKrullDim (Set.range eB) :=
      (Topology.IsEmbedding.inclusion hsub).isInducing.topologicalKrullDim_le
    _ = topologicalKrullDim B :=
      (IsHomeomorph.topologicalKrullDim_eq _ hB.toHomeomorph.isHomeomorph).symm

/-- A point of the support of a module lying over `s` is the image of a point of the support of
its pullback to the fibre over `s`. -/
private lemma exists_mem_supp_pullback_fiberι {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [F.IsFiniteType] {s : S} {y : X} (hy : y ∈ SheafOfModules.supp F)
    (hys : f y = s) :
    ∃ u ∈ SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F),
      f.fiberι s u = y := by
  obtain ⟨u, rfl⟩ : ∃ u : f.fiber s, f.fiberι s u = y :=
    ⟨(f.fiberHomeo s).symm ⟨y, by simp [hys]⟩, by simp⟩
  refine ⟨u, ?_, rfl⟩
  rwa [Stacks.Modules.supp_pullback]

/-- A point specializing to the generic point of an irreducible component is that generic
point. -/
private lemma eq_of_specializes_of_isGenericPoint {α : Type*} [TopologicalSpace α] [T0Space α]
    {Z : Set α} (hZ : Z ∈ irreducibleComponents α) {z w : α} (hz : IsGenericPoint z Z)
    (hwz : w ⤳ z) : w = z := by
  have hZsub : Z ⊆ closure ({w} : Set α) := by
    rw [← hz.def]
    exact closure_minimal
      (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hwz)) isClosed_closure
  have hw : IsGenericPoint w Z := by
    rw [← (hZ.2 isIrreducible_singleton.closure hZsub).antisymm hZsub]
    exact isGenericPoint_closure
  exact (hz.eq hw).symm

/-- For a quasi-coherent module of finite type flat over an irreducible base, every point of the
support specializes from a point of the relative assassin on the generic fibre. -/
theorem exists_fiberι_mem_relativeAssassin_specializes
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (hF : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F)
    [IrreducibleSpace S] (η : S) (hη : IsGenericPoint η Set.univ)
    (x : X) (hx : x ∈ SheafOfModules.supp F) :
    ∃ z : f.fiber η, z ∈ SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι η)).obj F) ∧
      f.fiberι η z ∈ Stacks.Divisors.relativeAssassin f F ∧ f.fiberι η z ⤳ x := by
  classical
  obtain ⟨y, hyx, hyη, hySupp⟩ := exists_generalization_in_supp f F hF η hη x hx
  let Fη := (Scheme.Modules.pullback (f.fiberι η)).obj F
  have : Fη.IsFiniteType := AlgebraicGeometry.SheafOfModules.pullback_isFiniteType
    (f.fiberι η).toLRSHom.toShHom F
  have : Fη.IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback (f.fiberι η) F inferInstance
  let Pη : Set (f.fiber η) := SheafOfModules.supp Fη
  have : QuasiSober Pη :=
    (SheafOfModules.isClosed_supp Fη).isClosedEmbedding_subtypeVal.quasiSober
  obtain ⟨u, hu, rfl⟩ := exists_mem_supp_pullback_fiberι f F hySupp hyη
  let uP : Pη := ⟨u, hu⟩
  obtain ⟨Z, hZ, hZsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({uP} : Set Pη)) isIrreducible_singleton.closure
  let zP : Pη := genericPoints.ofComponent ⟨Z, hZ⟩
  have hzGen : IsGenericPoint zP Z := genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩
  have : LocallyOfFiniteType (f.fiberToSpecResidueField η) :=
    inferInstanceAs (LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd f (S.fromSpecResidueField η)))
  have : IsLocallyNoetherian (f.fiber η) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField η)
  have hzAssoc : zP.1 ∈ Stacks.Divisors.associatedPoints Fη :=
    AlgebraicGeometry.mem_associatedPoints_of_mem_supp_of_specialization
      (f.fiber η) Fη zP.1 zP.2 fun w hw hspec => congrArg Subtype.val
        (eq_of_specializes_of_isGenericPoint hZ hzGen
          ((subtype_specializes_iff ⟨w, hw⟩ zP).mpr hspec))
  refine ⟨zP.1, zP.2, ?_, ?_⟩
  · rw [Stacks.Divisors.mem_relativeAssassin]
    exact ⟨η, zP.1, hzAssoc, rfl⟩
  · exact ((hzGen.specializes (hZsub (subset_closure rfl))).map
      ((f.fiberι η).continuous.comp continuous_subtype_val)).trans hyx

/-- The fibres of the closure of a point of the relative assassin over the generic point of the
base all have the same dimension, at every point of the base under the closure. -/
private theorem exists_topologicalKrullDim_fiber_closure
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (hF : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F)
    (η : S) (hη : IsGenericPoint η Set.univ)
    (z : X) (hz : z ∈ Stacks.Divisors.relativeAssassin f F) (hzη : f z = η) :
    ∃ d : ℕ, ∀ v : S, ∀ w ∈ closure ({z} : Set X), f w = v →
      topologicalKrullDim (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({z} : Set X))).subschemeι ≫ f).fiber v) = (d : WithBot ℕ∞) := by
  classical
  let Y := Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure ({z} : Set X))
  let T := Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure ({f z} : Set S))
  let h : Y.subscheme ⟶ T.subscheme :=
    Scheme.IdealSheafData.subschemeMap Y T f (by
      rw [Scheme.IdealSheafData.map_vanishingIdeal]
      apply le_of_eq
      apply congrArg Scheme.IdealSheafData.vanishingIdeal
      apply Closeds.ext
      show closure ({f z} : Set S) = closure (f '' closure ({z} : Set X))
      exact ((closure_image_closure f.continuous).trans (by simp)).symm)
  let g : Y.subscheme ⟶ S := Y.subschemeι ≫ f
  have hcomp : h ≫ T.subschemeι = g := by
    rw [Scheme.IdealSheafData.subschemeMap_subschemeι]
  have : LocallyOfFiniteType (h ≫ T.subschemeι) := by
    rw [Scheme.IdealSheafData.subschemeMap_subschemeι]
    infer_instance
  have : LocallyOfFiniteType h := locallyOfFiniteType_of_comp h T.subschemeι
  obtain ⟨d, hd⟩ :=
    relativeDimension_closureSubschemeMap f F z hz (fun _ _ _ => hF _)
  have hYsupport : (Y.support : Set X) = closure ({z} : Set X) := by
    simp [Y]
  have hTsupport : (T.support : Set S) = closure ({f z} : Set S) := by
    simp [T]
  have hTrange : Set.range T.subschemeι = Set.univ := by
    rw [T.range_subschemeι, hTsupport, hzη, hη.def]
  refine ⟨d, fun v w hw hwv => ?_⟩
  obtain ⟨t, ht⟩ := Set.mem_range.mp (hTrange ▸ Set.mem_univ v)
  let e := fiberHomeomorphOfFactor h T.subschemeι g hcomp
    T.subschemeι.isClosedEmbedding.injective t
  rw [← hYsupport, ← Y.range_subschemeι] at hw
  obtain ⟨q, hq⟩ := hw
  have hqv : g q = v := by
    show f (Y.subschemeι q) = v
    rwa [hq]
  let qv : g.fiber v := (g.fiberHomeo v).symm ⟨q, hqv⟩
  calc
    topologicalKrullDim (g.fiber v) =
        topologicalKrullDim (g.fiber (T.subschemeι t)) := by rw [ht]
    _ = topologicalKrullDim (h.fiber t) :=
      (IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph).symm
    _ = (d : WithBot ℕ∞) := (hd t ⟨e.symm (ht.symm ▸ qv)⟩).2

/-- The fibre over `s` of the closure of a point of the support has dimension at most that of
the support of the module on the fibre over `s`. -/
private theorem topologicalKrullDim_fiber_closure_le {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) [F.IsFiniteType] {z : X} (hz : z ∈ SheafOfModules.supp F) (s : S) :
    topologicalKrullDim (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({z} : Set X))).subschemeι ≫ f).fiber s) ≤
      topologicalKrullDim
        (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) := by
  let Y := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))
  let g : Y.subscheme ⟶ S := Y.subschemeι ≫ f
  have hYsupport : (Y.support : Set X) = closure ({z} : Set X) := by
    simp [Y]
  refine topologicalKrullDim_le_of_range_subset
    (fun q : g.fiber s => Y.subschemeι (g.fiberι s q))
    (fun q : SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F) =>
      f.fiberι s q.1)
    (Y.subschemeι.isClosedEmbedding.isEmbedding.comp (g.fiberι s).isEmbedding)
    ((f.fiberι s).isEmbedding.comp Topology.IsEmbedding.subtypeVal) ?_
  rintro _ ⟨q, rfl⟩
  have hYmem : Y.subschemeι (g.fiberι s q) ∈ (Y.support : Set X) := by
    rw [← Y.range_subschemeι]
    exact ⟨g.fiberι s q, rfl⟩
  obtain ⟨v, hv, hvq⟩ := exists_mem_supp_pullback_fiberι f F
    (closure_minimal (Set.singleton_subset_iff.mpr hz) (SheafOfModules.isClosed_supp F)
      (hYsupport ▸ hYmem))
    (fiberι_point_maps_to_base g s q)
  exact ⟨⟨v, hv⟩, hvq⟩

/-- A space embedded in the fibre over `s` into the closure of a point `z` has dimension at most
that of the fibre over `s` of the closure of `z`. -/
private theorem topologicalKrullDim_le_fiber_closure {X S : Scheme.{u}} (f : X ⟶ S)
    {z : X} {s : S} {P : Type*} [TopologicalSpace P] (e : P → f.fiber s)
    (he : Topology.IsEmbedding e) (hP : ∀ p, f.fiberι s (e p) ∈ closure ({z} : Set X)) :
    topologicalKrullDim P ≤ topologicalKrullDim (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({z} : Set X))).subschemeι ≫ f).fiber s) := by
  let Y := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({z} : Set X))
  let g : Y.subscheme ⟶ S := Y.subschemeι ≫ f
  have hYsupport : (Y.support : Set X) = closure ({z} : Set X) := by
    simp [Y]
  refine topologicalKrullDim_le_of_range_subset (fun p => f.fiberι s (e p))
    (fun q : g.fiber s => Y.subschemeι (g.fiberι s q))
    ((f.fiberι s).isEmbedding.comp he)
    (Y.subschemeι.isClosedEmbedding.isEmbedding.comp (g.fiberι s).isEmbedding) ?_
  rintro _ ⟨p, rfl⟩
  have hYmem : f.fiberι s (e p) ∈ (Y.support : Set X) := hYsupport ▸ hP p
  rw [← Y.range_subschemeι] at hYmem
  obtain ⟨qY, hqY⟩ := hYmem
  have hqYbase : g qY = s := by
    show f (Y.subschemeι qY) = s
    rw [hqY]
    exact fiberι_point_maps_to_base f s (e p)
  exact ⟨(g.fiberHomeo s).symm ⟨qY, hqYbase⟩, by simp [hqY]⟩

/-- **Stacks Project, Tag 0H3X.** The dimension of the support of a finite type quasi-coherent
module flat over an irreducible base does not increase from the generic fibre to any other
fibre. -/
@[stacks 0H3X]
theorem topologicalKrullDim_supp_fiber_le_of_generic
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (hF : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F)
    [IrreducibleSpace S] (η : S) (hη : IsGenericPoint η Set.univ)
    (r : WithBot ℕ∞)
    (hdim : topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι η)).obj F)) ≤
        r)
    (s : S) :
    topologicalKrullDim
      (SheafOfModules.supp ((Scheme.Modules.pullback (f.fiberι s)).obj F)) ≤
        r := by
  classical
  let Fs := (Scheme.Modules.pullback (f.fiberι s)).obj F
  have : Fs.IsFiniteType := AlgebraicGeometry.SheafOfModules.pullback_isFiniteType
    (f.fiberι s).toLRSHom.toShHom F
  let Ps : Set (f.fiber s) := SheafOfModules.supp Fs
  have : QuasiSober Ps :=
    (SheafOfModules.isClosed_supp Fs).isClosedEmbedding_subtypeVal.quasiSober
  rw [topologicalKrullDim_eq_iSup_irreducibleComponents]
  refine iSup_le fun C => iSup_le fun hC => ?_
  let cP : Ps := genericPoints.ofComponent ⟨C, hC⟩
  have hcGen : IsGenericPoint cP C := genericPoints.isGenericPoint_ofComponent ⟨C, hC⟩
  have hxSupp : f.fiberι s cP.1 ∈ SheafOfModules.supp F := by
    have hxPull : cP.1 ∈ SheafOfModules.supp Fs := cP.2
    rwa [Stacks.Modules.supp_pullback] at hxPull
  obtain ⟨z, hzP, hzRel, hzx⟩ :=
    exists_fiberι_mem_relativeAssassin_specializes f F hF η hη _ hxSupp
  have hzSupp : f.fiberι η z ∈ SheafOfModules.supp F := by
    rwa [Stacks.Modules.supp_pullback] at hzP
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_fiber_closure f F hF η hη _ hzRel
    (fiberι_point_maps_to_base f η z)
  have hdC : topologicalKrullDim C ≤ (d : WithBot ℕ∞) := by
    rw [← hd s _ (specializes_iff_mem_closure.mp hzx) (fiberι_point_maps_to_base f s cP.1)]
    exact topologicalKrullDim_le_fiber_closure f (fun c : C => c.1.1)
      (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal)
      fun c => specializes_iff_mem_closure.mp (hzx.trans ((hcGen.specializes c.2).map
        ((f.fiberι s).continuous.comp continuous_subtype_val)))
  refine hdC.trans ?_
  rw [← hd η _ (subset_closure (Set.mem_singleton _)) (fiberι_point_maps_to_base f η z)]
  exact (topologicalKrullDim_fiber_closure_le f F hzSupp η).trans hdim

end Stacks.RelativeAssassin

end
