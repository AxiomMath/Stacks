module

public import
StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtensionExistence
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.LowDepthLocusClosure
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import
StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.DepthDimensionCriterionGlobal
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.PushforwardCoherence.FormalFibresAffineOpen
public import StacksFrontier.AlgebraicGeometry.RecoveryCatenary.Local
public import StacksFrontier.RingTheory.Dualizing.DimensionFunction
public import StacksFrontier.RingTheory.Dualizing.GorensteinCohenMacaulay
public import StacksFrontier.RingTheory.Dualizing.GorensteinFormalFibres
public import StacksFrontier.RingTheory.Dualizing.UniversallyCatenary
public import StacksFrontier.RingTheory.Serre.CohenMacaulay
public import StacksFrontier.Topology.Dimension.CatenaryAdditive
public import StacksFrontier.Topology.Dimension.DimensionFunctionCatenary
public import StacksFrontier.AlgebraicGeometry.Modules.RestrictStalkDepth
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentLocal
public import StacksFrontier.AlgebraicGeometry.DerivedPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OutsideImageDepth
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusCodimension
public import StacksCore.Tactic.StacksAttribute

import all StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtension
import all
StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtensionExistence

/-!
# Construction of the depth-two extension

Let `X` be a Noetherian scheme which locally has a dualizing complex, let `T ⊆ X` be stable
under specialization and let `𝓕` be a coherent `𝒪_X`-module such that `depth(𝓕_x) ≥ 1` whenever
`x ⤳ x'` is an immediate specialization with `x' ∈ T` and `x ∉ T`.  [Stacks, Tag 0EI3] asserts
that `𝓕` has a depth-two extension along `T`: a map to a coherent module which is an isomorphism
on the stalks off `T` and whose stalks on `T` have depth at least two.

The extension constructed is a single direct image.  For a closed subset `Z ⊆ T` containing every
point of `T` at which the stalk of `𝓕` has depth at most one, `V = X ∖ Z` and `j : V → X`, it is
the unit

`𝓕 ⟶ j_*(𝓕|_V)`

of the restriction adjunction.

## Main definitions

* `AlgebraicGeometry.HasDualizingComplexOnAffineCover`: `X` locally has a dualizing complex, in
  its affine-open-cover form.
* `AlgebraicGeometry.lowDepthLocus`: the points of `T` where the stalk has depth at most one.
* `AlgebraicGeometry.HasClosedLowDepthLocus`: that locus is contained in a closed subset of `T`.

## Main results

* `AlgebraicGeometry.isUniversallyCatenary_of_hasDualizingComplexOnAffineCover` and
  `AlgebraicGeometry.formalFibersHavePropertySk_stalk_of_hasDualizingComplexOnAffineCover`: a
  scheme which locally has a dualizing complex is universally catenary, and the formal fibres of
  its local rings satisfy `(Sₙ)` for every `n`.
* `AlgebraicGeometry.exists_isDepthTwoExtension_of_isClosed`: the extension `j_*(P|_{X ∖ Z})`
  across a closed subset `Z` of `T` containing the low-depth locus is both an
  `AlgebraicGeometry.IsDepthTwoExtension` and an `AlgebraicGeometry.IsStabilizedOpenExtension`.
* `AlgebraicGeometry.closure_lowDepthLocus_subset_of_hasDualizingComplex` and
  `AlgebraicGeometry.hasClosedLowDepthLocus_of_hasDualizingComplex`: the closure of the low-depth
  locus is a closed subset of `T`.
* `AlgebraicGeometry.exists_isDepthTwoExtension_of_hasDualizingComplex` and
  `AlgebraicGeometry.existsUnique_isDepthTwoExtension_of_hasDualizingComplex`: existence of the
  depth-two extension, and its uniqueness up to a unique isomorphism.
* `AlgebraicGeometry.exists_isStabilizedOpenExtension_of_hasDualizingComplex` and
  `AlgebraicGeometry.exists_isStabilizedOpenExtension_depthOneQuotient_of_hasDualizingComplex`:
  a stabilized open extension of a coherent module, and of its depth-one quotient, across `T`.

## References

* [Stacks Project, Tag 0EI3](https://stacks.math.columbia.edu/tag/0EI3)
* [Stacks Project, Tag 0BJY](https://stacks.math.columbia.edu/tag/0BJY)
* [Stacks Project, Tag 0ECM](https://stacks.math.columbia.edu/tag/0ECM)
* [Stacks Project, Tag 0EFD](https://stacks.math.columbia.edu/tag/0EFD)
* [Stacks Project, Tag 0EY0](https://stacks.math.columbia.edu/tag/0EY0)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80)
* [Stacks Project, Tag 0AWY](https://stacks.math.columbia.edu/tag/0AWY)
* [Stacks Project, Tag 0DW8](https://stacks.math.columbia.edu/tag/0DW8)
-/

@[expose] public section

open CategoryTheory TopologicalSpace IrreducibleClosedsCodim

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- A locally Noetherian scheme **locally has a dualizing complex** when every point has an
affine open neighbourhood whose ring of sections admits one. -/
public def HasDualizingComplexOnAffineCover (X : Scheme.{u}) [IsLocallyNoetherian X] : Prop :=
  ∀ x : X, ∃ U : X.affineOpens, x ∈ (U.1 : Set X) ∧
    letI : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(X, U.1)), Dualizing.IsDualizingComplex ω

/-- The affine-local form of the dualizing hypothesis implies the cover form. -/
public theorem hasDualizingComplexOnAffineCover_of_locallyHasDualizingComplex
    (X : Scheme.{u}) [IsLocallyNoetherian X] (h : LocallyHasDualizingComplex X) :
    HasDualizingComplexOnAffineCover X := by
  intro x
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨U, hU⟩, hxU, h ⟨U, hU⟩⟩

/-- A scheme which locally has a dualizing complex is universally catenary. -/
public theorem isUniversallyCatenary_of_hasDualizingComplexOnAffineCover
    (X : Scheme.{u}) [IsLocallyNoetherian X] (h : HasDualizingComplexOnAffineCover X) :
    Scheme.IsUniversallyCatenary X := by
  classical
  refine Scheme.isUniversallyCatenary_of_affineOpenCover X
    (fun x : X ↦ (h x).choose) ?_ ?_
  · refine IsOpenCover.mk (le_antisymm le_top fun x _ ↦ ?_)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, (h x).choose_spec.1⟩
  · intro x
    let : IsNoetherianRing Γ(X, ((h x).choose).1) :=
      IsLocallyNoetherian.component_noetherian ((h x).choose)
    obtain ⟨ω, hω⟩ := (h x).choose_spec.2
    exact Dualizing.isUniversallyCatenary_of_isDualizingComplex hω

/-- The formal fibres of the local rings of a scheme which locally has a dualizing complex
satisfy Serre's condition `(Sₙ)` for every `n`. -/
public theorem formalFibersHavePropertySk_stalk_of_hasDualizingComplexOnAffineCover
    (X : Scheme.{u}) [IsLocallyNoetherian X] (h : HasDualizingComplexOnAffineCover X)
    (z : X) (n : ℕ) :
    Stacks.LocalCohomology.FormalFibersHavePropertySk (X.presheaf.stalk z) n := by
  classical
  obtain ⟨U, hzU, hω⟩ := h z
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  obtain ⟨ω, hω⟩ := hω
  rw [← formalFibersHavePropertySk_stalk_iff_primeIdealOf U.2 hzU n]
  set p := U.2.primeIdealOf ⟨z, hzU⟩
  have hloc : Dualizing.IsDualizingComplex
      ((StacksDraft.PseudoCoherence.derivedExtensionScalars
        (algebraMap Γ(X, U.1) (Localization.AtPrime p.asIdeal))).obj ω) :=
    Dualizing.isDualizingComplex_localizationAtPrime.{u, u} ω hω p
  intro q hq
  obtain ⟨hF, hG⟩ :=
    Dualizing.isGorensteinRing_formalFibre_of_isDualizingComplex
      (Localization.AtPrime p.asIdeal) _ hloc q
  exact ⟨hF, @Stacks.propertySkRing_of_isCohenMacaulayRing _ _ hF
    (@Dualizing.IsGorensteinRing.isCohenMacaulayRing _ _ hF hG) n⟩

/-! ### Codimension and immediate specializations -/

/-- A strict specialization strictly shrinks the closures of the two points. -/
private lemma closureSingleton_lt_of_specializes {Y : Type*} [TopologicalSpace Y] [T0Space Y]
    {a b : Y} (hab : a ⤳ b) (hne : b ≠ a) :
    IrreducibleCloseds.closureSingleton b < IrreducibleCloseds.closureSingleton a := by
  refine lt_of_le_of_ne (show closure ({b} : Set Y) ⊆ closure ({a} : Set Y) from
    hab.closure_subset) fun e ↦ hne ?_
  exact (inseparable_iff_closure_eq.mpr
    (congrArg (fun t : IrreducibleCloseds Y ↦ (t : Set Y)) e)).eq

/-- A specialization which is not immediate has codimension at least two between the two point
closures. -/
private lemma two_le_topCodim_of_not_isImmediateSpecialization {Y : Type*} [TopologicalSpace Y]
    [T0Space Y] {x z : Y} (hxz : x ⤳ z) (hne : z ≠ x)
    (h : ¬ IsImmediateSpecialization x z) :
    (2 : ℕ∞) ≤ topCodim (IrreducibleCloseds.closureSingleton z)
      (IrreducibleCloseds.closureSingleton x) := by
  obtain ⟨w, hxw, hwz, hwx, hwz'⟩ : ∃ w : Y, x ⤳ w ∧ w ⤳ z ∧ w ≠ x ∧ w ≠ z := by
    by_contra hc
    refine h ⟨hxz, Ne.symm hne, fun w hxw hwz ↦ ?_⟩
    by_contra hw
    exact hc ⟨w, hxw, hwz, fun e ↦ hw (Or.inl e), fun e ↦ hw (Or.inr e)⟩
  have h1 : IrreducibleCloseds.closureSingleton z <
      IrreducibleCloseds.closureSingleton w := closureSingleton_lt_of_specializes hwz (Ne.symm hwz')
  have h2 : IrreducibleCloseds.closureSingleton w <
      IrreducibleCloseds.closureSingleton x := closureSingleton_lt_of_specializes hxw hwx
  let f : Fin 3 → IrreducibleCloseds Y := fun i ↦
    if (i : ℕ) = 0 then IrreducibleCloseds.closureSingleton z
    else if (i : ℕ) = 1 then IrreducibleCloseds.closureSingleton w
    else IrreducibleCloseds.closureSingleton x
  have hf : ∀ i : Fin 2, f i.castSucc < f i.succ := by
    intro i
    match i with
    | ⟨0, _⟩ => simpa [f] using h1
    | ⟨1, _⟩ => simpa [f] using h2
  have hmono : StrictMono f := Fin.strictMono_iff_lt_succ.mpr hf
  simpa using length_le_topCodim (IrreducibleCloseds.closureSingleton z)
    (IrreducibleCloseds.closureSingleton x) (LTSeries.mk 2 f hmono)
    (show (LTSeries.mk 2 f hmono).head = IrreducibleCloseds.closureSingleton z from rfl)
    (show (LTSeries.mk 2 f hmono).last = IrreducibleCloseds.closureSingleton x from rfl)

/-! ### The unit of the restriction adjunction -/

/-- The unit of the pullback--pushforward adjunction is invertible wherever the unit of the
restriction adjunction is. -/
private lemma isIso_pullbackPushforward_unit_of_isIso_restrict_unit {X : Scheme.{u}}
    (V : X.Opens) (M : X.Modules)
    (h : IsIso ((Scheme.Modules.restrictAdjunction V.ι).unit.app M)) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app M) := by
  have hcomp : (Scheme.Modules.restrictAdjunction V.ι).unit.app M ≫
      (Scheme.Modules.pushforward V.ι).map
        ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app M) =
      (Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app M :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ M
  rw [← hcomp]
  have h2 : IsIso ((Scheme.Modules.pushforward V.ι).map
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app M)) := inferInstance
  infer_instance

/-- A morphism of modules which becomes an isomorphism after restriction to an open subscheme
is an isomorphism on the stalk at every point of that open. -/
private lemma isIso_stalkMap_of_isIso_restrictFunctor_map {X : Scheme.{u}} (V : X.Opens)
    {M N : X.Modules} (g : M ⟶ N)
    (hg : IsIso ((Scheme.Modules.restrictFunctor V.ι).map g))
    (y : X) (hy : y ∈ (V : Set X)) :
    IsIso (AlgebraicGeometry.SheafOfModules.stalkMap X.ringCatSheaf y g) := by
  have hrestr : IsIso (Scheme.Modules.stalkMapOfHom
      ((Scheme.Modules.restrictFunctor V.ι).map g) (⟨y, hy⟩ : (V : Scheme))) := by
    let := hg
    let h1 : IsIso ((Scheme.Modules.toPresheaf (V : Scheme)).map
      ((Scheme.Modules.restrictFunctor V.ι).map g)) := inferInstance
    change IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} (⟨y, hy⟩ : (V : Scheme))).map
      ((Scheme.Modules.toPresheaf (V : Scheme)).map
        ((Scheme.Modules.restrictFunctor V.ι).map g)))
    exact Functor.map_isIso _ _
  exact isIso_stalkMap_of_isIso_stalkAb g y
    ((isIso_stalkMapOfHom_restrictFunctor_map_iff V.ι g (⟨y, hy⟩ : (V : Scheme))).mp hrestr)

/-! ### The extension across a closed subset of the given subset -/

/-- **The depth-two extension, across a closed subset.** Let `X` be a Noetherian universally
catenary scheme whose local rings have formal fibres satisfying `(S₁)`, let `T ⊆ X` be any
subset and let `P` be a coherent module.  Let `Z ⊆ T` be closed and assume

* the stalk of `P` has depth at least two at every point of `T` outside `Z`, and
* `depth(P_x) ≥ 1` at every `x ∉ T` admitting an immediate specialization into `T`.

Then `j_*(P|_{X ∖ Z})` is a depth-two extension of `P` along `T`. -/
public theorem exists_isDepthTwoExtension_of_isClosed
    (X : Scheme.{u}) [IsNoetherian X]
    (hcat : Scheme.IsUniversallyCatenary X)
    (hformal : ∀ z : X,
      Stacks.LocalCohomology.FormalFibersHavePropertySk (X.presheaf.stalk z) 1)
    (T : Set X) (hT : StableUnderSpecialization T) (P : X.Modules) [P.IsCoherent]
    (Z : Set X) (hZclosed : IsClosed Z) (hZT : Z ⊆ T)
    (hgood : ∀ x : X, x ∈ T → x ∉ Z →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (P.presheaf.stalk x))
    (himm : ∀ x z : X, IsImmediateSpecialization x z → z ∈ T → x ∉ T →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (P.presheaf.stalk x)) :
    ∃ (G : X.Modules) (ψ : P ⟶ G),
      IsDepthTwoExtension T ψ ∧ IsStabilizedOpenExtension T ψ := by
  classical
  set V : X.Opens := ⟨Zᶜ, hZclosed.isOpen_compl⟩
  set A : (V : Scheme).Modules := (Scheme.Modules.restrictFunctor V.ι).obj P
  have hAcoh : A.IsCoherent := Modules.isCoherent_restrict P V
  set G : X.Modules := (Scheme.Modules.pushforward V.ι).obj A
  set ψ : P ⟶ G := (Scheme.Modules.restrictAdjunction V.ι).unit.app P with hψdef
  have hcond : ∀ x : (V : Scheme), x ∈ SheafOfModules.supp A → ∀ z : X, z ∉ (V : Set X) →
      z ∈ closure ({V.ι.base x} : Set X) →
      (1 : ℕ∞) < Module.depth ((V : Scheme).presheaf.stalk x)
          (IsLocalRing.maximalIdeal ((V : Scheme).presheaf.stalk x)) (A.presheaf.stalk x) +
        topCodim (IrreducibleCloseds.closureSingleton z)
          (IrreducibleCloseds.closureSingleton (V.ι.base x)) := by
    intro x _ z hz hzx
    have hxV : V.ι.base x ∉ Z := x.2
    have hzZ : z ∈ Z := not_not.mp hz
    have hxz : V.ι.base x ⤳ z := specializes_iff_mem_closure.mpr hzx
    have hne : z ≠ V.ι.base x := fun e ↦ hxV (e ▸ hzZ)
    have hlt := closureSingleton_lt_of_specializes hxz hne
    rw [Scheme.Modules.depth_stalk_restrict V.ι P x]
    by_cases hdx : (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk (V.ι.base x))
        (IsLocalRing.maximalIdeal (X.presheaf.stalk (V.ι.base x)))
        (P.presheaf.stalk (V.ι.base x))
    · calc (1 : ℕ∞) < 1 + 1 := by norm_num
        _ ≤ _ + topCodim (IrreducibleCloseds.closureSingleton z)
              (IrreducibleCloseds.closureSingleton (V.ι.base x)) :=
          add_le_add hdx (one_le_topCodim_of_lt _ _ hlt)
    · have hxT : V.ι.base x ∉ T := fun hT ↦
        hdx (le_trans (by norm_num) (hgood _ hT hxV))
      have hnotimm : ¬ IsImmediateSpecialization (V.ι.base x) z := fun h' ↦
        hdx (himm _ z h' (hZT hzZ) hxT)
      calc (1 : ℕ∞) < 2 := by norm_num
        _ ≤ topCodim (IrreducibleCloseds.closureSingleton z)
              (IrreducibleCloseds.closureSingleton (V.ι.base x)) :=
          two_le_topCodim_of_not_isImmediateSpecialization hxz hne hnotimm
        _ ≤ _ := le_add_self
  have hGcoh : G.IsCoherent := by
    have h0 := open Stacks.LocalCohomologySequence in
      (forall_lt_depth_add_topCodim_iff_forall_isCoherent_rightDerived_opens_ι
        V A 1 hcat (fun z _ ↦ hformal z)).mp hcond 0 (by norm_num)
    exact ObjectProperty.prop_of_iso
      (P := fun M : SheafOfModules.{u} X.ringCatSheaf ↦ M.IsCoherent)
      (Stacks.AlgebraicGeometry.DerivedPushforward.pushforwardRightDerivedZeroObjIso V.ι A) h0
  have hψrestrict : IsIso ((Scheme.Modules.restrictFunctor V.ι).map ψ) := by
    have htri := (Scheme.Modules.restrictAdjunction V.ι).left_triangle_components P
    have h12 : IsIso ((Scheme.Modules.restrictFunctor V.ι).map ψ ≫
        (Scheme.Modules.restrictAdjunction V.ι).counit.app
          ((Scheme.Modules.restrictFunctor V.ι).obj P)) := by
      rw [hψdef, htri]; infer_instance
    exact IsIso.of_isIso_comp_right ((Scheme.Modules.restrictFunctor V.ι).map ψ)
      ((Scheme.Modules.restrictAdjunction V.ι).counit.app
        ((Scheme.Modules.restrictFunctor V.ι).obj P))
  have hψiso : ∀ y : X, y ∈ (V : Set X) →
      IsIso (AlgebraicGeometry.SheafOfModules.stalkMap X.ringCatSheaf y ψ) :=
    isIso_stalkMap_of_isIso_restrictFunctor_map V ψ hψrestrict
  have hGdepth : ∀ y : X, y ∈ T →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) (G.presheaf.stalk y) := by
    intro y hy
    by_cases hyZ : y ∈ Z
    · have hGft : G.IsFiniteType := by
        have := hGcoh
        exact SheafOfModules.IsCoherent.isFiniteType
      have hunit : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app G) :=
        isIso_pullbackPushforward_unit_of_isIso_restrict_unit V G
          (Adjunction.isIso_unit_app_of_iso (Scheme.Modules.restrictAdjunction V.ι)
            (Iso.refl ((Scheme.Modules.pushforward V.ι).obj A)))
      have := hGft
      exact
        Stacks.AlgebraicGeometry.PushforwardRegularity.two_le_depth_stalk_of_isIso_unit_of_notMem
        V G hunit y (fun hc ↦ hc hyZ)
    · have hyV : y ∈ (V : Set X) := hyZ
      have heq : Module.depth (X.presheaf.stalk y)
            (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) (G.presheaf.stalk y) =
          Module.depth (X.presheaf.stalk y)
            (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) (P.presheaf.stalk y) := by
        have h1 := Scheme.Modules.depth_stalk_pushforward_eq_of_isOpenImmersion V.ι A
          (⟨y, hyV⟩ : (V : Scheme))
        have h2 := Scheme.Modules.depth_stalk_restrict V.ι P (⟨y, hyV⟩ : (V : Scheme))
        exact h1.trans h2
      rw [heq]
      exact hgood y hy hyZ
  have hclosureT : ∀ x : X, x ∈ T → closure ({x} : Set X) ⊆ T := fun x hx y hy ↦
    hT (specializes_iff_mem_closure.mpr hy) hx
  refine ⟨G, ψ, ⟨hGcoh, fun x hx ↦ hψiso x (fun hc ↦ hx (hZT hc)), hGdepth⟩,
    hGcoh, fun x ↦ ?_⟩
  by_cases hxT : x ∈ T
  · refine ⟨⟨(Z ∪ closure ({x} : Set X))ᶜ,
      (hZclosed.union isClosed_closure).isOpen_compl⟩, ?_, ?_, ?_, ?_⟩
    · exact fun y hy ↦ (not_not.mp hy).elim (fun h ↦ hZT h) (fun h ↦ hclosureT x hxT h)
    · exact fun _ hmem ↦ hmem (Or.inr (subset_closure rfl))
    · exact fun y hy ↦ hψiso y fun hc ↦ hy (Or.inl hc)
    · let : G.IsCoherent := hGcoh
      exact isIso_unit_restrict_pushforward_of_depth_ge_two X G _ fun y hy ↦
        hGdepth y ((not_not.mp hy).elim (fun h ↦ hZT h) (fun h ↦ hclosureT x hxT h))
  · refine ⟨V, ?_, ?_, ?_, ?_⟩
    · exact fun y hy ↦ hZT (not_not.mp hy)
    · exact fun hmem ↦ absurd hmem hxT
    · exact fun y hy ↦ hψiso y hy
    · let : G.IsCoherent := hGcoh
      exact isIso_unit_restrict_pushforward_of_depth_ge_two X G V fun y hy ↦
        hGdepth y (hZT (not_not.mp hy))

/-! ### The depth-two extension at the hypotheses of the source -/

/-- The *low-depth locus* of `P` along `T`: the points of `T` at which the stalk of `P` has
depth at most one. -/
public def lowDepthLocus {X : Scheme.{u}} (T : Set X) (P : X.Modules) : Set X :=
  {x : X | x ∈ T ∧ ¬ (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (P.presheaf.stalk x)}

/-- The low-depth locus of `P` along `T` is contained in a closed subset of `T`. -/
public def HasClosedLowDepthLocus {X : Scheme.{u}} (T : Set X) (P : X.Modules) : Prop :=
  ∃ Z : Set X, IsClosed Z ∧ Z ⊆ T ∧ lowDepthLocus T P ⊆ Z

/-- The low-depth locus of `P` along `T` is contained in a closed subset of `T` as soon as its
closure stays inside `T`. -/
public theorem hasClosedLowDepthLocus_of_closure_subset {X : Scheme.{u}} (T : Set X)
    (P : X.Modules) (h : closure (lowDepthLocus T P) ⊆ T) :
    HasClosedLowDepthLocus T P :=
  ⟨closure (lowDepthLocus T P), isClosed_closure, h, subset_closure⟩

/-- **The closure of the low-depth locus stays inside `T`.**  Let `X` be Noetherian and locally
carry a dualizing complex, let `T` be stable under specialization and let `F` be coherent with
`depth(F_x) ≥ 1` at every immediate specialization into `T` from outside `T`.  Then the closure
of `AlgebraicGeometry.lowDepthLocus T F` is contained in `T`. -/
public theorem closure_lowDepthLocus_subset_of_hasDualizingComplex
    (X : Scheme.{u}) [IsNoetherian X] (hdual : HasDualizingComplexOnAffineCover X)
    (T : Set X) (hT : StableUnderSpecialization T) (F : X.Modules) [F.IsCoherent]
    (himm : ∀ x x' : X, IsImmediateSpecialization x x' → x' ∈ T → x ∉ T →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (F.presheaf.stalk x)) :
    closure (lowDepthLocus T F) ⊆ T := by
  obtain ⟨hqc, hft⟩ :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F
  let := hqc
  let := hft
  intro w hw
  obtain ⟨U, hwU, hdualU⟩ := hdual w
  let : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  obtain ⟨ω, hω⟩ := hdualU
  have : Module.Finite Γ(X, U.1) Γ(F, U.1) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections F U.2
  obtain ⟨f, hfemb, hfe, hfd⟩ :
      ∃ f : PrimeSpectrum Γ(X, U.1) → X, Topology.IsOpenEmbedding f ∧
        (∀ y : U.1, f (U.2.primeIdealOf y) = (y : X)) ∧
        (∀ p : PrimeSpectrum Γ(X, U.1),
          Module.depth (X.presheaf.stalk (f p))
              (IsLocalRing.maximalIdeal (X.presheaf.stalk (f p))) (F.presheaf.stalk (f p)) =
            Module.depth (Localization.AtPrime p.asIdeal)
              (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
              (LocalizedModule p.asIdeal.primeCompl Γ(F, U.1))) := by
    refine ⟨fun p ↦ Subtype.val (U.2.isoSpec.hom.homeomorph.symm p),
      U.1.isOpen.isOpenEmbedding_subtypeVal.comp
        U.2.isoSpec.hom.homeomorph.symm.isOpenEmbedding,
      fun y ↦ congrArg Subtype.val (U.2.isoSpec.hom.homeomorph.symm_apply_apply y),
      fun p ↦ ?_⟩
    have hb : U.2.primeIdealOf (U.2.isoSpec.hom.homeomorph.symm p) = p :=
      U.2.isoSpec.hom.homeomorph.apply_symm_apply p
    rw [Stacks.ModuleStalkSpecialization.depth_stalk_eq_depth_localizedModule F U.2
        (U.2.isoSpec.hom.homeomorph.symm p), hb]
  have hTAstab : StableUnderSpecialization (f ⁻¹' T) := fun p q hpq hp ↦
    hT (hpq.map hfemb.continuous) hp
  have himmA : ∀ p q : PrimeSpectrum Γ(X, U.1), IsImmediateSpecialization p q → q ∈ f ⁻¹' T →
      p ∉ f ⁻¹' T → (1 : ℕ∞) ≤ Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl Γ(F, U.1)) := by
    intro p q hpqimm hq hp
    rw [← hfd p]
    exact himm _ _ (hpqimm.map_of_isOpenEmbedding hfemb) hq hp
  have hBeq : f ⁻¹' lowDepthLocus T F = {p : PrimeSpectrum Γ(X, U.1) | p ∈ f ⁻¹' T ∧
      ¬ (2 : ℕ∞) ≤ Module.depth (Localization.AtPrime p.asIdeal)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (LocalizedModule p.asIdeal.primeCompl Γ(F, U.1))} := by
    ext p
    refine ⟨fun hp ↦ ⟨hp.1, fun hc ↦ hp.2 ?_⟩, fun hp ↦ ⟨hp.1, fun hc ↦ hp.2 ?_⟩⟩
    · rwa [hfd p]
    · rwa [← hfd p]
  have hy : U.2.primeIdealOf ⟨w, hwU⟩ ∈ f ⁻¹' closure (lowDepthLocus T F) := by
    rw [Set.mem_preimage, hfe ⟨w, hwU⟩]
    exact hw
  rw [hfemb.isOpenMap.preimage_closure_eq_closure_preimage hfemb.continuous, hBeq] at hy
  have hmem := Stacks.Algebraization.closure_lowDepth_subset_of_isDualizingComplex
    (M := Γ(F, U.1)) ω hω (f ⁻¹' T) hTAstab himmA hy
  rwa [Set.mem_preimage, hfe ⟨w, hwU⟩] at hmem

/-- Under the hypotheses of
`AlgebraicGeometry.closure_lowDepthLocus_subset_of_hasDualizingComplex` the low-depth locus of `F`
along `T` lies in a closed subset of `T`, namely in its own closure. -/
public theorem hasClosedLowDepthLocus_of_hasDualizingComplex
    (X : Scheme.{u}) [IsNoetherian X] (hdual : HasDualizingComplexOnAffineCover X)
    (T : Set X) (hT : StableUnderSpecialization T) (F : X.Modules) [F.IsCoherent]
    (himm : ∀ x x' : X, IsImmediateSpecialization x x' → x' ∈ T → x ∉ T →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (F.presheaf.stalk x)) :
    HasClosedLowDepthLocus T F :=
  hasClosedLowDepthLocus_of_closure_subset T F
    (closure_lowDepthLocus_subset_of_hasDualizingComplex X hdual T hT F himm)

/-- The extension `j_*(F|_{X ∖ Z})` across the closure of the low-depth locus is both a
depth-two extension and a stabilized open extension. -/
private theorem exists_isDepthTwoExtension_and_isStabilizedOpenExtension_of_hasDualizingComplex
    (X : Scheme.{u}) [IsNoetherian X] (hdual : HasDualizingComplexOnAffineCover X)
    (T : Set X) (hT : StableUnderSpecialization T) (F : X.Modules) [F.IsCoherent]
    (himm : ∀ x x' : X, IsImmediateSpecialization x x' → x' ∈ T → x ∉ T →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (F.presheaf.stalk x)) :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsDepthTwoExtension T φ ∧ IsStabilizedOpenExtension T φ := by
  obtain ⟨Z, hZclosed, hZT, hBZ⟩ :=
    hasClosedLowDepthLocus_of_hasDualizingComplex X hdual T hT F himm
  exact exists_isDepthTwoExtension_of_isClosed X
    (isUniversallyCatenary_of_hasDualizingComplexOnAffineCover X hdual)
    (fun z ↦ formalFibersHavePropertySk_stalk_of_hasDualizingComplexOnAffineCover X hdual z 1)
    T hT F Z hZclosed hZT (fun x hx hxZ ↦ of_not_not fun hc ↦ hxZ (hBZ ⟨hx, hc⟩)) himm

/-- **Existence of the depth-two extension.**  Let `X` be a Noetherian scheme which locally has a
dualizing complex, let `T ⊆ X` be stable under specialization and let `F` be coherent.  Assume
`depth(F_x) ≥ 1` at every immediate specialization `x ⤳ x'` with `x' ∈ T` and `x ∉ T`.  Then `F`
admits a map to a coherent module which is an isomorphism on the stalks off `T` and whose stalks
on `T` have depth at least two. -/
@[stacks 0EI3 "existence, at the source's hypotheses: X Noetherian with a dualizing complex on \
an affine open cover, T stable under specialization, F coherent, and depth at least one at the \
immediate specializations into T from outside T; the witness is the single direct image \
j_*(F|_{X ∖ Z}) across the closure Z of the low-depth locus, not the source's colimit of \
pushforwards, and its coherence is proved here from Faltings through Tag 0BJY"]
public theorem exists_isDepthTwoExtension_of_hasDualizingComplex
    (X : Scheme.{u}) [IsNoetherian X] (hdual : HasDualizingComplexOnAffineCover X)
    (T : Set X) (hT : StableUnderSpecialization T) (F : X.Modules) [F.IsCoherent]
    (himm : ∀ x x' : X, IsImmediateSpecialization x x' → x' ∈ T → x ∉ T →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (F.presheaf.stalk x)) :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsDepthTwoExtension T φ := by
  obtain ⟨G, φ, hφ, -⟩ :=
    exists_isDepthTwoExtension_and_isStabilizedOpenExtension_of_hasDualizingComplex
      X hdual T hT F himm
  exact ⟨G, φ, hφ⟩

/-- **Existence and uniqueness of the depth-two extension.**  Under the hypotheses of
`AlgebraicGeometry.exists_isDepthTwoExtension_of_hasDualizingComplex` there is a map `F ⟶ F''`
of coherent modules which is an isomorphism on the stalks off `T` and whose stalks on `T` have
depth at least two, and it is unique: any other such map is carried to it by a unique
isomorphism under `F`. -/
@[stacks 0EI3 "the source's unique map, as existence together with uniqueness up to a unique \
isomorphism under F, at the source's hypotheses"]
public theorem existsUnique_isDepthTwoExtension_of_hasDualizingComplex
    (X : Scheme.{u}) [IsNoetherian X] (hdual : HasDualizingComplexOnAffineCover X)
    (T : Set X) (hT : StableUnderSpecialization T) (F : X.Modules) [F.IsCoherent]
    (himm : ∀ x x' : X, IsImmediateSpecialization x x' → x' ∈ T → x ∉ T →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (F.presheaf.stalk x)) :
    ∃ (G : X.Modules) (φ : F ⟶ G), IsDepthTwoExtension T φ ∧
      ∀ (H : X.Modules) (ψ : F ⟶ H), IsDepthTwoExtension T ψ →
        ∃! e : G ≅ H, φ ≫ e.hom = ψ := by
  obtain ⟨G, φ, hφ⟩ :=
    exists_isDepthTwoExtension_of_hasDualizingComplex X hdual T hT F himm
  exact ⟨G, φ, hφ, fun H ψ hψ ↦ depthTwoExtension_unique X T F G H φ ψ hφ hψ⟩

/-- On a Noetherian scheme which locally has a dualizing complex, a coherent module `P` with
`depth(P_x) ≥ 1` at every immediate specialization into `T'` from outside `T'` has a stabilized
open extension across the specialization-stable subset `T'`. -/
public theorem exists_isStabilizedOpenExtension_of_hasDualizingComplex
    (X : Scheme.{u}) [IsNoetherian X] (hdual : HasDualizingComplexOnAffineCover X)
    (T' : Set X) (hT' : StableUnderSpecialization T') (P : X.Modules) [P.IsCoherent]
    (himm : ∀ x x' : X, IsImmediateSpecialization x x' → x' ∈ T' → x ∉ T' →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (P.presheaf.stalk x)) :
    ∃ (G : X.Modules) (ψ : P ⟶ G), IsStabilizedOpenExtension T' ψ := by
  obtain ⟨G, ψ, -, hstab⟩ :=
    exists_isDepthTwoExtension_and_isStabilizedOpenExtension_of_hasDualizingComplex
      X hdual T' hT' P himm
  exact ⟨G, ψ, hstab⟩

/-- The depth of a stalk is unchanged by a map of modules which is invertible on that stalk. -/
private lemma depth_stalk_eq_of_isIso_stalkMapOfHom {X : Scheme.{u}} {M N : X.Modules}
    (φ : M ⟶ N) (x : X) (h : IsIso (Scheme.Modules.stalkMapOfHom φ x)) :
    Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (M.presheaf.stalk x) =
      Module.depth (X.presheaf.stalk x) (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
        (N.presheaf.stalk x) := by
  set ψ : M.presheaf.stalk x ≃+ N.presheaf.stalk x :=
    (asIso (Scheme.Modules.stalkMapOfHom φ x)).addCommGroupIsoToAddEquiv
  have hsm : ∀ (r : X.presheaf.stalk x) (z : M.presheaf.stalk x),
      ψ (r • z) = (RingEquiv.refl (X.presheaf.stalk x)) r • ψ z := fun r z ↦
    Scheme.Modules.stalkMapOfHom_smul φ x r z
  rw [Module.depth_eq_of_semilinearEquiv (RingEquiv.refl (X.presheaf.stalk x))
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ψ hsm]
  congr 1
  simp

/-- **A stabilized open extension of the depth-one quotient.**  On a Noetherian scheme which
locally has a dualizing complex, for `T` stable under specialization and `F` coherent with
`depth(F_x) ≥ 1` at every immediate specialization into `T` from outside `T`, the depth-one
quotient of `F` along `T` has a stabilized open extension across `T`. -/
public theorem exists_isStabilizedOpenExtension_depthOneQuotient_of_hasDualizingComplex
    (X : Scheme.{u}) [IsNoetherian X] (hdual : HasDualizingComplexOnAffineCover X)
    (T : Set X) (hT : StableUnderSpecialization T) (F : X.Modules) [F.IsCoherent]
    (himm : ∀ x x' : X, IsImmediateSpecialization x x' → x' ∈ T → x ∉ T →
      (1 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (F.presheaf.stalk x)) :
    ∃ (G : X.Modules) (ψ : depthOneQuotient X T hT F ⟶ G),
      IsStabilizedOpenExtension T ψ := by
  let : (depthOneQuotient X T hT F).IsCoherent := (depthOneQuotient_spec X T hT F).1
  refine exists_isStabilizedOpenExtension_of_hasDualizingComplex X hdual T hT
    (depthOneQuotient X T hT F) (fun x x' himmx hx' hx ↦ ?_)
  rw [← depth_stalk_eq_of_isIso_stalkMapOfHom (toDepthOneQuotient X T hT F) x
    ((depthOneQuotient_spec X T hT F).2.2.1 x hx)]
  exact himm x x' himmx hx' hx

end AlgebraicGeometry

end
