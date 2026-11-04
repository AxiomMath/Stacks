module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.PartAAssembly
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectPushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.Etale.FShriekOpenCover
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.Locality
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Noetherian.CoherentHomology
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.PerfectDualAtTheSpaceHypothesis
public import
  StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RingedSitePerfectnessFromTheSpace

/-!
# The hypotheses of [Stacks, Tag 08IF] on an open neighbourhood of the support

Let `f : X ⟶ S` be a morphism of schemes and `𝒢` a bounded complex of coherent `𝒪_X`-modules,
flat over `S`, whose support lies in a closed subset `Z` proper over `S`. For an open `V ⊇ Z`
of `X`, the restriction `𝒢|_V` satisfies the same hypotheses over `S`. This file records this,
and the vanishing of the stalks of `𝒢` off `Z` in the form used by the restriction of `Ext`.

## Main definitions

* `Stacks.Cohomology.RelativeExt.IsBoundedAboveCoherent`: `E ∈ D^-_{Coh}(𝒪_X)`.

## Main results

* `Stacks.Cohomology.RelativeExt.flatProperSupportComplex_restrictComplex`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingedSpaceModuleAdjunction
open TopologicalSpace

universe u

namespace Stacks.Cohomology.RelativeExt

attribute [local instance] HasDerivedCategory.standard hasSheafifyOpensSpace
  wEqualsLocallyBijectiveOpensSpace

/-- **`E ∈ D^-_{Coh}(𝒪_X)`**: `E` is bounded above and all of its cohomology sheaves are
coherent. -/
def IsBoundedAboveCoherent {X : Scheme.{u}} (E : DStd X) : Prop :=
  @DerivedCategoryB.derivedCategoryBMinus _ _ _ (HasDerivedCategory.standard _)
    (fun F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace) => F.IsCoherent) E

/-- **A module has vanishing stalks off a closed subset containing its support.** -/
theorem isZero_stalk_of_supp_subset {X : Scheme.{u}}
    (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (Z : Set X)
    (h : SheafOfModules.supp M ⊆ Z) (x : X) (hx : x ∉ Z) :
    IsZero (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toRingedSpace.carrier)
      M.val.presheaf x) := by
  refine AddCommGrpCat.isZero_iff_subsingleton.2 ⟨fun a b => ?_⟩
  have h0 : ∀ c : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (X := X.toRingedSpace.carrier)
      M.val.presheaf x, c = 0 := fun c => by
    by_contra hc
    exact hx (h ⟨c, hc⟩)
  exact (h0 a).trans (h0 b).symm

/-- **The hypotheses on `𝒢` pass to an open neighbourhood of its support.** If `𝒢` is a bounded
complex of coherent `𝒪_X`-modules, flat over `S`, supported in a closed subset `Z` proper over `S`,
and `V ⊇ Z` is open, then `𝒢|_V` is such a complex over `S` for `f|_V`. -/
theorem flatProperSupportComplex_restrictComplex {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian X] (V : X.Opens)
    (G : CochainComplex (TModules X.toRingedSpace) ℤ)
    (hG : Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex f G) (Z : Closeds X)
    (hZ : IsProperOver f Z) (hsub : ∀ i : ℤ, SheafOfModules.supp (G.X i) ⊆ (Z : Set X))
    (hZV : (Z : Set X) ⊆ V) :
    Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex (V.ι ≫ f)
      (restrictComplex V.ι G) := by
  have hB := isBoundedFlatOver_restrictComplex (f := f) (j := V.ι) ⟨hG.bounded, hG.isFlatOver⟩
  refine ⟨hB.bounded, fun i => ?_, hB.isFlatOver, ?_⟩
  · exact Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app (G.X i))
      (Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_restrict V.ι (G.X i)
        (hG.isCoherent i))
  refine ⟨Z.preimage V.ι.continuous,
    AlgebraicGeometry.SmallEtale.isProperOver_preimage_of_subset_range
      V.ι f Z hZ (by rw [Scheme.Opens.range_ι]; exact hZV), fun i => ?_⟩
  intro x hx
  have hx' : x ∈ SheafOfModules.supp ((Scheme.Modules.restrictFunctor V.ι).obj (G.X i)) :=
    (congrArg (x ∈ ·) (SheafOfModules.supp_eq_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app (G.X i)))).mpr hx
  -- the stalk of the restriction at `x` is the stalk at `V.ι x`
  exact hsub i (((SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).trans
    (Equiv.nontrivial_congr ((Scheme.Modules.restrictStalkNatIso V.ι x).app
      (G.X i)).addCommGroupIsoToAddEquiv.toEquiv)).trans
    (SheafOfModules.mem_supp_iff_nontrivial_stalk (G.X i) (V.ι.base x)).symm |>.mp hx')

section Restrict

attribute [local instance] isOpenImmersion_toShHom modulePullback_preservesFiniteLimits

/-- **Restriction commutes with cohomology**: `H^i(E|_U) ≅ (H^i E)|_U`. -/
def restrictDerivedHomologyIso {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (E : DStd X)
    (i : ℤ) :
    (DerivedCategory.homologyFunctor _ i).obj ((restrictDerived j).obj E) ≅
      (modulePullback j.toLRSHom.toShHom).obj ((DerivedCategory.homologyFunctor _ i).obj E) :=
  (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
    (modulePullback j.toLRSHom.toShHom) i).app E

/-- **The restriction of an object of `D^-_{Coh}(𝒪_X)` to a Noetherian open is pseudo-coherent**
and has quasi-coherent cohomology ([Stacks, Tag 08E8]). -/
theorem isPseudoCoherent_restrictDerived {X : Scheme.{u}} [IsLocallyNoetherian X] (V : X.Opens)
    [IsNoetherian V] (E : DStd X) (hE : IsBoundedAboveCoherent E) :
    RingedSpace.IsPseudoCoherent (X := (V : Scheme.{u}).toRingedSpace)
        ((restrictDerived V.ι).obj E) ∧
      ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj
        ((restrictDerived V.ι).obj E)).IsQuasicoherent := by
  have hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj
      ((restrictDerived V.ι).obj E)).IsCoherent := fun i =>
    Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_of_iso
      (((Scheme.Modules.restrictFunctorIsoPullback V.ι).app _) ≪≫
        (restrictDerivedHomologyIso V.ι E i).symm)
      (Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_restrict V.ι _ (hE.2 i))
  have hqc : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj
      ((restrictDerived V.ι).obj E)).IsQuasicoherent := fun i =>
    (@Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _ _
      (hcoh i)).1
  refine ⟨?_, hqc⟩
  obtain ⟨n₀, hn₀⟩ := hE.1
  exact (isPseudoCoherent_iff_boundedAbove_coherent_homology (V : Scheme.{u})
    ⟨(restrictDerived V.ι).obj E, hqc⟩).2
      ⟨⟨n₀, fun n hn => (@Functor.map_isZero _ _ _ _ _ _ (modulePullback V.ι.toLRSHom.toShHom)
        (@Functor.preservesZeroMorphisms_of_additive _ _ _ _ _ _ _ (modulePullback_additive _)) _
          (hn₀ n hn)).of_iso
        (restrictDerivedHomologyIso V.ι E n)⟩, hcoh⟩

/-- **The restriction of an object of `D^-_{Coh}(𝒪_X)` to a Noetherian open is
`k`-pseudo-coherent for every `k`.** -/
theorem isPseudoCoherentFrom_restrictDerived {X : Scheme.{u}} [IsLocallyNoetherian X]
    (V : X.Opens) [IsNoetherian V] (E : DStd X) (hE : IsBoundedAboveCoherent E) (k : ℤ) :
    RingedSpace.IsPseudoCoherentFrom (X := (V : Scheme.{u}).toRingedSpace)
      ((restrictDerived V.ι).obj E) k :=
  (isPseudoCoherent_restrictDerived V E hE).1.isPseudoCoherentFrom k

end Restrict

/-- The complex `𝒢` of [Stacks, Tag 08IF] is bounded and flat over `S`. -/
theorem isBoundedFlatOver_of_flatProperSupportComplex {X S : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {G : CochainComplex (TModules X.toRingedSpace) ℤ}
    (hG : Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex f G) :
    IsBoundedFlatOver f.toLRSHom.toShHom G :=
  ⟨hG.bounded, hG.isFlatOver⟩

/-- **`K ∈ D(𝒪_S)` is perfect**, in the sense of [Stacks, Tag 08CM]. -/
abbrev IsPerfectObject {S : Scheme.{u}} (K : DStd S) : Prop :=
  RingedSpace.IsPerfect (X := S.toRingedSpace) K

section Stage

attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-- **The derived dual of a perfect object is perfect**, as an object of `D(𝒪_U)`. -/
theorem isPerfectObject_derivedDual {U : Scheme.{u}} (P : DStd U) (hP : IsPerfectObject P) :
    IsPerfectObject (Stacks.SheafOfModules.derivedDual U.toRingedSpace.sheaf P) :=
  Stacks.SheafOfModules.isPerfect_derivedDual_of_isPerfectSpace U.toRingedSpace P hP

/-- **`P^∨ ⊗^L 𝒢` has coherent, hence quasi-coherent, cohomology** for `P` perfect and `𝒢` a
bounded complex of coherent modules, flat over a Noetherian base, with proper support. -/
theorem isDQCoh_stageSource {U S : Scheme.{u}} (g : U ⟶ S) [IsNoetherian S]
    [LocallyOfFiniteType g] (P : DStd U) (hP : IsPerfectObject P)
    (G : CochainComplex (TModules U.toRingedSpace) ℤ)
    (hG : Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex g G) :
    qcohDerived U (stageSource (G := G) P) := fun i =>
  (@Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _ _
    (Stacks.Cohomology.PerfectPushforward.isCoherent_homology_derivedTensor g
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct U.toRingedSpace.sheaf)
      (Stacks.SheafOfModules.derivedDual U.toRingedSpace.sheaf P) G
      (isPerfectObject_derivedDual P hP) hG i)).1

/-- **`K = Rg_*(P^∨ ⊗^L 𝒢)` in the spelling of [Stacks, Tag 0DJQ].** -/
theorem stageK_eq {U S : Scheme.{u}} (g : U ⟶ S) (P : DStd U)
    (G : CochainComplex (TModules U.toRingedSpace) ℤ) :
    stageK g.toLRSHom.toShHom (G := G) P =
      (Stacks.Cohomology.ProperSupportPerfection.derivedPushforwardOX g).obj
        (((Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
          U.toRingedSpace.sheaf).tensor.obj
            (Stacks.SheafOfModules.derivedDual U.toRingedSpace.sheaf P)).obj
              (DerivedCategory.Q.obj G)) := rfl

/-- A perfect object of `D(𝒪_U)` is perfect for the ringed site of opens of `U`. -/
theorem isPerfect_ringedSite_of_isPerfectObject {U : Scheme.{u}} (P : DStd U)
    (hP : IsPerfectObject P) :
    (Stacks.SheafOfModules.ringedSite U.toRingedSpace.sheaf).IsPerfect P :=
  Stacks.Cohomology.PerfectComplexes.isPerfect_ringedSite_of_isPerfect U.toRingedSpace P hP

end Stage

end Stacks.Cohomology.RelativeExt

end
