module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectInternalHomLocalModels
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectTensorCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupport

/-!
# Finiteness properties of `RSheafHom(E, 𝒢)`

Let `X` be an algebraic space, `E` a perfect object of `D(𝒪_X)` and `𝒢` a bounded complex of
`𝒪_X`-modules with support in a closed compact set `Z ⊆ |X|`, and let `K = RSheafHom(E, 𝒢)`.

## Main definitions

* `AlgebraicGeometry.Space.derivedSheafHomObj`: the derived internal Hom `RSheafHom(E, Q𝒢)` on
  the small étale site of `X`.

## Main results

* `AlgebraicGeometry.Space.isCoherent_homology_derivedSheafHom_of_isPerfect`: if the terms of `𝒢`
  are coherent, the cohomology sheaves of `K` are coherent.
* `AlgebraicGeometry.Space.exists_isZero_homology_derivedSheafHom_of_isPerfect`: `K` has only
  finitely many nonzero cohomology sheaves.
* `AlgebraicGeometry.Space.cohomologySupportedOn_derivedSheafHom`: `K` is supported on `Z`.
* `AlgebraicGeometry.Space.hasFiniteTorDimension_derivedScalarRestriction_derivedSheafHom`: if
  `f : X ⟶ Y` is a morphism and the terms of `𝒢` are flat over `f⁻¹𝒪_Y`, then `K`, read in
  `D(f⁻¹𝒪_Y)`, has finite Tor dimension.

## References

* [Stacks Project, Tag 0DKK](https://stacks.math.columbia.edu/tag/0DKK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] smallEtaleRingedSite_essentiallySmall
  Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- The derived category of the modules on a slice of the small étale site. -/
local instance (priority := 20000) sliceHasDerivedCategoryHomC
    (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    HasDerivedCategory.{u + 1}
      (RingedSite.Modules.{u + 1, u, u} ((smallEtaleRingedSite B S hS X.1 X.2).over U)) :=
  @HasDerivedCategory.standard _ _ (smallEtaleRingedSite_over_abelian B S hS X.1 X.2 U)

attribute [local instance] essentiallySmall_smallEtale_over

/-- Sheafification of abelian-group presheaves on a slice of a slice of the small étale site. -/
local instance sliceSliceHasSheafifyC (U : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (W : ((smallEtaleRingedSite B S hS X.1 X.2).over U).C) :
    HasWeakSheafify (((smallEtaleRingedSite B S hS X.1 X.2).over U).J.over W) AddCommGrpCat.{u} :=
  have := Stacks.essentiallySmall_over.{u} (C := ((smallEtaleRingedSite B S hS X.1 X.2).over U).C) W
  have := GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{u}
    (((smallEtaleRingedSite B S hS X.1 X.2).over U).J.over W)
  inferInstance

/-- On a slice of a slice of the small étale site, the weak equivalences of abelian-group
presheaves are the locally bijective morphisms. -/
local instance sliceSliceWEqC (U : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (W : ((smallEtaleRingedSite B S hS X.1 X.2).over U).C) :
    (((smallEtaleRingedSite B S hS X.1 X.2).over U).J.over W).WEqualsLocallyBijective
      AddCommGrpCat.{u} :=
  have := Stacks.essentiallySmall_over.{u} (C := ((smallEtaleRingedSite B S hS X.1 X.2).over U).C) W
  .ofEssentiallySmall _

/-- Sheafification of presheaves of abelian groups in the universe `u + 1` on a slice of the
small étale site. -/
local instance sliceHasSheafifyMaxC (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    HasSheafify ((smallEtaleRingedSite B S hS X.1 X.2).over U).J AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1} _

/-- On a slice of the small étale site, the weak equivalences of presheaves of abelian groups in
the universe `u + 1` are the locally bijective morphisms. -/
local instance sliceWEqMaxC (U : (smallEtaleRingedSite B S hS X.1 X.2).C) :
    ((smallEtaleRingedSite B S hS X.1 X.2).over U).J.WEqualsLocallyBijective
      AddCommGrpCat.{u + 1} :=
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat.{u + 1} _

/-- Vanishing, as a property of objects, is closed under isomorphisms. -/
local instance isClosedUnderIsomorphisms_isZero {A : Type*} [Category A] :
    ObjectProperty.IsClosedUnderIsomorphisms (fun M : A => IsZero M) where
  of_iso e h := h.of_iso e.symm

/-- Vanishing, as a property of objects, is closed under finite coproducts. -/
local instance isClosedUnderFiniteCoproducts_isZero {A : Type*} [Category A] [HasZeroMorphisms A]
    [HasZeroObject A] :
    ObjectProperty.IsClosedUnderFiniteCoproducts (fun M : A => IsZero M) where
  isClosedUnderColimitsOfShape _ _ :=
    ⟨fun _ ⟨h⟩ => h.isColimit.isZero_pt (Functor.isZero _ fun j => h.prop_diag_obj j)⟩

/-- The derived internal Hom `RSheafHom(E, Q𝒢)` on the small étale site of `X`. -/
abbrev derivedSheafHomObj (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) :
    DerivedCategory (Modules.{u, u} B S hS X.1 X.2) :=
  ((RingedSite.derivedSheafHomSmallBifunctor (smallEtaleRingedSite B S hS X.1 X.2)).obj
    (op E)).obj (DerivedCategory.Q.obj G)

open Stacks.DerivedTensor.ExtensionByZero.OfEssentiallySmall (restriction restrictionComplex)

/-- The cohomology sheaves of `RSheafHom(E, 𝒢)` are coherent for `E` perfect and `𝒢` a complex of
coherent `𝒪_X`-modules. -/
theorem isCoherent_homology_derivedSheafHom_of_isPerfect
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E)
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ)
    (hG : ∀ q : ℤ, IsCoherent B S hS X.1 X.2 (G.X q)) (i : ℤ) :
    IsCoherent B S hS X.1 X.2 ((DerivedCategory.homologyFunctor _ i).obj
      (derivedSheafHomObj B S hS X E G)) := by
  let Xs := smallEtaleRingedSite B S hS X.1 X.2
  have hcoh : SheafOfModules.IsCoherentOnSite ((DerivedCategory.homologyFunctor _ i).obj
      (derivedSheafHomObj B S hS X E G)) := by
    obtain ⟨N, I, W, hW, hmod, -⟩ := exists_coversTop_uniform_hom_models B S hS X E hE G ∅
      isCompact_empty isClosed_empty
    refine (Stacks.SheafOfModules.isCoherentOnSite_iff_exists_cover_isCoherentOnSite Xs _).2
      ⟨I, W, hW, fun k => ?_⟩
    obtain ⟨P, hP, ⟨e⟩, -⟩ := hmod k
    let H := RingedSite.sheafHomComplexSmall (Xs.over (W k)) P (Xs.restrictComplex G (W k))
    have hterm : ∀ n, SheafOfModules.IsCoherentOnSite (H.X n) := fun n =>
      RingedSite.prop_sheafHomComplexSmall_X (Xs.over (W k))
        (fun M => SheafOfModules.IsCoherentOnSite M)
        Stacks.SheafOfModules.isCoherentOnSite_of_comp_eq_id P (Xs.restrictComplex G (W k)) hP n
        (fun p _ => Stacks.SheafOfModules.isCoherentOnSite_over (G.X (p + n))
          (hG _).toIsCoherentOnSite (W k))
    refine Stacks.SheafOfModules.isCoherentOnSite_of_iso ?_
      (Stacks.SheafOfModules.isCoherentOnSite_homology H hterm i)
    have : PreservesFiniteLimits (restriction Xs (W k)) :=
      Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits (W k)
    have : PreservesFiniteColimits (restriction Xs (W k)) :=
      Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits (W k)
    exact ((DerivedCategory.homologyFunctorFactors _ i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso e.symm ≪≫
      (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (restriction Xs (W k)) i).app _
  exact { toIsCoherentOnSite := hcoh }

/-- The restriction of a cohomology sheaf of an object with a local model vanishes where the model
has a vanishing term. -/
theorem isZero_restrict_homology_of_model (W : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (K : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (H : CochainComplex (RingedSite.Modules.{u + 1, u, u}
      ((smallEtaleRingedSite B S hS X.1 X.2).over W)) ℤ)
    (e : (RingedSite.derivedRestriction.{u + 1, u, u, u + 1}
      (smallEtaleRingedSite B S hS X.1 X.2) W).obj K ≅ DerivedCategory.Q.obj H)
    (n : ℤ) (hn : IsZero (H.X n)) :
    IsZero ((restriction (smallEtaleRingedSite B S hS X.1 X.2) W).obj
      ((DerivedCategory.homologyFunctor _ n).obj K)) := by
  have : PreservesFiniteLimits (restriction (smallEtaleRingedSite B S hS X.1 X.2) W) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits W
  have : PreservesFiniteColimits (restriction (smallEtaleRingedSite B S hS X.1 X.2) W) :=
    Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits W
  have hH : IsZero (H.homology n) := ShortComplex.isZero_homology_of_isZero_X₂ _ hn
  exact hH.of_iso (((DerivedCategory.homologyFunctorFactors _ n).app _).symm.trans
    ((DerivedCategory.homologyFunctor _ n).mapIso e.symm ≪≫
      (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
        (restriction (smallEtaleRingedSite B S hS X.1 X.2) W) n).app _)).symm

/-- The terms of `SheafHom^•(P, 𝒢|_W)` vanish on a member all of whose points lie outside a set
containing the supports of the terms of `𝒢`. -/
theorem isZero_sheafHomComplexSmall_X_of_out (W : (smallEtaleRingedSite B S hS X.1 X.2).C)
    (P : CochainComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).over W)) ℤ)
    (hP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X.1 X.2).O).over W) P)
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (Z : Set (points B S hS X.1))
    (hGZ : ∀ q : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X q)) ⊆ Z)
    (hout : ∀ z : chartScheme W, chartSchemeToPoints B S hS X.1 W z ∉ Z) (n : ℤ) :
    IsZero ((RingedSite.sheafHomComplexSmall ((smallEtaleRingedSite B S hS X.1 X.2).over W) P
      ((smallEtaleRingedSite B S hS X.1 X.2).restrictComplex G W)).X n) :=
  RingedSite.prop_sheafHomComplexSmall_X ((smallEtaleRingedSite B S hS X.1 X.2).over W)
    (fun M => IsZero M) (fun i r hir hD => by
      rw [IsZero.iff_id_eq_zero, ← hir, hD.eq_zero_of_tgt i, zero_comp])
    P _ hP n (fun p _ => isZero_over_of_forall_notMem_supportOfSheaf B S hS X (G.X (p + n)) W
      fun z hz => hout z (hGZ _ hz))

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck in
/-- For `E` perfect, if every term of `𝒢` has support in a closed compact set `Z`, then
`RSheafHom(E, 𝒢)` is supported on `Z`. -/
theorem cohomologySupportedOn_derivedSheafHom
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E)
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (Z : Set (points B S hS X.1))
    (hZc : IsCompact Z) (hZcl : IsClosed Z)
    (hGZ : ∀ q : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X q)) ⊆ Z) :
    CohomologySupportedOn.{u, u} B S hS X.1 X.2 Z (derivedSheafHomObj B S hS X E G) := by
  obtain ⟨N, I, W, hW, hmod, hcov⟩ :=
    exists_coversTop_uniform_hom_models B S hS X E hE G Z hZc hZcl
  intro n x hx
  by_contra hxZ
  obtain ⟨i, z, hout, rfl⟩ := hcov x hxZ
  obtain ⟨P, hP, ⟨e⟩, -⟩ := hmod i
  exact notMem_supportOfSheaf_of_isZero_over B S hS X _ (W i)
    (isZero_restrict_homology_of_model B S hS X (W i) _ _ e n
      (isZero_sheafHomComplexSmall_X_of_out B S hS X (W i) P hP G Z hGZ hout n)) z hx

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck in
/-- For `E` perfect and `𝒢` a bounded complex all of whose terms have support in a compact closed
set, `RSheafHom(E, 𝒢)` has only finitely many nonzero cohomology sheaves. -/
theorem exists_isZero_homology_derivedSheafHom_of_isPerfect
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E)
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (g₀ g₁ : ℤ)
    (hGb : ∀ q : ℤ, q < g₀ ∨ g₁ < q → IsZero (G.X q)) (Z : Set (points B S hS X.1))
    (hZc : IsCompact Z) (hZcl : IsClosed Z)
    (hGZ : ∀ q : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X q)) ⊆ Z) :
    ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n →
      IsZero ((DerivedCategory.homologyFunctor _ n).obj (derivedSheafHomObj B S hS X E G)) := by
  obtain ⟨N, I, W, hW, hmod, -⟩ :=
    exists_coversTop_uniform_hom_models B S hS X E hE G Z hZc hZcl
  refine ⟨g₀ - N, g₁ + N, fun n hn => ?_⟩
  refine Stacks.SheafOfModules.isZero_of_coversTop hW _ fun i => ?_
  obtain ⟨P, hP, ⟨e⟩, hkind⟩ := hmod i
  refine isZero_restrict_homology_of_model B S hS X (W i) _ _ e n ?_
  rcases hkind with hPz | hout
  · refine RingedSite.prop_sheafHomComplexSmall_X
      ((smallEtaleRingedSite B S hS X.1 X.2).over (W i))
      (fun M => IsZero M) (fun i r hir hD => by
        rw [IsZero.iff_id_eq_zero, ← hir, hD.eq_zero_of_tgt i, zero_comp])
      P _ hP n (fun p hp => ?_)
    have hpN : -(N : ℤ) ≤ p ∧ p ≤ N := of_not_not fun h => hp (hPz p (by omega))
    exact (restriction (smallEtaleRingedSite B S hS X.1 X.2) (W i)).map_isZero
      (hGb _ (by omega))
  · exact isZero_sheafHomComplexSmall_X_of_out B S hS X (W i) P hP G Z hGZ hout n

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck in
/-- For `E` perfect and `𝒢` a bounded complex whose terms have support in a compact closed set
and are flat over `f⁻¹𝒪_Y`, the object `RSheafHom(E, 𝒢)` of `D(𝒪_X)`, read in `D(f⁻¹𝒪_Y)`, has
finite Tor dimension. -/
theorem hasFiniteTorDimension_derivedScalarRestriction_derivedSheafHom {Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y)
    (T' : Stacks.SheafOfModules.DerivedTensorProduct.{u + 1, u, u, u + 1}
      (inverseImageRingedSite B S hS f))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect E)
    (G : CochainComplex (Modules.{u, u} B S hS X.1 X.2) ℤ) (g₀ g₁ : ℤ)
    (hGb : ∀ q : ℤ, q < g₀ ∨ g₁ < q → IsZero (G.X q)) (Z : Set (points B S hS X.1))
    (hZc : IsCompact Z) (hZcl : IsClosed Z)
    (hGZ : ∀ q : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X q)) ⊆ Z)
    (hGflat : ∀ q : ℤ, AlgebraicGeometry.SheafOfModules.IsFlat
      (O := (inverseImageRingedSite B S hS f).O) ((scalarRestriction B S hS f).obj (G.X q))) :
    Stacks.SheafOfModules.DerivedTensorProduct.HasFiniteTorDimension T'
      ((derivedScalarRestriction B S hS f).obj (derivedSheafHomObj B S hS X E G)) := by
  let Xs := smallEtaleRingedSite B S hS X.1 X.2
  let O' := (inverseImageRingedSite B S hS f).O
  let φ := inverseImageStructureMap B S hS f
  obtain ⟨N, I, W, hW, hmod, -⟩ :=
    exists_coversTop_uniform_hom_models B S hS X E hE G Z hZc hZcl
  refine ⟨g₀ - N, g₁ + N, ?_⟩
  open Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall in
  refine hasTorAmplitude_restrictScalars_of_flatModels
    Xs O' φ T' _ (g₀ - N) (g₁ + N) W hW fun i => Or.inl ?_
  obtain ⟨P, hP, ⟨e⟩, hkind⟩ := hmod i
  let G₂' := Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall.sliceRestrictScalarsOver
    Xs O' φ (W i)
  have : G₂'.Additive := ⟨by intros; ext; rfl⟩
  let Q : ObjectProperty (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (Xs.over (W i)).O)) :=
    fun M => AlgebraicGeometry.SheafOfModules.IsFlat (O := O'.over (W i)) (G₂'.obj M)
  have : Q.IsClosedUnderIsomorphisms :=
    ⟨fun e h => Stacks.SheafOfModules.FlatRetract.isFlat_of_iso (O'.over (W i)) (G₂'.mapIso e) h⟩
  have : Q.IsClosedUnderFiniteCoproducts :=
    open Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall in
    isClosedUnderFiniteCoproducts_isFlat_restrictScalars
      (J := Xs.J.over (W i))
      (O₁ := O'.over (W i)) (O₂ := Stacks.SheafOfModules.Tensor.ringSheaf (Xs.O.over (W i)))
      ((Xs.J.overPullback RingCat.{u} (W i)).map φ)
  have hGq : ∀ q : ℤ, Q ((Xs.restrictComplex G (W i)).X q) := fun q =>
    Stacks.SheafOfModules.FlatRetract.isFlat_of_iso (O'.over (W i))
      ((Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall.restrictScalarsOverIso φ
        (W i)).app (G.X q))
      (Stacks.SheafOfModules.FlatRestriction.OfEssentiallySmall.isFlat_over_of_essentiallySmall
        (Stacks.SheafOfModules.DerivedTensorProduct.OfEssentiallySmall.withStructureSheaf Xs O')
        (W i) _ (hGflat q))
  refine ⟨RingedSite.sheafHomComplexSmall (Xs.over (W i)) P (Xs.restrictComplex G (W i)),
    fun n => ?_, fun n hn => ?_, ⟨e⟩⟩
  · exact RingedSite.prop_sheafHomComplexSmall_X (Xs.over (W i)) Q
      (fun i' r hir hN => Stacks.SheafOfModules.FlatRetract.isFlat_of_retract (O'.over (W i))
        (G₂'.map i') (G₂'.map r) (by rw [← G₂'.map_comp, hir, G₂'.map_id]) hN)
      P _ hP n (fun p _ => hGq (p + n))
  · rcases hkind with hPz | hout
    · refine RingedSite.prop_sheafHomComplexSmall_X (Xs.over (W i))
        (fun M => IsZero M) (fun i r hir hD => by
          rw [IsZero.iff_id_eq_zero, ← hir, hD.eq_zero_of_tgt i, zero_comp])
        P _ hP n (fun p hp => ?_)
      have hpN : -(N : ℤ) ≤ p ∧ p ≤ N := of_not_not fun h => hp (hPz p (by omega))
      exact (restriction Xs (W i)).map_isZero (hGb _ (by omega))
    · exact isZero_sheafHomComplexSmall_X_of_out B S hS X (W i) P hP G Z hGZ hout n

end AlgebraicGeometry.Space

end
