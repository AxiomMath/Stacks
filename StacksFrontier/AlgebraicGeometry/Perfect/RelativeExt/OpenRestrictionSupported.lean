module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.ProjectionFormulaOpenCoverDescent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQuasiCoherent
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.VanishingOverOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardAndRestriction

/-!
# Restriction to an open containing the support of a derived object

Let `j : U ⟶ X` be an open immersion of schemes and let `Z ⊆ X` be a closed subset contained in
the image of `j`. For an object `M` of `D(𝒪_X)` whose cohomology sheaves are supported on `Z`,
the unit `M ⟶ Rj_* Lj^* M` of the derived adjunction `Lj^* ⊣ Rj_*` is an isomorphism, and
consequently `Lj^*` is bijective on morphisms into `M`. Also, a compact subset of a scheme has a
quasi-compact open neighbourhood.

## Main results

* `Stacks.Cohomology.RelativeExt.isIso_derivedAdjunction_unit_app_of_supportedOn`: the unit
  `M ⟶ Rj_* Lj^* M` is invertible for `M` supported on `Z`.
* `Stacks.Cohomology.RelativeExt.bijective_derivedPullback_map_of_supportedOn`: for such `M`
  and any `A`, `Hom(A, M) ⟶ Hom(Lj^* A, Lj^* M)` is bijective.
* `Stacks.Cohomology.RelativeExt.exists_isCompact_open_superset`: a compact subset of a scheme
  is contained in a quasi-compact open.

## Implementation notes

Everything is stated at the standard model `CategoryTheory.HasDerivedCategory.standard`, named
explicitly in every statement (local notations `Dstd`, `Lstd`, `Rstd`, `Astd` below), and no
instance is declared. The derived pullback, pushforward and adjunction are those of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces` at `j.toLRSHom.toShHom`.

Support is the predicate `Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn` at
`structureSheafRing X.toRingedSpace`, read at the standard model: every cohomology sheaf has
zero stalks at the points outside `Z`. It is definitionally the predicate
`AlgebraicGeometry.CohomologySupportedOn`, which has the standard model built in.

## References

* [Stacks Project, Tag 08IF](https://stacks.math.columbia.edu/tag/08IF)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

namespace Stacks.Cohomology.RelativeExt

/-- The derived category of a ringed space at the standard model. -/
local notation "Dstd" X:max => @DerivedCategory (SheafOfModules (structureSheafRing X)) _ _
  (HasDerivedCategory.standard _)

/-- The derived pullback at the standard model. -/
local notation "Lstd" f:max => @derivedPullback _ _ f (HasDerivedCategory.standard _)
  (HasDerivedCategory.standard _) _

/-- The derived pushforward at the standard model. -/
local notation "Rstd" f:max => @derivedPushforward _ _ f (HasDerivedCategory.standard _)
  (HasDerivedCategory.standard _)

/-- The derived adjunction at the standard model. -/
local notation "Astd" f:max => @derivedAdjunction _ _ f (HasDerivedCategory.standard _)
  (HasDerivedCategory.standard _)

/-- The cohomological support predicate at the standard model. -/
local notation "SuppStd" O:max T:max E:max =>
  @Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn _ O
    (HasDerivedCategory.standard _) T E

/-- **A derived object supported on a closed subset vanishes on its complement**: the derived
pullback of `M` to the open subspace `X \ Z` is zero. -/
theorem isZero_derivedPullback_compl_of_supportedOn {X : RingedSpace.{u, u}} (Z : Set X.carrier)
    (hZ : IsClosed Z) (M : Dstd X) (hM : SuppStd (structureSheafRing X) Z M) :
    IsZero ((Lstd (X.ofRestrict (⟨Zᶜ, hZ.isOpen_compl⟩ : Opens X.carrier).isOpenEmbedding)).obj
      M) :=
  (@Stacks.Cohomology.PushforwardRestriction.isZero_derived_restrict_compl_of_supported
    X.carrier (structureSheafRing X) Z hZ (HasDerivedCategory.standard _)
    (HasDerivedCategory.standard _) M hM).of_iso
    ((Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso X
      ⟨Zᶜ, hZ.isOpen_compl⟩).app M)

section OpenImmersion

variable {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- `Lj^*` of the unit of `Lj^* ⊣ Rj_*` is invertible for an open immersion `j`. -/
theorem isIso_derivedPullback_map_derivedAdjunction_unit_app (M : Dstd X.toRingedSpace) :
    IsIso ((Lstd j.toLRSHom.toShHom).map ((Astd j.toLRSHom.toShHom).unit.app M)) := by
  have : SheafedSpace.IsOpenImmersion j.toLRSHom.toShHom := (inferInstance : IsOpenImmersion j)
  have : IsIso (Astd j.toLRSHom.toShHom).counit :=
    Stacks.Cohomology.DerivedBaseChange.isIso_derivedAdjunction_counit_of_isOpenImmersion
      j.toLRSHom.toShHom
  have : IsIso ((Lstd j.toLRSHom.toShHom).map ((Astd j.toLRSHom.toShHom).unit.app M) ≫
      (Astd j.toLRSHom.toShHom).counit.app ((Lstd j.toLRSHom.toShHom).obj M)) := by
    rw [(Astd j.toLRSHom.toShHom).left_triangle_components M]
    exact IsIso.id _
  exact IsIso.of_isIso_comp_right _ ((Astd j.toLRSHom.toShHom).counit.app _)

/-- **The unit `M ⟶ Rj_* Lj^* M` is invertible for `M` supported on a closed subset of the image
of the open immersion `j`.** Let `Z ⊆ X` be closed with `Z ⊆ j(U)`, and let `M ∈ D(𝒪_X)` have
every cohomology sheaf with zero stalks off `Z`. Then the unit at `M` is an isomorphism. -/
theorem isIso_derivedAdjunction_unit_app_of_supportedOn (Z : Set X) (hZ : IsClosed Z)
    (hZj : Z ⊆ Set.range j.base) (M : Dstd X.toRingedSpace)
    (hM : SuppStd (structureSheafRing X.toRingedSpace) Z M) :
    IsIso ((Astd j.toLRSHom.toShHom).unit.app M) := by
  let V : Opens X.toRingedSpace.carrier := ⟨Zᶜ, hZ.isOpen_compl⟩
  let VX : X.Opens := ⟨Zᶜ, hZ.isOpen_compl⟩
  have : SheafedSpace.IsOpenImmersion j.toLRSHom.toShHom := (inferInstance : IsOpenImmersion j)
  have hMV : IsZero ((Lstd (X.toRingedSpace.ofRestrict V.isOpenEmbedding)).obj M) :=
    isZero_derivedPullback_compl_of_supportedOn Z hZ M hM
  have hNV : IsZero ((Lstd (X.toRingedSpace.ofRestrict V.isOpenEmbedding)).obj
      ((Rstd j.toLRSHom.toShHom).obj ((Lstd j.toLRSHom.toShHom).obj M))) := by
    refine IsZero.of_iso ?_ ((DerivedChow.derivedPushforwardRestrictIsoOfStandard
      j.toLRSHom.toShHom
      (U.toRingedSpace.ofRestrict
        (DerivedPushforwardOverOpen.preimageOpen j.toLRSHom.toShHom V).isOpenEmbedding)
      (X.toRingedSpace.ofRestrict V.isOpenEmbedding)
      (DerivedPushforwardOverOpen.restrictPreimage j.toLRSHom.toShHom V)
      (DerivedPushforwardOverOpen.isPullback_restrictPreimage j.toLRSHom.toShHom V)).app
        ((Lstd j.toLRSHom.toShHom).obj M))
    have := (Astd (DerivedPushforwardOverOpen.restrictPreimage j.toLRSHom.toShHom V)
      ).isRightAdjoint
    exact Functor.map_isZero (Rstd (DerivedPushforwardOverOpen.restrictPreimage
      j.toLRSHom.toShHom V))
      (DerivedPushforwardOverOpen.isZero_derivedPullback_derivedPullback_of_le
        j.toLRSHom.toShHom V _ le_rfl M hMV)
  have hW : IsIso ((Lstd j.opensRange.ι.toLRSHom.toShHom).map
      ((Astd j.toLRSHom.toShHom).unit.app M)) := by
    apply Stacks.Cohomology.DerivedProjectionFormula.isIso_of_isIso_derivedPullback_map_of_schemeIso
      j.isoOpensRange
    have hcomp : j.isoOpensRange.hom.toLRSHom.toShHom ≫ j.opensRange.ι.toLRSHom.toShHom =
        j.toLRSHom.toShHom :=
      congrArg (fun f : U ⟶ X => f.toLRSHom.toShHom) (Scheme.Hom.isoOpensRange_hom_ι j)
    have h : IsIso ((Lstd (j.isoOpensRange.hom.toLRSHom.toShHom ≫
        j.opensRange.ι.toLRSHom.toShHom)).map ((Astd j.toLRSHom.toShHom).unit.app M)) := by
      rw [hcomp]
      exact isIso_derivedPullback_map_derivedAdjunction_unit_app j M
    exact (NatIso.isIso_map_iff
      (@Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical _ _ _
        j.isoOpensRange.hom.toLRSHom.toShHom j.opensRange.ι.toLRSHom.toShHom
        (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
        (HasDerivedCategory.standard _)) _).2 h
  refine Stacks.Cohomology.DerivedProjectionFormula.isIso_of_isIso_derivedPullback_opens
    (fun b : Bool => cond b j.opensRange VX) (fun x => ?_) _ (fun b => ?_)
  · by_cases hx : x ∈ Z
    · exact ⟨true, hZj hx⟩
    · exact ⟨false, hx⟩
  · cases b
    · exact hMV.isIso hNV _
    · exact hW

/-- **`Lj^*` is bijective on morphisms into an object supported on a closed subset of the image
of `j`.** For `M ∈ D(𝒪_X)` supported on a closed `Z ⊆ j(U)` and any `A ∈ D(𝒪_X)`, the map
`Hom(A, M) ⟶ Hom(Lj^* A, Lj^* M)` is bijective. -/
theorem bijective_derivedPullback_map_of_supportedOn (Z : Set X) (hZ : IsClosed Z)
    (hZj : Z ⊆ Set.range j.base) (A M : Dstd X.toRingedSpace)
    (hM : SuppStd (structureSheafRing X.toRingedSpace) Z M) :
    Function.Bijective (fun φ : A ⟶ M => (Lstd j.toLRSHom.toShHom).map φ) := by
  have := isIso_derivedAdjunction_unit_app_of_supportedOn j Z hZ hZj M hM
  let e : (A ⟶ M) ≃ (A ⟶ (Rstd j.toLRSHom.toShHom).obj ((Lstd j.toLRSHom.toShHom).obj M)) :=
    { toFun := fun φ => φ ≫ (Astd j.toLRSHom.toShHom).unit.app M
      invFun := fun ψ => ψ ≫ inv ((Astd j.toLRSHom.toShHom).unit.app M)
      left_inv := fun φ => by simp
      right_inv := fun ψ => by simp }
  have key : (fun φ : A ⟶ M => (Lstd j.toLRSHom.toShHom).map φ) =
      ((Astd j.toLRSHom.toShHom).homEquiv A ((Lstd j.toLRSHom.toShHom).obj M)).symm ∘ e := by
    funext φ
    rw [Function.comp_apply, Equiv.eq_symm_apply, Adjunction.homEquiv_unit,
      Adjunction.unit_naturality]
    rfl
  rw [key]
  exact (Equiv.bijective _).comp e.bijective

end OpenImmersion

/-- **A compact subset of a scheme has a quasi-compact open neighbourhood.** -/
theorem exists_isCompact_open_superset (X : Scheme.{u}) (Z : Set X) (hZ : IsCompact Z) :
    ∃ V : X.Opens, Z ⊆ V ∧ IsCompact (V : Set X) := by
  have h : ∀ x : X, ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W := fun x => by
    obtain ⟨W, hW, hxW, -⟩ :=
      Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨W, hW, hxW⟩
  choose W hW hxW using h
  obtain ⟨t, -, ht⟩ := hZ.elim_nhds_subcover (fun x => (W x : Set X))
    fun x _ => (W x).isOpen.mem_nhds (hxW x)
  refine ⟨⨆ x ∈ t, W x, ?_, ?_⟩
  · simpa only [Opens.coe_iSup] using ht
  · simpa only [Opens.coe_iSup] using t.isCompact_biUnion fun x _ => (hW x).isCompact

end Stacks.Cohomology.RelativeExt

end
