module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentThree.DerivedChowFourierMukai
public import StacksFrontier.Algebra.Homology.TotalDegeneration
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.TwoOpenGlueingObjectTransport

/-!
# The derived direct image over an open of the target

The restriction to an open `V` of the derived direct image of a complex vanishes when the
complex restricts to zero over the preimage of `V`, and vanishing over an open propagates
along derived pullback.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.DerivedPushforwardOverOpen

attribute [local instance 100000] HasDerivedCategory.standard

variable {Y S : RingedSpace.{u, u}} (π : Y ⟶ S) (V : Opens S.carrier)

/-- The preimage `π⁻¹V` of an open of the target, as an open of the source. -/
abbrev preimageOpen : Opens Y.carrier := (Opens.map π.hom.base).obj V

/-- The image of an open subspace `U ⊆ φ⁻¹V` of the source, mapped to the target, lies inside
`V`. -/
private theorem range_ofRestrict_comp_subset_of_le {A B : RingedSpace.{u, u}} (φ : A ⟶ B)
    (V : Opens B.carrier) (U : Opens A.carrier) (hU : U ≤ preimageOpen φ V) :
    Set.range (A.ofRestrict U.isOpenEmbedding ≫ φ).hom.base ⊆
      Set.range (B.ofRestrict V.isOpenEmbedding).hom.base := by
  rintro _ ⟨y, rfl⟩
  rw [Stacks.DerivedGlueing.range_ofRestrict]
  exact hU y.2

/-- The image of the open subspace `π⁻¹V`, mapped to `S`, lies inside `V`. -/
theorem range_ofRestrict_comp_subset :
    Set.range (Y.ofRestrict (preimageOpen π V).isOpenEmbedding ≫ π).hom.base ⊆
      Set.range (S.ofRestrict V.isOpenEmbedding).hom.base :=
  range_ofRestrict_comp_subset_of_le π V _ le_rfl

/-- The restriction of `π : Y ⟶ S` over an open `V ⊆ S`, the morphism of ringed spaces
`Y|_{π⁻¹V} ⟶ S|_V`. -/
def restrictPreimage :
    Y.restrict (preimageOpen π V).isOpenEmbedding ⟶ S.restrict V.isOpenEmbedding :=
  InducedCategory.homMk (PresheafedSpace.IsOpenImmersion.lift
    (S.ofRestrict V.isOpenEmbedding).hom
    (Y.ofRestrict (preimageOpen π V).isOpenEmbedding ≫ π).hom
    (range_ofRestrict_comp_subset π V))

/-- The restriction of `π` over `V` is compatible with the two inclusions. -/
@[reassoc]
theorem restrictPreimage_comp :
    restrictPreimage π V ≫ S.ofRestrict V.isOpenEmbedding =
      Y.ofRestrict (preimageOpen π V).isOpenEmbedding ≫ π :=
  InducedCategory.hom_ext (PresheafedSpace.IsOpenImmersion.lift_fac _ _
    (range_ofRestrict_comp_subset π V))

/-- The square formed by the restriction of `π` over an open `V` of the target and the two
inclusions is cartesian. -/
theorem isPullback_restrictPreimage :
    IsPullback (Y.ofRestrict (preimageOpen π V).isOpenEmbedding) (restrictPreimage π V) π
      (S.ofRestrict V.isOpenEmbedding) := by
  have hw : Y.ofRestrict (preimageOpen π V).isOpenEmbedding ≫ π =
      restrictPreimage π V ≫ S.ofRestrict V.isOpenEmbedding :=
    (restrictPreimage_comp π V).symm
  have hrange : ∀ s : PullbackCone π (S.ofRestrict V.isOpenEmbedding),
      Set.range s.fst.hom.base ⊆
        Set.range (Y.ofRestrict (preimageOpen π V).isOpenEmbedding).hom.base := by
    rintro s _ ⟨t, rfl⟩
    rw [Stacks.DerivedGlueing.range_ofRestrict]
    show π.hom.base (s.fst.hom.base t) ∈ V
    have h := congrArg (fun m => m.hom.base t) s.condition
    change π.hom.base (s.fst.hom.base t) =
      (S.ofRestrict V.isOpenEmbedding).hom.base (s.snd.hom.base t) at h
    exact h ▸ (s.snd.hom.base t).2
  let lift : ∀ s : PullbackCone π (S.ofRestrict V.isOpenEmbedding),
      s.pt ⟶ Y.restrict (preimageOpen π V).isOpenEmbedding := fun s =>
    InducedCategory.homMk (PresheafedSpace.IsOpenImmersion.lift
      (Y.ofRestrict (preimageOpen π V).isOpenEmbedding).hom s.fst.hom (hrange s))
  have hlift : ∀ s : PullbackCone π (S.ofRestrict V.isOpenEmbedding),
      lift s ≫ Y.ofRestrict (preimageOpen π V).isOpenEmbedding = s.fst := fun s =>
    InducedCategory.hom_ext (PresheafedSpace.IsOpenImmersion.lift_fac _ _ (hrange s))
  refine IsPullback.of_isLimit' ⟨hw⟩
    (PullbackCone.IsLimit.mk hw lift hlift (fun s => ?_) (fun s m h₁ _ => ?_))
  · rw [← cancel_mono (S.ofRestrict V.isOpenEmbedding), Category.assoc, restrictPreimage_comp,
      ← Category.assoc, hlift, s.condition]
  · rw [← cancel_mono (Y.ofRestrict (preimageOpen π V).isOpenEmbedding), hlift, h₁]

/-- The derived direct image of a complex vanishing over `π⁻¹V` vanishes over `V`: if every term
of a complex `L` of `𝒪_Y`-modules restricts to zero on `π⁻¹V`, then the restriction to `V` of
`Rπ_*L` is zero. -/
theorem isZero_derivedPullback_derivedPushforward
    (L : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ)
    (hL : ∀ n, IsZero ((modulePullback (Y.ofRestrict (preimageOpen π V).isOpenEmbedding)).obj
      (L.X n))) :
    IsZero ((derivedPullback (S.ofRestrict V.isOpenEmbedding)).obj
      ((derivedPushforward π).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)))) := by
  refine IsZero.of_iso ?_ ((DerivedChow.derivedPushforwardRestrictIsoOfStandard π
    (Y.ofRestrict (preimageOpen π V).isOpenEmbedding) (S.ofRestrict V.isOpenEmbedding)
    (restrictPreimage π V) (isPullback_restrictPreimage π V)).app _)
  have := (derivedAdjunction (restrictPreimage π V)).right_adjoint_additive
  refine Functor.map_isZero (derivedPushforward (restrictPreimage π V)) ?_
  have := DerivedChow.isIso_derivedPullbackComparison_of_isOpenImmersion
    (Y.ofRestrict (preimageOpen π V).isOpenEmbedding)
  refine IsZero.of_iso ?_ (asIso ((derivedPullbackComparison
    (Y.ofRestrict (preimageOpen π V).isOpenEmbedding)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj L)))
  exact Functor.map_isZero DerivedCategory.Qh (Functor.map_isZero
    (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
    (StacksDraft.TotalDegeneration.isZero_of_isZero_X
      (K := ((modulePullback (Y.ofRestrict (preimageOpen π
          V).isOpenEmbedding)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L) hL))

/-- Vanishing over an open propagates along derived pullback: if the restriction of `E` to an
open `V` of the target of `φ` vanishes, then so does the restriction of `Lφ^*E` to any open `U`
of the source mapping into `V`. -/
theorem isZero_derivedPullback_derivedPullback_of_le {A B : RingedSpace.{u, u}} (φ : A ⟶ B)
    (V : Opens B.carrier) (U : Opens A.carrier) (hU : U ≤ preimageOpen φ V)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing B)))
    (hE : IsZero ((derivedPullback (B.ofRestrict V.isOpenEmbedding)).obj E)) :
    IsZero ((derivedPullback (A.ofRestrict U.isOpenEmbedding)).obj ((derivedPullback φ).obj
        E)) := by
  have hrange := range_ofRestrict_comp_subset_of_le φ V U hU
  let h : A.restrict U.isOpenEmbedding ⟶ B.restrict V.isOpenEmbedding :=
    InducedCategory.homMk (PresheafedSpace.IsOpenImmersion.lift
      (B.ofRestrict V.isOpenEmbedding).hom (A.ofRestrict U.isOpenEmbedding ≫ φ).hom hrange)
  have hh : h ≫ B.ofRestrict V.isOpenEmbedding = A.ofRestrict U.isOpenEmbedding ≫ φ :=
    InducedCategory.hom_ext (PresheafedSpace.IsOpenImmersion.lift_fac _ _ hrange)
  have := (derivedAdjunction h).right_adjoint_additive
  have := (derivedAdjunction h).left_adjoint_additive
  have h₂ : IsZero ((derivedPullback (h ≫ B.ofRestrict V.isOpenEmbedding)).obj E) :=
    IsZero.of_iso (Functor.map_isZero (derivedPullback h) hE)
      ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical h
        (B.ofRestrict V.isOpenEmbedding)).app E).symm
  rw [hh] at h₂
  exact IsZero.of_iso h₂ ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        (A.ofRestrict U.isOpenEmbedding) φ).app E)

end Stacks.Cohomology.DerivedPushforwardOverOpen
