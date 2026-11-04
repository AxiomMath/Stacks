module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCoproductRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineReductionRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasJointSurjectivity
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import StacksCore.CategoryTheory.Pullback
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.EtaleCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactMorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.QuasiCompactSpaceCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasFiniteSubcoverRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionRefined

/-!
# Criteria for a formal algebraic space to be quasi-compact

Let `X` be a formal algebraic space over `S` and let `i : Xred ⟶ X` be a reduction of `X`.
Stacks 0AJ9 says that `Xred` is a quasi-compact algebraic space if and only if `X` has a formal
atlas indexed by a finite type, if and only if `X` receives a representable étale surjection
from an affine formal algebraic space.

## Main results

* `AlgebraicGeometry.FormalSpace.affineReductionsQuasiCompact`: an affine formal algebraic space
  has quasi-compact reductions.
* `AlgebraicGeometry.FormalSpace.hasFiniteFormalAtlas_of_isQuasiCompactSpaceULift_reduction`:
  the implication (1) ⇒ (2) of Stacks 0AJ9.
* `AlgebraicGeometry.FormalSpace.tfae_isQuasiCompactSpace'`: Stacks 0AJ9.

## References

* [Stacks Project, Tag 0AJ9](https://stacks.math.columbia.edu/tag/0AJ9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Reductions of affine formal algebraic spaces -/

/-- **An affine formal algebraic space over `S` is quasi-compact as a space**: every reduction
of one is a quasi-compact algebraic space, which is the assertion
`AffineReductionsQuasiCompact`. -/
theorem affineReductionsQuasiCompact : AffineReductionsQuasiCompact B S hS := by
  intro Y Yred iY hY hiY
  obtain ⟨Yred', i', T, hTaffine, ⟨eT⟩, hi'⟩ :=
    exists_isReduction_isAffine_of_isAffineFormalAlgebraicSpace B S hS Y hY
  obtain ⟨e⟩ := hi'.nonempty_iso hiY
  refine Space.isQuasiCompactSpaceULift_of_iso B S hS
    (eT ≪≫ (sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).mapIso e) ?_
  exact ⟨T, 𝟙 _, @Scheme.compactSpace_of_isAffine _ hTaffine,
    Space.relative_id_surjective B S hS T, fun _ φ hφ ↦ by simpa using hφ⟩

/-! ### The implication (3) ⇒ (1) -/

/-- **Stacks 0AJ9, the implication (3) ⇒ (1).** Let `X` be a quasi-compact formal algebraic
space over `S` and let `i : Xred ⟶ X` be a reduction of `X`. Then `Xred` is a quasi-compact
algebraic space. -/
theorem IsQuasiCompactSpace.isQuasiCompactSpaceULift_reduction'
    (hReductionEtaleSurjective : ReductionsOfEtaleSurjectionsEtaleSurjective B S hS)
    {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X} (hi : IsReduction B S hS X Xred i)
    (h : IsQuasiCompactSpace B S hS X) :
    Space.IsQuasiCompactSpaceULift.{u + 1} B S hS Xred.obj := by
  obtain ⟨-, Y, c, haffine, hetale, hsurjective⟩ := h
  obtain ⟨Yred, iY, hiY⟩ := exists_isReduction_of_isAffineFormalAlgebraicSpace B S hS Y haffine
  obtain ⟨g, hg, -⟩ := hi.universal Yred hiY.algebraic hiY.reduced (iY ≫ c)
  obtain ⟨hgSurjective, hgEtale⟩ :=
    hReductionEtaleSurjective Y X Yred Xred c iY i g hiY hi hetale hsurjective hg
  obtain ⟨U, φ, hUcompact, hφSurjective, hφEtale⟩ :=
    affineReductionsQuasiCompact B S hS Y Yred iY haffine hiY
  exact ⟨U, φ ≫ g.hom, hUcompact,
    MorphismProperty.comp_mem _ _ _ hφSurjective hgSurjective,
    isEtaleULift_comp B S hS hφEtale hgEtale⟩

/-! ### The implication (1) ⇒ (2) -/

/-- **A finite jointly surjective subfamily of a prescribed covering of a formal algebraic
space with quasi-compact reduction.** Let `X` be an fppf sheaf on the big fppf site of `S`, let
`i : Xred ⟶ X` be a reduction of `X` whose source is a quasi-compact algebraic space, and let
`{Xᵢ ⟶ X}` be a covering as in Definition 0AIM. Then finitely many members of the *given*
covering are already jointly surjective: there are a finite type `K` and a reindexing
`k : K → I` for which `∐ⱼ X_{k j} ⟶ X` is still a surjection of sheaves. -/
theorem exists_finite_subfamily_jointly_surjective_of_isQuasiCompactSpaceULift_reduction
    {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X}
    (hi : IsReduction B S hS X Xred i)
    (hQC : Space.IsQuasiCompactSpaceULift.{u + 1} B S hS Xred.obj)
    {I : Type (u + 1)} {Xi : I → FppfSheaf B S hS} (f : ∀ i, Xi i ⟶ X)
    (haffine : ∀ i, IsAffineFormalAlgebraicSpace B S hS (Xi i))
    (hetale : ∀ i, ∃ hfi : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (f i).hom,
      Space.HasPropertyULift.{u + 1} B S hS
        (fun _ _ g ↦ Space.IsEtaleULift.{u + 1} B S hS g.hom) (f i).hom hfi)
    (hsurjective : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc f)) :
    ∃ (K : Type (u + 1)) (_ : Finite K) (k : K → I),
      letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
      Sheaf.IsLocallySurjective (Sigma.desc fun j ↦ f (k j)) := by
  classical
  let _ : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨U, g, hUcompact, hgsurj, -⟩ := hQC
  let c : uliftYoneda.{u + 1}.obj U ⟶ X.obj := g ≫ i.hom
  obtain ⟨K, k, V, q, ξ, hKfin, hsq, -, hcover⟩ :=
    exists_finite_subfamily_pullback_cover_of_compactSpace B S hS f haffine hetale hsurjective c
  refine ⟨K, hKfin, k, ?_⟩
  refine isLocallySurjective_sigmaDesc_of_jointly_surjective_points B S hS
    (fun j ↦ f (k j)) (fun j ↦ haffine (k j)) (fun j ↦ hetale (k j)) ?_
  intro x
  obtain ⟨xr, hxr⟩ := hi.bijective_pointsMapULift.2 x
  obtain ⟨pU, hpU⟩ := surjective_pointsMapULift_of_relative_surjective B S hS g hgsurj xr
  obtain ⟨j, w, hw⟩ := hcover (Space.pointsEquivSchemeULift.{u + 1} B S hS U pU)
  let pV : Space.pointsULift.{u + 1} B S hS (uliftYoneda.{u + 1}.obj (V j)) :=
    (Space.pointsEquivSchemeULift.{u + 1} B S hS (V j)).symm w
  have hqV : Space.pointsMapULift B S hS _ (uliftYoneda.{u + 1}.map (q j)) pV = pU := by
    refine (Space.pointsEquivSchemeULift.{u + 1} B S hS U).injective ?_
    rw [Space.pointsEquivSchemeULift_naturality B S hS (q j) pV,
      show Space.pointsEquivSchemeULift.{u + 1} B S hS (V j) pV = w from
        (Space.pointsEquivSchemeULift.{u + 1} B S hS (V j)).apply_symm_apply w]
    exact hw
  refine ⟨j, Space.pointsMapULift B S hS _ (ξ j) pV, ?_⟩
  calc Space.pointsMapULift B S hS _ (f (k j)).hom
          (Space.pointsMapULift B S hS _ (ξ j) pV)
      = Space.pointsMapULift B S hS _ (ξ j ≫ (f (k j)).hom) pV := by
        rw [Space.pointsMapULift_comp]; rfl
    _ = Space.pointsMapULift B S hS _ (uliftYoneda.{u + 1}.map (q j) ≫ c) pV := by
        rw [(hsq j).w]
    _ = Space.pointsMapULift B S hS _ c
          (Space.pointsMapULift B S hS _ (uliftYoneda.{u + 1}.map (q j)) pV) := by
        rw [Space.pointsMapULift_comp]; rfl
    _ = Space.pointsMapULift B S hS _ c pU := by rw [hqV]
    _ = Space.pointsMapULift B S hS Xred.obj i.hom
          (Space.pointsMapULift B S hS _ g pU) := by
        change Space.pointsMapULift B S hS _ (g ≫ i.hom) pU = _
        exact congrFun (Space.pointsMapULift_comp B S hS _ g i.hom) pU
    _ = x := by rw [hpU, hxr]

/-- **Stacks 0AJ9, the implication (1) ⇒ (2).** Let `X` be a formal algebraic space over `S`,
let `i : Xred ⟶ X` be a reduction of `X` and suppose that `Xred` is a quasi-compact algebraic
space. Then `X` has a finite formal atlas: an atlas as in Definition 0AIM indexed by a finite
type. -/
@[stacks 0AJ9 "the implication (1) ⇒ (2), for an arbitrary reduction of X"]
theorem hasFiniteFormalAtlas_of_isQuasiCompactSpaceULift_reduction
    {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X}
    (hX : IsFormalAlgebraicSpace B S hS X) (hi : IsReduction B S hS X Xred i)
    (hQC : Space.IsQuasiCompactSpaceULift.{u + 1} B S hS Xred.obj) :
    HasFiniteFormalAtlas B S hS X := by
  obtain ⟨hset, I, Xi, f, haffine, hetale, hsurjective⟩ := hX
  obtain ⟨K, hKfin, k, hcover⟩ :=
    exists_finite_subfamily_jointly_surjective_of_isQuasiCompactSpaceULift_reduction B S hS hi
      hQC f haffine hetale hsurjective
  exact ⟨hset, K, fun j ↦ Xi (k j), fun j ↦ f (k j), hKfin, fun j ↦ haffine (k j),
    fun j ↦ hetale (k j), hcover⟩

/-! ### The equivalence of the three conditions -/

/-- **Stacks 0AJ9.** Let `X` be a formal algebraic space over `S` and let `i : Xred ⟶ X` be a
reduction of `X`. The following are equivalent:

1. `Xred` is a quasi-compact algebraic space,
2. `X` admits an atlas as in Definition 0AIM indexed by a finite type,
3. `X` receives a morphism from an affine formal algebraic space which is representable by
   algebraic spaces, étale and a surjection of sheaves. -/
theorem tfae_isQuasiCompactSpace'
    (hReductionEtaleSurjective : ReductionsOfEtaleSurjectionsEtaleSurjective B S hS)
    (hCoproductEtale : CoproductsRepresentableEtale B S hS)
    {X Xred : FppfSheaf B S hS} {i : Xred ⟶ X}
    (hX : IsFormalAlgebraicSpace B S hS X) (hi : IsReduction B S hS X Xred i) :
    [Space.IsQuasiCompactSpaceULift.{u + 1} B S hS Xred.obj,
      HasFiniteFormalAtlas B S hS X,
      IsQuasiCompactSpace B S hS X].TFAE := by
  tfae_have 1 → 2 := hasFiniteFormalAtlas_of_isQuasiCompactSpaceULift_reduction B S hS hX hi
  tfae_have 2 → 3 := HasFiniteFormalAtlas.isQuasiCompactSpace B S hS hCoproductEtale
  tfae_have 3 → 1 := IsQuasiCompactSpace.isQuasiCompactSpaceULift_reduction' B S hS
    hReductionEtaleSurjective hi
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
