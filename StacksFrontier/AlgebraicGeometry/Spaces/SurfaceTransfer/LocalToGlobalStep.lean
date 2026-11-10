module

public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.ExistenceByNormalizedBlowUps
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalencePort
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPointsProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPointsResidualSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationsAtClosedPointsSinglePoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.EtaleChartNeighborhood
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.NormalizedBlowupLiftStep

/-!
# Lifting one normalized blowing up from an étale neighbourhood to the whole space

Let `X` be a decent algebraic space over a scheme `S` with pairwise distinct closed points
`x₁, …, xₙ` and chosen elementary étale neighbourhoods `(Uᵢ, uᵢ) ⟶ (X, xᵢ)` (Stacks 0BH9). Let
`g : A ⟶ X` be a normal, locally Noetherian algebraic space over `X` whose base change to `Uᵢ` is
represented by a scheme `Z` over `Uᵢ`, and let `Z' ⟶ Z` be the normalized blowup of `Z` at a
closed point lying over `uᵢ`. This file produces the normalized blowing up `A' ⟶ A` at the
corresponding closed point of `A` whose base change to `Uᵢ` is `Z'`, and shows that over every
étale `P ⟶ X` missing `xᵢ` the base change does not change.

This is one step of the "local to global" direction of Stacks 0BHL, in the form in which the
proof of (4) `⇒` (3) of Stacks 0BHY uses it: a sequence of normalized blowups of the
neighbourhood `Uᵢ` at points over `uᵢ` is lifted to `A` one blowing up at a time.

## Main definitions

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.StageRep`: the base change of `g : A ⟶ X` to
  the `i`th neighbourhood is represented by a given scheme over that neighbourhood.

## Main results

* `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_lift_isNormalizedBlowUpOutside`: the
  lifting step.

## References

* [Stacks Project, Tag 0BHL](https://stacks.math.columbia.edu/tag/0BHL)
* [Stacks Project, Tag 0BH9](https://stacks.math.columbia.edu/tag/0BH9)
* [Stacks Project, Tag 0BHY](https://stacks.math.columbia.edu/tag/0BHY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site goes deep
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_LocalToGlobalStep :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_LocalToGlobalStep
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- The scheme of the `i`th chosen neighbourhood. -/
abbrev neighborhoodScheme (i : Fin n) : Scheme.{u} :=
  (BigFppfOver.toScheme B S hS).obj (D.neighborhood i).scheme

/-- **The base change of `g : A ⟶ X` to the `i`th neighbourhood is represented by the scheme `Z`
over that neighbourhood**: there are an object `W` of the site over the neighbourhood whose
functor of points is the base change, and an isomorphism of `W` with `Z` over the
neighbourhood. -/
def StageRep (i : Fin n) {A : AlgebraicSpaces B S hS} (g : A ⟶ D.space)
    (Z : Over (D.neighborhoodScheme i)) : Prop :=
  ∃ (W : BigFppfOver B S hS) (q : W ⟶ (D.neighborhood i).scheme)
    (Φ : pullback g.hom (D.toSpaceHom i).hom ≅ yoneda.obj W)
    (θ : (BigFppfOver.toScheme B S hS).obj W ≅ Z.left),
    Φ.hom ≫ yoneda.map q = pullback.snd g.hom (D.toSpaceHom i).hom ∧
      θ.hom ≫ Z.hom = (BigFppfOver.toScheme B S hS).map q

/-- The distinguished point of a neighbourhood, read through the comparison of points of a
represented functor with the points of the scheme. -/
theorem neighborhoodPoint_eq_schemeSpacePoint (i : Fin n) :
    D.neighborhoodPoint i = schemeSpacePoint (D.neighborhood i).scheme (D.neighborhood i).point :=
  (pointsEquivScheme B S hS _).injective (by
    rw [schemeSpacePoint, Equiv.apply_symm_apply]
    exact pointsToScheme_presheafPoint B S hS _ _ _)

variable [HasSheafify (BigFppfOver.topology B S hS) (Type u)]

/-- **One normalized blowing up of the `i`th neighbourhood at a point over `uᵢ` lifts to `A`.**
If the base change of `g : A ⟶ X` to the `i`th neighbourhood is represented by the scheme `Z` and
`Z'` is obtained from `Z` by a normalized blowing up at a closed point over `uᵢ`, then there is a
normalized blowing up `g₁ : A' ⟶ A` at a closed point of `A` such that the base change of
`g₁ ≫ g` to the `i`th neighbourhood is represented by `Z'`, while over every étale `P ⟶ X` none
of whose points maps to `xᵢ` the base change of `g₁ ≫ g` is that of `g`. -/
theorem exists_lift_isNormalizedBlowUpOutside (i : Fin n) {A : AlgebraicSpaces B S hS}
    (g : A ⟶ D.space) (hAn : Space.IsNormal B S hS A.obj)
    (hAnoeth : HasEtaleLocalProperty B S hS A.obj (fun T : Scheme.{u} => IsLocallyNoetherian T))
    {U : (D.neighborhoodScheme i).Opens} (hU : ∀ y, y ∉ U → y = (D.neighborhood i).point)
    {Z Z' : Over (D.neighborhoodScheme i)} (hZ : D.StageRep i g Z)
    (hstep : IsNormalizedBlowUpOutside U Z Z') :
    ∃ (A' : AlgebraicSpaces B S hS) (g₁ : A' ⟶ A) (z : points B S hS A.obj)
      (hz : IsClosed ({z} : Set (points B S hS A.obj))),
      IsNormalizationOfBlowupAtClosedPoint B S hS z hz g₁ ∧ D.StageRep i (g₁ ≫ g) Z' ∧
        ∀ {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS P →
          ∀ (c : P ⟶ D.space.obj), IsEtale B S hS c →
            (∀ p, pointsMap B S hS P c p ≠ D.point i) →
            ∃ e : pullback (g₁.hom ≫ g.hom) c ≅ pullback g.hom c,
              e.hom ≫ pullback.snd g.hom c = pullback.snd (g₁.hom ≫ g.hom) c := by
  obtain ⟨W, q, Φ, θ, hΦ, hθ⟩ := hZ
  obtain ⟨hZfin, x, hx, hxU, e, he⟩ := hstep
  set φ := D.toSpaceHom i
  -- the point of `W` corresponding to the centre
  obtain ⟨w, rfl⟩ : ∃ w, θ.hom w = x := ⟨θ.inv x, by simp⟩
  have hw : IsClosed ({w} : Set ((BigFppfOver.toScheme B S hS).obj W)) := by
    have h := θ.inv.isClosedEmbedding.isClosedMap _ hx
    have hww : θ.inv (θ.hom w) = w := by rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
    rwa [Set.image_singleton, hww] at h
  have hWfin : ∀ V : ((BigFppfOver.toScheme B S hS).obj W).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj W)) →
        (irreducibleComponents V).Finite :=
    finiteIrreducibleComponents_of_etale θ.hom hZfin
  have hWv : (BigFppfOver.toScheme B S hS).map q w = (D.neighborhood i).point := by
    rw [← hθ, Scheme.Hom.comp_apply]
    exact hU _ hxU
  -- the corresponding point of the base change and of `A`
  set t := pointsMap B S hS _ Φ.inv (schemeSpacePoint W w) with htdef
  have ht : IsClosed ({t} : Set (points B S hS (pullback g.hom φ.hom))) := by
    have := isClosedMap_pointsMap_of_isIso B S hS Φ.inv _
      (isClosed_singleton_schemeSpacePoint W hw)
    convert this using 1
    exact Set.image_singleton.symm
  have htv : pointsMap B S hS _ (pullback.snd g.hom φ.hom) t = D.neighborhoodPoint i := by
    have hcomp : Φ.inv ≫ pullback.snd g.hom φ.hom = yoneda.map q :=
      (congrArg (Φ.inv ≫ ·) hΦ).symm.trans (Iso.inv_hom_id_assoc Φ _)
    have h1 : pointsMap B S hS (yoneda.obj W) (yoneda.map q) (schemeSpacePoint W w) =
        schemeSpacePoint _ ((BigFppfOver.toScheme B S hS).map q w) := by
      have := congrFun (pointsMap_yoneda_map_eq B S hS q) (schemeSpacePoint W w)
      simpa using this
    rw [htdef, ← pointsMap_comp_apply, hcomp]
    exact h1.trans (by rw [hWv, D.neighborhoodPoint_eq_schemeSpacePoint])
  have htx : pointsMap B S hS A.obj g.hom
      (pointsMap B S hS _ (pullback.fst g.hom φ.hom) t) = D.point i := by
    rw [← pointsMap_comp_apply, pullback.condition, pointsMap_comp_apply, htv]
    exact D.pointsMap_toSpaceHom_neighborhoodPoint i
  set z := pointsMap B S hS _ (pullback.fst g.hom φ.hom) t with hzdef
  have hz : IsClosed ({z} : Set (points B S hS A.obj)) :=
    isClosed_singleton_pointsMap_fst_of_isIso_fromPreimage (D.neighborhoodSpace i).property
      D.space.property A.property φ.hom (D.neighborhood i).etale_toSpace g.hom
      (D.pointSubspace i) (D.isIso_fromPreimage_pointSubspace i)
      (D.range_pointsMap_ι_pointSubspace i) (D.isClosed_point i) ht htx
  -- the normalized blowing up of `A` at `z`
  obtain ⟨Ab, b, hb, hAbfin⟩ :=
    exists_isBlowupAlong_of_isLocallyNoetherian hAnoeth (closedPointSubspace B S hS z hz)
  have hAfin : HasLocallyFiniteIrreducibleComponents B S hS A.obj := by
    obtain ⟨V, f, hfs, hfe, hV⟩ := hAnoeth
    have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj V) := hV
    exact (exists_surjective_etale_chart_iff_hasLocallyFiniteIrreducibleComponents B S hS
      A.property).mp ⟨V, f, isSurjective_of_presheafSurjective B S hS f hfs,
        isEtale_of_presheaf_etale B S hS hfe, finite_irreducibleComponents_of_isCompact _⟩
  have hWnoeth : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj W) := by
    have hfst : IsEtale B S hS (pullback.fst g.hom φ.hom) :=
      isEtale_pullback_fst B S hS A.property D.space.property (D.neighborhoodSpace i).property
        _ _ (D.neighborhood i).etale_toSpace
    exact (exists_atlas_iff_forall_etale B S hS A.obj
      (fun T : Scheme.{u} => IsLocallyNoetherian T) A.property).mp hAnoeth W
      (Φ.inv ≫ pullback.fst g.hom φ.hom)
      (presheaf_etale_of_isEtale B S hS (isEtale_comp B S hS (isEtale_of_iso B S hS Φ.symm) hfst))
  obtain ⟨Dν⟩ := nonempty_normalizationData B S hS Ab.property (hAbfin hAfin)
  let A' : AlgebraicSpaces B S hS := ⟨Dν.space, Dν.isAlgebraicSpace⟩
  let g₁ : A' ⟶ A := ObjectProperty.homMk (Dν.hom ≫ b.hom)
  have hg₁ : IsNormalizationOfBlowupAtClosedPoint B S hS z hz g₁ :=
    ⟨Ab, b, isBlowupAtClosedPoint_of_isBlowupAlong hb, Dν, Iso.refl _, by simp [g₁]⟩
  refine ⟨A', g₁, z, hz, hg₁, ?_, ?_⟩
  · -- the base change to the `i`th neighbourhood
    have hfib : pointsMap B S hS _ (Φ.inv ≫ pullback.fst g.hom φ.hom) ⁻¹' {z} =
        {schemeSpacePoint W w} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, pointsMap_comp_apply]
      constructor
      · intro hy
        have h1 := pointsMap_fst_injOn_of_isIso_fromPreimage φ.hom g.hom (D.pointSubspace i)
          (D.isIso_fromPreimage_pointSubspace i) (D.range_pointsMap_ι_pointSubspace i)
          htx hy.symm
        have h2 := congrArg (pointsMap B S hS _ Φ.hom) h1
        rw [htdef, ← pointsMap_comp_apply, ← pointsMap_comp_apply, Iso.inv_hom_id,
          pointsMap_id] at h2
        exact h2.symm
      · intro hy
        rw [hy]
    obtain ⟨N, q', e', ψ, he', hq'⟩ := exists_iso_pullback_comp_normalizedBlowUpScheme g hg₁ φ.hom
      (D.neighborhood i).etale_toSpace q Φ hΦ hWfin hw hfib
    obtain ⟨m, hm⟩ := exists_normalizedBlowUpScheme_iso_of_iso θ hWfin hZfin w hw hx
    refine ⟨N, q' ≫ q, e', ψ ≪≫ m ≪≫ e.symm, ?_, ?_⟩
    · change e'.hom ≫ yoneda.map (q' ≫ q) = pullback.snd (g₁.hom ≫ g.hom) φ.hom
      rw [Functor.map_comp]
      exact he'
    · have he₁ : e.inv ≫ Z'.hom = Stacks.Blowup.normalizedBlowUp _ hZfin _ hx ≫ Z.hom := by
        rw [Iso.inv_comp_eq, ← he]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Functor.map_comp]
      rw [he₁, ← Category.assoc m.hom, hm, Category.assoc, hθ, ← Category.assoc, hq']
  · intro P hP c hc hcx
    have hnormal : Space.IsNormal B S hS (pullback g.hom c) :=
      hasEtaleLocalProperty_of_isEtale B S hS
        (isAlgebraicSpace_pullback B S hS g.hom c A.property hP D.space.property) A.property
        (isEtale_pullback_fst B S hS A.property D.space.property hP _ _ hc) hAn
    refine exists_iso_pullback_comp_of_isNormalizationOfBlowupAtClosedPoint g hg₁ hP c hc
      hnormal fun p hp => hcx (pointsMap B S hS _ (pullback.snd g.hom c) p) ?_
    rw [← pointsMap_comp_apply, ← pullback.condition, pointsMap_comp_apply, hp, hzdef, htx]

end ClosedPointNeighborhoods

end AlgebraicGeometry.Space
