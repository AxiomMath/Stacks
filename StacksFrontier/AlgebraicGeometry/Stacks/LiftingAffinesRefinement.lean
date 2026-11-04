module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesSigmaDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesEtaleCovering
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAmbientSize
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC

/-!
# Refining a covering of the spaces-étale site by affine schemes of bounded size (Stacks 0CJU)

The proof of Stacks 0CJU begins: "in order to prove effectivity we may first refine the
covering", to a covering by affine schemes. For the descent to be carried out with disjoint
unions in the chosen big fppf site, the refinement has to be of bounded size: fewer members than
the site's cutoff, each of size bounded uniformly below the cutoff. This file produces such a
refinement of every covering sieve of the spaces-étale site of `W`.

Fix an étale surjective chart `T₀ ⟶ U` by a scheme of the site. Through the image of each point
`τ` of `T₀` the covering sieve has a member `V ⟶ U` hitting it; an affine étale chart of
`V ×_U T₀` through a point over `τ` is an affine scheme `A_τ`, étale over `T₀`, whose composite
to `U` lies in the sieve. Being étale and quasi-compact over `T₀`, `A_τ` has size at most that of
`T₀` (Stacks 04T7), and there are at most `2 ^ size T₀` points `τ`.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.exists_affine_refinement`: the refinement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.SpacesEtale

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {W : AlgebraicSpaces B S hS}

/-- **One member of the refinement.** Given an étale chart `t₀ : T₀ ⟶ U` and a pointwise
covering sieve `R` of `U`, through the image of every point of `T₀` there is an affine scheme
étale over `W`, of size at most that of `T₀`, with a morphism to `U` in `R` hitting that
image. -/
theorem exists_affine_member (U : SpacesEtale B S hS W) (T₀ : BigFppfOver B S hS)
    (t₀ : yoneda.obj T₀ ⟶ U.obj.left.obj) (ht₀ : IsEtale B S hS t₀) (R : Sieve U)
    (hR : SievePointwiseCover B S hS W R) (q : points B S hS (yoneda.obj T₀)) :
    ∃ (A : BigFppfOver B S hS) (a : yoneda.obj A ⟶ W.obj) (ha : IsEtale B S hS a)
      (g : ofRepresentable B S hS W A a ha ⟶ U), R g ∧
        IsAffine ((BigFppfOver.toScheme B S hS).obj A) ∧
        ((BigFppfOver.toScheme B S hS).obj A).size ≤ ((BigFppfOver.toScheme B S hS).obj T₀).size ∧
        ∃ z : points B S hS (yoneda.obj A),
          pointsMap B S hS _ g.hom.left.hom z = pointsMap B S hS _ t₀ q := by
  let T := ofRepresentable B S hS W T₀ (t₀ ≫ U.obj.hom.hom) (isEtale_comp B S hS ht₀ U.property)
  let tU : T ⟶ U :=
    ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk t₀) (ObjectProperty.hom_ext _ rfl))
  obtain ⟨V, g, hg, y, hy⟩ := hR (pointsMap B S hS _ t₀ q)
  obtain ⟨y', hy'₁, -⟩ := exists_point_of_isPullback_toSpaces (IsPullback.of_hasPullback g tU)
    y q hy
  obtain ⟨A, a, hAaff, haet, z, hz⟩ := exists_affine_etale_chart_at_point B S hS
    (pullback g tU).obj.left.obj (pullback g tU).obj.left.property y'
  have haW : IsEtale B S hS (a ≫ (pullback g tU).obj.hom.hom) :=
    isEtale_comp B S hS (isEtale_of_presheaf_etale B S hS haet) (pullback g tU).property
  let nV : ofRepresentable B S hS W A _ haW ⟶ pullback g tU :=
    ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk a) (ObjectProperty.hom_ext _ rfl))
  refine ⟨A, _, haW, nV ≫ pullback.fst g tU ≫ g, ?_, hAaff, ?_, z, ?_⟩
  · simpa only [Category.assoc] using R.downward_closed hg (nV ≫ pullback.fst g tU)
  · let s := nV ≫ pullback.snd g tU
    have hs : IsEtale B S hS ((toSpaces B S hS W).map s).hom := isEtale_toSpaces_map B S hS W s
    let s₀ : A ⟶ T₀ := yoneda.preimage ((toSpaces B S hS W).map s).hom
    have hs₀ : yoneda.map s₀ = ((toSpaces B S hS W).map s).hom := yoneda.map_preimage _
    have : Etale ((BigFppfOver.toScheme B S hS).map s₀) :=
      (presheaf_yoneda_map_etale_iff B S hS s₀).1
        ((isEtale_iff_presheaf_of_yoneda B S hS _).1 (hs₀ ▸ hs))
    have := hAaff
    exact Scheme.size_le_of_locallyOfFiniteType ((BigFppfOver.toScheme B S hS).map s₀)
  · show pointsMap B S hS _ (a ≫ (pullback.fst g tU).hom.left.hom ≫ g.hom.left.hom) z = _
    rwa [pointsMap_comp_apply, pointsMap_comp_apply, hz, hy'₁]

/-- **Stacks 0CJU, the refinement.** Every covering sieve of an object `U` of the spaces-étale
site of `W` contains a jointly surjective family of affine schemes indexed by the points of an
étale chart `T₀` of `U`, each of size at most that of `T₀`. -/
theorem exists_affine_refinement (U : SpacesEtale B S hS W) (R : Sieve U)
    (hR : R ∈ topology B S hS W U) :
    ∃ (T₀ : BigFppfOver B S hS)
      (nN : (BigFppfOver.toScheme B S hS).obj T₀ → BigFppfOver B S hS)
      (N : (BigFppfOver.toScheme B S hS).obj T₀ → SpacesEtale B S hS W)
      (_ : ∀ τ, yoneda.obj (nN τ) ≅ (N τ).obj.left.obj) (f : ∀ τ, N τ ⟶ U),
      (∀ τ, R (f τ)) ∧ (∀ τ, IsAffine ((BigFppfOver.toScheme B S hS).obj (nN τ))) ∧
      (∀ τ, ((BigFppfOver.toScheme B S hS).obj (nN τ)).size ≤
        ((BigFppfOver.toScheme B S hS).obj T₀).size) ∧
      ∀ p : points B S hS U.obj.left.obj, ∃ (τ : (BigFppfOver.toScheme B S hS).obj T₀)
        (z : points B S hS (N τ).obj.left.obj), pointsMap B S hS _ (f τ).hom.left.hom z = p := by
  obtain ⟨T₀, t₀, hsurj, het⟩ := U.obj.left.property.exists_atlas
  have hsurj' := (surjective_iff_surjective_pointsMap B S hS _ U.obj.left.property T₀ t₀).mp hsurj
  have hR' := (mem_topology_iff_sievePointwiseCover B S hS W R).1 hR
  choose A a ha g hg hA hsz z hz using fun τ =>
    exists_affine_member U T₀ t₀ ((isEtale_iff_presheaf_of_yoneda B S hS t₀).2 het) R hR'
      ((pointsEquivScheme B S hS T₀).symm τ)
  refine ⟨T₀, A, fun τ => ofRepresentable B S hS W (A τ) (a τ) (ha τ), fun τ => Iso.refl _, g,
    hg, hA, hsz, fun p => ?_⟩
  obtain ⟨q, rfl⟩ := hsurj' p
  refine ⟨pointsEquivScheme B S hS T₀ q, z _, ?_⟩
  rw [hz, Equiv.symm_apply_apply]

end AlgebraicGeometry.Space.SpacesEtale
