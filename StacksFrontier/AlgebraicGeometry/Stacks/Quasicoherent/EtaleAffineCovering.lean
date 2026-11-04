module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BaseSites

/-!
# Every object of the associated étale site of a fibred category is covered by affine objects

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids.  Every object `W` of `𝒳` carries
a covering family, for the associated **étale** topology, by objects lying over affine schemes:
an affine open cover of the scheme below `W`, replaced by a chosen covering family of the big
site, is a chosen étale covering family, and its members lift along `p`.

This is `AlgebraicGeometry.FibredSite.exists_affine_ofArrows` for the étale topology instead of
the fppf one; the only additional input is that the chosen covering family tautologically
equivalent to an open cover is an étale covering.

## Main results

* `AlgebraicGeometry.FibredSite.exists_affine_etale_ofArrows`: the étale covering family.
* `AlgebraicGeometry.FibredSite.mem_etale_of_forall_isAffine`: every sieve containing all the
  arrows out of objects lying over affine schemes is a covering sieve of the associated étale
  site.
-/

@[expose] public section

open CategoryTheory

universe v w u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- **Every object of the associated étale site carries a covering family by affine objects.** -/
theorem exists_affine_etale_ofArrows (hp : p.IsFiberedInGroupoids) (W : 𝒳) :
    ∃ (I : Type (u + 1)) (y : I → 𝒳) (φ : ∀ j, y j ⟶ W),
      (∀ j, IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (y j)))) ∧
        Sieve.ofArrows y φ ∈ BigFppfOver.associatedTopology B S hS p .etale W := by
  classical
  let U := (B.inclusion.obj (p.obj W).left).affineOpenCover.openCover
  obtain ⟨V, hV, hVU⟩ := exists_isCovering_tautologicallyEquivalent_openCover B
    (p.obj W).left U
  obtain ⟨⟨α, hα⟩, β, hβ⟩ := hVU
  have hVaff (j : V.I₀) : IsAffine (B.inclusion.obj (V.X j)) := by
    obtain ⟨e, -⟩ := hβ j
    exact @IsAffine.of_isIso _ _ e.hom e.isIso_hom (isAffine_Spec _)
  have hVet : IsEtaleCovering ⟨(p.obj W).left, V⟩ := by
    show (V.map B.inclusion).presieve₀ ∈ Scheme.precoverage @Etale _
    refine (Scheme.presieve₀_mem_precoverage_iff (V.map B.inclusion)).2 ⟨fun x => ?_, fun j => ?_⟩
    · obtain ⟨i, hi⟩ := U.exists_eq x
      obtain ⟨e, he⟩ := hα i
      obtain ⟨z, rfl⟩ := hi
      refine ⟨α i, e.hom.base z, ?_⟩
      rw [← Scheme.Hom.comp_apply, he]
    · obtain ⟨e, he⟩ := hβ j
      rw [← he]
      infer_instance
  let Vobj (j : V.I₀) : BigFppfOver B S hS := Over.mk (V.f j ≫ (p.obj W).hom)
  let vmap (j : V.I₀) : Vobj j ⟶ p.obj W := Over.homMk (V.f j)
  have hBcover : Sieve.ofArrows Vobj vmap ∈
      BigFppfOver.baseOverTopology B S hS .etale (p.obj W) := by
    show Sieve.ofArrows Vobj vmap ∈ (B.etaleTopology.over (B.obj hS)) (p.obj W)
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    show Sieve.ofArrows V.X V.f ∈ B.etaleTopology (p.obj W).left
    have hpre : V.presieve₀ ∈ B.etalePrecoverage (p.obj W).left := ⟨V, rfl, hV, hVet⟩
    simpa [PreZeroHypercover.presieve₀] using Precoverage.generate_mem_toGrothendieck hpre
  choose y φ hφ using fun j => hp.exists_lift (vmap j) W rfl
  have hdom : ∀ j, p.obj (y j) = Vobj j := fun j => by
    have := hφ j; exact IsHomLift.domain_eq p (vmap j) (φ j)
  have hvmapmem : ∀ j, (Sieve.ofArrows (fun k => p.obj (y k)) fun k => p.map (φ k)) (vmap j) := by
    intro j
    refine (Sieve.mem_ofArrows_iff _ _ _).2 ⟨j, eqToHom (hdom j).symm, ?_⟩
    have := hφ j
    simpa using IsHomLift.fac p (vmap j) (φ j)
  have hfib : p.IsFibered := hp.isFibered
  refine ⟨V.I₀, y, φ, fun j => ?_, ?_⟩
  · rw [hdom j]
    exact hVaff j
  · refine (Functor.isInheritedTopology_inheritedTopology p
      (BigFppfOver.baseOverTopology B S hS .etale) y φ
      fun j => hp.isStronglyCartesian (φ j)).2 ?_
    refine (BigFppfOver.baseOverTopology B S hS .etale).superset_covering ?_ hBcover
    intro Z g hg
    obtain ⟨j, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
    exact (Sieve.ofArrows (fun k => p.obj (y k)) fun k => p.map (φ k)).downward_closed
      (hvmapmem j) a

/-- **Every sieve containing all the arrows out of objects lying over affine schemes is a
covering sieve** of the associated étale site. -/
theorem mem_etale_of_forall_isAffine (hp : p.IsFiberedInGroupoids) (U : 𝒳) (T : Sieve U)
    (hT : ∀ ⦃V : 𝒳⦄ (f : V ⟶ U), IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj V)) →
      T f) :
    T ∈ BigFppfOver.associatedTopology B S hS p .etale U := by
  obtain ⟨I, y, φ, haff, hcov⟩ := exists_affine_etale_ofArrows B S hS p hp U
  refine (BigFppfOver.associatedTopology B S hS p .etale).superset_covering ?_ hcov
  rintro W g ⟨Y, a, b, ⟨j⟩, rfl⟩
  exact T.downward_closed (hT (φ j) (haff j)) a

end AlgebraicGeometry.FibredSite
