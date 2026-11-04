module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModulePullbackBigSitesMixed
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ChosenCoverings

/-!
# Objects lying over affine schemes cover for the Zariski and étale topologies

Every object `x` of a category fibred in groupoids `p : 𝒳 ⥤ (Sch/S)_{fppf}` lies over a scheme
`U`; an affine open cover of `U`, lifted along `p`, is a covering family of `x` for the inherited
*Zariski* topology all of whose members lie over affine schemes, hence also one for the inherited
étale topology. `AlgebraicGeometry.FibredSite.exists_affine_ofArrows` is the fppf statement.

## Main results

* `AlgebraicGeometry.FibredSite.exists_affine_ofArrows_zariski` and
  `AlgebraicGeometry.FibredSite.exists_affine_ofArrows_etale`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- The affine open cover of a scheme, with its index type lifted to `Type (u + 1)`. -/
private noncomputable def affineOpenCoverULift (T : Scheme.{u}) : T.OpenCover.{u + 1} where
  I₀ := ULift.{u + 1} T.affineOpenCover.openCover.I₀
  X i := T.affineOpenCover.openCover.X i.down
  f i := T.affineOpenCover.openCover.f i.down
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ T.affineOpenCover.openCover.map_prop _⟩
    obtain ⟨y, hy⟩ := T.affineOpenCover.openCover.covers x
    exact ⟨⟨T.affineOpenCover.openCover.idx x⟩, y, hy⟩

/-- **Every object of the associated Zariski site carries a covering family by objects lying over
affine schemes**: an affine open cover of the scheme below the object, lifted along `p`. -/
theorem exists_affine_ofArrows_zariski (hp : p.IsFiberedInGroupoids) (W : 𝒳) :
    ∃ (I : Type (u + 1)) (y : I → 𝒳) (φ : ∀ j, y j ⟶ W),
      (∀ j, IsAffineOver B S hS (p.obj (y j))) ∧
        Sieve.ofArrows y φ ∈ BigFppfOver.associatedTopology B S hS p .zariski W := by
  classical
  let O := affineOpenCoverULift (B.inclusion.obj (p.obj W).left)
  let V : PreZeroHypercover.{u + 1} (p.obj W).left :=
    { I₀ := O.I₀
      X := fun i => ⟨O.X i, Scheme.size_lt_of_isOpenImmersion (O.f i) (p.obj W).left.2⟩
      f := fun i => ObjectProperty.homMk (O.f i) }
  have hVaff : ∀ j, IsAffine (B.inclusion.obj (V.X j)) := fun j => by
    show IsAffine (Spec ((B.inclusion.obj (p.obj W).left).affineOpenCover.X j.down))
    exact isAffine_Spec _
  let Vobj (j : V.I₀) : BigFppfOver B S hS := Over.mk (V.f j ≫ (p.obj W).hom)
  let vmap (j : V.I₀) : Vobj j ⟶ p.obj W := Over.homMk (V.f j)
  have hBcover : Sieve.ofArrows Vobj vmap ∈
      BigFppfOver.baseOverTopology B S hS .zariski (p.obj W) := by
    have hZ : IsZariskiCovering (⟨(p.obj W).left, V⟩ : Covering B.Schemes) := by
      show (V.map B.inclusion).presieve₀ ∈ Scheme.zariskiPrecoverage _
      simpa [V, PreZeroHypercover.map] using O.mem₀
    obtain ⟨⟨T', E'⟩, hE', hbase, hfamily⟩ :=
      B.zariskiCovering_has_representative ⟨(p.obj W).left, V⟩ hZ
    change (p.obj W).left = T' at hbase
    cases hbase
    have hgen : Sieve.generate V.presieve₀ ∈ B.zariskiTopology (p.obj W).left := by
      rw [PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent
        (show PreZeroHypercover.CombinatoriallyEquivalent V E' by simpa using hfamily)]
      exact Precoverage.generate_mem_toGrothendieck ⟨E', rfl, hE'⟩
    let Vover : PreZeroHypercover.{u + 1} (p.obj W) := ⟨V.I₀, Vobj, vmap⟩
    show Sieve.generate Vover.presieve₀ ∈ B.zariskiTopology.over (B.obj hS) (p.obj W)
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate,
      ← Sieve.arrows_generate_map_eq_functorPushforward]
    simpa [Vover, Vobj, vmap, PreZeroHypercover.presieve₀, PreZeroHypercover.map] using hgen
  choose y φ hφ using fun j => hp.exists_lift (vmap j) W rfl
  have hdom : ∀ j, p.obj (y j) = Vobj j := fun j =>
    have := hφ j; IsHomLift.domain_eq p (vmap j) (φ j)
  have hvmapmem : ∀ j, (Sieve.ofArrows (fun k => p.obj (y k)) fun k => p.map (φ k)) (vmap j) := by
    intro j
    refine (Sieve.mem_ofArrows_iff _ _ _).2 ⟨j, eqToHom (hdom j).symm, ?_⟩
    have := hφ j
    simpa using IsHomLift.fac p (vmap j) (φ j)
  have : p.IsFibered := hp.isFibered
  refine ⟨V.I₀, y, φ, fun j => ?_, ?_⟩
  · show IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj (y j)))
    rw [hdom j]
    exact hVaff j
  · refine (Functor.isInheritedTopology_inheritedTopology p
      (BigFppfOver.baseOverTopology B S hS .zariski) y φ
      fun j => hp.isStronglyCartesian (φ j)).2 ?_
    refine (BigFppfOver.baseOverTopology B S hS .zariski).superset_covering
      (fun Z g hg => ?_) hBcover
    obtain ⟨j, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
    exact Sieve.downward_closed _ (hvmapmem j) a

/-- **Every object of the associated étale site carries a covering family by objects lying over
affine schemes**, the Zariski family of
`AlgebraicGeometry.FibredSite.exists_affine_ofArrows_zariski` being an étale one. -/
theorem exists_affine_ofArrows_etale (hp : p.IsFiberedInGroupoids) (W : 𝒳) :
    ∃ (I : Type (u + 1)) (y : I → 𝒳) (φ : ∀ j, y j ⟶ W),
      (∀ j, IsAffineOver B S hS (p.obj (y j))) ∧
        Sieve.ofArrows y φ ∈ BigFppfOver.associatedTopology B S hS p .etale W := by
  obtain ⟨I, y, φ, hy, hcov⟩ := exists_affine_ofArrows_zariski B S hS p hp W
  refine ⟨I, y, φ, hy, ?_⟩
  have hle : BigFppfOver.associatedTopology B S hS p .zariski ≤
      BigFppfOver.associatedTopology B S hS p .etale := by
    apply Precoverage.toGrothendieck_mono
    intro X R hR
    exact ⟨hR.1, BigFppfOver.baseOverTopology_zariski_le_etale B S hS _ hR.2⟩
  exact hle _ hcov

end AlgebraicGeometry.FibredSite
