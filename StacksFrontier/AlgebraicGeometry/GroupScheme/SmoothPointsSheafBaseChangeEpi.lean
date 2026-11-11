module

public import StacksFrontier.CategoryTheory.Sites.OverPullbackPushforward
public import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianSchemeFirstCohomologyGenericPoint
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteGluing

/-!
# Sections of a smooth group scheme lift along a first-order thickening of the base

Let `B` be a big fppf site, `S` a scheme of `B`, `z : Z ⟶ S` a morphism of `B` and `G` a smooth
commutative group scheme over `S` contained in `B`, with abelian sheaf of points `𝒜` on the big
fppf site of `S`. Restriction along the first projections `T ×_S Z ⟶ T` is a morphism
`𝒜 ⟶ 𝒜'` to the sheaf `𝒜' : T ↦ 𝒜(T ×_S Z)` of sections over the base change
(`CategoryTheory.Sheaf.toBaseChangePushforward`). If `U ×_S Z ⟶ U` is a first-order thickening,
this morphism becomes an epimorphism once restricted to the slice over `U`.

## Main results

* `AlgebraicGeometry.isFirstOrderThickening_baseChangeFst_of_hom`: if `U ×_S Z ⟶ U` is a
  first-order thickening, so is `T ×_S Z ⟶ T` for every `T` with a morphism `T ⟶ U`.
* `AlgebraicGeometry.exists_baseChangeFst_comp_eq_of_smooth`: when `T` is affine and
  `T ×_S Z ⟶ T` is a first-order thickening, every `S`-morphism `T ×_S Z ⟶ G` extends to `T`.
* `AlgebraicGeometry.exists_mem_topology_toBaseChangePushforward_pointsSheaf_eq`: sections of
  `𝒜'` over any `T ⟶ U` lift to `𝒜` locally on `T`, in the big fppf topology.
* `AlgebraicGeometry.epi_overPullback_toBaseChangePushforward_pointsSheaf`: the restriction of
  `𝒜 ⟶ 𝒜'` to the slice over `U` is an epimorphism of abelian sheaves.

## Implementation notes

The extension over an affine `T` is formal smoothness of `G ⟶ S`
(`Stacks.Smooth.formallySmoothScheme_of_smooth`), applied to the affine first-order thickening
`T ×_S Z ⟶ T`; that `T ×_S Z ⟶ T` is a first-order thickening is the stability of first-order
thickenings under base change (`Stacks.Thickenings.isFirstOrderThickening_of_isPullback`), since
it is the base change of `U ×_S Z ⟶ U` along `T ⟶ U`. A general `T` is covered by its affine
opens, which generate a covering sieve of the big fppf topology, so the morphism is locally
surjective and therefore an epimorphism (`CategoryTheory.Sheaf.epi_of_isLocallySurjective`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
  {Z : Scheme.{u}} (hZ : B.Contains Z) (z : B.obj hZ ⟶ B.obj hS)

/-- If the first projection `U ×_S Z ⟶ U` is a first-order thickening, then so is the first
projection `T ×_S Z ⟶ T` for every `T` mapping to `U`: it is the base change of the former along
`T ⟶ U`. -/
theorem isFirstOrderThickening_baseChangeFst_of_hom {T U : BigFppfOver B S hS} (g : T ⟶ U)
    (hU : Stacks.Thickenings.IsFirstOrderThickening
      (B.inclusion.map (Sheaf.baseChangeFst z U).left)) :
    Stacks.Thickenings.IsFirstOrderThickening
      (B.inclusion.map (Sheaf.baseChangeFst z T).left) := by
  have hsq : IsPullback (pullback.fst T.hom z)
      (pullback.lift (pullback.fst T.hom z ≫ g.left) (pullback.snd T.hom z)
        (by rw [Category.assoc, Over.w g, pullback.condition]))
      g.left (pullback.fst U.hom z) := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm
      (IsPullback.of_hasPullback U.hom z)
    rw [pullback.lift_snd, Over.w g]
    exact IsPullback.of_hasPullback T.hom z
  exact Stacks.Thickenings.isFirstOrderThickening_of_isPullback
    (B.inclusion.map_isPullback hsq) hU

/-- **Infinitesimal lifting for a smooth scheme over `S`.** If `T` is affine and the first
projection `T ×_S Z ⟶ T` is a first-order thickening, every `S`-morphism `T ×_S Z ⟶ G` to a
smooth `S`-scheme `G` is the restriction of an `S`-morphism `T ⟶ G`. -/
theorem exists_baseChangeFst_comp_eq_of_smooth (G : Over S) [Smooth G.hom]
    (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
    (hT : Stacks.Thickenings.IsFirstOrderThickening
      (B.inclusion.map (Sheaf.baseChangeFst z T).left))
    (σ : (Over.post B.inclusion).obj ((Over.map z).obj ((Over.pullback z).obj T)) ⟶ G) :
    ∃ τ : (Over.post B.inclusion).obj T ⟶ G,
      (Over.post B.inclusion).map (Sheaf.baseChangeFst z T) ≫ τ = σ := by
  have := hT.1
  have hTa : IsAffine (B.inclusion.obj T.left) := ‹_›
  have : IsAffine (B.inclusion.obj (pullback T.hom z)) :=
    isAffine_of_isAffineHom (B.inclusion.map (Sheaf.baseChangeFst z T).left)
  obtain ⟨g', hg'1, hg'2⟩ := Stacks.Smooth.formallySmoothScheme_of_smooth G.hom ‹_› ‹_›
    (B.inclusion.map (Sheaf.baseChangeFst z T).left) hT σ.left (B.inclusion.map T.hom) (by
      refine (Over.w σ).trans ?_
      change B.inclusion.map (pullback.snd T.hom z ≫ z) = _
      rw [← pullback.condition, Functor.map_comp]
      rfl)
  exact ⟨Over.homMk g' hg'1, Over.OverMorphism.ext hg'2⟩

/-- The affine opens of an object of the big fppf site of `S` generate a covering sieve. -/
theorem ofArrows_opensObjectι_affineOpens_mem_topology (T : BigFppfOver B S hS) :
    Sieve.ofArrows
      (fun W : ((BigFppfOver.toScheme B S hS).obj T).affineOpens => Space.opensObject B S hS T W.1)
      (fun W => Space.opensObjectι B S hS T W.1) ∈ BigFppfOver.topology B S hS T := by
  refine BigFppfOver.sieve_ofArrows_mem_topology_of_jointlySurjective B S hS _ _ _
    (fun W => ?_) (fun y => ?_)
  · exact inferInstanceAs (IsOpenImmersion W.1.ι)
  · obtain ⟨W, hW, hyW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      ((BigFppfOver.toScheme B S hS).obj T).isBasis_affineOpens)
      (show y ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj T).Opens) from trivial)
    refine ⟨⟨W, hW⟩, ?_⟩
    rw [Space.toScheme_map_opensObjectι]
    exact ⟨⟨y, hyW⟩, rfl⟩

/-- Over an affine `T` whose first projection `T ×_S Z ⟶ T` is a first-order thickening, every
section of the sheaf of points of a smooth commutative group scheme over `T ×_S Z` is the
restriction of a section over `T`. -/
theorem exists_toBaseChangePushforward_pointsSheaf_eq (G : Over S) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] (hG : B.Contains G.left) {T : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hTz : Stacks.Thickenings.IsFirstOrderThickening
      (B.inclusion.map (Sheaf.baseChangeFst z T).left))
    (s : ((pointsSheaf B S hS G hG).baseChangePushforward z).obj.obj (op T)) :
    ∃ r : (pointsSheaf B S hS G hG).obj.obj (op T),
      ((pointsSheaf B S hS G hG).toBaseChangePushforward z).hom.app (op T) r = s := by
  obtain ⟨τ, hτ⟩ := exists_baseChangeFst_comp_eq_of_smooth B hS hZ z G T hTz
    (Additive.toMul s)
  exact ⟨Additive.ofMul τ, congrArg Additive.ofMul hτ⟩

/-- **Local surjectivity.** If `U ×_S Z ⟶ U` is a first-order thickening, every section over
`T ×_S Z` of the sheaf of points of a smooth commutative group scheme, for `T` mapping to `U`,
lifts to a section over `T` locally on `T` in the big fppf topology. -/
theorem exists_mem_topology_toBaseChangePushforward_pointsSheaf_eq (G : Over S) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] (hG : B.Contains G.left) (U : BigFppfOver B S hS)
    (hU : Stacks.Thickenings.IsFirstOrderThickening
      (B.inclusion.map (Sheaf.baseChangeFst z U).left))
    ⦃T : BigFppfOver B S hS⦄ (g : T ⟶ U)
    (s : ((pointsSheaf B S hS G hG).baseChangePushforward z).obj.obj (op T)) :
    ∃ R ∈ BigFppfOver.topology B S hS T, ∀ ⦃Y : BigFppfOver B S hS⦄ (h : Y ⟶ T), R h →
      ∃ r : (pointsSheaf B S hS G hG).obj.obj (op Y),
        ((pointsSheaf B S hS G hG).toBaseChangePushforward z).hom.app (op Y) r =
          ((pointsSheaf B S hS G hG).baseChangePushforward z).obj.map h.op s := by
  refine ⟨Presheaf.imageSieve ((pointsSheaf B S hS G hG).toBaseChangePushforward z).hom s,
    ?_, fun Y h hh => hh⟩
  refine GrothendieckTopology.superset_covering _ ?_
    (ofArrows_opensObjectι_affineOpens_mem_topology B hS T)
  rintro Y h ⟨Y', k, l, ⟨i⟩, rfl⟩
  exact Sieve.downward_closed _
    (exists_toBaseChangePushforward_pointsSheaf_eq B hS hZ z G hG
      (T := Space.opensObject B S hS T i.1) (i.2 : IsAffineOpen i.1)
      (isFirstOrderThickening_baseChangeFst_of_hom B hS hZ z
        (Space.opensObjectι B S hS T i.1 ≫ g) hU) _) k

/-- If `U ×_S Z ⟶ U` is a first-order thickening, the restriction map `G(T) ⟶ G(T ×_S Z)` of
the sheaf of points of a smooth commutative group scheme `G` over `S` is an epimorphism of
abelian sheaves on the slice of the big fppf site over `U`. -/
theorem epi_overPullback_toBaseChangePushforward_pointsSheaf (G : Over S) [GrpObj G]
    [IsCommMonObj G] [Smooth G.hom] (hG : B.Contains G.left) (U : BigFppfOver B S hS)
    (hU : Stacks.Thickenings.IsFirstOrderThickening
      (B.inclusion.map (Sheaf.baseChangeFst z U).left)) :
    Epi (((BigFppfOver.topology B S hS).overPullback AddCommGrpCat.{u} U).map
      ((pointsSheaf B S hS G hG).toBaseChangePushforward z)) := by
  have : Sheaf.IsLocallySurjective (((BigFppfOver.topology B S hS).overPullback
      AddCommGrpCat.{u} U).map ((pointsSheaf B S hS G hG).toBaseChangePushforward z)) := by
    constructor
    intro V s
    obtain ⟨R, hR, hRs⟩ := exists_mem_topology_toBaseChangePushforward_pointsSheaf_eq
      B hS hZ z G hG U hU V.hom s
    refine GrothendieckTopology.superset_covering _ ?_
      (GrothendieckTopology.overEquiv_symm_mem_over _ V R hR)
    intro W g hg
    exact hRs g.left hg
  infer_instance

end AlgebraicGeometry

