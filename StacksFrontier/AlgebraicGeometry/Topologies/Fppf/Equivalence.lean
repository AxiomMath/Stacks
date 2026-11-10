module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.BigFppfSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismDefs
public import StacksCore.Tactic.StacksAttribute

/-!
# Affine objects in a big fppf site

Let `B` be a big fppf site containing a scheme `S`.  The inclusion of the big affine fppf
category over `S` into the big fppf category over `S` is cocontinuous and is a dense
subsite, so it induces an equivalence of the associated sheaf topoi: an fppf sheaf is
determined by its restriction to affine schemes.

## Main results

* `AlgebraicGeometry.exists_standardFppf_refinement`: every covering sieve of an affine
  object is refined by a chosen covering family which is a standard fppf covering.
* `AlgebraicGeometry.bigAffineFppfInclusion_isCocontinuous`: the inclusion is cocontinuous.
* `AlgebraicGeometry.bigAffineFppfInclusion_isDenseSubsite`: the inclusion is a dense
  subsite, which supplies the equivalence of topoi.

## Implementation notes

Density is expressed by Mathlib's `CategoryTheory.Functor.IsDenseSubsite`, which together
with cocontinuity yields the canonical equivalence of sheaf topoi with inverse and direct
images `gInv` and `gStar`.

## References

* [Stacks Project, Tag 021V](https://stacks.math.columbia.edu/tag/021V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Cardinal

universe u

namespace AlgebraicGeometry

/-- Every covering sieve of an affine object of a big fppf site is refined by a chosen covering
family which is a standard fppf covering, that is, by a finite family of flat morphisms of finite
presentation, jointly surjective, whose sources are affine over the affine target. -/
@[stacks 021P "the finite affine refinement; the tag's further assertion that each member may be
chosen open affine inside one of the given members is not claimed"]
theorem exists_standardFppf_refinement
    (B : AlgebraicGeometry.BigFppfSite.{u})
    {T : B.Schemes} [IsAffine (B.inclusion.obj T)] {R : Sieve T}
    (hR : R ∈ B.topology T) :
    ∃ Q : PreZeroHypercover T,
      B.IsCovering ⟨T, Q⟩ ∧
      AlgebraicGeometry.IsStandardFppfCovering
        (fun i ↦ B.inclusion.obj (Q.X i)) (fun i ↦ B.inclusion.map (Q.f i)) ∧
      Q.presieve₀ ≤ R := by
  classical
  obtain ⟨E, hE, hER⟩ := AlgebraicGeometry.Space.exists_covering_refining_sieve B hR
  have hEfp : AlgebraicGeometry.IsFppfCovering ⟨T, E⟩ :=
    B.isFppfCovering_of_isCovering hE
  let T₀ : Scheme := T.obj
  have hEfp' : (E.map B.inclusion).presieve₀ ∈ Scheme.fppfPrecoverage T₀ := by
    simpa [AlgebraicGeometry.IsFppfCovering, Scheme.fppfPrecoverage,
      PreZeroHypercover.presieve₀_map, T₀] using hEfp
  let U : T₀.Cover Scheme.fppfPrecoverage :=
    ⟨E.map B.inclusion, hEfp'⟩
  have hUfp := (Scheme.presieve₀_mem_precoverage_iff U.toPreZeroHypercover).mp U.mem₀
  have : Scheme.JointlySurjective Scheme.fppfPrecoverage := by
    change Scheme.JointlySurjective
      (Scheme.precoverage (@Flat ⊓ @LocallyOfFinitePresentation))
    infer_instance
  have : MorphismProperty.IsStableUnderComposition
      (@Flat ⊓ @LocallyOfFinitePresentation) :=
    ⟨fun f g hf hg => ⟨MorphismProperty.comp_mem (@Flat) f g hf.1 hg.1,
      MorphismProperty.comp_mem (@LocallyOfFinitePresentation) f g hf.2 hg.2⟩⟩
  have : MorphismProperty.RespectsLeft
      (@Flat ⊓ @LocallyOfFinitePresentation) @IsOpenImmersion := by
    constructor
    intro X Y Z i hi f hf
    exact MorphismProperty.comp_mem (@Flat ⊓ @LocallyOfFinitePresentation) i f
      (by constructor <;> infer_instance) hf
  have : QuasiCompactCover U.toPreZeroHypercover := by
    refine QuasiCompactCover.of_isOpenMap fun i => ?_
    obtain ⟨_, _⟩ := hUfp.2 i
    exact (U.f i).isOpenMap
  have : IsAffine T₀ := by
    change IsAffine (B.inclusion.obj T)
    infer_instance
  have : CompactSpace T₀ := (TopCat.homeoOfIso (asIso T₀.isoSpec.inv.base)).compactSpace
  obtain ⟨V, φ, hVfinite, hφopen⟩ := QuasiCompactCover.exists_hom U
  let P := V.cover.toPreZeroHypercover
  have : Finite P.I₀ := hVfinite
  have hPaff (i : P.I₀) : IsAffine (P.X i) := isAffine_Spec (V.X i)
  have hPstandard : AlgebraicGeometry.IsStandardFppfCovering P.X P.f := by
    refine ⟨hVfinite, inferInstance, hPaff, ?_, ?_, ?_⟩
    · exact fun i => (V.map_prop i).1
    · intro i
      have := hPaff i
      exact ⟨(V.map_prop i).2, inferInstance, inferInstance⟩
    · refine Set.eq_univ_iff_forall.mpr fun x => ?_
      obtain ⟨i, y, hy⟩ :=
        ((Scheme.presieve₀_mem_precoverage_iff P).mp V.cover.mem₀).1 x
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨y, hy⟩⟩
  obtain ⟨W, hW, hWP⟩ :=
    exists_isCovering_tautologicallyEquivalent_standardFppfCovering
      B T P V.cover.mem₀ hPstandard
  rcases hWP with ⟨⟨α, hα⟩, ⟨β, hβ⟩⟩
  let α' : P.I₀ → W.I₀ := fun i ↦ α i
  let β' : W.I₀ → P.I₀ := fun i ↦ β i
  have hα' (i : P.I₀) :
      ∃ e : P.X i ≅ B.inclusion.obj (W.X (α' i)),
        e.hom ≫ B.inclusion.map (W.f (α' i)) = P.f i := by
    simpa [α', PreZeroHypercover.map] using hα i
  have hβ' (i : W.I₀) :
      ∃ e : B.inclusion.obj (W.X i) ≅ P.X (β' i),
        e.hom ≫ P.f (β' i) = B.inclusion.map (W.f i) := by
    simpa [β', PreZeroHypercover.map] using hβ i
  let I := Set.range α'
  have : Finite I := Finite.of_surjective (fun i : P.I₀ ↦
      (⟨α' i, ⟨i, rfl⟩⟩ : I)) fun i => ⟨i.2.choose, Subtype.ext i.2.choose_spec⟩
  let Q : PreZeroHypercover T :=
    { I₀ := I
      X := fun i ↦ W.X i.1
      f := fun i ↦ W.f i.1 }
  have hQaff : ∀ i, IsAffine (B.inclusion.obj (Q.X i)) := by
    intro i
    obtain ⟨e, _⟩ := hβ' i.1
    have := hPaff (β' i.1)
    exact IsAffine.of_isIso e.hom
  have hWprops := (Scheme.presieve₀_mem_precoverage_iff
      (W.map B.inclusion)).mp (by
        simpa [AlgebraicGeometry.IsFppfCovering, Scheme.fppfPrecoverage,
          PreZeroHypercover.presieve₀_map] using B.isFppfCovering_of_isCovering hW)
  have hQstandard : AlgebraicGeometry.IsStandardFppfCovering
      (fun i ↦ B.inclusion.obj (Q.X i)) (fun i ↦ B.inclusion.map (Q.f i)) := by
    refine AlgebraicGeometry.IsStandardFppfCovering.mk inferInstance inferInstance
      hQaff ?_ ?_ ?_
    · exact fun i => (hWprops.2 i.1).1
    · intro i
      have := hQaff i
      exact ⟨(hWprops.2 i.1).2, inferInstance, inferInstance⟩
    · refine Set.eq_univ_iff_forall.mpr fun x => ?_
      obtain ⟨i, y, hy⟩ :=
        ((Scheme.presieve₀_mem_precoverage_iff P).mp V.cover.mem₀).1 x
      obtain ⟨e, he⟩ := hα' i
      let j : I := ⟨α' i, ⟨i, rfl⟩⟩
      refine Set.mem_iUnion.mpr ⟨j, Set.mem_range.mpr ⟨e.hom y, ?_⟩⟩
      change (B.inclusion.map (W.f j.1)) (e.hom y) = x
      rwa [← Scheme.Hom.comp_apply, he]
  have hQfp : AlgebraicGeometry.IsFppfCovering ⟨T, Q⟩ := by
    simpa [AlgebraicGeometry.IsFppfCovering, Scheme.fppfPrecoverage,
      PreZeroHypercover.presieve₀_map] using
      (Scheme.presieve₀_mem_precoverage_iff (Q.map B.inclusion)).2
        ⟨by
          intro x
          have hx : x ∈ ⋃ i, Set.range (B.inclusion.map (Q.f i)) := by
            rw [hQstandard.jointly_surjective]
            trivial
          exact Set.mem_iUnion.mp hx,
          fun i ↦ ⟨hQstandard.flat i, (hQstandard.finite_presentation i).1⟩⟩
  have hQcard : Cardinal.mk Q.I₀ ≤ B.coveringBound :=
    (Cardinal.mk_le_of_injective (f := fun i : Q.I₀ => (i.1 : W.I₀))
      Subtype.val_injective).trans hW.2
  have hQcover : B.IsCovering ⟨T, Q⟩ := ⟨hQfp, hQcard⟩
  have hQle : Q.presieve₀ ≤ R := by
    rw [Presieve.ofArrows_le_iff]
    intro i
    obtain ⟨e, he⟩ := hβ' i.1
    let k := β' i.1
    let gB : Q.X i ⟶ E.X (φ.s₀ k) :=
      B.inclusion.preimage (e.hom ≫ φ.h₀ k)
    have hmapg : B.inclusion.map gB = e.hom ≫ φ.h₀ k := B.inclusion.map_preimage _
    have hφ' : φ.h₀ k ≫ B.inclusion.map (E.f (φ.s₀ k)) = P.f k := φ.w₀ k
    have hEq : gB ≫ E.f (φ.s₀ k) = Q.f i := B.inclusion.map_injective (by
      rw [Functor.map_comp, hmapg]
      exact (Category.assoc _ _ _).trans ((congrArg (e.hom ≫ ·) hφ').trans he))
    rw [← hEq]
    exact R.downward_closed (hER _ _ ⟨φ.s₀ k⟩) gB
  exact ⟨Q, hQcover, hQstandard, hQle⟩

/-- The pullback of a pushed-forward sieve along the image of a morphism contains the
pushforward of the pullback, for a functor preserving fibre products. -/
private alias pullback_functorPushforward_le := ProEtale.pullback_functorPushforward_le

/-- A functor preserving fibre products is cover preserving for a topology generated by a
precoverage as soon as it preserves the generating families. -/
private alias coverPreserving_of_generators := ProEtale.coverPreserving_of_generators

/-- The inclusion of the affine slice is cover dense, since every object of the big fppf
category over `S` is covered by affine ones. -/
private theorem bigAffineFppfInclusion_isCoverDense
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).IsCoverDense
      (AlgebraicGeometry.BigFppfOver.topology B S hS) := by
  classical
  constructor
  intro X
  let T : B.Schemes := X.left
  let O := B.inclusion.obj T
  let U := O.affineOpenCover.openCover
  obtain ⟨W, hW, hWU⟩ :=
    exists_isCovering_tautologicallyEquivalent_openCover B T U
  rcases hWU with ⟨⟨α, hα⟩, ⟨β, hβ⟩⟩
  have hWaff : ∀ j, IsAffine (B.inclusion.obj (W.X j)) := by
    intro j
    obtain ⟨e, _⟩ := hβ j
    have : IsAffine (U.X (β j)) := isAffine_Spec (O.affineOpenCover.X (β j))
    exact @IsAffine.of_isIso _ _ e.hom e.isIso_hom inferInstance
  let Vobj (j : W.I₀) : AlgebraicGeometry.BigAffineFppf B S hS :=
    { obj := Over.mk (W.f j ≫ X.hom)
      property := hWaff j }
  let vmap (j : W.I₀) :
      (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj (Vobj j) ⟶ X :=
    Over.homMk (W.f j)
  have hBcover : Sieve.ofArrows
      (fun j => (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).obj (Vobj j))
        vmap ∈
      AlgebraicGeometry.BigFppfOver.topology B S hS X := by
    rw [AlgebraicGeometry.BigFppfOver.topology, GrothendieckTopology.mem_over_iff,
      Sieve.overEquiv_ofArrows]
    change Sieve.ofArrows W.X W.f ∈ B.topology T
    simpa [PreZeroHypercover.presieve₀] using
      Precoverage.generate_mem_toGrothendieck (⟨W, rfl, hW⟩ : W.presieve₀ ∈ B.precoverage T)
  refine (AlgebraicGeometry.BigFppfOver.topology B S hS).superset_covering ?_ hBcover
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  exact fun j => Presieve.in_coverByImage
    (AlgebraicGeometry.BigAffineFppf.inclusion B S hS) (vmap j)

/-- The inclusion of affine objects over `S` in a chosen big fppf site is cocontinuous. -/
@[stacks 021V "cocontinuity"]
public instance bigAffineFppfInclusion_isCocontinuous
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).IsCocontinuous
      (AlgebraicGeometry.BigAffineFppf.topology B S hS)
      (AlgebraicGeometry.BigFppfOver.topology B S hS) where
  cover_lift := by
    intro X R hR
    let u := AlgebraicGeometry.BigAffineFppf.inclusion B S hS
    let J := AlgebraicGeometry.BigAffineFppf.topology B S hS
    let K := AlgebraicGeometry.BigFppfOver.topology B S hS
    let T : B.Schemes :=
      (AlgebraicGeometry.BigFppfOver.forget B S hS).obj (u.obj X)
    have hRbase : (Sieve.overEquiv (u.obj X)) R ∈ B.topology T := by
      change R ∈ (B.topology.over (B.obj hS)) (u.obj X) at hR
      rwa [GrothendieckTopology.mem_over_iff] at hR
    have : IsAffine (B.inclusion.obj T) := by
      change IsAffine
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj (u.obj X))
      exact AlgebraicGeometry.BigAffineFppf.isAffine_toScheme_obj B S hS X
    obtain ⟨Q, hQcover, hQstandard, hQle⟩ :=
      exists_standardFppf_refinement B (T := T) (R := Sieve.overEquiv (u.obj X) R)
        hRbase
    let Vobj (i : Q.I₀) : AlgebraicGeometry.BigAffineFppf B S hS :=
      ⟨Over.mk (Q.f i ≫ (u.obj X).hom), hQstandard.affine_source i⟩
    let vf (i : Q.I₀) : Vobj i ⟶ X :=
      ObjectProperty.homMk
        (Over.homMk (X := B.obj hS) (U := (Vobj i).obj) (V := X.obj)
          (Q.f i) (by change Q.f i ≫ X.obj.hom = Q.f i ≫ X.obj.hom; rfl))
    let V : PreZeroHypercover X := ⟨Q.I₀, Vobj, vf⟩
    have hVcover :
        AlgebraicGeometry.BigAffineFppf.IsCovering B S hS ⟨X, V⟩ := by
      change AlgebraicGeometry.BigFppfOver.IsCovering B S hS _ ∧
        AlgebraicGeometry.BigAffineFppf.IsStandardFppfCovering B S hS _
      constructor
      · change B.IsCovering _
        have hmap : (V.map u).map
            (AlgebraicGeometry.BigFppfOver.forget B S hS) = Q := by
          ext <;> rfl
        change B.IsCovering
          ⟨T, (V.map u).map (AlgebraicGeometry.BigFppfOver.forget B S hS)⟩
        rwa [hmap]
      · change AlgebraicGeometry.IsStandardFppfCovering
          (fun i ↦ B.inclusion.obj (Q.X i)) (fun i ↦ B.inclusion.map (Q.f i))
        exact hQstandard
    have hVmem : Sieve.generate V.presieve₀ ∈ J X :=
      Precoverage.generate_mem_toGrothendieck ⟨V, rfl, hVcover⟩
    have hVle : V.presieve₀ ≤ R.functorPullback u := by
      rw [Presieve.ofArrows_le_iff]
      intro i
      change R (u.map (V.f i))
      have hmemBase : ((Sieve.overEquiv (u.obj X)) R) (Q.f i) := hQle _ _ ⟨i⟩
      change R (Over.homMk (X := B.obj hS)
        (U := (Over.mk (Q.f i ≫ X.obj.hom))) (V := X.obj) (Q.f i) (by rfl))
      exact (Sieve.overEquiv_iff R (Q.f i)).mp hmemBase
    refine J.superset_covering ?_ hVmem
    rwa [Sieve.generate_le_iff]

/-- The inclusion of affine objects over `S` in a chosen big fppf site is a dense subsite, so the
induced morphism of sheaf topoi is an equivalence. -/
@[stacks 021V "equivalence of topoi"]
public instance bigAffineFppfInclusion_isDenseSubsite
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (AlgebraicGeometry.BigAffineFppf.inclusion B S hS).IsDenseSubsite
      (AlgebraicGeometry.BigAffineFppf.topology B S hS)
      (AlgebraicGeometry.BigFppfOver.topology B S hS) := by
  let u := AlgebraicGeometry.BigAffineFppf.inclusion B S hS
  let J := AlgebraicGeometry.BigAffineFppf.topology B S hS
  let K := AlgebraicGeometry.BigFppfOver.topology B S hS
  have hcover : CoverPreserving J K u := by
    have : HasPullbacks (AlgebraicGeometry.BigAffineFppf B S hS) :=
      hasPullbacks_bigAffineFppf B S hS
    have : HasPullbacks (AlgebraicGeometry.BigFppfOver B S hS) := inferInstance
    have : HasLimitsOfShape WalkingCospan
      (AlgebraicGeometry.BigFppfOver B S hS) := inferInstance
    have : IsConnected WalkingCospan := inferInstance
    have : PreservesLimitsOfShape WalkingCospan
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS) := by infer_instance
    let P := AlgebraicGeometry.IsAffineOver B S hS
    have : P.IsClosedUnderIsomorphisms := ⟨fun e h => by
      change IsAffine
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj _) at h ⊢
      exact IsAffine.of_isIso
        ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map e.inv)⟩
    have : P.IsClosedUnderLimitsOfShape WalkingCospan := by
      apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
      rintro X ⟨F, hF⟩
      let G := F ⋙ AlgebraicGeometry.BigFppfOver.toScheme B S hS
      have : IsAffine (G.obj WalkingCospan.left) := hF WalkingCospan.left
      have : IsAffine (G.obj WalkingCospan.right) := hF WalkingCospan.right
      have : IsAffine (G.obj WalkingCospan.one) := hF WalkingCospan.one
      have hlim : IsAffine (limit G) := by
        have : IsAffine (pullback (G.map WalkingCospan.Hom.inl)
            (G.map WalkingCospan.Hom.inr)) := inferInstance
        exact IsAffine.of_isIso (HasLimit.isoOfNatIso
          (diagramIsoCospan G)).hom
      exact IsAffine.of_isIso (preservesLimitIso
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS) F).hom
    have : PreservesLimitsOfShape WalkingCospan u := by infer_instance
    apply coverPreserving_of_generators u
      (AlgebraicGeometry.BigAffineFppf.precoverage B S hS) K
    intro X R hR
    obtain ⟨E, rfl, hE⟩ := hR
    rw [← Sieve.generate_map_eq_functorPushforward]
    dsimp [K]
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
    have hbase : Presieve.map (AlgebraicGeometry.BigFppfOver.forget B S hS)
        ((E.map u).presieve₀) ∈ B.precoverage ((u.obj X).left) :=
      ⟨(E.map u).map (AlgebraicGeometry.BigFppfOver.forget B S hS),
        by simp [PreZeroHypercover.presieve₀_map], hE.1⟩
    refine B.topology.superset_covering ?_ (Precoverage.generate_mem_toGrothendieck hbase)
    rw [Sieve.generate_le_iff, PreZeroHypercover.presieve₀_map]
    exact le_trans
      (Presieve.map_le_functorPushforward
        (F := AlgebraicGeometry.BigFppfOver.forget B S hS)
        (Presieve.map u E.presieve₀))
      (Sieve.le_generate _)
  have hfaithful : ∀ ⦃U' U : AlgebraicGeometry.BigAffineFppf B S hS⦄
      (a b : U' ⟶ U), u.map a = u.map b → Sieve.equalizer a b ∈ J U' := by
    intro U' U a b hab
    obtain rfl := u.map_injective hab
    simp
  have hfull : ∀ ⦃U' U : AlgebraicGeometry.BigAffineFppf B S hS⦄
      (c : u.obj U' ⟶ u.obj U), u.imageSieve c ∈ J U' := by
    intro U' U c
    rw [← u.map_preimage c, Functor.imageSieve_map]
    exact J.top_mem U'
  have : u.IsCocontinuous J K := bigAffineFppfInclusion_isCocontinuous B S hS
  have : u.IsCoverDense K := bigAffineFppfInclusion_isCoverDense B S hS
  exact Functor.isDenseSubsite_of_isCocontinuous u J K hcover hfaithful hfull

end AlgebraicGeometry
