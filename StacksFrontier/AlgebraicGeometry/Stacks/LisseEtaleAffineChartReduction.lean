module

public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectStackMapJointlySurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.AssociatedSiteRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.LisseEtaleSmoothClosure
public import StacksFrontier.AlgebraicGeometry.Spaces.SchematicLocusRelative
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.ChosenEtaleSite
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeSmoothCoveringLocal
public import StacksFrontier.AlgebraicGeometry.Stacks.SubsiteGlobalCohomologyAtlas
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafFunctoriality

/-!
# Stacks 07B3 (1): the reduction to affine charts

Let `H` be a quasi-coherent module on the lisse-étale site of an algebraic stack `𝒳`. The proof of
Stacks 07B3 picks a smooth surjective `x : U → 𝒳`, an étale covering `{U_i → U}` over which `H`
has a global presentation (Stacks 03DL), refines it by affine schemes, and reduces the statement,
by Stacks 07AQ (1), to the 1-morphisms `f_i : U_i → 𝒳`. This file carries out that reduction: a
sheaf of modules `F` on `𝒳_étale` lies in `LQCoh^fbc(𝒪_𝒳)` as soon as its pullbacks along all
1-morphisms `y : (Sch/U) → 𝒳`, for `y` a smooth object over an affine `U` with an arrow to an
object over which `H` has a global presentation, do.

## Main results

* `AlgebraicGeometry.Stack.exists_mem_range_of_mem_associatedTopology_etale`: a covering sieve of
  the étale site of a category fibred in groupoids covers the points of the underlying scheme.
* `AlgebraicGeometry.Stack.exists_affine_hom_mem_range`: around every point of the scheme under an
  object there is an arrow from an object over an affine open.
* `LisseEtale.isLocallyQuasicoherentWithSheafFlatBaseChange_of_affine_presented`: the reduction.

## References

* [Stacks Project, Tag 07B3](https://stacks.math.columbia.edu/tag/07B3)
* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v v' w w'

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A covering sieve of the étale site of a category fibred in groupoids covers the points of
the underlying scheme.** Every point of the scheme under `x` is in the image of the scheme under
the source of some arrow of the sieve. -/
theorem exists_mem_range_of_mem_associatedTopology_etale {X : Type v} [Category.{v'} X]
    (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {x : X} {T : Sieve x}
    (hT : T ∈ associatedTopology B S hS p (etaleTopology B) x)
    (t : (BigFppfOver.toScheme B S hS).obj (p.obj x)) :
    ∃ (z : X) (g : z ⟶ x), T g ∧
      t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p.map g)) := by
  obtain ⟨E, hE, hle⟩ := exists_chosenCovering_le_of_mem_associatedTopology B S hS p
    (etaleTopology B)
    (fun F => ∀ t : (BigFppfOver.toScheme B S hS).obj F.1, ∃ i,
      t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (F.2.f i)))
    (fun U R hR => by
      rw [GrothendieckTopology.mem_over_iff] at hR
      obtain ⟨E₀, hE₀, hE₀le⟩ := exists_etaleCovering_le_of_mem_etaleTopology B hR
      refine ⟨⟨E₀.I₀, fun i => Over.mk (E₀.f i ≫ U.hom), fun i => Over.homMk (E₀.f i)⟩,
        fun t => ?_, ?_⟩
      · have h₂ : Presieve.ofArrows (fun i => B.inclusion.obj (E₀.X i))
            (fun i => B.inclusion.map (E₀.f i)) ∈
              Scheme.precoverage @Etale (B.inclusion.obj U.left) := hE₀.2
        obtain ⟨i, hi⟩ := ((Scheme.ofArrows_mem_precoverage_iff _).1 h₂).1 t
        exact ⟨i, hi⟩
      · rintro _ _ ⟨i⟩
        exact (Sieve.overEquiv_iff R (E₀.f i)).1 (hE₀le _ _ (Presieve.ofArrows.mk i)))
    hp T hT
  obtain ⟨i, hi⟩ := hE t
  exact ⟨E.X i, E.f i, hle _ _ (Presieve.ofArrows.mk i), hi⟩

/-- **An object of a category fibred in groupoids has, around every point of its scheme, an arrow
from an object over an affine open.** For a point `s` of the scheme under `x`, an affine open
`W ∋ s` of it lifts, `p` being fibred in groupoids, to an arrow `y ⟶ x` lying over the open
immersion `W ⟶ p x`. -/
theorem exists_affine_hom_mem_range {X : Type v} [Category.{v'} X]
    (p : X ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (x : X)
    (s : (BigFppfOver.toScheme B S hS).obj (p.obj x)) :
    ∃ (y : X) (g : y ⟶ x), IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj y)) ∧
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map (p.map g)) ∧
      s ∈ Set.range ((BigFppfOver.toScheme B S hS).map (p.map g)) := by
  have hs : s ∈ (⊤ : ((BigFppfOver.toScheme B S hS).obj (p.obj x)).Opens) := trivial
  rw [← iSup_affineOpens_eq_top] at hs
  obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.1 hs
  obtain ⟨Va, u, hu, hrange, hVaff⟩ := BigFppfOver.exists_affineOpen_restrict B S hS (p.obj x) W
  obtain ⟨y, φ, hφ⟩ := hp.exists_lift u x rfl
  have hy : p.obj y = Va := IsHomLift.domain_eq p u φ
  subst hy
  have hφu : p.map φ = u := by simpa using IsHomLift.fac' p u φ
  refine ⟨y, φ, hVaff, ?_, ?_⟩
  · rw [hφu]
    exact hu
  · rw [hφu, hrange]
    exact hW

section Transport

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)

/-- **The class `LQCoh^fbc` of an inverse image does not depend on which of two equal structure
functors carries it.** For `f` with `f ⋙ q = p`, the inverse image of Stacks 06WE of sheaves of
modules (whose structure functor is `p`) lies in `LQCoh^fbc` exactly when the inverse image of
presheaves of modules of Stacks 06WD (whose structure functor is `f ⋙ q`), the form in which
Stacks 07AQ is stated, does. -/
theorem isLocallyQuasicoherentWithSheafFlatBaseChange_modulePullback_iff
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) (hfq : (f ⋙ q).IsFiberedInGroupoids)
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS q hq (etaleTopology B)
      (etaleTopology_le_topology B))) :
    IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, u} B E h S hS p hp
      ((modulePullback.{u, v, w, u, v', w'} B S hS p q hp hq f hf (etaleTopology B)
        (etaleTopology_le_topology B)).obj M).val ↔
    IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, u} B E h S hS (f ⋙ q) hfq
      ((modulePresheafPullback.{u, v, w, v', w', u} B S hS q hq f hfq).obj M.val) := by
  subst hf
  rfl

end Transport

namespace LisseEtale

variable (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff) (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **Stacks 07B3, the reduction to affine charts, for the lisse-étale site.** Let `H` be a
quasi-coherent module on the lisse-étale site of `𝒳` and `F` a sheaf of modules on `𝒳_étale`. If
the pullback of `F` along `y : (Sch/U) → 𝒳` lies in `LQCoh^fbc` for every smooth object `y` over
an affine scheme `U` admitting an arrow to an object over which `H` has a global presentation,
then `F` lies in `LQCoh^fbc(𝒪_𝒳)`. These `y` are jointly surjective: a smooth atlas object `x₀`
is covered, in the lisse-étale site, by objects over which `H` is globally presented
(Stacks 03DL (6)), and their underlying schemes by affine opens; Stacks 07AQ (1) concludes. -/
theorem isLocallyQuasicoherentWithSheafFlatBaseChange_of_affine_presented
    {R : Sheaf (inclusionTopology.{u, w} B S hS 𝒳) RingCat.{u}} (H : SheafOfModules.{u} R)
    (hH : H.IsQuasicoherentOnSite)
    (F : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B)))
    (hF : ∀ (y V : LisseEtale.{u, w} B S hS 𝒳) (_ : y ⟶ V),
      IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj y.obj)) →
      (H.over V).HasGlobalPresentation →
      IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, _, _, u} B E h S hS
        (CatFiberedInGroupoids.homFunctor (objectStackMap B S hS 𝒳 y.obj).hom ⋙ 𝒳.val.val.p)
        (isFiberedInGroupoids_homFunctor_comp B S hS (objectStackMap B S hS 𝒳 y.obj).hom)
        ((stackModulePresheafPullback.{u, w, u} B S hS (objectStackMap B S hS 𝒳 y.obj)).obj
          F.val)) :
    IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, _, _, u} B E h S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids F.val := by
  let J := {t : (y : LisseEtale.{u, w} B S hS 𝒳) × (V : LisseEtale.{u, w} B S hS 𝒳) × (y ⟶ V) //
    IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj t.1.obj)) ∧
      (H.over t.2.1).HasGlobalPresentation}
  refine isLocallyQuasicoherentWithSheafFlatBaseChange_of_isSmooth_jointlySurjective B E h S hS
    (fun j : J => objectStackMap B S hS 𝒳 j.1.1.obj) (fun j => j.1.1.property) ?_ F.val F.isSheaf
    (fun j => hF j.1.1 j.1.2.1 j.1.2.2 j.2.1 j.2.2)
  -- the atlas and the covering of it over which `H` is globally presented
  obtain ⟨x₀, hsm, hsurj⟩ := exists_smooth_surjective_objectMorphism _ _ _ 𝒳
  let X₀ : LisseEtale.{u, w} B S hS 𝒳 := ⟨x₀, hsm⟩
  obtain ⟨I, V, fV, hcov, hpres⟩ := hH.locally_hasGlobalPresentation X₀
  have := isContinuous_inclusion'.{u, w} B S hS 𝒳
  have hcov' := (CoverPreserving.of_isContinuous (smoothObject.{u, w} B S hS 𝒳).ι
    (inclusionTopology.{u, w} B S hS 𝒳)
    (associatedTopology B S hS 𝒳.val.val.p (etaleTopology B))).cover_preserve hcov
  -- the affine refinement, indexed by the members of the covering
  let J₀ := (i : I) × {yg : (y : LisseEtale.{u, w} B S hS 𝒳) × (y ⟶ V i) //
    IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒳.val.val.p.obj yg.1.obj))}
  have h₀ := AlgebraicStacks.iUnion_range_pointsMap_objectStackMap B S hS 𝒳 x₀ hsurj
    (fun j : J₀ => j.2.1.1.obj) (fun j => j.2.1.2.hom ≫ (fV j.1).hom) (fun t => by
      obtain ⟨z, g, hg, s, hs⟩ := exists_mem_range_of_mem_associatedTopology_etale B S hS
        𝒳.val.val.p 𝒳.val.isFiberedInGroupoids hcov' t
      obtain ⟨Z, k, l, hk, rfl⟩ := hg
      obtain ⟨i, m, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hk
      let s' := (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (l ≫ m.hom)) s
      obtain ⟨y', g', haff, hopen, s'', hs''⟩ := exists_affine_hom_mem_range B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids (V i).obj s'
      have hy' : smoothObject.{u, w} B S hS 𝒳 y' :=
        smoothObject_of_smooth.{u, w} B S hS 𝒳 g' (by
          have : _root_.AlgebraicGeometry.IsOpenImmersion
              (B.inclusion.map (𝒳.val.val.p.map g').left) := hopen
          infer_instance) (V i).property
      refine ⟨⟨i, ⟨⟨y', hy'⟩, ObjectProperty.homMk g'⟩, haff⟩, s'', ?_⟩
      show (BigFppfOver.toScheme B S hS).map (𝒳.val.val.p.map (g' ≫ (fV i).hom)) s'' = t
      rw [Functor.map_comp, Functor.map_comp, Scheme.Hom.comp_apply, hs'', ← hs]
      simp only [s', Functor.map_comp, Scheme.Hom.comp_apply]
      rfl)
  refine (Set.eq_univ_of_univ_subset ?_).symm
  rw [h₀]
  exact Set.iUnion_subset fun j₀ => Set.subset_iUnion_of_subset
    (⟨⟨j₀.2.1.1, V j₀.1, j₀.2.1.2⟩, j₀.2.2, hpres j₀.1⟩ : J) subset_rfl

end LisseEtale

end AlgebraicGeometry.Stack
