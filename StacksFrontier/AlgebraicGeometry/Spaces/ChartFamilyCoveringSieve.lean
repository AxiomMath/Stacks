module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundleSplitEpiComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafIsoOfCartesianFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.Fiber

/-!
# A family of étale charts covering the points of an algebraic space is a covering family

Let `X` be an algebraic space and `V_k ⟶ X` a family of étale charts whose images cover the points
of `X`. For every object `T` of the big fppf site and every `x ∈ X(T)`, the sieve of the morphisms
`T' ⟶ T` along which `x` lifts to one of the `V_k` is a covering sieve: it contains the base
changes `T ×_X V_k ⟶ T`, which are étale and jointly surjective, so an fppf covering family.

## Main results

* `AlgebraicGeometry.Space.ofArrows_mem_topology_of_flat_of_jointlySurjective`: a jointly
  surjective family of flat morphisms locally of finite presentation generates a covering sieve.
* `AlgebraicGeometry.Space.familyImageSieve_chartHom_mem_topology`: the covering statement for a
  family of étale charts covering the points of `X`.
* `AlgebraicGeometry.Space.exists_affine_free_chart_over`: every point of a chart lies under a
  point of an affine chart on which a finite locally free module is free.
* `AlgebraicGeometry.Space.exists_affine_free_chart_family`: a covering family of affine charts
  on which a finite locally free module is free.

## References

* [Stacks Project, Tag 03YC](https://stacks.math.columbia.edu/tag/03YC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A jointly surjective family of flat morphisms locally of finite presentation generates a
covering sieve of the big fppf site**, for a family indexed by a type of the universe of the
schemes. -/
theorem ofArrows_mem_topology_of_flat_of_jointlySurjective {T : BigFppfOver B S hS} {ι : Type u}
    (P : ι → BigFppfOver B S hS) (q : ∀ k, P k ⟶ T)
    (hc : ∀ t : (BigFppfOver.toScheme B S hS).obj T,
      ∃ k, t ∈ Set.range ((BigFppfOver.toScheme B S hS).map (q k)).base)
    (hf : ∀ k, Flat ((BigFppfOver.toScheme B S hS).map (q k)) ∧
      LocallyOfFinitePresentation ((BigFppfOver.toScheme B S hS).map (q k))) :
    Sieve.ofArrows P q ∈ BigFppfOver.topology B S hS T := by
  have e : Sieve.ofArrows P q =
      Sieve.ofArrows (fun k : ULift.{u + 1} ι => P k.down) (fun k => q k.down) := by
    apply le_antisymm <;> rw [Sieve.ofArrows, Sieve.generate_le_iff] <;> rintro _ _ ⟨k⟩
    · exact Sieve.ofArrows_mk _ _ (ULift.up k)
    · exact Sieve.ofArrows_mk _ _ k.down
  rw [e, BigFppfOver.topology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
  let E : PreZeroHypercover.{u + 1} T.left :=
    ⟨ULift.{u + 1} ι, fun k => (P k.down).left, fun k => (q k.down).left⟩
  apply BigFppfSite.generate_mem_topology_of_isFppfCovering B (E := E)
  rw [AlgebraicGeometry.IsFppfCovering, Precoverage.mem_comap_iff,
    ← PreZeroHypercover.presieve₀_map, Scheme.fppfPrecoverage, Scheme.ofArrows_mem_precoverage_iff]
  refine ⟨fun t => ?_, fun k => hf k.down⟩
  obtain ⟨k, v, hv⟩ := hc t
  exact ⟨ULift.up k, v, hv⟩

variable {X : AlgebraicSpaces B S hS}

/-- **A family of étale charts covering the points of an algebraic space is a covering family**:
for `x ∈ X(T)`, the sieve of the morphisms `T' ⟶ T` along which `x` lifts to one of the charts is
a covering sieve of `T`. -/
theorem familyImageSieve_chartHom_mem_topology {ι : Type u} (V : ι → SmallEtale B S hS X.1)
    (hcov : ∀ p : points B S hS X.1, ∃ k, p ∈ Set.range (pointsMap B S hS _ (V k).obj.hom))
    (T : BigFppfOver B S hS) (x : X.1.obj (op T)) :
    Presheaf.familyImageSieve (fun k => (V k).obj.hom) x ∈ BigFppfOver.topology B S hS T := by
  let ψ : yoneda.obj T ⟶ X.1 := yonedaEquiv.symm x
  let P : ι → BigFppfOver B S hS := fun k => (V k).property.rep.pullback ψ
  let q : ∀ k, P k ⟶ T := fun k => (V k).property.rep.snd ψ
  refine BigFppfOver.topology B S hS |>.superset_covering ?_
    (ofArrows_mem_topology_of_flat_of_jointlySurjective P q (fun t => ?_) (fun k => ?_))
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨k⟩
    refine ⟨k, yonedaEquiv ((V k).property.rep.fst ψ), ?_⟩
    rw [← yonedaEquiv_comp, (V k).property.rep.w ψ, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact yonedaEquiv_symm_app_apply x (op (P k)) (q k)
  · obtain ⟨pt, rfl⟩ := surjective_pointsToScheme B S hS T t
    obtain ⟨k, hk⟩ := hcov (pointsMap B S hS _ ψ pt)
    refine ⟨k, (pointsToScheme_mem_range_iff (q k) pt).2 ?_⟩
    rwa [← preimage_range_pointsMap_of_isPullback B S hS ((V k).property.rep.isPullback ψ)]
  · have : Etale ((BigFppfOver.toScheme B S hS).map (q k)) := (V k).property.property_snd ψ
    exact ⟨inferInstance, inferInstance⟩

/-- **Every point of a chart lies under a point of an affine chart above it on which a finite
locally free module is free**, on a finite type. -/
theorem exists_affine_free_chart_over (F : SheafOfModules.{u} (structureRingSheaf B S hS X))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F]
    (V₀ : SmallEtale B S hS X.1) (z₀ : chartScheme V₀) :
    ∃ (V : SmallEtale B S hS X.1) (φ : V ⟶ V₀) (ι : Type u) (_ : Finite ι)
      (_ : F.over V ≅ SheafOfModules.free (R := (structureRingSheaf B S hS X).over V) ι)
      (z : chartScheme V), IsAffine (chartScheme V) ∧
        (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map φ) z = z₀ := by
  obtain ⟨q, hq, hfin⟩ :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.exists_isFiniteLocallyFreeData (M := F)
  obtain ⟨V, φ, ⟨i, ⟨g⟩⟩, hV, z, hz⟩ :=
    SmallEtale.exists_affine_mem_range_of_mem_topology B S hS X.1 (q.coversTop V₀) z₀
  have := hfin.isFiniteType i
  have : IsIso (q.generators i).π := hq.isIso i
  exact ⟨V, φ, (q.generators i).I, inferInstance,
    overFreeIsoOfHom B S hS X F g (asIso (q.generators i).π).symm, z, hV, hz⟩

/-- **A covering family of affine charts over the presenting chart on which a finite locally free
module is free**: affine charts `V_k` with morphisms `m_k` to the presenting chart of `X`, with
`ℰ|_{V_k}` free on a finite type, whose images cover the points of `X`, so that `x ∈ X(T)` lifts
to one of them locally on `T`. -/
theorem exists_affine_free_chart_family (F : SheafOfModules.{u} (structureRingSheaf B S hS X))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree F] :
    ∃ (ι : Type u) (V : ι → SmallEtale B S hS X.1)
      (_ : ∀ k, V k ⟶ presentationChart (presentationOfIsAlgebraicSpace B S hS X.1 X.2))
      (n : ι → Type u) (_ : ∀ k, Finite (n k))
      (_ : ∀ k, F.over (V k) ≅ SheafOfModules.free (R := (structureRingSheaf B S hS X).over (V k))
        (n k)),
      (∀ k, IsAffine (chartScheme (V k))) ∧
        ∀ (T : BigFppfOver B S hS) (x : X.1.obj (op T)),
          Presheaf.familyImageSieve (fun k => (V k).obj.hom) x ∈ BigFppfOver.topology B S hS T := by
  let P := presentationOfIsAlgebraicSpace B S hS X.1 X.2
  choose V φ n hn e z hV hz using exists_affine_free_chart_over F (presentationChart P)
  refine ⟨_, V, φ, n, hn, e, hV, familyImageSieve_chartHom_mem_topology V fun p => ?_⟩
  obtain ⟨a, rfl⟩ := Presentation.pointsMap_surjective P p
  let z₀ : chartScheme (presentationChart P) := pointsToScheme B S hS P.U a
  obtain ⟨b, hb⟩ := surjective_pointsToScheme B S hS _ (z z₀)
  refine ⟨z₀, b, ?_⟩
  have ha : pointsMap B S hS _ (yoneda.map ((SmallEtale.toOver B S hS X.1).map (φ z₀))) b = a := by
    refine injective_pointsToScheme B S hS P.U ?_
    refine (pointsToScheme_pointsMap_yoneda B S hS ((SmallEtale.toOver B S hS X.1).map (φ z₀))
      b).trans ?_
    rw [hb]
    exact hz z₀
  rw [← yoneda_map_toOver_map_comp_hom (φ z₀), pointsMap_comp_apply]
  exact congrArg (pointsMap B S hS _ P.toSpace) ha

end AlgebraicGeometry.Space

end
