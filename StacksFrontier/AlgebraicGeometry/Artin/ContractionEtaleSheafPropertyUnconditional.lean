module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleWitnessDescent

/-!
# Stacks 0GHG: the étale sheaf property of Artin's contraction functor, unconditionally

**Stacks 0GHG** says that in Situation 0GH8 the functor `F` of Stacks 0GHA —
`AlgebraicGeometry.Artin.contractionFunctor` — satisfies the sheaf property for all étale
coverings of locally Noetherian schemes over `S`. The statement is
`AlgebraicGeometry.Artin.ContractionSituation.SatisfiesEtaleSheafProperty`.

Let `{V_i ⟶ V}` be an étale covering of the locally Noetherian site over `S` and let
`t_i = (Z_i, u'_i, x̂_i)` be a compatible family of triples. Uniqueness of an amalgamation is
`AlgebraicGeometry.Artin.ContractionSituation.eq_of_mapTriple_eq`. For existence, the closed
subset `Z` and the morphisms `u' : V ∖ Z ⟶ U'` and `x̂ : V_{/Z} ⟶ W` are glued from the given
ones exactly as in `StacksFrontier.AlgebraicGeometry.Artin.ContractionEtaleSheafProperty`, and the
two remaining conditions on the glued triple are proved here:

* *`x̂` is adic*, because adicness of a morphism out of `V_{/Z}` into a formal algebraic space is
  étale local on `V`, by
  `AlgebraicGeometry.Space.isRepresentableByAlgebraicSpacesULift_of_etale_completionSheafRestrict`,
  since the completions `V_{i,/Z_i} ⟶ V_{/Z}` are representable étale and jointly surjective;
* *`(u', x̂)` is compatible*, because the compatibility condition descends along étale coverings
  of the locally Noetherian site
  (`AlgebraicGeometry.Artin.ContractionSituation.nonempty_compatibilityWitness_of_isEtaleCovering`:
  the dilatation of the base change of `g` along `x̂` exists by Stacks 0GDU, and the morphisms
  `x'_i` of the given witnesses, transported to it by the uniqueness half of Stacks 0GDU, glue by
  Stacks 0GI1).

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.exists_mapTriple_eq_of_isEtaleCovering`: the
  existence half of Stacks 0GHG.
* `AlgebraicGeometry.Artin.ContractionSituation.contractionFunctor_satisfiesEtaleSheafProperty`:
  **Stacks 0GHG**.

## References

* [Stacks Project, Tag 0GDU](https://stacks.math.columbia.edu/tag/0GDU)
* [Stacks Project, Tag 0GH8](https://stacks.math.columbia.edu/tag/0GH8)
* [Stacks Project, Tag 0GHA](https://stacks.math.columbia.edu/tag/0GHA)
* [Stacks Project, Tag 0GHG](https://stacks.math.columbia.edu/tag/0GHG)
* [Stacks Project, Tag 0GI1](https://stacks.math.columbia.edu/tag/0GI1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace Artin

attribute [local instance] Space.pointTopology

namespace ContractionSituation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A compatible family of triples on an étale covering family of the locally Noetherian site
over `S` has an amalgamation. -/
theorem exists_mapTriple_eq_of_isEtaleCovering (c : ContractionSituation B S hS)
    {E : Covering (LocallyNoetherianOver B S hS)}
    (hE : LocallyNoetherianOver.IsEtaleCovering B S hS E)
    (t : (i : E.2.I₀) → Triple c (E.2.X i).obj)
    (ht : ∀ (i j : E.2.I₀) (Y : LocallyNoetherianOver B S hS) (gi : Y ⟶ E.2.X i)
      (gj : Y ⟶ E.2.X j), gi ≫ E.2.f i = gj ≫ E.2.f j →
        mapTriple c gi.hom (t i) = mapTriple c gj.hom (t j)) :
    ∃ s : Triple c E.1.obj, ∀ i, mapTriple c (E.2.f i).hom s = t i := by
  have hetale : ∀ i, Etale ((BigFppfOver.toScheme B S hS).map (E.2.f i).hom) := fun i =>
    LocallyNoetherianOver.etale_of_isEtaleCovering B S hS hE i
  have hcov : Sieve.ofArrows (fun i => (E.2.X i).obj) (fun i => (E.2.f i).hom) ∈
      BigFppfOver.topology B S hS E.1.obj :=
    LocallyNoetherianOver.ofArrows_mem_topology_of_isCovering B S hS
      (LocallyNoetherianOver.isCovering_of_isEtaleCovering B S hS hE)
  have hpre : ∀ i, Space.pointsMap B S hS (yoneda.obj (E.2.X i).obj)
      (yoneda.map (E.2.f i).hom) ⁻¹' descendZ c t = (t i).Z :=
    fun i => pointsMap_preimage_descendZ c t ht i
  have hZi : ∀ i, (t i).Z = Space.pointsMap B S hS (yoneda.obj (E.2.X i).obj)
      (yoneda.map (E.2.f i).hom) ⁻¹' descendZ c t := fun i => (hpre i).symm
  have hWi := fun i => (congrArg compl (hZi i)).trans Set.preimage_compl.symm
  have htij : ∀ i j, mapTriple c
        (LocallyNoetherianOver.overlapFst B S hS (E.2.f i) (E.2.f j) (hetale i)).hom (t i) =
      mapTriple c
        (LocallyNoetherianOver.overlapSnd B S hS (E.2.f i) (E.2.f j) (hetale i)).hom (t j) :=
    fun i j => ht i j _ _ _ (LocallyNoetherianOver.overlapFst_comp_f B S hS _ _ _)
  have hZij : ∀ i j, Space.pointsMap B S hS
        (yoneda.obj (LocallyNoetherianOver.overlap B S hS (E.2.f i) (E.2.f j) (hetale i)).obj)
        (yoneda.map (LocallyNoetherianOver.overlapFst B S hS (E.2.f i) (E.2.f j)
          (hetale i)).hom) ⁻¹' (t i).Z =
      Space.pointsMap B S hS
        (yoneda.obj (LocallyNoetherianOver.overlap B S hS (E.2.f i) (E.2.f j) (hetale i)).obj)
        (yoneda.map (LocallyNoetherianOver.overlapSnd B S hS (E.2.f i) (E.2.f j)
          (hetale i)).hom) ⁻¹' (t j).Z := fun i j => congrArg Triple.Z (htij i j)
  have hWij₂ := fun i j => (congrArg compl (hZij i j)).trans Set.preimage_compl.symm
  have hcompatU := Space.compatible_of_overlap_openSubspaceOfPoints B S hS
    (fun i => (E.2.X i).obj) (fun i => (E.2.f i).hom) (descendZ c t)ᶜ
    (fun i => ((t i).Z)ᶜ) hWi (fun i => (t i).u)
    (fun i j => (LocallyNoetherianOver.overlap B S hS (E.2.f i) (E.2.f j) (hetale i)).obj)
    (fun i j =>
      (LocallyNoetherianOver.overlapFst B S hS (E.2.f i) (E.2.f j) (hetale i)).hom)
    (fun i j =>
      (LocallyNoetherianOver.overlapSnd B S hS (E.2.f i) (E.2.f j) (hetale i)).hom)
    (fun i j => (Space.pointsMap B S hS
      (yoneda.obj (LocallyNoetherianOver.overlap B S hS (E.2.f i) (E.2.f j) (hetale i)).obj)
      (yoneda.map (LocallyNoetherianOver.overlapFst B S hS (E.2.f i) (E.2.f j)
        (hetale i)).hom) ⁻¹' (t i).Z)ᶜ)
    (fun i j => Set.preimage_compl.symm) hWij₂
    (fun i j Y a b hab =>
      LocallyNoetherianOver.exists_lift_overlap B S hS (E.2.f i) (E.2.f j) (hetale i) Y a b hab)
    (fun i j => u_restrict_eq_of_mapTriple_eq c _ _ (t i) (t j) (htij i j) _ rfl
      (fun _ hz => hz) (hWij₂ i j).subset)
  obtain ⟨uG, huG, -⟩ := Space.glueHom_openSubspaceOfPoints B S hS
    (fun i => (E.2.X i).obj) (fun i => (E.2.f i).hom) hcov (descendZ c t)ᶜ
    (fun i => ((t i).Z)ᶜ) hWi c.isOpenSubspace_U'.1.isSheaf (fun i => (t i).u) hcompatU
  have hcompatX := Space.compatible_of_overlap_completionSubfunctor B S hS
    (fun i => (E.2.X i).obj) (fun i => (E.2.f i).hom) (descendZ c t)
    (fun i => (t i).Z) hZi
    (fun i => (BigFppfOver.topology B S hS).toSheafify
      (Space.completionSubfunctor B S hS (yoneda.obj (E.2.X i).obj) (t i).Z).toFunctor ≫
        (t i).xhat.hom)
    (fun i j => (LocallyNoetherianOver.overlap B S hS (E.2.f i) (E.2.f j) (hetale i)).obj)
    (fun i j =>
      (LocallyNoetherianOver.overlapFst B S hS (E.2.f i) (E.2.f j) (hetale i)).hom)
    (fun i j =>
      (LocallyNoetherianOver.overlapSnd B S hS (E.2.f i) (E.2.f j) (hetale i)).hom)
    (fun i j => Space.pointsMap B S hS
      (yoneda.obj (LocallyNoetherianOver.overlap B S hS (E.2.f i) (E.2.f j) (hetale i)).obj)
      (yoneda.map (LocallyNoetherianOver.overlapFst B S hS (E.2.f i) (E.2.f j)
        (hetale i)).hom) ⁻¹' (t i).Z)
    (fun i j => rfl) hZij
    (fun i j Y a b hab =>
      LocallyNoetherianOver.exists_lift_overlap B S hS (E.2.f i) (E.2.f j) (hetale i) Y a b hab)
    (fun i j => completionSubfunctorRestrict_comp_eq_of_mapTriple_eq c _ _ (t i) (t j)
      (htij i j) _ rfl (fun _ hz => hz) (hZij i j).subset)
  obtain ⟨ψ₀, hψ₀, -⟩ := Space.glueHom_completionSubfunctor B S hS
    (fun i => (E.2.X i).obj) (fun i => (E.2.f i).hom) hcov (descendZ c t)
    (fun i => (t i).Z) hZi c.W.property
    (fun i => (BigFppfOver.topology B S hS).toSheafify
      (Space.completionSubfunctor B S hS (yoneda.obj (E.2.X i).obj) (t i).Z).toFunctor ≫
        (t i).xhat.hom) hcompatX
  obtain ⟨xG, hxG⟩ := Space.exists_hom_completionSheaf B S hS
    (fun i => (E.2.X i).obj) (fun i => (E.2.f i).hom) (descendZ c t)
    (fun i => (t i).Z) (fun i => (hZi i).subset) (fun i => (t i).xhat) ψ₀ hψ₀
  have hadic : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS xG.hom := by
    refine Space.isRepresentableByAlgebraicSpacesULift_of_etale_completionSheafRestrict B S hS
      (fun i => (E.2.X i).obj) (fun i => (E.2.f i).hom) hcov hetale (descendZ c t)
      (isClosed_descendZ c hE t) c.isLocallyNoetherian_W.1 xG fun i => ?_
    refine (adic_completionSheafRestrict_congr (yoneda.map (E.2.f i).hom) (hpre i)
      (fun _ hz => hz) (hZi i).subset xG).mpr ?_
    rw [hxG i]
    exact (t i).adic_xhat
  refine ⟨{ Z := descendZ c t
            isClosed_Z := isClosed_descendZ c hE t
            u := uG
            xhat := xG
            adic_xhat := hadic
            compatible := ?_ }, ?_⟩
  · refine nonempty_compatibilityWitness_of_isEtaleCovering c hE (isClosed_descendZ c hE t)
      uG xG hadic fun i => ?_
    refine nonempty_compatibilityWitness_congr c (hZi i) ?_ ?_ (t i).compatible
    · exact (heq_of_eq (huG i).symm).trans
        (Space.heq_openSubspaceOfPointsRestrict_source B S hS (yoneda.map (E.2.f i).hom)
          (congrArg compl (hZi i)) (hWi i).subset (fun _ hz => hz) uG)
    · exact (heq_of_eq (hxG i).symm).trans
        (Space.heq_completionSheafRestrict_source B S hS (yoneda.map (E.2.f i).hom)
          (hZi i) (hZi i).subset (fun _ hz => hz) xG)
  · intro i
    refine Triple.ext_of_heq c ((mapTriple_Z_eq_preimage c _ _).trans (hpre i)) ?_ ?_
    · rw [mapTriple_u]
      refine HEq.trans ?_ (heq_of_eq (huG i))
      exact Space.heq_openSubspaceOfPointsRestrict_source B S hS
        (yoneda.map (E.2.f i).hom) (congrArg compl (hpre i))
        (W := (descendZ c t)ᶜ) (fun _ hz => hz) (hWi i).subset uG
    · rw [mapTriple_xhat]
      refine HEq.trans ?_ (heq_of_eq (hxG i))
      exact Space.heq_completionSheafRestrict_source B S hS (yoneda.map (E.2.f i).hom)
        (hpre i) (T := descendZ c t) (fun _ hz => hz) (hZi i).subset xG

/-! ### Stacks 0GHG -/

/-- In a contraction situation the functor `F` of triples satisfies the sheaf property for all
étale coverings of locally Noetherian schemes over `S`: a compatible family of triples on such a
covering has a unique amalgamation. -/
@[stacks 0GHG]
theorem contractionFunctor_satisfiesEtaleSheafProperty (c : ContractionSituation B S hS) :
    SatisfiesEtaleSheafProperty c := by
  rw [satisfiesEtaleSheafProperty_iff]
  intro E hE t ht
  obtain ⟨s, hs⟩ := exists_mapTriple_eq_of_isEtaleCovering B S hS c hE t ht
  exact ⟨s, hs, fun s' hs' =>
    eq_of_mapTriple_eq B S hS hE fun i => (hs' i).trans (hs i).symm⟩

end ContractionSituation

end Artin

end AlgebraicGeometry

end
