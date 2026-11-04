module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesEtaleCovering

/-!
# Étale coverings by smooth lifts from pointwise local lifts

The covering step of Stacks 0CJV, in the form its local step produces: if every scheme of the site
étale over `W` through a morphism factoring through a smooth surjection `p : V₀ ⟶ W` admits, around
each of its points, an open on which a smooth lift along the thickening exists, then the bases of
smooth lifts form an étale covering of `W`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The covering from pointwise local lifts.** -/
theorem exists_etaleCovering_etaleSmoothLift_of_local
    {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} (ι : 𝒳 ⟶ 𝒳') (hι : IsThickening ι)
    (W : AlgebraicSpaces B S hS)
    (x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳)
    (hx : AlgebraicStacks.IsSmooth B S hS x)
    (V₀ : AlgebraicSpaces B S hS) (p : V₀ ⟶ W)
    (hp : Space.IsSmooth B S hS p.hom)
    (hpsurj : Function.Surjective (Space.pointsMap B S hS V₀.obj p.hom))
    (hloc : ∀ (T : BigFppfOver B S hS) (t : yoneda.obj T ⟶ W.obj) (_ : Space.IsEtale B S hS t),
      (∃ s : yoneda.obj T ⟶ V₀.obj, s ≫ p.hom = t) →
      ∀ y : (BigFppfOver.toScheme B S hS).obj T,
        ∃ (A : BigFppfOver B S hS) (m : A ⟶ T) (hm : Space.IsEtale B S hS (yoneda.map m ≫ t))
          (ξ : EtaleSmoothLift B S hS ι hι W x hx),
          y ∈ Set.range ((BigFppfOver.toScheme B S hS).map m) ∧
          ξ.base = Space.SpacesEtale.ofRepresentable B S hS W A (yoneda.map m ≫ t) hm) :
    ∃ (J : Type (u + 1)) (ξ : J → EtaleSmoothLift B S hS ι hι W x hx),
      Space.IsEtaleCovering B S hS (fun j => ((ξ j).base.obj.left).obj)
        (fun j => ((ξ j).base.obj.hom).hom) := by
  classical
  have hpcov : Space.IsSmoothCovering B S hS (fun _ : Unit => V₀.obj) (fun _ => p.hom) := by
    refine ⟨W.property, fun _ => V₀.property, fun _ => hp, ?_⟩
    rw [Set.iUnion_const]
    exact Set.range_eq_univ.mpr hpsurj
  obtain ⟨J, T, t, hcov, href⟩ :=
    Space.exists_isEtaleCovering_representable_refining_isSmoothCovering B S hS hpcov
  have href' : ∀ j, ∃ s : yoneda.obj (T j) ⟶ V₀.obj, s ≫ p.hom = t j := by
    intro j
    obtain ⟨-, s, hs⟩ := href j
    exact ⟨s, hs⟩
  choose A m hm ξ hyA hbase using fun (j : J) (y : (BigFppfOver.toScheme B S hS).obj (T j)) =>
    hloc (T j) (t j) (hcov.etale j) (href' j) y
  have hrange : ∀ (j : J) (y : (BigFppfOver.toScheme B S hS).obj (T j)),
      Set.range (Space.pointsMap B S hS (yoneda.obj (A j y)) (yoneda.map (m j y) ≫ t j)) ⊆
        Set.range (Space.pointsMap B S hS ((ξ j y).base.obj.left).obj
          ((ξ j y).base.obj.hom).hom) := by
    intro j y
    rw [hbase j y, Space.SpacesEtale.ofRepresentable_hom]
    exact subset_rfl
  refine ⟨(j : J) × ((BigFppfOver.toScheme B S hS).obj (T j)), fun z => ξ z.1 z.2,
    W.property, fun z => ((ξ z.1 z.2).base.obj.left).property,
    fun z => (ξ z.1 z.2).base.property, ?_⟩
  refine Set.eq_univ_iff_forall.mpr fun q => ?_
  obtain ⟨j, z, hz⟩ :=
    Set.mem_iUnion.mp (Set.eq_univ_iff_forall.mp hcov.jointly_surjective q)
  set y := Space.pointsToScheme B S hS (T j) z with hy
  obtain ⟨s, hs⟩ := hyA j y
  obtain ⟨r, hr⟩ := (Space.bijective_pointsToScheme B S hS (A j y)).surjective s
  have hzr : Space.pointsMap B S hS (yoneda.obj (A j y)) (yoneda.map (m j y)) r = z :=
    (Space.bijective_pointsToScheme B S hS (T j)).injective
      (by rw [Space.pointsToScheme_pointsMap_yoneda, hr, hs, hy])
  have hq : Space.pointsMap B S hS (yoneda.obj (A j y))
      (yoneda.map (m j y) ≫ t j) r = q := by
    rw [Space.pointsMap_comp B S hS _ (yoneda.map (m j y)) (t j), Function.comp_apply, hzr, hz]
  exact Set.mem_iUnion.mpr ⟨⟨j, y⟩, hrange j y ⟨r, hq⟩⟩

end AlgebraicGeometry.Stack

end
