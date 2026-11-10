module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.CohenMacaulayDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SmoothDimensionFormula
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat

/-!
# The dimension formula for a flat morphism of algebraic spaces of constant relative dimension

Let `f : X ⟶ Y` be a flat morphism, locally of finite type, of locally Noetherian algebraic spaces
over `S`, of relative dimension `d` at every point of `X` (Stacks 04NM). Then
`dim_x(X) = dim_{f(x)}(Y) + d` at every point `x` of `X`. This is Stacks 0AFE read for algebraic
spaces.

## Main results

* `AlgebraicGeometry.relativeDimension_of_topologicalKrullDimAt_fiber_eq'`: a morphism of
  schemes locally of finite type whose fibres have local dimension `d` at each of their points has
  relative dimension `d`.
* `AlgebraicGeometry.Space.dimensionAtPoint_eq_add_of_isFlat`: the dimension formula.

## Implementation notes

The proof is the reduction to schemes of
`AlgebraicGeometry.Space.dimensionAtPoint_eq_add_of_isSmooth`
(Stacks 0AFI), with Stacks 0AFE in place of Stacks 0AFF. A commuting square of surjective étale
charts `α : U ⟶ V` over `f` is flat and locally of finite type. Every point `u` of `U` is the
point selected by the canonical field-valued representative at `u`
(`AlgebraicGeometry.Space.schemePointRepresentative`), so the relative dimension `d` of `f` at the
image of that representative reads, on the chart, as local dimension `d` of the fibre of `α` at
`u`. All fibres of `α` therefore have constant local dimension `d`, which is relative dimension
`d` in the sense of Stacks 0AFE.

## References

* [Stacks Project, Tag 0AFE](https://stacks.math.columbia.edu/tag/0AFE)
* [Stacks Project, Tag 0AFI](https://stacks.math.columbia.edu/tag/0AFI)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **A morphism locally of finite type whose fibres have constant local dimension `d` has
relative dimension `d`.** Each fibre is equidimensional, its components all having the local
dimension at their generic points, and of dimension `d`. -/
public theorem relativeDimension_of_topologicalKrullDimAt_fiber_eq' {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] {d : ℕ}
    (h : ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞)) :
    RelativeDimension f d := by
  have hall : ∀ (s : S) (w : f.fiber s),
      topologicalKrullDimAt (f.fiber s) w = (d : WithBot ℕ∞) := by
    intro s w
    have hs : f (f.fiberι s w) = s := by
      have hmem := (f.fiberHomeo s w).2
      rwa [Scheme.Hom.fiberHomeo_apply, Set.mem_preimage, Set.mem_singleton_iff] at hmem
    rw [← Scheme.Hom.cast_asFiber_fiberι f s w hs]
    have key : ∀ (y : S) (hy : f (f.fiberι s w) = y),
        topologicalKrullDimAt (f.fiber y) (hy ▸ f.asFiber (f.fiberι s w)) =
          (d : WithBot ℕ∞) := by
      rintro y rfl
      exact h _
    exact key s hs
  intro s hs
  have hFT : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
    change LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField s))
    infer_instance
  refine ⟨equidimensional_of_topologicalKrullDimAt_eq (S.residueField s) (f.fiber s)
    (f.fiberToSpecResidueField s) (hall s), ?_⟩
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  have hloc : ∀ w : f.fiber s, localKrullDim (f.fiber s) w = (d : WithBot ℕ∞) := fun w ↦ by
    rw [← topologicalKrullDimAt_eq_localKrullDim, hall s w]
  simp_rw [hloc]
  have : Nonempty (f.fiber s) := hs
  exact iSup_const

namespace Space

/-- **Stacks 0AFE for algebraic spaces.** Let `f : X ⟶ Y` be a flat morphism, locally of finite
type, of locally Noetherian algebraic spaces over `S`, of relative dimension `d` (Stacks 04NM) at
every point of `X`. Then `dim_x(X) = dim_{f(x)}(Y) + d` for every point `x` of `X`. -/
public theorem dimensionAtPoint_eq_add_of_isFlat
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hNY : HasEtaleLocalProperty B S hS Y (fun Z : Scheme.{u} => IsLocallyNoetherian Z))
    (f : X ⟶ Y) (hflat : IsFlat B S hS f) (hft : IsLocallyOfFiniteType B S hS f) {d : ℕ}
    (hd : ∀ x : points B S hS X, HasRelativeDimensionAt (d : ℕ∞) B S hS f x)
    (x : points B S hS X) :
    dimensionAtPoint B S hS X hX x =
      dimensionAtPoint B S hS Y hY (pointsMap B S hS X f x) + (d : WithBot ℕ∞) := by
  classical
  set T := BigFppfOver.toScheme B S hS
  obtain ⟨V, b, hbSurj, hbEtale, hVnoeth⟩ := hNY
  obtain ⟨U, a, α, hsq, haSurj, haEtale⟩ :=
    exists_surjective_etale_presentation_lift B S hS hX hY f V b hbSurj hbEtale
  have _ : IsLocallyNoetherian (T.obj V) := hVnoeth
  have _ : Flat (T.map α) := hflat U V a b α haEtale hbEtale hsq.symm
  have _ : LocallyOfFiniteType (T.map α) := hft U V a b α haEtale hbEtale hsq.symm
  have _ : IsLocallyNoetherian (T.obj U) :=
    LocallyOfFiniteType.isLocallyNoetherian (T.map α)
  -- every fibre of the chart morphism has local dimension `d` at each of its points
  have hfib : ∀ u : T.obj U,
      topologicalKrullDimAt ((T.map α).fiber ((T.map α) u)) ((T.map α).asFiber u) =
        (d : WithBot ℕ∞) := by
    intro u
    let p := schemePointRepresentative B S hS U u
    have hpu : schemePoint B S hS U p = u := schemePointRepresentative_point B S hS U u
    have h := (hasFiberDimensionAt_ofSchemeHom_iff (T.map α) (schemePoint B S hS U p) d).mp
      (hd (pointsMap B S hS (yoneda.obj U) a (p.class B S hS (yoneda.obj U)))
        { U := U, V := V, a := a, b := b, h := α, a_etale := haEtale, b_etale := hbEtale
          comm := hsq.symm, representative := p
          point := IsLocalRing.closedPoint p.carrier, maps_to := rfl })
    rwa [hpu] at h
  -- a field-valued representative of `x` on the chart, and its image on the target chart
  obtain ⟨z, hz⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).mp haSurj x
  obtain ⟨p, rfl⟩ := Quot.exists_rep z
  set pV := FieldValuedPoint.map B S hS (yoneda.obj U) (yoneda.map α) p with hpV
  have hpVmaps : pointsMap B S hS (yoneda.obj V) b (pV.class B S hS (yoneda.obj V)) =
      pointsMap B S hS X f x := by
    rw [hpV, ← pointsMap_class, ← Function.comp_apply
      (f := pointsMap B S hS (yoneda.obj V) b), ← pointsMap_comp, ← hsq, pointsMap_comp,
      Function.comp_apply, hz]
  rw [dimensionAtPoint_eq_of_etale_chart B S hS X hX x U a haEtale p hz,
    dimensionAtPoint_eq_of_etale_chart B S hS Y hY _ V b hbEtale pV hpVmaps,
    hpV, schemePoint_map_yoneda B S hS α p]
  exact topologicalKrullDimAt_eq_add_of_relativeDimension (T.map α)
    (relativeDimension_of_topologicalKrullDimAt_fiber_eq' (T.map α) hfib) (schemePoint B S hS U p)

end Space

end AlgebraicGeometry

end
