module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingFibreProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Point.PresheafFiberIndEtale

/-!
# The geometric stalks of an algebraic space are ind-étale over its affine charts

Let `Z` be an algebraic space over a scheme `S`, let `V` be an étale scheme chart of `Z` whose
underlying scheme is affine, and let `x` be a geometric point of `Z` together with a lift `v` of
it to `V`.  The stalk at `x` of the structure sheaf of the small étale site of `Z` — the fibre at
the point of the site of Stacks 04K0 — is a filtered colimit of étale `𝒪(V)`-algebras, through
the germ map at `v`.

This is the input that Stacks 04HX and 04KF provide for the étale local rings of an algebraic
space: the stalk is the strict henselization of the local ring of `V` at the image of `v`, and in
particular it is ind-étale over `𝒪(V)`.  Only the ind-étaleness is proved here, directly from the
neighbourhoods of `x`: each of them is refined by an affine one, and the restriction from `𝒪(V)`
to an affine chart over `V` is étale.

## Main results

* `AlgebraicGeometry.Space.geometricStalk_ind_etale`: the ind-étaleness above.
* `AlgebraicGeometry.Space.exists_affine_fiber_refinement`: every neighbourhood of a geometric
  point in the small étale site is refined by one with affine chart.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Affine refinements of neighbourhoods of a geometric point.**  Every lift of a geometric
point of an algebraic space to an étale chart comes from a lift to an étale chart whose
underlying scheme is affine, mapping to the given one. -/
theorem exists_affine_fiber_refinement (Z : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS Z.1) (X : SmallEtale B S hS Z.1)
    (p : (etaleSitePoint B S hS Z.1 x Z.2).fiber.obj X) :
    ∃ (Y : SmallEtale B S hS Z.1) (g : Y ⟶ X) (q : (etaleSitePoint B S hS Z.1 x Z.2).fiber.obj Y),
      (etaleSitePoint B S hS Z.1 x Z.2).fiber.map g q = p ∧
        IsAffine ((SmallEtale.toOver B S hS Z.1 ⋙ BigFppfOver.toScheme B S hS).obj Y) := by
  let N : SmallEtaleNeighborhood x := ⟨X, p.1, p.2⟩
  obtain ⟨W, j, hW, -, hj, hpt, -⟩ := exists_affine_refinement B S hS N ⊤ trivial
  let g : W.chart ⟶ X := ObjectProperty.homMk (CostructuredArrow.homMk j hj.symm)
  refine ⟨W.chart, g, ⟨W.point, W.point_comp⟩, Subtype.ext hpt, hW⟩

/-- **The geometric stalks of an algebraic space are ind-étale over its affine charts.** -/
theorem geometricStalk_ind_etale (Z : AlgebraicSpaces B S hS) (V : SmallEtale B S hS Z.1)
    (hV : IsAffine ((SmallEtale.toOver B S hS Z.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    (x : GeometricPoint B S hS Z.1) (v : (etaleSitePoint B S hS Z.1 x Z.2).fiber.obj V) :
    letI := ((etaleSitePoint B S hS Z.1 x Z.2).toPresheafFiber V v
      (smallEtaleRingedTopos B S hS Z).O.obj).hom.toAlgebra
    (CommAlgCat.etale.{u} ((smallEtaleRingedTopos B S hS Z).O.obj.obj (op V))).ind.{u}
      (CommAlgCat.of ((smallEtaleRingedTopos B S hS Z).O.obj.obj (op V))
        (((etaleSitePoint B S hS Z.1 x Z.2).presheafFiber (A := CommRingCat.{u})).obj
          (smallEtaleRingedTopos B S hS Z).O.obj)) := by
  refine (etaleSitePoint B S hS Z.1 x Z.2).ind_etale_presheafFiber _ v ?_
  intro X k p hp
  obtain ⟨Y, g, q, hq, hY⟩ := exists_affine_fiber_refinement B S hS Z x X p
  exact ⟨Y, g, q, hq, etale_chartRestrict B S hS (g ≫ k) hV hY⟩

end AlgebraicGeometry.Space

end
