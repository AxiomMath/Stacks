module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.PolynomialGeometry
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Unibranch
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts

/-!
# Both factors of an étale composite over a geometrically unibranch scheme are étale

Let `X ⟶ Y ⟶ Z` be morphisms of schemes with `Y` integral. If the composite is étale at a point
`x` of `X`, if `Y` is geometrically unibranch at the image of `x`, and if `x` is a specialization
of a point lying over the generic point of `Y`, then the first factor is étale at `x` and the
second is étale at the image of `x`. Globally: if the composite is étale and every irreducible
component of `X` dominates `Y`, then the first factor is étale and the second is étale at every
point in the image of the first. Dominance of an irreducible component `C` of `X` over `Y` is
stated as `closure (f '' C) = Set.univ`.

## Main results

* `AlgebraicGeometry.etaleAt_left_of_comp_etaleAt_of_specializes_genericPoint` and
  `AlgebraicGeometry.etaleAt_right_of_comp_etaleAt_of_specializes_genericPoint` are the two
  pointwise conclusions.
* `AlgebraicGeometry.etale_left_of_comp_etale_of_dominant_components` and
  `AlgebraicGeometry.etaleAt_right_of_comp_etale_of_dominant_components` are the two global
  conclusions.

## References

* [Stacks Project, Tag 0GSA](https://stacks.math.columbia.edu/tag/0GSA)
* [Stacks Project, Tag 0GSB](https://stacks.math.columbia.edu/tag/0GSB)
-/

public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

/-- If `j ≫ f` is étale at `x'` for an open immersion `j`, then `f` is étale at `j x'`. -/
private alias etaleAt_of_comp_isOpenImmersion := AlgebraicGeometry.etaleAt_of_open_precomp

/-- If a composite `f ≫ g` is étale at `x`, the intermediate scheme is integral and
geometrically unibranch at `f x`, and `x` is a specialization of a point whose image under `f` is
the generic point, then `f` is étale at `x`. -/
@[stacks 0GSA "first factor"]
theorem etaleAt_left_of_comp_etaleAt_of_specializes_genericPoint
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegral Y] {x x' : X}
    (hy : IsGeometricallyUnibranchAt Y (f x)) (hcomp : EtaleAt (f ≫ g) x)
    (hxx' : x' ⤳ x) (hx' : f x' = genericPoint Y) :
    EtaleAt f x := by
  obtain ⟨U, hU, hxU, hUcomp⟩ :=
    exists_isAffineOpen_etale_comp_ι_of_etaleAt (f ≫ g) x hcomp
  let fU : U.toScheme ⟶ Y := U.ι ≫ f
  have : Etale (fU ≫ g) := by simpa [fU, Category.assoc] using hUcomp
  have : Unramified (fU ≫ g) := ⟨fun z =>
    ((etaleAt_iff_smoothAt_and_unramifiedAt (fU ≫ g) z).mp
      ((etale_iff_forall_etaleAt (fU ≫ g)).mp ‹Etale (fU ≫ g)› z)).2⟩
  have : Unramified fU := unramified_of_comp fU g
  have : LocallyOfFiniteType fU :=
    ((unramified_iff_locallyOfFiniteType_and_formallyUnramified fU).mp ‹Unramified fU›).1
  have hx'U : x' ∈ U := (specializes_iff_forall_open.mp hxx') U U.2 hxU
  let xu : U.toScheme := ⟨x, hxU⟩
  let xu' : U.toScheme := ⟨x', hx'U⟩
  have hspecU : xu' ⤳ xu := U.ι.isOpenEmbedding.isInducing.specializes_iff.mp hxx'
  have hEtaleAtU : EtaleAt fU xu :=
    etaleAt_of_unramifiedAt_of_specializes_genericPoint fU hy hspecU hx'
      (Unramified.unramifiedAt xu)
  exact etaleAt_of_comp_isOpenImmersion U.ι f xu hEtaleAtU

/-- Under the hypotheses of
`AlgebraicGeometry.etaleAt_left_of_comp_etaleAt_of_specializes_genericPoint`, the second factor
is étale at the image of `x`. -/
@[stacks 0GSA "second factor"]
theorem etaleAt_right_of_comp_etaleAt_of_specializes_genericPoint
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegral Y] {x x' : X}
    (hy : IsGeometricallyUnibranchAt Y (f x)) (hcomp : EtaleAt (f ≫ g) x)
    (hxx' : x' ⤳ x) (hx' : f x' = genericPoint Y) :
    EtaleAt g (f x) := by
  obtain ⟨U, hU, hxU, hUF⟩ := exists_isAffineOpen_etale_comp_ι_of_etaleAt f x
    (etaleAt_left_of_comp_etaleAt_of_specializes_genericPoint f g hy hcomp hxx' hx')
  obtain ⟨V, hV, hxV, hVcomp⟩ :=
    exists_isAffineOpen_etale_comp_ι_of_etaleAt (f ≫ g) x hcomp
  obtain ⟨W, hW, hxW, hWUV⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  have hUFi : Etale (U.ι ≫ f) := hUF
  have hVci : Etale (V.ι ≫ (f ≫ g)) := hVcomp
  have hWf : Etale (W.ι ≫ f) := by
    rw [← Scheme.homOfLE_ι X (show W ≤ U from hWUV.trans inf_le_left), Category.assoc]
    infer_instance
  have hWcomp : Etale (W.ι ≫ (f ≫ g)) := by
    rw [← Scheme.homOfLE_ι X (show W ≤ V from hWUV.trans inf_le_right), Category.assoc]
    infer_instance
  let F : W.toScheme ⟶ Y := W.ι ≫ f
  let O : Y.Opens := ⟨Set.range F, (show IsOpenMap F from by
    have : Etale F := hWf
    exact Scheme.Hom.isOpenMap F).isOpen_range⟩
  have hxO : f x ∈ O := ⟨⟨x, hxW⟩, rfl⟩
  let D : W.toScheme.Opens := F ⁻¹ᵁ O
  let e : D.toScheme ⟶ O.toScheme := F.resLE O D le_rfl
  let q : O.toScheme ⟶ Z := O.ι ≫ g
  have : Surjective e :=
    ⟨fun ⟨_, w, hw⟩ => hw ▸ ⟨⟨w, ⟨w, rfl⟩⟩, Subtype.ext (by simp [e])⟩⟩
  have : Etale (e ≫ q) := by
    rw [show e ≫ q = D.ι ≫ (W.ι ≫ (f ≫ g)) by simp [e, q, F, Category.assoc]]
    infer_instance
  have : Etale q := Stacks.Etale.etale_of_comp_surjective_etale e q
  exact etaleAt_of_comp_isOpenImmersion O.ι g ⟨f x, hxO⟩
    ((etale_iff_forall_etaleAt q).mp ‹Etale q› ⟨f x, hxO⟩)

/-- The generic point of an irreducible component whose image is dense maps to the generic point
of an integral target, and generalizes any point of that component. -/
@[ega "0 2.1.8" "special case"]
private theorem exists_specializes_genericPoint_of_dominant_component
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegral Y]
    (hdom : ∀ C : irreducibleComponents X, closure (f '' (C : Set X)) = Set.univ) (x : X) :
    ∃ x' : X, x' ⤳ x ∧ f x' = genericPoint Y := by
  let C : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  have hη : IsGenericPoint C.2.1.genericPoint (C : Set X) :=
    C.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents _ C.2)
  refine ⟨C.2.1.genericPoint, hη.specializes mem_irreducibleComponent, ?_⟩
  have hfg := hη.image f.continuous
  rw [hdom C] at hfg
  exact hfg.eq (genericPoint_spec Y)

/-- If a composite `f ≫ g` is étale, the intermediate scheme is integral and geometrically
unibranch, and every irreducible component of the source dominates it, then `f` is étale. -/
@[stacks 0GSB "first factor"]
theorem etale_left_of_comp_etale_of_dominant_components
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegral Y]
    (hY : IsGeometricallyUnibranch Y) (hcomp : Etale (f ≫ g))
    (hdom : ∀ C : irreducibleComponents X, closure (f '' (C : Set X)) = Set.univ) :
    Etale f := by
  rw [etale_iff_forall_etaleAt]
  intro x
  obtain ⟨x', hxx', hx'⟩ := exists_specializes_genericPoint_of_dominant_component f hdom x
  exact etaleAt_left_of_comp_etaleAt_of_specializes_genericPoint f g (hY (f x))
    ((etale_iff_forall_etaleAt (f ≫ g)).mp hcomp x) hxx' hx'

/-- Under the hypotheses of
`AlgebraicGeometry.etale_left_of_comp_etale_of_dominant_components`, the second factor is étale
at every point in the image of the first. -/
@[stacks 0GSB "second factor"]
theorem etaleAt_right_of_comp_etale_of_dominant_components
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegral Y]
    (hY : IsGeometricallyUnibranch Y) (hcomp : Etale (f ≫ g))
    (hdom : ∀ C : irreducibleComponents X, closure (f '' (C : Set X)) = Set.univ) :
    ∀ y ∈ Set.range f, EtaleAt g y := by
  rintro y ⟨x, rfl⟩
  obtain ⟨x', hxx', hx'⟩ := exists_specializes_genericPoint_of_dominant_component f hdom x
  exact etaleAt_right_of_comp_etaleAt_of_specializes_genericPoint f g (hY (f x))
    ((etale_iff_forall_etaleAt (f ≫ g)).mp hcomp x) hxx' hx'

end AlgebraicGeometry

end
