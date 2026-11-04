module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalDichotomy
public import StacksFrontier.AlgebraicGeometry.Curves.NodalGorensteinReduced
public import StacksFrontier.AlgebraicGeometry.Curves.NodalUnramifiedSingularSubscheme
public import StacksFrontier.AlgebraicGeometry.Curves.NodeFittingIdealClosedPoint
public import StacksFrontier.AlgebraicGeometry.Curves.NodeStalkCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.TestModuleStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.AtPointCriteria
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.Separable
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.BaseFieldResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.RamificationAlgebraicClosure
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.DenseSmoothOpen
public import StacksFrontier.RingTheory.LocalCompleteIntersection.FlatAscent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Nodal curves are exactly the local complete intersections with unramified singular subscheme

Let `k` be a field and let `X` be a locally algebraic `k`-scheme, equidimensional of dimension
one.  Then `X` has at-worst-nodal singularities exactly when `X` is a local complete
intersection over `k` and the closed subscheme `Sing(X/k) ⊆ X` cut out by the first Fitting
ideal of `Ω_{X/k}` is unramified over `k`.  These are conditions (1) and (2) of Tag 0C4E.

For (2) ⟹ (1) the hypotheses give, at a closed point which is not a smooth point, the three
numerical conditions of condition (5) of Tag 0C4D
(`Stacks.Curves.smoothAt_or_isSeparable_and_depth_eq_one_and_fittingIdeal_eq_maximalIdeal`), and
the six-way equivalence of that tag at an arbitrary closed point over an arbitrary field
(`Stacks.Curves.isNode_tfae_of_isClosed`) turns them into the node condition.

For (1) ⟹ (2) nodality is first extended from the closed points to all of `X`: an at-worst-nodal
curve is geometrically reduced over `k` (Tag 0E37), so it is smooth over `k` at the generic point
of each of its irreducible components (Tag 056V), and every other point is closed.  The local
ring at a smooth point is then regular and the local ring at a node is a complete intersection
over `k` (its completion being a power-series hypersurface, Tag 0C49), which is local
completeness of the intersection by Tag 01UG.  For the singular subscheme, Tag 0C3K identifies
its points with the points at which `X` is not smooth over `k`, hence with the nodes; at a node
the stalk of the first Fitting ideal is the maximal ideal, so the local ring of the subscheme is
the residue field, which is finite and separable over `k`, and that is unramifiedness.

## Main results

* `AlgebraicGeometry.unramified_of_isField_stalk_of_finite_of_isSeparable` — a scheme locally of
  finite type over a field whose local rings are fields with finite separable residue field
  extensions is unramified over that field.
* `Stacks.Curves.smoothAt_of_not_isClosed` — a geometrically reduced curve is smooth over the
  base field at every point which is not closed.
* `Stacks.Curves.smoothAt_or_isNode_of_hasAtWorstNodalSingularities` — at *every* point of an
  at-worst-nodal curve the structure morphism is smooth or the point is a node.
* `Stacks.Curves.isNode_of_mem_range_relativeSingularIdeal` — every point of the singular
  subscheme of an at-worst-nodal curve is a node.
* `Stacks.Curves.hasAtWorstNodalSingularities_of_isLocalCompleteIntersectionOverField` and
  `Stacks.Curves.isLocalCompleteIntersectionOverField_of_hasAtWorstNodalSingularities` together
  with `Stacks.Curves.unramified_relativeSingularIdeal_of_hasAtWorstNodalSingularities` — the
  two implications of Tag 0C4E.
* `Stacks.Curves.hasAtWorstNodalSingularities_iff_lci_and_unramified_relativeSingularIdeal` —
  **Tag 0C4E**.

## Implementation notes

`AlgebraicGeometry.relativeSingularIdeal` is the first Fitting ideal of `Ω_{X/k}` and
`Scheme.IdealSheafData.subschemeι` the inclusion of the closed subscheme it cuts out, so
`Sing(X/k) ⟶ Spec k` is `(relativeSingularIdeal f).subschemeι ≫ f`;
`AlgebraicGeometry.IsLocalCompleteIntersectionOverField` is the local complete intersection
condition of Tag 01UC for a scheme over a field.

Unramifiedness is read off the stalks through item (7) of
`AlgebraicGeometry.unramifiedAt_tfae`, whose separability clause is stated over
`(Spec k).residueField`; the node supplies separability over `k` instead, and the two spellings
are compared by `AlgebraicGeometry.isSeparable_residueField_base_iff`.  The residue field of the
singular subscheme at a point is identified with the residue field of `X` at its image by
`AlgebraicGeometry.subschemeResidueFieldAlgEquiv`, an isomorphism of extensions of the residue
field of the base point, because the inclusion of a closed subscheme is surjective on stalks.

Completeness of the intersection is checked stalkwise, through the base-free notion
`LocalCompleteIntersection.IsCompleteIntersectionRing` and the comparison
`AlgebraicGeometry.isCompleteIntersection_stalk_iff_isCompleteIntersectionRing` of Tag 09Q6,
which is what lets the smooth points (where the stalk is regular) and the nodes (where the
completion of the stalk is a hypersurface) be treated by unrelated arguments.

## References

* [Stacks Project, Tag 0C4E](https://stacks.math.columbia.edu/tag/0C4E)
* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C47](https://stacks.math.columbia.edu/tag/0C47)
* [Stacks Project, Tag 0C49](https://stacks.math.columbia.edu/tag/0C49)
* [Stacks Project, Tag 0C3K](https://stacks.math.columbia.edu/tag/0C3K)
* [Stacks Project, Tag 01UC](https://stacks.math.columbia.edu/tag/01UC)
* [Stacks Project, Tag 01UG](https://stacks.math.columbia.edu/tag/01UG)
* [Stacks Project, Tag 02G8](https://stacks.math.columbia.edu/tag/02G8)
* [Stacks Project, Tag 056V](https://stacks.math.columbia.edu/tag/056V)
* [Stacks Project, Tag 09Q6](https://stacks.math.columbia.edu/tag/09Q6)
* [Stacks Project, Tag 0E37](https://stacks.math.columbia.edu/tag/0E37)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The residue field of the closed subscheme cut out by an ideal sheaf at a point is the
residue field of the ambient scheme at its image**, as an extension of the residue field of the
image of that point in the base. -/
noncomputable def subschemeResidueFieldAlgEquiv
    {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData) (z : I.subscheme) :
    letI : Algebra (S.residueField ((I.subschemeι ≫ f).base z))
        (X.residueField (I.subschemeι.base z)) :=
      (f.residueFieldMap (I.subschemeι.base z)).hom.toAlgebra
    letI : Algebra (S.residueField ((I.subschemeι ≫ f).base z)) (I.subscheme.residueField z) :=
      ((I.subschemeι ≫ f).residueFieldMap z).hom.toAlgebra
    X.residueField (I.subschemeι.base z) ≃ₐ[S.residueField ((I.subschemeι ≫ f).base z)]
      I.subscheme.residueField z :=
  letI : Algebra (S.residueField ((I.subschemeι ≫ f).base z))
      (X.residueField (I.subschemeι.base z)) :=
    (f.residueFieldMap (I.subschemeι.base z)).hom.toAlgebra
  letI : Algebra (S.residueField ((I.subschemeι ≫ f).base z)) (I.subscheme.residueField z) :=
    ((I.subschemeι ≫ f).residueFieldMap z).hom.toAlgebra
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective _
      (Scheme.Hom.bijective_residueFieldMap I.subschemeι z)) fun a => by
    change (I.subschemeι.residueFieldMap z).hom
        ((f.residueFieldMap (I.subschemeι.base z)).hom a) =
      ((I.subschemeι ≫ f).residueFieldMap z).hom a
    rw [Scheme.residueFieldMap_comp]
    rfl

/-- **A scheme locally of finite type over a field whose local rings are fields with finite
separable residue field extensions is unramified over that field.** -/
@[sga "3 XI 1.3" "(ii)"]
theorem unramified_of_isField_stalk_of_finite_of_isSeparable
    (k : Type u) [Field k] {Z : Scheme.{u}} (g : Z ⟶ AlgebraicGeometry.Spec (.of k))
    [LocallyOfFiniteType g]
    (hfield : ∀ z : Z, IsField (Z.presheaf.stalk z))
    (hfin : ∀ z : Z,
      letI : Algebra ((AlgebraicGeometry.Spec (.of k)).residueField (g.base z))
          (Z.residueField z) := (g.residueFieldMap z).hom.toAlgebra
      Module.Finite ((AlgebraicGeometry.Spec (.of k)).residueField (g.base z))
        (Z.residueField z))
    (hsep : ∀ z : Z,
      letI : Algebra ((AlgebraicGeometry.Spec (.of k)).residueField (g.base z))
          (Z.residueField z) := (g.residueFieldMap z).hom.toAlgebra
      Algebra.IsSeparable ((AlgebraicGeometry.Spec (.of k)).residueField (g.base z))
        (Z.residueField z)) :
    Unramified g := by
  refine ⟨fun z => ?_⟩
  have hA : IsField ((AlgebraicGeometry.Spec (.of k)).presheaf.stalk (g.base z)) :=
    isField_stalk_of_isMax (x := g.base z) fun b _ => (Subsingleton.elim b _).le
  have hmax : Ideal.map (g.stalkMap z).hom
      (IsLocalRing.maximalIdeal ((AlgebraicGeometry.Spec (.of k)).presheaf.stalk (g.base z))) =
      IsLocalRing.maximalIdeal (Z.presheaf.stalk z) := by
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp hA,
      IsLocalRing.isField_iff_maximalIdeal_eq.mp (hfield z), Ideal.map_bot]
  have h₇ := And.intro hmax (And.intro (hfin z) (hsep z))
  exact ((unramifiedAt_tfae g z).out 7 1).mp h₇

end AlgebraicGeometry

namespace Stacks.Curves

/-! ### Smoothness away from the nodes -/

/-- **A geometrically reduced curve is smooth over the base field at every point which is not
closed.** -/
theorem smoothAt_of_not_isClosed (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of k)) [LocallyOfFiniteType f]
    (hred : AlgebraicGeometry.IsReduced X) (hgeom : GeometricallyReduced f)
    (hdim : topologicalKrullDim X ≤ 1) {x : X} (hx : ¬ IsClosed ({x} : Set X)) :
    InfinitesimalLifting.SmoothAt f x := by
  have := hred
  have := hgeom
  have hgen : x ∈ genericPoints X :=
    closure_singleton_mem_irreducibleComponents_of_not_isClosed hdim hx
  exact InfinitesimalLifting.formallySmooth_stalkMap_smoothAt f x
    (Scheme.Hom.mem_smoothLocus.mp
      ((smoothLocus_iff_isGeometricallyReducedAt_genericPoint f x hgen).mpr
        ((geometricallyReduced_iff_forall_isGeometricallyReducedAt f).mp hgeom x)))

/-- **At every point of an at-worst-nodal curve the structure morphism is smooth or the point is
a node.** -/
theorem smoothAt_or_isNode_of_hasAtWorstNodalSingularities (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) (x : X) :
    InfinitesimalLifting.SmoothAt (X ↘ AlgebraicGeometry.Spec (.of k)) x ∨ IsNode k X x := by
  by_cases hx : IsClosed ({x} : Set X)
  · exact hnodal x hx
  · exact Or.inl (smoothAt_of_not_isClosed k _
      (isReduced_of_hasAtWorstNodalSingularities k X hnodal)
      (geometricallyReduced_of_hasAtWorstNodalSingularities k X hequi hdim hnodal) hdim.le hx)

/-- **Every point of the singular subscheme of an at-worst-nodal curve is a node.** -/
theorem isNode_of_mem_range_relativeSingularIdeal (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) {x : X}
    (hx : x ∈ Set.range
      (relativeSingularIdeal (X ↘ AlgebraicGeometry.Spec (.of k))).subschemeι) :
    IsNode k X x := by
  have hRD : RelativeDimension (X ↘ AlgebraicGeometry.Spec (.of k)) 1 :=
    relativeDimension_one_of_equidimensional k _ hequi hdim
  have : Flat (X ↘ AlgebraicGeometry.Spec (.of k)) := inferInstance
  have : LocallyOfFinitePresentation (X ↘ AlgebraicGeometry.Spec (.of k)) := inferInstance
  have hns : ¬ InfinitesimalLifting.SmoothAt (X ↘ AlgebraicGeometry.Spec (.of k)) x := by
    refine (mem_fittingIdeal_relativeDifferentials_iff_not_smoothAt
      (X ↘ AlgebraicGeometry.Spec (.of k)) 1 hRD x).mp ?_
    rw [Nat.cast_one]
    exact hx
  exact (smoothAt_or_isNode_of_hasAtWorstNodalSingularities k X hequi hdim hnodal x).resolve_left
    hns

/-! ### The implication (2) ⟹ (1) -/

/-- **The implication (2) ⟹ (1) of Tag 0C4E.** -/
theorem hasAtWorstNodalSingularities_of_isLocalCompleteIntersectionOverField
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (hlci : IsLocalCompleteIntersectionOverField (X ↘ AlgebraicGeometry.Spec (.of k)))
    (hZ : Unramified ((relativeSingularIdeal (X ↘ AlgebraicGeometry.Spec (.of k))).subschemeι ≫
      (X ↘ AlgebraicGeometry.Spec (.of k)))) :
    HasAtWorstNodalSingularities k X := by
  intro x hx
  obtain hsm | ⟨hsep, -, hdepth, hfit⟩ :=
    smoothAt_or_isSeparable_and_depth_eq_one_and_fittingIdeal_eq_maximalIdeal k
      (X ↘ AlgebraicGeometry.Spec (.of k)) hequi hdim hlci hZ x hx
  · exact Or.inl hsm
  · refine Or.inr ?_
    let : Algebra k (X.residueField x) :=
      ((X.residue x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫
        (X ↘ AlgebraicGeometry.Spec (.of k)).appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom).toAlgebra
    have hsepk : Algebra.IsSeparable k (X.residueField x) :=
      (isSeparable_residueField_base_iff k (X ↘ AlgebraicGeometry.Spec (.of k)) x).mp hsep
    have hc₅ := And.intro (Algebra.IsSeparableExtension.of_isSeparable k (X.residueField x))
      (And.intro hdepth hfit)
    exact ((isNode_tfae_of_isClosed k X hdim x hx).out 5 1).mp hc₅

/-! ### The implication (1) ⟹ (2) -/

/-- **The implication (1) ⟹ (2) of Tag 0C4E, the local-complete-intersection half.** -/
theorem isLocalCompleteIntersectionOverField_of_hasAtWorstNodalSingularities
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) :
    IsLocalCompleteIntersectionOverField (X ↘ AlgebraicGeometry.Spec (.of k)) := by
  refine ((localCompleteIntersection_tfae k X
    (X ↘ AlgebraicGeometry.Spec (.of k))).out 3 1).mp fun x => ?_
  refine (isCompleteIntersection_stalk_iff_isCompleteIntersectionRing k
    (X ↘ AlgebraicGeometry.Spec (.of k)) x).mpr ?_
  rcases smoothAt_or_isNode_of_hasAtWorstNodalSingularities k X hequi hdim hnodal x with hsm | hn
  · let := isRegularLocalRing_stalk_of_smoothAt k
      (X ↘ AlgebraicGeometry.Spec (.of k)) hsm
    exact LocalCompleteIntersection.isCompleteIntersectionRing_of_isRegularLocalRing _
  · exact isCompleteIntersectionRing_stalk_of_isNode k X hdim x hn

/-- **The implication (1) ⟹ (2) of Tag 0C4E, the unramifiedness half.** -/
theorem unramified_relativeSingularIdeal_of_hasAtWorstNodalSingularities
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) :
    Unramified ((relativeSingularIdeal (X ↘ AlgebraicGeometry.Spec (.of k))).subschemeι ≫
      (X ↘ AlgebraicGeometry.Spec (.of k))) := by
  set f : X ⟶ AlgebraicGeometry.Spec (.of k) := X ↘ AlgebraicGeometry.Spec (.of k)
  set I := relativeSingularIdeal f
  have hnodez : ∀ z : I.subscheme, IsNode k X (I.subschemeι.base z) := fun z =>
    isNode_of_mem_range_relativeSingularIdeal k X hequi hdim hnodal ⟨z, rfl⟩
  have hfitz : ∀ z : I.subscheme, IdealSheafData.stalk I (I.subschemeι.base z) =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (I.subschemeι.base z)) := by
    intro z
    have hc₄ := ((isNode_tfae_of_isClosed k X hdim _ (hnodez z).1).out 1 4).mp (hnodez z)
    exact hc₄.2.2
  let instK : ∀ x : X, Algebra k (X.residueField x) := fun x =>
    ((X.residue x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ x (by simp)).hom).toAlgebra
  let instR : ∀ z : I.subscheme,
      Algebra ((AlgebraicGeometry.Spec (.of k)).residueField ((I.subschemeι ≫ f).base z))
        (X.residueField (I.subschemeι.base z)) := fun z =>
    (f.residueFieldMap (I.subschemeι.base z)).hom.toAlgebra
  let instS : ∀ z : I.subscheme,
      Algebra ((AlgebraicGeometry.Spec (.of k)).residueField ((I.subschemeι ≫ f).base z))
        (I.subscheme.residueField z) := fun z =>
    ((I.subschemeι ≫ f).residueFieldMap z).hom.toAlgebra
  refine unramified_of_isField_stalk_of_finite_of_isSeparable k _ (fun z => ?_) (fun z => ?_)
    (fun z => ?_)
  · have e : I.subscheme.presheaf.stalk z ≃+*
        IsLocalRing.ResidueField (X.presheaf.stalk (I.subschemeι.base z)) :=
      (IdealSheafData.subschemeStalkQuotEquiv I z).symm.trans
        (Ideal.quotEquivOfEq (hfitz z))
    exact e.toMulEquiv.isField (Field.toIsField _)
  · have : Module.Finite
        ((AlgebraicGeometry.Spec (.of k)).residueField ((I.subschemeι ≫ f).base z))
        (X.residueField (I.subschemeι.base z)) :=
      (finite_residueField_base_iff k f (I.subschemeι.base z)).mpr
        (residueField_finite_of_closed_point k f _ (hnodez z).1)
    exact Module.Finite.equiv (subschemeResidueFieldAlgEquiv f I z).toLinearEquiv
  · have := isSeparableExtension_residueField_of_isNode k X hdim _ (hnodez z)
    have : Module.Finite k (X.residueField (I.subschemeι.base z)) :=
      residueField_finite_of_closed_point k f _ (hnodez z).1
    have hsepk : Algebra.IsSeparable k (X.residueField (I.subschemeι.base z)) :=
      Stacks.AlgebraicGeometry.ProperSectionsGeom.isSeparable_of_isSeparableExtension k _
    have hsepR : Algebra.IsSeparable
        ((AlgebraicGeometry.Spec (.of k)).residueField ((I.subschemeι ≫ f).base z))
        (X.residueField (I.subschemeι.base z)) :=
      (isSeparable_residueField_base_iff k f (I.subschemeι.base z)).mpr hsepk
    exact Algebra.IsSeparable.of_algHom _ (X.residueField (I.subschemeι.base z))
      (subschemeResidueFieldAlgEquiv f I z).symm.toAlgHom

/-! ### Tag 0C4E -/

/-- **Stacks Project, Tag 0C4E.** -/
@[stacks 0C4E]
theorem hasAtWorstNodalSingularities_iff_lci_and_unramified_relativeSingularIdeal
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 1) :
    HasAtWorstNodalSingularities k X ↔
      (IsLocalCompleteIntersectionOverField (X ↘ AlgebraicGeometry.Spec (.of k)) ∧
        Unramified ((relativeSingularIdeal
            (X ↘ AlgebraicGeometry.Spec (.of k))).subschemeι ≫
          (X ↘ AlgebraicGeometry.Spec (.of k)))) :=
  ⟨fun h => ⟨isLocalCompleteIntersectionOverField_of_hasAtWorstNodalSingularities k X hequi hdim h,
      unramified_relativeSingularIdeal_of_hasAtWorstNodalSingularities k X hequi hdim h⟩,
    fun h => hasAtWorstNodalSingularities_of_isLocalCompleteIntersectionOverField k X hequi hdim
      h.1 h.2⟩

end Stacks.Curves

end
