module

public import StacksFrontier.AlgebraicGeometry.Curves.GeometricallyReducedCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.NodalGorensteinReduced
public import StacksFrontier.AlgebraicGeometry.Curves.NodalUnramifiedSingularSubscheme
public import StacksFrontier.AlgebraicGeometry.Curves.NodeFittingIdealClosedPoint
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.SeparableTower
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic
public import StacksFrontier.AlgebraicGeometry.NodalContraction.Basic
public import StacksFrontier.AlgebraicGeometry.NodalContraction.GenericFibreField
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Reduced

/-!
# Reducedness of the fibres of an at-worst-nodal relative curve

The fibres of an at-worst-nodal morphism of relative dimension one are geometrically reduced over
the residue fields of their base points, hence reduced. Over a closed point of the base, the
quotient of a local ring of the total space by the stalk of the pulled-back vanishing ideal of
that point is then reduced as well. Finally, at a point of a geometrically reduced scheme over a
field at which the local ring is a field, the residue field of an intermediate scheme of the
structure morphism is geometrically reduced.

## Main results

* `AlgebraicGeometry.geometricallyReduced_fiber_of_nodal`: a nonempty fibre of an at-worst-nodal
  morphism of relative dimension one is geometrically reduced over the residue field of its base
  point.
* `AlgebraicGeometry.isReduced_fiber_of_nodal`: such a fibre is reduced.
* `AlgebraicGeometry.isReduced_quotient_stalk_comap_vanishingIdeal`: if the fibre over a closed
  point of the base is reduced, then every local ring of the total space is reduced modulo the
  stalk of the pullback of the vanishing ideal of that point.
* `AlgebraicGeometry.isGeometricallyReduced_residueField_of_isField_stalk`: for `ν : P ⟶ Y` and
  `g : Y ⟶ Spec k` with `ν ≫ g` geometrically reduced, the residue field of `Y` at `ν x` is
  geometrically reduced over `k` when the local ring of `P` at `x` is a field.

## References

* [Stacks Project, Tag 0CDF](https://stacks.math.columbia.edu/tag/0CDF)
* [Stacks Project, Tag 0C59](https://stacks.math.columbia.edu/tag/0C59)
* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C4E](https://stacks.math.columbia.edu/tag/0C4E)
* [Stacks Project, Tag 0E37](https://stacks.math.columbia.edu/tag/0E37)
* [Stacks Project, Tag 02G8](https://stacks.math.columbia.edu/tag/02G8)
* [Stacks Project, Tag 030O](https://stacks.math.columbia.edu/tag/030O)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The structure map of the residue field of `Spec k` at a point is surjective. -/
private theorem surjective_algebraMap_spec_residueField (k : Type u) [Field k]
    (x : Spec (CommRingCat.of k)) :
    letI : Algebra k ((Spec (CommRingCat.of k)).residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation x).hom.toAlgebra
    Function.Surjective (algebraMap k ((Spec (CommRingCat.of k)).residueField x)) := by
  let : Algebra k ((Spec (CommRingCat.of k)).residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation x).hom.toAlgebra
  let q := x.asIdeal
  let e := Scheme.Spec.residueFieldIso (.of k) x
  have : q.IsPrime := x.isPrime
  have : q.IsMaximal := by
    change x.asIdeal.IsMaximal
    rw [x.asIdeal.eq_bot_of_prime]
    exact Ideal.bot_isMaximal
  have key : (algebraMap k ((Spec (CommRingCat.of k)).residueField x)) =
      e.inv.hom.comp (algebraMap k q.ResidueField) := by
    rw [RingHom.algebraMap_toAlgebra]
    simpa [e, Scheme.Γevaluation, Scheme.evaluation, RingHom.comp_assoc] using
      (congrArg CommRingCat.Hom.hom
        (Scheme.Spec.algebraMap_residueFieldIso_inv (.of k) x)).symm
  rw [key]
  exact (ConcreteCategory.bijective_of_isIso e.inv).2.comp
    q.algebraMap_residueField_surjective

/-- Separability of the residue field extension at a point of a scheme over a field `k`, stated
over the residue field of the image point of `Spec k`, implies separability over `k` itself. -/
private theorem isSeparableExtension_residueField_of_isSeparable (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) (x : X)
    (h : letI : Algebra ((Spec (CommRingCat.of k)).residueField (f.base x)) (X.residueField x) :=
          (f.residueFieldMap x).hom.toAlgebra
        Algebra.IsSeparable ((Spec (CommRingCat.of k)).residueField (f.base x))
          (X.residueField x)) :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    Algebra.IsSeparableExtension k (X.residueField x) := by
  let : Algebra k ((Spec (CommRingCat.of k)).residueField (f.base x)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation (f.base x)).hom.toAlgebra
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let : Algebra ((Spec (CommRingCat.of k)).residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let : IsScalarTower k ((Spec (CommRingCat.of k)).residueField (f.base x))
      (X.residueField x) := residueField_isScalarTower k f x
  let : Algebra.IsSeparable ((Spec (CommRingCat.of k)).residueField (f.base x))
      (X.residueField x) := h
  have : Algebra.IsSeparableExtension k k := Algebra.IsSeparableExtension.of_isSeparable k k
  have : Algebra.IsSeparableExtension k
      ((Spec (CommRingCat.of k)).residueField (f.base x)) :=
    Algebra.IsSeparableExtension.of_algEquiv
      (AlgEquiv.ofBijective (Algebra.ofId k ((Spec (CommRingCat.of k)).residueField (f.base x)))
        ⟨(algebraMap k ((Spec (CommRingCat.of k)).residueField (f.base x))).injective,
          surjective_algebraMap_spec_residueField k (f.base x)⟩)
  exact Algebra.IsSeparableExtension.trans_of_isSeparable k
    ((Spec (CommRingCat.of k)).residueField (f.base x)) (X.residueField x)

/-- **Condition (2) of Tag 0C4E gives at-worst-nodal singularities.** A locally algebraic scheme
over a field, equidimensional of dimension one, which is a local complete intersection over that
field and whose relative singular subscheme is unramified over it, has at-worst-nodal
singularities. This combines Tag 0C4E with the equivalences of Tag 0C4D. -/
private theorem hasAtWorstNodalSingularities_of_lci_of_unramified (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (hlci : IsLocalCompleteIntersectionOverField (X ↘ Spec (CommRingCat.of k)))
    (hZ : Unramified ((relativeSingularIdeal (X ↘ Spec (CommRingCat.of k))).subschemeι ≫
      (X ↘ Spec (CommRingCat.of k)))) :
    Stacks.Curves.HasAtWorstNodalSingularities k X := by
  intro x hx
  rcases Stacks.Curves.smoothAt_or_isSeparable_and_depth_eq_one_and_fittingIdeal_eq_maximalIdeal
      k (X ↘ Spec (CommRingCat.of k)) hequi hdim hlci hZ x hx with hsm | ⟨hsep, -, hdepth, hfit⟩
  · exact Or.inl hsm
  · refine Or.inr (((Stacks.Curves.isNode_tfae_of_isClosed k X hdim x hx).out 5 1).mp ?_)
    refine ⟨?_, hdepth, hfit⟩
    exact isSeparableExtension_residueField_of_isSeparable k (X ↘ Spec (CommRingCat.of k)) x hsep

/-- **Condition (2) of Tag 0C4E gives geometric reducedness.** A locally algebraic scheme over a
field, equidimensional of dimension one, which is a local complete intersection over that field
and whose relative singular subscheme is unramified over it, is geometrically reduced
(Tag 0E37). -/
private theorem geometricallyReduced_of_lci_of_unramified (k : Type u) [Field k]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g]
    (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (hlci : IsLocalCompleteIntersectionOverField g)
    (hZ : Unramified ((relativeSingularIdeal g).subschemeι ≫ g)) :
    GeometricallyReduced g := by
  let : X.Over (Spec (CommRingCat.of k)) := ⟨g⟩
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType g)
  exact Stacks.Curves.geometricallyReduced_of_hasAtWorstNodalSingularities k X hequi hdim
    (hasAtWorstNodalSingularities_of_lci_of_unramified k X hequi hdim hlci hZ)

/-- **The fibres of an at-worst-nodal morphism of relative dimension one are geometrically
reduced.** A nonempty fibre of such a morphism is geometrically reduced over the residue field of
its base point (Tag 0E37). -/
public theorem geometricallyReduced_fiber_of_nodal {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) (s : S) (hs : Nonempty (f.fiber s)) :
    GeometricallyReduced (f.fiberToSpecResidueField s) := by
  obtain ⟨-, hlfp, hrd, hfib⟩ := (isAtWorstNodalOfRelativeDimensionOne_iff_fibres f).mp hf
  let : LocallyOfFinitePresentation f := hlfp
  have : LocallyOfFiniteType f := inferInstance
  have : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    locallyOfFiniteType_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (S.fromSpecResidueField s)) inferInstance
  obtain ⟨hequi, hdim⟩ := hrd s hs
  obtain ⟨hlci, hZ⟩ := hfib s
  exact geometricallyReduced_of_lci_of_unramified (S.residueField s)
    (f.fiberToSpecResidueField s) hequi hdim hlci hZ

/-- **A nonempty fibre of an at-worst-nodal morphism of relative dimension one is reduced.** -/
public theorem isReduced_fiber_of_nodal {X S : Scheme.{u}} (f : X ⟶ S)
    (hf : IsAtWorstNodalOfRelativeDimensionOne f) (s : S) (hs : Nonempty (f.fiber s)) :
    IsReduced (f.fiber s) :=
  have : GeometricallyReduced (f.fiberToSpecResidueField s) :=
    geometricallyReduced_fiber_of_nodal f hf s hs
  isReduced_of_geometricallyReduced (k := S.residueField s) (f.fiberToSpecResidueField s)

/-- The closed subscheme cut out by the pullback of the vanishing ideal of a closed point is
reduced when the scheme-theoretic fibre over that point is. -/
private theorem isReduced_comap_closed_point_of_isReduced_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (hs : IsClosed ({s} : Set S)) [IsReduced (f.fiber s)] :
    IsReduced ((Scheme.IdealSheafData.vanishingIdeal
      (⟨{s}, hs⟩ : Closeds S)).comap f).subscheme :=
  ObjectProperty.prop_of_iso IsReduced
    (exists_fiberIso_subscheme_comap_vanishingIdeal f s hs).choose inferInstance

/-- The quotient of a local ring of a scheme by the stalk of an ideal sheaf whose closed
subscheme is reduced is reduced. -/
private theorem isReduced_quotient_idealStalk {X : Scheme.{u}} (I : X.IdealSheafData)
    [IsReduced I.subscheme] (x : X) :
    _root_.IsReduced ((X.presheaf.stalk x) ⧸ IdealSheafData.stalk I x) := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  let U' : X.affineOpens := ⟨U, hU⟩
  let e := (I.subschemeObjIso U').symm.commRingCatIsoToRingEquiv
  have : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U') := isReduced_of_injective e e.injective
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  rw [IdealSheafData.stalk_eq_map_germ I x U' hxU]
  change _root_.IsReduced ((X.presheaf.stalk x) ⧸
    (I.ideal U').map (algebraMap Γ(X, U) (X.presheaf.stalk x)))
  exact isReduced_localizationPreserves
    (Algebra.algebraMapSubmonoid (Γ(X, U) ⧸ I.ideal U')
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl) _ inferInstance

/-- **The local rings of a scheme-theoretic fibre over a closed point are reduced when that
fibre is**, read as quotients of the local rings of the total space by the stalk of the pullback
of the vanishing ideal of the point. -/
public theorem isReduced_quotient_stalk_comap_vanishingIdeal
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (hs : IsClosed ({s} : Set S))
    [IsReduced (f.fiber s)] (d : X) :
    _root_.IsReduced (X.presheaf.stalk d ⧸
      IdealSheafData.stalk ((Scheme.IdealSheafData.vanishingIdeal
        (⟨{s}, hs⟩ : TopologicalSpace.Closeds S)).comap f) d) :=
  have := isReduced_comap_closed_point_of_isReduced_fiber f s hs
  isReduced_quotient_idealStalk _ d

/-- **The residue field at a point of a geometrically reduced scheme over a field whose local
ring there is a field is geometrically reduced**, read on the intermediate scheme of a
factorization of the structure morphism. For `ν : P ⟶ Y` and `g : Y ⟶ Spec k` with `ν ≫ g`
geometrically reduced, if the local ring of `P` at `x` is a field then the residue field of `Y`
at `ν x` is geometrically reduced over `k`. -/
public theorem isGeometricallyReduced_residueField_of_isField_stalk
    {k : Type u} [Field k] {P Y : Scheme.{u}}
    (ν : P ⟶ Y) (g : Y ⟶ Spec (CommRingCat.of k))
    [GeometricallyReduced (ν ≫ g)] (x : P) (hx : IsField (P.presheaf.stalk x)) :
    letI : Algebra k ((Spec (CommRingCat.of k)).presheaf.stalk (g (ν x))) :=
      StructureSheaf.stalkAlgebra k (g (ν x))
    letI : Algebra k (Y.presheaf.stalk (ν x)) :=
      ((g.stalkMap (ν x)).hom.comp
        (algebraMap k ((Spec (CommRingCat.of k)).presheaf.stalk (g (ν x))))).toAlgebra
    Algebra.IsGeometricallyReduced k
      (IsLocalRing.ResidueField (Y.presheaf.stalk (ν x))) := by
  let : Algebra k ((Spec (CommRingCat.of k)).presheaf.stalk (g (ν x))) :=
    StructureSheaf.stalkAlgebra k (g (ν x))
  let : Algebra k (Y.presheaf.stalk (ν x)) :=
    ((g.stalkMap (ν x)).hom.comp
      (algebraMap k ((Spec (CommRingCat.of k)).presheaf.stalk (g (ν x))))).toAlgebra
  let : Algebra k (P.presheaf.stalk x) :=
    (((ν ≫ g).stalkMap x).hom.comp
      (algebraMap k ((Spec (CommRingCat.of k)).presheaf.stalk (g (ν x))))).toAlgebra
  have : Algebra.IsGeometricallyReduced k (P.presheaf.stalk x) :=
    (isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk (ν ≫ g) x).mp
      ((geometricallyReduced_iff_forall_isGeometricallyReducedAt _).mp inferInstance x)
  let : Field (P.presheaf.stalk x) := hx.toField
  let e : P.presheaf.stalk x ≃ₐ[k] IsLocalRing.ResidueField (P.presheaf.stalk x) :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom k (P.presheaf.stalk x)
      (IsLocalRing.ResidueField (P.presheaf.stalk x)))
      ⟨(IsLocalRing.residue (P.presheaf.stalk x)).injective, IsLocalRing.residue_surjective⟩
  have : Algebra.IsGeometricallyReduced k (IsLocalRing.ResidueField (P.presheaf.stalk x)) :=
    Algebra.IsGeometricallyReduced.of_injective e.symm.toAlgHom e.symm.injective
  let φ : Y.presheaf.stalk (ν x) →ₐ[k] P.presheaf.stalk x :=
    { (ν.stalkMap x).hom with
      commutes' := by
        intro a
        change (ν.stalkMap x).hom ((g.stalkMap (ν x)).hom _) =
          ((ν ≫ g).stalkMap x).hom _
        rw [Scheme.Hom.stalkMap_comp]
        rfl }
  have : IsLocalHom φ := ⟨fun a ha => (isUnit_map_iff (ν.stalkMap x).hom a).mp ha⟩
  exact Algebra.IsGeometricallyReduced.of_injective (IsLocalRing.ResidueField.mapAlgHom φ)
    (IsLocalRing.ResidueField.mapAlgHom φ).injective

end AlgebraicGeometry

end
