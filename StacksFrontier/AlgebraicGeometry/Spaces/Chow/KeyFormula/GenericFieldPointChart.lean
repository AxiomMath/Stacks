module

public import StacksFrontier.AlgebraicGeometry.Spaces.DenseOpenSchemeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericRationalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicPullbackWeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom

/-!
# Étale charts receiving the generic point of an integral algebraic space

Let `F` be an integral algebraic space over a scheme `S` and let `p : Spec k → F` be a
*monomorphic* field-valued representative of its generic point `η`.  This file produces, inside
every dense open subspace `D ⊆ F`, an **affine** étale chart `V → F` factoring through `D`
through which `p` factors, and records that pullbacks of meromorphic functions are defined
along `p`.  Together these are what reading a meromorphic object of `F` at its generic point
needs: the chart diagrams `(Spec k, V)` over `p` are the squares along which the global pullback
of meromorphic sections of Stacks 0ENC is computed, and the freedom to put `V` inside a given
dense open is what lets the coordinate of a rational function be read on `V`.

The chart is the one of Stacks 0BBP.  The morphism `p` factors through `D` by Stacks 03IE,
`D` is decent, so its point under `η` has an affine elementary étale neighbourhood `(E, e)`
(Stacks 0BBP); the residue-field point of `(E, e)` and the factorization of `p` are two
monomorphic representatives of one point of `D`, hence isomorphic (Stacks 0H2X), which gives the
morphism from `Spec k` into `E`.

## Main definitions

* `AlgebraicGeometry.Space.genericFieldPointChartDiagram` is the chart diagram `(Spec k, V)`
  over `p` attached to a factorization of `p` through an étale chart `V`.

## Main results

* `AlgebraicGeometry.Space.exists_affine_etaleChart_factor_of_isDenseOpenSubspace`: inside every
  dense open subspace there is an affine étale chart through which `p` factors.
* `AlgebraicGeometry.Space.pullbacksMeromorphicSections_fieldMorphism_of_class_eq_genericPoint`:
  pullbacks of meromorphic functions are defined along any field-valued representative of the
  generic point, by Stacks 0EN9, part (1).

## References

* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0H2X](https://stacks.math.columbia.edu/tag/0H2X)
* [Stacks Project, Tag 03IE](https://stacks.math.columbia.edu/tag/03IE)
* [Stacks Project, Tag 0EN9](https://stacks.math.columbia.edu/tag/0EN9)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (hFint : IsIntegralSpace B S hS F) (p : FieldValuedPoint B S hS F)

/-- **Inside every dense open subspace there is an affine étale chart receiving a monomorphic
representative of the generic point.**  For a monomorphic field-valued representative `p` of the
generic point of an integral algebraic space and a dense open subspace `D`, there is an affine
étale chart `V` whose structure morphism factors through `D` and a morphism from the field
spectrum of `p` into `V` over the space. -/
theorem exists_affine_etaleChart_factor_of_isDenseOpenSubspace
    (hp : p.class B S hS F = genericPoint B S hS hF hFint)
    (hmono : Mono (fieldMorphism B S hS F p)) {D : Subfunctor F}
    (hD : IsDenseOpenSubspace B S hS hF D) :
    ∃ (V : SmallEtale B S hS F) (τ : yoneda.obj V.obj.left ⟶ D.toFunctor)
      (g : p.siteObject B S hS F ⟶ V.obj.left),
      IsAffine ((BigFppfOver.toScheme B S hS).obj V.obj.left) ∧ τ ≫ D.ι = V.1.hom ∧
        yoneda.map g ≫ V.1.hom = fieldMorphism B S hS F p := by
  obtain ⟨j, hj⟩ := exists_genericLift B S hS hF hFint p hp hD
  have hDalg : IsAlgebraicSpace B S hS D.toFunctor := hD.1.1
  have hdecD := isDecentSpace_of_isOpenSubspace B S hS hF hFint.2.1 hD.1
  let pD : FieldValuedPoint B S hS D.toFunctor :=
    ⟨p.carrier, p.contained, p.toBase, yonedaEquiv j⟩
  have hpD : fieldMorphism B S hS D.toFunctor pD = j := Equiv.symm_apply_apply _ _
  have : Mono j := by
    have : Mono (j ≫ D.ι) := by rwa [hj]
    exact mono_of_mono j D.ι
  obtain ⟨E, hEaff, -, -⟩ := exists_affine_elementaryEtaleNeighborhood' B S hS hDalg hdecD
    (pD.class B S hS D.toFunctor)
  have := ElementaryEtaleNeighborhood.mono_neighborhoodFieldPoint B S hS D.toFunctor hDalg _ E
  have : Mono (yonedaEquiv.symm pD.value) := by
    change Mono (fieldMorphism B S hS D.toFunctor pD)
    rw [hpD]
    infer_instance
  obtain ⟨e, he⟩ := iso_of_mono_of_point_eq B S hS D.toFunctor hDalg
    (neighborhoodFieldPoint B S hS D.toFunctor hDalg _ E) pD
    (neighborhoodFieldPoint_class B S hS _ hDalg _ E)
  have hrel : yoneda.map e.hom ≫ fieldMorphism B S hS D.toFunctor pD =
      fieldMorphism B S hS D.toFunctor (neighborhoodFieldPoint B S hS D.toFunctor hDalg _ E) := by
    change yoneda.map e.hom ≫ yonedaEquiv.symm pD.value = yonedaEquiv.symm _
    rw [yonedaEquiv_symm_naturality_left e.hom D.toFunctor pD.value, he]
  let r : (neighborhoodFieldPoint B S hS D.toFunctor hDalg _ E).siteObject B S hS D.toFunctor ⟶
      E.scheme := residueFieldMap B S hS E.scheme E.point E.residueField_contained
  have h1 : yoneda.map r ≫ E.toSpace = yoneda.map e.hom ≫ j := by
    rw [← hpD, hrel]
    exact (neighborhoodFieldPoint_morphism B S hS _ hDalg _ E).symm
  refine ⟨⟨CostructuredArrow.mk (E.toSpace ≫ D.ι), ?_⟩, E.toSpace, e.inv ≫ r, hEaff, rfl, ?_⟩
  · exact (isEtale_iff_presheaf_of_yoneda B S hS _).1
      (isEtale_comp B S hS E.etale_toSpace (isEtale_of_isOpenImmersion B S hS hD.1.2))
  · change yoneda.map (e.inv ≫ r) ≫ E.toSpace ≫ D.ι = _
    rw [yoneda.map_comp, Category.assoc, ← Category.assoc (yoneda.map r), h1, Category.assoc,
      ← Category.assoc (yoneda.map e.inv), ← yoneda.map_comp, e.inv_hom_id, yoneda.map_id,
      Category.id_comp, hj]

/-- **The chart diagram `(Spec k, V)` over a field-valued point `p`** attached to a factorization
`g` of `p` through an étale chart `V`: the source chart is the identity chart of the field
spectrum. -/
def genericFieldPointChartDiagram (V : SmallEtale B S hS F)
    (g : p.siteObject B S hS F ⟶ V.obj.left)
    (hg : yoneda.map g ≫ V.1.hom = fieldMorphism B S hS F p) :
    ChartDiagram B S hS (yoneda.obj (p.siteObject B S hS F)) F (fieldMorphism B S hS F p) where
  U := idEtaleChart B S hS (p.siteObject B S hS F)
  V := V
  g := g
  comm := by
    change 𝟙 _ ≫ fieldMorphism B S hS F p = _
    rw [Category.id_comp]
    exact hg.symm

/-- The identity chart of the field spectrum of a field-valued point is affine. -/
theorem isAffine_idEtaleChart_siteObject :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS (yoneda.obj (p.siteObject B S hS F))).obj
        (idEtaleChart B S hS (p.siteObject B S hS F)))) :=
  inferInstanceAs (IsAffine (Spec (CommRingCat.of p.carrier)))

/-- **Stacks 0EN9, part (1), along a representative of the generic point.** Pullbacks of
meromorphic functions are defined along the morphism presented by any field-valued
representative of the generic point of an integral algebraic space: every point of the field
spectrum maps to the generic point, which has codimension `0`. -/
theorem pullbacksMeromorphicSections_fieldMorphism_of_class_eq_genericPoint
    (hp : p.class B S hS F = genericPoint B S hS hF hFint) :
    PullbacksMeromorphicSections B S hS (fieldMorphism B S hS F p) := by
  have hgen : genericPoint B S hS hF hFint ∈ genericPoints (points B S hS F) := by
    have : IrreducibleSpace (points B S hS F) := hFint.2.2
    change closure {genericPoint B S hS hF hFint} ∈ irreducibleComponents (points B S hS F)
    rw [isGenericPoint_genericPoint B S hS hF hFint, irreducibleComponents_eq_singleton]
    exact rfl
  have hdim := (mem_genericPoints_iff_localRingDimension_eq_zero B S hS hF hFint.2.1 _).1 hgen
  exact pullbacksMeromorphicSections_of_mapsTo_codimensionZero B S hS
    (X := ⟨yoneda.obj (p.siteObject B S hS F), isAlgebraicSpace_yoneda B S hS _⟩)
    (Y := ⟨F, hF⟩) (fieldMorphism B S hS F p) fun x _ => by
      rw [FieldValuedPoint.pointsMap_eq_class, hp]
      exact hdim

end AlgebraicGeometry.Space

end
