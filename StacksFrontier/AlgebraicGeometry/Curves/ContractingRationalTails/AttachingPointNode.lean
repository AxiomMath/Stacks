module

public import Mathlib.RingTheory.Jacobson.Ring
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionNodes
public import StacksFrontier.AlgebraicGeometry.Curves.NodeResidueFieldSeparable
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.AutomaticProperties
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint

/-!
# The attaching point of a rational tail is a node

**Stacks 0E3H.** The intersection point of a rational tail `C` with the closure `X'` of its
complement is a node of `X`, and the extension `κ(x)'/κ(x)` of residue fields at that point is
finite separable.

The rational tail `C` is, by definition, an irreducible component of `X` meeting the rest of
`X` in a single reduced point `x` (`Stacks.Curves.IsRationalTail.attachingPoint`); this is
exactly the geometric situation of Tag 0E38, which identifies every point where two
one-dimensional irreducible components of an equidimensional at-worst-nodal curve cross as a
node. The finiteness and separability of `κ(x)'/κ(x)` is Tag 0C4D, applied at the same point.

## Main results

* `Stacks.Curves.isNode_attachingPoint` — the attaching point of a rational tail is a node.
* `Stacks.Curves.isFiniteSeparable_residueField_attachingPoint` — the residue field extension
  at the attaching point of a rational tail is finite and separable.

## References

* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Curves

/-- **Stacks 0E3H.** The attaching point of a rational tail — where it meets the closure of
its complement — is a node of the ambient curve. -/
@[stacks 0E3H "attaching_point_is_node"]
theorem isNode_attachingPoint
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C) :
    IsNode k X (C.subschemeι hC.attachingPoint) := by
  have hXeq : TopologicalSpace.Equidimensional X :=
    equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hdim
  have : IsIntegral C.subscheme := hC.isIntegral
  have hYeq : TopologicalSpace.Equidimensional C.subscheme :=
    TopologicalSpace.Equidimensional.of_preirreducibleSpace C.subscheme
  have hYdim : topologicalKrullDim C.subscheme = 1 := by
    have hCrange : (Set.range C.subschemeι : Set X) = (C.support : Set X) := C.range_subschemeι
    have hCW : topologicalKrullDim (C.support : Set X) = topologicalKrullDim C.subscheme :=
      (IsHomeomorph.topologicalKrullDim_eq _
        (C.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph.trans
          (Homeomorph.setCongr hCrange)).isHomeomorph).symm
    have hCdim := topologicalKrullDim_irreducibleComponent_eq_one (X ↘ Spec (.of k)) hXeq hdim
      (C.support : Set X) hC.support_mem_irreducibleComponents
    exact hCW.symm.trans hCdim
  have hnode_all := isNode_of_mem_intersection_complementaryCurve hXeq hdim hnodal C hYeq hYdim
  have heq : intersectionWithComplementaryCurveIdeal C =
      Scheme.IdealSheafData.vanishingIdeal
        ⟨{C.subschemeι hC.attachingPoint}, hC.attachingPoint_isClosed⟩ :=
    hC.intersectionWithComplementaryCurveIdeal_eq
  have hx₀mem : C.subschemeι hC.attachingPoint ∈ (Scheme.IdealSheafData.vanishingIdeal
      (⟨{C.subschemeι hC.attachingPoint}, hC.attachingPoint_isClosed⟩ :
        TopologicalSpace.Closeds X)).support :=
    rfl
  have hx₀mem' : C.subschemeι hC.attachingPoint ∈
      (intersectionWithComplementaryCurveIdeal C).support := by
    rw [heq]; exact hx₀mem
  have hx₀mem'' : C.subschemeι hC.attachingPoint ∈
      (↑(intersectionWithComplementaryCurveIdeal C).support : Set X) := hx₀mem'
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : (intersectionWithComplementaryCurveIdeal C).subscheme,
      (intersectionWithComplementaryCurveIdeal C).subschemeι.base y₀ =
        C.subschemeι hC.attachingPoint := by
    rwa [← Scheme.IdealSheafData.range_subschemeι] at hx₀mem''
  have hnode : IsNode k X
      ((intersectionWithComplementaryCurveIdeal C).subschemeι.base y₀) := hnode_all y₀
  rwa [hy₀] at hnode

/-- **Stacks 0E3H.** At the attaching point of a rational tail, the extension of the residue
field by the residue field of the node (in the sense of `Stacks.Curves.IsNode`) is finite and
separable. -/
@[stacks 0E3H "finite_separable_residue_field"]
theorem isFiniteSeparable_residueField_attachingPoint
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C) :
    let x := C.subschemeι hC.attachingPoint
    let kToStalk : k →+* X.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom
    letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
    letI : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
    Module.Finite k (X.residueField x) ∧ Algebra.IsSeparableExtension k (X.residueField x) := by
  intro x kToStalk
  let : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
  let : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
  have hnode : IsNode k X x := isNode_attachingPoint k X hdim hnodal C hC
  have hsep : Algebra.IsSeparableExtension k (X.residueField x) :=
    isSeparableExtension_residueField_of_isNode k X hdim x hnode
  refine ⟨?_, hsep⟩
  let f : X ⟶ Spec (.of k) := X ↘ Spec (.of k)
  have hxclosed : IsClosed ({x} : Set X) := hnode.1
  have : LocallyOfFiniteType (X.fromSpecResidueField x) := by
    have := isClosed_singleton_iff_isClosedImmersion.mp hxclosed; infer_instance
  have hcomp : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := inferInstance
  rw [← f.SpecMap_residueFieldMap_fromSpecResidueField x] at hcomp
  simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, Spec.map_comp] at hcomp
  simp only [← Spec.map_comp] at hcomp
  change LocallyOfFiniteType (Spec.map _) at hcomp
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hcomp
  have : Algebra.FiniteType k (X.residueField x) := by
    show RingHom.FiniteType (algebraMap k (X.residueField x))
    convert hcomp using 1
    · rfl
    · simp only [RingHom.algebraMap_toAlgebra]
      show ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom = _
      rw [← Scheme.Γevaluation_naturality]
      simp only [Scheme.Γevaluation, Scheme.evaluation, Category.assoc]
  exact finite_of_finite_type_of_isJacobsonRing _ _

end Stacks.Curves

end
