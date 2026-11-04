module

public import StacksFrontier.AlgebraicGeometry.BirationalCurveFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Dimension
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.IntersectionNodes
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.AutomaticProperties
public import StacksCore.Tactic.StacksAttribute

/-!
# The intersection of a rational bridge with the closure of its complement

Let `k` be a field, let `X` be a proper scheme over `k` of dimension one with
`H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities, and let `C ⊆ X` be a rational bridge
(Tag 0E3M). Write `X'` for the scheme-theoretic closure of `X \ C`.

This file proves the assertions of [Stacks, Tag 0E3M] that `k' = Γ(C, 𝒪_C)` is a field and that
the points of `C ∩ X'` are nodes of `X`, and derives from the latter that `C ∩ X'` is a finite
discrete set of closed points — the form in which the construction of the contraction uses it.

## Main results

* `Stacks.Curves.isField_globalSections_bridge` — `k'` is a field.
* `Stacks.Curves.isNode_of_mem_intersection_bridge` — every point of `C ∩ X'` is a node of `X`.
* `Stacks.Curves.finite_intersectionWithComplementaryCurve_bridge` — `C ∩ X'` is finite.

## Implementation notes

The ambient curve is equidimensional by
`AlgebraicGeometry.equidimensional_of_isIso_globalSections_of_dimension_one`, which is what the
hypotheses `topologicalKrullDim X = 1` and `H⁰(X, 𝒪_X) = k` of the source give; and it is reduced
by `Stacks.Curves.isReduced_of_hasAtWorstNodalSingularities`. The bridge is integral, hence
reduced and irreducible, hence equidimensional, and its support is an irreducible component of
`X`, so it is one-dimensional. Those are the hypotheses under which [Stacks, Tag 0E38] applies to
it, and that tag supplies the assertion that the points of the intersection are nodes of `X`.

A node is a closed point, so the intersection is a closed set of closed points of a Noetherian
scheme, hence discrete by
`Stacks.AlgebraicGeometry.BirationalCurveFinite.isDiscrete_of_forall_isClosed_singleton`, and
finite because it is also compact, being closed in the proper curve `X`.

That `k'` is a field is the source's appeal to [Stacks, Tag 0BUG]: `C` is integral and proper
over `k`, so `AlgebraicGeometry.isField_of_universallyClosed` applies.

## References

* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
* [Stacks Project, Tag 0BUG](https://stacks.math.columbia.edu/tag/0BUG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- A closed subscheme whose support is an irreducible component of a one-dimensional
equidimensional curve of finite type over a field is itself one-dimensional. -/
theorem topologicalKrullDim_eq_one_of_support_mem_irreducibleComponents
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hXeq : Equidimensional X) (hXdim : topologicalKrullDim X = 1)
    (I : X.IdealSheafData) (hI : (I.support : Set X) ∈ irreducibleComponents X) :
    topologicalKrullDim I.subscheme = 1 :=
  (Stacks.Chow.subschemeHomeoSupport I).isHomeomorph.topologicalKrullDim_eq.trans
    (topologicalKrullDim_irreducibleComponent_eq_one (X ↘ Spec (.of k)) hXeq hXdim _ hI)

/-- **The ring of global functions on a rational bridge is a field**: the bridge is an integral
scheme proper over `k`, so its global functions form a field ([Stacks, Tag 0BUG]). -/
@[stacks 0E3M "k' = H⁰(C, 𝒪_C) is a field"]
theorem isField_globalSections_bridge (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (_hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (_hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalBridge k X C) :
    IsField Γ(C.subscheme, ⊤) :=
  have := hC.isIntegral
  isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))

/-- A rational bridge is a one-dimensional reduced equidimensional closed subscheme of the
ambient curve: it is integral, so reduced and irreducible, and its support is an irreducible
component of a one-dimensional equidimensional curve. -/
theorem isReduced_and_equidimensional_and_dim_bridge
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    IsReduced C.subscheme ∧ Equidimensional C.subscheme ∧
      topologicalKrullDim C.subscheme = 1 := by
  have := hC.isIntegral
  refine ⟨inferInstance, Equidimensional.of_preirreducibleSpace C.subscheme, ?_⟩
  exact topologicalKrullDim_eq_one_of_support_mem_irreducibleComponents (k := k) (X := X)
    (equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hdim) hdim C
    hC.support_mem_irreducibleComponents

/-- **Every point of the intersection of a rational bridge with the closure of its complement is
a node of the ambient curve.**  At least two irreducible components of `X` pass through each
such point, so [Stacks, Tag 0E38] applies. -/
@[stacks 0E3M "the points of C ∩ X' are nodes of X"]
theorem isNode_of_mem_intersection_bridge (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalBridge k X C)
    (w : intersectionWithComplementaryCurve C) :
    IsNode k X ((intersectionWithComplementaryCurveIdeal C).subschemeι.base w) := by
  obtain ⟨_, heq, hdimC⟩ := isReduced_and_equidimensional_and_dim_bridge hdim hC
  exact isNode_of_mem_intersection_complementaryCurve
    (equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hdim) hdim
    hnodal C heq hdimC w

/-- Every point of the support of the intersection of a rational bridge with the closure of its
complement is a closed point of the ambient curve, a node being closed. -/
theorem isClosed_singleton_of_mem_support_intersection_bridge
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) {x : X}
    (hx : x ∈ ((intersectionWithComplementaryCurveIdeal C).support : Set X)) :
    IsClosed ({x} : Set X) := by
  rw [← Scheme.IdealSheafData.range_subschemeι] at hx
  obtain ⟨w, rfl⟩ := hx
  exact (isNode_of_mem_intersection_bridge k X hdim hnodal C hC w).1

/-- **The intersection of a rational bridge with the closure of its complement is finite.**  Its
points are nodes of `X`, hence closed, so it is a closed set of closed points of a Noetherian
scheme and therefore discrete; being closed in the proper curve `X` it is also compact. -/
theorem finite_intersectionWithComplementaryCurve_bridge
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    Finite (intersectionWithComplementaryCurve C) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of k))
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  have hsclosed : IsClosed ((intersectionWithComplementaryCurveIdeal C).support : Set X) :=
    (intersectionWithComplementaryCurveIdeal C).support.isClosed
  have hdisc :=
    Stacks.AlgebraicGeometry.BirationalCurveFinite.isDiscrete_of_forall_isClosed_singleton
      hsclosed
      fun x hx => isClosed_singleton_of_mem_support_intersection_bridge hdim hnodal hC hx
  have : Finite ((intersectionWithComplementaryCurveIdeal C).support : Set X) :=
    hsclosed.isCompact.finite hdisc
  exact Finite.of_equiv _
    (Stacks.Chow.subschemeHomeoSupport (intersectionWithComplementaryCurveIdeal C)).symm.toEquiv

end Stacks.Curves
