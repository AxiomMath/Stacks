module

public import StacksFrontier.AlgebraicGeometry.Curves.CanonicalContraction.ContractedCurve
public import StacksFrontier.AlgebraicGeometry.Curves.NodeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothAtPoint

/-!
# The contracted curve is at worst nodal away from the attaching point

Let `k` be a field, let `X` be a proper one-dimensional scheme over `k` with at-worst-nodal
singularities and only constant global functions, let `C ⊆ X` be a rational tail and let `X'` be
the scheme-theoretic closure of the complement of `C`. Away from the point at which `C` is
attached, `X'` agrees with `X` as a scheme over `k`, so every closed point of `X'` outside the
attaching locus is again smooth over `k` or a node.

## Main results

* `Stacks.Curves.smoothAt_or_isNode_of_etale_of_comm` — the dichotomy "smooth over `k` or a
  node" transports between two schemes over `k` receiving étale morphisms from a common source
  over `k`.
* `Stacks.Curves.smoothAt_or_isNode_complementaryCurve_of_notMem_support` — a closed point of
  `X'` whose image in `X` lies outside `C` is smooth over `k` or a node.
* `Stacks.Curves.base_eq_attachingPoint_of_mem_support` — a point of `X'` whose image in `X`
  lies on `C` is the attaching point: the two closed subschemes meet only there.
* `Stacks.Curves.exists_base_eq_attachingPoint` — and the attaching point is the image of a
  point of `X'`.
* `Stacks.Curves.hasAtWorstNodalSingularities_complementaryCurve_of_attachingPoint` — the
  at-worst-nodal clause of Tag 0E3H for `X'`, reduced to the single attaching point.

## Implementation notes

The two disjuncts of `Stacks.Curves.HasAtWorstNodalSingularities` travel for different reasons.
Being a node is étale-local by `Stacks.Curves.isNode_iff_of_etale`, which is Tag 0C57; being a
point of smoothness is étale-local by
`InfinitesimalLifting.smoothAt_comp_iff_of_etale`. Both are used in the same shape: a scheme `U`
over `k` with two étale morphisms `a : U ⟶ X` and `b : U ⟶ X'` whose composites with the two
structure morphisms agree, and a point `u` of `U`. That shape is isolated in
`Stacks.Curves.smoothAt_or_isNode_of_etale_of_comm`, where the structure morphisms are passed
explicitly, so that the `AlgebraicGeometry.Scheme.Over` instances the node predicate reads off
are the intended ones rather than whatever instance search finds.

For the contracted curve the shape is supplied by `Stacks.Curves.tailComplementIso`: the open
complement `U` of `C` in `X` is identified with the open complement `V` of the attaching locus
in `X'`, compatibly with the inclusions of both into `X`. The two étale morphisms are the
inclusion `U ⟶ X` and the composite of that identification with the inclusion `V ⟶ X'`, and
`Stacks.Curves.tailComplementIso_hom_ι` is exactly the compatibility the transport needs.

The étale transport says nothing at the attaching point itself, where the assertion of Tag 0E3H
is the stronger one that `X'` is *smooth*: a node of `X` is replaced by a single branch of
itself, and recognizing that branch as smooth asks for the local ring of `X'` at that point to
be identified. That is done in
`StacksFrontier.AlgebraicGeometry.Curves.CanonicalContraction.SmoothAtAttaching`, ring-theoretically
rather than through clause (2)(c) of Tag 0E38: the local ring of `X'` there is the quotient of
the local ring of `X` by one of its two minimal primes, and such a quotient is a discrete
valuation ring.

The locus over which the at-worst-nodal clause quantifies is therefore cut down here to the one
point this file does not cover.
`Stacks.Curves.base_eq_attachingPoint_of_mem_support` is what effects the reduction — a point of
`X'` over `C` lies in the scheme-theoretic intersection of the two, which for a rational tail is
the single reduced attaching point — and
`Stacks.Curves.hasAtWorstNodalSingularities_complementaryCurve_of_attachingPoint` then states
the clause with that one point as its hypothesis.

## References

* [Stacks Project, Tag 0C57](https://stacks.math.columbia.edu/tag/0C57)
* [Stacks Project, Tag 0E38](https://stacks.math.columbia.edu/tag/0E38)
* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.Curves

/-- Being a node reads the structure morphism of its scheme off the ambient instance, and so
depends on that instance only through the morphism it carries. -/
private theorem isNode_congr {k : Type u} [Field k] {Y : Scheme.{u}}
    {p q : Y ⟶ Spec (.of k)} (hpq : p = q) (y : Y) :
    @IsNode k _ Y ⟨p⟩ y ↔ @IsNode k _ Y ⟨q⟩ y := by
  subst hpq
  exact Iff.rfl

/-- **The dichotomy "smooth over the base field or a node" is étale-local.** Let `X` and `X'` be
schemes over `k`, both of dimension one and locally of finite type, and let `a : U ⟶ X` and
`b : U ⟶ X'` be étale morphisms from a common source whose composites with the two structure
morphisms agree. If `X` is smooth over `k` at `a u` or has a node there, then `X'` is smooth
over `k` at `b u` or has a node there. -/
theorem smoothAt_or_isNode_of_etale_of_comm
    (k : Type u) [Field k] {X X' U : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (p : X' ⟶ Spec (.of k)) [LocallyOfFiniteType p]
    (hdim : topologicalKrullDim X = 1) (hdim' : topologicalKrullDim X' = 1)
    (a : U ⟶ X) [Etale a] (b : U ⟶ X') [Etale b]
    (hcomm : b ≫ p = a ≫ f) (u : U)
    (h : InfinitesimalLifting.SmoothAt f (a.base u) ∨ @IsNode k _ X ⟨f⟩ (a.base u)) :
    InfinitesimalLifting.SmoothAt p (b.base u) ∨ @IsNode k _ X' ⟨p⟩ (b.base u) := by
  rcases h with hsm | hnd
  · refine Or.inl ?_
    have h1 : InfinitesimalLifting.SmoothAt (a ≫ f) u :=
      InfinitesimalLifting.smoothAt_comp_of_etale a f u hsm
    rw [← hcomm] at h1
    exact (InfinitesimalLifting.smoothAt_comp_iff_of_etale b p u).1 h1
  · refine Or.inr ?_
    have h1 : @IsNode k _ U ⟨a ≫ f⟩ u := (isNode_iff_of_etale k X U f hdim a u).1 hnd
    have h2 : @IsNode k _ U ⟨b ≫ p⟩ u := (isNode_congr hcomm.symm u).1 h1
    exact (isNode_iff_of_etale k X' U p hdim' b u).2 h2

/-- **Stacks 0E3H, the at-worst-nodal singularities of `X'` away from the attaching point.** Let
`X` be a proper one-dimensional scheme over a field `k` with at-worst-nodal singularities and
only constant global functions, let `C ⊆ X` be a rational tail and let `X'` be the
scheme-theoretic closure of the complement of `C`. Every closed point of `X'` whose image in `X`
lies outside `C` is smooth over `k` or is a node of `X'`. -/
@[stacks 0E3H "at_worst_nodal_away_from_the_attaching_point"]
theorem smoothAt_or_isNode_complementaryCurve_of_notMem_support
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C)
    (y : complementaryCurve C) (hyc : IsClosed ({y} : Set (complementaryCurve C)))
    (hy : (complementaryCurveι C).base y ∈ (C.support.compl : X.Opens)) :
    letI : (complementaryCurve C).Over (Spec (.of k)) :=
      ⟨complementaryCurveι C ≫ (X ↘ Spec (.of k))⟩
    InfinitesimalLifting.SmoothAt (complementaryCurveι C ≫ (X ↘ Spec (.of k))) y ∨
      IsNode k (complementaryCurve C) y := by
  have hdim' : topologicalKrullDim (complementaryCurve C) = 1 :=
    topologicalKrullDim_complementaryCurve k X hdim C hC
  -- `y` as a point of the complement of the attaching locus in `X'`
  have hyV : y ∈ (complementaryCurveι C) ⁻¹ᵁ (C.support.compl : X.Opens) := hy
  -- the identification of the two open subschemes, read as an equality of morphisms to `X`
  have hιeq : Scheme.Opens.ι ((complementaryCurveι C) ⁻¹ᵁ (C.support.compl : X.Opens)) ≫
        complementaryCurveι C =
      (tailComplementIso k X C).inv ≫ Scheme.Opens.ι (C.support.compl : X.Opens) :=
    (((tailComplementIso k X C).inv_comp_eq).2 (tailComplementIso_hom_ι k X C).symm).symm
  have hcomm : Scheme.Opens.ι ((complementaryCurveι C) ⁻¹ᵁ (C.support.compl : X.Opens)) ≫
        (complementaryCurveι C ≫ (X ↘ Spec (.of k))) =
      ((tailComplementIso k X C).inv ≫ Scheme.Opens.ι (C.support.compl : X.Opens)) ≫
        (X ↘ Spec (.of k)) := by
    rw [← Category.assoc, hιeq]
  have hab : ((tailComplementIso k X C).inv ≫
        Scheme.Opens.ι (C.support.compl : X.Opens)).base ⟨y, hyV⟩ =
      (complementaryCurveι C).base y := by
    rw [← hιeq]
    rfl
  -- the image point in `X` is closed, so `X` is smooth there over `k` or has a node there
  have hxclosed : IsClosed ({(complementaryCurveι C).base y} : Set X) := by
    have h := (complementaryCurveι C).isClosedEmbedding.isClosedMap _ hyc
    rwa [Set.image_singleton] at h
  have hX := hnodal ((complementaryCurveι C).base y) hxclosed
  rw [← hab] at hX
  exact smoothAt_or_isNode_of_etale_of_comm k (X ↘ Spec (.of k))
    (complementaryCurveι C ≫ (X ↘ Spec (.of k))) hdim hdim'
    ((tailComplementIso k X C).inv ≫ Scheme.Opens.ι (C.support.compl : X.Opens))
    (Scheme.Opens.ι ((complementaryCurveι C) ⁻¹ᵁ (C.support.compl : X.Opens)))
    hcomm ⟨y, hyV⟩ hX

/-! ### Reduction of the clause to the attaching point -/

/-- A point of `X` lies on the tail `C` and in the image of the closure `X'` of its complement
exactly when it is the attaching point, since the scheme-theoretic intersection of the two is the
single reduced attaching point. -/
private theorem mem_support_and_mem_range_iff
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {C : X.IdealSheafData} (hC : IsRationalTail k X C) (x : X) :
    (x ∈ (C.support : Set X) ∧ x ∈ Set.range (complementaryCurveι C).base) ↔
      x = C.subschemeι hC.attachingPoint := by
  have h := congrArg (x ∈ ·) (congrArg (fun I : X.IdealSheafData => (I.support : Set X))
    hC.intersectionWithComplementaryCurveIdeal_eq)
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at h
  simp only [intersectionWithComplementaryCurveIdeal, Scheme.IdealSheafData.support_sup,
    TopologicalSpace.Closeds.coe_inf, Set.mem_inter_iff, ← Scheme.IdealSheafData.range_subschemeι,
    eq_iff_iff] at h
  simpa using h

/-- **A point of the closure of the complement of a rational tail that lies on the tail is the
attaching point.** Such a point lies in the scheme-theoretic intersection of `C` with the
closure `X'` of its complement, and for a rational tail that intersection is the single reduced
point at which the tail is attached. -/
theorem base_eq_attachingPoint_of_mem_support
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {C : X.IdealSheafData} (hC : IsRationalTail k X C) (y : complementaryCurve C)
    (hy : (complementaryCurveι C).base y ∈ (C.support : Set X)) :
    (complementaryCurveι C).base y = C.subschemeι hC.attachingPoint :=
  (mem_support_and_mem_range_iff hC _).1 ⟨hy, y, rfl⟩

/-- **The attaching point of a rational tail lies on the closure of the complement.** It is a
point of the scheme-theoretic intersection of the two, and that intersection is a closed
subscheme of both. So the hypothesis of
`Stacks.Curves.hasAtWorstNodalSingularities_complementaryCurve_of_attachingPoint` is a condition
at a point that exists, and is not vacuous. -/
theorem exists_base_eq_attachingPoint
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    {C : X.IdealSheafData} (hC : IsRationalTail k X C) :
    ∃ y : complementaryCurve C,
      (complementaryCurveι C).base y = C.subschemeι hC.attachingPoint :=
  ((mem_support_and_mem_range_iff hC _).2 rfl).2

/-- **Stacks 0E3H, the at-worst-nodal clause for `X'`, reduced to the attaching point.** Let `X`
be a proper one-dimensional scheme over a field `k` with at-worst-nodal singularities and only
constant global functions, let `C ⊆ X` be a rational tail and let `X'` be the scheme-theoretic
closure of the complement of `C`. If `X'` is smooth over `k` or has a node at the point lying
over the attaching point of `C`, then `X'` has at-worst-nodal singularities.

Every other closed point of `X'` is handled by
`Stacks.Curves.smoothAt_or_isNode_complementaryCurve_of_notMem_support`, so the hypothesis is
the whole of what Tag 0E3H's at-worst-nodal clause still asks for. -/
theorem hasAtWorstNodalSingularities_complementaryCurve_of_attachingPoint
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalTail k X C)
    (hattach : ∀ y : complementaryCurve C, IsClosed ({y} : Set (complementaryCurve C)) →
      (complementaryCurveι C).base y = C.subschemeι hC.attachingPoint →
      InfinitesimalLifting.SmoothAt (complementaryCurveι C ≫ (X ↘ Spec (.of k))) y ∨
        @IsNode k _ (complementaryCurve C)
          ⟨complementaryCurveι C ≫ (X ↘ Spec (.of k))⟩ y) :
    letI : (complementaryCurve C).Over (Spec (.of k)) :=
      ⟨complementaryCurveι C ≫ (X ↘ Spec (.of k))⟩
    HasAtWorstNodalSingularities k (complementaryCurve C) := by
  intro y hyc
  by_cases hy : (complementaryCurveι C).base y ∈ (C.support : Set X)
  · exact hattach y hyc (base_eq_attachingPoint_of_mem_support hC y hy)
  · exact smoothAt_or_isNode_complementaryCurve_of_notMem_support k X hdim hnodal C hC y hyc hy

end Stacks.Curves

end
