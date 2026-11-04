module

public import StacksFrontier.AlgebraicGeometry.Curves.NodalGorensteinReduced
public import StacksFrontier.AlgebraicGeometry.Curves.NodalLciUnramifiedCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.NodalUnramifiedSingularSubscheme
public import StacksFrontier.AlgebraicGeometry.Curves.NodeCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Curves.NodeDepthFittingIdealCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.UniformizerDifferential
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.AtPointCriteria
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.QuasiFiniteCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.DenseSmoothOpen
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.SmoothLocus
public import StacksFrontier.FieldTheory.Separable.PerfectField
public import StacksFrontier.RingTheory.CompleteIntersection.Smooth
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing

/-!
# The unramified singular subscheme criterion for at-worst-nodal singularities

Let `k` be a field and let `X` be a locally algebraic `k`-scheme, equidimensional of dimension
one.  Condition (2) of Stacks Tag 0C4E asks that `X` be a local complete intersection over `k`
and that the closed subscheme `Z ⊆ X` cut out by the first Fitting ideal of `Ω_{X/k}` be
unramified over `k`; condition (1) asks that the singularities of `X` be at worst nodal.

This file proves the whole equivalence over an algebraically closed base field, assembling it
from the base's general-base-field halves in
`StacksFrontier.AlgebraicGeometry.Curves.NodalLciUnramifiedCriterion` together with the
algebraically-closed implication (2) ⟹ (1) proved here.

## Main results

* `Curves.hasAtWorstNodalSingularities_of_isLocalCompleteIntersectionOverField_of_isAlgClosed`
  — the implication (2) ⟹ (1) of Tag 0C4E over an algebraically closed base field.
* `Stacks.Curves.isCompleteIntersection_stalk_of_smoothAt` — the local ring at a smooth point of
  a scheme locally of finite type over a field is a complete intersection over that field.
* `Stacks.Curves.isClosed_singleton_of_notMem_genericPoints` — a point of a one-dimensional
  scheme that is not a generic point of an irreducible component is closed.
* `Stacks.Curves.dense_setOf_smoothAt_of_hasAtWorstNodalSingularities` — the smooth locus of an
  at-worst-nodal locally algebraic curve is dense.
* `Stacks.Curves.isClosed_singleton_of_not_smoothAt` — hence its non-smooth points, which by Tag
  0C3K are the points of `Z`, are closed.
* `Stacks.Curves.stalk_fittingIdeal_eq_maximalIdeal_of_isNode_of_isAlgClosed` — at a node of
  `Z`, the first Fitting ideal generates the maximal ideal, so `𝒪_{Z,x} = κ(x)`.

## Implementation notes

### The implication (2) ⟹ (1)

The two hypotheses are exactly condition (2):
`AlgebraicGeometry.IsLocalCompleteIntersectionOverField`
for the structure morphism, and unramifiedness over the base of
`AlgebraicGeometry.relativeSingularIdeal`, the closed subscheme cut out by the first Fitting
ideal of the relative differentials.  The conclusion
`Stacks.Curves.HasAtWorstNodalSingularities` is condition (1).

Everything is already in place.
`Stacks.Curves.smoothAt_or_isSeparable_and_depth_eq_one_and_fittingIdeal_eq_maximalIdeal`
takes condition (2) to the alternative "smooth at `x`, or condition (5) of Tag 0C4D at `x`" at
every closed point, and
`Stacks.Curves.isNode_of_depth_eq_one_and_stalk_fittingIdeal_eq_maximalIdeal_of_isAlgClosed`
takes condition (5) of Tag 0C4D to the node condition over an algebraically closed field.  The
latter is the implication (5) ⟹ (1) of Tag 0C4D; the module documentation of
`StacksFrontier.AlgebraicGeometry.Curves.NodalUnramifiedSingularSubscheme` records that this step
was unavailable, and that record is out of date for an algebraically closed base field.

Separability of the residue field extension is not taken from the first result: its separability
clause is stated over `κ(f x)`, the spelling of Tag 02G8, while the second result asks for
`Algebra.IsSeparableExtension k (κ(x))` for the `k`-algebra structure coming from the germ of the
structure morphism.  Over an algebraically closed — hence perfect — field every extension is
separable in that sense, by `Algebra.isSeparableExtension_of_perfectField`, so the clause is
free.

### The smooth points, and why the non-smooth ones are closed

By Tag 01UG, `localCompleteIntersection_tfae`, being a local complete intersection over `k` is
the assertion that every local ring is a complete intersection over `k`, so that conjunct of
(1) ⟹ (2) is proved point by point.  At a smooth point the local ring is regular — this is the
`moreover` of Tag 00TT, read through the identification of smoothness at a point with formal
smoothness of the stalk map, which is
`Stacks.Curves.isRegularLocalRing_stalk_of_smoothAt` of
`StacksFrontier.AlgebraicGeometry.Curves.NodalDichotomy` — and essentially of finite type over `k`,
hence a complete intersection over `k`; that is
`Stacks.Curves.isCompleteIntersection_stalk_of_smoothAt`, proved here.  At a node it is
`Stacks.Curves.isCompleteIntersection_stalk_of_isNode`.  The conjunct itself is
`Stacks.Curves.isLocalCompleteIntersectionOverField_of_hasAtWorstNodalSingularities` of
`StacksFrontier.AlgebraicGeometry.Curves.NodalLciUnramifiedCriterion`.

What joins the two is that the non-smooth points are closed, so that the at-worst-nodal
hypothesis, which only speaks of closed points, applies to all of them.  The source gets this
from the dense smooth open: an at-worst-nodal curve is geometrically reduced (Tag 0E37), a
reduced scheme locally of finite type over a field is geometrically reduced exactly when it has
a dense open subscheme smooth over the field (Tag 056V), and a generic point of a locally
Noetherian scheme lies in every dense open.  A point of a one-dimensional scheme which is not
such a generic point is closed, since otherwise a strict specialization of it, its own closure
and an irreducible component strictly above that closure form a chain of length two.

The non-smooth points are the points of `Z` by Tag 0C3K
(`AlgebraicGeometry.range_subschemeι_fittingIdeal_relativeDifferentials`), but that
identification is not used: the proof works with the non-smooth locus directly.

### The Fitting ideal at a node, and the unramifiedness conjunct of (1) ⟹ (2)

A point `z` of `Z` lies over a point `x` of `X` at which the structure morphism is not smooth,
by Tag 0C3K; that point is closed by the paragraph above, hence a node.  Over an algebraically
closed field the first Fitting ideal then generates the maximal ideal of `𝒪_{X,x}`, which is
`Stacks.Curves.stalk_fittingIdeal_eq_maximalIdeal_of_isNode_of_isAlgClosed`, proved here.  The
unramifiedness conjunct it feeds is
`Stacks.Curves.unramified_relativeSingularIdeal_of_hasAtWorstNodalSingularities` of
`StacksFrontier.AlgebraicGeometry.Curves.NodalLciUnramifiedCriterion`, which needs no algebraic
closedness.

## References

* [Stacks Project, Tag 0C4E](https://stacks.math.columbia.edu/tag/0C4E)
* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C3K](https://stacks.math.columbia.edu/tag/0C3K)
* [Stacks Project, Tag 01UG](https://stacks.math.columbia.edu/tag/01UG)
* [Stacks Project, Tag 00TT](https://stacks.math.columbia.edu/tag/00TT)
* [Stacks Project, Tag 056V](https://stacks.math.columbia.edu/tag/056V)
* [Stacks Project, Tag 0E37](https://stacks.math.columbia.edu/tag/0E37)
* [Stacks Project, Tag 02GF](https://stacks.math.columbia.edu/tag/02GF)
* [Stacks Project, Tag 01TF](https://stacks.math.columbia.edu/tag/01TF)
* [Stacks Project, Tag 0C47](https://stacks.math.columbia.edu/tag/0C47)
* [Stacks Project, Tag 0C5A](https://stacks.math.columbia.edu/tag/0C5A)
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry IsLocalRing

universe u

namespace Stacks.Curves

/-- The `k`-algebra structure on the stalk at `x` coming from the germ of the structure morphism. -/
private noncomputable abbrev stalkAlgebra (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of k)) (x : X) : Algebra k (X.presheaf.stalk x) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x (by simp)).hom.toAlgebra

/-- **The implication (2) ⟹ (1) of Stacks Tag 0C4E over an algebraically closed field.**

Let `k` be an algebraically closed field and let `X` be a locally algebraic `k`-scheme,
equidimensional of dimension one.  If `X` is a local complete intersection over `k` and the
closed subscheme `Z ⊆ X` cut out by the first Fitting ideal of `Ω_{X/k}` is unramified over `k`,
then the singularities of `X` are at worst nodal: every closed point of `X` is either a smooth
point of the structure morphism or a node.

The hypotheses are condition (2) of the tag and the conclusion is its condition (1). -/
theorem hasAtWorstNodalSingularities_of_isLocalCompleteIntersectionOverField_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (hlci : IsLocalCompleteIntersectionOverField (X ↘ AlgebraicGeometry.Spec (.of k)))
    (hZ : Unramified ((relativeSingularIdeal (X ↘ AlgebraicGeometry.Spec (.of k))).subschemeι ≫
      (X ↘ AlgebraicGeometry.Spec (.of k)))) :
    HasAtWorstNodalSingularities k X := by
  intro x hx
  rcases smoothAt_or_isSeparable_and_depth_eq_one_and_fittingIdeal_eq_maximalIdeal k
    (X ↘ AlgebraicGeometry.Spec (.of k)) hequi hdim hlci hZ x hx with hsm | ⟨-, -, hdepth, hfit⟩
  · exact Or.inl hsm
  · let := stalkAlgebra k (X ↘ AlgebraicGeometry.Spec (.of k)) x
    let : Algebra k (X.residueField x) :=
      ((X.residue x).hom.comp (algebraMap k (X.presheaf.stalk x))).toAlgebra
    exact Or.inr (isNode_of_depth_eq_one_and_stalk_fittingIdeal_eq_maximalIdeal_of_isAlgClosed
      k X x hx (Algebra.isSeparableExtension_of_perfectField k (X.residueField x)) hdepth hfit)

/-! ### The smooth points of the implication (1) ⟹ (2) -/

/-- **The local ring at a smooth point of a scheme locally of finite type over a field is a
complete intersection over that field.**  The local ring is regular, and essentially of finite
type over `k` because the morphism is smooth there; a regular local algebra essentially of
finite type over a field is a complete intersection over it, in the sense of Definition 00SD.

This is the local-complete-intersection half of the implication (1) ⟹ (2) of Stacks Tag 0C4E at
the points *outside* the closed subscheme cut out by the first Fitting ideal of `Ω_{X/k}`, which
by Tag 0C3K are exactly the smooth points.  Together with
`Stacks.Curves.isCompleteIntersection_stalk_of_isNode` at the nodes, and Tag 01UG, it is that
half of the implication at every point. -/
theorem isCompleteIntersection_stalk_of_smoothAt (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of k)) [LocallyOfFiniteType f] (x : X)
    (hsm : InfinitesimalLifting.SmoothAt f x) :
    letI : Algebra k (X.presheaf.stalk x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom.toAlgebra
    IsCompleteIntersection k (X.presheaf.stalk x) := by
  let := stalkAlgebra k f x
  have : IsRegularLocalRing (X.presheaf.stalk x) :=
    isRegularLocalRing_stalk_of_smoothAt k f hsm
  have : Algebra.EssFiniteType k (X.presheaf.stalk x) :=
    (smoothAt_field_stalk_properties f x hsm).1
  exact isCompleteIntersection_of_isRegularLocalRing k (X.presheaf.stalk x)

/-! ### The singular points of an at-worst-nodal curve are closed -/

/-- **A point of a one-dimensional scheme which is not a generic point of an irreducible
component is closed.**  Were it not closed, a strict specialization of it, its own closure and
an irreducible component strictly containing that closure would form a chain of three
irreducible closed subsets, so the dimension would be at least two. -/
theorem isClosed_singleton_of_notMem_genericPoints {X : Scheme.{u}}
    (hdim : topologicalKrullDim X = 1) (x : X) (hx : x ∉ genericPoints X) :
    IsClosed ({x} : Set X) := by
  by_contra hxc
  obtain ⟨z, hzmem, hzx⟩ : ∃ z ∈ closure ({x} : Set X), z ≠ x := by
    by_contra hcon
    push Not at hcon
    have heq : closure ({x} : Set X) = ({x} : Set X) :=
      Set.Subset.antisymm (fun y hy => hcon y hy) subset_closure
    refine hxc ?_
    rw [← heq]
    exact isClosed_closure
  obtain ⟨C, hC, hxC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({x} : Set X)) isIrreducible_singleton.closure
  let S₀ : IrreducibleCloseds X :=
    ⟨closure ({z} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
  let S₁ : IrreducibleCloseds X :=
    ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
  let S₂ : IrreducibleCloseds X := ⟨C, hC.1, isClosed_of_mem_irreducibleComponents C hC⟩
  have h01 : S₀ < S₁ := by
    refine ⟨closure_minimal (Set.singleton_subset_iff.mpr hzmem) isClosed_closure, fun h => ?_⟩
    exact hzx ((Specializes.antisymm (specializes_iff_mem_closure.mpr hzmem)
      (specializes_iff_mem_closure.mpr (h (subset_closure (Set.mem_singleton x))))).eq.symm)
  have h12 : S₁ < S₂ := by
    refine ⟨hxC, fun h => hx ?_⟩
    have heq : closure ({x} : Set X) = C :=
      congrArg (fun A : IrreducibleCloseds X => (A : Set X)) (le_antisymm hxC h)
    show closure ({x} : Set X) ∈ irreducibleComponents X
    rw [heq]
    exact hC
  let p : LTSeries (IrreducibleCloseds X) :=
    RelSeries.fromListIsChain [S₀, S₁, S₂] (by simp)
      (List.IsChain.cons_cons h01 (List.isChain_pair.mpr h12))
  have hdim' : Order.krullDim (IrreducibleCloseds X) = 1 := by
    simpa [topologicalKrullDim] using hdim
  have hdimlt : Order.krullDim (IrreducibleCloseds X) < 2 := by
    rw [hdim']
    decide
  have hp : p.length < 2 :=
    (Order.krullDim_lt_coe_iff (α := IrreducibleCloseds X) (n := 2)).mp hdimlt p
  have hplen : p.length = 2 := by simp [p]
  omega

/-- **The smooth locus of an at-worst-nodal locally algebraic curve is dense.**  Such a curve is
geometrically reduced over the base field by Tag 0E37, and a reduced scheme locally of finite
type over a field is geometrically reduced exactly when it has a dense open subscheme smooth
over that field (Tag 056V); every point of such an open is a smooth point of the curve. -/
theorem dense_setOf_smoothAt_of_hasAtWorstNodalSingularities (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) :
    Dense {x : X | InfinitesimalLifting.SmoothAt (X ↘ AlgebraicGeometry.Spec (.of k)) x} := by
  set f := X ↘ AlgebraicGeometry.Spec (.of k)
  have : AlgebraicGeometry.IsReduced X := isReduced_of_hasAtWorstNodalSingularities k X hnodal
  obtain ⟨U, hUdense, hUsmooth⟩ := (geometricallyReduced_iff_exists_dense_open_smooth f).mp
    (geometricallyReduced_of_hasAtWorstNodalSingularities k X hequi hdim hnodal)
  refine hUdense.mono fun u hu => ?_
  have htop : (U.ι ≫ f).smoothLocus = ⊤ := Scheme.Hom.smoothLocus_eq_top _
  have hmem : u ∈ f.smoothLocus :=
    ((Scheme.Hom.preimage_smoothLocus_eq U.ι f).trans htop).ge
      (Set.mem_univ (⟨u, hu⟩ : U.toScheme))
  exact InfinitesimalLifting.formallySmooth_stalkMap_smoothAt f u
    (Scheme.Hom.mem_smoothLocus.mp hmem)

/-- **A point of an at-worst-nodal locally algebraic curve at which the structure morphism is
not smooth is closed.**  The smooth locus is open and dense, so it contains every generic point
of an irreducible component; a point of a one-dimensional scheme that is not such a generic
point is closed.

By Tag 0C3K the points where the structure morphism is not smooth are exactly the points of the
closed subscheme cut out by the first Fitting ideal of `Ω_{X/k}`, so this says that that
subscheme consists of closed points. -/
theorem isClosed_singleton_of_not_smoothAt (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (hequi : Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X) (x : X)
    (hx : ¬ InfinitesimalLifting.SmoothAt (X ↘ AlgebraicGeometry.Spec (.of k)) x) :
    IsClosed ({x} : Set X) := by
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ AlgebraicGeometry.Spec (.of k))
  refine isClosed_singleton_of_notMem_genericPoints hdim x fun hgen => hx ?_
  exact scheme_genericPoints_mem_dense_open X
    (isOpen_smoothAt_locus (X ↘ AlgebraicGeometry.Spec (.of k)))
    (dense_setOf_smoothAt_of_hasAtWorstNodalSingularities k X hequi hdim hnodal) hgen

end Stacks.Curves

/-! ### The stalk of an ideal sheaf at a point of its closed subscheme -/

namespace AlgebraicGeometry

/-- **The stalk of an ideal sheaf at a point of the closed subscheme it cuts out is a proper
ideal.**  That stalk is the kernel of the stalk map of the closed immersion, which is a ring
map onto the local ring of the subscheme at the point, and that ring is nontrivial. -/
theorem IdealSheafData.stalk_le_maximalIdeal_subschemeι {X : Scheme.{u}} (I : X.IdealSheafData)
    (z : I.subscheme) :
    IdealSheafData.stalk I (I.subschemeι.base z) ≤
      maximalIdeal (X.presheaf.stalk (I.subschemeι.base z)) := by
  refine IsLocalRing.le_maximalIdeal fun htop => ?_
  rw [← IdealSheafData.ker_stalkMap_subschemeι_eq_stalk I z] at htop
  have : (1 : X.presheaf.stalk (I.subschemeι.base z)) ∈
      RingHom.ker (I.subschemeι.stalkMap z).hom := htop ▸ Submodule.mem_top
  exact one_ne_zero (by simp at this : (1 : I.subscheme.presheaf.stalk z) = 0)

end AlgebraicGeometry

namespace Stacks.Curves

/-! ### The Fitting ideal at a node generates the maximal ideal -/

/-- **At a node of a scheme locally of finite type over an algebraically closed field the first
Fitting ideal of `Ω_{X/k}` generates the maximal ideal of the local ring.**

This is the implication (1) ⟹ (4) of Stacks Tag 0C4D, Fitting clause, over an algebraically
closed base field: condition (4) of that tag asks, among other things, that "the first Fitting
ideal of `Ω_{X/k}` generates `𝔪_x` in `𝒪_{X,x}`", and the tag assumes of `x` only that it is a
closed point of a one-dimensional algebraic `k`-scheme.  Equivalently it says that the local ring
at `x` of the closed subscheme cut out by that Fitting ideal is the residue field `κ(x)`, which
is the step "for every point `x ∈ Z` the local ring `𝒪_{Z,x}` is equal to `κ(x)`" of the proof of
the implication (1) ⟹ (2) of Tag 0C4E.

Nothing is assumed about the subscheme: the Fitting-ideal criterion
`Stacks.Curves.isNodalAlgebra_stalk_iff_isReduced_and_stalk_fittingIdeal_eq_maximalIdeal` derives
the containment of the Jacobian minors in the prime of `x` from the presentation being centred
there. -/
theorem stalk_fittingIdeal_eq_maximalIdeal_of_isNode_of_isAlgClosed
    (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (.of k))]
    [LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (.of k))]
    (x : X) (hx : IsClosed ({x} : Set X)) (hnode : IsNode k X x) :
    IdealSheafData.stalk (fittingIdeal (Scheme.Hom.relativeDifferentials
        (X ↘ AlgebraicGeometry.Spec (.of k))) (1 : ℤ)) x =
      maximalIdeal (X.presheaf.stalk x) := by
  set f := X ↘ AlgebraicGeometry.Spec (.of k)
  let := stalkAlgebra k f x
  have hnodal : IsNodalAlgebra k (X.presheaf.stalk x) :=
    (isNode_iff_isNodalAlgebra_stalk_of_isAlgClosed k X x hx).mp hnode
  let e : Γ(AlgebraicGeometry.Spec (.of k), ⊤) ≃+* k :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  have : IsNoetherianRing Γ(AlgebraicGeometry.Spec (.of k), ⊤) :=
    isNoetherianRing_of_ringEquiv k e.symm
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  have hUV : U ≤ f ⁻¹ᵁ (⊤ : (AlgebraicGeometry.Spec (.of k)).Opens) := le_top
  let := Stacks.Smooth.algebraAppLE f hUV
  have : Algebra.FiniteType Γ(AlgebraicGeometry.Spec (.of k), ⊤) Γ(X, U) :=
    RingHom.finiteType_algebraMap.mp
      (f.finiteType_appLE (isAffineOpen_top (AlgebraicGeometry.Spec (.of k))) hU hUV)
  have : ((hU.primeIdealOf ⟨x, hxU⟩).asIdeal).IsMaximal :=
    hU.primeIdealOf_isMaximal_of_isClosed ⟨x, hxU⟩ hx
  obtain ⟨n, m, P, hv⟩ :=
    Algebra.Presentation.exists_centred_of_ringEquiv_isAlgClosed k e
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal
  exact (isNodalAlgebra_stalk_iff_isReduced_and_stalk_fittingIdeal_eq_maximalIdeal f x
    ⟨U, hU⟩ hxU hx (isAffineOpen_top (AlgebraicGeometry.Spec (.of k))) hUV k e k P hv).mp
      hnodal |>.2.2

end Stacks.Curves

end
