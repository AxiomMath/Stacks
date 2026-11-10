module

public import StacksFrontier.AlgebraicGeometry.Properties.Serre
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SyntomicFibres
public import StacksFrontier.Deformation.Examples.Geometric.CurveChartGeometry
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingDecomposition
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.LocalCompleteIntersection
public import StacksFrontier.RingTheory.Syntomic.SyntomicAt
public import StacksFrontier.Deformation.Examples.Geometric.SmoothingFitting
public import Mathlib.RingTheory.RingHom.EssFiniteType
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Reducedness of a curve with isolated complete intersection singularities

Let `X` be a scheme locally of finite type over a field `k` which is a local complete intersection
over `k` and smooth over `k` away from finitely many points. If no point of `X` is an irreducible
component — for instance if `X` is equidimensional of dimension one — then `X` is reduced. This is
the step "Then `X''` is reduced" of the proof of [Stacks, Tag 0E7Z]. The file also carries the
next step of that proof: a compactification of `X` by finitely many regular points is again a
local complete intersection, smooth away from finitely many points.

The proof is Serre's criterion [Stacks, Tag 0344]. Property `(S₁)` holds because `X` is
Cohen–Macaulay ([Stacks, Tags 00SB and 0342]). Property `(R₀)` holds because a local ring of
dimension zero is the local ring at the generic point of an irreducible component, and such a
point is smooth: otherwise its closure would be a finite irreducible closed set, hence, `X` being
Jacobson, a single closed point and an irreducible component. The local ring at a smooth point is
regular ([Stacks, Tag 00TT]).

## Main results

* `Deformation.Examples.Smoothing.isRegularLocalRing_stalk_of_mem_smoothLocus`: the local ring
  at a smooth point is regular.
* `Deformation.Examples.Smoothing.mem_smoothLocus_of_mem_genericPoints`: generic points of
  positive-dimensional irreducible components are smooth points.
* `Deformation.Examples.Smoothing.isReduced_of_syntomic_of_finite_compl_smoothLocus`: the
  reducedness criterion.
* `Deformation.Examples.Smoothing.isReduced_of_syntomic_of_equidimensional`: its equidimensional
  form.
* `Deformation.Examples.Smoothing.isLocalCompleteIntersectionOverField_of_isOpenImmersion` and
  `Deformation.Examples.Smoothing.finite_compl_smoothLocus_of_isOpenImmersion`: a
  compactification by finitely many points with discrete valuation rings as local rings keeps
  both hypotheses of [Stacks, Tag 0E7Y], as the proof of [Stacks, Tag 0E7Z] requires.

## References

* [The Stacks Project, Tag 0E7Z](https://stacks.math.columbia.edu/tag/0E7Z)
* [The Stacks Project, Tag 0344](https://stacks.math.columbia.edu/tag/0344)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Deformation.Examples.Smoothing

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **The local ring at a smooth point is regular**, for a scheme locally of finite presentation
over a field ([Stacks, Tag 00TT], read on an affine open). -/
@[ega "IV 17.15.2" "more general", sga "1 II 5.3" "more general", sga "1 II 5.4" "more general"]
theorem isRegularLocalRing_stalk_of_mem_smoothLocus [LocallyOfFinitePresentation f] (x : X)
    (hx : x ∈ f.smoothLocus) : IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) (by simp)
  let := sectionsAlgebra f U
  have := finiteType_sectionsAlgebra f hU
  have hsm := isSmoothAt_primeIdealOf f hU ⟨x, hxU⟩ hx
  let := X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  have := hU.isLocalization_stalk ⟨x, hxU⟩
  exact (Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing
    (hU.primeIdealOf ⟨x, hxU⟩) (X.presheaf.stalk x)).2 hsm

/-- **A non-smooth point is closed**, for a scheme locally of finite type over `k` whose
non-smooth locus is finite: the closure of a non-smooth point is a finite closed set, and in the
Jacobson space `X` a finite closed set consists of closed points. -/
theorem isClosed_singleton_of_notMem_smoothLocus [LocallyOfFiniteType f]
    (hfin : (f.smoothLocus : Set X)ᶜ.Finite) {x : X} (hxs : x ∉ f.smoothLocus) :
    IsClosed ({x} : Set X) := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hfinC : (closure ({x} : Set X)).Finite :=
    hfin.subset (f.smoothLocus.isOpen.isClosed_compl.closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hxs))
  set S := closure ({x} : Set X) ∩ closedPoints X
  have hSfin : S.Finite := hfinC.subset Set.inter_subset_left
  have hScl : IsClosed S := by
    rw [← Set.biUnion_of_singleton S]
    exact hSfin.isClosed_biUnion fun y hy => hy.2
  have hS : closure ({x} : Set X) = S := by
    rw [← hScl.closure_eq, JacobsonSpace.closure_inter_closedPoints_eq_closure
      isClosed_closure.isLocallyClosed, closure_closure]
  exact (hS ▸ subset_closure (Set.mem_singleton x) : x ∈ S).2

/-- **A generic point of an irreducible component of dimension at least one is a smooth point**,
for a scheme locally of finite type over `k` whose non-smooth locus is finite: a non-smooth point
is closed (`Deformation.Examples.Smoothing.isClosed_singleton_of_notMem_smoothLocus`), so a
non-smooth generic point would be an irreducible component of dimension zero. -/
theorem mem_smoothLocus_of_mem_genericPoints [LocallyOfFiniteType f]
    (hfin : (f.smoothLocus : Set X)ᶜ.Finite) {x : X} (hx : x ∈ genericPoints X)
    (hx0 : x ∉ zeroDimensionalLocus X) : x ∈ f.smoothLocus := by
  by_contra hxs
  have hxcl := isClosed_singleton_of_notMem_smoothLocus k f hfin hxs
  refine hx0 ?_
  change {x} ∈ irreducibleComponents X
  rwa [← hxcl.closure_eq]

/-- **A curve with isolated local complete intersection singularities and no isolated points is
reduced.** Let `X` be locally of finite type over `k`, a local complete intersection over `k`,
smooth over `k` away from finitely many points, and such that no point of `X` is an irreducible
component. Then `X` is reduced.

This is Serre's criterion [Stacks, Tag 0344]: `X` is Cohen–Macaulay ([Stacks, Tag 00SB]), so it
has property `(S₁)` ([Stacks, Tag 0342]); and the local ring at a point of dimension zero is the
local ring at a generic point of an irreducible component, which is a smooth point
(`Deformation.Examples.Smoothing.mem_smoothLocus_of_mem_genericPoints`) and therefore a regular
local ring, so `X` has property `(R₀)`. -/
theorem isReduced_of_syntomic_of_finite_compl_smoothLocus [LocallyOfFiniteType f]
    (hf : IsLocalCompleteIntersectionOverField f) (hfin : (f.smoothLocus : Set X)ᶜ.Finite)
    (hzero : ∀ x : X, x ∉ zeroDimensionalLocus X) : IsReduced X := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hCM := isCohenMacaulay_of_syntomic_over_field f hf
  refine (isReduced_iff_hasPropertyS1_and_isRegularInCodimension_zero X).mpr
    ⟨(isCohenMacaulay_iff_forall_hasPropertySk X).mp hCM 1, fun x hx => ?_⟩
  have h0 : ringKrullDim (X.presheaf.stalk x) = 0 :=
    le_antisymm (by exact_mod_cast hx) ringKrullDim_nonneg_of_nontrivial
  exact isRegularLocalRing_stalk_of_mem_smoothLocus k f x
    (mem_smoothLocus_of_mem_genericPoints k f hfin
      ((ringKrullDim_stalk_eq_zero_iff_mem_genericPoints X x).mp h0) (hzero x))

/-- In an equidimensional space of dimension one no point is an irreducible component. -/
theorem notMem_zeroDimensionalLocus_of_equidimensional {T : Type*} [TopologicalSpace T]
    (hequi : TopologicalSpace.Equidimensional T) (hdim : topologicalKrullDim T = 1) (x : T) :
    x ∉ zeroDimensionalLocus T := by
  intro hx
  have hx' : ({x} : Set T) ∈ irreducibleComponents T := hx
  have h0 : topologicalKrullDim ({x} : Set T) ≤ 0 := by
    have : DiscreteTopology ({x} : Set T) := Subsingleton.discreteTopology
    exact topologicalKrullDim_zero_of_discreteTopology ({x} : Set T)
  have hle : topologicalKrullDim T ≤ 0 := by
    rw [topologicalKrullDim_eq_iSup_irreducibleComponents]
    refine iSup₂_le fun W hW => ?_
    rwa [hequi W hW _ hx']
  rw [hdim] at hle
  exact absurd hle (by decide)

/-- **A curve with isolated local complete intersection singularities, equidimensional of
dimension one, is reduced.** The form of
`Deformation.Examples.Smoothing.isReduced_of_syntomic_of_finite_compl_smoothLocus` for the
equidimensional piece of the decomposition of [Stacks, Tag 0E7Y]. -/
theorem isReduced_of_syntomic_of_equidimensional [LocallyOfFiniteType f]
    (hf : IsLocalCompleteIntersectionOverField f) (hfin : (f.smoothLocus : Set X)ᶜ.Finite)
    (hequi : TopologicalSpace.Equidimensional X) (hdim : topologicalKrullDim X = 1) :
    IsReduced X :=
  isReduced_of_syntomic_of_finite_compl_smoothLocus k f hf hfin
    (notMem_zeroDimensionalLocus_of_equidimensional hequi hdim)

section Compactification

variable {Y : Scheme.{u}} (q : Y ⟶ Spec (.of k))

/-- **A regular local ring essentially of finite type over `k` is a complete intersection over
`k`**, with the empty regular sequence. This is the remark following [Stacks, Tag 00SD], used here
for the discrete valuation rings at the points added by a compactification. -/
@[ega "IV 19.3.3" "special case"]
theorem isCompleteIntersection_stalk_of_isRegularLocalRing [LocallyOfFiniteType q] (y : Y)
    [IsRegularLocalRing (Y.presheaf.stalk y)] :
    letI := stalkAlgebra k q y
    IsCompleteIntersection k (Y.presheaf.stalk y) := by
  let := stalkAlgebra k q y
  exact ⟨Y.presheaf.stalk y, inferInstance, inferInstance, inferInstance,
    essFiniteType_stalk k q y, [], RingTheory.Sequence.IsRegular.nil _ _,
    ⟨(AlgEquiv.quotientBot k (Y.presheaf.stalk y)).symm.trans
      (Ideal.quotientEquivAlgOfEq k (Ideal.ofList_nil).symm)⟩⟩

/-- **A compactification by regular points inherits the local complete intersection property.**
Let `j : X ⟶ Y` be an open immersion of schemes over `k` with `Y` locally of finite type, `X` a
local complete intersection over `k`, and the local ring of `Y` at every point outside the image
of `j` a discrete valuation ring. Then `Y` is a local complete intersection over `k`.

This is the step "`X̄` is a local complete intersection over `k` because this holds over the open
`X` and at the points `x_i`" of the proof of [Stacks, Tag 0E7Z], via the pointwise criterion
[Stacks, Tag 01UG] (`AlgebraicGeometry.localCompleteIntersection_tfae`). -/
theorem isLocalCompleteIntersectionOverField_of_isOpenImmersion {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (j : X ⟶ Y) [IsOpenImmersion j] (hjq : j ≫ q = p)
    [LocallyOfFiniteType q] (hp : IsLocalCompleteIntersectionOverField p)
    (hdvr : ∀ y : Y, y ∉ Set.range j.base →
      ∃ _ : IsDomain (Y.presheaf.stalk y), IsDiscreteValuationRing (Y.presheaf.stalk y)) :
    IsLocalCompleteIntersectionOverField q := by
  have : LocallyOfFiniteType p := hjq ▸ inferInstance
  refine ((localCompleteIntersection_tfae k Y q).out 1 3).mpr fun y => ?_
  by_cases hy : y ∈ Set.range j.base
  · obtain ⟨x, rfl⟩ := hy
    have h3 := ((localCompleteIntersection_tfae k X p).out 1 3).mp hp
    dsimp only at h3
    have hx := h3 x
    let := stalkAlgebra k p x
    let := stalkAlgebra k q (j.base x)
    refine hx.of_algEquiv (AlgEquiv.ofRingEquiv
      (f := (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv.symm) fun a => ?_)
    apply (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv.injective
    rw [RingEquiv.apply_symm_apply]
    change _ = (j.stalkMap x).hom (((Scheme.ΓSpecIso (.of k)).inv ≫ q.appTop ≫
      Y.presheaf.germ ⊤ (j.base x) (by simp)).hom a)
    rw [← CommRingCat.comp_apply, Category.assoc, Category.assoc, Scheme.Hom.germ_stalkMap]
    subst hjq
    rfl
  · obtain ⟨_, _⟩ := hdvr y hy
    exact isCompleteIntersection_stalk_of_isRegularLocalRing k q y

/-- **A compactification by finitely many points keeps the non-smooth locus finite.** With `j`,
`q` and `p` as in
`Deformation.Examples.Smoothing.isLocalCompleteIntersectionOverField_of_isOpenImmersion`, if
`X` is smooth over `k` away from finitely many points and `Y ∖ j(X)` is finite, then `Y` is
smooth over `k` away from finitely many points: the non-smooth locus of `Y` lies in the image of
that of `X` together with `Y ∖ j(X)`. -/
theorem finite_compl_smoothLocus_of_isOpenImmersion {X : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (j : X ⟶ Y) [IsOpenImmersion j] (hjq : j ≫ q = p)
    [LocallyOfFiniteType p] [LocallyOfFiniteType q] (hfin : ((p.smoothLocus : Set X)ᶜ).Finite)
    (hbd : ((Set.range j.base)ᶜ).Finite) : ((q.smoothLocus : Set Y)ᶜ).Finite := by
  subst hjq
  refine ((hfin.image j.base).union hbd).subset fun y hy => ?_
  by_cases hyr : y ∈ Set.range j.base
  · obtain ⟨x, rfl⟩ := hyr
    refine Or.inl ⟨x, fun hx => hy ?_, rfl⟩
    rwa [← Scheme.Hom.preimage_smoothLocus_eq] at hx
  · exact Or.inr hyr

end Compactification

end Deformation.Examples.Smoothing
