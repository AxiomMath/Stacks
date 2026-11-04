module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SyntomicFibres
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesSmooth
public import StacksFrontier.Topology.Dimension.Equidimensional
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# A curve over a field is a disjoint union of a finite part and an equidimensional part

Let `X` be a scheme locally of finite type and quasi-compact over a field `k` with
`dim(X) ≤ 1`. The proofs of [Stacks, Tag 0E7Y] and [Stacks, Tag 0E7Z] begin by writing
`X = X' ⊔ X''` with `dim(X') = 0` and `X''` equidimensional of dimension `1`. The source gets
this from Cohen–Macaulayness and [Stacks, Tag 02NM]; the decomposition is in fact purely
topological and needs neither.

`X'` is the set of points `x` for which `{x}` is an irreducible component of `X`. Such a point
lies on no other irreducible component, by maximality of components, so its complement is a
finite union of closed sets: `{x}` is open. There are finitely many such points and each is
closed, so `X'` is open and closed, and it is discrete. `X''` is the complement. A point `x` of
`X''` lies on an irreducible component `Z` with generic point `η` and `Z ≠ {x}`. In every open
neighbourhood `W` of `x` there is a strict specialization: `η ⤳ x` if `η ≠ x`; and if `η = x`,
some point of `Z` other than `x` lies in `W`, for otherwise `{x} = W ∩ Z` would be locally
closed, hence closed by the Jacobson property, and `Z = {x}`. So the local dimension of `X` at
`x` is `1`, and `X''` is equidimensional of dimension `1` by
`AlgebraicGeometry.forall_topologicalKrullDimAt_eq_iff_forall_irreducibleComponents`.

## Main definitions

* `Deformation.Examples.Smoothing.zeroDimensionalLocus`: the points `x` with `{x}` an irreducible
  component.

## Main results

* `Deformation.Examples.Smoothing.exists_isCompl_zeroDimensional_equidimensional`: the
  decomposition `X = X' ⊔ X''` into complementary opens, with `X'` of dimension at most `0`,
  `X''` equidimensional of dimension `1` when nonempty, and both inclusions closed immersions.
* `Deformation.Examples.Smoothing.isLocalCompleteIntersectionOverField_ι_comp` and
  `Deformation.Examples.Smoothing.finite_compl_smoothLocus_ι_comp`: the hypotheses of the
  smoothing lemmas pass to an open subscheme.

## References

* [Stacks Project, Tag 0E7Y](https://stacks.math.columbia.edu/tag/0E7Y)
* [Stacks Project, Tag 0E7Z](https://stacks.math.columbia.edu/tag/0E7Z)
* [Stacks Project, Tag 02NM](https://stacks.math.columbia.edu/tag/02NM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

universe u

namespace Deformation.Examples.Smoothing

section Topology

variable {T : Type*} [TopologicalSpace T]

/-- A point which is an irreducible component lies on no other irreducible component. -/
theorem eq_singleton_of_mem_irreducibleComponents {x : T} (hx : {x} ∈ irreducibleComponents T)
    {Z : Set T} (hZ : Z ∈ irreducibleComponents T) (hxZ : x ∈ Z) : Z = {x} :=
  (hx.eq_of_le hZ.1 (Set.singleton_subset_iff.mpr hxZ)).symm

/-- In a Noetherian space a point which is an irreducible component is open: its complement is
the union of the finitely many other irreducible components. -/
theorem isOpen_singleton_of_mem_irreducibleComponents [NoetherianSpace T] {x : T}
    (hx : {x} ∈ irreducibleComponents T) : IsOpen ({x} : Set T) := by
  have hcompl : ({x} : Set T)ᶜ = ⋃₀ (irreducibleComponents T \ {{x}}) := by
    ext y
    constructor
    · intro hy
      obtain ⟨Z, hZ, hyZ⟩ := Set.mem_sUnion.mp
        (show y ∈ ⋃₀ irreducibleComponents T by rw [sUnion_irreducibleComponents]; trivial)
      refine ⟨Z, ⟨hZ, fun hZx => hy ?_⟩, hyZ⟩
      rwa [Set.mem_singleton_iff.mp hZx] at hyZ
    · rintro ⟨Z, ⟨hZ, hZx⟩, hyZ⟩ rfl
      exact hZx (eq_singleton_of_mem_irreducibleComponents hx hZ hyZ)
  rw [← isClosed_compl_iff, hcompl]
  exact NoetherianSpace.finite_irreducibleComponents.sdiff.isClosed_sUnion
    fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1

/-- The points of `T` which are irreducible components of `T`. -/
def zeroDimensionalLocus (T : Type*) [TopologicalSpace T] : Set T :=
  {x | {x} ∈ irreducibleComponents T}

/-- In a Noetherian space the points which are irreducible components form an open and closed
subset. -/
theorem isClopen_zeroDimensionalLocus [NoetherianSpace T] : IsClopen (zeroDimensionalLocus T) := by
  refine ⟨?_, ?_⟩
  · rw [show zeroDimensionalLocus T = ⋃ x ∈ zeroDimensionalLocus T, ({x} : Set T) by simp]
    exact ((NoetherianSpace.finite_irreducibleComponents (α := T)).preimage
      (Set.injOn_of_injective Set.singleton_injective)).isClosed_biUnion
      fun x hx => isClosed_of_mem_irreducibleComponents _ hx
  · exact isOpen_iff_forall_mem_open.mpr fun x hx => ⟨{x}, Set.singleton_subset_iff.mpr hx,
      isOpen_singleton_of_mem_irreducibleComponents hx, rfl⟩

/-- A strict specialization in a T₀ space gives Krull dimension at least one. -/
theorem one_le_topologicalKrullDim_of_specializes [T0Space T] {a b : T} (hab : a ⤳ b)
    (hne : a ≠ b) : 1 ≤ topologicalKrullDim T := by
  refine Order.one_le_krullDim_iff.mpr
    ⟨⟨closure {b}, isIrreducible_singleton.closure, isClosed_closure⟩,
      ⟨closure {a}, isIrreducible_singleton.closure, isClosed_closure⟩, ?_⟩
  refine lt_of_le_of_ne (specializes_iff_closure_subset.mp hab) fun h => hne ?_
  exact (hab.antisymm (specializes_iff_closure_subset.mpr
    (by simpa using (congrArg (fun Z : IrreducibleCloseds T => (Z : Set T)) h).symm.le))).eq

end Topology

section Scheme

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- At a point of a Jacobson scheme which is not itself an irreducible component, every open
neighbourhood contains a strict specialization. -/
theorem exists_specializes_ne_of_notMem_zeroDimensionalLocus [JacobsonSpace X] {x : X}
    (hx : x ∉ zeroDimensionalLocus X) {W : Set X} (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ a ∈ W, ∃ b ∈ W, a ⤳ b ∧ a ≠ b := by
  let Z := irreducibleComponent x
  have hZ : Z ∈ irreducibleComponents X := irreducibleComponent_mem_irreducibleComponents x
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  let η := hZ.1.genericPoint
  have hη : IsGenericPoint η Z := hZ.1.isGenericPoint_genericPoint hZc
  have hηx : η ⤳ x := hη.specializes mem_irreducibleComponent
  by_cases hne : η = x
  · -- `x` is the generic point of `Z`; some other point of `Z` lies in `W`.
    have hZx : Z ≠ {x} := fun h => hx (by change {x} ∈ irreducibleComponents X; rwa [← h])
    by_contra hcon
    push Not at hcon
    have hloc : ({x} : Set X) = W ∩ Z := by
      ext y
      constructor
      · rintro rfl
        exact ⟨hxW, mem_irreducibleComponent⟩
      · rintro ⟨hyW, hyZ⟩
        exact (hcon x hxW y hyW (hne ▸ hη.specializes hyZ)).symm
    exact hZx (by rw [← hη.def, hne,
      (isClosed_singleton_of_isLocallyClosed_singleton ⟨W, Z, hW, hZc, hloc⟩).closure_eq])
  · exact ⟨η, hηx.mem_open hW hxW, x, hxW, hηx, hne⟩

/-- At a point outside the zero-dimensional locus of a scheme of dimension at most one, locally
of finite type over a field, the local dimension is exactly one. -/
theorem topologicalKrullDimAt_eq_one [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) {x : X} (hx : x ∉ zeroDimensionalLocus X) :
    topologicalKrullDimAt X x = 1 := by
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  refine le_antisymm ?_ ?_
  · rw [topologicalKrullDimAt_eq_localKrullDim]
    exact (le_iSup (TopologicalSpace.localKrullDim X) x).trans
      ((topologicalKrullDim_eq_iSup_localKrullDim X).symm.le.trans hdim)
  · refine le_iInf fun W => ?_
    obtain ⟨a, haW, b, hbW, hab, hne⟩ :=
      exists_specializes_ne_of_notMem_zeroDimensionalLocus hx W.2.2 W.2.1
    exact one_le_topologicalKrullDim_of_specializes (T := W.1)
      (a := ⟨a, haW⟩) (b := ⟨b, hbW⟩) (Topology.IsInducing.subtypeVal.specializes_iff.mp hab)
      (fun h => hne (congrArg Subtype.val h))

/-- **The decomposition `X = X' ⊔ X''`.** A quasi-compact scheme locally of finite type over a
field `k` with `dim(X) ≤ 1` is covered by two complementary opens `U` and `V`, with `U` of
dimension at most zero, `V` equidimensional and of dimension one when nonempty, and both
inclusions closed immersions. -/
theorem exists_isCompl_zeroDimensional_equidimensional [LocallyOfFiniteType f] [QuasiCompact f]
    (hdim : topologicalKrullDim X ≤ 1) :
    ∃ U V : X.Opens, IsCompl U V ∧ IsClosedImmersion U.ι ∧ IsClosedImmersion V.ι ∧
      topologicalKrullDim U.toScheme ≤ 0 ∧ TopologicalSpace.Equidimensional V.toScheme ∧
      (Nonempty V.toScheme → topologicalKrullDim V.toScheme = 1) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  have hcl := isClopen_zeroDimensionalLocus (T := X)
  let U : X.Opens := ⟨zeroDimensionalLocus X, hcl.2⟩
  let V : X.Opens := ⟨(zeroDimensionalLocus X)ᶜ, hcl.1.isOpen_compl⟩
  have hUV : IsCompl U V := by
    refine ⟨disjoint_iff.mpr ?_, codisjoint_iff.mpr ?_⟩ <;> ext x <;> simp [U, V]
  refine ⟨U, V, hUV, ?_, ?_, ?_, ?_⟩
  · exact IsClosedImmersion.of_isPreimmersion U.ι (by rw [Scheme.Opens.range_ι]; exact hcl.1)
  · exact IsClosedImmersion.of_isPreimmersion V.ι
      (by rw [Scheme.Opens.range_ι]; exact hcl.2.isClosed_compl)
  · have : DiscreteTopology U.toScheme := by
      refine discreteTopology_iff_isOpen_singleton.mpr fun y => ?_
      have hy : ({y} : Set U.toScheme) = U.ι ⁻¹' {U.ι y} := by
        ext z
        simp [U.ι.isOpenEmbedding.injective.eq_iff]
      rw [hy]
      have hU : U.ι y ∈ zeroDimensionalLocus X := by
        have h := Set.mem_range_self (f := U.ι) y
        rwa [Scheme.Opens.range_ι] at h
      exact (isOpen_singleton_of_mem_irreducibleComponents hU).preimage U.ι.continuous
    exact topologicalKrullDim_zero_of_discreteTopology _
  · have hV : ∀ z : V.toScheme, topologicalKrullDimAt V.toScheme z = ((1 : ℕ) : WithBot ℕ∞) := by
      intro z
      rw [← V.ι.isOpenEmbedding.topologicalKrullDimAt_eq z]
      have hz : V.ι z ∉ zeroDimensionalLocus X := by
        have h := Set.mem_range_self (f := V.ι) z
        rwa [Scheme.Opens.range_ι] at h
      exact topologicalKrullDimAt_eq_one k f hdim hz
    have hcomp := (forall_topologicalKrullDimAt_eq_iff_forall_irreducibleComponents k V.toScheme
      (V.ι ≫ f)).mp hV
    refine ⟨fun W hW W' hW' => (hcomp W hW).trans (hcomp W' hW').symm, fun hne => ?_⟩
    rw [topologicalKrullDim_eq_iSup_localKrullDim]
    simp_rw [← topologicalKrullDimAt_eq_localKrullDim, hV]
    simp

/-- An open subscheme of a local complete intersection over `k` is one. -/
theorem isLocalCompleteIntersectionOverField_ι_comp (hf : IsLocalCompleteIntersectionOverField f)
    (U : X.Opens) : IsLocalCompleteIntersectionOverField (U.ι ≫ f) :=
  MorphismProperty.comp_mem (W := @Syntomic.{u}) _ _ (syntomic_of_isOpenImmersion U.ι) hf

/-- The non-smooth locus of an open subscheme is the trace of the non-smooth locus. -/
theorem finite_compl_smoothLocus_ι_comp [LocallyOfFinitePresentation f]
    (hfin : ((f.smoothLocus : Set X)ᶜ).Finite) (U : X.Opens) :
    (((U.ι ≫ f).smoothLocus : Set U.toScheme)ᶜ).Finite := by
  rw [← Scheme.Hom.preimage_smoothLocus_eq U.ι f, Scheme.Hom.coe_preimage, ← Set.preimage_compl]
  exact hfin.preimage U.ι.isOpenEmbedding.injective.injOn

end Scheme

end Deformation.Examples.Smoothing

end
