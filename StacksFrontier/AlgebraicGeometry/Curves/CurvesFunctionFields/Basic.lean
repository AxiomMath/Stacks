module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension
public import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness of morphisms from proper curves

Let `X` be a proper scheme of dimension at most one over a field and let `Y` be separated over
that field. A morphism `X ⟶ Y` over the field is finite as soon as it does not contract any
one-dimensional irreducible component of `X` to a point.

## Main results

* `AlgebraicGeometry.isFinite_of_isProper_dimension_le_one_of_nontrivial_image_components` is
  the finiteness criterion.

## Implementation notes

The assertion that the image of a component has at least two points is expressed by
`Set.Nontrivial`. The structure morphisms and the equation saying that the given morphism is a
morphism over the field are explicit.

## References

* [Stacks Project, Tag 0CCL](https://stacks.math.columbia.edu/tag/0CCL)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- An irreducible subspace of a `T0` space whose Krull dimension is at most one has Krull
dimension exactly one as soon as it contains a point other than its generic point. -/
private lemma topologicalKrullDim_eq_one_of_irreducible_nontrivial
    {α : Type*} [TopologicalSpace α] [T0Space α] {s : Set α} {η : α}
    (hs : IsIrreducible s) (hη : η ∈ s) (hgeneric : IsGenericPoint η s)
    {z : α} (hz : z ∈ s) (hzn : z ≠ η)
    (hupper : topologicalKrullDim s ≤ 1) : topologicalKrullDim s = 1 := by
  have : IrreducibleSpace s := Subtype.irreducibleSpace hs
  let η' : s := ⟨η, hη⟩
  let z' : s := ⟨z, hz⟩
  let D : IrreducibleCloseds s :=
    ⟨closure ({z'} : Set s), isIrreducible_singleton.closure, isClosed_closure⟩
  let T : IrreducibleCloseds s :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ s, isClosed_univ⟩
  have hηnotD : η' ∉ (D : Set s) := by
    change η' ∉ closure ({z'} : Set s)
    rw [closure_subtype, Set.image_singleton]
    exact fun h ↦ hzn ((specializes_iff_mem_closure.mpr h).antisymm (hgeneric.specializes hz)).eq
  refine le_antisymm hupper ?_
  change 1 ≤ Order.krullDim (IrreducibleCloseds s)
  exact Order.one_le_krullDim_iff.mpr
    ⟨D, T, lt_iff_le_not_ge.mpr ⟨Set.subset_univ _, fun h ↦ hηnotD (h (Set.mem_univ _))⟩⟩

/-- A closed subset of a quasi-sober Noetherian space all of whose points are closed in the
ambient space is finite. -/
private lemma finite_of_isNoetherianSpace_and_all_points_closed
    {α : Type*} [TopologicalSpace α] [QuasiSober α] [NoetherianSpace α]
    (s : Set α) (hs : IsClosed s) (hclosed : ∀ x ∈ s, IsClosed ({x} : Set α)) : s.Finite := by
  obtain ⟨S, hSf, hSc, hSi, hsEq⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hs
  rw [hsEq]
  refine hSf.sUnion (fun t ht ↦ ?_)
  obtain ⟨η, hη⟩ := QuasiSober.sober (hSi t ht) (hSc t ht)
  have hηs : η ∈ s := hsEq ▸ Set.mem_sUnion_of_mem hη.mem ht
  rw [← hη.def, (hclosed η hηs).closure_eq]
  exact Set.finite_singleton η

/-- A morphism from a proper scheme of dimension at most one to a separated scheme over a
field is finite if the image of every one-dimensional irreducible component contains at least
two points. -/
@[stacks 0CCL]
lemma isFinite_of_isProper_dimension_le_one_of_nontrivial_image_components
    {k : Type u} [Field k] {X Y : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) [IsProper pX]
    (pY : Y ⟶ Spec (.of k)) [IsSeparated pY]
    (f : X ⟶ Y) (hf : f ≫ pY = pX)
    (hX : topologicalKrullDim X ≤ 1)
    (hcomponents : ∀ Z : irreducibleComponents X,
      topologicalKrullDim (Z : Set X) = 1 → (f '' (Z : Set X)).Nontrivial) :
    IsFinite f := by
  have : IsProper (f ≫ pY) := hf ▸ inferInstance
  have : IsProper f := IsProper.of_comp f pY
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pX
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace pX
  have : IsNoetherian X := IsNoetherian.mk
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace pX
  have hfiberFinite : ∀ y : Y, IsClosed ({y} : Set Y) → (f ⁻¹' {y}).Finite := by
    intro y hy
    refine finite_of_isNoetherianSpace_and_all_points_closed _ (hy.preimage f.continuous)
      fun x hx ↦ ?_
    have hxy : f x = y := by simpa using hx
    by_contra hnotclosed
    obtain ⟨z, hzW, hzx⟩ : (closure ({x} : Set X) \ {x}).Nonempty :=
      Set.sdiff_nonempty.mpr fun h ↦ hnotclosed (closure_subset_iff_isClosed.mp h)
    let W : IrreducibleCloseds X :=
      ⟨closure ({x} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
    have hWnotmin : ¬ IsMin W := by
      intro hmin
      let D : IrreducibleCloseds X :=
        ⟨closure ({z} : Set X), isIrreducible_singleton.closure, isClosed_closure⟩
      have hDW : D < W := by
        rw [lt_iff_le_not_ge]
        refine ⟨closure_minimal (Set.singleton_subset_iff.mpr hzW) W.isClosed, fun h ↦ ?_⟩
        have hxD : x ∈ (D : Set X) := h (subset_closure (by simp))
        have hxz : x ⤳ z := specializes_iff_mem_closure.mpr hzW
        have hzx' : z ⤳ x := specializes_iff_mem_closure.mpr hxD
        exact hzx ((hxz.antisymm hzx').eq.symm)
      exact (not_le_of_gt hDW) (hmin hDW.le)
    have hWmax : IsMax W := by
      change Order.krullDim (IrreducibleCloseds X) ≤ 1 at hX
      exact (Order.krullDim_le_one_iff.mp hX W).resolve_left hWnotmin
    have hWcomponent : (W : Set X) ∈ irreducibleComponents X := by
      rw [irreducibleComponents_eq_maximals_closed]
      refine ⟨⟨W.isClosed, W.isIrreducible⟩, fun V hV hWV ↦ ?_⟩
      exact hWmax (show W ≤ (⟨V, hV.2, hV.1⟩ : IrreducibleCloseds X) from hWV)
    let Z : irreducibleComponents X := ⟨(W : Set X), hWcomponent⟩
    have hdimZ : topologicalKrullDim (Z : Set X) = 1 :=
      topologicalKrullDim_eq_one_of_irreducible_nontrivial (η := x) Z.property.1
        (subset_closure (s := ({x} : Set X)) (Set.mem_singleton x)) isGenericPoint_closure hzW hzx
        ((topologicalKrullDim_subspace_le X (Z : Set X)).trans hX)
    have himage : f '' (Z : Set X) ⊆ {y} := by
      calc
        f '' (Z : Set X) = f '' closure ({x} : Set X) := rfl
        _ ⊆ closure (f '' ({x} : Set X)) := image_closure_subset_closure_image f.continuous
        _ = {y} := by simp [hxy]
    obtain ⟨a, ha, b, hb, hab⟩ := hcomponents Z hdimZ
    exact hab ((himage ha).trans (himage hb).symm)
  have hclosedPoint_quasiFinite : ∀ x ∈ closedPoints X, f.QuasiFiniteAt x := by
    intro x hx
    have hy : IsClosed ({f x} : Set Y) := by
      simpa only [Set.image_singleton] using f.isClosedMap _ (mem_closedPoints_iff.mp hx)
    have : Finite (f.fiber (f x)) := (f.fiberHomeo (f x)).finite_iff.mpr (hfiberFinite (f x) hy)
    exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)
  have hloc : f.quasiFiniteLocus = ⊤ := by
    refine top_unique fun x _ ↦ ?_
    by_contra hxnot
    obtain ⟨z, hz⟩ := nonempty_inter_closedPoints (Z := (f.quasiFiniteLocus : Set X)ᶜ)
      ⟨x, hxnot⟩ f.quasiFiniteLocus.2.isClosed_compl.isLocallyClosed
    exact hz.1 (by simpa [Scheme.Hom.mem_quasiFiniteLocus] using hclosedPoint_quasiFinite z hz.2)
  have : LocallyQuasiFinite f := (Scheme.Hom.quasiFiniteLocus_eq_top_iff (f := f)).mp hloc
  exact .of_isProper_of_locallyQuasiFinite f

end AlgebraicGeometry
