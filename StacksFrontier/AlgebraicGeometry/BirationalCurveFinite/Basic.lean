module

public import StacksFrontier.AlgebraicGeometry.ComponentDegrees.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksCore.Tactic.StacksAttribute

/-!
# A morphism of proper curves bijective on one-dimensional generic points is finite

Let `k` be a field and let `f : X' ⟶ X` be a morphism over `k` between schemes proper over `k`
of dimension at most one. If `f` carries the generic points of the one-dimensional irreducible
components of `X'` bijectively onto those of `X`, then `f` is finite.

This is the first step of the proof of [Stacks Project, Tag 0AYU], where it is the sentence
"the morphism `f` is proper and has fibres of dimension `≤ 0`, hence `f` is finite". The tag
itself asserts that `deg(f^*ℰ) = deg(ℰ)`; **this file proves only the finiteness**, and no
Stacks attribute is attached — see the implementation notes.

## Main results

* `Stacks.Topology.Dimension.topologicalKrullDim_le_zero_of_quasiSober_of_t1Space`: a sober `T1`
  space has Krull dimension at most zero.
* `Stacks.AlgebraicGeometry.BirationalCurveFinite.isClosed_singleton_of_notMem_genericPointsOne`:
  on a scheme of dimension at most one, a point which is not the generic point of a
  one-dimensional irreducible component is closed.
* `Stacks.AlgebraicGeometry.BirationalCurveFinite.isDiscrete_preimage_singleton`: under the
  bijection hypothesis every fibre of `f` is discrete.
* `Stacks.AlgebraicGeometry.BirationalCurveFinite.isFinite_of_bijOn_genericPointsOne`: `f` is
  finite.

## Implementation notes

The set of generic points of the one-dimensional components is
`Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne`, already in the tree; no second
name for it is introduced here.

The closedness of the remaining points splits into two cases, and only one of them is the
chain-of-three argument. If the point is not a generic point at all, its closure contains no
irreducible component — a component inside it would be forced to equal it by maximality, making
the point generic — and
`Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset` applies. If the
point *is* generic but its component is not one-dimensional, that component has dimension at most
zero and the point is closed in it, hence in the scheme. The second case is why the hypothesis is
non-membership of `genericPointsOne` rather than of `genericPoints`: a zero-dimensional
irreducible component is a closed point which *is* generic.

Discreteness of a fibre is likewise two cases. Over a point of `genericPointsOne X` the fibre is
a subsingleton: a point of it off `genericPointsOne X'` would be closed, and its image — closed,
because a proper morphism is closed — would make the target point closed and so of dimension
zero, contradicting membership; so the whole fibre lies in `genericPointsOne X'`, where the
bijection is injective. Over any other point the fibre is a closed set all of whose points are
closed, hence a Noetherian sober `T1` space, hence of dimension at most zero, hence finite and
discrete.

Finiteness is then [Stacks Project, Tag 02OH] in Mathlib's form
`AlgebraicGeometry.IsFinite.of_isProper_of_locallyQuasiFinite`, reached through
`AlgebraicGeometry.locallyQuasiFinite_iff_isDiscrete_preimage_singleton`. The fibre-dimension
phrasing `AlgebraicGeometry.isFinite_of_isProper_of_forall_topologicalKrullDim_fiber_le_zero`
would also serve, but it is stated for the scheme-theoretic fibre
`AlgebraicGeometry.Scheme.Hom.fiber` and the hypothesis available here is about the topological
preimage, so the discreteness route is shorter.

**No Stacks attribute is attached.** The conclusion of Tag 0AYU is the equality of degrees, whose
proof needs, beyond this finiteness, the comparison `Hⁿ(X', ℰ) ≅ Hⁿ(X, f_*ℰ)` along a finite
morphism (Tag 089W), the projection formula (Tag 01E8), additivity of Euler characteristics
(Tag 08AA, and through it the finite-dimensionality of Tag 02O6) and Tag 0AYT. None of those four
is available, so the tag is not closed and the attribute would be a weakening.

## References

* [Stacks Project, Tag 0AYU](https://stacks.math.columbia.edu/tag/0AYU)
* [Stacks Project, Tag 02OH](https://stacks.math.columbia.edu/tag/02OH)
* [Stacks Project, Tag 01RO](https://stacks.math.columbia.edu/tag/01RO)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.ComponentDegrees

universe u

namespace Stacks.Topology.Dimension

/-- **A sober `T1` space has Krull dimension at most zero.** Every irreducible closed subset is
the closure of a generic point, which in a `T1` space is that point, so the irreducible closed
subsets are the singletons and no two of them are comparable. -/
public theorem topologicalKrullDim_le_zero_of_quasiSober_of_t1Space {S : Type u}
    [TopologicalSpace S] [T1Space S] [QuasiSober S] : topologicalKrullDim S ≤ 0 := by
  refine Order.krullDim_nonpos_iff_forall_isMax.2 fun C D hCD => ?_
  obtain ⟨w, hw⟩ := QuasiSober.sober D.2 D.3
  have hDw : D.carrier = {w} := by
    rw [← isGenericPoint_def.1 hw, (isClosed_singleton (x := w)).closure_eq]
  obtain ⟨c, hc⟩ := C.2.1
  have hcD : c ∈ D.carrier := hCD hc
  rw [hDw, Set.mem_singleton_iff] at hcD
  show D.carrier ⊆ C.carrier
  rw [hDw, ← hcD]
  exact Set.singleton_subset_iff.2 hc

end Stacks.Topology.Dimension

namespace Stacks.AlgebraicGeometry.BirationalCurveFinite

/-! ### Closed points of a scheme of dimension at most one -/

/-- **On a scheme of dimension at most one, a point which is not the generic point of a
one-dimensional irreducible component is closed.** -/
@[ega "II 7.4.3" "partial"]
public theorem isClosed_singleton_of_notMem_genericPointsOne {X : Scheme.{u}}
    (hdim : topologicalKrullDim (X : Type u) ≤ 1) {x : X} (hx : x ∉ genericPointsOne X) :
    IsClosed ({x} : Set X) := by
  by_cases hgen : x ∈ genericPoints (X : Type u)
  · -- `x` is generic, so its component is not one-dimensional, hence zero-dimensional.
    have hne : topologicalKrullDim (closure ({x} : Set X)) ≠ 1 := fun h =>
      hx (mem_genericPointsOne_iff.mpr ⟨hgen, h⟩)
    have hle : topologicalKrullDim (closure ({x} : Set X)) ≤ 1 :=
      (topologicalKrullDim_subspace_le _ _).trans hdim
    have hz : topologicalKrullDim (closure ({x} : Set X)) ≤ 0 := by
      rcases lt_or_eq_of_le hle with h | h
      · cases hS : topologicalKrullDim (closure ({x} : Set X)) with
        | bot => exact bot_le
        | coe d =>
          have hd : d < (1 : ℕ∞) := by simpa [hS] using h
          exact_mod_cast (Order.le_of_lt_add_one (by simpa using hd) : d ≤ 0)
      · exact absurd h hne
    have hxmem : x ∈ closure ({x} : Set X) := subset_closure rfl
    have hsing : closure ({x} : Set X) = {x} := by
      refine Set.Subset.antisymm (fun y hy => ?_) subset_closure
      have hspec : x ⤳ y := specializes_iff_mem_closure.mpr hy
      have heq := Stacks.Topology.Dimension.eq_of_specializes_of_topologicalKrullDim_le_zero hz
        (x := (⟨x, hxmem⟩ : closure ({x} : Set X))) (y := ⟨y, hy⟩)
        ((Topology.IsInducing.subtypeVal (t := closure ({x} : Set X))).specializes_iff.mp hspec)
      exact (congrArg Subtype.val heq).symm
    rw [← hsing]
    exact isClosed_closure
  · -- `x` is not generic, so its closure contains no irreducible component.
    refine Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset
      hdim (T := closure ({x} : Set X)) isClosed_closure ?_ (subset_closure rfl)
    intro C hC hCsub
    have hmax := hC.2 ((isIrreducible_singleton (x := x)).closure) hCsub
    have hCeq : C = closure ({x} : Set X) := Set.Subset.antisymm hCsub hmax
    exact hgen (show closure ({x} : Set X) ∈ irreducibleComponents (X : Type u) from hCeq ▸ hC)

/-- **A closed subset of a Noetherian scheme all of whose points are closed is discrete.** It is
a Noetherian sober `T1` space, hence of dimension at most zero, hence finite. -/
@[ega "I 6.2.2" "more general"]
public theorem isDiscrete_of_forall_isClosed_singleton {X : Scheme.{u}} [IsNoetherian X]
    {s : Set X} (hs : IsClosed s) (hcl : ∀ x ∈ s, IsClosed ({x} : Set X)) :
    _root_.IsDiscrete s := by
  have : T1Space ↥s := ⟨fun x => by
    have hx : ({x} : Set ↥s) = Subtype.val ⁻¹' ({(x : X)} : Set X) := by
      ext y; simp [Subtype.ext_iff]
    rw [hx]
    exact (hcl x.1 x.2).preimage continuous_subtype_val⟩
  have : QuasiSober ↥s := hs.isClosedEmbedding_subtypeVal.quasiSober
  have hfin : (Set.univ : Set ↥s).Finite :=
    Stacks.Topology.Dimension.finite_of_topologicalKrullDim_le_zero
      Stacks.Topology.Dimension.topologicalKrullDim_le_zero_of_quasiSober_of_t1Space
  have : Finite ↥s := Set.finite_univ_iff.mp hfin
  exact _root_.isDiscrete_iff_discreteTopology.mpr Finite.instDiscreteTopology

/-! ### Fibres under the bijection hypothesis -/

/-- **A morphism which composes with a separated morphism to a proper one is proper.** The
properness of the source structure morphism transfers to the morphism over the base. -/
public theorem isProper_of_comp_eq {X' X Y : Scheme.{u}} {f : X' ⟶ X} {p : X ⟶ Y}
    {p' : X' ⟶ Y} [IsProper p'] [IsSeparated p] (hfOver : f ≫ p = p') : IsProper f :=
  have : IsProper (f ≫ p) := by rw [hfOver]; infer_instance
  IsProper.of_comp f p

section Fibres

variable (k : Type u) [Field k] {X' X : Scheme.{u}} (p' : X' ⟶ Spec (.of k))
  (p : X ⟶ Spec (.of k)) [IsProper p'] [IsProper p]

/-- **Over the generic point of a one-dimensional component, the fibre lies in the generic
points of the one-dimensional components of the source.** A fibre point off that set would be
closed, and its image under the closed map `f` would make the target point closed and so of
dimension zero. -/
public theorem preimage_singleton_subset_genericPointsOne
    (hdimX' : topologicalKrullDim (X' : Type u) ≤ 1) (f : X' ⟶ X) (hfOver : f ≫ p = p')
    {y : X} (hy : y ∈ genericPointsOne X) : f ⁻¹' {y} ⊆ genericPointsOne X' := by
  have : IsProper f := isProper_of_comp_eq hfOver
  intro x hx
  by_contra hxgen
  have hxclosed := isClosed_singleton_of_notMem_genericPointsOne hdimX' hxgen
  have himage : IsClosed (f.base '' ({x} : Set X')) := f.isClosedMap _ hxclosed
  have hyclosed : IsClosed ({y} : Set X) := by
    rw [Set.image_singleton, (Set.mem_singleton_iff.mp hx)] at himage
    simpa using himage
  have hdimy := (mem_genericPointsOne_iff.mp hy).2
  rw [hyclosed.closure_eq] at hdimy
  have hzero : topologicalKrullDim ({y} : Set X) ≤ 0 :=
    Stacks.Topology.Dimension.topologicalKrullDim_le_zero_of_quasiSober_of_t1Space
  rw [hdimy] at hzero
  norm_num at hzero

/-- **Every fibre of `f` is discrete.** -/
public theorem isDiscrete_preimage_singleton
    (hdimX' : topologicalKrullDim (X' : Type u) ≤ 1)
    (hdimX : topologicalKrullDim (X : Type u) ≤ 1)
    (f : X' ⟶ X) (hfOver : f ≫ p = p')
    (hbij : Set.BijOn f (genericPointsOne X') (genericPointsOne X)) (y : X) :
    _root_.IsDiscrete (f ⁻¹' {y}) := by
  have : IsProper f := isProper_of_comp_eq hfOver
  have : IsNoetherian X' := isNoetherian_of_isProper_over_field k p'
  by_cases hy : y ∈ genericPointsOne X
  · -- The fibre lies in `genericPointsOne X'`, where `f` is injective.
    have hsub := preimage_singleton_subset_genericPointsOne k p' p hdimX' f hfOver hy
    have hss : (f ⁻¹' {y}).Subsingleton := fun a ha b hb =>
      hbij.injOn (hsub ha) (hsub hb)
        ((Set.mem_singleton_iff.mp ha).trans (Set.mem_singleton_iff.mp hb).symm)
    have : Subsingleton ↥(f ⁻¹' {y}) := ⟨fun a b => Subtype.ext (hss a.2 b.2)⟩
    exact _root_.isDiscrete_iff_discreteTopology.mpr inferInstance
  · -- The fibre is a closed set of closed points.
    have hyclosed := isClosed_singleton_of_notMem_genericPointsOne hdimX hy
    refine isDiscrete_of_forall_isClosed_singleton (hyclosed.preimage f.continuous) ?_
    intro z hz
    refine isClosed_singleton_of_notMem_genericPointsOne hdimX' fun hzgen => ?_
    exact hy ((Set.mem_singleton_iff.mp hz) ▸ hbij.mapsTo hzgen)

/-- **A morphism over a field between schemes proper over it of dimension at most one which
carries the generic points of the one-dimensional components bijectively onto each other is
finite.** This is the first step of the proof of [Stacks Project, Tag 0AYU]; it is not the
tag, whose conclusion is an equality of degrees. -/
public theorem isFinite_of_bijOn_genericPointsOne
    (hdimX' : topologicalKrullDim (X' : Type u) ≤ 1)
    (hdimX : topologicalKrullDim (X : Type u) ≤ 1)
    (f : X' ⟶ X) (hfOver : f ≫ p = p')
    (hbij : Set.BijOn f (genericPointsOne X') (genericPointsOne X)) : IsFinite f :=
  have : IsProper f := isProper_of_comp_eq hfOver
  have : LocallyQuasiFinite f :=
    locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr
      (isDiscrete_preimage_singleton k p' p hdimX' hdimX f hfOver hbij)
  IsFinite.of_isProper_of_locallyQuasiFinite f

end Fibres

end Stacks.AlgebraicGeometry.BirationalCurveFinite

end
