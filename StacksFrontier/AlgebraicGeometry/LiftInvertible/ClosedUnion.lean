module

public import StacksFrontier.AlgebraicGeometry.LiftInvertible.Factorization
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import StacksFrontier.AlgebraicGeometry.ClosedLift.Basic

/-!
# The closed union that reduces Tag 09NY to one patching statement

Let `i : Z ⟶ X` be a closed immersion, with `X` of Noetherian underlying space and
`topologicalKrullDim X ≤ 1`. Write `R = i (Z)` for the (closed) image.

The proof of [Stacks, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY) recorded in this
directory splits on how `R` meets the irreducible components of `X`, and two of the three cases
are proved: `R` containing **no** component
(`Stacks.LiftInvertible.exists_modulePullback_iso_of_not_irreducibleComponent_subset_range`) and
`R` containing **every** component, where `i` is onto
(`Stacks.LiftInvertible.exists_modulePullback_iso_of_surjective`). This file **removes the case
split altogether**, by enlarging `Z` instead of analysing it.

## The construction

Let `Y ⊆ X` be the union of the irreducible components of `X` **not** contained in `R`
(`Stacks.LiftInvertible.complementaryComponents`), a closed set because a Noetherian space has
finitely many components, and let

`closedUnionIdeal i = i.ker ⊓ vanishingIdeal Y`,

the ideal sheaf of the **scheme-theoretic union** of `Z` with the reduced induced subscheme on
`Y`. Three things are then true, and together they are the whole point:

* its support is **all of `X`**, because `V(I ⊓ J) = V(I) ∪ V(J)` and every component of `X`
  either lies in `R` or lies in `Y` (`Stacks.LiftInvertible.coe_support_closedUnionIdeal`).
  Hence the closed immersion of the union into `X` is **onto**, and the already-proved
  surjective case of Tag 09NY lifts invertible modules from the union to `X`;
* `Z` is a closed subscheme of the union (`Stacks.LiftInvertible.closedUnionLift`), because
  `closedUnionIdeal i ≤ i.ker`, and the factorization is literally `i`;
* `R ∩ Y` is **finite** (`Stacks.LiftInvertible.finite_range_inter_complementaryClosed`): a
  component not contained in `R` meets `R` in a proper closed subset of a one-dimensional
  irreducible space, which is a finite set of closed points.

So Tag 09NY for `i` follows, with **no hypothesis and no case analysis**, from Tag 09NY for the
single morphism `Z ⟶` the union — and there `Z` and the reduced `Y` cover the target with
intersection of ideal sheaves `⊥` *by construction of the union* and with **finite**
set-theoretic intersection. That is the Milnor-square situation, and it is the only thing still
owed. The case split is gone because `Y = ∅` recovers the surjective case and `Y = X` the
no-component case, with no appeal to which of them obtains.

## Main definitions

* `Stacks.LiftInvertible.complementaryComponents`: the union of the irreducible components of a
  space not contained in a given subset.
* `Stacks.LiftInvertible.complementaryClosed`: the same for the image of a morphism, as a
  `TopologicalSpace.Closeds`.
* `Stacks.LiftInvertible.closedUnionIdeal`: the ideal sheaf of the scheme-theoretic union.
* `Stacks.LiftInvertible.closedUnionLift`: `Z` as a closed subscheme of the union.

## Main results

* `Stacks.IdealSheafData.support_inf`: `V(I ⊓ J) = V(I) ∪ V(J)` for ideal sheaves. Mathlib has
  `support_sup` and `support_mul` but not this.
* `Stacks.LiftInvertible.coe_support_closedUnionIdeal` and
  `Stacks.LiftInvertible.surjective_subschemeι_closedUnionIdeal`: the union is all of `X`.
* `Stacks.LiftInvertible.finite_range_inter_complementaryClosed` and
  `Stacks.LiftInvertible.discreteTopology_range_inter_complementaryClosed`: the overlap is a
  finite discrete set of closed points.
* `Stacks.LiftInvertible.picPullbackSurjective_of_closedUnionLift` and
  `Stacks.LiftInvertible.exists_modulePullback_iso_of_closedUnionLift`: **the reduction**, in
  predicate form and in Tag 09NY's own `∃`-form.

## References

* [Stacks Project, Tag 09NY](https://stacks.math.columbia.edu/tag/09NY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Set TopologicalSpace Topology
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.IdealSheafData

open AlgebraicGeometry.Scheme.IdealSheafData

/-- **The support of an intersection of ideal sheaves is the union of the supports**, the ideal
sheaf form of `V(I ∩ J) = V(I) ∪ V(J)`.

Mathlib has `AlgebraicGeometry.Scheme.IdealSheafData.support_sup` (the support of a sum is the
*intersection* of the supports) and `support_mul` (the support of a product is the union), but
not this one. It follows from those two and antitonicity, since `I * J ≤ I ⊓ J ≤ I, J`
sandwiches the supports from both sides. -/
theorem support_inf {X : Scheme.{u}} (I J : X.IdealSheafData) :
    (I ⊓ J).support = I.support ⊔ J.support := by
  have h : I * J ≤ I ⊓ J := by
    refine le_inf (fun U ↦ ?_) (fun U ↦ ?_) <;> simp only [ideal_mul, Pi.mul_apply]
    · exact Ideal.mul_le_left
    · exact Ideal.mul_le_right
  refine le_antisymm ?_ (sup_le (support_antitone inf_le_left) (support_antitone inf_le_right))
  simpa only [support_mul] using support_antitone h

end Stacks.IdealSheafData

open Stacks.AlgebraicGeometry.Tag09NY (LiftsInvertibleModules)

namespace Stacks.LiftInvertible

open AlgebraicGeometry.Scheme.IdealSheafData

section Topological

variable (X : Type u) [TopologicalSpace X]

/-- **The union of the irreducible components of `X` not contained in `R`.** For `R` the image
of a closed immersion into a space of dimension at most one, this is the part of `X` that the
closed subscheme fails to fill out, and the two of them cover `X`. -/
def complementaryComponents (R : Set X) : Set X :=
  ⋃₀ {C | C ∈ irreducibleComponents X ∧ ¬ C ⊆ R}

/-- `complementaryComponents` is closed: a Noetherian space has finitely many irreducible
components, and each is closed. -/
theorem isClosed_complementaryComponents [NoetherianSpace X] (R : Set X) :
    IsClosed (complementaryComponents X R) := by
  have hfin : {C | C ∈ irreducibleComponents X ∧ ¬ C ⊆ R}.Finite :=
    NoetherianSpace.finite_irreducibleComponents.subset fun C hC ↦ hC.1
  exact hfin.isClosed_sUnion fun C hC ↦ isClosed_of_mem_irreducibleComponents C hC.1

/-- **`R` together with the components it misses covers the space**, with no hypothesis on `R` or
on `X`: a point lies in some irreducible component, and that component either lies in `R` — in
which case so does the point — or is one of the components making up
`complementaryComponents X R`. -/
theorem union_complementaryComponents (R : Set X) : R ∪ complementaryComponents X R = univ := by
  refine eq_univ_of_forall fun x ↦ ?_
  by_cases h : irreducibleComponent x ⊆ R
  · exact Or.inl (h mem_irreducibleComponent)
  · exact Or.inr ⟨irreducibleComponent x,
      ⟨irreducibleComponent_mem_irreducibleComponents x, h⟩, mem_irreducibleComponent⟩

/-- **A component not inside `R` meets `R` in a set containing no component at all.** If
`C ⊆ R ∩ C'` with `C` and `C'` irreducible components, then `C ⊆ C'`, so `C = C'` by maximality
of components, and then `C' ⊆ R` — contradicting `C' ⊄ R`.

This is what lets the one-dimensionality hypothesis bite on `R ∩ C'`, and it is the only place
maximality of irreducible components is used. -/
theorem not_irreducibleComponent_subset_inter (R : Set X) {C' : Set X}
    (hC' : C' ∈ irreducibleComponents X) (hC'R : ¬ C' ⊆ R) :
    ∀ C ∈ irreducibleComponents X, ¬ C ⊆ R ∩ C' := by
  intro C hC hsub
  have hCC' : C ⊆ C' := fun z hz ↦ (hsub hz).2
  have hC'C : C' ⊆ C := hC.2 hC'.1 hCC'
  exact hC'R fun y hy ↦ (hsub (hC'C hy)).1

/-- **Every point of the overlap is a closed point.** A point of `R ∩ complementaryComponents X R`
lies in `R ∩ C'` for some component `C' ⊄ R`, and that closed set contains no irreducible
component by `Stacks.LiftInvertible.not_irreducibleComponent_subset_inter`, so
`Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset` applies. No
soberness and no Noetherianness are needed. -/
theorem isClosed_singleton_of_mem_inter_complementaryComponents [T0Space X]
    (hdim : topologicalKrullDim X ≤ 1) (R : Set X) (hR : IsClosed R)
    {x : X} (hx : x ∈ R ∩ complementaryComponents X R) : IsClosed ({x} : Set X) := by
  obtain ⟨hxR, C', hC', hxC'⟩ := hx
  exact Stacks.Topology.Dimension.isClosed_singleton_of_not_irreducibleComponent_subset hdim
    (hR.inter (isClosed_of_mem_irreducibleComponents C' hC'.1))
    (not_irreducibleComponent_subset_inter X R hC'.1 hC'.2) ⟨hxR, hxC'⟩

/-- **The overlap is finite.** In a Noetherian sober `T0` space of Krull dimension at most one, a
closed set `R` meets the union of the components it does not contain in a finite set: component
by component, `R ∩ C'` contains no irreducible component
(`Stacks.LiftInvertible.not_irreducibleComponent_subset_inter`) so
`Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset` makes it finite, and a
Noetherian space has finitely many components. -/
theorem finite_inter_complementaryComponents [T0Space X] [NoetherianSpace X] [QuasiSober X]
    (hdim : topologicalKrullDim X ≤ 1) (R : Set X) (hR : IsClosed R) :
    (R ∩ complementaryComponents X R).Finite := by
  have hfin : {C | C ∈ irreducibleComponents X ∧ ¬ C ⊆ R}.Finite :=
    NoetherianSpace.finite_irreducibleComponents.subset fun C hC ↦ hC.1
  have hpiece : ∀ C' ∈ {C | C ∈ irreducibleComponents X ∧ ¬ C ⊆ R}, (R ∩ C').Finite := fun C' hC' ↦
    Stacks.Topology.Dimension.finite_of_not_irreducibleComponent_subset hdim
      (hR.inter (isClosed_of_mem_irreducibleComponents C' hC'.1))
      (not_irreducibleComponent_subset_inter X R hC'.1 hC'.2)
  refine (hfin.biUnion hpiece).subset ?_
  rintro x ⟨hxR, C', hC', hxC'⟩
  exact mem_biUnion hC' ⟨hxR, hxC'⟩

/-- The overlap is a discrete subspace: it is finite and `T1`, the latter because each of its
points is closed in the ambient space. -/
theorem discreteTopology_inter_complementaryComponents [T0Space X] [NoetherianSpace X]
    [QuasiSober X] (hdim : topologicalKrullDim X ≤ 1) (R : Set X) (hR : IsClosed R) :
    DiscreteTopology ((R ∩ complementaryComponents X R : Set X) : Set X) := by
  have _ : Finite ((R ∩ complementaryComponents X R : Set X) : Set X) :=
    (finite_inter_complementaryComponents X hdim R hR).to_subtype
  have _ : T1Space ((R ∩ complementaryComponents X R : Set X) : Set X) := by
    refine ⟨fun x ↦ ?_⟩
    have h := isClosed_singleton_of_mem_inter_complementaryComponents X hdim R hR x.2
    have he : ({x} : Set ((R ∩ complementaryComponents X R : Set X) : Set X))
        = Subtype.val ⁻¹' ({(x : X)} : Set X) := by
      ext y; simp [Subtype.ext_iff]
    rw [he]
    exact h.preimage continuous_subtype_val
  infer_instance

end Topological

variable {X Z : Scheme.{u}}

/-- **The closed set of components of `X` that `Z` does not fill out.** This is
`Stacks.LiftInvertible.complementaryComponents` at the image of `i`, packaged as a
`TopologicalSpace.Closeds` so that `vanishingIdeal` applies to it. -/
noncomputable def complementaryClosed (i : Z ⟶ X) [NoetherianSpace X] :
    Closeds (X : Type u) :=
  ⟨complementaryComponents (X : Type u) (Set.range i.base),
    isClosed_complementaryComponents _ _⟩

/-- **The ideal sheaf of the scheme-theoretic union of `Z` with the components it misses.** It is
`i.ker ⊓ vanishingIdeal (complementaryClosed i)`; taking the *intersection* of ideal sheaves is
what makes the corresponding closed subscheme the union of the two, and makes the Milnor-square
identity `𝒪 = 𝒪_Z ×_{𝒪_{Z ∩ Y}} 𝒪_Y` hold on it by construction rather than by hypothesis. -/
noncomputable def closedUnionIdeal (i : Z ⟶ X) [NoetherianSpace X] : X.IdealSheafData :=
  Scheme.Hom.ker i ⊓ vanishingIdeal (complementaryClosed i)

/-- The ideal sheaf of the union is contained in the kernel of `i`. -/
theorem closedUnionIdeal_le_ker (i : Z ⟶ X) [NoetherianSpace X] :
    closedUnionIdeal i ≤ Scheme.Hom.ker i := inf_le_left

/-- The ideal sheaf of the union is contained in the vanishing ideal of `complementaryClosed i`. -/
theorem closedUnionIdeal_le_vanishingIdeal (i : Z ⟶ X) [NoetherianSpace X] :
    closedUnionIdeal i ≤ vanishingIdeal (complementaryClosed i) := inf_le_right

/-- **The union is all of `X`.** Its support is `V(i.ker) ∪ Y`, which is the image of `i` union
the components that image misses, and those cover `X` by
`Stacks.LiftInvertible.union_complementaryComponents`.

This is the hypothesis of the already-proved surjective case of Tag 09NY, obtained with no
hypothesis on `i` beyond being a closed immersion — in particular with no dimension bound. -/
theorem coe_support_closedUnionIdeal (i : Z ⟶ X) [IsClosedImmersion i] [NoetherianSpace X] :
    ((closedUnionIdeal i).support : Set (X : Type u)) = univ := by
  rw [closedUnionIdeal, Stacks.IdealSheafData.support_inf]
  have h1 : ((Scheme.Hom.ker i).support : Set (X : Type u)) = Set.range i.base := by
    rw [Scheme.Hom.support_ker]
    exact (IsClosedImmersion.isClosedEmbedding i).isClosed_range.closure_eq
  have h2 : ((vanishingIdeal (complementaryClosed i)).support : Set (X : Type u))
      = complementaryComponents (X : Type u) (Set.range i.base) :=
    coe_support_vanishingIdeal _
  show ((Scheme.Hom.ker i).support : Set (X : Type u)) ∪ _ = univ
  rw [h1, h2]
  exact union_complementaryComponents _ _

/-- **The closed immersion of the union into `X` is onto**, by
`Stacks.LiftInvertible.coe_support_closedUnionIdeal` and
`AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι`. -/
theorem surjective_subschemeι_closedUnionIdeal (i : Z ⟶ X) [IsClosedImmersion i]
    [NoetherianSpace X] : Function.Surjective (closedUnionIdeal i).subschemeι.base := by
  rw [← Set.range_eq_univ]
  show Set.range (closedUnionIdeal i).subschemeι = univ
  rw [Scheme.IdealSheafData.range_subschemeι]
  exact coe_support_closedUnionIdeal i

/-- The kernel of the closed immersion of the union into `X` is contained in the kernel of `i`. -/
theorem ker_subschemeι_closedUnionIdeal_le (i : Z ⟶ X) [NoetherianSpace X] :
    (closedUnionIdeal i).subschemeι.ker ≤ Scheme.Hom.ker i := by
  rw [Scheme.IdealSheafData.ker_subschemeι]
  exact closedUnionIdeal_le_ker i

/-- **`Z` as a closed subscheme of the union.** The ideal sheaf of the union is contained in that
of `Z`, so `i` factors through it; `AlgebraicGeometry.IsClosedImmersion.lift` produces the
factorization and `Stacks.LiftInvertible.closedUnionLift_subschemeι` says it is one. -/
noncomputable def closedUnionLift (i : Z ⟶ X) [IsClosedImmersion i] [NoetherianSpace X] :
    Z ⟶ (closedUnionIdeal i).subscheme :=
  IsClosedImmersion.lift (closedUnionIdeal i).subschemeι i (ker_subschemeι_closedUnionIdeal_le i)

/-- The factorization `closedUnionLift i` composed with the closed immersion of the union into `X`
is `i`. -/
@[simp]
theorem closedUnionLift_subschemeι (i : Z ⟶ X) [IsClosedImmersion i] [NoetherianSpace X] :
    closedUnionLift i ≫ (closedUnionIdeal i).subschemeι = i :=
  IsClosedImmersion.lift_fac _ _ _

/-- **The overlap of `Z` with the components it misses is a finite set of closed points.** This
is `Stacks.LiftInvertible.finite_inter_complementaryComponents` at the image of a closed
immersion; it is the input that makes the outstanding patching problem a *Milnor* square, the
two closed pieces meeting in dimension zero. -/
theorem finite_range_inter_complementaryClosed (i : Z ⟶ X) [IsClosedImmersion i]
    [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1) :
    (Set.range i.base ∩ (complementaryClosed i : Set (X : Type u))).Finite :=
  finite_inter_complementaryComponents (X : Type u) hdim (Set.range i.base)
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range

/-- The overlap, as a subspace, is discrete. This is the shape in which
`Stacks.PicFinite.exists_isInvertible_modulePullback_iso` (Tag 0C0T) consumes it. -/
theorem discreteTopology_range_inter_complementaryClosed (i : Z ⟶ X) [IsClosedImmersion i]
    [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1) :
    DiscreteTopology
      ((Set.range i.base ∩ (complementaryClosed i : Set (X : Type u))) : Set (X : Type u)) :=
  discreteTopology_inter_complementaryComponents (X : Type u) hdim (Set.range i.base)
    (IsClosedImmersion.isClosedEmbedding i).isClosed_range

/-- **Tag 09NY reduces, with no case analysis, to Tag 09NY for the closed union.** For a closed
immersion `i : Z ⟶ X` into a scheme whose underlying space is Noetherian of dimension at most
one, if every invertible module on `Z` is the pullback of an invertible module on the
scheme-theoretic union of `Z` with the components of `X` that `Z` misses, then every invertible
module on `Z` is the pullback of an invertible module on `X`.

The union has the same underlying space as `X`
(`Stacks.LiftInvertible.surjective_subschemeι_closedUnionIdeal`), so the already-proved
surjective case of Tag 09NY lifts from the union to `X`, and
`Stacks.AlgebraicGeometry.Tag09NY.LiftsInvertibleModules.comp` composes the two steps.

The tag is withheld: `LiftsInvertibleModules (closedUnionLift i)` is a hypothesis here, and it is
precisely what Tag 09NY still owes. -/
theorem picPullbackSurjective_of_closedUnionLift (i : Z ⟶ X) [IsClosedImmersion i]
    [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1)
    (h : LiftsInvertibleModules (closedUnionLift i)) : LiftsInvertibleModules i :=
  closedUnionLift_subschemeι i ▸ picPullbackSurjective_comp_of_surjective (closedUnionLift i)
    (closedUnionIdeal i).subschemeι (surjective_subschemeι_closedUnionIdeal i) hdim h

/-- **The reduction in Tag 09NY's own form.** The tag is withheld for the reason given on
`Stacks.LiftInvertible.picPullbackSurjective_of_closedUnionLift`. -/
theorem exists_modulePullback_iso_of_closedUnionLift (X Z : Scheme.{u}) (i : Z ⟶ X)
    [IsClosedImmersion i] [NoetherianSpace X] (hdim : topologicalKrullDim X ≤ 1)
    (h : LiftsInvertibleModules (closedUnionLift i))
    (L : SheafOfModules.{u} (structureSheafRing Z.toRingedSpace))
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible Z.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) Z.IsSheaf) L) :
    ∃ (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
      (_ : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) M),
      Nonempty ((modulePullback i.toLRSHom.toShHom).obj M ≅ L) :=
  let ⟨M, hM, hiso⟩ := picPullbackSurjective_of_closedUnionLift i hdim h L hL
  ⟨M, hM, hiso⟩

end Stacks.LiftInvertible

end
