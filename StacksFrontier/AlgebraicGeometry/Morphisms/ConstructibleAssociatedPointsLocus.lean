module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Properties.Constructible
public import StacksFrontier.Topology.Constructible.InConstructible
public import StacksFrontier.Topology.Noetherian.ConstructibleDichotomy
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The locus where the associated points of a fibre lie in an open subscheme

Let `f : X ⟶ Y` be a morphism of schemes, let `F` be an `𝒪_X`-module and let `U ⊆ X` be an
open subscheme. This file studies the subset

`E = {y : Y | Ass(F_y) ⊆ U_y}`

of the base, where `F_y` is the pullback of `F` to the scheme-theoretic fibre `X_y` and `U_y`
is the inverse image of `U` in that fibre. Two independent halves of the argument that `E` is
locally constructible are provided.

The first half is a description of `E`: its complement is exactly the image under `f` of the
part of the relative assassin `Ass_{X/Y}(F)` lying outside `U`. So `E` is locally constructible
precisely when that image is, which is the form in which Chevalley-type theorems apply.

The second half is the topological criterion that the Stacks proof applies to `E` once the base
has been reduced to a Noetherian scheme: a subset of a locally Noetherian scheme is locally
constructible as soon as, on every irreducible closed subset `Z`, it either contains a nonempty
open of `Z` or is avoided by one. The hypothesis is phrased a second time in terms of the
generic point of `Z`, which is the shape in which the spreading-out lemmas (Stacks 05KN and
05KP) deliver it.

## Main results

* `Topology.IsLocallyConstructible.compl`: locally constructible sets are closed under
  complement.
* `Topology.isConstructible_of_open_dichotomy` and
  `Topology.isConstructible_preimage_val_of_open_dichotomy`: the dichotomy criterion on a
  Noetherian space, and on a Noetherian open subspace of an arbitrary space.
* `AlgebraicGeometry.isLocallyConstructible_of_open_dichotomy` and
  `AlgebraicGeometry.isLocallyConstructible_of_isGenericPoint_dichotomy`: the criterion on a
  locally Noetherian scheme.
* `Stacks.Divisors.mem_associatedPoints_fiber_iff_mem_relativeAssassin`: a point of a fibre is
  associated to the restricted module exactly when its image lies in the relative assassin.
* `Stacks.Divisors.compl_setOf_associatedPoints_fiber_subset`: the complement of `E` is the
  image of `Ass_{X/Y}(F) \ U`.
* `Stacks.Divisors.isLocallyConstructible_setOf_associatedPoints_fiber_subset_iff`: `E` is
  locally constructible exactly when that image is.

## Implementation notes

The dichotomy itself is Stacks tag 053Z,
`constructible_iff_dichotomy_irreducible_closed`, which is stated for the explicit
finite-union predicate `IsConstructibleSet`; `isConstructible_of_isConstructibleSet` is the
bridge to Mathlib's Boolean-algebra definition, and needs no hypothesis on the space.

The passage from a Noetherian space to a locally Noetherian scheme uses irreducibility twice:
an irreducible closed subset `Z'` of an open `U` is replaced by its closure `Z` in the ambient
space, and a nonempty open of `Z` automatically meets the dense subset `Z'`.

The hypothesis of the generic-point form is split into two implications rather than stated as a
disjunction, so that the two spreading-out lemmas can be supplied independently.

## References

* [Stacks Project, Tag 053Z](https://stacks.math.columbia.edu/tag/053Z)
* [Stacks Project, Tag 05AT](https://stacks.math.columbia.edu/tag/05AT)
* [Stacks Project, Tag 05KR](https://stacks.math.columbia.edu/tag/05KR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Topology TopologicalSpace
open scoped Set.Notation

universe u


section GeneralTopology

variable {X : Type*} [TopologicalSpace X]

namespace Topology

/-- The complement of a locally constructible set is locally constructible: constructibility in
a fixed open neighbourhood is preserved by complementation there. -/
theorem IsLocallyConstructible.compl {E : Set X} (hE : IsLocallyConstructible E) :
    IsLocallyConstructible Eᶜ := fun x => by
  obtain ⟨U, hxU, hU, hUE⟩ := hE x
  exact ⟨U, hxU, hU, by simpa using hUE.compl⟩

/-- **Stacks 053Z, applied form.** On a Noetherian space a subset `E` is constructible as soon
as every irreducible closed `Z` carries a nonempty open subset either contained in `E` or
disjoint from `E`. -/
theorem isConstructible_of_open_dichotomy [NoetherianSpace X] {E : Set X}
    (h : ∀ Z : Set X, IsIrreducible Z → IsClosed Z →
      (∃ V : Set X, IsOpen V ∧ (V ∩ Z).Nonempty ∧ V ∩ Z ⊆ E) ∨
      (∃ V : Set X, IsOpen V ∧ (V ∩ Z).Nonempty ∧ Disjoint (V ∩ Z) E)) :
    IsConstructible E := by
  refine isConstructible_of_isConstructibleSet
    ((constructible_iff_dichotomy_irreducible_closed E).2 fun Z hZ hZc => ?_)
  rcases h Z hZ hZc with ⟨V, hVo, hVne, hVE⟩ | ⟨V, hVo, hVne, hVd⟩
  · exact Or.inl ⟨V, hVo, hVne, fun z hz => ⟨hVE hz, hz.2⟩⟩
  · refine Or.inr fun hd => ?_
    obtain ⟨v, hvV, hvZ⟩ := hVne
    obtain ⟨w, hwV, hwE, hwZ⟩ := mem_closure_iff.1 (hd hvZ) V hVo hvV
    exact Set.disjoint_left.1 hVd ⟨hwV, hwZ⟩ hwE

/-- The dichotomy criterion localized: if the alternative holds on every irreducible closed
subset of `X`, then `E` is constructible inside every subspace `U` that is a Noetherian space.

An irreducible closed subset `Z'` of `U` is handled through its closure `Z` in `X`: a nonempty
open subset of `Z` meets the dense subset `Z'`, and `Z' ⊆ Z`. -/
@[ega "0 9.2.3" "partial", sga "1 IV 6.1" "sufficiency"]
theorem isConstructible_preimage_val_of_open_dichotomy {E U : Set X} [NoetherianSpace U]
    (h : ∀ Z : Set X, IsIrreducible Z → IsClosed Z →
      (∃ V : Set X, IsOpen V ∧ (V ∩ Z).Nonempty ∧ V ∩ Z ⊆ E) ∨
      (∃ V : Set X, IsOpen V ∧ (V ∩ Z).Nonempty ∧ Disjoint (V ∩ Z) E)) :
    IsConstructible (U ↓∩ E) := by
  refine isConstructible_of_open_dichotomy fun Z' hZ' hZ'c => ?_
  have hZ : ∀ V : Set X, (U ↓∩ V) ∩ Z' = U ↓∩ (V ∩ closure ((Subtype.val : U → X) '' Z')) :=
    fun V => by
      rw [Set.preimage_inter, ← IsInducing.subtypeVal.closure_eq_preimage_closure_image,
        hZ'c.closure_eq]
  have key : ∀ V : Set X, IsOpen V → (V ∩ closure ((Subtype.val : U → X) '' Z')).Nonempty →
      ((U ↓∩ V) ∩ Z').Nonempty := by
    rintro V hVo ⟨z, hzV, hzc⟩
    obtain ⟨w, hwV, ⟨w', hw'Z, rfl⟩⟩ := mem_closure_iff.1 hzc V hVo hzV
    exact ⟨w', hwV, hw'Z⟩
  rcases h _ (hZ'.image _ continuous_subtype_val.continuousOn).closure isClosed_closure with
    ⟨V, hVo, hVne, hVE⟩ | ⟨V, hVo, hVne, hVd⟩
  · exact Or.inl ⟨U ↓∩ V, hVo.preimage continuous_subtype_val, key V hVo hVne,
      (hZ V).trans_subset (Set.preimage_mono hVE)⟩
  · exact Or.inr ⟨U ↓∩ V, hVo.preimage continuous_subtype_val, key V hVo hVne,
      (hZ V).symm ▸ hVd.preimage _⟩

end Topology

end GeneralTopology

namespace AlgebraicGeometry

/-- On a locally Noetherian scheme a subset `E` is locally constructible as soon as every
irreducible closed subset `Z` carries a nonempty open subset either contained in `E` or disjoint
from `E`: the affine opens of such a scheme are Noetherian spaces. -/
theorem isLocallyConstructible_of_open_dichotomy {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    {E : Set Y}
    (h : ∀ Z : Set Y, IsIrreducible Z → IsClosed Z →
      (∃ V : Set Y, IsOpen V ∧ (V ∩ Z).Nonempty ∧ V ∩ Z ⊆ E) ∨
      (∃ V : Set Y, IsOpen V ∧ (V ∩ Z).Nonempty ∧ Disjoint (V ∩ Z) E)) :
    IsLocallyConstructible E := by
  rw [isLocallyConstructible_iff_forall_affineOpens]
  intro U
  have : IsNoetherianRing Γ(Y, U.1) := IsLocallyNoetherian.component_noetherian U
  have : NoetherianSpace (U.1 : Set Y) := noetherianSpace_of_isAffineOpen U.1 U.2
  exact Topology.isConstructible_preimage_val_of_open_dichotomy h

/-- The generic-point form of the criterion, which is the shape in which spreading-out lemmas
supply it: on a locally Noetherian scheme it is enough to know, for the generic point `η` of
each irreducible closed `Z`, that membership of `η` in `E` spreads to a nonempty open of `Z`
and that non-membership spreads to a nonempty open of `Z` as well. -/
theorem isLocallyConstructible_of_isGenericPoint_dichotomy {Y : Scheme.{u}}
    [IsLocallyNoetherian Y] {E : Set Y}
    (hmem : ∀ (Z : Set Y) (η : Y), IsIrreducible Z → IsClosed Z → IsGenericPoint η Z → η ∈ E →
      ∃ V : Set Y, IsOpen V ∧ (V ∩ Z).Nonempty ∧ V ∩ Z ⊆ E)
    (hnmem : ∀ (Z : Set Y) (η : Y), IsIrreducible Z → IsClosed Z → IsGenericPoint η Z → η ∉ E →
      ∃ V : Set Y, IsOpen V ∧ (V ∩ Z).Nonempty ∧ Disjoint (V ∩ Z) E) :
    IsLocallyConstructible E := by
  refine isLocallyConstructible_of_open_dichotomy fun Z hZ hZc => ?_
  obtain ⟨η, hη⟩ := QuasiSober.sober hZ hZc
  by_cases hηE : η ∈ E
  · exact Or.inl (hmem Z η hZ hZc hη hηE)
  · exact Or.inr (hnmem Z η hZ hZc hη hηE)

end AlgebraicGeometry

namespace Stacks.Divisors

variable {X Y : Scheme.{u}}

/-- A point of the scheme-theoretic fibre over `y` is associated to the restriction of `F` to
that fibre exactly when its image in `X` lies in the relative assassin `Ass_{X/Y}(F)`.

The nontrivial direction uses that a point of `X` lies over at most one point of `Y`, so the
fibre witnessing membership in the relative assassin is the fibre over `y` itself. -/
theorem mem_associatedPoints_fiber_iff_mem_relativeAssassin (f : X ⟶ Y) (F : X.Modules) (y : Y)
    (x : f.fiber y) :
    x ∈ associatedPoints ((Scheme.Modules.pullback (f.fiberι y)).obj F) ↔
      f.fiberι y x ∈ relativeAssassin f F := by
  rw [mem_relativeAssassin]
  refine ⟨fun hx => ⟨y, x, hx, rfl⟩, ?_⟩
  rintro ⟨t, z, hz, hxz⟩
  have ht : t = y :=
    (f.apply_fiberι t z).symm.trans ((congrArg f hxz).trans (f.apply_fiberι y x))
  subst t
  exact (f.fiberι y).isEmbedding.injective hxz ▸ hz

/-- The complement of the locus `{y | Ass(F_y) ⊆ U_y}` is the image under `f` of the part of the
relative assassin `Ass_{X/Y}(F)` lying outside `U`.

Indeed a point `y` fails to lie in the locus exactly when some associated point of `F_y` has
image outside `U`, and the image of a point of the fibre over `y` is a point of `X` lying over
`y`. -/
theorem compl_setOf_associatedPoints_fiber_subset (f : X ⟶ Y) (F : X.Modules) (U : X.Opens) :
    {y : Y | associatedPoints ((Scheme.Modules.pullback (f.fiberι y)).obj F) ⊆
        f.fiberι y ⁻¹' (U : Set X)}ᶜ = f '' (relativeAssassin f F \ (U : Set X)) := by
  ext y
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.not_subset, Set.mem_image,
    Set.mem_sdiff, mem_relativeAssassin]
  constructor
  · rintro ⟨x, hx, hxU⟩
    exact ⟨f.fiberι y x, ⟨⟨y, x, hx, rfl⟩, hxU⟩, f.apply_fiberι y x⟩
  · rintro ⟨x, ⟨⟨s, z, hz, rfl⟩, hxU⟩, hfx⟩
    rw [f.apply_fiberι s z] at hfx
    subst hfx
    exact ⟨z, hz, hxU⟩

/-- The locus `{y | Ass(F_y) ⊆ U_y}` is locally constructible exactly when the image under `f`
of `Ass_{X/Y}(F) \ U` is: the two sets are complementary, and locally constructible subsets are
closed under complement. -/
theorem isLocallyConstructible_setOf_associatedPoints_fiber_subset_iff
    (f : X ⟶ Y) (F : X.Modules) (U : X.Opens) :
    IsLocallyConstructible {y : Y | associatedPoints ((Scheme.Modules.pullback (f.fiberι y)).obj F)
        ⊆ f.fiberι y ⁻¹' (U : Set X)} ↔
      IsLocallyConstructible (f '' (relativeAssassin f F \ (U : Set X))) := by
  rw [← compl_setOf_associatedPoints_fiber_subset]
  exact ⟨fun h => h.compl, fun h => by simpa using h.compl⟩

end Stacks.Divisors

end
