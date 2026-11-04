module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Irreducible.GenericPoints
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.UniversallyInjective

/-!
# Codimension-zero points and local finiteness along a flat morphism of finite type

The normalization of a scheme is defined only under the hypothesis that every quasi-compact
open has finitely many irreducible components, and the functoriality of the normalization
requires in addition that generic points of irreducible components be carried to generic
points of irreducible components. Both conditions ascend along a flat morphism locally of
finite type. For algebraic spaces these are the two conclusions of Tag 0GMD, whose first
condition is the one of Tag 0BB1 and whose second is Tag 0GMC; the statements proved here
are the representable cases of all three, in which — as Tag 0BB1 itself records — the
condition of Tag 0BB1 reads literally "every quasi-compact open has finitely many
irreducible components", and a point has codimension `0` exactly when it is the generic
point of an irreducible component.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.mem_genericPoints_of_flat`: a flat morphism of schemes carries generic
  points of irreducible components to generic points of irreducible components. This is the
  representable case of Tag 0GMC, and the second conclusion of Tag 0GMD in the representable
  case.
* `AlgebraicGeometry.finite_irreducibleComponents_of_flat_locallyOfFiniteType`: if every
  quasi-compact open of the target of a flat morphism locally of finite type has finitely
  many irreducible components, then so does every quasi-compact open of the source. This is
  the first conclusion of Tag 0GMD in the representable case.

## Implementation notes

Irreducible components of a scheme correspond to its generic points, so both statements are
proved by counting and transporting generic points. A flat morphism is generalizing, and a
generalizing map between sober spaces carries generic points to generic points; this gives
the second statement outright and is the first step of the first one. For the first
statement, over a generic point of the target the generic points of the source lying above
it are the generic points of the scheme-theoretic fibre, and the fibre of a morphism
locally of finite type over a field is a Noetherian scheme and so has finitely many of
them. This bounds the generic points of an affine piece of the source by a sigma type over
the generic points of the target, and a quasi-compact open is covered by finitely many such
pieces.

The hypothesis and conclusion of the first statement quantify over quasi-compact opens
rather than assuming the schemes themselves quasi-compact. That is what makes the statement
local, and what lets it be applied to the affine pieces of the covering during its own
proof.

## References

* [Stacks Project, Tag 0GMD](https://stacks.math.columbia.edu/tag/0GMD)
* [Stacks Project, Tag 0GMC](https://stacks.math.columbia.edu/tag/0GMC)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A generic point of an irreducible component of the source of a morphism of schemes is,
viewed in the scheme-theoretic fibre over its image, a generic point of an irreducible
component of that fibre. -/
@[ega "0 2.1.8" "partial, special case"]
lemma genericPoint_mem_fiber_of_genericPoint
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (hx : x ∈ genericPoints X)
    (η : S) (hη : f x = η) :
    (f.fiberHomeo η).symm ⟨x, by simp [hη]⟩ ∈ genericPoints (f.fiber η) := by
  let xη : f.fiber η := (f.fiberHomeo η).symm ⟨x, by simp [hη]⟩
  apply (mem_genericPoints_iff_forall_specializes_eq xη).2
  intro y hy
  have hxy : f.fiberι η y ⤳ x := by
    have := hy.map (f.fiberι η).continuous
    simpa [xη, Scheme.Hom.fiberι_fiberHomeo_symm] using this
  have heq : f.fiberι η y = x :=
    (mem_genericPoints_iff_forall_specializes_eq x).1 hx _ hxy
  apply (f.fiberι η).isEmbedding.injective
  simpa [xη, Scheme.Hom.fiberι_fiberHomeo_symm] using heq

/-- An affine scheme flat and locally of finite type over an affine scheme with finitely many
irreducible components has finitely many generic points. -/
lemma finite_genericPoints_of_flat_locallyOfFiniteType_affine
    {T S : Scheme.{u}} [IsAffine T] [IsAffine S] (f : T ⟶ S) [Flat f]
    [LocallyOfFiniteType f] (hS : (irreducibleComponents S).Finite) :
    (genericPoints T).Finite := by
  classical
  have hSg : (genericPoints S).Finite := genericPoints.finite hS
  have : Finite (genericPoints S) := hSg
  have hfg : ∀ η : genericPoints S, (genericPoints (f.fiber η.1)).Finite := by
    intro η
    have : LocallyOfFiniteType (f.fiberToSpecResidueField η.1) := by
      dsimp [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]
      infer_instance
    have : IsLocallyNoetherian (f.fiber η.1) :=
      LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField η.1)
    have : IsNoetherian (f.fiber η.1) := AlgebraicGeometry.IsNoetherian.mk
    exact genericPoints.finite finite_irreducibleComponents_of_isNoetherian
  have (η : genericPoints S) : Finite (genericPoints (f.fiber η.1)) := hfg η
  let g : genericPoints T → Σ η : genericPoints S, genericPoints (f.fiber η.1) := fun x =>
    let η : genericPoints S := ⟨f x.1,
      genericPoints_map_of_generalizingMap f (Flat.generalizingMap f) x.2⟩
    ⟨η, ⟨(f.fiberHomeo η.1).symm ⟨x.1, by simp [η]⟩,
      genericPoint_mem_fiber_of_genericPoint f x.1 x.2 η.1 rfl⟩⟩
  apply Finite.of_injective g
  intro x y h
  apply Subtype.ext
  simpa [g, Scheme.Hom.fiberι_fiberHomeo_symm] using
    congrArg (fun z : Σ η : genericPoints S, genericPoints (f.fiber η.1) =>
      f.fiberι z.1.1 z.2.1) h

/-- A generic point of an irreducible component of a scheme that lies in an open subscheme is
a generic point of an irreducible component of that open subscheme. -/
lemma genericPoints_of_open
    (X : Scheme.{u}) (U : X.Opens) (x : X) (hx : x ∈ U)
    (hgen : x ∈ genericPoints X) :
    (⟨x, hx⟩ : U.toScheme) ∈ genericPoints U.toScheme := by
  let y : U.toScheme := ⟨x, hx⟩
  have he := U.ι.isOpenEmbedding
  have hpre : U.ι ⁻¹' closure ({x} : Set X) = closure {y} := by
    rw [he.isOpenMap.preimage_closure_eq_closure_preimage he.continuous]
    congr 1
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    show z.1 = x ↔ z = y
    exact ⟨fun h => Subtype.ext h, congrArg Subtype.val⟩
  have hirr : U.ι ⁻¹' closure ({x} : Set X) ∈ irreducibleComponents U.toScheme :=
    preimage_mem_irreducibleComponents hgen he ⟨x, subset_closure (Set.mem_singleton _), y, rfl⟩
  show closure {y} ∈ irreducibleComponents U.toScheme
  rw [← hpre]
  exact hirr

/-- A scheme with finitely many generic points of irreducible components has finitely many
irreducible components. -/
private lemma finite_irreducibleComponents_of_finite_genericPoints
    (X : Scheme.{u}) (h : (genericPoints X).Finite) : (irreducibleComponents X).Finite := by
  have : Finite (genericPoints X) := h
  exact Finite.of_equiv (genericPoints X) (genericPoints.equiv (α := X))

/-- A scheme covered by finitely many open subschemes each with finitely many irreducible
components has finitely many irreducible components. -/
lemma finite_irreducibleComponents_of_finite_open_cover
    (X : Scheme.{u}) (ι : Type*) [Finite ι] (U : ι → X.Opens)
    (hcover : (Set.univ : Set X) ⊆ ⋃ i, (U i : Set X))
    (hfin : ∀ i, (irreducibleComponents (U i).toScheme).Finite) :
    (irreducibleComponents X).Finite := by
  classical
  have (i : ι) : Finite (genericPoints (U i).toScheme) := genericPoints.finite (hfin i)
  have chooseIndex : ∀ η : genericPoints X, ∃ i : ι, η.1 ∈ (U i : Set X) := by
    intro η
    exact Set.mem_iUnion.mp (hcover (Set.mem_univ _))
  choose i hi using chooseIndex
  let q : genericPoints X → Σ i : ι, genericPoints (U i).toScheme := fun η =>
    ⟨i η, ⟨⟨η.1, by simpa using hi η⟩,
      genericPoints_of_open X (U (i η)) η.1 (by simpa using hi η) η.2⟩⟩
  let ev : (Σ i : ι, genericPoints (U i).toScheme) → X := fun z => (U z.1).ι z.2.1
  have hfinite : (genericPoints X).Finite := by
    apply Finite.of_injective q
    intro η θ heq
    apply Subtype.ext
    calc
      η.1 = ev (q η) := rfl
      _ = ev (q θ) := congrArg ev heq
      _ = θ.1 := rfl
  exact finite_irreducibleComponents_of_finite_genericPoints X hfinite

/-- **Stacks Project, Tag 0GMC, representable case.** A flat morphism of schemes carries a
generic point of an irreducible component of its source to a generic point of an irreducible
component of its target. Equivalently, it carries codimension-zero points to
codimension-zero points, which is the second conclusion of Tag 0GMD. -/
@[stacks 0GMC "representable case"]
public theorem mem_genericPoints_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {x : X} (hx : x ∈ genericPoints X) : f x ∈ genericPoints Y :=
  genericPoints_map_of_generalizingMap f (Flat.generalizingMap f) hx

/-- **Stacks Project, Tag 0GMD, representable case.** Let `f : T ⟶ S` be a flat morphism of
schemes locally of finite type. If every quasi-compact open of `S` has finitely many
irreducible components, then so does every quasi-compact open of `T`. For a representable
algebraic space this is the condition of Tag 0BB1, so this is the first conclusion of Tag
0GMD in the representable case. -/
@[ega "IV 18.10.6" "more general"]
public theorem finite_irreducibleComponents_of_flat_locallyOfFiniteType
    {T S : Scheme.{u}} (f : T ⟶ S) [Flat f] [LocallyOfFiniteType f]
    (hS : ∀ V : S.Opens, IsCompact (V : Set S) →
      (irreducibleComponents V).Finite) :
    ∀ U : T.Opens, IsCompact (U : Set T) → (irreducibleComponents U).Finite := by
  intro U hU
  classical
  let W : Scheme.{u} := U.toScheme
  let g : W ⟶ S := U.ι ≫ f
  let I := {p : S.affineOpens × W.affineOpens // p.2.1 ≤ g ⁻¹ᵁ p.1.1}
  let A (i : I) : W.Opens := i.1.2.1
  have hcover : (Set.univ : Set W) ⊆ ⋃ i : I, (A i : Set W) := by
    intro x hx
    obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g x)) isOpen_univ
    let V : S.affineOpens := ⟨V₀, hV₀⟩
    obtain ⟨_, ⟨Z, hZ, rfl⟩, hxZ, hZW⟩ :=
      W.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ g ⁻¹ᵁ V.1 from hxV) (V.1.isOpen.preimage g.continuous)
    let i : I := ⟨(V, ⟨Z, hZ⟩), hZW⟩
    exact Set.mem_iUnion.mpr ⟨i, hxZ⟩
  have : CompactSpace W := isCompact_iff_compactSpace.mp (by simpa [W] using hU)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i : I => (A i : Set W)) (fun i => (A i).isOpen) hcover
  let J := {i : I // i ∈ t}
  let A' (i : J) : W.Opens := A i.1
  have hcover' : (Set.univ : Set W) ⊆ ⋃ i : J, (A' i : Set W) := by
    intro x hx
    obtain ⟨i, hit, hix⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact Set.mem_iUnion.mpr ⟨⟨i, hit⟩, hix⟩
  have hfin' : ∀ i : J, (irreducibleComponents (A' i).toScheme).Finite := by
    intro i
    let V : S.affineOpens := i.1.1.1
    let Z : W.affineOpens := i.1.1.2
    let hZV : Z.1 ≤ g ⁻¹ᵁ V.1 := i.1.2
    let q := g.resLE V.1 Z.1 hZV
    have hV : (irreducibleComponents V.1).Finite :=
      hS V.1 (by simpa using V.2.isCompact)
    have : Flat q := by dsimp [q]; infer_instance
    have : LocallyOfFiniteType q := by dsimp [q]; infer_instance
    exact finite_irreducibleComponents_of_finite_genericPoints _
      (finite_genericPoints_of_flat_locallyOfFiniteType_affine q hV)
  simpa [W] using finite_irreducibleComponents_of_finite_open_cover W J A' hcover' hfin'

end AlgebraicGeometry

end
