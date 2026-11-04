module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.Limits.Descending.ConstructibleImage
public import StacksFrontier.AlgebraicGeometry.Limits.FinitePresentationDescent

/-!
# Base change of a directed inverse system of schemes, indexed by the directed set

An inverse system of schemes indexed by a directed set `I` is a functor `Iᵒᵖ ⥤ Scheme`. Its
base change along a scheme `P` over the stage `S_i` is, in the library, indexed by the objects
of `Iᵒᵖ` lying over `op i`: that is `AlgebraicGeometry.Scheme.baseChangeDiagram`, and
`AlgebraicGeometry.Scheme.isLimitBaseChangeCone` exhibits `P ×_{S_i} S` as its limit. The
over category is cofiltered but it is not a directed set, so the base-changed system in that
form cannot be fed to the results about directed systems — in particular not to Tag 05F4,
`AlgebraicGeometry.eventually_range_transition_subset_of_isLocallyConstructible`, which
consumes an `AlgebraicGeometry.DescentSituation` over a preorder.

This file reindexes the base-changed system by the directed set `{k : I // i ≤ k}` of indices
above `i`, which is what the source means by "the directed set", and transports the limit
property to the reindexed system.

## Main definitions

* `AlgebraicGeometry.aboveToOver` is the comparison functor `{k : I // i ≤ k}ᵒᵖ ⥤ Over (op i)`,
  and `AlgebraicGeometry.aboveOverEquiv` says it is an equivalence.
* `AlgebraicGeometry.directedBaseChangeDiagram` is the base-changed system indexed by
  `{k : I // i ≤ k}ᵒᵖ`, `AlgebraicGeometry.directedBaseChangeCone` the cone over it with apex
  `P ×_{S_i} S`, and `AlgebraicGeometry.isLimitDirectedBaseChangeCone` the proof that this cone
  is limiting.
* `AlgebraicGeometry.directedBaseChangeDescentSituation` packages the system, the cone and the
  limit property as a `DescentSituation` over the directed set `{k : I // i ≤ k}`, which is the
  form Tag 05F4 and the results about directed systems take.

## Implementation notes

The comparison functor is an equivalence for an entirely formal reason: an object of `Iᵒᵖ` over
`op i` is an index `k` together with a morphism `op k ⟶ op i`, that is with a proof of `i ≤ k`,
and all the hom sets in sight are subsingletons because `I` is a preorder. So the functor is
full and faithful by `Subsingleton.elim` and essentially surjective by eta for the opposite
category, and the limit transports by
`CategoryTheory.Limits.IsLimit.whiskerEquivalence`.

Compactness and quasi-separatedness of the stages of the base-changed system are hypotheses of
`AlgebraicGeometry.directedBaseChangeDescentSituation` rather than derived: in the intended
application every stage is affine, and that is where they come from.

## References

* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
* [Stacks Project, Tag 05F4](https://stacks.math.columbia.edu/tag/05F4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

section Directed

variable {I : Type u} [Preorder I]

/-- The indices above a fixed index of a directed set form a directed set. -/
public instance isDirected_subtype_le [IsDirected I (· ≤ ·)] (i : I) :
    IsDirected {k : I // i ≤ k} (· ≤ ·) :=
  ⟨fun a b => by
    obtain ⟨cc, hac, hbc⟩ := exists_ge_ge a.1 b.1
    exact ⟨⟨cc, a.2.trans hac⟩, hac, hbc⟩⟩

/-- The indices above a fixed index are nonempty, that index being one of them. -/
public instance nonempty_subtype_le (i : I) : Nonempty {k : I // i ≤ k} := ⟨⟨i, le_refl i⟩⟩

/-- The comparison functor sending an index `k ≥ i`, taken opposite, to the object `op k` of
`Iᵒᵖ` over `op i`. -/
public def aboveToOver (i : I) : {k : I // i ≤ k}ᵒᵖ ⥤ Over (op i) where
  obj k := Over.mk (homOfLE k.unop.2).op
  map {k k'} f :=
    Over.homMk (homOfLE (show k'.unop.1 ≤ k.unop.1 from leOfHom f.unop)).op
      (Subsingleton.elim _ _)
  map_id _ := by ext; exact Subsingleton.elim _ _
  map_comp _ _ := by ext; exact Subsingleton.elim _ _

/-- Morphisms between objects of `Iᵒᵖ` over `op i` are determined by their sources and targets,
`I` being a preorder. -/
private theorem over_hom_eq {i : I} {A B : Over (op i)} (a b : A ⟶ B) : a = b := by
  ext
  exact Subsingleton.elim _ _

/-- The functor `aboveToOver i` is faithful. -/
public instance (i : I) : (aboveToOver i).Faithful where
  map_injective {_ _} {a b} _ := Subsingleton.elim a b

/-- The functor `aboveToOver i` is full. -/
public instance (i : I) : (aboveToOver i).Full where
  map_surjective {k k'} g :=
    ⟨(homOfLE (show k'.unop ≤ k.unop from leOfHom g.left.unop)).op, over_hom_eq _ _⟩

/-- The functor `aboveToOver i` is essentially surjective. -/
public instance (i : I) : (aboveToOver i).EssSurj where
  mem_essImage A :=
    ⟨op ⟨A.left.unop, leOfHom A.hom.unop⟩,
      ⟨Over.isoMk (Iso.refl _) (Subsingleton.elim _ _)⟩⟩

/-- The functor `aboveToOver i` is an equivalence of categories. -/
public instance (i : I) : (aboveToOver i).IsEquivalence where

/-- The indices above `i`, taken opposite, are equivalent to the objects of `Iᵒᵖ` over
`op i`. -/
public def aboveOverEquiv (i : I) : {k : I // i ≤ k}ᵒᵖ ≌ Over (op i) :=
  (aboveToOver i).asEquivalence

variable (D : Iᵒᵖ ⥤ Scheme.{u}) (i : I) {P : Scheme.{u}} (w : P ⟶ D.obj (op i))

/-- The base change of the inverse system `D` along `w`, reindexed by the indices above `i`:
its value at `k ≥ i` is `P ×_{S_i} S_k`. -/
public def directedBaseChangeDiagram : {k : I // i ≤ k}ᵒᵖ ⥤ Scheme.{u} :=
  (aboveOverEquiv i).functor ⋙ Scheme.baseChangeDiagram D (op i) (Over.mk w)

/-- The value of the reindexed base-changed system at `k ≥ i` is `P ×_{S_i} S_k`. -/
public theorem directedBaseChangeDiagram_obj (k : {k : I // i ≤ k}) :
    (directedBaseChangeDiagram D i w).obj (op k) =
      pullback (D.map (homOfLE k.2).op) w :=
  rfl

/-- On the `D`-component the transition morphisms of the reindexed base-changed system are the
transition morphisms of `D`. -/
@[reassoc]
public theorem directedBaseChangeDiagram_map_fst {k k' : {k : I // i ≤ k}ᵒᵖ}
    (e : k ⟶ k') :
    (directedBaseChangeDiagram D i w).map e ≫
        pullback.fst (D.map (homOfLE k'.unop.2).op) w =
      pullback.fst (D.map (homOfLE k.unop.2).op) w ≫
        D.map (homOfLE (show k'.unop.1 ≤ k.unop.1 from leOfHom e.unop)).op :=
  Scheme.baseChangeDiagram_map_fst D (op i) (Over.mk w) ((aboveOverEquiv i).functor.map e)

/-- On the `P`-component the transition morphisms of the reindexed base-changed system are the
identity. -/
@[reassoc]
public theorem directedBaseChangeDiagram_map_snd {k k' : {k : I // i ≤ k}ᵒᵖ}
    (e : k ⟶ k') :
    (directedBaseChangeDiagram D i w).map e ≫
        pullback.snd (D.map (homOfLE k'.unop.2).op) w =
      pullback.snd (D.map (homOfLE k.unop.2).op) w :=
  Scheme.baseChangeDiagram_map_snd D (op i) (Over.mk w) ((aboveOverEquiv i).functor.map e)

/-- The transition morphisms of the reindexed base-changed system are affine. -/
public theorem isAffineHom_directedBaseChangeDiagram_map
    [∀ {a b : Iᵒᵖ} (e : a ⟶ b), IsAffineHom (D.map e)] {k k' : {k : I // i ≤ k}ᵒᵖ}
    (e : k ⟶ k') : IsAffineHom ((directedBaseChangeDiagram D i w).map e) :=
  Scheme.isAffineHom_baseChangeDiagram_map D (op i) (Over.mk w)
    ((aboveOverEquiv i).functor.map e)

variable (c : Cone D)

/-- The cone over the reindexed base-changed system with apex `P ×_{S_i} S`. -/
public def directedBaseChangeCone : Cone (directedBaseChangeDiagram D i w) :=
  (Scheme.baseChangeCone D (op i) (Over.mk w) c).whisker (aboveOverEquiv i).functor

/-- The apex of `AlgebraicGeometry.directedBaseChangeCone` is `P ×_{S_i} S`. -/
public theorem directedBaseChangeCone_pt :
    (directedBaseChangeCone D i w c).pt = pullback (c.π.app (op i)) w :=
  rfl

/-- On the `D`-component the legs of `AlgebraicGeometry.directedBaseChangeCone` are the legs of
`c`. -/
@[reassoc]
public theorem directedBaseChangeCone_π_fst (k : {k : I // i ≤ k}) :
    (directedBaseChangeCone D i w c).π.app (op k) ≫
        pullback.fst (D.map (homOfLE k.2).op) w =
      pullback.fst (c.π.app (op i)) w ≫ c.π.app (op k.1) :=
  Scheme.baseChangeCone_π_fst D (op i) (Over.mk w) c ((aboveOverEquiv i).functor.obj (op k))

/-- On the `P`-component the legs of `AlgebraicGeometry.directedBaseChangeCone` are the
identity. -/
@[reassoc]
public theorem directedBaseChangeCone_π_snd (k : {k : I // i ≤ k}) :
    (directedBaseChangeCone D i w c).π.app (op k) ≫
        pullback.snd (D.map (homOfLE k.2).op) w =
      pullback.snd (c.π.app (op i)) w :=
  Scheme.baseChangeCone_π_snd D (op i) (Over.mk w) c ((aboveOverEquiv i).functor.obj (op k))

/-- `AlgebraicGeometry.directedBaseChangeCone` is a limit cone whenever `c` is: it is the
cone of `AlgebraicGeometry.Scheme.isLimitBaseChangeCone` whiskered along the equivalence
`AlgebraicGeometry.aboveOverEquiv`. -/
public def isLimitDirectedBaseChangeCone [IsDirected I (· ≤ ·)] [Nonempty I] (hc : IsLimit c) :
    IsLimit (directedBaseChangeCone D i w c) :=
  (Scheme.isLimitBaseChangeCone D (op i) (Over.mk w) c hc).whiskerEquivalence (aboveOverEquiv i)

/-- The base change of a directed inverse system of schemes with affine transition morphisms,
packaged as a `DescentSituation` over the directed set of indices above `i`, with an arbitrary
chosen base stage `j ≥ i`. -/
public def directedBaseChangeDescentSituation
    [IsDirected I (· ≤ ·)] [Nonempty I]
    [∀ {a b : Iᵒᵖ} (e : a ⟶ b), IsAffineHom (D.map e)] (hc : IsLimit c)
    (hcpt : ∀ k : {k : I // i ≤ k},
      CompactSpace (pullback (D.map (homOfLE k.2).op) w : Scheme.{u}))
    (hqs : ∀ k : {k : I // i ≤ k},
      QuasiSeparatedSpace (pullback (D.map (homOfLE k.2).op) w : Scheme.{u}))
    (j : {k : I // i ≤ k}) :
    DescentSituation.{u, u} {k : I // i ≤ k} where
  system := directedBaseChangeDiagram D i w
  transition_affine e := isAffineHom_directedBaseChangeDiagram_map D i w e
  quasiCompact := hcpt
  quasiSeparated := hqs
  limitCone := directedBaseChangeCone D i w c
  isLimit := isLimitDirectedBaseChangeCone D i w c hc
  base := j

/-- **Tag 05F4 for the reindexed base-changed system.** A locally constructible subset of the
stage `j` of the base change which contains the image of `P ×_{S_i} S` already contains the
image of the stage `k` for some `k ≥ j`. -/
public theorem exists_stage_range_subset_of_isLocallyConstructible
    [IsDirected I (· ≤ ·)] [Nonempty I]
    [∀ {a b : Iᵒᵖ} (e : a ⟶ b), IsAffineHom (D.map e)] (hc : IsLimit c)
    (hcpt : ∀ k : {k : I // i ≤ k},
      CompactSpace (pullback (D.map (homOfLE k.2).op) w : Scheme.{u}))
    (hqs : ∀ k : {k : I // i ≤ k},
      QuasiSeparatedSpace (pullback (D.map (homOfLE k.2).op) w : Scheme.{u}))
    (j : {k : I // i ≤ k}) (Ej : Set ((directedBaseChangeDiagram D i w).obj (op j)))
    (hEj : Topology.IsLocallyConstructible Ej)
    (hlim : Set.range ⇑((directedBaseChangeCone D i w c).π.app (op j)) ⊆ Ej) :
    ∃ (k : {k : I // i ≤ k}) (hjk : j ≤ k),
      Set.range ⇑((directedBaseChangeDiagram D i w).map (homOfLE hjk).op) ⊆ Ej := by
  have h := eventually_range_transition_subset_of_isLocallyConstructible
    (directedBaseChangeDescentSituation D i w c hc hcpt hqs j) Ej hEj hlim
  obtain ⟨k, hjk, hrange⟩ := h.exists
  exact ⟨k, hjk, hrange⟩

end Directed

end AlgebraicGeometry

end
