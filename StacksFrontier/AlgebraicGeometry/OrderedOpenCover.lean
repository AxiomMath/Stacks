module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Cover.Directed
public import Mathlib.Topology.Sets.OpenCover
public import StacksCore.Tactic.StacksAttribute

/-!
# Gluing morphisms along an ordered family of opens

Let `T` be a scheme and let `U : s → T.Opens` be a family of open subschemes covering `T`,
indexed by a preorder `s` whose order is inclusion of the members. If the members form a basis
of the topology of `T`, then any family of morphisms `g i : U i ⟶ X` compatible with the
inclusions `U i ≤ U j` glues to a unique morphism `T ⟶ X`. In other words

  `Mor(T, X) = lim_{i : s} Mor(U i, X)`.

Such a cover is *locally directed* in the sense of
`AlgebraicGeometry.Scheme.Cover.LocallyDirected`: the intersection `U i ⊓ U j` is again covered by
members of the family.

The family of all quasi-compact opens of `T` covers `T` and forms a basis, so `Mor(T, X)` is the
limit of `Mor(V, X)` over the quasi-compact opens `V ⊆ T`.

## Main definitions

* `AlgebraicGeometry.Scheme.orderedOpenCover`: an ordered family of opens covering `T`, read as
  an open cover of `T`.
* `AlgebraicGeometry.Scheme.locallyDirectedOrderedOpenCover`: such a cover is locally directed
  when the order is inclusion and the members form a basis.
* `AlgebraicGeometry.Scheme.CompactOpens`: the quasi-compact opens of `T`, as an index type.

## Main results

* `AlgebraicGeometry.Scheme.trans_orderedOpenCover`: the transition maps of the locally directed
  structure are the inclusions of open subschemes.
* `AlgebraicGeometry.Scheme.existsUnique_hom_of_compatible`: a family of morphisms out of the
  members, compatible with the inclusions, comes from a unique morphism out of `T`.
* `AlgebraicGeometry.Scheme.isOpenCover_compactOpens` and
  `AlgebraicGeometry.Scheme.isBasis_range_compactOpens`: the quasi-compact opens cover `T` and
  form a basis of its topology.
* `AlgebraicGeometry.Scheme.existsUnique_hom_of_compatible_compactOpens`: the same gluing
  statement for the family of quasi-compact opens, that is,
  `Mor(T, X) = lim_{V ⊆ T quasi-compact open} Mor(V, X)`.

## References

* [Stacks Project, Tag 01NC](https://stacks.math.columbia.edu/tag/01NC)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u v

variable {T : Scheme.{u}} {s : Type v} [Preorder s] (U : s → T.Opens) (hU : IsOpenCover U)

/-- An ordered family of opens covering `T`, read as an open cover of `T`. -/
def orderedOpenCover : T.OpenCover := T.openCoverOfIsOpenCover U hU

/-- The index type of `orderedOpenCover U hU` carries the preorder of `s`. -/
instance : Preorder (orderedOpenCover U hU).I₀ := inferInstanceAs (Preorder s)

/-- **An ordered basis of opens is a locally directed cover.** If the order on the index type is
inclusion of the members and the members form a basis of the topology, then the intersection of
two members is covered by members below both, which is local directedness. -/
@[instance_reducible]
def locallyDirectedOrderedOpenCover (hle : ∀ i j : s, i ≤ j ↔ U i ≤ U j)
    (hbasis : Opens.IsBasis (Set.range U)) :
    (orderedOpenCover U hU).LocallyDirected :=
  Cover.LocallyDirected.ofIsBasisOpensRange
    (fun {i j} => by
      change (i : s) ≤ (j : s) ↔ ((U i).ι).opensRange ≤ ((U j).ι).opensRange
      rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
      exact hle i j)
    (by
      change Opens.IsBasis (Set.range fun i : s => ((U i).ι).opensRange)
      simpa [Scheme.Opens.opensRange_ι] using hbasis)

variable (hle : ∀ i j : s, i ≤ j ↔ U i ≤ U j) (hbasis : Opens.IsBasis (Set.range U))

include hU hle hbasis in
/-- The transition maps of the locally directed structure of `orderedOpenCover` are the
inclusions of open subschemes: both are morphisms over `T`, and such a morphism into an open
subscheme is unique. -/
theorem trans_orderedOpenCover {i j : s} (hij : i ⟶ j) :
    letI := locallyDirectedOrderedOpenCover U hU hle hbasis
    (orderedOpenCover U hU).trans hij = T.homOfLE ((hle i j).mp (leOfHom hij)) := by
  let _ := locallyDirectedOrderedOpenCover U hU hle hbasis
  exact (IsOpenImmersion.lift_uniq _ _ _ _ (Scheme.homOfLE_ι _ _)).symm

include hU hle hbasis in
/-- **Morphisms out of `T` are the limit of the morphisms out of the members.** A family of
morphisms `g i : U i ⟶ X` which is compatible with the inclusions `U i ≤ U j` is the family of
restrictions of a unique morphism `T ⟶ X`. -/
theorem existsUnique_hom_of_compatible {X : Scheme.{u}} (g : ∀ i, (U i).toScheme ⟶ X)
    (hg : ∀ (i j : s) (h : U i ≤ U j), T.homOfLE h ≫ g j = g i) :
    ∃! f : T ⟶ X, ∀ i, (U i).ι ≫ f = g i := by
  let _ := locallyDirectedOrderedOpenCover U hU hle hbasis
  refine ⟨(orderedOpenCover U hU).glueMorphismsOfLocallyDirected g ?_, ?_, ?_⟩
  · intro i j hij
    rw [trans_orderedOpenCover U hU hle hbasis hij]
    exact hg i j _
  · intro i
    exact (orderedOpenCover U hU).map_glueMorphismsOfLocallyDirected g _ i
  · intro f hf
    refine (orderedOpenCover U hU).hom_ext _ _ fun i => ?_
    exact (hf i).trans ((orderedOpenCover U hU).map_glueMorphismsOfLocallyDirected g _ i).symm

/-! ### The family of quasi-compact opens -/

variable (T)

/-- The quasi-compact opens of a scheme, as an index type ordered by inclusion. -/
abbrev CompactOpens : Type u := {V : T.Opens // IsCompact (V : Set T)}

/-- **The quasi-compact opens form a basis** of the topology of a scheme: the affine opens do, and
an affine open is quasi-compact. -/
theorem isBasis_range_compactOpens :
    Opens.IsBasis (Set.range fun V : T.CompactOpens => (V : T.Opens)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro V x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  exact ⟨(U : T.Opens), ⟨⟨(U : T.Opens), hU.isCompact⟩, rfl⟩, hxU, hUV⟩

/-- **The quasi-compact opens cover a scheme**, since the affine opens do. -/
theorem isOpenCover_compactOpens :
    IsOpenCover (fun V : T.CompactOpens => (V : T.Opens)) := by
  refine top_le_iff.mp fun x _ => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ x) isOpen_univ
  exact Opens.mem_iSup.mpr ⟨⟨(U : T.Opens), hU.isCompact⟩, hxU⟩

/-- **`Mor(T, X) = lim_{V ⊆ T quasi-compact open} Mor(V, X)`.** A family of morphisms out of the
quasi-compact opens of `T`, compatible with the inclusions between them, is the family of
restrictions of a unique morphism out of `T`. -/
theorem existsUnique_hom_of_compatible_compactOpens {X : Scheme.{u}}
    (g : ∀ V : T.Opens, IsCompact (V : Set T) → (V.toScheme ⟶ X))
    (hg : ∀ (V W : T.Opens) (hV : IsCompact (V : Set T)) (hW : IsCompact (W : Set T))
      (h : V ≤ W), T.homOfLE h ≫ g W hW = g V hV) :
    ∃! f : T ⟶ X, ∀ (V : T.Opens) (hV : IsCompact (V : Set T)), V.ι ≫ f = g V hV := by
  obtain ⟨f, hf, huniq⟩ := existsUnique_hom_of_compatible
    (U := fun V : T.CompactOpens => (V : T.Opens)) (isOpenCover_compactOpens T)
    (fun _ _ => Subtype.coe_le_coe.symm) (isBasis_range_compactOpens T)
    (fun V => g V.1 V.2) fun V W h => hg _ _ V.2 W.2 h
  exact ⟨f, fun V hV => hf ⟨V, hV⟩, fun f' hf' => huniq f' fun V => hf' V.1 V.2⟩

end AlgebraicGeometry.Scheme

end
