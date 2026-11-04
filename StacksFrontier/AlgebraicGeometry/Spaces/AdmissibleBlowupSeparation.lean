module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowup
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupIsomorphismOffCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPointSetDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierComplement
import StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackComponents
import StacksFrontier.AlgebraicGeometry.Spaces.EmptyOpenSubspace
import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Smallness
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImagePoints
import StacksFrontier.AlgebraicGeometry.Spaces.OpenComplement
import StacksFrontier.AlgebraicGeometry.Spaces.Separated
import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion

/-!
# Separating two disjoint quasi-compact open subspaces by a blowup

Let `S` be a scheme, let `X` be a quasi-compact and quasi-separated algebraic space over `S` and
let `U, V ⊆ X` be disjoint quasi-compact open subspaces.  Stacks 086F asserts that there is a
`U ∪ V`-admissible blowup `b : X' ⟶ X` whose source is a disjoint union of two open subspaces
`X' = X'₁ ⊔ X'₂` with `b⁻¹(U) ⊆ X'₁` and `b⁻¹(V) ⊆ X'₂`.

The source argues as follows.  Choose finite type quasi-coherent ideals `𝓘`, `𝓙` with
`|X| ∖ |U| = |V(𝓘)|` and `|X| ∖ |V| = |V(𝓙)|`; then `|V(𝓘𝓙)| = |X|`, so `𝓘𝓙` is locally
nilpotent and, `X` being quasi-compact and the ideals of finite type, `𝓘ⁿ𝓙ⁿ = 0` for some
`n > 0`.  Replacing `𝓘` and `𝓙` by those powers one may assume `𝓘𝓙 = 0`.  Let `b : X' ⟶ X` be
the blowup of `X` in `𝓘 + 𝓙`.  Its centre has vanishing locus `|X| ∖ (|U| ∪ |V|)`, so `b` is
`U ∪ V`-admissible and the inverse image of `U ∪ V` is exactly the complement of the exceptional
divisor, hence scheme-theoretically dense in `X'`.  Therefore the two pieces of any
decomposition are forced to be the scheme-theoretic closures of `b⁻¹(U)` and of `b⁻¹(V)`, and
since `U ⟶ X'` and `V ⟶ X'` are quasi-compact the formation of those closures commutes with
étale localization, so existence may be checked étale-locally on `X`, where it is the scheme
case.

## Main definitions

* `AlgebraicGeometry.Space.openSubspaceUnion` is the union `U ∪ V` of two open subspaces, the
  open subspace whose set of points is the union of the two sets of points.

## Main results

* `AlgebraicGeometry.Space.dense_subspacePointSet_of_isSchemeTheoreticallyDense`: a
  scheme-theoretically dense subspace is topologically dense on points.  This is the comparison
  of the two notions of density of Stacks 0834 in the direction which holds unconditionally.
* `AlgebraicGeometry.Space.preimage_eq_openComplement_preimage`: if the centre of a blowup has
  for its points exactly the complement of the points of an open subspace `W ⊆ X`, then the
  inverse image of `W` in the blowup is the open complement of the exceptional divisor.
* `AlgebraicGeometry.Space.isSchemeTheoreticallyDense_preimage_of_isBlowupAlong`: in that
  situation the inverse image of `W` is scheme-theoretically dense in the blowup.  This is the
  fourth step of the source's argument, and rests on Stacks 085T (2) and Stacks 083S.
* `AlgebraicGeometry.Space.subspacePointSet_eq_closure_of_decomposition`: the fifth step, the
  decomposition is forced — the points of `X'₁` are the closure of the points of `b⁻¹(U)` and
  those of `X'₂` the closure of the points of `b⁻¹(V)`.

## Where the full statement is

Stacks 086F itself is
`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_disjoint_openSubspace_decomposition'`, in
`StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSeparationQuasiCompact`.  What this file
proves is unconditional: the fourth and fifth steps of the argument — scheme-theoretic density of
`b⁻¹(U ∪ V)` and the resulting rigidity of the decomposition — and the passage from the clopen
set of points `closure |b⁻¹(U)|` to the pair of open subspaces, which is the Stacks 02YU package
of `StacksFrontier/AlgebraicGeometry/Spaces/ClopenPointSetDecomposition.lean`.

## Implementation notes

"`X'` is the disjoint union of `X'₁` and `X'₂`" is recorded exactly as the library records the
decompositions of Stacks 082H and 0ADU: two subfunctors which are open and closed subspaces,
whose join sheafifies to the whole of `X'` and whose meet is the sheafification of the bottom
subfunctor, with complementary sets of points.  The sheafifications are necessary and not an
artefact: the join of two subfunctors is not a sheaf, and the bottom of the lattice of
subfunctors is not the empty algebraic space, since the empty algebraic space has a section over
an empty test scheme.

The union `U ∪ V` is formed on points, by the order isomorphism of Stacks 03BZ between open
subspaces and open sets of points, for the same reason: the join of the two subfunctors is not a
sheaf.  Admissibility of Stacks 086B refers to an open subspace only through its set of points,
so this is the open subspace the source means.

The topological density used in the fifth step is deduced from scheme-theoretic density here
rather than assumed.  Were the closure of the points of a scheme-theoretically dense subspace
`U` not everything, its complement would cut out an open subspace `G ⊆ X` in which the inverse
image of `U` has no points, so that the scheme-theoretic closure of `U ×_X G` is at once all of
`G` and contained in the empty closed subspace, forcing `G` to have no points.

## References

* [Stacks Project, Tag 086F](https://stacks.math.columbia.edu/tag/086F)
* [Stacks Project, Tag 086B](https://stacks.math.columbia.edu/tag/086B)
* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 085Q](https://stacks.math.columbia.edu/tag/085Q)
* [Stacks Project, Tag 083S](https://stacks.math.columbia.edu/tag/083S)
* [Stacks Project, Tag 0834](https://stacks.math.columbia.edu/tag/0834)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 0855](https://stacks.math.columbia.edu/tag/0855)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 02YU](https://stacks.math.columbia.edu/tag/02YU)
* [Stacks Project, Tag 080P](https://stacks.math.columbia.edu/tag/080P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### A topological rigidity lemma -/

/-- One half of a clopen partition of a topological space which separates two subsets with dense
union is the closure of the subset it contains.

It contains that subset and is closed, being the complement of the other half, so it contains
its closure; conversely it is open and misses the second subset, hence misses the closure of the
second subset, and the two closures cover the space. -/
private theorem eq_closure_of_isOpen_of_dense {α : Type*} [TopologicalSpace α]
    {A₁ A₂ T₁ T₂ : Set α} (hT₁ : IsOpen T₁) (hT₂ : IsOpen T₂) (hdisj : Disjoint T₁ T₂)
    (hcover : T₁ ∪ T₂ = Set.univ) (h₁ : A₁ ⊆ T₁) (h₂ : A₂ ⊆ T₂)
    (hdense : Dense (A₁ ∪ A₂)) :
    T₁ = closure A₁ := by
  have hcompl : T₁ = T₂ᶜ := by
    refine Set.Subset.antisymm (fun x hx => Set.disjoint_left.mp hdisj hx) fun x hx => ?_
    rcases hcover.ge (Set.mem_univ x) with h | h
    · exact h
    · exact absurd h hx
  have hT₁c : IsClosed T₁ := by rw [hcompl]; exact hT₂.isClosed_compl
  refine Set.Subset.antisymm (fun x hx => ?_) (closure_minimal h₁ hT₁c)
  have hA₂ : Disjoint T₁ (closure A₂) :=
    Disjoint.closure_right
      (Set.disjoint_left.mpr fun y hy₁ hy₂ => Set.disjoint_left.mp hdisj hy₁ (h₂ hy₂)) hT₁
  have hall : closure A₁ ∪ closure A₂ = Set.univ := by
    rw [← closure_union, hdense.closure_eq]
  rcases hall.ge (Set.mem_univ x) with h | h
  · exact h
  · exact absurd h (Set.disjoint_left.mp hA₂ hx)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Scheme-theoretic density implies density on points -/

/-- An open subspace of an algebraic space in which a scheme-theoretically dense subspace has no
points has no points itself.

The scheme-theoretic image of a morphism whose source has no points is contained in the empty
closed subspace, while scheme-theoretic density applied to the étale inclusion of the open
subspace says that it is all of the open subspace; so the top subfunctor of that subspace has no
points, and the top subfunctor is the subspace cut out by every point. -/
private theorem subspacePointSet_eq_empty_of_isSchemeTheoreticallyDense
    {X : AlgebraicSpaces B S hS} {U : Subfunctor X.1}
    (hU : IsSchemeTheoreticallyDense B S hS U) {G : Subfunctor X.1}
    (hG : IsOpenSubspace B S hS G)
    (hGU : subspacePointSet B S hS G.toFunctor (U.preimage G.ι) = ∅) :
    subspacePointSet B S hS X.1 G = ∅ := by
  have hempty : IsEmpty (points B S hS (U.preimage G.ι).toFunctor) :=
    Set.range_eq_empty_iff.mp hGU
  have htop : (⊤ : Subfunctor G.toFunctor)
      ≤ (⊥ : Subfunctor G.toFunctor).sheafify (BigFppfOver.topology B S hS) := by
    rw [← hU hG.1 G.ι (isEtale_of_isOpenImmersion B S hS hG.2)]
    exact schemeTheoreticImageSubfunctor_le_sheafify_bot_of_isEmpty_points B S hS
      (U.preimage G.ι).ι hG.1 hempty
  have huniv : (Set.univ : Set (points B S hS G.toFunctor)) = ∅ := by
    rw [← range_pointsMap_ι_openSubspaceOfPoints B S hS (F := G.toFunctor) Set.univ]
    refine range_pointsMap_ι_eq_empty_of_le_sheafify_bot B S hS ?_
    rw [openSubspaceOfPoints_univ]
    exact htop
  exact Set.range_eq_empty_iff.mpr (Set.univ_eq_empty_iff.mp huniv)

/-- **A scheme-theoretically dense subspace is dense on points.**  For a subspace `U` of an
algebraic space `X` over `S` which is scheme-theoretically dense in the sense of Stacks 0834
part (2), the set of points of `U` is dense in the point space of `X`.

The complement of the closure of the points of `U` is open, so it cuts out an open subspace of
`X` by Stacks 03BZ, and the inverse image of `U` in that subspace has no points; so the subspace
itself has no points, that is, the closure of the points of `U` is everything. -/
theorem dense_subspacePointSet_of_isSchemeTheoreticallyDense {X : AlgebraicSpaces B S hS}
    (U : Subfunctor X.1) (hU : IsSchemeTheoreticallyDense B S hS U) :
    Dense (subspacePointSet B S hS X.1 U) := by
  refine dense_iff_closure_eq.mpr (Set.compl_empty_iff.mp ?_)
  have hGrange : subspacePointSet B S hS X.1 (openSubspaceOfPoints B S hS X.1
      (closure (subspacePointSet B S hS X.1 U))ᶜ)
      = (closure (subspacePointSet B S hS X.1 U))ᶜ :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS _
  have hGU : subspacePointSet B S hS (openSubspaceOfPoints B S hS X.1
      (closure (subspacePointSet B S hS X.1 U))ᶜ).toFunctor
      (U.preimage (openSubspaceOfPoints B S hS X.1
        (closure (subspacePointSet B S hS X.1 U))ᶜ).ι) = ∅ := by
    rw [subspacePointSet_preimage]
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    exact hGrange.le (Set.mem_range_self x) (subset_closure hx)
  exact hGrange.symm.trans (subspacePointSet_eq_empty_of_isSchemeTheoreticallyDense B S hS hU
    (isOpenSubspace_openSubspaceOfPoints B S hS X.2
      (closure (subspacePointSet B S hS X.1 U))ᶜ isClosed_closure.isOpen_compl) hGU)

/-! ### The union of two open subspaces -/

/-- The union `U ∪ V` of two open subspaces of an algebraic space `X` over `S`: the open
subspace of Stacks 03BZ cut out by the union of their two sets of points. -/
def openSubspaceUnion (X : AlgebraicSpaces B S hS) (U V : OpenSubspaces B S hS X.1) :
    OpenSubspaces B S hS X.1 :=
  ⟨openSubspaceOfPoints B S hS X.1
      (subspacePointSet B S hS X.1 U.1 ∪ subspacePointSet B S hS X.1 V.1),
    isOpenSubspace_openSubspaceOfPoints B S hS X.2 _
      ((isOpen_range_pointsMap_of_isOpenImmersion B S hS U.1.ι U.2.2).union
        (isOpen_range_pointsMap_of_isOpenImmersion B S hS V.1.ι V.2.2))⟩

/-- The points of the union of two open subspaces are the union of their points. -/
theorem subspacePointSet_openSubspaceUnion (X : AlgebraicSpaces B S hS)
    (U V : OpenSubspaces B S hS X.1) :
    subspacePointSet B S hS X.1 (openSubspaceUnion B S hS X U V).1 =
      subspacePointSet B S hS X.1 U.1 ∪ subspacePointSet B S hS X.1 V.1 :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS _

/-- The inverse image of the union of two open subspaces along a morphism is, on points, the
union of the inverse images of the two. -/
theorem subspacePointSet_preimage_openSubspaceUnion {X X' : AlgebraicSpaces B S hS}
    (U V : OpenSubspaces B S hS X.1) (b : X' ⟶ X) :
    subspacePointSet B S hS X'.1 ((openSubspaceUnion B S hS X U V).1.preimage b.hom) =
      subspacePointSet B S hS X'.1 (U.1.preimage b.hom) ∪
        subspacePointSet B S hS X'.1 (V.1.preimage b.hom) := by
  rw [subspacePointSet_preimage, subspacePointSet_preimage, subspacePointSet_preimage,
    subspacePointSet_openSubspaceUnion, Set.preimage_union]

/-! ### The complement of the exceptional divisor -/

variable {B S hS}

/-- **The inverse image of an open subspace whose complement is the centre is the complement of
the exceptional divisor.**  Let `b : X' ⟶ X` be a morphism of algebraic spaces over `S` and let
`Z ⊆ X` be a closed subspace whose set of points is the complement of the set of points of an
open subspace `W ⊆ X`.  Then the inverse image of `W` in `X'` is the open complement of the
inverse image of `Z`.

Both are open subspaces of `X'` and their sets of points agree, being the inverse image along
`b` of the points of `W`, so they coincide by the order isomorphism of Stacks 03BZ. -/
theorem preimage_eq_openComplement_preimage {X X' : AlgebraicSpaces B S hS}
    (W : OpenSubspaces B S hS X.1) (Z : ClosedSubspaces B S hS X.1) (b : X' ⟶ X)
    (hZ : subspacePointSet B S hS X.1 Z.1 = (subspacePointSet B S hS X.1 W.1)ᶜ) :
    W.1.preimage b.hom = openComplement B S hS (Z.1.preimage b.hom) := by
  have hWopen : IsOpenSubspace B S hS (W.1.preimage b.hom) :=
    isOpenSubspace_preimage B S hS b.hom W.1 X.2 X'.2 W.2
  have hCopen : IsOpenSubspace B S hS (openComplement B S hS (Z.1.preimage b.hom)) :=
    isOpenSubspace_openComplement B S hS X'.2 _
      (isClosedSubspace_preimage B S hS b.hom Z.1 X.2 X'.2 Z.2)
  have hcompl : subspacePointSet B S hS X'.1 (openComplement B S hS (Z.1.preimage b.hom))
      = (subspacePointSet B S hS X'.1 (Z.1.preimage b.hom))ᶜ :=
    range_pointsMap_ι_openComplement B S hS _
  have hpts : subspacePointSet B S hS X'.1 (openComplement B S hS (Z.1.preimage b.hom)) =
      subspacePointSet B S hS X'.1 (W.1.preimage b.hom) := by
    rw [hcompl, subspacePointSet_preimage, subspacePointSet_preimage, hZ,
      Set.preimage_compl, compl_compl]
  exact le_antisymm (le_of_range_pointsMap_ι_subset B S hS hCopen hpts.ge)
    (le_of_range_pointsMap_ι_subset B S hS hWopen hpts.le)

/-- **Stacks 085T (2) and Stacks 083S.**  Let `b : X' ⟶ X` be the blowup of an algebraic space
`X` over `S` in a closed subspace `Z ⊆ X` whose set of points is the complement of the set of
points of an open subspace `W ⊆ X`.  Then the inverse image of `W` in `X'` is
scheme-theoretically dense in `X'`.

The inverse image of `W` is the open complement of the exceptional divisor `b⁻¹(Z)`, which is an
effective Cartier divisor on `X'` by Stacks 085T part (2), and the complement of an effective
Cartier divisor is scheme-theoretically dense by Stacks 083S. -/
theorem isSchemeTheoreticallyDense_preimage_of_isBlowupAlong {X X' : AlgebraicSpaces B S hS}
    (W : OpenSubspaces B S hS X.1) (Z : ClosedSubspaces B S hS X.1) {b : X' ⟶ X}
    (hb : IsBlowupAlong B S hS Z b)
    (hZ : subspacePointSet B S hS X.1 Z.1 = (subspacePointSet B S hS X.1 W.1)ᶜ) :
    IsSchemeTheoreticallyDense B S hS (W.1.preimage b.hom) := by
  rw [preimage_eq_openComplement_preimage W Z b hZ]
  exact isSchemeTheoreticallyDense_openComplement_of_isEffectiveCartierDivisor B S hS X'
    ⟨Z.1.preimage b.hom, isClosedSubspace_preimage B S hS b.hom Z.1 X.2 X'.2 Z.2⟩
    hb.isPullbackDefined

/-- In the situation of
`AlgebraicGeometry.Space.isSchemeTheoreticallyDense_preimage_of_isBlowupAlong` the points of the
inverse image of `W` are dense in the point space of the blowup. -/
theorem dense_subspacePointSet_preimage_of_isBlowupAlong {X X' : AlgebraicSpaces B S hS}
    (W : OpenSubspaces B S hS X.1) (Z : ClosedSubspaces B S hS X.1) {b : X' ⟶ X}
    (hb : IsBlowupAlong B S hS Z b)
    (hZ : subspacePointSet B S hS X.1 Z.1 = (subspacePointSet B S hS X.1 W.1)ᶜ) :
    Dense (subspacePointSet B S hS X'.1 (W.1.preimage b.hom)) :=
  dense_subspacePointSet_of_isSchemeTheoreticallyDense B S hS _
    (isSchemeTheoreticallyDense_preimage_of_isBlowupAlong W Z hb hZ)

/-! ### The decomposition is forced -/

/-- **The two pieces of a separating decomposition are the closures of the two open subspaces.**
Let `b : X' ⟶ X` be the blowup of an algebraic space `X` over `S` in a closed subspace whose set
of points is the complement of the points of `U ∪ V`, for open subspaces `U, V ⊆ X`, and let
`X'₁, X'₂ ⊆ X'` be open subspaces with disjoint sets of points covering `|X'|` and with
`b⁻¹(U) ⊆ X'₁` and `b⁻¹(V) ⊆ X'₂`.  Then the points of `X'₁` are the closure of the points of
`b⁻¹(U)`, and the points of `X'₂` the closure of the points of `b⁻¹(V)`.

This is the fifth step of the argument for Stacks 086F.  The points of `b⁻¹(U ∪ V)` are dense in
`|X'|` because that subspace is scheme-theoretically dense, and a clopen partition separating
two subsets with dense union has each piece equal to the closure of the subset it contains. -/
theorem subspacePointSet_eq_closure_of_decomposition {X X' : AlgebraicSpaces B S hS}
    (U V : OpenSubspaces B S hS X.1) (Z : ClosedSubspaces B S hS X.1) {b : X' ⟶ X}
    (hb : IsBlowupAlong B S hS Z b)
    (hZ : subspacePointSet B S hS X.1 Z.1 =
      (subspacePointSet B S hS X.1 (openSubspaceUnion B S hS X U V).1)ᶜ)
    (X'₁ X'₂ : OpenSubspaces B S hS X'.1)
    (hdisj : Disjoint (subspacePointSet B S hS X'.1 X'₁.1)
      (subspacePointSet B S hS X'.1 X'₂.1))
    (hcover : subspacePointSet B S hS X'.1 X'₁.1 ∪ subspacePointSet B S hS X'.1 X'₂.1
      = Set.univ)
    (h₁ : U.1.preimage b.hom ≤ X'₁.1) (h₂ : V.1.preimage b.hom ≤ X'₂.1) :
    subspacePointSet B S hS X'.1 X'₁.1
        = closure (subspacePointSet B S hS X'.1 (U.1.preimage b.hom)) ∧
      subspacePointSet B S hS X'.1 X'₂.1
        = closure (subspacePointSet B S hS X'.1 (V.1.preimage b.hom)) := by
  have hdense : Dense (subspacePointSet B S hS X'.1 (U.1.preimage b.hom) ∪
      subspacePointSet B S hS X'.1 (V.1.preimage b.hom)) := by
    rw [← subspacePointSet_preimage_openSubspaceUnion B S hS U V b]
    exact dense_subspacePointSet_preimage_of_isBlowupAlong
      (openSubspaceUnion B S hS X U V) Z hb hZ
  have hT₁ : IsOpen (subspacePointSet B S hS X'.1 X'₁.1) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS X'₁.1.ι X'₁.2.2
  have hT₂ : IsOpen (subspacePointSet B S hS X'.1 X'₂.1) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS X'₂.1.ι X'₂.2.2
  refine ⟨eq_closure_of_isOpen_of_dense hT₁ hT₂ hdisj hcover
      (range_pointsMap_ι_le B S hS h₁) (range_pointsMap_ι_le B S hS h₂) hdense,
    eq_closure_of_isOpen_of_dense hT₂ hT₁ hdisj.symm ?_ (range_pointsMap_ι_le B S hS h₂)
      (range_pointsMap_ι_le B S hS h₁) ?_⟩
  · rw [Set.union_comm]; exact hcover
  · rw [Set.union_comm]; exact hdense

end AlgebraicGeometry.Space

end
