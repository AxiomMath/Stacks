module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianIrreducibleComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Components of the étale inverse image of an integral closed subspace

In the situation of Stacks 0EDT let `X/B` and `Y/B` be good, let `f : X ⟶ Y` be an étale
morphism over the base and let `Z ⊆ Y` be an integral closed subspace. The inverse image
`f^{-1}(Z)` is then a closed subspace of `X`, and each irreducible component of its set of
points carries a reduced closed subspace structure which is integral; so the irreducible
components of `f^{-1}(Z)` are integral closed subspaces of `X`, as in Stacks 0EE8.

Each of them has the same δ-dimension as `Z`. This is where étaleness enters, twice: an étale
morphism is locally quasi-finite, so the dimension function of Situation 0EDT is unchanged
along it, and an étale morphism is open on points, which forces a generic point of a component
of `f^{-1}(Z)` to be carried to the generic point of `|Z|`. The second step also uses that the
irreducible components of a closed subset of `|X|` are locally finite, by Stacks 0EE5: that is
what produces an open neighbourhood of a generic point of one component meeting no other.

Local finiteness of the family of components is the last ingredient, and the four statements
together say that the formal sum of the irreducible components of `f^{-1}(Z)`, each with
coefficient one, is a well-defined element of the group `Z_{δ(Z)}(X)` of Stacks 0EDZ.

## Main definitions

* `AlgebraicGeometry.Space.IntegralClosedSubspace.preimagePointSet`: the set of points of the
  inverse image of an integral closed subspace.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.preimageComponent`: an irreducible component
  of the inverse image, as an integral closed subspace of the source.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.preimageComponentsCycle`: the coefficient
  family giving the coefficient one at each irreducible component of the inverse image and zero
  at every other integral closed subspace.

## Main results

* `AlgebraicGeometry.Space.IntegralClosedSubspace.isClosedSubspace_preimage`: the inverse image
  of an integral closed subspace is a closed subspace.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.subspacePointSet_preimageComponent`: the set
  of points of the integral closed subspace attached to a component is that component.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.locallyFinite_preimageComponent`: the
  components form a locally finite family of subsets of `|X|`.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.isGenericPoint_pointsMap_of_isGenericPoint`:
  along an étale morphism a generic point of a component of the inverse image is carried to a
  generic point of the set of points of the subspace.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.deltaDimension_preimageComponent`: a component
  of the inverse image along an étale morphism over the base has the δ-dimension of the
  subspace.
* `AlgebraicGeometry.Space.IntegralClosedSubspace.preimageComponentsCycle_mem_cyclesOfDimension`:
  **Stacks 0EPY** for the right-hand side of its formula — the formal sum of the components is a
  cycle of the δ-dimension of the subspace.

## Implementation notes

The cycle identity `f^*[Z] = ∑ [Z']` of Stacks 0EPY is not proved here: its left-hand side, the
flat pullback of Stacks 0EP8 applied to the cycle `[Z]` of Stacks 0EE9, lives in files that import
this one. The identity is
`IntegralClosedSubspace.flatPullbackMap_integralCycle_eq_preimageComponentsCycle` in
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.EtalePullbackIdentity`. What is proved here is that
the right-hand side of the formula is a well-defined element of `Z_{δ(Z)}(X)`, which is the part
of the statement that does not presuppose the left-hand side.

The components are indexed as in Stacks 0EE5, by `irreducibleComponents` of the set of points
of the inverse image, rather than by the predicate
`AlgebraicGeometry.Space.IsIrreducibleComponent` of Stacks 0EE8. Indexing makes the family whose
local finiteness is at issue a family of sets over an index type, which is what `LocallyFinite`
and `AlgebraicGeometry.Space.locallyFinite_irreducibleComponents_of_isClosed` ask for, and it
produces the components as integral closed subspaces of `X` rather than of the inverse image,
which is how a cycle on `X` is indexed.

The set of points of the inverse image is taken to be the inverse image of the set of points,
and its agreement with the set of points of the closed subspace `f^{-1}(Z)` is
`AlgebraicGeometry.Space.subspacePointSet_preimage`. That subspace is
`CategoryTheory.Subfunctor.preimage`, so the agreement is the base-change computation
`AlgebraicGeometry.Space.preimage_image_pointsMap_of_isPullback` applied to the cartesian square
of Stacks 083Q, and no choice of a fibre product has to be made.

The step at which étaleness enters is isolated as a statement about a continuous open map
between topological spaces; only there is local finiteness of the components needed, and that
hypothesis cannot be dropped. The map from `{0} ∪ {1/n : n ≥ 1} ⊆ ℝ` to the Sierpiński space
sending `0` to the closed point and every `1/n` to the generic point is continuous and open, and
the whole of its source is the inverse image of the closure of the generic point; but `{0}` is an
irreducible component of that inverse image whose generic point is not carried to the generic
point.

The formal sum of the components is recorded as a coefficient family, with membership in the
subgroup `AlgebraicGeometry.Space.cyclesOfDimension` as a separate statement; this keeps the
definition independent of the δ-dimension of the subspace.

## References

* [Stacks Project, Tag 0EPY](https://stacks.math.columbia.edu/tag/0EPY)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
* [Stacks Project, Tag 0EDX](https://stacks.math.columbia.edu/tag/0EDX)
* [Stacks Project, Tag 0EDZ](https://stacks.math.columbia.edu/tag/0EDZ)
* [Stacks Project, Tag 0EE5](https://stacks.math.columbia.edu/tag/0EE5)
* [Stacks Project, Tag 0EE8](https://stacks.math.columbia.edu/tag/0EE8)
* [Stacks Project, Tag 083Q](https://stacks.math.columbia.edu/tag/083Q)
* [Stacks Project, Tag 03IR](https://stacks.math.columbia.edu/tag/03IR)
* [Stacks Project, Tag 03XU](https://stacks.math.columbia.edu/tag/03XU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Generic points of irreducible components under an open map -/

/-- An irreducible component of a closed subset whose image in the ambient space contains a
generic point of the image of a second component is that second component: the image of a
component is irreducible and closed, so it contains the closure of that point, and maximality
forces the two components to agree. -/
@[ega "0 2.1.6" "more general"]
private theorem eq_of_isGenericPoint_image_val {α : Type*} [TopologicalSpace α] {T : Set α}
    (hT : IsClosed T) {C C' : irreducibleComponents T} {x : α}
    (hx : IsGenericPoint x (Subtype.val '' (C : Set T)))
    (hx' : x ∈ Subtype.val '' (C' : Set T)) :
    C' = C := by
  have hclosed : IsClosed (Subtype.val '' (C' : Set T)) :=
    hT.isClosedEmbedding_subtypeVal.isClosedMap _
      (isClosed_of_mem_irreducibleComponents _ C'.2)
  have hsub : Subtype.val '' (C : Set T) ⊆ Subtype.val '' (C' : Set T) := by
    rw [← hx]
    exact closure_minimal (Set.singleton_subset_iff.2 hx') hclosed
  have hCC' : (C : Set T) ⊆ (C' : Set T) :=
    (Set.image_subset_image_iff Subtype.val_injective).1 hsub
  exact Subtype.ext (Set.Subset.antisymm (C.2.2 C'.2.1 hCC') hCC')

/-- Let `φ` be a continuous open map into a Kolmogorov space, `ξ` a generic point of a subset
`V` of the target, and assume the irreducible components of `φ ⁻¹' V` are locally finite. Then a
generic point of such a component is carried to `ξ`.

Local finiteness provides an open set `W` containing the given generic point `x` and meeting no
other component. The image of `W` is open and meets `V`, hence contains `ξ`, so some `w ∈ W` is
carried to `ξ`. Such a `w` lies in `φ ⁻¹' V`, and the component through it meets `W`, so it is
the given component; therefore `x` specializes to `w` and the image of `x` specializes to `ξ`.
The image of `x` lies in `V`, so `ξ` specializes to it as well. -/
private theorem isGenericPoint_map_of_isGenericPoint_image_val {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] [T0Space β] {φ : α → β} (hcont : Continuous φ)
    (hopen : IsOpenMap φ) {V : Set β} {ξ : β} (hξ : IsGenericPoint ξ V)
    (hT : IsClosed (φ ⁻¹' V))
    (hlf : LocallyFinite fun C : irreducibleComponents (φ ⁻¹' V) =>
      Subtype.val '' (C : Set (φ ⁻¹' V)))
    (C : irreducibleComponents (φ ⁻¹' V)) {x : α}
    (hx : IsGenericPoint x (Subtype.val '' (C : Set (φ ⁻¹' V)))) :
    IsGenericPoint (φ x) V := by
  obtain ⟨c, -, hc⟩ := hx.mem
  have hxT : x ∈ φ ⁻¹' V := hc ▸ c.2
  obtain ⟨U, hU, hUfin⟩ := hlf x
  obtain ⟨W, hWU, hWopen, hxW⟩ := mem_nhds_iff.1 hU
  set E := {C' : irreducibleComponents (φ ⁻¹' V) | C' ≠ C ∧
    (Subtype.val '' (C' : Set (φ ⁻¹' V)) ∩ U).Nonempty} with hE
  have hEfin : E.Finite := by
    refine hUfin.subset fun C' hC' => ?_
    rw [hE] at hC'
    exact hC'.2
  have hKclosed : IsClosed (⋃ C' ∈ E, Subtype.val '' (C' : Set (φ ⁻¹' V))) :=
    hEfin.isClosed_biUnion fun C' _ =>
      hT.isClosedEmbedding_subtypeVal.isClosedMap _
        (isClosed_of_mem_irreducibleComponents _ C'.2)
  have hxK : x ∉ ⋃ C' ∈ E, Subtype.val '' (C' : Set (φ ⁻¹' V)) := by
    intro hmem
    obtain ⟨C', hC'E, hxC'⟩ := Set.mem_iUnion₂.1 hmem
    rw [hE] at hC'E
    exact hC'E.1 (eq_of_isGenericPoint_image_val hT hx hxC')
  obtain ⟨w, hwW, hwξ⟩ := (hξ.mem_open_set_iff (hopen _ (hWopen.sdiff hKclosed))).2
    ⟨φ x, hxT, ⟨x, ⟨hxW, hxK⟩, rfl⟩⟩
  have hwT : w ∈ φ ⁻¹' V := by
    rw [Set.mem_preimage, hwξ]
    exact hξ.mem
  have hwC : w ∈ Subtype.val '' (C : Set (φ ⁻¹' V)) := by
    by_contra hwC
    set C' : irreducibleComponents (φ ⁻¹' V) :=
      ⟨irreducibleComponent (⟨w, hwT⟩ : φ ⁻¹' V),
        irreducibleComponent_mem_irreducibleComponents _⟩ with hC'
    have hwC' : w ∈ Subtype.val '' (C' : Set (φ ⁻¹' V)) := by
      rw [hC']
      exact ⟨⟨w, hwT⟩, mem_irreducibleComponent, rfl⟩
    have hC'E : C' ∈ E := by
      rw [hE]
      exact ⟨fun h => hwC (h ▸ hwC'), ⟨w, hwC', hWU hwW.1⟩⟩
    exact hwW.2 (Set.mem_biUnion hC'E hwC')
  have hspec : φ x ⤳ ξ := by
    rw [← hwξ]
    exact (hx.specializes hwC).map hcont
  rw [(hspec.antisymm (hξ.specializes hxT)).eq]
  exact hξ

/-! ### The inverse image of an integral closed subspace -/

section Preimage

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The set of points of the inverse image of a subfunctor is the inverse image of its set of
points: the inverse image is a leg of a cartesian square over the subfunctor by Stacks 083Q, and
the set of points of a leg of a cartesian square is the inverse image of the set of points of
the opposite leg. -/
theorem subspacePointSet_preimage (f : X ⟶ Y) (Z : Subfunctor Y) :
    subspacePointSet B S hS X (Z.preimage f) =
      pointsMap B S hS X f ⁻¹' subspacePointSet B S hS Y Z := by
  simpa using (preimage_image_pointsMap_of_isPullback B S hS
    (Subfunctor.isPullback_preimage f Z) Set.univ).symm

/-- **Stacks 0EPY, first part.** The inverse image of an integral closed subspace of `Y` along a
morphism `f : X ⟶ Y` of algebraic spaces over `S` is a closed subspace of `X`. -/
theorem IntegralClosedSubspace.isClosedSubspace_preimage (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (Z : IntegralClosedSubspace B S hS Y) :
    IsClosedSubspace B S hS (Z.subspace.preimage f) :=
  _root_.AlgebraicGeometry.Space.isClosedSubspace_preimage B S hS f Z.subspace hY hX
    Z.isClosedSubspace

/-- The set of points of the inverse image of an integral closed subspace of `Y` along a
morphism `f : X ⟶ Y`, that is, the inverse image of its set of points. -/
abbrev IntegralClosedSubspace.preimagePointSet (f : X ⟶ Y)
    (Z : IntegralClosedSubspace B S hS Y) : Set (points B S hS X) :=
  pointsMap B S hS X f ⁻¹' subspacePointSet B S hS Y Z.subspace

/-- The set of points of the inverse image of an integral closed subspace is the set of points
of the closed subspace it is the inverse image of. -/
theorem IntegralClosedSubspace.preimagePointSet_eq (f : X ⟶ Y)
    (Z : IntegralClosedSubspace B S hS Y) :
    Z.preimagePointSet B S hS f = subspacePointSet B S hS X (Z.subspace.preimage f) :=
  (subspacePointSet_preimage B S hS f Z.subspace).symm

/-- The set of points of the inverse image of an integral closed subspace is closed: the set of
points of the subspace is closed and the map on points is continuous. -/
theorem IntegralClosedSubspace.isClosed_preimagePointSet (f : X ⟶ Y)
    (hY : IsAlgebraicSpace B S hS Y) (Z : IntegralClosedSubspace B S hS Y) :
    IsClosed (Z.preimagePointSet B S hS f) :=
  (isClosed_range_pointsMap_integralClosedSubspace B S hS hY Z).preimage
    (continuous_pointsMap B S hS f)

/-- An irreducible component of the set of points of the inverse image of an integral closed
subspace, as an irreducible closed subset of `|X|`: a component is irreducible and closed in the
inverse image, and the inclusion of the inverse image is a closed embedding. -/
noncomputable def IntegralClosedSubspace.preimageComponentPoints (f : X ⟶ Y)
    (hY : IsAlgebraicSpace B S hS Y) (Z : IntegralClosedSubspace B S hS Y)
    (C : irreducibleComponents (Z.preimagePointSet B S hS f)) :
    IrreducibleCloseds (points B S hS X) where
  carrier := Subtype.val '' (C : Set (Z.preimagePointSet B S hS f))
  isIrreducible' := C.2.1.image _ continuous_subtype_val.continuousOn
  isClosed' :=
    (Z.isClosed_preimagePointSet B S hS f hY).isClosedEmbedding_subtypeVal.isClosedMap _
      (isClosed_of_mem_irreducibleComponents _ C.2)

/-- **Stacks 0EPY, second part.** An irreducible component of the inverse image of an integral
closed subspace of `Y` along a morphism `f : X ⟶ Y`, as an integral closed subspace of a decent
algebraic space `X`: it is the reduced closed subspace on an irreducible closed set of points,
and such a subspace is integral. -/
noncomputable def IntegralClosedSubspace.preimageComponent (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hXdec : IsDecentSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (Z : IntegralClosedSubspace B S hS Y)
    (C : irreducibleComponents (Z.preimagePointSet B S hS f)) :
    IntegralClosedSubspace B S hS X :=
  integralClosedSubspaceOfPoints B S hS hX hXdec (Z.preimageComponentPoints B S hS f hY C)

/-- The set of points of the integral closed subspace attached to an irreducible component of
the inverse image of an integral closed subspace is that component. -/
@[simp]
theorem IntegralClosedSubspace.subspacePointSet_preimageComponent (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hXdec : IsDecentSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (Z : IntegralClosedSubspace B S hS Y)
    (C : irreducibleComponents (Z.preimagePointSet B S hS f)) :
    subspacePointSet B S hS X (Z.preimageComponent B S hS f hX hXdec hY C).subspace =
      Subtype.val '' (C : Set (Z.preimagePointSet B S hS f)) :=
  subspacePointSet_integralClosedSubspaceOfPoints B S hS hX hXdec _

/-- Distinct irreducible components of the inverse image of an integral closed subspace give
distinct integral closed subspaces: they have distinct sets of points, and an integral closed
subspace is determined by its set of points. -/
theorem IntegralClosedSubspace.injective_preimageComponent (f : X ⟶ Y)
    (hX : IsAlgebraicSpace B S hS X) (hXdec : IsDecentSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (Z : IntegralClosedSubspace B S hS Y) :
    Function.Injective (Z.preimageComponent B S hS f hX hXdec hY) := by
  intro C C' h
  have hpts : Subtype.val '' (C : Set (Z.preimagePointSet B S hS f)) =
      Subtype.val '' (C' : Set (Z.preimagePointSet B S hS f)) := by
    rw [← Z.subspacePointSet_preimageComponent B S hS f hX hXdec hY C,
      ← Z.subspacePointSet_preimageComponent B S hS f hX hXdec hY C', h]
  exact Subtype.ext (Subtype.val_injective.image_injective hpts)

end Preimage

/-! ### Local finiteness, δ-dimension and the resulting cycle -/

section Situation

variable (D : BaseSpaceDimensionSituation.{u})
    {X Y : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}

/-- **Stacks 0EPY, fourth part.** The irreducible components of the inverse image of an integral
closed subspace of a good algebraic space `Y/B` along a morphism `f : X ⟶ Y` of good algebraic
spaces over the base form a locally finite family of subsets of `|X|`.

The point space of `X` is locally Noetherian, the structure morphism being locally of finite
type over a locally Noetherian base, so Stacks 0EE5 applies to the closed set of points of the
inverse image. -/
theorem IntegralClosedSubspace.locallyFinite_preimageComponent (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    LocallyFinite fun C : irreducibleComponents
        (Z.preimagePointSet D.site D.base D.base_mem f) =>
      subspacePointSet D.site D.base D.base_mem X
        (Z.preimageComponent D.site D.base D.base_mem f hX.1
          (D.isDecentSpace_of_isGood sX hX) hY.1 C).subspace := by
  have hN := isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base D.base_mem hX.1
    D.isAlgebraicSpace sX hX.2.2 D.locallyNoetherian
  simpa only [Z.subspacePointSet_preimageComponent D.site D.base D.base_mem f hX.1
    (D.isDecentSpace_of_isGood sX hX) hY.1] using
    locallyFinite_irreducibleComponents_of_isClosed D.site D.base D.base_mem X hX.1 hN
      (Z.preimagePointSet D.site D.base D.base_mem f)
      (Z.isClosed_preimagePointSet D.site D.base D.base_mem f hY.1)

/-- **Stacks 0EPY, the step at which étaleness enters.** Let `f : X ⟶ Y` be an étale morphism of
good algebraic spaces over the base and let `Z ⊆ Y` be an integral closed subspace. A generic
point of an irreducible component of the inverse image of `Z` is carried by `f` to a generic
point of the set of points of `Z`.

The map on points of an étale morphism is open by Stacks 03IR, the components of the inverse
image are locally finite, and the point space of `Y` is Kolmogorov because a good algebraic
space is decent. -/
theorem IntegralClosedSubspace.isGenericPoint_pointsMap_of_isGenericPoint (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y}
    (hf : IsEtale D.site D.base D.base_mem f)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f))
    (x : points D.site D.base D.base_mem X)
    (hx : IsGenericPoint x (subspacePointSet D.site D.base D.base_mem X
      (Z.preimageComponent D.site D.base D.base_mem f hX.1
        (D.isDecentSpace_of_isGood sX hX) hY.1 C).subspace)) :
    IsGenericPoint (pointsMap D.site D.base D.base_mem X f x)
      (subspacePointSet D.site D.base D.base_mem Y Z.subspace) := by
  have hT0 : T0Space (points D.site D.base D.base_mem Y) :=
    t0Space_points_of_isDecentSpace D.site D.base D.base_mem hY.1
      (D.isDecentSpace_of_isGood sY hY)
  have hN := isLocallyNoetherian_of_isLocallyOfFiniteType D.site D.base D.base_mem hX.1
    D.isAlgebraicSpace sX hX.2.2 D.locallyNoetherian
  refine isGenericPoint_map_of_isGenericPoint_image_val
    (continuous_pointsMap D.site D.base D.base_mem f)
    (isOpenMap_pointsMap_of_isEtale D.site D.base D.base_mem f hX.1 hY.1 hf)
    (isGenericPoint_pointsMap_genericPoint D.site D.base D.base_mem hY.1 Z)
    (Z.isClosed_preimagePointSet D.site D.base D.base_mem f hY.1)
    (locallyFinite_irreducibleComponents_of_isClosed D.site D.base D.base_mem X hX.1 hN
      (Z.preimagePointSet D.site D.base D.base_mem f)
      (Z.isClosed_preimagePointSet D.site D.base D.base_mem f hY.1)) C ?_
  rwa [Z.subspacePointSet_preimageComponent D.site D.base D.base_mem f hX.1
    (D.isDecentSpace_of_isGood sX hX) hY.1 C] at hx

/-- **Stacks 0EPY, third part.** An irreducible component of the inverse image of an integral
closed subspace `Z ⊆ Y` along an étale morphism `f : X ⟶ Y` of good algebraic spaces over the
base has the δ-dimension of `Z`.

The δ-dimension of an integral closed subspace is the value of `δ_{X/B}` at any generic point of
its set of points; a generic point of the component is carried to a generic point of the set of
points of `Z`, and `δ_{X/B}` is unchanged along `f`, which is locally quasi-finite by
Stacks 03XU because it is étale. -/
theorem IntegralClosedSubspace.deltaDimension_preimageComponent (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y}
    (hf : IsEtale D.site D.base D.base_mem f) (hfc : f ≫ sY = sX)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (C : irreducibleComponents (Z.preimagePointSet D.site D.base D.base_mem f)) :
    deltaDimension D sX (Z.preimageComponent D.site D.base D.base_mem f hX.1
        (D.isDecentSpace_of_isGood sX hX) hY.1 C) = deltaDimension D sY Z := by
  have hgen := isGenericPoint_pointsMap_genericPoint D.site D.base D.base_mem hX.1
    (Z.preimageComponent D.site D.base D.base_mem f hX.1
      (D.isDecentSpace_of_isGood sX hX) hY.1 C)
  have hstep := D.deltaValue_comp_of_isLocallyQuasiFinite hX.1 hY.1 f sY
    (isLocallyQuasiFinite_of_isEtale D.site D.base D.base_mem hY.1 hf) hY.2.2
    (pointsMap D.site D.base D.base_mem
      (Z.preimageComponent D.site D.base D.base_mem f hX.1
        (D.isDecentSpace_of_isGood sX hX) hY.1 C).subspace.toFunctor
      (Z.preimageComponent D.site D.base D.base_mem f hX.1
        (D.isDecentSpace_of_isGood sX hX) hY.1 C).subspace.ι
      ((Z.preimageComponent D.site D.base D.base_mem f hX.1
        (D.isDecentSpace_of_isGood sX hX) hY.1 C).genericPoint D.site D.base D.base_mem))
  rw [hfc] at hstep
  exact (deltaDimension_eq_of_isGenericPoint D sX hX.1 _ _ hgen).trans
    (hstep.trans (deltaDimension_eq_of_isGenericPoint D sY hY.1 Z _
      (Z.isGenericPoint_pointsMap_of_isGenericPoint D sX hX sY hY hf C _ hgen)).symm)

/-- The formal sum of the irreducible components of the inverse image of an integral closed
subspace `Z ⊆ Y` along a morphism `f : X ⟶ Y`, as a coefficient family on the integral closed
subspaces of `X`: the coefficient is one at a component of the inverse image and zero
elsewhere. -/
noncomputable def IntegralClosedSubspace.preimageComponentsCycle (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    IntegralClosedSubspace D.site D.base D.base_mem X → ℤ :=
  Set.indicator {W | ∃ C, Z.preimageComponent D.site D.base D.base_mem f hX.1
    (D.isDecentSpace_of_isGood sX hX) hY.1 C = W} 1

/-- The coefficient of the formal sum of the irreducible components of an inverse image is
nonzero exactly at those integral closed subspaces which are components of that inverse
image. -/
theorem IntegralClosedSubspace.preimageComponentsCycle_ne_zero_iff (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y)
    (W : IntegralClosedSubspace D.site D.base D.base_mem X) :
    Z.preimageComponentsCycle D sX hX sY hY f W ≠ 0 ↔
      ∃ C, Z.preimageComponent D.site D.base D.base_mem f hX.1
        (D.isDecentSpace_of_isGood sX hX) hY.1 C = W := by
  by_cases h : W ∈ {W | ∃ C, Z.preimageComponent D.site D.base D.base_mem f hX.1
      (D.isDecentSpace_of_isGood sX hX) hY.1 C = W}
  · rw [preimageComponentsCycle, Set.indicator_of_mem h]
    simpa using h
  · rw [preimageComponentsCycle, Set.indicator_of_notMem h]
    simpa using h

/-- **Stacks 0EPY, the right-hand side of its formula.** Let `f : X ⟶ Y` be an étale morphism of
good algebraic spaces over the base of Situation 0EDT and let `Z ⊆ Y` be an integral closed
subspace. The formal sum of the irreducible components of the inverse image of `Z`, each with
coefficient one, is a cycle of the δ-dimension of `Z` on `X`.

The components are integral closed subspaces of `X`, they form a locally finite family, and each
of them has the δ-dimension of `Z`; these are exactly the two conditions defining
`Z_{δ(Z)}(X)`. -/
@[stacks 0EPY "the sum of the components of the inverse image is a cycle of the same δ-dimension"]
theorem IntegralClosedSubspace.preimageComponentsCycle_mem_cyclesOfDimension (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (sY : Y ⟶ D.space) (hY : D.IsGood sY) {f : X ⟶ Y}
    (hf : IsEtale D.site D.base D.base_mem f) (hfc : f ≫ sY = sX)
    (Z : IntegralClosedSubspace D.site D.base D.base_mem Y) :
    Z.preimageComponentsCycle D sX hX sY hY f ∈
      cyclesOfDimension D sX (deltaDimension D sY Z) := by
  refine ⟨fun p => ?_, fun W hW => ?_⟩
  · obtain ⟨U, hU, hUfin⟩ := Z.locallyFinite_preimageComponent D sX hX sY hY f p
    refine ⟨U, hU, (hUfin.image (Z.preimageComponent D.site D.base D.base_mem f hX.1
      (D.isDecentSpace_of_isGood sX hX) hY.1)).subset ?_⟩
    rintro W ⟨q, hq, hqU⟩
    simp only [Set.mem_ite_empty_left] at hq
    obtain ⟨C, hC⟩ := (Z.preimageComponentsCycle_ne_zero_iff D sX hX sY hY f W).1 hq.1
    exact ⟨C, ⟨q, by simpa only [hC] using hq.2, hqU⟩, hC⟩
  · obtain ⟨C, hC⟩ := (Z.preimageComponentsCycle_ne_zero_iff D sX hX sY hY f W).1 hW
    exact hC ▸ Z.deltaDimension_preimageComponent D sX hX sY hY hf hfc C

end Situation

end AlgebraicGeometry.Space

end
