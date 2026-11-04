module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented

/-!
# An immersion of algebraic spaces is a homeomorphism onto a locally closed set of points

Let `i : Z ⟶ X` be an immersion of algebraic spaces over a scheme `S`. Tag 0ABJ says that the
induced map `|Z| → |X|` on the point sets of Tag 03BU is a homeomorphism of `|Z|` onto a
locally closed subset of `|X|`. This file proves that, in the two halves a homeomorphism onto
a subspace splits into: the map is a topological embedding, and its image is locally closed.

The argument is the source's. Fix a surjective étale atlas `a : U ⟶ X` by a scheme and let
`j : P ⟶ U` be the chosen represented base change of `i` along `a`, an immersion of schemes.
Then `|P| → |U|` is an embedding with locally closed image, `|U| → |X|` is an open quotient
map on points, `|P| → |Z|` is surjective on points, and the point set of `j` is the preimage
of the point set of `i` by Tag 03H4. Each of the two conclusions is a transfer along that
square.

## Main definitions

* `AlgebraicGeometry.Space.schemePointsHomeomorph` is the Tag 03BX homeomorphism between the
  point space of a represented presheaf and the representing scheme. Its underlying bijection
  is `AlgebraicGeometry.Space.pointsEquivScheme`.

## Main results

* `AlgebraicGeometry.Space.isEmbedding_pointsMap_yoneda`,
  `AlgebraicGeometry.Space.isLocallyClosed_range_pointsMap_yoneda`: a morphism of the big fppf
  site of `S` whose underlying map of schemes is an embedding, respectively has locally closed
  image, has the same property on points.
* `AlgebraicGeometry.Space.injective_pointsMap_of_isImmersion`,
  `AlgebraicGeometry.Space.isInducing_pointsMap_of_isImmersion` and
  `AlgebraicGeometry.Space.isEmbedding_pointsMap_of_isImmersion`: the map on points of an
  immersion of algebraic spaces over `S` is a topological embedding.
* `AlgebraicGeometry.Space.isLocallyClosed_range_pointsMap_of_isImmersion`: its image is
  locally closed.

## Implementation notes

The point topology `AlgebraicGeometry.Space.pointTopology` is installed as a local instance,
as elsewhere in this directory.

`AlgebraicGeometry.Space.isLocallyClosed_of_isLocallyClosed_preimage` is the point-set
topology behind the second conclusion: local closedness descends along a continuous open
surjection, because such a map commutes with closure on preimages
(`IsOpenMap.preimage_closure_eq_closure_preimage`), hence with `coborder`, and is a quotient
map. This is Topology, Lemma 02YB of the source.

Injectivity on points is the one place where the source appeals to injectivity of the
transformation of functors `Z → X`. It is obtained here from the square instead: two points of
`|Z|` with the same image in `|X|` both lift, by Tag 03H4, to points of `|P|` over one and the
same point of `|U|`, and `|P| → |U|` is injective because an immersion of schemes is.

The inducing property needs no injectivity. An open set of `|Z|` pulls back to an open set of
`|P|`, which is the preimage along `|j|` of an open set `O` of `|U|` because `|j|` is inducing;
the image of `O` in `|X|` is open because the atlas is open on points, and its preimage in
`|Z|` is the original open set — one inclusion by Tag 03H4 and the other by surjectivity of
`|P| → |Z|`.

## References

* [Stacks Project, Tag 02YB](https://stacks.math.columbia.edu/tag/02YB)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03H5](https://stacks.math.columbia.edu/tag/03H5)
* [Stacks Project, Tag 0ABJ](https://stacks.math.columbia.edu/tag/0ABJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Local closedness descends along a continuous open surjection -/

/-- **Topology, Lemma 02YB.** A set whose preimage under a continuous, open and surjective map
is locally closed is itself locally closed.

Such a map commutes with closure on preimages, hence with `coborder`, and it is a quotient map,
so openness of the coborder descends. -/
theorem isLocallyClosed_of_isLocallyClosed_preimage {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {q : α → β} (hc : Continuous q) (ho : IsOpenMap q)
    (hsurj : Function.Surjective q) {s : Set β} (h : IsLocallyClosed (q ⁻¹' s)) :
    IsLocallyClosed s := by
  rw [isLocallyClosed_iff_isOpen_coborder] at h ⊢
  rw [← (ho.isQuotientMap hc hsurj).isCoinducing.isOpen_preimage]
  have hcob : q ⁻¹' coborder s = coborder (q ⁻¹' s) := by
    change q ⁻¹' (closure s \ s)ᶜ = (closure (q ⁻¹' s) \ q ⁻¹' s)ᶜ
    rw [Set.preimage_compl, Set.preimage_sdiff, ho.preimage_closure_eq_closure_preimage hc]
  rwa [hcob]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The point space of a represented presheaf, as a topological space -/

/-- The map on points of a morphism of the big fppf site of `S`, conjugated into the
underlying map of schemes by the homeomorphisms of
`AlgebraicGeometry.Space.schemePointsHomeomorph`. -/
theorem pointsMap_yoneda_eq_conj {U V : BigFppfOver B S hS} (h : U ⟶ V) :
    pointsMap B S hS (yoneda.obj U) (yoneda.map h) =
      (schemePointsHomeomorph B S hS V).symm ∘
        ⇑((BigFppfOver.toScheme B S hS).map h) ∘ (schemePointsHomeomorph B S hS U) := by
  funext w
  apply (schemePointsHomeomorph B S hS V).injective
  simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
  exact pointsToScheme_pointsMap_yoneda B S hS h w

/-- A morphism of the big fppf site of `S` whose underlying map of schemes is a topological
embedding induces a topological embedding on points. -/
theorem isEmbedding_pointsMap_yoneda {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (hh : Topology.IsEmbedding ⇑((BigFppfOver.toScheme B S hS).map h)) :
    Topology.IsEmbedding (pointsMap B S hS (yoneda.obj U) (yoneda.map h)) := by
  rw [pointsMap_yoneda_eq_conj]
  exact (schemePointsHomeomorph B S hS V).symm.isEmbedding.comp
    (hh.comp (schemePointsHomeomorph B S hS U).isEmbedding)

/-- The image on points of a morphism of the big fppf site of `S` is the preimage, under the
Tag 03BX comparison bijection, of the image of the underlying map of schemes. -/
theorem range_pointsMap_yoneda_eq_preimage {U V : BigFppfOver B S hS} (h : U ⟶ V) :
    Set.range (pointsMap B S hS (yoneda.obj U) (yoneda.map h)) =
      pointsToScheme B S hS V ⁻¹' Set.range ⇑((BigFppfOver.toScheme B S hS).map h) := by
  ext w
  rw [Set.mem_preimage]
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨pointsToScheme B S hS U v, (pointsToScheme_pointsMap_yoneda B S hS h v).symm⟩
  · rintro ⟨y, hy⟩
    obtain ⟨v, rfl⟩ := surjective_pointsToScheme B S hS U y
    refine ⟨v, (injective_pointsToScheme B S hS V) ?_⟩
    rwa [pointsToScheme_pointsMap_yoneda B S hS h v]

/-- A morphism of the big fppf site of `S` whose underlying map of schemes has locally closed
image has locally closed image on points. -/
theorem isLocallyClosed_range_pointsMap_yoneda {U V : BigFppfOver B S hS} (h : U ⟶ V)
    (hh : IsLocallyClosed (Set.range ⇑((BigFppfOver.toScheme B S hS).map h))) :
    IsLocallyClosed (Set.range (pointsMap B S hS (yoneda.obj U) (yoneda.map h))) := by
  rw [range_pointsMap_yoneda_eq_preimage]
  exact hh.preimage (schemePointsHomeomorph B S hS V).continuous

/-! ### The point map of an immersion -/

variable {Z X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- The map on points of the base change of an immersion of algebraic spaces along a map from a
scheme is a topological embedding. -/
private theorem isEmbedding_pointsMap_snd {U : BigFppfOver B S hS} {i : Z ⟶ X}
    (hi : IsImmersion B S hS i)
    (a : yoneda.obj U ⟶ X) :
    Topology.IsEmbedding
      (pointsMap B S hS (yoneda.obj (hi.rep.pullback a)) (yoneda.map (hi.rep.snd a))) := by
  have : _root_.AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd a)) := hi.property_snd a
  exact isEmbedding_pointsMap_yoneda B S hS _
    ((BigFppfOver.toScheme B S hS).map (hi.rep.snd a)).isEmbedding

/-- **Stacks 0ABJ, injectivity.** The map on points of an immersion of algebraic spaces over
`S` is injective.

Two points of `|Z|` with the same image in `|X|` lift, by Tag 03H4, to points of the base
change of `i` to an étale atlas of `X` lying over one and the same point of the atlas; the base
change is an immersion of schemes, hence injective on points. -/
theorem injective_pointsMap_of_isImmersion (hX : IsAlgebraicSpace B S hS X) (i : Z ⟶ X)
    (hi : IsImmersion B S hS i) :
    Function.Injective (pointsMap B S hS Z i) := by
  obtain ⟨U, a, haSurj, -⟩ := hX.exists_atlas
  intro z₁ z₂ hz
  obtain ⟨u, hu⟩ := (presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).mp haSurj
    (pointsMap B S hS Z i z₁)
  obtain ⟨p₁, hp₁f, hp₁j⟩ :=
    exists_points_of_isPullback B S hS (hi.rep.isPullback a) z₁ u hu.symm
  obtain ⟨p₂, hp₂f, hp₂j⟩ :=
    exists_points_of_isPullback B S hS (hi.rep.isPullback a) z₂ u (hu.trans hz).symm
  rw [← hp₁f, ← hp₂f, (isEmbedding_pointsMap_snd B S hS hi a).injective
    (hp₁j.trans hp₂j.symm)]

/-- **Stacks 0ABJ, the topology.** The map on points of an immersion of algebraic spaces over
`S` is topologically inducing: the point topology of the source is the topology induced from
the point space of the target. -/
theorem isInducing_pointsMap_of_isImmersion (hX : IsAlgebraicSpace B S hS X) (i : Z ⟶ X)
    (hi : IsImmersion B S hS i) :
    Topology.IsInducing (pointsMap B S hS Z i) := by
  obtain ⟨U, a, haSurj, haEtale⟩ := hX.exists_atlas
  refine (Topology.isInducing_iff _).mpr (le_antisymm
    (continuous_iff_le_induced.mp (continuous_pointsMap B S hS i))
    (TopologicalSpace.le_def.mpr fun W hW => isOpen_induced_iff.mpr ?_))
  obtain ⟨O, hO, hOeq⟩ := (isEmbedding_pointsMap_snd B S hS hi a).isInducing.isOpen_iff.mp
    (hW.preimage (continuous_pointsMap B S hS (hi.rep.fst a)))
  refine ⟨pointsMap B S hS (yoneda.obj U) a '' O,
    isOpenMap_pointsMap_of_presheafEtale B S hS a haEtale O hO, ?_⟩
  apply Set.eq_of_subset_of_subset
  · rintro z ⟨o, hoO, hoz⟩
    obtain ⟨p, hpf, hpj⟩ :=
      exists_points_of_isPullback B S hS (hi.rep.isPullback a) z o hoz.symm
    have hpW : p ∈ pointsMap B S hS (yoneda.obj (hi.rep.pullback a)) (hi.rep.fst a) ⁻¹' W := by
      rwa [← hOeq, Set.mem_preimage, hpj]
    rwa [← hpf]
  · intro z hz
    obtain ⟨p, hpf⟩ := surjective_pointsMap_of_isPullback B S hS (hi.rep.isPullback a).flip
      ((presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).mp haSurj) z
    have hpO : pointsMap B S hS (yoneda.obj (hi.rep.pullback a))
        (yoneda.map (hi.rep.snd a)) p ∈ O := by
      rwa [← Set.mem_preimage, hOeq, Set.mem_preimage, hpf]
    refine ⟨_, hpO, ?_⟩
    rw [← hpf]
    exact (pointsMap_apply_comm B S hS (hi.rep.isPullback a).w p).symm

/-- **Stacks 0ABJ, part one.** The map on points of an immersion of algebraic spaces over `S`
is a topological embedding: a homeomorphism onto its image. -/
@[stacks 0ABJ "homeomorphism onto the image"]
theorem isEmbedding_pointsMap_of_isImmersion (hX : IsAlgebraicSpace B S hS X) (i : Z ⟶ X)
    (hi : IsImmersion B S hS i) :
    Topology.IsEmbedding (pointsMap B S hS Z i) :=
  ⟨isInducing_pointsMap_of_isImmersion B S hS hX i hi,
    injective_pointsMap_of_isImmersion B S hS hX i hi⟩

/-- **Stacks 0ABJ, part two.** The image on points of an immersion of algebraic spaces over
`S` is a locally closed subset of the point space of the target. -/
@[stacks 0ABJ "locally closed image"]
theorem isLocallyClosed_range_pointsMap_of_isImmersion (hX : IsAlgebraicSpace B S hS X)
    (i : Z ⟶ X) (hi : IsImmersion B S hS i) :
    IsLocallyClosed (Set.range (pointsMap B S hS Z i)) := by
  obtain ⟨U, a, haSurj, haEtale⟩ := hX.exists_atlas
  have : _root_.AlgebraicGeometry.IsImmersion
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd a)) := hi.property_snd a
  refine isLocallyClosed_of_isLocallyClosed_preimage (continuous_pointsMap B S hS a)
    (isOpenMap_pointsMap_of_presheafEtale B S hS a haEtale)
    ((presheafSurjective_iff_isSurjective_yoneda B S hS X hX U a).mp haSurj) ?_
  rw [preimage_range_pointsMap_eq_range_pointsMap_snd B S hS hi.rep a]
  exact isLocallyClosed_range_pointsMap_yoneda B S hS (hi.rep.snd a)
    _root_.AlgebraicGeometry.IsImmersion.isLocallyClosed_range

add_to_stacks 04CD AlgebraicGeometry.Space.isEmbedding_pointsMap_of_isImmersion
add_to_stacks 04CD AlgebraicGeometry.Space.isLocallyClosed_range_pointsMap_of_isImmersion

end AlgebraicGeometry.Space

end
