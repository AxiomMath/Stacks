module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Sheafify
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.Abelian
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.DerivedPushforwardComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 01AX — closed immersions and abelian sheaves

Let `i : Z ⟶ X` be a closed embedding of topological spaces. Stacks 01AX states four things
about the pushforward `i_* : Ab(Z) ⥤ Ab(X)` on sheaves of abelian groups: it is exact, it is
fully faithful, its essential image consists exactly of the abelian sheaves whose support is
contained in the image of `i`, and `i^{-1}` is a left inverse to it.

The two clauses proved here are exactness and the essential-image description. The other two
are already in the library, for an *inducing* map and for an arbitrary value category
(`StacksFrontier.Topology.Sheaves.ClosedImmersion.Pushforward`), and are registered against this
tag at the end of the file.

## Main definitions

* `Stacks.AbelianSheaf.support` is the support of a sheaf of abelian groups: the set of points
  at which its stalk fails to be a zero object.
* `Stacks.ClosedImmersion.stalkPushforwardNatIso` is the natural isomorphism identifying the
  stalk of `i_* 𝒜` at `i z` with the stalk of `𝒜` at `z`.

## Main results

* `Stacks.ClosedImmersion.exactFunctor_closedInclusionPushforward`: `i_*` is exact.
* `Stacks.ClosedImmersion.closedInclusionPushforward_full_faithful_and_essImage_iff`: Stacks
  00AG in full — `i_*` is fully faithful with essential image the sheaves whose stalks vanish
  off the image of `i`.
* `Stacks.ClosedImmersion.essImage_closedInclusionPushforward_iff_forall_stalk_isZero` and
  `Stacks.ClosedImmersion.essImage_closedInclusionPushforward_iff_support_subset`: the
  essential image of `i_*` consists exactly of the abelian sheaves supported on the image
  of `i`.

## Implementation notes

Exactness is checked on stalks. `TopCat.Sheaf.exact_iff_stalkFunctor_map_exact` reduces
exactness of a short complex of abelian sheaves on `X` to exactness of every stalk complex.
At a point `i z` of the image, `TopCat.Presheaf.stalkPushforward` is an isomorphism because a
closed embedding is inducing, and it is natural in the sheaf
(`Stacks.ClosedImmersion.stalkPushforward_naturality`); assembling the two gives a natural
isomorphism of `i_* ⋙ (stalk at i z)` with `stalk at z`, so the stalk complex at `i z` is
isomorphic to the stalk complex at `z`, which is exact by hypothesis. At a point off the image
the stalk of `i_* 𝒜` is a zero object by Stacks 00AE
(`closedInclusion_pushforward_stalk_isZero_of_not_mem_range`), so the stalk complex is exact
for trivial reasons. The passage from "preserves exact short complexes" to
"preserves finite limits and finite colimits" is `CategoryTheory.Functor.exact_tfae`, for which
`i_*` must be known to be additive; on underlying presheaves `i_*` is precomposition with
`Opens.map i`, so additivity is `rfl`.

The essential-image description is proved by exhibiting the sheafification `ℱ` of `i^{-1} G` as
a preimage: the morphism `G ⟶ i_* ℱ` obtained from the unit of `i^{-1} ⊣ i_*` followed by
`i_*` of the sheafification map is an isomorphism. Again this is checked on stalks. Off the
image both stalks are zero. At `i z` the composite of the stalk of that morphism with
`stalkPushforward` is the stalk-pullback isomorphism followed by the stalk of the
sheafification map, which is
`Stacks.ClosedImmersion.stalkFunctor_map_unit_comp_stalkPushforward` — a *definitional*
identity once the naturality of `stalkPushforward` has been applied, since
`TopCat.Presheaf.stalkPullbackHom` is by definition the stalk of the unit followed by
`stalkPushforward`. Both outer factors are isomorphisms, hence so is the stalk of the
morphism.

`TopCat.Presheaf.stalk` is *defined* as `(stalkFunctor C x).obj`, but not reducibly, so the
two spellings are not interchangeable at the `implicit` transparency that `rw` uses when
checking type-correctness of a motive. The two declarations that mix them are therefore
written under `attribute [local implicit_reducible]`, as
`Stacks.ClosedImmersion.stalkPushforward_naturality` already is.

## References

* [Stacks Project, Lemma 17.6.1 (Tag 01AX)](https://stacks.math.columbia.edu/tag/01AX)
* [Stacks Project, Lemma 6.32.1 (Tag 00AG)](https://stacks.math.columbia.edu/tag/00AG)
* [Stacks Project, Lemma 6.31.4 (Tag 00AE)](https://stacks.math.columbia.edu/tag/00AE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology TopCat.Presheaf

universe u

namespace Stacks.AbelianSheaf

/-- The **support** of a sheaf of abelian groups: the set of points at which its stalk is not a
zero object. Stacks 01AX describes the essential image of pushforward along a closed embedding
in terms of this set. -/
def support {X : TopCat.{u}} (G : TopCat.Sheaf AddCommGrpCat.{u} X) : Set X :=
  {x | ¬ IsZero (G.presheaf.stalk x)}

/-- A point lies outside the support of `G` exactly when the stalk of `G` there is zero. -/
lemma notMem_support_iff {X : TopCat.{u}} (G : TopCat.Sheaf AddCommGrpCat.{u} X) (x : X) :
    x ∉ support G ↔ IsZero (G.presheaf.stalk x) :=
  not_not

/-- The support of `G` is contained in a set `S` exactly when the stalk of `G` vanishes at
every point outside `S`. -/
lemma support_subset_iff {X : TopCat.{u}} (G : TopCat.Sheaf AddCommGrpCat.{u} X) (S : Set X) :
    support G ⊆ S ↔ ∀ x : X, x ∉ S → IsZero (G.presheaf.stalk x) := by
  constructor
  · exact fun h x hx => not_not.mp fun hz => hx (h hz)
  · intro h x hx
    by_contra hxS
    exact hx (h x hxS)

end Stacks.AbelianSheaf

namespace Stacks.ClosedImmersion

variable {Z X : TopCat.{u}} (i : Z ⟶ X)

/-! ### Stalks of `i_*` over the image -/

/-- For an inducing map `i` and a point `z` of `Z`, taking the stalk at `i z` of the
pushforward is naturally isomorphic to taking the stalk at `z`. The isomorphism is
`TopCat.Presheaf.stalkPushforward`, which is invertible because `i` is inducing and natural in
the sheaf by `Stacks.ClosedImmersion.stalkPushforward_naturality`. -/
noncomputable def stalkPushforwardNatIso (hi : IsInducing i.hom) (z : Z) :
    closedInclusionPushforward Z X i ⋙
        TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙ stalkFunctor AddCommGrpCat.{u} (i.hom z) ≅
      TopCat.Sheaf.forget AddCommGrpCat.{u} Z ⋙ stalkFunctor AddCommGrpCat.{u} z :=
  NatIso.ofComponents
    (fun 𝒜 => @asIso _ _ _ _ (stalkPushforward AddCommGrpCat.{u} i 𝒜.1 z)
      (stalkPushforward.stalkPushforward_iso_of_isInducing (C := AddCommGrpCat.{u}) hi 𝒜.1 z))
    (fun {_ _} φ => Stacks.ClosedImmersion.stalkPushforward_naturality i φ.hom z)

/-! ### Exactness -/

/-- Pushforward of sheaves of abelian groups along a (closed) inclusion is additive: on
underlying presheaves it is precomposition with `Opens.map i`. -/
instance additive_closedInclusionPushforward :
    (closedInclusionPushforward Z X i).Additive where
  map_add := by intros; rfl

/-- **Stacks 01AX, exactness.** Pushforward of sheaves of abelian groups along a closed
embedding `i : Z ⟶ X` is an exact functor `Ab(Z) ⥤ Ab(X)`.

Exactness is detected on stalks. Over a point of the image of `i` the stalk of `i_* 𝒜` is the
stalk of `𝒜`, naturally in `𝒜`, because a closed embedding is inducing; over a point off the
image the stalk of `i_* 𝒜` vanishes. -/
@[stacks 01AX "exactness"]
theorem exactFunctor_closedInclusionPushforward (hi : IsClosedEmbedding i.hom) :
    exactFunctor (TopCat.Sheaf AddCommGrpCat.{u} Z) (TopCat.Sheaf AddCommGrpCat.{u} X)
      (closedInclusionPushforward Z X i) := by
  refine ((Functor.exact_tfae (closedInclusionPushforward Z X i)).out 2 4).mp ?_
  intro S hS
  rw [TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
  intro x
  by_cases hx : x ∈ Set.range i.hom
  · obtain ⟨z, rfl⟩ := hx
    exact ShortComplex.exact_of_iso
      (ShortComplex.mapNatIso S (stalkPushforwardNatIso i hi.isInducing z)).symm
      ((TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mp hS z)
  · exact ShortComplex.exact_of_isZero_X₂ _
      (closedInclusion_pushforward_stalk_isZero_of_not_mem_range Z X i hi S.X₂ x hx)

/-- **Stacks 01AX, exactness.** Pushforward along a closed embedding preserves finite
limits. -/
@[stacks 01AX "exactness: left exactness"]
theorem preservesFiniteLimits_closedInclusionPushforward (hi : IsClosedEmbedding i.hom) :
    PreservesFiniteLimits (closedInclusionPushforward Z X i) :=
  (exactFunctor_closedInclusionPushforward i hi).1

/-- **Stacks 01AX, exactness.** Pushforward along a closed embedding preserves finite
colimits. -/
@[stacks 01AX "exactness: right exactness"]
theorem preservesFiniteColimits_closedInclusionPushforward (hi : IsClosedEmbedding i.hom) :
    PreservesFiniteColimits (closedInclusionPushforward Z X i) :=
  (exactFunctor_closedInclusionPushforward i hi).2

/-! ### The essential image -/

attribute [local implicit_reducible] TopCat.Presheaf.stalk TopCat.Presheaf.stalkFunctor in
/-- The stalk at `i z` of the canonical morphism `G ⟶ i_* ℱ` built from the unit of
`i^{-1} ⊣ i_*` followed by `i_*` of a morphism `α : i^{-1} G ⟶ ℱ`, composed with the
comparison `(i_* ℱ)_{i z} ⟶ ℱ_z`, is the stalk-pullback isomorphism followed by the stalk
of `α`.

Once the naturality of `TopCat.Presheaf.stalkPushforward` has been used this is definitional:
`TopCat.Presheaf.stalkPullbackHom` *is* the stalk of the unit followed by
`stalkPushforward`. -/
theorem stalkFunctor_map_unit_comp_stalkPushforward (G : X.Presheaf AddCommGrpCat.{u})
    {ℱ : Z.Presheaf AddCommGrpCat.{u}}
    (α : (TopCat.Presheaf.pullback AddCommGrpCat.{u} i).obj G ⟶ ℱ) (z : Z) :
    (stalkFunctor AddCommGrpCat.{u} (i.hom z)).map
        ((TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app G ≫
          (TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map α) ≫
        ℱ.stalkPushforward AddCommGrpCat.{u} i z =
      (TopCat.Presheaf.stalkPullbackIso AddCommGrpCat.{u} i G z).hom ≫
        (stalkFunctor AddCommGrpCat.{u} z).map α := by
  rw [Functor.map_comp_assoc, Stacks.ClosedImmersion.stalkPushforward_naturality,
    ← Category.assoc]
  rfl

/-- **Stacks 01AX, essential image.** A sheaf `G` of abelian groups on `X` is in the essential
image of pushforward along the closed embedding `i : Z ⟶ X` if and only if the stalk of `G`
vanishes at every point outside the image of `i`.

The forward direction is Stacks 00AG
(`closedInclusion_pushforward_essImage_stalk_isZero`). For the converse the preimage is the
sheafification `ℱ` of `i^{-1} G`; the canonical morphism `η : G ⟶ i_* ℱ` is an isomorphism
because it is one on every stalk: off the image of `i` both stalks vanish, and at `i z` the
composite of the stalk of `η` with the isomorphism `(i_* ℱ)_{i z} ⟶ ℱ_z` is an isomorphism by
`stalkFunctor_map_unit_comp_stalkPushforward` together with
`TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`. -/
@[stacks 01AX "essential image", ega "0 4.2.5" "Ψ_*M is zero outside X"]
theorem essImage_closedInclusionPushforward_iff_forall_stalk_isZero
    (hi : IsClosedEmbedding i.hom) (G : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (closedInclusionPushforward Z X i).essImage G ↔
      ∀ x : X, x ∉ Set.range i.hom → IsZero (G.presheaf.stalk x) := by
  refine ⟨closedInclusion_pushforward_essImage_stalk_isZero Z X i hi G, fun hG => ?_⟩
  set P := (TopCat.Presheaf.pullback AddCommGrpCat.{u} i).obj G.presheaf with hP
  set ℱ : TopCat.Sheaf AddCommGrpCat.{u} Z :=
    (presheafToSheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{u}).obj P with hℱ
  set α := CategoryTheory.toSheafify (Opens.grothendieckTopology Z) P with hα
  set η : G ⟶ (closedInclusionPushforward Z X i).obj ℱ :=
    ⟨(TopCat.Presheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} i).unit.app G.presheaf ≫
      (TopCat.Presheaf.pushforward AddCommGrpCat.{u} i).map α⟩ with hη
  have hiso : IsIso η := by
    rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
    intro x
    by_cases hx : x ∈ Set.range i.hom
    · obtain ⟨z, rfl⟩ := hx
      have hs : IsIso (ℱ.presheaf.stalkPushforward AddCommGrpCat.{u} i z) :=
        inferInstanceAs (IsIso ((stalkPushforwardNatIso i hi.isInducing z).hom.app ℱ))
      have hα' : IsIso ((stalkFunctor AddCommGrpCat.{u} z).map α) :=
        TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso z AddCommGrpCat.{u} P
      refine @IsIso.of_isIso_comp_right _ _ _ _ _
        ((stalkFunctor AddCommGrpCat.{u} (i.hom z)).map η.hom)
        (ℱ.presheaf.stalkPushforward AddCommGrpCat.{u} i z) hs ?_
      erw [stalkFunctor_map_unit_comp_stalkPushforward i G.presheaf α z]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) hα'
    · exact (hG x hx).isIso
        (closedInclusion_pushforward_stalk_isZero_of_not_mem_range Z X i hi ℱ x hx) _
  exact ⟨ℱ, ⟨(asIso η).symm⟩⟩

/-- **Stacks 01AX, essential image.** The essential image of pushforward along a closed
embedding `i : Z ⟶ X` consists exactly of the sheaves of abelian groups whose support is
contained in the image of `i`.

This is the source's phrasing of
`essImage_closedInclusionPushforward_iff_forall_stalk_isZero`, since the support of an abelian
sheaf is by definition the set of points with nonzero stalk. -/
@[stacks 01AX "essential image, in terms of the support", ega "0 4.2.5" "Ψ_*M is zero outside X"]
theorem essImage_closedInclusionPushforward_iff_support_subset
    (hi : IsClosedEmbedding i.hom) (G : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (closedInclusionPushforward Z X i).essImage G ↔
      Stacks.AbelianSheaf.support G ⊆ Set.range i.hom :=
  (essImage_closedInclusionPushforward_iff_forall_stalk_isZero i hi G).trans
    (Stacks.AbelianSheaf.support_subset_iff G _).symm

/-! ### Stacks 00AG -/

/-- **Stacks 00AG.** Let `i : Z ⟶ X` be a closed embedding of topological spaces. The
pushforward `i_* : Ab(Z) ⥤ Ab(X)` on sheaves of abelian groups is fully faithful, and its
essential image consists exactly of the sheaves `G` with `G_x = 0` for every `x ∈ X` outside
the image of `i`.

Fullness and faithfulness are `closedInclusion_pushforward_full` and
`closedInclusion_pushforward_faithful`; the description of the essential image, in both
directions, is `essImage_closedInclusionPushforward_iff_forall_stalk_isZero`. -/
@[stacks 00AG]
theorem closedInclusionPushforward_full_faithful_and_essImage_iff
    (hi : IsClosedEmbedding i.hom) :
    (closedInclusionPushforward Z X i).Full ∧ (closedInclusionPushforward Z X i).Faithful ∧
      ∀ G : TopCat.Sheaf AddCommGrpCat.{u} X, (closedInclusionPushforward Z X i).essImage G ↔
        ∀ x : X, x ∉ Set.range i.hom → IsZero (G.presheaf.stalk x) :=
  ⟨closedInclusion_pushforward_full Z X i hi, closedInclusion_pushforward_faithful Z X i hi,
    essImage_closedInclusionPushforward_iff_forall_stalk_isZero i hi⟩

/-! ### The remaining clauses of the tag

Full faithfulness of `i_*` and the fact that `i^{-1}` is a left inverse to it are already in
the library, proved for an arbitrary *inducing* map and an arbitrary value category; a closed
embedding is inducing, so they cover this tag. They are registered against it here. -/

add_to_stacks 01AX "fully faithful: faithfulness" closedInclusion_pushforward_faithful
add_to_stacks 01AX "fully faithful: fullness" closedInclusion_pushforward_full
add_to_stacks 01AX "`i^{-1}` is a left inverse to `i_*`: the counit of `i^{-1} ⊣ i_*` is an
  isomorphism" ClosedImmersionSheaves.sheaf_pullback_pushforward_counit_isIso

end Stacks.ClosedImmersion

end
