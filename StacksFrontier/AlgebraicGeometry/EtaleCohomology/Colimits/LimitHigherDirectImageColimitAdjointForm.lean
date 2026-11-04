module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageColimit

/-!
# The colimit half of Stacks 0EYN, with the inverse images removed

`Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation` at the system of
direct images — the hypothesis `h0EYN` of [Stacks, Tag 0DV2] and, by
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isCompatibleFamily_coneDirectImageLeg`, the whole
of what the presentation predicate of [Stacks, Tag 09YQ] still asks at that system — is a
statement about *inverse* images: for every abelian sheaf `𝒢` on the small étale site of the limit
`X = lim X_i` and every family `τ_i : f_i^{-1}f_{i, *}𝓕 ⟶ 𝒢` compatible with the transition maps,
there is a unique `χ : 𝓕 ⟶ 𝒢` with `ι_i ≫ χ = τ_i`, the `ι_i` being the counits.

Inverse images are left adjoints built by sheafification, and every tool this library has for a
colimit of sites — [Stacks, Tag 09YN] and its descent along a restriction functor — speaks only of
*direct* images, which are restrictions along functors of sites with no sheafification in them.
This file removes the inverse images from the obligation: it states the same condition as a
descent statement for the direct images alone, and proves the two equivalent.

## Main definitions

* `Stacks.EtaleCohomology.LimitHigherDirectImage.IsDirectImageCompatible` — the compatibility of a
  family `σ_i : f_{i, *}𝓕 ⟶ f_{i, *}𝒢` with the identifications
  `Stacks.EtaleCohomology.coneDirectImageCompAb` of direct images along the factorisations
  `f_j = f_i ≫ f_{ji}` of the projections.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.IsDirectImageDescent` — **the obligation with the
  inverse images removed**: every compatible family of maps of direct images is `f_{i, *}χ` for a
  unique `χ : 𝓕 ⟶ 𝒢`.

## Main results

* `Stacks.EtaleCohomology.counit_comp_eq_iff` — the counit triangle `ι_Y ≫ χ = τ`, read through
  the adjunction, is the equation `R χ = τ̃` on the adjoint of `τ`.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.compatible_iff` — the compatibility of the family
  of maps out of the inverse images adjoint to a family `σ` of maps of direct images is the
  compatibility of `σ`.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.isDirectImageCompatible_homEquiv` — the same read
  in the other direction, starting from a family out of the inverse images.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.counit_comp_symm_eq_iff` — the counit triangle at
  a projection against the adjoint of a map of direct images.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.isPullbackColimitPresentation_iff` — **the two
  conditions agree.**

## Implementation notes

**Nothing is weakened.** The equivalence is the inverse-image/direct-image adjunction and nothing
else: the triangle `ι_i ≫ χ = τ_i` is `f_{i, *}χ = σ_i` on adjoints because `ι_i` is the counit
(`counit_comp_eq_iff` is the right triangle identity), and the compatibility of the `τ_i` is the
compatibility of the `σ_i` because the diagram map `f_j^{-1}f_{j, *}𝓕 ⟶ f_i^{-1}f_{i, *}𝓕` of
`Stacks.EtaleCohomology.directImageSystem` is itself an adjoint — of
`Stacks.EtaleCohomology.coneDirectImageCompAb` — so that the hexagon
`Stacks.EtaleCohomology.leftAdjointCompIso_inv_homEquiv_symm`, which the cocone half of
[Stacks, Tag 0EYN] already runs on, computes the whole left-hand side as one adjoint. The
quantifier over `𝒢` and the uniqueness of `χ` are untouched, and `χ` itself is the same morphism
on both sides.

**What is still owed.** `IsDirectImageDescent` mentions no inverse image, no sheafification and no
left adjoint: `Stacks.EtaleCohomology.smallEtalePushforwardAb` is restriction along
`Stacks.EtaleCohomology.smallEtaleBaseChange`, and `coneDirectImageCompAb` is the comparison of
two such restrictions. It is therefore exactly the shape that
`CategoryTheory.Sites.InverseSystem.InverseSystemOfFiniteSites.descent_along_restriction'` proves,
once the small étale site of `X` is presented as a colimit of the sites of the `X_i`. What is
missing for that is not the coefficients — `descent_along_restriction'` is at an arbitrary
coefficient category — nor any longer the *geometry*: the levels of
`Stacks.EtaleCohomology.affineEtaleSiteColimit` are categories of chosen pullback models, but the
identification of `(affineEtaleSiteColimit …).toLimit i`, composed with the crossing to Mathlib's
site, with base change along the projection of the limit cone is now carried, as
`Stacks.EtaleCohomology.AffineLimitCohomology.levelCrossingIso` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Colimits/SmallEtaleLimitLevelCrossing.lean`.

Neither is the transition coherence still owed: `D.u a ⋙ u i = u j` holds on the nose for the
system's own functors and only up to the base-change comparison once the levels are read through
that identification, and that discrepancy is
`Stacks.EtaleCohomology.AffineLimitCohomology.levelBaseChangeCrossing_transition`, across which
the universal property is carried by
`Stacks.EtaleCohomology.AffineLimitCohomology.restrictionIsColimitAb_levelBaseChange`.

Nor is the scheme universe an obstruction: this file
is at `Scheme.{u}` over an index in `Type v` with `u` and `v` independent variables, so the
development's `Scheme.{max u v}` is an *instance* of it and not a narrowing. Indeed, the bridge
`Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimitPresentation_directImageSystem_iff`,
which is this file's `isPullbackColimitPresentation_iff` composed with the comparison of the two
inverse images, applies verbatim at `D : Iᵒᵖ ⥤ Scheme.{max u v}` and
`AddCommGrpCat.{max u v + 1}`.

What is still owed, then, is only the *site crossing at the levels* and the reindexing: the legs
of `restrictionIsColimitAb_levelBaseChange` are indexed by `(affineEtaleSiteColimit …).system.I`
and start from the levels, whereas `IsDirectImageDescent` is indexed by `Iᵒᵖ` and starts from
Mathlib's small étale sites of the `X_i`. The crossing of the sites is
`Stacks.EtaleCohomology.AffineLimitCohomology.isEquivalence_levelEtaleRestrictionAb`; the
reindexing has to go through `(affineEtaleSiteColimit …).indexEquiv` rather than through an
equality, since `affineEtaleSiteColimit` is `@[no_expose]` and its body can never be exposed —
its levels are *chosen* fibre products and `CategoryTheory.Limits.pullback` reduces only through
Mathlib's `@[no_expose] CategoryTheory.Limits.getLimitCone`. And the two transition data have to
be identified: `levelBaseChangeCrossing_transition`, the conjugate of the on-the-nose cocone
identity, against `Stacks.EtaleCohomology.coneDirectImageCompAb`, the associativity of fibre
products.

## References

* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 0DV2](https://stacks.math.columbia.edu/tag/0DV2)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 09YN](https://stacks.math.columbia.edu/tag/09YN)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v₁ u₁ v₂ u₂ v u

namespace Stacks.EtaleCohomology

/-! ### The counit triangle, read through the adjunction -/

section Adjunction

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {L : C₁ ⥤ C₂} {R : C₂ ⥤ C₁}

/-- **A counit triangle is an equation on adjoints.** For an adjunction `L ⊣ R`, a morphism
`χ : Y ⟶ Z` and `τ : L(RY) ⟶ Z`, the triangle `ε_Y ≫ χ = τ` holds exactly when `R χ` is the
adjoint of `τ`.

The computation inside is the right triangle identity: the adjoint of `ε_Y ≫ χ` is `R χ`, which
the tree also records, for a fixed pair of adjunctions, as
`CategoryTheory.Adjunction.homEquiv_counit_comp`; it is reproved here as a `have` rather than
imported, that declaration living in the Mayer–Vietoris development of perfect complexes whose
import would carry the derived category into this file. -/
theorem counit_comp_eq_iff (adj : L ⊣ R) {Y Z : C₂} (χ : Y ⟶ Z) (τ : L.obj (R.obj Y) ⟶ Z) :
    adj.counit.app Y ≫ χ = τ ↔ R.map χ = adj.homEquiv (R.obj Y) Z τ := by
  have hc : adj.homEquiv (R.obj Y) Z (adj.counit.app Y ≫ χ) = R.map χ := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      adj.right_triangle_components, Category.id_comp]
  rw [← hc]
  exact (adj.homEquiv (R.obj Y) Z).apply_eq_iff_eq.symm

end Adjunction

namespace LimitHigherDirectImage

variable {I : Type v} [Preorder I] {DX : Iᵒᵖ ⥤ Scheme.{u}} (cX : Cone DX)
  (𝓕 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})

/-! ### The obligation with the inverse images removed -/

/-- **A family of maps of direct images, compatible with the identifications along the
factorisations of the projections.** For `a : i ⟶ j` in `Iᵒᵖ` the projection factors as
`f_j = f_i ≫ f_{ji}`, and `Stacks.EtaleCohomology.coneDirectImageCompAb` identifies
`f_{ji, *}f_{i, *}` with `f_{j, *}`; a family `σ_i : f_{i, *}𝓕 ⟶ f_{i, *}𝒢` is compatible when
`σ_j` is `f_{ji, *}σ_i` read through those identifications.

This is the adjoint form of the compatibility clause of
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation` at the system
`Stacks.EtaleCohomology.directImageSystem`; see
`Stacks.EtaleCohomology.LimitHigherDirectImage.compatible_iff`. -/
def IsDirectImageCompatible (𝒢 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})
    (σ : ∀ i : Iᵒᵖ, (smallEtalePushforwardAb (cX.π.app i)).obj 𝓕 ⟶
      (smallEtalePushforwardAb (cX.π.app i)).obj 𝒢) : Prop :=
  ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
    σ j =
      (coneDirectImageCompAb cX a).inv.app 𝓕 ≫
        (systemPushforward DX Ab.{u + 1} a).map (σ i) ≫
          (coneDirectImageCompAb cX a).hom.app 𝒢

/-- **The colimit half of [Stacks, Tag 0EYN] with the inverse images removed.** For every abelian
sheaf `𝒢` on the small étale site of the limit, every family of maps of direct images
`σ_i : f_{i, *}𝓕 ⟶ f_{i, *}𝒢` compatible with the identifications along the factorisations of the
projections is the family of direct images `f_{i, *}χ` of a unique `χ : 𝓕 ⟶ 𝒢`.

Only direct images occur: `Stacks.EtaleCohomology.smallEtalePushforwardAb` is restriction along
`Stacks.EtaleCohomology.smallEtaleBaseChange` and
`Stacks.EtaleCohomology.coneDirectImageCompAb` is a comparison of two such restrictions, so
neither a left adjoint nor a sheafification appears.
`Stacks.EtaleCohomology.LimitHigherDirectImage.isPullbackColimitPresentation_iff` identifies this
with the hypothesis `h0EYN` of [Stacks, Tag 0DV2]. -/
def IsDirectImageDescent : Prop :=
  ∀ (𝒢 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})
      (σ : ∀ i : Iᵒᵖ, (smallEtalePushforwardAb (cX.π.app i)).obj 𝓕 ⟶
        (smallEtalePushforwardAb (cX.π.app i)).obj 𝒢),
    IsDirectImageCompatible cX 𝓕 𝒢 σ →
      ∃! χ : 𝓕 ⟶ 𝒢, ∀ i : Iᵒᵖ, (smallEtalePushforwardAb (cX.π.app i)).map χ = σ i

/-! ### The two compatibilities agree -/

/-- **The compatibility of a family of maps out of the inverse images is the compatibility of the
adjoint family of maps of direct images.**

The left-hand side is the compatibility clause of
`Stacks.EtaleCohomology.LimitHigherDirectImage.IsPullbackColimitPresentation` at the system of
direct images, at the family out of the inverse images adjoint to `σ`; it is stated at that family
rather than at an arbitrary one so that the hexagon below applies with no round trip through the
adjunction, `Stacks.EtaleCohomology.LimitHigherDirectImage.isDirectImageCompatible_homEquiv` being
the reading that starts from an arbitrary family. Its first two factors are both adjoints —
`Stacks.EtaleCohomology.conePullbackComp` is the left adjoint comparison of
`Stacks.EtaleCohomology.coneDirectImageCompAb` and the transition map of
`Stacks.EtaleCohomology.directImageSystem` is the adjoint of that comparison at `𝓕` — so the whole
composite is a single adjoint, by the hexagon
`Stacks.EtaleCohomology.leftAdjointCompIso_inv_homEquiv_symm`. -/
theorem compatible_iff (𝒢 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})
    (σ : ∀ i : Iᵒᵖ, (smallEtalePushforwardAb (cX.π.app i)).obj 𝓕 ⟶
      (smallEtalePushforwardAb (cX.π.app i)).obj 𝒢) {i j : Iᵒᵖ} (a : i ⟶ j) :
    ((conePullbackComp cX a).inv.app ((directImageSystem DX Ab.{u + 1} cX 𝓕).obj j) ≫
        (smallEtalePullbackAb (cX.π.app i)).map
            ((directImageSystem DX Ab.{u + 1} cX 𝓕).map a) ≫
          ((smallEtaleAdjunctionAb (cX.π.app i)).homEquiv
            ((smallEtalePushforwardAb (cX.π.app i)).obj 𝓕) 𝒢).symm (σ i) =
      ((smallEtaleAdjunctionAb (cX.π.app j)).homEquiv
        ((smallEtalePushforwardAb (cX.π.app j)).obj 𝓕) 𝒢).symm (σ j)) ↔
      σ j =
        (coneDirectImageCompAb cX a).inv.app 𝓕 ≫
          (systemPushforward DX Ab.{u + 1} a).map (σ i) ≫
            (coneDirectImageCompAb cX a).hom.app 𝒢 := by
  refine (Iff.of_eq (congrArg (· = _) (leftAdjointCompIso_inv_homEquiv_symm
    (systemAdjunction DX Ab.{u + 1} a) (smallEtaleAdjunctionAb (cX.π.app i))
    (smallEtaleAdjunctionAb (cX.π.app j)) (coneDirectImageCompAb cX a)
    ((coneDirectImageCompAb cX a).inv.app 𝓕) (σ i)))).trans ?_
  exact (Equiv.apply_eq_iff_eq _).trans eq_comm

/-- **The compatibility of a family of maps out of the inverse images, transported to its adjoint
family of maps of direct images.** This is
`Stacks.EtaleCohomology.LimitHigherDirectImage.compatible_iff` read at `σ_i` the adjoint of `τ_i`,
where the round trip `ε`-adjoint-of-adjoint has to be undone at both ends. -/
theorem isDirectImageCompatible_homEquiv (𝒢 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})
    (τ : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj
      ((directImageSystem DX Ab.{u + 1} cX 𝓕).obj i) ⟶ 𝒢)
    (hτ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (conePullbackComp cX a).inv.app ((directImageSystem DX Ab.{u + 1} cX 𝓕).obj j) ≫
        (smallEtalePullbackAb (cX.π.app i)).map
            ((directImageSystem DX Ab.{u + 1} cX 𝓕).map a) ≫ τ i = τ j) :
    IsDirectImageCompatible cX 𝓕 𝒢 (fun i =>
      (smallEtaleAdjunctionAb (cX.π.app i)).homEquiv
        ((smallEtalePushforwardAb (cX.π.app i)).obj 𝓕) 𝒢 (τ i)) := by
  intro i j a
  refine (compatible_iff cX 𝓕 𝒢 (fun i =>
    (smallEtaleAdjunctionAb (cX.π.app i)).homEquiv
      ((smallEtalePushforwardAb (cX.π.app i)).obj 𝓕) 𝒢 (τ i)) a).mp ?_
  exact ((congrArg (_ ≫ _ ≫ ·) (Equiv.symm_apply_apply _ _)).trans (hτ a)).trans
    (Equiv.symm_apply_apply _ _).symm

/-- **The counit triangle at a projection, against the adjoint of a map of direct images.**
`ι_i ≫ χ` is the adjoint of `σ_i` exactly when `f_{i, *}χ = σ_i`. This is
`Stacks.EtaleCohomology.counit_comp_eq_iff` at the inverse-image/direct-image adjunction of the
projection, with the right-hand side read back through the adjunction. -/
theorem counit_comp_symm_eq_iff (𝒢 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1})
    (σ : ∀ i : Iᵒᵖ, (smallEtalePushforwardAb (cX.π.app i)).obj 𝓕 ⟶
      (smallEtalePushforwardAb (cX.π.app i)).obj 𝒢) (χ : 𝓕 ⟶ 𝒢) (i : Iᵒᵖ) :
    coneDirectImageCounit cX 𝓕 i ≫ χ =
        ((smallEtaleAdjunctionAb (cX.π.app i)).homEquiv
          ((smallEtalePushforwardAb (cX.π.app i)).obj 𝓕) 𝒢).symm (σ i) ↔
      (smallEtalePushforwardAb (cX.π.app i)).map χ = σ i := by
  refine (counit_comp_eq_iff (smallEtaleAdjunctionAb (cX.π.app i)) χ _).trans ?_
  rw [Equiv.apply_symm_apply]

/-- **The colimit half of [Stacks, Tag 0EYN] is the descent statement for the direct images.**
The hypothesis `h0EYN` of [Stacks, Tag 0DV2] — that the counits present
`𝓕 = colim_i f_i^{-1}f_{i, *}𝓕` — holds exactly when every compatible family of maps of direct
images is the family of direct images of a unique map out of `𝓕`.

The morphism `χ` is the same on both sides; what the equivalence removes is the inverse image,
which is a left adjoint built by sheafification and about which the colimit-of-sites machinery of
[Stacks, Tag 09YN] says nothing. See the module docstring. -/
theorem isPullbackColimitPresentation_iff :
    IsPullbackColimitPresentation cX 𝓕 (directImageSystem DX Ab.{u + 1} cX 𝓕)
        (coneDirectImageCounit cX 𝓕) ↔
      IsDirectImageDescent cX 𝓕 := by
  constructor
  · intro h 𝒢 σ hσ
    obtain ⟨χ, hχ, hχu⟩ :=
      h 𝒢 (fun i => ((smallEtaleAdjunctionAb (cX.π.app i)).homEquiv
            ((smallEtalePushforwardAb (cX.π.app i)).obj 𝓕) 𝒢).symm (σ i))
        fun a => (compatible_iff cX 𝓕 𝒢 σ a).mpr (hσ a)
    exact ⟨χ, fun i => (counit_comp_symm_eq_iff cX 𝓕 𝒢 σ χ i).mp (hχ i),
      fun y hy => hχu y fun i => (counit_comp_symm_eq_iff cX 𝓕 𝒢 σ y i).mpr (hy i)⟩
  · intro h 𝒢 τ hτ
    obtain ⟨χ, hχ, hχu⟩ :=
      h 𝒢 (fun i => (smallEtaleAdjunctionAb (cX.π.app i)).homEquiv
            ((smallEtalePushforwardAb (cX.π.app i)).obj 𝓕) 𝒢 (τ i))
        (isDirectImageCompatible_homEquiv cX 𝓕 𝒢 τ hτ)
    exact ⟨χ, fun i =>
        (counit_comp_eq_iff (smallEtaleAdjunctionAb (cX.π.app i)) χ (τ i)).mpr (hχ i),
      fun y hy => hχu y fun i =>
        (counit_comp_eq_iff (smallEtaleAdjunctionAb (cX.π.app i)) y (τ i)).mp (hy i)⟩

end LimitHigherDirectImage

end Stacks.EtaleCohomology

end
