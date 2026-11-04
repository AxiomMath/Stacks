module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.ClosedUnionPushoutClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.Schemes
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableClosedSubspaceIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsOfPullback

/-!
# Four closed subschemes of an object of the site, as a pushout square of algebraic spaces

Let `V` be an object of the big fppf site over a scheme `S` and let `j₁, j₂, j₃, j₄` be closed
immersions of the site into `V` whose sheaves of ideals are `I`, `J`, `I ⊔ J` and `I ⊓ J`.  This
file proves that the resulting square of representable algebraic spaces is a pushout square in
the category of algebraic spaces over `S`.  It is the representable core of the third assertion
of [Stacks Project, Tag 0CZ1]; the passage to closed subspaces and then to a general ambient
algebraic space is `StacksFrontier/AlgebraicGeometry/Spaces/ClosedUnionPushout.lean`.

Two results are combined.  On the scheme side,
`AlgebraicGeometry.isPushout_of_ker_eq_inf` says that the four closed subschemes of `V` cut out
by `I`, `J`, `I ⊔ J` and `I ⊓ J` form a pushout square of schemes, which is [Stacks Project,
Tag 0C4J].  On the algebraic-space side,
`AlgebraicGeometry.Space.pushout_isPushout_algebraicSpaces` says that a scheme pushout in the
standing situation of [Stacks Project, Tag 0ECI] is a pushout against *every* algebraic space
over `S`, which is [Stacks Project, Tag 0EDP]; a span of two closed immersions is such a
situation, because a closed immersion is integral and has at most one point in each fibre so
that the affine-neighbourhood condition is the existence of an affine open around a point.
Comparing the two pushouts of the same span gives an isomorphism of their apexes, along which
Tag 0EDP transports onto the square of the four closed subschemes.

The passage from this square of representable presheaves to the square of closed subspaces of
`h_V` is carried out in `StacksFrontier/AlgebraicGeometry/Spaces/ClosedUnionPushout.lean`, through
the dictionary of `StacksFrontier/AlgebraicGeometry/Spaces/RepresentableClosedSubspaceIdeal.lean`.

## Main definitions

* `AlgebraicGeometry.Space.siteIsoOfSchemeIso`: an isomorphism of the underlying schemes over
  `S` of two objects of the site, read as an isomorphism of the site.
* `AlgebraicGeometry.Space.closedImmersionSpanSituation`: the standing situation of Tag 0ECI
  attached to a span of two closed immersions of the site, with base the base scheme itself.

## Main results

* `AlgebraicGeometry.Space.exists_iso_pushoutScheme`: the apex of the scheme pushout of
  Tag 0E25 is isomorphic, compatibly with the two legs, to the apex of any other pushout of the
  same span.
* `AlgebraicGeometry.Space.isPushout_yoneda_of_ker_eq_inf`: **the representable core of the
  third assertion of Tag 0CZ1** — the square of the four representable algebraic spaces
  attached to four closed immersions of the site with sheaves of ideals `I`, `J`, `I ⊔ J` and
  `I ⊓ J` is a pushout square of algebraic spaces over `S`.

## Implementation notes

The situation of Tag 0ECI records the four schemes and their structure morphisms as *data*, so
building it from a span of the site requires choosing those; the choice made here —
`B.inclusion.map R.hom` for the structure morphism of the object `R` — is the one for which
`AlgebraicGeometry.Space.fppfOverX` and its companions return the given objects of the site on
the nose, so that Tag 0EDP needs no transport at three of its four corners.  That is why
`AlgebraicGeometry.Space.closedImmersionSpanSituation_fppfOverX` and its companions are proved
by `rfl`.

## References

* [Stacks Project, Tag 0CZ1](https://stacks.math.columbia.edu/tag/0CZ1)
* [Stacks Project, Tag 0CYZ](https://stacks.math.columbia.edu/tag/0CYZ)
* [Stacks Project, Tag 0C4J](https://stacks.math.columbia.edu/tag/0C4J)
* [Stacks Project, Tag 0ECI](https://stacks.math.columbia.edu/tag/0ECI)
* [Stacks Project, Tag 0EDP](https://stacks.math.columbia.edu/tag/0EDP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Isomorphisms of the site -/

/-- **An isomorphism of the underlying schemes of two objects of the site which is compatible
with their structure morphisms to `S` is an isomorphism of the site.**  A morphism of the site is
determined by the underlying morphism of schemes,
`AlgebraicGeometry.BigFppfOver.map_toScheme_injective`, so the two composites are identities. -/
def siteIsoOfSchemeIso {T T' : BigFppfOver B S hS}
    (σ : (BigFppfOver.toScheme B S hS).obj T ≅ (BigFppfOver.toScheme B S hS).obj T')
    (hσ : σ.hom ≫ B.inclusion.map T'.hom = B.inclusion.map T.hom) : T ≅ T' where
  hom := Over.homMk (ObjectProperty.homMk σ.hom) (by apply ObjectProperty.hom_ext; exact hσ)
  inv := Over.homMk (ObjectProperty.homMk σ.inv) (by
    apply ObjectProperty.hom_ext
    exact show σ.inv ≫ B.inclusion.map T.hom = B.inclusion.map T'.hom by
      rw [← hσ, Iso.inv_hom_id_assoc])
  hom_inv_id := (BigFppfOver.toScheme B S hS).map_injective (by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    exact σ.hom_inv_id)
  inv_hom_id := (BigFppfOver.toScheme B S hS).map_injective (by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id]
    exact σ.inv_hom_id)

/-- The morphism of schemes underlying `AlgebraicGeometry.Space.siteIsoOfSchemeIso` is the given
isomorphism of schemes. -/
@[simp]
theorem toScheme_map_siteIsoOfSchemeIso_hom {T T' : BigFppfOver B S hS}
    (σ : (BigFppfOver.toScheme B S hS).obj T ≅ (BigFppfOver.toScheme B S hS).obj T')
    (hσ : σ.hom ≫ B.inclusion.map T'.hom = B.inclusion.map T.hom) :
    (BigFppfOver.toScheme B S hS).map (siteIsoOfSchemeIso B S hS σ hσ).hom = σ.hom := rfl

/-! ### The pushout situation attached to a span of closed immersions of the site -/

/-- A morphism of the site whose composite with a closed immersion is a closed immersion has a
closed immersion as underlying morphism of schemes. -/
private theorem isClosedImmersion_toScheme_map_of_comp {X Y Z : BigFppfOver B S hS}
    {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z} (hfg : f ≫ g = h)
    [_root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map g)]
    [_root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map h)] :
    _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map f) := by
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map f ≫ (BigFppfOver.toScheme B S hS).map g) := by
    rw [← Functor.map_comp, hfg]
    infer_instance
  exact .of_comp _ ((BigFppfOver.toScheme B S hS).map g)

/-- **The standing situation of [Stacks Project, Tag 0ECI] attached to a span of two closed
immersions of the big fppf category over `S`**, with the base scheme `S` as base.

The second morphism is integral because a closed immersion is finite.  The affine-neighbourhood
condition holds because a closed immersion is injective on points, so each of its fibres has at
most one point, and the affine opens of a scheme form a basis of its topology. -/
noncomputable def closedImmersionSpanSituation {R₁ R₂ R₃ : BigFppfOver B S hS}
    (a₁ : R₃ ⟶ R₁) (a₂ : R₃ ⟶ R₂)
    (ha₁ : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map a₁))
    (ha₂ : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map a₂)) :
    PushoutAlongClosedImmersionAndIntegralSituation.{u} where
  S := S
  X := (BigFppfOver.toScheme B S hS).obj R₁
  Y := (BigFppfOver.toScheme B S hS).obj R₂
  Z := (BigFppfOver.toScheme B S hS).obj R₃
  pX := B.inclusion.map R₁.hom
  pY := B.inclusion.map R₂.hom
  pZ := B.inclusion.map R₃.hom
  i := (BigFppfOver.toScheme B S hS).map a₁
  j := (BigFppfOver.toScheme B S hS).map a₂
  isClosedImmersion_i := ha₁
  isIntegralHom_j :=
    @_root_.AlgebraicGeometry.IsIntegralHom.instOfIsClosedImmersion _ _ _ ha₂
  i_over := toScheme_map_comp_inclusion_hom B S hS a₁
  j_over := toScheme_map_comp_inclusion_hom B S hS a₂
  fiber_preimage_subset_affine := by
    intro y
    by_cases hy : ∃ z, (BigFppfOver.toScheme B S hS).map a₂ z = y
    · obtain ⟨z, rfl⟩ := hy
      obtain ⟨-, ⟨U, hU, rfl⟩, hzi, -⟩ :=
        ((BigFppfOver.toScheme B S hS).obj R₁).isBasis_affineOpens.exists_subset_of_mem_open
          (a := (BigFppfOver.toScheme B S hS).map a₁ z) (by trivial) isOpen_univ
      refine ⟨U, hU, fun z' hz' => ?_⟩
      simpa [((BigFppfOver.toScheme B S hS).map a₂).isClosedEmbedding.injective hz'] using hzi
    · exact ⟨⊥, isAffineOpen_bot _, fun z hz => absurd ⟨z, hz⟩ hy⟩

section Situation

variable {R₁ R₂ R₃ : BigFppfOver B S hS} (a₁ : R₃ ⟶ R₁) (a₂ : R₃ ⟶ R₂)
    (ha₁ : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map a₁))
    (ha₂ : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map a₂))

/-- The first scheme of `AlgebraicGeometry.Space.closedImmersionSpanSituation`, read back as an
object of the site, is the first object of the span. -/
theorem closedImmersionSpanSituation_fppfOverX :
    fppfOverX (closedImmersionSpanSituation B S hS a₁ a₂ ha₁ ha₂) B hS R₁.left.2 = R₁ := rfl

/-- The second scheme of `AlgebraicGeometry.Space.closedImmersionSpanSituation`, read back as an
object of the site, is the second object of the span. -/
theorem closedImmersionSpanSituation_fppfOverY :
    fppfOverY (closedImmersionSpanSituation B S hS a₁ a₂ ha₁ ha₂) B hS R₂.left.2 = R₂ := rfl

/-- The common source of `AlgebraicGeometry.Space.closedImmersionSpanSituation`, read back as an
object of the site, is the source of the span. -/
theorem closedImmersionSpanSituation_fppfOverZ :
    fppfOverZ (closedImmersionSpanSituation B S hS a₁ a₂ ha₁ ha₂) B hS R₃.left.2 = R₃ := rfl

/-- The structure morphism of the first scheme of
`AlgebraicGeometry.Space.closedImmersionSpanSituation` is that of the first object of the span. -/
theorem closedImmersionSpanSituation_pX :
    (closedImmersionSpanSituation B S hS a₁ a₂ ha₁ ha₂).pX = B.inclusion.map R₁.hom := rfl

/-- The structure morphism of the second scheme of
`AlgebraicGeometry.Space.closedImmersionSpanSituation` is that of the second object of the
span. -/
theorem closedImmersionSpanSituation_pY :
    (closedImmersionSpanSituation B S hS a₁ a₂ ha₁ ha₂).pY = B.inclusion.map R₂.hom := rfl

/-- The first morphism of `AlgebraicGeometry.Space.closedImmersionSpanSituation`, read back as a
morphism of the site, is the first morphism of the span. -/
theorem closedImmersionSpanSituation_fppfOverI :
    fppfOverI (closedImmersionSpanSituation B S hS a₁ a₂ ha₁ ha₂) B hS R₁.left.2 R₃.left.2
      = a₁ := rfl

/-- The second morphism of `AlgebraicGeometry.Space.closedImmersionSpanSituation`, read back as a
morphism of the site, is the second morphism of the span. -/
theorem closedImmersionSpanSituation_fppfOverJ :
    fppfOverJ (closedImmersionSpanSituation B S hS a₁ a₂ ha₁ ha₂) B hS R₂.left.2 R₃.left.2
      = a₂ := rfl

end Situation

/-! ### The representable pushout square -/

/-- **The apex of the scheme pushout of [Stacks Project, Tag 0E25] is isomorphic to the apex of
any other pushout of the same span, compatibly with the two legs.** -/
theorem exists_iso_pushoutScheme (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
    {P : Scheme.{u}} (inl : s.X ⟶ P) (inr : s.Y ⟶ P) (h : IsPushout s.i s.j inl inr) :
    ∃ σ : pushoutScheme s ≅ P, pushoutInl s ≫ σ.hom = inl ∧ pushoutInr s ≫ σ.hom = inr := by
  have hc := (pushoutAlongClosedImmersionAndIntegral s).isPushout.isColimit
  exact ⟨hc.coconePointUniqueUpToIso h.isColimit,
    hc.comp_coconePointUniqueUpToIso_hom h.isColimit WalkingSpan.left,
    hc.comp_coconePointUniqueUpToIso_hom h.isColimit WalkingSpan.right⟩

/-- **The square of four closed immersions of the site into an object `V`, whose sheaves of
ideals are `I`, `J`, `I ⊔ J` and `I ⊓ J`, is a pushout square of algebraic spaces over `S`
after the Yoneda embedding.**

On schemes the square is a pushout by `AlgebraicGeometry.isPushout_of_ker_eq_inf`, which is
[Stacks Project, Tag 0C4J].  A span of two closed immersions is a standing situation of
[Stacks Project, Tag 0ECI], and the scheme pushout of that situation is a pushout against all
algebraic spaces over `S` by [Stacks Project, Tag 0EDP]; comparing the two pushouts of the span
gives an isomorphism of their apexes, which lifts to the site and transports Tag 0EDP onto this
square. -/
theorem isPushout_yoneda_of_ker_eq_inf {V R₁ R₂ R₃ R₄ : BigFppfOver B S hS}
    (j₁ : R₁ ⟶ V) (j₂ : R₂ ⟶ V) (j₃ : R₃ ⟶ V) (j₄ : R₄ ⟶ V)
    (hj₁ : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j₁))
    (hj₂ : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j₂))
    (hj₃ : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j₃))
    (hj₄ : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map j₄))
    (a₁ : R₃ ⟶ R₁) (a₂ : R₃ ⟶ R₂) (b₁ : R₁ ⟶ R₄) (b₂ : R₂ ⟶ R₄)
    (ha₁ : a₁ ≫ j₁ = j₃) (ha₂ : a₂ ≫ j₂ = j₃) (hb₁ : b₁ ≫ j₄ = j₁) (hb₂ : b₂ ≫ j₄ = j₂)
    (h₃ : ((BigFppfOver.toScheme B S hS).map j₃).ker =
      ((BigFppfOver.toScheme B S hS).map j₁).ker ⊔ ((BigFppfOver.toScheme B S hS).map j₂).ker)
    (h₄ : ((BigFppfOver.toScheme B S hS).map j₄).ker =
      ((BigFppfOver.toScheme B S hS).map j₁).ker ⊓ ((BigFppfOver.toScheme B S hS).map j₂).ker) :
    IsPushout
      (ObjectProperty.homMk (yoneda.map a₁) :
        yonedaSpace B S hS R₃ ⟶ yonedaSpace B S hS R₁)
      (ObjectProperty.homMk (yoneda.map a₂) :
        yonedaSpace B S hS R₃ ⟶ yonedaSpace B S hS R₂)
      (ObjectProperty.homMk (yoneda.map b₁) :
        yonedaSpace B S hS R₁ ⟶ yonedaSpace B S hS R₄)
      (ObjectProperty.homMk (yoneda.map b₂) :
        yonedaSpace B S hS R₂ ⟶ yonedaSpace B S hS R₄) := by
  -- the four morphisms of the span and the cocone are closed immersions of schemes
  have hA₁ := isClosedImmersion_toScheme_map_of_comp B S hS ha₁
  have hA₂ := isClosedImmersion_toScheme_map_of_comp B S hS ha₂
  have hB₁ := isClosedImmersion_toScheme_map_of_comp B S hS hb₁
  have hB₂ := isClosedImmersion_toScheme_map_of_comp B S hS hb₂
  -- the square of schemes is a pushout square, by Tag 0C4J
  have hsq : IsPushout ((BigFppfOver.toScheme B S hS).map a₁)
      ((BigFppfOver.toScheme B S hS).map a₂) ((BigFppfOver.toScheme B S hS).map b₁)
      ((BigFppfOver.toScheme B S hS).map b₂) :=
    isPushout_of_ker_eq_inf _ _ _ _ _ _ _ _
      (by rw [← Functor.map_comp, ha₁]) (by rw [← Functor.map_comp, ha₂])
      (by rw [← Functor.map_comp, hb₁]) (by rw [← Functor.map_comp, hb₂]) h₃ h₄
  -- compare its apex with the scheme pushout of the situation of Tag 0ECI
  obtain ⟨σ, hσl, hσr⟩ :=
    exists_iso_pushoutScheme (closedImmersionSpanSituation B S hS a₁ a₂ hA₁ hA₂)
      ((BigFppfOver.toScheme B S hS).map b₁) ((BigFppfOver.toScheme B S hS).map b₂) hsq
  have hP : B.Contains
      (pushoutScheme (closedImmersionSpanSituation B S hS a₁ a₂ hA₁ hA₂)) :=
    lt_of_le_of_lt (pushoutScheme_size_le _) (max_lt R₁.left.2 R₂.left.2)
  -- lift the comparison isomorphism to the site
  have hbase : σ.hom ≫ B.inclusion.map R₄.hom =
      pushoutToBase (closedImmersionSpanSituation B S hS a₁ a₂ hA₁ hA₂) := by
    refine (pushoutAlongClosedImmersionAndIntegral
      (closedImmersionSpanSituation B S hS a₁ a₂ hA₁ hA₂)).isPushout.hom_ext ?_ ?_
    · refine Eq.trans ?_
        (pushoutToBase_inl (closedImmersionSpanSituation B S hS a₁ a₂ hA₁ hA₂)).symm
      rw [← Category.assoc, hσl]
      exact toScheme_map_comp_inclusion_hom B S hS b₁
    · refine Eq.trans ?_
        (pushoutToBase_inr (closedImmersionSpanSituation B S hS a₁ a₂ hA₁ hA₂)).symm
      rw [← Category.assoc, hσr]
      exact toScheme_map_comp_inclusion_hom B S hS b₂
  -- transport Tag 0EDP along it
  refine (pushout_isPushout_algebraicSpaces (closedImmersionSpanSituation B S hS a₁ a₂ hA₁ hA₂)
      B hS R₁.left.2 R₂.left.2 R₃.left.2 hP).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (ObjectProperty.isoMk _ (yoneda.mapIso (siteIsoOfSchemeIso B S hS σ hbase))) ?_ ?_ ?_ ?_
  all_goals apply ObjectProperty.hom_ext
  · exact congrArg yoneda.map
      (closedImmersionSpanSituation_fppfOverI B S hS a₁ a₂ hA₁ hA₂)
  · exact congrArg yoneda.map
      (closedImmersionSpanSituation_fppfOverJ B S hS a₁ a₂ hA₁ hA₂)
  all_goals exact (yoneda.map_comp _ _).symm.trans (congrArg yoneda.map
    ((BigFppfOver.toScheme B S hS).map_injective
      (((BigFppfOver.toScheme B S hS).map_comp _ _).trans (by first | exact hσl | exact hσr))))

end AlgebraicGeometry.Space

end
