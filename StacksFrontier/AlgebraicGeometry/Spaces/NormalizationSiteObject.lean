module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.GenericPointsSize
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationChartObject

/-!
# The normalization of an object of the big fppf site, as an object of the site

`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationChartObject` reads the *relative*
normalization of a quasi-compact quasi-separated morphism of the big fppf site of `S` as an
object of the site. This file does the same for the *absolute* normalization of Tag 035N: for
an object `U` of the site whose quasi-compact opens have finitely many irreducible components,
the normalization scheme `U^ν` is an object of the site, the normalization morphism is a
morphism of the site, and the assignment is functorial in the flat morphisms of the site and
cartesian along the étale ones.

Containment in the site is free, by
`AlgebraicGeometry.Scheme.size_normalizationScheme_le`; this is what lets the construction of
the normalization of an algebraic space carry no size hypothesis, unlike
`AlgebraicGeometry.Space.NormalizationData.ofRepresentable`.

## Main definitions

* `AlgebraicGeometry.Space.normSpace` is the normalization of an object of the site, as an
  object of the site, and `AlgebraicGeometry.Space.normSpaceProj` its normalization morphism.
* `AlgebraicGeometry.Space.normSpaceMap` is the morphism of normalizations induced by a
  morphism of the site which carries generic points to generic points.

## Main results

* `AlgebraicGeometry.Space.contains_normalizationScheme`: the site contains the normalization
  of any of its objects, with no size hypothesis.
* `AlgebraicGeometry.Space.normSpace_hom_ext`: rigidity. A morphism of normalizations over a
  given morphism of the bases which commutes with the normalization morphisms is unique. This
  is the uniqueness half of Tag 035Q, part (4), read in the site.
* `AlgebraicGeometry.Space.normSpaceMap_comp`: the assignment is functorial; this is the
  cocycle condition of the descent datum the normalization of an algebraic space is glued
  from.
* `AlgebraicGeometry.Space.isPullback_normSpaceMap_of_etale` and
  `AlgebraicGeometry.Space.isPullback_yoneda_map_normSpaceMap_of_etale`: along an étale
  morphism of the bases the square of normalizations is cartesian — Tag 07TD read in the site
  and in presheaves.
* `AlgebraicGeometry.Space.etale_toScheme_map_normSpaceMap` and
  `AlgebraicGeometry.Space.surjective_toScheme_map_normSpaceMap`: the induced morphism of
  normalizations is étale, resp. surjective, when the morphism of the bases is.

## Implementation notes

The finiteness condition on irreducible components is a `Prop`, so two proofs of it are
definitionally equal and the normalization morphisms they name are literally the same
morphism. No transport along a change of proof is ever needed, and in particular the proof
produced by `AlgebraicGeometry.finite_irreducibleComponents_of_smooth` along a chart may be
used interchangeably with any other.

Functoriality is stated for a morphism of the bases carrying generic points to generic points,
which is exactly the hypothesis of Tag 035Q, part (4), and so exactly the generality in which
rigidity holds. This is *weaker* than flatness, and the weakening is needed: the diagonal of
the relation `R = U ×_F U` of an étale chart is not flat over `R`, but it does carry generic
points to generic points, because `pr₁` is étale and étale morphisms reflect generic points.
For a flat morphism of the bases the induced morphism agrees with
`AlgebraicGeometry.normalizationSchemeMap`
(`AlgebraicGeometry.Space.normSpaceSchemeMap_eq_normalizationSchemeMap`), which is how
cartesianness along an étale morphism is imported from Tag 07TD.

**No tag.** Tag 035N is carried by `AlgebraicGeometry.Scheme.normalization`, Tag 035Q part (4)
by `AlgebraicGeometry.Scheme.existsUnique_lift_normalization` and Tag 07TD by
`AlgebraicGeometry.isPullback_normalizationSchemeMap_of_etale`; what is done here is to read
them in the site, which is a change of shape and not a new assertion.

## References

* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 07TD](https://stacks.math.columbia.edu/tag/07TD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The big fppf site contains the normalization of any of its objects.** The normalization
of a scheme has size at most that of the scheme
(`AlgebraicGeometry.Scheme.size_normalizationScheme_le`) and containment is precisely a bound
on `AlgebraicGeometry.Scheme.size`, so no size hypothesis is needed. -/
theorem contains_normalizationScheme (U : BigFppfOver B S hS)
    (hU : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
        (irreducibleComponents V).Finite) :
    B.Contains (Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj U) hU) :=
  (Scheme.size_normalizationScheme_le _ hU).trans_lt U.left.property

variable {U₁ U₂ U₃ : BigFppfOver B S hS}

/-- **The normalization of an object of the big fppf site, as an object of the site.** -/
def normSpace (U : BigFppfOver B S hS)
    (hU : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
        (irreducibleComponents V).Finite) :
    BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_normalizationScheme B S hS U hU)
    (Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U) hU ≫ B.inclusion.map U.hom)

/-- The underlying scheme of `normSpace B S hS U hU` is the normalization scheme of the
underlying scheme of `U`. -/
lemma toScheme_obj_normSpace (U : BigFppfOver B S hS)
    (hU : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
        (irreducibleComponents V).Finite) :
    (BigFppfOver.toScheme B S hS).obj (normSpace B S hS U hU) =
      Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj U) hU :=
  rfl

/-- The structure morphism of `normSpace B S hS U hU` is the normalization morphism followed by
the structure morphism of `U`. -/
lemma inclusion_hom_normSpace (U : BigFppfOver B S hS)
    (hU : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
        (irreducibleComponents V).Finite) :
    B.inclusion.map (normSpace B S hS U hU).hom =
      Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U) hU ≫ B.inclusion.map U.hom :=
  rfl

/-- **The normalization morphism, as a morphism of the site.** -/
def normSpaceProj (U : BigFppfOver B S hS)
    (hU : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
        (irreducibleComponents V).Finite) :
    normSpace B S hS U hU ⟶ U :=
  siteHom B S hS (Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U) hU) rfl

/-- The underlying morphism of schemes of `normSpaceProj B S hS U hU` is the normalization
morphism of the underlying scheme of `U`. -/
lemma toScheme_map_normSpaceProj (U : BigFppfOver B S hS)
    (hU : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
        (irreducibleComponents V).Finite) :
    (BigFppfOver.toScheme B S hS).map (normSpaceProj B S hS U hU) =
      Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U) hU :=
  rfl

variable (hU₁ : ∀ V : ((BigFppfOver.toScheme B S hS).obj U₁).Opens,
    IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U₁)) →
      (irreducibleComponents V).Finite)
  (hU₂ : ∀ V : ((BigFppfOver.toScheme B S hS).obj U₂).Opens,
    IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U₂)) →
      (irreducibleComponents V).Finite)
  (hU₃ : ∀ V : ((BigFppfOver.toScheme B S hS).obj U₃).Opens,
    IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U₃)) →
      (irreducibleComponents V).Finite)

/-- **The normalization is functorial in the morphisms of the site which carry generic points
to generic points**: Tag 035Q, part (4), applied to the composite of the normalization morphism
of the source with such a morphism. The source of that composite is normal and it carries
generic points to generic points, so it lifts through the normalization of the target, and in
exactly one way. -/
theorem existsUnique_normSpaceSchemeMap (k : U₂ ⟶ U₁)
    (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₂),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U₁)) :
    ∃! g : Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj U₂) hU₂ ⟶
        Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj U₁) hU₁,
      g ≫ Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U₁) hU₁ =
        Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U₂) hU₂ ≫
          (BigFppfOver.toScheme B S hS).map k := by
  have _ : _root_.AlgebraicGeometry.IsNormal
      (Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj U₂) hU₂) :=
    Scheme.isNormal_normalizationScheme _ hU₂
  exact Scheme.existsUnique_lift_normalization hU₁ _ fun η =>
    hk ⟨_, Scheme.normalization_mem_genericPoints _ hU₂ η.2⟩

/-- **Rigidity of the normalization.** A morphism of normalizations lying over a morphism `k`
of the bases which carries generic points to generic points, and commuting with the two
normalization morphisms, is unique. This is the uniqueness half of Tag 035Q, part (4), read in
the site. -/
lemma normSpace_hom_ext (k : U₂ ⟶ U₁)
    (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₂),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U₁))
    {a b : normSpace B S hS U₂ hU₂ ⟶ normSpace B S hS U₁ hU₁}
    (ha : a ≫ normSpaceProj B S hS U₁ hU₁ = normSpaceProj B S hS U₂ hU₂ ≫ k)
    (hb : b ≫ normSpaceProj B S hS U₁ hU₁ = normSpaceProj B S hS U₂ hU₂ ≫ k) :
    a = b := by
  have key : ∀ c : normSpace B S hS U₂ hU₂ ⟶ normSpace B S hS U₁ hU₁,
      c ≫ normSpaceProj B S hS U₁ hU₁ = normSpaceProj B S hS U₂ hU₂ ≫ k →
      (BigFppfOver.toScheme B S hS).map c ≫
        Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U₁) hU₁ =
      Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U₂) hU₂ ≫
        (BigFppfOver.toScheme B S hS).map k := fun c hc => by
    have h := congrArg (BigFppfOver.toScheme B S hS).map hc
    rwa [Functor.map_comp, Functor.map_comp, toScheme_map_normSpaceProj,
      toScheme_map_normSpaceProj] at h
  exact (BigFppfOver.toScheme B S hS).map_injective
    ((existsUnique_normSpaceSchemeMap B S hS hU₁ hU₂ k hk).unique (key a ha) (key b hb))

/-- The morphism of normalization *schemes* induced by a morphism of the site which carries
generic points to generic points. -/
def normSpaceSchemeMap (k : U₂ ⟶ U₁)
    (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₂),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U₁)) :
    Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj U₂) hU₂ ⟶
      Scheme.normalizationScheme ((BigFppfOver.toScheme B S hS).obj U₁) hU₁ :=
  (existsUnique_normSpaceSchemeMap B S hS hU₁ hU₂ k hk).choose

/-- The morphism `normSpaceSchemeMap` lies over `k`: composed with the normalization morphism of
the target it equals the normalization morphism of the source followed by `k`. -/
@[reassoc]
lemma normSpaceSchemeMap_normalization (k : U₂ ⟶ U₁)
    (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₂),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U₁)) :
    normSpaceSchemeMap B S hS hU₁ hU₂ k hk ≫
        Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U₁) hU₁ =
      Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U₂) hU₂ ≫
        (BigFppfOver.toScheme B S hS).map k :=
  (existsUnique_normSpaceSchemeMap B S hS hU₁ hU₂ k hk).choose_spec.1

/-- **The morphism of normalizations induced by a morphism of the site which carries generic
points to generic points.** -/
def normSpaceMap (k : U₂ ⟶ U₁)
    (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₂),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U₁)) :
    normSpace B S hS U₂ hU₂ ⟶ normSpace B S hS U₁ hU₁ :=
  siteHom B S hS (normSpaceSchemeMap B S hS hU₁ hU₂ k hk) (by
    change normSpaceSchemeMap B S hS hU₁ hU₂ k hk ≫
        (Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U₁) hU₁ ≫
          B.inclusion.map U₁.hom) =
      Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U₂) hU₂ ≫
        B.inclusion.map U₂.hom
    rw [← Category.assoc, normSpaceSchemeMap_normalization, Category.assoc,
      toScheme_map_comp_inclusion_hom])

/-- The underlying morphism of schemes of `normSpaceMap B S hS hU₁ hU₂ k hk` is
`normSpaceSchemeMap B S hS hU₁ hU₂ k hk`. -/
lemma toScheme_map_normSpaceMap (k : U₂ ⟶ U₁)
    (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₂),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U₁)) :
    (BigFppfOver.toScheme B S hS).map (normSpaceMap B S hS hU₁ hU₂ k hk) =
      normSpaceSchemeMap B S hS hU₁ hU₂ k hk :=
  rfl

/-- The morphism `normSpaceMap` lies over `k`: composed with the normalization morphism of the
target it equals the normalization morphism of the source followed by `k`. -/
@[reassoc]
lemma normSpaceMap_comp_normSpaceProj (k : U₂ ⟶ U₁)
    (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₂),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U₁)) :
    normSpaceMap B S hS hU₁ hU₂ k hk ≫ normSpaceProj B S hS U₁ hU₁ =
      normSpaceProj B S hS U₂ hU₂ ≫ k := by
  refine (BigFppfOver.toScheme B S hS).map_injective ?_
  rw [Functor.map_comp, Functor.map_comp, toScheme_map_normSpaceMap,
    toScheme_map_normSpaceProj, toScheme_map_normSpaceProj]
  exact normSpaceSchemeMap_normalization B S hS hU₁ hU₂ k hk

/-- The induced morphism of normalizations depends on the morphism of the bases alone. -/
lemma normSpaceMap_congr (k k' : U₂ ⟶ U₁)
    (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₂),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U₁))
    (hk' : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₂),
      (BigFppfOver.toScheme B S hS).map k' η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U₁))
    (h : k = k') :
    normSpaceMap B S hS hU₁ hU₂ k hk = normSpaceMap B S hS hU₁ hU₂ k' hk' := by
  subst h; rfl

/-- **The normalization of the identity is the identity.** -/
lemma normSpaceMap_id (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₁),
    (BigFppfOver.toScheme B S hS).map (𝟙 U₁) η.1 ∈
      genericPoints ((BigFppfOver.toScheme B S hS).obj U₁)) :
    normSpaceMap B S hS hU₁ hU₁ (𝟙 U₁) hk = 𝟙 (normSpace B S hS U₁ hU₁) :=
  normSpace_hom_ext B S hS hU₁ hU₁ (𝟙 U₁) hk
    (normSpaceMap_comp_normSpaceProj B S hS hU₁ hU₁ (𝟙 U₁) hk)
    (by rw [Category.id_comp, Category.comp_id])

/-- **The normalization of a composite is the composite of the normalizations.** This is the
cocycle condition of the descent datum formed by the normalizations of the charts; it is an
instance of rigidity, as is every other identity between morphisms of normalizations. -/
lemma normSpaceMap_comp (k : U₂ ⟶ U₁) (l : U₃ ⟶ U₂)
    (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₂),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U₁))
    (hl : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₃),
      (BigFppfOver.toScheme B S hS).map l η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U₂))
    (hlk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₃),
      (BigFppfOver.toScheme B S hS).map (l ≫ k) η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U₁)) :
    normSpaceMap B S hS hU₁ hU₃ (l ≫ k) hlk =
      normSpaceMap B S hS hU₂ hU₃ l hl ≫ normSpaceMap B S hS hU₁ hU₂ k hk := by
  refine normSpace_hom_ext B S hS hU₁ hU₃ (l ≫ k) hlk
    (normSpaceMap_comp_normSpaceProj B S hS hU₁ hU₃ (l ≫ k) hlk) ?_
  rw [Category.assoc, normSpaceMap_comp_normSpaceProj, ← Category.assoc,
    normSpaceMap_comp_normSpaceProj, Category.assoc]

/-! ### The flat and the étale case -/

/-- A flat morphism of the site carries generic points to generic points, so it induces a
morphism of normalizations with no further hypothesis. -/
lemma mem_genericPoints_toScheme_map_of_flat (k : U₂ ⟶ U₁)
    [Flat ((BigFppfOver.toScheme B S hS).map k)] :
    ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₂),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U₁) := fun η =>
  Scheme.Hom.mem_genericPoints_of_flat _ η.2

/-- For a flat morphism of the bases the induced morphism of normalizations is the one of
`AlgebraicGeometry.normalizationSchemeMap`, by rigidity. -/
lemma normSpaceSchemeMap_eq_normalizationSchemeMap (k : U₂ ⟶ U₁)
    [Flat ((BigFppfOver.toScheme B S hS).map k)]
    (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₂),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U₁)) :
    normSpaceSchemeMap B S hS hU₁ hU₂ k hk =
      normalizationSchemeMap ((BigFppfOver.toScheme B S hS).map k) hU₂ hU₁ :=
  (existsUnique_normSpaceSchemeMap B S hS hU₁ hU₂ k hk).unique
    (normSpaceSchemeMap_normalization B S hS hU₁ hU₂ k hk)
    (normalizationSchemeMap_normalization _ hU₂ hU₁)

/-- **Tag 07TD in the site, on underlying schemes.** Along an étale morphism of the bases the
square formed by the two normalization morphisms and the induced morphism of normalizations is
cartesian. -/
lemma isPullback_toScheme_map_normSpaceMap_of_etale (k : U₂ ⟶ U₁)
    [Etale ((BigFppfOver.toScheme B S hS).map k)]
    (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₂),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U₁)) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (normSpaceMap B S hS hU₁ hU₂ k hk))
      ((BigFppfOver.toScheme B S hS).map (normSpaceProj B S hS U₂ hU₂))
      ((BigFppfOver.toScheme B S hS).map (normSpaceProj B S hS U₁ hU₁))
      ((BigFppfOver.toScheme B S hS).map k) := by
  rw [toScheme_map_normSpaceMap, normSpaceSchemeMap_eq_normalizationSchemeMap,
    toScheme_map_normSpaceProj, toScheme_map_normSpaceProj]
  exact isPullback_normalizationSchemeMap_of_etale ((BigFppfOver.toScheme B S hS).map k) hU₁

/-- **Tag 07TD in the site.** The forgetful functor to schemes preserves fibre products and
reflects isomorphisms, so it reflects cartesian squares. -/
lemma isPullback_normSpaceMap_of_etale (k : U₂ ⟶ U₁)
    [Etale ((BigFppfOver.toScheme B S hS).map k)]
    (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₂),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U₁)) :
    IsPullback (normSpaceMap B S hS hU₁ hU₂ k hk) (normSpaceProj B S hS U₂ hU₂)
      (normSpaceProj B S hS U₁ hU₁) k := by
  have _ : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have _ : ReflectsLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS)
    (isPullback_toScheme_map_normSpaceMap_of_etale B S hS hU₁ hU₂ k hk)

/-- **Tag 07TD in presheaves.** -/
lemma isPullback_yoneda_map_normSpaceMap_of_etale (k : U₂ ⟶ U₁)
    [Etale ((BigFppfOver.toScheme B S hS).map k)]
    (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₂),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U₁)) :
    IsPullback (yoneda.map (normSpaceMap B S hS hU₁ hU₂ k hk))
      (yoneda.map (normSpaceProj B S hS U₂ hU₂))
      (yoneda.map (normSpaceProj B S hS U₁ hU₁)) (yoneda.map k) :=
  (isPullback_normSpaceMap_of_etale B S hS hU₁ hU₂ k hk).map yoneda

/-- The induced morphism of normalizations is étale when the morphism of the bases is, being a
base change of it. -/
lemma etale_toScheme_map_normSpaceMap (k : U₂ ⟶ U₁)
    [Etale ((BigFppfOver.toScheme B S hS).map k)]
    (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₂),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U₁)) :
    Etale ((BigFppfOver.toScheme B S hS).map (normSpaceMap B S hS hU₁ hU₂ k hk)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Etale.{u})
    (isPullback_toScheme_map_normSpaceMap_of_etale B S hS hU₁ hU₂ k hk).flip inferInstance

/-- The induced morphism of normalizations is surjective when the morphism of the bases is
étale and surjective, being a base change of it. -/
lemma surjective_toScheme_map_normSpaceMap (k : U₂ ⟶ U₁)
    [Etale ((BigFppfOver.toScheme B S hS).map k)]
    [Surjective ((BigFppfOver.toScheme B S hS).map k)]
    (hk : ∀ η : genericPoints ((BigFppfOver.toScheme B S hS).obj U₂),
      (BigFppfOver.toScheme B S hS).map k η.1 ∈
        genericPoints ((BigFppfOver.toScheme B S hS).obj U₁)) :
    Surjective ((BigFppfOver.toScheme B S hS).map (normSpaceMap B S hS hU₁ hU₂ k hk)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Surjective.{u})
    (isPullback_toScheme_map_normSpaceMap_of_etale B S hS hU₁ hU₂ k hk).flip inferInstance

end AlgebraicGeometry.Space

end
