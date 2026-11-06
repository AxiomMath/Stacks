module

public import StacksFrontier.AlgebraicGeometry.Spaces.DimensionEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Normalization
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Normal
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSpaceConstruction

/-!
# The normalization of an algebraic space commutes with étale base change

Let `S` be a scheme, let `φ : F ⟶ G` be an étale morphism of algebraic spaces over `S`, let `D`
be normalization data for `G` and let `D'` be normalization data for `F`.  The square

```
F^ν ⟶ G^ν
 |      |
 v      v
 F  ⟶  G
    φ
```

formed by the two normalization morphisms, `φ` and the morphism of normalizations induced by
`φ`, is cartesian: `F^ν` is the base change `F ×_G G^ν`.  This is the isomorphism
`X^ν ≅ X ×_Y Y^ν` of part (4) of Tag 07U4, for an étale morphism of arbitrary algebraic spaces.

The ingredient that makes this available is the universal property of the normalization of an
algebraic space, part (4) of Tag 0BB4
(`AlgebraicGeometry.Space.NormalizationData.existsUnique_lift_hom`): a morphism to `G` from a
normal algebraic space carrying codimension-zero points to codimension-zero points factors
uniquely through `G^ν`.  Both comparison morphisms between `F^ν` and `F ×_G G^ν` come from it,
and the two composites are identities because each is a factorization of a morphism that has
exactly one.

The same property gives, for a *normal* algebraic space, that its normalization morphism is an
isomorphism — the identity factors through it, and the factorization is inverse to it by the
uniqueness half.  Over a normal base this is what makes a normalized blowing up an isomorphism
away from its centre, which the transfer of resolutions by normalized blowups from étale
neighbourhoods to the whole space uses.

## Main results

* `AlgebraicGeometry.Space.NormalizationData.isIso_hom_of_isNormal`: the normalization morphism
  of a normal algebraic space is an isomorphism.
* `AlgebraicGeometry.Space.hasLocallyFiniteIrreducibleComponents_of_isEtale`: condition (2) of
  Tag 0BB1 ascends along an étale morphism of algebraic spaces.
* `AlgebraicGeometry.Space.NormalizationData.isPullback_hom_of_isEtale`: the normalization
  square of an étale morphism of algebraic spaces is cartesian.
* `AlgebraicGeometry.Space.NormalizationData.exists_isPullback_hom_of_isEtale`: the same
  statement with the normalization data of the source produced rather than given.

## Implementation notes

**What this adds to `StacksFrontier.AlgebraicGeometry.Spaces.NormalizationEtaleChart`.**  That
module proves the comparison only for a *surjective* étale chart by an object of the site, and
records why: "for a non-surjective étale `U ⟶ F` the chart condition says nothing about `U`, and
for a non-representable `X` the comparison would have to be descended along an atlas of `X`".
Both restrictions are restrictions of the argument used there, which reads the comparison off
the chart condition of `AlgebraicGeometry.Space.NormalizationData`.  The argument used here
never looks at a chart: it is the scheme-level proof of
`AlgebraicGeometry.isPullback_normalizationSchemeMap_of_etale` read in algebraic spaces, with
the universal property of the normalization of a scheme replaced by that of the normalization of
an algebraic space.  So neither surjectivity nor representability is needed.

**The two hypotheses of the universal property, for the fibre product.**  `F ×_G G^ν` is normal,
because its projection to `G^ν` is a base change of `φ` hence étale, `G^ν` is normal by part (1)
of Tag 07U4, and an étale-local property of schemes passes from an algebraic space to any
algebraic space étale over it
(`AlgebraicGeometry.Space.hasEtaleLocalProperty_of_isEtale`).  And its projection to `F` carries
codimension-zero points to codimension-zero points: the projection to `G^ν` is étale hence flat,
so it preserves codimension zero by Tag 0GMC, the normalization morphism of `G` preserves it by
part (3) of Tag 0BB4, and étale invariance of the dimension of the local ring, Tag 0A4H,
transports the conclusion back across `φ`.  The last step is where étaleness of `φ` is used, and
it is the reason the smooth case of part (4) is not proved here: a smooth morphism does not
reflect codimension zero.

**No tag.**  Part (4) of Tag 07U4 asserts its conclusion for an étale *or smooth* morphism, and
asserts in addition that the hypotheses of part (3) hold, that is the existence and uniqueness of
the induced morphism of normalizations.  Only the étale half of the first assertion is proved
here — the morphism of normalizations is produced, but as the factorization supplied by Tag 0BB4
rather than as the `f^ν` of part (3) — so nothing here carries `@[stacks 07U4]`, for the same
reason that nothing in `StacksFrontier.AlgebraicGeometry.Spaces.NormalizationEtaleChart` does.

## References

* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
* [Stacks Project, Tag 07TD](https://stacks.math.columbia.edu/tag/07TD)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
* [Stacks Project, Tag 0BB4](https://stacks.math.columbia.edu/tag/0BB4)
* [Stacks Project, Tag 0A4H](https://stacks.math.columbia.edu/tag/0A4H)
* [Stacks Project, Tag 0GMC](https://stacks.math.columbia.edu/tag/0GMC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- **Condition (2) of Tag 0BB1 ascends along an étale morphism.**  An étale scheme chart of the
source of an étale morphism of algebraic spaces becomes, after composition with that morphism, an
étale scheme chart of the target, and the condition is a condition on the étale scheme charts. -/
theorem hasLocallyFiniteIrreducibleComponents_of_isEtale (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : HasLocallyFiniteIrreducibleComponents B S hS G) {φ : F ⟶ G}
    (hφ : IsEtale B S hS φ) : HasLocallyFiniteIrreducibleComponents B S hS F := fun U f hf ↦
  hG U (f ≫ φ) ((isEtale_iff_presheaf_of_yoneda B S hS _).mpr
    (hφ U f ((isEtale_iff_presheaf_of_yoneda B S hS f).mp hf)))

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullback_presheaf_normalizationEtaleBaseChange
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

namespace NormalizationData

/-- **The normalization morphism of a normal algebraic space is an isomorphism.**

The identity of the space is a morphism from a normal algebraic space preserving codimension
zero, so the universal property of part (4) of Tag 0BB4 factors it through the normalization
morphism; that factorization is a right inverse of the normalization morphism by construction,
and a left inverse because the normalization morphism factors through itself in only one way. -/
theorem isIso_hom_of_isNormal (D : NormalizationData B S hS F)
    (hF : IsAlgebraicSpace B S hS F) (hFn : Space.IsNormal B S hS F) : IsIso D.hom := by
  obtain ⟨g, hg, -⟩ := D.existsUnique_lift_hom hF hF hFn (𝟙 F) (by
    intro z hz
    rwa [congrFun (pointsMap_id B S hS F) z])
  refine ⟨g, ?_, hg⟩
  refine ExistsUnique.unique (D.existsUnique_lift_hom hF D.isAlgebraicSpace
    (D.hasEtaleLocalProperty_isNormal hF) D.hom
    (fun z hz => (D.bijOn_codimensionZeroPoints_hom hF).1 hz)) ?_ (Category.id_comp _)
  rw [Category.assoc, hg, Category.comp_id]

/-- **Part (4) of Tag 07U4 for an étale morphism of algebraic spaces: the normalization square
is cartesian.**  Let `φ : F ⟶ G` be an étale morphism of algebraic spaces over `S`, let `D` be
normalization data for `G` and `D'` normalization data for `F`.  Then there is a morphism
`F^ν ⟶ G^ν` over `φ` exhibiting `F^ν` as the fibre product `F ×_G G^ν`.

The morphism `m : F^ν ⟶ G^ν` is the factorization of `F^ν ⟶ F ⟶ G` through `G^ν` supplied by
the universal property of part (4) of Tag 0BB4, and the comparison `F^ν ⟶ F ×_G G^ν` is the
morphism into the fibre product it determines together with the normalization morphism of `F`.
Its inverse is the factorization of the projection `F ×_G G^ν ⟶ F` through `F^ν`, which the same
universal property supplies because the fibre product is normal and its projection to `F`
preserves codimension zero.  Both composites are identities, each being a factorization of a
morphism that factors in only one way. -/
theorem isPullback_hom_of_isEtale (D : NormalizationData B S hS G)
    (D' : NormalizationData B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hF : IsAlgebraicSpace B S hS F) (φ : F ⟶ G) (hφ : IsEtale B S hS φ) :
    ∃ m : D'.space ⟶ D.space, IsPullback m D'.hom D.hom φ := by
  have hN : IsAlgebraicSpace B S hS (pullback D.hom φ) :=
    isAlgebraicSpace_pullback B S hS D.hom φ D.isAlgebraicSpace hF hG
  have hp : IsEtale B S hS (pullback.fst D.hom φ) :=
    isEtale_pullback_fst B S hS D.isAlgebraicSpace hG hF D.hom φ hφ
  have hNn : Space.IsNormal B S hS (pullback D.hom φ) :=
    hasEtaleLocalProperty_of_isEtale B S hS hN D.isAlgebraicSpace hp (D.isNormal hG)
  -- the first projection, followed by the normalization morphism of `G`, preserves codimension
  -- zero: it is flat, and the normalization morphism preserves codimension zero
  have hgenP : ∀ z : points B S hS (pullback D.hom φ), localRingDimension B S hS z = 0 →
      localRingDimension B S hS
        (pointsMap B S hS _ (pullback.fst D.hom φ ≫ D.hom) z) = 0 := by
    intro z hz
    rw [pointsMap_comp_apply]
    exact (D.bijOn_codimensionZeroPoints_hom hG).1
      (localRingDimension_eq_zero_of_isFlat B S hS hN D.isAlgebraicSpace _
        (isFlat_of_isEtale B S hS hp) z hz)
  -- hence so does the second projection, by the cartesian square and étale invariance of the
  -- dimension of the local ring
  have hgenQ : ∀ z : points B S hS (pullback D.hom φ), localRingDimension B S hS z = 0 →
      localRingDimension B S hS (pointsMap B S hS _ (pullback.snd D.hom φ) z) = 0 := by
    intro z hz
    have h := hgenP z hz
    rw [pullback.condition, pointsMap_comp_apply,
      localRingDimension_pointsMap_of_etale B S hS hF hG φ hφ] at h
    exact h
  -- the morphism of normalizations induced by `φ`
  have hgenM : ∀ z : points B S hS D'.space, localRingDimension B S hS z = 0 →
      localRingDimension B S hS (pointsMap B S hS _ (D'.hom ≫ φ) z) = 0 := by
    intro z hz
    rw [pointsMap_comp_apply, localRingDimension_pointsMap_of_etale B S hS hF hG φ hφ]
    exact (D'.bijOn_codimensionZeroPoints_hom hF).1 hz
  obtain ⟨m, hm, -⟩ := D.existsUnique_lift_hom hG D'.isAlgebraicSpace
    (D'.hasEtaleLocalProperty_isNormal hF) (D'.hom ≫ φ) hgenM
  refine ⟨m, ?_⟩
  set lift : D'.space ⟶ pullback D.hom φ := pullback.lift m D'.hom hm with hliftdef
  obtain ⟨u, hu, -⟩ := D'.existsUnique_lift_hom hF hN hNn (pullback.snd D.hom φ) hgenQ
  have hliftu : lift ≫ u = 𝟙 D'.space := by
    refine ExistsUnique.unique (D'.existsUnique_lift_hom hF D'.isAlgebraicSpace
      (D'.hasEtaleLocalProperty_isNormal hF) D'.hom
      (fun z hz => (D'.bijOn_codimensionZeroPoints_hom hF).1 hz)) ?_ (Category.id_comp _)
    rw [Category.assoc, hu, hliftdef, pullback.lift_snd]
  have hfst : u ≫ m = pullback.fst D.hom φ := by
    refine ExistsUnique.unique (D.existsUnique_lift_hom hG hN hNn
      (pullback.fst D.hom φ ≫ D.hom) hgenP) ?_ rfl
    rw [Category.assoc, hm, ← Category.assoc, hu, pullback.condition]
  have hulift : u ≫ lift = 𝟙 (pullback D.hom φ) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hliftdef, pullback.lift_fst, hfst, Category.id_comp]
    · rw [Category.assoc, hliftdef, pullback.lift_snd, hu, Category.id_comp]
  have : IsIso lift := ⟨u, hliftu, hulift⟩
  exact IsPullback.of_iso_pullback ⟨hm⟩ (asIso lift)
    (by rw [asIso_hom, hliftdef, pullback.lift_fst])
    (by rw [asIso_hom, hliftdef, pullback.lift_snd])

/-- **Part (4) of Tag 07U4 for an étale morphism, with the normalization of the source
produced.**  Only normalization data for the target is given: the source satisfies condition (2)
of Tag 0BB1 because the target does and the morphism is étale, so it has normalization data by
Tag 07U4, and `AlgebraicGeometry.Space.NormalizationData.isPullback_hom_of_isEtale` applies to
it. -/
theorem exists_isPullback_hom_of_isEtale (D : NormalizationData B S hS G)
    (hG : IsAlgebraicSpace B S hS G) (hF : IsAlgebraicSpace B S hS F) (φ : F ⟶ G)
    (hφ : IsEtale B S hS φ) (hGfin : HasLocallyFiniteIrreducibleComponents B S hS G) :
    ∃ (D' : NormalizationData B S hS F) (m : D'.space ⟶ D.space),
      IsPullback m D'.hom D.hom φ := by
  obtain ⟨D'⟩ := nonempty_normalizationData B S hS hF
    (hasLocallyFiniteIrreducibleComponents_of_isEtale B S hS hGfin hφ)
  obtain ⟨m, hm⟩ := D.isPullback_hom_of_isEtale D' hG hF φ hφ
  exact ⟨D', m, hm⟩

end NormalizationData

end AlgebraicGeometry.Space

end
