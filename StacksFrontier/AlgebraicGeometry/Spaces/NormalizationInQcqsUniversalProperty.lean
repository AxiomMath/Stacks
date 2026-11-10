module

public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInChartRelativeSpecIntegral
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparationCancellation

/-!
# The universal property of the normalization of an algebraic space in another

Let `f : Y ⟶ X` be a quasi-compact and quasi-separated morphism of algebraic spaces over `S`,
and let `f = ν ∘ f'` be its factorization through the normalization `ν : X' ⟶ X` of `X` in `Y`
(Stacks 0822: `AlgebraicGeometry.Space.normalizationInQcqsHom` and
`AlgebraicGeometry.Space.toNormalizationInQcqs`).  Stacks 0823 says that this factorization is
characterized by the following two properties:

1. the morphism `ν` is integral, and
2. for any factorization `f = π ∘ g` with `π : Z ⟶ X` integral there is a unique `h : X' ⟶ Z`
   with `h ∘ f' = g` and `π ∘ h = ν`;

and that, moreover, in (2) the morphism `h : X' ⟶ Z` is the normalization of `Z` in `Y`.

This file proves all of it for the normalization of Stacks 0822.

## Main results

* `AlgebraicGeometry.Space.isIntegralHom_normalizationInQcqsHom`: property (1).
* `AlgebraicGeometry.Space.pushforwardAlgebraMap_toNormalizationInQcqsOver`: the map
  `ν_* 𝒪_{X'} ⟶ f_* 𝒪_Y` induced by `f'` is `ν_* 𝒪_{X'} ≅ 𝒪' ⊂ f_* 𝒪_Y`.
* `AlgebraicGeometry.Space.isRelativeNormalization_normalizationInQcqs`: **properties (1) and
  (2)**, as the predicate `AlgebraicGeometry.Space.IsRelativeNormalization` of
  `StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeNormalization`.
* `AlgebraicGeometry.Space.isRelativeNormalization_iff_exists_iso_normalizationInQcqs` and
  `AlgebraicGeometry.Space.existsUnique_iso_normalizationInQcqs_of_isRelativeNormalization`:
  **the characterization.**  A factorization `f = ν'' ∘ f''` through an algebraic space has
  properties (1) and (2) exactly when it is isomorphic to `f = ν ∘ f'`, and then the
  isomorphism is unique.
* `AlgebraicGeometry.Space.isRelativeNormalization_comparison_normalizationInQcqs`: **the final
  clause.**  The morphism `h : X' ⟶ Z` of (2) exhibits `X'` as the normalization of `Z` in `Y`:
  the factorization `g = h ∘ f'` has properties (1) and (2) for `g`, and it is uniquely
  isomorphic to the normalization of `Z` in `Y` of Stacks 0822, `g` being quasi-compact and
  quasi-separated.

## Implementation notes

Property (2) is the criterion
`AlgebraicGeometry.Space.isRelativeNormalization_of_pushforwardAlgebraMap_eq` of
`StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalizationAlgebraCriterion`, which is the
source's
proof: the algebra `π_* 𝒪_Z` of a test object is integral, so its map to `f_* 𝒪_Y`
lands in `𝒪'` (Stacks 0820), and the mapping property of a space affine over `X`
(`AlgebraicGeometry.Space.overHomEquivPushforwardAlgebraHom`, the form of Stacks 081V the source
cites) turns that into `h`.  Its one input about `f'` is that `f'` induces the inclusion
`𝒪' ⊂ f_* 𝒪_Y`, which is how Stacks 0822 defines `f'`; the construction of
`StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqs` states it at every point of `Y`, and
`AlgebraicGeometry.Space.pushforwardAlgebraMap_toNormalizationInQcqsOver` reads it globally.

The characterization and the final clause are the source's argument with the characterization:
the two properties make the factorization initial among factorizations of `f` through integral
morphisms (`AlgebraicGeometry.Space.IsRelativeNormalization.existsUnique_iso`), and the
comparison morphism `h` is integral by Stacks 081Z
(`AlgebraicGeometry.Space.IsRelativeNormalization.comparison`).

## References

* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 0820](https://stacks.math.columbia.edu/tag/0820)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 081Z](https://stacks.math.columbia.edu/tag/081Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)

/-! ### The two properties -/

/-- **Stacks 0823, property (1): the normalization `ν : X' ⟶ X` is integral.**  It is the
relative spectrum of the integral closure `𝒪'`, an integral `𝒪_X`-algebra. -/
@[stacks 0823 "property (1): ν is integral"]
theorem isIntegralHom_normalizationInQcqsHom :
    IsIntegralHom B S hS (normalizationInQcqsHom B S hS f hfqc hfqs).hom :=
  isIntegralHom_normalizationInChartQuotientHom B S hS f hfqc hfqs _ _
    (isPullback_chosenAtlasPair B S hS X) (surjective_chosenAtlasPairTarget B S hS X)

/-- **The map `ν_* 𝒪_{X'} ⟶ f_* 𝒪_Y` induced by `f'` is `ν_* 𝒪_{X'} ≅ 𝒪' ⊂ f_* 𝒪_Y`.**  The
morphism over `X` inducing that map, which exists by the mapping property of `X'`, has the
pointwise property characterizing `f'`
(`AlgebraicGeometry.Space.eq_toNormalizationInQcqsOver`), so it is `f'`. -/
theorem pushforwardAlgebraMap_toNormalizationInQcqsOver :
    pushforwardAlgebraMap B S hS (toNormalizationInQcqsOver f hfqc hfqs) =
      normalizationInQcqsAlgebraMap B S hS f hfqc hfqs := by
  obtain ⟨g, hg⟩ := exists_pushforwardAlgebraMap_eq_of_affineOver B S hS (Over.mk f)
    (normalizationInQcqsAffineOver B S hS f hfqc hfqs)
    (normalizationInQcqsAlgebraMap B S hS f hfqc hfqs)
  have hgf : g = toNormalizationInQcqsOver f hfqc hfqs :=
    eq_toNormalizationInQcqsOver f hfqc hfqs g fun T y => by
      rw [pushforwardAlgebraMap_comp, hg]
  rw [← hgf, hg]

/-- **Stacks 0823, properties (1) and (2) for the normalization of Stacks 0822.**  Let
`f : Y ⟶ X` be a quasi-compact and quasi-separated morphism of algebraic spaces over `S`, and
`f = ν ∘ f'` its factorization through the normalization `ν : X' ⟶ X` of `X` in `Y`.  Then `ν` is
integral, and for every factorization `f = π ∘ g` with `π : Z ⟶ X` an integral morphism of
algebraic spaces over `S` there is a unique `h : X' ⟶ Z` with `h ∘ f' = g` and `π ∘ h = ν`. -/
@[stacks 0823 "properties (1) and (2) hold for the normalization f = ν ∘ f' of Stacks 0822"]
theorem isRelativeNormalization_normalizationInQcqs :
    IsRelativeNormalization B S hS f.hom (normalizationInQcqsHom B S hS f hfqc hfqs).hom
      (toNormalizationInQcqs f hfqc hfqs).hom :=
  isRelativeNormalization_of_pushforwardAlgebraMap_eq B S hS f
    (normalizationInQcqsAffineOver B S hS f hfqc hfqs)
    (isIntegralHom_normalizationInQcqsHom f hfqc hfqs)
    (toNormalizationInQcqsOver f hfqc hfqs)
    (normalizationInQcqsPushforwardIso B S hS f hfqc hfqs).symm (by
      rw [pushforwardAlgebraMap_toNormalizationInQcqsOver]
      exact Iso.inv_hom_id_assoc _ _)

/-! ### The characterization -/

/-- Being a relative normalization is invariant under isomorphism of the intermediate space. -/
theorem IsRelativeNormalization.of_iso {X₁ X₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Y₀ X₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f₀ : Y₀ ⟶ X₀} {ν₁ : X₁ ⟶ X₀} {f₁ : Y₀ ⟶ X₁}
    {ν₂ : X₂ ⟶ X₀} {f₂ : Y₀ ⟶ X₂} (h : IsRelativeNormalization B S hS f₀ ν₁ f₁) (e : X₁ ≅ X₂)
    (he : f₁ ≫ e.hom = f₂) (heν : e.hom ≫ ν₂ = ν₁) :
    IsRelativeNormalization B S hS f₀ ν₂ f₂ := by
  have hν : ν₂ = e.inv ≫ ν₁ := by rw [← heν, Iso.inv_hom_id_assoc]
  have hf : f₂ ≫ e.inv = f₁ := by rw [← he, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨by rw [← he, Category.assoc, heν, h.fac], ?_, ?_⟩
  · rw [hν]
    exact isIntegralHom_comp B S hS (isIntegralHom_of_isIso B S hS e.inv) h.isIntegralHom
  · intro Z hZ π hπ g hg
    obtain ⟨k, ⟨hk, hkπ⟩, hkuniq⟩ := h.existsUnique_lift hZ π hπ g hg
    refine ⟨e.inv ≫ k, ⟨by rw [← Category.assoc, hf, hk], by rw [Category.assoc, hkπ, hν]⟩, ?_⟩
    rintro k' ⟨hk', hk'π⟩
    have : e.hom ≫ k' = k :=
      hkuniq _ ⟨by rw [← Category.assoc, he, hk'], by rw [Category.assoc, hk'π, heν]⟩
    rw [← this, Iso.inv_hom_id_assoc]

/-- **Stacks 0823, "characterized by", existence and uniqueness of the comparison.**  A
factorization `f = ν'' ∘ f''` through an algebraic space with properties (1) and (2) is joined to
the normalization `f = ν ∘ f'` by a unique isomorphism compatible with both factorizations. -/
theorem existsUnique_iso_normalizationInQcqs_of_isRelativeNormalization
    {X'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX'' : IsAlgebraicSpace B S hS X'')
    {ν'' : X'' ⟶ X.1} {f'' : Y.1 ⟶ X''} (h : IsRelativeNormalization B S hS f.hom ν'' f'') :
    ∃! e : (normalizationInQcqs B S hS f hfqc hfqs).1 ≅ X'',
      (toNormalizationInQcqs f hfqc hfqs).hom ≫ e.hom = f'' ∧
        e.hom ≫ ν'' = (normalizationInQcqsHom B S hS f hfqc hfqs).hom :=
  (isRelativeNormalization_normalizationInQcqs f hfqc hfqs).existsUnique_iso h
    (normalizationInQcqs B S hS f hfqc hfqs).property hX''

/-- **Stacks 0823: the normalization is characterized by properties (1) and (2).**  Let
`f : Y ⟶ X` be quasi-compact and quasi-separated.  A factorization `f = ν'' ∘ f''` of `f` through
an algebraic space `X''` has properties (1) and (2) — `ν''` integral, and every factorization of
`f` through an integral morphism receiving a unique compatible morphism from `X''` — if and only
if it is isomorphic to the factorization `f = ν ∘ f'` through the normalization of `X` in `Y`;
the isomorphism is then unique, by
`AlgebraicGeometry.Space.existsUnique_iso_normalizationInQcqs_of_isRelativeNormalization`. -/
@[stacks 0823 "the factorization through the normalization is characterized by (1) and (2)"]
theorem isRelativeNormalization_iff_exists_iso_normalizationInQcqs
    {X'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX'' : IsAlgebraicSpace B S hS X'')
    (ν'' : X'' ⟶ X.1) (f'' : Y.1 ⟶ X'') :
    IsRelativeNormalization B S hS f.hom ν'' f'' ↔
      ∃ e : (normalizationInQcqs B S hS f hfqc hfqs).1 ≅ X'',
        (toNormalizationInQcqs f hfqc hfqs).hom ≫ e.hom = f'' ∧
          e.hom ≫ ν'' = (normalizationInQcqsHom B S hS f hfqc hfqs).hom :=
  ⟨fun h => (existsUnique_iso_normalizationInQcqs_of_isRelativeNormalization f hfqc hfqs hX''
      h).exists,
    fun ⟨e, he, heν⟩ => (isRelativeNormalization_normalizationInQcqs f hfqc hfqs).of_iso e he heν⟩

/-! ### The comparison morphism is the normalization of `Z` in `Y` -/

/-- **Stacks 0823, the final clause.**  Let `f : Y ⟶ X` be quasi-compact and quasi-separated,
let `f = π ∘ g` with `π : Z ⟶ X` an integral morphism of algebraic spaces, and let `h : X' ⟶ Z`
be the morphism of property (2), so `h ∘ f' = g` and `π ∘ h = ν`.  Then `h : X' ⟶ Z` is the
normalization of `Z` in `Y`: the factorization `g = h ∘ f'` has properties (1) and (2) for `g`,
and it is uniquely isomorphic to the factorization of `g` through the normalization of `Z` in
`Y` of Stacks 0822, `g` being quasi-compact and quasi-separated. -/
@[stacks 0823 "moreover, in (2) the morphism h : X' ⟶ Z is the normalization of Z in Y"]
theorem isRelativeNormalization_comparison_normalizationInQcqs {Z : AlgebraicSpaces B S hS}
    (π : Z ⟶ X) (hπ : IsIntegralHom B S hS π.hom) (g : Y ⟶ Z) (hg : g ≫ π = f)
    (h : normalizationInQcqs B S hS f hfqc hfqs ⟶ Z)
    (hh : toNormalizationInQcqs f hfqc hfqs ≫ h = g)
    (hhπ : h ≫ π = normalizationInQcqsHom B S hS f hfqc hfqs) :
    IsRelativeNormalization B S hS g.hom h.hom (toNormalizationInQcqs f hfqc hfqs).hom ∧
      ∃ (hgqc : IsQuasiCompact B S hS g.hom) (hgqs : IsQuasiSeparated B S hS g.hom),
        ∃! e : (normalizationInQcqs B S hS g hgqc hgqs).1 ≅
            (normalizationInQcqs B S hS f hfqc hfqs).1,
          (toNormalizationInQcqs g hgqc hgqs).hom ≫ e.hom =
              (toNormalizationInQcqs f hfqc hfqs).hom ∧
            e.hom ≫ h.hom = (normalizationInQcqsHom B S hS g hgqc hgqs).hom := by
  have hrel : IsRelativeNormalization B S hS g.hom h.hom
      (toNormalizationInQcqs f hfqc hfqs).hom :=
    (isRelativeNormalization_normalizationInQcqs f hfqc hfqs).comparison X.property Z.property
      hπ (congrArg (fun m => m.hom) hh) (congrArg (fun m => m.hom) hhπ)
  have hgπ : g.hom ≫ π.hom = f.hom := congrArg (fun m => m.hom) hg
  have hπqs : IsQuasiSeparated B S hS π.hom :=
    isQuasiSeparated_of_isAffineHom B S hS π.hom Z.property X.property
      (isAffineHom_of_isIntegralHom π.hom hπ)
  have hgqc : IsQuasiCompact B S hS g.hom :=
    isQuasiCompact_of_comp_of_isQuasiSeparated B S hS g.hom π.hom Y.property X.property
      (by rw [hgπ]; exact hfqc) hπqs
  have hgqs : IsQuasiSeparated B S hS g.hom :=
    isQuasiSeparated_of_comp B S hS g.hom π.hom (by rw [hgπ]; exact hfqs)
  exact ⟨hrel, hgqc, hgqs,
    existsUnique_iso_normalizationInQcqs_of_isRelativeNormalization g hgqc hgqs
      (normalizationInQcqs B S hS f hfqc hfqs).property hrel⟩

end AlgebraicGeometry.Space

end
