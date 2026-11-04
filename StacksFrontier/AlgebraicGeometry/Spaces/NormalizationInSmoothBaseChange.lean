module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegrallyClosedSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeSmooth
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationInQcqsComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSmoothBaseChange

/-!
# Normalization commutes with smooth base change

Let
```
Y₂ ⟶ Y₁
 |     | f
 v     v
X₂ ⟶ X₁
   φ
```
be a fibre square of algebraic spaces over a scheme `S`, with `f` quasi-compact and
quasi-separated and `φ` smooth, and let `Yᵢ ⟶ Xᵢ' ⟶ Xᵢ` be the normalization of `Xᵢ` in `Yᵢ`.
Stacks 082F asserts that `X₂' ≅ X₂ ×_{X₁} X₁'`.  This file proves it with no further
hypothesis.

## Main results

* `AlgebraicGeometry.Space.isIntegrallyClosed_pushforwardAlgebra_of_isRelativeNormalization_id`:
  if `X'` is the normalization of itself in `Y` for a quasi-compact quasi-separated
  `q : Y ⟶ X'`, then `𝒪_{X'}` is integrally closed in `q_* 𝒪_Y`.
* `AlgebraicGeometry.Space.IsRelativeNormalization.isRelativeNormalization_baseChange_of_isSmooth`:
  the base change `Y₂ ⟶ X₂ ×_{X₁} X₁' ⟶ X₂` of the normalization of `X₁` in `Y₁` is a
  normalization of `X₂` in `Y₂`.
* `AlgebraicGeometry.Space.IsRelativeNormalization.existsUnique_iso_baseChange_of_isSmooth`:
  **Stacks 082F**, for any two normalizations in the sense of Stacks 0823.
* `AlgebraicGeometry.Space.existsUnique_iso_normalizationInQcqs_baseChange_of_isSmooth`:
  **Stacks 082F** for the normalizations constructed in Stacks 0822.

## Implementation notes

The source's proof identifies both sides as relative spectra: `X₂'` is the relative spectrum of
the integral closure of `𝒪_{X₂}` in `f_{2,*} 𝒪_{Y₂}`, and `X₂ ×_{X₁} X₁'` that of `φ^* 𝒜'` with
`𝒜'` the integral closure of `𝒪_{X₁}` in `f_{1,*} 𝒪_{Y₁}`; the two algebras agree by Stacks 073K
and Stacks 082E.  Here the comparison is made through the universal property of Stacks 0823
instead, which avoids identifying the relative spectrum of a pullback.

* `X₁'` is the normalization of itself in `Y₁` (the final clause of Stacks 0823), and `f₁'` is
  quasi-compact and quasi-separated, so `𝒪_{X₁'}` is integrally closed in `f₁'_* 𝒪_{Y₁}`.
* `P = X₂ ×_{X₁} X₁'` and `Y₂ = P ×_{X₁'} Y₁`, and `P ⟶ X₁'` is smooth as a base change of `φ`
  (Stacks 03ZE), so `𝒪_P` is integrally closed in the direct image of `𝒪_{Y₂}`: this is
  `AlgebraicGeometry.Space.isIntegrallyClosed_pushforwardAlgebra_of_isPullback_of_isSmooth`, the
  combination of Stacks 073K and Stacks 082E the source uses, carried out over affine charts.
* By the algebra criterion of Stacks 0823 `P` is then the normalization of itself in `Y₂`, and,
  `P ⟶ X₂` being integral (Stacks 03ZS), the normalization of `X₂` in `Y₂`
  (`AlgebraicGeometry.Space.IsRelativeNormalization.comp_of_id`).  The characterization of
  Stacks 0823 gives the unique isomorphism with `X₂'`.

The comparison isomorphism is compatible with the factorizations of `f₂` and the morphisms to
`X₂`; the morphism `Y₂ ⟶ X₂ ×_{X₁} X₁'` is
`AlgebraicGeometry.Space.IsRelativeNormalization.baseChangeFactorization`.

## References

* [Stacks Project, Tag 082F](https://stacks.math.columbia.edu/tag/082F)
* [Stacks Project, Tag 0823](https://stacks.math.columbia.edu/tag/0823)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
* [Stacks Project, Tag 082E](https://stacks.math.columbia.edu/tag/082E)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 03ZS](https://stacks.math.columbia.edu/tag/03ZS)
* [Stacks Project, Tag 03ZE](https://stacks.math.columbia.edu/tag/03ZE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

section Closed

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- If `T` is the normalization of itself in `Y` along a quasi-compact quasi-separated
`q : Y ⟶ T`, then `𝒪_T` is integrally closed in `q_* 𝒪_Y`: the normalization of `T` in `Y` of
Stacks 0822 has the integral closure for its algebra, and is identified with `T` by Stacks
0823. -/
theorem isIntegrallyClosed_pushforwardAlgebra_of_isRelativeNormalization_id
    {T Y : AlgebraicSpaces B S hS} (q : Y ⟶ T) (hqc : IsQuasiCompact B S hS q.hom)
    (hqs : IsQuasiSeparated B S hS q.hom)
    (h : IsRelativeNormalization B S hS q.hom (𝟙 T.1) q.hom) :
    (pushforwardAlgebra B S hS (Over.mk q)).IsIntegrallyClosed :=
  isIntegrallyClosed_of_isRelativeNormalization_id B S hS q h
    (normalizationInQcqsAffineOver B S hS q hqc hqs) (toNormalizationInQcqsOver q hqc hqs)
    (isRelativeNormalization_normalizationInQcqs q hqc hqs)
    (normalizationInQcqsPushforwardIso B S hS q hqc hqs).symm (by
      rw [pushforwardAlgebraMap_toNormalizationInQcqsOver]
      exact Iso.inv_hom_id_assoc _ _)

end Closed

namespace IsRelativeNormalization

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X₁ X₂ Y₁ Y₂ X₁' X₂' P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : Y₁ ⟶ X₁} {φ : X₂ ⟶ X₁} {g : Y₂ ⟶ Y₁} {f₂ : Y₂ ⟶ X₂}
    {ν₁ : X₁' ⟶ X₁} {f₁' : Y₁ ⟶ X₁'} {ν₂ : X₂' ⟶ X₂} {f₂' : Y₂ ⟶ X₂'}
    {p : P ⟶ X₂} {q : P ⟶ X₁'}

/-- **The base change of a normalization along a smooth morphism is a normalization.**  For a
fibre square of algebraic spaces with `f : Y₁ ⟶ X₁` quasi-compact and quasi-separated and
`φ : X₂ ⟶ X₁` smooth, and a normalization `Y₁ ⟶ X₁' ⟶ X₁` of `X₁` in `Y₁`, the base change
`Y₂ ⟶ X₂ ×_{X₁} X₁' ⟶ X₂` is a normalization of `X₂` in `Y₂`. -/
theorem isRelativeNormalization_baseChange_of_isSmooth
    (hnorm₁ : IsRelativeNormalization B S hS f ν₁ f₁')
    (hX₁ : IsAlgebraicSpace B S hS X₁) (hX₂ : IsAlgebraicSpace B S hS X₂)
    (hY₁ : IsAlgebraicSpace B S hS Y₁) (hX₁' : IsAlgebraicSpace B S hS X₁')
    (hfqc : IsQuasiCompact B S hS f) (hfqs : IsQuasiSeparated B S hS f)
    (hφ : IsSmooth B S hS φ)
    (sq : IsPullback g f₂ f φ) (sqP : IsPullback p q φ ν₁) :
    IsRelativeNormalization B S hS f₂ p (hnorm₁.baseChangeFactorization sq sqP) := by
  have hP : IsAlgebraicSpace B S hS P :=
    isAlgebraicSpace_of_isPullback hX₂ hX₁' hX₁.isSheaf hX₁.diagonal_representable sqP
  have hY₂ : IsAlgebraicSpace B S hS Y₂ :=
    isAlgebraicSpace_of_isPullback hY₁ hX₂ hX₁.isSheaf hX₁.diagonal_representable sq
  -- the bundled algebraic spaces and morphisms
  let Y₁b : AlgebraicSpaces B S hS := ⟨Y₁, hY₁⟩
  let Y₂b : AlgebraicSpaces B S hS := ⟨Y₂, hY₂⟩
  let X₁'b : AlgebraicSpaces B S hS := ⟨X₁', hX₁'⟩
  let Pb : AlgebraicSpaces B S hS := ⟨P, hP⟩
  let f₁'b : Y₁b ⟶ X₁'b := ObjectProperty.homMk f₁'
  let qb : Pb ⟶ X₁'b := ObjectProperty.homMk q
  let gb : Y₂b ⟶ Y₁b := ObjectProperty.homMk g
  let hb : Y₂b ⟶ Pb := ObjectProperty.homMk (hnorm₁.baseChangeFactorization sq sqP)
  -- `f₁' : Y₁ ⟶ X₁'` is quasi-compact and quasi-separated
  have hνqs : IsQuasiSeparated B S hS ν₁ :=
    isQuasiSeparated_of_isAffineHom B S hS ν₁ hX₁' hX₁
      (isAffineHom_of_isIntegralHom ν₁ hnorm₁.isIntegralHom)
  have hqc' : IsQuasiCompact B S hS f₁' :=
    isQuasiCompact_of_comp_of_isQuasiSeparated B S hS f₁' ν₁ hY₁ hX₁
      (by rw [hnorm₁.fac]; exact hfqc) hνqs
  have hqs' : IsQuasiSeparated B S hS f₁' :=
    isQuasiSeparated_of_comp B S hS f₁' ν₁ (by rw [hnorm₁.fac]; exact hfqs)
  -- `𝒪_{X₁'}` is integrally closed in `f₁'_* 𝒪_{Y₁}`
  have hid₁ : IsRelativeNormalization B S hS f₁' (𝟙 X₁') f₁' :=
    hnorm₁.comparison hX₁ hX₁' hnorm₁.isIntegralHom (Category.comp_id f₁')
      (Category.id_comp ν₁)
  have hcl₁ : (pushforwardAlgebra B S hS (Over.mk f₁'b)).IsIntegrallyClosed :=
    isIntegrallyClosed_pushforwardAlgebra_of_isRelativeNormalization_id f₁'b hqc' hqs' hid₁
  -- the square `Y₂ ⟶ Y₁` over `P ⟶ X₁'` is cartesian
  have htop : IsPullback g (hnorm₁.baseChangeFactorization sq sqP) f₁' q := by
    refine IsPullback.of_bot ?_ (hnorm₁.baseChangeFactorization_snd sq sqP).symm sqP.flip
    rw [hnorm₁.baseChangeFactorization_fst, hnorm₁.fac]
    exact sq
  have htopb : IsPullback gb hb f₁'b qb := IsPullback.of_map_of_faithful (ObjectProperty.ι _) htop
  -- `q : P ⟶ X₁'` is smooth, as a base change of `φ`
  have hqsm : IsSmooth B S hS qb.hom := isSmooth_of_isPullback sqP.flip hP hX₂ hX₁' hX₁ hφ
  -- so `𝒪_P` is integrally closed in the direct image of `𝒪_{Y₂}`
  have hclP : (pushforwardAlgebra B S hS (Over.mk hb)).IsIntegrallyClosed :=
    isIntegrallyClosed_pushforwardAlgebra_of_isPullback_of_isSmooth htopb hqc' hqs' hqsm hcl₁
  have hidP : IsRelativeNormalization B S hS (hnorm₁.baseChangeFactorization sq sqP) (𝟙 P)
      (hnorm₁.baseChangeFactorization sq sqP) :=
    isRelativeNormalization_id_of_isIntegrallyClosed B S hS hb hclP
  have h := hidP.comp_of_id B S hS (hnorm₁.isIntegralHom_baseChange sqP) hP hX₂
  rwa [hnorm₁.baseChangeFactorization_fst] at h

/-- **Stacks 082F.**  Let `Y₂ = X₂ ×_{X₁} Y₁` be a fibre square of algebraic spaces over `S`
with `f : Y₁ ⟶ X₁` quasi-compact and quasi-separated and `φ : X₂ ⟶ X₁` smooth, and let
`Yᵢ ⟶ Xᵢ' ⟶ Xᵢ` be the normalization of `Xᵢ` in `Yᵢ` (Stacks 0823).  Then `X₂' ≅ X₂ ×_{X₁} X₁'`,
by a unique isomorphism compatible with the two factorizations of `f₂` and with the two
morphisms to `X₂`. -/
@[stacks 082F "X₂' ≅ X₂ ×_{X₁} X₁' for f qcqs and φ smooth, for normalizations given by the \
universal property of Tag 0823"]
theorem existsUnique_iso_baseChange_of_isSmooth
    (hnorm₁ : IsRelativeNormalization B S hS f ν₁ f₁')
    (hnorm₂ : IsRelativeNormalization B S hS f₂ ν₂ f₂')
    (hX₁ : IsAlgebraicSpace B S hS X₁) (hX₂ : IsAlgebraicSpace B S hS X₂)
    (hY₁ : IsAlgebraicSpace B S hS Y₁) (hX₁' : IsAlgebraicSpace B S hS X₁')
    (hX₂' : IsAlgebraicSpace B S hS X₂')
    (hfqc : IsQuasiCompact B S hS f) (hfqs : IsQuasiSeparated B S hS f)
    (hφ : IsSmooth B S hS φ)
    (sq : IsPullback g f₂ f φ) (sqP : IsPullback p q φ ν₁) :
    ∃! e : X₂' ≅ P, f₂' ≫ e.hom = hnorm₁.baseChangeFactorization sq sqP ∧ e.hom ≫ p = ν₂ :=
  hnorm₂.existsUnique_iso
    (hnorm₁.isRelativeNormalization_baseChange_of_isSmooth hX₁ hX₂ hY₁ hX₁' hfqc hfqs hφ
      sq sqP) hX₂'
    (isAlgebraicSpace_of_isPullback hX₂ hX₁' hX₁.isSheaf hX₁.diagonal_representable sqP)

end IsRelativeNormalization

section Qcqs

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X₁ X₂ Y₁ Y₂ P : AlgebraicSpaces B S hS}

/-- **Stacks 082F, for the normalizations of Stacks 0822.**  Let `Y₂ = X₂ ×_{X₁} Y₁` be a fibre
square of algebraic spaces over `S` with `f : Y₁ ⟶ X₁` quasi-compact and quasi-separated and
`φ : X₂ ⟶ X₁` smooth, and let `P = X₂ ×_{X₁} X₁'` for `X₁'` the normalization of `X₁` in `Y₁`,
with `f₂P : Y₂ ⟶ P` the base change of `Y₁ ⟶ X₁'`.  Then `f₂ : Y₂ ⟶ X₂` is quasi-compact and
quasi-separated, and the normalization `X₂'` of `X₂` in `Y₂` is isomorphic to `P` by a unique
isomorphism compatible with the two factorizations of `f₂` and the two morphisms to `X₂`. -/
@[stacks 082F "X₂' ≅ X₂ ×_{X₁} X₁' for f qcqs and φ smooth, for the normalizations of Tag 0822"]
theorem existsUnique_iso_normalizationInQcqs_baseChange_of_isSmooth (f : Y₁ ⟶ X₁)
    (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    {φ : X₂ ⟶ X₁} (hφ : IsSmooth B S hS φ.hom) {g : Y₂ ⟶ Y₁} {f₂ : Y₂ ⟶ X₂}
    (sq : IsPullback g f₂ f φ) {p : P ⟶ X₂} {q : P ⟶ normalizationInQcqs B S hS f hfqc hfqs}
    (sqP : IsPullback p q φ (normalizationInQcqsHom B S hS f hfqc hfqs)) {f₂P : Y₂ ⟶ P}
    (h₁ : f₂P ≫ q = g ≫ toNormalizationInQcqs f hfqc hfqs) (h₂ : f₂P ≫ p = f₂) :
    ∃ (hqc₂ : IsQuasiCompact B S hS f₂.hom) (hqs₂ : IsQuasiSeparated B S hS f₂.hom),
      ∃! e : (normalizationInQcqs B S hS f₂ hqc₂ hqs₂).1 ≅ P.1,
        (toNormalizationInQcqs f₂ hqc₂ hqs₂).hom ≫ e.hom = f₂P.hom ∧
          e.hom ≫ p.hom = (normalizationInQcqsHom B S hS f₂ hqc₂ hqs₂).hom := by
  have hsq : IsPullback g.hom f₂.hom f.hom φ.hom := sq.map (ObjectProperty.ι _)
  have hsqP : IsPullback p.hom q.hom φ.hom (normalizationInQcqsHom B S hS f hfqc hfqs).hom :=
    sqP.map (ObjectProperty.ι _)
  have hqc₂ : IsQuasiCompact B S hS f₂.hom := isQuasiCompact_of_isPullback B S hS hsq hfqc
  have hqs₂ : IsQuasiSeparated B S hS f₂.hom := isQuasiSeparated_of_isPullback B S hS hsq hfqs
  have hnorm₁ := isRelativeNormalization_normalizationInQcqs f hfqc hfqs
  have hfac : hnorm₁.baseChangeFactorization hsq hsqP = f₂P.hom :=
    hsqP.hom_ext (by rw [hnorm₁.baseChangeFactorization_fst]; exact congrArg (·.hom) h₂.symm)
      (by rw [hnorm₁.baseChangeFactorization_snd]; exact congrArg (·.hom) h₁.symm)
  obtain ⟨e, ⟨he₁, he₂⟩, heu⟩ := hnorm₁.existsUnique_iso_baseChange_of_isSmooth
    (isRelativeNormalization_normalizationInQcqs f₂ hqc₂ hqs₂) X₁.2 X₂.2 Y₁.2
    (normalizationInQcqs B S hS f hfqc hfqs).2 (normalizationInQcqs B S hS f₂ hqc₂ hqs₂).2
    hfqc hfqs hφ hsq hsqP
  refine ⟨hqc₂, hqs₂, e, ⟨he₁.trans hfac, he₂⟩, fun e' ⟨he₁', he₂'⟩ => heu e' ⟨?_, he₂'⟩⟩
  rw [hfac]
  exact he₁'

end Qcqs

end AlgebraicGeometry.Space

end
