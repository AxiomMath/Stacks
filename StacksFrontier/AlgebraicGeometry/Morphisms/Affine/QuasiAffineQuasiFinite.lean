module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import StacksFrontier.AlgebraicGeometry.AmpleCluster.QuasiAffineAndImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffineStability
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A separated quasi-finite morphism of schemes is quasi-affine

Stacks 02LR is the quasi-affineness half of Zariski's main theorem. Let `f : X ⟶ S` be a
quasi-finite separated morphism of schemes and let `ν : S' ⟶ S` be the normalization of `S` in
`X`, so that `f` factors as `f' : X ⟶ S'` followed by `ν`. Then `f'` is a quasi-compact open
immersion and `ν` is integral; in particular `f` is quasi-affine.

The factorization and both of its properties are Mathlib's: `ν` is
`AlgebraicGeometry.Scheme.Hom.fromNormalization`, which is integral for any quasi-compact
quasi-separated `f`, and `f'` is `AlgebraicGeometry.Scheme.Hom.toNormalization`, which is
quasi-compact always and an open immersion exactly under the hypotheses of Stacks 02LR, by
`AlgebraicGeometry.Scheme.Hom.exists_isIso_morphismRestrict_toNormalization` — Mathlib's form of
Stacks 03GW, the lemma the source cites.

What this file adds is the "in particular": quasi-affineness is read off the factorization
through Stacks 01SN, stability of quasi-affine morphisms under composition, once each factor is
known to be quasi-affine. A quasi-compact immersion is quasi-affine because the inverse image of
an affine open of the target is a quasi-compact locally closed subscheme of an affine scheme,
which is quasi-affine by Stacks 0BCK; and an affine morphism is quasi-affine because the inverse
image of an affine open is affine.

"Quasi-finite" is Stacks 02NG, that is, locally quasi-finite and of finite type, so in Mathlib's
vocabulary `AlgebraicGeometry.LocallyQuasiFinite`, `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.QuasiCompact` together. The local-of-finite-type conjunct is not redundant:
Mathlib's `AlgebraicGeometry.LocallyQuasiFinite` omits the finite-type condition of Stacks 00PL,
and Stacks 02LR is false without it — `Spec ℚ ⟶ Spec ℤ` is a separated, quasi-compact morphism
which is locally quasi-finite in Mathlib's sense and is not quasi-affine, `ℚ` not being a
finitely generated `ℤ`-algebra. See the implementation notes of
`StacksFrontier.AlgebraicGeometry.Descent.SeparatedQuasiFiniteEtaleDescent`.

## Main results

* `AlgebraicGeometry.isQuasiAffineHom_of_isAffineHom`: an affine morphism of schemes is
  quasi-affine.
* `AlgebraicGeometry.isQuasiAffineHom_of_isImmersion`: a quasi-compact immersion of schemes is
  quasi-affine.
* `AlgebraicGeometry.isOpenImmersion_toNormalization_and_isIntegralHom_fromNormalization` is the
  factorization clause of Stacks 02LR: for a separated quasi-finite `f`, the morphism to the
  normalization of the target in the source is a quasi-compact open immersion and the
  normalization itself is integral.
* `AlgebraicGeometry.isQuasiAffineHom_of_locallyQuasiFinite` is the "in particular" clause of
  Stacks 02LR: a separated quasi-finite morphism of schemes is quasi-affine.
* `AlgebraicGeometry.isSeparated_inf_quasiFinite_le_isQuasiAffineHom` is the same statement as a
  containment of morphism properties, which is the shape in which
  `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_quasiFinite`
  consumes Stacks 02LR.
* `AlgebraicGeometry.exists_isAffineOpen_containing_finite_of_locallyQuasiFinite` is Stacks 07S0:
  over an affine base, every finite set of points of the source of a separated quasi-finite
  morphism lies in a single affine open.

## Implementation notes

The two helper lemmas are stated as lemmas rather than registered as instances. They would both
fire on every search for `AlgebraicGeometry.IsQuasiAffineHom`, and the second would do so from
the pair of unrelated hypotheses `AlgebraicGeometry.IsImmersion` and
`AlgebraicGeometry.QuasiCompact`; the composition below names them explicitly instead.

## References

* [Stacks Project, Tag 02LR](https://stacks.math.columbia.edu/tag/02LR)
* [Stacks Project, Tag 07S0](https://stacks.math.columbia.edu/tag/07S0)
* [Stacks Project, Tag 01ZY](https://stacks.math.columbia.edu/tag/01ZY)
* [Stacks Project, Tag 03GW](https://stacks.math.columbia.edu/tag/03GW)
* [Stacks Project, Tag 01SM](https://stacks.math.columbia.edu/tag/01SM)
* [Stacks Project, Tag 01SN](https://stacks.math.columbia.edu/tag/01SN)
* [Stacks Project, Tag 0BCK](https://stacks.math.columbia.edu/tag/0BCK)
* [Stacks Project, Tag 02NG](https://stacks.math.columbia.edu/tag/02NG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- An affine morphism of schemes is quasi-affine: the inverse image of an affine open of the
target is affine, hence quasi-affine. -/
lemma isQuasiAffineHom_of_isAffineHom [IsAffineHom f] : IsQuasiAffineHom f := by
  refine ⟨fun U hU ↦ ?_⟩
  have : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  infer_instance

/-- **Stacks Project, Tag 0BCK, relative form.** A quasi-compact immersion of schemes is
quasi-affine: the inverse image of an affine open `U` of the target is a quasi-compact locally
closed subscheme of the affine scheme `U`. -/
@[ega "II 5.1.10" "(i), special case"]
lemma isQuasiAffineHom_of_isImmersion [IsImmersion f] [QuasiCompact f] :
    IsQuasiAffineHom f := by
  refine ⟨fun U hU ↦ ?_⟩
  have : CompactSpace (f ⁻¹ᵁ U).toScheme :=
    isCompact_iff_compactSpace.mp ((quasiCompact_iff_forall_isAffineOpen.mp ‹_›) U hU)
  have : IsAffine U.toScheme := hU
  exact Scheme.IsQuasiAffine.of_isImmersion (f ∣_ U)

/-- **Stacks Project, Tag 02LR, the factorization.** Let `f : X ⟶ S` be a separated quasi-finite
morphism of schemes. Then the morphism from `X` to the normalization of `S` in `X` is a
quasi-compact open immersion, and the normalization is integral over `S`.

Both clauses are Mathlib instances; the open immersion is Mathlib's form of Stacks 03GW. -/
@[stacks 02LR "the factorization", ega "IV 8.12.11" "sufficiency"]
theorem isOpenImmersion_toNormalization_and_isIntegralHom_fromNormalization [IsSeparated f]
    [LocallyQuasiFinite f] [LocallyOfFiniteType f] [QuasiCompact f] :
    IsOpenImmersion f.toNormalization ∧ QuasiCompact f.toNormalization ∧
      IsIntegralHom f.fromNormalization :=
  ⟨inferInstance, inferInstance, inferInstance⟩

/-- **Stacks Project, Tag 02LR, quasi-affineness.** A separated quasi-finite morphism of schemes
is quasi-affine.

It factors as the morphism to the normalization of the target in the source, which is a
quasi-compact open immersion and hence quasi-affine, followed by the normalization, which is
integral and hence affine and hence quasi-affine; quasi-affine morphisms are stable under
composition by Stacks 01SN. -/
@[stacks 02LR "quasi-affineness",
  ega "IV 18.12.12",
  ega "II 6.2.7" "more general",
  ega "III 4.4.12" "(i) quasi-affine",
  ega "IV 8.11.2" "more general",
  sga "1 VIII 6.2" "more general"]
theorem isQuasiAffineHom_of_locallyQuasiFinite [IsSeparated f] [LocallyQuasiFinite f]
    [LocallyOfFiniteType f] [QuasiCompact f] : IsQuasiAffineHom f := by
  rw [← f.toNormalization_fromNormalization]
  exact MorphismProperty.comp_mem _ _ _
    (isQuasiAffineHom_of_isImmersion f.toNormalization)
    (isQuasiAffineHom_of_isAffineHom f.fromNormalization)

/-- **Stacks Project, Tag 02LR** as a containment of morphism properties: the separated
quasi-finite morphisms of schemes — separated, locally quasi-finite, locally of finite type and
quasi-compact — are quasi-affine.

This is the shape in which
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_quasiFinite`
takes Stacks 02LR as a hypothesis. -/
@[stacks 02LR "containment of properties",
  ega "IV 18.12.12",
  ega "II 6.2.7",
  ega "III 4.4.12" "(i) quasi-affine",
  ega "IV 8.11.2" "more general",
  sga "1 VIII 6.2" "more general",
  sga "3 X 5.4" "more general"]
theorem isSeparated_inf_quasiFinite_le_isQuasiAffineHom :
    (@IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType ⊓ @QuasiCompact :
        MorphismProperty Scheme.{u}) ≤ @IsQuasiAffineHom := by
  rintro X S g ⟨⟨⟨hsep, hqf⟩, hft⟩, hqc⟩
  exact @isQuasiAffineHom_of_locallyQuasiFinite _ _ g hsep hqf hft hqc

/-- **Stacks Project, Tag 07S0.** Let `f : X ⟶ S` be a separated quasi-finite morphism of
schemes with affine target. Then every finite set of points of `X` is contained in a single
affine open of `X`.

Cover the finite set by finitely many affine opens and let `U` be their union. Then `U` is
quasi-compact, so `U.ι ≫ f` is quasi-compact, and it is still separated and quasi-finite; hence
it is quasi-affine by Stacks 02LR. Taking the affine open `⊤` of `S` shows that `U` itself is a
quasi-affine scheme, and Stacks 01ZY part (1) puts the finite set into an affine open of `U`. -/
@[stacks 07S0]
theorem exists_isAffineOpen_containing_finite_of_locallyQuasiFinite [IsSeparated f]
    [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsAffine S] {E : Set X} (hE : E.Finite) :
    ∃ U : X.Opens, IsAffineOpen U ∧ E ⊆ U := by
  have : Finite E := hE.to_subtype
  choose V hV hxV _ using fun x : E ↦
    exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ (x : X))
  let U : X.Opens := ⨆ x : E, V x
  have hEU : E ⊆ (U : Set X) := fun x hx ↦ (le_iSup V ⟨x, hx⟩) (hxV ⟨x, hx⟩)
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp (by
    simpa [U] using isCompact_iUnion fun x : E ↦ (hV x).isCompact)
  have : Scheme.IsQuasiAffine ((⊤ : U.toScheme.Opens) : Scheme) := by
    simpa using (isQuasiAffineHom_iff (U.ι ≫ f)).mp
      (isQuasiAffineHom_of_locallyQuasiFinite (U.ι ≫ f)) ⊤ (isAffineOpen_top S)
  have : U.toScheme.IsQuasiAffine := Scheme.IsQuasiAffine.of_isImmersion U.toScheme.topIso.inv
  obtain ⟨W, hW, hEW⟩ := Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_isQuasiAffine
    (X := U.toScheme) (hE.preimage fun _ _ _ _ hab ↦ U.ι.isOpenEmbedding.injective hab)
  have : IsAffine W.toScheme := hW
  exact ⟨(W.ι ≫ U.ι).opensRange, isAffineOpen_opensRange _, fun x hx ↦
    Scheme.Hom.mem_opensRange.mpr ⟨⟨⟨x, hEU hx⟩,
      hEW (show U.ι (⟨x, hEU hx⟩ : U.toScheme) ∈ E by simpa using hx)⟩, rfl⟩⟩

end AlgebraicGeometry

end
