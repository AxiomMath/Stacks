module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreReductionNormalization

/-!
# The normalization is insensitive to isomorphisms and to surjective closed immersions

The normalization of a scheme is characterised by a universal property among morphisms from
normal schemes whose generic points dominate generic points
(`AlgebraicGeometry.Scheme.existsUnique_lift_normalization`).  Two consequences of that
characterisation are collected here.

* An isomorphism of schemes induces an isomorphism of their normalizations, compatibly with the
  two normalization morphisms.
* A **surjective closed immersion** `ι : Z ⟶ W` induces an isomorphism of their normalizations,
  again compatibly: such an `ι` cuts out a closed subscheme whose ideal consists of nilpotents,
  and the normalization only sees the reduction.  *Neither* scheme is assumed reduced.

The second statement is what lets a normalized base change be computed after discarding
nilpotents.  In the reduced fibre theorem the scheme whose normalization is taken is a base
change `X ×_{Spec A} Spec B` of a scheme that is *not* assumed reduced, while the comparison of
iterated normalized base changes (in `AlgebraicGeometry.NormalizedBaseChange`,
`exists_normalizationScheme_iso_baseChangeMap_normalization_of_isNoetherianRing`)
asks the scheme being normalized to be reduced — because the base change of the normalization
morphism is birational only then.  Replacing the base change by its reduction is legitimate
exactly by the second statement.

## Main results

* `AlgebraicGeometry.Scheme.exists_normalizationScheme_iso_of_iso`: an isomorphism of schemes
  induces one of their normalizations.
* `AlgebraicGeometry.Scheme.exists_normalizationScheme_iso_of_ker_eq_nilradical`: a closed
  immersion whose kernel ideal sheaf is the nilradical induces one.
* `AlgebraicGeometry.Scheme.exists_normalizationScheme_iso_of_surjective`: a surjective closed
  immersion induces one, with no reducedness hypothesis on either scheme.

## Implementation notes

All three statements are existential rather than definitional: the normalization is a chosen
object with a universal property, and the comparison isomorphism is the unique morphism the
property provides, which is cheaper to produce than to name.

The third statement is reduced to the second by factoring through the reduction of the *source*:
the composite `Z_red ⟶ Z ⟶ W` is a surjective closed immersion with reduced source, hence has
kernel the nilradical of `W` by `AlgebraicGeometry.ker_eq_nilradical_of_surjective`, and the same
applies to `Z_red ⟶ Z`.

## References

* [Stacks Project, Tag 035O](https://stacks.math.columbia.edu/tag/035O)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
-/

public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- **An isomorphism of schemes induces an isomorphism of their normalizations.** The comparison
is compatible with the two normalization morphisms.

Each direction is the unique lift of the one normalization morphism, composed with the
isomorphism, through the other; the two composites are identities because the identity is the
unique lift of a normalization morphism through itself. -/
theorem exists_normalizationScheme_iso_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite) :
    ∃ d : X.normalizationScheme hX ≅ Y.normalizationScheme hY,
      d.hom ≫ Y.normalization hY = X.normalization hX ≫ e.hom := by
  have hgen : ∀ {Z W : Scheme.{u}} (c : Z ≅ W) (z : Z), z ∈ genericPoints Z →
      c.hom.base z ∈ genericPoints W := fun c _ hz =>
    mem_genericPoints_of_generalizingMap
      (Scheme.homeoOfIso c).isOpenEmbedding.generalizingMap hz
  have _ : IsNormal (X.normalizationScheme hX) := isNormal_normalizationScheme X hX
  have _ : IsNormal (Y.normalizationScheme hY) := isNormal_normalizationScheme Y hY
  obtain ⟨g, hg, -⟩ := existsUnique_lift_normalization hY (X.normalization hX ≫ e.hom)
    fun η => hgen e _ (normalization_mem_genericPoints X hX η.2)
  obtain ⟨g', hg', -⟩ := existsUnique_lift_normalization hX (Y.normalization hY ≫ e.inv)
    fun η => hgen e.symm _ (normalization_mem_genericPoints Y hY η.2)
  have huX := existsUnique_lift_normalization hX (X.normalization hX)
    fun η => normalization_mem_genericPoints X hX η.2
  have huY := existsUnique_lift_normalization hY (Y.normalization hY)
    fun η => normalization_mem_genericPoints Y hY η.2
  refine ⟨⟨g, g', huX.unique ?_ (Category.id_comp _), huY.unique ?_ (Category.id_comp _)⟩, hg⟩
  · rw [Category.assoc, hg', ← Category.assoc, hg, Category.assoc, e.hom_inv_id,
      Category.comp_id]
  · rw [Category.assoc, hg, ← Category.assoc, hg', Category.assoc, e.inv_hom_id,
      Category.comp_id]

/-- **A closed immersion whose kernel ideal sheaf is the nilradical induces an isomorphism of
normalizations.** Such a closed immersion is the reduction
(`AlgebraicGeometry.exists_iso_nilradical_subscheme_of_ker_eq_nilradical`), and the normalization
of a scheme is the normalization of its reduction (Tag 035O). -/
theorem exists_normalizationScheme_iso_of_ker_eq_nilradical {Z W : Scheme.{u}} (ι : Z ⟶ W)
    [IsClosedImmersion ι] (hι : ι.ker = W.nilradical)
    (hZ : ∀ U : Z.Opens, IsCompact (U : Set Z) → (irreducibleComponents U).Finite)
    (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite) :
    ∃ d : W.normalizationScheme hW ≅ Z.normalizationScheme hZ,
      d.hom ≫ Z.normalization hZ ≫ ι = W.normalization hW := by
  obtain ⟨c, hc⟩ := exists_iso_nilradical_subscheme_of_ker_eq_nilradical ι hι
  obtain ⟨e₀, he₀⟩ := W.exists_normalizationScheme_iso_reduction hW
  obtain ⟨d₀, hd₀⟩ := exists_normalizationScheme_iso_of_iso c hZ
    (W.finite_irreducibleComponents_reduction hW)
  refine ⟨e₀ ≪≫ d₀.symm, ?_⟩
  have hinv : d₀.inv ≫ Z.normalization hZ ≫ c.hom =
      W.nilradical.subscheme.normalization (W.finite_irreducibleComponents_reduction hW) := by
    rw [← hd₀, Iso.inv_hom_id_assoc]
  have hsplit : (e₀ ≪≫ d₀.symm).hom ≫ Z.normalization hZ ≫ ι =
      e₀.hom ≫ (d₀.inv ≫ Z.normalization hZ ≫ c.hom) ≫ W.nilradical.subschemeι := by
    rw [← hc]; simp
  rw [hsplit, hinv, he₀]

/-- **A surjective closed immersion induces an isomorphism of normalizations.** Neither scheme is
assumed reduced: the composite `Z_red ⟶ Z ⟶ W` is a surjective closed immersion with reduced
source, so it has kernel the nilradical of `W`, and likewise `Z_red ⟶ Z` has kernel the
nilradical of `Z`; the two resulting comparisons with the normalization of `Z_red` give the
isomorphism. -/
theorem exists_normalizationScheme_iso_of_surjective {Z W : Scheme.{u}} (ι : Z ⟶ W)
    [IsClosedImmersion ι] [Surjective ι]
    (hZ : ∀ U : Z.Opens, IsCompact (U : Set Z) → (irreducibleComponents U).Finite)
    (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite) :
    ∃ d : W.normalizationScheme hW ≅ Z.normalizationScheme hZ,
      d.hom ≫ Z.normalization hZ ≫ ι = W.normalization hW := by
  have hR : IsReduced Z.nilradical.subscheme := by
    simpa only [Scheme.IdealSheafData.vanishingIdeal_top] using
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (X := Z) ⊤
  have hsurjR : Surjective Z.nilradical.subschemeι := ⟨fun x ↦
    Set.mem_range.mp (by rw [Z.nilradical.range_subschemeι, Scheme.support_nilradical]; trivial)⟩
  have _ := hR
  have _ := hsurjR
  obtain ⟨d₁, hd₁⟩ := exists_normalizationScheme_iso_of_ker_eq_nilradical
    (Z.nilradical.subschemeι ≫ ι) (ker_eq_nilradical_of_surjective _)
    (Z.finite_irreducibleComponents_reduction hZ) hW
  obtain ⟨d₂, hd₂⟩ := exists_normalizationScheme_iso_of_ker_eq_nilradical
    Z.nilradical.subschemeι (ker_eq_nilradical_of_surjective _)
    (Z.finite_irreducibleComponents_reduction hZ) hZ
  refine ⟨d₁ ≪≫ d₂.symm, ?_⟩
  have hinv : d₂.inv ≫ Z.normalization hZ =
      Z.nilradical.subscheme.normalization (Z.finite_irreducibleComponents_reduction hZ) ≫
        Z.nilradical.subschemeι := by
    rw [← hd₂, Iso.inv_hom_id_assoc]
  have hsplit : (d₁ ≪≫ d₂.symm).hom ≫ Z.normalization hZ ≫ ι =
      d₁.hom ≫ (d₂.inv ≫ Z.normalization hZ) ≫ ι := by simp
  rw [hsplit, hinv, Category.assoc]
  exact hd₁

end AlgebraicGeometry.Scheme

end
