module

public import Mathlib.AlgebraicGeometry.Normalization
public import StacksCore.Tactic.StacksAttribute

/-!
# Relative normalization

The *relative normalization* of a quasi-compact, quasi-separated morphism `f : X ⟶ Y` is the
normalization of `Y` in `X`: a scheme `f.normalization` factoring `f` as an integral morphism
`f.fromNormalization` preceded by a dominant one `f.toNormalization`. The construction and its
API are already in the library; this module records the properties the source states about it
and the universal property that characterizes it.

The characterization has two forms. One says that an integral factorization of `f` is a
relative normalization exactly when it is uniquely isomorphic to `f.normalization`,
compatibly with both maps of the factorization. The other says that relative normalization is
unchanged after replacing the target by an intermediate scheme integral over it.

Finally, normalizing a relative normalization again in the same source changes nothing: the
structural morphism from the iterated normalization is an isomorphism.

## Main results

* `AlgebraicGeometry.Scheme.Hom.normalization_universalProperty_iff_existsUnique_iso`
  characterizes an integral factorization by its unique compatible isomorphism to the relative
  normalization.
* `AlgebraicGeometry.Scheme.Hom.normalizationDesc_universalProperty` gives the universal
  property of relative normalization over an intermediate scheme.
* `AlgebraicGeometry.Scheme.Hom.normalization_fromNormalization_isIso`: the iterated relative
  normalization agrees with the first one.

## Implementation notes

The library already supplies the universal property in construction-and-specification form:
`Scheme.Hom.normalizationDesc` is existence, the two composition lemmas
`Scheme.Hom.toNormalization_normalizationDesc` and `Scheme.Hom.normalizationDesc_comp` are its
defining equations, and `Scheme.Hom.normalization.hom_ext` is uniqueness. The last is stated
for an affine structural morphism, slightly more general than needed here because every
integral morphism is affine.

Dominance of the map to the relative normalization and integrality of the map from it hold in
the library without the quasi-compactness and quasi-separatedness hypotheses imposed in the
source, so the existing more general instances are adopted directly.

For the iterated normalization, rather than choosing an isomorphism between the two
normalizations the result states that the canonical structural morphism supplied by relative
normalization is an isomorphism. This retains the canonical factorization over the original
target.

## References

* [Stacks Project, Tag 035I](https://stacks.math.columbia.edu/tag/035I)
* [Stacks Project, Tag 035L](https://stacks.math.columbia.edu/tag/035L)
* [Stacks Project, Tag 0BXA](https://stacks.math.columbia.edu/tag/0BXA)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

add_to_stacks 035I "integral" AlgebraicGeometry.Scheme.Hom.instIsIntegralHomFromNormalization

add_to_stacks 035I "dominant" AlgebraicGeometry.Scheme.Hom.instIsDominantToNormalization

add_to_stacks 035L "dominance" AlgebraicGeometry.Scheme.Hom.instIsDominantToNormalization

add_to_stacks 035I "universal_property"
  AlgebraicGeometry.Scheme.Hom.normalizationDesc

add_to_stacks 035I "universal_property"
  AlgebraicGeometry.Scheme.Hom.toNormalization_normalizationDesc

add_to_stacks 035I "universal_property"
  AlgebraicGeometry.Scheme.Hom.normalizationDesc_comp

add_to_stacks 035I "universal_property"
  AlgebraicGeometry.Scheme.Hom.normalization.hom_ext

/-- A factorization of `f` through a scheme integral over the target factors through the
relative normalization. -/
private theorem exists_normalization_desc {X Y T : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f]
    [QuasiSeparated f] (j : Y ⟶ T) (q : T ⟶ X) [IsIntegralHom q] (h : j ≫ q = f) :
    ∃ b : f.normalization ⟶ T, f.toNormalization ≫ b = j ∧ b ≫ q = f.fromNormalization :=
  ⟨_, f.toNormalization_normalizationDesc j q h.symm, f.normalizationDesc_comp j q h.symm⟩

/-- An integral factorization of a quasi-compact, quasi-separated morphism has the
universal property of relative normalization if and only if it is uniquely isomorphic
to the relative normalization, compatibly with both maps of the factorization. -/
@[stacks 035I "universal_property"]
theorem normalization_universalProperty_iff_existsUnique_iso
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (i : Y ⟶ Z) (p : Z ⟶ X) [IsIntegralHom p] (hip : i ≫ p = f) :
    (∀ (T : Scheme.{u}) (j : Y ⟶ T) (q : T ⟶ X),
      IsIntegralHom q → j ≫ q = f →
        ∃! k : Z ⟶ T, i ≫ k = j ∧ k ≫ q = p) ↔
      ∃! e : Z ≅ f.normalization,
        i ≫ e.hom = f.toNormalization ∧ e.hom ≫ f.fromNormalization = p := by
  constructor
  · intro h
    obtain ⟨a, ha, ha_unique⟩ := h f.normalization f.toNormalization
      f.fromNormalization inferInstance f.toNormalization_fromNormalization
    obtain ⟨b, hb₁, hb₂⟩ := exists_normalization_desc f i p hip
    have hab : a ≫ b = 𝟙 Z := by
      refine (h Z i p inferInstance hip).unique ⟨?_, ?_⟩ (by simp)
      · rw [← Category.assoc, ha.1, hb₁]
      · rw [Category.assoc, hb₂, ha.2]
    have hba : b ≫ a = 𝟙 f.normalization := by
      refine normalization.hom_ext (f := f) _ _ f.fromNormalization ?_ ?_ (by simp)
      · rw [← Category.assoc, hb₁, ha.1, Category.comp_id]
      · rw [Category.assoc, ha.2, hb₂]
    exact ⟨⟨a, b, hab, hba⟩, ha, fun e he => Iso.ext (ha_unique e.hom he)⟩
  · rintro ⟨e, he, _⟩ T j q hq hjq
    obtain ⟨b, hb₁, hb₂⟩ := exists_normalization_desc f j q hjq
    refine ⟨e.hom ≫ b, ⟨?_, ?_⟩, fun k hk => ?_⟩
    · rw [← Category.assoc, he.1, hb₁]
    · rw [Category.assoc, hb₂, he.2]
    have he_inv₁ : f.toNormalization ≫ e.inv = i := by simp [← he.1, Category.assoc]
    have he_inv₂ : e.inv ≫ p = f.fromNormalization := by simp [← he.2, ← Category.assoc]
    have hk' : e.inv ≫ k = b := by
      refine normalization.hom_ext (f := f) _ _ q ?_ ?_ hb₂
      · rw [← Category.assoc, he_inv₁, hk.1, hb₁]
      · rw [Category.assoc, hk.2, he_inv₂]
    rw [← hk', Iso.hom_inv_id_assoc]

/-- Relative normalization is unchanged after replacing the target by an
intermediate scheme integral over it. -/
@[stacks 035I "normalization_over_intermediate"]
theorem normalizationDesc_universalProperty
    {X Y Z : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f]
    (g : Y ⟶ Z) (p : Z ⟶ X) [IsIntegralHom p] (H : f = g ≫ p) :
    ∀ (T : Scheme.{u}) (j : Y ⟶ T) (q : T ⟶ Z),
      IsIntegralHom q → j ≫ q = g →
        ∃! k : f.normalization ⟶ T,
          f.toNormalization ≫ k = j ∧
            k ≫ q = f.normalizationDesc g p H := by
  intro T j q hq hjq
  obtain ⟨b, hb₁, hb₂⟩ := exists_normalization_desc f j (q ≫ p)
    (by simpa only [← Category.assoc, hjq] using H.symm)
  refine ⟨b, ⟨hb₁, ?_⟩, fun l hl => ?_⟩
  · refine normalization.hom_ext (f := f) _ _ p ?_ ?_ (f.normalizationDesc_comp g p H)
    · simp only [← Category.assoc, f.toNormalization_normalizationDesc, hb₁, hjq]
    · simpa only [Category.assoc] using hb₂
  · refine normalization.hom_ext (f := f) _ _ (q ≫ p) (hl.1.trans hb₁.symm) ?_ hb₂
    simpa only [← Category.assoc, hl.2] using f.normalizationDesc_comp g p H

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]

/-- The normalization of `f.normalization` in `X` is canonically isomorphic to
`f.normalization`. -/
@[stacks 0BXA]
instance normalization_fromNormalization_isIso :
    IsIso (f.toNormalization.fromNormalization) := by
  let g := f.toNormalization
  let q : g.normalization ⟶ Y := g.fromNormalization ≫ f.fromNormalization
  have hfactor : f = g.toNormalization ≫ q := by
    change f = g.toNormalization ≫ (g.fromNormalization ≫ f.fromNormalization)
    rw [← Category.assoc, g.toNormalization_fromNormalization,
      f.toNormalization_fromNormalization]
  let h : f.normalization ⟶ g.normalization :=
    f.normalizationDesc g.toNormalization q hfactor
  have hh₁ : f.toNormalization ≫ h = g.toNormalization :=
    f.toNormalization_normalizationDesc g.toNormalization q hfactor
  have h_inv_hom : h ≫ g.fromNormalization = 𝟙 f.normalization := by
    refine normalization.hom_ext (f := f) _ _ f.fromNormalization ?_ ?_ (by simp)
    · simp only [← Category.assoc, hh₁, g.toNormalization_fromNormalization,
        Category.comp_id]
      rfl
    · simpa only [Category.assoc] using
        f.normalizationDesc_comp g.toNormalization q hfactor
  have h_hom_inv : g.fromNormalization ≫ h = 𝟙 g.normalization := by
    refine normalization.hom_ext (f := g) _ _ g.fromNormalization ?_ ?_ (by simp)
    · simpa only [← Category.assoc, g.toNormalization_fromNormalization,
        Category.comp_id] using hh₁
    · simp only [Category.assoc, h_inv_hom, Category.comp_id]
  exact ⟨h, h_hom_inv, h_inv_hom⟩

end AlgebraicGeometry.Scheme.Hom
