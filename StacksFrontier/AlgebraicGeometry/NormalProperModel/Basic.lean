module

public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Japanese
public import StacksFrontier.AlgebraicGeometry.Properties.Nagata
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.RingTheory.Nagata.MonogenicN1

/-!
# Replacing a variety by its normalization

Let `k` be a field and let `f : Xbar ⟶ Spec k` be a variety over `k`. Its normalization
`ν : Xbar^ν ⟶ Xbar` is a finite morphism from a normal variety, so composing with `f` presents
`Xbar^ν` as a variety over `k` which is proper whenever `Xbar` is. Moreover `ν` is an isomorphism
over any normal open of `Xbar`, so an open subscheme of `Xbar` which is normal is also an open
subscheme of `Xbar^ν`. This is Tag 0BXR (4) for an irreducible base together with the detail the
source omits, and it is what lets an argument about a normal open of a proper variety assume that
the ambient proper variety is itself normal.

## Main results

* `AlgebraicGeometry.Scheme.isIso_normalization_restrict_of_isNormalRing`: the normalization
  morphism restricted to an affine open with normal ring of sections is an isomorphism.
* `AlgebraicGeometry.Scheme.isIso_normalization_restrict_of_isNormal`: hence the normalization
  morphism is an isomorphism over any open subscheme which is normal, with no reducedness
  hypothesis on the ambient scheme.
* `AlgebraicGeometry.Scheme.exists_isOpenImmersion_normalization_of_isNormal`: a normal open
  subscheme of `Xbar` is an open subscheme of the normalization of `Xbar`, compatibly with `ν`.
* `AlgebraicGeometry.isJapaneseScheme_of_isNagataScheme`: an integral Nagata scheme is Japanese.
* `AlgebraicGeometry.Scheme.isIntegral_normalizationScheme` (stated in
  `StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme`): the normalization of an integral
  scheme is integral.
* `AlgebraicGeometry.exists_normal_properVariety_model`: a normal open subscheme of a proper
  variety is an open subscheme of a *normal* proper variety, compatibly with the structure
  morphisms.

## Implementation notes

The affine case is the inclusion of a normal ring into its integral closure in its total ring of
fractions, which is bijective by Tag 034M; this is the computation already carried out for the
global statement `AlgebraicGeometry.Scheme.isIso_normalization_of_isNormal`, isolated here for one
affine open so that it can be used over a proper open. Passing from affine opens to a normal open
is `AlgebraicGeometry.IsZariskiLocalAtTarget` for the isomorphism property, with
`AlgebraicGeometry.morphismRestrictRestrict` identifying the two successive restrictions; the
affine opens used are those of the open subscheme, whose images are affine opens of the ambient
scheme because the inclusion is an open immersion, and whose rings of sections are *equal* to the
rings of sections on those images.

Finiteness of the normalization is `AlgebraicGeometry.normalization_isFinite`, which asks for the
Japanese condition; for a scheme locally of finite type over a field that comes from Tag 035B
through `AlgebraicGeometry.isNagataScheme_of_locallyOfFiniteType_over_field` and the ring-level
implication `MonogenicN1.isJapaneseRing_of_isNagataRing`. Integrality of the normalization is
Mathlib's instance for the relative normalization of a morphism with integral source, the source
here being the coproduct of the residue fields at the generic points, which for an irreducible
scheme has exactly one summand.

## References

* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
* [Stacks Project, Tag 035R](https://stacks.math.columbia.edu/tag/035R)
* [Stacks Project, Tag 0BXR](https://stacks.math.columbia.edu/tag/0BXR)
* [Stacks Project, Tag 034M](https://stacks.math.columbia.edu/tag/034M)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The normalization morphism over a normal open -/

namespace Scheme

/-- The normalization morphism of a reduced scheme, restricted over an affine open whose ring of
sections is a normal ring, is an isomorphism: over that open it is the inclusion of the ring of
sections into its integral closure in its total ring of fractions, which is bijective because a
normal ring is integrally closed in its total ring of fractions (Tag 034M). -/
theorem isIso_normalization_restrict_of_isNormalRing (X : Scheme.{u}) [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    {U : X.Opens} (hU : IsAffineOpen U) (hnorm : IsNormalRing Γ(X, U)) :
    IsIso (X.normalization hX ∣_ U) := by
  have hredU : _root_.IsReduced Γ(X, U) := IsReduced.component_reduced U
  have hbij : Function.Bijective
      (algebraMap Γ(X, U) (integralClosure Γ(X, U) (FractionRing Γ(X, U)))) := by
    refine ⟨fun a b hab ↦ ?_, fun b ↦ ?_⟩
    · exact IsLocalization.injective (M := nonZeroDivisors Γ(X, U))
        (FractionRing Γ(X, U)) le_rfl (congrArg Subtype.val hab)
    · obtain ⟨a, ha⟩ := hnorm.exists_algebraMap_eq_of_isIntegral b.2
      exact ⟨a, Subtype.ext ha⟩
  have hiso : IsIso (CommRingCat.ofHom
      (algebraMap Γ(X, U) (integralClosure Γ(X, U) (FractionRing Γ(X, U))))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have hchart := preimageNormalizationIsoSpecIntegralClosure_hom_comp hX U hU.isoSpec.symm
  have heq : (X.normalization hX ∣_ U) =
      ((preimageNormalizationIsoSpecIntegralClosure hX U hU.isoSpec.symm).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X, U) (integralClosure Γ(X, U) (FractionRing Γ(X, U)))))) ≫
        hU.isoSpec.inv := by
    rw [hchart]
    simp
  rw [heq]
  infer_instance

/-- The ring of sections of a normal scheme on an affine open is a normal ring. -/
private theorem isNormalRing_of_isNormal_of_affineOpen (X : Scheme.{u}) (hX : IsNormal X)
    (V : X.affineOpens) : IsNormalRing Γ(X, V.1) :=
  (((isNormal_tfae X).out 1 2).mp hX : ∀ V : X.affineOpens, IsNormalRing Γ(X, V.1)) V

/-- The normalization morphism of a reduced scheme is an isomorphism over every open subscheme
which is a normal scheme. -/
private theorem isIso_normalization_restrict_of_isNormal_of_isReduced (X : Scheme.{u})
    [IsReduced X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (W : X.Opens) (hW : IsNormal W.toScheme) :
    IsIso (X.normalization hX ∣_ W) := by
  refine IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := .isomorphisms Scheme) fun w ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hwV, -⟩ :=
    W.toScheme.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ w) isOpen_univ
  refine ⟨V, hwV, ?_⟩
  rw [MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (morphismRestrictRestrict (X.normalization hX) W V)]
  exact X.isIso_normalization_restrict_of_isNormalRing hX (hV.image_of_isOpenImmersion W.ι)
    (isNormalRing_of_isNormal_of_affineOpen W.toScheme hW ⟨V, hV⟩)

/-- **The normalization morphism is an isomorphism over every normal open subscheme.** The
scheme `X` is *not* assumed reduced.

The normalization only sees the reduction: the closed immersion `X_red ⟶ X` is surjective, so
it induces an isomorphism of normalizations compatible with the two normalization morphisms
(Tag 035O). A normal open `W ⊆ X` is in particular reduced, so the surjective closed immersion
`X_red ⟶ X` restricted over `W` is an isomorphism; its source is therefore a normal open of
`X_red`, over which the reduced case applies. -/
theorem isIso_normalization_restrict_of_isNormal (X : Scheme.{u})
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (W : X.Opens) (hW : IsNormal W.toScheme) :
    IsIso (X.normalization hX ∣_ W) := by
  have _ : IsReduced X.nilradical.subscheme := by
    rw [Scheme.nilradical]
    infer_instance
  have hsurj : Surjective X.nilradical.subschemeι := ⟨fun x ↦ Set.mem_range.mp
    (by rw [X.nilradical.range_subschemeι, Scheme.support_nilradical]; trivial)⟩
  have _ : Surjective (X.nilradical.subschemeι ∣_ W) :=
    IsZariskiLocalAtTarget.restrict hsurj W
  have _ : IsReduced W.toScheme := isReduced_of_isNormal W.toScheme
  have h3 : IsIso (X.nilradical.subschemeι ∣_ W) :=
    isIso_of_isClosedImmersion_of_surjective _
  have h2 : IsIso (X.nilradical.subscheme.normalization
      (X.finite_irreducibleComponents_reduction hX) ∣_ (X.nilradical.subschemeι ⁻¹ᵁ W)) :=
    isIso_normalization_restrict_of_isNormal_of_isReduced _
      (X.finite_irreducibleComponents_reduction hX) _
      (isNormal_of_iso (asIso (X.nilradical.subschemeι ∣_ W)))
  obtain ⟨e, he⟩ := X.exists_normalizationScheme_iso_reduction hX
  have h1 : IsIso (e.hom ∣_ (X.nilradical.subscheme.normalization
      (X.finite_irreducibleComponents_reduction hX) ≫ X.nilradical.subschemeι) ⁻¹ᵁ W) :=
    inferInstance
  rw [← he, morphismRestrict_comp, morphismRestrict_comp]
  exact IsIso.comp_isIso' h1 (IsIso.comp_isIso' h2 h3)

/-- A normal open subscheme of a scheme `Y` is an open subscheme of the normalization of `Y`,
compatibly with the normalization morphism. This is the detail omitted in the source of
Tag 04L4: the normalization is an isomorphism over a normal open. -/
theorem exists_isOpenImmersion_normalization_of_isNormal {X Y : Scheme.{u}}
    (hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite)
    (i : X ⟶ Y) [IsOpenImmersion i] [IsNormal X] :
    ∃ j : X ⟶ Y.normalizationScheme hY, IsOpenImmersion j ∧ j ≫ Y.normalization hY = i := by
  set W : Y.Opens := i.opensRange with hWdef
  have hWn : IsNormal W.toScheme := isNormal_of_iso i.isoOpensRange.symm
  have hiso : IsIso (Y.normalization hY ∣_ W) :=
    Y.isIso_normalization_restrict_of_isNormal hY W hWn
  refine ⟨i.isoOpensRange.hom ≫ inv (Y.normalization hY ∣_ W) ≫
    (Y.normalization hY ⁻¹ᵁ W).ι, inferInstance, ?_⟩
  rw [Category.assoc, Category.assoc, ← morphismRestrict_ι (Y.normalization hY) W,
    IsIso.inv_hom_id_assoc]
  exact i.isoOpensRange_hom_ι

end Scheme

/-! ### The Japanese condition for a variety -/

/-- An integral Nagata scheme is Japanese: the ring of sections on a nonempty affine open is a
Nagata domain, and a Nagata domain is N-2. -/
theorem isJapaneseScheme_of_isNagataScheme (X : Scheme.{u}) [IsIntegral X]
    (hX : IsNagataScheme X) : IsJapaneseScheme X := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hX x
  refine ⟨U, hxU, ?_⟩
  have : IsDomain Γ(X, (U : X.Opens)) :=
    @IsIntegral.component_integral X _ (U : X.Opens) ⟨⟨x, hxU⟩⟩
  exact MonogenicN1.isJapaneseRing_of_isNagataRing hU

/-- **Stacks Project, Tag 035B (variety case).** A variety over a field is Japanese: it is
locally of finite type over the field, hence Nagata, and it is integral. -/
theorem isJapaneseScheme_of_isVariety (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f] : IsJapaneseScheme X :=
  isJapaneseScheme_of_isNagataScheme X (isNagataScheme_of_locallyOfFiniteType_over_field k f)

/-! ### The normalization of a variety -/

/-- **Stacks Project, Tag 0BXR (1), irreducible case.** The normalization morphism of a variety
over a field is finite. -/
theorem isFinite_normalization_of_isVariety (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsVariety k f]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsFinite (X.normalization hX) :=
  normalization_isFinite X (isJapaneseScheme_of_isVariety k f)

/-- Every open of an integral scheme has finitely many irreducible components: it has at
most one. -/
theorem finite_irreducibleComponents_of_isIntegral (X : Scheme.{u}) [IsIntegral X] :
    ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite := by
  intro U _
  cases isEmpty_or_nonempty U with
  | inl hU =>
      rw [Set.finite_def]
      have : IsEmpty U := hU
      exact ⟨⟨∅, fun C ↦ isEmptyElim (C.2.1.nonempty.some)⟩⟩
  | inr hU =>
      have : Nonempty U := hU
      rw [irreducibleComponents_eq_singleton]
      exact Set.finite_singleton _

/-- **Stacks Project, Tag 0BXR (4), irreducible case, with the detail the source omits.** Let `k`
be a field, let `f : Xbar ⟶ Spec k` be a proper variety over `k` and let `i : X ⟶ Xbar` be a
normal open subscheme of it. Then `X` is an open subscheme of a proper variety over `k` all of
whose rings of sections on affine opens are integrally closed, compatibly with the structure
morphisms.

The model is the normalization `Xbar^ν` of `Xbar`: it is integral, normal, and finite over
`Xbar`, hence proper over `k`; and the normalization morphism is an isomorphism over the normal
open `X`. -/
theorem exists_normal_properVariety_model (k : Type u) [Field k] {X Xbar : Scheme.{u}}
    (f : Xbar ⟶ Spec (.of k)) [IsProperVariety k f] (i : X ⟶ Xbar) [IsOpenImmersion i]
    [IsNormal X] :
    ∃ (Z : Scheme.{u}) (g : Z ⟶ Spec (.of k)) (_ : IsProperVariety k g)
      (_ : ∀ V : Z.affineOpens, IsIntegrallyClosed Γ(Z, V.1)) (j : X ⟶ Z)
      (_ : IsOpenImmersion j), j ≫ g = i ≫ f := by
  have hfin := finite_irreducibleComponents_of_isIntegral Xbar
  set ν := Xbar.normalization hfin with hνdef
  have hνfinite : IsFinite ν := isFinite_normalization_of_isVariety k f hfin
  obtain ⟨j, hj, hjν⟩ :=
    Scheme.exists_isOpenImmersion_normalization_of_isNormal hfin i
  refine ⟨Xbar.normalizationScheme hfin, ν ≫ f, ?_, fun V ↦ ?_, j, hj, ?_⟩
  · exact { }
  · exact (Scheme.isNormalRing_of_isNormal_of_affineOpen _ (Xbar.isNormal_normalizationScheme hfin)
      V).isIntegrallyClosed
  · rw [← Category.assoc, hjν]

end AlgebraicGeometry

end
