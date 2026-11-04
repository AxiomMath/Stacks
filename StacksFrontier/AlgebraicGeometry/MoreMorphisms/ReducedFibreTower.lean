module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreNormalizationTransport
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.IntegralClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Composition

/-!
# The normalized base change of a normalized base change

Let `A ⟶ B₀ ⟶ B₁` be a tower of Noetherian rings with `B₀` Nagata and `Spec B₁ ⟶ Spec B₀`
universally open, and let `f : X ⟶ Spec A` be quasi-compact and locally of finite type.  Write
`W₀ = X ×_{Spec A} Spec B₀` and let `Y₀ = W₀^ν` be its normalization.  **Then the normalization
of `Y₀ ×_{Spec B₀} Spec B₁` is the normalization of `X ×_{Spec A} Spec B₁`, by an isomorphism
over `Spec B₁`.**

This is the composition of the two finite extensions in the proof of the reduced fibre theorem:
its first paragraph replaces `A` by `B₀` and `X` by `Y₀`, its last paragraph produces a further
extension `B₁` and asserts smoothness of the normalization of `Y₀ ×_{Spec B₀} Spec B₁`, while the
statement of the theorem is about the normalization of `X ×_{Spec A} Spec B₁`.  The isomorphism
below is over `Spec B₁`, so it carries smoothness at a point of either scheme to smoothness at
the corresponding point of the other.

The comparison of iterated normalized base changes, in `AlgebraicGeometry.NormalizedBaseChange`,
`exists_normalizationScheme_iso_baseChangeMap_normalization_of_isNoetherianRing`, asks the scheme
being normalized to be **reduced** — the base change of its normalization morphism is birational
only then — and `W₀` is not, `X` being arbitrary.  The argument therefore runs over the reduction
`W₀_red`, whose normalization is that of `W₀`, and transports the result back along
`AlgebraicGeometry.Scheme.exists_normalizationScheme_iso_of_surjective`: the base change of
`W₀_red ⟶ W₀` is again a surjective closed immersion, and a surjective closed immersion does not
change the normalization.

## Main results

* `AlgebraicGeometry.exists_normalizationScheme_iso_normalization_pullback_tower`: the
  normalization of `X ×_{Spec A} Spec B₁` is the normalization of `Y₀ ×_{Spec B₀} Spec B₁`, over
  `Spec B₁`.

## Implementation notes

The base change of `X` to `Spec B₁` is written as the pullback along the *composite*
`Spec B₁ ⟶ Spec B₀ ⟶ Spec A` rather than along `Spec.map` of `algebraMap A B₁`: the two agree
under `IsScalarTower A B₀ B₁`, but keeping the composite avoids rewriting a morphism inside a
pullback, which no `IsScalarTower` instance makes definitional.

Every finiteness-of-irreducible-components hypothesis is a proposition, so the normalizations
named with different such proofs are the same type and the isomorphisms compose without
transport.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 09IK](https://stacks.math.columbia.edu/tag/09IK)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {A B₀ B₁ : Type u} [CommRing A] [CommRing B₀] [CommRing B₁] [IsNoetherianRing B₀]
  [IsNoetherianRing B₁] [Algebra A B₀] [Algebra B₀ B₁]

omit [Algebra A B₀] in
/-- **Taking the normalized base change twice along a tower is taking it once.**  Let
`A ⟶ B₀ ⟶ B₁` be a tower of rings with `B₀` and `B₁` Noetherian, `B₀` Nagata and
`Spec B₁ ⟶ Spec B₀` universally open, and let `f : X ⟶ Spec A` be quasi-compact and locally of
finite type.  Write `W₀ = X ×_{Spec A} Spec B₀`, let `Y₀` be its normalization and let
`r₀ : Y₀ ⟶ Spec B₀` be the structure morphism.  Then the normalization of
`X ×_{Spec A} Spec B₁` and the normalization of `Y₀ ×_{Spec B₀} Spec B₁` are isomorphic over
`Spec B₁`.

The reduction `W₀_red` has the same normalization as `W₀`, is reduced, and is still
quasi-compact and locally of finite type over `Spec B₀` with finite normalization, `B₀` being
Nagata; so the comparison of iterated normalized base changes applies to it and identifies the
normalization of `W₀_red ×_{Spec B₀} Spec B₁` with that of `Y₀ ×_{Spec B₀} Spec B₁`.  The base
change of `W₀_red ⟶ W₀` is a surjective closed immersion, which does not change the
normalization, and `(X ×_{Spec A} Spec B₀) ×_{Spec B₀} Spec B₁` is `X ×_{Spec A} Spec B₁`. -/
theorem exists_normalizationScheme_iso_normalization_pullback_tower (hB₀ : IsNagataRing B₀)
    [UniversallyOpen (Spec.map (CommRingCat.ofHom (algebraMap B₀ B₁)))]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] [QuasiCompact f]
    (g₀ : Spec (.of B₀) ⟶ Spec (.of A))
    (hW₀ : ∀ U : (pullback f g₀ : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback f g₀ : Scheme.{u})) → (irreducibleComponents U).Finite)
    (hV : ∀ U : (pullback ((pullback f g₀ : Scheme.{u}).normalization hW₀ ≫
          pullback.snd f g₀) (Spec.map (CommRingCat.ofHom (algebraMap B₀ B₁)))
            : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback ((pullback f g₀ : Scheme.{u}).normalization hW₀ ≫
        pullback.snd f g₀) (Spec.map (CommRingCat.ofHom (algebraMap B₀ B₁)))
          : Scheme.{u})) → (irreducibleComponents U).Finite)
    (hW₁ : ∀ U : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap B₀ B₁)) ≫ g₀)
        : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback f (Spec.map (CommRingCat.ofHom (algebraMap B₀ B₁)) ≫ g₀)
        : Scheme.{u})) → (irreducibleComponents U).Finite) :
    ∃ e : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap B₀ B₁)) ≫ g₀)
          : Scheme.{u}).normalizationScheme hW₁ ≅
        (pullback ((pullback f g₀ : Scheme.{u}).normalization hW₀ ≫ pullback.snd f g₀)
          (Spec.map (CommRingCat.ofHom (algebraMap B₀ B₁)))
            : Scheme.{u}).normalizationScheme hV,
      e.hom ≫ (pullback ((pullback f g₀ : Scheme.{u}).normalization hW₀ ≫
            pullback.snd f g₀) (Spec.map (CommRingCat.ofHom (algebraMap B₀ B₁)))
              : Scheme.{u}).normalization hV ≫
          pullback.snd ((pullback f g₀ : Scheme.{u}).normalization hW₀ ≫
            pullback.snd f g₀) (Spec.map (CommRingCat.ofHom (algebraMap B₀ B₁))) =
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap B₀ B₁)) ≫ g₀)
          : Scheme.{u}).normalization hW₁ ≫
          pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap B₀ B₁)) ≫ g₀) := by
  set h := Spec.map (CommRingCat.ofHom (algebraMap B₀ B₁)) with hhdef
  set W₀ := (pullback f g₀ : Scheme.{u}) with hW₀def
  set q₀ : W₀ ⟶ Spec (.of B₀) := pullback.snd f g₀ with hq₀def
  -- the reduction of `W₀` is reduced, and surjects onto `W₀`
  have hRred : IsReduced W₀.nilradical.subscheme := by
    simpa only [Scheme.IdealSheafData.vanishingIdeal_top] using
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (X := W₀) ⊤
  have hRsurj : Surjective W₀.nilradical.subschemeι := ⟨fun x ↦
    Set.mem_range.mp (by rw [W₀.nilradical.range_subschemeι, Scheme.support_nilradical]; trivial)⟩
  have _ := hRred
  have _ := hRsurj
  -- the normalization of `W₀` is the normalization of its reduction
  obtain ⟨dR, hdR⟩ := Scheme.exists_normalizationScheme_iso_of_surjective
    W₀.nilradical.subschemeι (W₀.finite_irreducibleComponents_reduction hW₀) hW₀
  set r₀ : W₀.normalizationScheme hW₀ ⟶ Spec (.of B₀) :=
    W₀.normalization hW₀ ≫ q₀ with hr₀def
  -- the two base changes along `h`
  have hsqV : IsPullback (pullback.fst r₀ h ≫ dR.hom) (pullback.snd r₀ h)
      (W₀.nilradical.subscheme.normalization (W₀.finite_irreducibleComponents_reduction hW₀) ≫
        W₀.nilradical.subschemeι ≫ q₀) h := by
    refine (IsPullback.of_hasPullback r₀ h).of_iso (Iso.refl _) dR (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) ?_ (by simp)
    rw [Iso.refl_hom, Category.comp_id, hr₀def, ← hdR]
    simp
  have hsqW : IsPullback (pullback.fst (W₀.nilradical.subschemeι ≫ q₀) h)
      (pullback.snd (W₀.nilradical.subschemeι ≫ q₀) h)
      (W₀.nilradical.subschemeι ≫ q₀) h := IsPullback.of_hasPullback _ _
  -- the reduction is of finite type over the Nagata base, so its normalization is finite
  have _ : LocallyOfFiniteType (W₀.nilradical.subschemeι ≫ q₀) := inferInstance
  have _ : QuasiCompact (W₀.nilradical.subschemeι ≫ q₀) := inferInstance
  have hfinR : IsFinite (W₀.nilradical.subscheme.normalization
      (W₀.finite_irreducibleComponents_reduction hW₀)) :=
    Scheme.isFinite_normalization
      (isNagataScheme_of_isNagataRing (W₀.nilradical.subschemeι ≫ q₀) hB₀) _
  -- the two projections are open
  have hopenW : UniversallyOpen (pullback.fst (W₀.nilradical.subschemeι ≫ q₀) h) :=
    MorphismProperty.of_isPullback (P := @UniversallyOpen) hsqW.flip inferInstance
  have hopenV : UniversallyOpen (pullback.fst r₀ h) :=
    MorphismProperty.of_isPullback (P := @UniversallyOpen)
      (IsPullback.of_hasPullback r₀ h).flip inferInstance
  have _ := hopenV
  have _ := hopenW
  have _ : UniversallyOpen (pullback.fst r₀ h ≫ dR.hom) := inferInstance
  -- the comparison of iterated normalized base changes, on the reduction
  obtain ⟨g, e₃, hg, he₃⟩ :=
    open NormalizedBaseChange in
    exists_normalizationScheme_iso_baseChangeMap_normalization_of_isNoetherianRing
      (W₀.nilradical.subschemeι ≫ q₀) (W₀.finite_irreducibleComponents_reduction hW₀) hfinR
      hsqV hsqW (pullback.fst (W₀.nilradical.subschemeι ≫ q₀) h).isOpenMap
      (pullback.fst r₀ h ≫ dR.hom).isOpenMap
  -- the base change of the reduction morphism is a surjective closed immersion
  have hbcmpb := NormalizedBaseChange.isPullback_baseChangeMap hsqW
    (IsPullback.of_hasPullback q₀ h)
  have _ : IsClosedImmersion
      (NormalizedBaseChange.baseChangeMap hsqW (IsPullback.of_hasPullback q₀ h)) :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hbcmpb.flip inferInstance
  have _ : Surjective
      (NormalizedBaseChange.baseChangeMap hsqW (IsPullback.of_hasPullback q₀ h)) :=
    MorphismProperty.of_isPullback (P := @Surjective) hbcmpb.flip inferInstance
  have hfinW' : ∀ U : (pullback (W₀.nilradical.subschemeι ≫ q₀) h : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback (W₀.nilradical.subschemeι ≫ q₀) h : Scheme.{u})) →
        (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_isCompact_of_locallyOfFiniteType
      (pullback.snd (W₀.nilradical.subschemeι ≫ q₀) h)
  have hfinW₀' : ∀ U : (pullback q₀ h : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback q₀ h : Scheme.{u})) → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_isCompact_of_locallyOfFiniteType (pullback.snd q₀ h)
  obtain ⟨e₂, he₂⟩ := Scheme.exists_normalizationScheme_iso_of_surjective
    (NormalizedBaseChange.baseChangeMap hsqW (IsPullback.of_hasPullback q₀ h)) hfinW' hfinW₀'
  -- `(X ×_A B₀) ×_{B₀} B₁ = X ×_A B₁`
  obtain ⟨d₁, hd₁⟩ := Scheme.exists_normalizationScheme_iso_of_iso
    (pullbackLeftPullbackSndIso f g₀ h) hfinW₀' hW₁
  refine ⟨d₁.symm ≪≫ e₂ ≪≫ e₃, ?_⟩
  -- the three comparisons, each read against the structure morphism to `Spec B₁`
  have comp : ∀ {P Q R S T : Scheme.{u}} (e : P ⟶ Q) (n : Q ⟶ R) (n' : P ⟶ S) (φ : R ⟶ S)
      (s : S ⟶ T) (s' : R ⟶ T), (e ≫ n) ≫ φ = n' → φ ≫ s = s' → e ≫ n ≫ s' = n' ≫ s := by
    rintro _ _ _ _ _ _ _ _ _ _ _ rfl rfl
    simp
  have key₃ := comp e₃.hom ((pullback r₀ h).normalization hV) _ _ _ _ (by rw [he₃, hg])
    (NormalizedBaseChange.baseChangeMap_comp_snd hsqV hsqW)
  have key₂ := comp e₂.hom ((pullback (W₀.nilradical.subschemeι ≫ q₀) h).normalization hfinW')
    _ _ _ _ (by rw [Category.assoc, he₂])
    (NormalizedBaseChange.baseChangeMap_comp_snd hsqW (IsPullback.of_hasPullback q₀ h))
  have key₁ := comp d₁.inv ((pullback q₀ h).normalization hfinW₀') _ _ _ _
    (by rw [Category.assoc, ← hd₁, Iso.inv_hom_id_assoc])
    (pullbackLeftPullbackSndIso_hom_snd f g₀ h)
  calc (d₁.symm ≪≫ e₂ ≪≫ e₃).hom ≫ (pullback r₀ h : Scheme.{u}).normalization hV ≫
        pullback.snd r₀ h
      = d₁.inv ≫ e₂.hom ≫ (e₃.hom ≫ (pullback r₀ h : Scheme.{u}).normalization hV ≫
        pullback.snd r₀ h) := by simp
    _ = (pullback f (h ≫ g₀) : Scheme.{u}).normalization hW₁ ≫ pullback.snd f (h ≫ g₀) := by
        rw [key₃, key₂, key₁]

end AlgebraicGeometry

end
