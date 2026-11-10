module

public import StacksFrontier.AlgebraicGeometry.Models.BaseChange

/-!
# Morphisms of models from isomorphisms of generic fibres

Let `R` be a discrete valuation ring with fraction field `K`. A morphism `b : X ⟶ X'` of schemes
over `R` which is an isomorphism over the generic fibre induces an isomorphism `X_K ≅ X'_K` of
generic fibres. A model structure on either side then transports to the other, making `b` a
morphism of models (Section 0C2R). This is how the blowups and contractions in the proof of
[Stacks, Tag 0E97] are read as morphisms of models.

## Main results

* `Stacks.Models.genericFiberMapOfHomOver_comp`: functoriality of generic fibres.
* `Stacks.Models.isIso_genericFiberMapOfHomOver_of_isIso_morphismRestrict`: an isomorphism over
  the generic fibre induces an isomorphism of generic fibres.
* `Stacks.Models.exists_isModel_isModelHom_of_isIso_source`: the model structure transported to
  the source.
* `Stacks.Models.exists_isModel_isModelHom_of_isIso_target`: the model structure transported to
  the target.

## References

* [Stacks Project, Section 0C2R](https://stacks.math.columbia.edu/tag/0C2R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The morphism of generic fibres of a composite is the composite. -/
theorem genericFiberMapOfHomOver_comp {X X' X'' : Scheme.{u}} (p : X ⟶ Spec (.of R))
    (p' : X' ⟶ Spec (.of R)) (p'' : X'' ⟶ Spec (.of R)) (b : X ⟶ X') (b' : X' ⟶ X'')
    (h : b ≫ p' = p) (h' : b' ≫ p'' = p') (h'' : (b ≫ b') ≫ p'' = p) :
    genericFiberMapOfHomOver (K := K) p p'' (b ≫ b') h'' =
      genericFiberMapOfHomOver (K := K) p p' b h ≫
        genericFiberMapOfHomOver (K := K) p' p'' b' h' := by
  apply pullback.hom_ext <;> simp [genericFiberMapOfHomOver, pullback.map]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- The morphism of generic fibres of the identity is the identity. -/
theorem genericFiberMapOfHomOver_id {X : Scheme.{u}} (p : X ⟶ Spec (.of R))
    (h : 𝟙 X ≫ p = p) : genericFiberMapOfHomOver (K := K) p p (𝟙 X) h = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [genericFiberMapOfHomOver, pullback.map]

attribute [local instance] genericFiberSpec_isOpenImmersion

/-- **An isomorphism over the generic fibre induces an isomorphism of generic fibres.** If
`b : X ⟶ X'` over `R` restricts to an isomorphism over the preimage of the generic point, then
`X_K ⟶ X'_K` is an isomorphism, the generic fibres being those open subschemes. -/
theorem isIso_genericFiberMapOfHomOver_of_isIso_morphismRestrict {X X' : Scheme.{u}}
    (p : X ⟶ Spec (.of R)) (p' : X' ⟶ Spec (.of R)) (b : X ⟶ X') (h : b ≫ p' = p)
    (hb : IsIso (b ∣_ (p' ⁻¹ᵁ (genericPointInclusion R K).opensRange))) :
    IsIso (genericFiberMapOfHomOver (K := K) p p' b h) := by
  subst h
  let V : X'.Opens := p' ⁻¹ᵁ (genericPointInclusion R K).opensRange
  let eg : pullback p' (genericPointInclusion R K) ≅ V.toScheme :=
    IsOpenImmersion.isoOfRangeEq (pullback.fst p' (genericPointInclusion R K)) V.ι (by
      rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.range_ι])
  let ep : pullback (b ≫ p') (genericPointInclusion R K) ≅ (b ⁻¹ᵁ V).toScheme :=
    IsOpenImmersion.isoOfRangeEq (pullback.fst (b ≫ p') (genericPointInclusion R K))
      (b ⁻¹ᵁ V).ι (by
        rw [IsOpenImmersion.range_pullbackFst, Scheme.Opens.range_ι]
        rfl)
  have hm : genericFiberMapOfHomOver (K := K) (b ≫ p') p' b rfl =
      ep.hom ≫ (b ∣_ V) ≫ eg.inv := by
    rw [← cancel_mono (pullback.fst p' (genericPointInclusion R K))]
    simp only [Category.assoc, eg, ep, IsOpenImmersion.isoOfRangeEq_inv_fac,
      morphismRestrict_ι, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
    exact pullback.lift_fst _ _ _
  rw [hm]
  infer_instance

/-- The morphism of generic fibres commutes with the projections to `Spec K`. -/
private theorem genericFiberMapOfHomOver_comp_snd {R K : Type u} [CommRing R] [Field K]
    [Algebra R K] {X X' : Scheme.{u}} (p : X ⟶ Spec (.of R)) (p' : X' ⟶ Spec (.of R))
    (b : X ⟶ X') (h : b ≫ p' = p) :
    genericFiberMapOfHomOver (K := K) p p' b h ≫ pullback.snd p' (genericPointInclusion R K) =
      pullback.snd p (genericPointInclusion R K) :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- **Transporting a model structure to the source.** Let `(X', p', e')` be a model of `V` and
`b : X ⟶ X'` a morphism with `b ≫ p'` flat, locally of finite type and quasi-compact, inducing an
isomorphism of generic fibres. Then `X` is a model of `V` for which `b` is a morphism of
models. -/
theorem exists_isModel_isModelHom_of_isIso_source {V X X' : Scheme.{u}}
    {v : V ⟶ Spec (.of K)} {p' : X' ⟶ Spec (.of R)}
    {e' : V ≅ pullback p' (genericPointInclusion R K)} (hX' : IsModel v p' e') (b : X ⟶ X')
    [Flat (b ≫ p')] [LocallyOfFiniteType (b ≫ p')] [QuasiCompact (b ≫ p')]
    [IsIso (genericFiberMapOfHomOver (K := K) (b ≫ p') p' b rfl)] :
    ∃ e : V ≅ pullback (b ≫ p') (genericPointInclusion R K),
      IsModel v (b ≫ p') e ∧ IsModelHom (b ≫ p') p' e e' b := by
  let m := genericFiberMapOfHomOver (K := K) (b ≫ p') p' b rfl
  refine ⟨e' ≪≫ (asIso m).symm, ⟨inferInstance, inferInstance, inferInstance, ?_⟩,
    ⟨rfl, by simp [m]⟩⟩
  have hms : inv m ≫ pullback.snd (b ≫ p') (genericPointInclusion R K) =
      pullback.snd p' (genericPointInclusion R K) := by
    rw [IsIso.inv_comp_eq]
    exact (genericFiberMapOfHomOver_comp_snd _ _ _ _).symm
  rw [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, hms]
  exact hX'.2.2.2

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] in
/-- **Transporting a model structure to the target.** Let `(X, p, e)` be a model of `V` and
`b : X ⟶ X'` a morphism over `p' : X' ⟶ Spec R`, with `p'` flat, locally of finite type and
quasi-compact, inducing an isomorphism of generic fibres. Then `X'` is a model of `V` for which
`b` is a morphism of models. -/
theorem exists_isModel_isModelHom_of_isIso_target {V X X' : Scheme.{u}}
    {v : V ⟶ Spec (.of K)} {p : X ⟶ Spec (.of R)} {e : V ≅ pullback p (genericPointInclusion R K)}
    (hX : IsModel v p e) {p' : X' ⟶ Spec (.of R)} (b : X ⟶ X') (h : b ≫ p' = p)
    [Flat p'] [LocallyOfFiniteType p'] [QuasiCompact p']
    [IsIso (genericFiberMapOfHomOver (K := K) p p' b h)] :
    ∃ e' : V ≅ pullback p' (genericPointInclusion R K),
      IsModel v p' e' ∧ IsModelHom p p' e e' b := by
  let m := genericFiberMapOfHomOver (K := K) p p' b h
  refine ⟨e ≪≫ asIso m, ⟨inferInstance, inferInstance, inferInstance, ?_⟩, ⟨h, rfl⟩⟩
  rw [Iso.trans_hom, asIso_hom, Category.assoc, genericFiberMapOfHomOver_comp_snd]
  exact hX.2.2.2

/-- The closed point of `Spec R` is not the generic point: it is not in the image of
`Spec K ⟶ Spec R`. -/
theorem closedPoint_notMem_range_genericPointInclusion :
    IsLocalRing.closedPoint R ∉ Set.range (genericPointInclusion R K).base := by
  rintro ⟨t, ht⟩
  have h : (IsLocalRing.closedPoint R).asIdeal = ⊥ := by
    rw [← ht]
    let t' : PrimeSpectrum K := t
    have ht0 : t'.asIdeal = ⊥ := (Ideal.eq_bot_or_top _).resolve_right t'.isPrime.ne_top
    change Ideal.comap (algebraMap R K) t'.asIdeal = ⊥
    rw [ht0]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  exact IsDiscreteValuationRing.not_a_field R h

/-- A point of `Spec R` other than the closed point is the generic point, the image of
`Spec K ⟶ Spec R`. -/
theorem mem_range_genericPointInclusion_of_ne_closedPoint {s : Spec (.of R)}
    (hs : s ≠ IsLocalRing.closedPoint R) : s ∈ Set.range (genericPointInclusion R K).base := by
  have h0 : s.asIdeal = ⊥ := by
    by_contra h0
    exact hs (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
      (Ring.DimensionLEOne.maximalOfPrime h0 s.isPrime)))
  refine ⟨IsLocalRing.closedPoint K, PrimeSpectrum.ext ?_⟩
  change Ideal.comap (algebraMap R K) (IsLocalRing.maximalIdeal K) = s.asIdeal
  rw [h0, IsLocalRing.maximalIdeal_eq_bot]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)

/-- **An isomorphism of generic fibres is injective over the generic point**: if `b : X ⟶ X'`
over `R` induces an isomorphism `X_K ≅ X'_K`, two points of `X` over the generic point with the
same image under `b` are equal. -/
theorem eq_of_isIso_genericFiberMapOfHomOver {X X' : Scheme.{u}} {p : X ⟶ Spec (.of R)}
    {p' : X' ⟶ Spec (.of R)} {b : X ⟶ X'} (h : b ≫ p' = p)
    [IsIso (genericFiberMapOfHomOver (K := K) p p' b h)] {x₁ x₂ : X}
    (hx : p x₁ ≠ IsLocalRing.closedPoint R) (hb : b x₁ = b x₂) : x₁ = x₂ := by
  have hx₂ : p x₂ = p x₁ := by
    rw [← h, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hb]
  have hr : ∀ x : X, p x ≠ IsLocalRing.closedPoint R →
      x ∈ Set.range (pullback.fst p (genericPointInclusion R K)).base := fun x hx => by
    rw [IsOpenImmersion.range_pullbackFst]
    exact mem_range_genericPointInclusion_of_ne_closedPoint hx
  obtain ⟨y₁, rfl⟩ := hr x₁ hx
  obtain ⟨y₂, rfl⟩ := hr x₂ (hx₂ ▸ hx)
  have hfst : ∀ y, pullback.fst p' (genericPointInclusion R K)
      (genericFiberMapOfHomOver (K := K) p p' b h y) =
        b (pullback.fst p (genericPointInclusion R K) y) := fun y => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
    exact congrArg (fun f : pullback p (genericPointInclusion R K) ⟶ X' => f y)
      (pullback.lift_fst _ _ _)
  have hm : genericFiberMapOfHomOver (K := K) p p' b h y₁ =
      genericFiberMapOfHomOver (K := K) p p' b h y₂ :=
    (pullback.fst p' (genericPointInclusion R K)).isOpenEmbedding.injective
      (by rw [hfst, hfst, hb])
  rw [(ConcreteCategory.bijective_of_isIso
    (Scheme.forgetToTop.map (genericFiberMapOfHomOver (K := K) p p' b h))).1 hm]

end Stacks.Models

end
