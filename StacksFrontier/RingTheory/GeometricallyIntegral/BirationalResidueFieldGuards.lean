module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Examples.Localization
public import StacksFrontier.RingTheory.GeometricallyIntegral.BirationalResidueField

/-!
# Both extremes of the generic-residue-field criterion

`AlgebraicGeometry.birationalOver_iff_generic_residueField_iso` (Stacks 0552, parts (1) and
(3)) is an equivalence, so it carries content only if both of its sides are satisfiable and both
are refutable on pairs meeting its hypotheses. This file pins both extremes down over the base
`Spec ℤ`, with integral schemes locally of finite type over it in every case.

## Main results

* `AlgebraicGeometry.birationalOver_specLocalizationAwayTwo`: `Spec ℤ[1/2]` and `Spec ℤ` are
  birational over `Spec ℤ`. With the criterion this makes its right-hand side satisfiable, which
  is `AlgebraicGeometry.exists_generic_residueField_iso_specLocalizationAwayTwo`.
* `AlgebraicGeometry.notMem_range_specLocalizationAwayTwo`: and that pair is not degenerate —
  the prime `(2)` is not in the image of `Spec ℤ[1/2] → Spec ℤ`, while it is in the image of
  the identity, so the two are not isomorphic over `Spec ℤ`. The criterion is therefore not an
  assertion about isomorphic pairs.
* `AlgebraicGeometry.not_birationalOver_specZModTwo`: `Spec ℤ` and `Spec (ZMod 2)` are *not*
  birational over `Spec ℤ`, so the left-hand side is refutable. This is proved *through* the
  criterion, so its right-hand side is refutable too.

## Implementation notes

`Spec ℤ[1/2] → Spec ℤ` is locally of finite type because the structure map of a localization
away from an element is; `Spec (ZMod 2) → Spec ℤ` is because that map is surjective, hence of
finite type. Both sources are integral: the first because a localization of a domain at a
submonoid of nonzerodivisors is a domain, the second because `ZMod 2` is a field.

The refuting pair is refuted on the *first* conjunct of part (3) of Stacks 0552 — the demand
that the two generic points have the same image in the base — rather than by comparing residue
fields, which would need a field-theoretic non-isomorphism. The generic point of `Spec (ZMod 2)`
lands on `(2)` and that of `Spec ℤ` on `(0)`.

## References

* [Stacks Project, Tag 0552](https://stacks.math.columbia.edu/tag/0552)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

private theorem powers_two_le_nonZeroDivisors :
    Submonoid.powers (2 : ℤ) ≤ nonZeroDivisors ℤ := by
  intro s hs
  obtain ⟨n, rfl⟩ := hs
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n (by norm_num))

/-- `ℤ[1/2]` is a domain, so `Spec ℤ[1/2]` is integral and has a generic point. -/
instance isDomain_localizationAwayTwo : IsDomain (Localization.Away (2 : ℤ)) :=
  Localization.Away.isDomain (by norm_num)

private instance : Finite (irreducibleComponents (Spec (CommRingCat.of ℤ))) := by
  rw [irreducibleComponents_eq_singleton]
  infer_instance

private instance :
    Finite (irreducibleComponents (Spec (CommRingCat.of (Localization.Away (2 : ℤ))))) := by
  rw [irreducibleComponents_eq_singleton]
  infer_instance

/-- `Spec ℤ[1/2]` and `Spec ℤ` are birational over `Spec ℤ`: the localization morphism is
birational by Stacks 01RQ and commutes with the structure morphisms by construction, so Stacks
0BAC applies. -/
theorem birationalOver_specLocalizationAwayTwo :
    Scheme.BirationalOver
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (2 : ℤ)))))
      (𝟙 (Spec (CommRingCat.of ℤ))) := by
  refine birationalOver_of_isBirational _ _
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (2 : ℤ)))))
    ?_ (Category.comp_id _) (Or.inl ⟨inferInstance, inferInstance⟩)
  exact localization_isBirational ℤ (Submonoid.powers (2 : ℤ))
    (fun h => by simpa using powers_two_le_nonZeroDivisors h)

/-- The right-hand side of Stacks 0552 is satisfiable: the generic points of `Spec ℤ[1/2]` and
of `Spec ℤ` have the same image in `Spec ℤ` and isomorphic residue fields over it. -/
theorem exists_generic_residueField_iso_specLocalizationAwayTwo :
    ∃ (h : (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (2 : ℤ)))))
          (genericPoint (Spec (CommRingCat.of (Localization.Away (2 : ℤ))))) =
        (𝟙 (Spec (CommRingCat.of ℤ))) (genericPoint (Spec (CommRingCat.of ℤ))))
      (e : (Spec (CommRingCat.of (Localization.Away (2 : ℤ)))).residueField
            (genericPoint (Spec (CommRingCat.of (Localization.Away (2 : ℤ))))) ≅
          (Spec (CommRingCat.of ℤ)).residueField (genericPoint (Spec (CommRingCat.of ℤ)))),
      h ▸ (Scheme.Hom.residueFieldMap
            (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (2 : ℤ)))))
            (genericPoint (Spec (CommRingCat.of (Localization.Away (2 : ℤ))))) ≫ e.hom) =
        Scheme.Hom.residueFieldMap (𝟙 (Spec (CommRingCat.of ℤ)))
          (genericPoint (Spec (CommRingCat.of ℤ))) :=
  (birationalOver_iff_generic_residueField_iso _ _).mp birationalOver_specLocalizationAwayTwo

/-- The prime `(2)` of `ℤ`, as a point of `Spec ℤ`. -/
def primeTwoInt : PrimeSpectrum ℤ :=
  ⟨Ideal.span {(2 : ℤ)}, (Ideal.span_singleton_prime (by norm_num)).mpr Int.prime_two⟩

/-- The birational pair above is not a pair of schemes isomorphic over the base: the prime `(2)`
is not in the image of `Spec ℤ[1/2] → Spec ℤ`, because `2` becomes a unit and a prime ideal
contains no unit, whereas it is in the image of `𝟙`. So
`AlgebraicGeometry.birationalOver_iff_generic_residueField_iso` is not an assertion about
isomorphic pairs. -/
theorem notMem_range_specLocalizationAwayTwo :
    primeTwoInt ∉ Set.range
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (2 : ℤ))))) := by
  rintro ⟨p, hp⟩
  have h2 : (2 : ℤ) ∈ primeTwoInt.asIdeal := Ideal.mem_span_singleton_self _
  rw [← hp] at h2
  have hmem : algebraMap ℤ (Localization.Away (2 : ℤ)) 2 ∈ p.asIdeal := h2
  exact p.isPrime.ne_top
    (p.asIdeal.eq_top_of_isUnit_mem hmem (IsLocalization.Away.algebraMap_isUnit (2 : ℤ)))

/-- The generic point of `Spec (ZMod 2)` lands on a prime of `ℤ` containing `2`. -/
private theorem two_mem_image_genericPoint_specZModTwo :
    (2 : ℤ) ∈ ((Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 2))))
      (genericPoint (Spec (CommRingCat.of (ZMod 2))))).asIdeal := by
  rw [genericPoint_eq_bot_of_affine]
  change (2 : ℤ) ∈ (PrimeSpectrum.comap (algebraMap ℤ (ZMod 2)) ⊥).asIdeal
  rw [PrimeSpectrum.comap_asIdeal]
  change ((2 : ℤ) : ZMod 2) ∈ (⊥ : Ideal (ZMod 2))
  simpa using (by decide : ((2 : ℤ) : ZMod 2) = 0)

private instance : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 2)))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  refine RingHom.FiniteType.of_surjective _ (fun x => ?_)
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective (show ZMod 2 from x)
  exact ⟨n, hn⟩

/-- The left-hand side of Stacks 0552 is refutable: `Spec ℤ` and `Spec (ZMod 2)` are integral and
locally of finite type over `Spec ℤ`, and they are not birational over it.

The proof runs through `AlgebraicGeometry.birationalOver_iff_generic_residueField_iso` and
refutes the first conjunct of part (3): the generic point of `Spec ℤ` has image `(0)` and that of
`Spec (ZMod 2)` has image `(2)`. So the right-hand side of the criterion is refutable too. -/
theorem not_birationalOver_specZModTwo :
    ¬ Scheme.BirationalOver (𝟙 (Spec (CommRingCat.of ℤ)))
      (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ZMod 2)))) := by
  intro hbir
  obtain ⟨h, -, -⟩ := (birationalOver_iff_generic_residueField_iso _ _).mp hbir
  have h2 : (2 : ℤ) ∈ ((𝟙 (Spec (CommRingCat.of ℤ)))
      (genericPoint (Spec (CommRingCat.of ℤ)))).asIdeal := by
    rw [h]
    exact two_mem_image_genericPoint_specZModTwo
  rw [show (𝟙 (Spec (CommRingCat.of ℤ))) (genericPoint (Spec (CommRingCat.of ℤ))) =
      genericPoint (Spec (CommRingCat.of ℤ)) from rfl,
    genericPoint_eq_bot_of_affine] at h2
  simp at h2

end AlgebraicGeometry

end
