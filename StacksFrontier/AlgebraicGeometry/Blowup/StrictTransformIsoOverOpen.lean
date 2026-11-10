module

public import StacksFrontier.AlgebraicGeometry.Blowup.Separation
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformOffExceptional

/-!
# The strict transform over an open avoided by the centre

Let `f : X ⟶ S` be a morphism of schemes, let `I` be a quasi-coherent sheaf of ideals on `S` and
let `U ⊆ S` be an open disjoint from the support of `I`. Then the inverse image of `U` in the
blowup of `S` in `I` avoids the exceptional divisor, so over it the strict transform of `X` is
the plain base change of `X`; in particular, if `f` is an isomorphism over `U`, then the strict
transform is an isomorphism over the inverse image of `U`.

## Main results

* `AlgebraicGeometry.isIso_pullbackSnd_morphismRestrict`: a base change of a morphism which is an
  isomorphism over an open is an isomorphism over the inverse image of that open.
* `AlgebraicGeometry.preimage_le_compl_support_exceptionalIdeal`: the inverse image of an open
  disjoint from the centre avoids the exceptional divisor.
* `AlgebraicGeometry.isIso_strictTransformToBlowUp_morphismRestrict`: the strict transform
  along a `U`-admissible centre of an isomorphism over `U` is an isomorphism over the inverse
  image of `U`.
* `AlgebraicGeometry.isSeparated_strictTransformToBlowUp`,
  `AlgebraicGeometry.locallyOfFiniteType_strictTransformToBlowUp`,
  `AlgebraicGeometry.quasiCompact_strictTransformToBlowUp` and
  `AlgebraicGeometry.quasiSeparated_strictTransformToBlowUp`: the strict transform of a separated
  morphism of finite type is again separated of finite type.

## References

* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 081S](https://stacks.math.columbia.edu/tag/081S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- A base change of a morphism which is an isomorphism over an open subscheme is an isomorphism
over the inverse image of that open. -/
theorem isIso_pullbackSnd_morphismRestrict {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
    (U : S.Opens) [IsIso (f ∣_ U)] : IsIso (pullback.snd f g ∣_ (g ⁻¹ᵁ U)) := by
  have : IsIso (pullback.snd f U.ι) := by
    rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict f U]
    infer_instance
  have : IsIso (pullback.snd f ((g ⁻¹ᵁ U).ι ≫ g)) := by
    rw [← morphismRestrict_ι, ← isIso_comp_left_iff (pullbackLeftPullbackSndIso f U.ι (g ∣_ U)).hom,
      pullbackLeftPullbackSndIso_hom_snd]
    infer_instance
  rw [← isIso_comp_left_iff (pullbackRestrictIsoRestrict (pullback.snd f g) (g ⁻¹ᵁ U)).hom,
    pullbackRestrictIsoRestrict_hom_morphismRestrict,
    ← pullbackLeftPullbackSndIso_hom_snd f g (g ⁻¹ᵁ U).ι]
  infer_instance

/-- The inverse image of an open disjoint from the centre avoids the exceptional divisor. -/
theorem preimage_le_compl_support_exceptionalIdeal {S : Scheme.{u}} (I : S.IdealSheafData)
    {U : S.Opens} (h : Disjoint (U : Set S) (I.support : Set S)) :
    blowUpToBase I ⁻¹ᵁ U ≤ (exceptionalIdeal I).support.compl := by
  have hsupp : ((exceptionalIdeal I).support : Set (blowUp I)) =
      (blowUpToBase I).base ⁻¹' (I.support : Set S) := by
    change ((I.comap (blowUpToBase I)).support : Set (blowUp I)) = _
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  intro y hy
  change y ∉ ((exceptionalIdeal I).support : Set (blowUp I))
  rw [hsupp]
  exact Set.disjoint_left.mp h hy

/-- The inverse image in the base change of an open of the blowup disjoint from the exceptional
divisor lies in the complement of the inverse image of the exceptional divisor. -/
theorem preimage_le_exceptionalComplement {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) {U : S.Opens}
    (h : Disjoint (U : Set S) (I.support : Set S)) :
    pullback.snd f (blowUpToBase I) ⁻¹ᵁ (blowUpToBase I ⁻¹ᵁ U) ≤
      Stacks.StrictTransform.exceptionalComplement f (blowUpToBase I) (exceptionalIdeal I) :=
  fun _ hx ↦ preimage_le_compl_support_exceptionalIdeal I h hx

/-- The strict transform along a `U`-admissible centre of a morphism which is an isomorphism over
`U` is an isomorphism over the inverse image of `U`. -/
theorem isIso_strictTransformToBlowUp_morphismRestrict {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) (U : S.Opens) [IsIso (f ∣_ U)]
    (h : Disjoint (U : Set S) (I.support : Set S)) :
    IsIso (strictTransformToBlowUp f I ∣_ (blowUpToBase I ⁻¹ᵁ U)) := by
  have h1 : IsIso ((Stacks.StrictTransform.ideal f (blowUpToBase I)
      (exceptionalIdeal I)).subschemeι ∣_
      (pullback.snd f (blowUpToBase I) ⁻¹ᵁ (blowUpToBase I ⁻¹ᵁ U))) :=
    Stacks.StrictTransform.isIso_subschemeι_restrict f (blowUpToBase I) (exceptionalIdeal I)
      (preimage_le_exceptionalComplement f I h)
  have h2 : IsIso (pullback.snd f (blowUpToBase I) ∣_ (blowUpToBase I ⁻¹ᵁ U)) :=
    isIso_pullbackSnd_morphismRestrict f (blowUpToBase I) U
  change IsIso (((Stacks.StrictTransform.ideal f (blowUpToBase I)
    (exceptionalIdeal I)).subschemeι ≫ pullback.snd f (blowUpToBase I)) ∣_
      (blowUpToBase I ⁻¹ᵁ U))
  rw [morphismRestrict_comp]
  exact IsIso.comp_isIso' h1 h2

/-- The strict transform of a separated morphism is separated over the blowup. -/
theorem isSeparated_strictTransformToBlowUp {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (I : S.IdealSheafData) : IsSeparated (strictTransformToBlowUp f I) := by
  change IsSeparated ((Stacks.StrictTransform.ideal f (blowUpToBase I)
    (exceptionalIdeal I)).subschemeι ≫ pullback.snd f (blowUpToBase I))
  infer_instance

/-- The strict transform of a morphism locally of finite type is locally of finite type over the
blowup. -/
theorem locallyOfFiniteType_strictTransformToBlowUp {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (I : S.IdealSheafData) :
    LocallyOfFiniteType (strictTransformToBlowUp f I) := by
  change LocallyOfFiniteType ((Stacks.StrictTransform.ideal f (blowUpToBase I)
    (exceptionalIdeal I)).subschemeι ≫ pullback.snd f (blowUpToBase I))
  infer_instance

/-- The strict transform of a quasi-compact morphism is quasi-compact over the blowup. -/
theorem quasiCompact_strictTransformToBlowUp {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
    (I : S.IdealSheafData) : QuasiCompact (strictTransformToBlowUp f I) := by
  change QuasiCompact ((Stacks.StrictTransform.ideal f (blowUpToBase I)
    (exceptionalIdeal I)).subschemeι ≫ pullback.snd f (blowUpToBase I))
  infer_instance

/-- The strict transform of a quasi-separated morphism is quasi-separated over the blowup. -/
theorem quasiSeparated_strictTransformToBlowUp {X S : Scheme.{u}} (f : X ⟶ S) [QuasiSeparated f]
    (I : S.IdealSheafData) : QuasiSeparated (strictTransformToBlowUp f I) := by
  change QuasiSeparated ((Stacks.StrictTransform.ideal f (blowUpToBase I)
    (exceptionalIdeal I)).subschemeι ≫ pullback.snd f (blowUpToBase I))
  infer_instance

end AlgebraicGeometry

end
