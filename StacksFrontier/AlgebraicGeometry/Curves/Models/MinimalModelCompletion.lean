module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModel
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.RegularNodalModel
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Models.GenericFibreModelHom
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.Descent.SchemeProperty.Regular
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.StalkBaseChange
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.DiscreteValuationRing.EppCompletionInput
public import StacksFrontier.AlgebraicGeometry.FiberCotangentIdentification.Kaehler
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwists
public import StacksFrontier.AlgebraicGeometry.Picard.GaloisDescent.Pullback
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Curves.Models.MinimalModelNumericalType
public import StacksFrontier.AlgebraicGeometry.Curves.Models.PicardSequence
public import StacksFrontier.AlgebraicGeometry.NodalContraction.Basic

/-!
# The minimal model after completion of the discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `K`, `R^` its completion and `K^` the
fraction field of `R^`. Let `C` be a smooth projective curve over `K` with `H⁰(C, 𝒪_C) = K` and
`Y ⟶ Spec R` a minimal model of `C` ([Stacks, Tag 0C2V]). Then `Y ×_R R^ ⟶ Spec R^` is a minimal
model of `C ×_K K^`:

* it is a proper model of `C_{K^}`, with generic fibre the base change of that of `Y`;
* it is regular: at a point over the closed point of `Spec R^` its local ring has the completion
  of the local ring of `Y` ([Stacks, Tag 0BG5]), and a Noetherian local ring is regular exactly
  when its completion is; at a point over the generic point it is a point of the smooth curve
  `C_{K^}`;
* it has no exceptional curve of the first kind, because an exceptional curve lies in the special
  fibre, which is the special fibre of `Y`, and is an exceptional curve of `Y` there.

## Main results

* `Stacks.Models.isPullback_baseChange_adicCompletion`: the generic fibre of `Y ×_R R^` is
  `C ×_K K^`.
* `Stacks.Models.isRegular_pullback_adicCompletion`: `Y ×_R R^` is regular.
* `Stacks.Models.isMinimalModel_pullback_adicCompletion`: it is a minimal model of `C_{K^}`.

## References

* [Stacks Project, Tag 0C2V](https://stacks.math.columbia.edu/tag/0C2V)
* [Stacks Project, Tag 0BG5](https://stacks.math.columbia.edu/tag/0BG5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- **An exceptional curve of the first kind descends along a flat morphism inducing an
isomorphism of the curves.** Let `j : Y ⟶ X` be flat and `D` an effective Cartier divisor on `X`
such that the subscheme cut out by `D.comap j` maps isomorphically onto the subscheme cut out by
`D`. If `D.comap j` is an exceptional curve of the first kind presented by `e'`, then so is `D`,
presented by `e'` followed by that isomorphism: the class of `𝒪_X(D)` pulls back along the flat
`j` to that of `𝒪_Y(j⁻¹D)` ([Stacks, Tag 0C4U]), so both restrict to the same class on the
curve. -/
theorem IsExceptionalCurveOfFirstKind.of_comap_of_flat {X Y : Scheme.{u}} (j : Y ⟶ X) [Flat j]
    (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D]
    (φ : (D.comap j).subscheme ⟶ D.subscheme) [IsIso φ]
    (hφ : φ ≫ D.subschemeι = (D.comap j).subschemeι ≫ j) {k : Type u} [Field k]
    {e' : projectiveLineProj k ≅ (D.comap j).subscheme}
    (hE : (D.comap j).IsExceptionalCurveOfFirstKind k e') :
    D.IsExceptionalCurveOfFirstKind k (e' ≪≫ asIso φ) := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor (D.comap j) :=
    Stacks.Divisors.isPullbackDefined_of_flat j D inferInstance
  rw [isExceptionalCurveOfFirstKind_iff_pullbackPicardClass]
  have h := hE.pullbackPicardClass_invertibleSheaf
  rw [← schemePullbackClass_picardClass j D] at h
  have hcomp : e'.hom ≫ (D.comap j).subschemeι ≫ j = (e' ≪≫ asIso φ).hom ≫ D.subschemeι := by
    rw [Iso.trans_hom, asIso_hom, Category.assoc, hφ]
  refine Eq.trans ?_ h
  show Stacks.Picard.schemePullbackClass _ (Stacks.Picard.schemePullbackClass _ _) =
    Stacks.Picard.schemePullbackClass _ (Stacks.Picard.schemePullbackClass _
      (Stacks.Picard.schemePullbackClass j _))
  rw [Stacks.Picard.schemePullbackClass_comp, Stacks.Picard.schemePullbackClass_comp,
    Stacks.Picard.schemePullbackClass_comp, ← hcomp, Category.assoc]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace Stacks.Models

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The completion `R^` of `R`. -/
local notation "𝓡" => AdicCompletion (IsLocalRing.maximalIdeal R) R
/-- The fraction field `K^` of `R^`. -/
local notation "𝓚" => IsDiscreteValuationRing.AdicCompletionFractionField R
/-- `Spec K ⟶ Spec R`. -/
local notation "gR" => Spec.map (CommRingCat.ofHom (algebraMap R K))
/-- `Spec K^ ⟶ Spec K`. -/
local notation "gK" => Spec.map (CommRingCat.ofHom (algebraMap K 𝓚))
/-- `Spec R^ ⟶ Spec R`. -/
local notation "gΛ" => Spec.map (CommRingCat.ofHom (algebraMap R 𝓡))
/-- `Spec K^ ⟶ Spec R^`. -/
local notation "gΛK" => Spec.map (CommRingCat.ofHom (algebraMap 𝓡 𝓚))

/-- The fraction field `K^` of the completion `R^`, as a `K`-algebra. -/
local instance : Algebra K 𝓚 :=
  IsDiscreteValuationRing.algebraAdicCompletionFractionField R K

/-- The maps `R ⟶ K ⟶ K^` and `R ⟶ R^ ⟶ K^` agree. -/
local instance : IsScalarTower R K 𝓚 :=
  IsDiscreteValuationRing.isScalarTower_adicCompletionFractionField R K

/-- The two ways from `Spec K^` to `Spec R` agree: through `Spec K` and through `Spec R^`. -/
theorem spec_map_algebraMap_comp_adicCompletion :
    (gK) ≫ (gR) = (gΛK) ≫ (gΛ) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

/-- **The generic fibre of the base change of a model to the completion.** If `C ≅ Y_K` is the
generic fibre of `q : Y ⟶ Spec R`, then `C ×_K K^` is the generic fibre of
`Y ×_R R^ ⟶ Spec R^`: the square
`C_{K^} ⟶ Y ×_R R^`, `C_{K^} ⟶ Spec K^`, over `Spec K^ ⟶ Spec R^` is cartesian. -/
theorem isPullback_baseChange_adicCompletion {C Y : Scheme.{u}} (c : C ⟶ Spec (.of K))
    {q : Y ⟶ Spec (.of R)} {eY : C ≅ pullback q (gR)}
    (he : eY.hom ≫ pullback.snd q (gR) = c) :
    ∃ l : pullback c (gK) ⟶ pullback q (gΛ),
      IsPullback l (pullback.snd c (gK)) (pullback.snd q (gΛ)) (gΛK) := by
  have hcart : IsPullback (eY.hom ≫ pullback.fst q (gR)) c q (gR) :=
    IsPullback.of_iso_pullback ⟨by rw [Category.assoc, pullback.condition, ← he,
      Category.assoc]⟩ eY rfl he
  have hbig : IsPullback (pullback.fst c (gK) ≫ eY.hom ≫ pullback.fst q (gR))
      (pullback.snd c (gK)) q ((gΛK) ≫ (gΛ)) := by
    rw [← spec_map_algebraMap_comp_adicCompletion (R := R) (K := K)]
    exact (IsPullback.of_hasPullback c (gK)).paste_horiz hcart
  have hright : IsPullback (pullback.fst q (gΛ)) (pullback.snd q (gΛ)) q (gΛ) :=
    IsPullback.of_hasPullback q (gΛ)
  refine ⟨hright.lift (pullback.fst c (gK) ≫ eY.hom ≫ pullback.fst q (gR))
    (pullback.snd c (gK) ≫ (gΛK)) (by rw [hbig.w, Category.assoc]), ?_⟩
  exact IsPullback.of_right (by rwa [hright.lift_fst]) (hright.lift_snd _ _ _) hright

/-- The maximal ideal of `R^` is `𝔪 R^`. -/
private theorem map_maximalIdeal_adicCompletion :
    (maximalIdeal R).map (algebraMap R 𝓡) = maximalIdeal 𝓡 :=
  (AdicCompletion.maximalIdeal_eq_map (R := R)).symm

/-- A prime ideal of the quotient of a local ring by an ideal containing its maximal ideal pulls
back to the maximal ideal. -/
private theorem comap_algebraMap_quotient_eq_maximalIdeal {A : Type*} [CommRing A] [IsLocalRing A]
    {I : Ideal A} (hI : maximalIdeal A ≤ I) (P : Ideal (A ⧸ I)) (hP : P.IsPrime) :
    P.comap (algebraMap A (A ⧸ I)) = maximalIdeal A := by
  refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _ hP.ne_top)) ?_
  intro x hx
  rw [Ideal.mem_comap, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.2 (hI hx)]
  exact P.zero_mem

/-- **Completion does not change the residue ring of the maximal ideal**: the map
`R ⧸ 𝔪 ⟶ R^ ⧸ 𝔪 R^` is bijective. It is a map out of a field, and it is surjective because the
maximal ideal of `R^` is `𝔪 R^` and completion does not change the residue field. -/
theorem bijective_algebraMap_quotient_adicCompletion :
    Function.Bijective (algebraMap (R ⧸ maximalIdeal R)
      (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡))) := by
  have hm := map_maximalIdeal_adicCompletion (R := R)
  have : Nontrivial (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡)) := by
    rw [hm]
    infer_instance
  let := Ideal.Quotient.field (maximalIdeal R)
  refine ⟨RingHom.injective _, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨r, hr⟩ := IsDiscreteValuationRing.surjective_algebraMap_residueField_adicCompletion R
    (IsLocalRing.residue 𝓡 x)
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
  refine ⟨Ideal.Quotient.mk _ r, ?_⟩
  rw [IsLocalRing.ResidueField.algebraMap_residue] at hr
  rwa [Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.eq, hm,
    ← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]

/-- The closed point of `Spec R` pulls back to the closed point of `Spec R^`: the square of
spectra of `R ⟶ R ⧸ 𝔪`, `R ⟶ R^` and `R^ ⟶ R^ ⧸ 𝔪 R^` is cartesian, `R^ ⧸ 𝔪 R^` being the base
change `(R ⧸ 𝔪) ⊗_R R^`. -/
theorem isPullback_spec_quotient_adicCompletion :
    IsPullback (Spec.map (CommRingCat.ofHom (algebraMap (R ⧸ maximalIdeal R)
        (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡)))))
      (Spec.map (CommRingCat.ofHom (algebraMap 𝓡 (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡)))))
      (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ maximalIdeal R)))) (gΛ) := by
  have := Stacks.FiberCotangentIdentification.isPushout_quotient (A := R) (B := 𝓡)
    (maximalIdeal R)
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout R
    (R ⧸ maximalIdeal R) 𝓡 (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡)))

/-- The map `Spec (R^ ⧸ 𝔪 R^) ⟶ Spec (R ⧸ 𝔪)` is an isomorphism. -/
instance isIso_spec_map_quotient_adicCompletion :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap (R ⧸ maximalIdeal R)
      (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡))))) := by
  have : IsIso (CommRingCat.ofHom (algebraMap (R ⧸ maximalIdeal R)
      (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡)))) :=
    (ConcreteCategory.isIso_iff_bijective _).2 bijective_algebraMap_quotient_adicCompletion
  infer_instance

/-- **Base change to the completion does not change a scheme over the closed point.** If
`t : Z ⟶ Spec R` factors through `Spec (R ⧸ 𝔪)`, then the projection
`Z ×_R R^ ⟶ Z` is an isomorphism: `(R ⧸ 𝔪) ⊗_R R^ = R^ ⧸ 𝔪 R^ = R ⧸ 𝔪`. -/
theorem isIso_pullback_fst_adicCompletion_of_factors {Z : Scheme.{u}} (t : Z ⟶ Spec (.of R))
    (t' : Z ⟶ Spec (.of (R ⧸ maximalIdeal R)))
    (ht : t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ maximalIdeal R))) = t) :
    IsIso (pullback.fst t (gΛ)) := by
  have htop := IsPullback.of_hasPullback t' (Spec.map (CommRingCat.ofHom
    (algebraMap (R ⧸ maximalIdeal R) (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡)))))
  have hbig := htop.paste_vert isPullback_spec_quotient_adicCompletion
  rw [ht] at hbig
  have : pullback.fst t (gΛ) = hbig.isoPullback.inv ≫ pullback.fst _ _ := by
    rw [Iso.eq_inv_comp, IsPullback.isoPullback_hom_fst]
  rw [this]
  infer_instance

/-- The point of `Spec (R^ ⧸ 𝔪 R^)` lies over the closed point of `Spec R^`. -/
theorem spec_map_quotient_adicCompletion_apply
    (p : Spec (.of (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡)))) :
    Spec.map (CommRingCat.ofHom (algebraMap 𝓡 (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡)))) p =
      closedPoint 𝓡 := by
  exact PrimeSpectrum.ext (comap_algebraMap_quotient_eq_maximalIdeal
    map_maximalIdeal_adicCompletion.ge p.asIdeal p.isPrime)

/-- **The closed fibre of `Y ×_R R^` is the closed fibre of `Y`**: the closed fibre of
`Y ×_R R^`, mapped to `Y` and to `Spec (R ⧸ 𝔪)`, is the fibre product of `Y` with the closed point
`Spec (R ⧸ 𝔪) ⟶ Spec R`. -/
theorem isPullback_closedFibre_adicCompletion {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R)) :
    IsPullback (pullback.fst (pullback.snd q (gΛ)) (Spec.map (CommRingCat.ofHom
        (algebraMap 𝓡 (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡))))) ≫ pullback.fst q (gΛ))
      (pullback.snd (pullback.snd q (gΛ)) (Spec.map (CommRingCat.ofHom
        (algebraMap 𝓡 (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡))))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (R ⧸ maximalIdeal R)
          (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡)))))
      q (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ maximalIdeal R)))) := by
  have h₁ := IsPullback.of_hasPullback (pullback.snd q (gΛ)) (Spec.map (CommRingCat.ofHom
      (algebraMap 𝓡 (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡)))))
  have hbig := h₁.paste_horiz (IsPullback.of_hasPullback q (gΛ))
  rw [← isPullback_spec_quotient_adicCompletion.w] at hbig
  exact IsPullback.of_iso hbig (Iso.refl _) (Iso.refl _) (asIso (Spec.map (CommRingCat.ofHom
    (algebraMap (R ⧸ maximalIdeal R) (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡)))))) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

/-- The closed fibre of `Y ×_R R^` maps to `Y` by a closed immersion, the base change of the
closed point `Spec (R ⧸ 𝔪) ⟶ Spec R`. -/
theorem isClosedImmersion_closedFibre_adicCompletion {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R)) :
    IsClosedImmersion (pullback.fst (pullback.snd q (gΛ)) (Spec.map (CommRingCat.ofHom
      (algebraMap 𝓡 (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡))))) ≫ pullback.fst q (gΛ)) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ maximalIdeal R)))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact MorphismProperty.of_isPullback (isPullback_closedFibre_adicCompletion q).flip
    inferInstance

/-- Every point of `Y ×_R R^` over the closed point of `Spec R^` lies in its closed fibre. -/
theorem exists_closedFibre_lift_adicCompletion {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R))
    (y : (pullback q (gΛ) : Scheme.{u})) (hy : pullback.snd q (gΛ) y = closedPoint 𝓡) :
    ∃ a, pullback.fst (pullback.snd q (gΛ)) (Spec.map (CommRingCat.ofHom
      (algebraMap 𝓡 (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡))))) a = y := by
  have : Nontrivial (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡)) := by
    rw [map_maximalIdeal_adicCompletion (R := R)]
    infer_instance
  obtain ⟨p₀⟩ : Nonempty (Spec (.of (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡)))) :=
    inferInstance
  obtain ⟨a, ha, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := pullback.snd q (gΛ))
    (g := Spec.map (CommRingCat.ofHom (algebraMap 𝓡 (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡)))))
    y p₀ (hy.trans (spec_map_quotient_adicCompletion_apply p₀).symm)
  exact ⟨a, ha⟩

/-- Two points of `Y ×_R R^` over the closed point of `Spec R^` with the same image in `Y` are
equal. -/
theorem eq_of_base_fst_eq_of_closedPoint {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R))
    {y₁ y₂ : (pullback q (gΛ) : Scheme.{u})} (h₁ : pullback.snd q (gΛ) y₁ = closedPoint 𝓡)
    (h₂ : pullback.snd q (gΛ) y₂ = closedPoint 𝓡)
    (h : pullback.fst q (gΛ) y₁ = pullback.fst q (gΛ) y₂) : y₁ = y₂ := by
  obtain ⟨a₁, rfl⟩ := exists_closedFibre_lift_adicCompletion q y₁ h₁
  obtain ⟨a₂, rfl⟩ := exists_closedFibre_lift_adicCompletion q y₂ h₂
  set b := Spec.map (CommRingCat.ofHom
    (algebraMap 𝓡 (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡))))
  have := isClosedImmersion_closedFibre_adicCompletion q
  have hinj :=
    (pullback.fst (pullback.snd q (gΛ)) b ≫ pullback.fst q (gΛ)).isClosedEmbedding.injective
  refine congrArg _ (hinj ?_)
  simpa only [Scheme.Hom.comp_apply] using h

/-- A morphism from a reduced scheme to `Spec R` with image the closed point factors through
`Spec (R ⧸ 𝔪)`. -/
theorem exists_comp_spec_quotient_eq {X : Scheme.{u}} [IsReduced X] (f : X ⟶ Spec (.of R))
    (hf : ∀ x, f x = closedPoint R) :
    ∃ t' : X ⟶ Spec (.of (R ⧸ maximalIdeal R)),
      t' ≫ Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ maximalIdeal R))) = f := by
  set i := Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ maximalIdeal R)))
  have : IsClosedImmersion i := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine ⟨IsClosedImmersion.lift i f ?_, IsClosedImmersion.lift_fac _ _ _⟩
  rw [Scheme.Hom.ker_eq_vanishingIdeal_closure_range f,
    ← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
  intro y hy
  show y ∈ (i.ker.support : Set _)
  rw [Scheme.Hom.support_ker i]
  refine closure_mono ?_ hy
  rintro _ ⟨x, rfl⟩
  let := Ideal.Quotient.field (maximalIdeal R)
  obtain ⟨p₀⟩ : Nonempty (Spec (.of (R ⧸ maximalIdeal R))) := inferInstance
  refine ⟨p₀, ?_⟩
  rw [hf x]
  exact PrimeSpectrum.ext (comap_algebraMap_quotient_eq_maximalIdeal le_rfl p₀.asIdeal p₀.isPrime)

/-- A point of `Spec R^` over the closed point of `Spec R` is the closed point. -/
theorem eq_closedPoint_of_spec_map_eq (y : Spec (.of 𝓡)) (hy : (gΛ) y = closedPoint R) :
    y = closedPoint 𝓡 := by
  by_contra hne
  have h0 : y.asIdeal = ⊥ := by
    by_contra h0
    exact hne (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
      (Ring.DimensionLEOne.maximalOfPrime h0 y.isPrime)))
  have := congrArg PrimeSpectrum.asIdeal hy
  change Ideal.comap (algebraMap R 𝓡) y.asIdeal = maximalIdeal R at this
  have hinj : Function.Injective (algebraMap R 𝓡) := AdicCompletion.of_injective (maximalIdeal R) R
  rw [h0, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 hinj] at this
  exact IsDiscreteValuationRing.not_a_field R this.symm

/-- The image in `Y` of a closed subscheme of `Y ×_R R^` lying over the closed point of
`Spec R^` is closed. -/
private theorem isClosed_range_subschemeι_comp_fst_adicCompletion {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of R)) (D' : (pullback q (gΛ) : Scheme.{u}).IdealSheafData)
    (hcl : ∀ d, pullback.snd q (gΛ) (D'.subschemeι d) = closedPoint 𝓡) :
    IsClosed (Set.range (D'.subschemeι ≫ pullback.fst q (gΛ))) := by
  set j := pullback.fst q (gΛ)
  set q' := pullback.snd q (gΛ)
  set b := Spec.map (CommRingCat.ofHom
    (algebraMap 𝓡 (𝓡 ⧸ (maximalIdeal R).map (algebraMap R 𝓡))))
  have := isClosedImmersion_closedFibre_adicCompletion q
  have hrange : Set.range (D'.subschemeι ≫ j) =
      (pullback.fst q' b ≫ j) '' ((pullback.fst q' b) ⁻¹' Set.range D'.subschemeι) := by
    ext y
    constructor
    · rintro ⟨d, rfl⟩
      obtain ⟨a, ha⟩ := exists_closedFibre_lift_adicCompletion q _ (hcl d)
      exact ⟨a, ⟨d, ha.symm⟩, congrArg j ha⟩
    · rintro ⟨a, ⟨d, hd⟩, rfl⟩
      exact ⟨d, congrArg j hd⟩
  rw [hrange]
  exact (pullback.fst q' b ≫ j).isClosedEmbedding.isClosedMap _
    (D'.subschemeι.isClosedEmbedding.isClosed_range.preimage (pullback.fst q' b).continuous)

/-- **A reduced closed subscheme of the closed fibre of `Y ×_R R^` comes from `Y`.** Let `D'`
cut out a reduced closed subscheme of `Y ×_R R^` lying over the closed point of `Spec R^`. Its
image `D` in `Y` (the scheme-theoretic image) pulls back to `D'`, and the subscheme of `D'` maps
isomorphically onto that of `D`: the closed fibre of `Y ×_R R^` is that of `Y`. -/
theorem exists_comap_eq_of_closedFibre {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R))
    (D' : (pullback q (gΛ) : Scheme.{u}).IdealSheafData) [IsReduced D'.subscheme]
    (hcl : ∀ d, pullback.snd q (gΛ) (D'.subschemeι d) = closedPoint 𝓡) :
    ∃ (D : Y.IdealSheafData) (φ : (D.comap (pullback.fst q (gΛ))).subscheme ⟶ D.subscheme),
      IsIso φ ∧ φ ≫ D.subschemeι = (D.comap (pullback.fst q (gΛ))).subschemeι ≫
        pullback.fst q (gΛ) ∧ D.comap (pullback.fst q (gΛ)) = D' := by
  set j := pullback.fst q (gΛ)
  set q' := pullback.snd q (gΛ)
  set g := D'.subschemeι ≫ j
  have hclosed : IsClosed (Set.range g) :=
    isClosed_range_subschemeι_comp_fst_adicCompletion q D' hcl
  set D : Y.IdealSheafData := D'.map j
  have hDsupp : (D.support : Set Y) = Set.range g := by
    show (g.ker.support : Set Y) = _
    rw [Scheme.Hom.support_ker_eq_closure_range g]
    exact hclosed.closure_eq
  have : IsReduced D.subscheme := Scheme.Hom.isReduced_image g
  have hqg : ∀ d, q (g d) = closedPoint R := fun d => by
    simp only [g, Scheme.Hom.comp_apply]
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hcl d]
    exact IsLocalRing.comap_closedPoint (algebraMap R 𝓡)
  have hDcl : ∀ x, (D.subschemeι ≫ q) x = closedPoint R := fun x => by
    have hx : D.subschemeι x ∈ (D.support : Set Y) := by
      rw [← D.range_subschemeι]
      exact ⟨x, rfl⟩
    rw [hDsupp] at hx
    obtain ⟨d, hd⟩ := hx
    rw [Scheme.Hom.comp_apply, ← hd]
    exact hqg d
  obtain ⟨t', ht'⟩ := exists_comp_spec_quotient_eq (D.subschemeι ≫ q) hDcl
  have hsq : IsPullback (pullback.snd j D.subschemeι) (pullback.fst j D.subschemeι ≫ q')
      (D.subschemeι ≫ q) (gΛ) :=
    (IsPullback.of_hasPullback j D.subschemeι).flip.paste_vert (IsPullback.of_hasPullback q (gΛ))
  have := isIso_pullback_fst_adicCompletion_of_factors (D.subschemeι ≫ q) t' ht'
  have : IsIso (pullback.snd j D.subschemeι) := by
    rw [← hsq.isoPullback_hom_fst]
    infer_instance
  let φ := (D.comapIso j).hom ≫ pullback.snd j D.subschemeι
  have hφ : φ ≫ D.subschemeι = (D.comap j).subschemeι ≫ j := by
    simp [φ]
  refine ⟨D, φ, inferInstance, hφ, ?_⟩
  have : IsReduced (D.comap j).subscheme := isReduced_of_isOpenImmersion φ
  have hsupp : (D.comap j).support = D'.support := by
    apply SetLike.coe_injective
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage, hDsupp,
      ← D'.range_subschemeι]
    ext y
    constructor
    · rintro ⟨d, hd⟩
      have hy : q' y = closedPoint 𝓡 := eq_closedPoint_of_spec_map_eq _ <| by
        rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
        show q (j y) = _
        rw [← hd]
        exact hqg d
      exact ⟨d, eq_of_base_fst_eq_of_closedPoint q (hcl d) hy hd⟩
    · rintro ⟨d, rfl⟩
      exact ⟨d, rfl⟩
  rw [Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme (D.comap j) _ hsupp,
    ← Scheme.IdealSheafData.eq_vanishingIdeal_of_isReduced_subscheme D' _ rfl]

/-- The structure morphism of the base change `Y ×_R R^` sends a point over the closed point of
`Spec R^` to a point of `Y` over the closed point of `Spec R`. -/
theorem base_fst_eq_closedPoint {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R))
    (y : (pullback q (gΛ) : Scheme.{u}))
    (hy : pullback.snd q (gΛ) y = closedPoint 𝓡) :
    q (pullback.fst q (gΛ) y) = closedPoint R := by
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply, hy]
  exact IsLocalRing.comap_closedPoint (algebraMap R 𝓡)

/-- **The base change of a regular model to the completion is regular.** At a point over the
closed point of `Spec R^` the local ring of `Y ×_R R^` has the completion of the local ring of
`Y` at its image ([Stacks, Tag 0BG5]), and a Noetherian local ring is regular exactly when its
completion is; at a point over the generic point it is a local ring of the smooth curve
`C ×_K K^`. -/
theorem isRegular_pullback_adicCompletion {C Y : Scheme.{u}} (c : C ⟶ Spec (.of K)) [Smooth c]
    {q : Y ⟶ Spec (.of R)} [LocallyOfFiniteType q] {eY : C ≅ pullback q (gR)}
    (he : eY.hom ≫ pullback.snd q (gR) = c) (hY : IsRegular Y) :
    IsRegular (pullback q (gΛ)) := by
  obtain ⟨l, hl⟩ := isPullback_baseChange_adicCompletion c he
  obtain ⟨-, hYs⟩ := (isRegular_iff_regular_stalks Y).1 hY
  have : IsLocallyNoetherian (pullback q (gΛ)) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd q (gΛ))
  refine (isRegular_iff_regular_stalks _).2 ⟨inferInstance, fun y => ?_⟩
  by_cases hy : pullback.snd q (gΛ) y = closedPoint 𝓡
  · have hfg : (maximalIdeal R).FG := (IsNoetherian.noetherian _)
    obtain ⟨e, -⟩ := stalkMap_adicCompletion_isomorphism R hfg Y q y
      (base_fst_eq_closedPoint q y hy)
    have := hYs (pullback.fst q (gΛ) y)
    have : IsRegularLocalRing (AdicCompletion
        (maximalIdeal (Y.presheaf.stalk (pullback.fst q (gΛ) y)))
        (Y.presheaf.stalk (pullback.fst q (gΛ) y))) :=
      isRegularLocalRing_iff_adicCompletion_maximalIdeal.1 inferInstance
    have := IsRegularLocalRing.of_ringEquiv e
    exact isRegularLocalRing_iff_adicCompletion_maximalIdeal.2 inferInstance
  · exact isRegularLocalRing_stalk_of_isModel (pullback.snd c (gK)) (pullback.snd q (gΛ))
      hl.isoPullback y (mem_range_genericPointInclusion_of_ne_closedPoint hy)

/-- **The minimal model after completion.** Let `Y ⟶ Spec R` be a minimal model of a smooth
projective curve `C` over `K` with `H⁰(C, 𝒪_C) = K`. Then `Y ×_R R^ ⟶ Spec R^` is a minimal model
of `C ×_K K^` over the completion `R^`: it is a proper model of `C_{K^}`, it is regular
(`isRegular_pullback_adicCompletion`), and an exceptional curve of the first kind on it lies in
the closed fibre, which is that of `Y`, and descends to one on `Y`. -/
theorem isMinimalModel_pullback_adicCompletion {C Y : Scheme.{u}} (c : C ⟶ Spec (.of K))
    [IsCurve K c] [Smooth c] [IsProper c] [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop)]
    {q : Y ⟶ Spec (.of R)} {eY : C ≅ pullback q (gR)} (hY : IsMinimalModel c q eY) :
    ∃ e' : pullback c (gK) ≅ pullback (pullback.snd q (gΛ)) (gΛK),
      IsMinimalModel (pullback.snd c (gK)) (pullback.snd q (gΛ)) e' := by
  obtain ⟨hproj, hH0, ⟨hflat, hlft, hqc, hce⟩, hprop, hreg, hnoexc⟩ := hY
  obtain ⟨l, hl⟩ := isPullback_baseChange_adicCompletion c hce
  have hproj' : Stacks.HProjective.IsHProjective (pullback.snd c (gK)) :=
    (isProjective_iff_isProjectiveMorphism_of_isAffine _).mp
      (IsProjective.pullback_snd (gK) ((isProjective_iff_isProjectiveMorphism_of_isAffine c).mpr
        hproj))
  have hreg' := isRegular_pullback_adicCompletion c hce hreg
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let S : RegularProperModelSituation.{u} :=
    { R := R, K := K, k := IsLocalRing.ResidueField R, residueEquiv := AlgEquiv.refl,
      C := C, C_to_K := c, X := Y, X_to_R := q, flat := hflat,
      locallyOfFiniteType := hlft, quasiCompact := hqc, regular := hreg,
      genericFiberIso := eY, genericFiberIso_over_K := hce,
      π := π, uniformizer := hπ, curveProjective := hproj }
  let S' : RegularProperModelSituation.{u} :=
    { R := 𝓡, K := 𝓚, k := IsLocalRing.ResidueField 𝓡, residueEquiv := AlgEquiv.refl,
      C := pullback c (gK), C_to_K := pullback.snd c (gK), X := pullback q (gΛ),
      X_to_R := pullback.snd q (gΛ), regular := hreg',
      genericFiberIso := hl.isoPullback, genericFiberIso_over_K := hl.isoPullback_hom_snd,
      π := algebraMap R 𝓡 π,
      uniformizer := IsDiscreteValuationRing.irreducible_algebraMap_adicCompletion R hπ,
      curveProjective := hproj' }
  refine ⟨hl.isoPullback, hproj', inferInstance,
    ⟨inferInstance, inferInstance, inferInstance, hl.isoPullback_hom_snd⟩, inferInstance, hreg',
    ?_⟩
  rintro ⟨κ, hκ, D', ε, hE⟩
  let := hκ
  have hr := S'.range_subschemeι_subset_range_specialFiberι_of_iso_projectiveLineProj D' κ ε
  have hcl : ∀ d, pullback.snd q (gΛ) (D'.subschemeι d) = closedPoint 𝓡 := fun d => by
    obtain ⟨z, hz⟩ := hr ⟨d, rfl⟩
    rw [← hz]
    show (pullback.fst (pullback.snd q (gΛ)) _ ≫ pullback.snd q (gΛ)) z = _
    rw [pullback.condition, Scheme.Hom.comp_apply, show (pullback.snd (pullback.snd q (gΛ))
        (Spec.map (CommRingCat.ofHom (algebraMap 𝓡 (IsLocalRing.ResidueField 𝓡))))) z =
          closedPoint _ from Subsingleton.elim _ _]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue 𝓡)
  have := isIntegral_subscheme_of_iso_projectiveLineProj D' κ ε
  obtain ⟨D, φ, _, hφ, rfl⟩ := exists_comap_eq_of_closedFibre q D' hcl
  obtain ⟨Z, hZ⟩ := S.exists_eq_specialFiberComponentIdeal_of_iso_projectiveLineProj D κ
    (ε ≪≫ asIso φ)
  have : Stacks.Divisors.IsEffectiveCartierDivisor D := by
    rw [hZ]
    exact isEffectiveCartierDivisor_specialFiberComponentIdeal S.toRegularModelSituation Z
  have : Flat (gΛ) := by
    rw [AlgebraicGeometry.Flat.SpecMap_iff, CommRingCat.hom_ofHom]
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  exact hnoexc ⟨κ, hκ, D, _,
    Scheme.IdealSheafData.IsExceptionalCurveOfFirstKind.of_comap_of_flat _ D φ hφ hE⟩

end Stacks.Models

end
