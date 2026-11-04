module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.FieldTheory.IsSepClosed
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.ResidueField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.SpecFieldNormal
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Support
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Injective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleEmbedding.ResidueFieldSeparability

/-!
# A normal integral scheme with separably closed function field over a point

Let `X` be a quasi-separated scheme and `x` a point of `X`. Let `Z` be the reduced closure of
`{x}`, an integral scheme with generic point `x` and function field `K = κ(x)`, and let `L` be a
separable closure of `K`. The relative normalization `Y` of `Z` in `Spec L` is an integral normal
scheme, integral over `X`, with generic point over `x` and with function field `L`: over an affine
open `Spec A` of `Z` it is the spectrum of the integral closure of `A` in `L`, whose fraction field
is `L` because `L` is algebraic over `K = Frac A`.

This is the scheme of the proof of Stacks 09Z6 on which the inverse image of a constructible sheaf
becomes constant at the generic point.

## Main results

* `AlgebraicGeometry.exists_isIntegralHom_isNormal_isSepClosed_functionField` — such a `Y`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- The morphism from the spectrum of the function field of an integral scheme sends every point
to the generic point. -/
private theorem fromSpecStalk_genericPoint_apply (Z : Scheme.{u}) [IsIntegral Z]
    (y : Spec Z.functionField) : Z.fromSpecStalk (genericPoint Z) y = genericPoint Z := by
  have : Subsingleton ↥(Spec Z.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Z.functionField))
  rw [Subsingleton.elim y (IsLocalRing.closedPoint _), Scheme.fromSpecStalk_closedPoint]

/-- A morphism to the spectrum of the function field gives a morphism landing in every open
containing the generic point. -/
private theorem top_le_preimage_fromSpecStalk_genericPoint (Z : Scheme.{u}) [IsIntegral Z]
    {W : Scheme.{u}} (g : W ⟶ Spec Z.functionField) {U : Z.Opens} (hU : genericPoint Z ∈ U) :
    ⊤ ≤ (g ≫ Z.fromSpecStalk (genericPoint Z)) ⁻¹ᵁ U := fun y _ => by
  change Z.fromSpecStalk (genericPoint Z) (g y) ∈ U
  rwa [fromSpecStalk_genericPoint_apply]

/-- Restricting a section over a nonempty open of an irreducible scheme to the spectrum of a field
through the generic point is the germ at the generic point followed by the field map. -/
theorem appLE_fromSpecStalk_genericPoint_ΓSpecIso (Z : Scheme.{u}) [IsIntegral Z]
    {L : CommRingCat.{u}} (φ : Z.functionField ⟶ L) (U : Z.Opens) [Nonempty U]
    (e : ⊤ ≤ (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)) ⁻¹ᵁ U) :
    (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)).appLE U ⊤ e ≫ (Scheme.ΓSpecIso L).hom =
      Z.germToFunctionField U ≫ φ := by
  have hU : genericPoint Z ∈ U :=
    ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  have htop : ⊤ ≤ Z.fromSpecStalk (genericPoint Z) ⁻¹ᵁ U :=
    top_le_preimage_fromSpecStalk_genericPoint Z (𝟙 _) hU
  have h₁ : (Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)).appLE U ⊤ e =
      (Z.fromSpecStalk (genericPoint Z)).appLE U ⊤ htop ≫ (Spec.map φ).appTop := by
    rw [Scheme.Hom.comp_appLE, Scheme.Hom.appLE, Category.assoc]
    congr 1
  rw [h₁, Category.assoc, Scheme.ΓSpecIso_naturality, Scheme.Hom.appLE,
    Scheme.fromSpecStalk_app hU]
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← op_comp, homOfLE_comp, homOfLE_refl,
    op_id, CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_assoc]

/-- `appLE` of two equal morphisms. -/
theorem appLE_eq_of_eq {X Y : Scheme.{u}} {h₁ h₂ : X ⟶ Y} (h : h₁ = h₂) (U : Y.Opens)
    (V : X.Opens) (e₁ : V ≤ h₁ ⁻¹ᵁ U) (e₂ : V ≤ h₂ ⁻¹ᵁ U) :
    h₁.appLE U V e₁ = h₂.appLE U V e₂ := by
  subst h
  rfl

/-- If a morphism from the spectrum of a field lands in `U`, so does its map to the
normalization, into the preimage of `U`. -/
private theorem top_le_preimage_toNormalization {Z : Scheme.{u}} {L : Type u} [Field L]
    (j : Spec (.of L) ⟶ Z) [QuasiCompact j] [QuasiSeparated j] {U : Z.Opens}
    (hjtop : ⊤ ≤ j ⁻¹ᵁ U) : ⊤ ≤ j.toNormalization ⁻¹ᵁ (j.fromNormalization ⁻¹ᵁ U) :=
  fun y hy => by
    change j.fromNormalization (j.toNormalization y) ∈ U
    rw [← Scheme.Hom.comp_apply, j.toNormalization_fromNormalization]
    exact hjtop hy

/-- Evaluating a section of `Z` pulled back to the normalization at the point of `Spec L` is
evaluating it along `j`. -/
private theorem appLE_toNormalization_fromNormalization_app_apply {Z : Scheme.{u}} {L : Type u}
    [Field L] (j : Spec (.of L) ⟶ Z) [QuasiCompact j] [QuasiSeparated j] {U : Z.Opens}
    (hjtop : ⊤ ≤ j ⁻¹ᵁ U) (a : Γ(Z, U)) :
    (j.toNormalization.appLE _ ⊤ (top_le_preimage_toNormalization j hjtop) ≫
      (Scheme.ΓSpecIso (.of L)).hom).hom ((j.fromNormalization.app U).hom a) =
      (j.appLE U ⊤ hjtop ≫ (Scheme.ΓSpecIso (.of L)).hom).hom a := by
  have h : j.fromNormalization.app U ≫
      j.toNormalization.appLE _ ⊤ (top_le_preimage_toNormalization j hjtop) =
      j.appLE U ⊤ hjtop :=
    (Scheme.Hom.comp_appLE _ _ U ⊤ _).symm.trans
      (appLE_eq_of_eq j.toNormalization_fromNormalization _ _ _ _)
  rw [← h]
  rfl

/-- Over an affine open `U` of `Z` that `j : Spec L ⟶ Z` lands in, evaluating sections of the
normalization at the point of `Spec L` is injective, with image containing every element of `L`
integral over `Γ(Z, U)`. -/
private theorem injective_appLE_toNormalization_and_isIntegral_mem_range {Z : Scheme.{u}}
    {L : Type u} [Field L] (j : Spec (.of L) ⟶ Z) [QuasiCompact j] [QuasiSeparated j] {U : Z.Opens}
    (hU : IsAffineOpen U) (hjtop : ⊤ ≤ j ⁻¹ᵁ U) (χ : Γ(Z, U) ⟶ .of L)
    (hχ : j.appLE U ⊤ hjtop ≫ (Scheme.ΓSpecIso (.of L)).hom = χ) :
    letI := χ.hom.toAlgebra
    Function.Injective (j.toNormalization.appLE _ ⊤ (top_le_preimage_toNormalization j hjtop) ≫
        (Scheme.ΓSpecIso (.of L)).hom).hom ∧
      ∀ ℓ : L, _root_.IsIntegral Γ(Z, U) ℓ → ∃ x, (j.toNormalization.appLE _ ⊤
        (top_le_preimage_toNormalization j hjtop) ≫ (Scheme.ΓSpecIso (.of L)).hom).hom x = ℓ := by
  subst hχ
  let algL : Algebra Γ(Z, U) L :=
    (j.appLE U ⊤ hjtop ≫ (Scheme.ΓSpecIso (.of L)).hom).hom.toAlgebra
  have hgtop := top_le_preimage_toNormalization j hjtop
  let algB : Algebra Γ(Z, U) Γ(Spec (.of L), j ⁻¹ᵁ U) := (j.app U).hom.toAlgebra
  let iso := j.normalizationObjIso hU
  have hjeq : j ⁻¹ᵁ U = ⊤ := le_antisymm le_top hjtop
  let eR : Γ(Spec (.of L), j ⁻¹ᵁ U) ≃+* L :=
    ((Spec (.of L)).presheaf.mapIso (eqToIso hjeq.symm).op ≪≫
      Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv
  have heR : ∀ a, eR (algebraMap Γ(Z, U) _ a) = algebraMap Γ(Z, U) L a := fun a => by
    change ((Spec (.of L)).presheaf.map (eqToIso hjeq.symm).op.hom ≫
      (Scheme.ΓSpecIso (.of L)).hom).hom ((j.app U).hom a) = _
    rw [show (eqToIso hjeq.symm).op.hom = (homOfLE hjtop).op from Subsingleton.elim _ _]
    rfl
  have hψ : ∀ x, (j.toNormalization.appLE _ ⊤ hgtop ≫ (Scheme.ΓSpecIso (.of L)).hom).hom x =
      eR (iso.hom x).1 := fun x => by
    change ((j.toNormalization.app _ ≫ (Spec (.of L)).presheaf.map (homOfLE hgtop).op) ≫
      (Scheme.ΓSpecIso (.of L)).hom).hom x = _
    rw [j.toNormalization_app_preimage ⟨U, hU⟩]
    simp only [Category.assoc, ← Functor.map_comp]
    rfl
  let eA : Γ(Spec (.of L), j ⁻¹ᵁ U) →ₐ[Γ(Z, U)] L := { eR.toRingHom with commutes' := heR }
  refine ⟨fun x y hxy => ?_, fun ℓ hℓ => ?_⟩
  · rw [hψ, hψ] at hxy
    exact iso.commRingCatIsoToRingEquiv.injective (Subtype.ext (eR.injective hxy))
  have hb : _root_.IsIntegral Γ(Z, U) (eR.symm ℓ) := by
    rw [← isIntegral_algHom_iff eA eR.injective]
    change _root_.IsIntegral Γ(Z, U) (eR (eR.symm ℓ))
    rwa [RingEquiv.apply_symm_apply]
  refine ⟨iso.inv ⟨eR.symm ℓ, hb⟩, ?_⟩
  rw [hψ]
  change eR ((iso.inv ≫ iso.hom) ⟨eR.symm ℓ, hb⟩).1 = ℓ
  rw [Iso.inv_hom_id]
  exact eR.apply_symm_apply ℓ

/-- Let `L` be algebraic over a domain `A`, and `ψ : B →+* L` injective, compatible with a map
`A →+* B`, with image containing every element of `L` integral over `A`. Then `L` is the fraction
field of `B`. -/
private theorem isFractionRing_of_isIntegral_mem_range {A B L : Type*} [CommRing A] [CommRing B]
    [IsDomain B] [Field L] [Algebra A L] [Algebra.IsAlgebraic A L] (ψ : B →+* L)
    (hψ : Function.Injective ψ) (fA : A →+* B) (hinj : Function.Injective (algebraMap A L))
    (hf : ∀ a, ψ (fA a) = algebraMap A L a) (hint : ∀ ℓ : L, _root_.IsIntegral A ℓ → ∃ x, ψ x = ℓ) :
    letI := ψ.toAlgebra
    IsFractionRing B L := by
  let := ψ.toAlgebra
  refine ⟨fun y => IsUnit.mk0 _ fun h => nonZeroDivisors.ne_zero y.2 (hψ (by rwa [map_zero])),
    fun ℓ => ?_, fun {x y} hxy => ⟨1, by rw [hψ hxy]⟩⟩
  obtain ⟨a, ha, hℓ⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) ℓ).exists_integral_multiple
  obtain ⟨c, hc⟩ := hint (a • ℓ) hℓ
  have ha' : fA a ≠ 0 := fun h => ha (hinj (by rw [← hf, h, map_zero, map_zero]))
  rw [Algebra.smul_def] at hc
  refine ⟨⟨c, ⟨fA a, mem_nonZeroDivisors_of_ne_zero ha'⟩⟩, ?_⟩
  change ℓ * ψ (fA a) = ψ c
  rw [hc, hf, mul_comm]

/-- **The normalization of an integral scheme in an algebraic extension `L` of its function field
has function field `L`**; in particular it is separably closed when `L` is. -/
theorem isSepClosed_functionField_normalization (Z : Scheme.{u}) [IsIntegral Z]
    (L : Type u) [Field L] [IsSepClosed L] [Algebra Z.functionField L]
    [Algebra.IsAlgebraic Z.functionField L]
    [QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L)) ≫
      Z.fromSpecStalk (genericPoint Z))]
    [QuasiSeparated (Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L)) ≫
      Z.fromSpecStalk (genericPoint Z))] :
    IsSepClosed (Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L)) ≫
      Z.fromSpecStalk (genericPoint Z)).normalization.functionField := by
  classical
  set φ := CommRingCat.ofHom (algebraMap Z.functionField L)
  set j := Spec.map φ ≫ Z.fromSpecStalk (genericPoint Z)
  obtain ⟨_, ⟨U, hU, rfl⟩, hξU, -⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint Z)) isOpen_univ
  have : Nonempty U := ⟨⟨_, hξU⟩⟩
  have hjtop : ⊤ ≤ j ⁻¹ᵁ U := top_le_preimage_fromSpecStalk_genericPoint Z (Spec.map φ) hξU
  have hgtop := top_le_preimage_toNormalization j hjtop
  have : Nonempty (j.fromNormalization ⁻¹ᵁ U) :=
    ⟨⟨j.toNormalization (IsLocalRing.closedPoint L), hgtop trivial⟩⟩
  have h := appLE_fromSpecStalk_genericPoint_ΓSpecIso Z φ U hjtop
  let : Algebra Γ(Z, U) L := (Z.germToFunctionField U ≫ φ).hom.toAlgebra
  have : IsScalarTower Γ(Z, U) Z.functionField L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsFractionRing Γ(Z, U) Z.functionField :=
    functionField_isFractionRing_of_isAffineOpen Z U hU
  have : Algebra.IsAlgebraic Γ(Z, U) L :=
    (IsFractionRing.comap_isAlgebraic_iff (K := Z.functionField)).mpr inferInstance
  obtain ⟨hψinj, hint⟩ := injective_appLE_toNormalization_and_isIntegral_mem_range j hU hjtop _ h
  let ψ := (j.toNormalization.appLE _ ⊤ hgtop ≫ (Scheme.ΓSpecIso (.of L)).hom).hom
  let := ψ.toAlgebra
  have : IsFractionRing Γ(j.normalization, j.fromNormalization ⁻¹ᵁ U) L :=
    isFractionRing_of_isIntegral_mem_range ψ hψinj (j.fromNormalization.app U).hom
      (fun a b hab => Z.germToFunctionField_injective U (φ.hom.injective hab))
      (fun a => (appLE_toNormalization_fromNormalization_app_apply j hjtop a).trans
        (congrArg (fun t => t.hom a) h)) hint
  have : IsFractionRing Γ(j.normalization, j.fromNormalization ⁻¹ᵁ U)
      j.normalization.functionField :=
    functionField_isFractionRing_of_isAffineOpen _ _ (hU.preimage _)
  exact IsSepClosed.of_ringEquiv
    (IsFractionRing.ringEquivOfRingEquiv (A := Γ(j.normalization, j.fromNormalization ⁻¹ᵁ U))
      (B := Γ(j.normalization, j.fromNormalization ⁻¹ᵁ U)) (K := j.normalization.functionField)
      (L := L) (RingEquiv.refl _))

/-- The generic point of the normalization of a morphism from the spectrum of a field is the
image of the unique point. -/
private theorem genericPoint_normalization_eq_toNormalization {Z : Scheme.{u}} {L : Type u}
    [Field L] (j : Spec (.of L) ⟶ Z) [QuasiCompact j] [QuasiSeparated j] :
    genericPoint j.normalization = j.toNormalization (IsLocalRing.closedPoint L) := by
  have : Subsingleton ↥(Spec (CommRingCat.of L)) := inferInstanceAs (Subsingleton (PrimeSpectrum L))
  have hr : Set.range j.toNormalization = {j.toNormalization (IsLocalRing.closedPoint L)} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨Set.mem_range_self _, ?_⟩
    rintro _ ⟨w, rfl⟩
    rw [Subsingleton.elim w (IsLocalRing.closedPoint L)]
  refine (genericPoint_spec _).eq (isGenericPoint_iff_specializes.2 fun y => ?_)
  refine iff_of_true (specializes_iff_mem_closure.mpr ?_) trivial
  rw [← hr, j.toNormalization.denseRange.closure_range]
  trivial

/-- **An integral normal scheme with separably closed function field over a point.** For a point
`x` of a quasi-separated scheme `X` there is an integral morphism `f : Y ⟶ X` from an integral
normal scheme `Y` with separably closed function field whose generic point lies over `x`: the
normalization of the reduced closure `Z` of `{x}` in a separable closure of its function field.
The function field of `Y` is separable over `κ(x)`. -/
theorem exists_isIntegralHom_isNormal_isSepClosed_functionField [QuasiSeparatedSpace X]
    (x : X) :
    ∃ (Y : Scheme.{u}) (_ : IsIntegral Y) (f : Y ⟶ X), IsIntegralHom f ∧ IsNormal Y ∧
      IsSepClosed Y.functionField ∧ f (genericPoint Y) = x ∧
      (letI := (f.residueFieldMap (genericPoint Y)).hom.toAlgebra;
        Algebra.IsSeparable (X.residueField (f (genericPoint Y)))
          (Y.residueField (genericPoint Y))) := by
  let I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x} : Set X))
  let Z := I.subscheme
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated I.subschemeι
  let L := SeparableClosure Z.functionField
  let j := Spec.map (CommRingCat.ofHom (algebraMap Z.functionField L)) ≫
    Z.fromSpecStalk (genericPoint Z)
  let pt : ↥(Spec (CommRingCat.of L)) := IsLocalRing.closedPoint L
  have hgen : genericPoint j.normalization = j.toNormalization pt :=
    genericPoint_normalization_eq_toNormalization j
  have hL : let := (CommRingCat.ofHom (algebraMap Z.functionField L)).hom.toAlgebra
      Algebra.IsSeparable Z.functionField L := by
    have e : (inferInstance : Algebra Z.functionField L) =
        (CommRingCat.ofHom (algebraMap Z.functionField L)).hom.toAlgebra :=
      Algebra.algebra_ext _ _ fun _ => rfl
    exact e ▸ (inferInstance : Algebra.IsSeparable Z.functionField L)
  refine ⟨j.normalization, inferInstance, j.fromNormalization ≫ I.subschemeι, inferInstance,
    isNormal_normalization_of_spec_field L j, isSepClosed_functionField_normalization Z L, ?_, ?_⟩
  · rw [hgen, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply j.toNormalization,
      j.toNormalization_fromNormalization]
    change I.subschemeι (Z.fromSpecStalk (genericPoint Z) (Spec.map _ pt)) = x
    rw [fromSpecStalk_genericPoint_apply]
    exact Stacks.Chow.image_genericPoint_eq_of_range_eq_closure I.subschemeι x
      (Stacks.Chow.range_subschemeι_vanishingIdeal_closure x)
  · rw [hgen]
    exact isSeparable_residueFieldMap_of_isSeparable_descResidueField j.toNormalization
      (j.fromNormalization ≫ I.subschemeι) rfl
      (isSeparable_descResidueField_comp_of_surjectiveOnStalks j I.subschemeι
        (q := j.toNormalization ≫ j.fromNormalization ≫ I.subschemeι)
        (by rw [← Category.assoc, j.toNormalization_fromNormalization])
        (isSeparable_descResidueField_fromSpecStalk_genericPoint (Z := Z)
          (CommRingCat.ofHom (algebraMap Z.functionField L)) hL j rfl))

end AlgebraicGeometry

end
