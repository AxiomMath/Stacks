module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SmoothLift.Cech
public import StacksFrontier.AlgebraicGeometry.Size.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.Algebra.Category.Ring.Constructions
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.EtaleDescentAlongPresentation

/-!
# From affine objects of the site to algebras

An affine square-zero thickening `i : T ⟶ T'` of objects of the big fppf site is put in the
normal form of `StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.SmoothLift.Objects`: `T'` is
the spectrum of `A' = Γ(T')`, `T` that of `A' ⧸ C` for the kernel `C` of `Γ(T') → Γ(T)`, and every
affine object `U` over `T'` is the spectrum of the `A'`-algebra `Γ(U)`.  The two pullback squares
the gluing argument needs are identified (`isPullback_tensor`, `isPullback_incl`).

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal TensorProduct

universe u

namespace AlgebraicGeometry.Space.SmoothLift

open Stacks.SmoothLift

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Pullback squares from pushout squares of rings -/

variable {D : Base B S hS}

/-- **A pushout square of rings under `A'` is a pullback square of the site.** -/
theorem isPullback_homOf {Rc₀ Rc₁ Rc₂ Rc₃ : CommRingCat.{u}} {φ₀ : CommRingCat.of D.A ⟶ Rc₀}
    {φ₁ : CommRingCat.of D.A ⟶ Rc₁} {φ₂ : CommRingCat.of D.A ⟶ Rc₂}
    {φ₃ : CommRingCat.of D.A ⟶ Rc₃} {h₀ : #Rc₀ < B.cutoff} {h₁ : #Rc₁ < B.cutoff}
    {h₂ : #Rc₂ < B.cutoff} {h₃ : #Rc₃ < B.cutoff}
    (a : Rc₀ ⟶ Rc₁) (b : Rc₀ ⟶ Rc₂) (c : Rc₁ ⟶ Rc₃) (d : Rc₂ ⟶ Rc₃)
    (ha : φ₀ ≫ a = φ₁) (hb : φ₀ ≫ b = φ₂) (hc : φ₁ ≫ c = φ₃) (hd : φ₂ ≫ d = φ₃)
    (H : IsPushout a b c d) :
    IsPullback (homOf (h := h₁) (h' := h₃) c hc) (homOf (h := h₂) (h' := h₃) d hd)
      (homOf (h := h₀) (h' := h₁) a ha) (homOf (h := h₀) (h' := h₂) b hb) :=
  isPullback_of_isPullback_toScheme (isPullback_SpecMap_of_isPushout a b c d H)

/-! ### The two pullback squares -/

/-- The square of a tensor product algebra over the base is cartesian. -/
theorem isPullback_tensor (R R' : Alg D) :
    IsPullback (mO (incl₁ R')) (mO (incl₂ (R := R) R')) (mO (toBase R)) (mO (toBase R')) :=
  isPullback_homOf _ _ _ _ _ _ _ _ (CommRingCat.isPushout_tensorProduct D.A R.R R'.R)

/-- The reduction of an algebra is the base change of the reduction of the base. -/
theorem isPushout_quotient (R : Alg D) :
    IsPushout (CommRingCat.ofHom (Ideal.Quotient.mk (sqIdeal D.C (baseAlg D).R)))
      (CommRingCat.ofHom (algebraMap D.A R.R))
      (CommRingCat.ofHom (qMap D.C (toBase R)))
      (CommRingCat.ofHom (Ideal.Quotient.mk (sqIdeal D.C R.R))) := by
  have hI : (sqIdeal D.C (baseAlg D).R).map (algebraMap D.A R.R) = sqIdeal D.C R.R := by
    rw [sqIdeal, sqIdeal, Ideal.map_map]
    rfl
  let e : R.R ⊗[D.A] (D.A ⧸ sqIdeal D.C (baseAlg D).R) ≃+* Q D.C R.R :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot R.R
      (sqIdeal D.C (baseAlg D).R)).symm.toRingEquiv.trans (Ideal.quotEquivOfEq hI)
  refine (CommRingCat.isPushout_tensorProduct D.A R.R (D.A ⧸ sqIdeal D.C (baseAlg D).R)).flip.of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toCommRingCatIso ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · ext a
    show e (1 ⊗ₜ[D.A] Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ (algebraMap D.A R.R a)
    show Ideal.quotEquivOfEq hI ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R.R
      (sqIdeal D.C (baseAlg D).R)).symm (1 ⊗ₜ[D.A] (Ideal.Quotient.mk _ a))) = _
    have h1 : (1 : R.R) ⊗ₜ[D.A] (Ideal.Quotient.mk (sqIdeal D.C (baseAlg D).R) a) =
        (1 : R.R) ⊗ₜ[D.A] (a • (1 : D.A ⧸ sqIdeal D.C (baseAlg D).R)) := by
      congr 1
      rw [Algebra.smul_def, mul_one]
      rfl
    rw [h1, ← TensorProduct.smul_tmul, ← Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk,
      AlgEquiv.symm_apply_apply, Algebra.algebraMap_eq_smul_one]
    rfl
  · ext r
    show Ideal.quotEquivOfEq hI ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot R.R
      (sqIdeal D.C (baseAlg D).R)).symm (r ⊗ₜ[D.A] 1)) = _
    rw [← Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, AlgEquiv.symm_apply_apply]
    rfl

/-- The reduction square, on schemes. -/
theorem isPullback_incl_scheme (R : Alg D) :
    IsPullback ((BigFppfOver.toScheme B S hS).map (incl R))
      ((BigFppfOver.toScheme B S hS).map (mO₀ (toBase R)))
      ((BigFppfOver.toScheme B S hS).map (mO (toBase R)))
      ((BigFppfOver.toScheme B S hS).map (incl (baseAlg D))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_quotient R).flip

/-- The reduction of an algebra is the fibre product of the algebra and the closed subscheme of
the base. -/
theorem isPullback_incl (R : Alg D) :
    IsPullback (incl R) (mO₀ (toBase R)) (mO (toBase R)) (incl (baseAlg D)) :=
  isPullback_homOf _ _ _ _ _ _ _ _ (isPushout_quotient R).flip

/-! ### The normal form of an affine square-zero thickening -/

section Normal

variable {T T' : BigFppfOver B S hS} [hT' : IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  (i : T ⟶ T') (hi : IsSquareZeroClosedImmersion B S hS i)

include hi in
/-- The kernel `C` of `Γ(T') → Γ(T)` of an affine square-zero thickening squares to zero. -/
theorem sqZero_ker : RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom *
    RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom = ⊥ := by
  have := hi.1
  rw [← pow_two]
  exact (Stacks.Smooth.ker_pow_eq_bot_iff_of_isAffine _ 2).mp hi.2

include hi in
/-- The base data of an affine square-zero thickening. -/
noncomputable abbrev baseOf : Base B S hS where
  A := Γ((BigFppfOver.toScheme B S hS).obj T', ⊤)
  C := RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom
  sq := ⟨sqZero_ker i hi⟩
  pS := ((BigFppfOver.toScheme B S hS).obj T').isoSpec.inv ≫ B.inclusion.map T'.hom
  size := lt_of_le_of_lt (Scheme.mk_sections_le_size _ ⟨⊤, isAffineOpen_top _⟩) T'.left.property

/-- The structure map of the base algebra `A'` is the identity. -/
theorem φO_base (D : Base B S hS) : φO (baseAlg D) = 𝟙 _ := rfl

/-- The structure morphism of `Spec R` to `S` is `Spec R ⟶ Spec A' ⟶ S`. -/
theorem inclusion_O_hom (D : Base B S hS) (R : Alg D) :
    B.inclusion.map (O R).hom = Spec.map (φO R) ≫ D.pS := rfl

/-- The scheme of the thickening is the spectrum of its global sections. -/
noncomputable def eT'Hom : O (baseAlg (baseOf i hi)) ⟶ T' :=
  siteHom ((BigFppfOver.toScheme B S hS).obj T').isoSpec.inv (by
    rw [inclusion_O_hom, φO_base, Spec.map_id, Category.id_comp]
    rfl)

/-- The inverse of `eT'Hom`. -/
noncomputable def eT'Inv : T' ⟶ O (baseAlg (baseOf i hi)) :=
  siteHom ((BigFppfOver.toScheme B S hS).obj T').isoSpec.hom (by
    rw [inclusion_O_hom, φO_base, Spec.map_id, Category.id_comp]
    exact Iso.hom_inv_id_assoc _ _)

/-- The morphism of schemes underlying `eT'Hom` is the inverse of `T' ≅ Spec Γ(T')`. -/
theorem toScheme_eT'Hom :
    (BigFppfOver.toScheme B S hS).map (eT'Hom i hi) =
      ((BigFppfOver.toScheme B S hS).obj T').isoSpec.inv :=
  toScheme_map_siteHom _ _

/-- The morphism of schemes underlying `eT'Inv` is `T' ≅ Spec Γ(T')`. -/
theorem toScheme_eT'Inv :
    (BigFppfOver.toScheme B S hS).map (eT'Inv i hi) =
      ((BigFppfOver.toScheme B S hS).obj T').isoSpec.hom :=
  toScheme_map_siteHom _ _

/-- **The thickening as the spectrum of its global sections**, in the site. -/
noncomputable def eT' : O (baseAlg (baseOf i hi)) ≅ T' where
  hom := eT'Hom i hi
  inv := eT'Inv i hi
  hom_inv_id := ext_toScheme (by
    rw [Functor.map_comp, toScheme_eT'Hom, toScheme_eT'Inv]
    exact (Iso.inv_hom_id _).trans
      ((BigFppfOver.toScheme B S hS).map_id (O (baseAlg (baseOf i hi)))).symm)
  inv_hom_id := ext_toScheme (by
    rw [Functor.map_comp, toScheme_eT'Hom, toScheme_eT'Inv]
    exact (Iso.hom_inv_id _).trans ((BigFppfOver.toScheme B S hS).map_id T').symm)

/-- The morphism of schemes underlying `eT'` is the inverse of `T' ≅ Spec Γ(T')`. -/
theorem toScheme_eT'_hom :
    (BigFppfOver.toScheme B S hS).map (eT' i hi).hom =
      ((BigFppfOver.toScheme B S hS).obj T').isoSpec.inv :=
  toScheme_eT'Hom i hi

include hi in
/-- The map `Γ(T') → Γ(T)` of an affine square-zero thickening is surjective. -/
theorem surjective_appTop : Function.Surjective ((BigFppfOver.toScheme B S hS).map i).appTop := by
  have := hi.1
  exact (IsClosedImmersion.isAffine_surjective_of_isAffine
    ((BigFppfOver.toScheme B S hS).map i)).2

/-- The extension of `C` to the base algebra `Γ(T')` is `C`, the kernel of `Γ(T') → Γ(T)`. -/
theorem sqIdeal_baseOf :
    sqIdeal (baseOf i hi).C (baseAlg (baseOf i hi)).R =
      RingHom.ker ((BigFppfOver.toScheme B S hS).map i).appTop.hom := by
  show Ideal.map (RingHom.id _) _ = _
  rw [Ideal.map_id]

/-- `Γ(T) = Γ(T') ⧸ C`. -/
noncomputable def psiT : CommRingCat.of (Q (baseOf i hi).C (baseAlg (baseOf i hi)).R) ≅
    Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  ((Ideal.quotEquivOfEq (sqIdeal_baseOf i hi)).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_appTop i hi))).toCommRingCatIso

/-- The map `Γ(T') → Γ(T)`, read through `Γ(T) ≅ Γ(T') ⧸ C`, is the quotient map. -/
theorem appTop_psiT_inv :
    ((BigFppfOver.toScheme B S hS).map i).appTop ≫ (psiT i hi).inv =
      CommRingCat.ofHom (Ideal.Quotient.mk _) := by
  apply (cancel_mono (psiT i hi).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  ext a
  show _ = (RingHom.quotientKerEquivOfSurjective (surjective_appTop i hi))
    (Ideal.quotEquivOfEq (sqIdeal_baseOf i hi) (Ideal.Quotient.mk _ a))
  rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]

/-- The thickening `T ⟶ T'`, read through `Γ(T) ≅ Γ(T') ⧸ C` and the identifications of `T`
and `T'` with the spectra of their global sections, is `Spec` of the quotient map. -/
theorem specMap_psiT_inv_comp :
    Spec.map (psiT i hi).inv ≫ ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv ≫
        (BigFppfOver.toScheme B S hS).map i =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫
        ((BigFppfOver.toScheme B S hS).obj T').isoSpec.inv := by
  rw [← Scheme.isoSpec_inv_naturality, ← Category.assoc, ← Spec.map_comp, appTop_psiT_inv]

/-- The morphism `Spec (Γ(T') ⧸ C) ⟶ T` underlying `eTHom` lies over `S`. -/
theorem eTHom_over :
    (Spec.map (psiT i hi).inv ≫ ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv) ≫
        B.inclusion.map T.hom =
      Spec.map (φQ (baseAlg (baseOf i hi))) ≫ (baseOf i hi).pS := by
  rw [← toScheme_map_comp_hom i, φQ, φO_base, Category.id_comp]
  simpa only [Category.assoc] using
    congrArg (· ≫ B.inclusion.map T'.hom) (specMap_psiT_inv_comp i hi)

/-- The closed subscheme as the spectrum of `Γ(T') ⧸ C`, as a morphism of the site. -/
noncomputable def eTHom : O₀ (baseAlg (baseOf i hi)) ⟶ T :=
  siteHom (Spec.map (psiT i hi).inv ≫ ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv)
    (eTHom_over i hi)

/-- The morphism `T ⟶ Spec (Γ(T') ⧸ C)` underlying `eTInv` lies over `S`. -/
theorem eTInv_over :
    (((BigFppfOver.toScheme B S hS).obj T).isoSpec.hom ≫ Spec.map (psiT i hi).hom) ≫
        (Spec.map (φQ (baseAlg (baseOf i hi))) ≫ (baseOf i hi).pS) = B.inclusion.map T.hom := by
  rw [← eTHom_over i hi]
  simp only [Category.assoc]
  rw [← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp, Iso.hom_inv_id_assoc]

/-- The inverse of `eTHom`. -/
noncomputable def eTInv : T ⟶ O₀ (baseAlg (baseOf i hi)) :=
  siteHom (((BigFppfOver.toScheme B S hS).obj T).isoSpec.hom ≫ Spec.map (psiT i hi).hom)
    (eTInv_over i hi)

/-- The morphism of schemes underlying `eTHom`. -/
theorem toScheme_eTHom :
    (BigFppfOver.toScheme B S hS).map (eTHom i hi) =
      Spec.map (psiT i hi).inv ≫ ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv :=
  toScheme_map_siteHom _ _

/-- The morphism of schemes underlying `eTInv`. -/
theorem toScheme_eTInv :
    (BigFppfOver.toScheme B S hS).map (eTInv i hi) =
      ((BigFppfOver.toScheme B S hS).obj T).isoSpec.hom ≫ Spec.map (psiT i hi).hom :=
  toScheme_map_siteHom _ _

/-- The morphisms of schemes underlying `eTHom` and `eTInv` compose to the identity of
`Spec (Γ(T') ⧸ C)`. -/
theorem eT_scheme_hom_inv :
    (Spec.map (psiT i hi).inv ≫ ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv) ≫
      (((BigFppfOver.toScheme B S hS).obj T).isoSpec.hom ≫ Spec.map (psiT i hi).hom) = 𝟙 _ := by
  rw [Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]

/-- The morphisms of schemes underlying `eTInv` and `eTHom` compose to the identity of `T`. -/
theorem eT_scheme_inv_hom :
    (((BigFppfOver.toScheme B S hS).obj T).isoSpec.hom ≫ Spec.map (psiT i hi).hom) ≫
      (Spec.map (psiT i hi).inv ≫ ((BigFppfOver.toScheme B S hS).obj T).isoSpec.inv) = 𝟙 _ := by
  rw [Category.assoc, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id, Category.id_comp,
    Iso.hom_inv_id]

/-- **The closed subscheme as the spectrum of `Γ(T') ⧸ C`**, in the site. -/
noncomputable def eT : O₀ (baseAlg (baseOf i hi)) ≅ T where
  hom := eTHom i hi
  inv := eTInv i hi
  hom_inv_id := ext_toScheme (by
    rw [Functor.map_comp, toScheme_eTHom, toScheme_eTInv]
    exact (eT_scheme_hom_inv i hi).trans
      ((BigFppfOver.toScheme B S hS).map_id (O₀ (baseAlg (baseOf i hi)))).symm)
  inv_hom_id := ext_toScheme (by
    rw [Functor.map_comp, toScheme_eTHom, toScheme_eTInv]
    exact (eT_scheme_inv_hom i hi).trans ((BigFppfOver.toScheme B S hS).map_id T).symm)

/-- **The two normal forms are compatible with the thickening.** -/
theorem eT_hom_i : (eT i hi).hom ≫ i = incl (baseAlg (baseOf i hi)) ≫ (eT' i hi).hom := by
  apply ext_toScheme
  rw [Functor.map_comp, Functor.map_comp, toScheme_eT'_hom]
  exact (congrArg (· ≫ _) (toScheme_eTHom i hi)).trans
    ((Category.assoc _ _ _).trans (specMap_psiT_inv_comp i hi))

end Normal

/-! ### Affine objects over the thickening as algebras -/

section AffineOver

variable (D) {U : BigFppfOver B S hS} [hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  (j : U ⟶ O (baseAlg D))

/-- The structure map `A' → Γ(U)` of an affine object over `Spec A'`. -/
noncomputable def structOf : CommRingCat.of D.A ⟶ Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of D.A)).inv ≫ ((BigFppfOver.toScheme B S hS).map j).appTop

/-- **An affine object over `Spec A'` as an `A'`-algebra.** -/
noncomputable def algOf : Alg D :=
  letI : Algebra D.A Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) := (structOf D j).hom.toAlgebra
  ⟨Γ((BigFppfOver.toScheme B S hS).obj U, ⊤),
    lt_of_le_of_lt (Scheme.mk_sections_le_size _ ⟨⊤, isAffineOpen_top _⟩) U.left.property⟩

/-- The structure map of `algOf D j` is `structOf D j`. -/
theorem φO_algOf : φO (algOf D j) = structOf D j := rfl

/-- The structure morphism, as a morphism of schemes to a spectrum. -/
noncomputable abbrev jS : (BigFppfOver.toScheme B S hS).obj U ⟶ Spec (CommRingCat.of D.A) :=
  (BigFppfOver.toScheme B S hS).map j

omit hU in
/-- The structure morphism `U ⟶ Spec A'` lies over `S`. -/
theorem jS_over : jS D j ≫ D.pS = B.inclusion.map U.hom := by
  have := toScheme_map_comp_hom j
  rw [inclusion_O_hom, φO_base, Spec.map_id, Category.id_comp] at this
  exact this

/-- `Spec Γ(U) ≅ U ⟶ Spec A'` is `Spec` of the structure map `A' → Γ(U)`. -/
theorem isoSpec_inv_j :
    ((BigFppfOver.toScheme B S hS).obj U).isoSpec.inv ≫ jS D j = Spec.map (structOf D j) := by
  rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

/-- The morphism `Spec Γ(U) ⟶ U` underlying `eUHom` lies over `S`. -/
theorem eUHom_over :
    ((BigFppfOver.toScheme B S hS).obj U).isoSpec.inv ≫ B.inclusion.map U.hom =
      Spec.map (structOf D j) ≫ D.pS := by
  rw [← jS_over, ← Category.assoc, isoSpec_inv_j]

/-- The identification of `U` with the spectrum of its global sections, in the site. -/
noncomputable def eUHom : O (algOf D j) ⟶ U :=
  siteHom ((BigFppfOver.toScheme B S hS).obj U).isoSpec.inv (eUHom_over D j)

/-- The morphism `U ⟶ Spec Γ(U)` underlying `eUInv` lies over `S`. -/
theorem eUInv_over :
    ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom ≫ Spec.map (structOf D j) ≫ D.pS =
      B.inclusion.map U.hom := by
  rw [← eUHom_over, Iso.hom_inv_id_assoc]

/-- The inverse of `eUHom`. -/
noncomputable def eUInv : U ⟶ O (algOf D j) :=
  siteHom ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom (eUInv_over D j)

/-- The morphism of schemes underlying `eUHom` is the inverse of `U ≅ Spec Γ(U)`. -/
theorem toScheme_eUHom :
    (BigFppfOver.toScheme B S hS).map (eUHom D j) =
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.inv := toScheme_map_siteHom _ _

/-- The morphism of schemes underlying `eUInv` is `U ≅ Spec Γ(U)`. -/
theorem toScheme_eUInv :
    (BigFppfOver.toScheme B S hS).map (eUInv D j) =
      ((BigFppfOver.toScheme B S hS).obj U).isoSpec.hom := toScheme_map_siteHom _ _

/-- **An affine object over `Spec A'` is the spectrum of its global sections**, in the site. -/
noncomputable def eU : O (algOf D j) ≅ U where
  hom := eUHom D j
  inv := eUInv D j
  hom_inv_id := ext_toScheme (by
    rw [Functor.map_comp, toScheme_eUHom, toScheme_eUInv]
    exact (Iso.inv_hom_id _).trans ((BigFppfOver.toScheme B S hS).map_id (O (algOf D j))).symm)
  inv_hom_id := ext_toScheme (by
    rw [Functor.map_comp, toScheme_eUHom, toScheme_eUInv]
    exact (Iso.hom_inv_id _).trans ((BigFppfOver.toScheme B S hS).map_id U).symm)

/-- The identification is compatible with the structure maps. -/
theorem eU_hom_j : (eU D j).hom ≫ j = mO (toBase (algOf D j)) :=
  ext_toScheme <| ((BigFppfOver.toScheme B S hS).map_comp _ _).trans <|
    (congrArg (· ≫ jS D j) (toScheme_eUHom D j)).trans (isoSpec_inv_j D j)

/-- The inverse of the identification is compatible with the structure maps. -/
theorem eU_inv_mO : (eU D j).inv ≫ mO (toBase (algOf D j)) = j := by
  rw [← eU_hom_j, Iso.inv_hom_id_assoc]

/-- The structure morphism `U ⟶ Spec A'` is étale if and only if `Spec Γ(U) ⟶ Spec A'` is. -/
theorem etale_jS_iff : Etale (jS D j) ↔ Etale (Spec.map (structOf D j)) := by
  rw [← isoSpec_inv_j]
  exact (MorphismProperty.cancel_left_of_respectsIso @Etale _ _).symm

/-- **An étale affine object over `Spec A'` is a flat `A'`-algebra.** -/
theorem flat_algOf (hj : Etale ((BigFppfOver.toScheme B S hS).map j)) :
    Module.Flat D.A (algOf D j).R := by
  let : Algebra D.A Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) := (structOf D j).hom.toAlgebra
  have : Algebra.Etale D.A Γ((BigFppfOver.toScheme B S hS).obj U, ⊤) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp ((etale_jS_iff D j).mp hj)
  exact inferInstanceAs (Module.Flat D.A Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))

/-- The étale map `Spec Γ(U) ⟶ Spec A'` of an étale affine object. -/
theorem etale_mO_toBase (hj : Etale ((BigFppfOver.toScheme B S hS).map j)) :
    Etale ((BigFppfOver.toScheme B S hS).map (mO (toBase (algOf D j)))) :=
  (etale_jS_iff D j).mp hj

end AffineOver

/-! ### Faithful flatness of a jointly surjective family -/

/-- A finite product of flat `A`-algebras whose spectra jointly cover `Spec A` is faithfully flat
over `A`. -/
theorem faithfullyFlat_pi {A : Type u} [CommRing A] {K : Type u} [Fintype K] (Bk : K → Type u)
    [∀ k, CommRing (Bk k)] [∀ k, Algebra A (Bk k)] [∀ k, Module.Flat A (Bk k)]
    (h : ∀ p : PrimeSpectrum A, ∃ k, ∃ q : PrimeSpectrum (Bk k),
      PrimeSpectrum.comap (algebraMap A (Bk k)) q = p) :
    Module.FaithfullyFlat A (∀ k, Bk k) := by
  classical
  have : Module.Flat A (∀ k, Bk k) :=
    Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype A K Bk).symm
  refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_
  obtain ⟨k, q, hq⟩ := h p
  refine ⟨PrimeSpectrum.comap (Pi.evalRingHom Bk k) q, ?_⟩
  rw [← hq, ← PrimeSpectrum.comap_comp_apply]
  rfl

end AlgebraicGeometry.Space.SmoothLift
