module

public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.DeformationLaurent
public import StacksFrontier.AlgebraicGeometry.Chow.VirtualNormalClass.DeformationFiniteType
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.AffineLine
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.FibreDimension
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyOverFieldIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Composition

/-!
# The complement of the special fibre of the deformation space

Let `ℐ` be a quasi-coherent ideal sheaf on a scheme `X` and `π : D ⟶ X` the deformation space
`D = Spec_X(𝒪_X[t⁻¹, ℐt])`. The complement `U = D(t⁻¹)` of the special fibre `t⁻¹ = 0` is
`X × 𝐆_m`: over an affine open `W = Spec A` of `X` its ring of functions is the Laurent polynomial
ring `A[T, T⁻¹]` (`Stacks.Deformation.isLocalization_chartLaurent`). Hence `U ⟶ X` is flat of
relative dimension one, which is the hypothesis on the open part of the construction of the class
at infinity of Stacks 0F9J.

## Main results

* `Stacks.Deformation.flat_specMap_laurentC` and
  `Stacks.Deformation.relativeDimension_specMap_laurentC` — `Spec A[T, T⁻¹] ⟶ Spec A` is flat of
  relative dimension one.
* `Stacks.Deformation.exists_ringEquiv_laurent` — over an affine open `W = Spec A` of the base, the
  functions on `D(t⁻¹) ∩ π⁻¹W` are `A[T, T⁻¹]`, with the structure map the constants.
* `Stacks.Deformation.flat_complementOpen`, `Stacks.Deformation.relativeDimension_complementOpen` —
  **`D(t⁻¹) ⟶ X` is flat, locally of finite type and of relative dimension one.**
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Deformation

section Laurent

variable (R : CommRingCat.{u})

/-- `Spec A[T, T⁻¹] ⟶ Spec A[T]` is an open immersion, the localization at `T`. -/
instance isOpenImmersion_specMap_toLaurent :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (Polynomial.toLaurent (R := R)))) := by
  have := IsOpenImmersion.of_isLocalization (R := Polynomial R) (S := LaurentPolynomial R)
    (Polynomial.X : Polynomial R)
  convert this using 3

/-- The constants `Spec A[T, T⁻¹] ⟶ Spec A` factor as `Spec A[T, T⁻¹] ⟶ Spec A[T] ⟶ Spec A`. -/
theorem specMap_laurentC_eq :
    Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : R →+* LaurentPolynomial R)) =
      Spec.map (CommRingCat.ofHom (Polynomial.toLaurent (R := R))) ≫
        Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun r => (Polynomial.toLaurent_C r).symm

/-- `Spec A[T, T⁻¹] ⟶ Spec A` is flat. -/
instance flat_specMap_laurentC :
    Flat (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : R →+* LaurentPolynomial R))) := by
  rw [specMap_laurentC_eq]
  infer_instance

/-- `Spec A[T, T⁻¹] ⟶ Spec A` is locally of finite type. -/
instance locallyOfFiniteType_specMap_laurentC :
    LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : R →+* LaurentPolynomial R))) := by
  rw [specMap_laurentC_eq]
  infer_instance

/-- **`Spec A[T, T⁻¹] ⟶ Spec A` has relative dimension one**: it is an open subscheme of the
affine line. -/
theorem relativeDimension_specMap_laurentC :
    AlgebraicGeometry.RelativeDimension
      (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : R →+* LaurentPolynomial R))) 1 := by
  have h := AlgebraicGeometry.RelativeDimension.comp_isOpenImmersion
    (Spec.map (CommRingCat.ofHom (Polynomial.toLaurent (R := R))))
    (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))
    (Stacks.Chow.relativeDimension_specMap_C R)
  have key : ∀ (g : Spec (CommRingCat.of (LaurentPolynomial R)) ⟶ Spec R) [LocallyOfFiniteType g],
      g = Spec.map (CommRingCat.ofHom (Polynomial.toLaurent (R := R))) ≫
          Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)) →
        AlgebraicGeometry.RelativeDimension g 1 := by
    intro g _ hg
    subst hg
    exact h
  exact key _ (specMap_laurentC_eq R)

end Laurent

section Complement

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The parameter `t⁻¹` as a global function on the deformation space. -/
abbrev paramFunction : Γ(deformationSpace I, ⊤) := paramGlobal I

/-- **The complement `D(t⁻¹)` of the special fibre of the deformation space.** -/
abbrev complementOpen : (deformationSpace I).Opens :=
  (deformationSpace I).basicOpen (paramFunction I)

/-- Over an open `W` of the base, the complement of the special fibre is the basic open of
`t⁻¹` in the chart `π⁻¹W`. -/
theorem complementOpen_inf_preimage (W : X.Opens) :
    complementOpen I ⊓ deformationSpaceToBase I ⁻¹ᵁ W =
      (deformationSpace I).basicOpen (paramChartOf I W) := by
  have h := (deformationSpace I).basicOpen_res (paramFunction I)
    (homOfLE (le_top : deformationSpaceToBase I ⁻¹ᵁ W ≤ ⊤)).op
  have h2 : ((deformationSpace I).presheaf.map
      (homOfLE (le_top : deformationSpaceToBase I ⁻¹ᵁ W ≤ ⊤)).op).hom (paramFunction I) =
      paramChartOf I W := paramGlobal_restrict I W
  rw [h2] at h
  rw [h, inf_comm]

/-- The Laurent chart of `D(t⁻¹) ∩ π⁻¹W`: a ring isomorphism with `Γ(X, W)[T, T⁻¹]` carrying the
structure map to `C` and the restriction of `t⁻¹` to `T⁻¹`. -/
private theorem exists_ringEquiv_laurent_aux (W : X.affineOpens) :
    ∃ θ : Γ(deformationSpace I, (deformationSpace I).basicOpen (paramChartOf I W.1)) ≃+*
        LaurentPolynomial Γ(X, W.1),
      (∀ a : Γ(X, W.1), θ (((deformationSpaceToBase I).appLE W.1
          ((deformationSpace I).basicOpen (paramChartOf I W.1))
          ((deformationSpace I).basicOpen_le _)).hom a) = LaurentPolynomial.C a) ∧
      θ (((deformationSpace I).presheaf.map
        (homOfLE ((deformationSpace I).basicOpen_le (paramChartOf I W.1))).op).hom
          (paramChartOf I W.1)) = LaurentPolynomial.T (-1) := by
  have hW' : IsAffineOpen (deformationSpaceToBase I ⁻¹ᵁ W.1) :=
    Stacks.RelativeSpec.isAffineOpen_toBase_preimage (extReesSituation I) W
  have := hW'.isLocalization_basicOpen (paramChartOf I W.1)
  let : Algebra Γ(deformationSpace I, deformationSpaceToBase I ⁻¹ᵁ W.1)
      (LaurentPolynomial Γ(X, W.1)) := (chartLaurent I W).toAlgebra
  have := isLocalization_chartLaurent I W
  let θ := IsLocalization.algEquiv (Submonoid.powers (paramChartOf I W.1))
    Γ(deformationSpace I, (deformationSpace I).basicOpen (paramChartOf I W.1))
    (LaurentPolynomial Γ(X, W.1))
  refine ⟨θ.toRingEquiv, fun a => ?_, ?_⟩
  · have h1 : ((deformationSpaceToBase I).appLE W.1
        ((deformationSpace I).basicOpen (paramChartOf I W.1))
        ((deformationSpace I).basicOpen_le _)).hom a =
        algebraMap Γ(deformationSpace I, deformationSpaceToBase I ⁻¹ᵁ W.1)
          Γ(deformationSpace I, (deformationSpace I).basicOpen (paramChartOf I W.1))
          (((deformationSpaceToBase I).app W.1).hom a) := by
      rw [Scheme.Hom.appLE]
      rfl
    rw [h1]
    change θ (algebraMap _ _ _) = _
    rw [AlgEquiv.commutes]
    exact chartLaurent_app I W a
  · change θ (algebraMap _ _ _) = _
    rw [AlgEquiv.commutes]
    exact chartLaurent_paramChartOf I W

/-- **On the chart `π⁻¹W` with `t⁻¹` inverted, the structure map is the inclusion of constants
into the Laurent polynomials**: there is a ring isomorphism of the functions on
`D(t⁻¹) ∩ π⁻¹W` with `Γ(X, W)[T, T⁻¹]` carrying the structure map of the base to `C`. -/
theorem exists_ringEquiv_laurent (W : X.affineOpens) :
    ∃ θ : Γ(deformationSpace I, (deformationSpace I).basicOpen (paramChartOf I W.1)) ≃+*
        LaurentPolynomial Γ(X, W.1),
      ∀ a : Γ(X, W.1), θ (((deformationSpaceToBase I).appLE W.1
          ((deformationSpace I).basicOpen (paramChartOf I W.1))
          ((deformationSpace I).basicOpen_le _)).hom a) = LaurentPolynomial.C a :=
  (exists_ringEquiv_laurent_aux I W).imp fun _ h => h.1

/-- The restriction of `t⁻¹` from the chart `π⁻¹W` to `D(t⁻¹) ∩ π⁻¹W`. -/
abbrev paramBasicOpen (W : X.Opens) :
    Γ(deformationSpace I, (deformationSpace I).basicOpen (paramChartOf I W)) :=
  ((deformationSpace I).presheaf.map
    (homOfLE ((deformationSpace I).basicOpen_le (paramChartOf I W))).op).hom (paramChartOf I W)

/-- **The Laurent chart of `D(t⁻¹) ∩ π⁻¹W`, with `t⁻¹` going to `T⁻¹`**: a ring isomorphism of the
functions on `D(t⁻¹) ∩ π⁻¹W` with `Γ(X, W)[T, T⁻¹]` carrying the structure map of the base to `C`
and `t⁻¹` to `T⁻¹`. -/
theorem exists_ringEquiv_laurent' (W : X.affineOpens) :
    ∃ θ : Γ(deformationSpace I, (deformationSpace I).basicOpen (paramChartOf I W.1)) ≃+*
        LaurentPolynomial Γ(X, W.1),
      (∀ a : Γ(X, W.1), θ (((deformationSpaceToBase I).appLE W.1
          ((deformationSpace I).basicOpen (paramChartOf I W.1))
          ((deformationSpace I).basicOpen_le _)).hom a) = LaurentPolynomial.C a) ∧
      θ (paramBasicOpen I W.1) = LaurentPolynomial.T (-1) :=
  exists_ringEquiv_laurent_aux I W

end Complement

section ComplementProperties

/-- A property of morphisms respecting isomorphisms holds for the restriction `V ⟶ U` of a
morphism to affine opens as soon as it holds for `Spec` of the map on sections. -/
theorem prop_resLE_of_spec (P : MorphismProperty Scheme.{u}) [P.RespectsIso] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : V ≤ f ⁻¹ᵁ U) (h : P (Spec.map (f.appLE U V e))) : P (f.resLE U V e) := by
  have : IsAffine U := hU
  have : IsAffine V := hV
  refine (P.arrow_mk_iso_iff (arrowIsoSpecΓOfIsAffine (f.resLE U V e))).mpr ?_
  have hsq : U.topIso.hom ≫ f.appLE U V e = (f.resLE U V e).appTop ≫ V.topIso.hom :=
    (arrowResLEAppIso f U V e).hom.w
  have happ : (f.resLE U V e).appTop = U.topIso.hom ≫ f.appLE U V e ≫ V.topIso.inv := by
    rw [← Category.assoc, hsq, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have heq : Spec.map (f.resLE U V e).appTop =
      (Spec.map V.topIso.inv ≫ Spec.map (f.appLE U V e)) ≫ Spec.map U.topIso.hom := by
    rw [happ, Spec.map_comp, Spec.map_comp]
  change P (Spec.map (f.resLE U V e).appTop)
  exact heq ▸ (P.cancel_right_of_respectsIso _ _).mpr ((P.cancel_left_of_respectsIso _ _).mpr h)

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- A property respecting isomorphisms and satisfied by `Spec A[T, T⁻¹] ⟶ Spec A` holds for the
restriction `D(t⁻¹) ∩ π⁻¹W ⟶ W` of the deformation space over an affine open `W`. -/
theorem prop_resLE_basicOpen (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (h : ∀ R : CommRingCat.{u},
      P (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : R →+* LaurentPolynomial R))))
    (W : X.affineOpens) :
    P ((deformationSpaceToBase I).resLE W.1
      ((deformationSpace I).basicOpen (paramChartOf I W.1))
      ((deformationSpace I).basicOpen_le _)) := by
  have hW' : IsAffineOpen (deformationSpaceToBase I ⁻¹ᵁ W.1) :=
    Stacks.RelativeSpec.isAffineOpen_toBase_preimage (extReesSituation I) W
  refine prop_resLE_of_spec P _ _ _ W.2 (hW'.basicOpen _) _ ?_
  obtain ⟨θ, hθ⟩ := exists_ringEquiv_laurent I W
  have hfac : (deformationSpaceToBase I).appLE W.1
      ((deformationSpace I).basicOpen (paramChartOf I W.1))
      ((deformationSpace I).basicOpen_le _) =
      CommRingCat.ofHom (LaurentPolynomial.C : Γ(X, W.1) →+* LaurentPolynomial Γ(X, W.1)) ≫
        θ.symm.toCommRingCatIso.hom := by
    ext a
    change _ = θ.symm (LaurentPolynomial.C a)
    rw [← hθ a, RingEquiv.symm_apply_apply]
  rw [hfac, Spec.map_comp]
  exact (P.cancel_left_of_respectsIso _ _).mpr (h _)

/-- Every point of the complement `D(t⁻¹)` lies over an affine open `W` of the base, i.e. in
`D(t⁻¹) ∩ π⁻¹W`. -/
theorem exists_mem_basicOpen_paramChartOf (x : complementOpen I) :
    ∃ W : X.affineOpens, x ∈ (complementOpen I).ι ⁻¹ᵁ
      (deformationSpace I).basicOpen (paramChartOf I W.1) := by
  obtain ⟨W, hW, hxW, -⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show deformationSpaceToBase I ((complementOpen I).ι x) ∈ (⊤ : X.Opens) from trivial)
  refine ⟨⟨W, hW⟩, ?_⟩
  change (complementOpen I).ι x ∈ (deformationSpace I).basicOpen (paramChartOf I W)
  rw [← complementOpen_inf_preimage]
  exact ⟨by simp, hxW⟩

/-- Restricting `D(t⁻¹) ⟶ X` to the opens `D(t⁻¹) ∩ π⁻¹W` factors through an open immersion into
`D(t⁻¹) ∩ π⁻¹W ⊆ D` followed by the restriction of `π` over `W`. -/
theorem ι_comp_complementOpen_ι_comp (W : X.affineOpens) :
    ((complementOpen I).ι ⁻¹ᵁ (deformationSpace I).basicOpen (paramChartOf I W.1)).ι ≫
        (complementOpen I).ι ≫ deformationSpaceToBase I =
      (complementOpen I).ι.resLE ((deformationSpace I).basicOpen (paramChartOf I W.1)) _ le_rfl ≫
        (deformationSpaceToBase I).resLE W.1
          ((deformationSpace I).basicOpen (paramChartOf I W.1))
          ((deformationSpace I).basicOpen_le _) ≫ W.1.ι := by
  rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc ((complementOpen I).ι.resLE _ _ _),
    Scheme.Hom.resLE_comp_ι, Category.assoc]

/-- The inclusion `D(t⁻¹) ⊆ D`, restricted to the open `D(t⁻¹) ∩ π⁻¹W` of `D(t⁻¹)` and the open
`D(t⁻¹) ∩ π⁻¹W` of `D`, is an open immersion. -/
instance isOpenImmersion_complementOpen_resLE (W : X.affineOpens) :
    IsOpenImmersion ((complementOpen I).ι.resLE
      ((deformationSpace I).basicOpen (paramChartOf I W.1)) _ le_rfl) := by
  have : IsOpenImmersion ((complementOpen I).ι.resLE
      ((deformationSpace I).basicOpen (paramChartOf I W.1)) _ le_rfl ≫
        ((deformationSpace I).basicOpen (paramChartOf I W.1)).ι) := by
    rw [Scheme.Hom.resLE_comp_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ ((deformationSpace I).basicOpen (paramChartOf I W.1)).ι

/-- The opens `D(t⁻¹) ∩ π⁻¹W`, for `W` ranging over the affine opens of `X`, cover `D(t⁻¹)`. -/
theorem iSup_preimage_basicOpen_paramChartOf :
    ⨆ W : X.affineOpens, (complementOpen I).ι ⁻¹ᵁ
      (deformationSpace I).basicOpen (paramChartOf I W.1) = ⊤ :=
  eq_top_iff.mpr fun x _ => by
    obtain ⟨W, hW⟩ := exists_mem_basicOpen_paramChartOf I x
    exact Opens.mem_iSup.mpr ⟨W, hW⟩

/-- A property local on the source, respecting isomorphisms, stable under composition and
satisfied by open immersions and by `Spec A[T, T⁻¹] ⟶ Spec A`, holds for `D(t⁻¹) ⟶ X`. -/
theorem prop_complementOpen (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtSource P]
    [P.IsStableUnderComposition] (hι : ∀ {U V : Scheme.{u}} (j : U ⟶ V) [IsOpenImmersion j], P j)
    (h : ∀ R : CommRingCat.{u},
      P (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : R →+* LaurentPolynomial R)))) :
    P ((complementOpen I).ι ≫ deformationSpaceToBase I) := by
  refine IsZariskiLocalAtSource.of_iSup_eq_top _ (iSup_preimage_basicOpen_paramChartOf I)
    fun W => ?_
  rw [ι_comp_complementOpen_ι_comp]
  exact P.comp_mem _ _ (hι _) (P.comp_mem _ _ (prop_resLE_basicOpen I P h W) (hι _))

/-- **The complement of the special fibre of the deformation space is flat over the base.** -/
instance flat_complementOpen : Flat ((complementOpen I).ι ≫ deformationSpaceToBase I) :=
  haveI := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Flat) (Q := RingHom.Flat)
  prop_complementOpen I (@Flat : MorphismProperty Scheme.{u}) (fun _ _ => inferInstance)
    fun _ => inferInstance

/-- The complement of the special fibre of the deformation space is locally of finite type over
the base. -/
instance locallyOfFiniteType_complementOpen :
    LocallyOfFiniteType ((complementOpen I).ι ≫ deformationSpaceToBase I) :=
  haveI := HasRingHomProperty.instIsZariskiLocalAtSource (P := @LocallyOfFiniteType)
    (Q := RingHom.FiniteType)
  prop_complementOpen I (@LocallyOfFiniteType : MorphismProperty Scheme.{u})
    (fun _ _ => inferInstance) fun _ => inferInstance

/-- **The complement of the special fibre of the deformation space has relative dimension one
over the base**: over an affine open `W = Spec A` it is `Spec A[T, T⁻¹]`. -/
theorem relativeDimension_complementOpen :
    AlgebraicGeometry.RelativeDimension ((complementOpen I).ι ≫ deformationSpaceToBase I) 1 := by
  refine AlgebraicGeometry.RelativeDimension.of_opensCover _
    (fun W : X.affineOpens => (complementOpen I).ι ⁻¹ᵁ
      (deformationSpace I).basicOpen (paramChartOf I W.1))
    (exists_mem_basicOpen_paramChartOf I) fun W => ?_
  have hP := prop_resLE_basicOpen I (AlgebraicGeometry.locallyOfFiniteTypeRelativeDimension 1)
    (fun R => ⟨inferInstance, relativeDimension_specMap_laurentC R⟩) W
  obtain ⟨hft, hrd⟩ := hP
  have : MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso (P := @Flat)
  have hfl : Flat ((deformationSpaceToBase I).resLE W.1
      ((deformationSpace I).basicOpen (paramChartOf I W.1))
      ((deformationSpace I).basicOpen_le _)) :=
    prop_resLE_basicOpen I (@Flat : MorphismProperty Scheme.{u}) (fun _ => inferInstance) W
  have hι0 : AlgebraicGeometry.RelativeDimension W.1.ι 0 :=
    (AlgebraicGeometry.locallyQuasiFinite_iff_relativeDimension_zero _).mp inferInstance
  have h1 := AlgebraicGeometry.RelativeDimension.comp_of_flat _ _ hrd hι0
  have h2 := AlgebraicGeometry.RelativeDimension.comp_isOpenImmersion
    ((complementOpen I).ι.resLE ((deformationSpace I).basicOpen (paramChartOf I W.1)) _ le_rfl)
    _ h1
  exact AlgebraicGeometry.RelativeDimension.congr (ι_comp_complementOpen_ι_comp I W).symm h2

end ComplementProperties

end Stacks.Deformation

end
