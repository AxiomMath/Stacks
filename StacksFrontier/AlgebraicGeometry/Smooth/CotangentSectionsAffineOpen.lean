module

public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentBijective
public import StacksFrontier.AlgebraicGeometry.Smooth.CotangentRestrictNatural

/-!
# The sections of `Ω_{X/S}` over an affine open are the Kähler differentials

Let `f : X ⟶ S` be a morphism of schemes and let `Spec A = U ⊆ X` and `Spec R = V ⊆ S` be affine
opens with `f(U) ⊆ V`, so that `A = Γ(X, U)` is an `R = Γ(S, V)`-algebra. This file identifies

`Ω[A⁄R] ≅ Γ(Ω_{X/S}, U)`,

compatibly with the universal differentials on the two sides and uniquely so. That is
[Stacks Project, Tag 01UT].

## Main definitions

* `Stacks.Smooth.universalSectionsDerivation`: the universal differential
  `d_{X/S} : Γ(X, U) → Γ(Ω_{X/S}, U)` as a `Γ(S, V)`-derivation.
* `Stacks.Smooth.cotangentSectionsMap`: the induced `Γ(X, U)`-linear map
  `Ω[Γ(X, U)⁄Γ(S, V)] →ₗ[Γ(X, U)] Γ(Ω_{X/S}, U)`.
* `Stacks.Smooth.cotangentSectionsEquiv`: that map as a linear equivalence, for `U` and `V`
  affine.
* `Stacks.Smooth.toPullbackSectionsHom`: the comparison `Γ(Ω_{X/S}, U) ⟶ Γ((U.ι)^*Ω_{X/S}, ⊤)`.

## Main results

* `Stacks.Smooth.existsUnique_linearEquiv_universalD`: for `U` and `V` affine opens with
  `U ≤ f ⁻¹ᵁ V`, there is exactly one `Γ(X, U)`-linear isomorphism
  `Ω[Γ(X, U)⁄Γ(S, V)] ≃ₗ Γ(Ω_{X/S}, U)` carrying `d a` to `d_{X/S} a`.
* `Stacks.Smooth.bijective_cotangentSectionsMap`: for `U` and `V` affine, the canonical
  comparison map is bijective.
* `Stacks.Smooth.cotangentSectionsMap_unique`: a `Γ(X, U)`-linear map out of
  `Ω[Γ(X, U)⁄Γ(S, V)]` compatible with the differentials is the canonical one.
* `Stacks.Smooth.existsUnique_linearMap_comp_universalD`: for `U` and `V` affine, a
  `Γ(S, V)`-derivation of `Γ(X, U)` with values in a `Γ(X, U)`-module is induced by exactly one
  `Γ(X, U)`-linear map out of `Γ(Ω_{X/S}, U)`.
* `Stacks.Smooth.bijective_toPullbackSections`: for an arbitrary open `U`, the comparison
  `Γ(Ω_{X/S}, U) ⟶ Γ((U.ι)^*Ω_{X/S}, ⊤)` is bijective.

## References

* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
* [Stacks Project, Tag 01UM](https://stacks.math.columbia.edu/tag/01UM)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TensorProduct
open Stacks.Sheaves.RingedSpaceDifferentials

universe u

namespace Stacks.Smooth

/-! ### Restriction of sections along an equality of opens -/

/-- Restriction of sections along an inclusion `O₁ ≤ O₂` of equal opens is bijective. -/
theorem bijective_presheaf_map_of_eq {Y : Scheme.{u}} (M : Y.Modules) {O₁ O₂ : Y.Opens}
    (h : O₁ ≤ O₂) (heq : O₂ = O₁) :
    Function.Bijective (M.presheaf.map (homOfLE h).op).hom := by
  subst heq
  rw [Subsingleton.elim (homOfLE h) (CategoryTheory.CategoryStruct.id _), op_id,
    CategoryTheory.Functor.map_id]
  exact Function.bijective_id

/-! ### The sections of `Ω_{X/S}` over `U` as the global sections of `(U.ι)^*Ω_{X/S}` -/

section Transport

variable {X S : Scheme.{u}} (f : X ⟶ S) {V : S.Opens} {U : X.Opens}

/-- The unit of `U.ι^* ⊣ U.ι_*` at the open `U` is bijective on sections. -/
theorem bijective_pullbackCotangentUnitApp_ι :
    Function.Bijective fun t : Γ(cotangentSheaf f, U) ↦
      (pullbackCotangentUnitApp f U.ι U).hom t := by
  have hfac : ∀ t : Γ(cotangentSheaf f, U),
      (pullbackCotangentUnitApp f U.ι U).hom t
        = (((Scheme.Modules.restrictFunctorIsoPullback U.ι).hom.app
            (cotangentSheaf f)).app (U.ι ⁻¹ᵁ U)).hom
          (((cotangentSheaf f).presheaf.map
            (homOfLE (U.ι.image_preimage_le U)).op).hom t) :=
    fun t ↦ (restrictFunctorIsoPullback_app_map U (cotangentSheaf f) U t).symm
  rw [funext hfac]
  exact (AlgebraicGeometry.sectionsLinearEquivOfIso
      ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app (cotangentSheaf f))
      (U.ι ⁻¹ᵁ U)).bijective.comp
    (bijective_presheaf_map_of_eq (cotangentSheaf f) (U.ι.image_preimage_le U)
      (by rw [U.ι_preimage_self, U.ι_image_top]))

/-- The comparison `Γ(Ω_{X/S}, U) ⟶ Γ((U.ι)^*Ω_{X/S}, ⊤)`: the unit of `U.ι^* ⊣ U.ι_*` at `U`,
followed by restriction of sections to the top open of `U`. -/
noncomputable def toPullbackSectionsHom :
    Γ(cotangentSheaf f, U) →+ Γ(pullbackCotangentSheaf f U.ι, (⊤ : (U : Scheme.{u}).Opens)) :=
  ((pullbackCotangentSheaf f U.ι).presheaf.map
      (homOfLE (le_of_eq U.ι_preimage_self.symm)).op).hom.comp
    (pullbackCotangentUnitApp f U.ι U).hom

/-- The comparison carries the universal differential to its pullback along `U.ι`. -/
theorem toPullbackSectionsHom_universalD (b : Γ(X, U)) :
    toPullbackSectionsHom f (universalD f U b)
      = pullbackD f U.ι U (le_of_eq U.ι_preimage_self.symm) b :=
  rfl

/-- The comparison is semilinear over `U.ι.appLE U ⊤`, that is over the comparison ring
isomorphism `AlgebraicGeometry.Scheme.Opens.topIso` between `Γ(X, U)` and `Γ(U, ⊤)`. -/
theorem toPullbackSectionsHom_smul (b : Γ(X, U)) (s : Γ(cotangentSheaf f, U)) :
    toPullbackSectionsHom f (b • s)
      = (U.ι.appLE U ⊤ (le_of_eq U.ι_preimage_self.symm)).hom b • toPullbackSectionsHom f s := by
  change ((pullbackCotangentSheaf f U.ι).presheaf.map
      (homOfLE (le_of_eq U.ι_preimage_self.symm)).op).hom
    ((pullbackCotangentUnitApp f U.ι U).hom (b • s)) = _
  rw [pullbackCotangentUnitApp_smul, Scheme.Modules.map_smul]
  rfl

/-- The comparison `Stacks.Smooth.toPullbackSectionsHom` is bijective. -/
theorem bijective_toPullbackSections :
    Function.Bijective (toPullbackSectionsHom f (U := U)) :=
  (bijective_presheaf_map_of_eq (pullbackCotangentSheaf f U.ι)
      (le_of_eq U.ι_preimage_self.symm) U.ι_preimage_self).comp
    (bijective_pullbackCotangentUnitApp_ι f)

/-- `Stacks.Smooth.toPullbackSectionsHom` as an additive equivalence. -/
noncomputable def toPullbackSectionsAddEquiv :
    Γ(cotangentSheaf f, U) ≃+ Γ(pullbackCotangentSheaf f U.ι, (⊤ : (U : Scheme.{u}).Opens)) :=
  AddEquiv.ofBijective (toPullbackSectionsHom f) (bijective_toPullbackSections f)

end Transport

/-! ### The universal differential on an open as a derivation -/

section Derivation

variable {X S : Scheme.{u}} (f : X ⟶ S) {V : S.Opens} {U : X.Opens}

/-- For `U ≤ f ⁻¹ᵁ V`, the universal differential `d_{X/S} : Γ(X, U) → Γ(Ω_{X/S}, U)` as a
derivation of `Γ(X, U)` over `Γ(S, V)`. -/
noncomputable def universalSectionsDerivation (hUV : U ≤ f ⁻¹ᵁ V) :
    letI := algebraAppLE f hUV
    letI := moduleOfAppLE f hUV Γ(cotangentSheaf f, U)
    Derivation Γ(S, V) Γ(X, U) Γ(cotangentSheaf f, U) :=
  letI := algebraAppLE f hUV
  letI := moduleOfAppLE f hUV Γ(cotangentSheaf f, U)
  { toFun := universalD f U
    map_add' := map_add _
    map_smul' := fun r b ↦ by
      rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, universalD_mul,
        universalD_appLE f U hUV r, smul_zero, add_zero]
      rfl
    map_one_eq_zero' := universalD_one f U
    leibniz' := universalD_mul f U }

/-- The underlying map of `Stacks.Smooth.universalSectionsDerivation` is the universal
differential. -/
@[simp]
theorem universalSectionsDerivation_apply (hUV : U ≤ f ⁻¹ᵁ V) (b : Γ(X, U)) :
    letI := algebraAppLE f hUV
    letI := moduleOfAppLE f hUV Γ(cotangentSheaf f, U)
    universalSectionsDerivation f hUV b = universalD f U b :=
  rfl

/-- For `U ≤ f ⁻¹ᵁ V`, the `Γ(X, U)`-linear map

`Ω[Γ(X, U)⁄Γ(S, V)] →ₗ[Γ(X, U)] Γ(Ω_{X/S}, U)`

induced by the universal differential. -/
noncomputable def cotangentSectionsMap (hUV : U ≤ f ⁻¹ᵁ V) :
    letI := algebraAppLE f hUV
    Ω[Γ(X, U)⁄Γ(S, V)] →ₗ[Γ(X, U)] Γ(cotangentSheaf f, U) :=
  letI := algebraAppLE f hUV
  letI := moduleOfAppLE f hUV Γ(cotangentSheaf f, U)
  letI := isScalarTowerOfAppLE f hUV Γ(cotangentSheaf f, U)
  (universalSectionsDerivation f hUV).liftKaehlerDifferential

/-- `Stacks.Smooth.cotangentSectionsMap` carries the Kähler differential `d a` to the universal
differential `d_{X/S} a`. -/
@[simp]
theorem cotangentSectionsMap_D (hUV : U ≤ f ⁻¹ᵁ V) (b : Γ(X, U)) :
    letI := algebraAppLE f hUV
    cotangentSectionsMap f hUV (KaehlerDifferential.D Γ(S, V) Γ(X, U) b)
      = universalD f U b := by
  let := algebraAppLE f hUV
  let := moduleOfAppLE f hUV Γ(cotangentSheaf f, U)
  let := isScalarTowerOfAppLE f hUV Γ(cotangentSheaf f, U)
  exact Derivation.liftKaehlerDifferential_comp_D (universalSectionsDerivation f hUV) b

/-- A `Γ(X, U)`-linear map `Ω[Γ(X, U)⁄Γ(S, V)] → Γ(Ω_{X/S}, U)` carrying `d a` to `d_{X/S} a` is
`Stacks.Smooth.cotangentSectionsMap`. -/
theorem cotangentSectionsMap_unique (hUV : U ≤ f ⁻¹ᵁ V) :
    letI := algebraAppLE f hUV
    ∀ φ : Ω[Γ(X, U)⁄Γ(S, V)] →ₗ[Γ(X, U)] Γ(cotangentSheaf f, U),
      (∀ b : Γ(X, U), φ (KaehlerDifferential.D Γ(S, V) Γ(X, U) b) = universalD f U b) →
        φ = cotangentSectionsMap f hUV := by
  let := algebraAppLE f hUV
  exact fun φ hφ ↦ kaehlerDifferential_linearMap_ext _ _ fun b ↦
    (hφ b).trans (cotangentSectionsMap_D f hUV b).symm

end Derivation

/-! ### The corepresentation of derivations by `Γ(Ω_{X/S}, U)` -/

section Corepresentation

variable {X S : Scheme.{u}} (f : X ⟶ S) {V : S.Opens} {U : X.Opens}

/-- Let `U` be an affine open of `X` and `V` an affine open of `S` with `U ≤ f ⁻¹ᵁ V`, and let `M`
be a `Γ(X, U)`-module. A map `δ : Γ(X, U) → M` which is additive, kills the sections coming from
`Γ(S, V)` and satisfies the Leibniz rule is induced along the universal differential by exactly
one `Γ(X, U)`-linear map `Γ(Ω_{X/S}, U) → M`. -/
theorem existsUnique_linearMap_comp_universalD (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) (M : Type u) [AddCommGroup M] [Module Γ(X, U) M] (δ : Γ(X, U) → M)
    (hadd : ∀ x y, δ (x + y) = δ x + δ y)
    (hbase : ∀ r : Γ(S, V), δ ((f.appLE V U hUV).hom r) = 0)
    (hleib : ∀ x y, δ (x * y) = x • δ y + y • δ x) :
    ∃! θ : Γ(cotangentSheaf f, U) →ₗ[Γ(X, U)] M,
      ∀ b : Γ(X, U), θ (universalD f U b) = δ b := by
  have hUa : IsAffine (U : Scheme.{u}) := hU
  set ρ := U.topIso.symm.commRingCatIsoToRingEquiv
  let : Module Γ((U : Scheme.{u}), (⊤ : (U : Scheme.{u}).Opens)) M :=
    Module.compHom M (U.topIso.hom.hom : Γ((U : Scheme.{u}),
      (⊤ : (U : Scheme.{u}).Opens)) →+* Γ(X, U))
  have hM : ∀ (r : Γ(X, U)) (m : M), r • m = ρ r • m := fun r m ↦ by
    change r • m = U.topIso.hom.hom (U.topIso.inv.hom r) • m
    rw [← CommRingCat.comp_apply, U.topIso.inv_hom_id]
    rfl
  have hρ : ∀ r : Γ(X, U),
      ρ r = (U.ι.appLE U ⊤ (le_of_eq U.ι_preimage_self.symm)).hom r := fun r ↦ by
    rw [opens_ι_appLE_top (W := U)]
    rfl
  refine existsUnique_linearMap_of_ringEquiv ρ hM (toPullbackSectionsAddEquiv f)
    (fun r x ↦ ?_) (universalD f U) (pullbackD f U.ι U (le_of_eq U.ι_preimage_self.symm))
    (fun b ↦ toPullbackSectionsHom_universalD f b) δ
    (existsUnique_linearMap_of_leibniz f U.ι M hV hU hUV (le_of_eq U.ι_preimage_self.symm) δ hadd
      hbase fun x y ↦ ?_)
  · rw [hρ]
    exact toPullbackSectionsHom_smul f r x
  · rw [hleib x y, hM, hM, hρ, hρ]

end Corepresentation

/-! ### The isomorphism `Ω[A⁄R] ≃ₗ[A] Γ(Ω_{X/S}, U)` -/

section Main

variable {X S : Scheme.{u}} (f : X ⟶ S) {V : S.Opens} {U : X.Opens}

/-- For `Spec A = U ⊆ X` and `Spec R = V ⊆ S` affine opens with `f(U) ⊆ V`, the canonical
`A`-linear map `Ω[A⁄R] → Γ(Ω_{X/S}, U)` is bijective. -/
theorem bijective_cotangentSectionsMap (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    letI := algebraAppLE f hUV
    Function.Bijective (cotangentSectionsMap f hUV) := by
  let := algebraAppLE f hUV
  let := moduleOfAppLE f hUV Γ(cotangentSheaf f, U)
  let := isScalarTowerOfAppLE f hUV Γ(cotangentSheaf f, U)
  obtain ⟨θ, hθ, -⟩ := existsUnique_linearMap_comp_universalD f hU hV hUV
    Ω[Γ(X, U)⁄Γ(S, V)] (KaehlerDifferential.D Γ(S, V) Γ(X, U))
    (map_add _) (KaehlerDifferential.D Γ(S, V) Γ(X, U)).map_algebraMap
    (KaehlerDifferential.D Γ(S, V) Γ(X, U)).leibniz
  have hleft : θ ∘ₗ cotangentSectionsMap f hUV = LinearMap.id := by
    refine kaehlerDifferential_linearMap_ext _ _ fun b ↦ ?_
    change θ (cotangentSectionsMap f hUV (KaehlerDifferential.D Γ(S, V) Γ(X, U) b)) = _
    rw [cotangentSectionsMap_D f hUV b, hθ b]
    rfl
  have hright : cotangentSectionsMap f hUV ∘ₗ θ = LinearMap.id := by
    obtain ⟨ξ, -, huniq⟩ := existsUnique_linearMap_comp_universalD f hU hV hUV
      Γ(cotangentSheaf f, U) (universalD f U) (fun x y ↦ map_add _ x y)
      (universalD_appLE f U hUV) (universalD_mul f U)
    refine (huniq _ fun b ↦ ?_).trans (huniq _ fun _ ↦ rfl).symm
    change cotangentSectionsMap f hUV (θ (universalD f U b)) = universalD f U b
    rw [hθ b, cotangentSectionsMap_D f hUV b]
  exact ⟨Function.LeftInverse.injective (g := θ) fun x ↦ LinearMap.congr_fun hleft x,
    fun y ↦ ⟨θ y, LinearMap.congr_fun hright y⟩⟩

/-- For `Spec A = U ⊆ X` and `Spec R = V ⊆ S` affine opens with `f(U) ⊆ V`, the `A`-linear
isomorphism `Ω[A⁄R] ≃ₗ Γ(Ω_{X/S}, U)` carrying `d a` to `d_{X/S} a`. -/
noncomputable def cotangentSectionsEquiv (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    letI := algebraAppLE f hUV
    Ω[Γ(X, U)⁄Γ(S, V)] ≃ₗ[Γ(X, U)] Γ(cotangentSheaf f, U) :=
  letI := algebraAppLE f hUV
  LinearEquiv.ofBijective (cotangentSectionsMap f hUV)
    (bijective_cotangentSectionsMap f hU hV hUV)

/-- The underlying map of `Stacks.Smooth.cotangentSectionsEquiv` is
`Stacks.Smooth.cotangentSectionsMap`. -/
theorem cotangentSectionsEquiv_apply (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    letI := algebraAppLE f hUV
    ∀ x, cotangentSectionsEquiv f hU hV hUV x = cotangentSectionsMap f hUV x :=
  fun _ ↦ rfl

/-- `Stacks.Smooth.cotangentSectionsEquiv` is compatible with the differentials. -/
@[simp]
theorem cotangentSectionsEquiv_D (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) (b : Γ(X, U)) :
    letI := algebraAppLE f hUV
    cotangentSectionsEquiv f hU hV hUV (KaehlerDifferential.D Γ(S, V) Γ(X, U) b)
      = universalD f U b :=
  cotangentSectionsMap_D f hUV b

/-- Let `f : X ⟶ S` be a morphism of schemes. For any pair of affine opens `Spec A = U ⊆ X` and
`Spec R = V ⊆ S` with `f(U) ⊆ V` there is a unique isomorphism

`Ω[A⁄R] ≃ₗ[A] Γ(Ω_{X/S}, U)`

compatible with `d_{X/S}` and with `d : A → Ω[A⁄R]`. -/
@[stacks 01UT "unique isomorphism Γ(U, Ω_{X/S}) = Ω_{A/R} compatible with the differentials"]
theorem existsUnique_linearEquiv_universalD (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    letI := algebraAppLE f hUV
    ∃! e : Ω[Γ(X, U)⁄Γ(S, V)] ≃ₗ[Γ(X, U)] Γ(cotangentSheaf f, U),
      ∀ b : Γ(X, U), e (KaehlerDifferential.D Γ(S, V) Γ(X, U) b) = universalD f U b := by
  let := algebraAppLE f hUV
  refine ⟨cotangentSectionsEquiv f hU hV hUV, cotangentSectionsEquiv_D f hU hV hUV, fun e he ↦ ?_⟩
  exact LinearEquiv.toLinearMap_injective <| (cotangentSectionsMap_unique f hUV _ he).trans
    (cotangentSectionsMap_unique f hUV _ (cotangentSectionsEquiv_D f hU hV hUV)).symm

end Main

end Stacks.Smooth

end
