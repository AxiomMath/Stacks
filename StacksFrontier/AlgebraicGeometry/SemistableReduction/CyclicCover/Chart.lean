module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.Construction
public import StacksCore.Tactic.StacksAttribute

/-!
# The affine charts of a cyclic cover

Let `k` be a field, `f : Z ⟶ Spec k`, `L` an invertible `𝒪_Z`-module, `φ : Symⁿ L ≅ 𝒪_Z`, `S` a
`k`-algebra and `c ∈ S`, and let `p : X ⟶ Z_S` be the cyclic cover
`X = Spec_{Z_S}(Sym(L_S)/(φ - c))` of
`StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.Construction`.

Let `U = Spec A` be an affine open of `Z` on which `Γ(L, U)` has a basis `s`, and put `f = φ(sⁿ)`.
This file proves the local description of [Stacks, Tag 0CEH]:

`p⁻¹(U_S) = Spec((A ⊗_k S)[x]/(xⁿ - c f))`,

as an isomorphism of arrows between `p` restricted over `U_S` and the spectrum of the structure
map `A ⊗_k S → (A ⊗_k S)[x]/(xⁿ - c f)`.

## Main definitions

* `Stacks.CyclicCover.chartCoeff`: the function `f = φ(sⁿ)` on `U`.
* `Stacks.CyclicCover.coverOpenIso`: the inverse image of `π⁻¹U` in `X` is `Spec` of the chart
  ring.
* `Stacks.CyclicCover.baseChangeOpenIso`: `U_S = Spec(A ⊗_k S)`.
* `Stacks.CyclicCover.coverMapArrowIso`: **the local description of `p`.**

## Main results

* `Stacks.CyclicCover.rootSectionOn_eq`, `Stacks.CyclicCover.rootCoeff_mul_chartCoeff`: on `U`,
  `φ⁻¹(1) = g sⁿ` with `g f = 1`.
* `Stacks.CyclicCover.chartOpen_ι_rootMap`: over `π⁻¹U = Spec A[T]`, the function `φ⁻¹(1)` is
  `g Tⁿ`.

## References

* [Stacks Project, Tag 0CEH](https://stacks.math.columbia.edu/tag/0CEH)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace Polynomial
open scoped TensorProduct

universe u

namespace Stacks.CyclicCover

variable {k : Type u} [Field k] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k))

/-- The `k`-algebra structure of the functions on an open of `Z`. -/
def sectionsStructure (U : Z.Opens) : CommRingCat.of k ⟶ Γ(Z, U) :=
  (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)

/-- On an affine open `U` of `Z`, the composite `U ⟶ Z ⟶ Spec k` is
`U ≅ Spec Γ(Z, U) ⟶ Spec k`. -/
theorem ι_comp_eq {U : Z.Opens} (hU : IsAffineOpen U) :
    U.ι ≫ f = hU.isoSpec.hom ≫ Spec.map (sectionsStructure f U) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of k))) hU (by simp)
  rw [← hU.isoSpec_inv_ι, Category.assoc] at h
  rw [sectionsStructure, Spec.map_comp, ← cancel_epi hU.isoSpec.inv, Iso.inv_hom_id_assoc, ← h,
    IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]

section Base

variable (S : Type u) [CommRing S] [Algebra k S] {U : Z.Opens} (hU : IsAffineOpen U)

/-- The projection `Z_S ⟶ Z`. -/
abbrev baseChangeFst : baseChange f S ⟶ Z := pullback.fst _ _

/-- The projection `Z_S ⟶ Spec S`. -/
abbrev baseChangeSnd : baseChange f S ⟶ Spec (.of S) := pullback.snd _ _

/-- The open `U_S` of `Z_S` over an open `U` of `Z`. -/
abbrev baseChangeOpen (U : Z.Opens) : (baseChange f S).Opens := baseChangeFst f S ⁻¹ᵁ U

/-- The open of a pullback `X ×_Y T` over an open `U` of `X` is the pullback of `h : T ⟶ Y` along
any `q : W ⟶ Y` through which `U ⟶ X ⟶ Y` factors by an isomorphism `U ≅ W`. -/
private theorem isPullback_fst_preimage {X Y T W : Scheme.{u}} (g : X ⟶ Y) (h : T ⟶ Y)
    (U : X.Opens) (e : U.toScheme ≅ W) (q : W ⟶ Y) (he : U.ι ≫ g = e.hom ≫ q) :
    IsPullback (pullback.fst g h ∣_ U ≫ e.hom)
      ((pullback.fst g h ⁻¹ᵁ U).ι ≫ pullback.snd g h) q h := by
  have P1 := (isPullback_morphismRestrict (pullback.fst g h) U).paste_vert
    (IsPullback.of_hasPullback g h)
  refine IsPullback.of_iso P1 (Iso.refl _) e (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · rw [Iso.refl_hom, Category.comp_id, he]
  · simp

/-- For an affine open `U` of `Z`, the open `U_S` is the pullback of `Spec Γ(Z, U) ⟶ Spec k`
along `Spec S ⟶ Spec k`. -/
theorem isPullback_baseChangeOpen :
    IsPullback (baseChangeFst f S ∣_ U ≫ hU.isoSpec.hom)
      ((baseChangeOpen f S U).ι ≫ baseChangeSnd f S)
      (Spec.map (sectionsStructure f U)) (Spec.map (CommRingCat.ofHom (algebraMap k S))) := by
  exact isPullback_fst_preimage f _ U hU.isoSpec _ (ι_comp_eq f hU)

/-- `Spec (Γ(Z, U) ⊗_k S)` is the pullback of `Spec Γ(Z, U) ⟶ Spec k` along
`Spec S ⟶ Spec k`. -/
theorem isPullback_tensor :
    letI := (sectionsStructure f U).hom.toAlgebra
    IsPullback (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := k) (A := Γ(Z, U)) (B := S))))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := k) (A := Γ(Z, U))
        (B := S)).toRingHom))
      (Spec.map (sectionsStructure f U)) (Spec.map (CommRingCat.ofHom (algebraMap k S))) := by
  let := (sectionsStructure f U).hom.toAlgebra
  exact isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct k Γ(Z, U) S)

end Base

section Chart

variable {L : Z.Modules}
  [SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L] {n : ℕ}
  (φ : (situation f L).symmetricAlgebra.piece (n : ℤ) ≅ SheafOfModules.unit Z.ringCatSheaf)
  (U : Z.affineOpens) (b : Module.Basis PUnit.{u + 1} Γ(Z, U.1) Γ(L, U.1))

/-- The restriction of `φ⁻¹(1)` to `U`. -/
def rootSectionOn : ((situation f L).symmetricAlgebra.piece (n : ℤ)).val.obj (op U.1) :=
  ((situation f L).symmetricAlgebra.piece (n : ℤ)).val.map (homOfLE le_top).op (rootSection f φ)

/-- Through the basis `s`, the function of `φ⁻¹(1)|_U` on the total space is a monomial `g Tⁿ`. -/
theorem exists_rootCoeff : ∃ g : Γ(Z, U.1),
    (situation f L).polynomialSectionsRingEquiv U b (monomial n g) =
      (situation f L).totalFunction n U.1 (rootSectionOn f φ U) :=
  ((situation f L).exists_totalFunction_iff U b n _).mp ⟨_, rfl⟩

/-- The coefficient `g` with `φ⁻¹(1)|_U = g sⁿ`. -/
def rootCoeff : Γ(Z, U.1) := (exists_rootCoeff f φ U b).choose

/-- Through the basis `s`, the function of `φ⁻¹(1)|_U` on the total space is `rootCoeff • Tⁿ`. -/
theorem rootCoeff_spec : (situation f L).polynomialSectionsRingEquiv U b
    (monomial n (rootCoeff f φ U b)) = (situation f L).totalFunction n U.1 (rootSectionOn f φ U) :=
  (exists_rootCoeff f φ U b).choose_spec

/-- The restriction of `φ⁻¹(1)` to the chart over `U`. -/
theorem rootFunction_restrict :
    (totalSpace f L).presheaf.map (homOfLE le_top : totalSpaceToBase f L ⁻¹ᵁ U.1 ⟶ ⊤).op
      (rootFunction f φ) = (situation f L).totalFunction n U.1 (rootSectionOn f φ U) := by
  rw [rootFunction, ← CommRingCat.comp_apply, ← Functor.map_comp]
  exact (situation f L).totalFunction_map n le_top _ _


/-- The projection `π : 𝕃 ⟶ Z` of the total space is affine. -/
instance : IsAffineHom (totalSpaceToBase f L) :=
  Stacks.RelativeSpec.isAffineHom_toBase _

/-- The chart `π⁻¹U` of the total space over `U`. -/
abbrev chartOpen : (totalSpace f L).Opens := totalSpaceToBase f L ⁻¹ᵁ U.1

/-- The chart `π⁻¹U` is an affine open. -/
theorem isAffineOpen_chartOpen : IsAffineOpen (chartOpen f (L := L) U) := U.2.preimage _

/-- `π⁻¹U ≅ Spec Γ(Z, U)[T]`, through the basis `b`. -/
def chartOpenIso : (chartOpen f (L := L) U).toScheme ≅ Spec (.of Γ(Z, U.1)[X]) :=
  (isAffineOpen_chartOpen f U).isoSpec ≪≫
    Scheme.Spec.mapIso ((situation f L).polynomialSectionsRingEquiv U b).toCommRingCatIso.op

/-- The isomorphism `π⁻¹U ≅ Spec Γ(Z, U)[T]` is `π⁻¹U ⟶ Spec Γ(π⁻¹U)` followed by the
spectrum of `Γ(Z, U)[T] ≃ Γ(π⁻¹U)`. -/
theorem chartOpenIso_hom : (chartOpenIso f U b).hom = (chartOpen f (L := L) U).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom ((situation f L).polynomialSectionsRingEquiv U b).toRingHom) := by
  simp [chartOpenIso, IsAffineOpen.isoSpec_hom]

/-- The pullback of a scalar `y ∈ k` to the total space, restricted to `π⁻¹V`, is the pullback
along `π` of its image in `Γ(Z, V)`. -/
theorem appTop_comp_map_eq (V : Z.Opens) (y : Γ(Spec (.of k), ⊤)) :
    (totalSpace f L).presheaf.map (homOfLE le_top : totalSpaceToBase f L ⁻¹ᵁ V ⟶ ⊤).op
      ((totalSpaceToBase f L ≫ f).appTop y) =
    (totalSpaceToBase f L).app V (f.appLE ⊤ V (by simp) y) :=
  (congrArg (fun φ => φ (f.app ⊤ y)) (congrArg CommRingCat.Hom.hom
    (Scheme.Hom.naturality (totalSpaceToBase f L) (homOfLE (le_top : V ≤ f ⁻¹ᵁ ⊤)).op))).symm

/-- Over `π⁻¹U = Spec Γ(Z, U)[T]`, the morphism `rootMap` given by `φ⁻¹(1)` is the spectrum
of `T ↦ g Tⁿ`, with `g = rootCoeff`. -/
theorem chartOpen_ι_rootMap :
    letI := (sectionsStructure f U.1).hom.toAlgebra
    (chartOpen f (L := L) U).ι ≫ rootMap f φ =
    (chartOpenIso f U b).hom ≫ Spec.map (CommRingCat.ofHom (totalHom k n (rootCoeff f φ U b))) := by
  let := (sectionsStructure f U.1).hom.toAlgebra
  rw [chartOpenIso_hom, Category.assoc, ← Spec.map_comp, rootMap, ← Category.assoc,
    ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top, Category.assoc, ← Spec.map_comp]
  congr 2
  refine CommRingCat.hom_ext (Polynomial.ringHom_ext (fun r => ?_) ?_)
  · have h1 := (situation f L).polynomialSectionsRingEquiv_C U b (algebraMap k Γ(Z, U.1) r)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, coe_eval₂RingHom,
      eval₂_C, totalHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C,
      Polynomial.algebraMap_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe] at h1 ⊢
    rw [h1, totalStructure, RingHom.algebraMap_toAlgebra, sectionsStructure]
    exact appTop_comp_map_eq f U.1 _
  · simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, coe_eval₂RingHom,
      eval₂_X, totalHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X,
      RingEquiv.toRingHom_eq_coe, C_mul_X_pow_eq_monomial]
    rw [rootCoeff_spec, ← rootFunction_restrict]


/-- The section `sⁿ` of `Symⁿ L` over `U`, for the basis `s` of `Γ(L, U)`. -/
def basisPow : ((situation f L).symmetricAlgebra.piece (n : ℤ)).val.obj (op U.1) :=
  Stacks.SymAlgSections.pieceUnit L U.2 n
    ⟨(SymmetricAlgebra.ι Γ(Z, U.1) Γ(L, U.1) (b PUnit.unit)) ^ n,
      Submodule.pow_mem_pow _ (LinearMap.mem_range_self _ _) n⟩

/-- The map `pieceUnit` from `Symⁿ Γ(L, U)` to the sections of `Symⁿ L` over `U` is
`Γ(Z, U)`-linear. -/
theorem pieceUnit_smul (a : Γ(Z, U.1))
    (y : SymPow.symmetricPower n Γ(Z, U.1) Γ(L, U.1)) :
    Stacks.SymAlgSections.pieceUnit L U.2 n (a • y) =
      id (α := Z.ringCatSheaf.obj.obj (op U.1)) a • Stacks.SymAlgSections.pieceUnit L U.2 n y :=
  (PresheafOfModules.Hom.app (PresheafOfModules.sheafifyUnit (R := Z.ringCatSheaf)
    (𝟙 Z.ringCatSheaf.obj) (PresheafOfModules.symPowInt (n : ℤ) L.val)) (op U.1)).hom.map_smul a y


/-- A section of `Symⁿ L` over `U` is determined by its function on the total space over `U`. -/
theorem totalFunction_injective :
    Function.Injective ((situation f L).totalFunction n U.1) := by
  intro x y h
  obtain ⟨x', rfl⟩ := (Stacks.SymAlgSections.pieceUnit L U.2 n).surjective x
  obtain ⟨y', rfl⟩ := (Stacks.SymAlgSections.pieceUnit L U.2 n).surjective y
  rw [← (situation f L).symSectionsRingEquiv_coe, ← (situation f L).symSectionsRingEquiv_coe] at h
  exact congrArg _ (Subtype.ext (((situation f L).symSectionsRingEquiv U).injective h))

/-- Under `Γ(Z, U)[T] ≃ Sym Γ(L, U)`, the monomial `g Tⁿ` corresponds to `g sⁿ`. -/
theorem polynomialAlgEquiv_symm_monomial (g : Γ(Z, U.1)) :
    ((situation f L).polynomialAlgEquiv U b).symm (monomial n g) =
      g • (SymmetricAlgebra.ι Γ(Z, U.1) Γ(L, U.1) (b PUnit.unit)) ^ n := by
  rw [AlgEquiv.symm_apply_eq, map_smul, map_pow, (situation f L).polynomialAlgEquiv_ι,
    Polynomial.smul_eq_C_mul, C_mul_X_pow_eq_monomial]

/-- **`φ⁻¹(1)|_U = g sⁿ`.** -/
theorem rootSectionOn_eq : rootSectionOn f φ U =
    id (α := Z.ringCatSheaf.obj.obj (op U.1)) (rootCoeff f φ U b) • basisPow f U b := by
  apply totalFunction_injective f U
  refine (rootCoeff_spec f φ U b).symm.trans ?_
  refine Eq.trans ?_ (congrArg _ (pieceUnit_smul U _ _))
  rw [← (situation f L).symSectionsRingEquiv_coe]
  show ((situation f L).symSectionsRingEquiv U) (((situation f L).polynomialAlgEquiv U b).symm
    (monomial n (rootCoeff f φ U b))) = _
  rw [polynomialAlgEquiv_symm_monomial]
  rfl


/-- The coefficient `f = φ(sⁿ)` of the source, a function on `U`. -/
def chartCoeff : Γ(Z, U.1) := φ.hom.val.app (op U.1) (basisPow f U b)

/-- `φ(φ⁻¹(1)|_U) = 1` in `Γ(Z, U)`. -/
theorem hom_rootSectionOn :
    (show Γ(Z, U.1) from φ.hom.val.app (op U.1) (rootSectionOn f φ U)) = 1 := by
  have h := PresheafOfModules.naturality_apply φ.inv.val (homOfLE (le_top : U.1 ≤ ⊤)).op
    (1 : Γ(Z, ⊤))
  rw [rootSectionOn, rootSection, ← h]
  have h2 := congrArg (fun ψ => ψ.val.app (op U.1)
    ((SheafOfModules.unit Z.ringCatSheaf).val.map (homOfLE (le_top : U.1 ≤ ⊤)).op (1 : Γ(Z, ⊤))))
    φ.inv_hom_id
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.hom_comp,
    SheafOfModules.id_val, PresheafOfModules.id_app, ModuleCat.hom_id] at h2
  exact h2.trans (Z.ringCatSheaf.obj.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom.map_one


/-- **`g f = 1`**: the coefficient of `φ⁻¹(1)` in the basis `sⁿ` is the inverse of `φ(sⁿ)`. -/
theorem rootCoeff_mul_chartCoeff : rootCoeff f φ U b * chartCoeff f φ U b = 1 := by
  have h := hom_rootSectionOn f φ U
  rw [rootSectionOn_eq f φ U b] at h
  exact Eq.trans ((φ.hom.val.app (op U.1)).hom.map_smul _ _).symm h


variable (S : Type u) [CommRing S] [Algebra k S] (c : S)

/-- The projection `X ⟶ 𝕃`. -/
abbrev coverFst : cover f φ S c ⟶ totalSpace f L := pullback.fst _ _

/-- The projection `X ⟶ Spec S`. -/
abbrev coverSnd : cover f φ S c ⟶ Spec (.of S) := pullback.snd _ _

/-- The open of `X` over the chart `π⁻¹U`. -/
abbrev coverOpen : (cover f φ S c).Opens := coverFst f φ S c ⁻¹ᵁ chartOpen f (L := L) U

/-- The open of `X` over `π⁻¹U` is the pullback of `Spec` of `T ↦ g Tⁿ` along the point
`Spec S ⟶ 𝔸¹` given by `c`. -/
theorem isPullback_coverOpen :
    letI := (sectionsStructure f U.1).hom.toAlgebra
    IsPullback (coverFst f φ S c ∣_ chartOpen f U ≫ (chartOpenIso f U b).hom)
      ((coverOpen f φ U S c).ι ≫ coverSnd f φ S c)
      (Spec.map (CommRingCat.ofHom (totalHom k n (rootCoeff f φ U b))))
      (Spec.map (CommRingCat.ofHom (pointHom (k := k) c))) := by
  let := (sectionsStructure f U.1).hom.toAlgebra
  exact isPullback_fst_preimage _ _ _ (chartOpenIso f U b) _ (chartOpen_ι_rootMap f φ U b)

/-- `Spec (A ⊗_k S)[x]/(xⁿ - c f)` is the pullback of `Spec` of `T ↦ g Tⁿ` along the point
`Spec S ⟶ 𝔸¹` given by `c`, where `g f = 1`. -/
theorem isPullback_chartRing :
    letI := (sectionsStructure f U.1).hom.toAlgebra
    IsPullback (Spec.map (CommRingCat.ofHom (chartLeft k n (chartCoeff f φ U b) c)))
      (Spec.map (CommRingCat.ofHom (chartRight k n (chartCoeff f φ U b) c)))
      (Spec.map (CommRingCat.ofHom (totalHom k n (rootCoeff f φ U b))))
      (Spec.map (CommRingCat.ofHom (pointHom (k := k) c))) := by
  let := (sectionsStructure f U.1).hom.toAlgebra
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_chart (rootCoeff_mul_chartCoeff f φ U b))

/-- **The chart of the cyclic cover**: over `π⁻¹U`, the cover is `Spec (A ⊗_k S)[x]/(xⁿ - c f)`. -/
def coverOpenIso :
    letI := (sectionsStructure f U.1).hom.toAlgebra
    (coverOpen f φ U S c).toScheme ≅ Spec (.of (chartRing k n (chartCoeff f φ U b) c)) :=
  letI := (sectionsStructure f U.1).hom.toAlgebra
  (isPullback_coverOpen f φ U b S c).isoIsPullback _ _ (isPullback_chartRing f φ U b S c)


/-- Under `π⁻¹U ≅ Spec Γ(Z, U)[T]` and `U ≅ Spec Γ(Z, U)`, the projection `π` is the spectrum
of the inclusion of constants. -/
theorem chartOpenIso_hom_comp_C :
    letI := (sectionsStructure f U.1).hom.toAlgebra
    (chartOpenIso f U b).hom ≫ Spec.map (CommRingCat.ofHom (C : Γ(Z, U.1) →+* Γ(Z, U.1)[X])) =
      (totalSpaceToBase f L ∣_ U.1) ≫ U.2.isoSpec.hom := by
  rw [chartOpenIso_hom, Category.assoc, ← Spec.map_comp,
    show (U.2 : IsAffineOpen U.1).isoSpec.hom = U.1.toSpecΓ from IsAffineOpen.isoSpec_hom _,
    ← Scheme.Opens.toSpecΓ_naturality]
  congr 2
  ext r
  exact (situation f L).polynomialSectionsRingEquiv_C U b r

/-- The open `U_S` of `Z_S` is affine with ring `A ⊗_k S`. -/
def baseChangeOpenIso :
    letI := (sectionsStructure f U.1).hom.toAlgebra
    (baseChangeOpen f S U.1).toScheme ≅ Spec (.of (Γ(Z, U.1) ⊗[k] S)) :=
  letI := (sectionsStructure f U.1).hom.toAlgebra
  (isPullback_baseChangeOpen f S U.2).isoIsPullback _ _ (isPullback_tensor f S)

/-- The inverse image `p⁻¹(U_S)` is the open of `X` over the chart `π⁻¹U`. -/
theorem preimage_baseChangeOpen :
    coverMap f φ S c ⁻¹ᵁ baseChangeOpen f S U.1 = coverOpen f φ U S c := by
  rw [baseChangeOpen, ← Scheme.Hom.comp_preimage, coverMap_fst, Scheme.Hom.comp_preimage]


/-- On `p⁻¹(U_S)`, the composite `X ⟶ 𝕃 ⟶ Z` restricted over `U` agrees with
`X ⟶ Z_S ⟶ Z`. -/
@[reassoc]
theorem restrict_comp_restrict :
    (Scheme.isoOfEq _ (preimage_baseChangeOpen f φ U S c)).hom ≫
        (coverFst f φ S c ∣_ chartOpen f U) ≫ (totalSpaceToBase f L ∣_ U.1) =
      (coverMap f φ S c ∣_ baseChangeOpen f S U.1) ≫ (baseChangeFst f S ∣_ U.1) := by
  rw [← cancel_mono U.1.ι]
  simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
    Scheme.isoOfEq_hom_ι_assoc, coverMap_fst]

/-- **The local description of `p`**: over `U_S`, the morphism `p : X ⟶ Z_S` is
`Spec (A ⊗_k S)[x]/(xⁿ - c f) ⟶ Spec (A ⊗_k S)`. -/
def coverMapArrowIso :
    letI := (sectionsStructure f U.1).hom.toAlgebra
    Arrow.mk (coverMap f φ S c ∣_ baseChangeOpen f S U.1) ≅
      Arrow.mk (Spec.map (CommRingCat.ofHom
        (algebraMap (Γ(Z, U.1) ⊗[k] S) (chartRing k n (chartCoeff f φ U b) c)))) :=
  letI := (sectionsStructure f U.1).hom.toAlgebra
  Arrow.isoMk (Scheme.isoOfEq _ (preimage_baseChangeOpen f φ U S c) ≪≫ coverOpenIso f φ U b S c)
    (baseChangeOpenIso f U S) (by
      refine (isPullback_tensor f S).hom_ext ?_ ?_
      · simp only [Arrow.mk_hom, Iso.trans_hom, Category.assoc, baseChangeOpenIso]
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        have : (algebraMap (Γ(Z, U.1) ⊗[k] S) (chartRing k n (chartCoeff f φ U b) c)).comp
            Algebra.TensorProduct.includeLeftRingHom =
              (chartLeft k n (chartCoeff f φ U b) c).comp C := by
          ext a; simp [chartLeft_C]
        rw [this, CommRingCat.ofHom_comp, Spec.map_comp, coverOpenIso,
          IsPullback.isoIsPullback_hom_fst_assoc, Category.assoc, chartOpenIso_hom_comp_C,
          restrict_comp_restrict_assoc]
        exact congrArg (fun t => coverMap f φ S c ∣_ baseChangeOpen f S U.1 ≫ t)
          (IsPullback.isoIsPullback_hom_fst _ _ _ _).symm
      · simp only [Arrow.mk_hom, Iso.trans_hom, Category.assoc, baseChangeOpenIso,
          IsPullback.isoIsPullback_hom_snd]
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
        change _ ≫ _ ≫ Spec.map (CommRingCat.ofHom (chartRight k n (chartCoeff f φ U b) c)) = _
        rw [coverOpenIso, IsPullback.isoIsPullback_hom_snd, Scheme.isoOfEq_hom_ι_assoc,
          morphismRestrict_ι_assoc, coverMap_snd])

end Chart

end Stacks.CyclicCover

end
