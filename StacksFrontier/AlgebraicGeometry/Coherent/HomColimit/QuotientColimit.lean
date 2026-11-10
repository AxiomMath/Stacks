module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.AnnihilatorQuotient

/-!
# The colimit of `Hom(Iⁿ, F/F_n)` and the sections away from `V(I)`

Let `X` be a quasi-compact scheme, let `I` be a quasi-coherent sheaf of ideals of finite type,
let `Z` be the closed subscheme it defines and let `U = X \ Z`. Let `F` be a quasi-coherent
`𝒪_X`-module and let `F_n` be the subsheaf of sections annihilated by `Iⁿ`. This file constructs
the canonical map

`colim_n Hom_{𝒪_X}(Iⁿ, F/F_n) ⟶ Γ(U, F)`

and proves that it is injective.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPowerColimit.quotientMap`: the map `F/F_n ⟶ F/F_m` for
  `n ≤ m`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowHomQuotientSystem`: the direct system
  `n ↦ Hom_{𝒪_X}(Iⁿ, F/F_n)`, whose transition maps precompose with `I^(n+1) ⟶ Iⁿ` and
  postcompose with `F/F_n ⟶ F/F_(n+1)`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToSectionsQuotient`: the canonical
  map out of the colimit of that system, sending `φ` to the section of `F` over `U`
  corresponding to `φ(1)` under the identification `Γ(U, F) ≅ Γ(U, F/F_n)`.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToSectionsQuotient_injective`: for
  quasi-compact `X`, the canonical map `colim_n Hom_{𝒪_X}(Iⁿ, F/F_n) ⟶ Γ(U, F)` is injective.

## Implementation notes

The identification `Γ(U, F) ≅ Γ(U, F/F_n)` is
`Stacks.AlgebraicGeometry.IdealPowerColimit.quotientSectionsEquiv`: `F_n` vanishes on `U`
because `Iⁿ` is the whole structure sheaf there, so the projection `F ⟶ F/F_n` is injective on
sections over any open of `U`, and it is surjective because it is surjective over affine opens
and the local lifts are unique. The canonical map is defined through the inverse of this
identification, so the finite-type hypothesis on `I` appears already in its definition: it makes
`F_n`, and hence `F/F_n`, quasi-coherent.

A class in the colimit is represented by some `φ : Iⁿ ⟶ F/F_n`, and it is sent to zero exactly
when `φ(1) = 0` in `Γ(U, F/F_n)`. Since `F/F_n` is quasi-coherent, the injectivity of the map
`colim_n Hom_{𝒪_X}(Iⁿ, F/F_n) ⟶ Γ(U, F/F_n)` gives an `N` with `I^(n+N) ⟶ Iⁿ ⟶ F/F_n` zero
(`Stacks.AlgebraicGeometry.IdealPowerColimit.exists_comp_eq_zero`); composing with
`F/F_n ⟶ F/F_(n+N)` keeps it zero, so the transition map of the system kills `φ`.

## References

* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}}

/-! ### The transition maps between the quotients -/

/-- The map `F/F_n ⟶ F/F_m` for `n ≤ m`, induced by `F_n ≤ F_m`. -/
noncomputable def quotientMap (I : X.IdealSheafData) (F : X.Modules) {n m : ℕ} (h : n ≤ m) :
    quotientModule I F n ⟶ quotientModule I F m :=
  cokernel.desc (annihilatorι I F n) (quotientπ I F m) (by
    rw [← annihilatorLE_comp_annihilatorι I F h, Category.assoc, cokernel.condition, comp_zero])

/-- The projection `F ⟶ F/F_n` followed by `F/F_n ⟶ F/F_m` is the projection `F ⟶ F/F_m`. -/
@[reassoc (attr := simp)]
theorem quotientπ_comp_quotientMap (I : X.IdealSheafData) (F : X.Modules) {n m : ℕ}
    (h : n ≤ m) :
    quotientπ I F n ≫ quotientMap I F h = quotientπ I F m :=
  cokernel.π_desc _ _ _

/-- The map `F/F_n ⟶ F/F_n` is the identity. -/
theorem quotientMap_refl (I : X.IdealSheafData) (F : X.Modules) (n : ℕ) :
    quotientMap I F (le_refl n) = 𝟙 (quotientModule I F n) := by
  rw [← cancel_epi (quotientπ I F n), quotientπ_comp_quotientMap, Category.comp_id]

/-- The maps `F/F_n ⟶ F/F_m ⟶ F/F_k` compose to `F/F_n ⟶ F/F_k`. -/
theorem quotientMap_comp (I : X.IdealSheafData) (F : X.Modules) {n m k : ℕ} (h : n ≤ m)
    (h' : m ≤ k) :
    quotientMap I F h ≫ quotientMap I F h' = quotientMap I F (h.trans h') := by
  rw [← cancel_epi (quotientπ I F n), ← Category.assoc, quotientπ_comp_quotientMap,
    quotientπ_comp_quotientMap, quotientπ_comp_quotientMap]

/-! ### The direct system `n ↦ Hom(Iⁿ, F/F_n)` -/

/-- The direct system `n ↦ Hom_{𝒪_X}(Iⁿ, F/F_n)`: the transition map for `n ≤ m` precomposes
with the inclusion `I^m ⟶ Iⁿ` and postcomposes with the projection `F/F_n ⟶ F/F_m`. -/
noncomputable def idealPowHomQuotientSystem (I : X.IdealSheafData) (F : X.Modules) :
    ℕ ⥤ AddCommGrpCat.{u} where
  obj n := AddCommGrpCat.of (idealPow I n ⟶ quotientModule I F n)
  map {m n} h := AddCommGrpCat.ofHom
    (AddMonoidHom.mk' (fun φ : idealPow I m ⟶ quotientModule I F m ↦
        idealPowMap I (leOfHom h) ≫ φ ≫ quotientMap I F (leOfHom h))
      (fun φ ψ ↦ by rw [Preadditive.add_comp, Preadditive.comp_add]))
  map_id n := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ ↦ by
    change idealPowMap I (le_refl n) ≫ φ ≫ quotientMap I F (le_refl n) = φ
    rw [idealPowMap_refl, Category.id_comp, quotientMap_refl, Category.comp_id])
  map_comp {k m n} h h' := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ ↦ by
    change idealPowMap I (leOfHom (h ≫ h')) ≫ φ ≫ quotientMap I F (leOfHom (h ≫ h'))
      = idealPowMap I (leOfHom h') ≫
        (idealPowMap I (leOfHom h) ≫ φ ≫ quotientMap I F (leOfHom h)) ≫
          quotientMap I F (leOfHom h')
    rw [← idealPowMap_comp I (leOfHom h) (leOfHom h'),
      ← quotientMap_comp I F (leOfHom h) (leOfHom h')]
    simp only [Category.assoc])

/-- The transition map of `idealPowHomQuotientSystem` for `m ≤ n` sends `φ : I^m ⟶ F/F_m` to
the composite `Iⁿ ⟶ I^m ⟶ F/F_m ⟶ F/F_n`. -/
@[simp] theorem idealPowHomQuotientSystem_map (I : X.IdealSheafData) (F : X.Modules) {m n : ℕ}
    (h : m ⟶ n) (φ : idealPow I m ⟶ quotientModule I F m) :
    (idealPowHomQuotientSystem I F).map h φ
      = idealPowMap I (leOfHom h) ≫ φ ≫ quotientMap I F (leOfHom h) := rfl

/-! ### The canonical map to the sections away from `V(I)` -/

variable (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
  (hFG : ∀ V : X.affineOpens, (I.ideal V).FG)

/-- The section of `F` over `X \ V(I)` attached to a morphism `φ : Iⁿ ⟶ F/F_n`: the section
`φ(1)` of `F/F_n`, read through the identification of the sections of `F` and of `F/F_n`
there. -/
noncomputable def quotientSectionOfHom (n : ℕ) (φ : idealPow I n ⟶ quotientModule I F n) :
    Γ(F, (I.support.compl : X.Opens)) :=
  (quotientSectionsEquiv I F n hFG (le_refl (I.support.compl : X.Opens))).symm
    (φ.app (I.support.compl : X.Opens) (oneSection I n))

/-- The image of `quotientSectionOfHom I F hFG n φ` in the sections of `F/F_n` over `X \ V(I)`
is `φ(1)`. -/
theorem quotientπ_app_quotientSectionOfHom (n : ℕ)
    (φ : idealPow I n ⟶ quotientModule I F n) :
    (quotientπ I F n).app (I.support.compl : X.Opens) (quotientSectionOfHom I F hFG n φ)
      = φ.app (I.support.compl : X.Opens) (oneSection I n) :=
  quotientSectionsEquiv_symm_apply I F n hFG _ _

/-- The cocone on `idealPowHomQuotientSystem` sending `φ : Iⁿ ⟶ F/F_n` to the section of `F`
over `X \ V(I)` corresponding to `φ(1)`. -/
noncomputable def quotientSectionsCocone :
    Limits.Cocone (idealPowHomQuotientSystem I F) where
  pt := Γ(F, (I.support.compl : X.Opens))
  ι :=
    { app := fun n ↦ AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (quotientSectionOfHom I F hFG n)
          (fun φ ψ ↦ by
            have h : (φ + ψ).app (I.support.compl : X.Opens) (oneSection I n)
                = φ.app (I.support.compl : X.Opens) (oneSection I n)
                  + ψ.app (I.support.compl : X.Opens) (oneSection I n) := by
              rw [Scheme.Modules.Hom.add_app]; rfl
            rw [quotientSectionOfHom, h, map_add]
            rfl))
      naturality := fun {m n} h ↦ by
        simp only [Functor.const_obj_map]
        refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun φ₀ ↦ ?_)
        obtain ⟨φ, rfl⟩ : ∃ φ : idealPow I m ⟶ quotientModule I F m, φ = φ₀ := ⟨φ₀, rfl⟩
        change quotientSectionOfHom I F hFG n
              (idealPowMap I (leOfHom h) ≫ φ ≫ quotientMap I F (leOfHom h))
            = quotientSectionOfHom I F hFG m φ
        refine injective_quotientπ_app_of_le_compl_support I F n (le_refl _) ?_
        rw [quotientπ_app_quotientSectionOfHom]
        have hr : (quotientπ I F n).app (I.support.compl : X.Opens)
              (quotientSectionOfHom I F hFG m φ)
            = (quotientMap I F (leOfHom h)).app (I.support.compl : X.Opens)
                (φ.app (I.support.compl : X.Opens) (oneSection I m)) := by
          conv_lhs => rw [← quotientπ_comp_quotientMap I F (leOfHom h)]
          change (quotientMap I F (leOfHom h)).app (I.support.compl : X.Opens)
            ((quotientπ I F m).app (I.support.compl : X.Opens)
              (quotientSectionOfHom I F hFG m φ)) = _
          rw [quotientπ_app_quotientSectionOfHom]
        rw [hr]
        change (quotientMap I F (leOfHom h)).app (I.support.compl : X.Opens)
          (φ.app (I.support.compl : X.Opens)
            ((idealPowMap I (leOfHom h)).app (I.support.compl : X.Opens)
              (oneSection I n))) = _
        rw [idealPowMap_app_oneSection] }

/-- The canonical map `colim_n Hom_{𝒪_X}(Iⁿ, F/F_n) ⟶ Γ(X \ V(I), F)`, where `F_n` is the
subsheaf of sections annihilated by `Iⁿ`, sending the class of `φ` to the section of `F`
corresponding to `φ(1)`. -/
@[stacks 01PQ "canonical map of the second display, colim Hom(Iⁿ, F/F_n) → Γ(U, F)"]
noncomputable def canonicalMapToSectionsQuotient :
    Limits.colimit (idealPowHomQuotientSystem I F) ⟶ Γ(F, (I.support.compl : X.Opens)) :=
  Limits.colimit.desc _ (quotientSectionsCocone I F hFG)

/-- The canonical map sends the class of `φ : Iⁿ ⟶ F/F_n` to `quotientSectionOfHom I F hFG n φ`.
-/
theorem canonicalMapToSectionsQuotient_ι (n : ℕ) (φ : idealPow I n ⟶ quotientModule I F n) :
    canonicalMapToSectionsQuotient I F hFG
        (Limits.colimit.ι (idealPowHomQuotientSystem I F) n φ)
      = quotientSectionOfHom I F hFG n φ :=
  congr($(Limits.colimit.ι_desc (quotientSectionsCocone I F hFG) n) φ)

/-- For a quasi-compact scheme `X`, a quasi-coherent sheaf of ideals `I` of finite type and a
quasi-coherent `𝒪_X`-module `F`, the canonical map
`colim_n Hom_{𝒪_X}(Iⁿ, F/F_n) → Γ(X \ V(I), F)` is injective. -/
@[stacks 01PQ "second display colim Hom(Iⁿ, F/F_n) → Γ(U, F) is injective; X quasi-compact,
I of finite type; surjectivity is canonicalMapToSectionsQuotient_surjective"]
theorem canonicalMapToSectionsQuotient_injective [CompactSpace X] :
    Function.Injective (canonicalMapToSectionsQuotient I F hFG) := by
  have hforget : PreservesFilteredColimitsOfSize.{0, 0} (forget AddCommGrpCat.{u}) :=
    preservesSmallestFilteredColimits_of_preservesFilteredColimits _
  refine (injective_iff_map_eq_zero
    (AddCommGrpCat.Hom.hom (canonicalMapToSectionsQuotient I F hFG))).mpr fun z hz ↦ ?_
  obtain ⟨n, φ₀, rfl⟩ :=
    Limits.Concrete.colimit_exists_rep (idealPowHomQuotientSystem I F) z
  obtain ⟨φ, rfl⟩ : ∃ φ : idealPow I n ⟶ quotientModule I F n, φ = φ₀ := ⟨φ₀, rfl⟩
  let := isQuasicoherent_quotientModule I F n hFG
  have hφ : φ.app (I.support.compl : X.Opens) (oneSection I n) = 0 := by
    have h : quotientSectionOfHom I F hFG n φ = 0 :=
      (canonicalMapToSectionsQuotient_ι I F hFG n φ).symm.trans hz
    have h2 := congrArg
      (fun y : Γ(F, (I.support.compl : X.Opens)) ↦
        (quotientπ I F n).app (I.support.compl : X.Opens) y) h
    rw [quotientπ_app_quotientSectionOfHom] at h2
    exact h2.trans (map_zero _)
  obtain ⟨N, hN⟩ := exists_comp_eq_zero (F := quotientModule I F n) hFG φ hφ
  calc Limits.colimit.ι (idealPowHomQuotientSystem I F) n φ
      = Limits.colimit.ι (idealPowHomQuotientSystem I F) (n + N)
          ((idealPowHomQuotientSystem I F).map (homOfLE (Nat.le_add_right n N)) φ) :=
        (ConcreteCategory.congr_hom
          (Limits.colimit.w (idealPowHomQuotientSystem I F)
            (homOfLE (Nat.le_add_right n N))) φ).symm
    _ = Limits.colimit.ι (idealPowHomQuotientSystem I F) (n + N) 0 :=
        congrArg
          (ConcreteCategory.hom (Limits.colimit.ι (idealPowHomQuotientSystem I F) (n + N)))
          (show (idealPowHomQuotientSystem I F).map (homOfLE (Nat.le_add_right n N)) φ = 0 by
            change idealPowMap I (Nat.le_add_right n N) ≫ φ ≫
              quotientMap I F (Nat.le_add_right n N) = 0
            rw [← Category.assoc, hN, Limits.zero_comp])
    _ = 0 := map_zero _

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
