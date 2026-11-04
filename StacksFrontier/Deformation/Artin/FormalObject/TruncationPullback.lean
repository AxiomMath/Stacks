module

public import StacksFrontier.Deformation.Artin.FormalObject.BaseChange
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties

/-!
# Infinitesimal thickenings as fibre products

The `n`-th infinitesimal thickening `Spec (R / 𝔪 ^ (n + 1))` of the closed point of a complete
local base is a closed subscheme of `Spec R`, and its base change along a morphism
`X ⟶ Spec R` is the closed subscheme of `X` cut out by `𝔪 ^ (n + 1)`. On rings this is the
isomorphism `A ⊗_R (R / I) ≅ A / I A`. This file records two forms of it:

* for an affine object `M` of the site over `Spec R`, the base change of the thickening is the
  spectrum of `Γ(M) / 𝔪 ^ (n + 1) Γ(M)`, compatibly with the projection to `M`;
* for a formally unramified local homomorphism `R → R'`, so that `𝔪_R R' = 𝔪_{R'}`, the
  thickenings of `R'` are the base changes of those of `R`.

## Main results

* `CommRingCat.isPushout_quotientMap`: `A / J` is the pushout of `A ← R → R / I` when `J = I A`.
* `Deformation.Artin.isPullback_truncationOverMap`: the square of thickenings of a formally
  unramified local homomorphism is a fibre product in the site.
* `Deformation.Artin.exists_iso_toScheme_pullback_restrictionToBase`: the base change of a
  thickening to an affine object of the site.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped TensorProduct

universe u v w

namespace CommRingCat

/-- **The quotient by an extended ideal is a pushout.** For an `R`-algebra `A`, an ideal `I` of `R`
and `J = I A`, the square `R → A → A / J`, `R → R / I → A / J` is a pushout of commutative
rings. -/
theorem isPushout_quotientMap {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal R) (J : Ideal A) (hJ : J = I.map (algebraMap R A)) :
    IsPushout (ofHom (algebraMap R A)) (ofHom (Ideal.Quotient.mk I)) (ofHom (Ideal.Quotient.mk J))
      (ofHom (Ideal.quotientMap J (algebraMap R A) (by rw [hJ]; exact Ideal.le_comap_map))) := by
  subst hJ
  let e : (A ⊗[R] (R ⧸ I)) ≃+* (A ⧸ I.map (algebraMap R A)) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).symm.toRingEquiv
  refine (isPushout_tensorProduct R A (R ⧸ I)).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    e.toCommRingCatIso (by simp) (by simp) ?_ ?_
  · ext a
    show (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).symm (a ⊗ₜ[R] 1) = _
    rw [← map_one (Ideal.Quotient.mk I),
      Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul, one_smul]
    rfl
  · ext r
    show (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).symm
      (1 ⊗ₜ[R] Ideal.Quotient.mk I r) = _
    simp [Algebra.algebraMap_eq_smul_one]

end CommRingCat

namespace Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The spectra of the quotient square of `CommRingCat.isPushout_quotientMap` form a fibre
product of schemes. -/
theorem isPullback_specMap_quotient {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (I : Ideal R) (J : Ideal A) (hJ : J = I.map (algebraMap R A)) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
      (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap J (algebraMap R A) (by rw [hJ]; exact Ideal.le_comap_map))))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_quotientMap I J hJ)

/-- A commutative square of the big fppf site whose image in schemes is a fibre product is a
fibre product. -/
theorem isPullback_of_toScheme {P X Y Z : BigFppfOver B S hS} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (w : fst ≫ f = snd ≫ g)
    (h : IsPullback ((BigFppfOver.toScheme B S hS).map fst)
      ((BigFppfOver.toScheme B S hS).map snd) ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map g)) : IsPullback fst snd f g :=
  IsPullback.of_map (BigFppfOver.toScheme B S hS) w h

section BaseChange

variable (A A' : FormalBase S) [Algebra A.R A'.R] [IsLocalHom (algebraMap A.R A'.R)]
  (hφ : Spec.map (CommRingCat.ofHom (algebraMap A.R A'.R)) ≫ A.toS = A'.toS)
  (hA : B.Contains (Spec (.of A.R))) (hA' : B.Contains (Spec (.of A'.R)))
  (c : ∀ n, B.Contains (A.truncation n)) (c' : ∀ n, B.Contains (A'.truncation n))

/-- The morphism of complete local bases induced by a homomorphism, in the site. -/
def baseOverMap : baseOver B S hS A' hA' ⟶ baseOver B S hS A hA :=
  Over.homMk (ObjectProperty.homMk (X := B.obj hA') (Y := B.obj hA)
    (Spec.map (CommRingCat.ofHom (algebraMap A.R A'.R)))) (by
    apply ObjectProperty.hom_ext; exact hφ)

omit [IsLocalHom (algebraMap A.R A'.R)] in
/-- The image of `baseOverMap` in schemes is the spectrum of the algebra map `A.R → A'.R`. -/
theorem toScheme_map_baseOverMap :
    (BigFppfOver.toScheme B S hS).map (baseOverMap A A' hφ hA hA') =
      Spec.map (CommRingCat.ofHom (algebraMap A.R A'.R)) := rfl

/-- The maps of thickenings lie over the map of complete local bases. -/
@[reassoc]
theorem truncationOverMap_restrictionToBase (n : ℕ) :
    truncationOverMap A A' (algebraMap A.R A'.R) hφ c c' n ≫ restrictionToBase B S hS A hA c n =
      restrictionToBase B S hS A' hA' c' n ≫ baseOverMap A A' hφ hA hA' := by
  have key : Spec.map (CommRingCat.ofHom (localQuotientMap (algebraMap A.R A'.R) n)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A.R ^ (n + 1)))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A'.R ^ (n + 1)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A.R A'.R)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      localQuotientMap_comp_mk]
  apply (BigFppfOver.toScheme B S hS).map_injective
  simp only [Functor.map_comp]
  exact key

/-- **The thickenings of a formally unramified extension are base changes.** For a formally
unramified local homomorphism `R → R'` of complete local bases, `𝔪_R R' = 𝔪_{R'}`, so the `n`-th
thickening of `R'` is the fibre product of `Spec R'` with the `n`-th thickening of `R` over
`Spec R`, in the big fppf site. -/
theorem isPullback_truncationOverMap [Algebra.FormallyUnramified A.R A'.R]
    [Algebra.EssFiniteType A.R A'.R] (n : ℕ) :
    IsPullback (restrictionToBase B S hS A' hA' c' n)
      (truncationOverMap A A' (algebraMap A.R A'.R) hφ c c' n)
      (baseOverMap A A' hφ hA hA') (restrictionToBase B S hS A hA c n) := by
  refine isPullback_of_toScheme (truncationOverMap_restrictionToBase A A' hφ hA hA' c c' n).symm ?_
  have hJ : maximalIdeal A'.R ^ (n + 1) =
      (maximalIdeal A.R ^ (n + 1)).map (algebraMap A.R A'.R) := by
    rw [Ideal.map_pow, Algebra.FormallyUnramified.map_maximalIdeal]
  exact isPullback_specMap_quotient (maximalIdeal A.R ^ (n + 1)) (maximalIdeal A'.R ^ (n + 1)) hJ

end BaseChange


section Affine

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

variable (A : FormalBase S) (hA : B.Contains (Spec (.of A.R)))
  (c : ∀ n, B.Contains (A.truncation n)) {M : BigFppfOver B S hS} (f : M ⟶ baseOver B S hS A hA)

/-- The `A.R`-algebra structure on the global sections of an object of the site over the
spectrum of a complete local base. -/
abbrev globalSectionsAlgebra :
    Algebra A.R Γ((BigFppfOver.toScheme B S hS).obj M, ⊤) :=
  ((Scheme.ΓSpecIso (.of A.R)).inv ≫ ((BigFppfOver.toScheme B S hS).map f).appTop).hom.toAlgebra

/-- On an affine object of the site over `Spec R`, the structure morphism is the spectrum of the
algebra structure of its global sections. -/
theorem toScheme_map_eq_isoSpec_hom_specMap [IsAffine ((BigFppfOver.toScheme B S hS).obj M)] :
    letI := globalSectionsAlgebra A hA f
    (BigFppfOver.toScheme B S hS).map f =
      ((BigFppfOver.toScheme B S hS).obj M).isoSpec.hom ≫
        Spec.map
          (CommRingCat.ofHom (algebraMap A.R Γ((BigFppfOver.toScheme B S hS).obj M, ⊤))) := by
  let := globalSectionsAlgebra A hA f
  let g : (BigFppfOver.toScheme B S hS).obj M ⟶ Spec (.of A.R) :=
    (BigFppfOver.toScheme B S hS).map f
  have h : ((BigFppfOver.toScheme B S hS).obj M).isoSpec.hom ≫ Spec.map g.appTop =
      g ≫ Spec.map (Scheme.ΓSpecIso (.of A.R)).hom := by
    rw [← Scheme.isoSpec_Spec_hom]; exact Scheme.isoSpec_hom_naturality g
  have hinv : Spec.map (Scheme.ΓSpecIso (.of A.R)).hom ≫ Spec.map (Scheme.ΓSpecIso (.of A.R)).inv =
      𝟙 _ := by
    rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]
  show g = _
  calc g = g ≫ Spec.map (Scheme.ΓSpecIso (.of A.R)).hom ≫
        Spec.map (Scheme.ΓSpecIso (.of A.R)).inv := by
        rw [hinv, Category.comp_id]
    _ = _ := by
        rw [← Category.assoc, ← h, Category.assoc, ← Spec.map_comp]
        rfl

/-- If the structure morphism is finite, the global sections form a finite algebra. -/
theorem module_finite_globalSections [IsAffine ((BigFppfOver.toScheme B S hS).obj M)]
    [IsFinite ((BigFppfOver.toScheme B S hS).map f)] :
    letI := globalSectionsAlgebra A hA f
    Module.Finite A.R Γ((BigFppfOver.toScheme B S hS).obj M, ⊤) := by
  let := globalSectionsAlgebra A hA f
  let g : (BigFppfOver.toScheme B S hS).obj M ⟶ Spec (.of A.R) :=
    (BigFppfOver.toScheme B S hS).map f
  have : IsFinite g := ‹_›
  have h₁ := g.finite_appTop
  have h₂ : (Scheme.ΓSpecIso (.of A.R)).inv.hom.Finite :=
    RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of A.R)).inv).2
  exact RingHom.Finite.comp h₁ h₂

/-- **The base change of a thickening to an affine object of the site.** For an affine object `M`
of the site over the spectrum of a complete local base `R`, the base change of the `n`-th
thickening `Spec (R / 𝔪 ^ (n + 1)) ⟶ Spec R` along `M ⟶ Spec R` is the spectrum of
`Γ(M) / 𝔪 ^ (n + 1) Γ(M)`, compatibly with the projection to `M`. -/
theorem exists_iso_toScheme_pullback_restrictionToBase
    [IsAffine ((BigFppfOver.toScheme B S hS).obj M)] (n : ℕ) :
    letI := globalSectionsAlgebra A hA f
    ∃ e : (BigFppfOver.toScheme B S hS).obj (pullback f (restrictionToBase B S hS A hA c n)) ≅
        Spec (.of (Γ((BigFppfOver.toScheme B S hS).obj M, ⊤) ⧸
          (maximalIdeal A.R ^ (n + 1)).map
            (algebraMap A.R Γ((BigFppfOver.toScheme B S hS).obj M, ⊤)))),
      (BigFppfOver.toScheme B S hS).map (pullback.fst f (restrictionToBase B S hS A hA c n)) ≫
          ((BigFppfOver.toScheme B S hS).obj M).isoSpec.hom =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) := by
  let := globalSectionsAlgebra A hA f
  have hSch := (IsPullback.of_hasPullback f (restrictionToBase B S hS A hA c n)).map
    (BigFppfOver.toScheme B S hS)
  have hRing := isPullback_specMap_quotient (A := Γ((BigFppfOver.toScheme B S hS).obj M, ⊤))
    (maximalIdeal A.R ^ (n + 1))
    ((maximalIdeal A.R ^ (n + 1)).map (algebraMap A.R Γ((BigFppfOver.toScheme B S hS).obj M, ⊤)))
    rfl
  have e := toScheme_map_eq_isoSpec_hom_specMap A hA f
  have hRing' : IsPullback (X := (BigFppfOver.toScheme B S hS).obj M)
      (Y := (BigFppfOver.toScheme B S hS).obj (restrictionBase B S hS A c n))
      (Z := (BigFppfOver.toScheme B S hS).obj (baseOver B S hS A hA))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((maximalIdeal A.R ^ (n + 1)).map
        (algebraMap A.R Γ((BigFppfOver.toScheme B S hS).obj M, ⊤))))) ≫
          ((BigFppfOver.toScheme B S hS).obj M).isoSpec.inv)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap _
        (algebraMap A.R Γ((BigFppfOver.toScheme B S hS).obj M, ⊤)) Ideal.le_comap_map)))
      ((BigFppfOver.toScheme B S hS).map f)
      ((BigFppfOver.toScheme B S hS).map (restrictionToBase B S hS A hA c n)) := by
    refine hRing.of_iso (Iso.refl _) ((BigFppfOver.toScheme B S hS).obj M).isoSpec.symm
      (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · refine (Category.comp_id _).trans ?_
      rw [e, Iso.symm_hom]
      exact (Iso.inv_hom_id_assoc _ _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  refine ⟨hSch.isoIsPullback _ _ hRing', ?_⟩
  have h := IsPullback.isoIsPullback_hom_fst _ _ hSch hRing'
  refine Eq.trans (congrArg (· ≫ ((BigFppfOver.toScheme B S hS).obj M).isoSpec.hom) h.symm) ?_
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Affine

end Deformation.Artin

end
