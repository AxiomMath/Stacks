module

public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeNoetherian

/-!
# Relative dualizing complexes that stay relative dualizing under every base change

Let `R → A` be flat of finite presentation and `K` in `D(A)`.  Say `K` is *universally* a relative
dualizing complex if for every ring map `R → R'` the derived base change `K ⊗ᴸ_A (A ⊗_R R')` is a
relative dualizing complex for `R' → A ⊗_R R'`.  This file proves that the property is invariant
under isomorphism, transports along isomorphisms of `R`-algebras, and is stable under base change:
if `K₁` is universally relative dualizing for `R₁ → A₁` then so is `K₁ ⊗ᴸ_{A₁} (A₁ ⊗_{R₁} R)`
for `R → A₁ ⊗_{R₁} R`, for any `R₁ → R`.  The last is the transitivity of derived base change
together with the identification `(A₁ ⊗_{R₁} R) ⊗_R R' = A₁ ⊗_{R₁} R'`.

These are the bookkeeping steps of the proof of [stacks 0E2F] (2): the source proves (2) at the
Noetherian model of the reduction to the Noetherian case and carries it to `R` "by transitivity of
derived base change".

## Main definitions

* `Dualizing.IsUniversallyRelativeDualizing` — the property above.

## Main results

* `Dualizing.isRelativeDualizingComplex_totalDerivedExtension_of_algEquiv` — being a relative
  dualizing complex, for a derived extension of scalars, transports along an isomorphism of
  `R'`-algebras of the target compatible with the two ring maps.
* `Dualizing.IsUniversallyRelativeDualizing.of_iso`,
  `Dualizing.IsUniversallyRelativeDualizing.of_algEquiv` and
  `Dualizing.IsUniversallyRelativeDualizing.baseChange` — the three stability properties.

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

namespace Dualizing

noncomputable section

/-- The chosen derived extension of scalars along `g` is a left derived functor of the degreewise
extension of scalars, for the spelling of the comparison used by `derivedExtensionRingEquivIso`. -/
private theorem isLeftDerivedFunctor_totalDerivedExtensionScalars {B C : Type u} [CommRing B]
    [CommRing C] (g : B →+* C) :
    (totalDerivedExtensionScalars.{u, u, u} g).functor.IsLeftDerivedFunctor
      (show DerivedCategory.Q ⋙ (totalDerivedExtensionScalars.{u, u, u} g).functor ⟶
        (ModuleCat.extendScalars.{u, u, u} g).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q from
        (totalDerivedExtensionScalars.{u, u, u} g).comparison)
      (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)) :=
  (totalDerivedExtensionScalars.{u, u, u} g).isLeftDerived

/-- **Transport of a relative dualizing complex along an isomorphism of the target algebra.**
Let `ε : C' ≃ₐ[R'] C` be an isomorphism of flat, finitely presented `R'`-algebras and let
`g : B → C`, `g' : B → C'` be ring maps with `ε ∘ g' = g`.  If the derived extension of `K` along
`g` is a relative dualizing complex for `R' → C`, then its derived extension along `g'` is one
for `R' → C'`. -/
theorem isRelativeDualizingComplex_totalDerivedExtension_of_algEquiv
    {R' B C C' : Type u} [CommRing R'] [CommRing B] [CommRing C] [CommRing C']
    [Algebra R' C] [Algebra R' C'] [Module.Flat R' C] [Module.Flat R' C']
    [Algebra.FinitePresentation R' C] [Algebra.FinitePresentation R' C']
    (ε : C' ≃ₐ[R'] C) (g : B →+* C) (g' : B →+* C') (hg : ε.toRingHom.comp g' = g)
    (K : DerivedCategory (ModuleCat.{u} B))
    (hK : IsRelativeDualizingComplex R' C
      ((totalDerivedExtensionScalars.{u, u, u} g).functor.obj K)) :
    IsRelativeDualizingComplex R' C'
      ((totalDerivedExtensionScalars.{u, u, u} g').functor.obj K) := by
  have h1 := RelativeExistence.isRelativeDualizingComplex_of_algEquiv ε.symm _ hK
  let F := totalDerivedExtensionScalars.{u, u, u} g
  let h : B →+* C' := ε.toRingEquiv.symm.toRingHom.comp (g.comp (RingEquiv.refl B).toRingHom)
  have hh : h = g' := by
    ext b
    simp only [h, ← hg]
    exact ε.symm_apply_apply (g' b)
  let G := totalDerivedExtensionScalars.{u, u, u} h
  have := isLeftDerivedFunctor_totalDerivedExtensionScalars g
  have := isLeftDerivedFunctor_totalDerivedExtensionScalars h
  have eG := StacksDraft.DerivedRingEquivIso.derivedExtensionRingEquivIsoRight.{u}
    ε.toRingEquiv g F.functor F.comparison G.functor G.comparison
  exact isRelativeDualizingComplex_of_iso R' C' h1 <| (eG.app K).symm ≪≫ eqToIso (congrArg
    (fun k : B →+* C' => (totalDerivedExtensionScalars.{u, u, u} k).functor.obj K) hh)

/-- **A relative dualizing complex that stays one under every base change.**  `K` in `D(A)` is
universally relative dualizing for `R → A` if for every ring map `R → R'` the derived base change
`K ⊗ᴸ_A (A ⊗_R R')` is a relative dualizing complex for `R' → A ⊗_R R'`.

Taking `R' = R` this contains being a relative dualizing complex for `R → A ⊗_R R`, and
[stacks 0E2F] (2) says that every relative dualizing complex has the property. -/
def IsUniversallyRelativeDualizing (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.Flat R A] [Algebra.FinitePresentation R A] (K : DerivedCategory (ModuleCat.{u} A)) :
    Prop :=
  ∀ (R' : Type u) [CommRing R'] [Algebra R R'],
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    letI : Algebra.FinitePresentation R' (A ⊗[R] R') :=
      Algebra.FinitePresentation.equiv (baseChangeComm R A R')
    IsRelativeDualizingComplex R' (A ⊗[R] R')
      ((totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K)

namespace IsUniversallyRelativeDualizing

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Flat R A]
  [Algebra.FinitePresentation R A]

/-- Being universally relative dualizing depends only on the isomorphism class. -/
theorem of_iso {K L : DerivedCategory (ModuleCat.{u} A)}
    (hK : IsUniversallyRelativeDualizing R A K) (e : K ≅ L) :
    IsUniversallyRelativeDualizing R A L := by
  intro R' _ _
  let : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
  let : Algebra.FinitePresentation R' (A ⊗[R] R') :=
    Algebra.FinitePresentation.equiv (baseChangeComm R A R')
  exact isRelativeDualizingComplex_of_iso R' (A ⊗[R] R') (hK R')
    ((totalDerivedExtensionScalars.{u, u, u}
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.mapIso e)

end IsUniversallyRelativeDualizing

/-- The isomorphism `A₂ ⊗_R R' ≃ A ⊗_R R'` of `R'`-algebras induced by an isomorphism of
`R`-algebras `A₂ ≃ A`. -/
def baseChangeAlgEquiv {R A₂ A : Type u} [CommRing R] [CommRing A₂] [CommRing A] [Algebra R A₂]
    [Algebra R A] (R' : Type u) [CommRing R'] [Algebra R R'] (e : A₂ ≃ₐ[R] A) :
    (A₂ ⊗[R] R') ≃ₐ[R'] (A ⊗[R] R') :=
  AlgEquiv.ofRingEquiv
    (f := (Algebra.TensorProduct.congr e (AlgEquiv.refl : R' ≃ₐ[R] R')).toRingEquiv)
    (fun r' => by
      change Algebra.TensorProduct.congr e (AlgEquiv.refl : R' ≃ₐ[R] R')
        ((1 : A₂) ⊗ₜ[R] r') = (1 : A) ⊗ₜ[R] r'
      rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
      simp)

namespace IsUniversallyRelativeDualizing

variable {R A₂ A : Type u} [CommRing R] [CommRing A₂] [CommRing A] [Algebra R A₂] [Algebra R A]
  [Module.Flat R A₂] [Algebra.FinitePresentation R A₂] [Module.Flat R A]
  [Algebra.FinitePresentation R A]

/-- **Transport along an isomorphism of `R`-algebras.**  If `K₂` is universally relative
dualizing for `R → A₂` and `e : A₂ ≃ₐ[R] A`, then so is its transport to `D(A)`. -/
theorem of_algEquiv (e : A₂ ≃ₐ[R] A) {K₂ : DerivedCategory (ModuleCat.{u} A₂)}
    (hK : IsUniversallyRelativeDualizing R A₂ K₂) :
    IsUniversallyRelativeDualizing R A
      ((ModuleCat.restrictScalars.{u} e.symm.toRingEquiv.toRingHom).mapDerivedCategory.obj K₂) := by
  intro R' _ _
  let : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
  let : Algebra.FinitePresentation R' (A ⊗[R] R') :=
    Algebra.FinitePresentation.equiv (baseChangeComm R A R')
  let : Module.Flat R' (A₂ ⊗[R] R') := flat_baseChange R A₂ R'
  let : Algebra.FinitePresentation R' (A₂ ⊗[R] R') :=
    Algebra.FinitePresentation.equiv (baseChangeComm R A₂ R')
  let e' := baseChangeAlgEquiv R' e
  have h1 := RelativeExistence.isRelativeDualizingComplex_of_algEquiv e' _ (hK R')
  let f₂ : A₂ →+* A₂ ⊗[R] R' := Algebra.TensorProduct.includeLeftRingHom
  let F := totalDerivedExtensionScalars.{u, u, u} f₂
  let h : A →+* A ⊗[R] R' :=
    e'.toRingEquiv.symm.symm.toRingHom.comp (f₂.comp e.symm.toRingEquiv.toRingHom)
  have hh : h = (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R') := by
    ext a
    show Algebra.TensorProduct.congr e (AlgEquiv.refl : R' ≃ₐ[R] R')
      (e.symm a ⊗ₜ[R] (1 : R')) = a ⊗ₜ[R] (1 : R')
    rw [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
    simp
  let G := totalDerivedExtensionScalars.{u, u, u} h
  have := isLeftDerivedFunctor_totalDerivedExtensionScalars f₂
  have := isLeftDerivedFunctor_totalDerivedExtensionScalars h
  have eG := StacksDraft.DerivedRingEquivIso.derivedExtensionRingEquivIso.{u, 0}
    e.symm.toRingEquiv e'.toRingEquiv.symm f₂ F.functor F.comparison G.functor G.comparison
  exact isRelativeDualizingComplex_of_iso R' (A ⊗[R] R') h1 <| (eG.app K₂).symm ≪≫ eqToIso (congrArg
    (fun k : A →+* A ⊗[R] R' => (totalDerivedExtensionScalars.{u, u, u} k).functor.obj
      ((ModuleCat.restrictScalars.{u} e.symm.toRingEquiv.toRingHom).mapDerivedCategory.obj K₂))
    hh)

end IsUniversallyRelativeDualizing

section BaseChange

variable {R₁ R A₁ : Type u} [CommRing R₁] [CommRing R] [CommRing A₁] [Algebra R₁ R]
  [Algebra R₁ A₁]

/-- **`(A₁ ⊗_{R₁} R) ⊗_R R' = A₁ ⊗_{R₁} R'`**, as `R'`-algebras, for ring maps `R₁ → R → R'`.
The algebra structure of `R'` over `R₁` is the composite one. -/
def baseChangeBaseChangeAlgEquiv (R' : Type u) [CommRing R'] [Algebra R R'] :
    letI : Algebra R₁ R' := ((algebraMap R R').comp (algebraMap R₁ R)).toAlgebra
    ((A₁ ⊗[R₁] R) ⊗[R] R') ≃ₐ[R'] (A₁ ⊗[R₁] R') :=
  letI : Algebra R₁ R' := ((algebraMap R R').comp (algebraMap R₁ R)).toAlgebra
  letI : IsScalarTower R₁ R R' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  AlgEquiv.ofRingEquiv
    (f := ((((Algebra.TensorProduct.commRight R R' (A₁ ⊗[R₁] R)).symm.toRingEquiv.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : R' ≃ₐ[R] R')
        (Algebra.TensorProduct.commRight R₁ R A₁).symm).toRingEquiv).trans
      (Algebra.TensorProduct.cancelBaseChange R₁ R R' R' A₁).toRingEquiv).trans
      (Algebra.TensorProduct.commRight R₁ R' A₁).toRingEquiv))
    (fun r' => by
      change Algebra.TensorProduct.commRight R₁ R' A₁
        (Algebra.TensorProduct.cancelBaseChange R₁ R R' R' A₁
          (Algebra.TensorProduct.congr (AlgEquiv.refl : R' ≃ₐ[R] R')
            (Algebra.TensorProduct.commRight R₁ R A₁).symm
            ((Algebra.TensorProduct.commRight R R' (A₁ ⊗[R₁] R)).symm
              ((1 : A₁ ⊗[R₁] R) ⊗ₜ[R] r')))) = (1 : A₁) ⊗ₜ[R₁] r'
      simp [Algebra.TensorProduct.one_def])

/-- The left coprojection `A₁ → A₁ ⊗_{R₁} R'` is the composite of the two left coprojections
`A₁ → A₁ ⊗_{R₁} R → (A₁ ⊗_{R₁} R) ⊗_R R'` followed by `Dualizing.baseChangeBaseChangeAlgEquiv`. -/
theorem baseChangeBaseChangeAlgEquiv_comp (R' : Type u) [CommRing R'] [Algebra R R'] :
    letI : Algebra R₁ R' := ((algebraMap R R').comp (algebraMap R₁ R)).toAlgebra
    (baseChangeBaseChangeAlgEquiv (A₁ := A₁) R').toRingHom.comp
        ((Algebra.TensorProduct.includeLeftRingHom :
            A₁ ⊗[R₁] R →+* (A₁ ⊗[R₁] R) ⊗[R] R').comp
          (Algebra.TensorProduct.includeLeftRingHom : A₁ →+* A₁ ⊗[R₁] R)) =
      (Algebra.TensorProduct.includeLeftRingHom : A₁ →+* A₁ ⊗[R₁] R') := by
  let : Algebra R₁ R' := ((algebraMap R R').comp (algebraMap R₁ R)).toAlgebra
  let : IsScalarTower R₁ R R' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  ext a
  show Algebra.TensorProduct.commRight R₁ R' A₁
      (Algebra.TensorProduct.cancelBaseChange R₁ R R' R' A₁
        (Algebra.TensorProduct.congr (AlgEquiv.refl : R' ≃ₐ[R] R')
          (Algebra.TensorProduct.commRight R₁ R A₁).symm
          ((Algebra.TensorProduct.commRight R R' (A₁ ⊗[R₁] R)).symm
            ((a ⊗ₜ[R₁] (1 : R)) ⊗ₜ[R] (1 : R'))))) = a ⊗ₜ[R₁] (1 : R')
  simp

variable [Module.Flat R₁ A₁] [Algebra.FinitePresentation R₁ A₁]

/-- **Transitivity of derived base change for universally relative dualizing complexes.**  If
`K₁` is universally relative dualizing for `R₁ → A₁` and `R₁ → R` is any ring map, then
`K₁ ⊗ᴸ_{A₁} (A₁ ⊗_{R₁} R)` is universally relative dualizing for `R → A₁ ⊗_{R₁} R`. -/
theorem IsUniversallyRelativeDualizing.baseChange {K₁ : DerivedCategory (ModuleCat.{u} A₁)}
    (hK : IsUniversallyRelativeDualizing R₁ A₁ K₁) :
    letI : Module.Flat R (A₁ ⊗[R₁] R) := flat_baseChange R₁ A₁ R
    letI : Algebra.FinitePresentation R (A₁ ⊗[R₁] R) :=
      Algebra.FinitePresentation.equiv (baseChangeComm R₁ A₁ R)
    IsUniversallyRelativeDualizing R (A₁ ⊗[R₁] R)
      ((totalDerivedExtensionScalars.{u, u, u}
        (Algebra.TensorProduct.includeLeftRingHom : A₁ →+* A₁ ⊗[R₁] R)).functor.obj K₁) := by
  let : Module.Flat R (A₁ ⊗[R₁] R) := flat_baseChange R₁ A₁ R
  let : Algebra.FinitePresentation R (A₁ ⊗[R₁] R) :=
    Algebra.FinitePresentation.equiv (baseChangeComm R₁ A₁ R)
  intro R' _ _
  let : Algebra R₁ R' := ((algebraMap R R').comp (algebraMap R₁ R)).toAlgebra
  let : Module.Flat R' ((A₁ ⊗[R₁] R) ⊗[R] R') := flat_baseChange R (A₁ ⊗[R₁] R) R'
  let : Algebra.FinitePresentation R' ((A₁ ⊗[R₁] R) ⊗[R] R') :=
    Algebra.FinitePresentation.equiv (baseChangeComm R (A₁ ⊗[R₁] R) R')
  let : Module.Flat R' (A₁ ⊗[R₁] R') := flat_baseChange R₁ A₁ R'
  let : Algebra.FinitePresentation R' (A₁ ⊗[R₁] R') :=
    Algebra.FinitePresentation.equiv (baseChangeComm R₁ A₁ R')
  let f : A₁ →+* A₁ ⊗[R₁] R := Algebra.TensorProduct.includeLeftRingHom
  let g : A₁ ⊗[R₁] R →+* (A₁ ⊗[R₁] R) ⊗[R] R' := Algebra.TensorProduct.includeLeftRingHom
  exact isRelativeDualizingComplex_of_iso R' _
    (isRelativeDualizingComplex_totalDerivedExtension_of_algEquiv
      (baseChangeBaseChangeAlgEquiv (A₁ := A₁) R')
      (Algebra.TensorProduct.includeLeftRingHom : A₁ →+* A₁ ⊗[R₁] R') (g.comp f)
      (baseChangeBaseChangeAlgEquiv_comp R') K₁ (hK R'))
    ((totalDerivedExtensionScalarsComp f g).app K₁).symm

end BaseChange

end

end Dualizing

end
