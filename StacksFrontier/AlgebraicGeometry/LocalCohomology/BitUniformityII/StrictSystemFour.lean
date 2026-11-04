module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityII.DerivedBaseChangeQuotients
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityII.StrictDerivedReduction

/-!
# System (4) of Stacks 0GA5 is strictly pro-isomorphic to system (2)

Let `P → A` be a ring map with `P` Noetherian, `J ⊆ P` an ideal and `I = JA`, and let `M` be a
complex of `A`-modules.  Stacks 0GA5 considers the inverse system (4) `M ⊗ᴸ_P P/Jⁿ` in `D(A)`,
formed with the derived change-of-rings tensor product `M ⊗ᴸ_P - : D(P) ⥤ D(A)` of
[Stacks, Tag 06Y6], and asserts that if `P → A` is finite then (4) is *strictly*
pro-isomorphic to the system (2) `M ⊗ᴸ_A A/Iⁿ`.

The source's argument is followed: `M ⊗ᴸ_P P/Jⁿ = M ⊗ᴸ_A (A ⊗ᴸ_P P/Jⁿ)` by the change-of-rings
isomorphism of [Stacks, Tag 06Y6], and the system `A ⊗ᴸ_P P/Jⁿ` is strictly pro-isomorphic to
`A ⊗_P P/Jⁿ = A/Iⁿ`
(`Stacks.LocalCohomology.UniformityII.hasUniformInverses_extensionCounit_quotientSingleSystem`).

## Main definitions

* `Stacks.LocalCohomology.UniformityII.extendScalarsQuotientIso`: `A ⊗_P P/K ≅ A/KA`.
* `Stacks.LocalCohomology.UniformityII.systemFour`,
  `Stacks.LocalCohomology.UniformityII.systemTwo`: the systems (4) and (2) for the canonical
  derived change-of-rings tensor product.
* `Stacks.LocalCohomology.UniformityII.systemFourToTwo`: the comparison (4) ⟶ (2).

## Main results

* `Stacks.LocalCohomology.UniformityII.hasUniformInverses_systemFourToTwo` and
  `Stacks.LocalCohomology.UniformityII.isIso_proHom_systemFourToTwo`: **if `P → A` is finite,
  the comparison is a strict pro-isomorphism.**

## References

* [Stacks Project, Tag 0GA5](https://stacks.math.columbia.edu/tag/0GA5)
* [Stacks Project, Tag 06Y6](https://stacks.math.columbia.edu/tag/06Y6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.InverseSequence
open scoped ChangeOfRings

attribute [local instance 2000] HasDerivedCategory.standard

namespace Stacks.LocalCohomology.UniformityII

universe u

variable {P A : Type u} [CommRing P] [CommRing A] (f : P →+* A)

/-! ### Base change of a quotient -/

/-- Extension of scalars of `P/K` along `f : P → A` is `A/KA`. -/
noncomputable def extendScalarsQuotientIso (K : Ideal P) (L : Ideal A) (h : K.map f = L) :
    (ModuleCat.extendScalars.{u, u, u} f).obj (ModuleCat.of P (P ⧸ K)) ≅
      ModuleCat.of A (A ⧸ L) := by
  letI := f.toAlgebra
  exact ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot A K).toLinearEquiv.symm.trans
    (Submodule.quotEquivOfEq _ _ h)).toModuleIso

/-- The isomorphism `extendScalarsQuotientIso` sends `a ⊗ (p mod K)` to `f p * a mod L`. -/
theorem extendScalarsQuotientIso_hom_tmul (K : Ideal P) (L : Ideal A) (h : K.map f = L)
    (a : A) (p : P) :
    (extendScalarsQuotientIso f K L h).hom (a ⊗ₜ[P,f] (Ideal.Quotient.mk K p)) =
      Ideal.Quotient.mk L (f p * a) := rfl

/-- `A ⊗_P P/K ≅ A/KA` is natural in the ideals. -/
theorem extendScalarsQuotientIso_naturality {K K' : Ideal P} {L L' : Ideal A} (hK : K ≤ K')
    (hL : L ≤ L') (h : K.map f = L) (h' : K'.map f = L') :
    (ModuleCat.extendScalars.{u, u, u} f).map (ModuleCat.ofHom (Submodule.factor hK)) ≫
        (extendScalarsQuotientIso f K' L' h').hom =
      (extendScalarsQuotientIso f K L h).hom ≫ ModuleCat.ofHom (Submodule.factor hL) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective m
  rfl

/-! ### The systems (4) and (2) -/

variable (M : CochainComplex (ModuleCat.{u} A) ℤ)

/-- The derived change-of-rings tensor product `M ⊗ᴸ_P - : D(P) ⥤ D(A)` of
[Stacks, Tag 06Y6]. -/
noncomputable abbrev changeOfRings :
    CochainComplex.DerivedTensor.DerivedTensorChangeOfRings.{u, u, u} f M :=
  CochainComplex.DerivedTensor.canonicalDerivedTensorChangeOfRings.{u, u, u} f M

/-- **System (4) of Stacks 0GA5**: `n ↦ M ⊗ᴸ_P P/Jⁿ⁺¹` in `D(A)`. -/
noncomputable abbrev systemFour (J : Ideal P) : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
  quotientSingleSystem J ⋙ DerivedCategory.Q ⋙ (changeOfRings f M).F

/-- **System (2) of Stacks 0GA5**: `n ↦ M ⊗ᴸ_A A/Iⁿ⁺¹` in `D(A)`, for the derived tensor
product over `A` of the change-of-rings construction. -/
noncomputable abbrev systemTwo (I : Ideal A) : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
  quotientSingleSystem I ⋙ DerivedCategory.Q ⋙ (changeOfRings f M).G

/-- The isomorphism of systems of modules `A ⊗_P P/Jⁿ⁺¹ ≅ A/Iⁿ⁺¹`, for `I = JA`. -/
noncomputable def extendQuotientModuleSystemIso (J : Ideal P) (I : Ideal A) (hI : I = J.map f) :
    quotientModuleSystem J ⋙ ModuleCat.extendScalars.{u, u, u} f ≅ quotientModuleSystem I :=
  NatIso.ofComponents
    (fun n ↦ extendScalarsQuotientIso f (J ^ (n.unop + 1)) (I ^ (n.unop + 1))
      (by rw [Ideal.map_pow, hI]))
    (fun {n m} g ↦ by
      have h : m.unop ≤ n.unop := leOfHom g.unop
      have hg : g = (homOfLE h).op := Subsingleton.elim _ _
      subst hg
      rw [Functor.comp_map, quotientModuleSystem_map, quotientModuleSystem_map]
      exact extendScalarsQuotientIso_naturality f _ _ _ _)

/-- The isomorphism of systems of complexes `A ⊗_P (P/Jⁿ⁺¹)[0] ≅ (A/Iⁿ⁺¹)[0]`, for `I = JA`. -/
noncomputable def extendQuotientSingleSystemIso (J : Ideal P) (I : Ideal A) (hI : I = J.map f) :
    quotientSingleSystem J ⋙ CochainComplex.extendScalarsLarge.{u, u, u} f ≅
      quotientSingleSystem I :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (quotientModuleSystem J)
      (HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.extendScalars.{u, u, u} f) (ComplexShape.up ℤ) 0) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (extendQuotientModuleSystemIso f J I hI)
      (CochainComplex.singleFunctor (ModuleCat.{u} A) 0)

/-- **The comparison from system (4) to system (2)** of Stacks 0GA5: the change-of-rings
isomorphism `M ⊗ᴸ_P P/Jⁿ ≅ M ⊗ᴸ_A (A ⊗ᴸ_P P/Jⁿ)` of [Stacks, Tag 06Y6], followed by
`M ⊗ᴸ_A -` applied to the counit `A ⊗ᴸ_P P/Jⁿ ⟶ A ⊗_P P/Jⁿ = A/Iⁿ`. -/
noncomputable def systemFourToTwo (J : Ideal P) (I : Ideal A) (hI : I = J.map f) :
    NatTrans (systemFour f M J) (systemTwo f M I) :=
  Functor.whiskerLeft (quotientSingleSystem J ⋙ DerivedCategory.Q)
      (changeOfRings f M).changeOfRings.hom ≫
    Functor.whiskerRight (Functor.whiskerLeft (quotientSingleSystem J) (changeOfRings f M).alphaB)
      (changeOfRings f M).G ≫
    Functor.whiskerRight (Functor.whiskerRight (extendQuotientSingleSystemIso f J I hI).hom
      DerivedCategory.Q) (changeOfRings f M).G

/-- **Stacks 0GA5, system (4) against system (2)**: if `P → A` is finite (and `P` Noetherian),
the comparison from `M ⊗ᴸ_P P/Jⁿ` to `M ⊗ᴸ_A A/Iⁿ`, `I = JA`, has inverses over a shift
independent of `n`. -/
theorem hasUniformInverses_systemFourToTwo [IsNoetherianRing P] (hf : f.Finite) (J : Ideal P)
    (I : Ideal A) (hI : I = J.map f) :
    HasUniformInverses (systemFourToTwo f M J I hI) := by
  refine HasUniformInverses.comp (HasUniformInverses.of_isIso _)
    (HasUniformInverses.comp ?_ (HasUniformInverses.of_isIso _))
  exact (hasUniformInverses_extensionCounit_quotientSingleSystem f hf J _ _).whiskerRight _

/-- **Stacks 0GA5: if `P → A` is finite, system (4) is strictly pro-isomorphic to system
(2).**  Let `P` be Noetherian, `f : P → A` a finite ring map, `J ⊆ P` an ideal with `I = JA`,
and `M` a complex of `A`-modules.  Then the comparison from the system `n ↦ M ⊗ᴸ_P P/Jⁿ⁺¹` to
the system `n ↦ M ⊗ᴸ_A A/Iⁿ⁺¹` is an isomorphism of the strict pro-category of `D(A)`.

The source states the remark for a bounded complex `M` of finite modules over a Noetherian
ring `A`; neither hypothesis is used here. -/
@[stacks 0GA5 "if `P → A` is finite, the system (4) is strictly pro-isomorphic to the system (2)"]
theorem isIso_proHom_systemFourToTwo [IsNoetherianRing P] (hf : f.Finite) (J : Ideal P)
    (I : Ideal A) (hI : I = J.map f) :
    IsIso (proHom (⟨0, systemFourToTwo f M J I hI⟩ :
      StrictProHomRep (systemFour f M J) (systemTwo f M I))) :=
  isIso_proHom_of_hasUniformInverses _ (hasUniformInverses_systemFourToTwo f M hf J I hI)

end Stacks.LocalCohomology.UniformityII

end
