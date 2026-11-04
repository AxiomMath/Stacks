module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.CompositionFiniteType
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatAlgebraBaseChangeIso
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.FlatEpimorphism
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.PolynomialEvalDualityReduction
public import StacksFrontier.Homology.Tor.DerivedExtensionScalarsTotalComp

/-!
# Upper shriek under flat base change followed by an open immersion

Let `R → A` be flat of finite type with `R` Noetherian, let `R → R'` be a homomorphism with `R'`
Noetherian, and let `R' ⊗_R A → B` be a ring map whose spectrum map is an open immersion. Write
`ψ : R' → B` for the composite. Then for `K ∈ D(R)` with `K ⊗_R^L R'` bounded below,

  `φ^!(K) ⊗_A^L B ≅ ψ^!(K ⊗_R^L R')`.

This is the algebra behind [Stacks, Tag 0BZY]: the flat base change [Stacks, Tag 0BZS] gives
`φ^!(K) ⊗_A^L (R' ⊗_R A) ≅ φ'^!(K ⊗_R^L R')`, the composition [Stacks, Tag 0BZT] gives
`ψ^! ≅ (R' ⊗_R A → B)^! ∘ φ'^!` on `D⁺(R')`, and [Stacks, Tag 0C0H] computes the upper shriek of
an open immersion as `- ⊗^L B`.

## Main results

* `Dualizing.nonempty_derivedTensorProductOver_unitObject_iso` — derived tensor product
  over `R` with the unit of `D(A)` is derived extension of scalars.
* `Dualizing.nonempty_totalDerivedExtensionScalars_upperShriekFunctor_iso_of_isOpenImmersion` —
  the base change isomorphism above.
-/

@[expose] public noncomputable section

open CategoryTheory CochainComplex.DerivedExtensionScalars AlgebraicGeometry
open scoped TensorProduct

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

/-- **Derived tensor product over `R` with the unit of `D(A)` is derived extension of scalars**,
for any ring map `f : R → A`. -/
theorem nonempty_derivedTensorProductOver_unitObject_iso {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) :
    Nonempty (derivedTensorProductOver.{u, u} f (Stacks0BZE.unitObject.{u, u} A) ≅
      (totalDerivedExtensionScalars.{u, u, u} f).functor) := by
  let D := totalDerivedExtensionScalars.{u, u, u} f
  let Lc := ((DerivedCategory.Qh (C := ModuleCat.{u} A)).objPreimage
    (Stacks0BZE.unitObject.{u, u} A)).as
  let eL : (DerivedCategory.Qh (C := ModuleCat.{u} A)).obj
      ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj Lc) ≅
      (DerivedCategory.Qh (C := ModuleCat.{u} A)).obj
        ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj
          (Stacks0BZE.unitComplex.{u, u} A)) :=
    (DerivedCategory.Qh (C := ModuleCat.{u} A)).objObjPreimageIso _ ≪≫
      Stacks0BZE.unitObjectIso.{u, u} A ≪≫
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app _).symm
  obtain ⟨e⟩ := derivedTensorRepresentative_congr.{u, u} f Lc (Stacks0BZE.unitComplex.{u, u} A) eL
  exact ⟨e ≪≫ InvertibleKernel.derivedTensorUnitComplexIsoDerivedExtension f D.functor
    D.comparison D.isLeftDerived⟩

/-- **Upper shriek under flat base change followed by an open immersion.** Let `φ : R → A` be
flat of finite type with `R` Noetherian, presented by `p`, let `R → R'` be a homomorphism with
`R'` Noetherian, let `e : R' ⊗_R A → B` be a ring map whose spectrum map is an open immersion, and
let `q` present `ψ : R' → B`, the composite of `e` with `R' → R' ⊗_R A`. Then for `K ∈ D(R)` with
`K ⊗_R^L R'` bounded below, `φ^!(K) ⊗_A^L B ≅ ψ^!(K ⊗_R^L R')`. -/
theorem nonempty_totalDerivedExtensionScalars_upperShriekFunctor_iso_of_isOpenImmersion
    {R R' A B : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R R'] [IsNoetherianRing R] [IsNoetherianRing R']
    (hflat : (algebraMap R A).Flat) (p : PolynomialPresentation (algebraMap R A))
    (e : R' ⊗[R] A →+* B) (he : IsOpenImmersion (Spec.map (CommRingCat.ofHom e)))
    (q : PolynomialPresentation (e.comp (algebraMap R' (R' ⊗[R] A))))
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : DerivedCategoryB.IsBoundedBelow
      ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor.obj K)) :
    Nonempty ((totalDerivedExtensionScalars.{u, u, u}
        (e.comp (Algebra.TensorProduct.includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom)).functor.obj
          (p.upperShriekFunctor.{u, u}.obj K) ≅
      q.upperShriekFunctor.{u, u}.obj
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor.obj K)) := by
  have : Algebra.FiniteType R A := RingHom.finiteType_algebraMap.mp p.finiteType
  have hft : (algebraMap R' (R' ⊗[R] A)).FiniteType :=
    RingHom.finiteType_algebraMap.mpr inferInstance
  obtain ⟨p'⟩ := nonempty_polynomialPresentation (algebraMap R' (R' ⊗[R] A)) hft
  obtain ⟨⟨qe⟩, h0C0H⟩ :=
    nonempty_upperShriekFunctor_iso_derivedTensorProduct_of_isOpenImmersion.{u, u} e he
  obtain ⟨eC⟩ := h0C0H qe
  obtain ⟨eU⟩ := nonempty_derivedTensorProductOver_unitObject_iso e
  let bcR := totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')
  let bcT := totalDerivedExtensionScalars.{u, u, u}
    (Algebra.TensorProduct.includeRight : A →ₐ[R] R' ⊗[R] A).toRingHom
  obtain ⟨eS⟩ :=
    PolynomialPresentation.nonempty_upperShriekFunctor_comp_iso_of_flat.{u, u} hflat p p'
    bcR.functor bcR.comparison bcR.isLeftDerived bcT.functor bcT.comparison bcT.isLeftDerived
  obtain ⟨τ, hτ⟩ := PolynomialPresentation.exists_upperShriekComp_of_finiteType.{u, u} p' qe q
  have := hτ _ hK
  let bcE := totalDerivedExtensionScalars.{u, u, u} e
  exact ⟨((totalDerivedExtensionScalarsComp.{u, u} _ e).app _).symm ≪≫
    bcE.functor.mapIso (eS.app K) ≪≫ (eU.app _).symm ≪≫ (eC.app _).symm ≪≫ asIso (τ.app _)⟩

end Dualizing

end
