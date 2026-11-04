module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactificationChangeCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationCommutantCohomology

/-!
# Changing the compactification, `E`-linearly and Frobenius-equivariantly

Let `X` be separated of finite type over a finite field `k` and `F` an ℓ-adic sheaf on `X` with
coefficients in a `ℤ_ℓ`-algebra `O`, `E = O[1/ℓ]`. For any two compactifications `j₁`, `j₂` of
`X` there is an `E`-linear isomorphism `Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` through `j₁` `≃` through `j₂`
intertwining the geometric Frobenius endomorphisms ([Stacks, Tag 0F7I] read on the Frobenius and
the coefficients): both are compared with a third compactification mapping to each
([Stacks, Tag 0ATU]) by
`Stacks.EtaleCohomology.LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso`, which is
`E`-linear and Frobenius-equivariant. This lets a fibre of Laumon's family, compactified by an
arbitrary compactification, be compared with a base change compactified by the base change of a
given compactification ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main definitions

* `LAdicSheaf.CoefficientSheaf.rationalCompactificationHomLinearEquiv`.
* `LAdicSheaf.CoefficientSheaf.rationalCompactificationLinearEquiv`.

## Main results

* `LAdicSheaf.CoefficientSheaf.rationalCompactificationLinearEquiv_frobenius`.

The standard model `HasDerivedCategory.standard` is used because compactly supported cohomology is
defined there.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (B : BigEtaleSite.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  {X : B.Scheme} [IsNoetherian X.1] {k : Type u} [Field k] [Fintype k]
  (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (kbar : Type u) [Field kbar] [Algebra k kbar]
  {O : Type} [CommRing O] [Algebra ℤ_[ℓ] O] (F : LAdicSheaf.CoefficientSheaf B X ℓ O) (i : ℤ)
  (E : Type) [CommRing E] [Algebra ℚ_[ℓ] E] [Algebra O E]
  [IsLocalization (Submonoid.powers (ℓ : O)) E]

/-- **`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` through `j` `≃` through `l`, `E`-linearly**, for a morphism
`g : j ⟶ l` of compactifications. -/
public def LAdicSheaf.CoefficientSheaf.rationalCompactificationHomLinearEquiv
    {j l : CompactificationOf (Over.mk f)} (g : j ⟶ l) :
    letI := F.rationalCohomologyModule f j kbar i E
    letI := F.rationalCohomologyModule f l kbar i E
    LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i ≃ₗ[E]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f l kbar F.toLAdicSheaf i :=
  letI := F.rationalCohomologyModule f j kbar i E
  letI := F.rationalCohomologyModule f l kbar i E
  { toFun := (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso B ℓ f g kbar
      F.toLAdicSheaf i).hom
    map_add' := map_add _
    map_smul' := fun e v =>
      F.rationalGeometricCompactlySupportedCohomologyHomIso_hom_rationalRingHom B ℓ f g kbar i E e v
    invFun := (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso B ℓ f g kbar
      F.toLAdicSheaf i).inv
    left_inv := fun v => Iso.hom_inv_id_apply
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso B ℓ f g kbar
        F.toLAdicSheaf i) v
    right_inv := fun v => Iso.inv_hom_id_apply
      (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso B ℓ f g kbar
        F.toLAdicSheaf i) v }

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- The `E`-linear isomorphism along a morphism of compactifications intertwines the Frobenius. -/
public theorem LAdicSheaf.CoefficientSheaf.rationalCompactificationHomLinearEquiv_frobenius
    {j l : CompactificationOf (Over.mk f)} (g : j ⟶ l)
    (v : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j kbar F.toLAdicSheaf i) :
    F.rationalCompactificationHomLinearEquiv B ℓ f kbar i E g
        (F.rationalGeometricCompactlySupportedFrobenius f j kbar i E p q hcard v) =
      F.rationalGeometricCompactlySupportedFrobenius f l kbar i E p q hcard
        (F.rationalCompactificationHomLinearEquiv B ℓ f kbar i E g v) :=
  congrArg (fun t => t.hom v)
    (LAdicSheaf.rationalGeometricCompactlySupportedCohomologyHomIso_hom_frobenius B ℓ f g kbar
      F.toLAdicSheaf p q hcard i)

/-- **`Hⁱ_c(X_k̄, F ⊗ ℚ_ℓ)` through `j₁` `≃` through `j₂`, `E`-linearly**, for any two
compactifications, through a third one mapping to both ([Stacks, Tag 0ATU]). -/
public def LAdicSheaf.CoefficientSheaf.rationalCompactificationLinearEquiv
    (j₁ j₂ : CompactificationOf (Over.mk f)) :
    letI := F.rationalCohomologyModule f j₁ kbar i E
    letI := F.rationalCohomologyModule f j₂ kbar i E
    LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j₁ kbar F.toLAdicSheaf i ≃ₗ[E]
      LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j₂ kbar F.toLAdicSheaf i :=
  (F.rationalCompactificationHomLinearEquiv B ℓ f kbar i E
      (IsCofiltered.minToLeft j₁ j₂)).symm.trans
    (F.rationalCompactificationHomLinearEquiv B ℓ f kbar i E (IsCofiltered.minToRight j₁ j₂))

/-- **The change of compactification intertwines the Frobenius.** -/
public theorem LAdicSheaf.CoefficientSheaf.rationalCompactificationLinearEquiv_frobenius
    (j₁ j₂ : CompactificationOf (Over.mk f))
    (v : LAdicSheaf.rationalGeometricCompactlySupportedCohomology B X ℓ f j₁ kbar
      F.toLAdicSheaf i) :
    F.rationalCompactificationLinearEquiv B ℓ f kbar i E j₁ j₂
        (F.rationalGeometricCompactlySupportedFrobenius f j₁ kbar i E p q hcard v) =
      F.rationalGeometricCompactlySupportedFrobenius f j₂ kbar i E p q hcard
        (F.rationalCompactificationLinearEquiv B ℓ f kbar i E j₁ j₂ v) := by
  let a := F.rationalCompactificationHomLinearEquiv B ℓ f kbar i E (IsCofiltered.minToLeft j₁ j₂)
  let c := F.rationalCompactificationHomLinearEquiv B ℓ f kbar i E (IsCofiltered.minToRight j₁ j₂)
  have h1 := F.rationalCompactificationHomLinearEquiv_frobenius B ℓ f kbar i E p q hcard
    (IsCofiltered.minToLeft j₁ j₂) (a.symm v)
  rw [LinearEquiv.apply_symm_apply] at h1
  show c (a.symm _) = _
  rw [a.symm_apply_eq.2 h1.symm]
  exact F.rationalCompactificationHomLinearEquiv_frobenius B ℓ f kbar i E p q hcard
    (IsCofiltered.minToRight j₁ j₂) (a.symm v)

end Stacks.EtaleCohomology

end
