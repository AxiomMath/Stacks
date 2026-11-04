module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Polynomial.Basis
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
public import Mathlib.RingTheory.Noetherian.Orzech
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality.BaseChange

/-!
# The affine line: the right adjoint of pushforward does not preserve coherence

Let `k` be a field and let `f : 𝔸¹_k ⟶ Spec k` be the structure morphism of the affine line,
that is `Spec` of the inclusion `k → k[X]`. The morphism is separated, of finite type, and
both its source and its target are Noetherian schemes, so it is an instance of the situation
of [Stacks, Tag 0A9G]. Nevertheless the right adjoint of
`Rf_* : D_QCoh(𝒪_{𝔸¹}) ⥤ D_QCoh(Spec k)` does not carry complexes with coherent cohomology to
complexes with coherent cohomology.

The obstruction is algebraic. Under the affine identifications of [Stacks, Tag 0A9F] the right
adjoint is `RHom_k(k[X], -)`, and `k[X]` is free over `k`, so `RHom_k(k[X], k)` is
concentrated in degree zero where it is the ordinary linear dual `Hom_k(k[X], k)`. As a
`k`-vector space that dual is the countable product `∏_{n ≥ 0} k`, and as a `k[X]`-module it is
not finitely generated: multiplication by `X` on it is the shift of a sequence, which is
surjective but not injective, and a finitely generated module over the Noetherian ring `k[X]`
has no such endomorphism.

## Main results

* `AlgebraicGeometry.affineLine_isSeparated`, `AlgebraicGeometry.affineLine_locallyOfFiniteType`
  and `AlgebraicGeometry.affineLine_quasiCompact` — the structure morphism of the affine line
  is separated and of finite type.
* `AlgebraicGeometry.affineLine_isLocallyNoetherian` and
  `AlgebraicGeometry.isLocallyNoetherian_Spec_of_field` — source and target are Noetherian.
* `Dualizing.polynomialDerivedHom_isSingle` — `RHom_k(k[X], k)` is concentrated in degree zero.
* `Dualizing.polynomialDerivedHom_homologyZero` — its degree-zero cohomology is the linear dual.
* `Dualizing.polynomialLinearDual_equiv_sequences` — that dual is `∏_{n ≥ 0} k` as a
  `k`-vector space, by reading off coefficients.
* `Dualizing.polynomialDerivedHom_not_finite` — it is not a finite `k[X]`-module. This is the
  obstruction of [Stacks, Tag 0A9G].

## Implementation notes

**No `@[stacks 0A9G]` attribute appears below, deliberately.** Only the algebraic obstruction is
proved here, and at `CategoryTheory.HasDerivedCategory.standard` only. The conclusion of the
example — that the right adjoint of `Rf_*` sends `𝒪_{Spec k}` to a complex with non-coherent
degree-zero cohomology — passes from the obstruction to the sheaf-theoretic statement through
[Stacks, Tag 0A9F], at the locally small model at which derived sheafification is stated; that is
`AlgebraicGeometry.polynomialRightAdjoint_homologyZero_not_finite` in
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/AffineRightAdjointDerivedHom.lean`,
where the attribute is attached. The passage uses two inputs — that derived sheafification is an
equivalence, the remainder of [Stacks, Tag 06Z0], and the identification of derived pushforward
with restriction of scalars, [Stacks, Tag 0DJK]. Both are proved, as
`AlgebraicGeometry.derivedTilde_isEquivalence` and
`AlgebraicGeometry.derivedTildeCompDerivedQuasicoherentPushforwardIso`.

Derived categories here are the ones of `CategoryTheory.HasDerivedCategory.standard`, which is
the model `Dualizing.derivedHom` is stated at.

## References

* [Stacks Project, Tag 0A9G](https://stacks.math.columbia.edu/tag/0A9G)
* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The structure morphism of the affine line over a field is separated, being affine. -/
theorem affineLine_isSeparated (k : Type u) [Field k] :
    IsSeparated (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) :=
  IsSeparated.of_isAffineHom _

/-- The structure morphism of the affine line over a field is locally of finite type:
`k[X]` is a finite-type `k`-algebra. -/
theorem affineLine_locallyOfFiniteType (k : Type u) [Field k] :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.mpr inferInstance

/-- The structure morphism of the affine line over a field is quasi-compact, the affine line
being a compact space. -/
theorem affineLine_quasiCompact (k : Type u) [Field k] :
    QuasiCompact (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) :=
  AlgebraicGeometry.quasiCompact_of_compactSpace _

/-- The affine line over a field is a Noetherian scheme. -/
theorem affineLine_isLocallyNoetherian (k : Type u) [Field k] :
    IsLocallyNoetherian (Spec (CommRingCat.of (Polynomial k))) :=
  isLocallyNoetherian_Spec.mpr inferInstance

/-- The spectrum of a field is a Noetherian scheme. -/
theorem isLocallyNoetherian_Spec_of_field (k : Type u) [Field k] :
    IsLocallyNoetherian (Spec (CommRingCat.of k)) :=
  isLocallyNoetherian_Spec.mpr inferInstance

end AlgebraicGeometry

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard

/-- Coextension of scalars along a ring homomorphism is additive. -/
local instance additive_coextendScalars {A : Type u} {B : Type u} [Ring A] [Ring B]
    (f : A →+* B) : (ModuleCat.coextendScalars.{u, u, u} f).Additive where
  map_add := by intros; ext; rfl

/-- Coextension of scalars along a homomorphism out of a division ring is exact: it is a right
adjoint, and it preserves epimorphisms because its left adjoint, restriction of scalars,
preserves projective objects — every module over a division ring is free, hence projective. -/
local instance preservesFiniteColimits_coextendScalars {A : Type u} {B : Type u}
    [DivisionRing A] [Ring B] (f : A →+* B) :
    PreservesFiniteColimits (ModuleCat.coextendScalars.{u, u, u} f) := by
  have hproj : (ModuleCat.restrictScalars.{u} f).PreservesProjectiveObjects :=
    { projective_obj := fun {M} _ =>
        ModuleCat.projective_of_categoryTheory_projective
          (P := (ModuleCat.restrictScalars.{u} f).obj M) }
  have : (ModuleCat.coextendScalars.{u, u, u} f).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction_of_preservesProjectiveObjects
      (ModuleCat.restrictCoextendScalarsAdj.{u} f)
  have : (ModuleCat.coextendScalars.{u, u, u} f).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  exact Functor.preservesFiniteColimits_of_preservesHomology _

/-- **Stacks 0A9G.** Since `k[X]` is free as a `k`-module, the derived Hom `RHom_k(k[X], -)` is
already exact, so at the one-term complex `k` it is concentrated in degree zero, where it is
ordinary coextension of scalars `Hom_k(k[X], k)`. -/
theorem polynomialDerivedHom_isSingle (k : Type u) [Field k] :
    Nonempty ((derivedHom.{u, u, u} (Polynomial.C : k →+* Polynomial k)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (Polynomial k)) 0).obj
        ((ModuleCat.coextendScalars.{u, u, u}
          (Polynomial.C : k →+* Polynomial k)).obj (ModuleCat.of k k))) := by
  let φ : k →+* Polynomial k := Polynomial.C
  let F := ModuleCat.coextendScalars.{u, u, u} φ
  have hF : F.mapDerivedCategory.IsRightDerivedFunctor F.mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (ModuleCat.{u} k) (ComplexShape.up ℤ)) :=
    Functor.isRightDerivedFunctor_of_inverts
      (HomotopyCategory.quasiIso (ModuleCat.{u} k) (ComplexShape.up ℤ))
      F.mapDerivedCategory F.mapDerivedCategoryFactorsh
  have hG : (derivedHom.{u, u, u} φ).IsRightDerivedFunctor (derivedHomComparison.{u, u, u} φ)
      (HomotopyCategory.quasiIso (ModuleCat.{u} k) (ComplexShape.up ℤ)) := by
    have := coextendScalars_hasPointwiseRightDerivedFunctor.{u, u, u} φ
    dsimp [derivedHom, derivedHomComparison]
    infer_instance
  let e : F.mapDerivedCategory ≅ derivedHom.{u, u, u} φ :=
    Functor.rightDerivedUnique F.mapDerivedCategory (derivedHom.{u, u, u} φ)
      F.mapDerivedCategoryFactorsh.inv (derivedHomComparison.{u, u, u} φ)
      (HomotopyCategory.quasiIso (ModuleCat.{u} k) (ComplexShape.up ℤ))
  exact ⟨(e.app ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj
    (ModuleCat.of k k))).symm ≪≫ (F.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of k k)⟩

/-- **Stacks 0A9G.** The degree-zero cohomology of `RHom_k(k[X], k)` is the `k[X]`-module
`Hom_k(k[X], k)` of `k`-linear forms on the polynomial ring. -/
theorem polynomialDerivedHom_homologyZero (k : Type u) [Field k] :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Polynomial k)) 0).obj
        ((derivedHom.{u, u, u} (Polynomial.C : k →+* Polynomial k)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k))) ≅
      (ModuleCat.coextendScalars.{u, u, u}
        (Polynomial.C : k →+* Polynomial k)).obj (ModuleCat.of k k)) := by
  obtain ⟨e⟩ := polynomialDerivedHom_isSingle k
  exact ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} (Polynomial k)) 0).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{u} (Polynomial k)) 0).app _⟩

/-- **Stacks 0A9G.** As a `k`-vector space the linear dual of `k[X]` is the countable product
`∏_{n ≥ 0} k`, the isomorphism reading off the values on the monomials. -/
theorem polynomialLinearDual_equiv_sequences (k : Type u) [Field k] :
    ∃ e : (Polynomial k →ₗ[k] k) ≃ₗ[k] (ℕ → k),
      ∀ (ψ : Polynomial k →ₗ[k] k) (n : ℕ), e ψ n = ψ (Polynomial.monomial n 1) := by
  refine ⟨((Polynomial.basisMonomials k).constr k).symm, fun ψ n => ?_⟩
  simp [Polynomial.coe_basisMonomials]

/-- **Stacks 0A9G.** The degree-zero cohomology of `RHom_k(k[X], k)` is not a finite
`k[X]`-module.

Multiplication by `X` on `Hom_k(k[X], k)` is, in the coordinates of
`Dualizing.polynomialLinearDual_equiv_sequences`, the shift `(a₀, a₁, …) ↦ (a₁, a₂, …)`. That is
surjective and has the nonzero element `(1, 0, 0, …)` in its kernel; over the Noetherian ring
`k[X]` a surjective endomorphism of a finite module is injective, so the module is not
finite. -/
theorem polynomialDerivedHom_not_finite (k : Type u) [Field k] :
    ¬ Module.Finite (Polynomial k)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Polynomial k)) 0).obj
        ((derivedHom.{u, u, u} (Polynomial.C : k →+* Polynomial k)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)))) := by
  let φ : k →+* Polynomial k := Polynomial.C
  let M := (ModuleCat.coextendScalars.{u, u, u} φ).obj (ModuleCat.of k k)
  intro hfinite
  obtain ⟨hiso⟩ := polynomialDerivedHom_homologyZero k
  have hfiniteM : Module.Finite (Polynomial k) M :=
    Module.Finite.of_surjective hiso.hom.hom (fun m => ⟨hiso.inv m, by simp⟩)
  let T : (↑M) →ₗ[Polynomial k] (↑M) :=
    { toFun := fun m => Polynomial.X • m
      map_add' := fun m n => smul_add _ _ _
      map_smul' := fun p m => by
        calc Polynomial.X • (p • m) = (Polynomial.X * p) • m := smul_smul _ _ _
          _ = (p * Polynomial.X) • m := by rw [mul_comm]
          _ = p • (Polynomial.X • m) := (smul_smul _ _ _).symm }
  let D := (ModuleCat.restrictScalars φ).obj (ModuleCat.of (Polynomial k) (Polynomial k))
  let d : (↑D) ≃ₗ[k] Polynomial k :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r p => by
        dsimp
        rw [ModuleCat.restrictScalars.smul_def (f := φ)
          (M := ModuleCat.of (Polynomial k) (Polynomial k))]
        simpa [φ] using
          (IsScalarTower.algebraMap_smul (A := Polynomial k) r (show Polynomial k from p)) }
  let b := (Polynomial.basisMonomials k).map d.symm
  let c : (↑M) ≃ₗ[Polynomial k] (↑D →ₗ[k] ↑(ModuleCat.of k k)) :=
    ModuleCat.CoextendScalars.equiv φ (ModuleCat.of k k)
  let e : (D →ₗ[k] (ModuleCat.of k k)) ≃ₗ[k] (ℕ → (ModuleCat.of k k)) :=
    (b.constr (ModuleCat.of k k)).symm
  have he (g : D →ₗ[k] (ModuleCat.of k k)) (n : ℕ) : e g n = g (b n) :=
    b.constr_symm_apply (S := k) g n
  have hb (n : ℕ) : b n = d.symm (Polynomial.monomial n 1) := by
    simp [b, Polynomial.coe_basisMonomials]
  have hsmul (g : D →ₗ[k] (ModuleCat.of k k)) (p : Polynomial k) :
      ((Polynomial.X : Polynomial k) • g) (d.symm p) =
        g (d.symm (p * (Polynomial.X : Polynomial k))) := rfl
  have hct (ψ : (↑M)) : c (T ψ) = (Polynomial.X : Polynomial k) • c ψ :=
    LinearEquiv.map_smul c (Polynomial.X : Polynomial k) ψ
  let Φ : M ≃+ (ℕ → ModuleCat.of k k) := c.toAddEquiv.trans e.toAddEquiv
  have hshift (ψ : M) (n : ℕ) : Φ (T ψ) n = Φ ψ (n + 1) := by
    change e (c (T ψ)) n = e (c ψ) (n + 1)
    rw [he, he, hct, hb n, hsmul, hb (n + 1)]
    refine congrArg (c ψ) (congrArg d.symm ?_)
    simp [Polynomial.X, Polynomial.monomial_mul_monomial]
  have hsurj : Function.Surjective T := by
    intro ψ
    refine ⟨Φ.symm (fun n => if n = 0 then 0 else Φ ψ (n - 1)), Φ.injective (funext fun n => ?_)⟩
    rw [hshift]
    simp
  let δ : ℕ → (ModuleCat.of k k) := fun n => if n = 0 then 1 else 0
  let ψ₀ : M := Φ.symm δ
  have hψ₀ : ψ₀ ≠ 0 := by
    intro hz
    simpa [ψ₀, δ] using congrFun (congrArg Φ hz) 0
  have hTψ₀ : T ψ₀ = 0 := by
    refine Φ.injective (funext fun n => ?_)
    rw [hshift]
    simp [ψ₀, δ]
  have : IsNoetherian (Polynomial k) M := inferInstance
  exact hψ₀ ((IsNoetherian.injective_of_surjective_endomorphism T hsurj)
    (by rw [hTψ₀, map_zero]))

end Dualizing

end
