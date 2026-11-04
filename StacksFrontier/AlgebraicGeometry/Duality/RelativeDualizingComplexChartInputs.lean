module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexChartConverse
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectAffineCriterion
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseOpen
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeNoetherian
public import StacksFrontier.RingTheory.Dualizing.RelativeExistenceInputs

/-!
# Inputs for relative dualizing complexes on an affine chart

Let `g : X ⟶ S` be a flat, locally finitely presented morphism of affine schemes, and put
`A = Γ(X, ⊤)`, `R = Γ(S, ⊤)`. The first step of the proof of Stacks 0E2X takes a relative
dualizing complex `K_A` for `R → A` (Stacks 0E2F) and the complex of quasi-coherent sheaves
`K_A^~` it determines (Stacks 06Z0). This file proves the two properties of `K_A^~` that do not
involve the map `ξ`: it is `S`-perfect (Stacks 0DI2 on a single chart), and
`R ℰom(𝒪_X, L pr₁^*K_A^~|_W) ≅ 𝒪_X[0]` for every diagonal open `W` (the proof of Stacks 0E2U run
backwards). It also contains the linear-algebra step that turns the latter into a map `ξ`.

## Main definitions

* `AlgebraicGeometry.Scheme.affineDerivedTilde`: on an affine scheme `X`, the object of
  `D(𝒪_X)` attached to an object of `D(Γ(X, ⊤))` by Stacks 06Z0.

## Main results

* `AlgebraicGeometry.Scheme.nonempty_derivedSectionsUnbounded_affineDerivedTilde_iso`:
  `RΓ(X, M^~) ≅ M`.
* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_affineDerivedTilde`: if `M` is `R`-perfect,
  then `M^~` is `S`-perfect.
* `AlgebraicGeometry.Scheme.Hom.exists_isPerfectRelativeTo_diagonalExactSupport_iso`: an
  `S`-perfect `K` with `R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]`.
* `CategoryTheory.isIso_of_leftInverse_of_generator`: an injective linear map between free
  modules of rank one with a linear left inverse carries a generator to an isomorphism, read on
  morphisms of a linear category.

## Implementation notes

The derived categories are those of `CategoryTheory.HasDerivedCategory.standard`, the model at
which `AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex` is stated.

## References

* [Stacks Project, Lemma 48.28.6 (Tag 0E2X)](https://stacks.math.columbia.edu/tag/0E2X)
* [Stacks Project, Lemma 47.27.5 (Tag 0E2F)](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Lemma 36.3.5 (Tag 06Z0)](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Lemma 36.35.3 (Tag 0DI2)](https://stacks.math.columbia.edu/tag/0DI2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite StrictlyPerfect
open scoped TensorProduct

universe u

section StandardModel

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsAffine X]

/-- **The complex of quasi-coherent sheaves attached to a complex of `Γ(X, ⊤)`-modules** on an
affine scheme `X`, Stacks 06Z0: `M ↦ M^~` on `Spec Γ(X, ⊤)`, carried to `X` along
`X ≅ Spec Γ(X, ⊤)`. -/
abbrev affineDerivedTilde (M : DerivedCategory (ModuleCat.{u} Γ(X, ⊤))) :
    DerivedCategory X.Modules :=
  (Modules.restrictFunctor X.isoSpec.hom).mapDerivedCategory.obj
    ((tilde.functor Γ(X, ⊤)).mapDerivedCategory.obj M)

/-- `M^~` has quasi-coherent cohomology sheaves. -/
theorem isQuasicoherent_homology_affineDerivedTilde
    (M : DerivedCategory (ModuleCat.{u} Γ(X, ⊤))) (i : ℤ) :
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      (affineDerivedTilde X M)).IsQuasicoherent :=
  isQuasicoherent_homology_restrictFunctor_mapDerivedCategory X.isoSpec.hom
    (fun n => isQuasicoherent_homology_mapDerivedCategory_obj _ M n) i

/-- The three restrictions `Spec Γ(X, ⊤) ⟶ ⊤ ⟶ X ⟶ Spec Γ(X, ⊤)` compose to the identity. -/
theorem isoSpec_inv_ι_isoSpec_hom :
    (isAffineOpen_top X).isoSpec.inv ≫ (⊤ : X.Opens).ι ≫ X.isoSpec.hom = 𝟙 _ := by
  rw [← Category.assoc, IsAffineOpen.isoSpec_inv_ι, IsAffineOpen.fromSpec_top, Iso.inv_hom_id]

/-- **Stacks 06Z0: `RΓ(X, M^~) ≅ M`** on an affine scheme, for every object `M` of
`D(Γ(X, ⊤))`. -/
theorem nonempty_derivedSectionsUnbounded_affineDerivedTilde_iso
    (M : DerivedCategory (ModuleCat.{u} Γ(X, ⊤))) :
    Nonempty ((derivedSectionsUnbounded X ⊤).obj (affineDerivedTilde X M) ≅ M) := by
  let hU := isAffineOpen_top X
  obtain ⟨e₁⟩ := hU.nonempty_iso_derivedSectionsSpec (affineDerivedTilde X M)
  let T := (tilde.functor Γ(X, ⊤)).mapDerivedCategory.obj M
  let a := hU.isoSpec.inv
  let b := (⊤ : X.Opens).ι
  let c := X.isoSpec.hom
  have eF : Modules.restrictFunctor c ⋙ Modules.restrictFunctor b ⋙ Modules.restrictFunctor a ≅
      𝟭 _ :=
    (Functor.associator _ _ _).symm ≪≫
    (Functor.isoWhiskerRight (Modules.restrictFunctorComp b c) _).symm ≪≫
    (Modules.restrictFunctorComp a (b ≫ c)).symm ≪≫
    Modules.restrictFunctorCongr (isoSpec_inv_ι_isoSpec_hom X) ≪≫
    Modules.restrictFunctorId
  have e₂ : hU.derivedRestrictSpec (affineDerivedTilde X M) ≅ T :=
    ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
        (Modules.restrictFunctor c ⋙ Modules.restrictFunctor b)
        (Modules.restrictFunctor a)).app T ≪≫
      (Modules.restrictFunctor a).mapDerivedCategory.mapIso
        ((Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso
          (Modules.restrictFunctor c) (Modules.restrictFunctor b)).app T)).symm ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _
      (Functor.associator _ _ _ ≪≫ eF)).app T ≪≫
    Stacks.Homology.mapDerivedCategoryIdIso.app T
  have hunit := isIso_derivedTildeGlobalSectionsAdjunction_unit Γ(X, ⊤)
  have e₃ : (derivedGlobalSectionsOver (𝟙 (Spec Γ(X, ⊤)))).obj T ≅ M :=
    (derivedGlobalSectionsOver (𝟙 (Spec Γ(X, ⊤)))).mapIso
      ((derivedTildeCompι Γ(X, ⊤)).app M).symm ≪≫
    (asIso ((derivedTildeGlobalSectionsAdjunction Γ(X, ⊤)).val.unit.app M)).symm
  exact ⟨e₁.symm ≪≫ (derivedGlobalSectionsOver (𝟙 (Spec Γ(X, ⊤)))).mapIso e₂ ≪≫ e₃⟩

end AlgebraicGeometry.Scheme


namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (g : X ⟶ S) [IsAffine X] [IsAffine S] [Flat g]
  [LocallyOfFinitePresentation g]

/-- **Relative perfectness of `M^~`**, Stacks 0DI2 on the single chart `X ⟶ S`: for a flat,
locally finitely presented morphism of affine schemes, if `M` is `Γ(S, ⊤)`-perfect then the
object `M^~` of `D(𝒪_X)` is `S`-perfect. -/
theorem isPerfectRelativeTo_affineDerivedTilde (M : DerivedCategory (ModuleCat.{u} Γ(X, ⊤)))
    (hM : letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := (g.appLE ⊤ ⊤ le_top).hom.toAlgebra
      letI : Module.Flat Γ(S, ⊤) Γ(X, ⊤) :=
        moduleFlat_appLE g (isAffineOpen_top S) (isAffineOpen_top X) le_top rfl
      letI : Algebra.FinitePresentation Γ(S, ⊤) Γ(X, ⊤) :=
        algebraFinitePresentation_appLE g (isAffineOpen_top S) (isAffineOpen_top X) le_top rfl
      PseudoCoherence.IsRelativelyPerfect
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct Γ(S, ⊤)).tensor
        (StacksDraft.TorAmplitude.canonicalTensorComparison Γ(S, ⊤))
        (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived Γ(S, ⊤)) M) :
    IsPerfectRelativeTo g
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace g.base)) (affineDerivedTilde X M) := by
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := (g.appLE ⊤ ⊤ le_top).hom.toAlgebra
  let : Module.Flat Γ(S, ⊤) Γ(X, ⊤) :=
    moduleFlat_appLE g (isAffineOpen_top S) (isAffineOpen_top X) le_top rfl
  let : Algebra.FinitePresentation Γ(S, ⊤) Γ(X, ⊤) :=
    algebraFinitePresentation_appLE g (isAffineOpen_top S) (isAffineOpen_top X) le_top rfl
  obtain ⟨eΓ⟩ := nonempty_derivedSectionsUnbounded_affineDerivedTilde_iso X M
  have h31 := (isPerfectRelativeTo_tfae g (affineDerivedTilde X M)
    (isQuasicoherent_homology_affineDerivedTilde X M)).out 3 1
  refine h31.1 ⟨PUnit, fun _ => ⟨⊤, isAffineOpen_top S⟩, ?_, fun _ =>
    ⟨PUnit, fun _ => ⟨⊤, isAffineOpen_top X⟩, fun _ => le_top, ?_, fun _ => ?_⟩⟩
  · exact top_le_iff.mp (le_iSup_of_le PUnit.unit le_rfl)
  · exact (top_le_iff.mp (le_iSup_of_le PUnit.unit le_rfl)).trans (Scheme.Hom.preimage_top g).symm
  · exact Dualizing.isRelativelyPerfect_of_iso
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct Γ(S, ⊤)).tensor
      (StacksDraft.TorAmplitude.canonicalTensorComparison Γ(S, ⊤))
      (StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived Γ(S, ⊤)) eΓ.symm hM

/-- **The algebraic relative dualizing complex, sheafified.** For a flat, locally finitely
presented morphism `g : X ⟶ S` of affine schemes and any open `W ⊆ X ×_S X` through which the
diagonal factors as a closed immersion, there is an `S`-perfect object `K` of `D(𝒪_X)` with
`R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]`: `K = K_A^~` for a relative dualizing complex `K_A` of
`Γ(S, ⊤) → Γ(X, ⊤)` (Stacks 0E2F), and the isomorphism is the proof of Stacks 0E2U run
backwards. -/
theorem exists_isPerfectRelativeTo_diagonalExactSupport_iso (D : DiagonalOpen g) :
    ∃ K : DerivedCategory X.Modules,
      IsPerfectRelativeTo g
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage S.toRingedSpace g.base)) K ∧
      Nonempty (D.diagonalExactSupport K ≅ structureSingle X) := by
  let : Algebra Γ(S, ⊤) Γ(X, ⊤) := (g.appLE ⊤ ⊤ le_top).hom.toAlgebra
  let : Module.Flat Γ(S, ⊤) Γ(X, ⊤) :=
    moduleFlat_appLE g (isAffineOpen_top S) (isAffineOpen_top X) le_top rfl
  let : Algebra.FinitePresentation Γ(S, ⊤) Γ(X, ⊤) :=
    algebraFinitePresentation_appLE g (isAffineOpen_top S) (isAffineOpen_top X) le_top rfl
  obtain ⟨KA, hKA⟩ := Dualizing.exists_isRelativeDualizingComplex_of_flat Γ(S, ⊤) Γ(X, ⊤)
  obtain ⟨eΓ⟩ := nonempty_derivedSectionsUnbounded_affineDerivedTilde_iso X KA
  have hK : Dualizing.IsRelativeDualizingComplex Γ(S, ⊤) Γ(X, ⊤)
      ((derivedSectionsUnbounded X ⊤).obj (affineDerivedTilde X KA)) :=
    Dualizing.isRelativeDualizingComplex_of_iso _ _ hKA eΓ.symm
  refine ⟨affineDerivedTilde X KA,
    isPerfectRelativeTo_affineDerivedTilde g KA hKA.relativelyPerfect, ?_⟩
  exact D.nonempty_diagonalExactSupport_iso_of_top (isAffineOpen_top X) (isAffineOpen_top S)
    le_top rfl _ (isQuasicoherent_homology_affineDerivedTilde X KA) hK

end AlgebraicGeometry.Scheme.Hom

end StandardModel

namespace CategoryTheory

/-- **An injective linear map between free modules of rank one with a linear retraction is an
isomorphism, read on morphisms.** Let `C` be `R`-linear for a commutative ring `R`, with every
endomorphism of `B` a scalar. Let `Φ : Hom(B, L) → Hom(B, M)` have a left inverse `Ψ` which is
`R`-linear, let `M ≅ B`, and let `ζ₁` generate `Hom(B, L)` freely over `End(B)` by
precomposition. Then `Φ ζ₁` is an isomorphism: writing `Φ ζ₁ = s • τ` and `Ψ τ = r • ζ₁`, the
identity `ζ₁ = Ψ (Φ ζ₁) = (s r) • ζ₁` forces `s r = 1`. -/
theorem isIso_of_leftInverse_of_generator {C : Type*} [Category C] [Preadditive C] {R : Type*}
    [CommRing R] [Linear R C] {B L M : C} (τ : B ≅ M) (Φ : (B ⟶ L) → (B ⟶ M))
    (Ψ : (B ⟶ M) → (B ⟶ L)) (hΨΦ : ∀ ζ, Ψ (Φ ζ) = ζ) (hΨ : ∀ (a : R) ψ, Ψ (a • ψ) = a • Ψ ψ)
    (hEnd : ∀ x : B ⟶ B, ∃ a : R, x = a • 𝟙 B) (ζ₁ : B ⟶ L)
    (hgen : ∀ ζ, ∃ x : B ⟶ B, ζ = x ≫ ζ₁) (huniq : ∀ x y : B ⟶ B, x ≫ ζ₁ = y ≫ ζ₁ → x = y) :
    IsIso (Φ ζ₁) := by
  obtain ⟨s, hs⟩ := hEnd (Φ ζ₁ ≫ τ.inv)
  obtain ⟨x, hx⟩ := hgen (Ψ τ.hom)
  obtain ⟨r, rfl⟩ := hEnd x
  have hΦ : Φ ζ₁ = (s • 𝟙 B) ≫ τ.hom := by
    rw [← hs, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hsr : (s * r) • 𝟙 B = 𝟙 B := by
    refine huniq _ _ ?_
    have h₁ : Ψ (Φ ζ₁) = ζ₁ := hΨΦ ζ₁
    rw [hΦ, Linear.smul_comp, Category.id_comp, hΨ, hx, Linear.smul_comp, Category.id_comp] at h₁
    rw [Category.id_comp, Linear.smul_comp, Category.id_comp, mul_smul, h₁]
  have hrs : (r * s) • 𝟙 B = 𝟙 B := by rw [mul_comm, hsr]
  have : IsIso (s • 𝟙 B) := ⟨⟨r • 𝟙 B, by
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul, hsr], by
    rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul, hrs]⟩⟩
  rw [hΦ]
  infer_instance

end CategoryTheory

end
