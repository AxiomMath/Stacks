module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.HenselianBase
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.PolynomialLocalizationReduction
public import StacksFrontier.RingTheory.Flat.BaseChangeAlongFlatAlgebra
public import StacksFrontier.RingTheory.Flat.DegreewiseChase
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# The injectivity criterion for a linear map to a flat module: Stacks 0AT4

Let `A → B` be a local homomorphism of local rings which is essentially of finite type, let
`u : N → M` be a `B`-linear map from a finite `B`-module to a `B`-module which is flat over `A`,
and assume `u` is injective modulo the maximal ideal of `A`. Stacks proves that `u` is
universally injective over `A`, that `N` is finitely presented over `B` and that `N` is flat
over `A` by passing to the henselization `A → A^h`: with `B'` the localization of `A^h ⊗_A B`
at the prime over the closed points of `Spec A^h` and `Spec B`, the base change
`u' : B' ⊗_B N → B' ⊗_B M` is again in this situation over the henselian base `A^h`, and the
three conclusions descend along the faithfully flat map `B → B'`.

## Main results

* `AlgebraicGeometry.universallyInjective_and_finitePresentation_and_flat_of_linearMap`: Stacks
  0AT4, from the henselian case Stacks 0AT3
  (`AlgebraicGeometry.injectiveModuloMaximalIdealConclusion_of_henselianLocalRing`).
* `AlgebraicGeometry.HenselizationReduction.conclusions_of_henselian_cases`:
  the three conclusions for `u`, given them for every instance of Situation 0AT0 over a
  henselian base.
* `AlgebraicGeometry.HenselizationReduction.flat_tensorProduct_of_flat`: for a flat algebra `B'`
  over `Ah ⊗_A B` and a `B`-module `M` flat over `A`, the base change `B' ⊗_B M` is flat over
  `Ah`.
* `AlgebraicGeometry.HenselizationReduction.injective_rTensor_baseChange_iff`: along a faithfully
  flat `S → S'`, the map `(S' ⊗_S u) ⊗_R Q` is injective exactly when `u ⊗_R Q` is.
* `AlgebraicGeometry.HenselizationReduction.injective_rTensor_tensorProduct_iff`: for an
  `S`-linear `f` and an `R`-module `Q`, `f ⊗_S (S ⊗_R Q)` is injective exactly when `f ⊗_R Q`
  is.
* `AlgebraicGeometry.HenselizationReduction.injective_mapQ_map_smul_top_iff`: injectivity modulo
  an ideal `I` of `R` and modulo its extension `IS` are the same condition.

## Implementation notes

The henselization is the one of Stacks 04GN (`IsLocalRing.exists_henselization`), which lives in
the universe of `A`; it is flat over `A` as a filtered colimit of étale algebras. The prime of
`A^h ⊗_A B` is the kernel of the map to the residue field of `B` given by
`A^h → κ(A^h) = κ(A) → κ(B)` and `B → κ(B)`; it lies over both maximal ideals, so `A^h → B'` and
`B → B'` are local. The right `B`-algebra structure on `A^h ⊗_A B` is enabled locally, as
`Mathlib` does not make it an instance.

The source's descent along `B → B'` cites Stacks 03C4 for finite presentation and Stacks 0584
for flatness; these are `Module.FinitePresentation.of_isBaseChange_of_faithfullyFlat` and
`Module.Flat.tensorProduct_iff_of_faithfullyFlat`. Universal injectivity over `A` descends by
`injective_rTensor_baseChange_iff`, after `injective_rTensor_tensorProduct_iff` has turned
universal injectivity over `A^h` into injectivity of `u' ⊗_A Q` for every `A`-module `Q`.

## References

* [Stacks Project, Tag 0AT4](https://stacks.math.columbia.edu/tag/0AT4)
* [Stacks Project, Tag 04GN](https://stacks.math.columbia.edu/tag/04GN)
-/

@[expose] public section

open TensorProduct IsLocalRing

universe u₁ u₂ u₃ u₄ w

namespace AlgebraicGeometry

namespace HenselizationReduction

section CancelBaseChange

variable {R S X Y : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]
  [AddCommGroup Y] [Module R Y] [Module S Y] [IsScalarTower R S Y]

/-- For an `S`-linear map `f : X → Y` between `S`-modules and an `R`-module `Q`, the map
`f ⊗_S (S ⊗_R Q)` is `f ⊗_R Q` under `X ⊗_S (S ⊗_R Q) = X ⊗_R Q`, so one is injective exactly
when the other is. -/
theorem injective_rTensor_tensorProduct_iff (f : X →ₗ[S] Y) (Q : Type*) [AddCommGroup Q]
    [Module R Q] :
    Function.Injective (f.rTensor (S ⊗[R] Q)) ↔
      Function.Injective ((f.restrictScalars R).rTensor Q) := by
  have key : ⇑(AlgebraTensorModule.cancelBaseChange R S S Y Q) ∘ ⇑(f.rTensor (S ⊗[R] Q)) =
      ⇑((f.restrictScalars R).rTensor Q) ∘ ⇑(AlgebraTensorModule.cancelBaseChange R S S X Q) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
      simp only [Function.comp_apply, map_add] at ha hb ⊢
      rw [ha, hb]
    | tmul x w =>
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb =>
        simp only [Function.comp_apply, tmul_add, map_add] at ha hb ⊢
        rw [ha, hb]
      | tmul s q => simp
  rw [← EquivLike.comp_injective _ (AlgebraTensorModule.cancelBaseChange R S S Y Q), key,
    EquivLike.injective_comp]

end CancelBaseChange

section FaithfullyFlatBaseChange

variable {R S S' N M : Type*} [CommRing R] [CommRing S] [CommRing S']
  [Algebra R S] [Algebra R S'] [Algebra S S'] [IsScalarTower R S S']
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- For an `S`-linear map `u : N → M`, an `R`-module `Q` and a faithfully flat `S`-algebra `S'`,
the map `(S' ⊗_S u) ⊗_R Q` is injective exactly when `u ⊗_R Q` is: under
`(S' ⊗_S N) ⊗_R Q = S' ⊗_S (N ⊗_R Q)` the former is `S' ⊗_S (u ⊗_R Q)`. -/
theorem injective_rTensor_baseChange_iff [Module.FaithfullyFlat S S'] (u : N →ₗ[S] M)
    (Q : Type*) [AddCommGroup Q] [Module R Q] :
    Function.Injective (((u.baseChange S').restrictScalars R).rTensor Q) ↔
      Function.Injective ((u.restrictScalars R).rTensor Q) := by
  have key : ⇑(AlgebraTensorModule.assoc R S S' S' M Q) ∘
        ⇑(((u.baseChange S').restrictScalars R).rTensor Q) =
      ⇑((AlgebraTensorModule.rTensor R Q u).lTensor S') ∘
        ⇑(AlgebraTensorModule.assoc R S S' S' N Q) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb =>
      simp only [Function.comp_apply, map_add] at ha hb ⊢
      rw [ha, hb]
    | tmul x q =>
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb =>
        simp only [Function.comp_apply, add_tmul, map_add] at ha hb ⊢
        rw [ha, hb]
      | tmul s n => simp
  have hfun : ⇑(AlgebraTensorModule.rTensor R Q u) = ⇑((u.restrictScalars R).rTensor Q) := by
    funext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul n q => simp
  rw [← EquivLike.comp_injective _ (AlgebraTensorModule.assoc R S S' S' M Q), key,
    EquivLike.injective_comp, Module.FaithfullyFlat.lTensor_injective_iff_injective, hfun]

end FaithfullyFlatBaseChange

section PushoutFlat

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A Ah B B' M : Type*} [CommRing A] [CommRing Ah] [CommRing B] [CommRing B']
  [Algebra A Ah] [Algebra A B] [Algebra (Ah ⊗[A] B) B'] [Algebra Ah B'] [Algebra B B']
  [IsScalarTower Ah (Ah ⊗[A] B) B'] [IsScalarTower B (Ah ⊗[A] B) B']
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- Let `A → Ah` and `A → B` be ring maps and let `B'` be a flat algebra over `Ah ⊗_A B`. For a
`B`-module `M` that is flat over `A`, the base change `B' ⊗_B M` is flat over `Ah`: it is
`B' ⊗_{Ah ⊗_A B} (Ah ⊗_A M)`. -/
theorem flat_tensorProduct_of_flat [Module.Flat (Ah ⊗[A] B) B'] [Module.Flat A M] :
    Module.Flat Ah (B' ⊗[B] M) := by
  have : Module.Flat Ah ((Ah ⊗[A] B) ⊗[B] M) :=
    Module.Flat.of_linearEquiv (Algebra.IsPushout.cancelBaseChange A Ah B (Ah ⊗[A] B) M)
  have : Module.Flat Ah (B' ⊗[Ah ⊗[A] B] ((Ah ⊗[A] B) ⊗[B] M)) :=
    Module.Flat.tensorProduct_of_flat
  exact Module.Flat.of_linearEquiv
    ((AlgebraTensorModule.cancelBaseChange B (Ah ⊗[A] B) B' B' M).symm.restrictScalars Ah)

end PushoutFlat

section ExtendedIdeal

variable {R S X Y : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup X] [Module R X] [Module S X] [IsScalarTower R S X]
  [AddCommGroup Y] [Module R Y] [Module S Y] [IsScalarTower R S Y]

/-- For an `S`-linear map `f : X → Y` and an ideal `I ⊆ R`, the map `X/(IS)X → Y/(IS)Y` is
injective exactly when `X/IX → Y/IY` is: the submodules `(IS)X` and `IX` have the same
elements. -/
theorem injective_mapQ_map_smul_top_iff (f : X →ₗ[S] Y) (I : Ideal R) :
    Function.Injective (Submodule.mapQ (I.map (algebraMap R S) • (⊤ : Submodule S X))
      (I.map (algebraMap R S) • (⊤ : Submodule S Y)) f
      (Submodule.smul_top_le_comap_smul_top _ f)) ↔
    Function.Injective (Submodule.mapQ (I • (⊤ : Submodule R X)) (I • (⊤ : Submodule R Y))
      (f.restrictScalars R) (Submodule.smul_top_le_comap_smul_top I _)) := by
  rw [Stacks.UniversalInjectivity.FGIdealTest.injective_mapQ_iff,
    Stacks.UniversalInjectivity.FGIdealTest.injective_mapQ_iff]
  constructor
  · intro h x hx
    rw [Submodule.mem_comap, LinearMap.restrictScalars_apply,
      ← Module.Flat.mem_map_smul_top_iff (S := S)] at hx
    exact (Module.Flat.mem_map_smul_top_iff (S := S) I x).1 (h hx)
  · intro h x hx
    rw [Submodule.mem_comap, Module.Flat.mem_map_smul_top_iff (R := R)] at hx
    exact (Module.Flat.mem_map_smul_top_iff (S := S) I x).2 (h hx)

end ExtendedIdeal

section Reduction

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- If `R → T → T'` is a tower with `T'` local, and the maximal ideal of `T'` contracts to a prime
of `T` that contracts to the maximal ideal of `R`, then `R → T'` is a local homomorphism. -/
private theorem isLocalHom_of_comap_eq {R T' : Type*} (T : Type*) [CommRing R] [IsLocalRing R]
    [CommRing T] [CommRing T'] [Algebra R T] [Algebra R T'] [Algebra T T'] [IsScalarTower R T T']
    [IsLocalRing T'] {q : Ideal T} (hq' : (maximalIdeal T').comap (algebraMap T T') = q)
    (hq : q.comap (algebraMap R T) = maximalIdeal R) : IsLocalHom (algebraMap R T') := by
  refine ((local_hom_TFAE (algebraMap R T')).out 5 1).mp ?_
  rw [IsScalarTower.algebraMap_eq R T T', ← Ideal.comap_comap, hq', hq]

/-- **The reduction of Stacks 0AT4 to the henselian case.** Let `A → B` be a local homomorphism
of local rings which is essentially of finite type, `N` a finite `B`-module, `M` a `B`-module
which is flat over `A`, and `u : N → M` a `B`-linear map which is injective modulo the maximal
ideal of `A`. If the three conclusions of "the lemma" hold in every instance of Situation 0AT0
over a henselian base, then `u` is universally injective over `A`, `N` is finitely presented
over `B`, and `N` is flat over `A`.

The instance used is the base change of `u` to the localization `B'` of `A^h ⊗_A B` at the prime
lying over the closed points, with `A^h` the henselization of `A`. -/
theorem conclusions_of_henselian_cases
    {A : Type u₁} {B : Type u₂} {M : Type u₃} {N : Type u₄}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] [Module.Flat A M]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] [Module.Finite B N]
    (u : N →ₗ[B] M)
    (hu : Function.Injective (Submodule.mapQ (maximalIdeal A • (⊤ : Submodule A N))
      (maximalIdeal A • (⊤ : Submodule A M)) (u.restrictScalars A)
      (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (u.restrictScalars A))))
    (h : ∀ T : InjectiveModuloMaximalIdealSituation.{u₁, max u₁ u₂, max u₁ u₂ u₃, max u₁ u₂ u₄},
      HenselianLocalRing T.A → InjectiveModuloMaximalIdealConclusion.{max u₁ w} T) :
    UniversallyInjectivePoly.{_, w} (u.restrictScalars A) ∧ Module.FinitePresentation B N ∧
      Module.Flat A N := by
  classical
  obtain ⟨Ah, _, _, _, _, hhens, hind, hmax, hres⟩ := IsLocalRing.exists_henselization A
  have : Module.Flat A Ah := CommAlgCat.flat_of_ind_etale hind
  let T := Ah ⊗[A] B
  -- the point of `Spec T` over the closed points of `Spec Ah` and `Spec B`
  let e : ResidueField A ≃+* ResidueField Ah := RingEquiv.ofBijective _ hres
  let ψ : Ah →ₐ[A] ResidueField B :=
    { toRingHom := (ResidueField.map (algebraMap A B)).comp (e.symm.toRingHom.comp (residue Ah))
      commutes' := fun a => by
        have ha : residue Ah (algebraMap A Ah a) = e (residue A a) :=
          (ResidueField.map_residue (algebraMap A Ah) a).symm
        show (ResidueField.map (algebraMap A B)) (e.symm (residue Ah (algebraMap A Ah a))) = _
        rw [ha, RingEquiv.symm_apply_apply, ResidueField.map_residue,
          IsScalarTower.algebraMap_apply A B (ResidueField B)]
        rfl }
  let χ : B →ₐ[A] ResidueField B := IsScalarTower.toAlgHom A B (ResidueField B)
  let φ : T →ₐ[A] ResidueField B := Algebra.TensorProduct.lift ψ χ (fun _ _ => Commute.all _ _)
  have hφ : ∀ a b, φ (a ⊗ₜ b) = ψ a * χ b := fun a b => Algebra.TensorProduct.lift_tmul _ _ _ a b
  let q : Ideal T := RingHom.ker φ
  have : q.IsPrime := RingHom.ker_isPrime φ
  let B' := Localization.AtPrime q
  have hqB : q.comap (algebraMap B T) = maximalIdeal B := by
    ext b
    show φ (1 ⊗ₜ b) = 0 ↔ _
    rw [hφ, map_one, one_mul, ← residue_eq_zero_iff]
    rfl
  have hqAh : q.comap (algebraMap Ah T) = maximalIdeal Ah := by
    ext a
    show φ (a ⊗ₜ 1) = 0 ↔ _
    rw [hφ, map_one, mul_one, ← residue_eq_zero_iff]
    show (ResidueField.map (algebraMap A B)) (e.symm (residue Ah a)) = 0 ↔ _
    rw [map_eq_zero_iff _ (ResidueField.map (algebraMap A B)).injective,
      map_eq_zero_iff _ e.symm.injective]
  have hB' : (maximalIdeal B').comap (algebraMap T B') = q :=
    Localization.AtPrime.under_maximalIdeal
  have : IsLocalHom (algebraMap B B') := isLocalHom_of_comap_eq T hB' hqB
  have : IsLocalHom (algebraMap Ah B') := isLocalHom_of_comap_eq T hB' hqAh
  have : Module.Flat B T := Module.Flat.isBaseChange (R := A) (S := B) (M := Ah) T
    (Algebra.IsPushout.out : IsBaseChange B (IsScalarTower.toAlgHom A Ah T).toLinearMap)
  have : Module.Flat B B' := Module.Flat.trans B T B'
  have : Module.FaithfullyFlat B B' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq A T B', IsScalarTower.algebraMap_eq B T B',
      RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq A B T])
  have : Algebra.EssFiniteType Ah B' := inferInstance
  let N' := B' ⊗[B] N
  let M' := B' ⊗[B] M
  have hM' : Module.Flat Ah M' := flat_tensorProduct_of_flat (A := A) (B := B)
  let u' : N' →ₗ[B'] M' := u.baseChange B'
  have hu' : Function.Injective (Submodule.mapQ (maximalIdeal Ah • (⊤ : Submodule Ah N'))
      (maximalIdeal Ah • (⊤ : Submodule Ah M')) (u'.restrictScalars Ah)
      (Submodule.smul_top_le_comap_smul_top (maximalIdeal Ah) (u'.restrictScalars Ah))) := by
    have h := (injective_mapQ_map_smul_top_iff (u'.restrictScalars Ah) (maximalIdeal A)).2
      ((StacksDraft.DegreewiseChase.injective_mapQ_iff_injective_rTensor_quotient
        ((u'.restrictScalars Ah).restrictScalars A) (maximalIdeal A)).2
        ((injective_rTensor_baseChange_iff (S' := B') u (A ⧸ maximalIdeal A)).2
          ((StacksDraft.DegreewiseChase.injective_mapQ_iff_injective_rTensor_quotient
            (u.restrictScalars A) (maximalIdeal A)).1 hu)))
    rwa [hmax] at h
  obtain ⟨hUI, hFP, hF⟩ := h
    { A := Ah, B := B', M := M', N := N', u := u'.restrictScalars Ah, flatM := hM'
      injective_mod_maximalIdeal := hu' } hhens
  refine ⟨fun Q _ _ => ?_, ?_, ?_⟩
  · have h₁ : Function.Injective ((u'.restrictScalars Ah).rTensor (Ah ⊗[A] Q)) := hUI _
    have h₂ := (injective_rTensor_tensorProduct_iff (u'.restrictScalars Ah) Q).1 h₁
    exact (injective_rTensor_baseChange_iff (S' := B') u Q).1 h₂
  · have : Module.FinitePresentation B' N' := hFP
    exact Module.FinitePresentation.of_isBaseChange_of_faithfullyFlat (S := B')
      (TensorProduct.mk B B' N 1) (TensorProduct.isBaseChange B N B')
  · have : Module.Flat Ah N' := hF
    have : Module.Flat A N' := Module.Flat.trans A Ah N'
    exact (Module.Flat.tensorProduct_iff_of_faithfullyFlat (R := A) (S := B) (S' := B')).1 this

end Reduction

end HenselizationReduction

/-- **Stacks Project, Tag 0AT4.** Let `A → B` be a local homomorphism of local rings which is
essentially of finite type and let `u : N → M` be a `B`-linear map. If `N` is a finite
`B`-module, `M` is flat over `A`, and the induced map `N/𝔪_A N → M/𝔪_A M` is injective, then
`u` is universally injective over `A`, `N` is finitely presented over `B`, and `N` is flat over
`A`.

This is `HenselizationReduction.conclusions_of_henselian_cases` applied to the henselian case
Stacks 0AT3, `injectiveModuloMaximalIdealConclusion_of_henselianLocalRing`. -/
@[stacks 0AT4 "`N/𝔪_A N → M/𝔪_A M` is the `Submodule.mapQ` of `u` for `𝔪_A • ⊤`, and
`A`-universal injectivity is `UniversallyInjectivePoly` of `u` with scalars restricted to `A`."]
theorem universallyInjective_and_finitePresentation_and_flat_of_linearMap
    {A : Type u₁} {B : Type u₂} {M : Type u₃} {N : Type u₄}
    [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Algebra.EssFiniteType A B]
    [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] [Module.Flat A M]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] [Module.Finite B N]
    (u : N →ₗ[B] M)
    (hu : Function.Injective (Submodule.mapQ (maximalIdeal A • (⊤ : Submodule A N))
      (maximalIdeal A • (⊤ : Submodule A M)) (u.restrictScalars A)
      (Submodule.smul_top_le_comap_smul_top (maximalIdeal A) (u.restrictScalars A)))) :
    UniversallyInjectivePoly.{_, w} (u.restrictScalars A) ∧ Module.FinitePresentation B N ∧
      Module.Flat A N :=
  HenselizationReduction.conclusions_of_henselian_cases u hu fun T _ =>
    injectiveModuloMaximalIdealConclusion_of_henselianLocalRing T

end AlgebraicGeometry
