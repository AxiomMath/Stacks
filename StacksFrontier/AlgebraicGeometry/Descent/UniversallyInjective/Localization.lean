module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.UniversallyInjective.Defs

/-!
# Universal injectivity of a localization cover

If elements of a commutative ring generate the unit ideal, the canonical map from the ring to
the product of its localizations at those elements is universally injective.

## Main definitions

There are no new definitions.

## Main results

* `Algebra.UniversallyInjective.pi_localizationAway` states universal injectivity of the
  canonical map to the localizations of a unit-ideal cover.

## Implementation notes

The finite direct sum of rings in the source is represented by their finite product; the
statement also holds for arbitrary families whose elements generate the unit ideal. The
`Algebra` structure on this product gives the canonical map componentwise. The index type
shares the ring's universe because `Algebra.UniversallyInjective` is defined for algebras
whose source and target lie in the same universe.

## References

* [Stacks Project, Tag 08WN](https://stacks.math.columbia.edu/tag/08WN)
-/

@[expose] public section

universe u

private lemma localizedTensorMk_injective {R : Type u} [CommRing R]
    (r : R) (A : Type u) [CommRing A] [Algebra R A]
    [IsLocalization.Away r A] (Q : Type u) [AddCommGroup Q] [Module R Q] :
    Function.Injective
      (LocalizedModule.map (Submonoid.powers r)
        (TensorProduct.mk R A Q (1 : A))) := by
  let m : Q →ₗ[R] TensorProduct R A Q := TensorProduct.mk R A Q (1 : A)
  let e : TensorProduct R A (TensorProduct R A Q) ≃ₗ[A]
      TensorProduct R A Q := IsLocalization.moduleLid (Submonoid.powers r) A
        (TensorProduct R A Q)
  let eR := e.restrictScalars R
  have he : eR ∘ₗ TensorProduct.mk R A (TensorProduct R A Q) (1 : A) =
      LinearMap.id := by
    ext x
    simp [eR, e, IsLocalization.moduleLid, TensorProduct.equivOfCompatibleSMul]
  have : IsLocalizedModule (Submonoid.powers r)
      (LinearMap.id : TensorProduct R A Q →ₗ[R] TensorProduct R A Q) := he ▸ inferInstance
  have hmap : IsLocalizedModule.map (Submonoid.powers r) m
      (LinearMap.id : TensorProduct R A Q →ₗ[R] TensorProduct R A Q) m =
      LinearMap.id := by
    apply IsLocalizedModule.ext (S := Submonoid.powers r) (f := m)
      (fun x => IsLocalizedModule.map_units (S := Submonoid.powers r)
        (f := (LinearMap.id : TensorProduct R A Q →ₗ[R] TensorProduct R A Q)) x)
    rw [IsLocalizedModule.map_comp]
  rw [← IsLocalizedModule.map_injective_iff_localizedModuleMap_injective
    (S := Submonoid.powers r) (g₁ := m)
    (g₂ := (LinearMap.id : TensorProduct R A Q →ₗ[R] TensorProduct R A Q)), hmap]
  exact fun _ _ h => h

private lemma localizedTensorMkPi_injective {R : Type u} [CommRing R]
    {ι : Type u} (f : ι → R) (i : ι) (Q : Type u)
    [AddCommGroup Q] [Module R Q] :
    Function.Injective
      (LocalizedModule.map (Submonoid.powers (f i))
        (TensorProduct.mk R (∀ j, Localization.Away (f j)) Q
          (1 : ∀ j, Localization.Away (f j)))) := by
  let S := ∀ j, Localization.Away (f j)
  let π : S →ₗ[R] Localization.Away (f i) :=
    { toFun := fun x => x i
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let p := TensorProduct.map π (LinearMap.id : Q →ₗ[R] Q)
  have hcomp : p.comp (TensorProduct.mk R S Q (1 : S)) =
      TensorProduct.mk R (Localization.Away (f i)) Q 1 := by
    ext q
    rfl
  have hlocal := localizedTensorMk_injective (R := R) (r := f i)
    (A := Localization.Away (f i)) Q
  have hlocalcomp :
      LocalizedModule.map (Submonoid.powers (f i))
        (TensorProduct.mk R (Localization.Away (f i)) Q (1 : Localization.Away (f i))) =
      LocalizedModule.map (Submonoid.powers (f i)) p ∘ₗ
        LocalizedModule.map (Submonoid.powers (f i))
          (TensorProduct.mk R S Q (1 : S)) := by
    ext x
    induction x using LocalizedModule.induction_on with
    | _ x s =>
      simp only [LinearMap.comp_apply, LocalizedModule.map_mk]
      apply congrArg (fun z => LocalizedModule.mk z s)
      simpa [LinearMap.comp_apply] using (LinearMap.congr_fun hcomp x).symm
  rw [hlocalcomp] at hlocal
  exact fun x y h => hlocal (congrArg (LocalizedModule.map (Submonoid.powers (f i)) p) h)

/-- A family of principal localizations covering `Spec R` yields a universally injective
canonical map from `R` to their product. -/
@[stacks 08WN]
theorem Algebra.UniversallyInjective.pi_localizationAway
    {R : Type u} [CommRing R] {ι : Type u} (f : ι → R)
    (hspan : Ideal.span (Set.range f) = ⊤) :
    Algebra.UniversallyInjective R (∀ i : ι, Localization.Away (f i)) := by
  intro Q _ _
  let S := ∀ i : ι, Localization.Away (f i)
  let m : Q →ₗ[R] TensorProduct R S Q := TensorProduct.mk R S Q 1
  have hm : Function.Injective m := by
    refine injective_of_localized_span (s := Set.range f) hspan m ?_
    rintro ⟨_, i, rfl⟩
    exact localizedTensorMkPi_injective f i Q
  have hrtensor : (Algebra.linearMap R S).rTensor Q = m ∘ₗ _root_.TensorProduct.lid R Q := by
    refine LinearMap.ext fun z => ?_
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp [hx, hy]
    | tmul a q =>
      change algebraMap R S a ⊗ₜ[R] q = (1 : S) ⊗ₜ[R] (a • q)
      rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hm' : Function.Injective ((Algebra.linearMap R S).rTensor Q) := by
    rw [hrtensor]
    exact hm.comp (_root_.TensorProduct.lid R Q).injective
  exact hm'
