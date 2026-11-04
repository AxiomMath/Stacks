module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.Cartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.BaseChangeHom
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.InjectiveBaseChange
public import StacksFrontier.Algebra.Module.Injective.ChangeOfRings
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.RingHom.Etale

/-!
# Étale base change of injective modules over a Noetherian ring

Let `A` be a Noetherian ring and `A → B` an étale ring map. For an injective `A`-module `I`, the
`A`-module `B ⊗_A I` is again injective: it is an injective `B`-module (Stacks 0E4F, the
hypothesis on primes being Stacks 00U4 for an étale map), and the restriction of scalars of an
injective module along a flat map is injective (Stacks 08XQ).

Applied to the ring of an affine object of the small étale site of `Spec A`, this shows that
`𝒪(V) ⊗_A I` is a complex of injective `A`-modules for every bounded below complex `I` of
injective `A`-modules, hence K-injective.

## Main results

* `Module.Injective.tensorProduct_of_etale`.
* `AlgebraicGeometry.AffineEtaleDuality.etale_ρc`: the ring of an affine object of the small étale
  site is étale over `A`.
* `AlgebraicGeometry.AffineEtaleDuality.isKInjective_REc`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace Module.Injective

/-- **Étale base change preserves injective modules over a Noetherian ring**: for `A → B` étale
with `A` Noetherian and `I` an injective `A`-module, `B ⊗_A I` is an injective `A`-module. -/
theorem tensorProduct_of_etale {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Algebra.Etale A B] (I : Type u) [AddCommGroup I] [Module A I]
    [Module.Injective A I] : Module.Injective A (TensorProduct A B I) := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have hB : Module.Injective B (TensorProduct A B I) := by
    refine Module.tensorProduct_injective_of_flat_of_map_comap_eq (fun q hq => ?_) I
    let p := Ideal.comap (algebraMap A B) q
    have : q.LiesOver p := ⟨rfl⟩
    let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver p q
    have : Algebra.IsUnramifiedAt A q := inferInstance
    rw [Localization.AtPrime.map_eq_maximalIdeal]
    exact ((Algebra.isUnramifiedAt_iff_map_eq A p q).1 this).2
  exact Module.Injective.restrictScalars_of_flat' A hB

end Module.Injective

namespace AlgebraicGeometry.AffineEtaleDuality

variable (A : CommRingCat.{u}) (B : BigEtaleSite.{u}) (hX : B.Contains (Spec A))

/-- **The ring of an affine object of the small étale site of `Spec A` is étale over `A`.** -/
lemma etale_ρc (V : Site A B hX)
    (hV : AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B (Spec A) hX).obj V)) :
    (ρc A B hX V).Etale := by
  have h : ((SmallEtale.affineChartRings B (Spec A) hX).map
      (ObjectProperty.homMk (P := fun W => AlgebraicGeometry.IsAffine
        ((SmallEtale.toScheme B (Spec A) hX).obj W))
        (X := ⟨V, hV⟩) (Y := ⟨top A B hX, isAffine_top A B hX⟩)
        (toTop A B hX V)).op).hom.Etale := by
    rw [SmallEtale.affineChartRings_map]
    exact HasRingHomProperty.appTop (P := @Etale) _
      (SmallEtale.etale_smallAffineEtale_toScheme_map B (Spec A) hX _)
  rw [ρc_eq]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (bijective_ρtop A B hX)) h

/-- **For `V` affine and `E` an injective `A`-module, `𝒪(V) ⊗_A E` is an injective
`A`-module.** -/
lemma injective_RE [IsNoetherianRing A] (V : Site A B hX)
    (hV : AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B (Spec A) hX).obj V))
    (E : ModuleCat.{u} A) [Injective E] :
    Injective ((Stacks.FlatBaseChangeHom.RE (ρc A B hX V)).obj E) := by
  let := (ρc A B hX V).toAlgebra
  have : Algebra.Etale A ((Rc A B hX).obj (op V)) := etale_ρc A B hX V hV
  have : Module.Injective A E := Module.injective_module_of_injective_object A E
  have := Module.Injective.tensorProduct_of_etale (A := A) (B := (Rc A B hX).obj (op V)) E
  have := Module.injective_object_of_injective_module A
    (TensorProduct A ((Rc A B hX).obj (op V)) E)
  let l : TensorProduct A ((Rc A B hX).obj (op V)) E ≃ₗ[A]
      ((Stacks.FlatBaseChangeHom.RE (ρc A B hX V)).obj E) :=
    { toFun := fun x => x
      invFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Injective.of_iso l.toModuleIso inferInstance

/-- **For `V` affine and `I` a bounded below complex of injective `A`-modules, `𝒪(V) ⊗_A I` is
K-injective.** -/
lemma isKInjective_REc [IsNoetherianRing A] (V : Site A B hX)
    (hV : AlgebraicGeometry.IsAffine ((SmallEtale.toScheme B (Spec A) hX).obj V))
    (I : CochainComplex (ModuleCat.{u} A) ℤ) (a : ℤ) [I.IsStrictlyGE a]
    [∀ n, Injective (I.X n)] :
    (Stacks.FlatBaseChangeHom.REc (ρc A B hX V) I).IsKInjective := by
  have : (Stacks.FlatBaseChangeHom.REc (ρc A B hX V) I).IsStrictlyGE a := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact (Stacks.FlatBaseChangeHom.RE (ρc A B hX V)).map_isZero
      (I.isZero_of_isStrictlyGE a i hi)
  have : ∀ n, Injective ((Stacks.FlatBaseChangeHom.REc (ρc A B hX V) I).X n) := fun n =>
    injective_RE A B hX V hV (I.X n)
  exact CochainComplex.isKInjective_of_injective _ a

end AlgebraicGeometry.AffineEtaleDuality

end
