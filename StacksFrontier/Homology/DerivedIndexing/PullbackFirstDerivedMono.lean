module

public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Injectivity of `R¹F` along a pullback of a map with `R¹F`-acyclic source

Let `F : 𝒜 ⥤ ℬ` be a left exact additive functor between abelian categories, `𝒜` having enough
injectives. Consider a pullback square

```
M ──ι──▶ M'
│P       │P'
▼        ▼
N ──κ──▶ N'
```

in `𝒜` with `ι` a monomorphism. If `R¹F(N) = 0` and `F(κ)` is an epimorphism, then
`R¹F(ι) : R¹F(M) ⟶ R¹F(M')` is a monomorphism.

The proof is the long exact sequence: the map `coker ι ⟶ coker κ` induced by a pullback square is a
monomorphism (`CategoryTheory.Abelian.mono_cokernel_map_of_isPullback`), the exact sequence
`F(N) ⟶ F(N') ⟶ F(coker κ) ⟶ R¹F(N) = 0` shows `F(coker κ) = 0`, hence `F(coker ι) = 0`, so the
connecting map `F(coker ι) ⟶ R¹F(M)` vanishes and `R¹F(M) ⟶ R¹F(M')` is injective.

In sheaf theory this is the mechanism by which `H¹(X, ℳ) ⟶ H¹(X, j_* j^* ℳ)` is shown to be
injective for an open `j : U ⟶ X`, from an (additive, not necessarily linear) map `ℳ ⟶ 𝒩` into a
sheaf with `H¹(X, 𝒩) = 0` and `Γ(X, 𝒩) = Γ(U, 𝒩)`, as in the Frobenius argument for
[Stacks, Tag 0B4U].

## Main results

* `Stacks.DerivedIndexing.mono_rightDerived_one_map_of_isPullback`: the statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u v' u'

namespace Stacks.DerivedIndexing

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] [Abelian C] [Abelian D]
  [EnoughInjectives C] (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- The sequence `X ⟶ Y ⟶ cokernel f` is short exact when `f` is a monomorphism. -/
private theorem shortExact_cokernel_sequence {E : Type*} [Category E] [Abelian E]
    {X Y : E} (f : X ⟶ Y) [Mono f] :
    (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
  { exact := ShortComplex.exact_cokernel f }

/-- **`R¹F` is injective along the top edge of a pullback square whose bottom edge has
`R¹F`-acyclic source and `F`-surjective image.** For a pullback square `ι ≫ P' = P ≫ κ` of
monomorphisms `ι` and `κ`, with `R¹F(N) = 0` and `F(κ)` epi, the map `R¹F(ι)` is a
monomorphism. -/
theorem mono_rightDerived_one_map_of_isPullback {M M' N N' : C} {ι : M ⟶ M'} {P : M ⟶ N}
    {P' : M' ⟶ N'} {κ : N ⟶ N'} (sq : IsPullback ι P P' κ) [Mono ι] [Mono κ]
    (hN : IsZero ((F.rightDerived 1).obj N)) (hκ : Epi (F.map κ)) :
    Mono ((F.rightDerived 1).map ι) := by
  let Δ := rightDerivedDeltaFunctorOfEnoughInjectives F
  have : (F.rightDerived 0).Additive := Δ.additive 0
  let m : cokernel ι ⟶ cokernel κ := cokernel.map ι κ P P' sq.w
  have : Mono m := Abelian.mono_cokernel_map_of_isPullback sq
  have : Epi ((F.rightDerived 0).map (cokernel.π κ)) :=
    (Δ.exact_δ₁ (shortExact_cokernel_sequence κ) 0).epi_f (hN.eq_of_tgt _ _)
  have : Epi ((F.rightDerived 0).map κ) := by
    rw [show (F.rightDerived 0).map κ = inv (F.toRightDerivedZero.app N) ≫ F.map κ ≫
        F.toRightDerivedZero.app N' by
      rw [F.toRightDerivedZero.naturality κ, IsIso.inv_hom_id_assoc]]
    infer_instance
  have h₃ : (F.rightDerived 0).map (cokernel.π κ) = 0 := by
    rw [← cancel_epi ((F.rightDerived 0).map κ), ← Functor.map_comp, cokernel.condition,
      Functor.map_zero, comp_zero]
  have : Mono ((F.rightDerived 0).map m) := Δ.mono_map_f (shortExact_cokernel_sequence m)
  have hQ : IsZero ((F.rightDerived 0).obj (cokernel ι)) :=
    IsZero.of_mono ((F.rightDerived 0).map m) (IsZero.of_epi_eq_zero _ h₃)
  exact (Δ.exact_δ₂ (shortExact_cokernel_sequence ι) 0).mono_g (hQ.eq_of_src _ _)

end Stacks.DerivedIndexing

end
