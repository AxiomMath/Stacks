module

public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import StacksFrontier.RingTheory.AdicCompletion.Flat
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing
public import StacksFrontier.RingTheory.Flat.ProjectiveOfFlatOverComplete
public import StacksFrontier.RingTheory.Flat.ProjectiveOfIntegralFibresQuotient

/-!
# The completed step of Stacks 05FS

The proof of Stacks 05FS descends projectivity of a flat finite type algebra `C` over a reduced
Noetherian ring `A` along the faithfully flat ring map `A → A_f × A^∧`, where `A^∧` is the
`f`-adic completion of `A`. This file carries out the `A^∧` half: the base change
`A^∧ ⊗_A C` is projective over `A^∧`, by the criterion of Stacks 05DP.

Of the six hypotheses of Stacks 05DP, four are immediate for `A^∧` and `A^∧ ⊗_A C` — `A^∧` is
Noetherian (Stacks 0316) and `IA^∧`-adically complete (Stacks 05GG), and finite type and
flatness are stable under base change. The remaining two are the content of this file:
hypothesis 5, that `(A^∧ ⊗_A C)/I(A^∧ ⊗_A C)` is projective over `A^∧/IA^∧`, which is supplied
by the Noetherian induction because `A^∧/IA^∧` is a quotient of `A` by a nonzero ideal, and
hypothesis 6, which is
`AlgebraicGeometry.GeometricallyIntegral.map_sup_ne_top` applied to `IA^∧`, legitimate because
`IA^∧` lies in the Jacobson radical of the `IA^∧`-adically complete ring `A^∧`.

## Main results

* `AdicCompletion.surjective_algebraMap_quotient_map`: `A → A^∧/IA^∧` is surjective, so that
  `A^∧/IA^∧` is one of the quotients of `A` that the Noetherian induction knows about.
* `AdicCompletion.le_ker_algebraMap_quotient_map`: `I` is contained in the kernel of
  `A → A^∧/IA^∧`, so that kernel is nonzero as soon as `I` is.
* `AdicCompletion.smul_top_ne_top_of_le`: `𝔪A^∧ ≠ A^∧` for a proper ideal `𝔪` containing `I`.
  This is the `f ∈ 𝔪` branch of the faithful flatness of `A → A_f × A^∧`.
* `Module.Projective.tensorProduct_adicCompletion`: the conclusion, `A^∧ ⊗_A C` is projective
  over `A^∧`.

## Implementation notes

The induction hypothesis is taken in the shape "for every ring `D` which is a quotient of `A`
by a nonzero ideal, `D ⊗_A C` is projective over `D`", quantified over the *type* `D` rather
than stated for `A ⧸ 𝔞`. That is what lets it be applied to `A^∧/IA^∧` directly, with no
transport of projectivity along a ring isomorphism `A^∧/IA^∧ ≅ A/I`: the two sides of
hypothesis 5 then differ only by an `A^∧/IA^∧`-linear isomorphism of modules, namely
`TensorProduct.quotTensorEquivQuotSMulBase` composed with
`TensorProduct.AlgebraTensorModule.cancelBaseChange`.

The identification `A^∧/IA^∧ ≅ A/I` is still what makes `A → A^∧/IA^∧` surjective, and it is
used in that form only: `AdicCompletion.evalOneₐ` is a surjection onto `A/I` whose kernel is
`IA^∧` (`AdicCompletion.ker_evalOneₐ_eq_map`, which needs `I` finitely generated) and which
composes with `A → A^∧` to the quotient map.

## References

* [Stacks Project, Tag 05FS](https://stacks.math.columbia.edu/tag/05FS)
* [Stacks Project, Tag 05DP](https://stacks.math.columbia.edu/tag/05DP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

open scoped TensorProduct

universe u

namespace AdicCompletion

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- The structure map `A → A^∧/IA^∧` of the reduction of the `I`-adic completion is surjective.

Indeed `AdicCompletion.evalOneₐ` identifies `A^∧/IA^∧` with `A/I`, compatibly with the maps
out of `A`: it is a surjection `A^∧ → A/I` whose kernel is `IA^∧` and whose composite with
`A → A^∧` is the quotient map `A → A/I`. -/
theorem surjective_algebraMap_quotient_map (hI : I.FG) :
    Function.Surjective
      (algebraMap A (AdicCompletion I A ⧸ I.map (algebraMap A (AdicCompletion I A)))) := by
  intro d
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective d
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalOneₐ I x)
  refine ⟨a, ?_⟩
  rw [IsScalarTower.algebraMap_apply A (AdicCompletion I A) _]
  refine (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr ?_
  rw [← ker_evalOneₐ_eq_map I hI, RingHom.mem_ker, map_sub, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, show evalOneₐ I (algebraMap A (AdicCompletion I A) a)
      = Ideal.Quotient.mk I a from rfl, ha, sub_self]

/-- The ideal `I` is contained in the kernel of `A → A^∧/IA^∧`, since the image of `I` in `A^∧`
generates the ideal that is divided out. -/
theorem le_ker_algebraMap_quotient_map :
    I ≤ RingHom.ker
      (algebraMap A (AdicCompletion I A ⧸ I.map (algebraMap A (AdicCompletion I A)))) := by
  intro a ha
  rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply A (AdicCompletion I A) _,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_map_of_mem _ ha

/-- For a proper ideal `𝔪` of `A` containing `I`, the ideal `𝔪A^∧` of the `I`-adic completion is
proper. Indeed `A^∧` surjects onto `A/I` by `AdicCompletion.evalOneₐ`, which carries `𝔪A^∧` into
the image of `𝔪`, and `𝔪 + I = 𝔪 ≠ A`.

This is the branch of the faithful flatness of `A → A_f × A^∧` in Stacks 05FS that the
completion factor is responsible for, namely the maximal ideals containing `f`. -/
theorem smul_top_ne_top_of_le {m : Ideal A} (hm : m ≠ ⊤) (hIm : I ≤ m) :
    m • (⊤ : Submodule A (AdicCompletion I A)) ≠ ⊤ := by
  intro hc
  have hmap : m • (⊤ : Submodule A (A ⧸ I)) = ⊤ := by
    have := congrArg (Submodule.map (evalOneₐ I).toLinearMap) hc
    rwa [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr
      (evalOneₐ_surjective I)] at this
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_eq_top_iff,
    Ideal.Quotient.algebraMap_eq] at hmap
  refine hm (top_unique ?_)
  have hcm := Ideal.comap_map_of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective m
  rw [Ideal.mk_ker, sup_eq_left.mpr hIm] at hcm
  rw [← hcm, hmap]
  exact le_top

end AdicCompletion

/-- **The completed step of Stacks 05FS.** Let `A` be a Noetherian ring, `C` a flat finite type
`A`-algebra whose fibres are geometrically integral, and `I` a nonzero ideal of `A`. If
`D ⊗_A C` is projective over `D` for every ring `D` which is a quotient of `A` by a nonzero
ideal, then `A^∧ ⊗_A C` is projective over the `I`-adic completion `A^∧` of `A`.

This is the criterion of Stacks 05DP,
`projective_of_flat_of_projective_quotient_of_associatedPrimes`, applied to the ideal `IA^∧` of
`A^∧`. The ring `A^∧` is Noetherian and `IA^∧`-adically complete, and `A^∧ ⊗_A C` is of finite
type and flat over it as a base change; the reduction
`(A^∧ ⊗_A C)/I(A^∧ ⊗_A C) = (A^∧/IA^∧) ⊗_A C` is projective over `A^∧/IA^∧` by hypothesis,
because `A^∧/IA^∧` is a quotient of `A` by an ideal containing `I`; and the associated-prime
condition is `AlgebraicGeometry.GeometricallyIntegral.map_sup_ne_top`, applicable because
`IA^∧` lies in the Jacobson radical of the `IA^∧`-adically complete `A^∧`. -/
theorem Module.Projective.tensorProduct_adicCompletion (A C : Type u) [CommRing A] [CommRing C]
    [Algebra A C] [IsNoetherianRing A] [Algebra.FiniteType A C] [Module.Flat A C]
    (h : GeometricallyIntegral (Spec.map (ofHom (algebraMap A C)))) (I : Ideal A) (hI : I ≠ ⊥)
    (hquot : ∀ (D : Type u) [CommRing D] [Algebra A D],
      Function.Surjective (algebraMap A D) → RingHom.ker (algebraMap A D) ≠ ⊥ →
      Module.Projective D (D ⊗[A] C)) :
    Module.Projective (AdicCompletion I A) (AdicCompletion I A ⊗[A] C) := by
  have hIfg : I.FG := I.fg_of_isNoetherianRing
  set Ac := AdicCompletion I A with hAc
  set J := I.map (algebraMap A Ac) with hJ
  have : IsAdicComplete J Ac := AdicCompletion.isAdicComplete_self I hIfg
  -- Hypothesis 5 of Stacks 05DP: the reduction of `Ac ⊗[A] C` modulo `J` is projective.
  have hker : RingHom.ker (algebraMap A (Ac ⧸ J)) ≠ ⊥ := fun hc =>
    hI (le_bot_iff.mp (hc ▸ AdicCompletion.le_ker_algebraMap_quotient_map I))
  have hD := hquot (Ac ⧸ J) (AdicCompletion.surjective_algebraMap_quotient_map I hIfg) hker
  have h5 : Module.Projective (Ac ⧸ J) ((Ac ⊗[A] C) ⧸ J • (⊤ : Submodule Ac (Ac ⊗[A] C))) :=
    have := hD
    Module.Projective.of_equiv
      ((TensorProduct.AlgebraTensorModule.cancelBaseChange A Ac (Ac ⧸ J) (Ac ⧸ J) C).symm.trans
        (TensorProduct.quotTensorEquivQuotSMulBase Ac (Ac ⊗[A] C) J))
  -- Hypothesis 6 of Stacks 05DP: the associated primes of the fibres avoid `J`.
  have h6 := (h.baseChange_algebraMap Ac).map_sup_ne_top J (IsAdicComplete.le_jacobson_bot J)
  exact projective_of_flat_of_projective_quotient_of_associatedPrimes Ac (Ac ⊗[A] C) J
    (Ac ⊗[A] C) h5 h6

end
