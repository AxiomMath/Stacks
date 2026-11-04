module

public import StacksFrontier.RingTheory.Dualizing.MonicQuotient
public import StacksFrontier.RingTheory.Dualizing.SelfDualAlgebra
public import StacksFrontier.RingTheory.Dualizing.SelfDualDerivedTensor
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.CompleteIntersection
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.DerivedTensor
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.DerivedTensorUnconditional
public import StacksFrontier.RingTheory.Dualizing.UpperShriek.SurjectiveAnyPresentation
import all StacksFrontier.RingTheory.Dualizing.UpperShriek.DerivedTensor

/-!
# Upper shriek of a finite ring map is derived coextension of scalars

This is [Stacks, Tag 0C0G] for a finite homomorphism, with no Noetherian hypothesis: for
`φ : R → A` finite and any polynomial presentation `p` of `φ`,

`φ^! ≅ RHom_R(A, -) : D(R) ⥤ D(A)`.

The source's reduction is followed with one change of route.  A finite `φ` factors as
`R → C → A` with `C = R[T₀, …, Tₙ₋₁]/(f₀(T₀), …, fₙ₋₁(Tₙ₋₁))` for monic `fᵢ` and the second map
surjective (`Dualizing.exists_monicIdeal_quotient_surjection`), and the case of a surjection is
already known at every presentation, as is the composition of upper shrieks with a surjective
second map; so everything reduces to the bottom map `R → C`.  There the two sides are computed
separately and found equal:

* `(R → C)^! ≅ - ⊗_R^L ω_{C/R}` with `ω_{C/R} = (R → C)^!(R)`, because the relations
  `f₀(T₀), …, fₙ₋₁(Tₙ₋₁)` are a weakly regular sequence of length `n`
  (`MvPolynomial.isWeaklyRegular_ofFn_aeval_X_of_monic`), which makes `R → C` a local complete
  intersection and so puts [Stacks, Tag 0E4B] at its disposal;
* `ω_{C/R} ≅ C` in degree zero, by the same weak regularity through
  `Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_obj_unit_iso_single`: the sequence
  has length `n` and the presentation has `n` variables, so the shift cancels;
* `RHom_R(C, -) ≅ - ⊗_R^L C`, because `C` is finite free over `R` and is its own `R`-linear dual
  (`Dualizing.nonempty_derivedHom_iso_derivedTensorProductOver_of_selfDual_algebra`, which is
  [Stacks, Tag 0BZE] together with the source's computation of `Hom_R(C, R)`).

Where the source instead invokes [Stacks, Tag 0BZH] for `R[x] → R[x]/(f)` one variable at a time
and composes with [Stacks, Tag 0BZT], here all `n` variables are treated at once; the composition
lemma is then needed only for the final surjection `C → A`, where it is unconditional and holds
on all of `D(R)` rather than only on `D⁺(R)`.

## Main results

* `Dualizing.nonempty_upperShriekFunctor_obj_unit_iso_single_monicIdeal` — **`ω_{C/R} ≅ C` in
  degree zero** for a monic quotient `C`.
* `Dualizing.nonempty_upperShriekFunctor_iso_derivedHom_monicIdeal` — Tag 0C0G for the bottom map
  `R → C` of the factorization.
* `Dualizing.upperShriekFunctor_iso_derivedHom_of_finite` — **[Stacks, Tag 0C0G] for a finite
  `φ`**, at an arbitrary polynomial presentation.

## References

* [Stacks Project, Tag 0C0G](https://stacks.math.columbia.edu/tag/0C0G)
* [Stacks Project, Tag 0BZE](https://stacks.math.columbia.edu/tag/0BZE)
* [Stacks Project, Tag 0E4B](https://stacks.math.columbia.edu/tag/0E4B)
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial Polynomial RingTheory.Sequence

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace Dualizing

variable {R A : Type u} [CommRing R] [CommRing A]

/-- **The relative dualizing complex of a monic quotient is the quotient itself, in degree zero.**
For monic `f₀, …, fₙ₋₁` in `R[T]` and `C = R[T₀, …, Tₙ₋₁]/(f₀(T₀), …, fₙ₋₁(Tₙ₋₁))`,

`ω_{C/R} = (R → C)^!(R) ≅ C`

in degree zero, upper shriek being read at the quotient presentation.

This is the one input of [Stacks, Tag 0C0G] in the finite case that the surjective case does not
supply.  The relations are a weakly regular sequence of length `n`
(`MvPolynomial.isWeaklyRegular_ofFn_aeval_X_of_monic`) and the presentation has `n` variables, so
the degree `c - n` of
`Dualizing.PolynomialPresentation.nonempty_upperShriekFunctor_obj_unit_iso_single` is zero. -/
theorem nonempty_upperShriekFunctor_obj_unit_iso_single_monicIdeal (n : ℕ)
    (f : Fin n → Polynomial R) (hf : ∀ i, (f i).Monic) :
    letI : MonoidalCategoryStruct (ModuleCat.{u} R) :=
      ModuleCat.liftedModuleMonoidalStruct.{u, u}
    letI : MonoidalCategory (ModuleCat.{u} R) := ModuleCat.liftedModuleMonoidal.{u, u}
    let R₀ := (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
      (MonoidalCategoryStruct.tensorUnit (ModuleCat.{u} R))
    Nonempty ((quotientPresentation n (monicIdeal n f)).upperShriekFunctor.{u, u}.obj R₀ ≅
      (DerivedCategory.singleFunctor
          (ModuleCat.{u} (MvPolynomial (Fin n) R ⧸ monicIdeal n f)) 0).obj
        (ModuleCat.of (MvPolynomial (Fin n) R ⧸ monicIdeal n f)
          (MvPolynomial (Fin n) R ⧸ monicIdeal n f))) := by
  obtain ⟨e⟩ := PolynomialPresentation.nonempty_upperShriekFunctor_obj_unit_iso_single
    (quotientPresentation n (monicIdeal n f))
    (MvPolynomial.isWeaklyRegular_ofFn_aeval_X_of_monic n f hf)
    ((ker_quotientPresentation n (monicIdeal n f)).trans (monicIdeal_eq_ofList n f))
  refine ⟨e.trans (eqToIso ?_)⟩
  congr 1
  simp [quotientPresentation]

/-- **Stacks Project, Tag 0C0G for the bottom map of the monic factorization.**  For monic
`f₀, …, fₙ₋₁` in `R[T]` and `C = R[T₀, …, Tₙ₋₁]/(f₀(T₀), …, fₙ₋₁(Tₙ₋₁))` finite, free and
self-dual over `R`, upper shriek of the quotient presentation of `R → C` is the
derived coextension of scalars `RHom_R(C, -)`.

Both sides are derived tensoring with a single object: the left by [Stacks, Tag 0E4B], `R → C`
being a local complete intersection because the relations are a weakly regular sequence, and the
right by [Stacks, Tag 0BZE] in the form
`Dualizing.nonempty_derivedHom_iso_derivedTensorProductOver_of_selfDual_algebra`.  The two
objects agree: the first is `ω_{C/R}`, which is `C` in degree zero by
`Dualizing.nonempty_upperShriekFunctor_obj_unit_iso_single_monicIdeal`, and the second is `C` in
degree zero. -/
theorem nonempty_upperShriekFunctor_iso_derivedHom_monicIdeal (n : ℕ)
    (f : Fin n → Polynomial R) (hf : ∀ i, (f i).Monic)
    (hfin : Module.Finite R (MvPolynomial (Fin n) R ⧸ monicIdeal n f))
    (hfree : Module.Free R (MvPolynomial (Fin n) R ⧸ monicIdeal n f))
    (hself : IsSelfDualAlgebra R (MvPolynomial (Fin n) R ⧸ monicIdeal n f)) :
    Nonempty ((quotientPresentation n (monicIdeal n f)).upperShriekFunctor.{u, u} ≅
      derivedHom.{u, u, u} (algebraMap R (MvPolynomial (Fin n) R ⧸ monicIdeal n f))) := by
  let := hfin
  let := hfree
  obtain ⟨eOmega⟩ := nonempty_upperShriekFunctor_obj_unit_iso_single_monicIdeal n f hf
  obtain ⟨eTensor⟩ :=
    PolynomialPresentation.nonempty_upperShriekFunctor_iso_derivedTensorProduct_of_lci
      (quotientPresentation n (monicIdeal n f))
      (isLocalCompleteIntersection_algebraMap_monicIdeal n f hf)
  obtain ⟨eDual⟩ := nonempty_derivedHom_iso_derivedTensorProductOver_of_selfDual_algebra
    (R := R) (B := MvPolynomial (Fin n) R ⧸ monicIdeal n f) hself.iso
  exact ⟨eTensor.trans (Iso.trans (derivedTensorProductOver_congr.{u, u}
    (algebraMap R (MvPolynomial (Fin n) R ⧸ monicIdeal n f)) _ _ eOmega).some eDual.symm)⟩

/-- **Stacks Project, Tag 0C0G for a finite `φ`.**  Let `φ : R →+* A` be a finite homomorphism
and let `p` be any polynomial presentation of `φ`.  Then the algebraic upper
shriek functor of `p` is the derived coextension-of-scalars functor

`φ^! ≅ RHom_R(A, -) : D(R) ⥤ D(A)`

of [Stacks, Tag 0A70].

`φ` factors as `R → C → A` through a monic quotient
`C = R[T₀, …, Tₙ₋₁]/(f₀(T₀), …, fₙ₋₁(Tₙ₋₁))` by a surjection
(`Dualizing.exists_monicIdeal_quotient_surjection`).  The bottom map is
`Dualizing.nonempty_upperShriekFunctor_iso_derivedHom_monicIdeal`, whose inputs — the weak
regularity of `f₀(T₀), …, fₙ₋₁(Tₙ₋₁)` and the finiteness, freeness and self-duality of `C` — are
`MvPolynomial.isWeaklyRegular_ofFn_aeval_X_of_monic` and
`Dualizing.finite_free_selfDual_monicIdeal`.  The surjection is Tag 0C0G at an arbitrary
presentation, `Dualizing.upperShriekFunctor_iso_derivedHom_of_surjective`, and the two halves are
put together by [Stacks, Tag 0BZT] for a surjective second map
(`Dualizing.upperShriekFunctor_comp_of_surjective`) and [Stacks, Tag 0C0F]
(`Dualizing.derivedHomCompIso`).

The module universe is the ring universe here, unlike in the surjective case: the computation of
`ω_{C/R}` and the tensor formula of [Stacks, Tag 0E4B] it is fed to are both stated at module
universe equal to the ring universe. -/
@[stacks 0C0G "for a finite φ of Noetherian rings, at an arbitrary polynomial presentation, at \
module universe equal to the ring universe"]
theorem upperShriekFunctor_iso_derivedHom_of_finite (φ : R →+* A) (hφ : φ.Finite)
    (p : PolynomialPresentation φ) :
    Nonempty (p.upperShriekFunctor.{u, u} ≅ derivedHom.{u, u, u} φ) := by
  obtain ⟨n, f, hf, ψ, hψ, hcomp⟩ := exists_monicIdeal_quotient_surjection φ hφ
  obtain ⟨hfin, hfree, hself⟩ := finite_free_selfDual_monicIdeal n f hf
  obtain ⟨eBottom⟩ := nonempty_upperShriekFunctor_iso_derivedHom_monicIdeal n f hf hfin hfree hself
  let q := quotientPresentation n (monicIdeal n f)
  let q' := PolynomialPresentation.ofSurjective ψ hψ
  let r : PolynomialPresentation
      (ψ.comp (algebraMap R (MvPolynomial (Fin n) R ⧸ monicIdeal n f))) :=
    { variableCount := p.variableCount
      toRingHom := p.toRingHom
      commutes := p.commutes.trans hcomp.symm
      surjective := p.surjective }
  have hr : r.upperShriekFunctor.{u, u} = p.upperShriekFunctor.{u, u} := rfl
  obtain ⟨eComp⟩ := upperShriekFunctor_comp_of_surjective.{u, u} q hψ q' r
  obtain ⟨eTop⟩ := upperShriekFunctor_iso_derivedHom_of_surjective.{u, u} ψ hψ q'
  obtain ⟨eMerge⟩ := derivedHomCompIso.{u, u}
    (algebraMap R (MvPolynomial (Fin n) R ⧸ monicIdeal n f)) ψ
  rw [hr] at eComp
  have hfun : derivedHom.{u, u, u}
        (ψ.comp (algebraMap R (MvPolynomial (Fin n) R ⧸ monicIdeal n f)))
      = derivedHom.{u, u, u} φ := congrArg _ hcomp
  exact ⟨eComp.symm ≪≫ Functor.isoWhiskerRight eBottom q'.upperShriekFunctor.{u, u} ≪≫
    Functor.isoWhiskerLeft _ eTop ≪≫ eMerge ≪≫ eqToIso hfun⟩

end Dualizing

end
