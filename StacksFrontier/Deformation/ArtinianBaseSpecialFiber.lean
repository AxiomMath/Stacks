module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Localization.Away.AdjoinRoot
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Smooth.Fiber
public import Mathlib.RingTheory.Smooth.Locus
public import StacksFrontier.RingTheory.Nilpotent.Descent
public import StacksFrontier.RingTheory.Smooth.Syntomic
public import StacksFrontier.RingTheory.UniversalHomeomorphism.Examples
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat algebras over an Artinian local base and their special fibres

Let `A` be an Artinian local ring with a surjection `A → k` onto a field, let `Q` be a flat
`A`-algebra and let `P = k ⊗_A Q` be its special fibre. Because the kernel of `A → k` is the
maximal ideal of `A` and therefore nilpotent, properties of `Q` over `A` are governed by
properties of `P` over `k`. This file records the two such transfers that the smoothness
conclusion of **Stacks 0DZ5** needs.

The first is finiteness: `Q` is of finite type over `A` as soon as `P` is of finite type over
`k`. This is **Stacks 0G8U** applied to the nilpotent ideal `ker(A → k)`, whose extension to
`Q` is the kernel of `Q → P`.

The second is syntomy of localizations. If `h ∈ Q` has image in an ideal `J ⊆ P` outside whose
zero set `P` is smooth over `k`, then `A → Q_h` is syntomic. Indeed `Q_h` is flat and of finite
presentation over `A`, and the only prime of the Artinian local ring `A` is `ker(A → k)`, so
the only fibre to inspect is the special one; that fibre is `κ ⊗_k P_{h̄}` for the residue
field `κ` of the prime, and `P_{h̄}` is smooth over `k` because `D(h̄) ⊆ D(J)` lies in the
smooth locus. Smoothness is stable under base change, and a smooth algebra is syntomic.

## Main results

* `Deformation.finiteType_of_isPushout_specialFiber`: `Q` is of finite type over `A`.
* `Deformation.smooth_localizationAway_specialFiber`: `A → Q_h` is smooth.
* `Deformation.syntomic_localizationAway_specialFiber`: `A → Q_h` is syntomic, the affine
  reading of "syntomic outside `V(J)`" that Stacks 0DZ3 consumes.

## Implementation notes

The special-fibre square is taken as an `Algebra.IsPushout A k Q P` hypothesis rather than
spelled out as a tensor product, so that a caller holding a pushout square of commutative rings
can feed it in after transporting it once.

The fibre of a prime `I` of `A` is `I.ResidueField ⊗_A Q_h`, and the proof never identifies
`I.ResidueField` with `k`: it only uses that the structural map `A → I.ResidueField` kills
`ker(A → k)`, hence factors through `k`, which turns the fibre into a base change of `P_{h̄}`
along `k → I.ResidueField` by `Algebra.TensorProduct.cancelBaseChange`. That avoids having to
identify the localization of `A` at its maximal ideal with `A`.

## References

* [Stacks Project, Tag 0G8U](https://stacks.math.columbia.edu/tag/0G8U)
* [Stacks Project, Tag 00TF](https://stacks.math.columbia.edu/tag/00TF)
* [Stacks Project, Tag 0DZ3](https://stacks.math.columbia.edu/tag/0DZ3)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Deformation

section SpecialFibre

variable {A k Q P : Type u} [CommRing A] [Field k] [CommRing Q] [CommRing P]
  [Algebra A k] [Algebra A Q] [Algebra A P] [Algebra k P] [Algebra Q P]
  [IsScalarTower A k P] [IsScalarTower A Q P]
  [IsArtinianRing A] [IsLocalRing A] [Algebra.IsPushout A k Q P]

/-- The kernel of a surjection from an Artinian local ring onto a field is nilpotent: it is the
maximal ideal, which is the Jacobson radical of an Artinian ring. -/
@[sga "3 VIIB 1.6.D" "partial", sga "3 VIIB 3.2" "special case"]
theorem isNilpotent_ker_of_isArtinianRing (hsurj : Function.Surjective (algebraMap A k)) :
    IsNilpotent (RingHom.ker (algebraMap A k)) := by
  rw [IsLocalRing.ker_eq_maximalIdeal (algebraMap A k) hsurj,
    ← IsLocalRing.ringJacobson_eq_maximalIdeal, ← Ideal.jacobson_bot]
  exact IsArtinianRing.isNilpotent_jacobson_bot

/-- **Every prime of an Artinian local ring is the kernel of its surjection onto a field.** -/
theorem eq_ker_of_isPrime (hsurj : Function.Surjective (algebraMap A k))
    (I : Ideal A) [I.IsPrime] : I = RingHom.ker (algebraMap A k) := by
  rw [IsLocalRing.ker_eq_maximalIdeal (algebraMap A k) hsurj]
  exact IsLocalRing.eq_maximalIdeal ((IsArtinianRing.isPrime_iff_isMaximal I).mp ‹_›)

/-- **A flat algebra over an Artinian local base is of finite type as soon as its special fibre
is.** This is Stacks 0G8U for the nilpotent ideal `ker(A → k)`: the extension of that ideal to
`Q` is the kernel of the reduction `Q → P`, so the reduction of `Q` modulo it is `P`, which is
of finite type over `k = A / ker(A → k)`. -/
theorem finiteType_of_isPushout_specialFiber
    (hsurj : Function.Surjective (algebraMap A k)) [Algebra.FiniteType k P] :
    Algebra.FiniteType A Q := by
  obtain ⟨hsurjQ, hkerQ⟩ := Algebra.IsPushout.surjective_and_ker_eq_map_of_surjective
    (R := A) (S := k) (R' := Q) (S' := P) hsurj
  refine finiteType_of_isNilpotent_quotient_finiteType A (RingHom.ker (algebraMap A k)) Q
    (isNilpotent_ker_of_isArtinianRing hsurj) ?_
  -- identify the two quotients with `k` and `P`
  set I : Ideal A := RingHom.ker (algebraMap A k)
  let e₁ : (A ⧸ I) ≃+* k := RingHom.quotientKerEquivOfSurjective hsurj
  have he₁ : ∀ a : A, e₁ (Ideal.Quotient.mk I a) = algebraMap A k a := fun _ => rfl
  let : Algebra k (A ⧸ I) := e₁.symm.toRingHom.toAlgebra
  let : Algebra (A ⧸ I) P := ((algebraMap k P).comp e₁.toRingHom).toAlgebra
  have : IsScalarTower k (A ⧸ I) P := IsScalarTower.of_algebraMap_eq fun x => by
    show algebraMap k P x = algebraMap k P (e₁ (e₁.symm x))
    rw [e₁.apply_symm_apply]
  have hftP : Algebra.FiniteType (A ⧸ I) P :=
    Algebra.FiniteType.of_restrictScalars_finiteType k (A ⧸ I) P
  refine Algebra.FiniteType.equiv hftP (AlgEquiv.ofRingEquiv
    (f := (RingHom.quotientKerEquivOfSurjective hsurjQ).symm.trans
      (Ideal.quotEquivOfEq hkerQ)) fun r => ?_)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
  have hx : (RingHom.quotientKerEquivOfSurjective hsurjQ)
      (Ideal.Quotient.mk (RingHom.ker (algebraMap Q P)) (algebraMap A Q a)) =
      algebraMap A P a := (IsScalarTower.algebraMap_apply A Q P a).symm
  show (Ideal.quotEquivOfEq hkerQ)
      ((RingHom.quotientKerEquivOfSurjective hsurjQ).symm
        (algebraMap k P (e₁ (Ideal.Quotient.mk I a)))) = _
  rw [he₁ a, ← IsScalarTower.algebraMap_apply A k P, ← hx, RingEquiv.symm_apply_apply]
  rfl

/-- **A localization of a flat algebra over an Artinian local base is smooth as soon as the
corresponding localization of its special fibre is.** Let `J ⊆ P` be an ideal outside whose zero
set `P` is smooth over `k`, and let `h ∈ Q` have image in `J`. Then `A → Q_h` is smooth.

The basic open `D(h̄)` of `Spec(P)` is contained in `D(J)`, hence in the smooth locus, so
`P_{h̄}` is smooth over `k`. Over the Artinian local ring `A` the only prime is `ker(A → k)`, so
the fibre criterion of **Stacks 00TF** has a single fibre to check; that fibre is
`κ ⊗_A Q_h = κ ⊗_k P_{h̄}` for the residue field `κ` of the prime, a base change of a smooth
algebra. -/
theorem smooth_localizationAway_specialFiber
    (hsurj : Function.Surjective (algebraMap A k)) [Algebra.FiniteType k P] [Module.Flat A Q]
    (J : Ideal P)
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal)
    (h : Q) (hh : algebraMap Q P h ∈ J) :
    Algebra.Smooth A (Localization.Away h) := by
  have : Algebra.FiniteType A Q := finiteType_of_isPushout_specialFiber (P := P) hsurj
  have : Algebra.FinitePresentation A Q := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : Algebra.FinitePresentation Q (Localization.Away h) :=
    IsLocalization.Away.finitePresentation h
  have : Algebra.FinitePresentation A (Localization.Away h) :=
    Algebra.FinitePresentation.trans A Q (Localization.Away h)
  have : Module.Flat A (Localization.Away h) := Module.Flat.trans A Q (Localization.Away h)
  have : Algebra.FinitePresentation k P := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  -- the localization of the special fibre is smooth over `k`
  have hsmoothP : Algebra.Smooth k (Localization.Away (algebraMap Q P h)) := by
    rw [← Algebra.basicOpen_subset_smoothLocus_iff_smooth]
    intro q hq
    exact hsm q fun hJ => (PrimeSpectrum.mem_basicOpen _ _).mp hq (hJ hh)
  have : Algebra.FormallySmooth k (Localization.Away (algebraMap Q P h)) :=
    hsmoothP.formallySmooth
  -- `P_{h̄}` is the base change of `Q_h` along `A → k`
  let φ : Localization.Away h →+* Localization.Away (algebraMap Q P h) :=
    Localization.awayMap (algebraMap Q P) h
  have hφ : φ.comp (algebraMap Q (Localization.Away h))
      = (algebraMap P (Localization.Away (algebraMap Q P h))).comp (algebraMap Q P) := by
    ext x
    simp [φ, IsLocalization.Away.map]
  let : Algebra (Localization.Away h) (Localization.Away (algebraMap Q P h)) := φ.toAlgebra
  have htQ : IsScalarTower Q (Localization.Away h) (Localization.Away (algebraMap Q P h)) :=
    IsScalarTower.of_algebraMap_eq' <| by
      show _ = φ.comp (algebraMap Q (Localization.Away h))
      rw [hφ]
      exact IsScalarTower.algebraMap_eq Q P (Localization.Away (algebraMap Q P h))
  have : IsScalarTower A Q (Localization.Away (algebraMap Q P h)) :=
    IsScalarTower.to₁₂₄ A Q P (Localization.Away (algebraMap Q P h))
  have : IsScalarTower A k (Localization.Away (algebraMap Q P h)) :=
    IsScalarTower.to₁₂₄ A k P (Localization.Away (algebraMap Q P h))
  have : IsScalarTower A (Localization.Away h) (Localization.Away (algebraMap Q P h)) :=
    IsScalarTower.to₁₃₄ A Q (Localization.Away h) (Localization.Away (algebraMap Q P h))
  have : Algebra.IsPushout A Q k P := Algebra.IsPushout.symm inferInstance
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid P (Submonoid.powers h))
      (Localization.Away (algebraMap Q P h)) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    infer_instance
  have hpushL : Algebra.IsPushout Q P (Localization.Away h)
      (Localization.Away (algebraMap Q P h)) :=
    Algebra.isPushout_of_isLocalization (Submonoid.powers h) (Localization.Away h) P
      (Localization.Away (algebraMap Q P h))
  have : Algebra.IsPushout A k (Localization.Away h)
      (Localization.Away (algebraMap Q P h)) :=
    Algebra.IsPushout.symm ((Algebra.IsPushout.comp_iff A Q k P).mpr hpushL.symm)
  let e : k ⊗[A] Localization.Away h ≃ₐ[k] Localization.Away (algebraMap Q P h) :=
    Algebra.IsPushout.equiv A k (Localization.Away h) (Localization.Away (algebraMap Q P h))
  -- check the single fibre
  refine Algebra.Smooth.of_formallySmooth_fiber fun I _ => ?_
  have hIk : I = RingHom.ker (algebraMap A k) := eq_ker_of_isPrime hsurj I
  let g : k →+* I.ResidueField := (algebraMap A k).liftOfSurjective hsurj
    ⟨algebraMap A I.ResidueField, fun a ha => Ideal.algebraMap_residueField_eq_zero.mpr
      (by rw [hIk]; exact ha)⟩
  have hg : ∀ a : A, g (algebraMap A k a) = algebraMap A I.ResidueField a :=
    RingHom.liftOfSurjective_comp_apply _ hsurj _
  let : Algebra k I.ResidueField := g.toAlgebra
  have : IsScalarTower A k I.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun a => (hg a).symm
  exact Algebra.FormallySmooth.of_equiv
    (A := I.ResidueField ⊗[k] Localization.Away (algebraMap Q P h))
    ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := I.ResidueField)
        (A₁ := I.ResidueField)) e.symm).trans
      (Algebra.TensorProduct.cancelBaseChange A k I.ResidueField I.ResidueField
        (Localization.Away h)))

/-- **The affine reading of "syntomic outside `V(J)`" over an Artinian local base.** If `P` is
smooth over `k` away from the zero set of `J` and `h ∈ Q` has image in `J`, then `A → Q_h` is
syntomic. This is the hypothesis `hsyn` of **Stacks 0DZ3**.

It follows from `Deformation.smooth_localizationAway_specialFiber` because a smooth algebra is
syntomic (**Stacks 00TA**). -/
theorem syntomic_localizationAway_specialFiber
    (hsurj : Function.Surjective (algebraMap A k)) [Algebra.FiniteType k P] [Module.Flat A Q]
    (J : Ideal P)
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal)
    (h : Q) (hh : algebraMap Q P h ∈ J) :
    Algebra.Syntomic A (Localization.Away h) :=
  let := smooth_localizationAway_specialFiber (P := P) hsurj J hsm h hh
  Algebra.Smooth.syntomic A (Localization.Away h)

end SpecialFibre

end Deformation

end
