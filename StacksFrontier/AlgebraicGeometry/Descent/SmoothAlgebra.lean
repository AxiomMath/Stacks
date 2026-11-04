module

public import Mathlib.RingTheory.Etale.Descent
public import StacksFrontier.AlgebraicGeometry.Etale.Descent
public import StacksFrontier.RingTheory.FinitePresentation.ColimitsII
public import StacksFrontier.FieldTheory.Separable.PerfectField
public import StacksFrontier.RingTheory.RegularRing.FaithfullyFlatDescent
public import StacksFrontier.RingTheory.Smooth.RegularLocalRing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smoothness descends along a faithfully flat algebra of finite presentation

Let `R → A → B` be ring maps with `B` faithfully flat and of finite presentation over `A`. If
`B` is smooth over `R`, then so is `A`. This is the commutative algebra content of the descent
of smoothness along a surjective flat morphism locally of finite presentation.

The proof is the one of the source. Finite presentation of `A` over `R` descends by the
finitely presented model of `A → B`, flatness of `A` over `R` by faithfully flat descent of
flatness, and what is left is the smoothness of every fibre over a prime of `R`. Over a field
`k` the argument is regularity: a smooth algebra over a field is a regular ring, regularity
descends along a faithfully flat ring map, and over a perfect field a regular algebra of finite
presentation is smooth again — the last step applied after base change to the algebraic closure,
along which smoothness descends.

## Main definitions

No new definitions are introduced.

## Main results

* `Stacks.RingTheory.SmoothDescent.isRegularRing_of_smooth`: a smooth algebra over a field is a
  regular ring.
* `Stacks.RingTheory.SmoothDescent.smooth_of_isRegularRing`: over a perfect field, a regular
  algebra of finite presentation is smooth.
* `Stacks.RingTheory.SmoothDescent.smooth_of_faithfullyFlat_of_field`: over a field, smoothness
  descends along a faithfully flat algebra.
* `Stacks.RingTheory.SmoothDescent.finitePresentation_of_faithfullyFlat`: finite presentation
  descends along a faithfully flat algebra of finite presentation.
* `Stacks.RingTheory.SmoothDescent.smooth_of_faithfullyFlat`: smoothness descends along a
  faithfully flat algebra of finite presentation.
* `Stacks.RingTheory.SmoothDescent.ringHom_smooth_of_faithfullyFlat`: the same statement for
  ring homomorphisms, which is the form the scheme-level descent consumes.

## Implementation notes

Over a field which is not perfect a regular algebra of finite presentation need not be smooth,
so the last step of the fibre argument is run over the algebraic closure. What has to be
transported there is regularity of the base change, and this is done by the same two-step
argument as in Lemma 07NH: the base change `A ⊗[k] K → (A ⊗[k] K) ⊗[A] B` of a faithfully flat
map is faithfully flat, and `(A ⊗[k] K) ⊗[A] B` is `K ⊗[k] B` after cancelling the base change.
Both tensor products are written with the ring supplying the new scalars on the left, the side
Mathlib puts the `Algebra` instance of a tensor product on; the commutations this costs are
`Algebra.TensorProduct.comm`, and regularity travels along them by `IsRegularRing.of_ringEquiv`.

The fibre over a prime `p` of `R` is Mathlib's `Ideal.Fiber`, that is `κ(p) ⊗[R] A`, and the
faithfully flat algebra over it is `κ(p) ⊗[R] B`. The map between them is
`Algebra.TensorProduct.map`, and that it exhibits `κ(p) ⊗[R] B` as the base change of `B` along
`A → κ(p) ⊗[R] A` is `Algebra.IsPushout.comp_iff` applied to the tower `R → A → B` and the
scalar extension `R → κ(p)`.

Separability of an arbitrary extension of a perfect field, which is what Lemma 00TV needs at
the primes of a regular algebra over an algebraically closed field, is
`Algebra.isSeparableExtension_of_perfectField`: it is `Algebra.IsSeparableExtension`,
Definition 030O (2), and holds because every finitely generated subextension of a perfect field
is separably generated.

## References

* [Stacks Project, Tag 00TT](https://stacks.math.columbia.edu/tag/00TT)
* [Stacks Project, Tag 00TV](https://stacks.math.columbia.edu/tag/00TV)
* [Stacks Project, Tag 02KK](https://stacks.math.columbia.edu/tag/02KK)
* [Stacks Project, Tag 05B5](https://stacks.math.columbia.edu/tag/05B5)
* [Stacks Project, Tag 07NG](https://stacks.math.columbia.edu/tag/07NG)
* [Stacks Project, Tag 07NH](https://stacks.math.columbia.edu/tag/07NH)
-/

@[expose] public section

open TensorProduct

universe u v

namespace Stacks.RingTheory.SmoothDescent

/-- A smooth algebra over a field is a regular ring: it is Noetherian, being of finite type over
a field, and smoothness at a prime implies regularity of the local ring there. -/
theorem isRegularRing_of_smooth (k S : Type*) [Field k] [CommRing S] [Algebra k S]
    [Algebra.Smooth k S] : IsRegularRing S := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  rw [isRegularRing_iff]
  intro p _
  refine (Algebra.isSmoothAt_tfae_localKrullDim_and_isRegularLocalRing (k := k)
    ⟨p, ‹_›⟩ (Localization.AtPrime p)).2 ?_
  exact (Algebra.smoothLocus_eq_univ_iff.mpr
    (inferInstanceAs (Algebra.FormallySmooth k S))).ge (Set.mem_univ (⟨p, ‹_›⟩ : PrimeSpectrum S))

/-- Over a perfect field, an algebra of finite presentation which is a regular ring is smooth:
every residue field is a separable extension of the base, so Lemma 00TV turns regularity of each
local ring into smoothness at the corresponding prime. -/
@[ega "0 20.6.26" "special case",
  ega "IV 17.15.1" "special case",
  ega "IV 17.15.9" "a ⇒ b",
  sga "1 II 5.10" "regular implies smooth"]
theorem smooth_of_isRegularRing (k S : Type*) [Field k] [PerfectField k] [CommRing S] [Algebra k S]
    [Algebra.FinitePresentation k S] [IsRegularRing S] : Algebra.Smooth k S := by
  refine ⟨Algebra.smoothLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun x ↦ ?_), ‹_›⟩
  have := Algebra.isSeparableExtension_of_perfectField k x.asIdeal.ResidueField
  exact (Algebra.isSmoothAt_iff_isRegularLocalRing x.asIdeal (Localization.AtPrime x.asIdeal)).mpr
    inferInstance

/-- Regularity of a base change descends along a faithfully flat algebra: for a tower `k → A → B`
with `B` faithfully flat over `A` and any `k`-algebra `K`, regularity of `K ⊗[k] B` implies
regularity of `K ⊗[k] A`. The map `A ⊗[k] K → (A ⊗[k] K) ⊗[A] B` is the base change of
`A → B`, hence faithfully flat, and its target is `K ⊗[k] B`. -/
private theorem isRegularRing_tensorProduct_of_faithfullyFlat (k A B K : Type*) [CommRing k]
    [CommRing A] [CommRing B] [CommRing K] [Algebra k A] [Algebra k B] [Algebra A B]
    [IsScalarTower k A B] [Algebra k K] [Module.FaithfullyFlat A B] [IsRegularRing (K ⊗[k] B)] :
    IsRegularRing (K ⊗[k] A) := by
  have e : (A ⊗[k] K) ⊗[A] B ≃+* K ⊗[k] B :=
    ((Algebra.TensorProduct.comm A (A ⊗[k] K) B).toRingEquiv.trans
      (Algebra.TensorProduct.cancelBaseChange k A A B K).toRingEquiv).trans
        (Algebra.TensorProduct.comm k B K).toRingEquiv
  have : IsRegularRing ((A ⊗[k] K) ⊗[A] B) := IsRegularRing.of_ringEquiv e.symm
  have : IsRegularRing (A ⊗[k] K) := IsRegularRing.of_faithfullyFlat ((A ⊗[k] K) ⊗[A] B)
  exact IsRegularRing.of_ringEquiv (Algebra.TensorProduct.comm k A K).toRingEquiv

/-- **Descent of smoothness over a field.** Let `k → A → B` be algebras over a field `k` with `B`
faithfully flat over `A` and smooth over `k`, and let `A` be of finite presentation over `k`.
Then `A` is smooth over `k`. -/
@[sga "3 XIX 2.1" "special case"]
theorem smooth_of_faithfullyFlat_of_field {k : Type u} {A B : Type v} [Field k] [CommRing A]
    [CommRing B] [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation k A] [Algebra.Smooth k B] :
    Algebra.Smooth k A := by
  have : IsRegularRing (AlgebraicClosure k ⊗[k] B) :=
    isRegularRing_of_smooth (AlgebraicClosure k) _
  have : IsRegularRing (AlgebraicClosure k ⊗[k] A) :=
    isRegularRing_tensorProduct_of_faithfullyFlat k A B (AlgebraicClosure k)
  have : Algebra.Smooth (AlgebraicClosure k) (AlgebraicClosure k ⊗[k] A) :=
    smooth_of_isRegularRing _ _
  exact Algebra.Smooth.of_smooth_tensorProduct_of_faithfullyFlat (AlgebraicClosure k)

/-- **Stacks Project, Tag 02KK.** Finite presentation descends along a faithfully flat algebra of
finite presentation: if `A → B` is faithfully flat and of finite presentation and `B` is of finite
presentation over `R`, then so is `A`. -/
@[ega "IV 11.3.16" "special case", ega "IV 11.3.17", sga "3 XIX 2.1" "special case"]
theorem finitePresentation_of_faithfullyFlat {R : Type v} {A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation A B]
    [Algebra.FinitePresentation R B] : Algebra.FinitePresentation R A := by
  obtain ⟨A₀, B₀, _, _, _, _, _, _, _, _, _, _, hA₀, hB₀ff, hB₀fp, hpush⟩ :=
    Algebra.exists_faithfullyFlat_finitePresentation_model (R := R) (A := A) (B := B)
  have : IsScalarTower R A₀ B := .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R A B, IsScalarTower.algebraMap_apply R A₀ A,
      IsScalarTower.algebraMap_apply A₀ A B]
  have : Algebra.FinitePresentation R A₀ := hA₀
  have : Module.FaithfullyFlat A₀ B₀ := hB₀ff
  have : Algebra.FinitePresentation A₀ B₀ := hB₀fp
  have : Algebra.FinitePresentation A₀ B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R A₀ B
  have : Algebra.FinitePresentation B₀ B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation A₀ B₀ B
  have : Algebra.IsPushout A₀ B₀ A B := hpush.symm
  have : Algebra.FinitePresentation B₀ (B₀ ⊗[A₀] A) :=
    Algebra.FinitePresentation.equiv (Algebra.IsPushout.equiv A₀ B₀ A B).symm
  have : Algebra.FinitePresentation A₀ A :=
    Algebra.FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat B₀
  exact Algebra.FinitePresentation.trans R A₀ A

/-- The fibres of a descent situation are again descent situations: for a tower `R → A → B` with
`B` faithfully flat over `A`, the base change `T ⊗[R] B` is faithfully flat over `T ⊗[R] A` for
any `R`-algebra `T`, so over a field `T` the fibre `T ⊗[R] A` is formally smooth. -/
private theorem formallySmooth_tensorProduct {R A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Module.FaithfullyFlat A B] [Algebra.FinitePresentation R A] [Algebra.Smooth R B]
    (T : Type u) [Field T] [Algebra R T] :
    Algebra.FormallySmooth T (T ⊗[R] A) := by
  let _ : Algebra A (T ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra B (T ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
  let _ : Algebra (T ⊗[R] A) (T ⊗[R] B) :=
    (Algebra.TensorProduct.map (AlgHom.id T T) (IsScalarTower.toAlgHom R A B)).toRingHom.toAlgebra
  let _ : Algebra A (T ⊗[R] B) := ((algebraMap B (T ⊗[R] B)).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B (T ⊗[R] B) := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower T (T ⊗[R] A) (T ⊗[R] B) := .of_algebraMap_eq fun t =>
    ((Algebra.TensorProduct.map (AlgHom.id T T) (IsScalarTower.toAlgHom R A B)).commutes t).symm
  have : IsScalarTower A (T ⊗[R] A) (T ⊗[R] B) := .of_algebraMap_eq fun a => by
    show (1 : T) ⊗ₜ[R] (algebraMap A B a) =
      Algebra.TensorProduct.map (AlgHom.id T T) (IsScalarTower.toAlgHom R A B) (1 ⊗ₜ[R] a)
    simp
  have : IsScalarTower R (T ⊗[R] A) (T ⊗[R] B) := .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply R T (T ⊗[R] B),
      IsScalarTower.algebraMap_apply R T (T ⊗[R] A),
      ← IsScalarTower.algebraMap_apply T (T ⊗[R] A) (T ⊗[R] B)]
  have : Algebra.IsPushout A (T ⊗[R] A) B (T ⊗[R] B) :=
    ((Algebra.IsPushout.comp_iff R A T (T ⊗[R] A) (T := B) (T' := T ⊗[R] B)).mp
      inferInstance).symm
  have : Module.FaithfullyFlat (T ⊗[R] A) (T ⊗[R] B) :=
    Module.FaithfullyFlat.of_linearEquiv (T ⊗[R] A) ((T ⊗[R] A) ⊗[A] B)
      (Algebra.IsPushout.equiv A (T ⊗[R] A) B (T ⊗[R] B)).symm.toLinearEquiv
  exact (smooth_of_faithfullyFlat_of_field (k := T) (A := T ⊗[R] A) (B := T ⊗[R] B)).1

/-- **Descent of smoothness along a faithfully flat algebra of finite presentation.** Let
`R → A → B` be ring maps with `B` faithfully flat and of finite presentation over `A`. If `B` is
smooth over `R`, then `A` is smooth over `R`. -/
@[sga "3 XIX 2.1" "special case", sga "4 IV 8.5.5" "special case"]
theorem smooth_of_faithfullyFlat {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [Module.FaithfullyFlat A B]
    [Algebra.FinitePresentation A B] [Algebra.Smooth R B] : Algebra.Smooth R A := by
  have : Module.Flat R B :=
    RingHom.flat_algebraMap_iff.mp (RingHom.smooth_algebraMap.mpr inferInstance).flat
  have : Algebra.FinitePresentation R A := finitePresentation_of_faithfullyFlat (B := B)
  have : Module.Flat R A := Stacks.Etale.flat_of_flat_of_faithfullyFlat R A B
  exact Algebra.Smooth.of_formallySmooth_fiber fun p _ =>
    formallySmooth_tensorProduct (A := A) (B := B) p.ResidueField

/-- **Descent of smoothness along a faithfully flat ring map of finite presentation.** If
`ψ : A →+* B` is faithfully flat and of finite presentation and `ψ.comp φ` is smooth, then
`φ : R →+* A` is smooth. -/
@[sga "3 XIX 2.1" "special case", sga "4 IV 8.5.5" "special case"]
theorem ringHom_smooth_of_faithfullyFlat {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    (φ : R →+* A) (ψ : A →+* B) (hcomp : (ψ.comp φ).Smooth) (hff : ψ.FaithfullyFlat)
    (hfp : ψ.FinitePresentation) : φ.Smooth := by
  let _ : Algebra R A := φ.toAlgebra
  let _ : Algebra A B := ψ.toAlgebra
  let _ : Algebra R B := (ψ.comp φ).toAlgebra
  have : IsScalarTower R A B := .of_algebraMap_eq fun _ => rfl
  have : Module.FaithfullyFlat A B := RingHom.faithfullyFlat_algebraMap_iff.mp hff
  have : Algebra.FinitePresentation A B := RingHom.finitePresentation_algebraMap.mp hfp
  have : Algebra.Smooth R B := RingHom.smooth_algebraMap.mp hcomp
  exact RingHom.smooth_algebraMap.mpr (smooth_of_faithfullyFlat (B := B))

end Stacks.RingTheory.SmoothDescent

end
