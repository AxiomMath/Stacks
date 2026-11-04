module

public import StacksFrontier.Homology.Tor.Independence
public import StacksFrontier.RingTheory.Flat.TensorProductFlatLifts

/-!
# Descent of the vanishing of Tor along a flat base change with flat lifts

Stacks 08HW compares the Tor modules of two algebras with those of two flat lifts of them over a
flat base change: the comparison map

`(A' ⊗_{R'} C') ⊗_{A₀ ⊗_{R₀} C₀} Tor_i^{R₀}(A₀, C₀) → Tor_i^{R'}(A', C')`

is an isomorphism.  So Tor independence of `A'` and `C'` over `R'` says that the left-hand side
vanishes, and the question is what that gives back about `Tor_i^{R₀}(A₀, C₀)` itself.  It gives
the vanishing of its localization at every prime of `A₀ ⊗_{R₀} C₀` that is the contraction of a
prime of `A' ⊗_{R'} C'` — which by Stacks 08HX is the form in which Tor independence of `A₀` and
`C₀` over `R₀` is checked.

The descent is faithfully flat descent at a pair of primes: the map
`A₀ ⊗_{R₀} C₀ → A' ⊗_{R'} C'` is flat by
`RingHom.Flat.tensorProduct_of_flat_lifts`, so its localization at a prime and its contraction is
a flat local homomorphism of local rings, hence faithfully flat, and a faithfully flat base change
reflects the triviality of a module.

## Main results

* `RingTheory.TorIndependence.subsingleton_localizedModule_of_subsingleton_tensorProduct`: a
  module whose base change along a flat ring map is trivial has trivial localization at every
  prime which is the contraction of a prime of the target.
* `RingTheory.TorIndependence.subsingleton_localizedModule_torObj_of_flat_lifts`: the Tor module
  of `A₀` and `C₀` over `R₀` has trivial localization at a prime of `A₀ ⊗_{R₀} C₀` which is the
  contraction of a prime of `A' ⊗_{R'} C'`, as soon as `A'` and `C'` are Tor independent
  over `R'`.

## Implementation notes

The hypotheses are exactly those of `RingTheory.TorIndependence.isIso_torExtensionMap_of_flat`,
with the flatness of the second lift taken in the form `C₀ ⊗_{R₀} R' → C'` that
`IsLocalRing.IsHenselization.flat_tensorProduct_lift` produces; the form `R' ⊗_{R₀} C₀ → C'`
that Stacks 08HW asks for is obtained from it by `Algebra.TensorProduct.comm`, which is
bijective.

All six rings are taken in one universe, which is what lets
`RingTheory.TorIndependence.isIso_torExtensionMap_of_flat_sameUniverse` be used directly, and is
the situation of the comparison of conditions (1) and (4) of Stacks 08IQ after the étale local
rings have been brought down to the universe of the schemes by
`RingTheory.TorIndependence.torIndependent_congr_universe`.

## References

* [Stacks Project, Tag 08HW](https://stacks.math.columbia.edu/tag/08HW)
* [Stacks Project, Tag 08HX](https://stacks.math.columbia.edu/tag/08HX)
* [Stacks Project, Tag 08IQ](https://stacks.math.columbia.edu/tag/08IQ)
-/

@[expose] public noncomputable section

open CategoryTheory

open scoped TensorProduct

namespace RingTheory.TorIndependence

universe u

/-- **Faithfully flat descent of triviality at a pair of primes.**  Let `T → C` be a flat ring
map, let `M` be a `T`-module whose base change `C ⊗_T M` is trivial, and let `𝔰` be a prime of `T`
which is the contraction of a prime `𝔭` of `C`.  Then the localization of `M` at `𝔰` is trivial.

The localized map `T_𝔰 → C_𝔭` is a flat local homomorphism of local rings, hence faithfully flat,
and `Module.FaithfullyFlat.lTensor_reflects_triviality` turns the triviality of
`C_𝔭 ⊗_{T_𝔰} M_𝔰` into that of `M_𝔰`. -/
theorem subsingleton_localizedModule_of_subsingleton_tensorProduct
    {T C M : Type u} [CommRing T] [CommRing C] [Algebra T C]
    [AddCommGroup M] [Module T M]
    (hflat : Module.Flat T C)
    (s : Ideal T) [s.IsPrime] (p : Ideal C) [p.IsPrime]
    (hsp : s = p.comap (algebraMap T C))
    (hsub : Subsingleton (C ⊗[T] M)) :
    Subsingleton (LocalizedModule s.primeCompl M) := by
  -- the localized map `T_𝔰 → C_𝔭`, with the scalar tower through `T`
  let : Algebra (Localization.AtPrime s) (Localization.AtPrime p) :=
    (Localization.localRingHom s p (algebraMap T C) hsp).toAlgebra
  have : IsScalarTower T (Localization.AtPrime s) (Localization.AtPrime p) :=
    IsScalarTower.of_algebraMap_eq fun t =>
      (Localization.localRingHom_to_map s p (algebraMap T C) hsp t).symm
  -- it is flat and local, hence faithfully flat
  have hflatloc : Module.Flat (Localization.AtPrime s) (Localization.AtPrime p) :=
    RingHom.Flat.localRingHom (RingHom.flat_algebraMap_iff.mpr hflat) p s hsp
  have : IsLocalHom
      (algebraMap (Localization.AtPrime s) (Localization.AtPrime p)) :=
    Localization.isLocalHom_localRingHom s p (algebraMap T C) hsp
  have : Module.FaithfullyFlat (Localization.AtPrime s) (Localization.AtPrime p) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  -- the base change to `C_𝔭` of `M` is trivial, `C_𝔭` being a `C`-algebra
  have hsubp : Subsingleton (Localization.AtPrime p ⊗[T] M) := by
    refine (subsingleton_iff_forall_eq 0).mpr fun x => ?_
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul c m =>
      have h1 : (1 : Localization.AtPrime p) ⊗ₜ[T] m = 0 := by
        have h := congrArg
          (TensorProduct.map
            (IsScalarTower.toAlgHom T C (Localization.AtPrime p)).toLinearMap
            (LinearMap.id : M →ₗ[T] M))
          (Subsingleton.elim ((1 : C) ⊗ₜ[T] m) 0)
        simpa using h
      calc c ⊗ₜ[T] m = c • ((1 : Localization.AtPrime p) ⊗ₜ[T] m) := by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        _ = 0 := by rw [h1, smul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  -- and that is the base change of `M_𝔰` to `C_𝔭` over `T_𝔰`
  have : Subsingleton
      (Localization.AtPrime p ⊗[Localization.AtPrime s] LocalizedModule s.primeCompl M) := by
    have ec : (Localization.AtPrime p ⊗[Localization.AtPrime s]
          LocalizedModule s.primeCompl M) ≃ₗ[Localization.AtPrime s]
        (Localization.AtPrime p ⊗[Localization.AtPrime s]
          (Localization.AtPrime s ⊗[T] M)) :=
      TensorProduct.congr (LinearEquiv.refl (Localization.AtPrime s) _)
        (LocalizedModule.equivTensorProduct s.primeCompl M)
    have ecb : (Localization.AtPrime p ⊗[Localization.AtPrime s]
          (Localization.AtPrime s ⊗[T] M)) ≃ₗ[Localization.AtPrime s]
        (Localization.AtPrime p ⊗[T] M) :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange T
        (Localization.AtPrime s) (Localization.AtPrime s) (Localization.AtPrime p) M
    exact (ec.trans ecb).injective.subsingleton
  exact Module.FaithfullyFlat.lTensor_reflects_triviality (Localization.AtPrime s)
    (Localization.AtPrime p) (LocalizedModule s.primeCompl M)

/-- **Stacks 08HW read as a descent statement at a prime of the tensor product.**  Let `R₀ → R'`
be flat, let `A₀`, `C₀` be `R₀`-algebras and `A'`, `C'` be `R'`-algebras receiving them over `R₀`
by maps whose lifts `A₀ ⊗_{R₀} R' → A'` and `C₀ ⊗_{R₀} R' → C'` are flat.  If `A'` and `C'` are
Tor independent over `R'`, then for every prime `𝔰` of `A₀ ⊗_{R₀} C₀` which is the contraction of
a prime of `A' ⊗_{R'} C'` the localization of `Tor_i^{R₀}(A₀, C₀)` at `𝔰` is trivial, for every
`i > 0`.

This is the vanishing that condition (3) of Stacks 08HX asks for at the prime `𝔰`, so it is the
step that turns Tor independence of the étale local rings into Tor independence of the ordinary
rings of sections in the comparison of conditions (1) and (4) of Stacks 08IQ. -/
theorem subsingleton_localizedModule_torObj_of_flat_lifts
    (R₀ A₀ C₀ R' A' C' : Type u)
    [CommRing R₀] [CommRing A₀] [CommRing C₀] [CommRing R'] [CommRing A'] [CommRing C']
    [Algebra R₀ A₀] [Algebra R₀ C₀] [Algebra R₀ R'] [Algebra R₀ A'] [Algebra R₀ C']
    [Algebra R' A'] [Algebra R' C'] [IsScalarTower R₀ R' A'] [IsScalarTower R₀ R' C']
    (fA : A₀ →ₐ[R₀] A') (fC : C₀ →ₐ[R₀] C')
    (hR' : RingHom.Flat (algebraMap R₀ R'))
    (hA : RingHom.Flat (Algebra.TensorProduct.lift fA
      (IsScalarTower.toAlgHom R₀ R' A') fun _ _ => Commute.all _ _).toRingHom)
    (hC : RingHom.Flat (Algebra.TensorProduct.lift fC
      (IsScalarTower.toAlgHom R₀ R' C') fun _ _ => Commute.all _ _).toRingHom)
    (hTor : TorIndependent R' A' C')
    (s : Ideal (A₀ ⊗[R₀] C₀)) [s.IsPrime]
    (p : Ideal (A' ⊗[R'] C')) [p.IsPrime]
    (hsp : s = p.comap (TorChangeOfRings.tensorProductMap R₀ R' A₀ C₀ A' C' fA fC))
    (i : ℕ) (hi : 0 < i) :
    letI := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty
      R₀ A₀ C₀ i
    Subsingleton (LocalizedModule s.primeCompl (TorChangeOfRings.torObj R₀ i A₀ C₀)) := by
  let := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R₀ A₀ C₀ i
  let := TorChangeOfRings.moduleStructure TorChangeOfRings.canonicalSystem_nonempty R' A' C' i
  -- Stacks 08HW asks for the second lift with the base change on the left
  have hC₂ : RingHom.Flat (Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom R₀ R' C') fC fun _ _ => Commute.all _ _).toRingHom := by
    have he : (Algebra.TensorProduct.lift (IsScalarTower.toAlgHom R₀ R' C') fC
        fun _ _ => Commute.all _ _).toRingHom =
        (Algebra.TensorProduct.lift fC (IsScalarTower.toAlgHom R₀ R' C')
          fun _ _ => Commute.all _ _).toRingHom.comp
          (Algebra.TensorProduct.comm R₀ R' C₀).toRingHom := by
      refine RingHom.ext fun z => ?_
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul r c =>
        show algebraMap R' C' r * fC c = _
        simpa using (mul_comm (algebraMap R' C' r) (fC c))
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    rw [he]
    exact RingHom.Flat.comp
      (RingHom.Flat.of_bijective (Algebra.TensorProduct.comm R₀ R' C₀).bijective) hC
  -- the comparison map of Stacks 08HW is invertible
  set e := TorChangeOfRings.extensionMap TorChangeOfRings.canonicalSystem_nonempty
    R₀ R' A₀ C₀ A' C' i fA fC with hedef
  have he : IsIso e :=
    isIso_torExtensionMap_of_flat_sameUniverse R₀ R' A₀ C₀ A' C' fA fC hR' hA hC₂ i
  -- the target of the comparison is trivial, so its source is
  have : Subsingleton (TorChangeOfRings.torObj R' i A' C') :=
    (torIndependent_iff_subsingleton_tor R' A' C').mp hTor i hi
  let : Algebra (A₀ ⊗[R₀] C₀) (A' ⊗[R'] C') :=
    (TorChangeOfRings.tensorProductMap R₀ R' A₀ C₀ A' C' fA fC).toAlgebra
  have hsub : Subsingleton
      ((A' ⊗[R'] C') ⊗[A₀ ⊗[R₀] C₀] TorChangeOfRings.torObj R₀ i A₀ C₀) :=
    ((ModuleCat.mono_iff_injective e).mp inferInstance).subsingleton
  -- the map of tensor-product algebras is flat
  have hflat : Module.Flat (A₀ ⊗[R₀] C₀) (A' ⊗[R'] C') :=
    RingHom.flat_algebraMap_iff.mp
      (RingHom.Flat.tensorProduct_of_flat_lifts fA fC hR' hA hC
        (TorChangeOfRings.tensorProductMap R₀ R' A₀ C₀ A' C' fA fC) fun a c => by
          show (fA a ⊗ₜ[R'] (1 : C')) * ((1 : A') ⊗ₜ[R'] fC c) = _
          simp)
  exact subsingleton_localizedModule_of_subsingleton_tensorProduct hflat s p hsp hsub

end RingTheory.TorIndependence

end
