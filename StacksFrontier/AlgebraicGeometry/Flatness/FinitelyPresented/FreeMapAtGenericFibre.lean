module

public import Mathlib.RingTheory.Flat.Equalizer
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.CompleteDevissageStep

/-!
# The generic point of a geometrically integral fibre, and a free map over its residue field

Let `R → S` be a flat ring map whose fibre over a prime `r ⊆ R` is a geometrically integral
`κ(r)`-algebra. Then the extension `𝔭 = rS` is a prime ideal of `S` — the generic point of the
fibre — and for every finite `S`-module `N` there is a map from a finite free `S`-module to `N`
which becomes an isomorphism after base change to `κ(𝔭)`.

This is the existence assertion of Stacks Tag 05IA, the starting point of the induction on a
dévissage.

## Main results

* `Algebra.ker_algebraMap_tensorProduct_left`: the kernel of `C → C ⊗[D] N` for a flat
  `D`-algebra `C` is the extension of the kernel of `D → N`.
* `Ideal.isPrime_map_of_flat_of_isGeometricallyIntegral`: the extension `rS` is prime.
* `Module.exists_freeMap_bijective_residueField`: **Stacks Tag 05IA**, the existence assertion.
  The spreading-out half of the tag is in
  `StacksFrontier.AlgebraicGeometry.Flatness.FinitelyPresented.FreeMapSpreadingOut`.

## Implementation notes

Geometric integrality of the fibre is taken in its algebraic form
`Algebra.IsGeometricallyIntegral κ(r) (r.Fiber S)`, which is how
`Algebra.isGeometricallyIntegral_tensorProduct_residueField` delivers it from the scheme-level
condition. The prime `rS` is identified with the kernel of `S → S ⊗[R] κ(r)`, whose target is a
domain; the comparison of the two tensor factors is `Algebra.TensorProduct.comm`.

Base change to the residue field is expressed by `LinearMap.rTensor`, whose source is
canonically the finite power of that residue field; the free map itself is
`Module.freeMapAtResidueField`.

Only the existence assertion carries the tag here. The equivalence of the source's six
conditions is in
`StacksFrontier.AlgebraicGeometry.Flatness.FinitelyPresented.FreeMapSpreadingOut`
(`Module.flat_localizedModule_freeMap_tfae`), together with each of its implications
separately — among them the spreading out
`Module.exists_universallyInjective_and_flat_coker_of_flat_localizedModule`, which is the one
step that is not a formal consequence of the local-base Stacks Tag 05I3
(`Module.flat_localizedModule_tfae`).

## References

* [Stacks Project, Tag 05IA](https://stacks.math.columbia.edu/tag/05IA)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

/-- For a flat `D`-algebra `C` the kernel of the base change of an algebra map is the extension
of its kernel. -/
public theorem Algebra.ker_map_id_of_flat {D C N P : Type*} [CommRing D] [CommRing C]
    [CommRing N] [CommRing P] [Algebra D C] [Algebra D N] [Algebra D P] [Module.Flat D C]
    (f : N →ₐ[D] P) :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id D C) f) =
      (RingHom.ker f).map (Algebra.TensorProduct.includeRight : N →ₐ[D] C ⊗[D] N) := by
  rw [← Submodule.restrictScalars_inj D]
  change LinearMap.ker
    (TensorProduct.AlgebraTensorModule.lTensor D C f.toLinearMap) = _
  rw [Module.Flat.ker_lTensor_eq, Ideal.map_includeRight_eq]
  rfl

/-- For a flat `D`-algebra `C` the kernel of `C → C ⊗[D] N` is the extension to `C` of the
kernel of `D → N`. -/
public theorem Algebra.ker_algebraMap_tensorProduct_left (D C N : Type*) [CommRing D]
    [CommRing C] [CommRing N] [Algebra D C] [Algebra D N] [Module.Flat D C] :
    RingHom.ker (algebraMap C (C ⊗[D] N)) =
      (RingHom.ker (algebraMap D N)).map (algebraMap D C) := by
  let e := Algebra.TensorProduct.rid D C C
  have he : (algebraMap C (C ⊗[D] N)).comp e.toRingHom =
      (Algebra.TensorProduct.map (AlgHom.id D C) (Algebra.ofId D N)).toRingHom := by
    refine RingHom.ext fun x ↦ ?_
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul x y =>
      change (y • x) ⊗ₜ[D] (1 : N) = x ⊗ₜ[D] algebraMap D N y
      rw [TensorProduct.smul_tmul]
      simp [Algebra.smul_def]
  have h := Algebra.ker_map_id_of_flat (C := C) (Algebra.ofId D N)
  change RingHom.ker (Algebra.TensorProduct.map (AlgHom.id D C)
    (Algebra.ofId D N)).toRingHom = _ at h
  rw [← he, ← RingHom.comap_ker] at h
  have hh := congrArg (Ideal.map e.toRingHom) h
  rw [Ideal.map_comap_of_surjective e.toRingHom e.surjective] at hh
  change RingHom.ker (algebraMap C (C ⊗[D] N)) =
    Ideal.map e.toRingHom
      ((RingHom.ker (algebraMap D N)).map
        (Algebra.TensorProduct.includeRight : D →ₐ[D] C ⊗[D] D).toRingHom) at hh
  rw [Ideal.map_map] at hh
  have hcomp : e.toRingHom.comp
      (Algebra.TensorProduct.includeRight : D →ₐ[D] C ⊗[D] D).toRingHom = algebraMap D C := by
    ext x
    simp [e, Algebra.smul_def]
  simpa only [hcomp] using hh

/-- **The generic point of a geometrically integral fibre.** If `R → S` is flat and the fibre
of `S` over a prime `r` is a geometrically integral `κ(r)`-algebra, then the extension `rS` is a
prime ideal of `S`. -/
public theorem Ideal.isPrime_map_of_flat_of_isGeometricallyIntegral {R S : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S] (r : Ideal R) [r.IsPrime]
    (hgeom : Algebra.IsGeometricallyIntegral r.ResidueField (r.Fiber S)) :
    (r.map (algebraMap R S)).IsPrime := by
  have ht : IsDomain (r.Fiber S ⊗[r.ResidueField] r.ResidueField) :=
    (Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct r.ResidueField
      (r.Fiber S)).mp hgeom r.ResidueField
  have _ : IsDomain (r.Fiber S) :=
    (Algebra.TensorProduct.rid r.ResidueField r.ResidueField
      (r.Fiber S)).symm.toRingEquiv.injective.isDomain _
  have hker : RingHom.ker
      (Algebra.TensorProduct.includeRight : S →ₐ[R] r.Fiber S).toRingHom =
      r.map (algebraMap R S) := by
    let e := Algebra.TensorProduct.comm R r.ResidueField S
    have hk : RingHom.ker (algebraMap S (S ⊗[R] r.ResidueField)) = r.map (algebraMap R S) := by
      rw [Algebra.ker_algebraMap_tensorProduct_left, Ideal.ker_algebraMap_residueField]
    ext x
    rw [← hk, RingHom.mem_ker, RingHom.mem_ker, ← map_eq_zero_iff e e.injective]
    simp [e]
  rw [← hker]
  exact RingHom.ker_isPrime _

/-- **Stacks Project, Tag 05IA, the existence assertion.** Let `R → S` be flat with a
geometrically integral fibre over the prime `r`, and let `N` be a finite `S`-module. Then the
extension `𝔭 = rS` is prime and some map from a finite free `S`-module to `N` becomes an
isomorphism after base change to the residue field `κ(𝔭)`. -/
@[stacks 05IA "existence"]
public theorem Module.exists_freeMap_bijective_residueField {R S N : Type u} [CommRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S] {r : Ideal R} [r.IsPrime] [AddCommGroup N]
    [Module S N] [Module.Finite S N]
    (hgeom : Algebra.IsGeometricallyIntegral r.ResidueField (r.Fiber S)) :
    ∃ (n : ℕ) (a : (Fin n → S) →ₗ[S] N),
      ∃ hp : (r.map (algebraMap R S)).IsPrime,
        Function.Bijective
          (a.rTensor (@Ideal.ResidueField S _ (r.map (algebraMap R S)) hp)) := by
  have hp := Ideal.isPrime_map_of_flat_of_isGeometricallyIntegral r hgeom
  obtain ⟨n, a, ha⟩ := Module.freeMapAtResidueField S (r.map (algebraMap R S)) N
  exact ⟨n, a, hp, ha⟩
