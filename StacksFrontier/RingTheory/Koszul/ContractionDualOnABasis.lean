module

public import StacksFrontier.RingTheory.Koszul.ContractionDeterminant

/-!
# Recognising the duality pairing from its values on a basis

`Koszul.bijective_of_listContractionDual` recognises a linear map
`⋀ⁿ(E^∨) ⟶ (⋀ⁿ E)^∨` as the duality pairing, hence as bijective, from its values on **every**
wedge of linear forms. A local computation does not produce that: it produces the values on the
wedges of the forms of one chosen basis — for a free module `Rⁱ`, on the wedges of the coordinate
projections. This file closes the gap.

What makes it close with no new input is that the hypothesis of
`Koszul.bijective_of_listContractionDual` is, by `Koszul.pairingDual_ιMulti`, the assertion that
the map agrees with `exteriorPower.pairingDual` on wedges — and both sides of *that* are
multilinear in the family of forms, being a linear map composed with `exteriorPower.ιMulti`. Two
multilinear maps agreeing on tuples of basis vectors are equal, by
`Module.Basis.ext_multilinear`. So agreement on the wedges of a basis of `E^∨` propagates to all
wedges on its own.

In particular **no multilinearity of `Koszul.listContraction` in its list entries is needed.** One
might expect to need it: iterated contraction is visibly multilinear in the contracting forms, and
the family `List.ofFn f` varies with `f`. But `Koszul.pairingDual_ιMulti` already holds for every
family, so the iterated contraction can be replaced by the pairing before any multilinearity is
invoked, and the multilinearity actually used is that of `exteriorPower.ιMulti`, which is part of
its definition as an alternating map.

## Main results

* `Koszul.eq_pairingDual_of_basis`: a linear map agreeing with iterated contraction on the wedges
  of a basis of `E^∨` is the duality pairing.
* `Koszul.bijective_of_listContractionDual_basis`: **hence it is bijective**, for `E` finite free.
* `Koszul.dualBasis_basisFun_eq_proj`: the dual basis of the standard basis of `ι → R` is the
  family of coordinate projections.
* `Koszul.bijective_of_listContractionDual_proj`: **the form a local computation produces** —
  bijectivity from the values on wedges of coordinate projections of a free module `Rⁱ`.
* `Koszul.linearMap_ext_of_single` and `Koszul.dual_ext_of_single`: a linear map out of `⋀ⁿ(Rⁱ)`,
  in particular a functional, is determined by its values on the wedges of standard basis
  vectors — which is how the hypothesis of the previous item is checked, both of its sides being
  such maps.

## Implementation notes

**The basis used is a basis of the dual, and it is taken to be a dual basis.** The hypothesis
quantifies over families `Fin n → ι` of indices, not over strictly monotone ones: `ext_multilinear`
needs every tuple of basis vectors, including repeats, and on a repeat both sides vanish for their
own reasons — the left by the alternating property of `ιMulti`, the right by
`Koszul.listContraction_eq_zero_of_adjacent_eq`. Nothing has to be said about that here, since
both sides are evaluated through the same `ιMulti`.

**The coordinate form is the one that is consumed.** The stalk computation of Stacks 0BQY produces
iterated contractions by coordinate projections, which is what
`SheafOfModules.TensorExteriorSymmetricAlgebras.listContractionDual_exteriorKoszulStalkEquiv`
states; `Koszul.bijective_of_listContractionDual_proj` is stated to match it, and
`Koszul.dualBasis_basisFun_eq_proj` is what identifies the two spellings of a coordinate form.

## References

* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public section

open scoped ExteriorAlgebra

namespace Koszul

universe u v

variable {R : Type u} [CommRing R] {E : Type v} [AddCommGroup E] [Module R E]

/-- Two linear maps out of an exterior power agreeing on the wedges of the families of basis
vectors agree on every wedge. -/
private theorem apply_ιMulti_eq_of_basis {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*}
    [Finite ι] (b : Module.Basis ι R M) (n : ℕ) {N : Type*} [AddCommGroup N] [Module R N]
    {f g : ⋀[R]^n M →ₗ[R] N}
    (h : ∀ v : Fin n → ι,
      f (exteriorPower.ιMulti R n fun k => b (v k)) = g (exteriorPower.ιMulti R n fun k => b (v k)))
    (u : Fin n → M) : f (exteriorPower.ιMulti R n u) = g (exteriorPower.ιMulti R n u) :=
  DFunLike.congr_fun (Module.Basis.ext_multilinear (f := (f.compAlternatingMap
    (exteriorPower.ιMulti R n)).toMultilinearMap) (g := (g.compAlternatingMap
    (exteriorPower.ιMulti R n)).toMultilinearMap) (fun _ => b) h) u

/-- **A linear map agreeing with iterated contraction on the wedges of a basis of `E^∨` is the
duality pairing.** By `Koszul.pairingDual_ιMulti` the hypothesis says that the map agrees with
`exteriorPower.pairingDual` on those wedges; both sides, read as functions of the family of forms,
are multilinear, being a linear map composed with the alternating map `exteriorPower.ιMulti`; and
two multilinear maps agreeing on tuples of basis vectors are equal. The agreement therefore holds
for every family, which is the hypothesis of `Koszul.eq_pairingDual`. -/
theorem eq_pairingDual_of_basis {ι : Type*} [Finite ι] (b : Module.Basis ι R (Module.Dual R E))
    (n : ℕ) (Φ : ⋀[R]^n (Module.Dual R E) →ₗ[R] Module.Dual R (⋀[R]^n E))
    (hΦ : ∀ v : Fin n → ι, Φ (exteriorPower.ιMulti R n fun k => b (v k)) =
      listContractionDual n (List.ofFn fun k => b (v k))) :
    Φ = exteriorPower.pairingDual R E n := by
  refine eq_pairingDual n Φ fun f => ?_
  have h := apply_ιMulti_eq_of_basis b n (g := exteriorPower.pairingDual R E n)
    (fun v => by simpa [pairingDual_ιMulti] using hΦ v) f
  simpa [pairingDual_ιMulti] using h

/-- **Bijectivity from the values on the wedges of a basis of the dual.** For `E` finite free, a
linear map `⋀ⁿ(E^∨) ⟶ (⋀ⁿ E)^∨` sending the wedge of any family of basis forms to the
corresponding iterated contraction is bijective.

This is the weakening of `Koszul.bijective_of_listContractionDual` that a local computation can
meet: the computation evaluates the map on wedges of one chosen basis of the dual, not on all
wedges. -/
theorem bijective_of_listContractionDual_basis [Module.Free R E] [Module.Finite R E]
    {ι : Type*} [Finite ι] (b : Module.Basis ι R (Module.Dual R E)) (n : ℕ)
    (Φ : ⋀[R]^n (Module.Dual R E) →ₗ[R] Module.Dual R (⋀[R]^n E))
    (hΦ : ∀ v : Fin n → ι, Φ (exteriorPower.ιMulti R n fun k => b (v k)) =
      listContractionDual n (List.ofFn fun k => b (v k))) :
    Function.Bijective Φ := by
  rw [eq_pairingDual_of_basis b n Φ hΦ]
  exact exteriorPower.bijective_pairingDual R E n

/-- **The dual basis of the standard basis of `ι → R` is the family of coordinate
projections.** -/
theorem dualBasis_basisFun_eq_proj {ι : Type*} [Finite ι] [DecidableEq ι] (i : ι) :
    (Pi.basisFun R ι).dualBasis i = LinearMap.proj i :=
  LinearMap.ext fun x => by
    simp [Module.Basis.coe_dualBasis, Module.Basis.coord_apply, Pi.basisFun_repr]

/-- **Bijectivity from the values on wedges of coordinate projections**, for the free module
`Rⁱ`. This is the form in which the stalk computation of Stacks 0BQY delivers its hypothesis: the
iterated contractions it produces are contractions by coordinate projections, and the coordinate
projections are the dual basis of the standard basis. -/
theorem bijective_of_listContractionDual_proj {ι : Type*} [Finite ι] (n : ℕ)
    (Φ : ⋀[R]^n (Module.Dual R (ι → R)) →ₗ[R] Module.Dual R (⋀[R]^n (ι → R)))
    (hΦ : ∀ v : Fin n → ι,
      Φ (exteriorPower.ιMulti R n fun k => (LinearMap.proj (v k) : Module.Dual R (ι → R))) =
        listContractionDual n
          (List.ofFn fun k => (LinearMap.proj (v k) : Module.Dual R (ι → R)))) :
    Function.Bijective Φ := by
  classical
  refine bijective_of_listContractionDual_basis (Pi.basisFun R ι).dualBasis n Φ fun v => ?_
  simpa only [dualBasis_basisFun_eq_proj] using hΦ v

/-- **A linear map out of the exterior power of a free module is determined by its values on the
wedges of standard basis vectors.** Two linear maps on `⋀ⁿ(Rⁱ)` agreeing on every wedge of standard
basis vectors are equal: a linear map out of an exterior power is determined by its values on all
wedges, by `exteriorPower.linearMap_ext`, and those values are multilinear in the family of
vectors, so `Module.Basis.ext_multilinear` propagates agreement from basis families to all
families. -/
theorem linearMap_ext_of_single {ι : Type*} [Finite ι] [DecidableEq ι] (n : ℕ)
    {N : Type*} [AddCommGroup N] [Module R N]
    {f g : (⋀[R]^n (ι → R)) →ₗ[R] N}
    (h : ∀ v : Fin n → ι,
      f (exteriorPower.ιMulti R n fun k => Pi.single (v k) (1 : R)) =
        g (exteriorPower.ιMulti R n fun k => Pi.single (v k) (1 : R))) :
    f = g := by
  exact exteriorPower.linearMap_ext (AlternatingMap.ext fun u =>
    apply_ιMulti_eq_of_basis (Pi.basisFun R ι) n
      (fun v => by simpa [Pi.basisFun_apply] using h v) u)

/-- **A functional on the exterior power of a free module is determined by its values on the
wedges of standard basis vectors.** The case of `linearMap_ext_of_single` with values in the base
ring, which is the one the recognition hypothesis of
`Koszul.bijective_of_listContractionDual_proj` is checked against. -/
theorem dual_ext_of_single {ι : Type*} [Finite ι] [DecidableEq ι] (n : ℕ)
    {f g : Module.Dual R (⋀[R]^n (ι → R))}
    (h : ∀ v : Fin n → ι,
      f (exteriorPower.ιMulti R n fun k => Pi.single (v k) (1 : R)) =
        g (exteriorPower.ιMulti R n fun k => Pi.single (v k) (1 : R))) :
    f = g :=
  linearMap_ext_of_single n h

/-- **Bijectivity from the values on wedges of coordinate projections, with the contracting
order reversed.** The form the local computation of Stacks 0BQY actually produces: the composition
product of the degree-one classes `c_{j₀}, …, c_{jᵢ}`, taken in that order, is the class of the
iterated contraction `δ_{jᵢ} ∘ ⋯ ∘ δ_{j₀}`, because a cochain of the internal endomorphism complex
composes its factors in the opposite order. So the wedge is indexed by `v` while the contraction
list is indexed by `v ∘ Fin.rev`.

That reversal is a genuine sign and not an artefact: reversing the list permutes the rows of the
Kronecker matrix whose determinant the pairing is. It is harmless, the sign being a unit — the map
differs from the duality pairing by `(-1)^{n(n-1)/2}`, which is invertible, so bijectivity is
unaffected. The proof multiplies by that sign, which is `Equiv.Perm.sign Fin.revPerm`: the
alternating property of `exteriorPower.ιMulti` (`AlternatingMap.map_perm`) moves the reversal from
the index family to the scalar, `Fin.rev_rev` cancels the two reversals, and
`Koszul.bijective_of_listContractionDual_proj` applies to the rescaled map. -/
theorem bijective_of_listContractionDual_proj_rev {ι : Type*} [Finite ι] (n : ℕ)
    (Φ : ⋀[R]^n (Module.Dual R (ι → R)) →ₗ[R] Module.Dual R (⋀[R]^n (ι → R)))
    (hΦ : ∀ v : Fin n → ι,
      Φ (exteriorPower.ιMulti R n fun k => (LinearMap.proj (v k) : Module.Dual R (ι → R))) =
        listContractionDual n
          (List.ofFn fun k => (LinearMap.proj (v k.rev) : Module.Dual R (ι → R)))) :
    Function.Bijective Φ := by
  have key : ∀ c : ℤ, c * c = 1 →
      (∀ v : Fin n → ι,
        exteriorPower.ιMulti R n (fun k => (LinearMap.proj (v k.rev) :
            Module.Dual R (ι → R))) =
          c • exteriorPower.ιMulti R n (fun k => (LinearMap.proj (v k) :
            Module.Dual R (ι → R)))) →
      Function.Bijective Φ := by
    intro c hc hperm
    have hb : Function.Bijective (c • Φ) := by
      refine bijective_of_listContractionDual_proj n (c • Φ) (fun v => ?_)
      refine Eq.trans (LinearMap.smul_apply c Φ _) ?_
      refine Eq.trans (map_zsmul Φ c _).symm ?_
      refine Eq.trans (congrArg Φ (hperm v).symm) ?_
      refine Eq.trans (hΦ (fun k => v k.rev)) ?_
      exact congrArg
        (fun g : Fin n → Module.Dual R (ι → R) => listContractionDual n (List.ofFn g))
        (funext fun k => congrArg (fun i : ι => (LinearMap.proj i : Module.Dual R (ι → R)))
          (congrArg v (Fin.rev_rev k)))
    have hunit : Function.Bijective
        (fun w : Module.Dual R (⋀[R]^n (ι → R)) => c • w) :=
      Function.bijective_iff_has_inverse.2
        ⟨fun w => c • w,
          fun w => by change c • c • w = w; rw [smul_smul, hc, one_smul],
          fun w => by change c • c • w = w; rw [smul_smul, hc, one_smul]⟩
    have heq : (Φ : ⋀[R]^n (Module.Dual R (ι → R)) → Module.Dual R (⋀[R]^n (ι → R))) =
        (fun w => c • w) ∘ (c • Φ) :=
      funext fun z => by
        rw [Function.comp_apply, LinearMap.smul_apply, smul_smul, hc, one_smul]
    rw [heq]
    exact hunit.comp hb
  refine key ((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) ?_ (fun v => ?_)
  · rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  · refine Eq.trans ((exteriorPower.ιMulti R n).map_perm
      (fun k => (LinearMap.proj (v k) : Module.Dual R (ι → R))) Fin.revPerm) ?_
    exact Units.smul_def _ _

/-! ### Transfer along a ring map -/

section Transfer

variable {S : Type*} [CommRing S]

/-- **The pairing of coordinate projections against standard basis wedges is transferred by any
ring map.** Both sides are the determinant of the Kronecker matrix of the two index families
(`Koszul.listContractionDual_ofFn_ιMulti`), whose entries are `0` and `1`, so a ring homomorphism
carries one determinant to the other: it commutes with `Matrix.det` and fixes `0` and `1`.

This is what moves the local computation of Stacks 0BQY from the stalk of `O♯` to the stalk of
`O_X`. The stalk computation produces an iterated contraction over the stalk of `O♯`; the
statement of the tag is about the exterior power formed over the stalk of `O_X`; and the two are
related by the stalk of the quotient map, which is a ring homomorphism and nothing more. -/
theorem listContractionDual_proj_single_map (g : R →+* S) {ι : Type*} [DecidableEq ι]
    (n : ℕ) (a b : Fin n → ι) :
    g (listContractionDual n
        (List.ofFn fun k => (LinearMap.proj (a k) : Module.Dual R (ι → R)))
        (exteriorPower.ιMulti R n fun k => Pi.single (b k) (1 : R))) =
      listContractionDual n
        (List.ofFn fun k => (LinearMap.proj (a k) : Module.Dual S (ι → S)))
        (exteriorPower.ιMulti S n fun k => Pi.single (b k) (1 : S)) := by
  rw [listContractionDual_ofFn_ιMulti, listContractionDual_ofFn_ιMulti, RingHom.map_det]
  refine congrArg Matrix.det (Matrix.ext fun p q => ?_)
  simp [Pi.single_apply, apply_ite g]

end Transfer

end Koszul

end
