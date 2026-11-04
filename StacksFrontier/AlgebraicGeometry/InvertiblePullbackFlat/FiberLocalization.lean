module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.SurjectiveOnStalks
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.Stalks
import StacksCore.Tactic.StacksAttribute

/-!
# Fibre rings under localization of the base and of the algebra

The penultimate paragraph of Stacks Tag 0BD7 is applied in the source to
`Spec 𝒪_{X, x} → Spec 𝒪_{Y, y}`, and
`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/StalkGenerator.lean` reduces its primality
hypothesis to *every fibre ring `Ideal.Fiber 𝔭 𝒪_{X, x}` is a domain*, for `𝔭` an arbitrary
prime of `𝒪_{Y, y}`. The geometry supplies that only on an affine chart: for affine opens
`x ∈ U = Spec S` of `X` over `y ∈ V = Spec T` of `Y`, the fibre of `f|_U` over the point `𝔮` of
`V` corresponding to `𝔭` is `Spec (Ideal.Fiber 𝔮 S)`
(`AlgebraicGeometry.fiberIsoSpecFiberRing`), and that ring is a domain because the fibre
`X_{y'}` is integral.

This file crosses the two descriptions. Both the base and the algebra are localized between
them — `𝒪_{Y, y}` is a localization of `T` and `𝒪_{X, x}` is a localization of `S` — and the
two localizations are handled separately.

* Localizing the **algebra** is Mathlib's `IsLocalization.tensorProduct_tensorProduct_right`:
  `κ(𝔮) ⊗_T S` localized at the image of a submonoid `M` of `S` is `κ(𝔮) ⊗_T S_M`. A
  localization of a domain is a domain as soon as it is not the zero ring, which is where
  nontriviality of the fibre enters.
* Localizing the **base** does not change the fibre at all:
  `Ideal.fiberComapRingEquivOfIsLocalization` identifies `Ideal.Fiber 𝔭 A` over a localization
  `R` of `T` with `Ideal.Fiber (𝔭 ∩ T) A` over `T`. Two inputs: the residue field is unchanged
  (`RingHom.SurjectiveOnStalks.residueFieldMap_bijective`, a localization being surjective on
  stalks), and `R ⊗_T A = A` for an algebra `A` that is already an `R`-algebra
  (`IsLocalization.baseTensorAlgEquiv`).

Nontriviality is the remaining input, and for the stalks of a flat morphism it is free: the map
on local rings is faithfully flat (`AlgebraicGeometry.Flat.faithfullyFlat_stalkMap`), and a
faithfully flat algebra tensored with a nonzero module is nonzero. Geometrically this is
surjectivity of `Spec 𝒪_{X, x} → Spec 𝒪_{Y, y}`: every fibre of that map is nonempty.

## Main results

* `Algebra.TensorProduct.tmul_one_eq_one_tmul_algebraMap_of_isLocalization`: in `R ⊗_T A` for
  `R` a localization of `T` and `A` an `R`-algebra, `x ⊗ 1 = 1 ⊗ x`.
* `IsLocalization.baseTensorAlgEquiv`: `A ≃ₐ[R] R ⊗_T A` for such an `A`, and
  `IsLocalization.baseTensorAlgEquiv_apply`: it sends `a` to `1 ⊗ a`.
* `Ideal.residueFieldComapAlgEquivOfIsLocalization`: the residue field of a prime of a
  localization is the residue field of its contraction.
* `Ideal.fiberComapRingEquivOfIsLocalization`: the fibre ring is unchanged by localizing the
  base, and `Ideal.fiberComapRingEquivOfIsLocalization_one_tmul`: that identification fixes
  `1 ⊗ a`.
* `Ideal.nontrivial_fiber_of_nontrivial_fiber`: a fibre ring is nonzero as soon as the fibre ring
  of a further algebra over it is.
* `Ideal.isDomain_fiber_of_isLocalization`: the fibre ring of a localization of `A` is a domain
  if the fibre ring of `A` is a domain and it is nonzero.
* `Ideal.isDomain_fiber_of_isDomain_fiber_of_isLocalization`: the two steps combined — for `R` a
  localization of `T` and `A` a localization of a `T`-algebra `S`, a prime `𝔭` of `R` with
  contraction `𝔮` in `T`, the fibre `Ideal.Fiber 𝔭 A` is a domain as soon as
  `Ideal.Fiber 𝔮 S` is a domain and `Ideal.Fiber 𝔭 A` is nonzero.
* `Ideal.forall_isDomain_fiber_of_forall_isDomain_fiber_of_isLocalization`: the same for *every*
  prime at once, with both nonvanishing hypotheses discharged by faithful flatness — the exact
  hypothesis of `Ideal.exists_isUnit_mul_eq_of_isDomain_fiber`. The hypothesis on `S` is asked
  only at the primes where the fibre ring of `S` is nonzero.
* `Ideal.surjective_comap_of_forall_isDomain_fiber`: asking the fibre ring of `T → S` to be a
  domain at *every* prime of `T` forces `Spec S → Spec T` to be surjective.
* `Ideal.isDomain_fiber_localizationAway_of_nontrivial` and
  `Ideal.not_isDomain_fiber_localizationAway_of_mem`: on a standard affine open `Spec T_t` the
  guarded hypothesis is automatic and the unguarded one is false.
* `Ideal.isDomain_fiberBot_of_isDomain_fiberBot_of_isLocalization`: the `𝔭 = ⊥` case, which is
  the ring `A ⊗_R K` of Stacks Tag 0BD7.
* `AlgebraicGeometry.nontrivial_fiber_stalkMap_of_flat`: every fibre ring of the map of local
  rings induced by a flat morphism is nonzero.

## Implementation notes

**Why the `∀`-form asks for a domain only where the fibre ring is nonzero.** The unguarded
hypothesis *every fibre ring `Ideal.Fiber 𝔮 S` is a domain, for every prime `𝔮` of `T`* is not a
hypothesis a chart can satisfy, and not because it is hard to prove: it is false. `IsDomain`
contains `Nontrivial`, so the unguarded form says in particular that `κ(𝔮) ⊗_T S ≠ 0` for every
prime `𝔮`, which is surjectivity of `Spec S → Spec T`
(`Ideal.surjective_comap_of_forall_isDomain_fiber`). For `T = Γ(Y, V)` and `S = Γ(X, U)` that is
the demand that the fibre of `φ` through every point of `V` meet the affine open `U`, which the
hypotheses of Stacks Tag 0BD7 do not give and which fails for the standard open `Spec T_t` of
`Spec T` at any prime containing `t` (`Ideal.not_isDomain_fiber_localizationAway_of_mem`) —
while the guarded hypothesis holds on that same open with no hypothesis on `T` whatever
(`Ideal.isDomain_fiber_localizationAway_of_nontrivial`).

Guarding the hypothesis by `Nontrivial (Ideal.Fiber 𝔮 S)` costs nothing, because that
nonvanishing is already available: faithful flatness of `R → A` gives
`Nontrivial (Ideal.Fiber 𝔭 A)`, `Ideal.fiberComapRingEquivOfIsLocalization` carries it to the
contraction `𝔮`, and `Ideal.nontrivial_fiber_of_nontrivial_fiber` descends it from `A` to `S`.
The guarded form is exactly what
`AlgebraicGeometry.isDomain_fiber_appLE_of_isIntegral_fiber` proves — integrality of the fibre
*plus* nonvanishing — so the chart feeds it with no further work.

The contracted prime is an explicit argument of
`Ideal.isDomain_fiber_of_isDomain_fiber_of_isLocalization` together with its own equation
`p.comap (algebraMap T R) = q`, rather than being written `p.comap (algebraMap T R)` in place.
The hypothesis `[q.IsPrime]` depends on `q`, so a consumer that has its own name for the
contraction cannot `rw` the equation into the statement — `rw` fails with *motive is not type
correct* on exactly that instance argument. With the equation supplied the proof substitutes it
instead. This also makes the `⊥` case a one-line specialization, since
`(⊥ : Ideal R).comap (algebraMap T R) = ⊥` is `Ideal.comap_bot_of_injective`; that
specialization is recorded as
`Ideal.isDomain_fiberBot_of_isDomain_fiberBot_of_isLocalization`, because
`Ideal.fiberBotRingEquivOfIsLocalization` makes `Ideal.Fiber ⊥ 𝒪_{X, x}` the ring in which
assumption (5) of Stacks Tag 0BD7 lives.

`Algebra.TensorProduct.rightAlgebra` is not a global instance, so the declaration that needs the
`A`-algebra structure on a tensor product introduces it locally. The `κ(𝔭) ⊗_R A`-algebra
structure on `κ(𝔭) ⊗_R B` inside `Ideal.isDomain_fiber_of_isLocalization` is
`Algebra.TensorProduct.lTensor` of the localization map — the library's own bundled form, which
also makes its scalar tower `IsScalarTower.of_algHom` rather than a computation. The same
construction is already present, `private` and in another chapter's namespace, as
`Proof_T_00PK.toFiberLocalization` and `Proof_T_00PK.fiberLocalizationAlgebra`
(`StacksFrontier/RingTheory/QuasiFinite/Basic.lean`), which does not state the `IsLocalization`
property; collapsing the two is a cross-file move.

The chart itself — affine opens `x ∈ U` over `y ∈ V` with `f(U) ⊆ V`, and the identification of
`Ideal.Fiber 𝔮 Γ(X, U)` with the ring of the affine open `X_{y'} ∩ U` of the integral fibre — is
`FiberChart.lean`, which consumes the `∀`-form below. Nothing here states a clause of Tag 0BD7:
every statement is about `Ideal.Fiber` and carries hypotheses the tag does not, so the attribute
for tag 0BD7 is withheld from all of them.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
-/

@[expose] public section

universe u

open Algebra TensorProduct

namespace Algebra.TensorProduct

/-- **In `R ⊗_T A` the two copies of an element of `R` agree**, when `R` is a localization of
`T` and `A` is already an `R`-algebra: `x ⊗ 1 = 1 ⊗ x`.

Over `T` alone this is false; it holds here because `x = t/n` with `n ∈ T`, and multiplying both
sides by the image of `n` — a unit of `R ⊗_T A`, since it is a unit of `R` — turns both into
`1 ⊗ t`, where `t` lies in `T` and crosses the tensor sign freely. -/
theorem tmul_one_eq_one_tmul_algebraMap_of_isLocalization
    {T R A : Type u} [CommRing T] [CommRing R] [CommRing A]
    [Algebra T R] [Algebra R A] [Algebra T A] [IsScalarTower T R A]
    (N : Submonoid T) [IsLocalization N R] (x : R) :
    (x ⊗ₜ[T] (1 : A)) = (1 : R) ⊗ₜ[T] algebraMap R A x := by
  have hmap : ∀ s : T, (algebraMap T R s) ⊗ₜ[T] (1 : A)
      = (1 : R) ⊗ₜ[T] algebraMap T A s := fun s => by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_tmul]
  obtain ⟨⟨t, n⟩, rfl⟩ := IsLocalization.mk'_surjective N x
  have hu : IsUnit ((algebraMap T R n) ⊗ₜ[T] (1 : A)) :=
    (IsLocalization.map_units R n).map (algebraMap R (R ⊗[T] A))
  refine hu.mul_left_cancel ?_
  rw [tmul_mul_tmul, mul_one, IsLocalization.mk'_spec', hmap n, tmul_mul_tmul, one_mul,
    IsScalarTower.algebraMap_apply T R A (n : T), ← map_mul, IsLocalization.mk'_spec',
    ← IsScalarTower.algebraMap_apply T R A, hmap t]

end Algebra.TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Base change along a localization is trivial on algebras that already live over it.** For
`R` a localization of `T` at `N` and `A` an `R`-algebra, `R ⊗_T A` is the localization of `A` at
the image of `N` (`IsLocalization.tensorRight`), and that image consists of units of `A`, so the
localization map is an isomorphism. It is `R`-linear by
`Algebra.TensorProduct.tmul_one_eq_one_tmul_algebraMap_of_isLocalization`. -/
noncomputable def IsLocalization.baseTensorAlgEquiv
    {T R A : Type u} [CommRing T] [CommRing R] [CommRing A]
    [Algebra T R] [Algebra R A] [Algebra T A] [IsScalarTower T R A]
    (N : Submonoid T) [IsLocalization N R] : A ≃ₐ[R] R ⊗[T] A := by
  have hN : Algebra.algebraMapSubmonoid A N ≤ IsUnit.submonoid A := by
    rintro a ⟨n, hn, rfl⟩
    change IsUnit _
    rw [IsScalarTower.algebraMap_apply T R A n]
    exact (IsLocalization.map_units R (⟨n, hn⟩ : N)).map (algebraMap R A)
  have h₁ : IsLocalization (Algebra.algebraMapSubmonoid A N) A := IsLocalization.self hN
  have h₂ : IsLocalization (Algebra.algebraMapSubmonoid A N) (R ⊗[T] A) :=
    IsLocalization.tensorRight (R := T) (S := A) (A := R) N
  let ε : A ≃ₐ[A] R ⊗[T] A := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid A N) A _
  have hε : ∀ a : A, ε a = (1 : R) ⊗ₜ[T] a := fun a => ε.commutes a
  exact
    { toFun := ε
      invFun := ε.symm
      left_inv := ε.left_inv
      right_inv := ε.right_inv
      map_mul' := ε.map_mul
      map_add' := ε.map_add
      commutes' := fun x => by
        rw [hε]
        exact (Algebra.TensorProduct.tmul_one_eq_one_tmul_algebraMap_of_isLocalization
          N x).symm }

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **The identification `A = R ⊗_T A` sends `a` to `1 ⊗ a`.** -/
theorem IsLocalization.baseTensorAlgEquiv_apply
    {T R A : Type u} [CommRing T] [CommRing R] [CommRing A]
    [Algebra T R] [Algebra R A] [Algebra T A] [IsScalarTower T R A]
    (N : Submonoid T) [IsLocalization N R] (a : A) :
    IsLocalization.baseTensorAlgEquiv (A := A) N a = (1 : R) ⊗ₜ[T] a := by
  simp only [IsLocalization.baseTensorAlgEquiv]
  exact AlgEquiv.commutes _ a

namespace Ideal

/-- **The residue field at a prime of a localization is the residue field of its
contraction.** The map `κ(𝔭 ∩ T) → κ(𝔭)` is always injective, and it is surjective because a
localization is surjective on stalks. -/
noncomputable def residueFieldComapAlgEquivOfIsLocalization
    {T R : Type u} [CommRing T] [CommRing R] [Algebra T R]
    (N : Submonoid T) [IsLocalization N R] (p : Ideal R) [p.IsPrime] :
    (p.comap (algebraMap T R)).ResidueField ≃ₐ[T] p.ResidueField :=
  AlgEquiv.ofBijective
    (Ideal.ResidueField.mapₐ (R := T) (p.comap (algebraMap T R)) p (Algebra.ofId T R) rfl)
    ((RingHom.surjectiveOnStalks_of_isLocalization (M := N) R).residueFieldMap_bijective
      (p.comap (algebraMap T R)) p rfl)

/-- **The fibre ring does not see a localization of the base.** For `R` a localization of `T`
and `A` an `R`-algebra, `κ(𝔭) ⊗_R A = κ(𝔭 ∩ T) ⊗_T A`: the residue fields agree
(`Ideal.residueFieldComapAlgEquivOfIsLocalization`) and the two base rings give the same tensor
product, because `R ⊗_T A = A` (`IsLocalization.baseTensorAlgEquiv`) and
`Algebra.TensorProduct.cancelBaseChange` cancels the intermediate base change. -/
noncomputable def fiberComapRingEquivOfIsLocalization
    {T R A : Type u} [CommRing T] [CommRing R] [CommRing A]
    [Algebra T R] [Algebra R A] [Algebra T A] [IsScalarTower T R A]
    (N : Submonoid T) [IsLocalization N R] (p : Ideal R) [p.IsPrime] :
    (p.comap (algebraMap T R)).Fiber A ≃+* p.Fiber A :=
  let e₁ : p.ResidueField ⊗[R] A ≃ₐ[R] p.ResidueField ⊗[R] (R ⊗[T] A) :=
    Algebra.TensorProduct.congr AlgEquiv.refl (IsLocalization.baseTensorAlgEquiv N)
  let e₂ : p.ResidueField ⊗[R] (R ⊗[T] A) ≃ₐ[R] p.ResidueField ⊗[T] A :=
    Algebra.TensorProduct.cancelBaseChange T R R p.ResidueField A
  let e₃ : (p.comap (algebraMap T R)).ResidueField ⊗[T] A ≃ₐ[T] p.ResidueField ⊗[T] A :=
    Algebra.TensorProduct.congr (residueFieldComapAlgEquivOfIsLocalization N p) AlgEquiv.refl
  e₃.toRingEquiv.trans (e₂.toRingEquiv.symm.trans e₁.toRingEquiv.symm)

/-- **The identification of the two fibre rings is the identity on `1 ⊗ a`.** All three
isomorphisms it is built from fix such an element, so the only content is bookkeeping; it is
recorded because `1 ⊗ a` is the image of `A` in the fibre ring, and a ring map out of the fibre
ring is determined by what it does there. -/
theorem fiberComapRingEquivOfIsLocalization_one_tmul
    {T R A : Type u} [CommRing T] [CommRing R] [CommRing A]
    [Algebra T R] [Algebra R A] [Algebra T A] [IsScalarTower T R A]
    (N : Submonoid T) [IsLocalization N R] (p : Ideal R) [p.IsPrime] (a : A) :
    fiberComapRingEquivOfIsLocalization N p
        ((1 : (p.comap (algebraMap T R)).ResidueField) ⊗ₜ[T] a)
      = (1 : p.ResidueField) ⊗ₜ[R] a := by
  refine ((RingEquiv.symm_apply_eq _).mp ?_).symm
  simp [fiberComapRingEquivOfIsLocalization, IsLocalization.baseTensorAlgEquiv_apply,
    Algebra.TensorProduct.cancelBaseChange_tmul]

/-- **A fibre ring is nonzero as soon as the fibre ring of a further algebra is.** The map
`κ(𝔮) ⊗_R S → κ(𝔮) ⊗_R A` induced by `S → A` is a ring homomorphism, and a ring that maps to a
nonzero ring is nonzero. Geometrically: if the fibre of `Spec A → Spec R` over `𝔮` is nonempty
then so is the fibre of `Spec S → Spec R`, since the first maps to the second. -/
theorem nontrivial_fiber_of_nontrivial_fiber {R S A : Type u} [CommRing R] [CommRing S]
    [CommRing A] [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
    (q : Ideal R) [q.IsPrime] (h : Nontrivial (q.Fiber A)) : Nontrivial (q.Fiber S) :=
  (Algebra.TensorProduct.lTensor (R := R) (S := R) q.ResidueField
    (IsScalarTower.toAlgHom R S A)).toRingHom.domain_nontrivial

/-- **The fibre ring of a localization of `A` is a domain when the fibre ring of `A` is.**
`κ(𝔭) ⊗_R A_M` is the localization of `κ(𝔭) ⊗_R A` at the image of `M`
(`IsLocalization.tensorProduct_tensorProduct_right`), and a localization of a domain is a domain
as soon as it is nonzero: nonzero forces `0` out of the multiplicative set, which in a domain is
exactly the condition that the set consists of nonzerodivisors. -/
theorem isDomain_fiber_of_isLocalization {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    (M : Submonoid A) [IsLocalization M B] (p : Ideal R) [p.IsPrime]
    (hdom : IsDomain (p.Fiber A)) (hnt : Nontrivial (p.Fiber B)) : IsDomain (p.Fiber B) := by
  let φ : p.Fiber A →ₐ[p.ResidueField] p.Fiber B :=
    Algebra.TensorProduct.lTensor _ (IsScalarTower.toAlgHom R A B)
  let _ : Algebra (p.Fiber A) (p.Fiber B) := φ.toRingHom.toAlgebra
  have _ : IsScalarTower p.ResidueField (p.Fiber A) (p.Fiber B) := IsScalarTower.of_algHom φ
  have hloc : IsLocalization
      (M.map (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField)))
      (p.Fiber B) :=
    IsLocalization.tensorProduct_tensorProduct_right R p.ResidueField M B
      (by ext; simp [RingHom.algebraMap_toAlgebra, φ])
  have hle : (M.map (Algebra.TensorProduct.includeRight (R := R) (A := p.ResidueField)))
      ≤ nonZeroDivisors (p.Fiber A) := by
    intro z hz
    refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
    have hun : IsUnit (algebraMap (p.Fiber A) (p.Fiber B) z) :=
      IsLocalization.map_units _ ⟨z, hz⟩
    rw [h0, map_zero, isUnit_zero_iff] at hun
    exact zero_ne_one hun
  exact IsLocalization.isDomain_of_le_nonZeroDivisors _ hle

/-- **The fibre ring over a localized base, from the fibre ring on a chart.** Let `R` be a
localization of `T`, let `A` be a localization of a `T`-algebra `S` and an `R`-algebra
compatibly, let `𝔭` be a prime of `R` and `𝔮` its contraction to `T`. Then `Ideal.Fiber 𝔭 A` is
a domain as soon as `Ideal.Fiber 𝔮 S` is a domain and `Ideal.Fiber 𝔭 A` is nonzero.

For `T = Γ(V, ⊤)`, `S = Γ(U, ⊤)`, `R = 𝒪_{Y, y}` and `A = 𝒪_{X, x}` this is the crossing that
obstruction (i) of Stacks Tag 0BD7 needs: the domain hypothesis is integrality of the fibre
`X_{y'}` read on the affine chart `U`, and the nonvanishing hypothesis is
`AlgebraicGeometry.nontrivial_fiber_stalkMap_of_flat`. -/
theorem isDomain_fiber_of_isDomain_fiber_of_isLocalization
    {T S R A : Type u} [CommRing T] [CommRing S] [CommRing R] [CommRing A]
    [Algebra T S] [Algebra T R] [Algebra R A] [Algebra T A] [Algebra S A]
    [IsScalarTower T R A] [IsScalarTower T S A]
    (N : Submonoid T) [IsLocalization N R] (M : Submonoid S) [IsLocalization M A]
    (p : Ideal R) [p.IsPrime] (q : Ideal T) [q.IsPrime]
    (hq : p.comap (algebraMap T R) = q)
    (hdom : IsDomain (q.Fiber S)) (hnt : Nontrivial (p.Fiber A)) :
    IsDomain (p.Fiber A) := by
  subst hq
  have e := fiberComapRingEquivOfIsLocalization (A := A) N p
  have := isDomain_fiber_of_isLocalization M (p.comap (algebraMap T R)) hdom e.toEquiv.nontrivial
  exact e.symm.toMulEquiv.isDomain _

/-- **The hypothesis of `Ideal.exists_isUnit_mul_eq_of_isDomain_fiber`, from the same hypothesis
on a chart.** If every *nonzero* fibre ring of `T → S` is a domain and `A` is faithfully flat
over `R`, then every fibre ring of `R → A` is a domain. Both nonvanishing hypotheses — the one of
`Ideal.isDomain_fiber_of_isDomain_fiber_of_isLocalization` at `𝔭` and the guard on the hypothesis
at `𝔮` — are discharged by faithful flatness, so this form carries no hypothesis about `A` beyond
the standing ones.

This is the statement `Ideal.exists_isUnit_mul_eq_of_isDomain_fiber` asks for, at
`R = 𝒪_{Y, y}` and `A = 𝒪_{X, x}`: with `T = Γ(Y, V)` and `S = Γ(X, U)` for affine opens
`x ∈ U ≤ φ ⁻¹ᵁ V`, the hypothesis is
`AlgebraicGeometry.isDomain_fiber_appLE_of_isIntegral_fiber` verbatim.

**The guard is not a convenience.** Without it the hypothesis is false rather than unproved: it
asserts `κ(𝔮) ⊗_T S ≠ 0` for every prime `𝔮` of `T`, hence surjectivity of `Spec S → Spec T`
(`Ideal.surjective_comap_of_forall_isDomain_fiber`), which no chart of a morphism satisfying the
hypotheses of Stacks Tag 0BD7 has to have
(`Ideal.not_isDomain_fiber_localizationAway_of_mem`). -/
theorem forall_isDomain_fiber_of_forall_isDomain_fiber_of_isLocalization
    {T S R A : Type u} [CommRing T] [CommRing S] [CommRing R] [CommRing A]
    [Algebra T S] [Algebra T R] [Algebra R A] [Algebra T A] [Algebra S A]
    [IsScalarTower T R A] [IsScalarTower T S A] [Module.FaithfullyFlat R A]
    (N : Submonoid T) [IsLocalization N R] (M : Submonoid S) [IsLocalization M A]
    (hdom : ∀ q : Ideal T, ∀ _ : q.IsPrime, Nontrivial (q.Fiber S) → IsDomain (q.Fiber S)) :
    ∀ p : Ideal R, ∀ _ : p.IsPrime, IsDomain (p.Fiber A) :=
  fun p _ => isDomain_fiber_of_isDomain_fiber_of_isLocalization N M p _ rfl
    (hdom _ inferInstance (nontrivial_fiber_of_nontrivial_fiber _
      (fiberComapRingEquivOfIsLocalization (A := A) N p).toEquiv.nontrivial)) inferInstance

/-- **Asking for a domain at every prime is asking for surjectivity.** If `Ideal.Fiber 𝔮 S` is a
domain for every prime `𝔮` of `T` then `Spec S → Spec T` is surjective: a domain is in
particular nonzero, so its spectrum is nonempty, and
`PrimeSpectrum.preimageEquivFiber` identifies that spectrum with the set-theoretic fibre of
`Spec S → Spec T` over `𝔮`.

This is what makes the unguarded hypothesis of
`Ideal.forall_isDomain_fiber_of_forall_isDomain_fiber_of_isLocalization` false rather than
merely unproved on a chart: it carries a geometric conclusion about the pair `T → S` that is not
part of the data. -/
theorem surjective_comap_of_forall_isDomain_fiber {T S : Type u} [CommRing T] [CommRing S]
    [Algebra T S] (hdom : ∀ q : Ideal T, ∀ _ : q.IsPrime, IsDomain (q.Fiber S)) :
    Function.Surjective (PrimeSpectrum.comap (algebraMap T S)) := by
  intro q
  have _ := hdom q.asIdeal q.isPrime
  obtain ⟨z⟩ : Nonempty (PrimeSpectrum (q.asIdeal.Fiber S)) :=
    PrimeSpectrum.nonempty_iff_nontrivial.2 inferInstance
  exact ⟨_, ((PrimeSpectrum.preimageEquivFiber T S q).symm z).2⟩

/-- **The guarded hypothesis holds on every standard affine open**, with no hypothesis on `T` at
all: `κ(𝔮) ⊗_T T_t` is a localization of `κ(𝔮) ⊗_T T = κ(𝔮)`
(`Algebra.TensorProduct.rid`) at the image of the powers of `t`, and a field is a domain, so
`Ideal.isDomain_fiber_of_isLocalization` applies the moment the localization is nonzero.

Together with `Ideal.not_isDomain_fiber_localizationAway_of_mem` this is the separation: on
`Spec T_t ⊆ Spec T` the guarded hypothesis of
`Ideal.forall_isDomain_fiber_of_forall_isDomain_fiber_of_isLocalization` is automatic while the
unguarded one is false. The guard is therefore not a weakening that has to be paid for later —
it is the difference between a hypothesis a chart always has and one it never has. -/
theorem isDomain_fiber_localizationAway_of_nontrivial {T : Type u} [CommRing T] (t : T)
    (q : Ideal T) [q.IsPrime] (hnt : Nontrivial (q.Fiber (Localization.Away t))) :
    IsDomain (q.Fiber (Localization.Away t)) :=
  isDomain_fiber_of_isLocalization (R := T) (A := T) (B := Localization.Away t)
    (Submonoid.powers t) q ((Algebra.TensorProduct.rid T T q.ResidueField).toMulEquiv.isDomain _)
    hnt

/-- **Surjectivity fails already on a standard affine open**, so the hypothesis the previous
declarations are about is genuinely unsatisfiable on a chart. For `t ∈ 𝔮` the element
`algebraMap T (Ideal.Fiber 𝔮 T_t) t` is simultaneously zero — because `t` dies in `κ(𝔮)` — and a
unit — because it is the image of a unit of `T_t` under `Algebra.TensorProduct.includeRight` — so
the fibre ring is the zero ring, which is not a domain.

Geometrically `Spec T_t` is the open `D(t)` of `Spec T`, and `𝔮 ∉ D(t)`: the fibre of an open
immersion over a point outside its image is empty. -/
theorem not_isDomain_fiber_localizationAway_of_mem {T : Type u} [CommRing T] (t : T)
    (q : Ideal T) [q.IsPrime] (ht : t ∈ q) :
    ¬ IsDomain (q.Fiber (Localization.Away t)) := by
  intro _
  have hu : IsUnit (algebraMap T (q.Fiber (Localization.Away t)) t) := by
    rw [← (Algebra.TensorProduct.includeRight (R := T) (A := q.ResidueField)
      (B := Localization.Away t)).commutes t]
    exact (IsLocalization.map_units (M := Submonoid.powers t) _
      ⟨t, Submonoid.mem_powers _⟩).map _
  have hz : algebraMap T (q.Fiber (Localization.Away t)) t = 0 := by
    rw [Algebra.TensorProduct.algebraMap_apply, algebraMap_residueField_eq_zero.2 ht,
      TensorProduct.zero_tmul]
  exact not_isUnit_zero (hz ▸ hu)

/-- **The `𝔭 = ⊥` case of `Ideal.isDomain_fiber_of_isDomain_fiber_of_isLocalization`.** For
domains `T` and `R` with `algebraMap T R` injective — a localization of a domain at a submonoid
of nonzerodivisors — the generic fibre of `A` is a domain as soon as the generic fibre of `S` is
and it is nonzero.

This is the specialization the second obstruction of Stacks Tag 0BD7 works in:
`Ideal.fiberBotRingEquivOfIsLocalization` identifies `Ideal.Fiber ⊥ 𝒪_{X, x}` with the ring
`A ⊗_R K` of the source, where assumption (5) of the tag places the germ of the meromorphic
section. -/
theorem isDomain_fiberBot_of_isDomain_fiberBot_of_isLocalization
    {T S R A : Type u} [CommRing T] [CommRing S] [CommRing R] [CommRing A]
    [IsDomain T] [IsDomain R]
    [Algebra T S] [Algebra T R] [Algebra R A] [Algebra T A] [Algebra S A]
    [IsScalarTower T R A] [IsScalarTower T S A]
    (N : Submonoid T) [IsLocalization N R] (M : Submonoid S) [IsLocalization M A]
    (hinj : Function.Injective (algebraMap T R))
    (hdom : IsDomain ((⊥ : Ideal T).Fiber S))
    (hnt : Nontrivial ((⊥ : Ideal R).Fiber A)) :
    IsDomain ((⊥ : Ideal R).Fiber A) :=
  isDomain_fiber_of_isDomain_fiber_of_isLocalization N M (⊥ : Ideal R) (⊥ : Ideal T)
    (Ideal.comap_bot_of_injective _ hinj) hdom hnt

end Ideal

namespace AlgebraicGeometry

/-- **Every fibre ring of the map of local rings induced by a flat morphism is nonzero.** The
map `𝒪_{Y, f x} → 𝒪_{X, x}` is faithfully flat
(`AlgebraicGeometry.Flat.faithfullyFlat_stalkMap`), so `Ideal.Fiber 𝔭 𝒪_{X, x}` is nonzero for
every prime `𝔭`. This is the nonvanishing input of obstruction (i) of Stacks Tag 0BD7, and it is
surjectivity of `Spec 𝒪_{X, x} → Spec 𝒪_{Y, y}` read on rings. -/
theorem nontrivial_fiber_stalkMap_of_flat {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (x : X)
    (p : Ideal (Y.presheaf.stalk (f x))) [p.IsPrime] :
    letI : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
    Nontrivial (p.Fiber (X.presheaf.stalk x)) := by
  let : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Flat.faithfullyFlat_stalkMap f x
  exact inferInstance

end AlgebraicGeometry

end
