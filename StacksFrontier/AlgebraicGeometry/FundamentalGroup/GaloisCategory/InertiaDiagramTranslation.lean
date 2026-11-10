module

public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.InertiaKernel
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.NormalFunctionField
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.CoverEquivalenceInvariance
public import StacksFrontier.RingTheory.Henselian.Pair.LocalRing
public import StacksFrontier.RingTheory.Invariant.DecompositionFixedField
public import StacksFrontier.RingTheory.Invariant.Primes

/-!
# The inertia diagram in Galois-theoretic terms

Let `(A, 𝔪, κ)` be a normal local ring with fraction field `K`, let `K^sep` be a separable
algebraic closure of `K`, let `A^sep` be the integral closure of `A` in `K^sep` and let
`𝔪^sep ⊆ A^sep` be a maximal ideal. The profinite group `G = Gal(K^sep/K)` acts on `A^sep`, and

```
D = {σ ∈ G | σ 𝔪^sep = 𝔪^sep}  ⊇  I = {σ ∈ D | σ mod 𝔪^sep = id on κ(𝔪^sep)}
```

are the decomposition and the inertia group at `𝔪^sep`. Writing `A ⊆ A^h ⊆ A^sh` for the
henselization and a strict henselization, the residue field `κ(𝔪^sh)` of `A^sh` is a separable
algebraic closure of `κ` while `κ(𝔪^sep)` is an algebraic closure of `κ`, so the ambient setup
comes with a `κ`-embedding `κ(𝔪^sh) → κ(𝔪^sep)`. Finally `M` denotes the maximal subextension of
`K^sep/K` unramified with respect to `A`, and `U = Spec K`, `X = Spec A`.

The source asserts that the diagram of fundamental groups

```
π₁(U^sh) → π₁(U^h) → π₁(U)
            ↓          ↓
          π₁(X^h) →  π₁(X)
```

translates, under `π₁(U) = Gal(K^sep/K)`, into

```
I → D → Gal(K^sep/K)
     ↓        ↓
  Gal(κ(𝔪^sh)/κ) → Gal(M/K)
```

that both vertical arrows are surjective, that the kernel of the left one is `I`, and that the
kernel of the right one is the smallest closed normal subgroup of `Gal(K^sep/K)` containing `I`.

This file provides the two **vertical arrows** and their fibrewise information:

* the left vertical arrow `D → Gal(κ(𝔪^sh)/κ)` is built, shown surjective, and its kernel is
  identified with the inertia group `I` — so the sequence `1 → I → D → Gal(κ(𝔪^sh)/κ) → 1` is
  exact and the diagonal arrow `I → Gal(κ(𝔪^sh)/κ)` labelled `1` in the diagram is trivial;
* the right vertical arrow `π₁(U) → π₁(X)` is shown surjective with kernel `Gal(K^sep/M)`;
* that kernel is identified with the smallest closed normal subgroup of `Gal(K^sep/K)`
  containing `I`, for `X = Spec A` the spectrum of the normal local ring itself;
* the **square** of the diagram commutes, with a unique bottom arrow
  `Gal(κ(𝔪^sh)/κ) → π₁(X)`;
* the lower left corner is identified: `π₁(X^h) = Gal(κ(𝔪^sh)/κ)` for `X^h` the spectrum of a
  henselian local ring with residue field `κ`;
* the top row is identified: the images of `π₁(U^sh)` and `π₁(U^h)` in `π₁(U) = Gal(K^sep/K)`
  are the inertia group `I` and the decomposition group `D`.

## Main definitions

* `Stacks.RamificationTheory.decompositionResidueHom` — the left vertical arrow
  `D → Gal(κ(𝔪^sh)/κ)`: the residue action of the decomposition group, followed by restriction to
  the chosen separable closure `κ(𝔪^sh)` of `κ` inside `κ(𝔪^sep)`.

## Main results

* `Stacks.RamificationTheory.surjective_decompositionResidueHom` — the left vertical arrow is
  surjective.
* `Stacks.RamificationTheory.ker_decompositionResidueHom` — its kernel is the inertia group `I`,
  as a subgroup of `D`; `Stacks.RamificationTheory.map_ker_decompositionResidueHom` records the
  same statement with `I` inside `Gal(K^sep/K)`, which is how the source writes it.
* `Stacks.RamificationTheory.decompositionResidueHom_comp_inertia_subtype` — the diagonal arrow
  `I → Gal(κ(𝔪^sh)/κ)` is trivial.
* `Stacks.RamificationTheory.surjective_and_ker_absoluteGaloisToFundamentalGroup` — the right
  vertical arrow is surjective and its kernel is the subgroup fixing the maximal unramified
  subextension `M`.
* `Stacks.RamificationTheory.bijective_restrictNormalHom_sepClosure` — restriction along a
  separable closure sitting inside a normal algebraic extension is an isomorphism of Galois
  groups; this is what turns `Aut(κ(𝔪^sep)/κ)` into `Gal(κ(𝔪^sh)/κ)`.
* `Stacks.RamificationTheory.comap_ker_etaleFundamentalGroupMap_eq_normalClosure_inertia` and
  `Stacks.RamificationTheory.isLeast_ker_etaleFundamentalGroupMap_inertia` — the kernel of the
  right vertical arrow is the smallest closed normal subgroup of `Gal(K^sep/K)` containing `I`.
* `Stacks.RamificationTheory.existsUnique_bottomArrow_square` — the square of the diagram
  commutes: there is exactly one homomorphism `Gal(κ(𝔪^sh)/κ) → π₁(X)` whose composition with
  the left vertical arrow is the right vertical arrow restricted to `D`.
* `Stacks.RamificationTheory.exists_continuousMulEquiv_etaleFundamentalGroup_henselianLocalRing`
  — `π₁(X^h) = Gal(κ(𝔪^sh)/κ)`: the fundamental group of the spectrum of a henselian local ring
  is the absolute Galois group of its residue field, by the canonical map.
* `Stacks.RamificationTheory.galoisEquiv_preimage_range_etaleFundamentalGroupMap_decomposition`
  and `Stacks.RamificationTheory.galoisEquiv_preimage_range_etaleFundamentalGroupMap_inertia` —
  `π₁(U^h) = D` and `π₁(U^sh) = I`: the images of `π₁(Spec K^h)` and `π₁(Spec K^sh)` in
  `π₁(Spec K)` are the decomposition group and the inertia group.

## Implementation notes

The residue action of the decomposition group is Mathlib's `IsFractionRing.stabilizerHom`, whose
surjectivity onto `Aut(κ(𝔪^sep)/κ)` is Stacks Tag 0BRK
(`IsIntegralClosure.exists_smul_of_under_eq_and_residue_normal_stabilizerHom_surjective`) and
whose kernel is `Ideal.inertia` by Mathlib's `IsFractionRing.ker_stabilizerHom`. Since the source
phrases the target as `Gal(κ(𝔪^sh)/κ)` rather than `Aut(κ(𝔪^sep)/κ)`, the arrow built here is
post-composed with restriction to `κ(𝔪^sh)`; that restriction is bijective because
`κ(𝔪^sep)/κ(𝔪^sh)` is purely inseparable, `κ(𝔪^sh)` being separably closed.

Residue fields are represented as in Stacks Tag 0BRK, by arbitrary fraction fields `κ` of
`A ⧸ 𝔪` and `κ(𝔪^sep)` of `A^sep ⧸ 𝔪^sep`, and `κ(𝔪^sh)` by an arbitrary separable closure of
`κ` embedded `κ`-linearly in `κ(𝔪^sep)` — exactly the data the ambient setup of the source
chooses. The decomposition group is `MulAction.stabilizer` and the inertia group is
`Ideal.inertia`, following the registry of Stacks Tag 09EC in this library.

The right vertical arrow is `AlgebraicGeometry.absoluteGaloisToFundamentalGroup`, the action of
the absolute Galois group of the function field on the geometric fibre functor; the maximal
unramified subextension is `AlgebraicGeometry.maximalEtaleExtension`. Both are the ones used for
Stacks Tags 0BQM and 03VG, where the quotient map onto the fundamental group is identified with
restriction to `M` (`AlgebraicGeometry.fundamentalGroupIsoGalMaximalEtaleExtension_apply`);
surjectivity and the kernel follow from that identification together with Galois theory, since
`M/K` is Galois by `AlgebraicGeometry.normal_maximalEtaleExtension`. The source field is the
algebraic closure `Ω = κ(η̄)` rather than `K^sep`; restriction `Gal(Ω/K) → Gal(K^sep/K)` is an
isomorphism, so this is the diagram's arrow. The right column assumes `X` integral and normal
only: Tag 0BQM holds without a Noetherian hypothesis, which the source's `Spec A` need not
satisfy.

The description of the kernel of the right vertical arrow as the smallest closed normal subgroup
containing `I` is proved for `X = Spec A`, in the last section. It rests on the step
`A^sh = ((A^sep)_{𝔪^sep})^I` of the source's proof, which is
`IsIntegralClosure.isHenselization_inertiaInvariants`, together with the identification of the
fraction field of that ring as the fixed field `(K^sep)^I`
(`IsIntegralClosure.isFractionRing_inertiaFixedField`) and the local exact sequence of Tag 0BSM.
The homomorphism in question is the one induced by `Spec K → Spec A` rather than
`AlgebraicGeometry.absoluteGaloisToFundamentalGroup`, and its kernel is read inside
`Gal(K^sep/K)` through the identification of Tag 0BNE; the two descriptions of that kernel are
not compared here.

The square of the diagram is recorded as the existence and uniqueness of its bottom arrow: the
left vertical arrow is surjective with kernel `I`, and `I` is contained in the kernel of the
right vertical arrow, so the bottom arrow exists and the square determines it. Its target is
`π₁(X)` rather than `Gal(M/K)`, those being identified by Tag 0BQM.

The identification `π₁(X^h) = Gal(κ(𝔪^sh)/κ)` is proved for the spectrum of an arbitrary
henselian local ring and its residue field, of which the source's `X^h = Spec A^h` is the case
of the henselization of `A`: the residue field of the henselization is `κ` by definition, and
`κ(𝔪^sh)`, the residue field of a strict henselization, is a separable algebraic closure of `κ`.
It comes from Tag 09ZS through Tag 0BQA and Tag 0BNE.

The identification `π₁(U^h) = D` rests on the step `K^h = (K^sep)^D` of the source's proof,
which is `IsIntegralClosure.exists_algHom_fieldRange_eq_fixedField_stabilizer`, together with
the naturality of Tag 0BNE. The embedding `K^h ⊆ K^sep` is data here, as it is in the source,
where it is induced by the chosen `κ`-embedding `κ(𝔪^sh) → κ(𝔪^sep)`; the hypothesis pinning it
down is that it comes from the canonical local map `A^h → (A^sep)_{𝔪^sep}`.

The identification `π₁(U^sh) = I` is the same naturality applied to the fixed field
`(K^sep)^I`, whose fixing subgroup is `I` by
`IsIntegralClosure.fixingSubgroup_inertiaFixedField`; that field is the fraction field of the
strict henselization `A^sh = ((A^sep)_{𝔪^sep})^I`, so no separate choice of embedding is
needed there.

## References

* [Stacks Project, Tag 0BSW](https://stacks.math.columbia.edu/tag/0BSW)
* [Stacks Project, Tag 0BSV](https://stacks.math.columbia.edu/tag/0BSV)
* [Stacks Project, Tag 0BRK](https://stacks.math.columbia.edu/tag/0BRK)
* [Stacks Project, Tag 03VG](https://stacks.math.columbia.edu/tag/03VG)
* [Stacks Project, Tag 0BSM](https://stacks.math.columbia.edu/tag/0BSM)
* [Stacks Project, Tag 0BNE](https://stacks.math.columbia.edu/tag/0BNE)
-/

@[expose] public section

universe uA uK uL uB uk ul us u

open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped Pointwise

namespace Stacks.RamificationTheory

/-! ### Restriction along a separable closure -/

/-- Restriction to a separable closure `ksep` of `k` inside an algebraic extension `l` of `ksep`
is injective on `Gal(l/k)`: an automorphism fixing `ksep` pointwise is a `ksep`-algebra
automorphism of the purely inseparable extension `l / ksep`, hence the identity. -/
theorem injective_restrictNormalHom_sepClosure
    (k ksep l : Type*) [Field k] [Field ksep] [Field l]
    [Algebra k ksep] [Algebra k l] [Algebra ksep l] [IsScalarTower k ksep l]
    [IsSepClosure k ksep] [Algebra.IsAlgebraic ksep l] :
    Function.Injective (AlgEquiv.restrictNormalHom (F := k) (K₁ := l) ksep) := by
  have : IsSepClosed ksep := IsSepClosure.sep_closed k
  rw [← MonoidHom.ker_eq_bot_iff, AlgEquiv.ker_restrictNormalHom]
  refine (Subgroup.eq_bot_iff_forall _).2 fun σ hσ => ?_
  rw [IntermediateField.mem_fixingSubgroup_iff] at hσ
  let τ : l →ₐ[ksep] l := { σ.toAlgHom.toRingHom with commutes' := fun x => hσ _ ⟨x, rfl⟩ }
  exact AlgEquiv.ext fun x => by
    simpa [τ] using congrArg (fun f : l →ₐ[ksep] l => f x)
      (Subsingleton.elim τ (IsScalarTower.toAlgHom ksep l l))

/-- Restriction to a separable closure `ksep` of `k` inside a normal algebraic extension `l` of
`k` is an isomorphism `Gal(l/k) ≃ Gal(ksep/k)`. -/
theorem bijective_restrictNormalHom_sepClosure
    (k ksep l : Type*) [Field k] [Field ksep] [Field l]
    [Algebra k ksep] [Algebra k l] [Algebra ksep l] [IsScalarTower k ksep l]
    [IsSepClosure k ksep] [Normal k l] :
    Function.Bijective (AlgEquiv.restrictNormalHom (F := k) (K₁ := l) ksep) := by
  have : Algebra.IsAlgebraic ksep l := Algebra.IsAlgebraic.tower_top (K := k) (L := ksep)
  exact ⟨injective_restrictNormalHom_sepClosure k ksep l,
    AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := ksep) (E := l)⟩

/-! ### The left vertical arrow `D → Gal(κ(𝔪^sh)/κ)` -/

section LeftColumn

variable (A : Type uA) (K : Type uK) (Ksep : Type uL) (Asep : Type uB)
    [CommRing A] [IsLocalRing A] [CommRing Asep] [Field K] [Field Ksep]
    [Algebra A K] [Algebra Asep Ksep] [IsFractionRing A K] [IsFractionRing Asep Ksep]
    [Algebra A Asep] [Algebra K Ksep] [Algebra A Ksep] [IsScalarTower A K Ksep]
    [IsScalarTower A Asep Ksep] [IsIntegrallyClosed A] [IsIntegralClosure Asep A Ksep]
    [IsSepClosure K Ksep]
    (msep : Ideal Asep) [msep.IsMaximal] [msep.LiesOver (maximalIdeal A)]
    (κ : Type uk) [Field κ] [Algebra (A ⧸ maximalIdeal A) κ]
      [IsFractionRing (A ⧸ maximalIdeal A) κ]
    (κmsep : Type ul) [Field κmsep] [Algebra (Asep ⧸ msep) κmsep]
      [IsFractionRing (Asep ⧸ msep) κmsep]
      [Algebra (A ⧸ maximalIdeal A) κmsep]
      [IsScalarTower (A ⧸ maximalIdeal A) (Asep ⧸ msep) κmsep]
      [Algebra κ κmsep] [IsScalarTower (A ⧸ maximalIdeal A) κ κmsep]
    (κmsh : Type us) [Field κmsh] [Algebra κ κmsh] [IsSepClosure κ κmsh]
      [Algebra κmsh κmsep] [IsScalarTower κ κmsh κmsep]

/-- The action of `Gal(K^sep/K)` on the integral closure `A^sep` of `A` in `K^sep`. -/
noncomputable abbrev galAction : MulSemiringAction Gal(Ksep/K) Asep :=
  IsIntegralClosure.MulSemiringAction A K Ksep Asep

omit [IsLocalRing A] [IsFractionRing Asep Ksep] [IsIntegrallyClosed A] in
/-- `Gal(K^sep/K)` acts `A`-linearly on `A^sep`. -/
theorem galSMulCommClass :
    letI := galAction A K Ksep Asep
    SMulCommClass Gal(Ksep/K) A Asep :=
  let := galAction A K Ksep Asep
  ⟨fun σ a b ↦ by
    simp only [Algebra.smul_def, smul_mul']
    congr 1
    exact (galRestrict A K Ksep Asep σ).commutes a⟩

/-- **The left vertical arrow of the diagram of Stacks Tag 0BSW.** The decomposition group
`D ⊆ Gal(K^sep/K)` at `𝔪^sep` acts on the residue field `κ(𝔪^sep)` over `κ`; composing with
restriction to the separable closure `κ(𝔪^sh)` of `κ` inside `κ(𝔪^sep)` gives the arrow
`D → Gal(κ(𝔪^sh)/κ)`. -/
noncomputable def decompositionResidueHom :
    letI := galAction A K Ksep Asep
    letI := galSMulCommClass A K Ksep Asep
    MulAction.stabilizer Gal(Ksep/K) msep →* Gal(κmsh/κ) :=
  let := galAction A K Ksep Asep
  let := galSMulCommClass A K Ksep Asep
  (AlgEquiv.restrictNormalHom (F := κ) (K₁ := κmsep) κmsh).comp
    (IsFractionRing.stabilizerHom Gal(Ksep/K) (maximalIdeal A) msep κ κmsep)

omit [IsFractionRing Asep Ksep] [IsIntegrallyClosed A] [msep.IsMaximal] in
/-- The left vertical arrow is the residue action of the decomposition group followed by
restriction to `κ(𝔪^sh)`. -/
theorem decompositionResidueHom_eq :
    letI := galAction A K Ksep Asep
    letI := galSMulCommClass A K Ksep Asep
    decompositionResidueHom A K Ksep Asep msep κ κmsep κmsh =
      (AlgEquiv.restrictNormalHom (F := κ) (K₁ := κmsep) κmsh).comp
        (IsFractionRing.stabilizerHom Gal(Ksep/K) (maximalIdeal A) msep κ κmsep) :=
  rfl

/-- **Stacks Project, Tag 0BSW.** The left vertical arrow `D → Gal(κ(𝔪^sh)/κ)` of the diagram is
surjective.

The decomposition group surjects onto `Aut(κ(𝔪^sep)/κ)` by Stacks Tag 0BRK, and restriction
`Aut(κ(𝔪^sep)/κ) → Gal(κ(𝔪^sh)/κ)` is surjective because `κ(𝔪^sep)/κ` is normal. -/
@[stacks 0BSW "surjectivity of the left vertical arrow D → Gal(κ(𝔪^sh)/κ)"]
theorem surjective_decompositionResidueHom :
    letI := galAction A K Ksep Asep
    letI := galSMulCommClass A K Ksep Asep
    Function.Surjective (decompositionResidueHom A K Ksep Asep msep κ κmsep κmsh) := by
  let := galAction A K Ksep Asep
  let := galSMulCommClass A K Ksep Asep
  obtain ⟨hnormal, hsurj⟩ :=
    (IsIntegralClosure.exists_smul_of_under_eq_and_residue_normal_stabilizerHom_surjective
      A K Ksep Asep).2 (maximalIdeal A) msep κ κmsep
  have : Normal κ κmsep := hnormal
  exact (bijective_restrictNormalHom_sepClosure κ κmsh κmsep).2.comp hsurj

/-- **Stacks Project, Tag 0BSW.** The kernel of the left vertical arrow `D → Gal(κ(𝔪^sh)/κ)` is
the inertia group `I`, viewed as a subgroup of the decomposition group `D`.

The residue action of `D` has kernel `I` by Mathlib's `IsFractionRing.ker_stabilizerHom`, and
restriction to `κ(𝔪^sh)` is injective because `κ(𝔪^sep)/κ(𝔪^sh)` is purely inseparable. -/
@[stacks 0BSW "the kernel of the left vertical arrow is the inertia group I"]
theorem ker_decompositionResidueHom :
    letI := galAction A K Ksep Asep
    letI := galSMulCommClass A K Ksep Asep
    (decompositionResidueHom A K Ksep Asep msep κ κmsep κmsh).ker =
      msep.inertia (MulAction.stabilizer Gal(Ksep/K) msep) := by
  let := galAction A K Ksep Asep
  let := galSMulCommClass A K Ksep Asep
  obtain ⟨hnormal, -⟩ :=
    (IsIntegralClosure.exists_smul_of_under_eq_and_residue_normal_stabilizerHom_surjective
      A K Ksep Asep).2 (maximalIdeal A) msep κ κmsep
  have : Normal κ κmsep := hnormal
  have : Algebra.IsAlgebraic κmsh κmsep := Algebra.IsAlgebraic.tower_top (K := κ) (L := κmsh)
  rw [decompositionResidueHom_eq A K Ksep Asep msep κ κmsep κmsh,
    MonoidHom.ker_comp_of_injective _ _ (injective_restrictNormalHom_sepClosure κ κmsh κmsep),
    IsFractionRing.ker_stabilizerHom]

/-- **Stacks Project, Tag 0BSW.** The kernel of the left vertical arrow, pushed forward into
`Gal(K^sep/K)`, is the inertia group `I` as the source defines it — a subgroup of
`Gal(K^sep/K)`. -/
@[stacks 0BSW "the kernel of the left vertical arrow is the inertia group I, as a subgroup of \
Gal(K^sep/K)"]
theorem map_ker_decompositionResidueHom :
    letI := galAction A K Ksep Asep
    letI := galSMulCommClass A K Ksep Asep
    (decompositionResidueHom A K Ksep Asep msep κ κmsep κmsh).ker.map
        (MulAction.stabilizer Gal(Ksep/K) msep).subtype =
      msep.inertia Gal(Ksep/K) := by
  let := galAction A K Ksep Asep
  let := galSMulCommClass A K Ksep Asep
  rw [ker_decompositionResidueHom A K Ksep Asep msep κ κmsep κmsh,
    AddSubgroup.inertia_map_subtype,
    inf_eq_left.2 (Ideal.inertia_le_stabilizer (M := Gal(Ksep/K)) msep)]

/-- **Stacks Project, Tag 0BSW.** The diagonal arrow of the diagram, from the inertia group `I`
to `Gal(κ(𝔪^sh)/κ)`, is trivial — the arrow labelled `1` in the source. -/
@[stacks 0BSW "triviality of the diagonal arrow I → Gal(κ(𝔪^sh)/κ) labelled 1 in the diagram"]
theorem decompositionResidueHom_comp_inertia_subtype :
    letI := galAction A K Ksep Asep
    letI := galSMulCommClass A K Ksep Asep
    (decompositionResidueHom A K Ksep Asep msep κ κmsep κmsh).comp
        (msep.inertia (MulAction.stabilizer Gal(Ksep/K) msep)).subtype = 1 := by
  let := galAction A K Ksep Asep
  let := galSMulCommClass A K Ksep Asep
  exact MonoidHom.ext fun σ => by
    simpa using (ker_decompositionResidueHom A K Ksep Asep msep κ κmsep κmsh).ge σ.2

end LeftColumn

/-! ### The right vertical arrow `π₁(U) → π₁(X)` -/

section RightColumn

attribute [local instance] GeometricPoint.residueFieldAlgebra

variable (X : Scheme.{u}) (sbar : GeometricPoint X)

/-- **Stacks Project, Tag 0BSW.** The right vertical arrow `π₁(U) → π₁(X)` of the diagram is
surjective, and its kernel is the subgroup fixing the maximal subextension `M` unramified with
respect to `X` — that is, `Gal(K^sep/M)`.

Both come from Stacks Tag 0BQM, where the arrow is identified with restriction to `M`
(`AlgebraicGeometry.fundamentalGroupIsoGalMaximalEtaleExtension_apply`) and `M/K` is shown to be
Galois (`AlgebraicGeometry.normal_maximalEtaleExtension`): restriction onto a normal
subextension is surjective with kernel its fixing subgroup. -/
@[stacks 0BSW "surjectivity of the right vertical arrow π₁(U) → π₁(X) and the identification of \
its kernel with Gal(K^sep/M), for a general integral normal X; that this kernel is the smallest \
closed normal subgroup of Gal(K^sep/K) containing I is \
Stacks.RamificationTheory.comap_ker_etaleFundamentalGroupMap_eq_normalClosure_inertia, for \
X = Spec A"]
theorem surjective_and_ker_absoluteGaloisToFundamentalGroup
    [IsIntegral X] [IsNormal X]
    (hs : GeometricPoint.IsAlgebraic sbar)
    (hgeneric : sbar.hom default = genericPoint X) :
    let _ : Normal (X.residueField (sbar.hom default)) (maximalEtaleExtension X sbar) :=
      normal_maximalEtaleExtension X sbar hs
    Function.Surjective (absoluteGaloisToFundamentalGroup X sbar) ∧
      (absoluteGaloisToFundamentalGroup X sbar).toMonoidHom.ker =
        (maximalEtaleExtension X sbar).fixingSubgroup := by
  let : Normal (X.residueField (sbar.hom default)) (maximalEtaleExtension X sbar) :=
    normal_maximalEtaleExtension X sbar hs
  set e := fundamentalGroupIsoGalMaximalEtaleExtension X sbar hs hgeneric
  have hap := fundamentalGroupIsoGalMaximalEtaleExtension_apply X sbar hs hgeneric
  refine ⟨fun ρ => ?_, ?_⟩
  · obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective
      (F := X.residueField (sbar.hom default)) (K₁ := maximalEtaleExtension X sbar)
      (E := sbar.residueField) (e ρ)
    exact ⟨σ, e.injective ((hap σ).trans hσ)⟩
  · ext σ
    rw [MonoidHom.mem_ker, ← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, ← hap σ]
    exact (map_eq_one_iff e e.injective).symm

end RightColumn

/-! ### The kernel of the right vertical arrow as the closed normal subgroup generated by `I` -/

/-- The `K`-algebra inclusion of an intermediate field `E` of `L/K` has range `E`. -/
private theorem fieldRange_isScalarTower_toAlgHom {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) : (IsScalarTower.toAlgHom K E L).fieldRange = E := by
  rw [show IsScalarTower.toAlgHom K E L = E.val from AlgHom.ext fun _ => rfl]
  exact E.fieldRange_val

/-- A separable closure `L` of `K` is a separable closure of any intermediate field `Kh`, and an
algebraic extension `Ω` of `K` is algebraic over `Kh`. -/
private theorem isSepClosure_and_isAlgebraic_of_tower {K Kh L Ω : Type*} [Field K] [Field Kh]
    [Field L] [Field Ω] [Algebra K Kh] [Algebra K L] [Algebra Kh L] [IsScalarTower K Kh L]
    [IsSepClosure K L] [Algebra L Ω] [Algebra K Ω] [Algebra Kh Ω] [IsScalarTower K Kh Ω]
    [Algebra.IsAlgebraic K Ω] : IsSepClosure Kh L ∧ Algebra.IsAlgebraic Kh Ω :=
  have : IsSepClosed L := IsSepClosure.sep_closed K
  have : Algebra.IsSeparable Kh L := Algebra.isSeparable_tower_top_of_isSeparable K Kh L
  ⟨⟨inferInstance, inferInstance⟩, Algebra.IsAlgebraic.tower_top (K := K) (L := Kh)⟩

section InertiaKernel

open scoped Pointwise

/-- **Stacks Project, Tag 0BSW.** The kernel of the right vertical arrow `π₁(U) → π₁(X)` of the
diagram, read inside `Gal(K^sep/K)` through the identification of Stacks Tag 0BNE, is the
smallest closed normal subgroup containing the inertia group `I` at `𝔪^sep`.

Here `A` is a normal local domain with fraction field `K`, `L = K^sep` is a separable closure of
`K`, `q = 𝔪^sep` is a prime of the integral closure `A^sep` of `A` in `K^sep` lying over the
maximal ideal, `U = Spec K` and `X = Spec A`. "Smallest closed normal subgroup containing `I`" is
written, as in `Stacks.FundamentalGroup.IsExactSequence`, as the topological closure of the
normal subgroup generated by `I`;
`Stacks.RamificationTheory.isLeast_ker_etaleFundamentalGroupMap_inertia` records the minimality
itself.

The strict henselization `A^sh = ((A^sep)_{𝔪^sep})^I` has `(K^sep)^I` as its fraction field, so
the local exact sequence of Stacks Tag 0BSM describes the kernel as the closed normal subgroup
generated by the image of `π₁(Spec (K^sep)^I)`; by naturality of Stacks Tag 0BNE that image is
the subgroup of `Gal(K^sep/K)` fixing `(K^sep)^I`, which is `I`. -/
@[stacks 0BSW "the kernel of the right vertical arrow π₁(U) → π₁(X) is the smallest closed \
normal subgroup of Gal(K^sep/K) containing the inertia group I, the kernel being read inside \
Gal(K^sep/K) through the identification of Tag 0BNE"]
theorem comap_ker_etaleFundamentalGroupMap_eq_normalClosure_inertia
    (A K L Ω : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
    [Field K] [Field L] [Field Ω]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsSepClosure K L]
    [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω]
    (q : Ideal (integralClosure A L)) [q.IsPrime]
    [q.LiesOver (maximalIdeal A)] :
    letI : ConnectedSpace (Spec (.of A)) := connectedSpace_spec_of_isLocalRing A
    letI := IsIntegralClosure.galAction A K L
    Subgroup.comap (galoisEquivEtaleFundamentalGroup K L Ω).toMonoidHom
        (MonoidHom.ker (etaleFundamentalGroupMap
          (Spec.map (CommRingCat.ofHom (algebraMap A K)))
          (algebraicClosureGeometricPoint K Ω)).toMonoidHom) =
      (Subgroup.normalClosure
        ((q.inertia Gal(L/K) : Subgroup Gal(L/K)) : Set Gal(L/K))).topologicalClosure := by
  let : ConnectedSpace (Spec (.of A)) := connectedSpace_spec_of_isLocalRing A
  let := IsIntegralClosure.galAction A K L
  let := IsIntegralClosure.galSMulCommClass A K L
  have : IsSepClosed L := IsSepClosure.sep_closed K
  let : IsFractionRing (IsIntegralClosure.inertiaInvariants A K L q)
      (IsIntegralClosure.inertiaFixedField A K L q : Type u) :=
    IsIntegralClosure.isFractionRing_inertiaFixedField A K L q
  obtain ⟨_, _⟩ := IsIntegralClosure.isHenselization_inertiaInvariants A K L q
  obtain ⟨_, _⟩ := isSepClosure_and_isAlgebraic_of_tower (K := K)
    (Kh := (IsIntegralClosure.inertiaFixedField A K L q : Type u)) (L := L) (Ω := Ω)
  rw [← IsIntegralClosure.fixingSubgroup_inertiaFixedField A K L q,
    ← fieldRange_isScalarTower_toAlgHom (IsIntegralClosure.inertiaFixedField A K L q)]
  refine comap_ker_etaleFundamentalGroupMap_eq_normalClosure_fixingSubgroup A K
    (IsIntegralClosure.inertiaFixedField A K L q : Type u) L Ω fun z hz => ?_
  subst hz
  exact (isExactSequence_etaleFundamentalGroupMap_fractionField_of_isHenselization A
    (IsIntegralClosure.inertiaInvariants A K L q)
    (ResidueField (IsIntegralClosure.inertiaInvariants A K L q)) K
    (IsIntegralClosure.inertiaFixedField A K L q : Type u)
    (algebraicClosureGeometricPoint
      (IsIntegralClosure.inertiaFixedField A K L q : Type u) Ω)).2.2

/-- **Stacks Project, Tag 0BSW.** The kernel of the right vertical arrow `π₁(U) → π₁(X)`, read
inside `Gal(K^sep/K)`, is the least closed normal subgroup containing the inertia group `I` —
the minimality assertion of the source, read off from
`Stacks.RamificationTheory.comap_ker_etaleFundamentalGroupMap_eq_normalClosure_inertia`. -/
@[stacks 0BSW "the minimality form of the previous statement: the kernel of the right vertical \
arrow is the least closed normal subgroup of Gal(K^sep/K) containing the inertia group I"]
theorem isLeast_ker_etaleFundamentalGroupMap_inertia
    (A K L Ω : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
    [Field K] [Field L] [Field Ω]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsSepClosure K L]
    [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω]
    (q : Ideal (integralClosure A L)) [q.IsPrime]
    [q.LiesOver (maximalIdeal A)] :
    letI : ConnectedSpace (Spec (.of A)) := connectedSpace_spec_of_isLocalRing A
    letI := IsIntegralClosure.galAction A K L
    IsLeast {N : Subgroup Gal(L/K) |
        N.Normal ∧ IsClosed (N : Set Gal(L/K)) ∧ q.inertia Gal(L/K) ≤ N}
      (Subgroup.comap (galoisEquivEtaleFundamentalGroup K L Ω).toMonoidHom
        (MonoidHom.ker (etaleFundamentalGroupMap
          (Spec.map (CommRingCat.ofHom (algebraMap A K)))
          (algebraicClosureGeometricPoint K Ω)).toMonoidHom)) := by
  let : ConnectedSpace (Spec (.of A)) := connectedSpace_spec_of_isLocalRing A
  let := IsIntegralClosure.galAction A K L
  rw [comap_ker_etaleFundamentalGroupMap_eq_normalClosure_inertia A K L Ω q]
  refine ⟨⟨Subgroup.is_normal_topologicalClosure _, Subgroup.isClosed_topologicalClosure _,
    fun g hg => Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hg)⟩,
    fun N hN => ?_⟩
  have := hN.1
  exact Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hN.2.2) hN.2.1

end InertiaKernel

/-! ### The commutative square of the diagram -/

section Square

open scoped Pointwise

/-- **Stacks Project, Tag 0BSW: the square of the diagram commutes.** With `A` a normal local
domain with fraction field `K`, `L = K^sep` a separable closure of `K` inside an algebraically
closed algebraic extension `Ω`, `q = 𝔪^sep` a maximal ideal of the integral closure `A^sep` of
`A` in `K^sep` lying over `𝔪`, `U = Spec K` and `X = Spec A`, there is exactly one homomorphism
`Gal(κ(𝔪^sh)/κ) → π₁(X)` making the square

```
D ─────────────→ Gal(K^sep/K) = π₁(U)
│                          │
↓                          ↓
Gal(κ(𝔪^sh)/κ) ───────→ π₁(X)
```

commute: the top arrow is the inclusion of the decomposition group, the left vertical arrow is
`Stacks.RamificationTheory.decompositionResidueHom`, and the right vertical arrow is the map
induced by `Spec K → Spec A` read on `Gal(K^sep/K)` through the identification of Stacks Tag
0BNE. By Stacks Tag 0BQM the target `π₁(X)` is `Gal(M/K)` for `M` the maximal subextension of
`K^sep/K` unramified with respect to `A`
(`AlgebraicGeometry.isQuotientMap_absoluteGaloisToFundamentalGroup`), which is how the source
labels the lower right corner.

Existence and uniqueness are the exactness of `1 → I → D → Gal(κ(𝔪^sh)/κ) → 1` recorded in
`Stacks.RamificationTheory.surjective_decompositionResidueHom` and
`Stacks.RamificationTheory.ker_decompositionResidueHom`, together with the fact that `I` dies in
`π₁(X)`, which is
`Stacks.RamificationTheory.comap_ker_etaleFundamentalGroupMap_eq_normalClosure_inertia`. So the
bottom arrow of the source's diagram exists, is determined by the square, and the square is the
one the source draws. -/
@[stacks 0BSW "commutativity of the square of the diagram: the bottom arrow \
Gal(κ(𝔪^sh)/κ) → π₁(X) exists and is unique, the right vertical arrow being the map induced by \
Spec K → Spec A read in Gal(K^sep/K) through the identification of Tag 0BNE and the lower right \
corner being π₁(X), which is Gal(M/K) by Tag 0BQM"]
theorem existsUnique_bottomArrow_square
    (A K L Ω : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
    [Field K] [Field L] [Field Ω]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsSepClosure K L]
    [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic K Ω]
    (q : Ideal (integralClosure A L)) [q.IsMaximal] [q.LiesOver (maximalIdeal A)]
    (κ : Type uk) [Field κ] [Algebra (A ⧸ maximalIdeal A) κ]
      [IsFractionRing (A ⧸ maximalIdeal A) κ]
    (κmsep : Type ul) [Field κmsep] [Algebra (integralClosure A L ⧸ q) κmsep]
      [IsFractionRing (integralClosure A L ⧸ q) κmsep]
      [Algebra (A ⧸ maximalIdeal A) κmsep]
      [IsScalarTower (A ⧸ maximalIdeal A) (integralClosure A L ⧸ q) κmsep]
      [Algebra κ κmsep] [IsScalarTower (A ⧸ maximalIdeal A) κ κmsep]
    (κmsh : Type us) [Field κmsh] [Algebra κ κmsh] [IsSepClosure κ κmsh]
      [Algebra κmsh κmsep] [IsScalarTower κ κmsh κmsep] :
    letI : ConnectedSpace (Spec (.of A)) := connectedSpace_spec_of_isLocalRing A
    letI := IsIntegralClosure.isFractionRing_integralClosure A K L
    letI := IsIntegralClosure.galAction A K L
    letI := IsIntegralClosure.galSMulCommClass A K L
    ∃! h : Gal(κmsh/κ) →*
        EtaleFundamentalGroup (Spec (.of A))
          ((algebraicClosureGeometricPoint K Ω).map
            (Spec.map (CommRingCat.ofHom (algebraMap A K)))),
      ∀ σ : MulAction.stabilizer Gal(L/K) q,
        h (decompositionResidueHom A K L (integralClosure A L) q κ κmsep κmsh σ) =
          etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap A K)))
            (algebraicClosureGeometricPoint K Ω)
            (galoisEquivEtaleFundamentalGroup K L Ω (σ : Gal(L/K))) := by
  let : ConnectedSpace (Spec (.of A)) := connectedSpace_spec_of_isLocalRing A
  let := IsIntegralClosure.isFractionRing_integralClosure A K L
  let := IsIntegralClosure.galAction A K L
  let := IsIntegralClosure.galSMulCommClass A K L
  set D := MulAction.stabilizer Gal(L/K) q
  set ρ : Gal(L/K) →*
      EtaleFundamentalGroup (Spec (.of A))
        ((algebraicClosureGeometricPoint K Ω).map
          (Spec.map (CommRingCat.ofHom (algebraMap A K)))) :=
    (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap A K)))
        (algebraicClosureGeometricPoint K Ω)).toMonoidHom.comp
      (galoisEquivEtaleFundamentalGroup K L Ω).toMonoidHom
  have hkerρ : q.inertia Gal(L/K) ≤ ρ.ker := fun σ hσ =>
    (comap_ker_etaleFundamentalGroupMap_eq_normalClosure_inertia A K L Ω q).ge
      (Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hσ))
  set f : D →* Gal(κmsh/κ) :=
    decompositionResidueHom A K L (integralClosure A L) q κ κmsep κmsh with hf
  set g : D →* _ := ρ.comp D.subtype
  have hsurj : Function.Surjective f :=
    surjective_decompositionResidueHom A K L (integralClosure A L) q κ κmsep κmsh
  have hfg : f.ker ≤ g.ker := fun σ hσ => hkerρ (Ideal.coe_mem_inertia.mpr (by
    rwa [hf, ker_decompositionResidueHom A K L (integralClosure A L) q κ κmsep κmsh] at hσ))
  set e := QuotientGroup.quotientKerEquivOfSurjective f hsurj
  have key : ∀ σ, QuotientGroup.lift f.ker g hfg (e.symm (f σ)) = g σ := fun σ => by
    rw [← QuotientGroup.kerLift_mk f σ]
    change QuotientGroup.lift f.ker g hfg (e.symm (e (QuotientGroup.mk σ))) = g σ
    rw [e.symm_apply_apply]
    rfl
  refine ⟨(QuotientGroup.lift f.ker g hfg).comp e.symm.toMonoidHom, key,
    fun h' hh' => MonoidHom.ext fun τ => ?_⟩
  obtain ⟨σ, rfl⟩ := hsurj τ
  exact (hh' σ).trans (key σ).symm

end Square

/-! ### The fundamental group of the spectrum of a henselian local ring -/

section Henselian

/-- **Stacks Project, Tag 0BSW: `π₁(X^h) = Gal(κ(𝔪^sh)/κ)`.** For a henselian local ring `A^h`
with residue field `κ` and a separable algebraic closure `κ(𝔪^sh)` of `κ` inside an algebraically
closed algebraic extension `Ω`, the étale fundamental group of `X^h = Spec A^h` at the geometric
point coming from `Ω` is `Gal(κ(𝔪^sh)/κ)`, by the canonical map induced by the closed immersion
`Spec κ → Spec A^h`.

This is the identification the source quotes from Stacks Tag 09ZS: base change along
`Spec κ → Spec A^h` is an equivalence on finite étale schemes for the henselian pair
`(A^h, 𝔪^h)` (`AlgebraicGeometry.finiteEtaleBaseChange_isEquivalence_of_henselianPair`), hence an
isomorphism of fundamental groups by Stacks Tag 0BQA
(`AlgebraicGeometry.fundamentalGroupContinuousMulEquivOfFiniteEtaleBaseChange`), and
`π₁(Spec κ) = Gal(κ(𝔪^sh)/κ)` by Stacks Tag 0BNE
(`AlgebraicGeometry.galoisEquivEtaleFundamentalGroup`).

In the situation of the source `A^h` is the henselization of the normal local ring `(A, 𝔪, κ)`,
whose residue field is `κ` itself — that is a defining condition on
`IsLocalRing.IsHenselization A (IsLocalRing.ResidueField A) A^h` — and `κ(𝔪^sh)`, the residue
field of a strict henselization, is a separable algebraic closure of `κ`; so this is the
statement the source makes about the lower left corner of its diagram. The identification is
recorded with the side condition that the underlying map is the canonical one, so that the
statement is not merely an abstract isomorphism of two groups. -/
@[stacks 0BSW "the identification π₁(X^h) = Gal(κ(𝔪^sh)/κ) of the lower left corner of the \
diagram, stated for the spectrum of an arbitrary henselian local ring and its residue field, of \
which X^h = Spec A^h is the case of the henselization of A",
  sga "3 X 4.0" "Recall 4.0, special case"]
theorem exists_continuousMulEquiv_etaleFundamentalGroup_henselianLocalRing
    (Ah : Type u) [CommRing Ah] [IsLocalRing Ah] [HenselianLocalRing Ah]
    (κsh Ω : Type u) [Field κsh] [Field Ω]
    [Algebra (ResidueField Ah) κsh] [IsSepClosure (ResidueField Ah) κsh]
    [Algebra κsh Ω] [Algebra (ResidueField Ah) Ω]
    [IsScalarTower (ResidueField Ah) κsh Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic (ResidueField Ah) Ω] :
    letI : ConnectedSpace (Spec (.of Ah)) := connectedSpace_spec_of_isLocalRing Ah
    letI : ConnectedSpace (Spec (.of (ResidueField Ah))) :=
      connectedSpace_spec_of_isLocalRing (ResidueField Ah)
    ∃ e : Gal(κsh / ResidueField Ah) ≃ₜ*
        EtaleFundamentalGroup (Spec (.of Ah))
          ((algebraicClosureGeometricPoint (ResidueField Ah) Ω).map
            (Spec.map (CommRingCat.ofHom (residue Ah)))),
      ∀ σ : Gal(κsh / ResidueField Ah),
        e σ = etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (residue Ah)))
            (algebraicClosureGeometricPoint (ResidueField Ah) Ω)
            (galoisEquivEtaleFundamentalGroup (ResidueField Ah) κsh Ω σ) := by
  let : ConnectedSpace (Spec (.of Ah)) := connectedSpace_spec_of_isLocalRing Ah
  let : ConnectedSpace (Spec (.of (ResidueField Ah))) :=
    connectedSpace_spec_of_isLocalRing (ResidueField Ah)
  have heq :
      (finiteEtaleBaseChange (Spec.map (CommRingCat.ofHom (residue Ah)))).IsEquivalence :=
    finiteEtaleBaseChange_isEquivalence_of_henselianPair Ah (maximalIdeal Ah)
      (henselianPair_maximalIdeal Ah)
  obtain ⟨e, he⟩ := fundamentalGroupContinuousMulEquivOfFiniteEtaleBaseChange
    (Spec.map (CommRingCat.ofHom (residue Ah))) heq
    (algebraicClosureGeometricPoint (ResidueField Ah) Ω)
  exact ⟨(galoisEquivEtaleFundamentalGroup (ResidueField Ah) κsh Ω).trans e, fun σ => he _⟩

/-! ### The identification `π₁(U^h) = D` -/

section TopRow

open scoped Pointwise

/-- **Stacks Project, Tag 0BSW: `π₁(U^h) = D`.** In the situation of the source, with
`U^h = Spec K^h` for `K^h` the fraction field of a henselization `A^h` of `A` and
`K^h ⊆ K^sep` the embedding induced by the chosen local map `A^h → (A^sep)_{𝔪^sep}`, the image of
`π₁(U^h)` in `π₁(U) = Gal(K^sep/K)` is exactly the decomposition group
`D = {σ | σ 𝔪^sep = 𝔪^sep}`.

This is the middle of the top row of the diagram of Tag 0BSV, read through the identification of
Tag 0BNE. It combines
`IsIntegralClosure.exists_algHom_fieldRange_eq_fixedField_stabilizer` — the source's step
`K^h = (K^sep)^D` — with the naturality of Tag 0BNE
(`AlgebraicGeometry.galoisEquiv_preimage_range_etaleFundamentalGroupMap`), which says that the
image of `π₁(Spec E)` in `π₁(Spec K)` is the subgroup of `Gal(K^sep/K)` fixing `E`.

The embedding `K^h → K^sep` is data, as it is in the source, where it comes from the chosen
`κ`-embedding `κ(𝔪^sh) → κ(𝔪^sep)` and the resulting map `A^sh → (A^sep)_{𝔪^sep}`; the
hypothesis `hcompat` says that it is the one induced by the canonical local map `A^h → B_q`, and
`IsIntegralClosure.exists_algHom_fieldRange_eq_fixedField_stabilizer` provides such an
embedding. -/
@[stacks 0BSW "the identification π₁(U^h) = D of the top row of the diagram: the image of \
π₁(Spec K^h) in π₁(Spec K) is the decomposition group D, read in Gal(K^sep/K) through the \
identification of Tag 0BNE, for the embedding K^h ⊆ K^sep induced by the canonical local map \
from the henselization to (A^sep)_{𝔪^sep}"]
theorem galoisEquiv_preimage_range_etaleFundamentalGroupMap_decomposition
    (A K L Ω : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
    [Field K] [Field L] [Field Ω]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsSepClosure K L] [IsSepClosed L]
    [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (q : Ideal (integralClosure A L)) [q.IsPrime] [q.LiesOver (maximalIdeal A)]
    (Ah Kh : Type u) [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsLocalRing.IsHenselization A (ResidueField A) Ah]
    [Field Kh] [Algebra Ah Kh] [IsFractionRing Ah Kh]
    [Algebra A Kh] [IsScalarTower A Ah Kh] [Algebra K Kh] [IsScalarTower A K Kh]
    [Algebra Kh L] [IsScalarTower K Kh L] [Algebra Kh Ω] [IsScalarTower Kh L Ω]
    (hcompat : ∀ x : Ah, algebraMap Kh L (algebraMap Ah Kh x) =
      IsIntegralClosure.henselizationToField A K L q Ah x) :
    letI := IsIntegralClosure.galAction A K L
    ∃ hx : (algebraicClosureGeometricPoint Kh Ω).map
        (Spec.map (CommRingCat.ofHom (algebraMap K Kh))) = algebraicClosureGeometricPoint K Ω,
      (galoisEquivEtaleFundamentalGroup K L Ω) ⁻¹'
          Set.range (fun τ : EtaleFundamentalGroup (Spec (.of Kh))
              (algebraicClosureGeometricPoint Kh Ω) =>
            hx ▸ etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap K Kh)))
              (algebraicClosureGeometricPoint Kh Ω) τ) =
        (MulAction.stabilizer Gal(L/K) q : Set Gal(L/K)) := by
  let := IsIntegralClosure.galAction A K L
  let := IsIntegralClosure.galSMulCommClass A K L
  have : IsScalarTower K Kh Ω := .of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K L Ω, IsScalarTower.algebraMap_apply K Kh L,
      ← IsScalarTower.algebraMap_apply Kh L Ω]
  obtain ⟨_, _⟩ := isSepClosure_and_isAlgebraic_of_tower (K := K) (Kh := Kh) (L := L) (Ω := Ω)
  obtain ⟨hx, hrange⟩ := galoisEquiv_preimage_range_etaleFundamentalGroupMap K Kh L Ω
  refine ⟨hx, hrange.trans ?_⟩
  congr 1
  obtain ⟨j, hcj, hfix, -⟩ :=
    IsIntegralClosure.exists_algHom_fieldRange_eq_fixedField_stabilizer A K L q Ah Kh
  have hj : IsScalarTower.toAlgHom K Kh L = j := by
    refine AlgHom.ext fun z => ?_
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := Ah) z
    have h (w : Ah) : IsScalarTower.toAlgHom K Kh L (algebraMap Ah Kh w) =
        j (algebraMap Ah Kh w) := (hcompat w).trans (hcj w).symm
    rw [map_div₀, map_div₀, h, h]
  rwa [hj]

/-- **Stacks Project, Tag 0BSW: `π₁(U^sh) = I`.** With `U^sh = Spec K^sh` for
`K^sh = (K^sep)^I` the fraction field of the strict henselization
`A^sh = ((A^sep)_{𝔪^sep})^I`, the image of `π₁(U^sh)` in `π₁(U) = Gal(K^sep/K)` is exactly the
inertia group `I` at `𝔪^sep`.

This is the left end of the top row of the diagram of Tag 0BSV, read through the identification
of Tag 0BNE. The strictly henselized fraction field is presented as the fixed field
`IsIntegralClosure.inertiaFixedField`, which is a fraction field of
`((A^sep)_{𝔪^sep})^I` by `IsIntegralClosure.isFractionRing_inertiaFixedField`, that ring being a
strict henselization of `A` by `IsIntegralClosure.isHenselization_inertiaInvariants`; its fixing
subgroup is `I` by `IsIntegralClosure.fixingSubgroup_inertiaFixedField`, and the naturality of
Tag 0BNE (`AlgebraicGeometry.galoisEquiv_preimage_range_etaleFundamentalGroupMap`) turns that
into the assertion about fundamental groups. -/
@[stacks 0BSW "the identification π₁(U^sh) = I of the top row of the diagram: the image of \
π₁(Spec K^sh) in π₁(Spec K) is the inertia group I, read in Gal(K^sep/K) through the \
identification of Tag 0BNE, with K^sh presented as the fixed field (K^sep)^I"]
theorem galoisEquiv_preimage_range_etaleFundamentalGroupMap_inertia
    (A K L Ω : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
    [Field K] [Field L] [Field Ω]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsSepClosure K L]
    [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (q : Ideal (integralClosure A L)) [q.IsPrime] :
    letI := IsIntegralClosure.galAction A K L
    ∃ hx : (algebraicClosureGeometricPoint
          (IsIntegralClosure.inertiaFixedField A K L q : Type u) Ω).map
          (Spec.map (CommRingCat.ofHom (algebraMap K
            (IsIntegralClosure.inertiaFixedField A K L q : Type u)))) =
        algebraicClosureGeometricPoint K Ω,
      (galoisEquivEtaleFundamentalGroup K L Ω) ⁻¹'
          Set.range (fun τ : EtaleFundamentalGroup
              (Spec (.of (IsIntegralClosure.inertiaFixedField A K L q : Type u)))
              (algebraicClosureGeometricPoint
                (IsIntegralClosure.inertiaFixedField A K L q : Type u) Ω) =>
            hx ▸ etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap K
                (IsIntegralClosure.inertiaFixedField A K L q : Type u))))
              (algebraicClosureGeometricPoint
                (IsIntegralClosure.inertiaFixedField A K L q : Type u) Ω) τ) =
        (q.inertia Gal(L/K) : Set Gal(L/K)) := by
  let := IsIntegralClosure.galAction A K L
  let := IsIntegralClosure.galSMulCommClass A K L
  have : IsSepClosed L := IsSepClosure.sep_closed K
  obtain ⟨_, _⟩ := isSepClosure_and_isAlgebraic_of_tower (K := K)
    (Kh := (IsIntegralClosure.inertiaFixedField A K L q : Type u)) (L := L) (Ω := Ω)
  obtain ⟨hx, hrange⟩ := galoisEquiv_preimage_range_etaleFundamentalGroupMap K
    (IsIntegralClosure.inertiaFixedField A K L q : Type u) L Ω
  refine ⟨hx, hrange.trans ?_⟩
  congr 1
  rw [fieldRange_isScalarTower_toAlgHom]
  exact IsIntegralClosure.fixingSubgroup_inertiaFixedField A K L q

end TopRow

end Henselian

end Stacks.RamificationTheory

end
