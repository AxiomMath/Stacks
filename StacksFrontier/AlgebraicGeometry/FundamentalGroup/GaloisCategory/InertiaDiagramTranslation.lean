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

The full statement, every object and arrow of the diagram included, is
`Stacks.RamificationTheory.inertiaDiagram_translation`, assembled in the last section from the
pieces below:

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
* the left vertical arrow `π₁(U^h) → π₁(X^h)` is identified with `D → Gal(κ(𝔪^sh)/κ)` through an
  isomorphism `Gal(κ(𝔪^sh)/κ) ≅ π₁(X^h)`, and then the bottom arrow `π₁(X^h) → π₁(X)` is the
  bottom arrow of the square.

## Main definitions

* `Stacks.RamificationTheory.decompositionResidueHom` — the left vertical arrow
  `D → Gal(κ(𝔪^sh)/κ)`: the residue action of the decomposition group, followed by restriction to
  the chosen separable closure `κ(𝔪^sh)` of `κ` inside `κ(𝔪^sep)`.

## Main results

* `Stacks.RamificationTheory.inertiaDiagram_translation` — **Stacks Tag 0BSW**: the diagram of
  Tag 0BSV translates into the Galois diagram, objects and arrows alike.
* `Stacks.RamificationTheory.surjective_and_comap_ker_etaleFundamentalGroupMap_henselization` —
  `π₁(U^h) → π₁(X^h)` is surjective, and its kernel, read in `Gal(K^sep/K^h)`, is the preimage of
  `I`.
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

The identification of the left vertical arrow `π₁(U^h) → π₁(X^h)` rests on the local exact
sequence of Tag 0BSM for the normal local domain `A^h` (Tag 06DI): the strict henselization
`((A^sep)_{𝔪^sep})^I` of `A` is ind-étale over `A^h` (Tag 08HS), hence a strict henselization of
`A^h`, and its fraction field `(K^sep)^I` has fixing subgroup in `Gal(K^sep/K^h)` the preimage of
`I`. So `π₁(U^h) → π₁(X^h)` and `D → Gal(κ(𝔪^sh)/κ)` are surjections with the same kernel `I`,
and the isomorphism `Gal(κ(𝔪^sh)/κ) ≅ π₁(X^h)` they induce is an isomorphism of groups. The square
then commutes by Tag 0BSV and the naturality of Tag 0BNE.

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

/-- **Part of Stacks Project, Tag 0BSW.** The left vertical arrow `D → Gal(κ(𝔪^sh)/κ)` of the
diagram is surjective. The full statement of Stacks Tag 0BSW is
`Stacks.RamificationTheory.inertiaDiagram_translation`.

The decomposition group surjects onto `Aut(κ(𝔪^sep)/κ)` by Stacks Tag 0BRK, and restriction
`Aut(κ(𝔪^sep)/κ) → Gal(κ(𝔪^sh)/κ)` is surjective because `κ(𝔪^sep)/κ` is normal. -/
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

/-- **Part of Stacks Project, Tag 0BSW.** The kernel of the left vertical arrow
`D → Gal(κ(𝔪^sh)/κ)` is the inertia group `I`, viewed as a subgroup of the decomposition group
`D`. The full statement of Stacks Tag 0BSW is
`Stacks.RamificationTheory.inertiaDiagram_translation`.

The residue action of `D` has kernel `I` by Mathlib's `IsFractionRing.ker_stabilizerHom`, and
restriction to `κ(𝔪^sh)` is injective because `κ(𝔪^sep)/κ(𝔪^sh)` is purely inseparable. -/
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

/-- **Part of Stacks Project, Tag 0BSW.** The kernel of the left vertical arrow, pushed forward
into `Gal(K^sep/K)`, is the inertia group `I` as the source defines it — a subgroup of
`Gal(K^sep/K)`. The full statement of Stacks Tag 0BSW is
`Stacks.RamificationTheory.inertiaDiagram_translation`. -/
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

/-- **Part of Stacks Project, Tag 0BSW.** The diagonal arrow of the diagram, from the inertia
group `I` to `Gal(κ(𝔪^sh)/κ)`, is trivial — the arrow labelled `1` in the source. The full statement
of Stacks Tag 0BSW is `Stacks.RamificationTheory.inertiaDiagram_translation`. -/
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
subextension is surjective with kernel its fixing subgroup.

This is the lower right corner `π₁(X) = Gal(M/K)` of the translated diagram, with the right
vertical arrow read as restriction to `M`; the rest of the lemma — every other object and arrow,
the square, and both kernels — is `Stacks.RamificationTheory.inertiaDiagram_translation`, which
also shows that for `X = Spec A` its right vertical arrow agrees with the one here
(`exists_absoluteGaloisToFundamentalGroup_eq_etaleFundamentalGroupMap`). -/
@[stacks 0BSW "the lower right corner π₁(X) = Gal(M/K) of the translated diagram, M the maximal \
subextension unramified with respect to X: the right vertical arrow, from the absolute Galois \
group of the function field, is surjective with kernel Gal(K^sep/M), for a general integral \
normal X. The other objects and arrows of the diagram, the square and the kernels are \
Stacks.RamificationTheory.inertiaDiagram_translation, which also proves that its right vertical \
arrow, for X = Spec A, is this one"]
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

/-- **Part of Stacks Project, Tag 0BSW.** The kernel of the right vertical arrow `π₁(U) → π₁(X)`
of the diagram, read inside `Gal(K^sep/K)` through the identification of Stacks Tag 0BNE, is the
smallest closed normal subgroup containing the inertia group `I` at `𝔪^sep`.

Here `A` is a normal local domain with fraction field `K`, `L = K^sep` is a separable closure of
`K`, `q = 𝔪^sep` is a prime of the integral closure `A^sep` of `A` in `K^sep` lying over the
maximal ideal, `U = Spec K` and `X = Spec A`. "Smallest closed normal subgroup containing `I`" is
written, as in `Stacks.FundamentalGroup.IsExactSequence`, as the topological closure of the
normal subgroup generated by `I`;
`Stacks.RamificationTheory.isLeast_ker_etaleFundamentalGroupMap_inertia` records the minimality
itself. The full statement of Stacks Tag 0BSW is
`Stacks.RamificationTheory.inertiaDiagram_translation`.

The strict henselization `A^sh = ((A^sep)_{𝔪^sep})^I` has `(K^sep)^I` as its fraction field, so
the local exact sequence of Stacks Tag 0BSM describes the kernel as the closed normal subgroup
generated by the image of `π₁(Spec (K^sep)^I)`; by naturality of Stacks Tag 0BNE that image is
the subgroup of `Gal(K^sep/K)` fixing `(K^sep)^I`, which is `I`. -/
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

/-- **Part of Stacks Project, Tag 0BSW.** The kernel of the right vertical arrow
`π₁(U) → π₁(X)`, read inside `Gal(K^sep/K)`, is the least closed normal subgroup containing the
inertia group `I` — the minimality assertion of the source, read off from
`Stacks.RamificationTheory.comap_ker_etaleFundamentalGroupMap_eq_normalClosure_inertia`.
The full statement of Stacks Tag 0BSW is `Stacks.RamificationTheory.inertiaDiagram_translation`. -/
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

/-- **Part of Stacks Project, Tag 0BSW: the square of the diagram commutes.** With `A` a normal
local domain with fraction field `K`, `L = K^sep` a separable closure of `K` inside an algebraically
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
one the source draws. That the bottom arrow is the one induced by `Spec A^h → Spec A` is part of
`Stacks.RamificationTheory.inertiaDiagram_translation`, the full statement of Stacks Tag 0BSW. -/
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

/-- **`π₁(X^h) = Gal(κ(𝔪^sh)/κ)`, from Stacks Tag 09ZS, as used in the proof of Tag 0BSW.** For a
henselian local ring `A^h` with residue field `κ` and a separable algebraic closure `κ(𝔪^sh)` of `κ`
inside an algebraically closed algebraic extension `Ω`, the étale fundamental group of
`X^h = Spec A^h` at the geometric point coming from `Ω` is `Gal(κ(𝔪^sh)/κ)`, by the canonical map
induced by the closed immersion `Spec κ → Spec A^h`.

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
statement is not merely an abstract isomorphism of two groups. The identification at the generic
geometric point, compatible with the left vertical arrows of the two diagrams, is part of
`Stacks.RamificationTheory.inertiaDiagram_translation`, the full statement of Stacks Tag 0BSW. -/
@[sga "3 X 4.0" "Recall 4.0, special case"]
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

/-- **Part of Stacks Project, Tag 0BSW: `π₁(U^h) = D`.** In the situation of the source, with
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
embedding. The full statement of Stacks Tag 0BSW is
`Stacks.RamificationTheory.inertiaDiagram_translation`. -/
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

/-- **Part of Stacks Project, Tag 0BSW: `π₁(U^sh) = I`.** With `U^sh = Spec K^sh` for
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
into the assertion about fundamental groups. The full statement of Stacks Tag 0BSW is
`Stacks.RamificationTheory.inertiaDiagram_translation`. -/
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

/-! ### The right vertical arrow and `absoluteGaloisToFundamentalGroup` -/

section RightArrowComparison

attribute [local instance] GeometricPoint.residueFieldAlgebra

/-- **The two descriptions of the right vertical arrow agree.** For a ring `A` with fraction field
`K` (any ring map `A → K` will do) and `X = Spec A` with the geometric point `x̄` induced by
`Spec Ω → Spec K → Spec A`, the right vertical arrow `Gal(K^sep/K) = π₁(U) → π₁(X)`, induced by
`Spec K → Spec A` and read through Stacks Tag 0BNE, is the action of the absolute Galois group of
the residue field of `X` at the image of `x̄` used for Stacks Tag 0BQM
(`AlgebraicGeometry.absoluteGaloisToFundamentalGroup`): every `σ ∈ Gal(K^sep/K)` lifts to an
automorphism `τ` of `Ω` over that residue field, and the two arrows send `σ` and `τ` to the same
element of `π₁(X)`. Through
`Stacks.RamificationTheory.surjective_and_ker_absoluteGaloisToFundamentalGroup` this identifies the
right vertical arrow with restriction `Gal(K^sep/K) → Gal(M/K)`. -/
theorem exists_absoluteGaloisToFundamentalGroup_eq_etaleFundamentalGroupMap
    (A K L Ω : Type u) [CommRing A] [ConnectedSpace (Spec (.of A))]
    [Field K] [Field L] [Field Ω] [Algebra A K] [Algebra K L] [IsSepClosure K L]
    [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (σ : Gal(L/K)) :
    ∃ τ : Gal(((algebraicClosureGeometricPoint K Ω).map
          (Spec.map (CommRingCat.ofHom (algebraMap A K)))).residueField /
        (Spec (.of A)).residueField (((algebraicClosureGeometricPoint K Ω).map
          (Spec.map (CommRingCat.ofHom (algebraMap A K)))).hom default)),
      (∀ y : L, τ (algebraMap L Ω y) = algebraMap L Ω (σ y)) ∧
      absoluteGaloisToFundamentalGroup (Spec (.of A))
          ((algebraicClosureGeometricPoint K Ω).map
            (Spec.map (CommRingCat.ofHom (algebraMap A K)))) τ =
        etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap A K)))
          (algebraicClosureGeometricPoint K Ω) (galoisEquivEtaleFundamentalGroup K L Ω σ) := by
  set f := Spec.map (CommRingCat.ofHom (algebraMap A K))
  set x := algebraicClosureGeometricPoint K Ω
  have : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  have : IsGalois K L := inferInstance
  set τ₀ : Gal(Ω/K) := σ.liftNormal Ω
  have hτ₀ : ∀ y : L, τ₀ (algebraMap L Ω y) = algebraMap L Ω (σ y) := σ.liftNormal_commutes Ω
  -- `τ₀` is an automorphism over the residue field at the image of the geometric point.
  have hK : Spec.map (CommRingCat.ofHom τ₀.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) =
        Spec.map (CommRingCat.ofHom (algebraMap K Ω)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun g => Spec.map (CommRingCat.ofHom g)) (RingHom.ext fun c => τ₀.commutes c)
  have hres : ∀ c, τ₀ (GeometricPoint.residueFieldHom (x.map f) c) =
      GeometricPoint.residueFieldHom (x.map f) c := by
    have h := geometricPoint_factorization (Spec (.of A)) (x.map f)
    have hK' : Spec.map (CommRingCat.ofHom τ₀.toAlgHom.toRingHom) ≫
        (Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ f) =
          Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ f :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ f) hK)
    have h2 : Spec.map (CommRingCat.ofHom τ₀.toAlgHom.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (GeometricPoint.residueFieldHom (x.map f))) =
        Spec.map (CommRingCat.ofHom (GeometricPoint.residueFieldHom (x.map f))) :=
      (cancel_mono ((Spec (.of A)).fromSpecResidueField ((x.map f).hom default))).1
        (((Category.assoc _ _ _).trans
          ((congrArg (Spec.map (CommRingCat.ofHom τ₀.toAlgHom.toRingHom) ≫ ·) h).trans
            hK')).trans h.symm)
    have h3 := Spec.map_injective ((Spec.map_comp _ _).trans h2)
    exact fun c => congrArg (fun g => g.hom c) h3
  let τ : Gal((x.map f).residueField / (Spec (.of A)).residueField ((x.map f).hom default)) :=
    { τ₀.toRingEquiv with commutes' := fun c => hres c }
  refine ⟨τ, hτ₀, ?_⟩
  apply Aut.ext
  apply Iso.ext
  apply NatTrans.ext
  funext Y
  apply ConcreteCategory.hom_ext
  intro p
  apply Subtype.ext
  refine (absoluteGaloisToFundamentalGroup_apply (Spec (.of A)) (x.map f) τ Y p).trans ?_
  obtain ⟨pE, hpE⟩ := (finiteEtaleFiberProjectionEquiv f x Y).surjective p
  have hp : finiteEtaleFiberProjection f x Y pE = p := hpE
  have hp1 : p.1 = pE.1 ≫ Limits.pullback.fst Y.hom f := (congrArg Subtype.val hp).symm
  -- lift the point of the fibre over `Spec K` through `Spec L`
  obtain ⟨y, hy⟩ := (ConcreteCategory.bijective_of_isIso
    ((finiteEtaleFiberIso K L Ω).hom.app ((finiteEtaleBaseChange f).obj Y))).2 pE
  set r := (separableFiberEquiv K L Ω _ y).1
  have hr : pE.1 = Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ r := by
    rw [← hy]
    exact finiteEtaleFiberIso_apply K L Ω _ y
  have hR : (((etaleFundamentalGroupMap f x (galoisEquivEtaleFundamentalGroup K L Ω σ)).asIso.app
      Y).hom p).1 = (Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫
        Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) ≫ r) ≫ Limits.pullback.fst Y.hom f := by
    rw [← hp, ← etaleFundamentalGroupMap_finiteEtaleFiberProjection]
    change (((galoisEquivEtaleFundamentalGroup K L Ω σ).asIso.app _).hom pE).1 ≫
      Limits.pullback.fst Y.hom f = _
    exact congrArg (· ≫ Limits.pullback.fst Y.hom f)
      (galoisEquivEtaleFundamentalGroup_apply K L Ω _ σ pE r hr)
  refine Eq.trans ?_ hR.symm
  rw [hp1, hr]
  have hring : CommRingCat.ofHom (algebraMap L Ω) ≫ CommRingCat.ofHom τ₀.toAlgHom.toRingHom =
      CommRingCat.ofHom σ.toAlgHom.toRingHom ≫ CommRingCat.ofHom (algebraMap L Ω) :=
    CommRingCat.hom_ext (RingHom.ext fun y => hτ₀ y)
  have hcomm : Spec.map (CommRingCat.ofHom τ₀.toAlgHom.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L Ω)) =
      Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫
        Spec.map (CommRingCat.ofHom σ.toAlgHom.toRingHom) :=
    (Spec.map_comp _ _).symm.trans ((congrArg Spec.map hring).trans (Spec.map_comp _ _))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ r ≫ Limits.pullback.fst Y.hom f) hcomm).trans (Category.assoc _ _ _))

end RightArrowComparison

/-! ### The left vertical arrow `π₁(U^h) → π₁(X^h)` and the whole diagram -/

section LeftArrow

open scoped Pointwise

attribute [local instance] GeometricPoint.residueFieldAlgebra

variable (A K L Ω : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
    [Field K] [Field L] [Field Ω]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsFractionRing A K]
    [IsSepClosure K L] [IsSepClosed L]
    [Algebra L Ω] [Algebra K Ω] [IsScalarTower K L Ω] [IsAlgClosed Ω] [Algebra.IsAlgebraic K Ω]
    (q : Ideal (integralClosure A L)) [q.IsPrime] [q.LiesOver (maximalIdeal A)]
    (Ah Kh : Type u) [CommRing Ah] [IsLocalRing Ah] [Algebra A Ah]
    [IsLocalRing.IsHenselization A (ResidueField A) Ah]
    [Field Kh] [Algebra Ah Kh] [IsFractionRing Ah Kh]
    [Algebra A Kh] [IsScalarTower A Ah Kh] [Algebra K Kh] [IsScalarTower A K Kh]
    [Algebra Kh L] [IsScalarTower K Kh L]

omit [IsFractionRing Ah Kh] [Algebra A Kh] [IsScalarTower A Ah Kh] [IsScalarTower A K Kh] in
/-- An automorphism of `K^sep` over `K^h` lies, as an automorphism over `K`, in the decomposition
group `D` at `𝔪^sep`, for the embedding `K^h ⊆ K^sep` induced by the canonical local map
`A^h → (A^sep)_{𝔪^sep}`. -/
theorem restrictScalars_mem_stabilizer_of_henselization
    (hcompat : ∀ x : Ah, algebraMap Kh L (algebraMap Ah Kh x) =
      IsIntegralClosure.henselizationToField A K L q Ah x) (σ : Gal(L/Kh)) :
    letI := IsIntegralClosure.galAction A K L
    σ.restrictScalars K ∈ MulAction.stabilizer Gal(L/K) q := by
  let := IsIntegralClosure.galAction A K L
  refine (IsIntegralClosure.mem_stabilizer_iff_apply_henselizationToField A K L q Ah _).2
    fun x => ?_
  rw [← hcompat x]
  exact σ.commutes _

omit [Algebra A Kh] [IsScalarTower A Ah Kh] [IsScalarTower A K Kh] in
/-- Every element of the decomposition group `D` at `𝔪^sep` is an automorphism of `K^sep` over
`K^h`: restriction of scalars `Gal(K^sep/K^h) → Gal(K^sep/K)` maps onto `D`. -/
theorem exists_restrictScalars_eq_of_mem_stabilizer
    (hcompat : ∀ x : Ah, algebraMap Kh L (algebraMap Ah Kh x) =
      IsIntegralClosure.henselizationToField A K L q Ah x) :
    letI := IsIntegralClosure.galAction A K L
    ∀ τ ∈ MulAction.stabilizer Gal(L/K) q, ∃ σ : Gal(L/Kh), σ.restrictScalars K = τ := by
  let := IsIntegralClosure.galAction A K L
  intro τ hτ
  have h := (IsIntegralClosure.mem_stabilizer_iff_apply_henselizationToField A K L q Ah τ).1 hτ
  have hfix : ∀ z : Kh, τ (algebraMap Kh L z) = algebraMap Kh L z := by
    intro z
    obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (A := Ah) z
    simp only [map_div₀, hcompat, h]
  exact ⟨{ τ.toRingEquiv with commutes' := hfix }, AlgEquiv.ext fun _ => rfl⟩

variable [Algebra Kh Ω] [IsScalarTower Kh L Ω]

/-- Transporting an element of a fundamental group along an equality of base points does not
change its image under an induced map, up to the corresponding transport. -/
private theorem heq_etaleFundamentalGroupMap_of_eq {X Y : Scheme.{u}} [ConnectedSpace X]
    [ConnectedSpace Y] (g : X ⟶ Y) {z z' : GeometricPoint X} (h : z = z')
    (a : EtaleFundamentalGroup X z) :
    HEq (etaleFundamentalGroupMap g z a) (etaleFundamentalGroupMap g z' (h ▸ a)) := by
  subst h
  rfl

omit [Algebra A Kh] [IsScalarTower A Ah Kh] [IsScalarTower A K Kh] in
/-- **The left vertical arrow `π₁(U^h) → π₁(X^h)`, read in `Gal(K^sep/K^h)`.** The map induced
by `Spec K^h → Spec A^h` is surjective, and its kernel, read in `Gal(K^sep/K^h)` through the
identification of Stacks Tag 0BNE, consists of the automorphisms which, as automorphisms over
`K`, lie in the inertia group `I` at `𝔪^sep`.

Both come from the local exact sequence of Stacks Tag 0BSM for the normal local domain `A^h`
(Stacks 06DI), with the strict henselization `A^sh = ((A^sep)_{𝔪^sep})^I` of `A`, which is also
a strict henselization of `A^h` since it is ind-étale over `A^h` (Stacks 08HS). Its fraction
field is `(K^sep)^I`, whose fixing subgroup in `Gal(K^sep/K^h)` is the preimage of `I`, a closed
normal subgroup because `D` normalizes `I`. -/
theorem surjective_and_comap_ker_etaleFundamentalGroupMap_henselization
    [IsSepClosure Kh L] [Algebra.IsAlgebraic Kh Ω]
    (hcompat : ∀ x : Ah, algebraMap Kh L (algebraMap Ah Kh x) =
      IsIntegralClosure.henselizationToField A K L q Ah x) :
    letI : ConnectedSpace (Spec (.of Ah)) := connectedSpace_spec_of_isLocalRing Ah
    letI := IsIntegralClosure.galAction A K L
    Function.Surjective (etaleFundamentalGroupMap
        (Spec.map (CommRingCat.ofHom (algebraMap Ah Kh)))
        (algebraicClosureGeometricPoint Kh Ω)) ∧
      Subgroup.comap (galoisEquivEtaleFundamentalGroup Kh L Ω).toMonoidHom
          (MonoidHom.ker (etaleFundamentalGroupMap
            (Spec.map (CommRingCat.ofHom (algebraMap Ah Kh)))
            (algebraicClosureGeometricPoint Kh Ω)).toMonoidHom) =
        (q.inertia Gal(L/K)).comap (AlgEquiv.restrictScalarsHom K) := by
  let : ConnectedSpace (Spec (.of Ah)) := connectedSpace_spec_of_isLocalRing Ah
  let := IsIntegralClosure.galAction A K L
  let := IsIntegralClosure.galSMulCommClass A K L
  obtain ⟨_, _⟩ := IsIntegralClosure.isDomain_and_isIntegrallyClosed_henselization A Ah
  -- The strict henselization `A^sh = ((A^sep)_{𝔪^sep})^I` as an `A^h`-algebra.
  let ψ : Ah →+* IsIntegralClosure.inertiaInvariants A K L q :=
    (IsIntegralClosure.henselizationToLocalizedSubring A K L q Ah).toRingHom.codRestrict
      (IsIntegralClosure.inertiaInvariants A K L q) fun x =>
        (IsIntegralClosure.mem_inertiaInvariants_iff A K L q _).2 fun σ hσ =>
          IsIntegralClosure.apply_henselizationToField_of_stabilizes A K L q Ah
            (MulAction.mem_stabilizer_iff.mp
              (Ideal.inertia_le_stabilizer (M := Gal(L/K)) q hσ)) x
  let : Algebra Ah (IsIntegralClosure.inertiaInvariants A K L q) := ψ.toAlgebra
  have : IsScalarTower A Ah (IsIntegralClosure.inertiaInvariants A K L q) :=
    .of_algebraMap_eq fun a => Subtype.ext (Subtype.ext
      ((IsIntegralClosure.henselizationToField A K L q Ah).commutes a).symm)
  have : IsLocalHom (algebraMap Ah (IsIntegralClosure.inertiaInvariants A K L q)) :=
    ⟨fun x hx =>
      (IsIntegralClosure.isLocalHom_henselizationToLocalizedSubring A K L q Ah).map_nonunit x
        (hx.map (IsIntegralClosure.inertiaInvariants A K L q).subtype)⟩
  have : IsLocalHom (algebraMap A Ah) :=
    IsLocalRing.IsHenselization.isLocalHom (R := A) (L := ResidueField A) (Rh := Ah)
  obtain ⟨hAsh, hsepAsh⟩ := IsIntegralClosure.isHenselization_inertiaInvariants A K L q
  have hi : StacksDraft.IndEtale Ah (IsIntegralClosure.inertiaInvariants A K L q) :=
    StacksDraft.indEtale_of_comp
      (StacksDraft.indEtale_of_isHenselization (R := A) (ResidueField A) (Rh := Ah))
      (StacksDraft.indEtale_of_isHenselization (R := A)
        (ResidueField (IsIntegralClosure.inertiaInvariants A K L q))
        (Rh := IsIntegralClosure.inertiaInvariants A K L q))
  obtain ⟨alg, hHens, hSep⟩ := StacksDraft.exists_isHenselization_of_indEtale (A := A) (B := Ah)
    (C := IsIntegralClosure.inertiaInvariants A K L q)
    (L := ResidueField (IsIntegralClosure.inertiaInvariants A K L q)) hi
  let := alg
  have := hSep hsepAsh
  -- Its fraction field `K^sh = (K^sep)^I`, as an extension of `K^h`.
  have hmem : ∀ z : Kh, algebraMap Kh L z ∈ IsIntegralClosure.inertiaFixedField A K L q :=
    fun z => (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ => by
      obtain ⟨τ, rfl⟩ := exists_restrictScalars_eq_of_mem_stabilizer A K L q Ah Kh hcompat σ
        (Ideal.inertia_le_stabilizer (M := Gal(L/K)) q hσ)
      exact τ.commutes z
  let : Algebra Kh (IsIntegralClosure.inertiaFixedField A K L q) :=
    ((algebraMap Kh L).codRestrict (IsIntegralClosure.inertiaFixedField A K L q) hmem).toAlgebra
  have : IsScalarTower Kh (IsIntegralClosure.inertiaFixedField A K L q) L :=
    .of_algebraMap_eq fun _ => rfl
  let : Algebra Ah (IsIntegralClosure.inertiaFixedField A K L q) :=
    ((algebraMap (IsIntegralClosure.inertiaInvariants A K L q)
      (IsIntegralClosure.inertiaFixedField A K L q)).comp
        (algebraMap Ah (IsIntegralClosure.inertiaInvariants A K L q))).toAlgebra
  have : IsScalarTower Ah (IsIntegralClosure.inertiaInvariants A K L q)
      (IsIntegralClosure.inertiaFixedField A K L q) := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower Ah Kh (IsIntegralClosure.inertiaFixedField A K L q) :=
    .of_algebraMap_eq fun x => Subtype.ext (hcompat x).symm
  let : IsFractionRing (IsIntegralClosure.inertiaInvariants A K L q)
      (IsIntegralClosure.inertiaFixedField A K L q : Type u) :=
    IsIntegralClosure.isFractionRing_inertiaFixedField A K L q
  obtain ⟨_, _⟩ := isSepClosure_and_isAlgebraic_of_tower (K := K)
    (Kh := (IsIntegralClosure.inertiaFixedField A K L q : Type u)) (L := L) (Ω := Ω)
  -- The fixing subgroup of `K^sh` in `Gal(K^sep/K^h)` is the preimage of `I`.
  have hS : (IsScalarTower.toAlgHom Kh (IsIntegralClosure.inertiaFixedField A K L q)
        L).fieldRange.fixingSubgroup =
      (q.inertia Gal(L/K)).comap (AlgEquiv.restrictScalarsHom K) := by
    ext σ
    rw [Subgroup.mem_comap, ← IsIntegralClosure.fixingSubgroup_inertiaFixedField A K L q,
      IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h y hy
      exact h y ⟨⟨y, hy⟩, rfl⟩
    · rintro h _ ⟨y, rfl⟩
      exact h y y.2
  have hnormal : ((q.inertia Gal(L/K)).comap
      (AlgEquiv.restrictScalarsHom K : Gal(L/Kh) →* Gal(L/K))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hD : (g.restrictScalars K) • q = q := MulAction.mem_stabilizer_iff.mp
      (restrictScalars_mem_stabilizer_of_henselization A K L q Ah Kh hcompat g)
    have h := Ideal.inertia_smul (M := Gal(L/K)) (g.restrictScalars K) q
    rw [hD] at h
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv, h]
    exact ⟨_, hn, rfl⟩
  have hclosed : IsClosed (((q.inertia Gal(L/K)).comap
      (AlgEquiv.restrictScalarsHom K : Gal(L/Kh) →* Gal(L/K))) : Set Gal(L/Kh)) := by
    rw [← hS]
    exact InfiniteGalois.fixingSubgroup_isClosed _
  obtain ⟨hx', -⟩ := galoisEquivEtaleFundamentalGroup_naturality Kh
    (IsIntegralClosure.inertiaFixedField A K L q : Type u) L Ω
  have hexact := isExactSequence_etaleFundamentalGroupMap_fractionField_of_isHenselization Ah
    (IsIntegralClosure.inertiaInvariants A K L q)
    (ResidueField (IsIntegralClosure.inertiaInvariants A K L q)) Kh
    (IsIntegralClosure.inertiaFixedField A K L q : Type u)
    (algebraicClosureGeometricPoint (IsIntegralClosure.inertiaFixedField A K L q : Type u) Ω)
  refine ⟨?_, ?_⟩
  · have key : ∀ z (hz : (algebraicClosureGeometricPoint
          (IsIntegralClosure.inertiaFixedField A K L q : Type u) Ω).map
          (Spec.map (CommRingCat.ofHom (algebraMap Kh
            (IsIntegralClosure.inertiaFixedField A K L q)))) = z),
        Function.Surjective (etaleFundamentalGroupMap
          (Spec.map (CommRingCat.ofHom (algebraMap Ah Kh))) z) := by
      rintro z rfl
      exact hexact.1
    exact key _ hx'
  · rw [comap_ker_etaleFundamentalGroupMap_eq_normalClosure_fixingSubgroup Ah Kh
      (IsIntegralClosure.inertiaFixedField A K L q : Type u) L Ω (fun z hz => by
        subst hz
        exact hexact.2.2), hS, Subgroup.normalClosure_eq_self]
    exact le_antisymm (Subgroup.topologicalClosure_minimal _ le_rfl hclosed)
      (Subgroup.le_topologicalClosure _)

/-- Two surjections out of the same group with the same kernel differ by a unique isomorphism of
their targets. -/
private theorem exists_mulEquiv_comp_eq_of_ker_eq {G H₁ H₂ : Type*} [Group G] [Group H₁]
    [Group H₂] (f : G →* H₁) (g : G →* H₂) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (h : f.ker = g.ker) :
    ∃ e : H₁ ≃* H₂, ∀ x, e (f x) = g x := by
  refine ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq h).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)), fun x => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply,
    show (QuotientGroup.quotientKerEquivOfSurjective f hf).symm (f x) = (x : G ⧸ f.ker) from
      (MulEquiv.symm_apply_eq _).2 rfl, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

omit [IsSepClosed L] [Algebra Kh L] [IsScalarTower K Kh L] [Algebra Kh Ω] [IsScalarTower Kh L Ω]
  in
include q in
/-- The right vertical arrow `Gal(K^sep/K) = π₁(U) → π₁(X)` is surjective, by the local exact
sequence of Stacks Tag 0BSM. -/
theorem surjective_etaleFundamentalGroupMap_fractionField_comp_galoisEquiv :
    letI : ConnectedSpace (Spec (.of A)) := connectedSpace_spec_of_isLocalRing A
    Function.Surjective (fun σ : Gal(L/K) =>
      etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap A K)))
        (algebraicClosureGeometricPoint K Ω) (galoisEquivEtaleFundamentalGroup K L Ω σ)) := by
  let : ConnectedSpace (Spec (.of A)) := connectedSpace_spec_of_isLocalRing A
  let := IsIntegralClosure.galAction A K L
  have : IsSepClosed L := IsSepClosure.sep_closed K
  let : IsFractionRing (IsIntegralClosure.inertiaInvariants A K L q)
      (IsIntegralClosure.inertiaFixedField A K L q : Type u) :=
    IsIntegralClosure.isFractionRing_inertiaFixedField A K L q
  obtain ⟨_, _⟩ := IsIntegralClosure.isHenselization_inertiaInvariants A K L q
  obtain ⟨_, _⟩ := isSepClosure_and_isAlgebraic_of_tower (K := K)
    (Kh := (IsIntegralClosure.inertiaFixedField A K L q : Type u)) (L := L) (Ω := Ω)
  have key : ∀ z (hz : (algebraicClosureGeometricPoint
        (IsIntegralClosure.inertiaFixedField A K L q : Type u) Ω).map
        (Spec.map (CommRingCat.ofHom (algebraMap K
          (IsIntegralClosure.inertiaFixedField A K L q)))) = z),
      Function.Surjective (etaleFundamentalGroupMap
        (Spec.map (CommRingCat.ofHom (algebraMap A K))) z) := by
    rintro z rfl
    exact (isExactSequence_etaleFundamentalGroupMap_fractionField_of_isHenselization A
      (IsIntegralClosure.inertiaInvariants A K L q)
      (ResidueField (IsIntegralClosure.inertiaInvariants A K L q)) K
      (IsIntegralClosure.inertiaFixedField A K L q : Type u) _).1
  obtain ⟨hxK, -⟩ := galoisEquivEtaleFundamentalGroup_naturality K
    (IsIntegralClosure.inertiaFixedField A K L q : Type u) L Ω
  intro ρ
  obtain ⟨γ, hγ⟩ := key _ hxK ρ
  obtain ⟨σ, rfl⟩ := (galoisEquivEtaleFundamentalGroup K L Ω).surjective γ
  exact ⟨σ, hγ⟩

omit [Algebra A Kh] [IsScalarTower A Ah Kh] [IsScalarTower A K Kh] in
/-- **`π₁(X^h) = Gal(κ(𝔪^sh)/κ)`, compatibly with the left vertical arrows.** There is an
isomorphism `Gal(κ(𝔪^sh)/κ) ≅ π₁(X^h)` carrying the left vertical arrow `D → Gal(κ(𝔪^sh)/κ)` of
the Galois diagram to the arrow `π₁(U^h) → π₁(X^h)`, where `σ ∈ Gal(K^sep/K^h) = π₁(U^h)` is
viewed in `D` by restriction of scalars. Both arrows are surjective with kernel `I`
(`Stacks.RamificationTheory.ker_decompositionResidueHom` and
`Stacks.RamificationTheory.surjective_and_comap_ker_etaleFundamentalGroupMap_henselization`). -/
theorem exists_mulEquiv_etaleFundamentalGroup_henselization [q.IsMaximal]
    [IsSepClosure Kh L] [Algebra.IsAlgebraic Kh Ω]
    (hcompat : ∀ x : Ah, algebraMap Kh L (algebraMap Ah Kh x) =
      IsIntegralClosure.henselizationToField A K L q Ah x)
    (κ : Type uk) [Field κ] [Algebra (A ⧸ maximalIdeal A) κ]
      [IsFractionRing (A ⧸ maximalIdeal A) κ]
    (κmsep : Type ul) [Field κmsep] [Algebra (integralClosure A L ⧸ q) κmsep]
      [IsFractionRing (integralClosure A L ⧸ q) κmsep]
      [Algebra (A ⧸ maximalIdeal A) κmsep]
      [IsScalarTower (A ⧸ maximalIdeal A) (integralClosure A L ⧸ q) κmsep]
      [Algebra κ κmsep] [IsScalarTower (A ⧸ maximalIdeal A) κ κmsep]
    (κmsh : Type us) [Field κmsh] [Algebra κ κmsh] [IsSepClosure κ κmsh]
      [Algebra κmsh κmsep] [IsScalarTower κ κmsh κmsep] :
    letI : ConnectedSpace (Spec (.of Ah)) := connectedSpace_spec_of_isLocalRing Ah
    letI := IsIntegralClosure.isFractionRing_integralClosure A K L
    letI := IsIntegralClosure.galAction A K L
    letI := IsIntegralClosure.galSMulCommClass A K L
    ∃ e : Gal(κmsh/κ) ≃* EtaleFundamentalGroup (Spec (.of Ah))
        ((algebraicClosureGeometricPoint Kh Ω).map
          (Spec.map (CommRingCat.ofHom (algebraMap Ah Kh)))),
      ∀ σ : Gal(L/Kh),
        e (decompositionResidueHom A K L (integralClosure A L) q κ κmsep κmsh
            ⟨σ.restrictScalars K,
              restrictScalars_mem_stabilizer_of_henselization A K L q Ah Kh hcompat σ⟩) =
          etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap Ah Kh)))
            (algebraicClosureGeometricPoint Kh Ω) (galoisEquivEtaleFundamentalGroup Kh L Ω σ) := by
  let : ConnectedSpace (Spec (.of Ah)) := connectedSpace_spec_of_isLocalRing Ah
  let := IsIntegralClosure.isFractionRing_integralClosure A K L
  let := IsIntegralClosure.galAction A K L
  let := IsIntegralClosure.galSMulCommClass A K L
  obtain ⟨hφ, hker⟩ :=
    surjective_and_comap_ker_etaleFundamentalGroupMap_henselization A K L Ω q Ah Kh hcompat
  let rD : Gal(L/Kh) →* MulAction.stabilizer Gal(L/K) q :=
    (AlgEquiv.restrictScalarsHom K).codRestrict _
      (restrictScalars_mem_stabilizer_of_henselization A K L q Ah Kh hcompat)
  have hrD : Function.Surjective rD := fun τ => by
    obtain ⟨σ, hσ⟩ := exists_restrictScalars_eq_of_mem_stabilizer A K L q Ah Kh hcompat τ τ.2
    exact ⟨σ, Subtype.ext hσ⟩
  let f := decompositionResidueHom A K L (integralClosure A L) q κ κmsep κmsh
  let g := (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap Ah Kh)))
    (algebraicClosureGeometricPoint Kh Ω)).toMonoidHom.comp
      (galoisEquivEtaleFundamentalGroup Kh L Ω).toMonoidHom
  have hf : Function.Surjective (f.comp rD) :=
    (surjective_decompositionResidueHom A K L (integralClosure A L) q κ κmsep κmsh).comp hrD
  have hg : Function.Surjective g := fun y => by
    obtain ⟨γ, rfl⟩ := hφ y
    obtain ⟨σ, rfl⟩ := (galoisEquivEtaleFundamentalGroup Kh L Ω).surjective γ
    exact ⟨σ, rfl⟩
  have hkk : (f.comp rD).ker = g.ker := by
    rw [← MonoidHom.comap_ker, ← MonoidHom.comap_ker,
      ker_decompositionResidueHom A K L (integralClosure A L) q κ κmsep κmsh, hker]
    ext σ
    exact Ideal.coe_mem_inertia.symm
  obtain ⟨e, he⟩ := exists_mulEquiv_comp_eq_of_ker_eq _ _ hf hg hkk
  exact ⟨e, he⟩

omit [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A] [IsFractionRing A K] [IsSepClosed L]
  [Algebra A L] [IsScalarTower A K L] [Algebra Ah Kh] [IsFractionRing Ah Kh] [Algebra A Kh]
  [IsScalarTower A Ah Kh] [IsScalarTower A K Kh] [IsLocalRing Ah] [Algebra A Ah] in
/-- The top arrow `π₁(U^h) → π₁(U)` is injective, since `Gal(K^sep/K^h) → Gal(K^sep/K)` is. -/
theorem injective_etaleFundamentalGroupMap_fractionField_tower [IsSepClosure Kh L]
    [IsScalarTower K Kh Ω] [Algebra.IsAlgebraic Kh Ω]
    (hx : (algebraicClosureGeometricPoint Kh Ω).map
        (Spec.map (CommRingCat.ofHom (algebraMap K Kh))) = algebraicClosureGeometricPoint K Ω) :
    Function.Injective (fun γ : EtaleFundamentalGroup (Spec (.of Kh))
        (algebraicClosureGeometricPoint Kh Ω) =>
      hx ▸ etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap K Kh)))
        (algebraicClosureGeometricPoint Kh Ω) γ) := by
  obtain ⟨_, hn⟩ := galoisEquivEtaleFundamentalGroup_naturality K Kh L Ω
  intro γ γ' hγγ'
  obtain ⟨σ, rfl⟩ := (galoisEquivEtaleFundamentalGroup Kh L Ω).surjective γ
  obtain ⟨σ', rfl⟩ := (galoisEquivEtaleFundamentalGroup Kh L Ω).surjective γ'
  have h' := (galoisEquivEtaleFundamentalGroup K L Ω).injective
    ((hn σ).symm.trans (hγγ'.trans (hn σ')))
  congr 1
  exact AlgEquiv.ext fun x => DFunLike.congr_fun h' x

omit [IsSepClosed L] in
/-- **Stacks Project, Tag 0BSW.** Let `(A, 𝔪, κ)` be a normal local domain with fraction field
`K`, let `K^sep = L` be a separable closure of `K` inside an algebraically closed algebraic
extension `Ω`, let `A^sep` be the integral closure of `A` in `K^sep` and `𝔪^sep = q` a maximal
ideal of `A^sep` over `𝔪`, with decomposition group `D` and inertia group `I` in
`G = Gal(K^sep/K)`. Let `A^h` be a henselization of `A` with fraction field `K^h`, embedded in
`K^sep` through the canonical local map `A^h → (A^sep)_{𝔪^sep}` (`hcompat`), let `κ(𝔪^sh)` be a
separable algebraic closure of `κ` inside `κ(𝔪^sep)`, and write `U = Spec K`, `U^h = Spec K^h`,
`X = Spec A`, `X^h = Spec A^h`. Then, via the isomorphism `π₁(U) = Gal(K^sep/K)` of Stacks Tag
0BNE, the diagram

```
π₁(U^sh) → π₁(U^h) → π₁(U)
             ↓         ↓
          π₁(X^h) →  π₁(X)
```

translates into

```
I → D → Gal(K^sep/K)
    ↓        ↓
 Gal(κ(𝔪^sh)/κ) → π₁(X)
```

in the following sense, objects and arrows alike:

* the top arrow `π₁(U^h) → π₁(U)` is injective with image `D` (so `π₁(U^h) = D`, the arrow
  being the inclusion), and the image of `π₁(U^sh)` in `π₁(U)` is `I`, for
  `U^sh = Spec (K^sep)^I` the spectrum of the fraction field of the strict henselization
  `A^sh = ((A^sep)_{𝔪^sep})^I`;
* the left vertical arrow `D → Gal(κ(𝔪^sh)/κ)` (`decompositionResidueHom`) is surjective with
  kernel `I`, so the diagonal `I → Gal(κ(𝔪^sh)/κ)` is trivial;
* there is an isomorphism `e : Gal(κ(𝔪^sh)/κ) ≅ π₁(X^h)` carrying the left vertical arrow to the
  arrow `π₁(U^h) → π₁(X^h)`: for `γ ∈ π₁(U^h)` corresponding to `τ ∈ D`, `e(τ̄) = γ|_{X^h}`;
  this is the identification `π₁(X^h) = Gal(κ(𝔪^sh)/κ)` of the lower left corner, and `e` is
  determined by this property since the left arrow is surjective;
* under `e` the bottom arrow `π₁(X^h) → π₁(X)` becomes the bottom arrow `Gal(κ(𝔪^sh)/κ) → π₁(X)`
  of the translated diagram, i.e. the square commutes: for `τ ∈ D`, the image of `e(τ̄)` in
  `π₁(X)` is the image of `τ` under the right vertical arrow (a heterogeneous equality, the two
  geometric points of `X` being equal only propositionally);
* the right vertical arrow `Gal(K^sep/K) = π₁(U) → π₁(X)` is surjective, and its kernel is the
  smallest closed normal subgroup of `Gal(K^sep/K)` containing `I`.
* the right vertical arrow is the arrow `absoluteGaloisToFundamentalGroup` of Stacks Tag 0BQM:
  every `σ ∈ Gal(K^sep/K)` lifts to an automorphism `τ` of `Ω` over the residue field of `X` at
  the generic point, and both arrows send them to the same element of `π₁(X)`.

The lower right corner `π₁(X)` is `Gal(M/K)` for `M` the maximal subextension of `K^sep/K`
unramified with respect to `A` by Stacks Tag 0BQM, which in this library is
`AlgebraicGeometry.fundamentalGroupIsoGalMaximalEtaleExtension`, carrying
`absoluteGaloisToFundamentalGroup` to restriction to `M`
(`Stacks.RamificationTheory.surjective_and_ker_absoluteGaloisToFundamentalGroup`); the last
clause on the right vertical arrow identifies it with that arrow, so under Tag 0BQM the right
vertical arrow is restriction `Gal(K^sep/K) → Gal(M/K)`.

The hypotheses are the source's: `A` a normal local domain, `K^sep` a separable closure of `K`,
`𝔪^sep` a maximal ideal over `𝔪`, `A^h` a henselization, `κ(𝔪^sh)` a separable closure of `κ`;
`K^sep` being separably closed, which the canonical map `A^h → (A^sep)_{𝔪^sep}` needs, is derived
from it being a separable closure. -/
@[stacks 0BSW "the whole translated diagram: π₁(U^h) = D with the top arrow the inclusion, the \
image I of π₁(U^sh), the left vertical arrow D → Gal(κ(𝔪^sh)/κ) surjective with kernel I and \
identified with π₁(U^h) → π₁(X^h) through an isomorphism Gal(κ(𝔪^sh)/κ) ≅ π₁(X^h), the bottom \
arrow and the commutative square, and the right vertical arrow surjective with kernel the \
smallest closed normal subgroup containing I and equal to absoluteGaloisToFundamentalGroup, the \
arrow which Tag 0BQM identifies with restriction Gal(K^sep/K) → Gal(M/K)"]
theorem inertiaDiagram_translation [q.IsMaximal]
    (hcompat : letI : IsSepClosed L := IsSepClosure.sep_closed K
      ∀ x : Ah, algebraMap Kh L (algebraMap Ah Kh x) =
        IsIntegralClosure.henselizationToField A K L q Ah x)
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
    letI : ConnectedSpace (Spec (.of Ah)) := connectedSpace_spec_of_isLocalRing Ah
    letI := IsIntegralClosure.isFractionRing_integralClosure A K L
    letI := IsIntegralClosure.galAction A K L
    letI := IsIntegralClosure.galSMulCommClass A K L
    ∃ hx : (algebraicClosureGeometricPoint Kh Ω).map
        (Spec.map (CommRingCat.ofHom (algebraMap K Kh))) = algebraicClosureGeometricPoint K Ω,
      -- the top row: `π₁(U^h) = D`, the top arrow being the inclusion
      (galoisEquivEtaleFundamentalGroup K L Ω) ⁻¹'
          Set.range (fun γ : EtaleFundamentalGroup (Spec (.of Kh))
              (algebraicClosureGeometricPoint Kh Ω) =>
            hx ▸ etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap K Kh)))
              (algebraicClosureGeometricPoint Kh Ω) γ) =
        (MulAction.stabilizer Gal(L/K) q : Set Gal(L/K)) ∧
      Function.Injective (fun γ : EtaleFundamentalGroup (Spec (.of Kh))
          (algebraicClosureGeometricPoint Kh Ω) =>
        hx ▸ etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap K Kh)))
          (algebraicClosureGeometricPoint Kh Ω) γ) ∧
      -- the top row: the image of `π₁(U^sh)` is `I`
      (∃ hx' : (algebraicClosureGeometricPoint
            (IsIntegralClosure.inertiaFixedField A K L q : Type u) Ω).map
            (Spec.map (CommRingCat.ofHom (algebraMap K
              (IsIntegralClosure.inertiaFixedField A K L q : Type u)))) =
          algebraicClosureGeometricPoint K Ω,
        (galoisEquivEtaleFundamentalGroup K L Ω) ⁻¹'
            Set.range (fun τ : EtaleFundamentalGroup
                (Spec (.of (IsIntegralClosure.inertiaFixedField A K L q : Type u)))
                (algebraicClosureGeometricPoint
                  (IsIntegralClosure.inertiaFixedField A K L q : Type u) Ω) =>
              hx' ▸ etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap K
                  (IsIntegralClosure.inertiaFixedField A K L q : Type u))))
                (algebraicClosureGeometricPoint
                  (IsIntegralClosure.inertiaFixedField A K L q : Type u) Ω) τ) =
          (q.inertia Gal(L/K) : Set Gal(L/K))) ∧
      -- the left vertical arrow `D → Gal(κ(𝔪^sh)/κ)`: surjective with kernel `I`
      Function.Surjective (decompositionResidueHom A K L (integralClosure A L) q κ κmsep κmsh) ∧
      (decompositionResidueHom A K L (integralClosure A L) q κ κmsep κmsh).ker =
        q.inertia (MulAction.stabilizer Gal(L/K) q) ∧
      -- the right vertical arrow: surjective, kernel the closed normal subgroup generated by `I`
      Function.Surjective (fun σ : Gal(L/K) =>
        etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap A K)))
          (algebraicClosureGeometricPoint K Ω) (galoisEquivEtaleFundamentalGroup K L Ω σ)) ∧
      Subgroup.comap (galoisEquivEtaleFundamentalGroup K L Ω).toMonoidHom
          (MonoidHom.ker (etaleFundamentalGroupMap
            (Spec.map (CommRingCat.ofHom (algebraMap A K)))
            (algebraicClosureGeometricPoint K Ω)).toMonoidHom) =
        (Subgroup.normalClosure
          ((q.inertia Gal(L/K) : Subgroup Gal(L/K)) : Set Gal(L/K))).topologicalClosure ∧
      -- the right vertical arrow is the arrow `absoluteGaloisToFundamentalGroup` of Tag 0BQM,
      -- whose target is `Gal(M/K)` through `fundamentalGroupIsoGalMaximalEtaleExtension`
      (∀ σ : Gal(L/K), ∃ τ : Gal(((algebraicClosureGeometricPoint K Ω).map
            (Spec.map (CommRingCat.ofHom (algebraMap A K)))).residueField /
          (Spec (.of A)).residueField (((algebraicClosureGeometricPoint K Ω).map
            (Spec.map (CommRingCat.ofHom (algebraMap A K)))).hom default)),
        (∀ y : L, τ (algebraMap L Ω y) = algebraMap L Ω (σ y)) ∧
        absoluteGaloisToFundamentalGroup (Spec (.of A))
            ((algebraicClosureGeometricPoint K Ω).map
              (Spec.map (CommRingCat.ofHom (algebraMap A K)))) τ =
          etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap A K)))
            (algebraicClosureGeometricPoint K Ω) (galoisEquivEtaleFundamentalGroup K L Ω σ)) ∧
      -- `π₁(X^h) = Gal(κ(𝔪^sh)/κ)`, carrying the left arrows to each other, and the square
      ∃ e : Gal(κmsh/κ) ≃* EtaleFundamentalGroup (Spec (.of Ah))
          ((algebraicClosureGeometricPoint Kh Ω).map
            (Spec.map (CommRingCat.ofHom (algebraMap Ah Kh)))),
        ∀ (γ : EtaleFundamentalGroup (Spec (.of Kh)) (algebraicClosureGeometricPoint Kh Ω))
          (τ : MulAction.stabilizer Gal(L/K) q),
          galoisEquivEtaleFundamentalGroup K L Ω τ =
              hx ▸ etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap K Kh)))
                (algebraicClosureGeometricPoint Kh Ω) γ →
            e (decompositionResidueHom A K L (integralClosure A L) q κ κmsep κmsh τ) =
                etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap Ah Kh)))
                  (algebraicClosureGeometricPoint Kh Ω) γ ∧
              HEq (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap A Ah)))
                  ((algebraicClosureGeometricPoint Kh Ω).map
                    (Spec.map (CommRingCat.ofHom (algebraMap Ah Kh))))
                  (e (decompositionResidueHom A K L (integralClosure A L) q κ κmsep κmsh τ)))
                (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom (algebraMap A K)))
                  (algebraicClosureGeometricPoint K Ω)
                  (galoisEquivEtaleFundamentalGroup K L Ω τ)) := by
  let : ConnectedSpace (Spec (.of A)) := connectedSpace_spec_of_isLocalRing A
  let : ConnectedSpace (Spec (.of Ah)) := connectedSpace_spec_of_isLocalRing Ah
  let := IsIntegralClosure.isFractionRing_integralClosure A K L
  let := IsIntegralClosure.galAction A K L
  let := IsIntegralClosure.galSMulCommClass A K L
  have : IsSepClosed L := IsSepClosure.sep_closed K
  have : IsScalarTower K Kh Ω := .of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply K L Ω, IsScalarTower.algebraMap_apply K Kh L,
      ← IsScalarTower.algebraMap_apply Kh L Ω]
  obtain ⟨_, _⟩ := isSepClosure_and_isAlgebraic_of_tower (K := K) (Kh := Kh) (L := L) (Ω := Ω)
  obtain ⟨hx, hn⟩ := galoisEquivEtaleFundamentalGroup_naturality K Kh L Ω
  obtain ⟨e, he⟩ := exists_mulEquiv_etaleFundamentalGroup_henselization A K L Ω q Ah Kh hcompat
    κ κmsep κmsh
  refine ⟨hx, ?_, ?_, galoisEquiv_preimage_range_etaleFundamentalGroupMap_inertia A K L Ω q,
    surjective_decompositionResidueHom A K L (integralClosure A L) q κ κmsep κmsh,
    ker_decompositionResidueHom A K L (integralClosure A L) q κ κmsep κmsh,
    surjective_etaleFundamentalGroupMap_fractionField_comp_galoisEquiv A K L Ω q,
    comap_ker_etaleFundamentalGroupMap_eq_normalClosure_inertia A K L Ω q,
    exists_absoluteGaloisToFundamentalGroup_eq_etaleFundamentalGroupMap A K L Ω, e,
    fun γ τ hγ => ?_⟩
  · obtain ⟨_, h₀⟩ :=
      galoisEquiv_preimage_range_etaleFundamentalGroupMap_decomposition A K L Ω q Ah Kh hcompat
    exact h₀
  · exact injective_etaleFundamentalGroupMap_fractionField_tower K L Ω Kh hx
  · obtain ⟨σ, rfl⟩ := (galoisEquivEtaleFundamentalGroup Kh L Ω).surjective γ
    have hτ : τ = ⟨σ.restrictScalars K,
        restrictScalars_mem_stabilizer_of_henselization A K L q Ah Kh hcompat σ⟩ :=
      Subtype.ext ((galoisEquivEtaleFundamentalGroup K L Ω).injective (hγ.trans (hn σ)))
    have hleft := he σ
    rw [← hτ] at hleft
    refine ⟨hleft, ?_⟩
    rw [hleft, hγ]
    exact (etaleFundamentalGroupMap_inertiaSquare A Ah K Kh _ _).symm.trans
      (heq_etaleFundamentalGroupMap_of_eq _ hx _)

end LeftArrow

end Henselian

end Stacks.RamificationTheory

end
