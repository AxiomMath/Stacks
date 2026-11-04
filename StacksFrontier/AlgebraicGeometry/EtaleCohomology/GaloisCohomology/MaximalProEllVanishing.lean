module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.MaximalProPSubgroup
import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.ExtComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.SeparableClosureModules

/-!
# Vanishing of étale cohomology of a field and maximal pro-`ℓ` subgroups

Let `ℓ` be a prime and `n` a natural number. Let `K` be a field with separable closure `Kˢᵉᵖ` and
absolute Galois group `G = Gal(Kˢᵉᵖ/K)`, let `H ⊆ G` be a maximal pro-`ℓ` subgroup and let
`L = (Kˢᵉᵖ)ᴴ` be the corresponding field extension of `K`. Then `Hⁿ_ét(Spec K, 𝓕) = 0` for all
`ℓ`-power torsion abelian sheaves `𝓕` on the small étale site of `Spec K` if and only if
`Hⁿ_ét(Spec L, ℤ/ℓℤ) = 0`.

Under the equivalence between abelian sheaves on the small étale site of the spectrum of a field
and discrete modules over its absolute Galois group
(`AlgebraicGeometry.fieldEtaleSheafEquiv`), étale cohomology is Galois cohomology
(`AlgebraicGeometry.subsingleton_sheafH_iff`), `ℓ`-power torsion sheaves correspond to `ℓ`-power
torsion modules, and the constant sheaf `ℤ/ℓℤ` corresponds to the trivial module `ℤ/ℓℤ`. The
absolute Galois group of `L` is `H`, as a topological group
(`InfiniteGalois.fixedFieldGalContinuousMulEquiv`). The statement is thus
`Stacks.GroupCohomology.subsingleton_ext_iff_of_isMaximalProPSubgroup`.

The same condition `Hⁿ_ét(Spec L, ℤ/ℓℤ) = 0` is equivalent to the vanishing of
`H^q_ét(Spec K, 𝓕)` for all `q ≥ n` and all `ℓ`-power torsion sheaves `𝓕`, and to the vanishing
for all `q ≥ n` and all sheaves `𝓕` killed by `ℓ` ([Stacks, Tag 0DV9]): vanishing in degree `n`
for all `ℓ`-power torsion coefficients propagates to higher degrees by dimension shifting
(`Stacks.GroupCohomology.subsingleton_ext_of_le`), and the converse direction of Tag 0DV8 only
uses a coinduced module, which is killed by `ℓ`.

## Main results

* `AlgebraicGeometry.subsingleton_sheafH_constant_fixedField_iff`: `Hⁿ_ét(Spec L, ℤ/ℓℤ)` is the
  cohomology of `H` with coefficients `ℤ/ℓℤ`, for any closed subgroup `H`.
* `AlgebraicGeometry.subsingleton_sheafH_iff_of_isMaximalProPSubgroup`: [Stacks, Tag 0DV8].
* `AlgebraicGeometry.tfae_subsingleton_sheafH_of_isMaximalProPSubgroup`: [Stacks, Tag 0DV9].
* `AlgebraicGeometry.forall_le_subsingleton_sheafH_iff_of_isMaximalProPSubgroup`: its
  `ℓ`-power torsion form.

## Implementation notes

The sources assume `n > 0`; the statements hold, with the same proofs, in every degree, so no
assumption on `n` is made. The statement of [Stacks, Tag 0DV9] speaks of `ℓ`-torsion sheaves and
its proof of `ℓ`-power torsion sheaves; both readings are covered, as the first two conditions of
`AlgebraicGeometry.tfae_subsingleton_sheafH_of_isMaximalProPSubgroup`, a sheaf killed by `ℓ`
being one with `ℓ • 𝟙 𝓕 = 0`. Étale cohomology is Mathlib's `CategoryTheory.Sheaf.H` on the small
étale sites, for an arbitrary choice of `Ext` groups, and `ℓ`-power torsion is
`Stacks.Torsion.IsPrimePowerTorsion`: every local section is locally killed by a power of `ℓ`.

The proof follows the group-theoretic route rather than the étale one of the source (which
writes `Spec L` as a limit of finite étale covers of degree prime to `ℓ` and uses the trace
method, [Stacks, Tag 0DV7]): restriction from `G` to `H` is injective on cohomology with
`ℓ`-power torsion coefficients because every open subgroup containing `H` has index prime to
`ℓ`, and the cohomology of the pro-`ℓ` group `H` is controlled by `Hⁿ(H, ℤ/ℓℤ)` by dévissage.

## References

* [Stacks Project, Tag 0DV8](https://stacks.math.columbia.edu/tag/0DV8)
* [Stacks Project, Tag 0DV9](https://stacks.math.columbia.edu/tag/0DV9)
-/

@[expose] public noncomputable section

open CategoryTheory Limits IntermediateField

universe v u

namespace AlgebraicGeometry

variable {ℓ : ℕ} (K Ksep : Type u) [Field K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
  {H : Subgroup Gal(Ksep/K)}

/-- The category of continuous discrete `G`-modules has `Ext` groups in the universe used here. -/
private lemma hasExt_continuousGModule (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : HasExt.{max (u + 1) v} (ContinuousGModule.{u, max (u + 1) v} G) :=
  Stacks.ContinuousCohomology.hasExt_continuousModule.{0, u, max (u + 1) v} ℤ _

/-- **The étale cohomology of the fixed field of a closed subgroup with coefficients `ℤ/ℓℤ` is
the cohomology of the subgroup.** For a closed subgroup `H` of `Gal(Kˢᵉᵖ/K)` with fixed field `L`,
`Hⁿ_ét(Spec L, ℤ/ℓℤ)` vanishes if and only if `Hⁿ(H, ℤ/ℓℤ)` does. -/
theorem subsingleton_sheafH_constant_fixedField_iff (hH : IsClosed (H : Set Gal(Ksep/K)))
    (n : ℕ) [HasExt (Sheaf (Spec (.of (fixedField H))).smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{max (u + 1) v} (ContinuousGModule.{u, max (u + 1) v} H)] :
    Subsingleton (Sheaf.H ((constantSheaf (Spec (.of (fixedField H))).smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod ℓ))))
          n) ↔
      Subsingleton (Abelian.Ext
        (Stacks.GroupCohomology.trivialGModule.{u, max (u + 1) v} H (ULift.{max (u + 1) v} ℤ))
        (Stacks.GroupCohomology.trivialGModule H (ULift.{max (u + 1) v} (ZMod ℓ))) n) := by
  let L := fixedField H
  let HC : ClosedSubgroup Gal(Ksep/K) := ⟨H, hH⟩
  have : IsSepClosure L Ksep :=
    ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K L Ksep⟩
  have := hasExt_continuousGModule.{v} Gal(Ksep/L)
  rw [subsingleton_sheafH_iff.{v} L Ksep]
  refine (Equiv.subsingleton_congr ((Abelian.extFunctorObj _ n).mapIso
    ((fieldEtaleSheafEquivConstantIso.{v} L Ksep).app _)).addCommGroupIsoToAddEquiv.toEquiv).trans
    ?_
  exact subsingleton_ext_trivialGModule_iff.{v}
    (InfiniteGalois.fixedFieldGalContinuousMulEquiv HC) (ULift.{max (u + 1) v} (ZMod ℓ)) n

/-- Let `H` be a closed subgroup of `Gal(Kˢᵉᵖ/K)` with fixed field `L`. If `Hⁿ_ét(Spec K, 𝓕)`
vanishes for every abelian sheaf `𝓕` on the small étale site of `Spec K` killed by `ℓ`, then
`Hⁿ_ét(Spec L, ℤ/ℓℤ)` vanishes: by Shapiro's lemma it is `Hⁿ(Spec K, 𝓕)` for the sheaf `𝓕`
corresponding to the module coinduced from `ℤ/ℓℤ`. -/
theorem subsingleton_sheafH_constant_fixedField_of_forall (hH : IsClosed (H : Set Gal(Ksep/K)))
    (n : ℕ) [HasExt (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt (Sheaf (Spec (.of (fixedField H))).smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v})]
    (hK : ∀ 𝓕 : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
      ℓ • 𝟙 𝓕 = 0 → Subsingleton (Sheaf.H 𝓕 n)) :
    Subsingleton (Sheaf.H ((constantSheaf (Spec (.of (fixedField H))).smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod ℓ))))
        n) := by
  have := hasExt_continuousGModule.{v} Gal(Ksep/K)
  have := hasExt_continuousGModule.{v} H
  rw [subsingleton_sheafH_constant_fixedField_iff.{v} K Ksep hH]
  let M := (Stacks.GroupCohomology.coinduction.{u, max (u + 1) v} H).obj
    (Stacks.GroupCohomology.trivialGModule H (ULift.{max (u + 1) v} (ZMod ℓ)))
  have hM : ∀ x : M.obj.obj.V, ℓ • x = 0 := fun x ↦ Subtype.ext (funext fun g ↦
    ULift.ext _ _ (show ℓ • ((x : Stacks.GroupCohomology.coinductionCarrier H _).1 g).down = 0
      by simp))
  have h := hK _ (nsmul_id_fieldEtaleSheafEquiv_inverse_eq_zero.{v} K Ksep M hM)
  rw [subsingleton_sheafH_iff.{v} K Ksep] at h
  have h' : Subsingleton (Abelian.Ext
      (Stacks.GroupCohomology.trivialGModule.{u, max (u + 1) v} Gal(Ksep/K)
        (ULift.{max (u + 1) v} ℤ)) M n) :=
    (Equiv.subsingleton_congr ((Abelian.extFunctorObj _ n).mapIso
      ((fieldEtaleSheafEquiv.{v} K Ksep).counitIso.app M)).addCommGroupIsoToAddEquiv.toEquiv).mp h
  exact (Stacks.GroupCohomology.shapiroAddEquiv.{u, max (u + 1) v} H _ n).injective.subsingleton

/-- **Stacks Project, Tag 0DV8.** Let `ℓ` be a prime, `K` a field with separable closure `Kˢᵉᵖ`,
`H` a maximal pro-`ℓ` subgroup of `Gal(Kˢᵉᵖ/K)` and `L` its fixed field. Then
`Hⁿ_ét(Spec K, 𝓕)` vanishes for every `ℓ`-power torsion abelian sheaf `𝓕` on the small étale
site of `Spec K` if and only if `Hⁿ_ét(Spec L, ℤ/ℓℤ)` vanishes. -/
@[stacks 0DV8]
theorem subsingleton_sheafH_iff_of_isMaximalProPSubgroup (hℓ : ℓ.Prime) (n : ℕ)
    (hH : IsMaximalProPSubgroup ℓ H)
    [HasExt (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt (Sheaf (Spec (.of (fixedField H))).smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v})] :
    (∀ 𝓕 : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
      Stacks.Torsion.IsPrimePowerTorsion _ ℓ 𝓕 → Subsingleton (Sheaf.H 𝓕 n)) ↔
      Subsingleton (Sheaf.H ((constantSheaf (Spec (.of (fixedField H))).smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod ℓ))))
          n) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have := hasExt_continuousGModule.{v} Gal(Ksep/K)
  have := hasExt_continuousGModule.{v} H
  have := hasExt_continuousGModule.{v} (⊥ : Subgroup H)
  refine ⟨fun hK ↦ subsingleton_sheafH_constant_fixedField_of_forall.{v} K Ksep hH.prop.1 n
    fun 𝓕 h𝓕 ↦ hK 𝓕 (Stacks.Torsion.isPrimePowerTorsion_of_nsmul_id_eq_zero _ h𝓕),
    fun hHn 𝓕 h𝓕 ↦ ?_⟩
  rw [subsingleton_sheafH_iff.{v} K Ksep]
  exact (Stacks.GroupCohomology.subsingleton_ext_iff_of_isMaximalProPSubgroup.{u, max (u + 1) v}
    hH n).mpr ((subsingleton_sheafH_constant_fixedField_iff.{v} K Ksep hH.prop.1 n).mp hHn) _
    (exists_pow_smul_fieldEtaleSheafEquiv_eq_zero.{v} K Ksep 𝓕 h𝓕)

/-- **Stacks Project, Tag 0DV9.** Let `ℓ` be a prime, `K` a field with separable closure `Kˢᵉᵖ`,
`H` a maximal pro-`ℓ` subgroup of `Gal(Kˢᵉᵖ/K)` and `L` its fixed field. The following are
equivalent:
1. `H^q_ét(Spec K, 𝓕)` vanishes for every `q ≥ n` and every `ℓ`-power torsion abelian sheaf `𝓕`
   on the small étale site of `Spec K`;
2. `H^q_ét(Spec K, 𝓕)` vanishes for every `q ≥ n` and every abelian sheaf `𝓕` on the small étale
   site of `Spec K` killed by `ℓ`;
3. `Hⁿ_ét(Spec L, ℤ/ℓℤ)` vanishes. -/
@[stacks 0DV9 "both readings of `ℓ`-torsion: `ℓ`-power torsion (1) and killed by `ℓ` (2)"]
theorem tfae_subsingleton_sheafH_of_isMaximalProPSubgroup (hℓ : ℓ.Prime) (n : ℕ)
    (hH : IsMaximalProPSubgroup ℓ H)
    [HasExt (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt (Sheaf (Spec (.of (fixedField H))).smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v})] :
    List.TFAE [
      ∀ q, n ≤ q → ∀ 𝓕 : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
        Stacks.Torsion.IsPrimePowerTorsion _ ℓ 𝓕 → Subsingleton (Sheaf.H 𝓕 q),
      ∀ q, n ≤ q → ∀ 𝓕 : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
        ℓ • 𝟙 𝓕 = 0 → Subsingleton (Sheaf.H 𝓕 q),
      Subsingleton (Sheaf.H ((constantSheaf (Spec (.of (fixedField H))).smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod ℓ))))
          n)] := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have := hasExt_continuousGModule.{v} Gal(Ksep/K)
  have := hasExt_continuousGModule.{v} (⊥ : Subgroup Gal(Ksep/K))
  have := hasExt_continuousGModule.{v} H
  have := hasExt_continuousGModule.{v} (⊥ : Subgroup H)
  tfae_have 1 → 2 := fun h q hq 𝓕 h𝓕 ↦
    h q hq 𝓕 (Stacks.Torsion.isPrimePowerTorsion_of_nsmul_id_eq_zero _ h𝓕)
  tfae_have 2 → 3 := fun h ↦
    subsingleton_sheafH_constant_fixedField_of_forall.{v} K Ksep hH.prop.1 n (h n le_rfl)
  tfae_have 3 → 1 := fun h q hq 𝓕 h𝓕 ↦ by
    rw [subsingleton_sheafH_iff.{v} K Ksep]
    exact (Stacks.GroupCohomology.forall_le_subsingleton_ext_iff_of_isMaximalProPSubgroup.{u,
      max (u + 1) v} hH n).mpr ((subsingleton_sheafH_constant_fixedField_iff.{v} K Ksep
        hH.prop.1 n).mp h) q hq _ (exists_pow_smul_fieldEtaleSheafEquiv_eq_zero.{v} K Ksep 𝓕 h𝓕)
  tfae_finish

/-- **Stacks Project, Tag 0DV9**, `ℓ`-power torsion form: `H^q_ét(Spec K, 𝓕)` vanishes for every
`q ≥ n` and every `ℓ`-power torsion abelian sheaf `𝓕` on the small étale site of `Spec K` if and
only if `Hⁿ_ét(Spec L, ℤ/ℓℤ)` vanishes. -/
theorem forall_le_subsingleton_sheafH_iff_of_isMaximalProPSubgroup (hℓ : ℓ.Prime) (n : ℕ)
    (hH : IsMaximalProPSubgroup ℓ H)
    [HasExt (Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt (Sheaf (Spec (.of (fixedField H))).smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v})] :
    (∀ q, n ≤ q → ∀ 𝓕 : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{max (u + 1) v},
      Stacks.Torsion.IsPrimePowerTorsion _ ℓ 𝓕 → Subsingleton (Sheaf.H 𝓕 q)) ↔
      Subsingleton (Sheaf.H ((constantSheaf (Spec (.of (fixedField H))).smallEtaleTopology
        AddCommGrpCat.{max (u + 1) v}).obj (AddCommGrpCat.of (ULift.{max (u + 1) v} (ZMod ℓ))))
          n) :=
  (tfae_subsingleton_sheafH_of_isMaximalProPSubgroup.{v} K Ksep hℓ n hH).out 1 3

end AlgebraicGeometry

end
