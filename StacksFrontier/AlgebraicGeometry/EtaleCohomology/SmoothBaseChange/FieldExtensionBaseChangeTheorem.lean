module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PrimeToCharacteristicStalkCriterion
public import
    StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FieldExtensionBaseChange
public import
    StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.SmoothLimitBaseChangeHolds
public import StacksCore.Tactic.StacksAttribute

/-!
# Direct images commute with extension of the base field

[Stacks, Tag 0F1C]: let `L/K` be an extension of fields, let `g : T ⟶ S` be a quasi-compact and
quasi-separated morphism of schemes over `K`, and let `g_L : T_L ⟶ S_L` be its base change to
`Spec L`. For `E ∈ D⁺(T_étale)` whose cohomology sheaves have stalks which are torsion of orders
invertible in `K`, `Rg_{L,*} E_L` is the pullback of `Rg_* E` to `S_L`: the base change map
`(S_L ⟶ S)⁻¹ Rg_* E ⟶ Rg_{L,*} E_L` is an isomorphism.

## Main results

* `Stacks.EtaleCohomology.FieldExtensionBaseChange.isIso_smallEtaleDerivedBaseChangeAb_of_stalks`

## Implementation notes

The proof is
`Stacks.EtaleCohomology.FieldExtensionBaseChange.isIso_smallEtaleDerivedBaseChangeAb_baseChange`
(the separable case from [Stacks, Tag 07BV] and smooth base change along a limit, the general case
through the perfect closures), with [Stacks, Tag 0F09] supplied by
`Stacks.EtaleCohomology.smoothLimitBaseChange_holds`. The torsion
hypothesis is stated on stalks at geometric points, as in the source; it is torsion prime to the
exponential characteristic of `K` by
`AlgebraicGeometry.isPrimeToCharacteristicTorsion_ringExpChar_iff_forall_smallEtaleStalkAb`.

## References

* [Stacks Project, Tag 0F1C](https://stacks.math.columbia.edu/tag/0F1C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.FieldExtensionBaseChange

-- `smallEtaleDerivedBaseChangeAb` (BaseChangeHigher/BaseChangeCondition.lean:220) is built under
-- the standard model, so its components live in the standard bounded below derived categories.
attribute [local instance] HasDerivedCategory.standard

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  {S T : Scheme.{u}} (sS : S ⟶ Spec (.of K)) (sT : T ⟶ Spec (.of K)) (g : T ⟶ S)
  [QuasiCompact g] [QuasiSeparated g] (hg : g ≫ sS = sT)

/-- **Direct images commute with extension of the base field** ([Stacks, Tag 0F1C]). Let `L/K`
be an extension of fields, let `g : T ⟶ S` be a quasi-compact and quasi-separated morphism of
schemes over `K`, and let `g_L : T_L ⟶ S_L` be its base change to `Spec L`, with
`S_L = Spec L ×_K S` and `T_L = Spec L ×_K T`. Let `E ∈ D⁺(T_étale)` have cohomology sheaves whose
stalks are torsion of orders invertible in `K`: every element of the stalk of `H^q(E)` at every
geometric point of `T` is killed by a positive integer invertible in `K`. Let `E_L` be the
pullback of `E` to `(T_L)_étale`. Then `Rg_{L,*} E_L` is the pullback of `Rg_* E` to `S_L`: the
base change map `(S_L ⟶ S)⁻¹ Rg_* E ⟶ Rg_{L,*} E_L` is an isomorphism. -/
@[stacks 0F1C "the base change map `(S_L ⟶ S)⁻¹ Rg_* E ⟶ Rg_{L,*} E_L` is an isomorphism"]
theorem isIso_smallEtaleDerivedBaseChangeAb_of_stalks
    (E : DerivedCategory.Plus (Sheaf (smallEtaleTopology T) Ab.{u + 1}))
    (hE : ∀ (q : ℤ) (t : GeometricPoint T)
      (a : ↑((smallEtaleStalkAb t.hom).obj ((DerivedCategory.Plus.homologyFunctor _ q).obj E))),
      ∃ n : ℕ, 0 < n ∧ IsUnit (n : K) ∧ n • a = 0) :
    IsIso ((smallEtaleDerivedBaseChangeAb (pullback.snd _ sS) g
      (baseChangeMap (Spec.map (CommRingCat.ofHom (algebraMap K L))) sS sT g hg)
      (pullback.snd _ sT) (baseChangeMap_snd _ sS sT g hg)).app E) :=
  isIso_smallEtaleDerivedBaseChangeAb_baseChange K L sS sT g hg smoothLimitBaseChange_holds E
    fun q ↦
      (isPrimeToCharacteristicTorsion_ringExpChar_iff_forall_smallEtaleStalkAb _ K).2 (hE q)

end Stacks.EtaleCohomology.FieldExtensionBaseChange

end
