module

public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteLocallyFreeBiprod
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealProductTensor

/-!
# A power of a sheaf of ideals is a quotient of a tensor power

Let `X` be a scheme, let `I` be a quasi-coherent sheaf of ideals on `X` and suppose `I` is the
quotient of a finite locally free `𝒪_X`-module, say `e : 𝓔 ⟶ I` is an epimorphism with `𝓔`
finite locally free.  Then every positive power `Iⁿ` is the quotient of a finite locally free
`𝒪_X`-module, namely of the `n`-fold tensor power `𝓔^{⊗ n}`.

The input is the datum that the hypotheses of [Stacks, Tag 0F89] provide, and the conclusion is
what the proof of its substantial direction uses in the Noetherian case: a section of a coherent
module over a member `U` of the affine covering extends to a morphism `Iⁿ ⟶ 𝓕` out of a power of
the sheaf of ideals cutting out the complement of `U` ([Stacks, Tag 01YB]), and that morphism is
of use only once `Iⁿ` is known to be a quotient of a finite locally free module.

## Main definitions

* `AlgebraicGeometry.idealPowPowOneHom`: the comparison morphism `(Iⁿ)¹ ⟶ Iⁿ` between the first
  power of the `n`-th power of `I` in `AlgebraicGeometry.Scheme.IdealSheafData` and the `n`-th
  power of `I` as a subsheaf of the structure sheaf.

## Main results

* `AlgebraicGeometry.epi_idealPowPowOneHom`: that comparison is an epimorphism.
* `AlgebraicGeometry.exists_isFiniteLocallyFree_epi_idealPowPowOne_of_epi`: `(I^{n+1})¹` is a
  quotient of a finite locally free module.
* `AlgebraicGeometry.exists_isFiniteLocallyFree_epi_idealPow_of_epi`: **a positive power of a
  sheaf of ideals that is a quotient of a finite locally free module is itself a quotient of a
  finite locally free module.**

## Implementation notes

The induction runs over the powers of `I` taken in
`AlgebraicGeometry.Scheme.IdealSheafData`, not over the exponent of
`Stacks.AlgebraicGeometry.IdealPowerColimit.idealPow`, because the multiplication epimorphism
available is `Stacks.AlgebraicGeometry.IdealProduct.epi_idealPowMulOfHom`, which takes a quotient
of `Kⁿ` and a quotient of `K'ⁿ` to a quotient of `(K K')ⁿ`: with the exponent held at `1` and
`K' = I^n` the ideal sheaf multiplies and the exponent does not move, so one step of the
induction is `𝓔 ⊗ 𝓔^{⊗ n} ⟶ (I · Iⁿ)¹`.  Finite local freeness of the tensor product is
`AlgebraicGeometry.isFiniteLocallyFree_tensorObj`, [Stacks, Tag 0FDK].

The two spellings of the `n`-th power then have to be compared, and they are *not* the same
subsheaf by definition: `(Iⁿ)¹` is the subsheaf attached to the ideal sheaf `Iⁿ` and `Iⁿ` is the
`n`-th member of the filtration of the structure sheaf by `I`.  They agree on the affine opens,
by `AlgebraicGeometry.Scheme.IdealSheafData.ideal_pow` and
`Stacks.AlgebraicGeometry.IdealPowerColimit.obj_idealPow_affineOpen_eq_ideal_pow`, which is all
that is needed: the comparison morphism is produced by `AlgebraicGeometry.factorThruOfLocalMem`,
which asks for membership only on a neighbourhood of each point, and its surjectivity is checked
by the section-level criterion, which likewise asks for a preimage only on a neighbourhood.  So
no equality of the two subsheaves is required, and none is proved here.

## References

* [Stacks Project, Tag 0F89](https://stacks.math.columbia.edu/tag/0F89)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe u

noncomputable section

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- **`(Iⁿ)¹` and `Iⁿ` have the same sections over an affine open.** Both are the `n`-th power
of the ideal of `I` there: the left-hand side by
`AlgebraicGeometry.Scheme.IdealSheafData.ideal_pow`, the right-hand side by the description of
the filtration of the structure sheaf. -/
theorem obj_idealPowerMultiple_pow_one_affineOpen (I : X.IdealSheafData) (n : ℕ)
    (V : X.affineOpens) :
    (idealPowerMultiple (I ^ n) 1 (structureModule X)).toSubmodule.obj (op V.1) =
      (idealPowerMultiple I n (structureModule X)).toSubmodule.obj (op V.1) := by
  rw [obj_idealPow_affineOpen_eq_ideal_pow, obj_idealPow_affineOpen_eq_ideal_pow, pow_one]

/-- **`(Iⁿ)¹` is contained in `Iⁿ`.** Membership in a subsheaf of a sheaf of modules on a scheme
is detected on the affine opens contained in the given one
(`AlgebraicGeometry.mem_of_forall_affineOpens`), and there the two subsheaves coincide. -/
theorem idealPowerMultiple_pow_one_le (I : X.IdealSheafData) (n : ℕ) :
    idealPowerMultiple (I ^ n) 1 (structureModule X) ≤
      idealPowerMultiple I n (structureModule X) := by
  refine SheafOfModules.Submodule.le_iff.mpr (PresheafOfModules.Submodule.le_iff.mpr ?_)
  intro W x hx
  obtain ⟨W, rfl⟩ : ∃ W' : X.Opens, op W' = W := ⟨W.unop, rfl⟩
  refine mem_of_forall_affineOpens (idealPowerMultiple I n (structureModule X))
    (show Γ(structureModule X, W) from x) fun V hV ↦
    (obj_idealPowerMultiple_pow_one_affineOpen I n V).le ?_
  exact ((idealPow (I ^ n) 1).presheaf.map (homOfLE hV).op
    (⟨x, hx⟩ : Γ(idealPow (I ^ n) 1, W))).2

/-- **The comparison morphism `(Iⁿ)¹ ⟶ Iⁿ`**, the inclusion of one subsheaf of the structure
sheaf into the other. -/
def idealPowPowOneHom (I : X.IdealSheafData) (n : ℕ) :
    idealPow (I ^ n) 1 ⟶ idealPow I n :=
  subInclusion (idealPowerMultiple_pow_one_le I n)

/-- **The comparison morphism `(Iⁿ)¹ ⟶ Iⁿ` is an epimorphism.** Over an affine open the two
subsheaves of the structure sheaf coincide, so a section of `Iⁿ` has a preimage on an affine
neighbourhood of each of its points. -/
theorem epi_idealPowPowOneHom (I : X.IdealSheafData) (n : ℕ) :
    Epi (idealPowPowOneHom I n) := by
  have hepi : @Epi (SheafOfModules X.ringCatSheaf) _ _ _ (idealPowPowOneHom I n) := by
    refine Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections _ fun W t p hp ↦ ?_
    obtain ⟨-, ⟨V, hVaff, rfl⟩, hpV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (show p ∈ (W : Set X) from hp) W.isOpen
    exact ⟨V, hVW, hpV,
      ⟨((idealPow I n).presheaf.map (homOfLE hVW).op t).1,
        (obj_idealPowerMultiple_pow_one_affineOpen I n ⟨V, hVaff⟩).ge
          ((idealPow I n).presheaf.map (homOfLE hVW).op t).2⟩,
      Subtype.ext (val_subInclusion_app (idealPowerMultiple_pow_one_le I n) V _)⟩
  exact ⟨fun g₁ g₂ h ↦ hepi.left_cancellation g₁ g₂ h⟩

/-- **A positive power of the ideal sheaf, in the `AlgebraicGeometry.Scheme.IdealSheafData`
spelling, is a quotient of a tensor power of `𝓔`.** The induction multiplies the ideal sheaf and
leaves the exponent at `1`: one step takes a quotient of `I¹` and a quotient of `(Iⁿ)¹` to a
quotient of `(I · Iⁿ)¹`, by [Stacks, Tag 01CA]. -/
theorem exists_isFiniteLocallyFree_epi_idealPowPowOne_of_epi (I : X.IdealSheafData)
    {E : X.Modules} (hE : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
    {e : E ⟶ idealPow I 1} (he : Epi e) (n : ℕ) :
    ∃ (P : X.Modules) (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) P)
      (q : P ⟶ idealPow (I ^ (n + 1)) 1), Epi q := by
  induction n with
  | zero =>
    rw [show (I : X.IdealSheafData) ^ (0 + 1) = I from by rw [zero_add, pow_one]]
    exact ⟨E, hE, e, he⟩
  | succ m ih =>
    obtain ⟨P, hP, q, hq⟩ := ih
    rw [show (I : X.IdealSheafData) ^ (m + 1 + 1) = I * I ^ (m + 1) from pow_succ' I (m + 1)]
    refine ⟨Stacks.AlgebraicGeometry.IdealProduct.tensorModules E P,
      (@isFiniteLocallyFree_tensorObj X E P
          hE
          hP),
      Stacks.AlgebraicGeometry.IdealProduct.idealPowMulOfHom I (I ^ (m + 1)) 1 e q,
      Stacks.AlgebraicGeometry.IdealProduct.epi_idealPowMulOfHom I (I ^ (m + 1)) 1 e q he hq⟩

/-- **A positive power of a sheaf of ideals which is a quotient of a finite locally free module
is a quotient of a finite locally free module.** This is the statement the Noetherian case of the
substantial direction of [Stacks, Tag 0F89] needs: the hypotheses of that tag supply an
epimorphism `𝓔 ⟶ I` with `𝓔` finite locally free, and [Stacks, Tag 01YB] produces morphisms out
of powers `Iⁿ`, so those powers have to be reached from `𝓔`.

The source argues with the `n`-fold tensor power of `𝓔 ⟶ I` and the epimorphism
`I^{⊗ n} ⟶ Iⁿ`; that is what the proof here does, the tensor power being accumulated by the
induction of `exists_isFiniteLocallyFree_epi_idealPowPowOne_of_epi`.

The exponent must be positive: `I⁰` is the whole structure sheaf and `𝓔` need not surject onto
it. -/
theorem exists_isFiniteLocallyFree_epi_idealPow_of_epi (I : X.IdealSheafData)
    {E : X.Modules} (hE : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) E)
    {e : E ⟶ idealPow I 1} (he : Epi e) {n : ℕ} (hn : n ≠ 0) :
    ∃ (P : X.Modules) (_ : SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) P)
      (q : P ⟶ idealPow I n), Epi q := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  obtain ⟨P, hP, q, hq⟩ := exists_isFiniteLocallyFree_epi_idealPowPowOne_of_epi I hE he m
  have := hq
  have := epi_idealPowPowOneHom I (m + 1)
  exact ⟨P, hP, q ≫ idealPowPowOneHom I (m + 1), inferInstance⟩

end AlgebraicGeometry

end

end
