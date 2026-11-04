module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.DualNumber
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.CoherentCohomologySheaves

/-!
# The dual numbers: the right adjoint of pushforward does not preserve boundedness above

Let `k` be a field, let `k[ε]` be the ring of dual numbers over it, let `Y = Spec(k[ε])`, let
`X = Spec(k)` and let `f : X ⟶ Y` be the closed immersion of the closed point, a finite morphism
of Noetherian schemes. Let `a` be a right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. The residue field `M = k[ε]/(ε)`, placed in degree zero and
sheafified, is a bounded-above object of `D_QCoh(𝒪_Y)`, yet `a(M^~)` is not bounded above: by
[Stacks, Tag 0A9F] it is `RHom_{k[ε]}(k, M)^~`, and `Ext^i_{k[ε]}(k, k)` is nonzero for every
`i ≥ 0`. So `a` does not map `D^-_QCoh(𝒪_Y)` into `D^-_QCoh(𝒪_X)`.

The Ext computation is dimension shifting along the short exact sequence
`0 → M → k[ε] → M → 0`, whose middle term is free: the class of that sequence is a nonzero
element of `Ext^1_{k[ε]}(M, M)`, and composing with it is injective on `Ext^i_{k[ε]}(M, M)`
for every `i ≥ 1`.

## Main definitions

* `Dualizing.dualNumberFst` — the projection `k[ε] → k`.
* `Dualizing.dualNumberResidue` — the residue field `k[ε]/(ε)` as a `k[ε]`-module.

## Main results

* `Dualizing.dualNumberResidue_zExt_nontrivial` — `Ext^i_{k[ε]}(k, k)` is nonzero for every
  `i ≥ 0`, in the form `Hom_{D(k[ε])}(M, M⟦i⟧) ≠ 0`.
* `Dualizing.dualNumberDerivedHom_not_minus` — `RHom_{k[ε]}(k, M)` is not bounded above.
* `AlgebraicGeometry.dualNumberSpecMap_isFinite` and
  `AlgebraicGeometry.isLocallyNoetherian_Spec_dualNumber` — the morphism is finite and its target
  is a Noetherian scheme; its source is by
  `AlgebraicGeometry.isLocallyNoetherian_Spec_of_field`.
* `AlgebraicGeometry.minus_derivedTildeSingle` — a module placed in degree zero and sheafified is
  a bounded-above object, so the input of the example lies in `D^-_QCoh(𝒪_Y)`.
* `AlgebraicGeometry.dualNumberRightAdjoint_not_minus` — **[Stacks, Tag 0A9H]**: `a(M^~)` is not
  bounded above.
* `AlgebraicGeometry.dualNumberRightAdjoint_not_preserves_minus` — **[Stacks, Tag 0A9H]**: hence
  `a` does not map `D^-_QCoh(𝒪_Y)` into `D^-_QCoh(𝒪_X)`.

## Implementation notes

**Which object witnesses the failure.** The source states the conclusion for `a(𝒪_Y)`. That
object is bounded: `k[ε]` is self-injective, so `RHom_{k[ε]}(k, k[ε])` is concentrated in degree
zero. The group the source computes, `Ext^i_{k[ε]}(k, k)`, is the cohomology of
`RHom_{k[ε]}(k, M)` with `M = k[ε]/(ε) = f_*𝒪_X`, and it is that object which is unbounded. The
witness below is therefore `M^~` rather than `𝒪_Y`; the assertion of the example — that the right
adjoint does not map `D^-_QCoh(𝒪_Y)` into `D^-_QCoh(𝒪_X)` — is what is proved, with the input
exhibited as bounded above by `AlgebraicGeometry.minus_derivedTildeSingle`.

**Why the tag sits on two declarations.** The assertion of the example is the failure of
preservation, `AlgebraicGeometry.dualNumberRightAdjoint_not_preserves_minus`, and that statement
is checkable on its own. Its whole content, though, is the witness: that `a` sends the
bounded-above object `(k[ε]/(ε))^~` to one which is not bounded above, which is
`AlgebraicGeometry.dualNumberRightAdjoint_not_minus`. Neither alone is the example — the first
without the second names no witness, and the second does not state the source's sentence — so both
carry the attribute.

**The existence of `a` is not asserted**, exactly as the source does not assert it: it comes from
[Stacks, Tag 0A9E], whose proof needs compact generation of `D_QCoh` ([Stacks, Tag 09IS]), and it
enters as the hypothesis `adjP`. This is the convention of
`AlgebraicGeometry.polynomialRightAdjoint_homologyZero_not_isCoherent` and of
`AlgebraicGeometry.derivedTilde_comp_rightAdjoint_derivedQuasicoherentPushforwardIsoDerivedHom`.

**The short exact sequence `0 → M → k[ε] → M → 0`** is also built, for the same ring, in the
private part of `StacksFrontier/Algebra/Homology/ProjectiveDimension/DualNumbers.lean`, where it
proves that `M` has infinite projective dimension. Dropping `private` there and reusing
`periodicShortComplex` is a free deduplication; infinite projective dimension itself does not
give the nonvanishing of `Ext^i(M, M)` needed here, which is why the sequence is what gets
reused rather than its consequence.

## References

* [Stacks Project, Tag 0A9H](https://stacks.math.columbia.edu/tag/0A9H)
* [Stacks Project, Tag 0A9F](https://stacks.math.columbia.edu/tag/0A9F)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Dualizing

variable (k : Type u) [Field k]

/-- The projection `k[ε] → k` of the dual numbers over a field onto their residue field. -/
abbrev dualNumberFst : DualNumber k →+* k := (TrivSqZeroExt.fstHom k k k).toRingHom

/-- The residue field of the dual numbers `k[ε]` over a field, as a `k[ε]`-module: the quotient
of `k[ε]` by the ideal generated by `ε`. -/
abbrev dualNumberResidue : ModuleCat.{u} (DualNumber k) :=
  ModuleCat.of (DualNumber k)
    (DualNumber k ⧸ Ideal.span {(DualNumber.eps : DualNumber k)})

/-! ### The self-Ext of the residue field -/

private lemma dualNumberResidue_nontrivial :
    Nontrivial (DualNumber k ⧸ Ideal.span {(DualNumber.eps : DualNumber k)}) :=
  have : (Ideal.span {(DualNumber.eps : DualNumber k)}).IsMaximal :=
    DualNumber.isMaximal_span_singleton_eps
  Ideal.Quotient.nontrivial_iff.mpr this.ne_top

private lemma dualNumber_mul_eps_eq_zero_iff (r : DualNumber k) :
    r * DualNumber.eps = 0 ↔ r ∈ Ideal.span {(DualNumber.eps : DualNumber k)} := by
  constructor
  · intro h
    have hfst : r.fst = 0 := by
      simpa [TrivSqZeroExt.snd_mul, DualNumber.snd_eps, DualNumber.fst_eps] using
        congrArg TrivSqZeroExt.snd h
    rw [Ideal.mem_span_singleton']
    refine ⟨TrivSqZeroExt.inl r.snd, ?_⟩
    apply TrivSqZeroExt.ext
    · simp [TrivSqZeroExt.fst_mul, DualNumber.fst_eps, hfst]
    · simp [TrivSqZeroExt.snd_mul, DualNumber.snd_eps, DualNumber.fst_eps]
  · rw [Ideal.mem_span_singleton']
    rintro ⟨s, rfl⟩
    simp [mul_assoc, DualNumber.eps_mul_eps]

/-- Multiplication by `ε`, viewed as the inclusion of the residue field `k[ε]/(ε)` as the ideal
`(ε)` of `k[ε]`. -/
private def dualNumberResidueToDual :
    (DualNumber k ⧸ Ideal.span {(DualNumber.eps : DualNumber k)}) →ₗ[DualNumber k]
      DualNumber k :=
  Submodule.liftQ _
    (LinearMap.toSpanSingleton (DualNumber k) (DualNumber k) DualNumber.eps) (by
      rw [Ideal.span_le]
      rintro x rfl
      simp [DualNumber.eps_mul_eps])

private lemma dualNumberResidueToDual_mk (x : DualNumber k) :
    dualNumberResidueToDual k (Submodule.Quotient.mk x) = x * DualNumber.eps := by
  rw [dualNumberResidueToDual, Submodule.liftQ_apply]
  simp [LinearMap.toSpanSingleton_apply, smul_eq_mul]

/-- The short exact sequence `0 → k[ε]/(ε) → k[ε] → k[ε]/(ε) → 0`, whose first map is
multiplication by `ε` and whose second is the quotient map. -/
private def dualNumberResidueExtension : ShortComplex (ModuleCat.{u} (DualNumber k)) :=
  ShortComplex.mk
    (ModuleCat.ofHom (dualNumberResidueToDual k))
    (ModuleCat.ofHom (Ideal.span {(DualNumber.eps : DualNumber k)}).mkQ)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change Submodule.Quotient.mk (r * DualNumber.eps) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Ideal.mul_mem_left (Ideal.span {(DualNumber.eps : DualNumber k)}) r
        (Ideal.mem_span_singleton_self _))

private lemma dualNumberResidueExtension_shortExact :
    (dualNumberResidueExtension k).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · change Function.Exact (dualNumberResidueToDual k)
      (Ideal.span {(DualNumber.eps : DualNumber k)}).mkQ
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, dualNumberResidueToDual,
      Submodule.range_liftQ, LinearMap.range_toSpanSingleton]
  · change Function.Injective (dualNumberResidueToDual k)
    intro x y h
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    simp only [dualNumberResidueToDual_mk] at h
    change Submodule.Quotient.mk r = Submodule.Quotient.mk s
    rw [Submodule.Quotient.eq, ← dualNumber_mul_eps_eq_zero_iff k]
    simpa [sub_mul] using sub_eq_zero.mpr h
  · change Function.Surjective (Ideal.span {(DualNumber.eps : DualNumber k)}).mkQ
    exact Submodule.Quotient.mk_surjective _

/-- Every `k[ε]`-linear map `k[ε] ⟶ k[ε]/(ε)` kills the ideal `(ε)`, so it vanishes on the
image of the first map of `0 → k[ε]/(ε) → k[ε] → k[ε]/(ε) → 0`. This is what makes that sequence
non-split. -/
private lemma dualNumberResidueExtension_map_zero
    (g : ModuleCat.of (DualNumber k) (DualNumber k) ⟶ dualNumberResidue k) :
    (dualNumberResidueExtension k).f ≫ g = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change g.hom (dualNumberResidueToDual k (Submodule.Quotient.mk r)) = 0
  rw [dualNumberResidueToDual_mk, mul_comm r]
  change g.hom ((DualNumber.eps : DualNumber k) • r) = 0
  rw [map_smul]
  obtain ⟨s, hs⟩ := Submodule.Quotient.mk_surjective _ (g.hom r)
  rw [← hs, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Ideal.mul_mem_right s _ (Ideal.mem_span_singleton_self _)

private theorem dualNumberResidue_ext_nontrivial
    [HasExt.{u} (ModuleCat.{u} (DualNumber k))] (n : ℕ) :
    Nontrivial (Abelian.Ext.{u} (dualNumberResidue k) (dualNumberResidue k) n) := by
  let M := dualNumberResidue k
  let S := dualNumberResidueExtension k
  let hS := dualNumberResidueExtension_shortExact k
  have : Nontrivial M := dualNumberResidue_nontrivial k
  have hid : (𝟙 M : M ⟶ M) ≠ 0 := by
    intro hid
    obtain ⟨m, hm⟩ := exists_ne (0 : M)
    exact hm (by simpa using congrArg (fun f : M ⟶ M => f.hom m) hid)
  have hzero : Nontrivial (Abelian.Ext.{u} M M 0) :=
    (Abelian.Ext.homEquiv₀.{u} (X := M) (Y := M)).nontrivial_congr.mpr
      (nontrivial_of_ne (𝟙 M) 0 hid)
  have key : ∀ {m : ℕ} (x : Abelian.Ext.{u} S.X₁ S.X₁ m),
      hS.extClass.comp x (add_comm 1 m) = 0 →
      (∀ z : Abelian.Ext.{u} S.X₂ S.X₁ m, (Abelian.Ext.mk₀ S.f).comp z (zero_add m) = 0) →
      x = 0 := fun x hx hz => by
    obtain ⟨z, rfl⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS S.X₁ x (add_comm 1 _) hx
    exact hz z
  have hclass : hS.extClass ≠ (0 : Abelian.Ext.{u} S.X₃ S.X₁ 1) := by
    intro hclass
    refine hid ((Abelian.Ext.mk₀_eq_zero_iff (𝟙 S.X₁)).mp
      (key (Abelian.Ext.mk₀ (𝟙 S.X₁)) (by rw [hclass]; simp) fun z => ?_))
    rw [← Abelian.Ext.mk₀_homEquiv₀_apply z, Abelian.Ext.mk₀_comp_mk₀,
      Abelian.Ext.mk₀_eq_zero_iff]
    exact dualNumberResidueExtension_map_zero k _
  have hfirst : Nontrivial (Abelian.Ext.{u} M M 1) := by
    simpa [S, dualNumberResidueExtension, M] using nontrivial_of_ne hS.extClass 0 hclass
  have hsucc : ∀ n : ℕ, Nontrivial (Abelian.Ext.{u} M M (n + 1)) := by
    intro n
    induction n with
    | zero => exact hfirst
    | succ n ih =>
        have hδ : Function.Injective
            (fun x : Abelian.Ext.{u} S.X₁ S.X₁ (n + 1) =>
              hS.extClass.comp x (show 1 + (n + 1) = n + 2 from by omega)) := by
          intro x y hxy
          have hzero : hS.extClass.comp (x - y)
              (show 1 + (n + 1) = n + 2 from by omega) = 0 := by
            rw [sub_eq_add_neg, Abelian.Ext.comp_add, Abelian.Ext.comp_neg]
            simpa only [sub_eq_add_neg] using sub_eq_zero.mpr hxy
          have : Projective S.X₂ :=
            ModuleCat.projective_of_free (Module.Free.chooseBasis (DualNumber k) (DualNumber k))
          exact sub_eq_zero.mp (key _ hzero fun z => by
            rw [Abelian.Ext.eq_zero_of_projective z]; simp)
        have : Nontrivial (Abelian.Ext.{u} S.X₁ S.X₁ (n + 1)) := by
          simpa [S, dualNumberResidueExtension] using ih
        simpa [S, dualNumberResidueExtension] using Function.Injective.nontrivial hδ
  cases n with
  | zero => exact hzero
  | succ n => exact hsucc n

/-- **`Ext^i_{k[ε]}(k, k)` is nonzero for every `i ≥ 0`.** For the ring `k[ε]` of dual numbers
over a field and its residue field `M = k[ε]/(ε)`, the group `Hom_{D(k[ε])}(M, M⟦i⟧)` is
nontrivial for every natural number `i`.

The class of the non-split short exact sequence `0 → M → k[ε] → M → 0` is a nonzero element of
`Ext^1(M, M)`, and composition with it is injective on `Ext^i(M, M)` for `i ≥ 1` because the
middle term `k[ε]` is free. -/
theorem dualNumberResidue_zExt_nontrivial (i : ℕ) :
    Nontrivial (Abelian.zExt (dualNumberResidue k) (dualNumberResidue k) (i : ℤ)) := by
  have : HasExt.{u} (ModuleCat.{u} (DualNumber k)) := hasExt_of_hasDerivedCategory _
  exact (Abelian.Ext.homEquiv.{u} (X := dualNumberResidue k) (Y := dualNumberResidue k)
    (n := i)).nontrivial_congr.mp (dualNumberResidue_ext_nontrivial k i)

/-! ### Derived Hom along the projection of the dual numbers -/

/-- The residue field `k[ε]/(ε)` is the base field `k` with `k[ε]` acting through the projection
`k[ε] → k`. -/
private def dualNumberResidueRestrictionIso :
    dualNumberResidue k ≅
      (ModuleCat.restrictScalars.{u} (dualNumberFst k)).obj (ModuleCat.of k k) := by
  have hker : RingHom.ker (dualNumberFst k) =
      Ideal.span {(DualNumber.eps : DualNumber k)} := by
    ext x
    change x.fst = 0 ↔ x ∈ Ideal.span {(DualNumber.eps : DualNumber k)}
    rw [DualNumber.fst_eq_zero_iff_eps_dvd, Ideal.mem_span_singleton']
    simp only [dvd_def]
    exact ⟨fun ⟨a, ha⟩ => ⟨a, by simpa [mul_comm] using ha.symm⟩,
      fun ⟨a, ha⟩ => ⟨a, by simpa [mul_comm] using ha.symm⟩⟩
  let eRing : (DualNumber k ⧸ Ideal.span {(DualNumber.eps : DualNumber k)}) ≃+* k :=
    (Ideal.quotEquivOfEq hker.symm).trans
      ((dualNumberFst k).quotientKerEquivOfSurjective TrivSqZeroExt.fst_surjective)
  let eLinear : (DualNumber k ⧸ Ideal.span {(DualNumber.eps : DualNumber k)}) ≃ₗ[DualNumber k]
      ((ModuleCat.restrictScalars.{u} (dualNumberFst k)).obj (ModuleCat.of k k)) :=
    { toEquiv := eRing.toEquiv
      map_add' := map_add eRing
      map_smul' := by
        intro r x
        change eRing ((Ideal.Quotient.mk _ r) * x) = dualNumberFst k r * eRing x
        rw [map_mul]
        congr 1 }
  exact eLinear.toModuleIso

/-- The identification of `Ext^i_{k[ε]}(M, M)` with morphisms out of `k[i]` into
`RHom_{k[ε]}(k, M)`, given by the adjunction of [Stacks, Tag 0A70]. -/
private def dualNumberResidueExtDerivedHomEquiv (i : ℕ) :
    Abelian.zExt (dualNumberResidue k) (dualNumberResidue k) (i : ℤ) ≃
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) (i : ℤ)).obj (ModuleCat.of k k) ⟶
        (AnyModel.derivedHom.{u, u, u, u, u} (dualNumberFst k)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (DualNumber k)) 0).obj
            (dualNumberResidue k))) := by
  let R := ModuleCat.{u} (DualNumber k)
  let F₀ := ModuleCat.restrictScalars.{u} (dualNumberFst k)
  let L := F₀.mapDerivedCategory
  let G := AnyModel.derivedHom.{u, u, u, u, u} (dualNumberFst k)
  let X := (DerivedCategory.singleFunctor R 0).obj (dualNumberResidue k)
  let Y := (DerivedCategory.singleFunctor (ModuleCat.{u} k) 0).obj (ModuleCat.of k k)
  let adj := (AnyModel.restrictScalarsDerived_adj_derivedHom.{u, u, u, u, u}
    (dualNumberFst k)).some
  let eShiftObj : (shiftEquiv (DerivedCategory R) (-(i : ℤ))).inverse.obj X ≅ X⟦(i : ℤ)⟧ :=
    eqToIso (by simp)
  let eShiftHom : (X ⟶ X⟦(i : ℤ)⟧) ≃ (X⟦-(i : ℤ)⟧ ⟶ X) :=
    ((Iso.refl X).homCongr eShiftObj).symm.trans
      ((shiftEquiv (DerivedCategory R) (-(i : ℤ))).toAdjunction.homEquiv X X).symm
  let e0 : L.obj Y ≅ X :=
    (F₀.mapDerivedCategorySingleFunctor 0).app (ModuleCat.of k k) ≪≫
      (DerivedCategory.singleFunctor R 0).mapIso (dualNumberResidueRestrictionIso k).symm
  let eShift : L.obj (Y⟦-(i : ℤ)⟧) ≅ X⟦-(i : ℤ)⟧ :=
    (Functor.CommShift.commShiftIso L (-(i : ℤ))).app Y ≪≫
      (shiftFunctor (DerivedCategory R) (-(i : ℤ))).mapIso e0
  let eSingle : (DerivedCategory.singleFunctor (ModuleCat.{u} k) (i : ℤ)).obj
      (ModuleCat.of k k) ≅ Y⟦-(i : ℤ)⟧ :=
    (((DerivedCategory.singleFunctors (ModuleCat.{u} k)).shiftIso
      (-(i : ℤ)) (i : ℤ) 0 (by omega)).app (ModuleCat.of k k)).symm
  exact eShiftHom.trans ((eShift.homCongr (Iso.refl X)).symm.trans
    ((adj.homEquiv (Y⟦-(i : ℤ)⟧) X).trans
      (eSingle.homCongr (Iso.refl (G.obj X))).symm))

/-- **The obstruction of Stacks 0A9H, on the module side.** For the projection `k[ε] → k` of the
dual numbers over a field, the complex `RHom_{k[ε]}(k, M)` with `M = k[ε]/(ε)` is not bounded
above.

Were it in degrees `≤ b`, then for `i > b` every morphism `k[i] ⟶ RHom_{k[ε]}(k, M)` would
vanish, `k` being projective over `k`
(`DerivedCategory.from_singleFunctor_obj_eq_zero_of_isLE_of_projective`). By the adjunction of
[Stacks, Tag 0A70] those morphisms are `Ext^i_{k[ε]}(M, M)`, which is nonzero
(`Dualizing.dualNumberResidue_zExt_nontrivial`). -/
theorem dualNumberDerivedHom_not_minus :
    ¬ (DerivedCategory.TStructure.t (C := ModuleCat.{u} k)).minus
      ((AnyModel.derivedHom.{u, u, u, u, u} (dualNumberFst k)).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (DualNumber k)) 0).obj
          (dualNumberResidue k))) := by
  rintro ⟨b, hb⟩
  have := hb
  have : Projective (ModuleCat.of k k) :=
    ModuleCat.projective_of_free (Module.Free.chooseBasis k k)
  have hbn : b < ((b.toNat + 1 : ℕ) : ℤ) := by omega
  have hsub : Subsingleton
      ((DerivedCategory.singleFunctor (ModuleCat.{u} k) ((b.toNat + 1 : ℕ) : ℤ)).obj
        (ModuleCat.of k k) ⟶
          (AnyModel.derivedHom.{u, u, u, u, u} (dualNumberFst k)).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} (DualNumber k)) 0).obj
              (dualNumberResidue k))) :=
    subsingleton_of_forall_eq 0 fun f =>
      DerivedCategory.from_singleFunctor_obj_eq_zero_of_isLE_of_projective hbn _ f
  exact (not_nontrivial_iff_subsingleton.mpr
    ((dualNumberResidueExtDerivedHomEquiv k (b.toNat + 1)).subsingleton_congr.mpr hsub))
    (dualNumberResidue_zExt_nontrivial k (b.toNat + 1))

end Dualizing

namespace AlgebraicGeometry

/-! ### The example on the scheme side -/

/-- The closed immersion of the closed point of the spectrum of the dual numbers, as the
morphism of affine schemes `Spec(k) ⟶ Spec(k[ε])` induced by the projection `k[ε] → k`, is
finite: `k` is generated by one element as a `k[ε]`-module. -/
theorem dualNumberSpecMap_isFinite (k : Type u) [Field k] :
    IsFinite (Spec.map (CommRingCat.ofHom (Dualizing.dualNumberFst k))) := by
  rw [IsFinite.SpecMap_iff]
  exact RingHom.Finite.of_surjective _ fun x => ⟨TrivSqZeroExt.inl x, by simp⟩

/-- The spectrum of the dual numbers over a field is a Noetherian scheme. -/
theorem isLocallyNoetherian_Spec_dualNumber (k : Type u) [Field k] :
    IsLocallyNoetherian (Spec (CommRingCat.of (DualNumber k))) :=
  isLocallyNoetherian_Spec.mpr inferInstance

/-- A faithful functor reflects zero objects, so a module whose associated sheaf on `Spec R` is
zero is itself zero. -/
private theorem isZero_of_isZero_tilde (R : CommRingCat.{u}) (N : ModuleCat.{u} R)
    (h : IsZero ((tilde.functor R).obj N)) : IsZero N := by
  refine (IsZero.iff_id_eq_zero N).mpr ((tilde.functor R).map_injective ?_)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact h.eq_of_src _ _

/-- **A module placed in degree zero and sheafified is bounded above.** The cohomology sheaves of
`(M[0])^~` are the sheaves associated to the cohomology of `M[0]`
(`AlgebraicGeometry.homologyDerivedTildeObjIso`), and those vanish in positive degrees, so
`(M[0])^~` lies in `D^-_QCoh(𝒪_{Spec R})`. -/
theorem minus_derivedTildeSingle (R : CommRingCat.{u}) (M : ModuleCat.{u} R) :
    (DerivedCategory.TStructure.t (C := (Spec R).Modules)).minus
      ((DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).ι.obj
          ((derivedTilde R).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M))) := by
  refine ⟨0, (DerivedCategory.isLE_iff _ 0).mpr fun i hi => ?_⟩
  have hzC : IsZero ((((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ)
      0).obj M)).homology i) :=
    HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M i (by omega)
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)) :=
    hzC.of_iso ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M))
  exact ((tilde.functor R).map_isZero hz).of_iso (homologyDerivedTildeObjIso R _ i)

/-- **Stacks Project, Tag 0A9H.** Let `k` be a field, `Y = Spec(k[ε])` the spectrum of the dual
numbers, `X = Spec(k)` and `f : X ⟶ Y` the closed immersion of the closed point, a finite
morphism of Noetherian schemes (`AlgebraicGeometry.dualNumberSpecMap_isFinite`,
`AlgebraicGeometry.isLocallyNoetherian_Spec_dualNumber`,
`AlgebraicGeometry.isLocallyNoetherian_Spec_of_field`). Let `a` be a right adjoint of
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. Then the image under `a` of the sheafification of the residue
field `k[ε]/(ε)` in degree zero is not bounded above. That object is itself bounded above
(`AlgebraicGeometry.minus_derivedTildeSingle`), so `a` does not map `D^-_QCoh(𝒪_Y)` into
`D^-_QCoh(𝒪_X)`, which is
`AlgebraicGeometry.dualNumberRightAdjoint_not_preserves_minus`.

By [Stacks, Tag 0A9F] that image is `RHom_{k[ε]}(k, k[ε]/(ε))^~`, which is unbounded above
because `Ext^i_{k[ε]}(k, k)` is nonzero for every `i ≥ 0`
(`Dualizing.dualNumberDerivedHom_not_minus`, resting on
`Dualizing.dualNumberResidue_zExt_nontrivial`); sheafification reflects the vanishing of a
cohomology module, being faithful. The existence of `a` is not asserted: it comes from
[Stacks, Tag 0A9E] and enters as the hypothesis `adjP`. -/
@[stacks 0A9H]
theorem dualNumberRightAdjoint_not_minus (k : Type u) [Field k]
    {a : (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent
          (Spec (CommRingCat.of (DualNumber k))).ringCatSheaf)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of k)).ringCatSheaf)).FullSubcategory}
    (adjP : derivedQuasicoherentPushforward
      (Spec.map (CommRingCat.ofHom (Dualizing.dualNumberFst k))) ⊣ a) :
    ¬ (DerivedCategory.TStructure.t (C := (Spec (CommRingCat.of k)).Modules)).minus
      ((DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of k)).ringCatSheaf)).ι.obj
          (a.obj ((derivedTilde (CommRingCat.of (DualNumber k))).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} (DualNumber k)) 0).obj
              (Dualizing.dualNumberResidue k))))) := by
  intro h
  obtain ⟨iso⟩ := derivedTilde_comp_rightAdjoint_derivedQuasicoherentPushforwardIsoDerivedHom
    (CommRingCat.ofHom (Dualizing.dualNumberFst k)) adjP
  have e0 : a.obj ((derivedTilde (CommRingCat.of (DualNumber k))).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (DualNumber k)) 0).obj
          (Dualizing.dualNumberResidue k))) ≅
      (derivedTilde (CommRingCat.of k)).obj
        ((Dualizing.AnyModel.derivedHom.{u, u, u, u, u} (Dualizing.dualNumberFst k)).obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} (DualNumber k)) 0).obj
            (Dualizing.dualNumberResidue k))) :=
    iso.app ((DerivedCategory.singleFunctor (ModuleCat.{u} (DualNumber k)) 0).obj
      (Dualizing.dualNumberResidue k))
  obtain ⟨b, hb⟩ := (DerivedCategory.TStructure.t
    (C := (Spec (CommRingCat.of k)).Modules)).minus.prop_of_iso
      ((DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of k)).ringCatSheaf)).ι.mapIso e0) h
  have := hb
  refine Dualizing.dualNumberDerivedHom_not_minus k
    ⟨b, (DerivedCategory.isLE_iff _ b).mpr fun i hi => ?_⟩
  exact isZero_of_isZero_tilde (CommRingCat.of k) _
    ((DerivedCategory.isZero_of_isLE _ b i hi).of_iso
      (homologyDerivedTildeObjIso (CommRingCat.of k) _ i).symm)

/-- **Stacks Project, Tag 0A9H.** For `f : Spec(k) ⟶ Spec(k[ε])` the closed immersion of the
closed point of the spectrum of the dual numbers over a field, a finite morphism of Noetherian
schemes, a right adjoint `a` of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` does not map
`D^-_QCoh(𝒪_Y)` into `D^-_QCoh(𝒪_X)`.

The residue field `k[ε]/(ε)`, in degree zero and sheafified, is a bounded-above object
(`AlgebraicGeometry.minus_derivedTildeSingle`) whose image under `a` is not
(`AlgebraicGeometry.dualNumberRightAdjoint_not_minus`). -/
@[stacks 0A9H]
theorem dualNumberRightAdjoint_not_preserves_minus (k : Type u) [Field k]
    {a : (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent
          (Spec (CommRingCat.of (DualNumber k))).ringCatSheaf)).FullSubcategory ⥤
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of k)).ringCatSheaf)).FullSubcategory}
    (adjP : derivedQuasicoherentPushforward
      (Spec.map (CommRingCat.ofHom (Dualizing.dualNumberFst k))) ⊣ a) :
    ¬ ∀ K : (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent
          (Spec (CommRingCat.of (DualNumber k))).ringCatSheaf)).FullSubcategory,
      (DerivedCategory.TStructure.t
          (C := (Spec (CommRingCat.of (DualNumber k))).Modules)).minus
        ((DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherent
            (Spec (CommRingCat.of (DualNumber k))).ringCatSheaf)).ι.obj K) →
        (DerivedCategory.TStructure.t (C := (Spec (CommRingCat.of k)).Modules)).minus
          ((DerivedCategoryB.derivedCategoryB
            (SheafOfModules.isQuasicoherent
              (Spec (CommRingCat.of k)).ringCatSheaf)).ι.obj (a.obj K)) := fun h =>
  dualNumberRightAdjoint_not_minus k adjP
    (h _ (minus_derivedTildeSingle (CommRingCat.of (DualNumber k))
      (Dualizing.dualNumberResidue k)))

end AlgebraicGeometry

end
