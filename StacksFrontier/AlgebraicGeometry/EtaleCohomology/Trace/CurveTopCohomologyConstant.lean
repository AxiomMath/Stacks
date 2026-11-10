module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LAdicFrobeniusLevel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstantCurveCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTowerExcision

/-!
# `H²(X_k̄, ℤ/m) = ℤ/m` of a proper curve, with `π_X^* = q`

Let `X` be proper over a finite field `k` with `q` elements, compactified by itself, such that
`X_k̄` is a smooth proper curve over an algebraically closed extension `k̄` of `k`, and let `m` be
invertible in `k̄`. Then `H²(X_k̄, ℤ/m) ≅ ℤ/m`, with the canonical geometric Frobenius acting as
multiplication by `q`. This is the computation, at a finite level and with `ℤ/m`-coefficients, of
the statement on `H²` in the proof of [Tag 03V8](https://stacks.math.columbia.edu/tag/03V8): the
group is `Ext²(ℤ/m, ℤ/m)` on `X_k̄` (`Stacks.EtaleCohomology.compactSupportFrobeniusSingleIsoExt`),
on which `π_X^*` is restriction along `π̄ = π_X × id`
(`Stacks.EtaleCohomology.compactSupportFrobeniusSingleIsoExt_canonical_constant`), which
multiplies by `deg π̄ = q` (`Stacks.Picard.constantExtRestriction_two_eq_smul`), and the trace
`H²(X_k̄, μ_m) ≅ ℤ/m` (`Stacks.Kummer.smoothProperCurveTrace`) identifies it with `ℤ/m`.

## Main results

* `Stacks.EtaleCohomology.exists_addEquiv_compactSupportSheafCohomology_two_constant`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [IsProper f]
  (kbar : Type u) [Field kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)
  [IsAlgClosed kbar] [IsCurve kbar (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
  [Smooth (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]
  [IsProper (pullback.snd (Over.mk f).hom (specAlgebraMap k kbar))]

omit [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] in
include hcard in
/-- **`H²(X_k̄, ℤ/m) ≅ ℤ/m`, with `π_X^*` acting as `q`**, for `X` proper over the finite field `k`
with `X_k̄` a smooth proper curve and `m` invertible in `k̄`. -/
theorem exists_addEquiv_compactSupportSheafCohomology_two_constant (m : ℕ) [NeZero m]
    (hm : IsUnit (m : kbar)) :
    ∃ Φ : (compactSupportSheafCohomology (ZMod m) f (CompactificationOf.ofProper f) kbar 2).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod m) X.smallEtaleTopology) ≃+
          ZMod m,
      ∀ x, Φ (((compactSupportSheafFrobenius (ZMod m) f (CompactificationOf.ofProper f) kbar p q
          hcard 2).app (Stacks.Cohomology.GlobalSections.constantModuleSheaf (ZMod m)
            X.smallEtaleTopology)).hom x) = ((p ^ q : ℕ) : ZMod m) * Φ x := by
  let j := CompactificationOf.ofProper f
  let Λ := ZMod m
  let K := Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology
  let γ : (etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K ≅
      Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        (Over.mk j.toBase).left.smallEtaleTopology :=
    (etaleModuleExtensionByZeroIdIso Λ X).app K
  let δ := (etaleModuleInverseImage.{u, 0} Λ
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)).mapIso γ ≪≫
    inverseImageEtaleModuleConstantSheafIso.{u, 0} Λ (ModuleCat.of Λ (ULift.{u + 1} Λ))
      (fieldBaseChangeProj (Over.mk j.toBase) kbar)
  let e₃ : (compactSupportSheafCohomology Λ f j kbar 2).obj K ≃+
      Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology)
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K)) 2 :=
    (compactSupportFrobeniusSingleIsoExt Λ f j kbar K 2).addCommGroupIsoToAddEquiv
  let e₄ : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology)
        ((etaleModuleInverseImage.{u, 0} Λ (fieldBaseChangeProj (Over.mk j.toBase) kbar)).obj
          ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj K)) 2 ≃+
      Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
          (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology) 2 :=
    SmallEtale.extPostcompIsoAddEquiv.{u + 1}
      (X := Stacks.Cohomology.GlobalSections.constantModuleSheaf
        Λ (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology) δ 2
  have hN0 : m ≠ 0 := NeZero.ne m
  have : NeZero (m : kbar) := ⟨hm.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot kbar m
  let fY := pullback.snd (Over.mk f).hom (specAlgebraMap k kbar)
  let e₅ : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
        (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ
          (fieldBaseChange (Over.mk j.toBase) kbar).smallEtaleTopology) 2 ≃+ _ :=
    Stacks.Picard.extRootsOfUnityAddEquiv fY hζ hN0 2
  let e₆ := Stacks.Kummer.smoothProperCurveTrace fY hm
  refine ⟨((e₃.trans e₄).trans e₅).trans e₆, fun x => ?_⟩
  have h₃ := compactSupportFrobeniusSingleIsoExt_canonical_constant Λ kbar p q hcard f j K γ
    (e₄ (e₃ x))
  have h4 := (congrArg (compactSupportFrobeniusSingleIsoExt Λ f j kbar K 2).inv.hom
    (e₄.symm_apply_apply (e₃ x))).trans (e₃.symm_apply_apply x)
  have hrestr := Stacks.Picard.constantExtRestriction_two_eq_smul fY hm
    (geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
    (geometricFrobeniusBaseChange_comp_snd (Over.mk f) kbar p q hcard) _
    (picardDegree_schemePullbackClassHom_geometricFrobeniusBaseChange (Over.mk f) kbar p q hcard)
    (e₄ (e₃ x))
  have hx : e₄ (e₃ (((compactSupportSheafFrobenius (ZMod m) f (CompactificationOf.ofProper f) kbar
      p q hcard 2).app K).hom x)) = (Fintype.card k : ℤ) • e₄ (e₃ x) := by
    refine Eq.trans ?_ (h₃.trans hrestr)
    erw [h4]
    rfl
  rw [AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.trans_apply, AddEquiv.trans_apply,
    AddEquiv.trans_apply, AddEquiv.trans_apply, hx, map_zsmul, map_zsmul, hcard, zsmul_eq_mul]
  push_cast
  rfl

end Stacks.EtaleCohomology

end
