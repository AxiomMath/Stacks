module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.PushforwardGenerator
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.SectionProduct.PullbackUnitComparisonSection
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.Reflexive
public import StacksFrontier.AlgebraicGeometry.Nondegeneracy.StructureSheafNotIsZero
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardPerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.LocallyPrincipalFibre
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionIntegral
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeProperties
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.ZeroSchemeIdeal
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.TwistByInvertible

/-!
# The zero scheme of a generator on the fibres

This file reads the generators of `AlgebraicGeometry.PushforwardGenerator` as global sections and
records the fibrewise input of the claim in the proof of [Stacks, Tag 0B9X]: the pullback of a
generator to a fibre is a nonzero section.

## Main results

* `AlgebraicGeometry.PushforwardGenerator.pullbackGlobalSections_ne_zero_of_map_ne_zero`: the
  pullback of the global section of `s : 𝒪_Y ⟶ ℒ` is nonzero as soon as `g^*s` is (through the
  section dictionary `Stacks.PullbackUnitComparisonSection.pullbackGlobalSections_unitHomEquiv`).
* `AlgebraicGeometry.PushforwardGenerator.pullbackGlobalSections_fiberι_ne_zero`: a generator is
  nonzero on every fibre, with [Stacks, Tag 0A1H] as an argument.
* `PushforwardGenerator.isRelativeEffectiveCartierDivisor_zeroScheme_of_isGenerator`: its zero
  scheme is a relative effective Cartier divisor when the fibres are integral.
* `AlgebraicGeometry.PushforwardGenerator.nonempty_derivedPushforward_fiber_iso`:
  `R(p_v)_*(ℒ_v[0]) ≅ 𝒪_{κ(v)}[0]` on every fibre.

## References

* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.PushforwardGenerator

variable {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (L : Y.Modules)

/-- **The pullback of the global section of `s` is nonzero as soon as `g^*s` is.** -/
theorem pullbackGlobalSections_ne_zero_of_map_ne_zero (s : SheafOfModules.unit Y.ringCatSheaf ⟶ L)
    (hs : (Scheme.Modules.pullback g).map s ≠ 0) :
    pullbackGlobalSections g L ((L.unitHomEquiv s).eval (op ⊤)) ≠ 0 := by
  rw [Stacks.PullbackUnitComparisonSection.pullbackGlobalSections_unitHomEquiv g L
    (L.unitHomEquiv s), Equiv.symm_apply_apply]
  intro h0
  apply hs
  let e := Stacks.PullbackAlgebra.pullbackUnitIso g.toLRSHom.toShHom
  let t : Scheme.unitModule Y' ⟶ (Scheme.Modules.pullback g).obj L :=
    e.inv ≫ (Scheme.Modules.pullback g).map s
  have h2 : t = 0 := by
    apply (Scheme.Modules.unitHomEquivTop ((Scheme.Modules.pullback g).obj L)).symm.injective
    refine h0.trans ?_
    show (0 : Γ((Scheme.Modules.pullback g).obj L, ⊤)) =
      ((0 : Scheme.unitModule Y' ⟶ _).val.app (op ⊤)) (1 : Y'.ringCatSheaf.obj.obj (op ⊤))
    rfl
  have h3 : (Scheme.Modules.pullback g).map s = e.hom ≫ t := (e.hom_inv_id_assoc _).symm
  rw [h3, h2]
  exact comp_zero

/-- The derived base change map of the fibre square, for a finite locally free `ℒ`, is invertible
by [Stacks, Tag 0B91] (1). -/
private theorem isIso_derivedBaseChangeMap_fiber {S : Scheme.{u}} (p : Y ⟶ S) [IsProper p]
    [Flat p] [LocallyOfFinitePresentation p]
    (hL : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) L) (v : S)
    (hsq : IsPullback (p.fiberι v) (p.fiberToSpecResidueField v) p (S.fromSpecResidueField v)) :
    IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap
      (p.fiberι v).toLRSHom.toShHom (p.fiberToSpecResidueField v).toLRSHom.toShHom
      p.toLRSHom.toShHom (S.fromSpecResidueField v).toLRSHom.toShHom
      (comp_toShHom_of_comm hsq.w) ((DerivedCategory.singleFunctor Y.Modules 0).obj L)) :=
  have hf : FinitePresentation p := ⟨inferInstance, inferInstance, inferInstance⟩
  (ProperFlatBaseChange.isPerfect_derivedPushforward_and_isIso_derivedBaseChangeMap_of_flat
    p hf inferInstance inferInstance _
    (isPerfect_singleFunctor_of_isFiniteLocallyFree Y L hL)).2 _ _ _ hsq

/-- **A generator is nonzero on every fibre**, with [Stacks, Tag 0A1H] as an argument (`hPerfBC`,
typed as in `AlgebraicGeometry.RigidifiedPicard.rankOneLocus_isSubfunctor_and_representable`): for
`p : Y ⟶ S` proper, flat and of finite presentation, `ℒ` finite locally free and `s` a generator
of `ℒ` relative to `p`, the pullback of the global section of `s` to the fibre `Y_v` is nonzero.
The derived base change map of the fibre square is invertible by [Stacks, Tag 0B91] (1). -/
theorem pullbackGlobalSections_fiberι_ne_zero
    (hPerfBC : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
      (E : DerivedCategory X.Modules) (_hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
      (G : CochainComplex X.Modules ℤ)
      (_hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
        FlatProperSupportFinitelyPresented f G),
      RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforward f.toLRSHom.toShHom).obj
            (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ∧
        ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
          (hsq : IsPullback g' f' f g),
          IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G))
    {S : Scheme.{u}} (p : Y ⟶ S) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    (hL : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) L)
    (hLflat : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.sheaf) L)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ L) (hs : IsGenerator p.toLRSHom.toShHom L s)
    (v : S) :
    pullbackGlobalSections (p.fiberι v) L ((L.unitHomEquiv s).eval (op ⊤)) ≠ 0 := by
  apply pullbackGlobalSections_ne_zero_of_map_ne_zero
  have hsq : IsPullback (p.fiberι v) (p.fiberToSpecResidueField v) p (S.fromSpecResidueField v) :=
    IsPullback.of_hasPullback _ _
  have hbc := isIso_derivedBaseChangeMap_fiber L p hL v hsq
  exact map_ne_zero_of_isGenerator p.toLRSHom.toShHom L (p.fiberι v).toLRSHom.toShHom
    (p.fiberToSpecResidueField v).toLRSHom.toShHom (S.fromSpecResidueField v).toLRSHom.toShHom
    (comp_toShHom_of_comm hsq.w) hLflat hbc
    (Scheme.not_isZero_unit (Spec (S.residueField v))) s hs

/-- **The zero scheme of a generator is a relative effective Cartier divisor** when the fibres
of `p` are integral, with [Stacks, Tag 0A1H] as an argument (`hPerfBC`). It is locally principal
([Stacks, Tag 02OR] (3)); on each fibre it is the zero scheme of the pulled-back section
([Stacks, Tag 0B6Y]), which is nonzero (`pullbackGlobalSections_fiberι_ne_zero`), hence regular on
the integral fibre, so an effective Cartier divisor ([Stacks, Tag 02OR] (4)); and a locally
principal closed subscheme all of whose fibres are effective Cartier divisors is a relative
effective Cartier divisor ([Stacks, Tag 062Y]). -/
theorem isRelativeEffectiveCartierDivisor_zeroScheme_of_isGenerator
    (hPerfBC : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
      (E : DerivedCategory X.Modules) (_hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
      (G : CochainComplex X.Modules ℤ)
      (_hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
        FlatProperSupportFinitelyPresented f G),
      RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforward f.toLRSHom.toShHom).obj
            (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ∧
        ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
          (hsq : IsPullback g' f' f g),
          IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G))
    {S : Scheme.{u}} (p : Y ⟶ S) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ L) (hs : IsGenerator p.toLRSHom.toShHom L s)
    (hint : ∀ v : S, IsIntegral (p.fiber v)) :
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor p
      (zeroScheme Y L ((L.unitHomEquiv s).eval (op ⊤))) := by
  refine Stacks.Divisors.isRelativeEffectiveCartierDivisor_of_isLocallyPrincipal_of_fibres p _
    (isLocallyPrincipal_zeroScheme Y L _) fun v => ?_
  have := hint v
  have hz := Stacks.Divisors.zeroScheme_pullback (p.fiberι v) L ((L.unitHomEquiv s).eval (op ⊤))
  have hne := pullbackGlobalSections_fiberι_ne_zero L hPerfBC p
    (Stacks.Divisors.isFiniteLocallyFree_of_isInvertible Y L) (Stacks.Chow.isFlat_of_isInvertible L)
    s hs v
  rw [Stacks.PullbackUnitComparisonSection.pullbackGlobalSections_unitHomEquiv _ L
    (L.unitHomEquiv s), Equiv.symm_apply_apply] at hz hne
  have hcart := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection _ _ _).2
    (isRegularSection_of_eval_top_ne_zero _ _ hne)
  exact hz ▸ hcart

/-- **On a fibre, the derived pushforward of `ℒ` is the structure sheaf**: if `ℒ` is invertible
with a generator relative to `p`, then `R(p_v)_*(ℒ_v[0]) ≅ 𝒪_{κ(v)}[0]` on every fibre, with
[Stacks, Tag 0A1H] as an argument (`hPerfBC`), through [Stacks, Tag 0B91] (1) for the fibre square.
-/
theorem nonempty_derivedPushforward_fiber_iso
    (hPerfBC : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (hf : FinitePresentation f)
      (E : DerivedCategory X.Modules) (_hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
      (G : CochainComplex X.Modules ℤ)
      (_hG : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
        FlatProperSupportFinitelyPresented f G),
      RingedSpace.IsPerfect (X := S.toRingedSpace)
          ((derivedPushforward f.toLRSHom.toShHom).obj
            (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ∧
        ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
          (hsq : IsPullback g' f' f g),
          IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G))
    {S : Scheme.{u}} (p : Y ⟶ S) [IsProper p] [Flat p] [LocallyOfFinitePresentation p]
    [SheafOfModules.IsInvertible Y.sheaf.obj Y.ringCatSheaf.property L]
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ L) (hs : IsGenerator p.toLRSHom.toShHom L s)
    (v : S) :
    Nonempty ((derivedPushforward (p.fiberToSpecResidueField v).toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing (p.fiber v).toRingedSpace)) 0).obj
          ((RingedSpaceModuleAdjunction.modulePullback (p.fiberι v).toLRSHom.toShHom).obj L)) ≅
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing (Spec (S.residueField v)).toRingedSpace)) 0).obj
        (SheafOfModules.unit (structureSheafRing (Spec (S.residueField v)).toRingedSpace))) := by
  have hsq : IsPullback (p.fiberι v) (p.fiberToSpecResidueField v) p (S.fromSpecResidueField v) :=
    IsPullback.of_hasPullback _ _
  have hbc := isIso_derivedBaseChangeMap_fiber L p
    (Stacks.Divisors.isFiniteLocallyFree_of_isInvertible Y L) v hsq
  exact nonempty_derivedPushforward_pullback_iso p.toLRSHom.toShHom L _ _ _
    (comp_toShHom_of_comm hsq.w) (Stacks.Chow.isFlat_of_isInvertible L) hbc s hs

end AlgebraicGeometry.PushforwardGenerator

end
