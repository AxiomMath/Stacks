module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdeals
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismToAffineScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.RingHomIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.AdicSectionsAffineDescent
public import StacksFrontier.AlgebraicGeometry.KerDetected.RingColimit

/-!
# The base change of a closed subscheme of an affine scheme cuts out the extended ideal

Let `X` be an algebraic space over `S` with a morphism `π : X ⟶ T` to an affine object of the
big fppf site, let `ι : T' ⟶ T` be a closed immersion of affine schemes with ideal
`J = ker(Γ(T) ⟶ Γ(T'))`, and let `i : Z ⟶ X` be the base change of `ι` along `π`.  This file
proves that `i` is a closed immersion whose ideal is `J 𝒪_X`: over an affine étale chart `U` of
`X` the kernel of `Γ(U) ⟶ Γ(Z ×_X U)` is `J Γ(U)`, the base change `Z ×_X U ⟶ U` being the base
change of `ι` along `U ⟶ T`.  Consequently, for every `𝒪_X`-module `M`, the unit
`M ⟶ i_* i^* M` of Stacks 03LU identifies `M / J M` with `i_* i^* M` — Stacks 04CJ for this
closed immersion, with its ideal computed.

## Main results

* `AlgebraicGeometry.Space.ker_structureSharp_obj_of_isAffine_of_isPullback`: on an affine chart
  the ideal of `i` is the extension of `J`.
* `AlgebraicGeometry.Space.mem_ker_structureSharp_of_isPullback`: the elements of `J` lie in the
  ideal of `i` on every chart.
* `AlgebraicGeometry.Space.baseChangeQuotientIso`: `M / J M ≅ i_* i^* M`, compatibly with the
  unit.

## References

* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Z : AlgebraicSpaces B S hS} {T T' : BigFppfOver B S hS}
  (π : X ⟶ schemeSpace T) (ι : T' ⟶ T) (i : Z ⟶ X) (p : Z ⟶ schemeSpace T')
  (hpb : IsPullback i p π (schemeSpaceMap ι))

/-- The ideal `J = ker(Γ(T) ⟶ Γ(T'))` of a morphism of the site, on global functions. -/
abbrev siteMapKer : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) :=
  RingHom.ker ((BigFppfOver.toScheme B S hS).map ι).appTop.hom

/-- The morphism of the site from the object of an étale chart to `T` along which the chart maps
to `T`. -/
abbrev chartToTarget (V : SmallEtale B S hS X.1) : V.1.left ⟶ T :=
  yoneda.preimage (V.1.hom ≫ π.hom)

include hpb in
/-- **A base change of a closed immersion of schemes is a closed immersion.** -/
theorem isClosedImmersion_of_isPullback_schemeSpaceMap
    (hι : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι)) :
    IsClosedImmersion B S hS i.hom :=
  have := isClosedImmersion_isStableUnderBaseChange B S hS
  MorphismProperty.of_isPullback ((AlgebraicSpaces.isPullback_hom B S hS hpb).flip)
    ((presheaf_yoneda_map_iff B S hS inferInstance _).2 hι)

include hpb in
/-- The square exhibiting the base change of `Z` to an étale chart of `X` as the base change of
`ι` along the chart. -/
theorem isPullback_chart_of_isPullback (hf : yoneda.relativelyRepresentable i.hom)
    (V : SmallEtale B S hS X.1) :
    IsPullback (yoneda.preimage (hf.fst V.1.hom ≫ p.hom)) (hf.snd V.1.hom)
      ι (chartToTarget B S hS π V) := by
  have h2 : IsPullback (yoneda.map (yoneda.preimage (hf.fst V.1.hom ≫ p.hom)))
      (yoneda.map (hf.snd V.1.hom)) (yoneda.map ι) (yoneda.map (chartToTarget B S hS π V)) := by
    rw [yoneda.map_preimage, yoneda.map_preimage]
    exact (hf.isPullback V.1.hom).paste_horiz ((AlgebraicSpaces.isPullback_hom B S hS hpb).flip)
  exact IsPullback.of_map_of_faithful yoneda h2

include π in
/-- Pullback of global functions along `π`, the scalars from `T` on `𝒪_X`-modules: a function on
`T` is sent to the family of its pullbacks to the étale charts of `X`. -/
def targetScalars :
    Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) where
  toFun a := ⟨fun U => ((BigFppfOver.toScheme B S hS).map
      (chartToTarget B S hS π U.unop)).appTop.hom a, by
    intro U V g
    have hp : (SmallEtale.toOver B S hS X.1).map g.unop ≫ chartToTarget B S hS π U.unop =
        chartToTarget B S hS π V.unop := by
      apply yoneda.map_injective
      rw [Functor.map_comp, yoneda.map_preimage, yoneda.map_preimage]
      exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ π.hom) g.unop.hom.w)
    change (((BigFppfOver.toScheme B S hS).map (chartToTarget B S hS π U.unop)).appTop ≫
        ((BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map g.unop)).appTop).hom
          a = _
    rw [← Scheme.Hom.comp_appTop, ← Functor.map_comp, hp]⟩
  map_one' := Subtype.ext (funext fun _ => map_one _)
  map_mul' a b := Subtype.ext (funext fun _ => map_mul _ a b)
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' a b := Subtype.ext (funext fun _ => map_add _ a b)

/-- The component of `targetScalars` at a chart `U` is the pullback of global functions along
`chartToTarget`. -/
theorem targetScalars_apply (a : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    (targetScalars B S hS π a).1 U =
      ((BigFppfOver.toScheme B S hS).map (chartToTarget B S hS π U.unop)).appTop.hom a :=
  rfl

/-- The base change `i` of a morphism of the site is relatively representable. -/
private theorem relativelyRepresentable_of_isPullback
    (hpb : IsPullback i p π (schemeSpaceMap ι)) : yoneda.relativelyRepresentable i.hom :=
  MorphismProperty.of_isPullback ((AlgebraicSpaces.isPullback_hom B S hS hpb).flip)
    (Functor.relativelyRepresentable.map yoneda _)

variable [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]

include hpb in
/-- **The ideal of the base change on an affine chart.** On an affine étale chart `V` of `X` the
kernel of the structure map of `i` is the extension of `J = ker(Γ(T) ⟶ Γ(T'))` along
`Γ(T) ⟶ Γ(V)`. -/
theorem ker_structureSharp_obj_of_isAffine_of_isPullback
    (hsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map ι).appTop.hom)
    (V : SmallEtale B S hS X.1)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V.1.left)] :
    RingHom.ker ((structureSharp B S hS i).hom.app (op V)).hom =
      Ideal.map ((BigFppfOver.toScheme B S hS).map (chartToTarget B S hS π V)).appTop.hom
        (siteMapKer B S hS ι) := by
  have hf := relativelyRepresentable_of_isPullback B S hS π ι i p hpb
  rw [ker_structureSharp_eq B S hS _ hf V, chartPullbackRingHom_chartBaseChangeArrow,
    Scheme.Γ_map_op]
  exact GoodDiagramKer.ker_eq_map_of_isPushout_of_surjective
    ((BigFppfOver.toScheme B S hS).map ι).appTop.hom
    ((BigFppfOver.toScheme B S hS).map (chartToTarget B S hS π V)).appTop.hom
    ((BigFppfOver.toScheme B S hS).map
      (yoneda.preimage (hf.fst V.1.hom ≫ p.hom))).appTop.hom
    ((BigFppfOver.toScheme B S hS).map (hf.snd V.1.hom)).appTop.hom
    (isPushout_appTop_of_isPullback ((isPullback_chart_of_isPullback B S hS π ι i p hpb hf V).map
      (BigFppfOver.toScheme B S hS))) hsurj

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
include hpb in
/-- **The elements of `J` lie in the ideal of the base change on every chart**: the base change
of `Z` to a chart lies over `T'`, on which `J` vanishes. -/
theorem mem_ker_structureSharp_of_isPullback (V : SmallEtale B S hS X.1)
    {a : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)} (ha : a ∈ siteMapKer B S hS ι) :
    ringHomChartHom X.1 X.2 (targetScalars B S hS π) V a ∈
      RingHom.ker ((structureSharp B S hS i).hom.app (op V)).hom := by
  have hf := relativelyRepresentable_of_isPullback B S hS π ι i p hpb
  rw [ker_structureSharp_eq B S hS _ hf V, chartPullbackRingHom_chartBaseChangeArrow,
    Scheme.Γ_map_op]
  have hw := congrArg (fun q => ((BigFppfOver.toScheme B S hS).map q).appTop)
    (isPullback_chart_of_isPullback B S hS π ι i p hpb hf V).w
  simp only [Functor.map_comp, Scheme.Hom.comp_appTop] at hw
  refine RingHom.mem_ker.mpr ((congrArg (fun f => f.hom a) hw.symm).trans ?_)
  rw [CommRingCat.hom_comp, RingHom.comp_apply, RingHom.mem_ker.mp ha]
  exact map_zero _

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
include hpb in
/-- **`J` kills every direct image along the base change.** -/
theorem globalSmul_modulePushforward_of_isPullback
    {a : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)} (ha : a ∈ siteMapKer B S hS ι)
    (N : Modules.{u, u} B S hS Z.1 Z.2) :
    Stacks.Cohomology.SiteModules.globalSmul _ (targetScalars B S hS π a)
      ((modulePushforward B S hS i).obj N) = 0 := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun U => ?_)
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  exact annihilatedByKerIdeal_modulePushforward B S hS i N U _
    ((SheafOfModules.mem_kerIdeal _ U _).2
      (mem_ker_structureSharp_of_isPullback B S hS π ι i p hpb U.unop ha)) x

include hpb in
/-- **The ideal of the base change annihilates `M / J M`.** -/
theorem annihilatedByKerIdeal_idealQuotient_of_isPullback
    (hsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map ι).appTop.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    AnnihilatedByKerIdeal B S hS i
      (idealQuotient (targetScalars B S hS π) M (siteMapKer B S hS ι)) := by
  rw [show siteMapKer B S hS ι = siteMapKer B S hS ι ^ 1 from (pow_one _).symm]
  intro U r hr y
  refine SmallEtale.C1573.eq_of_forall_isAffine B S hS X.1 X.2
    (Stacks.SheafOfModules.ImageSubsheaf.isSheaf_forget
      (idealQuotient (targetScalars B S hS π) M (siteMapKer B S hS ι ^ 1))) fun W g hW => ?_
  let : Module ((structureRingSheaf B S hS X).obj.obj U)
      ((idealQuotient (targetScalars B S hS π) M (siteMapKer B S hS ι ^ 1)).val.obj U) :=
    ((idealQuotient (targetScalars B S hS π) M (siteMapKer B S hS ι ^ 1)).val.obj U).isModule
  change (idealQuotient (targetScalars B S hS π) M (siteMapKer B S hS ι ^ 1)).val.map g.op
      (r • y) =
    (idealQuotient (targetScalars B S hS π) M (siteMapKer B S hS ι ^ 1)).val.map g.op 0
  rw [map_zero]
  refine (PresheafOfModules.map_smul
    (idealQuotient (targetScalars B S hS π) M (siteMapKer B S hS ι ^ 1)).val g.op r y).trans ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj W.1.left) := hW
  have hrW : (structureRingSheaf B S hS X).obj.map g.op r ∈
      Ideal.map (ringHomChartHom X.1 X.2 (targetScalars B S hS π) W) (siteMapKer B S hS ι) := by
    have h := (SheafOfModules.mem_kerIdeal _ (op W) _).1
      ((SheafOfModules.kerIdeal (structureSharp B S hS i)).map_mem g.op hr)
    rwa [ker_structureSharp_obj_of_isAffine_of_isPullback B S hS π ι i p hpb hsurj W] at h
  have hmem : (structureRingSheaf B S hS X).obj.map g.op r ∈
      chartIdeal B S hS ⟨X.1, X.2⟩
        (ringHomIdealSheaf X.1 X.2 (targetScalars B S hS π) (siteMapKer B S hS ι)) W ^ 1 := by
    rw [pow_one]
    exact map_le_ringHomIdealSheaf_obj _ W hrW
  exact ringHom_smul_idealQuotient_eq_zero (φ := targetScalars B S hS π) M
    (siteMapKer B S hS ι) 1 W _ hmem
    (show ((idealQuotient (targetScalars B S hS π) M (siteMapKer B S hS ι ^ 1)).val.obj
      (op W) : Type u) from
      (idealQuotient (targetScalars B S hS π) M (siteMapKer B S hS ι ^ 1)).val.map g.op y)

/-- The map `M / J M ⟶ i_* i^* M` induced by the unit of Stacks 03LU. -/
def baseChangeQuotientUnitMap (M : Modules.{u, u} B S hS X.1 X.2) :
    idealQuotient (targetScalars B S hS π) M (siteMapKer B S hS ι) ⟶
      (modulePushforward B S hS i).obj ((modulePullback B S hS i).obj M) :=
  cokernel.desc _ ((modulePullbackAdjunction B S hS i).unit.app M) (by
    refine idealMultiple_hom_ext _ M _ fun a ha => ?_
    rw [comp_zero, ← Category.assoc, idealMultipleFactor_ι,
      ← Stacks.Cohomology.SiteModules.comp_globalSmul,
      globalSmul_modulePushforward_of_isPullback B S hS π ι i p hpb ha, comp_zero])

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- Precomposed with the quotient map `M ⟶ M / J M`, `baseChangeQuotientUnitMap` is the unit
`M ⟶ i_* i^* M`. -/
@[reassoc (attr := simp)]
theorem idealQuotientπ_baseChangeQuotientUnitMap (M : Modules.{u, u} B S hS X.1 X.2) :
    idealQuotientπ (targetScalars B S hS π) M (siteMapKer B S hS ι) ≫
        baseChangeQuotientUnitMap B S hS π ι i p hpb M =
      (modulePullbackAdjunction B S hS i).unit.app M :=
  cokernel.π_desc _ _ _

/-- If `ι` is a closed immersion surjective on global functions, the map
`M / J M ⟶ i_* i^* M` induced by the unit is an isomorphism. -/
theorem isIso_baseChangeQuotientUnitMap
    (hι : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι))
    (hsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map ι).appTop.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    IsIso (baseChangeQuotientUnitMap B S hS π ι i p hpb M) := by
  have hi := isClosedImmersion_of_isPullback_schemeSpaceMap B S hS π ι i p hpb hι
  have : Epi ((modulePullbackAdjunction B S hS i).unit.app M) :=
    epi_modulePullbackAdjunction_unit_of_essImage_of_annihilated B S hS i hi
      (fun N hN => essImage_modulePushforward_of_annihilatedByKerIdeal B S hS i hi N hN) M
  have hepi : Epi (baseChangeQuotientUnitMap B S hS π ι i p hpb M) :=
    epi_of_epi_fac (idealQuotientπ_baseChangeQuotientUnitMap B S hS π ι i p hpb M)
  have hQ : IsIso ((modulePullbackAdjunction B S hS i).unit.app
      (idealQuotient (targetScalars B S hS π) M (siteMapKer B S hS ι))) :=
    (essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit B S hS i hi _).1
      ((essImage_modulePushforward_iff B S hS i hi _).2
        (annihilatedByKerIdeal_idealQuotient_of_isPullback B S hS π ι i p hpb hsurj M))
  have hfac : baseChangeQuotientUnitMap B S hS π ι i p hpb M ≫
      (modulePullback B S hS i ⋙ modulePushforward B S hS i).map
        (idealQuotientπ (targetScalars B S hS π) M (siteMapKer B S hS ι)) =
      (modulePullbackAdjunction B S hS i).unit.app
        (idealQuotient (targetScalars B S hS π) M (siteMapKer B S hS ι)) := by
    refine (cancel_epi (idealQuotientπ (targetScalars B S hS π) M (siteMapKer B S hS ι))).1 ?_
    rw [← Category.assoc, idealQuotientπ_baseChangeQuotientUnitMap]
    exact ((modulePullbackAdjunction B S hS i).unit.naturality
      (idealQuotientπ (targetScalars B S hS π) M (siteMapKer B S hS ι))).symm
  have : Mono ((modulePullbackAdjunction B S hS i).unit.app
      (idealQuotient (targetScalars B S hS π) M (siteMapKer B S hS ι))) :=
    @IsIso.mono_of_iso _ _ _ _ _ hQ
  have hmono : Mono (baseChangeQuotientUnitMap B S hS π ι i p hpb M) := mono_of_mono_fac hfac
  exact isIso_of_mono_of_epi _

/-- **`M / J M ≅ i_* i^* M`**, the isomorphism induced by the unit of Stacks 03LU for the base
change `i` of a closed immersion of affine schemes `ι` with ideal `J` (Stacks 04CJ, with the
ideal of `i` computed as `J 𝒪_X`). -/
def baseChangeQuotientIso
    (hι : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι))
    (hsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map ι).appTop.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    idealQuotient (targetScalars B S hS π) M (siteMapKer B S hS ι) ≅
      (modulePushforward B S hS i).obj ((modulePullback B S hS i).obj M) :=
  have := isIso_baseChangeQuotientUnitMap B S hS π ι i p hpb hι hsurj M
  asIso (baseChangeQuotientUnitMap B S hS π ι i p hpb M)

/-- Precomposed with the quotient map `M ⟶ M / J M`, the isomorphism `baseChangeQuotientIso` is
the unit `M ⟶ i_* i^* M`. -/
@[reassoc (attr := simp)]
theorem idealQuotientπ_baseChangeQuotientIso_hom
    (hι : AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map ι))
    (hsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map ι).appTop.hom)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    idealQuotientπ (targetScalars B S hS π) M (siteMapKer B S hS ι) ≫
        (baseChangeQuotientIso B S hS π ι i p hpb hι hsurj M).hom =
      (modulePullbackAdjunction B S hS i).unit.app M :=
  idealQuotientπ_baseChangeQuotientUnitMap B S hS π ι i p hpb M

end AlgebraicGeometry.Space

end
