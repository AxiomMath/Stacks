module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicChartAnnihilation
public import StacksFrontier.AlgebraicGeometry.Spaces.PullbackIdealQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicKernelCokernelAnnihilated

/-!
# Stacks 08BD: the map `α : (𝓖_n) ⟶ (f_*𝓕)^∧`

Let `f : X ⟶ Y` be a representable proper morphism of Noetherian algebraic spaces over `S`, let
`𝓙, 𝓚 ⊆ 𝒪_Y` be quasi-coherent sheaves of ideals with `f` an isomorphism over `Y ∖ V(𝓚)`, and let
`β : (f^*𝓖_n) ≅ 𝓕^∧` be an isomorphism in `Coh(X, f⁻¹𝓙 𝒪_X)`.  This file proves Stacks 08BD:
there is a map `α : (𝓖_n) ⟶ (f_*𝓕)^∧` in `Coh(Y, 𝓙)` whose kernel and cokernel are annihilated
by a power of `𝓚`.

## Main results

* `AlgebraicGeometry.Space.isIso_limMap_directImageCompletionComparison` — the theorem on formal
  functions: the comparison `(f_*𝓕)^∧ ⟶ f_*(𝓕^∧)` is an isomorphism on limits.
* `AlgebraicGeometry.Space.exists_comp_directImageCompletionComparison_eq` — the map `α` whose
  composite with that comparison is the system `γ` of adjunction maps followed by `f_*β`.
* `AlgebraicGeometry.Space.exists_kernel_cokernel_annihilated_of_comp_eq` — the kernels and
  cokernels of such a map are annihilated by a power of `𝓚`, the notion
  `AlgebraicGeometry.Space.IsKernelCokernelAnnihilatedByPower` of Stacks 08BA.
* `AlgebraicGeometry.Space.exists_completionMap_kernel_cokernel_annihilated` — **Stacks 08BD.**

## Implementation notes

The direct image is computed on base-changed charts
(`AlgebraicGeometry.Space.baseChangeDirectImage`) throughout the construction, where its sections
over `V` are on the nose the sections over `V ×_Y X`; the statement is transported to
`AlgebraicGeometry.Space.modulePushforward` at the end along
`AlgebraicGeometry.Space.modulePushforwardChartIso`.

The two `Fact` instances recording local Noetherianity, which the completion functors are indexed
by, are produced from the Noetherian hypotheses inside the statement.

## References

* [Stacks Project, Tag 08BD](https://stacks.math.columbia.edu/tag/08BD)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
* [Stacks Project, Tag 07UK](https://stacks.math.columbia.edu/tag/07UK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The sections over a chart of a morphism of limits are the morphism of the limits of the
sections.**  If the limit of the sections over `V` of a morphism of inverse systems is invertible,
then the sections over `V` of the morphism of limits are bijective. -/
theorem bijective_limMap_val_app {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} {E D : ℕᵒᵖ ⥤ Modules.{u, u} B S hS F hF} (c : E ⟶ D)
    (V : SmallEtale B S hS F)
    [hc : IsIso (limMap (Functor.whiskerRight c (SheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) (op V))))] :
    Function.Bijective ((limMap c).val.app (op V)).hom := by
  let ev := SheafOfModules.evaluation
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) (op V)
  have h' : ev.map (limMap c) ≫ (limitSectionsIso B S hS F hF D V).hom =
      (limitSectionsIso B S hS F hF E V).hom ≫ limMap (Functor.whiskerRight c ev) := by
    refine limit.hom_ext fun n => ?_
    have h1 := limitSectionsIso_hom_chartSectionsLevel B S hS F hF D V n.unop
    have h2 := limitSectionsIso_hom_chartSectionsLevel B S hS F hF E V n.unop
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (ev.map (limMap c) ≫ ·) h1).trans ?_
    refine (ev.map_comp _ _).symm.trans ?_
    refine (congrArg ev.map (limMap_π c n)).trans ?_
    refine (ev.map_comp _ _).trans ?_
    refine (congrArg (· ≫ ev.map (c.app n)) h2.symm).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    exact congrArg ((limitSectionsIso B S hS F hF E V).hom ≫ ·)
      (limMap_π (Functor.whiskerRight c ev) n).symm
  have h : ev.map (limMap c) = (limitSectionsIso B S hS F hF E V).hom ≫
      limMap (Functor.whiskerRight c ev) ≫ (limitSectionsIso B S hS F hF D V).inv :=
    ((Iso.eq_comp_inv _).mpr h').trans (Category.assoc _ _ _)
  have hL := (ConcreteCategory.isIso_iff_bijective _).mp hc
  have hE := (ConcreteCategory.isIso_iff_bijective _).mp
    (inferInstance : IsIso (limitSectionsIso B S hS F hF E V).hom)
  have hD := (ConcreteCategory.isIso_iff_bijective _).mp
    (inferInstance : IsIso (limitSectionsIso B S hS F hF D V).inv)
  have hfun : (ev.map (limMap c)).hom = ((limitSectionsIso B S hS F hF E V).hom ≫
      limMap (Functor.whiskerRight c ev) ≫ (limitSectionsIso B S hS F hF D V).inv).hom :=
    congrArg ModuleCat.Hom.hom h
  have hb : Function.Bijective ((limitSectionsIso B S hS F hF E V).hom ≫
      limMap (Functor.whiskerRight c ev) ≫ (limitSectionsIso B S hS F hF D V).inv).hom :=
    hD.comp (hL.comp hE)
  change Function.Bijective (ev.map (limMap c)).hom
  exact hfun ▸ hb

section GlobalComparison

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (hfp : IsProper B S hS f.hom)
    (J : (SheafOfModules.unit.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
    (hJq : J.toSheafOfModules.IsQuasicoherentOnSite)
    [hXloc : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    [hYloc : Fact (HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hIq : (pullbackIdealSubsheaf B S hS f hf J).toSheafOfModules.IsQuasicoherentOnSite)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (hFF : IsCoherent B S hS Y.1 Y.2 ((baseChangeDirectImage B S hS f hf).obj F))

include hfp in
/-- **The theorem on formal functions for a representable proper morphism of algebraic spaces**:
the comparison `c : (f_*𝓕)^∧ ⟶ f_*(𝓕^∧)` of Stacks 08BD becomes an isomorphism on limits.  It is
checked on the sections over the affine charts of `Y`, where it is the theorem on formal functions
on the chart's scheme. -/
theorem isIso_limMap_directImageCompletionComparison :
    IsIso (limMap (directImageCompletionComparison B S hS f hf J hJq hIq ⟨F, hF⟩ hFF)) := by
  have hJc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _ hJq
  have hIc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 _ hIq
  refine SmallEtale.isIso_of_bijective_app_of_isAffineChart B S hS Y.1 Y.2 _ fun Z hZ => ?_
  have : IsAffine (chartScheme Z) := hZ
  have : IsLocallyNoetherian (chartScheme ((smallBaseChange B S hS f hf).obj Z)) :=
    isLocallyNoetherian_chart B S hS hXloc.out _
  have : IsLocallyNoetherian (chartScheme Z) := isLocallyNoetherian_chart B S hS hYloc.out Z
  have : _root_.AlgebraicGeometry.IsProper (chartBaseChangeMorphism B S hS f hf Z) :=
    isProper_toScheme_smallBaseChangeProjection B S hS f hf hfp Z
  have := isIso_limMap_directImageCompletionComparisonTower B S hS f hf J hIq Z F hF hJq hFF hJc
    hIc
  exact bijective_limMap_val_app B S hS _ Z

end GlobalComparison

section ChartGlobal

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (hfp : IsProper B S hS f.hom)
    (J : (SheafOfModules.unit.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
    (hJ : J.toSheafOfModules.IsQuasicoherentOnSite)
    [hXloc : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    [hYloc : Fact (HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hIq : (pullbackIdealSubsheaf B S hS f hf J).toSheafOfModules.IsQuasicoherentOnSite)
    (G : CoherentAdicSystems B S hS Y.1 Y.2 J)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (hFF : IsCoherent B S hS Y.1 Y.2 ((baseChangeDirectImage B S hS f hf).obj F))
    (β : G.obj ⋙ modulePullback B S hS f ≅
      ((completionFunctor B S hS X.1 X.2 (pullbackIdealSubsheaf B S hS f hf J) hIq).obj
        ⟨F, hF⟩).obj)

include hfp in
/-- **The map `α` of Stacks 08BD into the completion of the base-changed direct image**: there is
a morphism `α : (𝓖_n) ⟶ (f_*𝓕)^∧` of coherent adic systems whose composite with the comparison
`c : (f_*𝓕)^∧ ⟶ f_*(𝓕^∧)` is the system `γ` of adjunction maps followed by `f_*β`. -/
theorem exists_comp_directImageCompletionComparison_eq :
    ∃ α : G ⟶ (completionFunctor B S hS Y.1 Y.2 J hJ).obj ⟨_, hFF⟩,
      α.hom ≫ directImageCompletionComparison B S hS f hf J hJ hIq ⟨F, hF⟩ hFF =
        directImageChartComparison B S hS f hf (pullbackIdealSubsheaf B S hS f hf J) hIq G.obj
          ⟨F, hF⟩ β := by
  have hJc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _ hJ
  have hN : ∀ Z : SmallEtale B S hS Y.1, IsAffine (chartScheme Z) →
      IsNoetherianAffineChart B S hS Y.1 Z := fun Z hZ => by
    have : IsAffine (chartScheme Z) := hZ
    have : IsLocallyNoetherian (chartScheme Z) := isLocallyNoetherian_chart B S hS hYloc.out Z
    exact ⟨hZ, IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top (chartScheme Z)⟩⟩
  have := isIso_limMap_directImageCompletionComparison B S hS f hf hfp J hJ hIq F hF hFF
  exact ⟨_, systemMapOfComparisonIso_comp B S hS Y.1 Y.2 J hJc hN _ _⟩

include hfp in
/-- **The kernel–cokernel bound of Stacks 08BD for the base-changed direct image.**  If
`α : (𝓖_n) ⟶ (f_*𝓕)^∧` composed with the comparison `c` is `γ`, then one power of `𝓚` kills all
the levelwise kernels and cokernels of `α`: the scheme case 088B on a surjective Noetherian affine
chart of `Y` gives the exponent there, and quasi-coherence spreads it over `Y`. -/
theorem exists_kernel_cokernel_annihilated_of_comp_eq (hZ : B.Contains (⊤_ Scheme.{u}))
    (hY : IsNoetherian B S hS hZ Y.1)
    (K : (SheafOfModules.unit.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
    (hK : K.toSheafOfModules.IsQuasicoherentOnSite)
    (hiso : IsIso ((idealComplementSubfunctor B S hS Y K).fromPreimage f.hom))
    (α : G ⟶ (completionFunctor B S hS Y.1 Y.2 J hJ).obj ⟨_, hFF⟩)
    (hα : α.hom ≫ directImageCompletionComparison B S hS f hf J hJ hIq ⟨F, hF⟩ hFF =
        directImageChartComparison B S hS f hf (pullbackIdealSubsheaf B S hS f hf J) hIq G.obj
          ⟨F, hF⟩ β) :
    IsKernelCokernelAnnihilatedByPower B S hS Y.1 Y.2 K α.hom := by
  have hJc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _ hJ
  have hKc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS Y.1 Y.2 _ hK
  have hIc := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 _ hIq
  obtain ⟨U, hUN, hUsurj, -⟩ := exists_surjective_isNoetherianAffineChart B S hS hZ Y hY
  have hUa : IsAffine (chartScheme U) := hUN.1
  have : IsNoetherianRing Γ(chartScheme U, ⊤) := hUN.2
  have : IsLocallyNoetherian (chartScheme U) := isLocallyNoetherian_chart B S hS hYloc.out U
  have : IsLocallyNoetherian (chartScheme ((smallBaseChange B S hS f hf).obj U)) :=
    isLocallyNoetherian_chart B S hS hXloc.out _
  have : _root_.AlgebraicGeometry.IsProper (chartBaseChangeMorphism B S hS f hf U) :=
    isProper_toScheme_smallBaseChangeProjection B S hS f hf hfp U
  have hch := @exists_pow_smul_chart_kernel_cokernel B S hS X Y f hf J hJc U hUa G hIc hXloc hIq
    inferInstance F hF β inferInstance inferInstance inferInstance hYloc hJ hFF K hKc hiso α hα
  exact (isKernelCokernelAnnihilatedByPower_iff_chartSections B S hS Y.1 Y.2 J K hK α hUa
    hUsurj).mpr hch

end ChartGlobal

/-- **Stacks 08BD.** Let `f : X ⟶ Y` be a representable proper morphism of Noetherian algebraic
spaces over `S`, let `𝓙, 𝓚 ⊆ 𝒪_Y` be quasi-coherent sheaves of ideals, and assume `f` is an
isomorphism over `Y ∖ V(𝓚)`.  Set `𝓘 = f⁻¹𝓙 𝒪_X`.  Let `(𝓖_n)` be an object of `Coh(Y, 𝓙)`,
`𝓕` a coherent `𝒪_X`-module and `β : (f^*𝓖_n) ≅ 𝓕^∧` an isomorphism in `Coh(X, 𝓘)`.  Then there
is a map `α : (𝓖_n) ⟶ (f_*𝓕)^∧` in `Coh(Y, 𝓙)` whose kernel and cokernel are annihilated by a
power of `𝓚` (`AlgebraicGeometry.Space.IsKernelCokernelAnnihilatedByPower`, the notion of
Stacks 08BA: one exponent `t > 0` with `𝓚 ^ t` killing every levelwise kernel and cokernel).

`α` is the map whose composite with the comparison `(f_*𝓕)^∧ ⟶ f_*(𝓕^∧)` is the system of
adjunction maps followed by `f_*β`; it exists because that comparison is an isomorphism on limits
(the theorem on formal functions, checked on affine charts), and the annihilation is the scheme
case Stacks 088B on one surjective affine chart of `Y`, spread over `Y` by quasi-coherence. -/
@[stacks 08BD "the full statement: for a representable proper morphism of Noetherian algebraic \
spaces which is an isomorphism over Y minus V(K), a map alpha from (G_n) to the completion of \
f_*F in Coh(Y, J) whose levelwise kernels and cokernels are all annihilated by one positive \
power of K"]
theorem exists_completionMap_kernel_cokernel_annihilated (hZ : B.Contains (⊤_ Scheme.{u}))
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f.hom)
    (hfp : IsProper B S hS f.hom) (hX : IsNoetherian B S hS hZ X.1)
    (hY : IsNoetherian B S hS hZ Y.1)
    (J K : (SheafOfModules.unit.{u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))).Submodule)
    (hJ : J.toSheafOfModules.IsQuasicoherentOnSite) (hK : K.toSheafOfModules.IsQuasicoherentOnSite)
    (hiso : IsIso ((idealComplementSubfunctor B S hS Y K).fromPreimage f.hom))
    (G : CoherentAdicSystems B S hS Y.1 Y.2 J) (F : Modules.{u, u} B S hS X.1 X.2)
    (hF : IsCoherent B S hS X.1 X.2 F) :
    letI : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
      ⟨hX.2.2⟩
    letI : Fact (HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
      ⟨hY.2.2⟩
    ∀ _β : G.obj ⋙ modulePullback B S hS f ≅
        ((completionFunctor B S hS X.1 X.2 (pullbackIdealSubsheaf B S hS f hf J)
          (isQuasicoherentOnSite_pullbackIdealSubsheaf B S hS f hf J hJ)).obj ⟨F, hF⟩).obj,
      ∃ α : G ⟶ (completionFunctor B S hS Y.1 Y.2 J hJ).obj
          ⟨(modulePushforward B S hS f).obj F,
            isCoherent_modulePushforward_of_isProper B S hS f hf hfp hY.2.2 F hF⟩,
        IsKernelCokernelAnnihilatedByPower B S hS Y.1 Y.2 K α.hom := by
  intro β
  have hXl : Fact (HasEtaleLocalProperty B S hS X.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hX.2.2⟩
  have hYl : Fact (HasEtaleLocalProperty B S hS Y.1
    (fun V : Scheme.{u} => IsLocallyNoetherian V)) := ⟨hY.2.2⟩
  have hpush := isCoherent_modulePushforward_of_isProper B S hS f hf hfp hY.2.2 F hF
  have hFF : IsCoherent B S hS Y.1 Y.2 ((baseChangeDirectImage B S hS f hf).obj F) :=
    isCoherent_of_iso B S hS Y.2 ((modulePushforwardChartIso B S hS f hf).app F) hpush
  obtain ⟨α', hα'⟩ := exists_comp_directImageCompletionComparison_eq B S hS f hf hfp J hJ
    (isQuasicoherentOnSite_pullbackIdealSubsheaf B S hS f hf J hJ) G F hF hFF β
  have hann := @exists_kernel_cokernel_annihilated_of_comp_eq B S hS X Y f hf hfp J hJ hXl hYl
    (isQuasicoherentOnSite_pullbackIdealSubsheaf B S hS f hf J hJ) G F hF hFF β hZ hY K hK hiso
    α' hα'
  let e : (completionFunctor B S hS Y.1 Y.2 J hJ).obj ⟨_, hFF⟩ ≅
      (completionFunctor B S hS Y.1 Y.2 J hJ).obj ⟨(modulePushforward B S hS f).obj F, hpush⟩ :=
    (completionFunctor B S hS Y.1 Y.2 J hJ).mapIso
      (ObjectProperty.isoMk _ ((modulePushforwardChartIso B S hS f hf).app F).symm)
  exact ⟨α' ≫ e.hom, (exists_pos_idealPowerMultiple_kernel_cokernel_comp_iso_iff B S hS K α'.hom
    ((ObjectProperty.ι _).mapIso e)).mpr hann⟩

end AlgebraicGeometry.Space
