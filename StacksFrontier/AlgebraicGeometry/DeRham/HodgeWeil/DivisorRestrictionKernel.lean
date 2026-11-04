module

public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeWeil.DivisorKernelWedge
public import StacksFrontier.AlgebraicGeometry.DeRham.LerayHirsch.DeRhamComparisonAdjoint
public import StacksFrontier.AlgebraicGeometry.DeRham.LogPoles.DivisorDeRhamPushforward
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SubmoduleRestrictScalars
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective

/-!
# The forms vanishing on a closed subscheme as a kernel

Let `f : X ⟶ S` be a morphism of schemes and `Y ⊆ X` the closed subscheme cut out by `I`, with
`i : Y ⟶ X`. The canonical map of Tag 07HX in degree `p`,
`Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S}`, through which the Hodge pullback along `i` is defined
(`Stacks.DeRhamBaseChange.formsPushforward`), is the restriction of forms
`AlgebraicGeometry.Scheme.Hom.formRestriction` on sections. It is therefore an epimorphism of
sheaves of `f⁻¹𝒪_S`-modules whose kernel is the sheaf `𝒦^p` of forms vanishing on `Y`:

`0 ⟶ 𝒦^p ⟶ Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S} ⟶ 0`

is a short exact sequence of sheaves of `f⁻¹𝒪_S`-modules.

## Main results

* `Stacks.HodgeWeil.formsPushforward_subschemeι_apply`: the canonical map is the restriction of
  forms on sections.
* `Stacks.HodgeWeil.kernelFormsShortComplex_shortExact`: the short exact sequence.

## References

* [Stacks Project, Tag 07HX](https://stacks.math.columbia.edu/tag/07HX)
* [Stacks Project, Section 0FM4](https://stacks.math.columbia.edu/tag/0FM4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom

universe u

namespace Stacks.HodgeWeil

variable {X S : Scheme.{u}} (f : X ⟶ S) (I : X.IdealSheafData)

/-- The commutative square `i ≫ f = (i ≫ f) ≫ 𝟙` of the inclusion `i : Y ⟶ X`. -/
theorem subschemeι_square : I.subschemeι ≫ f = (I.subschemeι ≫ f) ≫ 𝟙 S :=
  (Category.comp_id _).symm

/-- In abelian sheaves the canonical map is the restriction of forms. -/
private theorem toSheaf_map_formsPushforward_subschemeι (p : ℕ) :
    (_root_.SheafOfModules.toSheaf _).map (Stacks.DeRhamBaseChange.formsPushforward I.subschemeι
        (I.subschemeι ≫ f) f (𝟙 S) (subschemeι_square f I) p) =
      (_root_.SheafOfModules.toSheaf X.ringCatSheaf).map
        (formRestriction I.subschemeι f (p : ℤ)) := by
  have h1 := Stacks.DeRhamBaseChange.deRhamAbelianPushforwardMap_f I.subschemeι
    (I.subschemeι ≫ f) f (𝟙 S) (subschemeι_square f I) p
  have h2 := congrArg (fun φ => φ.f p) (toSheaf_divisorRestrictionBase_comp_divisorDeRhamAbIso f I)
  exact h1.symm.trans (h2.symm.trans (Category.comp_id _))

/-- **The canonical map `Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S}` is the restriction of forms**, on sections. -/
theorem formsPushforward_subschemeι_apply (p : ℕ) (U : (X.Opens)ᵒᵖ)
    (x : ((Scheme.Hom.deRhamComplex f).X p).val.obj U) :
    (Stacks.DeRhamBaseChange.formsPushforward I.subschemeι (I.subschemeι ≫ f) f (𝟙 S)
        (subschemeι_square f I) p).val.app U x =
      (formRestriction I.subschemeι f (p : ℤ)).val.app U x := by
  exact congrArg (fun φ => φ.hom.app U x) (toSheaf_map_formsPushforward_subschemeι f I p)

/-- The canonical map `Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S}` of sheaves of `f⁻¹𝒪_S`-modules. -/
abbrev formsRestrictionBase (p : ℕ) :
    (Scheme.Hom.deRhamComplex f).X p ⟶
      (StacksDraft.KFlat.modulePushforward (Stacks.DeRhamBaseChange.inverseImageBaseMap
        I.subschemeι (I.subschemeι ≫ f) f (𝟙 S) (subschemeι_square f I))).obj
        ((Scheme.Hom.deRhamComplex (I.subschemeι ≫ f)).X p) :=
  Stacks.DeRhamBaseChange.formsPushforward I.subschemeι (I.subschemeι ≫ f) f (𝟙 S)
    (subschemeι_square f I) p

/-- **In abelian sheaves the canonical map is the restriction of forms.** -/
theorem toSheaf_map_formsRestrictionBase (p : ℕ) :
    (_root_.SheafOfModules.toSheaf _).map (formsRestrictionBase f I p) =
      (_root_.SheafOfModules.toSheaf X.ringCatSheaf).map
        (formRestriction I.subschemeι f (p : ℤ)) := by
  exact toSheaf_map_formsPushforward_subschemeι f I p

/-- **The canonical map `Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S}` is an epimorphism** of sheaves of
`f⁻¹𝒪_S`-modules, the restriction of forms to a closed subscheme being one (Tag 08KS). -/
instance epi_formsRestrictionBase (p : ℕ) : Epi (formsRestrictionBase f I p) := by
  have : Epi (C := SheafOfModules.{u} X.ringCatSheaf)
      (formRestriction I.subschemeι f (p : ℤ)) := epi_formRestriction I.subschemeι f p
  have h : Epi ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).map
      (formRestriction I.subschemeι f (p : ℤ))) :=
    Stacks.SheafOfModules.EpiMono.epi_toSheaf_map (formRestriction I.subschemeι f (p : ℤ))
  rw [← toSheaf_map_formsRestrictionBase] at h
  exact (_root_.SheafOfModules.toSheaf _).epi_of_epi_map h

/-- The forms vanishing on `Y`, as a submodule of `Ω^p_{X/S}` read as a sheaf of
`f⁻¹𝒪_S`-modules. -/
abbrev kernelFormsSubmodule (p : ℕ) :
    (AlgebraicGeometry.SheafOfModules.deRhamTerm (formsAlgebras f) p).Submodule :=
  _root_.SheafOfModules.Submodule.restrictScalars (baseRingHom f) (formRestrictionKernel f I p)

/-- `𝒦^p` in the category of sheaves of modules over `(X, f⁻¹𝒪_S)` in which the direct image
along `i` lands. -/
abbrev kernelFormsSheaf (p : ℕ) :
    _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (AlgebraicGeometry.SheafedSpace.sheaf (Stacks.DeRhamDirectImage.inverseImageBase f))) :=
  kernelFormsBase f I p

/-- `Ω^p_{X/S}` in that category. -/
abbrev formsSheaf (p : ℕ) :
    _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (AlgebraicGeometry.SheafedSpace.sheaf (Stacks.DeRhamDirectImage.inverseImageBase f))) :=
  (Scheme.Hom.deRhamComplex f).X p

/-- The inclusion `𝒦^p ⟶ Ω^p_{X/S}`, in that category. -/
abbrev kernelFormsInclusion (p : ℕ) : kernelFormsSheaf f I p ⟶ formsSheaf f p :=
  kernelFormsBaseInclusion f I p

/-- The canonical map `Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S}`, in that category. -/
abbrev formsRestriction (p : ℕ) :
    formsSheaf f p ⟶
      (StacksDraft.KFlat.modulePushforward (Stacks.DeRhamBaseChange.inverseImageBaseMap
        I.subschemeι (I.subschemeι ≫ f) f (𝟙 S) (subschemeι_square f I))).obj
        ((Scheme.Hom.deRhamComplex (I.subschemeι ≫ f)).X p) :=
  formsRestrictionBase f I p

/-- The composite `𝒦^p ⟶ Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S}` is zero. -/
theorem kernelFormsBaseInclusion_comp_formsRestrictionBase (p : ℕ) :
    kernelFormsInclusion f I p ≫ formsRestriction f I p = 0 := by
  ext U x
  exact (formsPushforward_subschemeι_apply f I p U _).trans (formRestriction_kernelFormsBase x)

/-- The inclusion `𝒦^p ⟶ Ω^p_{X/S}` is a monomorphism. -/
instance mono_kernelFormsInclusion (p : ℕ) : Mono (kernelFormsInclusion f I p) :=
  (inferInstance : Mono (kernelFormsSubmodule f I p).ι)

/-- **`𝒦^p` is the kernel of `Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S}`.** -/
def kernelFormsIsLimit (p : ℕ) :
    IsLimit (KernelFork.ofι (kernelFormsInclusion f I p)
      (kernelFormsBaseInclusion_comp_formsRestrictionBase f I p)) :=
  KernelFork.IsLimit.ofι' _ _ fun {P} k hk =>
    ⟨(kernelFormsSubmodule f I p).factorThru k fun U x =>
      (mem_formRestrictionKernel f I p U _).2
        ((formsPushforward_subschemeι_apply f I p U _).symm.trans
          (congrArg (fun φ : P ⟶ _ => φ.val.app U x) hk)),
      (kernelFormsSubmodule f I p).factorThru_ι k _⟩

/-- The short complex `𝒦^p ⟶ Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S}`. -/
abbrev kernelFormsShortComplex (p : ℕ) :
    ShortComplex (_root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (AlgebraicGeometry.SheafedSpace.sheaf (Stacks.DeRhamDirectImage.inverseImageBase f)))) :=
  ShortComplex.mk (kernelFormsInclusion f I p) (formsRestriction f I p)
    (kernelFormsBaseInclusion_comp_formsRestrictionBase f I p)

/-- **`0 ⟶ 𝒦^p ⟶ Ω^p_{X/S} ⟶ i_*Ω^p_{Y/S} ⟶ 0` is short exact.** -/
theorem kernelFormsShortComplex_shortExact (p : ℕ) : (kernelFormsShortComplex f I p).ShortExact :=
  have : Epi (formsRestriction f I p) := epi_formsRestrictionBase f I p
  { exact := ShortComplex.exact_of_f_is_kernel _ (kernelFormsIsLimit f I p) }

end Stacks.HodgeWeil

end
