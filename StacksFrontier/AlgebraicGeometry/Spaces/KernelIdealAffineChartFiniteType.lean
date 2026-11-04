module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionFinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeOnSiteAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.KernelIdealEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactKernelQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSchemeStructureSharp
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite type of the kernel ideal sheaf, read on the affine étale charts

Let `f : X ⟶ Y` be a representable quasi-compact morphism of algebraic spaces over a scheme
`S` contained in a big fppf site `B`.  Its kernel ideal sheaf
`𝓘 = Ker(𝒪_Y ⟶ f_*𝒪_X)` of Stacks 03G8 is of finite type on the small étale site of `Y`
exactly when, for every affine étale chart `C` of `Y`, the ideal cut out in the functions on
`C` by the cartesian projection `X ×_Y C ⟶ C` is finitely generated.

Both halves are already available.  Finite type on the site is finiteness of the sections over
the affine charts, which is
`AlgebraicGeometry.Space.isFiniteTypeOnSite_iff_forall_affine_moduleFinite`; the kernel ideal
sheaf of a quasi-compact morphism is cartesian on affine charts, which is
`AlgebraicGeometry.Space.isCartesianOnAffineCharts_kernelIdealSheaf`; and its sections over a
chart are the kernel of pullback of regular functions along the cartesian projection, which is
Stacks 03G8, part (2).

## Main results

* `AlgebraicGeometry.Space.ker_structureSharp_app_eq_ker_appTop`: the sections of the kernel
  ideal sheaf over an étale chart `C` are the kernel of pullback of regular functions along the
  cartesian projection `X ×_Y C ⟶ C`.
* `AlgebraicGeometry.Space.isFiniteTypeOnSite_kernelIdealSheaf_iff_forall_affine_fg` and
  `AlgebraicGeometry.Space.isFiniteTypeOnSite_kernelIdealSheaf_iff_forall_affine_fg_ker`: finite
  type of the kernel ideal sheaf is finite generation of those ideals over the affine charts.
* `AlgebraicGeometry.Space.isFiniteTypeOnSite_kernelIdealSheaf_of_isFinitePresentation`: a
  closed immersion of finite presentation has kernel ideal sheaf of finite type.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : AlgebraicSpaces B S hS}

/-- **The sections of the kernel ideal sheaf over an étale chart are the kernel of pullback of
regular functions along the cartesian projection.**  The structure map of Stacks 03G8, read
through the identification of the sections of `f_*𝒪_X` over the chart with the functions on
`X ×_Y C`, is that pullback (Stacks 03G8, part (2)), and the identification is an isomorphism
of sheaves of rings, hence injective on sections, so the two kernels agree. -/
theorem ker_structureSharp_app_eq_ker_appTop (f : X ⟶ Y)
    (hf : yoneda.relativelyRepresentable f.hom) (C : SmallEtale B S hS Y.1) :
    RingHom.ker ((structureSharp B S hS f).hom.app (op C)).hom =
      RingHom.ker ((BigFppfOver.toScheme B S hS).map (hf.snd C.1.hom)).appTop.hom := by
  let := isContinuous_smallBaseChange B S hS f hf
  have hinj : Function.Injective
      ((chartProjectionSharpDirectImage B S hS f hf).hom.app (op C)).hom :=
    injective_ringSheafIso_app B S hS Y
      (asIso (chartProjectionSharpDirectImage B S hS f hf)) (op C)
  have happ : ∀ x, ((chartProjectionSharpDirectImage B S hS f hf).hom.app (op C)).hom
        (((structureSharp B S hS f).hom.app (op C)).hom x)
      = ((BigFppfOver.toScheme B S hS).map (hf.snd C.1.hom)).appTop.hom x := fun x =>
    congrArg
      (fun t : structureRingSheaf B S hS Y ⟶
          ((smallBaseChange B S hS f hf).sheafPushforwardContinuous RingCat.{u}
            (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS X.1)).obj
            (structureRingSheaf B S hS X) => (t.hom.app (op C)).hom x)
      (structureSharp_comp_chartProjectionSharpDirectImage B S hS f hf)
  refine Ideal.ext fun a =>
    ⟨fun ha => RingHom.mem_ker.2 ?_, fun ha => RingHom.mem_ker.2 ?_⟩
  · refine (happ a).symm.trans ?_
    rw [RingHom.mem_ker.1 ha]
    exact map_zero _
  · exact (map_eq_zero_iff _ hinj).1 ((happ a).trans (RingHom.mem_ker.1 ha))

/-- Finiteness of the ideal of sections of the kernel ideal sheaf over a chart, as a module
over the functions on that chart, is finite generation of that ideal. -/
theorem moduleFinite_ker_structureSharp_iff_fg (f : X ⟶ Y) (C : SmallEtale B S hS Y.1) :
    Module.Finite ((structureRingSheaf B S hS Y).obj.obj (op C))
        (RingHom.ker ((structureSharp B S hS f).hom.app (op C)).hom) ↔
      (RingHom.ker ((structureSharp B S hS f).hom.app (op C)).hom).FG :=
  Module.Finite.iff_fg

/-- **Finite type of the kernel ideal sheaf is finite generation of the ideals of sections over
the affine étale charts.** -/
theorem isFiniteTypeOnSite_kernelIdealSheaf_iff_forall_affine_fg (f : X ⟶ Y)
    (hqc : IsQuasiCompact B S hS f.hom) :
    SheafOfModules.IsFiniteTypeOnSite (kernelIdealSheaf B S hS f).toSheafOfModules ↔
      ∀ C : (smallEtaleRingedSite B S hS Y.1 Y.2).C,
        IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj C) →
          (RingHom.ker ((structureSharp B S hS f).hom.app (op C)).hom).FG :=
  Iff.trans (isFiniteTypeOnSite_iff_forall_affine_moduleFinite B S hS Y.1 Y.2 _
      (isCartesianOnAffineCharts_kernelIdealSheaf B S hS f hqc))
    (forall_congr' fun C => imp_congr_right fun _ =>
      moduleFinite_ker_structureSharp_iff_fg B S hS f C)

/-- **Finite type of the kernel ideal sheaf of a representable quasi-compact morphism is finite
generation, over every affine étale chart `C` of the target, of the ideal cut out by the
cartesian projection `X ×_Y C ⟶ C`.** -/
theorem isFiniteTypeOnSite_kernelIdealSheaf_iff_forall_affine_fg_ker (f : X ⟶ Y)
    (hqc : IsQuasiCompact B S hS f.hom) (hf : yoneda.relativelyRepresentable f.hom) :
    SheafOfModules.IsFiniteTypeOnSite (kernelIdealSheaf B S hS f).toSheafOfModules ↔
      ∀ C : (smallEtaleRingedSite B S hS Y.1 Y.2).C,
        IsAffine ((SmallEtale.toOver B S hS Y.1 ⋙ BigFppfOver.toScheme B S hS).obj C) →
          (RingHom.ker
            ((BigFppfOver.toScheme B S hS).map (hf.snd C.1.hom)).appTop.hom).FG :=
  Iff.trans (isFiniteTypeOnSite_kernelIdealSheaf_iff_forall_affine_fg B S hS f hqc)
    (forall_congr' fun C => imp_congr_right fun _ =>
      iff_of_eq (congrArg Submodule.FG (ker_structureSharp_app_eq_ker_appTop B S hS f hf C)))

/-! ### The ideal sheaf of a closed immersion of finite presentation -/

/-- **A closed immersion of finite presentation has kernel ideal sheaf of finite type.**  This
is one implication of Stacks 084Q.  Local finite presentation of `i` gives local finite
presentation of the cartesian projection `Z ×_X C ⟶ C` at every affine étale chart `C`, the
case of schemes (Stacks 01TV) makes the ideal of that closed immersion finitely generated over
every affine open of `C` — in particular over `C` itself, which is affine — and that ideal is
the ideal of sections of the kernel ideal sheaf over `C`. -/
@[ega "IV 8.6.1" "Necessary direction"]
theorem isFiniteTypeOnSite_kernelIdealSheaf_of_isFinitePresentation (i : X ⟶ Y)
    (hi : IsClosedImmersion B S hS i.hom) (h : IsFinitePresentation B S hS i.hom) :
    SheafOfModules.IsFiniteTypeOnSite (kernelIdealSheaf B S hS i).toSheafOfModules := by
  refine (isFiniteTypeOnSite_kernelIdealSheaf_iff_forall_affine_fg_ker B S hS i
    (isQuasiCompact_of_isClosedImmersion' B S hS hi) hi.rep).2 fun C hC => ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj C.1.left) := hC
  have hqEtale : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hi.rep.fst C.1.hom) :=
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (hi.rep.isPullback C.1.hom).flip C.property
  have hq : _root_.AlgebraicGeometry.LocallyOfFinitePresentation
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd C.1.hom)) :=
    h.1 _ C.1.left (hi.rep.fst C.1.hom) C.1.hom (hi.rep.snd C.1.hom) hqEtale C.property
      ((hi.rep.isPullback C.1.hom).w).symm
  have hclosed : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hi.rep.snd C.1.hom)) := hi.property_snd C.1.hom
  have hfg := (_root_.AlgebraicGeometry.locallyOfFinitePresentation_iff_fg_ker _).1 hq
    ⟨⊤, isAffineOpen_top _⟩
  rwa [Scheme.Hom.ker_apply] at hfg

end AlgebraicGeometry.Space

end
