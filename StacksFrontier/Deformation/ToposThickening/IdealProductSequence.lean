module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import StacksFrontier.Deformation.ToposThickening.PushforwardComparison.ModuleMapLifts

/-!
# The ideal-product sequence of a first order thickening of ringed topoi

Let `i : (Sh(C), O) ⟶ (Sh(D), O')` be a first order thickening of ringed topoi with square-zero
ideal `I`, and let `G'` be a sheaf of `O'`-modules. The unit of the adjunction `i^* ⊣ i_*` at
`G'` is the canonical map `G' ⟶ i_*i^*G'`, and this file shows that

```
  0 ⟶ I·G' ⟶ G' ⟶ i_*i^*G' ⟶ 0
```

is a short exact sequence of `O'`-modules: the first map is the inclusion of the sheaf submodule
`I·G'`, which is exactly the kernel of the unit, and the unit is surjective.

## Main definitions

* `Deformation.ToposThickening.idealProductShortComplex`: the displayed sequence, as a short
  complex.

## Main results

* `Deformation.ToposThickening.essImage_pushforwardModules_of_mono`: the essential image of the
  direct image of modules along a closed immersion of ringed topoi is closed under subobjects.
* `Deformation.ToposThickening.epi_unit_of_essImage_mono_stable`: if the right adjoint of an
  adjunction is fully faithful and its essential image is closed under subobjects, every
  component of the unit is an epimorphism.
* `Deformation.ToposThickening.epi_pullbackAdjPushforward_unit_app`: the unit
  `G' ⟶ i_*i^*G'` is an epimorphism.
* `Deformation.ToposThickening.idealProductShortComplex_shortExact`: the sequence is short
  exact.
* `Deformation.ToposThickening.nonempty_moduleMapLift_iff_exists_factorization`: a map of
  pullbacks lifts exactly when its adjoint transpose factors through the unit. This is the form
  in which the sequence computes the lifts of Stacks 08MP.

## Implementation notes

Surjectivity of the unit is the only part that is not already on main. It is the standard
reflective-subcategory argument: the direct image of modules along a first order thickening is
fully faithful (Stacks 08M3), so the adjunction is reflective; the image of the unit at `G'` is
a subobject of an object of the essential image, hence — the essential image being closed under
subobjects, which is the annihilation criterion of Stacks 08M3 again — itself in the essential
image; and at an object of the essential image the unit is invertible, so the inclusion of the
image splits and is therefore an isomorphism.

Closure of the essential image under subobjects is read off the sectionwise criterion
`AlgebraicGeometry.ClosedRingedImmersion.pushforwardModules_essImage_iff_ideal_annihilates`: a
monomorphism of sheaves of modules is sectionwise injective, so a section annihilated after the
inclusion is annihilated before it.

The two remaining exactness facts are on main and are not reproved here: the composite vanishes
by `Deformation.ToposThickening.idealProductSubmodule_unit_comp_zero`, and every map killed by
the unit factors through `I·G'` by
`Deformation.ToposThickening.idealProductSubmodule_factors_through`, which together say that
`I·G' ⟶ G'` is a kernel of the unit.

The source and target ringed topoi share their section universe, as they must:
`Deformation.ToposThickening.FirstOrderThickening.closedRingedImmersion` lands in
`AlgebraicGeometry.ClosedRingedImmersion`, which carries one section universe for both.

## References

* [Stacks Project, Tag 08MP](https://stacks.math.columbia.edu/tag/08MP)
* [Stacks Project, Tag 08M3](https://stacks.math.columbia.edu/tag/08M3)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom ClosedRingedImmersion)

universe v u v' u' w

namespace Deformation.ToposThickening

/-- **The unit of a reflective adjunction whose essential image is closed under subobjects is
epimorphic.** The image of the unit at `M` is a subobject of `R(L M)`, hence lies in the
essential image of `R`; the unit at an object of the essential image is invertible, so the
inclusion of the image into `R(L M)` admits a retraction and is an isomorphism; and the unit
factors through its image. -/
theorem epi_unit_of_essImage_mono_stable {A : Type*} [Category A] [Abelian A] {B : Type*}
    [Category B] {L : A ⥤ B} {R : B ⥤ A} (adj : L ⊣ R) [R.Full] [R.Faithful]
    (hR : ∀ {M N : A} (f : M ⟶ N), Mono f → R.essImage N → R.essImage M) (M : A) :
    Epi (adj.unit.app M) := by
  let : Reflective R := { L := L, adj := adj }
  let η := adj.unit.app M
  have hIm : R.essImage (image η) :=
    hR (image.ι η) inferInstance (R.obj_mem_essImage _)
  let e := unitCompPartialBijective M hIm
  let r : R.obj (L.obj M) ⟶ image η := e (factorThruImage η)
  have hr : η ≫ r = factorThruImage η :=
    (unitCompPartialBijective_symm_apply M hIm r).symm.trans (e.symm_apply_apply _)
  have key : η ≫ r ≫ image.ι η = η ≫ 𝟙 (R.obj (L.obj M)) :=
    ((Category.assoc η r (image.ι η)).symm.trans
        ((congrArg (fun z ↦ z ≫ image.ι η) hr).trans (image.fac η))).trans
      (Category.comp_id η).symm
  have hri : r ≫ image.ι η = 𝟙 (R.obj (L.obj M)) :=
    (unitCompPartialBijective M (R.obj_mem_essImage (L.obj M))).symm.injective
      ((unitCompPartialBijective_symm_apply M _ _).trans
        (key.trans (unitCompPartialBijective_symm_apply M _ _).symm))
  have : IsIso (image.ι η) :=
    ⟨⟨r, (cancel_mono (image.ι η)).mp
        ((Category.assoc (image.ι η) r (image.ι η)).trans
          ((congrArg (fun z ↦ image.ι η ≫ z) hri).trans
            ((Category.comp_id (image.ι η)).trans (Category.id_comp _).symm))), hri⟩⟩
  have hfac : Epi (factorThruImage η ≫ image.ι η) := inferInstance
  exact Eq.mp (congrArg (fun g ↦ Epi g) (image.fac η)) hfac

section Thickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {i : RingedToposHom X Y}

/-- **The essential image of the direct image of modules along a first order thickening is
closed under subobjects.** By the criterion of Stacks 08M3 an `O'`-module is a direct image
exactly when the kernel ideal of the structure map annihilates it sectionwise, and a
monomorphism of sheaves of modules is injective on sections.

Sectionwise injectivity goes through the evaluation functor, whose
`CategoryTheory.Limits.PreservesLimitsOfShape` instance is named here rather than left to
instance search: the search does not reach `SheafOfModules.evaluationPreservesLimitsOfShape`
through the ring sheaf of `AlgebraicGeometry.ClosedRingedImmersion.targetRingSheaf`, although
the instance applies to it. -/
theorem essImage_pushforwardModules_of_mono (S : ClosedRingedImmersion.{v, u, v', u', w})
    {M N : SheafOfModules.{w} S.targetRingSheaf} (f : M ⟶ N) (_hf : Mono f)
    (hN : S.hom.pushforwardModules.essImage N) : S.hom.pushforwardModules.essImage M := by
  rw [ClosedRingedImmersion.pushforwardModules_essImage_iff_ideal_annihilates S] at hN ⊢
  intro U a ha m
  have : Mono f := _hf
  have : PreservesLimitsOfShape WalkingCospan
      (SheafOfModules.evaluation.{w} S.targetRingSheaf U) :=
    SheafOfModules.evaluationPreservesLimitsOfShape _ _ _
  have hmono : Mono (f.val.app U) := (SheafOfModules.evaluation _ U).map_mono f
  apply (ModuleCat.mono_iff_injective (f.val.app U)).mp inferInstance
  simpa only [map_smul, map_zero] using hN U a ha (f.val.app U m)

/-- **The unit `G' ⟶ i_*i^*G'` of a first order thickening is surjective.** The direct image of
modules is fully faithful (Stacks 08M3) and its essential image is closed under subobjects, so
`epi_unit_of_essImage_mono_stable` applies. -/
theorem epi_pullbackAdjPushforward_unit_app (hi : FirstOrderThickening i)
    (G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    Epi (i.pullbackAdjPushforwardModulesViaComparison.unit.app G') := by
  have ff := (ClosedRingedImmersion.pushforwardModules_fullyFaithful
    hi.closedRingedImmersion).some
  have : i.pushforwardModules.Full := ff.full
  have : i.pushforwardModules.Faithful := ff.faithful
  exact epi_unit_of_essImage_mono_stable i.pullbackAdjPushforwardModulesViaComparison
    (fun f hf hN ↦
      essImage_pushforwardModules_of_mono hi.closedRingedImmersion f hf hN) G'

/-- The sequence `0 ⟶ I·G' ⟶ G' ⟶ i_*i^*G' ⟶ 0` of `O'`-modules attached to a first order
thickening and a sheaf of `O'`-modules `G'`: the inclusion of the ideal product followed by the
unit of the adjunction. -/
noncomputable def idealProductShortComplex (hi : FirstOrderThickening i)
    (G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    ShortComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  ShortComplex.mk (idealProductSubmodule hi G').ι
    (i.pullbackAdjPushforwardModulesViaComparison.unit.app G')
    (idealProductSubmodule_unit_comp_zero hi G')

/-- **The ideal-product sequence is short exact.** The inclusion of a sheaf submodule is a
monomorphism, the unit is an epimorphism by `epi_pullbackAdjPushforward_unit_app`, and `I·G'` is
a kernel of the unit because every map killed by the unit factors through it
(`Deformation.ToposThickening.idealProductSubmodule_factors_through`). -/
theorem idealProductShortComplex_shortExact (hi : FirstOrderThickening i)
    (G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    (idealProductShortComplex hi G').ShortExact := by
  classical
  have hepi : Epi (idealProductShortComplex hi G').g :=
    epi_pullbackAdjPushforward_unit_app hi G'
  have hmono : Mono (idealProductShortComplex hi G').f :=
    inferInstanceAs (Mono (idealProductSubmodule hi G').ι)
  have hex : (idealProductShortComplex hi G').Exact := by
    apply ShortComplex.exact_of_f_is_kernel
    refine KernelFork.IsLimit.ofι' _ _ ?_
    intro M f hf
    exact ⟨(idealProductSubmodule_factors_through hi M G' f hf).choose,
      (idealProductSubmodule_factors_through hi M G' f hf).choose_spec.symm⟩
  exact { exact := hex, mono_f := hmono, epi_g := hepi }

omit [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- **A map of pullbacks lifts exactly when its adjoint transpose factors through the unit.**
A lift of `φ` is a map `ψ : F' ⟶ G'` with `i^*ψ = φ`, and `i^*ψ` corresponds under the
adjunction to `ψ` followed by the unit. -/
theorem nonempty_moduleMapLift_iff_exists_factorization
    (F' G' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    (φ : (i.toRingedToposModulesHom.pullbackModules).obj F' ⟶
      (i.toRingedToposModulesHom.pullbackModules).obj G') :
    Nonempty (ModuleMapLift F' G' φ) ↔
      ∃ ψ : F' ⟶ G',
        ψ ≫ i.pullbackAdjPushforwardModulesViaComparison.unit.app G' =
          i.pullbackAdjPushforwardModulesViaComparison.homEquiv F' _ φ := by
  let L := i.toRingedToposModulesHom.pullbackModules
  let adj := i.pullbackAdjPushforwardModulesViaComparison
  have hunit (ψ : F' ⟶ G') :
      adj.homEquiv F' (L.obj G') (L.map ψ) = ψ ≫ adj.unit.app G' := by
    rw [Adjunction.homEquiv_unit]
    exact (adj.unit.naturality ψ).symm
  constructor
  · rintro ⟨⟨ψ, hψ⟩⟩
    exact ⟨ψ, by rw [← hunit ψ, hψ]⟩
  · rintro ⟨ψ, hψ⟩
    exact ⟨⟨ψ, (adj.homEquiv F' (L.obj G')).injective ((hunit ψ).trans hψ)⟩⟩

end Thickening

end Deformation.ToposThickening

end
