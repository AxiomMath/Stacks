module

public import Mathlib.Algebra.Category.FGModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Colimit.Finiteness
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.CategoryTheory.Presentable.ColimitPresentation

/-!
# Left exactness from the restriction to finite modules

A functor on modules over a Noetherian ring that preserves filtered colimits is left
exact as soon as its restriction to the finite modules is. The ring universes need not
agree with the module universe: every module is the directed union of its finitely
generated submodules, and over a Noetherian ring a kernel between finite modules is
again finite, so both halves of the criterion stay inside the finite modules.

## Main results

* `ModuleCat.preservesFiniteLimits_of_finiteModuleRestriction` — the criterion.

## Implementation notes

The reduction is to kernels: `Functor.preservesFiniteLimits_of_preservesKernels` turns
preservation of every `parallelPair f 0` into preservation of all finite limits. The
kernel of a map of finite modules over a Noetherian ring is finite, which is what lets
the hypothesis on the restriction be applied there.
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u v w

namespace ModuleCat

variable {A : Type u} [CommRing A] {B : Type w} [Ring B]

private abbrev FiniteSubmoduleIndex (M : ModuleCat.{v} A) :=
  {P : Submodule A M // P.FG}

private instance (M : ModuleCat.{v} A) : IsFiltered (FiniteSubmoduleIndex M) := by
  have : Nonempty (FiniteSubmoduleIndex M) := ⟨⟨⊥, Submodule.fg_bot⟩⟩
  infer_instance

private def finiteSubmoduleDiagram (M : ModuleCat.{v} A) :
    FiniteSubmoduleIndex M ⥤ ModuleCat.{v} A where
  obj P := ModuleCat.of A P.1
  map f := ModuleCat.ofHom (Submodule.inclusion f.down.down)
  map_id _ := rfl
  map_comp _ _ := rfl

private def finiteSubmoduleCocone (M : ModuleCat.{v} A) :
    Cocone (finiteSubmoduleDiagram M) where
  pt := M
  ι := {
    app := fun P => ModuleCat.ofHom P.1.subtype
    naturality _ _ _ := rfl }

private noncomputable def finiteSubmoduleIsColimit (M : ModuleCat.{v} A) :
    IsColimit (finiteSubmoduleCocone M) := by
  classical
  let I := FiniteSubmoduleIndex M
  let G : I → Type v := fun P => P.1
  let f := Module.fgSystem A M
  let p : ColimitPresentation I (ModuleCat.of A (Module.DirectLimit G f)) := {
    diag := ModuleCat.directLimitDiagram G f
    ι := (ModuleCat.directLimitCocone G f).ι
    isColimit := ModuleCat.directLimitIsColimit G f }
  let q := p.ofIso (Module.fgSystem.equiv A M).toModuleIso
  refine IsColimit.ofIsoColimit q.isColimit (Cocone.ext (Iso.refl M) ?_)
  intro P
  change ModuleCat.ofHom
      ((Module.fgSystem.equiv A M).toLinearMap.comp (Module.DirectLimit.of A I G f P)) = _
  rw [Module.fgSystem.equiv_comp_of]
  rfl

variable (E : ModuleCat.{v} A ⥤ ModuleCat.{v} B)
  [PreservesFilteredColimitsOfSize.{v, v} E]

private lemma exists_finiteSubmodule_rep (M : ModuleCat.{v} A) (x : E.obj M) :
    ∃ (P : FiniteSubmoduleIndex M) (y : E.obj (ModuleCat.of A P.1)),
      E.map (ModuleCat.ofHom P.1.subtype) y = x :=
  Types.jointly_surjective_of_isColimit (isColimitOfPreserves (forget AddCommGrpCat.{v})
    (isColimitOfPreserves (forget₂ (ModuleCat.{v} B) AddCommGrpCat.{v})
      (isColimitOfPreserves E (finiteSubmoduleIsColimit M)))) x

variable [IsNoetherianRing A]
  [PreservesFiniteLimits (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A) ⋙ E)]

omit [PreservesFilteredColimitsOfSize.{v, v} E] in
private lemma map_injective_of_finite {X Y : ModuleCat.{v} A}
    [Module.Finite A X] [Module.Finite A Y]
    (f : X ⟶ Y) (hf : Function.Injective f) : Function.Injective (E.map f) := by
  let X' : FGModuleCat.{v} A := ⟨X, ‹Module.Finite A X›⟩
  let Y' : FGModuleCat.{v} A := ⟨Y, ‹Module.Finite A Y›⟩
  let f' : X' ⟶ Y' := ObjectProperty.homMk f
  let I := forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)
  have : Mono f' := I.mono_of_mono_map (f := f') ((ModuleCat.mono_iff_injective f).2 hf)
  exact (ModuleCat.mono_iff_injective ((I ⋙ E).map f')).1 inferInstance

private lemma map_subtype_injective (M : ModuleCat.{v} A) (P : FiniteSubmoduleIndex M) :
    Function.Injective (E.map (ModuleCat.ofHom P.1.subtype)) := by
  intro x y hxy
  have hc := isColimitOfPreserves (forget AddCommGrpCat.{v})
    (isColimitOfPreserves (forget₂ (ModuleCat.{v} B) AddCommGrpCat.{v})
      (isColimitOfPreserves E (finiteSubmoduleIsColimit M)))
  obtain ⟨Q, f, hf⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc x y).1 hxy
  have : Module.Finite A P.1 := Module.Finite.of_fg P.2
  have : Module.Finite A Q.1 := Module.Finite.of_fg Q.2
  exact map_injective_of_finite E (ModuleCat.ofHom (Submodule.inclusion f.down.down))
    (Submodule.inclusion_injective f.down.down) hf

private lemma map_rangeRestrict_eq_zero {X Y : ModuleCat.{v} A} (f : X ⟶ Y)
    (P : FiniteSubmoduleIndex X) (z : E.obj (ModuleCat.of A P.1))
    (hz : E.map f (E.map (ModuleCat.ofHom P.1.subtype) z) = 0) :
    E.map (ModuleCat.ofHom (f.hom.comp P.1.subtype).rangeRestrict) z = 0 := by
  have : Module.Finite A P.1 := Module.Finite.of_fg P.2
  let g := f.hom.comp P.1.subtype
  let Q : FiniteSubmoduleIndex Y := ⟨g.range, Submodule.fg_range g⟩
  let g' : ModuleCat.of A P.1 ⟶ ModuleCat.of A Q.1 := ModuleCat.ofHom g.rangeRestrict
  have hg : g' ≫ ModuleCat.ofHom Q.1.subtype = ModuleCat.ofHom P.1.subtype ≫ f := rfl
  apply map_subtype_injective E Y Q
  rw [map_zero]
  show (E.map g' ≫ E.map (ModuleCat.ofHom Q.1.subtype)) z = 0
  rw [← E.map_comp, hg, E.map_comp]
  exact hz

private lemma map_injective {X Y : ModuleCat.{v} A}
    (f : X ⟶ Y) (hf : Function.Injective f) : Function.Injective (E.map f) := by
  apply (injective_iff_map_eq_zero (E.map f).hom).mpr
  intro x hx
  obtain ⟨P, z, rfl⟩ := exists_finiteSubmodule_rep E X x
  have : Module.Finite A P.1 := Module.Finite.of_fg P.2
  let g := f.hom.comp P.1.subtype
  let Q : FiniteSubmoduleIndex Y := ⟨g.range, Submodule.fg_range g⟩
  have : Module.Finite A Q.1 := Module.Finite.of_fg Q.2
  let g' : ModuleCat.of A P.1 ⟶ ModuleCat.of A Q.1 := ModuleCat.ofHom g.rangeRestrict
  have hz : z = 0 := by
    apply map_injective_of_finite E g' (fun a b hab =>
      Subtype.ext (hf (congrArg Subtype.val hab)))
    rw [map_zero]
    exact map_rangeRestrict_eq_zero E f P z hx
  simp [hz]

omit [PreservesFilteredColimitsOfSize.{v, v} E] in
private lemma preservesZeroMorphisms_of_finiteModuleRestriction :
    E.PreservesZeroMorphisms := by
  let I := forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)
  have : HasZeroObject (FGModuleCat.{v} A) := hasZeroObject_of_hasTerminal_object
  have : Subsingleton (0 : ModuleCat.{v} A) := ModuleCat.subsingleton_of_isZero (isZero_zero _)
  let Z : FGModuleCat.{v} A := ⟨0, show Module.Finite A (0 : ModuleCat.{v} A) from inferInstance⟩
  have hZ : IsZero Z := by
    rw [IsZero.iff_id_eq_zero]
    apply I.map_injective
    exact (isZero_zero (ModuleCat.{v} A)).eq_of_src _ _
  have hEZ : IsZero (E.obj (0 : ModuleCat.{v} A)) := (I ⋙ E).map_isZero hZ
  exact Functor.preservesZeroMorphisms_of_map_zero_object hEZ.isoZero

attribute [local instance] preservesZeroMorphisms_of_finiteModuleRestriction

omit [PreservesFilteredColimitsOfSize.{v, v} E] in
private noncomputable def finiteKernelMapIsLimit {X Y : ModuleCat.{v} A}
    [Module.Finite A X] [Module.Finite A Y] (f : X ⟶ Y) :
    IsLimit ((ModuleCat.kernelCone f).map E) := by
  let I := forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)
  have : HasZeroObject (FGModuleCat.{v} A) := hasZeroObject_of_hasTerminal_object
  let X' : FGModuleCat.{v} A := ⟨X, ‹Module.Finite A X›⟩
  let Y' : FGModuleCat.{v} A := ⟨Y, ‹Module.Finite A Y›⟩
  let K' : FGModuleCat.{v} A := ⟨ModuleCat.of A f.hom.ker,
    show Module.Finite A f.hom.ker from inferInstance⟩
  let f' : X' ⟶ Y' := ObjectProperty.homMk f
  let i' : K' ⟶ X' := ObjectProperty.homMk (ModuleCat.ofHom f.hom.ker.subtype)
  have hi : i' ≫ f' = 0 := by
    apply I.map_injective
    ext x
    exact x.property
  let c : KernelFork f' := KernelFork.ofι i' hi
  have hc : IsLimit c := isLimitOfReflects I
    ((c.isLimitMapConeEquiv I).symm (ModuleCat.kernelIsLimit f))
  exact c.mapIsLimit hc (I ⋙ E)

omit [PreservesFilteredColimitsOfSize.{v, v} E] in
private lemma exists_preimage_of_finite_kernel {X Y : ModuleCat.{v} A}
    [Module.Finite A X] [Module.Finite A Y] (f : X ⟶ Y)
    (y : E.obj X) (hy : E.map f y = 0) :
    ∃ z : E.obj (ModuleCat.of A f.hom.ker),
      E.map (ModuleCat.ofHom f.hom.ker.subtype) z = y := by
  let h := finiteKernelMapIsLimit E f
  let e := h.conePointUniqueUpToIso (ModuleCat.kernelIsLimit (E.map f))
  refine ⟨e.inv ⟨y, hy⟩, ?_⟩
  have he := h.conePointUniqueUpToIso_inv_comp
    (ModuleCat.kernelIsLimit (E.map f)) WalkingParallelPair.zero
  exact congrArg (fun k => (k : ModuleCat.of B (E.map f).hom.ker ⟶ E.obj X) ⟨y, hy⟩) he

private lemma exists_map_ker_subtype_eq_of_map_eq_zero {X Y : ModuleCat.{v} A} (f : X ⟶ Y)
    (y : E.obj X) (hy : E.map f y = 0) :
    ∃ t, E.map (ModuleCat.ofHom f.hom.ker.subtype) t = y := by
  obtain ⟨P, z, rfl⟩ := exists_finiteSubmodule_rep E X y
  have : Module.Finite A P.1 := Module.Finite.of_fg P.2
  let g := f.hom.comp P.1.subtype
  let Q : FiniteSubmoduleIndex Y := ⟨g.range, Submodule.fg_range g⟩
  have : Module.Finite A Q.1 := Module.Finite.of_fg Q.2
  let g' : ModuleCat.of A P.1 ⟶ ModuleCat.of A Q.1 := ModuleCat.ofHom g.rangeRestrict
  obtain ⟨t, ht⟩ :=
    exists_preimage_of_finite_kernel E g' z (map_rangeRestrict_eq_zero E f P z hy)
  let k : ModuleCat.of A g'.hom.ker ⟶ ModuleCat.of A f.hom.ker :=
    ModuleCat.ofHom ((P.1.subtype.comp g'.hom.ker.subtype).codRestrict f.hom.ker
      fun x => congrArg Subtype.val x.property)
  have hk : k ≫ ModuleCat.ofHom f.hom.ker.subtype =
      ModuleCat.ofHom g'.hom.ker.subtype ≫ ModuleCat.ofHom P.1.subtype := rfl
  refine ⟨E.map k t, ?_⟩
  show (E.map k ≫ E.map (ModuleCat.ofHom f.hom.ker.subtype)) t = _
  rw [← E.map_comp, hk, E.map_comp]
  show E.map (ModuleCat.ofHom P.1.subtype)
    (E.map (ModuleCat.ofHom g'.hom.ker.subtype) t) = _
  rw [ht]

private lemma preservesKernel_of_finiteModuleRestriction {X Y : ModuleCat.{v} A}
    (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) E := by
  let i : ModuleCat.of A f.hom.ker ⟶ X := ModuleCat.ofHom f.hom.ker.subtype
  have hi : i ≫ f = 0 := by
    ext x
    exact x.property
  have hEi : E.map i ≫ E.map f = 0 := by rw [← E.map_comp, hi, E.map_zero]
  have hex : Function.Exact (E.map i).hom (E.map f).hom := fun y =>
    ⟨exists_map_ker_subtype_eq_of_map_eq_zero E f y, by
      rintro ⟨x, rfl⟩
      exact congrArg (fun k : E.obj (ModuleCat.of A f.hom.ker) ⟶ E.obj Y => k x) hEi⟩
  exact preservesLimit_of_preserves_limit_cone (ModuleCat.kernelIsLimit f)
    (((ModuleCat.kernelCone f).isLimitMapConeEquiv E).symm
      (ModuleCat.isLimitKernelFork (E.map i) (E.map f) hex
        (map_injective E i Subtype.val_injective)))

/-- A filtered-colimit-preserving functor on modules over a Noetherian ring preserves
finite limits if its restriction to finite modules does. The ring universes are independent
of the common module universe. -/
theorem preservesFiniteLimits_of_finiteModuleRestriction : PreservesFiniteLimits E := by
  have : ∀ {X Y : ModuleCat.{v} A} (f : X ⟶ Y), PreservesLimit (parallelPair f 0) E :=
    preservesKernel_of_finiteModuleRestriction E
  exact Functor.preservesFiniteLimits_of_preservesKernels E

end ModuleCat
