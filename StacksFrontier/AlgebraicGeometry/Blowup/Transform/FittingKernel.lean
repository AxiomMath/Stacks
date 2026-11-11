module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationCokernel
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.FittingFlatten
public import StacksFrontier.AlgebraicGeometry.Descent.Modules.FpqcFinitePresentation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.FinitePresentationExtension

/-!
# The kernel of the strict transform of a module along the blowup of its Fitting ideal

Let `ℱ` be a finitely presented module on a scheme `X` which is finite locally free of constant
rank `r` on an open `U`, and let `b : X' ⟶ X` be the blowup of `X` in the `r`-th Fitting ideal of
`ℱ`. This file studies the kernel `𝒦` of the canonical surjection from `b^*ℱ` onto the strict
transform `ℱ'` of `ℱ`: it vanishes over `U`, and, when `U` is scheme-theoretically dense, it is
finitely presented. Together with
`AlgebraicGeometry.isAdmissibleBlowup_fittingIdeal` and
`AlgebraicGeometry.isFiniteLocallyFreeOfRank_strictTransform_of_dense` this completes Stacks tag
0ESN.

## Main definitions

* `AlgebraicGeometry.strictTransformKernel`: the kernel `𝒦`.

## Main results

* `AlgebraicGeometry.strictTransformKernel_restrict_isZero`: `𝒦` vanishes over `U`, because the
  surjection onto the strict transform is an isomorphism away from the exceptional divisor and
  the preimage of `U` misses that divisor.
* `AlgebraicGeometry.exists_isSplitEpi_restrictFunctor_map`: **an epimorphism of modules on a
  scheme whose target is finite locally free splits after restriction to a neighbourhood of any
  given point.** This is the content of the two items below, and it is also what
  `AlgebraicGeometry.hasTorAmplitude_single_kernel_of_isFiniteLocallyFree` of
  `StacksFrontier/AlgebraicGeometry/Blowup/Transform/KernelTorAmplitude.lean` consumes.
* `AlgebraicGeometry.kernelι_comp_kernelRetraction`: the kernel of a split epimorphism is a
  retract of its source, by the complementary idempotent
  `AlgebraicGeometry.kernelRetraction`.
* `AlgebraicGeometry.isFinitePresentation_kernel_of_isFiniteLocallyFree`: the kernel of an
  epimorphism from a finitely presented module onto a finite locally free one is finitely
  presented. This is the general statement behind the next item.
* `AlgebraicGeometry.strictTransformKernel_isFinitePresentation`: `𝒦` is finitely presented.

## Implementation notes

The vanishing half needs no new input: the quotient map onto the strict transform is an
isomorphism over the complement of the preimage of the exceptional divisor
(`Stacks.StrictTransform.isIso_restrictFunctor_map_π`), the preimage of `U` is contained in that
complement because the support of the Fitting ideal misses `U`
(`AlgebraicGeometry.disjoint_support_fittingIdeal`), and a morphism which is a monomorphism over
an open has vanishing kernel there.

The finite-presentation half is the general statement about kernels, whose content is that an
epimorphism onto a finite locally free module splits locally on the base. The basis sections of
the target over a trivializing open lift, finitely many at a time, over a smaller open — an
epimorphism of sheaves of modules is locally surjective, and finitely many opens can be
intersected — and the restricted basis is again a basis. Over such an open the kernel is the
cokernel of the splitting section, hence finitely presented by Stacks tag 0H96; and finite
presentation is local on the base.

The local-splitting construction is carried out over an arbitrary site with pullbacks rather than
for schemes only, so that the comparison isomorphisms between a free module and its restriction
stay opaque; spelling them out for the scheme site would force the definitional unfolding of the
restriction functor on the unit object.

## References

* [Stacks Project, Tag 0ESN](https://stacks.math.columbia.edu/tag/0ESN)
* [Stacks Project, Tag 01BQ](https://stacks.math.columbia.edu/tag/01BQ)
* [Stacks Project, Tag 0H96](https://stacks.math.columbia.edu/tag/0H96)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u t

namespace AlgebraicGeometry

/-- The kernel of the canonical surjection from the pullback of a module to its strict transform
along the blowup of the `r`-th Fitting ideal of the module. -/
noncomputable abbrev strictTransformKernel {X : Scheme.{u}} (F : X.Modules) (r : ℕ) :
    (Stacks.StrictTransform.baseChange (𝟙 X)
      (blowUpToBase (fittingIdeal F (r : ℤ)))).Modules :=
  kernel (Stacks.StrictTransform.π (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ)))
    (exceptionalIdeal (fittingIdeal F (r : ℤ))) F)

/-- The preimage under the first projection of an open avoiding the support of an ideal sheaf `I`
is contained in the complement of the preimage of the exceptional divisor of the blowup of `I`.
-/
private lemma preimage_le_exceptionalComplement {X : Scheme.{u}} (I : X.IdealSheafData)
    (U : X.Opens) (hdisj : Disjoint (U : Set X) (I.support : Set X)) :
    (Limits.pullback.fst (𝟙 X) (blowUpToBase I)) ⁻¹ᵁ U ≤
      Stacks.StrictTransform.exceptionalComplement (𝟙 X) (blowUpToBase I)
        (exceptionalIdeal I) := by
  intro y hy
  have hfst : (Limits.pullback.fst (𝟙 X) (blowUpToBase I)).base y ∈ (U : Set X) := hy
  have hcond : (Limits.pullback.fst (𝟙 X) (blowUpToBase I)).base y =
      (blowUpToBase I).base ((Limits.pullback.snd (𝟙 X) (blowUpToBase I)).base y) := by
    simpa using congrArg
      (fun f : Stacks.StrictTransform.baseChange (𝟙 X) (blowUpToBase I) ⟶ X ↦ f.base y)
      (Limits.pullback.condition (f := 𝟙 X) (g := blowUpToBase I))
  have hmem : (Limits.pullback.snd (𝟙 X) (blowUpToBase I)).base y ∉
      ((exceptionalIdeal I).support : Set (blowUp I)) := by
    rw [Scheme.IdealSheafData.support_comap]
    exact fun h ↦ Set.disjoint_left.mp hdisj hfst (hcond ▸ h)
  exact hmem

/-- **Stacks Project, Tag 0ESN, part (3).** The kernel of the canonical surjection onto the
strict transform vanishes over the open on which the module is finite locally free of rank `r`:
away from the exceptional divisor the surjection is an isomorphism. -/
@[stacks 0ESN "kernel"]
theorem strictTransformKernel_restrict_isZero {X : Scheme.{u}} (F : X.Modules)
    [F.IsFinitePresentation] (U : X.Opens) (r : ℕ)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r) :
    IsZero ((Scheme.Modules.pullback
      ((Limits.pullback.fst (𝟙 X) (blowUpToBase (fittingIdeal F (r : ℤ)))) ⁻¹ᵁ U).ι).obj
        (strictTransformKernel F r)) := by
  have : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  have : F.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F
  set I : X.IdealSheafData := fittingIdeal F (r : ℤ)
  set V : (Stacks.StrictTransform.baseChange (𝟙 X) (blowUpToBase I)).Opens :=
    (Limits.pullback.fst (𝟙 X) (blowUpToBase I)) ⁻¹ᵁ U
  have hcompl : IsIso ((Scheme.Modules.restrictFunctor
      (Stacks.StrictTransform.exceptionalComplement (𝟙 X) (blowUpToBase I)
        (exceptionalIdeal I)).ι).map
      (Stacks.StrictTransform.π (𝟙 X) (blowUpToBase I) (exceptionalIdeal I) F)) :=
    Stacks.StrictTransform.isIso_restrictFunctor_map_π (𝟙 X) (blowUpToBase I)
      (exceptionalIdeal I) F
  have hiso : IsIso ((Scheme.Modules.restrictFunctor V.ι).map
      (Stacks.StrictTransform.π (𝟙 X) (blowUpToBase I) (exceptionalIdeal I) F)) :=
    Scheme.Modules.isIso_restrictFunctor_map_of_le
      (preimage_le_exceptionalComplement I U
        (disjoint_support_fittingIdeal F U r hrank)) _
  have hzero : IsZero ((Scheme.Modules.restrictFunctor V.ι).obj
      (strictTransformKernel F r)) :=
    (isZero_kernel_of_mono ((Scheme.Modules.restrictFunctor V.ι).map
        (Stacks.StrictTransform.π (𝟙 X) (blowUpToBase I) (exceptionalIdeal I) F))).of_iso
      (PreservesKernel.iso (Scheme.Modules.restrictFunctor V.ι) _)
  exact hzero.of_iso ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app _).symm

/-! ### Kernels of epimorphisms onto finite locally free modules

The second half of tag 0ESN (3) is the general statement that the kernel of an epimorphism from
a finitely presented module onto a finite locally free one is finitely presented: locally the
epimorphism splits, so there the kernel is the cokernel of the splitting section, and the
cokernel of a finite-type module into a finitely presented one is finitely presented.
-/

section Kernel

open Opposite

/-! #### General categorical input -/

/-- A natural isomorphism of functors carries split epimorphisms to split epimorphisms. -/
theorem isSplitEpi_map_of_iso_functor {D E : Type*} [Category D] [Category E] {G H : D ⥤ E}
    (η : G ≅ H) {A B : D} (g : A ⟶ B) [IsSplitEpi (G.map g)] : IsSplitEpi (H.map g) :=
  IsSplitEpi.mk' ⟨η.inv.app B ≫ section_ (G.map g) ≫ η.hom.app A, by
    rw [Category.assoc, Category.assoc, ← η.hom.naturality g,
      ← Category.assoc (section_ (G.map g)), IsSplitEpi.id, Category.id_comp,
      η.inv_hom_id_app]⟩

/-- A natural isomorphism of functors carries split epimorphisms to split epimorphisms. -/
private alias isSplitEpi_map_of_natIso := isSplitEpi_map_of_iso_functor

/-- The complementary idempotent `1 - g ∘ s` of a split epimorphism `g` with section `s`, read
as a morphism into `ker g`. It retracts the kernel inclusion
(`AlgebraicGeometry.kernelι_comp_kernelRetraction`), so the kernel of a split epimorphism is a
direct summand of its source. -/
noncomputable def kernelRetraction {D : Type*} [Category D] [Abelian D] {A B : D} (g : A ⟶ B)
    [IsSplitEpi g] : A ⟶ kernel g :=
  kernel.lift g (𝟙 A - g ≫ section_ g) (by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, IsSplitEpi.id g,
      Category.comp_id, sub_self])

/-- `AlgebraicGeometry.kernelRetraction` followed by the kernel inclusion is the complementary
idempotent. -/
theorem kernelRetraction_comp_kernelι {D : Type*} [Category D] [Abelian D] {A B : D} (g : A ⟶ B)
    [IsSplitEpi g] : kernelRetraction g ≫ kernel.ι g = 𝟙 A - g ≫ section_ g :=
  kernel.lift_ι _ _ _

/-- **The kernel of a split epimorphism is a retract of its source.** The complementary
idempotent `1 - g ∘ s` is the identity on the kernel, because `g` vanishes there. -/
theorem kernelι_comp_kernelRetraction {D : Type*} [Category D] [Abelian D] {A B : D} (g : A ⟶ B)
    [IsSplitEpi g] : kernel.ι g ≫ kernelRetraction g = 𝟙 (kernel g) := by
  refine (cancel_mono (kernel.ι g)).1 ?_
  rw [Category.assoc, kernelRetraction_comp_kernelι, Category.id_comp, Preadditive.comp_sub,
    ← Category.assoc, kernel.condition, zero_comp, sub_zero, Category.comp_id]

/-- **An object isomorphic to the kernel of a split epimorphism is a retract of its source.**
This is `AlgebraicGeometry.kernelι_comp_kernelRetraction` transported along an isomorphism, which
is the form an exact functor applied to a kernel produces. -/
theorem kernelι_comp_kernelRetraction_of_iso {D : Type*} [Category D] [Abelian D] {A B K : D}
    (g : A ⟶ B) [IsSplitEpi g] (e : K ≅ kernel g) :
    (e.hom ≫ kernel.ι g) ≫ kernelRetraction g ≫ e.inv = 𝟙 K := by
  rw [Category.assoc, ← Category.assoc (kernel.ι g), kernelι_comp_kernelRetraction,
    Category.id_comp, e.hom_inv_id]

/-- For a split epimorphism the kernel is the cokernel of any of its sections: the
complementary idempotent `1 - g ∘ s` factors through the kernel by a morphism which the kernel
inclusion splits, and it kills the section. -/
private noncomputable def cokernelSectionIsoKernel {D : Type*} [Category D] [Abelian D]
    {A B : D} (g : A ⟶ B) [IsSplitEpi g] : cokernel (section_ g) ≅ kernel g := by
  have hsg : section_ g ≫ kernelRetraction g = 0 := by
    refine (cancel_mono (kernel.ι g)).1 ?_
    rw [Category.assoc, kernelRetraction_comp_kernelι, zero_comp, Preadditive.comp_sub,
      Category.comp_id, ← Category.assoc, IsSplitEpi.id, Category.id_comp, sub_self]
  refine ⟨cokernel.desc _ _ hsg, kernel.ι g ≫ cokernel.π (section_ g), ?_, ?_⟩
  · refine (cancel_epi (cokernel.π (section_ g))).1 ?_
    rw [Category.comp_id, ← Category.assoc, cokernel.π_desc, ← Category.assoc,
      kernelRetraction_comp_kernelι, Preadditive.sub_comp, Category.id_comp, Category.assoc,
      cokernel.condition, comp_zero, sub_zero]
  · rw [Category.assoc, cokernel.π_desc, kernelι_comp_kernelRetraction]

/-! #### Lifting a morphism out of a free module, over a site -/

section Site

variable {C : Type u} [Category.{v} C] [Limits.HasPullbacks C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [∀ Z : C, HasSheafify (J.over Z) AddCommGrpCat.{t}]
  [∀ Z : C, (J.over Z).WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- The comparison isomorphism identifying the unit object over an object of the site with its
image under restriction to a smaller object. It is the identity, but writing it down with this
type keeps the terms built from it type-correct without unfolding the restriction functor. -/
private def overMapUnitIso {W V : C} (g : V ⟶ W) :
    SheafOfModules.unit (R.over V) ≅
      (SheafOfModules.overMap R g).obj (SheafOfModules.unit (R.over W)) :=
  Iso.refl _

omit [Limits.HasPullbacks C] in
/-- The sections named by a morphism out of a free module transported along a functor: they are
the transports of the morphisms out of the unit object which name the original sections. -/
private lemma freeHomEquiv_mapFreeIso_comp {W V : C} {N : _root_.SheafOfModules.{t} R}
    {ι : Type t}
    (F : _root_.SheafOfModules.{t} (R.over W) ⥤ _root_.SheafOfModules.{t} (R.over V))
    (η : SheafOfModules.unit (R.over V) ≅ F.obj (SheafOfModules.unit (R.over W)))
    (e : SheafOfModules.free ι ⟶ N.over W) (φ : F.obj (N.over W) ⟶ N.over V) (j : ι)
    [PreservesColimitsOfShape (Discrete ι) F] :
    (N.over V).freeHomEquiv ((SheafOfModules.mapFreeIso F ι η).hom ≫ F.map e ≫ φ) j =
      (N.over V).unitHomEquiv (η.hom ≫ F.map (SheafOfModules.ιFree j ≫ e) ≫ φ) := by
  change (N.over V).unitHomEquiv
    (SheafOfModules.ιFree j ≫ (SheafOfModules.mapFreeIso F ι η).hom ≫ F.map e ≫ φ) = _
  rw [← Category.assoc, SheafOfModules.ιFree_mapFreeIso_hom]
  simp only [Category.assoc, Functor.map_comp]

omit [Limits.HasPullbacks C] in
/-- A morphism out of a free module lifts through a morphism `f` as soon as the sections it
names lift: the lifted sections assemble into a morphism out of the free module, and the two
composites agree because a section over a slice object is determined by its value over the
terminal object. -/
private lemma exists_lift_free_over {M N : _root_.SheafOfModules.{t} R} (f : M ⟶ N) {V : C}
    {ι : Type t} (α : SheafOfModules.free ι ⟶ N.over V) (m : ι → M.val.obj (op V))
    (hm : ∀ j, f.val.app (op V) (m j) =
      ((N.over V).freeHomEquiv α j).val (op (Over.mk (𝟙 V)))) :
    ∃ β : SheafOfModules.free ι ⟶ M.over V, β ≫ f.over V = α := by
  refine ⟨(M.over V).freeHomEquiv.symm fun j ↦
    PresheafOfModules.sectionsMk (fun Z ↦ M.val.map Z.unop.hom.op (m j)) (by
      intro Z Z' k
      change M.val.map k.unop.left.op (M.val.map Z.unop.hom.op (m j)) = _
      rw [← M.val.map_comp_apply, ← op_comp, Over.w]), ?_⟩
  rw [SheafOfModules.freeHomEquiv_symm_comp]
  refine (N.over V).freeHomEquiv.symm_apply_eq.2 (funext fun j ↦ ?_)
  refine PresheafOfModules.sections_ext _ _ fun Z ↦ ?_
  change f.val.app (op Z.unop.left) (M.val.map Z.unop.hom.op (m j)) = _
  rw [PresheafOfModules.naturality_apply, hm j]
  exact ((N.over V).freeHomEquiv α j).property
    (Over.homMk Z.unop.hom (by simp) : Z.unop ⟶ Over.mk (𝟙 V)).op

/-- The restriction to a smaller object of the site of a morphism out of a free module. -/
private noncomputable def restrictFreeHom {W V : C} (g : V ⟶ W)
    {N : _root_.SheafOfModules.{t} R} {ι : Type t}
    (e : SheafOfModules.free ι ⟶ N.over W) :
    SheafOfModules.free ι ⟶ N.over V :=
  (SheafOfModules.mapFreeIso (SheafOfModules.overMap R g) ι (overMapUnitIso g)).hom ≫
    (SheafOfModules.overMap R g).map e ≫ ((SheafOfModules.overFunctorMap R g).app N).hom

/-- `AlgebraicGeometry.restrictFreeHom` written out. -/
private lemma restrictFreeHom_eq {W V : C} (g : V ⟶ W)
    {N : _root_.SheafOfModules.{t} R} {ι : Type t}
    (e : SheafOfModules.free ι ⟶ N.over W) :
    restrictFreeHom g e =
      (SheafOfModules.mapFreeIso (SheafOfModules.overMap R g) ι (overMapUnitIso g)).hom ≫
        (SheafOfModules.overMap R g).map e ≫
        ((SheafOfModules.overFunctorMap R g).app N).hom := rfl

/-- Restricting a free basis to a smaller object of the site keeps it a free basis. -/
private instance isIso_restrictFreeHom {W V : C} (g : V ⟶ W)
    {N : _root_.SheafOfModules.{t} R} {ι : Type t}
    (e : SheafOfModules.free ι ⟶ N.over W) [IsIso e] :
    IsIso (restrictFreeHom g e) := by
  rw [restrictFreeHom_eq]
  infer_instance

/-- The sections named by `AlgebraicGeometry.restrictFreeHom` are the restrictions of the
sections named by the original morphism. -/
private lemma restrictFreeHom_val {W V : C} (g : V ⟶ W)
    {N : _root_.SheafOfModules.{t} R} {ι : Type t}
    (e : SheafOfModules.free ι ⟶ N.over W) (j : ι) (Z : (Over V)ᵒᵖ) :
    ((N.over V).freeHomEquiv (restrictFreeHom g e) j).val Z =
      ((N.over W).freeHomEquiv e j).val (op (Over.mk (Z.unop.hom ≫ g))) := by
  rw [restrictFreeHom_eq, freeHomEquiv_mapFreeIso_comp]
  rfl

/-- A morphism whose target has a free basis over an object of the site splits over a smaller
object as soon as the basis sections lift there: the restricted basis is again a basis, and the
lifted sections provide a morphism inverting it. -/
lemma isSplitEpi_over_of_lift {M N : _root_.SheafOfModules.{t} R} (f : M ⟶ N)
    {W V : C} (g : V ⟶ W) {ι : Type t}
    (e : SheafOfModules.free ι ⟶ N.over W) [IsIso e] (m : ι → M.val.obj (op V))
    (hm : ∀ j, f.val.app (op V) (m j) =
      N.val.map g.op (((N.over W).freeHomEquiv e j).val (op (Over.mk (𝟙 W))))) :
    IsSplitEpi (f.over V) := by
  obtain ⟨β, hβ⟩ : ∃ β : SheafOfModules.free ι ⟶ M.over V,
      β ≫ f.over V = restrictFreeHom g e := by
    refine exists_lift_free_over f _ m fun j ↦ ?_
    rw [hm j, restrictFreeHom_val]
    exact ((N.over W).freeHomEquiv e j).property
      (Over.homMk g (by simp) :
        Over.mk ((Over.mk (𝟙 V)).hom ≫ g) ⟶ Over.mk (𝟙 W)).op
  exact IsSplitEpi.mk' ⟨inv (restrictFreeHom g e) ≫ β, by
    rw [Category.assoc, hβ, IsIso.inv_hom_id]⟩

end Site

/-! #### The local splitting on a scheme -/

variable {Y : Scheme.{u}} {M N : Y.Modules}

/-- A single section of the target of an epimorphism of modules on a scheme lifts over some
open neighbourhood of any point of the open it lives on. -/
private lemma exists_le_lift_section (f : M ⟶ N) [Epi f] (W : Y.Opens)
    (t : N.val.obj (op W)) (y : Y) (hy : y ∈ W) :
    ∃ (V : Y.Opens) (hVW : V ≤ W), y ∈ V ∧ ∃ s : M.val.obj (op V),
      f.val.app (op V) s = N.val.map (homOfLE hVW).op t := by
  obtain ⟨S, hS, hlift⟩ := @Stacks.SheafOfModules.EpiMono.exists_covering_of_epi
    _ _ _ Y.ringCatSheaf _ _ M N f ‹_› W t
  obtain ⟨V, i, hi, hyV⟩ := (Opens.mem_grothendieckTopology _).1 hS y hy
  obtain ⟨s, hsf⟩ := hlift i hi
  exact ⟨V, leOfHom i, hyV, s, hsf⟩

/-- Finitely many sections of the target of an epimorphism of modules on a scheme lift over one
common open neighbourhood of any point of the open they live on: the finitely many
neighbourhoods produced section by section are intersected. -/
private lemma exists_le_lift_sections (f : M ⟶ N) [Epi f] {ι : Type u} [Finite ι] (W : Y.Opens)
    (t : ι → N.val.obj (op W)) (y : Y) (hy : y ∈ W) :
    ∃ (V : Y.Opens) (hVW : V ≤ W), y ∈ V ∧ ∃ s : ι → M.val.obj (op V),
      ∀ i, f.val.app (op V) (s i) = N.val.map (homOfLE hVW).op (t i) := by
  classical
  choose V hVW hyV s hs using fun i ↦ exists_le_lift_section f W (t i) y hy
  have hZV (i : ι) : W ⊓ ⨅ j, V j ≤ V i := inf_le_right.trans (iInf_le _ i)
  refine ⟨W ⊓ ⨅ j, V j, inf_le_left, ⟨hy, ?_⟩,
    fun i ↦ M.val.map (homOfLE (hZV i)).op (s i), fun i ↦ ?_⟩
  · change y ∈ ((⨅ j, V j : Y.Opens) : Set Y)
    rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
    exact hyV
  · refine Eq.trans (PresheafOfModules.naturality_apply f.val (homOfLE (hZV i)).op (s i)) ?_
    rw [hs i]
    exact (N.val.map_comp_apply (homOfLE (hVW i)).op (homOfLE (hZV i)).op (t i)).symm

/-- An epimorphism of modules on a scheme splits over a neighbourhood of any point of an open
over which the target is finite free: the finitely many basis sections lift over a common
smaller neighbourhood, over which the restricted basis is still a basis. -/
private lemma exists_isSplitEpi_over (f : M ⟶ N) [Epi f] {W : Y.Opens} {ι : Type u} [Finite ι]
    (e : SheafOfModules.free ι ⟶ N.over W) [IsIso e] (y : Y) (hy : y ∈ W) :
    ∃ V : Y.Opens, y ∈ V ∧ IsSplitEpi (f.over V) := by
  obtain ⟨V, hVW, hyV, m, hm⟩ := exists_le_lift_sections f W
    (fun j ↦ ((N.over W).freeHomEquiv e j).val (op (Over.mk (𝟙 W)))) y hy
  exact ⟨V, hyV, isSplitEpi_over_of_lift f (homOfLE hVW) e m hm⟩

/-- An epimorphism of modules on a scheme whose target is finite locally free splits after
restriction to a neighbourhood of any given point. -/
theorem exists_isSplitEpi_restrictFunctor_map (f : M ⟶ N) [Epi f]
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] (y : Y) :
    ∃ V : Y.Opens, y ∈ V ∧ IsSplitEpi ((Scheme.Modules.restrictFunctor V.ι).map f) := by
  obtain ⟨q, hfree, hfin⟩ :=
    SheafOfModules.IsFiniteLocallyFree.exists_isFiniteLocallyFreeData (M := N)
  obtain ⟨i, hi⟩ := ((_root_.Opens.coversTop_iff Y q.X).mp q.coversTop).exists_mem y
  have : IsIso (q.generators i).π := hfree.isIso i
  have : Finite (q.generators i).I := (hfin.isFiniteType i).finite
  obtain ⟨V, hyV, hsplit⟩ := exists_isSplitEpi_over f (q.generators i).π y hi
  refine ⟨V, hyV, ?_⟩
  have := hsplit
  exact @isSplitEpi_map_of_natIso _ _ _ _ _ _ (Scheme.Modules.overFunctorEquiv V) _ _ f
    (inferInstanceAs (IsSplitEpi ((Scheme.Modules.overEquiv V).functor.map (f.over V))))

/-! #### Finite presentation of the kernel -/

/-- The restriction of the kernel of a morphism to an open over which the morphism splits is
finitely presented: there the kernel is the cokernel of the section, whose source is of finite
type and whose target is finitely presented, so Stacks tag 0H96 applies. -/
private lemma isFinitePresentation_restrict_kernel_of_isSplitEpi (f : M ⟶ N)
    [M.IsFinitePresentation] [SheafOfModules.IsFiniteType.{u, u, u} N] (V : Y.Opens)
    (hsplit : IsSplitEpi ((Scheme.Modules.restrictFunctor V.ι).map f)) :
    ((kernel f).restrict V.ι).IsFinitePresentation := by
  have := hsplit
  have hM : (M.restrict V.ι).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation V.toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app M).symm
      (@Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _
        V.ι.toLRSHom.toShHom M ‹_›)
  have hNp : SheafOfModules.IsFiniteType.{u, u, u} ((Scheme.Modules.pullback V.ι).obj N) :=
    @SheafOfModules.pullback_isFiniteType _ _ V.ι.toLRSHom.toShHom N ‹_›
  have hN : SheafOfModules.IsFiniteType.{u, u, u} (N.restrict V.ι) :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u}
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).app N).symm
  have hck :
      (cokernel (section_ ((Scheme.Modules.restrictFunctor V.ι).map f))).IsFinitePresentation :=
    Stacks.SheafOfModules.isFinitePresentation_cokernel _
  exact (SheafOfModules.isFinitePresentation V.toScheme.ringCatSheaf).prop_of_iso
    (cokernelSectionIsoKernel ((Scheme.Modules.restrictFunctor V.ι).map f) ≪≫
      (PreservesKernel.iso (Scheme.Modules.restrictFunctor V.ι) f).symm) hck

/-- **The kernel of an epimorphism from a finitely presented module onto a finite locally free
module is finitely presented.** Locally on the base the epimorphism splits, so there the kernel
is the cokernel of the splitting section, which has a finite-type source and a finitely
presented target; and finite presentation is local on the base. -/
theorem isFinitePresentation_kernel_of_isFiniteLocallyFree (f : M ⟶ N) [Epi f]
    [M.IsFinitePresentation] [M.IsQuasicoherent]
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} N] : (kernel f).IsFinitePresentation := by
  classical
  have hb : Stacks.FiniteLocallyFree.IsFiniteLocallyFree (R := Y.ringCatSheaf) N :=
    ⟨SheafOfModules.IsFiniteLocallyFree.exists_isFiniteLocallyFreeData⟩
  have hN : SheafOfModules.IsFiniteType.{u, u, u} N :=
    Stacks.FiniteLocallyFree.isFiniteType (h := hb) N
  have hNq : N.IsQuasicoherent := by
    obtain ⟨q, hq, -⟩ :=
      SheafOfModules.IsFiniteLocallyFree.exists_isFiniteLocallyFreeData (M := N)
    have := hq
    exact q.quasiCoherentData.isQuasicoherent
  have : (kernel f).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel f
  choose V hyV hsplit using fun y : Y ↦ exists_isSplitEpi_restrictFunctor_map f y
  refine isFinitePresentation_of_isOpenCover (kernel f) V ?_
    fun y ↦ isFinitePresentation_restrict_kernel_of_isSplitEpi f (V y) (hsplit y)
  exact eq_top_iff.mpr fun y _ ↦ TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyV y⟩

end Kernel

/-- **Stacks Project, Tag 0ESN, part (3).** The kernel of the canonical surjection onto the
strict transform is finitely presented: the strict transform is finite locally free, so the
surjection splits locally, and the pullback of a finitely presented module is finitely
presented (Stacks tag 01BQ). -/
@[stacks 0ESN "kernel"]
theorem strictTransformKernel_isFinitePresentation {X : Scheme.{u}} (F : X.Modules)
    [F.IsFinitePresentation] (U : X.Opens)
    (hU : Scheme.Opens.IsSchemeTheoreticallyDense U) (r : ℕ)
    (hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback U.ι).obj F) r) :
    (strictTransformKernel F r).IsFinitePresentation := by
  have : F.IsFiniteType := SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F
  have : F.IsQuasicoherent := SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F
  set I : X.IdealSheafData := fittingIdeal F (r : ℤ)
  set p : Stacks.StrictTransform.baseChange (𝟙 X) (blowUpToBase I) ⟶ X :=
    Limits.pullback.fst (𝟙 X) (blowUpToBase I)
  have hM : ((Scheme.Modules.pullback p).obj F).IsFinitePresentation :=
    @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _ p.toLRSHom.toShHom F ‹_›
  have hMq : ((Scheme.Modules.pullback p).obj F).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ p.toLRSHom.toShHom F ‹_›
  have hrk : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.StrictTransform.sheaf (𝟙 X) (blowUpToBase I) (exceptionalIdeal I) F) r :=
    isFiniteLocallyFreeOfRank_strictTransform_of_dense F U r hU hrank
  have hflf : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (Stacks.StrictTransform.sheaf (𝟙 X) (blowUpToBase I) (exceptionalIdeal I) F) :=
    @SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree.{u, u, u}
      _ _ _ _ _ _ _ r hrk
  exact isFinitePresentation_kernel_of_isFiniteLocallyFree
    (Stacks.StrictTransform.π (𝟙 X) (blowUpToBase I) (exceptionalIdeal I) F)

end AlgebraicGeometry

end
