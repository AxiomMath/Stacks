module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PseudoTorsors
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology.AbelianTorsor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology.FiberTorsor

/-!
# The pushout extension of a torsor

For a torsor `F` under an abelian sheaf `H`, the sheafified augmentation sequence of the free
abelian presheaf on `F` is short exact; pushing it out along the difference map of `F` gives an
extension of the constant sheaf of integers by `H`.  This file constructs that extension,
identifies its extension class with the boundary of the constant section one, and defines the
resulting class of `F` together with the canonical generator map from `F` into the extension.

## Main definitions

* `Stacks.Cohomology.Torsors.torsorPushoutComplex` is the pushout extension of a torsor.
* `Stacks.Cohomology.Torsors.torsorPushoutClass` is the class of a torsor in first cohomology.
* `Stacks.Cohomology.Torsors.torsorPushoutGenerator` sends a section of the torsor to its
  generator in the middle term of the extension.

## Main results

* `Stacks.Cohomology.Torsors.torsorPushoutComplex_shortExact`: the pushout extension is short
  exact.
* `Stacks.Cohomology.Torsors.torsorPushout_extClass_eq_boundary`: its extension class is the
  boundary of the constant section one.
-/

@[expose] public noncomputable section

open CategoryTheory

universe w t v u

namespace Stacks.Cohomology.Torsors

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

variable [HasSheafify J AddCommGrpCat.{t}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{t})]

/-- The augmentation sequence before sheafification. -/
public noncomputable def freeAbelianPresheafAugmentationComplex
    (P : Cᵒᵖ ⥤ Type t) : ShortComplex (Cᵒᵖ ⥤ AddCommGrpCat.{t}) where
  X₁ := freeAbelianPresheafAugmentationKernel P
  X₂ := freeAbelianPresheaf P
  X₃ := (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ))
  f := Limits.kernel.ι (freeAbelianPresheafAugmentation P)
  g := freeAbelianPresheafAugmentation P
  zero := Limits.kernel.condition _

public lemma freeAbelianPresheafAugmentationComplex_exact
    (P : Cᵒᵖ ⥤ Type t) :
    (freeAbelianPresheafAugmentationComplex P).Exact :=
  ShortComplex.exact_of_f_is_kernel _
    (Limits.kernelIsKernel (freeAbelianPresheafAugmentation P))

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- Sheafifying the free abelian augmentation sequence of a torsor yields a
short exact sequence. -/
public lemma freeAbelianSheafAugmentationComplex_shortExact
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) :
    ((freeAbelianPresheafAugmentationComplex F.1.presheaf).map
      (presheafToSheaf J AddCommGrpCat)).ShortExact := by
  let S := freeAbelianPresheafAugmentationComplex F.1.presheaf
  have : Mono S.f := by
    change Mono (Limits.kernel.ι (freeAbelianPresheafAugmentation F.1.presheaf))
    infer_instance
  let : Presheaf.IsLocallySurjective J
      (freeAbelianPresheafAugmentation F.1.presheaf) :=
    freeAbelianPresheafAugmentation_locallySurjective H F
  have : Epi ((S.map (presheafToSheaf J AddCommGrpCat)).g) :=
    sheafify_map_epi_of_locallySurjective
      (freeAbelianPresheafAugmentation F.1.presheaf)
  have hS : S.Exact := freeAbelianPresheafAugmentationComplex_exact F.1.presheaf
  have hExact : (S.map (presheafToSheaf J AddCommGrpCat)).Exact :=
    hS.map_of_mono_of_preservesKernel (presheafToSheaf J AddCommGrpCat)
      (by infer_instance) (by infer_instance)
  have : Mono ((S.map (presheafToSheaf J AddCommGrpCat)).f) := by
    change Mono ((presheafToSheaf J AddCommGrpCat).map S.f)
    infer_instance
  exact ⟨hExact⟩

/-- The middle object of the extension obtained by pushing out the
augmentation kernel through the torsor difference map. -/
public noncomputable abbrev torsorPushoutMiddle
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) :
    Sheaf J AddCommGrpCat.{t} :=
  Limits.pushout
    ((presheafToSheaf J AddCommGrpCat).map
      (Limits.kernel.ι (freeAbelianPresheafAugmentation F.1.presheaf)))
    (torsorSheafAugmentationKernelMap H F)

/-- The augmentation descends to the pushout extension. -/
public noncomputable def torsorPushoutProjection
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) :
    torsorPushoutMiddle H F ⟶
      (presheafToSheaf J AddCommGrpCat).obj
        ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ))) :=
  Limits.pushout.desc
    (freeAbelianSheafAugmentation F.1.presheaf) 0 (by
      rw [Limits.comp_zero]
      change (presheafToSheaf J AddCommGrpCat).map
        (Limits.kernel.ι (freeAbelianPresheafAugmentation F.1.presheaf)) ≫
          (presheafToSheaf J AddCommGrpCat).map
            (freeAbelianPresheafAugmentation F.1.presheaf) = 0
      rw [← Functor.map_comp, Limits.kernel.condition, Functor.map_zero])

/-- The extension of the constant integer sheaf associated to a torsor.

This is glue around `torsorPushoutMiddle`: it is reducible so that its components are the
pushout and its two legs in a single spelling, which is what lets the pushout API apply to
them directly. -/
public noncomputable abbrev torsorPushoutComplex
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) :
    ShortComplex (Sheaf J AddCommGrpCat.{t}) where
  X₁ := H
  X₂ := torsorPushoutMiddle H F
  X₃ := (presheafToSheaf J AddCommGrpCat).obj
    ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)))
  f := Limits.pushout.inr _ _
  g := torsorPushoutProjection H F
  zero := Limits.pushout.inr_desc _ _ _

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma torsorPushoutInclusion_mono
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) :
    Mono (torsorPushoutComplex H F).f := by
  change Mono (Limits.pushout.inr
    ((presheafToSheaf J AddCommGrpCat).map
      (Limits.kernel.ι (freeAbelianPresheafAugmentation F.1.presheaf)))
    (torsorSheafAugmentationKernelMap H F))
  let S := freeAbelianPresheafAugmentationComplex F.1.presheaf
  have : Mono ((S.map (presheafToSheaf J AddCommGrpCat)).f) :=
    (freeAbelianSheafAugmentationComplex_shortExact H F).mono_f
  infer_instance

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma torsorPushoutProjection_epi
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) :
    Epi (torsorPushoutComplex H F).g := by
  have : Epi (freeAbelianSheafAugmentation F.1.presheaf) :=
    (freeAbelianSheafAugmentationComplex_shortExact H F).epi_g
  exact epi_of_epi_fac (f := Limits.pushout.inl _ _) (Limits.pushout.inl_desc _ _ _)

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- The pushout extension attached to a torsor is short exact. -/
public lemma torsorPushoutComplex_shortExact
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) :
    (torsorPushoutComplex H F).ShortExact := by
  have hS : ((freeAbelianPresheafAugmentationComplex F.1.presheaf).map
      (presheafToSheaf J AddCommGrpCat)).ShortExact :=
    freeAbelianSheafAugmentationComplex_shortExact H F
  have : Mono (torsorPushoutComplex H F).f := torsorPushoutInclusion_mono H F
  have : Epi (torsorPushoutComplex H F).g := torsorPushoutProjection_epi H F
  have hT : Limits.IsColimit (Limits.CokernelCofork.ofπ (torsorPushoutComplex H F).g
      (torsorPushoutComplex H F).zero) :=
    Limits.CokernelCofork.IsColimit.ofπ' _ _ (by
      intro Y k hk
      have hik : (presheafToSheaf J AddCommGrpCat).map
            (Limits.kernel.ι (freeAbelianPresheafAugmentation F.1.presheaf)) ≫
          (Limits.pushout.inl _ (torsorSheafAugmentationKernelMap H F) ≫ k) = 0 := by
        rw [Limits.pushout.condition_assoc, hk, Limits.comp_zero]
      obtain ⟨l, hl⟩ := Limits.CokernelCofork.IsColimit.desc'
        hS.gIsCokernel (Limits.pushout.inl _ _ ≫ k) hik
      refine ⟨l, Limits.pushout.hom_ext ?_ ?_⟩
      · exact (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ l) (Limits.pushout.inl_desc _ _ _)).trans hl)
      · exact (Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ l) (torsorPushoutComplex H F).zero).trans
            (Limits.zero_comp.trans hk.symm)))
  exact ⟨(torsorPushoutComplex H F).exact_of_g_is_cokernel hT⟩

/-- A section gives the corresponding generator of its free abelian
presheaf. -/
public def freeAbelianGenerators (P : Cᵒᵖ ⥤ Type t) :
    P ⟶ freeAbelianPresheaf P ⋙ forget AddCommGrpCat.{t} where
  app U := by
    dsimp [freeAbelianPresheaf, AddCommGrpCat.free]
    exact TypeCat.ofHom FreeAbelianGroup.of
  naturality := by
    intro U V f
    ext x
    change FreeAbelianGroup.of (P.map f x) =
      FreeAbelianGroup.map (P.map f) (FreeAbelianGroup.of x)
    exact (FreeAbelianGroup.map_of_apply x).symm

/-- A map of presheaves of sets into an abelian presheaf extends linearly
from its generators. -/
public noncomputable def freeAbelianPresheafLift
    (P : Cᵒᵖ ⥤ Type t) (A : Cᵒᵖ ⥤ AddCommGrpCat.{t})
    (i : P ⟶ A ⋙ forget AddCommGrpCat.{t}) :
    freeAbelianPresheaf P ⟶ A where
  app U := AddCommGrpCat.ofHom (FreeAbelianGroup.lift (fun s => i.app U s))
  naturality := by
    intro U V f
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro s
    simp [freeAbelianPresheaf, AddCommGrpCat.free,
      FreeAbelianGroup.lift_apply_of]

/-- A section of the free abelian presheaf with augmentation zero comes
from the augmentation kernel at the same object. -/
public lemma freeAbelianPresheafAugmentationKernel_lift
    (P : Cᵒᵖ ⥤ Type t) (U : Cᵒᵖ)
    (x : FreeAbelianGroup (P.obj U))
    (hx : (freeAbelianPresheafAugmentation P).app U x = 0) :
    ∃ z : (freeAbelianPresheafAugmentationKernel P).obj U,
      (Limits.kernel.ι (freeAbelianPresheafAugmentation P)).app U z = x := by
  let E : (Cᵒᵖ ⥤ AddCommGrpCat.{t}) ⥤ AddCommGrpCat.{t} :=
    (evaluation Cᵒᵖ AddCommGrpCat).obj U
  let S := freeAbelianPresheafAugmentationComplex P
  have : Mono S.f := by
    change Mono (Limits.kernel.ι (freeAbelianPresheafAugmentation P))
    infer_instance
  have hS : (S.map E).Exact :=
    (freeAbelianPresheafAugmentationComplex_exact P).map_of_mono_of_preservesKernel E
      (by infer_instance) (by infer_instance)
  exact (ShortComplex.ab_exact_iff (S.map E)).1 hS x hx

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- The kernel element represented by the difference of two generators maps
to the unique coefficient carrying the second torsor section to the first. -/
public lemma torsorGenerators_difference
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H)
    (U : Cᵒᵖ) (s s' : F.1.presheaf.obj U) :
    ∃ z : (freeAbelianPresheafAugmentationKernel F.1.presheaf).obj U,
      (Limits.kernel.ι (freeAbelianPresheafAugmentation F.1.presheaf)).app U z =
        FreeAbelianGroup.of s - FreeAbelianGroup.of s' ∧
      torsorAugmentationKernelMapAt H F U z = torsorDifference H F U s s' := by
  have hx : (freeAbelianPresheafAugmentation F.1.presheaf).app U
      (FreeAbelianGroup.of s - FreeAbelianGroup.of s') = 0 := by
    change (FreeAbelianGroup.lift (fun _ : F.1.presheaf.obj U =>
      (⟨1⟩ : ULift.{t} ℤ))) (FreeAbelianGroup.of s - FreeAbelianGroup.of s') = 0
    rw [map_sub, FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      sub_self]
  obtain ⟨z, hz⟩ := freeAbelianPresheafAugmentationKernel_lift
    F.1.presheaf U _ hx
  refine ⟨z, hz, ?_⟩
  rw [torsorAugmentationKernelMapAt_eq H F U s' z, hz, map_sub,
    torsorAffineLinearMap_of, torsorAffineLinearMap_of,
    torsorDifference_self, sub_zero]

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- A linear extension of an equivariant torsor embedding restricts on the
augmentation kernel to the coefficient map followed by the kernel inclusion. -/
public lemma freeAbelianPresheafLift_on_kernel
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t}))
    (F : AbelianTorsor S.X₁)
    (i : F.1.presheaf ⟶ S.X₂.obj ⋙ forget AddCommGrpCat.{t})
    (hi : ∀ (U : Cᵒᵖ) (h : S.X₁.obj.obj U) (s : F.1.presheaf.obj U),
      let iU : F.1.presheaf.obj U → S.X₂.obj.obj U := i.app U
      iU (F.1.act U (Multiplicative.ofAdd h) s) =
        S.f.hom.app U h + iU s)
    (U : Cᵒᵖ)
    (z : (freeAbelianPresheafAugmentationKernel F.1.presheaf).obj U) :
    (freeAbelianPresheafLift F.1.presheaf S.X₂.obj i).app U
      ((Limits.kernel.ι (freeAbelianPresheafAugmentation F.1.presheaf)).app U z) =
      S.f.hom.app U (torsorAugmentationKernelMapAt S.X₁ F U z) := by
  let x : FreeAbelianGroup (F.1.presheaf.obj U) :=
    (Limits.kernel.ι (freeAbelianPresheafAugmentation F.1.presheaf)).app U z
  have hx : (freeAbelianPresheafAugmentation F.1.presheaf).app U x = 0 :=
    congrArg (fun η => η.app U z)
      (Limits.kernel.condition (freeAbelianPresheafAugmentation F.1.presheaf))
  by_cases hne : Nonempty (F.1.presheaf.obj U)
  · let s₀ := Classical.choice hne
    have hx' : (FreeAbelianGroup.lift (fun _ : F.1.presheaf.obj U =>
        (⟨1⟩ : ULift.{t} ℤ))) x = 0 := hx
    have hgen (s : F.1.presheaf.obj U) :
        (i.app U s : S.X₂.obj.obj U) =
          S.f.hom.app U (torsorAffineLinearMap S.X₁ F U s₀ (FreeAbelianGroup.of s)) +
            ((uliftZMultiplesHom (S.X₂.obj.obj U))
                (i.app U s₀ : S.X₂.obj.obj U))
              (FreeAbelianGroup.lift (fun _ : F.1.presheaf.obj U =>
                (⟨1⟩ : ULift.{t} ℤ)) (FreeAbelianGroup.of s)) := by
      have h := hi U (torsorDifference S.X₁ F U s s₀) s₀
      rw [torsorDifference_act] at h
      have hone : ((uliftZMultiplesHom (S.X₂.obj.obj U))
            (i.app U s₀ : S.X₂.obj.obj U))
          (⟨1⟩ : ULift.{t} ℤ) = (i.app U s₀ : S.X₂.obj.obj U) := by
        rw [uliftZMultiplesHom_apply_apply]
        exact one_zsmul _
      rw [torsorAffineLinearMap_of, FreeAbelianGroup.lift_apply_of, hone]
      exact h
    have hm : FreeAbelianGroup.lift
          (fun s : F.1.presheaf.obj U => (i.app U s : S.X₂.obj.obj U)) =
        (S.f.hom.app U).hom.comp (torsorAffineLinearMap S.X₁ F U s₀) +
          ((uliftZMultiplesHom (S.X₂.obj.obj U))
              (i.app U s₀ : S.X₂.obj.obj U)).comp
            (FreeAbelianGroup.lift (fun _ : F.1.presheaf.obj U =>
              (⟨1⟩ : ULift.{t} ℤ))) := by
      refine FreeAbelianGroup.lift_ext _ _ (fun s => ?_)
      refine (FreeAbelianGroup.lift_apply_of _ _).trans ?_
      exact (hgen s).trans (AddMonoidHom.add_apply
        ((S.f.hom.app U).hom.comp (torsorAffineLinearMap S.X₁ F U s₀))
        (((uliftZMultiplesHom (S.X₂.obj.obj U))
            (i.app U s₀ : S.X₂.obj.obj U)).comp
          (FreeAbelianGroup.lift (fun _ : F.1.presheaf.obj U =>
            (⟨1⟩ : ULift.{t} ℤ)))) (FreeAbelianGroup.of s)).symm
    have hmx := congrArg
      (fun φ : FreeAbelianGroup (F.1.presheaf.obj U) →+ S.X₂.obj.obj U => φ x) hm
    have hz : ((uliftZMultiplesHom (S.X₂.obj.obj U))
          (i.app U s₀ : S.X₂.obj.obj U))
        ((FreeAbelianGroup.lift (fun _ : F.1.presheaf.obj U =>
          (⟨1⟩ : ULift.{t} ℤ))) x) = 0 := by
      rw [hx']
      exact map_zero _
    rw [torsorAugmentationKernelMapAt_eq S.X₁ F U s₀ z]
    refine Eq.trans hmx ?_
    refine (AddMonoidHom.add_apply _ _ x).trans ?_
    refine (congrArg (fun c => ((S.f.hom.app U).hom.comp
      (torsorAffineLinearMap S.X₁ F U s₀)) x + c) hz).trans ?_
    exact add_zero _
  · have : IsEmpty (F.1.presheaf.obj U) := ⟨fun s => hne ⟨s⟩⟩
    have : Subsingleton (FreeAbelianGroup (F.1.presheaf.obj U)) := inferInstance
    have hx0 : x = 0 := Subsingleton.elim _ _
    have hz0 : (Limits.kernel.ι
        (freeAbelianPresheafAugmentation F.1.presheaf)).app U z = 0 := hx0
    rw [torsorAugmentationKernelMapAt_eq_zero_of_empty S.X₁ F U hne]
    rw [hz0]
    simp only [AddMonoidHom.zero_apply, map_zero]

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma freeAbelianPresheafLift_kernel_comp
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t}))
    (F : AbelianTorsor S.X₁)
    (i : F.1.presheaf ⟶ S.X₂.obj ⋙ forget AddCommGrpCat.{t})
    (hi : ∀ (U : Cᵒᵖ) (h : S.X₁.obj.obj U) (s : F.1.presheaf.obj U),
      let iU : F.1.presheaf.obj U → S.X₂.obj.obj U := i.app U
      iU (F.1.act U (Multiplicative.ofAdd h) s) =
        S.f.hom.app U h + iU s) :
    Limits.kernel.ι (freeAbelianPresheafAugmentation F.1.presheaf) ≫
      freeAbelianPresheafLift F.1.presheaf S.X₂.obj i =
      torsorAugmentationKernelMap S.X₁ F ≫ S.f.hom := by
  ext U z
  exact freeAbelianPresheafLift_on_kernel S F i hi U z

/-- Sheafified linear extension of an equivariant map from a torsor. -/
public noncomputable def freeAbelianSheafLift
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t}))
    (F : AbelianTorsor S.X₁)
    (i : F.1.presheaf ⟶ S.X₂.obj ⋙ forget AddCommGrpCat.{t}) :
    freeAbelianSheafOnPresheaf F.1.presheaf ⟶ S.X₂ :=
  ((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).symm
    (freeAbelianPresheafLift F.1.presheaf S.X₂.obj i)

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma freeAbelianSheafLift_kernel_comp
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t}))
    (F : AbelianTorsor S.X₁)
    (i : F.1.presheaf ⟶ S.X₂.obj ⋙ forget AddCommGrpCat.{t})
    (hi : ∀ (U : Cᵒᵖ) (h : S.X₁.obj.obj U) (s : F.1.presheaf.obj U),
      let iU : F.1.presheaf.obj U → S.X₂.obj.obj U := i.app U
      iU (F.1.act U (Multiplicative.ofAdd h) s) =
        S.f.hom.app U h + iU s) :
    (presheafToSheaf J AddCommGrpCat).map
        (Limits.kernel.ι (freeAbelianPresheafAugmentation F.1.presheaf)) ≫
      freeAbelianSheafLift S F i =
    torsorSheafAugmentationKernelMap S.X₁ F ≫ S.f := by
  apply ((sheafificationAdjunction J AddCommGrpCat.{t}).homEquiv _ S.X₂).injective
  rw [Adjunction.homEquiv_naturality_left, freeAbelianSheafLift, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, torsorSheafAugmentationKernelMap,
    Equiv.apply_symm_apply]
  exact freeAbelianPresheafLift_kernel_comp S F i hi

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- If every torsor section maps to a chosen quotient section, the linear
extension has the expected quotient map on generators. -/
public lemma freeAbelianPresheafLift_quotient_comp
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t}))
    (q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj)
    (F : AbelianTorsor S.X₁)
    (i : F.1.presheaf ⟶ S.X₂.obj ⋙ forget AddCommGrpCat.{t})
    (hi : ∀ (U : Cᵒᵖ) (s : F.1.presheaf.obj U),
      S.g.hom.app U (i.app U s) = q.app U ⟨1⟩) :
    freeAbelianPresheafLift F.1.presheaf S.X₂.obj i ≫ S.g.hom =
      freeAbelianPresheafAugmentation F.1.presheaf ≫ q := by
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro s
  have hl : (freeAbelianPresheafLift F.1.presheaf S.X₂.obj i).app U
      (FreeAbelianGroup.of s) = (i.app U s : S.X₂.obj.obj U) :=
    FreeAbelianGroup.lift_apply_of _ _
  have hr : (freeAbelianPresheafAugmentation F.1.presheaf).app U
      (FreeAbelianGroup.of s) = (⟨1⟩ : ULift.{t} ℤ) :=
    FreeAbelianGroup.lift_apply_of _ _
  calc (freeAbelianPresheafLift F.1.presheaf S.X₂.obj i ≫ S.g.hom).app U
        (FreeAbelianGroup.of s)
      = S.g.hom.app U ((freeAbelianPresheafLift F.1.presheaf S.X₂.obj i).app U
          (FreeAbelianGroup.of s)) := CategoryTheory.comp_apply _ _ _
    _ = S.g.hom.app U (i.app U s) := congrArg _ hl
    _ = q.app U (⟨1⟩ : ULift.{t} ℤ) := hi U s
    _ = q.app U ((freeAbelianPresheafAugmentation F.1.presheaf).app U
          (FreeAbelianGroup.of s)) := congrArg _ hr.symm
    _ = (freeAbelianPresheafAugmentation F.1.presheaf ≫ q).app U
          (FreeAbelianGroup.of s) := (CategoryTheory.comp_apply _ _ _).symm

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma freeAbelianSheafLift_quotient_comp
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t}))
    (q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj)
    (F : AbelianTorsor S.X₁)
    (i : F.1.presheaf ⟶ S.X₂.obj ⋙ forget AddCommGrpCat.{t})
    (hi : ∀ (U : Cᵒᵖ) (s : F.1.presheaf.obj U),
      S.g.hom.app U (i.app U s) = q.app U ⟨1⟩) :
    freeAbelianSheafLift S F i ≫ S.g =
      freeAbelianSheafAugmentation F.1.presheaf ≫
        ((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).symm q := by
  apply ((sheafificationAdjunction J AddCommGrpCat.{t}).homEquiv _ S.X₃).injective
  rw [Adjunction.homEquiv_naturality_right, freeAbelianSheafLift, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply]
  exact freeAbelianPresheafLift_quotient_comp S q F i hi

/-- An equivariant map of a torsor into the middle sheaf extends uniquely
over the pushout associated to the torsor. -/
public noncomputable def torsorPushoutToMiddle
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t}))
    (F : AbelianTorsor S.X₁)
    (i : F.1.presheaf ⟶ S.X₂.obj ⋙ forget AddCommGrpCat.{t})
    (hi : ∀ (U : Cᵒᵖ) (h : S.X₁.obj.obj U) (s : F.1.presheaf.obj U),
      let iU : F.1.presheaf.obj U → S.X₂.obj.obj U := i.app U
      iU (F.1.act U (Multiplicative.ofAdd h) s) =
        S.f.hom.app U h + iU s) :
    torsorPushoutMiddle S.X₁ F ⟶ S.X₂ :=
  Limits.pushout.desc (freeAbelianSheafLift S F i) S.f
    (freeAbelianSheafLift_kernel_comp S F i hi)

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma torsorPushoutToMiddle_comp_g
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t}))
    (q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj)
    (F : AbelianTorsor S.X₁)
    (i : F.1.presheaf ⟶ S.X₂.obj ⋙ forget AddCommGrpCat.{t})
    (hi : ∀ (U : Cᵒᵖ) (h : S.X₁.obj.obj U) (s : F.1.presheaf.obj U),
      let iU : F.1.presheaf.obj U → S.X₂.obj.obj U := i.app U
      iU (F.1.act U (Multiplicative.ofAdd h) s) =
        S.f.hom.app U h + iU s)
    (hiFiber : ∀ (U : Cᵒᵖ) (s : F.1.presheaf.obj U),
      S.g.hom.app U (i.app U s) = q.app U ⟨1⟩) :
    torsorPushoutToMiddle S F i hi ≫ S.g =
      torsorPushoutProjection S.X₁ F ≫
        ((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).symm q := by
  apply Limits.pushout.hom_ext
  · simp only [← Category.assoc, torsorPushoutToMiddle,
      Limits.pushout.inl_desc, torsorPushoutProjection,
      freeAbelianSheafLift_quotient_comp S q F i hiFiber,
      Limits.pushout.inl_desc]
  · simp only [← Category.assoc, torsorPushoutToMiddle,
      Limits.pushout.inr_desc, torsorPushoutProjection,
      Limits.pushout.inr_desc, S.zero, Limits.zero_comp]

public def torsorPushoutComparison
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t}))
    (q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj)
    (F : AbelianTorsor S.X₁)
    (i : F.1.presheaf ⟶ S.X₂.obj ⋙ forget AddCommGrpCat.{t})
    (hi : ∀ (U : Cᵒᵖ) (h : S.X₁.obj.obj U) (s : F.1.presheaf.obj U),
      let iU : F.1.presheaf.obj U → S.X₂.obj.obj U := i.app U
      iU (F.1.act U (Multiplicative.ofAdd h) s) =
        S.f.hom.app U h + iU s)
    (hiFiber : ∀ (U : Cᵒᵖ) (s : F.1.presheaf.obj U),
      S.g.hom.app U (i.app U s) = q.app U ⟨1⟩) :
    torsorPushoutComplex S.X₁ F ⟶ S where
  τ₁ := 𝟙 _
  τ₂ := torsorPushoutToMiddle S F i hi
  τ₃ := ((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).symm q
  comm₁₂ := by
    rw [Category.id_comp]
    exact (Limits.pushout.inr_desc _ _ _).symm
  comm₂₃ := torsorPushoutToMiddle_comp_g S q F i hi hiFiber

/-- The pushout extension of any torsor embedded in a fiber represents the
boundary of the section defining that fiber. -/
public lemma torsorPushout_extClass_eq_boundary
    (S : ShortComplex (Sheaf J AddCommGrpCat.{t})) (hS : S.ShortExact)
    (q : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ S.X₃.obj)
    (F : AbelianTorsor S.X₁)
    (i : F.1.presheaf ⟶ S.X₂.obj ⋙ forget AddCommGrpCat.{t})
    (hi : ∀ (U : Cᵒᵖ) (h : S.X₁.obj.obj U) (s : F.1.presheaf.obj U),
      let iU : F.1.presheaf.obj U → S.X₂.obj.obj U := i.app U
      iU (F.1.act U (Multiplicative.ofAdd h) s) =
        S.f.hom.app U h + iU s)
    (hiFiber : ∀ (U : Cᵒᵖ) (s : F.1.presheaf.obj U),
      S.g.hom.app U (i.app U s) = q.app U ⟨1⟩) :
    (torsorPushoutComplex_shortExact S.X₁ F).extClass =
      (Abelian.Ext.mk₀ (((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).symm q)).comp
        hS.extClass (zero_add 1) :=
  (Abelian.Ext.comp_mk₀_id _).symm.trans
    ((torsorPushoutComplex_shortExact S.X₁ F).extClass_naturality hS
      (torsorPushoutComparison S q F i hi hiFiber))

/-- The unit of sheafification for the constant integer presheaf. -/
public noncomputable def constantUnit :
    (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶
      ((presheafToSheaf J AddCommGrpCat).obj
        ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)))).obj :=
  (sheafificationAdjunction J AddCommGrpCat).homEquiv _ _ (𝟙 _)

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma constantUnit_adj_inverse :
    ((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _).symm
      (constantUnit (J := J) (C := C)) =
        𝟙 ((presheafToSheaf J AddCommGrpCat).obj
          ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)))) := by
  let P := (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ))
  let adj := sheafificationAdjunction J AddCommGrpCat.{t}
  exact (adj.homEquiv P ((presheafToSheaf J AddCommGrpCat).obj P)).symm_apply_apply (𝟙 _)

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma constantUnit_app_one (U : Cᵒᵖ) :
    (constantUnit (J := J) (C := C)).app U (⟨1⟩ : ULift.{t} ℤ) =
      (toSheafify J
        ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)))).app U ⟨1⟩ := by
  let P := (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ))
  let adj := sheafificationAdjunction J AddCommGrpCat.{t}
  change ((adj.homEquiv P ((presheafToSheaf J AddCommGrpCat).obj P))
    (𝟙 _)).app U ⟨1⟩ = _
  rw [adj.homEquiv_unit]
  simp
  rfl

/-- The cohomology class of the extension canonically attached to a torsor. -/
public noncomputable def torsorPushoutClass
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) : Sheaf.H H 1 :=
  (torsorPushoutComplex_shortExact H F).extClass

/-- The generator of a torsor section in the pushout extension. -/
public noncomputable def torsorPushoutGenerator
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H) :
    F.1.presheaf ⟶ (torsorPushoutMiddle H F).obj ⋙ forget AddCommGrpCat.{t} :=
  freeAbelianGenerators F.1.presheaf ≫
    Functor.whiskerRight
      (toSheafify J (freeAbelianPresheaf F.1.presheaf)) (forget AddCommGrpCat.{t}) ≫
    Functor.whiskerRight
      (Limits.pushout.inl
        ((presheafToSheaf J AddCommGrpCat).map
          (Limits.kernel.ι (freeAbelianPresheafAugmentation F.1.presheaf)))
        (torsorSheafAugmentationKernelMap H F)).hom (forget AddCommGrpCat.{t})

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- Every torsor generator has augmentation one in the pushout extension. -/
public lemma torsorPushoutGenerator_projection
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H)
    (U : Cᵒᵖ) (s : F.1.presheaf.obj U) :
    (torsorPushoutProjection H F).hom.app U
      ((torsorPushoutGenerator H F).app U s) =
      (toSheafify J
        ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)))).app U ⟨1⟩ := by
  have hdesc : Limits.pushout.inl _ (torsorSheafAugmentationKernelMap H F) ≫
      torsorPushoutProjection H F = freeAbelianSheafAugmentation F.1.presheaf :=
    Limits.pushout.inl_desc _ _ _
  have hnat := toSheafify_naturality J
    (freeAbelianPresheafAugmentation F.1.presheaf)
  have hU := congrArg (fun k => k.app U
    (FreeAbelianGroup.of s)) hnat
  simp only [NatTrans.comp_app] at hU
  have hdescU := congrArg (fun k => k.hom.app U
    ((toSheafify J (freeAbelianPresheaf F.1.presheaf)).app U
      (FreeAbelianGroup.of s))) hdesc
  have haug : (freeAbelianPresheafAugmentation F.1.presheaf).app U
      (FreeAbelianGroup.of s) = (⟨1⟩ : ULift.{t} ℤ) := by
    change FreeAbelianGroup.lift (fun _ : F.1.presheaf.obj U =>
      (⟨1⟩ : ULift.{t} ℤ)) (FreeAbelianGroup.of s) = ⟨1⟩
    simp
  refine (hdescU.trans hU.symm).trans ?_
  refine (CategoryTheory.comp_apply _ _ _).trans ?_
  exact congrArg (fun y => (toSheafify J
    ((Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)))).app U y) haug

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
/-- The difference of two generators in the pushout is the image of the
unique coefficient carrying one torsor section to the other. -/
public lemma torsorPushoutGenerator_sub
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H)
    (U : Cᵒᵖ) (s s' : F.1.presheaf.obj U) :
    (torsorPushoutGenerator H F).app U s -
      (torsorPushoutGenerator H F).app U s' =
      (torsorPushoutComplex H F).f.hom.app U
        (torsorDifference H F U s s') := by
  obtain ⟨z, hz, hd⟩ := torsorGenerators_difference H F U s s'
  let k := Limits.kernel.ι (freeAbelianPresheafAugmentation F.1.presheaf)
  let a := torsorSheafAugmentationKernelMap H F
  let e := (presheafToSheaf J AddCommGrpCat).map k
  let l := Limits.pushout.inl e a
  let r := Limits.pushout.inr e a
  have hcond : e ≫ l = a ≫ r := Limits.pushout.condition
  have hcondU := congrArg (fun f => f.hom.app U
    ((toSheafify J (freeAbelianPresheafAugmentationKernel F.1.presheaf)).app U z))
    hcond
  have hnat := toSheafify_naturality J k
  have hnatU := congrArg (fun f => f.app U z) hnat
  have hmap := torsorSheafAugmentationKernelMap_on_sections H F
  have hmapU := congrArg (fun f => f.app U z) hmap
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hnatU hmapU
  change (l.hom.app U) ((e.hom.app U)
      ((toSheafify J (freeAbelianPresheafAugmentationKernel F.1.presheaf)).app U z)) =
    (r.hom.app U) ((a.hom.app U)
      ((toSheafify J (freeAbelianPresheafAugmentationKernel F.1.presheaf)).app U z))
    at hcondU
  have hleft : (e.hom.app U)
      ((toSheafify J (freeAbelianPresheafAugmentationKernel F.1.presheaf)).app U z) =
      (toSheafify J (freeAbelianPresheaf F.1.presheaf)).app U
        (FreeAbelianGroup.of s - FreeAbelianGroup.of s') := by
    simpa only [e, k, hz] using hnatU.symm
  have hright : (a.hom.app U)
      ((toSheafify J (freeAbelianPresheafAugmentationKernel F.1.presheaf)).app U z) =
      torsorDifference H F U s s' := by
    change (a.hom.app U)
      ((toSheafify J (freeAbelianPresheafAugmentationKernel F.1.presheaf)).app U z) =
      torsorAugmentationKernelMapAt H F U z at hmapU
    exact hmapU.trans hd
  have hsub : (toSheafify J (freeAbelianPresheaf F.1.presheaf)).app U
        (FreeAbelianGroup.of s - FreeAbelianGroup.of s') =
      (toSheafify J (freeAbelianPresheaf F.1.presheaf)).app U
          (FreeAbelianGroup.of s) -
        (toSheafify J (freeAbelianPresheaf F.1.presheaf)).app U
          (FreeAbelianGroup.of s') :=
    map_sub _ _ _
  have hlsub : (l.hom.app U)
        ((toSheafify J (freeAbelianPresheaf F.1.presheaf)).app U
            (FreeAbelianGroup.of s) -
          (toSheafify J (freeAbelianPresheaf F.1.presheaf)).app U
            (FreeAbelianGroup.of s')) =
      (l.hom.app U) ((toSheafify J (freeAbelianPresheaf F.1.presheaf)).app U
          (FreeAbelianGroup.of s)) -
        (l.hom.app U) ((toSheafify J (freeAbelianPresheaf F.1.presheaf)).app U
          (FreeAbelianGroup.of s')) :=
    map_sub _ _ _
  rw [hleft, hright, hsub, hlsub] at hcondU
  exact hcondU

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{t})] in
public lemma torsorPushoutGenerator_act
    (H : Sheaf J AddCommGrpCat.{t}) (F : AbelianTorsor H)
    (U : Cᵒᵖ) (h : H.obj.obj U) (s : F.1.presheaf.obj U) :
    let iU : F.1.presheaf.obj U → (torsorPushoutComplex H F).X₂.obj.obj U :=
      (torsorPushoutGenerator H F).app U
    iU (F.1.act U (Multiplicative.ofAdd h) s) =
      (torsorPushoutComplex H F).f.hom.app U h + iU s := by
  have hs := torsorPushoutGenerator_sub H F U
    (F.1.act U (Multiplicative.ofAdd h) s) s
  rw [torsorDifference_eq_of_act H F U _ s h rfl] at hs
  exact sub_eq_iff_eq_add.mp hs

end Stacks.Cohomology.Torsors
