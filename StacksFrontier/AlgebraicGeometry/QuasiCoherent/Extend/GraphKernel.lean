module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Properties.GabberResult.Abelian
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# Graph kernels along a quasi-compact open immersion

Let `j : U ⟶ X` be a quasi-compact open immersion of schemes, let `F` be a module on `X`, let
`G` be a module on `U` and let `φ : G ⟶ j^*F`. The *graph kernel* of `φ` is the kernel of
`F ⊞ j_*G ⟶ j_*j^*F`, `(a, b) ↦ η_F a - j_*φ b`, where `η` is the unit of `j^* ⊣ j_*`. It is a
module on `X` whose inverse image along `j` is canonically `G`, by way of the graph
`b ↦ (φ b, b)`, and it is quasi-coherent as soon as `F` and `G` are. This is the construction
behind the two extension statements of Stacks Tag 01PE that carry a morphism: a morphism into
`j^*F`, and a quasi-coherent submodule of `j^*F`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.graphKernelMap` is the map `F ⊞ j_*G ⟶ j_*j^*F` whose kernel
  is taken.
* `AlgebraicGeometry.Scheme.Modules.graphKernel` is its kernel, and
  `AlgebraicGeometry.Scheme.Modules.graphKernelProjection` is the induced map to `F`.
* `CategoryTheory.Limits.kernelBiprodDescIdNegIso` is the underlying categorical fact: the graph
  of `f : B ⟶ A` identifies `B` with the kernel of `A ⊞ B ⟶ A`, `(a, b) ↦ a - f b`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.graphKernel_isQuasicoherent`: the graph kernel of a map
  between quasi-coherent modules is quasi-coherent.
* `AlgebraicGeometry.Scheme.Modules.graphKernelPullbackIso` identifies `j^*` of the graph kernel
  with `G`, and `AlgebraicGeometry.Scheme.Modules.graphKernelPullbackIso_hom_comp` says that
  under that identification `j^*` of the projection to `F` is `φ`.
* `AlgebraicGeometry.Scheme.Modules.graphKernelProjection_mono`: the projection is a
  monomorphism whenever `φ` is.

## Implementation notes

Quasi-coherence of the graph kernel needs no local computation: pushforward along a
quasi-compact open immersion preserves quasi-coherence (Tag 01LC,
`AlgebraicGeometry.pushforward_isQuasicoherent`), inverse image preserves it along any morphism
(Tag 01BG, `Stacks.Modules.isQuasicoherent_pullback`), a biproduct of quasi-coherent modules is
quasi-coherent (Tag 01BF, here in the scheme-level form
`AlgebraicGeometry.isQuasicoherent_binaryProduct`), and a kernel of a map of quasi-coherent
modules is quasi-coherent
(`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`). So the instance is one
`inferInstanceAs`.

`graphKernel` carries `@[implicit_reducible]`, which is what lets the identification of
`(pullback j).obj (graphKernel j F G φ)` with `(pullback j).obj (kernel (graphKernelMap j F G φ))`
happen inside a definitional-equality check while leaving `graphKernel` folded for `simp`; the
composite isomorphism `graphKernelPullbackIso` does not elaborate without it.

## References

* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

/-- The graph of `f : B ⟶ A` identifies `B` with the kernel of `A ⊞ B ⟶ A`, `(a, b) ↦ a - f b`. -/
def kernelBiprodDescIdNegIso {A B : C} (f : B ⟶ A)
    [HasKernel (biprod.desc (𝟙 A) (-f))] : kernel (biprod.desc (𝟙 A) (-f)) ≅ B where
  hom := kernel.ι (biprod.desc (𝟙 A) (-f)) ≫ biprod.snd
  inv := kernel.lift (biprod.desc (𝟙 A) (-f)) (biprod.lift f (𝟙 B)) (by simp)
  hom_inv_id := by
    refine (cancel_mono (kernel.ι (biprod.desc (𝟙 A) (-f)))).1 ?_
    rw [Category.assoc, kernel.lift_ι, Category.id_comp]
    refine biprod.hom_ext _ _ ?_ ?_
    · have h : kernel.ι (biprod.desc (𝟙 A) (-f)) ≫ biprod.fst
          + -(kernel.ι (biprod.desc (𝟙 A) (-f)) ≫ biprod.snd ≫ f) = 0 := by
        simpa [biprod.desc_eq] using kernel.condition (biprod.desc (𝟙 A) (-f))
      simpa using (add_neg_eq_zero.mp h).symm
    · simp
  inv_hom_id := by
    rw [← Category.assoc, kernel.lift_ι]
    simp

/-- The kernel inclusion of `biprod.desc f g` satisfies `ι ≫ fst ≫ f + ι ≫ snd ≫ g = 0`. -/
lemma kernel_ι_comp_biprod_desc_add {A B W : C} (f : A ⟶ W) (g : B ⟶ W)
    [HasKernel (biprod.desc f g)] :
    kernel.ι (biprod.desc f g) ≫ biprod.fst ≫ f +
      kernel.ι (biprod.desc f g) ≫ biprod.snd ≫ g = 0 := by
  rw [← Preadditive.comp_add, ← biprod.desc_eq]
  exact kernel.condition _

/-- The isomorphism `kernelBiprodDescIdNegIso f` is the kernel inclusion followed by the second
projection. -/
@[simp]
lemma kernelBiprodDescIdNegIso_hom {A B : C} (f : B ⟶ A)
    [HasKernel (biprod.desc (𝟙 A) (-f))] :
    (kernelBiprodDescIdNegIso f).hom = kernel.ι (biprod.desc (𝟙 A) (-f)) ≫ biprod.snd :=
  rfl

end CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- A biproduct of two quasi-coherent modules on a scheme is quasi-coherent. -/
instance isQuasicoherent_biprod {X : Scheme.{u}} (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (M ⊞ N).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (biprod.isoProd M N).symm
    (isQuasicoherent_binaryProduct X)

variable {U X : Scheme.{u}} (j : U ⟶ X) (F : X.Modules) (G : U.Modules)
  (φ : G ⟶ (pullback j).obj F)

/-- The unit on `F` minus the pushforward of `φ` on the second summand. -/
def graphKernelMap :
    F ⊞ (pushforward j).obj G ⟶ (pushforward j).obj ((pullback j).obj F) :=
  biprod.desc ((pullbackPushforwardAdjunction j).unit.app F) (-(pushforward j).map φ)

/-- The graph kernel extending `G` across the open immersion. -/
@[implicit_reducible]
def graphKernel : X.Modules := kernel (graphKernelMap j F G φ)

/-- The projection of the graph kernel to `F`. -/
def graphKernelProjection : graphKernel j F G φ ⟶ F :=
  kernel.ι (graphKernelMap j F G φ) ≫ biprod.fst

/-- The two components of a section of the graph kernel determine each other. -/
lemma graphKernel_ι_comp_fst_unit :
    kernel.ι (graphKernelMap j F G φ) ≫ biprod.fst ≫
        (pullbackPushforwardAdjunction j).unit.app F =
      kernel.ι (graphKernelMap j F G φ) ≫ biprod.snd ≫ (pushforward j).map φ := by
  have h := kernel_ι_comp_biprod_desc_add
    ((pullbackPushforwardAdjunction j).unit.app F) (-(pushforward j).map φ)
  rw [Preadditive.comp_neg, Preadditive.comp_neg] at h
  exact add_neg_eq_zero.mp h

/-- The graph kernel of a map between quasi-coherent modules along a quasi-compact open immersion
is quasi-coherent. -/
instance graphKernel_isQuasicoherent [IsOpenImmersion j] [QuasiCompact j]
    [F.IsQuasicoherent] [G.IsQuasicoherent] : (graphKernel j F G φ).IsQuasicoherent :=
  inferInstanceAs (kernel (graphKernelMap j F G φ)).IsQuasicoherent

/-- Inverse image along an open immersion preserves finite limits. -/
instance pullback_preservesFiniteLimits [IsOpenImmersion j] :
    PreservesFiniteLimits (pullback j) :=
  preservesFiniteLimits_of_natIso (restrictFunctorIsoPullback j)

/-- The counit of `j^* ⊣ j_*` is an isomorphism for an open immersion `j`. -/
instance pullbackPushforwardAdjunction_counit_isIso [IsOpenImmersion j] :
    IsIso (pullbackPushforwardAdjunction j).counit :=
  Adjunction.counit_isIso_of_R_fully_faithful _

/-- Inverse image along an open immersion preserves binary biproducts. -/
instance pullback_preservesBinaryBiproducts [IsOpenImmersion j] :
    PreservesBinaryBiproducts (pullback j) :=
  preservesBinaryBiproducts_of_preservesBinaryCoproducts _

/-- The pullback of `F ⊞ j_*G` splits as `j^*F ⊞ G`. -/
def graphKernelSourceIso [IsOpenImmersion j] :
    (pullback j).obj (F ⊞ (pushforward j).obj G) ≅ (pullback j).obj F ⊞ G :=
  (pullback j).mapBiprod F ((pushforward j).obj G) ≪≫
    biprod.mapIso (Iso.refl _) (asIso ((pullbackPushforwardAdjunction j).counit.app G))

/-- The counit at `j^*F`, identifying `j^*j_*j^*F` with `j^*F`. -/
def graphKernelTargetIso [IsOpenImmersion j] :
    (pullback j).obj ((pushforward j).obj ((pullback j).obj F)) ≅ (pullback j).obj F :=
  asIso ((pullbackPushforwardAdjunction j).counit.app ((pullback j).obj F))

/-- The isomorphism `graphKernelTargetIso j F` is the counit of `j^* ⊣ j_*` at `j^*F`. -/
@[simp]
lemma graphKernelTargetIso_hom [IsOpenImmersion j] :
    (graphKernelTargetIso j F).hom =
      (pullbackPushforwardAdjunction j).counit.app ((pullback j).obj F) :=
  rfl

/-- The inverse of `graphKernelSourceIso` restricts on `j^*F` to `j^*` of the first inclusion. -/
lemma graphKernelSourceIso_inv_inl [IsOpenImmersion j] :
    biprod.inl ≫ (graphKernelSourceIso j F G).inv = (pullback j).map biprod.inl := by
  rw [graphKernelSourceIso, Iso.trans_inv, biprod.mapIso_inv, ← Category.assoc, biprod.inl_map,
    Iso.refl_inv, Category.id_comp]
  exact biprod.inl_desc _ _

/-- The inverse of `graphKernelSourceIso` restricts on `G` to the inverse of the counit followed
by `j^*` of the second inclusion. -/
lemma graphKernelSourceIso_inv_inr [IsOpenImmersion j] :
    biprod.inr ≫ (graphKernelSourceIso j F G).inv =
      inv ((pullbackPushforwardAdjunction j).counit.app G) ≫ (pullback j).map biprod.inr := by
  rw [graphKernelSourceIso, Iso.trans_inv, biprod.mapIso_inv, ← Category.assoc, biprod.inr_map,
    Category.assoc]
  exact congrArg (fun x => inv ((pullbackPushforwardAdjunction j).counit.app G) ≫ x)
    (biprod.inr_desc ((pullback j).map biprod.inl) ((pullback j).map biprod.inr))

/-- The second component of `graphKernelSourceIso` is `j^*` of the second projection followed by
the counit. -/
lemma graphKernelSourceIso_hom_snd [IsOpenImmersion j] :
    (graphKernelSourceIso j F G).hom ≫ biprod.snd =
      (pullback j).map biprod.snd ≫ (pullbackPushforwardAdjunction j).counit.app G := by
  rw [graphKernelSourceIso, Iso.trans_hom, biprod.mapIso_hom, Category.assoc, biprod.map_snd,
    ← Category.assoc]
  exact congrArg (fun x => x ≫ (pullbackPushforwardAdjunction j).counit.app G)
    (biprod.lift_snd ((pullback j).map biprod.fst) ((pullback j).map biprod.snd))

/-- Naturality of the counit: `φ` and its pushforward agree under the counit. -/
lemma counit_app_comp [IsOpenImmersion j] :
    (pullbackPushforwardAdjunction j).counit.app G ≫ φ =
      (pullback j).map ((pushforward j).map φ) ≫ (graphKernelTargetIso j F).hom :=
  ((pullbackPushforwardAdjunction j).counit.naturality φ).symm

/-- Under the two identifications, `j^*` of the graph-kernel map is `(a, b) ↦ a - φ b`. -/
lemma graphKernelSourceIso_inv_map_comp [IsOpenImmersion j] :
    (graphKernelSourceIso j F G).inv ≫ (pullback j).map (graphKernelMap j F G φ) ≫
        (graphKernelTargetIso j F).hom = biprod.desc (𝟙 ((pullback j).obj F)) (-φ) := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [← Category.assoc, graphKernelSourceIso_inv_inl]
    calc (pullback j).map biprod.inl ≫ (pullback j).map (graphKernelMap j F G φ) ≫
            (graphKernelTargetIso j F).hom
        = (pullback j).map (biprod.inl ≫ graphKernelMap j F G φ) ≫
            (graphKernelTargetIso j F).hom := by rw [← Category.assoc, ← Functor.map_comp]
      _ = (pullback j).map ((pullbackPushforwardAdjunction j).unit.app F) ≫
            (pullbackPushforwardAdjunction j).counit.app ((pullback j).obj F) := by
            rw [graphKernelMap, biprod.inl_desc, graphKernelTargetIso_hom]
      _ = 𝟙 ((pullback j).obj F) := Adjunction.left_triangle_components _ F
      _ = biprod.inl ≫ biprod.desc (𝟙 ((pullback j).obj F)) (-φ) := (biprod.inl_desc _ _).symm
  · rw [← Category.assoc, graphKernelSourceIso_inv_inr]
    calc (inv ((pullbackPushforwardAdjunction j).counit.app G) ≫ (pullback j).map biprod.inr) ≫
            (pullback j).map (graphKernelMap j F G φ) ≫ (graphKernelTargetIso j F).hom
        = inv ((pullbackPushforwardAdjunction j).counit.app G) ≫
            (pullback j).map (biprod.inr ≫ graphKernelMap j F G φ) ≫
              (graphKernelTargetIso j F).hom := by
            rw [Category.assoc, ← Category.assoc ((pullback j).map biprod.inr), ← Functor.map_comp]
      _ = inv ((pullbackPushforwardAdjunction j).counit.app G) ≫
            (-((pullback j).map ((pushforward j).map φ) ≫ (graphKernelTargetIso j F).hom)) := by
            rw [graphKernelMap, biprod.inr_desc, Functor.map_neg, Preadditive.neg_comp]
      _ = -φ := by
            rw [← counit_app_comp j F G φ, Preadditive.comp_neg, IsIso.inv_hom_id_assoc]
      _ = biprod.inr ≫ biprod.desc (𝟙 ((pullback j).obj F)) (-φ) := (biprod.inr_desc _ _).symm

/-- The canonical graph identification of the pulled-back kernel with `G`. -/
def graphKernelPullbackIso [IsOpenImmersion j] :
    (pullback j).obj (graphKernel j F G φ) ≅ G :=
  PreservesKernel.iso (pullback j) (graphKernelMap j F G φ) ≪≫
    kernel.mapIso ((pullback j).map (graphKernelMap j F G φ))
      (biprod.desc (𝟙 ((pullback j).obj F)) (-φ)) (graphKernelSourceIso j F G)
      (graphKernelTargetIso j F)
      (by rw [← graphKernelSourceIso_inv_map_comp j F G φ, Iso.hom_inv_id_assoc]) ≪≫
    kernelBiprodDescIdNegIso φ

/-- The graph identification is induced by the second projection and the counit. -/
lemma graphKernelPullbackIso_hom [IsOpenImmersion j] :
    (graphKernelPullbackIso j F G φ).hom =
      (pullback j).map (kernel.ι (graphKernelMap j F G φ) ≫ biprod.snd) ≫
        (pullbackPushforwardAdjunction j).counit.app G := by
  rw [graphKernelPullbackIso, Iso.trans_hom, Iso.trans_hom, kernelBiprodDescIdNegIso_hom,
    kernel.mapIso_hom, kernel.lift_ι_assoc, PreservesKernel.iso_hom, Category.assoc,
    kernelComparison_comp_ι_assoc, graphKernelSourceIso_hom_snd, ← Category.assoc,
    ← Functor.map_comp]

/-- Under the graph identification, the restricted projection is `φ`. -/
lemma graphKernelPullbackIso_hom_comp [IsOpenImmersion j] :
    (graphKernelPullbackIso j F G φ).hom ≫ φ =
      (pullback j).map (graphKernelProjection j F G φ) := by
  rw [graphKernelPullbackIso_hom, Category.assoc, counit_app_comp j F G φ, ← Category.assoc,
    ← Functor.map_comp, Category.assoc, ← graphKernel_ι_comp_fst_unit, graphKernelTargetIso_hom,
    show kernel.ι (graphKernelMap j F G φ) ≫ biprod.fst ≫
        (pullbackPushforwardAdjunction j).unit.app F =
        graphKernelProjection j F G φ ≫ (pullbackPushforwardAdjunction j).unit.app F from
      (Category.assoc _ _ _).symm,
    Functor.map_comp, Category.assoc, Adjunction.left_triangle_components, Category.comp_id]

/-- Injectivity of `φ` implies injectivity of the graph projection. -/
instance graphKernelProjection_mono [IsOpenImmersion j] [Mono φ] :
    Mono (graphKernelProjection j F G φ) := by
  have hmono : Mono ((pushforward j).map φ) := inferInstance
  refine ⟨fun {Z} a b hab => ?_⟩
  have hfst : a ≫ kernel.ι (graphKernelMap j F G φ) ≫ biprod.fst =
      b ≫ kernel.ι (graphKernelMap j F G φ) ≫ biprod.fst := hab
  refine (cancel_mono (kernel.ι (graphKernelMap j F G φ))).1 (biprod.hom_ext _ _ ?_ ?_)
  · rw [Category.assoc, Category.assoc]
    exact hfst
  · refine (cancel_mono ((pushforward j).map φ)).1 ?_
    calc ((a ≫ kernel.ι (graphKernelMap j F G φ)) ≫ biprod.snd) ≫ (pushforward j).map φ
        = a ≫ kernel.ι (graphKernelMap j F G φ) ≫ biprod.fst ≫
            (pullbackPushforwardAdjunction j).unit.app F := by
          rw [graphKernel_ι_comp_fst_unit]
          simp only [Category.assoc]
      _ = b ≫ kernel.ι (graphKernelMap j F G φ) ≫ biprod.fst ≫
            (pullbackPushforwardAdjunction j).unit.app F := by
          rw [← Category.assoc (kernel.ι (graphKernelMap j F G φ)), ← Category.assoc a,
            ← Category.assoc b, hfst]
      _ = ((b ≫ kernel.ι (graphKernelMap j F G φ)) ≫ biprod.snd) ≫ (pushforward j).map φ := by
          rw [graphKernel_ι_comp_fst_unit]
          simp only [Category.assoc]

end AlgebraicGeometry.Scheme.Modules

end
