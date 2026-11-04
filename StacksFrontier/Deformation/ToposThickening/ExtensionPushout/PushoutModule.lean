module

public import StacksFrontier.Deformation.ToposThickening.ExtensionPushout.SqZeroExt

/-!
# Pushout along a morphism of thickenings: the pushout extension over the second thickening

The data `PushoutExtensionData` of an `O`-module `F`, kernel modules `K₁`, `K₂` with action maps
`c₁`, `c₂` and a map `κ : K₂ ⟶ K₁` making the square with the induced map of defining ideals
commute; the pushout `F'₂ ⊔_{K₂} K₁` of an extension of `F` by `K₂` over the second thickening,
its short exact sequence and its action map; and the local-section calculus of the pushout and of
`I₁ ⊗_O F` used to twist its action.

See `StacksFrontier.Deformation.ToposThickening.ExtensionPushout` for the overview.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v₂ u₂ t

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.ConcreteCategory.hom CategoryTheory.sheafCompose SheafOfModules.forget
  SheafOfModules.restrictScalars PresheafOfModules.restrictScalars ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' PresheafOfModules.restrictScalarsObj

attribute [local instance] PresheafOfModules.moduleMulOpposite
  PresheafOfModules.isCentralScalar_of_commRing

namespace Deformation.ToposThickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v₂, u₂, max v₂ u₂}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{max v₂ u₂})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{max v₂ u₂} RingCat.{max v₂ u₂})]

section PushoutExtension

variable [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max v₂ u₂}]
  [HasSheafify Y.J AddCommGrpCat.{max v₂ u₂}]
  [HasWeakSheafify Y.J AddCommGrpCat.{max v₂ u₂}]

attribute [local instance] sectionsModuleOfCommRing

namespace MorphismOfFirstOrderThickenings

attribute [local instance] sectionsModuleOverTwo

variable {i : RingedToposHom X Y}

section Bridge

omit [Y.J.WEqualsLocallyBijective AddCommGrpCat.{max v₂ u₂}]
  [HasSheafify Y.J AddCommGrpCat.{max v₂ u₂}]
  [HasWeakSheafify Y.J AddCommGrpCat.{max v₂ u₂}]

/-- A module over the thickened structure sheaf of the first thickening is a module over
`T = O'₂ ⋉ I₁`, through the structure map `q`. -/
@[instance_reducible]
noncomputable def sectionsModuleOverSqZero (D : MorphismOfFirstOrderThickenings i)
    (M : SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (U : Y.Cᵒᵖ) :
    Module (D.sqZeroSections U) (M.val.obj U) :=
  (((SheafOfModules.restrictScalars D.sqZeroProj).obj M).val.obj U).isModule

/-- Local sections of a module over `T = O'₂ ⋉ I₁` form a module over the ring of local
sections of `T`. -/
@[instance_reducible]
noncomputable def sectionsModuleOfSqZeroExt (D : MorphismOfFirstOrderThickenings i)
    (M : SheafOfModules.{max v₂ u₂} D.sqZeroExt) (U : Y.Cᵒᵖ) :
    Module (D.sqZeroSections U) (M.val.obj U) :=
  (M.val.obj U).isModule

/-- The action of the structure sheaf of the second thickening on a module over the base is the
action of the base through the structure map of the second thickening, read in the sheaf of
commutative rings. -/
lemma smul_overTwo_eq (D : MorphismOfFirstOrderThickenings i)
    (M : SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)))
    (U : Y.Cᵒᵖ)
    (a : D.O₂.obj.obj U) (m : M.val.obj U) : a • m = D.fSharp₂.hom.app U a • m := rfl

end Bridge

attribute [local instance] sectionsModuleOverSqZero sectionsModuleOfSqZeroExt

/-- The data of the remark: an `O`-module `F`, kernel modules for the two thickenings with
their prescribed action maps, and a map of kernel modules making the square with the induced
map of defining ideals commute. -/
structure PushoutExtensionData (D : MorphismOfFirstOrderThickenings i) where
  /-- The `O`-module whose extensions are compared. -/
  F : SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
  /-- The kernel module for the first thickening. -/
  K₁ : SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
  /-- The kernel module for the second thickening. -/
  K₂ : SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
  /-- The prescribed action map `c₁ : I₁ ⊗_O F ⟶ K₁`. -/
  c₁ : (PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).obj
      (AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj
        D.first.I.val F.val) ⟶ K₁
  /-- The prescribed action map `c₂ : I₂ ⊗_O F ⟶ K₂`. -/
  c₂ : (PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).obj
      (AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj
        D.second.I.val F.val) ⟶ K₂
  /-- The map `κ : K₂ ⟶ K₁` of kernel modules. -/
  kernelMap : K₂ ⟶ K₁
  /-- The square formed by the two action maps, the map of kernel modules and the induced map
  of defining ideals commutes, read on local pure tensors. -/
  comm : ∀ (U : Y.Cᵒᵖ) (b : D.second.I.val.obj U) (y : F.val.obj U),
    kernelMap.val.app U (c₂.val.app U (((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).unit.app
      (AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj
        D.second.I.val F.val)).app U
        (b ⊗ₜ[(baseRing i).obj.obj U] y))) =
      c₁.val.app U (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).unit.app
        (AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj
          D.first.I.val F.val)).app U
        (D.idealMap.val.app U b ⊗ₜ[(baseRing i).obj.obj U] y))

namespace PushoutExtensionData

variable {D : MorphismOfFirstOrderThickenings i} (dat : D.PushoutExtensionData)
  (E₂ : Abelian.YonedaExtension ((SheafOfModules.restrictScalars D.ringMap₂).obj dat.F)
    ((SheafOfModules.restrictScalars D.ringMap₂).obj dat.K₂) 0)

/-- The map of kernel modules, read over the structure sheaf of the second thickening. -/
noncomputable abbrev kernelMapTwo :
    (SheafOfModules.restrictScalars D.ringMap₂).obj dat.K₂ ⟶
      (SheafOfModules.restrictScalars D.ringMap₂).obj dat.K₁ :=
  (SheafOfModules.restrictScalars D.ringMap₂).map dat.kernelMap

/-- The pushout `F'₂ ⊔_{K₂} K₁` of the middle term of the given extension along the map of
kernel modules, formed in modules over the structure sheaf of the second thickening. -/
noncomputable def pushoutModule :
    SheafOfModules.{max v₂ u₂} (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂) :=
  pushout E₂.f dat.kernelMapTwo

/-- The comparison from the middle term of the given extension to the pushout. -/
noncomputable def pushoutLift : E₂.Z.left ⟶ dat.pushoutModule E₂ :=
  pushout.inl E₂.f dat.kernelMapTwo

/-- The inclusion of the new kernel module into the pushout. -/
noncomputable def pushoutIncl :
    (SheafOfModules.restrictScalars D.ringMap₂).obj dat.K₁ ⟶ dat.pushoutModule E₂ :=
  pushout.inr E₂.f dat.kernelMapTwo

/-- The defining square of the pushout commutes. -/
lemma pushout_comm :
    E₂.f ≫ dat.pushoutLift E₂ = dat.kernelMapTwo ≫ dat.pushoutIncl E₂ :=
  pushout.condition

/-- The quotient map from the pushout onto `F`, induced by the quotient map of the given
extension and the zero map on the new kernel module. -/
noncomputable def pushoutQuot :
    dat.pushoutModule E₂ ⟶ (SheafOfModules.restrictScalars D.ringMap₂).obj dat.F :=
  pushout.desc E₂.g 0 (by rw [yonedaExtension_comp_zero, comp_zero])

/-- The comparison map is compatible with the two quotient maps onto `F`. -/
@[simp] lemma pushoutLift_quot : dat.pushoutLift E₂ ≫ dat.pushoutQuot E₂ = E₂.g :=
  pushout.inl_desc _ _ _

/-- The new kernel module is carried to zero in `F`. -/
@[simp] lemma pushoutIncl_quot : dat.pushoutIncl E₂ ≫ dat.pushoutQuot E₂ = 0 :=
  pushout.inr_desc _ _ _

/-- The inclusion of the new kernel module into the pushout is a monomorphism, being the
pushout of a monomorphism. -/
instance mono_pushoutIncl : Mono (dat.pushoutIncl E₂) :=
  inferInstanceAs (Mono (pushout.inr E₂.f dat.kernelMapTwo))

/-- The quotient map from the pushout onto `F` is an epimorphism. -/
instance epi_pushoutQuot : Epi (dat.pushoutQuot E₂) := by
  have h : Epi (dat.pushoutLift E₂ ≫ dat.pushoutQuot E₂) := by
    rw [dat.pushoutLift_quot E₂]
    exact E₂.epi_g
  exact epi_of_epi (dat.pushoutLift E₂) (dat.pushoutQuot E₂)

/-- The pushout sits in a short exact sequence `0 → K₁ → F'₂ ⊔_{K₂} K₁ → F → 0`: a local
section of the pushout is, up to refinement, a sum of a section coming from the middle term of
the given extension and one coming from the new kernel module. -/
@[sga "3 III 4.1" "special case"]
lemma pushout_shortExact :
    (ShortComplex.mk (dat.pushoutIncl E₂) (dat.pushoutQuot E₂)
      (dat.pushoutIncl_quot E₂)).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ (dat.mono_pushoutIncl E₂) (dat.epi_pushoutQuot E₂)
  rw [ShortComplex.exact_iff_exact_up_to_refinements]
  intro A x hx
  change x ≫ dat.pushoutQuot E₂ = 0 at hx
  obtain ⟨A', π, hπ, x₂, x₃, heq⟩ :=
    (IsPushout.of_hasPushout E₂.f dat.kernelMapTwo).hom_eq_add_up_to_refinements x
  change π ≫ x = x₂ ≫ dat.pushoutLift E₂ + x₃ ≫ dat.pushoutIncl E₂ at heq
  have h2 : x₂ ≫ E₂.g = 0 := by
    have h : π ≫ (x ≫ dat.pushoutQuot E₂) = x₂ ≫ E₂.g := by
      rw [← Category.assoc, heq, Preadditive.add_comp, Category.assoc, Category.assoc,
        dat.pushoutLift_quot E₂, dat.pushoutIncl_quot E₂, comp_zero, add_zero]
    rw [hx, comp_zero] at h
    exact h.symm
  obtain ⟨A'', π', hπ', k, hk⟩ :=
    (yonedaExtension_shortExact E₂).exact.exact_up_to_refinements x₂ h2
  change π' ≫ x₂ = k ≫ E₂.f at hk
  refine ⟨A'', π' ≫ π, inferInstance, k ≫ dat.kernelMapTwo + π' ≫ x₃, ?_⟩
  change (π' ≫ π) ≫ x = (k ≫ dat.kernelMapTwo + π' ≫ x₃) ≫ dat.pushoutIncl E₂
  calc (π' ≫ π) ≫ x = π' ≫ (π ≫ x) := Category.assoc _ _ _
    _ = π' ≫ (x₂ ≫ dat.pushoutLift E₂ + x₃ ≫ dat.pushoutIncl E₂) := congrArg _ heq
    _ = π' ≫ (x₂ ≫ dat.pushoutLift E₂) + π' ≫ (x₃ ≫ dat.pushoutIncl E₂) :=
        Preadditive.comp_add _ _ _ _ _ _
    _ = (π' ≫ x₂) ≫ dat.pushoutLift E₂ + (π' ≫ x₃) ≫ dat.pushoutIncl E₂ :=
        congrArg₂ (· + ·) (Category.assoc π' x₂ (dat.pushoutLift E₂)).symm
          (Category.assoc π' x₃ (dat.pushoutIncl E₂)).symm
    _ = (k ≫ E₂.f) ≫ dat.pushoutLift E₂ + (π' ≫ x₃) ≫ dat.pushoutIncl E₂ :=
        congrArg (fun z => z ≫ dat.pushoutLift E₂ + (π' ≫ x₃) ≫ dat.pushoutIncl E₂) hk
    _ = k ≫ (E₂.f ≫ dat.pushoutLift E₂) + (π' ≫ x₃) ≫ dat.pushoutIncl E₂ :=
        congrArg (fun z => z + (π' ≫ x₃) ≫ dat.pushoutIncl E₂)
          (Category.assoc k E₂.f (dat.pushoutLift E₂))
    _ = k ≫ (dat.kernelMapTwo ≫ dat.pushoutIncl E₂) +
          (π' ≫ x₃) ≫ dat.pushoutIncl E₂ :=
        congrArg (fun z => k ≫ z + (π' ≫ x₃) ≫ dat.pushoutIncl E₂) (dat.pushout_comm E₂)
    _ = (k ≫ dat.kernelMapTwo) ≫ dat.pushoutIncl E₂ +
          (π' ≫ x₃) ≫ dat.pushoutIncl E₂ :=
        congrArg (fun z => z + (π' ≫ x₃) ≫ dat.pushoutIncl E₂)
          (Category.assoc k dat.kernelMapTwo (dat.pushoutIncl E₂)).symm
    _ = (k ≫ dat.kernelMapTwo + π' ≫ x₃) ≫ dat.pushoutIncl E₂ :=
        (Preadditive.add_comp _ _ _ _ _ _).symm

/-- The pushout, as an extension of `F` by `K₁` over the second thickening. -/
noncomputable def pushoutExtension :
    Abelian.YonedaExtension ((SheafOfModules.restrictScalars D.ringMap₂).obj dat.F)
      ((SheafOfModules.restrictScalars D.ringMap₂).obj dat.K₁) 0 where
  Z := ComposableArrows.mk₀ (dat.pushoutModule E₂)
  f := dat.pushoutIncl E₂
  g := dat.pushoutQuot E₂
  mono_f := (dat.pushout_shortExact E₂).mono_f
  exact := ComposableArrows.exact₁ _
  exact_g := (dat.pushout_shortExact E₂).exact.exact_toComposableArrows
  epi_g := (dat.pushout_shortExact E₂).epi_g

/-- The canonical action map of the pushout extension is the prescribed action map of the
second thickening followed by the map of kernel modules: the two agree after applying the
monomorphism `K₁ ⟶ F'₂ ⊔_{K₂} K₁`, by the defining square of the pushout and the
characterisation of the action map of the given extension, and a local section of `F` is
locally the image of a section of the middle term. -/
lemma pushoutExtension_actionMap
    (hE₂ : (extensionActionMap D.second E₂).1 = dat.c₂) :
    (extensionActionMap D.second (dat.pushoutExtension E₂)).1 = dat.c₂ ≫ dat.kernelMap := by
  have hls : Presheaf.IsLocallySurjective Y.J
      (show E₂.Z.left.val.presheaf ⟶ dat.F.val.presheaf from
        (PresheafOfModules.toPresheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂).obj).map E₂.g.val) :=
    sheafModule_epi_locallySurjective E₂.g
  have hmono : Mono (dat.pushoutIncl E₂).val :=
    (SheafOfModules.forget
      (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂)).map_mono (dat.pushoutIncl E₂)
  refine tensorSheaf_hom_ext_of_locallySurjective (baseRing i)
    (M := D.second.I) (N := dat.F) (P := dat.K₁) (Q := E₂.Z.left.val.presheaf)
    ((PresheafOfModules.toPresheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf D.O₂).obj).map E₂.g.val) ?_
  intro U b x
  change (extensionActionMap D.second (dat.pushoutExtension E₂)).1.val.app U
      (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).unit.app
        (PresheafOfModules.tensorObj D.second.I.val dat.F.val)).app U
        (b ⊗ₜ[(baseRing i).obj.obj U] E₂.g.val.app U x)) =
    (dat.c₂ ≫ dat.kernelMap).val.app U
      (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).unit.app
        (PresheafOfModules.tensorObj D.second.I.val dat.F.val)).app U
        (b ⊗ₜ[(baseRing i).obj.obj U] E₂.g.val.app U x))
  refine PresheafOfModules.injective_of_mono (dat.pushoutIncl E₂).val U ?_
  set τ : ((PresheafOfModules.sheafification
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).obj
      (AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj
        D.second.I.val dat.F.val)).val.obj U :=
    ((PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).unit.app
      (PresheafOfModules.tensorObj D.second.I.val dat.F.val)).app U
      (b ⊗ₜ[(baseRing i).obj.obj U] E₂.g.val.app U x) with hτ
  have hq : (dat.pushoutQuot E₂).val.app U ((dat.pushoutLift E₂).val.app U x) =
      E₂.g.val.app U x :=
    congrArg (fun z : E₂.Z.left ⟶ (SheafOfModules.restrictScalars D.ringMap₂).obj dat.F =>
      z.val.app U x) (dat.pushoutLift_quot E₂)
  have step1 : (dat.pushoutIncl E₂).val.app U
      ((extensionActionMap D.second (dat.pushoutExtension E₂)).1.val.app U τ) =
      D.inclTwo U b • (dat.pushoutLift E₂).val.app U x := by
    refine Eq.trans ?_ ((extensionActionMap D.second (dat.pushoutExtension E₂)).2 U b
      ((dat.pushoutLift E₂).val.app U x))
    exact congrArg (fun z : dat.F.val.obj U => (dat.pushoutIncl E₂).val.app U
      ((extensionActionMap D.second (dat.pushoutExtension E₂)).1.val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).unit.app
          (PresheafOfModules.tensorObj D.second.I.val dat.F.val)).app U
          (b ⊗ₜ[(baseRing i).obj.obj U] z)))) hq.symm
  have step2 : (dat.pushoutLift E₂).val.app U (D.inclTwo U b • x) =
      D.inclTwo U b • (dat.pushoutLift E₂).val.app U x :=
    map_smul ((dat.pushoutLift E₂).val.app U).hom _ _
  have step3 : D.inclTwo U b • x = E₂.f.val.app U (dat.c₂.val.app U τ) := by
    have hact := (extensionActionMap D.second E₂).2 U b x
    rw [hE₂] at hact
    exact hact.symm
  have step4 : (dat.pushoutLift E₂).val.app U (E₂.f.val.app U (dat.c₂.val.app U τ)) =
      (dat.pushoutIncl E₂).val.app U (dat.kernelMap.val.app U (dat.c₂.val.app U τ)) :=
    congrArg (fun z : (SheafOfModules.restrictScalars D.ringMap₂).obj dat.K₂ ⟶
      dat.pushoutModule E₂ => z.val.app U (dat.c₂.val.app U τ)) (dat.pushout_comm E₂)
  rw [step1, ← step2, step3, step4]
  rfl

/-- The image in `F` of a local section of the pushout. -/
noncomputable def quotSection (U : Y.Cᵒᵖ) (p : (dat.pushoutModule E₂).val.obj U) :
    dat.F.val.obj U :=
  (dat.pushoutQuot E₂).val.app U p

/-- The image in the pushout of a local section of the new kernel module. -/
noncomputable def inclSection (U : Y.Cᵒᵖ) (k : dat.K₁.val.obj U) :
    (dat.pushoutModule E₂).val.obj U :=
  (dat.pushoutIncl E₂).val.app U k

/-- The quotient map onto `F` respects differences of sections. -/
lemma quotSection_sub (U : Y.Cᵒᵖ) (p p' : (dat.pushoutModule E₂).val.obj U) :
    dat.quotSection E₂ U (p - p') = dat.quotSection E₂ U p - dat.quotSection E₂ U p' :=
  map_sub ((dat.pushoutQuot E₂).val.app U).hom p p'

/-- The quotient map onto `F` is additive on sections. -/
lemma quotSection_add (U : Y.Cᵒᵖ) (p p' : (dat.pushoutModule E₂).val.obj U) :
    dat.quotSection E₂ U (p + p') = dat.quotSection E₂ U p + dat.quotSection E₂ U p' :=
  map_add ((dat.pushoutQuot E₂).val.app U).hom p p'

/-- The quotient map onto `F` is linear over the structure sheaf of the second thickening. -/
lemma quotSection_smul (U : Y.Cᵒᵖ) (a : D.O₂.obj.obj U)
    (p : (dat.pushoutModule E₂).val.obj U) :
    dat.quotSection E₂ U (a • p) = D.fSharp₂.hom.app U a • dat.quotSection E₂ U p :=
  map_smul ((dat.pushoutQuot E₂).val.app U).hom a p

/-- The quotient map onto `F` kills the new kernel module. -/
lemma quotSection_inclSection (U : Y.Cᵒᵖ) (k : dat.K₁.val.obj U) :
    dat.quotSection E₂ U (dat.inclSection E₂ U k) = 0 :=
  congrArg (fun z : (SheafOfModules.restrictScalars D.ringMap₂).obj dat.K₁ ⟶
    (SheafOfModules.restrictScalars D.ringMap₂).obj dat.F => z.val.app U k)
    (dat.pushoutIncl_quot E₂)

/-- The quotient map onto `F` commutes with restriction. -/
lemma quotSection_restrict {U V : Y.Cᵒᵖ} (g : U ⟶ V)
    (p : (dat.pushoutModule E₂).val.obj U) :
    dat.quotSection E₂ V ((dat.pushoutModule E₂).val.map g p) =
      dat.F.val.map g (dat.quotSection E₂ U p) :=
  PresheafOfModules.naturality_apply (dat.pushoutQuot E₂).val g p

/-- The inclusion of the new kernel module is additive. -/
lemma inclSection_add (U : Y.Cᵒᵖ) (k k' : dat.K₁.val.obj U) :
    dat.inclSection E₂ U (k + k') = dat.inclSection E₂ U k + dat.inclSection E₂ U k' :=
  map_add ((dat.pushoutIncl E₂).val.app U).hom k k'

/-- The inclusion of the new kernel module kills zero. -/
lemma inclSection_zero (U : Y.Cᵒᵖ) : dat.inclSection E₂ U 0 = 0 :=
  map_zero ((dat.pushoutIncl E₂).val.app U).hom

/-- The inclusion of the new kernel module is linear over the structure sheaf of the second
thickening. -/
lemma inclSection_smul (U : Y.Cᵒᵖ) (a : D.O₂.obj.obj U) (k : dat.K₁.val.obj U) :
    dat.inclSection E₂ U (D.fSharp₂.hom.app U a • k) = a • dat.inclSection E₂ U k :=
  map_smul ((dat.pushoutIncl E₂).val.app U).hom a k

/-- The inclusion of the new kernel module respects differences. -/
lemma inclSection_sub (U : Y.Cᵒᵖ) (k k' : dat.K₁.val.obj U) :
    dat.inclSection E₂ U (k - k') = dat.inclSection E₂ U k - dat.inclSection E₂ U k' :=
  map_sub ((dat.pushoutIncl E₂).val.app U).hom k k'

/-- The inclusion of the new kernel module commutes with restriction. -/
lemma inclSection_restrict {U V : Y.Cᵒᵖ} (g : U ⟶ V) (k : dat.K₁.val.obj U) :
    dat.inclSection E₂ V (dat.K₁.val.map g k) =
      (dat.pushoutModule E₂).val.map g (dat.inclSection E₂ U k) :=
  PresheafOfModules.naturality_apply (dat.pushoutIncl E₂).val g k

section TensorSections

omit [HasSheafify Y.J AddCommGrpCat.{max v₂ u₂}]

/-- The image in `I₁ ⊗_O F` of a pure tensor of local sections. -/
noncomputable def tensorMk (U : Y.Cᵒᵖ) (m : D.first.I.val.obj U) (y : dat.F.val.obj U) :
    ((PresheafOfModules.sheafification
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).obj
        (AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj
          D.first.I.val dat.F.val)).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).unit.app
    (PresheafOfModules.tensorObj D.first.I.val dat.F.val)).app U (m ⊗ₜ[(baseRing i).obj.obj U] y)

/-- A pure tensor is additive in its ideal factor. -/
lemma tensorMk_add_left (U : Y.Cᵒᵖ) (m m' : D.first.I.val.obj U) (y : dat.F.val.obj U) :
    dat.tensorMk U (m + m') y = dat.tensorMk U m y + dat.tensorMk U m' y := by
  simp only [tensorMk, TensorProduct.add_tmul]
  exact map_add _ _ _

/-- A pure tensor is additive in its module factor. -/
lemma tensorMk_add_right (U : Y.Cᵒᵖ) (m : D.first.I.val.obj U) (y y' : dat.F.val.obj U) :
    dat.tensorMk U m (y + y') = dat.tensorMk U m y + dat.tensorMk U m y' := by
  simp only [tensorMk, TensorProduct.tmul_add]
  exact map_add _ _ _

/-- A pure tensor with zero ideal factor vanishes. -/
lemma tensorMk_zero_left (U : Y.Cᵒᵖ) (y : dat.F.val.obj U) :
    dat.tensorMk U 0 y = 0 := by
  simp only [tensorMk, TensorProduct.zero_tmul]
  exact map_zero _

/-- A scalar on the ideal factor of a pure tensor comes out. -/
lemma tensorMk_smul_left (U : Y.Cᵒᵖ) (r : (baseRing i).obj.obj U)
    (m : D.first.I.val.obj U) (y : dat.F.val.obj U) :
    dat.tensorMk U (r • m) y = r • dat.tensorMk U m y := by
  simp only [tensorMk, ← TensorProduct.smul_tmul']
  exact map_smul _ _ _

/-- A pure tensor respects differences in its module factor. -/
lemma tensorMk_sub_right (U : Y.Cᵒᵖ) (m : D.first.I.val.obj U) (y y' : dat.F.val.obj U) :
    dat.tensorMk U m (y - y') = dat.tensorMk U m y - dat.tensorMk U m y' := by
  simp only [tensorMk, TensorProduct.tmul_sub]
  exact map_sub _ _ _

/-- A pure tensor with zero module factor vanishes. -/
lemma tensorMk_zero_right (U : Y.Cᵒᵖ) (m : D.first.I.val.obj U) :
    dat.tensorMk U m 0 = 0 := by
  simp only [tensorMk, TensorProduct.tmul_zero]
  exact map_zero _

/-- A scalar on the module factor of a pure tensor comes out. -/
lemma tensorMk_smul_right (U : Y.Cᵒᵖ) (r : (baseRing i).obj.obj U)
    (m : D.first.I.val.obj U) (y : dat.F.val.obj U) :
    dat.tensorMk U m (r • y) = r • dat.tensorMk U m y := by
  simp only [tensorMk, TensorProduct.tmul_smul]
  exact map_smul _ _ _

/-- A pure tensor commutes with restriction. -/
lemma tensorMk_restrict {U V : Y.Cᵒᵖ} (g : U ⟶ V) (m : D.first.I.val.obj U)
    (y : dat.F.val.obj U) :
    ((PresheafOfModules.sheafification
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).obj
        (AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj
          D.first.I.val dat.F.val)).val.map g (dat.tensorMk U m y) =
      dat.tensorMk V (D.first.I.val.map g m) (dat.F.val.map g y) :=
  tensorSheafificationUnit_naturality D.first.I dat.F g m y

/-- The prescribed action map of the first thickening is additive on sections. -/
lemma c₁_add (U : Y.Cᵒᵖ)
    (t t' : ((PresheafOfModules.sheafification
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).obj
        (AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj
          D.first.I.val dat.F.val)).val.obj U) :
    dat.c₁.val.app U (t + t') = dat.c₁.val.app U t + dat.c₁.val.app U t' :=
  map_add (dat.c₁.val.app U).hom t t'

/-- The prescribed action map of the first thickening kills zero. -/
lemma c₁_zero (U : Y.Cᵒᵖ) :
    dat.c₁.val.app U (0 : ((PresheafOfModules.sheafification
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).obj
        (AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj
          D.first.I.val dat.F.val)).val.obj U) = 0 :=
  map_zero (dat.c₁.val.app U).hom

/-- The prescribed action map of the first thickening respects differences. -/
lemma c₁_sub (U : Y.Cᵒᵖ)
    (t t' : ((PresheafOfModules.sheafification
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).obj
        (AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj
          D.first.I.val dat.F.val)).val.obj U) :
    dat.c₁.val.app U (t - t') = dat.c₁.val.app U t - dat.c₁.val.app U t' :=
  map_sub (dat.c₁.val.app U).hom t t'

/-- The prescribed action map of the first thickening is linear over the base. -/
lemma c₁_smul (U : Y.Cᵒᵖ) (r : (baseRing i).obj.obj U)
    (t : ((PresheafOfModules.sheafification
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).obj
        (AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj
          D.first.I.val dat.F.val)).val.obj U) :
    dat.c₁.val.app U (r • t) = r • dat.c₁.val.app U t :=
  map_smul (dat.c₁.val.app U).hom r t

/-- The prescribed action map of the first thickening commutes with restriction. -/
lemma c₁_restrict {U V : Y.Cᵒᵖ} (g : U ⟶ V)
    (t : ((PresheafOfModules.sheafification
        (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).obj
        (AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj
          D.first.I.val dat.F.val)).val.obj U) :
    dat.c₁.val.app V
        (((PresheafOfModules.sheafification
            (R := Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i))
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i)).obj)).obj
            (AlgebraicGeometry.SheafOfModules.PresheafOfModules.tensorObj
              D.first.I.val dat.F.val)).val.map g t) =
      dat.K₁.val.map g (dat.c₁.val.app U t) :=
  PresheafOfModules.naturality_apply dat.c₁.val g t

end TensorSections

end PushoutExtensionData

end MorphismOfFirstOrderThickenings

end PushoutExtension

end Deformation.ToposThickening

end
