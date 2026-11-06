module

public import StacksFrontier.Algebra.Module.Adequate.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Flat.Equalizer
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat base change for adequate functors

An adequate module-valued functor on a chosen domain of commutative algebras commutes with
flat base change.

## Main definitions

* `AdequateFunctor.moduleValuedFunctorBaseChangeMap` is the canonical map from the base
  change of the value at an algebra to the value at the target algebra.

## Main results

* `AdequateFunctor.moduleValuedFunctorBaseChangeMap_bijective` asserts that this map is an
  isomorphism for a flat algebra map.

## Implementation notes

The tensor product is written with the target algebra on the left, as in Mathlib's extension of
scalars. The canonical map sends `c ⊗ x` to `c • F(f)(x)`; bijectivity expresses precisely the
isomorphism in the source. The domain functor `ι` allows the site-restricted category
`Alg_A` of Tag 06Z3, as well as the identity domain of all algebras. No values outside
the chosen domain are needed. The domain, morphism, algebra, and module universes are
independent.

## References

* [Stacks Project, Tag 06UW](https://stacks.math.columbia.edu/tag/06UW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe w v u v₁ u₁

namespace AdequateFunctor


-- Evaluating kernels in presheaves requires deep reducible instance search.
/-- The value at `X` of the kernel of `q`, identified with the kernel of the value of `q`,
together with the compatibility of that identification with the kernel inclusion. -/
private noncomputable def evaluatedKernelIsoData
    {A : Type u} [CommRing A]
    {D : Type u₁} [Category.{v₁} D] {ι : D ⥤ CommAlgCat.{max u v} A}
    {F G : ModuleValuedFunctorOn.{max u v w} ι}
    (q : F ⟶ G) (X : (Dᵒᵖ)ᵒᵖ) :
    {e : (PresheafOfModules.evaluation (algebraRingDiagramOn ι) X).obj (kernel q) ≅
        ModuleCat.of (ι.obj X.unop.unop) ((q.app X).hom.ker) //
      e.hom ≫ ModuleCat.ofHom (LinearMap.ker (q.app X).hom).subtype =
        (PresheafOfModules.evaluation (algebraRingDiagramOn ι) X).map (kernel.ι q)} := by
  let E := PresheafOfModules.evaluation.{max u v w} (algebraRingDiagramOn ι) X
  have hEval : IsLimit (E.mapCone (Fork.ofι (kernel.ι q) (kernel.condition q))) :=
    isLimitOfPreserves E (kernelIsKernel q)
  have hEval' : IsLimit (KernelFork.ofι (E.map (kernel.ι q)) (by
      rw [← E.map_comp, kernel.condition, E.map_zero])) :=
    (isLimitMapConeForkEquiv' E (kernel.condition q)) hEval
  let j := hEval'.conePointUniqueUpToIso (ModuleCat.kernelIsLimit (E.map q))
  refine ⟨j, ?_⟩
  have hj := IsLimit.conePointUniqueUpToIso_hom_comp hEval'
    (ModuleCat.kernelIsLimit (E.map q)) WalkingParallelPair.zero
  simp only [ModuleCat.kernelCone] at hj
  change j.hom ≫ ModuleCat.ofHom (LinearMap.ker (q.app X).hom).subtype =
    (PresheafOfModules.evaluation (algebraRingDiagramOn ι) X).map (kernel.ι q) at hj
  exact hj

-- Evaluating kernels in presheaves requires deep reducible instance search.
/-- The value at `X` of the kernel of `q` is the kernel of the value of `q` at `X`. -/
private noncomputable def evaluatedKernelIso
    {A : Type u} [CommRing A]
    {D : Type u₁} [Category.{v₁} D] {ι : D ⥤ CommAlgCat.{max u v} A}
    {F G : ModuleValuedFunctorOn.{max u v w} ι}
    (q : F ⟶ G) (X : (Dᵒᵖ)ᵒᵖ) :
    (PresheafOfModules.evaluation (algebraRingDiagramOn ι) X).obj (kernel q) ≅
      ModuleCat.of (ι.obj X.unop.unop) ((q.app X).hom.ker) :=
  (evaluatedKernelIsoData q X).val

-- Evaluating kernels in presheaves requires deep reducible instance search.
/-- The identification of `AdequateFunctor.evaluatedKernelIso` is compatible with the
kernel inclusion. -/
private theorem evaluatedKernelIso_hom_comp
    {A : Type u} [CommRing A]
    {D : Type u₁} [Category.{v₁} D] {ι : D ⥤ CommAlgCat.{max u v} A}
    {F G : ModuleValuedFunctorOn.{max u v w} ι}
    (q : F ⟶ G) (X : (Dᵒᵖ)ᵒᵖ) :
    (evaluatedKernelIso q X).hom ≫
      ModuleCat.ofHom (LinearMap.ker (q.app X).hom).subtype =
        (PresheafOfModules.evaluation (algebraRingDiagramOn ι) X).map (kernel.ι q) :=
  (evaluatedKernelIsoData q X).property

-- Evaluating kernels in presheaves requires deep reducible instance search.
/-- For an adequate presentation `i`, the value at `X` of the universe lift of `F` is the
kernel of the value of `q` at `X`. -/
private noncomputable def adequateValueKernelIso
    {A : Type u} [CommRing A]
    {D : Type u₁} [Category.{v₁} D] {ι : D ⥤ CommAlgCat.{max u v} A}
    {F : ModuleValuedFunctorOn.{w} ι}
    {F' G : ModuleValuedFunctorOn.{max u v w} ι} (q : F' ⟶ G)
    (i : (presheafOfModulesUliftFunctor.{max u v} (algebraRingDiagramOn ι)).obj F ≅ kernel q)
    (X : (Dᵒᵖ)ᵒᵖ) :
    (PresheafOfModules.evaluation (algebraRingDiagramOn ι) X).obj
        ((presheafOfModulesUliftFunctor.{max u v} (algebraRingDiagramOn ι)).obj F) ≅
      ModuleCat.of (ι.obj X.unop.unop) ((q.app X).hom.ker) :=
  (PresheafOfModules.evaluation (algebraRingDiagramOn ι) X).mapIso i ≪≫ evaluatedKernelIso q X

-- Evaluating kernels in presheaves requires deep reducible instance search.
/-- The identification of `AdequateFunctor.adequateValueKernelIso` is compatible with the
kernel inclusion. -/
private theorem adequateValueKernelIso_hom_comp
    {A : Type u} [CommRing A]
    {D : Type u₁} [Category.{v₁} D] {ι : D ⥤ CommAlgCat.{max u v} A}
    {F : ModuleValuedFunctorOn.{w} ι}
    {F' G : ModuleValuedFunctorOn.{max u v w} ι} (q : F' ⟶ G)
    (i : (presheafOfModulesUliftFunctor.{max u v} (algebraRingDiagramOn ι)).obj F ≅ kernel q)
    (X : (Dᵒᵖ)ᵒᵖ) :
    (adequateValueKernelIso q i X).hom ≫
      ModuleCat.ofHom (LinearMap.ker (q.app X).hom).subtype =
        i.hom.app X ≫ (kernel.ι q).app X := by
  dsimp only [adequateValueKernelIso]
  rw [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, evaluatedKernelIso_hom_comp]
  rfl

-- Evaluating kernels in presheaves requires deep reducible instance search.
/-- For an adequate presentation `i`, the value of `F` at `X` is linearly equivalent to the
kernel of the value of `q` at `X`. -/
private noncomputable def adequateValueKernelEquiv
    {A : Type u} [CommRing A]
    {D : Type u₁} [Category.{v₁} D] {ι : D ⥤ CommAlgCat.{max u v} A}
    {F : ModuleValuedFunctorOn.{w} ι}
    {F' G : ModuleValuedFunctorOn.{max u v w} ι} (q : F' ⟶ G)
    (i : (presheafOfModulesUliftFunctor.{max u v} (algebraRingDiagramOn ι)).obj F ≅ kernel q)
    (X : (Dᵒᵖ)ᵒᵖ) :
    F.obj X ≃ₗ[ι.obj X.unop.unop] ((q.app X).hom.ker) :=
  (ULift.moduleEquiv.{max u v} :
    ULift.{max u v} (F.obj X) ≃ₗ[ι.obj X.unop.unop] F.obj X).symm.trans
      (adequateValueKernelIso q i X).toLinearEquiv

-- Evaluating kernels in presheaves requires deep reducible instance search.
-- The pointwise comparison sends a section to the corresponding kernel element.
/-- The equivalence of `AdequateFunctor.adequateValueKernelEquiv` sends a section to the
element of the kernel named by the adequate presentation. -/
private theorem adequateValueKernelEquiv_coe
    {A : Type u} [CommRing A]
    {D : Type u₁} [Category.{v₁} D] {ι : D ⥤ CommAlgCat.{max u v} A}
    {F : ModuleValuedFunctorOn.{w} ι}
    {F' G : ModuleValuedFunctorOn.{max u v w} ι} (q : F' ⟶ G)
    (i : (presheafOfModulesUliftFunctor.{max u v} (algebraRingDiagramOn ι)).obj F ≅ kernel q)
    (X : (Dᵒᵖ)ᵒᵖ) (x : F.obj X) :
    ((adequateValueKernelEquiv q i X x : LinearMap.ker (q.app X).hom) : F'.obj X) =
      (kernel.ι q).app X (i.hom.app X (ULift.up x)) :=
  congrArg (fun k => k (ULift.up x)) (adequateValueKernelIso_hom_comp q i X)

-- Evaluating kernels in presheaves requires deep reducible instance search.
/-- The equivalence of `AdequateFunctor.adequateValueKernelEquiv` is natural in the
algebra. -/
private theorem adequateValueKernelEquiv_naturality
    {A : Type u} [CommRing A]
    {D : Type u₁} [Category.{v₁} D] {ι : D ⥤ CommAlgCat.{max u v} A}
    {F : ModuleValuedFunctorOn.{w} ι}
    {F' G : ModuleValuedFunctorOn.{max u v w} ι} (q : F' ⟶ G)
    (i : (presheafOfModulesUliftFunctor.{max u v} (algebraRingDiagramOn ι)).obj F ≅ kernel q)
    {X Y : (Dᵒᵖ)ᵒᵖ} (f : X ⟶ Y) (x : F.obj X) :
    (F'.map f) ((adequateValueKernelEquiv q i X x : LinearMap.ker (q.app X).hom) : F'.obj X) =
      ((adequateValueKernelEquiv q i Y ((F.map f) x) :
        LinearMap.ker (q.app Y).hom) : F'.obj Y) := by
  rw [adequateValueKernelEquiv_coe q i X x,
    adequateValueKernelEquiv_coe q i Y (F.map f x)]
  let U := presheafOfModulesUliftFunctor.{max u v} (algebraRingDiagramOn ι)
  have hu : (U.obj F).map f (ULift.up x) = ULift.up ((F.map f) x) :=
    ULift.ext (presheafOfModulesUlift_map_apply (algebraRingDiagramOn ι) F f (ULift.up x))
  have hi := PresheafOfModules.naturality_apply i.hom f (ULift.up x)
  have hk := PresheafOfModules.naturality_apply (kernel.ι q) f
    (i.hom.app X (ULift.up x))
  have h1 : (F'.map f) ((kernel.ι q).app X (i.hom.app X (ULift.up x))) =
      (kernel.ι q).app Y ((kernel q).map f (i.hom.app X (ULift.up x))) := hk.symm
  have h2 : (kernel.ι q).app Y ((kernel q).map f (i.hom.app X (ULift.up x))) =
      (kernel.ι q).app Y (i.hom.app Y (ULift.up ((F.map f) x))) := by
    rw [← hi, hu]
    rfl
  exact h1.trans h2

/-- Cancelling the intermediate base change on `C ⊗[B] (B ⊗[A] M)` sends `c ⊗ z` to the
scalar multiple by `c` of the base change of `z` along `B → C`. -/
private theorem cancelBaseChange_moduleExtensionMap
    {A : Type u} [CommRing A] {B C : CommAlgCat.{max u v} A}
    {M : ModuleCat.{max u v w} A} [Algebra B C]
    [IsScalarTower A B C] [SMulCommClass B C C] (f : B ⟶ C)
    (hAlg : ∀ b : B, algebraMap B C b = f.hom b) (c : C)
    (z : TensorProduct A B M) :
    TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C M (c ⊗ₜ[B] z) =
      c • (moduleExtensionMap A M f z : TensorProduct A C M) := by
  induction z using TensorProduct.induction_on with
  | zero =>
      show 0 = c • (TensorProduct.map f.hom.toLinearMap LinearMap.id 0)
      simp
  | tmul b m =>
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]
      show (b • c) ⊗ₜ[A] m =
        c • (TensorProduct.map f.hom.toLinearMap LinearMap.id (b ⊗ₜ[A] m))
      simp only [TensorProduct.map_tmul, LinearMap.id_apply,
        Algebra.smul_def, TensorProduct.smul_tmul']
      show ((algebraMap B C b) * c) ⊗ₜ[A] m =
        (c * f.hom.toLinearMap b) ⊗ₜ[A] m
      rw [show f.hom.toLinearMap b = f.hom b from rfl, ← hAlg b, mul_comm]
  | add z₁ z₂ h₁ h₂ =>
      show TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C M
          (c ⊗ₜ[B] (z₁ + z₂)) =
        c • (TensorProduct.map f.hom.toLinearMap LinearMap.id (z₁ + z₂))
      change _ = c • (TensorProduct.map f.hom.toLinearMap LinearMap.id z₁) at h₁
      change _ = c • (TensorProduct.map f.hom.toLinearMap LinearMap.id z₂) at h₂
      simpa only [TensorProduct.tmul_add, map_add, smul_add] using
        congrArg₂ (· + ·) h₁ h₂

/-- Two linear maps related by a commuting square of linear equivalences have equivalent
kernels. -/
private def linearMapKerEquivOfCommutingEquivs
    {R : Type*} [CommRing R] {M M' N N' : Type*}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    (f : M →ₗ[R] N) (g : M' →ₗ[R] N') (eM : M ≃ₗ[R] M') (eN : N ≃ₗ[R] N')
    (h : eN.toLinearMap.comp f = g.comp eM.toLinearMap) :
    LinearMap.ker f ≃ₗ[R] LinearMap.ker g :=
  (eM.submoduleMap (LinearMap.ker f)).trans (LinearEquiv.ofEq _ _ (by
    ext y
    rw [Submodule.mem_map_equiv, LinearMap.mem_ker, LinearMap.mem_ker, ← eN.map_eq_zero_iff]
    have := LinearMap.congr_fun h (eM.symm y)
    simp only [LinearEquiv.coe_coe, LinearMap.comp_apply, LinearEquiv.apply_symm_apply] at this
    rw [this]))

/-- For a flat algebra `C` over `B`, cancelling the intermediate base change identifies the
kernel of `g` base changed in two steps with its kernel base changed in one. -/
private noncomputable def cancelBaseChangeKernelEquiv
    {A B C M N : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (g : M →ₗ[A] N) [Module.Flat B C] :
    LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor C C (LinearMap.baseChange B g)) ≃ₗ[C]
      LinearMap.ker (LinearMap.baseChange C g) := by
  let eM := TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C M
  let eN := TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C N
  have h : eN.toLinearMap.comp
      (TensorProduct.AlgebraTensorModule.lTensor C C (LinearMap.baseChange B g)) =
      (LinearMap.baseChange C g).comp eM.toLinearMap := by
    change eN.toLinearMap.comp
        (TensorProduct.AlgebraTensorModule.lTensor C C
          (TensorProduct.AlgebraTensorModule.lTensor B B g)) =
      (TensorProduct.AlgebraTensorModule.lTensor C C g).comp eM.toLinearMap
    exact (TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange A B C (M := C) g).symm
  exact linearMapKerEquivOfCommutingEquivs _ _ eM eN h


/-- The canonical base-change map of a module-valued functor along a map of algebras. -/
public noncomputable def moduleValuedFunctorBaseChangeMap {A : Type u} [CommRing A]
    {D : Type u₁} [Category.{v₁} D] (ι : D ⥤ CommAlgCat.{max u v} A)
    (F : ModuleValuedFunctorOn.{w} ι) {B C : D} (f : B ⟶ C) :
    letI : Algebra (ι.obj B) (ι.obj C) := (ι.map f).hom.toRingHom.toAlgebra;
    (ι.obj C) ⊗[ι.obj B] F.obj (Opposite.op (Opposite.op B)) →ₗ[ι.obj C]
      F.obj (Opposite.op (Opposite.op C)) := by
  letI : Algebra (ι.obj B) (ι.obj C) := (ι.map f).hom.toRingHom.toAlgebra
  letI : Module (ι.obj B) (F.obj (Opposite.op (Opposite.op C))) :=
    Module.compHom _ (algebraMap (ι.obj B) (ι.obj C))
  letI : IsScalarTower (ι.obj B) (ι.obj C) (F.obj (Opposite.op (Opposite.op C))) :=
    IsScalarTower.of_algebraMap_smul fun _ => congrFun rfl
  exact TensorProduct.AlgebraTensorModule.lift {
    toFun := fun c => {
      toFun := fun x => c • F.map f.op.op x
      map_add' := by
        intro x y
        change c • (F.map f.op.op).hom (x + y) =
          c • (F.map f.op.op).hom x + c • (F.map f.op.op).hom y
        rw [map_add (F.map f.op.op).hom, smul_add]
      map_smul' := by
        intro b x
        change c • F.map f.op.op (b • x) = b • (c • F.map f.op.op x)
        rw [F.map_smul]
        change c • ((ι.map f).hom b • F.map f.op.op x) =
          (ι.map f).hom b • (c • F.map f.op.op x)
        exact smul_comm c ((ι.map f).hom b) _ }
    map_add' := by
      intro c d
      ext x
      change (c + d) • F.map f.op.op x =
        c • F.map f.op.op x + d • F.map f.op.op x
      exact add_smul c d _
    map_smul' := by
      intro c d
      ext x
      change (c * d) • F.map f.op.op x = c • (d • F.map f.op.op x)
      exact mul_smul c d _ }

/-- The base-change map sends a pure tensor to the corresponding scalar multiple of the
transition map. -/
@[simp]
public theorem moduleValuedFunctorBaseChangeMap_tmul {A : Type u} [CommRing A]
    {D : Type u₁} [Category.{v₁} D] (ι : D ⥤ CommAlgCat.{max u v} A)
    (F : ModuleValuedFunctorOn.{w} ι) {B C : D} (f : B ⟶ C)
    (c : ι.obj C) (x : F.obj (Opposite.op (Opposite.op B))) :
    letI : Algebra (ι.obj B) (ι.obj C) := (ι.map f).hom.toRingHom.toAlgebra;
    moduleValuedFunctorBaseChangeMap ι F f (c ⊗ₜ[ι.obj B] x) = c • F.map f.op.op x := by
  let : Algebra (ι.obj B) (ι.obj C) := (ι.map f).hom.toRingHom.toAlgebra
  rfl

/-- An adequate functor on a chosen algebra domain commutes with flat base change
along every morphism in that domain. -/
@[stacks 06UW]
public theorem moduleValuedFunctorBaseChangeMap_bijective {A : Type u} [CommRing A]
    {D : Type u₁} [Category.{v₁} D] (ι : D ⥤ CommAlgCat.{max u v} A)
    (F : ModuleValuedFunctorOn.{w} ι) (hF : IsAdequate ι F)
    {B C : D} (f : B ⟶ C) (hf : RingHom.Flat (ι.map f).hom.toRingHom) :
    Function.Bijective (moduleValuedFunctorBaseChangeMap ι F f) := by
  let : Algebra (ι.obj B) (ι.obj C) := (ι.map f).hom.toRingHom.toAlgebra
  have hAlg : ∀ b : ι.obj B, algebraMap (ι.obj B) (ι.obj C) b = (ι.map f).hom b := fun _ => rfl
  let : IsScalarTower A (ι.obj B) (ι.obj C) := IsScalarTower.of_algebraMap_smul fun a c => by
    rw [Algebra.smul_def, Algebra.smul_def]
    show algebraMap (ι.obj B) (ι.obj C) (algebraMap A (ι.obj B) a) * c =
      algebraMap A (ι.obj C) a * c
    rw [hAlg, (ι.map f).hom.commutes]
  have : Module.Flat (ι.obj B) (ι.obj C) := hf
  let : SMulCommClass (ι.obj B) (ι.obj C) (ι.obj C) := ⟨fun b c d => by
    show (algebraMap (ι.obj B) (ι.obj C) b) * (c * d) =
      c * ((algebraMap (ι.obj B) (ι.obj C) b) * d)
    ac_rfl⟩
  obtain ⟨M, N, g, hg⟩ := hF
  obtain ⟨i⟩ := hg
  let q := (moduleExtensionFunctorOn.{max u v w} ι).map g
  let xB : (Dᵒᵖ)ᵒᵖ := Opposite.op (Opposite.op B)
  let xC : (Dᵒᵖ)ᵒᵖ := Opposite.op (Opposite.op C)
  let eB := adequateValueKernelEquiv q i xB
  let eC := adequateValueKernelEquiv q i xC
  let eTotal : (ι.obj C) ⊗[ι.obj B] F.obj xB ≃ₗ[ι.obj C] F.obj xC :=
    (LinearEquiv.baseChange (ι.obj B) (ι.obj C) (F.obj xB) _ eB).trans
      ((LinearMap.tensorKerEquiv (ι.obj C) (ι.obj C) (LinearMap.baseChange (ι.obj B) g.hom)).trans
        ((cancelBaseChangeKernelEquiv (A := A) (B := ι.obj B) (C := ι.obj C) g.hom).trans eC.symm))
  have heq : eTotal.toLinearMap = moduleValuedFunctorBaseChangeMap ι F f := by
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul c x =>
        let y : F.obj xC := (F.map f.op.op).hom x
        show eC.symm _ = c • y
        refine eC.symm_apply_eq.mpr ?_
        rw [map_smul]
        apply Subtype.ext
        have hn := adequateValueKernelEquiv_naturality q i f.op.op x
        show TensorProduct.AlgebraTensorModule.cancelBaseChange A (ι.obj B) (ι.obj C) (ι.obj C) M
            (c ⊗ₜ[ι.obj B] ((eB x : LinearMap.ker (q.app xB).hom) :
              ((moduleExtensionFunctorOn.{max u v w} ι).obj M).obj xB)) =
          c • ((eC ((F.map f.op.op) x) : LinearMap.ker (q.app xC).hom) :
            ((moduleExtensionFunctorOn.{max u v w} ι).obj M).obj xC)
        refine (cancelBaseChange_moduleExtensionMap (M := M) (ι.map f) hAlg c _).trans ?_
        rw [← hn]
        rfl
    | add x y hx hy => simp [map_add, hx, hy]
  exact heq ▸ eTotal.bijective


end AdequateFunctor
