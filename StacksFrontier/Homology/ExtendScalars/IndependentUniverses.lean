module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Extension of scalars between rings in independent universes

Let `f : R →+* S` be a homomorphism of commutative rings whose source and target are allowed to
live in different universes, and let `ModuleCat.extendScalars f` be the induced functor
`ModuleCat.{w} R ⥤ ModuleCat.{max v w} S`, `M ↦ S ⊗[R] M`.

This file records the exactness of that functor — it always preserves cokernels, and preserves
kernels when `f` is flat — together with the two identifications of a base-changed module that
a descent argument along a ring map needs: the base change of the regular module and the base
change of a module restricted along a ring isomorphism.

`StacksFrontier.Homology.ExtendScalars.Flat` proves the same exactness statements for a ring map
whose source and target share a universe; neither form specializes to the other, because there
the module universe is tied to the common ring universe.

## Main definitions

* `ModuleCat.extendScalarsHomologyIso` — flat extension of scalars commutes with the cohomology
  of a cochain complex.
* `ModuleCat.extendScalarsULiftIso` — the base change of the regular module `ULift R` is the
  regular module `S`.
* `ModuleCat.extendScalarsRestrictScalarsIso` — along a ring isomorphism, extension of scalars
  undoes restriction of scalars.

## Main results

* `ModuleCat.extendScalars_preservesKernel_of_flat` and
  `ModuleCat.extendScalars_preservesFiniteLimits_of_flat` — left exactness under flatness.
* `ModuleCat.extendScalars_preservesCokernel` and
  `ModuleCat.extendScalars_preservesFiniteColimits` — right exactness, unconditionally.
* `ModuleCat.isZero_of_isZero_extendScalars` — a faithfully flat extension reflects vanishing.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

universe u v w

namespace ModuleCat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Extension of scalars preserves zero morphisms, whatever the universes of the two rings and
of the module. -/
instance extendScalars_preservesZeroMorphisms (f : R →+* S) :
    (extendScalars.{u, v, w} f).PreservesZeroMorphisms :=
  ⟨fun X Y => by
    ext m
    change (1 : S) ⊗ₜ[R,f] ((0 : X →ₗ[R] Y) m) = 0
    simp⟩

/-- Extension of scalars along a flat ring map preserves the kernel of every morphism. -/
theorem extendScalars_preservesKernel_of_flat (f : R →+* S) (hf : f.Flat)
    {X Y : ModuleCat.{w} R} (g : X ⟶ Y) :
    PreservesLimit (parallelPair g 0) (extendScalars.{u, v, w} f) := by
  let _ := f.toAlgebra
  have : Module.Flat R S := hf
  let F : ModuleCat.{w} R ⥤ ModuleCat.{max v w} S := extendScalars.{u, v, w} f
  let ι : (kernelCone g).pt ⟶ X := Fork.ι (kernelCone g)
  have hcomp0 : ι ≫ g = 0 := KernelFork.condition (kernelCone g)
  have hFι : ⇑(Hom.hom (F.map ι)) = ⇑(LinearMap.lTensor S (Hom.hom ι)) := rfl
  have hFg : ⇑(Hom.hom (F.map g)) = ⇑(LinearMap.lTensor S (Hom.hom g)) := rfl
  have hinjF : Function.Injective ⇑(Hom.hom (F.map ι)) := by
    rw [hFι]
    exact Module.Flat.lTensor_preserves_injective_linearMap (Hom.hom ι) Subtype.coe_injective
  have hexF : Function.Exact ⇑(Hom.hom (F.map ι)) ⇑(Hom.hom (F.map g)) := by
    rw [hFι, hFg]
    exact Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map (Hom.hom g))
  have hFcomp : F.map ι ≫ F.map g = 0 := by rw [← F.map_comp, hcomp0, F.map_zero]
  have wF : F.map ι ≫ F.map g = F.map ι ≫ 0 := hFcomp.trans comp_zero.symm
  have hker : (Hom.hom (F.map g)).ker = (Hom.hom (F.map ι)).range := hexF.linearMap_ker_eq
  have hmem : ∀ c, (Hom.hom (F.map ι)) c ∈ (Hom.hom (F.map g)).ker := by
    intro c
    rw [hker]
    exact LinearMap.mem_range_self _ c
  let φ := LinearMap.codRestrict (Hom.hom (F.map g)).ker (Hom.hom (F.map ι)) hmem
  have hφinj : Function.Injective φ := fun a b hab => hinjF (congrArg Subtype.val hab)
  have hφsurj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [hker] at hy
    obtain ⟨c, hc⟩ := hy
    exact ⟨c, Subtype.ext hc⟩
  let e := LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  have keyFork : IsLimit (Fork.ofι (F.map ι) wF) := by
    refine IsLimit.ofIsoLimit (kernelIsLimit (F.map g)) ?_
    refine Fork.ext e.toModuleIso.symm ?_
    refine hom_ext (LinearMap.ext fun y => ?_)
    change (Hom.hom (F.map ι)) (e.symm y) = y.val
    exact congrArg Subtype.val (e.apply_symm_apply y)
  have w0 : ι ≫ g = ι ≫ 0 := hcomp0.trans comp_zero.symm
  have key2 : IsLimit (F.mapCone (Fork.ofι ι w0)) := by
    refine (isLimitMapConeForkEquiv F w0).symm ?_
    convert keyFork using 2 <;> exact F.map_zero _ _
  have hforkiso : kernelCone g ≅ Fork.ofι ι w0 := Fork.ext (Iso.refl _) (by simp [ι])
  exact preservesLimit_of_preserves_limit_cone (kernelIsLimit g) <|
    IsLimit.ofIsoLimit key2 ((Cone.functoriality _ F).mapIso hforkiso.symm)

/-- Extension of scalars along a flat ring map preserves finite limits. -/
theorem extendScalars_preservesFiniteLimits_of_flat (f : R →+* S) (hf : f.Flat) :
    PreservesFiniteLimits (extendScalars.{u, v, w} f) := by
  have : ∀ {X Y : ModuleCat.{w} R}, (g : X ⟶ Y) →
      PreservesLimit (parallelPair g 0) (extendScalars.{u, v, w} f) :=
    fun {_ _} g => extendScalars_preservesKernel_of_flat f hf g
  exact Functor.preservesFiniteLimits_of_preservesKernels (extendScalars.{u, v, w} f)

/-- Extension of scalars preserves the cokernel of every morphism: the tensor product is right
exact, with no flatness hypothesis. -/
theorem extendScalars_preservesCokernel (f : R →+* S) {X Y : ModuleCat.{w} R} (g : X ⟶ Y) :
    PreservesColimit (parallelPair g 0) (extendScalars.{u, v, w} f) := by
  let _ := f.toAlgebra
  let F : ModuleCat.{w} R ⥤ ModuleCat.{max v w} S := extendScalars.{u, v, w} f
  let π : Y ⟶ (cokernelCocone g).pt := Cofork.π (cokernelCocone g)
  have hcomp0 : g ≫ π = 0 := CokernelCofork.condition (cokernelCocone g)
  have hex : Function.Exact ⇑(Hom.hom g) ⇑(Hom.hom π) := by
    apply LinearMap.exact_iff.mpr
    change ((Hom.hom g).range).mkQ.ker = (Hom.hom g).range
    exact Submodule.ker_mkQ _
  have hsurj : Function.Surjective ⇑(Hom.hom π) := Submodule.mkQ_surjective _
  have hFg : ⇑(Hom.hom (F.map g)) = ⇑(LinearMap.lTensor S (Hom.hom g)) := rfl
  have hFπ : ⇑(Hom.hom (F.map π)) = ⇑(LinearMap.lTensor S (Hom.hom π)) := rfl
  have hexF : Function.Exact ⇑(Hom.hom (F.map g)) ⇑(Hom.hom (F.map π)) := by
    rw [hFg, hFπ]
    exact lTensor_exact S hex hsurj
  have hsurjF : Function.Surjective ⇑(Hom.hom (F.map π)) := by
    rw [hFπ]
    exact LinearMap.lTensor_surjective S hsurj
  have hFcomp : F.map g ≫ F.map π = 0 := by rw [← F.map_comp, hcomp0, F.map_zero]
  have wF : F.map g ≫ F.map π = 0 ≫ F.map π := hFcomp.trans zero_comp.symm
  have keyCofork : IsColimit (Cofork.ofπ (F.map π) wF) :=
    isColimitCokernelCofork (F.map g) (F.map π) hexF hsurjF
  have w0 : g ≫ π = 0 ≫ π := hcomp0.trans zero_comp.symm
  have key2 : IsColimit (F.mapCocone (Cofork.ofπ π w0)) := by
    refine (isColimitMapCoconeCoforkEquiv F w0).symm ?_
    convert keyCofork using 2 <;> exact F.map_zero _ _
  have hcoforkiso : cokernelCocone g ≅ Cofork.ofπ π w0 := Cofork.ext (Iso.refl _) (by simp [π])
  exact preservesColimit_of_preserves_colimit_cocone (cokernelIsColimit g) <|
    IsColimit.ofIsoColimit key2 ((Cocone.functoriality _ F).mapIso hcoforkiso.symm)

/-- Extension of scalars preserves finite colimits. -/
theorem extendScalars_preservesFiniteColimits (f : R →+* S) :
    PreservesFiniteColimits (extendScalars.{u, v, w} f) := by
  have : ∀ {X Y : ModuleCat.{w} R}, (g : X ⟶ Y) →
      PreservesColimit (parallelPair g 0) (extendScalars.{u, v, w} f) :=
    fun {_ _} g => extendScalars_preservesCokernel f g
  exact Functor.preservesFiniteColimits_of_preservesCokernels (extendScalars.{u, v, w} f)

/-- Flat extension of scalars commutes with the cohomology of a cochain complex. -/
def extendScalarsHomologyIso (f : R →+* S) (hf : f.Flat)
    (K : CochainComplex (ModuleCat.{w} R) ℤ) (i : ℤ) :
    (((extendScalars.{u, v, w} f).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology i ≅
      (extendScalars.{u, v, w} f).obj (K.homology i) := by
  let F : ModuleCat.{w} R ⥤ ModuleCat.{max v w} S := extendScalars.{u, v, w} f
  letI : PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat.{u, v, w} f hf
  letI : PreservesFiniteColimits F := extendScalars_preservesFiniteColimits.{u, v, w} f
  letI : F.PreservesHomology := Functor.preservesHomologyOfExact F
  exact (K.sc i).mapHomologyIso F

/-- A faithfully flat extension of scalars reflects vanishing of a module. -/
theorem isZero_of_isZero_extendScalars (f : R →+* S) (hf : f.FaithfullyFlat)
    (M : ModuleCat.{w} R) (h : IsZero ((extendScalars.{u, v, w} f).obj M)) : IsZero M := by
  rw [isZero_iff_subsingleton] at h ⊢
  algebraize [f]
  change Subsingleton (TensorProduct R S M) at h
  exact Module.FaithfullyFlat.lTensor_reflects_triviality R S M

/-- The base change along `f : R →+* S` of the regular `R`-module, universe-lifted, is the
regular `S`-module. -/
def extendScalarsULiftIso {R : Type u} {S : Type (max u v)} [CommRing R] [CommRing S]
    (f : R →+* S) :
    (extendScalars.{u, max u v, max u v} f).obj (of R (ULift.{max u v} R)) ≅ of S S := by
  letI : Algebra R S := f.toAlgebra
  let X := (restrictScalars f).obj (of S S)
  letI : Module S X := inferInstance
  letI : SMulCommClass R S X := sMulCommClass_mk f X
  letI : IsScalarTower R S X := ⟨fun r s x => by
    change (f r * s) • x = f r • (s • x)
    exact mul_smul (f r) s x⟩
  letI : IsScalarTower R S S := IsScalarTower.of_algebraMap_eq' rfl
  let e : ULift.{max u v} R ≃ₗ[R] R := ULift.moduleEquiv
  let e' : TensorProduct R X (ULift.{max u v} R) ≃ₗ[S] TensorProduct R X R :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S X) e
  exact LinearEquiv.toModuleIso (e'.trans (TensorProduct.AlgebraTensorModule.rid R S S))

/-- Along a ring isomorphism `e : R ≃+* S`, extension of scalars undoes restriction of
scalars. -/
def extendScalarsRestrictScalarsIso (e : R ≃+* S) (M : ModuleCat.{max u v w} S) :
    (extendScalars.{u, v, max u v w} e.toRingHom).obj
      ((restrictScalars.{max u v w, u, v} e.toRingHom).obj M) ≅ M := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  letI : Module S R := Module.compHom R e.symm.toRingHom
  letI : IsScalarTower S R S := ⟨fun a r s => by
    change e (e.symm a * r) * s = a * (e r * s)
    rw [map_mul, e.apply_symm_apply, mul_assoc]⟩
  letI : Module R M := Module.compHom M e.toRingHom
  letI : IsScalarTower S R M := ⟨fun a r m => by
    change e (e.symm a * r) • m = a • (e r • m)
    rw [map_mul, e.apply_symm_apply, mul_smul]⟩
  letI : IsScalarTower R S M := ⟨fun r s x => by
    change (e r * s) • x = e r • (s • x)
    rw [mul_smul]⟩
  letI : IsScalarTower R S S := IsScalarTower.of_algebraMap_eq' rfl
  let F : S →ₗ[S] M →ₗ[R] M :=
    { toFun := fun s => (LinearMap.lsmul S M s).restrictScalars R
      map_add' a b := by
        ext x
        simp
      map_smul' a s := by
        ext x
        simp [mul_smul] }
  let φ : TensorProduct R S M →ₗ[S] M := TensorProduct.AlgebraTensorModule.lift F
  let ψ : M →ₗ[S] TensorProduct R S M :=
    { toFun := fun m => (1 : S) ⊗ₜ[R] m
      map_add' x y := TensorProduct.tmul_add _ x y
      map_smul' a m := by simp }
  let E : TensorProduct R S M ≃ₗ[S] M :=
    { toLinearMap := φ
      invFun := ψ
      left_inv := by
        intro x
        induction x using TensorProduct.inductionOn with
        | tmul s m =>
          change ψ (TensorProduct.AlgebraTensorModule.lift F (s ⊗ₜ[R] m)) = s ⊗ₜ[R] m
          rw [TensorProduct.AlgebraTensorModule.lift_tmul]
          change (1 : S) ⊗ₜ[R] (s • m) = s ⊗ₜ[R] m
          rw [TensorProduct.tmul_smul]
          change (s • (1 : S)) ⊗ₜ[R] m = s ⊗ₜ[R] m
          simp
        | add x y hx hy =>
          change ψ (φ (x + y)) = x + y
          rw [map_add φ, map_add ψ]
          exact congrArg₂ (· + ·) hx hy
      right_inv := by
        intro m
        simp [φ, F, ψ] }
  exact LinearEquiv.toModuleIso E

end ModuleCat

end
