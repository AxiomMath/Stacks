module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackChartCoefficient
public import Mathlib.Algebra.TrivSqZeroExt.Ideal

/-!
# The trivial square-zero thickening `Spec A ⊂ Spec A[M]` of a chart

For a site module `M` over `A`, the trivial square-zero extension `A[M] → A` is a square-zero
thickening of `Spec A` over `S` (`Deformation.Artin.squareZeroModuleThickening`), with kernel `M`
(`Deformation.Artin.squareZeroModuleKernelIso`). Its closed immersion is the arrow
`Deformation.Artin.squareZeroArrow` along which the tangent spaces are formed. This is how the
tangent space of `Coh_{X/B}` at an object over a chart is computed with the deformation theory
of thickenings of the second proof of Stacks 08WA, and the coefficient of its tangent
identification is `ℱ ⊗ p^*M̃` (`AlgebraicGeometry.Space.CoherentSituation.tangentCoefficientIso`).

This module is a helper and carries no `@[stacks]` attribute.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Deformation.Artin

variable {A : Type u} [CommRing A] {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}

/-- **The trivial square-zero thickening `A[M] → A`** of `Spec A` over `S`, for a site module
`M`; its closed immersion is `Deformation.Artin.squareZeroArrow`. -/
def squareZeroModuleThickening (M : SiteModule A B) :
    SquareZeroThickening A B S hS toS hA (TrivSqZeroExt A M.obj) where
  q := (TrivSqZeroExt.fstHom A A M.obj).toRingHom
  squareZeroSurjection := ⟨fun a => ⟨TrivSqZeroExt.inl a, rfl⟩, TrivSqZeroExt.kerIdeal_sq A M.obj⟩
  hA' := M.property
  toS' := ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj)) ≫ toS)
  arrow := squareZeroArrow A B S hS toS hA M
  arrow_spec := rfl

/-- **The kernel of `A[M] → A` is `M`.** -/
def squareZeroModuleKernelIso (M : SiteModule A B) :
    (squareZeroModuleThickening (S := S) (hS := hS) (toS := toS) (hA := hA) M).kernel ≅ M.obj := by
  letI := Stacks.Smooth.kerModule
    (squareZeroModuleThickening (S := S) (hS := hS) (toS := toS) (hA := hA)
      M).squareZeroSurjection.1
    (squareZeroModuleThickening (S := S) (hS := hS) (toS := toS) (hA := hA)
      M).squareZeroSurjection.2
  refine LinearEquiv.toModuleIso
    (X₁ := RingHom.ker (squareZeroModuleThickening (S := S) (hS := hS) (toS := toS) (hA := hA) M).q)
    (X₂ := (M.obj : Type u))
    { toFun := fun z => z.1.snd
      invFun := fun m => ⟨TrivSqZeroExt.inr m, TrivSqZeroExt.fst_inr A m⟩
      left_inv := fun z => Subtype.ext ((TrivSqZeroExt.mem_kerIdeal_iff_inr A M.obj z.1).1 z.2).symm
      right_inv := fun m => TrivSqZeroExt.snd_inr A m
      map_add' := fun z z' => rfl
      map_smul' := fun a z => ?_ }
  have h := congrArg (fun w : RingHom.ker (squareZeroModuleThickening (S := S) (hS := hS)
      (toS := toS) (hA := hA) M).q => (w : TrivSqZeroExt A M.obj).snd)
    (Stacks.Smooth.kerModule_smul
      (squareZeroModuleThickening (S := S) (hS := hS) (toS := toS) (hA := hA)
        M).squareZeroSurjection.1
      (squareZeroModuleThickening (S := S) (hS := hS) (toS := toS) (hA := hA)
        M).squareZeroSurjection.2
      (TrivSqZeroExt.inl a) z)
  refine h.trans ?_
  change (TrivSqZeroExt.inl a * z.1).snd = a • z.1.snd
  rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl,
    show z.1.fst = 0 from z.2, MulOpposite.op_zero, zero_smul, add_zero]

/-- **The morphism `A[M] → A[N]` of square-zero thickenings induced by a module map `M ⟶ N`.** -/
def squareZeroModuleThickeningHom {M N : SiteModule A B} (f : M ⟶ N) :
    SquareZeroThickening.Hom (squareZeroModuleThickening (S := S) (hS := hS) (toS := toS)
      (hA := hA) M) (squareZeroModuleThickening (S := S) (hS := hS) (toS := toS) (hA := hA) N) where
  ringHom := (TrivSqZeroExt.map f.hom.hom).toRingHom
  overBase := RingHom.ext fun z => TrivSqZeroExt.fst_map _ z
  overS := by
    have h := congrArg (fun φ => B.inclusion.map φ) (Over.w (squareZeroOverMap A B S hS toS f))
    simp only [CategoryTheory.Functor.map_comp] at h
    exact h
  kernelMap := (squareZeroModuleKernelIso M).hom ≫ f.hom ≫ (squareZeroModuleKernelIso N).inv
  kernelMap_spec i := by
    change TrivSqZeroExt.inr (f.hom.hom i.1.snd) = TrivSqZeroExt.map f.hom.hom i.1
    conv_rhs => rw [(TrivSqZeroExt.mem_kerIdeal_iff_inr A M.obj i.1).1 i.2]
    exact (TrivSqZeroExt.map_inr f.hom.hom _).symm

end Deformation.Artin

attribute [local instance 2000] CategoryTheory.instHasWeakSheafifyOfHasSheafify
attribute [local instance 6000] IsIso.epi_of_iso IsIso.mono_of_iso
attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance 5000] Abelian.has_kernels Abelian.has_cokernels

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}
  (hY : IsTerminal D.Y)
  {A : Type u} [CommRing A] {toS : Spec (.of A) ⟶ S} {hA : B.Contains (Spec (.of A))}
  {x : CoherentObject D}
  (hx : (coherentCFG D).val.p.obj x = Deformation.Artin.algebraOver A B S hS toS hA)
  [IsAffine ((BigFppfOver.toScheme B S hS).obj x.T.left)] (M : Deformation.Artin.SiteModule A B)

/-- **The coefficient of the tangent identification at `A[M]` is `ℱ ⊗ p^*M̃`**:
`p^*t^*𝒥 ⊗ ℱ ≅ ℱ ⊗ p^*M̃` for the thickening `Spec A ⊂ Spec A[M]` of test schemes. -/
def tangentCoefficientIso :=
  D.coefficientIsoOfIdealAt x (D.chartRingEquiv x hx) _ _
    (toRingedToposModulesHom_eq_baseProjection x)
    (((smallEtaleRingedToposHom B S hS
      (D.relativeSquareSituation.projection x.T)).toRingedToposModulesHom.pullbackModules).mapIso
      (thickeningIdealTildeIso (D.thickeningTestMap hY x hx
          (Deformation.Artin.squareZeroModuleThickening M)).left
        (isIso_toRange_testSchemeMap
          (D.thickeningTestMap hY x hx (Deformation.Artin.squareZeroModuleThickening M))
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening M)))
        (isFirstOrderThickening_range_yoneda_map B S hS _
          (D.isFirstOrderThickening_thickeningTestMap hY x hx
            (Deformation.Artin.squareZeroModuleThickening M)))
        (D.isFirstOrderThickening_thickeningTestMap hY x hx
          (Deformation.Artin.squareZeroModuleThickening M)) ≪≫
      (representedAffineAssociated B S hS x.T.left).mapIso
        (chartKernelIso hY hx (Deformation.Artin.squareZeroModuleThickening M) ≪≫
          (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
              (D.chartRingEquiv x hx).symm).functor.mapIso
            (Deformation.Artin.squareZeroModuleKernelIso M))))


end AlgebraicGeometry.Space.CoherentSituation

end
