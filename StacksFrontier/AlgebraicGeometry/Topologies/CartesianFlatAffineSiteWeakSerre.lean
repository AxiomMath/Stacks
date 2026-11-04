module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianFlatAffineSiteSurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianChangeOfRings

/-!
# Cartesian modules on a site of affine schemes form a weak Serre subcategory

Let `C` be a site of affine schemes with fibre products along its coverings, as in
`StacksFrontier.AlgebraicGeometry.Topologies.CartesianFlatAffineSite`, which moreover has flat
factorizations (`Stacks.FlatAffineSite.HasFlatFactorizations`). This file proves that the sheaves
of modules which are cartesian over every morphism form a weak Serre subcategory of all sheaves of
modules (Stacks 0754, conditions (1)–(4)): they contain `0`, are closed under isomorphisms,
kernels, cokernels and extensions.

## Main definitions

* `Stacks.FlatAffineSite.cartesianModules`: the sheaves of modules cartesian over every morphism.

## Main results

* `Stacks.SheafOfModules.injective_app_of_isLimit` and
  `Stacks.SheafOfModules.exact_app_of_isLimit`: a kernel of sheaves of modules is a kernel on
  sections.
* `Stacks.FlatAffineSite.isWeakSerreClass_cartesianModules`: the weak Serre property.

## References

* [Stacks Project, Tag 07B4](https://stacks.math.columbia.edu/tag/07B4)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w m u u₁ v₁ t u' v'

namespace Stacks.SheafOfModules

variable {D : Type u'} [Category.{v'} D] {K : GrothendieckTopology D} {R : Sheaf K RingCat.{u}}

/-- Evaluation of sheaves of modules at an object preserves zero morphisms. -/
instance (X : Dᵒᵖ) : (_root_.SheafOfModules.evaluation.{t} R X).PreservesZeroMorphisms :=
  ⟨fun _ _ => rfl⟩

/-- The sections of a kernel of sheaves of modules inject into the sections of the source. -/
theorem injective_app_of_isLimit {M N : _root_.SheafOfModules.{t} R} {φ : M ⟶ N}
    {k : KernelFork φ} (hk : IsLimit k) (X : Dᵒᵖ) : Function.Injective (k.ι.val.app X) :=
  (ModuleCat.mono_iff_injective _).mp
    (Fork.IsLimit.mono (KernelFork.mapIsLimit k hk (_root_.SheafOfModules.evaluation R X)))

/-- The sections of a kernel of sheaves of modules are the kernel of the map on sections. -/
theorem exact_app_of_isLimit {M N : _root_.SheafOfModules.{t} R} {φ : M ⟶ N}
    {k : KernelFork φ} (hk : IsLimit k) (X : Dᵒᵖ) :
    Function.Exact (k.ι.val.app X) (φ.val.app X) := by
  have hex := ShortComplex.exact_of_f_is_kernel
    (ShortComplex.mk ((_root_.SheafOfModules.evaluation R X).map k.ι)
      ((_root_.SheafOfModules.evaluation R X).map φ)
      (by rw [← Functor.map_comp, KernelFork.condition, Functor.map_zero]))
    (KernelFork.mapIsLimit k hk (_root_.SheafOfModules.evaluation R X))
  exact LinearMap.exact_iff.mpr ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp hex).symm

/-- The sections of a zero sheaf of modules are zero. -/
theorem subsingleton_obj_of_isZero {M : _root_.SheafOfModules.{t} R} (hM : IsZero M)
    (X : Dᵒᵖ) : Subsingleton (M.val.obj X) := by
  refine ⟨fun x y => ?_⟩
  have h : ∀ z : M.val.obj X, z = 0 := fun z =>
    congrArg (fun f : M ⟶ M => f.val.app X z) ((IsZero.iff_id_eq_zero M).1 hM)
  rw [h x, h y]

end Stacks.SheafOfModules

namespace Stacks.FlatAffineSite

open Stacks.PresheafOfModules ZeroObject

variable {C : Type u₁} [Category.{v₁} C] {L : C ⥤ Scheme.{u}} {Q : MorphismProperty C}
  {J : GrothendieckTopology C}

variable (hR : Presheaf.IsSheaf J (rings L ⋙ forget₂ CommRingCat RingCat))

/-- The sheaves of modules on a site of affine schemes which are cartesian over every morphism:
for every `h : Y ⟶ X` the comparison `𝒪(Y) ⊗_{𝒪(X)} M(X) ⟶ M(Y)` is an isomorphism. This is
`Stacks.PresheafOfModules.cartesianModules` read on the underlying presheaves. -/
def cartesianModules : ObjectProperty (SheafOfModules.{max m u}
    (⟨rings L ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf J RingCat.{u})) :=
  fun M => Stacks.PresheafOfModules.cartesianModules.{u₁, v₁, u, m} (rings L) M.val

/-- A zero sheaf of modules is cartesian. -/
theorem cartesianModules_of_isZero {M : SheafOfModules.{max m u}
    (⟨rings L ⋙ forget₂ CommRingCat RingCat, hR⟩ : Sheaf J RingCat.{u})} (hM : IsZero M) :
    cartesianModules.{m} hR M := by
  intro X Y f
  let : Algebra ((rings L).obj X) ((rings L).obj Y) := ((rings L).map f).hom.toAlgebra
  have := Stacks.SheafOfModules.subsingleton_obj_of_isZero hM X
  have := Stacks.SheafOfModules.subsingleton_obj_of_isZero hM Y
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun a b _ => ?_, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  have hs : Subsingleton (TensorProduct ((rings L).obj X) ((rings L).obj Y) (M.val.obj X)) :=
    inferInstance
  exact @Subsingleton.elim _ hs a b

/-- **Cartesian sheaves of modules on a site of affine schemes with flat factorizations form a
weak Serre subcategory** (Stacks 0754, conditions (1)–(4)). -/
theorem isWeakSerreClass_cartesianModules [∀ X, IsAffine (L.obj X)] [Q.HasPullbacks]
    [Q.IsStableUnderBaseChange] [Q.IsStableUnderComposition]
    [HasSheafify J AddCommGrpCat.{max m u}] [J.WEqualsLocallyBijective AddCommGrpCat.{max m u}]
    (hQ : ∀ ⦃X Y : C⦄ (f : X ⟶ Y), Q f → Flat (L.map f)) (hL : PreservesPullbacksAlong L Q)
    (hJ : HasCoverRefinements.{w} L Q J) (hcov : CoversAreCovering.{w} L Q J)
    (hfac : HasFlatFactorizations.{w} L Q) :
    (cartesianModules.{m} hR).IsWeakSerreClass where
  exists_zero := ⟨0, isZero_zero _, cartesianModules_of_isZero hR (isZero_zero _)⟩
  of_iso {M N} e h := fun X Y f => by
    have : IsIso (restrictionBaseChange ((SheafOfModules.forget _).obj M) f) := h f
    exact isIso_restrictionBaseChange_of_iso ((SheafOfModules.forget _).mapIso e) f
  kernels_le := by
    rintro _ ⟨φ, k, hk, hM, hN⟩
    exact fun X Y f => isIso_restrictionBaseChange_kernel hQ hfac k.ι.val φ.val
      (Stacks.SheafOfModules.injective_app_of_isLimit hk)
      (Stacks.SheafOfModules.exact_app_of_isLimit hk) (fun f => hM f) (fun f => hN f) f
  cokernels_le := by
    rintro _ ⟨φ, k, hk, hM, hN⟩
    exact fun X Y f => isIso_restrictionBaseChange_colimit hQ hL hJ hR (parallelPair φ 0) k hk
      (by rintro (_ | _) X Y f; exacts [hM f, hN f]) f
  prop_X₂_of_shortExact {T} hT h₁ h₃ := by
    have := hT.mono_f
    have := hT.epi_g
    have hk := hT.fIsKernel
    have hinj := Stacks.SheafOfModules.injective_app_of_isLimit hk
    have hex := Stacks.SheafOfModules.exact_app_of_isLimit hk
    have hsurj : ∀ X : C, Function.Surjective (T.g.val.app (op X)) :=
      surjective_app_of_isLocallySurjective hQ hL hJ hcov hR T.f T.g hinj hex
        (fun f => h₁ f)
        (fun X s => Stacks.SheafOfModules.EpiMono.exists_covering_of_epi T.g s)
    exact fun X Y f => isIso_restrictionBaseChange_of_shortExact T.f.val T.g.val hinj hex
      (fun Z => hsurj Z.unop) f (h₁ f) (h₃ f)

end Stacks.FlatAffineSite

end
