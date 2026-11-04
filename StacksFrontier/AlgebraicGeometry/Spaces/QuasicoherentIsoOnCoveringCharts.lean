module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.AffineExtensionSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts

/-!
# Isomorphisms of quasi-coherent modules detected on a covering family of affine charts

Let `F` be an algebraic space and `T : ι → SmallEtale F` a family of affine étale charts covering
the final object of the small étale site.  A morphism `φ : M ⟶ N` of quasi-coherent `𝒪_F`-modules
which is bijective on the sections over every `T i` is an isomorphism.  Over an affine chart `A`
with a morphism `κ : A ⟶ T i` the sections of a quasi-coherent module are the base change of its
sections over `T i` (Stacks 03DX(2), in the form
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`), so `φ` is
bijective over `A` too; and such charts `A` generate a covering sieve of every chart.

## Main results

* `AlgebraicGeometry.Space.bijective_app_of_isCartesianOnAffineCharts`: bijectivity of a morphism
  of modules cartesian on affine charts passes from an affine chart to an affine chart over it.
* `AlgebraicGeometry.Space.isIso_of_bijective_app_of_coversTop_family`: a morphism of modules
  bijective over the affine charts admitting a morphism to some member of a covering family is
  an isomorphism.
* `AlgebraicGeometry.Space.isIso_of_bijective_app_of_coversTop_of_isQuasicoherentOnSite`: **the
  isomorphism criterion** for quasi-coherent modules and a covering family of affine charts.
-/

@[expose] public section

open CategoryTheory Opposite TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)

/-- **Bijectivity on sections passes along a morphism of affine charts** for modules cartesian
on affine charts: the sections over `A` are the base change of the sections over `Z`, compatibly
with `φ`. -/
theorem bijective_app_of_isCartesianOnAffineCharts {M N : Modules.{u, u} B S hS X hX}
    (hM : IsCartesianOnAffineCharts M) (hN : IsCartesianOnAffineCharts N) (φ : M ⟶ N)
    {A Z : SmallEtale B S hS X}
    (hA : IsAffine ((SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS).obj A))
    (hZ : IsAffine ((SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS).obj Z))
    (κ : A ⟶ Z) (hφ : Function.Bijective (φ.val.app (op Z))) :
    Function.Bijective (φ.val.app (op A)) := by
  let := chartAlgebra (hF := hX) κ
  let e : TensorProduct (chartRing B S hS X hX Z) (chartRing B S hS X hX A) (M.val.obj (op Z)) ≃ₗ[
      chartRing B S hS X hX A]
      TensorProduct (chartRing B S hS X hX Z) (chartRing B S hS X hX A) (N.val.obj (op Z)) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _)
      (LinearEquiv.ofBijective (φ.val.app (op Z)).hom hφ)
  have hcomm : ∀ z, φ.val.app (op A) (sectionsBaseChange M κ z) = sectionsBaseChange N κ (e z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b x =>
      rw [chartBaseChange_tmul, TensorProduct.AlgebraTensorModule.congr_tmul, chartBaseChange_tmul,
        map_smul, chartRestrictLinear_apply, chartRestrictLinear_apply]
      exact congrArg (b • ·) (PresheafOfModules.naturality_apply φ.val κ.op x)
    | add z w hz hw => simp only [map_add, hz, hw]
  have hcomp : Function.Bijective ((φ.val.app (op A)) ∘ (sectionsBaseChange M κ)) := by
    convert (hN Z A hZ hA κ).comp e.bijective using 1
    exact funext hcomm
  exact (Function.Bijective.of_comp_iff _ (hM Z A hZ hA κ)).1 hcomp

/-- The sieve of the morphisms to `U` factoring through an affine chart admitting a morphism to
some member of a family `T`. -/
def affineOverFamilySieve {ι : Type*} (T : ι → SmallEtale B S hS X) (U : SmallEtale B S hS X) :
    Sieve U where
  arrows W g := ∃ (A : SmallEtale B S hS X) (a : W ⟶ A) (b : A ⟶ U),
    IsAffine ((SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS).obj A) ∧
      (∃ i, Nonempty (A ⟶ T i)) ∧ a ≫ b = g
  downward_closed := by
    rintro W W' g ⟨A, a, b, hA, hT, rfl⟩ h
    exact ⟨A, h ≫ a, b, hA, hT, by simp⟩

include hX in
/-- If a family `T` covers the final object, the sieve `affineOverFamilySieve` is covering. -/
theorem affineOverFamilySieve_mem {ι : Type*} {T : ι → SmallEtale B S hS X}
    (hT : (SmallEtale.topology B S hS X).CoversTop T) (U : SmallEtale B S hS X) :
    affineOverFamilySieve B S hS T U ∈ SmallEtale.topology B S hS X U := by
  refine (SmallEtale.topology B S hS X).transitive (hT U) _ fun W g hg => ?_
  obtain ⟨i, ⟨t⟩⟩ := (Sieve.mem_ofObjects_iff _ g).1 hg
  refine (SmallEtale.topology B S hS X).superset_covering ?_
    ((SmallEtale.isCoverDense_affineEtaleInclusion B S hS X hX).is_cover W)
  rintro W' h ⟨⟨A, lift, map, fac⟩⟩
  exact ⟨(AffineEtale.inclusion B S hS X).obj A, lift, map ≫ g, A.property, ⟨i, ⟨map ≫ t⟩⟩,
    by rw [← Category.assoc, fac]⟩

include hX in
/-- **A morphism of modules bijective on the sections over the affine charts admitting a
morphism to a member of a covering family is an isomorphism.** -/
theorem isIso_of_bijective_app_of_coversTop_family {ι : Type*} {T : ι → SmallEtale B S hS X}
    (hT : (SmallEtale.topology B S hS X).CoversTop T)
    {M N : Modules.{u, u} B S hS X hX} (φ : M ⟶ N)
    (h : ∀ A : SmallEtale B S hS X,
      IsAffine ((SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS).obj A) →
        (∃ i, Nonempty (A ⟶ T i)) → Function.Bijective (φ.val.app (op A))) :
    IsIso φ := by
  have hinj : PresheafOfModules.IsLocallyInjective (smallEtaleRingedSite B S hS X hX).J
      φ.val := by
    constructor
    intro U x y hxy
    refine (SmallEtale.topology B S hS X).superset_covering ?_
      (affineOverFamilySieve_mem B S hS hX hT U.unop)
    rintro W g ⟨A, a, b, hA, hT', rfl⟩
    refine (Presheaf.equalizerSieve x y).downward_closed ?_ a
    refine (h A hA hT').1 ?_
    have hx := NatTrans.naturality_apply
      ((PresheafOfModules.toPresheaf _).map φ.val) b.op x
    have hy := NatTrans.naturality_apply
      ((PresheafOfModules.toPresheaf _).map φ.val) b.op y
    exact hx.trans ((congrArg (((PresheafOfModules.toPresheaf _).obj N.val).map b.op) hxy).trans
      hy.symm)
  have hsurj : PresheafOfModules.IsLocallySurjective (smallEtaleRingedSite B S hS X hX).J
      φ.val := by
    constructor
    intro U s
    refine (SmallEtale.topology B S hS X).superset_covering ?_
      (affineOverFamilySieve_mem B S hS hX hT U)
    rintro W g ⟨A, a, b, hA, hT', rfl⟩
    refine (Presheaf.imageSieve _ s).downward_closed ?_ a
    exact (h A hA hT').2 (((PresheafOfModules.toPresheaf _).obj N.val).map b.op s)
  exact Stacks.SheafOfModules.isIso_of_isLocallyBijective φ

/-- **A morphism of quasi-coherent modules bijective on the sections over a covering family of
affine charts is an isomorphism.** -/
theorem isIso_of_bijective_app_of_coversTop_of_isQuasicoherentOnSite {ι : Type*}
    {T : ι → SmallEtale B S hS X} (hT : (SmallEtale.topology B S hS X).CoversTop T)
    (hTaff : ∀ i,
      IsAffine ((SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS).obj (T i)))
    {M N : Modules.{u, u} B S hS X hX} (hM : M.IsQuasicoherentOnSite)
    (hN : N.IsQuasicoherentOnSite) (φ : M ⟶ N)
    (h : ∀ i, Function.Bijective (φ.val.app (op (T i)))) : IsIso φ :=
  isIso_of_bijective_app_of_coversTop_family B S hS hX hT φ fun _ hA ⟨i, ⟨κ⟩⟩ =>
    bijective_app_of_isCartesianOnAffineCharts B S hS hX
      ((isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X hX M).1 hM)
      ((isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X hX N).1 hN) φ hA (hTaff i) κ
      (h i)

end AlgebraicGeometry.Space

end
