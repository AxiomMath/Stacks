module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianRestriction

/-!
# Cartesian presheaves of modules: composition and faithfully flat descent

Let `R` be a presheaf of commutative rings on a category `C` and `M` a presheaf of modules over
its underlying presheaf of rings. For a morphism `f : X ⟶ Y` of `Cᵒᵖ` the module `M` is
*cartesian over `f`* when the base-change comparison `R Y ⊗[R X] M X ⟶ M Y` of
`Stacks.PresheafOfModules.restrictionBaseChange` is an isomorphism.

Along a composite `f ≫ g`, the comparison over the composite is the comparison over `g` after
the base change along `R Y ⟶ R Z` of the comparison over `f`. Being cartesian is closed under
composition, and it descends along a faithfully flat finite family: if `M` is cartesian over
each `q i : Y ⟶ Z i` and over each composite `f ≫ q i`, and the product of the ring maps
`R Y ⟶ R (Z i)` is faithfully flat, then `M` is cartesian over `f`.

## Main results

* `Stacks.PresheafOfModules.bijective_restrictionBaseChange_comp_iff`: given that `M` is
  cartesian over `g`, it is cartesian over `f ≫ g` exactly when the base change of the
  comparison over `f` along `R Y ⟶ R Z` is bijective.
* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_comp`: being cartesian is closed under
  composition.
* `Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_faithfullyFlat`: being cartesian
  descends along a finite family whose product of ring maps is faithfully flat.

## References

* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory TensorProduct

universe u v r m

namespace Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ CommRingCat.{r}}
  (M : PresheafOfModules.{max m r} (R ⋙ forget₂ CommRingCat RingCat))

/-- Given that `M` is cartesian over `g`, it is cartesian over `f ≫ g` exactly when the base
change along `R Y ⟶ R Z` of the comparison over `f` is bijective. -/
theorem bijective_restrictionBaseChange_comp_iff {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : Function.Bijective (restrictionBaseChange M g)) :
    letI := (R.map f).hom.toAlgebra
    letI := (R.map g).hom.toAlgebra
    Function.Bijective (restrictionBaseChange M (f ≫ g)) ↔
      Function.Bijective (LinearMap.lTensor (R.obj Z)
        ((restrictionBaseChange M f).hom :
          TensorProduct (R.obj X) (R.obj Y) (M.obj X) →ₗ[R.obj Y] M.obj Y)) := by
  let : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  let : Algebra (R.obj Y) (R.obj Z) := (R.map g).hom.toAlgebra
  let : Algebra (R.obj X) (R.obj Z) := (R.map (f ≫ g)).hom.toAlgebra
  let : IsScalarTower (R.obj X) (R.obj Y) (R.obj Z) :=
    .of_algebraMap_eq fun a => congrArg (fun φ => φ.hom a) (R.map_comp f g)
  let θ : TensorProduct (R.obj X) (R.obj Y) (M.obj X) →ₗ[R.obj Y] M.obj Y :=
    (restrictionBaseChange M f).hom
  let θg : TensorProduct (R.obj Y) (R.obj Z) (M.obj Y) →ₗ[R.obj Z] M.obj Z :=
    (restrictionBaseChange M g).hom
  let θfg : TensorProduct (R.obj X) (R.obj Z) (M.obj X) →ₗ[R.obj Z] M.obj Z :=
    (restrictionBaseChange M (f ≫ g)).hom
  let c := AlgebraTensorModule.cancelBaseChange (R.obj X) (R.obj Y) (R.obj Z) (R.obj Z)
    (M.obj X)
  have key : ∀ z, θfg (c z) = θg (LinearMap.lTensor (R.obj Z) θ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add z z' hz hz' => simp only [map_add, hz, hz']
    | tmul d w =>
      induction w using TensorProduct.induction_on with
      | zero => simp only [tmul_zero, map_zero]
      | add w w' hw hw' => simp only [tmul_add, map_add, hw, hw']
      | tmul b x =>
        rw [AlgebraTensorModule.cancelBaseChange_tmul, LinearMap.lTensor_tmul]
        have h1 : θfg ((b • d) ⊗ₜ x) = (b • d) • (M.map (f ≫ g) x : M.obj Z) :=
          restrictionBaseChange_tmul M (f ≫ g) (b • d) x
        have h2 : θ (b ⊗ₜ x) = b • (M.map f x : M.obj Y) := restrictionBaseChange_tmul M f b x
        have h3 : θg (d ⊗ₜ (b • (M.map f x : M.obj Y))) =
            d • (M.map g (b • (M.map f x : M.obj Y)) : M.obj Z) :=
          restrictionBaseChange_tmul M g d (b • (M.map f x : M.obj Y))
        have h4 : (M.map g (b • (M.map f x : M.obj Y)) : M.obj Z) =
            (R.map g).hom b • (M.map g (M.map f x) : M.obj Z) :=
          M.map_smul g b (M.map f x)
        have h5 : (M.map (f ≫ g) x : M.obj Z) = M.map g (M.map f x) := M.map_comp_apply f g x
        rw [h1, h2, h3, h4, h5, smul_smul]
        congr 1
        show (R.map g).hom b * d = d * (R.map g).hom b
        exact mul_comm _ _
  have hg' : Function.Bijective θg := hg
  show Function.Bijective θfg ↔ _
  have hc : (⇑θfg) ∘ ⇑c = (⇑θg) ∘ ⇑(LinearMap.lTensor (R.obj Z) θ) := funext key
  exact ⟨fun h => (Function.Bijective.of_comp_iff' hg' _).mp (hc ▸ h.comp c.bijective),
    fun h => (Function.Bijective.of_comp_iff _ c.bijective).mp (hc ▸ hg'.comp h)⟩

/-- If `M` is cartesian over `f` and over `g`, it is cartesian over `f ≫ g`. -/
theorem isIso_restrictionBaseChange_comp {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsIso (restrictionBaseChange M f)) (hg : IsIso (restrictionBaseChange M g)) :
    IsIso (restrictionBaseChange M (f ≫ g)) := by
  let : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  let : Algebra (R.obj Y) (R.obj Z) := (R.map g).hom.toAlgebra
  rw [ConcreteCategory.isIso_iff_bijective] at hf hg ⊢
  refine (bijective_restrictionBaseChange_comp_iff M f g hg).mpr ?_
  let e : TensorProduct (R.obj X) (R.obj Y) (M.obj X) ≃ₗ[R.obj Y] M.obj Y :=
    LinearEquiv.ofBijective ((restrictionBaseChange M f).hom :
      TensorProduct (R.obj X) (R.obj Y) (M.obj X) →ₗ[R.obj Y] M.obj Y) hf
  exact (LinearEquiv.lTensor (R.obj Z) e).bijective

/-- If `M` is cartesian over each `q i : Y ⟶ Z i` and over each composite `f ≫ q i`, and the
product of the ring maps `R Y ⟶ R (Z i)` is faithfully flat, then `M` is cartesian over `f`. -/
theorem isIso_restrictionBaseChange_of_faithfullyFlat {X Y : Cᵒᵖ} (f : X ⟶ Y)
    {I : Type*} [Finite I] (Z : I → Cᵒᵖ) (q : ∀ i, Y ⟶ Z i)
    (hff : (RingHom.pi (fun i => (R.map (q i)).hom)).FaithfullyFlat)
    (hq : ∀ i, IsIso (restrictionBaseChange M (q i)))
    (hfq : ∀ i, IsIso (restrictionBaseChange M (f ≫ q i))) :
    IsIso (restrictionBaseChange M f) := by
  classical
  let _ := Fintype.ofFinite I
  let : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  let (i : I) : Algebra (R.obj Y) (R.obj (Z i)) := (R.map (q i)).hom.toAlgebra
  let θ : TensorProduct (R.obj X) (R.obj Y) (M.obj X) →ₗ[R.obj Y] M.obj Y :=
    (restrictionBaseChange M f).hom
  have hi : ∀ i, Function.Bijective (LinearMap.lTensor (R.obj (Z i)) θ) := fun i =>
    (bijective_restrictionBaseChange_comp_iff M f (q i)
      ((ConcreteCategory.isIso_iff_bijective _).mp (hq i))).mp
      ((ConcreteCategory.isIso_iff_bijective _).mp (hfq i))
  have hmod : Module.FaithfullyFlat (R.obj Y) (∀ i, R.obj (Z i)) :=
    RingHom.faithfullyFlat_algebraMap_iff.mp hff
  let P := TensorProduct.piLeft (R.obj Y) (TensorProduct (R.obj X) (R.obj Y) (M.obj X))
    (fun i => R.obj (Z i))
  let Q := TensorProduct.piLeft (R.obj Y) (M.obj Y) (fun i => R.obj (Z i))
  have hsq : ∀ z, Q (LinearMap.lTensor (∀ i, R.obj (Z i)) θ z) =
      fun i => LinearMap.lTensor (R.obj (Z i)) θ (P z i) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => funext i; simp only [map_zero, Pi.zero_apply]
    | add z z' hz hz' => funext i; simp only [map_add, hz, hz', Pi.add_apply]
    | tmul a x => funext i; simp [P, Q]
  have hpi : Function.Bijective (fun z : ∀ i, TensorProduct (R.obj Y) (R.obj (Z i))
      (TensorProduct (R.obj X) (R.obj Y) (M.obj X)) =>
        fun i => LinearMap.lTensor (R.obj (Z i)) θ (z i)) :=
    ⟨fun z z' h => funext fun i => (hi i).1 (congrFun h i),
      fun y => ⟨fun i => ((hi i).2 (y i)).choose,
        funext fun i => ((hi i).2 (y i)).choose_spec⟩⟩
  have hfun : ⇑(LinearMap.lTensor (∀ i, R.obj (Z i)) θ) =
      ⇑Q.symm ∘ (fun z : ∀ i, TensorProduct (R.obj Y) (R.obj (Z i))
        (TensorProduct (R.obj X) (R.obj Y) (M.obj X)) =>
          fun i => LinearMap.lTensor (R.obj (Z i)) θ (z i)) ∘ ⇑P := by
    funext z
    simp only [Function.comp_apply, ← hsq, LinearEquiv.symm_apply_apply]
  have hP : Function.Bijective (LinearMap.lTensor (∀ i, R.obj (Z i)) θ) := by
    rw [hfun]
    exact Q.symm.bijective.comp (hpi.comp P.bijective)
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective (R.obj Y)
    (∀ i, R.obj (Z i)) θ).mp hP

end Stacks.PresheafOfModules

end
