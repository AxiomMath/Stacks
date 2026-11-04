module

public import Mathlib.CategoryTheory.Abelian.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.SheavesOfRings.SectionwiseSheafification

/-!
# Descending a homomorphism of sheaves of rings along a locally surjective map

Let `p : P ⟶ Q` be a locally surjective homomorphism of sheaves of commutative rings on a site,
and let `ψ : P ⟶ R` be a homomorphism of sheaves of commutative rings killing every local section
of `P` that `p` kills. Then `ψ` factors uniquely through `p`. On underlying sheaves of abelian
groups `p` is an epimorphism, hence the cokernel of its kernel, so `ψ` descends to a morphism of
sheaves of abelian groups `Q ⟶ R`; it is multiplicative because multiplicativity can be checked
on the images of local sections of `P`.

## Main definitions

* `CategoryTheory.Sheaf.descendRingHom`: the homomorphism `Q ⟶ R` through which `ψ` factors.

## Main results

* `CategoryTheory.Sheaf.descendRingHom_comp`: `p ≫ descendRingHom p ψ h = ψ`.
* `CategoryTheory.Sheaf.descendRingHom_unique`: it is the only such homomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {P Q R : Sheaf J CommRingCat.{max u v w}}

/-- Two binary families of maps into a sheaf of rings, natural in the site variable, agree as soon
as they agree on the images of sections along the locally surjective `p`. -/
private theorem eq_of_isLocallySurjective_ringSheaf (p : P ⟶ Q)
    [Presheaf.IsLocallySurjective J p.hom]
    (a b : ∀ U : Cᵒᵖ, Q.obj.obj U → Q.obj.obj U → R.obj.obj U)
    (ha : ∀ {U V} (g : U ⟶ V) x y, R.obj.map g (a U x y) = a V (Q.obj.map g x) (Q.obj.map g y))
    (hb : ∀ {U V} (g : U ⟶ V) x y, R.obj.map g (b U x y) = b V (Q.obj.map g x) (Q.obj.map g y))
    (h : ∀ U (x y : P.obj.obj U), a U (p.hom.app U x) (p.hom.app U y) =
      b U (p.hom.app U x) (p.hom.app U y))
    (U : Cᵒᵖ) (x y : Q.obj.obj U) : a U x y = b U x y := by
  have : Presheaf.IsLocallySurjective J (Functor.whiskerRight p.hom (forget CommRingCat)) :=
    (Presheaf.isLocallySurjective_iff_whisker_forget J p.hom).mp inferInstance
  exact eq_of_isLocallySurjective_binary J (Functor.whiskerRight p.hom (forget CommRingCat))
    ((sheafCompose J (forget CommRingCat)).obj R) a b ha hb h U x y

variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]

/-- The underlying sheaf of abelian groups of a sheaf of commutative rings: that of its unit
module. -/
noncomputable abbrev ringSheafAb (P : Sheaf J CommRingCat.{max u v w}) :
    Sheaf J AddCommGrpCat.{max u v w} :=
  (SheafOfModules.toSheaf _).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf P))

/-- A homomorphism of sheaves of commutative rings, on underlying sheaves of abelian groups. -/
noncomputable def ringSheafAbMap (p : P ⟶ Q) : ringSheafAb J P ⟶ ringSheafAb J Q :=
  ⟨{ app U := AddCommGrpCat.ofHom (p.hom.app U).hom.toAddMonoidHom
     naturality {U V} g := by
        ext x
        exact ConcreteCategory.congr_hom (p.hom.naturality g) x }⟩

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- On sections, the underlying map of abelian groups is the ring homomorphism. -/
theorem ringSheafAbMap_app (p : P ⟶ Q) (U : Cᵒᵖ) (x : P.obj.obj U) :
    (ringSheafAbMap J p).hom.app U x = p.hom.app U x := rfl

variable {J} (p : P ⟶ Q) [Presheaf.IsLocallySurjective J p.hom] (ψ : P ⟶ R)
  (hψ : ∀ (U : Cᵒᵖ) (x : P.obj.obj U), p.hom.app U x = 0 → ψ.hom.app U x = 0)

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- On underlying sheaves of abelian groups a locally surjective homomorphism of sheaves of rings
is an epimorphism. -/
theorem epi_ringSheafAbMap : Epi (ringSheafAbMap J p) := by
  have h : Presheaf.IsLocallySurjective J (ringSheafAbMap J p).hom :=
    (Presheaf.isLocallySurjective_iff_whisker_forget J (ringSheafAbMap J p).hom).mpr
      ((Presheaf.isLocallySurjective_iff_whisker_forget J p.hom).mp inferInstance : _)
  have : Sheaf.IsLocallySurjective (ringSheafAbMap J p) := h
  exact Sheaf.epi_of_isLocallySurjective _

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
omit [Presheaf.IsLocallySurjective J p.hom] in
include hψ in
/-- `ψ` kills the kernel of `p`, on underlying sheaves of abelian groups. -/
theorem kernel_ι_ringSheafAbMap :
    kernel.ι (ringSheafAbMap J p) ≫ ringSheafAbMap J ψ = 0 := by
  ext U x
  have hx : p.hom.app U ((kernel.ι (ringSheafAbMap J p)).hom.app U x) = 0 :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (congrArg (fun k => k.hom) (kernel.condition (ringSheafAbMap J p))) U) x
  exact hψ U _ hx

/-- The underlying map of abelian groups of the descended homomorphism. -/
noncomputable def descendRingHomAb : ringSheafAb J Q ⟶ ringSheafAb J R :=
  have := epi_ringSheafAbMap p
  (Abelian.epiIsCokernelOfKernel (Fork.ofι (kernel.ι (ringSheafAbMap J p)) (kernel.condition _))
    (kernelIsKernel (ringSheafAbMap J p))).desc
    (CokernelCofork.ofπ (ringSheafAbMap J ψ) (kernel_ι_ringSheafAbMap p ψ hψ))

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- The descended map of abelian groups factors `ψ` through `p`. -/
theorem ringSheafAbMap_descendRingHomAb :
    ringSheafAbMap J p ≫ descendRingHomAb p ψ hψ = ringSheafAbMap J ψ :=
  have := epi_ringSheafAbMap p
  (Abelian.epiIsCokernelOfKernel (Fork.ofι (kernel.ι (ringSheafAbMap J p)) (kernel.condition _))
    (kernelIsKernel (ringSheafAbMap J p))).fac _ WalkingParallelPair.one

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- On sections, the descended map sends `p(x)` to `ψ(x)`. -/
theorem descendRingHomAb_apply (U : Cᵒᵖ) (x : P.obj.obj U) :
    (descendRingHomAb p ψ hψ).hom.app U (p.hom.app U x) = ψ.hom.app U x :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun k : ringSheafAb J P ⟶ ringSheafAb J R => k.hom)
      (ringSheafAbMap_descendRingHomAb p ψ hψ)) U) x

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- The descended map commutes with the restriction maps of the site. -/
theorem descendRingHomAb_naturality {U V : Cᵒᵖ} (g : U ⟶ V) (y : Q.obj.obj U) :
    R.obj.map g ((descendRingHomAb p ψ hψ).hom.app U y) =
      (descendRingHomAb p ψ hψ).hom.app V (Q.obj.map g y) :=
  (ConcreteCategory.congr_hom ((descendRingHomAb p ψ hψ).hom.naturality g) y).symm

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- The descended map is multiplicative, as this can be checked on images of sections of
`P`. -/
theorem descendRingHomAb_map_mul (U : Cᵒᵖ) (x y : Q.obj.obj U) :
    (show R.obj.obj U from (descendRingHomAb p ψ hψ).hom.app U (x * y)) =
      (show R.obj.obj U from (descendRingHomAb p ψ hψ).hom.app U x) *
        (show R.obj.obj U from (descendRingHomAb p ψ hψ).hom.app U y) := by
  refine eq_of_isLocallySurjective_ringSheaf J p
    (fun U (x y : Q.obj.obj U) =>
      (show R.obj.obj U from (descendRingHomAb p ψ hψ).hom.app U (x * y)))
    (fun U (x y : Q.obj.obj U) =>
      (show R.obj.obj U from (descendRingHomAb p ψ hψ).hom.app U x) *
        (show R.obj.obj U from (descendRingHomAb p ψ hψ).hom.app U y))
    ?_ ?_ ?_ U x y
  · rintro U V g (x : Q.obj.obj U) (y : Q.obj.obj U)
    change R.obj.map g ((descendRingHomAb p ψ hψ).hom.app U (x * y)) =
      (descendRingHomAb p ψ hψ).hom.app V (Q.obj.map g x * Q.obj.map g y)
    rw [descendRingHomAb_naturality, map_mul]
  · rintro U V g (x : Q.obj.obj U) (y : Q.obj.obj U)
    rw [map_mul, descendRingHomAb_naturality, descendRingHomAb_naturality]
  · intro U x' y'
    rw [← map_mul, descendRingHomAb_apply, descendRingHomAb_apply, descendRingHomAb_apply,
      map_mul]

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- The descended map sends `1` to `1`. -/
theorem descendRingHomAb_map_one (U : Cᵒᵖ) :
    (show R.obj.obj U from (descendRingHomAb p ψ hψ).hom.app U (1 : Q.obj.obj U)) = 1 := by
  have h := descendRingHomAb_apply p ψ hψ U 1
  rw [map_one, map_one] at h
  exact h

/-- **Descent of a homomorphism of sheaves of rings along a locally surjective homomorphism.** A
homomorphism `ψ : P ⟶ R` killing every local section killed by the locally surjective
`p : P ⟶ Q` factors through `p`. -/
noncomputable def descendRingHom : Q ⟶ R :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom
        { toFun := (descendRingHomAb p ψ hψ).hom.app U
          map_one' := descendRingHomAb_map_one p ψ hψ U
          map_mul' := descendRingHomAb_map_mul p ψ hψ U
          map_zero' := map_zero _
          map_add' := map_add _ }
      naturality {U V} g := by
        ext y
        exact (descendRingHomAb_naturality p ψ hψ g y).symm }

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- On sections, the descended homomorphism sends `p(x)` to `ψ(x)`. -/
theorem descendRingHom_apply (U : Cᵒᵖ) (x : P.obj.obj U) :
    (descendRingHom p ψ hψ).hom.app U (p.hom.app U x) = ψ.hom.app U x :=
  descendRingHomAb_apply p ψ hψ U x

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- The descended homomorphism factors `ψ` through `p`. -/
theorem descendRingHom_comp : p ≫ descendRingHom p ψ hψ = ψ := by
  ext U x
  exact descendRingHom_apply p ψ hψ U x

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
omit [Presheaf.IsLocallySurjective J p.hom] in
/-- Two homomorphisms out of the target of a locally surjective homomorphism agreeing after
precomposition with it are equal. -/
theorem hom_ext_of_isLocallySurjective [Presheaf.IsLocallySurjective J p.hom] {h₁ h₂ : Q ⟶ R}
    (h : p ≫ h₁ = p ≫ h₂) : h₁ = h₂ := by
  ext U y
  refine eq_of_isLocallySurjective_ringSheaf J p
    (fun U (x _ : Q.obj.obj U) => h₁.hom.app U x) (fun U (x _ : Q.obj.obj U) => h₂.hom.app U x)
    ?_ ?_ ?_ U y y
  · rintro U V g x -
    exact (ConcreteCategory.congr_hom (h₁.hom.naturality g) x).symm
  · rintro U V g x -
    exact (ConcreteCategory.congr_hom (h₂.hom.naturality g) x).symm
  · intro U x' _
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg (fun k => k.hom) h) U) x'

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- The descended homomorphism is the only homomorphism factoring `ψ` through `p`. -/
theorem descendRingHom_unique (h : Q ⟶ R) (hh : p ≫ h = ψ) : h = descendRingHom p ψ hψ :=
  hom_ext_of_isLocallySurjective p (hh.trans (descendRingHom_comp p ψ hψ).symm)

end CategoryTheory.Sheaf

end
