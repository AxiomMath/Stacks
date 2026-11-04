module

public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import StacksFrontier.CategoryTheory.Sites.Modules.ConormalSequence

/-!
# A locally bijective change of presentation is locally bijective on conormal modules

Let `φ₁ : A₁ ⟶ B` and `φ₂ : A₂ ⟶ B` be two presentations of a presheaf of commutative rings on
a site `(C, J)` and let `ψ : A₁ ⟶ A₂` be a factorisation, `ψ ≫ φ₂ = φ₁`. Write `I₁` and `I₂`
for the two kernel presheaves. This file proves that if `ψ` is locally injective and locally
surjective then so is the induced map of conormal presheaves `I₁/I₁² ⟶ I₂/I₂²`.

Every statement is elementwise: a covering sieve of the object, together with the witness over
each of its arrows. Nothing here uses the sheaf condition.

## Main definitions

* `Stacks.Sites.Conormal.vanishingSieve`: the arrows along which a local section of a presheaf
  of modules restricts to zero.

## Main results

* `Stacks.Sites.Conormal.exists_covering_kernelIdeal_lift`: a local section of `I₂` is locally a
  value of `ψ` on a local section of `I₁`.
* `Stacks.Sites.Conormal.exists_covering_sq_lift`: the same for the square of the kernel.
* `Stacks.Sites.Conormal.exists_covering_conormalMapOfFac_eq`: the induced map of conormal
  presheaves is locally surjective.
* `Stacks.Sites.Conormal.vanishingSieve_mem_of_conormalMapOfFac_eq_zero`: it is locally
  injective.

## References

* [Stacks Project, Tag 08TS](https://stacks.math.columbia.edu/tag/08TS), the conormal sequence.
* [Stacks Project, Tag 08TY](https://stacks.math.columbia.edu/tag/08TY), the independence of the
  naive cotangent complex from the presentation.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w w'

namespace Stacks.Sites.Conormal

/-- The sieve of arrows along which a local section of a presheaf of modules restricts to
zero. -/
def vanishingSieve {C : Type u} [Category.{v} C] {S : Cᵒᵖ ⥤ RingCat.{w}}
    (M : PresheafOfModules.{w'} S) {X : C} (c : M.obj (op X)) : Sieve X where
  arrows Y g := M.map g.op c = 0
  downward_closed := by
    intro Y Z g hg k
    have h : M.map (k ≫ g).op c = M.map k.op (M.map g.op c) := by
      rw [op_comp]; exact M.map_comp_apply g.op k.op c
    rw [h, hg]
    exact map_zero _

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A₁ A₂ B : Cᵒᵖ ⥤ CommRingCat.{w}} {φ₁ : A₁ ⟶ B} {φ₂ : A₂ ⟶ B} {ψ : A₁ ⟶ A₂}
  (hψ : ψ ≫ φ₂ = φ₁)

include hψ in
/-- Applying `ψ` and then `φ₂` to a local section is applying `φ₁` to it. -/
theorem app_apply_of_fac (X : Cᵒᵖ) (x : A₁.obj X) : φ₂.app X (ψ.app X x) = φ₁.app X x :=
  congrArg (fun t : A₁ ⟶ B ↦ (t.app X).hom x) hψ

/-- Restriction along an arrow of the site carries the square of the kernel ideal into the
square of the kernel ideal. -/
theorem presheafMap_mem_kernelIdeal_sq {X Y : Cᵒᵖ} (f : X ⟶ Y) {z : A₁.obj X}
    (hz : z ∈ kernelIdeal φ₁ X ^ 2) : A₁.map f z ∈ kernelIdeal φ₁ Y ^ 2 := by
  rw [pow_two] at hz ⊢
  refine Submodule.mul_induction_on hz (fun m hm n hn ↦ ?_) (fun x y hx hy ↦ ?_)
  · rw [map_mul]
    exact Ideal.mul_mem_mul (map_kernel φ₁ f hm) (map_kernel φ₁ f hn)
  · rw [map_add]
    exact Ideal.add_mem _ hx hy

include hψ in
/-- A local section of the kernel of `φ₂` is, on a covering sieve, the value of `ψ` on a local
section of the kernel of `φ₁`. -/
theorem exists_covering_kernelIdeal_lift [Presheaf.IsLocallySurjective J ψ] {X : C}
    (x : A₂.obj (op X)) (hx : x ∈ kernelIdeal φ₂ (op X)) :
    ∃ S : Sieve X, S ∈ J X ∧ ∀ (Y : C) (g : Y ⟶ X), S g →
      ∃ y : A₁.obj (op Y), y ∈ kernelIdeal φ₁ (op Y) ∧ ψ.app (op Y) y = A₂.map g.op x := by
  refine ⟨Presheaf.imageSieve ψ x, Presheaf.imageSieve_mem J ψ x, fun Y g ⟨y, hy⟩ ↦ ⟨y, ?_, hy⟩⟩
  change φ₁.app (op Y) y = 0
  rw [← app_apply_of_fac hψ (op Y) y, hy, φ₂.naturality_apply,
    show φ₂.app (op X) x = 0 from hx, map_zero]

include hψ in
/-- A local section of the square of the kernel of `φ₂` is, on a covering sieve, the value of
`ψ` on a local section of the square of the kernel of `φ₁`. -/
theorem exists_covering_sq_lift [Presheaf.IsLocallySurjective J ψ] {X : C}
    (w : A₂.obj (op X)) (hw : w ∈ kernelIdeal φ₂ (op X) ^ 2) :
    ∃ S : Sieve X, S ∈ J X ∧ ∀ (Y : C) (g : Y ⟶ X), S g →
      ∃ y : A₁.obj (op Y), y ∈ kernelIdeal φ₁ (op Y) ^ 2 ∧
        ψ.app (op Y) y = A₂.map g.op w := by
  rw [pow_two] at hw
  refine Submodule.mul_induction_on hw (fun m hm n hn ↦ ?_) (fun x y hx hy ↦ ?_)
  · obtain ⟨S, hS, hm'⟩ := exists_covering_kernelIdeal_lift J hψ m hm
    obtain ⟨T, hT, hn'⟩ := exists_covering_kernelIdeal_lift J hψ n hn
    refine ⟨S ⊓ T, J.intersection_covering hS hT, fun Y g hg ↦ ?_⟩
    obtain ⟨p, hp, hp'⟩ := hm' Y g hg.1
    obtain ⟨q, hq, hq'⟩ := hn' Y g hg.2
    refine ⟨p * q, by rw [pow_two]; exact Ideal.mul_mem_mul hp hq, ?_⟩
    rw [map_mul, hp', hq', ← map_mul]
  · obtain ⟨S, hS, hx'⟩ := hx
    obtain ⟨T, hT, hy'⟩ := hy
    refine ⟨S ⊓ T, J.intersection_covering hS hT, fun Y g hg ↦ ?_⟩
    obtain ⟨p, hp, hp'⟩ := hx' Y g hg.1
    obtain ⟨q, hq, hq'⟩ := hy' Y g hg.2
    exact ⟨p + q, Ideal.add_mem _ hp hq, by rw [map_add, hp', hq', ← map_add]⟩

include hψ in
/-- A local section of `I₂/I₂²` is, on a covering
sieve, the image of a local section of `I₁/I₁²`. -/
theorem exists_covering_conormalMapOfFac_eq [Presheaf.IsLocallySurjective J ψ] {X : C}
    (c : (conormalPresheaf φ₂).obj (op X)) :
    ∃ S : Sieve X, S ∈ J X ∧ ∀ (Y : C) (g : Y ⟶ X), S g →
      ∃ d : (conormalPresheaf φ₁).obj (op Y),
        conormalMapOfFac φ₁ φ₂ ψ hψ (op Y) d = (conormalPresheaf φ₂).map g.op c := by
  obtain ⟨x, rfl⟩ := (kernelIdeal φ₂ (op X)).toCotangent_surjective c
  obtain ⟨S, hS, hlift⟩ := exists_covering_kernelIdeal_lift J hψ (x : A₂.obj (op X)) x.2
  refine ⟨S, hS, fun Y g hg ↦ ?_⟩
  obtain ⟨y, hy, hy'⟩ := hlift Y g hg
  refine ⟨(kernelIdeal φ₁ (op Y)).toCotangent ⟨y, hy⟩, ?_⟩
  change (kernelIdeal φ₂ (op Y)).toCotangent ⟨ψ.app (op Y) y, _⟩ =
    (kernelIdeal φ₂ (op Y)).toCotangent ⟨A₂.map g.op (x : A₂.obj (op X)), _⟩
  exact congrArg (kernelIdeal φ₂ (op Y)).toCotangent (Subtype.ext hy')

include hψ in
/-- A local section of `I₁/I₁²` killed by the induced map restricts to zero on a covering
sieve. -/
theorem vanishingSieve_mem_of_conormalMapOfFac_eq_zero [Presheaf.IsLocallySurjective J ψ]
    [Presheaf.IsLocallyInjective J ψ] {X : C} (c : (conormalPresheaf φ₁).obj (op X))
    (hc : conormalMapOfFac φ₁ φ₂ ψ hψ (op X) c = 0) :
    vanishingSieve (conormalPresheaf φ₁) c ∈ J X := by
  obtain ⟨z, rfl⟩ := (kernelIdeal φ₁ (op X)).toCotangent_surjective c
  have hmem : ψ.app (op X) (z : A₁.obj (op X)) ∈ kernelIdeal φ₂ (op X) :=
    (app_apply_of_fac hψ (op X) _).trans z.2
  have hz : ψ.app (op X) (z : A₁.obj (op X)) ∈ kernelIdeal φ₂ (op X) ^ 2 :=
    (Ideal.toCotangent_eq_zero _ ⟨_, hmem⟩).mp hc
  obtain ⟨S, hS, hlift⟩ := exists_covering_sq_lift J hψ _ hz
  refine J.transitive hS _ (fun Y g hg ↦ ?_)
  obtain ⟨y, hy, hy'⟩ := hlift Y g hg
  have hyz : ψ.app (op Y) y = ψ.app (op Y) (A₁.map g.op (z : A₁.obj (op X))) :=
    hy'.trans (NatTrans.naturality_apply ψ g.op (z : A₁.obj (op X))).symm
  refine J.superset_covering (fun Z k hk ↦ ?_) (Presheaf.equalizerSieve_mem J ψ y _ hyz)
  have hzero : A₁.map k.op (A₁.map g.op (z : A₁.obj (op X))) ∈ kernelIdeal φ₁ (op Z) ^ 2 :=
    hk ▸ presheafMap_mem_kernelIdeal_sq k.op hy
  have hcomp : (conormalPresheaf φ₁).map (k ≫ g).op
        ((kernelIdeal φ₁ (op X)).toCotangent z) =
      (kernelIdeal φ₁ (op Z)).toCotangent
        ⟨A₁.map k.op (A₁.map g.op (z : A₁.obj (op X))), map_kernel φ₁ k.op
          (map_kernel φ₁ g.op z.2)⟩ := by
    rw [op_comp]
    exact (conormalPresheaf φ₁).map_comp_apply g.op k.op _
  exact hcomp.trans ((Ideal.toCotangent_eq_zero _ _).mpr hzero)

end Stacks.Sites.Conormal

end
