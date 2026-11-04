module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Tactic.LinearCombination

/-!
# Adding a derivation to a homomorphism of sheaves of commutative rings

Let `J` be a Grothendieck topology on a category `C`, let `R` and `A` be sheaves of commutative
rings on `(C, J)` and let `f : R ⟶ A` be a homomorphism. A *derivation along `f` with square zero
values* is a natural family of maps `δ_U : R(U) ⟶ A(U)` which is additive, satisfies the Leibniz
rule `δ(xy) = f(x) δ(y) + f(y) δ(x)` with the scalars acting through `f`, and whose values
multiply to zero. For such a `δ` the sectionwise sum `x ↦ f(x) + δ(x)` is again a homomorphism of
sheaves of commutative rings.

## Main definitions

* `Stacks.Sites.RingSheafDerivation`: a natural, additive, Leibniz family of maps `R(U) ⟶ A(U)`
  along `f : R ⟶ A` whose values multiply to zero.
* `Stacks.Sites.RingSheafDerivation.add`: the homomorphism `x ↦ f(x) + δ(x)` of sheaves of
  commutative rings.

## Main results

* `Stacks.Sites.RingSheafDerivation.add_apply`: the value of the sum on a section.
* `Stacks.Sites.RingSheafDerivation.toFun_one` and
  `Stacks.Sites.RingSheafDerivation.toFun_zero`: a derivation kills `1` and `0`.
* `Stacks.Sites.RingSheafDerivation.add_zero_eq`: adding the zero derivation to `f` gives `f`.
* `Stacks.Sites.RingSheafDerivation.add_comp_eq`: a map killing the values of the derivation does
  not see the modification.
* `Stacks.Sites.RingSheafDerivation.precomp_add_eq`: a map on whose image the derivation vanishes
  does not see the modification.
* `Stacks.Sites.RingSheafDerivation.eq_of_add_eq`: a derivation is determined by its sum with `f`.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace Stacks.Sites

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A derivation along a homomorphism `f : R ⟶ A` of sheaves of commutative rings, with values
whose products vanish: a natural additive family `R(U) ⟶ A(U)` satisfying the Leibniz rule with
scalars acting through `f`. -/
structure RingSheafDerivation {R A : Sheaf J CommRingCat.{w}} (f : R ⟶ A) where
  /-- The underlying sectionwise map. -/
  toFun : ∀ U : Cᵒᵖ, R.obj.obj U → A.obj.obj U
  /-- The family is additive on sections. -/
  map_add' : ∀ (U : Cᵒᵖ) (x y : R.obj.obj U), toFun U (x + y) = toFun U x + toFun U y
  /-- The Leibniz rule, the scalars acting through `f`. -/
  leibniz : ∀ (U : Cᵒᵖ) (x y : R.obj.obj U),
    toFun U (x * y) =
      (f.hom.app U).hom x * toFun U y + (f.hom.app U).hom y * toFun U x
  /-- The values of the family multiply to zero. -/
  mul_eq_zero : ∀ (U : Cᵒᵖ) (x y : R.obj.obj U), toFun U x * toFun U y = 0
  /-- The family commutes with the restriction maps of the site. -/
  naturality : ∀ {U V : Cᵒᵖ} (h : U ⟶ V) (x : R.obj.obj U),
    (A.obj.map h).hom (toFun U x) = toFun V ((R.obj.map h).hom x)

/-- Two homomorphisms of sheaves of commutative rings agreeing on every section are equal. -/
private theorem sheaf_hom_ext_apply {P Q : Sheaf J CommRingCat.{w}} {g h : P ⟶ Q}
    (H : ∀ (U : Cᵒᵖ) (x : P.obj.obj U), (g.hom.app U).hom x = (h.hom.app U).hom x) : g = h :=
  Sheaf.hom_ext (NatTrans.ext (funext fun U => CommRingCat.hom_ext (RingHom.ext (H U))))

namespace RingSheafDerivation

variable {R A : Sheaf J CommRingCat.{w}} {f : R ⟶ A} (δ : RingSheafDerivation f)

/-- A derivation kills the zero section. -/
theorem toFun_zero (U : Cᵒᵖ) : δ.toFun U 0 = 0 := by
  simpa using δ.map_add' U 0 0

/-- A derivation kills the unit section. -/
theorem toFun_one (U : Cᵒᵖ) : δ.toFun U 1 = 0 := by
  simpa using δ.leibniz U 1 1

/-- The homomorphism of sheaves of commutative rings obtained by adding a derivation with square
zero values to `f`: it is `x ↦ f(x) + δ(x)` on every object of the site. -/
noncomputable def add : R ⟶ A :=
  ObjectProperty.homMk
    { app := fun U => CommRingCat.ofHom
        { toFun := fun x => (f.hom.app U).hom x + δ.toFun U x
          map_one' := by rw [δ.toFun_one U, add_zero, map_one]
          map_zero' := by rw [δ.toFun_zero U, add_zero, map_zero]
          map_add' := fun x y => by rw [δ.map_add' U x y, map_add, add_add_add_comm]
          map_mul' := fun x y => by
            rw [map_mul, δ.leibniz U x y]
            linear_combination -δ.mul_eq_zero U x y }
      naturality := fun {U V} h => by
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        have hf : (f.hom.app V).hom ((R.obj.map h).hom x) =
            (A.obj.map h).hom ((f.hom.app U).hom x) :=
          ConcreteCategory.congr_hom (f.hom.naturality h) x
        change (f.hom.app V).hom ((R.obj.map h).hom x) +
            δ.toFun V ((R.obj.map h).hom x) =
          (A.obj.map h).hom ((f.hom.app U).hom x + δ.toFun U x)
        rw [map_add, ← hf, δ.naturality h x] }

/-- The value of `δ.add` on a section `x` is `f(x) + δ(x)`. -/
@[simp]
theorem add_apply (U : Cᵒᵖ) (x : R.obj.obj U) :
    (δ.add.hom.app U).hom x = (f.hom.app U).hom x + δ.toFun U x := rfl

/-- The zero derivation. -/
instance : Zero (RingSheafDerivation f) where
  zero :=
    { toFun := fun _ _ => 0
      map_add' := fun _ _ _ => (add_zero (0 : _)).symm
      leibniz := fun _ _ _ => by rw [mul_zero, mul_zero, add_zero]
      mul_eq_zero := fun _ _ _ => mul_zero 0
      naturality := fun _ _ => map_zero _ }

/-- The value of the zero derivation. -/
@[simp]
theorem zero_toFun (U : Cᵒᵖ) (x : R.obj.obj U) :
    (0 : RingSheafDerivation f).toFun U x = 0 := rfl

/-- Adding the zero derivation to `f` gives `f`. -/
theorem add_zero_eq : (0 : RingSheafDerivation f).add = f := by
  refine sheaf_hom_ext_apply fun U x => ?_
  rw [add_apply, zero_toFun, add_zero]

/-- If `q : A ⟶ P` kills every value of `δ` then `(f + δ) ≫ q = f ≫ q`. -/
theorem add_comp_eq {P : Sheaf J CommRingCat.{w}} (q : A ⟶ P)
    (hδ : ∀ (U : Cᵒᵖ) (x : R.obj.obj U), (q.hom.app U).hom (δ.toFun U x) = 0) :
    δ.add ≫ q = f ≫ q := by
  refine sheaf_hom_ext_apply fun U x => ?_
  show (q.hom.app U).hom ((δ.add.hom.app U).hom x) = (q.hom.app U).hom ((f.hom.app U).hom x)
  rw [δ.add_apply U x, map_add, hδ U x, add_zero]

/-- If `δ` vanishes on the image of `g : R₀ ⟶ R` then `g ≫ (f + δ) = g ≫ f`. -/
theorem precomp_add_eq {R₀ : Sheaf J CommRingCat.{w}} (g : R₀ ⟶ R)
    (hδ : ∀ (U : Cᵒᵖ) (t : R₀.obj.obj U), δ.toFun U (g.hom.app U t) = 0) :
    g ≫ δ.add = g ≫ f := by
  refine sheaf_hom_ext_apply fun U t => ?_
  show (δ.add.hom.app U).hom (g.hom.app U t) = (f.hom.app U).hom (g.hom.app U t)
  rw [δ.add_apply U _, hδ U t, add_zero]

/-- Two derivations agreeing on every section are equal. -/
theorem ext_apply {δ ε : RingSheafDerivation f}
    (h : ∀ (U : Cᵒᵖ) (x : R.obj.obj U), δ.toFun U x = ε.toFun U x) : δ = ε := by
  cases δ; cases ε
  congr 1
  exact funext₂ h

/-- Two derivations whose sums with `f` agree are equal. -/
theorem eq_of_add_eq {δ ε : RingSheafDerivation f} (h : δ.add = ε.add) : δ = ε :=
  ext_apply fun U x => add_left_cancel (a := (f.hom.app U).hom x) <| by
    rw [← δ.add_apply, ← ε.add_apply, h]

end RingSheafDerivation

end Stacks.Sites

end
