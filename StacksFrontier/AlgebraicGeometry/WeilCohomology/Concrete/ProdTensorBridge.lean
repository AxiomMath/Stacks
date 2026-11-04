module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.Monoidal
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.BlowupTrace
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DisjointUnionIso

/-!
# The products of smooth projective schemes are the monoidal ones

The category `Stacks.WeilCohomology.(SmoothProjectiveScheme k).FullSubcategory` of smooth
projective schemes over a field `k` has one product `X ×_k Y` and one point `Spec k`, with two
vocabularies for them:

* `Concrete/Monoidal.lean` (before Stacks 0FG7) makes
  `(SmoothProjectiveScheme k).FullSubcategory` a symmetric monoidal category as a full monoidal
  subcategory of `Over (Spec k)` with its cartesian monoidal structure, with tensor product
  `X ⊗ Y`, unit `𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)`, constraints `α_`, `λ_`, `ρ_`
  and braiding `β_`.
* `Concrete/WeilData.lean` (the data of Section 0FHA) defines
  `Stacks.WeilCohomology.SmoothProjectiveScheme.prod X Y` as `X ⊗ Y` and
  `Stacks.WeilCohomology.SmoothProjectiveScheme.point k` as `𝟙_ _`, and adds the projections
  `fst`, `snd` and the diagonal `diag` written on the fibre product; the later files add
  `prodLift` (`Concrete/DisjointUnionIdempotent.lean`), `prodMapLeft`
  (`Concrete/DisjointUnionIso.lean`) and `prodMap` (`Concrete/BlowupTrace.lean`).

This file compares the two vocabularies. Each comparison holds by `rfl` at default transparency,
but not at reducible-and-instances transparency (`prod` and `point` are `def`s), so `rw`/`simp`
do not see through them on their own and these lemmas are the way to pass between the two
spellings. None of them is `@[simp]`: neither spelling is declared normal, and both keep their
own simp lemmas (`fst_left`, `tensorObj_left`, ...).

## Main results

* `Stacks.WeilCohomology.SmoothProjectiveScheme.prod_eq_tensorObj`: `prod X Y = X ⊗ Y`.
* `Stacks.WeilCohomology.SmoothProjectiveScheme.point_eq_tensorUnit`:
  `point k = 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory)`.
* `prodMap_eq_tensorHom`, `prodMapLeft_eq_whiskerRight`: `prodMap f g = f ⊗ₘ g` and
  `prodMapLeft f W = f ▷ W`.
* `braiding_hom_eq_prodLift`, `associator_hom_eq_prodLift`, `leftUnitor_hom_eq_snd`,
  `rightUnitor_hom_eq_fst`: the constraints of the monoidal structure in terms of `prodLift`,
  `fst` and `snd`.
* `diag_eq_prodLift`: `diag X = prodLift (𝟙 X) (𝟙 X)`.
* `fst_hom`, `snd_hom`, `prodLift_hom`, `diag_hom`: on the underlying morphisms of
  `Over (Spec k)`, `fst`, `snd`, `prodLift` and `diag` are the cartesian projections, the
  cartesian lift and the cartesian diagonal of `Over.cartesianMonoidalCategory`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry

universe u

namespace Stacks.WeilCohomology.SmoothProjectiveScheme

variable {k : Type u} [Field k]

/-! ### Objects -/

/-- **The product `X ×_k Y` of `Concrete/WeilData.lean` is the tensor product of
`Concrete/Monoidal.lean`.** -/
theorem prod_eq_tensorObj (X Y : (SmoothProjectiveScheme k).FullSubcategory) : prod X Y = X ⊗ Y
    := rfl

/-- **The point `Spec k` of `Concrete/WeilData.lean` is the tensor unit of
`Concrete/Monoidal.lean`.** -/
theorem point_eq_tensorUnit : point k = 𝟙_ ((SmoothProjectiveScheme k).FullSubcategory) := rfl

/-! ### Morphisms -/

/-- The product `f × g` of `Concrete/BlowupTrace.lean` is the tensor product of morphisms. -/
theorem prodMap_eq_tensorHom {X' X Y' Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X' ⟶ X)
    (g : Y' ⟶ Y) : prodMap f g = f ⊗ₘ g := rfl

/-- The product `f × id_W` of `Concrete/DisjointUnionIso.lean` is the right whiskering
`f ▷ W`. -/
theorem prodMapLeft_eq_whiskerRight {X Z : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Z)
    (W : (SmoothProjectiveScheme k).FullSubcategory) : prodMapLeft f W = f ▷ W := rfl

/-- The diagonal `X ⟶ X × X` has components the identity of `X`. -/
theorem diag_eq_prodLift (X : (SmoothProjectiveScheme k).FullSubcategory) :
    diag X = prodLift (𝟙 X) (𝟙 X) := rfl

/-- The commutativity constraint `X × Y ≅ Y × X` is the factor switch `(pr₂, pr₁)`. -/
theorem braiding_hom_eq_prodLift (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (β_ X Y).hom = prodLift (snd X Y) (fst X Y) := rfl

/-- The associativity constraint `(X × Y) × Z ≅ X × (Y × Z)` is `(pr₁ pr₁, (pr₂ pr₁, pr₂))`. -/
theorem associator_hom_eq_prodLift (X Y Z : (SmoothProjectiveScheme k).FullSubcategory) :
    (α_ X Y Z).hom = prodLift (fst (prod X Y) Z ≫ fst X Y)
      (prodLift (fst (prod X Y) Z ≫ snd X Y) (snd (prod X Y) Z)) := rfl

/-- The left unit constraint `Spec k × X ≅ X` is the second projection. -/
theorem leftUnitor_hom_eq_snd (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (λ_ X).hom = snd (point k) X := rfl

/-- The right unit constraint `X × Spec k ≅ X` is the first projection. -/
theorem rightUnitor_hom_eq_fst (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (ρ_ X).hom = fst X (point k) := rfl

/-! ### The cartesian structure of `Over (Spec k)`

`Concrete/Monoidal.lean` obtains the monoidal structure from the cartesian monoidal structure
`Over.cartesianMonoidalCategory` of `Over (Spec k)`, switched on locally there; it is switched on
locally here too, to compare `fst`, `snd`, `prodLift` and `diag` with its projections, lift and
diagonal. -/

section Cartesian

attribute [local instance] Over.cartesianMonoidalCategory

/-- `pr₁ : X × Y ⟶ X` is the first cartesian projection of `Over (Spec k)`. -/
theorem fst_hom (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (fst X Y).hom = CartesianMonoidalCategory.fst X.obj Y.obj := rfl

/-- `pr₂ : X × Y ⟶ Y` is the second cartesian projection of `Over (Spec k)`. -/
theorem snd_hom (X Y : (SmoothProjectiveScheme k).FullSubcategory) :
    (snd X Y).hom = CartesianMonoidalCategory.snd X.obj Y.obj := rfl

/-- `prodLift f g : T ⟶ X × Y` is the cartesian lift of `Over (Spec k)`. -/
theorem prodLift_hom {T X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : T ⟶ X) (g : T ⟶ Y) :
    (prodLift f g).hom = CartesianMonoidalCategory.lift f.hom g.hom := rfl

/-- The diagonal `X ⟶ X × X` is the cartesian diagonal of `Over (Spec k)`. -/
theorem diag_hom (X : (SmoothProjectiveScheme k).FullSubcategory) :
    (diag X).hom = CartesianMonoidalCategory.lift (𝟙 X.obj) (𝟙 X.obj) := rfl

end Cartesian

end Stacks.WeilCohomology.SmoothProjectiveScheme
