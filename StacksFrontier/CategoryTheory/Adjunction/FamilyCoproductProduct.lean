module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Pi.Basic

/-!
# The coproduct of a family of left adjoints is left adjoint to the product of the right adjoints

Let `L i ⊣ R i` be a family of adjunctions between two fixed categories `C` and `D`, indexed by
a type `ι`. Then the functor `X ↦ ∐ i, (L i).obj X` is left adjoint to the functor
`Y ↦ ∏ i, (R i).obj Y`, because
`Hom(∐ᵢ Lᵢ X, Y) ≃ ∏ᵢ Hom(Lᵢ X, Y) ≃ ∏ᵢ Hom(X, Rᵢ Y) ≃ Hom(X, ∏ᵢ Rᵢ Y)`.

## Main definitions

* `CategoryTheory.Adjunction.sigmaFamily` — the functor `X ↦ ∐ i, (L i).obj X`.
* `CategoryTheory.Adjunction.piFamily` — the functor `Y ↦ ∏ i, (R i).obj Y`.
* `CategoryTheory.Adjunction.sigmaFamilyAdjunction` — the adjunction `∐ᵢ Lᵢ ⊣ ∏ᵢ Rᵢ`.
* `CategoryTheory.Adjunction.rightAdjointIsoPiFamily` — a right adjoint of a functor isomorphic
  to `∐ᵢ Lᵢ` is isomorphic to `∏ᵢ Rᵢ`.

## Implementation notes

The two functors are assembled from `CategoryTheory.Functor.pi'` and
`CategoryTheory.Limits.Sigma.functor`, respectively `CategoryTheory.Limits.Pi.functor`, so that
`sigmaFamily L` is definitionally the composite `Functor.pi' L ⋙ Sigma.functor ι`. This is the
shape in which a stalk decomposition of a functor arrives, which is what the last result is for:
it turns an isomorphism identifying a left adjoint with `∐ᵢ Lᵢ` into a formula for its right
adjoint.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Adjunction

variable {ι : Type w} {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (L : ι → C ⥤ D) (R : ι → D ⥤ C)

/-- The coproduct `X ↦ ∐ i, (L i).obj X` of a family of functors `L i : C ⥤ D`. -/
@[simps]
public def sigmaFamily [HasCoproductsOfShape ι D] : C ⥤ D where
  obj X := ∐ fun i => (L i).obj X
  map f := Limits.Sigma.map fun i => (L i).map f

/-- The product `Y ↦ ∏ i, (R i).obj Y` of a family of functors `R i : D ⥤ C`. -/
@[simps]
public def piFamily [HasProductsOfShape ι C] : D ⥤ C where
  obj Y := ∏ᶜ fun i => (R i).obj Y
  map g := Limits.Pi.map fun i => (R i).map g

variable [HasCoproductsOfShape ι D] [HasProductsOfShape ι C]

/-- The transposition `Hom(∐ᵢ Lᵢ X, Y) ≃ Hom(X, ∏ᵢ Rᵢ Y)` built from the transpositions of the
family: a map out of a coproduct is a family of maps, and a map into a product likewise. -/
@[simps]
public def sigmaFamilyHomEquiv (adj : ∀ i, L i ⊣ R i) (X : C) (Y : D) :
    ((∐ fun i => (L i).obj X) ⟶ Y) ≃ (X ⟶ ∏ᶜ fun i => (R i).obj Y) where
  toFun f := Pi.lift fun i =>
    (adj i).homEquiv X Y (Sigma.ι (fun j => (L j).obj X) i ≫ f)
  invFun g := Sigma.desc fun i =>
    ((adj i).homEquiv X Y).symm (g ≫ Pi.π (fun j => (R j).obj Y) i)
  left_inv f := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [Sigma.ι_desc, Pi.lift_comp_π, Equiv.symm_apply_apply]
  right_inv g := by
    refine Pi.hom_ext _ _ fun i => ?_
    rw [Pi.lift_comp_π, Sigma.ι_desc, Equiv.apply_symm_apply]

variable (adj : ∀ i, L i ⊣ R i)

/-- The transposition is natural in the source: it intertwines precomposition with
`CategoryTheory.Limits.Sigma.map`. -/
public theorem sigmaFamilyHomEquiv_naturality_left_symm {X' X : C} {Y : D} (f : X' ⟶ X)
    (g : X ⟶ ∏ᶜ fun i => (R i).obj Y) :
    (sigmaFamilyHomEquiv L R adj X' Y).symm (f ≫ g) =
      (Limits.Sigma.map fun i => (L i).map f) ≫ (sigmaFamilyHomEquiv L R adj X Y).symm g := by
  refine Sigma.hom_ext _ _ fun i => ?_
  rw [sigmaFamilyHomEquiv_symm_apply, Sigma.ι_desc, Category.assoc, Sigma.ι_map_assoc,
    sigmaFamilyHomEquiv_symm_apply, Sigma.ι_desc]
  exact (adj i).homEquiv_naturality_left_symm _ _

/-- The transposition is natural in the target: it intertwines postcomposition with
`CategoryTheory.Limits.Pi.map`. -/
public theorem sigmaFamilyHomEquiv_naturality_right {X : C} {Y Y' : D}
    (f : (∐ fun i => (L i).obj X) ⟶ Y) (g : Y ⟶ Y') :
    sigmaFamilyHomEquiv L R adj X Y' (f ≫ g) =
      sigmaFamilyHomEquiv L R adj X Y f ≫ Limits.Pi.map fun i => (R i).map g := by
  refine Pi.hom_ext _ _ fun i => ?_
  rw [sigmaFamilyHomEquiv_apply, Pi.lift_comp_π, Category.assoc, Pi.map_π,
    sigmaFamilyHomEquiv_apply, Pi.lift_comp_π_assoc,
    ← Category.assoc (Sigma.ι (fun j => (L j).obj X) i) f g]
  exact (adj i).homEquiv_naturality_right _ _

/-- The coproduct of a family of left adjoints is left adjoint to the product of the right
adjoints: `(∐ᵢ Lᵢ) ⊣ (∏ᵢ Rᵢ)`. -/
public def sigmaFamilyAdjunction : sigmaFamily L ⊣ piFamily R :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Y := sigmaFamilyHomEquiv L R adj X Y
      homEquiv_naturality_left_symm f g :=
        sigmaFamilyHomEquiv_naturality_left_symm L R adj f g
      homEquiv_naturality_right f g := sigmaFamilyHomEquiv_naturality_right L R adj f g }

/-- A right adjoint of a functor isomorphic to the coproduct `∐ᵢ Lᵢ` of a family of left
adjoints is isomorphic to the product `∏ᵢ Rᵢ` of the right adjoints. -/
public def rightAdjointIsoPiFamily {F : C ⥤ D} {G : D ⥤ C}
    (adjFG : F ⊣ G) (e : F ≅ sigmaFamily L) : G ≅ piFamily R :=
  rightAdjointUniq adjFG (ofNatIsoLeft (sigmaFamilyAdjunction L R adj) e.symm)

end CategoryTheory.Adjunction

end
