module

public import StacksFrontier.CategoryTheory.Sites.Modules.InverseImage.AbelianSheaf
public import StacksFrontier.CategoryTheory.Monoidal.Cartesian.Bimultiplicative

/-!
# Biadditive pairings of abelian sheaves from internal pairings

Abelian sheaves on a site are the commutative group objects in its sheaves of sets
(`CategoryTheory.Sites.AbelianSheaf.equivalence`). A bimultiplicative morphism
`β : R ⊗ S ⟶ T` of commutative group objects of sheaves of sets, in the sense of
`CategoryTheory.IsBimultiplicative`, is read on sections as a family of biadditive maps
`R(U) × S(U) → T(U)`, natural in `U`, between the abelian groups of sections of the abelian sheaves
`externalSheaf R`, `externalSheaf S`, `externalSheaf T`. This is the form in which the pairing of
coefficients `ℱ_ρ ⊗ ℱ_{ρ^∨} → ℤ/ℓ^kℤ` of the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) is extracted from Tag 0DV5 (2).

## Main definitions

* `CategoryTheory.Sites.AbelianSheaf.sectionsPairing`: the biadditive pairing of sections.

## Main results

* `CategoryTheory.Sites.AbelianSheaf.sectionsPairing_naturality`: it commutes with restriction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory

universe w v u

namespace CategoryTheory.Sites.AbelianSheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The cartesian structure on sheaves of sets used for
`CategoryTheory.Sites.AbelianSheaf.equivalence`. -/
noncomputable local instance (priority := high) cartesianSheafTypePairing :
    CartesianMonoidalCategory (Sheaf J (Type w)) :=
  .ofHasFiniteProducts
/-- Its braiding. -/
noncomputable local instance (priority := high) braidedSheafTypePairing :
    BraidedCategory (Sheaf J (Type w)) :=
  .ofCartesianMonoidalCategory
/-- The braided structure of `sheafToPresheaf` used for `externalSheaf`. -/
noncomputable local instance braidedSheafToPresheafPairing :
    (sheafToPresheaf J (Type w)).Braided :=
  .ofChosenFiniteProducts _

variable {J} {R S T : CommGrp (Sheaf J (Type w))} {β : R.X ⊗ S.X ⟶ T.X}

/-- The morphism of presheaves of sets read off from `β`: on sections over `U` it sends a pair
`(x, y)` of sections of the underlying sheaves of `R` and `S` to a section of that of `T`. -/
abbrev presheafPairing (β : R.X ⊗ S.X ⟶ T.X) :
    (sheafToPresheaf J (Type w)).obj R.X ⊗ (sheafToPresheaf J (Type w)).obj S.X ⟶
      (sheafToPresheaf J (Type w)).obj T.X :=
  Functor.LaxMonoidal.μ (sheafToPresheaf J (Type w)) R.X S.X ≫
    (sheafToPresheaf J (Type w)).map β

open scoped Obj in
/-- **The pairing of sections attached to a bimultiplicative `β`**: on sections over `U` of the
abelian sheaves attached to `R`, `S` and `T`, it is biadditive. -/
def sectionsPairing (hβ : IsBimultiplicative β) (U : Cᵒᵖ) :
    ((externalSheaf J).obj R).obj.obj U →+ ((externalSheaf J).obj S).obj.obj U →+
      ((externalSheaf J).obj T).obj.obj U :=
  have h := (isBimultiplicative_iff_app _).1 (hβ.map (sheafToPresheaf J (Type w))) U
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk'
    (fun y => (presheafPairing β).app U (Additive.toMul x, Additive.toMul y))
    (fun y y' => h.2 x y y')) (fun x x' => by
      ext y
      exact h.1 x x' y)

/-- **The pairing of sections commutes with restriction.** -/
theorem sectionsPairing_naturality (hβ : IsBimultiplicative β) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : ((externalSheaf J).obj R).obj.obj U) (y : ((externalSheaf J).obj S).obj.obj U) :
    ((externalSheaf J).obj T).obj.map f (sectionsPairing hβ U x y) =
      sectionsPairing hβ V (((externalSheaf J).obj R).obj.map f x)
        (((externalSheaf J).obj S).obj.map f y) :=
  (ConcreteCategory.congr_hom (CC := fun X : Type w => X) ((presheafPairing β).naturality f)
    (Additive.toMul x, Additive.toMul y)).symm

end CategoryTheory.Sites.AbelianSheaf
