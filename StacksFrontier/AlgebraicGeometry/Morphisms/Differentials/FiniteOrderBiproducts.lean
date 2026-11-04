module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteOrderCategory

/-!
# Finite biproducts of finite-order differential operators

Let `a : X ⟶ S` be a morphism of schemes. A finite family of quasi-coherent `𝒪_X`-modules has a
biproduct in the category of finite-order differential operators on `X/S`: the underlying module
is the biproduct of the underlying modules, which is again quasi-coherent, and the inclusions and
projections are the module-sheaf inclusions and projections, read as operators of order zero.

## Main definitions

* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.homOrderZeroAddMonoidHom` reads a
  morphism of the underlying modules as a finite-order operator, additively in the morphism.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.biproductObj` is the biproduct of a
  finite family, as an object of the category.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.bicone` is the bicone of its
  inclusions and projections.

## Main results

* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.hasBiproduct`: a finite family of
  objects has a biproduct.
* `AlgebraicGeometry.FiniteOrderDifferentialOperatorCategory.hasFiniteBiproducts`: the category
  has finite biproducts.

## References

* [Stacks Project, Tag 01BF](https://stacks.math.columbia.edu/tag/01BF)
* [Stacks Project, Tag 0G46](https://stacks.math.columbia.edu/tag/0G46)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace FiniteOrderDifferentialOperatorCategory

variable {X S : Scheme.{u}} {a : X ⟶ S}

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- A morphism of the underlying modules, read as a differential operator of order zero,
depends additively on the morphism. -/
noncomputable def homOrderZeroAddMonoidHom
    (F G : FiniteOrderDifferentialOperatorCategory a) :
    (F.module ⟶ G.module) →+ (F ⟶ G) where
  toFun f := homOrderZero f
  map_zero' := by apply Subtype.ext; funext U; ext s; rfl
  map_add' _ _ := by apply Subtype.ext; funext U; ext s; rfl

/-- The identity of the underlying module is the identity operator. -/
@[simp]
lemma homOrderZeroAddMonoidHom_id (F : FiniteOrderDifferentialOperatorCategory a) :
    homOrderZeroAddMonoidHom F F (𝟙 F.module) = 𝟙 F := rfl

/-- Reading module morphisms as order-zero operators is compatible with composition. -/
@[simp]
lemma homOrderZeroAddMonoidHom_comp {F G H : FiniteOrderDifferentialOperatorCategory a}
    (f : F.module ⟶ G.module) (g : G.module ⟶ H.module) :
    homOrderZeroAddMonoidHom F G f ≫ homOrderZeroAddMonoidHom G H g =
      homOrderZeroAddMonoidHom F H (f ≫ g) := rfl

/-- A biproduct of finitely many quasi-coherent modules is quasi-coherent. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.isQuasicoherent_biproduct {J : Type} [Finite J]
    (g : J → X.Modules) [∀ j, (g j).IsQuasicoherent] : (⨁ g).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit
    (D := Discrete.functor g) (fun k => (inferInstance : (g k.as).IsQuasicoherent))
    (biproduct.isColimit g)

/-- The biproduct of a finite family of quasi-coherent modules, regarded as an object of the
category of finite-order differential operators. -/
noncomputable abbrev biproductObj {J : Type} [Finite J]
    (g : J → FiniteOrderDifferentialOperatorCategory a) :
    FiniteOrderDifferentialOperatorCategory a :=
  { module := ⨁ fun j => (g j).module }

/-- The inclusions and projections of the biproduct of the underlying modules, read as
differential operators of order zero. -/
noncomputable abbrev bicone {J : Type} [Finite J]
    (g : J → FiniteOrderDifferentialOperatorCategory a) : Bicone g where
  pt := biproductObj g
  π j := homOrderZeroAddMonoidHom _ _ (biproduct.π (fun j => (g j).module) j)
  ι j := homOrderZeroAddMonoidHom _ _ (biproduct.ι (fun j => (g j).module) j)
  ι_π j j' := by
    rw [homOrderZeroAddMonoidHom_comp]
    by_cases h : j = j'
    · subst h
      simp
    · simp [h, biproduct.ι_π_ne _ h]

/-- The projections and inclusions of the bicone sum to the identity. -/
lemma bicone_total {J : Type} [Fintype J]
    (g : J → FiniteOrderDifferentialOperatorCategory a) :
    ∑ j : J, (bicone g).π j ≫ (bicone g).ι j = 𝟙 (bicone g).pt := by
  rw [Finset.sum_congr rfl fun j _ => homOrderZeroAddMonoidHom_comp (F := biproductObj g)
    (H := biproductObj g) _ _, ← map_sum, biproduct.total, homOrderZeroAddMonoidHom_id]

/-- A finite family of objects has a biproduct: the biproduct of the underlying modules, with
the inclusions and projections read as operators of order zero. -/
instance hasBiproduct {J : Type} [Finite J]
    (g : J → FiniteOrderDifferentialOperatorCategory a) : HasBiproduct g := by
  cases nonempty_fintype J
  exact hasBiproduct_of_total (bicone g) (bicone_total g)

/-- The category of finite-order differential operators on `X/S` has finite biproducts. -/
instance hasFiniteBiproducts :
    HasFiniteBiproducts (FiniteOrderDifferentialOperatorCategory a) :=
  ⟨fun _ => { has_biproduct := fun g => hasBiproduct g }⟩

end FiniteOrderDifferentialOperatorCategory

end AlgebraicGeometry

end
