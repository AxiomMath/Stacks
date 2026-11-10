module

public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Reflexive.DualMap

/-!
# Duality is additive, and turns a finite biproduct into a finite biproduct

Let `X` be a scheme. Taking the dual `F ↦ F^∨ = SheafHom(F, 𝒪_X)` of an `𝒪_X`-module is
contravariant and *additive*: `(f + g)^∨ = f^∨ + g^∨` on morphisms. An additive contravariant
functor carries a biproduct to a biproduct, because the one identity characterising a biproduct
among bicones in a preadditive category — `∑ⱼ πⱼ ≫ ιⱼ = 𝟙` — is a sum of composites, and both
sums and composites are preserved (composites with the order reversed, which exchanges the two
families of structure maps of the bicone and so leaves the identity in the same shape).

## Main definitions

* `Stacks.AlgebraicGeometry.ReflexiveModules.dualMapAddHom` — the dual of a morphism, as an
  additive map on each hom group.
* `Stacks.AlgebraicGeometry.ReflexiveModules.dualBicone` — the bicone on the duals of a family
  obtained from a bicone on the family, with vertex the dual of the vertex.

## Main results

* `Stacks.AlgebraicGeometry.ReflexiveModules.dualMap_add`, `dualMap_zero` and `dualMap_sum` —
  additivity of duality on morphisms.
* `Stacks.AlgebraicGeometry.ReflexiveModules.dualBicone_isBilimit` — the dual of a finite
  biproduct is the biproduct of the duals.

## Implementation notes

Additivity is checked on values: `dualPairing F (f^∨ t) W x = dualPairing G t W (f x)` holds by
definitional unfolding (`dualPairing_dualMap`), addition of morphisms of `𝒪_X`-modules is
pointwise on sections (`AlgebraicGeometry.Scheme.Modules.Hom.add_app`), and what is left is
additivity of one local functional, i.e. `map_add`. Vanishing is then deduced from additivity
rather than proved again, since `dualPairing` at `0` needs the same unfolding with the type of
the zero section supplied by hand.

The biproduct statement is phrased with `CategoryTheory.Limits.isBilimitOfTotal`, whose
hypothesis is exactly the sum identity above; the index type is `Finite` and the `Fintype`
needed to form the sum is supplied classically.

## References

* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

variable {X : Scheme.{u}}

/-! ### Additivity -/

/-- **Duality is additive on morphisms.** -/
public theorem dualMap_add {F G : X.Modules} (f g : F ⟶ G) :
    dualMap (f + g) = dualMap f + dualMap g := by
  refine hom_ext_dualSheaf fun U x W y => ?_
  simp only [dualPairing_dualMap, Scheme.Modules.Hom.add_app]
  change _ = dualPairing _ (Scheme.Modules.Hom.app (dualMap f) U x
      + Scheme.Modules.Hom.app (dualMap g) U x) W y
  change _ = dualPairing _ (Scheme.Modules.Hom.app (dualMap f) U x) W y
      + dualPairing _ (Scheme.Modules.Hom.app (dualMap g) U x) W y
  simp only [dualPairing_dualMap]
  exact map_add _ _ _

/-- **Duality sends the zero morphism to the zero morphism.** -/
public theorem dualMap_zero {F G : X.Modules} : dualMap (0 : F ⟶ G) = 0 :=
  have h : dualMap (0 : F ⟶ G) + (0 : dualSheaf G ⟶ dualSheaf F)
      = dualMap (0 : F ⟶ G) + dualMap (0 : F ⟶ G) := by
    rw [← dualMap_add, add_zero, add_zero]
  (add_left_cancel h).symm

/-- The dual of a morphism, as an additive map on hom groups. -/
public def dualMapAddHom (F G : X.Modules) : (F ⟶ G) →+ (dualSheaf G ⟶ dualSheaf F) where
  toFun := dualMap
  map_zero' := dualMap_zero
  map_add' := dualMap_add

/-- The additive map `dualMapAddHom F G` sends a morphism `f` to its dual `dualMap f`. -/
@[simp] public theorem dualMapAddHom_apply {F G : X.Modules} (f : F ⟶ G) :
    dualMapAddHom F G f = dualMap f := rfl

/-- **Duality is additive on finite sums of morphisms.** -/
public theorem dualMap_sum {F G : X.Modules} {ι : Type*} (s : Finset ι) (f : ι → (F ⟶ G)) :
    dualMap (∑ j ∈ s, f j) = ∑ j ∈ s, dualMap (f j) :=
  map_sum (dualMapAddHom F G) f s

/-! ### Duality on a finite biproduct -/

/-- The bicone on the duals of a family, obtained by dualising a bicone on the family. The two
families of structure maps are exchanged, since duality is contravariant. -/
public def dualBicone {ι : Type*} {F : ι → X.Modules} (b : Bicone F) :
    Bicone (fun j => dualSheaf (F j)) where
  pt := dualSheaf b.pt
  π j := dualMap (b.ι j)
  ι j := dualMap (b.π j)
  ι_π j j' := by
    rw [← dualMap_comp]
    by_cases h : j = j'
    · subst h
      rw [bicone_ι_π_self, dualMap_id]
      simp
    · rw [bicone_ι_π_ne b (Ne.symm h), dualMap_zero]
      simp [h]

/-- The vertex of `dualBicone b` is the dual of the vertex of `b`. -/
@[simp] public theorem dualBicone_pt {ι : Type*} {F : ι → X.Modules} (b : Bicone F) :
    (dualBicone b).pt = dualSheaf b.pt := rfl

/-- The `j`-th projection of `dualBicone b` is the dual of the `j`-th inclusion of `b`. -/
@[simp] public theorem dualBicone_π {ι : Type*} {F : ι → X.Modules} (b : Bicone F) (j : ι) :
    (dualBicone b).π j = dualMap (b.ι j) := rfl

/-- The `j`-th inclusion of `dualBicone b` is the dual of the `j`-th projection of `b`. -/
@[simp] public theorem dualBicone_ι {ι : Type*} {F : ι → X.Modules} (b : Bicone F) (j : ι) :
    (dualBicone b).ι j = dualMap (b.π j) := rfl

/-- **The dual of a finite biproduct is the biproduct of the duals.** -/
public def dualBicone_isBilimit {ι : Type*} [Finite ι] {F : ι → X.Modules} (b : Bicone F)
    (hb : b.IsBilimit) : (dualBicone b).IsBilimit :=
  letI : Fintype ι := Fintype.ofFinite ι
  isBilimitOfTotal _ <| by
    have h : ∑ j : ι, (dualBicone b).π j ≫ (dualBicone b).ι j
        = dualMap (∑ j : ι, b.π j ≫ b.ι j) := by
      rw [dualMap_sum]
      exact Finset.sum_congr rfl fun j _ => (dualMap_comp (b.π j) (b.ι j)).symm
    rw [h, Limits.IsBilimit.total hb, dualMap_id]
    rfl

end Stacks.AlgebraicGeometry.ReflexiveModules

end

end
