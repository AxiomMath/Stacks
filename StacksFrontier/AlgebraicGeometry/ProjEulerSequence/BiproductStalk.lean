module

public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic

/-!
# The stalk of a finite direct sum of sheaves of modules

Let `O` be a sheaf of rings on a topological space, `F` a finite family of sheaves of
`O`-modules and `x` a point. Taking stalks at `x` is an additive functor, so the identity
`∑ⱼ πⱼ ≫ ιⱼ = 1` of a finite biproduct survives it: an element of the stalk of `⨁ F` is the
sum of the images of its components, and the components of the inclusion of a summand are a
Kronecker delta. The stalk of `⨁ F` is therefore the product of the stalks of the `F j`.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.stalkBiproductLift`: the element of the stalk of `⨁ F`
  assembled from one stalk element in each summand.

## Main results

* `AlgebraicGeometry.SheafOfModules.stalkBiproductLift_stalkMap_π`: assembling an element of
  the stalk of `⨁ F` from its own components returns it.
* `AlgebraicGeometry.SheafOfModules.stalkMap_π_stalkMap_ι_self` and
  `AlgebraicGeometry.SheafOfModules.stalkMap_π_stalkMap_ι_ne`: on stalks, the inclusion of the
  `j`-th summand followed by the `k`-th projection is the identity when `j = k` and zero
  otherwise.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.SheafOfModules

/-- A finite sum of maps of modules acts on an element as the sum of their values. -/
private theorem moduleCat_hom_sum {Λ : Type u} [Ring Λ] {M N : ModuleCat.{u} Λ} {ι : Type*}
    (s : Finset ι) (f : ι → (M ⟶ N)) (m : M) :
    (∑ a ∈ s, f a).hom m = ∑ a ∈ s, (f a).hom m := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    simp

variable {X : TopCat.{u}}
  (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X)
  {J : Type} [Fintype J] (F : J → _root_.SheafOfModules.{u} O) [HasBiproduct F]

/-- The element of the stalk of `⨁ F` assembled from a family of stalk elements, one in each
summand: the sum of their images under the inclusions of the summands. -/
def stalkBiproductLift (c : ∀ j, ↥(stalkObj O x (F j))) : ↥(stalkObj O x (⨁ F)) :=
  ∑ j : J, (stalkMap O x (biproduct.ι F j)).hom (c j)

/-- `stalkBiproductLift O x F c` is the sum over `j` of the image of `c j` under the stalk map
of the inclusion of the `j`-th summand. -/
theorem stalkBiproductLift_def (c : ∀ j, ↥(stalkObj O x (F j))) :
    stalkBiproductLift O x F c = ∑ j : J, (stalkMap O x (biproduct.ι F j)).hom (c j) :=
  rfl

/-- Stalk maps of composable morphisms compose, evaluated at an element. -/
private theorem stalkMap_comp_apply {A B C : _root_.SheafOfModules.{u} O} (f : A ⟶ B)
    (g : B ⟶ C) (m : ↥(stalkObj O x A)) :
    (stalkMap O x g).hom ((stalkMap O x f).hom m) = (stalkMap O x (f ≫ g)).hom m := by
  rw [show stalkMap O x (f ≫ g) = stalkMap O x f ≫ stalkMap O x g from
    (stalkFunctor O x).map_comp f g]
  rfl

/-- An element of the stalk of `⨁ F` is the sum of the images of its own components under the
inclusions of the summands. -/
theorem stalkBiproductLift_stalkMap_π (d : ↥(stalkObj O x (⨁ F))) :
    stalkBiproductLift O x F (fun j => (stalkMap O x (biproduct.π F j)).hom d) = d := by
  have : (stalkFunctor O x).Additive := stalkFunctor_additive O x
  have key : ∑ j : J, (stalkFunctor O x).map (biproduct.π F j ≫ biproduct.ι F j) =
      𝟙 (stalkObj O x (⨁ F)) := by
    rw [← Functor.map_sum, biproduct.total]
    exact (stalkFunctor O x).map_id _
  have h1 : stalkBiproductLift O x F (fun j => (stalkMap O x (biproduct.π F j)).hom d) =
      ∑ j : J, ((stalkFunctor O x).map (biproduct.π F j ≫ biproduct.ι F j)).hom d := by
    rw [stalkBiproductLift_def]
    exact Finset.sum_congr rfl fun j _ => stalkMap_comp_apply O x _ _ d
  rw [h1, show ∑ j : J, ((stalkFunctor O x).map (biproduct.π F j ≫ biproduct.ι F j)).hom d =
    (∑ j : J, (stalkFunctor O x).map (biproduct.π F j ≫ biproduct.ι F j)).hom d from
    (moduleCat_hom_sum _ _ d).symm, key]
  rfl

omit [Fintype J] in
/-- On stalks, the inclusion of the `j`-th summand followed by the `j`-th projection is the
identity. -/
theorem stalkMap_π_stalkMap_ι_self (j : J) (m : ↥(stalkObj O x (F j))) :
    (stalkMap O x (biproduct.π F j)).hom ((stalkMap O x (biproduct.ι F j)).hom m) = m := by
  rw [stalkMap_comp_apply, biproduct.ι_π_self]
  exact congrArg (fun φ : stalkObj O x (F j) ⟶ stalkObj O x (F j) => φ.hom m)
    ((stalkFunctor O x).map_id _)

omit [Fintype J] in
/-- On stalks, the inclusion of the `j`-th summand followed by the `k`-th projection vanishes
for `j ≠ k`. -/
theorem stalkMap_π_stalkMap_ι_ne {j k : J} (hjk : j ≠ k) (m : ↥(stalkObj O x (F j))) :
    (stalkMap O x (biproduct.π F k)).hom ((stalkMap O x (biproduct.ι F j)).hom m) = 0 := by
  rw [stalkMap_comp_apply, biproduct.ι_π_ne _ hjk]
  exact congrArg (fun φ : stalkObj O x (F j) ⟶ stalkObj O x (F k) => φ.hom m)
    ((stalkFunctor O x).map_zero _ _)

end AlgebraicGeometry.SheafOfModules

end
