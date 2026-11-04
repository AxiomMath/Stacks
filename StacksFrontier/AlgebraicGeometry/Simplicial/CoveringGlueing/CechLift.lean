module

public import StacksFrontier.AlgebraicGeometry.Simplicial.CoveringGlueing.LocallyGivenOfCovering
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Cech

/-!
# The Čech object of a covering, lifted to the indexing category of its locally given objects

Let `f_i : U_i ⟶ X` be a family of arrows of a category with fibre products. Its Čech object is
the simplicial object of `SR(C/X)` whose degree-`n` term is `{U_{i_0} ×_X ⋯ ×_X U_{i_n} → X}`.
Every member of that family comes with an arrow to a member `U_{i_0}` of the family, the
projection to the first factor, so the Čech object lifts along the forgetful functor from the
indexing category `AlgebraicGeometry.RingedSite.CoveringGlueing.IndexCategory` of objects of `C/X`
equipped with an arrow to a member of the family. This is the simplicial object of `SR(B)` to which
the second proof of Stacks 0GMG applies Stacks 0DCA.

## Main definitions

* `AlgebraicGeometry.RingedSite.CoveringGlueing.family`: the family `{U_i → X}` as an object of
  `SR(C/X)`.
* `AlgebraicGeometry.RingedSite.CoveringGlueing.cechLift`: the lift of its Čech object.

## Main results

* `AlgebraicGeometry.RingedSite.CoveringGlueing.cechLift_comp_mapFormalCoproduct`: the lift
  recovers the Čech object, on the nose.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.RingedSite.CoveringGlueing
variable {X : RingedSite.{u, u, u}} [HasPullbacks X.C] {X₀ : X.C} {ι : Type u} {U : ι → X.C}
  (f : ∀ i, U i ⟶ X₀)

/-- The slice `C/X` has finite products: a final object and, from the fibre products of `C`,
binary products. -/
instance : HasFiniteProducts (Over X₀) :=
  letI : HasTerminal (Over X₀) := Over.over_hasTerminal X₀
  letI : HasBinaryProducts (Over X₀) := Over.ConstructProducts.over_binaryProduct_of_pullback
  hasFiniteProducts_of_has_binary_and_terminal

/-- The family `{U_i → X}`, as an object of `SR(C/X)`. -/
def family : FormalCoproduct.{u} (Over X₀) := ⟨ι, fun i => Over.mk (f i)⟩

omit [HasPullbacks X.C] in
/-- Applying an induced functor componentwise is faithful on morphisms of formal coproducts. -/
theorem _root_.CategoryTheory.Limits.FormalCoproduct.mapFormalCoproduct_inducedFunctor_map_injective
    {C : Type*} {D : Type*} [Category D] {G : C → D}
    {X Y : FormalCoproduct.{u} (InducedCategory D G)} {a b : X ⟶ Y}
    (h : (Stacks.CategoryTheory.Hypercovering.mapFormalCoproduct (inducedFunctor G)).map a =
      (Stacks.CategoryTheory.Hypercovering.mapFormalCoproduct (inducedFunctor G)).map b) :
    a = b := by
  obtain ⟨af, aφ⟩ := a
  obtain ⟨bf, bφ⟩ := b
  change (FormalCoproduct.Hom.mk af (fun i => (aφ i).hom) :
      (Stacks.CategoryTheory.Hypercovering.mapFormalCoproduct (inducedFunctor G)).obj X ⟶
        (Stacks.CategoryTheory.Hypercovering.mapFormalCoproduct (inducedFunctor G)).obj Y) =
    (FormalCoproduct.Hom.mk bf (fun i => (bφ i).hom) :
      (Stacks.CategoryTheory.Hypercovering.mapFormalCoproduct (inducedFunctor G)).obj X ⟶
        (Stacks.CategoryTheory.Hypercovering.mapFormalCoproduct (inducedFunctor G)).obj Y) at h
  injection h with h1 h2
  subst h1
  have h3 : (fun i => (aφ i).hom) = (fun i => (bφ i).hom) := eq_of_heq h2
  have h4 : aφ = bφ := funext fun i => InducedCategory.hom_ext (congrFun h3 i)
  subst h4
  rfl

/-- The object of the indexing category attached to a member of the degree-`n` term of the Čech
object: the member itself, with its projection to the first factor. -/
def cechIndex (n : SimplexCategoryᵒᵖ) (t : ((family f).cech.obj n).I) : Index f where
  V := ((family f).cech.obj n).obj t
  i := t (0 : Fin (n.unop.len + 1))
  a := (Pi.π ((family f).obj ∘ t) (0 : Fin (n.unop.len + 1))).left
  w := Over.w (Pi.π ((family f).obj ∘ t) (0 : Fin (n.unop.len + 1)))

/-- The map of `cechLift` along a simplex map: that of the Čech object, read in the indexing
category. -/
def cechLiftMap {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    (⟨((family f).cech.obj n).I, cechIndex f n⟩ : FormalCoproduct.{u} (IndexCategory f)) ⟶
      ⟨((family f).cech.obj m).I, cechIndex f m⟩ :=
  ⟨((family f).cech.map φ).f, fun t => InducedCategory.homMk (((family f).cech.map φ).φ t)⟩

/-- **The Čech object of the family, lifted to the indexing category.** -/
def cechLift : SimplicialObject (FormalCoproduct.{u} (IndexCategory f)) where
  obj n := ⟨((family f).cech.obj n).I, cechIndex f n⟩
  map φ := cechLiftMap f φ
  map_id n := FormalCoproduct.mapFormalCoproduct_inducedFunctor_map_injective
    ((family f).cech.map_id n |>.trans (CategoryTheory.Functor.map_id
      (Stacks.CategoryTheory.Hypercovering.mapFormalCoproduct (inducedFunctor _))
      (⟨((family f).cech.obj n).I, cechIndex f n⟩ : FormalCoproduct.{u} (IndexCategory f))).symm)
  map_comp φ ψ := FormalCoproduct.mapFormalCoproduct_inducedFunctor_map_injective
    ((family f).cech.map_comp φ ψ |>.trans (CategoryTheory.Functor.map_comp
      (Stacks.CategoryTheory.Hypercovering.mapFormalCoproduct (inducedFunctor _))
      (cechLiftMap f φ) (cechLiftMap f ψ)).symm)

/-- The lift of the Čech object recovers the Čech object, on the nose. -/
theorem cechLift_comp_mapFormalCoproduct :
    cechLift f ⋙ Stacks.CategoryTheory.Hypercovering.mapFormalCoproduct (inducedFunctor _) =
      (family f).cech :=
  rfl

end AlgebraicGeometry.RingedSite.CoveringGlueing

end
