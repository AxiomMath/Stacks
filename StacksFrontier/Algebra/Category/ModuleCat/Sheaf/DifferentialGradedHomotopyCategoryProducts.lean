module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedProductHomotopy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedProducts

/-!
# Products in the homotopy category of differential graded modules

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. The homotopy category of right differential graded `A`-modules has arbitrary
products, and they are the images of the products of right differential graded modules.

## Main results

* `SheafOfModules.DifferentialGradedModule.HomotopyCategory.hasProducts`: the homotopy category
  admits arbitrary products.

## Implementation notes

The product cone is the image under the quotient functor of the product of right differential
graded modules, which exists by
`SheafOfModules.DifferentialGradedModule.hasProducts`. Its universal property has two halves,
and each uses one property of the quotient functor: a morphism into the product is lifted from
a preimage of the given family, which needs the quotient functor to be *full*, and two such
lifts agree because morphisms into a product which are homotopic after every projection are
homotopic, which is
`SheafOfModules.DifferentialGradedModule.homotopyIntoProduct`.

The index type lies in the universe of the module sections, which is where the category of
right differential graded modules has its products.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring and the algebra pieces are independent;
a ringed site `X` is the case `R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FS2](https://stacks.math.columbia.edu/tag/0FS2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- The image under the quotient functor of the product of a family of right differential
graded modules, as a cone in the homotopy category. -/
private noncomputable def quotientProductCone {A : DifferentialGradedAlgebra.{t, a} R}
    {ι : Type m} (F : Discrete ι ⥤ HomotopyCategory.{t, a, m} A) : Cone F := by
  classical
  let q := HomotopyCategory.quotient A
  let N : ι → DifferentialGradedModule.{t, a, m} A := fun i => (F.obj ⟨i⟩).as
  refine {
    pt := q.obj (∏ᶜ N)
    π := {
      app := fun i => q.map (Pi.π N i.as)
      naturality := ?_ } }
  rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl⟩⟩
  simp

/-- The image of a product of right differential graded modules is a product in the homotopy
category. -/
private noncomputable def quotientProductIsLimit {A : DifferentialGradedAlgebra.{t, a} R}
    {ι : Type m} (F : Discrete ι ⥤ HomotopyCategory.{t, a, m} A) :
    IsLimit (quotientProductCone F) := by
  classical
  let q := HomotopyCategory.quotient A
  let N : ι → DifferentialGradedModule.{t, a, m} A := fun i => (F.obj ⟨i⟩).as
  refine {
    lift := fun s => q.map (Pi.lift (fun i => q.preimage (s.π.app ⟨i⟩)))
    fac := ?_
    uniq := ?_ }
  · intro s i
    change q.map (Pi.lift (fun j => q.preimage (s.π.app ⟨j⟩))) ≫
      q.map (Pi.π N i.as) = s.π.app i
    rw [← q.map_comp, Pi.lift_comp_π]
    simp [q]
  · intro s m hm
    let g : s.pt.as ⟶ ∏ᶜ N := Pi.lift (fun i => q.preimage (s.π.app ⟨i⟩))
    let m₀ : s.pt.as ⟶ ∏ᶜ N := q.preimage m
    have hpre : q.map m₀ = m := q.map_preimage m
    have hcomp (i : ι) : q.map (m₀ ≫ Pi.π N i) = q.map (g ≫ Pi.π N i) := by
      calc
        q.map (m₀ ≫ Pi.π N i) = q.map m₀ ≫ q.map (Pi.π N i) := by simp
        _ = m ≫ q.map (Pi.π N i) := by rw [hpre]; rfl
        _ = s.π.app ⟨i⟩ := hm ⟨i⟩
        _ = q.map (g ≫ Pi.π N i) := by simp [g, q]
    have hmEq := (HomotopyCategory.quotient_map_eq_iff m₀ g).mpr
      ⟨homotopyIntoProduct N (∏ᶜ N) (Pi.π N) (productIsProduct N)
        fun i => (HomotopyCategory.quotient_map_eq_iff _ _).mp (hcomp i)⟩
    change q.map m₀ = q.map g at hmEq
    change m = q.map g
    exact hpre.symm.trans hmEq

namespace HomotopyCategory

/-- The homotopy category of right differential graded modules admits arbitrary products. -/
@[stacks 0FS2 "homotopy_products"]
noncomputable instance hasProducts (A : DifferentialGradedAlgebra.{t, a} R) :
    HasProducts.{m} (HomotopyCategory.{t, a, m} A) :=
  fun _ => ⟨fun F => ⟨⟨quotientProductCone F, quotientProductIsLimit F⟩⟩⟩

end HomotopyCategory

end DifferentialGradedModule

end SheafOfModules
