module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.ExactSequence
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit

/-!
# The cohomology sequence of a derived inverse limit

Let `A` be an abelian category with countable products, let `(Kₙ)` be an inverse system in
`D(A)` indexed by `ℕ`, and let `L` be a derived limit of that system, so that `L` sits in a
distinguished triangle `L ⟶ ∏ Kₙ ⟶ ∏ Kₙ ⟶ L⟦1⟧` whose middle map is the difference map
`(xₙ) ↦ (xₙ - fₙ₊₁(xₙ₊₁))`. Taking the long exact homology sequence of that triangle gives a
five-term exact sequence

`Hᵖ⁻¹(∏ Kₙ) ⟶ Hᵖ⁻¹(∏ Kₙ) ⟶ Hᵖ(L) ⟶ Hᵖ(∏ Kₙ) ⟶ Hᵖ(∏ Kₙ)`

whose outer two maps are the homology of the difference map. If moreover countable products in
`A` are exact then homology commutes with them, so the four outer terms may be rewritten as
products of homology objects, and under that rewriting the outer maps become the difference map
of the inverse system of homology objects.

## Main definitions

* `Stacks.DerivedLimit.inverseSystemDifference` is the difference map `1 - shift` on the product
  of a countable inverse system in a preadditive category.

## Main results

* `Stacks.DerivedLimit.map_inverseSystemDifference_comp_piComparison`: an additive functor
  intertwines the difference map of a system with the difference map of the image system,
  through the canonical product comparison.
* `Stacks.DerivedLimit.exists_cohomologySequence_of_isDerivedLimit`: the five-term exact
  cohomology sequence of a derived limit, with the product comparisons for the homology functor
  as the identifications of the outer terms.

## Implementation notes

The source of this statement (Stacks 0947(7), see the references) is set on a site with enough
weakly contractible objects, where the exactness of countable products of sheaves of modules is
what makes homology commute with them. That hypothesis is used *only* through the exactness of
countable products, so the statement is proved here for an arbitrary abelian category `A`
satisfying `HasExactLimitsOfShape (Discrete ℕ) A`. Specializing `A` to the category of modules
over a sheaf of rings on such a site recovers the source's statement, and nothing about sites,
sheaves or weak contractibility is needed here.

`HasProductsOfShape ℕ (DerivedCategory A)` is listed as a hypothesis even though it is
derivable from the other three (it is Stacks 07KC(1),
`Stacks.DerivedProducts.hasProductsOfShape_nat`). Taking it as a hypothesis rather than deriving it
in the file keeps the products appearing in the statement the ones instance search finds at the
use site, instead of a second, propositionally equal copy produced by the derivation; the two
are not definitionally equal, and `piComparison` mentions them.

The outer two maps and the connecting map are pinned, not existentially quantified: the two
identifications `ePrev` and `eCur` are required to have the canonical `piComparison` morphisms
as their forward maps, so the sequence produced is the canonical one and not merely some exact
sequence with the right objects. The first and last morphisms of the triangle remain
existentially quantified, exactly as in `IsDerivedLimit`, because a derived limit determines
them only up to non-unique isomorphism.

The exactness assertion is the five-term exactness of the long homology sequence, obtained as
the `δ₀` of Mathlib's `Functor.homologySequenceComposableArrows₅` for the homological functor
`DerivedCategory.homologyFunctor A 0` with its `ShiftSequence ℤ` structure, transported along
the product comparisons. Since `mk₅ f g h i j` is by definition `(mk₄ g h i j).precomp f`, that
`δ₀` is the required `mk₄` on the nose.

## References

* [Stacks Project, Tag 0945](https://stacks.math.columbia.edu/tag/0945), Proposition 0947(7)
* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
* [Stacks Project, Tag 07KC](https://stacks.math.columbia.edu/tag/07KC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u v' u'

namespace Stacks.DerivedLimit

/-- The difference morphism `1 - shift` on the product of a countable inverse system `(Kₙ)` in a
preadditive category: its `n`-th component sends `(xᵢ)` to `xₙ - fₙ₊₁(xₙ₊₁)`. -/
public noncomputable def inverseSystemDifference {D : Type u} [Category.{v} D] [Preadditive D]
    (K : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ => K.obj ⟨n⟩] :
    (∏ᶜ fun n : ℕ => K.obj ⟨n⟩) ⟶ (∏ᶜ fun n : ℕ => K.obj ⟨n⟩) :=
  Pi.lift fun n : ℕ =>
    Pi.π (fun n : ℕ => K.obj ⟨n⟩) n -
      Pi.π (fun n : ℕ => K.obj ⟨n⟩) (n + 1) ≫
        K.map (homOfLE (Nat.le_succ n)).op

/-- The `n`-th component of `inverseSystemDifference K` is `πₙ - πₙ₊₁ ≫ fₙ₊₁`. -/
@[reassoc (attr := simp)]
public lemma inverseSystemDifference_comp_π {D : Type u} [Category.{v} D] [Preadditive D]
    (K : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ => K.obj ⟨n⟩] (n : ℕ) :
    inverseSystemDifference K ≫ Pi.π (fun n : ℕ => K.obj ⟨n⟩) n =
      Pi.π (fun n : ℕ => K.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ => K.obj ⟨n⟩) (n + 1) ≫
          K.map (homOfLE (Nat.le_succ n)).op :=
  Pi.lift_π _ _

/-- An additive functor intertwines the difference map of a countable inverse system with the
difference map of the image system, through the canonical product comparison. -/
public lemma map_inverseSystemDifference_comp_piComparison
    {D : Type u} [Category.{v} D] [Preadditive D]
    {B : Type u'} [Category.{v'} B] [Preadditive B] (F : D ⥤ B) [F.Additive]
    (K : ℕᵒᵖ ⥤ D) [HasProduct fun n : ℕ => K.obj ⟨n⟩] [HasProductsOfShape ℕ B] :
    F.map (inverseSystemDifference K) ≫ piComparison F (fun n : ℕ => K.obj ⟨n⟩) =
      piComparison F (fun n : ℕ => K.obj ⟨n⟩) ≫ inverseSystemDifference (K ⋙ F) := by
  have key (n : ℕ) :
      inverseSystemDifference (K ⋙ F) ≫ Pi.π (fun n : ℕ => F.obj (K.obj ⟨n⟩)) n =
        Pi.π (fun n : ℕ => F.obj (K.obj ⟨n⟩)) n -
          Pi.π (fun n : ℕ => F.obj (K.obj ⟨n⟩)) (n + 1) ≫
            F.map (K.map (homOfLE (Nat.le_succ n)).op) :=
    Pi.lift_π _ _
  refine Pi.hom_ext _ _ fun n ↦ ?_
  rw [Category.assoc, piComparison_comp_π, ← F.map_comp, inverseSystemDifference_comp_π,
    Category.assoc, key, F.map_sub, Functor.map_comp, Preadditive.comp_sub,
    piComparison_comp_π, piComparison_comp_π_assoc]

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
  [HasProductsOfShape ℕ A] [HasExactLimitsOfShape (Discrete ℕ) A]
  [HasProductsOfShape ℕ (DerivedCategory A)]

/-- **The cohomology sequence of a derived inverse limit.** Let `(Kₙ)` be an inverse system in
`D(A)` indexed by `ℕ`, with `A` abelian with exact countable products, and let `L` be a derived
limit of `(Kₙ)`. Then for every `p` the sequence

`∏ Hᵖ⁻¹(Kₙ) ⟶ ∏ Hᵖ⁻¹(Kₙ) ⟶ Hᵖ(L) ⟶ ∏ Hᵖ(Kₙ) ⟶ ∏ Hᵖ(Kₙ)`

is exact, where both outer maps are the difference map of the corresponding inverse system of
homology objects, the second map is the connecting morphism of the derived-limit triangle and
the third is induced by its structural morphism `L ⟶ ∏ Kₙ`, both transported along the
canonical product comparisons for the homology functor. -/
public theorem exists_cohomologySequence_of_isDerivedLimit
    (K : ℕᵒᵖ ⥤ DerivedCategory A) (L : DerivedCategory A) (hL : IsDerivedLimit K L) (p : ℤ) :
    ∃ (a : L ⟶ ∏ᶜ fun n : ℕ => K.obj ⟨n⟩)
      (δ : (∏ᶜ fun n : ℕ => K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧),
      let T := Triangle.mk a (inverseSystemDifference K) δ
      ∃ (_hT : T ∈ distTriang (DerivedCategory A))
        (ePrev : (DerivedCategory.homologyFunctor A (p - 1)).obj
            (∏ᶜ fun n : ℕ => K.obj ⟨n⟩) ≅
          ∏ᶜ fun n : ℕ => (DerivedCategory.homologyFunctor A (p - 1)).obj (K.obj ⟨n⟩))
        (eCur : (DerivedCategory.homologyFunctor A p).obj (∏ᶜ fun n : ℕ => K.obj ⟨n⟩) ≅
          ∏ᶜ fun n : ℕ => (DerivedCategory.homologyFunctor A p).obj (K.obj ⟨n⟩)),
        ePrev.hom = piComparison (DerivedCategory.homologyFunctor A (p - 1))
            (fun n : ℕ => K.obj ⟨n⟩) ∧
          eCur.hom = piComparison (DerivedCategory.homologyFunctor A p)
            (fun n : ℕ => K.obj ⟨n⟩) ∧
          (ComposableArrows.mk₄
            (inverseSystemDifference (K ⋙ DerivedCategory.homologyFunctor A (p - 1)))
            (ePrev.inv ≫ DerivedCategory.HomologySequence.δ T (p - 1) p (by omega))
            ((DerivedCategory.homologyFunctor A p).map a ≫ eCur.hom)
            (inverseSystemDifference (K ⋙ DerivedCategory.homologyFunctor A p))).Exact := by
  obtain ⟨a, δ, hT⟩ := hL
  have hPrev : IsIso (piComparison (DerivedCategory.homologyFunctor A (p - 1))
      (fun n : ℕ => K.obj ⟨n⟩)) :=
    Stacks.DerivedProducts.isIso_piComparison_homologyFunctor (I := ℕ) _ _
  have hCur : IsIso (piComparison (DerivedCategory.homologyFunctor A p)
      (fun n : ℕ => K.obj ⟨n⟩)) :=
    Stacks.DerivedProducts.isIso_piComparison_homologyFunctor (I := ℕ) _ _
  let ePrev := asIso (piComparison (DerivedCategory.homologyFunctor A (p - 1))
    (fun n : ℕ => K.obj ⟨n⟩))
  let eCur := asIso (piComparison (DerivedCategory.homologyFunctor A p)
    (fun n : ℕ => K.obj ⟨n⟩))
  refine ⟨a, δ, hT, ePrev, eCur, rfl, rfl, ?_⟩
  have h5 := ((DerivedCategory.homologyFunctor A 0).homologySequenceComposableArrows₅_exact
    (Triangle.mk a (inverseSystemDifference K) δ) hT (p - 1) p (by omega)).δ₀
  refine ComposableArrows.exact_of_iso ?_ h5
  refine ComposableArrows.isoMk₄ ePrev ePrev (Iso.refl _) eCur eCur ?_ ?_ ?_ ?_
  · exact map_inverseSystemDifference_comp_piComparison
      (DerivedCategory.homologyFunctor A (p - 1)) K
  · exact (Category.comp_id _).trans (Iso.hom_inv_id_assoc ePrev
      (DerivedCategory.HomologySequence.δ (Triangle.mk a (inverseSystemDifference K) δ)
        (p - 1) p (by omega))).symm
  · exact (Category.id_comp _).symm
  · exact map_inverseSystemDifference_comp_piComparison
      (DerivedCategory.homologyFunctor A p) K

end Stacks.DerivedLimit

end
