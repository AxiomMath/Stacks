module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.AcyclicCoveringFamily
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.AcyclicObject
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProducts
import StacksCore.Tactic.StacksAttribute

/-! # Cohomology commutes with a derived inverse limit over an acyclic covering family

Let `(C, O)` be a ringed site, `(Kₙ)` an inverse system of objects of the unbounded derived
category of `O`-modules with derived limit `L`, and `B` a class of objects of `C` large enough to
cover every object of `C`. Assume that for every `U ∈ B` and every `q` the cohomology sheaf
`H^q(Kₙ)` has no higher cohomology over `U`, and that the inverse system of its sections over `U`
has vanishing `R¹lim`. Then `H^q(L) = lim H^q(Kₙ)`.

The proof is the one the source gives, and both of its halves are already in the library. Over a
member `U` of `B` the hypercohomology `H^q(U, Kₙ)` is the module of sections of `H^q(Kₙ)` over
`U` -- the hypercohomology edge morphism is invertible there, which is
`Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover`. Feeding
that into
`Stacks.Cohomology.DerivedLimitAcyclic.cohomology_isLimit_of_isDerivedLimit_of_acyclic_cover`,
whose only input beyond the hypotheses below is exactly this invertibility, gives the result.

## Main results

* `Stacks.Cohomology.DerivedLimitAcyclic.isLimit_cohomology_of_isDerivedLimit_of_acyclic_cover`:
  the degree-`q` cohomology sheaf of a derived inverse limit is the inverse limit of the
  degree-`q` cohomology sheaves of the system, exhibited as a limit cone.

## Implementation notes

The universes of the site, its morphisms, the structure ring and the modules all coincide,
because the sections functor `Stacks.Cohomology.Localization.sectionsOverObject` in whose terms
the vanishing of `R¹lim` is stated is itself only available at that profile.

The statement carries no instance hypotheses beyond those of the ringed site itself. Enough
injectives in `SheafOfModules O` follows from the Grothendieck abelianness already assumed, by
`CategoryTheory.IsGrothendieckAbelian.enoughInjectives`, and the countable products of the
derived category that the derived-limit triangle names come from
`Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules`, made available to
synthesis here as a local instance.

## References

* [Stacks Project, Tag 0A09](https://stacks.math.columbia.edu/tag/0A09)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry

namespace Stacks.Cohomology.DerivedLimitAcyclic

universe u g

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.HypercohomologyEdge
open Stacks.Cohomology.Localization

attribute [local instance] evaluation_additive

attribute [local instance]
  Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **Stacks Project Tag 0A09.** Cohomology commutes with a derived inverse limit if there is a
class of objects covering the site on which all positive cohomology of the cohomology sheaves
vanishes and the towers of their sections have vanishing first derived inverse limit.

The conclusion records the canonical limiting cone: the legs of the cone on the system of
degree-`q` cohomology sheaves are induced by the projections of a derived-limit triangle for
`L`. -/
@[stacks 0A09]
theorem isLimit_cohomology_of_isDerivedLimit_of_acyclic_cover
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hL : IsDerivedLimit K L)
    (B : ObjectProperty X.C)
    (hB : X.J.HasEnoughObjects B)
    (hacyclic : ∀ U, B U → ∀ q : ℤ, ∀ n : ℕ, ∀ r : ℕ, 0 < r →
      haveI := evaluation_additive (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
      IsZero (((SheafOfModules.evaluation
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op U)).rightDerived r).obj
        ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).obj
          (K.obj ⟨n⟩))))
    (hlimOne : ∀ U, B U → ∀ q : ℤ,
      IsZero (Rlim.firstDerivedLimit
        (K ⋙ DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q ⋙
          sectionsOverObject X U)))
    (q : ℤ) :
    ∃ p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩,
      (∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
        Triangle.mk p (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
              K.map (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang
            (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) ∧
      ∃ τ : (Functor.const ℕᵒᵖ).obj
          ((DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).obj L) ⟶
          K ⋙ DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q,
        (∀ n : ℕ, τ.app ⟨n⟩ =
          (DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).map
            (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) ∧
        Nonempty (IsLimit (Cone.mk _ τ)) :=
  cohomology_isLimit_of_isDerivedLimit_of_acyclic_cover X K L hL B hB hacyclic hlimOne
    (fun M U hU hvan m ↦
      isIso_hypercohomologyEdge_app_of_acyclic_cover
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U M B hB hvan hU m) q

end Stacks.Cohomology.DerivedLimitAcyclic

end
