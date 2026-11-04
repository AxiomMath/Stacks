module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CupProductSquare
public import StacksFrontier.AlgebraicGeometry.Cohomology.FlasqueReductionOfTheCupProductSquare

/-!
# Cancelling the Čech augmentation in the cup-product square of [Stacks, Tag 0FKV]

Let `(S, 𝒪_S)` be a ringed space, put `A = Γ(S, 𝒪_S)`, let `𝒰 : S = ⋃ U i` be an open covering
and let `𝒦^•`, `ℳ^•` be bounded below complexes of `𝒪_S`-modules.  The second paragraph of the
proof of [Stacks, Tag 0FKV] treats complexes `𝒦^•` and `ℳ^•` of *flasque* modules and
compares the tag's square with the diagram displayed just before the tag -- the one whose top
left corner is `Γ(S, 𝒦^•) ⊗^𝐋_A Γ(S, ℳ^•)` -- along the Čech augmentation of
[Stacks, Tag 07M9], which is invertible in `D(A)` for such a complex.

This file performs that cancellation for the square
`Stacks.Cech.CupProductSquare.CupProductSquareCommutes`: for a flasque pair the assertion of
Tag 0FKV is *equivalent* to the equality of the two legs precomposed with the augmentation in both
tensor factors.

## Main results

* `Stacks.Cech.CupProductSquare.isIso_tensorBase_map_sectionsToTotalCechDerived_of_isFlasque`:
  for a pair of bounded below complexes of flasque modules the Čech augmentation of
  [Stacks, Tag 07M9], applied in both tensor factors of `- ⊗^𝐋_A -`, is invertible in `D(A)`.
* `Stacks.Cech.CupProductSquare.cupProductSquareCommutes_iff_of_isFlasque`: **the flasque
  cancellation.**  For such a pair, `Stacks.Cech.CupProductSquare.CupProductSquareCommutes` holds
  if and only if the two legs agree after precomposition with that augmentation.
* `Stacks.Cech.CupProductSquare.exists_flasquePlusResolution`: every bounded below pair maps to
  a pair of objects of `CochainComplex.Plus` with flasque terms, the flasqueness spelled as the
  cancellation consumes it; the maps are those of the Godement resolution of
  [Stacks, Tag 0FKT].

Together with `Stacks.Cech.CupProductSquare.sectionsToTotalCechDerived_comp_cechRightLeg`, which
rewrites the right-hand leg after that precomposition as the right-hand column of the source's
preceding diagram, this reduces the flasque case of Tag 0FKV to the commutativity of that
preceding diagram -- which is [Stacks, Tag 0FP3] for the morphism from `S` to a point.

## Use

This is the second paragraph of the proof of [Stacks, Tag 0FKV]; the flasque hypothesis is the
one introduced by the first paragraph
(`Stacks.Cohomology.FlasqueReduction.exists_flasqueResolution_isIso_baseSections_map`).  The tag
itself is `Stacks.Cech.CupProductSquare.cupProductSquareCommutes`.

## Implementation notes

The augmentation is the module-valued `Stacks.Cech.Linear.sectionsToTotalCechDerived`, in the
spelling `Stacks.Cech.CupProductSquare.sectionsToTotalCechDerived_comp_cechRightLeg` uses, so that
the two statements compose with no transport.  Its invertibility on a bounded below complex of
flasque modules is `Stacks.Cech.Linear.isIso_sectionsToTotalCechDerived_of_isFlasque`; that it
stays invertible after `- ⊗^𝐋_A -` is `CategoryTheory.isIso_prod_iff` followed by
`CategoryTheory.Functor.map_isIso`, which is `isIso_map_mkHom` below -- stated with every
category, functor, object and morphism a variable and applied by `exact`, since the instance
`IsIso` of the concrete morphism is not synthesized at the spelling the square is written in.

## References

* [Stacks Project, Tag 0FKV](https://stacks.math.columbia.edu/tag/0FKV)
* [Stacks Project, Tag 07M9](https://stacks.math.columbia.edu/tag/07M9)
* [Stacks Project, Tag 09SY](https://stacks.math.columbia.edu/tag/09SY)
* [Stacks Project, Tag 0FP3](https://stacks.math.columbia.edu/tag/0FP3)
-/

@[expose] public noncomputable section

attribute [local instance_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.CechSheaf (abSheaf)
open Stacks.Cohomology.GlobalKunneth (tensorBase)
open Stacks.SheafOfModules.Tensor (ringSheaf)
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cech.CupProductSquare

attribute [local instance] HasDerivedCategory.standard

/-- The image under a bifunctor of a pair of isomorphisms is an isomorphism, stated with every
category, functor, object and morphism a variable.  It is applied below by `exact`, which is one
`isDefEq`; the instance `IsIso` of the concrete morphism of the cup-product square is not
synthesized at the spelling that square is written in. -/
theorem isIso_map_mkHom {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (F : C × D ⥤ E) {a b : C} {a' b' : D} (f : a ⟶ b) (g : a' ⟶ b')
    (hf : IsIso f) (hg : IsIso g) : IsIso (F.map (f ×ₘ g)) := by
  have : IsIso (f ×ₘ g) := (isIso_prod_iff _ _).mpr ⟨hf, hg⟩
  infer_instance

/-- Cancelling an isomorphism on the left of an equation of composites, stated with every
category, object and morphism a variable; applied below by `exact`, since `Epi` is not
synthesized from `IsIso` at the spelling the cup-product square is written in. -/
theorem eq_of_isIso_comp_eq {C : Type*} [Category* C] {a b c : C} (f : a ⟶ b)
    (hf : IsIso f) {g g' : b ⟶ c} (h : f ≫ g = f ≫ g') : g = g' := by
  have := hf
  exact (cancel_epi f).mp h

variable (S : RingedSpace.{u, u}) {I : Type u} (Ui : I → Opens S.carrier)
  (hU : (⊤ : Opens S.carrier) = ⨆ i, Ui i)
  (K M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)))

/-- **For a pair of bounded below complexes of flasque modules the Čech augmentation of
[Stacks, Tag 07M9] is invertible in both tensor factors of `- ⊗^𝐋_A -`.**  This is the top edge
of the diagram the source displays just before [Stacks, Tag 0FKV], and it is what makes that
diagram's top left corner `Γ(S, 𝒦^•) ⊗^𝐋_A Γ(S, ℳ^•)` interchangeable with the tag's. -/
theorem isIso_tensorBase_map_sectionsToTotalCechDerived_of_isFlasque
    (hK : ∀ n : ℤ, (abSheaf (K.1.X n)).IsFlasque)
    (hM : ∀ n : ℤ, (abSheaf (M.1.X n)).IsFlasque) :
    IsIso ((Functor.uncurry.obj (tensorBase S)).map
      ((Stacks.Cech.Linear.sectionsToTotalCechDerived S.carrier
          (ringSheaf.{u, u, u} S.sheaf) ⊤ Ui hU).app K ×ₘ
        (Stacks.Cech.Linear.sectionsToTotalCechDerived S.carrier
          (ringSheaf.{u, u, u} S.sheaf) ⊤ Ui hU).app M)) :=
  isIso_map_mkHom (Functor.uncurry.obj (tensorBase S)) _ _
    (Stacks.Cech.Linear.isIso_sectionsToTotalCechDerived_of_isFlasque S.carrier
      (ringSheaf.{u, u, u} S.sheaf) ⊤ Ui hU K hK)
    (Stacks.Cech.Linear.isIso_sectionsToTotalCechDerived_of_isFlasque S.carrier
      (ringSheaf.{u, u, u} S.sheaf) ⊤ Ui hU M hM)

/-- **The flasque cancellation of [Stacks, Tag 0FKV]'s square.**  For a pair of bounded below
complexes of flasque `𝒪_S`-modules the tag's square commutes if and only if its two legs agree
after precomposition with the Čech augmentation of [Stacks, Tag 07M9] in both tensor factors.

This is the move the second paragraph of the source's proof makes: the horizontal arrows of the
preceding diagram are isomorphisms for a bounded below complex of flasque modules, so the tag's
square and that diagram carry the same information.  With
`sectionsToTotalCechDerived_comp_cechRightLeg` rewriting the right-hand side of the equivalent
assertion as the right-hand column of the preceding diagram, this reduces the flasque case of
Tag 0FKV to the commutativity of that diagram, which is [Stacks, Tag 0FP3] for the morphism from
`S` to a point.

Flasqueness is used only to invert the augmentation. -/
theorem cupProductSquareCommutes_iff_of_isFlasque
    (hK : ∀ n : ℤ, (abSheaf (K.1.X n)).IsFlasque)
    (hM : ∀ n : ℤ, (abSheaf (M.1.X n)).IsFlasque) :
    CupProductSquareCommutes S Ui hU K M ↔
      (Functor.uncurry.obj (tensorBase S)).map
            ((Stacks.Cech.Linear.sectionsToTotalCechDerived S.carrier
                (ringSheaf.{u, u, u} S.sheaf) ⊤ Ui hU).app K ×ₘ
              (Stacks.Cech.Linear.sectionsToTotalCechDerived S.carrier
                (ringSheaf.{u, u, u} S.sheaf) ⊤ Ui hU).app M) ≫
          cechLeftLeg S Ui hU K M =
        (Functor.uncurry.obj (tensorBase S)).map
            ((Stacks.Cech.Linear.sectionsToTotalCechDerived S.carrier
                (ringSheaf.{u, u, u} S.sheaf) ⊤ Ui hU).app K ×ₘ
              (Stacks.Cech.Linear.sectionsToTotalCechDerived S.carrier
                (ringSheaf.{u, u, u} S.sheaf) ⊤ Ui hU).app M) ≫
          cechRightLeg S Ui hU K M := by
  refine ⟨fun h => by rw [show cechLeftLeg S Ui hU K M = cechRightLeg S Ui hU K M from h],
    fun h => eq_of_isIso_comp_eq _
      (isIso_tensorBase_map_sectionsToTotalCechDerived_of_isFlasque S Ui hU K M hK hM) h⟩

/-- **A flasque pair under an arbitrary bounded below pair.**  For bounded below complexes
`𝒦^•`, `ℳ^•` of `𝒪_S`-modules there are morphisms `𝒦^• → 𝒦₁^•`, `ℳ^• → ℳ₁^•` to a pair of
objects of `CochainComplex.Plus` whose terms are flasque in the spelling
`cupProductSquareCommutes_iff_of_isFlasque` consumes.

The morphisms are those of the first paragraph of the proof of [Stacks, Tag 0FKV],
`Stacks.Cohomology.FlasqueReduction.exists_flasqueResolution_quasiIso_tensor` (the Godement
resolution of [Stacks, Tag 0FKT]); they are quasi-isomorphisms there, but this statement keeps
only the morphisms. -/
theorem exists_flasquePlusResolution
    (K M : CochainComplex (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)) ℤ)
    (hK : ∃ n : ℤ, K.IsStrictlyGE n) (hM : ∃ n : ℤ, M.IsStrictlyGE n) :
    ∃ (K₁ M₁ : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf.{u, u, u} S.sheaf)))
      (_ : K ⟶ K₁.1) (_ : M ⟶ M₁.1),
      (∀ n : ℤ, (abSheaf (K₁.1.X n)).IsFlasque) ∧
        ∀ n : ℤ, (abSheaf (M₁.1.X n)).IsFlasque := by
  obtain ⟨K₁, M₁, a, b, _, _, hK₁ge, hM₁ge, hK₁fl, hM₁fl, _⟩ :=
    Stacks.Cohomology.FlasqueReduction.exists_flasqueResolution_quasiIso_tensor S K M hK hM
  exact ⟨⟨K₁, (CochainComplex.plus_iff _ K₁).mpr hK₁ge⟩,
    ⟨M₁, (CochainComplex.plus_iff _ M₁).mpr hM₁ge⟩, a, b, hK₁fl, hM₁fl⟩

end Stacks.Cech.CupProductSquare

end
