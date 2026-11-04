module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjectivePushforwardFiniteness
public import StacksFrontier.AlgebraicGeometry.Cohomology.AffineBase
public import StacksFrontier.AlgebraicGeometry.ProjMapTwistDegreeSection.Basic

/-!
# The twist of the pushforward of the structure sheaf of a blowup, degree by degree

Let `A` be a Noetherian ring, `I ⊆ A` an ideal with a chosen finite generating family `x₀, …, x_m`,
and `X = Proj(⨁ₙ Iⁿ)` the blowup of `Spec A` in `I`. Write `i : X ⟶ 𝐏 = Proj A[T₀, …, T_m]` for the
closed immersion of `X` into projective space coming from the polynomial presentation of the Rees
algebra (`Stacks.Blowup.isClosedImmersion_blowUpSpecToProjSpace`). For every `d : ℤ` the `d`-th
twist of the pushforward `i_*𝒪_X` is the pushforward of the `d`-th twist of `𝒪_X`:

`(i_*𝒪_X)(d) ≅ i_*(𝒪_X(d))`.

The isomorphism is the projection formula at `i` ([Stacks, Tag 01E8]) composed with the
identification of the pullback of the twisting sheaf of `𝐏` along `i` ([Stacks, Tag 01N1]
part (3)).

## Main definitions

* `Stacks.Blowup.twistSheafOfModules_pushforward_unit_iso`: the degree-`d` comparison
  `(i_*𝒪_X)(d) ≅ i_*(𝒪_X(d))`, as sheaves of `𝒪_𝐏`-modules.
* `Stacks.Blowup.globalSections_twistSheafOfModules_pushforward_unit_iso`: the same comparison on
  global sections, `Γ(𝐏, (i_*𝒪_X)(d)) ≅ Γ(X, 𝒪_X(d))` as `Γ(𝐏, 𝒪_𝐏)`-modules, the right side with
  scalars restricted along `i^\#`.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj (twistingSheaf twistSheafOfModules)
open Stacks.ProjectiveCohomology (polyGrading)

universe u

namespace Stacks.Blowup

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The `d`-th twist of the pushforward of the structure sheaf of a blowup is the pushforward of
the `d`-th twist**, for a blowup presented by a finite generating family of `I`:

`(i_*𝒪_X)(d) ≅ i_*(𝒪_X(d))`,

where `i : X ⟶ 𝐏 = Proj A[T₀, …, T_m]` is the closed immersion coming from the chosen generating
family. This is the projection formula at `i` (`Stacks.Blowup.pushforwardUnitTensorIso`,
[Stacks, Tag 01E8]) composed with the identification of the pullback of the twisting sheaf of `𝐏`
along `i` (`Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso`,
[Stacks, Tag 01N1] part (3)). -/
def twistSheafOfModules_pushforward_unit_iso {A : Type u} [CommRing A] [IsNoetherianRing A]
    {I : Ideal A} {n : ℕ} (x : Fin (n + 1) → A) (hx : ∀ j, x j ∈ I)
    (hspan : I = Ideal.span (Set.range x)) (d : ℤ) :
    twistSheafOfModules (polyGrading A n)
        ((Scheme.Modules.pushforward (blowUpSpecToProjSpace I x hx hspan)).obj
          (SheafOfModules.unit (blowUpSpec I).ringCatSheaf)) d ≅
      (Scheme.Modules.pushforward (blowUpSpecToProjSpace I x hx hspan)).obj
        (twistingSheaf (reesGrading I) d) :=
  have e := Stacks.AlgebraicGeometry.ProjMapTwistDegreeSection.pullbackTwistIso
    (reesPresentation I x hx) _ (surjective_reesPresentation I x hx hspan)
    (Stacks.ProjectiveSpace.SerreVanishing.adjoin_one_polyGrading A n) d
  pushforwardUnitTensorIso (blowUpSpecToProjSpace I x hx hspan)
    (twistingSheaf (polyGrading A n) d) (twistingSheaf (reesGrading I) d) e

/-- **The degree-`d` comparison above, read off on global sections:**
`Γ(𝐏, (i_*𝒪_X)(d)) ≅ Γ(X, 𝒪_X(d))`, as `Γ(𝐏, 𝒪_𝐏)`-modules, with the right side having its scalars
restricted along `i^\# : Γ(𝐏, 𝒪_𝐏) ⟶ Γ(X, 𝒪_X)`. This is `twistSheafOfModules_pushforward_unit_iso`
pushed through `Stacks.Cohomology.sectionsFunctor` and composed with
`Stacks.Cohomology.AffineBase.pushforwardSectionsIso`, under which the sections of a direct image
over the whole base are, by definition, the sections of the source. -/
def globalSections_twistSheafOfModules_pushforward_unit_iso {A : Type u} [CommRing A]
    [IsNoetherianRing A] {I : Ideal A} {n : ℕ} (x : Fin (n + 1) → A) (hx : ∀ j, x j ∈ I)
    (hspan : I = Ideal.span (Set.range x)) (d : ℤ) :
    (Stacks.Cohomology.sectionsFunctor (AlgebraicGeometry.Proj (polyGrading A n)) ⊤).obj
        (twistSheafOfModules (polyGrading A n)
          ((Scheme.Modules.pushforward (blowUpSpecToProjSpace I x hx hspan)).obj
            (SheafOfModules.unit (blowUpSpec I).ringCatSheaf)) d) ≅
      (ModuleCat.restrictScalars (blowUpSpecToProjSpace I x hx hspan).appTop.hom).obj
        ((Stacks.Cohomology.sectionsFunctor (blowUpSpec I) ⊤).obj
          (twistingSheaf (reesGrading I) d)) :=
  (Stacks.Cohomology.sectionsFunctor _ ⊤).mapIso
      (twistSheafOfModules_pushforward_unit_iso x hx hspan d) ≪≫
    (Stacks.Cohomology.AffineBase.pushforwardSectionsIso
        (blowUpSpecToProjSpace I x hx hspan)).app (twistingSheaf (reesGrading I) d)

end Stacks.Blowup

end
