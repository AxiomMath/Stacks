module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedZerothCohomology

/-!
# Zeroth cohomology on the derived category of a sheaf of differential graded algebras

Let `R` be a sheaf of rings on a site admitting sheafification and let `A` be a sheaf of
differential graded `R`-algebras. Zeroth cohomology of a right differential graded `A`-module
is unchanged by homotopy, so it descends to the homotopy category `K(Mod(A, d))` (tag 0FT2);
a quasi-isomorphism of right differential graded modules is in particular an isomorphism on
zeroth cohomology, so that descended functor inverts the quasi-isomorphisms and therefore
descends once more, along the localization functor `K(Mod(A, d)) ⥤ D(A, d)` of tag 0FT5, to a
functor `H⁰ : D(A, d) ⥤ Mod(O)`. The descent is unique up to a unique natural isomorphism
compatible with the given factorization.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.derivedZerothCohomologyFunctor` is zeroth
  cohomology on the derived category `D(A, d)`.
* `SheafOfModules.DifferentialGradedModule.derivedZerothCohomologyFunctorIso` is the natural
  isomorphism exhibiting it as a factorization of zeroth cohomology on the homotopy category
  through the localization functor.

## Main results

* `SheafOfModules.DifferentialGradedModule.zerothCohomology_inverts_quasiIsomorphisms`: zeroth
  cohomology on the homotopy category sends quasi-isomorphisms to isomorphisms.
* `SheafOfModules.DifferentialGradedModule.derivedZerothCohomology_unique`: any factorization
  of zeroth cohomology on the homotopy category through the localization functor agrees with
  `SheafOfModules.DifferentialGradedModule.derivedZerothCohomologyFunctor` by a unique natural
  isomorphism compatible with the given one.

## Scope of `@[stacks 0FT7]`

Tag 0FT7 makes two assertions about zeroth cohomology on the homotopy category: that it
*factors* through `D(A, d)`, and that the factored functor is *homological*. Only the first is
proved here, so the attributes below carry the scoped clause
`"the factorization of H^0 through the derived category"`.

The second assertion is
`SheafOfModules.DifferentialGradedModule.derivedZerothCohomologyFunctor_isHomological`, stated
in a separate module because `CategoryTheory.Functor.IsHomological` is a property of a functor
out of a *pre-triangulated* category, and the pre-triangulated structure on
`SheafOfModules.DifferentialGradedModule.derivedCategory` is the one Mathlib puts on a
localization — `CategoryTheory.Triangulated.Localization.pretriangulated` — which needs
`CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions` and
`CategoryTheory.MorphismProperty.IsCompatibleWithTriangulation` of
`SheafOfModules.DifferentialGradedModule.quasiIsomorphisms`. Both of those come from the
identification of the quasi-isomorphisms with the class `(acyclic A).trW` attached to the
triangulated subcategory of acyclic objects, for which Mathlib supplies them outright; that
identification is tag 0FT4,
`SheafOfModules.DifferentialGradedModule.acyclic_trW_eq_quasiIsomorphisms`. The acyclic
subcategory is available only over a *ringed site*, whereas this module works over an arbitrary
sheaf of rings.

The ingredients of the second assertion are the following.

* The acyclic objects are a strictly full saturated triangulated subcategory of
  `K(Mod(A, d))`: `SheafOfModules.DifferentialGradedModule.acyclic_isTriangulated` of tag 0FT3.
* A homomorphism of right differential graded modules is a quasi-isomorphism exactly when its
  cone is acyclic: `SheafOfModules.DifferentialGradedModule.acyclic_cone_iff_quasiIso`.
* The quasi-isomorphisms are the class attached to the acyclic objects, tag 0FT4; so they admit
  a left calculus of fractions and are compatible with the triangulation.
* Zeroth cohomology on the homotopy category is homological:
  `SheafOfModules.DifferentialGradedModule.HomotopyCategory.zerothCohomologyFunctor_isHomological`,
  the second clause of tag 0FT2. The clause `"h0_factors"` on
  `SheafOfModules.DifferentialGradedModule.HomotopyCategory.zerothCohomologyFunctor` is the
  *factorization* half of tag 0FT2.

Given the pre-triangulated structure the second assertion is immediate from Mathlib's
`CategoryTheory.Functor.isHomological_of_localization`, which is tag 05R7 (1); tag 05R7 (2) is
`CategoryTheory.Functor.isTriangulated_of_localization`.

## Implementation notes

That zeroth cohomology inverts the quasi-isomorphisms is read off one representative: the
quotient functor to the homotopy category is full, so an arrow of `K(Mod(A, d))` is the class
of a morphism `f` of right differential graded modules, the class of quasi-isomorphisms
evaluates on `f` to `QuasiIso f.toHomologicalComplex` by its definition, and the value of
zeroth cohomology on that class is, by construction of the descent as a
`CategoryTheory.Quotient.lift`, the degree-zero homology map of `f.toHomologicalComplex`.

The descent along the localization is `CategoryTheory.Localization.lift` for the localization
functor `SheafOfModules.DifferentialGradedModule.toDerivedCategory`, so its factorization is
`CategoryTheory.Localization.fac` and the uniqueness statement is
`CategoryTheory.Localization.liftNatIso` together with
`CategoryTheory.Localization.natTrans_ext`. Uniqueness up to a unique natural isomorphism is
the appropriate form for a functor on a localized category: the restriction along the
localization functor determines a functor only up to such an isomorphism.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring, the algebra pieces and the module
pieces are independent; a ringed site `X` is the case `R := X.ringSheaf`. The two hypotheses
`HasSheafify J AddCommGrpCat.{m}` and `J.WEqualsLocallyBijective AddCommGrpCat.{m}` are what
make `SheafOfModules.{m} R` abelian, and so make the homology of its cochain complexes
available; they replace the source's standing convention that a site admits sheafification.

## References

* [Stacks Project, Tag 0FT7](https://stacks.math.columbia.edu/tag/0FT7)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
* [Stacks Project, Tag 0FT2](https://stacks.math.columbia.edu/tag/0FT2)
* [Stacks Project, Tag 05R7](https://stacks.math.columbia.edu/tag/05R7)
-/

@[expose] public noncomputable section

open CategoryTheory

universe t a m v u

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- Zeroth cohomology on the homotopy category of right differential graded modules sends
quasi-isomorphisms to isomorphisms of sheaves of modules. -/
theorem zerothCohomology_inverts_quasiIsomorphisms (A : DifferentialGradedAlgebra.{t, a} R) :
    (quasiIsomorphisms.{t, a, m} A).IsInvertedBy
      (HomotopyCategory.zerothCohomologyFunctor.{t, a, m} A) := by
  intro M N φ hφ
  have hf : (HomotopyCategory.quotient A).map
      ((HomotopyCategory.quotient A).preimage φ) = φ :=
    (HomotopyCategory.quotient A).map_preimage φ
  rw [← hf]
  show IsIso (HomologicalComplex.homologyMap
    ((HomotopyCategory.quotient A).preimage φ).toHomologicalComplex 0)
  exact (quasiIso_iff_isIso_homologyMap _).1 (hφ _ hf) 0

/-- Zeroth cohomology on the derived category of `(A, d)`: the factorization of zeroth
cohomology on the homotopy category through the localization at the quasi-isomorphisms. -/
@[stacks 0FT7 "the factorization of H^0 through the derived category"]
def derivedZerothCohomologyFunctor (A : DifferentialGradedAlgebra.{t, a} R) :
    derivedCategory.{t, a, m} A ⥤ SheafOfModules.{m} R :=
  Localization.lift (HomotopyCategory.zerothCohomologyFunctor.{t, a, m} A)
    (zerothCohomology_inverts_quasiIsomorphisms A) (toDerivedCategory.{t, a, m} A)

/-- Zeroth cohomology on the homotopy category is the restriction of zeroth cohomology on the
derived category along the localization functor. -/
@[stacks 0FT7 "the factorization of H^0 through the derived category"]
def derivedZerothCohomologyFunctorIso (A : DifferentialGradedAlgebra.{t, a} R) :
    toDerivedCategory.{t, a, m} A ⋙ derivedZerothCohomologyFunctor.{t, a, m} A ≅
      HomotopyCategory.zerothCohomologyFunctor.{t, a, m} A :=
  Localization.fac (HomotopyCategory.zerothCohomologyFunctor.{t, a, m} A)
    (zerothCohomology_inverts_quasiIsomorphisms A) (toDerivedCategory.{t, a, m} A)

/-- Zeroth cohomology on the derived category is the unique descent of zeroth cohomology on the
homotopy category: a functor `G` on `D(A, d)` together with an identification `α` of its
restriction along the localization functor with
`SheafOfModules.DifferentialGradedModule.HomotopyCategory.zerothCohomologyFunctor` agrees with
`SheafOfModules.DifferentialGradedModule.derivedZerothCohomologyFunctor` by a unique natural
isomorphism compatible with `α`. -/
theorem derivedZerothCohomology_unique (A : DifferentialGradedAlgebra.{t, a} R)
    (G : derivedCategory.{t, a, m} A ⥤ SheafOfModules.{m} R)
    (α : toDerivedCategory.{t, a, m} A ⋙ G ≅
      HomotopyCategory.zerothCohomologyFunctor.{t, a, m} A) :
    ∃! e : G ≅ derivedZerothCohomologyFunctor.{t, a, m} A,
      Functor.whiskerLeft (toDerivedCategory.{t, a, m} A) e.hom ≫
        (derivedZerothCohomologyFunctorIso.{t, a, m} A).hom = α.hom := by
  let Q := toDerivedCategory.{t, a, m} A
  let W := quasiIsomorphisms.{t, a, m} A
  let F := derivedZerothCohomologyFunctor.{t, a, m} A
  let δ := derivedZerothCohomologyFunctorIso.{t, a, m} A
  let β : Q ⋙ G ≅ Q ⋙ F := α ≪≫ δ.symm
  let e : G ≅ F := Localization.liftNatIso Q W (Q ⋙ G) (Q ⋙ F) G F β
  have he : Functor.whiskerLeft Q e.hom = β.hom := by
    ext X
    simp [e, Localization.liftNatIso]
  have he_prop : Functor.whiskerLeft Q e.hom ≫ δ.hom = α.hom := by
    rw [he]
    simp [β]
  refine ⟨e, he_prop, fun e' he' => Iso.ext <| Localization.natTrans_ext Q W fun X =>
    (cancel_mono (δ.hom.app X)).1 ?_⟩
  exact congrArg (fun η => η.app X) (he'.trans he_prop.symm)

end DifferentialGradedModule

end SheafOfModules

end
