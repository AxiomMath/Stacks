module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.CategoryTheory.Sites.FunctorialInjectiveEmbeddings
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SectionsComplexFunctorial
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SpectralSequence

/-!
# Comparing a hypercovering with derived sections

Let `C` be a site with fibre products, let `X` be an object of `C` and let `K` be a hypercovering
of `X`.  [Stacks, Tag 01GY] asserts that there is a map

`s(F(K)) ⟶ RΓ(X, F)`

in `D⁺(Ab)`, functorial in the abelian sheaf `F`, and that it induces natural transformations
`Ȟ^i(K, -) ⟶ H^i(X, -)` of functors `Ab(C) ⥤ Ab`.  This file proves both, with a strengthening
that makes them non-vacuous: the map is compatible with the augmentation of `s(F(K))` by the
sections on `X`, and it is an isomorphism at every injective sheaf.

## Main results

* `exists_hypercoverToDerivedSections`: **[Stacks, Tag 01GY]**, the comparison map.
* `exists_cechCohomologyToSheafCohomology`: **[Stacks, Tag 01GY]**, the natural transformations
  it induces on cohomology in every degree, from the Čech cohomology of the hypercovering to
  sheaf cohomology on `X`.
* `hypercoverDerivedHomologyIso`: the cohomology of `s(-(K))` read in `D⁺(Ab)` is the cohomology
  of the complex, which is what makes the source of those transformations Čech cohomology.

## Implementation notes

The construction is `StacksDraft.DerivedSectionsComparison`, the abstract form of the double
complex argument of [Stacks, Tag 01GY] and [Stacks, Tag 09VX]: for an additive functor
`Γ : A ⥤ B`, an additive `T : A ⥤ CochainComplex B ℤ` vanishing in negative degrees, and an
augmentation `ε : Γ(-)[0] ⟶ T` that is a quasi-isomorphism at every injective object, it produces
a natural transformation `T ⟶ R⁺Γ(-[0])` with `Q(ε) ≫ α = ψ` and `α` invertible at injectives.
Here `A` is the category of abelian sheaves, `Γ` is `sheafSectionsFunctor`, i.e. evaluation on
`X`, and `T` is `hypercoverCochainIntFunctor`, i.e. `s(-(K))` extended by zero.

The three data `ε`, its naturality and its quasi-isomorphy at injectives are *not* constructed
here.  They are `sectionsEps`, `sectionsEps_naturality` and `quasiIso_sectionsEps` of
`SpectralSequence.lean`, where the same augmentation drives the spectral sequence.  There `ε` is
assembled as the natural transformation `sectionsEpsNatTrans` and only then read pointwise, so its
naturality is `NatTrans.naturality` and needs no proof.  It is transported from the corresponding
data for the Hom complex of the augmented simplicial presheaf of `K`, which
`CategoryTheory.SimplicialObject.Augmented.freeAbelianSheafEpsNatTrans` supplies and
`quasiIso_freeAbelianSheafEps` pins, along the two natural isomorphisms of
`SectionsComplexFunctorial.lean`: [Stacks, Tag 01GX] in the coefficient sheaf, and the Yoneda
identification of the sections on `X` with the morphisms out of `**Z**_X^♯`.  Transporting rather
than reproving is what makes the degree-zero input [Stacks, Tag 01GV] available in the
*canonical-map* form the construction needs — the library's carrier of that tag is an abstract
`Nonempty` isomorphism, from which no augmentation can be read off, whereas
`isIso_kernelLift_freeAbelianSheafAugZero` is canonical.

Both conclusions are existential, as the source statement is: "there is a map ... which induces
natural transformations ...".  The pin `Q(ε) ≫ α = ψ` and the invertibility at injectives are
what rule out the zero map, which inhabits the same hom-type; see
`StacksDraft.DerivedSectionsComparison.isZero_of_pin_zero` and `not_isIso_zero_app`.

## References

* [Stacks Project, Tag 01GY](https://stacks.math.columbia.edu/tag/01GY)
* [Stacks Project, Tag 01GV](https://stacks.math.columbia.edu/tag/01GV)
* [Stacks Project, Tag 01GW](https://stacks.math.columbia.edu/tag/01GW)
* [Stacks Project, Tag 01GX](https://stacks.math.columbia.edu/tag/01GX)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open CategoryTheory.SimplicialObject.Augmented
open StacksDraft.DerivedSectionsComparison

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasPullbacks C] (J : Pretopology C) (X : C)
  (K : SimplicialObject (FormalCoproduct.{w} (Over X)))

/-! ### The size conditions, discharged

The three class hypotheses of `derivedSectionsFunctor` — sheafification of
`AddCommGrpCat.{max u v w}`-valued presheaves, its inverting exactly the locally bijective
morphisms, and enough injectives in the resulting category of sheaves
(`enoughInjectives_sheafAddCommGrpCat`) — hold on any site whose objects lie in `Type u` and whose
morphisms lie in `Type v`. They are local instances here, so the statements below assume only that
`C` has fibre products. -/

/-- Presheaves of abelian groups in `AddCommGrpCat.{max u v w}` on the topology generated by `J`
admit sheafification. -/
local instance hasSheafify_sheafAddCommGrpCat :
    HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w} :=
  hasSheafify_addCommGrpCat.{w} J.toGrothendieck

/-- For the topology generated by `J`, the morphisms of presheaves of abelian groups in
`AddCommGrpCat.{max u v w}` that sheafification inverts are exactly the locally bijective ones. -/
local instance wEqualsLocallyBijective_sheafAddCommGrpCat :
    J.toGrothendieck.WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat.{max u v w} J.toGrothendieck

attribute [local instance] enoughInjectives_sheafAddCommGrpCat

/-- **Stacks Project, Tag 01GY.**  For a hypercovering `K` of an object `X` of a site with fibre
products there are a canonical map `ψ` from the sections on `X` to derived sections at the single
complex, and a map

`α : s(-(K)) ⟶ RΓ(X, -)`

in `D⁺(Ab)`, functorial in the abelian sheaf, compatible with the augmentation of `s(-(K))` by the
sections on `X`; and both are isomorphisms at every injective sheaf.

The last clause is what makes the statement non-vacuous: by
`StacksDraft.DerivedSectionsComparison.isZero_of_pin_zero`, `α = 0` would force `Q(s(I(K)))` to be
a zero object for every injective `I`. -/
@[stacks 01GY "the comparison map s(F(K)) ⟶ RΓ(X, F) in D⁺(Ab), functorial in F"]
theorem exists_hypercoverToDerivedSections (hK : IsHypercovering J K) :
    ∃ (ψ : (sheafSectionsFunctor.{w} J X ⋙ singlePlus AddCommGrpCat.{max u v w}) ⋙
          DerivedCategory.Plus.Q ⟶ derivedSectionsFunctor.{w} J X)
      (α : hypercoverDerivedFunctor.{w} J X K ⟶ derivedSectionsFunctor.{w} J X),
      Functor.whiskerRight
            (epsNat (sheafSectionsFunctor.{w} J X) (hypercoverCochainIntFunctor.{w} J X K)
              (sectionsEps.{w} J X K)
              (fun {_ _} φ ↦ sectionsEps_naturality.{w} J X K φ)
              (isZero_hypercoverCochainIntFunctor_obj_X.{w} J X K))
            DerivedCategory.Plus.Q ≫ α = ψ ∧
        (∀ F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}, Injective F → IsIso (ψ.app F)) ∧
        ∀ F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}, Injective F → IsIso (α.app F) :=
  exists_comparison_of_hasFunctorialInjectiveEmbeddings
    (Γ := sheafSectionsFunctor.{w} J X) (T := hypercoverCochainIntFunctor.{w} J X K)
    (ε := sectionsEps.{w} J X K)
    (hε := fun {_ _} φ ↦ sectionsEps_naturality.{w} J X K φ)
    (hT0 := isZero_hypercoverCochainIntFunctor_obj_X.{w} J X K)
    (hεinj := fun F hF ↦ by
      have := hF
      exact quasiIso_sectionsEps.{w} J X K hK F)
    (Sheaf.hasFunctorialInjectiveEmbeddings_addCommGrpCat J.toGrothendieck)

/-- **The cohomology of `s(-(K))` read in `D⁺(Ab)` is the Čech cohomology of the
hypercovering.**  The bounded-below localisation followed by the inclusion into the unbounded
derived category is the inclusion of complexes followed by the unbounded localisation, so this is
`DerivedCategory.homologyFunctorFactors`. -/
noncomputable def hypercoverDerivedHomologyIso (i : ℤ) :
    hypercoverDerivedFunctor.{w} J X K ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v w} i ≅
      hypercoverCochainIntFunctor.{w} J X K ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w} (ComplexShape.up ℤ) i :=
  Functor.isoWhiskerLeft (hypercoverCochainIntFunctor.{w} J X K)
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max u v w} i)

/-- **Stacks Project, Tag 01GY.**  The comparison map of
`exists_hypercoverToDerivedSections` induces, in every degree `i`, a natural transformation

`Ȟ^i(K, -) ⟶ H^i(X, -)`

of functors from abelian sheaves to abelian groups, and these are isomorphisms at every injective
sheaf.

The source is the `i`-th cohomology of the complex `s(-(K))` itself, i.e. the Čech cohomology of
the hypercovering, and the target is the `i`-th cohomology of `RΓ(X, -)`, i.e. sheaf cohomology on
`X`.  The invertibility at injectives is again what rules out the zero transformation. -/
@[stacks 01GY "the induced natural transformations Ȟ^i(K, -) ⟶ H^i(X, -)"]
theorem exists_cechCohomologyToSheafCohomology (hK : IsHypercovering J K) :
    ∃ β : ∀ i : ℤ,
        (hypercoverCochainIntFunctor.{w} J X K ⋙
            HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w}
              (ComplexShape.up ℤ) i) ⟶
          (derivedSectionsFunctor.{w} J X ⋙
            DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v w} i),
      ∀ (i : ℤ) (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}),
        Injective F → IsIso ((β i).app F) := by
  obtain ⟨_, α, _, _, hα⟩ := exists_hypercoverToDerivedSections.{w} J X K hK
  refine ⟨fun i ↦ (hypercoverDerivedHomologyIso.{w} J X K i).inv ≫
    Functor.whiskerRight α
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max u v w} i), fun i F hF ↦ ?_⟩
  have := hα F hF
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app]
  infer_instance

end Stacks.CategoryTheory.Hypercovering

end
