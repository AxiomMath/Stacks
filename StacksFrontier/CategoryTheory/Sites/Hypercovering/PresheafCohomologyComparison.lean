module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.FunctorialInjectiveEmbeddings
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Injectives
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.PresheafSectionsFunctorial

/-!
# Comparing a hypercovering of a presheaf with derived sections

Let `C` be a site with equalizers and fibre products, let `G` be a presheaf on `C` and let `K` be
a hypercovering of `G`. There is a map

`s(F(K)) ⟶ RΓ(G, F)`

in `D⁺(Ab)`, functorial in the abelian sheaf `F`, compatible with the augmentation of `s(F(K))`
by the sections over `G` and an isomorphism at every injective sheaf; it induces natural
transformations `Ȟ^i(K, -) ⟶ H^i(G, -)` of functors `Ab(C) ⥤ Ab`.

## Main definitions

* `presheafSectionsFunctor`: the sections `Γ(G, -) = Hom(**Z**_G^♯, -)` over the presheaf `G`.
* `presheafDerivedSectionsFunctor`: `RΓ(G, -)` with values in `D⁺(Ab)`.
* `hypercoverPresheafDerivedFunctor`: the complex `s(-(K))`, viewed in `D⁺(Ab)`.
* `hypercoverPresheafAugmentation`: the augmentation `Γ(G, F)[0] ⟶ s(F(K))`.

## Main results

* `quasiIso_hypercoverPresheafAugmentation`: the augmentation is a quasi-isomorphism at an
  injective sheaf.
* `exists_hypercoverPresheafToDerivedSections`: the comparison map `s(-(K)) ⟶ RΓ(G, -)`,
  compatible with the augmentation and invertible at injective sheaves.
* `exists_presheafCechCohomologyToCohomology`: the natural transformations it induces on
  cohomology in every degree, from the Čech cohomology of the hypercovering to the cohomology
  over `G`.
* `hypercoverPresheafDerivedHomologyIso`: the cohomology of `s(-(K))` read in `D⁺(Ab)` is the
  cohomology of the complex.

## References

* [Stacks Project, Tag 09VX](https://stacks.math.columbia.edu/tag/09VX)
* [Stacks Project, Tag 09VU](https://stacks.math.columbia.edu/tag/09VU)
-/

@[expose] public section

universe q w v u

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite
open CategoryTheory.SimplicialObject.Augmented
open StacksDraft.DerivedSectionsComparison

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] [HasEqualizers C] [HasPullbacks C]
  (J : Pretopology C) (G : Cᵒᵖ ⥤ Type q) (K : HypercoveringOf.{q, w} J G)
  [HasSheafify J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}]
  [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})]

/-- **The sections over the presheaf `G`**, that is the morphisms out of the free abelian sheaf
`**Z**_G^♯`. -/
noncomputable abbrev presheafSectionsFunctor :
    Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)} ⥤
      AddCommGrpCat.{max (max u v) (max q w)} :=
  freeAbelianSheafSections J.toGrothendieck (K.toAugmentedULift.{q, w, v, u} J G)

/-- **Derived sections `RΓ(G, -)` over the presheaf `G`**, with values in `D⁺(Ab)`. -/
noncomputable def presheafDerivedSectionsFunctor :
    Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)} ⥤
      DerivedCategory.Plus AddCommGrpCat.{max (max u v) (max q w)} :=
  DerivedCategory.Plus.singleFunctor _ 0 ⋙
    (presheafSectionsFunctor.{q, w, v, u} J G K).rightDerivedFunctorPlus

/-- The isomorphism from the complex of free abelian sheaves of the augmented simplicial presheaf
of `K` to that of the associated simplicial presheaf of `K`, induced by
`HypercoveringOf.toAugmentedULiftLeftIso`. -/
noncomputable def freeAbelianSheafComplexIsoOfToAugmentedULift :
    (SimplicialObject.freeAbelianSheafComplexFunctor J.toGrothendieck).obj
        ((K.toAugmentedULift.{q, w, v, u} J G).left) ≅
      (SimplicialObject.freeAbelianSheafComplexFunctor J.toGrothendieck).obj
        (associatedSimplicialPresheaf.{max (max u v) (max q w)} K.toSimplicialObject) :=
  (SimplicialObject.freeAbelianSheafComplexFunctor J.toGrothendieck).mapIso
    (HypercoveringOf.toAugmentedULiftLeftIso.{q, w, v, u} J G K)

/-- The isomorphism, natural in the coefficient sheaf, from the complex `s(-(K))` to the Hom
complex out of the complex of free abelian sheaves of `HypercoveringOf.toAugmentedULift`. -/
noncomputable def sectionsComplexIsoFreeAbelianSheafHomCx :
    SemiRepresentable.sectionsComplexFunctor.{q, w, v, u} J.toGrothendieck
        K.toSimplicialObject ≅
      freeAbelianSheafHomCx J.toGrothendieck (K.toAugmentedULift.{q, w, v, u} J G) :=
  SemiRepresentable.sectionsComplexFunctorIsoHomComplexFunctor.{q, w, v, u} J.toGrothendieck
      K.toSimplicialObject ≪≫
    ChainComplex.homComplexFunctorIsoOfIso
      (freeAbelianSheafComplexIsoOfToAugmentedULift.{q, w, v, u} J G K)

/-- The isomorphism `sectionsComplexIsoFreeAbelianSheafHomCx` after extension by zero to integer
degrees. -/
noncomputable def sectionsComplexIntIsoFreeAbelianSheafHomCxZ :
    SemiRepresentable.sectionsComplexIntFunctor.{q, w, v, u} J.toGrothendieck
        K.toSimplicialObject ≅
      freeAbelianSheafHomCxZ J.toGrothendieck (K.toAugmentedULift.{q, w, v, u} J G) :=
  Functor.isoWhiskerRight (sectionsComplexIsoFreeAbelianSheafHomCx.{q, w, v, u} J G K)
    (ComplexShape.embeddingUpNat.extendFunctor AddCommGrpCat.{max (max u v) (max q w)})

/-- **The augmentation of the Čech complex of `K` by the sections over `G`**: the augmentation
`freeAbelianSheafEpsNatTrans` of the Hom complex out of the free abelian sheaves of the augmented
simplicial presheaf of `K`, followed by the inverse of
`sectionsComplexIntIsoFreeAbelianSheafHomCxZ`. -/
noncomputable def hypercoverPresheafAugmentation :
    presheafSectionsFunctor.{q, w, v, u} J G K ⋙
        HomologicalComplex.single AddCommGrpCat.{max (max u v) (max q w)}
          (ComplexShape.up ℤ) 0 ⟶
      SemiRepresentable.sectionsComplexIntFunctor.{q, w, v, u} J.toGrothendieck
        K.toSimplicialObject :=
  freeAbelianSheafEpsNatTrans J.toGrothendieck (K.toAugmentedULift.{q, w, v, u} J G) ≫
    (sectionsComplexIntIsoFreeAbelianSheafHomCxZ.{q, w, v, u} J G K).inv

omit [EnoughInjectives (Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)})] in
/-- **The augmentation is a quasi-isomorphism at an injective sheaf**: for an injective abelian
sheaf `I`, the augmentation `Γ(G, I)[0] ⟶ s(I(K))` is a quasi-isomorphism. -/
theorem quasiIso_hypercoverPresheafAugmentation
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}) [Injective F] :
    QuasiIso ((hypercoverPresheafAugmentation.{q, w, v, u} J G K).app F) := by
  have hmid : QuasiIso (freeAbelianSheafEps J.toGrothendieck
      (K.toAugmentedULift.{q, w, v, u} J G) F) :=
    quasiIso_freeAbelianSheafEps_toAugmentedULift J G K F
  have hright : QuasiIso
      ((sectionsComplexIntIsoFreeAbelianSheafHomCxZ.{q, w, v, u} J G K).inv.app F) :=
    quasiIso_of_isIso _
  have key : QuasiIso (freeAbelianSheafEps J.toGrothendieck
        (K.toAugmentedULift.{q, w, v, u} J G) F ≫
      (sectionsComplexIntIsoFreeAbelianSheafHomCxZ.{q, w, v, u} J G K).inv.app F) :=
    quasiIso_comp _ _ (hφ := hmid) (hφ' := hright)
  exact key

/-- The Čech complex `s(-(K))` of a hypercovering of a presheaf, as a bounded-below complex. -/
noncomputable def hypercoverPresheafCochainPlusFunctor :
    Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)} ⥤
      CochainComplex.Plus AddCommGrpCat.{max (max u v) (max q w)} :=
  TPlus (SemiRepresentable.sectionsComplexIntFunctor.{q, w, v, u} J.toGrothendieck
      K.toSimplicialObject)
    (SemiRepresentable.isZero_sectionsComplexIntFunctor_obj_X.{q, w, v, u} J.toGrothendieck
      K.toSimplicialObject)

/-- The Čech complex `s(-(K))` of a hypercovering of a presheaf, viewed in `D⁺(Ab)`. -/
noncomputable def hypercoverPresheafDerivedFunctor :
    Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)} ⥤
      DerivedCategory.Plus AddCommGrpCat.{max (max u v) (max q w)} :=
  hypercoverPresheafCochainPlusFunctor.{q, w, v, u} J G K ⋙ DerivedCategory.Plus.Q

/-- For a hypercovering `K` of a presheaf `G` on a site with equalizers and fibre products there
are a canonical map `ψ` from the sections over `G` to derived sections at the single complex, and
a map

`α : s(-(K)) ⟶ RΓ(G, -)`

in `D⁺(Ab)`, functorial in the abelian sheaf, compatible with the augmentation of `s(-(K))` by the
sections over `G`; and both are isomorphisms at every injective sheaf. -/
@[stacks 09VX "the comparison map s(F(K)) ⟶ RΓ(G, F) in D⁺(Ab), functorial in F"]
theorem exists_hypercoverPresheafToDerivedSections :
    ∃ (ψ : (presheafSectionsFunctor.{q, w, v, u} J G K ⋙
          singlePlus AddCommGrpCat.{max (max u v) (max q w)}) ⋙ DerivedCategory.Plus.Q ⟶
        presheafDerivedSectionsFunctor.{q, w, v, u} J G K)
      (α : hypercoverPresheafDerivedFunctor.{q, w, v, u} J G K ⟶
        presheafDerivedSectionsFunctor.{q, w, v, u} J G K),
      Functor.whiskerRight
            (epsNat (presheafSectionsFunctor.{q, w, v, u} J G K)
              (SemiRepresentable.sectionsComplexIntFunctor.{q, w, v, u} J.toGrothendieck
                K.toSimplicialObject)
              ((hypercoverPresheafAugmentation.{q, w, v, u} J G K).app)
              (fun {_ _} φ ↦ (hypercoverPresheafAugmentation.{q, w, v, u} J G K).naturality φ)
              (SemiRepresentable.isZero_sectionsComplexIntFunctor_obj_X.{q, w, v, u}
                J.toGrothendieck K.toSimplicialObject))
            DerivedCategory.Plus.Q ≫ α = ψ ∧
        (∀ F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)},
          Injective F → IsIso (ψ.app F)) ∧
        ∀ F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)},
          Injective F → IsIso (α.app F) :=
  exists_comparison_of_hasFunctorialInjectiveEmbeddings
    (Γ := presheafSectionsFunctor.{q, w, v, u} J G K)
    (T := SemiRepresentable.sectionsComplexIntFunctor.{q, w, v, u} J.toGrothendieck
      K.toSimplicialObject)
    (ε := (hypercoverPresheafAugmentation.{q, w, v, u} J G K).app)
    (hε := fun {_ _} φ ↦ (hypercoverPresheafAugmentation.{q, w, v, u} J G K).naturality φ)
    (hT0 := SemiRepresentable.isZero_sectionsComplexIntFunctor_obj_X.{q, w, v, u}
      J.toGrothendieck K.toSimplicialObject)
    (hεinj := fun F hF ↦ by
      have := hF
      exact quasiIso_hypercoverPresheafAugmentation.{q, w, v, u} J G K F)
    (Sheaf.hasFunctorialInjectiveEmbeddings_addCommGrpCat.{max (max u v) (max q w), v, u}
      J.toGrothendieck)

/-- **The cohomology of `s(-(K))` read in `D⁺(Ab)` is the Čech cohomology of the
hypercovering.** -/
noncomputable def hypercoverPresheafDerivedHomologyIso (i : ℤ) :
    hypercoverPresheafDerivedFunctor.{q, w, v, u} J G K ⋙
        DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)} i ≅
      SemiRepresentable.sectionsComplexIntFunctor.{q, w, v, u} J.toGrothendieck
          K.toSimplicialObject ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
          (ComplexShape.up ℤ) i :=
  Functor.isoWhiskerLeft
    (SemiRepresentable.sectionsComplexIntFunctor.{q, w, v, u} J.toGrothendieck
      K.toSimplicialObject)
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{max (max u v) (max q w)} i)

/-- The comparison map of `exists_hypercoverPresheafToDerivedSections` induces, in every degree
`i`, a natural transformation

`Ȟ^i(K, -) ⟶ H^i(G, -)`

of functors from abelian sheaves to abelian groups, and these are isomorphisms at every injective
sheaf.

The source is the `i`-th cohomology of the complex `s(-(K))` itself, i.e. the Čech cohomology of
the hypercovering, and the target is the `i`-th cohomology of `RΓ(G, -)`. -/
@[stacks 09VX "the induced natural transformations Ȟ^i(K, -) ⟶ H^i(G, -)"]
theorem exists_presheafCechCohomologyToCohomology :
    ∃ β : ∀ i : ℤ,
        (SemiRepresentable.sectionsComplexIntFunctor.{q, w, v, u} J.toGrothendieck
              K.toSimplicialObject ⋙
            HomologicalComplex.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)}
              (ComplexShape.up ℤ) i) ⟶
          (presheafDerivedSectionsFunctor.{q, w, v, u} J G K ⋙
            DerivedCategory.Plus.homologyFunctor
              AddCommGrpCat.{max (max u v) (max q w)} i),
      ∀ (i : ℤ) (F : Sheaf J.toGrothendieck AddCommGrpCat.{max (max u v) (max q w)}),
        Injective F → IsIso ((β i).app F) := by
  obtain ⟨_, α, _, _, hα⟩ := exists_hypercoverPresheafToDerivedSections.{q, w, v, u} J G K
  refine ⟨fun i ↦ (hypercoverPresheafDerivedHomologyIso.{q, w, v, u} J G K i).inv ≫
    Functor.whiskerRight α
      (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{max (max u v) (max q w)} i),
    fun i F hF ↦ ?_⟩
  have := hα F hF
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app]
  infer_instance

end Stacks.CategoryTheory.Hypercovering

end
