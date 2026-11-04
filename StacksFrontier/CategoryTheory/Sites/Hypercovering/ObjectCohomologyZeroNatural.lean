module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.SectionsComplexFunctorial

/-!
# Degree-zero Čech cohomology of a hypercovering of an object

Let `C` be a site with fibre products, let `X` be an object of `C` and let `K` be a hypercovering
of `X`.  [Stacks, Tag 01GV] asserts `Ȟ⁰(K, F) = F(X)` for every abelian sheaf `F`.  This file
delivers that identification as an isomorphism, and as an isomorphism of functors of `F`.

It also gives [Stacks, Tag 01GW] as a single `p`-indexed statement: for an injective coefficient
sheaf `I`, the group `Ȟᵖ(K, I)` is `I(X)` when `p = 0` and zero otherwise.

## Main definitions

* `CategoryTheory.SimplicialObject.Augmented.freeAbelianSheafSectionsIsoHomologyZero`:
  [Stacks, Tag 01GV] for the Hom complex of a locally covering augmented simplicial presheaf, as
  a natural isomorphism whose inverse is induced by the degree-zero augmentation.
* `Stacks.CategoryTheory.Hypercovering.zerothCechCohomologyFunctorIsoSections`:
  **Tag 01GV**, as an isomorphism of functors on the abelian sheaves.
* `Stacks.CategoryTheory.Hypercovering.zerothCechCohomologyIsoSections`: **Tag 01GV** at a fixed
  abelian sheaf, the component of the previous isomorphism.
* `Stacks.CategoryTheory.Hypercovering.cechCohomologyOverIsoOfInjective`: **Tag 01GW** in full —
  for an injective coefficient sheaf, `Ȟᵖ(K, I)` is `I(X)` when `p = 0` and zero when `p > 0`.

## Main results

* `CategoryTheory.SimplicialObject.Augmented.quasiIsoAt_freeAbelianSheafEpsNat_zero`: the
  augmentation of the Hom complex is a quasi-isomorphism in degree zero at *every* coefficient
  sheaf.

## References

* [Stacks Project, Tag 01GV](https://stacks.math.columbia.edu/tag/01GV)
* [Stacks Project, Tag 01GW](https://stacks.math.columbia.edu/tag/01GW)
* [Stacks Project, Tag 01GX](https://stacks.math.columbia.edu/tag/01GX)
-/

@[expose] public section

universe t w v u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{t}] (A : SimplicialObject.Augmented (Cᵒᵖ ⥤ Type t))

/-- **The augmentation of the Hom complex of free abelian sheaves is a quasi-isomorphism in
degree zero at every coefficient sheaf.** -/
theorem quasiIsoAt_freeAbelianSheafEpsNat_zero
    (h₀ : Presheaf.IsLocallySurjective J (A.hom.app (op (SimplexCategory.mk 0))))
    (h₁ : Presheaf.IsLocallySurjective J (edgesToFiberProduct A))
    (F : Sheaf J AddCommGrpCat.{t}) :
    QuasiIsoAt (freeAbelianSheafEpsNat J A F) 0 :=
  CochainComplex.quasiIsoAt_zero_mkHomFromSingle ((freeAbelianSheafHomCx J A).obj F)
    (freeAbelianSheafEpsZero J A F) (freeAbelianSheafEpsZero_comp_d J A F)
    (isIso_kernelLift_freeAbelianSheafAugZero J A h₀ h₁ F)

/-- **The canonical map `Γ_A(F) ⟶ H⁰(Hom(s(**Z**_A^♯), F))`**, natural in `F`: the degree-zero
homology of the augmentation `freeAbelianSheafEpsNatTransNat`, read through the computation of the
homology of a complex concentrated in degree zero. -/
noncomputable def freeAbelianSheafSectionsToHomologyZero :
    freeAbelianSheafSections J A ⟶
      freeAbelianSheafHomCx J A ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max u t} (ComplexShape.up ℕ) 0 :=
  (Functor.rightUnitor (freeAbelianSheafSections J A)).inv ≫
    Functor.whiskerLeft (freeAbelianSheafSections J A)
      (HomologicalComplex.homologyFunctorSingleIso AddCommGrpCat.{max u t}
        (c := ComplexShape.up ℕ) (j := 0)).inv ≫
    (Functor.associator (freeAbelianSheafSections J A)
      (HomologicalComplex.single AddCommGrpCat.{max u t} (ComplexShape.up ℕ) 0)
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u t}
        (ComplexShape.up ℕ) 0)).inv ≫
    Functor.whiskerRight (freeAbelianSheafEpsNatTransNat J A)
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u t} (ComplexShape.up ℕ) 0)

/-- **[Stacks, Tag 01GV] in canonical-map form, for a locally covering augmented simplicial
presheaf, and natural in the coefficient sheaf.**  The sections of a sheaf of abelian groups over
the presheaf of augmentation points of `A` are the degree-zero cohomology of the Hom complex out
of the complex of free abelian sheaves of `A`, the isomorphism being induced by the degree-zero
augmentation. -/
noncomputable def freeAbelianSheafSectionsIsoHomologyZero
    (h₀ : Presheaf.IsLocallySurjective J (A.hom.app (op (SimplexCategory.mk 0))))
    (h₁ : Presheaf.IsLocallySurjective J (edgesToFiberProduct A)) :
    freeAbelianSheafSections J A ≅
      freeAbelianSheafHomCx J A ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max u t} (ComplexShape.up ℕ) 0 := by
  have happ : ∀ F : Sheaf J AddCommGrpCat.{t},
      IsIso ((freeAbelianSheafSectionsToHomologyZero J A).app F) := by
    intro F
    have h : QuasiIsoAt (freeAbelianSheafEpsNat J A F) 0 :=
      quasiIsoAt_freeAbelianSheafEpsNat_zero J A h₀ h₁ F
    rw [quasiIsoAt_iff_isIso_homologyMap] at h
    have h4 : IsIso ((Functor.whiskerRight (freeAbelianSheafEpsNatTransNat J A)
        (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u t}
          (ComplexShape.up ℕ) 0)).app F) := h
    dsimp only [freeAbelianSheafSectionsToHomologyZero, NatTrans.comp_app]
    infer_instance
  have : IsIso (freeAbelianSheafSectionsToHomologyZero J A) :=
    NatIso.isIso_of_isIso_app _
  exact asIso (freeAbelianSheafSectionsToHomologyZero J A)

end CategoryTheory.SimplicialObject.Augmented

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory.SimplicialObject.Augmented

variable {C : Type u} [Category.{v} C] [HasPullbacks C] (J : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{w} (Over X)))

/-- Abelian sheaves of the right size on a site have a sheafification, by
`hasSheafify_addCommGrpCat`. -/
local instance hasSheafify_sheafAddCommGrpCat_zeroNatural :
    HasSheafify J.toGrothendieck AddCommGrpCat.{max u v w} :=
  hasSheafify_addCommGrpCat.{w} J.toGrothendieck

/-- For a hypercovering `K` of `X` the degree-zero Čech cohomology `Ȟ⁰(K, -)` is the functor of
sections on `X`, as an isomorphism of functors on the abelian sheaves, inverse to the canonical map
induced by the augmentation of the Čech complex by the sections on `X`. -/
@[stacks 01GV "the identification Ȟ⁰(K, 𝓕) = 𝓕(X), as functors on Ab(C)"]
noncomputable def zerothCechCohomologyFunctorIsoSections (hK : IsHypercovering J K) :
    SectionsOver.sectionsComplexFunctor J.toGrothendieck K ⋙
        HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w} (ComplexShape.up ℕ) 0 ≅
      sheafToPresheaf J.toGrothendieck AddCommGrpCat.{max u v w} ⋙
        (evaluation Cᵒᵖ AddCommGrpCat.{max u v w}).obj (op X) :=
  Functor.isoWhiskerRight
      (SectionsOver.sectionsComplexFunctorIsoHomFreeAbelianSheafComplexFunctor
        J.toGrothendieck K)
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v w} (ComplexShape.up ℕ) 0) ≪≫
    (freeAbelianSheafSectionsIsoHomologyZero J.toGrothendieck
      (associatedAugmentedSimplicialPresheafOver.{w} K)
      (isLocallySurjective_of_isHypercovering.{w} J K hK).1
      (isLocallySurjective_of_isHypercovering.{w} J K hK).2.1).symm ≪≫
    (evaluationIsoFreeAbelianSheafSections.{w} J.toGrothendieck K).symm

/-- For a hypercovering `K` of `X` and an abelian sheaf `F`, the degree-zero Čech cohomology
`Ȟ⁰(K, F)` is the group `F(X)` of sections on `X`: the component at `F` of
`zerothCechCohomologyFunctorIsoSections`. -/
@[stacks 01GV "the identification Ȟ⁰(K, 𝓕) = 𝓕(X)"]
noncomputable def zerothCechCohomologyIsoSections (hK : IsHypercovering J K)
    (F : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) :
    (SectionsOver.sectionsComplex J.toGrothendieck K F).homology 0 ≅ F.obj.obj (op X) :=
  (zerothCechCohomologyFunctorIsoSections.{w} J K hK).app F

open ZeroObject in
/-- For a hypercovering `K` of `X` and an injective abelian sheaf `I`, the Čech cohomology
`Ȟᵖ(K, I)` is the group `I(X)` of sections on `X` when `p = 0` and is zero when `p > 0`. -/
@[stacks 01GW]
noncomputable def cechCohomologyOverIsoOfInjective (hK : IsHypercovering J K)
    (I : Sheaf J.toGrothendieck AddCommGrpCat.{max u v w}) [Injective I] (p : ℕ) :
    (SectionsOver.sectionsComplex J.toGrothendieck K I).homology p ≅
      if p = 0 then I.obj.obj (op X) else 0 := by
  cases p with
  | zero =>
    exact (zerothCechCohomologyIsoSections.{w} J K hK I).trans
      (eqToIso (ite_eq_left rfl).symm)
  | succ n =>
    exact (cechCohomologyOver_isZero_of_injective.{w} J K hK I (n + 1)
      (by omega)).isoZero.trans (eqToIso (ite_eq_right (by omega)).symm)

end Stacks.CategoryTheory.Hypercovering

end
