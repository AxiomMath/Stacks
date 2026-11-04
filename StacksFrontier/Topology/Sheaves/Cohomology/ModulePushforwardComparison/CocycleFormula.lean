module

public import StacksFrontier.Topology.Sheaves.Cohomology.ModulePushforwardComparison.ResolutionFormulaInDegreeZero
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedFunctors.CompositeComparisonInDegreeZero

/-!
# The cocycle clause of Stacks 01F1 part (2) in positive degree

`Stacks.Cohomology.ModulePushforwardComparison.rightDerived_modulePushforward_forget_iso` is Stacks
01F1 part (2). One clause of the tag characterizes that comparison by its effect on cocycles: for
an injective resolution `I` of a sheaf of modules `M`, an injective resolution `J` of the
underlying abelian sheaf and a comparison `φ` of the two extending the identity, the comparison
carries the class of a degree-`n` cocycle of `I` to the class of its image under `φ`. This file
proves the clause in positive degree from the equation

`(rightDerivedToSheafAbelianPushforwardIso f n).hom.app M =`
`  (I.isoRightDerivedObj (toSheaf ⋙ f_*) n).hom ≫ Hⁿ(f_* φ) ≫ (J.isoRightDerivedObj f_* n).inv`,

which says that the comparison `rightDerivedToSheafAbelianPushforwardIso` is computed on the pair
`(I, J)` by `φ`.

## Main results

* `homologyπ_mapHomologyIso_inv_comp_homologyMap`: the clause at the level of a short complex. For
  `G` exact, the projection to homology of `G` applied to a short complex, read through
  `CategoryTheory.ShortComplex.mapHomologyIso` and then pushed along two morphisms of short
  complexes, is any map prescribed on cycles.
* `mapComplexHomologyIso_hom_app` and `mapComplexHomologyIso_homologyπ`: the same for cochain
  complexes, through `Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso`.
* `rightDerivedCompIso_trans_hom_app_eq`: the resolution-level formula for the whole comparison,
  from the formula for its second factor.
* `rightDerived_forget_iso_cocycles_of_hom_app_eq`: the clause, abstractly, from that formula.
* `rightDerived_modulePushforward_forget_iso_cocycles_succ`: the clause of Stacks 01F1 part (2) in
  degree `m + 1`, from the formula for `rightDerivedToSheafAbelianPushforwardIso`.
* `rightDerivedComparison_app_singleFunctor_obj`,
  `rightDerivedFunctorPlusUnit_comp_app_singleFunctor_obj` and
  `derivedComposition_app_singleFunctor_obj`: the comparison `R(G ∘ F) ⟶ RG ∘ RF` of Stacks 05T2
  computed on an injective resolution.
* `extendedHomologyIso_comp`: naturality of
  `Stacks.Cohomology.HigherDirectImagePresheaf.extendedHomologyIso` in the functor.
* `resolutionDerivedIso_hom_eq`, `ι_map_resolutionSingleQhHom` and
  `mapSingleFunctorCompQhIso_hom_app_comp`: `resolutionDerivedIso` and
  `CategoryTheory.Functor.mapSingleFunctorCompQhIso` through morphisms of the bounded below
  homotopy category.
* `singleMapHomologicalComplex_comp_ι`: a comparison of resolutions compatible with the
  augmentations in degree zero is compatible with them as a map of complexes.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
-/
@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.ModulePushforwardComparison

/-! ### The cocycle equation at the level of a short complex -/

section ShortComplexLevel

variable {B : Type*} {D : Type*} [Category* B] [Category* D] [Abelian B] [Abelian D]
  (G : B ⥤ D) [G.Additive] [G.PreservesHomology]

/-- **The cocycle clause on a short complex.** Let `G` be exact, `S` a short complex, and
`τ : S.map G ⟶ S₁`, `σ : S₁ ⟶ S₂` two morphisms of short complexes. Any map `c` on cycles induced
by `τ ≫ σ` computes, on homology, the projection of `S` pushed through `G`, read along
`CategoryTheory.ShortComplex.mapHomologyIso` and then along `τ` and `σ`. -/
theorem homologyπ_mapHomologyIso_inv_comp_homologyMap
    (S : ShortComplex B) (S₁ S₂ : ShortComplex D) (τ : S.map G ⟶ S₁) (σ : S₁ ⟶ S₂)
    (c : G.obj S.cycles ⟶ S₂.cycles)
    (hc : c ≫ S₂.iCycles = G.map S.iCycles ≫ τ.τ₂ ≫ σ.τ₂) :
    G.map S.homologyπ ≫ ((S.mapHomologyIso G).inv ≫ ShortComplex.homologyMap τ) ≫
        ShortComplex.homologyMap σ = c ≫ S₂.homologyπ := by
  have hcyc : (S.mapCyclesIso G).inv ≫
      ShortComplex.cyclesMap τ ≫ ShortComplex.cyclesMap σ = c := by
    refine (cancel_mono S₂.iCycles).1 ?_
    rw [hc, Category.assoc, Category.assoc, ShortComplex.cyclesMap_i,
      ShortComplex.cyclesMap_i_assoc, ShortComplex.mapCyclesIso_inv_comp_iCycles_assoc]
  rw [Category.assoc, ← Category.assoc (G.map S.homologyπ),
    ShortComplex.π_comp_mapHomologyIso_inv, Category.assoc,
    ShortComplex.homologyπ_naturality_assoc, ShortComplex.homologyπ_naturality, ← hcyc]
  simp

end ShortComplexLevel

/-! ### The cocycle equation at the level of cochain complexes -/

section ComplexLevel

variable {A : Type*} {B : Type*} {D : Type*} [Category* A] [Category* B] [Category* D]
  [Abelian A] [Abelian B] [Abelian D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D) [F.Additive] [G.Additive] [H.Additive]
  [G.PreservesHomology] (e : F ⋙ G ≅ H)

/-- The component of `Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso` in degree `n`:
compare the degree-`n` homology of `G` applied degreewise to the complex of `F` with `G` of that
homology, then take the homology of `e` applied degreewise. -/
theorem mapComplexHomologyIso_hom_app (n : ℕ)
    (K : HomologicalComplex A (ComplexShape.up ℕ)) :
    (ModuleComparison.mapComplexHomologyIso F G H e n).hom.app K =
      ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc n).mapHomologyIso G).inv ≫
        HomologicalComplex.homologyMap
          ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app K) n := rfl

/-- **The cocycle clause on a cochain complex.** Let `G` be exact and `e : F ⋙ G ≅ H`. Given a
cochain map `ψ` out of `H` applied degreewise to `K`, any map `c` on degree-`n` cycles induced by
`e` and `ψ` computes, on homology, the degree-`n` projection of the complex of `F` pushed through
`G`, read along `Stacks.Cohomology.ModuleComparison.mapComplexHomologyIso` and then along `ψ`. -/
theorem mapComplexHomologyIso_homologyπ (n : ℕ)
    {K : HomologicalComplex A (ComplexShape.up ℕ)}
    {L : HomologicalComplex D (ComplexShape.up ℕ)}
    (ψ : (H.mapHomologicalComplex (ComplexShape.up ℕ)).obj K ⟶ L)
    (c : G.obj (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).cycles n) ⟶ L.cycles n)
    (hc : c ≫ L.iCycles n =
      G.map (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).iCycles n) ≫
        e.hom.app (K.X n) ≫ ψ.f n) :
    G.map (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).homologyπ n) ≫
        (ModuleComparison.mapComplexHomologyIso F G H e n).hom.app K ≫
          HomologicalComplex.homologyMap ψ n =
      c ≫ L.homologyπ n :=
  (congrArg (fun g => G.map (HomologicalComplex.homologyπ
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) n) ≫ g ≫
          HomologicalComplex.homologyMap ψ n)
      (mapComplexHomologyIso_hom_app F G H e n K)).trans
    (homologyπ_mapHomologyIso_inv_comp_homologyMap G
      (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc n)
      (((H.mapHomologicalComplex (ComplexShape.up ℕ)).obj K).sc n) (L.sc n)
      ((HomologicalComplex.shortComplexFunctor D (ComplexShape.up ℕ) n).map
        ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℕ)).hom.app K))
      ((HomologicalComplex.shortComplexFunctor D (ComplexShape.up ℕ) n).map ψ) c hc)

end ComplexLevel

/-! ### The clause from the resolution-level formula for the second factor -/

section Reduction

/-- Cancelling an inverse against its own `hom` in the middle of a composite. -/
private theorem glue_cancel {E' : Type*} [Category* E'] {R₁ R₂ R₃ R₄ R₅ R₆ : E'}
    (a : R₁ ⟶ R₂) (m : R₂ ⟶ R₃) (q : R₄ ≅ R₃) (h : R₃ ⟶ R₅) (k : R₅ ⟶ R₆) :
    (a ≫ m ≫ q.inv) ≫ q.hom ≫ h ≫ k = a ≫ m ≫ h ≫ k := by simp

/-- Cancelling the two outer isomorphisms of a composite, the first of them under a functor. -/
private theorem glue_three {Ca Cb : Type*} [Category* Ca] [Category* Cb] (G : Ca ⥤ Cb)
    {X Y Z : Ca} (a : X ⟶ Y) (p : Z ≅ Y) {R₃ R₄ R₅ : Cb}
    (m : G.obj Y ⟶ R₃) (h : R₃ ⟶ R₄) (r : R₅ ≅ R₄) :
    G.map (a ≫ p.inv) ≫ (G.map p.hom ≫ m ≫ h ≫ r.inv) ≫ r.hom = G.map a ≫ m ≫ h := by
  have h1 : G.map (a ≫ p.inv) ≫ G.map p.hom = G.map a := by
    rw [← G.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, h1]

variable {C₁ : Type*} {C₂ : Type*} {C₃ : Type*} {C₄ : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Abelian C₁] [HasInjectiveResolutions C₁] [Abelian C₂] [Abelian C₃]
  [HasInjectiveResolutions C₃] [Abelian C₄]
  (E : C₁ ⥤ C₂) (G : C₂ ⥤ C₄) (T : C₁ ⥤ C₃) (Av : C₃ ⥤ C₄)
  [E.Additive] [G.Additive] [T.Additive] [Av.Additive] [G.PreservesHomology]
  (e : E ⋙ G ≅ T ⋙ Av)

/-- **The resolution-level formula for the two-step comparison.** Let `G` be exact,
`e : E ⋙ G ≅ T ⋙ Av`, and let `Ξ` be a comparison `(T ⋙ Av).rightDerived n ≅ T ⋙ Av.rightDerived n`
whose component at `M` is computed on the pair `(I, J)` by `φ`. Then the composite of
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` with `Ξ` is computed on `(I, J)` by `φ` as
well. -/
theorem rightDerivedCompIso_trans_hom_app_eq (n : ℕ) {M : C₁} (I : InjectiveResolution M)
    (J : InjectiveResolution (T.obj M))
    (φ : (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (Ξ : (T ⋙ Av).rightDerived n ≅ T ⋙ Av.rightDerived n)
    (hΞ : Ξ.hom.app M = (I.isoRightDerivedObj (T ⋙ Av) n).hom ≫
      (Av.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor C₄ (ComplexShape.up ℕ) n).map φ ≫
      (J.isoRightDerivedObj Av n).inv) :
    (ModuleComparison.rightDerivedCompIso E G (T ⋙ Av) e n ≪≫ Ξ).hom.app M =
      G.map (I.isoRightDerivedObj E n).hom ≫
        (ModuleComparison.mapComplexHomologyIso E G (T ⋙ Av) e n).hom.app I.cocomplex ≫
          (Av.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
            HomologicalComplex.homologyFunctor C₄ (ComplexShape.up ℕ) n).map φ ≫
            (J.isoRightDerivedObj Av n).inv := by
  rw [Iso.trans_hom, NatTrans.comp_app,
    DerivedCompTransport.rightDerivedCompIso_hom_app_eq E G (T ⋙ Av) e n I, hΞ]
  exact glue_cancel _ _ _ _ _

/-- **The cocycle clause, abstractly.** Let `G` be exact and `e : E ⋙ G ≅ T ⋙ Av`, and let `Φ` be a
comparison `E.rightDerived n ⋙ G ≅ T ⋙ Av.rightDerived n` whose component at `M` is computed on the
pair `(I, J)` by `φ`. Then `Φ` carries the class of a degree-`n` cocycle of the complex of `I` to
the class of its image under any cocycle comparison `c` induced by `φ`. -/
theorem rightDerived_forget_iso_cocycles_of_hom_app_eq (n : ℕ) {M : C₁}
    (I : InjectiveResolution M) (J : InjectiveResolution (T.obj M))
    (φ : (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (Φ : E.rightDerived n ⋙ G ≅ T ⋙ Av.rightDerived n)
    (hΦ : Φ.hom.app M = G.map (I.isoRightDerivedObj E n).hom ≫
      (ModuleComparison.mapComplexHomologyIso E G (T ⋙ Av) e n).hom.app I.cocomplex ≫
        (Av.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor C₄ (ComplexShape.up ℕ) n).map φ ≫
          (J.isoRightDerivedObj Av n).inv)
    (c : G.obj (((E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).cycles n) ⟶
      ((Av.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex).cycles n)
    (hc : c ≫ ((Av.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex).iCycles n =
      G.map (((E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).iCycles n) ≫
        e.hom.app (I.cocomplex.X n) ≫ Av.map (φ.f n)) :
    G.map (((E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homologyπ n ≫
          (I.isoRightDerivedObj E n).inv) ≫
        Φ.hom.app M ≫ (J.isoRightDerivedObj Av n).hom =
      c ≫ ((Av.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex).homologyπ n := by
  rw [hΦ]
  refine Eq.trans (glue_three G (HomologicalComplex.homologyπ
      ((E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) n)
    (I.isoRightDerivedObj E n)
    ((ModuleComparison.mapComplexHomologyIso E G (T ⋙ Av) e n).hom.app I.cocomplex)
    ((Av.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      HomologicalComplex.homologyFunctor C₄ (ComplexShape.up ℕ) n).map φ)
    (J.isoRightDerivedObj Av n)) ?_
  exact mapComplexHomologyIso_homologyπ E G (T ⋙ Av) e n
    (K := I.cocomplex)
    (L := (Av.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex)
    ((Av.mapHomologicalComplex (ComplexShape.up ℕ)).map φ) c hc

end Reduction

/-! ### The Stacks 05T2 comparison on an injective resolution -/

section DerivedCompositionResolution

open Stacks.Cohomology.HigherDirectImagePresheaf

variable {C₁ : Type*} {C₂ : Type*} {C₃ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] [HasDerivedCategory C₃]
  [EnoughInjectives C₁] [EnoughInjectives C₂]
  (T : C₁ ⥤ C₂) (Av : C₂ ⥤ C₃) [T.Additive] [Av.Additive]

/-- The unit of `R(Av ∘ T)` followed by `dc` at the image of an object of the bounded below
homotopy category is `β`, read on components. -/
private theorem unit_comp_app_eq (dc : (T ⋙ Av).rightDerivedFunctorPlus ⟶
      T.rightDerivedFunctorPlus ⋙ Av.rightDerivedFunctorPlus)
    (β : (T ⋙ Av).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ T.rightDerivedFunctorPlus ⋙ Av.rightDerivedFunctorPlus)
    (hdc : (T ⋙ Av).rightDerivedFunctorPlusUnit ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh dc = β)
    (X : HomotopyCategory.Plus C₁) :
    (T ⋙ Av).rightDerivedFunctorPlusUnit.app X ≫ dc.app (DerivedCategory.Plus.Qh.obj X) =
      β.app X :=
  congrArg (fun γ => γ.app X) hdc

/-- **The comparison `R(Av ∘ T) ⟶ R Av ∘ R T` of Stacks 05T2 on an injective resolution.** Let `dc`
be a transformation whose composite with the unit of `R(Av ∘ T)` is `β`. Then its component at `M`
placed in degree zero is computed from any injective resolution `I` of `M`: transport along
`Stacks.Cohomology.HigherDirectImagePresheaf.resolutionDerivedIso`, invert the unit at
`Stacks.Cohomology.HigherDirectImagePresheaf.resolutionCochainPlus I`, and read `β` there. -/
theorem rightDerivedComparison_app_singleFunctor_obj
    (dc : (T ⋙ Av).rightDerivedFunctorPlus ⟶
      T.rightDerivedFunctorPlus ⋙ Av.rightDerivedFunctorPlus)
    (β : (T ⋙ Av).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ T.rightDerivedFunctorPlus ⋙ Av.rightDerivedFunctorPlus)
    (hdc : (T ⋙ Av).rightDerivedFunctorPlusUnit ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh dc = β)
    {M : C₁} (I : InjectiveResolution M) :
    dc.app ((DerivedCategory.Plus.singleFunctor C₁ 0).obj M) =
      (T ⋙ Av).rightDerivedFunctorPlus.map (resolutionDerivedIso I).hom ≫
        (asIso ((T ⋙ Av).rightDerivedFunctorPlusUnit.app
            ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I)))).inv ≫
          β.app ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I)) ≫
            (T.rightDerivedFunctorPlus ⋙ Av.rightDerivedFunctorPlus).map
              (resolutionDerivedIso I).inv := by
  have hfac := unit_comp_app_eq T Av dc β hdc ((HomotopyCategory.Plus.quotient C₁).obj
    (resolutionCochainPlus I))
  have key : dc.app (DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I))) =
      (asIso ((T ⋙ Av).rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I)))).inv ≫
        β.app ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I)) :=
    (Iso.eq_inv_comp _).2 hfac
  calc dc.app ((DerivedCategory.Plus.singleFunctor C₁ 0).obj M)
      = ((T ⋙ Av).rightDerivedFunctorPlus.map (resolutionDerivedIso I).hom ≫
            dc.app (DerivedCategory.Plus.Qh.obj
              ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I)))) ≫
          (T.rightDerivedFunctorPlus ⋙ Av.rightDerivedFunctorPlus).map
            (resolutionDerivedIso I).inv := by
        rw [dc.naturality (resolutionDerivedIso I).hom, Category.assoc, ← Functor.map_comp,
          Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.comp_id]
    _ = _ := by rw [key]; simp

/-- `rightDerivedComparison_app_singleFunctor_obj` with no inverses: the comparison at `M` placed
in degree zero, transported back along
`Stacks.Cohomology.HigherDirectImagePresheaf.resolutionDerivedIso` and composed with the unit of
`R(Av ∘ T)` at `Stacks.Cohomology.HigherDirectImagePresheaf.resolutionCochainPlus I`, is `β` there.
-/
theorem rightDerivedFunctorPlusUnit_comp_app_singleFunctor_obj
    (dc : (T ⋙ Av).rightDerivedFunctorPlus ⟶
      T.rightDerivedFunctorPlus ⋙ Av.rightDerivedFunctorPlus)
    (β : (T ⋙ Av).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ T.rightDerivedFunctorPlus ⋙ Av.rightDerivedFunctorPlus)
    (hdc : (T ⋙ Av).rightDerivedFunctorPlusUnit ≫
      Functor.whiskerLeft DerivedCategory.Plus.Qh dc = β)
    {M : C₁} (I : InjectiveResolution M) :
    (T ⋙ Av).rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I)) ≫
        (T ⋙ Av).rightDerivedFunctorPlus.map (resolutionDerivedIso I).inv ≫
          dc.app ((DerivedCategory.Plus.singleFunctor C₁ 0).obj M) =
      β.app ((HomotopyCategory.Plus.quotient C₁).obj (resolutionCochainPlus I)) ≫
        (T.rightDerivedFunctorPlus ⋙ Av.rightDerivedFunctorPlus).map
          (resolutionDerivedIso I).inv := by
  have hfac := unit_comp_app_eq T Av dc β hdc ((HomotopyCategory.Plus.quotient C₁).obj
    (resolutionCochainPlus I))
  rw [dc.naturality (resolutionDerivedIso I).inv, ← Category.assoc, hfac]

end DerivedCompositionResolution

/-! ### `extendedHomologyIso` for a composite functor -/

section ExtendedHomology

open Stacks.Cohomology.HigherDirectImagePresheaf

variable {A : Type*} {A' : Type*} {B : Type*} [Category* A] [Category* A'] [Category* B]
  [Abelian A] [Abelian A'] [Abelian B]

/-- **The derived-category homology of a cochain complex is its homology**, as the composite of
`DerivedCategory.quotientCompQhIso`, `DerivedCategory.homologyFunctorFactors` and
`Stacks.Cohomology.HigherDirectImagePresheaf.homologyFunctorObjIso`. -/
noncomputable def derivedHomologyObjIso [HasDerivedCategory B]
    (Z : CochainComplex B ℤ) (i : ℤ) :
    (DerivedCategory.homologyFunctor B i).obj (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj Z)) ≅ Z.homology i :=
  (DerivedCategory.homologyFunctor B i).mapIso ((DerivedCategory.quotientCompQhIso B).app Z) ≪≫
    (DerivedCategory.homologyFunctorFactors B i).app Z ≪≫ homologyFunctorObjIso Z i

/-- `derivedHomologyObjIso` is natural in the complex. -/
theorem derivedHomologyObjIso_hom_naturality [HasDerivedCategory B]
    {Z W : CochainComplex B ℤ} (ψ : Z ⟶ W) (i : ℤ) :
    (DerivedCategory.homologyFunctor B i).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map ψ)) ≫
        (derivedHomologyObjIso W i).hom =
      (derivedHomologyObjIso Z i).hom ≫ HomologicalComplex.homologyMap ψ i := by
  have h₁ := congrArg ((DerivedCategory.homologyFunctor B i).map)
    ((DerivedCategory.quotientCompQhIso B).hom.naturality ψ)
  have h₂ := (DerivedCategory.homologyFunctorFactors B i).hom.naturality ψ
  dsimp only [Functor.comp_map] at h₁ h₂
  simp only [Functor.map_comp] at h₁
  simp only [derivedHomologyObjIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  simp only [← Category.assoc]
  rw [h₁]
  simp only [Category.assoc]
  rw [reassoc_of% h₂, homologyFunctorObjIso_hom_naturality]

/-- `Stacks.Cohomology.HigherDirectImagePresheaf.extendedHomologyIso` split into the half that
happens in the derived category and the half that happens inside `HomologicalComplex`. -/
theorem extendedHomologyIso_hom_eq [HasDerivedCategory B] (F : A' ⥤ B) [F.Additive]
    (K : CochainComplex A' ℕ) (n : ℕ) :
    (extendedHomologyIso F K n).hom =
      (derivedHomologyObjIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (K.extend ComplexShape.embeddingUpNat)) (n : ℤ)).hom ≫
        (extendedHomologyTailIso F K n).hom := by
  simp only [extendedHomologyIso, derivedHomologyObjIso, Iso.trans_hom, Category.assoc]

/-- The degreewise comparison between applying a functor and extending a complex by zero is
compatible with composing two functors. -/
theorem derivedMapExtendXIso_comp {ι : Type*} {c : ComplexShape ι}
    (T : A ⥤ A') (F : A' ⥤ B) [T.Additive] [F.Additive]
    (K : HomologicalComplex A c) (o : Option ι) :
    (derivedMapExtendXIso (T ⋙ F) K o).hom =
      F.map (derivedMapExtendXIso T K o).hom ≫
        (derivedMapExtendXIso F ((T.mapHomologicalComplex c).obj K) o).hom := by
  cases o with
  | some i => exact (F.map_id _).symm.trans (Category.comp_id _).symm
  | none =>
      exact ((T ⋙ F).map_isZero (HomologicalComplex.extend.isZero_X K rfl)).eq_of_src _ _

/-- **`derivedMapExtendIso` for a composite functor.** Extending by zero and then applying `T ⋙ F`
agrees with extending, applying `T` degreewise and then applying `F` degreewise: the comparison for
the composite is the comparison for `T` pushed through `F`, followed by the comparison for `F`. -/
theorem derivedMapExtendIso_comp {ι : Type*} {c : ComplexShape ι}
    (T : A ⥤ A') (F : A' ⥤ B) [T.Additive] [F.Additive]
    (e : c.Embedding (ComplexShape.up ℤ)) (K : HomologicalComplex A c) :
    (derivedMapExtendIso (T ⋙ F) e K).hom =
      (F.mapHomologicalComplex (ComplexShape.up ℤ)).map (derivedMapExtendIso T e K).hom ≫
        (derivedMapExtendIso F e ((T.mapHomologicalComplex c).obj K)).hom := by
  ext j
  exact derivedMapExtendXIso_comp T F K (e.r j)

/-- The degreewise comparison between applying a functor and extending by zero, evaluated at an
index `o = some a` coming from the original complex: the analogue of
`CategoryTheory.HomologicalComplex.extend.mapX_some`. -/
theorem derivedMapExtendXIso_hom_some {ι : Type*} {c : ComplexShape ι}
    (F : A ⥤ A') [F.Additive] (K : HomologicalComplex A c)
    {o : Option ι} {a : ι} (ho : o = some a) :
    (derivedMapExtendXIso F K o).hom =
      F.map (HomologicalComplex.extend.XIso K ho).hom ≫
        (HomologicalComplex.extend.XIso ((F.mapHomologicalComplex c).obj K) ho).inv := by
  subst ho
  exact (F.map_id (K.X a)).symm.trans (Category.comp_id _).symm

/-- `derivedMapExtendIso` in a degree that comes from the original complex: the analogue of
`CategoryTheory.HomologicalComplex.extendMap_f`. -/
theorem derivedMapExtendIso_hom_f {ι : Type*} {c : ComplexShape ι}
    (F : A ⥤ A') [F.Additive] (e : c.Embedding (ComplexShape.up ℤ))
    (K : HomologicalComplex A c) {i : ι} {j : ℤ} (h : e.f i = j) :
    (derivedMapExtendIso F e K).hom.f j =
      F.map ((K.extendXIso e h).hom) ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h).inv :=
  derivedMapExtendXIso_hom_some F K (e.r_eq_some h)

/-- **`extendedHomologyTailIso` for a composite functor**: the comparison for `T ⋙ F` is the
homology of `derivedMapExtendIso T` pushed through `F`, followed by the comparison for `F`. -/
theorem extendedHomologyTailIso_comp (T : A ⥤ A') (F : A' ⥤ B) [T.Additive] [F.Additive]
    (K : CochainComplex A ℕ) (n : ℕ) :
    (extendedHomologyTailIso (T ⋙ F) K n).hom =
      HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (derivedMapExtendIso T ComplexShape.embeddingUpNat K).hom) (n : ℤ) ≫
        (extendedHomologyTailIso F
          ((T.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) n).hom := by
  simp only [extendedHomologyTailIso, Iso.trans_hom, HomologicalComplex.homologyMapIso_hom]
  rw [derivedMapExtendIso_comp, HomologicalComplex.homologyMap_comp, Category.assoc]
  rfl

/-- **`extendedHomologyIso` for a composite functor**, that is, its naturality *in the functor*
rather than in the complex. The degree-`n` cohomology of `T ⋙ F` applied to the extension of `K` is
computed by transporting along `derivedMapExtendIso T` and then computing the degree-`n` cohomology
of `F` applied to `T` applied to `K` degreewise. -/
theorem extendedHomologyIso_comp [HasDerivedCategory B]
    (T : A ⥤ A') (F : A' ⥤ B) [T.Additive] [F.Additive]
    (K : CochainComplex A ℕ) (n : ℕ) :
    (extendedHomologyIso (T ⋙ F) K n).hom =
      (DerivedCategory.homologyFunctor B (n : ℤ)).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
              (derivedMapExtendIso T ComplexShape.embeddingUpNat K).hom))) ≫
        (extendedHomologyIso F
          ((T.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) n).hom := by
  rw [extendedHomologyIso_hom_eq, extendedHomologyIso_hom_eq, extendedHomologyTailIso_comp,
    ← Category.assoc, ← Category.assoc, derivedHomologyObjIso_hom_naturality]
  rfl

end ExtendedHomology

/-! ### The resolution comparison in the bounded below homotopy and derived categories -/

section ResolutionComparison

open Stacks.Cohomology.HigherDirectImagePresheaf

variable {A : Type*} [Category* A] [Abelian A]

/-- The augmentation of an injective resolution read in the bounded below homotopy category: a
morphism from `M` placed in degree zero to the image of
`Stacks.Cohomology.HigherDirectImagePresheaf.resolutionCochainPlus I`. -/
noncomputable def resolutionSingleQhHom {M : A} (I : InjectiveResolution M) :
    (HomotopyCategory.Plus.singleFunctor A 0).obj M ⟶
      (HomotopyCategory.Plus.quotient A).obj (resolutionCochainPlus I) :=
  (singlePlusToCochainQuotientIso (A := A)).hom.app M ≫
    (HomotopyCategory.Plus.quotient A).map (resolutionSinglePlusHom I)

/-- `Stacks.Cohomology.HigherDirectImagePresheaf.resolutionDerivedIso` is `DerivedCategory.Plus.Qh`
of `resolutionSingleQhHom`, after the identification of `M` placed in degree zero in the derived
category with its image from the homotopy category. -/
theorem resolutionDerivedIso_hom_eq [HasDerivedCategory A] {M : A} (I : InjectiveResolution M) :
    (resolutionDerivedIso I).hom =
      (Functor.singleFunctorPlusIsoCompQh (A := A) 0).hom.app M ≫
        DerivedCategory.Plus.Qh.map (resolutionSingleQhHom I) := by
  dsimp only [resolutionDerivedIso, resolutionSingleQhHom]
  simp

/-- `resolutionSingleQhHom` read in the unbounded homotopy category: it is the class of
`Stacks.Cohomology.HigherDirectImagePresheaf.resolutionSingleHom`, the extension by zero of the
augmentation. -/
theorem ι_map_resolutionSingleQhHom {M : A} (I : InjectiveResolution M) :
    (HomotopyCategory.Plus.ι A).map (resolutionSingleQhHom I) =
      (HomotopyCategory.singleFunctorPostcompQuotientIso A 0).hom.app M ≫
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (resolutionSingleHom I) := by
  have h : (HomotopyCategory.Plus.ι A).map
      ((singlePlusToCochainQuotientIso (A := A)).hom.app M) =
      (HomotopyCategory.singleFunctorPostcompQuotientIso A 0).hom.app M := by
    dsimp only [singlePlusToCochainQuotientIso]
    rw [Functor.fullyFaithfulCancelRight_hom_app, Functor.map_preimage]
    exact (Category.comp_id ((HomotopyCategory.Plus.singleFunctorCompιIso A 0).hom.app M ≫
        (HomotopyCategory.singleFunctorPostcompQuotientIso A 0).hom.app M)).trans
      (Category.id_comp _)
  rw [resolutionSingleQhHom, Functor.map_comp, h]
  rfl

section SingleComparison

/-- Cancelling a fully faithful functor off a natural isomorphism, read on components. -/
private theorem map_cancelRight_hom_app {Ca Cb Cc : Type*} [Category* Ca] [Category* Cb]
    [Category* Cc] {F G : Ca ⥤ Cb} (H : Cb ⥤ Cc) [H.Full] [H.Faithful]
    (iso : F ⋙ H ≅ G ⋙ H) (X : Ca) :
    H.map ((Functor.fullyFaithfulCancelRight H iso).hom.app X) = iso.hom.app X := by
  rw [Functor.fullyFaithfulCancelRight_hom_app]
  exact Functor.map_preimage _ _

variable {C₁ : Type*} {C₂ : Type*} [Category* C₁] [Category* C₂] [Abelian C₁] [Abelian C₂]
  (T : C₁ ⥤ C₂) [T.Additive]

/-- The comparison in the bounded below homotopy category between applying `T` to `M` placed in
degree zero and `T M` placed in degree zero: the unique lift of
`CategoryTheory.Functor.mapHomotopyCategorySingleFunctor` through the fully faithful inclusion of
the bounded below homotopy category. -/
noncomputable def singleMapPlusHom (M : C₁) :
    T.mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.singleFunctor C₁ 0).obj M) ⟶
      (HomotopyCategory.Plus.singleFunctor C₂ 0).obj (T.obj M) :=
  (HomotopyCategory.Plus.ι C₂).preimage
    ((Functor.mapHomotopyCategorySingleFunctor T 0).hom.app M)

/-- `singleMapPlusHom` is `CategoryTheory.Functor.mapHomotopyCategorySingleFunctor` read in the
unbounded homotopy category. -/
theorem ι_map_singleMapPlusHom (M : C₁) :
    (HomotopyCategory.Plus.ι C₂).map (singleMapPlusHom T M) =
      (Functor.mapHomotopyCategorySingleFunctor T 0).hom.app M :=
  Functor.map_preimage _ _

/-- **`CategoryTheory.Functor.mapSingleFunctorCompQhIso` comes from the homotopy category.** Its
component at `M`, followed by the identification of `T M` placed in degree zero with its image from
the homotopy category, is `DerivedCategory.Plus.Qh` of `singleMapPlusHom`. -/
theorem mapSingleFunctorCompQhIso_hom_app_comp [HasDerivedCategory C₂] (M : C₁) :
    (Functor.mapSingleFunctorCompQhIso T).hom.app M ≫
        (Functor.singleFunctorPlusIsoCompQh (A := C₂) 0).hom.app (T.obj M) =
      DerivedCategory.Plus.Qh.map (singleMapPlusHom T M) := by
  apply (DerivedCategory.Plus.ι (C := C₂)).map_injective
  have h1 : DerivedCategory.Plus.ι.map ((Functor.mapSingleFunctorCompQhIso T).hom.app M) =
      𝟙 _ ≫ DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategorySingleFunctor T 0).hom.app M) ≫ 𝟙 _ ≫
        (DerivedCategory.singleFunctorIsoCompQh C₂ 0).inv.app (T.obj M) :=
    map_cancelRight_hom_app DerivedCategory.Plus.ι _ M
  have h2 : DerivedCategory.Plus.ι.map
        ((Functor.singleFunctorPlusIsoCompQh (A := C₂) 0).hom.app (T.obj M)) =
      (DerivedCategory.singleFunctorIsoCompQh C₂ 0).hom.app (T.obj M) :=
    map_cancelRight_hom_app DerivedCategory.Plus.ι _ (T.obj M)
  have h3 : DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Qh.map (singleMapPlusHom T M)) =
      DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι C₂).map (singleMapPlusHom T M)) := rfl
  rw [Functor.map_comp, h1, h2, h3, ι_map_singleMapPlusHom, Category.id_comp,
    Category.id_comp]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun g => DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategorySingleFunctor T 0).hom.app M) ≫ g)
        (Iso.inv_hom_id_app (DerivedCategory.singleFunctorIsoCompQh C₂ 0) (T.obj M))).trans
      (Category.comp_id _))

/-- The cochain map from the image under `T` of the extension of `I` to the extension of `J`
induced by a comparison `φ` of resolutions: transport along `derivedMapExtendIso` and then extend
`φ` by zero. -/
noncomputable def resolutionExtendComparison {M : C₁} (I : InjectiveResolution M)
    (J : InjectiveResolution (T.obj M))
    (φ : (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex) :
    (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (I.cocomplex.extend ComplexShape.embeddingUpNat) ⟶
      J.cocomplex.extend ComplexShape.embeddingUpNat :=
  (derivedMapExtendIso T ComplexShape.embeddingUpNat I.cocomplex).hom ≫
    HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat

/-- **The degree-zero hypothesis on `φ` propagates to every degree.** A comparison of resolutions
whose degree-zero component carries the image of the augmentation of `I` to the augmentation of `J`
does so as a map of complexes. -/
theorem singleMapHomologicalComplex_comp_ι {M : C₁} (I : InjectiveResolution M)
    (J : InjectiveResolution (T.obj M))
    (φ : (T.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (hφ : T.map (I.ι.f 0) ≫ φ.f 0 = J.ι.f 0) :
    (T.mapHomologicalComplex (ComplexShape.up ℕ)).map I.ι ≫ φ =
      (HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℕ) 0).hom.app M ≫
        J.ι := by
  ext j
  by_cases hj : j = 0
  · subst hj
    exact hφ.trans (Category.id_comp (J.ι.f 0)).symm
  · exact (T.map_isZero
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 M j hj)).eq_of_src _ _

end SingleComparison

end ResolutionComparison

/-! ### Stacks 01F1 part (2) in positive degree -/

section Pushforward

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

open Stacks.Cohomology.HigherDirectImagePresheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The Stacks 05T2 comparison for (forget, abelian pushforward) on an injective resolution:**
`rightDerivedFunctorPlusUnit_comp_app_singleFunctor_obj` for `derivedComposition f`. -/
theorem derivedComposition_app_singleFunctor_obj (M : SheafOfModules.{u} (structureSheafRing X))
    (I : InjectiveResolution M) :
    (SheafOfModules.toSheaf (structureSheafRing X) ⋙
            abelianPushforward f).rightDerivedFunctorPlusUnit.app
          ((HomotopyCategory.Plus.quotient (SheafOfModules.{u} (structureSheafRing X))).obj
            (resolutionCochainPlus I)) ≫
        (SheafOfModules.toSheaf (structureSheafRing X) ⋙
              abelianPushforward f).rightDerivedFunctorPlus.map
            (resolutionDerivedIso I).inv ≫
          (derivedComposition f).app ((DerivedCategory.Plus.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X)) 0).obj M) =
      (derivedCompositionUnit f).app
          ((HomotopyCategory.Plus.quotient (SheafOfModules.{u} (structureSheafRing X))).obj
            (resolutionCochainPlus I)) ≫
        ((SheafOfModules.toSheaf (structureSheafRing X)).rightDerivedFunctorPlus ⋙
          (abelianPushforward f).rightDerivedFunctorPlus).map (resolutionDerivedIso I).inv :=
  rightDerivedFunctorPlusUnit_comp_app_singleFunctor_obj _ _ _ _
    (Functor.rightDerived_fac _ _ _ _ _) I

/-- **Stacks 01F1 part (2), canonical comparison, in degree `m + 1`, from the resolution-level
formula for the second factor of the comparison.** Given that
`rightDerivedToSheafAbelianPushforwardIso f (m + 1)` is computed at `M` on the pair `(I, J)` by
`φ`, the higher-direct-image comparison sends the class of a degree-`(m + 1)` cocycle of the
complex of `I` to the class of its image under any cocycle comparison induced by `φ`. -/
theorem rightDerived_modulePushforward_forget_iso_cocycles_succ
    (m : ℕ) (M : SheafOfModules.{u} (structureSheafRing X)) (I : InjectiveResolution M)
    (J : InjectiveResolution ((SheafOfModules.toSheaf (structureSheafRing X)).obj M))
    (φ : ((SheafOfModules.toSheaf (structureSheafRing X)).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj I.cocomplex ⟶ J.cocomplex)
    (hΞ : (rightDerivedToSheafAbelianPushforwardIso f (m + 1)).hom.app M =
      (I.isoRightDerivedObj (SheafOfModules.toSheaf (structureSheafRing X) ⋙
          abelianPushforward f) (m + 1)).hom ≫
        ((abelianPushforward f).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor
            (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})
            (ComplexShape.up ℕ) (m + 1)).map φ ≫
        (J.isoRightDerivedObj (abelianPushforward f) (m + 1)).inv) :
    let E := modulePushforward f
    let G := SheafOfModules.toSheaf (structureSheafRing Y)
    let A := (opensMap f).sheafPushforwardContinuous AddCommGrpCat.{u}
      (Opens.grothendieckTopology Y.carrier) (Opens.grothendieckTopology X.carrier)
    let K := (E.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let L := (A.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex
    ∀ (c : G.obj (K.cycles (m + 1)) ⟶ L.cycles (m + 1))
      (_ : c ≫ L.iCycles (m + 1) = G.map (K.iCycles (m + 1)) ≫ A.map (φ.f (m + 1))),
      G.map (K.homologyπ (m + 1) ≫ (I.isoRightDerivedObj E (m + 1)).inv) ≫
          (rightDerived_modulePushforward_forget_iso f (m + 1)).hom.app M ≫
          (J.isoRightDerivedObj A (m + 1)).hom =
        c ≫ L.homologyπ (m + 1) := by
  intro _ _ _ _ _ c hc
  exact rightDerived_forget_iso_cocycles_of_hom_app_eq (modulePushforward f)
    (SheafOfModules.toSheaf (structureSheafRing Y))
    (SheafOfModules.toSheaf (structureSheafRing X)) (abelianPushforward f)
    (modulePushforwardCompToSheafIso f) (m + 1) I J φ
    (rightDerivedModulePushforwardCompIso f (m + 1) ≪≫
      rightDerivedToSheafAbelianPushforwardIso f (m + 1))
    (rightDerivedCompIso_trans_hom_app_eq (modulePushforward f)
      (SheafOfModules.toSheaf (structureSheafRing Y))
      (SheafOfModules.toSheaf (structureSheafRing X)) (abelianPushforward f)
      (modulePushforwardCompToSheafIso f) (m + 1) I J φ _ hΞ)
    c (hc.trans (congrArg (fun g => (SheafOfModules.toSheaf (structureSheafRing Y)).map
      (HomologicalComplex.iCycles
        (((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex) (m + 1)) ≫ g)
      (Category.id_comp ((abelianPushforward f).map (φ.f (m + 1)))).symm))

end Pushforward

end Stacks.Cohomology.ModulePushforwardComparison

end
