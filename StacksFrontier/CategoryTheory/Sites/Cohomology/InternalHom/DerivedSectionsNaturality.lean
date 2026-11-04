module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedSectionsOnDerivedObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomRepresentativePair
import StacksCore.Tactic.StacksAttribute

/-! # Naturality of Stacks 08JA globally

Let `(C, O)` be a ringed site. **Stacks 08JA** identifies the degree-zero global
hypercohomology of the derived internal Hom `RSheafHom(L, M)` with the group of morphisms
`L ⟶ M` in `D(O)`, and `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv` is
that identification. This file proves it **natural in both variables, for arbitrary morphisms
of `D(O)`** — contravariantly in `L`, covariantly in `M`.

The argument is the one of
`StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingNaturality`: the
identification is constructed at a *model*, a K-flat complex in the first variable and a
K-injective complex in the second, where
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_naturality`
gives naturality for morphisms of complexes; an arbitrary morphism of `D(O)` between classes of
complexes is a fraction, and the apex of the pair of fractions is made into a model by a K-flat
resolution in the first slot and the K-injective resolution in the second, so that both legs are
classes of morphisms of complexes and the denominator is invertible.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsFunctor`: the source of Stacks
  08JA, `(L, M) ↦ H⁰(C, RSheafHom(L, M))`, as a bifunctor `D(O)ᵒᵖ × D(O) ⥤ Ab`.
* `AlgebraicGeometry.RingedSite.homModels` and
  `AlgebraicGeometry.RingedSite.modelSectionsEquiv`: the models of Stacks 08JA and the
  identification at a model.

## Main results

* `AlgebraicGeometry.RingedSite.modelSectionsEquiv_naturality`: the identification at models is
  natural for an arbitrary morphism of `D(O)` in each variable.
* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality_bifunctor`:
  **Stacks 08JA globally is natural in both variables.**
* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_eq_modelSectionsEquiv`:
  Stacks 08JA globally, at the classes of a K-flat and a K-injective complex, is the
  identification at that model — the chosen representatives being different complexes, this is
  a statement and not a definitional unfolding. Its spelling at a pair of complexes is
  `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_eq_ofKFlat`, imported.

## Implementation notes

The naturality is stated as an equation between elements rather than as an isomorphism of
bifunctors. That is not a matter of taste: the two sides of Stacks 08JA live in **different
universes**. The source `H⁰(C, RSheafHom(L, M))` is an object of `AddCommGrpCat.{u}`, while the
morphisms of `D(O)` at `CategoryTheory.HasDerivedCategory.standard` form a type in
`Type (u + 1)`, the derived category's morphism universe being the maximum of the object and
morphism universes of `SheafOfModules.{u} X.ringSheaf`. So the target bifunctor
`(L, M) ↦ (L ⟶ M)` takes values in `AddCommGrpCat.{u + 1}`, the two cannot be compared by an
isomorphism of functors into one category without interposing
`AddCommGrpCat.uliftFunctor`, and `CategoryTheory.NatIso.ofModels` does not apply on the nose.
An equation between elements is immune to this, and the functoriality of the source — which is
what the fraction argument needs — is still available, as
`derivedSheafHomGlobalSectionsFunctor`.

The cancellation at the end of `modelSectionsEquiv_naturality` is therefore performed on
morphisms of `D(O)`, not on the bifunctors: the denominator of the pair of fractions is
invertible in each variable, so pre- and postcomposition with it is injective.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- `(L, M) ↦ H⁰(C, RSheafHom(L, M))`, the source of Stacks 08JA globally, as a bifunctor on
`D(O)`: the derived internal Hom uncurried, followed by derived global sections and degree-zero
cohomology. -/
def derivedSheafHomGlobalSectionsFunctor :
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
        DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      AddCommGrpCat.{u} :=
  Functor.uncurry.obj (derivedSheafHomBifunctor X) ⋙
    derivedModuleGlobalSections X ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0

/-- The models of Stacks 08JA: a K-flat complex in the first variable and a K-injective complex
in the second, for which the internal Hom complex between them is K-injective by Stacks 0A96.
Every pair of objects of `D(O)` is represented by one, which is what makes the identification on
models extend to all of `D(O)`. -/
abbrev homModels :=
  {A : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ //
      Stacks.SheafOfModules.IsKFlat X.O A} ×
    {I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ //
      I.IsKInjective}

/-- The pair of objects of `D(O)` represented by a model. -/
abbrev modelPair (a : homModels X) :
    (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (op (DerivedCategory.Q.obj a.1.1), DerivedCategory.Q.obj a.2.1)

/-- Stacks 08JA globally, at a model. -/
noncomputable def modelSectionsEquiv (a : homModels X) :
    (((derivedSheafHomGlobalSectionsFunctor X).obj (modelPair X a) : Type u)) ≃+
      (DerivedCategory.Q.obj a.1.1 ⟶ DerivedCategory.Q.obj a.2.1) :=
  haveI := a.2.2
  derivedSheafHomGlobalSectionsEquivOfKFlat X a.1.1 a.2.1 a.1.2

/-- **The identification at models is natural for morphisms of complexes.** This is
`derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_naturality` read at the bifunctor
`derivedSheafHomGlobalSectionsFunctor`. -/
theorem modelSectionsEquiv_complexMap (a b : homModels X)
    (k : b.1.1 ⟶ a.1.1) (m : a.2.1 ⟶ b.2.1)
    (z : ((derivedSheafHomGlobalSectionsFunctor X).obj (modelPair X a) : Type u)) :
    modelSectionsEquiv X b
        ((derivedSheafHomGlobalSectionsFunctor X).map
          (((DerivedCategory.Q.map k).op, DerivedCategory.Q.map m) :
            modelPair X a ⟶ modelPair X b) z) =
      DerivedCategory.Q.map k ≫ modelSectionsEquiv X a z ≫ DerivedCategory.Q.map m := by
  have := a.2.2
  have := b.2.2
  have := isKInjective_sheafHomComplex_of_isKFlat X a.1.1 a.2.1 a.1.2
  have := isKInjective_sheafHomComplex_of_isKFlat X b.1.1 b.2.1 b.1.2
  exact derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_naturality X k m z

/-- **The identification at models is natural for an arbitrary morphism of `D(O)` in each
variable.** Each of the two components of the morphism is factored as a fraction through a third
complex, contravariantly in the first slot and covariantly in the second; the apex is made into
a model by a K-flat resolution in the first slot and the K-injective resolution in the second.
Both legs of the resulting pair of fractions are then classes of morphisms of complexes, where
naturality is `modelSectionsEquiv_complexMap`, and the denominator is invertible. -/
theorem modelSectionsEquiv_naturality (a b : homModels X)
    (φ : modelPair X a ⟶ modelPair X b)
    (z : ((derivedSheafHomGlobalSectionsFunctor X).obj (modelPair X a) : Type u)) :
    modelSectionsEquiv X b ((derivedSheafHomGlobalSectionsFunctor X).map φ z) =
      φ.1.unop ≫ modelSectionsEquiv X a z ≫ φ.2 := by
  obtain ⟨A₀, sk, hsk, gk, hk⟩ := DerivedCategory.right_fac φ.1.unop
  obtain ⟨I₀, gi, si, hsi, hi⟩ := DerivedCategory.left_fac φ.2
  obtain ⟨AF, qA, hAF, hqA⟩ := Stacks.SheafOfModules.exists_kFlat_quasiIso X A₀
  have : IsIso (DerivedCategory.Q.map qA) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hqA
  have := hsk
  have := hsi
  set aug := (kInjectiveAugmentation X).app I₀ with haug
  have : IsIso (DerivedCategory.Q.map aug) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  -- the apex model
  set c : homModels X :=
    (⟨AF, hAF⟩, ⟨(kInjectiveResolution X).obj I₀, inferInstance⟩) with hc
  -- the two legs, as morphisms of complexes
  set sA : AF ⟶ b.1.1 := qA ≫ sk with hsA
  set tA : AF ⟶ a.1.1 := qA ≫ gk with htA
  set sI : b.2.1 ⟶ (kInjectiveResolution X).obj I₀ := si ≫ aug with hsI
  set tI : a.2.1 ⟶ (kInjectiveResolution X).obj I₀ := gi ≫ aug with htI
  have : IsIso (DerivedCategory.Q.map sA) := by
    rw [hsA, Functor.map_comp]; infer_instance
  have : IsIso (DerivedCategory.Q.map sI) := by
    rw [hsI, Functor.map_comp]; infer_instance
  -- the two identities expressing that the fractions have a common apex
  have h1 : DerivedCategory.Q.map sA ≫ φ.1.unop = DerivedCategory.Q.map tA := by
    rw [hsA, htA, Functor.map_comp, Functor.map_comp, hk, Category.assoc,
      IsIso.hom_inv_id_assoc]
  have h2 : φ.2 ≫ DerivedCategory.Q.map sI = DerivedCategory.Q.map tI := by
    rw [hsI, htI, Functor.map_comp, Functor.map_comp, hi, Category.assoc,
      IsIso.inv_hom_id_assoc]
  -- naturality along the two legs
  have hb := modelSectionsEquiv_complexMap X b c sA sI
    ((derivedSheafHomGlobalSectionsFunctor X).map φ z)
  have ha := modelSectionsEquiv_complexMap X a c tA tI z
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hb
  -- the composite of the two product morphisms is the single one through the apex
  have hcomp : φ ≫ (((DerivedCategory.Q.map sA).op, DerivedCategory.Q.map sI) :
        modelPair X b ⟶ modelPair X c) =
      (((DerivedCategory.Q.map tA).op, DerivedCategory.Q.map tI) :
        modelPair X a ⟶ modelPair X c) := by
    refine Prod.ext ?_ ?_
    · exact Quiver.Hom.unop_inj h1
    · exact h2
  rw [hcomp, ha] at hb
  -- cancel the invertible denominator in each variable
  rw [← h1, ← h2] at hb
  simp only [Category.assoc] at hb
  replace hb := (cancel_epi (DerivedCategory.Q.map sA)).1 hb
  refine (cancel_mono (DerivedCategory.Q.map sI)).1 ?_
  simpa only [Category.assoc] using hb.symm

/-- The chosen model of a pair of objects of `D(O)`: the same representatives that
`derivedSheafHomGlobalSectionsEquiv` is built from. -/
abbrev chosenHomModel
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    homModels X :=
  (⟨kFlatModel X L, isKFlat_kFlatModel X L⟩, ⟨kInjectiveModel X M, inferInstance⟩)

/-- The chosen model does represent the given pair of objects of `D(O)`, as a morphism of the
product category. -/
abbrev chosenHomModelMap
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((op L, M) :
        (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
          DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
      modelPair X (chosenHomModel X L M) :=
  ((kFlatModelIso X L).hom.op, (kInjectiveModelIso X M).inv)

/-- `derivedSheafHomGlobalSectionsEquiv` is the identification at the chosen model, transported
along the chosen representatives. -/
theorem derivedSheafHomGlobalSectionsEquiv_eq_chosenHomModel
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv X L M z =
      ((kFlatModelIso X L).inv ≫
          modelSectionsEquiv X (chosenHomModel X L M)
            ((derivedSheafHomGlobalSectionsFunctor X).map (chosenHomModelMap X L M) z)) ≫
        (kInjectiveModelIso X M).hom := rfl

/-- **Stacks 08JA globally is natural in both variables.** For arbitrary morphisms `f : L' ⟶ L`
and `g : M ⟶ M'` of `D(O)`, the identification of the degree-zero global hypercohomology of
`RSheafHom(L, M)` with `Hom_{D(O)}(L, M)` carries the derived internal Hom of `f` and `g` to
precomposition with `f` and postcomposition with `g`. -/
@[stacks 08JA "global sections, naturality in both variables"]
theorem derivedSheafHomGlobalSectionsEquiv_naturality_bifunctor
    {L L' M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (f : L' ⟶ L) (g : M ⟶ M')
    (z : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv X L' M'
        ((derivedSheafHomGlobalSectionsFunctor X).map
          ((f.op, g) : ((op L, M) :
            (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
              DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
            (op L', M')) z) =
      f ≫ derivedSheafHomGlobalSectionsEquiv X L M z ≫ g := by
  have hψ : ((f.op, g) : ((op L, M) :
        (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
          DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
        (op L', M')) ≫
        chosenHomModelMap X L' M' =
      chosenHomModelMap X L M ≫
        ((((kFlatModelIso X L').hom ≫ f ≫ (kFlatModelIso X L).inv).op,
          (kInjectiveModelIso X M).hom ≫ g ≫ (kInjectiveModelIso X M').inv) :
          modelPair X (chosenHomModel X L M) ⟶ modelPair X (chosenHomModel X L' M')) := by
    refine Prod.ext ?_ ?_
    · apply Quiver.Hom.unop_inj
      simp [Category.assoc]
    · simp [Category.assoc]
  have hnat := modelSectionsEquiv_naturality X (chosenHomModel X L M) (chosenHomModel X L' M')
    ((((kFlatModelIso X L').hom ≫ f ≫ (kFlatModelIso X L).inv).op,
        (kInjectiveModelIso X M).hom ≫ g ≫ (kInjectiveModelIso X M').inv) :
      modelPair X (chosenHomModel X L M) ⟶ modelPair X (chosenHomModel X L' M'))
    ((derivedSheafHomGlobalSectionsFunctor X).map (chosenHomModelMap X L M) z)
  have hL := derivedSheafHomGlobalSectionsEquiv_eq_chosenHomModel X L M z
  have hL' := derivedSheafHomGlobalSectionsEquiv_eq_chosenHomModel X L' M'
    ((derivedSheafHomGlobalSectionsFunctor X).map
      ((f.op, g) : ((op L, M) :
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ×
            DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
          (op L', M')) z)
  have hmerge := congr_arg (fun h => (derivedSheafHomGlobalSectionsFunctor X).map h
    (show ((derivedSheafHomGlobalSectionsFunctor X).obj (op L, M) : Type u) from z)) hψ
  simp only [Functor.map_comp] at hmerge
  rw [hL', hL]
  erw [hmerge, hnat]
  simp only [Quiver.Hom.unop_op, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- **Stacks 08JA globally is the identification at *any* model, not only at the chosen one.**
For a K-flat complex `A` and a K-injective complex `I`, the identification at the classes of
`A` and `I` is the one built directly from those complexes.

The chosen representatives of `Q A` and `Q I` are different complexes, so this is a statement
and not a definitional unfolding; it is the naturality at models applied to the comparison
morphism between the given model and the chosen one. -/
theorem derivedSheafHomGlobalSectionsEquiv_eq_modelSectionsEquiv (a : homModels X)
    (z : ((derivedSheafHomGlobalSectionsFunctor X).obj (modelPair X a) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv X (DerivedCategory.Q.obj a.1.1)
        (DerivedCategory.Q.obj a.2.1) z = modelSectionsEquiv X a z := by
  have hnat := modelSectionsEquiv_naturality X a
    (chosenHomModel X (DerivedCategory.Q.obj a.1.1) (DerivedCategory.Q.obj a.2.1))
    (chosenHomModelMap X (DerivedCategory.Q.obj a.1.1) (DerivedCategory.Q.obj a.2.1)) z
  have hL := derivedSheafHomGlobalSectionsEquiv_eq_chosenHomModel X (DerivedCategory.Q.obj a.1.1)
    (DerivedCategory.Q.obj a.2.1) z
  rw [hL, hnat]
  simp only [Quiver.Hom.unop_op, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id]

end AlgebraicGeometry.RingedSite

end
