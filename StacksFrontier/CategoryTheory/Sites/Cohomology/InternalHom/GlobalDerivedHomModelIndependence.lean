module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.GlobalDerivedHomTransport

/-!
# Tag 08JA does not depend on the chosen models

Let `(C, O)` be a ringed site. The degree-zero identification
`H^0(C, RSheafHom(L, M)) = Hom_{D(O)}(L, M)` of Tag 08JA,
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv`, is constructed by choosing a
K-flat complex representing `L` and a K-injective complex representing `M` and transporting the
identification at that pair. This file proves that the result is natural in both variables for
arbitrary morphisms of `D(O)`, and so does not depend on those choices.

## Main results

* `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_naturality`: Tag 08JA is
  natural in both variables.

## Implementation notes

The proof is stated at the chosen models, whose definitions are `@[expose]`; elaborating it in the
same module as
`AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_naturality` and
`AlgebraicGeometry.RingedSite.exists_kFlat_common_refinement` exhausts the heartbeat budget on
unfolding them.

## References

* [Stacks Project, Tag 08JA](https://stacks.math.columbia.edu/tag/08JA)
* [Stacks Project, Tag 0A96](https://stacks.math.columbia.edu/tag/0A96)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Cohomology.ModuleSections

namespace AlgebraicGeometry.RingedSite

universe v u

/-- Let `g : P ⟶ Y` and `g' : P' ⟶ Y'` be compared through a common refinement `R`, by an
invertible `qu : R ⟶ P'`, a `qv : R ⟶ P` and a `qm : Y ⟶ Y'` which are the conjugates of `φ` and
`ψ` by four representing isomorphisms. Then the conjugates of `g` and `g'` by those isomorphisms
are related by `φ` and `ψ`. -/
theorem conj_of_refinement_of_category {C : Type u} [Category.{v} C]
    {P P' Y Y' L L' M M' R : C} (eA : P ≅ L) (eA' : P' ≅ L') (eI : Y ≅ M) (eI' : Y' ≅ M')
    (φ : L' ⟶ L) (ψ : M ⟶ M') (qu : R ⟶ P') (qv : R ⟶ P) (qm : Y ⟶ Y') (qn : Y' ⟶ Y')
    [IsIso qu] (hn : qn = 𝟙 Y')
    (hu : qu ≫ eA'.hom ≫ φ ≫ eA.inv = qv) (hm : qm = eI.hom ≫ ψ ≫ eI'.inv)
    (g : P ⟶ Y) (g' : P' ⟶ Y') (hcomb : qv ≫ g ≫ qm = qu ≫ g' ≫ qn) :
    (eA'.inv ≫ g') ≫ eI'.hom = φ ≫ ((eA.inv ≫ g) ≫ eI.hom) ≫ ψ := by
  rw [hn, Category.comp_id] at hcomb
  have hg' : g' = inv qu ≫ qv ≫ g ≫ qm := (IsIso.eq_inv_comp _).2 hcomb.symm
  have h4 : eA'.inv ≫ inv qu ≫ qv = φ ≫ eA.inv := by
    rw [← hu]; simp
  have h5 : qm ≫ eI'.hom = eI.hom ≫ ψ := by
    rw [hm]; simp
  rw [hg']
  simp only [Category.assoc]
  rw [h5, reassoc_of% h4]

private alias conj_of_refinement := conj_of_refinement_of_category

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-- Two morphisms of `D(O)` applied in succession to a degree-zero class of a global derived
hom act as their composite. -/
theorem homologyGlobalSections_map_comp_apply
    {Z Z' Z'' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (a : Z ⟶ Z') (b : Z' ⟶ Z'')
    (x : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj Z) : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map b)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map a) x) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map (a ≫ b)) x := by
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  rfl

variable [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- Tag 08JA at a K-flat source agrees with Tag 08JA at a K-injective internal Hom complex. -/
theorem derivedSheafHomGlobalSectionsEquivOfKFlat_eq
    (A I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) [I.IsKInjective]
    [((sheafHomComplex X A I).obj).IsKInjective] :
    derivedSheafHomGlobalSectionsEquivOfKFlat X A I hA =
      derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X A I := rfl

/-- `AlgebraicGeometry.RingedSite.derivedSheafHomGlobalSectionsEquiv_apply` with the
identification at the models written as the one for a K-injective internal Hom complex. -/
private theorem derivedSheafHomGlobalSectionsEquiv_apply'
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [((sheafHomComplex X (kFlatModel X L) (kInjectiveModel X M)).obj).IsKInjective]
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv X L M ξ =
      ((kFlatModelIso X L).inv ≫
          derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X (kFlatModel X L)
            (kInjectiveModel X M)
            ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
              ((derivedModuleGlobalSections X).map
                (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
                  (kInjectiveModelIso X M)).hom) ξ)) ≫
        (kInjectiveModelIso X M).hom :=
  Linear.homCongr_apply ℤ (kFlatModelIso X L) (kInjectiveModelIso X M)
    (derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X (kFlatModel X L) (kInjectiveModel X M)
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
            (kInjectiveModelIso X M)).hom) ξ))

/-- The two routes from `RSheafHom(L, M)` to `RSheafHom(Q R, Q I₀')` agree: transporting to the
chosen models of `L` and `M` and then along `v` and `m` is the same as inducing by `φ` and `ψ`
first, transporting to the chosen models of `L'` and `M'`, and then going along `u`. -/
theorem modelIso_route_eq_of_refinement
    {L L' M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : L' ⟶ L) (ψ : M ⟶ M')
    {R : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (u : R ⟶ kFlatModel X L') (v : R ⟶ kFlatModel X L)
    (m : kInjectiveModel X M ⟶ kInjectiveModel X M')
    (hm : DerivedCategory.Q.map m =
      (kInjectiveModelIso X M).hom ≫ ψ ≫ (kInjectiveModelIso X M').inv)
    (huv : DerivedCategory.Q.map u ≫
      ((kFlatModelIso X L').hom ≫ φ ≫ (kFlatModelIso X L).inv) = DerivedCategory.Q.map v) :
    (derivedSheafHomObjectsModelIso X (kFlatModelIso X L) (kInjectiveModelIso X M)).hom ≫
        (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map v).op).app
            (DerivedCategory.Q.obj (kInjectiveModel X M)) ≫
          ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj R))).map
            (DerivedCategory.Q.map m)) =
      (((derivedSheafHomBifunctor X).map φ.op).app M ≫
          ((derivedSheafHomBifunctor X).obj (op L')).map ψ) ≫
        (derivedSheafHomObjectsModelIso X (kFlatModelIso X L')
            (kInjectiveModelIso X M')).hom ≫
          (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map u).op).app
              (DerivedCategory.Q.obj (kInjectiveModel X M')) ≫
            ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj R))).map
              (DerivedCategory.Q.map (𝟙 (kInjectiveModel X M')))) := by
  have h1 : DerivedCategory.Q.map v ≫ (kFlatModelIso X L).hom =
      DerivedCategory.Q.map u ≫ (kFlatModelIso X L').hom ≫ φ := by
    rw [← huv]; simp
  have h2 : (kInjectiveModelIso X M).inv ≫ DerivedCategory.Q.map m =
      (ψ ≫ (kInjectiveModelIso X M').inv) ≫
        DerivedCategory.Q.map (𝟙 (kInjectiveModel X M')) := by
    rw [hm]; simp
  rw [derivedSheafHomObjectsModelIso_hom, derivedSheafHomObjectsModelIso_hom,
    derivedSheafHomBifunctor_map_comp, ← Category.assoc,
    derivedSheafHomBifunctor_map_comp, derivedSheafHomBifunctor_map_comp, h1, h2]

private alias modelIso_route_eq := modelIso_route_eq_of_refinement

/-- `AlgebraicGeometry.RingedSite.modelIso_route_eq` applied to a degree-zero class `ξ`. -/
private theorem transport_arg_eq
    {L L' M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : L' ⟶ L) (ψ : M ⟶ M')
    {R : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (u : R ⟶ kFlatModel X L') (v : R ⟶ kFlatModel X L)
    (m : kInjectiveModel X M ⟶ kInjectiveModel X M')
    (hm : DerivedCategory.Q.map m =
      (kInjectiveModelIso X M).hom ≫ ψ ≫ (kInjectiveModelIso X M').inv)
    (huv : DerivedCategory.Q.map u ≫
      ((kFlatModelIso X L').hom ≫ φ ≫ (kFlatModelIso X L).inv) = DerivedCategory.Q.map v)
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map v).op).app
                (DerivedCategory.Q.obj (kInjectiveModel X M)) ≫
              ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj R))).map
                (DerivedCategory.Q.map m)))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
              (kInjectiveModelIso X M)).hom) ξ) =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).map (DerivedCategory.Q.map u).op).app
                (DerivedCategory.Q.obj (kInjectiveModel X M')) ≫
              ((derivedSheafHomBifunctor X).obj (op (DerivedCategory.Q.obj R))).map
                (DerivedCategory.Q.map (𝟙 (kInjectiveModel X M')))))
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
            ((derivedModuleGlobalSections X).map
              (derivedSheafHomObjectsModelIso X (kFlatModelIso X L')
                (kInjectiveModelIso X M')).hom)
          ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
            ((derivedModuleGlobalSections X).map
              (((derivedSheafHomBifunctor X).map φ.op).app M ≫
                ((derivedSheafHomBifunctor X).obj (op L')).map ψ)) ξ)) := by
  rw [homologyGlobalSections_map_comp_apply, homologyGlobalSections_map_comp_apply,
    homologyGlobalSections_map_comp_apply]
  exact congrArg
    (fun f ↦ (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedModuleGlobalSections X).map f) ξ)
    (modelIso_route_eq X φ ψ u v m hm huv)

/-- Tag 08JA is natural in both variables for arbitrary morphisms of `D(O)`: for `φ : L' ⟶ L`
and `ψ : M ⟶ M'` the morphism induced on `RSheafHom` carries the identification of the
degree-zero global hypercohomology of `RSheafHom(L, M)` with `Hom_{D(O)}(L, M)` to precomposition
with `φ` and postcomposition with `ψ`. -/
theorem derivedSheafHomGlobalSectionsEquiv_naturality
    {L L' M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (φ : L' ⟶ L) (ψ : M ⟶ M')
    (ξ : ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).obj
      ((derivedModuleGlobalSections X).obj
        (((derivedSheafHomBifunctor X).obj (op L)).obj M)) : Type u)) :
    derivedSheafHomGlobalSectionsEquiv X L' M'
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).map φ.op).app M ≫
              ((derivedSheafHomBifunctor X).obj (op L')).map ψ)) ξ) =
      φ ≫ derivedSheafHomGlobalSectionsEquiv X L M ξ ≫ ψ := by
  obtain ⟨m, hm⟩ := exists_Q_map_eq_of_isKInjective X
    ((kInjectiveModelIso X M).hom ≫ ψ ≫ (kInjectiveModelIso X M').inv)
  obtain ⟨R, hR, u, v, hu, huv⟩ := exists_kFlat_common_refinement X
    ((kFlatModelIso X L').hom ≫ φ ≫ (kFlatModelIso X L).inv)
  have := isKInjective_sheafHomComplex_of_isKFlat X _ (kInjectiveModel X M) (isKFlat_kFlatModel X L)
  have := isKInjective_sheafHomComplex_of_isKFlat X _ (kInjectiveModel X M')
    (isKFlat_kFlatModel X L')
  have := isKInjective_sheafHomComplex_of_isKFlat X R (kInjectiveModel X M') hR
  have hI := derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_naturality X v m
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
      ((derivedModuleGlobalSections X).map
        (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
          (kInjectiveModelIso X M)).hom) ξ)
  have hII := derivedSheafHomGlobalSectionsEquivOfKInjectiveHom_naturality X u
    (𝟙 (kInjectiveModel X M'))
    ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (derivedSheafHomObjectsModelIso X (kFlatModelIso X L')
            (kInjectiveModelIso X M')).hom)
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (((derivedSheafHomBifunctor X).map φ.op).app M ≫
            ((derivedSheafHomBifunctor X).obj (op L')).map ψ)) ξ))
  have hcomb := hI.symm.trans ((congrArg
    (derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X R (kInjectiveModel X M'))
    (transport_arg_eq X φ ψ u v m hm huv ξ)).trans hII)
  rw [derivedSheafHomGlobalSectionsEquiv_apply' X L' M',
    derivedSheafHomGlobalSectionsEquiv_apply' X L M]
  exact conj_of_refinement (kFlatModelIso X L) (kFlatModelIso X L') (kInjectiveModelIso X M)
    (kInjectiveModelIso X M') φ ψ (DerivedCategory.Q.map u) (DerivedCategory.Q.map v)
    (DerivedCategory.Q.map m) (DerivedCategory.Q.map (𝟙 (kInjectiveModel X M')))
    (CategoryTheory.Functor.map_id _ _) huv hm
    (derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X (kFlatModel X L) (kInjectiveModel X M)
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
        ((derivedModuleGlobalSections X).map
          (derivedSheafHomObjectsModelIso X (kFlatModelIso X L)
            (kInjectiveModelIso X M)).hom) ξ))
    (derivedSheafHomGlobalSectionsEquivOfKInjectiveHom X (kFlatModel X L')
      (kInjectiveModel X M')
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (derivedSheafHomObjectsModelIso X (kFlatModelIso X L')
              (kInjectiveModelIso X M')).hom)
        ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).map
          ((derivedModuleGlobalSections X).map
            (((derivedSheafHomBifunctor X).map φ.op).app M ≫
              ((derivedSheafHomBifunctor X).obj (op L')).map ψ)) ξ)))
    hcomb

end AlgebraicGeometry.RingedSite

end
