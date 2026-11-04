module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionDatum
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedInverseSystem
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryIsoDetection
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedQuasiIsoMultiplicative

/-!
# Derived sections detect isomorphisms on a chaotic site

Let `C` be a category with the chaotic topology, `O` a sheaf of rings on it and `(A, d)` a sheaf of
differential graded `O`-algebras. A morphism `f` of `D(A, d)` is an isomorphism as soon as every
derived sections functor `RΓ(U, -) : D(A, d) ⥤ D(A(U), d)` carries it to an isomorphism.

## Main results

* `DifferentialGradedModule.quasiIsomorphisms'_of_isIso_Q_map`: an arrow of the homotopy
  category of differential graded modules over a differential graded algebra which the
  localization functor inverts is a quasi-isomorphism.
* `SheafOfModules.DifferentialGradedModule.quasiIso_of_forall_isIso_derivedSections_map`,
  `SheafOfModules.DifferentialGradedModule.quasiIsomorphisms_of_forall_isIso_derivedSections_map`:
  a homomorphism of right differential graded `A`-modules, resp. an arrow of the homotopy
  category, which every derived sections functor inverts is a quasi-isomorphism.
* `SheafOfModules.DifferentialGradedModule.isIso_of_forall_isIso_derivedSections_map`: **the
  derived sections functors of a chaotic site jointly reflect isomorphisms.**
* `SheafOfModules.DifferentialGradedModule.sectionDatum_reflectsIsomorphisms`: the same, for the
  section datum of a sheaf of differential graded algebras over a sheaf of commutative rings.

## References

* [Stacks Project, Lemma 24.35.3 (Tag 0GZH)](https://stacks.math.columbia.edu/tag/0GZH)
-/

@[expose] public noncomputable section

open CategoryTheory

universe t a v u

namespace DifferentialGradedModule

variable {R : Type a} [CommRing R] (B : DifferentialGradedAlgebra.{a, a} R)

/-- **The quasi-isomorphisms of `K(B, d)` are saturated**: an arrow of the homotopy category of
differential graded `B`-modules which becomes invertible in `D(B, d)` is a quasi-isomorphism. -/
theorem quasiIsomorphisms'_of_isIso_Q_map {X Y : HomotopyCategory.{a, a, a} B} (φ : X ⟶ Y)
    (h : IsIso ((quasiIsomorphisms' B).Q.map φ)) : quasiIsomorphisms' B φ := by
  rw [quasiIsomorphisms_iff_forall_isIso_degreeZeroCohomology]
  exact fun n => (isIso_degreeZeroCohomologyOnLocalization_map_shift_Q_map_iff B φ n).1
    ((isIso_iff_forall_isIso_degreeZeroCohomology B _).1 h n)

end DifferentialGradedModule

namespace SheafOfModules

namespace DifferentialGradedModule

attribute [local instance] Stacks.SheafOfModules.botWEqualsLocallyBijective

variable {C : Type u} [Category.{v} C] {R : Sheaf (⊥ : GrothendieckTopology C) RingCat.{t}}
  (A : DifferentialGradedAlgebra.{t, a} R)

/-- A homomorphism of right differential graded `A`-modules on a chaotic site whose class every
derived sections functor `RΓ(U, -)` inverts is a quasi-isomorphism. -/
theorem quasiIso_of_forall_isIso_derivedSections_map {M N : DifferentialGradedModule.{t, a, a} A}
    (g : M ⟶ N)
    (h : ∀ U : Cᵒᵖ, IsIso ((derivedSections A U).map
      ((toDerivedCategory.{t, a, a} A).map ((HomotopyCategory.quotient A).map g)))) :
    QuasiIso g.toHomologicalComplex := by
  refine (Stacks.SheafOfModules.quasiIso_iff_forall_quasiIso_evaluation.{t, a}
    g.toHomologicalComplex).2 fun U => ?_
  have h1 : IsIso ((sectionHomotopyFunctor A U ⋙
      (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q).map
        ((HomotopyCategory.quotient A).map g)) :=
    (NatIso.isIso_map_iff (derivedSectionsFactorization A U) _).1 (h U)
  have h2 : IsIso ((_root_.DifferentialGradedModule.quasiIsomorphisms'
      (A.sectionAlgebra U)).Q.map ((sectionModuleFunctor A U ⋙
        _root_.DifferentialGradedModule.toHomotopyCategory (A.sectionAlgebra U)).map g)) :=
    (NatIso.isIso_map_iff (Functor.isoWhiskerRight (sectionHomotopyFunctorIso A U)
      (_root_.DifferentialGradedModule.quasiIsomorphisms' (A.sectionAlgebra U)).Q) g).1 h1
  have h3 := (_root_.DifferentialGradedModule.quasiIsomorphisms_map_iff' (A.sectionAlgebra U)
    (sectionMap g U)).1
    (_root_.DifferentialGradedModule.quasiIsomorphisms'_of_isIso_Q_map _ _ h2)
  have h4 : QuasiIso (((Stacks.SheafOfModules.sectionsFunctor R U).mapHomologicalComplex
      (ComplexShape.up ℤ)).map g.toHomologicalComplex) :=
    (quasiIso_iff_of_arrow_mk_iso _ _ (sectionsArrowIso g U)).2 h3
  have h5 : QuasiIso (((forget₂ (ModuleCat.{a} (ULift.{a, 0} ℤ)) AddCommGrpCat.{a}
      ).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (((Stacks.SheafOfModules.sectionsFunctor R U).mapHomologicalComplex
          (ComplexShape.up ℤ)).map g.toHomologicalComplex)) := inferInstance
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _
    (forget₂ (ModuleCat.{a} (R.obj.obj U)) AddCommGrpCat.{a})).1 h5

/-- An arrow of the homotopy category whose image in `D(A, d)` every derived sections functor
inverts is a quasi-isomorphism. -/
theorem quasiIsomorphisms_of_forall_isIso_derivedSections_map
    {X Y : HomotopyCategory.{t, a, a} A} (ψ : X ⟶ Y)
    (h : ∀ U : Cᵒᵖ, IsIso ((derivedSections A U).map ((toDerivedCategory.{t, a, a} A).map ψ))) :
    quasiIsomorphisms.{t, a, a} A ψ := by
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A).map_surjective ψ
  exact (quasiIsomorphisms_quotient_map_iff g).2
    (quasiIso_of_forall_isIso_derivedSections_map A g h)

section SingleUniverse

/-! ### A site, its morphisms and its sheaf of rings in one universe -/

variable {C : Type u} [Category.{u} C] [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{a}]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  (A : DifferentialGradedAlgebra.{u, a} (Sheaf.toRingCat (⊥ : GrothendieckTopology C) Osharp))

/-- **On a chaotic site the derived sections functors jointly reflect isomorphisms**: a morphism
of `D(A, d)` which every `RΓ(U, -)` carries to an isomorphism is an isomorphism. -/
theorem isIso_of_forall_isIso_derivedSections_map {X Y : derivedCategory.{u, a, a} A}
    (f : X ⟶ Y) (h : ∀ U : Cᵒᵖ, IsIso ((derivedSections A U).map f)) : IsIso f := by
  let : (quasiIsomorphisms.{u, a, a} A).HasLeftCalculusOfFractions :=
    quasiIsomorphisms_hasLeftCalculusOfFractions (X := ⟨C, ⊥, Osharp⟩) A
  have : (toDerivedCategory.{u, a, a} A).EssSurj :=
    Localization.essSurj (toDerivedCategory.{u, a, a} A) (quasiIsomorphisms.{u, a, a} A)
  let eX := (toDerivedCategory.{u, a, a} A).objObjPreimageIso X
  let eY := (toDerivedCategory.{u, a, a} A).objObjPreimageIso Y
  suffices IsIso (eX.hom ≫ f ≫ eY.inv) by
    rw [show f = eX.inv ≫ (eX.hom ≫ f ≫ eY.inv) ≫ eY.hom by simp]
    infer_instance
  obtain ⟨ψ, hψ⟩ := Localization.exists_leftFraction (toDerivedCategory.{u, a, a} A)
    (quasiIsomorphisms.{u, a, a} A) (eX.hom ≫ f ≫ eY.inv)
  have hs : IsIso ((toDerivedCategory.{u, a, a} A).map ψ.s) :=
    Localization.inverts (toDerivedCategory.{u, a, a} A) (quasiIsomorphisms.{u, a, a} A) _ ψ.hs
  have hmap : eX.hom ≫ f ≫ eY.inv =
      (toDerivedCategory.{u, a, a} A).map ψ.f ≫ inv ((toDerivedCategory.{u, a, a} A).map ψ.s) :=
    hψ
  have hf : quasiIsomorphisms.{u, a, a} A ψ.f := by
    refine quasiIsomorphisms_of_forall_isIso_derivedSections_map A ψ.f fun U => ?_
    have h1 : IsIso ((derivedSections A U).map (eX.hom ≫ f ≫ eY.inv)) := by
      rw [Functor.map_comp, Functor.map_comp]
      have := h U
      infer_instance
    rw [hmap, Functor.map_comp] at h1
    exact IsIso.of_isIso_comp_right _ ((derivedSections A U).map
      (inv ((toDerivedCategory.{u, a, a} A).map ψ.s)))
  have : IsIso ((toDerivedCategory.{u, a, a} A).map ψ.f) :=
    Localization.inverts (toDerivedCategory.{u, a, a} A) (quasiIsomorphisms.{u, a, a} A) _ hf
  rw [hmap]
  infer_instance

end SingleUniverse

end DifferentialGradedModule

section SectionDatum

variable {C : Type u} [Category.{u} C]
  [(⊥ : GrothendieckTopology C).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify (⊥ : GrothendieckTopology C) (Type a)]
  [HasSheafify (⊥ : GrothendieckTopology C) AddCommGrpCat.{a}]
  {Osharp : Sheaf (⊥ : GrothendieckTopology C) CommRingCat.{u}}
  (A : DifferentialGradedAlgebra.{u, a}
    (Sheaf.toRingCat (⊥ : GrothendieckTopology C) Osharp))

/-- **The section datum of a sheaf of differential graded algebras on a chaotic site reflects
isomorphisms**: a morphism of `D(A, d)` which every derived sections functor of the section datum
carries to an isomorphism is an isomorphism. -/
theorem DifferentialGradedModule.sectionDatum_reflectsIsomorphisms :
    (DifferentialGradedModule.sectionDatum A).ReflectsIsomorphisms :=
  fun _ _ f h => DifferentialGradedModule.isIso_of_forall_isIso_derivedSections_map A f h

end SectionDatum

end SheafOfModules
