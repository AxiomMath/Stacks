module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomCohomologyIso
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomValueCohomology
public import StacksFrontier.CategoryTheory.Localization.LeftFraction.HomAsColimitShift

/-!
# The cohomology of a value of derived Hom is a morphism group of the derived category

Let `A` be an abelian category whose morphisms are sets and let `K` be a cochain complex in `A`.
Assume Tag 09LK's own hypothesis: the right derived functor of the abelian-group-valued
`Hom(K, -) : K(A) ⥤ D(Ab)` is everywhere defined. Then
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomValueCohomology.lean` assembles the
functor `R Hom(K, -) : D(A) ⥤ D(Ab)` and shows that its value at `Q(X)` has

`H^n(R Hom(K, -)(Q X)) = colim_{(s : X ⟶ Y) ∈ X/W} H^n Hom^•(K, Y)`,

the colimit over the quasi-isomorphisms out of `X`. This file identifies the right-hand side with
a morphism group of the derived category:

`H^n(R Hom(K, -)(Q X)) ≅ Hom_{D(A)}(Q K, (Q X)⟦n⟧)`.

The identification is forced, not chosen: both sides are colimits over the same index category
`X/W` of isomorphic diagrams. On the left the diagram is `(s : X ⟶ Y) ↦ H^n Hom^•(K, Y)`; on the
right, by Stacks 05Q0 in the shifted shape of
`StacksFrontier/CategoryTheory/Localization/LeftFraction/HomAsColimitShift.lean`, the morphisms
`Q K ⟶ (Q X)⟦n⟧` of the localization are the colimit of the morphism sets `Mor_{K(A)}(K, Y⟦n⟧)`
over the same `X/W`. The two diagrams are identified by
`CochainComplex.homologyCoyonedaNatIso` of
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomCohomologyIso.lean`,
`H^n(Hom^•(K, -)) ≅ Hom_{K(A)}(K, (-)⟦n⟧)`.

## Main definitions

* `CochainComplex.derivedHomValueDiagramIso`: the isomorphism of the two diagrams over `X/W`.
* `CochainComplex.derivedHomValueHomIso`: the comparison of the two colimits, as an isomorphism
  of lifted types.
* `CochainComplex.derivedHomValueHomEquiv`: the bijection
  `H^n(R Hom(K, -)(Q X)) ≃ Hom_{D(A)}(Q K, (Q X)⟦n⟧)`.
* `CochainComplex.derivedHomValueHomAddEquiv`: **the identification itself**, that bijection as an
  isomorphism of abelian groups.

## Main results

* `CochainComplex.derivedHomValueHomEquiv_apply` and
  `CochainComplex.derivedHomValueHomEquiv_apply_of_hom`: **the identification is the left
  fraction.** The second is the displayed formula the comparison is wanted for: a quasi-isomorphism
  `s : X ⟶ Y` and a morphism `f : K ⟶ Y⟦n⟧` of the homotopy category determine a degree-`n`
  cohomology class of `Hom^•(K, Y)`, and the image of that class in `H^n(R Hom(K, -)(Q X))` is
  carried to `Q(s)⟦n⟧⁻¹ ∘ Q(f)`.
* `CochainComplex.derivedHomValueHomEquiv_add`: the identification is additive.

## Implementation notes

*Why additivity needs an argument.* The comparison is produced by the universal property of a
colimit **in types**: `CochainComplex.isColimitMapCoconeHomologyType` composes with the forgetful
functor precisely so that the two colimits live in the same category, and that functor is where
the group structure is dropped, so additivity is not part of what the two colimits give. It is
recovered from the legs. Each leg of the comparison is additive — it is the identification
`CochainComplex.homologyHomAddEquiv` of Tag 09LC, followed by the additive functor `Q` and by
composition with a fixed morphism of a preadditive category — and the legs of a colimit cocone in
types are jointly surjective, so every element comes from a leg
(`CochainComplex.exists_homologyFunctor_map_derivedHomForgetUnitCocone_ι_app`). Filteredness of
`X/W`, which is the other half of Stacks 05Q0, then puts any two elements on the *same* leg
(`CochainComplex.exists_homologyFunctor_map_derivedHomForgetUnitCocone_ι_app_pair`), and that is
what makes a statement about a sum reduce to a statement about one Hom complex.

*Why the universes are as they are.* The colimit on the left is a colimit of the underlying sets
of `ℤ`-modules, which live in the universe of the morphisms of `A`, here `Type 0`; the colimit on
the right is a colimit of morphism sets of `D(A)`, which live in `HasDerivedCategory.{v} A`'s
universe. Both are therefore lifted to `Type v` before being compared, by
`CategoryTheory.uliftFunctor`, and `CochainComplex.derivedHomValueHomEquiv` strips the two lifts
again. No constraint between the two universes is imposed: that is what the universe-general form
of Stacks 05Q0 in
`StacksFrontier/CategoryTheory/Localization/LeftFraction/HomAsColimitShift.lean` was proved for.

*Where the hypothesis enters.* Only through
`CochainComplex.isRightDerivedValueAt_derivedHomForgetUnitCocone`, i.e. through Tag 09LK's own
hypothesis on the abelian-group-valued functor. Nothing here uses the stronger hypothesis under
which the differential-graded-module-valued `R Hom(K, -) : D(A) ⥤ D(E, d)` is constructed.

## References

* [Stacks, Tag 05Q0](https://stacks.math.columbia.edu/tag/05Q0), whose displayed formula
  [Tag 05Q1] is the right-hand colimit; [Tag 05S9](https://stacks.math.columbia.edu/tag/05S9),
  being defined at an object; [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC), the
  cohomology of the Hom complex; [Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), whose
  hypothesis is assumed throughout.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty Opposite

universe v w u

namespace CochainComplex

variable (A : Type u) [Category.{0} A] [Abelian A] [HasDerivedCategory.{v} A]
  (K : CochainComplex A ℤ) [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]
  (X : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ)

/-- **The two diagrams over `X/W` agree.** The diagram whose colimit is the degree-`n` cohomology
of the value of derived Hom at `Q(X)`, namely `(s : X ⟶ Y) ↦ H^n Hom^•(K, Y)` read in types and
lifted, is isomorphic to the diagram whose colimit is `Hom_{D(A)}(Q K, (Q X)⟦n⟧)` by Stacks 05Q0,
namely `(s : X ⟶ Y) ↦ Mor_{K(A)}(K, Y⟦n⟧)` lifted.

It is `CochainComplex.homologyCoyonedaNatIso` restricted along `X/W ⥤ K(A)` and lifted. -/
def derivedHomValueDiagramIso :
    (MorphismProperty.Under.forget (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ X ⋙
        Under.forget X ⋙ homToDerivedCategoryForget A K) ⋙
      (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n ⋙
        forget (ModuleCat.{0} ℤ) ⋙ uliftFunctor.{v}) ≅
      MorphismProperty.Under.forget (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ X ⋙
        CategoryTheory.Under.forget X ⋙
          CategoryTheory.shiftFunctor (HomotopyCategory A (ComplexShape.up ℤ)) n ⋙
            coyoneda.obj (op ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K)) ⋙
              uliftFunctor.{v} :=
  Functor.isoWhiskerLeft
    (MorphismProperty.Under.forget (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ X ⋙
      CategoryTheory.Under.forget X)
    (Functor.isoWhiskerRight (homologyCoyonedaNatIso A K n) uliftFunctor.{v})

omit [HasDerivedCategory A] in
/-- The component of `CochainComplex.derivedHomValueDiagramIso` at an object `s : X ⟶ Y` of `X/W`
is the identification `H^n(Hom^•(K, Y)) ≅ Hom_{K(A)}(K, Y⟦n⟧)` of Tag 09LC. -/
theorem derivedHomValueDiagramIso_hom_app_apply
    (S : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ X)
    (x : ULift.{v} ↥((homToDerivedCategoryForget A K ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj S.right)) :
    (derivedHomValueDiagramIso A K X n).hom.app S x =
      ULift.up (homologyHomAddEquiv A K n S.right x.down) :=
  rfl

variable (h : (homToDerivedCategoryForget A K).IsRightDerivable
  (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))

/-- **The comparison of the two colimits.** Under Tag 09LK's own hypothesis, the lift of the
degree-`n` cohomology of `R Hom(K, -)(Q X)` and the lift of the morphism group
`Hom_{D(A)}(Q K, (Q X)⟦n⟧)` are colimits over `X/W` of isomorphic diagrams, hence canonically
isomorphic. -/
def derivedHomValueHomIso :
    ULift.{v} ↥((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
        ((derivedHomForgetFunctor A K h).obj (DerivedCategory.Qh.obj X))) ≅
      ULift.{0} (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⟶
        (DerivedCategory.Qh.obj X)⟦n⟧) :=
  IsColimit.coconePointsIsoOfNatIso
    (isColimitMapCoconeHomologyType.{v} A K
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) n
      (isRightDerivedValueAt_derivedHomForgetUnitCocone A K h X))
    ((HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).isColimitShiftedUnderHomCoconeCommShift
      DerivedCategory.Qh ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) X n)
    (derivedHomValueDiagramIso A K X n)

/-- **`H^n(R Hom(K, -)(Q X)) ≅ Hom_{D(A)}(Q K, (Q X)⟦n⟧)`.** Under Tag 09LK's own hypothesis —
everywhere-definedness of the right derived functor of the abelian-group-valued
`Hom(K, -) : K(A) ⥤ D(Ab)` — the degree-`n` cohomology of the value at `Q(X)` of the assembled
`R Hom(K, -) : D(A) ⥤ D(Ab)` is the group of morphisms `Q K ⟶ (Q X)⟦n⟧` of the derived category.

The bijection is pinned down by `CochainComplex.derivedHomValueHomEquiv_apply_of_hom`: it is the
one sending the class of a quasi-isomorphism `s : X ⟶ Y` together with a morphism
`f : K ⟶ Y⟦n⟧` to the left fraction `Q(s)⟦n⟧⁻¹ ∘ Q(f)`. -/
def derivedHomValueHomEquiv :
    ↥((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
        ((derivedHomForgetFunctor A K h).obj (DerivedCategory.Qh.obj X))) ≃
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⟶
        (DerivedCategory.Qh.obj X)⟦n⟧) :=
  Equiv.ulift.symm.trans ((derivedHomValueHomIso A K X n h).toEquiv.trans Equiv.ulift)

/-- **The comparison is the left fraction.** Let `s : X ⟶ Y` be a quasi-isomorphism out of `X` and
let `x` be a degree-`n` cohomology class of `Hom^•(K, Y)`. The image of `x` in
`H^n(R Hom(K, -)(Q X))`, along the leg of the comparison cocone at `s`, is carried by
`CochainComplex.derivedHomValueHomIso` to
`Q(f) ≫ (Q.commShiftIso n).hom ≫ Q(s)⟦n⟧⁻¹`, where `f : K ⟶ Y⟦n⟧` is the morphism of the homotopy
category that `x` is; that is the morphism of `D(A)` written `Q(s)⟦n⟧⁻¹ ∘ Q(f)`.

This is the leg of the colimit cocone of Stacks 05Q0 in the shifted shape,
`MorphismProperty.shiftedUnderHomCoconeCommShift_ι_app_apply`, transported along the colimit
comparison. -/
theorem derivedHomValueHomIso_hom_apply
    (S : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ X)
    (x : ↥((homToDerivedCategoryForget A K ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj S.right)) :
    (derivedHomValueHomIso A K X n h).hom
        (ULift.up ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((derivedHomForgetUnitCocone A K h X).ι.app S) x)) =
      ULift.up (DerivedCategory.Qh.map (homologyHomAddEquiv A K n S.right x) ≫
        (DerivedCategory.Qh.commShiftIso n).hom.app S.right ≫
          CategoryTheory.inv ((DerivedCategory.Qh.map S.hom)⟦n⟧')) := by
  have key : (derivedHomValueHomIso A K X n h).hom
        (ULift.up ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((derivedHomForgetUnitCocone A K h X).ι.app S) x)) =
      ((HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).shiftedUnderHomCoconeCommShift
            DerivedCategory.Qh ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) X
            n).ι.app S
        ((derivedHomValueDiagramIso A K X n).hom.app S (ULift.up x)) :=
    types_congr_hom (IsColimit.comp_coconePointsIsoOfNatIso_hom
      (isColimitMapCoconeHomologyType.{v} A K
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) n
        (isRightDerivedValueAt_derivedHomForgetUnitCocone A K h X))
      ((HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).isColimitShiftedUnderHomCoconeCommShift
        DerivedCategory.Qh ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) X n)
      (derivedHomValueDiagramIso A K X n) S) (ULift.up x)
  exact key.trans (MorphismProperty.shiftedUnderHomCoconeCommShift_ι_app_apply
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Qh
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) X n S
    ((derivedHomValueDiagramIso A K X n).hom.app S (ULift.up x)))

/-- **The identification is the left fraction.** The statement of
`CochainComplex.derivedHomValueHomIso_hom_apply` for the bijection
`CochainComplex.derivedHomValueHomEquiv`, with the universe lifts stripped. -/
theorem derivedHomValueHomEquiv_apply
    (S : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ X)
    (x : ↥((homToDerivedCategoryForget A K ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj S.right)) :
    derivedHomValueHomEquiv A K X n h
        ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((derivedHomForgetUnitCocone A K h X).ι.app S) x) =
      DerivedCategory.Qh.map (homologyHomAddEquiv A K n S.right x) ≫
        (DerivedCategory.Qh.commShiftIso n).hom.app S.right ≫
          CategoryTheory.inv ((DerivedCategory.Qh.map S.hom)⟦n⟧') :=
  congrArg ULift.down (derivedHomValueHomIso_hom_apply A K X n h S x)

/-- **The displayed formula.** A quasi-isomorphism `s : X ⟶ Y` and a morphism `f : K ⟶ Y⟦n⟧` of
the homotopy category determine a degree-`n` cohomology class of `Hom^•(K, Y)`, hence an element
of `H^n(R Hom(K, -)(Q X))`, and the identification carries that element to the left fraction
`Q(s)⟦n⟧⁻¹ ∘ Q(f)`. -/
theorem derivedHomValueHomEquiv_apply_of_hom
    (S : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ X)
    (f : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K ⟶ S.right⟦n⟧) :
    derivedHomValueHomEquiv A K X n h
        ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((derivedHomForgetUnitCocone A K h X).ι.app S)
          ((homologyHomAddEquiv A K n S.right).symm f)) =
      DerivedCategory.Qh.map f ≫ (DerivedCategory.Qh.commShiftIso n).hom.app S.right ≫
        CategoryTheory.inv ((DerivedCategory.Qh.map S.hom)⟦n⟧') := by
  rw [derivedHomValueHomEquiv_apply, AddEquiv.apply_symm_apply]

/-- **Every cohomology class of the value comes from a Hom complex.** The legs of a colimit cocone
in types are jointly surjective, so a degree-`n` cohomology class of `R Hom(K, -)(Q X)` is the
image of a degree-`n` cohomology class of `Hom^•(K, Y)` for some quasi-isomorphism
`s : X ⟶ Y`. -/
theorem exists_homologyFunctor_map_derivedHomForgetUnitCocone_ι_app
    (y : ↥((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
      ((derivedHomForgetFunctor A K h).obj (DerivedCategory.Qh.obj X)))) :
    ∃ (S : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ X)
      (x : ↥((homToDerivedCategoryForget A K ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj S.right)),
      (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
        ((derivedHomForgetUnitCocone A K h X).ι.app S) x = y := by
  obtain ⟨S, z, hz⟩ := Limits.Types.jointly_surjective_of_isColimit
    (isColimitMapCoconeHomologyType.{v} A K
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) n
      (isRightDerivedValueAt_derivedHomForgetUnitCocone A K h X)) (ULift.up y)
  exact ⟨S, z.down, congrArg ULift.down hz⟩

/-- **The legs of the comparison cocone are compatible with a morphism of `X/W`.** Composing the
leg at `s : X ⟶ Y` with the map induced by a morphism `Y ⟶ Y'` over `X` is the leg at the target.
This is the cocone relation, read on degree-`n` cohomology and elementwise. -/
theorem homologyFunctor_map_derivedHomForgetUnitCocone_ι_app_map
    {S T : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ X} (φ : S ⟶ T)
    (x : ↥((homToDerivedCategoryForget A K ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj S.right)) :
    (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
        ((derivedHomForgetUnitCocone A K h X).ι.app T)
        ((homToDerivedCategoryForget A K ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map φ.right x) =
      (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
        ((derivedHomForgetUnitCocone A K h X).ι.app S) x := by
  conv_rhs => rw [← (derivedHomForgetUnitCocone A K h X).w φ]
  rw [Functor.map_comp]
  rfl

/-- **Two cohomology classes of the value come from one and the same Hom complex.** The index
category `X/W` is filtered, by Stacks 05Q0, so the two quasi-isomorphisms produced by
`CochainComplex.exists_homologyFunctor_map_derivedHomForgetUnitCocone_ι_app` can be replaced by a
single one. -/
theorem exists_homologyFunctor_map_derivedHomForgetUnitCocone_ι_app_pair
    (α β : ↥((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
      ((derivedHomForgetFunctor A K h).obj (DerivedCategory.Qh.obj X)))) :
    ∃ (S : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ X)
      (a b : ↥((homToDerivedCategoryForget A K ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj S.right)),
      (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((derivedHomForgetUnitCocone A K h X).ι.app S) a = α ∧
        (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((derivedHomForgetUnitCocone A K h X).ι.app S) b = β := by
  have := MorphismProperty.isFiltered_under_of_hasLeftCalculusOfFractions
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) X
  obtain ⟨S, a, ha⟩ :=
    exists_homologyFunctor_map_derivedHomForgetUnitCocone_ι_app A K X n h α
  obtain ⟨T, b, hb⟩ :=
    exists_homologyFunctor_map_derivedHomForgetUnitCocone_ι_app A K X n h β
  exact ⟨IsFiltered.max S T,
    (homToDerivedCategoryForget A K ⋙ DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
      (IsFiltered.leftToMax S T).right a,
    (homToDerivedCategoryForget A K ⋙ DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
      (IsFiltered.rightToMax S T).right b,
    (homologyFunctor_map_derivedHomForgetUnitCocone_ι_app_map A K X n h
      (IsFiltered.leftToMax S T) a).trans ha,
    (homologyFunctor_map_derivedHomForgetUnitCocone_ι_app_map A K X n h
      (IsFiltered.rightToMax S T) b).trans hb⟩

/-- **The identification is additive.** Any two cohomology classes of `R Hom(K, -)(Q X)` come from
one and the same Hom complex, because `X/W` is filtered, and on each Hom complex the
identification is a composite of additive maps: the identification
`CochainComplex.homologyHomAddEquiv` of Tag 09LC, the additive functor `Q`, and composition with
a fixed morphism in a preadditive category. -/
theorem derivedHomValueHomEquiv_add
    (α β : ↥((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
      ((derivedHomForgetFunctor A K h).obj (DerivedCategory.Qh.obj X)))) :
    derivedHomValueHomEquiv A K X n h (α + β) =
      derivedHomValueHomEquiv A K X n h α + derivedHomValueHomEquiv A K X n h β := by
  obtain ⟨S, a, b, ha, hb⟩ :=
    exists_homologyFunctor_map_derivedHomForgetUnitCocone_ι_app_pair A K X n h α β
  have hadd : (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
        ((derivedHomForgetUnitCocone A K h X).ι.app S) (a + b) =
      (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((derivedHomForgetUnitCocone A K h X).ι.app S) a +
        (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((derivedHomForgetUnitCocone A K h X).ι.app S) b :=
    map_add _ a b
  calc derivedHomValueHomEquiv A K X n h (α + β)
      = derivedHomValueHomEquiv A K X n h
          ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
            ((derivedHomForgetUnitCocone A K h X).ι.app S) (a + b)) :=
        congrArg _ (hadd.trans (congrArg₂ (· + ·) ha hb)).symm
    _ = DerivedCategory.Qh.map (homologyHomAddEquiv A K n S.right (a + b)) ≫
          (DerivedCategory.Qh.commShiftIso n).hom.app S.right ≫
            CategoryTheory.inv ((DerivedCategory.Qh.map S.hom)⟦n⟧') :=
        derivedHomValueHomEquiv_apply A K X n h S (a + b)
    _ = (DerivedCategory.Qh.map (homologyHomAddEquiv A K n S.right a) +
            DerivedCategory.Qh.map (homologyHomAddEquiv A K n S.right b)) ≫
          (DerivedCategory.Qh.commShiftIso n).hom.app S.right ≫
            CategoryTheory.inv ((DerivedCategory.Qh.map S.hom)⟦n⟧') := by
        rw [map_add, Functor.map_add]
    _ = DerivedCategory.Qh.map (homologyHomAddEquiv A K n S.right a) ≫
            (DerivedCategory.Qh.commShiftIso n).hom.app S.right ≫
              CategoryTheory.inv ((DerivedCategory.Qh.map S.hom)⟦n⟧') +
          DerivedCategory.Qh.map (homologyHomAddEquiv A K n S.right b) ≫
            (DerivedCategory.Qh.commShiftIso n).hom.app S.right ≫
              CategoryTheory.inv ((DerivedCategory.Qh.map S.hom)⟦n⟧') :=
        Preadditive.add_comp _ _ _ _ _ _
    _ = derivedHomValueHomEquiv A K X n h α + derivedHomValueHomEquiv A K X n h β :=
        congrArg₂ (· + ·)
          ((derivedHomValueHomEquiv_apply A K X n h S a).symm.trans (congrArg _ ha))
          ((derivedHomValueHomEquiv_apply A K X n h S b).symm.trans (congrArg _ hb))

/-- **`H^n(R Hom(K, -)(Q X)) ≅ Hom_{D(A)}(Q K, (Q X)⟦n⟧)` as abelian groups.** Under Tag 09LK's
own hypothesis — everywhere-definedness of the right derived functor of the abelian-group-valued
`Hom(K, -) : K(A) ⥤ D(Ab)` — the degree-`n` cohomology of the value at `Q(X)` of the assembled
`R Hom(K, -) : D(A) ⥤ D(Ab)` is the group of morphisms `Q K ⟶ (Q X)⟦n⟧` of the derived
category.

The isomorphism is pinned down by `CochainComplex.derivedHomValueHomEquiv_apply_of_hom`: it is
the one sending the class determined by a quasi-isomorphism `s : X ⟶ Y` and a morphism
`f : K ⟶ Y⟦n⟧` to the left fraction `Q(s)⟦n⟧⁻¹ ∘ Q(f)`. -/
def derivedHomValueHomAddEquiv :
    ↥((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
        ((derivedHomForgetFunctor A K h).obj (DerivedCategory.Qh.obj X))) ≃+
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⟶
        (DerivedCategory.Qh.obj X)⟦n⟧) :=
  { derivedHomValueHomEquiv A K X n h with
    map_add' := derivedHomValueHomEquiv_add A K X n h }

/-- The additive isomorphism is the bijection. -/
@[simp] theorem derivedHomValueHomAddEquiv_apply
    (y : ↥((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
      ((derivedHomForgetFunctor A K h).obj (DerivedCategory.Qh.obj X)))) :
    derivedHomValueHomAddEquiv A K X n h y = derivedHomValueHomEquiv A K X n h y :=
  rfl

end CochainComplex

end
