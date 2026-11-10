module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Exactness
public import StacksFrontier.Homology.KFlat.BifunctorCommShiftTwoInstances
public import Mathlib.CategoryTheory.ObjectProperty.Shift
import StacksCore.Tactic.StacksAttribute

/-!
# The derived tensor product of a ringed site commutes with the shifts in both variables

Let `(C, O)` be a ringed site.  `Stacks.SheafOfModules.derivedTensorBifunctor` is the derived
tensor product `- ⊗^L_O -` on `D(Mod(O))`, obtained by descending the total tensor complex
`Tot(- ⊗_O -)` along the K-flat complexes in the first variable and along all complexes in the
second.  This file equips it with `CategoryTheory.Functor.CommShift₂Int`, the two-variable shift
coherence of [Stacks, Tag 079U] — the commutation isomorphisms in the two variables exist, are
natural, and commute with each other up to Mathlib's sign `(-1) ^ (p * q)` — and proves it exact
in each variable **at the commutation with the shift that that coherence carries**.

## Main results

* `Stacks.SheafOfModules.derivedTensorBifunctor_commShift₂Int`: **the derived tensor product
  commutes with the shifts in both variables.**
* `Stacks.SheafOfModules.derivedTensorBifunctor_isTriangulated_obj` and
  `derivedTensorBifunctor_isTriangulated_flipObj`: **it is exact in each variable**, at
  `CategoryTheory.Functor.CommShift₂.commShiftObj` and `commShiftFlipObj` rather than at an
  unrelated witness.

## Implementation notes

**The coherence is one application of the two-variable localization descent.**
`derivedTensorBifunctor` is a `CategoryTheory.Localization.lift₂` of `kFlatTensorToDerived`
along `kFlatComplexQ` and `DerivedCategory.Q`, so
`CategoryTheory.Functor.CommShift₂.ofLocalizationInt` applies once its source has the coherence.
That source is `ι ⋙ (Tot(- ⊗_O -) ⋙ (whiskeringRight _ _ _).obj Q)`, i.e. Mathlib's sign
coherence on cochain complexes followed by `CategoryTheory.Functor.CommShift₂.postcompInt` and
`precomp₁`.  Instance search does not cross the first step unaided, because `tensorComplex` is a
plain `def` and so is not unfolded when the discrimination tree is consulted;
`tensorComplex_commShift₂Int` crosses it with the coherence of the copy
`CategoryTheory.Functor.map₂HomologicalComplexReg` that `tensorComplex` unfolds to, and instance
search at the unfolded spelling of the composite does the rest.

**Exactness is the part that is not a descent.**
`CategoryTheory.Localization.isTriangulated_objCommShift` reduces each exactness goal to the
*inner* one-variable descent, and for this bifunctor both inner descents come off a
complex-level localization — `DerivedCategory.Q` out of `CochainComplex` for the second
variable, `kFlatComplexQ` out of the K-flat complexes for the first.  Neither source is
pre-triangulated, so Stacks 05R7 (`CategoryTheory.Functor.isTriangulated_of_localization`) does
not apply there at all; exactness is only available further up, at the *homotopy-level*
descents along `DerivedCategory.Qh` and `Stacks.SheafOfModules.kFlatQ`, where Tag 06YM's `Φ`
and `Φ^R` live.

The two levels are joined by `CategoryTheory.Functor.isTriangulated_of_precomp_iso` along the
homotopy-level localization.  Its hypothesis is that the comparison isomorphism commutes with
the shifts *for the complex-level structure*, and that is supplied by
`CategoryTheory.Localization.natTrans_commShift_of_whiskerLeft`: the comparison is a
transformation between functors out of a localization, so it suffices to check its restriction,
and the restriction is computed from the two factorisations of `Tot(A ⊗_O -) ⋙ Q`.

**The objects of the site live in their own universe `c`**, independent of the universe `u` of
its morphisms, of the sections of its structure sheaf and of the sections of its modules, and of
the derived category's hom universe `d`, as for a small étale site.  The coherence is a
two-variable localization descent and the exactness a one-variable one, and neither involves the
objects of the site.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 05R7](https://stacks.math.columbia.edu/tag/05R7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe c u d

namespace Stacks.SheafOfModules

/-! ### The shift compatibility of `bifunctorPhiFactors`, read at the copy

`Stacks.SheafOfModules.Tensor.tensorComplex` unfolds to
`CategoryTheory.Functor.map₂HomologicalComplexReg`, Mathlib's
`CategoryTheory.Functor.map₂HomologicalComplex` with the regular-hinted copies
`HomologicalComplex.mapBifunctorReg` and `HomologicalComplex.mapBifunctorMapReg` as objects and
morphisms, while `Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors` and
`bifunctorPhiRFactors` are stated with Mathlib's. The exactness proofs below need the
compatibility of these two isomorphisms with the shifts when their targets are read at the copy.
The two lemmas state it for an arbitrary bifunctor, where the kernel compares the copy with
Mathlib's spelling without evaluating a tensor product. They exist only because of the copies of
`StacksFrontier/Algebra/Homology/MapBifunctorReg.lean`, and go away with them. -/

namespace Tensor.Reduction

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Preadditive A] [Preadditive B] [Preadditive D]
  (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
  [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
      (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
    K₁.HasMapBifunctorReg K₂ F (ComplexShape.up ℤ)]

/-- `bifunctorPhiFactors F G` commutes with the shifts when its target `Tot(F(G, -)) ⋙ quotient`
carries the shift of the copy `CategoryTheory.Functor.map₂HomologicalComplexReg`. -/
theorem bifunctorPhiFactors_commShift_reg (G : HomologicalComplex A (ComplexShape.up ℤ)) :
    letI := bifunctorXi F G
    NatTrans.CommShift (Iso.hom
      (Y := (F.map₂HomologicalComplexReg (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj G ⋙ HomotopyCategory.quotient D (ComplexShape.up ℤ))
      (bifunctorPhiFactors F G)) ℤ :=
  Quotient.liftCommShift_compatibility _ _ _ _

/-- `bifunctorPhiFactors_commShift_reg` for the right factor: `bifunctorPhiRFactors F G`
commutes with the shifts when its target `Tot(F(-, G)) ⋙ quotient` carries the shift of the
copy. -/
theorem bifunctorPhiRFactors_commShift_reg (G : HomologicalComplex B (ComplexShape.up ℤ)) :
    letI := bifunctorXiR F G
    NatTrans.CommShift (Iso.hom
      (Y := (F.map₂HomologicalComplexReg (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).flip.obj G ⋙ HomotopyCategory.quotient D (ComplexShape.up ℤ))
      (bifunctorPhiRFactors F G)) ℤ :=
  Quotient.liftCommShift_compatibility _ _ _ _

end Tensor.Reduction

variable (X : AlgebraicGeometry.RingedSite.{c, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{c, u, u, u, u} X.O).obj M).Additive]
  [∀ (K₁ K₂ : CochainComplex
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O)) ℤ),
    HomologicalComplex.HasMapBifunctorReg K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasDerivedCategory.{d}
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))]

attribute [local instance] derivedTensorBifunctorLifting
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.tensorComplex

/-- The total tensor complex `Tot(- ⊗_O -)` on cochain complexes of `O`-modules commutes with the
shifts in both variables, with Mathlib's sign coherence. -/
instance tensorComplex_commShift₂Int :
    (Stacks.SheafOfModules.Tensor.tensorComplex X.O).CommShift₂Int :=
  Functor.map₂HomologicalComplexReg_commShift₂Int _

/-- The functor sending a K-flat complex `K` and a complex `L` to the image of `Tot(K ⊗_O L)` in
the derived category commutes with the shifts in both variables. -/
instance kFlatTensorToDerived_commShift₂Int : (kFlatTensorToDerived X).CommShift₂Int :=
  (inferInstance : ((kFlatComplexes X).ι ⋙
    (Stacks.SheafOfModules.Tensor.tensorComplex X.O ⋙
      (Functor.whiskeringRight _ _ _).obj DerivedCategory.Q)).CommShift₂Int)

/-- The derived tensor product `- ⊗^L_O -` on `D(Mod(O))` commutes with the shifts in both
variables, with Mathlib's sign coherence. -/
instance derivedTensorBifunctor_commShift₂Int :
    (derivedTensorBifunctor X).CommShift₂Int :=
  Functor.CommShift₂.ofLocalizationInt (kFlatComplexQ X) DerivedCategory.Q
    (kFlatComplexQuasiIso X)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
      (ComplexShape.up ℤ))
    (kFlatTensorToDerived X) (derivedTensorBifunctor X)

/-! ### The shift on the K-flat models, and the two factorisations of `Pc.ι ⋙ Q` -/

/-- The quotient from K-flat complexes to K-flat objects of the homotopy category commutes
with the shifts. -/
instance complexSubcategoryQuotient_commShift :
    (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O)).CommShift ℤ :=
  Functor.CommShift.ofComp (ObjectProperty.liftCompιIso (kFlatObjects.{c, u, u} X.O)
    ((kFlatComplexes X).ι ⋙
      HomotopyCategory.quotient
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
        (ComplexShape.up ℤ)) (fun Y ↦ Y.2)) ℤ

/-- The isomorphism of `complexSubcategoryQuotient_commShift` is itself compatible with the
shifts. -/
instance complexSubcategoryQuotient_liftCompιIso_commShift :
    NatTrans.CommShift (ObjectProperty.liftCompιIso (kFlatObjects.{c, u, u} X.O)
      ((kFlatComplexes X).ι ⋙
        HomotopyCategory.quotient
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
          (ComplexShape.up ℤ)) (fun Y ↦ Y.2)).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

/-- The comparison of the two factorisations of `Pc.ι ⋙ Q` is compatible with the shifts. -/
instance complexSubcategoryQuotientCompIso_commShift :
    NatTrans.CommShift
      (ObjectProperty.complexSubcategoryQuotientCompIso (kFlatObjects.{c, u, u} X.O)).hom ℤ := by
  have h : (ObjectProperty.complexSubcategoryQuotientCompIso (kFlatObjects.{c, u, u} X.O)).hom =
      (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (ObjectProperty.liftCompιIso (kFlatObjects.{c, u, u} X.O)
          ((kFlatComplexes X).ι ⋙
            HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
              (ComplexShape.up ℤ)) (fun Y ↦ Y.2)).hom DerivedCategory.Qh ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (DerivedCategory.quotientCompQhIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))).hom :=
    rfl
  rw [h]
  infer_instance

/-! ### Exactness in the second variable, at the canonical structure -/

/-- For each object `N` of `D(Mod(O))`, the functor `N ⊗^L_O -` is triangulated, for the
commutation with the shift given by `derivedTensorBifunctor_commShift₂Int`. -/
instance derivedTensorBifunctor_isTriangulated_obj
    (N : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))) :
    ((derivedTensorBifunctor X).obj N).IsTriangulated :=
  Localization.isTriangulated_objCommShift (kFlatComplexQ X) DerivedCategory.Q
    (kFlatComplexQuasiIso X)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
      (ComplexShape.up ℤ))
    (kFlatTensorToDerived X) (derivedTensorBifunctor X)
    (fun Â => by
      let := Localization.Lifting₂.fst (kFlatComplexQ X) DerivedCategory.Q
        (kFlatComplexQuasiIso X)
        (HomologicalComplex.quasiIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
          (ComplexShape.up ℤ))
        (kFlatTensorToDerived X) (derivedTensorBifunctor X) Â
      let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj
      have := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi_isTriangulated
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj
      -- `bifunctorPhiFactors` with its target at `tensorComplex`: instance search compares the
      -- functors of the composites below at implicit transparency, where `tensorComplex` unfolds
      -- to the copy but not to Mathlib's `map₂HomologicalComplex`.
      let φ : HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙
            Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj ≅
          (Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Â.obj ⋙
            HomotopyCategory.quotient _ (ComplexShape.up ℤ) :=
        Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj
      have : NatTrans.CommShift φ.hom ℤ :=
        Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors_commShift_reg _ Â.obj
      let : ((derivedTensorBifunctor X).obj ((kFlatComplexQ X).obj Â)).CommShift ℤ :=
        Functor.commShiftOfLocalization DerivedCategory.Q
          (HomologicalComplex.quasiIso
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
            (ComplexShape.up ℤ)) ℤ
          ((kFlatTensorToDerived X).obj Â)
          ((derivedTensorBifunctor X).obj ((kFlatComplexQ X).obj Â))
      let : Localization.Lifting
          (HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
            (ComplexShape.up ℤ))
          (HomologicalComplex.homotopyEquivalences
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
            (ComplexShape.up ℤ))
          ((kFlatTensorToDerived X).obj Â)
          (DerivedCategory.Qh ⋙
            (derivedTensorBifunctor X).obj ((kFlatComplexQ X).obj Â)) :=
        ⟨(Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _)
            ((derivedTensorBifunctor X).obj ((kFlatComplexQ X).obj Â)) ≪≫
          Localization.Lifting.iso DerivedCategory.Q
            (HomologicalComplex.quasiIso
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
              (ComplexShape.up ℤ))
            ((kFlatTensorToDerived X).obj Â)
            ((derivedTensorBifunctor X).obj ((kFlatComplexQ X).obj Â))⟩
      let : Localization.Lifting
          (HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
            (ComplexShape.up ℤ))
          (HomologicalComplex.homotopyEquivalences
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
            (ComplexShape.up ℤ))
          ((kFlatTensorToDerived X).obj Â)
          (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj ⋙ DerivedCategory.Qh) :=
        ⟨(Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight φ DerivedCategory.Qh ≪≫
          Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft
            ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Â.obj)
            (DerivedCategory.quotientCompQhIso _)⟩
      have e1 : (Localization.Lifting.iso
            (HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
              (ComplexShape.up ℤ))
            (HomologicalComplex.homotopyEquivalences
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
              (ComplexShape.up ℤ))
            ((kFlatTensorToDerived X).obj Â)
            (DerivedCategory.Qh ⋙
              (derivedTensorBifunctor X).obj ((kFlatComplexQ X).obj Â))).hom =
          (Functor.associator _ _ _).inv ≫
            Functor.whiskerRight (DerivedCategory.quotientCompQhIso _).hom
              ((derivedTensorBifunctor X).obj ((kFlatComplexQ X).obj Â)) ≫
            (Localization.Lifting.iso DerivedCategory.Q
              (HomologicalComplex.quasiIso
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
                (ComplexShape.up ℤ))
              ((kFlatTensorToDerived X).obj Â)
              ((derivedTensorBifunctor X).obj ((kFlatComplexQ X).obj Â))).hom :=
        rfl
      have e2 : (Localization.Lifting.iso
            (HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
              (ComplexShape.up ℤ))
            (HomologicalComplex.homotopyEquivalences
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
              (ComplexShape.up ℤ))
            ((kFlatTensorToDerived X).obj Â)
            (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj ⋙
                DerivedCategory.Qh)).inv =
          ((Functor.whiskerLeft
                ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Â.obj)
                (DerivedCategory.quotientCompQhIso _).inv ≫
              (Functor.associator _ _ _).inv) ≫
            Functor.whiskerRight φ.inv DerivedCategory.Qh) ≫
            (Functor.associator _ _ _).hom :=
        rfl
      have : NatTrans.CommShift
          (Localization.liftNatIso
            (HomotopyCategory.quotient
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
              (ComplexShape.up ℤ))
            (HomologicalComplex.homotopyEquivalences
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
              (ComplexShape.up ℤ))
            ((kFlatTensorToDerived X).obj Â) ((kFlatTensorToDerived X).obj Â)
            (DerivedCategory.Qh ⋙
              (derivedTensorBifunctor X).obj ((kFlatComplexQ X).obj Â))
            (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj ⋙ DerivedCategory.Qh)
            (Iso.refl _)).hom ℤ := by
        refine Localization.natTrans_commShift_of_whiskerLeft
          (HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
            (ComplexShape.up ℤ))
          (HomologicalComplex.homotopyEquivalences
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
            (ComplexShape.up ℤ)) _ ?_
        have heq : Functor.whiskerLeft
              (HomotopyCategory.quotient
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
                (ComplexShape.up ℤ))
              (Localization.liftNatIso
                (HomotopyCategory.quotient
                  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
                  (ComplexShape.up ℤ))
                (HomologicalComplex.homotopyEquivalences
                  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
                  (ComplexShape.up ℤ))
                ((kFlatTensorToDerived X).obj Â) ((kFlatTensorToDerived X).obj Â)
                (DerivedCategory.Qh ⋙
                  (derivedTensorBifunctor X).obj ((kFlatComplexQ X).obj Â))
                (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi
                  (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj ⋙
                    DerivedCategory.Qh)
                (Iso.refl _)).hom =
            (Localization.Lifting.iso
              (HomotopyCategory.quotient
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
                (ComplexShape.up ℤ))
              (HomologicalComplex.homotopyEquivalences
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
                (ComplexShape.up ℤ))
              ((kFlatTensorToDerived X).obj Â)
              (DerivedCategory.Qh ⋙
                (derivedTensorBifunctor X).obj ((kFlatComplexQ X).obj Â))).hom ≫
            (Localization.Lifting.iso
              (HomotopyCategory.quotient
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
                (ComplexShape.up ℤ))
              (HomologicalComplex.homotopyEquivalences
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
                (ComplexShape.up ℤ))
              ((kFlatTensorToDerived X).obj Â)
              (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi
                (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj ⋙
                  DerivedCategory.Qh)).inv := by
          ext K
          simp
        rw [heq, e1, e2]
        infer_instance
      exact Functor.isTriangulated_of_precomp_iso
        (Localization.liftNatIso
          (HomotopyCategory.quotient
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
            (ComplexShape.up ℤ))
          (HomologicalComplex.homotopyEquivalences
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
            (ComplexShape.up ℤ))
          ((kFlatTensorToDerived X).obj Â) ((kFlatTensorToDerived X).obj Â)
          (DerivedCategory.Qh ⋙
            (derivedTensorBifunctor X).obj ((kFlatComplexQ X).obj Â))
          (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) Â.obj ⋙ DerivedCategory.Qh)
          (Iso.refl _)))
    N

/-! ### Exactness in the first variable, at the canonical structure -/

attribute [local instance] kFlatQ_isLocalization kFlatQuasiIso_hasLeftCalculusOfFractions
  kFlatQ_mapArrow_essSurj

/-- For each object `M` of `D(Mod(O))`, the functor `- ⊗^L_O M` is triangulated, for the
commutation with the shift given by `derivedTensorBifunctor_commShift₂Int`. -/
instance derivedTensorBifunctor_isTriangulated_flipObj
    (M : DerivedCategory
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))) :
    ((derivedTensorBifunctor X).flip.obj M).IsTriangulated :=
  Localization.isTriangulated_objCommShift DerivedCategory.Q (kFlatComplexQ X)
    (HomologicalComplex.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
      (ComplexShape.up ℤ))
    (kFlatComplexQuasiIso X)
    (kFlatTensorToDerived X).flip (derivedTensorBifunctor X).flip
    (fun B => by
      let := Localization.Lifting₂.fst DerivedCategory.Q (kFlatComplexQ X)
        (HomologicalComplex.quasiIso
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
          (ComplexShape.up ℤ))
        (kFlatComplexQuasiIso X)
        (kFlatTensorToDerived X).flip (derivedTensorBifunctor X).flip B
      let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXiR
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B
      have := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR_isTriangulated
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B
      -- `bifunctorPhiRFactors` with its target at `tensorComplex`, as in
      -- `derivedTensorBifunctor_isTriangulated_obj`.
      let φ : HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙
            Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ≅
          (Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj B ⋙
            HomotopyCategory.quotient _ (ComplexShape.up ℤ) :=
        Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiRFactors
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B
      have : NatTrans.CommShift φ.hom ℤ :=
        Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiRFactors_commShift_reg _ B
      let : ((derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B)).CommShift ℤ :=
        Functor.commShiftOfLocalization (kFlatComplexQ X) (kFlatComplexQuasiIso X) ℤ
          ((kFlatTensorToDerived X).flip.obj B)
          ((derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B))
      let : Localization.Lifting
          (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O))
          ((HomologicalComplex.homotopyEquivalences
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
            (ComplexShape.up ℤ)).inverseImage (kFlatComplexes X).ι)
          ((kFlatTensorToDerived X).flip.obj B)
          (kFlatQ.{c, u, d} X ⋙
            (derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B)) :=
        ⟨(Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (ObjectProperty.complexSubcategoryQuotientCompIso (kFlatObjects.{c, u, u} X.O))
            ((derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B)) ≪≫
          Localization.Lifting.iso (kFlatComplexQ X) (kFlatComplexQuasiIso X)
            ((kFlatTensorToDerived X).flip.obj B)
            ((derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B))⟩
      let : Localization.Lifting
          (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O))
          ((HomologicalComplex.homotopyEquivalences
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
            (ComplexShape.up ℤ)).inverseImage (kFlatComplexes X).ι)
          ((kFlatTensorToDerived X).flip.obj B)
          ((kFlatObjects.{c, u, u} X.O).ι ⋙
            Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙ DerivedCategory.Qh) :=
        ⟨(Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight
            (ObjectProperty.liftCompιIso (kFlatObjects.{c, u, u} X.O)
              ((kFlatComplexes X).ι ⋙
                HomotopyCategory.quotient
                  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
                  (ComplexShape.up ℤ)) (fun Y ↦ Y.2))
            (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙ DerivedCategory.Qh) ≪≫
          Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft (kFlatComplexes X).ι
            ((Functor.associator _ _ _).symm ≪≫
              Functor.isoWhiskerRight φ DerivedCategory.Qh ≪≫
              Functor.associator _ _ _ ≪≫
              Functor.isoWhiskerLeft
                ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj B)
                (DerivedCategory.quotientCompQhIso _))⟩
      have e1 : (Localization.Lifting.iso
            (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O))
            ((HomologicalComplex.homotopyEquivalences
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
              (ComplexShape.up ℤ)).inverseImage (kFlatComplexes X).ι)
            ((kFlatTensorToDerived X).flip.obj B)
            (kFlatQ.{c, u, d} X ⋙
              (derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B))).hom =
          (Functor.associator _ _ _).inv ≫
            Functor.whiskerRight
              (ObjectProperty.complexSubcategoryQuotientCompIso
                (kFlatObjects.{c, u, u} X.O)).hom
              ((derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B)) ≫
            (Localization.Lifting.iso (kFlatComplexQ X) (kFlatComplexQuasiIso X)
              ((kFlatTensorToDerived X).flip.obj B)
              ((derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B))).hom :=
        rfl
      have e2 : (Localization.Lifting.iso
            (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O))
            ((HomologicalComplex.homotopyEquivalences
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
              (ComplexShape.up ℤ)).inverseImage (kFlatComplexes X).ι)
            ((kFlatTensorToDerived X).flip.obj B)
            ((kFlatObjects.{c, u, u} X.O).ι ⋙
              Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
                (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙
                  DerivedCategory.Qh)).inv =
          ((Functor.whiskerLeft (kFlatComplexes X).ι
                (((Functor.whiskerLeft
                      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).flip.obj B)
                      (DerivedCategory.quotientCompQhIso _).inv ≫
                    (Functor.associator _ _ _).inv) ≫
                  Functor.whiskerRight φ.inv DerivedCategory.Qh) ≫
                  (Functor.associator _ _ _).hom) ≫
              (Functor.associator _ _ _).inv) ≫
            Functor.whiskerRight
              (ObjectProperty.liftCompιIso (kFlatObjects.{c, u, u} X.O)
                ((kFlatComplexes X).ι ⋙
                  HomotopyCategory.quotient
                    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
                    (ComplexShape.up ℤ)) (fun Y ↦ Y.2)).inv
              (Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
                (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙
                  DerivedCategory.Qh)) ≫
            (Functor.associator _ _ _).hom :=
        rfl
      have : NatTrans.CommShift
          (Localization.liftNatIso
            (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O))
            ((HomologicalComplex.homotopyEquivalences
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
              (ComplexShape.up ℤ)).inverseImage (kFlatComplexes X).ι)
            ((kFlatTensorToDerived X).flip.obj B)
            ((kFlatTensorToDerived X).flip.obj B)
            (kFlatQ.{c, u, d} X ⋙
              (derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B))
            ((kFlatObjects.{c, u, u} X.O).ι ⋙
              Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
                (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙ DerivedCategory.Qh)
            (Iso.refl _)).hom ℤ := by
        refine Localization.natTrans_commShift_of_whiskerLeft
          (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O))
          ((HomologicalComplex.homotopyEquivalences
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
            (ComplexShape.up ℤ)).inverseImage (kFlatComplexes X).ι) _ ?_
        have heq : Functor.whiskerLeft
              (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O))
              (Localization.liftNatIso
                (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O))
                ((HomologicalComplex.homotopyEquivalences
                  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
                  (ComplexShape.up ℤ)).inverseImage (kFlatComplexes X).ι)
                ((kFlatTensorToDerived X).flip.obj B)
                ((kFlatTensorToDerived X).flip.obj B)
                (kFlatQ.{c, u, d} X ⋙
                  (derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B))
                ((kFlatObjects.{c, u, u} X.O).ι ⋙
                  Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
                    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙
                      DerivedCategory.Qh)
                (Iso.refl _)).hom =
            (Localization.Lifting.iso
              (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O))
              ((HomologicalComplex.homotopyEquivalences
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
                (ComplexShape.up ℤ)).inverseImage (kFlatComplexes X).ι)
              ((kFlatTensorToDerived X).flip.obj B)
              (kFlatQ.{c, u, d} X ⋙
                (derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B))).hom ≫
            (Localization.Lifting.iso
              (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O))
              ((HomologicalComplex.homotopyEquivalences
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
                (ComplexShape.up ℤ)).inverseImage (kFlatComplexes X).ι)
              ((kFlatTensorToDerived X).flip.obj B)
              ((kFlatObjects.{c, u, u} X.O).ι ⋙
                Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
                  (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙
                    DerivedCategory.Qh)).inv := by
          ext K
          simp
        rw [heq, e1, e2]
        infer_instance
      exact Functor.isTriangulated_of_precomp_iso
        (Localization.liftNatIso
          (ObjectProperty.complexSubcategoryQuotient (kFlatObjects.{c, u, u} X.O))
          ((HomologicalComplex.homotopyEquivalences
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{c, u, u} X.O))
            (ComplexShape.up ℤ)).inverseImage (kFlatComplexes X).ι)
          ((kFlatTensorToDerived X).flip.obj B)
          ((kFlatTensorToDerived X).flip.obj B)
          (kFlatQ.{c, u, d} X ⋙
            (derivedTensorBifunctor X).flip.obj (DerivedCategory.Q.obj B))
          ((kFlatObjects.{c, u, u} X.O).ι ⋙
            Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiR
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) B ⋙ DerivedCategory.Qh)
          (Iso.refl _)))
    M

end Stacks.SheafOfModules

end
