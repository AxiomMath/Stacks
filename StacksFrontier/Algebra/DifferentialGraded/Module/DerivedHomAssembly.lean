module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomLiftComparison

/-!
# The identification `(*)` of Tag 09LK from naturality and a single value

`CochainComplex.DerivedHomLiftIdentification` — the hypothesis `(*)` of step 3 of
[Stacks, Tag 09LK] — asks for an injection `φ` out of `H^n(U(R̃(Q X)))` together with the
left-fraction formula on *every* leg of the comparison cocone of Tag 05S9, one leg for each
quasi-isomorphism `s : X ⟶ Y` out of `X`.

This file reduces that family of conditions to two, neither of which mentions a leg other than
the one at the identity:

* `naturality`: `φ` is compatible with the transition morphisms of the cocone, i.e. with
  `U(R̃(Q s))⁻¹` on the left and with `Q(s)⟦n⟧⁻¹` on the right;
* `unit_app_id`: on the image of `β` at `Y` itself, `φ` is `Q` of the morphism of the homotopy
  category that the cohomology class is, by Tag 09LC.

## Main definitions

* `CochainComplex.derivedHomLiftIdentificationOfNaturality`: `(*)` from injectivity, naturality,
  and the left-fraction formula at the identity leg alone.
* `CochainComplex.derivedHomLiftIdentificationOfCovariantNaturality`: the same, with the
  naturality clause in its covariant form, for every morphism of `K(A)`.

## Implementation notes

The hypothesis `unit_app_id` asks for nothing beyond `(*)`: the object `(𝟙 X : X ⟶ X)` of `X/W` is
one of the legs, the comparison isomorphism `CategoryTheory.MorphismProperty.underIso` at it is
the identity, so the coprojection there is `β` at `X` and the unit compatibility of `(*)` reads at
that leg exactly as `unit_app_id`. So the two hypotheses together are a reformulation of the unit
compatibility and not a strengthening of it.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), whose step 3 the
  hypothesis `(*)` belongs to; [Tag 05S9](https://stacks.math.columbia.edu/tag/05S9), the
  comparison cocone whose legs are being reduced to one;
  [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC), the identification of a cohomology class
  of a Hom complex with a morphism of the homotopy category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

universe v w u u' v'

namespace CochainComplex

variable (A : Type u) [Category.{0} A] [Abelian A] [HasDerivedCategory.{v} A]
  (K : CochainComplex A ℤ) [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]
  {E : Type u'} [Category.{v'} E] (U : E ⥤ DerivedCategory (ModuleCat.{0} ℤ))
  (Rt : DerivedCategory A ⥤ E)
  (β : homToDerivedCategoryForget A K ⟶ DerivedCategory.Qh ⋙ Rt ⋙ U)

/-- **The identification `(*)` from naturality and a single value.** Let `φ` be an injective
family of maps `H^n(U(R̃(Q X))) → Hom_{D(A)}(Q K, (Q X)⟦n⟧)`, as in
`CochainComplex.DerivedHomLiftIdentification`. Suppose that

* `naturality`: for every quasi-isomorphism `s : X ⟶ Y`, `φ` at `X` composed with the transition
  map `H^n(U(R̃(Q s))⁻¹)` of the comparison cocone is `φ` at `Y` followed by composition with
  `Q(s)⟦n⟧⁻¹`; and
* `unit_app_id`: for every `Y`, `φ` carries the `β`-image of a degree-`n` cohomology class of
  `Hom^•(K, Y)` to `Q` of the morphism `K ⟶ Y⟦n⟧` of the homotopy category that the class is, by
  Tag 09LC.

Then `(*)` holds. -/
def derivedHomLiftIdentificationOfNaturality
    (φ : ∀ (X : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ),
      ↥((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
          ((Rt ⋙ U).obj (DerivedCategory.Qh.obj X))) →
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⟶
          (DerivedCategory.Qh.obj X)⟦n⟧))
    (injective : ∀ X n, Function.Injective (φ X n))
    (naturality : ∀ (X : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ)
      (S : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ X)
      (y : ↥((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
        ((Rt ⋙ U).obj (DerivedCategory.Qh.obj S.right)))),
      φ X n ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((Rt ⋙ U).map ((HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).underIso
            DerivedCategory.Qh X S).inv) y) =
        φ S.right n y ≫ CategoryTheory.inv ((DerivedCategory.Qh.map S.hom)⟦n⟧'))
    (unit_app_id : ∀ (Y : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ)
      (x : ↥((homToDerivedCategoryForget A K ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj Y)),
      φ Y n ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map (β.app Y) x) =
        DerivedCategory.Qh.map (homologyHomAddEquiv A K n Y x) ≫
          (DerivedCategory.Qh.commShiftIso n).hom.app Y) :
    DerivedHomLiftIdentification A K U Rt β where
  φ := φ
  injective := injective
  unit_app X n S x := by
    have hleg : (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((Functor.derivedUnitCocone (homToDerivedCategoryForget A K)
            (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Qh (Rt ⋙ U) β
            X).ι.app S) =
        (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map (β.app S.right) ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
            ((Rt ⋙ U).map ((HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).underIso
              DerivedCategory.Qh X S).inv) :=
      (congrArg (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
        (Functor.derivedUnitCocone_ι_app (homToDerivedCategoryForget A K)
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Qh (Rt ⋙ U) β
          X S)).trans ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map_comp _ _)
    have hx := (ConcreteCategory.congr_hom hleg x).trans (ModuleCat.comp_apply _ _ x)
    rw [hx]
    exact (naturality X n S _).trans
      ((congrArg (· ≫ CategoryTheory.inv ((DerivedCategory.Qh.map S.hom)⟦n⟧'))
        (unit_app_id S.right n x)).trans (assoc _ _ _))

/-- **The identification `(*)` from covariant naturality and a single value.** The variant of
`CochainComplex.derivedHomLiftIdentificationOfNaturality` whose naturality clause is the
*covariant* square

`φ Y n (H^n(U(R̃(Q s))) z) = φ X n z ≫ Q(s)⟦n⟧`

for **every** morphism `s : X ⟶ Y` of `K(A)`, in place of the contravariant compatibility with
`U(R̃(Q s))⁻¹` on the left and with `Q(s)⟦n⟧⁻¹` on the right for a quasi-isomorphism `s`. The
hypothesis `unit_app_id` is unchanged. -/
def derivedHomLiftIdentificationOfCovariantNaturality
    (φ : ∀ (X : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ),
      ↥((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
          ((Rt ⋙ U).obj (DerivedCategory.Qh.obj X))) →
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⟶
          (DerivedCategory.Qh.obj X)⟦n⟧))
    (injective : ∀ X n, Function.Injective (φ X n))
    (covariant : ∀ (X Y : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ) (s : X ⟶ Y)
      (z : ↥((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
        ((Rt ⋙ U).obj (DerivedCategory.Qh.obj X)))),
      φ Y n ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((Rt ⋙ U).map (DerivedCategory.Qh.map s)) z) =
        φ X n z ≫ (DerivedCategory.Qh.map s)⟦n⟧')
    (unit_app_id : ∀ (Y : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ)
      (x : ↥((homToDerivedCategoryForget A K ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj Y)),
      φ Y n ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map (β.app Y) x) =
        DerivedCategory.Qh.map (homologyHomAddEquiv A K n Y x) ≫
          (DerivedCategory.Qh.commShiftIso n).hom.app Y) :
    DerivedHomLiftIdentification A K U Rt β :=
  derivedHomLiftIdentificationOfNaturality A K U Rt β φ injective
    (fun X n S y => by
      have hiso : IsIso (DerivedCategory.Qh.map S.hom) := by
        rw [← MorphismProperty.underIso_hom (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
          DerivedCategory.Qh X S]
        infer_instance
      have hy : (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
            ((Rt ⋙ U).map (DerivedCategory.Qh.map S.hom))
            ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
              ((Rt ⋙ U).map ((HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).underIso
                DerivedCategory.Qh X S).inv) y) = y := by
        rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp,
          ← MorphismProperty.underIso_hom (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
            DerivedCategory.Qh X S, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
          CategoryTheory.Functor.map_id]
        rfl
      have hcov := covariant X S.right n S.hom
        ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((Rt ⋙ U).map ((HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).underIso
            DerivedCategory.Qh X S).inv) y)
      rw [hy] at hcov
      rw [hcov, assoc, IsIso.hom_inv_id, comp_id])
    unit_app_id

end CochainComplex

end
