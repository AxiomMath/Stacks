module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomAssembly
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedHomPhiTransport

/-!
# Step 3 of Tag 09LK at the reflector: the lift recovers the ordinary derived Hom

Steps 1 and 2 of the replacement proof of [Stacks, Tag 09LK] produce the lifted functor

`R̃ = DGCategory.phiReflector A K L hΦ : D(A) ⥤ D(C(K, K))`

together with the identification `DGCategory.derivedHomPhiQh` of the cohomology of its values
with the morphism groups of `D(A)`. Step 3 is the statement that forgetting `R̃` along
`DGCategory.endDerivedForget` gives back the ordinary abelian-group-valued derived Hom:

`R Hom(K, -) ≅ R̃ ⋙ U`,

for `R Hom(K, -) = CochainComplex.derivedHomForgetFunctor A K h` the functor Tag 09LK's own
hypothesis `h` produces, and `R̃ ⋙ U = DGCategory.phiReflectorForget A K L hΦ`.

This file assembles that conclusion from the pieces already in place. The general machinery is
`CochainComplex.derivedHomForgetComparisonIso`
(`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomLiftComparison.lean`), which turns an
identification `CochainComplex.DerivedHomLiftIdentification` into exactly this isomorphism, and
`CochainComplex.derivedHomLiftIdentificationOfCovariantNaturality`
(`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomAssembly.lean`), which builds such an
identification from four clauses. Three of the four are theorems of
`StacksFrontier/CategoryTheory/DifferentialGraded/RightModule/DerivedHomPhiTransport.lean`:
`DGCategory.derivedHomPhiQh`, `DGCategory.derivedHomPhiQh_injective` and
`DGCategory.derivedHomPhiQh_covariant`. Nothing here is new mathematics; what the file does is
fit those three into the consumer's shape and carry the conclusion out.

## What is assumed, and what is still owed

Beyond Tag 09LK's own hypothesis `h` — that the abelian-group-valued
`Hom(K, -) : K(A) ⥤ D(Ab)` is right derivable — the statements below assume only what steps 1 and
2 already carry: the exactness of the differential graded Yoneda functor, as the two instance
binders on `((yonedaDGFunctor (CochainComplex.dgCategory A)).onK)`, and the reflector data
`L`, `η`, `hL`, `hη`, `hΦ` that step 1 produces. In particular neither
`(CochainComplex.homToDerivedCategoryForget A K)`'s derivability in `D(E)` nor any smallness,
universe inequality, K-injective resolution or right derivability of
`(CochainComplex.homToDerivedCategory A K)` is assumed. The reflector data is taken as binders
rather than obtained from `DGCategory.exists_derivedHomPhiQh`, so that the results hold at
*every* such reflector and in particular at the one a sibling step fixes.

The fourth clause, `unit_app_id`, is **not** proved anywhere: it is the single elementwise
computation that `φ`, applied to the `β`-image of a degree-`n` cohomology class of `Hom^•(K, Y)`,
is `Q` of the morphism `K ⟶ Y⟦n⟧` that [Stacks, Tag 09LC] assigns to that class, and it is where
the mathematics of the replacement proof still has to be done. It is therefore carried as a named
hypothesis of both declarations below, spelled out in full, so that the conclusion follows the
moment it is supplied.

The comparison `β : Hom(K, -) ⟶ Q ⋙ (R̃ ⋙ U)` is also a binder. It has to be: the
`Qh`-indexed shape step 3 consumes is not the shape
`DGCategory.derivedHomReflectorUnit` comes in — that transformation is indexed by the
differential graded homotopy category and runs along
`DGCategory.phiComparisonLocalization`, not along `DerivedCategory.Qh`. Leaving `β` free is also
strictly more general: any `β` whatsoever, in particular the one
`DGCategory.RightModule.derivedHomForgetUnitAtReflector` builds, may be substituted.

*No converse shortcut.* The other way into
`CochainComplex.derivedHomForgetComparisonIso` is
`CochainComplex.derivedHomLiftIdentificationOfIsRightDerivedFunctor`, which asks for
`(R̃ ⋙ U).IsRightDerivedFunctor β`. That is the conclusion of step 3 itself — the two are proved
equivalent in `DerivedHomLiftComparison.lean` — so it is not available from what is proved, and
the route through `unit_app_id` is the only one.

## Main definitions

* `DGCategory.phiDerivedHomLiftIdentification`: the identification `(*)` at the reflector, from
  the transported `φ` and the one owed elementwise computation.
* `DGCategory.derivedHomForgetPhiReflectorIso`: **step 3 of [Stacks, Tag 09LK]** at the
  reflector — `R Hom(K, -) ≅ R̃ ⋙ U`.

## Main results

* `DGCategory.isIso_derivedHomForgetComparison_phiReflector`: the same conclusion as the
  invertibility of the canonical comparison `θ`, which is the form that identifies the
  isomorphism rather than merely asserting one exists.
* `DGCategory.isRightDerivedFunctor_phiReflectorForget`: equivalently, `R̃ ⋙ U` with `β` is
  itself a right derived functor of `Hom(K, -) : K(A) ⥤ D(Ab)`.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), whose third step this
  is; [Tag 09LC](https://stacks.math.columbia.edu/tag/09LC), the identification of a cohomology
  class of a Hom complex with a morphism of the homotopy category, which `unit_app_id` is about.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.ObjectProperty

namespace DGCategory

universe w v

variable (A : Type) [Category.{0} A] [Abelian A] [HasDerivedCategory.{v} A]
  (K : CochainComplex A ℤ) [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]
  [((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).CommShift ℤ]
  [((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).IsTriangulated]
  (L : (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K ⥤
    (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K)
  [L.CommShift ℤ] [L.IsTriangulated]
  {η : 𝟭 (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K ⟶ L}

attribute [local implicit_reducible] DGCategory.K

variable
  (hL : ∀ X, (RightModule.yonedaLocalizing (CochainComplex.dgCategory A) (phiGen A)).rightOrthogonal
    (L.obj X))
  (hη : ∀ (X Z : (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K) (f : Z ⟶ X)
      (g : L.obj X ⟶ Z⟦(1 : ℤ)⟧),
    Triangle.mk f (η.app X) g ∈
        distTriang (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K →
      RightModule.yonedaLocalizing (CochainComplex.dgCategory A) (phiGen A) Z)
  (hΦ : ∀ X, RightModule.yonedaInverseImage (CochainComplex.dgCategory A) (phiGen A) X →
    IsZero (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK ⋙ L).obj X))
  (β : CochainComplex.homToDerivedCategoryForget A K ⟶
    DerivedCategory.Qh ⋙ phiReflector A K L hΦ ⋙
      endDerivedForget (CochainComplex.dgCategory A) K)

/-- **The identification `(*)` of step 3 of [Stacks, Tag 09LK] at the reflector of steps 1 and
2.** The `φ` clause is the transported identification `DGCategory.derivedHomPhiQh`, its
injectivity clause is `DGCategory.derivedHomPhiQh_injective`, and its naturality clause is the
covariant square `DGCategory.derivedHomPhiQh_covariant`, which holds for every morphism of
`K(A)` and so in particular for the quasi-isomorphisms the consumer needs; the passage from the
covariant square to the contravariant transition condition is performed by
`CochainComplex.derivedHomLiftIdentificationOfCovariantNaturality`.

The clause `unit_app_id` is the hypothesis: for every `Y` and every `n`, the transported `φ`
carries the `β`-image of a degree-`n` cohomology class `x` of `Hom^•(K, Y)` to `Q` of the
morphism `K ⟶ Y⟦n⟧` of the homotopy category that `x` is, by [Stacks, Tag 09LC]. It is the one
elementwise computation the replacement proof still owes, and nothing else here depends on
anything unproved. -/
def phiDerivedHomLiftIdentification
    (unit_app_id : ∀ (Y : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ)
      (x : ↥((CochainComplex.homToDerivedCategoryForget A K ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj Y)),
      derivedHomPhiQh A K L hL hη hΦ Y n
          ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map (β.app Y) x) =
        DerivedCategory.Qh.map (CochainComplex.homologyHomAddEquiv A K n Y x) ≫
          (DerivedCategory.Qh.commShiftIso n).hom.app Y) :
    CochainComplex.DerivedHomLiftIdentification A K
      (endDerivedForget (CochainComplex.dgCategory A) K) (phiReflector A K L hΦ) β :=
  CochainComplex.derivedHomLiftIdentificationOfCovariantNaturality A K
    (endDerivedForget (CochainComplex.dgCategory A) K) (phiReflector A K L hΦ) β
    (fun X n z ↦ derivedHomPhiQh A K L hL hη hΦ X n z)
    (fun X n ↦ derivedHomPhiQh_injective A K L hL hη hΦ X n)
    (fun _ _ n s z ↦ derivedHomPhiQh_covariant A K L hL hη hΦ s n z)
    unit_app_id

variable (h : (CochainComplex.homToDerivedCategoryForget A K).IsRightDerivable
  (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))

/-- **Step 3 of [Stacks, Tag 09LK], as invertibility of the canonical comparison.** Under Tag
09LK's own hypothesis `h` and the owed elementwise computation `unit_app_id`, the comparison

`θ : R Hom(K, -) ⟶ R̃ ⋙ U`

that the universal property of the abelian-group-valued derived Hom produces out of `β` is an
isomorphism. This is the sharp form: the isomorphism below is this particular `θ`, not merely
some isomorphism of the two functors. -/
theorem isIso_derivedHomForgetComparison_phiReflector
    (unit_app_id : ∀ (Y : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ)
      (x : ↥((CochainComplex.homToDerivedCategoryForget A K ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj Y)),
      derivedHomPhiQh A K L hL hη hΦ Y n
          ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map (β.app Y) x) =
        DerivedCategory.Qh.map (CochainComplex.homologyHomAddEquiv A K n Y x) ≫
          (DerivedCategory.Qh.commShiftIso n).hom.app Y) :
    IsIso (CochainComplex.derivedHomForgetComparison A K
      (endDerivedForget (CochainComplex.dgCategory A) K) (phiReflector A K L hΦ) h β) :=
  CochainComplex.isIso_derivedHomForgetComparison A K
    (endDerivedForget (CochainComplex.dgCategory A) K) (phiReflector A K L hΦ) h β
    (phiDerivedHomLiftIdentification A K L hL hη hΦ β unit_app_id)

/-- **Step 3 of [Stacks, Tag 09LK]: the lifted functor recovers the ordinary derived Hom.** Under
Tag 09LK's own hypothesis `h` and the owed elementwise computation `unit_app_id`,

`R Hom(K, -) ≅ R̃ ⋙ U`,

i.e. forgetting the lift `DGCategory.phiReflector` of steps 1 and 2 along the forgetful functor
`DGCategory.endDerivedForget` gives the abelian-group-valued derived Hom of Tag 09LK's own
hypothesis. The isomorphism is the canonical comparison `θ` of
`CochainComplex.derivedHomForgetComparison`. -/
def derivedHomForgetPhiReflectorIso
    (unit_app_id : ∀ (Y : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ)
      (x : ↥((CochainComplex.homToDerivedCategoryForget A K ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj Y)),
      derivedHomPhiQh A K L hL hη hΦ Y n
          ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map (β.app Y) x) =
        DerivedCategory.Qh.map (CochainComplex.homologyHomAddEquiv A K n Y x) ≫
          (DerivedCategory.Qh.commShiftIso n).hom.app Y) :
    CochainComplex.derivedHomForgetFunctor A K h ≅ phiReflectorForget A K L hΦ :=
  CochainComplex.derivedHomForgetComparisonIso A K
    (endDerivedForget (CochainComplex.dgCategory A) K) (phiReflector A K L hΦ) h β
    (phiDerivedHomLiftIdentification A K L hL hη hΦ β unit_app_id)

include h in
/-- **The same conclusion as a universal property.** Equivalently to step 3: `R̃ ⋙ U` together
with `β` is itself a right derived functor of `Hom(K, -) : K(A) ⥤ D(Ab)`, i.e. a left Kan
extension along the localization `K(A) ⥤ D(A)`.

This is the strongest conclusion available, and deliberately not the statement that `R̃` is a
right derived functor of a `D(E)`-valued `Hom(K, -)`: getting that from this would mean
reflecting essential constancy through `U`, which is refuted in
`StacksFrontier/CategoryTheory/Functor/Derived/ValueReflection.lean`. -/
theorem isRightDerivedFunctor_phiReflectorForget
    (unit_app_id : ∀ (Y : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ)
      (x : ↥((CochainComplex.homToDerivedCategoryForget A K ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj Y)),
      derivedHomPhiQh A K L hL hη hΦ Y n
          ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map (β.app Y) x) =
        DerivedCategory.Qh.map (CochainComplex.homologyHomAddEquiv A K n Y x) ≫
          (DerivedCategory.Qh.commShiftIso n).hom.app Y) :
    (phiReflectorForget A K L hΦ).IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  CochainComplex.isRightDerivedFunctor_comp_of_derivedHomLiftIdentification A K
    (endDerivedForget (CochainComplex.dgCategory A) K) (phiReflector A K L hΦ) h β
    (phiDerivedHomLiftIdentification A K L hL hη hΦ β unit_app_id)

end DGCategory

end
