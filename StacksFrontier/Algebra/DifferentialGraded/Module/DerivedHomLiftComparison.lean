module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomValueHomIso
public import StacksFrontier.CategoryTheory.Functor.Derived.RightDerivedDescCocone

/-!
# Comparing derived Hom with an assumed lift of it

Let `A` be an abelian category whose morphisms are sets, let `K` be a cochain complex in `A`,
and assume Tag 09LK's own hypothesis: the right derived functor of the abelian-group-valued
`Hom(K, -) : K(A) ⥤ D(Ab)` is everywhere defined. Write `R = R Hom(K, -) : D(A) ⥤ D(Ab)` for the
functor that hypothesis produces, as assembled in
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomValueCohomology.lean`.

Suppose given, by whatever means, a category `E` with a functor `U : E ⥤ D(Ab)`, a functor
`R̃ : D(A) ⥤ E`, and a comparison `β : Hom(K, -) ⟶ Q ⋙ (R̃ ⋙ U)` — the `U`-image of a unit
`Hom(K, -) ⟶ Q ⋙ R̃` for a lift of derived Hom through `U`. Nothing is assumed of `R̃`; in
particular it is *not* assumed that the `E`-valued `Hom(K, -)` has a right derived functor, which
is the hypothesis this whole development exists to avoid
(`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomVariant.lean` constructs
`R Hom(K, -) : D(A) ⥤ D(E, d)` from exactly that stronger hypothesis).

The universal property of `R` then produces the comparison

`θ : R ⟶ R̃ ⋙ U`,

and this file proves it invertible from one hypothesis, which is the identification the
construction of `R̃` is supposed to supply:

`(*)` for every `X` in `K(A)` and every `n`, an injection
  `φ : H^n(U(R̃(Q X))) → Hom_{D(A)}(Q K, (Q X)⟦n⟧)` carrying the class of a morphism
  `f : K ⟶ Y⟦n⟧` along the comparison cocone at a quasi-isomorphism `s : X ⟶ Y` to the left
  fraction `Q(s)⟦n⟧⁻¹ ∘ Q(f)`.

On the other side the same formula already holds, and is the content of
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomValueHomIso.lean`: by preservation of
essential constancy (Tags 05PT, 05SH), `H^n(R(Q X))` is the colimit over `X/W` of the
`H^n Hom^•(K, Y)`, and the calculus of left fractions identifies that colimit with
`Hom_{D(A)}(Q K, (Q X)⟦n⟧)` by a bijection with exactly that description. The two agree leg by
leg, the legs are jointly surjective, so `H^n(θ)` is the composite of two bijections and is one.
Being invertible on every `H^n` makes `θ` invertible in `D(Ab)` object by object, and every
object of `D(A)` is a `Q X`.

## Main definitions

* `CochainComplex.derivedHomForgetUnitOfLift`: the comparison `β` obtained by forgetting a unit
  `V ⟶ Q ⋙ R̃` along `U`, for `V : K(A) ⥤ E` a lift of `Hom(K, -)` through `U`.
* `CochainComplex.derivedHomForgetComparison`: **the comparison `θ : R ⟶ R̃ ⋙ U`**, from the
  universal property of `R` alone.
* `CochainComplex.DerivedHomLiftIdentification`: the hypothesis `(*)`.
* `CochainComplex.derivedHomForgetComparisonIso`: `θ` as a natural isomorphism, once `(*)` holds.

## Main results

* `CochainComplex.derivedUnitCocone_ι_app_comp_derivedHomForgetComparison_app` and
  `CochainComplex.homologyFunctor_map_derivedHomForgetComparison_app_apply`: `θ` is a morphism of
  the comparison cocones of Tag 05S9, and what that says on cohomology classes.
* `CochainComplex.derivedHomLiftIdentification_homologyFunctor_map_comparison`: the identification
  `(*)` carries `H^n(θ)` to the identification of
  `CochainComplex.derivedHomValueHomEquiv`. This is the heart: both are the left fraction.
* `CochainComplex.isIso_homologyFunctor_map_derivedHomForgetComparison_app`: hence `H^n(θ)` is
  invertible, for every `X` and every `n`.
* `CochainComplex.isIso_derivedHomForgetComparison`: **step 3 of Tag 09LK.** `θ` is a natural
  isomorphism.
* `CochainComplex.isRightDerivedFunctor_comp_of_derivedHomLiftIdentification`: equivalently,
  `R̃ ⋙ U` with `β` is itself a right derived functor of `Hom(K, -) : K(A) ⥤ D(Ab)`.
* `CochainComplex.derivedHomLiftIdentificationOfIsRightDerivedFunctor`: the converse of that, so
  `(*)` and the conclusion are equivalent.
* `CochainComplex.isIso_derivedHomForgetComparison_of_isRightDerivedFunctor` and
  `CochainComplex.derivedHomForgetComparisonIsoOfIsRightDerivedFunctor`: step 3's conclusion
  taken straight off the left Kan extension property of `R̃ ⋙ U`, for a construction that already
  has it and so has no need of `(*)`.

## Implementation notes

*What `(*)` is and is not.* It is an identification of the cohomology of the values of the lift,
pinned down on the comparison cocone. It is *equivalent* to the conclusion that `R̃ ⋙ U` is a
right derived functor — both directions are proved here — and the file does not pretend
otherwise. Its reason for existing is that the two are not equally easy to *supply*: a
construction of `R̃`, by a reflector onto the right orthogonal of a localizing subcategory say,
computes `H^n(U(R̃(Q X)))` directly, and does not come with a left Kan extension property or a
colimit description of its values. Step 3 is the passage from the computation to the property.

*Only injectivity of `φ` is used.* `(*)` is stated with a family of injections rather than of
bijections, because surjectivity is not needed: the left-hand side is already identified with
`Hom_{D(A)}(Q K, (Q X)⟦n⟧)` bijectively, so an injection on the right-hand side forces the
comparison between them to be a bijection, and the right-hand identification to be one as well. A
construction supplying an isomorphism supplies this.

*No conservativity is needed.* `θ` is a transformation of functors valued in `D(Ab)`, so
detecting its invertibility needs only that a morphism of `D(Ab)` is invertible when every
`H^n` of it is, which is `DerivedCategory.isIso_iff`. The forgetful functor `U` is never asked to
reflect anything. In particular nothing here reflects essential constancy through `U`, which is
false in general — see
`StacksFrontier/CategoryTheory/Functor/Derived/ValueReflection.lean` — and nothing here concludes
that `R̃` itself is a right derived functor of the `E`-valued `Hom(K, -)`, which would need
exactly that reflection.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK), whose hypothesis is
  assumed throughout and whose third step this is;
  [Tag 05PT](https://stacks.math.columbia.edu/tag/05PT)
  and [Tag 05SH](https://stacks.math.columbia.edu/tag/05SH), preservation of essential constancy;
  [Tag 05Q0](https://stacks.math.columbia.edu/tag/05Q0), the calculus of fractions behind the
  left-hand identification.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

universe v w u u' v'

namespace CochainComplex

variable (A : Type u) [Category.{0} A] [Abelian A] [HasDerivedCategory.{v} A]
  (K : CochainComplex A ℤ) [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]
  {E : Type u'} [Category.{v'} E] (U : E ⥤ DerivedCategory (ModuleCat.{0} ℤ))
  (Rt : DerivedCategory A ⥤ E)

/-- **Forgetting a unit along `U`.** Let `V : K(A) ⥤ E` be a lift of the abelian-group-valued
`Hom(K, -)` through `U`, exhibited by an isomorphism `ι : V ⋙ U ≅ Hom(K, -)`, and let
`η : V ⟶ Q ⋙ R̃` be a unit for `R̃`. Applying `U` to `η` and composing with `ι` gives the
comparison `Hom(K, -) ⟶ Q ⋙ (R̃ ⋙ U)` that the universal property of derived Hom consumes. -/
def derivedHomForgetUnitOfLift (V : HomotopyCategory A (ComplexShape.up ℤ) ⥤ E)
    (ι : V ⋙ U ≅ homToDerivedCategoryForget A K) (η : V ⟶ DerivedCategory.Qh ⋙ Rt) :
    homToDerivedCategoryForget A K ⟶ DerivedCategory.Qh ⋙ Rt ⋙ U :=
  ι.inv ≫ Functor.whiskerRight η U ≫ (Functor.associator _ _ _).hom

variable (h : (homToDerivedCategoryForget A K).IsRightDerivable
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
  (β : homToDerivedCategoryForget A K ⟶ DerivedCategory.Qh ⋙ Rt ⋙ U)

/-- **The comparison `θ : R ⟶ R̃ ⋙ U`.** Tag 09LK's own hypothesis makes
`R = R Hom(K, -) : D(A) ⥤ D(Ab)` a right derived functor of `Hom(K, -) : K(A) ⥤ D(Ab)`, i.e. a
left Kan extension along `K(A) ⥤ D(A)`. Its universal property turns any comparison
`β : Hom(K, -) ⟶ Q ⋙ (R̃ ⋙ U)` into a natural transformation out of `R`, uniquely so that
composing with the unit of `R` returns `β`.

Nothing is assumed of `R̃` or of `U`. In particular the `E`-valued `Hom(K, -)` is not assumed to
be derivable: the comparison runs from `R`, not towards it. -/
def derivedHomForgetComparison : derivedHomForgetFunctor A K h ⟶ Rt ⋙ U :=
  have := derivedHomForgetFunctor_isRightDerivedFunctor A K h
  (derivedHomForgetFunctor A K h).rightDerivedDesc (derivedHomForgetFunctorUnit A K h)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (Rt ⋙ U) β

/-- **The comparison is a morphism of comparison cocones.** At `Q X`, the comparison `θ` carries
the coprojection at a quasi-isomorphism `s : X ⟶ Y` of the cocone of Tag 05S9 attached to `R` to
the coprojection at `s` of the cocone attached to `β`.

This is `CategoryTheory.Functor.derivedUnitCocone_ι_app_comp_rightDerivedDesc_app`, which is
naturality of `θ` together with its defining compatibility with the unit of `R`. -/
theorem derivedUnitCocone_ι_app_comp_derivedHomForgetComparison_app
    (X : HomotopyCategory A (ComplexShape.up ℤ))
    (S : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ X) :
    (derivedHomForgetUnitCocone A K h X).ι.app S ≫
        (derivedHomForgetComparison A K U Rt h β).app (DerivedCategory.Qh.obj X) =
      (Functor.derivedUnitCocone (homToDerivedCategoryForget A K)
        (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Qh (Rt ⋙ U) β X).ι.app
        S :=
  have := derivedHomForgetFunctor_isRightDerivedFunctor A K h
  Functor.derivedUnitCocone_ι_app_comp_rightDerivedDesc_app (homToDerivedCategoryForget A K)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Qh
    (derivedHomForgetFunctor A K h) (derivedHomForgetFunctorUnit A K h) (Rt ⋙ U) β X S

/-- **The hypothesis `(*)` of step 3 of Tag 09LK**: the cohomology of the values of the lift is
identified with the morphism groups of the derived category, compatibly with the unit.

The data is a family of maps `φ` out of `H^n(U(R̃(Q X)))`, one for each object `X` of `K(A)` and
each degree `n`, each injective, and together satisfying the displayed formula of the source: the
class in `H^n(U(R̃(Q X)))` obtained from a degree-`n` cohomology class `x` of `Hom^•(K, Y)` by the
coprojection of the comparison cocone at a quasi-isomorphism `s : X ⟶ Y` goes to the left
fraction `Q(s)⟦n⟧⁻¹ ∘ Q(f)`, where `f : K ⟶ Y⟦n⟧` is the morphism of the homotopy category that
`x` is.

This is what a construction of `R̃` produces — it computes the cohomology of its values — and it
is strictly less than saying that `R̃ ⋙ U` is a right derived functor of `Hom(K, -)`, which is the
conclusion drawn from it below. -/
structure DerivedHomLiftIdentification where
  /-- The identification of the degree-`n` cohomology of the value of the lift at `Q X` with the
  morphism group `Hom_{D(A)}(Q K, (Q X)⟦n⟧)` of the derived category. -/
  φ : ∀ (X : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ),
    ↥((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
        ((Rt ⋙ U).obj (DerivedCategory.Qh.obj X))) →
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⟶
        (DerivedCategory.Qh.obj X)⟦n⟧)
  /-- The identification is injective. Surjectivity would also be supplied by any construction of
  `R̃`, but is not used: it follows from the rest. -/
  injective : ∀ X n, Function.Injective (φ X n)
  /-- **The unit compatibility.** On the coprojection of the comparison cocone at a
  quasi-isomorphism `s : X ⟶ Y`, the identification is the left fraction `Q(s)⟦n⟧⁻¹ ∘ Q(f)`. -/
  unit_app : ∀ (X : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ)
    (S : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ X)
    (x : ↥((homToDerivedCategoryForget A K ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj S.right)),
    φ X n ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
        ((Functor.derivedUnitCocone (homToDerivedCategoryForget A K)
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Qh (Rt ⋙ U) β
          X).ι.app S) x) =
      DerivedCategory.Qh.map (homologyHomAddEquiv A K n S.right x) ≫
        (DerivedCategory.Qh.commShiftIso n).hom.app S.right ≫
          CategoryTheory.inv ((DerivedCategory.Qh.map S.hom)⟦n⟧')

/-- **The comparison, read on cohomology and elementwise.** The degree-`n` cohomology class
obtained from a class `x` of `Hom^•(K, Y)` by the coprojection of the comparison cocone of `R` at
a quasi-isomorphism `s : X ⟶ Y` is carried by `H^n(θ)` to the class obtained from `x` by the
coprojection of the comparison cocone of `β` at the same `s`.

This is `CochainComplex.derivedUnitCocone_ι_app_comp_derivedHomForgetComparison_app` after `H^n`
and evaluation. -/
theorem homologyFunctor_map_derivedHomForgetComparison_app_apply
    (X : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ)
    (S : (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)).Under ⊤ X)
    (x : ↥((homToDerivedCategoryForget A K ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj S.right)) :
    (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
        ((derivedHomForgetComparison A K U Rt h β).app (DerivedCategory.Qh.obj X))
        ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((derivedHomForgetUnitCocone A K h X).ι.app S) x) =
      (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
        ((Functor.derivedUnitCocone (homToDerivedCategoryForget A K)
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Qh (Rt ⋙ U) β
          X).ι.app S) x :=
  have key : (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
        ((derivedHomForgetUnitCocone A K h X).ι.app S) ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
        ((derivedHomForgetComparison A K U Rt h β).app (DerivedCategory.Qh.obj X)) =
      (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
        ((Functor.derivedUnitCocone (homToDerivedCategoryForget A K)
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Qh (Rt ⋙ U) β
          X).ι.app S) :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map_comp _ _).symm.trans
      (congrArg _
        (derivedUnitCocone_ι_app_comp_derivedHomForgetComparison_app A K U Rt h β X S))
  (ModuleCat.comp_apply _ _ x).symm.trans (ConcreteCategory.congr_hom key x)

/-- **The two identifications agree.** Composing `H^n(θ)` with the identification `(*)` of the
right-hand side gives the identification `CochainComplex.derivedHomValueHomEquiv` of the
left-hand side.

Both are the left fraction, and the comparison of the two comparison cocones is leg by leg the
identity on the indexing data, so the two agree on every leg; the legs of the left-hand side are
jointly surjective because it is a colimit, which is where Tag 09LK's own hypothesis is used. -/
theorem derivedHomLiftIdentification_homologyFunctor_map_comparison
    (D : DerivedHomLiftIdentification A K U Rt β)
    (X : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ)
    (y : ↥((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
      ((derivedHomForgetFunctor A K h).obj (DerivedCategory.Qh.obj X)))) :
    D.φ X n ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
        ((derivedHomForgetComparison A K U Rt h β).app (DerivedCategory.Qh.obj X)) y) =
      derivedHomValueHomEquiv A K X n h y := by
  obtain ⟨S, x, rfl⟩ := exists_homologyFunctor_map_derivedHomForgetUnitCocone_ι_app A K X n h y
  exact (congrArg (D.φ X n)
      (homologyFunctor_map_derivedHomForgetComparison_app_apply A K U Rt h β X n S x)).trans
    ((D.unit_app X n S x).trans (derivedHomValueHomEquiv_apply A K X n h S x).symm)

/-- **`H^n(θ)` is invertible.** The identification `(*)` carries `H^n(θ)` to a bijection, and is
itself injective, so `H^n(θ)` is a bijection; a bijective morphism of `ℤ`-modules is invertible.

Injectivity: `H^n(θ)` followed by an injection is a bijection. Surjectivity: given a class `z` on
the right, the element of the left-hand side that
`CochainComplex.derivedHomValueHomEquiv` sends to `φ z` has the same image as `z` under the
injection `φ`, hence equals `z`. -/
theorem isIso_homologyFunctor_map_derivedHomForgetComparison_app
    (D : DerivedHomLiftIdentification A K U Rt β)
    (X : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
      ((derivedHomForgetComparison A K U Rt h β).app (DerivedCategory.Qh.obj X))) := by
  have key := derivedHomLiftIdentification_homologyFunctor_map_comparison A K U Rt h β D X n
  rw [ConcreteCategory.isIso_iff_bijective]
  constructor
  · intro y₁ y₂ hy
    refine (derivedHomValueHomEquiv A K X n h).injective ?_
    rw [← key y₁, ← key y₂, hy]
  · intro z
    refine ⟨(derivedHomValueHomEquiv A K X n h).symm (D.φ X n z), D.injective X n ?_⟩
    rw [key, Equiv.apply_symm_apply]

/-- **`θ` is invertible at every object of `D(A)`.** A morphism of `D(Ab)` is invertible as soon
as every `H^n` of it is, and `θ` is invertible on every `H^n` at every `Q X`; every object of
`D(A)` is isomorphic to a `Q X`, because `Q` is a localization functor.

Only `DerivedCategory.isIso_iff` is used to pass from cohomology to `D(Ab)`. The forgetful
functor `U` is not asked to reflect isomorphisms. -/
theorem isIso_derivedHomForgetComparison_app (D : DerivedHomLiftIdentification A K U Rt β)
    (Z : DerivedCategory A) :
    IsIso ((derivedHomForgetComparison A K U Rt h β).app Z) := by
  have := Localization.essSurj DerivedCategory.Qh
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  rw [← NatTrans.isIso_app_iff_of_iso _ (DerivedCategory.Qh.objObjPreimageIso Z),
    DerivedCategory.isIso_iff]
  exact fun n => isIso_homologyFunctor_map_derivedHomForgetComparison_app A K U Rt h β D _ n

/-- **Step 3 of Tag 09LK.** Under Tag 09LK's own hypothesis, and given the identification `(*)`,
the canonical comparison `θ : R Hom(K, -) ⟶ R̃ ⋙ U` out of the abelian-group-valued derived Hom
is a natural isomorphism. -/
theorem isIso_derivedHomForgetComparison (D : DerivedHomLiftIdentification A K U Rt β) :
    IsIso (derivedHomForgetComparison A K U Rt h β) :=
  have : ∀ Z, IsIso ((derivedHomForgetComparison A K U Rt h β).app Z) :=
    isIso_derivedHomForgetComparison_app A K U Rt h β D
  NatIso.isIso_of_isIso_app _

/-- **The conclusion as an isomorphism of functors**, `R Hom(K, -) ≅ R̃ ⋙ U`. -/
def derivedHomForgetComparisonIso (D : DerivedHomLiftIdentification A K U Rt β) :
    derivedHomForgetFunctor A K h ≅ Rt ⋙ U :=
  haveI := isIso_derivedHomForgetComparison A K U Rt h β D
  asIso (derivedHomForgetComparison A K U Rt h β)

include h in
/-- **The lift computes derived Hom.** Equivalently to step 3: `R̃ ⋙ U` together with `β` is
itself a right derived functor of `Hom(K, -) : K(A) ⥤ D(Ab)`, i.e. a left Kan extension along the
localization `K(A) ⥤ D(A)`.

This is the strongest conclusion available here. It is *not* the statement that `R̃` is a right
derived functor of an `E`-valued `Hom(K, -)`: getting that from this would mean reflecting
essential constancy through `U`, which is false even for a full and faithful functor
(`CategoryTheory.Functor.exists_fullyFaithful_not_reflecting`). -/
theorem isRightDerivedFunctor_comp_of_derivedHomLiftIdentification
    (D : DerivedHomLiftIdentification A K U Rt β) :
    (Rt ⋙ U).IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  have := derivedHomForgetFunctor_isRightDerivedFunctor A K h
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc (derivedHomForgetFunctor A K h)
    (derivedHomForgetFunctorUnit A K h) (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (Rt ⋙ U) β).2 (isIso_derivedHomForgetComparison A K U Rt h β D)

/-- **The hypothesis `(*)` is a reformulation of the conclusion, not something weaker.** If
`R̃ ⋙ U` with `β` is already a right derived functor of `Hom(K, -) : K(A) ⥤ D(Ab)`, then `(*)`
holds: the comparison `θ` is invertible, and `(*)` is
`CochainComplex.derivedHomValueHomEquiv` transported backwards along `H^n(θ)`.

Together with
`CochainComplex.isRightDerivedFunctor_comp_of_derivedHomLiftIdentification` this says the two are
equivalent, which is worth recording plainly: step 3 does not derive the conclusion from
something strictly weaker. What it does is exhibit the conclusion in the form a *construction* of
`R̃` can discharge — a computation of the cohomology of the values, with the left fraction on the
comparison cocone — rather than in the form of a left Kan extension property, which such a
construction does not come with. -/
def derivedHomLiftIdentificationOfIsRightDerivedFunctor
    (hG : (Rt ⋙ U).IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    DerivedHomLiftIdentification A K U Rt β :=
  haveI := derivedHomForgetFunctor_isRightDerivedFunctor A K h
  haveI : IsIso (derivedHomForgetComparison A K U Rt h β) :=
    (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc (derivedHomForgetFunctor A K h)
      (derivedHomForgetFunctorUnit A K h) (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
      (Rt ⋙ U) β).1 hG
  have hbij : ∀ (X : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ), Function.Bijective
      ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
        ((derivedHomForgetComparison A K U Rt h β).app (DerivedCategory.Qh.obj X))) :=
    fun _ _ => (ConcreteCategory.isIso_iff_bijective _).1 inferInstance
  { φ := fun X n z =>
      derivedHomValueHomEquiv A K X n h ((Equiv.ofBijective _ (hbij X n)).symm z)
    injective := fun X n _ _ hz =>
      (Equiv.ofBijective _ (hbij X n)).symm.injective
        ((derivedHomValueHomEquiv A K X n h).injective hz)
    unit_app := fun X n S x =>
      (congrArg (derivedHomValueHomEquiv A K X n h)
        ((Equiv.symm_apply_eq (Equiv.ofBijective _ (hbij X n))).2
          (homologyFunctor_map_derivedHomForgetComparison_app_apply A K U Rt h β X n
            S x).symm)).trans (derivedHomValueHomEquiv_apply A K X n h S x) }

/-- **`θ` is invertible as soon as `R̃ ⋙ U` is already a right derived functor of
`Hom(K, -) : K(A) ⥤ D(Ab)` with unit `β`.** This is the forward direction of
`CategoryTheory.Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc` at `θ`, which is by
definition the descent of `β` along the universal property of `R`.

It is stated separately from
`CochainComplex.derivedHomLiftIdentificationOfIsRightDerivedFunctor` because the identification
`(*)` is not the only way to reach step 3's conclusion. A construction of `R̃` that comes with
the left Kan extension property of `R̃ ⋙ U` already — K-injective resolutions on `A` produce one,
in `StacksFrontier/Algebra/DifferentialGraded/Module/DerivedHomKInjectiveAssembly.lean` —
discharges the hypothesis here directly, and routing such a proof through `(*)` would be a detour
through a reformulation of the hypothesis it starts from. -/
theorem isIso_derivedHomForgetComparison_of_isRightDerivedFunctor
    (hG : (Rt ⋙ U).IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    IsIso (derivedHomForgetComparison A K U Rt h β) :=
  have := derivedHomForgetFunctor_isRightDerivedFunctor A K h
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc (derivedHomForgetFunctor A K h)
    (derivedHomForgetFunctorUnit A K h) (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    (Rt ⋙ U) β).1 hG

/-- **The comparison as an isomorphism `R Hom(K, -) ≅ R̃ ⋙ U`**, from the left Kan extension
property of `R̃ ⋙ U` rather than from the identification `(*)`. -/
def derivedHomForgetComparisonIsoOfIsRightDerivedFunctor
    (hG : (Rt ⋙ U).IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    derivedHomForgetFunctor A K h ≅ Rt ⋙ U :=
  haveI := isIso_derivedHomForgetComparison_of_isRightDerivedFunctor A K U Rt h β hG
  asIso (derivedHomForgetComparison A K U Rt h β)

end CochainComplex

end
