module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomFunctorAssembly
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomEvaluationDerivedIso
public import StacksFrontier.CategoryTheory.EssentiallyConstant.Transport

/-!
# The two encodings of `Hom(K, -)` in Tag 09LK agree

[Stacks, Tag 09LK] right derives the functor `Hom(K, -)` out of a cochain complex `K` in an
abelian category `A`, and this development states that functor in two different ways, because
the endomorphism object `E` of `K` is modelled twice:

* as a **differential graded algebra**, `DGCategory.endAlgebra (Comp^dg A) K`, giving
  `CochainComplex.homToDerivedCategoryForget A K`, the functor
  `K(A) ⥤ D(E, d) ⥤ D(Ab)` that step 3 of the replacement proof is stated for;
* as a **one-object differential graded category**,
  `DGCategory.endDGCategory (Comp^dg A) K`, giving
  `CochainComplex.derivedHomReflectorSource A K`, the functor `K(A) ⥤ D(E)` that the
  reflector construction of steps 1 and 2 works in, read in `D(Ab)` by
  `DGCategory.endDerivedForget`.

Both are "`Hom(K, -)` read in the derived category of abelian groups", but they are not the same
term: in the first the degree-`n` part of a value is the range of the `n`-th inclusion into a
direct sum, in the second it is the group `C(K, Y)_n` of degree-`n` cochains itself. This file
supplies the comparison between them, which
`CochainComplex.isRightDerivedFunctor_derivedHomReflectorFunctor` records as owed, and uses it to
restate [Stacks, Tag 09LK]'s own hypothesis and step 3's conclusion in the encoding that theorem
consumes.

## Where the mathematics is

Nowhere here: the comparison is already in the library, under a name that mentions neither
encoding's endomorphism object. Its content is `CochainComplex.homEvaluationComparisonIso`, the
degreewise linear equivalence `CochainComplex.homGradingEquiv` assembled into complexes, and it
is carried to the derived categories by `CochainComplex.homEvaluationDerivedIso` and
`CochainComplex.homDerivedLiftForgetIso`. The only thing missing was the observation that
`CochainComplex.derivedHomReflectorSource` and `CochainComplex.homDerivedLift` are the *same*
functor — they are the differential graded Yoneda functor followed by evaluation at `K` and the
quotient functor of `D(E)`, bracketed differently — so that the existing isomorphism already has
the source the reflector's theorems are stated with.

## Main definitions

* `CochainComplex.derivedHomEncodingComparison`: **the comparison `ι`**, a natural isomorphism
  `Hom(K, -) ⋙ U ≅ Hom(K, -)` between the one-object-category encoding read through the
  forgetful functor and the differential graded algebra encoding.

## Main results

* `CochainComplex.derivedHomReflectorSource_eq_homDerivedLift`: the two spellings of the
  `D(E)`-valued `Hom(K, -)` are the same functor.
* `CochainComplex.isRightDerivable_derivedHomReflectorSource_comp_forget`: **Tag 09LK's own
  hypothesis in the reflector's encoding**, from the hypothesis as the source states it.
* `CochainComplex.isRightDerivedFunctor_derivedHomReflectorForgetUnit`: **step 3's conclusion in
  the reflector's encoding**, from step 3's conclusion as it is proved. This is the hypothesis
  `hstep3` of `CochainComplex.isRightDerivedFunctor_derivedHomReflectorFunctor`, so with it that
  theorem no longer owes a comparison of encodings.
* `CategoryTheory.Functor.IsRightDerivable.of_natIso`: everywhere-definedness of a right derived
  functor only depends on the functor up to isomorphism.

## Implementation notes

`CochainComplex.derivedHomEncodingComparison` is `CochainComplex.homDerivedLiftForgetIso` on the
nose; it is given a name of its own because the identity of the two sources is a definitional
unfolding of `Functor.comp` that no `rw` can see, and because the statements below have to name
the isomorphism whose inverse the two units differ by.

The two units do differ by exactly that inverse:
`CochainComplex.derivedHomForgetUnitOfLift_derivedHomEncodingComparison` says
`β_alg = ι⁻¹ ≫ β_cat`, which is what makes the transport of step 3's conclusion a matter of
`CategoryTheory.Functor.isLeftKanExtension_iff_of_iso₂` with the identity on the extension.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK);
  [Tag 09LE](https://stacks.math.columbia.edu/tag/09LE), the functor `Hom(K, -)` and the
  endomorphism object of `K`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂

variable {D : Type u₁} [Category.{v₁} D] {D' : Type u₂} [Category.{v₂} D']

/-- **Right derivability is invariant under isomorphism of the functor.** If the right derived
functor of `F` is defined at every object and `F ≅ F'`, then the right derived functor of `F'` is
defined at every object: the ind-object of `F'` at `X` is isomorphic to that of `F`, and
essential constancy transports along an isomorphism of diagrams. -/
theorem IsRightDerivable.of_natIso {F F' : D ⥤ D'} (e : F ≅ F') (W : MorphismProperty D)
    (h : F.IsRightDerivable W) : F'.IsRightDerivable W := fun X => by
  obtain ⟨c, hc⟩ := h X
  obtain ⟨s₀, r, hw⟩ := (F.isRightDerivedValueAt_iff W X c).1 hc
  refine (F'.exists_isRightDerivedValueAt_iff W X).2 ⟨_, s₀, _, hw.precompose ?_⟩
  exact Functor.isoWhiskerLeft (MorphismProperty.Under.forget W ⊤ X)
    (Functor.isoWhiskerLeft (Under.forget X) e.symm)

end CategoryTheory.Functor

namespace CochainComplex

universe v w

variable (A : Type) [Category.{0} A] [Abelian A] (K : CochainComplex A ℤ)
  [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]

omit [HasDerivedCategory (ModuleCat ℤ)] in
/-- **The two spellings of the `D(E)`-valued `Hom(K, -)` are one functor.** The source
`CochainComplex.derivedHomReflectorSource` that the reflector of steps 1 and 2 of
[Stacks, Tag 09LK] is a right derived functor of, and the lift
`CochainComplex.homDerivedLift` that the identification of encodings is stated for, are both the
comparison equivalence of homotopy categories followed by the differential graded Yoneda functor,
evaluation at `K` and the quotient functor of `D(E)`; they differ only in how the composite is
bracketed. -/
theorem derivedHomReflectorSource_eq_homDerivedLift :
    derivedHomReflectorSource A K = homDerivedLift A K := rfl

/-- **The comparison of the two encodings of `Hom(K, -)` in [Stacks, Tag 09LK].** The
`D(E)`-valued `Hom(K, -)` of the one-object differential graded category
`E = C(K, K)`, read in `D(Ab)` by the forgetful functor `U = DGCategory.endDerivedForget`, is the
`D(Ab)`-valued `Hom(K, -)` built from the endomorphism differential graded *algebra* `End(K)`.

This is `CochainComplex.homDerivedLiftForgetIso`, whose source is the same functor as
`CochainComplex.derivedHomReflectorSource` by
`CochainComplex.derivedHomReflectorSource_eq_homDerivedLift`; its mathematical content is the
degreewise identification `CochainComplex.homGradingEquiv` of a homogeneous element of the
representable differential graded `End(K)`-module with the cochain it is. No hypothesis beyond
those the two functors already carry is used. -/
def derivedHomEncodingComparison :
    derivedHomReflectorSource A K ⋙ DGCategory.endDerivedForget (dgCategory A) K ≅
      homToDerivedCategoryForget A K :=
  homDerivedLiftForgetIso A K

/-- **[Stacks, Tag 09LK]'s own hypothesis, in the reflector's encoding.** The tag assumes that
the right derived functor of the abelian-group-valued `Hom(K, -)` is everywhere defined; stated
for the differential graded algebra encoding, that is derivability of
`CochainComplex.homToDerivedCategoryForget`. The comparison carries it to the encoding the
reflector's theorems use, which is the hypothesis `h` of
`CochainComplex.isRightDerivedFunctor_derivedHomReflectorFunctor`. -/
theorem isRightDerivable_derivedHomReflectorSource_comp_forget
    (h : (homToDerivedCategoryForget A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    (derivedHomReflectorSource A K ⋙
        DGCategory.endDerivedForget (dgCategory A) K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) :=
  Functor.IsRightDerivable.of_natIso (derivedHomEncodingComparison A K).symm _ h

section Reflector

variable [((DGCategory.yonedaDGFunctor (dgCategory A)).onK).CommShift ℤ]
  [((DGCategory.yonedaDGFunctor (dgCategory A)).onK).IsTriangulated] [HasDerivedCategory.{v} A]
  (β : derivedHomReflectorSource A K ⟶
    DerivedCategory.Qh ⋙ derivedHomReflectorFunctor A K)

/-- **The two units differ by the comparison.** The unit step 3 of the replacement proof of
[Stacks, Tag 09LK] consumes is built from a lift and an identification of encodings; at the
identification of this file it is the unit of steps 1 and 2 forgotten along `U`, precomposed with
the inverse of the comparison. -/
theorem derivedHomForgetUnitOfLift_derivedHomEncodingComparison :
    derivedHomForgetUnitOfLift A K (derivedHomReflectorForget A K)
        (derivedHomReflectorFunctor A K) (derivedHomReflectorSource A K)
        (derivedHomEncodingComparison A K) β =
      (derivedHomEncodingComparison A K).inv ≫ derivedHomReflectorForgetUnit A K β :=
  rfl

/-- **Step 3's conclusion, in the reflector's encoding.** Step 3 of the replacement proof of
[Stacks, Tag 09LK] concludes that `R̃ ⋙ U` with the `U`-image of the unit is a right derived
functor of the abelian-group-valued `Hom(K, -)`, stated for the differential graded algebra
encoding `CochainComplex.homToDerivedCategoryForget`. The comparison restates it for the source
`CochainComplex.derivedHomReflectorSource A K ⋙ U` that the reflector's theorems use: the two
units differ by an isomorphism of their common source, and a left Kan extension does not notice
that. This is the hypothesis `hstep3` of
`CochainComplex.isRightDerivedFunctor_derivedHomReflectorFunctor`. -/
theorem isRightDerivedFunctor_derivedHomReflectorForgetUnit
    (hstep3 : (derivedHomReflectorFunctor A K ⋙
        derivedHomReflectorForget A K).IsRightDerivedFunctor
      ((derivedHomEncodingComparison A K).inv ≫ derivedHomReflectorForgetUnit A K β)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))) :
    (derivedHomReflectorFunctor A K ⋙
        derivedHomReflectorForget A K).IsRightDerivedFunctor
      (derivedHomReflectorForgetUnit A K β)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  rw [Functor.isRightDerivedFunctor_iff_isLeftKanExtension] at hstep3 ⊢
  refine (Functor.isLeftKanExtension_iff_of_iso₂ _ _
    (derivedHomEncodingComparison A K).symm (Iso.refl _) ?_).1 hstep3
  simp [derivedHomReflectorForgetUnit]

end Reflector

end CochainComplex

end
