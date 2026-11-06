module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedHomPhiTransport
public import StacksFrontier.CategoryTheory.Functor.Derived.EverywhereDefinedTriangulated

/-!
# The functor `R Hom(K, -) : D(A) ⥤ D(E, d)` of Tag 09LK at one set of witnesses

Steps 1 and 2 of the replacement proof of [Stacks, Tag 09LK] produce their reflector `L`, its
unit `η` and the hypothesis `hΦ` as *witnesses of an existential*
(`DGCategory.exists_derivedHomReflector_data`), and the identification `(*)` of
`DGCategory.derivedHomPhiQh` is then taken at those same witnesses. Step 3 needs the functor, its
unit and `(*)` at **one** choice, since a second choice gives a different `L` and nothing matches.

This file makes that choice once, with `Classical.choice`, and exposes every piece of it by name.
Everything downstream — the exactness of `DGCategory.phiReflector`, the identification `(*)` and
step 3 — is stated for an arbitrary `L` with those clauses, so it applies to the choice made here
by instantiation and nothing is restated.

## Main definitions

* `CochainComplex.derivedHomReflectorL`, `CochainComplex.derivedHomReflectorEta`: the chosen
  reflector on `K(Mod^dg(Comp^dg A))` and its unit, with the `CommShift`/`IsTriangulated`
  instances of the chosen `L` registered — they cannot be found by instance search, since `L` is
  a witness.
* `CochainComplex.derivedHomReflectorFunctor`: **the functor `R Hom(K, -) : D(A) ⥤ D(E, d)`** of
  Tag 09LK, namely `DGCategory.phiReflector` at the chosen witnesses. It is an `abbrev`, so the
  exactness instances of `DGCategory.phiReflector` and every statement about `phiReflector` apply
  to it unchanged; no instance is re-registered here.
* `CochainComplex.derivedHomReflectorSource`: the functor it is to be the right derived functor
  *of*, namely the `D(E, d)`-valued `Hom(K, -) : K(A) ⥤ D(E, d)` in the encoding the reflector
  construction works in.

## Main results

* `CochainComplex.derivedHomReflector_local`, `CochainComplex.derivedHomReflector_cone`,
  `CochainComplex.derivedHomReflector_isZero`: the three clauses of steps 1 and 2 at the chosen
  witnesses. The third is the `hΦ` every `DGCategory.phiReflector` call is given.
* `CochainComplex.derivedHomReflectorSource_eq`: the source really is `Hom(K, -)`, i.e. the
  functor `X ↦ C(K, X)` of [Stacks, Tag 09LE] read in `D(E, d)`.
* `CochainComplex.isRightDerivedFunctor_derivedHomReflectorFunctor`: **the `D(E, d)`-level
  universal property**, from Tag 09LK's own hypothesis, step 3's conclusion, and the reflection
  of right-derived values along the forgetful functor, carried as the named hypothesis `hU`.
* `CategoryTheory.Functor.isRightDerivedFunctor_of_isRightDerivedValueAt_derivedUnitCocone`: the
  general converse of `CategoryTheory.Functor.isRightDerivedValueAt_derivedUnitCocone` — pointwise
  values at the comparison cocones make a candidate a left Kan extension.

## What is still owed

**The `D(E, d)`-level universal property remains conditional.** Tag 09LK's statement asserts a
canonical exact functor `D(A) ⥤ D(E, d)` reducing to the usual `R Hom(K, -)`, and those three
clauses carry the `09LK` registration: the functor itself below,
`DGCategory.phiReflectorCommShift` with `DGCategory.phiReflector_isTriangulated` for exactness,
and `DGCategory.derivedHomForgetPhiReflectorBetaIso` for the reduction. The property
`(derivedHomReflectorFunctor A K).IsRightDerivedFunctor β W` — how the source *constructs* the
functor — is proved only as an implication, from `hU` in
`CochainComplex.isRightDerivedFunctor_derivedHomReflectorFunctor` and from `hdef` in
`CochainComplex.isRightDerivedFunctor_derivedHomReflectorFunctor_of_isRightDerivable`; neither
`hU` nor `hdef` is among Tag 09LK's hypotheses, so neither declaration is registered. The
residue is the one implication "`R(Hom(K, -) ⋙ U)` everywhere defined ⇒ `R Hom(K, -)` everywhere
defined" for this additive exact conservative `U`, which is **open** here: neither proved nor
refuted.

`CochainComplex.isRightDerivedFunctor_derivedHomReflectorFunctor` reaches the `D(E, d)`-level
universal property but it is **not** registered as `09LK`, because it assumes one result this
development does not prove: that the forgetful functor
`U : D(E, d) ⥤ D(Ab)` *reflects* right-derived values. That is the step the Stacks Project's own
proof passes over, and the only other way to it, step 3
(`DGCategory.isRightDerivedFunctor_phiReflectorForget`), gives the property for the composite
`R̃ ⋙ U` valued in `D(Ab)` and nothing more: the owed elementwise computation `unit_app_id` is a
statement about cohomology classes in `D(Ab)`, so everything it can yield is `D(Ab)`-valued. The
general reflection lemma is refuted in
`StacksFrontier/CategoryTheory/Functor/Derived/ValueReflection.lean`; the statement for *this* `U`,
which is additive, exact and conservative, is open rather than refuted. The declaration's
docstring says all of this at the hypothesis.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK);
  [Tag 09LE](https://stacks.math.columbia.edu/tag/09LE), the functor `X ↦ C(K, X)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.ObjectProperty

namespace CategoryTheory.Functor

universe v₁ v₂ v₃ u₁ u₂ u₃

/-- **Pointwise values at the comparison cocones make a candidate the right derived functor.**
The converse of `CategoryTheory.Functor.isRightDerivedValueAt_derivedUnitCocone`: if, for every
`X`, the cocone with vertex `F'(L X)` attached to `α` is a *value* of the right derived functor
at `X` in the sense of Tag 05S9, then `F'` together with `α` is the right derived functor of `F`
along `L`.

A value is a colimit cocone, the comparison functor from Deligne's index category `X/W` to the
Kan-extension index category is final, so `α` is a pointwise left Kan extension at every `L X`,
hence — `L` being essentially surjective — at every object, hence a left Kan extension. No
derivability hypothesis is needed: it is contained in the assumption. -/
theorem isRightDerivedFunctor_of_isRightDerivedValueAt_derivedUnitCocone
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {H : Type u₃} [Category.{v₃} H]
    (F : C ⥤ H) (W : MorphismProperty C) [W.HasLeftCalculusOfFractions] (L : C ⥤ D)
    [L.IsLocalization W] (F' : D ⥤ H) (α : F ⟶ L ⋙ F')
    (hval : ∀ X, F.IsRightDerivedValueAt W X (derivedUnitCocone F W L F' α X)) :
    F'.IsRightDerivedFunctor α W := by
  haveI := Localization.essSurj L W
  have hpt : ∀ X : C, (LeftExtension.mk F' α).IsPointwiseLeftKanExtensionAt (L.obj X) := by
    intro X
    letI := W.final_underToCostructuredArrow L X
    exact Final.isColimitWhiskerEquiv (W.underToCostructuredArrow L X)
      ((LeftExtension.mk F' α).coconeAt (L.obj X)) (hval X).isColimit
  have hall : (LeftExtension.mk F' α).IsPointwiseLeftKanExtension := fun Y =>
    LeftExtension.isPointwiseLeftKanExtensionAtOfIso' _ (hpt (L.objPreimage Y))
      (L.objObjPreimageIso Y)
  exact (isRightDerivedFunctor_iff_isLeftKanExtension F' α W).2 hall.isLeftKanExtension

end CategoryTheory.Functor

namespace CochainComplex

universe w v

variable (A : Type) [Category.{0} A] [Abelian A]
  [((DGCategory.yonedaDGFunctor (CochainComplex.dgCategory A)).onK).CommShift ℤ]
  [((DGCategory.yonedaDGFunctor (CochainComplex.dgCategory A)).onK).IsTriangulated]

/-- The homotopy category of right differential graded modules over the differential graded
category of complexes in `A`, where the reflector of steps 1 and 2 lives. -/
abbrev derivedHomModuleK :=
  (DGCategory.rightModuleCategory.{0} (CochainComplex.dgCategory A)).K

/-- Steps 1 and 2 of [Stacks, Tag 09LK] at the canonical generator family
`DGCategory.phiGen`, with the reflector, its unit and all three clauses kept. This is
`DGCategory.exists_derivedHomReflector_data` with its hypothesis discharged by `fun _ h ↦ h`, and
it is the single existential every declaration below chooses from. -/
def exists_derivedHomReflectorData :=
  DGCategory.exists_derivedHomReflector_data (CochainComplex.dgCategory A) (DGCategory.phiGen A)
    ((DGCategory.yonedaDGFunctor (CochainComplex.dgCategory A)).onK)
    (DGCategory.RightModule.yonedaInverseImage (CochainComplex.dgCategory A)
      (DGCategory.phiGen A)) fun _ h ↦ h

/-- **The chosen reflector `L`** of steps 1 and 2 of [Stacks, Tag 09LK]. -/
def derivedHomReflectorL : derivedHomModuleK A ⥤ derivedHomModuleK A :=
  (exists_derivedHomReflectorData A).choose

instance derivedHomReflectorL_commShift : (derivedHomReflectorL A).CommShift ℤ :=
  (exists_derivedHomReflectorData A).choose_spec.choose

instance derivedHomReflectorL_isTriangulated : (derivedHomReflectorL A).IsTriangulated :=
  (exists_derivedHomReflectorData A).choose_spec.choose_spec.choose

/-- **The chosen unit `η : 𝟭 ⟶ L`** of steps 1 and 2 of [Stacks, Tag 09LK]. -/
def derivedHomReflectorEta : 𝟭 (derivedHomModuleK A) ⟶ derivedHomReflectorL A :=
  (exists_derivedHomReflectorData A).choose_spec.choose_spec.choose_spec.choose

/-- **Every `L X` is local**: the first clause of step 1, at the chosen witnesses. -/
theorem derivedHomReflector_local (X : derivedHomModuleK A) :
    (DGCategory.RightModule.yonedaLocalizing (CochainComplex.dgCategory A)
      (DGCategory.phiGen A)).rightOrthogonal ((derivedHomReflectorL A).obj X) :=
  (exists_derivedHomReflectorData A).choose_spec.choose_spec.choose_spec.choose_spec.choose X

/-- **The cone of every `η X` is in `N`**: the second clause of step 1, at the chosen
witnesses. -/
theorem derivedHomReflector_cone (X Z : derivedHomModuleK A) (f : Z ⟶ X)
    (g : (derivedHomReflectorL A).obj X ⟶ Z⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f ((derivedHomReflectorEta A).app X) g ∈
      distTriang (derivedHomModuleK A)) :
    DGCategory.RightModule.yonedaLocalizing (CochainComplex.dgCategory A)
      (DGCategory.phiGen A) Z :=
  (exists_derivedHomReflectorData
    A).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose X Z f g hT

/-- **`L` kills the preimage of `N`**: the hypothesis `hΦ` of `DGCategory.derivedHomReflector`,
at the chosen witnesses. -/
theorem derivedHomReflector_isZero (X) (hX : DGCategory.RightModule.yonedaInverseImage
    (CochainComplex.dgCategory A) (DGCategory.phiGen A) X) :
    IsZero ((((DGCategory.yonedaDGFunctor (CochainComplex.dgCategory A)).onK) ⋙
      derivedHomReflectorL A).obj X) :=
  (exists_derivedHomReflectorData
    A).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec X hX

variable (K : CochainComplex A ℤ)

/-- **The `D(E, d)`-valued `Hom(K, -) : K(A) ⥤ D(E, d)`**, the functor [Stacks, Tag 09LK] right
derives, in the encoding the reflector construction of steps 1 and 2 works in: the comparison
equivalence of the two homotopy categories, the differential graded Yoneda functor, evaluation at
`K`, and the localization of right differential graded `C(K, K)`-modules at the
quasi-isomorphisms.

`CochainComplex.derivedHomReflectorSource_eq` identifies it with the functor `X ↦ C(K, X)` of
[Stacks, Tag 09LE]. It is stated in this form because this is the form the unit of the
construction comes in: `DGCategory.derivedHomReflectorUnit` is a transformation out of
`Φ ⋙ ev_K ⋙ Q_E`. -/
def derivedHomReflectorSource : HomotopyCategory A (ComplexShape.up ℤ) ⥤
    DGCategory.RightModule.derivedCategory
      (DGCategory.endDGCategory (CochainComplex.dgCategory A) K) :=
  (CochainComplex.homotopyCategoryEquivalence A).functor ⋙
    (DGCategory.yonedaDGFunctor (CochainComplex.dgCategory A)).onK ⋙
      DGCategory.evaluationOnK (CochainComplex.dgCategory A) K ⋙
        DGCategory.RightModule.derivedQ
          (DGCategory.endDGCategory (CochainComplex.dgCategory A) K)

/-- **The source really is `Hom(K, -)`.** The differential graded Yoneda functor followed by
evaluation at `K` is the functor `X ↦ C(K, X)` of [Stacks, Tag 09LE], so
`CochainComplex.derivedHomReflectorSource` is that functor read in `D(E, d)` and reindexed by the
ordinary homotopy category along the comparison equivalence. -/
theorem derivedHomReflectorSource_eq :
    derivedHomReflectorSource A K =
      (CochainComplex.homotopyCategoryEquivalence A).functor ⋙
        (DGCategory.homDGFunctor (CochainComplex.dgCategory A) K).onK ⋙
          DGCategory.RightModule.derivedQ
            (DGCategory.endDGCategory (CochainComplex.dgCategory A) K) :=
  congrArg ((CochainComplex.homotopyCategoryEquivalence A).functor ⋙ ·)
    (DGCategory.yonedaOnK_comp_evaluationOnK_comp_derivedQ (CochainComplex.dgCategory A) K)

variable [HasDerivedCategory.{v} A]

/-- **The functor `R Hom(K, -) : D(A) ⥤ D(E, d)` of [Stacks, Tag 09LK]**, for
`E = C(K, K)` the endomorphism differential graded category of `K` in `Comp^dg(A)`: the
reflector-and-descend functor `DGCategory.phiReflector` of steps 1 and 2, taken at the chosen
witnesses `CochainComplex.derivedHomReflectorL` and `CochainComplex.derivedHomReflector_isZero`.

Deliberately an `abbrev`: the exactness and shift compatibility of `DGCategory.phiReflector`
(`DGCategory.phiReflectorCommShift`, `DGCategory.phiReflector_isTriangulated`) and the
identification `(*)` and step 3 at an arbitrary reflector all apply to it after reduction, so
nothing has to be re-registered or restated at the chosen witnesses — and in particular no second
`CommShift` term competes with the canonical one. -/
@[stacks 09LK "the functor itself: R Hom(K, -) : D(A) ⥤ D(E, d), for E the endomorphism \
differential graded category of K"]
abbrev derivedHomReflectorFunctor : DerivedCategory A ⥤
    DGCategory.RightModule.derivedCategory
      (DGCategory.endDGCategory (CochainComplex.dgCategory A) K) :=
  DGCategory.phiReflector A K (derivedHomReflectorL A) (derivedHomReflector_isZero A)

variable [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]

/-- **`U`**, the forgetful functor `D(E, d) ⥤ D(Ab)` of `DGCategory.endDerivedForget`, named here
because the statements below do not fit in a line otherwise. -/
abbrev derivedHomReflectorForget :
    DGCategory.RightModule.derivedCategory
        (DGCategory.endDGCategory (CochainComplex.dgCategory A) K) ⥤
      DerivedCategory (ModuleCat.{0} ℤ) :=
  DGCategory.endDerivedForget (CochainComplex.dgCategory A) K

/-- The `U`-image of a unit `β : Hom(K, -) ⟶ Q ⋙ R̃`, reassociated: the comparison
`Hom(K, -) ⋙ U ⟶ Q ⋙ (R̃ ⋙ U)` that step 3's conclusion
`DGCategory.isRightDerivedFunctor_phiReflectorForget` is stated with respect to. -/
def derivedHomReflectorForgetUnit
    (β : derivedHomReflectorSource A K ⟶
      DerivedCategory.Qh ⋙ derivedHomReflectorFunctor A K) :
    derivedHomReflectorSource A K ⋙ derivedHomReflectorForget A K ⟶
      DerivedCategory.Qh ⋙ derivedHomReflectorFunctor A K ⋙
        derivedHomReflectorForget A K :=
  Functor.whiskerRight β (derivedHomReflectorForget A K) ≫
    (Functor.associator DerivedCategory.Qh (derivedHomReflectorFunctor A K)
      (derivedHomReflectorForget A K)).hom

/-- **The `D(E, d)`-level universal property of Tag 09LK, from the reflection of right-derived
values along `U`.** Let `β` be a unit `Hom(K, -) ⟶ Q ⋙ R̃` for the functor
`CochainComplex.derivedHomReflectorFunctor` of steps 1 and 2. Then `R̃` together with `β` is a
right derived functor of the `D(E, d)`-valued `Hom(K, -)` along `K(A) ⥤ D(A)` — the conclusion
Tag 09LK asserts — given three things.

* `h`: **Tag 09LK's own hypothesis**, that the right derived functor of the abelian-group-valued
  `Hom(K, -)` is everywhere defined, stated for `Hom(K, -) ⋙ U` in this encoding.
* `hstep3`: **step 3's conclusion**, that `R̃ ⋙ U` with the `U`-image of `β` is a right derived
  functor of `Hom(K, -) ⋙ U`. This is `DGCategory.isRightDerivedFunctor_phiReflectorForget`,
  which is proved from `h` and the owed elementwise computation `unit_app_id`; it is carried as a
  hypothesis here rather than invoked only because of the owed elementwise computation
  `unit_app_id`. The comparison of encodings that this paragraph once said was missing *does*
  exist: `CochainComplex.homToDerivedCategoryForget A K` is the *differential graded algebra*
  encoding of `E`, and `CochainComplex.derivedHomEncodingComparison` identifies it with
  `Hom(K, -) ⋙ U` in the `DGCategory.endDGCategory (Comp^dg A) K` encoding, so
  `CochainComplex.isRightDerivedFunctor_derivedHomReflectorForgetUnit` supplies `hstep3` and
  `CochainComplex.isRightDerivable_derivedHomReflectorSource_comp_forget` supplies `h`, both
  from the hypothesis as the source states it. `unit_app_id` is therefore the only way in which
  `hstep3` is still owed, and it is not a hypothesis on `A`.
* `hU`: **the assumption this development does not prove** — that the forgetful functor `U`
  *reflects* right-derived values: a cocone on Deligne's ind-object `X/W ⥤ D(E, d)` whose
  `U`-image is a value of the right derived functor of `Hom(K, -) ⋙ U` at `X` is already a value
  of the right derived functor of the `D(E, d)`-valued `Hom(K, -)` at `X`. Equivalently, `U`
  reflects essential constancy of these ind-objects. **This is the step the Stacks Project's own
  proof of Tag 09LK passes over**, and it is why the declaration below is deliberately **not**
  registered as `09LK`: a registration may sit only on a declaration that proves its tag under
  the source's own hypotheses, and this one assumes a further result.

*The status of `hU`.* The general lemma "`U` reflects right-derived values" is **false**:
`CategoryTheory.Functor.exists_fullyFaithful_not_reflecting` and
`CategoryTheory.Functor.isRightDerivable_comp_and_not_isRightDerivable_of_map_eq_zero` of
`StacksFrontier/CategoryTheory/Functor/Derived/ValueReflection.lean` refute it, the second even for
a conservative functor. That does **not** refute `hU`. The counterexample functor there is
neither additive nor exact, whereas `DGCategory.endDerivedForget` is additive, exact and
conservative. So `hU` is **open** for this `U`, not refuted — a distinction worth keeping, since
the only positive result available, `CategoryTheory.Functor.IsRightDerivable.of_comp`, needs `U`
full and faithful with idempotent-complete source, and `U` is neither full nor faithful.

The proof is the three steps the obstruction leaves: `h` and `hstep3` make the `U`-image of the
comparison cocone at `X` a value of the right derived functor of `Hom(K, -) ⋙ U`
(`CategoryTheory.Functor.isRightDerivedValueAt_derivedUnitCocone`, after matching that `U`-image
with the comparison cocone of the `U`-image of `β`); `hU` carries that back to `D(E, d)`; and
pointwise values at the comparison cocones are a left Kan extension
(`CategoryTheory.Functor.isRightDerivedFunctor_of_isRightDerivedValueAt_derivedUnitCocone`). -/
theorem isRightDerivedFunctor_derivedHomReflectorFunctor
    (β : derivedHomReflectorSource A K ⟶
      DerivedCategory.Qh ⋙ derivedHomReflectorFunctor A K)
    (h : (derivedHomReflectorSource A K ⋙ derivedHomReflectorForget A K).IsRightDerivable
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hstep3 : (derivedHomReflectorFunctor A K ⋙ derivedHomReflectorForget A K).IsRightDerivedFunctor
      (derivedHomReflectorForgetUnit A K β)
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)))
    (hU : ∀ (X : HomotopyCategory A (ComplexShape.up ℤ))
      (c : Limits.Cocone (MorphismProperty.Under.forget
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) ⊤ X ⋙
        Under.forget X ⋙ derivedHomReflectorSource A K)),
      (derivedHomReflectorSource A K ⋙ derivedHomReflectorForget A K).IsRightDerivedValueAt
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) X
          ((derivedHomReflectorForget A K).mapCocone c) →
        (derivedHomReflectorSource A K).IsRightDerivedValueAt
          (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) X c) :
    (derivedHomReflectorFunctor A K).IsRightDerivedFunctor β
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  haveI := hstep3
  refine Functor.isRightDerivedFunctor_of_isRightDerivedValueAt_derivedUnitCocone
    (derivedHomReflectorSource A K) (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
    DerivedCategory.Qh (derivedHomReflectorFunctor A K) β fun X => hU X _ ?_
  refine Functor.isRightDerivedValueAt_of_isColimit
    (derivedHomReflectorSource A K ⋙ derivedHomReflectorForget A K)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) X (h X) ?_
  refine Limits.IsColimit.ofIsoColimit (Functor.isRightDerivedValueAt_derivedUnitCocone
    (derivedHomReflectorSource A K ⋙ derivedHomReflectorForget A K)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) DerivedCategory.Qh
    (derivedHomReflectorFunctor A K ⋙ derivedHomReflectorForget A K)
    (derivedHomReflectorForgetUnit A K β) h X).isColimit
    (Limits.Cocone.ext (Iso.refl _) fun s => ?_)
  simp [Functor.derivedUnitCocone_ι_app, derivedHomReflectorForgetUnit]

end CochainComplex

end
