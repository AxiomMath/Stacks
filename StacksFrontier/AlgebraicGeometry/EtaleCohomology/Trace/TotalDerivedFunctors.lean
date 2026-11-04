module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.BoundedBelowInjectiveEquivalence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.MorphismsFromBoundedAboveProjectives
import StacksCore.Tactic.StacksAttribute

/-!
# Total derived functors

Let `F : A ⥤ B` be an additive functor between abelian categories. If `A` has enough
injectives, the total right derived functor of `F` is a functor `RF : D⁺(A) ⥤ D⁺(B)`
constructed from injective resolutions: writing `K⁺(I)` for the full subcategory of the
homotopy category `K(A)` on the bounded below complexes of injective objects, the
localization functor restricts to an equivalence `K⁺(I) ≌ D⁺(A)`, and `RF` is the composite
of a chosen inverse of that equivalence with "apply `F` termwise, then localize". Dually, if
`A` has enough projectives, the total left derived functor of `G : A ⥤ B` is a functor
`LG : D⁻(A) ⥤ D⁻(B)`, built the same way out of the bounded above complexes of projectives
`K⁻(Proj A)`.

The equivalence `K⁻(Proj A) ≌ D⁻(A)` is part (4) of [Stacks, Tag 03T6]. Fully faithfulness is
part (2) of that tag — morphisms out of a bounded above complex of projectives do not change
on passing from `K(A)` to `D(A)` — which is
`CochainComplex.Qh_map_bijective_of_projective_of_minus`; essential surjectivity is
the existence of bounded above projective resolutions, `ProjectiveResolutionLemma.statement3`.
The injective equivalence `K⁺(I) ≌ D⁺(A)`, part (3) of the same tag, is
`CategoryTheory.HomotopyCategory.PlusInjective.isEquivalence_toDerivedPlus`, imported from
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.BoundedBelowInjectiveEquivalence`.

## Main definitions

* `CategoryTheory.HomotopyCategory.minusProjective`: the property of an object of the
  homotopy category of being bounded above with projective terms.
* `CategoryTheory.HomotopyCategory.MinusProjective`: the category `K⁻(Proj A)` cut out by
  that property.
* `CategoryTheory.HomotopyCategory.MinusProjective.toDerivedMinus`: the canonical functor
  `K⁻(Proj A) ⥤ D⁻(A)`.
* `CategoryTheory.HomotopyCategory.PlusInjective.toHomotopyPlus`: the inclusion
  `K⁺(I) ⥤ K⁺(A)`.
* `CategoryTheory.Functor.mapMinusProjectiveToDerivedMinus`: the lower route in the diagram
  defining the total left derived functor — apply the functor termwise to a bounded above
  complex of projectives, then pass to `D⁻(B)`.
* `CategoryTheory.Functor.leftDerivedFunctorMinus`: the total left derived functor
  `D⁻(A) ⥤ D⁻(B)`.
* `CategoryTheory.Functor.leftDerivedFunctorMinusIso`: the natural isomorphism expressing
  that the diagram defining the total left derived functor commutes.
* `CategoryTheory.Functor.mapPlusInjectiveToDerivedPlus`: the lower route in the diagram
  defining the total right derived functor — apply the functor termwise to a bounded below
  complex of injectives, then pass to `D⁺(B)`.
* `CategoryTheory.Functor.rightDerivedFunctorPlusOfInjectives`: the total right derived
  functor `D⁺(A) ⥤ D⁺(B)`.
* `CategoryTheory.Functor.rightDerivedFunctorPlusOfInjectivesIso`: the natural isomorphism
  expressing that the diagram defining the total right derived functor commutes.

## Main results

* `CategoryTheory.HomotopyCategory.MinusProjective.isEquivalence_toDerivedMinus`
  ([Stacks, Tag 03T6] part (4)): the canonical functor `K⁻(Proj A) ⥤ D⁻(A)` is an equivalence
  when `A` has enough projectives.
* `CategoryTheory.Functor.rightDerivedFunctorPlusOfInjectivesIsoRightDerivedFunctorPlus`:
  the total right derived functor built from `K⁺(I)` is isomorphic to Mathlib's abstract
  right derived functor `CategoryTheory.Functor.rightDerivedFunctorPlus`.

## Implementation notes

Both constructions use only additivity of the functor, so they are stated for an additive
functor; the left exact and right exact functors of the source are the special cases. The
`HasDerivedCategory` hypotheses are the universe-sensitive existence assumptions for
Mathlib's chosen derived categories, and the two categories are allowed independent such
choices.

`leftDerivedFunctorMinus` and `rightDerivedFunctorPlusOfInjectives` are built from
`Functor.inv`, i.e. from an arbitrary chosen inverse of the relevant equivalence of Tag 03T6,
so each is only well defined up to the isomorphisms `leftDerivedFunctorMinusIso` and
`rightDerivedFunctorPlusOfInjectivesIso`; such an isomorphism, not an equality, is what the
source's diagram asserts.

## References

* [Stacks Project, Tag 03T7](https://stacks.math.columbia.edu/tag/03T7)
* [Stacks Project, Tag 03T6](https://stacks.math.columbia.edu/tag/03T6)
-/

@[expose] public noncomputable section

namespace CategoryTheory

universe w v u

namespace HomotopyCategory

variable (A : Type u) [Category.{v} A] [Abelian A]

/-- The property of an object of the homotopy category of cochain complexes that it is
strictly bounded above and all its terms are projective. -/
def minusProjective : ObjectProperty (HomotopyCategory A (.up ℤ)) :=
  fun K ↦ (∃ n : ℤ, CochainComplex.IsStrictlyLE K.as n) ∧ ∀ i : ℤ, Projective (K.as.X i)

/-- The category `K⁻(Proj A)` of bounded above complexes of projective objects up to
homotopy. -/
abbrev MinusProjective := (minusProjective A).FullSubcategory

namespace MinusProjective

variable [HasDerivedCategory.{w} A]

/-- The canonical functor `K⁻(Proj A) ⥤ D⁻(A)`, the restriction of the localization
functor. -/
def toDerivedMinus : MinusProjective A ⥤ DerivedCategory.Minus A :=
  ObjectProperty.lift DerivedCategory.TStructure.t.minus
    ((minusProjective A).ι ⋙ DerivedCategory.Qh) (by
      rintro ⟨K, ⟨n, hn⟩, _⟩
      refine ⟨n, K.as, (DerivedCategory.quotientCompQhIso A).app K.as, ?_⟩
      let _ := hn
      infer_instance)

@[sga "4½ Rapport 4.3" "more general",
  sga "6 I 4.10" "Clause (i), special case",
  sga "6 I 4.12.2" "special case",
  sga "6 II 1.1" "c), special case"]
private lemma nonempty_fullyFaithful_toDerivedMinus [EnoughProjectives A] :
    Nonempty ((toDerivedMinus A ⋙ DerivedCategory.Minus.ι).FullyFaithful) := by
  change Nonempty (((minusProjective A).ι ⋙ DerivedCategory.Qh).FullyFaithful)
  rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
  rintro ⟨X, hX⟩ ⟨Y, hY⟩
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  obtain ⟨Q, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  obtain ⟨n, hn⟩ := hX.1
  let _ : ∀ n, Projective (P.X n) := hX.2
  exact (CochainComplex.Qh_map_bijective_of_projective_of_minus P _ ⟨n, hn⟩).comp
    (((minusProjective A).fullyFaithfulι).map_bijective _ _)

private lemma essSurj_toDerivedMinus [EnoughProjectives A] :
    (toDerivedMinus A).EssSurj := by
  refine ⟨fun Y ↦ ?_⟩
  obtain ⟨n, hn⟩ := Y.property
  obtain ⟨K, hK, ⟨e⟩⟩ := Y.obj.exists_iso_Q_obj_of_isLE n
  obtain ⟨R⟩ := ProjectiveResolutionLemma.statement3 n K hK
  have : IsIso (DerivedCategory.Q.map R.α) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso A R.α).mpr R.quasiIso
  exact ⟨⟨(HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj R.complex,
    ⟨⟨n, R.boundedAbove⟩, R.projective⟩⟩,
    ⟨(DerivedCategory.TStructure.t.minus).fullyFaithfulι.preimageIso
      ((DerivedCategory.quotientCompQhIso A).app R.complex ≪≫
        asIso (DerivedCategory.Q.map R.α) ≪≫ e.symm)⟩⟩

/-- **Stacks 03T6, part (4).** If `A` has enough projectives and `P ⊆ A` is the additive
subcategory of projectives, then `D⁻(A) ≅ K⁻(P)`: the canonical functor from the bounded above
homotopy category of complexes of projective objects to the bounded above derived category is
an equivalence. -/
@[stacks 03T6 "projective_equivalence", sga "4½ Etat_0 3.2.3" "(4) proj. analogue"]
theorem isEquivalence_toDerivedMinus [EnoughProjectives A] :
    (toDerivedMinus A).IsEquivalence := by
  let hff := (Classical.choice (nonempty_fullyFaithful_toDerivedMinus A)).ofCompFaithful
  exact ⟨hff.faithful, hff.full, essSurj_toDerivedMinus A⟩

end MinusProjective

namespace PlusInjective

/-- The inclusion `K⁺(I) ⥤ K⁺(A)` of the bounded below complexes of injectives into the
bounded below homotopy category. -/
def toHomotopyPlus : PlusInjective A ⥤ HomotopyCategory.Plus A :=
  ObjectProperty.lift (HomotopyCategory.plus A) (plusInjective A).ι (by
    rintro ⟨X, ⟨n, hn⟩, _⟩
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    exact ⟨K, ⟨n, hn⟩⟩)

/-- Each term of the image of an object of `K⁺(I)` in `K⁺(A)` is injective. -/
instance (X : PlusInjective A) (n : ℤ) :
    Injective (((toHomotopyPlus A).obj X).obj.as.X n) :=
  X.property.2 n

end PlusInjective

end HomotopyCategory

namespace Functor

universe wB vB uB

variable {A : Type u} {B : Type uB} [Category.{v} A] [Category.{vB} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} A] [HasDerivedCategory.{wB} B]

/-- The lower route in the diagram defining the total left derived functor: apply the
additive functor termwise to a bounded above complex of projectives, then pass to the
bounded above derived category. -/
@[implicit_reducible, stacks 03T7 "the projective-complex route for the left derived functor"]
def mapMinusProjectiveToDerivedMinus (G : A ⥤ B) [G.Additive] :
    HomotopyCategory.MinusProjective A ⥤ DerivedCategory.Minus B :=
  ObjectProperty.lift DerivedCategory.TStructure.t.minus
    ((HomotopyCategory.minusProjective A).ι ⋙ G.mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh) (by
      rintro ⟨K, ⟨n, hn⟩, _⟩
      refine ⟨n, (G.mapHomologicalComplex (.up ℤ)).obj K.as,
        (DerivedCategory.quotientCompQhIso B).app _, ?_⟩
      rw [CochainComplex.isStrictlyLE_iff] at hn ⊢
      intro i hi
      exact G.map_isZero (hn i hi))

/-- The total left derived functor on the bounded above derived category, constructed using
bounded above complexes of projective objects. -/
@[implicit_reducible,
  stacks 03T7 "the total left derived functor",
  sga "4½ Etat_0 4.1.2" "left derived functor",
  sga "4½ Etat_0 4.1.4" "LF",
  sga "4½ Etat_0 4.1.5" "L^- f",
  sga "4 XVII 1.2.5" "(ii), single functor",
  sga "4½ Etat_0 4.1.3" "L⁻ f"]
def leftDerivedFunctorMinus (G : A ⥤ B) [G.Additive] [EnoughProjectives A] :
    DerivedCategory.Minus A ⥤ DerivedCategory.Minus B := by
  let : (HomotopyCategory.MinusProjective.toDerivedMinus A).IsEquivalence :=
    HomotopyCategory.MinusProjective.isEquivalence_toDerivedMinus A
  exact (HomotopyCategory.MinusProjective.toDerivedMinus A).inv ⋙
    mapMinusProjectiveToDerivedMinus G

/-- The natural commuting isomorphism in the projective-resolution diagram defining the total
left derived functor. -/
@[stacks 03T7 "the comparison isomorphism for the total left derived functor"]
def leftDerivedFunctorMinusIso (G : A ⥤ B) [G.Additive] [EnoughProjectives A] :
    HomotopyCategory.MinusProjective.toDerivedMinus A ⋙ leftDerivedFunctorMinus G ≅
      mapMinusProjectiveToDerivedMinus G := by
  let : (HomotopyCategory.MinusProjective.toDerivedMinus A).IsEquivalence :=
    HomotopyCategory.MinusProjective.isEquivalence_toDerivedMinus A
  exact Functor.isoWhiskerRight
    (HomotopyCategory.MinusProjective.toDerivedMinus A).asEquivalence.unitIso.symm
    (mapMinusProjectiveToDerivedMinus G)

/-- The lower route in the diagram defining the total right derived functor: apply the
additive functor termwise to a bounded below complex of injectives, then pass to the
bounded below derived category. -/
@[implicit_reducible, stacks 03T7 "the injective-complex route for the right derived functor"]
def mapPlusInjectiveToDerivedPlus (F : A ⥤ B) [F.Additive] :
    HomotopyCategory.PlusInjective A ⥤ DerivedCategory.Plus B :=
  ObjectProperty.lift DerivedCategory.TStructure.t.plus
    ((HomotopyCategory.plusInjective A).ι ⋙ F.mapHomotopyCategory (.up ℤ) ⋙
      DerivedCategory.Qh) (by
      rintro ⟨K, ⟨n, hn⟩, _⟩
      refine ⟨n, (F.mapHomologicalComplex (.up ℤ)).obj K.as,
        (DerivedCategory.quotientCompQhIso B).app _, ?_⟩
      rw [CochainComplex.isStrictlyGE_iff] at hn ⊢
      intro i hi
      exact F.map_isZero (hn i hi))

/-- The total right derived functor on the bounded below derived category, constructed using
bounded below complexes of injective objects. -/
@[implicit_reducible,
  stacks 03T7 "the total right derived functor",
  sga "4½ Etat_0 4.1.2" "right derived functor",
  sga "4½ Etat_0 4.1.4" "RF",
  sga "4 XVII 1.2.5" "(ii), single functor"]
def rightDerivedFunctorPlusOfInjectives (F : A ⥤ B) [F.Additive] [EnoughInjectives A] :
    DerivedCategory.Plus A ⥤ DerivedCategory.Plus B := by
  let : (HomotopyCategory.PlusInjective.toDerivedPlus A).IsEquivalence :=
    HomotopyCategory.PlusInjective.isEquivalence_toDerivedPlus A
  exact (HomotopyCategory.PlusInjective.toDerivedPlus A).inv ⋙
    mapPlusInjectiveToDerivedPlus F

/-- The natural commuting isomorphism in the injective-resolution diagram defining the total
right derived functor. -/
@[stacks 03T7 "the comparison isomorphism for the total right derived functor"]
def rightDerivedFunctorPlusOfInjectivesIso (F : A ⥤ B) [F.Additive] [EnoughInjectives A] :
    HomotopyCategory.PlusInjective.toDerivedPlus A ⋙ rightDerivedFunctorPlusOfInjectives F ≅
      mapPlusInjectiveToDerivedPlus F := by
  let : (HomotopyCategory.PlusInjective.toDerivedPlus A).IsEquivalence :=
    HomotopyCategory.PlusInjective.isEquivalence_toDerivedPlus A
  exact Functor.isoWhiskerRight
    (HomotopyCategory.PlusInjective.toDerivedPlus A).asEquivalence.unitIso.symm
    (mapPlusInjectiveToDerivedPlus F)

/-- On a bounded below complex of injectives the canonical map into Mathlib's abstract right
derived functor is invertible, so that functor also fits in the defining diagram. -/
def rightDerivedFunctorPlusIsoOnPlusInjective (F : A ⥤ B) [F.Additive] [EnoughInjectives A] :
    HomotopyCategory.PlusInjective.toDerivedPlus A ⋙ F.rightDerivedFunctorPlus ≅
      mapPlusInjectiveToDerivedPlus F := by
  let : ∀ X : HomotopyCategory.PlusInjective A,
      IsIso ((Functor.whiskerLeft (HomotopyCategory.PlusInjective.toHomotopyPlus A)
        F.rightDerivedFunctorPlusUnit).app X) := fun X ↦
    inferInstanceAs (IsIso (F.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.PlusInjective.toHomotopyPlus A).obj X)))
  let := NatIso.isIso_of_isIso_app (Functor.whiskerLeft
    (HomotopyCategory.PlusInjective.toHomotopyPlus A) F.rightDerivedFunctorPlusUnit)
  exact (asIso (Functor.whiskerLeft (HomotopyCategory.PlusInjective.toHomotopyPlus A)
    F.rightDerivedFunctorPlusUnit)).symm

/-- The total right derived functor built from `K⁺(I)` agrees with the abstract right derived
functor of the localization: both fit in the diagram of [Stacks, Tag 03T7]. -/
def rightDerivedFunctorPlusOfInjectivesIsoRightDerivedFunctorPlus
    (F : A ⥤ B) [F.Additive] [EnoughInjectives A] :
    rightDerivedFunctorPlusOfInjectives F ≅ F.rightDerivedFunctorPlus := by
  let : (HomotopyCategory.PlusInjective.toDerivedPlus A).IsEquivalence :=
    HomotopyCategory.PlusInjective.isEquivalence_toDerivedPlus A
  exact Functor.isoWhiskerLeft (HomotopyCategory.PlusInjective.toDerivedPlus A).inv
    (rightDerivedFunctorPlusIsoOnPlusInjective F).symm ≪≫
    (HomotopyCategory.PlusInjective.toDerivedPlus A).asEquivalence.invFunIdAssoc _

/-- The comparison map for the total right derived functor: the natural transformation from
"apply `F` termwise, then localize" to the composite of the localization functor with
`RF`. -/
@[stacks 03T7 "the comparison map for the total right derived functor"]
def rightDerivedFunctorPlusOfInjectivesUnit (F : A ⥤ B) [F.Additive] [EnoughInjectives A] :
    F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ rightDerivedFunctorPlusOfInjectives F :=
  F.rightDerivedFunctorPlusUnit ≫ whiskerLeft DerivedCategory.Plus.Qh
    (rightDerivedFunctorPlusOfInjectivesIsoRightDerivedFunctorPlus F).inv

/-- The total right derived functor, with its comparison map, is a right derived functor of
"apply `F` termwise, then localize": a left Kan extension along the localization functor
`K⁺(A) ⥤ D⁺(A)`. -/
instance (F : A ⥤ B) [F.Additive] [EnoughInjectives A] :
    (rightDerivedFunctorPlusOfInjectives F).IsRightDerivedFunctor
      (rightDerivedFunctorPlusOfInjectivesUnit F) (HomotopyCategory.Plus.quasiIso A) :=
  (isRightDerivedFunctor_iff_of_iso F.rightDerivedFunctorPlusUnit _
    (HomotopyCategory.Plus.quasiIso A)
    (rightDerivedFunctorPlusOfInjectivesIsoRightDerivedFunctorPlus F).symm rfl).1
    inferInstance

end Functor

end CategoryTheory
