module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedHomPhiConcrete
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.YonedaInverseImageAcyclic
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexComparisonTriangulated
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexCompShift

/-!
# The identification `(*)` of Tag 09LK, indexed by the ordinary homotopy category

`DGCategory.derivedHomPhi` is a bijection

`H^n(U(R̃(q y))) ≃ Hom_{DA}(q x, (q y)⟦n⟧)`

indexed by objects `y` of `K(C)` for `C` a differential graded category and `q : K(C) ⥤ DA` a
localization of `K(C)` at `Z = Φ⁻¹ N`. Step 3 of the replacement proof of [Stacks, Tag 09LK]
(`CochainComplex.DerivedHomLiftIdentification`) asks instead for a family indexed by the objects
`X` of the *ordinary* homotopy category `K(A)` of complexes, with target
`Hom_{D(A)}(Q K, (Q X)⟦n⟧)` for `Q = ` `DerivedCategory.Qh`.

This file carries `φ` across that reindexing. Nothing mathematical happens here: taking
`C = Comp^dg(A)` and `q = Φ'⁻¹ ⋙ Q` for `Φ'` the comparison equivalence
`CochainComplex.homotopyCategoryEquivalence` of the two homotopy categories, the two families
differ by the unit of that equivalence, and the transport is conjugation by its `Q`-image on the
target and by its `R̃`-image on the source.

## What is assumed

Less than `DGCategory.derivedHomPhi` assumes: its binder

`[(Φ'⁻¹ ⋙ Q).IsLocalization (yonedaInverseImage (Comp^dg A) G).trW]`

is *discharged* here rather than carried. Its content is the identification of `Φ⁻¹ N` with the
acyclic complexes, and the generator family is accordingly taken to be the canonical enumeration
`DGCategory.phiGen` of those, at which
`DGCategory.RightModule.yonedaInverseImage_dgCategoryKAcyclicEnum` gives the identification and
`DGCategory.RightModule.comparisonInverse_comp_isLocalization_yonedaInverseImage` turns it into
the instance. Both rest on the resolution-free
`DGCategory.RightModule.yonedaInverseImage_eq_of_isTriangulated` and on the unconditional
thickness of the acyclic complexes, so neither costs a hypothesis on `A`.

What is left is the exactness of the differential graded Yoneda functor, carried as the two
instance binders on `((yonedaDGFunctor (Comp^dg A)).onK)`, which is where steps 1 and 2 leave
it; with `A` abelian, those two are the whole of what the statements below assume.

## Main definitions

* `DGCategory.phiComparisonLocalization`: the localization `q = Φ'⁻¹ ⋙ Q` of `K(Comp^dg(A))` the
  transport runs against.
* `DGCategory.phiGen`: the generator family it runs at, the canonical enumeration of the acyclic
  complexes, which is what makes `q` a localization at `Z = Φ⁻¹ N`.
* `DGCategory.phiReflector`: the `R̃ : D(A) ⥤ D(C(K, K))` of
  `DGCategory.derivedHomPhi` at that `q`, which is the `R̃` step 3 receives.
* `DGCategory.phiUnitIso` and `DGCategory.phiSourceIso`: the two comparisons the transport
  conjugates by — at a general `X`, and at the complex `K` itself, where the comparison
  equivalence's identity on objects (`CochainComplex.homotopyCategoryEquivalence_obj`) enters.
* `DGCategory.derivedHomPhiQh`: **the transported `φ`**, in exactly the shape
  `CochainComplex.derivedHomLiftIdentificationOfCovariantNaturality` consumes.

## Main results

* `DGCategory.derivedHomPhiQh_injective`: injectivity, again `Equiv.injective` of a composite of
  bijections and not a hypothesis.
* `DGCategory.derivedHomPhiQh_covariant`: **the covariant square**, for every morphism
  `s : X ⟶ Y` of `K(A)`. The transport of
  `DGCategory.derivedHomPhi_covariant` along the unit of the comparison equivalence, whose
  naturality is the only fact used.
* `DGCategory.exists_derivedHomPhiQh`: the three together, with steps 1 and 2 invoked once
  through `DGCategory.exists_derivedHomReflector_data`.

## What is still owed

The clause `unit_app_id` of
`CochainComplex.derivedHomLiftIdentificationOfCovariantNaturality` — the elementwise statement
that `φ`, on the `β`-image of a degree-`n` cohomology class of `Hom^•(K, Y)`, is `Q` of the
morphism that Tag 09LC's identification assigns to that class. It is not here, and it is the one
place where the mathematics of the replacement proof still has to be done.

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK);
  [Tag 09L9](https://stacks.math.columbia.edu/tag/09L9), the comparison of the two homotopy
  categories.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Pretriangulated CategoryTheory.ObjectProperty

namespace DGCategory

universe w v

variable (A : Type) [Category.{0} A] [Abelian A] [HasDerivedCategory.{v} A]

/-- **The localization the transport runs against.** The comparison equivalence of the two
homotopy categories, inverted, followed by the localization `Q : K(A) ⥤ D(A)`: a functor
`K(Comp^dg(A)) ⥤ D(A)` out of the differential graded homotopy category, which is the shape
`DGCategory.derivedHomPhi` asks its target localization to have. -/
abbrev phiComparisonLocalization : (CochainComplex.dgCategory A).K ⥤ DerivedCategory A :=
  (CochainComplex.homotopyCategoryEquivalence A).inverse ⋙ DerivedCategory.Qh

/-- **The generator family the transport runs against**: the tautological enumeration
`CochainComplex.dgCategoryKAcyclicEnum` of the acyclic complexes, indexed by the subtype they
form.

Step 1 of [Stacks, Tag 09LK] takes the generators of `N` from an enumeration of the acyclic
complexes, and taking the canonical such enumeration is what makes the chain's localization
hypothesis hold outright, by
`DGCategory.RightModule.comparisonInverse_comp_isLocalization_yonedaInverseImage`. -/
abbrev phiGen : Subtype (CochainComplex.dgCategoryKAcyclic A) →
    (CochainComplex.dgCategory A).Obj :=
  CochainComplex.dgCategoryKAcyclicEnum A

variable (K : CochainComplex A ℤ) [HasDerivedCategory.{w} (ModuleCat.{0} ℤ)]
  [((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).CommShift ℤ]
  [((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).IsTriangulated]
  (L : (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K ⥤
    (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K)
  [L.CommShift ℤ] [L.IsTriangulated]
  {η : 𝟭 (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K ⟶ L}

attribute [local implicit_reducible] DGCategory.K

/-- **The comparison at a general object.** For `X` an object of `K(A)` the unit of the
comparison equivalence identifies `Q X` with `q (Φ' X)`, which is the object
`DGCategory.derivedHomPhi` is indexed by. -/
def phiUnitIso (X : HomotopyCategory A (ComplexShape.up ℤ)) :
    DerivedCategory.Qh.obj X ≅
      (phiComparisonLocalization A).obj
        ((CochainComplex.homotopyCategoryEquivalence A).functor.obj X) :=
  DerivedCategory.Qh.mapIso ((CochainComplex.homotopyCategoryEquivalence A).unitIso.app X)

/-- **The comparison at the complex `K`.** The source of step 3's `φ` is `Q` of the image of `K`
in `K(A)`, while `DGCategory.derivedHomPhi` is a map into a Hom group out of `q K` for `K` read
as an object of `K(Comp^dg(A))`. The two are identified by the unit of the comparison
equivalence together with its being the identity on complexes,
`CochainComplex.homotopyCategoryEquivalence_obj`. -/
def phiSourceIso :
    DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≅
      (phiComparisonLocalization A).obj (K : (CochainComplex.dgCategory A).K) :=
  phiUnitIso A ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ≪≫
    DerivedCategory.Qh.mapIso
      ((CochainComplex.homotopyCategoryEquivalence A).inverse.mapIso
        (eqToIso (CochainComplex.homotopyCategoryEquivalence_obj A K)))

/-- **The `R̃ : D(A) ⥤ D(C(K, K))` the transported `φ` is a map out of.** This is
`DGCategory.derivedHomReflector` at the differential graded Yoneda functor, the subcategory
`Z = Φ⁻¹ N` and the localization `DGCategory.phiComparisonLocalization`. -/
abbrev phiReflector
    (hΦ : ∀ X, RightModule.yonedaInverseImage (CochainComplex.dgCategory A) (phiGen A) X →
      IsZero (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK ⋙ L).obj X)) :
    DerivedCategory A ⥤
      RightModule.derivedCategory (endDGCategory (CochainComplex.dgCategory A) K) :=
  derivedHomReflector (CochainComplex.dgCategory A) K L
    ((yonedaDGFunctor (CochainComplex.dgCategory A)).onK)
    (RightModule.yonedaInverseImage (CochainComplex.dgCategory A) (phiGen A))
    (phiComparisonLocalization A) hΦ

/-- `R̃ ⋙ U`, the functor whose values' homology the transported `(*)` is a map out of. -/
abbrev phiReflectorForget
    (hΦ : ∀ X, RightModule.yonedaInverseImage (CochainComplex.dgCategory A) (phiGen A) X →
      IsZero (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK ⋙ L).obj X)) :
    DerivedCategory A ⥤ DerivedCategory (ModuleCat.{0} ℤ) :=
  phiReflector A K L hΦ ⋙ endDerivedForget (CochainComplex.dgCategory A) K

section Transport

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

/-- **The identification `(*)` of [Stacks, Tag 09LK], indexed by `K(A)`.** The composite
`DGCategory.derivedHomPhi` at the object `Φ' X`, conjugated by the unit of the comparison
equivalence on both sides: on the source by its `R̃ ⋙ U`-image, on the target by its `Q`-image.

This is exactly the shape of the `φ` clause of
`CochainComplex.derivedHomLiftIdentificationOfCovariantNaturality`, at `U` the forgetful functor
`DGCategory.endDerivedForget` out of `D(C(K, K))` and `R̃` the `DGCategory.phiReflector`. -/
def derivedHomPhiQh (X : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ) :
    ↥((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
        ((phiReflectorForget A K L hΦ).obj (DerivedCategory.Qh.obj X))) ≃
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⟶
        (DerivedCategory.Qh.obj X)⟦n⟧) :=
  (((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).mapIso
        ((phiReflectorForget A K L hΦ).mapIso
          (phiUnitIso A X))).toLinearEquiv.toEquiv.trans
    (derivedHomPhi (CochainComplex.dgCategory A) (phiGen A) L (phiComparisonLocalization A) hL hη hΦ
      (K : (CochainComplex.dgCategory A).K)
      ((CochainComplex.homotopyCategoryEquivalence A).functor.obj X) PUnit.unit n)).trans
    (Iso.homCongr (phiSourceIso A K).symm
      ((shiftFunctor (DerivedCategory A) n).mapIso (phiUnitIso A X)).symm)

/-- The transported `(*)`, written out: the junction and chain at `Φ' X`, conjugated by the
`Q`-image of the unit of the comparison equivalence. -/
theorem derivedHomPhiQh_apply (X : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ)
    (z : ↥((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
      ((phiReflectorForget A K L hΦ).obj (DerivedCategory.Qh.obj X)))) :
    derivedHomPhiQh A K L hL hη hΦ X n z =
      (phiSourceIso A K).hom ≫
        derivedHomPhi (CochainComplex.dgCategory A) (phiGen A) L
            (phiComparisonLocalization A) hL hη hΦ
            (K : (CochainComplex.dgCategory A).K)
            ((CochainComplex.homotopyCategoryEquivalence A).functor.obj X) PUnit.unit n
          ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
            ((phiReflectorForget A K L hΦ).map (phiUnitIso A X).hom) z) ≫
        (shiftFunctor (DerivedCategory A) n).map (phiUnitIso A X).inv := rfl

/-- **The transported `(*)` is injective.** It is a composite of bijections. -/
theorem derivedHomPhiQh_injective (X : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ) :
    Function.Injective (derivedHomPhiQh A K L hL hη hΦ X n) :=
  (derivedHomPhiQh A K L hL hη hΦ X n).injective

/-- **The covariant naturality square of the transported `(*)`.** For every morphism
`s : X ⟶ Y` of `K(A)`,

`φ Y n (H^n(U(R̃(Q s))) z) = φ X n z ≫ (Q s)⟦n⟧`.

This is `DGCategory.derivedHomPhi_covariant` at the morphism `Φ' s`, transported along the unit
of the comparison equivalence; the only fact used is the naturality of that unit, so no
quasi-isomorphism hypothesis on `s` appears, and the inverse-transition clause of
`CochainComplex.derivedHomLiftIdentificationOfCovariantNaturality` follows from this by
substituting `z = H^n(U(R̃(Q s)))⁻¹ w` there. -/
theorem derivedHomPhiQh_covariant {X Y : HomotopyCategory A (ComplexShape.up ℤ)} (s : X ⟶ Y)
    (n : ℤ)
    (z : ↥((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
      ((phiReflectorForget A K L hΦ).obj (DerivedCategory.Qh.obj X)))) :
    derivedHomPhiQh A K L hL hη hΦ Y n
        ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((phiReflectorForget A K L hΦ).map (DerivedCategory.Qh.map s)) z) =
      derivedHomPhiQh A K L hL hη hΦ X n z ≫ (DerivedCategory.Qh.map s)⟦n⟧' := by
  have hu : (phiUnitIso A X).hom ≫ (phiComparisonLocalization A).map
        ((CochainComplex.homotopyCategoryEquivalence A).functor.map s) =
      DerivedCategory.Qh.map s ≫ (phiUnitIso A Y).hom := by
    rw [phiUnitIso, phiUnitIso, Functor.mapIso_hom, Functor.mapIso_hom, Functor.comp_map,
      ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg DerivedCategory.Qh.map
      ((CochainComplex.homotopyCategoryEquivalence A).unitIso.hom.naturality s).symm
  have hinv : (phiComparisonLocalization A).map
        ((CochainComplex.homotopyCategoryEquivalence A).functor.map s) ≫
      (phiUnitIso A Y).inv = (phiUnitIso A X).inv ≫ DerivedCategory.Qh.map s := by
    rw [Iso.comp_inv_eq, Category.assoc, ← hu, Iso.inv_hom_id_assoc]
  have h1 : (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((phiReflectorForget A K L hΦ).map (phiUnitIso A Y).hom)
          ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
            ((phiReflectorForget A K L hΦ).map (DerivedCategory.Qh.map s)) z) =
      (DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
        ((phiReflectorForget A K L hΦ).map ((phiComparisonLocalization A).map
          ((CochainComplex.homotopyCategoryEquivalence A).functor.map s)))
        ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
          ((phiReflectorForget A K L hΦ).map (phiUnitIso A X).hom) z) := by
    rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← Functor.map_comp, ← Functor.map_comp,
      ← Functor.map_comp, ← Functor.map_comp, hu]
  rw [derivedHomPhiQh_apply, derivedHomPhiQh_apply]
  refine Eq.trans (congrArg (fun g ↦ (phiSourceIso A K).hom ≫ g ≫
      (shiftFunctor (DerivedCategory A) n).map (phiUnitIso A Y).inv)
    ((congrArg (fun c ↦ derivedHomPhi (CochainComplex.dgCategory A) (phiGen A) L
          (phiComparisonLocalization A) hL hη hΦ (K : (CochainComplex.dgCategory A).K)
          ((CochainComplex.homotopyCategoryEquivalence A).functor.obj Y) PUnit.unit n c)
        h1).trans
      (derivedHomPhi_covariant (CochainComplex.dgCategory A) (phiGen A) L
        (phiComparisonLocalization A)
        hL hη hΦ (K : (CochainComplex.dgCategory A).K)
        ((CochainComplex.homotopyCategoryEquivalence A).functor.map s) PUnit.unit n _))) ?_
  rw [Category.assoc, ← Functor.map_comp, hinv, Functor.map_comp]
  simp only [Category.assoc]

end Transport

/-- **The transported `(*)` at one reflector, with the reflector's data kept.** Steps 1 and 2 of
[Stacks, Tag 09LK] are invoked once, through `DGCategory.exists_derivedHomReflector_data`, and
the junction, the chain, the transport and the covariant square are all taken at those same `L`,
`η`, `hL`, `hη` and `hΦ`. The existential's hypothesis is discharged by `fun _ h ↦ h`: an object
of `Z = Φ⁻¹ N` is by definition one whose representable lies in `N`.

The three conclusions are exactly the `φ`, `injective` and `covariant` clauses of
`CochainComplex.derivedHomLiftIdentificationOfCovariantNaturality` at
`U = DGCategory.endDerivedForget (Comp^dg A) K` and `R̃ = DGCategory.phiReflector`; injectivity is
not listed because `φ` is produced as a bijection. -/
theorem exists_derivedHomPhiQh :
    ∃ (L' : (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K ⥤
        (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K)
      (_ : L'.CommShift ℤ) (_ : L'.IsTriangulated)
      (hΦ : ∀ X, RightModule.yonedaInverseImage (CochainComplex.dgCategory A) (phiGen A) X →
        IsZero (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK ⋙ L').obj X))
      (φ : ∀ (X : HomotopyCategory A (ComplexShape.up ℤ)) (n : ℤ),
        ↥((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).obj
            ((phiReflectorForget A K L' hΦ).obj (DerivedCategory.Qh.obj X))) ≃
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K) ⟶
            (DerivedCategory.Qh.obj X)⟦n⟧)),
      ∀ (X Y : HomotopyCategory A (ComplexShape.up ℤ)) (s : X ⟶ Y) (n : ℤ) (z),
        φ Y n ((DerivedCategory.homologyFunctor (ModuleCat.{0} ℤ) n).map
            ((phiReflectorForget A K L' hΦ).map (DerivedCategory.Qh.map s)) z) =
          φ X n z ≫ (DerivedCategory.Qh.map s)⟦n⟧' := by
  obtain ⟨L', cs, tri, η, hL, hη, hΦ⟩ :=
    exists_derivedHomReflector_data (CochainComplex.dgCategory A) (phiGen A)
      ((yonedaDGFunctor (CochainComplex.dgCategory A)).onK)
      (RightModule.yonedaInverseImage (CochainComplex.dgCategory A) (phiGen A)) fun _ h ↦ h
  exact ⟨L', cs, tri, hΦ, fun X n ↦ derivedHomPhiQh A K L' hL hη hΦ X n,
    fun _ _ s n z ↦ derivedHomPhiQh_covariant A K L' hL hη hΦ s n z⟩

end DGCategory

end
