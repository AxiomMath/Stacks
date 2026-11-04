module

public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncationLevelHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.TruncGELTSingle

/-! # The edge transformation `H^i ∘ Rw ⟶ w ∘ H^i` of a right derived functor

Let `A` and `B` be abelian categories with unbounded derived categories, let `w : A ⥤ B` and let
`Rw : D(A) ⥤ D(B)` be a right derived functor of `w`, carried as a triangulated functor. For every
degree `i` there is a canonical comparison

`H^i(Rw Z) ⟶ w(H^i Z)`

natural in `Z`, which is an isomorphism when `Z` has no cohomology below degree `i`. This file
constructs it, as `Stacks.DerivedFunctor.homologyEdge`.

The construction is the one the source uses: the truncation map `Z ⟶ τ_{≥ i}Z` is inverted by
`H^i`, so the whole content sits over `τ_{≥ i}Z`, where `Z` is replaced by its one-step interval
truncation `τ_{[i,i]}Z = τ_{< i+1}τ_{≥ i}Z`, an object concentrated in degree `i`. Concretely the
comparison is the composite

`H^i(Rw Z) ⟶ H^i(Rw τ_{≥ i}Z) ≅ H^i(Rw τ_{[i,i]}Z) ≅ w(H^i τ_{[i,i]}Z) ≅ w(H^i τ_{≥ i}Z)
  ≅ w(H^i Z)`

of which only the first map is not invertible. The second is invertible because `Rw` is left
t-exact, the third is the hypothesis, and the last two are the two truncation maps read by `H^i`
in a degree the truncation retains.

Two things are taken as hypotheses rather than built, because neither is a formal consequence of
`Rw` being a right derived functor:

* **left t-exactness** of `Rw`, in the form `∀ Z n, Z.IsGE n → (Rw.obj Z).IsGE n`. For the
  unbounded right derived functor of an additive functor out of a Grothendieck abelian category
  with enough injectives this is
  `Stacks.DerivedFunctor.isGE_totalRightDerived_obj`.
* the **degree-`i` agreement on single objects**,
  `singleFunctor A i ⋙ Rw ⋙ homologyFunctor B i ≅ w`, i.e. `R⁰w ≅ w`. This is exactly where left
  exactness of `w` enters, and it is false for a merely additive `w`.

Both are supplied as data, never chosen: no `Nonempty`-wrapped isomorphism appears on the
construction path, since an arbitrarily chosen isomorphism satisfies no naturality square.

## Main definitions

* `Stacks.DerivedFunctor.concentratedAt`: the objects of `D(A)` concentrated in degree `i`.
* `Stacks.DerivedFunctor.truncConcentratedAt`, `Stacks.DerivedFunctor.singleConcentratedAt`,
  `Stacks.DerivedFunctor.homologyConcentratedAt`: the one-step interval truncation, the single
  object, and degree-`i` cohomology, read against that full subcategory.
* `Stacks.DerivedFunctor.concentratedAtEquivalence`: that full subcategory is `A`.
* `Stacks.DerivedFunctor.homologyCompSingleConcentratedAtIso`: an object concentrated in degree
  `i` is its own degree-`i` cohomology, placed in degree `i`, naturally.
* `Stacks.DerivedFunctor.concentratedComparisonIso`: the degree-`i` agreement on single objects,
  propagated to every object concentrated in degree `i`.
* `Stacks.DerivedFunctor.truncGEComparisonIso`: the identification
  `H^i(Rw (τ_{≥ i}Z)) ≅ w(H^i Z)`.
* `Stacks.DerivedFunctor.homologyEdge`: the edge transformation
  `Rw ⋙ H^i ⟶ H^i ⋙ w`.

## Main results

* `Stacks.DerivedFunctor.isIso_homologyMap_map_truncLTι_app`: a left t-exact `Rw` turns the
  truncation map `τ_{< i+1}Y ⟶ Y` into an isomorphism on degree-`i` cohomology.
* `Stacks.DerivedFunctor.homologyEdge_app`: the two factors of the edge transformation.
* `Stacks.DerivedFunctor.isIso_homologyEdge_app_of_isGE`: the edge transformation is invertible at
  an object with no cohomology below degree `i`. This is the lowest-degree identification
  `H^i ∘ Rw ≅ w ∘ H^i` on `D^{≥ i}`.

## Implementation notes

The statement is for arbitrary abelian `A` and `B`, an arbitrary functor `w` and an arbitrary
degree; nothing is specialised to sheaves.
It is not stated for an arbitrary t-structure on an arbitrary triangulated category: the two
inputs that make the argument run -- that the cohomology functors are homological, and that
truncation does not change cohomology in the degrees it retains -- are available here as
statements about `DerivedCategory`, and abstracting them would require a shift sequence of
cohomology functors to the heart, which Mathlib does not have.

`Rw` is not required to satisfy `CategoryTheory.Functor.IsRightDerivedFunctor`, and no unit
`w ⟶ Rw` is taken as data. All the construction uses is that `Rw` is triangulated and the two
hypotheses above, so it applies to any functor a caller has in hand that satisfies them -- in
particular to whichever derived functors a comparison square such as
`Stacks.ComparingTopologies.derivedComparisonSquareIso` is stated for, since that declaration
likewise quantifies over arbitrary supplied derived functors.

The exactness of `w` is not a hypothesis of any declaration in this file. It is carried entirely
by `concentratedComparisonIso`'s argument `hsingle`, which is the only place it is used in the
source argument as well; stating it this way also lets a caller who already knows the degree-`i`
agreement for other reasons use the construction.

`Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge` is this comparison for the single
functor `w = Γ(U, -)` on a ringed site, built there by a different route (the unit of
sheafification on the cohomology presheaf) which does not generalise to an arbitrary `w`.

## References

* [Stacks Project, Tag 0EZA](https://stacks.math.columbia.edu/tag/0EZA)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated

namespace Stacks.DerivedFunctor

universe wA vA uA wB vB uB

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-! ## The objects concentrated in a single degree -/

/-- The objects of the unbounded derived category of `A` concentrated in cohomological degree
`i`: those that are both `≤ i` and `≥ i` for the canonical t-structure. For `i = 0` this is the
heart of that t-structure. -/
def concentratedAt (A : Type uA) [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
    (i : ℤ) : ObjectProperty (DerivedCategory A) :=
  DerivedCategory.TStructure.t.le i ⊓ DerivedCategory.TStructure.t.ge i

/-- Being concentrated in degree `i` is being `≤ i` and `≥ i`. -/
lemma mem_concentratedAt_iff (i : ℤ) (X : DerivedCategory A) :
    concentratedAt A i X ↔ X.IsLE i ∧ X.IsGE i := by
  simp [concentratedAt]

/-- The one-step interval truncation `τ_{< i+1}τ_{≥ i}X` is concentrated in degree `i`. -/
lemma concentratedAt_truncLTGE_obj (i : ℤ) (X : DerivedCategory A) :
    concentratedAt A i ((DerivedCategory.TStructure.t.truncLTGE i (i + 1)).obj X) := by
  rw [mem_concentratedAt_iff]
  refine ⟨?_, inferInstance⟩
  have h : DerivedCategory.TStructure.t.IsLE
      ((DerivedCategory.TStructure.t.truncLTGE i (i + 1)).obj X) (i + 1 - 1) := inferInstance
  simpa using h

/-- An object of `A` placed in degree `i` is concentrated in degree `i`. -/
lemma concentratedAt_singleFunctor_obj (i : ℤ) (M : A) :
    concentratedAt A i ((DerivedCategory.singleFunctor A i).obj M) := by
  rw [mem_concentratedAt_iff]
  exact ⟨inferInstance, inferInstance⟩

/-- The one-step interval truncation `τ_{[i,i]} = τ_{< i+1}τ_{≥ i}`, as a functor into the
objects concentrated in degree `i`. -/
def truncConcentratedAt (i : ℤ) :
    DerivedCategory A ⥤ (concentratedAt A i).FullSubcategory :=
  (concentratedAt A i).lift (DerivedCategory.TStructure.t.truncLTGE i (i + 1))
    (concentratedAt_truncLTGE_obj i)

/-- Placing an object of `A` in degree `i`, as a functor into the objects concentrated in
degree `i`. -/
def singleConcentratedAt (i : ℤ) : A ⥤ (concentratedAt A i).FullSubcategory :=
  (concentratedAt A i).lift (DerivedCategory.singleFunctor A i)
    (concentratedAt_singleFunctor_obj i)

/-- Degree-`i` cohomology, restricted to the objects concentrated in degree `i`. -/
def homologyConcentratedAt (i : ℤ) : (concentratedAt A i).FullSubcategory ⥤ A :=
  (concentratedAt A i).ι ⋙ DerivedCategory.homologyFunctor A i

/-- Placing an object in degree `i` is full, because `DerivedCategory.singleFunctor` is. -/
instance (i : ℤ) : (singleConcentratedAt (A := A) i).Full :=
  inferInstanceAs ((concentratedAt A i).lift (DerivedCategory.singleFunctor A i)
    (concentratedAt_singleFunctor_obj i)).Full

/-- Placing an object in degree `i` is faithful, because `DerivedCategory.singleFunctor` is. -/
instance (i : ℤ) : (singleConcentratedAt (A := A) i).Faithful :=
  inferInstanceAs ((concentratedAt A i).lift (DerivedCategory.singleFunctor A i)
    (concentratedAt_singleFunctor_obj i)).Faithful

/-- Every object of `D(A)` concentrated in degree `i` is an object of `A` placed in degree `i`. -/
instance (i : ℤ) : (singleConcentratedAt (A := A) i).EssSurj where
  mem_essImage U := by
    obtain ⟨hLE, hGE⟩ := (mem_concentratedAt_iff i U.obj).1 U.property
    have := hLE
    have := hGE
    obtain ⟨M, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE U.obj i
    exact ⟨M, ⟨((concentratedAt A i).isoMk e).symm⟩⟩

/-- Placing an object in degree `i` is an equivalence onto the objects concentrated there. -/
instance (i : ℤ) : (singleConcentratedAt (A := A) i).IsEquivalence where

/-- **The objects concentrated in degree `i` form a copy of `A`.** Placing an object of `A` in
degree `i` is an equivalence onto the full subcategory of objects of `D(A)` that are both `≤ i`
and `≥ i`. -/
def concentratedAtEquivalence (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasDerivedCategory.{wA} A] (i : ℤ) : A ≌ (concentratedAt A i).FullSubcategory :=
  (singleConcentratedAt i).asEquivalence

/-- Degree-`i` cohomology of an object of `A` placed in degree `i` is that object. -/
def singleCompHomologyConcentratedAtIso (i : ℤ) :
    singleConcentratedAt (A := A) i ⋙ homologyConcentratedAt i ≅ 𝟭 A :=
  DerivedCategory.singleFunctorCompHomologyFunctorIso A i

/-- **An object concentrated in degree `i` is its degree-`i` cohomology, placed in degree `i`.**
This is the naturality the chosen isomorphism of
`Stacks.TruncationLevel.nonempty_iso_singleFunctor_truncLTGE` cannot provide: it is read off the
equivalence `concentratedAtEquivalence`, not chosen object by object. -/
def homologyCompSingleConcentratedAtIso (i : ℤ) :
    𝟭 (concentratedAt A i).FullSubcategory ≅
      homologyConcentratedAt i ⋙ singleConcentratedAt i :=
  have e : homologyConcentratedAt (A := A) i ≅ (concentratedAtEquivalence A i).inverse :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight (concentratedAtEquivalence A i).counitIso.symm
        (homologyConcentratedAt i) ≪≫
      Functor.isoWhiskerLeft (concentratedAtEquivalence A i).inverse
        (singleCompHomologyConcentratedAtIso i) ≪≫
      Functor.rightUnitor _
  (concentratedAtEquivalence A i).counitIso.symm ≪≫
    (Functor.isoWhiskerRight e (singleConcentratedAt i)).symm

/-! ## The comparison on the objects concentrated in degree `i` -/

variable (w : A ⥤ B) (Rw : DerivedCategory A ⥤ DerivedCategory B)

/-- **The degree-`i` agreement, on every object concentrated in degree `i`.** Given the
isomorphism `R⁰w ≅ w` in the form `hsingle`, degree-`i` cohomology of `Rw U` is `w` of the
degree-`i` cohomology of `U`, naturally in an object `U` of `D(A)` concentrated in degree `i`. -/
def concentratedComparisonIso (i : ℤ)
    (hsingle : DerivedCategory.singleFunctor A i ⋙ Rw ⋙
      DerivedCategory.homologyFunctor B i ≅ w) :
    (concentratedAt A i).ι ⋙ Rw ⋙ DerivedCategory.homologyFunctor B i ≅
      (concentratedAt A i).ι ⋙ DerivedCategory.homologyFunctor A i ⋙ w :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight (homologyCompSingleConcentratedAtIso i)
      ((concentratedAt A i).ι ⋙ Rw ⋙ DerivedCategory.homologyFunctor B i) ≪≫
    Functor.isoWhiskerLeft (homologyConcentratedAt (A := A) i) hsingle

/-! ## The edge transformation -/

variable [Rw.CommShift ℤ] [Rw.IsTriangulated]

/-- **Left t-exactness read on one truncation map.** If `Rw` carries `D^{≥ n}` into `D^{≥ n}`,
then the truncation map `τ_{< i+1}Y ⟶ Y` becomes an isomorphism after `Rw` and degree-`i`
cohomology: the third vertex of the truncation triangle is `τ_{≥ i+1}Y`, so its image under `Rw`
has no cohomology in degrees `i - 1` and `i`. -/
lemma isIso_homologyMap_map_truncLTι_app
    (hGE : ∀ (Z : DerivedCategory A) (n : ℤ), Z.IsGE n → (Rw.obj Z).IsGE n)
    (i : ℤ) (Y : DerivedCategory A) :
    IsIso ((DerivedCategory.homologyFunctor B i).map
      (Rw.map ((DerivedCategory.TStructure.t.truncLTι (i + 1)).app Y))) := by
  have : (Rw.obj ((DerivedCategory.TStructure.t.truncGE (i + 1)).obj Y)).IsGE (i + 1) :=
    hGE _ (i + 1) inferInstance
  have h := DerivedCategory.isZero_of_isGE
    (Rw.obj ((DerivedCategory.TStructure.t.truncGE (i + 1)).obj Y)) (i + 1)
  exact Stacks.TruncationLevel.isIso_homologyMap_mor₁
    (Rw.mapTriangle.obj ((DerivedCategory.TStructure.t.triangleLTGE (i + 1)).obj Y))
    (Rw.map_distinguished _
      (DerivedCategory.TStructure.t.triangleLTGE_distinguished (i + 1) Y)) i
    (h i (by omega)) (h (i - 1) (by omega))

/-- The truncation map `τ_{< i+1}Y ⟶ Y`, read by `Rw` and degree-`i` cohomology, as a natural
isomorphism. -/
def truncLTCompDerivedHomologyIso
    (hGE : ∀ (Z : DerivedCategory A) (n : ℤ), Z.IsGE n → (Rw.obj Z).IsGE n) (i : ℤ) :
    DerivedCategory.TStructure.t.truncLT (i + 1) ⋙ Rw ⋙
        DerivedCategory.homologyFunctor B i ≅
      Rw ⋙ DerivedCategory.homologyFunctor B i :=
  haveI : ∀ Y, IsIso ((Functor.whiskerRight
      (DerivedCategory.TStructure.t.truncLTι (i + 1))
      (Rw ⋙ DerivedCategory.homologyFunctor B i)).app Y) := fun Y ↦
    isIso_homologyMap_map_truncLTι_app Rw hGE i Y
  haveI : IsIso (Functor.whiskerRight (DerivedCategory.TStructure.t.truncLTι (i + 1))
      (Rw ⋙ DerivedCategory.homologyFunctor B i)) := NatIso.isIso_of_isIso_app _
  asIso (Functor.whiskerRight (DerivedCategory.TStructure.t.truncLTι (i + 1))
      (Rw ⋙ DerivedCategory.homologyFunctor B i)) ≪≫
    Functor.leftUnitor _

omit [Rw.CommShift ℤ] [Rw.IsTriangulated] in
/-- The truncation map `τ_{< i+1}Y ⟶ Y`, read by degree-`i` cohomology and then `w`, as a
natural isomorphism. -/
def truncLTCompHomologyIso (i : ℤ) :
    DerivedCategory.TStructure.t.truncLT (i + 1) ⋙
        DerivedCategory.homologyFunctor A i ⋙ w ≅
      DerivedCategory.homologyFunctor A i ⋙ w :=
  haveI : ∀ Y, IsIso ((Functor.whiskerRight
      (DerivedCategory.TStructure.t.truncLTι (i + 1))
      (DerivedCategory.homologyFunctor A i ⋙ w)).app Y) := fun Y ↦
    haveI := Stacks.TruncationLevel.isIso_homologyMap_truncLTι_app (i + 1) i (by omega) Y
    Functor.map_isIso w _
  haveI : IsIso (Functor.whiskerRight (DerivedCategory.TStructure.t.truncLTι (i + 1))
      (DerivedCategory.homologyFunctor A i ⋙ w)) := NatIso.isIso_of_isIso_app _
  asIso (Functor.whiskerRight (DerivedCategory.TStructure.t.truncLTι (i + 1))
      (DerivedCategory.homologyFunctor A i ⋙ w)) ≪≫
    Functor.leftUnitor _

omit [Rw.CommShift ℤ] [Rw.IsTriangulated] in
/-- The truncation map `Z ⟶ τ_{≥ i}Z`, read by degree-`i` cohomology and then `w`, as a natural
isomorphism. -/
def truncGECompHomologyIso (i : ℤ) :
    DerivedCategory.homologyFunctor A i ⋙ w ≅
      DerivedCategory.TStructure.t.truncGE i ⋙
        DerivedCategory.homologyFunctor A i ⋙ w :=
  haveI : ∀ Y, IsIso ((Functor.whiskerRight (DerivedCategory.TStructure.t.truncGEπ i)
      (DerivedCategory.homologyFunctor A i ⋙ w)).app Y) := fun Y ↦
    haveI := DerivedCategory.isIso_homologyMap_truncGEπ_app i i le_rfl Y
    Functor.map_isIso w _
  haveI : IsIso (Functor.whiskerRight (DerivedCategory.TStructure.t.truncGEπ i)
      (DerivedCategory.homologyFunctor A i ⋙ w)) := NatIso.isIso_of_isIso_app _
  (Functor.leftUnitor _).symm ≪≫
    asIso (Functor.whiskerRight (DerivedCategory.TStructure.t.truncGEπ i)
      (DerivedCategory.homologyFunctor A i ⋙ w))

/-- **The lowest-degree identification, over the truncation.** Degree-`i` cohomology of
`Rw (τ_{≥ i}Z)` is `w` of the degree-`i` cohomology of `Z`, naturally in `Z`. Since every object
with no cohomology below degree `i` is its own `τ_{≥ i}`, this is the identification
`H^i ∘ Rw ≅ w ∘ H^i` on `D^{≥ i}`; see `isIso_homologyEdge_app_of_isGE`.

The three factors are: the one-step interval truncation `τ_{[i,i]}` of `τ_{≥ i}Z`, inside which
`Rw` may be compared with `w` by `hsingle`, and the two truncation maps read by `w ∘ H^i` in a
degree they retain. Left t-exactness of `Rw` is what makes the first factor invertible. -/
def truncGEComparisonIso
    (hGE : ∀ (Z : DerivedCategory A) (n : ℤ), Z.IsGE n → (Rw.obj Z).IsGE n) (i : ℤ)
    (hsingle : DerivedCategory.singleFunctor A i ⋙ Rw ⋙
      DerivedCategory.homologyFunctor B i ≅ w) :
    DerivedCategory.TStructure.t.truncGE i ⋙ Rw ⋙
        DerivedCategory.homologyFunctor B i ≅
      DerivedCategory.homologyFunctor A i ⋙ w :=
  (Functor.isoWhiskerLeft (DerivedCategory.TStructure.t.truncGE i)
      (truncLTCompDerivedHomologyIso Rw hGE i)).symm ≪≫
    Functor.isoWhiskerLeft (truncConcentratedAt (A := A) i)
      (concentratedComparisonIso w Rw i hsingle) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.TStructure.t.truncGE i)
      (truncLTCompHomologyIso w i) ≪≫
    (truncGECompHomologyIso w i).symm

/-- **The edge transformation of a right derived functor.** For a right derived functor `Rw` of
`w` which is left t-exact and agrees with `w` in degree `i` on objects placed in degree `i`,
the canonical natural comparison `H^i(Rw Z) ⟶ w(H^i Z)`.

It is the truncation map `Z ⟶ τ_{≥ i}Z`, read by `H^i ∘ Rw`, followed by the isomorphism
`truncGEComparisonIso`. That single factor is the only one that fails to be invertible, and it
is invertible as soon as `Z` has no cohomology below degree `i`. -/
def homologyEdge
    (hGE : ∀ (Z : DerivedCategory A) (n : ℤ), Z.IsGE n → (Rw.obj Z).IsGE n) (i : ℤ)
    (hsingle : DerivedCategory.singleFunctor A i ⋙ Rw ⋙
      DerivedCategory.homologyFunctor B i ≅ w) :
    Rw ⋙ DerivedCategory.homologyFunctor B i ⟶
      DerivedCategory.homologyFunctor A i ⋙ w :=
  (Functor.leftUnitor _).inv ≫
    Functor.whiskerRight (DerivedCategory.TStructure.t.truncGEπ i)
      (Rw ⋙ DerivedCategory.homologyFunctor B i) ≫
    (truncGEComparisonIso w Rw hGE i hsingle).hom

/-- The edge transformation at an object, as the truncation map followed by
`truncGEComparisonIso`. -/
lemma homologyEdge_app
    (hGE : ∀ (Z : DerivedCategory A) (n : ℤ), Z.IsGE n → (Rw.obj Z).IsGE n) (i : ℤ)
    (hsingle : DerivedCategory.singleFunctor A i ⋙ Rw ⋙
      DerivedCategory.homologyFunctor B i ≅ w)
    (Z : DerivedCategory A) :
    (homologyEdge w Rw hGE i hsingle).app Z =
      (DerivedCategory.homologyFunctor B i).map
          (Rw.map ((DerivedCategory.TStructure.t.truncGEπ i).app Z)) ≫
        (truncGEComparisonIso w Rw hGE i hsingle).hom.app Z := by
  simp [homologyEdge]

/-- **The lowest-degree identification.** The edge transformation is invertible at an object
with no cohomology below degree `i`: its only non-invertible factor is the truncation map
`Z ⟶ τ_{≥ i}Z`, which is itself invertible there. -/
lemma isIso_homologyEdge_app_of_isGE
    (hGE : ∀ (Z : DerivedCategory A) (n : ℤ), Z.IsGE n → (Rw.obj Z).IsGE n) (i : ℤ)
    (hsingle : DerivedCategory.singleFunctor A i ⋙ Rw ⋙
      DerivedCategory.homologyFunctor B i ≅ w)
    (Z : DerivedCategory A) [Z.IsGE i] :
    IsIso ((homologyEdge w Rw hGE i hsingle).app Z) := by
  rw [homologyEdge_app]
  infer_instance

end Stacks.DerivedFunctor

end
