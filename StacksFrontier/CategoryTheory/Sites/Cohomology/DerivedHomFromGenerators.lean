module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.Refinements
public import Mathlib.CategoryTheory.Sites.Grothendieck
public import StacksFrontier.Homology.Injectives.Spaltenstein.Enlargement

/-!
# Morphisms in the derived category out of locally projective objects

Let `A` be an abelian category, let `(C, J)` be a site and let `Y : C ⥤ A` be a functor whose
values are *locally projective*: every epimorphism onto `Y U` splits after restricting along the
arrows `V ⟶ U` of a covering sieve.  The guiding example is `U ↦ j_{U!} Λ`, the extension by zero
of the constant sheaf, in sheaves of `Λ`-modules on a site: a morphism `j_{U!} Λ ⟶ F` is a
section of `F` over `U`, and an epimorphism of sheaves is locally surjective on sections.

For an object `N` of the derived category `D(A)` this file compares the two presheaves of abelian
groups on `C`
```
U ↦ Hom_{D(A)}((Y U)[0], N)        and        U ↦ Hom_A(Y U, H^0(N)),
```
the comparison being the map induced by the cohomology functor `H^0`.  It is *locally bijective*
(`homToHomologyZero_locallySurjective`, `homToHomologyZero_locallyInjective`), so the two
presheaves have the same sheafification.  Applied to `U ↦ j_{U!} Λ` this is the statement that the
cohomology sheaf `H^n(M)` is the sheaf associated to `U ↦ Hom(j_{U!} Λ, M[n]) = H^n(U, M)`.

## Main definitions

* `Stacks.Cohomology.DerivedHomFromGenerators.homToHomologyZero`: the comparison
  `Hom_{D(A)}(X[0], N) →+ Hom_A(X, H^0(N))`.
* `Stacks.Cohomology.DerivedHomFromGenerators.epiLiftSieve`: for an epimorphism `π` onto `Y U`,
  the sieve of the arrows `v : V ⟶ U` along which `Y.map v` lifts through `π`.

## Main results

* `homToHomologyZero_Q_map_mkHomFromSingle`: on the class of a cocycle `φ : X ⟶ L^0` of a cochain
  complex `L`, the comparison is the cohomology class of `φ`.
* `homToHomologyZero_locallySurjective`: every morphism `Y U ⟶ H^0(N)` lifts, locally on `U`, to a
  morphism `(Y U)[0] ⟶ N` of the derived category.
* `homToHomologyZero_locallyInjective`: a morphism `(Y U)[0] ⟶ N` inducing zero on `H^0` vanishes
  locally on `U`.  This is where K-injective resolutions enter, so `A` is assumed Grothendieck
  abelian.

## Implementation notes

The derived category is any model `[HasDerivedCategory A]`.  The argument is the source's: choose a
K-injective complex `I` representing `N`, so that a morphism `(Y U)[0] ⟶ N` is the homotopy class
of a cocycle `Y U ⟶ I^0`; it induces zero on `H^0` exactly when, after an epimorphism onto `Y U`,
it is a coboundary, and local projectivity of `Y U` removes the epimorphism locally.

## References

* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
* [Stacks Project, Tag 0GLK](https://stacks.math.columbia.edu/tag/0GLK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w wD vA uA vC uC

namespace Stacks.Cohomology.DerivedHomFromGenerators

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wD} A]

/-! ### The comparison map -/

/-- The comparison `Hom_{D(A)}(X[0], N) →+ Hom_A(X, H^0(N))` induced by the cohomology functor
`H^0`, read through `H^0(X[0]) = X`. -/
def homToHomologyZero (X : A) (N : DerivedCategory A) :
    ((DerivedCategory.singleFunctor A 0).obj X ⟶ N) →+
      (X ⟶ (DerivedCategory.homologyFunctor A 0).obj N) where
  toFun φ := (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).inv.app X ≫
    (DerivedCategory.homologyFunctor A 0).map φ
  map_zero' := by simp
  map_add' _ _ := by simp

/-- The comparison sends `φ` to `H^0(φ)` precomposed with the identification `X ≅ H^0(X[0])`. -/
lemma homToHomologyZero_apply (X : A) (N : DerivedCategory A)
    (φ : (DerivedCategory.singleFunctor A 0).obj X ⟶ N) :
    homToHomologyZero X N φ =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).inv.app X ≫
        (DerivedCategory.homologyFunctor A 0).map φ := rfl

/-- `H^0(N[n]) = H^n(N)`, the shift sequence of the cohomology functor of the derived category
read at the indices `0` and `n`. -/
def homologyZeroShiftIso (N : DerivedCategory A) (n : ℤ) :
    (DerivedCategory.homologyFunctor A 0).obj (N⟦n⟧) ≅
      (DerivedCategory.homologyFunctor A n).obj N :=
  ((DerivedCategory.homologyFunctor A 0).shiftIso n 0 n (add_zero n)).app N

/-- The comparison is natural in the source. -/
lemma homToHomologyZero_comp_left {X' X : A} (g : X' ⟶ X) (N : DerivedCategory A)
    (φ : (DerivedCategory.singleFunctor A 0).obj X ⟶ N) :
    homToHomologyZero X' N ((DerivedCategory.singleFunctor A 0).map g ≫ φ) =
      g ≫ homToHomologyZero X N φ := by
  have := (DerivedCategory.singleFunctorCompHomologyFunctorIso A 0).inv.naturality g
  dsimp at this
  simp only [homToHomologyZero_apply, Functor.map_comp, ← Category.assoc, ← this]

/-- The comparison is natural in the target. -/
lemma homToHomologyZero_comp_right (X : A) {N N' : DerivedCategory A}
    (φ : (DerivedCategory.singleFunctor A 0).obj X ⟶ N) (e : N ⟶ N') :
    homToHomologyZero X N' (φ ≫ e) =
      homToHomologyZero X N φ ≫ (DerivedCategory.homologyFunctor A 0).map e := by
  simp [homToHomologyZero_apply]

/-- On the image of a morphism of cochain complexes out of a single complex, the comparison is
the morphism induced on cohomology. -/
lemma homToHomologyZero_Q_map (L : CochainComplex A ℤ) {X : A}
    (f : (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X ⟶ L) :
    homToHomologyZero X (DerivedCategory.Q.obj L) (DerivedCategory.Q.map f) ≫
      (DerivedCategory.homologyFunctorFactors A 0).hom.app L =
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 X).inv ≫
        HomologicalComplex.homologyMap f 0 := by
  rw [homToHomologyZero_apply, Category.assoc,
    DerivedCategory.homologyFunctorFactors_hom_naturality]
  simp only [Functor.comp_obj, DerivedCategory.singleFunctorCompHomologyFunctorIso,
    SingleFunctors.evaluation_obj, SingleFunctors.postcomp_functor,
    DerivedCategory.singleFunctorsPostcompQIso, Functor.mapIso_refl, Functor.isoWhiskerRight_refl,
    Iso.refl_trans, Iso.trans_inv, Functor.isoWhiskerLeft_inv, Category.assoc, NatTrans.comp_app,
    Functor.id_obj, HomologicalComplex.homologyFunctorSingleIso_inv_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, Category.comp_id]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
    ((DerivedCategory.homologyFunctorFactors A 0).inv_hom_id_app_assoc _ _))

/-- On the class of a cocycle `φ : X ⟶ L^0`, the comparison followed by the identification of
`H^0` of the image of `L` with `L.homology 0` is the cohomology class of `φ`. -/
lemma homToHomologyZero_Q_map_mkHomFromSingle (L : CochainComplex A ℤ) {X : A}
    (φ : X ⟶ L.X 0) (hφ : ∀ k, (ComplexShape.up ℤ).Rel 0 k → φ ≫ L.d 0 k = 0) :
    homToHomologyZero X (DerivedCategory.Q.obj L)
        (DerivedCategory.Q.map (HomologicalComplex.mkHomFromSingle φ hφ)) ≫
      (DerivedCategory.homologyFunctorFactors A 0).hom.app L =
      L.liftCycles φ 1 (by simp) (hφ 1 (by simp)) ≫ L.homologyπ 0 := by
  rw [homToHomologyZero_Q_map,
    ← HomologicalComplex.singleObjCyclesSelfIso_inv_homologyπ, Category.assoc,
    HomologicalComplex.homologyπ_naturality, ← Category.assoc]
  congr 1
  rw [← cancel_mono (L.iCycles 0)]
  simp

/-- `H^0(L) = H^0` of the cochain complex `L`, for the image of `L` in the derived category. -/
def homologyZeroIso (L : CochainComplex A ℤ) :
    (DerivedCategory.homologyFunctor A 0).obj (DerivedCategory.Q.obj L) ≅ L.homology 0 :=
  (DerivedCategory.homologyFunctorFactors A 0).app L

/-- On the class of a cocycle `φ : X ⟶ L^0`, the comparison is the cohomology class of `φ`. -/
lemma homToHomologyZero_Q_map_mkHomFromSingle_eq (L : CochainComplex A ℤ) {X : A}
    (φ : X ⟶ L.X 0) (hφ : ∀ k, (ComplexShape.up ℤ).Rel 0 k → φ ≫ L.d 0 k = 0) :
    homToHomologyZero X (DerivedCategory.Q.obj L)
        (DerivedCategory.Q.map (HomologicalComplex.mkHomFromSingle φ hφ)) =
      (L.liftCycles φ 1 (by simp) (hφ 1 (by simp)) ≫ L.homologyπ 0) ≫
        (homologyZeroIso L).inv := by
  rw [Iso.eq_comp_inv]
  exact homToHomologyZero_Q_map_mkHomFromSingle L φ hφ

/-- A cocycle `X ⟶ L^0` which is a coboundary gives the zero morphism `X[0] ⟶ L` of the derived
category: the morphism of complexes is null-homotopic. -/
lemma Q_map_mkHomFromSingle_eq_zero (L : CochainComplex A ℤ) {X : A} (φ : X ⟶ L.X 0)
    (hφ : ∀ k, (ComplexShape.up ℤ).Rel 0 k → φ ≫ L.d 0 k = 0) (x : X ⟶ L.X (-1))
    (hx : x ≫ L.d (-1) 0 = φ) :
    DerivedCategory.Q.map (HomologicalComplex.mkHomFromSingle φ hφ) = 0 := by
  let h : ∀ i j, (ComplexShape.up ℤ).Rel j i →
      (((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X).X i ⟶ L.X j) :=
    fun i j hr => if hi : i = 0 then
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 0 X i hi).hom ≫ x ≫
        (L.XIsoOfEq (show (-1 : ℤ) = j by simp only [ComplexShape.up_Rel] at hr; omega)).hom
      else 0
  have key : HomologicalComplex.mkHomFromSingle φ hφ = Homotopy.nullHomotopicMap' h := by
    apply HomologicalComplex.from_single_hom_ext
    rw [Homotopy.nullHomotopicMap'_f (show (ComplexShape.up ℤ).Rel (-1) 0 by simp)
      (show (ComplexShape.up ℤ).Rel 0 1 by simp) h, HomologicalComplex.mkHomFromSingle_f]
    simp [h, ← hx, HomologicalComplex.singleObjXSelf]
  rw [key, DerivedCategory.Q_map_eq_of_homotopy (h := Homotopy.nullHomotopy' h), Functor.map_zero]

omit [HasDerivedCategory.{wD} A] in
/-- Precomposing a morphism out of a single complex with the image of a morphism of the single
term. -/
lemma single_map_comp_mkHomFromSingle (L : CochainComplex A ℤ) {X' X : A} (g : X' ⟶ X)
    (φ : X ⟶ L.X 0) (hφ : ∀ k, (ComplexShape.up ℤ).Rel 0 k → φ ≫ L.d 0 k = 0) :
    (HomologicalComplex.single A (ComplexShape.up ℤ) 0).map g ≫
        HomologicalComplex.mkHomFromSingle φ hφ =
      HomologicalComplex.mkHomFromSingle (g ≫ φ)
        (fun k hk ↦ by rw [Category.assoc, hφ k hk, comp_zero]) := by
  apply HomologicalComplex.from_single_hom_ext
  simp [HomologicalComplex.single_map_f_self]

omit [HasDerivedCategory.{wD} A] in
/-- Every morphism of cochain complexes out of a single complex concentrated in degree `0` is
`HomologicalComplex.mkHomFromSingle` of its degree `0` component. -/
lemma eq_mkHomFromSingle (L : CochainComplex A ℤ) {X : A}
    (f : (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X ⟶ L) :
    ∃ (φ : X ⟶ L.X 0) (hφ : ∀ k, (ComplexShape.up ℤ).Rel 0 k → φ ≫ L.d 0 k = 0),
      f = HomologicalComplex.mkHomFromSingle φ hφ := by
  refine ⟨(HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv ≫ f.f 0, ?_, ?_⟩
  · intro k hk
    rw [Category.assoc, f.comm, HomologicalComplex.single_obj_d, zero_comp, comp_zero]
  · apply HomologicalComplex.from_single_hom_ext
    simp

/-- Morphisms of the derived category into a K-injective complex are images of morphisms of
cochain complexes. -/
lemma Q_map_surjective_of_isKInjective (K I : CochainComplex A ℤ) [I.IsKInjective]
    (g : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj I) :
    ∃ f : K ⟶ I, DerivedCategory.Q.map f = g := by
  obtain ⟨α, hα⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient _ _).obj K) I).2
      ((DerivedCategory.quotientCompQhIso A).hom.app K ≫ g ≫
        (DerivedCategory.quotientCompQhIso A).inv.app I)
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A _).map_surjective α
  refine ⟨f, ?_⟩
  have h := DerivedCategory.quotientCompQhIso_hom_naturality f
  rw [hα] at h
  simpa using h.symm

/-! ### Locality -/

variable {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C) (Y : C ⥤ A)

/-- For an epimorphism `π : A' ⟶ Y U`, the sieve of the arrows `v : V ⟶ U` along which `Y.map v`
lifts through `π`.  The objects `Y U` are locally projective when these sieves cover. -/
def epiLiftSieve {U : C} {A' : A} (π : A' ⟶ Y.obj U) : Sieve U where
  arrows V v := ∃ k : Y.obj V ⟶ A', k ≫ π = Y.map v
  downward_closed := by
    rintro V W v ⟨k, hk⟩ w
    exact ⟨Y.map w ≫ k, by rw [Category.assoc, hk, ← Functor.map_comp]⟩

/-- The sieve of the arrows `v : V ⟶ U` along which a morphism `γ : Y U ⟶ H^0(N)` lifts, after
restriction along `v`, to a morphism `(Y V)[0] ⟶ N` of the derived category. -/
def homologyLiftSieve {U : C} (N : DerivedCategory A)
    (γ : Y.obj U ⟶ (DerivedCategory.homologyFunctor A 0).obj N) : Sieve U where
  arrows V v := ∃ ψ, homToHomologyZero (Y.obj V) N ψ = Y.map v ≫ γ
  downward_closed := by
    rintro V W v ⟨ψ, hψ⟩ w
    exact ⟨(DerivedCategory.singleFunctor A 0).map (Y.map w) ≫ ψ, by
      rw [homToHomologyZero_comp_left, hψ, ← Category.assoc, ← Functor.map_comp]⟩

/-- The sieve of the arrows `v : V ⟶ U` along which a morphism `ψ : (Y U)[0] ⟶ N` of the derived
category restricts to zero. -/
def vanishingSieve {U : C} (N : DerivedCategory A)
    (ψ : (DerivedCategory.singleFunctor A 0).obj (Y.obj U) ⟶ N) : Sieve U where
  arrows V v := (DerivedCategory.singleFunctor A 0).map (Y.map v) ≫ ψ = 0
  downward_closed := by
    intro V W v hv w
    rw [Functor.map_comp, Functor.map_comp, Category.assoc, hv, comp_zero]

variable {J Y}

/-- **Local surjectivity.** If the objects `Y U` are locally projective, every morphism
`Y U ⟶ H^0(N)` is, locally on `U`, the image of a morphism `(Y V)[0] ⟶ N` of the derived
category. -/
theorem homToHomologyZero_locallySurjective
    (hY : ∀ ⦃U : C⦄ ⦃A' : A⦄ (π : A' ⟶ Y.obj U) [Epi π], epiLiftSieve Y π ∈ J U)
    {U : C} (N : DerivedCategory A)
    (γ : Y.obj U ⟶ (DerivedCategory.homologyFunctor A 0).obj N) :
    homologyLiftSieve Y N γ ∈ J U := by
  let L := DerivedCategory.Q.objPreimage N
  let e : DerivedCategory.Q.obj L ≅ N := DerivedCategory.Q.objObjPreimageIso N
  let eL : (DerivedCategory.homologyFunctor A 0).obj N ≅ L.homology 0 :=
    (DerivedCategory.homologyFunctor A 0).mapIso e.symm ≪≫ homologyZeroIso L
  obtain ⟨A', π, _, z, hz, fac⟩ :=
    L.eq_liftCycles_homologyπ_up_to_refinements (γ ≫ eL.hom) 1 (by simp)
  refine J.superset_covering ?_ (hY π)
  rintro V v ⟨k, hk⟩
  have hkz : ∀ m, (ComplexShape.up ℤ).Rel 0 m → (k ≫ z) ≫ L.d 0 m = 0 := by
    rintro m hm
    obtain rfl : m = 1 := by simp only [ComplexShape.up_Rel] at hm; omega
    rw [Category.assoc, hz, comp_zero]
  refine ⟨DerivedCategory.Q.map (HomologicalComplex.mkHomFromSingle (k ≫ z) hkz) ≫ e.hom, ?_⟩
  have h2 : (DerivedCategory.homologyFunctor A 0).map e.hom = (homologyZeroIso L).hom ≫ eL.inv := by
    simp [eL]
  have h3 : L.liftCycles (k ≫ z) 1 (by simp) (hkz 1 (by simp)) =
      k ≫ L.liftCycles z 1 (by simp) hz := by
    rw [← cancel_mono (L.iCycles 0)]
    simp
  have h4 : L.liftCycles z 1 (by simp) hz ≫ L.homologyπ 0 ≫ eL.inv = π ≫ γ := by
    rw [← Category.assoc, ← fac]
    simp
  rw [homToHomologyZero_comp_right, homToHomologyZero_Q_map_mkHomFromSingle_eq, h2, h3]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [h4, ← hk, Category.assoc]

/-- **Local injectivity.** If the objects `Y U` are locally projective and `A` is a Grothendieck
abelian category, a morphism `(Y U)[0] ⟶ N` of the derived category which induces zero on `H^0`
vanishes locally on `U`. -/
theorem homToHomologyZero_locallyInjective [IsGrothendieckAbelian.{w} A]
    (hY : ∀ ⦃U : C⦄ ⦃A' : A⦄ (π : A' ⟶ Y.obj U) [Epi π], epiLiftSieve Y π ∈ J U)
    {U : C} (N : DerivedCategory A)
    (ψ : (DerivedCategory.singleFunctor A 0).obj (Y.obj U) ⟶ N)
    (hψ : homToHomologyZero (Y.obj U) N ψ = 0) :
    vanishingSieve Y N ψ ∈ J U := by
  let R := (Stacks.Injectives.FunctorialEnlargement.exists_functorial_quasiIso_isKInjective.{w}
    A).some
  let L := DerivedCategory.Q.objPreimage N
  let e : DerivedCategory.Q.obj L ≅ N := DerivedCategory.Q.objObjPreimageIso N
  let I := R.functor.obj L
  have : I.IsKInjective := R.isKInjective L
  have : QuasiIso (R.inclusion.app L) := R.quasiIso L
  have : IsIso (DerivedCategory.Q.map (R.inclusion.app L)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso A _).2 inferInstance
  let e' : DerivedCategory.Q.obj I ≅ N :=
    (asIso (DerivedCategory.Q.map (R.inclusion.app L))).symm ≪≫ e
  obtain ⟨f, hf⟩ := Q_map_surjective_of_isKInjective
    ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj (Y.obj U)) I (ψ ≫ e'.inv)
  obtain ⟨φ, hφ, rfl⟩ := eq_mkHomFromSingle I f
  have h0 : I.liftCycles φ 1 (by simp) (hφ 1 (by simp)) ≫ I.homologyπ 0 = 0 := by
    have h := homToHomologyZero_Q_map_mkHomFromSingle_eq I φ hφ
    rw [hf, homToHomologyZero_comp_right, hψ, zero_comp] at h
    have h' := congrArg (· ≫ (homologyZeroIso I).hom) h
    simpa using h'.symm
  obtain ⟨A', π, _, x, fac⟩ :=
    (I.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements (-1) 0 1 (by simp) (by simp) φ
      (hφ 1 (by simp))).1 h0
  refine J.superset_covering ?_ (hY π)
  rintro V v ⟨k, hk⟩
  have hψ' : ψ = DerivedCategory.Q.map (HomologicalComplex.mkHomFromSingle φ hφ) ≫ e'.hom := by
    rw [hf, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change (DerivedCategory.Q).map ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).map
    (Y.map v)) ≫ ψ = 0
  rw [hψ', ← Category.assoc, ← Functor.map_comp, single_map_comp_mkHomFromSingle,
    Q_map_mkHomFromSingle_eq_zero I _ _ (k ≫ x)
      (by rw [Category.assoc, ← fac, ← Category.assoc, hk]), zero_comp]

end Stacks.Cohomology.DerivedHomFromGenerators
