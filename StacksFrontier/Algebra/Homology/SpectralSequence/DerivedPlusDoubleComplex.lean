module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.Algebra.Homology.SpectralSequence.AbutsToTransport
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplexNaturality
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
public import StacksFrontier.Topology.Sheaves.Cohomology.CechSpectralSequence.SequenceAndSecondPage

/-!
# The spectral sequence of a degreewise functor to complexes, on the bounded below derived category

Let `A` and `B` be abelian categories, `A` with enough injectives, and let `F : A ⥤ C(B)` be an
additive functor from `A` to cochain complexes in `B`. A cochain complex `Z^•` in `A` gives the
double complex `F(Z^•)` with `F(Z^q)^p` in bidegree `(q, p)`, and its second spectral sequence,
of the filtration of the total complex by `p`, has

```
E_1^{p,q} = H^q(F(Z^•)^p).
```

Homotopic morphisms of complexes in `A` give homotopic morphisms of double complexes, hence the
same morphism of spectral sequences from the first page on. So representing an object `K` of
`D⁺(A)` by a bounded below complex of injectives gives a spectral sequence that is a functor of
`K`, with the following two properties.

* If `F(-)^p` is isomorphic to a composite `P ∘ R` of an exact functor `R : A ⥤ A'` carrying
  injective objects to objects right acyclic for an additive functor `P : A' ⥤ B`, then
  `E_1^{p,q} ≅ H^q(RP(R K))`, naturally in `K`. This holds in particular when `R` preserves
  injective objects.
* If an additive functor `T : A ⥤ B` with an augmentation `T(Z^•) ⟶ F(Z^•)^0` satisfies, for
  bounded below complexes of injectives, the hypotheses of Stacks 0133, then the spectral sequence
  abuts to `H^n(RT(K))`.

## Main definitions

* `DerivedCategory.Plus.injectiveObjectEquivalence`: the equivalence `K⁺(Inj A) ≌ D⁺(A)`.
* `Stacks.DegreewiseSpectralSequence.complexFunctor`, `.homotopyFunctor`, `.derivedFunctor`: the
  spectral sequence as a functor of a complex, of an object of the homotopy category, and of an
  object of `D⁺(A)`.

## Main results

* `Stacks.DegreewiseSpectralSequence.derivedPageOneIsoOfRightAcyclic`:
  `E_1^{p,q} ≅ H^q(RP(R K))`, naturally, by Leray's acyclicity lemma (Stacks 015E).
* `Stacks.DegreewiseSpectralSequence.derivedPageOneIso`: the same when `R` preserves injective
  objects.
* `Stacks.DegreewiseSpectralSequence.isZero_derivedFunctor_page_one`: the first page vanishes in
  the columns where `F(-)^p` vanishes.
* `Stacks.DegreewiseSpectralSequence.abutsTo_derivedFunctor`: the abutment is `H^n(RT(K))`.

## Implementation notes

Every statement is made over abstract categories and functors. Instantiated at categories of
abelian sheaves the same chases do not elaborate inside the default budgets, while an instance of
a lemma proved here is a single application.

## References

* [Stacks Project, Tag 0D7A](https://stacks.math.columbia.edu/tag/0D7A)
* [Stacks Project, Tag 0132](https://stacks.math.columbia.edu/tag/0132)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Tag 05TG](https://stacks.math.columbia.edu/tag/05TG)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory.Plus

variable (C : Type*) [Category* C] [Abelian C] [HasDerivedCategory C]

/-- The canonical functor `K⁺(Inj C) ⥤ D⁺(C)` from the bounded below homotopy category of
complexes of injective objects to the bounded below derived category. -/
abbrev injectiveObjectQh : HomotopyCategory.Plus (InjectiveObject C) ⥤ DerivedCategory.Plus C :=
  (InjectiveObject.ι C).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh

/-- A bounded below complex of injective objects stays bounded below in the ambient category. -/
private lemma exists_isStrictlyGE_injectiveObject {D : Type*} [Category* D] [Abelian D]
    (X : HomotopyCategory.Plus (InjectiveObject D)) :
    ∃ n, CochainComplex.IsStrictlyGE
      ((InjectiveObject.ι D).mapHomotopyCategoryPlus.obj X).obj.as n := by
  obtain ⟨n, hn⟩ := (HomotopyCategory.plus_quotient_obj_iff X.obj.as).1 X.property
  refine ⟨n, ?_⟩
  change CochainComplex.IsStrictlyGE
    (((InjectiveObject.ι D).mapHomologicalComplex (.up ℤ)).obj X.obj.as) n
  infer_instance

omit [HasDerivedCategory C] in
/-- A bounded below complex of injective objects is K-injective. -/
lemma isKInjective_injectiveObject (X : HomotopyCategory.Plus (InjectiveObject C)) :
    CochainComplex.IsKInjective ((InjectiveObject.ι C).mapHomotopyCategoryPlus.obj X).obj.as := by
  obtain ⟨n, _⟩ := exists_isStrictlyGE_injectiveObject X
  exact CochainComplex.isKInjective_of_injective _ n

/-- **`K⁺(Inj C) ⥤ D⁺(C)` is an equivalence** when `C` has enough injectives (Stacks 05TG,
Stacks 013K). -/
instance isEquivalence_injectiveObjectQh [EnoughInjectives C] :
    (injectiveObjectQh C).IsEquivalence := by
  have hbij : ∀ X Y, Function.Bijective ((injectiveObjectQh C).map : (X ⟶ Y) → _) :=
    fun X Y => (DerivedCategory.Plus.Qh_map_bijective_of_isKInjective _ _
      (isKInjective_injectiveObject C Y)).comp
      ⟨(InjectiveObject.ι C).mapHomotopyCategoryPlus.map_injective,
        (InjectiveObject.ι C).mapHomotopyCategoryPlus.map_surjective⟩
  have : (injectiveObjectQh C).Full := ⟨fun f => (hbij _ _).surjective f⟩
  have : (injectiveObjectQh C).Faithful := ⟨fun h => (hbij _ _).injective h⟩
  exact {}

/-- The equivalence `K⁺(Inj C) ≌ D⁺(C)`, whose functor is `injectiveObjectQh`. -/
def injectiveObjectEquivalence [EnoughInjectives C] :
    HomotopyCategory.Plus (InjectiveObject C) ≌ DerivedCategory.Plus C :=
  (injectiveObjectQh C).asEquivalence

/-- The homology of the image in `D⁺(C)` of a bounded below homotopy class is its homology. -/
def QhHomologyIso (n : ℤ) :
    DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.homologyFunctor C n ≅
      HomotopyCategory.Plus.ι C ⋙ HomotopyCategory.homologyFunctor C (ComplexShape.up ℤ) n :=
  Functor.isoWhiskerLeft (HomotopyCategory.Plus.ι C)
    (DerivedCategory.homologyFunctorFactorsh C n)

end DerivedCategory.Plus

namespace Stacks.DegreewiseSpectralSequence

variable {A : Type*} [Category* A] [Abelian A] {B : Type*} [Category* B] [Abelian B]
  [∀ L : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ),
    L.HasTotal (ComplexShape.up ℤ)]
  (F : A ⥤ CochainComplex B ℤ) [F.Additive]

/-! ### The spectral sequence of a complex -/

/-- The double complex `F(Z^•)`, with `F(Z^q)^p` in bidegree `(q, p)`. -/
abbrev doubleComplex (Z : CochainComplex A ℤ) :
    HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z

/-- The second spectral sequence of the double complex `F(Z^•)`, presented from its first page,
as a functor of the complex `Z^•`. -/
def complexFunctor : CochainComplex A ℤ ⥤ CohomologicalSpectralSequence B 1 :=
  F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex₂.spectralSequence₂Functor B ⋙
      Stacks.Cohomology.CechSpectral.restrictR₀ (show (0 : ℤ) ≤ 1 by omega)

/-- **Homotopic morphisms of complexes induce the same morphism of spectral sequences.** -/
theorem complexFunctor_map_eq_of_homotopy {Z Z' : CochainComplex A ℤ} {f g : Z ⟶ Z'}
    (h : Homotopy f g) : (complexFunctor F).map f = (complexFunctor F).map g :=
  CategoryTheory.SpectralSequence.hom_ext fun r hr =>
    HomologicalComplex₂.spectralSequenceMap₂_hom_eq_of_filteredHomotopy₂
      (HomologicalComplex₂.filteredHomotopy₂_of_homotopy (F.mapHomotopy h))
      (show (1 : ℤ) ≤ r by omega)

/-- The spectral sequence, as a functor on the homotopy category of `A`. -/
def homotopyFunctor : HomotopyCategory A (ComplexShape.up ℤ) ⥤ CohomologicalSpectralSequence B 1 :=
  CategoryTheory.Quotient.lift _ (complexFunctor F)
    (fun _ _ _ _ ⟨h⟩ => complexFunctor_map_eq_of_homotopy F h)

variable [EnoughInjectives A] [HasDerivedCategory A]

/-- **The spectral sequence, as a functor on `D⁺(A)`**: an object is represented by a bounded
below complex of injectives `I^•`, and sent to the second spectral sequence of `F(I^•)`. -/
def derivedFunctor : DerivedCategory.Plus A ⥤ CohomologicalSpectralSequence B 1 :=
  (DerivedCategory.Plus.injectiveObjectEquivalence A).inverse ⋙
    (InjectiveObject.ι A).mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι A ⋙
      homotopyFunctor F

/-! ### The first page -/

section PageOne

variable (p q : ℤ) (G : A ⥤ B) [G.Additive]

/-- Taking homology of `F(Z^•)` in the outer degree `q` and then the term of inner degree `p` is
taking `G` degreewise and then the `q`-th cohomology, for `G ≅ F(-)^p`. -/
def columnHomologyIso (e : F ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) p ≅ G) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor (CochainComplex B ℤ) (ComplexShape.up ℤ) q ⋙
          HomologicalComplex.eval B (ComplexShape.up ℤ) p ≅
      G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) q :=
  Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (StacksDraft.DerivedCategoryHomology.mapHomologicalComplexHomologyIso
        (HomologicalComplex.eval B (ComplexShape.up ℤ) p) (ComplexShape.up ℤ) q).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ))
      (HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) q)

/-- **`E_1^{p,q} ≅ H^q(G(Z^•))`** for the spectral sequence of a complex, naturally in the
complex, where `G ≅ F(-)^p`. -/
def complexPageOneIso (e : F ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) p ≅ G) :
    complexFunctor F ⋙ CategoryTheory.SpectralSequence.pageFunctor B _ 1 1 le_rfl ⋙
        HomologicalComplex.eval B _ (p, q) ≅
      G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor B (ComplexShape.up ℤ) q :=
  NatIso.ofComponents
    (fun Z => HomologicalComplex₂.isoOnePageTotalFiltration₂
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) _
        (HomologicalComplex₂.pageIso₂ _) (HomologicalComplex₂.exists_delta₂ _) p q ≪≫
      (columnHomologyIso F p q G e).app Z)
    (fun {_ _} f => (CommSq.vert_comp
      ⟨HomologicalComplex₂.isoOnePageTotalFiltration₂_naturality_functor
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) p q⟩
      ⟨(columnHomologyIso F p q G e).hom.naturality f⟩).w)

/-- **`E_1^{p,q} ≅ H^q(G(Z^•))`** on the homotopy category. -/
def homotopyPageOneIso (e : F ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) p ≅ G) :
    homotopyFunctor F ⋙ CategoryTheory.SpectralSequence.pageFunctor B _ 1 1 le_rfl ⋙
        HomologicalComplex.eval B _ (p, q) ≅
      G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) q :=
  CategoryTheory.Quotient.natIsoLift _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (CategoryTheory.Quotient.lift.isLift _ _ _) _ ≪≫
      complexPageOneIso F p q G e ≪≫
      Functor.isoWhiskerLeft (G.mapHomologicalComplex (ComplexShape.up ℤ))
        (HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) q).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm _ ≪≫
      Functor.associator _ _ _)

-- `CategoryTheory.Functor.rightAcyclic` mentions `HasRightDerivedFunctor`; the instance coming
-- from `EnoughInjectives` is given precedence over the route that would try to prove termwise
-- injectivity of an unknown complex.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A' : Type*} [Category* A'] [Abelian A'] [EnoughInjectives A'] [HasDerivedCategory A']
  [HasDerivedCategory B]
  (R : A ⥤ A') [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  (P : A' ⥤ B) [P.Additive]

/-- On bounded below complexes of injectives, `H^q` of `R ⋙ P` applied degreewise is the
cohomology of the right derived functor of `P` at `R` of the object of `D⁺(A)`, provided `R`
carries injective objects to objects right acyclic for `P`. -/
def injectivePageOneIso (hR : ∀ X : A, Injective X → P.rightAcyclic (R.obj X)) :
    (InjectiveObject.ι A).mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι A ⋙
        (R ⋙ P).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) q ≅
      DerivedCategory.Plus.injectiveObjectQh A ⋙ R.mapDerivedCategoryPlus ⋙
        P.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor B q := by
  let J := (InjectiveObject.ι A).mapHomotopyCategoryPlus
  let H := HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) q
  let H' := DerivedCategory.Plus.homologyFunctor B q
  have hiso (X : HomotopyCategory.Plus (InjectiveObject A)) :
      IsIso ((Functor.whiskerLeft (J ⋙ R.mapHomotopyCategoryPlus)
        P.rightDerivedFunctorPlusUnith).app X) := by
    let Y := (J ⋙ R.mapHomotopyCategoryPlus).obj X
    let α := (P.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
      DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso _)
    have h₁ : IsIso (α.app Y) :=
      P.isIso_totalRightDerivedUnit_app_of_rightAcyclic Y.obj.as
        ((HomotopyCategory.plus_quotient_obj_iff Y.obj.as).1 Y.property)
        (fun n => hR _ (X.obj.as.X n).property)
    let e := Functor.rightDerivedNatIso _ P.rightDerivedFunctorPlus α
      P.rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso _) (Iso.refl _)
    have h₂ : P.rightDerivedFunctorPlusUnith.app Y =
        α.app Y ≫ e.hom.app (DerivedCategory.Plus.Qh.obj Y) := by
      simpa [e] using (Functor.rightDerivedNatTrans_app _ P.rightDerivedFunctorPlus α
        P.rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso _) (𝟙 _) Y).symm
    change IsIso (P.rightDerivedFunctorPlusUnith.app Y)
    rw [h₂]
    infer_instance
  have : IsIso (Functor.whiskerLeft (J ⋙ R.mapHomotopyCategoryPlus)
      P.rightDerivedFunctorPlusUnith) := NatIso.isIso_of_isIso_app _
  let step₁ : HomotopyCategory.Plus.ι A ⋙ (R ⋙ P).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (R ⋙ P).mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι B :=
    ((HomotopyCategory.plus B).liftCompιIso
      (HomotopyCategory.Plus.ι A ⋙ (R ⋙ P).mapHomotopyCategory (ComplexShape.up ℤ)) _).symm
  let step₂ : (R ⋙ P).mapHomotopyCategoryPlus ≅
      R.mapHomotopyCategoryPlus ⋙ P.mapHomotopyCategoryPlus :=
    (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (R ⋙ P))).symm
  let e₁ : HomotopyCategory.Plus.ι A ⋙ (R ⋙ P).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ H ≅
      (R.mapHomotopyCategoryPlus ⋙ P.mapHomotopyCategoryPlus) ⋙ DerivedCategory.Plus.Qh ⋙ H' :=
    (Iso.refl _ : _ ≅ (HomotopyCategory.Plus.ι A ⋙
        (R ⋙ P).mapHomotopyCategory (ComplexShape.up ℤ)) ⋙ H) ≪≫
      Functor.isoWhiskerRight step₁ H ≪≫
      (Iso.refl _ : _ ≅ (R ⋙ P).mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι B ⋙ H) ≪≫
      Functor.isoWhiskerRight step₂ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.Plus.QhHomologyIso B q).symm
  let e₂ : (J ⋙ R.mapHomotopyCategoryPlus) ⋙ P.mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh ≅
      (J ⋙ R.mapHomotopyCategoryPlus) ⋙ DerivedCategory.Plus.Qh ⋙ P.rightDerivedFunctorPlus :=
    asIso (Functor.whiskerLeft (J ⋙ R.mapHomotopyCategoryPlus) P.rightDerivedFunctorPlusUnith)
  exact Functor.isoWhiskerLeft J e₁ ≪≫
    (Iso.refl _ : _ ≅ ((J ⋙ R.mapHomotopyCategoryPlus) ⋙ P.mapHomotopyCategoryPlus ⋙
      DerivedCategory.Plus.Qh) ⋙ H') ≪≫
    Functor.isoWhiskerRight e₂ H' ≪≫
    (Iso.refl _ : _ ≅ (J ⋙ R.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
      P.rightDerivedFunctorPlus ⋙ H') ≪≫
    Functor.isoWhiskerRight (Functor.isoWhiskerLeft J R.mapDerivedCategoryPlusFactorsh.symm) _ ≪≫
    (Iso.refl _ : _ ≅ DerivedCategory.Plus.injectiveObjectQh A ⋙ R.mapDerivedCategoryPlus ⋙
      P.rightDerivedFunctorPlus ⋙ H')

/-- The page-one identification on the homotopy category, read through the quasi-inverse of
`K⁺(Inj A) ≌ D⁺(A)`. -/
def derivedPageOneIsoAux (e : F ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) p ≅ R ⋙ P) :
    derivedFunctor F ⋙ CategoryTheory.SpectralSequence.pageFunctor B _ 1 1 le_rfl ⋙
        HomologicalComplex.eval B _ (p, q) ≅
      (DerivedCategory.Plus.injectiveObjectEquivalence A).inverse ⋙
        (InjectiveObject.ι A).mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι A ⋙
          (R ⋙ P).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            HomotopyCategory.homologyFunctor B (ComplexShape.up ℤ) q :=
  (Iso.refl _ : _ ≅ ((DerivedCategory.Plus.injectiveObjectEquivalence A).inverse ⋙
      (InjectiveObject.ι A).mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι A ⋙
        homotopyFunctor F) ⋙ (CategoryTheory.SpectralSequence.pageFunctor B _ 1 1 le_rfl ⋙
          HomologicalComplex.eval B _ (p, q))) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.injectiveObjectEquivalence A).inverse
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (InjectiveObject.ι A).mapHomotopyCategoryPlus
          (Functor.associator _ _ _ ≪≫
            Functor.isoWhiskerLeft (HomotopyCategory.Plus.ι A)
              (homotopyPageOneIso F p q (R ⋙ P) e)))

/-- The counit of `K⁺(Inj A) ≌ D⁺(A)`, with its functor written as `injectiveObjectQh`. -/
def injectiveObjectCounit :
    (DerivedCategory.Plus.injectiveObjectEquivalence A).inverse ⋙
        DerivedCategory.Plus.injectiveObjectQh A ≅ 𝟭 _ :=
  (DerivedCategory.Plus.injectiveObjectEquivalence A).counitIso

/-- **`E_1^{p,q} ≅ H^q(RP(R K))`, naturally in `K` in `D⁺(A)`**, when `F(-)^p ≅ R ⋙ P` for an
exact functor `R` carrying injective objects to objects right acyclic for `P`. -/
def derivedPageOneIsoOfRightAcyclic
    (e : F ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) p ≅ R ⋙ P)
    (hR : ∀ X : A, Injective X → P.rightAcyclic (R.obj X)) :
    derivedFunctor F ⋙ CategoryTheory.SpectralSequence.pageFunctor B _ 1 1 le_rfl ⋙
        HomologicalComplex.eval B _ (p, q) ≅
      R.mapDerivedCategoryPlus ⋙ P.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor B q :=
  derivedPageOneIsoAux F p q R P e ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.injectiveObjectEquivalence A).inverse
      (injectivePageOneIso q R P hR) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (injectiveObjectCounit (A := A)) _ ≪≫ Functor.leftUnitor _

/-- **`E_1^{p,q} ≅ H^q(RP(R K))`, naturally in `K` in `D⁺(A)`**, when `F(-)^p ≅ R ⋙ P` for an
exact functor `R` preserving injective objects. -/
def derivedPageOneIso [R.PreservesInjectiveObjects]
    (e : F ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) p ≅ R ⋙ P) :
    derivedFunctor F ⋙ CategoryTheory.SpectralSequence.pageFunctor B _ 1 1 le_rfl ⋙
        HomologicalComplex.eval B _ (p, q) ≅
      R.mapDerivedCategoryPlus ⋙ P.rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor B q :=
  derivedPageOneIsoOfRightAcyclic F p q R P e fun X hX =>
    have : Injective (R.obj X) := Functor.PreservesInjectiveObjects.injective_obj (F := R) hX
    Functor.rightAcyclic_of_injective P (R.obj X)

omit [HasDerivedCategory B] in
/-- **The first page vanishes in the columns where `F(-)^p` vanishes.** -/
theorem isZero_derivedFunctor_page_one (p q : ℤ)
    (hp : ∀ X : A, IsZero ((F.obj X).X p)) (K : DerivedCategory.Plus A) :
    IsZero ((((derivedFunctor F).obj K).page 1 le_rfl).X (p, q)) := by
  let Z := ((HomotopyCategory.Plus.ι A).obj ((InjectiveObject.ι A).mapHomotopyCategoryPlus.obj
    ((DerivedCategory.Plus.injectiveObjectEquivalence A).inverse.obj K))).as
  refine (Iso.isZero_iff ((complexPageOneIso F p q
    (F ⋙ HomologicalComplex.eval B (ComplexShape.up ℤ) p) (Iso.refl _)).app Z)).2 ?_
  refine (HomologicalComplex.exactAt_iff_isZero_homology _ q).1
    (ShortComplex.exact_of_isZero_X₂ _ (hp (Z.X q)))

end PageOne

/-! ### The abutment -/

section Abutment

variable [HasDerivedCategory B] (T : A ⥤ B) [T.Additive]
  (α : T.mapHomologicalComplex (ComplexShape.up ℤ) ⟶
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ rowZeroFunctor B)

omit [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B] in
/-- **The spectral sequence of a complex satisfying the hypotheses of Stacks 0133 abuts to the
cohomology of `T(Z^•)`.** -/
theorem abutsTo_complexFunctor (Z : CochainComplex A ℤ)
    (h : Hypotheses ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) (α.app Z)) :
    CategoryTheory.SpectralSequence.AbutsTo ((complexFunctor F).obj Z)
      (fun n => ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z).homology n) := by
  have hfin (n : ℤ) : {pq : ℤ × ℤ | pq.1 + pq.2 = n ∧ ¬ IsZero
      (((doubleComplex F Z).X pq.1).X pq.2)}.Finite := by
    refine ((h.diagonalFinite n).image fun p => (p, n - p)).subset ?_
    rintro ⟨p, q⟩ ⟨hpq, hz⟩
    have hq : q = n - p := by simp only at hpq; omega
    subst hq
    exact ⟨p, hz, rfl⟩
  have habuts := CochainComplex.Filtered.abutsTo_of_isDegreewiseFinite
    (doubleComplex F Z).totalFiltration₂
    (fun p n => (doubleComplex F Z).stepSubobject (fun (_ : ℤ) j => j) p n)
    (fun _ _ => (Subobject.mk_arrow _).symm) _ (fun _ _ _ => rfl) _ (fun _ _ _ => rfl) _
    (HomologicalComplex₂.pageIso₂ _)
    (HomologicalComplex₂.isDegreewiseFinite_totalFiltration₂ _ hfin)
  exact (habuts.of_iso fun n => (comparisonHomologyIso _ _ _ h n).symm).shiftStart zero_le_one

/-- **The spectral sequence of `K` in `D⁺(A)` abuts to `H^n(RT(K))`**, provided the hypotheses of
Stacks 0133 hold for every bounded below complex of injectives. -/
theorem abutsTo_derivedFunctor
    (h : ∀ (Z : CochainComplex A ℤ) (n : ℤ), Z.IsStrictlyGE n → (∀ q, Injective (Z.X q)) →
      Hypotheses ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z) (α.app Z))
    (K : DerivedCategory.Plus A) :
    CategoryTheory.SpectralSequence.AbutsTo ((derivedFunctor F).obj K)
      (fun n => (DerivedCategory.Plus.homologyFunctor B n).obj
        (T.rightDerivedFunctorPlus.obj K)) := by
  let X := (DerivedCategory.Plus.injectiveObjectEquivalence A).inverse.obj K
  let Y := (InjectiveObject.ι A).mapHomotopyCategoryPlus.obj X
  let Z : CochainComplex A ℤ := ((HomotopyCategory.Plus.ι A).obj Y).as
  obtain ⟨n, hZ⟩ := DerivedCategory.Plus.exists_isStrictlyGE_injectiveObject X
  have hinj (q : ℤ) : Injective (Y.obj.as.X q) := (X.obj.as.X q).property
  exact (abutsTo_complexFunctor F T α Z (h Z n hZ hinj)).of_iso fun m =>
    ((HomotopyCategory.homologyFunctorFactors B (ComplexShape.up ℤ) m).app
      ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj Z)).symm ≪≫
    ((DerivedCategory.Plus.QhHomologyIso B m).app (T.mapHomotopyCategoryPlus.obj Y)).symm ≪≫
    (DerivedCategory.Plus.homologyFunctor B m).mapIso
      ((asIso (T.rightDerivedFunctorPlusUnith.app Y)) ≪≫
        T.rightDerivedFunctorPlus.mapIso
          ((DerivedCategory.Plus.injectiveObjectEquivalence A).counitIso.app K))

end Abutment

end Stacks.DegreewiseSpectralSequence

end
