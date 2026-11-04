module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Homology.DerivedComplete
public import StacksFrontier.Homology.DerivedComplete.CompleteAdic

/-!
# Derived completeness and restriction of scalars

For a homomorphism `φ : A → B` of commutative rings and an ideal `I` of `A`, restriction of
scalars carries the derived-complete objects of `D(B)` for the extended ideal `I B` precisely to
the derived-complete objects of `D(A)` for `I`. Equivalently, the inverse image of
`D_comp(A, I)` under restriction of scalars is `D_comp(B, I B)`.

## Main results

* `isDerivedComplete_restrictScalars_iff`: derived completeness for an extended ideal is
  equivalent to derived completeness after restriction of scalars.
* `isIso_oneSubSmulShift_derived_restrictScalars_iff`: the elementwise statement, that
  `oneSubSmulShift` is invertible on `L` at `φ f` exactly when it is invertible on the
  restriction of `L` at `f`.

## References

* [The Stacks Project, Tag 0924](https://stacks.math.columbia.edu/tag/0924)
* [Bhatt--Scholze, *Projectivity of the Witt vector affine Grassmannian*][BS]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

noncomputable section

universe u v w

/-- Countable products of modules over a commutative ring are exact. -/
local instance (R : Type*) [CommRing R] :
    HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{w} R) :=
  moduleCat_hasExactLimitsOfShape_discrete.{w} R ℕ

/-- The derived category of modules over a commutative ring has countable products. -/
local instance (R : Type*) [CommRing R] :
    HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{w} R)) :=
  Stacks.DerivedProducts.hasProductsOfShape_derivedCategory

attribute [local instance] homologicalHomologyFunctorLinear derivedHomologyFunctorLinear

private lemma restrictScalars_map_oneSubSmulShift
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] (φ : A →+* B)
    (M : ModuleCat.{w} B) (f : A) :
    (ModuleCat.restrictScalars φ).map (oneSubSmulShift M (φ f)) ≫
        piComparison (ModuleCat.restrictScalars φ) (fun _ : ℕ => M) =
      piComparison (ModuleCat.restrictScalars φ) (fun _ : ℕ => M) ≫
        oneSubSmulShift ((ModuleCat.restrictScalars φ).obj M) f := by
  apply limit.hom_ext
  rintro ⟨n⟩
  simp only [oneSubSmulShift, milnorMap, Category.assoc, piComparison_comp_π, Pi.lift_π,
    Preadditive.comp_sub, Linear.comp_smul, Category.comp_id, ← Functor.map_comp,
    Functor.map_sub]
  ext x
  rfl

/-- The comparison isomorphism between the homology of the image of a complex under an exact
additive functor and the image of its homology. -/
private noncomputable def mapHomologicalComplexCompHomologyFunctorIso
    {C : Type u} [Category C] [Abelian C] [HasDerivedCategory C]
    {D : Type v} [Category D] [Abelian D] [HasDerivedCategory D]
    (F : Functor C D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℤ) :
    F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) n ≅
      HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F :=
  NatIso.ofComponents (fun K ↦ (K.sc n).mapHomologyIso F) (fun ψ ↦
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map ψ) F)

/-- The induced functor on derived categories commutes with the homology functors. -/
private noncomputable def mapDerivedCategoryCompHomologyFunctorIso
    {C : Type u} [Category C] [Abelian C] [HasDerivedCategory C]
    {D : Type v} [Category D] [Abelian D] [HasDerivedCategory D]
    (F : Functor C D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (n : ℤ) :
    F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n ≅
      DerivedCategory.homologyFunctor C n ⋙ F :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
    (DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n))
    (DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor C n ⋙ F)) _ _
    (Functor.isoWhiskerRight F.mapDerivedCategoryFactors
        (DerivedCategory.homologyFunctor D n) ≪≫
      Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
        (DerivedCategory.homologyFunctorFactors D n) ≪≫
      mapHomologicalComplexCompHomologyFunctorIso F n ≪≫
      Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C n).symm F)

private lemma isIso_oneSubSmulShift_restrictScalars_iff
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] (φ : A →+* B)
    (M : ModuleCat.{w} B) (f : A) :
    IsIso (oneSubSmulShift M (φ f)) ↔
      IsIso (oneSubSmulShift ((ModuleCat.restrictScalars φ).obj M) f) := by
  let F := ModuleCat.restrictScalars.{w} φ
  let c := piComparison F (fun _ : ℕ => M)
  have : IsIso c := by dsimp [c, F]; infer_instance
  rw [← isIso_iff_of_reflects_iso _ F, ← isIso_comp_right_iff _ c,
    restrictScalars_map_oneSubSmulShift, isIso_comp_left_iff]

/-- Restriction of scalars along `φ : A → B` reflects and preserves invertibility of the
difference map: `oneSubSmulShift` is invertible on the restriction of `L` at `f` exactly when it
is invertible on `L` at `φ f`. -/
public theorem isIso_oneSubSmulShift_derived_restrictScalars_iff
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] (φ : A →+* B)
    (L : DerivedCategory (ModuleCat.{w} B)) (f : A) :
    IsIso (oneSubSmulShift ((ModuleCat.restrictScalars φ).mapDerivedCategory.obj L) f) ↔
      IsIso (oneSubSmulShift L (φ f)) := by
  rw [DerivedCategory.isIso_iff, DerivedCategory.isIso_iff]
  refine forall_congr' fun i ↦ ?_
  rw [isIso_homology_map_oneSubSmulShift_iff, isIso_homology_map_oneSubSmulShift_iff]
  let F := ModuleCat.restrictScalars.{w} φ
  let e := (mapDerivedCategoryCompHomologyFunctorIso F i).app L
  have he :
      IsIso (oneSubSmulShift
          ((DerivedCategory.homologyFunctor (ModuleCat.{w} A) i).obj
            (F.mapDerivedCategory.obj L)) f) ↔
        IsIso (oneSubSmulShift
          ((DerivedCategory.homologyFunctor (ModuleCat.{w} B) i ⋙ F).obj L) f) := by
    rw [← isIso_comp_right_iff _ (Limits.Pi.map (fun _ : ℕ => e.hom)),
      oneSubSmulShift_naturality, isIso_comp_left_iff]
  exact he.trans (by
    simpa [F] using
      (isIso_oneSubSmulShift_restrictScalars_iff A B φ
        ((DerivedCategory.homologyFunctor (ModuleCat.{w} B) i).obj L) f).symm)

/-- A complex of `B`-modules is derived complete for the extension of `I` to
`B` if and only if its restriction to `A` is derived complete for `I`. Equivalently, the inverse
image of `D_comp(A, I)` under restriction of scalars is `D_comp(B, I B)`. -/
@[stacks 0924]
public theorem isDerivedComplete_restrictScalars_iff
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] (φ : A →+* B) (I : Ideal A)
    (L : DerivedCategory (ModuleCat.{w} B)) :
    IsDerivedComplete I ((ModuleCat.restrictScalars φ).mapDerivedCategory.obj L) ↔
      IsDerivedComplete (I.map φ) L := by
  refine ⟨fun hA b hb ↦ ?_, fun hB f hf ↦
    (isIso_oneSubSmulShift_derived_restrictScalars_iff A B φ L f).mpr
      (hB (φ f) (Ideal.mem_map_of_mem φ hf))⟩
  obtain ⟨J, -, hJ⟩ := exists_isRadical_ideal_isDerivedCompleteAt B L
  exact (hJ b).mp (Ideal.map_le_iff_le_comap.mpr (fun f hf ↦ (hJ (φ f)).mpr
    ((isIso_oneSubSmulShift_derived_restrictScalars_iff A B φ L f).mp (hA f hf))) hb)

end

end
