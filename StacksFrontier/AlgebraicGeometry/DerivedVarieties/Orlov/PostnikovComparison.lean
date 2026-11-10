module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.ResolutionPostnikov
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.PointSupportedPushforward
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.SpecFieldPerfectSums
public import StacksFrontier.CategoryTheory.Triangulated.SequentialPostnikovComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackPseudoCoherent

/-!
# Comparing the transforms of the two Postnikov systems of [Stacks, Section 0G07]

Let `k` be a field, `X` and `Y` proper smooth `k`-schemes, `F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` a
`k`-linear exact fully faithful functor, `⋯ → ℰ₁ ⊠ 𝒢₁ → ℰ₀ ⊠ 𝒢₀ → 𝒪_Δ` a resolution of the
diagonal, and `𝓕` a coherent `𝒪_X`-module supported at a closed point. Write
`Ψ'(N) = R pr_{2,*}(L pr_1^*𝓕 ⊗^𝐋 N)` on `D(𝒪_{X ×_k X})` and `Ψ(N)` for the same transform on
`D(𝒪_{X ×_k Y})`. The source computes

`F(Ψ'(ℰᵢ ⊠ 𝒢ᵢ)) = F(Γ(X, 𝓕 ⊗ ℰᵢ) ⊗_k 𝒢ᵢ) = Γ(X, 𝓕 ⊗ ℰᵢ) ⊗_k F(𝒢ᵢ) = Ψ(ℰᵢ ⊠ F(𝒢ᵢ))`,

compatibly with the differentials, and concludes by uniqueness of Postnikov systems that the
systems `n ↦ F(Ψ'(Mₙ[n]))` and `n ↦ Ψ(Kₙ[n])` are isomorphic. This file carries that out:
the identifications are `AlgebraicGeometry.boxTransformMap` on both sides and
`AlgebraicGeometry.twistApply_comm` in the middle, with `V = Rf_*(𝓕 ⊗ ℰᵢ)` a finite sum of copies
of `𝒪_{Spec k}[0]` because `𝓕 ⊗ ℰᵢ` is supported at a point.

## Main results

* `AlgebraicGeometry.boxTransformMap_naturality`: naturality of the transform of a derived
  external product in both factors at once.
* `AlgebraicGeometry.DiagonalResolution.nonempty_sequence_iso`: the comparison of the systems.

## References

* [Stacks Project, Section 0G07](https://stacks.math.columbia.edu/tag/0G07)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

section Naturality

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- **Naturality of the transform of a derived external product in both factors.** -/
theorem boxTransformMap_naturality (𝓕 : DerivedCategory X.Modules)
    {E E' : DerivedCategory X.Modules} {B B' : DerivedCategory Y.Modules} (a : E ⟶ E')
    (b : B ⟶ B') :
    ((derivedTensorProductFunctor Y.toRingedSpace.sheaf).map
        ((dpull g).map ((dpush f).map
          (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj 𝓕).map a)))).app B ≫
      ((derivedTensorProductFunctor Y.toRingedSpace.sheaf).obj
        ((dpull g).obj ((dpush f).obj
          (((derivedTensorProductFunctor X.toRingedSpace.sheaf).obj 𝓕).obj E')))).map b ≫
      boxTransformMap f g 𝓕 E' B' =
    boxTransformMap f g 𝓕 E B ≫ (kernelIntegralTransform f g 𝓕).map (derivedBoxMap f g a b) :=
  (congrArg (_ ≫ ·) (boxTransformMap_naturality_right f g 𝓕 E' b)).trans
    ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (boxTransformMap_naturality_left f g 𝓕 a B)).trans
    ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) ((kernelIntegralTransform f g 𝓕).map_comp _ _).symm))))

end Naturality

/-- The objects of a sequential Postnikov system lie in a triangulated subcategory containing
its terms. -/
theorem _root_.CategoryTheory.Triangulated.SequentialPostnikovSystem.prop_obj {D : Type*}
    [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ t : ℤ, (shiftFunctor D t).Additive] [Pretriangulated D] {X : ℕ → D}
    {d : ∀ n, X (n + 1) ⟶ X n} (P : Triangulated.SequentialPostnikovSystem X d)
    (S : ObjectProperty D) [S.IsTriangulated] (hS : ∀ {K L : D}, (K ≅ L) → S K → S L)
    (hX : ∀ n, S (X n)) (n : ℕ) : S (P.obj n) := by
  induction n with
  | zero => exact hS (asIso (P.π 0)).symm (hX 0)
  | succ n ih =>
    obtain ⟨Z, hZ, ⟨e⟩⟩ := S.ext_of_isTriangulatedClosed₂'
      (Pretriangulated.Triangle.mk (P.π (n + 1)) (P.p n) (P.δ n)).invRotate
      (Pretriangulated.inv_rot_of_distTriang _ (P.distinguished n))
      (S.le_shift (-1 : ℤ) _ ih) (hX (n + 1))
    exact hS e.symm hZ

/-- **A fully faithful exact functor has no negative `Ext` between the images of heart objects**,
read in the ambient derived category. -/
theorem hom_shift_obj_eq_zero_of_fullyFaithful {X Y : Scheme.{u}}
    (F : PerfectDerivedCategory X ⥤ PerfectDerivedCategory Y) (hFF : F.FullyFaithful)
    [F.CommShift ℤ] [F.IsTriangulated] (X₁ X₂ : PerfectDerivedCategory X) (h₁ : X₁.obj.IsLE 0)
    (h₂ : X₂.obj.IsGE 0) (s : ℤ) (hs : 0 < s) (c : (F.obj X₁).obj⟦s⟧ ⟶ (F.obj X₂).obj) :
    c = 0 := by
  let e := ((ObjectProperty.ι (fun K : DerivedCategory Y.Modules =>
    IsPerfect (X := Y.toRingedSpace) K)).commShiftIso s).app (F.obj X₁)
  have h0 := map_shift_hom_eq_zero_of_fullyFaithful F hFF X₁ X₂ h₁ h₂ s hs
    (ObjectProperty.homMk (e.hom ≫ c))
  have h1 : e.hom ≫ c = 0 := congrArg (fun x => x.hom) h0
  rwa [Preadditive.IsIso.comp_left_eq_zero] at h1

section Comparison

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} (B : Over (Spec (.of k)))
  [Smooth A.hom] [IsProper A.hom] (R : DiagonalResolution A.hom)
  (𝓕 : A.left.Modules) (h𝓕 : IsPerfect (X := A.left.toRingedSpace)
    ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕))

namespace DiagonalResolution

/-- `V = Rf_*(𝓕 ⊗ ℰₙ)`, as a perfect object of `D(𝒪_{Spec k})`. -/
def twistCoefficient (n : ℕ) : PerfectDerivedCategory (Spec (.of k)) :=
  ⟨(dpush A.hom).obj (((derivedTensorProductFunctor A.left.toRingedSpace.sheaf).obj
      ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).obj
      ((DerivedCategory.singleFunctor A.left.Modules 0).obj (R.left n))),
    isPerfect_dpush_of_perfect_of_isProper A.hom _
      (isPerfect_dtenR _ _ h𝓕 (isPerfect_singleFunctor_of_isFiniteLocallyFree A.left (R.left n)
        (R.left_finiteLocallyFree n)))⟩

/-- The morphism `Rf_*(𝓕 ⊗ a) : V(ℰ) ⟶ V(ℰ')` attached to `a : ℰ ⟶ ℰ'`. -/
def twistCoefficientMap {i j : ℕ} (a : R.left i ⟶ R.left j) :
    R.twistCoefficient 𝓕 h𝓕 i ⟶ R.twistCoefficient 𝓕 h𝓕 j :=
  ObjectProperty.homMk ((dpush A.hom).map
    (((derivedTensorProductFunctor A.left.toRingedSpace.sheaf).obj
      ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).map
      ((DerivedCategory.singleFunctor A.left.Modules 0).map a)))

/-- `Rf_*(𝓕 ⊗ ℰₙ)` lies in degrees `≥ 0`. -/
theorem isGE_twistCoefficient (n : ℕ) : (R.twistCoefficient 𝓕 h𝓕 n).obj.IsGE 0 :=
  Stacks.AlgebraicGeometry.ProperSupportCoherent.isGE_derivedPushforward A.hom _ 0
    (isGE_dtenR_single_of_isFlat _ inferInstance (R.left n)
      (AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree _
        (R.left_finiteLocallyFree n)))

/-- For `𝓕` supported on a closed subset of an affine open, `Rf_*(𝓕 ⊗ ℰₙ)` lies in degrees
`≤ 0`. -/
theorem isLE_twistCoefficient (h𝓕qc : 𝓕.IsQuasicoherent) {U : A.left.Opens}
    (hU : IsAffineOpen U) {Z : Set A.left} (hZ : IsClosed Z) (hZU : Z ⊆ U)
    (hsupp : SheafOfModules.supp 𝓕 ⊆ Z) (n : ℕ) : (R.twistCoefficient 𝓕 h𝓕 n).obj.IsLE 0 := by
  have : IsAffine U.toScheme := hU
  have hE := isPerfect_singleFunctor_of_isFiniteLocallyFree A.left (R.left n)
    (R.left_finiteLocallyFree n)
  exact (DerivedCategory.isLE_iff _ 0).2
    fun i hi => isZero_homology_dpush_dtenR_of_supp A.hom hZ hZU 𝓕 hsupp h𝓕qc
      ((DerivedCategory.singleFunctor A.left.Modules 0).obj (R.left n))
      (isQCohAll_of_isPerfect hE) 0 inferInstance i hi

/-- **For `𝓕` supported at a closed point of an affine open, `Rf_*(𝓕 ⊗ ℰₙ)` is a finite sum of
copies of `𝒪_{Spec k}[0]`.** -/
theorem exists_iso_twistCoefficient (h𝓕qc : 𝓕.IsQuasicoherent) {U : A.left.Opens}
    (hU : IsAffineOpen U) {Z : Set A.left} (hZ : IsClosed Z) (hZU : Z ⊆ U)
    (hsupp : SheafOfModules.supp 𝓕 ⊆ Z) (n : ℕ) :
    ∃ r : ℕ, Nonempty (R.twistCoefficient 𝓕 h𝓕 n ≅
      ⨁ fun _ : Fin r => (perfectUnitSpecField (k := k))) := by
  have := R.isGE_twistCoefficient 𝓕 h𝓕 n
  have := R.isLE_twistCoefficient 𝓕 h𝓕 h𝓕qc hU hZ hZU hsupp n
  have := isCoherent_homology_of_isPerfect' (Spec (.of k)) _ (R.twistCoefficient 𝓕 h𝓕 n).property 0
  obtain ⟨_, _⟩ := Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent
    ((DerivedCategory.homologyFunctor (Spec (.of k)).Modules 0).obj
      (R.twistCoefficient 𝓕 h𝓕 n).obj)
  exact exists_iso_biproduct_perfectUnitSpecField _

include h𝓕 in
/-- `AlgebraicGeometry.boxTransformMap` is an isomorphism on `𝓕` and `ℰₙ ⊠ 𝒢` for perfect `𝒢`. -/
private theorem isIso_boxTransformMap_single (n : ℕ) (G : DerivedCategory B.left.Modules)
    (hG : IsPerfect (X := B.left.toRingedSpace) G) :
    IsIso (boxTransformMap A.hom B.hom ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)
      ((DerivedCategory.singleFunctor A.left.Modules 0).obj (R.left n)) G) :=
  isIso_boxTransformMap A.hom B.hom _ _ G (isQCohAll_of_isPerfect h𝓕)
    (isQCohAll_of_isPerfect (isPerfect_singleFunctor_of_isFiniteLocallyFree A.left (R.left n)
      (R.left_finiteLocallyFree n)))
    (isQCohAll_of_isPerfect hG)

/-- `Ψ'(ℰₙ ⊠ 𝒢ₙ) ≅ V ⊗ 𝒢ₙ` on `X`, the inverse of `AlgebraicGeometry.boxTransformMap`. -/
def origTransformIso (n : ℕ) :
    (kernelIntegralTransform A.hom A.hom
        ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).obj (R.origTerm n) ≅
      ((perfectTwist A.hom (R.twistCoefficient 𝓕 h𝓕 n)).obj
        (rightPerfect A R R.isPerfect_single_right n)).obj :=
  haveI hb := isIso_boxTransformMap A.hom A.hom
    ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)
    ((DerivedCategory.singleFunctor A.left.Modules 0).obj (R.left n))
    (imageOfRight A A R (𝟭 _) R.isPerfect_single_right n)
    (isQCohAll_of_isPerfect h𝓕)
    (isQCohAll_of_isPerfect (isPerfect_singleFunctor_of_isFiniteLocallyFree A.left (R.left n)
      (R.left_finiteLocallyFree n)))
    (isQCohAll_of_isPerfect (R.isPerfect_single_right n))
  (@asIso _ _ _ _ (boxTransformMap A.hom A.hom _ _ _) hb).symm

include h𝓕 in
/-- The transforms `Ψ'(ℰₙ ⊠ 𝒢ₙ)` are perfect. -/
theorem isPerfect_origTransform (n : ℕ) :
    IsPerfect (X := A.left.toRingedSpace)
      ((kernelIntegralTransform A.hom A.hom
        ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).obj (R.origTerm n)) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := A.left.toRingedSpace)
    (R.origTransformIso 𝓕 h𝓕 n).symm
    ((perfectTwist A.hom (R.twistCoefficient 𝓕 h𝓕 n)).obj
      (rightPerfect A R R.isPerfect_single_right n)).property

/-- The transform `Ψ'(ℰₙ ⊠ 𝒢ₙ)`, as a perfect object. -/
abbrev origTransformPerfect (n : ℕ) : PerfectDerivedCategory A.left :=
  ⟨_, R.isPerfect_origTransform 𝓕 h𝓕 n⟩

/-- **The square of `Ψ'` on (0G09)**: the transform of a pure map `a ⊠ b` is
`V(a) ⊗ b` under `Ψ'(ℰ ⊠ 𝒢) ≅ V(ℰ) ⊗ 𝒢`. -/
theorem origTransformIso_naturality {i j : ℕ} (a : R.left i ⟶ R.left j)
    (b : R.right i ⟶ R.right j) :
    (kernelIntegralTransform A.hom A.hom
        ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).map
        (derivedBoxMap A.hom A.hom ((DerivedCategory.singleFunctor A.left.Modules 0).map a)
          ((DerivedCategory.singleFunctor A.left.Modules 0).map b)) ≫
      (R.origTransformIso 𝓕 h𝓕 j).hom =
    (R.origTransformIso 𝓕 h𝓕 i).hom ≫
      (((perfectTwistMap A.hom (R.twistCoefficientMap 𝓕 h𝓕 a)).app
          (rightPerfect A R R.isPerfect_single_right i)).hom ≫
        ((perfectTwist A.hom (R.twistCoefficient 𝓕 h𝓕 j)).map
          (ObjectProperty.homMk ((DerivedCategory.singleFunctor A.left.Modules 0).map b) :
            rightPerfect A R R.isPerfect_single_right i ⟶
              rightPerfect A R R.isPerfect_single_right j)).hom) := by
  have h := boxTransformMap_naturality A.hom A.hom
    ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)
    ((DerivedCategory.singleFunctor A.left.Modules 0).map a)
    ((DerivedCategory.singleFunctor A.left.Modules 0).map b)
  have hi := isIso_boxTransformMap_single A R 𝓕 h𝓕 i
    (imageOfRight A A R (𝟭 _) R.isPerfect_single_right i)
    (R.isPerfect_single_right i)
  have hj := isIso_boxTransformMap_single A R 𝓕 h𝓕 j
    (imageOfRight A A R (𝟭 _) R.isPerfect_single_right j)
    (R.isPerfect_single_right j)
  change _ ≫ inv (boxTransformMap A.hom A.hom _ _
      (imageOfRight A A R (𝟭 _) R.isPerfect_single_right j)) =
    inv (boxTransformMap A.hom A.hom _ _ (imageOfRight A A R (𝟭 _) R.isPerfect_single_right i)) ≫ _
  refine (IsIso.comp_inv_eq _).2 (((IsIso.eq_inv_comp _).2 ?_).trans (Category.assoc _ _ _).symm)
  exact ((Category.assoc _ _ _).trans h).symm

variable (F : PerfectDerivedCategory A.left ⥤ PerfectDerivedCategory B.left)
  [F.CommShift ℤ] [F.IsTriangulated]
  (hF : letI := modulesLinear k A; letI := modulesLinear k B; F.Linear k)
  (r : ℕ → ℕ) (eV : ∀ n, R.twistCoefficient 𝓕 h𝓕 n ≅
    ⨁ fun _ : Fin (r n) => (perfectUnitSpecField (k := k)))

/-- The category of functors from the perfect derived category of `A` to the derived category
of `B` has finite biproducts. -/
instance : HasFiniteBiproducts (PerfectDerivedCategory A.left ⥤ DerivedCategory B.left.Modules) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- **`F(Ψ'(ℰₙ ⊠ 𝒢ₙ)) ⟶ Ψ(ℰₙ ⊠ F(𝒢ₙ))`**: `F(V ⊗ 𝒢ₙ) = V ⊗ F(𝒢ₙ)` between the two transforms
of derived external products. -/
def imgComparisonHom (n : ℕ) :
    (F.obj (R.origTransformPerfect 𝓕 h𝓕 n)).obj ⟶
      (kernelIntegralTransform A.hom B.hom
        ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).obj
        (AlgebraicGeometry.transformedTerm A B R F R.isPerfect_single_right n) :=
  (F.map (ObjectProperty.isoMk _ (R.origTransformIso 𝓕 h𝓕 n)).hom).hom ≫
    (Linear.scalarBiproductIso (twistThenApply A.hom F) (applyThenTwist B.hom F)
      (twistApplyUnitIso A.hom B.hom F) (eV n)).hom.app
        (rightPerfect A R R.isPerfect_single_right n) ≫
    boxTransformMap A.hom B.hom _ _ (imageOfRight A B R F R.isPerfect_single_right n)

/-- The comparison morphism `imgComparisonHom` is an isomorphism. -/
theorem isIso_imgComparisonHom (n : ℕ) : IsIso (R.imgComparisonHom B 𝓕 h𝓕 F r eV n) := by
  have hb := isIso_boxTransformMap_single B R 𝓕 h𝓕 n
    (imageOfRight A B R F R.isPerfect_single_right n)
    (F.obj (rightPerfect A R R.isPerfect_single_right n)).property
  let ι₀ : R.origTransformPerfect 𝓕 h𝓕 n ≅
      (perfectTwist A.hom (R.twistCoefficient 𝓕 h𝓕 n)).obj
        (rightPerfect A R R.isPerfect_single_right n) :=
    ObjectProperty.isoMk _ (R.origTransformIso 𝓕 h𝓕 n)
  have h₁ : IsIso (F.map ι₀.hom).hom :=
    Iso.isIso_hom ((ObjectProperty.ι _).mapIso (F.mapIso ι₀))
  exact IsIso.comp_isIso' h₁ (IsIso.comp_isIso' (Iso.isIso_hom ((Linear.scalarBiproductIso
    (twistThenApply A.hom F) (applyThenTwist B.hom F) (twistApplyUnitIso A.hom B.hom F) (eV n)).app
      (rightPerfect A R R.isPerfect_single_right n))) hb)

/-- The comparison as an isomorphism. -/
def imgComparison (n : ℕ) :
    (F.obj (R.origTransformPerfect 𝓕 h𝓕 n)).obj ≅
      (kernelIntegralTransform A.hom B.hom
        ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).obj
        (AlgebraicGeometry.transformedTerm A B R F R.isPerfect_single_right n) :=
  @asIso _ _ _ _ _ (R.isIso_imgComparisonHom B 𝓕 h𝓕 F r eV n)

omit [IsProper A.hom] [Smooth A.hom] in
/-- The pasting of the four squares behind `imgComparison_naturality`. -/
theorem comparison_paste {C : Type*} [Category C]
    {P Q T₁ T₂ T₃ U₁ U₂ U₃ W₁ W₂ : C} (h₁ : P ⟶ Q) (i : Q ⟶ T₃) (i' : P ⟶ T₁) (Lt : T₁ ⟶ T₂)
    (Rt : T₂ ⟶ T₃) (S : T₃ ⟶ U₃) (S' : T₂ ⟶ U₂) (S₁ : T₁ ⟶ U₁) (La : U₁ ⟶ U₂) (Ra : U₂ ⟶ U₃)
    (b : U₃ ⟶ W₂) (b₁ : U₁ ⟶ W₁) (ψ : W₁ ⟶ W₂)
    (hM : h₁ ≫ i = i' ≫ Lt ≫ Rt) (hG : Rt ≫ S = S' ≫ Ra) (hV : Lt ≫ S' = S₁ ≫ La)
    (hT : La ≫ Ra ≫ b = b₁ ≫ ψ) :
    h₁ ≫ i ≫ S ≫ b = (i' ≫ S₁ ≫ b₁) ≫ ψ := by
  rw [← Category.assoc, hM, Category.assoc, Category.assoc, reassoc_of% hG, reassoc_of% hV, hT]
  simp only [Category.assoc]

include hF in
/-- **The comparison commutes with the transforms of pure maps** `a ⊠ b` and `a ⊠ F(b)`. -/
theorem imgComparison_naturality {n : ℕ} (a : R.left (n + 1) ⟶ R.left n)
    (b : R.right (n + 1) ⟶ R.right n) :
    (F.map (ObjectProperty.homMk ((kernelIntegralTransform A.hom A.hom
        ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).map
        (derivedBoxMap A.hom A.hom ((DerivedCategory.singleFunctor A.left.Modules 0).map a)
          ((DerivedCategory.singleFunctor A.left.Modules 0).map b))) :
        R.origTransformPerfect 𝓕 h𝓕 (n + 1) ⟶ R.origTransformPerfect 𝓕 h𝓕 n)).hom ≫
      R.imgComparisonHom B 𝓕 h𝓕 F r eV n =
    R.imgComparisonHom B 𝓕 h𝓕 F r eV (n + 1) ≫
      (kernelIntegralTransform A.hom B.hom
        ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).map
        (derivedBoxMap A.hom B.hom ((DerivedCategory.singleFunctor A.left.Modules 0).map a)
          (imageOfRightMap A B R F R.isPerfect_single_right b)) := by
  let : Linear k (Spec (.of k)).Modules := modulesLinear k (specFieldOver k)
  let : Linear k B.left.Modules := modulesLinear k B
  have := twistThenApply_linear A B F hF
  have := applyThenTwist_linear A B F
  let G' := rightPerfect A R R.isPerfect_single_right (n + 1)
  let β : G' ⟶ rightPerfect A R R.isPerfect_single_right n :=
    ObjectProperty.homMk ((DerivedCategory.singleFunctor A.left.Modules 0).map b)
  let φa := R.twistCoefficientMap 𝓕 h𝓕 a
  have hM₀ : (ObjectProperty.homMk ((kernelIntegralTransform A.hom A.hom
        ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).map
        (derivedBoxMap A.hom A.hom ((DerivedCategory.singleFunctor A.left.Modules 0).map a)
          ((DerivedCategory.singleFunctor A.left.Modules 0).map b))) :
        R.origTransformPerfect 𝓕 h𝓕 (n + 1) ⟶ R.origTransformPerfect 𝓕 h𝓕 n) ≫
      (ObjectProperty.isoMk _ (R.origTransformIso 𝓕 h𝓕 n)).hom =
      (ObjectProperty.isoMk _ (R.origTransformIso 𝓕 h𝓕 (n + 1))).hom ≫
        (perfectTwistMap A.hom φa).app G' ≫
          (perfectTwist A.hom (R.twistCoefficient 𝓕 h𝓕 n)).map β := by
    ext
    exact R.origTransformIso_naturality 𝓕 h𝓕 a b
  have hM : (F.map (ObjectProperty.homMk ((kernelIntegralTransform A.hom A.hom
        ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).map
        (derivedBoxMap A.hom A.hom ((DerivedCategory.singleFunctor A.left.Modules 0).map a)
          ((DerivedCategory.singleFunctor A.left.Modules 0).map b))) :
        R.origTransformPerfect 𝓕 h𝓕 (n + 1) ⟶ R.origTransformPerfect 𝓕 h𝓕 n)).hom ≫
      (F.map (ObjectProperty.isoMk _ (R.origTransformIso 𝓕 h𝓕 n)).hom).hom =
      (F.map (ObjectProperty.isoMk _ (R.origTransformIso 𝓕 h𝓕 (n + 1))).hom).hom ≫
        ((twistThenApply A.hom F).map φa).app G' ≫
          ((twistThenApply A.hom F).obj (R.twistCoefficient 𝓕 h𝓕 n)).map β := by
    have := congrArg (fun x => (F.map x).hom) hM₀
    simp only [Functor.map_comp] at this
    exact this
  have hV := NatTrans.congr_app (twistApply_comm A B F hF (eV (n + 1)) (eV n) φa) G'
  have hG := (Linear.scalarBiproductIso (twistThenApply A.hom F) (applyThenTwist B.hom F)
      (twistApplyUnitIso A.hom B.hom F) (eV n)).hom.naturality β
  have hT := boxTransformMap_naturality A.hom B.hom
    ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)
    ((DerivedCategory.singleFunctor A.left.Modules 0).map a)
    (imageOfRightMap A B R F R.isPerfect_single_right b)
  exact comparison_paste _ _ _ _ _ _ _ _ _ _ _ _ _ hM hG hV hT

include hF in
/-- **The comparison commutes with the transforms of the differentials** of (0G09) and (0G0A),
read as `κ(t)` for one tensor `t` in `Hom(ℰₙ₊₁, ℰₙ) ⊗ Hom(𝒢ₙ₊₁, 𝒢ₙ)`. -/
theorem imgComparison_kappa (n : ℕ)
    (t : letI := modulesLinear k A;
      (R.left (n + 1) ⟶ R.left n) ⊗[k] (R.right (n + 1) ⟶ R.right n)) :
    letI := modulesLinear k A
    letI := modulesLinear k B
    letI : Linear k (pullback A.hom A.hom).Modules := modulesLinear k (overPullback k A A)
    letI : Linear k (pullback A.hom B.hom).Modules := modulesLinear k (overPullback k A B)
    (F.map (ObjectProperty.homMk ((kernelIntegralTransform A.hom A.hom
        ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).map
        ((transformedBoxPairing A A R (𝟭 _) R.isPerfect_single_right
          (id_linear (A := A))).κ (n + 1) n t)) :
        R.origTransformPerfect 𝓕 h𝓕 (n + 1) ⟶ R.origTransformPerfect 𝓕 h𝓕 n)).hom ≫
      R.imgComparisonHom B 𝓕 h𝓕 F r eV n =
    R.imgComparisonHom B 𝓕 h𝓕 F r eV (n + 1) ≫
      (kernelIntegralTransform A.hom B.hom
        ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).map
        ((transformedBoxPairing A B R F R.isPerfect_single_right hF).κ (n + 1) n t) := by
  let := modulesLinear k A
  induction t using TensorProduct.inductionOn with
  | tmul a b =>
    have e₁ := by
      let : Linear k (pullback A.hom A.hom).Modules := modulesLinear k (overPullback k A A)
      exact (transformedBoxPairing A A R (𝟭 _) R.isPerfect_single_right
        (id_linear (A := A))).κ_tmul (n + 1) n a b
    have e₂ := by
      let := modulesLinear k B
      let : Linear k (pullback A.hom B.hom).Modules := modulesLinear k (overPullback k A B)
      exact (transformedBoxPairing A B R F R.isPerfect_single_right hF).κ_tmul (n + 1) n a b
    rw [e₁, e₂]
    exact R.imgComparison_naturality B 𝓕 h𝓕 F hF r eV a b
  | add t t' ht ht' =>
    have hadd : ∀ (x y : (kernelIntegralTransform A.hom A.hom
          ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).obj (R.origTerm (n + 1)) ⟶
          (kernelIntegralTransform A.hom A.hom
            ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).obj (R.origTerm n)),
        (ObjectProperty.homMk (x + y) :
          R.origTransformPerfect 𝓕 h𝓕 (n + 1) ⟶ R.origTransformPerfect 𝓕 h𝓕 n) =
        ObjectProperty.homMk x + ObjectProperty.homMk y := fun x y => by ext; rfl
    rw [map_add, map_add, Functor.map_add, hadd, Functor.map_add, Functor.map_add]
    change ((F.map _).hom + (F.map _).hom) ≫ _ = _
    rw [Preadditive.add_comp, Preadditive.comp_add, ht, ht']

include h𝓕 in
/-- The transforms `Ψ'(ℰₙ ⊠ 𝒢ₙ)` lie in degrees `≥ 0`. -/
theorem isGE_origTransform (n : ℕ) :
    ((kernelIntegralTransform A.hom A.hom
      ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).obj (R.origTerm n)).IsGE 0 := by
  have hV := Stacks.Cohomology.DerivedInternalHomPullback.isGE_derivedPullback_obj_of_isFlat
    A.hom.toLRSHom.toShHom (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom A.hom)
    (R.twistCoefficient 𝓕 h𝓕 n).obj 0 (R.isGE_twistCoefficient 𝓕 h𝓕 n)
  have h : ((perfectTwist A.hom (R.twistCoefficient 𝓕 h𝓕 n)).obj
      (rightPerfect A R R.isPerfect_single_right n)).obj.IsGE 0 :=
    isGE_dtenR_single_of_isFlat _ hV (R.right n)
      (AlgebraicGeometry.SheafOfModules.isFlat_of_isFiniteLocallyFree _
        (R.right_finiteLocallyFree n))
  exact DerivedCategory.TStructure.t.isGE_of_iso (R.origTransformIso 𝓕 h𝓕 n).symm 0

include h𝓕 in
/-- For `𝓕` supported on a closed subset of an affine open, the transforms `Ψ'(ℰₙ ⊠ 𝒢ₙ)` lie
in degrees `≤ 0`. -/
theorem isLE_origTransform (h𝓕qc : 𝓕.IsQuasicoherent) {U : A.left.Opens}
    (hU : IsAffineOpen U) {Z : Set A.left} (hZ : IsClosed Z) (hZU : Z ⊆ U)
    (hsupp : SheafOfModules.supp 𝓕 ⊆ Z) (n : ℕ) :
    ((kernelIntegralTransform A.hom A.hom
      ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).obj (R.origTerm n)).IsLE 0 := by
  have hV := Stacks.Cohomology.DerivedInternalHomPullback.isLE_derivedPullback_obj_of_isFlat
    A.hom.toLRSHom.toShHom (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom A.hom)
    (R.twistCoefficient 𝓕 h𝓕 n).obj 0 (R.isLE_twistCoefficient 𝓕 h𝓕 h𝓕qc hU hZ hZU hsupp n)
  have h : ((perfectTwist A.hom (R.twistCoefficient 𝓕 h𝓕 n)).obj
      (rightPerfect A R R.isPerfect_single_right n)).obj.IsLE (0 + 0) :=
    @Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProductFunctor _ _ _
      A.left.toRingedSpace.sheaf _ _ _ _ _ _ _ _ 0 0 hV
      (inferInstanceAs (((DerivedCategory.singleFunctor A.left.Modules 0).obj (R.right n)).IsLE 0))
  rw [zero_add] at h
  exact DerivedCategory.TStructure.t.isLE_of_iso (R.origTransformIso 𝓕 h𝓕 n).symm 0

/-- **The Postnikov system `Ψ'(M₀), Ψ'(M₁), …`**, read in `D_perf(𝒪_X)`. -/
def origLift : Triangulated.SequentialPostnikovSystem (fun n => R.origTransformPerfect 𝓕 h𝓕 n)
    (fun n => ObjectProperty.homMk ((kernelIntegralTransform A.hom A.hom
      ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).map (R.origDiff n))) :=
  (R.origPostnikov.map (kernelIntegralTransform A.hom A.hom
      ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕))).lift
    (fun K : DerivedCategory A.left.Modules => IsPerfect (X := A.left.toRingedSpace) K)
    (R.isPerfect_origTransform 𝓕 h𝓕)
    (fun n => (R.origPostnikov.map (kernelIntegralTransform A.hom A.hom
      ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕))).prop_obj
      (fun K : DerivedCategory A.left.Modules => IsPerfect (X := A.left.toRingedSpace) K)
      (fun e h => Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
        (X := A.left.toRingedSpace) e h) (R.isPerfect_origTransform 𝓕 h𝓕) n)

include hF r eV in
/-- **The systems `n ↦ F(Ψ'(Mₙ[n]))` and `n ↦ Ψ(Kₙ[n])` are isomorphic.** This is the
uniqueness of Postnikov systems ([Stacks, Tag 0D83]) applied to the images of the two
systems, whose terms are identified by `imgComparison`, compatibly with the differentials, and
have no negative `Ext` because `F` is fully faithful. -/
theorem nonempty_sequence_iso (hFF : F.FullyFaithful) (h𝓕qc : 𝓕.IsQuasicoherent)
    {U : A.left.Opens} (hU : IsAffineOpen U) {Z : Set A.left} (hZ : IsClosed Z) (hZU : Z ⊆ U)
    (hsupp : SheafOfModules.supp 𝓕 ⊆ Z) :
    Nonempty ((R.origLift 𝓕 h𝓕).sequence ⋙ (F ⋙ ObjectProperty.ι _) ≅
      (R.imgPostnikov B F hF hFF).sequence ⋙ kernelIntegralTransform A.hom B.hom
        ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)) := by
  refine Triangulated.SequentialPostnikovSystem.nonempty_sequence_comp_iso _ _ _ _
    (fun n => R.imgComparison B 𝓕 h𝓕 F r eV n) (fun n => ?_) (fun i j t ht c => ?_)
  · exact R.imgComparison_kappa B 𝓕 h𝓕 F hF r eV n (resolutionTensor A R n)
  · have h₀ := hom_shift_obj_eq_zero_of_fullyFaithful F hFF (R.origTransformPerfect 𝓕 h𝓕 i)
      (R.origTransformPerfect 𝓕 h𝓕 j) (R.isLE_origTransform 𝓕 h𝓕 h𝓕qc hU hZ hZU hsupp i)
      (R.isGE_origTransform 𝓕 h𝓕 j) t (by omega) (c ≫ (R.imgComparison B 𝓕 h𝓕 F r eV j).inv)
    simpa using congrArg (· ≫ (R.imgComparison B 𝓕 h𝓕 F r eV j).hom) h₀

end DiagonalResolution

end Comparison

end AlgebraicGeometry
