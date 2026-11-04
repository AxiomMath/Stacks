module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.TransformedComplex
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.BoxHomVanishing
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.FullyFaithfulNegativeExt
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.TransformedDiagonal.Terms
public import StacksFrontier.Algebra.Homology.DerivedCategory.PostnikovHeartResolution

/-!
# The two Postnikov systems of [Stacks, Section 0G07]

Let `k` be a field, `X` a proper smooth `k`-scheme, `F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` a `k`-linear
exact fully faithful functor and `⋯ → ℰ₁ ⊠ 𝒢₁ → ℰ₀ ⊠ 𝒢₀ → 𝒪_Δ → 0` a resolution of the diagonal.
This file builds the infinite Postnikov systems `M₀, M₁, …` of the complex (0G09)
`⋯ → ℰ₁ ⊠ 𝒢₁ → ℰ₀ ⊠ 𝒢₀` in `D(𝒪_{X ×_k X})` and `K₀, K₁, …` of the transformed complex (0G0A)
`⋯ → ℰ₁ ⊠ F(𝒢₁) → ℰ₀ ⊠ F(𝒢₀)` in `D(𝒪_{X ×_k Y})`. Both exist because their terms have no
negative `Ext` between each other (`AlgebraicGeometry.subsingleton_hom_shift_derivedBox`).

The complex (0G09) is read as the transformed complex at `F = 𝟭`, i.e. through derived external
products; its terms are the external tensor products placed in degree zero
(`AlgebraicGeometry.boxSingleHom`), compatibly with the differentials, so the complex of their
`H⁰` is the resolution of `𝒪_Δ`. Consequently `Mₙ⟦n⟧` is an extension of `𝒪_Δ[0]` by an object
concentrated in degree `-n`
(`CategoryTheory.Triangulated.SequentialPostnikovSystem.exists_distTriang_shift_obj`).

## Main definitions

* `AlgebraicGeometry.DiagonalResolution.origTerm`, `.origDiff`: the complex (0G09).
* `AlgebraicGeometry.DiagonalResolution.origPostnikov`: its Postnikov system.
* `AlgebraicGeometry.DiagonalResolution.imgPostnikov`: the Postnikov system of (0G0A).

## References

* [Stacks Project, Section 0G07](https://stacks.math.columbia.edu/tag/0G07)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

namespace DiagonalResolution

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} (R : DiagonalResolution A.hom)

/-- The identity functor of `D_perf(𝒪_X)` is `k`-linear. -/
theorem id_linear :
    letI := modulesLinear k A; letI := modulesLinear k A;
    (𝟭 (PerfectDerivedCategory A.left)).Linear k := by
  let := modulesLinear k A
  infer_instance

/-- A second factor of the resolution, placed in degree zero, is perfect. -/
theorem isPerfect_single_right (i : ℕ) :
    IsPerfect (X := A.left.toRingedSpace)
      ((DerivedCategory.singleFunctor A.left.Modules 0).obj (R.right i)) :=
  isPerfect_singleFunctor_of_isFiniteLocallyFree A.left (R.right i) (R.right_finiteLocallyFree i)

/-- **The complex (0G09)** `⋯ → ℰ₁ ⊠ 𝒢₁ → ℰ₀ ⊠ 𝒢₀` of derived external products. -/
abbrev origTerm (i : ℕ) : DerivedCategory (pullback A.hom A.hom).Modules :=
  AlgebraicGeometry.transformedTerm A A R (𝟭 _) R.isPerfect_single_right i

variable [IsProper A.hom]

/-- The differentials of the complex (0G09). -/
abbrev origDiff (i : ℕ) : R.origTerm (i + 1) ⟶ R.origTerm i :=
  AlgebraicGeometry.transformedDifferential A A R (𝟭 _) R.isPerfect_single_right
    (id_linear (A := A)) i

/-! ### The terms are the external tensor products in degree zero -/

variable [Smooth A.hom]

omit [IsProper A.hom] in
/-- **The pure maps of the derived and of the module pairing correspond**: for every tensor `t`,
`κ(t) ≫ h = h ≫ κ_mod(t)[0]` with `h : ℰ[0] ⊠ 𝒢[0] ⟶ (ℰ ⊠ 𝒢)[0]` the comparison. -/
theorem kappa_comp_boxSingleHom (i j : ℕ)
    (t : letI := modulesLinear k A; (R.left i ⟶ R.left j) ⊗[k] (R.right i ⟶ R.right j)) :
    letI := modulesLinear k A
    letI : Linear k (pullback A.hom A.hom).Modules := modulesLinear k (overPullback k A A)
    letI : Linear k (pullback A.hom A.hom).Modules := modulesLinear k (externalTensorOver k A A)
    (transformedBoxPairing A A R (𝟭 _) R.isPerfect_single_right (id_linear (A := A))).κ i j t ≫
        boxSingleHom A.hom A.hom (R.left j) (R.right j) =
      boxSingleHom A.hom A.hom (R.left i) (R.right i) ≫
        (DerivedCategory.singleFunctor _ 0).map ((moduleBoxPairing A R).κ i j t) := by
  let := modulesLinear k A
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    have e₁ := by
      let : Linear k (pullback A.hom A.hom).Modules := modulesLinear k (overPullback k A A)
      exact (transformedBoxPairing A A R (𝟭 _) R.isPerfect_single_right
        (id_linear (A := A))).κ_tmul i j a b
    have e₂ := by
      let : Linear k (pullback A.hom A.hom).Modules := modulesLinear k (externalTensorOver k A A)
      exact (moduleBoxPairing A R).κ_tmul i j a b
    rw [e₁, e₂]
    exact boxSingleHom_naturality A.hom A.hom a b
  | add t t' ht ht' =>
    rw [map_add, map_add, Preadditive.add_comp, ht, ht', Functor.map_add, Preadditive.comp_add]

/-- **The differentials of (0G09) are those of the resolution, in degree zero.** -/
theorem origDiff_comp_boxSingleHom (i : ℕ) :
    R.origDiff i ≫ boxSingleHom A.hom A.hom (R.left i) (R.right i) =
      boxSingleHom A.hom A.hom (R.left (i + 1)) (R.right (i + 1)) ≫
        (DerivedCategory.singleFunctor _ 0).map (R.boxDifferential i) := by
  have h := R.kappa_comp_boxSingleHom (i + 1) i (resolutionTensor A R i)
  rw [moduleBoxPairing_κ_resolutionTensor] at h
  exact h

omit [IsProper A.hom] in
/-- The comparison `ℰᵢ[0] ⊠ 𝒢ᵢ[0] ⟶ (ℰᵢ ⊠ 𝒢ᵢ)[0]` is an isomorphism. -/
theorem isIso_boxSingleHom_right (i : ℕ) :
    IsIso (boxSingleHom A.hom A.hom (R.left i) (R.right i)) :=
  isIso_boxSingleHom A.hom A.hom _ _ (R.right_finiteLocallyFree i)

omit [IsProper A.hom] in
/-- The terms of (0G09) have cohomology only in degree zero. -/
theorem isZero_homology_origTerm (n : ℕ) (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor _ i).obj (R.origTerm n)) := by
  have := R.isIso_boxSingleHom_right n
  have hz : IsZero ((DerivedCategory.homologyFunctor (pullback A.hom A.hom).Modules i).obj
      ((DerivedCategory.singleFunctor _ 0).obj (R.boxTerm n))) := by
    rcases lt_or_gt_of_ne hi with h | h
    · exact DerivedCategory.isZero_of_isGE _ 0 i h
    · exact DerivedCategory.isZero_of_isLE _ 0 i h
  exact hz.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
    (asIso (boxSingleHom A.hom A.hom (R.left n) (R.right n))))

/-- `H⁰` of a term of (0G09) is the corresponding external tensor product. -/
def homologyOrigTermIso (n : ℕ) :
    (DerivedCategory.homologyFunctor _ 0).obj (R.origTerm n) ≅ R.boxTerm n :=
  haveI := R.isIso_boxSingleHom_right n
  (DerivedCategory.homologyFunctor _ 0).mapIso
      (asIso (boxSingleHom A.hom A.hom (R.left n) (R.right n))) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _

/-- The isomorphisms `homologyOrigTermIso` identify `H⁰` of the differentials of (0G09) with the
differentials of the resolution. -/
theorem homologyOrigTermIso_comm (n : ℕ) :
    (DerivedCategory.homologyFunctor _ 0).map (R.origDiff n) ≫ (R.homologyOrigTermIso n).hom =
      (R.homologyOrigTermIso (n + 1)).hom ≫ R.boxDifferential n := by
  have h₁ := congrArg (DerivedCategory.homologyFunctor (pullback A.hom A.hom).Modules 0).map
    (R.origDiff_comp_boxSingleHom n)
  rw [Functor.map_comp, Functor.map_comp] at h₁
  have h₂ := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (pullback A.hom A.hom).Modules 0).hom.naturality (R.boxDifferential n)
  dsimp only [homologyOrigTermIso, Iso.trans_hom, Functor.mapIso_hom, asIso_hom, Iso.app_hom]
  rw [← Category.assoc, h₁, Category.assoc, Category.assoc]
  exact congrArg (_ ≫ ·) h₂

omit [IsProper A.hom] [Smooth A.hom] in
/-- The complex of external tensor products is exact in positive degrees. -/
theorem exact_boxDifferential (n : ℕ) :
    (ShortComplex.mk (R.boxDifferential (n + 1)) (R.boxDifferential n)
      (R.boxDifferential_comp n)).Exact := by
  have h := (R.complex.exactAt_iff' (n + 3) (n + 2) (n + 1) (by simp) (by simp)).1
    (R.acyclic (n + 2))
  let φ : ShortComplex.mk (R.complex.d (n + 3) (n + 2)) (R.complex.d (n + 2) (n + 1))
      (R.complex.d_comp_d _ _ _) ⟶ ShortComplex.mk (R.boxDifferential (n + 1))
        (R.boxDifferential n) (R.boxDifferential_comp n) :=
    { τ₁ := (R.termIso (n + 2)).hom, τ₂ := (R.termIso (n + 1)).hom, τ₃ := (R.termIso n).hom
      comm₁₂ := by simp [boxDifferential]
      comm₂₃ := by simp [boxDifferential] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 h

/-- The complex of the `H⁰` of the terms of (0G09) is exact in positive degrees. -/
theorem exact_homology_origDiff (n : ℕ) :
    (ShortComplex.mk ((DerivedCategory.homologyFunctor _ 0).map (R.origDiff (n + 1)))
      ((DerivedCategory.homologyFunctor _ 0).map (R.origDiff n))
      (Triangulated.homologyMap_comp_eq_zero (fun n => transformedDifferential_comp A A R (𝟭 _)
        R.isPerfect_single_right (id_linear (A := A)) n) n)).Exact := by
  let φ : ShortComplex.mk ((DerivedCategory.homologyFunctor _ 0).map (R.origDiff (n + 1)))
      ((DerivedCategory.homologyFunctor _ 0).map (R.origDiff n))
      (Triangulated.homologyMap_comp_eq_zero (fun n => transformedDifferential_comp A A R (𝟭 _)
        R.isPerfect_single_right (id_linear (A := A)) n) n) ⟶
      ShortComplex.mk (R.boxDifferential (n + 1)) (R.boxDifferential n)
        (R.boxDifferential_comp n) :=
    { τ₁ := (R.homologyOrigTermIso (n + 1 + 1)).hom, τ₂ := (R.homologyOrigTermIso (n + 1)).hom,
      τ₃ := (R.homologyOrigTermIso n).hom
      comm₁₂ := (R.homologyOrigTermIso_comm (n + 1)).symm
      comm₂₃ := (R.homologyOrigTermIso_comm n).symm }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 (R.exact_boxDifferential n)

/-- `𝒪_Δ`, the structure sheaf of the diagonal. -/
abbrev diagonalModule : (pullback A.hom A.hom).Modules :=
  (Scheme.Modules.pushforward (pullback.diagonal A.hom)).obj (SheafOfModules.unit _)

/-- The augmentation `H⁰(ℰ₀ ⊠ 𝒢₀) ⟶ 𝒪_Δ`. -/
def origAugmentation :
    (DerivedCategory.homologyFunctor _ 0).obj (R.origTerm 0) ⟶ diagonalModule (A := A) :=
  (R.homologyOrigTermIso 0).hom ≫ (R.termIso 0).inv ≫ R.complex.d 1 0 ≫ R.zeroIso.hom

/-- The augmentation `H⁰(ℰ₀ ⊠ 𝒢₀) ⟶ 𝒪_Δ` is an epimorphism. -/
instance : Epi R.origAugmentation := by
  have h := R.epi_augmentation
  have e : R.origAugmentation =
      (R.homologyOrigTermIso 0).hom ≫ (R.termIso 0).inv ≫ R.augmentation := rfl
  rw [e]
  exact epi_comp' inferInstance (epi_comp' inferInstance h)

/-- The composite `H⁰(ℰ₁ ⊠ 𝒢₁) ⟶ H⁰(ℰ₀ ⊠ 𝒢₀) ⟶ 𝒪_Δ` vanishes. -/
theorem homology_origDiff_comp_origAugmentation :
    (DerivedCategory.homologyFunctor _ 0).map (R.origDiff 0) ≫ R.origAugmentation = 0 := by
  rw [origAugmentation, reassoc_of% (R.homologyOrigTermIso_comm 0), boxDifferential]
  simp

/-- The sequence `H⁰(ℰ₁ ⊠ 𝒢₁) ⟶ H⁰(ℰ₀ ⊠ 𝒢₀) ⟶ 𝒪_Δ` is exact. -/
theorem exact_origAugmentation :
    (ShortComplex.mk _ _ R.homology_origDiff_comp_origAugmentation).Exact := by
  have h := (R.complex.exactAt_iff' 2 1 0 (by simp) (by simp)).1 (R.acyclic 1)
  let φ : ShortComplex.mk _ _ R.homology_origDiff_comp_origAugmentation ⟶
      ShortComplex.mk (R.complex.d 2 1) (R.complex.d 1 0) (R.complex.d_comp_d _ _ _) :=
    { τ₁ := (R.homologyOrigTermIso 1).hom ≫ (R.termIso 1).inv,
      τ₂ := (R.homologyOrigTermIso 0).hom ≫ (R.termIso 0).inv,
      τ₃ := R.zeroIso.inv
      comm₁₂ := by
        dsimp
        rw [reassoc_of% (R.homologyOrigTermIso_comm 0), boxDifferential]
        simp
      comm₂₃ := by simp [origAugmentation] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).2 h

/-! ### The Postnikov systems -/

omit [IsProper A.hom] [Smooth A.hom] in
/-- A positive shift of an object in degrees `≤ 0` has no morphism to an object in degrees
`≥ 0`. -/
theorem subsingleton_hom_shift_of_isLE_of_isGE {W : Scheme.{u}} {K L : DerivedCategory W.Modules}
    (hK : K.IsLE 0) (hL : L.IsGE 0) (s : ℤ) (hs : 0 < s) : Subsingleton (K⟦s⟧ ⟶ L) := by
  have h : (K⟦s⟧).IsLE (-s) := DerivedCategory.TStructure.t.isLE_shift K 0 s (-s) (by omega)
  exact ⟨fun a b =>
    (DerivedCategory.TStructure.t.zero_of_isLE_of_isGE a (-s) 0 (by omega) h hL).trans
      (DerivedCategory.TStructure.t.zero_of_isLE_of_isGE b (-s) 0 (by omega) h hL).symm⟩

/-- For `F` fully faithful, the terms `ℰᵢ ⊠ F(𝒢ᵢ)` have no negative `Ext` between each other. -/
private theorem transformedTerm_hom_shift_eq_zero (B : Over (Spec (.of k)))
    (F : PerfectDerivedCategory A.left ⥤ PerfectDerivedCategory B.left)
    [F.Additive] [F.CommShift ℤ] (hFF : F.FullyFaithful) (i j t : ℕ) (ht : 0 < t)
    (φ : (AlgebraicGeometry.transformedTerm A B R F R.isPerfect_single_right i)⟦(t : ℤ)⟧ ⟶
      AlgebraicGeometry.transformedTerm A B R F R.isPerfect_single_right j) : φ = 0 := by
  have hvan : ∀ s : ℤ, 0 < s → Subsingleton
      ((imageOfRight A B R F R.isPerfect_single_right i)⟦s⟧ ⟶
        imageOfRight A B R F R.isPerfect_single_right j) := by
    intro s hs
    refine ⟨fun a b => ?_⟩
    let e := ((ObjectProperty.ι (fun K : DerivedCategory B.left.Modules =>
      IsPerfect (X := B.left.toRingedSpace) K)).commShiftIso s).app
        (F.obj (rightPerfect A R R.isPerfect_single_right i))
    have key : ∀ c : (imageOfRight A B R F R.isPerfect_single_right i)⟦s⟧ ⟶
        imageOfRight A B R F R.isPerfect_single_right j, c = 0 := by
      intro c
      have h0 := map_shift_hom_eq_zero_of_fullyFaithful F hFF
        (rightPerfect A R R.isPerfect_single_right i) (rightPerfect A R R.isPerfect_single_right j)
        (inferInstanceAs (((DerivedCategory.singleFunctor A.left.Modules 0).obj
          (R.right i)).IsLE 0))
        (inferInstanceAs (((DerivedCategory.singleFunctor A.left.Modules 0).obj
          (R.right j)).IsGE 0)) s hs (ObjectProperty.homMk (e.hom ≫ c))
      have h1 : e.hom ≫ c = 0 := congrArg (fun x => x.hom) h0
      rwa [Preadditive.IsIso.comp_left_eq_zero] at h1
    rw [key a, key b]
  have := subsingleton_hom_shift_derivedBox A.hom B.hom (R.left i) (R.left j)
    (R.left_finiteLocallyFree i) (R.left_finiteLocallyFree j)
    (imageOfRight A B R F R.isPerfect_single_right i)
    (imageOfRight A B R F R.isPerfect_single_right j)
    (isQCohAll_of_isPerfect (F.obj (rightPerfect A R R.isPerfect_single_right j)).property)
    hvan (t : ℤ) (by omega)
  exact @Subsingleton.elim _ this _ _

/-- **The terms of (0G09) have no negative `Ext`.** -/
theorem origTerm_hom_shift_eq_zero (i j t : ℕ) (ht : 0 < t)
    (φ : (R.origTerm i)⟦(t : ℤ)⟧ ⟶ R.origTerm j) : φ = 0 :=
  R.transformedTerm_hom_shift_eq_zero A (𝟭 _) (Functor.FullyFaithful.id _) i j t ht φ

/-- **The Postnikov system `M₀, M₁, …` of the complex (0G09).** -/
def origPostnikov : Triangulated.SequentialPostnikovSystem R.origTerm R.origDiff :=
  Classical.choice (Triangulated.nonempty_sequentialPostnikovSystem _ _
    (fun n => transformedDifferential_comp A A R (𝟭 _) R.isPerfect_single_right
      (id_linear (A := A)) n) R.origTerm_hom_shift_eq_zero)

/-- **`Mₙ⟦n⟧` is an extension of `𝒪_Δ[0]` by an object concentrated in degree `-n`.** -/
theorem exists_distTriang_origPostnikov (n : ℕ) (hn : 1 ≤ n) :
    ∃ T : Pretriangulated.Triangle (DerivedCategory (pullback A.hom A.hom).Modules),
      T ∈ distTriang _ ∧ Nonempty (T.obj₂ ≅ (R.origPostnikov.obj n)⟦(n : ℤ)⟧) ∧
        T.obj₁.IsLE (-(n : ℤ)) ∧ T.obj₁.IsGE (-(n : ℤ)) ∧
        Nonempty (T.obj₃ ≅ (DerivedCategory.singleFunctor _ 0).obj (diagonalModule (A := A))) :=
  R.origPostnikov.exists_distTriang_shift_obj R.isZero_homology_origTerm
    (fun n => transformedDifferential_comp A A R (𝟭 _) R.isPerfect_single_right
      (id_linear (A := A)) n) R.exact_homology_origDiff R.origAugmentation
    R.homology_origDiff_comp_origAugmentation R.exact_origAugmentation n hn

section Image

variable (B : Over (Spec (.of k)))
  (F : PerfectDerivedCategory A.left ⥤ PerfectDerivedCategory B.left)
  [F.Additive] [F.CommShift ℤ]
  (hF : letI := modulesLinear k A; letI := modulesLinear k B; F.Linear k)

/-- **The terms of the transformed complex (0G0A) have no negative `Ext`**, for `F` fully
faithful. -/
theorem imgTerm_hom_shift_eq_zero (hFF : F.FullyFaithful) (i j t : ℕ) (ht : 0 < t)
    (φ : (AlgebraicGeometry.transformedTerm A B R F R.isPerfect_single_right i)⟦(t : ℤ)⟧ ⟶
      AlgebraicGeometry.transformedTerm A B R F R.isPerfect_single_right j) : φ = 0 :=
  R.transformedTerm_hom_shift_eq_zero B F hFF i j t ht φ

/-- **The Postnikov system `K₀, K₁, …` of the transformed complex (0G0A).** -/
def imgPostnikov (hFF : F.FullyFaithful) :
    Triangulated.SequentialPostnikovSystem
      (AlgebraicGeometry.transformedTerm A B R F R.isPerfect_single_right)
      (AlgebraicGeometry.transformedDifferential A B R F R.isPerfect_single_right hF) :=
  Classical.choice (Triangulated.nonempty_sequentialPostnikovSystem _ _
    (fun n => transformedDifferential_comp A B R F R.isPerfect_single_right hF n)
    (R.imgTerm_hom_shift_eq_zero B F hFF))

end Image

end DiagonalResolution

end AlgebraicGeometry
