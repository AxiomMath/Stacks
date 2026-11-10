module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.PostnikovComparison
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Orlov.CoherentUniformBound
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FibreBandSplitting
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.DiagonalKernelTower
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.DiagonalResolution
public import
  StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.RelativeEquivalenceEquivalences
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularCoherentPerfect
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Countability.ObjectwiseOrlov
public import StacksFrontier.CategoryTheory.Triangulated.TStructure.SummandTruncation

/-!
# A fully faithful functor agrees with a Fourier-Mukai functor on zero-dimensional sheaves

Let `k` be a field, `X` and `Y` proper smooth `k`-schemes and `F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` a
`k`-linear exact fully faithful functor. This file completes the construction of
[Stacks, Section 0G07]: there is a perfect kernel `K` on `X ×_k Y` whose Fourier-Mukai functor
agrees with `F` on every coherent module with zero-dimensional support. This is
`AlgebraicGeometry.FourierMukaiAgreesOnZeroDimensional`, part A of the object-wise Orlov theorem.

With `Mₙ` and `Kₙ` the Postnikov systems of the resolution (0G09) of the diagonal and of the
transformed complex (0G0A), and `Ψ'`, `Ψ` the integral transforms by a coherent `𝓕` supported at
a point, `F(Ψ'(Mₙ[n])) ≅ Ψ(Kₙ[n])` (`AlgebraicGeometry.DiagonalResolution.nonempty_sequence_iso`).
On the left, `Mₙ[n]` is an extension of `𝒪_Δ[0]` by an object in degree `-n`, so
`F(Ψ'(Mₙ[n]))` is an extension of `F(𝓕)` by an object with cohomology in `[-m - n, m - n]`, for
the uniform bound `m` of `F` on coherent modules. These bands let [Stacks, Tag 0FZ9] split
`Kₙ[n] = K ⊕ Cₙ` for large `n`, and comparing the parts in degrees `≥ -m` gives
`Φ_K(𝓕) ≅ F(𝓕)`. A general zero-dimensional coherent module is a finite direct sum of modules
supported at single points.

## Main results

* `AlgebraicGeometry.fourierMukaiAgreesOnZeroDimensional`: part A.

## References

* [Stacks Project, Section 0G07](https://stacks.math.columbia.edu/tag/0G07)
* [Stacks Project, Tag 0G0B](https://stacks.math.columbia.edu/tag/0G0B)
* [Stacks Project, Tag 0FZ9](https://stacks.math.columbia.edu/tag/0FZ9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open Stacks.Perfect.BoundedLocallyFreeComplexes (PerfectDerivedCategory)

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### Triangles of perfect objects -/

section PerfectTriangles

variable {W : Scheme.{u}}

/-- A distinguished triangle of `D(𝒪_W)` with perfect vertices, read in `D_perf(𝒪_W)`. -/
def perfectTriangle (T : Triangle (DerivedCategory W.Modules))
    (h₁ : IsPerfect (X := W.toRingedSpace) T.obj₁)
    (h₂ : IsPerfect (X := W.toRingedSpace) T.obj₂) (h₃ : IsPerfect (X := W.toRingedSpace) T.obj₃) :
    Triangle (PerfectDerivedCategory W) :=
  Triangle.mk
    (ObjectProperty.homMk T.mor₁ : (⟨T.obj₁, h₁⟩ : PerfectDerivedCategory W) ⟶ ⟨T.obj₂, h₂⟩)
    (ObjectProperty.homMk T.mor₂ : (⟨T.obj₂, h₂⟩ : PerfectDerivedCategory W) ⟶ ⟨T.obj₃, h₃⟩)
    (ObjectProperty.homMk (T.mor₃ ≫ (((ObjectProperty.ι _).commShiftIso (1 : ℤ)).app
      (⟨T.obj₁, h₁⟩ : PerfectDerivedCategory W)).inv))

/-- A distinguished triangle of `D(𝒪_W)` with perfect vertices is distinguished in
`D_perf(𝒪_W)`. -/
theorem perfectTriangle_distinguished (T : Triangle (DerivedCategory W.Modules))
    (hT : T ∈ distTriang _) (h₁ : IsPerfect (X := W.toRingedSpace) T.obj₁)
    (h₂ : IsPerfect (X := W.toRingedSpace) T.obj₂) (h₃ : IsPerfect (X := W.toRingedSpace) T.obj₃) :
    perfectTriangle T h₁ h₂ h₃ ∈ distTriang (PerfectDerivedCategory W) := by
  change (ObjectProperty.ι _).mapTriangle.obj _ ∈ distTriang (DerivedCategory W.Modules)
  refine isomorphic_distinguished _ hT _
    (Triangle.isoMk _ _ (Iso.refl T.obj₁) (Iso.refl T.obj₂) (Iso.refl T.obj₃) ?_ ?_ ?_)
  · exact (Category.comp_id _).trans (Category.id_comp T.mor₁).symm
  · exact (Category.comp_id _).trans (Category.id_comp T.mor₂).symm
  · simp [Functor.mapTriangle, perfectTriangle]

end PerfectTriangles

/-! ### Transforms by a module supported over an affine open -/

section Transforms

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
  [Flat g]

/-- **The integral transform by a quasi-coherent module supported over an affine open is right
t-exact** on objects with quasi-coherent cohomology. -/
theorem isZero_homology_kernelIntegralTransform_of_isLE (𝓕 : X.Modules)
    (h𝓕qc : 𝓕.IsQuasicoherent) {U : X.Opens} (hU : IsAffineOpen U) {Z : Set X} (hZ : IsClosed Z)
    (hZU : Z ⊆ U) (hsupp : SheafOfModules.supp 𝓕 ⊆ Z) (N : DerivedCategory (pullback f g).Modules)
    (hN : IsQCohAll N) (a : ℤ) (ha : N.IsLE a) (i : ℤ) (hi : a < i) :
    IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((kernelIntegralTransform f g ((DerivedCategory.singleFunctor X.Modules 0).obj 𝓕)).obj N)) :=
  (isZero_homology_fibreTransform_of_isLE f g hU hZ hZU 𝓕 hsupp h𝓕qc N hN a ha i hi).of_iso
    ((DerivedCategory.homologyFunctor Y.Modules i).mapIso
      ((fibreTransformFunctorIso f g
        (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _) 𝓕).app N).symm)

/-- **`Ψ'(𝒪_Δ[0]) ≅ 𝓕[0]`**: the integral transform of the structure sheaf of the diagonal is the
identity ([Stacks, Tag 0FYV]). -/
def diagonalTransformIso [IsSeparated f] (M : DerivedCategory X.Modules) :
    (kernelIntegralTransform f f M).obj ((DerivedCategory.singleFunctor _ 0).obj
      ((Scheme.Modules.pushforward (pullback.diagonal f)).obj
        (SheafOfModules.unit X.ringCatSheaf))) ≅ M :=
  (kernelIntegralTransform f f M).mapIso (diagonalKernelIsoSingle f).symm ≪≫
    (diagonalFourierMukaiIsIdentity f inferInstance).some.app M

end Transforms

/-! ### The bands of the transforms of the Postnikov system of the diagonal -/

section Bands

/-- An object of `D(𝒪_W)` that is `a`-connective and `b`-coconnective has vanishing cohomology
outside `[a, b]`. -/
private theorem isZero_homology_of_not_mem_Icc {W : Scheme.{u}} (K : DerivedCategory W.Modules)
    (a b : ℤ) [K.IsGE a] [K.IsLE b] (i : ℤ) (hi : i ∉ Set.Icc a b) :
    IsZero ((DerivedCategory.homologyFunctor W.Modules i).obj K) := by
  rcases not_and_or.1 hi with h | h
  · exact DerivedCategory.isZero_of_isGE _ a i (not_le.1 h)
  · exact DerivedCategory.isZero_of_isLE _ b i (not_le.1 h)

variable {k : Type u} [Field k] {A : Over (Spec (.of k))} [Smooth A.hom] [IsProper A.hom]
  (R : DiagonalResolution A.hom)

namespace DiagonalResolution

omit [Smooth A.hom] [IsProper A.hom] in
/-- The terms of (0G09) are perfect. -/
theorem isPerfect_origTerm (n : ℕ) : IsPerfect (X := (pullback A.hom A.hom).toRingedSpace)
    (R.origTerm n) :=
  isPerfect_dtenR _ _
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback.{u} _ _
      (isPerfect_singleFunctor_of_isFiniteLocallyFree A.left (R.left n)
        (R.left_finiteLocallyFree n)))
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback.{u} _ _
      (R.isPerfect_single_right n))

/-- The objects of the Postnikov system of (0G09) are perfect. -/
theorem isPerfect_origPostnikov_obj (n : ℕ) :
    IsPerfect (X := (pullback A.hom A.hom).toRingedSpace) (R.origPostnikov.obj n) :=
  R.origPostnikov.prop_obj
    (fun K : DerivedCategory (pullback A.hom A.hom).Modules =>
      IsPerfect (X := (pullback A.hom A.hom).toRingedSpace) K)
    (fun e h => Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      (X := (pullback A.hom A.hom).toRingedSpace) e h) R.isPerfect_origTerm n

/-- `𝒪_Δ[0]` is perfect. -/
theorem isPerfect_single_diagonalModule :
    IsPerfect (X := (pullback A.hom A.hom).toRingedSpace)
      ((DerivedCategory.singleFunctor _ 0).obj (diagonalModule (A := A))) :=
  Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
    (X := (pullback A.hom A.hom).toRingedSpace) (diagonalKernelIsoSingle A.hom)
    (isPerfect_diagonalKernel_ringedSpace A.hom)

variable (𝓕 : A.left.Modules) (h𝓕 : IsPerfect (X := A.left.toRingedSpace)
    ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕))

/-- **`F(Ψ'(Mₙ[n]))` is an extension of `F(𝓕)` by an object in degrees `≤ m - n`**, for `F`
with uniform bound `m` and `𝓕` supported on a closed subset of an affine open, `n ≥ 1`. -/
theorem exists_distTriang_origLift_sequence {B : Scheme.{u}}
    (F : PerfectDerivedCategory A.left ⥤ PerfectDerivedCategory B) [F.CommShift ℤ]
    [F.IsTriangulated] (m : ℕ)
    (hm : ∀ (Z : PerfectDerivedCategory A.left) (a b : ℤ), a ≤ b →
      (∀ i : ℤ, i ∉ Set.Icc a b → IsZero ((DerivedCategory.homologyFunctor A.left.Modules i).obj
        Z.obj)) →
        ∀ i : ℤ, i ∉ Set.Icc (a - m) (b + m) →
          IsZero ((DerivedCategory.homologyFunctor B.Modules i).obj (F.obj Z).obj))
    (h𝓕qc : 𝓕.IsQuasicoherent) {U : A.left.Opens} (hU : IsAffineOpen U) {Z : Set A.left}
    (hZ : IsClosed Z) (hZU : Z ⊆ U) (hsupp : SheafOfModules.supp 𝓕 ⊆ Z) (n : ℕ) (hn : 1 ≤ n) :
    ∃ TY : Triangle (DerivedCategory B.Modules), TY ∈ distTriang _ ∧
      Nonempty (TY.obj₂ ≅ (F.obj ((R.origLift 𝓕 h𝓕).sequence.obj n)).obj) ∧
      Nonempty (TY.obj₃ ≅ (F.obj ⟨_, h𝓕⟩).obj) ∧
      ∀ i : ℤ, (m : ℤ) - n < i →
        IsZero ((DerivedCategory.homologyFunctor B.Modules i).obj TY.obj₁) := by
  let Ψ' :=
    kernelIntegralTransform A.hom A.hom ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)
  let Zn := (R.origLift 𝓕 h𝓕).sequence.obj n
  let Y' := R.origPostnikov.map Ψ'
  have eZ : Zn.obj ≅ (Y'.obj n)⟦(n : ℤ)⟧ :=
    ((ObjectProperty.ι (fun K : DerivedCategory A.left.Modules =>
      IsPerfect (X := A.left.toRingedSpace) K)).commShiftIso (n : ℤ)).app _
  obtain ⟨T, hT, ⟨e₂⟩, h₁LE, -, ⟨e₃⟩⟩ := R.exists_distTriang_origPostnikov n hn
  have hT₂ : IsPerfect (X := (pullback A.hom A.hom).toRingedSpace) T.obj₂ :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      (X := (pullback A.hom A.hom).toRingedSpace) e₂.symm
      (Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift
        (R.isPerfect_origPostnikov_obj n) (n : ℤ))
  have hT₃ : IsPerfect (X := (pullback A.hom A.hom).toRingedSpace) T.obj₃ :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
      (X := (pullback A.hom A.hom).toRingedSpace) e₃.symm (isPerfect_single_diagonalModule (A := A))
  have hT₁ : IsPerfect (X := (pullback A.hom A.hom).toRingedSpace) T.obj₁ :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₁_of_distinguished T hT hT₂ hT₃
  let T' := Ψ'.mapTriangle.obj T
  have hT' : T' ∈ distTriang _ := Ψ'.map_distinguished T hT
  let e₂' : T'.obj₂ ≅ Zn.obj := Ψ'.mapIso e₂ ≪≫ (Ψ'.commShiftIso (n : ℤ)).app _ ≪≫ eZ.symm
  let e₃' : T'.obj₃ ≅ (DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕 :=
    Ψ'.mapIso e₃ ≪≫ diagonalTransformIso A.hom _
  have h₂ : IsPerfect (X := A.left.toRingedSpace) T'.obj₂ :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := A.left.toRingedSpace)
      e₂'.symm Zn.property
  have h₃ : IsPerfect (X := A.left.toRingedSpace) T'.obj₃ :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso (X := A.left.toRingedSpace)
      e₃'.symm h𝓕
  have h₁ : IsPerfect (X := A.left.toRingedSpace) T'.obj₁ :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₁_of_distinguished T' hT' h₂ h₃
  -- `W = Ψ'(T.obj₁)` lies in degrees `≤ -n`
  have hW : ∀ i : ℤ, -(n : ℤ) < i →
      IsZero ((DerivedCategory.homologyFunctor A.left.Modules i).obj T'.obj₁) :=
    fun i hi => isZero_homology_kernelIntegralTransform_of_isLE A.hom A.hom 𝓕 h𝓕qc hU hZ hZU
      hsupp T.obj₁ (isQCohAll_of_isPerfect hT₁) (-(n : ℤ)) h₁LE i hi
  obtain ⟨-, c, -, hc, -⟩ :=
    Stacks.AlgebraicGeometry.PerfectProperDirectImage.isCoherent_homology_and_bounds_of_isPerfect
      A.hom T'.obj₁ h₁
  have hWamp : ∀ i : ℤ, i ∉ Set.Icc (min c (-(n : ℤ))) (-(n : ℤ)) →
      IsZero ((DerivedCategory.homologyFunctor A.left.Modules i).obj T'.obj₁) := by
    intro i hi
    rcases not_and_or.1 hi with h | h
    · exact DerivedCategory.isZero_of_isGE _ c i (by omega)
    · exact hW i (by omega)
  have hFW := hm ⟨T'.obj₁, h₁⟩ _ _ (min_le_right _ _) hWamp
  -- the triangle `F(W) ⟶ F(Ψ'(Mₙ[n])) ⟶ F(𝓕)` in `D(𝒪_Y)`
  let TP := perfectTriangle T' h₁ h₂ h₃
  have hTP := perfectTriangle_distinguished T' hT' h₁ h₂ h₃
  let TY := (ObjectProperty.ι _).mapTriangle.obj (F.mapTriangle.obj TP)
  have hTY : TY ∈ distTriang _ := (ObjectProperty.ι _).map_distinguished _
    (F.map_distinguished _ hTP)
  exact ⟨TY, hTY, ⟨(ObjectProperty.ι _).mapIso (F.mapIso (ObjectProperty.isoMk _ e₂'))⟩,
    ⟨(ObjectProperty.ι _).mapIso (F.mapIso (ObjectProperty.isoMk _ e₃'))⟩,
    fun i hi => hFW i (by rintro ⟨-, h₂⟩; omega)⟩

/-- **The bands of `F(Ψ'(Mₙ[n]))`.** For `F` with uniform bound `m` on perfect complexes of
amplitude `[a, b]`, and `𝓕` supported at a closed subset of an affine open, the cohomology of
`F(Ψ'(Mₙ[n]))` vanishes outside `[-m, m] ∪ [-m - n, m - n]`. -/
theorem isZero_homology_origLift_sequence {B : Scheme.{u}}
    (F : PerfectDerivedCategory A.left ⥤ PerfectDerivedCategory B) [F.CommShift ℤ]
    [F.IsTriangulated] (m : ℕ)
    (hm : ∀ (Z : PerfectDerivedCategory A.left) (a b : ℤ), a ≤ b →
      (∀ i : ℤ, i ∉ Set.Icc a b → IsZero ((DerivedCategory.homologyFunctor A.left.Modules i).obj
        Z.obj)) →
        ∀ i : ℤ, i ∉ Set.Icc (a - m) (b + m) →
          IsZero ((DerivedCategory.homologyFunctor B.Modules i).obj (F.obj Z).obj))
    (h𝓕qc : 𝓕.IsQuasicoherent) {U : A.left.Opens} (hU : IsAffineOpen U) {Z : Set A.left}
    (hZ : IsClosed Z) (hZU : Z ⊆ U) (hsupp : SheafOfModules.supp 𝓕 ⊆ Z)
    (n : ℕ) (j : ℤ) (hj : ¬ InBands m n j) :
    IsZero ((DerivedCategory.homologyFunctor B.Modules j).obj
      (F.obj ((R.origLift 𝓕 h𝓕).sequence.obj n)).obj) := by
  let Ψ' :=
    kernelIntegralTransform A.hom A.hom ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)
  let Zn := (R.origLift 𝓕 h𝓕).sequence.obj n
  let Y' := R.origPostnikov.map Ψ'
  have eZ : Zn.obj ≅ (Y'.obj n)⟦(n : ℤ)⟧ :=
    ((ObjectProperty.ι (fun K : DerivedCategory A.left.Modules =>
      IsPerfect (X := A.left.toRingedSpace) K)).commShiftIso (n : ℤ)).app _
  -- the amplitude `[-n, 0]` of `Ψ'(Mₙ[n])`
  have hLE : ((Y'.obj n)⟦(n : ℤ)⟧).IsLE 0 :=
    Y'.isLE_shift_obj_of_isLE 0 (fun i => R.isLE_origTransform 𝓕 h𝓕 h𝓕qc hU hZ hZU hsupp i) n
  have hGE : ((Y'.obj n)⟦(n : ℤ)⟧).IsGE (-(n : ℤ)) := by
    simpa using Y'.isGE_shift_obj_of_isGE 0 (fun i => R.isGE_origTransform 𝓕 h𝓕 i) n
  have hamp : ∀ i : ℤ, i ∉ Set.Icc (-(n : ℤ)) 0 →
      IsZero ((DerivedCategory.homologyFunctor A.left.Modules i).obj Zn.obj) := by
    intro i hi
    exact (isZero_homology_of_not_mem_Icc ((Y'.obj n)⟦(n : ℤ)⟧) (-(n : ℤ)) 0 i hi).of_iso
      ((DerivedCategory.homologyFunctor A.left.Modules i).mapIso eZ)
  have hF := hm Zn (-(n : ℤ)) 0 (by omega) hamp
  simp only [InBands, not_or, not_and_or, not_le] at hj
  by_cases hout : j < -(n : ℤ) - m ∨ (m : ℤ) < j
  · exact hF j (by rintro ⟨h₁, h₂⟩; omega)
  obtain ⟨TY, hTY, ⟨e₂⟩, ⟨e₃⟩, hW⟩ :=
    R.exists_distTriang_origLift_sequence 𝓕 h𝓕 F m hm h𝓕qc hU hZ hZU hsupp n (by omega)
  have hF𝓕 := hm ⟨_, h𝓕⟩ 0 0 le_rfl (isZero_homology_of_not_mem_Icc _ 0 0)
  exact ((DerivedCategory.HomologySequence.exact₂ TY hTY j).isZero_of_both_isZero (hW j (by omega))
    ((hF𝓕 j (by rintro ⟨h₁, h₂⟩; omega)).of_iso
      ((DerivedCategory.homologyFunctor B.Modules j).mapIso e₃))).of_iso
    ((DerivedCategory.homologyFunctor B.Modules j).mapIso e₂.symm)

variable (B : Over (Spec (.of k)))
  (F : PerfectDerivedCategory A.left ⥤ PerfectDerivedCategory B.left)
  [F.CommShift ℤ] [F.IsTriangulated]
  (hF : letI := modulesLinear k A; letI := modulesLinear k B; F.Linear k) (hFF : F.FullyFaithful)
  (m : ℕ)
  (hm : ∀ (Z : PerfectDerivedCategory A.left) (a b : ℤ), a ≤ b →
      (∀ i : ℤ, i ∉ Set.Icc a b → IsZero ((DerivedCategory.homologyFunctor A.left.Modules i).obj
        Z.obj)) →
        ∀ i : ℤ, i ∉ Set.Icc (a - m) (b + m) →
          IsZero ((DerivedCategory.homologyFunctor B.left.Modules i).obj (F.obj Z).obj))

include hm h𝓕 in
/-- **The bands of `Ψ(Kₙ[n])`** for `𝓕` supported on a closed subset of an affine open. -/
theorem isZero_homology_imgPostnikov_sequence
    (h𝓕qc : 𝓕.IsQuasicoherent) {U : A.left.Opens} (hU : IsAffineOpen U) {Z : Set A.left}
    (hZ : IsClosed Z) (hZU : Z ⊆ U) (hsupp : SheafOfModules.supp 𝓕 ⊆ Z)
    (n : ℕ) (j : ℤ) (hj : ¬ InBands m n j) :
    IsZero ((DerivedCategory.homologyFunctor B.left.Modules j).obj
      ((kernelIntegralTransform A.hom B.hom
        ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).obj
        ((R.imgPostnikov B F hF hFF).sequence.obj n))) := by
  have hr := fun n => R.exists_iso_twistCoefficient 𝓕 h𝓕 h𝓕qc hU hZ hZU hsupp n
  obtain ⟨Θ⟩ := R.nonempty_sequence_iso B 𝓕 h𝓕 F hF (fun n => (hr n).choose)
    (fun n => (hr n).choose_spec.some) hFF h𝓕qc hU hZ hZU hsupp
  exact (R.isZero_homology_origLift_sequence 𝓕 h𝓕 F m hm h𝓕qc hU hZ hZU hsupp n j hj).of_iso
    ((DerivedCategory.homologyFunctor B.left.Modules j).mapIso (Θ.app n).symm)

include hm h𝓕 in
/-- **The transforms of the cones of the transition maps of `Kₙ[n]` vanish in `[-m - 1, m]`**
once `n > 2m`, for `𝓕` supported on a closed subset of an affine open. -/
theorem isZero_homology_imgCone
    (h𝓕qc : 𝓕.IsQuasicoherent) {U : A.left.Opens} (hU : IsAffineOpen U) {Z : Set A.left}
    (hZ : IsClosed Z) (hZU : Z ⊆ U) (hsupp : SheafOfModules.supp 𝓕 ⊆ Z)
    (n : ℕ) (j : ℤ) (hn : 2 * m < n) (hj₁ : -(m : ℤ) - 1 ≤ j) :
    IsZero ((DerivedCategory.homologyFunctor B.left.Modules j).obj
      ((kernelIntegralTransform A.hom B.hom
        ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)).obj
        (((AlgebraicGeometry.transformedTerm A B R F R.isPerfect_single_right
          (n + 1))⟦(1 : ℤ)⟧)⟦(n : ℤ)⟧))) := by
  have hr := fun n => R.exists_iso_twistCoefficient 𝓕 h𝓕 h𝓕qc hU hZ hZU hsupp n
  let Ψ :=
    kernelIntegralTransform A.hom B.hom ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)
  let T := AlgebraicGeometry.transformedTerm A B R F R.isPerfect_single_right (n + 1)
  let e : Ψ.obj ((T⟦(1 : ℤ)⟧)⟦(n : ℤ)⟧) ≅ ((Ψ.obj T)⟦(1 : ℤ)⟧)⟦(n : ℤ)⟧ :=
    (Ψ.commShiftIso (n : ℤ)).app _ ≪≫
      (shiftFunctor _ (n : ℤ)).mapIso ((Ψ.commShiftIso (1 : ℤ)).app T)
  let e' : (DerivedCategory.homologyFunctor B.left.Modules j).obj (((Ψ.obj T)⟦(1 : ℤ)⟧)⟦(n : ℤ)⟧) ≅
      (DerivedCategory.homologyFunctor B.left.Modules (1 + (n + j))).obj (Ψ.obj T) :=
    (Stacks.HomologyShift.homologyShiftIso _ (n : ℤ) j (n + j) rfl).app _ ≪≫
      (Stacks.HomologyShift.homologyShiftIso _ 1 (n + j) (1 + (n + j)) rfl).app _
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor B.left.Modules j).mapIso e ≪≫ e')
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor B.left.Modules _).mapIso
    (R.imgComparison B 𝓕 h𝓕 F (fun n => (hr n).choose) (fun n => (hr n).choose_spec.some)
      (n + 1)).symm)
  have := R.isGE_origTransform 𝓕 h𝓕 (n + 1)
  have := R.isLE_origTransform 𝓕 h𝓕 h𝓕qc hU hZ hZU hsupp (n + 1)
  exact hm _ 0 0 le_rfl (isZero_homology_of_not_mem_Icc _ 0 0) _ (by rintro ⟨-, h⟩; omega)

omit [Smooth A.hom] [IsProper A.hom] [F.CommShift ℤ] [F.IsTriangulated] in
/-- The terms of the transformed complex are perfect. -/
theorem isPerfect_imgTerm (n : ℕ) : IsPerfect (X := (pullback A.hom B.hom).toRingedSpace)
    (AlgebraicGeometry.transformedTerm A B R F R.isPerfect_single_right n) :=
  isPerfect_dtenR _ _
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback.{u} _ _
      (isPerfect_singleFunctor_of_isFiniteLocallyFree A.left (R.left n)
        (R.left_finiteLocallyFree n)))
    (RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback.{u} _ _
      (F.obj (rightPerfect A R R.isPerfect_single_right n)).property)

omit [IsProper A.hom] [F.CommShift ℤ] [F.IsTriangulated] in
include hm in
/-- The terms of the transformed complex lie in degrees `≤ m`. -/
theorem isLE_imgTerm [Smooth B.hom] (n : ℕ) :
    (AlgebraicGeometry.transformedTerm A B R F R.isPerfect_single_right n).IsLE m := by
  have hG : (imageOfRight A B R F R.isPerfect_single_right n).IsLE m := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact hm _ 0 0 le_rfl
      (isZero_homology_of_not_mem_Icc (rightPerfect A R R.isPerfect_single_right n).obj 0 0) i
      (by rintro ⟨-, h⟩; omega)
  have h₁ := Stacks.Cohomology.DerivedInternalHomPullback.isLE_derivedPullback_obj_of_isFlat
    (pullback.fst A.hom B.hom).toLRSHom.toShHom
    (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _)
    ((DerivedCategory.singleFunctor A.left.Modules 0).obj (R.left n)) 0
    (inferInstanceAs (((DerivedCategory.singleFunctor A.left.Modules 0).obj (R.left n)).IsLE 0))
  have h₂ := Stacks.Cohomology.DerivedInternalHomPullback.isLE_derivedPullback_obj_of_isFlat
    (pullback.snd A.hom B.hom).toLRSHom.toShHom
    (Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _) _ (m : ℤ) hG
  have h := @Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProductFunctor _ _ _
      (pullback A.hom B.hom).toRingedSpace.sheaf _ _ _ _ _ _ _ _ 0 m h₁ h₂
  rwa [zero_add] at h

include hm in
/-- **The splitting `Kₙ[n] = K ⊕ Cₙ` gives `Φ_K(𝓕) ≅ F(𝓕)`** for `𝓕` supported on a closed subset
of an affine open: both are the part of `Ψ(Kₙ[n]) ≅ F(Ψ'(Mₙ[n]))` in degrees `> m - n` for `n`
large. -/
theorem nonempty_fourierMukai_iso_of_biprod [Smooth B.hom] [IsProper B.hom] (N : ℕ)
    (P : DerivedCategory (pullback A.hom B.hom).Modules)
    (C : ℕ → DerivedCategory (pullback A.hom B.hom).Modules)
    (hP : IsPerfect (X := (pullback A.hom B.hom).toRingedSpace) P)
    (hCp : ∀ n, N ≤ n → IsPerfect (X := (pullback A.hom B.hom).toRingedSpace) (C n))
    (hCb : ∀ n, N ≤ n → ∀ i : ℤ, (i < -(m : ℤ) - (n : ℤ) ∨ (m : ℤ) - (n : ℤ) < i) →
      IsZero ((DerivedCategory.homologyFunctor (pullback A.hom B.hom).Modules i).obj (C n)))
    (e : ∀ n : ℕ, N ≤ n → (((R.imgPostnikov B F hF hFF).obj n)⟦(n : ℤ)⟧ ≅ P ⊞ C n))
    (h𝓕qc : 𝓕.IsQuasicoherent) {U : A.left.Opens} (hU : IsAffineOpen U) {Z : Set A.left}
    (hZ : IsClosed Z) (hZU : Z ⊆ U) (hsupp : SheafOfModules.supp 𝓕 ⊆ Z) :
    Nonempty ((fourierMukai A.hom B.hom P).obj
      ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕) ≅ (F.obj ⟨_, h𝓕⟩).obj) := by
  let t := DerivedCategory.TStructure.t (C := B.left.Modules)
  let ψ :=
    kernelIntegralTransform A.hom B.hom ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)
  have : IsNoetherian B.left := isNoetherian_of_locallyOfFiniteType B.hom
  have hPψ : IsPerfect (X := B.left.toRingedSpace) (ψ.obj P) :=
    isPerfect_fourierMukai_obj A.hom B.hom hP h𝓕
  obtain ⟨-, c, -, hc, -⟩ :=
    Stacks.AlgebraicGeometry.PerfectProperDirectImage.isCoherent_homology_and_bounds_of_isPerfect
      B.hom (ψ.obj P) hPψ
  let n : ℕ := N + 2 * m + 1 + (m + 1 - c).toNat
  have hnN : N ≤ n := by omega
  -- the splitting side
  let eK : ψ.obj (((R.imgPostnikov B F hF hFF).obj n)⟦(n : ℤ)⟧) ≅ ψ.obj (C n ⊞ P) :=
    ψ.mapIso (e n hnN ≪≫ biprod.braiding _ _)
  have hTK := ψ.map_distinguished _ (binaryBiproductTriangle_distinguished (C n) P)
  have hCn : (ψ.obj (C n)).IsLE ((m : ℤ) - n) := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact isZero_homology_kernelIntegralTransform_of_isLE A.hom B.hom 𝓕 h𝓕qc hU hZ hZU hsupp
      (C n) (isQCohAll_of_isPerfect (hCp n hnN)) ((m : ℤ) - n)
      ((DerivedCategory.isLE_iff _ _).2 fun j hj => hCb n hnN j (Or.inr hj)) i hi
  have hPn : (ψ.obj P).IsGE ((m : ℤ) - n + 1) := by
    have := hc
    exact DerivedCategory.TStructure.t.isGE_of_ge (ψ.obj P) ((m : ℤ) - n + 1) c (by omega)
  obtain ⟨φ₁'⟩ := t.nonempty_iso_truncGE_of_distTriang _ hTK ((m : ℤ) - n) hCn hPn
  let φ₁ := φ₁' ≪≫ (t.truncGE ((m : ℤ) - n + 1)).mapIso eK.symm
  -- the side of the Postnikov system of the diagonal
  have hr := fun n => R.exists_iso_twistCoefficient 𝓕 h𝓕 h𝓕qc hU hZ hZU hsupp n
  obtain ⟨Θ⟩ := R.nonempty_sequence_iso B 𝓕 h𝓕 F hF (fun n => (hr n).choose)
    (fun n => (hr n).choose_spec.some) hFF h𝓕qc hU hZ hZU hsupp
  obtain ⟨TY, hTY, ⟨e₂⟩, ⟨e₃⟩, hW⟩ :=
    R.exists_distTriang_origLift_sequence 𝓕 h𝓕 F m hm h𝓕qc hU hZ hZU hsupp n (by omega)
  have h₁ : TY.obj₁.IsLE ((m : ℤ) - n) := (DerivedCategory.isLE_iff _ _).2 hW
  have h₃ : TY.obj₃.IsGE ((m : ℤ) - n + 1) := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact (hm ⟨_, h𝓕⟩ 0 0 le_rfl (isZero_homology_of_not_mem_Icc _ 0 0) i
      (by rintro ⟨h, -⟩; omega)).of_iso
      ((DerivedCategory.homologyFunctor B.left.Modules i).mapIso e₃)
  obtain ⟨φ₂⟩ := t.nonempty_iso_truncGE_of_distTriang TY hTY ((m : ℤ) - n) h₁ h₃
  exact ⟨φ₁ ≪≫ (t.truncGE ((m : ℤ) - n + 1)).mapIso ((Θ.app n).symm ≪≫ e₂.symm) ≪≫ φ₂.symm ≪≫
    e₃⟩

end DiagonalResolution

end Bands

/-! ### From point-supported modules to all zero-dimensional ones -/

section Pieces

variable {X Y S : Scheme.{u}} [IsNoetherian X]

/-- Coherent modules supported on a closed subset of an affine open. -/
def PointSupported (𝓕 : X.Modules) : Prop :=
  𝓕.IsCoherent ∧ ∃ (U : X.Opens) (_ : IsAffineOpen U) (Z : Set X) (_ : IsClosed Z),
    Z ⊆ U ∧ SheafOfModules.supp 𝓕 ⊆ Z

open Stacks.AlgebraicGeometry.DerivedVarieties.Orlov in
/-- **A zero-dimensional coherent module is a finite sum of point-supported ones.** -/
theorem exists_iso_biproduct_pointSupported (𝓕 : X.Modules) (h𝓕 : 𝓕.IsCoherent)
    (hdim : topologicalKrullDim (SheafOfModules.supp 𝓕) = 0) :
    ∃ (n : ℕ) (𝓕ᵢ : Fin n → X.Modules), (∀ i, PointSupported (𝓕ᵢ i)) ∧ Nonempty (𝓕 ≅ ⨁ 𝓕ᵢ) := by
  obtain ⟨n, 𝓕ᵢ, U, x, -, -, hcl, hxU, -, hcoh, hsupp, -, ⟨e⟩⟩ :=
    exists_iso_biproduct_of_topologicalKrullDim_supp_le_zero
      𝓕 h𝓕 hdim.le
  refine ⟨n, 𝓕ᵢ, fun i => ⟨hcoh i, U i, (U i).2, {x i}, hcl i, ?_, (hsupp i).le⟩, ⟨e⟩⟩
  simpa using hxU i

/-- **Vanishing of a homological invariant of the transform on point-supported modules passes to
zero-dimensional ones**, for any additive functor of the module. -/
theorem isZero_of_pointSupported {C : Type*} [Category C] [Preadditive C]
    (G : X.Modules ⥤ C) [G.Additive] (hG : ∀ 𝓕 : X.Modules, PointSupported 𝓕 → IsZero (G.obj 𝓕))
    (𝓕 : X.Modules) (h𝓕 : 𝓕.IsCoherent) (hdim : topologicalKrullDim (SheafOfModules.supp 𝓕) = 0) :
    IsZero (G.obj 𝓕) := by
  obtain ⟨n, 𝓕ᵢ, h, ⟨e⟩⟩ := exists_iso_biproduct_pointSupported 𝓕 h𝓕 hdim
  exact (CategoryTheory.Limits.isZero_obj_biproduct_of_isZero G (fun i => hG _ (h i))).of_iso
    (G.mapIso e)

/-- `𝓕 ↦ Hʲ(R pr_{2,*}(pr_1^*𝓕 ⊗^𝐋 K))`, as a functor of the module. -/
def fibreHomologyFunctor (f : X ⟶ S) (g : Y ⟶ S) (K : DerivedCategory (pullback f g).Modules)
    (j : ℤ) : X.Modules ⥤ Y.Modules :=
  Scheme.Modules.pullback (pullback.fst f g) ⋙ DerivedCategory.singleFunctor _ 0 ⋙
    (derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).flip.obj K ⋙
      fourierMukaiPushforward f g ⋙ DerivedCategory.homologyFunctor Y.Modules j

/-- The functor `fibreHomologyFunctor f g K j` is additive. -/
instance (f : X ⟶ S) (g : Y ⟶ S) (K : DerivedCategory (pullback f g).Modules) (j : ℤ) :
    (fibreHomologyFunctor f g K j).Additive := by
  let := (canonicalDerivedTensorProduct (pullback f g).toRingedSpace.sheaf).commShift_left K
  have := (canonicalDerivedTensorProduct (pullback f g).toRingedSpace.sheaf).exact_left K
  let := AlgebraicGeometry.commShift_pushforward f g
  have := AlgebraicGeometry.isTriangulated_pushforward f g
  have : (Scheme.Modules.pullback (pullback.fst f g)).Additive := inferInstance
  have : ((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).flip.obj K).Additive :=
    inferInstance
  have : (fourierMukaiPushforward f g).Additive := inferInstance
  have : (DerivedCategory.singleFunctor (pullback f g).Modules 0).Additive := inferInstance
  refine ⟨fun {M M'} a b => ?_⟩
  change (DerivedCategory.homologyFunctor Y.Modules j).map ((fourierMukaiPushforward f g).map
      (((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).flip.obj K).map
        ((DerivedCategory.singleFunctor (pullback f g).Modules 0).map
          ((Scheme.Modules.pullback (pullback.fst f g)).map (a + b))))) = _
  rw [Functor.map_add, Functor.map_add]
  have h₃ := ((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).flip.obj K).map_add
    (f := (DerivedCategory.singleFunctor (pullback f g).Modules 0).map
      ((Scheme.Modules.pullback (pullback.fst f g)).map a))
    (g := (DerivedCategory.singleFunctor (pullback f g).Modules 0).map
      ((Scheme.Modules.pullback (pullback.fst f g)).map b))
  refine (congrArg (fun x => (DerivedCategory.homologyFunctor Y.Modules j).map
    ((fourierMukaiPushforward f g).map x)) h₃).trans ?_
  have h₄ := (fourierMukaiPushforward f g).map_add
    (f := ((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).flip.obj K).map
      ((DerivedCategory.singleFunctor (pullback f g).Modules 0).map
        ((Scheme.Modules.pullback (pullback.fst f g)).map a)))
    (g := ((derivedTensorProductFunctor (pullback f g).toRingedSpace.sheaf).flip.obj K).map
      ((DerivedCategory.singleFunctor (pullback f g).Modules 0).map
        ((Scheme.Modules.pullback (pullback.fst f g)).map b)))
  refine (congrArg (fun x => (DerivedCategory.homologyFunctor Y.Modules j).map x) h₄).trans ?_
  exact (DerivedCategory.homologyFunctor Y.Modules j).map_add

end Pieces

/-! ### Part A -/

/-- **Part A of the object-wise Orlov theorem: the construction of [Stacks, Section 0G07].** For
smooth proper `K`-schemes `X`, `Y` and a `K`-linear exact fully faithful
`F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` there is a perfect kernel `P` on `X ×_K Y` whose Fourier-Mukai
functor agrees with `F` on every coherent `𝒪_X`-module with zero-dimensional support. -/
theorem fourierMukaiAgreesOnZeroDimensional (K : Type u) [Field K] :
    FourierMukaiAgreesOnZeroDimensional K := by
  intro A B hAs hAp hBs hBp
  let : Linear K A.left.Modules := modulesLinear K A
  let : Linear K B.left.Modules := modulesLinear K B
  intro F hlin hcs htri hFF'
  obtain ⟨hFF⟩ := hFF'
  let := hcs
  have : F.IsTriangulated := htri
  have := hAs
  have := hAp
  have := hBs
  have := hBp
  -- `X` is regular and Noetherian, so it has the resolution property
  have hreg : IsRegular A.left := isRegular_of_smooth_over_field A.hom
  have : CompactSpace A.left := (quasiCompact_iff_compactSpace A.hom).mp inferInstance
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  have : IsNoetherian A.left := ⟨⟩
  have hsepT : IsSeparated (terminal.from A.left) := by
    have h : terminal.from A.left = A.hom ≫ terminal.from (Spec (.of K)) := terminal.hom_ext _ _
    rw [h]; infer_instance
  have : HasResolutionProperty A.left :=
    hasResolutionProperty_of_isRegular_of_isNoetherian A.left hreg
  obtain ⟨R⟩ := nonempty_diagonalResolution_of_externalTensorCovers A.hom
    fun M hM => (nonempty_externalTensorCover K A.hom M hM).some
  have : CompactSpace B.left := (quasiCompact_iff_compactSpace B.hom).mp inferInstance
  -- the uniform bound of `F`
  obtain ⟨m, hm⟩ := exists_isZero_homology_perfectFunctor_obj A.hom B.hom F
  -- the Postnikov system of the transformed complex and its transition triangles
  let Q := R.imgPostnikov B F hlin hFF
  let Kn : ℕ → DerivedCategory (pullback A.hom B.hom).Modules := fun n => (Q.obj n)⟦(n : ℤ)⟧
  choose u w hT using fun n => Q.exists_distTriang_sequenceStep n
  have hpt : ∀ 𝓕 : A.left.Modules, PointSupported 𝓕 →
      ∃ (h𝓕 : IsPerfect (X := A.left.toRingedSpace)
        ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕)) (h𝓕qc : 𝓕.IsQuasicoherent)
        (U : A.left.Opens) (_ : IsAffineOpen U) (Z : Set A.left) (_ : IsClosed Z) (_ : Z ⊆ U),
        SheafOfModules.supp 𝓕 ⊆ Z := by
    rintro 𝓕 ⟨hcoh, U, hU, Z, hZ, hZU, hsupp⟩
    have := hcoh
    exact ⟨isPerfect_single_of_isCoherent_of_isRegular hreg 𝓕,
      (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent 𝓕).1,
      U, hU, Z, hZ, hZU, hsupp⟩
  have hflat : AlgebraicGeometry.IsFlat (fourierMukaiFst A.hom B.hom) :=
    Stacks.Cohomology.PseudoCoherence.FlatDescent.isFlat_toShHom _
  -- the hypotheses of [Stacks, Tag 0FZ9]
  have hperf : ∀ n, RingedSpace.IsPerfect (X := (pullback A.hom B.hom).toRingedSpace) (Kn n) :=
    fun n => Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift
      (Q.prop_obj (fun K : DerivedCategory (pullback A.hom B.hom).Modules =>
        IsPerfect (X := (pullback A.hom B.hom).toRingedSpace) K)
        (fun e h => Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso
          (X := (pullback A.hom B.hom).toRingedSpace) e h) (R.isPerfect_imgTerm B F) n) (n : ℤ)
  have hupper : ∀ (n : ℕ) (j : ℤ), (m : ℤ) < j →
      IsZero ((DerivedCategory.homologyFunctor (pullback A.hom B.hom).Modules j).obj (Kn n)) :=
    fun n j hj => @DerivedCategory.isZero_of_isLE _ _ _ _ (Kn n) m j hj
      (Q.isLE_shift_obj_of_isLE m (R.isLE_imgTerm B F m hm) n)
  have hfibreBand : ∀ F' : A.left.Modules, F'.IsCoherent →
      topologicalKrullDim (SheafOfModules.supp F') = 0 → ∀ (n : ℕ) (j : ℤ), ¬ InBands m n j →
      IsZero ((DerivedCategory.homologyFunctor B.left.Modules j).obj
        (fibreTransform A.hom B.hom (Kn n) F')) := by
    intro F' hF' hdim n j hj
    refine isZero_of_pointSupported (fibreHomologyFunctor A.hom B.hom (Kn n) j) (fun 𝓕 h => ?_)
      F' hF' hdim
    obtain ⟨h𝓕, h𝓕qc, U, hU, Z, hZ, hZU, hsupp⟩ := hpt 𝓕 h
    exact (R.isZero_homology_imgPostnikov_sequence 𝓕 h𝓕 B F hlin hFF m hm h𝓕qc hU hZ hZU hsupp
      n j hj).of_iso ((DerivedCategory.homologyFunctor B.left.Modules j).mapIso
        ((fibreTransformFunctorIso A.hom B.hom hflat 𝓕).app (Kn n)))
  have hfibreStable := isIso_homologyMap_fibreTransformFunctor_map_of_distTriang A.hom B.hom Kn
    (fun n => ((AlgebraicGeometry.transformedTerm A B R F R.isPerfect_single_right
      (n + 1))⟦(1 : ℤ)⟧)⟦(n : ℤ)⟧)
    (fun n => Q.sequenceStep n) u w hT m (by
      rintro F' hF' hdim n j hn hj₁ -
      refine isZero_of_pointSupported (fibreHomologyFunctor A.hom B.hom _ j) (fun 𝓕 h => ?_)
        F' hF' hdim
      obtain ⟨h𝓕, h𝓕qc, U, hU, Z, hZ, hZU, hsupp⟩ := hpt 𝓕 h
      exact (R.isZero_homology_imgCone 𝓕 h𝓕 B F m hm h𝓕qc hU hZ hZU hsupp n j hn
        hj₁).of_iso ((DerivedCategory.homologyFunctor B.left.Modules j).mapIso
          ((fibreTransformFunctorIso A.hom B.hom hflat 𝓕).app _)))
  -- the splitting
  obtain ⟨N, P, C, hP, hCp, -, hCb, e, -⟩ := exists_stable_biprod_of_smooth_of_fibreBands K
    A.hom B.hom Kn (fun n => Q.sequenceStep n) m hperf hupper hfibreBand hfibreStable
  refine ⟨P, hP, fun 𝓕 hcoh hdim h𝓕 => ?_⟩
  -- the point-supported pieces
  have hagree : ∀ (𝓕' : A.left.Modules) (_ : PointSupported 𝓕')
      (h' : IsPerfect (X := A.left.toRingedSpace)
        ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕')),
      Nonempty ((fourierMukai A.hom B.hom P).obj
        ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕') ≅ (F.obj ⟨_, h'⟩).obj) := by
    intro 𝓕' h h'
    obtain ⟨-, h𝓕qc, U, hU, Z, hZ, hZU, hsupp⟩ := hpt 𝓕' h
    exact R.nonempty_fourierMukai_iso_of_biprod 𝓕' h' B F hlin hFF m hm N P C hP hCp hCb e h𝓕qc
      hU hZ hZU hsupp
  obtain ⟨n, 𝓕ᵢ, hpts, ⟨eD⟩⟩ := exists_iso_biproduct_pointSupported 𝓕 hcoh hdim
  have hpᵢ : ∀ i, IsPerfect (X := A.left.toRingedSpace)
      ((DerivedCategory.singleFunctor A.left.Modules 0).obj (𝓕ᵢ i)) :=
    fun i => (hpt _ (hpts i)).1
  let Zᵢ : Fin n → PerfectDerivedCategory A.left := fun i => ⟨_, hpᵢ i⟩
  let eS : (⟨_, h𝓕⟩ : PerfectDerivedCategory A.left) ≅ ⨁ Zᵢ :=
    ObjectProperty.isoMk _ ((DerivedCategory.singleFunctor A.left.Modules 0).mapIso eD ≪≫
      (DerivedCategory.singleFunctor A.left.Modules 0).mapBiproduct 𝓕ᵢ ≪≫
      ((ObjectProperty.ι _).mapBiproduct Zᵢ).symm)
  let eF : (F.obj ⟨_, h𝓕⟩).obj ≅ ⨁ fun i => (F.obj (Zᵢ i)).obj :=
    (ObjectProperty.ι _).mapIso (F.mapIso eS ≪≫ F.mapBiproduct Zᵢ) ≪≫
      (ObjectProperty.ι _).mapBiproduct _
  let eΦ : (fourierMukai A.hom B.hom P).obj
      ((DerivedCategory.singleFunctor A.left.Modules 0).obj 𝓕) ≅
      ⨁ fun i => (fourierMukai A.hom B.hom P).obj
        ((DerivedCategory.singleFunctor A.left.Modules 0).obj (𝓕ᵢ i)) :=
    (DerivedCategory.singleFunctor A.left.Modules 0 ⋙ fourierMukai A.hom B.hom P).mapIso eD ≪≫
      (DerivedCategory.singleFunctor A.left.Modules 0 ⋙ fourierMukai A.hom B.hom P).mapBiproduct 𝓕ᵢ
  exact ⟨eΦ ≪≫ biproduct.mapIso (fun i => (hagree _ (hpts i) (hpᵢ i)).some) ≪≫ eF.symm⟩

end AlgebraicGeometry
