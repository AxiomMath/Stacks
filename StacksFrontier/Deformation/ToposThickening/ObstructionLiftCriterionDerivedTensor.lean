module

public import StacksFrontier.Deformation.ToposThickening.CurvatureClassDerivedTensor
public import StacksFrontier.Deformation.ToposThickening.ObstructionLiftCriterion
import StacksCore.Tactic.StacksAttribute

/-!
# The obstruction criterion with values in the derived tensor product

Let `C` be a site, `f : O ⟶ O₀` a surjection of sheaves of commutative rings whose kernel is an
ideal sheaf `I` of square zero, and `K₀ ∈ D⁻(O₀)`. Stacks 0DIW: the canonical class
`ω(K₀) ∈ Ext²_{O₀}(K₀, K₀ ⊗^L_{O₀} I)` of Tag 0DIU vanishes if and only if there is
`K ∈ D⁻(O)` with `K ⊗^L_O O₀ ≅ K₀` in `D(O₀)`.

Here `ω(K₀)` is `Deformation.ComplexLift.tensorOmegaMinus`, with values in the derived tensor
product `Deformation.ComplexLift.derivedTensorRight I` constructed from flat resolutions
(Tag 0794), and `- ⊗^L_O O₀` is the constructed derived base change
`Deformation.ComplexLift.derivedExtensionOfScalarsData`. Nothing is assumed of `I` beyond being
the square-zero kernel of `f`: unlike the criterion of
`StacksFrontier.Deformation.ToposThickening.ObstructionLiftCriterion`, which is stated against a
supplied `Deformation.ComplexLift.DerivedIdealTensor` and so concerns flat `I` only, no datum
for the derived tensor product is taken as input.

The proof is the one of the source. For `(2) ⇒ (1)`, represent `K` by a bounded above complex
`P` of flat `O`-modules; its degreewise reduction represents `K ⊗^L_O O₀` and is a flat lift of
itself whose lifted differential squares to zero. For `(1) ⇒ (2)`, the vanishing of `ω(K₀)` says
the curvature of a bounded above flat lift is zero in `D(O₀)`, and the correction of
`Deformation.ComplexLift.correctedComplex` produces the lift.

## Main results

* `Deformation.ComplexLift.tensorObstruction_eq_zero_iff`: the class computed by a flat lift
  vanishes iff the curvature of the lift vanishes in `D(O₀)`.
* `Deformation.ComplexLift.tensorOmegaObj_eq_zero_iff`: the vanishing of `ω` does not depend on
  the complex representing an object.
* `Deformation.ComplexLift.nonempty_derivedLift_of_tensorOmegaMinus_eq_zero`: **Tag 0DIW,
  `(1) ⇒ (2)`**.
* `Deformation.ComplexLift.tensorOmegaMinus_eq_zero_of_nonempty_derivedLift`: **Tag 0DIW,
  `(2) ⇒ (1)`**.
* `Deformation.ComplexLift.tensorOmegaMinus_eq_zero_iff_nonempty_derivedLift`: **Tag 0DIW**.

## References

* [Stacks Project, Tag 0DIW](https://stacks.math.columbia.edu/tag/0DIW)
* [Stacks Project, Tag 0DIU](https://stacks.math.columbia.edu/tag/0DIU)
* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w d d₀

namespace Deformation.ComplexLift

attribute [-instance] CategoryTheory.catToReflQuiver

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  {O O₀ : Sheaf J CommRingCat.{max u v w}} {f : O ⟶ O₀}
  {I : SheafMod O₀} {S : SquareZeroIdeal f I}

section DerivedTensor

variable [HasDerivedCategory.{d₀} (SheafMod O₀)]

/-- **The map computed from a flat lift vanishes iff its curvature vanishes in `D(O₀)`**: the
two differ by isomorphisms of the derived category, the comparison
`F₀ ⊗^L_{O₀} I ≅ F₀ ⊗_{O₀} I` being invertible on the reduction of the lift. -/
theorem tensorObstruction_eq_zero_iff {K₀ : CochainComplex (SheafMod O₀) ℤ} {L : FlatLift f K₀}
    (T : IdealKernel S L) :
    tensorObstruction.{v, u, max u v w, d₀} T = 0 ↔
      (DerivedCategory.Q (C := SheafMod O₀)).map (curvatureMap T) = 0 := by
  constructor
  · intro h
    simp only [tensorObstruction, tensorCurvature, Category.assoc] at h
    rw [Preadditive.IsIso.comp_left_eq_zero] at h
    exact (Preadditive.IsIso.comp_right_eq_zero _ _).1 h
  · intro h
    simp [tensorObstruction, tensorCurvature, h]

/-- **`ω` of an object of `D(O₀)` vanishes iff `ω` of any complex representing it vanishes**:
`ω` is natural along isomorphisms of `D(O₀)`. -/
theorem tensorOmegaObj_eq_zero_iff (hf : Sheaf.IsLocallySurjective f) (S : SquareZeroIdeal f I)
    {X : DerivedCategory (SheafMod O₀)}
    (hX : ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      IsZero ((DerivedCategory.homologyFunctor (SheafMod O₀) n).obj X))
    {K₀ : CochainComplex (SheafMod O₀) ℤ} (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n))
    (e : DerivedCategory.Q.obj K₀ ≅ X) :
    tensorOmegaObj.{v, u, w, d₀} hf S X hX = 0 ↔ tensorOmega.{v, u, w, d₀} hf S K₀ hK = 0 := by
  let ψ := e.hom ≫ (DerivedCategory.Q.objObjPreimageIso X).inv
  have hn := tensorOmega_natural_derived.{v, u, w, d₀} hf S hK (homology_objPreimage_isZero hX) ψ
  simp only [tensorOmegaObj]
  rw [Preadditive.IsIso.comp_left_eq_zero, Preadditive.IsIso.comp_right_eq_zero]
  constructor
  · intro h
    have h' : tensorOmega.{v, u, w, d₀} hf S K₀ hK ≫
        (CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀)) (2 : ℤ)).map
          ((derivedTensorRight.{d₀} I).map ψ) = 0 := by
      rw [← hn, h, comp_zero]
    exact (Preadditive.IsIso.comp_right_eq_zero _ _).1 h'
  · intro h
    have h' : ψ ≫ tensorOmega.{v, u, w, d₀} hf S _ (homology_objPreimage_isZero hX) = 0 := by
      rw [hn, h, zero_comp]
    exact (Preadditive.IsIso.comp_left_eq_zero _ _).1 h'

/-- **`ω` of the reduction of a bounded above complex of flat `O`-modules vanishes**: the
complex is a flat lift of its reduction whose lifted differential squares to zero. -/
theorem tensorOmega_eq_zero_of_flatComplex (hf : Sheaf.IsLocallySurjective f)
    (S : SquareZeroIdeal f I) (P : CochainComplex (SheafMod O) ℤ)
    (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (O := O) (P.X n))
    (hbdd : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (P.X n))
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n →
      IsZero (((extensionOfScalarsCochainComplex J f).obj P).homology n)) :
    tensorOmega.{v, u, w, d₀} hf S ((extensionOfScalarsCochainComplex J f).obj P) hK = 0 := by
  rw [tensorOmega_eq hf S hK (idealKernel hf S (FlatLift.ofFlatComplex f P hflat hbdd)),
    tensorObstruction_eq_zero_iff, curvatureMap_eq_zero _ (fun n => P.d_comp_d _ _ _),
    Functor.map_zero]

variable [HasDerivedCategory.{d} (SheafMod O)]

/-- **A flat lift whose curvature vanishes in `D(O₀)` yields a lift in `D⁻(O)`.** This is the
construction of the source: the curvature becomes null-homotopic after a quasi-isomorphism
`α : G₀ ⟶ F₀`, the homotopy corrects the differential of `F ×_{F₀} G₀`, and a bounded above flat
resolution of the corrected complex has reduction quasi-isomorphic to `G₀`. -/
theorem nonempty_derivedLift_of_Q_map_curvatureMap_eq_zero (hf : Sheaf.IsLocallySurjective f)
    (S : SquareZeroIdeal f I) (T : DerivedExtensionOfScalars f)
    (E : DerivedCategory.Minus (SheafMod O₀)) {K₀ : CochainComplex (SheafMod O₀) ℤ}
    (e : DerivedCategory.Q.obj K₀ ≅ E.obj) (L : FlatLift f K₀)
    (hQ : (DerivedCategory.Q (C := SheafMod O₀)).map (curvatureMap (idealKernel hf S L)) = 0) :
    Nonempty (DerivedLift T E) := by
  obtain ⟨N, hN⟩ := L.boundedAbove
  have hFz : ∀ n, N < n → IsZero (L.F.X n) := fun n hn => hN n hn.le
  have : L.baseChange.complex.IsStrictlyLE N := by
    rw [CochainComplex.isStrictlyLE_iff]
    exact fun n hn => L.isZero_reduction (hFz n hn)
  obtain ⟨G₀, hG, α, hα, ⟨h⟩⟩ :=
    exists_bounded_quasiIso_homotopy_of_Q_map_eq_zero N (curvatureMap (idealKernel hf S L)) hQ
  obtain ⟨k, hk⟩ := exists_correction_of_homotopy (idealKernel hf S L) α h
  have := isStrictlyLE_correctedComplex (idealKernel hf S L) α k hk N hFz
  obtain ⟨E', γ, -, hγ, hflat, hE'⟩ :=
    exists_isFlat_quasiIso_isStrictlyLE O N (correctedComplex (idealKernel hf S L) α k hk)
  have hδ := quasiIso_correctedTranspose hf (idealKernel hf S L) α k hk N γ hflat hE'
  exact nonempty_derivedLift_of_flatComplex T E N hflat hE'
    (asIso (DerivedCategory.Q.map
        (flatComplexTranspose (γ ≫ correctedProj (idealKernel hf S L) α k hk))) ≪≫
      asIso (DerivedCategory.Q.map α) ≪≫ asIso (DerivedCategory.Q.map L.baseChange.map) ≪≫ e)

/-- **Stacks 0DIW, `(1) ⇒ (2)`, for the canonical class with values in the derived tensor
product.** If `ω(K₀) : K₀ ⟶ (K₀ ⊗^L_{O₀} I)[2]` vanishes, there is `K ∈ D⁻(O)` with
`K ⊗^L_O O₀ ≅ K₀` in `D(O₀)`, for any derived base change `T` along `f`. -/
theorem nonempty_derivedLift_of_tensorOmegaMinus_eq_zero (hf : Sheaf.IsLocallySurjective f)
    (S : SquareZeroIdeal f I) (T : DerivedExtensionOfScalars f)
    (E : DerivedCategory.Minus (SheafMod O₀)) (h0 : tensorOmegaMinus.{v, u, w, d₀} hf S E = 0) :
    Nonempty (DerivedLift T E) := by
  let e : DerivedCategory.Q.obj (DerivedCategory.Q.objPreimage E.obj) ≅ E.obj :=
    DerivedCategory.Q.objObjPreimageIso E.obj
  have hK := homology_boundedAbove_of_iso E e
  rw [tensorOmegaMinus, tensorOmegaObj_eq_zero_iff hf S _ hK e] at h0
  obtain ⟨L⟩ := exists_flatLift hf _ hK
  exact nonempty_derivedLift_of_Q_map_curvatureMap_eq_zero hf S T E e L
    ((tensorObstruction_eq_zero_iff _).1 ((tensorOmega_eq hf S hK _).symm.trans h0))

/-- **Stacks 0DIW, `(2) ⇒ (1)`, for the canonical class with values in the derived tensor
product.** If there is `K ∈ D⁻(O)` with `K ⊗^L_O O₀ ≅ K₀` in `D(O₀)`, for any derived base
change `T` along `f`, then `ω(K₀) = 0`: represent `K` by a bounded above complex `P` of flat
`O`-modules; `K ⊗^L_O O₀` is represented by its degreewise reduction `P₀`, whose class vanishes
because the differential of `P` squares to zero, and `ω` is natural along `P₀ ≅ K₀`. -/
theorem tensorOmegaMinus_eq_zero_of_nonempty_derivedLift (hf : Sheaf.IsLocallySurjective f)
    (S : SquareZeroIdeal f I) (T : DerivedExtensionOfScalars f)
    (E : DerivedCategory.Minus (SheafMod O₀)) (hL : Nonempty (DerivedLift T E)) :
    tensorOmegaMinus.{v, u, w, d₀} hf S E = 0 := by
  obtain ⟨L⟩ := hL
  let L' := L.transport (T' := derivedExtensionOfScalarsData.{d, d₀} f)
  obtain ⟨b, P, hflat, hLE, ⟨r⟩⟩ := exists_isFlat_representative O L'.K
  have hcell := isFlatCellular_of_isStrictlyLE O P b hflat
  have := isIso_derivedExtensionOfScalarsCounit_app.{d, d₀} f P hcell
  have hP₀ : CochainComplex.IsStrictlyLE ((extensionOfScalarsCochainComplex J f).obj P) b :=
    isStrictlyLE_map_extensionOfScalars f b P hLE
  let ψ : DerivedCategory.Q.obj ((extensionOfScalarsCochainComplex J f).obj P) ≅ E.obj :=
    (asIso ((derivedExtensionOfScalarsCounit.{d, d₀} f).app P)).symm ≪≫
      (derivedExtensionOfScalars.{d, d₀} f).mapIso r ≪≫ L'.identification
  have hbdd : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (P.X n) :=
    ⟨b + 1, fun n hn => P.isZero_of_isStrictlyLE b n (by omega)⟩
  have hK₀ := homology_boundedAbove ((extensionOfScalarsCochainComplex J f).obj P) b
  rw [tensorOmegaMinus, tensorOmegaObj_eq_zero_iff hf S _ hK₀ ψ]
  exact tensorOmega_eq_zero_of_flatComplex hf S P hflat hbdd hK₀

/-- **Stacks 0DIW.** Let `C` be a site and `f : O ⟶ O₀` a surjection of sheaves of commutative
rings whose kernel is an ideal sheaf `I` of square zero (`S`), with no further hypothesis on
`I`. For every object `K₀` of `D⁻(O₀)` the following are equivalent:

1. the canonical class `ω(K₀) : K₀ ⟶ (K₀ ⊗^L_{O₀} I)[2]` of Tag 0DIU,
   `Deformation.ComplexLift.tensorOmegaMinus`, is zero;
2. there exists `K ∈ D⁻(O)` with `K ⊗^L_O O₀ ≅ K₀` in `D(O₀)`.

Here `- ⊗^L_{O₀} I` is the derived tensor product `Deformation.ComplexLift.derivedTensorRight I`
and `- ⊗^L_O O₀` the derived base change `Deformation.ComplexLift.derivedExtensionOfScalarsData`,
both constructed from flat resolutions (Tag 0794). -/
@[stacks 0DIW "ω is the class tensorOmegaMinus with values in the derived tensor product
K₀ ⊗^L I, and K ⊗^L O₀ the derived base change derivedExtensionOfScalarsData; no flatness on I"]
theorem tensorOmegaMinus_eq_zero_iff_nonempty_derivedLift (hf : Sheaf.IsLocallySurjective f)
    (S : SquareZeroIdeal f I) (E : DerivedCategory.Minus (SheafMod O₀)) :
    tensorOmegaMinus.{v, u, w, d₀} hf S E = 0 ↔
      Nonempty (DerivedLift (derivedExtensionOfScalarsData.{d, d₀} f) E) :=
  ⟨nonempty_derivedLift_of_tensorOmegaMinus_eq_zero hf S _ E,
    tensorOmegaMinus_eq_zero_of_nonempty_derivedLift hf S _ E⟩

end DerivedTensor

end Deformation.ComplexLift

end
