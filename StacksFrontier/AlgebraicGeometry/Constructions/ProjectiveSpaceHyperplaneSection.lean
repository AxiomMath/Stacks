module

public import Mathlib.Algebra.Module.Submodule.Union
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceSectionMultiplication
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finite
public import StacksFrontier.AlgebraicGeometry.ProjIdealSheaf.Basic
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.ProjStalkGlobalSections.TwistTrivialization
public import StacksFrontier.AlgebraicGeometry.ProjTwistSection.Basic
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MonoidalRightUnitorCompare
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MonoNonvanishing

/-!
# Hyperplane sections of projective space avoiding associated points

Let `k` be an infinite field and let `ℱ` be a coherent module on `ℙⁿ_k = Proj k[T₀, …, Tₙ]`.
There is a nonzero global section `s` of `𝒪(1)`, given by a linear form, whose nonvanishing locus
contains every associated point of `ℱ`. For a section `s` of `𝒪(1)` on `ℙⁿ_S` that does not
vanish near any associated point of `ℱ(-1)`, the sequence `0 ⟶ ℱ(-1) ⟶ ℱ ⟶ i_*i^*ℱ ⟶ 0` is short
exact, where `i : H ⟶ ℙⁿ_S` is the hyperplane cut out by `s` and the first arrow is
multiplication by `s`.

## Main results

* `exists_mem_polyGradingOne_notMem`: over an infinite field a single nonzero linear form avoids
  the homogeneous primes of any finite set of points of `ℙⁿ_k`.
* `finite_associatedPoints`: a coherent module on `ℙⁿ_k` has finitely many associated points.
* `exists_homogeneousSection_nonvanishing`: for `ℱ` coherent there is a nonzero global section of
  `𝒪(1)` whose nonvanishing locus contains every associated point of `ℱ`.
* `mono_twistSectionMulNegOne_of_nonvanishing`: multiplication by such a section is a
  monomorphism `ℱ(-1) ⟶ ℱ`.
* `shortExact_hyperplaneUnit_of_nonvanishing`: the short exact sequence
  `0 ⟶ ℱ(-1) ⟶ ℱ ⟶ i_*i^*ℱ ⟶ 0` on `ℙⁿ_S`.

## References

* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
* [Stacks Project, Tag 00LC](https://stacks.math.columbia.edu/tag/00LC)
* [Stacks Project, Tag 05AF](https://stacks.math.columbia.edu/tag/05AF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.ProjTwistSection

universe v u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHyperplaneSection

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k : Type u) [Field k] (n : ℕ)

/-- The twisting sheaf `𝒪(1)` on `Proj k[T₀, …, Tₙ]` is invertible. -/
instance isInvertible_twistingModule_one :
    Stacks.SheafOfModules.IsInvertible (AlgebraicGeometry.Proj (polyGrading k n)).presheaf
      (structureSheafRing
        (AlgebraicGeometry.Proj (polyGrading k n)).toRingedSpace).property
      (twistingModule (polyGrading k n) 1) :=
  Stacks.AlgebraicGeometry.ProjDegreeOne.isInvertible_twistingSheaf (polyGrading k n)
    (MvPolynomial.adjoin_homogeneousSubmodule_one_eq_top (Fin (n + 1)) k) 1

/-! ### Avoiding finitely many points -/

/-- Over an infinite field, given finitely many points of `Proj k[T₀, …, Tₙ]`, there is a nonzero
homogeneous polynomial of degree one lying in none of their homogeneous primes. -/
theorem exists_mem_polyGradingOne_notMem [Infinite k] {ι : Type v} [Finite ι]
    (xs : ι → ProjectiveSpectrum (polyGrading k n)) :
    ∃ (f : MvPolynomial (Fin (n + 1)) k) (_ : f ∈ polyGrading k n 1),
      f ≠ 0 ∧ ∀ j, f ∉ (xs j).asHomogeneousIdeal := by
  classical
  set V : Submodule k (MvPolynomial (Fin (n + 1)) k) := polyGrading k n 1
  set ys : Option ι → ProjectiveSpectrum (polyGrading k n) :=
    fun j ↦ j.elim (genericPoint k n) xs
  set p : Option ι → Submodule k V := fun j ↦
    Submodule.comap V.subtype (Submodule.restrictScalars k (ys j).asHomogeneousIdeal.toIdeal)
  have hne : ∀ j, p j ≠ ⊤ := by
    intro j htop
    obtain ⟨i, hi⟩ :=
      Stacks.AlgebraicGeometry.ProjStalkGlobalSections.exists_X_notMem_asHomogeneousIdeal
        k n (ys j)
    exact hi (htop ▸ Submodule.mem_top : (⟨MvPolynomial.X i, X_mem_one k n i⟩ : V) ∈ p j)
  obtain ⟨w, hw⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hne
  have hgen : (w : MvPolynomial (Fin (n + 1)) k) ∉ (genericPoint k n).asHomogeneousIdeal :=
    hw none
  exact ⟨w.1, w.2, fun h0 ↦ hgen (h0 ▸ HomogeneousIdeal.mem_iff.mp (Submodule.zero_mem _)),
    fun j ↦ hw (some j)⟩

/-! ### The hyperplane section of a coherent module -/

/-- The associated points of a coherent module on `ℙⁿ_k` form a finite set. -/
theorem finite_associatedPoints (F : (AlgebraicGeometry.Proj (polyGrading k n)).Modules)
    [F.IsCoherent] : (Stacks.Divisors.associatedPoints F).Finite := by
  have h := AlgebraicGeometry.associatedPoints_inter_finite F ⊤
    (by simpa using (isCompact_univ (X := ↥(AlgebraicGeometry.Proj (polyGrading k n)))))
  simpa using h

/-- Let `k` be an infinite field and let `ℱ` be a coherent module on `ℙⁿ_k = Proj k[T₀, …, Tₙ]`.
Then some nonzero linear form `f` gives a nonzero global section `f / 1` of `𝒪(1)` whose
nonvanishing locus contains every associated point of `ℱ`. -/
@[stacks 08A0 "the choice of the hyperplane section — a nonzero `s` vanishing at no associated \
point of `ℱ`, which is the one step needing `k` infinite; not the exact sequence"]
theorem exists_homogeneousSection_nonvanishing [Infinite k]
    (F : (AlgebraicGeometry.Proj (polyGrading k n)).Modules) [F.IsCoherent] :
    ∃ (f : MvPolynomial (Fin (n + 1)) k) (hf : f ∈ polyGrading k n 1), f ≠ 0 ∧
      (homogeneousSection (polyGrading k n) f hf).eval (op ⊤) ≠ 0 ∧
      Stacks.Divisors.associatedPoints F ⊆
        (Stacks.SheafOfModules.nonvanishingOpen
          (X := (AlgebraicGeometry.Proj (polyGrading k n)).toRingedSpace)
          (twistingModule (polyGrading k n) 1)
          (homogeneousSection (polyGrading k n) f hf) :
            Set ↥(AlgebraicGeometry.Proj (polyGrading k n))) := by
  have : Finite (Stacks.Divisors.associatedPoints F) := (finite_associatedPoints k n F).to_subtype
  obtain ⟨f, hf, hf0, hfx⟩ :=
    exists_mem_polyGradingOne_notMem k n
      (fun x : Stacks.Divisors.associatedPoints F => x.1)
  have key := fun (x : ProjectiveSpectrum _) (hx : f ∉ x.asHomogeneousIdeal) ↦
    basicOpen_le_nonvanishingOpen_homogeneousSection (polyGrading k n) f hf
      ((ProjectiveSpectrum.mem_basicOpen (polyGrading k n) f x).mpr hx)
  exact ⟨f, hf, hf0, fun hzero ↦
    key (genericPoint k n) (mt (eq_zero_of_mem_bot k n) hf0) (by simp [hzero]),
    fun x hx ↦ key x (hfx ⟨x, hx⟩)⟩

/-! ### The short exact sequence of [Stacks, Tag 08A0] -/

section Sequence

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso Stacks.SheafInternalHom.isLocalization_sheafify
  Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

open CategoryTheory.MonoidalCategory
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication
open Stacks.RelativeVeryAmple

/-- If `a = c ≫ d`, then `a ≫ b = c ≫ d ≫ b`. -/
private theorem comp_assoc_of_eq {C : Type v} [CategoryTheory.Category C] {A B D E : C}
    {a : A ⟶ D} {c : A ⟶ B} {d : B ⟶ D} (h : a = c ≫ d) (b : D ⟶ E) : a ≫ b = c ≫ d ≫ b := by
  rw [h, CategoryTheory.Category.assoc]

/-- Multiplication by a global section `s` of `𝒪(1)` is a monomorphism `ℱ(-1) ⟶ ℱ` on `ℙⁿ_S` as
soon as `s` does not vanish near any associated point of `ℱ(-1)`. -/
theorem mono_twistSectionMulNegOne_of_nonvanishing (S : Scheme.{u})
    [IsLocallyNoetherian (projectiveSpaceOver n S)]
    (F : (projectiveSpaceOver n S).Modules) (s : (twistOver n S 1).sections)
    [(tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1))).IsQuasicoherent]
    [(tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1)) ⊗
        twistOver n S 1).IsQuasicoherent]
    (hW : ∀ x ∈ Stacks.Divisors.associatedPoints
        (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1))),
      ∃ W : (projectiveSpaceOver n S).Opens, x ∈ W ∧ ∀ y ∈ W,
        y ∈ Stacks.SheafOfModules.nonvanishingLocus
          (X := (projectiveSpaceOver n S).toRingedSpace) (twistOver n S 1) s) :
    CategoryTheory.Mono (twistSectionMulNegOne n S F s) := by
  have hA : twistNegOneMulSection n S F s =
      Stacks.TensorSectionNonvanishing.mulRight
          (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1)))
          (Stacks.SectionProduct.ofUnitHom (sectionHom (twistOver n S 1) s)) ≫
        (Stacks.AmplePullbackPart1.tensorIsoTensorModules (projectiveSpaceOver n S)
          (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1)))
          (twistOver n S 1)).hom :=
    (congrArg
      (fun k ↦ (Stacks.SheafOfModules.Invertible.tensorProductRightUnitor
        (projectiveSpaceOver n S).presheaf (projectiveSpaceOver n S).ringCatSheaf.property
        (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1)))).inv ≫ k)
      (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
        ⟨(projectiveSpaceOver n S).presheaf, (projectiveSpaceOver n S).IsSheaf⟩
        (𝟙 (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1))))
        (sectionHom (twistOver n S 1) s))).trans
    (AlgebraicGeometry.tensorProductRightUnitor_inv_comp_sheafifyWhiskerLeft
      (projectiveSpaceOver n S)
      (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1)))
      (sectionHom (twistOver n S 1) s))
  have heq : twistSectionMulNegOne n S F s =
      Stacks.TensorSectionNonvanishing.mulRight
          (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1)))
          (Stacks.SectionProduct.ofUnitHom (sectionHom (twistOver n S 1) s)) ≫
        (Stacks.AmplePullbackPart1.tensorIsoTensorModules (projectiveSpaceOver n S)
            (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1)))
            (twistOver n S 1) ≪≫ twistNegOneTensorIso n S F).hom :=
    (twistSectionMulNegOne_eq_comp n S F s).trans
      (comp_assoc_of_eq hA (twistNegOneTensorIso n S F).hom)
  have hs : Stacks.SectionProduct.monoidalUnitHomEquiv (twistOver n S 1)
      (Stacks.SectionProduct.ofUnitHom (sectionHom (twistOver n S 1) s)) = s :=
    Stacks.SectionProduct.monoidalUnitHomEquiv_ofUnitHom_unitHomEquiv_symm (twistOver n S 1) s
  have hpsi : ((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(projectiveSpaceOver n S).toRingedSpace.presheaf,
          (projectiveSpaceOver n S).toRingedSpace.IsSheaf⟩).obj (twistOver n S 1)).obj
        (twistOver n S (-1)) ≅ _root_.SheafOfModules.unit _ :=
    twistOverMulIso n S 1 (-1) ≪≫
      eqToIso (congrArg (twistOver n S) (show (1 : ℤ) + (-1) = 0 from by ring)) ≪≫
        twistZeroIsoUnit n S
  rw [heq]
  refine Stacks.SectionProduct.mono_mulRight_comp_of_associatedPoints
    (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1))) hpsi _ _ ?_
  intro x hx
  obtain ⟨W, hxW, hWL⟩ := hW x hx
  exact ⟨W, hxW, fun y hy ↦ by rw [hs]; exact hWL y hy⟩

/-- Let `S` be a scheme with `ℙⁿ_S` locally Noetherian, let `ℱ` be an `𝒪`-module on `ℙⁿ_S` with
`ℱ(-1)` and `ℱ(-1) ⊗ 𝒪(1)` quasi-coherent, and let `s` be a global section of `𝒪(1)` that does
not vanish near any associated point of `ℱ(-1)`. Writing `i : H ⟶ ℙⁿ_S` for the hyperplane cut
out by `s`, the sequence

`0 ⟶ ℱ(-1) ⟶ ℱ ⟶ i_* i^* ℱ ⟶ 0`

is short exact, the first arrow being multiplication by `s` and the second the restriction to
`H`. -/
@[stacks 08A0 "the short exact sequence for an arbitrary coherent module"]
theorem shortExact_hyperplaneUnit_of_nonvanishing (S : Scheme.{u})
    [IsLocallyNoetherian (projectiveSpaceOver n S)]
    (F : (projectiveSpaceOver n S).Modules) (s : (twistOver n S 1).sections)
    [(tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1))).IsQuasicoherent]
    [(tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1)) ⊗
        twistOver n S 1).IsQuasicoherent]
    (hW : ∀ x ∈ Stacks.Divisors.associatedPoints
        (tensorModules (projectiveSpaceOver n S) F (twistOver n S (-1))),
      ∃ W : (projectiveSpaceOver n S).Opens, x ∈ W ∧ ∀ y ∈ W,
        y ∈ Stacks.SheafOfModules.nonvanishingLocus
          (X := (projectiveSpaceOver n S).toRingedSpace) (twistOver n S 1) s) :
    ∃ h : twistSectionMulNegOne n S F s ≫ hyperplaneUnit n S F s = 0,
      (CategoryTheory.ShortComplex.mk (twistSectionMulNegOne n S F s)
        (hyperplaneUnit n S F s) h).ShortExact :=
  have := mono_twistSectionMulNegOne_of_nonvanishing n S F s hW
  shortExact_hyperplaneUnit n S F s (twistSectionMulNegOne_comp_hyperplaneUnit n S F s)
    (isIso_unit_app_cokernel_twistSectionMulNegOne n S F s)

end Sequence

end Stacks.AlgebraicGeometry.ProjectiveSpaceHyperplaneSection

end

