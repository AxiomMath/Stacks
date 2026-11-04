module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorFullyFaithful
public import StacksFrontier.Algebra.DifferentialGraded.Module.WeakGeneratorIsoCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.CompactPerfect
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.QcqsCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentPerfectDual
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullbackBraided
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensorTriangulated
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ProjectionFormulaQuasiCoherent
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.LocallySmall
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.QuasiCompactQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PseudoCoherentPushforwardLocallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BoundedAbove
public import StacksFrontier.CategoryTheory.Triangulated.TensorDiagonalApproximation
public import StacksFrontier.Homology.DerivedCategory.PerfectApproximation

/-!
# The comparison map `Lf^*J ⊗ a(K) ⟶ a(J ⊗ K)` for `K` bounded below

Let `f : X ⟶ Y` be a proper morphism of schemes with `Y` Noetherian, and let `a` be the right
adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. For `K ∈ D^+_QCoh(𝒪_Y)` and `J ∈ D_QCoh(𝒪_Y)` of
Tor amplitude bounded below, the comparison map `Lf^*J ⊗ᴸ a(K) ⟶ a(J ⊗ᴸ K)` of
[Stacks, Tag 0A9S] is an isomorphism.

This is the input of part (3) of [Stacks, Tag 0AA8] at `J = Rg_*𝒪_{Y'}`. The source computes
`R Hom_X(M, -)` of both sides for a perfect generator `M`; here the same computation is made one
compact object `P` of `D_QCoh(𝒪_X)` at a time:

* `P` is perfect ([Stacks, Tag 09M1]) and so dualizable, and morphisms `P ⟶ Lf^*J ⊗ a(K)` and
  `P ⟶ a(J ⊗ K)` are global sections of `J ⊗ W(K)` and `W(J ⊗ K)`, where `W = Rf_*(a(-) ⊗ P^∨)`
  is right adjoint to `- ⊗ Rf_*P` (`CategoryTheory.Adjunction.bijective_comp_comparisonMap_iff`);
* `Rf_*P` is pseudo-coherent ([Stacks, Tag 08E2], [Stacks, Tag 08E8]), so it is approximated by
  perfect objects of `D_QCoh(𝒪_Y)` ([Stacks, Tag 08ES]); against those the comparison is the
  associator, and the error terms are concentrated in degrees that `K` bounded below and the Tor
  amplitude of `J` push out of the way
  (`CategoryTheory.Adjunction.bijective_comp_tensorRightDiagonal_of_approximation`);
* `D_QCoh(𝒪_X)` is compactly generated ([Stacks, Tag 09IS]).

## Main results

* `Stacks.Duality.isIso_comparisonMap_of_isGE` — the comparison map is an isomorphism.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
  MonoidalCategory

universe u

namespace Stacks.Duality

/-! ### Cohomological degrees on `D_QCoh` -/

section Degrees

variable {Z : Scheme.{u}}

/-- `D_QCoh(𝒪_Z)` is concentrated in degrees `≤ p` when the ambient object is. -/
abbrev QcLE (p : ℤ) (E : quasiCoherentDerivedCategory Z) : Prop := E.obj.IsLE p

/-- `D_QCoh(𝒪_Z)` is concentrated in degrees `≥ q` when the ambient object is. -/
abbrev QcGE (q : ℤ) (E : quasiCoherentDerivedCategory Z) : Prop := E.obj.IsGE q

/-- If `E` is concentrated in degrees `≤ p`, then `E[-1]` is concentrated in degrees `≤ p + 1`. -/
theorem qcLE_shift (p : ℤ) (E : quasiCoherentDerivedCategory Z) (h : QcLE p E) :
    QcLE (p + 1) (E⟦(-1 : ℤ)⟧) := by
  have : E.obj.IsLE p := h
  have : DerivedCategory.TStructure.t.IsLE
      (((ObjectProperty.ι _) ⋙ shiftFunctor (DerivedCategory Z.Modules) (-1 : ℤ)).obj E)
      (p + 1) :=
    DerivedCategory.TStructure.t.isLE_shift E.obj p (-1) (p + 1) (by omega)
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (((ObjectProperty.ι _).commShiftIso (-1 : ℤ)).app E).symm (p + 1)

/-- If `E` is concentrated in degrees `≥ q`, then `E[-1]` is concentrated in degrees `≥ q + 1`. -/
theorem qcGE_shift (q : ℤ) (E : quasiCoherentDerivedCategory Z) (h : QcGE q E) :
    QcGE (q + 1) (E⟦(-1 : ℤ)⟧) := by
  have : E.obj.IsGE q := h
  have : DerivedCategory.TStructure.t.IsGE
      (((ObjectProperty.ι _) ⋙ shiftFunctor (DerivedCategory Z.Modules) (-1 : ℤ)).obj E)
      (q + 1) :=
    DerivedCategory.TStructure.t.isGE_shift E.obj q (-1) (q + 1) (by omega)
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (((ObjectProperty.ι _).commShiftIso (-1 : ℤ)).app E).symm (q + 1)

/-- If `E` is concentrated in degrees `≤ p` and `F` in degrees `≤ q`, then `E ⊗ F` is
concentrated in degrees `≤ p + q`. -/
theorem qcLE_tensor (p q : ℤ) (E F : quasiCoherentDerivedCategory Z) (hE : QcLE p E)
    (hF : QcLE q F) : QcLE (p + q) (E ⊗ F) := by
  have h := @Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProduct _ _ _ Z.sheaf _ _ _ _ _ _
    (Stacks.Cohomology.TorAmplitude.derTensor Z.toRingedSpace) E.obj F.obj p q hE hF
  show (((@curriedTensor (DerivedCategory Z.Modules) _
    (Scheme.Modules.canonicalDerivedMonoidal Z)).obj E.obj).obj F.obj).IsLE (p + q)
  rw [curriedTensor_canonicalDerivedMonoidal_eq]
  exact h

/-- The monoidal unit of `D_QCoh(𝒪_Z)` is concentrated in degrees `≤ 0`. -/
theorem qcLE_unit : QcLE 0 (𝟙_ (quasiCoherentDerivedCategory Z)) := by
  rw [tensorUnit_quasiCoherentDerivedCategory]
  have h : ∀ M : Z.Modules, ((DerivedCategory.singleFunctor Z.Modules 0).obj M).IsLE 0 :=
    fun M => inferInstance
  exact h _

/-- Every morphism from an object concentrated in degrees `≤ p` to an object concentrated in
degrees `≥ q` is zero when `p < q`. -/
theorem qc_hom_eq_zero (p q : ℤ) (E F : quasiCoherentDerivedCategory Z) (hpq : p < q)
    (hE : QcLE p E) (hF : QcGE q F) (φ : E ⟶ F) : φ = 0 := by
  refine ObjectProperty.hom_ext _ ?_
  exact DerivedCategory.TStructure.t.zero_of_isLE_of_isGE φ.hom p q hpq hE hF

/-- **`GE` is detected by orthogonality within `D_QCoh`.** -/
theorem qcGE_of_forall (m : ℤ) (E : quasiCoherentDerivedCategory Z)
    (h : ∀ T : quasiCoherentDerivedCategory Z, QcLE (m - 1) T → ∀ φ : T ⟶ E, φ = 0) :
    QcGE m E := by
  obtain ⟨d, rfl⟩ : ∃ d : ℤ, m = d + 1 := ⟨m - 1, by omega⟩
  let T : quasiCoherentDerivedCategory Z :=
    ⟨(DerivedCategory.TStructure.t.truncLE d).obj E.obj,
      fun i => isQuasicoherent_homology_truncLE _ E.property d i⟩
  have hT : QcLE (d + 1 - 1) T := by
    rw [show d + 1 - 1 = d by omega]
    show ((DerivedCategory.TStructure.t.truncLE d).obj E.obj).IsLE d
    infer_instance
  have h0 := h T hT
    (ObjectProperty.homMk ((DerivedCategory.TStructure.t.truncLEι d).app E.obj))
  have hι : (DerivedCategory.TStructure.t.truncLTι (d + 1)).app E.obj = 0 :=
    congrArg InducedCategory.Hom.hom h0
  refine (DerivedCategory.TStructure.t.isGE_iff_orthogonal d (d + 1) rfl _).2 fun W g hW => ?_
  have := hW
  rw [← DerivedCategory.TStructure.t.liftTruncLT_ι g d (d + 1) rfl, hι, comp_zero]

end Degrees

/-! ### Tensoring on `D_QCoh` -/

section Tensor

variable {Z : Scheme.{u}}

/-- `- ⊗ T` on `D_QCoh(𝒪_Z)` is `Stacks.Duality.quasiCoherentDerivedTensor` with `T` in the
second variable. -/
def tensorRightIsoQuasiCoherentDerivedTensor (T : quasiCoherentDerivedCategory Z) :
    (quasiCoherentDerivedTensor Z).flip.obj T ≅ MonoidalCategory.tensorRight T :=
  ((flipFunctor _ _ _).mapIso (quasiCoherentDerivedTensorIsoCurriedTensor Z)).app T

/-- Tensoring on the right with a fixed object of `D_QCoh(𝒪_Z)` preserves zero morphisms. -/
instance preservesZeroMorphisms_tensorRight (T : quasiCoherentDerivedCategory Z) :
    (MonoidalCategory.tensorRight T).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_iso (tensorRightIsoQuasiCoherentDerivedTensor T)

/-- **Tensoring on the left with a fixed object carries distinguished triangles of `D_QCoh(𝒪_Z)`
to distinguished triangles**: tensoring on the right is exact, and the braiding identifies the
two. -/
theorem exists_distTriang_whiskerLeft (T : quasiCoherentDerivedCategory Z)
    (Tr : Triangle (quasiCoherentDerivedCategory Z)) (hTr : Tr ∈ distTriang _) :
    ∃ w : T ⊗ Tr.obj₃ ⟶ (T ⊗ Tr.obj₁)⟦(1 : ℤ)⟧,
      Triangle.mk (T ◁ Tr.mor₁) (T ◁ Tr.mor₂) w ∈ distTriang _ := by
  let e := tensorRightIsoQuasiCoherentDerivedTensor T ≪≫
    (BraidedCategory.tensorLeftIsoTensorRight T).symm
  let : (MonoidalCategory.tensorLeft T).CommShift ℤ := Functor.CommShift.ofIso e ℤ
  have := Functor.CommShift.ofIso_compatibility e ℤ
  have : (MonoidalCategory.tensorLeft T).IsTriangulated := Functor.isTriangulated_of_iso e
  exact ⟨_, (MonoidalCategory.tensorLeft T).map_distinguished Tr hTr⟩

end Tensor

/-! ### Approximation by perfect objects in `D_QCoh` -/

section Approximation

variable {Z : Scheme.{u}} [CompactSpace Z] [QuasiSeparatedSpace Z]

/-- **A pseudo-coherent object of `D_QCoh(𝒪_Z)` is approximated by perfect ones** ([Stacks,
Tag 08ES]): for every `N` there is a distinguished triangle `Q' ⟶ Q ⟶ C ⟶ Q'[1]` in
`D_QCoh(𝒪_Z)` with `Q'` perfect, hence dualizable, and `C` in degrees `≤ -N`. -/
theorem exists_approximation_of_isPseudoCoherent (Q : quasiCoherentDerivedCategory Z)
    (hQ : RingedSpace.IsPseudoCoherent (X := Z.toRingedSpace) Q.obj) (N : ℤ) :
    ∃ (Q' Q'' C : quasiCoherentDerivedCategory Z) (_ : ExactPairing Q' Q'') (u : Q' ⟶ Q)
      (v : Q ⟶ C) (w : C ⟶ Q'⟦(1 : ℤ)⟧), Triangle.mk u v w ∈ distTriang _ ∧ QcLE (-N) C := by
  obtain ⟨r, hr⟩ := (PerfectApproximation.hasApproximationByPerfectComplexes_iff_locallySmall Z).1
    (PerfectApproximation.hasApproximationByPerfectComplexes Z) Set.univ isClosed_univ
    (by rw [Set.compl_univ]; exact IsRetrocompact.empty)
  obtain ⟨K, hK, ⟨e⟩⟩ := hQ
  obtain ⟨P, hP, -, α, hα⟩ := hr Q.obj (-N + 1) Q.property ⟨K, hK (-N + 1 - r), ⟨e⟩⟩
    (fun i x _ hx => absurd (Set.mem_univ x) hx)
  let Q' : quasiCoherentDerivedCategory Z :=
    ⟨P, fun i => isQuasicoherentDerived_of_isPseudoCoherent.{u, u} Z P
      (((Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSpace
        (X := Z.toRingedSpace) P).1 hP).isPseudoCoherent) i⟩
  let u : Q' ⟶ Q := ObjectProperty.homMk α
  obtain ⟨C, v, w, hT⟩ := distinguished_cocone_triangle u
  refine ⟨Q', perfectDual Q' hP, C, exactPairingPerfectDual Q' hP,
    u, v, w, hT, ?_⟩
  have hT' := (ObjectProperty.ι _).map_distinguished _ hT
  have hz := (DerivedCategory.approximatesFrom_iff_isZero_homology_obj₃ _ hT' (-N + 1)).1 hα
  refine (DerivedCategory.isLE_iff _ (-N)).2 fun i hi => hz i (by omega)

end Approximation

/-! ### The comparison map -/

section Comparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y] [IsNoetherian Y] [IsProper f]

/-- **The comparison map `Lf^*J ⊗ᴸ a(K) ⟶ a(J ⊗ᴸ K)` of [Stacks, Tag 0A9S] for `K` bounded
below and `J` of Tor amplitude bounded below.** Let `f : X ⟶ Y` be a proper morphism of
quasi-compact quasi-separated schemes with `Y` Noetherian, let `K ∈ D_QCoh(𝒪_Y)` be in degrees
`≥ b`, and let `J ∈ D_QCoh(𝒪_Y)` be such that `J ⊗ᴸ -` carries objects in degrees `≥ m` to
objects in degrees `≥ m + a`. Then the comparison map is an isomorphism. -/
theorem isIso_comparisonMap_of_isGE (J K : quasiCoherentDerivedCategory Y) (a b : ℤ)
    (hJ : ∀ (m : ℤ) (E : quasiCoherentDerivedCategory Y), QcGE m E → QcGE (m + a) (J ⊗ E))
    (hK : QcGE b K) :
    IsIso ((quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).comparisonMap
      (twistedInverseImageAdjunction f (isQuasicoherent_homology_derivedPushforward_of_qcqs f))
        J K) := by
  let adj := quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
  let adj₂ := twistedInverseImageAdjunction f
    (isQuasicoherent_homology_derivedPushforward_of_qcqs f)
  obtain ⟨ι, E, hEc, hE⟩ := QcqsGeneration.isCompactlyGenerated_quasiCoherentDerivedCategory X
  refine hE.isIso_of_bijective_comp_shiftClosure _ fun P hP => ?_
  obtain ⟨E', n, e, ⟨i⟩⟩ := hP
  have hPc : IsCompactObject.{u} P :=
    isCompactObject_of_iso e (isCompactObject_shift (hEc i) n)
  have hPp := isPerfect_of_isCompactObject P hPc
  let := exactPairingPerfectDual P hPp
  rw [adj.bijective_comp_comparisonMap_iff adj₂ P (perfectDual P hPp) J K]
  refine Adjunction.bijective_comp_tensorRightDiagonal_of_approximation
    (adj.dualTestAdjunction adj₂ P (perfectDual P hPp)) QcLE QcGE qcLE_shift
    qcLE_tensor qcLE_unit qcGE_shift qc_hom_eq_zero qcGE_of_forall exists_distTriang_whiskerLeft
    (exists_approximation_of_isPseudoCoherent _ ?_) J K a b hJ hK
  exact
    Stacks.AlgebraicGeometry.ProperSupportCoherent.isPseudoCoherent_derivedPushforward_of_isProper
      f P.obj
      (((Stacks.Cohomology.PerfectComplexes.isPerfect_iff_ringedSpace
        (X := X.toRingedSpace) P.obj).1 hPp).isPseudoCoherent)

end Comparison

end Stacks.Duality

end
