module

public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.ChartMap
public import StacksFrontier.AlgebraicGeometry.Picard.SymmetricPower.HilbertZariskiSheaf
public import StacksFrontier.RingTheory.Module.LocallyFree.Field
public import Mathlib.AlgebraicGeometry.ResidueField

/-!
# The Hilbert scheme of points of an affine scheme

**Stacks Tag 0B99.** Let `X ⟶ S` be a morphism of affine schemes and `d` a natural number. The
degree-`d` Hilbert functor of `X` over `S` is representable.

The proof is the one of the source: the charts `C_w`, for `w : Fin d → Γ(X)`, are open
subfunctors of the Hilbert functor (the openness is Stacks Tag 00O0, in the form of the
Fitting-ideal description of the locus where a chart applies), they cover it (Nakayama's lemma,
reduced to a field-valued point), and the Hilbert functor is a Zariski sheaf, so Stacks
Tag 01JJ glues the charts.

The tag itself is not registered here; the result is proved here as named theorems.

## Main results

* `Stacks.Hilbert.Chart.isOpenSubfunctor_chartMap`: the charts are open subfunctors.
* `Stacks.Hilbert.Chart.exists_mem_chartLocus`: the charts cover the Hilbert functor.
* `Stacks.Hilbert.isRepresentable_hilbPresheaf_of_isAffine`: representability of the Hilbert
  presheaf of an affine scheme over an affine base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TensorProduct

universe u

namespace Stacks.Hilbert.Chart

variable {S : Scheme.{u}} [IsAffine S] {X : Over S} [IsAffine X.left] {d : ℕ}

attribute [local instance] baseAlgebra

/-- **The charts are open subfunctors of the Hilbert functor.** -/
theorem isOpenSubfunctor_chartMap (w : Fin d → Γ(X.left, ⊤)) :
    IsOpenSubfunctorHom (chartMap w) :=
  isOpenSubfunctor_of_affine (isSheaf_hilbPresheaf X d) _
    (fun T _ => chartMap_injective_of_isAffine w T)
    (fun _ _ p _ _ g hg t' => exists_open_inImage_chartMap w p g hg t')

/-- The global sections of the spectrum of a field form a field. -/
theorem isField_Γ_Spec (K : Type u) [Field K] : IsField Γ(Spec (.of K), ⊤) :=
  MulEquiv.isField (Field.toIsField K)
    ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv)

/-- Over the spectrum of a field, every family lies in some chart. -/
theorem exists_isChart_of_field (K : Type u) [Field K] (s : Spec (.of K) ⟶ S)
    (Z : HilbertFamily X (Over.mk s) d) : ∃ w : Fin d → Γ(X.left, ⊤), IsChart w Z := by
  classical
  let : Field Γ((Over.mk s).left, ⊤) := (isField_Γ_Spec K).toField
  let R' := Γ((Over.mk s).left, ⊤)
  let B := R' ⊗[Γ(S, ⊤)] Γ(X.left, ⊤) ⧸ familyKernel Z
  obtain ⟨hfin, hrank⟩ := Module.IsFiniteLocallyFreeOfRank.finite_and_finrank_eq
    (isFiniteLocallyFreeOfRank_familyKernel Z)
  let v : Γ(X.left, ⊤) → B := fun a => Ideal.Quotient.mk _ ((1 : R') ⊗ₜ a)
  have hv : Submodule.span R' (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul r a =>
      have : Ideal.Quotient.mk (familyKernel Z) (r ⊗ₜ[Γ(S, ⊤)] a) = r • v a := by
        rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul,
          Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.algebraMap_self, RingHom.id_apply, mul_one, one_mul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    | add x y hx hy =>
      rw [map_add]
      exact add_mem hx hy
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent R' (Set.range v)
  let bas : Module.Basis b R' B := Module.Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hv])
  have : Finite b := Module.Finite.finite_basis bas
  let : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = d := by rw [← Module.finrank_eq_card_basis bas, hrank]
  let e : Fin d ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  choose w hw using fun l => hbsub (e l).2
  refine ⟨w, eq_top_iff.mpr ?_⟩
  rw [← hv, ← hbspan]
  refine Submodule.span_le.mpr fun x hx => Submodule.subset_span ?_
  obtain ⟨l, hl⟩ := e.surjective ⟨x, hx⟩
  exact ⟨l, (hw l).trans (congrArg Subtype.val hl)⟩

/-- **The charts cover the Hilbert functor.** -/
theorem exists_mem_chartLocus {T : Scheme.{u}} (p : (hilbPresheaf X d).obj (op T)) (t : T) :
    ∃ (w : Fin d → Γ(X.left, ⊤)) (O : T.Opens), t ∈ O ∧
      InImage (chartMap w) ((hilbPresheaf X d).map O.ι.op p) := by
  obtain ⟨s, Z⟩ := p
  let g := T.fromSpecResidueField t
  obtain ⟨w, hw⟩ := exists_isChart_of_field (X := X) (T.residueField t) (g ≫ s)
    (baseChange X (Over.homMk g rfl : Over.mk (g ≫ s) ⟶ Over.mk s) Z)
  refine ⟨w, ?_⟩
  obtain ⟨V, hV⟩ := (isOpenSubfunctor_chartMap w).locus T ⟨s, Z⟩
  refine ⟨V, ?_, (hV _ V.ι).mpr (by rw [Scheme.Opens.range_ι])⟩
  obtain ⟨pt⟩ : Nonempty (Spec (.of (T.residueField t))) := inferInstance
  rw [← show g pt = t from Scheme.fromSpecResidueField_apply _ _]
  exact (hV _ g).mp ((inImage_chartMap_iff w (g ≫ s) _).mpr hw) ⟨pt, rfl⟩

end Stacks.Hilbert.Chart

namespace Stacks.Hilbert

variable {S : Scheme.{u}} [IsAffine S] (X : Over S) [IsAffine X.left] (d : ℕ)

/-- **Stacks Tag 0B99, for the Hilbert presheaf.** The degree-`d` Hilbert functor of points of
an affine scheme over an affine base, read on all schemes, is representable. -/
theorem isRepresentable_hilbPresheaf_of_isAffine : (hilbPresheaf X d).IsRepresentable :=
  isRepresentable_of_isOpenSubfunctor (isSheaf_hilbPresheaf X d)
    (C := fun w : Fin d → Γ(X.left, ⊤) => Chart.chartScheme w) Chart.chartMap
    Chart.isOpenSubfunctor_chartMap
    (fun _ p t => Chart.exists_mem_chartLocus p t)

end Stacks.Hilbert

end
