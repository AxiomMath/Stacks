module

public import StacksFrontier.AlgebraicGeometry.Blowup.ProjBaseChangeGlobal
public import StacksFrontier.AlgebraicGeometry.Blowup.ProjRegrading
public import StacksFrontier.RingTheory.GradedAlgebra.NoetherianModel
public import StacksFrontier.RingTheory.HomogeneousLocalization.DegreeZero
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpectrum.NoetherianModelClauses
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.RingHom.FinitePresentation

/-!
# Finite presentation of the structure morphism of a homogeneous spectrum

Let `A` be a commutative ring graded by `R`-submodules `𝒜 : ℕ → Submodule R A` and finitely
presented as an `R`-algebra. This file proves that the structure morphism `Proj 𝒜 ⟶ Spec R` is
locally of finite presentation; this is the affine case of the first assertion of Stacks tag
0D4D.

The proof is the limit argument of the source. A finitely presented graded algebra is a base
change of a *Noetherian graded model*: a graded algebra `𝒜₀` over a subring `R₀ ⊆ R` of finite
type over `ℤ`, with `A ≅ R ⊗_{R₀} A₀` (`Stacks.GradedModel.exists_noetherianGradedModel`). Over
the Noetherian base `R₀` the structure morphism of `Proj 𝒜₀` is locally of finite type and its
target is locally Noetherian, hence it is locally of finite presentation by tag 01TX; and `Proj`
commutes with base change (`Stacks.ProjBaseChange.isPullback_map_Spec`), so the property
descends along the cartesian square to `Proj 𝒜 ⟶ Spec R`.

## Main results

* `Stacks.GradedTransport.symm_mem`: the inverse of a ring isomorphism between two internally
  graded rings which preserves the graded pieces preserves them as well. This is what upgrades
  the *algebra* isomorphism `R ⊗_{R₀} A₀ ≅ A` supplied by the Noetherian model to an isomorphism
  of *graded* rings, which is what the base-change square for `Proj` asks for.
* `Stacks.AlgebraicGeometry.Proj.locallyOfFinitePresentation_projToSpec`: the structure morphism
  `Proj 𝒜 ⟶ Spec R` of a finitely presented graded `R`-algebra is locally of finite
  presentation. This is the affine case of the first assertion of Stacks tag 0D4D.

## Implementation notes

The Noetherian graded model supplies only the underlying algebra isomorphism
`e : R ⊗_{R₀} A₀ ≅ A` together with a degree-preserving homomorphism `f : A₀ → A` satisfying
`e (r ⊗ₜ x) = r • f x`; neither a graded inverse of `e` nor the irrelevant-ideal hypothesis of
`AlgebraicGeometry.Proj.map` comes with it. That `e` carries the base-changed grading into `𝒜`
follows by span induction from `Submodule.baseChange_eq_span`, `Stacks.GradedTransport.symm_mem`
then makes the inverse degree preserving as well, and the irrelevant-ideal hypotheses follow for
both directions from `Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id`.

The two structure morphisms over `Spec R` are compared through the naturality square
`AlgebraicGeometry.Proj.map_toSpecZero` of `AlgebraicGeometry.Proj.toSpecZero`, whose horizontal
edge is `Spec` of the degree-zero part of the graded isomorphism; that edge composes with the
structure map of the base-changed degree-zero part to the structure map of `𝒜 0` because the
isomorphism is one of `R`-algebras.

`AlgebraicGeometry.LocallyOfFinitePresentation` carries no `CategoryTheory.MorphismProperty`
`RespectsIso` instance, so one is produced from `AlgebraicGeometry.affineLocally_respectsIso`
through `AlgebraicGeometry.HasRingHomProperty.eq_affineLocally`.

No `@[stacks 0D4D]` attribute is attached here: the covering declaration for that tag is
`Stacks.AlgebraicGeometry.RelativeProjFinitePresentation.finitePresentation_toBase`, which is
the statement for a relative homogeneous spectrum over an arbitrary base scheme.

## References

* [Stacks Project, Tag 0D4D](https://stacks.math.columbia.edu/tag/0D4D)
* [Stacks Project, Tag 01TX](https://stacks.math.columbia.edu/tag/01TX)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TensorProduct CommRingCat

universe u

namespace Stacks.GradedTransport

variable {ι A B σ τ : Type*} [DecidableEq ι] [AddMonoid ι] [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubmonoidClass σ A] [SetLike τ B] [AddSubmonoidClass τ B]
  (𝒜 : ι → σ) (ℬ : ι → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **The inverse of a grading-preserving ring isomorphism preserves the grading.** If a ring
isomorphism `φ` between two internally graded rings carries each graded piece of the source into
the corresponding piece of the target, then so does its inverse: for `b` homogeneous of degree
`i`, applying `φ` to the homogeneous decomposition of `φ⁻¹ b` and reading off the degree-`i`
component shows `b = φ ((φ⁻¹ b)ᵢ)`, so `φ⁻¹ b` is its own degree-`i` component. -/
public theorem symm_mem (φ : A ≃+* B) (hφ : ∀ (i : ι) (x : A), x ∈ 𝒜 i → φ x ∈ ℬ i)
    {i : ι} {b : B} (hb : b ∈ ℬ i) : φ.symm b ∈ 𝒜 i := by
  classical
  have hb' : φ (φ.symm b) = b := φ.apply_symm_apply b
  set a : A := φ.symm b
  have key : GradedRing.proj ℬ i b = φ ((DirectSum.decompose 𝒜 a i : A)) := by
    conv_lhs => rw [← hb', ← DirectSum.sum_support_decompose 𝒜 a]
    simp only [map_sum]
    refine (Finset.sum_eq_single i (fun j _ hj => ?_) (fun hi => ?_)).trans ?_
    · rw [GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_ne ℬ (hφ j _ (DirectSum.decompose 𝒜 a j).2) hj
    · rw [DFinsupp.notMem_support_iff.mp hi]
      simp
    · rw [GradedRing.proj_apply]
      exact DirectSum.decompose_of_mem_same ℬ (hφ i _ (DirectSum.decompose 𝒜 a i).2)
  rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same ℬ hb] at key
  have heq : (DirectSum.decompose 𝒜 a i : A) = a := φ.injective (key.symm.trans hb'.symm)
  exact heq ▸ (DirectSum.decompose 𝒜 a i).2

end Stacks.GradedTransport

namespace Stacks.AlgebraicGeometry.Proj

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]

/-- **Stacks 0D4D over an affine base.** The structure morphism `Proj 𝒜 ⟶ Spec R` of a graded
algebra which is finitely presented over `R` is locally of finite presentation. Over a Noetherian
graded model `𝒜₀` of `𝒜`, with base a finite type `ℤ`-subalgebra `R₀` of `R`, the statement is
tag 01TX — locally of finite type over a locally Noetherian target — and the general case follows
because `Proj` commutes with base change. -/
public theorem locallyOfFinitePresentation_projToSpec [Algebra.FinitePresentation R A] :
    LocallyOfFinitePresentation (AlgebraicGeometry.Proj.toSpecZero 𝒜 ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0)))) := by
  obtain ⟨R₀, -, hR₀noeth, A₀, hring, halg, 𝒜₀, hgraded, hft₀, hnoeth₀, f, e, -, hetmul⟩ :=
    Stacks.GradedModel.exists_noetherianGradedModel 𝒜
  let _ := hring
  let _ := halg
  let _ := hgraded
  let _ := hft₀
  let _ := hnoeth₀
  let _ := hR₀noeth
  let _ : Algebra.FiniteType R₀ (𝒜₀ 0) := gradeZero_finiteType 𝒜₀
  let _ : IsLocallyNoetherian (Spec (CommRingCat.of R₀)) := inferInstance
  have hmodel : LocallyOfFinitePresentation (AlgebraicGeometry.Proj.toSpecZero 𝒜₀ ≫
      Spec.map (CommRingCat.ofHom (algebraMap R₀ (𝒜₀ 0)))) := by
    have := locallyOfFiniteType_projToSpec 𝒜₀
    infer_instance
  -- the base-changed grading and the graded isomorphism carrying it onto `𝒜`
  have hmem : ∀ (i : ℕ) (x : TensorProduct R₀ R A₀),
      x ∈ Stacks.ProjBaseChange.grading 𝒜₀ R i → e x ∈ 𝒜 i := by
    intro i x hx
    rw [Stacks.ProjBaseChange.grading, Submodule.baseChange_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨z, hz, rfl⟩ := hy
        have : e ((1 : R) ⊗ₜ[R₀] z) = f z := by rw [hetmul, one_smul]
        exact this ▸ f.map_mem hz
    | zero => simp
    | add y z _ _ ihy ihz => simpa using add_mem ihy ihz
    | smul r y _ ih => simpa using Submodule.smul_mem _ r ih
  let E : Stacks.ProjBaseChange.grading 𝒜₀ R →+*ᵍ 𝒜 :=
    { __ := (e : TensorProduct R₀ R A₀ →+* A)
      map_mem := fun {i x} hx => hmem i x hx }
  let E' : 𝒜 →+*ᵍ Stacks.ProjBaseChange.grading 𝒜₀ R :=
    { __ := (e.symm : A →+* TensorProduct R₀ R A₀)
      map_mem := fun {i x} hx =>
        Stacks.GradedTransport.symm_mem _ _ (e : TensorProduct R₀ R A₀ ≃+* A) hmem hx }
  have hEE' : E'.comp E = GradedRingHom.id (Stacks.ProjBaseChange.grading 𝒜₀ R) :=
    GradedRingHom.ext e.symm_apply_apply
  have hE'E : E.comp E' = GradedRingHom.id 𝒜 := GradedRingHom.ext e.apply_symm_apply
  have hE := Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id hE'E
  have hE' := Stacks.GradedRegrading.irrelevant_le_map_of_comp_eq_id hEE'
  have hiso : IsIso (AlgebraicGeometry.Proj.map E hE) :=
    AlgebraicGeometry.Proj.isIso_map hE hE' hEE' hE'E
  have hbc : LocallyOfFinitePresentation
      (AlgebraicGeometry.Proj.toSpecZero (Stacks.ProjBaseChange.grading 𝒜₀ R) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R (Stacks.ProjBaseChange.grading 𝒜₀ R 0)))) :=
    MorphismProperty.of_isPullback (Stacks.ProjBaseChange.isPullback_map_Spec 𝒜₀ R) hmodel
  have hzero : E.gradedZeroRingHom.comp
      (algebraMap R (Stacks.ProjBaseChange.grading 𝒜₀ R 0)) = algebraMap R (𝒜 0) :=
    RingHom.ext fun r => Subtype.ext (e.commutes r)
  have hcomp : AlgebraicGeometry.Proj.map E hE ≫
      (AlgebraicGeometry.Proj.toSpecZero (Stacks.ProjBaseChange.grading 𝒜₀ R) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R (Stacks.ProjBaseChange.grading 𝒜₀ R 0)))) =
      AlgebraicGeometry.Proj.toSpecZero 𝒜 ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0))) := by
    rw [← Category.assoc, AlgebraicGeometry.Proj.map_toSpecZero E hE, Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, hzero]
  have hrio : MorphismProperty.RespectsIso @LocallyOfFinitePresentation := by
    rw [HasRingHomProperty.eq_affineLocally @LocallyOfFinitePresentation]
    exact affineLocally_respectsIso _ RingHom.finitePresentation_respectsIso
  rw [← hcomp]
  exact (MorphismProperty.cancel_left_of_respectsIso @LocallyOfFinitePresentation _ _).2 hbc

end Stacks.AlgebraicGeometry.Proj

end
