module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.AlgebraicGeometry.FormalSpace.StageBaseChangeColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautStageBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite
public import StacksFrontier.CategoryTheory.Limits.RelativeProductOfColimits
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.Adic
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.QuotientLimit
import all StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful

/-!
# Fibre products of formal spectra and the completed tensor product

Let `S` be a scheme contained in a big fppf site `B` and let `A₀ → A₁`, `A₀ → A₂` be continuous
homomorphisms of weakly admissible topological rings over `S`. The completed tensor product
`T = A₁ ⊗̂_{A₀} A₂` is made a topological ring over `S`, with continuous homomorphisms `A₁ → T` and
`A₂ → T` over `S`; its stages are compared with the tensor products `A₁/I ⊗_{A₀} A₂/J` of the
stages of the factors, and `Spf T` is identified with `Spf A₁ ×_{Spf A₀} Spf A₂`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.completedTensorStageRingHom`: the projection
  `T → A₁/I ⊗_{A₀} A₂/J` for weak ideals of definition `I ⊆ A₁` and `J ⊆ A₂`.
* `AlgebraicGeometry.FormalSpace.completedTensorLeft`,
  `AlgebraicGeometry.FormalSpace.completedTensorRight`: the canonical maps `A₁ → T`, `A₂ → T`.
* `AlgebraicGeometry.FormalSpace.completedTensorQuotientSystem`: the structure of a ring over `S`
  on `T`, a quotient stage `Spec (T/L)` lying over `S` through a stage of `A₁`.
* `AlgebraicGeometry.FormalSpace.completedTensorLeftHom`,
  `AlgebraicGeometry.FormalSpace.completedTensorRightHom`: the two maps as continuous
  homomorphisms over `S`.

## Main results

* `AlgebraicGeometry.FormalSpace.completedTensorStageRingHom_coe`: the projection on the dense
  image of `A₁ ⊗_{A₀} A₂`.
* `AlgebraicGeometry.FormalSpace.surjective_completedTensorStageRingHom` and
  `AlgebraicGeometry.FormalSpace.ker_completedTensorStageRingHom_le`: the projection is
  surjective, and its kernel lies in every open ideal containing the images of `I` and `J`.
* `AlgebraicGeometry.FormalSpace.isPullback_completedTensorStage_formalSpectrum`: the fibre
  product over `Spf A₀` of the stages `Spec (A₁/I)` and `Spec (A₂/J)` is
  `Spec (A₁/I ⊗_{A₀} A₂/J)`.
* `AlgebraicGeometry.FormalSpace.isPullback_formalSpectrumMap_completedTensor`: `T` is weakly
  admissible and `Spf T` is the fibre product `Spf A₁ ×_{Spf A₀} Spf A₂`.

## References

* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
* [Stacks Project, Tag 0AMU](https://stacks.math.columbia.edu/tag/0AMU)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.FormalSpace

universe u

/-- In a weakly admissible linearly topologized ring the weak ideals of definition form a
fundamental system of neighbourhoods of zero. -/
theorem hasBasis_nhds_zero_isWeakIdealOfDefinition {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] (hA : TopologicalRing.IsWeaklyAdmissible A) :
    (nhds (0 : A)).HasBasis
      (fun _ : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } => True)
      (fun I => (I.1 : Set A)) := by
  obtain ⟨I₀, hI₀⟩ := hA.1
  refine IsLinearTopology.hasBasis_open_ideal.to_hasBasis
    (fun J hJ ↦ ⟨⟨I₀ ⊓ J, ⟨?_, fun x hx ↦ hI₀.2 x (Ideal.mem_inf.mp hx).1⟩⟩, trivial,
      fun x hx ↦ (Ideal.mem_inf.mp hx).2⟩) (fun I _ ↦ ⟨I.1, I.2.1, subset_rfl⟩)
  change IsOpen ((I₀ : Set A) ∩ J)
  exact hI₀.1.inter hJ

/-- `Spec` reverses the order of a commutative square of ring homomorphisms. -/
private theorem spec_map_comp_eq {R₁ R₂ R₃ R₄ : Type u} [CommRing R₁] [CommRing R₂]
    [CommRing R₃] [CommRing R₄] (f : R₁ →+* R₂) (g : R₂ →+* R₄) (f' : R₁ →+* R₃)
    (g' : R₃ →+* R₄) (h : g.comp f = g'.comp f') :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom g') ≫ Spec.map (CommRingCat.ofHom f') := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, h]

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {A₀ A₁ A₂ : Type u}
  [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀]
  [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁] [IsLinearTopology A₁ A₁]
  [CommRing A₂] [TopologicalSpace A₂] [IsTopologicalRing A₂] [IsLinearTopology A₂ A₂]
  [Algebra A₀ A₁] [Algebra A₀ A₂]

section Ring

variable (A₀ A₁ A₂)

/-- The canonical map `A₁ → A₁ ⊗̂_{A₀} A₂`. -/
def completedTensorLeft :
    A₁ →+* TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂) :=
  letI := TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A₂)
  (UniformSpace.Completion.coeRingHom :
      (A₁ ⊗[A₀] A₂) →+* TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)).comp
    (Algebra.TensorProduct.includeLeft : A₁ →ₐ[A₀] A₁ ⊗[A₀] A₂).toRingHom

/-- The canonical map `A₂ → A₁ ⊗̂_{A₀} A₂`. -/
def completedTensorRight :
    A₂ →+* TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂) :=
  letI := TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A₂)
  (UniformSpace.Completion.coeRingHom :
      (A₁ ⊗[A₀] A₂) →+* TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)).comp
    (Algebra.TensorProduct.includeRight : A₂ →ₐ[A₀] A₁ ⊗[A₀] A₂).toRingHom

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The canonical map `A₁ → A₁ ⊗̂_{A₀} A₂` is continuous. -/
theorem continuous_completedTensorLeft : Continuous (completedTensorLeft A₀ A₁ A₂) := by
  let := TopologicalRing.tensorProductTopology (R := A₀) (M := A₁) (N := A₂)
  let := TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A₂)
  change Continuous fun a : A₁ ↦
    ((a ⊗ₜ[A₀] (1 : A₂) : A₁ ⊗[A₀] A₂) :
      TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂))
  exact (UniformSpace.Completion.continuous_coe (A₁ ⊗[A₀] A₂)).comp
    (TopologicalRing.continuous_tmul_const (R := A₀) (M := A₁) (N := A₂) (1 : A₂))

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The canonical map `A₂ → A₁ ⊗̂_{A₀} A₂` is continuous. -/
theorem continuous_completedTensorRight : Continuous (completedTensorRight A₀ A₁ A₂) := by
  let := TopologicalRing.tensorProductTopology (R := A₀) (M := A₁) (N := A₂)
  let := TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A₂)
  change Continuous fun c : A₂ ↦
    ((((1 : A₁) ⊗ₜ[A₀] c) : A₁ ⊗[A₀] A₂) :
      TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂))
  exact (UniformSpace.Completion.continuous_coe (A₁ ⊗[A₀] A₂)).comp
    (TopologicalRing.continuous_const_tmul (R := A₀) (M := A₁) (N := A₂) (1 : A₁))

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The two canonical maps into `A₁ ⊗̂_{A₀} A₂` agree on `A₀`. -/
theorem completedTensorLeft_comp_algebraMap :
    (completedTensorLeft A₀ A₁ A₂).comp (algebraMap A₀ A₁) =
      (completedTensorRight A₀ A₁ A₂).comp (algebraMap A₀ A₂) := by
  refine RingHom.ext fun c ↦ ?_
  simp only [completedTensorLeft, completedTensorRight, RingHom.coe_comp, Function.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]

variable {A₁ A₂}

/-- The projection of `A₁ ⊗̂_{A₀} A₂` onto `A₁/I ⊗_{A₀} A₂/J`, for weak ideals of definition
`I ⊆ A₁` and `J ⊆ A₂`. -/
def completedTensorStageRingHom (hA₁ : TopologicalRing.IsWeaklyAdmissible A₁)
    (hA₂ : TopologicalRing.IsWeaklyAdmissible A₂)
    (I : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I })
    (J : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J }) :
    TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂) →+*
      (A₁ ⧸ I.1) ⊗[A₀] (A₂ ⧸ J.1) :=
  TopologicalRing.projectionRingHom (B := A₀) (A := A₁) (C := A₂)
    (ι := { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I })
    (κ := { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J })
    (fun I ↦ I.1) (fun J ↦ J.1)
    (hasBasis_nhds_zero_isWeakIdealOfDefinition hA₁)
    (hasBasis_nhds_zero_isWeakIdealOfDefinition hA₂) I J

variable (hA₁ : TopologicalRing.IsWeaklyAdmissible A₁)
  (hA₂ : TopologicalRing.IsWeaklyAdmissible A₂)
  (I : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I })
  (J : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J })

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- On the dense image of `A₁ ⊗_{A₀} A₂` the projection is the tensor product of the two
quotient maps. -/
theorem completedTensorStageRingHom_coe (z : A₁ ⊗[A₀] A₂) :
    letI := TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A₂)
    completedTensorStageRingHom A₀ hA₁ hA₂ I J
        (z : TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) =
      Algebra.TensorProduct.map (Ideal.Quotient.mkₐ A₀ I.1) (Ideal.Quotient.mkₐ A₀ J.1) z :=
  (Classical.choose_spec (TopologicalRing.exists_completedTensorProductRingEquivQuotientLimit
    (B := A₀) (fun I : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I } ↦ I.1)
    (fun J : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J } ↦ J.1)
    (hasBasis_nhds_zero_isWeakIdealOfDefinition hA₁)
    (hasBasis_nhds_zero_isWeakIdealOfDefinition hA₂))).2.2 z I J

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The projection onto `A₁/I ⊗_{A₀} A₂/J` sends the image of `a ∈ A₁` to `ā ⊗ 1`. -/
theorem completedTensorStageRingHom_left (a : A₁) :
    completedTensorStageRingHom A₀ hA₁ hA₂ I J (completedTensorLeft A₀ A₁ A₂ a) =
      Ideal.Quotient.mk I.1 a ⊗ₜ[A₀] (1 : A₂ ⧸ J.1) := by
  have h := completedTensorStageRingHom_coe A₀ hA₁ hA₂ I J (a ⊗ₜ[A₀] (1 : A₂))
  simp only [Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk, map_one] at h
  exact h

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The projection onto `A₁/I ⊗_{A₀} A₂/J` sends the image of `c ∈ A₂` to `1 ⊗ c̄`. -/
theorem completedTensorStageRingHom_right (c : A₂) :
    completedTensorStageRingHom A₀ hA₁ hA₂ I J (completedTensorRight A₀ A₁ A₂ c) =
      (1 : A₁ ⧸ I.1) ⊗ₜ[A₀] Ideal.Quotient.mk J.1 c := by
  have h := completedTensorStageRingHom_coe A₀ hA₁ hA₂ I J ((1 : A₁) ⊗ₜ[A₀] c)
  simp only [Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk, map_one] at h
  exact h

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The kernel of the projection onto `A₁/I ⊗_{A₀} A₂/J` is open. -/
theorem isOpen_ker_completedTensorStageRingHom :
    IsOpen (RingHom.ker (completedTensorStageRingHom A₀ hA₁ hA₂ I J) :
      Set (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂))) :=
  TopologicalRing.isOpen_projectionKernel (B := A₀) _ _ _ _ I J

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The projection onto `A₁/I ⊗_{A₀} A₂/J` is surjective. -/
theorem surjective_completedTensorStageRingHom :
    Function.Surjective (completedTensorStageRingHom A₀ hA₁ hA₂ I J) := by
  let := TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A₂)
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul p q =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective p
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective q
    refine ⟨((a ⊗ₜ[A₀] c : A₁ ⊗[A₀] A₂) :
      TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)), ?_⟩
    rw [completedTensorStageRingHom_coe]
    rfl
  | add x y hx hy =>
    obtain ⟨s, rfl⟩ := hx
    obtain ⟨t, rfl⟩ := hy
    exact ⟨s + t, map_add _ _ _⟩

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The kernel of the projection onto `A₁/I ⊗_{A₀} A₂/J` lies in every open ideal of the
completed tensor product containing the images of `I` and of `J`. -/
theorem ker_completedTensorStageRingHom_le
    (L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)))
    (hL : IsOpen (L : Set (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁)
      (N := A₂))))
    (hIL : ∀ a ∈ I.1, completedTensorLeft A₀ A₁ A₂ a ∈ L)
    (hJL : ∀ c ∈ J.1, completedTensorRight A₀ A₁ A₂ c ∈ L) :
    RingHom.ker (completedTensorStageRingHom A₀ hA₁ hA₂ I J) ≤ L := by
  let := TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A₂)
  intro x hx
  have hx' : x ∈ (TopologicalRing.projectionKernel (B := A₀)
      (fun I : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I } ↦ I.1)
      (fun J : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J } ↦ J.1)
      (hasBasis_nhds_zero_isWeakIdealOfDefinition hA₁)
      (hasBasis_nhds_zero_isWeakIdealOfDefinition hA₂) I J : Set _) := hx
  rw [TopologicalRing.projectionKernel_eq_closure, Ideal.coe_closure] at hx'
  have hle : I.1.map (completedTensorLeft A₀ A₁ A₂) + J.1.map (completedTensorRight A₀ A₁ A₂) ≤
      L := sup_le (Ideal.map_le_iff_le_comap.mpr hIL) (Ideal.map_le_iff_le_comap.mpr hJL)
  exact closure_minimal hle (L.toAddSubgroup.isClosed_of_isOpen hL) hx'

end Ring

/-- A weak ideal of definition of a weakly admissible ring lies inside the preimages of two given
open ideals under two continuous homomorphisms. -/
theorem exists_isWeakIdealOfDefinition_le_comap_of_isOpen
    (hA₀ : TopologicalRing.IsWeaklyAdmissible A₀)
    {C₁ C₂ : Type u} [CommRing C₁] [TopologicalSpace C₁] [CommRing C₂] [TopologicalSpace C₂]
    {f₁ : A₀ →+* C₁} {f₂ : A₀ →+* C₂} (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    {L₁ : Ideal C₁} {L₂ : Ideal C₂} (h₁ : IsOpen (L₁ : Set C₁)) (h₂ : IsOpen (L₂ : Set C₂)) :
    ∃ K : { K : Ideal A₀ // TopologicalRing.IsWeakIdealOfDefinition K },
      K.1 ≤ L₁.comap f₁ ∧ K.1 ≤ L₂.comap f₂ := by
  obtain ⟨K₀, hK₀⟩ := hA₀.1
  refine ⟨⟨K₀ ⊓ L₁.comap f₁ ⊓ L₂.comap f₂, ⟨?_, fun x hx ↦
    hK₀.2 x (Ideal.mem_inf.mp (Ideal.mem_inf.mp hx).1).1⟩⟩,
    inf_le_left.trans inf_le_right, inf_le_right⟩
  change IsOpen (((K₀ : Set A₀) ∩ f₁ ⁻¹' L₁) ∩ f₂ ⁻¹' L₂)
  exact (hK₀.1.inter (h₁.preimage hf₁)).inter (h₂.preimage hf₂)

section QuotientSystem

variable (A₀) (hA₁ : TopologicalRing.IsWeaklyAdmissible A₁)
  (hA₂ : TopologicalRing.IsWeaklyAdmissible A₂)

/-- The weak ideal of definition `I₀ ∩ ψ₁⁻¹(L)` of `A₁` attached to a weak ideal of definition
`L` of `A₁ ⊗̂_{A₀} A₂`, for a fixed weak ideal of definition `I₀` of `A₁` and the canonical map
`ψ₁ : A₁ → A₁ ⊗̂_{A₀} A₂`. -/
def completedTensorLeftIdeal
    (L : { L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) //
      TopologicalRing.IsWeakIdealOfDefinition L }) :
    { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I } :=
  ⟨hA₁.1.choose ⊓ L.1.comap (completedTensorLeft A₀ A₁ A₂),
    ⟨by
      change IsOpen ((hA₁.1.choose : Set A₁) ∩ (completedTensorLeft A₀ A₁ A₂) ⁻¹' L.1)
      exact hA₁.1.choose_spec.1.inter (L.2.1.preimage (continuous_completedTensorLeft A₀ A₁ A₂)),
      fun x hx ↦ hA₁.1.choose_spec.2 x (Ideal.mem_inf.mp hx).1⟩⟩

/-- The weak ideal of definition `J₀ ∩ ψ₂⁻¹(L)` of `A₂` attached to a weak ideal of definition
`L` of `A₁ ⊗̂_{A₀} A₂`. -/
def completedTensorRightIdeal
    (L : { L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) //
      TopologicalRing.IsWeakIdealOfDefinition L }) :
    { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J } :=
  ⟨hA₂.1.choose ⊓ L.1.comap (completedTensorRight A₀ A₁ A₂),
    ⟨by
      change IsOpen ((hA₂.1.choose : Set A₂) ∩ (completedTensorRight A₀ A₁ A₂) ⁻¹' L.1)
      exact hA₂.1.choose_spec.1.inter
        (L.2.1.preimage (continuous_completedTensorRight A₀ A₁ A₂)),
      fun x hx ↦ hA₂.1.choose_spec.2 x (Ideal.mem_inf.mp hx).1⟩⟩

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The ideal `completedTensorLeftIdeal A₀ hA₁ L` lies in the preimage of `L` under
`A₁ → A₁ ⊗̂_{A₀} A₂`. -/
theorem completedTensorLeftIdeal_le
    (L : { L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) //
      TopologicalRing.IsWeakIdealOfDefinition L }) :
    (completedTensorLeftIdeal A₀ hA₁ L).1 ≤ L.1.comap (completedTensorLeft A₀ A₁ A₂) :=
  inf_le_right

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The ideal `completedTensorRightIdeal A₀ hA₂ L` lies in the preimage of `L` under
`A₂ → A₁ ⊗̂_{A₀} A₂`. -/
theorem completedTensorRightIdeal_le
    (L : { L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) //
      TopologicalRing.IsWeakIdealOfDefinition L }) :
    (completedTensorRightIdeal A₀ hA₂ L).1 ≤ L.1.comap (completedTensorRight A₀ A₁ A₂) :=
  inf_le_right

variable (D₁ : QuotientSystem B S hS A₁) (D₂ : QuotientSystem B S hS A₂)

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
include hA₁ hA₂ D₁ D₂ in
/-- Every quotient stage of `A₁ ⊗̂_{A₀} A₂` by a weak ideal of definition lies in the site. -/
theorem contains_spec_completedTensor_quotient
    (L : { L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) //
      TopologicalRing.IsWeakIdealOfDefinition L }) :
    B.Contains (Spec (.of (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁)
      (N := A₂) ⧸ L.1))) := by
  let I := completedTensorLeftIdeal A₀ hA₁ L
  let J := completedTensorRightIdeal A₀ hA₂ L
  let π := completedTensorStageRingHom A₀ hA₁ hA₂ I J
  have hker : RingHom.ker π ≤ L.1 :=
    ker_completedTensorStageRingHom_le A₀ hA₁ hA₂ I J L.1 L.2.1
      (fun a ha ↦ (Ideal.mem_inf.mp ha).2) (fun c hc ↦ (Ideal.mem_inf.mp hc).2)
  have hsurj := surjective_completedTensorStageRingHom A₀ hA₁ hA₂ I J
  refine BigFppfSite.contains_spec_of_mk_lt_cutoff B (lt_of_le_of_lt ?_
    (BigFppfSite.mk_lt_cutoff_of_contains_spec B
      (BigFppfSite.contains_spec_tensorProduct B (R := A₀) (D₁.inSite I) (D₂.inSite J))))
  refine Cardinal.mk_le_of_surjective (f := fun x ↦ Ideal.Quotient.mk L.1 (hsurj x).choose) ?_
  intro y
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨π t, Ideal.Quotient.eq.mpr (hker ?_)⟩
  rw [RingHom.mem_ker, map_sub, (hsurj (π t)).choose_spec, sub_self]

/-- The structure of a ring over `S` on `T = A₁ ⊗̂_{A₀} A₂`: the quotient stage `Spec (T/L)` lies
over `S` through the stage `Spec (A₁/I)` of `A₁` with `I = completedTensorLeftIdeal A₀ hA₁ L`. -/
def completedTensorQuotientSystem :
    QuotientSystem B S hS (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂))
    where
  inSite L := contains_spec_completedTensor_quotient A₀ hA₁ hA₂ D₁ D₂ L
  overS L := Spec.map (CommRingCat.ofHom (Ideal.quotientMap L.1 (completedTensorLeft A₀ A₁ A₂)
    (completedTensorLeftIdeal_le A₀ hA₁ L))) ≫ D₁.overS (completedTensorLeftIdeal A₀ hA₁ L)
  compatible L L' h := by
    have hI : (completedTensorLeftIdeal A₀ hA₁ L).1 ≤ (completedTensorLeftIdeal A₀ hA₁ L').1 :=
      inf_le_inf_left _ (Ideal.comap_mono h)
    rw [← D₁.compatible _ _ hI, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 3
    exact Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ rfl)

/-- The canonical map `A₁ → A₁ ⊗̂_{A₀} A₂` as a continuous homomorphism over `S`. -/
def completedTensorLeftHom : ContinuousHom D₁ (completedTensorQuotientSystem A₀ hA₁ hA₂ D₁ D₂) where
  toRingHom := completedTensorLeft A₀ A₁ A₂
  continuous := continuous_completedTensorLeft A₀ A₁ A₂
  overS J K h := by
    let M : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I } :=
      ⟨J.1 ⊓ (completedTensorLeftIdeal A₀ hA₁ K).1,
        ⟨J.2.1.inter (completedTensorLeftIdeal A₀ hA₁ K).2.1,
        fun x hx ↦ J.2.2 x (Ideal.mem_inf.mp hx).1⟩⟩
    change _ = Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 (completedTensorLeft A₀ A₁ A₂)
      (completedTensorLeftIdeal_le A₀ hA₁ K))) ≫ D₁.overS (completedTensorLeftIdeal A₀ hA₁ K)
    rw [← D₁.compatible M J inf_le_left, ← D₁.compatible M _ inf_le_right, ← Category.assoc,
      ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
    exact Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ rfl)

variable {D₀ : QuotientSystem B S hS A₀} (hA₀ : TopologicalRing.IsWeaklyAdmissible A₀)
  (φ₁ : ContinuousHom D₀ D₁) (φ₂ : ContinuousHom D₀ D₂)
  (hφ₁ : φ₁.toRingHom = algebraMap A₀ A₁) (hφ₂ : φ₂.toRingHom = algebraMap A₀ A₂)

/-- The canonical map `A₂ → A₁ ⊗̂_{A₀} A₂` as a continuous homomorphism over `S`. -/
def completedTensorRightHom :
    ContinuousHom D₂ (completedTensorQuotientSystem A₀ hA₁ hA₂ D₁ D₂) where
  toRingHom := completedTensorRight A₀ A₁ A₂
  continuous := continuous_completedTensorRight A₀ A₁ A₂
  overS J K h := by
    have hc₁ : Continuous (algebraMap A₀ A₁) := hφ₁ ▸ φ₁.continuous
    have hc₂ : Continuous (algebraMap A₀ A₂) := hφ₂ ▸ φ₂.continuous
    let K₀ : { I : Ideal A₀ // TopologicalRing.IsWeakIdealOfDefinition I } :=
      ⟨hA₀.1.choose ⊓ (completedTensorLeftIdeal A₀ hA₁ K).1.comap (algebraMap A₀ A₁) ⊓
          J.1.comap (algebraMap A₀ A₂),
        ⟨by
          change IsOpen (((hA₀.1.choose : Set A₀) ∩
            (algebraMap A₀ A₁) ⁻¹' (completedTensorLeftIdeal A₀ hA₁ K).1) ∩
              (algebraMap A₀ A₂) ⁻¹' J.1)
          exact (hA₀.1.choose_spec.1.inter
            ((completedTensorLeftIdeal A₀ hA₁ K).2.1.preimage hc₁)).inter
            (J.2.1.preimage hc₂),
          fun x hx ↦ hA₀.1.choose_spec.2 x (Ideal.mem_inf.mp (Ideal.mem_inf.mp hx).1).1⟩⟩
    have h₁ : K₀.1 ≤ (completedTensorLeftIdeal A₀ hA₁ K).1.comap φ₁.toRingHom := by
      rw [hφ₁]; exact inf_le_left.trans inf_le_right
    have h₂ : K₀.1 ≤ J.1.comap φ₂.toRingHom := by
      rw [hφ₂]; exact inf_le_right
    change _ = Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 (completedTensorLeft A₀ A₁ A₂)
      (completedTensorLeftIdeal_le A₀ hA₁ K))) ≫ D₁.overS (completedTensorLeftIdeal A₀ hA₁ K)
    rw [← φ₂.overS K₀ J h₂, ← φ₁.overS K₀ _ h₁, ← Category.assoc, ← Category.assoc,
      ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 3
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun c ↦ ?_)
    change Ideal.Quotient.mk K.1 (completedTensorRight A₀ A₁ A₂ (φ₂.toRingHom c)) =
      Ideal.Quotient.mk K.1 (completedTensorLeft A₀ A₁ A₂ (φ₁.toRingHom c))
    rw [hφ₁, hφ₂]
    exact congrArg (Ideal.Quotient.mk K.1)
      (RingHom.congr_fun (completedTensorLeft_comp_algebraMap A₀ A₁ A₂) c).symm

end QuotientSystem

section Pullback

variable {C : Type*} [Category* C] {P X Y Z W : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}
  {g : Y ⟶ Z}

/-- A cartesian square stays cartesian after composing its two lower edges with a monomorphism. -/
private theorem isPullback_comp_mono (h : IsPullback fst snd f g) (i : Z ⟶ W) (_ : Mono i) :
    IsPullback fst snd (f ≫ i) (g ≫ i) := by
  have w : CommSq fst snd (f ≫ i) (g ≫ i) := ⟨by rw [← Category.assoc, h.w, Category.assoc]⟩
  refine IsPullback.of_isLimit' w (PullbackCone.IsLimit.mk _
    (fun s ↦ h.lift s.fst s.snd ((cancel_mono i).1 (by simpa using s.condition)))
    (fun s ↦ h.lift_fst _ _ _) (fun s ↦ h.lift_snd _ _ _)
    fun s m h₁ h₂ ↦ h.hom_ext (by simpa using h₁) (by simpa using h₂))

/-- A square whose lower edges become those of a cartesian square after composing with a
monomorphism is cartesian. -/
private theorem isPullback_of_comp_mono (i : Z ⟶ W) [Mono i]
    (h : IsPullback fst snd (f ≫ i) (g ≫ i)) : IsPullback fst snd f g := by
  have w : CommSq fst snd f g := ⟨(cancel_mono i).1 (by simpa using h.w)⟩
  refine IsPullback.of_isLimit' w (PullbackCone.IsLimit.mk _
    (fun s ↦ h.lift s.fst s.snd (by rw [← Category.assoc, s.condition, Category.assoc]))
    (fun s ↦ h.lift_fst _ _ _) (fun s ↦ h.lift_snd _ _ _)
    fun s m h₁ h₂ ↦ h.hom_ext (by simpa using h₁) (by simpa using h₂))

private theorem comp_comp_comp_assoc {V : C} (u : P ⟶ X) (v : X ⟶ Y) (w : Y ⟶ Z) (z : Z ⟶ V) :
    ((u ≫ v) ≫ w) ≫ z = u ≫ v ≫ w ≫ z := by
  simp only [Category.assoc]

private theorem comp_comp_comp_reassoc {V : C} (u : P ⟶ X) (v : X ⟶ Y) (w : Y ⟶ Z)
    (z : Z ⟶ V) : (u ≫ v) ≫ w ≫ z = u ≫ (v ≫ w) ≫ z := by
  simp only [Category.assoc]

private theorem comp_hom_inv_comp (u : P ⟶ X) (e : X ≅ Y) (z : X ⟶ Z) :
    (u ≫ e.hom) ≫ e.inv ≫ z = u ≫ z := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Pasting of commutative squares: if `ι ≫ σ` factors through `sM`, `q ≫ sM` through the
transition `tr`, and `tr ≫ ιM` is `ιI`, then `inv ≫ q ≫ ι ≫ σ` is `inv ≫ f1 ≫ ιI`. -/
private theorem comp_comp_comp_eq_of_factor {a b c d e f g : C} {inv : a ⟶ b} {q : b ⟶ c}
    {ι : c ⟶ d} {σ : d ⟶ e} {sM : c ⟶ f} {ιM : f ⟶ e} {f1 : b ⟶ g} {tr : g ⟶ f} {ιI : g ⟶ e}
    {pr : a ⟶ g} (hs : ι ≫ σ = sM ≫ ιM) (he : q ≫ sM = f1 ≫ tr) (hw : tr ≫ ιM = ιI)
    (hf : inv ≫ f1 = pr) : (inv ≫ q ≫ ι) ≫ σ = pr ≫ ιI := by
  rw [Category.assoc, Category.assoc, hs, ← Category.assoc q, he, Category.assoc, hw,
    ← Category.assoc, hf]

/-- Two maps into a square compare after composing with a projection, if each is compatible with
the projections. -/
private theorem comp_comp_eq_comp_comp_of_factor {a b c d e f : C} {x : a ⟶ b} {inv' : b ⟶ c}
    {F' : c ⟶ d} {pr' : b ⟶ d} {pr : a ⟶ e} {t : e ⟶ d} {inv : a ⟶ f} {T : f ⟶ c} {F : f ⟶ e}
    (h₁ : inv' ≫ F' = pr') (h₂ : x ≫ pr' = pr ≫ t) (h₃ : T ≫ F' = F ≫ t) (h₄ : inv ≫ F = pr) :
    (x ≫ inv') ≫ F' = (inv ≫ T) ≫ F' := by
  rw [Category.assoc, Category.assoc, h₁, h₂, h₃, ← Category.assoc, h₄]

/-- A map out of a stage that is compatible with the maps `σ` and `lift ≫ fst`, and a comparison
isomorphism `iso`, give equal composites with `fst`. -/
private theorem comp_lift_comp_eq_of_factor {a b c d e f g : C} {ι : a ⟶ b} {lift : b ⟶ c}
    {fst : c ⟶ d} {σ : b ⟶ d} {Yn : a ⟶ f} {ιI : f ⟶ d} {n : a ⟶ e} {iso : e ⟶ g} {rl : g ⟶ c}
    {pr : g ⟶ f} {F : e ⟶ f} (hlift : lift ≫ fst = σ) (hA : ι ≫ σ = Yn ≫ ιI) (hF : Yn = n ≫ F)
    (hrl : rl ≫ fst = pr ≫ ιI) (kf : iso ≫ pr = F) :
    (ι ≫ lift) ≫ fst = ((n ≫ iso) ≫ rl) ≫ fst := by
  subst hF
  simp only [Category.assoc]
  rw [hlift, hA, hrl, ← Category.assoc iso, kf, Category.assoc]

end Pullback

/-- Two composites in the big fppf site over `S` are equal if the underlying composites of schemes
are. -/
private theorem comp_eq_comp_of_toScheme_map {X Y Z W : BigFppfOver B S hS} {f : X ⟶ Y}
    {g : Y ⟶ W} {f' : X ⟶ Z} {g' : Z ⟶ W}
    (h : (BigFppfOver.toScheme B S hS).map f ≫ (BigFppfOver.toScheme B S hS).map g =
      (BigFppfOver.toScheme B S hS).map f' ≫ (BigFppfOver.toScheme B S hS).map g') :
    f ≫ g = f' ≫ g' :=
  (BigFppfOver.toScheme B S hS).map_injective (by rwa [Functor.map_comp, Functor.map_comp])

/-- A composite of morphisms of the big fppf site over `S` is a given morphism if this holds
for the underlying schemes. -/
private theorem comp_eq_of_toScheme_map {X Y Z : BigFppfOver B S hS} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : X ⟶ Z}
    (e : (BigFppfOver.toScheme B S hS).map f ≫ (BigFppfOver.toScheme B S hS).map g =
      (BigFppfOver.toScheme B S hS).map h) : f ≫ g = h :=
  (BigFppfOver.toScheme B S hS).map_injective (by rwa [Functor.map_comp])

section Stage

variable (A₀) (hA₁ : TopologicalRing.IsWeaklyAdmissible A₁)
  (hA₂ : TopologicalRing.IsWeaklyAdmissible A₂)
  (D₁ : QuotientSystem B S hS A₁) (D₂ : QuotientSystem B S hS A₂)
  {D₀ : QuotientSystem B S hS A₀} (hA₀ : TopologicalRing.IsWeaklyAdmissible A₀)
  (φ₁ : ContinuousHom D₀ D₁) (φ₂ : ContinuousHom D₀ D₂)
  (hφ₁ : φ₁.toRingHom = algebraMap A₀ A₁) (hφ₂ : φ₂.toRingHom = algebraMap A₀ A₂)
  (I : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I })
  (J : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J })

/-- The affine scheme `Spec (A₁/I ⊗_{A₀} A₂/J)` as an object of the big fppf site over `S`,
lying over `S` through the stage `Spec (A₁/I)` of `A₁`. -/
def completedTensorStage : BigFppfOver B S hS :=
  siteObject B S hS (BigFppfSite.contains_spec_tensorProduct B (R := A₀) (D₁.inSite I)
      (D₂.inSite J))
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
      A₁ ⧸ I.1 →+* (A₁ ⧸ I.1) ⊗[A₀] (A₂ ⧸ J.1))) ≫ D₁.overS I)

/-- The projection of `Spec (A₁/I ⊗_{A₀} A₂/J)` to the stage `Spec (A₁/I)`. -/
def completedTensorStageFst :
    completedTensorStage A₀ D₁ D₂ I J ⟶ (BigAffineFppf.inclusion B S hS).obj (D₁.stage I) :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeLeftRingHom : A₁ ⧸ I.1 →+* (A₁ ⧸ I.1) ⊗[A₀] (A₂ ⧸ J.1)))))
    (by apply ObjectProperty.hom_ext; rfl)

include hφ₁ hφ₂ in
omit [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] [IsTopologicalRing A₁]
  [IsLinearTopology A₁ A₁] [IsTopologicalRing A₂] [IsLinearTopology A₂ A₂] in
/-- The two composites `A₀/K → A₁/I ⊗_{A₀} A₂/J` agree. -/
private theorem includeRight_comp_quotientMap
    (K : { K : Ideal A₀ // TopologicalRing.IsWeakIdealOfDefinition K })
    (h₁ : K.1 ≤ I.1.comap φ₁.toRingHom) (h₂ : K.1 ≤ J.1.comap φ₂.toRingHom) :
    (Algebra.TensorProduct.includeRight :
        A₂ ⧸ J.1 →ₐ[A₀] (A₁ ⧸ I.1) ⊗[A₀] (A₂ ⧸ J.1)).toRingHom.comp
        (Ideal.quotientMap J.1 φ₂.toRingHom h₂) =
      (Algebra.TensorProduct.includeLeftRingHom :
        A₁ ⧸ I.1 →+* (A₁ ⧸ I.1) ⊗[A₀] (A₂ ⧸ J.1)).comp (Ideal.quotientMap I.1 φ₁.toRingHom h₁) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun c ↦ ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, Ideal.quotientMap_mk, hφ₁, hφ₂,
    Ideal.Quotient.mk_algebraMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
  rw [← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply]

omit [IsTopologicalRing A₁] [IsLinearTopology A₁ A₁] [IsTopologicalRing A₂]
  [IsLinearTopology A₂ A₂] in
include hA₀ hφ₁ hφ₂ in
/-- The two morphisms `Spec (A₁/I ⊗_{A₀} A₂/J) ⟶ S`, through the stage `Spec (A₂/J)` and through
the stage `Spec (A₁/I)`, agree. -/
theorem completedTensorStage_overS_right :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
        A₂ ⧸ J.1 →ₐ[A₀] (A₁ ⧸ I.1) ⊗[A₀] (A₂ ⧸ J.1)).toRingHom) ≫ D₂.overS J =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        A₁ ⧸ I.1 →+* (A₁ ⧸ I.1) ⊗[A₀] (A₂ ⧸ J.1))) ≫ D₁.overS I := by
  obtain ⟨K, h₁, h₂⟩ := exists_isWeakIdealOfDefinition_le_comap_of_isOpen hA₀ φ₁.continuous
    φ₂.continuous I.2.1 J.2.1
  rw [← φ₂.overS K J h₂, ← φ₁.overS K I h₁, ← Category.assoc, ← Category.assoc,
    spec_map_comp_eq _ _ _ _ (includeRight_comp_quotientMap A₀ D₁ D₂ φ₁ φ₂ hφ₁ hφ₂ I J K h₁ h₂)]

/-- The projection of `Spec (A₁/I ⊗_{A₀} A₂/J)` to the stage `Spec (A₂/J)`. -/
def completedTensorStageSnd :
    completedTensorStage A₀ D₁ D₂ I J ⟶ (BigAffineFppf.inclusion B S hS).obj (D₂.stage J) :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight :
      A₂ ⧸ J.1 →ₐ[A₀] (A₁ ⧸ I.1) ⊗[A₀] (A₂ ⧸ J.1)).toRingHom)))
    (ObjectProperty.hom_ext _ (completedTensorStage_overS_right A₀ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J))

omit [IsTopologicalRing A₁] [IsLinearTopology A₁ A₁] [IsTopologicalRing A₂]
  [IsLinearTopology A₂ A₂] in
/-- For a weak ideal of
definition `K ⊆ A₀` mapping into `I` and into `J`, the square
`Spec (A₁/I ⊗_{A₀} A₂/J) ⟶ Spec (A₁/I), Spec (A₂/J) ⟶ Spec (A₀/K)` is cartesian in the big fppf
site over `S`. -/
theorem isPullback_completedTensorStage
    (K : { K : Ideal A₀ // TopologicalRing.IsWeakIdealOfDefinition K })
    (h₁ : K.1 ≤ I.1.comap φ₁.toRingHom) (h₂ : K.1 ≤ J.1.comap φ₂.toRingHom) :
    IsPullback (completedTensorStageFst A₀ D₁ D₂ I J)
      (completedTensorStageSnd A₀ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J)
      ((BigAffineFppf.inclusion B S hS).map (φ₁.stageMap K I h₁))
      ((BigAffineFppf.inclusion B S hS).map (φ₂.stageMap K J h₂)) := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have : ReflectsLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  refine IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) ?_
  change IsPullback
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
      A₁ ⧸ I.1 →+* (A₁ ⧸ I.1) ⊗[A₀] (A₂ ⧸ J.1))))
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight :
      A₂ ⧸ J.1 →ₐ[A₀] (A₁ ⧸ I.1) ⊗[A₀] (A₂ ⧸ J.1)).toRingHom))
    (Spec.map (CommRingCat.ofHom (Ideal.quotientMap I.1 φ₁.toRingHom h₁)))
    (Spec.map (CommRingCat.ofHom (Ideal.quotientMap J.1 φ₂.toRingHom h₂)))
  have hsq := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct A₀ (A₁ ⧸ I.1) (A₂ ⧸ J.1))
  have e₁ : Spec.map (CommRingCat.ofHom (algebraMap A₀ (A₁ ⧸ I.1))) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap I.1 φ₁.toRingHom h₁)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K.1)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun c ↦ by simp [hφ₁, Ideal.Quotient.mk_algebraMap]
  have e₂ : Spec.map (CommRingCat.ofHom (algebraMap A₀ (A₂ ⧸ J.1))) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap J.1 φ₂.toRingHom h₂)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K.1)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun c ↦ by simp [hφ₂, Ideal.Quotient.mk_algebraMap]
  rw [e₁, e₂] at hsq
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K.1))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact isPullback_of_comp_mono _ hsq

omit [IsTopologicalRing A₁] [IsLinearTopology A₁ A₁] [IsTopologicalRing A₂]
  [IsLinearTopology A₂ A₂] in
/-- The fibre product over `Spf A₀` of the stages `Spec (A₁/I)` and `Spec (A₂/J)` is
`Spec (A₁/I ⊗_{A₀} A₂/J)`. -/
theorem isPullback_completedTensorStage_formalSpectrum :
    IsPullback
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (completedTensorStageFst A₀ D₁ D₂ I J))
      ((Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        (completedTensorStageSnd A₀ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J))
      (formalSpectrumInclusion D₁ (OrderDual.toDual I) ≫ formalSpectrumMap hA₀ φ₁)
      (formalSpectrumInclusion D₂ (OrderDual.toDual J) ≫ formalSpectrumMap hA₀ φ₂) := by
  obtain ⟨K, h₁, h₂⟩ := exists_isWeakIdealOfDefinition_le_comap_of_isOpen hA₀ φ₁.continuous
    φ₂.continuous I.2.1 J.2.1
  have : PreservesLimitsOfShape WalkingCospan
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan
      (uliftYoneda.{u + 1} ⋙ presheafToSheaf (BigFppfOver.topology B S hS) (Type (u + 1))))
  have h := isPullback_comp_mono
    ((isPullback_completedTensorStage A₀ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J K h₁ h₂).map
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)))
    (formalSpectrumInclusion D₀ (OrderDual.toDual K))
    (mono_formalSpectrumInclusion hA₀ D₀ _)
  rwa [← formalSpectrumMap_spec hA₀ φ₁ K I h₁, ← formalSpectrumMap_spec hA₀ φ₂ K J h₂] at h

end Stage

section Product

variable (A₀) (hA₁ : TopologicalRing.IsWeaklyAdmissible A₁)
  (hA₂ : TopologicalRing.IsWeaklyAdmissible A₂)
  (D₁ : QuotientSystem B S hS A₁) (D₂ : QuotientSystem B S hS A₂)
  {D₀ : QuotientSystem B S hS A₀} (hA₀ : TopologicalRing.IsWeaklyAdmissible A₀)
  (φ₁ : ContinuousHom D₀ D₁) (φ₂ : ContinuousHom D₀ D₂)
  (hφ₁ : φ₁.toRingHom = algebraMap A₀ A₁) (hφ₂ : φ₂.toRingHom = algebraMap A₀ A₂)
  (I : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I })
  (J : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J })

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The projections of `A₁ ⊗̂_{A₀} A₂` onto the tensor products of the stages are compatible
with the maps between those tensor products. -/
theorem completedTensorStageRingHom_factor
    {I I' : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I }}
    {J J' : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J }}
    (hI : I'.1 ≤ I.1) (hJ : J'.1 ≤ J.1)
    (x : TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) :
    Algebra.TensorProduct.map (Ideal.Quotient.factorₐ A₀ hI) (Ideal.Quotient.factorₐ A₀ hJ)
        (completedTensorStageRingHom A₀ hA₁ hA₂ I' J' x) =
      completedTensorStageRingHom A₀ hA₁ hA₂ I J x :=
  (TopologicalRing.completedTensorProductRingEquivQuotientLimit (B := A₀)
    (fun I : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I } ↦ I.1)
    (fun J : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J } ↦ J.1)
    (hasBasis_nhds_zero_isWeakIdealOfDefinition hA₁)
    (hasBasis_nhds_zero_isWeakIdealOfDefinition hA₂) x).2 (I', J') (I, J) hI hJ

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The canonical maps multiply to the image of a pure tensor. -/
theorem completedTensorLeft_mul_completedTensorRight (a : A₁) (c : A₂) :
    letI := TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A₂)
    completedTensorLeft A₀ A₁ A₂ a * completedTensorRight A₀ A₁ A₂ c =
      ((a ⊗ₜ[A₀] c : A₁ ⊗[A₀] A₂) :
        TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) := by
  let := TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A₂)
  change (UniformSpace.Completion.coeRingHom :
      (A₁ ⊗[A₀] A₂) →+* TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂))
        (a ⊗ₜ[A₀] (1 : A₂)) * UniformSpace.Completion.coeRingHom ((1 : A₁) ⊗ₜ[A₀] c) = _
  rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rfl

/-- The weak ideal of definition `L₀ ∩ ker(T → A₁/I ⊗_{A₀} A₂/J)` of `T = A₁ ⊗̂_{A₀} A₂`, for a
fixed weak ideal of definition `L₀` of `T`. -/
def completedTensorStageIdeal :
    { L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) //
      TopologicalRing.IsWeakIdealOfDefinition L } :=
  ⟨(TopologicalRing.completedTensorProduct_isWeaklyAdmissible (B := A₀) hA₁.1 hA₂.1).1.choose ⊓
      RingHom.ker (completedTensorStageRingHom A₀ hA₁ hA₂ I J),
    TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right
      (TopologicalRing.completedTensorProduct_isWeaklyAdmissible (B := A₀)
        hA₁.1 hA₂.1).1.choose_spec
      (isOpen_ker_completedTensorStageRingHom A₀ hA₁ hA₂ I J)⟩

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The ideal `completedTensorStageIdeal A₀ hA₁ hA₂ I J` lies in the kernel of the projection onto
`A₁/I ⊗_{A₀} A₂/J`. -/
theorem completedTensorStageIdeal_le_ker :
    (completedTensorStageIdeal A₀ hA₁ hA₂ I J).1 ≤
      RingHom.ker (completedTensorStageRingHom A₀ hA₁ hA₂ I J) :=
  inf_le_right

/-- The ring map `T/L → A₁/I ⊗_{A₀} A₂/J` induced by the projection, for
`L = completedTensorStageIdeal A₀ hA₁ hA₂ I J`. -/
def completedTensorStageQuotientMap :
    TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂) ⧸
        (completedTensorStageIdeal A₀ hA₁ hA₂ I J).1 →+* (A₁ ⧸ I.1) ⊗[A₀] (A₂ ⧸ J.1) :=
  Ideal.Quotient.lift _ (completedTensorStageRingHom A₀ hA₁ hA₂ I J)
    (fun _ ha ↦ RingHom.mem_ker.mp (completedTensorStageIdeal_le_ker A₀ hA₁ hA₂ I J ha))

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The map `T/L → A₁/I ⊗_{A₀} A₂/J` sends the class of `x` to the projection of `x`. -/
theorem completedTensorStageQuotientMap_mk
    (x : TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) :
    completedTensorStageQuotientMap A₀ hA₁ hA₂ I J (Ideal.Quotient.mk _ x) =
      completedTensorStageRingHom A₀ hA₁ hA₂ I J x :=
  Ideal.Quotient.lift_mk _ _ _

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- `Spec (A₁/I ⊗_{A₀} A₂/J) ⟶ Spec (T/L)` lies over `S`. -/
theorem completedTensorStageToQuotient_overS :
    Spec.map (CommRingCat.ofHom (completedTensorStageQuotientMap A₀ hA₁ hA₂ I J)) ≫
        (completedTensorQuotientSystem A₀ hA₁ hA₂ D₁ D₂).overS
          (completedTensorStageIdeal A₀ hA₁ hA₂ I J) =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        A₁ ⧸ I.1 →+* (A₁ ⧸ I.1) ⊗[A₀] (A₂ ⧸ J.1))) ≫ D₁.overS I := by
  let L := completedTensorStageIdeal A₀ hA₁ hA₂ I J
  let I' := completedTensorLeftIdeal A₀ hA₁ L
  let M : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨I.1 ⊓ I'.1, TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right I.2 I'.2.1⟩
  change _ ≫ Spec.map (CommRingCat.ofHom (Ideal.quotientMap L.1 (completedTensorLeft A₀ A₁ A₂)
      (completedTensorLeftIdeal_le A₀ hA₁ L))) ≫ D₁.overS I' = _
  rw [← D₁.compatible M I inf_le_left, ← D₁.compatible M I' inf_le_right]
  simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_)
  change completedTensorStageQuotientMap A₀ hA₁ hA₂ I J
    (Ideal.Quotient.mk _ (completedTensorLeft A₀ A₁ A₂ a)) = _
  rw [completedTensorStageQuotientMap_mk, completedTensorStageRingHom_left]
  rfl

/-- The map `Spec (A₁/I ⊗_{A₀} A₂/J) ⟶ Spec (T/L)` of objects of the site, for
`L = completedTensorStageIdeal A₀ hA₁ hA₂ I J`. -/
def completedTensorStageToQuotient :
    completedTensorStage A₀ D₁ D₂ I J ⟶ (BigAffineFppf.inclusion B S hS).obj
      ((completedTensorQuotientSystem A₀ hA₁ hA₂ D₁ D₂).stage
        (completedTensorStageIdeal A₀ hA₁ hA₂ I J)) :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
    (completedTensorStageQuotientMap A₀ hA₁ hA₂ I J))))
    (ObjectProperty.hom_ext _ (completedTensorStageToQuotient_overS A₀ hA₁ hA₂ D₁ D₂ I J))

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] [IsTopologicalRing A₁]
  [IsLinearTopology A₁ A₁] [IsTopologicalRing A₂] [IsLinearTopology A₂ A₂] in
private theorem tensorMap_comp_includeLeft
    {I I' : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I }}
    {J J' : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J }}
    (hI : I'.1 ≤ I.1) (hJ : J'.1 ≤ J.1) :
    (Algebra.TensorProduct.map (Ideal.Quotient.factorₐ A₀ hI)
        (Ideal.Quotient.factorₐ A₀ hJ)).toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom :
        A₁ ⧸ I'.1 →+* (A₁ ⧸ I'.1) ⊗[A₀] (A₂ ⧸ J'.1)) =
    (Algebra.TensorProduct.includeLeftRingHom :
        A₁ ⧸ I.1 →+* (A₁ ⧸ I.1) ⊗[A₀] (A₂ ⧸ J.1)).comp (Ideal.Quotient.factor hI) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_)
  simp

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] [IsTopologicalRing A₁]
  [IsLinearTopology A₁ A₁] [IsTopologicalRing A₂] [IsLinearTopology A₂ A₂] in
private theorem tensorMap_comp_includeRight
    {I I' : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I }}
    {J J' : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J }}
    (hI : I'.1 ≤ I.1) (hJ : J'.1 ≤ J.1) :
    (Algebra.TensorProduct.map (Ideal.Quotient.factorₐ A₀ hI)
        (Ideal.Quotient.factorₐ A₀ hJ)).toRingHom.comp
      (Algebra.TensorProduct.includeRight :
        A₂ ⧸ J'.1 →ₐ[A₀] (A₁ ⧸ I'.1) ⊗[A₀] (A₂ ⧸ J'.1)).toRingHom =
    (Algebra.TensorProduct.includeRight :
        A₂ ⧸ J.1 →ₐ[A₀] (A₁ ⧸ I.1) ⊗[A₀] (A₂ ⧸ J.1)).toRingHom.comp
      (Ideal.Quotient.factor hJ) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun c ↦ ?_)
  simp

omit [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] [IsTopologicalRing A₁]
  [IsLinearTopology A₁ A₁] [IsTopologicalRing A₂] [IsLinearTopology A₂ A₂] [TopologicalSpace A₀] in
/-- The map `Spec (A₁/I ⊗_{A₀} A₂/J) ⟶ Spec (A₁/I' ⊗_{A₀} A₂/J')` for `I' ⊆ I` and `J' ⊆ J`
commutes with the morphisms to `S`. -/
theorem completedTensorStageTransition_overS
    {I I' : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I }}
    {J J' : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J }}
    (hI : I'.1 ≤ I.1) (hJ : J'.1 ≤ J.1) :
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (Ideal.Quotient.factorₐ A₀ hI)
        (Ideal.Quotient.factorₐ A₀ hJ)).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        A₁ ⧸ I'.1 →+* (A₁ ⧸ I'.1) ⊗[A₀] (A₂ ⧸ J'.1))) ≫ D₁.overS I' =
    Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        A₁ ⧸ I.1 →+* (A₁ ⧸ I.1) ⊗[A₀] (A₂ ⧸ J.1))) ≫ D₁.overS I := by
  rw [← D₁.compatible I' I hI, ← Category.assoc, ← Category.assoc,
    spec_map_comp_eq _ _ _ _ (tensorMap_comp_includeLeft A₀ hI hJ)]

/-- The map `Spec (A₁/I ⊗_{A₀} A₂/J) ⟶ Spec (A₁/I' ⊗_{A₀} A₂/J')` for `I' ⊆ I` and `J' ⊆ J`. -/
def completedTensorStageTransition
    {I I' : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I }}
    {J J' : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J }}
    (hI : I'.1 ≤ I.1) (hJ : J'.1 ≤ J.1) :
    completedTensorStage A₀ D₁ D₂ I J ⟶ completedTensorStage A₀ D₁ D₂ I' J' :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.map (Ideal.Quotient.factorₐ A₀ hI)
      (Ideal.Quotient.factorₐ A₀ hJ)).toRingHom)))
    (ObjectProperty.hom_ext _ (completedTensorStageTransition_overS A₀ D₁ hI hJ))

omit [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] [IsTopologicalRing A₁]
  [IsLinearTopology A₁ A₁] [IsTopologicalRing A₂] [IsLinearTopology A₂ A₂] [TopologicalSpace A₀] in
/-- The transition maps between the stages `Spec (A₁/I ⊗_{A₀} A₂/J)` commute with the projections
to the stages of `A₁`. -/
theorem completedTensorStageTransition_fst
    {I I' : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I }}
    {J J' : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J }}
    (hI : I'.1 ≤ I.1) (hJ : J'.1 ≤ J.1) :
    completedTensorStageTransition A₀ D₁ D₂ hI hJ ≫ completedTensorStageFst A₀ D₁ D₂ I' J' =
      completedTensorStageFst A₀ D₁ D₂ I J ≫
        (BigAffineFppf.inclusion B S hS).map (D₁.transition hI) := by
  exact comp_eq_comp_of_toScheme_map
    (spec_map_comp_eq _ _ _ _ (tensorMap_comp_includeLeft A₀ hI hJ))

omit [IsTopologicalRing A₁] [IsLinearTopology A₁ A₁] [IsTopologicalRing A₂]
  [IsLinearTopology A₂ A₂] in
/-- The transition maps between the stages `Spec (A₁/I ⊗_{A₀} A₂/J)` commute with the projections
to the stages of `A₂`. -/
theorem completedTensorStageTransition_snd
    {I I' : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I }}
    {J J' : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J }}
    (hI : I'.1 ≤ I.1) (hJ : J'.1 ≤ J.1) :
    completedTensorStageTransition A₀ D₁ D₂ hI hJ ≫
        completedTensorStageSnd A₀ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I' J' =
      completedTensorStageSnd A₀ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J ≫
        (BigAffineFppf.inclusion B S hS).map (D₂.transition hJ) := by
  exact comp_eq_comp_of_toScheme_map
    (spec_map_comp_eq _ _ _ _ (tensorMap_comp_includeRight A₀ hI hJ))

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The ideals `completedTensorStageIdeal` decrease with `I` and `J`. -/
theorem completedTensorStageIdeal_mono
    {I I' : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I }}
    {J J' : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J }}
    (hI : I'.1 ≤ I.1) (hJ : J'.1 ≤ J.1) :
    (completedTensorStageIdeal A₀ hA₁ hA₂ I' J').1 ≤ (completedTensorStageIdeal A₀ hA₁ hA₂ I J).1 :=
  inf_le_inf_left _ fun x hx ↦ by
    rw [RingHom.mem_ker] at hx ⊢
    rw [← completedTensorStageRingHom_factor A₀ hA₁ hA₂ hI hJ x, hx, map_zero]

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The transition maps between the stages `Spec (A₁/I ⊗_{A₀} A₂/J)` commute with the maps
`completedTensorStageToQuotient` to the stages of `A₁ ⊗̂_{A₀} A₂`. -/
theorem completedTensorStageTransition_toQuotient
    {I I' : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I }}
    {J J' : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J }}
    (hI : I'.1 ≤ I.1) (hJ : J'.1 ≤ J.1) :
    completedTensorStageTransition A₀ D₁ D₂ hI hJ ≫
        completedTensorStageToQuotient A₀ hA₁ hA₂ D₁ D₂ I' J' =
      completedTensorStageToQuotient A₀ hA₁ hA₂ D₁ D₂ I J ≫
        (BigAffineFppf.inclusion B S hS).map
          ((completedTensorQuotientSystem A₀ hA₁ hA₂ D₁ D₂).transition
            (completedTensorStageIdeal_mono A₀ hA₁ hA₂ hI hJ)) := by
  refine comp_eq_comp_of_toScheme_map (spec_map_comp_eq _ _ _ _
    (Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_)))
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    completedTensorStageQuotientMap_mk, Ideal.Quotient.factor_mk,
    completedTensorStageRingHom_factor]

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- For the ideals `completedTensorLeftIdeal` and `completedTensorRightIdeal` attached to `L`, the
kernel of the projection onto `A₁/I ⊗_{A₀} A₂/J` lies in `L`. -/
theorem ker_completedTensorStageRingHom_le_of_ideal
    (L : { L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) //
      TopologicalRing.IsWeakIdealOfDefinition L }) :
    RingHom.ker (completedTensorStageRingHom A₀ hA₁ hA₂ (completedTensorLeftIdeal A₀ hA₁ L)
      (completedTensorRightIdeal A₀ hA₂ L)) ≤ L.1 :=
  ker_completedTensorStageRingHom_le A₀ hA₁ hA₂ _ _ L.1 L.2.1
    (fun _ ha ↦ (Ideal.mem_inf.mp ha).2) (fun _ hc ↦ (Ideal.mem_inf.mp hc).2)

/-- The ring map `A₁/I ⊗_{A₀} A₂/J → T/L` induced by the projection, for `I` and `J` the
ideals `completedTensorLeftIdeal` and `completedTensorRightIdeal` attached to `L`. -/
def completedTensorQuotientRingHom
    (L : { L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) //
      TopologicalRing.IsWeakIdealOfDefinition L }) :
    (A₁ ⧸ (completedTensorLeftIdeal A₀ hA₁ L).1) ⊗[A₀]
        (A₂ ⧸ (completedTensorRightIdeal A₀ hA₂ L).1) →+*
      TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂) ⧸ L.1 :=
  (Ideal.Quotient.factor (ker_completedTensorStageRingHom_le_of_ideal A₀ hA₁ hA₂ L)).comp
    (RingHom.quotientKerEquivOfSurjective
      (surjective_completedTensorStageRingHom A₀ hA₁ hA₂ _ _)).symm.toRingHom

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The ring map `A₁/I ⊗_{A₀} A₂/J → T/L` is inverse to the projection modulo `L`. -/
theorem completedTensorQuotientRingHom_stageRingHom
    (L : { L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) //
      TopologicalRing.IsWeakIdealOfDefinition L })
    (x : TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) :
    completedTensorQuotientRingHom A₀ hA₁ hA₂ L (completedTensorStageRingHom A₀ hA₁ hA₂
        (completedTensorLeftIdeal A₀ hA₁ L) (completedTensorRightIdeal A₀ hA₂ L) x) =
      Ideal.Quotient.mk L.1 x := by
  have h : (RingHom.quotientKerEquivOfSurjective
      (surjective_completedTensorStageRingHom A₀ hA₁ hA₂ (completedTensorLeftIdeal A₀ hA₁ L)
        (completedTensorRightIdeal A₀ hA₂ L))).symm
      (completedTensorStageRingHom A₀ hA₁ hA₂ _ _ x) = Ideal.Quotient.mk _ x := by
    rw [RingEquiv.symm_apply_eq, RingHom.quotientKerEquivOfSurjective_apply_mk]
  exact (congrArg (Ideal.Quotient.factor (ker_completedTensorStageRingHom_le_of_ideal A₀ hA₁ hA₂ L))
    h).trans (Ideal.Quotient.factor_mk _ _)

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The map `A₁/I ⊗_{A₀} A₂/J → T/L` sends `ā ⊗ c̄` to the class of the product of the images of
`a` and `c` in `T`. -/
theorem completedTensorQuotientRingHom_tmul
    (L : { L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) //
      TopologicalRing.IsWeakIdealOfDefinition L }) (a : A₁) (c : A₂) :
    completedTensorQuotientRingHom A₀ hA₁ hA₂ L
        (Ideal.Quotient.mk _ a ⊗ₜ[A₀] Ideal.Quotient.mk _ c) =
      Ideal.Quotient.mk L.1 (completedTensorLeft A₀ A₁ A₂ a * completedTensorRight A₀ A₁ A₂ c) := by
  let := TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A₂)
  have h := completedTensorStageRingHom_coe A₀ hA₁ hA₂ (completedTensorLeftIdeal A₀ hA₁ L)
    (completedTensorRightIdeal A₀ hA₂ L) (a ⊗ₜ[A₀] c)
  rw [Algebra.TensorProduct.map_tmul, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.mkₐ_eq_mk] at h
  rw [← h, completedTensorQuotientRingHom_stageRingHom,
    completedTensorLeft_mul_completedTensorRight]

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- Restricted to `A₁/I`, the map `A₁/I ⊗_{A₀} A₂/J → T/L` is induced by `A₁ → T`. -/
theorem completedTensorQuotientRingHom_comp_includeLeft
    (L : { L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) //
      TopologicalRing.IsWeakIdealOfDefinition L }) :
    (completedTensorQuotientRingHom A₀ hA₁ hA₂ L).comp Algebra.TensorProduct.includeLeftRingHom =
      Ideal.quotientMap L.1 (completedTensorLeft A₀ A₁ A₂)
        (completedTensorLeftIdeal_le A₀ hA₁ L) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_)
  simp only [RingHom.coe_comp, Function.comp_apply,
    Algebra.TensorProduct.includeLeftRingHom_apply, Ideal.quotientMap_mk]
  rw [← map_one (Ideal.Quotient.mk (completedTensorRightIdeal A₀ hA₂ L).1),
    completedTensorQuotientRingHom_tmul, map_one, mul_one]

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- Restricted to `A₂/J`, the map `A₁/I ⊗_{A₀} A₂/J → T/L` is induced by `A₂ → T`. -/
theorem completedTensorQuotientRingHom_comp_includeRight
    (L : { L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) //
      TopologicalRing.IsWeakIdealOfDefinition L }) :
    (completedTensorQuotientRingHom A₀ hA₁ hA₂ L).comp
        (Algebra.TensorProduct.includeRight : A₂ ⧸ (completedTensorRightIdeal A₀ hA₂ L).1 →ₐ[A₀]
          (A₁ ⧸ (completedTensorLeftIdeal A₀ hA₁ L).1) ⊗[A₀]
            (A₂ ⧸ (completedTensorRightIdeal A₀ hA₂ L).1)).toRingHom =
      Ideal.quotientMap L.1 (completedTensorRight A₀ A₁ A₂)
        (completedTensorRightIdeal_le A₀ hA₂ L) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun c ↦ ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Ideal.quotientMap_mk]
  rw [← map_one (Ideal.Quotient.mk (completedTensorLeftIdeal A₀ hA₁ L).1),
    completedTensorQuotientRingHom_tmul, map_one, one_mul]

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The map `Spec (T/L) ⟶ Spec (A₁/I ⊗_{A₀} A₂/J)` commutes with the morphisms to `S`. -/
theorem completedTensorQuotientToStage_overS
    (L : { L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) //
      TopologicalRing.IsWeakIdealOfDefinition L }) :
    Spec.map (CommRingCat.ofHom (completedTensorQuotientRingHom A₀ hA₁ hA₂ L)) ≫
        Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom) ≫
          D₁.overS (completedTensorLeftIdeal A₀ hA₁ L) =
      (completedTensorQuotientSystem A₀ hA₁ hA₂ D₁ D₂).overS L := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    completedTensorQuotientRingHom_comp_includeLeft]
  rfl

/-- The map `Spec (T/L) ⟶ Spec (A₁/I ⊗_{A₀} A₂/J)` of objects of the site, for `I` and `J` the
ideals `completedTensorLeftIdeal` and `completedTensorRightIdeal` attached to `L`. -/
def completedTensorQuotientToStage
    (L : { L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) //
      TopologicalRing.IsWeakIdealOfDefinition L }) :
    (BigAffineFppf.inclusion B S hS).obj
        ((completedTensorQuotientSystem A₀ hA₁ hA₂ D₁ D₂).stage L) ⟶
      completedTensorStage A₀ D₁ D₂ (completedTensorLeftIdeal A₀ hA₁ L)
        (completedTensorRightIdeal A₀ hA₂ L) :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
    (completedTensorQuotientRingHom A₀ hA₁ hA₂ L))))
    (ObjectProperty.hom_ext _ (completedTensorQuotientToStage_overS A₀ hA₁ hA₂ D₁ D₂ L))

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The map `Spec (T/L) ⟶ Spec (A₁/I ⊗_{A₀} A₂/J)` followed by the projection to `Spec (A₁/I)` is
the stage map of `A₁ → T`. -/
theorem completedTensorQuotientToStage_fst
    (L : { L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) //
      TopologicalRing.IsWeakIdealOfDefinition L }) :
    completedTensorQuotientToStage A₀ hA₁ hA₂ D₁ D₂ L ≫
        completedTensorStageFst A₀ D₁ D₂ _ _ =
      (BigAffineFppf.inclusion B S hS).map ((completedTensorLeftHom A₀ hA₁ hA₂ D₁ D₂).stageMap
        (completedTensorLeftIdeal A₀ hA₁ L) L (completedTensorLeftIdeal_le A₀ hA₁ L)) := by
  refine comp_eq_of_toScheme_map ?_
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, completedTensorQuotientRingHom_comp_includeLeft]
  rfl

/-- The map `Spec (T/L) ⟶ Spec (A₁/I ⊗_{A₀} A₂/J)` followed by the projection to `Spec (A₂/J)` is
the stage map of `A₂ → T`. -/
theorem completedTensorQuotientToStage_snd
    (L : { L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) //
      TopologicalRing.IsWeakIdealOfDefinition L }) :
    completedTensorQuotientToStage A₀ hA₁ hA₂ D₁ D₂ L ≫
        completedTensorStageSnd A₀ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ _ _ =
      (BigAffineFppf.inclusion B S hS).map
        ((completedTensorRightHom A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂).stageMap
          (completedTensorRightIdeal A₀ hA₂ L) L (completedTensorRightIdeal_le A₀ hA₂ L)) := by
  refine comp_eq_of_toScheme_map ?_
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, completedTensorQuotientRingHom_comp_includeRight]
  rfl

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The composite `Spec (T/L) ⟶ Spec (A₁/I ⊗_{A₀} A₂/J) ⟶ Spec (T/L')`, for
`L' = completedTensorStageIdeal A₀ hA₁ hA₂ I J`, is the transition map of the stages of `T`. -/
theorem completedTensorQuotientToStage_toQuotient
    (L : { L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) //
      TopologicalRing.IsWeakIdealOfDefinition L })
    (h : (completedTensorStageIdeal A₀ hA₁ hA₂ (completedTensorLeftIdeal A₀ hA₁ L)
      (completedTensorRightIdeal A₀ hA₂ L)).1 ≤ L.1) :
    completedTensorQuotientToStage A₀ hA₁ hA₂ D₁ D₂ L ≫
        completedTensorStageToQuotient A₀ hA₁ hA₂ D₁ D₂ _ _ =
      (BigAffineFppf.inclusion B S hS).map
        ((completedTensorQuotientSystem A₀ hA₁ hA₂ D₁ D₂).transition h) := by
  refine comp_eq_of_toScheme_map ?_
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun x ↦ ?_)
  simp only [RingHom.coe_comp, Function.comp_apply, completedTensorStageQuotientMap_mk,
    completedTensorQuotientRingHom_stageRingHom, Ideal.Quotient.factor_mk]

end Product

section Main

variable (A₀) (hA₁ : TopologicalRing.IsWeaklyAdmissible A₁)
  (hA₂ : TopologicalRing.IsWeaklyAdmissible A₂)
  (D₁ : QuotientSystem B S hS A₁) (D₂ : QuotientSystem B S hS A₂)
  {D₀ : QuotientSystem B S hS A₀} (hA₀ : TopologicalRing.IsWeaklyAdmissible A₀)
  (φ₁ : ContinuousHom D₀ D₁) (φ₂ : ContinuousHom D₀ D₂)
  (hφ₁ : φ₁.toRingHom = algebraMap A₀ A₁) (hφ₂ : φ₂.toRingHom = algebraMap A₀ A₂)

/-- The map from the fibre product over `Spf A₀` of the stages `Spec (A₁/I)` and `Spec (A₂/J)`
to `Spf (A₁ ⊗̂_{A₀} A₂)`: the fibre product is `Spec (A₁/I ⊗_{A₀} A₂/J)`, which maps to the stage
`Spec (T/L)` for `L = completedTensorStageIdeal A₀ hA₁ hA₂ I J`. -/
def completedTensorLeg
    (I : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I })
    (J : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J }) :
    pullback (formalSpectrumInclusion D₁ (OrderDual.toDual I) ≫ formalSpectrumMap hA₀ φ₁)
        (formalSpectrumInclusion D₂ (OrderDual.toDual J) ≫ formalSpectrumMap hA₀ φ₂) ⟶
      formalSpectrum (completedTensorQuotientSystem A₀ hA₁ hA₂ D₁ D₂) :=
  (isPullback_completedTensorStage_formalSpectrum A₀ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J).isoPullback.inv ≫
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
      (completedTensorStageToQuotient A₀ hA₁ hA₂ D₁ D₂ I J) ≫
    formalSpectrumInclusion _ (OrderDual.toDual (completedTensorStageIdeal A₀ hA₁ hA₂ I J))

/-- The maps `completedTensorLeg` are compatible with the transitions between the fibre
products of stages. -/
theorem completedTensorLeg_comp
    {I I' : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I }}
    {J J' : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J }}
    (hI : I'.1 ≤ I.1) (hJ : J'.1 ≤ J.1)
    (d : pullback (formalSpectrumInclusion D₁ (OrderDual.toDual I) ≫ formalSpectrumMap hA₀ φ₁)
        (formalSpectrumInclusion D₂ (OrderDual.toDual J) ≫ formalSpectrumMap hA₀ φ₂) ⟶
      pullback (formalSpectrumInclusion D₁ (OrderDual.toDual I') ≫ formalSpectrumMap hA₀ φ₁)
        (formalSpectrumInclusion D₂ (OrderDual.toDual J') ≫ formalSpectrumMap hA₀ φ₂))
    (h₁ : d ≫ pullback.fst _ _ = pullback.fst _ _ ≫
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (D₁.transition hI)))
    (h₂ : d ≫ pullback.snd _ _ = pullback.snd _ _ ≫
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (D₂.transition hJ))) :
    d ≫ completedTensorLeg A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I' J' =
      completedTensorLeg A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J := by
  let Yo := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  have sq := isPullback_completedTensorStage_formalSpectrum A₀ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J
  have sq' := isPullback_completedTensorStage_formalSpectrum A₀ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I' J'
  let m := completedTensorStageToQuotient A₀ hA₁ hA₂ D₁ D₂ I J
  let m' := completedTensorStageToQuotient A₀ hA₁ hA₂ D₁ D₂ I' J'
  let ι' := formalSpectrumInclusion (completedTensorQuotientSystem A₀ hA₁ hA₂ D₁ D₂)
    (OrderDual.toDual (completedTensorStageIdeal A₀ hA₁ hA₂ I' J'))
  have e3 := congrArg Yo.map (completedTensorStageTransition_fst A₀ D₁ D₂ hI hJ)
  have e3' := congrArg Yo.map
    (completedTensorStageTransition_snd A₀ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ hI hJ)
  have e4 := congrArg Yo.map (completedTensorStageTransition_toQuotient A₀ hA₁ hA₂ D₁ D₂ hI hJ)
  rw [Functor.map_comp, Functor.map_comp] at e3 e3' e4
  have key : d ≫ sq'.isoPullback.inv =
      sq.isoPullback.inv ≫ Yo.map (completedTensorStageTransition A₀ D₁ D₂ hI hJ) := by
    refine sq'.hom_ext ?_ ?_
    · exact comp_comp_eq_comp_comp_of_factor sq'.isoPullback_inv_fst h₁ e3 sq.isoPullback_inv_fst
    · exact comp_comp_eq_comp_comp_of_factor sq'.isoPullback_inv_snd h₂ e3' sq.isoPullback_inv_snd
  have hw := colimit.w (formalSpectrumDiagram (completedTensorQuotientSystem A₀ hA₁ hA₂ D₁ D₂))
    (homOfLE (show OrderDual.toDual (completedTensorStageIdeal A₀ hA₁ hA₂ I J) ≤
      OrderDual.toDual (completedTensorStageIdeal A₀ hA₁ hA₂ I' J') from
      completedTensorStageIdeal_mono A₀ hA₁ hA₂ hI hJ))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ Yo.map m' ≫ ι') key).trans
    ((comp_comp_comp_reassoc _ _ _ _).trans ((congrArg (fun k ↦ sq.isoPullback.inv ≫ k ≫ ι')
      e4).trans ((congrArg (sq.isoPullback.inv ≫ ·) (Category.assoc _ _ _)).trans
        (congrArg (fun k ↦ sq.isoPullback.inv ≫ Yo.map m ≫ k) hw)))))

/-- The cocone with vertex `Spf (A₁ ⊗̂_{A₀} A₂)` on the diagram of fibre products over `Spf A₀`
of the stages of `Spf A₁` and `Spf A₂`. -/
def completedTensorCocone :
    Cocone (Functor.uncurry.obj (relativeProductDiagram
      (colimit.cocone (formalSpectrumDiagram D₁)) (colimit.cocone (formalSpectrumDiagram D₂))
      (formalSpectrumMap hA₀ φ₁) (formalSpectrumMap hA₀ φ₂))) where
  pt := formalSpectrum (completedTensorQuotientSystem A₀ hA₁ hA₂ D₁ D₂)
  ι :=
    { app := fun p ↦ completedTensorLeg A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂
        (OrderDual.ofDual p.1) (OrderDual.ofDual p.2)
      naturality := fun _ _ f ↦
        (completedTensorLeg_comp A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂
          (leOfHom f.1) (leOfHom f.2) _
          (uncurry_relativeProductDiagram_map_fst _ _ _ _ f)
          (uncurry_relativeProductDiagram_map_snd _ _ _ _ f)).trans (Category.comp_id _).symm }

/-- The map `Spf A₁ ×_{Spf A₀} Spf A₂ ⟶ Spf (A₁ ⊗̂_{A₀} A₂)` out of the colimit of the fibre
products of the stages. -/
def completedTensorPullbackInv :
    pullback (formalSpectrumMap hA₀ φ₁) (formalSpectrumMap hA₀ φ₂) ⟶
      formalSpectrum (completedTensorQuotientSystem A₀ hA₁ hA₂ D₁ D₂) :=
  (isColimit_relativeProductCocone _ _ _ _ (isUniversalColimit_formalSpectrumDiagram hA₁.1 D₁)
    (isUniversalColimit_formalSpectrumDiagram hA₂.1 D₂)).desc
      (completedTensorCocone A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂)

/-- On the fibre product of the stages `Spec (A₁/I)` and `Spec (A₂/J)`, the map
`completedTensorPullbackInv` restricts to `completedTensorLeg`. -/
theorem relativeProductLeg_completedTensorPullbackInv
    (I : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I })
    (J : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J }) :
    relativeProductLeg (colimit.cocone (formalSpectrumDiagram D₁))
        (colimit.cocone (formalSpectrumDiagram D₂)) (formalSpectrumMap hA₀ φ₁)
        (formalSpectrumMap hA₀ φ₂) (OrderDual.toDual I) (OrderDual.toDual J) ≫
      completedTensorPullbackInv A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ =
    completedTensorLeg A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J :=
  (isColimit_relativeProductCocone _ _ _ _ (isUniversalColimit_formalSpectrumDiagram hA₁.1 D₁)
    (isUniversalColimit_formalSpectrumDiagram hA₂.1 D₂)).fac _
      (OrderDual.toDual I, OrderDual.toDual J)

/-- `completedTensorLeg` followed by `Spf T ⟶ Spf A₁` is the first projection followed by the
inclusion of the stage `Spec (A₁/I)`. -/
theorem completedTensorLeg_fst
    (I : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I })
    (J : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J }) :
    completedTensorLeg A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J ≫
        formalSpectrumMap hA₁ (completedTensorLeftHom A₀ hA₁ hA₂ D₁ D₂) =
      pullback.fst _ _ ≫ formalSpectrumInclusion D₁ (OrderDual.toDual I) := by
  let Yo := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let L := completedTensorStageIdeal A₀ hA₁ hA₂ I J
  let M : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I } :=
    ⟨I.1 ⊓ L.1.comap (completedTensorLeft A₀ A₁ A₂),
      TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right I.2
        (L.2.1.preimage (continuous_completedTensorLeft A₀ A₁ A₂))⟩
  have sq := isPullback_completedTensorStage_formalSpectrum A₀ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J
  have hs := formalSpectrumMap_spec hA₁ (completedTensorLeftHom A₀ hA₁ hA₂ D₁ D₂) M L inf_le_right
  have hst : completedTensorStageToQuotient A₀ hA₁ hA₂ D₁ D₂ I J ≫
      (BigAffineFppf.inclusion B S hS).map
        ((completedTensorLeftHom A₀ hA₁ hA₂ D₁ D₂).stageMap M L inf_le_right) =
      completedTensorStageFst A₀ D₁ D₂ I J ≫
        (BigAffineFppf.inclusion B S hS).map (D₁.transition (inf_le_left : M.1 ≤ I.1)) := by
    refine comp_eq_comp_of_toScheme_map (spec_map_comp_eq _ _ _ _
      (Ideal.Quotient.ringHom_ext (RingHom.ext fun a ↦ ?_)))
    change completedTensorStageQuotientMap A₀ hA₁ hA₂ I J
      (Ideal.Quotient.mk _ (completedTensorLeft A₀ A₁ A₂ a)) = _
    rw [completedTensorStageQuotientMap_mk, completedTensorStageRingHom_left]
    rfl
  have hw := colimit.w (formalSpectrumDiagram D₁)
    (homOfLE (show OrderDual.toDual I ≤ OrderDual.toDual M from (inf_le_left : M.1 ≤ I.1)))
  have e := congrArg Yo.map hst
  rw [Functor.map_comp, Functor.map_comp] at e
  exact comp_comp_comp_eq_of_factor hs e hw sq.isoPullback_inv_fst

/-- `completedTensorLeg` followed by `Spf T ⟶ Spf A₂` is the second projection followed by the
inclusion of the stage `Spec (A₂/J)`. -/
theorem completedTensorLeg_snd
    (I : { I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I })
    (J : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J }) :
    completedTensorLeg A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J ≫
        formalSpectrumMap hA₂ (completedTensorRightHom A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂) =
      pullback.snd _ _ ≫ formalSpectrumInclusion D₂ (OrderDual.toDual J) := by
  let Yo := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let L := completedTensorStageIdeal A₀ hA₁ hA₂ I J
  let M : { J : Ideal A₂ // TopologicalRing.IsWeakIdealOfDefinition J } :=
    ⟨J.1 ⊓ L.1.comap (completedTensorRight A₀ A₁ A₂),
      TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right J.2
        (L.2.1.preimage (continuous_completedTensorRight A₀ A₁ A₂))⟩
  have sq := isPullback_completedTensorStage_formalSpectrum A₀ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J
  have hs := formalSpectrumMap_spec hA₂
    (completedTensorRightHom A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂) M L inf_le_right
  have hst : completedTensorStageToQuotient A₀ hA₁ hA₂ D₁ D₂ I J ≫
      (BigAffineFppf.inclusion B S hS).map
        ((completedTensorRightHom A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂).stageMap M L
          inf_le_right) =
      completedTensorStageSnd A₀ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J ≫
        (BigAffineFppf.inclusion B S hS).map (D₂.transition (inf_le_left : M.1 ≤ J.1)) := by
    refine comp_eq_comp_of_toScheme_map (spec_map_comp_eq _ _ _ _
      (Ideal.Quotient.ringHom_ext (RingHom.ext fun c ↦ ?_)))
    change completedTensorStageQuotientMap A₀ hA₁ hA₂ I J
      (Ideal.Quotient.mk _ (completedTensorRight A₀ A₁ A₂ c)) = _
    rw [completedTensorStageQuotientMap_mk, completedTensorStageRingHom_right]
    rfl
  have hw := colimit.w (formalSpectrumDiagram D₂)
    (homOfLE (show OrderDual.toDual J ≤ OrderDual.toDual M from (inf_le_left : M.1 ≤ J.1)))
  have e := congrArg Yo.map hst
  rw [Functor.map_comp, Functor.map_comp] at e
  exact comp_comp_comp_eq_of_factor hs e hw sq.isoPullback_inv_snd

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The stage `Spec (T/L)` of `Spf T` maps to `Spf A₁` through `Spec (A₁/I ⊗_{A₀} A₂/J)` and
`Spec (A₁/I)`, for `I` and `J` the ideals attached to `L`. -/
theorem formalSpectrumInclusion_completedTensorLeft
    (L : { L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) //
      TopologicalRing.IsWeakIdealOfDefinition L }) :
    formalSpectrumInclusion (completedTensorQuotientSystem A₀ hA₁ hA₂ D₁ D₂) (OrderDual.toDual L) ≫
        formalSpectrumMap hA₁ (completedTensorLeftHom A₀ hA₁ hA₂ D₁ D₂) =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          (completedTensorQuotientToStage A₀ hA₁ hA₂ D₁ D₂ L ≫
            completedTensorStageFst A₀ D₁ D₂ _ _) ≫
        formalSpectrumInclusion D₁ (OrderDual.toDual (completedTensorLeftIdeal A₀ hA₁ L)) := by
  have hs := formalSpectrumMap_spec hA₁ (completedTensorLeftHom A₀ hA₁ hA₂ D₁ D₂)
    (completedTensorLeftIdeal A₀ hA₁ L) L (completedTensorLeftIdeal_le A₀ hA₁ L)
  rwa [← completedTensorQuotientToStage_fst] at hs

/-- The stage `Spec (T/L)` of `Spf T` maps to `Spf A₂` through `Spec (A₁/I ⊗_{A₀} A₂/J)` and
`Spec (A₂/J)`, for `I` and `J` the ideals attached to `L`. -/
theorem formalSpectrumInclusion_completedTensorRight
    (L : { L : Ideal (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) //
      TopologicalRing.IsWeakIdealOfDefinition L }) :
    formalSpectrumInclusion (completedTensorQuotientSystem A₀ hA₁ hA₂ D₁ D₂) (OrderDual.toDual L) ≫
        formalSpectrumMap hA₂ (completedTensorRightHom A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂) =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
          (completedTensorQuotientToStage A₀ hA₁ hA₂ D₁ D₂ L ≫
            completedTensorStageSnd A₀ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ _ _) ≫
        formalSpectrumInclusion D₂ (OrderDual.toDual (completedTensorRightIdeal A₀ hA₂ L)) := by
  have hs := formalSpectrumMap_spec hA₂
    (completedTensorRightHom A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂)
    (completedTensorRightIdeal A₀ hA₂ L) L (completedTensorRightIdeal_le A₀ hA₂ L)
  rwa [← completedTensorQuotientToStage_snd] at hs

/-- The square `Spf T ⟶ Spf A₁, Spf T ⟶ Spf A₂` over `Spf A₀` commutes. -/
theorem formalSpectrumMap_completedTensor_comm :
    formalSpectrumMap hA₁ (completedTensorLeftHom A₀ hA₁ hA₂ D₁ D₂) ≫ formalSpectrumMap hA₀ φ₁ =
      formalSpectrumMap hA₂ (completedTensorRightHom A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂) ≫
        formalSpectrumMap hA₀ φ₂ := by
  refine colimit.hom_ext fun l ↦ ?_
  let Yo := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let L := OrderDual.ofDual l
  have h₁ := formalSpectrumInclusion_completedTensorLeft A₀ hA₁ hA₂ D₁ D₂ L
  have h₂ := formalSpectrumInclusion_completedTensorRight A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ L
  have hsq := (isPullback_completedTensorStage_formalSpectrum A₀ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂
    (completedTensorLeftIdeal A₀ hA₁ L) (completedTensorRightIdeal A₀ hA₂ L)).w
  have e₁ := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ formalSpectrumMap hA₀ φ₁) h₁).trans
    ((congrArg (fun k ↦ (k ≫ formalSpectrumInclusion D₁
      (OrderDual.toDual (completedTensorLeftIdeal A₀ hA₁ L))) ≫ formalSpectrumMap hA₀ φ₁)
        (Yo.map_comp _ _)).trans (comp_comp_comp_assoc _ _ _ _)))
  have e₂ := (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ formalSpectrumMap hA₀ φ₂) h₂).trans
    ((congrArg (fun k ↦ (k ≫ formalSpectrumInclusion D₂
      (OrderDual.toDual (completedTensorRightIdeal A₀ hA₂ L))) ≫ formalSpectrumMap hA₀ φ₂)
        (Yo.map_comp _ _)).trans (comp_comp_comp_assoc _ _ _ _)))
  exact e₁.trans ((congrArg (Yo.map (completedTensorQuotientToStage A₀ hA₁ hA₂ D₁ D₂ L) ≫ ·)
    hsq).trans e₂.symm)

/-- `completedTensorPullbackInv` followed by the map
`Spf (A₁ ⊗̂_{A₀} A₂) ⟶ Spf A₁ ×_{Spf A₀} Spf A₂` is the identity. -/
theorem completedTensorPullbackInv_lift :
    completedTensorPullbackInv A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ ≫
        pullback.lift _ _
          (formalSpectrumMap_completedTensor_comm A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂) =
      𝟙 _ := by
  refine (isColimit_relativeProductCocone _ _ _ _
    (isUniversalColimit_formalSpectrumDiagram hA₁.1 D₁)
    (isUniversalColimit_formalSpectrumDiagram hA₂.1 D₂)).hom_ext fun ij ↦ ?_
  let I := OrderDual.ofDual ij.1
  let J := OrderDual.ofDual ij.2
  have hfac := relativeProductLeg_completedTensorPullbackInv A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J
  let leg := completedTensorLeg A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J
  refine (Category.assoc _ _ _).symm.trans (((congrArg (· ≫ pullback.lift _ _
    (formalSpectrumMap_completedTensor_comm A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂)) hfac).trans
      ?_).trans (Category.comp_id _).symm)
  refine pullback.hom_ext ?_ ?_
  · exact (Category.assoc _ _ _).trans ((congrArg (leg ≫ ·) (pullback.lift_fst _ _ _)).trans
      ((completedTensorLeg_fst A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J).trans
        (relativeProductLeg_fst _ _ _ _ _ _).symm))
  · exact (Category.assoc _ _ _).trans ((congrArg (leg ≫ ·) (pullback.lift_snd _ _ _)).trans
      ((completedTensorLeg_snd A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J).trans
        (relativeProductLeg_snd _ _ _ _ _ _).symm))

/-- The map `Spf (A₁ ⊗̂_{A₀} A₂) ⟶ Spf A₁ ×_{Spf A₀} Spf A₂` followed by
`completedTensorPullbackInv` is the identity. -/
theorem lift_completedTensorPullbackInv :
    pullback.lift _ _ (formalSpectrumMap_completedTensor_comm A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂) ≫
        completedTensorPullbackInv A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ = 𝟙 _ := by
  refine colimit.hom_ext fun l ↦ ?_
  let Yo := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let L := OrderDual.ofDual l
  let I := completedTensorLeftIdeal A₀ hA₁ L
  let J := completedTensorRightIdeal A₀ hA₂ L
  have sq := isPullback_completedTensorStage_formalSpectrum A₀ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J
  have hLL : (completedTensorStageIdeal A₀ hA₁ hA₂ I J).1 ≤ L.1 :=
    (completedTensorStageIdeal_le_ker A₀ hA₁ hA₂ I J).trans
      (ker_completedTensorStageRingHom_le_of_ideal A₀ hA₁ hA₂ L)
  have kf : sq.isoPullback.hom ≫ pullback.fst
      ((colimit.cocone (formalSpectrumDiagram D₁)).ι.app (OrderDual.toDual I) ≫
        formalSpectrumMap hA₀ φ₁)
      ((colimit.cocone (formalSpectrumDiagram D₂)).ι.app (OrderDual.toDual J) ≫
        formalSpectrumMap hA₀ φ₂) = Yo.map (completedTensorStageFst A₀ D₁ D₂ I J) :=
    sq.isoPullback_hom_fst
  have ks : sq.isoPullback.hom ≫ pullback.snd
      ((colimit.cocone (formalSpectrumDiagram D₁)).ι.app (OrderDual.toDual I) ≫
        formalSpectrumMap hA₀ φ₁)
      ((colimit.cocone (formalSpectrumDiagram D₂)).ι.app (OrderDual.toDual J) ≫
        formalSpectrumMap hA₀ φ₂) =
      Yo.map (completedTensorStageSnd A₀ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I J) :=
    sq.isoPullback_hom_snd
  have e1 : colimit.ι _ l ≫ pullback.lift _ _
      (formalSpectrumMap_completedTensor_comm A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂) =
      (Yo.map (completedTensorQuotientToStage A₀ hA₁ hA₂ D₁ D₂ L) ≫ sq.isoPullback.hom) ≫
        relativeProductLeg (colimit.cocone (formalSpectrumDiagram D₁))
          (colimit.cocone (formalSpectrumDiagram D₂)) (formalSpectrumMap hA₀ φ₁)
          (formalSpectrumMap hA₀ φ₂) (OrderDual.toDual I) (OrderDual.toDual J) := by
    refine pullback.hom_ext ?_ ?_
    · exact comp_lift_comp_eq_of_factor (pullback.lift_fst _ _ _)
        (formalSpectrumInclusion_completedTensorLeft A₀ hA₁ hA₂ D₁ D₂ L) (Yo.map_comp _ _)
        (relativeProductLeg_fst _ _ _ _ _ _) kf
    · exact comp_lift_comp_eq_of_factor (pullback.lift_snd _ _ _)
        (formalSpectrumInclusion_completedTensorRight A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ L)
        (Yo.map_comp _ _) (relativeProductLeg_snd _ _ _ _ _ _) ks
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ completedTensorPullbackInv A₀ hA₁ hA₂ D₁
    D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂) e1).trans ((Category.assoc _ _ _).trans
      ((congrArg ((Yo.map (completedTensorQuotientToStage A₀ hA₁ hA₂ D₁ D₂ L) ≫
        sq.isoPullback.hom) ≫ ·)
        (relativeProductLeg_completedTensorPullbackInv A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ I
          J)).trans
        ((comp_hom_inv_comp _ _ _).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ formalSpectrumInclusion (completedTensorQuotientSystem A₀ hA₁ hA₂ D₁ D₂)
            (OrderDual.toDual (completedTensorStageIdeal A₀ hA₁ hA₂ I J)))
            ((Yo.map_comp _ _).symm.trans (congrArg Yo.map
              (completedTensorQuotientToStage_toQuotient A₀ hA₁ hA₂ D₁ D₂ L hLL)))).trans
            ((colimit.w (formalSpectrumDiagram (completedTensorQuotientSystem A₀ hA₁ hA₂ D₁ D₂))
              (homOfLE (show l ≤ OrderDual.toDual (completedTensorStageIdeal A₀ hA₁ hA₂ I J)
                from hLL))).trans (Category.comp_id _).symm)))))))

/-- Let `A₀ → A₁` and `A₀ → A₂` be continuous homomorphisms of
weakly admissible topological rings over `S`. Then the completed tensor product
`T = A₁ ⊗̂_{A₀} A₂` is weakly admissible and `Spf T`, with the maps induced by the canonical
continuous homomorphisms `A₁ → T` and `A₂ → T`, is the fibre product
`Spf A₁ ×_{Spf A₀} Spf A₂`. -/
@[stacks 0AN3 "clause (3): Spf A ×_{Spf C} Spf B corresponds to the completed tensor product"]
theorem isPullback_formalSpectrumMap_completedTensor :
    TopologicalRing.IsWeaklyAdmissible
        (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A₂)) ∧
      IsPullback (formalSpectrumMap hA₁ (completedTensorLeftHom A₀ hA₁ hA₂ D₁ D₂))
        (formalSpectrumMap hA₂ (completedTensorRightHom A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂))
        (formalSpectrumMap hA₀ φ₁) (formalSpectrumMap hA₀ φ₂) :=
  ⟨TopologicalRing.completedTensorProduct_isWeaklyAdmissible (B := A₀) hA₁.1 hA₂.1,
    IsPullback.of_iso_pullback
      ⟨formalSpectrumMap_completedTensor_comm A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂⟩
      { hom := pullback.lift _ _
          (formalSpectrumMap_completedTensor_comm A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂)
        inv := completedTensorPullbackInv A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂
        hom_inv_id := lift_completedTensorPullbackInv A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂
        inv_hom_id := completedTensorPullbackInv_lift A₀ hA₁ hA₂ D₁ D₂ hA₀ φ₁ φ₂ hφ₁ hφ₂ }
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)⟩

end Main

end AlgebraicGeometry.FormalSpace

end
