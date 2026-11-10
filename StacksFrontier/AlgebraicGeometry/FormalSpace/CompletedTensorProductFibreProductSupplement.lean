module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletedTensorProductFibreProduct
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentationQuotientSystem
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedFibreProduct
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SurjectivePresentationRing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleChartLocality

/-!
# Fibre products of McQuillan affine formal algebraic spaces with compatibilities

Let `X ⟶ Z` and `Y ⟶ Z` be morphisms of McQuillan affine formal algebraic spaces over `S` with
`Z` separated, and let `X = Spf A`, `Y = Spf B`, `Z = Spf C` for weakly admissible topological
rings over `S`. This module shows that `X ×_Z Y = Spf (A ⊗̂_C B)`, compatibly with the two
projections and with the canonical maps of `A` and `B` into the completed tensor product, and
that every such pair of morphisms is induced by continuous ring maps `C → A` and `C → B` over
`S`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.ContinuousHom.ofStages`: the continuous homomorphism over the
  base given by a continuous ring map compatible with the structure morphisms at one weak ideal
  of definition of the source for each weak ideal of definition of the target.
* `AlgebraicGeometry.FormalSpace.ContinuousHom.ofComp'`: a continuous ring map out of the target
  of a continuous homomorphism over the base whose composite with it is one, as a continuous
  homomorphism over the base.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_formalSpectrum_completedTensorProduct_compatible`: the
  fibre product `X ×_Z Y` is the formal spectrum of `A ⊗̂_C B`, compatibly with both
  projections.
* `AlgebraicGeometry.FormalSpace.exists_continuousHom_formalSpectrumMap_eq`: morphisms `X ⟶ Z`
  and `Y ⟶ Z` of formal spectra are induced by continuous ring maps `C → A` and `C → B` over
  `S`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

namespace AlgebraicGeometry.FormalSpace

universe u

/-! ### Site membership of the quotient stages -/

section Site

/-- The spectrum of a quotient of a ring whose spectrum lies in the site lies in the site. -/
private theorem contains_spec_of_surjective (𝔅 : BigFppfSite.{u})
    {R Q : Type u} [CommRing R] [CommRing Q] (φ : R →+* Q) (hφ : Function.Surjective φ)
    (hR : 𝔅.Contains (Spec (.of R))) : 𝔅.Contains (Spec (.of Q)) := by
  have hci : AlgebraicGeometry.IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    AlgebraicGeometry.IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ) hφ
  exact lt_of_le_of_lt
    (Scheme.size_le_of_mono_quasiCompact (Spec.map (CommRingCat.ofHom φ))) hR

/-- The spectrum of a tensor product of two rings whose spectra lie in the site lies in the
site. -/
private theorem contains_spec_tensorProduct (𝔅 : BigFppfSite.{u})
    {R A C : Type u} [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
    (hA : 𝔅.Contains (Spec (.of A))) (hC : 𝔅.Contains (Spec (.of C))) :
    𝔅.Contains (Spec (.of (A ⊗[R] C))) := by
  change (Spec (.of (A ⊗[R] C))).size < 𝔅.cutoff
  rw [← Scheme.size_congr (AlgebraicGeometry.pullbackSpecIso R A C)]
  exact Scheme.size_pullback_lt _ _ hA hC

end Site

/-! ### Surjections onto a quotient of a completion -/

section Completion

/-- Every element of the quotient of a completion by an open ideal is the class of an element of
the original ring. -/
private theorem surjective_quotientMk_coe {R : Type u} [CommRing R] [UniformSpace R]
    [IsUniformAddGroup R] [IsTopologicalRing R] [IsLinearTopology R R]
    {I : Ideal (UniformSpace.Completion R)}
    (hI : IsOpen (I : Set (UniformSpace.Completion R))) :
    Function.Surjective
      (fun r : R => Ideal.Quotient.mk I (r : UniformSpace.Completion R)) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hU : {z : UniformSpace.Completion R | z - x ∈ I} ∈ nhds x := by
    change (fun z : UniformSpace.Completion R => z - x) ⁻¹' (I : Set _) ∈ nhds x
    exact (continuous_id.sub continuous_const).continuousAt.preimage_mem_nhds
      (by simpa using hI.mem_nhds (Ideal.zero_mem I))
  obtain ⟨r, hr⟩ := (UniformSpace.Completion.denseRange_coe (α := R)).mem_nhds hU
  exact ⟨r, Ideal.Quotient.eq.mpr hr⟩

end Completion

/-! ### Factoring a lift through a tensor product of quotients -/

section TensorQuotient

variable {R A C : Type u} [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]

/-- The canonical image of an element of an ideal of the first factor lies in the submodule
cutting out the tensor product topology. -/
private theorem tensorProductSubmodule_includeLeft_mem {I : Ideal A} {J : Ideal C} {a : A}
    (ha : a ∈ I) :
    (Algebra.TensorProduct.includeLeft (R := R) (S := R) (B := C) a : A ⊗[R] C) ∈
      TopologicalRing.tensorProductSubmodule (I.restrictScalars R) (J.restrictScalars R) := by
  change (Algebra.TensorProduct.includeLeft (R := R) (S := R) a : A ⊗[R] C) ∈
    LinearMap.range (TensorProduct.map (I.restrictScalars R).subtype
      (LinearMap.id : C →ₗ[R] C)) ⊔ _
  refine Submodule.mem_sup.mpr ⟨TensorProduct.map (I.restrictScalars R).subtype
      (LinearMap.id : C →ₗ[R] C) ((⟨a, ha⟩ : I.restrictScalars R) ⊗ₜ[R] (1 : C)),
    ⟨_, rfl⟩, 0, ⟨0, by simp⟩, ?_⟩
  simp [Algebra.TensorProduct.includeLeft_apply]

/-- The canonical image of an element of an ideal of the second factor lies in the submodule
cutting out the tensor product topology. -/
private theorem tensorProductSubmodule_includeRight_mem {I : Ideal A} {J : Ideal C} {c : C}
    (hc : c ∈ J) :
    (Algebra.TensorProduct.includeRight (R := R) (A := A) c : A ⊗[R] C) ∈
      TopologicalRing.tensorProductSubmodule (I.restrictScalars R) (J.restrictScalars R) := by
  change (Algebra.TensorProduct.includeRight c : A ⊗[R] C) ∈
    _ ⊔ LinearMap.range (TensorProduct.map (LinearMap.id : A →ₗ[R] A)
      (J.restrictScalars R).subtype)
  refine Submodule.mem_sup.mpr ⟨0, ⟨0, by simp⟩,
    TensorProduct.map (LinearMap.id : A →ₗ[R] A) (J.restrictScalars R).subtype
      ((1 : A) ⊗ₜ[R] (⟨c, hc⟩ : J.restrictScalars R)), ⟨_, rfl⟩, ?_⟩
  simp [Algebra.TensorProduct.includeRight_apply]

/-- A pair of algebra maps killing two ideals factors through the tensor product of the two
quotients, surjectively if their lift is surjective. -/
private theorem exists_tensorQuotientAlgHom {Q : Type u} [CommRing Q] [Algebra R Q]
    {I : Ideal A} {J : Ideal C} (f : A →ₐ[R] Q) (g : C →ₐ[R] Q)
    (hI : ∀ a ∈ I, f a = 0) (hJ : ∀ c ∈ J, g c = 0)
    (hψ : Function.Surjective
      (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _))) :
    ∃ φ : (A ⧸ I) ⊗[R] (C ⧸ J) →ₐ[R] Q,
      φ.comp (Algebra.TensorProduct.map
          (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R J)) =
        Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) ∧
      Function.Surjective φ := by
  let q := Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R J)
  let ψ := Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)
  have hmkI : Function.Surjective (Ideal.Quotient.mkₐ R I) := Ideal.Quotient.mkₐ_surjective R I
  have hmkJ : Function.Surjective (Ideal.Quotient.mkₐ R J) := Ideal.Quotient.mkₐ_surjective R J
  have hq : Function.Surjective q :=
    Algebra.TensorProduct.map_surjective (f := Ideal.Quotient.mkₐ R I)
      (g := Ideal.Quotient.mkₐ R J) hmkI hmkJ
  have hker : RingHom.ker q.toRingHom ≤ RingHom.ker ψ.toRingHom := by
    change RingHom.ker (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I)
      (Ideal.Quotient.mkₐ R J)) ≤ RingHom.ker ψ
    have hkerI : RingHom.ker (Ideal.Quotient.mkₐ R I) = I := by
      ext a; exact Ideal.Quotient.eq_zero_iff_mem
    have hkerJ : RingHom.ker (Ideal.Quotient.mkₐ R J) = J := by
      ext c; exact Ideal.Quotient.eq_zero_iff_mem
    rw [Algebra.TensorProduct.map_ker (f := Ideal.Quotient.mkₐ R I)
      (g := Ideal.Quotient.mkₐ R J) hmkI hmkJ, hkerI, hkerJ]
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      change ψ (Algebra.TensorProduct.includeLeft a) = 0
      calc ψ (Algebra.TensorProduct.includeLeft a)
          = f a := congrArg (fun k : A →ₐ[R] Q => k a)
            (Algebra.TensorProduct.lift_comp_includeLeft f g (fun _ _ => Commute.all _ _))
        _ = 0 := hI a ha
    · rw [Ideal.map_le_iff_le_comap]
      intro c hc
      change ψ (Algebra.TensorProduct.includeRight c) = 0
      calc ψ (Algebra.TensorProduct.includeRight c)
          = g c := congrArg (fun k : C →ₐ[R] Q => k c)
            (Algebra.TensorProduct.lift_comp_includeRight' f g (fun _ _ => Commute.all _ _))
        _ = 0 := hJ c hc
  exact ⟨AlgHom.liftOfSurjective q hq ψ hker, AlgHom.liftOfSurjective_comp q hq ψ hker,
    AlgHom.liftOfSurjective_surjective q hq ψ hker hψ⟩

/-- A ring map out of a tensor product sends the submodule cutting out the tensor product
topology into an ideal as soon as it sends `a ⊗ 1` and `1 ⊗ c` into it for `a`, `c` in the two
factors. -/
private theorem map_tensorProductSubmodule_mem {Q : Type u} [CommRing Q]
    {P : Submodule R A} {O : Submodule R C} (ψ : A ⊗[R] C →+* Q)
    (K : Ideal Q) (hP : ∀ a ∈ P, ψ (a ⊗ₜ[R] 1) ∈ K)
    (hO : ∀ c ∈ O, ψ (1 ⊗ₜ[R] c) ∈ K) :
    ∀ z ∈ TopologicalRing.tensorProductSubmodule P O, ψ z ∈ K := by
  have hmul (a : A) (c : C) : ψ (a ⊗ₜ[R] c) = ψ (a ⊗ₜ[R] 1) * ψ (1 ⊗ₜ[R] c) := by
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
  clear hz
  refine (map_add ψ x y) ▸ K.add_mem ?_ ?_
  · obtain ⟨w, rfl⟩ := hx
    induction w using TensorProduct.inductionOn with
    | tmul a c => exact hmul a c ▸ K.mul_mem_right _ (hP a a.2)
    | add x y hx hy => simpa only [map_add] using K.add_mem hx hy
  · obtain ⟨w, rfl⟩ := hy
    induction w using TensorProduct.inductionOn with
    | tmul a c => exact hmul a c ▸ K.mul_mem_left _ (hO c c.2)
    | add x y hx hy => simpa only [map_add] using K.add_mem hx hy

end TensorQuotient

/-! ### Continuity of a lift out of a tensor product -/

section Lift

open Filter

variable {R A C Q : Type u} [CommRing R] [CommRing A] [CommRing C] [CommRing Q]
  [Algebra R A] [Algebra R C] [Algebra R Q]

/-- The lift of two algebra maps out of the tensor product sends the submodule cut out by the
preimages of an ideal into that ideal. -/
private theorem lift_tensorProductSubmodule_le (f : A →ₐ[R] Q) (g : C →ₐ[R] Q) (K : Ideal Q) :
    ∀ z ∈ TopologicalRing.tensorProductSubmodule
        ((Ideal.comap f.toRingHom K).restrictScalars R)
        ((Ideal.comap g.toRingHom K).restrictScalars R),
      Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) z ∈ K :=
  map_tensorProductSubmodule_mem
    (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom K
    (fun a ha => by simpa using ha) (fun c hc => by simpa using hc)

/-- A pair of continuous algebra maps into a linearly topologized algebra lifts to a continuous
map out of the tensor product with its tensor product topology. -/
@[ega "0 7.7.6"]
private theorem continuous_tensorProduct_lift
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    [TopologicalSpace Q] [IsTopologicalRing Q] [IsLinearTopology Q Q]
    (f : A →ₐ[R] Q) (g : C →ₐ[R] Q) (hf : Continuous f) (hg : Continuous g) :
    letI := TopologicalRing.tensorProductTopology (R := R) (M := A) (N := C)
    Continuous (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)) := by
  let := TopologicalRing.tensorProductTopology (R := R) (M := A) (N := C)
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero]
  exact (TopologicalRing.hasBasis_tensorProductTopology (R := R) (M := A) (N := C)).tendsto_iff
      IsLinearTopology.hasBasis_open_ideal |>.mpr fun K hK ↦
    ⟨(⟨(Ideal.comap f.toRingHom K).restrictScalars R, hK.preimage hf⟩,
      ⟨(Ideal.comap g.toRingHom K).restrictScalars R, hK.preimage hg⟩), trivial,
    lift_tensorProductSubmodule_le f g K⟩

end Lift

/-! ### Two constructions of continuous homomorphisms over the base -/

section ContinuousHoms

variable {𝔅 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝔅.Contains S}
  {A C T : Type u} [CommRing A] [TopologicalSpace A] [CommRing C] [TopologicalSpace C]
  [CommRing T] [TopologicalSpace T]

/-- The continuous homomorphism over the base given by a continuous ring map compatible with the
structure morphisms at one weak ideal of definition of the source for each weak ideal of
definition of the target. -/
def ContinuousHom.ofStages (D : QuotientSystem 𝔅 S hS A) (E : QuotientSystem 𝔅 S hS C)
    (f : A →+* C) (hf : Continuous f)
    (H : ∀ K : { I : Ideal C // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ (J : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
        (h : J.1 ≤ Ideal.comap f K.1),
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 f h)) ≫ D.overS J = E.overS K) :
    ContinuousHom D E where
  toRingHom := f
  continuous := hf
  overS J K h := by
    obtain ⟨J', h', e⟩ := H K
    let L : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
      ⟨J.1 ⊓ J'.1, TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right J.2 J'.2.1⟩
    have hcompL : ∀ (M : { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I })
        (hLM : L.1 ≤ M.1) (hM : M.1 ≤ Ideal.comap f K.1),
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 f hM)) ≫ D.overS M =
          Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 f (hLM.trans hM))) ≫
            D.overS L := by
      intro M hLM hM
      have hfac : (Ideal.quotientMap K.1 f hM).comp (Ideal.Quotient.factor hLM) =
          Ideal.quotientMap K.1 f (hLM.trans hM) := by
        refine Ideal.Quotient.ringHom_ext ?_
        ext a
        rfl
      rw [← D.compatible L M hLM, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        hfac]
    rw [hcompL J inf_le_left h, ← e, hcompL J' inf_le_right h']

variable [IsTopologicalRing A] [IsLinearTopology A A]

/-- A continuous ring map out of the target of a continuous homomorphism over the base, as a
continuous homomorphism over the base, given that its composite with that homomorphism is
one. -/
def ContinuousHom.ofComp' {D : QuotientSystem 𝔅 S hS A} {E : QuotientSystem 𝔅 S hS C}
    {F : QuotientSystem 𝔅 S hS T} (hA : TopologicalRing.IsWeaklyAdmissible A)
    (g : ContinuousHom D E) (fg : ContinuousHom D F) (f : C →+* T) (hf : Continuous f)
    (hfg : fg.toRingHom = f.comp g.toRingHom) : ContinuousHom E F where
  toRingHom := f
  continuous := hf
  overS J K h := by
    obtain ⟨I, hIJ⟩ :=
      exists_isWeakIdealOfDefinition_le_comap hA.1 g.toRingHom g.continuous J
    have hIK : I.1 ≤ Ideal.comap fg.toRingHom K.1 := by
      rw [hfg]
      exact fun x hx => h (hIJ hx)
    have hcomp : (Ideal.quotientMap K.1 f h).comp
        (Ideal.quotientMap J.1 g.toRingHom hIJ) =
        Ideal.quotientMap K.1 fg.toRingHom hIK := by
      refine Ideal.Quotient.ringHom_ext ?_
      ext x
      change Ideal.Quotient.mk K.1 (f (g.toRingHom x)) =
        Ideal.Quotient.mk K.1 (fg.toRingHom x)
      rw [hfg]
      rfl
    rw [← g.overS I J hIJ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      hcomp, fg.overS I K hIK]

variable [IsTopologicalRing C] [IsLinearTopology C C]

/-- A continuous homomorphism of topological rings over the base is determined by its formal
spectrum. -/
private theorem continuousHom_injective_formalSpectrumMap {D : QuotientSystem 𝔅 S hS A}
    {E : QuotientSystem 𝔅 S hS C} (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hC : TopologicalRing.IsWeaklyAdmissible C)
    {u v : ContinuousHom D E} (h : formalSpectrumMap hA u = formalSpectrumMap hA v) : u = v :=
  (existsUnique_continuousHom_formalSpectrumMap_eq hA hC
    (formalSpectrumMap hA v)).unique h rfl

/-- Two continuous homomorphisms over the base out of the same source are equal if their formal
spectra are, the one being the composite of two given ones. -/
private theorem comp_eq_of_formalSpectrumMap_comp_eq [IsTopologicalRing T] [IsLinearTopology T T]
    {D : QuotientSystem 𝔅 S hS A} {E : QuotientSystem 𝔅 S hS C} {F : QuotientSystem 𝔅 S hS T}
    (hA : TopologicalRing.IsWeaklyAdmissible A) (hC : TopologicalRing.IsWeaklyAdmissible C)
    (hT : TopologicalRing.IsWeaklyAdmissible T)
    (w : ContinuousHom D E) (d : ContinuousHom E F) (m : ContinuousHom D F)
    (h : formalSpectrumMap hC d ≫ formalSpectrumMap hA w = formalSpectrumMap hA m) :
    ContinuousHom.comp hC hA d w = m :=
  continuousHom_injective_formalSpectrumMap hA hT
    ((formalSpectrumMap_comp hA hC w d _ rfl).symm.trans h)

end ContinuousHoms

/-! ### Clause (3) -/

section Clause

variable (𝔅 : BigFppfSite.{u}) (S : Scheme.{u}) (hS : 𝔅.Contains S)

attribute [local instance] sheaf_hasColimits

/-- Let `X ⟶ Z` and `Y ⟶ Z` be morphisms of fppf sheaves on the big fppf site of `S` with `Z` a
separated affine formal algebraic space, let `X` and `Y` be McQuillan affine formal algebraic
spaces, and let `X = Spf A`, `Y = Spf B`, `Z = Spf C` for weakly admissible topological rings
`A`, `B`, `C` over `S` with the two morphisms induced by continuous ring maps `C → A` and `C → B`
over `S`. Then

`X ×_Z Y = Spf (A ⊗̂_C B)`,

compatibly with the two projections and with the canonical maps of `A` and of `B` into the
completed tensor product.

The conclusion produces the ring over `S`, that is the
`AlgebraicGeometry.FormalSpace.QuotientSystem` of `A ⊗̂_C B`, together with the two continuous
homomorphisms over `S` out of `A` and `B`, says that those are the canonical maps into the
completion of the algebraic tensor product, and characterises the isomorphism by its
compatibility with both projections of the fibre product. -/
@[stacks 0AN3 "clause (3): the fibre product of two McQuillan affine formal algebraic spaces \
over a separated McQuillan affine formal algebraic space is the formal spectrum of the \
completed tensor product of the three weakly admissible topological rings, compatibly with \
both projections; McQuillanness of the two factors is in the form of condition (2) of Stacks \
0AIC, the form the library's clause (2) consumes"]
theorem exists_formalSpectrum_completedTensorProduct_compatible {X Y Z : FppfSheaf 𝔅 S hS}
    (hX : HasAffineClosedImmersionCriterionMapToSpec 𝔅 S hS X)
    (hY : HasAffineClosedImmersionCriterionMapToSpec 𝔅 S hS Y)
    (hZ : IsAffineFormalAlgebraicSpace 𝔅 S hS Z)
    (hZsep : IsSeparated 𝔅 S hS Z)
    {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    (hC : TopologicalRing.IsWeaklyAdmissible C)
    (DA : QuotientSystem 𝔅 S hS A) (DB : QuotientSystem 𝔅 S hS B)
    (DC : QuotientSystem 𝔅 S hS C)
    (eX : X ≅ formalSpectrum DA) (eY : Y ≅ formalSpectrum DB) (eZ : Z ≅ formalSpectrum DC)
    (f : X ⟶ Z) (g : Y ⟶ Z)
    (cToA : ContinuousHom DC DA) (cToB : ContinuousHom DC DB)
    (hf : formalSpectrumMap hC cToA = eX.inv ≫ f ≫ eZ.hom)
    (hg : formalSpectrumMap hC cToB = eY.inv ≫ g ≫ eZ.hom) :
    letI : Algebra C A := cToA.toRingHom.toAlgebra
    letI : Algebra C B := cToB.toRingHom.toAlgebra
    letI : TopologicalSpace (A ⊗[C] B) :=
      TopologicalRing.tensorProductTopology (R := C) (M := A) (N := B)
    letI : UniformSpace (A ⊗[C] B) :=
      TopologicalRing.tensorProductUniformSpace (R := C) (M := A) (N := B)
    ∃ (DT : QuotientSystem 𝔅 S hS
        (TopologicalRing.CompletedTensorProduct (R := C) (M := A) (N := B)))
      (aToT : ContinuousHom DA DT) (bToT : ContinuousHom DB DT)
      (e : pullback f g ≅ formalSpectrum DT),
      TopologicalRing.IsWeaklyAdmissible
          (TopologicalRing.CompletedTensorProduct (R := C) (M := A) (N := B)) ∧
        aToT.toRingHom = (UniformSpace.Completion.coeRingHom).comp
            (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[C] B) ∧
        bToT.toRingHom = (UniformSpace.Completion.coeRingHom).comp
            ((Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).toRingHom) ∧
        e.hom ≫ formalSpectrumMap hA aToT = pullback.fst f g ≫ eX.hom ∧
        e.hom ≫ formalSpectrumMap hB bToT = pullback.snd f g ≫ eY.hom := by
  classical
  let : Algebra C A := cToA.toRingHom.toAlgebra
  let : Algebra C B := cToB.toRingHom.toAlgebra
  let : TopologicalSpace (A ⊗[C] B) :=
    TopologicalRing.tensorProductTopology (R := C) (M := A) (N := B)
  let : UniformSpace (A ⊗[C] B) :=
    TopologicalRing.tensorProductUniformSpace (R := C) (M := A) (N := B)
  have hTweak : TopologicalRing.IsWeaklyAdmissible
      (TopologicalRing.CompletedTensorProduct (R := C) (M := A) (N := B)) :=
    TopologicalRing.completedTensorProduct_isWeaklyAdmissible
      (B := C) (A := A) (C := B) hA.1 hB.1
  let T := TopologicalRing.CompletedTensorProduct (R := C) (M := A) (N := B)
  let aToT : A →+* T :=
    (UniformSpace.Completion.coeRingHom : (A ⊗[C] B) →+* T).comp
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[C] B)
  let bToT : B →+* T :=
    (UniformSpace.Completion.coeRingHom : (A ⊗[C] B) →+* T).comp
      ((Algebra.TensorProduct.includeRight : B →ₐ[C] A ⊗[C] B).toRingHom)
  have haToTcont : Continuous aToT := by
    change Continuous (fun a : A => ((a ⊗ₜ[C] (1 : B) : A ⊗[C] B) : T))
    exact (UniformSpace.Completion.continuous_coe (A ⊗[C] B)).comp
      (TopologicalRing.continuous_tmul_const (R := C) (M := A) (N := B) (1 : B))
  have hbToTcont : Continuous bToT := by
    change Continuous (fun b : B => (((1 : A) ⊗ₜ[C] b : A ⊗[C] B) : T))
    exact (UniformSpace.Completion.continuous_coe (A ⊗[C] B)).comp
      (TopologicalRing.continuous_const_tmul (R := C) (M := A) (N := B) (1 : A))
  have hbase : aToT.comp (algebraMap C A) = bToT.comp (algebraMap C B) := by
    ext c
    simp [aToT, bToT, Algebra.TensorProduct.algebraMap_apply]
  let cToT := aToT.comp (algebraMap C A)
  let : Algebra C T := cToT.toAlgebra
  let aToTAlg : A →ₐ[C] T := { toRingHom := aToT, commutes' := fun _ => rfl }
  let bToTAlg : B →ₐ[C] T :=
    { toRingHom := bToT
      commutes' := fun c => by
        change bToT (algebraMap C B c) = cToT c
        exact congrArg (fun φ : C →+* T => φ c) hbase.symm }
  let coeT : (A ⊗[C] B) →+* T := UniformSpace.Completion.coeRingHom
  have hmul_include (a : A) (b : B) : aToT a * bToT b = coeT (a ⊗ₜ[C] b) := by
    calc aToT a * bToT b
        = coeT (Algebra.TensorProduct.includeLeft (R := C) (S := C) a) *
            coeT (Algebra.TensorProduct.includeRight (R := C) b) := rfl
      _ = coeT (Algebra.TensorProduct.includeLeft (R := C) (S := C) a *
            Algebra.TensorProduct.includeRight (R := C) b) := (map_mul coeT _ _).symm
      _ = coeT (a ⊗ₜ[C] b) := by
          congr 1
          rw [Algebra.TensorProduct.includeLeft_apply,
            Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul]
          simp
  let coeTAlg : (A ⊗[C] B) →ₐ[C] T :=
    { toRingHom := coeT
      commutes' := fun c => by
        change coeT (algebraMap C (A ⊗[C] B) c) = cToT c
        simp [coeT, aToT, cToT, Algebra.TensorProduct.algebraMap_apply] }
  let I₀ : Ideal A := hA.1.choose
  have hI₀ : TopologicalRing.IsWeakIdealOfDefinition I₀ := hA.1.choose_spec
  let J₀ : Ideal B := hB.1.choose
  have hJ₀ : TopologicalRing.IsWeakIdealOfDefinition J₀ := hB.1.choose_spec
  let pair : ∀ _L : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I },
      Ideal A × Ideal B := fun L =>
    (I₀ ⊓ Ideal.comap aToT L.1, J₀ ⊓ Ideal.comap bToT L.1)
  have pair_weak (L : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I }) :
      TopologicalRing.IsWeakIdealOfDefinition (pair L).1 ∧
        TopologicalRing.IsWeakIdealOfDefinition (pair L).2 :=
    ⟨TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right hI₀
        (L.2.1.preimage haToTcont),
      TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right hJ₀
        (L.2.1.preimage hbToTcont)⟩
  have pair_le (L : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I }) :
      TopologicalRing.tensorProductSubmodule ((pair L).1.restrictScalars C)
          ((pair L).2.restrictScalars C) ≤ (Ideal.comap coeT L.1).restrictScalars C := by
    exact map_tensorProductSubmodule_mem coeT L.1
      (fun a ha => (Ideal.mem_inf.mp ha).2) (fun b hb => (Ideal.mem_inf.mp hb).2)
  have pair_mono (L M : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I })
      (hLM : L.1 ≤ M.1) : (pair L).1 ≤ (pair M).1 ∧ (pair L).2 ≤ (pair M).2 :=
    ⟨inf_le_inf le_rfl (Ideal.comap_mono hLM), inf_le_inf le_rfl (Ideal.comap_mono hLM)⟩
  have stageFactor : ∀ L : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I },
      ∃ φ : (A ⧸ (pair L).1) ⊗[C] (B ⧸ (pair L).2) →ₐ[C] (T ⧸ L.1),
        φ.comp (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ C (pair L).1)
            (Ideal.Quotient.mkₐ C (pair L).2)) = (Ideal.Quotient.mkₐ C L.1).comp coeTAlg ∧
          Function.Surjective φ := by
    intro L
    let fQ : A →ₐ[C] (T ⧸ L.1) := (Ideal.Quotient.mkₐ C L.1).comp aToTAlg
    let gQ : B →ₐ[C] (T ⧸ L.1) := (Ideal.Quotient.mkₐ C L.1).comp bToTAlg
    have hψeq : (Algebra.TensorProduct.lift fQ gQ (fun _ _ => Commute.all _ _)).toRingHom =
        (Ideal.Quotient.mk L.1).comp coeT := by
      refine RingHom.ext fun x => ?_
      induction x using TensorProduct.inductionOn with
      | tmul a b =>
          change Algebra.TensorProduct.lift fQ gQ (fun _ _ => Commute.all _ _)
            (a ⊗ₜ[C] b) = _
          rw [Algebra.TensorProduct.lift_tmul]
          change Ideal.Quotient.mk L.1 (aToT a) * Ideal.Quotient.mk L.1 (bToT b) =
            Ideal.Quotient.mk L.1 (coeT (a ⊗ₜ[C] b))
          rw [← map_mul]
          exact congrArg (Ideal.Quotient.mk L.1) (hmul_include a b)
      | add x y hx hy => rw [map_add, map_add, hx, hy]
    have hψ : Function.Surjective
        (Algebra.TensorProduct.lift fQ gQ (fun _ _ => Commute.all _ _)) := by
      intro z
      obtain ⟨x, hx⟩ := surjective_quotientMk_coe (R := A ⊗[C] B) L.2.1 z
      refine ⟨(x : A ⊗[C] B), ?_⟩
      change (Algebra.TensorProduct.lift fQ gQ (fun _ _ => Commute.all _ _)).toRingHom x = _
      rw [hψeq]
      exact hx
    have hIzero : ∀ a ∈ (pair L).1, fQ a = 0 := by
      intro a ha
      change Ideal.Quotient.mk L.1 (aToT a) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (pair_le L (tensorProductSubmodule_includeLeft_mem
        (R := C) (I := (pair L).1) (J := (pair L).2) ha))
    have hJzero : ∀ b ∈ (pair L).2, gQ b = 0 := by
      intro b hb
      change Ideal.Quotient.mk L.1 (bToT b) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (pair_le L (tensorProductSubmodule_includeRight_mem
        (R := C) (I := (pair L).1) (J := (pair L).2) hb))
    obtain ⟨φ, hfactor, hφ⟩ := exists_tensorQuotientAlgHom fQ gQ hIzero hJzero hψ
    refine ⟨φ, hfactor.trans ?_, hφ⟩
    refine AlgHom.ext fun z => ?_
    change (Algebra.TensorProduct.lift fQ gQ (fun _ _ => Commute.all _ _)).toRingHom z = _
    rw [hψeq]
    rfl
  let stageA : ∀ L : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I },
      { I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I } :=
    fun L => ⟨(pair L).1, (pair_weak L).1⟩
  let stageB : ∀ L : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I },
      { I : Ideal B // TopologicalRing.IsWeakIdealOfDefinition I } :=
    fun L => ⟨(pair L).2, (pair_weak L).2⟩
  let stageMap' : ∀ L : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I },
      (A ⧸ (pair L).1) ⊗[C] (B ⧸ (pair L).2) →ₐ[C] (T ⧸ L.1) :=
    fun L => Classical.choose (stageFactor L)
  let quotientMk : ∀ L : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I },
      (A ⊗[C] B) →ₐ[C] (A ⧸ (pair L).1) ⊗[C] (B ⧸ (pair L).2) :=
    fun L => Algebra.TensorProduct.map (Ideal.Quotient.mkₐ C (pair L).1)
      (Ideal.Quotient.mkₐ C (pair L).2)
  have quotientMk_surjective (L : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I }) :
      Function.Surjective (quotientMk L) :=
    Algebra.TensorProduct.map_surjective (f := Ideal.Quotient.mkₐ C (pair L).1)
      (g := Ideal.Quotient.mkₐ C (pair L).2) (Ideal.Quotient.mkₐ_surjective C (pair L).1)
      (Ideal.Quotient.mkₐ_surjective C (pair L).2)
  let stageTransition : ∀ (L M : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I }),
      (pair L).1 ≤ (pair M).1 → (pair L).2 ≤ (pair M).2 →
      ((A ⧸ (pair L).1) ⊗[C] (B ⧸ (pair L).2) →ₐ[C]
        (A ⧸ (pair M).1) ⊗[C] (B ⧸ (pair M).2)) :=
    fun _ _ hI hJ => Algebra.TensorProduct.map (Ideal.Quotient.factorₐ C hI)
      (Ideal.Quotient.factorₐ C hJ)
  have stageTransition_comp (L M : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I })
      (hI : (pair L).1 ≤ (pair M).1) (hJ : (pair L).2 ≤ (pair M).2) :
      (stageTransition L M hI hJ).comp (quotientMk L) = quotientMk M := by
    refine AlgHom.ext fun z => ?_
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
        simp [stageTransition, quotientMk, Algebra.TensorProduct.map_tmul,
          Ideal.Quotient.factor_mk]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have stageMap_transition (L M : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I })
      (hLM : L.1 ≤ M.1) :
      (Ideal.Quotient.factorₐ C hLM).comp (stageMap' L) =
        (stageMap' M).comp (stageTransition L M (pair_mono L M hLM).1 (pair_mono L M hLM).2) := by
    refine (AlgHom.cancel_right (quotientMk_surjective L)).1 ?_
    calc _ = (Ideal.Quotient.factorₐ C hLM).comp ((stageMap' L).comp (quotientMk L)) := by
          simp [AlgHom.comp_assoc]
      _ = (Ideal.Quotient.factorₐ C hLM).comp ((Ideal.Quotient.mkₐ C L.1).comp coeTAlg) :=
          congrArg (fun ψ => (Ideal.Quotient.factorₐ C hLM).comp ψ)
            (Classical.choose_spec (stageFactor L)).1
      _ = (Ideal.Quotient.mkₐ C M.1).comp coeTAlg := by
          rw [← AlgHom.comp_assoc, Ideal.Quotient.factorₐ_comp_mk]
      _ = (stageMap' M).comp (quotientMk M) := (Classical.choose_spec (stageFactor M)).1.symm
      _ = _ := by
          rw [← stageTransition_comp L M (pair_mono L M hLM).1 (pair_mono L M hLM).2,
            AlgHom.comp_assoc]
  have inSite : ∀ L : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I },
      𝔅.Contains (Spec (.of (T ⧸ L.1))) := fun L =>
    contains_spec_of_surjective 𝔅 (stageMap' L).toRingHom
      (Classical.choose_spec (stageFactor L)).2
      (contains_spec_tensorProduct 𝔅 (DA.inSite (stageA L)) (DB.inSite (stageB L)))
  let overS : ∀ L : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I },
      Spec (.of (T ⧸ L.1)) ⟶ S := fun L =>
    Spec.map (CommRingCat.ofHom ((stageMap' L).toRingHom)) ≫
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
        (A ⧸ (pair L).1) →+* (A ⧸ (pair L).1) ⊗[C] (B ⧸ (pair L).2))) ≫
      DA.overS (stageA L)
  have overS_compatible : ∀ (L M : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I })
      (hLM : L.1 ≤ M.1),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hLM)) ≫ overS L = overS M := by
    intro L M hLM
    have hI := (pair_mono L M hLM).1
    have hJ := (pair_mono L M hLM).2
    have hτincl : (stageTransition L M hI hJ).toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom :
          (A ⧸ (pair L).1) →+* (A ⧸ (pair L).1) ⊗[C] (B ⧸ (pair L).2)) =
        (Algebra.TensorProduct.includeLeftRingHom :
          (A ⧸ (pair M).1) →+* (A ⧸ (pair M).1) ⊗[C] (B ⧸ (pair M).2)).comp
          (Ideal.Quotient.factor hI) := by
      ext a
      simp [stageTransition]
    have hcomp : (Ideal.Quotient.factor hLM).comp
          ((stageMap' L).toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom :
            (A ⧸ (pair L).1) →+* (A ⧸ (pair L).1) ⊗[C] (B ⧸ (pair L).2))) =
        (stageMap' M).toRingHom.comp
          ((Algebra.TensorProduct.includeLeftRingHom :
            (A ⧸ (pair M).1) →+* (A ⧸ (pair M).1) ⊗[C] (B ⧸ (pair M).2)).comp
            (Ideal.Quotient.factor hI)) := by
      calc (Ideal.Quotient.factor hLM).comp
            ((stageMap' L).toRingHom.comp Algebra.TensorProduct.includeLeftRingHom)
          = ((Ideal.Quotient.factorₐ C hLM).comp (stageMap' L)).toRingHom.comp
              Algebra.TensorProduct.includeLeftRingHom := rfl
        _ = ((stageMap' M).comp (stageTransition L M hI hJ)).toRingHom.comp
              Algebra.TensorProduct.includeLeftRingHom := by
            rw [stageMap_transition L M hLM]
        _ = (stageMap' M).toRingHom.comp
              ((stageTransition L M hI hJ).toRingHom.comp
                Algebra.TensorProduct.includeLeftRingHom) := RingHom.comp_assoc _ _ _
        _ = _ := by rw [hτincl]
    have hmaps : Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hLM)) ≫
          Spec.map (CommRingCat.ofHom (stageMap' L).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
            (A ⧸ (pair L).1) →+* (A ⧸ (pair L).1) ⊗[C] (B ⧸ (pair L).2))) =
        Spec.map (CommRingCat.ofHom (stageMap' M).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom :
            (A ⧸ (pair M).1) →+* (A ⧸ (pair M).1) ⊗[C] (B ⧸ (pair M).2))) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hI)) := by
      simpa only [CommRingCat.ofHom_comp, Spec.map_comp] using
        congrArg (fun q => Spec.map (CommRingCat.ofHom q)) hcomp
    dsimp only [overS]
    rw [← DA.compatible (stageA L) (stageA M) hI]
    simpa only [Category.assoc] using hmaps =≫ DA.overS (stageA L)
  let DT : QuotientSystem 𝔅 S hS T :=
    { inSite := inSite, overS := overS, compatible := overS_compatible }
  have haStage (L : { I : Ideal T // TopologicalRing.IsWeakIdealOfDefinition I }) :
      (stageMap' L).toRingHom.comp (Algebra.TensorProduct.includeLeftRingHom :
          (A ⧸ (pair L).1) →+* (A ⧸ (pair L).1) ⊗[C] (B ⧸ (pair L).2)) =
        Ideal.quotientMap L.1 aToT
          (show (pair L).1 ≤ Ideal.comap aToT L.1 from inf_le_right) := by
    ext a
    have H := congrArg (fun k : (A ⊗[C] B) →ₐ[C] (T ⧸ L.1) => k (a ⊗ₜ[C] (1 : B)))
      (Classical.choose_spec (stageFactor L)).1
    simpa [stageMap', Algebra.TensorProduct.includeLeftRingHom,
      Algebra.TensorProduct.includeLeft_apply, aToT, coeTAlg, coeT] using H
  let aHom : ContinuousHom DA DT :=
    ContinuousHom.ofStages DA DT aToT haToTcont (by
      intro L
      refine ⟨stageA L, inf_le_right, ?_⟩
      change _ = overS L
      dsimp only [overS]
      rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      exact congrArg (fun k => Spec.map (CommRingCat.ofHom k) ≫ DA.overS (stageA L))
        (haStage L).symm)
  let cHom : ContinuousHom DC DT := ContinuousHom.comp hA hC aHom cToA
  let bHom : ContinuousHom DB DT :=
    ContinuousHom.ofComp' hC cToB cHom bToT hbToTcont hbase
  have hcomm : formalSpectrumMap hA aHom ≫ formalSpectrumMap hC cToA =
      formalSpectrumMap hB bHom ≫ formalSpectrumMap hC cToB := by
    rw [formalSpectrumMap_comp hC hA cToA aHom cHom rfl,
      formalSpectrumMap_comp hC hB cToB bHom cHom hbase]
  let p : formalSpectrum DT ⟶ pullback f g :=
    pullback.lift (formalSpectrumMap hA aHom ≫ eX.inv)
      (formalSpectrumMap hB bHom ≫ eY.inv) (by
        apply (cancel_mono eZ.hom).mp
        simpa only [Category.assoc, ← hf, ← hg] using hcomm)
  have hZformal : IsFormalAlgebraicSpace 𝔅 S hS Z :=
    isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace 𝔅 S hS hZ
  have hP : HasAffineClosedImmersionCriterionMapToSpec 𝔅 S hS (pullback f g) :=
    hasAffineClosedImmersionCriterion_pullback 𝔅 S hS f g hZformal hZsep hX hY
  obtain ⟨R, iCR, iTS, iTR, iLT, hpr⟩ :=
    exists_isPresentingRing_of_hasAffineClosedImmersionCriterion 𝔅 S hS hP
  let := iCR
  let := iTS
  let := iTR
  let := iLT
  have hR : TopologicalRing.IsWeaklyAdmissible R := hpr.1
  obtain ⟨DR, ⟨eR⟩⟩ := exists_quotientSystem_iso_formalSpectrum_of_isPresentingRing hpr
  have hDAaff : IsAffineFormalAlgebraicSpace 𝔅 S hS (formalSpectrum DA) :=
    isAffineFormalAlgebraicSpace_of_iso 𝔅 S hS eX hX.1
  have hDBaff : IsAffineFormalAlgebraicSpace 𝔅 S hS (formalSpectrum DB) :=
    isAffineFormalAlgebraicSpace_of_iso 𝔅 S hS eY hY.1
  have hDCaff : IsAffineFormalAlgebraicSpace 𝔅 S hS (formalSpectrum DC) :=
    isAffineFormalAlgebraicSpace_of_iso 𝔅 S hS eZ hZ
  have hDRaff : IsAffineFormalAlgebraicSpace 𝔅 S hS (formalSpectrum DR) :=
    isAffineFormalAlgebraicSpace_of_iso 𝔅 S hS eR hP.1
  obtain ⟨aR, haR, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA hR
    (eR.inv ≫ pullback.fst f g ≫ eX.hom)
  obtain ⟨bR, hbR, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hB hR
    (eR.inv ≫ pullback.snd f g ≫ eY.hom)
  have hcaR : ContinuousHom.comp hA hC aR cToA = ContinuousHom.comp hB hC bR cToB := by
    refine continuousHom_injective_formalSpectrumMap hC hR ?_
    rw [← formalSpectrumMap_comp hC hA cToA aR (ContinuousHom.comp hA hC aR cToA) rfl,
      ← formalSpectrumMap_comp hC hB cToB bR (ContinuousHom.comp hB hC bR cToB) rfl,
      haR, hbR, hf, hg]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← pullback.condition_assoc]
  let : Algebra C R := (ContinuousHom.comp hA hC aR cToA).toRingHom.toAlgebra
  let aAlg : A →ₐ[C] R := { toRingHom := aR.toRingHom, commutes' := fun _ => rfl }
  let bAlg : B →ₐ[C] R :=
    { toRingHom := bR.toRingHom
      commutes' := fun c => by
        change (ContinuousHom.comp hB hC bR cToB).toRingHom c =
          (ContinuousHom.comp hA hC aR cToA).toRingHom c
        rw [hcaR] }
  have hl : Continuous (Algebra.TensorProduct.lift aAlg bAlg (fun _ _ => Commute.all _ _)) :=
    continuous_tensorProduct_lift aAlg bAlg aR.continuous bR.continuous
  let : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  let : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace R := hR.2.1
  let : T2Space R := hR.2.2
  let tR : T →+* R := UniformSpace.Completion.extensionHom
    (Algebra.TensorProduct.lift aAlg bAlg (fun _ _ => Commute.all _ _)).toRingHom hl
  have htR : Continuous tR := UniformSpace.Completion.continuous_extension
  have hta : tR.comp aToT = aR.toRingHom := by
    ext a
    change tR ((a ⊗ₜ[C] (1 : B) : A ⊗[C] B) : T) = _
    rw [UniformSpace.Completion.extensionHom_coe]
    change aAlg a * bAlg 1 = _
    rw [map_one, mul_one]
    rfl
  have htb : tR.comp bToT = bR.toRingHom := by
    ext b
    change tR (((1 : A) ⊗ₜ[C] b : A ⊗[C] B) : T) = _
    rw [UniformSpace.Completion.extensionHom_coe]
    change aAlg 1 * bAlg b = _
    rw [map_one, one_mul]
    rfl
  let tHom : ContinuousHom DT DR := ContinuousHom.ofComp' hA aHom aR tR htR hta.symm
  have hma : formalSpectrumMap hTweak tHom ≫ formalSpectrumMap hA aHom =
      formalSpectrumMap hA aR :=
    formalSpectrumMap_comp hA hTweak aHom tHom aR hta.symm
  have hmb : formalSpectrumMap hTweak tHom ≫ formalSpectrumMap hB bHom =
      formalSpectrumMap hB bR :=
    formalSpectrumMap_comp hB hTweak bHom tHom bR htb.symm
  let q : pullback f g ⟶ formalSpectrum DT := eR.hom ≫ formalSpectrumMap hTweak tHom
  have hqa : q ≫ formalSpectrumMap hA aHom = pullback.fst f g ≫ eX.hom := by
    simp only [q, Category.assoc, hma, haR, Iso.hom_inv_id_assoc]
  have hqb : q ≫ formalSpectrumMap hB bHom = pullback.snd f g ≫ eY.hom := by
    simp only [q, Category.assoc, hmb, hbR, Iso.hom_inv_id_assoc]
  have hqp : q ≫ p = 𝟙 _ := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc, p, pullback.lift_fst]
      rw [← Category.assoc, hqa]
      simp
    · simp only [Category.assoc, p, pullback.lift_snd]
      rw [← Category.assoc, hqb]
      simp
  obtain ⟨d, hd, -⟩ :=
    existsUnique_continuousHom_formalSpectrumMap_eq hR hTweak (p ≫ eR.hom)
  have hda : d.toRingHom.comp aR.toRingHom = aToT :=
    congrArg ContinuousHom.toRingHom <| comp_eq_of_formalSpectrumMap_comp_eq hA hR hTweak
      aR d aHom (by
        rw [hd, haR]
        simp only [p, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_fst_assoc,
          Iso.inv_hom_id, Category.comp_id])
  have hdb : d.toRingHom.comp bR.toRingHom = bToT :=
    congrArg ContinuousHom.toRingHom <| comp_eq_of_formalSpectrumMap_comp_eq hB hR hTweak
      bR d bHom (by
        rw [hd, hbR]
        simp only [p, Category.assoc, Iso.hom_inv_id_assoc, pullback.lift_snd_assoc,
          Iso.inv_hom_id, Category.comp_id])
  have hdt : d.toRingHom.comp tR = RingHom.id T := by
    refine RingHom.ext fun x => ?_
    refine UniformSpace.Completion.induction_on x ?_ ?_
    · have : T2Space T := hTweak.2.2
      exact isClosed_eq (d.continuous.comp htR) continuous_id
    · intro z
      change d.toRingHom (tR (z : T)) = _
      rw [UniformSpace.Completion.extensionHom_coe]
      induction z using TensorProduct.inductionOn with
      | tmul a b =>
          change d.toRingHom (Algebra.TensorProduct.lift aAlg bAlg
            (fun _ _ => Commute.all _ _) (a ⊗ₜ[C] b)) = _
          rw [Algebra.TensorProduct.lift_tmul, map_mul]
          have ha : d.toRingHom (aR.toRingHom a) = aToT a := RingHom.congr_fun hda a
          have hb : d.toRingHom (bR.toRingHom b) = bToT b := RingHom.congr_fun hdb b
          change d.toRingHom (aR.toRingHom a) * d.toRingHom (bR.toRingHom b) = _
          rw [ha, hb, hmul_include]
          rfl
      | add z w hz hw =>
          simpa only [UniformSpace.Completion.coe_add, map_add] using congrArg₂ (· + ·) hz hw
  have hpq : p ≫ q = 𝟙 _ := by
    change p ≫ eR.hom ≫ formalSpectrumMap hTweak tHom = _
    rw [← Category.assoc, ← hd, formalSpectrumMap_comp hTweak hR tHom d
      (ContinuousHom.comp hR hTweak d tHom) rfl]
    exact formalSpectrumMap_id hTweak (ContinuousHom.comp hR hTweak d tHom) hdt
  exact ⟨DT, aHom, bHom, ⟨q, p, hqp, hpq⟩, hTweak, rfl, rfl, hqa, hqb⟩

/-- Let `X = Spf A`, `Y = Spf B` and `Z = Spf C` for weakly admissible topological rings over `S`,
with `Spf C` an affine formal algebraic space. Then any two morphisms `f : X ⟶ Z` and
`g : Y ⟶ Z` are the formal spectra of continuous ring maps `C → A` and `C → B` over `S`. -/
theorem exists_continuousHom_formalSpectrumMap_eq {X Y Z : FppfSheaf 𝔅 S hS}
    {A B C : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
    (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hB : TopologicalRing.IsWeaklyAdmissible B)
    (hC : TopologicalRing.IsWeaklyAdmissible C)
    {DA : QuotientSystem 𝔅 S hS A} {DB : QuotientSystem 𝔅 S hS B}
    {DC : QuotientSystem 𝔅 S hS C}
    (eX : X ≅ formalSpectrum DA) (eY : Y ≅ formalSpectrum DB) (eZ : Z ≅ formalSpectrum DC)
    (f : X ⟶ Z) (g : Y ⟶ Z) :
    ∃ (cToA : ContinuousHom DC DA) (cToB : ContinuousHom DC DB),
      formalSpectrumMap hC cToA = eX.inv ≫ f ≫ eZ.hom ∧
        formalSpectrumMap hC cToB = eY.inv ≫ g ≫ eZ.hom := by
  obtain ⟨cToA, hcToA, -⟩ :=
    existsUnique_continuousHom_formalSpectrumMap_eq hC hA (eX.inv ≫ f ≫ eZ.hom)
  obtain ⟨cToB, hcToB, -⟩ :=
    existsUnique_continuousHom_formalSpectrumMap_eq hC hB (eY.inv ≫ g ≫ eZ.hom)
  exact ⟨cToA, cToB, hcToA, hcToB⟩

end Clause

end AlgebraicGeometry.FormalSpace

end
