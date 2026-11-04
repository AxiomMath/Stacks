module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.MapsToAlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PresentingRingUniqueness
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite
public import StacksFrontier.Topology.Algebra.AdicTopology.CompletedTensorProduct.WeakIdeal

/-!
# The fibre product of McQuillan affine formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B` and let `A₀`, `A₁` and `A` be weakly
admissible topological rings over `S`, presented by quotient systems `D₀`, `D₁` and `D`, with
continuous homomorphisms `A₀ → A₁` and `A₀ → A` over `S`. **Stacks 0AN3, clause (3)** says that
the fibre product `Spf A₁ ×_{Spf A₀} Spf A` is the formal spectrum of the completed tensor
product `A₁ ⊗̂_{A₀} A`.

Two things have to be produced. The first is a quotient system on `A₁ ⊗̂_{A₀} A`, that is, the
assertion that every quotient of it by a weak ideal of definition is an affine scheme of the
site, compatibly over `S`. This is unconditional and is the ring computation of the source: by
`TopologicalRing.exists_weakIdealProjectionKernel_le` a weak ideal of definition of
`A₁ ⊗̂_{A₀} A` contains one of the projection kernels, and by
`TopologicalRing.quotientWeakIdealProjectionKernelRingEquiv` the quotient by a projection kernel
is the ordinary tensor product `A₁ ⧸ I ⊗_{A₀} A ⧸ J` of two stages, whose spectrum is contained
in the site by `AlgebraicGeometry.BigFppfSite.contains_spec_tensorProduct`. The structure
morphism to `S` is taken through the stage of `Spf A₁` cut out by the intersection of a fixed
weak ideal of definition of `A₁` with the preimage of the given ideal, which is monotone and
therefore compatible with the transitions.

The second is the identification of the fibre product. The canonical morphism
`Spf (A₁ ⊗̂_{A₀} A) ⟶ Spf A₁ ×_{Spf A₀} Spf A` always exists, being the lift of the formal
spectra of the two canonical maps into the completed tensor product. That it is an isomorphism
is proved here from the hypothesis that the fibre product is *itself* the formal spectrum of a
weakly admissible topological ring `R` over `S` — the hypothesis `epres` below. Given that, the
two projections are the formal spectra of continuous homomorphisms `A₁ → R` and `A → R` by
Stacks 0AN0; they agree on `A₀`, so they lift to `A₁ ⊗_{A₀} A → R` and, `R` being complete and
separated, extend to `A₁ ⊗̂_{A₀} A → R`; the resulting morphism of formal spectra is inverse to
the canonical one.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_quotientSystem_iso_pullback_completedTensorProduct`:
  **Stacks 0AN3, clause (3)** — the quotient system on `A₁ ⊗̂_{A₀} A` together with an
  isomorphism of `Spf (A₁ ⊗̂_{A₀} A)` onto the fibre product compatible with both projections.
* `AlgebraicGeometry.FormalSpace.exists_continuous_ringEquiv_completedTensorProduct_pullback`:
  the same clause read on chart rings — the chart ring of the fibre product is `A₁ ⊗̂_{A₀} A` by
  an isomorphism of topological rings compatible with both projections. This is the shape in
  which the chart argument of Stacks 0GBD consumes clause (3).

## Implementation notes

The hypothesis `epres` is the one input this library does not carry. In the source it is clause
(2) of the same tag — the fibre product of McQuillan affine formal algebraic spaces over a
separated McQuillan one is again McQuillan — read through the McQuillan criterion of Stacks
0AIC, of which this library has the direction producing a presentation only for a sequential
one (`AlgebraicGeometry.FormalSpace.exists_quotientSystem_formalSpectrum_iso`) and for a
countably indexed one
(`AlgebraicGeometry.FormalSpace.exists_quotientSystem_of_isCountablyIndexed`). It cannot be
removed by Yoneda: `AlgebraicGeometry.FormalSpace.existsUnique_continuousHom_formalSpectrumMap_eq`,
which is Stacks 0AN0 here, is full faithfulness of `Spf` against *formal spectra*, not a
universal property against arbitrary fppf sheaves, so representability of the fibre product is
not a consequence of it. Clause (1),
`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_pullback`, gives affineness of the
fibre product and says nothing about its chart ring.

Separatedness of the base is therefore *not* assumed. The source uses it only to obtain clauses
(1) and (2); with the presentation of the fibre product granted, the identification of its chart
ring needs nothing of the base beyond weak admissibility.

## References

* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
* [Stacks Project, Tag 0AN0](https://stacks.math.columbia.edu/tag/0AN0)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0AMU](https://stacks.math.columbia.edu/tag/0AMU)
* [Stacks Project, Tag 0AMV](https://stacks.math.columbia.edu/tag/0AMV)
* [Stacks Project, Tag 0GB4](https://stacks.math.columbia.edu/tag/0GB4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry.FormalSpace

universe u

private theorem spec_size_le_of_surjective_ringHom
    {R Q : Type u} [CommRing R] [CommRing Q]
    (φ : R →+* Q) (hφ : Function.Surjective φ) :
    (Spec (.of Q)).size ≤ (Spec (.of R)).size :=
  have : _root_.AlgebraicGeometry.IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ) hφ
  Scheme.size_le_of_mono_quasiCompact (Spec.map (CommRingCat.ofHom φ))

private theorem quotientMap_comp_factor
    {R Q : Type u} [CommRing R] [CommRing Q]
    (f : R →+* Q) (I J : Ideal R) (K : Ideal Q)
    (hIJ : I ≤ J) (hJ : J ≤ Ideal.comap f K) :
    (Ideal.quotientMap K f hJ).comp (Ideal.Quotient.factor hIJ) =
      Ideal.quotientMap K f (hIJ.trans hJ) := by
  ext _; rfl

private theorem factor_comp_quotientMap
    {R Q : Type u} [CommRing R] [CommRing Q]
    (f : R →+* Q) (I : Ideal R) (K L : Ideal Q) (hKL : K ≤ L)
    (hK : I ≤ Ideal.comap f K) (hL : I ≤ Ideal.comap f L) :
    (Ideal.Quotient.factor hKL).comp (Ideal.quotientMap K f hK) =
      Ideal.quotientMap L f hL := by
  ext _; rfl

private theorem factor_comp_quotientMap_comp_factor
    {R Q : Type u} [CommRing R] [CommRing Q] (f : R →+* Q)
    {I J : Ideal R} {K L : Ideal Q} (hIJ : I ≤ J) (hKL : K ≤ L)
    (hK : I ≤ Ideal.comap f K) (hL : J ≤ Ideal.comap f L) :
    (Ideal.Quotient.factor hKL).comp (Ideal.quotientMap K f hK) =
      (Ideal.quotientMap L f hL).comp (Ideal.Quotient.factor hIJ) := by
  ext _; rfl

private theorem surjective_quotient_factor {R : Type u} [CommRing R] {I J : Ideal R}
    (h : I ≤ J) : Function.Surjective (Ideal.Quotient.factor h) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk I x, rfl⟩

/-- The weak ideals of definition of a weakly admissible ring form a nonempty directed set. -/
private theorem nonempty_directed_weakIdeals
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : TopologicalRing.IsWeaklyAdmissible R) :
    Nonempty (WeakIdeals R) ∧ IsDirected (WeakIdeals R) (· ≤ ·) :=
  ⟨⟨OrderDual.toDual ⟨hR.1.choose, hR.1.choose_spec⟩⟩, ⟨fun J K ↦ ⟨OrderDual.toDual ⟨J.1 ⊓ K.1,
    TopologicalRing.isWeakIdealOfDefinition_inf_of_isOpen_right J.2 K.2.1⟩,
    show J.1 ⊓ K.1 ≤ J.1 from inf_le_left, show J.1 ⊓ K.1 ≤ K.1 from inf_le_right⟩⟩⟩

private theorem exists_weakIdeal_comap_subset
    {R Q : Type u} [CommRing R] [TopologicalSpace R] [CommRing Q] [TopologicalSpace Q]
    [IsTopologicalRing R] [IsLinearTopology R R]
    (φ : R →+* Q) (hφ : Continuous φ) {J : Ideal Q}
    (hR : TopologicalRing.IsWeaklyAdmissible R)
    (hJ : TopologicalRing.IsWeakIdealOfDefinition J) :
    ∃ I : Ideal R, TopologicalRing.IsWeakIdealOfDefinition I ∧ I ≤ Ideal.comap φ J := by
  obtain ⟨I, hI⟩ := hR.1
  refine ⟨I ⊓ Ideal.comap φ J, ⟨?_, fun _ hx => hI.2 _ (Ideal.mem_inf.mp hx).1⟩, inf_le_right⟩
  change IsOpen ((I : Set R) ∩ φ ⁻¹' (J : Set Q))
  exact hI.1.inter (hJ.1.preimage hφ)

private theorem quotientMap_congr
    {R Q : Type u} [CommRing R] [CommRing Q] {f g : R →+* Q} (hfg : f = g)
    {I : Ideal R} {K : Ideal Q} (hf : I ≤ Ideal.comap f K) (hg : I ≤ Ideal.comap g K) :
    Ideal.quotientMap K f hf = Ideal.quotientMap K g hg := by
  subst hfg; rfl

private theorem quotientMap_comp_quotientMap
    {R Q T : Type u} [CommRing R] [CommRing Q] [CommRing T]
    (ρ : R →+* Q) (χ : Q →+* T) {I : Ideal R} {J : Ideal Q} {K : Ideal T}
    (hIJ : I ≤ Ideal.comap ρ J) (hJK : J ≤ Ideal.comap χ K)
    (hIK : I ≤ Ideal.comap (χ.comp ρ) K) :
    (Ideal.quotientMap K χ hJK).comp (Ideal.quotientMap J ρ hIJ) =
      Ideal.quotientMap K (χ.comp ρ) hIK := by
  ext _; rfl

/-- If the formal spectra of continuous homs `q` and `r` compose to that of `s`, then the ring
maps of `q` and `r` compose to that of `s`, by Stacks 0AN0. -/
private theorem toRingHom_comp_eq_of_formalSpectrumMap_comp_eq
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {R₁ R₂ R₃ : Type u}
    [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁] [IsLinearTopology R₁ R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂] [IsLinearTopology R₂ R₂]
    [CommRing R₃] [TopologicalSpace R₃] [IsTopologicalRing R₃] [IsLinearTopology R₃ R₃]
    {D₁ : QuotientSystem B S hS R₁} {D₂ : QuotientSystem B S hS R₂}
    {D₃ : QuotientSystem B S hS R₃}
    (h₁ : TopologicalRing.IsWeaklyAdmissible R₁) (h₂ : TopologicalRing.IsWeaklyAdmissible R₂)
    (h₃ : TopologicalRing.IsWeaklyAdmissible R₃)
    (q : ContinuousHom D₂ D₁) (r : ContinuousHom D₃ D₂) (s : ContinuousHom D₃ D₁)
    (h : formalSpectrumMap h₂ q ≫ formalSpectrumMap h₃ r = formalSpectrumMap h₃ s) :
    q.toRingHom.comp r.toRingHom = s.toRingHom :=
  congrArg ContinuousHom.toRingHom
    ((existsUnique_continuousHom_formalSpectrumMap_eq h₃ h₁ (formalSpectrumMap h₃ s)).unique
      ((formalSpectrumMap_comp_eq h₂ h₃ q r).symm.trans h) rfl)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

private def continuousHomOfStages
    {R Q : Type u} [CommRing R] [TopologicalSpace R] [CommRing Q] [TopologicalSpace Q]
    (D : QuotientSystem B S hS R) (E : QuotientSystem B S hS Q)
    (f : R →+* Q) (hf : Continuous f)
    (H : ∀ K : {I : Ideal Q // TopologicalRing.IsWeakIdealOfDefinition I},
      ∃ (J : {I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I})
        (h : J.1 ≤ Ideal.comap f K.1),
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 f h)) ≫ D.overS J = E.overS K) :
    ContinuousHom D E where
  toRingHom := f
  continuous := hf
  overS J K h := by
    obtain ⟨J', h', e⟩ := H K
    have HJ := D.compatible ⟨J.1 ⊓ J'.1, weakIdeal_inf J.2 J'.2⟩ J inf_le_left
    have HJ' := D.compatible ⟨J.1 ⊓ J'.1, weakIdeal_inf J.2 J'.2⟩ J' inf_le_right
    rw [← HJ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      quotientMap_comp_factor]
    rw [← HJ', ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      quotientMap_comp_factor] at e
    exact e

/-- A continuous ring map out of the target of a continuous hom of chart systems is itself a
continuous hom of chart systems, as soon as its composite with the given one is. -/
private def continuousHomOfComp
    {R Q T' : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R]
    [CommRing Q] [TopologicalSpace Q] [CommRing T'] [TopologicalSpace T']
    {D : QuotientSystem B S hS R} {E : QuotientSystem B S hS Q}
    {F : QuotientSystem B S hS T'}
    (hR : TopologicalRing.IsWeaklyAdmissible R)
    (g : ContinuousHom D E) (fg : ContinuousHom D F)
    (f : Q →+* T') (hf : Continuous f)
    (hfg : fg.toRingHom = f.comp g.toRingHom) :
    ContinuousHom E F where
  toRingHom := f
  continuous := hf
  overS J K h := by
    obtain ⟨I, hI, hIJ⟩ :=
      exists_weakIdeal_comap_subset g.toRingHom g.continuous hR J.2
    have hIK : I ≤ Ideal.comap fg.toRingHom K.1 := by
      rw [hfg]; exact fun _ hx => h (hIJ hx)
    have key : (Ideal.quotientMap K.1 f h).comp (Ideal.quotientMap J.1 g.toRingHom hIJ) =
        Ideal.quotientMap K.1 fg.toRingHom hIK := by
      refine Ideal.Quotient.ringHom_ext ?_
      ext a
      change Ideal.Quotient.mk K.1 (f (g.toRingHom a)) =
        Ideal.Quotient.mk K.1 (fg.toRingHom a)
      rw [hfg]; rfl
    rw [← g.overS ⟨I, hI⟩ J hIJ, ← Category.assoc, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, key, fg.overS ⟨I, hI⟩ K hIK]

/-- The functor from the big fppf site over `S` to schemes is faithful. -/
private theorem faithful_toScheme :
    (BigFppfOver.toScheme B S hS).Faithful := by
  dsimp [BigFppfOver.toScheme]; infer_instance

/-- The sheafified Yoneda embedding preserves pullbacks. -/
private theorem preservesLimitsOfShape_sheafifiedYoneda :
    PreservesLimitsOfShape WalkingCospan
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) := by
  dsimp [Sheaf.sheafifiedYoneda]; infer_instance

/-- The route to `S` through a quotient stage of the base does not depend on which weak ideal of
definition of the base is used. -/
private theorem spec_quotientMap_overS_eq
    {A₀ T' : Type u} [CommRing A₀] [TopologicalSpace A₀] [CommRing T'] [TopologicalSpace T']
    (D₀ : QuotientSystem B S hS A₀) (φ₀ : A₀ →+* T')
    {K : Ideal T'}
    {k₁ k₂ : {I : Ideal A₀ // TopologicalRing.IsWeakIdealOfDefinition I}}
    (h1 : k₁.1 ≤ Ideal.comap φ₀ K) (h2 : k₂.1 ≤ Ideal.comap φ₀ K) :
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap K φ₀ h1)) ≫ D₀.overS k₁ =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap K φ₀ h2)) ≫ D₀.overS k₂ := by
  have H1 := D₀.compatible ⟨k₁.1 ⊓ k₂.1, weakIdeal_inf k₁.2 k₂.2⟩ k₁ inf_le_left
  have H2 := D₀.compatible ⟨k₁.1 ⊓ k₂.1, weakIdeal_inf k₁.2 k₂.2⟩ k₂ inf_le_right
  rw [← H1, ← H2, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, quotientMap_comp_factor,
    quotientMap_comp_factor]

/-- A quotient stage of a ring over the base maps to `S` through the base: for a ring map
`χ : A' →+* T'` and a continuous hom `c' : D₀ ⟶ D'` on chart systems, the route from a stage of
`T'` to `S` through a stage of `A'` is the route through a stage of `A₀`. -/
private theorem exists_overS_route_through_base
    {A₀ A' T' : Type u}
    [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀]
    [CommRing A'] [TopologicalSpace A'] [CommRing T'] [TopologicalSpace T']
    (h₀ : TopologicalRing.IsWeaklyAdmissible A₀)
    (D₀ : QuotientSystem B S hS A₀) (D' : QuotientSystem B S hS A')
    (c' : ContinuousHom D₀ D') (χ : A' →+* T')
    {K : Ideal T'}
    (j : {I : Ideal A' // TopologicalRing.IsWeakIdealOfDefinition I})
    (hj : j.1 ≤ Ideal.comap χ K) :
    ∃ (k : {I : Ideal A₀ // TopologicalRing.IsWeakIdealOfDefinition I})
      (hk : k.1 ≤ Ideal.comap (χ.comp c'.toRingHom) K),
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap K χ hj)) ≫ D'.overS j =
        Spec.map (CommRingCat.ofHom (Ideal.quotientMap K (χ.comp c'.toRingHom) hk)) ≫
          D₀.overS k := by
  obtain ⟨k, hkw, hk⟩ := exists_weakIdeal_comap_subset c'.toRingHom c'.continuous h₀ j.2
  have hkK : k ≤ Ideal.comap (χ.comp c'.toRingHom) K := fun _ hx => hj (hk hx)
  refine ⟨⟨k, hkw⟩, hkK, ?_⟩
  rw [← c'.overS ⟨k, hkw⟩ j hk, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    quotientMap_comp_quotientMap c'.toRingHom χ hk hj hkK]

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A₀ A₁ A : Type u}
  [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀]
  [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁] [IsLinearTopology A₁ A₁]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [Algebra A₀ A₁] [Algebra A₀ A]

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The canonical map of a factor into the completed tensor product is the composition of the
inclusion into the ordinary tensor product with the completion map. -/
private theorem algebraMap_completedTensorProduct_left_eq :
    letI : UniformSpace (A₁ ⊗[A₀] A) :=
      TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A)
    (algebraMap A₁ (TopologicalRing.CompletedTensorProduct
        (R := A₀) (M := A₁) (N := A))) =
      (UniformSpace.Completion.coeRingHom : (A₁ ⊗[A₀] A) →+*
        TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)).comp
        (Algebra.TensorProduct.includeLeftRingHom : A₁ →+* A₁ ⊗[A₀] A) :=
  rfl

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
private theorem algebraMap_completedTensorProduct_right_eq :
    letI : UniformSpace (A₁ ⊗[A₀] A) :=
      TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A)
    (algebraMap A (TopologicalRing.CompletedTensorProduct
        (R := A₀) (M := A₁) (N := A))) =
      (UniformSpace.Completion.coeRingHom : (A₁ ⊗[A₀] A) →+*
        TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)).comp
        ((Algebra.TensorProduct.includeRight : A →ₐ[A₀] A₁ ⊗[A₀] A).toRingHom) :=
  rfl

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The left inclusion of a completed tensor product is continuous. -/
private theorem continuous_algebraMap_completedTensorProduct_left :
    Continuous (algebraMap A₁
      (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A))) := by
  let : UniformSpace (A₁ ⊗[A₀] A) :=
    TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A)
  rw [algebraMap_completedTensorProduct_left_eq]
  exact (UniformSpace.Completion.continuous_coe (A₁ ⊗[A₀] A)).comp
    (TopologicalRing.continuous_tmul_const (R := A₀) (M := A₁) (N := A) (1 : A))

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The right inclusion of a completed tensor product is continuous. -/
private theorem continuous_algebraMap_completedTensorProduct_right :
    Continuous (algebraMap A
      (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A))) := by
  let : UniformSpace (A₁ ⊗[A₀] A) :=
    TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A)
  rw [algebraMap_completedTensorProduct_right_eq]
  exact (UniformSpace.Completion.continuous_coe (A₁ ⊗[A₀] A)).comp
    (TopologicalRing.continuous_const_tmul (R := A₀) (M := A₁) (N := A) (1 : A₁))

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The two inclusions of a completed tensor product agree on the base ring. -/
private theorem algebraMap_completedTensorProduct_base :
    (algebraMap A₁ (TopologicalRing.CompletedTensorProduct
        (R := A₀) (M := A₁) (N := A))).comp (algebraMap A₀ A₁) =
      (algebraMap A (TopologicalRing.CompletedTensorProduct
        (R := A₀) (M := A₁) (N := A))).comp (algebraMap A₀ A) := by
  let : UniformSpace (A₁ ⊗[A₀] A) :=
    TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A)
  refine RingHom.ext fun x => ?_
  have h : ((algebraMap A₀ A₁ x) ⊗ₜ[A₀] (1 : A) : A₁ ⊗[A₀] A) =
      ((1 : A₁) ⊗ₜ[A₀] (algebraMap A₀ A x)) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    exact TensorProduct.smul_tmul _ _ _
  exact congrArg (UniformSpace.Completion.coeRingHom : (A₁ ⊗[A₀] A) →+*
    TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)) h

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The image of an elementary tensor in the completed tensor product is the product of the
images of its two factors. -/
private theorem coe_tmul_eq_mul (a : A₁) (b : A) :
    letI : UniformSpace (A₁ ⊗[A₀] A) :=
      TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A)
    ((a ⊗ₜ[A₀] b : A₁ ⊗[A₀] A) : (TopologicalRing.CompletedTensorProduct
        (R := A₀) (M := A₁) (N := A))) =
      algebraMap A₁ (TopologicalRing.CompletedTensorProduct
          (R := A₀) (M := A₁) (N := A)) a * algebraMap A (TopologicalRing.CompletedTensorProduct
              (R := A₀) (M := A₁) (N := A)) b := by
  let : UniformSpace (A₁ ⊗[A₀] A) :=
    TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A)
  rw [algebraMap_completedTensorProduct_left_eq, algebraMap_completedTensorProduct_right_eq]
  change _ = (UniformSpace.Completion.coeRingHom : (A₁ ⊗[A₀] A) →+* _)
      (Algebra.TensorProduct.includeLeftRingHom a) *
    (UniformSpace.Completion.coeRingHom : (A₁ ⊗[A₀] A) →+* _)
      ((Algebra.TensorProduct.includeRight : A →ₐ[A₀] A₁ ⊗[A₀] A) b)
  rw [← map_mul]
  refine congrArg (UniformSpace.Completion.coeRingHom : (A₁ ⊗[A₀] A) →+*
    TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)) ?_
  rw [Algebra.TensorProduct.includeLeftRingHom_apply,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul]
  simp

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- A continuous endomorphism of `A₁ ⊗̂_{A₀} A` fixing the images of both factors is the
identity: the elementary tensors are products of such images, and they are dense. -/
private theorem eq_id_of_comp_algebraMap_eq
    (ψ : (TopologicalRing.CompletedTensorProduct
        (R := A₀) (M := A₁) (N := A)) →+* (TopologicalRing.CompletedTensorProduct
            (R := A₀) (M := A₁) (N := A))) (hψ : Continuous ψ)
    (h1 : ψ.comp (algebraMap A₁ (TopologicalRing.CompletedTensorProduct
        (R := A₀) (M := A₁) (N := A))) = algebraMap A₁ (TopologicalRing.CompletedTensorProduct
            (R := A₀) (M := A₁) (N := A)))
    (h2 : ψ.comp (algebraMap A (TopologicalRing.CompletedTensorProduct
        (R := A₀) (M := A₁) (N := A))) = algebraMap A (TopologicalRing.CompletedTensorProduct
            (R := A₀) (M := A₁) (N := A))) :
    ψ = RingHom.id _ := by
  let : UniformSpace (A₁ ⊗[A₀] A) :=
    TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A)
  refine RingHom.ext fun x => ?_
  refine UniformSpace.Completion.induction_on x (isClosed_eq hψ continuous_id) ?_
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp [UniformSpace.Completion.coe_zero]
  | tmul a b =>
    have e1 : ψ (algebraMap A₁ (TopologicalRing.CompletedTensorProduct
        (R := A₀) (M := A₁) (N := A)) a) =
        algebraMap A₁ (TopologicalRing.CompletedTensorProduct
            (R := A₀) (M := A₁) (N := A)) a := RingHom.congr_fun h1 a
    have e2 : ψ (algebraMap A (TopologicalRing.CompletedTensorProduct
        (R := A₀) (M := A₁) (N := A)) b) =
        algebraMap A (TopologicalRing.CompletedTensorProduct
            (R := A₀) (M := A₁) (N := A)) b := RingHom.congr_fun h2 b
    rw [coe_tmul_eq_mul a b, map_mul, e1, e2]
    rfl
  | add z w hz hw =>
    rw [UniformSpace.Completion.coe_add, map_add, hz, hw]
    rfl

/-- The weak ideal of definition of `A₁` through which a weak ideal of definition `K` of
`A₁ ⊗̂_{A₀} A` is accounted for: the intersection of a fixed one with the preimage of `K`.
Monotone in `K`, which is what makes the quotient stages of the completed tensor product
compatible over `S`. -/
private def leftWeakIdeal (h₁ : TopologicalRing.IsWeaklyAdmissible A₁)
    (K : {I : Ideal (TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A)) // TopologicalRing.IsWeakIdealOfDefinition I}) :
    {I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I} :=
  ⟨h₁.1.choose ⊓ Ideal.comap (algebraMap A₁ _) K.1,
    ⟨by
      change IsOpen ((h₁.1.choose : Set A₁) ∩
        (algebraMap A₁ (TopologicalRing.CompletedTensorProduct
          (R := A₀) (M := A₁) (N := A))) ⁻¹' (K.1 : Set _))
      exact h₁.1.choose_spec.1.inter
        (K.2.1.preimage continuous_algebraMap_completedTensorProduct_left),
      fun _ hx => h₁.1.choose_spec.2 _ (Ideal.mem_inf.mp hx).1⟩⟩

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
private theorem leftWeakIdeal_mono (h₁ : TopologicalRing.IsWeaklyAdmissible A₁)
    {K L : {I : Ideal (TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A)) // TopologicalRing.IsWeakIdealOfDefinition I}}
    (h : K.1 ≤ L.1) : (leftWeakIdeal h₁ K).1 ≤ (leftWeakIdeal h₁ L).1 :=
  inf_le_inf le_rfl (Ideal.comap_mono h)

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- Every quotient of `A₁ ⊗̂_{A₀} A` by a weak ideal of definition has its spectrum in the
site. This is the ring computation of clause (3) of **Stacks 0AN3**: the ideal contains a
projection kernel by `TopologicalRing.exists_weakIdealProjectionKernel_le`, and the quotient by
that kernel is the ordinary tensor product `A₁ ⧸ I ⊗_{A₀} A ⧸ J` of two stages by
`TopologicalRing.quotientWeakIdealProjectionKernelRingEquiv`, whose spectrum is contained in
the site. -/
private theorem contains_spec_quotient_completedTensorProduct
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D₁ : QuotientSystem B S hS A₁) (D : QuotientSystem B S hS A)
    (K : {I : Ideal (TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A)) // TopologicalRing.IsWeakIdealOfDefinition I}) :
    B.Contains (Spec (.of (TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A) ⧸ K.1))) := by
  classical
  obtain ⟨i, j, hij⟩ :=
    TopologicalRing.exists_weakIdealProjectionKernel_le (B := A₀) h₁ hA K.2
  have hsurj : Function.Surjective ((Ideal.Quotient.factor hij).comp
      (TopologicalRing.quotientWeakIdealProjectionKernelRingEquiv
        (B := A₀) h₁ hA i j).symm.toRingHom) :=
    (surjective_quotient_factor hij).comp
      (TopologicalRing.quotientWeakIdealProjectionKernelRingEquiv
        (B := A₀) h₁ hA i j).symm.surjective
  exact lt_of_le_of_lt (spec_size_le_of_surjective_ringHom _ hsurj)
    (B.contains_spec_tensorProduct (R := A₀) (D₁.inSite i) (D.inSite j))

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The weak ideal of definition of `A₁` chosen for `K` does map into `K`. -/
private theorem leftWeakIdeal_le (h₁ : TopologicalRing.IsWeaklyAdmissible A₁)
    (K : {I : Ideal (TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A)) // TopologicalRing.IsWeakIdealOfDefinition I}) :
    (leftWeakIdeal h₁ K).1 ≤ Ideal.comap (algebraMap A₁
      (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A))) K.1 :=
  inf_le_right

/-- The structure morphism to `S` of the quotient stage of `A₁ ⊗̂_{A₀} A` at a weak ideal of
definition: the stage maps to the stage of `Spf A₁` at `leftWeakIdeal`, which maps to `S`. -/
private def completedTensorOverS (h₁ : TopologicalRing.IsWeaklyAdmissible A₁)
    (D₁ : QuotientSystem B S hS A₁)
    (K : {I : Ideal (TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A)) // TopologicalRing.IsWeakIdealOfDefinition I}) :
    Spec (.of (TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A) ⧸ K.1)) ⟶ S :=
  Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap K.1 (algebraMap A₁ _) (leftWeakIdeal_le h₁ K))) ≫
    D₁.overS (leftWeakIdeal h₁ K)

/-- **The quotient system of a completed tensor product**, the first half of clause (3) of
**Stacks 0AN3**: the quotient stages of `A₁ ⊗̂_{A₀} A` are objects of the site, compatibly over
`S`. -/
private def completedTensorQuotientSystem
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D₁ : QuotientSystem B S hS A₁) (D : QuotientSystem B S hS A) :
    QuotientSystem B S hS
      (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)) where
  inSite K := contains_spec_quotient_completedTensorProduct B S hS h₁ hA D₁ D K
  overS K := completedTensorOverS B S hS h₁ D₁ K
  compatible K L h := by
    have hmono := leftWeakIdeal_mono h₁ h
    have key := factor_comp_quotientMap_comp_factor
      (algebraMap A₁ (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)))
      hmono h (leftWeakIdeal_le h₁ K) (leftWeakIdeal_le h₁ L)
    have hD := D₁.compatible (leftWeakIdeal h₁ K) (leftWeakIdeal h₁ L) hmono
    unfold completedTensorOverS
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, key,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hD]

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
private theorem completedTensorQuotientSystem_overS
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D₁ : QuotientSystem B S hS A₁) (D : QuotientSystem B S hS A)
    (K : {I : Ideal (TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A)) // TopologicalRing.IsWeakIdealOfDefinition I}) :
    (completedTensorQuotientSystem (A₀ := A₀) B S hS h₁ hA D₁ D).overS K =
      completedTensorOverS B S hS h₁ D₁ K :=
  rfl

/-- The canonical map `A₁ → A₁ ⊗̂_{A₀} A` as a continuous hom of chart systems over `S`. -/
private def completedTensorLeftHom
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D₁ : QuotientSystem B S hS A₁) (D : QuotientSystem B S hS A) :
    ContinuousHom D₁ (completedTensorQuotientSystem (A₀ := A₀) B S hS h₁ hA D₁ D) :=
  continuousHomOfStages B S hS D₁ (completedTensorQuotientSystem (A₀ := A₀) B S hS h₁ hA D₁ D)
    (algebraMap A₁ (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)))
    continuous_algebraMap_completedTensorProduct_left
    fun K => ⟨leftWeakIdeal h₁ K, leftWeakIdeal_le h₁ K, rfl⟩

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
private theorem completedTensorLeftHom_toRingHom
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D₁ : QuotientSystem B S hS A₁) (D : QuotientSystem B S hS A) :
    (completedTensorLeftHom B S hS h₁ hA D₁ D).toRingHom = algebraMap A₁
      (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)) :=
  rfl

/-- The canonical map `A → A₁ ⊗̂_{A₀} A` as a continuous hom of chart systems over `S`. Its
compatibility with the structure morphisms to `S` is the one place where the two factors have to
be compared, and they are compared through the base: both routes from a stage of
`A₁ ⊗̂_{A₀} A` to `S` factor through a stage of `A₀`, along the same ring map. -/
private def completedTensorRightHom
    (h₀ : TopologicalRing.IsWeaklyAdmissible A₀)
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D₀ : QuotientSystem B S hS A₀)
    (D₁ : QuotientSystem B S hS A₁) (D : QuotientSystem B S hS A)
    (c₁ : ContinuousHom D₀ D₁) (c : ContinuousHom D₀ D)
    (hc₁ : c₁.toRingHom = algebraMap A₀ A₁) (hc : c.toRingHom = algebraMap A₀ A) :
    ContinuousHom D (completedTensorQuotientSystem (A₀ := A₀) B S hS h₁ hA D₁ D) :=
  continuousHomOfStages B S hS D (completedTensorQuotientSystem (A₀ := A₀) B S hS h₁ hA D₁ D)
    (algebraMap A (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)))
    continuous_algebraMap_completedTensorProduct_right (by
      intro K
      have hbase : (algebraMap A (TopologicalRing.CompletedTensorProduct
            (R := A₀) (M := A₁) (N := A))).comp c.toRingHom =
          (algebraMap A₁ (TopologicalRing.CompletedTensorProduct
            (R := A₀) (M := A₁) (N := A))).comp c₁.toRingHom := by
        rw [hc, hc₁, algebraMap_completedTensorProduct_base]
      obtain ⟨j, hjw, hj⟩ := exists_weakIdeal_comap_subset
        (algebraMap A (TopologicalRing.CompletedTensorProduct
          (R := A₀) (M := A₁) (N := A)))
        continuous_algebraMap_completedTensorProduct_right hA K.2
      refine ⟨⟨j, hjw⟩, hj, ?_⟩
      obtain ⟨k₂, hk₂, e₂⟩ := exists_overS_route_through_base B S hS h₀ D₀ D c
        (algebraMap A (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)))
        ⟨j, hjw⟩ hj
      obtain ⟨k₁, hk₁, e₁⟩ := exists_overS_route_through_base B S hS h₀ D₀ D₁ c₁
        (algebraMap A₁ (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)))
        (leftWeakIdeal h₁ K) (leftWeakIdeal_le h₁ K)
      have hk₂' : k₂.1 ≤ Ideal.comap ((algebraMap A₁ (TopologicalRing.CompletedTensorProduct
          (R := A₀) (M := A₁) (N := A))).comp c₁.toRingHom) K.1 := hbase ▸ hk₂
      rw [e₂, quotientMap_congr hbase hk₂ hk₂',
        spec_quotientMap_overS_eq B S hS D₀ _ hk₂' hk₁, ← e₁]
      rfl)

private theorem completedTensorRightHom_toRingHom
    (h₀ : TopologicalRing.IsWeaklyAdmissible A₀)
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D₀ : QuotientSystem B S hS A₀)
    (D₁ : QuotientSystem B S hS A₁) (D : QuotientSystem B S hS A)
    (c₁ : ContinuousHom D₀ D₁) (c : ContinuousHom D₀ D)
    (hc₁ : c₁.toRingHom = algebraMap A₀ A₁) (hc : c.toRingHom = algebraMap A₀ A) :
    (completedTensorRightHom B S hS h₀ h₁ hA D₀ D₁ D c₁ c hc₁ hc).toRingHom =
      algebraMap A (TopologicalRing.CompletedTensorProduct
        (R := A₀) (M := A₁) (N := A)) :=
  rfl

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀]
  [IsTopologicalRing A₁] [IsLinearTopology A₁ A₁] [IsTopologicalRing A] [IsLinearTopology A A] in
/-- The lift of two continuous homomorphisms to a tensor product is continuous for the tensor
product topology. -/
@[ega "0 7.7.6"]
private theorem continuous_tensorProduct_lift {R : Type u} [CommRing R]
    [Algebra A₀ R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (f : A₁ →ₐ[A₀] R) (g : A →ₐ[A₀] R) (hf : Continuous f) (hg : Continuous g) :
    letI := TopologicalRing.tensorProductTopology (R := A₀) (M := A₁) (N := A)
    Continuous (Algebra.TensorProduct.lift f g fun _ _ => Commute.all _ _) := by
  let := TopologicalRing.tensorProductTopology (R := A₀) (M := A₁) (N := A)
  let l := Algebra.TensorProduct.lift f g fun _ _ => Commute.all _ _
  apply continuous_of_continuousAt_zero l
  change Filter.Tendsto l (nhds 0) (nhds (l 0))
  rw [map_zero]
  refine ((TopologicalRing.hasBasis_tensorProductTopology (R := A₀) (M := A₁)
    (N := A)).tendsto_iff IsLinearTopology.hasBasis_open_ideal).mpr ?_
  intro K hK
  let I := Ideal.comap f.toRingHom K
  let J := Ideal.comap g.toRingHom K
  refine ⟨(⟨I.restrictScalars A₀, hK.preimage hf⟩,
      ⟨J.restrictScalars A₀, hK.preimage hg⟩), trivial, ?_⟩
  intro z hz
  rcases Submodule.mem_sup.mp hz with ⟨x, ⟨x, rfl⟩, y, ⟨y, rfl⟩, rfl⟩
  clear hz
  rw [map_add]
  apply K.add_mem
  · induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simpa [l, Algebra.TensorProduct.lift_tmul, mul_comm] using K.mul_mem_left (g b) a.2
    | add x y hx hy => simpa only [map_add] using K.add_mem hx hy
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simpa [l, Algebra.TensorProduct.lift_tmul] using K.mul_mem_left (f a) b.2
    | add x y hx hy => simpa only [map_add] using K.add_mem hx hy

/-- **Stacks 0AN3, clause (3).** Let `A₀`, `A₁` and `A` be weakly admissible topological rings
over `S` with chart systems `D₀`, `D₁`, `D`, and let `A₀ → A₁` and `A₀ → A` be continuous
homomorphisms over `S`. If the fibre product `Spf A₁ ×_{Spf A₀} Spf A` is itself the formal
spectrum of a weakly admissible topological ring over `S`, then it is the formal spectrum of the
completed tensor product `A₁ ⊗̂_{A₀} A`: that ring carries a chart system over `S` and an
isomorphism onto the fibre product compatible with both projections, through which the two
projections are the formal spectra of the two canonical maps into the completed tensor
product. -/
@[stacks 0AN3 "clause (3), that the fibre product of two McQuillan affine formal algebraic \
spaces over a third is the formal spectrum of the completed tensor product of their weakly \
admissible topological rings, compatibly with both projections. The quotient system on the \
completed tensor product and the comparison with the fibre product are proved. The one input \
this library does not carry is the hypothesis epres: that the fibre product is itself a formal \
spectrum, which is clause (2) of the same tag together with the McQuillan criterion of Stacks \
0AIC. Stacks 0AN0 is full faithfulness of Spf against formal spectra only \
(existsUnique_continuousHom_formalSpectrumMap_eq), not a universal property against arbitrary \
fppf sheaves, so representability of the fibre product is not a consequence of it; \
separatedness of the base, which the source uses only to obtain clauses (1) and (2), is \
therefore not needed here and is not assumed"]
theorem exists_quotientSystem_iso_pullback_completedTensorProduct
    (h₀ : TopologicalRing.IsWeaklyAdmissible A₀)
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D₀ : QuotientSystem B S hS A₀) (D₁ : QuotientSystem B S hS A₁)
    (D : QuotientSystem B S hS A)
    (c₁ : ContinuousHom D₀ D₁) (c : ContinuousHom D₀ D)
    (hc₁ : c₁.toRingHom = algebraMap A₀ A₁) (hc : c.toRingHom = algebraMap A₀ A)
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : TopologicalRing.IsWeaklyAdmissible R) (E : QuotientSystem B S hS R)
    (epres : pullback (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c) ≅ formalSpectrum E) :
    ∃ (DT : QuotientSystem B S hS (TopologicalRing.CompletedTensorProduct
        (R := A₀) (M := A₁) (N := A)))
        (t₁ : ContinuousHom D₁ DT) (t : ContinuousHom D DT)
        (eT : pullback (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c) ≅ formalSpectrum DT),
      t₁.toRingHom = algebraMap A₁ (TopologicalRing.CompletedTensorProduct
          (R := A₀) (M := A₁) (N := A)) ∧
        t.toRingHom = algebraMap A (TopologicalRing.CompletedTensorProduct
            (R := A₀) (M := A₁) (N := A)) ∧
        eT.hom ≫ formalSpectrumMap h₁ t₁ =
          pullback.fst (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c) ∧
        eT.hom ≫ formalSpectrumMap hA t =
          pullback.snd (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c) := by
  classical
  have hT : TopologicalRing.IsWeaklyAdmissible (TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A)) :=
    TopologicalRing.completedTensorProduct_isWeaklyAdmissible (B := A₀) h₁.1 hA.1
  set DT := completedTensorQuotientSystem (A₀ := A₀) B S hS h₁ hA D₁ D with hDT
  set t₁ := completedTensorLeftHom (A₀ := A₀) B S hS h₁ hA D₁ D with ht₁
  set t := completedTensorRightHom B S hS h₀ h₁ hA D₀ D₁ D c₁ c hc₁ hc with ht
  have ht₁r : t₁.toRingHom = algebraMap A₁ (TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A)) := rfl
  have htr : t.toRingHom = algebraMap A (TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A)) := rfl
  set cT : ContinuousHom D₀ DT := ContinuousHom.comp h₁ h₀ t₁ c₁ with hcTdef
  have hcT₁ : cT.toRingHom = t₁.toRingHom.comp c₁.toRingHom := rfl
  have hcT : cT.toRingHom = t.toRingHom.comp c.toRingHom := by
    rw [hcT₁, ht₁r, htr, hc₁, hc, algebraMap_completedTensorProduct_base]
  have hcomm : formalSpectrumMap h₁ t₁ ≫ formalSpectrumMap h₀ c₁ =
      formalSpectrumMap hA t ≫ formalSpectrumMap h₀ c := by
    rw [formalSpectrumMap_comp h₀ h₁ c₁ t₁ cT hcT₁, formalSpectrumMap_comp h₀ hA c t cT hcT]
  set p : formalSpectrum DT ⟶
      pullback (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c) :=
    pullback.lift (formalSpectrumMap h₁ t₁) (formalSpectrumMap hA t) hcomm with hp
  obtain ⟨a₁, ha₁, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq h₁ hR
    (epres.inv ≫ pullback.fst (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c))
  obtain ⟨a, ha, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA hR
    (epres.inv ≫ pullback.snd (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c))
  have hab : a₁.toRingHom.comp (algebraMap A₀ A₁) = a.toRingHom.comp (algebraMap A₀ A) := by
    have := toRingHom_comp_eq_of_formalSpectrumMap_sq h₁ h₀ hR hA a₁ c c₁ a _ _ rfl rfl
      (by rw [ha₁, ha, Category.assoc, Category.assoc, pullback.condition])
    rwa [hc₁, hc] at this
  let : Algebra A₀ R := (a₁.toRingHom.comp (algebraMap A₀ A₁)).toAlgebra
  set aAlg : A₁ →ₐ[A₀] R := { toRingHom := a₁.toRingHom, commutes' := fun _ => rfl } with haAlg
  set bAlg : A →ₐ[A₀] R :=
    { toRingHom := a.toRingHom, commutes' := fun x => (RingHom.congr_fun hab x).symm } with hbAlg
  let : UniformSpace (A₁ ⊗[A₀] A) :=
    TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A)
  set l := Algebra.TensorProduct.lift aAlg bAlg (fun _ _ => Commute.all _ _) with hl
  have hlcont : Continuous l := continuous_tensorProduct_lift aAlg bAlg a₁.continuous a.continuous
  let : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  let : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  let : CompleteSpace R := hR.2.1
  let : T2Space R := hR.2.2
  set tR : (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)) →+* R :=
    UniformSpace.Completion.extensionHom l.toRingHom hlcont with htRdef
  have htRcont : Continuous tR := UniformSpace.Completion.continuous_extension
  have hta : tR.comp (algebraMap A₁ (TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A))) = a₁.toRingHom := by
    refine RingHom.ext fun x => ?_
    change tR ((x ⊗ₜ[A₀] (1 : A) : A₁ ⊗[A₀] A) : (TopologicalRing.CompletedTensorProduct
        (R := A₀) (M := A₁) (N := A))) = _
    rw [htRdef, UniformSpace.Completion.extensionHom_coe]
    change aAlg x * bAlg 1 = _
    rw [map_one, mul_one]
    rfl
  have htb : tR.comp (algebraMap A (TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A))) = a.toRingHom := by
    refine RingHom.ext fun x => ?_
    change tR (((1 : A₁) ⊗ₜ[A₀] x : A₁ ⊗[A₀] A) : (TopologicalRing.CompletedTensorProduct
        (R := A₀) (M := A₁) (N := A))) = _
    rw [htRdef, UniformSpace.Completion.extensionHom_coe]
    change aAlg 1 * bAlg x = _
    rw [map_one, one_mul]
    rfl
  set tHom : ContinuousHom DT E :=
    continuousHomOfComp B S hS h₁ t₁ a₁ tR htRcont hta.symm with htHom
  set q : pullback (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c) ⟶ formalSpectrum DT :=
    epres.hom ≫ formalSpectrumMap hT tHom with hq
  have hqfst : q ≫ formalSpectrumMap h₁ t₁ =
      pullback.fst (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c) := by
    rw [hq, Category.assoc, formalSpectrumMap_comp h₁ hT t₁ tHom a₁ hta.symm, ha₁,
      Iso.hom_inv_id_assoc]
  have hqsnd : q ≫ formalSpectrumMap hA t =
      pullback.snd (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c) := by
    rw [hq, Category.assoc, formalSpectrumMap_comp hA hT t tHom a htb.symm, ha,
      Iso.hom_inv_id_assoc]
  have hqp : q ≫ p = 𝟙 _ := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hp, pullback.lift_fst, hqfst, Category.id_comp]
    · rw [Category.assoc, hp, pullback.lift_snd, hqsnd, Category.id_comp]
  have hpq : p ≫ q = 𝟙 _ := by
    obtain ⟨w, hw, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hT hT (p ≫ q)
    have hwid : w.toRingHom = RingHom.id _ := by
      refine eq_id_of_comp_algebraMap_eq w.toRingHom w.continuous ?_ ?_
      · rw [← ht₁r]
        exact toRingHom_comp_eq_of_formalSpectrumMap_comp_eq hT hT h₁ w t₁ t₁
          (by rw [hw, Category.assoc, hqfst, hp, pullback.lift_fst])
      · rw [← htr]
        exact toRingHom_comp_eq_of_formalSpectrumMap_comp_eq hT hT hA w t t
          (by rw [hw, Category.assoc, hqsnd, hp, pullback.lift_snd])
    rw [← hw, formalSpectrumMap_id hT w hwid]
  exact ⟨DT, t₁, t, ⟨q, p, hqp, hpq⟩, ht₁r, htr, hqfst, hqsnd⟩

/-- **Stacks 0AN3, clause (3), in the form of an isomorphism of chart rings.** If the fibre
product `Spf A₁ ×_{Spf A₀} Spf A` is the formal spectrum of a weakly admissible topological
ring `R` over `S`, then `R` is isomorphic, as a topological ring, to the completed tensor
product `A₁ ⊗̂_{A₀} A`, compatibly with the two projections: the isomorphism carries each of the
two canonical maps into the completed tensor product to the continuous homomorphism that
Stacks 0AN0 attaches to the corresponding projection. -/
@[stacks 0AN3 "clause (3) read on chart rings: the chart ring of the fibre product of two \
McQuillan affine formal algebraic spaces over a third is the completed tensor product of their \
weakly admissible topological rings, by an isomorphism of topological rings compatible with \
both projections. The one input this library does not carry is the hypothesis epres, that the \
fibre product is itself a formal spectrum, which is clause (2) of the same tag together with \
the McQuillan criterion of Stacks 0AIC; Stacks 0AN0 is full faithfulness of Spf against formal \
spectra only, so representability of the fibre product does not follow from it. Separatedness \
of the base, which the source uses only for clauses (1) and (2), is not needed here and is not \
assumed"]
theorem exists_continuous_ringEquiv_completedTensorProduct_pullback
    (h₀ : TopologicalRing.IsWeaklyAdmissible A₀)
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D₀ : QuotientSystem B S hS A₀) (D₁ : QuotientSystem B S hS A₁)
    (D : QuotientSystem B S hS A)
    (c₁ : ContinuousHom D₀ D₁) (c : ContinuousHom D₀ D)
    (hc₁ : c₁.toRingHom = algebraMap A₀ A₁) (hc : c.toRingHom = algebraMap A₀ A)
    {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : TopologicalRing.IsWeaklyAdmissible R) (E : QuotientSystem B S hS R)
    (epres : pullback (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c) ≅ formalSpectrum E) :
    ∃ ε : (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)) ≃+* R,
      Continuous ε ∧ Continuous ε.symm ∧
        ∀ (a₁ : ContinuousHom D₁ E) (a : ContinuousHom D E),
          formalSpectrumMap h₁ a₁ = epres.inv ≫
              pullback.fst (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c) →
            formalSpectrumMap hA a = epres.inv ≫
              pullback.snd (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c) →
            ε.toRingHom.comp (algebraMap A₁ (TopologicalRing.CompletedTensorProduct
                (R := A₀) (M := A₁) (N := A))) = a₁.toRingHom ∧
              ε.toRingHom.comp (algebraMap A (TopologicalRing.CompletedTensorProduct
                  (R := A₀) (M := A₁) (N := A))) = a.toRingHom := by
  have hT : TopologicalRing.IsWeaklyAdmissible (TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A)) :=
    TopologicalRing.completedTensorProduct_isWeaklyAdmissible (B := A₀) h₁.1 hA.1
  obtain ⟨DT, t₁, t, eT, ht₁r, htr, hfst, hsnd⟩ :=
    exists_quotientSystem_iso_pullback_completedTensorProduct
      B S hS h₀ h₁ hA D₀ D₁ D c₁ c hc₁ hc hR E epres
  obtain ⟨g, -, φ, hg, -, hφ, -, hφcont, hφsymmcont⟩ :=
    exists_continuous_ringEquiv_of_formalSpectrum_iso hT hR (epres.symm ≪≫ eT)
  have hφring : φ.toRingHom = g.toRingHom := RingHom.ext fun x => congrFun hφ x
  have hghom : formalSpectrumMap hT g = epres.inv ≫ eT.hom := hg
  refine ⟨φ, hφcont, hφsymmcont, fun a₁ a hfa hsa ↦ ⟨?_, ?_⟩⟩
  · rw [hφring, ← ht₁r]
    exact toRingHom_comp_eq_of_formalSpectrumMap_comp_eq hR hT h₁ g t₁ a₁
      (by rw [hghom, hfa, Category.assoc, hfst])
  · rw [hφring, ← htr]
    exact toRingHom_comp_eq_of_formalSpectrumMap_comp_eq hR hT hA g t a
      (by rw [hghom, hsa, Category.assoc, hsnd])

end

/-! ### Clause (3) of Stacks 0AN3 with no presentation of the fibre product assumed -/

section Presentation

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- If the composites of `f` and `g` with an epimorphism `h` form a pushout square, then so do
`f` and `g` themselves. -/
private theorem isPushout_of_epi_comp {C : Type*} [Category C] {W X Y Z P : C}
    {h : W ⟶ X} [Epi h] {f : X ⟶ Y} {g : X ⟶ Z} {inl : Y ⟶ P} {inr : Z ⟶ P}
    (H : IsPushout (h ≫ f) (h ≫ g) inl inr) (w : f ≫ inl = g ≫ inr) :
    IsPushout f g inl inr :=
  IsPushout.of_isColimit' ⟨w⟩ (PushoutCocone.isColimitAux' _ fun s ↦
    ⟨H.desc s.inl s.inr (by rw [Category.assoc, Category.assoc, s.condition]),
      H.inl_desc _ _ _, H.inr_desc _ _ _, fun h₁ h₂ ↦ H.hom_ext
        (h₁.trans (H.inl_desc _ _ _).symm) (h₂.trans (H.inr_desc _ _ _).symm)⟩)

/-- A pullback square stays a pullback square after composing its two lower edges with a
monomorphism. -/
private theorem isPullback_comp_mono {C : Type*} [Category C] {P X Y W Z : C}
    {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ W} {g : Y ⟶ W} (h : IsPullback fst snd f g)
    (m : W ⟶ Z) [Mono m] : IsPullback fst snd (f ≫ m) (g ≫ m) :=
  IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono f g m _ h.isLimit)

variable {B S hS}

/-- Every stage of the formal spectrum of a weakly admissible ring includes into it as a
monomorphism: the transition maps of the canonical diagram are the represented sheaves of
closed immersions, and a filtered colimit of sheaves of sets along monomorphisms has
monomorphic coprojections. -/
theorem mono_formalSpectrumInclusion_of_isWeaklyAdmissible {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [IsLinearTopology R R]
    (hR : TopologicalRing.IsWeaklyAdmissible R) (D : QuotientSystem B S hS R)
    (J : WeakIdeals R) : Mono (formalSpectrumInclusion D J) := by
  obtain ⟨_, _⟩ := nonempty_directed_weakIdeals hR
  refine Sheaf.mono_colimit_ι_of_mono_transition (formalSpectrumDiagram D)
    (fun K L f ↦ ?_) J
  have hclosed : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (D.diagram.map f))) := by
    change _root_.AlgebraicGeometry.IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.factor (show L.1 ≤ K.1 from leOfHom f))))
    exact _root_.AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _
      (Ideal.Quotient.factor_surjective (show L.1 ≤ K.1 from leOfHom f))
  have := faithful_toScheme B S hS
  have : Mono ((BigAffineFppf.inclusion B S hS).map (D.diagram.map f)) :=
    (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  have := preservesLimitsOfShape_sheafifiedYoneda B S hS
  exact (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map_mono
    ((BigAffineFppf.inclusion B S hS).map (D.diagram.map f))

/-- An elementary tensor with a factor in the corresponding weak ideal of definition lies in the
projection kernel. -/
private theorem coe_tmul_mem_weakIdealProjectionKernel
    {A₀ A₁ A : Type u} [CommRing A₀] [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁]
    [IsLinearTopology A₁ A₁] [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] [Algebra A₀ A₁] [Algebra A₀ A]
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (i : {I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I})
    (j : {I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I}) (a : A₁) (b : A)
    (h : a ∈ i.1 ∨ b ∈ j.1) :
    letI : UniformSpace (A₁ ⊗[A₀] A) :=
      TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A)
    ((a ⊗ₜ[A₀] b : A₁ ⊗[A₀] A) : TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A)) ∈
        TopologicalRing.weakIdealProjectionKernel (B := A₀) h₁ hA i j := by
  let := TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A)
  change TopologicalRing.projectionRingHom (B := A₀) (fun i ↦ i.1) (fun j ↦ j.1)
    (TopologicalRing.hasBasis_isWeakIdealOfDefinition_subtype h₁)
    (TopologicalRing.hasBasis_isWeakIdealOfDefinition_subtype hA) i j
    (((a ⊗ₜ[A₀] b : A₁ ⊗[A₀] A) : TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A))) = 0
  rw [TopologicalRing.projectionRingHom_coe, Algebra.TensorProduct.map_tmul]
  rcases h with h | h <;> simp [Ideal.Quotient.eq_zero_iff_mem.mpr h]

variable {A₀ A₁ A : Type u}
  [CommRing A₀] [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀]
  [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁] [IsLinearTopology A₁ A₁]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
  [Algebra A₀ A₁] [Algebra A₀ A]

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The projection kernels of `A₁ ⊗̂_{A₀} A` grow with the two weak ideals cutting them out. -/
private theorem weakIdealProjectionKernel_mono
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    {i i' : {I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I}}
    {j j' : {I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I}}
    (hi : i.1 ≤ i'.1) (hj : j.1 ≤ j'.1) :
    TopologicalRing.weakIdealProjectionKernel (B := A₀) h₁ hA i j ≤
      TopologicalRing.weakIdealProjectionKernel (B := A₀) h₁ hA i' j' := by
  let := TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A)
  have e := TopologicalRing.projectionKernel_eq_closure (B := A₀)
    (fun i : {I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I} ↦ i.1)
    (fun j : {I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I} ↦ j.1)
    (TopologicalRing.hasBasis_isWeakIdealOfDefinition_subtype h₁)
    (TopologicalRing.hasBasis_isWeakIdealOfDefinition_subtype hA)
  rw [← SetLike.coe_subset_coe]
  refine (e i j).trans_subset (subset_of_subset_of_eq ?_ (e i' j').symm)
  rw [Ideal.coe_closure, Ideal.coe_closure]
  exact closure_mono (add_le_add (Ideal.map_mono hi) (Ideal.map_mono hj))

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- A weak ideal of definition of `A₁` maps into the projection kernel it cuts out. -/
private theorem le_comap_weakIdealProjectionKernel_left
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (i : {I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I})
    (j : {I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I}) :
    i.1 ≤ Ideal.comap (algebraMap A₁ (TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A)))
      (TopologicalRing.weakIdealProjectionKernel (B := A₀) h₁ hA i j) :=
  fun _ hx ↦ coe_tmul_mem_weakIdealProjectionKernel h₁ hA i j _ 1 (Or.inl hx)

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- A weak ideal of definition of `A` maps into the projection kernel it cuts out. -/
private theorem le_comap_weakIdealProjectionKernel_right
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (i : {I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I})
    (j : {I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I}) :
    j.1 ≤ Ideal.comap (algebraMap A (TopologicalRing.CompletedTensorProduct
      (R := A₀) (M := A₁) (N := A)))
      (TopologicalRing.weakIdealProjectionKernel (B := A₀) h₁ hA i j) :=
  fun _ hx ↦ coe_tmul_mem_weakIdealProjectionKernel h₁ hA i j 1 _ (Or.inr hx)

/-- The weak ideal of definition of `A₁ ⊗̂_{A₀} A` cut out by a pair of weak ideals of
definition of `A₁` and of `A`, read in the index of the quotient stages. -/
private noncomputable def kernelWeakIdeal
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (k : WeakIdeals A₁ × WeakIdeals A) :
    WeakIdeals (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)) :=
  OrderDual.toDual ⟨TopologicalRing.weakIdealProjectionKernel (B := A₀) h₁ hA
      (OrderDual.ofDual k.1) (OrderDual.ofDual k.2),
    TopologicalRing.weakIdealProjectionKernel_isWeakIdealOfDefinition (B := A₀) h₁ hA _ _⟩

/-- The projection kernels of `A₁ ⊗̂_{A₀} A` as a functor on pairs of weak ideals of definition
of `A₁` and of `A`. -/
private noncomputable def kernelWeakIdealFunctor
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A) :
    WeakIdeals A₁ × WeakIdeals A ⥤
      WeakIdeals (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)) where
  obj := kernelWeakIdeal h₁ hA
  map f := homOfLE (weakIdealProjectionKernel_mono h₁ hA (leOfHom f.1) (leOfHom f.2))

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- The quotient stages of `Spf (A₁ ⊗̂_{A₀} A)` cut out by the projection kernels are cofinal
among all its quotient stages. -/
private theorem final_kernelWeakIdealFunctor
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    [IsFilteredOrEmpty (WeakIdeals A₁ × WeakIdeals A)] :
    (kernelWeakIdealFunctor (A₀ := A₀) h₁ hA).Final := by
  refine Functor.final_of_exists_of_isFiltered _ (fun d ↦ ?_) fun {d c} s s' ↦
    ⟨c, 𝟙 c, Subsingleton.elim _ _⟩
  obtain ⟨i, j, hij⟩ := TopologicalRing.exists_weakIdealProjectionKernel_le (B := A₀) h₁ hA
    (OrderDual.ofDual d).2
  exact ⟨(OrderDual.toDual i, OrderDual.toDual j), ⟨homOfLE hij⟩⟩

omit [TopologicalSpace A₀] [IsTopologicalRing A₀] [IsLinearTopology A₀ A₀] in
/-- **The stage square of a fibre product of formal spectra, on rings.** For weak ideals of
definition `I` of `A₁` and `J` of `A`, and an ideal `k` of `A₀` mapping into both, the quotient
of `A₁ ⊗̂_{A₀} A` by the projection kernel of `(I, J)` is the pushout of `A₁ ⧸ I` and `A ⧸ J`
over `A₀ ⧸ k`: it is the tensor product `A₁ ⧸ I ⊗_{A₀} A ⧸ J`, and the tensor product over
`A₀` is the one over `A₀ ⧸ k`, the quotient map `A₀ → A₀ ⧸ k` being an epimorphism. -/
private theorem isPushout_quotient_weakIdealProjectionKernel
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (k : Ideal A₀) (i : {I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I})
    (j : {I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I})
    (hk₁ : k ≤ Ideal.comap (algebraMap A₀ A₁) i.1) (hk : k ≤ Ideal.comap (algebraMap A₀ A) j.1) :
    IsPushout (CommRingCat.ofHom (Ideal.quotientMap i.1 (algebraMap A₀ A₁) hk₁))
      (CommRingCat.ofHom (Ideal.quotientMap j.1 (algebraMap A₀ A) hk))
      (CommRingCat.ofHom (Ideal.quotientMap
        (TopologicalRing.weakIdealProjectionKernel (B := A₀) h₁ hA i j)
        (algebraMap A₁ (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)))
        (le_comap_weakIdealProjectionKernel_left h₁ hA i j)))
      (CommRingCat.ofHom (Ideal.quotientMap
        (TopologicalRing.weakIdealProjectionKernel (B := A₀) h₁ hA i j)
        (algebraMap A (TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)))
        (le_comap_weakIdealProjectionKernel_right h₁ hA i j))) := by
  let := TopologicalRing.tensorProductUniformSpace (R := A₀) (M := A₁) (N := A)
  have : Epi (CommRingCat.ofHom (Ideal.Quotient.mk k)) :=
    ConcreteCategory.epi_of_surjective _ Ideal.Quotient.mk_surjective
  set e := TopologicalRing.quotientWeakIdealProjectionKernelRingEquiv (B := A₀) h₁ hA i j
    with he
  have he_mk (x : TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)) :
      e (Ideal.Quotient.mk _ x) = TopologicalRing.projectionRingHom (B := A₀)
        (fun i : {I : Ideal A₁ // TopologicalRing.IsWeakIdealOfDefinition I} ↦ i.1)
        (fun j : {I : Ideal A // TopologicalRing.IsWeakIdealOfDefinition I} ↦ j.1)
        (TopologicalRing.hasBasis_isWeakIdealOfDefinition_subtype h₁)
        (TopologicalRing.hasBasis_isWeakIdealOfDefinition_subtype hA) i j x :=
    RingHom.quotientKerEquivOfSurjective_apply_mk
      (TopologicalRing.projectionRingHom_surjective (B := A₀) _ _
        (TopologicalRing.hasBasis_isWeakIdealOfDefinition_subtype h₁)
        (TopologicalRing.hasBasis_isWeakIdealOfDefinition_subtype hA) i j) x
  have hmk (a : A₁) (b : A) : e (Ideal.Quotient.mk _ (((a ⊗ₜ[A₀] b : A₁ ⊗[A₀] A) :
      TopologicalRing.CompletedTensorProduct (R := A₀) (M := A₁) (N := A)))) =
      Ideal.Quotient.mk i.1 a ⊗ₜ[A₀] Ideal.Quotient.mk j.1 b := by
    rw [he_mk, TopologicalRing.projectionRingHom_coe, Algebra.TensorProduct.map_tmul]
    rfl
  refine isPushout_of_epi_comp (h := CommRingCat.ofHom (Ideal.Quotient.mk k)) ?_ ?_
  · refine (CommRingCat.isPushout_tensorProduct A₀ (A₁ ⧸ i.1) (A ⧸ j.1)).of_iso'
      (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toCommRingCatIso ?_ ?_ ?_ ?_
    · ext x; rfl
    · ext x; rfl
    · ext a
      exact (hmk a 1).symm
    · ext a
      exact (hmk 1 a).symm
  · ext a
    exact congrArg (Ideal.Quotient.mk _)
      (RingHom.congr_fun algebraMap_completedTensorProduct_base a)

/-- The stage maps of a continuous homomorphism commute with the transition maps of the two
quotient systems. -/
private theorem transition_comp_stageMap {R Q : Type u} [CommRing R] [TopologicalSpace R]
    [CommRing Q] [TopologicalSpace Q] {D' : QuotientSystem B S hS R}
    {E : QuotientSystem B S hS Q} (f : ContinuousHom D' E)
    {J J' : {I : Ideal R // TopologicalRing.IsWeakIdealOfDefinition I}}
    {K K' : {I : Ideal Q // TopologicalRing.IsWeakIdealOfDefinition I}}
    (hJ : J'.1 ≤ J.1) (hK : K'.1 ≤ K.1) (h : J.1 ≤ Ideal.comap f.toRingHom K.1)
    (h' : J'.1 ≤ Ideal.comap f.toRingHom K'.1) :
    (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (E.transition hK ≫ f.stageMap J' K' h')) =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (f.stageMap J K h ≫ D'.transition hJ)) := by
  congr 2
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hK)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap K'.1 f.toRingHom h')) =
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap K.1 f.toRingHom h)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor hJ))
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ ↦ rfl)

variable (B S hS)

/-- The represented stages of `Spf (A₁ ⊗̂_{A₀} A)` at the projection kernels map to the stages of
`Spf A₁`. -/
private noncomputable def kernelStageLeft
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D₁ : QuotientSystem B S hS A₁) (D : QuotientSystem B S hS A) :
    kernelWeakIdealFunctor (A₀ := A₀) h₁ hA ⋙
        formalSpectrumDiagram (completedTensorQuotientSystem (A₀ := A₀) B S hS h₁ hA D₁ D) ⟶
      CategoryTheory.Prod.fst (WeakIdeals A₁) (WeakIdeals A) ⋙ formalSpectrumDiagram D₁ where
  app k := (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
    ((BigAffineFppf.inclusion B S hS).map
      ((completedTensorLeftHom (A₀ := A₀) B S hS h₁ hA D₁ D).stageMap (OrderDual.ofDual k.1)
        (OrderDual.ofDual (kernelWeakIdeal h₁ hA k))
        (by rw [completedTensorLeftHom_toRingHom]
            exact le_comap_weakIdealProjectionKernel_left h₁ hA _ _)))
  naturality k k' g := by
    simp only [Functor.comp_map, ← Functor.map_comp]
    exact (transition_comp_stageMap _ (leOfHom g.1)
        (leOfHom ((kernelWeakIdealFunctor (A₀ := A₀) h₁ hA).map g)) _ _)

/-- The represented stages of `Spf (A₁ ⊗̂_{A₀} A)` at the projection kernels map to the stages of
`Spf A`. -/
private noncomputable def kernelStageRight
    (h₀ : TopologicalRing.IsWeaklyAdmissible A₀)
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D₀ : QuotientSystem B S hS A₀)
    (D₁ : QuotientSystem B S hS A₁) (D : QuotientSystem B S hS A)
    (c₁ : ContinuousHom D₀ D₁) (c : ContinuousHom D₀ D)
    (hc₁ : c₁.toRingHom = algebraMap A₀ A₁) (hc : c.toRingHom = algebraMap A₀ A) :
    kernelWeakIdealFunctor (A₀ := A₀) h₁ hA ⋙
        formalSpectrumDiagram (completedTensorQuotientSystem (A₀ := A₀) B S hS h₁ hA D₁ D) ⟶
      CategoryTheory.Prod.snd (WeakIdeals A₁) (WeakIdeals A) ⋙ formalSpectrumDiagram D where
  app k := (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
    ((BigAffineFppf.inclusion B S hS).map
      ((completedTensorRightHom B S hS h₀ h₁ hA D₀ D₁ D c₁ c hc₁ hc).stageMap
        (OrderDual.ofDual k.2) (OrderDual.ofDual (kernelWeakIdeal h₁ hA k))
        (by rw [completedTensorRightHom_toRingHom]
            exact le_comap_weakIdealProjectionKernel_right h₁ hA _ _)))
  naturality k k' g := by
    simp only [Functor.comp_map, ← Functor.map_comp]
    exact (transition_comp_stageMap _ (leOfHom g.2)
        (leOfHom ((kernelWeakIdealFunctor (A₀ := A₀) h₁ hA).map g)) _ _)

/-- **The stage squares of the fibre product of two formal spectra are cartesian.** The
represented quotient stage of `Spf (A₁ ⊗̂_{A₀} A)` at the projection kernel of a pair `(I, J)` of
weak ideals of definition of `A₁` and `A` is the fibre product over `Spf A₀` of the stages of
`Spf A₁` at `I` and of `Spf A` at `J`. Both stages map to `Spf A₀` through one stage
`Spec (A₀ ⧸ k)`, which is a monomorphism into it, and over that stage the square is the
spectrum of the pushout square of rings of
`isPushout_quotient_weakIdealProjectionKernel`. -/
private theorem isPullback_kernelStage
    (h₀ : TopologicalRing.IsWeaklyAdmissible A₀)
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D₀ : QuotientSystem B S hS A₀)
    (D₁ : QuotientSystem B S hS A₁) (D : QuotientSystem B S hS A)
    (c₁ : ContinuousHom D₀ D₁) (c : ContinuousHom D₀ D)
    (hc₁ : c₁.toRingHom = algebraMap A₀ A₁) (hc : c.toRingHom = algebraMap A₀ A)
    (k : WeakIdeals A₁ × WeakIdeals A) :
    IsPullback ((kernelStageLeft B S hS h₁ hA D₁ D).app k)
      ((kernelStageRight B S hS h₀ h₁ hA D₀ D₁ D c₁ c hc₁ hc).app k)
      (formalSpectrumInclusion D₁ k.1 ≫ formalSpectrumMap h₀ c₁)
      (formalSpectrumInclusion D k.2 ≫ formalSpectrumMap h₀ c) := by
  set i := OrderDual.ofDual k.1
  set j := OrderDual.ofDual k.2
  let k₀ : {I : Ideal A₀ // TopologicalRing.IsWeakIdealOfDefinition I} :=
    ⟨h₀.1.choose ⊓ Ideal.comap c₁.toRingHom i.1 ⊓ Ideal.comap c.toRingHom j.1,
      ⟨(h₀.1.choose_spec.1.inter (i.2.1.preimage c₁.continuous)).inter
        (j.2.1.preimage c.continuous),
        fun x hx ↦ h₀.1.choose_spec.2 x hx.1.1⟩⟩
  have hk₁ : k₀.1 ≤ Ideal.comap c₁.toRingHom i.1 := inf_le_left.trans inf_le_right
  have hk : k₀.1 ≤ Ideal.comap c.toRingHom j.1 := inf_le_right
  have hk₁' : k₀.1 ≤ Ideal.comap (algebraMap A₀ A₁) i.1 := hc₁ ▸ hk₁
  have hk' : k₀.1 ≤ Ideal.comap (algebraMap A₀ A) j.1 := hc ▸ hk
  have e₁ : formalSpectrumInclusion D₁ k.1 ≫ formalSpectrumMap h₀ c₁ =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (c₁.stageMap k₀ i hk₁)) ≫
        formalSpectrumInclusion D₀ (OrderDual.toDual k₀) :=
    formalSpectrumMap_spec h₀ c₁ k₀ i hk₁
  have e : formalSpectrumInclusion D k.2 ≫ formalSpectrumMap h₀ c =
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map
        ((BigAffineFppf.inclusion B S hS).map (c.stageMap k₀ j hk)) ≫
        formalSpectrumInclusion D₀ (OrderDual.toDual k₀) :=
    formalSpectrumMap_spec h₀ c k₀ j hk
  rw [e₁, e]
  have := mono_formalSpectrumInclusion_of_isWeaklyAdmissible h₀ D₀ (OrderDual.toDual k₀)
  refine isPullback_comp_mono (m := formalSpectrumInclusion D₀ (OrderDual.toDual k₀)) ?_
  have := faithful_toScheme B S hS
  have : ReflectsLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) := by
    dsimp [BigFppfOver.toScheme, BigFppfOver.forget]; infer_instance
  have := preservesLimitsOfShape_sheafifiedYoneda B S hS
  refine IsPullback.map (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) ?_
  refine IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) ?_
  have hsq := isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_quotient_weakIdealProjectionKernel h₁ hA k₀.1 i j hk₁' hk')
  rw [← quotientMap_congr hc₁ hk₁ hk₁', ← quotientMap_congr hc hk hk'] at hsq
  exact hsq

/-- **The fibre product of two formal spectra over a third is the formal spectrum of the
completed tensor product.** For weakly admissible topological rings `A₀`, `A₁` and `A` over `S`
and continuous homomorphisms `A₀ → A₁` and `A₀ → A` over `S`, the formal spectrum of
`A₁ ⊗̂_{A₀} A` is isomorphic to `Spf A₁ ×_{Spf A₀} Spf A`.

The fibre product of the two colimits is the colimit of the stagewise fibre products, filtered
colimits of sheaves of sets being exact; over the pair `(I, J)` of weak ideals of definition the
stagewise fibre product is the stage of `Spf (A₁ ⊗̂_{A₀} A)` at the projection kernel of `(I, J)`
(`isPullback_kernelStage`); and those stages are cofinal among all stages of
`Spf (A₁ ⊗̂_{A₀} A)` (`final_kernelWeakIdealFunctor`). -/
private theorem nonempty_iso_formalSpectrum_completedTensorProduct_pullback
    (h₀ : TopologicalRing.IsWeaklyAdmissible A₀)
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D₀ : QuotientSystem B S hS A₀)
    (D₁ : QuotientSystem B S hS A₁) (D : QuotientSystem B S hS A)
    (c₁ : ContinuousHom D₀ D₁) (c : ContinuousHom D₀ D)
    (hc₁ : c₁.toRingHom = algebraMap A₀ A₁) (hc : c.toRingHom = algebraMap A₀ A) :
    Nonempty (formalSpectrum (completedTensorQuotientSystem (A₀ := A₀) B S hS h₁ hA D₁ D) ≅
      pullback (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c)) := by
  obtain ⟨_, _⟩ := nonempty_directed_weakIdeals h₁
  obtain ⟨_, _⟩ := nonempty_directed_weakIdeals hA
  have := final_kernelWeakIdealFunctor (A₀ := A₀) h₁ hA
  have : IsConnected (WeakIdeals A₁ × WeakIdeals A) := IsFiltered.isConnected _
  have : IsFiltered (AsSmall.{u + 1} (WeakIdeals A₁ × WeakIdeals A)) :=
    IsFiltered.of_equivalence AsSmall.equiv
  have : HasExactColimitsOfShape (WeakIdeals A₁ × WeakIdeals A) (FppfSheaf B S hS) :=
    HasExactColimitsOfShape.of_domain_equivalence (FppfSheaf B S hS)
      (AsSmall.equiv (C := WeakIdeals A₁ × WeakIdeals A)).symm
  let a₁ : CategoryTheory.Prod.fst (WeakIdeals A₁) (WeakIdeals A) ⋙ formalSpectrumDiagram D₁ ⟶
      (Functor.const _).obj (formalSpectrum D₀) :=
    { app := fun k ↦ formalSpectrumInclusion D₁ k.1 ≫ formalSpectrumMap h₀ c₁
      naturality := fun k k' g ↦ by
        simp only [Functor.comp_map, Functor.const_obj_map]
        exact colimit.w_assoc (formalSpectrumDiagram D₁) g.1 _ }
  let a : CategoryTheory.Prod.snd (WeakIdeals A₁) (WeakIdeals A) ⋙ formalSpectrumDiagram D ⟶
      (Functor.const _).obj (formalSpectrum D₀) :=
    { app := fun k ↦ formalSpectrumInclusion D k.2 ≫ formalSpectrumMap h₀ c
      naturality := fun k k' g ↦ by
        simp only [Functor.comp_map, Functor.const_obj_map]
        exact colimit.w_assoc (formalSpectrumDiagram D) g.2 _ }
  have hpb : IsPullback (kernelStageLeft B S hS h₁ hA D₁ D)
      (kernelStageRight B S hS h₀ h₁ hA D₀ D₁ D c₁ c hc₁ hc) a₁ a :=
    IsPullback.of_forall_isPullback_app fun k ↦
      isPullback_kernelStage B S hS h₀ h₁ hA D₀ D₁ D c₁ c hc₁ hc k
  have hq := hpb.map (colim : (WeakIdeals A₁ × WeakIdeals A ⥤ FppfSheaf B S hS) ⥤ _)
  let e₀ : colimit ((Functor.const (WeakIdeals A₁ × WeakIdeals A)).obj (formalSpectrum D₀)) ≅
      formalSpectrum D₀ :=
    (colimit.isColimit _).coconePointUniqueUpToIso (isColimitConstCocone _ _)
  have h0 : ∀ k, colimit.ι ((Functor.const (WeakIdeals A₁ × WeakIdeals A)).obj
      (formalSpectrum D₀)) k ≫ e₀.hom = 𝟙 _ := fun k ↦
    (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom (isColimitConstCocone _ _) k
  let eT := Functor.Final.colimitIso (kernelWeakIdealFunctor (A₀ := A₀) h₁ hA)
    (formalSpectrumDiagram (completedTensorQuotientSystem (A₀ := A₀) B S hS h₁ hA D₁ D))
  let e₁ := Functor.Final.colimitIso (CategoryTheory.Prod.fst (WeakIdeals A₁) (WeakIdeals A))
    (formalSpectrumDiagram D₁)
  let e := Functor.Final.colimitIso (CategoryTheory.Prod.snd (WeakIdeals A₁) (WeakIdeals A))
    (formalSpectrumDiagram D)
  have h := hq.of_iso eT e₁ e e₀
    (fst' := eT.inv ≫ colim.map (kernelStageLeft B S hS h₁ hA D₁ D) ≫ e₁.hom)
    (snd' := eT.inv ≫ colim.map (kernelStageRight B S hS h₀ h₁ hA D₀ D₁ D c₁ c hc₁ hc) ≫ e.hom)
    (f' := formalSpectrumMap h₀ c₁) (g' := formalSpectrumMap h₀ c) (by simp) (by simp)
    (colimit.hom_ext fun k ↦ by
      rw [colim_map, ι_colimMap_assoc, h0, Category.comp_id]
      exact (Functor.Final.ι_colimitIso_hom_assoc
        (CategoryTheory.Prod.fst (WeakIdeals A₁) (WeakIdeals A)) (formalSpectrumDiagram D₁) k
        _).symm)
    (colimit.hom_ext fun k ↦ by
      rw [colim_map, ι_colimMap_assoc, h0, Category.comp_id]
      exact (Functor.Final.ι_colimitIso_hom_assoc
        (CategoryTheory.Prod.snd (WeakIdeals A₁) (WeakIdeals A)) (formalSpectrumDiagram D) k
        _).symm)
  exact ⟨h.isoPullback⟩

/-- **Stacks 0AN3, clause (3), with no presentation of the fibre product assumed.** Let `A₀`,
`A₁` and `A` be weakly admissible topological rings over `S` with quotient systems `D₀`, `D₁`,
`D`, and let `A₀ → A₁` and `A₀ → A` be continuous homomorphisms over `S`. Then the fibre product
`Spf A₁ ×_{Spf A₀} Spf A` is the formal spectrum of the completed tensor product
`A₁ ⊗̂_{A₀} A`: that ring carries a quotient system over `S` and an isomorphism of its formal
spectrum onto the fibre product, through which the two projections are the formal spectra of
the two canonical maps into the completed tensor product.

This is `exists_quotientSystem_iso_pullback_completedTensorProduct` with its hypothesis `epres`
discharged: the fibre product of the two formal spectra is the colimit of the stagewise fibre
products, which are the stages of `Spf (A₁ ⊗̂_{A₀} A)` at the projection kernels, and those are
cofinal among all its stages. -/
@[stacks 0AN3 "clause (3), that the fibre product of two McQuillan affine formal algebraic \
spaces over a third is the formal spectrum of the completed tensor product of their weakly \
admissible topological rings, compatibly with both projections, with no hypothesis beyond the \
weak admissibility of the three rings: the fibre product is proved to be a formal spectrum, as \
the colimit of the stagewise fibre products"]
theorem exists_quotientSystem_iso_pullback_completedTensorProduct_of_isWeaklyAdmissible
    (h₀ : TopologicalRing.IsWeaklyAdmissible A₀)
    (h₁ : TopologicalRing.IsWeaklyAdmissible A₁) (hA : TopologicalRing.IsWeaklyAdmissible A)
    (D₀ : QuotientSystem B S hS A₀) (D₁ : QuotientSystem B S hS A₁)
    (D : QuotientSystem B S hS A)
    (c₁ : ContinuousHom D₀ D₁) (c : ContinuousHom D₀ D)
    (hc₁ : c₁.toRingHom = algebraMap A₀ A₁) (hc : c.toRingHom = algebraMap A₀ A) :
    ∃ (DT : QuotientSystem B S hS (TopologicalRing.CompletedTensorProduct
        (R := A₀) (M := A₁) (N := A)))
        (t₁ : ContinuousHom D₁ DT) (t : ContinuousHom D DT)
        (eT : pullback (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c) ≅ formalSpectrum DT),
      t₁.toRingHom = algebraMap A₁ (TopologicalRing.CompletedTensorProduct
          (R := A₀) (M := A₁) (N := A)) ∧
        t.toRingHom = algebraMap A (TopologicalRing.CompletedTensorProduct
            (R := A₀) (M := A₁) (N := A)) ∧
        eT.hom ≫ formalSpectrumMap h₁ t₁ =
          pullback.fst (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c) ∧
        eT.hom ≫ formalSpectrumMap hA t =
          pullback.snd (formalSpectrumMap h₀ c₁) (formalSpectrumMap h₀ c) := by
  obtain ⟨φ⟩ := nonempty_iso_formalSpectrum_completedTensorProduct_pullback B S hS h₀ h₁ hA D₀ D₁
    D c₁ c hc₁ hc
  exact exists_quotientSystem_iso_pullback_completedTensorProduct B S hS h₀ h₁ hA D₀ D₁ D c₁ c
    hc₁ hc (TopologicalRing.completedTensorProduct_isWeaklyAdmissible (B := A₀) h₁.1 hA.1) _
    φ.symm

end Presentation

end AlgebraicGeometry.FormalSpace
end
