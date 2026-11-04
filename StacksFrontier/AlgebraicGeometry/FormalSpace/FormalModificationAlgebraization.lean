module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineModificationBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineRigEtaleAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionAlgebraicSpaceAtlas
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionModificationEquivalence
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalModificationBaseChangeAdic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SmallerBaseAttachedModification

/-!
# Formal modifications are formally locally completions of proper models (Stacks 0GDV)

Let `S` be a scheme contained in a big fppf site `B` and let `𝔛' ⟶ 𝔛` be a formal modification
(Stacks 0GDK) of locally Noetherian formal algebraic spaces over `S`. **Stacks 0GDV** says that
for every adic Noetherian topological ring `A` and every adic morphism `Spf A ⟶ 𝔛` there are a
proper morphism of algebraic spaces `X ⟶ Spec A` and an isomorphism
`Spf A ×_𝔛 𝔛' ≅ X_{/Z}` over `Spf A`, where `Z = X ×_{Spec A} Spf(A)_red` is the closed fibre.

## Main definitions

* `AlgebraicGeometry.FormalSpace.toTerminalBase`: the structure morphism `S ⟶ Spec ℤ` as a
  morphism of the site.
* `AlgebraicGeometry.FormalSpace.formalSpectrumIsoOfRingEquivOfTerminal`: over the terminal base,
  a continuous ring isomorphism with continuous inverse gives an isomorphism of formal spectra.
* `AlgebraicGeometry.FormalSpace.formalSpectrumCompletionIso`: the canonical identification of
  `Spf A`, viewed absolutely, with the completion of `Spec A` along `V(I)` for an ideal of
  definition `I`.

## Main results

* `FormalSpace.exists_isProper_completionOverFunctor_iso_of_isFormalModification`:
  **Stacks 0GDV**. For a formal modification `𝔛' ⟶ 𝔛` and an adic morphism `Spf A ⟶ 𝔛`, the
  base change `Spf A ×_𝔛 𝔛'` is the completion of a proper algebraic space `X ⟶ Spec A` along
  its closed fibre.

## Implementation notes

The algebraic model lives over `Spec A`, and `Spec A` need not be a scheme over `S`: the structure
of `Spf A` over `S` is a compatible family of morphisms `Spec (A ⧸ J) ⟶ S`
(`AlgebraicGeometry.FormalSpace.QuotientSystem`), which need not come from a morphism
`Spec A ⟶ S`. The source's "algebraic spaces" with no base are therefore read as algebraic spaces
over `Spec ℤ`, the terminal scheme, which every scheme maps to, and the base change
`Spf A ×_𝔛 𝔛'`, a formal algebraic space over `S`, is viewed over `Spec ℤ` through the change of
base of Stacks 04SG (`AlgebraicGeometry.FormalSpace.smallerBaseSheafFunctor`). The two size
conditions, that the site contains `Spec ℤ` and `Spec A`, are what make these objects of the site;
the source's sites are indexed by a cutoff it is free to enlarge.

The proof is the source's. The base change `Spf A ×_𝔛 𝔛' ⟶ Spf A` is a formal modification by
Stacks 0GDN (`AlgebraicGeometry.FormalSpace.isFormalModification_pullback_snd_of_isAdicMorphism`),
here applied over `Spec ℤ`, where the formal modification `𝔛' ⟶ 𝔛` stays one
(`AlgebraicGeometry.FormalSpace.isFormalModification_smallerBaseSheafFunctor`) and `Spf A` is the
completion of `Spec A` along `V(I)` (Stacks 0GBA). Theorem 0GDU
(`AlgebraicGeometry.FormalSpace.exists_isProper_completion_iso_of_isFormalModification`) then
gives the proper model. The closed fibre `Z` is the inverse image in `X` of `V(I)`, for any ideal
of definition `I`, all of which have the same zero locus; that inverse image is what
`AlgebraicGeometry.Space.completionOverFunctor` completes along.

## References

* [Stacks Project, Tag 0GDV](https://stacks.math.columbia.edu/tag/0GDV)
* [Stacks Project, Tag 0GDN](https://stacks.math.columbia.edu/tag/0GDN)
* [Stacks Project, Tag 0GDU](https://stacks.math.columbia.edu/tag/0GDU)
* [Stacks Project, Tag 0GBA](https://stacks.math.columbia.edu/tag/0GBA)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Topology

universe u

namespace AlgebraicGeometry.FormalSpace

/-! ### Ideals of definition of an adic topological ring -/

section Rings

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- The topology of an adic topological ring is the adic topology of each of its ideals of
definition: an ideal of definition contains a power of an ideal defining the topology, so its
powers are open, and its powers tend to zero by definition. -/
@[ega "0 7.2.3" "special case"]
theorem isAdic_of_isIdealOfDefinition (hA : TopologicalRing.IsAdic A) {I : Ideal A}
    (hI : TopologicalRing.IsIdealOfDefinition I) : _root_.IsAdic I := by
  obtain ⟨⟨J, -, hJ⟩, -, -⟩ := hA
  obtain ⟨hJopen, hJbasis⟩ := isAdic_iff.mp hJ
  obtain ⟨m, hm⟩ := hJbasis _ (hI.1.mem_nhds I.zero_mem)
  refine isAdic_iff.mpr ⟨fun n => ?_, hI.2⟩
  have hle : J ^ (m * n) ≤ I ^ n := by
    rw [pow_mul]
    exact Ideal.pow_right_mono hm n
  exact Submodule.isOpen_mono hle (hJopen _)

/-- An adic topological ring is adically complete for each of its ideals of definition. -/
theorem isAdicComplete_of_isIdealOfDefinition (hA : TopologicalRing.IsAdic A) {I : Ideal A}
    (hI : TopologicalRing.IsIdealOfDefinition I) : IsAdicComplete I A := by
  have hIadic := isAdic_of_isIdealOfDefinition hA hI
  obtain ⟨-, hT2, hCompl⟩ := hA
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have _ : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  exact (IsAdic.isAdicComplete_iff hIadic).mpr ⟨hCompl, hT2⟩

/-- A ring homomorphism between adic topological rings sending the `n`-th power of the defining
ideal into the `n`-th power of the defining ideal, for every `n`, is continuous. -/
private theorem continuous_of_pow_mem_pow {R T : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CommRing T] [TopologicalSpace T] [IsTopologicalRing T] (f : R →+* T)
    {J : Ideal R} {K : Ideal T} (hJ : _root_.IsAdic J) (hK : _root_.IsAdic K)
    (h : ∀ n, ∀ x ∈ J ^ n, f x ∈ K ^ n) : Continuous f := by
  refine continuous_of_continuousAt_zero f.toAddMonoidHom fun U hU => ?_
  rw [AddMonoidHom.map_zero] at hU
  obtain ⟨n, hn⟩ := (isAdic_iff.mp hK).2 U hU
  exact Filter.mem_map.mpr (Filter.mem_of_superset
    (((isAdic_iff.mp hJ).1 n).mem_nhds (J ^ n).zero_mem) fun x hx => hn (h n x hx))

variable (I : Ideal A) [IsAdicComplete I A]

/-- For an ideal `I` of a topological ring whose topology is the `I`-adic one, the identification
of an `I`-adically complete ring with its `I`-adic completion is continuous for the `I`-adic
topology of the completion. -/
theorem continuous_adicCompletion_ofAlgEquiv (hIadic : _root_.IsAdic I) (hI : I.FG) :
    letI : TopologicalSpace (AdicCompletion I A) := I.adicModuleTopology (AdicCompletion I A)
    Continuous (AdicCompletion.ofAlgEquiv I : A →+* AdicCompletion I A) := by
  let : TopologicalSpace (AdicCompletion I A) := I.adicModuleTopology (AdicCompletion I A)
  obtain ⟨_, _, hJ, -, -⟩ := exists_isTopologicalRing_isAdic_adicCompletion I hI
  refine continuous_of_pow_mem_pow _ hIadic hJ fun n x hx => ?_
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem (algebraMap A (AdicCompletion I A)) hx

/-- The inverse of the identification of an `I`-adically complete ring with its `I`-adic
completion is continuous for the `I`-adic topology of the completion. -/
theorem continuous_adicCompletion_ofAlgEquiv_symm (hIadic : _root_.IsAdic I) (hI : I.FG) :
    letI : TopologicalSpace (AdicCompletion I A) := I.adicModuleTopology (AdicCompletion I A)
    Continuous ((AdicCompletion.ofAlgEquiv I).symm : AdicCompletion I A →+* A) := by
  let : TopologicalSpace (AdicCompletion I A) := I.adicModuleTopology (AdicCompletion I A)
  obtain ⟨_, _, hJ, -, -⟩ := exists_isTopologicalRing_isAdic_adicCompletion I hI
  refine continuous_of_pow_mem_pow _ hJ hIadic fun n y hy => ?_
  rw [← Ideal.map_pow] at hy
  have hsurj : Function.Surjective (algebraMap A (AdicCompletion I A)) := fun y =>
    ⟨(AdicCompletion.ofAlgEquiv I).symm y, AdicCompletion.of_ofAlgEquiv_symm I y⟩
  obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp hy
  show (AdicCompletion.ofAlgEquiv I).symm (AdicCompletion.of I A x) ∈ (I ^ n : Ideal A)
  rwa [AdicCompletion.ofAlgEquiv_symm_of]

end Rings

/-! ### Formal spectra over the terminal base -/

section Terminal

variable (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))

/-- A continuous ring homomorphism between topological rings with quotient systems over the
terminal scheme is a continuous homomorphism of quotient systems: every structure morphism has
the terminal scheme as target. -/
def continuousHomOfTerminal {A C : Type u} [CommRing A] [TopologicalSpace A] [CommRing C]
    [TopologicalSpace C] (D : QuotientSystem B (⊤_ Scheme.{u}) hZ A)
    (E : QuotientSystem B (⊤_ Scheme.{u}) hZ C) (φ : A →+* C) (hφ : Continuous φ) :
    ContinuousHom D E where
  toRingHom := φ
  continuous := hφ
  overS _ _ _ := terminal.hom_ext _ _

/-- Over the terminal base, a ring isomorphism of weakly admissible topological rings which is
continuous with continuous inverse identifies their formal spectra. -/
def formalSpectrumIsoOfRingEquivOfTerminal {A C : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] [CommRing C] [TopologicalSpace C]
    [IsTopologicalRing C] [IsLinearTopology C C] (hA : TopologicalRing.IsWeaklyAdmissible A)
    (hC : TopologicalRing.IsWeaklyAdmissible C) (D : QuotientSystem B (⊤_ Scheme.{u}) hZ A)
    (E : QuotientSystem B (⊤_ Scheme.{u}) hZ C) (φ : A ≃+* C) (hφ : Continuous φ)
    (hφ' : Continuous φ.symm) : formalSpectrum E ≅ formalSpectrum D where
  hom := formalSpectrumMap hA (continuousHomOfTerminal B hZ D E φ hφ)
  inv := formalSpectrumMap hC (continuousHomOfTerminal B hZ E D φ.symm hφ')
  hom_inv_id := (formalSpectrumMap_comp hC hA (continuousHomOfTerminal B hZ E D φ.symm hφ')
    (continuousHomOfTerminal B hZ D E φ hφ)
    (continuousHomOfTerminal B hZ E E (RingHom.id C) continuous_id)
    (by ext x; simp [continuousHomOfTerminal])).trans (formalSpectrumMap_id hC _ rfl)
  inv_hom_id := (formalSpectrumMap_comp hA hC (continuousHomOfTerminal B hZ D E φ hφ)
    (continuousHomOfTerminal B hZ E D φ.symm hφ')
    (continuousHomOfTerminal B hZ D D (RingHom.id A) continuous_id)
    (by ext x; simp [continuousHomOfTerminal])).trans (formalSpectrumMap_id hA _ rfl)

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure morphism of `S` to the terminal scheme `Spec ℤ`, as a morphism of the site. -/
abbrev toTerminalBase : B.obj hS ⟶ B.obj hZ :=
  ⟨terminal.from S⟩

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [IsLinearTopology A A] (hAB : B.Contains (Spec (.of A)))

/-- `Spec A` as a scheme over the terminal scheme `Spec ℤ`. -/
abbrev specOverTerminal : BigFppfOver B (⊤_ Scheme.{u}) hZ :=
  affineOver B (⊤_ Scheme.{u}) hZ hAB (terminal.from _)

/-- **The formal spectrum of an adic Noetherian ring is a completion of its spectrum.** Let `A`
be an adic Noetherian topological ring presented over `S` by the quotient system `D`, and let `I`
be an ideal of definition of `A`. Viewed over `Spec ℤ` (Stacks 04SG), the formal spectrum
`Spf A` is the formal completion of `Spec A` along `V(I)`: it is the formal spectrum over
`Spec ℤ` of the composite quotient system
(`AlgebraicGeometry.FormalSpace.smallerBaseFormalSpectrumIso`), `A` is its own `I`-adic completion
(`AdicCompletion.ofAlgEquiv`), and the formal spectrum of the completion is the completion along
`V(I)` (**Stacks 0GBA (2)**, `AlgebraicGeometry.FormalSpace.completionComparison`). -/
def formalSpectrumCompletionIso (hA : TopologicalRing.IsNoetherianAdic A) (I : Ideal A)
    (hI : TopologicalRing.IsIdealOfDefinition I) (D : QuotientSystem B S hS A) :
    (smallerBaseSheafFunctor B S (⊤_ Scheme.{u}) hS hZ (toTerminalBase B hZ S hS)).obj
        (formalSpectrum D) ≅
      Space.completionSheaf B (⊤_ Scheme.{u}) hZ (yoneda.obj (specOverTerminal B hZ hAB))
        (zeroLocusPoints B (⊤_ Scheme.{u}) hZ hAB (terminal.from _) I) :=
  have := hA.2
  have : IsAdicComplete I A := isAdicComplete_of_isIdealOfDefinition hA.1 hI
  let : TopologicalSpace (AdicCompletion I A) := I.adicModuleTopology (AdicCompletion I A)
  let := (exists_isTopologicalRing_isAdic_adicCompletion I I.fg_of_isNoetherianRing).choose
  let :=
    (exists_isTopologicalRing_isAdic_adicCompletion I I.fg_of_isNoetherianRing).choose_spec.choose
  smallerBaseFormalSpectrumIso B S (⊤_ Scheme.{u}) hS hZ (toTerminalBase B hZ S hS) D ≪≫
    formalSpectrumIsoOfRingEquivOfTerminal B hZ
      (exists_isTopologicalRing_isAdic_adicCompletion I
        I.fg_of_isNoetherianRing).choose_spec.choose_spec.2.2
      (TopologicalRing.isWeaklyAdmissible_of_isAdic (isAdic_of_isIdealOfDefinition hA.1 hI)
        (isAdicComplete_of_isIdealOfDefinition hA.1 hI))
      (adicQuotientSystem B (⊤_ Scheme.{u}) hZ hAB (terminal.from _) I I.fg_of_isNoetherianRing)
      (smallerBaseQuotientSystem B S (⊤_ Scheme.{u}) hS hZ (toTerminalBase B hZ S hS) D)
      (AdicCompletion.ofAlgEquiv I).symm.toRingEquiv
      (continuous_adicCompletion_ofAlgEquiv_symm I (isAdic_of_isIdealOfDefinition hA.1 hI)
        I.fg_of_isNoetherianRing)
      (continuous_adicCompletion_ofAlgEquiv I (isAdic_of_isIdealOfDefinition hA.1 hI)
        I.fg_of_isNoetherianRing) ≪≫
    @asIso _ _ _ _ (completionComparison B (⊤_ Scheme.{u}) hZ hAB (terminal.from _) I
        (adicQuotientSystem B (⊤_ Scheme.{u}) hZ hAB (terminal.from _) I I.fg_of_isNoetherianRing)
        (quotientSystemCompatible_adicQuotientSystem B (⊤_ Scheme.{u}) hZ hAB (terminal.from _) I
          I.fg_of_isNoetherianRing))
      (isIso_completionComparison_adicQuotientSystem B (⊤_ Scheme.{u}) hZ hAB (terminal.from _) I
        I.fg_of_isNoetherianRing)

end Terminal

/-! ### Stacks 0GDV -/

section Main

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (hZ : B.Contains (⊤_ Scheme.{u}))

local notation "Ψ" =>
  smallerBaseSheafFunctor B S (⊤_ Scheme) hS hZ (toTerminalBase B hZ S hS)

/-- **Stacks 0GDV.** Let `f : 𝔛' ⟶ 𝔛` be a formal modification (Definition 0GDK) of locally
Noetherian formal algebraic spaces over `S`. Let `A` be an adic Noetherian topological ring and
let `g : Spf A ⟶ 𝔛` be an adic morphism, `Spf A` being a formal algebraic space over `S` through
the quotient system `D`. Then there are a proper morphism `p : X ⟶ Spec A` of algebraic spaces
and an isomorphism `Spf A ×_𝔛 𝔛' ≅ X_{/Z}` over `Spf A` of the base change of `f` with the formal
completion of `X` along its closed fibre `Z = X ×_{Spec A} Spf(A)_red`.

Algebraic spaces with no base are algebraic spaces over `Spec ℤ`, the terminal scheme, and the
base change, a formal algebraic space over `S`, is viewed over `Spec ℤ` by the change of base of
Stacks 04SG (`AlgebraicGeometry.FormalSpace.smallerBaseSheafFunctor`). The closed fibre is the
inverse image under `p` of the zero locus `V(I)` of an ideal of definition `I`, which is the
closed subset of `Spec A` underlying `Spf(A)_red`; the completion along it is
`AlgebraicGeometry.Space.completionOverFunctor`, and the isomorphism is one over the completion of
`Spec A` along `V(I)`, which is `Spf A`
(`AlgebraicGeometry.FormalSpace.formalSpectrumCompletionIso`).
The statement holds for every ideal of definition `I`.

As in the source: the base change `Spf A ×_𝔛 𝔛' ⟶ Spf A` is a formal modification by Stacks
0GDN, and Theorem 0GDU applies to it. -/
@[stacks 0GDV]
theorem exists_isProper_completionOverFunctor_iso_of_isFormalModification
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsNoetherianAdic A) (hAB : B.Contains (Spec (.of A)))
    (I : Ideal A) (hI : TopologicalRing.IsIdealOfDefinition I)
    {X' X : FppfSheaf B S hS} (f : X' ⟶ X) (hf : IsFormalModification B S hS f)
    (D : QuotientSystem B S hS A) (g : formalSpectrum D ⟶ X) (hg : IsAdicMorphism B S hS g) :
    ∃ (Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
      (_ : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Y)
      (p : Y ⟶ yoneda.obj (specOverTerminal B hZ hAB)),
      Space.IsProper B (⊤_ Scheme.{u}) hZ p ∧
        Nonempty ((Space.completionOverFunctor B (⊤_ Scheme.{u}) hZ
            (zeroLocusPoints B (⊤_ Scheme.{u}) hZ hAB (terminal.from _) I)).obj (Over.mk p) ≅
          Over.mk ((Ψ).map (pullback.snd f g) ≫
            (formalSpectrumCompletionIso B hZ S hS hAB hA I hI D).hom)) := by
  have := hA.2
  have hFM : IsFormalModification B (⊤_ Scheme.{u}) hZ ((Ψ).map f) :=
    isFormalModification_smallerBaseSheafFunctor B S (⊤_ Scheme.{u}) hS hZ
      (toTerminalBase B hZ S hS) f hf
  have hg' : IsAdicMorphism B (⊤_ Scheme.{u}) hZ ((Ψ).map g) :=
    (isRepresentableByAlgebraicSpacesULift_smallerBaseULiftMap_iff B S (⊤_ Scheme.{u}) hS hZ
      (toTerminalBase B hZ S hS) g.hom).mpr hg
  have hc₀ : IsAdicMorphism B (⊤_ Scheme.{u}) hZ
      ((formalSpectrumCompletionIso B hZ S hS hAB hA I hI D).inv ≫ (Ψ).map g) :=
    Space.isRepresentableByAlgebraicSpacesULift_comp B (⊤_ Scheme.{u}) hZ _ _
      (isAdicMorphism_of_isIso B (⊤_ Scheme.{u}) hZ _) hg'
  have hXsp := isAlgebraicSpace_yoneda B (⊤_ Scheme.{u}) hZ (specOverTerminal B hZ hAB)
  have hXN : Space.IsLocallyNoetherian B (⊤_ Scheme.{u}) hZ
      (yoneda.obj (specOverTerminal B hZ hAB)) :=
    Space.isLocallyNoetherian_yoneda_affineOver hAB (terminal.from _)
  have hT := isClosed_zeroLocusPoints (B := B) (hS := hZ) I hAB (terminal.from _)
  have hCN := isLocallyNoetherian_completionSheaf_of_isLocallyNoetherian hXsp hXN _ hT
  have h𝔣 := isFormalModification_pullback_snd_of_isAdicMorphism B (⊤_ Scheme.{u}) hZ
    ((Ψ).map f) _ hCN hc₀ hFM
  obtain ⟨Y, hY, p, hp, -, ⟨E⟩⟩ :=
    exists_isProper_completion_iso_of_isFormalModification hXsp hXN _ hT h𝔣
  let φ : pullback ((Ψ).map f)
        ((formalSpectrumCompletionIso B hZ S hS hAB hA I hI D).inv ≫ (Ψ).map g) ≅
      (Ψ).obj (pullback f g) :=
    asIso (pullback.map ((Ψ).map f)
        ((formalSpectrumCompletionIso B hZ S hS hAB hA I hI D).inv ≫ (Ψ).map g)
        ((Ψ).map f) ((Ψ).map g) (𝟙 _) (formalSpectrumCompletionIso B hZ S hS hAB hA I hI D).inv
        (𝟙 _) (by simp) (by simp)) ≪≫
      (PreservesPullback.iso (Ψ) f g).symm
  have hφ : φ.hom ≫ (Ψ).map (pullback.snd f g) ≫
      (formalSpectrumCompletionIso B hZ S hS hAB hA I hI D).hom =
      pullback.snd ((Ψ).map f)
        ((formalSpectrumCompletionIso B hZ S hS hAB hA I hI D).inv ≫ (Ψ).map g) := by
    simp only [φ, Iso.trans_hom, asIso_hom, Iso.symm_hom, Category.assoc,
      PreservesPullback.iso_inv_snd_assoc, pullback.lift_snd_assoc, Iso.inv_hom_id,
      Category.comp_id]
  exact ⟨Y, hY, p, hp, ⟨E ≪≫ Over.isoMk φ hφ⟩⟩

end Main

end AlgebraicGeometry.FormalSpace

end
