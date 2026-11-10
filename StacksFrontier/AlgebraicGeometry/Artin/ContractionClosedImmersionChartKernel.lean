module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleClosedImmersionCharts
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleLocalCharacterization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothRigSurjectiveClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumFullyFaithful

/-!
# Kernels of chart presentations of closed formal subspaces

Let `V` be an affine formal algebraic space presented as `Spf D` by an adic Noetherian ring
`A`. For a morphism `f : X ⟶ Y` and `b : V ⟶ Y`, any fibre product of `f` along `b` presented
as `Spf E` with the projection to `V` given by a continuous homomorphism `φ : A → C` has the
*same* kernel `ker φ`, whatever fibre product and presentation are chosen: the comparison
isomorphism of two fibre products is a morphism of formal spectra over `Spf D`, hence comes
from a ring map compatible with the two `φ`'s (Stacks 0AN0).

This is what lets the proof of **Stacks 0GHE** speak of *the* ideal of `A^∧` cutting out a
closed formal subspace over an affine chart, and compare the ideals of `W`, of `Y_{/Z}` and of
their intersection `W''` through the conclusion of Stacks 0GD6 for the two projections of
`W''`.

## Main results

* `AlgebraicGeometry.FormalSpace.ker_eq_ker_of_isPullback_presentation`: the kernel of a chart
  presentation of a fibre product does not depend on the choices.
* `AlgebraicGeometry.FormalSpace.exists_isOpen_mul_ker_le_of_hasAnnihilatedKer`: if the two
  projections of `W'' = W ×_Q Y` are closed immersions whose kernels are annihilated on charts
  by ideals of definition (condition (3) of Stacks 0GD6), then over an affine chart of `Q`
  the kernels `K_W`, `K_Y` cutting out `W` and `Y` satisfy `L K_Y ⊆ K_W` and `L K_W ⊆ K_Y`
  for an open ideal `L`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.FormalSpace

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- One inclusion of kernels between two chart presentations of the same fibre product. -/
private theorem ker_le_ker_of_isPullback_presentation {X Y V : FppfSheaf B S hS}
    {f : X ⟶ Y} {b : V ⟶ Y} {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : TopologicalRing.IsWeaklyAdmissible A)
    {D : QuotientSystem B S hS A} (eV : V ≅ formalSpectrum D)
    {U₁ : FppfSheaf B S hS} {a₁ : U₁ ⟶ X} {t₁ : U₁ ⟶ V} (sq₁ : IsPullback a₁ t₁ f b)
    {C₁ : Type u} [CommRing C₁] [TopologicalSpace C₁] [IsTopologicalRing C₁]
    [IsLinearTopology C₁ C₁] (hC₁ : TopologicalRing.IsWeaklyAdmissible C₁)
    {E₁ : QuotientSystem B S hS C₁} (eU₁ : U₁ ≅ formalSpectrum E₁) (g₁ : ContinuousHom D E₁)
    (hg₁ : t₁ = eU₁.hom ≫ formalSpectrumMap hA g₁ ≫ eV.inv)
    {U₂ : FppfSheaf B S hS} {a₂ : U₂ ⟶ X} {t₂ : U₂ ⟶ V} (sq₂ : IsPullback a₂ t₂ f b)
    {C₂ : Type u} [CommRing C₂] [TopologicalSpace C₂] [IsTopologicalRing C₂]
    [IsLinearTopology C₂ C₂] (hC₂ : TopologicalRing.IsWeaklyAdmissible C₂)
    {E₂ : QuotientSystem B S hS C₂} (eU₂ : U₂ ≅ formalSpectrum E₂) (g₂ : ContinuousHom D E₂)
    (hg₂ : t₂ = eU₂.hom ≫ formalSpectrumMap hA g₂ ≫ eV.inv) :
    RingHom.ker g₂.toRingHom ≤ RingHom.ker g₁.toRingHom := by
  let e : U₁ ≅ U₂ := sq₁.isoIsPullback _ _ sq₂
  have he : e.hom ≫ t₂ = t₁ := sq₁.isoIsPullback_hom_snd _ _ sq₂
  let m : formalSpectrum E₁ ⟶ formalSpectrum E₂ := eU₁.inv ≫ e.hom ≫ eU₂.hom
  obtain ⟨ψ, hψ, -⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hC₂ hC₁ m
  let gψ : ContinuousHom D E₁ := ContinuousHom.comp hC₂ hA ψ g₂
  have hcomp : formalSpectrumMap hA gψ = formalSpectrumMap hA g₁ := by
    rw [← formalSpectrumMap_comp hA hC₂ g₂ ψ gψ rfl, hψ]
    have h2 : eU₂.hom ≫ formalSpectrumMap hA g₂ = t₂ ≫ eV.hom := by
      rw [hg₂]
      simp
    have h1 : formalSpectrumMap hA g₁ = eU₁.inv ≫ t₁ ≫ eV.hom := by
      rw [hg₁]
      simp
    rw [h1, ← he]
    simp only [m, Category.assoc, h2]
  obtain ⟨g, -, hg⟩ := existsUnique_continuousHom_formalSpectrumMap_eq hA hC₁
    (formalSpectrumMap hA g₁)
  have hEq : gψ = g₁ := (hg gψ hcomp).trans (hg g₁ rfl).symm
  intro x hx
  rw [RingHom.mem_ker] at hx ⊢
  rw [← hEq]
  change ψ.toRingHom (g₂.toRingHom x) = 0
  rw [hx, map_zero]

/-- **The kernel of a chart presentation of a fibre product is independent of the choices.** -/
theorem ker_eq_ker_of_isPullback_presentation {X Y V : FppfSheaf B S hS} {f : X ⟶ Y}
    {b : V ⟶ Y} {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [IsLinearTopology A A] (hA : TopologicalRing.IsWeaklyAdmissible A)
    {D : QuotientSystem B S hS A} (eV : V ≅ formalSpectrum D)
    {U₁ : FppfSheaf B S hS} {a₁ : U₁ ⟶ X} {t₁ : U₁ ⟶ V} (sq₁ : IsPullback a₁ t₁ f b)
    {C₁ : Type u} [CommRing C₁] [TopologicalSpace C₁] [IsTopologicalRing C₁]
    [IsLinearTopology C₁ C₁] (hC₁ : TopologicalRing.IsWeaklyAdmissible C₁)
    {E₁ : QuotientSystem B S hS C₁} (eU₁ : U₁ ≅ formalSpectrum E₁) (g₁ : ContinuousHom D E₁)
    (hg₁ : t₁ = eU₁.hom ≫ formalSpectrumMap hA g₁ ≫ eV.inv)
    {U₂ : FppfSheaf B S hS} {a₂ : U₂ ⟶ X} {t₂ : U₂ ⟶ V} (sq₂ : IsPullback a₂ t₂ f b)
    {C₂ : Type u} [CommRing C₂] [TopologicalSpace C₂] [IsTopologicalRing C₂]
    [IsLinearTopology C₂ C₂] (hC₂ : TopologicalRing.IsWeaklyAdmissible C₂)
    {E₂ : QuotientSystem B S hS C₂} (eU₂ : U₂ ≅ formalSpectrum E₂) (g₂ : ContinuousHom D E₂)
    (hg₂ : t₂ = eU₂.hom ≫ formalSpectrumMap hA g₂ ≫ eV.inv) :
    RingHom.ker g₁.toRingHom = RingHom.ker g₂.toRingHom :=
  le_antisymm (ker_le_ker_of_isPullback_presentation hA eV sq₂ hC₂ eU₂ g₂ hg₂ sq₁ hC₁ eU₁ g₁ hg₁)
    (ker_le_ker_of_isPullback_presentation hA eV sq₁ hC₁ eU₁ g₁ hg₁ sq₂ hC₂ eU₂ g₂ hg₂)

/-- If `I * ker g = ⊥`, then `I.comap f` multiplies `ker (g ∘ f)` into `ker f`. -/
private theorem _root_.Ideal.comap_mul_ker_comp_le_ker {R R' T : Type*} [CommRing R] [CommRing R']
    [CommRing T] (f : R →+* R') (g : R' →+* T) {I : Ideal R'} (hI : I * RingHom.ker g = ⊥) :
    I.comap f * RingHom.ker (g.comp f) ≤ RingHom.ker f := by
  rw [Ideal.mul_le]
  intro x hx z hz
  rw [RingHom.mem_ker, map_mul]
  have := Ideal.mul_mem_mul (Ideal.mem_comap.1 hx) (show f z ∈ RingHom.ker g from hz)
  rw [hI] at this
  exact (Submodule.mem_bot _).1 this

/-- One side of the chart comparison: for a closed immersion `p : W' ⟶ W` with kernels annihilated
on charts, the chart presentation `g` of `W' ×_W (W ×_Q V)` over `D` satisfies
`ker φ ≤ ker g` and `J * ker g ≤ ker φ` for an open ideal `J` of `A`. -/
private theorem exists_isOpen_mul_ker_le_of_isPullback_presentation {W' W Q V : FppfSheaf B S hS}
    {p : W' ⟶ W} {w : W ⟶ Q} (hp : IsClosedImmersion B S hS p)
    (hpA : HasAnnihilatedKerOnPullbackCharts B S hS p) {b : V ⟶ Q}
    (hb : IsRepresentableEtale B S hS b)
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hAw : TopologicalRing.IsWeaklyAdmissible A)
    {D : QuotientSystem B S hS A} (eV : V ≅ formalSpectrum D)
    {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C]
    [IsLinearTopology C C] [IsNoetherianRing C] (hCa : TopologicalRing.IsAdic C)
    {E : QuotientSystem B S hS C} (e : pullback w b ≅ formalSpectrum E) (φ : ContinuousHom D E)
    (hφ : pullback.snd w b = e.hom ≫ formalSpectrumMap hAw φ ≫ eV.inv) :
    ∃ J : Ideal A, IsOpen (J : Set A) ∧ ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R)
      (_ : IsTopologicalRing R) (_ : IsLinearTopology R R)
      (_ : TopologicalRing.IsWeaklyAdmissible R) (E' : QuotientSystem B S hS R)
      (e' : pullback p (pullback.fst w b) ≅ formalSpectrum E') (g : ContinuousHom D E'),
      IsPullback (pullback.fst p (pullback.fst w b))
        (pullback.snd p (pullback.fst w b) ≫ pullback.snd w b) (p ≫ w) b ∧
      pullback.snd p (pullback.fst w b) ≫ pullback.snd w b =
        e'.hom ≫ formalSpectrumMap hAw g ≫ eV.inv ∧
      RingHom.ker φ.toRingHom ≤ RingHom.ker g.toRingHom ∧
      J * RingHom.ker g.toRingHom ≤ RingHom.ker φ.toRingHom := by
  have hCw := Rig.weaklyAdmissible_of_isAdicRing hCa
  have hVW := isAffineFormalAlgebraicSpace_of_iso_formalSpectrum_of_isAdic B S hS hCa E e
  have sq := IsPullback.of_hasPullback p (pullback.fst w b)
  obtain ⟨R, _, _, _, _, _, hR, E', e', ψ, hψ⟩ :=
    exists_adic_presentation_of_isPullback B S hS hp sq hCa hCw E e
  obtain ⟨-, I, hI, hI0⟩ := hpA _ hVW _ (isRepresentableEtale_pullback_fst B S hS w b hb) _ _ _ sq
    C R hCa hR hCw E E' e' e ψ hψ
  refine ⟨I.comap φ.toRingHom, hI.1.preimage φ.continuous, R, _, _, _, _,
    Rig.weaklyAdmissible_of_isAdicRing hR, E', e', ContinuousHom.comp hCw hAw ψ φ,
    sq.paste_vert (IsPullback.of_hasPullback w b), ?_, fun x hx =>
      by change ψ.toRingHom (φ.toRingHom x) = 0; rw [RingHom.mem_ker.1 hx, map_zero],
    Ideal.comap_mul_ker_comp_le_ker φ.toRingHom ψ.toRingHom hI0⟩
  rw [hψ, hφ, ← formalSpectrumMap_comp hAw hCw φ ψ _ rfl]
  simp

/-- **The kernels of `W` and `Y` over an affine chart agree up to an open ideal.** Let
`w : W ⟶ Q` and `y : Y ⟶ Q` be morphisms whose two fibre-product projections out of
`W'' = W ×_Q Y` are closed immersions with kernels annihilated on charts by ideals of definition
(condition (3) of Stacks 0GD6). Over an affine chart `b : V ⟶ Q`, representable étale and
presented by an adic Noetherian ring `A`, let `K_W` and `K_Y` be the kernels of presentations of
`W ×_Q V` and `Y ×_Q V`. Then `L K_Y ⊆ K_W` and `L K_W ⊆ K_Y` for an open ideal `L` of `A`. -/
theorem exists_isOpen_mul_ker_le_of_hasAnnihilatedKer {W Yc Q V : FppfSheaf B S hS}
    (w : W ⟶ Q) (y : Yc ⟶ Q)
    (hfst : IsClosedImmersion B S hS (pullback.fst w y))
    (hsnd : IsClosedImmersion B S hS (pullback.snd w y))
    (hW : HasAnnihilatedKerOnPullbackCharts B S hS (pullback.fst w y))
    (hY : HasAnnihilatedKerOnPullbackCharts B S hS (pullback.snd w y))
    (b : V ⟶ Q) (hb : IsRepresentableEtale B S hS b)
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hAw : TopologicalRing.IsWeaklyAdmissible A)
    {D : QuotientSystem B S hS A} (eV : V ≅ formalSpectrum D)
    {CW : Type u} [CommRing CW] [TopologicalSpace CW] [IsTopologicalRing CW]
    [IsLinearTopology CW CW] [IsNoetherianRing CW] (hCWa : TopologicalRing.IsAdic CW)
    {EW : QuotientSystem B S hS CW} (eW : pullback w b ≅ formalSpectrum EW)
    (φW : ContinuousHom D EW)
    (hφW : pullback.snd w b = eW.hom ≫ formalSpectrumMap hAw φW ≫ eV.inv)
    {CY : Type u} [CommRing CY] [TopologicalSpace CY] [IsTopologicalRing CY]
    [IsLinearTopology CY CY] [IsNoetherianRing CY] (hCYa : TopologicalRing.IsAdic CY)
    {EY : QuotientSystem B S hS CY} (eY : pullback y b ≅ formalSpectrum EY)
    (φY : ContinuousHom D EY)
    (hφY : pullback.snd y b = eY.hom ≫ formalSpectrumMap hAw φY ≫ eV.inv) :
    ∃ L : Ideal A, IsOpen (L : Set A) ∧ L * RingHom.ker φY.toRingHom ≤ RingHom.ker φW.toRingHom ∧
      L * RingHom.ker φW.toRingHom ≤ RingHom.ker φY.toRingHom := by
  obtain ⟨L₁, hL₁, R₁, _, _, _, _, hR₁, E₁, e₁, g₁, sq₁, hg₁, hKW, hL₁K⟩ :=
    exists_isOpen_mul_ker_le_of_isPullback_presentation hfst hW hb hAw eV hCWa eW φW hφW
  obtain ⟨L₂, hL₂, R₂, _, _, _, _, hR₂, E₂, e₂, g₂, sq₂, hg₂, hKY, hL₂K⟩ :=
    exists_isOpen_mul_ker_le_of_isPullback_presentation hsnd hY hb hAw eV hCYa eY φY hφY
  rw [← pullback.condition] at sq₂
  have hK := ker_eq_ker_of_isPullback_presentation hAw eV sq₁ hR₁ e₁ g₁ hg₁ sq₂ hR₂ e₂ g₂ hg₂
  exact ⟨L₁ ⊓ L₂, hL₁.inter hL₂,
    (Ideal.mul_mono inf_le_left (hKY.trans hK.ge)).trans hL₁K,
    (Ideal.mul_mono inf_le_right (hKW.trans hK.le)).trans hL₂K⟩

end AlgebraicGeometry.FormalSpace
