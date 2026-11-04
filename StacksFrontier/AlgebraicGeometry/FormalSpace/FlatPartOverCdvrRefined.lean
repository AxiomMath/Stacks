module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.TypeImplicationsRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexedSpectrumRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatCharacterizationRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartOverCdvr
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTargetRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.RingTheory.Rig.FiniteType
public import StacksFrontier.RingTheory.Rig.FlatIsLocalRefined
public import StacksFrontier.Topology.Algebra.AdicTopology.NoetherianAdic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalPropertyRefined
import all StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartOverCdvr

/-!
# The maximal flat closed formal subspace over a complete discrete valuation ring: refined forms

Further results on the maximal flat closed formal subspace over a complete discrete valuation
ring that belong with `StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartOverCdvr`. A
declaration of that module whose statement was strengthened keeps its original statement there;
its strengthened form lives here under a primed name.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Algebra

/-! ### The torsion ideal and the flat quotient -/

universe v w x

variable (A : Type v) [CommRing A] [IsDomain A] (B : Type w) [CommRing B] [Algebra A B]

end Algebra

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (D : QuotientSystem B S hS A)

/-! ### The inputs this library does not carry -/

/-- The one remaining hypothesis of `AlgebraicGeometry.FormalSpace.isFlat_tfae'`, this library's
form of **Stacks 0GCD**, with the source of the morphism quantified over: the morphism whose
flatness is concluded in Stacks 0GD8 is produced during the proof, so the input cannot be
stated for a fixed morphism. It is the covering refinement of **Stacks 0AJ2** at the class
`WAdm^{Noeth}`. The three inputs that used to be bundled here alongside it — **Stacks 0AJ3**,
that a fibre product with an affine étale chart is a formal algebraic space, and the two
locality axioms of **Stacks 0GC9** read on affine formal algebraic spaces through **Stacks
0AN8** and **Stacks 0AN9** — are theorems of this library and are no longer asked for. -/
abbrev FlatnessLocalityInputs' : Prop :=
  ∀ {X' : FppfSheaf B S hS} (f : X' ⟶ formalSpectrum D),
    HasEtaleRefinementOfSourceCover' B S hS TopologicalRing.IsNoetherianAdic f

/-! ### Stacks 0GD8 -/

/-- An affine formal algebraic space over `S` with a property is its own one-member atlas as in
Definition 0AIM: the identity map is representable étale and the induced map out of the
one-member coproduct is split epi, hence a surjection of sheaves. -/
private theorem hasAffineEtaleAtlasWithProperty_self {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) {P : FppfSheaf B S hS → Prop} (hP : P X) :
    HasAffineEtaleAtlasWithProperty B S hS X P := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  refine ⟨PUnit.{u + 2}, fun _ ↦ X, fun _ ↦ 𝟙 X, fun _ ↦ hX,
    fun _ ↦ isRepresentableEtale_id B S hS X, ?_, fun _ ↦ hP⟩
  have : IsSplitEpi (Sigma.desc fun _ : PUnit.{u + 2} ↦ 𝟙 X) :=
    ⟨⟨Sigma.ι (fun _ : PUnit.{u + 2} ↦ X) PUnit.unit, by simp⟩⟩
  exact (Sheaf.isLocallySurjective_iff_epi _).2 inferInstance

/-- The formal spectrum of an adic topological ring over `S` whose formal spectrum is an affine
formal algebraic space is locally countably indexed: the ring is weakly admissible with
countably generated zero neighbourhoods, so the implication (2) ⟹ (1) of **Stacks 0AN1** makes
the formal spectrum countably indexed, and it is its own atlas. -/
private theorem isLocallyCountablyIndexed_formalSpectrum {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (hA : TopologicalRing.IsAdic A) (D : QuotientSystem B S hS A)
    (hform : IsFormalAlgebraicSpace B S hS (formalSpectrum D))
    (haff : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D)) :
    IsLocallyCountablyIndexed B S hS (formalSpectrum D) := by
  let : IsLinearTopology A A := Rig.isLinearTopology_of_isAdicRing hA
  have hci : IsCountablyIndexed B S hS (formalSpectrum D) :=
    (isCountablyIndexedAffine_of_hasCountableWeakPresentation B S hS (formalSpectrum D)
      ⟨{ ring := A, system := D, iso := ⟨Iso.refl _⟩ },
        Rig.weaklyAdmissible_of_isAdicRing hA,
        Rig.countablyGenerated_nhds_of_isAdicRing hA⟩).2
  exact ⟨hform, hasAffineEtaleAtlasWithProperty_self B S hS haff hci⟩

/-- **Stacks 0GD8.** Let `A` be a complete discrete valuation ring and let `X` be a locally
Noetherian formal algebraic space over `S` with a structure morphism `p : X ⟶ Spf A`. Then
there is a closed immersion `ι : X' ⟶ X` of formal algebraic spaces with `X'` locally
Noetherian and flat over `A` such that every morphism `q : Y ⟶ X` with `Y` a locally
Noetherian formal algebraic space flat over `A` factors through `ι`.

The atlas of `X` supplied by the locally Noetherian hypothesis is turned into a family of
affine flat parts by `hpart`; those are mutually compatible, since the universal property of
one of them applies to any Noetherian affine formal algebraic space flat over `A` mapping to
the corresponding chart, so they glue by `hdesc` to a closed immersion `ι : X' ⟶ X` whose
sources form an affine étale covering of `X'`. That covering exhibits `X'` as locally
Noetherian, and reading condition (4) of Stacks 0GCD on it gives flatness of `X'` over `A`.
For the universal property, `hrefine` covers a test object `Y` by Noetherian affine formal
algebraic spaces which are flat over `A` and map to the charts of `X`; each of them factors
through the corresponding flat part and hence through `X'`, and `hfac` glues those
factorizations. -/
theorem exists_flat_isClosedImmersion_of_isLocallyNoetherian'
    [IsDomain A] [IsDiscreteValuationRing A] [IsNoetherianRing A]
    (_hAadic : TopologicalRing.IsAdic A)
    (_hAcomplete : IsAdicComplete (IsLocalRing.maximalIdeal A) A)
    (hSpfAaffine : IsAffineFormalAlgebraicSpace B S hS (formalSpectrum D))
    (hSpfA : IsFormalAlgebraicSpace B S hS (formalSpectrum D))
    {X : FppfSheaf B S hS} (hX : IsLocallyNoetherian B S hS X) (p : X ⟶ formalSpectrum D)
    (hpart : HasAffineFlatParts B S hS D p)
    (hdesc : FlatPartsDescend B S hS D p)
    (hfac : FactorizationDescendsAlongAffineEtaleCover B S hS)
    (hrefine : HasFlatAffineCoverOfFlat B S hS D p)
    (hloc : FlatnessLocalityInputs' B S hS D) :
    ∃ (X' : FppfSheaf B S hS) (ι : X' ⟶ X),
      IsClosedImmersion B S hS ι ∧ IsLocallyNoetherian B S hS X' ∧
        IsFlat B S hS (ι ≫ p) ∧
        ∀ (Y : FppfSheaf B S hS) (q : Y ⟶ X), IsLocallyNoetherian B S hS Y →
          IsFlat B S hS (q ≫ p) → ∃ r : Y ⟶ X', r ≫ ι = q := by
  classical
  obtain ⟨-, I, U, u, hUaffine, hUetale, hUsurj, hUnoeth⟩ := hX
  choose Z z hZaffine hZnoeth hZclosed hZflat hZuniv using
    fun i ↦ hpart (U i) (u i) (hUaffine i) (hUnoeth i) (hUetale i)
  obtain ⟨X', ι, ζ, hX'fas, hιclosed, hZcover, hζ⟩ :=
    hdesc U u ⟨hUaffine, hUetale, hUsurj⟩ Z z hZaffine hZnoeth hZclosed hZflat
      fun i W w hWaffine hWnoeth hWflat ↦ hZuniv i W w hWaffine hWnoeth hWflat
  have hX'lci : IsLocallyCountablyIndexed B S hS X' :=
    ⟨hX'fas, I, Z, ζ, hZcover.1, hZcover.2.1, hZcover.2.2,
      fun i ↦ isCountablyIndexed_of_isNoetherian B S hS (hZnoeth i)⟩
  have hDlci : IsLocallyCountablyIndexed B S hS (formalSpectrum D) :=
    isLocallyCountablyIndexed_formalSpectrum B S hS _hAadic D hSpfA hSpfAaffine
  refine ⟨X', ι, hιclosed, ⟨hX'fas, I, Z, ζ, hZcover.1, hZcover.2.1, hZcover.2.2, hZnoeth⟩,
    ?_, ?_⟩
  · have hchart : ∀ i, HasPropertyOnAffineChartMap B S hS
        TopologicalRing.IsNoetherianAdic TopologicalRing.IsFlatHom (ζ i ≫ ι ≫ p) := by
      intro i
      have hrw : ζ i ≫ ι ≫ p = z i ≫ u i ≫ p := by
        rw [← Category.assoc, hζ i, Category.assoc]
      rw [hrw]
      exact hasPropertyOnAffineChartMap_of_isFlat B S hS (z i ≫ u i ≫ p) (hZaffine i)
        hSpfAaffine (hZflat i)
    have hsrc : HasPropertyAfterSourceCover B S hS TopologicalRing.IsNoetherianAdic
        TopologicalRing.IsFlatHom (ι ≫ p) :=
      ⟨I, Z, ζ, hZcover, fun i ↦
        ⟨formalSpectrum D, 𝟙 (formalSpectrum D), ζ i ≫ ι ≫ p, hSpfAaffine,
          isRepresentableEtale_id B S hS (formalSpectrum D), by simp, hchart i⟩⟩
    exact ((isFlat_tfae' B S hS (ι ≫ p) hX'lci hDlci (hloc (ι ≫ p))).out 4 1).mp hsrc
  · intro Y q hY hqflat
    obtain ⟨J, W, w, k, m, hWcover, hWnoeth, hWsq, hWflat⟩ :=
      hrefine U u ⟨hUaffine, hUetale, hUsurj⟩ Y q hY hqflat
    refine hfac ι q hιclosed W w hWcover fun j ↦ ?_
    obtain ⟨r, hr⟩ := hZuniv (k j) (W j) (m j) (hWcover.1 j) (hWnoeth j) (hWflat j)
    refine ⟨r ≫ ζ (k j), ?_⟩
    rw [Category.assoc, hζ (k j), ← Category.assoc, hr, hWsq j]

end AlgebraicGeometry.FormalSpace

end
