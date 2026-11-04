module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.RepresentableAffine
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionComparison
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types
public import StacksFrontier.RingTheory.Rig.RigEtaleSurjection
public import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissibleAdic

/-!
# Rig-smooth closed immersions are rig-étale

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` be a closed immersion
of locally Noetherian formal algebraic spaces over `S`.  **Stacks 0GD4** says that the
following three conditions are equivalent:

1. `f` is rig-smooth;
2. `f` is rig-étale;
3. for every affine formal algebraic space `V` and every morphism `V ⟶ Y` representable by
   algebraic spaces and étale, the base change `X ×_Y V ⟶ V` corresponds to a surjective
   morphism `B → A` of `WAdm^{Noeth}` whose kernel `J` satisfies `I · (J / J²) = 0` for some
   ideal of definition `I` of `B`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasAnnihilatedConormalOnPullbackCharts` — condition (3).
* `AlgebraicGeometry.FormalSpace.HasRigEtaleOnPullbackCharts` — the same quantification with
  the chart map required to be rig-étale, which is the shape in which Stacks 0GCZ is used.
* `AlgebraicGeometry.FormalSpace.HasAdicQuotientOnPullbackCharts` — the same quantification
  with the chart map required to be a surjection which is adic of topologically finite type,
  which is the shape in which Stacks 0AQI is used.

## Main results

* `AlgebraicGeometry.FormalSpace.isRigSmooth_tfae_of_isClosedImmersion`: **Stacks 0GD4**.

## Implementation notes

Conditions (1) and (2) are `AlgebraicGeometry.FormalSpace.IsRigSmooth` (Definition 0GCP) and
`AlgebraicGeometry.FormalSpace.IsRigEtale` (Definition 0AQM); both are chart conditions
quantified over affine representable étale squares over `f`, over adic Noetherian presenting
rings of the two charts, and over continuous homomorphisms inducing the chart map.  Condition
(3) is quantified over *less* data: only a chart `V ⟶ Y` of the target, together with a fibre
product of `f` along it; the source chart is the fibre product itself and is not free.  The
conormal condition `I · (J / J²) = 0` is rendered as `I * J ≤ J ^ 2` for `J` the kernel of the
chart homomorphism, these being the same assertion, and the ideal of definition is existentially
quantified, as in the source's "for some ideal of definition `I`".

The two hard implications both go through the algebraic statement
`Rig.isRigSmooth_iff_exists_pow_mul_ker_le_sq` and
`Rig.isRigEtale_iff_exists_pow_mul_ker_le_sq`: for a *surjection* of `WAdm^{Noeth}` the
completed naive cotangent complex is the conormal module in degree `-1`, so each of
rig-smoothness and rig-étaleness of the chart homomorphism is the annihilation of `J / J²` by a
power of the ideal of definition.  The ideal of definition is normalised to the one defining the
topology of the presenting ring, which is `I`-adically complete; the passage from the ideal
supplied by condition (1) to that one is Stacks 0GCI
(`Rig.isRigSmooth_iff_forall_idealOfDefinition`), and a positive power of an ideal of definition
is again one.  Implication (2) ⟹ (1) is Stacks 0GD0
(`AlgebraicGeometry.FormalSpace.isRigSmooth_of_isRigEtale`).

Two inputs are carried as explicit hypotheses because the library does not have them.

* `hAQI` is Stacks 0AQI, that a closed immersion whose target is an affine formal algebraic
  space is, on charts, the quotient by a closed ideal: the induced homomorphism of presenting
  rings is surjective and the quotient is adic of topologically finite type over the source.
  The source's proof of Stacks 0GD4 opens by invoking exactly this.  What the library carries of
  Stacks 0AQI is the countably indexed case, and even that only given the tautness of
  Stacks 0AN5, which is not carried; the surjectivity, as opposed to the dense image of
  `AlgebraicGeometry.FormalSpace.denseRange_of_isClosedImmersion_formalSpectrumMap`, is exactly
  what tautness is needed for.
* `hGCZ` is Stacks 0GCZ, read as the source's proof reads it: "it is enough to check that each
  ring map `B → A` appearing in (3) is rig-étale".  Condition (3) constrains only the fibre
  product charts, while Definition 0AQM quantifies over all affine representable étale squares,
  and passing between the two is the locality of rig-étaleness on `WAdm^{Noeth}` of
  Stacks 0AQL together with the covering comparison of Stacks 0ANG.

Everything else is proved: that the fibre product chart is an affine formal algebraic space
follows from Stacks 0AKP (`AlgebraicGeometry.isAffineFormalAlgebraicSpace_of_affine`) applied to
the base-changed closed immersion of Stacks 0GHX, and that the fibre product projection to `X`
is representable étale follows from the base-change stability of Stacks 0AIM charts.

## References

* [Stacks Project, Tag 0AQI](https://stacks.math.columbia.edu/tag/0AQI)
* [Stacks Project, Tag 0GCI](https://stacks.math.columbia.edu/tag/0GCI)
* [Stacks Project, Tag 0GCZ](https://stacks.math.columbia.edu/tag/0GCZ)
* [Stacks Project, Tag 0GD0](https://stacks.math.columbia.edu/tag/0GD0)
* [Stacks Project, Tag 0GD4](https://stacks.math.columbia.edu/tag/0GD4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Charts

/-- **Stacks 0GD4, condition (3).** For every affine formal algebraic space `V`, every
representable étale `V ⟶ Y` and every fibre product of `f` along it, the induced morphism of
presenting rings of `WAdm^{Noeth}` is surjective and some ideal of definition of the source
annihilates the conormal module `J / J²` of its kernel `J`. -/
abbrev HasAnnihilatedConormalOnPullbackCharts {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (V : FppfSheaf B S hS) (_hV : IsAffineFormalAlgebraicSpace B S hS V) (b : V ⟶ Y)
    (_hb : IsRepresentableEtale B S hS b) (U : FppfSheaf B S hS) (a : U ⟶ X) (t : U ⟶ V),
    IsPullback a t f b → ∀ (A C : Type u)
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
        [IsNoetherianRing A]
      [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
        [IsNoetherianRing C],
      TopologicalRing.IsAdic A → TopologicalRing.IsAdic C →
      ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
        (E : QuotientSystem B S hS C) (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D)
        (g : ContinuousHom D E),
        t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv →
          Function.Surjective g.toRingHom ∧
            ∃ I : Ideal A, TopologicalRing.IsIdealOfDefinition I ∧
              I * RingHom.ker g.toRingHom ≤ RingHom.ker g.toRingHom ^ 2

/-- The condition of `AlgebraicGeometry.FormalSpace.HasAnnihilatedConormalOnPullbackCharts`
with the conclusion replaced by rig-étaleness of the chart homomorphism in the sense of
Definition 0GCV. This is the antecedent of Stacks 0GCZ as the proof of Stacks 0GD4 uses it. -/
abbrev HasRigEtaleOnPullbackCharts {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (V : FppfSheaf B S hS) (_hV : IsAffineFormalAlgebraicSpace B S hS V) (b : V ⟶ Y)
    (_hb : IsRepresentableEtale B S hS b) (U : FppfSheaf B S hS) (a : U ⟶ X) (t : U ⟶ V),
    IsPullback a t f b → ∀ (A C : Type u)
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
        [IsNoetherianRing A]
      [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
        [IsNoetherianRing C],
      TopologicalRing.IsAdic A → TopologicalRing.IsAdic C →
      ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
        (E : QuotientSystem B S hS C) (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D)
        (g : ContinuousHom D E),
        t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv → RingHom.IsRigEtale g.toRingHom

/-- The condition of `AlgebraicGeometry.FormalSpace.HasAnnihilatedConormalOnPullbackCharts`
with the conclusion replaced by the chart homomorphism being a surjection which is adic of
topologically finite type — condition (6) of Tag 0GBW.  This is the content of Stacks 0AQI
which the proof of Stacks 0GD4 uses. -/
abbrev HasAdicQuotientOnPullbackCharts {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (V : FppfSheaf B S hS) (_hV : IsAffineFormalAlgebraicSpace B S hS V) (b : V ⟶ Y)
    (_hb : IsRepresentableEtale B S hS b) (U : FppfSheaf B S hS) (a : U ⟶ X) (t : U ⟶ V),
    IsPullback a t f b → ∀ (A C : Type u)
      [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
        [IsNoetherianRing A]
      [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsLinearTopology C C]
        [IsNoetherianRing C],
      TopologicalRing.IsAdic A → TopologicalRing.IsAdic C →
      ∀ (hA : TopologicalRing.IsWeaklyAdmissible A) (D : QuotientSystem B S hS A)
        (E : QuotientSystem B S hS C) (eU : U ≅ formalSpectrum E) (eV : V ≅ formalSpectrum D)
        (g : ContinuousHom D E),
        t = eU.hom ≫ formalSpectrumMap hA g ≫ eV.inv →
          Function.Surjective g.toRingHom ∧
            Rig.FiniteTypeAdicAlgebraForEveryIdeal g.toRingHom

end Charts

section Geometry

/-- A closed immersion of fppf sheaves is an affine morphism. -/
private theorem isAffineHom_of_isClosedImmersion {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : IsClosedImmersion B S hS f) :
    (MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative
        (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) f := by
  have hle : MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS) ≤
      MorphismProperty.inverseImage (@IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS) := by
    intro U V g hg
    change AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map g) at hg
    show IsAffineHom ((BigFppfOver.toScheme B S hS).map g)
    exact (isClosedImmersion_iff_isAffineHom.mp hg).1
  exact MorphismProperty.relative_monotone
    (F := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) hle f
    (isClosedImmersionInto_of_isClosedImmersion B S hS f hf)

/-- The source of a closed immersion whose target is an affine formal algebraic space is an
affine formal algebraic space. -/
private theorem isAffineFormalAlgebraicSpace_of_isClosedImmersion {X Y : FppfSheaf B S hS}
    (f : X ⟶ Y) (hY : IsAffineFormalAlgebraicSpace B S hS Y)
    (hf : IsClosedImmersion B S hS f) : IsAffineFormalAlgebraicSpace B S hS X :=
  AlgebraicGeometry.isAffineFormalAlgebraicSpace_of_affine B S hS f hY
    (isAffineHom_of_isClosedImmersion B S hS f hf)

/-- Representable étale morphisms are stable under base change along an arbitrary cartesian
square. -/
private theorem isRepresentableEtale_of_isPullback {X Y U V : FppfSheaf B S hS}
    {a : U ⟶ X} {t : U ⟶ V} {f : X ⟶ Y} {b : V ⟶ Y} (sq : IsPullback a t f b)
    (hb : IsRepresentableEtale B S hS b) : IsRepresentableEtale B S hS a := by
  obtain ⟨hbrep, hbet⟩ := hb
  have hsq : IsPullback t.hom a.hom b.hom f.hom :=
    sq.flip.map (sheafToPresheaf (BigFppfOver.topology B S hS) _)
  exact ⟨Space.isRepresentableByAlgebraicSpacesULift_of_isPullback B S hS
      t.hom a.hom b.hom f.hom hsq hbrep,
    isEtaleULift_pullback_fst_of_isPullback B S hS hsq hbet⟩

end Geometry

section Rings

/-- An adic topological ring has an ideal of definition which defines its topology and for
which it is adically complete. -/
theorem exists_idealOfDefinition_isAdicComplete {R : Type u} [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] (h : TopologicalRing.IsAdic R) :
    ∃ I : Ideal R, TopologicalRing.IsIdealOfDefinition I ∧ _root_.IsAdic I ∧
      IsAdicComplete I R := by
  obtain ⟨⟨I, hIdef, hIadic⟩, hT2, hCompl⟩ := h
  refine ⟨I, hIdef, hIadic, ?_⟩
  let _ : UniformSpace R := IsTopologicalAddGroup.rightUniformSpace R
  have _ : IsUniformAddGroup R := isUniformAddGroup_of_addCommGroup
  exact (IsAdic.isAdicComplete_iff hIadic).mpr ⟨hCompl, hT2⟩

/-- A positive power of an ideal defining an adic topology on a Noetherian ring is again an
ideal of definition. -/
theorem isIdealOfDefinition_pow_succ {R : Type u} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] [IsNoetherianRing R] {I : Ideal R}
    (hI : _root_.IsAdic I) (n : ℕ) : TopologicalRing.IsIdealOfDefinition (I ^ (n + 1)) :=
  TopologicalRing.isIdealOfDefinition_of_isWeakIdealOfDefinition
    (TopologicalRing.isWeakIdealOfDefinition_pow_of_isAdic hI n)
    (Ideal.fg_of_isNoetherianRing _)

end Rings

/-- **Stacks 0GD4.** For a closed immersion `f : X ⟶ Y` of locally Noetherian formal algebraic
spaces over `S`, rig-smoothness of `f` (Definition 0GCP), rig-étaleness of `f`
(Definition 0AQM), and the condition that on every affine representable étale chart `V ⟶ Y` of
the target the fibre product `X ×_Y V ⟶ V` be given by a surjection of `WAdm^{Noeth}` whose
kernel `J` has `J / J²` annihilated by an ideal of definition of the source, are all equivalent.

The implication (2) ⟹ (1) is Stacks 0GD0.  The implications (1) ⟹ (3) and (3) ⟹ (2) rest on
the computation of the completed naive cotangent complex of a surjection, for which both
rigidity notions reduce to the annihilation of the conormal module.  The hypotheses `hAQI` and
`hGCZ` carry Stacks 0AQI — that the fibre product chart map is a surjection which is adic of
topologically finite type — and Stacks 0GCZ in the form in which the source's proof uses it,
that rig-étaleness need only be checked on the ring maps appearing in (3). -/
@[stacks 0GD4 "the full equivalence of the three conditions, with Stacks 0AQI (the fibre \
product chart map being a surjection of WAdm^Noeth which is adic of topologically finite type) \
and Stacks 0GCZ (rig-étaleness need only be checked on the ring maps appearing in condition \
(3)) carried as the hypotheses `hAQI` and `hGCZ`"]
theorem isRigSmooth_tfae_of_isClosedImmersion {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (_hX : IsLocallyNoetherian B S hS X) (_hY : IsLocallyNoetherian B S hS Y)
    (hf : IsClosedImmersion B S hS f)
    (hAQI : HasAdicQuotientOnPullbackCharts B S hS f)
    (hGCZ : HasRigEtaleOnPullbackCharts B S hS f → IsRigEtale B S hS f) :
    List.TFAE
      [IsRigSmooth B S hS f, IsRigEtale B S hS f,
        HasAnnihilatedConormalOnPullbackCharts B S hS f] := by
  tfae_have 2 → 1 := fun h ↦ isRigSmooth_of_isRigEtale B S hS f h
  tfae_have 1 → 3 := by
    intro h V hV b hb U a t sq A C _ _ _ _ _ _ _ _ _ _ hAdicA hAdicC hA D E eU eV g hg
    obtain ⟨hsurj, hft⟩ := hAQI V hV b hb U a t sq A C hAdicA hAdicC hA D E eU eV g hg
    refine ⟨hsurj, ?_⟩
    have ht : IsClosedImmersion B S hS t := isClosedImmersion_of_isPullback B S hS sq hf
    have hU : IsAffineFormalAlgebraicSpace B S hS U :=
      isAffineFormalAlgebraicSpace_of_isClosedImmersion B S hS t hV ht
    obtain ⟨harep, haet⟩ := isRepresentableEtale_of_isPullback B S hS sq hb
    obtain ⟨hbrep, hbet⟩ := hb
    obtain ⟨hft', I, hI, hsm⟩ :=
      h U V hU hV a b t harep hbrep haet hbet sq.w A C hAdicA hAdicC hA D E eU eV g hg
    obtain ⟨I₀, hI₀def, hI₀adic, hI₀complete⟩ := exists_idealOfDefinition_isAdicComplete hAdicA
    have hC : TopologicalRing.IsWeaklyAdmissible C := by
      obtain ⟨K, -, hKadic, hKcomplete⟩ := exists_idealOfDefinition_isAdicComplete hAdicC
      exact TopologicalRing.isWeaklyAdmissible_of_isAdic hKadic hKcomplete
    have hsm₀ : Rig.IsRigSmooth (Rig.adicFiniteTypeAlgebra g.toRingHom hft' I₀ hI₀def) :=
      (Rig.isRigSmooth_iff_forall_idealOfDefinition hA hC g.toRingHom g.continuous hft').mp
        ⟨I, hI, hsm⟩ I₀ hI₀def
    let _ : IsAdicComplete I₀ A := hI₀complete
    obtain ⟨c, hc⟩ := (Rig.isRigSmooth_iff_exists_pow_mul_ker_le_sq
      (Rig.adicFiniteTypeAlgebra g.toRingHom hft' I₀ hI₀def) hsurj).mp hsm₀
    refine ⟨I₀ ^ (c + 1), isIdealOfDefinition_pow_succ hI₀adic c, Ideal.mul_le.mpr ?_⟩
    intro r hr s hs
    exact hc r (Ideal.pow_le_pow_right (Nat.le_succ c) hr) s hs
  tfae_have 3 → 2 := by
    intro h3
    refine hGCZ ?_
    intro V hV b hb U a t sq A C _ _ _ _ _ _ _ _ _ _ hAdicA hAdicC hA D E eU eV g hg
    obtain ⟨hsurj, hft⟩ := hAQI V hV b hb U a t sq A C hAdicA hAdicC hA D E eU eV g hg
    obtain ⟨-, I, hI, hJ⟩ := h3 V hV b hb U a t sq A C hAdicA hAdicC hA D E eU eV g hg
    obtain ⟨I₀, hI₀def, hI₀adic, hI₀complete⟩ := exists_idealOfDefinition_isAdicComplete hAdicA
    obtain ⟨n, hnle, -⟩ := hI₀def.exists_pow_le_and_pow_le hI
    let _ : IsAdicComplete I₀ A := hI₀complete
    refine RingHom.isRigEtale_of_isRigEtaleOver hft I₀ hI₀def
      (Rig.isRigEtaleOver_of_isRigEtale_adicFiniteTypeAlgebra g.toRingHom hft I₀ hI₀def ?_)
    refine (Rig.isRigEtale_iff_exists_pow_mul_ker_le_sq
      (Rig.adicFiniteTypeAlgebra g.toRingHom hft I₀ hI₀def) hsurj).mpr ⟨n, ?_⟩
    intro r hr s hs
    exact hJ (Ideal.mul_mem_mul (hnle hr) hs)
  tfae_finish

end AlgebraicGeometry.FormalSpace

end
