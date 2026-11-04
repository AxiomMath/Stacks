module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Defs
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FormalSpectrum
public import StacksFrontier.RingTheory.DiscreteValuationRing.Solution
public import StacksFrontier.Topology.Algebra.AdicTopology.Taut
import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
import StacksFrontier.RingTheory.DiscreteValuationRing.EppCondition
import StacksFrontier.Topology.Algebra.AdicTopology.AdicRingMap
import StacksFrontier.Topology.Algebra.AdicTopology.WeaklyAdmissibleAdic

/-!
# Rig-surjective morphisms of formal algebraic spaces

Let `S` be a scheme contained in a big fppf site `B`. A morphism `f : X ⟶ Y` of locally
Noetherian formal algebraic spaces over `S` which is locally of finite type is
*rig-surjective* (Stacks 0AQQ) when every adic morphism `p : Spf R ⟶ Y` out of the formal
spectrum of a complete discrete valuation ring `R` lifts to `X` after an extension
`R ⊂ R'` of complete discrete valuation rings: there is a morphism `Spf R' ⟶ X` whose
composite with `f` agrees with the composite of `Spf R' ⟶ Spf R` with `p`.

Rig-surjectivity of a composite forces rig-surjectivity of its second factor (Stacks 0AQT):
a lift to `X` of an adic point of `Z` becomes a lift to `Y` once composed with `f`.

Conversely a composite of rig-surjective morphisms locally of finite type is rig-surjective
(Stacks 0AQR): an adic point `Spf R ⟶ Z` lifts through `g` over an extension `R ⊂ R'`, that
lift is again adic, so it lifts through `f` over a further extension `R' ⊂ R''`, and the two
extensions compose to the single extension `R ⊂ R''` the definition asks for.

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsRigSurjective`: **Stacks 0AQQ**.

## Main results

* `AlgebraicGeometry.FormalSpace.IsRigSurjective.of_comp`: **Stacks 0AQT**.
* `AlgebraicGeometry.FormalSpace.IsRigSurjective.comp`: **Stacks 0AQR**, carrying two
  hypotheses — see below.

## Implementation notes

The formal spectrum is the one of Stacks 0AIF, so `R` is presented over `S` by an
`AlgebraicGeometry.FormalSpace.QuotientSystem` and the vertical map of formal spectra is
`AlgebraicGeometry.FormalSpace.formalSpectrumMap` applied to an
`AlgebraicGeometry.FormalSpace.ContinuousHom` whose ring map is required to be the structure
map of `R'` over `R`. A discrete valuation ring is complete when it is `IsAdicComplete` for
its maximal ideal, whose adic topology is the one it is given, and
`IsDiscreteValuationRing.IsExtension` is the extension condition of Stacks 09E4, namely an
injective local algebra map. Weak admissibility of the topology of `R` is quantified over
rather than derived: it is what `formalSpectrumMap` consumes, and it holds for every complete
discrete valuation ring carrying its maximal-adic topology.

Adicness of `p` is rendered by representability by algebraic spaces, which **Stacks 0AQ3**
identifies with adicness for a morphism of locally adic\* formal algebraic spaces — and `Spf R`
and a locally Noetherian `Y` are such. Representability is the universe-lifted notion of
`StacksFrontier.AlgebraicGeometry.Spaces.LargeValued`, since the sheaves carrying formal
algebraic spaces take values in `Type (u + 1)`. The extension `R'` is quantified in the
universe of the site, which is where a ring whose formal spectrum lies over `S` must sit.

As for `AlgebraicGeometry.FormalSpace.IsRigFlat`, the locally Noetherian hypotheses on the
source and target and the locally finite type hypothesis on the morphism are imposed by
applications rather than built into the predicate, which lets it be used before those
hypotheses are available. Being an `abbrev`, the predicate hands its quantifier interface
directly to consumers with no unfolding lemma.

### The two hypotheses carried by Stacks 0AQR

Adicness of the intermediate lift `Spf R' ⟶ Y` is the only step of Stacks 0AQR which is not
bookkeeping, and it needs two results the library does not have. Its composite with `g` is
`Spf R' ⟶ Spf R ⟶ Z`, whose second factor is adic by hypothesis and whose first factor is
`Spf` of an adic — hence taut — homomorphism of complete discrete valuation rings; that `Spf`
of a taut homomorphism of weakly admissible rings is representable by algebraic spaces is
**Stacks 0AN5**, (3) implies (1), and is carried as the hypothesis
`hformalSpectrumMap`. Cancelling `g` off the resulting representable composite is **Stacks
0AQ0**, and is carried for `g` as the hypothesis `hcancel`. Everything else — tautness of the
extension, weak admissibility of `R'`, the composite extension and its quotient system, and
the finite type condition on the composite from Stacks 0AQ4 — is proved here.

The first hypothesis would follow from the implication (3) to (2) of Stacks 0AN5 together with
`AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_formalSpectrumMap`, which
is the implication (2) to (1) of that lemma.

## References

* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AQ0](https://stacks.math.columbia.edu/tag/0AQ0)
* [Stacks Project, Tag 0AQ4](https://stacks.math.columbia.edu/tag/0AQ4)
* [Stacks Project, Tag 0AQQ](https://stacks.math.columbia.edu/tag/0AQQ)
* [Stacks Project, Tag 0AQR](https://stacks.math.columbia.edu/tag/0AQR)
* [Stacks Project, Tag 0AQT](https://stacks.math.columbia.edu/tag/0AQT)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u

/-- **Stacks 0AQQ.** A morphism `f : X ⟶ Y` of fppf sheaves on the big fppf site of `S` is
*rig-surjective* when every adic morphism `p : Spf R ⟶ Y` out of the formal spectrum of a
complete discrete valuation ring `R` lifts to `X` along the formal spectrum of an extension
`R ⊂ R'` of complete discrete valuation rings. Adic means representable by algebraic spaces,
which is the definition of an adic morphism, Stacks 0AQ3.

The source defines the notion for a morphism of locally Noetherian formal algebraic spaces that
is locally of finite type. The predicate drops those standing hypotheses and asks for the same
lifting condition for any morphism of fppf sheaves. Under them it is the source's definition. -/
@[stacks 0AQQ]
abbrev IsRigSurjective (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : FppfSheaf B S hS} (f : X ⟶ Y) : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R],
    IsAdic (IsLocalRing.maximalIdeal R) → IsAdicComplete (IsLocalRing.maximalIdeal R) R →
      ∀ (hR : TopologicalRing.IsWeaklyAdmissible R) (D : QuotientSystem B S hS R)
        (p : formalSpectrum D ⟶ Y),
        Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS p.hom →
          ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
            (_ : Algebra R R') (_ : IsDiscreteValuationRing.IsExtension R R')
            (_ : TopologicalSpace R') (_ : IsTopologicalRing R') (_ : IsLinearTopology R' R'),
            IsAdic (IsLocalRing.maximalIdeal R') ∧
              IsAdicComplete (IsLocalRing.maximalIdeal R') R' ∧
                ∃ (D' : QuotientSystem B S hS R') (e : ContinuousHom D D')
                  (x : formalSpectrum D' ⟶ X),
                  e.toRingHom = algebraMap R R' ∧ x ≫ f = formalSpectrumMap hR e ≫ p

/-- **Stacks 0AQT.** If a composition of morphisms of formal algebraic spaces over `S` is
rig-surjective, then so is its second factor: a lift of an adic point of the final target to
the initial source is, after composition with the first factor, a lift to the intermediate
space. -/
@[stacks 0AQT]
theorem IsRigSurjective.of_comp (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hgf : IsRigSurjective B S hS (f ≫ g)) :
    IsRigSurjective B S hS g := by
  intro R _ _ _ _ _ _ hadic hcomplete hR D p hp
  obtain ⟨R', hring, hdom, hdvr, halg, hext, htop, htopring, hlin, hadic', hcomplete',
    D', e, x, he, hx⟩ := hgf R hadic hcomplete hR D p hp
  exact ⟨R', hring, hdom, hdvr, halg, hext, htop, htopring, hlin, hadic', hcomplete',
    D', e, x ≫ f, he, by rw [Category.assoc]; exact hx⟩

/-- A positive power of the defining ideal of an adic topology defines the same topology: the
powers of `I ^ e` are cofinal among the powers of `I`, both being contained in each other at
a shift. -/
private theorem isAdic_pow {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    {I : Ideal A} (hI : IsAdic I) {e : ℕ} (he : 1 ≤ e) : IsAdic (I ^ e) := by
  rw [isAdic_iff]
  refine ⟨fun n => by simpa [pow_mul] using (isAdic_iff.mp hI).1 (e * n), fun s hs => ?_⟩
  obtain ⟨n, -, hn⟩ := hI.hasBasis_nhds_zero.mem_iff.mp hs
  refine ⟨n, fun x hx => hn ?_⟩
  have hle : (I ^ e) ^ n ≤ I ^ n := by
    simpa [pow_mul] using Ideal.pow_le_pow_right (I := I) (Nat.le_mul_of_pos_left n he)
  exact hle hx

/-- **Stacks 0AQR**, carrying two hypotheses. A composite of rig-surjective morphisms of formal
algebraic spaces over `S` which are locally of finite type is locally of finite type and
rig-surjective: an adic point of the final target lifts through the second factor over an
extension of complete discrete valuation rings, that lift is again adic, and so lifts through
the first factor over a further extension; the two extensions compose to one.

Adicness of the intermediate lift is `hcancel`, which is **Stacks 0AQ0** for the second factor,
applied to the composite made representable by `hformalSpectrumMap`, which is **Stacks 0AN5**,
(3) implies (1); neither is available in this library. -/
@[stacks 0AQR "assuming Stacks 0AN5 and, for the second factor, Stacks 0AQ0"]
theorem IsRigSurjective.comp (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsLocallyOfFiniteType B S hS f) (hg : IsLocallyOfFiniteType B S hS g)
    (hformalSpectrumMap : ∀ (A₁ A₂ : Type u) [CommRing A₁] [TopologicalSpace A₁]
      [IsTopologicalRing A₁] [IsLinearTopology A₁ A₁] [CommRing A₂] [TopologicalSpace A₂]
      [IsTopologicalRing A₂] (hA₁ : TopologicalRing.IsWeaklyAdmissible A₁)
      (D₁ : QuotientSystem B S hS A₁) (D₂ : QuotientSystem B S hS A₂)
      (φ : ContinuousHom D₁ D₂), RingHom.IsTaut φ.toRingHom →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (formalSpectrumMap hA₁ φ).hom)
    (hcancel : ∀ {W : FppfSheaf B S hS} (q : W ⟶ Y),
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS (q.hom ≫ g.hom) →
      Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS q.hom)
    (hsf : IsRigSurjective B S hS f) (hsg : IsRigSurjective B S hS g) :
    IsLocallyOfFiniteType B S hS (f ≫ g) ∧ IsRigSurjective B S hS (f ≫ g) := by
  refine ⟨IsLocallyOfFiniteType.comp B S hS f g hf hg, ?_⟩
  intro R _ _ _ _ _ _ hRadic hRcomplete hRweak D p hp
  obtain ⟨R', hR'ring, hR'dom, hR'dvr, hR'alg, hR'ext, hR'top, hR'topring, hR'lin, hR'adic,
    hR'complete, D', e, y, he, hy⟩ := hsg R hRadic hRcomplete hRweak D p hp
  let : CommRing R' := hR'ring
  let : IsDomain R' := hR'dom
  let : IsDiscreteValuationRing R' := hR'dvr
  let : Algebra R R' := hR'alg
  let : IsDiscreteValuationRing.IsExtension R R' := hR'ext
  let : TopologicalSpace R' := hR'top
  let : IsTopologicalRing R' := hR'topring
  let : IsLinearTopology R' R' := hR'lin
  have hR'weak : TopologicalRing.IsWeaklyAdmissible R' :=
    TopologicalRing.isWeaklyAdmissible_of_isAdic hR'adic hR'complete
  have hetaut : RingHom.IsTaut e.toRingHom := by
    refine RingHom.isTaut_of_isAdic e.toRingHom e.continuous
      ⟨IsLocalRing.maximalIdeal R, hRadic, ?_⟩
    obtain ⟨hpos, hpow, -, -⟩ := IsDiscreteValuationRing.ramificationIndex_characterization R R'
    rw [he, hpow]
    exact isAdic_pow hR'adic hpos
  have hcomp := Space.isRepresentableByAlgebraicSpacesULift_comp B S hS
    (formalSpectrumMap hRweak e).hom p.hom
    (hformalSpectrumMap R R' hRweak D D' e hetaut) hp
  have hyg : y.hom ≫ g.hom = (formalSpectrumMap hRweak e).hom ≫ p.hom :=
    congrArg (fun m : formalSpectrum D' ⟶ Z => m.hom) hy
  obtain ⟨R'', hR''ring, hR''dom, hR''dvr, hR''alg, hR''ext, hR''top, hR''topring, hR''lin,
    hR''adic, hR''complete, D'', e', x, he', hx⟩ :=
    hsf R' hR'adic hR'complete hR'weak D' y (hcancel y (hyg ▸ hcomp))
  let : CommRing R'' := hR''ring
  let : IsDomain R'' := hR''dom
  let : IsDiscreteValuationRing R'' := hR''dvr
  let : Algebra R' R'' := hR''alg
  let : IsDiscreteValuationRing.IsExtension R' R'' := hR''ext
  let : TopologicalSpace R'' := hR''top
  let : IsTopologicalRing R'' := hR''topring
  let : IsLinearTopology R'' R'' := hR''lin
  let : Algebra R R'' := ((algebraMap R' R'').comp (algebraMap R R')).toAlgebra
  have halg : (algebraMap R R'' : R →+* R'') = (algebraMap R' R'').comp (algebraMap R R') :=
    RingHom.algebraMap_toAlgebra _
  let : IsScalarTower R R' R'' := IsScalarTower.of_algebraMap_eq fun z => by rw [halg]; rfl
  refine ⟨R'', inferInstance, inferInstance, inferInstance, inferInstance,
    IsDiscreteValuationRing.IsExtension.trans R R' R'', inferInstance, inferInstance,
    inferInstance, hR''adic, hR''complete, D'',
    ContinuousHom.comp hR'weak hRweak e' e, x, ?_, ?_⟩
  · rw [ContinuousHom.comp_toRingHom, he', he, halg]
  · rw [← Category.assoc, hx, Category.assoc, hy, ← Category.assoc,
      formalSpectrumMap_comp_eq hR'weak hRweak e' e]

end AlgebraicGeometry.FormalSpace

end
