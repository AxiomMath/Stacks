module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveFaithfullyFlat
public import StacksFrontier.AlgebraicGeometry.FormalSpace.TautFormalSpectrumRepresentable
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.AlgebraicGeometry.FormalSpace.RigFlatComposition
import StacksFrontier.RingTheory.DiscreteValuationRing.EppCondition

/-!
# A composite of rig-surjective morphisms locally of finite type is rig-surjective

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of formal algebraic spaces over `S` which are locally of finite type. **Stacks 0AQR**
says that if `f` and `g` are rig-surjective then so is `g ∘ f`. This file proves it.

An adic point `p : Spf R ⟶ Z` out of a complete discrete valuation ring lifts through `g` over
an extension `R ⊂ R'` of complete discrete valuation rings; the lift `y : Spf R' ⟶ Y` is again
adic, so it lifts through `f` over a further extension `R' ⊂ R''`; and the two extensions
compose to the single extension `R ⊂ R''` that the definition of rig-surjectivity asks for.
Local finite type of the composite is Stacks 0AQ4.

## Main results

* `AlgebraicGeometry.FormalSpace.IsRigSurjective.comp_of_isFormalAlgebraicSpace`:
  **Stacks 0AQR**, with the source of the second factor assumed to be a formal algebraic space.

`StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjective` carries a second form of Stacks 0AQR,
`AlgebraicGeometry.FormalSpace.IsRigSurjective.comp`, which instead of that assumption takes as
hypotheses the two results used here to establish adicness of the intermediate lift. Neither
form implies the other: the hypotheses are different, not stronger or weaker.

## Implementation notes

Adicness of the intermediate lift `y` is the only step which is not bookkeeping, and it is the
reason this form lives in its own module rather than beside the predicate and Stacks 0AQT in
`StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjective`. It needs two results which that
module cannot see:

* `y ≫ g` is `Spf R' ⟶ Spf R ⟶ Z`, whose first factor is `Spf` of an adic — hence taut, by
  Stacks 0GBS part (1) — homomorphism of complete discrete valuation rings, and that `Spf` of a
  taut homomorphism of weakly admissible topological rings is representable by algebraic spaces
  is the implication (3) ⟹ (1) of **Stacks 0AN5**,
  `FormalSpace.isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isTaut`.
  Its site condition `D'.HasLargeSite` (Stacks 0AIF) is not assumed: `R'` is adic and adically
  complete and already carries a quotient system, so
  `AlgebraicGeometry.FormalSpace.mk_lt_cutoff_of_quotientSystem` bounds `#R'` by the cutoff of
  the site and `AlgebraicGeometry.FormalSpace.hasLargeSite_of_mk_lt_cutoff` supplies the
  condition.
* cancelling `g` off the resulting representable composite is **Stacks 0AQ0**,
  `FormalSpace.isRepresentableByAlgebraicSpacesULift_of_comp_of_isFormalAlgebraicSpace`,
  whose hypothesis is that the source of `g` be a formal algebraic space. That is `hY`, which
  the source of Stacks 0AQR assumes of `Y` in the stronger form "locally Noetherian formal
  algebraic space".

The two live in modules neither of which imports the other, and the cardinality bound lives in
a third, so the discharge is made here.

## References

* [Stacks Project, Tag 0AQR](https://stacks.math.columbia.edu/tag/0AQR)
* [Stacks Project, Tag 0AN5](https://stacks.math.columbia.edu/tag/0AN5)
* [Stacks Project, Tag 0AQ0](https://stacks.math.columbia.edu/tag/0AQ0)
* [Stacks Project, Tag 0AQ4](https://stacks.math.columbia.edu/tag/0AQ4)
* [Stacks Project, Tag 0AIF](https://stacks.math.columbia.edu/tag/0AIF)
* [Stacks Project, Tag 0GBS](https://stacks.math.columbia.edu/tag/0GBS)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.FormalSpace

universe u

/-- **A lift of an adic point along an extension of complete discrete valuation rings is again
adic.** Let `g : X ⟶ Y` be a morphism of fppf sheaves whose source `X` is a formal algebraic
space, let `p : Spf R ⟶ Y` be an adic morphism out of the formal spectrum of a complete discrete
valuation ring, let `R ⊂ R'` be an extension of complete discrete valuation rings realized by a
continuous homomorphism `e`, and let `y : Spf R' ⟶ X` satisfy `y ≫ g = Spf(e) ≫ p`. Then `y` is
adic.

This is the one step of Stacks 0AQR which is not bookkeeping, and it is what every iterated
lifting argument for rig-surjectivity needs: the definition of rig-surjectivity produces a lift
but does not record its adicness, while feeding that lift to a second lifting step requires it.

The composite `Spf(e) ≫ p` is representable by algebraic spaces because `e` is adic — the
maximal ideal of `R` generates a power of the maximal ideal of `R'`, which is the ramification
index characterization of an extension of discrete valuation rings — hence taut by Stacks 0GBS
part (1), and `Spf` of a taut homomorphism of weakly admissible topological rings is
representable, which is the implication (3) ⟹ (1) of Stacks 0AN5. Cancelling `g` off the
composite is Stacks 0AQ0, whose hypothesis on the source of `g` is `hX`. The site condition of
Stacks 0AIF for `D'` is not assumed: `R'` is adic and adically complete and carries a quotient
system, so its cardinality is below the cutoff of the site. -/
theorem isRepresentableByAlgebraicSpacesULift_of_comp_eq_formalSpectrumMap_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {R R' : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsLinearTopology R R] [CommRing R'] [IsDomain R']
    [IsDiscreteValuationRing R'] [TopologicalSpace R'] [IsTopologicalRing R']
    [IsLinearTopology R' R'] [Algebra R R'] [IsDiscreteValuationRing.IsExtension R R']
    (hRadic : IsAdic (IsLocalRing.maximalIdeal R))
    (hR'adic : IsAdic (IsLocalRing.maximalIdeal R'))
    (hR'complete : IsAdicComplete (IsLocalRing.maximalIdeal R') R')
    (hRweak : TopologicalRing.IsWeaklyAdmissible R)
    (hR'weak : TopologicalRing.IsWeaklyAdmissible R')
    {X Y : FppfSheaf B S hS} (g : X ⟶ Y) (hX : IsFormalAlgebraicSpace B S hS X)
    {D : QuotientSystem B S hS R} {D' : QuotientSystem B S hS R'} (e : ContinuousHom D D')
    (he : e.toRingHom = algebraMap R R') {p : formalSpectrum D ⟶ Y}
    (hp : Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS p.hom)
    {y : formalSpectrum D' ⟶ X} (hy : y ≫ g = formalSpectrumMap hRweak e ≫ p) :
    Space.IsRepresentableByAlgebraicSpacesULift.{u + 1} B S hS y.hom := by
  have hetaut : RingHom.IsTaut e.toRingHom := by
    refine RingHom.isTaut_of_isAdic e.toRingHom
      ⟨IsLocalRing.maximalIdeal R, hRadic, ?_⟩
    obtain ⟨hpos, hpow, -, -⟩ := IsDiscreteValuationRing.ramificationIndex_characterization R R'
    rw [he, hpow]
    -- The ramification index is positive, and a positive power of the defining ideal of an
    -- adic topology defines the same topology: the powers of `𝔪 ^ n` are cofinal among the
    -- powers of `𝔪`, each being contained in the other at a shift.
    set n := IsDiscreteValuationRing.ramificationIndex R R' with hn
    rw [isAdic_iff]
    refine ⟨fun k => by simpa [pow_mul] using (isAdic_iff.mp hR'adic).1 (n * k), fun s hs => ?_⟩
    obtain ⟨k, -, hk⟩ := hR'adic.hasBasis_nhds_zero.mem_iff.mp hs
    refine ⟨k, fun x hx => hk ?_⟩
    have hle : (IsLocalRing.maximalIdeal R' ^ n) ^ k ≤ IsLocalRing.maximalIdeal R' ^ k := by
      simpa [pow_mul] using Ideal.pow_le_pow_right
        (I := IsLocalRing.maximalIdeal R') (Nat.le_mul_of_pos_left k hpos)
    exact hle hx
  have hcomp := Space.isRepresentableByAlgebraicSpacesULift_comp B S hS
    (formalSpectrumMap hRweak e).hom p.hom
    (isRepresentableByAlgebraicSpacesULift_formalSpectrumMap_of_isTaut B S hS hRweak hR'weak
      D D' (hasLargeSite_of_mk_lt_cutoff D'
        (mk_lt_cutoff_of_quotientSystem hR'adic hR'complete D')) e hetaut) hp
  have hyg : y.hom ≫ g.hom = (formalSpectrumMap hRweak e).hom ≫ p.hom :=
    congrArg (fun m : formalSpectrum D' ⟶ Y => m.hom) hy
  exact isRepresentableByAlgebraicSpacesULift_of_comp_of_isFormalAlgebraicSpace B S hS y g hX
    (hyg ▸ hcomp)

/-- **Stacks 0AQR.** A composite of rig-surjective morphisms of formal algebraic spaces over `S`
which are locally of finite type is locally of finite type and rig-surjective: an adic point of
the final target lifts through the second factor over an extension of complete discrete
valuation rings, that lift is again adic, and so lifts through the first factor over a further
extension; the two extensions compose to one.

Adicness of the intermediate lift is Stacks 0AQ0 for the second factor, applied to the
composite made representable by the implication (3) ⟹ (1) of Stacks 0AN5. The hypothesis `hY`
is what Stacks 0AQ0 asks of the source of the second factor, and the source of Stacks 0AQR
assumes it of `Y` in the stronger form of a locally Noetherian formal algebraic space. -/
@[stacks 0AQR]
theorem IsRigSurjective.comp_of_isFormalAlgebraicSpace
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) (hg : IsLocallyOfFiniteType B S hS g)
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
  obtain ⟨R'', hR''ring, hR''dom, hR''dvr, hR''alg, hR''ext, hR''top, hR''topring, hR''lin,
    hR''adic, hR''complete, D'', e', x, he', hx⟩ :=
    hsf R' hR'adic hR'complete hR'weak D' y
      (isRepresentableByAlgebraicSpacesULift_of_comp_eq_formalSpectrumMap_comp B S hS
        hRadic hR'adic hR'complete hRweak hR'weak g hY e he hp hy)
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
