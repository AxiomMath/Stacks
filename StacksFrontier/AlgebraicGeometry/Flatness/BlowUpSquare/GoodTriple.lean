module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ComplexAndDivisor
public import StacksFrontier.Homology.Eta.Perfect.DeterminantalIdeal
public import StacksFrontier.Homology.Eta.Perfect.DeterminantalIdealLocalPrincipality
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.PerfectDerivedPullback
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Affine charts and good triples for a perfect complex and a divisor

Let `(X, D, M)` be a triple as in Situation 0F8S: `X` a scheme, `D ⊂ X` an effective Cartier
divisor, and `M` a perfect object of `D(𝒪_X)`.  An *affine chart* for `(X, D, M)` is an affine
open `U = Spec(A) ⊂ X` together with a nonzerodivisor `f ∈ A` cutting out `D ∩ U` and a bounded
complex `M^•` of finite free `A`-modules representing `M|_U`.  The triple is *good* if every
point of `D` lies in an affine chart all of whose determinantal ideals `I_i(M^•, f)` are
principal.

This file introduces that vocabulary and the pulled-back triple `(Y, h⁻¹D, Lh^*M)`, which is
what the statements of Stacks 38.43 are phrased in.

## Main definitions

* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart`: an affine chart for the triple.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.determinantalIdeal`: the ideal
  `I_i(M^•, f)` of More on Algebra, Section 15.98, read off the chart.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.blowupCentre`: the product
  `∏ᵢ I_i(M^•, f)` of the determinantal ideals, the centre in which Stacks tag 0GTY blows up
  the chart.
* `AlgebraicGeometry.ComplexAndDivisorSituation.IsGoodTriple`: the good-triple condition.
* `AlgebraicGeometry.ComplexAndDivisorSituation.derivedPullbackObject`: the derived pullback
  `Lh^*M`, transported to the standard model of the derived category.
* `AlgebraicGeometry.ComplexAndDivisorSituation.pullback`: the triple `(Y, h⁻¹D, Lh^*M)`,
  defined whenever the pullback of `D` along `h` is defined.

## Main results

* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.pow_rank_mem_determinantalIdeal`:
  `f ^ rᵢ ∈ I_i(M^•, f)`, the observation of More on Algebra, Section 15.98 that makes the
  product of the determinantal ideals a `(U \ D)`-admissible centre.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.blowupCentre_fg` and
  `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.pow_mem_blowupCentre`: the centre
  `∏ᵢ I_i(M^•, f)` is of finite type and contains `f ^ (∑ᵢ rᵢ)`, hence is supported on `D ∩ U`.
  These are the two conditions on a centre in the definition of a `(U \ D)`-admissible blowing
  up, which is what Stacks tag 0GTY asserts of its morphism over an affine chart.
* `AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.determinantalIdeal_eq_top` and
  `AffineChart.prod_determinantalIdeal_eq_blowupCentre`: the factors in degrees where `M^•`
  vanishes are the unit ideal, so the finite product over the support of `M^•` is the tag's
  product over all `i ∈ ℤ`.
* `AlgebraicGeometry.ComplexAndDivisorSituation.isPerfect_derivedPullbackObject`: `Lh^*M` is
  again perfect, so the pulled-back triple is a triple in the sense of Situation 0F8S.
* `AlgebraicGeometry.ComplexAndDivisorSituation.isGoodTriple_of_isEmpty_supportSet`: a triple
  whose divisor has empty support is good.

## Implementation notes

The coordinate ring of an affine open `U` is taken to be its ring of sections `Γ(X, U)`, so
that no chosen isomorphism with a spectrum has to be carried around; the bounded complex of
finite free modules is recorded in chosen bases as a `BoundedComplex Γ(X, U)`, which is also
the input of `idealI`, the determinantal ideal of More on Algebra, Section 15.98.

"`M^•` represents `M|_U`" is expressed in the derived category: some cochain complex `E` of
`𝒪_X`-modules represents `M`, and the restriction of `E` to `U` becomes isomorphic, in the
derived category of `𝒪_U`-modules, to the `𝒪_U`-module complex associated with `M^•` by the
`tilde` equivalence on `Spec Γ(X, U)` transported along `U ≅ Spec Γ(X, U)`.  A situation may
carry an arbitrary model of the derived category of `𝒪_X`-modules, whereas the derived pullback
is formed in the standard model; `CategoryTheory.Localization.uniq` moves the object between
the two, and `AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_uniqFunctor_obj`
moves its perfectness.  This is why the pulled-back triple lands in universe `u + 1`.

## References

* [Stacks Project, Tag 0F8S](https://stacks.math.columbia.edu/tag/0F8S)
* [Stacks Project, Tag 0F7V](https://stacks.math.columbia.edu/tag/0F7V)
-/

@[expose] public noncomputable section

open CategoryTheory StrictlyPerfect

attribute [local instance] HasDerivedCategory.standard

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

/-- An **affine chart** `(U, A, f, M^•)` for a triple `(X, D, M)` as in Situation 0F8S: an
affine open `U ⊂ X` with coordinate ring `A = Γ(X, U)`, a nonzerodivisor `f ∈ A` cutting out
`D ∩ U`, and a bounded complex `M^•` of finite free `A`-modules, given in chosen bases,
representing `M|_U`. -/
structure AffineChart (S : ComplexAndDivisorSituation.{u, d}) where
  /-- The affine open subset `U` of `X`. -/
  U : S.X.affineOpens
  /-- The equation `f ∈ Γ(X, U)` cutting out `D ∩ U`. -/
  f : Γ(S.X, U)
  /-- The equation is a nonzerodivisor. -/
  regular : IsRegular f
  /-- `D ∩ U` is the closed subscheme cut out by `f`. -/
  divisor_ideal : S.D.ideal U = Ideal.span {f}
  /-- A bounded complex of finite free `Γ(X, U)`-modules in chosen bases. -/
  complex : BoundedComplex Γ(S.X, U)
  /-- The complex represents the restriction of `M` to `U`: some complex `E` of `𝒪_X`-modules
  represents `M`, and `E|_U` is isomorphic in `D(𝒪_U)` to the sheaf of modules associated
  with `M^•`. -/
  represents : ∃ E : CochainComplex (OXMod.{u, u} S.X.toRingedSpace) ℤ,
    Nonempty ((@DerivedCategory.Q _ _ _ S.hasDerivedCategory).obj E ≅ S.M) ∧
      letI : HasDerivedCategory.{u + 1} U.1.toScheme.Modules :=
        HasDerivedCategory.standard _
      Nonempty
        (DerivedCategory.Q.obj
          (((Scheme.Modules.restrictFunctor U.1.ι).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj E) ≅
          DerivedCategory.Q.obj
            (((tilde.functor Γ(S.X, U) ⋙
              Scheme.Modules.restrictFunctor U.2.isoSpec.hom).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj complex.toCochainComplex))

namespace AffineChart

variable {S : ComplexAndDivisorSituation.{u, d}}

/-- The determinantal ideal `I_i(M^•, f) ⊂ A` of an affine chart: the ideal generated by the
`rᵢ × rᵢ` minors of `(f, dⁱ) : M^i → M^i ⊕ M^{i+1}`, as in More on Algebra, Section 15.98. -/
abbrev determinantalIdeal (C : AffineChart S) (i : ℤ) : Ideal Γ(S.X, C.U) :=
  idealI C.complex C.f i

/-- `f ^ rᵢ` lies in the determinantal ideal `I_i(M^•, f)`.  This is the observation of More on
Algebra, Section 15.98; it is what makes the product of the determinantal ideals supported on
the divisor, hence a `(U \ D)`-admissible centre. -/
theorem pow_rank_mem_determinantalIdeal (C : AffineChart S) (i : ℤ) :
    C.f ^ C.complex.rank i ∈ C.determinantalIdeal i :=
  pow_rank_mem_idealI C.complex C.f i

/-- The determinantal ideal `I_i(M^•, f)` of an affine chart is finitely generated: it is
spanned by the finitely many `rᵢ × rᵢ` minors of the matrix of `(f, dⁱ)`. -/
theorem determinantalIdeal_fg (C : AffineChart S) (i : ℤ) : (C.determinantalIdeal i).FG :=
  Stacks.DeterminantalIdeal.fg_idealI C.complex C.f i

/-- In a degree where `M^•` vanishes the determinantal ideal of an affine chart is the unit
ideal: for `rᵢ = 0` the only `rᵢ × rᵢ` minor is the determinant of the empty matrix. -/
theorem determinantalIdeal_eq_top (C : AffineChart S) {i : ℤ} (h : C.complex.rank i = 0) :
    C.determinantalIdeal i = ⊤ :=
  Stacks.DeterminantalIdeal.idealI_eq_top_of_rank_eq_zero C.complex C.f h

/-- The **centre of the blowup** of an affine chart in Stacks tag 0GTY: the product
`∏ᵢ I_i(M^•, f)` of the determinantal ideals of the chart.  All but the finitely many degrees in
which `M^•` is nonzero contribute the unit ideal, by
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.determinantalIdeal_eq_top`, so the
product is taken over those degrees. -/
noncomputable def blowupCentre (C : AffineChart S) : Ideal Γ(S.X, C.U) :=
  ∏ i ∈ C.complex.bounded.toFinset, C.determinantalIdeal i

/-- The product of the determinantal ideals over any finite set of degrees containing all those
in which `M^•` is nonzero is the centre: the extra factors are the unit ideal.  This is why the
finite product over the support of `M^•` is the tag's product over all `i ∈ ℤ`. -/
theorem prod_determinantalIdeal_eq_blowupCentre (C : AffineChart S) {s : Finset ℤ}
    (hs : C.complex.bounded.toFinset ⊆ s) :
    (∏ i ∈ s, C.determinantalIdeal i) = C.blowupCentre :=
  (Finset.prod_subset hs fun i _ hi => by
    have hr : C.complex.rank i = 0 := by
      simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hi
    simpa only [Ideal.one_eq_top] using C.determinantalIdeal_eq_top hr).symm

/-- **Stacks tag 0GTY, the centre of the blowup over an affine chart: finite type.**  The
product of the determinantal ideals is finitely generated, being a finite product of finitely
generated ideals.  Finite type of the centre is the condition under which the blowup in it is
proper and, with
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.pow_mem_blowupCentre`, admissible away
from the divisor. -/
@[stacks 0GTY "the centre `∏ᵢ I_i(M^•, f)` of the blowup over an affine chart is of finite \
type; for the blowup in it over an affine chart --- its admissibility, the goodness of the \
pulled-back triple and its universal property --- see `ChartBlowupAdmissible.lean` and \
`ChartBlowupUniversal.lean`, and for the morphism `b : X\' ⟶ X` glued from them see \
`GoodBlowupTag.lean`"]
theorem blowupCentre_fg (C : AffineChart S) : C.blowupCentre.FG := by
  classical
  refine Finset.prod_induction _ _ (fun I J hI hJ => hI.mul hJ) ?_
    fun i _ => C.determinantalIdeal_fg i
  exact ⟨{1}, by simp⟩

/-- **Stacks tag 0GTY, the centre of the blowup over an affine chart: supported on the
divisor.**  The power `f ^ (∑ᵢ rᵢ)` of the equation of `D ∩ U` lies in the product of the
determinantal ideals, since `f ^ rᵢ` lies in the `i`-th factor.  Hence the closed subscheme cut
out by the centre is contained in `D ∩ U`, so the centre is disjoint from `U \ D`: this is the
condition that makes the blowup of the chart in it a `(U \ D)`-admissible blowing up. -/
@[stacks 0GTY "the centre `∏ᵢ I_i(M^•, f)` of the blowup over an affine chart contains a power \
of the equation of the divisor, hence is supported on it; for the blowup in it over an affine \
chart --- its admissibility, the goodness of the pulled-back triple and its universal property \
--- see `ChartBlowupAdmissible.lean` and `ChartBlowupUniversal.lean`, and for the morphism \
`b : X\' ⟶ X` glued from them see `GoodBlowupTag.lean`"]
theorem pow_mem_blowupCentre (C : AffineChart S) :
    C.f ^ (∑ i ∈ C.complex.bounded.toFinset, C.complex.rank i) ∈ C.blowupCentre := by
  classical
  rw [blowupCentre, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => C.pow_rank_mem_determinantalIdeal i

end AffineChart

/-- A triple `(X, D, M)` as in Situation 0F8S is a **good triple** if every point of `D` lies
in an affine chart whose determinantal ideals `I_i(M^•, f)` are principal for every `i ∈ ℤ`. -/
def IsGoodTriple (S : ComplexAndDivisorSituation.{u, d}) : Prop :=
  ∀ x ∈ S.D.supportSet, ∃ C : AffineChart S,
    x ∈ (C.U : Set S.X) ∧ ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal

/-- A triple whose divisor has empty support is a good triple: there is no point at which a
chart has to be produced. -/
theorem isGoodTriple_of_isEmpty_supportSet (S : ComplexAndDivisorSituation.{u, d})
    (h : S.D.supportSet = ∅) : IsGoodTriple S := by
  intro x hx
  rw [h] at hx
  exact absurd hx (Set.notMem_empty x)

/-- The derived pullback `Lh^*M` of the perfect object of a triple along a morphism of schemes,
formed in the standard model of the derived category of `𝒪_Y`-modules.  The object `M` is first
carried from the situation's own model to the standard one by the canonical equivalence of two
localizations at the quasi-isomorphisms. -/
def derivedPullbackObject (S : ComplexAndDivisorSituation.{u, d}) {Y : Scheme.{u}}
    (h : Y ⟶ S.X) : DerivedCategory (OXMod.{u, u} Y.toRingedSpace) :=
  (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      h.toLRSHom.toShHom).obj
    ((Localization.uniq
        (@DerivedCategory.Q _ _ _ S.hasDerivedCategory)
        (@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard
          (OXMod.{u, u} S.X.toRingedSpace)))
        (HomologicalComplex.quasiIso (OXMod.{u, u} S.X.toRingedSpace)
          (ComplexShape.up ℤ))).functor.obj S.M)

/-- The derived pullback of the perfect object of a triple is again perfect.  Perfectness is
carried from the situation's model of the derived category to the standard one by
`AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.isPerfect_uniqFunctor_obj` and is then
preserved by derived pullback. -/
@[sga "6 I 4.19.1" "a), special case", sga "6 IV 2.7" "2.7 a), special case"]
theorem isPerfect_derivedPullbackObject (S : ComplexAndDivisorSituation.{u, d})
    {Y : Scheme.{u}} (h : Y ⟶ S.X) :
    RingedSpace.IsPerfect (X := Y.toRingedSpace) (S.derivedPullbackObject h) :=
  RingedSpace.KFlatDerivedPullback.isPerfect_derivedPullback h.toLRSHom.toShHom _
    (RingedSpace.KFlatDerivedPullback.isPerfect_uniqFunctor_obj
      S.hasDerivedCategory
      (HasDerivedCategory.standard (OXMod.{u, u} S.X.toRingedSpace)) S.M S.isPerfect)

/-- The triple `(Y, h⁻¹D, Lh^*M)` pulled back along a morphism `h : Y ⟶ X` for which the
pullback `h⁻¹D` of the effective Cartier divisor is defined. -/
def pullback (S : ComplexAndDivisorSituation.{u, d}) {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (hD : Stacks.Divisors.IsPullbackDefined h S.D) :
    ComplexAndDivisorSituation.{u, u + 1} where
  X := Y
  D := S.D.comap h
  isEffectiveCartierDivisor := hD
  hasDerivedCategory := HasDerivedCategory.standard (OXMod.{u, u} Y.toRingedSpace)
  M := S.derivedPullbackObject h
  isPerfect := S.isPerfect_derivedPullbackObject h

/-- The scheme of the pulled-back triple is the source `Y` of `h`. -/
@[simp]
theorem pullback_X (S : ComplexAndDivisorSituation.{u, d}) {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (hD : Stacks.Divisors.IsPullbackDefined h S.D) : (S.pullback h hD).X = Y :=
  rfl

/-- The divisor of the pulled-back triple is the pullback `h⁻¹D` of the divisor. -/
@[simp]
theorem pullback_D (S : ComplexAndDivisorSituation.{u, d}) {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (hD : Stacks.Divisors.IsPullbackDefined h S.D) :
    (S.pullback h hD).D = S.D.comap h :=
  rfl

/-- The perfect object of the pulled-back triple is the derived pullback `Lh^*M`. -/
@[simp]
theorem pullback_M (S : ComplexAndDivisorSituation.{u, d}) {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (hD : Stacks.Divisors.IsPullbackDefined h S.D) :
    (S.pullback h hD).M = S.derivedPullbackObject h :=
  rfl

end AlgebraicGeometry.ComplexAndDivisorSituation

end
