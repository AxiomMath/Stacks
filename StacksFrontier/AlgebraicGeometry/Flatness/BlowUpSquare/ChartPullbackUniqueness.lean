module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexCoverCriterion
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartHomologyFreeness
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPullbackRepresents
public import StacksFrontier.Homology.Eta.Perfect.DeterminantalIdealPrincipal

/-!
# Any chart of a pulled-back triple agrees with the pulled-back chart

Let `(X, D, M)` be a triple as in Situation 0F8S, let `h : Y ⟶ X` be a morphism of schemes for
which the pullback `E = h⁻¹D` is defined, let `(U, A, f, M^•)` be an affine chart for `(X, D, M)`,
and let `V = Spec B ⊆ Y` be an affine open with `h(V) ⊆ U`.  By part (1) of Stacks tag 0F8T the
base change `M^• ⊗_A B` represents `Lh^*M|_V`; so does the bounded complex `N^•` of any other
affine chart of `(Y, E, Lh^*M)` whose open is `V`, and derived sheafification on `V` is fully
faithful, so the two are isomorphic in `D(B)`.

This is the input that Stacks tag 0GTY's universal property asks of tag 0F8T: given a chart
`(V, B, g, N^•)` of the pulled-back triple, `N^•` and `M^• ⊗_A B` are isomorphic in `D(B)`, which
is what lets Stacks tag 0GSS transfer principality of the determinantal ideals between them.

## Main results

* `ComplexAndDivisorSituation.AffineChart.nonempty_derivedIso_pullback`:
  the two bounded complexes are isomorphic in `D(B)`.
* `ComplexAndDivisorSituation.AffineChart.isPrincipal_determinantalIdeal_of_eq_appLE`:
  hence the determinantal ideals of any chart of the pulled-back triple over `V` whose equation is
  the image of `f` are principal as soon as those of `(U, A, f, M^•)` are.

## Implementation notes

`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.representsDerivedIso` reads the
`represents` field of a chart as an isomorphism whose source is the restriction of the
situation's own object `M` to the chart, so the two charts' isomorphisms have the *same* source
once their opens agree, and
`Stacks.Duality.nonempty_iso_of_nonempty_iso_tilde` applies directly.  A triple carries its
derived category of `𝒪_X`-modules at the `OXMod` spelling while these functors are stated for
`Scheme.Modules`; `modulesHasDerivedCategory` is the laundering, made a local instance of high
priority, exactly as in `ChartPrincipalityTransfer.lean`.

## References

* [Stacks Project, Tag 0F8T](https://stacks.math.columbia.edu/tag/0F8T)
* [Stacks Project, Tag 0GTY](https://stacks.math.columbia.edu/tag/0GTY)
* [Stacks Project, Tag 0GSS](https://stacks.math.columbia.edu/tag/0GSS)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect

attribute [local instance 10000] HasDerivedCategory.standard

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 100000] modulesHasDerivedCategory

namespace AffineChart

variable {S : ComplexAndDivisorSituation.{u, d}}

/-- **Any chart of the pulled-back triple over `V` has the same bounded complex as the
pulled-back chart, up to isomorphism in `D(B)`.**  Both complexes represent `Lh^*M|_V`, the
first by part (1) of Stacks tag 0F8T and the second by being a chart, and derived sheafification
on an affine open is fully faithful. -/
theorem nonempty_derivedIso_pullback (C : AffineChart S) {Y : Scheme.{u}} (h : Y ⟶ S.X)
    (hD : Stacks.Divisors.IsPullbackDefined h S.D) (C' : AffineChart (S.pullback h hD))
    (hV : ((C'.U : (S.pullback h hD).X.Opens) : Y.Opens) ≤ h ⁻¹ᵁ (C.U : S.X.Opens)) :
    Nonempty (DerivedCategory.Q.obj
        (C.pullback h hD C'.U hV).complex.toCochainComplex ≅
      DerivedCategory.Q.obj C'.complex.toCochainComplex) :=
  Stacks.Duality.nonempty_iso_of_nonempty_iso_tilde C'.U.2
    (representsDerivedIso (C.pullback h hD C'.U hV)) (representsDerivedIso C')

/-- **Principality of the determinantal ideals passes to any chart of the pulled-back triple.**
If the determinantal ideal `I_i(M^•, f)` of the chart `(U, A, f, M^•)` is principal and
`(V, B, g, N^•)` is a chart of `(Y, h⁻¹D, Lh^*M)` whose open lies over `U` and whose equation is
the image of `f`, then `I_i(N^•, g)` is principal.

The base change `M^• ⊗_A B` has principal determinantal ideals by part (2) of the tag, it is
isomorphic to `N^•` in `D(B)` by
`AlgebraicGeometry.ComplexAndDivisorSituation.AffineChart.nonempty_derivedIso_pullback`, and
Stacks tag 0GSS transports principality across such an isomorphism. -/
theorem isPrincipal_determinantalIdeal_of_eq_appLE (C : AffineChart S) {Y : Scheme.{u}}
    (h : Y ⟶ S.X) (hD : Stacks.Divisors.IsPullbackDefined h S.D)
    (C' : AffineChart (S.pullback h hD))
    (hV : ((C'.U : (S.pullback h hD).X.Opens) : Y.Opens) ≤ h ⁻¹ᵁ (C.U : S.X.Opens))
    (hf : C'.f = (C.pullback h hD C'.U hV).f) (i : ℤ)
    (hp : (C.determinantalIdeal i).IsPrincipal) :
    (C'.determinantalIdeal i).IsPrincipal := by
  show (idealI C'.complex C'.f i).IsPrincipal
  rw [hf]
  exact Stacks.Eta.DeterminantalIdeal.isPrincipal_idealI_of_derived_iso
    (C.pullback h hD C'.U hV).f
    (by rw [← hf]; exact C'.regular.mem_nonZeroDivisors) _ C'.complex i
    (C.nonempty_derivedIso_pullback h hD C' hV)
    (C.isPrincipal_pullback_determinantalIdeal h hD C'.U hV hp)

end AffineChart

end AlgebraicGeometry.ComplexAndDivisorSituation

end
