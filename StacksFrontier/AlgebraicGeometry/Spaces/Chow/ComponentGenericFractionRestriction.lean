module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ComponentHenselianIdealRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorFunctionFieldChartIndependence

/-!
# A rational function read in the ambient henselian local ring

Let `X` be a decent algebraic space over `S`, let `x` be a point of it and write
`A = 𝒪^h_{X, x}` for the henselian local ring of Stacks 0ENK there. Let `X''` be a decent,
locally Noetherian, integral algebraic space with a prime divisor `Z''` of generic point `ξ''`,
and suppose `ξ''` is presented over `x` as in
`StacksFrontier.AlgebraicGeometry.Spaces.Decent.ClosedImmersionHenselianLocalRingQuotient`: there
are an elementary étale neighborhood `V` of `x`, one `U` of `ξ''`, and `j : U.scheme ⟶ V.scheme`
carrying the distinguished point to the distinguished point with surjective Zariski stalk map
`α`, so that

  `A ⧸ (ker α) · A ≅ 𝒪^h_{X'', ξ''}`.

In the application `X'' ⊆ X` is an irreducible component of `X` with its reduced induced
structure, `U` is the base-change chart `V ×_X X''` and `j` its projection.

This file reads a *rational function* of `X''` through that presentation. The canonical map of
Stacks 0ENK

  `R(X'') ⟶ Q(𝒪^h_{X'', ξ''})`

is defined through the affine chart of Stacks 0BBP chosen by
`AlgebraicGeometry.Space.PrimeDivisor.genericChart`; computed instead on `U`, it carries a
function whose reading there is a fraction `j^♯ s / j^♯ t` of images of global sections of `𝒪_V`
to the fraction of the *classes* of `s` and `t` read in `A`.

That is the only form in which an order of vanishing on `X''` can be compared with one computed
in `A`. There is no induced map `Q(A) ⟶ Q(𝒪^h_{X'', ξ''})` of total rings of fractions to
compare them with, and there cannot be: the quotient map does not carry nonzerodivisors to
nonzerodivisors, a nonzerodivisor of `A` being free to land in a minimal prime of the quotient.
The comparison is elementwise, on numerator and denominator.

## Main results

* `AlgebraicGeometry.Space.isAffine_rep_pullback` and
  `AlgebraicGeometry.Space.isAffine_closedImmersionBaseChangeNeighborhood`: the base-change chart
  `V ×_X X'` of an *affine* chart `V` along a closed immersion is affine, the second stated at
  the `AlgebraicGeometry.Space.closedImmersionBaseChangeNeighborhood` spelling.
* `AlgebraicGeometry.Space.PrimeDivisor.isReduced_closedImmersionBaseChangeNeighborhood` and
  `.isLocallyNoetherian_closedImmersionBaseChangeNeighborhood`: it is also reduced and locally
  Noetherian.
* `PrimeDivisor.rationalFunctionsToGenericTotalFractionRing_eq_mk'_ringEquiv_quotient`:
  **the fraction of the classes.** For global sections `s`, `t` of `𝒪_V` whose images `j^♯ s`,
  `j^♯ t` present the reading of a rational function `r` of `X''` on `U`, the image of `r` under
  the embedding of Stacks 0ENK is `e [σ_V s] / e [σ_V t]`, with `σ_V` the map of Stacks 0EMY from
  the chart stalk into `A`, `[·]` the class modulo `(ker α) · A`, and `e` the isomorphism onto
  `𝒪^h_{X'', ξ''}`.

## Implementation notes

The main result is stated for an arbitrary pair `(U, j)` surjective on stalks rather than for the
base-change chart. That is not only more general: the base-change chart is a structure instance
whose fields are choice terms built from proofs of étaleness, and the elaborator unfolds them
whenever it has to check a definitional equality against one, which made the statement phrased
directly at that chart exceed the heartbeat limit. Keeping `U` and `j` opaque is what keeps the
statement cheap. The ideal is the same term either way, so nothing is lost by instantiating
afterwards.

## References

* [Stacks Project, Tag 0BBP](https://stacks.math.columbia.edu/tag/0BBP)
* [Stacks Project, Tag 0BGV](https://stacks.math.columbia.edu/tag/0BGV)
* [Stacks Project, Tag 0EMY](https://stacks.math.columbia.edu/tag/0EMY)
* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0EQA](https://stacks.math.columbia.edu/tag/0EQA)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hXd : IsDecentSpace B S hS X) {x : points B S hS X}
    (V : ElementaryEtaleNeighborhood B S hS X hX x)
    {X' : Subfunctor X} (hX' : IsClosedSubspace B S hS X')
    (hX'int : IsIntegralSpace B S hS X'.toFunctor)
    (hX'N : HasEtaleLocalProperty B S hS X'.toFunctor
      (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (Z' : PrimeDivisor B S hS X'.toFunctor)
    (w : (hX'.2.rep.pullback V.toSpace).left.1)
    (hw : pointsMap B S hS (yoneda.obj (hX'.2.rep.pullback V.toSpace))
      (hX'.2.rep.fst V.toSpace)
      (presheafPoint B S hS (hX'.2.rep.pullback V.toSpace) w
        (B.residueField_spec_contains (hX'.2.rep.pullback V.toSpace).left.property w)) =
      Z'.genericPoint B S hS X'.toFunctor)
    (hpw : (hX'.2.rep.snd V.toSpace).left.1 w = V.point)

/-! ### The base-change chart of an affine chart is affine, reduced and locally Noetherian -/

/-- The base change `V ×_X X'` of an *affine* elementary étale neighborhood along a closed
immersion is affine. -/
theorem isAffine_rep_pullback [IsAffine V.scheme.left.1] :
    IsAffine (hX'.2.rep.pullback V.toSpace).left.1 := by
  have hpci : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hX'.2.rep.snd V.toSpace)) :=
    hX'.2.property_snd V.toSpace
  have : AlgebraicGeometry.IsClosedImmersion (hX'.2.rep.snd V.toSpace).left.1 := hpci
  exact isAffine_of_isAffineHom (hX'.2.rep.snd V.toSpace).left.1

/-- `AlgebraicGeometry.Space.isAffine_rep_pullback` restated at the
`AlgebraicGeometry.Space.closedImmersionBaseChangeNeighborhood` spelling of the same scheme.
The two are definitionally equal, but that definition is not reducible, so instance search does
not pass between them. -/
theorem isAffine_closedImmersionBaseChangeNeighborhood [IsAffine V.scheme.left.1] :
    IsAffine
      (closedImmersionBaseChangeNeighborhood B S hS hX'.1 hX'.2 V w hw hpw).scheme.left.1 :=
  isAffine_rep_pullback B S hS hX V hX'

include hX'int in
/-- The base-change chart `V ×_X X'`, as an elementary étale neighborhood of the generic point of
a prime divisor of an integral space `X'`, is reduced. -/
theorem PrimeDivisor.isReduced_closedImmersionBaseChangeNeighborhood :
    IsReduced
      (closedImmersionBaseChangeNeighborhood B S hS hX'.1 hX'.2 V w hw hpw).scheme.left.1 :=
  Z'.isReduced_chart B S hS hX'.1 hX'int
    (closedImmersionBaseChangeNeighborhood B S hS hX'.1 hX'.2 V w hw hpw)

include hX'N in
/-- The base-change chart `V ×_X X'`, as an elementary étale neighborhood of the generic point of
a prime divisor of a locally Noetherian space `X'`, is locally Noetherian. -/
theorem PrimeDivisor.isLocallyNoetherian_closedImmersionBaseChangeNeighborhood :
    IsLocallyNoetherian
      (closedImmersionBaseChangeNeighborhood B S hS hX'.1 hX'.2 V w hw hpw).scheme.left.1 :=
  Z'.isLocallyNoetherian_chart B S hS hX'.1 hX'N
    (closedImmersionBaseChangeNeighborhood B S hS hX'.1 hX'.2 V w hw hpw)


/-! ### The image of a rational function as the fraction of two classes -/

section Fraction

variable {X'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX'' : IsAlgebraicSpace B S hS X'')
    (hX''d : IsDecentSpace B S hS X'')
    (hX''int : IsIntegralSpace B S hS X'')
    (hX''N : HasEtaleLocalProperty B S hS X'' (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (Z'' : PrimeDivisor B S hS X'')

include hX hXd hX''int hX''N in
/-- **The image of a rational function under the embedding of Stacks 0ENK is the fraction of the
classes of a numerator and a denominator read in the ambient henselian local ring.** Let `V` be
an elementary étale neighborhood of a point `x` of `X`, let `X''` be a decent, locally
Noetherian, integral algebraic space with a prime divisor `Z''` of generic point `ξ''`, let `U`
be an *affine* elementary étale neighborhood of `ξ''` and let `j : U.scheme ⟶ V.scheme` carry the
distinguished point to the distinguished point with surjective Zariski stalk map. Let `s`, `t` be
global sections of `𝒪_V` with `j^♯ t` a nonzerodivisor, and suppose the reading of a rational
function `r` of `X''` in `Q(Γ(U, 𝒪_U))` is the fraction `j^♯ s / j^♯ t`. Then

  `emb_{X''}(r) = e [σ_V s] / e [σ_V t]`   in `Q(𝒪^h_{X'', ξ''})`,

where `σ_V : 𝒪_{V, V.point} ⟶ 𝒪^h_{X, x}` is the map of Stacks 0EMY, `[·]` is the class modulo
the ideal `(ker α) · 𝒪^h_{X, x}` generated by the kernel of the stalk map of `j`, and
`e : 𝒪^h_{X, x} ⧸ (ker α) · 𝒪^h_{X, x} ≅ 𝒪^h_{X'', ξ''}` is the presentation of
`exists_ringEquiv_henselianLocalRing_quotient_sectionsToHenselianLocalRing`. -/
theorem PrimeDivisor.rationalFunctionsToGenericTotalFractionRing_eq_mk'_ringEquiv_quotient
    (U : ElementaryEtaleNeighborhood B S hS X'' hX'' (Z''.genericPoint B S hS X''))
    [IsAffine U.scheme.left.1] (j : U.scheme ⟶ V.scheme) (hj : j.left.1 U.point = V.point)
    (hsurj : Function.Surjective ((V.scheme.left.1.presheaf.stalkCongr (.of_eq hj.symm)).hom ≫
      j.left.1.stalkMap U.point).hom)
    (s t : Γ(V.scheme.left.1, ⊤))
    (ht : (j.left.1.appTop).hom t ∈ (Γ(U.scheme.left.1, ⊤))⁰)
    (r : rationalFunctions B S hS hX'')
    (hr : letI := Z''.isReduced_chart B S hS hX'' hX''int U
      letI := Z''.isLocallyNoetherian_chart B S hS hX'' hX''N U
      rationalFunctionsToTotalFractionRing B S hS hX'' U.scheme U.toSpace U.etale_toSpace r =
        IsLocalization.mk' (FractionRing Γ(U.scheme.left.1, ⊤)) ((j.left.1.appTop).hom s)
          ⟨(j.left.1.appTop).hom t, ht⟩) :
    ∃ (e : ((henselianLocalRing B S hS X hX x hXd : Type (u + 1)) ⧸
          (RingHom.ker ((V.scheme.left.1.presheaf.stalkCongr (.of_eq hj.symm)).hom ≫
            j.left.1.stalkMap U.point).hom).map
            (stalkToHenselianLocalRing B S hS X hX x hXd V)) ≃+*
        ↥(Z''.genericHenselianLocalRing B S hS hX'' hX''int.isDecentSpace))
        (hb : e (Ideal.Quotient.mk _ (stalkToHenselianLocalRing B S hS X hX x hXd V
            ((V.scheme.left.1.presheaf.germ ⊤ V.point trivial).hom t))) ∈
          (↥(Z''.genericHenselianLocalRing B S hS hX'' hX''int.isDecentSpace))⁰),
      Z''.rationalFunctionsToGenericTotalFractionRing B S hS hX'' hX''int.isDecentSpace hX''int
          hX''N r =
        IsLocalization.mk' (Z''.genericTotalFractionRing B S hS hX'' hX''int.isDecentSpace)
          (e (Ideal.Quotient.mk _ (stalkToHenselianLocalRing B S hS X hX x hXd V
            ((V.scheme.left.1.presheaf.germ ⊤ V.point trivial).hom s))))
          ⟨_, hb⟩ := by
  let := Z''.isReduced_chart B S hS hX'' hX''int U
  let := Z''.isLocallyNoetherian_chart B S hS hX'' hX''N U
  let : IsLocalRing ↥(Z''.genericHenselianLocalRing B S hS hX'' hX''int.isDecentSpace) :=
    henselianLocalRing_isLocalRing B S hS X'' hX'' (Z''.genericPoint B S hS X'')
      hX''int.isDecentSpace
  have hCof : IsCofiltered
      (ElementaryEtaleNeighborhood B S hS X'' hX'' (Z''.genericPoint B S hS X'')) :=
    ElementaryEtaleNeighborhood.isCofiltered_of_nonempty B S hS X'' hX''
      (Z''.genericPoint B S hS X'') ⟨U⟩
  obtain ⟨e, he⟩ := exists_ringEquiv_henselianLocalRing_quotient_sectionsToHenselianLocalRing
    B S hS hX hXd x V hX'' hX''int.isDecentSpace U j hj hsurj
  have hval : ∀ a : Γ(V.scheme.left.1, ⊤),
      e (Ideal.Quotient.mk _ (stalkToHenselianLocalRing B S hS X hX x hXd V
          ((V.scheme.left.1.presheaf.germ ⊤ V.point trivial).hom a))) =
        Z''.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX''
          hX''int.isDecentSpace U ((j.left.1.appTop).hom a) := fun a => he a
  have hnz : Z''.neighborhoodSectionsToGenericHenselianLocalRing B S hS hX''
      hX''int.isDecentSpace U ((j.left.1.appTop).hom t) ∈
      (↥(Z''.genericHenselianLocalRing B S hS hX'' hX''int.isDecentSpace))⁰ :=
    Z''.nonZeroDivisors_le_comap_neighborhoodSectionsToGenericHenselianLocalRing B S hS hX''
      hX''int.isDecentSpace U hCof ht
  refine ⟨e, (hval t).symm ▸ hnz, ?_⟩
  rw [← Z''.neighborhoodTotalFractionRingToGeneric_pullback_eq B S hS hX''
    hX''int.isDecentSpace hX''int hX''N U hCof r, hr,
    PrimeDivisor.neighborhoodTotalFractionRingToGeneric, IsLocalization.map_mk', hval s]
  exact congrArg _ (Subtype.ext (hval t).symm)

end Fraction

end AlgebraicGeometry.Space

end
