module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedSupportEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationFromATriangle

/-!
# The induction on the cohomological amplitude in the proof of Stacks 08HN

Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished square of algebraic spaces over a
scheme `S` with `U` quasi-compact, `V` affine and `U ×_X V` quasi-compact.  Stacks 08HN says
that approximation by perfect complexes passes from `U` to `X`.  Its proof fixes a closed
`T ⊆ |X|` with quasi-compact open complement, produces two integers `r_U` and `r'` and runs
with an integer `r` built from them; the approximation of a triple `(T, E, m)` is then obtained
by an induction on

> `t`, the largest degree in which `Hᵗ(E)|_U` is nonzero,

whose base case `t ≤ m - r'` is Stacks 08HM on `V` followed by Stacks 08HL, and whose step
produces a perfect `R` supported on `T` mapping to `E` and surjective on `Hᵗ` over `U`, fits it
into a distinguished triangle `R ⟶ E ⟶ E' ⟶ R[1]`, and applies the inductive hypothesis to `E'`.

That induction is what this file carries out, as a statement about one space and two subsets of
its points, with the base case and the step as hypotheses.  The closing move — passing an
approximation of `E'` back to one of `E` across the triangle — is
`AlgebraicGeometry.Space.approximationHolds_of_distinguished`, so nothing of the diagram chase
is repeated here.

## Main definitions

* `AlgebraicGeometry.Space.CohomologySupportedOnFrom` is the degreewise support condition
  `Hⁱ(E) ⊆ T` for `i ≥ n`.  It is the shape in which the conditions of Stacks 08HJ, of
  Stacks 08HL and of Stacks 08HM are all stated, each of those having written it out inline,
  and it is what the amplitude of the induction is measured by here: `Hⁱ(E)|_U = 0` for `i > t`
  is `Hⁱ(E)` supported on `|X| ∖ |U|` for `i ≥ t + 1`.
* `AlgebraicGeometry.Space.ApproximationInput` is the class of objects the integer of
  Stacks 08HJ quantifies over at a subset and a degree.
* `AlgebraicGeometry.Space.AmplitudeInductionInputs` collects the inputs of the induction at a
  space and a subset of its points: the support hypothesis of the closing move, and, for each
  closed subset with quasi-compact open complement, the two integers, the base case, the step
  and the existence of an amplitude.

## Main results

* `AlgebraicGeometry.Space.isZero_etaleModulePullback_iff_disjoint_supportOfSheaf`: the
  restriction of a module along an étale morphism vanishes exactly when its support misses the
  image of the points.  This is what identifies the amplitude condition used here with the
  source's "`Hⁱ(E)|_U = 0`"; it is proved from the unconditional
  `AlgebraicGeometry.Space.supportOfSheaf_toSheaf_etaleModulePullback` and Stacks 04K5.
* `AlgebraicGeometry.Space.cohomologySupportedOnFrom_compl_range_of_isZero`: the same
  identification in the form the induction consumes.
* `AlgebraicGeometry.Space.approximationHolds_of_amplitudeInduction`: **the induction of
  Stacks 08HN**, from its base case and its step.
* `AlgebraicGeometry.Space.approximationByPerfectComplexes_of_amplitudeInduction`: the
  conclusion of Stacks 08HN — approximation by perfect complexes in the sense of Stacks 08HJ —
  from `AlgebraicGeometry.Space.AmplitudeInductionInputs`.  This is what
  `AlgebraicGeometry.Space.approximationByPerfectComplexes_of_induction_of_amplitudeInputs`
  feeds to the induction principle of Stacks 08GP in place of its hypothesis `hstep`, which was
  the conclusion of Stacks 08HN verbatim.

## Where Stacks 08HN is registered

This file carries out the induction in the abstract, with its base case, its step and the
existence of an amplitude as hypotheses (the fields of
`AlgebraicGeometry.Space.AmplitudeInductionInputs`); it attaches no `stacks` attribute.  Those
inputs are supplied, and Stacks 08HN is registered, in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ApproximationSquare.lean`
(`AlgebraicGeometry.Space.approximationByPerfectComplexes_of_isElementaryDistinguishedSquare`):

* the base case is Stacks 08EQ on the affine member followed by Stacks 08HL
  (`AlgebraicGeometry.Space.exists_approximation_edsEtale`,
  `AlgebraicGeometry.Space.approximationHolds_of_approximationHolds_edsEtale`);
* the step is Stacks 08EK and Stacks 08EH on the open immersion `U ×_X V ⊆ V`, carried across
  the comparison of Stacks 071Q, followed by Stacks 08HB
  (`AlgebraicGeometry.Space.exists_approximation_step`);
* the amplitude is `AlgebraicGeometry.Space.exists_cohomologySupportedOnFrom_compl_range`;
* `mid` is `AlgebraicGeometry.Space.cohomologySupportedOn_obj₂_of_distinguished`.

The integer is `r = r_U + r'` rather than the source's `max(r_U, r')`: the step approximates
`E|_U` at the degree `t` of the induction, where the source writes `m`, and that needs
`E|_U` to be `(t - r_U)`-pseudo-coherent.

## Implementation notes

*The induction variable.*  The source names `t` as the largest degree in which `Hᵗ(E)|_U` is
nonzero and notes that such a `t` exists because `U` is quasi-compact and `E|_U` is
`(m - r)`-pseudo-coherent.  Only an upper bound is used, so the statement below takes `t` with
`Hⁱ(E)|_U = 0` for `i > t` and makes no existence claim; the existence of some such `t` is the
third clause of `AlgebraicGeometry.Space.AmplitudeInductionInputs`, and it is the boundedness of
the cohomology of a pseudo-coherent complex on a quasi-compact space.

That third clause is proved as
`AlgebraicGeometry.Space.exists_cohomologySupportedOnFrom_compl_range`
(`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ApproximationAmplitudeBound.lean`): a
quasi-compact `U` has a surjective étale chart `h_{U₀} ⟶ U` with `U₀` quasi-compact
(Stacks 03E3), the restriction of `E` to it is `ε^*E₀` for a pseudo-coherent `E₀` on `U₀`
(Stacks 071Q and 08HE), and the cohomology of `E₀` vanishes in large degrees because `U₀` is
quasi-compact.

*The recursion.*  The induction runs on `(t - c).toNat` for `c` the cut-off `m - r'` of the
source's base case, which is a `Nat` and makes the recursion structural.  Below the cut-off the
base case applies directly, by monotonicity of the support condition in its degree; above it the
step is taken and the inductive hypothesis is applied at `t - 1`.

*What the class of objects being approximated is.*  The conditions the source imposes on `E` —
quasi-coherence of its cohomology, `(m - r)`-pseudo-coherence, and support on `T` from degree
`m - r` on — are collected into an arbitrary predicate `Good` on
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory`, because the induction uses nothing about
them beyond their being preserved by the step: `E'` is `(m - r)`-pseudo-coherent by Stacks 08FV
and supported on `T` from degree `m - r` on, and both are part of the step's conclusion.
Keeping them opaque is what makes this statement free of the pseudo-coherence hypotheses, which
appear nowhere in the induction itself.

*Two subsets of the points.*  `T` is the closed subset of the triple and `Tout` is the set the
amplitude is measured against — the complement of `|U|` in Stacks 08HN.  Neither is asked to be
closed: that is the convention of `AlgebraicGeometry.Space.ApproximationHolds` and of
`AlgebraicGeometry.Space.CohomologySupportedOn`, and closedness is used nowhere here.

*The one carried hypothesis of the closing move.*  `hmid` — that cohomological support on `T` is
inherited by the second vertex of a distinguished triangle from the other two — is the hypothesis
of `AlgebraicGeometry.Space.approximationHolds_of_distinguished` and is passed straight through;
the docstring of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ApproximationFromATriangle.lean` says what it is
and what the universe gap in the way of proving it is.

*Universes.*  The module sections are at the universe of the schemes throughout, as in
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ApproximationFromATriangle.lean`: at that universe
every sheafification and local-bijectivity hypothesis that
`AlgebraicGeometry.Space.ApproximationHolds`, `AlgebraicGeometry.Space.CohomologySupportedOn` and
`AlgebraicGeometry.RingedSite.IsPerfect` ask of the small étale site and of its slices is an
instance, by `AlgebraicGeometry.Space.RingedSite`, so none appears as a binder.  Stating
`AlgebraicGeometry.Space.CohomologySupportedOnFrom` at a free module universe instead, as
`AlgebraicGeometry.Space.CohomologySupportedOn` is stated, does not elaborate here: the import
closure of this file resolves `Abelian (AlgebraicGeometry.Space.Modules)` at a different
universe from the one the free-universe statement needs, and the resulting universe constraint
has no solution.

## References

* [Stacks Project, Tag 08HN](https://stacks.math.columbia.edu/tag/08HN)
* [Stacks Project, Tag 08HP](https://stacks.math.columbia.edu/tag/08HP)
* [Stacks Project, Tag 08HI](https://stacks.math.columbia.edu/tag/08HI)
* [Stacks Project, Tag 08HJ](https://stacks.math.columbia.edu/tag/08HJ)
* [Stacks Project, Tag 08HL](https://stacks.math.columbia.edu/tag/08HL)
* [Stacks Project, Tag 08HM](https://stacks.math.columbia.edu/tag/08HM)
* [Stacks Project, Tag 08GF](https://stacks.math.columbia.edu/tag/08GF)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

section SupportedFrom

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- An object `E` of `D(𝒪_F)` has its cohomology *supported on `T` from degree `n` on* when
`Hⁱ(E)` is supported on `T` for every `i ≥ n`.

This is the degreewise support condition of Stacks 08HJ, of Stacks 08HL and of Stacks 08HM,
each of which writes it out inline; `AlgebraicGeometry.Space.CohomologySupportedOn` of
Stacks 08GF is the case of no restriction on the degree. -/
abbrev CohomologySupportedOnFrom (T : Set (points B S hS F)) (n : ℤ)
    (E : DerivedCategory (Modules.{u, u} B S hS F hF)) : Prop :=
  ∀ i : ℤ, n ≤ i →
    supportOfSheaf B S hS F
      ((SheafOfModules.toSheaf
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS F hF) i).obj E)) ⊆ T

variable {B S hS F hF}

/-- The degreewise support condition is monotone in the subset. -/
theorem CohomologySupportedOnFrom.mono_set {T T' : Set (points B S hS F)} {n : ℤ}
    {E : DerivedCategory (Modules.{u, u} B S hS F hF)}
    (hE : CohomologySupportedOnFrom B S hS F hF T n E) (hT : T ⊆ T') :
    CohomologySupportedOnFrom B S hS F hF T' n E :=
  fun i hi ↦ (hE i hi).trans hT

/-- The degreewise support condition is monotone in the degree it starts from: asking it from a
later degree on is asking for less. -/
theorem CohomologySupportedOnFrom.mono_degree {T : Set (points B S hS F)} {n n' : ℤ}
    {E : DerivedCategory (Modules.{u, u} B S hS F hF)}
    (hE : CohomologySupportedOnFrom B S hS F hF T n E) (hn : n ≤ n') :
    CohomologySupportedOnFrom B S hS F hF T n' E :=
  fun i hi ↦ hE i (hn.trans hi)

/-- Two degreewise support conditions from the same degree on combine to one on the
intersection. -/
theorem CohomologySupportedOnFrom.inter {T T' : Set (points B S hS F)} {n : ℤ}
    {E : DerivedCategory (Modules.{u, u} B S hS F hF)}
    (hE : CohomologySupportedOnFrom B S hS F hF T n E)
    (hE' : CohomologySupportedOnFrom B S hS F hF T' n E) :
    CohomologySupportedOnFrom B S hS F hF (T ∩ T') n E :=
  fun i hi ↦ Set.subset_inter (hE i hi) (hE' i hi)

/-- An object supported on `T` in the sense of Stacks 08GF is supported on `T` from every
degree on. -/
theorem CohomologySupportedOn.cohomologySupportedOnFrom {T : Set (points B S hS F)}
    {E : DerivedCategory (Modules.{u, u} B S hS F hF)}
    (hE : CohomologySupportedOn B S hS F hF T E) (n : ℤ) :
    CohomologySupportedOnFrom B S hS F hF T n E :=
  fun i _ ↦ hE i

end SupportedFrom

section Restriction

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The vanishing of the restriction of the cohomology sheaves, read as a support
condition.**  If `Hⁱ(E)|_Y = 0` for every `i ≥ n` then `Hⁱ(E)` is supported on the complement of
the image of `|Y|` for every `i ≥ n`.

This is the identification of the amplitude condition of the induction of Stacks 08HN — stated
there as `Hⁱ(E)|_U = 0` for `i > t` — with the degreewise support condition
`AlgebraicGeometry.Space.CohomologySupportedOnFrom` used below. -/
theorem cohomologySupportedOnFrom_compl_range_of_isZero
    {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X) (hg : IsEtale B S hS g.hom) (n : ℤ)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hzero : ∀ i : ℤ, n ≤ i → IsZero ((etaleModulePullback.{u, u} B S hS g hg).obj
      ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E))) :
    CohomologySupportedOnFrom B S hS X.1 X.2
      (Set.range (pointsMap B S hS Y.1 g.hom))ᶜ n E := fun i hi ↦
  Set.subset_compl_iff_disjoint_right.2
    ((isZero_etaleModulePullback_iff_disjoint_supportOfSheaf B S hS g hg _).1 (hzero i hi))

end Restriction

section Induction

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The induction on the cohomological amplitude in the proof of Stacks 08HN.**  Let `T` and
`Tout` be subsets of `|F|`, let `m` and `c` be integers and let `Good` be a predicate on
`D_QCoh(𝒪_F)`.  Suppose that

1. approximation holds for `(T, E, m)` whenever `Good E` and `Hⁱ(E)` is supported on `Tout` for
   `i > c` — the base case; and
2. for `t > c`, every `E` with `Good E` whose `Hⁱ(E)` is supported on `Tout` for `i > t` fits
   into a distinguished triangle `R ⟶ E ⟶ E' ⟶ R[1]` with `R` perfect and supported on `T`, with
   `Good E'`, and with `Hⁱ(E')` supported on `Tout` for `i ≥ t` — the step.

Then approximation holds for `(T, E, m)` for every `E` with `Good E` whose `Hⁱ(E)` is supported
on `Tout` for `i > t`, whatever the integer `t`.

In Stacks 08HN, `Tout` is `|X| ∖ |U|`, so the amplitude condition is the source's
`Hⁱ(E)|_U = 0` for `i > t` — see
`AlgebraicGeometry.Space.cohomologySupportedOnFrom_compl_range_of_isZero` — and `c` is `m - r'`;
the base case is approximation on the affine member of the square followed by Stacks 08HL, and
the step is Stacks 08EK and Stacks 08EH on the open immersion `U ×_X V ⊆ V` followed by
Stacks 08HB; the module docstring says where each is proved.

The recursion is on `(t - c).toNat`, and its closing move is
`AlgebraicGeometry.Space.approximationHolds_of_distinguished`, whose hypothesis `hmid` is
passed through. -/
theorem approximationHolds_of_amplitudeInduction
    (T Tout : Set (points B S hS F)) (m c : ℤ)
    (Good : QuasicoherentDerivedCategory.{u, u} B S hS F hF → Prop)
    (hbase : ∀ E : QuasicoherentDerivedCategory.{u, u} B S hS F hF, Good E →
      CohomologySupportedOnFrom B S hS F hF Tout (c + 1) E.obj →
        ApproximationHolds B S hS F hF T E m)
    (hstep : ∀ (t : ℤ) (E : QuasicoherentDerivedCategory.{u, u} B S hS F hF), c < t → Good E →
      CohomologySupportedOnFrom B S hS F hF Tout (t + 1) E.obj →
        ∃ (Tri : Triangle (DerivedCategory (Modules.{u, u} B S hS F hF)))
          (E' : QuasicoherentDerivedCategory.{u, u} B S hS F hF),
          Tri ∈ distTriang (DerivedCategory (Modules.{u, u} B S hS F hF)) ∧
            (smallEtaleRingedSite B S hS F hF).IsPerfect Tri.obj₁ ∧
            CohomologySupportedOn B S hS F hF T Tri.obj₁ ∧
            E.obj = Tri.obj₂ ∧ E'.obj = Tri.obj₃ ∧ Good E' ∧
            CohomologySupportedOnFrom B S hS F hF Tout t E'.obj)
    (hmid : ∀ Tri' : Triangle (DerivedCategory (Modules.{u, u} B S hS F hF)),
      Tri' ∈ distTriang (DerivedCategory (Modules.{u, u} B S hS F hF)) →
        CohomologySupportedOn B S hS F hF T Tri'.obj₁ →
        CohomologySupportedOn B S hS F hF T Tri'.obj₃ →
          CohomologySupportedOn B S hS F hF T Tri'.obj₂)
    (t : ℤ) (E : QuasicoherentDerivedCategory.{u, u} B S hS F hF) (hGood : Good E)
    (hamp : CohomologySupportedOnFrom B S hS F hF Tout (t + 1) E.obj) :
    ApproximationHolds B S hS F hF T E m := by
  suffices H : ∀ k : ℕ, ∀ (t : ℤ) (E : QuasicoherentDerivedCategory.{u, u} B S hS F hF),
      (t - c).toNat = k → Good E →
        CohomologySupportedOnFrom B S hS F hF Tout (t + 1) E.obj →
          ApproximationHolds B S hS F hF T E m from
    H _ t E rfl hGood hamp
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro t E hk hGood hamp
      rcases le_or_gt t c with hle | hlt
      · exact hbase E hGood (hamp.mono_degree (by omega))
      · obtain ⟨Tri, E', hTri, hperf, hsupp, hE, hE', hGood', hamp'⟩ := hstep t E hlt hGood hamp
        exact approximationHolds_of_distinguished B S hS F hF T m Tri hTri hperf hsupp E hE E'
          hE' (ih _ (by omega) (t - 1) E' rfl hGood' (hamp'.mono_degree (by omega))) hmid

/-- The objects the integer `r` of Stacks 08HJ quantifies over at a subset `T` and a degree `m`:
those `E` of `D_QCoh(𝒪_F)` which are `(m - r)`-pseudo-coherent and whose `Hⁱ(E)` is supported on
`T` from degree `m - r` on.

These are the two conditions the induction of Stacks 08HN carries along and uses nothing of; the
step of that induction has to reproduce them for the third vertex of its triangle, which is
Stacks 08FV for the first and the support condition of the triangle for the second. -/
abbrev ApproximationInput (T : Set (points B S hS F)) (r m : ℤ)
    (E : QuasicoherentDerivedCategory.{u, u} B S hS F hF) : Prop :=
  (smallEtaleRingedSite B S hS F hF).IsPseudoCoherentFrom E.obj (m - r) ∧
    CohomologySupportedOnFrom B S hS F hF T (m - r) E.obj

/-- **The inputs of the induction of Stacks 08HN at a space `F` and a subset `Tout ⊆ |F|.**  They
are: the support hypothesis `mid` of the closing move, and, for every closed `T ⊆ |F|` whose open
complement has quasi-compact inclusion, integers `r` and `r'` such that, among the objects that
are `(m - r)`-pseudo-coherent and supported on `T` from degree `m - r` on,

1. approximation holds for `(T, E, m)` as soon as `Hⁱ(E)` is supported on `Tout` for `i > m - r'`;
2. above that cut-off the step of Stacks 08HN is available: `E` fits into a distinguished triangle
   `R ⟶ E ⟶ E' ⟶ R[1]` with `R` perfect and supported on `T`, with `E'` again in the class, and
   with the amplitude of `E'` over `Tout` one lower; and
3. every object of the class has *some* amplitude over `Tout`.

In Stacks 08HN, `F` is the ambient space `X` of an elementary distinguished square
`(U ⊆ X, j : V ⟶ X)` with `U` quasi-compact, `V` affine and `U ×_X V` quasi-compact, `Tout` is
`|X| ∖ |U|`, `r` is `r_U + r'` for `r_U` the integer Stacks 08HJ supplies on `U` and `r'` the
integer of the base case on `V`, clause (1) is approximation on `V` followed by Stacks 08HL,
clause (2) is Stacks 08EK and Stacks 08EH on the open immersion `U ×_X V ⊆ V` followed by
Stacks 08HB, and clause (3) is the boundedness above of the cohomology of a pseudo-coherent
complex on the quasi-compact `U`; see
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/ApproximationSquare.lean`. -/
structure AmplitudeInductionInputs (Tout : Set (points B S hS F)) : Prop where
  /-- Cohomological support on a subset is inherited by the second vertex of a distinguished
  triangle from the other two.  This is the hypothesis `hmid` of
  `AlgebraicGeometry.Space.approximationHolds_of_distinguished`, where it is passed to. -/
  mid : ∀ (T : Set (points B S hS F))
    (Tri : Triangle (DerivedCategory (Modules.{u, u} B S hS F hF))),
    Tri ∈ distTriang (DerivedCategory (Modules.{u, u} B S hS F hF)) →
      CohomologySupportedOn B S hS F hF T Tri.obj₁ →
      CohomologySupportedOn B S hS F hF T Tri.obj₃ →
        CohomologySupportedOn B S hS F hF T Tri.obj₂
  /-- For every closed `T` whose open complement has quasi-compact inclusion: the integer `r` of
  Stacks 08HJ, the cut-off `r'` of the base case, the base case, the step, and the existence of
  an amplitude over `Tout`. -/
  data : letI : TopologicalSpace (points B S hS F) := pointTopology B S hS F
    ∀ (T : Set (points B S hS F)) (hT : IsClosed T),
      IsQuasiCompact B S hS
          ((openSubspacesOrderIso B S hS F hF).symm ⟨Tᶜ, hT.isOpen_compl⟩).1.ι →
        ∃ r r' : ℤ,
          (∀ (m : ℤ) (E : QuasicoherentDerivedCategory.{u, u} B S hS F hF),
              ApproximationInput B S hS F hF T r m E →
              CohomologySupportedOnFrom B S hS F hF Tout (m - r' + 1) E.obj →
                ApproximationHolds B S hS F hF T E m) ∧
          (∀ (m t : ℤ) (E : QuasicoherentDerivedCategory.{u, u} B S hS F hF), m - r' < t →
              ApproximationInput B S hS F hF T r m E →
              CohomologySupportedOnFrom B S hS F hF Tout (t + 1) E.obj →
                ∃ (Tri : Triangle (DerivedCategory (Modules.{u, u} B S hS F hF)))
                  (E' : QuasicoherentDerivedCategory.{u, u} B S hS F hF),
                  Tri ∈ distTriang (DerivedCategory (Modules.{u, u} B S hS F hF)) ∧
                    (smallEtaleRingedSite B S hS F hF).IsPerfect Tri.obj₁ ∧
                    CohomologySupportedOn B S hS F hF T Tri.obj₁ ∧
                    E.obj = Tri.obj₂ ∧ E'.obj = Tri.obj₃ ∧
                    ApproximationInput B S hS F hF T r m E' ∧
                    CohomologySupportedOnFrom B S hS F hF Tout t E'.obj) ∧
          (∀ (m : ℤ) (E : QuasicoherentDerivedCategory.{u, u} B S hS F hF),
              ApproximationInput B S hS F hF T r m E →
                ∃ t : ℤ, CohomologySupportedOnFrom B S hS F hF Tout (t + 1) E.obj)

/-- **Approximation by perfect complexes from the induction of Stacks 08HN**, read off from
`AlgebraicGeometry.Space.AmplitudeInductionInputs`. -/
theorem approximationByPerfectComplexes_of_amplitudeInduction
    (Tout : Set (points B S hS F)) (h : AmplitudeInductionInputs B S hS F hF Tout) :
    ApproximationByPerfectComplexes.{u, u} B S hS F hF := by
  intro T hT hTc
  obtain ⟨r, r', hbase, hstep, hbound⟩ := h.data T hT hTc
  refine ⟨r, fun E m hpcE hsuppE => ?_⟩
  obtain ⟨t, hamp⟩ := hbound m E ⟨hpcE, hsuppE⟩
  exact approximationHolds_of_amplitudeInduction B S hS F hF T Tout m (m - r')
    (ApproximationInput B S hS F hF T r m) (hbase m)
    (fun t E ht hGood hampE => hstep m t E ht hGood hampE) (h.mid T) t E ⟨hpcE, hsuppE⟩ hamp

end Induction

end AlgebraicGeometry.Space

end
