module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ConormalApproximationCompletedCharts
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ConormalApproximationLocality
public import StacksFrontier.RingTheory.AdicCompletion.QuotientCompletionMap

/-!
# The sub-family of presented charts over which the comparison is available

`Stacks.ConormalApproximation.commonChartAssociatedGradedEquivOfPresentedCharts` asks for the
chart-local comparison over *every* member of
`Stacks.ConormalApproximation.PresentedChart` — every affine open of `Y` above `T₀` with every
finite presentation. That is more than Stacks 0CAY's affine core can give: the core produces an
Artin-Rees bound depending on the presentation, and
`Stacks.ConormalApproximation.exists_pointed_extension_merge_family` merges only finitely many
conditions, so one bound serves only finitely many charts.

What the gluing actually uses of the family is the two conditions of
`Stacks.Conormal.CommonChartAssociatedGradedEquiv`: the opens form a basis of the fibre, and two
members with a common point admit a refining member. Both survive restriction to the sub-family
cut out by *any* predicate `P` on presented charts which is rich enough around every point and
closed under the refinement — and `Stacks.ConormalApproximation.sameDenominator_of_localization`
says that the predicate "the denominator criterion holds here" is exactly that, because the charts
arbitrarily small below a given one are its basic opens.

This file carries the comparison over such a sub-family. It is a sibling of the full-family chain,
not a weakening of it: the full-family declarations are unchanged and still available.

## Main results

* `Stacks.ConormalApproximation.isBasis_commonChartOfSubPresentedChart`: the opens of the
  sub-family form a basis of the fibre, from richness of `P` around each point.
* `Stacks.ConormalApproximation.commonChartAssociatedGradedEquivOfSubPresentedCharts`: the
  comparison of associated graded algebras over the sub-family.
* `Stacks.ConormalApproximation.nonempty_conormalAlgebra_iso_of_subPresentedCharts_of_eq_on`:
  **the conormal algebras are isomorphic**, with the comparison required only over the
  sub-family.

## References

* [Stacks Project, Tag 0CAY](https://stacks.math.columbia.edu/tag/0CAY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.ConormalApproximation

/-- **The richness condition on a sub-family of presented charts**: every point of every open of
the fibre has a member of the sub-family around it whose part of the fibre lies inside that open.
This is what makes the opens of the sub-family a basis of the fibre. -/
def IsRichPredicate {T Y : Scheme.{u}} (p : Y ⟶ T) (t : T) {T₀ : T.Opens} {C : Type u}
    [CommRing C] (eC : Γ(T, T₀) ≃+* C) (P : PresentedChart p T₀ C eC → Prop) : Prop :=
  ∀ (Ω : (p.fiber t).Opens) (x : p.fiber t), x ∈ Ω →
    ∃ a : PresentedChart p T₀ C eC, P a ∧ x ∈ p.fiberι t ⁻¹ᵁ a.U ∧ p.fiberι t ⁻¹ᵁ a.U ≤ Ω

/-- **The refinement-closure condition on a sub-family of presented charts**: two members and a
point of both their opens admit a member of the sub-family refining both, with a presentation
whose variables absorb the generators of both. This is what makes the refinement condition of
`Stacks.Conormal.CommonChartAssociatedGradedEquiv` satisfiable inside the sub-family. -/
def IsRefinementClosed {T Y : Scheme.{u}} (p : Y ⟶ T) (t : T) {T₀ : T.Opens} {C : Type u}
    [CommRing C] (eC : Γ(T, T₀) ≃+* C) (P : PresentedChart p T₀ C eC → Prop) : Prop :=
  ∀ a₁ a₂ : PresentedChart p T₀ C eC, P a₁ → P a₂ → ∀ x : p.fiber t,
    x ∈ p.fiberι t ⁻¹ᵁ a₁.U → x ∈ p.fiberι t ⁻¹ᵁ a₂.U →
    ∃ (k : PresentedChart p T₀ C eC) (_ : P k) (_ : x ∈ p.fiberι t ⁻¹ᵁ k.U)
      (h₁ : k.U ≤ a₁.U) (h₂ : k.U ≤ a₂.U)
      (ι₁ : Fin a₁.n → Fin k.n) (ι₂ : Fin a₂.n → Fin k.n),
      (∀ i, k.val (ι₁ i) = (Y.presheaf.map (homOfLE h₁).op).hom (a₁.val i)) ∧
        ∀ i, k.val (ι₂ i) = (Y.presheaf.map (homOfLE h₂).op).hom (a₂.val i)

section SubFamily

variable {T Y W W' : Scheme.{u}} (p : Y ⟶ T) (t : T) (b : W ⟶ T) (b' : W' ⟶ T)
  {r : Spec (CommRingCat.of (T.residueField t)) ⟶ W}
  {r' : Spec (CommRingCat.of (T.residueField t)) ⟶ W'}
  {j : p.fiber t ⟶ pullback p b} {j' : p.fiber t ⟶ pullback p b'}
  [IsClosedImmersion j] [IsClosedImmersion j']
  (hr : r ≫ b = T.fromSpecResidueField t) (hr' : r' ≫ b' = T.fromSpecResidueField t)
  (hfst : j ≫ pullback.fst p b = p.fiberι t)
  (hsnd : j ≫ pullback.snd p b = p.fiberToSpecResidueField t ≫ r)
  (hfst' : j' ≫ pullback.fst p b' = p.fiberι t)
  (hsnd' : j' ≫ pullback.snd p b' = p.fiberToSpecResidueField t ≫ r')
  {T₀ : T.Opens} {W₀ : W.Opens} {W₀' : W'.Opens}
  (hT₀ : IsAffineOpen T₀) (hW₀ : IsAffineOpen W₀) (hW₀' : IsAffineOpen W₀')
  (hW₀T : W₀ ≤ b ⁻¹ᵁ T₀) (hW₀'T : W₀' ≤ b' ⁻¹ᵁ T₀)
  (hrW : (⊤ : (Spec (CommRingCat.of (T.residueField t))).Opens) ≤ r ⁻¹ᵁ W₀)
  (hrW' : (⊤ : (Spec (CommRingCat.of (T.residueField t))).Opens) ≤ r' ⁻¹ᵁ W₀')
  {C : Type u} [CommRing C] (eC : Γ(T, T₀) ≃+* C)
  {D : Type u} [CommRing D] (sigma sigma' : C →+* D)
  (eD : Γ(W, W₀) ≃+* D) (eD' : Γ(W', W₀') ≃+* D)
  (hD : ∀ x : Γ(T, T₀), eD ((b.appLE T₀ W₀ hW₀T).hom x) = sigma (eC x))
  (hD' : ∀ x : Γ(T, T₀), eD' ((b'.appLE T₀ W₀' hW₀'T).hom x) = sigma' (eC x))
  (I : Ideal D)
  (hI : (RingHom.ker (r.appLE W₀ ⊤ hrW).hom).map (eD : Γ(W, W₀) →+* D) = I)
  (hI' : (RingHom.ker (r'.appLE W₀' ⊤ hrW').hom).map (eD' : Γ(W', W₀') →+* D) = I)
  (hsurj : Function.Surjective (r.appLE W₀ ⊤ hrW).hom)
  (hsurj' : Function.Surjective (r'.appLE W₀' ⊤ hrW').hom)
  (hsource : ∀ d : D,
    (r.appLE W₀ ⊤ hrW).hom (eD.symm d) = (r'.appLE W₀' ⊤ hrW').hom (eD'.symm d))
  (P : PresentedChart p T₀ C eC → Prop)

variable [LocallyOfFiniteType p] [IsNoetherian T]

include hfst hsnd hfst' hsnd' hrW hrW' in
omit [LocallyOfFiniteType p] [AlgebraicGeometry.IsNoetherian T] in
/-- **The opens of the sub-family form a basis of the topology of the fibre**, as soon as every
point of every open of the fibre has a member of the sub-family around it inside that open. This
is the field `isBasis` of `Stacks.Conormal.CommonChartAssociatedGradedEquiv` for the sub-family. -/
theorem isBasis_commonChartOfSubPresentedChart
    (hbasis : IsRichPredicate p t eC P) :
    Opens.IsBasis (Set.range fun a : {a : PresentedChart p T₀ C eC // P a} =>
      Stacks.Conormal.commonChartOpens j j'
        (commonChartOfPresentedChart p t b b' hfst hsnd hfst' hsnd' hT₀ hW₀ hW₀' hW₀T hW₀'T
          hrW hrW' eC a.1)) := by
  rw [Opens.isBasis_iff_nbhd]
  intro Ω x hx
  obtain ⟨a, hPa, hxa, haΩ⟩ := hbasis Ω x hx
  refine ⟨_, ⟨⟨a, hPa⟩, rfl⟩, ?_, ?_⟩
  · simpa only [commonChartOpens_commonChartOfPresentedChart] using hxa
  · simpa only [commonChartOpens_commonChartOfPresentedChart] using haΩ

include hr hr' hfst hsnd hfst' hsnd' hT₀ hW₀ hW₀' hW₀T hW₀'T hrW hrW' eC hD hD' hI hI'
  hsurj hsurj' hsource in
/-- **The comparison of the associated graded algebras of the two fibre immersions over the
sub-family of charts where it is available.** The three fields of
`Stacks.Conormal.CommonChartAssociatedGradedEquiv` come from: `hbasis`, the comparison `e` over
the members of the sub-family, and `hrefine` followed by
`Stacks.ConormalApproximation.chartQuotientPresentationHomOfPresentedCharts`.

The refinement condition is asked of the sub-family itself: the refining member must again satisfy
`P`. For `P` the denominator criterion that is
`Stacks.ConormalApproximation.sameDenominator_of_localization`, the refining member being a basic
open of the one it refines. -/
def commonChartAssociatedGradedEquivOfSubPresentedCharts
    (hbasis : IsRichPredicate p t eC P)
    (hrefine : IsRefinementClosed p t eC P)
    (e : ∀ a : {a : PresentedChart p T₀ C eC // P a},
      AssociatedGraded.GradedAlgEquiv
        (I.map (MvPolynomial.C : D →+* MvPolynomial (Fin a.1.n) D))
        (MvPolynomial (Fin a.1.n) D ⧸ LinearMap.range (relationMapOfHom sigma a.1.relation))
        (MvPolynomial (Fin a.1.n) D ⧸ LinearMap.range (relationMapOfHom sigma' a.1.relation)))
    (hind : ∀ a, (e a).IsInducedByIdentity) :
    Stacks.Conormal.CommonChartAssociatedGradedEquiv j j'
      (fun a : {a : PresentedChart p T₀ C eC // P a} =>
        commonChartOfPresentedChart p t b b' hfst hsnd hfst' hsnd' hT₀ hW₀ hW₀' hW₀T hW₀'T
          hrW hrW' eC a.1) :=
  Stacks.Conormal.commonChartAssociatedGradedEquivOfPresentations j j' _
    (isBasis_commonChartOfSubPresentedChart p t b b' hfst hsnd hfst' hsnd' hT₀ hW₀ hW₀' hW₀T
      hW₀'T hrW hrW' eC P hbasis)
    (fun a => MvPolynomial (Fin a.1.n) D)
    (fun a => I.map (MvPolynomial.C : D →+* MvPolynomial (Fin a.1.n) D))
    (fun a => LinearMap.range (relationMapOfHom sigma a.1.relation))
    (fun a => LinearMap.range (relationMapOfHom sigma' a.1.relation))
    (fun a => chartPresentationOfHom p t b hr hfst hsnd hT₀ hW₀ hW₀T hrW eC sigma eD hD
      I hI hsurj a.1)
    (fun a => chartPresentationOfHom p t b' hr' hfst' hsnd' hT₀ hW₀' hW₀'T hrW' eC sigma' eD' hD'
      I hI' hsurj' a.1)
    e hind
    (fun a z => toSourceHom_cast_eq p t b b' hr hr' hfst hsnd hfst' hsnd' hT₀ hW₀ hW₀' hW₀T hW₀'T
      hrW hrW' eC sigma sigma' eD eD' hD hD' I hI hI' hsurj hsurj' hsource a.1 z)
    (fun a₁ a₂ x hx₁ hx₂ => by
      rw [commonChartOpens_commonChartOfPresentedChart] at hx₁ hx₂
      obtain ⟨k, hPk, hxk, h₁, h₂, ι₁, ι₂, hι₁, hι₂⟩ :=
        hrefine a₁.1 a₂.1 a₁.2 a₂.2 x hx₁ hx₂
      refine ⟨⟨k, hPk⟩, ?_,
        pullbackChart_mono p b hT₀ hW₀ a₁.1.isAffineOpen k.isAffineOpen hW₀T a₁.1.le_preimage
          k.le_preimage h₁,
        pullbackChart_mono p b' hT₀ hW₀' a₁.1.isAffineOpen k.isAffineOpen hW₀'T a₁.1.le_preimage
          k.le_preimage h₁,
        pullbackChart_mono p b hT₀ hW₀ a₂.1.isAffineOpen k.isAffineOpen hW₀T a₂.1.le_preimage
          k.le_preimage h₂,
        pullbackChart_mono p b' hT₀ hW₀' a₂.1.isAffineOpen k.isAffineOpen hW₀'T a₂.1.le_preimage
          k.le_preimage h₂,
        ⟨chartQuotientPresentationHomOfPresentedCharts p t b b' hr hr' hfst hsnd hfst' hsnd'
          hT₀ hW₀ hW₀' hW₀T hW₀'T hrW hrW' eC sigma sigma' eD eD' hD hD' I hI hI' hsurj hsurj'
          a₁.1 k h₁ ι₁ hι₁⟩,
        ⟨chartQuotientPresentationHomOfPresentedCharts p t b b' hr hr' hfst hsnd hfst' hsnd'
          hT₀ hW₀ hW₀' hW₀T hW₀'T hrW hrW' eC sigma sigma' eD eD' hD hD' I hI hI' hsurj hsurj'
          a₂.1 k h₂ ι₂ hι₂⟩⟩
      rw [commonChartOpens_commonChartOfPresentedChart]
      exact hxk)

include hr hr' hfst hsnd hfst' hsnd' hT₀ hW₀ hW₀' hW₀T hW₀'T hrW hrW' eC hD hD' hI
  hsurj hsurj' hsource in
omit [LocallyOfFiniteType p] [AlgebraicGeometry.IsNoetherian T] in
/-- **The conormal algebras of the two fibre immersions are isomorphic, with the comparison
required only over the sub-family.** The ideal is named once, `hI'` being discharged by
`Stacks.ConormalApproximation.map_ker_appLE_eq`. -/
theorem nonempty_conormalAlgebra_iso_of_subPresentedCharts_of_eq_on
    (hbasis : IsRichPredicate p t eC P)
    (hrefine : IsRefinementClosed p t eC P)
    (e : ∀ a : {a : PresentedChart p T₀ C eC // P a},
      AssociatedGraded.GradedAlgEquiv
        (I.map (MvPolynomial.C : D →+* MvPolynomial (Fin a.1.n) D))
        (MvPolynomial (Fin a.1.n) D ⧸ LinearMap.range (relationMapOfHom sigma a.1.relation))
        (MvPolynomial (Fin a.1.n) D ⧸ LinearMap.range (relationMapOfHom sigma' a.1.relation)))
    (hind : ∀ a, (e a).IsInducedByIdentity) :
    Nonempty ((Stacks.Conormal.conormalAlgebra j).algebra ≅
      (Stacks.Conormal.conormalAlgebra j').algebra) :=
  Stacks.Conormal.nonempty_conormalAlgebra_iso_of_commonChartAssociatedGradedEquiv j j'
    (commonChartAssociatedGradedEquivOfSubPresentedCharts p t b b' hr hr' hfst hsnd hfst' hsnd'
      hT₀ hW₀ hW₀' hW₀T hW₀'T hrW hrW' eC sigma sigma' eD eD' hD hD' I hI
      ((map_ker_appLE_eq t hrW hrW' eD eD' hsource).symm.trans hI) hsurj hsurj' hsource P
      hbasis hrefine e hind)

end SubFamily

/-! ### The sub-family cut out by the denominator criterion -/

section Denominator

variable {T Y : Scheme.{u}} (p : Y ⟶ T) [LocallyOfFiniteType p] [IsNoetherian T] (t : T)
  {T₀ : T.Opens} (hT₀ : IsAffineOpen T₀) {C : Type u} [CommRing C] (eC : Γ(T, T₀) ≃+* C)
  {D : Type u} [CommRing D] (sigma sigma' : C →+* D) (I : Ideal D)

/-- **The denominator criterion, read at a presented chart.** For the two base changes of Stacks
0CAY this is, by `Stacks.ArtinRees.sameDenominator_iff_exists_isInducedByIdentity`, exactly the
existence of the identity-induced comparison of associated graded algebras that the chart family
asks for at that chart. -/
def HasChartSameDenominator (a : PresentedChart p T₀ C eC) : Prop :=
  Stacks.ArtinRees.SameDenominator
    (I.map (MvPolynomial.C : D →+* MvPolynomial (Fin a.n) D))
    (LinearMap.range (relationMapOfHom sigma a.relation))
    (LinearMap.range (relationMapOfHom sigma' a.relation))

omit [LocallyOfFiniteType p] [AlgebraicGeometry.IsNoetherian T] in
/-- **The criterion passes from a presented chart to a presented chart whose open is a basic open
of it.** This is `Stacks.ConormalApproximation.sameDenominator_of_localization` with the geometric
input supplied: the sections over a basic open of an affine open are a localization
(`AlgebraicGeometry.IsAffineOpen.isLocalization_of_eq_basicOpen`), the inverted element is the
value at the generators of a polynomial over `C` (`Algebra.Generators.σ`), and each generator of
the smaller chart's presentation is such a value divided by a power of it
(`IsLocalization.surj`). -/
theorem hasChartSameDenominator_of_basicOpen (hσ : ∀ c, sigma c - sigma' c ∈ I)
    (a : PresentedChart p T₀ C eC) (ha : HasChartSameDenominator p eC sigma sigma' I a)
    (f : Γ(Y, a.U)) (k : PresentedChart p T₀ C eC) (hk : k.U = Y.basicOpen f) :
    HasChartSameDenominator p eC sigma sigma' I k := by
  have hkle : k.U ≤ a.U := hk ▸ Y.basicOpen_le f
  let algA : Algebra C Γ(Y, a.U) := chartAlgebra p a.le_preimage eC
  let algK : Algebra C Γ(Y, k.U) := chartAlgebra p k.le_preimage eC
  let algAK : Algebra Γ(Y, a.U) Γ(Y, k.U) :=
    (Y.presheaf.map (homOfLE hkle).op).hom.toAlgebra
  have htower : IsScalarTower C Γ(Y, a.U) Γ(Y, k.U) :=
    IsScalarTower.of_algebraMap_eq fun c =>
      ((restrictAlgHom p eC a.le_preimage k.le_preimage hkle).commutes c).symm
  have hloc : IsLocalization.Away f Γ(Y, k.U) :=
    a.isAffineOpen.isLocalization_of_eq_basicOpen f (homOfLE hkle) hk
  have hgen : ∀ j : Fin k.n, ∃ (Yj : MvPolynomial (Fin a.n) C) (d : ℕ),
      algebraMap Γ(Y, a.U) Γ(Y, k.U) (MvPolynomial.aeval a.presentation.val Yj) =
        k.presentation.val j * algebraMap Γ(Y, a.U) Γ(Y, k.U) f ^ d := by
    intro j
    obtain ⟨xs, hxs⟩ := IsLocalization.surj (Submonoid.powers f) (k.presentation.val j)
    obtain ⟨d, hd⟩ := xs.2.2
    refine ⟨a.presentation.σ xs.1, d, ?_⟩
    rw [a.presentation.aeval_val_σ, ← hxs, ← hd, map_pow]
  choose Yf dd hYf using hgen
  exact sameDenominator_of_localization hσ f a.presentation k.presentation
    (a.presentation.σ f) (a.presentation.aeval_val_σ f) Yf dd hYf ha

/-- A point of `a.U ⊓ V` has a basic open of `a.U` around it, inside `V`, carrying a presentation
that satisfies the criterion and whose variables absorb the sections `z` over it. -/
private theorem exists_hasChartSameDenominator_basicOpen (hT₀ : IsAffineOpen T₀)
    (hσ : ∀ c, sigma c - sigma' c ∈ I)
    (a : PresentedChart p T₀ C eC) (ha : HasChartSameDenominator p eC sigma sigma' I a)
    {V : Y.Opens} {y : Y} (hya : y ∈ a.U) (hyV : y ∈ V) {k : ℕ}
    (z : ∀ U : Y.Opens, U ≤ a.U ⊓ V → Fin k → Γ(Y, U)) :
    ∃ (c : PresentedChart p T₀ C eC) (ι : Fin k → Fin c.n) (h : c.U ≤ a.U ⊓ V),
      HasChartSameDenominator p eC sigma sigma' I c ∧ y ∈ c.U ∧ ∀ i, c.val (ι i) = z c.U h i := by
  obtain ⟨f, hfle, hyf⟩ := a.isAffineOpen.exists_basicOpen_le (V := a.U ⊓ V) ⟨y, hya, hyV⟩ hya
  have hUT : Y.basicOpen f ≤ p ⁻¹ᵁ T₀ := (hfle.trans inf_le_left).trans a.le_preimage
  obtain ⟨n, m, P, ι, hval⟩ :=
    exists_presentedChart_val_eq p hT₀ eC (a.isAffineOpen.basicOpen f) hUT (z _ hfle)
  exact ⟨⟨Y.basicOpen f, a.isAffineOpen.basicOpen f, hUT, n, m, P⟩, ι, hfle,
    hasChartSameDenominator_of_basicOpen p eC sigma sigma' I hσ a ha f _ rfl, hyf, hval⟩

include hT₀ in
/-- **The sub-family cut out by the denominator criterion is refinement-closed.** Two members and a
point of both their opens admit a refining member: a basic open of the first inside the
intersection, which again satisfies the criterion by
`Stacks.ConormalApproximation.hasChartSameDenominator_of_basicOpen`, carrying a presentation whose
variables absorb the generators of both by
`Stacks.ConormalApproximation.exists_presentedChart_val_eq`.

This is where restricting to *basic* opens rather than to arbitrary affine opens matters: the
criterion propagates down a localization, and shrinking to a basic open is exactly a
localization. -/
theorem isRefinementClosed_hasChartSameDenominator (hσ : ∀ c, sigma c - sigma' c ∈ I) :
    IsRefinementClosed p t eC (HasChartSameDenominator p eC sigma sigma' I) := by
  intro a₁ a₂ h₁ h₂ x hx₁ hx₂
  obtain ⟨k, ι, h, hk, hxk, hval⟩ := exists_hasChartSameDenominator_basicOpen p eC sigma
    sigma' I hT₀ hσ a₁ h₁ (y := p.fiberι t x) (V := a₂.U) hx₁ hx₂
    (z := fun U hU => Fin.addCases
      (fun i : Fin a₁.n => (Y.presheaf.map (homOfLE (hU.trans inf_le_left)).op).hom (a₁.val i))
      (fun i : Fin a₂.n => (Y.presheaf.map (homOfLE (hU.trans inf_le_right)).op).hom (a₂.val i)))
  exact ⟨k, hk, hxk, h.trans inf_le_left, h.trans inf_le_right, ι ∘ Fin.castAdd a₂.n,
    ι ∘ Fin.natAdd a₁.n, fun i => (hval _).trans (Fin.addCases_left i),
    fun i => (hval _).trans (Fin.addCases_right i)⟩

include hT₀ in
/-- **Finitely many presented charts satisfying the criterion whose opens cover the fibre make the
sub-family rich.** Around a point of an open of the fibre, pick a member of the family containing
it and shrink it to a basic open inside the open of `Y` cutting the given open of the fibre out;
the criterion survives by
`Stacks.ConormalApproximation.hasChartSameDenominator_of_basicOpen`.

This is the step for which a *finite* cover suffices, and it is the whole reason the affine core
of Stacks 0CAY — whose Artin-Rees bound depends on the presentation — can be used at all. -/
theorem isRichPredicate_hasChartSameDenominator_of_cover (hσ : ∀ c, sigma c - sigma' c ∈ I)
    {n : ℕ} (a : Fin n → PresentedChart p T₀ C eC)
    (ha : ∀ i, HasChartSameDenominator p eC sigma sigma' I (a i))
    (hcover : ∀ x : p.fiber t, ∃ i, x ∈ p.fiberι t ⁻¹ᵁ (a i).U) :
    IsRichPredicate p t eC (HasChartSameDenominator p eC sigma sigma' I) := by
  intro Ω x hx
  obtain ⟨i, hxi⟩ := hcover x
  obtain ⟨O, hO, hpre⟩ := (p.fiberι t).isEmbedding.isInducing.isOpen_iff.mp Ω.2
  have hmem : ∀ z : p.fiber t, p.fiberι t z ∈ O ↔ z ∈ Ω := fun z => Set.ext_iff.1 hpre z
  obtain ⟨k, -, h, hk, hxk, -⟩ := exists_hasChartSameDenominator_basicOpen p eC sigma sigma'
    I hT₀ hσ (a i) (ha i) (y := p.fiberι t x) (V := ⟨O, hO⟩) hxi ((hmem x).2 hx)
    (z := fun _ _ => Fin.elim0)
  exact ⟨k, hk, hxk, fun z hz => (hmem z).1 (h.trans inf_le_right hz)⟩

include hT₀ in
/-- **The fibre is covered by finitely many presented charts.** The fibre of a quasi-compact
morphism is a compact space, and every point of it has an affine open of `Y` above `T₀` around it
carrying a presentation. -/
theorem exists_finite_presentedChart_cover [QuasiCompact p] (ht : t ∈ T₀) :
    ∃ (n : ℕ) (a : Fin n → PresentedChart p T₀ C eC),
      ∀ x : p.fiber t, ∃ i, x ∈ p.fiberι t ⁻¹ᵁ (a i).U := by
  classical
  have hsub : (Set.univ : Set (p.fiber t)) ⊆
      ⋃ a : PresentedChart p T₀ C eC, (p.fiberι t ⁻¹ᵁ a.U : Set (p.fiber t)) := by
    intro x _
    obtain ⟨U, hU, hUT, -, hxU⟩ := exists_affineOpen_le_preimage_fiberι p t ht ⊤ x trivial
    obtain ⟨n, m, P, -, -⟩ :=
      exists_presentedChart_val_eq p hT₀ eC hU hUT (k := 0) (fun z => z.elim0)
    exact Set.mem_iUnion.2 ⟨⟨U, hU, hUT, n, m, P⟩, hxU⟩
  obtain ⟨sf, hsf⟩ := isCompact_univ.elim_finite_subcover
    (fun a : PresentedChart p T₀ C eC => (p.fiberι t ⁻¹ᵁ a.U : Set (p.fiber t)))
    (fun a => (p.fiberι t ⁻¹ᵁ a.U).2) hsub
  refine ⟨sf.card, fun i => (sf.equivFin.symm i : PresentedChart p T₀ C eC), fun x => ?_⟩
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hsf (Set.mem_univ x))
  exact ⟨sf.equivFin ⟨a, ha⟩, by simpa using hxa⟩

end Denominator

/-- If `σ = τ ∘ g` and `τ - τ'` lands in `𝔪_s^N ⬝ 𝒪^∧_{S,s}` for `N ≥ 1`, then `σ - τ' ∘ g` lands
in the maximal ideal of `𝒪^∧_{S,s}`. -/
private theorem sub_comp_pointedStalkMap_mem_maximalIdeal {S T T₁ : Scheme.{u}} [IsNoetherian S]
    (s : S) (t : T) {sigma : T.presheaf.stalk t →+* completedStalk S s} (g : T₁ ⟶ T) {t₁ : T₁}
    (hgt : g t₁ = t) {tau tau' : T₁.presheaf.stalk t₁ →+* completedStalk S s}
    (hfact : sigma = tau.comp (pointedStalkMap g hgt)) {N : ℕ} (hN : 1 ≤ N)
    (hcongr : ∀ y, tau y - tau' y ∈
      Ideal.map (algebraMap (S.presheaf.stalk s) (completedStalk S s))
        (IsLocalRing.maximalIdeal (S.presheaf.stalk s) ^ N))
    (x : T.presheaf.stalk t) :
    sigma x - (tau'.comp (pointedStalkMap g hgt)) x ∈
      IsLocalRing.maximalIdeal (completedStalk S s) := by
  subst hfact
  exact sub_mem_maximalIdeal_of_mem_map_pow s hN (hcongr _)

/-! ### The two completed base changes of Stacks 0CAY -/

section Completed

variable {S T Y : Scheme.{u}} (p : Y ⟶ T) [LocallyOfFiniteType p] [IsNoetherian T]
  [IsNoetherian S] (s : S) (t : T) {T₀ : T.Opens} (hT₀ : IsAffineOpen T₀) (ht : t ∈ T₀)
  (sigma sigma' : T.presheaf.stalk t →+* completedStalk S s)

include hT₀ ht in
omit [LocallyOfFiniteType p] [AlgebraicGeometry.IsNoetherian T] in
/-- **`Stacks.ConormalApproximation.HasConormalIso` for the two completed base changes, with the
chart comparison required only over a rich, refinement-closed sub-family of presented charts.**
Every geometric hypothesis is discharged exactly as in
`Stacks.ConormalApproximation.hasConormalIso_of_chartGradedAlgEquiv`; what differs is that the
comparison is asked for only over the sub-family, which is what the affine core of Stacks 0CAY
can supply. -/
theorem hasConormalIso_of_subChartGradedAlgEquiv
    (hcong : ∀ x, sigma x - sigma' x ∈ IsLocalRing.maximalIdeal (completedStalk S s))
    (P : PresentedChart p T₀ Γ(T, T₀) (RingEquiv.refl Γ(T, T₀)) → Prop)
    (hbasis : IsRichPredicate p t (RingEquiv.refl Γ(T, T₀)) P)
    (hrefine : IsRefinementClosed p t (RingEquiv.refl Γ(T, T₀)) P)
    (e : ∀ a : {a : PresentedChart p T₀ Γ(T, T₀) (RingEquiv.refl Γ(T, T₀)) // P a},
      AssociatedGraded.GradedAlgEquiv
        ((IsLocalRing.maximalIdeal (completedStalk S s)).map
          (MvPolynomial.C : completedStalk S s →+*
            MvPolynomial (Fin a.1.n) (completedStalk S s)))
        (MvPolynomial (Fin a.1.n) (completedStalk S s) ⧸
          LinearMap.range (relationMapOfHom (completedChartHom t ht sigma) a.1.relation))
        (MvPolynomial (Fin a.1.n) (completedStalk S s) ⧸
          LinearMap.range (relationMapOfHom (completedChartHom t ht sigma') a.1.relation)))
    (hind : ∀ a, (e a).IsInducedByIdentity) :
    HasConormalIso p t (Spec.map (CommRingCat.ofHom sigma) ≫ T.fromSpecStalk t)
      (Spec.map (CommRingCat.ofHom sigma') ≫ T.fromSpecStalk t) := by
  intro r r' j j' hr hr' hfst hfst' hsnd hsnd' hj hj'
  have := hj
  have := hj'
  have hrr : r = r' :=
    eq_of_sub_mem_maximalIdeal t (CommRingCat.ofHom sigma) (CommRingCat.ofHom sigma') hcong r r'
      hr hr'
  refine nonempty_conormalAlgebra_iso_of_subPresentedCharts_of_eq_on p t _ _ hr hr' hfst hsnd
    hfst' hsnd' hT₀ (isAffineOpen_top _) (isAffineOpen_top _)
    (preimage_eq_top_specMap_fromSpecStalk t ht (CommRingCat.ofHom sigma)).ge
    (preimage_eq_top_specMap_fromSpecStalk t ht (CommRingCat.ofHom sigma')).ge
    le_top le_top (RingEquiv.refl Γ(T, T₀))
    (completedChartHom t ht sigma) (completedChartHom t ht sigma')
    (specTopEquiv _) (specTopEquiv _)
    (fun x => specTopEquiv_appLE_specMap_fromSpecStalk t ht (CommRingCat.ofHom sigma) x)
    (fun x => specTopEquiv_appLE_specMap_fromSpecStalk t ht (CommRingCat.ofHom sigma') x)
    (IsLocalRing.maximalIdeal (completedStalk S s))
    (map_ker_appLE_top_eq_maximalIdeal t (CommRingCat.ofHom sigma) r hr le_top)
    (surjective_appLE_of_comp_eq_fromSpecResidueField t (CommRingCat.ofHom sigma) r hr ⊤
      le_top)
    (surjective_appLE_of_comp_eq_fromSpecResidueField t (CommRingCat.ofHom sigma') r' hr' ⊤
      le_top)
    (fun d => ?_) P hbasis hrefine e hind
  rw [hrr]

include hT₀ ht in
omit [LocallyOfFiniteType p] [AlgebraicGeometry.IsNoetherian T] in
/-- **`Stacks.ConormalApproximation.HasConormalBoundAlongExtension`, with the chart comparison
required only over a rich, refinement-closed sub-family of presented charts.** This is the
declaration whose remaining hypothesis the locality of the identity-induced comparison
eliminates: the sub-family may be taken to be the charts at which the denominator criterion
holds, and by `Stacks.ConormalApproximation.sameDenominator_of_localization` that family is
refinement-closed and, given finitely many charts covering the fibre, rich. -/
theorem hasConormalBoundAlongExtension_of_subChartGradedAlgEquiv
    {T₁ : Scheme.{u}} (g : T₁ ⟶ T) (t₁ : T₁) (hgt : g t₁ = t) [IsNoetherian T₁]
    [LocallyOfFiniteType g] [QuasiCompact g]
    (tau : T₁.presheaf.stalk t₁ →+* completedStalk S s) (htau : IsLocalHom tau)
    (hfact : sigma = tau.comp (pointedStalkMap g hgt))
    (N : ℕ) (hN : 1 ≤ N)
    (hchart : ∀ tau' : T₁.presheaf.stalk t₁ →+* completedStalk S s,
      (∀ y, tau y - tau' y ∈
        Ideal.map (algebraMap (S.presheaf.stalk s) (completedStalk S s))
          (IsLocalRing.maximalIdeal (S.presheaf.stalk s) ^ N)) →
      ∃ P : PresentedChart p T₀ Γ(T, T₀) (RingEquiv.refl Γ(T, T₀)) → Prop,
        IsRichPredicate p t (RingEquiv.refl Γ(T, T₀)) P ∧
          IsRefinementClosed p t (RingEquiv.refl Γ(T, T₀)) P ∧
          ∀ a : PresentedChart p T₀ Γ(T, T₀) (RingEquiv.refl Γ(T, T₀)), P a →
            ∃ eq : AssociatedGraded.GradedAlgEquiv
              ((IsLocalRing.maximalIdeal (completedStalk S s)).map
                (MvPolynomial.C : completedStalk S s →+*
                  MvPolynomial (Fin a.n) (completedStalk S s)))
              (MvPolynomial (Fin a.n) (completedStalk S s) ⧸
                LinearMap.range (relationMapOfHom (completedChartHom t ht sigma) a.relation))
              (MvPolynomial (Fin a.n) (completedStalk S s) ⧸
                LinearMap.range (relationMapOfHom
                  (completedChartHom t ht (tau'.comp (pointedStalkMap g hgt))) a.relation)),
              eq.IsInducedByIdentity) :
    HasConormalBoundAlongExtension p s t sigma := by
  refine ⟨T₁, g, t₁, hgt, inferInstance, inferInstance, inferInstance, tau, htau, hfact, N, hN,
    fun tau' hcongr => ?_⟩
  obtain ⟨P, hb, hre, hcomp⟩ := hchart tau' hcongr
  choose e hind using fun a : {a : PresentedChart p T₀ Γ(T, T₀) (RingEquiv.refl Γ(T, T₀)) // P a} =>
    hcomp a.1 a.2
  exact hasConormalIso_of_subChartGradedAlgEquiv p s t hT₀ ht sigma
    (tau'.comp (pointedStalkMap g hgt))
    (sub_comp_pointedStalkMap_mem_maximalIdeal s t g hgt hfact hN hcongr) P hb hre e hind

include hT₀ ht in
/-- **`Stacks.ConormalApproximation.HasConormalBoundAlongExtension` from the comparison at
*finitely many* charts covering the fibre.** This is the elimination of the per-chart hypothesis
that the locality of the identity-induced comparison buys: the chart family needs the comparison
at charts arbitrarily small, but by
`Stacks.ConormalApproximation.isRefinementClosed_hasChartSameDenominator` and
`Stacks.ConormalApproximation.isRichPredicate_hasChartSameDenominator_of_cover` it is enough to
have the denominator criterion — equivalently, by
`Stacks.ArtinRees.sameDenominator_iff_exists_isInducedByIdentity`, the identity-induced
comparison — at finitely many charts whose opens cover `Y_t`.

A finite family is exactly what the affine core of Stacks 0CAY can serve: it produces a finite
type extension and an Artin-Rees bound per presentation, and
`Stacks.ConormalApproximation.exists_pointed_extension_merge_family` merges finitely many of
those. The fibre is covered by finitely many presented charts by
`Stacks.ConormalApproximation.exists_finite_presentedChart_cover`. -/
theorem hasConormalBoundAlongExtension_of_finiteCoverSameDenominator
    {T₁ : Scheme.{u}} (g : T₁ ⟶ T) (t₁ : T₁) (hgt : g t₁ = t) [IsNoetherian T₁]
    [LocallyOfFiniteType g] [QuasiCompact g]
    (tau : T₁.presheaf.stalk t₁ →+* completedStalk S s) (htau : IsLocalHom tau)
    (hfact : sigma = tau.comp (pointedStalkMap g hgt))
    (N : ℕ) (hN : 1 ≤ N)
    (hcover : ∀ tau' : T₁.presheaf.stalk t₁ →+* completedStalk S s,
      (∀ y, tau y - tau' y ∈
        Ideal.map (algebraMap (S.presheaf.stalk s) (completedStalk S s))
          (IsLocalRing.maximalIdeal (S.presheaf.stalk s) ^ N)) →
      ∃ (n : ℕ) (a : Fin n → PresentedChart p T₀ Γ(T, T₀) (RingEquiv.refl Γ(T, T₀))),
        (∀ x : p.fiber t, ∃ i, x ∈ p.fiberι t ⁻¹ᵁ (a i).U) ∧
          ∀ i, HasChartSameDenominator p (RingEquiv.refl Γ(T, T₀))
            (completedChartHom t ht sigma)
            (completedChartHom t ht (tau'.comp (pointedStalkMap g hgt)))
            (IsLocalRing.maximalIdeal (completedStalk S s)) (a i)) :
    HasConormalBoundAlongExtension p s t sigma := by
  refine hasConormalBoundAlongExtension_of_subChartGradedAlgEquiv p s t hT₀ ht sigma g t₁ hgt
    tau htau hfact N hN fun tau' hcongr => ?_
  obtain ⟨n, a, hcov, hsame⟩ := hcover tau' hcongr
  have hσ : ∀ c : Γ(T, T₀),
      completedChartHom t ht sigma c -
        completedChartHom t ht (tau'.comp (pointedStalkMap g hgt)) c ∈
      IsLocalRing.maximalIdeal (completedStalk S s) := fun c =>
    sub_comp_pointedStalkMap_mem_maximalIdeal s t g hgt hfact hN hcongr (T.presheaf.germ T₀ t ht c)
  refine ⟨HasChartSameDenominator p (RingEquiv.refl Γ(T, T₀)) (completedChartHom t ht sigma)
      (completedChartHom t ht (tau'.comp (pointedStalkMap g hgt)))
      (IsLocalRing.maximalIdeal (completedStalk S s)),
    isRichPredicate_hasChartSameDenominator_of_cover p t hT₀ (RingEquiv.refl Γ(T, T₀)) _ _ _
      hσ a hsame hcov,
    isRefinementClosed_hasChartSameDenominator p t hT₀ (RingEquiv.refl Γ(T, T₀)) _ _ _ hσ,
    fun k hk => hk.exists_gradedAlgEquiv_isInducedByIdentity⟩

end Completed

/-! ### Stacks 0CAY's comparison hypothesis, discharged -/

section Discharge

variable {S T Y : Scheme.{u}} (p : Y ⟶ T) [LocallyOfFiniteType p] [QuasiCompact p]
  [IsNoetherian T] [IsNoetherian S] (s : S) (t : T)
  {T₀ : T.Opens} (hT₀ : IsAffineOpen T₀) (ht : t ∈ T₀)

include hT₀ ht in
/-- **`Stacks.ConormalApproximation.HasConormalBoundAlongExtension` holds for every local
`σ`.** This is Stacks 0CAY's comparison hypothesis, discharged.

The proof is the source's: cover the fibre by finitely many presented charts
(`Stacks.ConormalApproximation.exists_finite_presentedChart_cover`); apply the affine core
`Stacks.ConormalApproximation.exists_finiteType_coefficients_associatedGraded_equiv` at each,
getting a finite type extension `C'_i` of `Γ(T, T₀)` and an Artin-Rees bound `c_i`; take for the
single extension the `Γ(T, T₀)`-subalgebra of `𝒪^∧_{S,s}` that the images of all the `C'_i`
generate, which is again of finite type, and turn it into a pointed finite type extension of
`(T, t)` by
`AlgebraicGeometry.exists_pointed_extension_of_finiteType_chartAlgebra`; take `N` one more than
the largest `c_i`. A `τ'` congruent to `τ` modulo `𝔪_s^N` then restricts along each `C'_i` to a map
congruent to `τ_i` modulo `𝔪^(c_i+1)`, so the affine core applies at every chart of the cover — and
`Stacks.ConormalApproximation.hasConormalBoundAlongExtension_of_finiteCoverSameDenominator`
propagates that to the charts arbitrarily small which the gluing needs.

Locality of `σ` is a hypothesis of the source ("let `σ : 𝒪_{T,t} → 𝒪_{S,s}^∧` be a local
`𝒪_{S,s}`-algebra map") and is necessary: `HasConormalBoundAlongExtension` asserts that `σ`
factors through a local homomorphism out of the stalk of the extension, which forces it. -/
theorem hasConormalBoundAlongExtension_of_isLocalHom_of_isAffineOpen
    (sigma : T.presheaf.stalk t →+* completedStalk S s) (hsigma : IsLocalHom sigma) :
    HasConormalBoundAlongExtension p s t sigma := by
  classical
  let algCD : Algebra Γ(T, T₀) (completedStalk S s) :=
    (completedChartHom t ht sigma).toAlgebra
  have : IsNoetherianRing (completedStalk S s) :=
    isNoetherianRing_adicCompletion (S.presheaf.stalk s)
  have : IsNoetherianRing Γ(T, T₀) := IsLocallyNoetherian.component_noetherian ⟨T₀, hT₀⟩
  obtain ⟨n, a, hcov⟩ :=
    exists_finite_presentedChart_cover p t hT₀ (RingEquiv.refl Γ(T, T₀)) ht
  -- the affine core at each chart of the cover
  have hcore : ∀ i : Fin n,
      ∃ (C' : Type u) (_ : CommRing C') (_ : Algebra Γ(T, T₀) C')
        (_ : Algebra.FiniteType Γ(T, T₀) C')
        (τ : C' →ₐ[Γ(T, T₀)] completedStalk S s) (cc : ℕ),
        ∀ τ' : C' →+* completedStalk S s,
          (∀ y : C', (τ : C' →+* completedStalk S s) y - τ' y ∈
            IsLocalRing.maximalIdeal (completedStalk S s) ^ (cc + 1)) →
          ∃ eq : AssociatedGraded.GradedAlgEquiv
            ((IsLocalRing.maximalIdeal (completedStalk S s)).map
              (MvPolynomial.C : completedStalk S s →+*
                MvPolynomial (Fin (a i).n) (completedStalk S s)))
            (MvPolynomial (Fin (a i).n) (completedStalk S s) ⧸
              LinearMap.range (relationMapOfHom
                (algebraMap Γ(T, T₀) (completedStalk S s)) (a i).relation))
            (MvPolynomial (Fin (a i).n) (completedStalk S s) ⧸
              LinearMap.range (relationMapOfHom
                (τ'.comp (algebraMap Γ(T, T₀) C')) (a i).relation)),
            eq.IsInducedByIdentity := by
    intro i
    let := chartAlgebra p (a i).le_preimage (RingEquiv.refl Γ(T, T₀))
    exact exists_finiteType_coefficients_associatedGraded_equiv (a i).presentation
      (IsLocalRing.maximalIdeal (completedStalk S s))
  choose C' hCR hAlg hFT τ cc hcore using hcore
  -- one finite type extension dominating all of them: the subalgebra they generate
  have hfg : ∀ i : Fin n, ∃ sg : Finset (C' i),
      Algebra.adjoin Γ(T, T₀) (↑sg : Set (C' i)) = ⊤ := by
    intro i
    let := hCR i
    let := hAlg i
    exact (hFT i).out
  choose sg hsg using hfg
  let : ∀ i, CommRing (C' i) := hCR
  let : ∀ i, Algebra Γ(T, T₀) (C' i) := hAlg
  set G : Finset (completedStalk S s) :=
    Finset.univ.biUnion fun i : Fin n => (sg i).image fun x => τ i x with hG
  set E : Subalgebra Γ(T, T₀) (completedStalk S s) :=
    Algebra.adjoin Γ(T, T₀) (↑G : Set (completedStalk S s)) with hE
  have : Algebra.FiniteType Γ(T, T₀) ↥E :=
    (Subalgebra.fg_iff_finiteType E).1 (hE ▸ Subalgebra.fg_adjoin_finset G)
  have hmemE : ∀ (i : Fin n) (x : C' i), τ i x ∈ E := by
    intro i x
    have hx : τ i x ∈ (⊤ : Subalgebra Γ(T, T₀) (C' i)).map (τ i) :=
      ⟨x, Algebra.mem_top, rfl⟩
    rw [← hsg i, AlgHom.map_adjoin] at hx
    refine Algebra.adjoin_mono (fun y hy => ?_) hx
    obtain ⟨z, hz, rfl⟩ := hy
    exact Finset.mem_coe.2
      (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ i, Finset.mem_image.2 ⟨z, hz, rfl⟩⟩)
  set κ : ∀ i : Fin n, C' i →ₐ[Γ(T, T₀)] ↥E := fun i => (τ i).codRestrict E (hmemE i) with hκ
  -- the pointed finite type extension
  obtain ⟨T₁, g, t₁, hgt, hftg, hqcg, hnoeth₁, tau, iota, htau, hfact, hrhoFac, hclause⟩ :=
    AlgebraicGeometry.exists_pointed_extension_of_finiteType_chartAlgebra t hT₀ ht sigma hsigma
      ↥E (E.val : ↥E →+* completedStalk S s) (RingHom.ext fun x => rfl)
  have := hftg
  have := hqcg
  have := hnoeth₁
  -- the bound
  refine hasConormalBoundAlongExtension_of_finiteCoverSameDenominator p s t hT₀ ht sigma
    g t₁ hgt tau htau hfact (Finset.univ.sup cc + 1) (Nat.le_add_left 1 _) ?_
  intro tau' hcongr
  refine ⟨n, a, hcov, fun i => ?_⟩
  -- the per-chart data, pulled back along the subalgebra
  have hIle : Ideal.map (algebraMap (S.presheaf.stalk s) (completedStalk S s))
        (IsLocalRing.maximalIdeal (S.presheaf.stalk s) ^ (Finset.univ.sup cc + 1)) ≤
      IsLocalRing.maximalIdeal (completedStalk S s) ^ (cc i + 1) := by
    rw [Ideal.map_pow]
    exact (Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le _) _).trans
      (Ideal.pow_le_pow_right
        (Nat.add_le_add_right (Finset.le_sup (f := cc) (Finset.mem_univ i)) 1))
  have hcong : ∀ y : C' i,
      (τ i : C' i →+* completedStalk S s) y -
        ((tau'.comp (iota.comp (κ i : C' i →+* ↥E)))) y ∈
      IsLocalRing.maximalIdeal (completedStalk S s) ^ (cc i + 1) := by
    intro y
    have hval : (τ i : C' i →+* completedStalk S s) y =
        tau (iota (κ i y)) := by
      have h1 : (E.val : ↥E →+* completedStalk S s) (κ i y) =
          (τ i : C' i →+* completedStalk S s) y := rfl
      rw [← h1, hrhoFac]
      rfl
    rw [hval]
    exact hIle (hcongr (iota (κ i y)))
  have hspec : (tau'.comp (iota.comp (κ i : C' i →+* ↥E))).comp
        (algebraMap Γ(T, T₀) (C' i)) =
      completedChartHom t ht (tau'.comp (pointedStalkMap g hgt)) := by
    calc (tau'.comp (iota.comp (κ i : C' i →+* ↥E))).comp (algebraMap Γ(T, T₀) (C' i))
        = (tau'.comp iota).comp
            ((κ i : C' i →+* ↥E).comp (algebraMap Γ(T, T₀) (C' i))) := by
          simp [RingHom.comp_assoc]
      _ = (tau'.comp iota).comp (algebraMap Γ(T, T₀) ↥E) := by rw [(κ i).comp_algebraMap]
      _ = _ := hclause tau'
  obtain ⟨eq, heq⟩ := hcore i _ hcong
  have hsame := Stacks.ArtinRees.sameDenominator_of_isInducedByIdentity eq heq
  rwa [hspec] at hsame

/-- **Stacks 0CAY's comparison hypothesis, with no chart to choose.** Every point of a scheme has
an affine open neighbourhood, so
`Stacks.ConormalApproximation.hasConormalBoundAlongExtension_of_isLocalHom_of_isAffineOpen`
applies at one of them.

This is the form in which
`Stacks.ConormalApproximation.exists_finiteType_pointed_extension_conormalAlgebra_iso_of_bound`
consumes it: its hypothesis `hcompare` is exactly this conclusion, and the locality of `σ` which
it currently derives *from* `hcompare` is a hypothesis of the source. -/
theorem hasConormalBoundAlongExtension_of_isLocalHom
    (sigma : T.presheaf.stalk t →+* completedStalk S s) (hsigma : IsLocalHom sigma) :
    HasConormalBoundAlongExtension p s t sigma := by
  obtain ⟨T₀, hT₀, ht, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := (⊤ : T.Opens)) (x := t) (by simp)
  exact hasConormalBoundAlongExtension_of_isLocalHom_of_isAffineOpen p s t hT₀ ht sigma hsigma

end Discharge


/-! ### Stacks 0CAY -/

section Unconditional

/-- **Stacks 0CAY.** Let `Y → T → S` be finite type morphisms of Noetherian schemes, let `t ∈ T`
lie over `s ∈ S` and let `σ : 𝒪_{T,t} → 𝒪^∧_{S,s}` be a local `𝒪_{S,s}`-algebra map. Then there
is a finite type morphism of pointed schemes `(T', t') → (T, t)` through which `σ` factors by a
local homomorphism, such that for *every* local `𝒪_{S,s}`-algebra map
`σ' : 𝒪_{T,t} → 𝒪^∧_{S,s}` factoring through `𝒪_{T',t'}` the two closed immersions
`Y_σ ← Y_t → Y_{σ'}` of the fibre into the two base changes exist and have isomorphic conormal
algebras.

The hypotheses are the source's and nothing more: `σ` is assumed local because the source assumes
it ("let `σ : 𝒪_{T,t} → 𝒪_{S,s}^∧` be a local `𝒪_{S,s}`-algebra map"), and it is in any case
forced — a factorisation of `σ` through a local homomorphism out of the stalk of an extension
makes `σ` local.

This is
`Stacks.ConormalApproximation.exists_finiteType_pointed_extension_conormalAlgebra_iso_of_bound`
with its comparison hypothesis discharged by
`Stacks.ConormalApproximation.hasConormalBoundAlongExtension_of_isLocalHom`. The two facts that
discharge it are the locality of the identity-induced comparison
(`Stacks.ArtinRees.sameDenominator_iff_exists_isInducedByIdentity` together with
`Stacks.ConormalApproximation.sameDenominator_of_presentations` and
`Stacks.ConormalApproximation.sameDenominator_of_localization`), which lets the chart-local
comparison be propagated from a chart to the basic opens inside it, and the compactness of the
fibre, which makes finitely many charts enough — so the per-presentation Artin-Rees bound of the
affine core suffices, which is exactly the source's "cover `Y` by finitely many affines and glue
by uniqueness". -/
@[stacks 0CAY]
theorem exists_finiteType_pointed_extension_conormalAlgebra_iso_of_isLocalHom
    {S T Y : Scheme.{u}} (f : T ⟶ S) (p : Y ⟶ T)
    [IsNoetherian S] [IsNoetherian T] [IsNoetherian Y]
    [LocallyOfFiniteType f] [QuasiCompact f]
    [LocallyOfFiniteType p] [QuasiCompact p]
    (s : S) (t : T) (ht : f t = s)
    (sigma : T.presheaf.stalk t →+* completedStalk S s) (hsigma : IsLocalHom sigma)
    (hsigma_base : sigma.comp (pointedStalkMap f ht) =
      algebraMap (S.presheaf.stalk s) (completedStalk S s)) :
    ∃ (T' : Scheme.{u}) (g : T' ⟶ T) (t' : T') (hgt : g t' = t)
      (_ : LocallyOfFiniteType g) (_ : QuasiCompact g),
      ∃ tau : T'.presheaf.stalk t' →+* completedStalk S s,
        IsLocalHom tau ∧
        sigma = tau.comp (pointedStalkMap g hgt) ∧
        ∀ sigma' : T.presheaf.stalk t →+* completedStalk S s,
          IsLocalHom sigma' →
          sigma'.comp (pointedStalkMap f ht) =
            algebraMap (S.presheaf.stalk s) (completedStalk S s) →
          (∃ tau' : T'.presheaf.stalk t' →+* completedStalk S s,
            sigma' = tau'.comp (pointedStalkMap g hgt)) →
          HasIsoConormalFibreImmersions p t
            (Spec.map (CommRingCat.ofHom sigma) ≫ T.fromSpecStalk t)
            (Spec.map (CommRingCat.ofHom sigma') ≫ T.fromSpecStalk t) :=
  exists_finiteType_pointed_extension_conormalAlgebra_iso_of_bound f p s t ht sigma
    hsigma_base (hasConormalBoundAlongExtension_of_isLocalHom p s t sigma hsigma)

end Unconditional

end Stacks.ConormalApproximation

end
