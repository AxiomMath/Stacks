module

public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentCoefficient
public import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.SectionQuotientStalk
public import StacksFrontier.AlgebraicGeometry.DenominatorColonIdeal.SectionMultiplication

/-!
# The local ratio chart with the trivializing basis and the ratio equation retained

The coefficient identity
`Stacks.Chow.exists_affineOpen_sheafMultiplicity_sub_eq_finsum_componentOrd` produces an affine
open `V ∋ ξ` and a ratio `a / b` of sections of `𝒪_X` over `V`, both with nonzerodivisor germ at
`ξ`, and expresses `mult(𝒬₂, ξ) - mult(𝒬₁, ξ)` through the orders of vanishing of `a` and `b`
along the components of delta-dimension `k + 1` through `ξ`. What that chain **discards** is the
reason `a / b` is a ratio of `s` at all: the trivializing section `e` of `ℒ` over `V` and the
equation

  `a · e = b · s`   in   `Γ(K_X(ℒ), V)`

which `Stacks.DenominatorLocalRatio.exists_affineOpen_denominator` produces and
`Stacks.DenominatorMul.exists_affineOpen_denominator_presentations_of_isRegular` drops from its
conclusion. That equation is exactly the input needed to recognise `a / b` as a coordinate of the
restriction of `s` to a component, so it has to be carried along.

An existential cannot be strengthened after the fact, so the three statements of the chain are
re-proved here with the two extra clauses `e` and `hbt` retained; the proofs below are those of
the original statements with the two clauses threaded through.

## Main results

* `Stacks.Chow.exists_affineOpen_sectionRatio_denominator_presentations` — the chart of
  `Stacks.DenominatorMul.exists_affineOpen_denominator_presentations_of_isRegular` with the
  trivializing basis and the ratio equation retained.
* `Stacks.Chow.DenominatorStalk.exists_affineOpen_sectionRatio_length_eq` — the chart of
  `Stacks.Chow.DenominatorStalk.exists_affineOpen_length_denominatorQuotientStalk_eq` with the
  same two clauses retained.
* `Stacks.Chow.exists_affineOpen_sectionRatio_sheafMultiplicity_sub_eq_finsum_componentOrd` — the
  coefficient identity of
  `Stacks.Chow.exists_affineOpen_sheafMultiplicity_sub_eq_finsum_componentOrd` with the same two
  clauses retained.

## Implementation notes

The ratio equation is stated at `Stacks.DenominatorIdeal.toK` and
`Stacks.DenominatorIdeal.sectionMap`, the spelling at which
`Stacks.DenominatorLocalRatio.exists_affineOpen_denominator` and the two colon-ideal
presentations of `Stacks.DenominatorMul` are stated; that is also the spelling at which
`Stacks.DenominatorCokernel.mem_nonZeroDivisors_of_trivialization` makes the numerator a
nonzerodivisor.

## References

* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite Topology TopologicalSpace
open Stacks.DenominatorIdeal (sectionMap toK)

universe u

namespace Stacks.Chow

/-! ### The chart with the basis and the ratio equation -/

/-- **The local ratio chart of [Stacks, Tag 02P0] with the trivializing basis and the ratio
equation retained.** This is
`Stacks.DenominatorMul.exists_affineOpen_denominator_presentations_of_isRegular` with the one
clause its conclusion drops added back: the equation `a · e = b · s` in `Γ(K_X(ℒ), V)` saying
that the ratio `a / b` really is the ratio representing `s` against the trivializing section
`e`. -/
theorem exists_affineOpen_sectionRatio_denominator_presentations (X : Scheme.{u}) (L : X.Modules)
    (s : AlgebraicGeometry.MeromorphicSection.{u, u} X.sheaf L)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) (x : X) :
    ∃ (V : X.Opens) (hxV : x ∈ V), IsAffineOpen V ∧
      ∃ (a b : Γ(X, V)) (e : Γ(L, V)),
        a ∈ nonZeroDivisors Γ(X, V) ∧ b ∈ nonZeroDivisors Γ(X, V) ∧
        Stacks.Divisors.IsStalkBasis L x (L.presheaf.germ V x hxV e) ∧
        (toK X L).val.app (op V) (a • e) = (sectionMap X L s).val.app (op V) b ∧
        (∀ f : Γ(X, V),
          Set.range (ConcreteCategory.hom
              ((Stacks.DenominatorIdeal.denominatorIdealι X L s).val.app
                (op (X.basicOpen f)))) =
            {g : Γ(X, X.basicOpen f) | ∃ v : Γ(X, X.basicOpen f),
              g * algebraMap Γ(X, V) Γ(X, X.basicOpen f) a =
                algebraMap Γ(X, V) Γ(X, X.basicOpen f) b * v}) ∧
        ∀ f : Γ(X, V),
          Set.range (ConcreteCategory.hom
              ((AlgebraicGeometry.denominatorIdealMul X L s).val.app
                (op (X.basicOpen f)))) =
            (fun y : Γ(X, X.basicOpen f) =>
                y • L.presheaf.map (homOfLE (X.basicOpen_le f)).op e) ''
              {y : Γ(X, X.basicOpen f) | ∃ u : Γ(X, X.basicOpen f),
                y * algebraMap Γ(X, V) Γ(X, X.basicOpen f) b =
                  algebraMap Γ(X, V) Γ(X, X.basicOpen f) a * u} := by
  obtain ⟨V, -, hxV, hVaff, ⟨θ⟩, b, hb, t, hbt⟩ :=
    Stacks.DenominatorLocalRatio.exists_affineOpen_denominator X L s hL ⊤ x (Opens.mem_top x)
  obtain ⟨a, ha0⟩ : ∃ a : Γ(X, V), Stacks.DenominatorColonIdeal.oTriv X L θ t = a := ⟨_, rfl⟩
  have ha : a ∈ nonZeroDivisors Γ(X, V) :=
    Stacks.DenominatorCokernel.mem_nonZeroDivisors_of_trivialization X L s hs
      (Stacks.DenominatorColonIdeal.oTriv X L θ) b hb t hbt a ha0
  have hta : t = a • Stacks.DenominatorMul.trivBasis X L θ := by
    rw [← ha0]
    exact Stacks.DenominatorMul.eq_oTriv_smul_oTrivBasis X L θ t
  have hbt' : (toK X L).val.app (op V) (a • Stacks.DenominatorMul.trivBasis X L θ) =
      (sectionMap X L s).val.app (op V) b :=
    (congrArg (fun y : (L.val.obj (op V) : Type u) => (toK X L).val.app (op V) y) hta).symm.trans
      hbt
  exact ⟨V, hxV, hVaff, a, b, Stacks.DenominatorMul.trivBasis X L θ, ha, hb,
    Stacks.DenominatorMul.isStalkBasis_germ_trivBasis X L θ x hxV, hbt',
    fun f => Stacks.DenominatorIdealQcoh.range_denominatorIdealι_app_basicOpen
      X L s hL hVaff θ hb hbt' f,
    fun f => Stacks.DenominatorMul.range_denominatorIdealMul_app_basicOpen
      X L s hL hVaff θ hb hbt' f⟩

/-! ### The two stalk lengths, with the basis and the ratio equation -/

/-- **The chart on which the lengths of the stalks of the two denominator quotients are the
colengths of the two colon ideals, with the trivializing basis and the ratio equation
retained.** This is
`Stacks.Chow.DenominatorStalk.exists_affineOpen_length_denominatorQuotientStalk_eq` obtained from
`Stacks.Chow.exists_affineOpen_sectionRatio_denominator_presentations` instead, so that the two
extra clauses survive into the conclusion. -/
theorem DenominatorStalk.exists_affineOpen_sectionRatio_length_eq {X : Scheme.{u}}
    (L F : X.Modules) (s : AlgebraicGeometry.MeromorphicSection.{u, u} X.sheaf L)
    [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : AlgebraicGeometry.IsRegularMeromorphicSection X.sheaf L s) [F.IsCoherent]
    (hF : AlgebraicGeometry.HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
    (x : X) :
    ∃ (V : X.Opens) (hxV : x ∈ V), IsAffineOpen V ∧ ∃ (a b : Γ(X, V)) (e : Γ(L, V)),
      a ∈ nonZeroDivisors Γ(X, V) ∧ b ∈ nonZeroDivisors Γ(X, V) ∧
      Stacks.Divisors.IsStalkBasis L x (L.presheaf.germ V x hxV e) ∧
      (toK X L).val.app (op V) (a • e) = (sectionMap X L s).val.app (op V) b ∧
      Module.length (X.presheaf.stalk x)
            ((Stacks.Chow.denominatorQuotientDecl L F s).presheaf.stalk x) =
          Module.length (X.presheaf.stalk x)
            (F.presheaf.stalk x ⧸
              (Ideal.denominatorIdeal (X.presheaf.germ V x hxV a) (X.presheaf.germ V x hxV b) •
                (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)))) ∧
        Module.length (X.presheaf.stalk x)
            ((DenominatorStalk.denominatorSectionQuotientDecl L F s hL hs hF hSupp).presheaf.stalk
              x) =
          Module.length (X.presheaf.stalk x)
            (F.presheaf.stalk x ⧸
              (Ideal.fractionalProductIdeal
                  (X.presheaf.germ V x hxV a) (X.presheaf.germ V x hxV b) •
                (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)))) := by
  obtain ⟨V, hxV, hVaff, a, b, e, ha, hb, hm, hbt, hι, hmul⟩ :=
    exists_affineOpen_sectionRatio_denominator_presentations X L s hL hs x
  exact ⟨V, hxV, hVaff, a, b, e, ha, hb, hm, hbt,
    DenominatorStalk.length_denominatorQuotientStalk hVaff hι hxV,
    DenominatorStalk.length_denominatorSectionQuotientStalk hL hs hF hSupp hVaff hmul hxV hm⟩

/-! ### The coefficient identity, with the basis and the ratio equation -/

/-- **The coefficient identity of part (4) of [Stacks, Tag 02SW] with the trivializing basis and
the ratio equation retained.** This is
`Stacks.Chow.exists_affineOpen_sheafMultiplicity_sub_eq_finsum_componentOrd` obtained from
`Stacks.Chow.DenominatorStalk.exists_affineOpen_sectionRatio_length_eq` instead, so that the
chart's trivializing section `e` and the equation `a · e = b · s` survive into the conclusion.
The hypotheses are exactly those of Tag 02SW together with the point data of part (4). -/
theorem exists_affineOpen_sectionRatio_sheafMultiplicity_sub_eq_finsum_componentOrd
    (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (L F : X.Modules) (s : AlgebraicGeometry.MeromorphicSection X.sheaf L)
    [F.IsCoherent] {k : ℤ}
    (hdim : schemeDeltaDimension C f ≤ ((k + 1 : ℤ) : EInt))
    (_hX : HasNoEmbeddedPoints X)
    (hF : HasNoEmbeddedAssociatedPoints F)
    (hSupp : (AlgebraicGeometry.SheafOfModules.moduleSheafOfModules F).supp = Set.univ)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    {ξ : X} (hξ : ξ ∈ denominatorBadLocus X L s)
    (hδ : relativeDimension C.dimensionFunction f ξ = k) :
    ∃ (V : X.Opens) (hξV : ξ ∈ V), IsAffineOpen V ∧ ∃ (a b : Γ(X, V)) (e : Γ(L, V)),
      Stacks.Divisors.IsStalkBasis L ξ (L.presheaf.germ V ξ hξV e) ∧
      (toK X L).val.app (op V) (a • e) = (sectionMap X L s).val.app (op V) b ∧
      X.presheaf.germ V ξ hξV a ∈ nonZeroDivisors (X.presheaf.stalk ξ) ∧
      X.presheaf.germ V ξ hξV b ∈ nonZeroDivisors (X.presheaf.stalk ξ) ∧
      sheafMultiplicity
            (@DenominatorStalk.denominatorSectionQuotientDecl X L F s
              (LocallyOfFiniteType.isLocallyNoetherian f) hL hs inferInstance hF hSupp) ξ -
          sheafMultiplicity (denominatorQuotientDecl L F s) ξ =
        ∑ᶠ η ∈ {η : X | η ∈ genericPoints X ∧ η ⤳ ξ ∧
            relativeDimension C.dimensionFunction f η = k + 1},
          sheafMultiplicity F η *
            (@componentOrdAt X (LocallyOfFiniteType.isLocallyNoetherian f) ξ η V hξV a -
              @componentOrdAt X (LocallyOfFiniteType.isLocallyNoetherian f) ξ η V hξV b) := by
  have hNoeth := LocallyOfFiniteType.isLocallyNoetherian f
  have hFq : F.IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  obtain ⟨V, hξV, hVaff, a, b, e, ha, hb, hm, hbt, hQ₁, hQ₂⟩ :=
    DenominatorStalk.exists_affineOpen_sectionRatio_length_eq L F s hL hs hF hSupp ξ
  obtain ⟨hfin, ha', hb', hdim1, hemb, hsupp, -⟩ :=
    StalkLocalSituation.lengthFormula_hypotheses C f F hdim hF hSupp
      (denominatorBadLocus_isClosed X L s hL hs)
      (denominatorBadLocus_isNowhereDense X L s hL hs) hVaff hξV hξ hδ ha hb
  refine ⟨V, hξV, hVaff, a, b, e, hm, hbt, ha', hb', ?_⟩
  have : Module.Finite (X.presheaf.stalk ξ) (F.presheaf.stalk ξ) := hfin
  have hnat : ∀ {m n : ℕ∞}, m = n → (m.toNat : ℤ) = n.toNat := fun h => h ▸ rfl
  refine Eq.trans (congrArg₂ (fun u v : ℤ => u - v) (hnat hQ₂) (hnat hQ₁)) ?_
  refine Eq.trans (Ideal.length_fractionalProduct_quotient_sub_length_denominator_quotient
    (X.presheaf.germ V ξ hξV a) (X.presheaf.germ V ξ hξV b) ha' hb' hdim1 hemb hsupp) ?_
  refine Eq.trans ?_ (finsum_minimalPrimes_eq_finsum_componentOrd C f hdim
    (denominatorBadLocus_isClosed X L s hL hs)
    (denominatorBadLocus_isNowhereDense X L s hL hs) hξ hδ (sheafMultiplicity F) hξV ha' hb')
  refine finsum_mem_congr rfl fun q _ => ?_
  exact congrArg
    (fun z : ℤ => z *
      (((Ring.ord ((X.presheaf.stalk ξ) ⧸ q.asIdeal)
          (Ideal.Quotient.mk q.asIdeal (X.presheaf.germ V ξ hξV a))).toNat : ℤ) -
        ((Ring.ord ((X.presheaf.stalk ξ) ⧸ q.asIdeal)
          (Ideal.Quotient.mk q.asIdeal (X.presheaf.germ V ξ hξV b))).toNat : ℤ)))
    (length_localizedModule_stalk_eq_sheafMultiplicity F q)

end Stacks.Chow

end
