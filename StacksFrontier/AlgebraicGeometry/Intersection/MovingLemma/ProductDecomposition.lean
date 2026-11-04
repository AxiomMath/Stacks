module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.CycleDecomposition
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.EtaleMultiplicityOne
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormulaMultiplicities.LocalIdealImage
public import StacksFrontier.Topology.Dimension.UnionDimension

/-!
# The display `C · X = [Z] + ∑ m_j [Z_j]` from étaleness

Let `C` and `X'` be closed subvarieties of a regular scheme `X` which is quasi-compact, let `Z`
be a closed subvariety of their intersection with generic point `ξ`, and suppose some morphism
`π : X' ⟶ S` locally of finite presentation is étale at the point of `X'` over `ξ` and cuts out
there, inside `X'`, no more than the subvariety `C` does. Then the coefficient of
`ξ` in the Tor-formula intersection product `[C] · [X']` is one, by the local form of Stacks
0B1J, and therefore

`[C] · [X'] = [Z] + ∑ m_j [Z_j]`

with the `Z_j` the closures of the remaining points of the support of the product, each with a
nonzero multiplicity. This is the step of the proof of Stacks 0B0E that reads "Because `π` is
étale at the point `x` of `Z`, we see that the closed subscheme `C ∩ X = π^{-1}(π(Z))` contains
`Z` with multiplicity 1 (local calculation omitted). Hence by Lemma 0B1J we conclude that
`C · X = [Z] + ∑ m_j[Z_j]`".

## Main results

* `AlgebraicGeometry.TorFormula.support_torFormulaCycleIntersectionProduct_single_single_subset`:
  the product of two prime cycles is supported on the intersection of the two subvarieties.
* `AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct_apply_eq_one_of_etaleAt`: the
  coefficient of `ξ` in the product is one, with the transversality hypothesis of Stacks 0B1J
  replaced by étaleness of `π` at `ξ`.
* `AlgebraicGeometry.TorFormula.exists_finset_torFormulaCycleIntersectionProduct_eq`: the
  displayed decomposition of the product.
* `AlgebraicGeometry.TorFormula.topologicalKrullDim_inter_closure_le_of_mem_support`: the
  dimension clause of Stacks 0B0E for a component of the product.

## Implementation notes

The hypotheses other than the étale ones are exactly those of
`AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct_apply_eq_one`, the local form of
Stacks 0B1J: the two subvarieties are indexed by their generic points `x` and `y`, the ideals
`I₀` and `J₀` are those of the components of the two subschemes through `ξ`, and the three
dimension conditions are what proper intersection and the dimension count of Varieties, Lemma
0A21 supply. Only the transversality hypothesis — that `𝒪_{X, ξ} ⧸ (I ⊔ J)` has length one — is
replaced, by the étale data; it is discharged through
`AlgebraicGeometry.TorFormula.length_quotient_sup_localIdealAt_eq_one_of_etaleAt_closedSubscheme`.

**The étale morphism is one of the subvariety, not of the ambient scheme.** An earlier form of
the two lemmas below took `π : X ⟶ S` étale at `ξ` on the ambient scheme together with the
set-theoretic containment `π (C) ⊆ closure {π ξ}`. That form cannot be instantiated in its own
application. In the proof of Stacks 0B0E the ambient scheme is `𝐏^N`, the only morphism available
is the composite projection `r_W`, and on `𝐏^N` that projection is an `𝔸^{N-n}`-bundle over its
image and therefore étale at no point whatsoever; it is étale at the chosen points only after
restriction to the nonsingular subvariety `X'`. So the hypotheses are taken in the shape
`AlgebraicGeometry.TorFormula.length_quotient_sup_localIdealAt_eq_one_of_etaleAt_closedSubscheme`
consumes them: a morphism `ι' : X' ⟶ X` surjective on stalks — a closed immersion, say — a point
`ζ` of `X'` over `ξ`, étaleness of `π : X' ⟶ S` at `ζ`, the containment `hker` of the ideal of
`X'` in `X` at `ξ` in the local ideal of `X'`'s own generic point, and the containment `hπle` of
the ideal cut out on `X'` by `π^{-1}(closure {π ζ})` in the one cut out there by `C`. The last is
the source's identity `C ∩ X = π^{-1}(π(Z))`, which the construction of `C` as the closure of
`π^{-1}(π(Z))` supplies. Taking `ι' = 𝟙` recovers the ambient form, whose `hπimg` yields `hπle`
through `AlgebraicGeometry.TorFormula.map_stalkMap_localIdealAt_le`, so nothing is lost.

Finiteness of the support of the product is not a hypothesis: a cycle has locally finite support
by definition, and on a quasi-compact space that is finite support, which is
`AlgebraicGeometry.TorFormula.finite_support_of_compactSpace`.

The delta-dimension bound `hb` is taken at the one pair `(x, y)` of generic points the statements
are about, not at every pair of points of `X`. The bound at every pair fails as soon as `X` has a
closed subvariety of dimension more than `k`, so on the `𝐏^N` of Stacks 0B0E, where `k` is the
dimension `d` of the subvariety being moved, it never holds; and it is not needed, the product
`AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct` being total in the bound.

## References

* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
* [Stacks Project, Tag 0B1J](https://stacks.math.columbia.edu/tag/0B1J)
* [Stacks Project, Tag 0B08](https://stacks.math.columbia.edu/tag/0B08)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.TorFormula

variable {X : Scheme.{u}}

/-- **The product of two prime cycles is supported on the intersection of the two
subvarieties.** Off that intersection every `Tor` sheaf of the two structure sheaves vanishes, so
every coefficient of the product does.

This is what locates the subvarieties `Z_j` of the display of Stacks 0B0E inside `C ∩ X`, which
is the step the source records as "Note that `C ∩ X = π^{-1}(π(Z))` set theoretically. Hence
`T_i ∩ Z_j ⊆ T_i ∩ π^{-1}(π(Z))`". -/
public theorem support_torFormulaCycleIntersectionProduct_single_single_subset [DecidableEq X]
    (CS : Stacks.Chow.ChowSituation.{u}) (f : X ⟶ CS.S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ) {x y : X}
    (hb : TorSupportBound CS f hX k x y) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) :
    Function.support (torFormulaCycleIntersectionProduct CS f hX k
        (Function.locallyFinsuppWithin.single x (1 : ℤ))
        (Function.locallyFinsuppWithin.single y (1 : ℤ)) : X → ℤ) ⊆
      closure ({x} : Set X) ∩ closure ({y} : Set X) := by
  intro z hz
  by_contra hnot
  refine hz ?_
  have heq : torFormulaCycleIntersectionProduct CS f hX k
      (Function.locallyFinsuppWithin.single x (1 : ℤ))
      (Function.locallyFinsuppWithin.single y (1 : ℤ)) =
      ((1 : ℤ) * (1 : ℤ)) • torFormulaSubvarietyProductTotal CS f hX k x y :=
    cycleIntersectionProduct_single_single _ x y 1 1
  rw [heq, torFormulaSubvarietyProductTotal_eq_of_bound CS f hX k hb]
  simpa using
    torSubvarietyProductOfBound_apply_eq_zero_of_notMem_inter CS f hX k hb d hd hnot

/-- **Stacks 0B1J, clause (1), with the transversality hypothesis supplied by étaleness along a
closed subscheme.** In the situation of
`AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct_apply_eq_one`, the length-one
hypothesis on `𝒪_{X, ξ} ⧸ (I ⊔ J)` is discharged by a morphism `π : X' ⟶ S` locally of finite
presentation which is étale at a point `ζ` of a scheme `X'` mapping to `X` by a morphism
surjective on stalks and carrying `ζ` to `ξ`.

The étale morphism is one of `X'`, not of the ambient `X`: in the application `X = 𝐏^N`, `X'` is
the nonsingular closed subvariety and `π` is the composite projection
`(r_{n+1} ∘ ⋯ ∘ r_N)|_{X'}`, on which the projection of `𝐏^N` is an `𝔸^{N-n}`-bundle and so
étale nowhere. See
`AlgebraicGeometry.TorFormula.length_quotient_sup_localIdealAt_eq_one_of_etaleAt_closedSubscheme`,
which is what discharges the hypothesis. -/
public theorem torFormulaCycleIntersectionProduct_apply_eq_one_of_etaleAt [DecidableEq X]
    (CS : Stacks.Chow.ChowSituation.{u}) (f : X ⟶ CS.S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ) {x y : X}
    (hb : TorSupportBound CS f hX k x y) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {ξ : X}
    (hz : Stacks.Chow.relativeDimension CS.dimensionFunction f ξ = k)
    (hzx : ξ ∈ closure ({x} : Set X)) (hzy : ξ ∈ closure ({y} : Set X))
    (I₀ J₀ : Ideal (X.presheaf.stalk ξ))
    (hI : localIdealAt x ξ ≤ I₀) (hJ : localIdealAt y ξ ≤ J₀)
    (hdimI : ringKrullDim (X.presheaf.stalk ξ ⧸ localIdealAt x ξ) =
      ringKrullDim (X.presheaf.stalk ξ ⧸ I₀))
    (hdimJ : ringKrullDim (X.presheaf.stalk ξ ⧸ localIdealAt y ξ) =
      ringKrullDim (X.presheaf.stalk ξ ⧸ J₀))
    (hproper : ringKrullDim (X.presheaf.stalk ξ) ≤
      ringKrullDim (X.presheaf.stalk ξ ⧸ I₀) + ringKrullDim (X.presheaf.stalk ξ ⧸ J₀))
    {X' S : Scheme.{u}} (ι' : X' ⟶ X) [SurjectiveOnStalks ι'] (π : X' ⟶ S)
    [LocallyOfFinitePresentation π] {ζ : X'} (hζ : ι'.base ζ = ξ) (hπ : EtaleAt π ζ)
    (hker : RingHom.ker (ι'.stalkMap ζ).hom ≤ localIdealAt y (ι'.base ζ))
    (hπle : Ideal.map (π.stalkMap ζ).hom (localIdealAt (π.base ζ) (π.base ζ)) ≤
      Ideal.map (ι'.stalkMap ζ).hom (localIdealAt x (ι'.base ζ))) :
    torFormulaCycleIntersectionProduct CS f hX k
        (Function.locallyFinsuppWithin.single x (1 : ℤ))
        (Function.locallyFinsuppWithin.single y (1 : ℤ)) ξ = 1 := by
  subst hζ
  exact torFormulaCycleIntersectionProduct_apply_eq_one CS f hX k hb d hd hz hzx hzy I₀ J₀ hI hJ
    (length_quotient_sup_localIdealAt_eq_one_of_etaleAt_closedSubscheme ι' π hπ hzx hzy hker hπle)
    hdimI hdimJ hproper

/-- **The display `C · X = [Z] + ∑ m_j [Z_j]` of Stacks 0B0E.** Under the hypotheses of
`AlgebraicGeometry.TorFormula.torFormulaCycleIntersectionProduct_apply_eq_one_of_etaleAt` on a
quasi-compact scheme, the intersection product of the two prime cycles is the prime cycle of
`closure {ξ}` plus a finite integer combination of prime cycles of the remaining points of its
support, each with a nonzero multiplicity. -/
public theorem exists_finset_torFormulaCycleIntersectionProduct_eq [DecidableEq X]
    [CompactSpace X] (CS : Stacks.Chow.ChowSituation.{u}) (f : X ⟶ CS.S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ) {x y : X}
    (hb : TorSupportBound CS f hX k x y) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {ξ : X}
    (hz : Stacks.Chow.relativeDimension CS.dimensionFunction f ξ = k)
    (hzx : ξ ∈ closure ({x} : Set X)) (hzy : ξ ∈ closure ({y} : Set X))
    (I₀ J₀ : Ideal (X.presheaf.stalk ξ))
    (hI : localIdealAt x ξ ≤ I₀) (hJ : localIdealAt y ξ ≤ J₀)
    (hdimI : ringKrullDim (X.presheaf.stalk ξ ⧸ localIdealAt x ξ) =
      ringKrullDim (X.presheaf.stalk ξ ⧸ I₀))
    (hdimJ : ringKrullDim (X.presheaf.stalk ξ ⧸ localIdealAt y ξ) =
      ringKrullDim (X.presheaf.stalk ξ ⧸ J₀))
    (hproper : ringKrullDim (X.presheaf.stalk ξ) ≤
      ringKrullDim (X.presheaf.stalk ξ ⧸ I₀) + ringKrullDim (X.presheaf.stalk ξ ⧸ J₀))
    {X' S : Scheme.{u}} (ι' : X' ⟶ X) [SurjectiveOnStalks ι'] (π : X' ⟶ S)
    [LocallyOfFinitePresentation π] {ζ : X'} (hζ : ι'.base ζ = ξ) (hπ : EtaleAt π ζ)
    (hker : RingHom.ker (ι'.stalkMap ζ).hom ≤ localIdealAt y (ι'.base ζ))
    (hπle : Ideal.map (π.stalkMap ζ).hom (localIdealAt (π.base ζ) (π.base ζ)) ≤
      Ideal.map (ι'.stalkMap ζ).hom (localIdealAt x (ι'.base ζ))) :
    ∃ T : Finset X,
      (↑T : Set X) ⊆ Function.support (torFormulaCycleIntersectionProduct CS f hX k
          (Function.locallyFinsuppWithin.single x (1 : ℤ))
          (Function.locallyFinsuppWithin.single y (1 : ℤ))) ∧
        ξ ∉ T ∧
        (∀ w ∈ T, torFormulaCycleIntersectionProduct CS f hX k
          (Function.locallyFinsuppWithin.single x (1 : ℤ))
          (Function.locallyFinsuppWithin.single y (1 : ℤ)) w ≠ 0) ∧
        torFormulaCycleIntersectionProduct CS f hX k
            (Function.locallyFinsuppWithin.single x (1 : ℤ))
            (Function.locallyFinsuppWithin.single y (1 : ℤ)) =
          Function.locallyFinsuppWithin.single ξ (1 : ℤ) +
            ∑ w ∈ T, torFormulaCycleIntersectionProduct CS f hX k
                (Function.locallyFinsuppWithin.single x (1 : ℤ))
                (Function.locallyFinsuppWithin.single y (1 : ℤ)) w •
              Function.locallyFinsuppWithin.single w (1 : ℤ) :=
  AlgebraicCycle.exists_finset_eq_single_add_sum _ (finite_support_of_compactSpace _)
    (torFormulaCycleIntersectionProduct_apply_eq_one_of_etaleAt CS f hX k hb d hd hz hzx hzy
      I₀ J₀ hI hJ hdimI hdimJ hproper ι' π hζ hπ hker hπle)

/-- **The dimension clause of Stacks 0B0E, for a component of the product.** Let the
scheme-theoretic intersection of the two subvarieties lie inside `Z ∪ E` with `Z` and `E` closed.
Then for every component `W = closure {w}` of the product and every closed `T`,

`dim (T ∩ W) ≤ max (dim (T ∩ Z)) (dim E)`.

With `T = T_i`, `Z` the subvariety being moved and `E = E_i` the error term of Stacks 0B1R, this
is the inequality `dim (Z_j ∩ T_i) ≤ dim (Z ∩ T_i)` of the source, given the bound on
`dim E_i`. -/
public theorem topologicalKrullDim_inter_closure_le_of_mem_support [DecidableEq X]
    (CS : Stacks.Chow.ChowSituation.{u}) (f : X ⟶ CS.S) [LocallyOfFiniteType f]
    [IsLocallyNoetherian X] (hX : IsRegular X) (k : ℤ) {x y : X}
    (hb : TorSupportBound CS f hX k x y) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) {T Z E : Set X} (hT : IsClosed T)
    (hZ : IsClosed Z) (hE : IsClosed E)
    (hsub : closure ({x} : Set X) ∩ closure ({y} : Set X) ⊆ Z ∪ E)
    {w : X} (hw : w ∈ Function.support (torFormulaCycleIntersectionProduct CS f hX k
      (Function.locallyFinsuppWithin.single x (1 : ℤ))
      (Function.locallyFinsuppWithin.single y (1 : ℤ)) : X → ℤ)) :
    topologicalKrullDim ↥(T ∩ closure ({w} : Set X)) ≤
      max (topologicalKrullDim ↥(T ∩ Z)) (topologicalKrullDim ↥E) := by
  have hwmem : w ∈ closure ({x} : Set X) ∩ closure ({y} : Set X) :=
    support_torFormulaCycleIntersectionProduct_single_single_subset CS f hX k hb d hd hw
  have hwcl : closure ({w} : Set X) ⊆ closure ({x} : Set X) ∩ closure ({y} : Set X) :=
    (isClosed_closure.inter isClosed_closure).closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hwmem)
  refine topologicalKrullDim_inter_le_max_of_subset_union hT isClosed_closure hZ hE ?_
  exact fun z hz => hsub (hwcl hz.2)

end AlgebraicGeometry.TorFormula

end
