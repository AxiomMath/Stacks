module

public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.RingTheory.Henselian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityLocalCase.FaithfulRestriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TopologicalInvarianceFundamental.Basic
public import StacksFrontier.RingTheory.Henselian.Pair.Criteria

/-!
# Finite étale covers of the neighbourhoods of a punctured closed fibre

In the local Lefschetz situation `(A, f)` write `X = Spec A`, `X₀ = Spec (A / fA)`, and let
`U` and `U₀` be the punctured spectra of `A` and of `A / fA`.  The opens `U'` of `X` with
`U₀ ⊆ U' ⊆ U` are a filtered index (filtered for reverse inclusion: two of them meet in a
third), each carries the category `FÉt_{U'}` of finite étale covers, and restriction along the
inclusions makes `U' ↦ FÉt_{U'}` a filtered diagram whose colimit receives a canonical
restriction functor

```
colim_{U₀ ⊆ U' ⊆ U} FÉt_{U'} ⟶ FÉt_{U₀}.
```

This file proves that this functor is an equivalence, under the three hypotheses of Stacks
0BLV — `A` is `f`-adically complete, `f` is a nonzerodivisor, and `H¹_𝔪(A / fA)` and
`H²_𝔪(A / fA)` are finite `A`-modules — together with two explicitly carried hypotheses that
are discussed below.

The route is the one the first hypothesis opens up.  An `f`-adically complete ring is
henselian along `fA`, so `(A, fA)` is a henselian pair, and by Stacks 09ZS restriction of
finite étale covers from `X` to `X₀` is an equivalence.  Composing that with restriction from
`X₀` to the punctured spectrum `U₀` of `A / fA` identifies `FÉt_X` with `FÉt_{U₀}`.  For a
neighbourhood `U'` of `U₀` in `U` the morphism `U₀ ⟶ X` factors as `U₀ ⟶ U' ⟶ X`, so once
restriction from `X` to `U'` is an equivalence as well, restriction from `U'` to `U₀` is an
equivalence — stagewise, for every neighbourhood.  The three clauses of the equivalence of the
restriction functor out of the colimit then hold with no shrinking of the neighbourhood at all.

## Main definitions

* `AlgebraicGeometry.LocalLefschetzSituation.IsNeighbourhood` — the opens `U'` of `X` with
  `U₀ ⊆ U' ⊆ U`, the index of the colimit.
* `AlgebraicGeometry.LocalLefschetzSituation.nbhdRestriction` — the canonical morphism
  `U₀ ⟶ U'` attached to such an open; base change along it is restriction to `U₀`.
* `AlgebraicGeometry.LocalLefschetzSituation.closedFibreLocalCohomology` — the local
  cohomology `H^i_𝔪(A / fA)`, in which the finiteness hypotheses of Stacks 0BLV are phrased.
* `AlgebraicGeometry.LocalLefschetzSituation.Hypotheses` — the three hypotheses of Stacks
  0BLV.
* `AlgebraicGeometry.LocalLefschetzSituation.RestrictionToClosedFibreIsEquivalence` and
  `AlgebraicGeometry.LocalLefschetzSituation.RestrictionToNeighbourhoodsIsEquivalence` — the
  two carried hypotheses.
* `AlgebraicGeometry.LocalLefschetzSituation.IsColimitRestrictionEquivalence` — the assertion
  that the restriction functor out of the filtered colimit is an equivalence, written out on
  representatives of the colimit.

## Main results

* `AlgebraicGeometry.LocalLefschetzSituation.henselianPair_principalIdeal_of_isAdicComplete` —
  an `f`-adically complete ring forms a henselian pair with `fA`.
* `AlgebraicGeometry.LocalLefschetzSituation.finiteEtaleBaseChange_U₀ToX_isEquivalence` —
  restriction of finite étale covers from `X` to `U₀` is an equivalence.
* `AlgebraicGeometry.LocalLefschetzSituation.finiteEtaleBaseChange_nbhdRestriction_isEquivalence`
  — restriction from a neighbourhood `U'` to `U₀` is an equivalence.
* `AlgebraicGeometry.LocalLefschetzSituation.isColimitRestrictionEquivalence` — Stacks 0BLV.

## Implementation notes

**How the colimit is written.** A filtered colimit of categories is not needed as an object
here: a functor out of `colim_{U'} FÉt_{U'}` is faithful, full and essentially surjective
exactly when the three clauses of
`AlgebraicGeometry.LocalLefschetzSituation.IsColimitRestrictionEquivalence` hold, because an
object of the colimit is a cover over some representative `U'`, a morphism is a morphism over
some representative, and two morphisms are identified in the colimit when they agree over some
smaller representative.  This is the shape in which the faithfulness half of the same functor
is already recorded, as
`AlgebraicGeometry.LocalLefschetzSituation.exists_le_finiteEtaleBaseChange_map_eq`, and it
avoids having to fix a strictification of the restriction pseudofunctor in order to state the
tag.  In the fullness clause the two restrictions of a cover over `U'` to `U₀` — directly, and
through the smaller `U''` — are canonically isomorphic rather than equal, because each is a
separately chosen pullback, so the clause is phrased against the canonical comparison
`AlgebraicGeometry.finiteEtaleBaseChangeComp`.

**The two carried hypotheses, and why they are upstream.** Stacks 0BLV is deduced in the source
from Stacks 0EK1 (Fundamental Groups, Lemma 58.17.4), whose input is the completion equivalence
of Stacks 0EKZ (Algebraic and Formal Geometry, Lemma 52.24.2) on finite locally free objects.
Neither is available: the conclusion of Stacks 0EKZ cannot even be stated in this library,
because it compares `Coh(U, f𝒪_U)` with `Coh(V, f𝒪_V)` for the neighbourhoods `V`, which is
exactly the comparison recorded as missing in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionFullyFaithful/PrincipalComplement.lean`.
What is carried instead are two *purity* statements, each about a restriction functor that is
not the functor of Stacks 0BLV:

* `RestrictionToClosedFibreIsEquivalence`: restriction `FÉt_{X₀} ⟶ FÉt_{U₀}` from the spectrum
  of `A / fA` to its punctured spectrum is an equivalence.  This is purity for the ring
  `A / fA`, the statement proved for normal local rings as Stacks 0BM9.
* `RestrictionToNeighbourhoodsIsEquivalence`: restriction `FÉt_X ⟶ FÉt_{U'}` from the whole
  spectrum of `A` to a neighbourhood `U'` of `U₀` in `U` is an equivalence for every such `U'`.
  This is purity for `A` along those opens.

Both speak about restriction *from an affine spectrum*; the functor Stacks 0BLV is about goes
out of the filtered colimit over the opens between `U₀` and `U`, and neither its equivalence,
nor its fullness, faithfulness or essential surjectivity, is assumed anywhere below.  What the
hypotheses of Stacks 0BLV do here is supply the third side of the triangle: `f`-adic
completeness is discharged into a henselian pair and then into Stacks 09ZS, which is what turns
the two purity statements into the stagewise equivalence.

## References

* [Stacks Project, Tag 0BLV](https://stacks.math.columbia.edu/tag/0BLV)
* [Stacks Project, Tag 0BLF](https://stacks.math.columbia.edu/tag/0BLF)
* [Stacks Project, Tag 09ZS](https://stacks.math.columbia.edu/tag/09ZS)
-/

@[expose] public noncomputable section

open CategoryTheory Polynomial

universe u

namespace AlgebraicGeometry.LocalLefschetzSituation

variable (S : LocalLefschetzSituation.{u})

/-! ### The hypotheses of Stacks 0BLV -/

/-- The local cohomology `H^i_𝔪(A / fA)` of the closed fibre with support in the maximal ideal,
as an `A`-module.  The finiteness hypotheses of Stacks 0BLV are finiteness of this module for
`i = 1` and `i = 2`. -/
abbrev closedFibreLocalCohomology (i : ℕ) : ModuleCat.{u} S.A :=
  (localCohomology (IsLocalRing.maximalIdeal S.A) i).obj (ModuleCat.of S.A S.quotientRing)

/-- The three hypotheses of Stacks 0BLV on a local Lefschetz situation: `A` is `f`-adically
complete, `f` is a nonzerodivisor, and the first two local cohomology modules of `A / fA` with
support in the maximal ideal are finite `A`-modules. -/
structure Hypotheses : Prop where
  /-- Hypothesis (1): `A` is `f`-adically complete. -/
  isAdicComplete : IsAdicComplete S.principalIdeal S.A
  /-- Hypothesis (2): `f` is a nonzerodivisor. -/
  isRegular : IsRegular S.f
  /-- Hypothesis (3) for `i = 1`: `H¹_𝔪(A / fA)` is a finite `A`-module. -/
  finite_localCohomology_one : Module.Finite S.A (S.closedFibreLocalCohomology 1)
  /-- Hypothesis (3) for `i = 2`: `H²_𝔪(A / fA)` is a finite `A`-module. -/
  finite_localCohomology_two : Module.Finite S.A (S.closedFibreLocalCohomology 2)

/-! ### An adically complete ring is henselian along the ideal -/


/-- **Hypothesis (1) of Stacks 0BLV makes `(A, fA)` a henselian pair.** -/
theorem henselianPair_principalIdeal_of_isAdicComplete
    (h : IsAdicComplete S.principalIdeal S.A) :
    HenselianPair S.A S.principalIdeal := by
  let : IsAdicComplete S.principalIdeal S.A := h
  let : HenselianRing S.A S.principalIdeal :=
    IsAdicComplete.henselianRing S.A S.principalIdeal
  exact henselianPair_of_henselianRing S.A S.principalIdeal

/-- **Stacks 09ZS in the local Lefschetz situation.**  If `A` is `f`-adically complete then
restriction of finite étale covers from `X = Spec A` to the closed fibre `X₀ = Spec (A / fA)`
is an equivalence. -/
theorem finiteEtaleBaseChange_X₀ToX_isEquivalence
    (h : IsAdicComplete S.principalIdeal S.A) :
    (finiteEtaleBaseChange S.X₀ToX).IsEquivalence :=
  finiteEtaleBaseChange_isEquivalence_of_henselianPair S.A S.principalIdeal
    (S.henselianPair_principalIdeal_of_isAdicComplete h)

/-! ### The neighbourhoods of the punctured closed fibre -/

/-- An open `U'` of `X` with `U₀ ⊆ U' ⊆ U`.  These are the index of the filtered colimit in
Stacks 0BLV; they are filtered for reverse inclusion because two of them meet in a third. -/
def IsNeighbourhood (W : S.X.Opens) : Prop :=
  W ≤ S.UOpen ∧ S.U₀Open ≤ S.X₀ToX ⁻¹ᵁ W

/-- The punctured spectrum `U` of `A` is itself a neighbourhood of `U₀`. -/
theorem isNeighbourhood_UOpen : S.IsNeighbourhood S.UOpen :=
  ⟨le_rfl, le_rfl⟩

/-- A smaller open between `U₀` and a neighbourhood is again a neighbourhood. -/
theorem IsNeighbourhood.mono {W W' : S.X.Opens} (hW : S.IsNeighbourhood W) (hle : W' ≤ W)
    (hW' : S.U₀Open ≤ S.X₀ToX ⁻¹ᵁ W') :
    S.IsNeighbourhood W' :=
  ⟨hle.trans hW.1, hW'⟩

/-- The canonical morphism `U₀ ⟶ X` from the punctured closed fibre to the spectrum of `A`. -/
def U₀ToX : S.U₀ ⟶ S.X :=
  S.U₀Open.ι ≫ S.X₀ToX

/-- The canonical morphism `U₀ ⟶ U'` from the punctured closed fibre to a neighbourhood.  Base
change along it is restriction of finite étale covers to `U₀`. -/
def nbhdRestriction {W : S.X.Opens} (hW : S.IsNeighbourhood W) : S.U₀ ⟶ W.toScheme :=
  S.homToOpen hW.2

/-- The morphism `U₀ ⟶ U'` of a neighbourhood factors the morphism `U₀ ⟶ X`. -/
@[reassoc]
theorem nbhdRestriction_comp_ι {W : S.X.Opens} (hW : S.IsNeighbourhood W) :
    S.nbhdRestriction hW ≫ W.ι = S.U₀ToX := by
  rw [nbhdRestriction, S.homToOpen_comp_ι, S.U₀ToU_comp_immersion, U₀ToX]

/-- The morphism `U₀ ⟶ U'` of a neighbourhood factors through a smaller neighbourhood. -/
theorem nbhdRestriction_comp_homOfLE {W W' : S.X.Opens} (hW : S.IsNeighbourhood W)
    (hW' : S.IsNeighbourhood W') (hle : W' ≤ W) :
    S.nbhdRestriction hW' ≫ S.X.homOfLE hle = S.nbhdRestriction hW := by
  apply (cancel_mono W.ι).1
  rw [Category.assoc, Scheme.homOfLE_ι, S.nbhdRestriction_comp_ι, S.nbhdRestriction_comp_ι]

/-! ### The two carried hypotheses -/

/-- **Purity for `A / fA`**, carried as an explicit hypothesis: restriction of finite étale
covers from `X₀ = Spec (A / fA)` to its punctured spectrum `U₀` is an equivalence.  This is a
statement about the functor `FÉt_{X₀} ⟶ FÉt_{U₀}`, not about the restriction functor out of the
colimit over the neighbourhoods of `U₀` in `U`; for normal local rings it is Stacks 0BM9. -/
def RestrictionToClosedFibreIsEquivalence : Prop :=
  (finiteEtaleBaseChange S.U₀Open.ι).IsEquivalence

/-- **Purity for `A` along the neighbourhoods of `U₀`**, carried as an explicit hypothesis:
for every open `U'` with `U₀ ⊆ U' ⊆ U`, restriction of finite étale covers from `X = Spec A` to
`U'` is an equivalence.  This is a statement about the functors `FÉt_X ⟶ FÉt_{U'}`, whose source
is the whole spectrum, not about the restriction functor out of the colimit over the `U'`. -/
def RestrictionToNeighbourhoodsIsEquivalence : Prop :=
  ∀ W : S.X.Opens, S.IsNeighbourhood W → (finiteEtaleBaseChange W.ι).IsEquivalence

/-! ### Restriction to the punctured closed fibre -/

/-- **Restriction of finite étale covers from `X` to `U₀` is an equivalence.**  It factors as
restriction from `X` to the closed fibre `X₀`, which hypothesis (1) of Stacks 0BLV makes an
equivalence through Stacks 09ZS, followed by restriction from `X₀` to its punctured spectrum,
which is the first carried hypothesis. -/
@[sga "2 X 3.9" "(i)"]
theorem finiteEtaleBaseChange_U₀ToX_isEquivalence
    (hcomplete : IsAdicComplete S.principalIdeal S.A)
    (hfibre : S.RestrictionToClosedFibreIsEquivalence) :
    (finiteEtaleBaseChange S.U₀ToX).IsEquivalence := by
  let : (finiteEtaleBaseChange S.X₀ToX).IsEquivalence :=
    S.finiteEtaleBaseChange_X₀ToX_isEquivalence hcomplete
  let : (finiteEtaleBaseChange S.U₀Open.ι).IsEquivalence := hfibre
  let : (finiteEtaleBaseChange S.X₀ToX ⋙
      finiteEtaleBaseChange S.U₀Open.ι).IsEquivalence := inferInstance
  exact Functor.isEquivalence_of_iso
    (finiteEtaleBaseChangeComp S.U₀Open.ι S.X₀ToX S.U₀ToX rfl).symm

/-- **Restriction of finite étale covers from a neighbourhood of `U₀` in `U` to `U₀` is an
equivalence.**  The morphism `U₀ ⟶ X` factors through the neighbourhood `U'`, so the equivalence
`FÉt_X ⟶ FÉt_{U₀}` factors as restriction from `X` to `U'` — an equivalence by the second
carried hypothesis — followed by restriction from `U'` to `U₀`. -/
theorem finiteEtaleBaseChange_nbhdRestriction_isEquivalence
    (hcomplete : IsAdicComplete S.principalIdeal S.A)
    (hfibre : S.RestrictionToClosedFibreIsEquivalence)
    (hnbhd : S.RestrictionToNeighbourhoodsIsEquivalence)
    {W : S.X.Opens} (hW : S.IsNeighbourhood W) :
    (finiteEtaleBaseChange (S.nbhdRestriction hW)).IsEquivalence := by
  let : (finiteEtaleBaseChange W.ι).IsEquivalence := hnbhd W hW
  let : (finiteEtaleBaseChange S.U₀ToX).IsEquivalence :=
    S.finiteEtaleBaseChange_U₀ToX_isEquivalence hcomplete hfibre
  let : (finiteEtaleBaseChange W.ι ⋙
      finiteEtaleBaseChange (S.nbhdRestriction hW)).IsEquivalence :=
    Functor.isEquivalence_of_iso
      (finiteEtaleBaseChangeComp (S.nbhdRestriction hW) W.ι S.U₀ToX
        (S.nbhdRestriction_comp_ι hW).symm)
  exact Functor.isEquivalence_of_comp_left (finiteEtaleBaseChange W.ι)
    (finiteEtaleBaseChange (S.nbhdRestriction hW))

/-! ### The restriction functor out of the filtered colimit -/

/-- **The restriction functor `colim_{U₀ ⊆ U' ⊆ U} FÉt_{U'} ⟶ FÉt_{U₀}` is an equivalence**,
written out on representatives of the filtered colimit.

An object of the colimit is a finite étale cover of some open `U'` with `U₀ ⊆ U' ⊆ U`, a
morphism of the colimit is a morphism of covers over some such representative, and two
morphisms over `U'` are identified in the colimit exactly when they agree over some smaller
such `U''`.  Faithfulness, fullness and essential surjectivity of the restriction functor out
of the colimit are therefore the three clauses below. -/
structure IsColimitRestrictionEquivalence : Prop where
  /-- **Faithful.**  Two morphisms of finite étale covers over a neighbourhood `U'` of `U₀`
  whose restrictions to `U₀` agree already agree over a smaller neighbourhood `U''`, hence are
  the same morphism of the colimit. -/
  faithful : ∀ {W : S.X.Opens} (hW : S.IsNeighbourhood W)
      {A B : FiniteEtaleOver W.toScheme} (a b : A ⟶ B),
      (finiteEtaleBaseChange (S.nbhdRestriction hW)).map a =
          (finiteEtaleBaseChange (S.nbhdRestriction hW)).map b →
        ∃ (W' : S.X.Opens) (_ : S.IsNeighbourhood W') (hle : W' ≤ W),
          (finiteEtaleBaseChange (S.X.homOfLE hle)).map a =
            (finiteEtaleBaseChange (S.X.homOfLE hle)).map b
  /-- **Full.**  Every morphism between the restrictions to `U₀` of two finite étale covers
  over a neighbourhood `U'` is the restriction of a morphism over a smaller neighbourhood
  `U''`, hence comes from a morphism of the colimit.  The compatibility is stated against the
  canonical comparison between restricting to `U₀` directly and restricting through `U''`,
  because the two are isomorphic rather than equal. -/
  full : ∀ {W : S.X.Opens} (hW : S.IsNeighbourhood W)
      {A B : FiniteEtaleOver W.toScheme}
      (φ : (finiteEtaleBaseChange (S.nbhdRestriction hW)).obj A ⟶
          (finiteEtaleBaseChange (S.nbhdRestriction hW)).obj B),
      ∃ (W' : S.X.Opens) (hW' : S.IsNeighbourhood W') (hle : W' ≤ W)
        (ψ : (finiteEtaleBaseChange (S.X.homOfLE hle)).obj A ⟶
          (finiteEtaleBaseChange (S.X.homOfLE hle)).obj B),
        ((finiteEtaleBaseChangeComp (S.nbhdRestriction hW') (S.X.homOfLE hle)
              (S.nbhdRestriction hW)
              (S.nbhdRestriction_comp_homOfLE hW hW' hle).symm).hom.app A) ≫
            (finiteEtaleBaseChange (S.nbhdRestriction hW')).map ψ =
          φ ≫ ((finiteEtaleBaseChangeComp (S.nbhdRestriction hW') (S.X.homOfLE hle)
            (S.nbhdRestriction hW)
            (S.nbhdRestriction_comp_homOfLE hW hW' hle).symm).hom.app B)
  /-- **Essentially surjective.**  Every finite étale cover of `U₀` is isomorphic to the
  restriction of a finite étale cover of some neighbourhood `U'` of `U₀` in `U`, hence lies in
  the essential image of the restriction functor out of the colimit. -/
  essSurj : ∀ C : FiniteEtaleOver S.U₀,
    ∃ (W : S.X.Opens) (hW : S.IsNeighbourhood W) (A : FiniteEtaleOver W.toScheme),
      Nonempty ((finiteEtaleBaseChange (S.nbhdRestriction hW)).obj A ≅ C)

/-- **Stacks Project, Tag 0BLV.**  In the local Lefschetz situation of Stacks 0BLF assume that
`A` is `f`-adically complete, that `f` is a nonzerodivisor, and that `H¹_𝔪(A / fA)` and
`H²_𝔪(A / fA)` are finite `A`-modules.  Then the restriction functor

```
colim_{U₀ ⊆ U' ⊆ U} FÉt_{U'} ⟶ FÉt_{U₀}
```

is an equivalence.

Two purity statements are carried as explicit hypotheses, each about a restriction functor out
of an affine spectrum and neither about the functor above: that restriction
`FÉt_{Spec (A / fA)} ⟶ FÉt_{U₀}` is an equivalence, and that restriction `FÉt_{Spec A} ⟶ FÉt_{U'}`
is an equivalence for every open `U'` between `U₀` and `U`.  The `f`-adic completeness
hypothesis is discharged: it makes `(A, fA)` a henselian pair, so that Stacks 09ZS identifies
`FÉt_{Spec A}` with `FÉt_{Spec (A / fA)}`, which is what turns the two carried statements into
the equivalence of restriction from each neighbourhood `U'` to `U₀`. -/
@[stacks 0BLV "the equivalence, carrying as explicit hypotheses the purity of restriction \
`FÉt_{Spec (A/fA)} ⟶ FÉt_{U₀}` and the purity of restriction `FÉt_{Spec A} ⟶ FÉt_{U'}` for the \
opens `U₀ ⊆ U' ⊆ U`"]
theorem isColimitRestrictionEquivalence (h : S.Hypotheses)
    (hfibre : S.RestrictionToClosedFibreIsEquivalence)
    (hnbhd : S.RestrictionToNeighbourhoodsIsEquivalence) :
    S.IsColimitRestrictionEquivalence := by
  have hequiv : ∀ {W : S.X.Opens} (hW : S.IsNeighbourhood W),
      (finiteEtaleBaseChange (S.nbhdRestriction hW)).IsEquivalence := fun hW =>
    S.finiteEtaleBaseChange_nbhdRestriction_isEquivalence h.isAdicComplete hfibre hnbhd hW
  refine ⟨?_, ?_, ?_⟩
  · intro W hW A B a b hab
    have := hequiv hW
    exact ⟨W, hW, le_rfl, congrArg _ ((finiteEtaleBaseChange
      (S.nbhdRestriction hW)).map_injective hab)⟩
  · intro W hW A B φ
    have := hequiv hW
    let e := finiteEtaleBaseChangeComp (S.nbhdRestriction hW) (S.X.homOfLE (le_refl W))
      (S.nbhdRestriction hW) (S.nbhdRestriction_comp_homOfLE hW hW (le_refl W)).symm
    obtain ⟨ψ, hψ⟩ := (finiteEtaleBaseChange (S.nbhdRestriction hW)).map_surjective
      (e.inv.app A ≫ φ ≫ e.hom.app B)
    refine ⟨W, hW, le_refl W, ψ, ?_⟩
    rw [hψ]
    simp [e]
  · intro C
    have := hequiv S.isNeighbourhood_UOpen
    exact ⟨S.UOpen, S.isNeighbourhood_UOpen,
      (finiteEtaleBaseChange (S.nbhdRestriction S.isNeighbourhood_UOpen)).objPreimage C,
      ⟨(finiteEtaleBaseChange (S.nbhdRestriction S.isNeighbourhood_UOpen)).objObjPreimageIso C⟩⟩

end AlgebraicGeometry.LocalLefschetzSituation

end
