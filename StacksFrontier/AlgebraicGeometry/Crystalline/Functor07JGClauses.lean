module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsQuasiCoherentToPairs

/-!
# The three clauses of [Stacks, Tag 07JH], each reduced to the reduction functor

[Stacks, Proposition 60.17.4, Tag 07JH] says that the functor
`Crystalline.GlobalCrystallineSituation.SmallSite.functor07JG` of [Stacks, Lemma 60.17.3,
Tag 07JG] is an equivalence of categories, that is: faithful, full and essentially surjective.
That functor is a composite

`functor07JG R = R.functor ⋙ firstOrderCrystalsToPairs`,

the reduction of a crystal in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)` to its first-order
comparison datum over `D`, followed by the algebraic functor into the pairs `(M, ∇)`.

For the **faithfulness** clause, `faithful_functor07JG_iff` of
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystalsQuasiCoherentToPairs.lean` already says that
all the content sits in the first factor: the clause holds for the composite if and only if it
holds for `R.functor`, with no hypotheses, because the second factor is unconditionally faithful.

This module proves the same for the other two clauses.  There is no analogue of
`firstOrderCrystalsToPairs_faithful` for them — fullness of the second factor needs the
hypothesis `hinj` and essential surjectivity needs `hlift`, both of
`Crystalline.firstOrderCrystalsToPairs_isEquivalence` — so the reductions carry those
hypotheses, and are stated so that it is visible which clause costs which.

## Main results

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`, except the
general category-theoretic lemma `Crystalline.essSurj_of_essSurj_comp`.

* `full_functor07JG_imp` — **the fullness clause of [Stacks, Tag 07JH] implies fullness of the
  reduction functor, with no hypotheses.**  This is the exact analogue of the easy half of
  `faithful_functor07JG_iff`, and it is unconditional for the same reason: the second factor is
  faithful outright.
* `full_functor07JG_of_full` — conversely, fullness of the reduction functor gives the clause,
  given `hinj`.
* `full_functor07JG_iff` — **the fullness clause is equivalent to fullness of the reduction
  functor**, given `hinj` and nothing else.  This is the `Functor.Full` analogue of
  `faithful_functor07JG_iff` that the library did not have.
* `essSurj_functor07JG_of_essSurj` — the essential-surjectivity clause from essential
  surjectivity of the reduction functor, given `hlift`.
* `essSurj_functor07JG_imp` — the converse, given `hinj` (which makes the second factor fully
  faithful, its faithfulness being free).
* `essSurj_functor07JG_iff` — **the essential-surjectivity clause is equivalent to essential
  surjectivity of the reduction functor**, given `hinj` and `hlift`.
* `essSurj_firstOrderCrystalsToPairs_of_essSurj_functor07JG` — the clause implies, with no
  hypotheses, the conclusion that `hlift` is used to buy, so `hlift` is no stronger than that
  half of the tag.
* `equivalence07JH_iff` — **the proposition `Equivalence07JH R` is equivalent to the reduction
  functor being an equivalence**, given `hinj` and `hlift`.  This upgrades
  `equivalence07JH_of_isEquivalence_functor` from an implication to an equivalence, so that
  `Functor.IsEquivalence R.functor` is not merely sufficient for that rendering of the tag but is
  exactly what it amounts to once the two completion hypotheses are assumed.

## What is and is not proved

**[Stacks, Tag 07JH] is `...SmallSite.crystalPairFunctor_isEquivalence`; no `@[stacks 07JH]`
attribute is placed in this module.**
Every statement below is an equivalence or an implication between a clause of the tag and the
corresponding property of `R.functor`; none of them asserts a clause.  What they do is move the
whole content of the tag onto one declaration — the reduction functor, which is the field
`Crystalline.GlobalCrystallineSituation.SmallSite.PreReduction07JG.functor` — and say precisely
what each clause costs beyond it.

The hypotheses are the two of `Crystalline.firstOrderCrystalsToPairs_isEquivalence`, carried
verbatim and not weakened:

* `hinj`, injectivity of the canonical map `M ⊗_D Ω → M ⊗̂_D Ω` on the modules of the first-order
  crystal data.  By `Crystalline.injective_toCompletedTensor_iff_isHausdorff` this is `p`-adic
  Hausdorffness of the uncompleted tensor product, and by
  `Crystalline.not_injective_toCompletedTensor_of_isUnit` it can fail; it is discharged when `Ω`
  is free over `D`, by
  `Crystalline.equivalence07JH_of_isEquivalence_functor_dividedPowerDifferentials` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/FreeDifferentials07JH.lean`.
* `hlift`, that the connection of every pair factors through `M ⊗_D Ω`.  It is discharged when
  `Ω` is free of **finite** rank, by
  `Crystalline.forall_exists_firstOrderConnection_of_finite_basis` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/CompletedTensorFreeFinite.lean`, and the finiteness
  is not removable there.

`Functor.Full R.functor`, `Functor.EssSurj R.functor` and `Functor.IsEquivalence R.functor` are
**not** discharged anywhere in the library, at any rank, so nothing below proves a clause of the
tag.  What is new is that the fullness and essential-surjectivity clauses are now *stated* at
all: `Functor.Full (functor07JG R)` and `Functor.EssSurj (functor07JG R)` appear in no other
module.

Every producer of a reduction datum
`Crystalline.GlobalCrystallineSituation.SmallSite.Reduction07JG` in the library consumes a datum
of its own — the newest being `...SmallSite.reduction07JGWholeSpaceOfLevelwise` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/LevelReductionAssembly.lean`, which asks for
the differentials of the levels, bijectivity of the base change of scalars at each level, and the
source's own `D(1)` and `D(2)` coefficient computations — so no closed term of it exists and the
statements below are hypothetical in a second, separate way; see the module documentation of
`StacksFrontier/AlgebraicGeometry/Crystalline/Reduction07JGWitness.lean`, where the only base case
`preReduction07JGBot` is *proved* to fail the field `levelSystem_isLevel`.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JB](https://stacks.math.columbia.edu/tag/07JB)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
* [Stacks Project, Tag 07JD](https://stacks.math.columbia.edu/tag/07JD)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
-/

@[expose] public section

open CategoryTheory Opposite
open scoped TensorProduct

universe u uI

namespace Crystalline

/-- **If a composite is essentially surjective then so is its second factor.**  Mathlib has the
other three combinations — `CategoryTheory.Functor.essSurj_comp` and
`CategoryTheory.Functor.essSurj_of_comp_fully_faithful` — and not this one, which needs no
hypothesis at all: a preimage of `Z` under `F ⋙ G` gives one under `G` by applying `F` to it. -/
theorem essSurj_of_essSurj_comp {C : Type*} [Category C] {E : Type*} [Category E]
    {T : Type*} [Category T] (F : C ⥤ E) (G : E ⥤ T) [(F ⋙ G).EssSurj] : G.EssSurj where
  mem_essImage Z :=
    ⟨F.obj ((F ⋙ G).objPreimage Z), ⟨(F ⋙ G).objObjPreimageIso Z⟩⟩

end Crystalline

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Crystalline AlgebraicGeometry

variable {S : GlobalCrystallineSituation.{u}}

variable {A : Type u} [CommRing A] {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u}
  [AddCommGroup Omega] [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {p : ℕ} {ι : Type uI} {dx : ι → Omega}
  [IsAffine S.X] [IsAffine S.S.scheme] {hp : IsNilpotent (S.p : Γ(S.X, ⊤))}

/-! ### The fullness clause -/

/-- **The fullness clause of [Stacks, Tag 07JH] implies fullness of the reduction, with no
hypotheses.**  This is the easy half of the fullness analogue of
`Crystalline.GlobalCrystallineSituation.SmallSite.faithful_functor07JG_iff`, and it is
unconditional for the same reason that one is: the second factor
`Crystalline.firstOrderCrystalsToPairs` is faithful outright, by
`Crystalline.firstOrderCrystalsToPairs_faithful`, and a composite that is full with a faithful
second factor has a full first factor. -/
theorem full_functor07JG_imp (R : Reduction07JG S A D g Omega d p dx hp)
    (h : Functor.Full (functor07JG R)) : Functor.Full R.functor := by
  have := firstOrderCrystalsToPairs_faithful A D g Omega d p dx
  have : Functor.Full (R.functor ⋙ firstOrderCrystalsToPairs A D g Omega d p dx) := h
  exact Functor.Full.of_comp_faithful (F := R.functor)
    (G := firstOrderCrystalsToPairs A D g Omega d p dx)

/-- **Fullness of the reduction gives the fullness clause of [Stacks, Tag 07JH]**, at the cost of
`hinj`: the second factor is full once the canonical map `M ⊗_D Ω → M ⊗̂_D Ω` is injective on the
modules of the first-order crystal data, by
`Crystalline.firstOrderCrystalsToPairs_full_of_injective`, and a composite of full functors is
full. -/
theorem full_functor07JG_of_full (R : Reduction07JG S A D g Omega d p dx hp)
    (hR : Functor.Full R.functor)
    (hinj : ∀ Q : FirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx,
      Function.Injective (toCompletedTensor p D Omega Q.carrier)) :
    Functor.Full (functor07JG R) := by
  have := hR
  have := firstOrderCrystalsToPairs_full_of_injective A D g Omega d p dx hinj
  exact Functor.Full.comp _ _

/-- **The fullness clause of [Stacks, Tag 07JH] is exactly fullness of the reduction, given
`hinj`.**  This is the `Functor.Full` analogue of
`Crystalline.GlobalCrystallineSituation.SmallSite.faithful_functor07JG_iff`: all of the content of
that half of the tag sits in the passage from a crystal in quasi-coherent `𝒪_{X/S}`-modules to its
first-order comparison datum over `D`, and none of it in the passage from that datum to the pair,
except for the hypothesis `hinj` on the completion.

Unlike the faithfulness statement this one is not hypothesis-free, and `hinj` is needed only for
the direction that produces the clause: `full_functor07JG_imp` is unconditional. -/
theorem full_functor07JG_iff (R : Reduction07JG S A D g Omega d p dx hp)
    (hinj : ∀ Q : FirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx,
      Function.Injective (toCompletedTensor p D Omega Q.carrier)) :
    Functor.Full (functor07JG R) ↔ Functor.Full R.functor :=
  ⟨full_functor07JG_imp R, fun hR ↦ full_functor07JG_of_full R hR hinj⟩

/-! ### The essential-surjectivity clause -/

/-- **Essential surjectivity of the reduction gives the essential-surjectivity clause of
[Stacks, Tag 07JH]**, at the cost of `hlift`: the second factor is essentially surjective once
the connection of every pair factors through `M ⊗_D Ω`, by
`Crystalline.firstOrderCrystalsToPairs_essSurj_of_exists_lift`, and a composite of essentially
surjective functors is essentially surjective. -/
theorem essSurj_functor07JG_of_essSurj (R : Reduction07JG S A D g Omega d p dx hp)
    (hR : Functor.EssSurj R.functor)
    (hlift : ∀ P : Pair.{u, u, uI, u} p D Omega dx (derivationFun A D g Omega d),
      ∃ nabla : FirstOrderConnection D Omega (derivationFun A D g Omega d) P.carrier,
        ∀ m : P.carrier, toCompletedTensor p D Omega P.carrier
          (TensorProduct.comm D Omega P.carrier (nabla m)) = P.nabla m) :
    Functor.EssSurj (functor07JG R) := by
  have := hR
  have := firstOrderCrystalsToPairs_essSurj_of_exists_lift A D g Omega d p dx hlift
  exact Functor.essSurj_comp _ _

/-- **The essential-surjectivity clause of [Stacks, Tag 07JH] implies essential surjectivity of
the reduction**, at the cost of `hinj`.  A composite that is essentially surjective with a fully
faithful second factor has an essentially surjective first factor, by
`CategoryTheory.Functor.essSurj_of_comp_fully_faithful`; the faithfulness of the second factor is
free and its fullness is what `hinj` buys. -/
theorem essSurj_functor07JG_imp (R : Reduction07JG S A D g Omega d p dx hp)
    (hinj : ∀ Q : FirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx,
      Function.Injective (toCompletedTensor p D Omega Q.carrier))
    (h : Functor.EssSurj (functor07JG R)) : Functor.EssSurj R.functor := by
  have := firstOrderCrystalsToPairs_faithful A D g Omega d p dx
  have := firstOrderCrystalsToPairs_full_of_injective A D g Omega d p dx hinj
  have : Functor.EssSurj (R.functor ⋙ firstOrderCrystalsToPairs A D g Omega d p dx) := h
  exact Functor.essSurj_of_comp_fully_faithful R.functor
    (firstOrderCrystalsToPairs A D g Omega d p dx)

/-- **The essential-surjectivity clause of [Stacks, Tag 07JH] is exactly essential surjectivity
of the reduction, given `hinj` and `hlift`.**  As with
`Crystalline.GlobalCrystallineSituation.SmallSite.full_functor07JG_iff`, this localizes the whole
content of that half of the tag in the reduction functor. -/
theorem essSurj_functor07JG_iff (R : Reduction07JG S A D g Omega d p dx hp)
    (hinj : ∀ Q : FirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx,
      Function.Injective (toCompletedTensor p D Omega Q.carrier))
    (hlift : ∀ P : Pair.{u, u, uI, u} p D Omega dx (derivationFun A D g Omega d),
      ∃ nabla : FirstOrderConnection D Omega (derivationFun A D g Omega d) P.carrier,
        ∀ m : P.carrier, toCompletedTensor p D Omega P.carrier
          (TensorProduct.comm D Omega P.carrier (nabla m)) = P.nabla m) :
    Functor.EssSurj (functor07JG R) ↔ Functor.EssSurj R.functor :=
  ⟨essSurj_functor07JG_imp R hinj, fun hR ↦ essSurj_functor07JG_of_essSurj R hR hlift⟩

/-- **The essential-surjectivity clause of [Stacks, Tag 07JH] already contains essential
surjectivity of the algebraic functor, with no hypotheses.**  A composite that is essentially
surjective has an essentially surjective second factor, by
`Crystalline.essSurj_of_essSurj_comp`; the second factor here is
`Crystalline.firstOrderCrystalsToPairs`, whose essential surjectivity is exactly what `hlift`
buys in `Crystalline.firstOrderCrystalsToPairs_essSurj_of_exists_lift`.

So `hlift` is not an assumption *beyond* that half of the tag: it is a sufficient condition for
something the half implies outright.  The hypothesis in
`essSurj_functor07JG_of_essSurj` is therefore no stronger than the conclusion it helps produce,
which is worth recording since `hlift` is known to fail to be derivable for a general `Ω`. -/
theorem essSurj_firstOrderCrystalsToPairs_of_essSurj_functor07JG
    (R : Reduction07JG S A D g Omega d p dx hp)
    (h : Functor.EssSurj (functor07JG R)) :
    Functor.EssSurj (firstOrderCrystalsToPairs A D g Omega d p dx :
      FirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx ⥤
        Pair.{u, u, uI, u} p D Omega dx (derivationFun A D g Omega d)) := by
  have : Functor.EssSurj (R.functor ⋙ firstOrderCrystalsToPairs A D g Omega d p dx) := h
  exact essSurj_of_essSurj_comp R.functor _

/-! ### The tag itself -/

/-- **[Stacks, Tag 07JH] implies that the reduction functor is an equivalence**, at the cost of
`hinj`.  Faithfulness transfers by
`Crystalline.GlobalCrystallineSituation.SmallSite.faithful_functor07JG_iff` with no hypothesis,
fullness by `full_functor07JG_imp` with no hypothesis, and essential surjectivity by
`essSurj_functor07JG_imp`, which is where `hinj` is spent. -/
theorem isEquivalence_functor_of_equivalence07JH (R : Reduction07JG S A D g Omega d p dx hp)
    (hinj : ∀ Q : FirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx,
      Function.Injective (toCompletedTensor p D Omega Q.carrier))
    (h : Equivalence07JH R) : Functor.IsEquivalence R.functor := by
  have hE : Functor.IsEquivalence (functor07JG R) := h
  exact { faithful := (faithful_functor07JG_iff R).mp hE.faithful
          full := full_functor07JG_imp R hE.full
          essSurj := essSurj_functor07JG_imp R hinj hE.essSurj }

/-- **`Equivalence07JH R` is exactly the statement that the reduction functor is an equivalence,
given `hinj` and `hlift`.**  This upgrades
`Crystalline.GlobalCrystallineSituation.SmallSite.equivalence07JH_of_isEquivalence_functor` from
an implication to an equivalence: once the two hypotheses on the completion are assumed, nothing
of that rendering of [Stacks, Tag 07JH] is left outside `Functor.IsEquivalence R.functor`.  The
tag itself is `...SmallSite.crystalPairFunctor_isEquivalence`, for the functor
`...SmallSite.crystalPairFunctor`, which does not go through a reduction datum. -/
theorem equivalence07JH_iff (R : Reduction07JG S A D g Omega d p dx hp)
    (hinj : ∀ Q : FirstOrderCrystal.{u, u, u, uI, u} A D g Omega d p dx,
      Function.Injective (toCompletedTensor p D Omega Q.carrier))
    (hlift : ∀ P : Pair.{u, u, uI, u} p D Omega dx (derivationFun A D g Omega d),
      ∃ nabla : FirstOrderConnection D Omega (derivationFun A D g Omega d) P.carrier,
        ∀ m : P.carrier, toCompletedTensor p D Omega P.carrier
          (TensorProduct.comm D Omega P.carrier (nabla m)) = P.nabla m) :
    Equivalence07JH R ↔ Functor.IsEquivalence R.functor :=
  ⟨isEquivalence_functor_of_equivalence07JH R hinj,
    fun hR ↦ equivalence07JH_of_isEquivalence_functor R hR hinj hlift⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end
