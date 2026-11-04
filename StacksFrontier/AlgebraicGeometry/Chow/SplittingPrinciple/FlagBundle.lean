module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDivisorClass
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleRelation
public import StacksFrontier.AlgebraicGeometry.Chow.ClopenDecomposition.FlatPullback
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SplittingPrinciple
public import StacksCore.Tactic.StacksAttribute

/-!
# The splitting principle in Chow homology

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be locally of
finite type over `S` and let `ℰ_i` be a finite collection of finite locally free `𝒪_X`-modules of
ranks `r_i`. Stacks 02UL asserts that there is a projective flat morphism `π : P ⟶ X` of
relative dimension `d` such that

1. for any `f : Y ⟶ X` the flat pullback `π_Y^* : A_*(Y) ⟶ A_{*+d}(Y ×_X P)` is injective, and
2. each `π^*ℰ_i` has a filtration whose successive quotients are invertible `𝒪_P`-modules.

The morphism is the iterated projective bundle: `𝐏(ℰ_i)` splits one invertible quotient off
`ℰ_i` and lowers its rank by one, and one iterates until every rank is at most one. Here the
iteration is carried out in Chow homology, with the degree shift `A_k(X) ⟶ A_{k+d}(P)` of the
Chow groups of chapter 42, which the ungraded setting of Stacks 0FI7 does not have.

## The relative dimension is `∑ binom(r_i, 2)`

Each layer contributes the relative dimension of one projective bundle, which is one less than
the rank of the module it is the bundle of. Splitting `ℰ_i` of rank `r_i` completely therefore
costs `(r_i - 1) + (r_i - 2) + ⋯ + 0 = binom(r_i, 2)`, and the collection costs the sum. The
recursion that produces this is `Nat.choose_succ_succ` at `k = 1`:
`binom(m + 1, 2) = binom(m, 2) + m`, the left summand being the cost of the remaining layers and
the right one the relative dimension `(m + 1) - 1` of the layer just taken.

## Main definitions

* `Stacks.Chow.BundleStep` — the datum of one layer: the projective bundle of a module of rank
  `r + 1`, its projection as a flat morphism of relative dimension `r`, the Chow-theoretic data
  that make flat pullback along it exist and be injective, and its tautological short exact
  sequence.
* `Stacks.Chow.SplittingMorphism` — a flat morphism of relative dimension `d` along which flat
  pullback on Chow groups exists and is injective in every degree.
* `Stacks.Chow.BundleStep.pullbackChow`, `Stacks.Chow.SplittingMorphism.pullbackChow` — the flat
  pullback `π^* : A_k(X) ⟶ A_{k+d}(P)` of Stacks 0FVK along a layer and along a tower.

## Main results

* `Stacks.Chow.flatPullbackFactorsThroughRationalEquivalence_comp` — **Stacks 02S1 along a
  composition**: the tag for `f ≫ g` follows from the tag for `f` and for `g`.
* `Stacks.Chow.BundleStep.injective_pullbackChow` — **flat pullback along the projection of a
  projective bundle is injective**, by the injectivity half of Stacks 02TX.
* `Stacks.Chow.exists_splittingMorphism` — **Stacks 02UL, clauses (1) and (2) over `X`.**
* `Stacks.Chow.exists_splittingMorphism_basechange` — **Stacks 02UL, clause (1) after an
  arbitrary base change**, in a weakened form; see below.

## The layers are hypotheses

`Stacks.Chow.BundleStep` bundles the projective bundle `π : 𝐏(ℰ) ⟶ X` of a finite locally free
module of rank `r + 1` with the following facts about it, each recorded on its field:

* flatness, properness and relative dimension `r` of `π` (Stacks 02TX and 0800);
* the tautological short exact sequence `0 ⟶ 𝓕 ⟶ π^*ℰ ⟶ 𝒪_P(1) ⟶ 0` with `𝓕` finite locally
  free of rank `r` (Stacks 01O4 and 0B3V);
* that flat pullback along `π` factors through rational equivalence (Stacks 02S1);
* the operator `c₁(𝒪_P(1)) ∩ -` (Stacks 02SO together with 02TI);
* injectivity of the projective space bundle map (the injectivity half of Stacks 02TX).

The results hold for any family of layers with these properties, and specialising the layers to
the projective bundles of the `ℰ_i` recovers Stacks 02UL. The filtrations are recorded with
`Stacks.WeilCohomology.HasInvertibleFiltration`, the notion of the ungraded splitting principle
`Stacks.WeilCohomology.ChernSetup.exists_injective_hasInvertibleFiltration` (Stacks 0FI7).

## Clause (1) after a base change

Clause (1) of the source asks for injectivity of `π_Y^*` for every `f : Y ⟶ X`, where
`π_Y : Y ×_X P ⟶ Y` is the base change of the one morphism `π`.
`Stacks.Chow.exists_splittingMorphism_basechange` gives injectivity of `π_Y^*` for a morphism
`π_Y : P_Y ⟶ Y` obtained by running the iteration over `Y` on the modules `f^*ℰ_i`: the same
relative dimension, the same filtrations, and injectivity in every degree, but with no assertion
that `P_Y` is `Y ×_X P`. This is weaker than clause (1).

## Projectivity

Each layer is proper, and properness is stable under composition, so the tower is proper
(`Stacks.Chow.SplittingMorphism.isProper_π`). The tower is not asserted to be H-projective, which
is what the source's "projective" means: the morphism is delivered proper, flat and of relative
dimension `d`, and the word "projective" of the tag is weakened to "proper".

## References

* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
* [Stacks Project, Tag 0FI7](https://stacks.math.columbia.edu/tag/0FI7)
* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Transport of Chow groups along an equality of degrees -/

/-- Injectivity of flat pullback in one degree transfers to any degree equal to it. -/
private theorem injective_flatPullbackChow_congr (C : ChowSituation.{u}) {X' X : Scheme.{u}}
    (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (f : X' ⟶ X) [LocallyOfFiniteType f] [Flat f] (hbase : f ≫ sX = sX') (d : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f d)
    (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sX' sX f hbase d hf k)
    {k l : ℤ} (h : k = l)
    (hinj : Function.Injective (flatPullbackChow C sX' sX f hbase d hf k (hfac k))) :
    Function.Injective (flatPullbackChow C sX' sX f hbase d hf l (hfac l)) := by
  subst h; exact hinj

/-! ### Stacks 02RD on Chow groups -/

/-- **Stacks 02S1 along a composition.** If flat pullback of cycles factors through rational
equivalence along `g : Y ⟶ Z` in degree `k` and along `f : X ⟶ Y` in degree `k + s`, then it does
so along `f ≫ g` in degree `k`. -/
theorem flatPullbackFactorsThroughRationalEquivalence_comp (C : ChowSituation.{u})
    {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S)
    [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (f : X ⟶ Y)
    [LocallyOfFiniteType f] [Flat f] (g : Y ⟶ Z) [LocallyOfFiniteType g] [Flat g]
    (hfbase : f ≫ sY = sX) (hgbase : g ≫ sZ = sY) (r s : ℕ)
    (hf : AlgebraicGeometry.RelativeDimension f r)
    (hg : AlgebraicGeometry.RelativeDimension g s) (k : ℤ)
    (hfacg : FlatPullbackFactorsThroughRationalEquivalence C sY sZ g hgbase s hg k)
    (hfacf : FlatPullbackFactorsThroughRationalEquivalence C sX sY f hfbase r hf (k + (s : ℤ))) :
    FlatPullbackFactorsThroughRationalEquivalence C sX sZ (f ≫ g)
      (by rw [Category.assoc, hgbase, hfbase]) (r + s)
      (AlgebraicGeometry.RelativeDimension.comp_of_flat f g hf hg) k := by
  intro α hα
  have hcast : k + (s : ℤ) + (r : ℤ) = k + ((r + s : ℕ) : ℤ) := by push_cast; ring
  rw [← flatPullback_comp C sX sY sZ f g hfbase hgbase r s hf hg k hcast α]
  exact mem_rationalEquivalences_cast C sX hcast (hfacf _ (hfacg α hα))

/-! ### Extracting one coordinate from an injective sum -/

/-- A sum `β ↦ ∑ i, T i (β i)` of additive maps which is injective in the whole family is
injective in each coordinate. -/
private theorem injective_of_injective_sum {n : ℕ} {M : Fin n → Type*}
    [∀ i, AddCommGroup (M i)] {N : Type*} [AddCommGroup N] (T : ∀ i, M i →+ N)
    (hinj : Function.Injective fun β : (∀ i, M i) ↦ ∑ i, T i (β i)) (i₀ : Fin n) :
    Function.Injective (T i₀) := by
  classical
  have key : ∀ z : M i₀, ∑ i, T i (Function.update (fun i ↦ (0 : M i)) i₀ z i) = T i₀ z := by
    intro z
    rw [Finset.sum_eq_single i₀ (fun j _ hj ↦ by rw [Function.update_of_ne hj, map_zero])
      (fun h ↦ absurd (Finset.mem_univ i₀) h), Function.update_self]
  intro x y hxy
  have h := hinj (show ∑ i, T i (Function.update (fun i ↦ (0 : M i)) i₀ x i) =
      ∑ i, T i (Function.update (fun i ↦ (0 : M i)) i₀ y i) from by rw [key x, key y, hxy])
  simpa using congrFun h i₀

/-! ### One layer of the tower -/

/-- **One layer of the splitting tower: the projective bundle of a finite locally free module of
rank `r + 1`, with everything Stacks 02UL uses about it.**

The geometry is the projection `π : 𝐏(ℰ) ⟶ X`, flat, proper and of relative dimension `r`; the
Chow-theoretic data are what make flat pullback along `π` exist on Chow groups and be injective;
and the tautological short exact sequence `0 ⟶ 𝓕 ⟶ π^*ℰ ⟶ 𝒪_P(1) ⟶ 0` has kernel finite locally
free of rank `r`. -/
structure BundleStep (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (E : X.Modules) (r : ℕ) where
  /-- The projective bundle `𝐏(ℰ)`: Stacks 01OB. -/
  P : Scheme.{u}
  /-- Its structure morphism to the base scheme of the situation of Stacks 02QL. -/
  sP : P ⟶ C.S
  /-- The bundle is locally of finite type over the base, so it has Chow groups. -/
  [locallyOfFiniteType_sP : LocallyOfFiniteType sP]
  /-- The projection `π : 𝐏(ℰ) ⟶ X`. -/
  π : P ⟶ X
  /-- The projection is locally of finite type: Stacks 02TX. -/
  [locallyOfFiniteType_π : LocallyOfFiniteType π]
  /-- The projection is flat: Stacks 02TX. -/
  [flat_π : Flat π]
  /-- The projection is proper: Stacks 0800. -/
  [isProper_π : IsProper π]
  /-- The projection is a morphism over the base scheme. -/
  hsP : π ≫ sX = sP
  /-- The projection has relative dimension `r`, one less than the rank of `ℰ`: Stacks 02TX. -/
  relDim : AlgebraicGeometry.RelativeDimension π r
  /-- Flat pullback of cycles along the projection factors through rational equivalence, so the
  flat pullback of Stacks 0FVK on Chow groups exists: Stacks 02S1. -/
  hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP r relDim k
  /-- The cap product `c₁(𝒪_P(1)) ∩ -` on the Chow groups of the bundle: Stacks 02SO for the
  component rule together with Stacks 02TI for its descent through rational equivalence. -/
  twist : ChernCapOperator C sP
  /-- The projective space bundle map `(α_0, …, α_r) ↦ ∑_{i ≤ r} c₁(𝒪_P(1))^i ∩ π^*α_i` is
  injective: the injectivity half of Stacks 02TX. -/
  hinj : ProjectiveBundleRelationInjective C sX sP π hsP (r + 1) relDim hfac twist
  /-- The tautological invertible module `𝒪_P(1)`: Stacks 01O4. -/
  twistModule : P.Modules
  /-- It is invertible: Stacks 01CS. -/
  twistModule_isInvertible : AlgebraicGeometry.SheafOfModules.IsInvertible P.presheaf
    P.ringCatSheaf.2 twistModule
  /-- The kernel `𝓕` of the tautological surjection. -/
  sub : P.Modules
  /-- Its inclusion into `π^*ℰ`. -/
  incl : sub ⟶ (Scheme.Modules.pullback π).obj E
  /-- The tautological surjection `π^*ℰ ⟶ 𝒪_P(1)`: Stacks 0B3V. -/
  quot : (Scheme.Modules.pullback π).obj E ⟶ twistModule
  /-- The two maps compose to zero. -/
  incl_comp_quot : incl ≫ quot = 0
  /-- The tautological sequence is short exact: Stacks 0B3V. -/
  shortExact : (ShortComplex.mk incl quot incl_comp_quot).ShortExact
  /-- The kernel is finite locally free of rank `r`, one less than the rank of `ℰ`: Stacks
  0B3V. -/
  sub_rank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} sub r

attribute [instance] BundleStep.locallyOfFiniteType_sP BundleStep.locallyOfFiniteType_π
  BundleStep.flat_π BundleStep.isProper_π

namespace BundleStep

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]
  {E : X.Modules} {r : ℕ}

/-- **Stacks 0FVK along one layer.** Flat pullback on Chow groups along the projection of the
bundle, `π^* : A_k(X) ⟶ A_{k+r}(𝐏(ℰ))`. -/
def pullbackChow (D : BundleStep C sX E r) (k : ℤ) :
    chowGroup C sX k →+ chowGroup C D.sP (k + (r : ℤ)) :=
  flatPullbackChow C D.sP sX D.π D.hsP r D.relDim k (D.hfac k)

/-- **Flat pullback along the projection of a projective bundle is injective.** -/
theorem injective_pullbackChow (D : BundleStep C sX E r) (k : ℤ) :
    Function.Injective (D.pullbackChow k) := by
  refine injective_flatPullbackChow_congr C D.sP sX D.π D.hsP r D.relDim D.hfac
    (show k + ((r + 1 : ℕ) : ℤ) - ((r + 1 - 0 : ℕ) : ℤ) = k from by push_cast; ring) ?_
  have hterm := injective_of_injective_sum
    (fun i : Fin (r + 1) ↦ projectiveBundleChernTerm C sX D.sP D.π D.hsP (r + 1) D.relDim D.hfac
      D.twist (k + ((r + 1 : ℕ) : ℤ)) i.val i.isLt.le)
    (D.hinj (k + ((r + 1 : ℕ) : ℤ))) ⟨0, Nat.zero_lt_succ r⟩
  simp only [projectiveBundleChernTerm, projectiveBundlePullback, AddMonoidHom.coe_comp] at hterm
  exact hterm.of_comp.of_comp

end BundleStep

/-! ### The output of the iteration -/

/-- **A splitting morphism of relative dimension `d` over `X`:** a flat, proper morphism
`π : P ⟶ X` of schemes locally of finite type over the base of Stacks 02QL, of relative dimension
`d`, along which the flat pullback of Stacks 0FVK on Chow groups exists and is injective in every
degree. -/
structure SplittingMorphism (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (d : ℕ) where
  /-- The source of the morphism. -/
  P : Scheme.{u}
  /-- Its structure morphism to the base scheme. -/
  sP : P ⟶ C.S
  /-- The source is locally of finite type over the base, so it has Chow groups. -/
  [locallyOfFiniteType_sP : LocallyOfFiniteType sP]
  /-- The morphism itself. -/
  π : P ⟶ X
  /-- It is locally of finite type. -/
  [locallyOfFiniteType_π : LocallyOfFiniteType π]
  /-- It is flat. -/
  [flat_π : Flat π]
  /-- It is proper. -/
  [isProper_π : IsProper π]
  /-- It is a morphism over the base scheme. -/
  hsP : π ≫ sX = sP
  /-- It has relative dimension `d`. -/
  relDim : AlgebraicGeometry.RelativeDimension π d
  /-- Flat pullback of cycles along it factors through rational equivalence: Stacks 02S1. -/
  hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP d relDim k
  /-- **Clause (1) of Stacks 02UL over `X`:** flat pullback on Chow groups along it is injective
  in every degree. -/
  injective_pullbackChow : ∀ k : ℤ,
    Function.Injective (flatPullbackChow C sP sX π hsP d relDim k (hfac k))

attribute [instance] SplittingMorphism.locallyOfFiniteType_sP
  SplittingMorphism.locallyOfFiniteType_π SplittingMorphism.flat_π SplittingMorphism.isProper_π

namespace SplittingMorphism

variable {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX]

/-- **Stacks 0FVK along a splitting morphism.** Flat pullback on Chow groups,
`π^* : A_k(X) ⟶ A_{k+d}(P)`. -/
def pullbackChow {d : ℕ} (T : SplittingMorphism C sX d) (k : ℤ) :
    chowGroup C sX k →+ chowGroup C T.sP (k + (d : ℤ)) :=
  flatPullbackChow C T.sP sX T.π T.hsP d T.relDim k (T.hfac k)

/-- **The identity is a splitting morphism of relative dimension zero.** -/
def id (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] :
    SplittingMorphism C sX 0 where
  P := X
  sP := sX
  π := 𝟙 X
  hsP := Category.id_comp sX
  relDim := relativeDimension_identity X
  hfac := flatPullbackFactorsThroughRationalEquivalence_id C sX
  injective_pullbackChow k x y hxy := by
    have h := (flatPullbackChow_id C sX k x).symm.trans
      (hxy.trans (flatPullbackChow_id C sX k y))
    exact (chowGroupCast C sX (show k = k + ((0 : ℕ) : ℤ) from by simp)).injective h

/-- **One layer composed onto a splitting morphism is a splitting morphism.** If
`π : 𝐏(ℰ) ⟶ X` is a layer of relative dimension `m` and `T : Q ⟶ 𝐏(ℰ)` is a splitting morphism of
relative dimension `n`, then `T.π ≫ π : Q ⟶ X` is a splitting morphism of relative dimension
`n + m`. -/
def compStep {E : X.Modules} {m : ℕ} (D : BundleStep C sX E m) {n : ℕ}
    (T : SplittingMorphism C D.sP n) : SplittingMorphism C sX (n + m) where
  P := T.P
  sP := T.sP
  π := T.π ≫ D.π
  hsP := by rw [Category.assoc, D.hsP, T.hsP]
  relDim := AlgebraicGeometry.RelativeDimension.comp_of_flat T.π D.π T.relDim D.relDim
  hfac k := flatPullbackFactorsThroughRationalEquivalence_comp C T.sP D.sP sX T.π D.π T.hsP
    D.hsP n m T.relDim D.relDim k (D.hfac k) (T.hfac (k + (m : ℤ)))
  injective_pullbackChow k x y hxy := by
    have hfacfg := flatPullbackFactorsThroughRationalEquivalence_comp C T.sP D.sP sX T.π D.π
      T.hsP D.hsP n m T.relDim D.relDim k (D.hfac k) (T.hfac (k + (m : ℤ)))
    have hx := flatPullbackChow_comp C T.sP D.sP sX T.π D.π T.hsP D.hsP n m T.relDim D.relDim k
      (T.hfac (k + (m : ℤ))) (D.hfac k) hfacfg x
    have hy := flatPullbackChow_comp C T.sP D.sP sX T.π D.π T.hsP D.hsP n m T.relDim D.relDim k
      (T.hfac (k + (m : ℤ))) (D.hfac k) hfacfg y
    refine D.injective_pullbackChow k (T.injective_pullbackChow (k + (m : ℤ)) ?_)
    simp only [BundleStep.pullbackChow]
    exact eq_of_heq (hx.trans ((heq_of_eq hxy).trans hy.symm))

/-- The source of `compStep D T` is that of `T`. -/
@[simp]
theorem compStep_P {E : X.Modules} {m : ℕ} (D : BundleStep C sX E m) {n : ℕ}
    (T : SplittingMorphism C D.sP n) : (compStep D T).P = T.P :=
  rfl

/-- The morphism of `compStep D T` is `T.π ≫ D.π`. -/
@[simp]
theorem compStep_π {E : X.Modules} {m : ℕ} (D : BundleStep C sX E m) {n : ℕ}
    (T : SplittingMorphism C D.sP n) : (compStep D T).π = T.π ≫ D.π :=
  rfl

end SplittingMorphism

/-! ### The splitting principle -/

/-- The splitting principle with the relative dimension `n = ∑ binom(r_i, 2)` as a parameter. -/
private theorem exists_splittingMorphism_aux (C : ChowSituation.{u})
    (step : ∀ {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (F : Y.Modules) (m : ℕ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (m + 1) →
        BundleStep C sY F m) :
    ∀ (n : ℕ) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (I : Type)
      [Fintype I] (E : I → X.Modules) (r : I → ℕ),
      (∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i)) →
      ∑ i, (r i).choose 2 = n →
      ∃ T : SplittingMorphism C sX n, ∀ i, Stacks.WeilCohomology.HasInvertibleFiltration T.P
        ((Scheme.Modules.pullback T.π).obj (E i)) (r i) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X sX _ I _ E r hE hn
    by_cases hr : ∀ i, r i ≤ 1
    · have hn0 : n = 0 := by
        rw [← hn]
        exact Finset.sum_eq_zero fun i _ ↦ Nat.choose_eq_zero_of_lt (by have := hr i; omega)
      subst hn0
      exact ⟨SplittingMorphism.id C sX, fun i ↦
        Stacks.WeilCohomology.hasInvertibleFiltration_of_rank_le_one _ (r i)
          (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ (𝟙 X) (E i) (r i) (hE i))
          (hr i)⟩
    obtain ⟨i, hi⟩ := not_forall.mp hr
    have hi : 1 < r i := by omega
    have hEi : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i)
        (r i - 1 + 1) := by
      rw [Nat.sub_add_cancel (show 1 ≤ r i by omega)]
      exact hE i
    set D := step sX (E i) (r i - 1) hEi with hD
    have hE' : ∀ j, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (Function.update (fun j ↦ (Scheme.Modules.pullback D.π).obj (E j)) i D.sub j)
        (Function.update r i (r i - 1) j) := by
      intro j
      by_cases hj : j = i
      · rw [hj]
        simpa only [Function.update_self] using D.sub_rank
      · simpa only [Function.update_of_ne hj] using
          @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ D.π (E j) (r j) (hE j)
    have hchoose : (r i - 1).choose 2 + (r i - 1) = (r i).choose 2 := by
      obtain ⟨m, hm⟩ : ∃ m, r i = m + 1 := ⟨r i - 1, by omega⟩
      have key : (m + 1).choose 2 = m.choose 2 + m := by
        show Nat.choose (m + 1) (1 + 1) = _
        rw [Nat.choose_succ_succ, Nat.choose_one_right]
        show m + Nat.choose m 2 = Nat.choose m 2 + m
        omega
      rw [hm, Nat.add_sub_cancel, key]
    have hsplit : ∀ g : I → ℕ, ∑ j, g j = g i + ∑ j ∈ Finset.univ.erase i, g j := fun g ↦
      (Finset.add_sum_erase Finset.univ g (Finset.mem_univ i)).symm
    have hA : (∑ j, (Function.update r i (r i - 1) j).choose 2) =
        (r i - 1).choose 2 + ∑ j ∈ Finset.univ.erase i, (r j).choose 2 := by
      rw [hsplit, Function.update_self]
      exact congrArg _ (Finset.sum_congr rfl fun j hj ↦ by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)])
    have hsum : (∑ j, (Function.update r i (r i - 1) j).choose 2) + (r i - 1) = n := by
      rw [hA, ← hn, hsplit fun j ↦ (r j).choose 2]; omega
    have hlt : (∑ j, (Function.update r i (r i - 1) j).choose 2) < n := by omega
    obtain ⟨T, hT⟩ := ih _ hlt D.sP I
      (Function.update (fun j ↦ (Scheme.Modules.pullback D.π).obj (E j)) i D.sub)
      (Function.update r i (r i - 1)) hE' rfl
    subst hsum
    refine ⟨SplittingMorphism.compStep D T, fun j ↦ ?_⟩
    simp only [SplittingMorphism.compStep_P, SplittingMorphism.compStep_π]
    have comp₁ : (Scheme.Modules.pullback T.π).obj
          ((Scheme.Modules.pullback D.π).obj (E j)) ≅
        (Scheme.Modules.pullback (T.π ≫ D.π)).obj (E j) :=
      (Scheme.Modules.pullbackComp T.π D.π).app (E j)
    by_cases hj : j = i
    · rw [hj] at comp₁ ⊢
      have hDx : ((ShortComplex.mk D.incl D.quot D.incl_comp_quot).map
          (Scheme.Modules.pullback T.π)).ShortExact :=
        Stacks.WeilCohomology.shortExact_map_pullback T.π _ D.shortExact
      have hleft : Stacks.WeilCohomology.HasInvertibleFiltration T.P
          ((Scheme.Modules.pullback T.π).obj D.sub) (r i - 1) := by
        simpa only [Function.update_self] using hT i
      have hrank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback T.π).obj
            ((Scheme.Modules.pullback D.π).obj (E i))) (r i - 1 + 1) :=
        @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ T.π _ _
          (@AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ D.π (E i) _ hEi)
      refine Stacks.WeilCohomology.HasInvertibleFiltration.of_iso comp₁ ?_
      simpa only [Nat.sub_add_cancel (show 1 ≤ r i by omega)] using
        Stacks.WeilCohomology.HasInvertibleFiltration.step _ _ _ hDx
          (Stacks.WeilCohomology.isInvertible_pullback_obj T.π D.twistModule
            D.twistModule_isInvertible)
          hrank.isFiniteLocallyFree hleft
    · refine Stacks.WeilCohomology.HasInvertibleFiltration.of_iso comp₁ ?_
      simpa only [Function.update_of_ne hj] using hT j

/-- **Stacks 02UL, the splitting principle.** Let `(S, δ)` be the situation of Stacks 02QL, let
`X` be locally of finite type over `S` and let `ℰ_i`, `i ∈ I` finite, be finite locally free
`𝒪_X`-modules of ranks `r_i`. There is a flat proper morphism `π : P ⟶ X` of relative dimension
`d = ∑_i binom(r_i, 2)` such that

1. the flat pullback `π^* : A_k(X) ⟶ A_{k+d}(P)` of Stacks 0FVK is injective in every degree, and
2. each `π^*ℰ_i` has a filtration of length `r_i` whose successive quotients are invertible
   `𝒪_P`-modules.

The relative dimension is `∑_i binom(r_i, 2)` and not `∑_i (r_i - 1)`: splitting a rank-`r`
module takes `r - 1` layers, of relative dimensions `r - 1, r - 2, …, 1`. -/
@[stacks 02UL "clauses (1) and (2) over X itself, for a finite collection of finite locally free \
modules of constant ranks, with relative dimension d = sum of binom(r_i, 2). Carries the \
projective bundle of a finite locally free module of rank m+1 as a BundleStep, i.e. as Stacks \
02TX for flatness, properness (Stacks 0800) and relative dimension m, Stacks 02S1 for the \
descent of flat pullback to Chow groups, Stacks 01O4, 02SO and 02TI for c_1(O_P(1)) cap -, the \
injectivity half of Stacks 02TX for the projective space bundle map, and Stacks 0B3V for the \
tautological short exact sequence with locally free kernel of rank m. Injectivity of pi^* itself \
is NOT carried: it is derived from the 02TX bundle map. The source says projective; only \
properness is carried through the tower, because IsProjectiveMorphism of the identity needs the \
identification of P^0_X with X, which this repository lacks. Clause (1) after a base change is \
exists_splittingMorphism_basechange"]
theorem exists_splittingMorphism (C : ChowSituation.{u})
    (step : ∀ {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (F : Y.Modules) (m : ℕ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (m + 1) →
        BundleStep C sY F m)
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (I : Type) [Fintype I]
    (E : I → X.Modules) (r : I → ℕ)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i)) :
    ∃ T : SplittingMorphism C sX (∑ i, (r i).choose 2),
      ∀ i, Stacks.WeilCohomology.HasInvertibleFiltration T.P
        ((Scheme.Modules.pullback T.π).obj (E i)) (r i) :=
  exists_splittingMorphism_aux C step _ sX I E r hE rfl

/-- **Stacks 02UL, clause (1) after an arbitrary base change.** For every `f : Y ⟶ X` with `Y`
locally of finite type over the base there is a flat proper morphism `π_Y : P_Y ⟶ Y` of the same
relative dimension `d = ∑_i binom(r_i, 2)` along which flat pullback on Chow groups is injective
in every degree, and such that each `π_Y^* f^* ℰ_i` has a filtration of length `r_i` with
invertible successive quotients.

This is the splitting principle run over `Y` on the modules `f^*ℰ_i`, whose ranks are the `r_i`
because finite local freeness of given rank is stable under pullback. **It does not assert that
`P_Y` is `Y ×_X P` for the `P` of `Stacks.Chow.exists_splittingMorphism`**, and that is a genuine
weakening of clause (1). -/
@[stacks 02UL "clause (1) after a base change, in the WEAKENED form that for EACH f : Y -> X \
there is a morphism P_Y -> Y with the same relative dimension, the same filtrations and \
injectivity in every degree. It is NOT asserted that P_Y is the fibre product Y x_X P of the \
single morphism delivered by exists_splittingMorphism, so this is weaker than clause (1) of the \
source. The reason is NOT that the base-change comparison of projective bundles is missing: the \
comparison projectiveBundleBaseChange and the cartesianness of its square \
(isPullback_projectiveBundleBaseChange) are both proved in this repository, untagged, and \
relative dimension is stable under base change by Stacks 02NK. What is missing is Stacks 02S1 \
for the base-changed projections (never derived for a base change here), base-change \
compatibility of the carried BundleStep, and the identification of the base change of the tower \
with the tower of base changes. Carries the same BundleStep operator as \
exists_splittingMorphism"]
theorem exists_splittingMorphism_basechange (C : ChowSituation.{u})
    (step : ∀ {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (F : Y.Modules) (m : ℕ),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (m + 1) →
        BundleStep C sY F m)
    {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (I : Type) [Fintype I]
    (E : I → X.Modules) (r : I → ℕ)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} (E i) (r i))
    {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : Y ⟶ X) :
    ∃ T : SplittingMorphism C sY (∑ i, (r i).choose 2),
      ∀ i, Stacks.WeilCohomology.HasInvertibleFiltration T.P
        ((Scheme.Modules.pullback T.π).obj ((Scheme.Modules.pullback f).obj (E i))) (r i) :=
  exists_splittingMorphism C step sY I (fun i ↦ (Scheme.Modules.pullback f).obj (E i)) r
    fun i ↦ @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ f (E i) (r i) (hE i)

end Stacks.Chow

end
