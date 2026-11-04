module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.CompletedStalkFinite
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.RegularSequence
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.MittagLefflerAlgebraization
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.RingTheory.Flat.MaximalIdealGradedPiece

/-!
# Algebraization of a coherent formal module flat over a Noetherian local base

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, the affine scheme
`X = Spec(A)` and the open complement `U = X \ V(𝔞)`. Let `(F_n)` be a coherent `I`-adic system
on `U`. Stacks 0EJU proves that such a system extends canonically to `X` as soon as there are a
Noetherian local ring `(R, 𝔪)` and a ring map `R → A` with

1. `I = 𝔪 A`,
2. the formal stalk `F_y^∧` flat over `R` for every point `y` of `U ∩ Y`,
3. `H⁰(U, F_1)` and `H¹(U, F_1)` finite `A`-modules.

The source's proof is the proof of Stacks 0EJS; the only difference is how the decomposition of
`Iⁿ F_(n+1)` into a finite direct sum of copies of `F_1` is obtained. Here it comes from
`Iⁿ F_(n+1) ≅ F_1 ⊗_κ 𝔪ⁿ/𝔪^(n+1)` with `κ = R/𝔪`, which is checked on stalks using the
flatness hypothesis (2), and `𝔪ⁿ/𝔪^(n+1)` is a finite-dimensional `κ`-vector space.

This file formalizes the half of that argument which starts from the decomposition: an
isomorphism of `Iⁿ F_(n+1)` with a finite direct sum of copies of `F_1` makes
`H⁰(U, Iⁿ F_(n+1))` a finite `A`-module, which is exactly the hypothesis that the 0EJS half
already in this library,
`Stacks.Algebraization.canonicallyExtends_of_finite_idealPowerSections`, consumes. The data (1)
and (2) of the source is recorded as the structure `Stacks.Algebraization.FlatLocalBase`.

## Main definitions

* `Stacks.Algebraization.baseToCompletedLocalRing` — the ring map `A → 𝒪_{X,y}^∧`.
* `Stacks.Algebraization.completedStalkBaseModule` — the formal stalk `F_y^∧` as a module over a
  ring mapping to the base ring `A`.
* `Stacks.Algebraization.FlatCompletedStalks` — hypothesis (2) of Stacks 0EJU.
* `Stacks.Algebraization.FlatLocalBase` — hypotheses (1) and (2) of Stacks 0EJU, as data.

## Main results

* `Stacks.Algebraization.exists_pi_linearEquiv_completedStalk` — hypothesis (2) of the source in
  use: at a point of `U ∩ Y` the graded piece `𝔪ⁿ F_y^∧ / 𝔪ⁿ⁺¹ F_y^∧` of the formal stalk is a
  finite product of copies of `F_y^∧ / 𝔪 F_y^∧`, which is the source's
  `Iⁿ F_(n+1) ≅ F_1 ⊗_κ 𝔪ⁿ/𝔪^(n+1)` read on the formal stalk.
* `Stacks.Algebraization.exists_pi_linearEquiv_completedStalk_uniform` — the same with one number
  of copies for every point of `U ∩ Y`, which is the shape `hdec` asks for.
* `Stacks.Algebraization.stalk_idealOnOpen_eq_map_scalarMap` and
  `Stacks.Algebraization.completedLocalIdeal_eq_map_baseToCompletedLocalRing` — the stalk of
  `I 𝒪_U` at a point of `U`, and the ideal `I 𝒪_{X,y}^∧`, are the images of `I`.
* `Stacks.Algebraization.exists_pi_linearEquiv_completedStalk_uniform_linear` — the same
  decomposition as a map of `𝒪_{X,y}^∧`-modules, with the powers of `I 𝒪_{X,y}^∧` in place of the
  powers of `𝔪`. This is hypothesis (1) in use.
* `Stacks.Algebraization.exists_pi_linearEquiv_stalk_idealPowerSub` and
  `Stacks.Algebraization.exists_pi_linearEquiv_range_stalkMap_idealPowerSub` — the decomposition
  read on the stalks of the terms of `(F_n)`: for one `k` and every `y` of `U ∩ Y` the stalk of
  `Iⁿ⁺¹ F_(n+2)` is `k` copies of the stalk of `F_1`, `𝒪_{U,y}`-linearly. This is the stalkwise
  content of `hdec`; the morphism of sheaves inducing it is
  `Stacks.Algebraization.idealPowerDesc`.
* `Stacks.Algebraization.finite_idealPowerSections_of_isoDirectSum` — the finiteness step of the
  source's proof: `H⁰(U, Iⁿ F_(n+1))` is a finite `A`-module once `Iⁿ F_(n+1)` is a finite
  direct sum of copies of `F_1` and `H⁰(U, F_1)` is a finite `A`-module.
* `Stacks.Algebraization.canonicallyExtends_of_isoDirectSum` — canonical extension of `(F_n)` to
  `X` from that decomposition.
* `Stacks.Algebraization.essImage_completionFunctor_of_isoDirectSum` — the source's concluding
  sentence: over an `I`-adically complete `A`, the system is the completion of a coherent
  `𝒪_U`-module, from the same decomposition hypothesis.

## Implementation notes

Indexing is zero-based, as everywhere in this corner of the library: the term of index `n` is
the source's `F_(n+1)`. So `H⁰(U, F_1)` is the module of sections of `F.obj.obj (op 0)`, and the
source's `Iⁿ F_(n+1)` is `Stacks.Algebraization.idealPowerSub`.

"A finite direct sum of copies of `F_1`" is the biproduct `⨁ fun _ : Fin k => F_1` in the
abelian category of `𝒪_U`-modules. Sections over `U` are computed by the functor
`Stacks.Algebraization.openSectionsFunctor`, which is additive and therefore carries that
biproduct to the biproduct of `k` copies of `H⁰(U, F_1)`; `ModuleCat.biproductIsoPi` turns the
latter into the module of `k`-tuples, whose finiteness is `Module.Finite.pi`. Two local
instances make this go through: `CategoryTheory.Limits.HasFiniteBiproducts` of
`AlgebraicGeometry.Scheme.Modules`, which Mathlib provides as a theorem rather than an
instance, and additivity of `Stacks.Algebraization.openSectionsFunctor`, which instance search
does not reach because the functor's declared domain is `AlgebraicGeometry.Scheme.Modules` while
its body is a composite of functors out of `SheafOfModules`, and the two spellings agree only up
to unfolding. Additivity is proved directly instead: addition of morphisms of sheaves of modules
is computed section by section.

The direct sum is written on the left of the isomorphism. That is deliberate: it fixes the
category in which the biproduct is formed to be `AlgebraicGeometry.Scheme.Modules`, the one
`Stacks.Algebraization.openSectionsFunctor` consumes.

The `R`-module structure on `F_y^∧` is the one the source uses: `R → A` followed by
`A → Γ(U, 𝒪_U) → 𝒪_{X,y} → 𝒪_{X,y}^∧`. The formal stalk is
`Stacks.Algebraization.completedStalk`, a module over the last of those rings, and `U ∩ Y` is
the support of `I 𝒪_U`, the same spelling
`Stacks.Algebraization.HasRegularSequenceOnCompletedStalks` uses.

Hypotheses (1) and (2) of the source are both consumed: (2) by
`Stacks.Algebraization.exists_pi_linearEquiv_completedStalk`, which is the flatness argument on
the formal stalk, and (1) by
`Stacks.Algebraization.exists_pi_linearEquiv_completedStalk_uniform_linear`, where it identifies
the image of `𝔪` in `𝒪_{X,y}^∧` with the image of `I`, namely with
`Stacks.Algebraization.completedLocalIdeal`. Between those and `hdec` stands one further step,
the global morphism.

Globalizing `Stacks.Algebraization.exists_pi_linearEquiv_completedStalk` requires three
refinements of it.

The first concerns the choice: an equivalence under `Nonempty` gives no term to glue. The
choice the decomposition makes is a `κ`-basis of `𝔪ⁿ/𝔪ⁿ⁺¹`, which does not mention the module
being decomposed (`Stacks.Flatness.exists_pi_linearEquiv_gradedPiece`); everything after it is a
map, canonical in that module (`Stacks.Flatness.piEquivSmulTopOfGradedPieceEquiv`). So the basis
can be chosen once, before any point is named, which is
`Stacks.Algebraization.exists_pi_linearEquiv_completedStalk_uniform` above.

The second is linearity: a `B.R`-linear equivalence does not suffice. A morphism of
`𝒪_U`-modules restricts on each stalk to an `𝒪_{U,y}`-linear map, so an `R`-linear map between
stalks is not a candidate for one at all, whatever its compatibilities. The construction *is*
`𝒪`-linear — every map in it is a tensor-product map in the module variable — and
`Stacks.Flatness.towerPiEquivSmulTopOfGradedPieceEquiv` says so: the submodules `𝔪ᵏ • ⊤` are
respelled there as submodules over the ring that acts and the tensor products are taken in
`TensorProduct.AlgebraTensorModule`. That is where hypothesis (1) enters a second time: the ring
that acts is `𝒪_{X,y}^∧` and the ideal that must appear is the image of `𝔪`, which is
`S.I = (maximalIdeal B.R).map B.φ` mapped on into the completion. The result is
`Stacks.Algebraization.exists_pi_linearEquiv_completedStalk_uniform_linear`, linear over
`𝒪_{X,y}^∧` and hence over `𝒪_{U,y}`.

The third is that its objects are quotients of `Stacks.Algebraization.completedStalk`, the formal
stalk `F_y^∧`, and not stalks of the terms of `(F_n)`. The comparison needed is
`F_y^∧ / Iⁿ⁺¹ F_y^∧ ≅ F_(n+1,y)` at every level, and it holds at every level for the reason it
holds at level zero: the projections of the stalk tower are surjective with kernel the
`(n+1)`-st ideal-power multiple at every level. It is
`Stacks.Algebraization.completedStalkQuotientEquivStalk`. Composed with the second step this
gives `Stacks.Algebraization.exists_pi_linearEquiv_stalk_idealPowerSub`, and —
`Stacks.Algebraization.stalk_idealPowerMultiple` naming the right-hand side as the stalk of the
subsheaf — `Stacks.Algebraization.exists_pi_linearEquiv_range_stalkMap_idealPowerSub`: the two
sides of `hdec` have isomorphic stalks at every point of `U ∩ Y`, with one `k`.

The globalization, a single morphism of sheaves `⨁_{i<k} F_1 ⟶ Iⁿ⁺¹ F_(n+2)` whose stalk maps
are bijective, is `Stacks.Algebraization.idealPowerDesc`, and
`Stacks.Algebraization.exists_isoDirectSum_idealPowerSub` is `hdec`.

The two results at the end of this file take conditions (a) and (b) of the Mittag-Leffler
criterion Stacks 0EHH as hypotheses `hML` and `htop`. Both follow from hypotheses (1)–(3) of
Stacks 0EJU. The statement of Stacks 0EJU is
`Stacks.Algebraization.canonicallyExtends_of_flatLocalBase`, and its concluding sentence is
`Stacks.Algebraization.essImage_completionFunctor_of_flatLocalBase`, which runs through part (2)
of Tag 0EIR, `Stacks.Algebraization.extendsToX_kerComapSystem_of_canonicallyExtends`, and the
chain of Tag 0EIL, as `Stacks.Algebraization.essImage_completionFunctor_of_isoDirectSum` below
does.

## References

* [Stacks Project, Tag 0EJU](https://stacks.math.columbia.edu/tag/0EJU)
* [Stacks Project, Tag 0EJS](https://stacks.math.columbia.edu/tag/0EJS)
* [Stacks Project, Tag 0EHH](https://stacks.math.columbia.edu/tag/0EHH)
* [Stacks Project, Tag 0EHC](https://stacks.math.columbia.edu/tag/0EHC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u v

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})
  (F : Stacks.Coherent.CoherentAdicSystems (idealOnOpen S))

/-! ### The hypotheses of Stacks 0EJU -/

/-- The ring map `A → 𝒪_{X,y}^∧` at a point `y` of the open complement: an element of the base
ring gives a global function on `U`, and the germ of that function at `y` is pushed into the
`I`-adic completion of the local ring. -/
def baseToCompletedLocalRing (y : S.U.toScheme) :
    S.A →+* completedLocalRing (idealOnOpen S) y :=
  (algebraMap (S.U.toScheme.presheaf.stalk y) (completedLocalRing (idealOnOpen S) y)).comp
    ((S.U.toScheme.presheaf.germ ⊤ y trivial).hom.comp (scalarMap S))

/-- `Stacks.Algebraization.baseToCompletedLocalRing` sends `a` to the image in `𝒪_{X,y}^∧` of
its germ `Stacks.Algebraization.germOfBase S y a` in `𝒪_{U,y}`. -/
theorem baseToCompletedLocalRing_apply (y : S.U.toScheme) (a : S.A) :
    baseToCompletedLocalRing S y a =
      algebraMap (S.U.toScheme.presheaf.stalk y) (completedLocalRing (idealOnOpen S) y)
        (germOfBase S y a) :=
  rfl

/-- The stalk at a point `y` of `U` of the ideal sheaf `I 𝒪_U` is the image of `I` under the
composite `A → Γ(U, 𝒪_U) → 𝒪_{U,y}`. -/
theorem stalk_idealOnOpen_eq_map_scalarMap (y : S.U.toScheme) :
    AlgebraicGeometry.IdealSheafData.stalk (idealOnOpen S) y =
      S.I.map ((S.U.toScheme.presheaf.germ ⊤ y trivial).hom.comp (scalarMap S)) := by
  have hgerm : (S.U.ι.stalkMap y).hom.comp
      (S.X.presheaf.germ ⊤ (S.U.ι.base y) (Set.mem_univ _)).hom =
      (S.U.toScheme.presheaf.germ ⊤ y trivial).hom.comp (S.U.ι.appTop).hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
    exact congrArg CommRingCat.Hom.hom (Scheme.Hom.germ_stalkMap S.U.ι ⊤ y trivial)
  have hT : (Scheme.IdealSheafData.ofIdealTop
        (S.I.map (Scheme.ΓSpecIso (.of S.A)).inv.hom)).ideal ⟨⊤, isAffineOpen_top S.X⟩ =
      S.I.map (Scheme.ΓSpecIso (.of S.A)).inv.hom := by
    simp [Scheme.IdealSheafData.ofIdealTop]
  have key : AlgebraicGeometry.IdealSheafData.stalk (idealOnOpen S) y =
      S.I.map (((S.U.ι.stalkMap y).hom.comp
        (S.X.presheaf.germ ⊤ (S.U.ι.base y) (Set.mem_univ _)).hom).comp
          (Scheme.ΓSpecIso (.of S.A)).inv.hom) := by
    rw [idealOnOpen, AlgebraicGeometry.IdealSheafData.stalk_comap,
      AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ _ (S.U.ι.base y)
        ⟨⊤, isAffineOpen_top S.X⟩ (Set.mem_univ _),
      hT, Ideal.map_map, Ideal.map_map]
  rw [key, hgerm, scalarMap, CommRingCat.hom_comp, RingHom.comp_assoc]

/-- The ideal `I 𝒪_{X,y}^∧` of the completed local ring is the image of `I` under
`Stacks.Algebraization.baseToCompletedLocalRing`. -/
theorem completedLocalIdeal_eq_map_baseToCompletedLocalRing (y : S.U.toScheme) :
    completedLocalIdeal (idealOnOpen S) y = S.I.map (baseToCompletedLocalRing S y) := by
  rw [baseToCompletedLocalRing, ← Ideal.map_map]
  exact congrArg (fun J => Ideal.map (algebraMap (S.U.toScheme.presheaf.stalk y)
    (completedLocalRing (idealOnOpen S) y)) J) (stalk_idealOnOpen_eq_map_scalarMap S y)

/-- The formal stalk `F_y^∧` of a coherent adic system, as a module over a ring `R` equipped
with a map to the base ring `A`. -/
abbrev completedStalkBaseModule (y : S.U.toScheme) {R : Type v} [CommRing R] (φ : R →+* S.A) :
    Module R (completedStalk (idealOnOpen S) F y) :=
  Module.compHom _ ((baseToCompletedLocalRing S y).comp φ)

/-- **Stacks Project, Tag 0EJU, hypothesis (2).** The formal stalk `F_y^∧` is flat over the base
ring `R` at every point `y` of `U ∩ Y`, the support of the ideal sheaf `I 𝒪_U`. -/
def FlatCompletedStalks {R : Type v} [CommRing R] (φ : R →+* S.A) : Prop :=
  ∀ y ∈ (idealOnOpen S).support,
    letI := completedStalkBaseModule S F y φ
    Module.Flat R (completedStalk (idealOnOpen S) F y)

/-- **Stacks Project, Tag 0EJU, hypotheses (1) and (2).** A Noetherian local ring `(R, 𝔪)`
together with a ring map `R → A` whose image of `𝔪` generates `I`, and over which the formal
stalk of `(F_n)` is flat at every point of `U ∩ Y`.

This is data, not a proposition: the ring `R` is part of it. Hypothesis (2) is consumed by
`Stacks.Algebraization.exists_pi_linearEquiv_completedStalk` below, the decomposition on the
formal stalks, and hypothesis (1) by
`Stacks.Algebraization.exists_pi_linearEquiv_completedStalk_uniform_linear`, which uses it to
replace the powers of `𝔪` by the powers of `I 𝒪_{X,y}^∧` — the ideal of the ring that acts, so
that the decomposition becomes a map of modules over it. The direct-sum decomposition of the
*sheaf* `Iⁿ F_(n+1)` is `Stacks.Algebraization.exists_isoDirectSum_idealPowerSub`.

The base ring may live in any universe.
-/
structure FlatLocalBase where
  /-- The Noetherian local base ring `R`. -/
  R : Type v
  /-- The commutative-ring structure on `R`. -/
  [commRingR : CommRing R]
  /-- The Noetherian hypothesis on `R`. -/
  [noetherianR : IsNoetherianRing R]
  /-- The hypothesis that `R` is local. -/
  [isLocalR : IsLocalRing R]
  /-- The ring map `R → A`. -/
  φ : R →+* S.A
  /-- Hypothesis (1): `I = 𝔪 A`. -/
  I_eq : S.I = (IsLocalRing.maximalIdeal R).map φ
  /-- Hypothesis (2): the formal stalks along `U ∩ Y` are `R`-flat. -/
  flat : FlatCompletedStalks S F φ

attribute [instance] FlatLocalBase.commRingR FlatLocalBase.noetherianR FlatLocalBase.isLocalR

/-! ### The decomposition on the formal stalks -/

/-- **Stacks Project, Tag 0EJU (the decomposition, on the formal stalks).** At a point `y` of
`U ∩ Y` the graded piece `𝔪ⁿ F_y^∧ / 𝔪ⁿ⁺¹ F_y^∧` of the formal stalk is a finite product of
copies of `F_y^∧ / 𝔪 F_y^∧`.

This is the source's `Iⁿ F_(n+1) ≅ F_1 ⊗_κ 𝔪ⁿ/𝔪ⁿ⁺¹`, read on the formal stalk: it is
`Stacks.Flatness.exists_pi_linearEquiv_smul_top_of_flat` applied to `F_y^∧`, whose `R`-flatness is
hypothesis (2) of the source. The number of copies is `dim_κ 𝔪ⁿ/𝔪ⁿ⁺¹`.

Hypothesis (1), `I = 𝔪 A`, is what turns the powers of `𝔪` here into the powers of the image of
`I`, and hence this statement into one about the stalks of the terms of `(F_n)`; that is
`Stacks.Algebraization.exists_pi_linearEquiv_completedStalk_uniform_linear` and
`Stacks.Algebraization.exists_pi_linearEquiv_stalk_idealPowerSub` below. What the hypothesis
`hdec` of the results below still stands for after those is the globalization of the stalkwise
data to a morphism of sheaves, which is
`Stacks.Algebraization.exists_isoDirectSum_idealPowerSub`. -/
theorem exists_pi_linearEquiv_completedStalk (B : FlatLocalBase S F)
    {y : S.U.toScheme} (hy : y ∈ (idealOnOpen S).support) (n : ℕ) :
    letI := completedStalkBaseModule S F y B.φ
    ∃ k : ℕ, Nonempty ((Fin k →
        (completedStalk (idealOnOpen S) F y ⧸
          (IsLocalRing.maximalIdeal B.R •
            (⊤ : Submodule B.R (completedStalk (idealOnOpen S) F y))))) ≃ₗ[B.R]
      ↥(IsLocalRing.maximalIdeal B.R ^ n •
        (⊤ : Submodule B.R (completedStalk (idealOnOpen S) F y ⧸
          (IsLocalRing.maximalIdeal B.R ^ (n + 1) •
            (⊤ : Submodule B.R (completedStalk (idealOnOpen S) F y))))))) := by
  let := completedStalkBaseModule S F y B.φ
  have : Module.Flat B.R (completedStalk (idealOnOpen S) F y) := B.flat y hy
  exact Stacks.Flatness.exists_pi_linearEquiv_smul_top_of_flat
    (IsLocalRing.maximalIdeal B.R) (completedStalk (idealOnOpen S) F y) n

/-- **Stacks Project, Tag 0EJU (the decomposition on the formal stalks, with a single number of
copies for all points).** The number of copies in
`Stacks.Algebraization.exists_pi_linearEquiv_completedStalk` can be chosen independently of the
point `y`: it is `dim_κ 𝔪ⁿ/𝔪ⁿ⁺¹`, which does not refer to the formal stalk at all.

The point is not the cardinal arithmetic but where the choice sits. The decomposition chooses a
`κ`-basis of `𝔪ⁿ/𝔪ⁿ⁺¹` (`Stacks.Flatness.exists_pi_linearEquiv_gradedPiece`) and is otherwise a
map, canonical in the module (`Stacks.Flatness.piEquivSmulTopOfGradedPieceEquiv`); so the basis can
be chosen once, before `y` is named. A `k` depending on `y` could not produce the hypothesis
`hdec` of the results below, which asks for one `k` for the whole sheaf `Iⁿ F_(n+1)`. -/
theorem exists_pi_linearEquiv_completedStalk_uniform (B : FlatLocalBase S F) (n : ℕ) :
    ∃ k : ℕ, ∀ y ∈ (idealOnOpen S).support,
      letI := completedStalkBaseModule S F y B.φ
      Nonempty ((Fin k →
          (completedStalk (idealOnOpen S) F y ⧸
            (IsLocalRing.maximalIdeal B.R •
              (⊤ : Submodule B.R (completedStalk (idealOnOpen S) F y))))) ≃ₗ[B.R]
        ↥(IsLocalRing.maximalIdeal B.R ^ n •
          (⊤ : Submodule B.R (completedStalk (idealOnOpen S) F y ⧸
            (IsLocalRing.maximalIdeal B.R ^ (n + 1) •
              (⊤ : Submodule B.R (completedStalk (idealOnOpen S) F y))))))) := by
  obtain ⟨k, ⟨e⟩⟩ :=
    Stacks.Flatness.exists_pi_linearEquiv_gradedPiece (IsLocalRing.maximalIdeal B.R) n
  refine ⟨k, fun y hy => ?_⟩
  let := completedStalkBaseModule S F y B.φ
  have : Module.Flat B.R (completedStalk (idealOnOpen S) F y) := B.flat y hy
  exact ⟨Stacks.Flatness.piEquivSmulTopOfGradedPieceEquiv (IsLocalRing.maximalIdeal B.R)
    (completedStalk (idealOnOpen S) F y) n e⟩

/-- **Stacks Project, Tag 0EJU (the decomposition on the formal stalks, over the ring that
acts).** The decomposition of
`Stacks.Algebraization.exists_pi_linearEquiv_completedStalk_uniform` is a map of
`𝒪_{X,y}^∧`-modules, with the powers of `𝔪` replaced by the powers of the ideal `I 𝒪_{X,y}^∧`:
for one `k` and every point `y` of `U ∩ Y`, the graded piece
`Iⁿ F_y^∧ / Iⁿ⁺¹ F_y^∧` is `k` copies of `F_y^∧ / I F_y^∧`, `𝒪_{X,y}^∧`-linearly.

This is the second use of hypothesis (1) that
`Stacks.Algebraization.exists_pi_linearEquiv_completedStalk` leaves open. Over `R` the ideal in
sight is `𝔪` and the maps are only `R`-linear, which is no use to a sheaf: a morphism of
`𝒪_U`-modules is `𝒪_{U,y}`-linear on each stalk. Here `I = 𝔪 A` turns `𝔪` into the image of `S.I`
in the completed local ring — the ring that acts on `F_y^∧` — and the equivalence becomes linear
over it, hence over `𝒪_{U,y}` by restriction of scalars. The underlying algebra is
`Stacks.Flatness.towerPiEquivSmulTopOfGradedPieceEquiv`, which is the decomposition written in
`TensorProduct.AlgebraTensorModule` over the acting ring; as there, the number of copies and the
identification are chosen once, before `y` is named, so that one `k` serves the whole support. -/
theorem exists_pi_linearEquiv_completedStalk_uniform_linear (B : FlatLocalBase S F) (n : ℕ) :
    ∃ k : ℕ, ∀ y ∈ (idealOnOpen S).support,
      Nonempty ((Fin k → (completedStalk (idealOnOpen S) F y ⧸
          (completedLocalIdeal (idealOnOpen S) y •
            (⊤ : Submodule (completedLocalRing (idealOnOpen S) y)
              (completedStalk (idealOnOpen S) F y))))) ≃ₗ[completedLocalRing (idealOnOpen S) y]
        ↥(completedLocalIdeal (idealOnOpen S) y ^ n •
          (⊤ : Submodule (completedLocalRing (idealOnOpen S) y)
            (completedStalk (idealOnOpen S) F y ⧸
              (completedLocalIdeal (idealOnOpen S) y ^ (n + 1) •
                (⊤ : Submodule (completedLocalRing (idealOnOpen S) y)
                  (completedStalk (idealOnOpen S) F y))))))) := by
  obtain ⟨k, ⟨e⟩⟩ :=
    Stacks.Flatness.exists_pi_linearEquiv_gradedPiece (IsLocalRing.maximalIdeal B.R) n
  refine ⟨k, fun y hy => ?_⟩
  let : Algebra B.R (completedLocalRing (idealOnOpen S) y) :=
    ((baseToCompletedLocalRing S y).comp B.φ).toAlgebra
  let := completedStalkBaseModule S F y B.φ
  have : IsScalarTower B.R (completedLocalRing (idealOnOpen S) y)
      (completedStalk (idealOnOpen S) F y) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat B.R (completedStalk (idealOnOpen S) F y) := B.flat y hy
  have hJ : (IsLocalRing.maximalIdeal B.R).map
        (algebraMap B.R (completedLocalRing (idealOnOpen S) y)) =
      S.I.map (baseToCompletedLocalRing S y) := by
    rw [B.I_eq, Ideal.map_map]
    rfl
  rw [completedLocalIdeal_eq_map_baseToCompletedLocalRing, ← hJ]
  exact ⟨Stacks.Flatness.towerPiEquivSmulTopOfGradedPieceEquiv (IsLocalRing.maximalIdeal B.R)
    (completedStalk (idealOnOpen S) F y) (completedLocalRing (idealOnOpen S) y) n e⟩

/-- **Stacks Project, Tag 0EJU (the decomposition, on the stalks of the terms of `(F_n)`).**
For one `k` and every point `y` of `U ∩ Y` the stalk `Iⁿ⁺¹ F_(n+2),y` of the subsheaf
`Stacks.Algebraization.idealPowerSub S F n` is `k` copies of the stalk `F_(1,y)`, as modules over
the local ring `𝒪_{U,y}`.

This is the stalkwise content of the hypothesis `hdec` of the results below: `hdec` asks for an
isomorphism of sheaves `⨁_{i<k} F_1 ≅ Iⁿ⁺¹ F_(n+2)`, and a morphism of `𝒪_U`-modules is an
isomorphism exactly when it is bijective on every stalk
(`AlgebraicGeometry.SheafOfModules.isIso_iff_bijective_stalkMap`). What is still missing is the
*morphism*: this statement produces, for each `y`, an unrelated equivalence of stalks, with no
claim that the family comes from a map of sheaves. The raw material for the morphism is described
in the module docstring and is formal; what this supplies is the bijectivity it has to be checked
for. The morphism is `Stacks.Algebraization.idealPowerDesc`.

Two things are combined. The decomposition on the formal stalks
(`Stacks.Algebraization.exists_pi_linearEquiv_completedStalk_uniform_linear`) is linear over the
completed local ring, hence over `𝒪_{U,y}`, and its terms are quotients of `F_y^∧` by the powers
of `I 𝒪_{X,y}^∧`; those quotients are the stalks of the terms of `(F_n)` by
`Stacks.Algebraization.completedStalkQuotientEquivStalk`, and the submodule
`(I 𝒪_{X,y}^∧)ⁿ⁺¹ (F_y^∧/…)` has the same elements as `ℐ_yⁿ⁺¹ (F_y^∧/…)`, which that
identification carries to `ℐ_yⁿ⁺¹ F_(n+2),y`. The last is the stalk of `Iⁿ⁺¹ F_(n+2)` by
`Stacks.Algebraization.stalk_idealPowerMultiple`. -/
theorem exists_pi_linearEquiv_stalk_idealPowerSub (B : FlatLocalBase S F) (n : ℕ) :
    ∃ k : ℕ, ∀ y ∈ (idealOnOpen S).support,
      Nonempty ((Fin k → ((Stacks.ModuleSkyscraper.modulesStalkFunctor S.U.toScheme y).obj
            (F.obj.obj (op 0)))) ≃ₗ[S.U.toScheme.presheaf.stalk y]
        ↥(AlgebraicGeometry.IdealSheafData.stalk (idealOnOpen S) y ^ (n + 1) •
          (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
            ((Stacks.ModuleSkyscraper.modulesStalkFunctor S.U.toScheme y).obj
              (F.obj.obj (op (n + 1))))))) := by
  have : IsLocallyNoetherian S.U.toScheme := isLocallyNoetherian_of_isOpenImmersion S.U.ι
  obtain ⟨k, hk⟩ := exists_pi_linearEquiv_completedStalk_uniform_linear S F B (n + 1)
  refine ⟨k, fun y hy => (hk y hy).elim fun e => ⟨?_⟩⟩
  have eL0 : (completedStalk (idealOnOpen S) F y ⧸
        (completedLocalIdeal (idealOnOpen S) y •
          (⊤ : Submodule (completedLocalRing (idealOnOpen S) y)
            (completedStalk (idealOnOpen S) F y)))) ≃ₗ[S.U.toScheme.presheaf.stalk y]
      ((Stacks.ModuleSkyscraper.modulesStalkFunctor S.U.toScheme y).obj (F.obj.obj (op 0))) :=
    ((Submodule.quotEquivOfEq
        (completedLocalIdeal (idealOnOpen S) y •
          (⊤ : Submodule (completedLocalRing (idealOnOpen S) y)
            (completedStalk (idealOnOpen S) F y)))
        (completedLocalIdeal (idealOnOpen S) y ^ (0 + 1) •
          (⊤ : Submodule (completedLocalRing (idealOnOpen S) y)
            (completedStalk (idealOnOpen S) F y)))
        (by rw [zero_add, pow_one])).restrictScalars
      (S.U.toScheme.presheaf.stalk y)).trans (completedStalkQuotientEquivStalk F y 0)
  have eR : ↥(completedLocalIdeal (idealOnOpen S) y ^ (n + 1) •
        (⊤ : Submodule (completedLocalRing (idealOnOpen S) y)
          (completedStalk (idealOnOpen S) F y ⧸
            (completedLocalIdeal (idealOnOpen S) y ^ (n + 1 + 1) •
              (⊤ : Submodule (completedLocalRing (idealOnOpen S) y)
                (completedStalk (idealOnOpen S) F y)))))) ≃ₗ[S.U.toScheme.presheaf.stalk y]
      ↥(AlgebraicGeometry.IdealSheafData.stalk (idealOnOpen S) y ^ (n + 1) •
        (⊤ : Submodule (S.U.toScheme.presheaf.stalk y)
          ((Stacks.ModuleSkyscraper.modulesStalkFunctor S.U.toScheme y).obj
            (F.obj.obj (op (n + 1)))))) :=
    (Stacks.Flatness.restrictScalarsSubmoduleEquiv _ _
        (restrictScalars_completedLocalIdeal_pow_smul_top (idealOnOpen S) y _ (n + 1))).trans
      (((completedStalkQuotientEquivStalk F y (n + 1)).submoduleMap _).trans
        (LinearEquiv.ofEq _ _
          (map_smul_top_linearEquiv (completedStalkQuotientEquivStalk F y (n + 1)) _)))
  exact (LinearEquiv.piCongrRight fun _ : Fin k => eL0.symm).trans
    ((e.restrictScalars (S.U.toScheme.presheaf.stalk y)).trans eR)

/-- **Stacks Project, Tag 0EJU (the decomposition, on the stalk of the subsheaf `Iⁿ⁺¹ F_(n+2)`
itself).** `Stacks.Algebraization.exists_pi_linearEquiv_stalk_idealPowerSub` with the right-hand
side named as the stalk of `Stacks.Algebraization.idealPowerSub S F n`, the subsheaf `hdec` speaks
about: that stalk is `ℐ_yⁿ⁺¹ F_(n+2),y` by
`Stacks.Algebraization.stalk_idealPowerMultiple`.

So the two sides of `hdec` do have isomorphic stalks at every point of `U ∩ Y`, uniformly in the
number of copies. What `hdec` asks for and this does not give is a single morphism of sheaves
inducing them; that is `Stacks.Algebraization.idealPowerDesc`, and
`Stacks.Algebraization.exists_isoDirectSum_idealPowerSub` is `hdec`. -/
theorem exists_pi_linearEquiv_range_stalkMap_idealPowerSub (B : FlatLocalBase S F) (n : ℕ) :
    ∃ k : ℕ, ∀ y ∈ (idealOnOpen S).support,
      Nonempty ((Fin k → ((Stacks.ModuleSkyscraper.modulesStalkFunctor S.U.toScheme y).obj
            (F.obj.obj (op 0)))) ≃ₗ[S.U.toScheme.presheaf.stalk y]
        ↥(LinearMap.range ((Stacks.ModuleSkyscraper.modulesStalkFunctor S.U.toScheme y).map
          (C := S.U.toScheme.Modules) (idealPowerSub S F n).ι).hom)) := by
  have hcoh : _root_.SheafOfModules.IsCoherent.{u} (F.obj.obj (op (n + 1))) :=
    F.property.1 (n + 1)
  have : (F.obj.obj (op (n + 1))).IsQuasicoherent := isQuasicoherent_of_isCoherent _
  obtain ⟨k, hk⟩ := exists_pi_linearEquiv_stalk_idealPowerSub S F B n
  exact ⟨k, fun y hy => (hk y hy).elim fun e => ⟨e.trans (LinearEquiv.ofEq _ _
    (stalk_idealPowerMultiple (idealOnOpen S) (n + 1) (F.obj.obj (op (n + 1))) y).symm)⟩⟩

/-! ### The finiteness step -/

/-- Sheaves of modules on a scheme have finite biproducts, being an abelian category.

`CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts` is a theorem rather than an
instance, so the direct sums below are out of reach of instance search without this. -/
local instance hasFiniteBiproducts_schemeModules (X : Scheme.{u}) :
    HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Sections over `U`, as a functor to `A`-modules, are additive: addition of morphisms of
sheaves of modules is computed section by section, and restriction of scalars does not change
it. -/
local instance openSectionsFunctor_additive : (openSectionsFunctor S).Additive where
  map_add := by
    intros
    ext x
    rfl

/-- **Stacks Project, Tag 0EJU (the finiteness step of the proof).** If `Iⁿ F_(n+1)` is
isomorphic to a finite direct sum of copies of `F_1` for every `n`, and `H⁰(U, F_1)` is a finite
`A`-module, then every `H⁰(U, Iⁿ F_(n+1))` is a finite `A`-module.

In the source the decomposition comes from `Iⁿ F_(n+1) ≅ F_1 ⊗_κ 𝔪ⁿ/𝔪^(n+1)`, verified on
stalks from hypotheses (1) and (2); the form that obtains the decomposition from those two
hypotheses is `Stacks.Algebraization.finite_idealPowerSections_of_flatLocalBase`. -/
theorem finite_idealPowerSections_of_isoDirectSum
    (h0 : Module.Finite S.A ((globalSectionsSystem S F).obj (op 0)))
    (hdec : ∀ n : ℕ, ∃ k : ℕ, Nonempty ((⨁ fun _ : Fin k => F.obj.obj (op 0)) ≅
      (idealPowerSub S F n).toSheafOfModules)) :
    ∀ n, Module.Finite S.A (idealPowerSections S F n) := by
  intro n
  obtain ⟨k, ⟨e⟩⟩ := hdec n
  have h0' : Module.Finite S.A ((openSectionsFunctor S).obj (F.obj.obj (op 0))) := h0
  have h1 : Module.Finite S.A
      (Fin k → ((openSectionsFunctor S).obj (F.obj.obj (op 0)) : Type u)) :=
    Module.Finite.pi
  have h2 : Module.Finite S.A
      ((openSectionsFunctor S).obj (⨁ fun _ : Fin k => F.obj.obj (op 0))) :=
    Module.Finite.equiv
      (M := (Fin k → ((openSectionsFunctor S).obj (F.obj.obj (op 0)) : Type u)))
      (((openSectionsFunctor S).mapBiproduct (fun _ : Fin k => F.obj.obj (op 0))).trans
        (ModuleCat.biproductIsoPi _)).symm.toLinearEquiv
  exact Module.Finite.equiv ((openSectionsFunctor S).mapIso e).toLinearEquiv

/-- **Canonical extension from the decomposition (the reduction in Stacks 0EJU).** A coherent
`I`-adic system on the open
complement extends canonically to `X` as soon as its system of global sections has
Mittag-Leffler, the limit topology on the module of compatible sections is the `I`-adic
topology, `H⁰(U, F_1)` is a finite `A`-module, and every `Iⁿ F_(n+1)` is a finite direct sum of
copies of `F_1`.

The last hypothesis is what the source derives from a Noetherian local base `R → A` with
`I = 𝔪 A` over which the formal stalks along `U ∩ Y` are flat, recorded here as
`Stacks.Algebraization.FlatLocalBase`. The first two are conditions (a) and (b) of Stacks
0EHH. Stacks 0EJU itself, with all three discharged from its hypotheses, is
`Stacks.Algebraization.canonicallyExtends_of_flatLocalBase`. -/
theorem canonicallyExtends_of_isoDirectSum
    (hML : IsMittagLefflerCategorical (globalSectionsSystem S F))
    (htop : (⨅ n : ℕ, TopologicalSpace.induced
      (fun x : limitGlobalSections S F =>
        (limit.π (globalSectionsSystem S F) (op n)).hom x) ⊥) =
        S.I.adicModuleTopology (limitGlobalSections S F))
    (h0 : Module.Finite S.A ((globalSectionsSystem S F).obj (op 0)))
    (hdec : ∀ n : ℕ, ∃ k : ℕ, Nonempty ((⨁ fun _ : Fin k => F.obj.obj (op 0)) ≅
      (idealPowerSub S F n).toSheafOfModules)) :
    CanonicallyExtends S F :=
  canonicallyExtends_of_finite_idealPowerSections S F hML htop h0
    (finite_idealPowerSections_of_isoDirectSum S F h0 hdec)

/-- **The concluding sentence of Stacks 0EJU, from the decomposition.** Under the same hypotheses
as `Stacks.Algebraization.canonicallyExtends_of_isoDirectSum` — Mittag-Leffler
and limit-topology conditions (a), (b) of Stacks 0EHH, finiteness of `H⁰(U, F_1)`, and the
direct-sum decomposition of every `Iⁿ F_(n+1)` — if moreover `A` is `I`-adically complete, then
`(F_n)` is the completion of a coherent `𝒪_U`-module.

The clause of Stacks 0EJU itself, with these hypotheses discharged, is
`Stacks.Algebraization.essImage_completionFunctor_of_flatLocalBase`.
The proof is the same composite that proves this for the sibling Tag 0EHH,
`Stacks.Algebraization.essImage_completionFunctor_of_finite_limit_images`: canonical extension
by `Stacks.Algebraization.canonicallyExtends_of_isoDirectSum`, then part (2) of Tag 0EIR
(`Stacks.Algebraization.extendsToX_kerComapSystem_of_canonicallyExtends`) turns that into
extendability to `X`, and completeness of `A` then runs the chain of Tag 0EIL. -/
theorem essImage_completionFunctor_of_isoDirectSum [IsAdicComplete S.I S.A]
    (hML : IsMittagLefflerCategorical (globalSectionsSystem S F))
    (htop : (⨅ n : ℕ, TopologicalSpace.induced
      (fun x : limitGlobalSections S F =>
        (limit.π (globalSectionsSystem S F) (op n)).hom x) ⊥) =
        S.I.adicModuleTopology (limitGlobalSections S F))
    (h0 : Module.Finite S.A ((globalSectionsSystem S F).obj (op 0)))
    (hdec : ∀ n : ℕ, ∃ k : ℕ, Nonempty ((⨁ fun _ : Fin k => F.obj.obj (op 0)) ≅
      (idealPowerSub S F n).toSheafOfModules)) :
    (completionFunctor S.U.toScheme (idealOnOpen S)).essImage F :=
  essImage_completionFunctor_congr (idealOnOpen_eq_ker_comap S) F.property
    (isCoherentAdicSystem_kerComap S F)
    ((isCompletion_iff_ofRestriction S (kerComapSystem S F)).mpr
      ((isCompletionOfRestriction_iff_isRestrictionOfCompletion S (kerComapSystem S F)).mpr
        (isRestrictionOfCompletion_of_extendsToX S (kerComapSystem S F)
          (extendsToX_kerComapSystem_of_canonicallyExtends S F
            (canonicallyExtends_of_isoDirectSum S F hML htop h0 hdec)))))

end Stacks.Algebraization

end
