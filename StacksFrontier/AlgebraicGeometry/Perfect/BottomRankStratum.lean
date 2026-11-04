module

public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiBaseChange
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Sheaf
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.Modules.SpecFieldModules
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedPullbackTopDegree
public import StacksFrontier.AlgebraicGeometry.Flatness.FittingStratification.RankStratumFinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# The locus where the bottom cohomology of a derived pullback is locally free of a given rank

Let `X` be a scheme, `E` an object of the derived category of sheaves of modules on `X`, `a` an
integer and `r` a natural number. A morphism of schemes `f : Y ⟶ X` is *universally of bottom
rank `r`* when, for every further morphism `g : Y' ⟶ Y`, the `𝒪_{Y'}`-module `H^a(L(g ∘ f)^* E)`
is finite locally free of rank `r`. This condition is visibly stable under precomposition, and
taking `g` the identity it implies that `H^a(Lf^* E)` itself is finite locally free of rank `r`.

A locally closed immersion `j : Z ⟶ X` is a *bottom rank `r` stratum* for `E` in degree `a` when
`H^a(Lj^* E)` is finite locally free of rank `r` and a morphism `f : Y ⟶ X` factors through `j`
exactly when it is universally of bottom rank `r`. These are the two descriptions by which
[stacks 0BDL] characterises its locally closed subscheme.

Two facts about this notion are proved. First, the characterisation determines the stratum: any
two bottom rank `r` strata for the same data are related by a unique isomorphism over `X`. The
hypothesis gives this at once, because a stratum factors through itself through the identity and
so is itself universally of bottom rank `r`; the two resulting morphisms over `X` are mutually
inverse because a locally closed immersion is a monomorphism. Second, a morphism universally of
bottom rank `r` has derived-fibre Betti number `β_a` equal to `r` at every point of its image:
pulling back along the canonical morphism from the spectrum of a residue field gives a module
over a field which is finite locally free of rank `r`, hence of dimension `r`, and base change
for `β_a` ([stacks 0BDI]) transports that dimension down to `X`.

For `E` a finite type quasi-coherent `𝒪_X`-module `F` placed in degree `a`, the bottom cohomology
of a derived pullback is the ordinary pullback of `F`, so the rank `r` Fitting stratum of `F`
([stacks 05P8]) is a bottom rank `r` stratum. For such an `E` the further assertions of
[stacks 0BDL] are also proved directly: the base-change formula
`H^a(L(g ∘ j)^* E) ≅ g^* H^a(Lj^* E)`, which here is a composite of the two canonical
identifications with an ordinary pullback of `F`; the finite presentation of the stratum when `F`
is finitely presented; the criterion that a morphism factors through the stratum exactly when
`H^a(Lf^* E)` is finite locally free of rank `r`, which for a module needs no bound on `β_a`; and
the closedness of the stratum when `F` needs at most `r` generators near every point, which for a
module is the bound `β_a ≤ r`. The general case, where `E` is perfect of Tor amplitude in
`[a, b]`, is `AlgebraicGeometry.BottomRankStratum.exists_isBottomRankStratum`.

## Main definitions

* `AlgebraicGeometry.BottomRankStratum.pullbackHomology`: the `𝒪_Y`-module `H^a(Lf^* E)`.
* `AlgebraicGeometry.BottomRankStratum.IsUniversallyFreeBottom`: the condition on `f : Y ⟶ X`
  that `H^a(L(g ∘ f)^* E)` be finite locally free of rank `r` for every `g : Y' ⟶ Y`.
* `AlgebraicGeometry.BottomRankStratum.IsBottomRankStratum`: the condition on a morphism
  `j : Z ⟶ X` of being a locally closed immersion satisfying the two descriptions above.

## Main results

* `AlgebraicGeometry.BottomRankStratum.pullbackHomologyCompIso`: the identification
  `H^a(Lg^*(Lf^* E)) ≅ H^a(L(g ∘ f)^* E)`.
* `AlgebraicGeometry.BottomRankStratum.IsUniversallyFreeBottom.comp` and
  `AlgebraicGeometry.BottomRankStratum.IsUniversallyFreeBottom.self`: the condition is stable
  under precomposition, and implies finite local freeness of rank `r` of `H^a(Lf^* E)`.
* `AlgebraicGeometry.BottomRankStratum.IsBottomRankStratum.isUniversallyFreeBottom`: a bottom
  rank `r` stratum is itself universally of bottom rank `r`.
* `AlgebraicGeometry.BottomRankStratum.IsBottomRankStratum.existsUnique_iso`: two bottom rank `r`
  strata for the same data are related by a unique isomorphism over `X`.
* `AlgebraicGeometry.BottomRankStratum.derivedFiberBetti_eq_of_isUniversallyFreeBottom`: a
  morphism universally of bottom rank `r` has `β_a = r` at every point of its image.
* `AlgebraicGeometry.BottomRankStratum.isBottomRankStratum_fittingRankStratum`: for a finite type
  quasi-coherent module placed in degree `a`, the rank `r` Fitting stratum is a bottom rank `r`
  stratum.
* `AlgebraicGeometry.BottomRankStratum.pullbackHomologySingleCompIso`: for a module placed in
  degree `a`, the canonical identification `H^a(L(g ∘ j)^* E) ≅ g^* H^a(Lj^* E)`.
* `AlgebraicGeometry.BottomRankStratum.factorsThrough_fittingRankStratum_iff`: a morphism factors
  through the rank `r` Fitting stratum exactly when `H^a(Lf^* E)` is finite locally free of
  rank `r`.
* `AlgebraicGeometry.BottomRankStratum.isBottomRankStratum_finitePresentation_fittingRankStratum`:
  for a finitely presented module placed in degree `a`, the rank `r` Fitting stratum is a bottom
  rank `r` stratum and its structural morphism is of finite presentation.
* `AlgebraicGeometry.BottomRankStratum.isClosedImmersion_fittingRankStratum_of_isGeneratedByNear`:
  the rank `r` Fitting stratum is a closed subscheme when the module needs at most `r` generators
  near every point.

## Implementation notes

The rank is a natural number, where the source says `r ≥ 0`.

The universal condition quantifies over all morphisms `g : Y' ⟶ Y` out of the source rather than
asking finite local freeness of `H^a(Lf^* E)` alone. That is what the source asks, and it is what
makes the condition behave: finite local freeness of `H^a(Lf^* E)` is not by itself inherited by
further pullbacks, since the bottom cohomology of a derived pullback is not the pullback of the
bottom cohomology.

Stability under precomposition is associativity of composition, and nothing else: the condition
for `g ∘ f` quantifies over morphisms `k` and asks about `(k ∘ g) ∘ f`.

`β_a` is `AlgebraicGeometry.DerivedFibreBetti.derivedFiberBetti`, the dimension over the residue
field `κ(x)` of the degree-`a` cohomology of the derived fibre at `x`, read through global
sections on `Spec κ(x)`. Reading it off a finite locally free module of rank `r` on the spectrum
of a field is `finrank_moduleSpecΓ_eq_of_isFiniteLocallyFreeOfRank`: over a field every sheaf of
modules on the spectrum is the sheaf associated to its global sections
(`AlgebraicGeometry.SpecField.isIso_fromTildeΓ`), finite local freeness of rank `r` passes
through that identification to the module of global sections
(`tilde_isFiniteLocallyFreeOfRank_iff`), and over a field a finite locally free module of rank
`r` has dimension `r` (`Module.IsFiniteLocallyFreeOfRank.finrank_eq`). The pseudo-coherence
argument of `β_a` is the only hypothesis the base-change statement needs, so no perfectness
enters that result.

The derived category used throughout is the one given by `HasDerivedCategory.standard`, installed
as a local instance. That is the model in which `β_a` and the derived pullback of
`StacksFrontier.AlgebraicGeometry.Perfect.DerivedFibreBettiBaseChange` are stated, and the model of
the neighbouring results on perfect complexes; a statement proved at one model of
`HasDerivedCategory` says nothing about another.

The derived pullback is the one of
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback`, indexed by morphisms of
ringed spaces, so a morphism of schemes enters it as `f.toLRSHom.toShHom`; its everywhere-defined
existence is an instance. The composition isomorphism is the unconditional one of
`Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical`, transported along
`comp_toLRSHom_toShHom`, which is compatibility of that passage with composition.

## References

* [The Stacks Project, Lemma 36.31.4 (0BDL)](https://stacks.math.columbia.edu/tag/0BDL)
* [The Stacks Project, Lemma 36.31.1 (0BDI)](https://stacks.math.columbia.edu/tag/0BDI)
* [The Stacks Project, Lemma 15.77.7 (0BCD)](https://stacks.math.columbia.edu/tag/0BCD)
* [The Stacks Project, Lemma 15.125.6 (0EWY)](https://stacks.math.columbia.edu/tag/0EWY)
* [The Stacks Project, Lemma 29.47.4 (05P8)](https://stacks.math.columbia.edu/tag/05P8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.BottomRankStratum

variable {X : Scheme.{u}}

/-! ### The bottom cohomology of a derived pullback -/

/-- **The `𝒪_Y`-module `H^a(Lf^* E)`.** The degree-`a` cohomology sheaf of the derived pullback
of `E` along `f : Y ⟶ X`. -/
public def pullbackHomology (E : DerivedCategory X.Modules) (a : ℤ) {Y : Scheme.{u}} (f : Y ⟶ X) :
    Y.Modules :=
  (DerivedCategory.homologyFunctor Y.Modules a).obj
    ((derivedPullback f.toLRSHom.toShHom).obj E)

/-- Passing from a morphism of schemes to the underlying morphism of ringed spaces is compatible
with composition. -/
public theorem comp_toLRSHom_toShHom {Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X) :
    (g ≫ f).toLRSHom.toShHom = g.toLRSHom.toShHom ≫ f.toLRSHom.toShHom := by
  simp only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom]

/-- **`H^a(Lg^*(Lf^* E)) ≅ H^a(L(g ∘ f)^* E)`.** The composition isomorphism for the derived
pullback, read on degree-`a` cohomology. -/
public def pullbackHomologyCompIso (E : DerivedCategory X.Modules) (a : ℤ)
    {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (f : Y ⟶ X) :
    pullbackHomology ((derivedPullback f.toLRSHom.toShHom).obj E) a g ≅
      pullbackHomology E a (g ≫ f) :=
  (DerivedCategory.homologyFunctor Y'.Modules a).mapIso
      ((derivedPullbackCompIsoCanonical g.toLRSHom.toShHom f.toLRSHom.toShHom).app E) ≪≫
    eqToIso (congrArg
      (fun k => (DerivedCategory.homologyFunctor Y'.Modules a).obj
        ((derivedPullback.{u, u + 1, u + 1} k).obj E))
      (comp_toLRSHom_toShHom g f).symm)

/-! ### Morphisms universally of bottom rank `r` -/

/-- **A morphism universally of bottom rank `r`.** The morphism `f : Y ⟶ X` is universally of
bottom rank `r` for `E` in degree `a` when, for every morphism `g : Y' ⟶ Y`, the `𝒪_{Y'}`-module
`H^a(L(g ∘ f)^* E)` is finite locally free of rank `r`.

This is the right-hand side of description (2) of [stacks 0BDL]. -/
public def IsUniversallyFreeBottom (E : DerivedCategory X.Modules) (a : ℤ) (r : ℕ)
    {Y : Scheme.{u}} (f : Y ⟶ X) : Prop :=
  ∀ (Y' : Scheme.{u}) (g : Y' ⟶ Y),
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (pullbackHomology E a (g ≫ f)) r

variable {E : DerivedCategory X.Modules} {a : ℤ} {r : ℕ}

/-- **Being universally of bottom rank `r` is stable under precomposition.** The condition for
`g ∘ f` quantifies over the morphisms `k` and asks about `(k ∘ g) ∘ f`, so it is the condition
for `f` read at the composites `k ∘ g`. -/
public theorem IsUniversallyFreeBottom.comp {Y Y' : Scheme.{u}} {f : Y ⟶ X}
    (h : IsUniversallyFreeBottom E a r f) (g : Y' ⟶ Y) :
    IsUniversallyFreeBottom E a r (g ≫ f) := by
  intro Y'' k
  simpa only [Category.assoc] using h Y'' (k ≫ g)

/-- **A morphism universally of bottom rank `r` has `H^a(Lf^* E)` finite locally free of rank
`r`.** This is the condition at the identity. -/
public theorem IsUniversallyFreeBottom.self {Y : Scheme.{u}} {f : Y ⟶ X}
    (h : IsUniversallyFreeBottom E a r f) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (pullbackHomology E a f) r := by
  simpa only [Category.id_comp] using h Y (𝟙 Y)

/-! ### Bottom rank strata and their uniqueness -/

/-- **A bottom rank `r` stratum.** The morphism `j : Z ⟶ X` is a locally closed immersion,
`H^a(Lj^* E)` is finite locally free of rank `r`, and a morphism `f : Y ⟶ X` factors through `j`
exactly when it is universally of bottom rank `r`.

These are the two descriptions by which [stacks 0BDL] characterises its locally closed
subscheme. -/
public structure IsBottomRankStratum (E : DerivedCategory X.Modules) (a : ℤ) (r : ℕ)
    {Z : Scheme.{u}} (j : Z ⟶ X) : Prop where
  /-- `j` is a locally closed immersion, so `Z` is a locally closed subscheme of `X`. -/
  isImmersion : IsImmersion j
  /-- Description (1): `H^a(Lj^* E)` is finite locally free of rank `r`. -/
  freeRank : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
    (pullbackHomology E a j) r
  /-- Description (2): a morphism factors through `j` exactly when it is universally of bottom
  rank `r`. -/
  factorsThrough_iff : ∀ (Y : Scheme.{u}) (f : Y ⟶ X),
    (∃ g : Y ⟶ Z, g ≫ j = f) ↔ IsUniversallyFreeBottom E a r f

/-- **A bottom rank `r` stratum is itself universally of bottom rank `r`.** It factors through
itself through the identity, so description (2) applies to it. -/
public theorem IsBottomRankStratum.isUniversallyFreeBottom {Z : Scheme.{u}} {j : Z ⟶ X}
    (h : IsBottomRankStratum E a r j) : IsUniversallyFreeBottom E a r j :=
  (h.factorsThrough_iff Z j).1 ⟨𝟙 Z, Category.id_comp j⟩

/-- **Description (2) determines the stratum.** Two bottom rank `r` strata for the same `E`, `a`
and `r` are related by a unique isomorphism over `X`.

Each stratum is universally of bottom rank `r`, so each factors through the other; the two
factorisations compose to the identity because a locally closed immersion is a monomorphism, and
that same monomorphism property makes the morphism over `X`, hence the isomorphism, unique. -/
public theorem IsBottomRankStratum.existsUnique_iso {Z₁ Z₂ : Scheme.{u}} {j₁ : Z₁ ⟶ X}
    {j₂ : Z₂ ⟶ X} (h₁ : IsBottomRankStratum E a r j₁) (h₂ : IsBottomRankStratum E a r j₂) :
    ∃! e : Z₁ ≅ Z₂, e.hom ≫ j₂ = j₁ := by
  have := h₁.isImmersion
  have := h₂.isImmersion
  obtain ⟨g₁, hg₁⟩ := (h₂.factorsThrough_iff Z₁ j₁).2 h₁.isUniversallyFreeBottom
  obtain ⟨g₂, hg₂⟩ := (h₁.factorsThrough_iff Z₂ j₂).2 h₂.isUniversallyFreeBottom
  have h12 : g₁ ≫ g₂ = 𝟙 Z₁ := by
    refine (cancel_mono j₁).1 ?_
    rw [Category.assoc, hg₂, hg₁, Category.id_comp]
  have h21 : g₂ ≫ g₁ = 𝟙 Z₂ := by
    refine (cancel_mono j₂).1 ?_
    rw [Category.assoc, hg₁, hg₂, Category.id_comp]
  refine ⟨⟨g₁, g₂, h12, h21⟩, hg₁, fun e he => ?_⟩
  exact Iso.ext ((cancel_mono j₂).1 (he.trans hg₁.symm))

/-! ### The derived-fibre Betti number along such a morphism -/

/-- **Over a field a finite locally free sheaf of modules of rank `s` on the spectrum has global
sections of dimension `s`.** Over a field the sheaf is the one associated to its module of global
sections, so finite local freeness of rank `s` is that of the module, which over a field is
dimension `s`. -/
public theorem finrank_moduleSpecΓ_eq_of_isFiniteLocallyFreeOfRank {R : CommRingCat.{u}}
    (hR : IsField R) (M : (Spec R).Modules) (s : ℕ)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M s) :
    Module.finrank ↑R ↑(moduleSpecΓFunctor.obj M) = s := by
  let _ : Field ↑R := hR.toField
  have : IsIso (Scheme.Modules.fromTildeΓ (R := R) M) := SpecField.isIso_fromTildeΓ hR M
  let e : M ≅ AlgebraicGeometry.tilde (moduleSpecΓFunctor.obj M) :=
    (asIso (Scheme.Modules.fromTildeΓ (R := R) M)).symm
  exact Module.IsFiniteLocallyFreeOfRank.finrank_eq
    ((tilde_isFiniteLocallyFreeOfRank_iff ↑R ↑(moduleSpecΓFunctor.obj M) s).mp
      (Scheme.Modules.IsFiniteLocallyFreeOfRank.of_iso e
        ((Scheme.Modules.isFiniteLocallyFreeOfRank_iff M s).mpr h)))

/-- **A morphism universally of bottom rank `r` has `β_a = r` at every point of its image.**
Pulling back along the canonical morphism from the spectrum of the residue field of `y` gives a
sheaf of modules on the spectrum of a field which is finite locally free of rank `r`, hence of
dimension `r`; base change for the derived-fibre Betti function ([stacks 0BDI]) identifies that
dimension with `β_a` at the image of `y`.

This is the reduction with which the proof of [stacks 0BDL] begins — a morphism as in its
description (2) lands in the locus where `β_a ≤ r` — and is not itself a part of that tag. The
hypothesis on `E` is pseudo-coherence, which is what `β_a` needs; perfectness is not used. -/
public theorem derivedFiberBetti_eq_of_isUniversallyFreeBottom (E : DerivedCategory X.Modules)
    (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E) (a : ℤ) (r : ℕ)
    {Y : Scheme.{u}} {f : Y ⟶ X} (h : IsUniversallyFreeBottom E a r f) (y : Y) :
    DerivedFibreBetti.derivedFiberBetti X E hE a (f.base y) = r := by
  have h2 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (pullbackHomology ((derivedPullback f.toLRSHom.toShHom).obj E) a
        (Y.fromSpecResidueField y)) r :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      (pullbackHomologyCompIso E a (Y.fromSpecResidueField y) f).symm
      (h _ (Y.fromSpecResidueField y))
  have hbc := congrFun (DerivedFibreBetti.derivedFiberBetti_derivedPullback f E hE a) y
  simp only [Function.comp_apply] at hbc
  rw [← hbc]
  exact finrank_moduleSpecΓ_eq_of_isFiniteLocallyFreeOfRank (Field.toIsField _) _ r h2

/-! ### A module placed in one degree, and the Fitting rank stratum -/

/-- **For a module placed in degree `a`, the bottom cohomology of a derived pullback is the
ordinary pullback.** So finite local freeness of rank `s` of `H^a(Lf^*(F[-a]))` is that of
`f^* F`. -/
public theorem isFiniteLocallyFreeOfRank_pullbackHomology_single_iff (F : X.Modules) (a : ℤ)
    (s : ℕ) {Y : Scheme.{u}} (f : Y ⟶ X) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (pullbackHomology ((DerivedCategory.singleFunctor X.Modules a).obj F) a f) s ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback f).obj F) s := by
  have e := Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyDerivedPullbackSingleIso
    f.toLRSHom.toShHom F a
  exact ⟨AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e,
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} e.symm⟩

/-- **For a module placed in degree `a`, being universally of bottom rank `s` is finite local
freeness of rank `s` of the ordinary pullback.** The quantification over further morphisms costs
nothing here, because the ordinary pullback of a finite locally free module of rank `s` is again
one; that is the functoriality of the rank `s` functor of [stacks 05P8]. -/
public theorem isUniversallyFreeBottom_single_iff (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] (a : ℤ) (s : ℕ) {Y : Scheme.{u}} (f : Y ⟶ X) :
    IsUniversallyFreeBottom ((DerivedCategory.singleFunctor X.Modules a).obj F) a s f ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback f).obj F) s := by
  refine ⟨fun h => (isFiniteLocallyFreeOfRank_pullbackHomology_single_iff F a s f).1 h.self,
    fun h Y' g => ?_⟩
  rw [isFiniteLocallyFreeOfRank_pullbackHomology_single_iff]
  exact ((rankRFunctor X F s).map
    (Opposite.op (Over.homMk g rfl : Over.mk (g ≫ f) ⟶ Over.mk f)) ⟨⟨h⟩⟩).down.down

/-- **The rank `s` Fitting stratum is a bottom rank `s` stratum for a module placed in degree
`a`.** Its structural morphism is a locally closed immersion and it represents the rank `s`
functor of `F` ([stacks 05P8]), which for a module placed in degree `a` is the condition of being
universally of bottom rank `s`.

This is descriptions (1) and (2) of [stacks 0BDL] for an `E` which is a module placed in degree
`a`. -/
@[stacks 0BDL "parts (1) and (2), for E a finite type quasi-coherent module placed in degree a"]
public theorem isBottomRankStratum_fittingRankStratum (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] (a : ℤ) (s : ℕ) :
    IsBottomRankStratum ((DerivedCategory.singleFunctor X.Modules a).obj F) a s
      (fittingRankStratum F s).hom := by
  obtain ⟨rep⟩ := rankRFunctor_representableBy_fittingRankStratum F s
  refine ⟨isImmersion_fittingRankStratum F s, ?_, ?_⟩
  · rw [isFiniteLocallyFreeOfRank_pullbackHomology_single_iff]
    exact (rep.homEquiv (𝟙 (fittingRankStratum F s))).down.down
  · intro Y f
    rw [isUniversallyFreeBottom_single_iff]
    constructor
    · rintro ⟨g, hg⟩
      exact (rep.homEquiv (Over.homMk g hg : Over.mk f ⟶ fittingRankStratum F s)).down.down
    · intro h
      let φ := rep.homEquiv.symm (⟨⟨h⟩⟩ : (rankRFunctor X F s).obj (Opposite.op (Over.mk f)))
      exact ⟨φ.left, φ.w⟩

/-! ### Base change, finite presentation and the closed case -/

/-- **For a module placed in degree `a`, the bottom cohomology of a derived pullback is the
ordinary pullback, as the canonical map.** -/
public def pullbackHomologySingleIso (F : X.Modules) (a : ℤ) {Y : Scheme.{u}} (f : Y ⟶ X) :
    pullbackHomology ((DerivedCategory.singleFunctor X.Modules a).obj F) a f ≅
      (Scheme.Modules.pullback f).obj F :=
  Stacks.AlgebraicGeometry.TopDegreeBaseChange.homologyDerivedPullbackSingleIso
    f.toLRSHom.toShHom F a

/-- **`H^a(L(g ∘ j)^* E) ≅ g^* H^a(Lj^* E)` for `E` a module placed in degree `a`.** This is
part (3) of [stacks 0BDL]: a morphism factoring as `Y ⟶ Z ⟶ X` has its degree-`a` cohomology of
the derived pullback the ordinary pullback along `g` of the one on `Z`.

Both sides are identified with an ordinary pullback of `F` by `pullbackHomologySingleIso`, and
the two ordinary pullbacks are identified by `AlgebraicGeometry.Scheme.Modules.pullbackComp`, so
the isomorphism is a composite of canonical maps and not merely an abstract isomorphism of
locally free modules of the same rank. -/
@[stacks 0BDL "part (3), for E a module placed in degree a"]
public def pullbackHomologySingleCompIso (F : X.Modules) (a : ℤ) {Y Z : Scheme.{u}} (j : Z ⟶ X)
    (g : Y ⟶ Z) :
    pullbackHomology ((DerivedCategory.singleFunctor X.Modules a).obj F) a (g ≫ j) ≅
      (Scheme.Modules.pullback g).obj
        (pullbackHomology ((DerivedCategory.singleFunctor X.Modules a).obj F) a j) :=
  pullbackHomologySingleIso F a (g ≫ j) ≪≫
    ((Scheme.Modules.pullbackComp g j).app F).symm ≪≫
    (Scheme.Modules.pullback g).mapIso (pullbackHomologySingleIso F a j).symm

/-- **A morphism factors through the rank `s` Fitting stratum exactly when `H^a(Lf^* E)` is
finite locally free of rank `s`.** This is the equivalence of (a) and (b) in part (4) of
[stacks 0BDL] for `E` a module placed in degree `a`.

No bound on the derived-fibre Betti numbers is needed: the quantification over further morphisms
in description (2) costs nothing for a module placed in degree `a`, because the ordinary pullback
of a finite locally free module of rank `s` is again one. -/
@[stacks 0BDL "part (4), (a) iff (b), for E a finite type quasi-coherent module in degree a"]
public theorem factorsThrough_fittingRankStratum_iff (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] (a : ℤ) (s : ℕ) {Y : Scheme.{u}} (f : Y ⟶ X) :
    (∃ g : Y ⟶ (fittingRankStratum F s).left, g ≫ (fittingRankStratum F s).hom = f) ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        (pullbackHomology ((DerivedCategory.singleFunctor X.Modules a).obj F) a f) s := by
  rw [(isBottomRankStratum_fittingRankStratum F a s).factorsThrough_iff Y f,
    isUniversallyFreeBottom_single_iff, ← isFiniteLocallyFreeOfRank_pullbackHomology_single_iff]

/-- **The rank `s` Fitting stratum of a finitely presented module is a bottom rank `s` stratum
whose structural morphism is of finite presentation.** This is descriptions (1) and (2) of
[stacks 0BDL] together with its assertion that `j : Z ⟶ X` is of finite presentation, for `E` a
finitely presented module placed in degree `a`.

The finite presentation is `AlgebraicGeometry.finitePresentation_fittingRankStratum`; the two
halves are stated together because the tag's "moreover" is about the same `j` that descriptions
(1) and (2) characterise. -/
@[stacks 0BDL "parts (1), (2) and finite presentation, E a finitely presented module in degree a"]
public theorem isBottomRankStratum_finitePresentation_fittingRankStratum (F : X.Modules)
    [F.IsFinitePresentation] (a : ℤ) (s : ℕ) :
    IsBottomRankStratum ((DerivedCategory.singleFunctor X.Modules a).obj F) a s
        (@fittingRankStratum X F (SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F)
          (SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F) s).hom ∧
      FinitePresentation
        (@fittingRankStratum X F (SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F)
          (SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F) s).hom :=
  ⟨@isBottomRankStratum_fittingRankStratum X F
      (SheafOfModules.instIsFiniteTypeOfIsFinitePresentation F)
      (SheafOfModules.instIsQuasicoherentOfIsFinitePresentation F) a s,
    finitePresentation_fittingRankStratum F s⟩

/-- A module generated by `s` sections near every point of the base has `s`-th Fitting ideal the
unit ideal everywhere, so the open complement of its `s`-th Fitting closed subscheme is the whole
base. -/
private theorem fittingGeneratorOpen_eq_top_of_isGeneratedByNear (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (s : ℕ) (hgen : ∀ x : X, IsGeneratedByNear F s x) :
    fittingGeneratorOpen F s = ⊤ := by
  refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun x => ?_)
  show x ∉ Set.range (fittingClosedSubscheme F (s : ℤ)).hom.base
  rw [fittingClosedSubscheme_ofNat]
  show x ∉ Set.range (fittingIdeal F (s : ℤ)).subschemeι.base
  rw [Scheme.IdealSheafData.range_subschemeι]
  exact (Stacks.Divisors.stalk_eq_top_iff_notMem_support _ x).mp
    ((isGeneratedByNear_iff_fittingIdeal_stalk_eq_top F s x).mp (hgen x))

/-- **When the module is generated by `s` sections near every point, the rank `s` Fitting stratum
is a closed subscheme.** This is the closedness assertion of part (4) of [stacks 0BDL] for `E` a
module placed in degree `a`, with the hypothesis `β_a ≤ s` in the form it takes for such an `E`:
`β_a(x)` is the dimension of the fibre of `F` at `x`, so `β_a(x) ≤ s` says that `F` needs at most
`s` generators near `x`.

Under that hypothesis the `s`-th Fitting ideal is the unit ideal, so the open subscheme cut out
of the Fitting closed subscheme of index `s - 1` by the generator open of index `s` is the whole
of it, and the structural morphism of the stratum is that closed immersion up to an
isomorphism. -/
@[stacks 0BDL "part (4), closedness of j, E a module in degree a, Betti bound as generation"]
public theorem isClosedImmersion_fittingRankStratum_of_isGeneratedByNear (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (s : ℕ) (hgen : ∀ x : X, IsGeneratedByNear F s x) :
    IsClosedImmersion (fittingRankStratum F s).hom := by
  have hpre : (fittingClosedSubscheme F ((s : ℤ) - 1)).hom ⁻¹ᵁ fittingGeneratorOpen F s = ⊤ := by
    rw [fittingGeneratorOpen_eq_top_of_isGeneratedByNear F s hgen]; simp
  have hiso : IsIso ((fittingClosedSubscheme F ((s : ℤ) - 1)).hom ⁻¹ᵁ
      fittingGeneratorOpen F s).ι := by
    rw [hpre, ← Scheme.topIso_hom]; infer_instance
  show IsClosedImmersion (((fittingClosedSubscheme F ((s : ℤ) - 1)).hom ⁻¹ᵁ
    fittingGeneratorOpen F s).ι ≫ (fittingClosedSubscheme F ((s : ℤ) - 1)).hom)
  infer_instance

end AlgebraicGeometry.BottomRankStratum

end
