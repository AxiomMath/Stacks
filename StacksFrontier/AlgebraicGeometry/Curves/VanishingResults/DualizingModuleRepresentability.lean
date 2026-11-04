module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplexLowerVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafClauseFive
public import StacksFrontier.AlgebraicGeometry.Duality.CohomologyHypercohomology
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDualitySupplement
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingExistenceSupplement

/-!
# The dualizing module of a proper scheme over a field represents `ℱ ↦ H^d(X, ℱ)^∨`

Let `k` be a field and `f : X ⟶ Spec k` a proper morphism with `X` of topological Krull dimension
at most `d`. The dualizing complex is `ω_X^• = f^×(𝒪_{Spec k})`
(`Stacks.Duality.dualizingComplexOverField`) and the dualizing module is its cohomology sheaf in
the lowest degree it can occupy,

  `ω_X = H^{-d}(ω_X^•)`.

This file proves that `ω_X` represents the functor

  `ℱ ↦ Hom_k(H^d(X, ℱ), k)`

on the quasi-coherent `𝒪_X`-modules, naturally in `ℱ`. This is [Stacks, Tag 0AWP]
(Lemma 48.22.5) in the case where the base ring is a field, with the dualizing complex spelled
as the concrete `f^×(𝒪_{Spec k})` and the cohomology as `AlgebraicGeometry.cohomologyOverField`.
The tag itself, over an arbitrary Noetherian local base, is registered on
`Stacks.Duality.dualizingModuleRepresentableBy` in
`Curves/VanishingResults/DualizingModuleRepresentabilityLocalBase.lean`; this file is not a
registration of it.

## What the source says, and what is proved here

[Stacks, Tag 0AWP] takes the situation of Example [Stacks, Tag 0AWI]: a Noetherian local ring
`(A, 𝔪, κ)`, a normalized dualizing complex `ω_A^•` on `S = Spec(A)`, a proper `f : X ⟶ S`, the
complex `ω_X^• = f^!ω_S^•` and the module `ω_X = H^{-dim(X)}(ω_X^•)`. With `d = dim(X_s)` the
dimension of the closed fibre and under the hypothesis `dim(X) = d + dim(A)`, it asserts that
`ω_X` represents `ℱ ↦ Hom_A(H^d(X, ℱ), ω_A)` on the coherent `𝒪_X`-modules.

Specialising `A` to a field `k` makes every ingredient of that setup explicit and discharges its
hypothesis:

* `k` is a Noetherian local ring with `𝔪 = 0`, `κ = k` and `dim(A) = 0`;
* `ω_A^• = k[0]`, which is a normalized dualizing complex over `k`, so `ω_S^• = 𝒪_{Spec k}` and
  `ω_A = H^0(k[0]) = k`; the target of the represented functor is therefore
  `Hom_k(H^d(X, ℱ), k)`;
* `S = Spec(k)` has one point `s`, so `X_s = X` and `d = dim(X_s) = dim(X)`;
* the hypothesis `dim(X) = d + dim(A)` reads `dim(X) = dim(X) + 0` and holds for every `X`;
* `f^! = f^×` for a proper morphism ([Stacks, Tag 0AU3]), so
  `ω_X^• = f^×(𝒪_{Spec k}) = Stacks.Duality.dualizingComplexOverField f`.

Two things here are *more* general than the source rather than less. The represented functor is
taken on the quasi-coherent modules, not only on the coherent ones; and the dimension enters as
`dim(X) ≤ d` rather than `dim(X) = d`, which is all the proof uses — at `dim(X) = d`, the case
the tag is about, `H^{-d}(ω_X^•)` is the dualizing module `ω_X` of [Stacks, Tag 0AWI], while for
`dim(X) < d` both sides of the identification vanish and the statement is empty.

A base ring of positive dimension is the subject of `DualizingModuleRepresentabilityLocalBase.lean`
in this directory, where the tag is proved in full.

## Main definitions

* `Stacks.Duality.dualizingModuleRepresentability`: [Stacks, Tag 0AWP] over a field — the
  identification `Hom_{𝒪_X}(ℱ, H^{-d}(ω_X^•)) = Hom_k(H^d(X, ℱ), k)`.

## Main results

* `Stacks.Duality.dualizingModuleRepresentability_naturality`: the identification is natural in
  `ℱ`, which is what makes it a representation of the functor rather than a family of
  bijections.
* `Stacks.Duality.dualizingModuleRepresentabilitySquare`: the naturality square before the two
  ends are read as a map of `k`-vector spaces.

## The argument

The source's chain of five equalities is

  `Hom_X(ℱ, ω_X) = Ext^{-dim(X)}_X(ℱ, ω_X^•) = Hom_X(ℱ[dim(X)], ω_X^•)`
  `= Hom_X(ℱ[dim(X)], f^!(ω_A^•)) = Hom_S(Rf_*ℱ[dim(X)], ω_A^•) = Hom_A(H^d(X, ℱ), ω_A)`.

Over a field the last two steps are a single statement — clause (4) of
[Stacks, Tag 0BS2] in degree zero, `Stacks.Duality.dualityAddEquivZero`, which is the adjunction
`Rf_* ⊣ f^×` composed with the identification of `Hom_{D(k)}(RΓ(X, K), k[0])` with the `k`-linear
dual of `H^0(X, K)` and holds for every object of `D_QCoh(𝒪_X)`. The first two steps are
`Stacks.Duality.dualityAddEquiv`, assembled in
`Curves/VanishingResults/DualizingSheafClauseFive.lean` in degree `-m` for an arbitrary `m`: the
functor placing a module in degree `-m` is fully faithful, and for a source in `D^{≤ -m}`
composition with `τ^{≤ -m}(ω_X^•) ⟶ ω_X^•` is bijective, so

  `Hom_{𝒪_X}(ℱ, H^{-m}(ω_X^•)) = Hom_{D(𝒪_X)}(ℱ[0]⟦m⟧, τ^{≤ -m}(ω_X^•))`
  `= Hom_{D(𝒪_X)}(ℱ[0]⟦m⟧, ω_X^•)`.

The single input that fixes `m = d` is that `ω_X^•` has no cohomology below degree `-d`, which is
`Stacks.Duality.isGE_dualizingComplexOverField_of_dim_le`. That is proved from clause (4) and
Grothendieck's vanishing theorem alone: the truncation `τ^{≤ -d-1}(ω_X^•)` has quasi-coherent
cohomology and lies in `D^{≤ -d-1}`, so `RΓ(X, -)` of it lies in `D^{≤ -1}` by the amplitude
bound `AlgebraicGeometry.isLE_derivedGlobalSectionsOver_obj_of_topologicalKrullDim_le`; its `H^0`
therefore vanishes, clause (4) makes `Hom(τ^{≤ -d-1}(ω_X^•), ω_X^•)` trivial, and the canonical
map being zero while an isomorphism on `H^j` for `j ≤ -d-1` forces those `H^j` to vanish.

**Nothing is carried.** In particular no dualizing-complex hypothesis is needed: the statement is
about the *concrete* complex `f^×(𝒪_{Spec k})`, and the route above never uses that it is a
dualizing complex in the sense of [Stacks, Tag 0A87] — which is as well, since
`Stacks.Duality.IsDualizingComplex (dualizingComplexOverField f)` is proved nowhere in this
development.

**No Cohen–Macaulay hypothesis and no equidimensionality.** The source's `ω_X` is the *first*
nonvanishing cohomology sheaf of `ω_X^•`; here `H^{-d}(ω_X^•)` is simply the sheaf in degree
`-d`, which is the same module whenever `dim(X) = d`, by the vanishing above. Whether it is
nonzero is not asserted, and is false for instance on the empty scheme.

## The general base

Over a Noetherian local `A` of positive dimension the statement is
`Stacks.Duality.dualizingModuleRepresentableBy`, which carries nothing: there the vanishing of
`ω_X^•` below `-dim(X)` is obtained from [Stacks, Tag 0A9I] and the closed-fibre bound of
Cohomology of Schemes Lemma 30.20.9, rather than from Grothendieck vanishing on `X`.

## Where this file sits

It is in `Curves/VanishingResults/` rather than in `Duality/` because the chain it composes and
the amplitude bound it rests on are there; nothing in it is about curves, and `d = 1` recovers
clause (5) of [Stacks, Tag 0BS2], `Stacks.Duality.clauseFiveAddEquiv`.

## References

* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0AWP](https://stacks.math.columbia.edu/tag/0AWP)
* [Stacks Project, Tag 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Duality

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]

omit [IsProper f] in
/-- **The naturality square of the field-base case of [Stacks, Tag 0AWP], before the two ends
are read as a map of `k`-vector spaces.** The comparison `H^d(X, ℱ) = H^d(X, ℱ[0])` intertwines
`AlgebraicGeometry.cohomologyOverFieldMap` with the map `ℱ ⟶ 𝒢` induces on hypercohomology; this
is that compatibility with a functional on the hypercohomology of `𝒢[0]` appended. -/
theorem dualizingModuleRepresentabilitySquare (d : ℕ) {F G : X.Modules} (u : F ⟶ G)
    (α : derivedCohomologyOverField f ((DerivedCategory.singleFunctor X.Modules 0).obj G)
      (d : ℤ) ⟶ ModuleCat.of k k) :
    (cohomologyOverFieldIsoDerivedCohomologyOverField k f F d).hom ≫
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) (d : ℤ)).map
            ((derivedGlobalSectionsOver f).map
              ((DerivedCategory.singleFunctor X.Modules 0).map u)) ≫ α) =
      cohomologyOverFieldMap k f u d ≫
        (cohomologyOverFieldIsoDerivedCohomologyOverField k f G d).hom ≫ α :=
  Eq.trans (Category.assoc _ _ _).symm <|
    Eq.trans
      (congrArg (fun z => z ≫ α)
        (cohomologyOverFieldIsoDerivedCohomologyOverField_cohomologyOverFieldMap k f d u).symm)
      (Category.assoc _ _ _)

/-- **The case of a field base of [Stacks, Tag 0AWP].** Let `k` be a field and `f : X ⟶ Spec k`
proper with `X` of topological Krull dimension at most `d`. Then the dualizing module
`ω_X = H^{-d}(f^×(𝒪_{Spec k}))` represents the functor

  `ℱ ↦ Hom_k(H^d(X, ℱ), k)`

on the quasi-coherent `𝒪_X`-modules: there is an isomorphism of abelian groups

  `Hom_{𝒪_X}(ℱ, ω_X) ≅ Hom_k(H^d(X, ℱ), k)`,

natural in `ℱ` by `Stacks.Duality.dualizingModuleRepresentability_naturality`.

This is Lemma 48.22.5 in the case `A = k`: there `d` is the dimension of the closed fibre, which
over a field is `X` itself, and the lemma's hypothesis `dim(X) = d + dim(A)` is automatic because
`dim(k) = 0`; the represented functor's target `Hom_A(H^d(X, ℱ), ω_A)` is `Hom_k(H^d(X, ℱ), k)`
because `ω_A = H^0(k[0]) = k`. See the module documentation for the full dictionary. The tag
itself, over an arbitrary Noetherian local base, is
`Stacks.Duality.dualizingModuleRepresentableBy`. -/
def dualizingModuleRepresentability (d : ℕ)
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (F : X.Modules)
    (hF : F.IsQuasicoherent) :
    (F ⟶ dualizingModuleOverField f (d : ℤ)) ≃+ (cohomologyOverField k f F d →ₗ[k] k) :=
  (dualityAddEquiv f (d : ℤ) (isGE_dualizingComplexOverField_of_dim_le f hdim) F hF).trans
    (derivedCohomologyOverFieldDualAddEquiv k f F d (d : ℤ) rfl)

/-- The functional `dualizingModuleRepresentability f d hdim F hF φ` on `H^d(X, ℱ)` is the
composite of the identification `H^d(X, ℱ) = H^0(X, ℱ[0]⟦d⟧)` with the image under
`Stacks.Duality.dualityAddEquivZero` of `φ[0]⟦d⟧` followed by the canonical map
`H^{-d}(ω_X^•)[0]⟦d⟧ ⟶ ω_X^•`. -/
theorem dualizingModuleRepresentability_apply (d : ℕ)
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (F : X.Modules)
    (hF : F.IsQuasicoherent) (φ : F ⟶ dualizingModuleOverField f (d : ℤ)) :
    dualizingModuleRepresentability f d hdim F hF φ =
      ModuleCat.homAddEquiv
        ((cohomologyOverFieldIsoDerivedCohomologyOverField k f F d).hom ≫
          (derivedCohomologyShiftIso f
              ((DerivedCategory.singleFunctor X.Modules 0).obj F) (d : ℤ)).inv ≫
            dualityAddEquivZero f (shiftQuasiCoherent (singleQuasiCoherent F hF 0) (d : ℤ))
              ((shiftFunctor (DerivedCategory X.Modules) (d : ℤ)).map
                  ((DerivedCategory.singleFunctor X.Modules 0).map φ) ≫
                singleShiftToDualizingComplex f (d : ℤ)
                  (isGE_dualizingComplexOverField_of_dim_le f hdim))) :=
  congrArg (fun z => ModuleCat.homAddEquiv
      ((cohomologyOverFieldIsoDerivedCohomologyOverField k f F d).hom ≫ z))
    (dualityAddEquiv_apply f (d : ℤ)
      (isGE_dualizingComplexOverField_of_dim_le f hdim) F hF φ)

/-- **The field-base case of [Stacks, Tag 0AWP] is natural in the module**: precomposing a map
`𝒢 ⟶ ω_X` with `u : ℱ ⟶ 𝒢` corresponds to precomposing the functional on `H^d(X, 𝒢)` with
`H^d(X, u)`. This is what makes `ω_X` *represent* the functor rather than merely have the right
Hom-groups: the source's use of the universal property — "the composition `ω ⟶ ℱ ⟶ ω` is the
identity" — consumes exactly this. -/
theorem dualizingModuleRepresentability_naturality (d : ℕ)
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (F G : X.Modules)
    (hF : F.IsQuasicoherent) (hG : G.IsQuasicoherent) (u : F ⟶ G)
    (φ : G ⟶ dualizingModuleOverField f (d : ℤ)) :
    dualizingModuleRepresentability f d hdim F hF (u ≫ φ) =
      (dualizingModuleRepresentability f d hdim G hG φ).comp
        (cohomologyOverFieldMap k f u d).hom := by
  refine Eq.trans (congrArg (fun z =>
      derivedCohomologyOverFieldDualAddEquiv k f F d (d : ℤ) rfl z)
    (dualityAddEquiv_naturality f (d : ℤ)
      (isGE_dualizingComplexOverField_of_dim_le f hdim) F G hF hG u φ)) ?_
  refine Eq.trans (congrArg (fun z => ModuleCat.homAddEquiv z)
    (dualizingModuleRepresentabilitySquare f d u
      (dualityAddEquiv f (d : ℤ)
        (isGE_dualizingComplexOverField_of_dim_le f hdim) G hG φ))) ?_
  rfl

end Stacks.Duality

end
