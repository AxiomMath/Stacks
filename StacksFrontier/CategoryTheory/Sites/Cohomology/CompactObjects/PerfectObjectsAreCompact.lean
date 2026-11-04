module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactnessFromCoverings.CompactnessFromFiniteCoverings
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.ExtensionByZeroIsCompact
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Triangulated.CompactObjects
import StacksCore.Tactic.StacksAttribute

/-!
# Compactness of a perfect object on a ringed site

Let `(C, O)` be a ringed site whose underlying site has a quasi-compact final object `X`, in
which every quasi-compact object has a cofinal system of finite coverings by quasi-compact
objects, and in which the fibre products occurring in such a covering are again quasi-compact.
**Stacks 09JC** asserts, for `K` a perfect object of `D(O)`, that

* **(a)** `K` is compact relative to the bounded-below part of `D(O)`: if `M = ⨁_{i ∈ I} M_i` is
  bounded below then `Hom(K, M) = ⨁_{i ∈ I} Hom(K, M_i)`; and
* **(b)** if `(C, O)` has finite cohomological dimension then `K` is a compact object of `D(O)`.

Both are proved here from the reduction the source performs, namely the identification
`Hom_{D(O)}(K, M) = H⁰(X, K^∨ ⊗^L_O M)`, functorial in `M`, together with the fact that
`K^∨ ⊗^L_O -` commutes with direct sums. Since `H⁰(X, -) = Hom_{D(O)}(j_{X!}O_X, -)`, that
reduction says precisely that `Hom(K, -)` is naturally isomorphic to
`Hom(j_{X!}O_X, T(-))` for a functor `T` commuting with the direct sums in question; the two
parts then follow from the compactness properties of `j_{X!}O_X` already in the library,
Stacks 0G22 for (a) and Stacks 094D for (b).

That reduction is **not formalized in this library** and is therefore an explicit hypothesis of
both tagged results; see "What this file assumes" below. The transfer itself is isolated in
`Stacks.Cohomology.bijective_cofanMap_of_homAddEquiv` and
`Stacks.Cohomology.isCompactObject_of_homAddEquiv`, which are statements about an arbitrary
preadditive category.

## Main results

* `Stacks.Cohomology.bijective_cofanMap_of_homAddEquiv`: the compactness map of `K` against a
  family is bijective as soon as the compactness map of `L` against its `T`-image is, given a
  natural additive bijection `(K ⟶ -) ≃+ (L ⟶ T(-))`.
* `Stacks.Cohomology.bijective_cofanMap_map_sigmaι`: the compactness map against the `T`-images
  of the coproduct inclusions is the compactness map against the inclusions of the coproduct of
  the `T`-images, when `T` preserves that coproduct.
* `Stacks.Cohomology.isCompactObject_of_homAddEquiv`: compactness of `K` transfers from
  compactness of `L` along such a natural bijection.
* `Stacks.Cohomology.hom_coproduct_bijective_of_isPerfect`: **Stacks 09JC (a)**, bounded-below
  compactness of a perfect object.
* `Stacks.Cohomology.isCompactObject_of_isPerfect`: **Stacks 09JC (b)**, compactness of a
  perfect object on a ringed site of finite cohomological dimension.

## What this file assumes

The source's reduction rests on Stacks 08JJ. All four of that tag's assertions are in the
library: `AlgebraicGeometry.RingedSite.isPerfect_derivedDual` (the dual of a perfect object is
perfect), `AlgebraicGeometry.RingedSite.isIso_derivedBidual_of_isPerfect` (`(K^∨)^∨ ≅ K`),
`AlgebraicGeometry.RingedSite.derivedDualTensorSheafHomIso` and
`AlgebraicGeometry.RingedSite.derivedDualTensorGlobalSectionsEquiv`. What is *absent* is the
identification `H⁰(C, M ⊗^L_O K^∨) = Hom_{D(O)}(K, M)` read off the **canonical** map, which is
what this file would need: that map is
`AlgebraicGeometry.RingedSite.derivedTensorDualGlobalSectionsMap` (Stacks 08JD), the equivalence
just named is built instead from the diagonal of Stacks 0BYS, and, as
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.Duals` records, the two are nowhere compared,
so no declaration in the library asserts that the canonical map is bijective. Neither is the
commutation of `K^∨ ⊗^L_O -` with direct sums. Both tagged results below therefore carry, as
explicit hypotheses, a functor `T` and a natural additive bijection `(K ⟶ -) ≃+ (j_{X!}O_X ⟶ T(-))`
with `T` preserving the relevant coproducts; this is the reduction "after reformulation as above"
of the source's proof, and nothing else of Stacks 08JJ is used. Perfectness of `K` is retained as a
hypothesis because it is what the source's Stacks 08JJ provides this datum for; it is not otherwise
consumed.

Part (a) needs in addition that `T` sends the bounded-below coproduct to a bounded-below object,
which for the intended `T = K^∨ ⊗^L_O -` follows from the finite tor-amplitude of a perfect
complex (Stacks 08G8); that implication is not available in the shape needed, so the
boundedness of `T(⨁ M_i)` is a hypothesis as well.

Part (b) is stated with the two hypotheses of Stacks 094D: finite cohomological dimension at the
final object, and the commutation of the higher cohomology functors there with direct sums. In
the source the latter is supplied by Stacks 0739 from hypotheses (2) and (3) of the tag; that
derivation is private to the module proving Stacks 0G22,
`StacksDraft.CategoryTheory.Sites.Cohomology.CompactnessFromCoverings.`
`CompactnessFromFiniteCoverings`, and is not re-proved here, so hypotheses (2) and (3) enter
part (b) only through it.

## Implementation notes

The final object `X` of the tag appears as an unconstrained object `X₀` of the site. Finality is
not needed: it serves in the source only to read `H⁰(X, -)` as global sections, and the
reduction datum is stated against `Hom(j_{X₀!}O_{X₀}, -)` directly. For part (a) the role of
"quasi-compact" is played by membership in the collection `B` of Stacks 0G22, whose covering
data `Cov` are the finite coverings of hypotheses (2) and (3).

The two parts use the two spellings of `j_{U!}O_U` that the library's two inputs use: Stacks 0G22
is stated for `Stacks.Sites.OverModules.extensionByZeroUnit`, Stacks 094D for the pullback along
`Over.forget` of the unit module of the slice. No comparison between them is needed, each part
naming only the one its input uses.

The instances making the right-derived evaluation functors of part (b) elaborate are declared as
`local instance`s in the module proving Stacks 094D, so they are reinstated here from the public
`AlgebraicGeometry.RingedSite.enoughInjectives_of_ringedSite` and
`AlgebraicGeometry.RingedSite.evaluation_additive_of_ringedSite`; being `Prop`-valued they agree
with the ones used there.

## References

* [Stacks Project, Tag 09JC](https://stacks.math.columbia.edu/tag/09JC)
* [Stacks Project, Tag 0G22](https://stacks.math.columbia.edu/tag/0G22)
* [Stacks Project, Tag 094D](https://stacks.math.columbia.edu/tag/094D)
* [Stacks Project, Tag 08JJ](https://stacks.math.columbia.edu/tag/08JJ)
* [Stacks Project, Tag 0739](https://stacks.math.columbia.edu/tag/0739)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.Sites.OverModules

universe w u i c v₁ u₁ v₂ u₂

namespace Stacks.Cohomology

/-! ### Transfer of compactness along a natural bijection of Hom groups -/

section Transfer

variable {D : Type u₁} [Category.{v₁} D] [Preadditive D]
  {E : Type u₂} [Category.{v₂} E] [Preadditive E]

/-- **Transfer of the compactness map along a natural bijection of morphism groups.** Let `T` be
a functor and let `(K ⟶ -) ≃+ (L ⟶ T(-))` be a family of additive bijections compatible with
postcomposition. Then the compactness map of `K` against a family of morphisms `j i : A i ⟶ S`
is bijective as soon as the compactness map of `L` against the `T`-images of the `j i` is. -/
lemma bijective_cofanMap_of_homAddEquiv (K : D) (L : E) (T : D ⥤ E)
    (e : ∀ M : D, (K ⟶ M) ≃+ (L ⟶ T.obj M))
    (he : ∀ {M N : D} (f : K ⟶ M) (g : M ⟶ N), e N (f ≫ g) = e M f ≫ T.map g)
    {I : Type*} [DecidableEq I] {A : I → D} {S : D} (j : ∀ i, A i ⟶ S)
    (h : Function.Bijective (cofanMap L fun i => T.map (j i))) :
    Function.Bijective (cofanMap K j) := by
  have hsq : ∀ x, (e S) (cofanMap K j x) =
      cofanMap L (fun i => T.map (j i))
        (DirectSum.map (fun i => (e (A i)).toAddMonoidHom) x) := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i f => simp [cofanMap_of, he f (j i)]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hcomp : Function.Bijective ((e S) ∘ (cofanMap K j)) := by
    rw [show ((e S) ∘ (cofanMap K j)) = (cofanMap L fun i => T.map (j i)) ∘
        DirectSum.map (fun i => (e (A i)).toAddMonoidHom) from funext hsq]
    exact h.comp (bijective_directSumMap _ fun i => (e (A i)).bijective)
  exact (Function.Bijective.of_comp_iff' (e S).bijective _).1 hcomp

omit [Preadditive D] in
/-- The compactness map of `L` against the `T`-images of the coproduct inclusions of a family `A`
is bijective as soon as the compactness map against the coproduct inclusions of the family of
`T`-images is, provided `T` preserves the coproduct of `A`. -/
lemma bijective_cofanMap_map_sigmaι (L : E) (T : D ⥤ E) {I : Type*} [DecidableEq I] (A : I → D)
    [HasCoproduct A] [PreservesColimit (Discrete.functor A) T]
    [HasCoproduct fun i => T.obj (A i)]
    (h : Function.Bijective (cofanMap L (Limits.Sigma.ι fun i => T.obj (A i)))) :
    Function.Bijective (cofanMap L fun i => T.map (Limits.Sigma.ι A i)) := by
  have hc := isColimitOfHasCoproductOfPreservesColimit T A
  refine bijective_cofanMap_of_iso L _ _ (fun i => Iso.refl _)
    ((coproductIsCoproduct fun i => T.obj (A i)).coconePointUniqueUpToIso hc) (fun i => ?_) h
  simpa using
    (coproductIsCoproduct fun i => T.obj (A i)).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩

/-- The compactness map of `K` against the coproduct inclusions of `A` is bijective as soon as
the one of `L` against the coproduct inclusions of the `T`-images is. -/
private lemma bijective_cofanMap_sigmaι_of_homAddEquiv (K : D) (L : E) (T : D ⥤ E)
    (e : ∀ M : D, (K ⟶ M) ≃+ (L ⟶ T.obj M))
    (he : ∀ {M N : D} (f : K ⟶ M) (g : M ⟶ N), e N (f ≫ g) = e M f ≫ T.map g)
    {I : Type*} [DecidableEq I] (A : I → D) [HasCoproduct A]
    [PreservesColimit (Discrete.functor A) T]
    (h : ∀ [HasCoproduct fun i => T.obj (A i)],
      Function.Bijective (cofanMap L (Limits.Sigma.ι fun i => T.obj (A i)))) :
    Function.Bijective (cofanMap K (Limits.Sigma.ι A)) := by
  have : HasCoproduct fun i => T.obj (A i) :=
    ⟨⟨⟨_, isColimitOfHasCoproductOfPreservesColimit T A⟩⟩⟩
  exact bijective_cofanMap_of_homAddEquiv K L T e he _ (bijective_cofanMap_map_sigmaι L T A h)

/-- **Compactness transfers along a natural bijection of morphism groups.** If
`(K ⟶ -) ≃+ (L ⟶ T(-))` compatibly with postcomposition, `L` is compact and `T` preserves the
coproducts being tested, then `K` is compact. -/
lemma isCompactObject_of_homAddEquiv (K : D) (L : E) (T : D ⥤ E)
    [∀ I : Type w, PreservesColimitsOfShape (Discrete I) T] (hL : IsCompactObject.{w} L)
    (e : ∀ M : D, (K ⟶ M) ≃+ (L ⟶ T.obj M))
    (he : ∀ {M N : D} (f : K ⟶ M) (g : M ⟶ N), e N (f ≫ g) = e M f ≫ T.map g) :
    IsCompactObject.{w} K := by
  classical
  constructor
  intro I _ A _
  exact bijective_cofanMap_sigmaι_of_homAddEquiv K L T e he A
    (hL.bijective_toAddMonoid_rightComp_sigmaι fun i => T.obj (A i))

end Transfer

/-! ### The tag -/

section RingedSite

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

-- Sheaves of modules on a ringed site have enough injectives: the registration of the module
-- proving Stacks 094D is scoped to its own file, so it is reinstated here.
attribute [local instance] CompactExtensionByZero.modulesEnoughInjectives

/-- Evaluation of a sheaf of modules at an object of the site is additive. Reinstated from the
public statement because the module proving Stacks 094D declares it only locally. -/
local instance perfectCompactEvaluationAdditive (X₀ : X.C) :
    (SheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (op X₀)).Additive :=
  evaluation_additive_of_ringedSite.{u, u, u, u} X X₀

/-- **The reduction of Stacks 09JC in the bounded-below case.** Let `B` be a collection of
objects of `C` with a cofinal system of finite coverings whose fibre products again lie in `B`,
and let `X₀` be a member of `B`. Suppose morphisms out of `K` are identified, naturally in the
target, with morphisms out of `j_{X₀!}O_{X₀}` after applying a functor `T` which preserves the
coproduct of `M` and sends it to a bounded-below object. Then morphisms from `K` into `∐ M` are
finite sums.

This is the step the source performs with `T = K^∨ ⊗^L_O -`, after which the statement is
Stacks 0G22 at `U = X₀`. -/
theorem hom_coproduct_bijective_of_reduction
    (B : Set X.C) (Cov : ∀ U : X.C, Set (PreZeroHypercover.{c} U))
    (hCov : ∀ (U : X.C) (F : PreZeroHypercover.{c} U), Cov U F → F.sieve₀ ∈ X.J U)
    (hfinite : ∀ (U : X.C) (F : PreZeroHypercover.{c} U), Cov U F → HasIntersectionsIn B F)
    (hcofinal : ∀ (U : X.C), B U → ∀ S ∈ X.J U,
      ∃ F : PreZeroHypercover.{c} U, Cov U F ∧ F.sieve₀ ≤ S)
    (X₀ : X.C) (hX₀ : B X₀)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (T : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (e : ∀ N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
      (K ⟶ N) ≃+
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (extensionByZeroUnit.{u, u, u, u} X.J (Stacks.SheafOfModules.Tensor.ringSheaf X.O) X₀) ⟶
          T.obj N))
    (he : ∀ {N N' : DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (f : K ⟶ N) (g : N ⟶ N'),
      e N' (f ≫ g) = e N f ≫ T.map g)
    {I : Type i} [DecidableEq I]
    (M : I → DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasCoproduct M]
    [PreservesColimit (Discrete.functor M) T]
    (hTplus : (DerivedCategory.TStructure.t
      (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).plus (T.obj (∐ M))) :
    Function.Bijective
      (DirectSum.toAddMonoid fun j => Preadditive.rightComp K (Limits.Sigma.ι M j)) := by
  classical
  refine bijective_cofanMap_sigmaι_of_homAddEquiv K _ T e he M @fun _ => ?_
  have hc := isColimitOfHasCoproductOfPreservesColimit T M
  have hplus : (DerivedCategory.TStructure.t
      (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).plus
        (∐ fun j => T.obj (M j)) := by
    obtain ⟨n, hn⟩ := hTplus
    have : (DerivedCategory.TStructure.t
      (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).IsGE
        (T.obj (∐ M)) n := hn
    have eiso : T.obj (∐ M) ≅ (∐ fun j => T.obj (M j)) :=
      ((coproductIsCoproduct fun j => T.obj (M j)).coconePointUniqueUpToIso hc).symm
    exact ⟨n, DerivedCategory.TStructure.t.isGE_of_iso eiso n⟩
  exact extensionByZero_unit_hom_coproduct_bijective_of_hasIntersectionsIn X B Cov hCov hfinite
    hcofinal X₀ hX₀ I (fun j => T.obj (M j)) hplus

/-- **The reduction of Stacks 09JC in the unbounded case.** Suppose morphisms out of `K` are
identified, naturally in the target, with morphisms out of `j_{X₀!}O_{X₀}` after applying a
functor `T` which commutes with direct sums. If cohomology over `X₀` has finite cohomological
dimension and the functors `F ↦ H^p(X₀, F)` commute with direct sums, then `K` is a compact
object of `D(O)`.

This is the step the source performs with `T = K^∨ ⊗^L_O -`, after which the statement is
Stacks 094D at `U = X₀`. -/
theorem isCompactObject_of_reduction (X₀ : X.C)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hcd : ∃ d : ℤ, ∀ (p : ℕ)
      (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)), d < (p : ℤ) →
        IsZero (((SheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (op X₀)).rightDerived p).obj G))
    (hsums : ∀ (p : ℕ) (I : Type w), PreservesColimitsOfShape (Discrete I)
      ((SheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (op X₀)).rightDerived p))
    (T : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [∀ I : Type w, PreservesColimitsOfShape (Discrete I) T]
    (e : ∀ N : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
      (K ⟶ N) ≃+
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        ((SheafOfModules.pullback.{u} (F := Over.forget X₀)
          (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over X₀))).obj
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over X₀))) ⟶
          T.obj N))
    (he : ∀ {N N' : DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (f : K ⟶ N) (g : N ⟶ N'),
      e N' (f ≫ g) = e N f ≫ T.map g) :
    IsCompactObject.{w} K :=
  isCompactObject_of_homAddEquiv K _ T
    (CompactExtensionByZero.isCompactObject_singleFunctor_extensionByZeroUnit X X₀ hcd hsums)
    e he

/-- **Stacks 09JC (a).** Let `(C, O)` be a ringed site, let `B` be a collection of objects of `C`
with a cofinal system of finite coverings whose fibre products again lie in `B` — hypotheses (1),
(2) and (3) of the tag, with `B` the quasi-compact objects — and let `X₀` be a member of `B`, the
quasi-compact final object of the tag. Let `K` be a perfect object of `D(O)`. If `M : I → D(O)`
has a bounded-below coproduct, then morphisms from `K` into that coproduct are finite sums,
`Hom(K, ⨁ M_i) = ⨁ Hom(K, M_i)`: the object `K` is compact relative to `D⁺(O)`.

The hypothesis `hreduce` is the reduction the source performs, and is what perfectness of `K` is
used for: by Stacks 08JJ the dual `K^∨` satisfies
`Hom_{D(O)}(K, N) = H⁰(X₀, K^∨ ⊗^L_O N)` naturally in `N`, the functor `T = K^∨ ⊗^L_O -`
commutes with direct sums, and `T` keeps a bounded-below coproduct bounded below. None of those
three facts is available in this library — see "What this file assumes" in the module
documentation — so the reduction is assumed; granted it, this is Stacks 0G22 at `U = X₀`. -/
@[stacks 09JC "(a) bounded-below compactness; assumes the 08JJ reduction, not formalized"]
theorem hom_coproduct_bijective_of_isPerfect
    (B : Set X.C) (Cov : ∀ U : X.C, Set (PreZeroHypercover.{c} U))
    (hCov : ∀ (U : X.C) (F : PreZeroHypercover.{c} U), Cov U F → F.sieve₀ ∈ X.J U)
    (hfinite : ∀ (U : X.C) (F : PreZeroHypercover.{c} U), Cov U F → HasIntersectionsIn B F)
    (hcofinal : ∀ (U : X.C), B U → ∀ S ∈ X.J U,
      ∃ F : PreZeroHypercover.{c} U, Cov U F ∧ F.sieve₀ ≤ S)
    (X₀ : X.C) (hX₀ : B X₀)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K)
    {I : Type i} [DecidableEq I]
    (M : I → DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasCoproduct M]
    (hreduce : X.IsPerfect K →
      ∃ T : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
          DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
        ∃ _ : PreservesColimit (Discrete.functor M) T,
          (DerivedCategory.TStructure.t
            (C := SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).plus
              (T.obj (∐ M)) ∧
          ∃ e : ∀ N : DerivedCategory
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)), (K ⟶ N) ≃+
              ((DerivedCategory.singleFunctor
                  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
                (extensionByZeroUnit.{u, u, u, u} X.J
                  (Stacks.SheafOfModules.Tensor.ringSheaf X.O) X₀) ⟶ T.obj N),
            ∀ {N N' : DerivedCategory
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
              (f : K ⟶ N) (g : N ⟶ N'), e N' (f ≫ g) = e N f ≫ T.map g) :
    Function.Bijective
      (DirectSum.toAddMonoid fun j => Preadditive.rightComp K (Limits.Sigma.ι M j)) := by
  obtain ⟨T, hT, hTplus, e, he⟩ := hreduce hK
  exact hom_coproduct_bijective_of_reduction X B Cov hCov hfinite hcofinal X₀ hX₀ K T e he M hTplus

/-- **Stacks 09JC (b).** Let `(C, O)` be a ringed site, let `X₀` be an object of `C` — the
quasi-compact final object of the tag — and let `K` be a perfect object of `D(O)`. If cohomology
over `X₀` has finite cohomological dimension, that is `(C, O)` has finite cohomological
dimension, and if the functors `F ↦ H^p(X₀, F)` commute with direct sums, then `K` is a compact
object of `D(O)`.

The hypothesis `hreduce` is the reduction the source performs, and is what perfectness of `K` is
used for: by Stacks 08JJ the dual `K^∨` satisfies
`Hom_{D(O)}(K, N) = H⁰(X₀, K^∨ ⊗^L_O N)` naturally in `N`, and `T = K^∨ ⊗^L_O -` commutes with
direct sums. Neither fact is available in this library — see "What this file assumes" in the
module documentation — so the reduction is assumed; granted it, this is Stacks 094D at `U = X₀`.
The hypothesis `hsums` is what hypotheses (2) and (3) of the tag supply through Stacks 0739. -/
@[stacks 09JC "(b) unbounded compactness; assumes the 08JJ reduction, 0739 sums; not formalized"]
theorem isCompactObject_of_isPerfect (X₀ : X.C)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : X.IsPerfect K)
    (hcd : ∃ d : ℤ, ∀ (p : ℕ)
      (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)), d < (p : ℤ) →
        IsZero (((SheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (op X₀)).rightDerived p).obj G))
    (hsums : ∀ (p : ℕ) (I : Type w), PreservesColimitsOfShape (Discrete I)
      ((SheafOfModules.evaluation.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (op X₀)).rightDerived p))
    (hreduce : X.IsPerfect K →
      ∃ T : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
          DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)),
        ∃ _ : ∀ I : Type w, PreservesColimitsOfShape (Discrete I) T,
          ∃ e : ∀ N : DerivedCategory
              (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)), (K ⟶ N) ≃+
              ((DerivedCategory.singleFunctor
                  (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
                ((SheafOfModules.pullback.{u} (F := Over.forget X₀)
                  (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over X₀))).obj
                    (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over X₀))) ⟶
                T.obj N),
            ∀ {N N' : DerivedCategory
                (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
              (f : K ⟶ N) (g : N ⟶ N'), e N' (f ≫ g) = e N f ≫ T.map g) :
    IsCompactObject.{w} K := by
  obtain ⟨T, hT, e, he⟩ := hreduce hK
  exact isCompactObject_of_reduction X X₀ K hcd hsums T e he

end RingedSite

end Stacks.Cohomology

end
