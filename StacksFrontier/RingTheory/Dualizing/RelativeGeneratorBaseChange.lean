module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.CategoryTheory.Adjunction.Unique
public import StacksFrontier.Homology.HomComplex.DerivedAdjunction
public import StacksFrontier.Homology.HomComplex.RHom.BaseChange
public import StacksFrontier.Homology.Perfect.Duality
public import StacksFrontier.Homology.PseudoCoherent.Basic
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChange

/-!
# Base change of a diagonal generator of a relative dualizing complex

Let `R → A` be a flat ring map of finite presentation, put `B = A ⊗[R] A` and write
`Δ : B → A` for the multiplication map.  Let `K` be an object of `D(A)` and let
`ξ : A ⟶ K ⊗ᴸ_A B` be a morphism in `D(B)` from the diagonal, generating the `B`-module
`Hom_{D(B)}(A, K ⊗ᴸ_A B)`.  For a ring map `R → R'` put `A' = A ⊗[R] R'` and
`B' = A' ⊗[R'] A'`.  This file proves that the derived base change of `ξ` along `B → B'`
generates `Hom_{D(B')}(A', K' ⊗ᴸ_{A'} B')`, where `K' = K ⊗ᴸ_A A'`.  That is the "moreover"
clause of [stacks 0E2F].

## Main definitions

* `Dualizing.envelopingBaseChangeRingHom` — the ring map `A ⊗[R] A → A' ⊗[R'] A'`.
* `Dualizing.diagonalSingle` — the diagonal `A`, placed in degree zero in `D(A ⊗[R] A)`.
* `Dualizing.cohomologyExtensionComparison`,
  `Dualizing.homCohomologyExtensionComparison` — the canonical comparisons between cohomology
  and derived base change, and between derived Hom and derived base change, of [stacks 0E1X].
* `Dualizing.derivedHomExtensionComparison` — the derived-Hom base-change transformation of
  [stacks 0E1X] at the derived extension of scalars used here; the second of the two factors of
  `Dualizing.homCohomologyExtensionComparison`.
* `Dualizing.DiagonalHomCohomologyBaseChangeEpiAt`,
  `Dualizing.DiagonalHomCohomologyBaseChangeEpi` — the one carried input, at a single object and
  at every object; see below.

## Main results

* `Dualizing.span_derivedBaseChange_diagonalGenerator_at` — **[stacks 0E2F], the "moreover"
  clause**, with the carried input read at the single object `K ⊗ᴸ_A B` the proof consumes.
* `Dualizing.span_derivedBaseChange_diagonalGenerator` — the same with that input quantified over
  every object of `D(B)`.
* `Dualizing.span_derivedBaseChange_diagonalGenerator_congr` — the conclusion does not depend on
  the chosen generator, so the clause is a property of `R → A` and `R → R'` alone.  Nothing is
  carried.
* `Dualizing.diagonalHomCohomologyBaseChangeEpiAt_of_iso` — the carried input depends on its
  object only up to isomorphism, so it may be checked at any representative.  Nothing is
  carried.
* `Dualizing.homCohomologyExtensionComparison_app`,
  `Dualizing.epi_homCohomologyExtensionComparison_app`,
  `Dualizing.diagonalHomCohomologyBaseChangeEpiAt_of_epi` — the comparison of [stacks 0E1X] in a
  degree is the comparison between cohomology and derived base change followed by cohomology of
  the derived-Hom base-change transformation, so the carried input splits into one epimorphy
  statement for each factor.  Nothing is carried.

## Generation stated as a span, and why the identifications are hypotheses

"`ξ` is a generator for the cyclic module `Hom_{D(B)}(A, K ⊗ᴸ_A B)`" is read here as
`Submodule.span B {ξ} = ⊤`: the derived category of `B`-modules is `B`-linear, so a Hom group in
it is a `B`-module, and a cyclic module with a chosen generator is exactly one whose span on that
single element is everything.

The conclusion is stated for the morphism `eΔ.inv ≫ D ξ ≫ eM.hom`, where `D` is derived base
change along `B → B'` and `eΔ`, `eM` are *arbitrary* identifications of `D A` with the diagonal
of `B'` and of `D (K ⊗ᴸ_A B)` with `K' ⊗ᴸ_{A'} B'`.  Quantifying over them is stronger than
choosing them, and it is what lets the statement be about the module
`Hom_{D(B')}(A', K' ⊗ᴸ_{A'} B')` that the source names without this file having to construct the
canonical comparison; any construction of it is covered.

## The hypothesis that is carried, and why

The carried input is `Dualizing.DiagonalHomCohomologyBaseChangeEpiAt` at the single object
`K ⊗ᴸ_A B`: the canonical comparison of [stacks 0E1X],
`B' ⊗_B H^0(RHom_B(A, M)) ⟶ H^0(RHom_{B'}(A ⊗ᴸ_B B', M ⊗ᴸ_B B'))`, is an epimorphism there.  This
is the degree-zero, surjectivity half of the derived-Hom base-change map at the diagonal square,
which the source establishes by producing a bounded below complex `E^•` of `R`-flat finitely
presented `B`-modules representing `RHom_B(A, K ⊗ᴸ_A B)` compatibly with derived base change
([stacks 0E1U]) and then checking flatness of the cokernels degree by degree.  It is the same
input `Dualizing.DiagonalDerivedHomBaseChange` carries for clause (2), read in cohomological
degree zero; see `StacksFrontier.RingTheory.Dualizing.RelativeBaseChange` for why the library's
unconditional criteria of [stacks 0A6A] do not supply it.

### What the input costs, and why it is not available unconditionally

With `E^•` the representative of [stacks 0E1U] the carried input is, degree by degree, the
surjectivity of `H^0(E^•) ⊗_R R' ⟶ H^0(E^• ⊗_R R')`, whose cokernel is
`Tor_1^R(E^1 / im(E^0 → E^1), R')`.  Writing `B^{n+1} = im(E^n → E^{n+1})`, the short exact
sequences `0 ⟶ B^n ⟶ E^n ⟶ B^{n+1} ⟶ 0` of the diagonal condition of [stacks 0E2C] -- which makes
`E^•` a bounded below `R`-flat coresolution of the `R`-flat module `A` -- give
`Tor_1^R(E^1/B^1, R') ≅ Tor_n^R(B^{n+1}, R')` for every `n ≥ 1`, and from the bottom of `E^•` they
give only `Tor_j^R(B^{n+1}, R') = 0` for `j ≥ n + 1 + d`, where `-d` is the lowest degree of `E^•`.
The two bookkeepings never meet, and they cannot be made to: `E^•` is bounded below and unbounded
above, so no truncation closes the gap -- replacing the resolution `P^•` of the diagonal by its
bounded brutal truncation `σ^{≥m}P^•`, which is perfect and therefore does commute with every base
change, moves the obstruction into `Ext^j_B(Ω, K ⊗ᴸ_A B)` for `Ω` a syzygy of the diagonal and `j`
in the Tor-amplitude window of `K` over `R`, where nothing makes it vanish.

What makes it vanish is the source's own input: each cokernel is `R`-flat, which the source gets
from `H^n(E^• ⊗_R κ(𝔭)) = 0` at every prime of `R` -- the **Noetherian case of this very clause**,
read at the residue fields.  So the degree-zero surjectivity is not a convenience of this proof's
architecture but the content of the clause, and it is reached only through the Noetherian theory:
[stacks 0E2E],
`Dualizing.PolynomialPresentation.relativeDualizingComplex_isRelativeDualizingComplex_of_flat`,
and [stacks 0BZV],
`Dualizing.PolynomialPresentation.relativeDualizingComplexBaseChange_of_flatAlgebra`, both of
which carry `Dualizing.PolynomialPresentation.ProjectionCompatibility`.

That Noetherian case is now a theorem of this library at one complex: at the upper shriek complex
`φ^!(R)` the vanishing is
`Dualizing.isZero_homology_derivedHom_diagonalBaseChangeTarget_upperShriek` of
`StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeNoetherian`, proved from the two tags above
and asking for nothing past that same compatibility.  It is not a theorem at the arbitrary `K`
read here, and the gap is the identification rather than the vanishing: carrying it over to `K`
wants `K ≅ φ^!(R)`, which is [stacks 0E2D] --
`Dualizing.nonempty_iso_of_isRelativeDualizingComplex`, whose hypothesis, the invertibility of
the two tensor--Hom diagonals of [stacks 0BYN], is *false* at the witness of
`StacksFrontier.RingTheory.Dualizing.RelativeDiagonalRefutation` and is discharged outright only in
the perfect cases, and under the same lower Tor-amplitude bound over `B` that the second bullet
below records as refuted.  So the input below is available at the complex clause (1)'s existence
proof produces, and not at a general one.  Until the compatibility itself is discharged the
clause has no unconditional proof, and the three unconditional routes one might hope for are all
closed:

* the two invertibility criteria of [stacks 0A6A] that do apply ask `B ⟶ B'` to be flat or of
  finite Tor dimension, which for `B' = B ⊗[R] R'` means `R ⟶ R'` flat or of finite Tor
  dimension, not a general ring map;
* the tensor--Hom criteria of [stacks 0ATK] ask the same of the tensor factor `B'`, the one
  remaining case -- a lower Tor-amplitude bound on `K ⊗ᴸ_A B` over `B` -- being refuted at
  `R = k`, `A = k[x, y]/(x, y)²` by the witness recorded in
  `StacksFrontier.RingTheory.Dualizing.RelativeUniqueness`;
* the degreewise chase of `StacksFrontier.RingTheory.Flat.DegreewiseChase`, which is proved and
  complete, needs both `IsNoetherianRing (A ⊗[R] A)` and the residue-field vanishing above, so it
  does not run over a general base either.

What the clause does *not* cost is anything of its own beyond clause (2)'s input: nothing in the
proof below is specific to `ξ` past `hξ` -- by
`Dualizing.span_derivedBaseChange_diagonalGenerator_congr` the conclusion is the same for every
generator -- and the input it reads is the degree-zero surjectivity shadow of the one clause (2)
reads, at a single object.  Note that clause (2)'s input as
`StacksFrontier.RingTheory.Dualizing.RelativeBaseChange` states it is an unspecified isomorphism and
so does not give this surjectivity: an isomorphism between the two sides says the Hom module over
`B'` is cyclic, not that the base change of `ξ` is one of its generators.

### The quantified form is false

`Dualizing.DiagonalHomCohomologyBaseChangeEpi`, the input read at *every* object of `D(B)`, is
false.  Take `R = A = ℤ`: then `B = A ⊗[R] A` is `ℤ`, the multiplication map `B ⟶ A` is an
isomorphism and the diagonal is free of rank one, so `RHom_B(A, M) = M` and the derived-Hom
base-change transformation at `(A, M)` is invertible.  Take `R' = 𝔽_p`, so that `A'` and `B'` are
`𝔽_p` and `B ⟶ B'` is the reduction `ℤ ⟶ 𝔽_p`.  By
`Dualizing.homCohomologyExtensionComparison_app` the comparison is then its first factor alone,
`𝔽_p ⊗_ℤ H^0(M) ⟶ H^0(M ⊗ᴸ_ℤ 𝔽_p)`.  Read it at the `M` with `𝔽_p` in cohomological degree one
and nothing elsewhere: the source is zero, while the distinguished triangle of multiplication by
`p` on `M` makes the target `ker(p : H^1(M) ⟶ H^1(M)) = 𝔽_p`.  So the comparison is not an
epimorphism there, and `Dualizing.span_derivedBaseChange_diagonalGenerator` cannot be made
unconditional by discharging its hypothesis;
`Dualizing.span_derivedBaseChange_diagonalGenerator_at`, which reads the input at the one object
the clause consumes, is the form to aim at.

The same two rings refute the conclusion of the clause at an arbitrary `K`, so an input of some
kind is unavoidable.  Let `K` have `ℤ` in degree zero and `𝔽_p` in degree one.  Then
`Hom_{D(B)}(A, K ⊗ᴸ_A B) = H^0(K) = ℤ` is cyclic, and `K' = K ⊗ᴸ_ℤ 𝔽_p` has
`Hom_{D(B')}(A', K' ⊗ᴸ_{A'} B') = H^0(K ⊗ᴸ_ℤ 𝔽_p) = 𝔽_p ⊕ 𝔽_p`, which is not — and the two
identifications `eΔ`, `eM` do exist, `ℤ` being flat over `ℤ`.  What the source assumes about `K`
is therefore what has to be used.

It mentions only the diagonal, derived Hom and derived base change.  It says nothing about `ξ`,
about spans, about relative perfection, or about either Hom module being cyclic, so it is not a
restatement of any part of the conclusion.

Everything else is proved: that an epimorphism on the degree-zero cohomology of the derived-Hom
object is the surjectivity of postcomposition (the chain
`Dualizing.homology_epi_iff_postcomp_surjective`, which identifies `Hom_{D(B)}(X, Y)` with
`H^0(RHom_B(X, Y))` through the derived-Hom adjunction and a projective resolution of the unit),
that the endomorphisms of the diagonal in `D(B')` are exactly the scalars, and the passage
between a span on one element and surjectivity of postcomposition in both directions.

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0E1U](https://stacks.math.columbia.edu/tag/0E1U)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

namespace Dualizing

open HomologicalComplex CochainComplex.HomComplex CategoryTheory.MonoidalCategory

/-! ### Hom groups in the derived category as degree-zero cohomology of derived Hom

The helpers of this namespace identify `Hom_{D(A)}(X, Y)` with `H^0(RHom_A(X, Y))` and read an
epimorphism on that cohomology as surjectivity of postcomposition. They rest on
`StacksDraft.Perfect.single_derived_homology_bijective`, which computes maps out of a projective
single complex in the derived category of any abelian category. -/

namespace DiagonalGenerator

private noncomputable def regularHomEquiv
    {A : Type u} [CommRing A] (M : ModuleCat.{u} A) :
    (ModuleCat.of A A ⟶ M) ≃ M :=
  ModuleCat.homEquiv.trans (LinearMap.ringLmapEquivSelf A ℤ M).toEquiv

private theorem regularHomEquiv_comp
    {A : Type u} [CommRing A] {M N : ModuleCat.{u} A}
    (f : ModuleCat.of A A ⟶ M) (g : M ⟶ N) :
    regularHomEquiv N (f ≫ g) = g (regularHomEquiv M f) := rfl

private noncomputable def singleHomEquiv
    {A : Type u} [CommRing A] (X : DerivedCategory (ModuleCat.{u} A)) :
    (DerivedCategory.Q.obj (𝟙_ (StacksDraft.DerivedHom.Model.Complex A)) ⟶ X) ≃
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj X :=
  (Equiv.ofBijective _
      (StacksDraft.Perfect.single_derived_homology_bijective (ModuleCat.of A A) X 0)).trans
    (regularHomEquiv _)

private theorem singleHomEquiv_comp
    {A : Type u} [CommRing A] {X Y : DerivedCategory (ModuleCat.{u} A)}
    (g : DerivedCategory.Q.obj (𝟙_ (StacksDraft.DerivedHom.Model.Complex A)) ⟶ X)
    (f : X ⟶ Y) :
    singleHomEquiv Y (g ≫ f) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map f (singleHomEquiv X g) := by
  simp only [singleHomEquiv, Equiv.trans_apply, Equiv.ofBijective_apply,
    CategoryTheory.Functor.map_comp, ← Category.assoc, regularHomEquiv_comp]

/-- Surjectivity transfers along two equivalences intertwining the maps. -/
private theorem surjective_iff_of_equiv {α β γ δ : Type*} (eα : α ≃ γ) (eβ : β ≃ δ)
    {f : α → β} {g : γ → δ} (h : ∀ a, eβ (f a) = g (eα a)) :
    Function.Surjective f ↔ Function.Surjective g := by
  rw [← eβ.comp_surjective, ← eα.surjective_comp]
  exact iff_of_eq (congrArg _ (funext h))

private theorem homology_epi_iff_single_postcomp_surjective
    {A : Type u} [CommRing A] {X Y : DerivedCategory (ModuleCat.{u} A)} (f : X ⟶ Y) :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map f) ↔
      Function.Surjective (fun g : DerivedCategory.Q.obj
        (𝟙_ (StacksDraft.DerivedHom.Model.Complex A)) ⟶ X => g ≫ f) := by
  rw [ModuleCat.epi_iff_surjective]
  exact (surjective_iff_of_equiv (singleHomEquiv X) (singleHomEquiv Y)
    fun g => singleHomEquiv_comp g f).symm

private theorem model_homology_epi_iff_postcomp_surjective
    {A : Type u} [CommRing A] (d : StacksDraft.DerivedHom.DerivedHomData A)
    (X : DerivedCategory (ModuleCat.{u} A))
    {Y Z : DerivedCategory (ModuleCat.{u} A)} (f : Y ⟶ Z) :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (d.hom.map (X := (Opposite.op X, Y)) (Y := (Opposite.op X, Z))
      (𝟙 (Opposite.op X), f))) ↔
      Function.Surjective (fun g : X ⟶ Y => g ≫ f) := by
  rw [homology_epi_iff_single_postcomp_surjective]
  have hn (g) : d.homZeroEquiv X Z (g ≫ d.hom.map
      (X := (Opposite.op X, Y)) (Y := (Opposite.op X, Z)) (𝟙 (Opposite.op X), f)) =
      d.homZeroEquiv X Y g ≫ f := by
    dsimp [StacksDraft.DerivedHom.DerivedHomData.homZeroEquiv]
    rw [d.homEquiv_naturality_right, Category.assoc]
  exact surjective_iff_of_equiv (d.homZeroEquiv X Y).toEquiv (d.homZeroEquiv X Z).toEquiv hn

private theorem homology_epi_mapDerivedCategory_iff
    {A B : Type u} [CommRing A] [CommRing B]
    (E : ModuleCat.{u} A ⥤ ModuleCat.{u} B) [E.Additive]
    [Limits.PreservesFiniteLimits E] [Limits.PreservesFiniteColimits E]
    [E.PreservesEpimorphisms] [E.ReflectsEpimorphisms]
    {X Y : DerivedCategory (ModuleCat.{u} A)} (f : X ⟶ Y) :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).map
      (E.mapDerivedCategory.map f)) ↔
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map f) := by
  let e := StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso E 0
  have h := e.hom.naturality f
  change (DerivedCategory.homologyFunctor (ModuleCat.{u} B) 0).map
    (E.mapDerivedCategory.map f) ≫ e.hom.app Y =
    e.hom.app X ≫ E.map ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map f) at h
  rw [← E.epi_map_iff_epi, ← epi_comp_iff_of_isIso _ (e.hom.app Y), h, epi_comp_iff_of_epi]

private theorem homology_epi_iff_postcomp_surjective
    {A : Type u} [CommRing A] (X : DerivedCategory (ModuleCat.{u} A))
    {Y Z : DerivedCategory (ModuleCat.{u} A)} (f : Y ⟶ Z) :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A).map
        (X := (Opposite.op X, Y)) (Y := (Opposite.op X, Z)) (𝟙 (Opposite.op X), f))) ↔
      Function.Surjective (fun g : X ⟶ Y => g ≫ f) := by
  let E := Stacks.DerivedHom.ScalarTransportedInternalHom.scalarEquivalence.{u, u} A
  let U := ModuleCat.restrictScalars.{u}
    (ULift.ringEquiv : ULift.{u} A ≃+* A).symm.toRingHom
  have : U.IsEquivalence :=
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv : ULift.{u} A ≃+* A).symm).isEquivalence_functor
  change Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
    (U.mapDerivedCategory.map ((StacksDraft.DerivedHom.derivedHomAdjunction
      (R := ULift.{u} A)).hom.map
      (X := (Opposite.op (E.functor.obj X), E.functor.obj Y))
      (Y := (Opposite.op (E.functor.obj X), E.functor.obj Z))
      ((E.functor.map (𝟙 X)).op, E.functor.map f)))) ↔ _
  rw [homology_epi_mapDerivedCategory_iff, CategoryTheory.Functor.map_id, op_id,
    model_homology_epi_iff_postcomp_surjective]
  exact (surjective_iff_of_equiv E.fullyFaithfulFunctor.homEquiv E.fullyFaithfulFunctor.homEquiv
    fun g => E.functor.map_comp g f).symm

end DiagonalGenerator

open DiagonalGenerator

/-- **The comparison between cohomology and derived base change.**  The canonical map
`B ⊗_A H^n(X) ⟶ H^n(X ⊗ᴸ_A B)`, obtained as the mate under the extension--restriction
adjunction of the unit of derived extension of scalars followed by the identification of
cohomology with restricted cohomology. -/
noncomputable def cohomologyExtensionComparison
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (n : ℤ) :
    DerivedCategory.homologyFunctor (ModuleCat.{u} A) n ⋙ ModuleCat.extendScalars.{u, u, u} f ⟶
      (totalDerivedExtensionScalars.{u, u, u} f).functor ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} B) n := by
  let D := totalDerivedExtensionScalars.{u, u, u} f
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) n
  let H' := DerivedCategory.homologyFunctor (ModuleCat.{u} B) n
  let adj := @derivedExtensionScalarsAdjunction.{u, u, u} A B _ _ f _ _
    D.functor D.comparison D.isLeftDerived
  let a := ModuleCat.extendRestrictScalarsAdj.{u} f
  let e := StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
    (ModuleCat.restrictScalars.{u} f) n
  refine { app X := (a.homEquiv _ _).symm (H.map (adj.unit.app X) ≫ e.hom.app (D.functor.obj X))
           naturality := ?_ }
  intro X Y g
  apply a.homEquiv_naturality_right_square
  simp only [Functor.comp_map]
  have he := e.hom.naturality (D.functor.map g)
  dsimp only [Functor.comp_map] at he
  rw [Category.assoc, ← he]
  have hu := adj.unit.naturality g
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, hu,
    CategoryTheory.Functor.map_comp, Category.assoc]

/-- **Stacks 0E1X in cohomological degree `n`.**  The canonical comparison
`B ⊗_A H^n(RHom_A(X, Y)) ⟶ H^n(RHom_B(X ⊗ᴸ_A B, Y ⊗ᴸ_A B))`: the comparison between
cohomology and derived base change, followed by the derived-Hom base-change transformation
of [stacks 0E1X]. -/
noncomputable def homCohomologyExtensionComparison
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (n : ℤ) :
    Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) n ⋙ ModuleCat.extendScalars.{u, u, u} f ⟶
      Functor.prod (totalDerivedExtensionScalars.{u, u, u} f).functor.op
          (totalDerivedExtensionScalars.{u, u, u} f).functor ⋙
        Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} B ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} B) n := by
  let D := totalDerivedExtensionScalars.{u, u, u} f
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} B) n
  let c := @Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeNatTrans.{u, u, u} _ _ _ _ f
    D.functor D.comparison D.isLeftDerived
  exact Functor.whiskerLeft _ (cohomologyExtensionComparison f n) ≫
    Functor.whiskerRight c H

/-- **The derived-Hom base-change transformation of [stacks 0E1X]**, read at the derived
extension-of-scalars functor `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`
chosen throughout this file: `RHom_A(X, Y) ⊗ᴸ_A B ⟶ RHom_B(X ⊗ᴸ_A B, Y ⊗ᴸ_A B)`.

This is the second of the two factors of `Dualizing.homCohomologyExtensionComparison`, the first
being `Dualizing.cohomologyExtensionComparison`; see
`Dualizing.homCohomologyExtensionComparison_app`. -/
noncomputable def derivedHomExtensionComparison
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A ⋙
        (totalDerivedExtensionScalars.{u, u, u} f).functor ⟶
      Functor.prod (totalDerivedExtensionScalars.{u, u, u} f).functor.op
          (totalDerivedExtensionScalars.{u, u, u} f).functor ⋙
        Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} B :=
  @Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeNatTrans.{u, u, u} _ _ _ _ f
    (totalDerivedExtensionScalars.{u, u, u} f).functor
    (totalDerivedExtensionScalars.{u, u, u} f).comparison
    (totalDerivedExtensionScalars.{u, u, u} f).isLeftDerived

/-- **The comparison of [stacks 0E1X] in degree `n`, factored.**  It is the comparison between
cohomology and derived base change, taken at the derived-Hom object, followed by degree-`n`
cohomology of the derived-Hom base-change transformation. -/
theorem homCohomologyExtensionComparison_app
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (n : ℤ)
    (X Y : DerivedCategory (ModuleCat.{u} A)) :
    (homCohomologyExtensionComparison f n).app (Opposite.op X, Y) =
      (cohomologyExtensionComparison f n).app
          ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A).obj
            (Opposite.op X, Y)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).map
          ((derivedHomExtensionComparison f).app (Opposite.op X, Y)) :=
  rfl

/-- **The two halves of an epimorphy statement for the comparison of [stacks 0E1X].**  The
degree-`n` comparison at `(X, Y)` is an epimorphism as soon as both of its factors are: the
comparison between cohomology and derived base change at `RHom_A(X, Y)`, and degree-`n`
cohomology of the derived-Hom base-change transformation at `(X, Y)`.

Neither factor is an epimorphism for every `X`, `Y`; see the module documentation. -/
theorem epi_homCohomologyExtensionComparison_app
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) (n : ℤ)
    (X Y : DerivedCategory (ModuleCat.{u} A))
    (h₁ : Epi ((cohomologyExtensionComparison f n).app
      ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A).obj (Opposite.op X, Y))))
    (h₂ : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).map
      ((derivedHomExtensionComparison f).app (Opposite.op X, Y)))) :
    Epi ((homCohomologyExtensionComparison f n).app (Opposite.op X, Y)) := by
  rw [homCohomologyExtensionComparison_app]
  exact epi_comp _ _

private theorem postcomp_surjective_of_homCohomologyExtension_epi
    {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)
    (X Y : DerivedCategory (ModuleCat.{u} A)) (g : X ⟶ Y)
    (hg : Function.Surjective (fun a : X ⟶ X => a ≫ g))
    (hc : Epi ((homCohomologyExtensionComparison f 0).app (Opposite.op X, Y))) :
    Function.Surjective (fun a :
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          f).functor.obj X ⟶
        (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
          f).functor.obj X =>
      a ≫ (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        f).functor.map g) := by
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u} f
  have := (ModuleCat.extendRestrictScalarsAdj.{u} f).isLeftAdjoint
  have : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
    ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} A).map
      (X := (Opposite.op X, X)) (Y := (Opposite.op X, Y)) (𝟙 _, g))) :=
    (homology_epi_iff_postcomp_surjective X g).2 hg
  apply (homology_epi_iff_postcomp_surjective (D.functor.obj X) (D.functor.map g)).1
  have h := (homCohomologyExtensionComparison f 0).naturality
    (show (Opposite.op X, X) ⟶ (Opposite.op X, Y) from (𝟙 _, g))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.op_map] at h
  simp only [CategoryTheory.unop_id, CategoryTheory.Functor.map_id, op_id] at h
  exact epi_of_epi_fac h.symm

/-- A morphism spanning its Hom module over the linear structure is a generator for
postcomposition: every morphism with the same source and target factors through it by an
endomorphism of the source. -/
theorem postcomp_surjective_of_span_singleton
    {R : Type u} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    {X Y : C} (f : X ⟶ Y) (hf : Submodule.span R ({f} : Set _) = ⊤) :
    Function.Surjective (fun g : X ⟶ X => g ≫ f) := by
  intro g
  have hg : g ∈ Submodule.span R ({f} : Set _) := by simp [hf]
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hg
  exact ⟨r • 𝟙 X, by simp [Linear.smul_comp]⟩

/-- Surjectivity of postcomposition with `f` survives conjugating `f` by isomorphisms of its
source and its target. -/
theorem postcomp_surjective_iso
    {C : Type*} [Category C] {X X' Y Y' : C}
    (eX : X ≅ X') (eY : Y ≅ Y') (f : X ⟶ Y)
    (hf : Function.Surjective (fun g : X ⟶ X => g ≫ f)) :
    Function.Surjective (fun g : X' ⟶ X' => g ≫ (eX.inv ≫ f ≫ eY.hom)) := by
  intro g
  obtain ⟨k, hk⟩ := hf (eX.hom ≫ g ≫ eY.inv)
  refine ⟨eX.inv ≫ k ≫ eX.hom, ?_⟩
  dsimp only at hk ⊢
  simp [reassoc_of% hk]

/-- **The endomorphisms of the diagonal are the scalars.**  Every endomorphism in `D(A ⊗[R] A)`
of the diagonal `A` placed in degree zero is multiplication by an element of `A ⊗[R] A`. -/
theorem diagonal_endomorphism_eq_smul_id
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (g : (DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj
        ((ModuleCat.restrictScalars
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj (ModuleCat.of A A)) ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj
        ((ModuleCat.restrictScalars
          (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj (ModuleCat.of A A))) :
    ∃ b : A ⊗[R] A, g = b • 𝟙 _ := by
  let μ := (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0
  obtain ⟨k, rfl⟩ := S.map_surjective g
  let b : A := k (1 : A)
  refine ⟨b ⊗ₜ[R] (1 : A), ?_⟩
  rw [← S.map_id, ← S.map_smul]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  let a₀ : A := a
  have h := k.hom.map_smul (a₀ ⊗ₜ[R] (1 : A)) (1 : A)
  change @Eq A (k (μ (a₀ ⊗ₜ[R] 1) * (1 : A))) (μ (a₀ ⊗ₜ[R] 1) * b) at h
  change @Eq A (k a₀) (μ (b ⊗ₜ[R] 1) * a₀)
  simpa [μ, mul_comm] using h

private theorem span_singleton_comp_le
    {R : Type u} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    {X Y : C} (h : X ⟶ X) (f : X ⟶ Y)
    (hX : ∀ g : X ⟶ X, ∃ r : R, g = r • 𝟙 X) :
    Submodule.span R ({h ≫ f} : Set (X ⟶ Y)) ≤ Submodule.span R ({f} : Set (X ⟶ Y)) := by
  rw [Submodule.span_le, Set.singleton_subset_iff]
  obtain ⟨r, rfl⟩ := hX h
  exact Submodule.mem_span_singleton.mpr ⟨r, by simp [Linear.smul_comp]⟩

/-- Conversely, when every endomorphism of the source is a scalar, a morphism through which
every morphism factors spans its Hom module. -/
theorem span_singleton_of_postcomp_surjective
    {R : Type u} [CommRing R] {C : Type*} [Category C] [Preadditive C] [Linear R C]
    {X Y : C} (f : X ⟶ Y)
    (hX : ∀ g : X ⟶ X, ∃ r : R, g = r • 𝟙 X)
    (hf : Function.Surjective (fun g : X ⟶ X => g ≫ f)) :
    Submodule.span R ({f} : Set _) = ⊤ := by
  refine top_unique fun g _ => ?_
  obtain ⟨k, rfl⟩ := hf g
  obtain ⟨r, rfl⟩ := hX k
  exact Submodule.mem_span_singleton.mpr ⟨r, by simp [Linear.smul_comp]⟩

section Enveloping

variable (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R']
  [Algebra R A] [Algebra R R']

/-- The diagonal: the ring `A`, placed in cohomological degree zero and read as an object of
`D(A ⊗[R] A)` by restriction of scalars along the multiplication map. -/
noncomputable def diagonalSingle : DerivedCategory (ModuleCat.{u} (A ⊗[R] A)) :=
  (DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj
    ((ModuleCat.restrictScalars
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj (ModuleCat.of A A))

/-- The ring map `A ⊗[R] A → A' ⊗[R'] A'` with `A' = A ⊗[R] R'`, induced on each factor by the
left coprojection `A → A'`.  This is the map along which the source base changes the generator
`ξ`. -/
noncomputable def envelopingBaseChangeRingHom :
    (A ⊗[R] A) →+* (A ⊗[R] R') ⊗[R'] (A ⊗[R] R') :=
  (Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft :
          A ⊗[R] R' →ₐ[R'] (A ⊗[R] R') ⊗[R'] (A ⊗[R] R')).restrictScalars R).comp
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] R'))
    (((Algebra.TensorProduct.includeRight :
          A ⊗[R] R' →ₐ[R'] (A ⊗[R] R') ⊗[R'] (A ⊗[R] R')).restrictScalars R).comp
      (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] R'))
    (fun _ _ => Commute.all _ _)).toRingHom

/-- **The one carried input of the "moreover" clause of [stacks 0E2F], at a single object.**  The
canonical degree-zero comparison of [stacks 0E1X] at the diagonal,
`B' ⊗_B H^0(RHom_B(A, M)) ⟶ H^0(RHom_{B'}(A ⊗ᴸ_B B', M ⊗ᴸ_B B'))` with `B = A ⊗[R] A` and
`B' = A' ⊗[R'] A'`, is an epimorphism at the given object `M`.

It mentions only the diagonal, derived Hom and derived base change; see the module documentation
for why it is carried and what would discharge it. -/
def DiagonalHomCohomologyBaseChangeEpiAt
    (M : DerivedCategory (ModuleCat.{u} (A ⊗[R] A))) : Prop :=
  Epi ((homCohomologyExtensionComparison (envelopingBaseChangeRingHom R A R') 0).app
    (Opposite.op (diagonalSingle R A), M))

/-- **The one carried input of the "moreover" clause of [stacks 0E2F].**
`Dualizing.DiagonalHomCohomologyBaseChangeEpiAt` read at every object of `D(A ⊗[R] A)`.

The clause reads it at the single object `K ⊗ᴸ_A (A ⊗[R] A)`, so
`Dualizing.span_derivedBaseChange_diagonalGenerator_at` carries strictly less than this.

This quantified form is **false**: the module documentation refutes it at `R = A = ℤ`,
`R' = 𝔽_p` and the object with `𝔽_p` in cohomological degree one.  So it is
`Dualizing.DiagonalHomCohomologyBaseChangeEpiAt`, at the object the clause consumes, that is to
be discharged. -/
def DiagonalHomCohomologyBaseChangeEpi : Prop :=
  ∀ M : DerivedCategory (ModuleCat.{u} (A ⊗[R] A)),
    DiagonalHomCohomologyBaseChangeEpiAt R A R' M

/-- **The carried input depends on its object only up to isomorphism.**  So it may be checked at
any representative of `K ⊗ᴸ_A (A ⊗[R] A)` -- for instance at the one [stacks 0E1U] produces -- and
the result transported to the object the clause names.

This is the naturality square of the comparison at `(𝟙, e.hom)`: the comparison at `M` followed by
an isomorphism is an epimorphism, and it factors the comparison at `N`. -/
theorem diagonalHomCohomologyBaseChangeEpiAt_of_iso
    {M N : DerivedCategory (ModuleCat.{u} (A ⊗[R] A))} (e : M ≅ N)
    (h : DiagonalHomCohomologyBaseChangeEpiAt R A R' M) :
    DiagonalHomCohomologyBaseChangeEpiAt R A R' N := by
  let i : (Opposite.op (diagonalSingle R A), M) ≅ (Opposite.op (diagonalSingle R A), N) :=
    (Iso.refl (Opposite.op (diagonalSingle R A))).prod e
  have : Epi ((homCohomologyExtensionComparison (envelopingBaseChangeRingHom R A R') 0).app
    (Opposite.op (diagonalSingle R A), M)) := h
  exact epi_of_epi_fac
    ((homCohomologyExtensionComparison (envelopingBaseChangeRingHom R A R') 0).naturality i.hom)

/-- **The carried input, split into its two halves at the diagonal.**  The input holds at `M` as
soon as both factors of the comparison are epimorphisms there: the comparison between degree-zero
cohomology and derived base change at `RHom_B(A, M)`, and degree-zero cohomology of the
derived-Hom base-change transformation of [stacks 0E1X] at `(A, M)`.

This is `Dualizing.epi_homCohomologyExtensionComparison_app` at the diagonal.  It is where the
input has to be attacked: neither factor holds at every `M`, and the module documentation records
a pair of rings and an `M` at which the first one fails. -/
theorem diagonalHomCohomologyBaseChangeEpiAt_of_epi
    (M : DerivedCategory (ModuleCat.{u} (A ⊗[R] A)))
    (h₁ : Epi ((cohomologyExtensionComparison (envelopingBaseChangeRingHom R A R') 0).app
      ((Stacks.DerivedHom.ScalarTransportedInternalHom.hom.{u, u} (A ⊗[R] A)).obj
        (Opposite.op (diagonalSingle R A), M))))
    (h₂ : Epi ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))) 0).map
      ((derivedHomExtensionComparison (envelopingBaseChangeRingHom R A R')).app
        (Opposite.op (diagonalSingle R A), M)))) :
    DiagonalHomCohomologyBaseChangeEpiAt R A R' M :=
  epi_homCohomologyExtensionComparison_app _ 0 _ _ h₁ h₂

variable [Module.Flat R A]

/-- **Stacks Project, Tag 0E2F, the "moreover" clause.**  Let `R → A` be flat of finite
presentation, put `B = A ⊗[R] A`, and let `ξ : A ⟶ K ⊗ᴸ_A B` in `D(B)` generate the cyclic
`B`-module `Hom_{D(B)}(A, K ⊗ᴸ_A B)`.  Let `R → R'` be any ring map, put `A' = A ⊗[R] R'`,
`B' = A' ⊗[R'] A'` and `K' = K ⊗ᴸ_A A'`.  Then the derived base change of `ξ` along `B → B'`
generates the cyclic `B'`-module `Hom_{D(B')}(A', K' ⊗ᴸ_{A'} B')`.

Generation is `Submodule.span = ⊤` on the single element, and the Hom module over `B'` is reached
through arbitrary identifications `eΔ`, `eM` of the base changes of the diagonal and of
`K ⊗ᴸ_A B` with the diagonal of `B'` and with `K' ⊗ᴸ_{A'} B'`; see the module documentation.
That `K` is a relative dualizing complex is not needed and is not assumed, so this is more
general than the source's statement.

The hypothesis `hepi` is the carried input `Dualizing.DiagonalHomCohomologyBaseChangeEpiAt`, read
at the single object `K ⊗ᴸ_A B` the proof consumes.
`Dualizing.span_derivedBaseChange_diagonalGenerator` is the same statement with that input
quantified over every object of `D(B)`. -/
theorem span_derivedBaseChange_diagonalGenerator_at
    (K : DerivedCategory (ModuleCat.{u} A))
    (hepi : DiagonalHomCohomologyBaseChangeEpiAt R A R'
      ((diagonalDerivedExtension R A).obj K))
    (ξ : diagonalSingle R A ⟶ (diagonalDerivedExtension R A).obj K)
    (hξ : Submodule.span (A ⊗[R] A) ({ξ} : Set _) = ⊤) :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    ∀ (eΔ : (totalDerivedExtensionScalars.{u, u, u}
            (envelopingBaseChangeRingHom R A R')).functor.obj (diagonalSingle R A) ≅
          diagonalSingle R' (A ⊗[R] R'))
      (eM : (totalDerivedExtensionScalars.{u, u, u}
            (envelopingBaseChangeRingHom R A R')).functor.obj
              ((diagonalDerivedExtension R A).obj K) ≅
          (diagonalDerivedExtension R' (A ⊗[R] R')).obj
            ((totalDerivedExtensionScalars.{u, u, u}
              (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K)),
      Submodule.span ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))
        ({eΔ.inv ≫ (totalDerivedExtensionScalars.{u, u, u}
          (envelopingBaseChangeRingHom R A R')).functor.map ξ ≫ eM.hom} : Set _) = ⊤ := by
  let : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
  intro eΔ eM
  exact span_singleton_of_postcomp_surjective _
    (diagonal_endomorphism_eq_smul_id R' (A ⊗[R] R'))
    (postcomp_surjective_iso eΔ eM _
      (postcomp_surjective_of_homCohomologyExtension_epi (envelopingBaseChangeRingHom R A R')
        (diagonalSingle R A) ((diagonalDerivedExtension R A).obj K) ξ
        (postcomp_surjective_of_span_singleton ξ hξ) hepi))

/-- **Stacks Project, Tag 0E2F, the "moreover" clause.**  Let `R → A` be flat of finite
presentation, put `B = A ⊗[R] A`, and let `ξ : A ⟶ K ⊗ᴸ_A B` in `D(B)` generate the cyclic
`B`-module `Hom_{D(B)}(A, K ⊗ᴸ_A B)`.  Let `R → R'` be any ring map, put `A' = A ⊗[R] R'`,
`B' = A' ⊗[R'] A'` and `K' = K ⊗ᴸ_A A'`.  Then the derived base change of `ξ` along `B → B'`
generates the cyclic `B'`-module `Hom_{D(B')}(A', K' ⊗ᴸ_{A'} B')`.

This is `Dualizing.span_derivedBaseChange_diagonalGenerator_at` with the carried input quantified
over every object of `D(B)`; the clause consumes it at one object only.

The hypothesis `hepi` is the carried input `Dualizing.DiagonalHomCohomologyBaseChangeEpi`. -/
theorem span_derivedBaseChange_diagonalGenerator
    (hepi : DiagonalHomCohomologyBaseChangeEpi R A R')
    (K : DerivedCategory (ModuleCat.{u} A))
    (ξ : diagonalSingle R A ⟶ (diagonalDerivedExtension R A).obj K)
    (hξ : Submodule.span (A ⊗[R] A) ({ξ} : Set _) = ⊤) :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    ∀ (eΔ : (totalDerivedExtensionScalars.{u, u, u}
            (envelopingBaseChangeRingHom R A R')).functor.obj (diagonalSingle R A) ≅
          diagonalSingle R' (A ⊗[R] R'))
      (eM : (totalDerivedExtensionScalars.{u, u, u}
            (envelopingBaseChangeRingHom R A R')).functor.obj
              ((diagonalDerivedExtension R A).obj K) ≅
          (diagonalDerivedExtension R' (A ⊗[R] R')).obj
            ((totalDerivedExtensionScalars.{u, u, u}
              (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K)),
      Submodule.span ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))
        ({eΔ.inv ≫ (totalDerivedExtensionScalars.{u, u, u}
          (envelopingBaseChangeRingHom R A R')).functor.map ξ ≫ eM.hom} : Set _) = ⊤ :=
  span_derivedBaseChange_diagonalGenerator_at R A R' K
    (hepi ((diagonalDerivedExtension R A).obj K)) ξ hξ

/-- **The "moreover" clause of [stacks 0E2F] does not depend on the chosen generator.**  Two
generators of `Hom_{D(B)}(A, K ⊗ᴸ_A B)` have derived base changes spanning the same `B'`-submodule
of `Hom_{D(B')}(A', K' ⊗ᴸ_{A'} B')`, through any identifications `eΔ`, `eM`.  So the clause is a
property of the two ring maps `R → A` and `R → R'` alone.

Nothing is carried.  Two generators differ by a scalar of `B`, derived base change carries the
corresponding scalar endomorphism of the diagonal to an endomorphism of its base change, and the
endomorphisms of the diagonal over `B'` are exactly the scalars
(`Dualizing.diagonal_endomorphism_eq_smul_id`), so each of the two transported morphisms is a
`B'`-multiple of the other. -/
theorem span_derivedBaseChange_diagonalGenerator_congr
    (K : DerivedCategory (ModuleCat.{u} A))
    (ξ₁ ξ₂ : diagonalSingle R A ⟶ (diagonalDerivedExtension R A).obj K)
    (h₁ : Submodule.span (A ⊗[R] A) ({ξ₁} : Set _) = ⊤)
    (h₂ : Submodule.span (A ⊗[R] A) ({ξ₂} : Set _) = ⊤) :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    ∀ (eΔ : (totalDerivedExtensionScalars.{u, u, u}
            (envelopingBaseChangeRingHom R A R')).functor.obj (diagonalSingle R A) ≅
          diagonalSingle R' (A ⊗[R] R'))
      (eM : (totalDerivedExtensionScalars.{u, u, u}
            (envelopingBaseChangeRingHom R A R')).functor.obj
              ((diagonalDerivedExtension R A).obj K) ≅
          (diagonalDerivedExtension R' (A ⊗[R] R')).obj
            ((totalDerivedExtensionScalars.{u, u, u}
              (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K)),
      Submodule.span ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))
          ({eΔ.inv ≫ (totalDerivedExtensionScalars.{u, u, u}
            (envelopingBaseChangeRingHom R A R')).functor.map ξ₁ ≫ eM.hom} : Set _) =
        Submodule.span ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))
          ({eΔ.inv ≫ (totalDerivedExtensionScalars.{u, u, u}
            (envelopingBaseChangeRingHom R A R')).functor.map ξ₂ ≫ eM.hom} : Set _) := by
  let : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
  intro eΔ eM
  let D := (totalDerivedExtensionScalars.{u, u, u}
    (envelopingBaseChangeRingHom R A R')).functor
  have key : ∀ (ζ η : diagonalSingle R A ⟶ (diagonalDerivedExtension R A).obj K),
      Submodule.span (A ⊗[R] A) ({η} : Set _) = ⊤ →
      Submodule.span ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))
          ({eΔ.inv ≫ D.map ζ ≫ eM.hom} : Set _) ≤
        Submodule.span ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))
          ({eΔ.inv ≫ D.map η ≫ eM.hom} : Set _) := by
    intro ζ η hη
    have hmem : ζ ∈ Submodule.span (A ⊗[R] A) ({η} : Set _) := by simp [hη]
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hmem
    have hfac : eΔ.inv ≫ D.map (b • η) ≫ eM.hom =
        (eΔ.inv ≫ D.map (b • 𝟙 (diagonalSingle R A)) ≫ eΔ.hom) ≫
          (eΔ.inv ≫ D.map η ≫ eM.hom) := by
      rw [show b • η = (b • 𝟙 (diagonalSingle R A)) ≫ η by
        rw [Linear.smul_comp, Category.id_comp], D.map_comp]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hfac]
    exact span_singleton_comp_le _ _ (diagonal_endomorphism_eq_smul_id R' (A ⊗[R] R'))
  exact le_antisymm (key ξ₁ ξ₂ h₂) (key ξ₂ ξ₁ h₁)

end Enveloping

end Dualizing

end
