module

public import StacksFrontier.AlgebraicGeometry.Quot.NegativeExtLocusHomFibres
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTensor

/-!
# The steps of the proof of Stacks 0DKY

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces over a scheme
`S`, with `Y` quasi-compact and quasi-separated, let `E` be a `Y`-perfect and `K` a
pseudo-coherent object of `D(𝒪_X)`.  Stacks 0DKY gives a pseudo-coherent `L ∈ D(𝒪_Y)` with
`Rf_* R𝓗om(K, E) = R𝓗om(L, 𝒪_Y)`, and the same after every base change.  The source's proof
is:

1. write `K = hocolim Kₙ` with `Kₙ` perfect (Stacks 0DKB);
2. `Mₙ = Rf_* R𝓗om(Kₙ, E) = Rf_*(Kₙ^∨ ⊗^L E)` is perfect and its formation commutes with base
   change (Stacks 0DKS and 0DKX);
3. **the window**: if `E` has Tor amplitude in `[a, b]` over `f⁻¹𝒪_Y`, then `Mₙ₊₁ ⟶ Mₙ` is an
   isomorphism on `τ_{≤ n + a}`, after any base change (Stacks 0DKD);
4. **the fibre test**: looking at the points of `Y` with values in a field, the cone of
   `Mₙ₊₁ ⟶ Mₙ` has Tor amplitude in `[n + a, mₙ]` (Stacks 0BCD), so `Lₙ = Mₙ^∨ ⟶ Lₙ₊₁` is an
   isomorphism on `τ_{≥ -n - a}`, and `L = hocolim Lₙ` is pseudo-coherent (Stacks 0DKB);
5. `R𝓗om(K, E) = R lim R𝓗om(Kₙ, E)` (Stacks 0A0A), `Rf_*` commutes with `R lim`, and
   `R lim Lₙ^∨ = R𝓗om(L, 𝒪_Y)`.

This file states, as propositions, the inputs not yet proved here and the three internal steps
of the proof that each need a development of their own, so that the assembly of Stacks 0DKY can
be written against them.  Nothing here is proved and nothing is registered.

## Main definitions

Inputs not yet proved here:

* `AlgebraicGeometry.Space.PseudoCoherentHomotopyColimitApproximation`: Stacks 0DKB (not yet proved
  here), in exactly the shape of
  `AlgebraicGeometry.Space.isPseudoCoherent_iff_exists_isHomotopyColimitWith`, at the standard
  model.
* `AlgebraicGeometry.Space.RelativelyPerfectPushforwardBaseChange`: Stacks 0DKX (not yet proved
  here).
* `AlgebraicGeometry.Space.TensorPerfectRelativelyPerfect`: Stacks 0DKS, assertion (2) (not yet
  proved here).

The internal steps:

* `AlgebraicGeometry.Space.RelativelyPerfectHomWindow`: step 3, the window.
* `AlgebraicGeometry.Space.PerfectDualIsoOfFieldFibres`: step 4, the fibre test.
* `AlgebraicGeometry.Space.PullSheafHomPerfectSystemIso`: derived pullback commutes with
  `R𝓗om` out of a system of perfect objects (Stacks 08JF and 08JJ), used in steps 2 and 5.
* `AlgebraicGeometry.Space.RelativeDerivedHomDualNaturality`: the naturality, in the test scheme,
  of the identification `Hom(K_T, E_T) = Hom(L_T, 𝒪_T)` built from steps 1-5, which is the form
  part (3) of Stacks 0DLC consumes
  (`AlgebraicGeometry.Space.RelativeDerivedHomDualExistsNaturalCompatible`).

## Indexing

Systems are indexed by `ℕ` from `0`, as in Stacks 0DKB: the member `Kₙ` at index `n` is
the source's `K_{n+1}`, and the condition on `cₙ : Kₙ ⟶ K` is in degree `-(n + 1)`.  The
truncation conditions of steps 3 and 4 are stated on cohomology, with the bounds existentially
quantified where the source's constant `a` appears, so that off-by-one conventions do not change
the propositions.

## References

* [Stacks Project, Tag 0DKY](https://stacks.math.columbia.edu/tag/0DKY)
* [Stacks Project, Tag 0DKB](https://stacks.math.columbia.edu/tag/0DKB)
* [Stacks Project, Tag 0DKX](https://stacks.math.columbia.edu/tag/0DKX)
* [Stacks Project, Tag 0DKS](https://stacks.math.columbia.edu/tag/0DKS)
* [Stacks Project, Tag 0DKD](https://stacks.math.columbia.edu/tag/0DKD)
* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

attribute [local instance] AlgebraicGeometry.Space.inverseImageRingedSite_hasWeakSheafify_over
  AlgebraicGeometry.Space.inverseImageRingedSite_wEqualsLocallyBijective_over
  AlgebraicGeometry.Space.inverseImageRingedSite_hasDerivedCategory
  Stacks.hasSheafCompose_forget₂_commRingCat
  AlgebraicGeometry.RingedSite.sliceHasSheafify
  AlgebraicGeometry.RingedSite.sliceWEqualsLocallyBijective
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteLimits
  AlgebraicGeometry.RingedSite.sliceRestrictionPreservesFiniteColimits
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasDerivedCategory
  AlgebraicGeometry.RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_sheafTensor_obj_additive
  AlgebraicGeometry.Space.inverseImageRingedSite_slice_hasMapBifunctor
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor
  AlgebraicGeometry.Space.instModulesHasDerivedCategory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- `D(𝒪_X)` has countable direct sums: the `𝒪_X`-modules form a Grothendieck abelian category
(`AlgebraicGeometry.Space.isGrothendieckAbelian_modules`).  This is what the derived colimits
`AlgebraicGeometry.Space.PseudoCoherentHomotopyColimitApproximation` and
`AlgebraicGeometry.Space.RelativeDerivedHomDualNaturality` mention need. -/
theorem hasColimitsOfShape_discrete_nat_derivedModules (X : AlgebraicSpaces B S hS) :
    HasColimitsOfShape (Discrete ℕ) (derivedModules B S hS X) :=
  have := isGrothendieckAbelian_modules B S hS X.1 X.2
  have := Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory
    (Modules.{u, u} B S hS X.1 X.2) (ULift.{u} ℕ)
  hasColimitsOfShape_of_equivalence (Discrete.equivalence Equiv.ulift)

/-! ### Inputs not yet proved here -/

/-- **Stacks 0DKB** (not yet proved here; registered there as
`AlgebraicGeometry.Space.isPseudoCoherent_iff_exists_isHomotopyColimitWith`; pending here), as a
proposition, at the standard model: on a quasi-compact and quasi-separated algebraic space `X`,
an object `K` of `D(𝒪_X)` is pseudo-coherent if and only if `K = hocolim Kₙ` for a system of
perfect objects `Kₙ` whose coprojections `cₙ : Kₙ ⟶ K` are isomorphisms on `τ_{≥ -(n+1)}`. -/
def PseudoCoherentHomotopyColimitApproximation : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) (X : AlgebraicSpaces B S hS),
    IsQuasiCompactSpace B S hS X.1 → IsAbsolutelyQuasiSeparated B S hS hZ X.1 →
    ∀ K : derivedModules B S hS X,
      haveI := hasColimitsOfShape_discrete_nat_derivedModules B S hS X
      (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K ↔
        ∃ (F : ℕ ⥤ derivedModules B S hS X) (c : ∀ n, F.obj n ⟶ K),
          (∀ n, (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect (F.obj n)) ∧
            (∀ n : ℕ,
              IsIso ((DerivedCategory.TStructure.t.truncGE (-((n : ℤ) + 1))).map (c n))) ∧
              IsHomotopyColimitWith F K c

/-- **Stacks 0DKX** (not yet proved here), as a proposition: for a flat, proper,
finitely presented morphism `f : X ⟶ Y` of algebraic spaces and a `Y`-perfect `E` in `D(𝒪_X)`,
`Rf_* E` is perfect, and its formation commutes with arbitrary base change: for every cartesian
square `X' = X ×_Y Y'` the canonical base change map `Lg^* Rf_* E ⟶ Rf'_* L(g')^* E` of
`AlgebraicGeometry.Space.smallEtaleDerivedModuleBaseChangeMap` (Stacks 07A7; the map Stacks
0A1K is stated for) is an isomorphism. -/
def RelativelyPerfectPushforwardBaseChange : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y), IsProper B S hS f.hom →
    ∀ (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
      (E : derivedModules B S hS X),
      IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E →
      (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect ((spaceDerivedPushforward B S hS f).obj E) ∧
        ∀ {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
          (hpb : IsPullback g' f' f g),
          IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' hpb.w E)

/-- **Stacks 0DKS, assertion (2)** (not yet proved here), as a proposition: for a flat
morphism `f : X ⟶ Y` of algebraic spaces locally of finite presentation, `K ⊗^L M` is
`Y`-perfect if `K` is perfect and `M` is `Y`-perfect. -/
def TensorPerfectRelativelyPerfect : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hflat : IsFlat B S hS f.hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS f.hom) (K M : derivedModules B S hS X),
    (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect K →
    IsPerfectRelativeToCanonical B S hS f hflat hlfp M →
    IsPerfectRelativeToCanonical B S hS f hflat hlfp
      (((smallEtaleDerivedTensor B S hS X).obj K).obj M)

/-! ### The internal steps -/

/-- **The window of the proof of Stacks 0DKY** (step 3; internal, proved as
`AlgebraicGeometry.Space.relativelyPerfectHomWindow` in
`StacksFrontier/AlgebraicGeometry/Quot/RelativelyPerfectHomWindow.lean`), as a proposition.
For a proper, flat, finitely presented `f : X ⟶ Y` with `Y` quasi-compact and quasi-separated and
a `Y`-perfect `E` in `D(𝒪_X)`, there is an integer `a` such that for every cartesian square
`X' = X ×_Y Y'` (projections `g' : X' ⟶ X`, `f' : X' ⟶ Y'`) and every morphism `φ : A ⟶ A'` of
perfect objects of `D(𝒪_X)` which is an isomorphism on cohomology in degrees `≥ k`, the induced
map
`Rf'_* R𝓗om(L(g')^*A', L(g')^*E) ⟶ Rf'_* R𝓗om(L(g')^*A, L(g')^*E)`
is an isomorphism on cohomology in degrees `≤ a - k`.

In the source: `E` has Tor amplitude in some `[a₀, b₀]` over `f⁻¹𝒪_Y` (`X` being
quasi-compact), so does `L(g')^*E` over `f'⁻¹𝒪_{Y'}` (Stacks 0DKD), in particular it lives in
degrees `≥ a₀`; the cone of `φ` is perfect and lives in degrees `≤ k - 1`, hence so does its
pullback, and `R𝓗om` out of it into `L(g')^*E` lives in degrees `≥ a₀ - k + 1`, which `Rf'_*`
preserves. -/
def RelativelyPerfectHomWindow : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
    IsQuasiCompactSpace B S hS Y.1 → IsAbsolutelyQuasiSeparated B S hS hZ Y.1 →
    IsProper B S hS f.hom →
    ∀ (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
      (E : derivedModules B S hS X),
      IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E →
      ∃ a : ℤ, ∀ {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y),
        IsPullback g' f' f g →
        ∀ {A A' : derivedModules B S hS X} (φ : A ⟶ A'),
          (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect A →
          (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect A' →
          ∀ k : ℤ, (∀ i : ℤ, k ≤ i →
              IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).map φ)) →
            ∀ i : ℤ, i ≤ a - k →
              IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) i).map
                ((spaceDerivedPushforward B S hS f').map
                  (((smallEtaleDerivedSheafHom B S hS X').map
                    (((smallEtaleDerivedPullbackData B S hS).pull g').map φ).op).app
                      (((smallEtaleDerivedPullbackData B S hS).pull g').obj E))))

/-- **The fibre test of the proof of Stacks 0DKY** (step 4; internal, pending), as a
proposition.  Let `ψ : M' ⟶ M` be a morphism of perfect objects of `D(𝒪_Y)` such that at every
point `y : Spec(k) ⟶ Y` with values in a field the derived pullback `Ly^*ψ` is an isomorphism on
cohomology in degrees `≤ j`.  Then the dual map `ψ^∨ : M^∨ ⟶ M'^∨` is an isomorphism on
cohomology in degrees `> -j`.

In the source: the cone `C` of `ψ` is perfect with `Ly^*C` in degrees `≥ j` at every field point,
so by Stacks 0BCD, on an étale neighbourhood of every point, `C` has Tor amplitude in `[j, m]`
for some `m`; its dual then lives in degrees `≤ -j`, and `M^∨ ⟶ M'^∨` sits in a distinguished
triangle with it. -/
def PerfectDualIsoOfFieldFibres : Prop :=
  ∀ (Y : AlgebraicSpaces B S hS) {M M' : derivedModules B S hS Y} (ψ : M' ⟶ M),
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect M →
    (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect M' →
    ∀ j : ℤ,
      (∀ T₀ : SchemesOver Y, Stack.IsFieldObject B S hS T₀.left → ∀ i : ℤ, i ≤ j →
        IsIso ((DerivedCategory.homologyFunctor
          (Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj T₀.left).1
            ((schemeSpaceFunctor B S hS).obj T₀.left).2) i).map
          (((smallEtaleDerivedPullbackData B S hS).pull T₀.hom).map ψ))) →
      ∀ i : ℤ, -j < i →
        IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).map
          (((smallEtaleDerivedSheafHom B S hS Y).map ψ.op).app (structureObject B S hS Y)))

/-- **Derived pullback commutes with derived internal Hom out of perfect objects, along an inverse
system** (internal, pending; Stacks 08JF with Stacks 08JJ), as a proposition: for a morphism
`g : X ⟶ Y` of algebraic spaces, a system `n ↦ Fₙ` of perfect objects of `D(𝒪_Y)` and any
`E ∈ D(𝒪_Y)`, the inverse systems `n ↦ Lg^* R𝓗om(Fₙ, E)` and `n ↦ R𝓗om(Lg^*Fₙ, Lg^*E)` are
isomorphic.

In the source this is the canonical map `Lg^* R𝓗om(A, E) ⟶ R𝓗om(Lg^*A, Lg^*E)` of Stacks 08JF,
which is natural in `A` and an isomorphism for `A` perfect (locally `A` is a finite complex of
finite free modules). -/
def PullSheafHomPerfectSystemIso : Prop :=
  ∀ {X Y : AlgebraicSpaces B S hS} (g : X ⟶ Y) (F : ℕ ⥤ derivedModules B S hS Y),
    (∀ n, (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect (F.obj n)) →
    ∀ E : derivedModules B S hS Y,
      Nonempty (F.op ⋙ (smallEtaleDerivedSheafHom B S hS Y).flip.obj E ⋙
          (smallEtaleDerivedPullbackData B S hS).pull g ≅
        (F ⋙ (smallEtaleDerivedPullbackData B S hS).pull g).op ⋙
          (smallEtaleDerivedSheafHom B S hS X).flip.obj
            (((smallEtaleDerivedPullbackData B S hS).pull g).obj E))

/-- **The naturality step of the proof of Stacks 0DKY** (internal, pending), as a proposition:
the identification `Hom(K_T, E_T) = Hom(L_T, 𝒪_T)` which the construction of the proof gives at
each test scheme `T` over `Y` is natural in `T`.

Precisely, in the situation of Stacks 0DKY, let `K = hocolim Kₙ` with `Kₙ` perfect and
coprojections `cₙ` which are isomorphisms on cohomology in degrees `≥ -(n + 1)`, let
`L = hocolim Lₙ` with `Lₙ` perfect and coprojections `c'ₙ` which are isomorphisms on cohomology in
degrees `> b - n` for some `b`, and let `θ : (n ↦ Lₙ^∨) ≅ (n ↦ Rf_* R𝓗om(Kₙ, E))` be an isomorphism
of inverse systems on `Y`.  Assume that the formation of each `Rf_* R𝓗om(Kₙ, E)` commutes with
every base change through the canonical map, and that the window of step 3 holds for the
transition maps of the system: for some `a`, after every cartesian base change,
`Rf'_* R𝓗om(L(g')^*Kₙ₊₁, L(g')^*E) ⟶ Rf'_* R𝓗om(L(g')^*Kₙ, L(g')^*E)` is an isomorphism on
cohomology in degrees `≤ a + n`.  Then the functor `T ↦ Hom(K_T, E_T)` on the test schemes over
`Y` is isomorphic to the functor `T ↦ Hom(L_T, 𝒪_T)`.

In the source this is implicit in "the formula continues to hold after any base change". At a test
scheme `T`, both sides are the limit of `Hom(K_{n,T}, E_T) = H⁰(T, Lg^*Mₙ) = Hom(L_{n,T}, 𝒪_T)`
(the Milnor sequences of the two derived colimits, whose `lim¹` terms vanish by the window), and
these identifications are natural in `T` because the base change maps are the canonical ones. -/
def RelativeDerivedHomDualNaturality : Prop :=
  ∀ (hZ : B.Contains (⊤_ Scheme.{u})) {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
    IsQuasiCompactSpace B S hS Y.1 → IsAbsolutelyQuasiSeparated B S hS hZ Y.1 →
    IsProper B S hS f.hom →
    ∀ (hflat : IsFlat B S hS f.hom) (hfp : IsFinitePresentation B S hS f.hom)
      (K E : derivedModules B S hS X),
      IsPerfectRelativeToCanonical B S hS f hflat hfp.1 E →
      (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K →
      haveI := hasColimitsOfShape_discrete_nat_derivedModules B S hS X
      haveI := hasColimitsOfShape_discrete_nat_derivedModules B S hS Y
      ∀ (F : ℕ ⥤ derivedModules B S hS X) (c : ∀ n, F.obj n ⟶ K),
        (∀ n, (smallEtaleRingedSite B S hS X.1 X.2).IsPerfect (F.obj n)) →
        (∀ (n : ℕ) (i : ℤ), -((n : ℤ) + 1) ≤ i →
          IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).map
            (c n))) →
        IsHomotopyColimitWith F K c →
      ∀ (G : ℕ ⥤ derivedModules B S hS Y) (L : derivedModules B S hS Y)
        (c' : ∀ n, G.obj n ⟶ L),
        (∀ n, (smallEtaleRingedSite B S hS Y.1 Y.2).IsPerfect (G.obj n)) →
        (∃ b : ℤ, ∀ (n : ℕ) (i : ℤ), b - (n : ℤ) < i →
          IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y.1 Y.2) i).map
            (c' n))) →
        IsHomotopyColimitWith G L c' →
        (G.op ⋙ (smallEtaleDerivedSheafHom B S hS Y).flip.obj (structureObject B S hS Y) ≅
          F.op ⋙ (smallEtaleDerivedSheafHom B S hS X).flip.obj E ⋙
            spaceDerivedPushforward B S hS f) →
        (∀ (n : ℕ) {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ Y)
          (hpb : IsPullback g' f' f g),
          IsIso (smallEtaleDerivedModuleBaseChangeMap B S hS f g f' g' hpb.w
            (((smallEtaleDerivedSheafHom B S hS X).obj (Opposite.op (F.obj n))).obj E))) →
        (∃ a : ℤ, ∀ (n : ℕ) {X' Y' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (f' : X' ⟶ Y')
          (g : Y' ⟶ Y), IsPullback g' f' f g → ∀ i : ℤ, i ≤ a + n →
          IsIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS Y'.1 Y'.2) i).map
            ((spaceDerivedPushforward B S hS f').map
              (((smallEtaleDerivedSheafHom B S hS X').map
                (((smallEtaleDerivedPullbackData B S hS).pull g').map
                  (F.map (homOfLE (Nat.le_succ n)))).op).app
                    (((smallEtaleDerivedPullbackData B S hS).pull g').obj E))))) →
        Nonempty (relativeDerivedHom f K E ≅
          (smallEtaleDerivedPullbackData B S hS).relHomFunctor
            (smallEtaleDerivedPullbackData_isCoherent B S hS) (schemesOverCone Y) L
            (structureObject B S hS Y))

end AlgebraicGeometry.Space

end
