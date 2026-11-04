module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Sheaves.Abelian
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.AlgebraicGeometry.LocalSchemesFpqcCover.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Higher direct images from a retrocompact open of a one-dimensional scheme

Let `X` be a scheme all of whose local rings are Noetherian of dimension at most one and let
`U ⊆ X` be a retrocompact open with inclusion `j = U.ι`. [Stacks, Tag 09N8] asserts that
`R ᵖ j_* ℱ = 0` for `p > 0` and every quasi-coherent `𝒪_U`-module `ℱ`.

The source's proof has three steps. Vanishing is checked at stalks; formation of `R ᵖ j_*`
commutes with the flat base change `Spec 𝒪_{X,x} ⟶ X`, which reduces the question to the
spectrum of a Noetherian local ring of dimension at most one; and over such a ring the
preimage of `U` is an *affine* open, so the vanishing is [Stacks, Tag 01XC].

This file proves the middle step's geometry and the reduction, and assembles the tag from
three hypotheses, each the statement of a result that does not exist in Mathlib or in this
repository at this revision. They are listed in the implementation notes.

## Main results

* `AlgebraicGeometry.isAffineOpen_of_krullDimLE_one`: **every** open of the spectrum of a
  Noetherian local ring of dimension at most one is an affine open. This is the geometric
  content of [Stacks, Tag 09N8]: such a spectrum has a closed point and finitely many other
  points, no two of which specialize to each other, so an open not containing the closed point
  is a finite discrete scheme and an open containing it is everything.
* `AlgebraicGeometry.isZero_of_forall_isZero_stalk`: a sheaf of modules on a scheme with
  vanishing stalks is a zero object.
* `Stacks.AlgebraicGeometry.OneDimensionalLocal.isZero_rightDerived_pushforward_of_isRetrocompact`:
  **the conclusion of [Stacks, Tag 09N8]**, from the three hypotheses below.
* `Stacks.AlgebraicGeometry.OneDimensionalLocal`'s
  `higherDirectImageVanishingAffine_of_rightDerivedPlus`: the first hypothesis follows from
  [Stacks, Tag 01XC] in its `ℤ`-indexed form, so it does not matter which indexing that tag is
  eventually proved in.

## Main definitions

The three hypotheses, one definition each:

* `Stacks.AlgebraicGeometry.OneDimensionalLocal.HigherDirectImageVanishingAffine` is
  [Stacks, Tag 01XC];
* `Stacks.AlgebraicGeometry.OneDimensionalLocal.FlatBaseChangeVanishing` is the vanishing half
  of [Stacks, Tag 02KH] part (1);
* `Stacks.AlgebraicGeometry.OneDimensionalLocal.PullbackFromSpecStalkDetectsStalk` is
  [Stacks, Tag 0098] along `Spec 𝒪_{X,x} ⟶ X`.

## Implementation notes

**Cohomology indexing.** `R ᵖ j_*` is the `ℕ`-indexed `CategoryTheory.Functor.rightDerived` of
`AlgebraicGeometry.Scheme.Modules.pushforward`, as [Stacks, Tag 09N8] is stated in this
development. It is *not* the `ℤ`-indexed `CategoryTheory.Functor.rightDerivedPlus`. The two are
nevertheless interchangeable in non-negative degrees: `Stacks.DerivedIndexing.rightDerivedIso`
is the comparison isomorphism and
`Stacks.DerivedIndexing.isZero_rightDerived_obj_iff` transports vanishing both ways. All three
hypotheses below are therefore stated in the `ℕ`-indexing, to match the conclusion; that this
costs nothing is recorded for the first of them by
`higherDirectImageVanishingAffine_of_rightDerivedPlus`, which derives it from the `ℤ`-indexed
form, and the same two-line argument serves for the other two.

**The three hypotheses, and why they are hypotheses.**

* `HigherDirectImageVanishingAffine` is [Stacks, Tag 01XC]: for an affine morphism `q` and a
  quasi-coherent `G`, `R ⁿ q_* G = 0` for `n > 0`. Mathlib has no vanishing theorem for the
  higher direct images of any morphism, and this repository has none either: the nearest
  results are `Stacks.AlgebraicGeometry.DerivedPushforward.*`, which treat only degree zero,
  and `Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj`, which is the formal vanishing in
  *negative* degrees. Proving it is the affine-cohomology vanishing of [Stacks, Tag 01XB],
  which belongs to the cohomology-of-schemes chapter.
* `FlatBaseChangeVanishing` is the half of [Stacks, Tag 02KH] part (1) that this proof uses:
  for a cartesian square with `g` flat and `f` quasi-compact and quasi-separated, vanishing of
  `R ⁿ f'_* (g')^* G` forces vanishing of `g^* R ⁿ f_* G`. Stating only the implication rather
  than the base-change isomorphism makes the hypothesis strictly weaker, hence the theorem
  strictly stronger. Only the *degree-zero* case of Tag 02KH is available here
  (`Stacks.AlgebraicGeometry.PicardBaseChange.isPushout_appTop_baseChange`, and over a field
  `Stacks.AlgebraicGeometry.ProperGeomConnected.isPushout_appTop_fieldBaseChange`), and
  degree zero is of no use for a statement about `p > 0`.
* `PullbackFromSpecStalkDetectsStalk` is [Stacks, Tag 0098] — the stalk of a pullback of
  sheaves of modules — specialized to `g = X.fromSpecStalk x`, where the stalk of
  `Spec 𝒪_{X,x}` at its closed point is `𝒪_{X,x}` itself and the tensor product is therefore
  trivial, so that `(g^* M)` vanishing forces `M_x` to vanish. The repository proves Tag 0098
  as `PullbackStalkTensor.stalkPullbackTensorIso`, for the explicit tensor-formula model of the
  pullback and only for `TopCat.{0}`, so that one does not apply to `Scheme.{u}`.

  A second proof, `RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv`
  (`StacksFrontier/Topology/Sheaves/RingedSpace/ModulePullbackStalkAdjunction.lean`, carrying
  `@[stacks 0098]`), *does* apply, and **is importable**: it is for the adjunction-defined
  pullback — the functor `Scheme.Modules.pullback` computes — at an arbitrary universe `u`, and
  it discharges this hypothesis outright, with no `set_option` of any kind in its file.

  It took some work to get there, and the route is worth knowing because the same wall recurs.
  The proof originally needed four `backward.isDefEq.respectTransparency false` scopes, whose
  root cause was Tag 08BQ's skyscraper API: `OXModule.skyscraperPOM` is built on a `dite` and
  lives over a ring presheaf spelled differently from Mathlib's, so every comparison failed the
  `implicit`-transparency check. All four are now gone, by adding an `eqToHom`-free section API
  to `StacksFrontier/Topology/Sheaves/Cohomology/KFlat/FlatModuleSheavesAndStalks.lean` —
  `OXModule.skyscraperPOMPresheafIso`,
  `OXModule.skyscraperPOMPushforwardIso` and `OXModule.skyscraperPOM_presheaf_smul` — and
  deleting the three declarations the options were protecting rather than patching them.

Each hypothesis is universe-monomorphic in the single universe `u` of the ambient schemes,
exactly as the conclusion is; none of them quantifies over a universe the conclusion does not.

**Why the reduction cannot avoid the local ring.** Restricting to an affine open `W = Spec A`
does not help: the hypothesis is that the *local rings* of `X` are Noetherian, which does not
make `A` Noetherian, and the finiteness of `minimalPrimes` used below is a theorem about
Noetherian rings. Passing to `𝒪_{X,x}` is what makes that finiteness available, and it is
`fromSpecStalk` rather than an open immersion, whence the need for flat base change.

**Discreteness rather than a point count.** The source enumerates the points of
`Spec 𝒪_{X,x}` as a closed point together with `x₁, …, xₙ` and then cites
[Stacks, Tag 02O0] for affineness of `{x₁, …, xᵣ}`. Here the open not containing the closed
point is shown to be finite — its points are minimal primes, by `Ring.krullDimLE_one_iff`, and
there are finitely many of those — and `T1`, hence discrete, and Mathlib's instance for a
finite discrete scheme gives affineness directly. No separate form of Tag 02O0 is needed.

## References

* [Stacks Project, Tag 09N8](https://stacks.math.columbia.edu/tag/09N8)
* [Stacks Project, Tag 01XC](https://stacks.math.columbia.edu/tag/01XC)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 00FR](https://stacks.math.columbia.edu/tag/00FR)
* [Stacks Project, Tag 02O0](https://stacks.math.columbia.edu/tag/02O0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u

namespace AlgebraicGeometry

/-! ### Opens of the spectrum of a one-dimensional Noetherian local ring -/

/-- **Every open of the spectrum of a Noetherian local ring of dimension at most one is an
affine open.**

If the open contains the closed point it is the whole spectrum, because every point of the
spectrum of a local ring specializes to the closed point. Otherwise each of its points is a
prime that is not maximal, hence — the dimension being at most one — a minimal prime; there
are finitely many of those, and no two minimal primes specialize to each other, so the open
is a finite discrete scheme.

This is the geometric step in the proof of [Stacks, Tag 09N8]; the source states it as
[Stacks, Tag 02O0] applied to the finite set of non-closed points. -/
@[ega "IV 21.12.9"]
theorem isAffineOpen_of_krullDimLE_one (R : CommRingCat.{u}) [IsLocalRing R]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R] (V : (Spec R).Opens) : IsAffineOpen V := by
  classical
  by_cases hclosed : IsLocalRing.closedPoint R ∈ V
  · have htop : V = ⊤ := by
      ext p
      exact ⟨fun _ ↦ trivial,
        fun _ ↦ (IsLocalRing.specializes_closedPoint p).mem_open V.2 hclosed⟩
    exact htop ▸ isAffineOpen_top _
  · have hnotmax (p : V) : ¬ p.1.asIdeal.IsMaximal := by
      intro hp
      have hp' : p.1 = IsLocalRing.closedPoint R :=
        PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal hp)
      exact hclosed (hp' ▸ p.2)
    have hmin (p : V) : p.1.asIdeal ∈ minimalPrimes R :=
      (Ring.krullDimLE_one_iff.mp ‹_› p.1.asIdeal p.1.2).resolve_right (hnotmax p)
    have hinj : Function.Injective
        (fun p : V ↦ (⟨p.1.asIdeal, hmin p⟩ : {I : Ideal R // I ∈ minimalPrimes R})) :=
      fun a b hab ↦ Subtype.ext (PrimeSpectrum.ext (congrArg Subtype.val hab))
    have : Finite {I : Ideal R // I ∈ minimalPrimes R} :=
      (minimalPrimes.finite_of_isNoetherianRing R).to_subtype
    have : Finite V := Finite.of_injective _ hinj
    have : T1Space V := t1Space_iff_specializes_imp_eq.mpr fun a b hab ↦
      Subtype.ext (PrimeSpectrum.ext
        (((IsMinimalPrime.iff_minimal _).mp (hmin b)).eq_of_le a.1.2
          ((PrimeSpectrum.le_iff_specializes a.1 b.1).mpr
            (hab.map continuous_subtype_val))))
    change IsAffine V.toScheme
    infer_instance

/-! ### Vanishing of a sheaf of modules is a condition on stalks -/

/-- **A sheaf of modules on a scheme with vanishing stalks is a zero object.** Vanishing of the
stalks makes the underlying sheaf of abelian groups a zero object, and the forgetful functor
`X.Modules ⥤ TopCat.Presheaf AddCommGrpCat X` is faithful and reflects isomorphisms. -/
theorem isZero_of_forall_isZero_stalk {X : Scheme.{u}} (M : X.Modules)
    (hM : ∀ x : X, IsZero (M.presheaf.stalk x)) : IsZero M := by
  let S : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of X) := ⟨M.presheaf, M.isSheaf⟩
  have hF : IsZero S := by
    rwa [TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero]
  let z : M ⟶ 0 := (isZero_zero _).from_ M
  let P := Scheme.Modules.toPresheaf X
  have hz : IsIso (P.map z) :=
    isIso_of_source_target_iso_zero (P.map z)
      ((sheafToPresheaf (Opens.grothendieckTopology (TopCat.of X))
        AddCommGrpCat).map_isZero hF).isoZero
      (P.map_isZero (isZero_zero _)).isoZero
  have : IsIso z := (isIso_iff_of_reflects_iso z P).mp hz
  exact (isZero_zero _).of_iso (asIso z)

end AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.OneDimensionalLocal

/-! ### The three missing inputs -/

/-- **[Stacks, Tag 01XC]**, in the `ℕ`-indexing of `CategoryTheory.Functor.rightDerived`: the
positive higher direct images of a quasi-coherent module along an affine morphism of schemes
vanish. -/
def HigherDirectImageVanishingAffine : Prop :=
  ∀ {Y Z : Scheme.{u}} (q : Y ⟶ Z) (G : Y.Modules), IsAffineHom q → G.IsQuasicoherent →
    ∀ n : ℕ, 0 < n → IsZero (((Scheme.Modules.pushforward q).rightDerived n).obj G)

section Indexing

attribute [local instance] HasDerivedCategory.standard

/-- **`HigherDirectImageVanishingAffine` is [Stacks, Tag 01XC] whichever indexing that tag is
stated in.** From the `ℤ`-indexed form — vanishing of
`(Scheme.Modules.pushforward q).rightDerivedPlus i` for `i > 0`, which is how the library states
it — the `ℕ`-indexed form follows by `Stacks.DerivedIndexing.isZero_rightDerived_obj_iff`. -/
theorem higherDirectImageVanishingAffine_of_rightDerivedPlus
    (h : ∀ {Y Z : Scheme.{u}} (q : Y ⟶ Z) (G : Y.Modules), IsAffineHom q → G.IsQuasicoherent →
      ∀ i : ℤ, 0 < i → IsZero (((Scheme.Modules.pushforward q).rightDerivedPlus i).obj G)) :
    HigherDirectImageVanishingAffine.{u} := fun q G hq hG n hn ↦
  (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff (Scheme.Modules.pushforward q) n G).2
    (h q G hq hG (n : ℤ) (by exact_mod_cast hn))

end Indexing

/-- **The vanishing half of [Stacks, Tag 02KH] part (1)**: for a cartesian square

```
T' --g'--> T
|          |
f'         f
v          v
S' --g---> S
```

with `g` flat and `f` quasi-compact and quasi-separated, and `G` a quasi-coherent
`𝒪_T`-module, vanishing of `R ⁿ f'_* (g')^* G` forces vanishing of `g^* R ⁿ f_* G`. This is
weaker than the base-change isomorphism the source proves, and is all that the proof of
[Stacks, Tag 09N8] uses. -/
def FlatBaseChangeVanishing : Prop :=
  ∀ {S S' T T' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T),
    IsPullback g' f' f g → Flat g → QuasiCompact f → QuasiSeparated f →
      ∀ (G : T.Modules), G.IsQuasicoherent → ∀ n : ℕ,
        IsZero (((Scheme.Modules.pushforward f').rightDerived n).obj
            ((Scheme.Modules.pullback g').obj G)) →
          IsZero ((Scheme.Modules.pullback g).obj
            (((Scheme.Modules.pushforward f).rightDerived n).obj G))

/-- **[Stacks, Tag 0098] along `Spec 𝒪_{X,x} ⟶ X`**: pullback along the canonical morphism
from the spectrum of a local ring detects vanishing of the stalk there. By Tag 0098 the stalk
of `(X.fromSpecStalk x)^* M` at the closed point is `M_x ⊗_{𝒪_{X,x}} 𝒪_{X,x} = M_x`, so this
is the implication that statement supplies. -/
def PullbackFromSpecStalkDetectsStalk : Prop :=
  ∀ (X : Scheme.{u}) (x : X) (M : X.Modules),
    IsZero ((Scheme.Modules.pullback (X.fromSpecStalk x)).obj M) →
      IsZero (M.presheaf.stalk x)

/-! ### Tag 09N8 -/

/-- **[Stacks, Tag 09N8].** Let `X` be a scheme all of whose local rings are Noetherian of
dimension at most one, let `U ⊆ X` be a retrocompact open and let `ℱ` be a quasi-coherent
`𝒪_U`-module. Then `R ᵖ U.ι_* ℱ = 0` for every `p > 0`.

The three hypotheses are the source's cited inputs [Stacks, Tag 01XC], [Stacks, Tag 02KH]
part (1) and [Stacks, Tag 0098]; see the module docstring for why each is a hypothesis. What
is proved here is the rest of the source's argument: vanishing is a condition on stalks, the
morphism `Spec 𝒪_{X,x} ⟶ X` is flat so that base change applies, `U.ι` is quasi-compact
because `U` is retrocompact, the preimage of `U` in `Spec 𝒪_{X,x}` is an affine open by
`AlgebraicGeometry.isAffineOpen_of_krullDimLE_one` and hence its inclusion is an affine
morphism, and the pullback of `ℱ` to it is again quasi-coherent by [Stacks, Tag 01BG].

No `@[stacks 09N8]` attribute is attached: the tag asserts the conclusion unconditionally. -/
theorem isZero_rightDerived_pushforward_of_isRetrocompact
    (hAff : HigherDirectImageVanishingAffine.{u})
    (hBC : FlatBaseChangeVanishing.{u}) (hStalk : PullbackFromSpecStalkDetectsStalk.{u})
    (X : Scheme.{u}) (U : X.Opens) (hU : IsRetrocompact (U : Set X))
    (h_noetherian : ∀ x : X, IsNoetherianRing (X.presheaf.stalk x))
    (h_dimension : ∀ x : X, Ring.KrullDimLE 1 (X.presheaf.stalk x))
    (F : U.toScheme.Modules) (hF : F.IsQuasicoherent)
    (p : ℕ) (hp : 0 < p) :
    IsZero (((Scheme.Modules.pushforward U.ι).rightDerived p).obj F) := by
  refine isZero_of_forall_isZero_stalk _ fun x ↦ hStalk X x _ ?_
  refine hBC U.ι (X.fromSpecStalk x) (X.fromSpecStalk x ⁻¹ᵁ U).ι (X.fromSpecStalk x ∣_ U)
    (isPullback_morphismRestrict _ U) (flat_fromSpecStalk X x)
    (quasiCompact_iff_isSpectralMap.mpr (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hU))
    inferInstance F hF p ?_
  have := h_noetherian x
  have := h_dimension x
  have : IsAffine (X.fromSpecStalk x ⁻¹ᵁ U).toScheme :=
    isAffineOpen_of_krullDimLE_one (X.presheaf.stalk x) _
  exact hAff _ _ inferInstance (Stacks.Modules.isQuasicoherent_pullback _ F hF) p hp

end Stacks.AlgebraicGeometry.OneDimensionalLocal
