module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Sites.LocalSite
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteProjective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Locally free modules and locally free sheaves on an affine scheme

Throughout, `R` is a commutative ring, `M` an `R`-module, `X = Spec R` the prime
spectrum of `R` with its Zariski topology and structure sheaf `O_X`, and
`F = M~` the quasi-coherent `O_X`-module associated to `M` (the "tilde"
construction `AlgebraicGeometry.tilde`).

Recall the relevant background:

- For `f ∈ R`, the standard open `D(f) = { p ∈ Spec R : f ∉ p }`.  The standard
  opens form a basis of the Zariski topology on `X`.
- `R_f = R[1/f]` denotes the localization of `R` at `{1, f, f^2, ...}`, and
  `M_f = M ⊗_R R_f` the corresponding localization of `M`, an `R_f`-module.
- The structure sheaf satisfies `O_X(D(f)) = R_f`, and the affine scheme
  `(D(f), O_X|_{D(f)})` is isomorphic to `Spec R_f`.  Under this identification
  `F|_{D(f)} = (M_f)~`.

## Locally free `R`-modules

The `R`-module `M` is:
1. *locally free* if there is a family `(f_i)_{i ∈ I}` of elements of `R` with
   `X = ⋃_i D(f_i)` and, for each `i`, `M_{f_i}` is a *free* `R_{f_i}`-module;
2. *finite locally free* if such a covering exists with each `M_{f_i}` a *finite
   free* `R_{f_i}`-module;
3. *finite locally free of rank `r`* if such a covering exists with each
   `M_{f_i} ≅ R_{f_i}^{⊕ r}`.

## Locally free `O_X`-modules

For a ringed space `(X, O_X)` and a sheaf `F` of `O_X`-modules, `F` is:
1. *locally free* if every point `x ∈ X` has an open neighbourhood `U` and an
   index set `I` with `F|_U ≅ ⨁_{i ∈ I} O_X|_U`;
2. *finite locally free* if the index sets `I` may always be chosen finite;
3. *finite locally free of rank `r`* if the index sets may always be chosen of
   cardinality `r`.

## The statements

1. `F = M~` is a locally free `O_X`-module iff `M` is a locally free `R`-module.
2. `F = M~` is a finite locally free `O_X`-module iff `M` is a finite locally
   free `R`-module.

The rank-`r` variant is included as well.
-/

@[expose] public section
-- needed file-scoped: 18 declarations fail without it, e.g. `bridge_N_gamma_carrier_addEquiv`
-- and `bridge_N_gamma_csmul_val`, whose `↑(…)` coercions need `bridgeNGammaTilde` unfolded to
-- `{ f // (StructureSheaf.isLocallyFraction R M).pred f }` at `default` transparency; also
-- `bridge_N_fromTildeΓ_isIso` (`SheafOfModules.pushforward … |>.IsRightAdjoint` synthesis)
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v

/-!
### Locally free `R`-modules

We use `Localization.Away (f i) = R_{f_i}` for the localized ring and
`LocalizedModule (Submonoid.powers (f i)) M = M_{f_i}` for the localized module.
The condition `X = ⋃_i D(f_i)` is, by `PrimeSpectrum.iSup_basicOpen_eq_top_iff`,
equivalent to `Ideal.span (Set.range f) = ⊤`, which we use directly.
-/

/-- `M` is a **locally free** `R`-module: there is a family `f : ι → R` whose
basic opens cover `Spec R` (equivalently, generate the unit ideal) and such that
each localization `M_{f i}` is a free `R_{f i}`-module. -/
@[stacks 00NW "(1)",
  ega "0 5.4.1" "affine case",
  ega "II 6.5.1" "(I)",
  ega "III 7.9.1",
  ega "IV 21.5.3" "special case", sga "3 XV 2.10"]
def Module.IsLocallyFree (R : Type u) [CommRing R] (M : Type u)
    [AddCommGroup M] [Module R M] : Prop :=
  ∃ (ι : Type u) (f : ι → R), Ideal.span (Set.range f) = ⊤ ∧
    ∀ i, Module.Free (Localization.Away (f i))
      (LocalizedModule (Submonoid.powers (f i)) M)

/-- `M` is a **finite locally free** `R`-module: as above, but each localization
`M_{f i}` is in addition finitely generated (hence finite free) over `R_{f i}`. -/
@[stacks 00NW "(2)",
  ega "0 5.4.1" "affine case",
  ega "II 6.5.1" "(I), special case",
  ega "III 7.9.1",
  ega "IV 18.2.7" "partial",
  ega "IV 21.5.3" "special case",
  sga "1 VIII 7.6" "affine module condition",
  sga "6 IV 2.1" "special case"]
def Module.IsFiniteLocallyFree (R : Type u) [CommRing R] (M : Type u)
    [AddCommGroup M] [Module R M] : Prop :=
  ∃ (ι : Type u) (f : ι → R), Ideal.span (Set.range f) = ⊤ ∧
    ∀ i, Module.Free (Localization.Away (f i))
        (LocalizedModule (Submonoid.powers (f i)) M) ∧
      Module.Finite (Localization.Away (f i))
        (LocalizedModule (Submonoid.powers (f i)) M)

/-- A module is finite locally free exactly when it is finite and projective.  This is the
characterisation of `Module.IsFiniteLocallyFree` by the two-out-of-eight clauses of
`Module.finite_projective_tfae`. -/
public theorem Module.isFiniteLocallyFree_iff_finite_projective (R : Type u) [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M] :
    Module.IsFiniteLocallyFree R M ↔ Module.Finite R M ∧ Module.Projective R M := by
  have hset :
      (∃ s : Set R, Ideal.span s = ⊤ ∧
        ∀ f ∈ s, Module.Free (Localization.Away f) (LocalizedModule.Away f M) ∧
          Module.Finite (Localization.Away f) (LocalizedModule.Away f M)) ↔
        Module.IsFiniteLocallyFree R M := by
    unfold Module.IsFiniteLocallyFree
    constructor
    · rintro ⟨s, hs, hfree⟩
      exact ⟨s, Subtype.val, by simpa using hs, fun f => hfree f.1 f.2⟩
    · rintro ⟨ι, f, hs, hfree⟩
      exact ⟨Set.range f, hs, by rintro x ⟨i, rfl⟩; exact hfree i⟩
  rw [← hset]
  exact (Module.finite_projective_tfae R M).out 7 2

/-- `M` is **finite locally free of rank `r`**: there is a covering family
`f : ι → R` of `Spec R` such that each localization `M_{f i}` is free of rank `r`
over `R_{f i}`, i.e. has a basis indexed by `Fin r`. -/
@[stacks 00NW "(3)",
  ega "0 5.4.1" "affine case, rank n",
  ega "II 6.5.1" "(I), special case",
  ega "IV 18.2.7" "partial", sga "4½ Arcata 1.4.2", sga "6 X 6.1" "partial"]
def Module.IsFiniteLocallyFreeOfRank (R : Type u) [CommRing R] (M : Type v)
    [AddCommGroup M] [Module R M] (r : ℕ) : Prop :=
  ∃ (ι : Type u) (f : ι → R), Ideal.span (Set.range f) = ⊤ ∧
    ∀ i, Nonempty (Basis (Fin r) (Localization.Away (f i))
      (LocalizedModule (Submonoid.powers (f i)) M))

/-!
### Sheaf side: locally free `O_X`-modules (Stacks Tag 01C6)

For a scheme `X`, the category `X.Modules` is the category of sheaves of
`O_X`-modules.  For an open `U : X.Opens`, `F.restrict U.ι : U.toScheme.Modules`
is the restriction `F|_U`, and `SheafOfModules.free I` is `⨁_{i ∈ I} O_U` (a free
sheaf of `O_U`-modules).  The local model `F|_U ≅ ⨁_{i ∈ I} O_X|_U` is thus an
isomorphism in `U.toScheme.Modules`.
-/

/-- A sheaf of `O_X`-modules `F` is **locally free** if every point of `X` has an
open neighbourhood `U` and an index set `I` such that `F|_U` is isomorphic to the
free sheaf `⨁_{i ∈ I} O_X|_U`. -/
@[ega "0 5.4.1", ega "III 7.9.1", ega "IV 2.1.12", ega "IV 21.5.3" "partial", sga "1 II 5.7"]
def AlgebraicGeometry.Scheme.Modules.IsLocallyFree {X : Scheme.{u}}
    (F : X.Modules) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (I : Type u),
    Nonempty (F.restrict U.ι ≅ SheafOfModules.free.{u} I)

/-- A sheaf of `O_X`-modules `F` is **finite locally free** if it is locally free
with the index sets always chosen finite. -/
@[ega "0 5.4.1",
  ega "III 4.6.2",
  ega "III 7.9.1",
  ega "IV 21.13.3",
  ega "IV 21.5.3" "partial",
  sga "1 VIII 7.6" "partial",
  sga "3 V 4.2",
  sga "3 VIB 13.5",
  sga "6 II 2.2.1" "objects of Loclib(U)",
  sga "6 IV 2.1" "special case",
  sga "6 VIII 2.4"]
def AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree {X : Scheme.{u}}
    (F : X.Modules) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U) (I : Type u) (_ : Finite I),
    Nonempty (F.restrict U.ι ≅ SheafOfModules.free.{u} I)

/-- A sheaf of `O_X`-modules `F` is **finite locally free of rank `r`** if it is
locally free with the index sets always chosen of cardinality `r`, i.e. one may
take `I = Fin r`. -/
@[ega "0 5.4.1",
  ega "II 6.5.1" "(I), special case",
  ega "IV 21.13.3",
  sga "3 I 4.6.3.1" "partial",
  sga "3 V 4.2",
  sga "3 VIB 13.5",
  sga "6 X 6.1" "partial"]
def AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank {X : Scheme.{u}}
    (F : X.Modules) (r : ℕ) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (_ : x ∈ U),
    Nonempty (F.restrict U.ι ≅ SheafOfModules.free.{u} (ULift (Fin r)))

/-!
## Supporting infrastructure (proof-sketch helper lemmas)

The two `Module.…IsLocallyFree` / `Scheme.Modules.…IsLocallyFree` definitions are
*not* verbatim equal : the algebra side covers by **standard**
opens `D(f_i)` with `M_{f_i}` free, while the sheaf side allows **arbitrary** open
neighbourhoods.  Bridging them factors through two reusable lemmas:

* `tilde_restrict_basicOpen_free_iff` — on a standard open `D(f)`, the restricted
  sheaf `(M~)|_{D(f)}` is free **iff** the localized module `M_f` is free over
  `R_f`.  This is the genuine algebraic-geometry content and is the analytic
  kernel of the whole lemma.
* `isLocallyFree_iff_basicOpen` — sheaf-side local freeness on arbitrary opens is
  equivalent to local freeness witnessed on **standard** opens (basis shrinking).

Statement 1 then follows by pure covering combinatorics (`iSup_basicOpen_eq_top_iff`),
and Statements 2/3 reuse the same helpers with finiteness / rank bookkeeping.

Statement 1 (`tilde_isLocallyFree_iff`) was checked for
counterexamples (R = 0 vacuous on both sides; universe constraints `I = ι : Type u`
are symmetric — `Module.Free` of a `Type u` module has a `Type u` basis index;
arbitrary-open vs standard-open handled by the basis). No counterexample found; the
formalization faithfully encodes Stacks Tag 05JM.
-/

/-- `D(f)` as a `Scheme.Opens` of `Spec R` (the bare `PrimeSpectrum.basicOpen f`
elaborates to `Opens (PrimeSpectrum R)`, losing the scheme structure needed for
`.ι`, so we package it here). -/
@[sga "4 XIV 4.3"]
noncomputable def specBasicOpen (R : Type u) [CommRing R] (f : R) :
    (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen f

/- **Helper 1 (the affine/localization kernel) — the affine kernel, retained
for reference.** On the standard open `D(f)`,
the restriction `(M~)|_{D(f)}` of the tilde sheaf is isomorphic to a free sheaf
`⨁_I O` (for some index set `I`) **iff** the localization `M_f` is a free
`R_f`-module.

INFORMAL PROOF (rigorous; this is Stacks Tag 05JM's actual content on one chart):

The open subscheme `(D(f), O_X|_{D(f)})` is isomorphic, as a scheme, to
`Spec R_f` via `AlgebraicGeometry.basicOpenIsoSpecAway f :
(PrimeSpectrum.basicOpen f).toScheme ≅ Spec (Localization.Away f)`.  Transporting
along this isomorphism, the restricted sheaf `(M~)|_{D(f)}` corresponds to the
tilde sheaf `(M_f)~` on `Spec R_f`.  Concretely: sections of `M~` over `D(f)` are
the localized module `M_f` (the instance
`IsLocalizedModule.Away f (tilde.toOpen M (basicOpen f)).hom`, equivalently
`AlgebraicGeometry.isLocalizing_tilde`), and these glue/restrict to give an
isomorphism of `O_{Spec R_f}`-modules `(M~)|_{D(f)} ≅ (M_f)~`.

Now apply the tilde dictionary over the ring `R_f`:
* `tilde.functor R_f : ModuleCat R_f ⥤ (Spec R_f).Modules` is **fully faithful**
  (`AlgebraicGeometry.tilde.fullyFaithfulFunctor`), and additive, hence preserves
  and *reflects* isomorphisms and direct sums.
* It sends the free module `(I →₀ R_f)` to the free sheaf `⨁_I O`
  (`AlgebraicGeometry.tildeFinsupp I : tilde (ModuleCat.of R_f (I →₀ R_f)) ≅
  SheafOfModules.free I`).

(⇐)  If `M_f` is free over `R_f`, pick a basis indexed by some `I : Type u`
  (`Module.Free` gives `M_f ≅ (I →₀ R_f)` as `R_f`-modules; the index type lives in
  `Type u` because `M_f : Type u`).  Apply `tilde.functor` to that linear iso and
  compose with `tildeFinsupp I` to get `(M_f)~ ≅ ⨁_I O`, then transport back along
  `basicOpenIsoSpecAway` to `(M~)|_{D(f)} ≅ ⨁_I O`.

(⇒)  Conversely, given `(M~)|_{D(f)} ≅ ⨁_I O`, transport to `(M_f)~ ≅ ⨁_I O ≅
  (I →₀ R_f)~` (using `tildeFinsupp I` backwards).  Because `tilde.functor R_f` is
  fully faithful it reflects this isomorphism: there is an `R_f`-linear iso
  `M_f ≅ (I →₀ R_f)`, so `M_f` is free (`Module.Free.of_basis` on the transported
  basis).

build `(M~)|_{D(f)} ≅ (M_f)~` once as a named
lemma (using `basicOpenIsoSpecAway`, `restrictFunctorIsoPullback`/`restrictAppIso`,
and the `IsLocalizedModule.Away` section identification), then transfer freeness
through `tilde.fullyFaithfulFunctor` and `tildeFinsupp`. -/
/-- A tilde sheaf is isomorphic to `free J` iff the module has a basis indexed by `J`. -/
private theorem tilde_iso_free_iff_nonempty_basis
    (Rf : Type u) [CommRing Rf] (Mf : Type u) [AddCommGroup Mf] [Module Rf Mf]
    (J : Type u) :
    Nonempty
        (AlgebraicGeometry.tilde (R := CommRingCat.of Rf) (ModuleCat.of Rf Mf) ≅
          SheafOfModules.free.{u} J) ↔
      Nonempty (Module.Basis J Rf Mf) := by
  constructor
  · rintro ⟨ψ⟩
    have ψ2 : (AlgebraicGeometry.tilde.functor (CommRingCat.of Rf)).obj (ModuleCat.of Rf Mf) ≅
        (AlgebraicGeometry.tilde.functor (CommRingCat.of Rf)).obj
          (ModuleCat.of Rf (J →₀ Rf)) := by
      refine ?_ ≪≫ (AlgebraicGeometry.tildeFinsupp (R := CommRingCat.of Rf) J).symm
      simpa [AlgebraicGeometry.tilde.functor_obj] using ψ
    have lin : ModuleCat.of Rf Mf ≅ ModuleCat.of Rf (J →₀ Rf) :=
      (AlgebraicGeometry.tilde.fullyFaithfulFunctor (R := CommRingCat.of Rf)).preimageIso ψ2
    exact ⟨(Finsupp.basisSingleOne (R := Rf) (ι := J)).map lin.symm.toLinearEquiv⟩
  · rintro ⟨b⟩
    have lin : ModuleCat.of Rf Mf ≅ ModuleCat.of Rf (J →₀ Rf) := b.repr.toModuleIso
    refine ⟨?_ ≪≫ AlgebraicGeometry.tildeFinsupp (R := CommRingCat.of Rf) J⟩
    simpa [AlgebraicGeometry.tilde.functor_obj] using
      (AlgebraicGeometry.tilde.functor (CommRingCat.of Rf)).mapIso lin

/-- **Pure-algebra wrapper.** Over any ring `Rf` and module `Mf`,
the tilde sheaf `(Mf)~` on `Spec Rf` is isomorphic to some free sheaf `⨁_I O`
**iff** `Mf` is a free `Rf`-module. This is the tilde-dictionary half of the kernel:
`tilde.functor` is fully faithful (`tilde.fullyFaithfulFunctor`) and sends
`(I →₀ Rf)` to `SheafOfModules.free I` (`tildeFinsupp`). No scheme transport is
involved, so it needs no `basicOpenIsoSpecAway`. -/
theorem tilde_free_iff_module_free
    (Rf : Type u) [CommRing Rf] (Mf : Type u) [AddCommGroup Mf] [Module Rf Mf] :
    (∃ I : Type u, Nonempty
        (AlgebraicGeometry.tilde (R := CommRingCat.of Rf) (ModuleCat.of Rf Mf) ≅
          SheafOfModules.free.{u} I)) ↔ Module.Free Rf Mf := by
  rw [Module.free_def]
  exact exists_congr (tilde_iso_free_iff_nonempty_basis Rf Mf)

/- **The geometric bridge, the algebraic-geometry content of the argument.**
Sheaf-side freeness of the restricted tilde sheaf `(M~)|_{D(f)}` on the standard open
`D(f)` is equivalent to freeness of the tilde sheaf `(M_f)~` over `Spec R_f`.

This absorbs the scheme isomorphism `D(f) ≅ Spec R_f` (`basicOpenIsoSpecAway f`):
under it the restricted sheaf `(M~)|_{D(f)}` corresponds to `(M_f)~`, and the
restriction functor sends a free sheaf `⨁_I O` on one chart to the free sheaf with
the SAME index `I` on the other (so the existential over `I` is preserved). Stated as
an iff of two existentials so the transport is symmetric and no functor inversion is
needed downstream.

build the iso
`(restrictFunctor (basicOpenIsoSpecAway f).inv).obj ((M~)|_{D(f)}) ≅ (M_f)~` over
`Spec R_f` (using `IsLocalizedModule.Away f (tilde.toOpen M (basicOpen f)).hom` to
identify sections with `M_f`, plus `restrictFunctorIsoPullback` to relate
`restrictFunctor`/`pullback`), together with the free-sheaf comparison
`(restrictFunctor (basicOpenIsoSpecAway f).inv).obj (free I) ≅ free I`
(`SheafOfModules.pullbackObjFreeIso` + `restrictFunctorIsoPullback`). Then both
directions of the iff transport an iso to a free sheaf across the (invertible)
restriction functor and re-index. This is the hard QCoh kernel of Stacks Tag 05JM.

Both sides are a clean symmetric transport
along `D(f) ≅ Spec R_f` (`basicOpenIsoSpecAway`), preserving `free I` with the SAME
index `I` (no IBN/rank-uniqueness needed). All degenerate cases (f nilpotent / R = 0 /
M = 0) make both sides TRUE simultaneously; no vacuous-satisfiability asymmetry.

(Decomposed into the sub-lemmas below).
Hybrid Route C + Route A: build the *equivalence of module categories* induced by the
scheme iso `e := basicOpenIsoSpecAway f` (Sub-lemma `bridge_specAwayEquiv`), which moves
the index `I` faithfully via `free ↦ free` (`bridge_restrict_free_iso`); pin down the
image of `(M~)|_{D(f)}` as `(M_f)~` via `fromTildeΓ` essential-image (`bridge_N_iso`);
then transport the existential `∃ I, _ ≅ free I` across the equivalence
(`exists_free_iso_of_equiv`). -/

/-- Restriction of sheaves of modules along the scheme isomorphism
`e := basicOpenIsoSpecAway f : D(f) ≅ Spec R_f` is an equivalence of categories
`D(f).Modules ≌ (Spec R_f).Modules`, with functor `restrictFunctor e.hom` and inverse
`restrictFunctor e.inv`.

Indeed `Scheme.Modules.restrictFunctorIsoPullback` gives `restrictFunctor g ≅ pullback g`
naturally, and pullback is pseudofunctorial, so along the iso `e` the two composites are
isomorphic to the identities. -/
noncomputable def bridge_specAwayEquiv
    (R : Type u) [CommRing R] (f : R) :
    (specBasicOpen R f).toScheme.Modules ≌
      (Spec (CommRingCat.of (Localization.Away f))).Modules := by
  unfold specBasicOpen
  letI e := AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f
  haveI : AlgebraicGeometry.IsOpenImmersion e.hom := AlgebraicGeometry.IsOpenImmersion.of_isIso
      e.hom
  haveI : AlgebraicGeometry.IsOpenImmersion e.inv := AlgebraicGeometry.IsOpenImmersion.of_isIso
      e.inv
  exact CategoryTheory.Equivalence.mk
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor e.inv)
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor e.hom)
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorId.symm ≪≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr e.hom_inv_id.symm) ≪≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctorComp e.hom e.inv))
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorComp e.inv e.hom).symm ≪≫
        (AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr e.inv_hom_id) ≪≫
        AlgebraicGeometry.Scheme.Modules.restrictFunctorId)

/-- **Bridge Sub-lemma 2 (`bridge_restrict_free_iso`).** The equivalence
`bridge_specAwayEquiv` sends the free sheaf `free I` to `free I` (same index `I`), in
both directions. We state the functor direction; the inverse direction is symmetric.

PROOF: `restrictFunctor g ≅ pullback g` (`restrictFunctorIsoPullback`) then
`SheafOfModules.pullbackObjFreeIso g I : (pullback g).obj (free I) ≅ free I`. -/
noncomputable def bridge_restrict_free_iso
    (R : Type u) [CommRing R] (f : R) (I : Type u) :
    (bridge_specAwayEquiv R f).functor.obj (SheafOfModules.free.{u} I) ≅
      SheafOfModules.free.{u} I := by
  letI e := AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f
  haveI : AlgebraicGeometry.IsOpenImmersion e.inv := AlgebraicGeometry.IsOpenImmersion.of_isIso
      e.inv
  haveI hfin : (Opens.map e.inv.base).Final := by
    have h : Opens.map e.inv.base = (Opens.mapMapIso (asIso e.inv.base)).functor := rfl
    rw [h]; infer_instance
  exact (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback e.inv).app
      (SheafOfModules.free.{u} I) ≪≫
    SheafOfModules.pullbackObjFreeIso (AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom e.inv) I

/-- **Bridge Sub-lemma 2' (inverse direction).** The inverse functor of
`bridge_specAwayEquiv` also sends `free I` to `free I`. -/
noncomputable def bridge_restrict_free_iso_inv
    (R : Type u) [CommRing R] (f : R) (I : Type u) :
    (bridge_specAwayEquiv R f).inverse.obj (SheafOfModules.free.{u} I) ≅
      SheafOfModules.free.{u} I := by
  letI e := AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f
  haveI : AlgebraicGeometry.IsOpenImmersion e.hom := AlgebraicGeometry.IsOpenImmersion.of_isIso
      e.hom
  haveI hfin : (Opens.map e.hom.base).Final := by
    have h : Opens.map e.hom.base = (Opens.mapMapIso (asIso e.hom.base)).functor := rfl
    rw [h]; infer_instance
  exact (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback e.hom).app
      (SheafOfModules.free.{u} I) ≪≫
    SheafOfModules.pullbackObjFreeIso (AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom e.hom) I

/- **Bridge Sub-lemma 3 (`bridge_N_iso`).** The equivalence `bridge_specAwayEquiv`
sends the restricted tilde sheaf `(M~)|_{D(f)}` to the tilde sheaf `(M_f)~` on `Spec R_f`.

PROOF (Route A, the heart): let `N := Φ.functor.obj ((M~)|_{D(f)})`. Its global sections
are `M_f` (via `restrict_obj` + `i ''ᵁ ⊤ = basicOpen f` + the instance
`IsLocalizedModule (powers f) (tilde.toOpen M (basicOpen f)).hom` and
`IsLocalizedModule.linearEquiv`); and `N` is in the essential image of `tilde.functor R_f`
(`isIso_fromTildeΓ_iff` / `isIso_fromTildeΓ_of_presentation` with a presentation
transported across the equivalence from the tautological presentation of `tilde M`).
Hence `N ≅ tilde (Γ N) ≅ (M_f)~`.

It is decomposed into two standalone sub-lemmas, `bridge_N_fromTildeΓ_isIso` and
`bridge_N_gammaIso`, which `bridge_N_iso` then assembles. -/
/-- **Sub-lemma A for `bridge_N_iso` (essential image / `fromTildeΓ` is iso).**
`N := Φ.functor.obj ((M~)|_{D(f)})` lies in the essential image of `tilde.functor R_f`,
witnessed by `IsIso N.fromTildeΓ`. By `AlgebraicGeometry.isIso_fromTildeΓ_of_presentation`
this follows from a `Presentation` of `N`, obtained by transporting the tautological free
presentation of `tilde M` (`AlgebraicGeometry.presentationTilde`) across the equivalence
`Φ = bridge_specAwayEquiv` (an equivalence preserves the cokernel-of-free colimit, and
`Φ.functor` sends `free I ↦ free I` by `bridge_restrict_free_iso`), then applying
`SheafOfModules.presentationOfIsCokernelFree`. (Stacks Tag 05JM, QCoh kernel.) -/
theorem bridge_N_fromTildeΓ_isIso
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    IsIso (@AlgebraicGeometry.Scheme.Modules.fromTildeΓ (CommRingCat.of (Localization.Away f))
      ((bridge_specAwayEquiv R f).functor.obj
        ((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
          (specBasicOpen R f).ι))) := by
  let e := AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f
  have : AlgebraicGeometry.IsOpenImmersion e.inv := AlgebraicGeometry.IsOpenImmersion.of_isIso
      e.inv
  -- finality of the relevant `Opens.map` functors (needed for the unit/free pullback isos)
  have hfinι : (Opens.map (specBasicOpen R f).ι.base).Final := by
    have : (Opens.map (specBasicOpen R f).ι.base).IsRightAdjoint :=
      ⟨_, ⟨(specBasicOpen R f).ι.isOpenEmbedding.isOpenMap.adjunction⟩⟩
    exact Functor.final_of_isRightAdjoint _
  have hfinE : (Opens.map e.inv.base).Final := by
    have h : Opens.map e.inv.base = (Opens.mapMapIso (asIso e.inv.base)).functor := rfl
    rw [h]; infer_instance
  have hisoι : IsIso (SheafOfModules.pullbackObjUnitToUnit
      (AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom (specBasicOpen R f).ι)) := inferInstance
  have hisoE : IsIso (SheafOfModules.pullbackObjUnitToUnit
      (AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom e.inv)) := inferInstance
  -- the composite functor `F : (Spec R).Modules ⥤ (Spec R_f).Modules`, with `F.obj (M~) = N`
  set F := AlgebraicGeometry.Scheme.Modules.restrictFunctor (specBasicOpen R f).ι ⋙
    (bridge_specAwayEquiv R f).functor with hF
  have hpres : Limits.PreservesColimitsOfSize.{u, u, u, u, u+1, u+1} F := by
    rw [hF]; infer_instance
  -- `F` sends the structure sheaf to the structure sheaf: `η : F.obj (unit) ≅ unit`
  have unitInner : (AlgebraicGeometry.Scheme.Modules.restrictFunctor (specBasicOpen R f).ι).obj
      (SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) ≅
      SheafOfModules.unit (specBasicOpen R f).toScheme.ringCatSheaf :=
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback (specBasicOpen R f).ι).app
        (SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) ≪≫
      asIso (SheafOfModules.pullbackObjUnitToUnit
        (AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom (specBasicOpen R f).ι))
  have unitOuter : (bridge_specAwayEquiv R f).functor.obj
      (SheafOfModules.unit (specBasicOpen R f).toScheme.ringCatSheaf) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (Localization.Away f))).ringCatSheaf :=
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback e.inv).app
        (SheafOfModules.unit (specBasicOpen R f).toScheme.ringCatSheaf) ≪≫
      asIso (SheafOfModules.pullbackObjUnitToUnit
        (AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom e.inv))
  have η : F.obj (SheafOfModules.unit (Spec (CommRingCat.of R)).ringCatSheaf) ≅
      SheafOfModules.unit (Spec (CommRingCat.of (Localization.Away f))).ringCatSheaf :=
    (bridge_specAwayEquiv R f).functor.mapIso unitInner ≪≫ unitOuter
  -- tautological free presentation of `M~` (generators = all of `M`, relations = the kernel)
  set s : Set (ModuleCat.of R M) := Set.univ with hs
  have P : (AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).Presentation :=
    AlgebraicGeometry.presentationTilde (R := CommRingCat.of R) (ModuleCat.of R M)
      s (by simp [hs])
      (SetLike.coe (Finsupp.linearCombination (CommRingCat.of R)
        (Subtype.val : s → (ModuleCat.of R M))).ker)
      (by rw [Submodule.span_coe_eq_restrictScalars]; simp)
  -- transport the presentation across the colimit-preserving `F` to a presentation of `N`
  have PN : (F.obj (AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R
      M))).Presentation :=
    P.map F η.symm
  exact AlgebraicGeometry.isIso_fromTildeΓ_of_presentation _ PN

/- **Sub-lemma B for `bridge_N_iso` (Γ-sections identification) — DECOMPOSED.**
The global sections of `N := Φ.functor.obj ((M~)|_{D(f)})` are the localized module `M_f`,
as an `R_f`-module. Concretely `Γ(N, ⊤) = Γ(M~, D(f))` (by `Scheme.Modules.restrict_obj`
twice, using `e.inv ''ᵁ ⊤ = ⊤` and `(D(f)).ι ''ᵁ ⊤ = D(f)`), and the canonical map
`tilde.toOpen M (basicOpen f)` exhibits `Γ(M~, D(f))` as a localization of `M` at
`Submonoid.powers f` (instance
`AlgebraicGeometry.tilde.instIsLocalizedModule…toOpen`); combined with
`LocalizedModule.mkLinearMap` via `IsLocalizedModule.linearEquiv`, this gives the
`R_f`-linear iso `Γ(N, ⊤) ≅ M_f`.

INFORMAL PROOF reference (rigorous, fresh perspective, STATUS: solved):
Three stages:
  (1) carrier identity `Γ(N,⊤) = Γ(M~, D(f))` as `Ab` (restrict_obj ×2);
  (2) the carrier identity is `R`-linear (scalar compatibility — the genuine hard
      obligation: the `R_f`-action on `Γ(N,⊤)`, restricted along `R → R_f`, equals the
      standard `R`-action on `Γ(M~, D(f))`), and transport `IsLocalizedModule` of
      `tilde.toOpen` through it (`IsLocalizedModule.of_linearEquiv_right`);
  (3) compare to `M_f` via `IsLocalizedModule.linearEquiv` (R-linear equiv) and upgrade to
      `R_f`-linear via `LinearEquiv.extendScalarsOfIsLocalization` (needs `IsScalarTower`),
      then `LinearEquiv.toModuleIso`.

This decomposes into two sub-lemmas plus their assembly:
  • `bridge_N_gamma_scalarTower` (instance) — `IsScalarTower R (Localization.Away f) (Γ(N,⊤))`:
    the `R`-action on the global sections factors through `R → R_f`. Holds because the
    `R_f`-module structure on `modulesSpecToSheaf.obj N` is by sections of the structure
    sheaf and the `R`-action is its restriction along the algebra map.
  • `bridge_N_gamma_Requiv` (DATA) — the `R`-linear equivalence `Γ(N,⊤) ≃ₗ[R] M_f`
    (Stages 1+2+3-localization): carrier identity + `IsLocalizedModule` transport +
    `IsLocalizedModule.linearEquiv` against `LocalizedModule.mkLinearMap`.
  The assembly `bridge_N_gammaIso` below is then:
    `(LinearEquiv.extendScalarsOfIsLocalization (powers f) (Localization.Away f)
        (bridge_N_gamma_Requiv …)).toModuleIso`. -/

/-- Abbreviation for the global sections `Γ(N, ⊤)` of `N := Φ.functor.obj ((M~)|_{D(f)})`,
as an `R_f = Localization.Away f`-module (an object of `ModuleCat (Localization.Away f)`). -/
noncomputable abbrev bridgeNGamma
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    ModuleCat (Localization.Away f) :=
  (modulesSpecToSheaf.obj ((bridge_specAwayEquiv R f).functor.obj
      ((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
        (specBasicOpen R f).ι))).presheaf.obj (Opposite.op ⊤)

/-- The global sections `Γ(M~, D(f))` of the tilde sheaf over the standard open `D(f)`,
as an `R`-module (an object of `ModuleCat R`).  We use the `StructureSheaf`-in-`Type`
presentation `(structureSheafInType R M).obj.obj (op (basicOpen f))` (carrier-defeq to the
`ModuleCat`-valued `(modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op (basicOpen f))`,
i.e. the codomain of `tilde.toOpen`), because the localization map
`StructureSheaf.toOpenₗ R M (basicOpen f) : M →ₗ[R] …` into it carries the
`IsLocalizedModule (Submonoid.powers f)` instance directly. -/
noncomputable abbrev bridgeNGammaTilde
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    ModuleCat R :=
  ModuleCat.of R
    ((AlgebraicGeometry.structureSheafInType R M).obj.obj (Opposite.op (PrimeSpectrum.basicOpen f)))

/-- **Sub-lemma B.carrier.addEquiv (Stage 1 — carrier identity).** The underlying additive
groups of `Γ(N, ⊤)` and `Γ(M~, D(f))` are canonically identified.  Concretely
`N := Φ.functor.obj ((M~)|_{D(f)})` is `((M~).restrict (D(f)).ι).restrict e.inv` with
`e := basicOpenIsoSpecAway f`, so two applications of `Scheme.Modules.restrict_obj`
(`Γ(M.restrict g, U) = Γ(M, g ''ᵁ U)`, an `Ab`-level equality), together with
`e.inv ''ᵁ ⊤ = ⊤` (`e` an iso) and `(specBasicOpen R f).ι ''ᵁ ⊤ = basicOpen f`
(`Scheme.Opens.ι_image_top`), identify the carriers.  This is the EASY (additive) half of
the carrier identity; the genuine hard content (scalar compatibility) is isolated in
`bridge_N_gamma_smul_compat`. -/
noncomputable def bridge_N_gamma_carrier_addEquiv
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    bridgeNGamma R M f ≃+ bridgeNGammaTilde R M f := by
  letI e := AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f
  letI U : (Spec (CommRingCat.of R)).Opens := specBasicOpen R f
  letI Mt := AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)
  have h1 := AlgebraicGeometry.Scheme.Modules.restrict_obj (Mt.restrict U.ι) e.inv ⊤
  have h2 := AlgebraicGeometry.Scheme.Modules.restrict_obj Mt U.ι (e.inv ''ᵁ ⊤)
  have hi : e.inv ''ᵁ (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens) = ⊤ := by
    rw [AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange,
        AlgebraicGeometry.Scheme.Hom.opensRange_of_isIso]
  have hu : U.ι ''ᵁ (⊤ : U.toScheme.Opens) = U := AlgebraicGeometry.Scheme.Opens.ι_image_top U
  have keyAb : Γ((Mt.restrict U.ι).restrict e.inv,
      (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens)) = Γ(Mt, U) := by
    rw [h1, h2, hi, hu]
  exact (eqToIso keyAb).addCommGroupIsoToAddEquiv

/-- **Sub-lemma B.carrier.smul_pointwise.germ (Part 3 — the algebraic germ kernel).**
The genuinely-algebraic content of `bridge_N_gamma_smul_pointwise`, isolated from the
geometric transport .  At a prime `p`, on the stalk module
`StructureSheaf.Localizations M p` (`= M_p`), the `R_p`-scalar `algebraMap R R_p r` acts
exactly as the native `R`-scalar `r`.

This is the clean reduction target of the germ-by-germ comparison: in
`bridge_N_gamma_smul_pointwise`, the `R_f`-sheaf action contributes, at `p`, the germ
`algebraMap R R_p r` of the transported global section `toOpen R (D(f)) r` (Part 3a/3b), and
this lemma discharges the final `algebraMap R R_p r •_{M_p} m = r •_{M_p} m`
(Part 3c) via the localization scalar tower `IsScalarTower R R_p M_p` (`algebraMap_smul`). -/
theorem bridge_N_gamma_germ_scalar
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
    (p : PrimeSpectrum R) (r : R) (m : StructureSheaf.Localizations M p) :
    (algebraMap R (StructureSheaf.Localizations R p) r) • m = r • m := by
  rw [algebraMap_smul]

/-- **Sub-lemma B.carrier.smul_pointwise.lhs (the irreducible geometric-transport atom).**
The genuine `modulesSpecToSheaf`/equivalence-transport content of `bridge_N_gamma_smul_pointwise`,
with the final germ-scalar reduction (Part 3c) already factored out into
`bridge_N_gamma_germ_scalar`.  At a prime `p ∈ D(f)`, the value of the transported section
`φ ((algebraMap R R_f r) • x)` (the `R_f`-sheaf action on `Γ(N,⊤)` via
`modulesSpecToSheaf = … ⋙ sheafCompose (restrictScalars (globalSectionsIso R_f).hom)`) equals
the germ scalar `algebraMap R R_p r` acting on the value of `φ x` in the stalk `M_p`.

This isolates **Parts 1 + 2 + 3a/3b**: (Part 1) the carrier transport `φ`
(= `keyAb ▸ ·`, `keyAb` two `Scheme.Modules.restrict_obj` carrier-`rfl` equalities + the open
re-indexings) does not change the underlying section data up to the point re-indexing; (Part 2)
the `R_f`-sheaf action is pointwise on stalks (`structureSheafInType.smul_apply`); (Part 3a/3b)
transported along `e = basicOpenIsoSpecAway f`, the global section
`(globalSectionsIso R_f).hom (algebraMap R R_f r) = toOpen R_f ⊤ (algebraMap r)` becomes
`toOpen R (D(f)) r`, whose germ at `p` is `algebraMap R R_p r`
(`StructureSheaf.toOpen_germ`/`algebraMap_germ` + `IsAffineOpen.isLocalization_basicOpen`).
The final `algebraMap R R_p r •_{M_p} m = r •_{M_p} m` is the `bridge_N_gamma_germ_scalar`.
-/
theorem bridge_N_gamma_germ_toStalk
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (r : R) (p : PrimeSpectrum R) (hp : p ∈ PrimeSpectrum.basicOpen f) :
    (CategoryTheory.ConcreteCategory.hom
        ((AlgebraicGeometry.structurePresheafInCommRingCat R).germ
          (PrimeSpectrum.basicOpen f) p hp))
      ((algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj
        (Opposite.op (PrimeSpectrum.basicOpen f)))) r)
      = (CategoryTheory.ConcreteCategory.hom (AlgebraicGeometry.StructureSheaf.toStalk R p)) r :=
  StructureSheaf.algebraMap_germ_apply (PrimeSpectrum.basicOpen f) p hp r

/-- **O-linear transport (Part 2 — the verified `app_smul` lever).**
The `Scheme.Modules` morphism `N ⟶ (M~).restrict (e.inv ≫ U.ι)` over `Spec R_f`, obtained as the
INVERSE of the `restrictFunctorComp` natural-iso component
`(restrictFunctorComp e.inv U.ι).app Mt : (M~).restrict (e.inv ≫ U.ι) ≅ N`
(recall `N = ((M~).restrict U.ι).restrict e.inv` by `rfl`).  Being a genuine `Scheme.Modules.Hom`
(NOT a raw `AddEquiv`), its components carry `Scheme.Modules.Hom.app_smul`, so the inner
`Γ(Spec R_f, 𝒪)`-section action pushes through — see `actionTransport_app_smul`.  This is the
O-module rebuild of the carrier transport, which is the only viable
route but never realized; it is the missing Part-2 lever for `bridge_N_gamma_action_section`. -/
noncomputable def actionTransport
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    ((bridge_specAwayEquiv R f).functor.obj
      ((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
        (specBasicOpen R f).ι))
      ⟶ ((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
          ((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv
            ≫ (specBasicOpen R f).ι)) := by
  letI e := AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f
  haveI : AlgebraicGeometry.IsOpenImmersion e.inv := AlgebraicGeometry.IsOpenImmersion.of_isIso
      e.inv
  letI U : (Spec (CommRingCat.of R)).Opens := specBasicOpen R f
  letI Mt := AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)
  exact ((AlgebraicGeometry.Scheme.Modules.restrictFunctorComp e.inv U.ι).app Mt).inv

/-- **`actionTransport` commutes with the `Γ(Spec R_f, 𝒪)`-section action.**
The R_f-section action on `Γ(N, ⊤)` (the genuine `modulesSpecToSheaf` inner action —
Part 2) is intertwined by `actionTransport.app ⊤` with the section action on
`Γ((M~).restrict (e.inv ≫ U.ι), ⊤)`, whose carrier is propositionally `Γ(M~, D(f)) =
bridgeNGammaTilde`.
This is `Scheme.Modules.Hom.app_smul` applied to `actionTransport`.  THE verified lever for pushing
the inner action through the carrier transport (replacing the raw-`AddEquiv` `φ` dead-end). -/
theorem actionTransport_app_smul
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (c : Γ((Spec (CommRingCat.of (Localization.Away f))),
            (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens)))
    (z : Γ(((bridge_specAwayEquiv R f).functor.obj
      ((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
        (specBasicOpen R f).ι)),
            (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens))) :
    (actionTransport R M f).app (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens) (c • z)
      = c • (actionTransport R M f).app (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens) z
          :=
  (actionTransport R M f).app_smul c z

/-- `actionTransport.app ⊤` is a presheaf reindex map:
`actionTransport.app ⊤ = Mt.presheaf.map (eqToHom (comp_image …)).op`, a genuine
`Scheme.Modules` presheaf restriction map, by `restrictFunctorComp_inv_app_app` — the
restrict-iso component is `presheaf.map (eqToHom).op`.  This is what makes
`Scheme.Modules.map_smul` and `app_smul` applicable to the carrier transport, and reduces the
`action_section` linchpin to `eqToHom`-cast algebra: `eqToHom_op` and `eqToHom_map` collapse
`(eqToHom h).op` and `presheaf.map (eqToHom)` to `eqToHom`, which then matches
`φ = (eqToIso keyAb).addCommGroupIsoToAddEquiv = eqToHom keyAb`. -/
theorem actionTransport_app_eq
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    letI e := AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f
    letI U : (Spec (CommRingCat.of R)).Opens := specBasicOpen R f
    letI Mt := AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)
    (actionTransport R M f).app (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens)
      = Mt.presheaf.map (eqToHom (show (e.inv ≫ U.ι) ''ᵁ
            (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens)
            = U.ι ''ᵁ e.inv ''ᵁ ⊤
              from AlgebraicGeometry.Scheme.Hom.comp_image e.inv U.ι ⊤)).op := by
  let e := AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f
  let U : (Spec (CommRingCat.of R)).Opens := specBasicOpen R f
  let Mt := AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)
  have e1 : ((AlgebraicGeometry.Scheme.Modules.restrictFunctorComp e.inv U.ι).app Mt).inv
      = (AlgebraicGeometry.Scheme.Modules.restrictFunctorComp e.inv U.ι).inv.app Mt := rfl
  show AlgebraicGeometry.Scheme.Modules.Hom.app
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctorComp e.inv U.ι).app Mt).inv ⊤ = _
  rw [e1, AlgebraicGeometry.Scheme.Modules.restrictFunctorComp_inv_app_app]

/-- The value of the transported section `actionTransport.app ⊤ z` at the point `⟨↑p, mem⟩` of
the composite open `(e.inv ≫ U.ι) ''ᵁ ⊤` equals `z.val` at the point obtained from the
`eqToHom` open-equality inclusion.  This is `actionTransport_app_eq`, rewriting the morphism to
the structure-sheaf presheaf reindex map `Mt.presheaf.map (eqToHom).op`, followed by
`StructureSheaf.res_apply`: a restriction map acts on `.val` by precomposing the point with the
open inclusion. -/
theorem bridge_N_gamma_actionTransport_val
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (z : bridgeNGamma R M f)
    (p : (Opposite.unop (Opposite.op (PrimeSpectrum.basicOpen f))))
    (mem : (p : PrimeSpectrum R) ∈
      ((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv
          ≫ (specBasicOpen R f).ι) ''ᵁ
        (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens)) :
    ((actionTransport R M f).app (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens) z).val
        ⟨(p : PrimeSpectrum R), mem⟩
      = z.val (((eqToHom (AlgebraicGeometry.Scheme.Hom.comp_image
            (AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv
            (specBasicOpen R f).ι ⊤)))
            ⟨(p : PrimeSpectrum R), mem⟩) := by
  rw [actionTransport_app_eq R M f]
  exact AlgebraicGeometry.StructureSheaf.res_apply _ _ _ z _

/-- The carrier transport `φ` is a pure cast.  The addEquiv
`bridge_N_gamma_carrier_addEquiv` is `(eqToIso keyAb).addCommGroupIsoToAddEquiv` for the
`AddCommGrpCat` carrier equality `keyAb`, so applied to any `z` it is an `eqToHom` cast:
`φ z ≍ z`, a heterogeneous equality of the underlying section data.  This follows from
`(eqToIso h).addCommGroupIsoToAddEquiv w ≍ w`. -/
theorem bridge_N_gamma_phi_heq
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (z : bridgeNGamma R M f) :
    (bridge_N_gamma_carrier_addEquiv R M f z : bridgeNGammaTilde R M f) ≍ z := by
  have key : ∀ (A B : AddCommGrpCat.{u}) (h : A = B) (w : (A : Type u)),
      ((CategoryTheory.eqToIso h).addCommGroupIsoToAddEquiv) w ≍ w := by
    intro A B h w; subst h; rfl
  simp only [bridge_N_gamma_carrier_addEquiv]
  apply key

/-- The `actionTransport.app ⊤` transport is a pure cast.  By `actionTransport_app_eq`,
`actionTransport.app ⊤ = Mt.presheaf.map (eqToHom …).op`, and the `presheaf.map` of an
`eqToHom` is itself an `eqToHom` by `eqToHom_op` and `eqToHom_map`, so applied to any `z` it is
a cast: `actionTransport.app ⊤ z ≍ z`. -/
theorem bridge_N_gamma_at_heq
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (z : bridgeNGamma R M f) :
    ((actionTransport R M f).app (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens) z)
      ≍ z := by
  rw [actionTransport_app_eq R M f]
  have key : ∀ (A B : AddCommGrpCat.{u}) (h : A = B) (w : (A : Type u)),
      (CategoryTheory.eqToHom h) w ≍ w := by
    intro A B h w; subst h; simp
  rw [eqToHom_op, eqToHom_map]
  apply key

universe w

/-- Heterogeneous function application: from a domain equality, a codomain-family `HEq`, a
function `HEq` and an argument `HEq`, the applications are `HEq`.  Used to push `.val` through
the carrier-transport `HEq` `φ z ≍ actionTransport.app ⊤ z` at the point level. -/
private theorem bridge_N_gamma_heq_funapp {α α' : Sort v} {β : α → Sort w} {β' : α' → Sort w}
    {fn : (a : α) → β a} {gn : (a : α') → β' a} {a : α} {a' : α'}
    (hα : α = α') (hβ : β ≍ β') (hf : fn ≍ gn) (ha : a ≍ a') : fn a ≍ gn a' := by
  subst hα; cases eq_of_heq hβ; cases eq_of_heq hf; cases eq_of_heq ha; rfl

/-- The composite open `(e.inv ≫ U.ι) ''ᵁ ⊤` equals the standard open `D(f) = basicOpen f`. -/
theorem bridge_N_gamma_open_comp_eq
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    ((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv ≫ (specBasicOpen R
        f).ι) ''ᵁ
        (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens)
      = PrimeSpectrum.basicOpen f := by
  let e := AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f
  let U : (Spec (CommRingCat.of R)).Opens := specBasicOpen R f
  rw [AlgebraicGeometry.Scheme.Hom.comp_image]
  have hi : e.inv ''ᵁ (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens) = ⊤ := by
    rw [AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange,
        AlgebraicGeometry.Scheme.Hom.opensRange_of_isIso]
  rw [hi]
  exact AlgebraicGeometry.Scheme.Opens.ι_image_top U

/-- The carrier-transport value `(φ z).val p` equals the `actionTransport`-transport value at
the corresponding point.  Both `φ z` and `actionTransport.app ⊤ z` are pure casts of `z`, by
`bridge_N_gamma_phi_heq` and `bridge_N_gamma_at_heq`, hence heterogeneously equal to each
other, so their `.val` projections agree at points with the same prime coordinate `↑p`.  The
open identification `(e.inv ≫ U.ι) ''ᵁ ⊤ = basicOpen f` supplies the index type and predicate
equalities.  Together with `bridge_N_gamma_actionTransport_val` this expresses `(φ z).val p` as
a plain `z.val` reindex. -/
theorem bridge_N_gamma_linchpin_val
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (z : bridgeNGamma R M f)
    (p : (Opposite.unop (Opposite.op (PrimeSpectrum.basicOpen f))))
    (mem : (p : PrimeSpectrum R) ∈
      ((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv ≫ (specBasicOpen R
          f).ι) ''ᵁ
        (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens)) :
    ((bridge_N_gamma_carrier_addEquiv R M f z : bridgeNGammaTilde R M f).val p)
      = ((actionTransport R M f).app (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens)
          z).val
          ⟨(p : PrimeSpectrum R), mem⟩ := by
  have hphi_at : (bridge_N_gamma_carrier_addEquiv R M f z : bridgeNGammaTilde R M f) ≍
      ((actionTransport R M f).app (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens) z) :=
    (bridge_N_gamma_phi_heq R M f z).trans (bridge_N_gamma_at_heq R M f z).symm
  have hOu : (Opposite.unop ((AlgebraicGeometry.Scheme.Hom.opensFunctor
        ((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv ≫ (specBasicOpen R
            f).ι)).op.obj
          (Opposite.op (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens))))
      = PrimeSpectrum.basicOpen f := bridge_N_gamma_open_comp_eq R M f
  apply eq_of_heq
  refine bridge_N_gamma_heq_funapp
    (fn := (bridge_N_gamma_carrier_addEquiv R M f z : bridgeNGammaTilde R M f).val)
    (gn := ((actionTransport R M f).app (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens)
        z).val)
    (a := p) (a' := ⟨(p : PrimeSpectrum R), mem⟩) ?_ ?_ ?_ ?_
  · rw [hOu]
  · rw [hOu]
  · exact Subtype.val.hcongr_3 _ _ (by simp only [Opposite.unop_op]; rw [hOu]) _ _
      (by rw [hOu]) _ _ hphi_at
  · rw [Subtype.heq_iff_coe_eq (by intro x; rw [hOu])]

/-- For the section ring `Γ(structureSheafInType R R, U)` acting on the module sections
`Γ(structureSheafInType R M, U)`, the value of `c • s` at a point `x` is the pointwise product
`c.val x • s.val x` of the stalk values.  This is the value-level analogue of
`structureSheafInType.smul_apply`, which is keyed on the bare-`R` action, for the *section-ring*
action, and holds definitionally.  Once a cross-scheme `c : Γ(Spec R_f, 𝒪)` is pulled back along
`g = e.inv ≫ U.ι` to a `Γ(D(f), 𝒪_{Spec R})` section, this turns its action value into
`(pulled-back c).val x • w.val x`. -/
theorem structureSheafInType_csmul_val
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
    (U : TopologicalSpace.Opens (PrimeSpectrum.Top R))
    (c : (AlgebraicGeometry.structureSheafInType R R).obj.obj (Opposite.op U))
    (s : (AlgebraicGeometry.structureSheafInType R M).obj.obj (Opposite.op U))
    (x : U) :
    (c • s).1 x = c.1 x • s.1 x :=
  rfl

/-- The open-immersion `g = e.inv ≫ D(f).ι : Spec R_f ⟶ Spec R` IS `Spec.map (algebraMap R R_f)`.
`basicOpenIsoSpecAway f` is `IsOpenImmersion.isoOfRangeEq (D(f).ι) (Spec.map (algebraMap …))`, so
`(basicOpenIsoSpecAway f).inv ≫ D(f).ι = Spec.map (algebraMap …)` by `isoOfRangeEq_inv_fac`. -/
@[ega "I 1.3.6" "partial", ega "I 10.2.3" "special case"]
theorem bridge_N_gamma_g_eq (R : Type u) [CommRing R] (f : R) :
    ((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv ≫ (specBasicOpen R f).ι)
      = AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))) :=
  AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/-- **`toOpen`-`comap` naturality of `g.app V` (structure-sheaf level).**
The structure-sheaf section ring map `g.app (g ''ᵁ ⊤)` for `g = e.inv ≫ D(f).ι =
Spec.map(algebraMap R R_f)`
intertwines the constant-section maps: `algebraMap R Γ(R, g''ᵁ⊤) ≫ g.app = algebraMap R R_f ≫
algebraMap R_f Γ`.
Proven by `Spec.map_app` (via `bridge_N_gamma_g_eq`) + `StructureSheaf.toOpen_comp_comap`; the
`generalize`
of the open `g''ᵁ⊤` lets `g` be rewritten in the `.app` slot without a motive-type clash. -/
theorem bridge_N_gamma_cval_hM (R : Type u) [CommRing R] (f : R) :
    haveI : AlgebraicGeometry.IsOpenImmersion
        (AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv :=
      AlgebraicGeometry.IsOpenImmersion.of_isIso _
    CommRingCat.ofHom (algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj
        (Opposite.op (((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv
          ≫ (specBasicOpen R f).ι) ''ᵁ (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens)))))
      ≫ AlgebraicGeometry.Scheme.Hom.app
          ((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv ≫ (specBasicOpen
              R f).ι)
          (((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv ≫ (specBasicOpen
              R f).ι) ''ᵁ
            (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens))
      = CommRingCat.ofHom (algebraMap R (Localization.Away f))
          ≫ CommRingCat.ofHom (algebraMap (Localization.Away f) _) := by
  have hg : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv :=
    AlgebraicGeometry.IsOpenImmersion.of_isIso _
  generalize hV : ((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv ≫
      (specBasicOpen R f).ι) ''ᵁ
      (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens) = V
  rw [bridge_N_gamma_g_eq, AlgebraicGeometry.Spec.map_app]
  exact AlgebraicGeometry.StructureSheaf.toOpen_comp_comap (algebraMap R (Localization.Away f)) V

/-- **Morphism-level form of the constant-section naturality.**
`(algebraMap R R_f ≫ globalSectionsIso.hom) ≫ (g.appIso ⊤).inv = algebraMap R Γ(R, g''ᵁ⊤)` as a
`CommRingCat` morphism `R ⟶ Γ(R, g''ᵁ⊤)`.  Proven from `bridge_N_gamma_cval_hM` via
`Iso.comp_inv_eq`
+ `appIso_hom` + `StructureSheaf.algebraMap_self_map` (the `pmap` reindex on the constant section).
-/
theorem bridge_N_gamma_cval_mor (R : Type u) [CommRing R] (f : R) :
    haveI : AlgebraicGeometry.IsOpenImmersion
        (AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv :=
      AlgebraicGeometry.IsOpenImmersion.of_isIso _
    (CommRingCat.ofHom (algebraMap R (Localization.Away f))
        ≫ (AlgebraicGeometry.StructureSheaf.globalSectionsIso (CommRingCat.of (Localization.Away
            f))).hom)
      ≫ (AlgebraicGeometry.Scheme.Hom.appIso
          ((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv ≫ (specBasicOpen
              R f).ι) ⊤).inv
      = CommRingCat.ofHom (algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj
          (Opposite.op (((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv
            ≫ (specBasicOpen R f).ι) ''ᵁ
            (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens))))) := by
  have hg : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv :=
    AlgebraicGeometry.IsOpenImmersion.of_isIso _
  rw [Iso.comp_inv_eq, AlgebraicGeometry.Scheme.Hom.appIso_hom,
      AlgebraicGeometry.StructureSheaf.globalSectionsIso_hom]
  rw [← Category.assoc, bridge_N_gamma_cval_hM R f, Category.assoc]
  congr 1

/-- **Pulled-back constant section = constant section (Part 3a/3b germ identification, ring
level).**
The structure-sheaf section `c = globalSectionsIso(algebraMap R R_f r)` over `Spec R_f`,
pulled back
along `g = e.inv ≫ D(f).ι` (i.e. applying `(g.appIso ⊤).inv`), equals the constant `algebraMap r`
section `algebraMap R Γ(Spec R, g ''ᵁ ⊤) r`.  This is the structure-sheaf naturality fact that the
pullback of the constant `r/1` section is the constant `r/1` section; combined with the (`rfl`)
value-of-constant-section `(algebraMap r).val q = algebraMap R R_q r`, it discharges the germ
identification, and (via `csmul_val_residual`) closes the whole
`csmul_val`/`action_section`/Tag-05JM
kernel.

This is a pure commutative-algebra and structure-sheaf naturality fact: no modules, no
sheafify and no QCoh transport, the abstract `c•w` action being discharged by `rfl` in
`csmul_val_residual`.  The route is:
* `bridge_N_gamma_g_eq` : `g = Spec.map (algebraMap R R_f)`.
* `StructureSheaf.globalSectionsIso_hom` : `globalSectionsIso.hom = ofHom (algebraMap …)`, so the
LHS
  scalar is `(g.appIso ⊤).inv (algebraMap_{R→Γ(Spec R_f,⊤)} r)` (after `IsScalarTower` merge).
* The naturality `ofHom (algebraMap R Γ(Spec R_f,⊤)) ≫ (g.appIso ⊤).inv = ofHom (algebraMap R Γ(R,
g''ᵁ⊤))`
  follows from `Scheme.Hom.appIso_inv_app` (`(g.appIso U).inv ≫ g.app (g''ᵁU) = presheaf.map
  (eqToHom).op`)
  composed/cancelled with `Spec.map_app` (`g.app = comap (algebraMap)` via `g_eq`),
  `StructureSheaf.toOpen_comp_comap` (`algebraMap ≫ comap = algebraMap ≫ algebraMap`), and
  `StructureSheaf.algebraMap_self_map`/`toOpen_res` (`algebraMap ≫ presheaf.map = algebraMap`); the
  `g.app` component is split-mono (open immersion) so it cancels.  Alternatively
  `IsLocalization.algHom_subsingleton` once the composite is packaged as an `R_f →ₐ[R] Γ(R,g''ᵁ⊤)`
  (needs the same naturality as its `commutes'`).  `Γ(R, g''ᵁ⊤) = Γ(R, basicOpen f)` is
  `IsLocalization.Away f` (`bridge_N_gamma_open_comp_eq` + `instAway…basicOpen`). -/
theorem bridge_N_gamma_cval_eq (R : Type u) [CommRing R] (f : R) (r : R) :
    haveI : AlgebraicGeometry.IsOpenImmersion
        (AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv :=
      AlgebraicGeometry.IsOpenImmersion.of_isIso _
    (((AlgebraicGeometry.Scheme.Hom.appIso
        ((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv ≫ (specBasicOpen R
            f).ι)
          ⊤).inv
        ((CommRingCat.Hom.hom (AlgebraicGeometry.StructureSheaf.globalSectionsIso
              (CommRingCat.of (Localization.Away f))).hom)
            ((algebraMap R (Localization.Away f)) r))))
      = (algebraMap R ((AlgebraicGeometry.structureSheafInType R R).obj.obj
          (Opposite.op (((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv
            ≫ (specBasicOpen R f).ι) ''ᵁ
              (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens)))) r) := by
  have h := congrArg (fun m => m r) (bridge_N_gamma_cval_mor R f)
  simp only [CategoryTheory.comp_apply, ConcreteCategory.hom_ofHom] at h
  exact h

/-- **Residual: restrict-module `c`-action value = bare-`R` stalk scalar.**
For the `Γ(Spec R_f, 𝒪)`-section `c = (globalSectionsIso R_f).hom (algebraMap R R_f r)` and an
arbitrary section `w` of the restricted-tilde module `(M~).restrict (e.inv ≫ U.ι)` over `Spec R_f`,
the value of the section action `c • w` at the prime `p ∈ D(f)` equals the bare-`R` stalk
action
`r •_{M_p} (w.val p)`.  This is the maximally-sharpened form of the QCoh transport kernel: the
explicit `algebraMap R R_p r` germ scalar has been eliminated, factored out via
`bridge_N_gamma_germ_scalar`, `algebraMap_smul`), so the sole remaining content is that the
`Γ(Spec R_f, 𝒪)`-section (restrict-module) action of `c` agrees, value-by-value at `p`, with the
bare-`R` action of `r` — i.e. the pullback `c ↦ r` under the global-sections / `D(f) ≅ Spec R_f`
identification commutes with the structure-sheaf section action.

ROUTE (inline): the `c`-action is the abstract `Scheme.Modules` section action on
`(M~).restrict (e.inv ≫ U.ι)` over `Spec R_f`.  To evaluate at `p`, connect `.val p` to a germ via
`TopCat.stalkToFiber_germ` (`(subsheafToTypes P).germ U x hx f` evaluated by `stalkToFiber` = `f.1
x`)
and `PresheafOfModules.germ_smul` (`germ (r • m) = R.germ r • germ m`), then identify the germ of
`c`
at the `e`-image of `p` with `algebraMap R R_p r` via `bridge_N_gamma_germ_toStalk` +
`IsLocalization.AtPrime` stalk + `bridge_N_gamma_germ_scalar`.  Alternatively pull `c` back along
`g = e.inv ≫ U.ι` to a `Γ(D(f), 𝒪_R)` structure-sheaf section `c'` (the constant `algebraMap r`
section) so the action becomes the bare structure-sheaf section action handled by
`structureSheafInType_csmul_val` / `structureSheafInType.smul_apply`. -/
theorem csmul_val_residual
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (r : R)
    (c : Γ((Spec (CommRingCat.of (Localization.Away f))),
            (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens)))
    (hc : c = (CommRingCat.Hom.hom (AlgebraicGeometry.StructureSheaf.globalSectionsIso
              (CommRingCat.of (Localization.Away f))).hom)
            ((algebraMap R (Localization.Away f)) r))
    (w : Γ(((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
          ((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv
            ≫ (specBasicOpen R f).ι)),
            (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens)))
    (p : (Opposite.unop (Opposite.op (PrimeSpectrum.basicOpen f))))
    (hmem : (p : PrimeSpectrum R) ∈
      ((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv ≫ (specBasicOpen R
          f).ι) ''ᵁ
        (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens)) :
    ((c • w).val ⟨(p : PrimeSpectrum R), hmem⟩)
      = r • (w.val ⟨(p : PrimeSpectrum R), hmem⟩) := by
  have : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv :=
    AlgebraicGeometry.IsOpenImmersion.of_isIso _
  -- STEP 1 (Part 2, semilinearity + pointwise, ALL by `rfl`): the restrict-module
  -- `Γ(Spec R_f, 𝒪)`-section action of `c` on `w`, evaluated at `p`, is the structure-sheaf
  -- `Γ(Spec R, D(f))`-section action of the pulled-back scalar `c' := (g.appIso ⊤).inv c`,
  -- evaluated pointwise (`structureSheafInType_csmul_val`): `(c•w).val q = c'.val q • w.val q`.
  -- (`Scheme.Modules.restrict = pushforward`, whose section module = `restrictScalars
  -- (g.appIso).inv`,
  --  and `ModuleCat.restrictScalars.smul_def` is `rfl`; the `.val` projection of the section-ring
  --  action is also `rfl` — see `structureSheafInType_csmul_val`.)
  rw [show ((c • w).val ⟨(p : PrimeSpectrum R), hmem⟩)
        = (((AlgebraicGeometry.Scheme.Hom.appIso
              ((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv
                ≫ (specBasicOpen R f).ι) ⊤).inv c).val ⟨(p : PrimeSpectrum R), hmem⟩)
            • (w.val ⟨(p : PrimeSpectrum R), hmem⟩) from rfl]
  -- STEP 2 (Part 3a/3b germ identification): the pulled-back scalar `c'` is the constant
  -- `algebraMap R Γ(R, D(f)) r` section (`bridge_N_gamma_cval_eq`), whose value at `p` is
  -- `algebraMap R R_p r` (`rfl`).  Then `bridge_N_gamma_germ_scalar` collapses the explicit germ
  -- scalar `algebraMap R R_p r •_{M_p}` to the bare-`R` action `r •_{M_p}`.
  rw [hc, bridge_N_gamma_cval_eq R f r]
  exact bridge_N_gamma_germ_scalar R M (p : PrimeSpectrum R) r _

/-- **Pointwise structure-sheaf-section scalar commutation (the residual analytic atom).**
For the `Γ(Spec R_f, 𝒪)`-section `c = (globalSectionsIso R_f).hom (algebraMap R R_f r)` and an
arbitrary section `w` of the restricted-tilde module `(M~).restrict (e.inv ≫ U.ι)` over `Spec R_f`,
the value of the section action `c • w` at the prime `p ∈ D(f)` equals the germ scalar
`algebraMap R R_p r` acting on `w.val p`.  This reduces to the sharper
`csmul_val_residual` by collapsing the explicit `algebraMap R R_p r` germ scalar on the
right-hand side to the bare-`R` action `r •` via `bridge_N_gamma_germ_scalar`
(`algebraMap_smul`); the content is then the restrict-module `c`-action value identity
`csmul_val_residual`. -/
theorem bridge_N_gamma_csmul_val
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (r : R)
    (c : Γ((Spec (CommRingCat.of (Localization.Away f))),
            (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens)))
    (hc : c = (CommRingCat.Hom.hom (AlgebraicGeometry.StructureSheaf.globalSectionsIso
              (CommRingCat.of (Localization.Away f))).hom)
            ((algebraMap R (Localization.Away f)) r))
    (w : Γ(((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
          ((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv
            ≫ (specBasicOpen R f).ι)),
            (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens)))
    (p : (Opposite.unop (Opposite.op (PrimeSpectrum.basicOpen f))))
    (hmem : (p : PrimeSpectrum R) ∈
      ((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv ≫ (specBasicOpen R
          f).ι) ''ᵁ
        (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens)) :
    ((c • w).val ⟨(p : PrimeSpectrum R), hmem⟩)
      = (algebraMap R (StructureSheaf.Localizations R (p : PrimeSpectrum R)) r)
          • (w.val ⟨(p : PrimeSpectrum R), hmem⟩) := by
  rw [bridge_N_gamma_germ_scalar]
  exact csmul_val_residual R M f r c hc w p hmem

/-- **Sub-lemma B.carrier.action_section (the cleaner, non-circular transport atom).**
The genuine sheafify/equivalence-transport content, with the representative abstracted to an
arbitrary section `k : Γ(M~, D(f))` (and `φ.symm k` its preimage in `Γ(N,⊤)`), so both `.val p`
projections are well-typed.  At a prime `p ∈ D(f)`:  the value of
`φ ((algebraMap R R_f r) • φ.symm k)` (the `R_f`-action on `Γ(N,⊤)` via `modulesSpecToSheaf`)
equals the explicit germ scalar `algebraMap R R_p r` acting on `k.val p`.

This is NON-CIRCULAR (it does not reduce to `bridge_N_gamma_smul_compat`/`_lhs`): it is quantified
over ALL sections `k` and concerns the composite `φ ∘ (algebraMap r • ·) ∘ φ.symm`.  The standing
attack: `rw [ModuleCat.restrictScalars.smul_def]` peels the OUTER
`restrictScalars (globalSectionsIso R_f).hom` layer of the action INLINE, reducing to the inner
`Scheme.Modules` O-module section action; the residue is that `φ` (only an `AddEquiv`) must push
that inner action through to the structure-sheaf germ at `p` (`bridge_N_gamma_germ_toStalk`
+ `IsLocalization.AtPrime` stalk).  The structural route is to rebuild the transport as a
`Scheme.Modules` presheaf-section map (`restrictFunctorCongr_hom_app_app` components are
`presheaf.map (eqToHom)`, satisfying `Scheme.Modules.map_smul`).

the linchpin is available.  `bridge_N_gamma_linchpin_val` (above) gives
`(φ z).val p = (actionTransport.app⊤ z).val ⟨↑p, mem⟩` for ANY `z` (both `φ z` and
`actionTransport.app⊤ z` are pure casts of `z` — `bridge_N_gamma_phi_heq` / `bridge_N_gamma_at_heq`
— so HEq to each other; `.val` then agrees pointwise via `bridge_N_gamma_heq_funapp` +
`Subtype.val.hcongr_3` + the open identity `bridge_N_gamma_open_comp_eq`).  ASSEMBLY (verified to
fire
on a probe): `rw [ModuleCat.restrictScalars.smul_def]` (peel) then
`rw [bridge_N_gamma_linchpin_val R M f _ p hmem, actionTransport_app_smul]`
(`hmem` = `bridge_N_gamma_open_comp_eq ▸ p.2`).  This leaves the SOLE residual:
`(c • actionTransport.app⊤ (φ.symm k)).val ⟨↑p, hmem⟩ = algebraMap R R_p r • k.val p`,
`c = (globalSectionsIso R_f).hom (algebraMap r)`.  To finish: (a) the pointwise section-scalar
`(c • w).val q = (germ_q c) • (w.val q)` — push `c` through `actionTransport.app⊤ =
presheaf.map(eqToHom).op`
(`actionTransport_app_eq`) by `Scheme.Modules.map_smul`, then `StructureSheaf.res_apply` pointwise;
(b) `germ_q c = algebraMap R R_p r` via `bridge_N_gamma_germ_toStalk` +
`IsLocalization.AtPrime`;
(c) `w.val ⟨↑p,hmem⟩ = (φ (φ.symm k)).val p = k.val p` by `bridge_N_gamma_linchpin_val` backwards +
`AddEquiv.apply_symm_apply`. -/
theorem bridge_N_gamma_action_section
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (r : R) (k : bridgeNGammaTilde R M f)
    (p : (Opposite.unop (Opposite.op (PrimeSpectrum.basicOpen f)))) :
    (bridge_N_gamma_carrier_addEquiv R M f
        ((algebraMap R (Localization.Away f) r)
          • (bridge_N_gamma_carrier_addEquiv R M f).symm k) : (bridgeNGammaTilde R M f)).val p
      = (algebraMap R (StructureSheaf.Localizations R (p : PrimeSpectrum R)) r) • (k.val p) := by
  -- structure-sheaf section / germ identification; k-quantified, well-typed, non-circular)
  rw [ModuleCat.restrictScalars.smul_def]
  have hmem : (p : PrimeSpectrum R) ∈
      ((AlgebraicGeometry.basicOpenIsoSpecAway (R := CommRingCat.of R) f).inv ≫ (specBasicOpen R
          f).ι) ''ᵁ
        (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens) := by
    rw [bridge_N_gamma_open_comp_eq R M f]; exact p.property
  have hwk : ((actionTransport R M f).app (⊤ : (Spec (CommRingCat.of (Localization.Away f))).Opens)
        ((bridge_N_gamma_carrier_addEquiv R M f).symm k)).val ⟨(p : PrimeSpectrum R), hmem⟩
      = k.val p := by
    rw [← bridge_N_gamma_linchpin_val R M f ((bridge_N_gamma_carrier_addEquiv R M f).symm k) p hmem]
    rw [AddEquiv.apply_symm_apply]
  rw [bridge_N_gamma_linchpin_val R M f _ p hmem, actionTransport_app_smul, ← hwk]
  exact bridge_N_gamma_csmul_val R M f r _ rfl _ p hmem

/-- The left-hand side of the pointwise `smul` identity: the value at `p` of the carrier
transport of `r • x` for `r : R` acting through `algebraMap R (Localization.Away f)`. -/
theorem bridge_N_gamma_smul_pointwise_lhs
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    letI : Module R (bridgeNGamma R M f) :=
      Module.compHom _ (algebraMap R (Localization.Away f))
    ∀ (r : R) (x : bridgeNGamma R M f)
      (p : (Opposite.unop (Opposite.op (PrimeSpectrum.basicOpen f)))),
      (bridge_N_gamma_carrier_addEquiv R M f (r • x) : (bridgeNGammaTilde R M f)).val p =
        (algebraMap R (StructureSheaf.Localizations R (p : PrimeSpectrum R)) r) •
          ((bridge_N_gamma_carrier_addEquiv R M f x : (bridgeNGammaTilde R M f)).val p) := by
  let inst : Module R (bridgeNGamma R M f) :=
    Module.compHom _ (algebraMap R (Localization.Away f))
  intro r x p
  have hx : x = (bridge_N_gamma_carrier_addEquiv R M f).symm
      (bridge_N_gamma_carrier_addEquiv R M f x) := by
    rw [AddEquiv.symm_apply_apply]
  rw [show (r • x) = (algebraMap R (Localization.Away f) r) • x from rfl]
  conv_lhs => rw [hx]
  exact bridge_N_gamma_action_section R M f r (bridge_N_gamma_carrier_addEquiv R M f x) p

/-- **Pointwise scalar identity at `p ∈ D(f)`** (Parts 1+2+3, the residual of
`bridge_N_gamma_smul_compat`).  Closes from the geometric-transport atom
`bridge_N_gamma_smul_pointwise_lhs` (which produces the explicit germ scalar `algebraMap R R_p r`)
followed by the algebraic germ kernel `bridge_N_gamma_germ_scalar`
(`algebraMap R R_p r •_{M_p} m = r •_{M_p} m`, the localization scalar tower). -/
theorem bridge_N_gamma_smul_pointwise
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    letI : Module R (bridgeNGamma R M f) :=
      Module.compHom _ (algebraMap R (Localization.Away f))
    ∀ (r : R) (x : bridgeNGamma R M f)
      (p : (Opposite.unop (Opposite.op (PrimeSpectrum.basicOpen f)))),
      (bridge_N_gamma_carrier_addEquiv R M f (r • x) : (bridgeNGammaTilde R M f)).val p =
        r • ((bridge_N_gamma_carrier_addEquiv R M f x : (bridgeNGammaTilde R M f)).val p) := by
  let inst : Module R (bridgeNGamma R M f) :=
    Module.compHom _ (algebraMap R (Localization.Away f))
  intro r x p
  rw [bridge_N_gamma_smul_pointwise_lhs R M f r x p]
  exact bridge_N_gamma_germ_scalar R M (p : PrimeSpectrum R) r _


/-- **Sub-lemma B.carrier.smul_compat (Stage 2 — THE GENUINE HARD KERNEL).** The additive
carrier identity `bridge_N_gamma_carrier_addEquiv` is `R`-linear, where `R` acts on
`Γ(N, ⊤)` by restriction of scalars along `algebraMap R R_f` (the `Module.compHom`
instance).  This is the scalar-compatibility fact that blocked the closer: the `R_f`-action
on `Γ(N,⊤)` (sections of the structure sheaf via `R_f ≅ Γ(Spec R_f, 𝒪) ≅ Γ(D(f), 𝒪)`),
restricted along `R → R_f`, equals the standard `R`-action on `Γ(M~, D(f))`.  Routes:
the restriction functors `restrictFunctor` are `𝒪`-module functors, so their action by
structure-sheaf sections is respected; the composite `R → R_f ≅ Γ(D(f), 𝒪)` equals the
localization map `R → Γ(D(f), 𝒪)` carried through `basicOpenIsoSpecAway`
(`IsAffineOpen.isLocalization_basicOpen` / `StructureSheaf.openAlgebra`). -/
theorem bridge_N_gamma_smul_compat
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    letI : Module R (bridgeNGamma R M f) :=
      Module.compHom _ (algebraMap R (Localization.Away f))
    ∀ (r : R) (x : bridgeNGamma R M f),
      bridge_N_gamma_carrier_addEquiv R M f (r • x) =
        r • bridge_N_gamma_carrier_addEquiv R M f x := by
  intro r x
  -- Both sides are sections of `structureSheafInType R M` over `D(f)` (a subtype of the
  -- dependent product over points of `D(f)`); compare pointwise.
  apply Subtype.ext
  funext p
  -- RHS: the native `R`-action on `Γ(M~, D(f))` is pointwise (`structureSheafInType.smul_apply`).
  rw [structureSheafInType.smul_apply]
  -- Remaining pointwise scalar identity at the prime `p ∈ D(f)`.  The genuine content
  -- (isolated as `bridge_N_gamma_smul_pointwise`): the carrier transport `φ` does not
  -- change the underlying section function, and the `R_f`-sheaf action on `Γ(N,⊤)`
  -- restricted along `algebraMap R R_f` agrees with the native `R`-action germ-by-germ
  -- (Step 3 of the argument: `globalSectionsIso`/`toOpen`/`germ_toOpen` +
  -- the localization scalar tower `IsScalarTower R R_p M_p`).
  exact bridge_N_gamma_smul_pointwise R M f r x p

/-- **Sub-lemma B.scalarTower.** The `R`-module structure on the global sections
`Γ(N, ⊤)` (obtained by restriction of scalars from its genuine `R_f`-module structure)
is compatible with the `R_f`-structure: `R` acts through the algebra map `R → R_f`.

the `R_f`-action on `modulesSpecToSheaf.obj N` comes from sections of the
structure sheaf via `R_f ≅ Γ(Spec R_f, 𝒪)`; the ambient `R`-action factors through that.
This is `IsScalarTower.of_algebraMap_smul` / unfolding the `Module R` instance on the
`ModuleCat (Localization.Away f)` carrier (it is `Module.compHom` along `algebraMap`).
Likely closeable by providing the defeq witness, or `IsScalarTower.of_algebraMap_eq`. -/
instance bridge_N_gamma_scalarTower
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    letI : Module R (bridgeNGamma R M f) :=
      Module.compHom _ (algebraMap R (Localization.Away f))
    IsScalarTower R (Localization.Away f) (bridgeNGamma R M f) := by
  let : Module R (bridgeNGamma R M f) :=
    Module.compHom _ (algebraMap R (Localization.Away f))
  exact IsScalarTower.of_algebraMap_smul fun r x => rfl

/-- **Sub-lemma B.Requiv.** The `R`-linear equivalence `Γ(N, ⊤) ≃ₗ[R] M_f`.

Stages 1+2+3, localized:
  • Carrier identity `Γ(N,⊤) = Γ(M~, basicOpen f)` as `Ab` via `Scheme.Modules.restrict_obj`
    twice + `e.inv ''ᵁ ⊤ = ⊤` (iso) + `(specBasicOpen R f).ι ''ᵁ ⊤ = basicOpen f`
    (`Scheme.Hom.image_top_eq_opensRange` + `opensRange_of_isIso` + `Scheme.Opens.ι_image_top`).
  • Prove that identity is `R`-linear (scalar compatibility, see comment above) ⟹ an
    `R`-linear equiv `c : Γ(N,⊤) ≃ₗ[R] Γ(M~, basicOpen f)`.
  • `tilde.toOpen M (basicOpen f)).hom` is `IsLocalizedModule (powers f)` (instance);
    transport along `c.symm` (`IsLocalizedModule.of_linearEquiv_right`) to make the composite
    `M → Γ(N,⊤)` a localization map.
  • `IsLocalizedModule.linearEquiv (Submonoid.powers f) (that map)
        (LocalizedModule.mkLinearMap (Submonoid.powers f) M) : Γ(N,⊤) ≃ₗ[R] M_f`. -/
@[ega "I 9.3.3" "special case",
  ega "I 9.6.2" "partial",
  ega "II 3.2.1" "special case",
  ega "III 1.4.6" "special case"]
noncomputable def bridge_N_gamma_Requiv
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    letI : Module R (bridgeNGamma R M f) :=
      Module.compHom _ (algebraMap R (Localization.Away f))
    (bridgeNGamma R M f) ≃ₗ[R] LocalizedModule (Submonoid.powers f) M := by
  letI : Module R (bridgeNGamma R M f) :=
    Module.compHom _ (algebraMap R (Localization.Away f))
  -- Stage 1+2: the R-linear carrier equiv Γ(N,⊤) ≃ₗ[R] Γ(M~, D(f)).
  let c : bridgeNGamma R M f ≃ₗ[R] bridgeNGammaTilde R M f :=
    (bridge_N_gamma_carrier_addEquiv R M f).toLinearEquiv
      (bridge_N_gamma_smul_compat R M f)
  -- Stage 3: toOpenₗ exhibits Γ(M~, D(f)) as a localization of M at powers f.
  let g₀ : M →ₗ[R] bridgeNGammaTilde R M f :=
    AlgebraicGeometry.StructureSheaf.toOpenₗ R M (PrimeSpectrum.basicOpen f)
  letI hloc : IsLocalizedModule (Submonoid.powers f) g₀ := inferInstance
  -- Transport the localization map along c.symm to a localization map M → Γ(N,⊤).
  letI : IsLocalizedModule (Submonoid.powers f) (c.symm.toLinearMap ∘ₗ g₀) :=
    IsLocalizedModule.of_linearEquiv (Submonoid.powers f) g₀ c.symm
  -- Compare to M_f via the canonical localization map.
  exact IsLocalizedModule.linearEquiv (Submonoid.powers f)
    (c.symm.toLinearMap ∘ₗ g₀)
    (LocalizedModule.mkLinearMap (Submonoid.powers f) M)

/-- **Sub-lemma B for `bridge_N_iso` (Γ-sections identification) — assembly.**
`Γ(N, ⊤) ≅ M_f` in `ModuleCat (Localization.Away f)`, obtained by upgrading the `R`-linear
equivalence `bridge_N_gamma_Requiv` to an `R_f`-linear one
(`LinearEquiv.extendScalarsOfIsLocalization`, using `bridge_N_gamma_scalarTower`) and reading
it as a `ModuleCat` iso (`LinearEquiv.toModuleIso`). -/
@[ega "I 9.3.3" "special case", ega "II 3.2.1" "special case", ega "III 1.4.6" "special case"]
noncomputable def bridge_N_gammaIso
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    (modulesSpecToSheaf.obj ((bridge_specAwayEquiv R f).functor.obj
        ((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
          (specBasicOpen R f).ι))).presheaf.obj (Opposite.op ⊤) ≅
      ModuleCat.of (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  letI : Module R (bridgeNGamma R M f) :=
    Module.compHom _ (algebraMap R (Localization.Away f))
  haveI := bridge_N_gamma_scalarTower R M f
  haveI : IsScalarTower R (Localization.Away f)
      (LocalizedModule (Submonoid.powers f) M) := inferInstance
  exact ((bridge_N_gamma_Requiv R M f).extendScalarsOfIsLocalization
    (Submonoid.powers f) (Localization.Away f)).toModuleIso

/-- The equivalence `bridge_specAwayEquiv` carries the restriction of `M̃` to `D(f)` to the
sheaf of modules associated with the localized module `M_f` over `Spec R_f`. -/
@[ega "I 1.3.6", ega "I 9.6.2" "partial"]
noncomputable def bridge_N_iso
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    (bridge_specAwayEquiv R f).functor.obj
        ((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
          (specBasicOpen R f).ι) ≅
      AlgebraicGeometry.tilde (R := CommRingCat.of (Localization.Away f))
        (ModuleCat.of (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)) := by
  haveI := bridge_N_fromTildeΓ_isIso R M f
  -- N ≅ tilde (Γ N) : the counit `fromTildeΓ` is an iso (Sub-lemma A)
  have iso1 := asIso (@AlgebraicGeometry.Scheme.Modules.fromTildeΓ
      (CommRingCat.of (Localization.Away f))
      ((bridge_specAwayEquiv R f).functor.obj
        ((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
          (specBasicOpen R f).ι)))
  -- tilde (Γ N) ≅ tilde (M_f) : apply the tilde functor to the Γ-iso (Sub-lemma B)
  have iso2 := (AlgebraicGeometry.tilde.functor (CommRingCat.of (Localization.Away f))).mapIso
    (bridge_N_gammaIso R M f)
  refine iso1.symm ≪≫ ?_
  simpa [AlgebraicGeometry.tilde.functor_obj] using iso2

/-- **Bridge Sub-lemma 4 (`exists_free_iso_of_equiv`).** A categorical equivalence whose
functor and inverse both send `free I ↦ free I` (same index) transports the property
"isomorphic to some free object" across the equivalence.

PROOF: pure category theory. (⇒) `mapIso` the given iso by `eqv.functor`, then compose
with `hfun`. (⇐) use `eqv.unitIso` to write `X ≅ eqv.inverse.obj (eqv.functor.obj X)`,
`mapIso` by `eqv.inverse`, compose with `hinv`. -/
theorem exists_free_iso_of_equiv
    {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (eqv : 𝒞 ≌ 𝒟)
    (Ofree : Type u → 𝒞) (Dfree : Type u → 𝒟)
    (hfun : ∀ I, eqv.functor.obj (Ofree I) ≅ Dfree I)
    (hinv : ∀ I, eqv.inverse.obj (Dfree I) ≅ Ofree I)
    (X : 𝒞) :
    (∃ I : Type u, Nonempty (X ≅ Ofree I)) ↔
      (∃ I : Type u, Nonempty (eqv.functor.obj X ≅ Dfree I)) := by
  constructor
  · rintro ⟨I, ⟨φ⟩⟩
    exact ⟨I, ⟨eqv.functor.mapIso φ ≪≫ hfun I⟩⟩
  · rintro ⟨I, ⟨ψ⟩⟩
    refine ⟨I, ⟨?_⟩⟩
    refine (eqv.unitIso.app X) ≪≫ ?_
    refine eqv.inverse.mapIso ψ ≪≫ hinv I
/-- Fixed-index form of the transport along `bridge_specAwayEquiv`. -/
private theorem restrict_iso_free_iff_tilde_away_iso_free
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (J : Type u) :
    Nonempty
        ((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
          (specBasicOpen R f).ι ≅ SheafOfModules.free.{u} J) ↔
      Nonempty
        (AlgebraicGeometry.tilde (R := CommRingCat.of (Localization.Away f))
          (ModuleCat.of (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)) ≅
          SheafOfModules.free.{u} J) := by
  constructor
  · rintro ⟨φ⟩
    exact ⟨(bridge_N_iso R M f).symm ≪≫ (bridge_specAwayEquiv R f).functor.mapIso φ ≪≫
      bridge_restrict_free_iso R f J⟩
  · rintro ⟨ψ⟩
    exact ⟨(bridge_specAwayEquiv R f).unitIso.app
        ((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
          (specBasicOpen R f).ι) ≪≫
      (bridge_specAwayEquiv R f).inverse.mapIso ((bridge_N_iso R M f) ≪≫ ψ) ≪≫
      bridge_restrict_free_iso_inv R f J⟩

/-- The restriction of `M̃` to `D(f)` is free if and only if the sheaf of modules associated
with `M_f` over `Spec R_f` is free. -/
theorem tilde_restrict_basicOpen_free_iff_specAway
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    (∃ I : Type u, Nonempty
        ((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
          (specBasicOpen R f).ι ≅ SheafOfModules.free.{u} I)) ↔
      (∃ I : Type u, Nonempty
        (AlgebraicGeometry.tilde (R := CommRingCat.of (Localization.Away f))
          (ModuleCat.of (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)) ≅
          SheafOfModules.free.{u} I)) :=
  exists_congr (restrict_iso_free_iff_tilde_away_iso_free R M f)

/-- **Helper 1, the affine/localization kernel** — the geometric bridge
`tilde_restrict_basicOpen_free_iff_specAway` composed with the pure-algebra wrapper
`tilde_free_iff_module_free`.

(Universes align — basis index of `M_f : Type u`
matches `∃ I : Type u`; degenerate `f` nilpotent / `M = 0` cases consistent). -/
theorem tilde_restrict_basicOpen_free_iff
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    (∃ I : Type u, Nonempty
        ((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
          (specBasicOpen R f).ι ≅ SheafOfModules.free.{u} I)) ↔
      Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) :=
  (tilde_restrict_basicOpen_free_iff_specAway R M f).trans
    (tilde_free_iff_module_free (Localization.Away f)
      (LocalizedModule (Submonoid.powers f) M))

/-- **Reusable (Group B core).** Restriction of `O`-modules along an open immersion `g`
sends the free sheaf `free I` to `free I` (same index). Same recipe as
`bridge_restrict_free_iso` but for a general open immersion: finality of `Opens.map g.base`
holds since `g.isOpenEmbedding.isOpenMap.adjunction` makes it a right adjoint. -/
@[sga "4 IV 13.4" "special case"]
noncomputable def restrictFunctor_obj_free_iso
    {X : Scheme.{u}} {Y : Scheme.{u}} (g : X ⟶ Y) [IsOpenImmersion g] (I : Type u) :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor g).obj (SheafOfModules.free.{u} I) ≅
      SheafOfModules.free.{u} I := by
  haveI hfin : (Opens.map g.base).Final := by
    have : (Opens.map g.base).IsRightAdjoint :=
      ⟨_, ⟨g.isOpenEmbedding.isOpenMap.adjunction⟩⟩
    exact Functor.final_of_isRightAdjoint _
  exact (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback g).app
      (SheafOfModules.free.{u} I) ≪≫
    SheafOfModules.pullbackObjFreeIso (AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom g) I

/-- **Reusable (Group B core).** Given a free trivialization `φ : (M~)|_U ≅ free I` on an
arbitrary open `U` and a standard open `D(f) ≤ U`, restrict `φ` further along the open
immersion `j : D(f) ⟶ U` (`X.homOfLE`, with `j ≫ U.ι = D(f).ι`) to obtain a free
trivialization on `D(f)` with the SAME index `I`. The transport is a `calc` of restrict
natural isos: `restrictFunctorCongr` rewrites `D(f).ι = j ≫ U.ι`, `restrictFunctorComp`
splits the composite restriction, `restrictFunctor j` carries `φ`, and
`restrictFunctor_obj_free_iso` identifies `(free I)|_{D(f)} ≅ free I`. -/
noncomputable def tilde_restrict_free_shrink
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M]
    (U : (Spec (CommRingCat.of R)).Opens) (f : R) (he : specBasicOpen R f ≤ U)
    (I : Type u)
    (φ : (AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict U.ι ≅
          SheafOfModules.free.{u} I) :
    (AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
        (specBasicOpen R f).ι ≅ SheafOfModules.free.{u} I := by
  set Mt := AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)
  set j := (Spec (CommRingCat.of R)).homOfLE he with hj
  haveI : IsOpenImmersion j := by rw [hj]; infer_instance
  have heq : (specBasicOpen R f).ι = j ≫ U.ι := by
    rw [hj]; exact ((Spec (CommRingCat.of R)).homOfLE_ι he).symm
  calc Mt.restrict (specBasicOpen R f).ι
      ≅ Mt.restrict (j ≫ U.ι) :=
        (AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr heq).app Mt
    _ ≅ (AlgebraicGeometry.Scheme.Modules.restrictFunctor j).obj (Mt.restrict U.ι) :=
        (AlgebraicGeometry.Scheme.Modules.restrictFunctorComp j U.ι).app Mt
    _ ≅ (AlgebraicGeometry.Scheme.Modules.restrictFunctor j).obj (SheafOfModules.free.{u} I) :=
        (AlgebraicGeometry.Scheme.Modules.restrictFunctor j).mapIso φ
    _ ≅ SheafOfModules.free.{u} I := restrictFunctor_obj_free_iso j I

/-- A point of an open `U` lies in a standard open `D(f)` contained in `U`. -/
private theorem exists_basicOpen_le_of_mem (R : Type u) [CommRing R]
    {U : (Spec (CommRingCat.of R)).Opens} {x : PrimeSpectrum R} (hxU : x ∈ U) :
    ∃ f : R, x ∈ PrimeSpectrum.basicOpen f ∧ specBasicOpen R f ≤ U := by
  have hbasis := PrimeSpectrum.isBasis_basic_opens (R := R)
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd] at hbasis
  obtain ⟨V, ⟨f, hf⟩, hxV, hVU⟩ := hbasis hxU
  subst hf
  exact ⟨f, hxV, hVU⟩

/-- Elements `g x` with `x ∈ D(g x)` for every prime `x` generate the unit ideal. -/
private theorem span_range_eq_top_of_mem_basicOpen {R : Type u} [CommRing R]
    {g : PrimeSpectrum R → R} (hmem : ∀ x, x ∈ PrimeSpectrum.basicOpen (g x)) :
    Ideal.span (Set.range g) = ⊤ := by
  rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff, eq_top_iff]
  intro x _
  simp only [TopologicalSpace.Opens.mem_iSup]
  exact ⟨x, hmem x⟩

/-- If the `f i` generate the unit ideal, every prime lies in some `D(f i)`. -/
private theorem exists_mem_basicOpen_of_span_eq_top {R : Type u} [CommRing R] {ι : Type u}
    {f : ι → R} (hspan : Ideal.span (Set.range f) = ⊤) (x : PrimeSpectrum R) :
    ∃ i, x ∈ PrimeSpectrum.basicOpen (f i) := by
  rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff] at hspan
  have hx : x ∈ (⨆ i, PrimeSpectrum.basicOpen (f i)) := by rw [hspan]; trivial
  exact TopologicalSpace.Opens.mem_iSup.mp hx

/-- The sheaf-side local freeness of `M~`
(Definition 2, arbitrary open neighbourhoods) is equivalent to local freeness
witnessed only on **standard** opens `D(f)`.

INFORMAL PROOF (rigorous):

(⇐ is trivial): a witness on a standard open `D(f) ∋ x` is in particular an open
neighbourhood `U = D(f)` of `x` with `(M~)|_U ≅ ⨁_I O`, which is exactly the
`Scheme.Modules.IsLocallyFree` requirement.

(⇒): Suppose `M~` is locally free.  Fix `x ∈ Spec R`.  By definition there is an
open neighbourhood `U ∋ x` and `I : Type u` with `φ : (M~)|_U ≅ ⨁_I O|_U`.  The
standard opens form a basis of the Zariski topology
(`PrimeSpectrum.isTopologicalBasis_basic_opens`), so there is `f` with
`x ∈ D(f) ⊆ U`.  Let `j : D(f) ⟶ U` be the induced open immersion (with
`D(f).ι = j ≫ U.ι`).  Restricting `φ` further along `j` (i.e. applying the
restriction functor `restrictFunctor j`, which is a functor hence preserves the
isomorphism `φ`) yields `(M~)|_{D(f)} ≅ (⨁_I O|_U)|_{D(f)}`.  Restriction of the
structure sheaf and of finite/arbitrary direct sums commutes with itself, so
`(⨁_I O|_U)|_{D(f)} ≅ ⨁_I O|_{D(f)} = SheafOfModules.free I` over `D(f)`
(restriction sends the free sheaf on `U` with index `I` to the free sheaf on
`D(f)` with the *same* index `I`; `SheafOfModules.free` is the coproduct of copies
of the unit/structure sheaf and restriction is additive and sends unit to unit).
Composing gives `(M~)|_{D(f)} ≅ SheafOfModules.free I`, the required standard-open
witness, with the same index set `I : Type u`.

use `isTopologicalBasis_basic_opens` /
`Opens.isBasis_iff_nbhd` to extract `f` and `x ∈ D(f) ≤ U`; build the open
immersion factorisation `D(f) ⟶ U`; transport the iso through `restrictFunctor`
(functoriality + `restrictFunctorComp`), and identify
`(SheafOfModules.free I)|_{D(f)} ≅ SheafOfModules.free I` (restriction commutes
with the coproduct defining `free`, sending `unit ↦ unit`). -/
theorem isLocallyFree_iff_basicOpen
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] :
    (AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).IsLocallyFree ↔
      ∀ x : PrimeSpectrum R, ∃ (f : R) (_ : x ∈ PrimeSpectrum.basicOpen f) (I : Type u),
        Nonempty
          ((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
            (specBasicOpen R f).ι ≅ SheafOfModules.free.{u} I) := by
  constructor
  · -- (⇒): shrink each open neighbourhood to a standard open via the basis of basic opens
    intro h x
    obtain ⟨U, hxU, I, ⟨φ⟩⟩ := h x
    obtain ⟨f, hxf, he⟩ := exists_basicOpen_le_of_mem R hxU
    exact ⟨f, hxf, I, ⟨tilde_restrict_free_shrink R M U f he I φ⟩⟩
  · -- (⇐): a standard-open witness IS an open-neighbourhood witness
    intro h x
    obtain ⟨f, hxf, I, hiso⟩ := h x
    exact ⟨specBasicOpen R f, hxf, I, hiso⟩

/-- **Fixed-index transport (reusable).** For ANY fixed index `J`, the restricted tilde
sheaf `(M~)|_{D(f)}` is isomorphic to `free J` iff `(M_f)~` over `Spec R_f` is — the
fixed-index analogue of `tilde_restrict_basicOpen_free_iff_specAway`. Proof: transport the
iso across the equivalence `bridge_specAwayEquiv` (mirroring `exists_free_iso_of_equiv` but
with the index `J` held fixed), using `bridge_restrict_free_iso(_inv)` (free ↦ free) and
`bridge_N_iso` (`Φ.functor.obj ((M~)|_{D(f)}) ≅ (M_f)~`). -/
theorem tilde_restrict_basicOpen_fixed_free_iff
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R)
    (J : Type u) :
    Nonempty
        ((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
          (specBasicOpen R f).ι ≅ SheafOfModules.free.{u} J) ↔
      Nonempty
        (AlgebraicGeometry.tilde (R := CommRingCat.of (Localization.Away f))
          (ModuleCat.of (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)) ≅
          SheafOfModules.free.{u} J) :=
  restrict_iso_free_iff_tilde_away_iso_free R M f J

/-- **Fixed-index tilde-dictionary (reusable).** Over any ring `Rf`, `(Mf)~ ≅ free J` for a
fixed index `J` iff `Mf` has an `Rf`-basis indexed by `J`. The fixed-index analogue of
`tilde_free_iff_module_free`: full faithfulness (`tilde.fullyFaithfulFunctor`) +
`tildeFinsupp` turn the sheaf iso into a linear iso `Mf ≃ₗ (J →₀ Rf)`, which is a `J`-basis
via `Finsupp.basisSingleOne` + `Module.Basis.map`. -/
theorem tilde_fixed_free_iff_basis
    (Rf : Type u) [CommRing Rf] (Mf : Type u) [AddCommGroup Mf] [Module Rf Mf]
    (J : Type u) :
    Nonempty
        (AlgebraicGeometry.tilde (R := CommRingCat.of Rf) (ModuleCat.of Rf Mf) ≅
          SheafOfModules.free.{u} J) ↔
      Nonempty (Module.Basis J Rf Mf) :=
  tilde_iso_free_iff_nonempty_basis Rf Mf J

/-- On `D(f)`, the restricted
sheaf is isomorphic to a free sheaf on a **finite** index set `I` iff `M_f` is
finite free (free *and* finitely generated) over `R_f`.

INFORMAL PROOF: identical to Helper 1, additionally tracking finiteness of the
index set.  `Module.Free` + `Module.Finite` over `R_f` is equivalent to having a
*finite* basis `Fin n` (`Module.finBasis`, `Module.Finite.of_basis`,
`Module.Free.of_basis`); under the tilde dictionary a finite index set `I` on the
sheaf side matches exactly a finite basis on the algebra side.  Concretely, the
same `(M~)|_{D(f)} ≅ (M_f)~` identification plus `tilde.fullyFaithfulFunctor` and
`tildeFinsupp` carries a finite-`I` free sheaf to a finite-rank free module and
back.  reuse Helper 1's `(M~)|_{D(f)} ≅ (M_f)~` bridge; the only
addition is `Finite I ↔ Module.Finite R_f M_f` for the matching basis. -/
theorem tilde_restrict_basicOpen_finiteFree_iff
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R) :
    (∃ (I : Type u) (_ : Finite I), Nonempty
        ((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
          (specBasicOpen R f).ι ≅ SheafOfModules.free.{u} I)) ↔
      (Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) ∧
        Module.Finite (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)) := by
  constructor
  · rintro ⟨I, hI, hiso⟩
    rw [tilde_restrict_basicOpen_fixed_free_iff R M f I,
      tilde_fixed_free_iff_basis] at hiso
    obtain ⟨b⟩ := hiso
    exact ⟨Module.Free.of_basis b, Module.Finite.of_basis b⟩
  · rintro ⟨hfree, hfin⟩
    refine ⟨Module.Free.ChooseBasisIndex (Localization.Away f)
        (LocalizedModule (Submonoid.powers f) M), inferInstance, ?_⟩
    rw [tilde_restrict_basicOpen_fixed_free_iff R M f, tilde_fixed_free_iff_basis]
    exact ⟨Module.Free.chooseBasis _ _⟩

/-- The finite-rank sheaf-side
local freeness of `M~` is equivalent to a finite-index witness on standard opens.
INFORMAL PROOF: identical to Helper 2; restriction along `D(f) ⟶ U` preserves the
finite index set `I`, since the index is unchanged by restriction of the free
sheaf. -/
theorem isFiniteLocallyFree_iff_basicOpen
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] :
    (AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).IsFiniteLocallyFree ↔
      ∀ x : PrimeSpectrum R, ∃ (f : R) (_ : x ∈ PrimeSpectrum.basicOpen f) (I : Type u)
        (_ : Finite I),
        Nonempty
          ((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
            (specBasicOpen R f).ι ≅ SheafOfModules.free.{u} I) := by
  constructor
  · -- (⇒): shrink each open neighbourhood to a standard open, carrying `Finite I`
    intro h x
    obtain ⟨U, hxU, I, hIfin, ⟨φ⟩⟩ := h x
    obtain ⟨f, hxf, he⟩ := exists_basicOpen_le_of_mem R hxU
    exact ⟨f, hxf, I, hIfin, ⟨tilde_restrict_free_shrink R M U f he I φ⟩⟩
  · -- (⇐): a standard-open witness IS an open-neighbourhood witness
    intro h x
    obtain ⟨f, hxf, I, hIfin, hiso⟩ := h x
    exact ⟨specBasicOpen R f, hxf, I, hIfin, hiso⟩

/-- On `D(f)`, the restricted sheaf is
isomorphic to the rank-`r` free sheaf `⨁_{Fin r} O` iff `M_f` has an `R_f`-basis
indexed by `Fin r`.  INFORMAL PROOF: Helper 1 with the fixed index set
`I = ULift (Fin r)`; `tildeFinsupp` and full faithfulness give
`(M~)|_{D(f)} ≅ ⨁_{Fin r} O ↔ M_f ≅ (Fin r →₀ R_f)`, i.e. `Nonempty (Basis (Fin r) R_f M_f)`.
(`ULift (Fin r)` vs `Fin r` indexing differ only by the `Equiv` `ULift.equiv`,
which `SheafOfModules.freeMap`/`Basis.reindex` absorb.) -/
theorem tilde_restrict_basicOpen_rank_iff
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (f : R) (r : ℕ) :
    Nonempty
        ((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
          (specBasicOpen R f).ι ≅ SheafOfModules.free.{u} (ULift (Fin r))) ↔
      Nonempty (Module.Basis (Fin r) (Localization.Away f)
        (LocalizedModule (Submonoid.powers f) M)) := by
  rw [tilde_restrict_basicOpen_fixed_free_iff R M f (ULift (Fin r)),
    tilde_fixed_free_iff_basis (Localization.Away f)
      (LocalizedModule (Submonoid.powers f) M) (ULift (Fin r))]
  exact ⟨fun ⟨b⟩ => ⟨b.reindex Equiv.ulift⟩, fun ⟨b⟩ => ⟨b.reindex Equiv.ulift.symm⟩⟩

/-- Rank-`r` sheaf-side local freeness
of `M~` is equivalent to a rank-`r` witness on standard opens.  INFORMAL PROOF:
identical to Helper 2 with the fixed index set `ULift (Fin r)`. -/
theorem isFiniteLocallyFreeOfRank_iff_basicOpen
    (R : Type u) [CommRing R] (M : Type u) [AddCommGroup M] [Module R M] (r : ℕ) :
    (AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).IsFiniteLocallyFreeOfRank
        r ↔
      ∀ x : PrimeSpectrum R, ∃ (f : R) (_ : x ∈ PrimeSpectrum.basicOpen f),
        Nonempty
          ((AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).restrict
            (specBasicOpen R f).ι ≅ SheafOfModules.free.{u} (ULift (Fin r))) := by
  constructor
  · -- (⇒): shrink each open neighbourhood to a standard open (fixed index `ULift (Fin r)`)
    intro h x
    obtain ⟨U, hxU, ⟨φ⟩⟩ := h x
    obtain ⟨f, hxf, he⟩ := exists_basicOpen_le_of_mem R hxU
    exact ⟨f, hxf, ⟨tilde_restrict_free_shrink R M U f he (ULift (Fin r)) φ⟩⟩
  · -- (⇐): a standard-open witness IS an open-neighbourhood witness
    intro h x
    obtain ⟨f, hxf, hiso⟩ := h x
    exact ⟨specBasicOpen R f, hxf, hiso⟩

/-!
## The main statements

Stacks Lemma 28.21.1 (Tag 05JM): the quasi-coherent sheaf `F = M~` is a (finite)
locally free `O_X`-module if and only if `M` is a (finite) locally free
`R`-module.

Each of the three biconditionals below reduces to its two helper lemmas above, the affine
kernel and basis shrinking, by pure covering combinatorics
(`PrimeSpectrum.iSup_basicOpen_eq_top_iff`).
-/

/-- **Statement 1 (locally free case).** `M~` is a locally free `O_X`-module if
and only if `M` is a locally free `R`-module.

PROOF (complete modulo the two helper lemmas): rewrite the sheaf side via
`isLocallyFree_iff_basicOpen`, then:
* (⇒) For each point `x` choose (by `choose`) a standard open `D(g x) ∋ x` on which
  the sheaf is free; the family `(g x)` covers `Spec R` (each `x ∈ D(g x)`), so
  `Ideal.span (range g) = ⊤` by `iSup_basicOpen_eq_top_iff`, and by Helper 1 each
  `M_{g x}` is free — giving `Module.IsLocallyFree R M` with `ι := PrimeSpectrum R`.
* (⇐) Given a covering family `f : ι → R` with span `⊤` and each `M_{f i}` free:
  for any `x`, the cover gives `i` with `x ∈ D(f i)`, and Helper 1 makes the sheaf
  free on `D(f i)`. -/
@[stacks 05JM]
theorem tilde_isLocallyFree_iff (R : Type u) [CommRing R] (M : Type u)
    [AddCommGroup M] [Module R M] :
    (AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).IsLocallyFree ↔
      Module.IsLocallyFree R M := by
  rw [isLocallyFree_iff_basicOpen]
  constructor
  · -- (⇒) collect the per-point trivializing standard opens into a covering family
    intro h
    choose g hmem I hiso using h
    refine ⟨PrimeSpectrum R, g, ?_, ?_⟩
    · exact span_range_eq_top_of_mem_basicOpen hmem
    · intro x
      exact (tilde_restrict_basicOpen_free_iff R M (g x)).mp ⟨I x, hiso x⟩
  · -- (⇐) any point lies in some D(f i); Helper 1 trivializes the sheaf there
    rintro ⟨ι, f, hspan, hfree⟩ x
    obtain ⟨i, hi⟩ := exists_mem_basicOpen_of_span_eq_top hspan x
    obtain ⟨I, hI⟩ := (tilde_restrict_basicOpen_free_iff R M (f i)).mpr (hfree i)
    exact ⟨f i, hi, I, hI⟩

/-- **Statement 2 (finite locally free case).** `M~` is a finite locally free
`O_X`-module if and only if `M` is a finite locally free `R`-module.

PROOF (complete modulo `isFiniteLocallyFree_iff_basicOpen` and
`tilde_restrict_basicOpen_finiteFree_iff`): same covering combinatorics as
Statement 1, now carrying the finiteness witness `Finite I` through the helpers. -/
@[stacks 05JM, ega "III 7.9.1" "M proj f.t. <=> M~ l.f."]
theorem tilde_isFiniteLocallyFree_iff (R : Type u) [CommRing R] (M : Type u)
    [AddCommGroup M] [Module R M] :
    (AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).IsFiniteLocallyFree ↔
      Module.IsFiniteLocallyFree R M := by
  rw [isFiniteLocallyFree_iff_basicOpen]
  constructor
  · -- (⇒) collect trivializing standard opens (with finite index) into a cover
    intro h
    choose g hmem I hIfin hiso using h
    refine ⟨PrimeSpectrum R, g, ?_, ?_⟩
    · exact span_range_eq_top_of_mem_basicOpen hmem
    · intro x
      exact (tilde_restrict_basicOpen_finiteFree_iff R M (g x)).mp ⟨I x, hIfin x, hiso x⟩
  · -- (⇐) any point lies in some D(f i); finite-rank Helper trivializes there
    rintro ⟨ι, f, hspan, hfree⟩ x
    obtain ⟨i, hi⟩ := exists_mem_basicOpen_of_span_eq_top hspan x
    obtain ⟨I, hIfin, hI⟩ :=
      (tilde_restrict_basicOpen_finiteFree_iff R M (f i)).mpr (hfree i)
    exact ⟨f i, hi, I, hIfin, hI⟩

/-- **Optional rank-`r` variant.** `M~` is a finite locally free `O_X`-module of
rank `r` if and only if `M` is a finite locally free `R`-module of rank `r`.

PROOF (complete modulo `isFiniteLocallyFreeOfRank_iff_basicOpen` and
`tilde_restrict_basicOpen_rank_iff`): same covering combinatorics, with the fixed
index set `ULift (Fin r)` carried through the helpers. -/
theorem tilde_isFiniteLocallyFreeOfRank_iff (R : Type u) [CommRing R] (M : Type u)
    [AddCommGroup M] [Module R M] (r : ℕ) :
    (AlgebraicGeometry.tilde (R := CommRingCat.of R) (ModuleCat.of R M)).IsFiniteLocallyFreeOfRank
        r ↔
      Module.IsFiniteLocallyFreeOfRank R M r := by
  rw [isFiniteLocallyFreeOfRank_iff_basicOpen]
  constructor
  · -- (⇒) collect rank-r trivializing standard opens into a cover
    intro h
    choose g hmem hiso using h
    refine ⟨PrimeSpectrum R, g, ?_, ?_⟩
    · exact span_range_eq_top_of_mem_basicOpen hmem
    · intro x
      exact (tilde_restrict_basicOpen_rank_iff R M (g x) r).mp (hiso x)
  · -- (⇐) any point lies in some D(f i); rank-r Helper trivializes there
    rintro ⟨ι, f, hspan, hbasis⟩ x
    obtain ⟨i, hi⟩ := exists_mem_basicOpen_of_span_eq_top hspan x
    exact ⟨f i, hi, (tilde_restrict_basicOpen_rank_iff R M (f i) r).mpr (hbasis i)⟩
