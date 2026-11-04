module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import StacksFrontier.Algebra.Homology.SpectralSequence.Grothendieck
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionRelativeLeray.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.ShortComplexOfDirectImages
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.SheafifiedCohomologyPresheaf
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The relative Leray spectral sequence

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of ringed spaces. For every bounded below complex
`M` of `𝒪_X`-modules, and in particular for every `𝒪_X`-module `ℱ`, there is a spectral sequence

`E₂^{p,q} = R^p g_*(R^q f_* ℱ) ⟹ R^{p+q}(g ∘ f)_* ℱ`,

which is [Stacks, Tag 01F6]. It is the Grothendieck spectral sequence of
[Stacks, Tag 015N] for the pair `(f_*, g_*)`, and the only thing the pair needs in order to
qualify is that `f_*` carries injective `𝒪_X`-modules to objects right acyclic for `g_*` — the
acyclicity step of the proof of [Stacks, Tag 01F5]. That step is what this file supplies, after
which both [Stacks, Tag 01F5] and [Stacks, Tag 01F6] are instantiations.

Acyclicity costs nothing beyond flasqueness: `f_* I` is flasque for an injective `I`
([Stacks, Tag 01EX] part (2), run from [Stacks, Tag 01EA]) and a flasque module has vanishing
positive higher direct images along any morphism ([Stacks, Tag 09T0]). **No hypothesis is
imposed on `f` or on `g`.**

## Main results

* `Stacks.Cohomology.RelativeLeray.rightAcyclic_modulePushforward_obj_of_injective`:
  `f_* I` is right acyclic for `g_*` whenever `I` is an injective `𝒪_X`-module. This is the
  acyclicity step of the proof of [Stacks, Tag 01F5] and the hypothesis of
  [Stacks, Tag 015N] for the pair `(f_*, g_*)`.
* `Stacks.Cohomology.RelativeLeray.derivedPushforwardPlusCompIso`: **[Stacks, Tag 01F5]** —
  `R(g ∘ f)_* ≅ Rf_* ⋙ Rg_*` as functors `D⁺(X) ⥤ D⁺(Z)`, the canonical comparison of
  [Stacks, Tag 05T2] inverted.
* `Stacks.Cohomology.RelativeLeray.exists_spectralSequence_relativeLeray`:
  **[Stacks, Tag 01F6] for a bounded below complex** — the sentence *"there is a version for
  bounded below complexes of `𝒪_X`-modules"*.
* `Stacks.Cohomology.RelativeLeray.exists_spectralSequence_relativeLeray_obj`:
  **[Stacks, Tag 01F6] for a module**, the statement as the source gives it.

## Implementation notes

**What the tag asks for and is not here: functoriality in `ℱ`.** [Stacks, Tag 01F6] adds *"this
spectral sequence is functorial in `ℱ`"*, and nothing below delivers that. The obstruction is in
the shape of the input, not in the geometry: [Stacks, Tag 015N] is an *existence* statement
producing a filtered complex and a spectral sequence one object at a time, so no functorial datum
can be extracted from it. The vocabulary for the functorial form is
`Stacks.Cohomology.Leray.FunctorialFirstQuadrantAbutsTo`, whose `gradedIso_naturality` field is
exactly what is missing. The `@[stacks 01F6 ...]` attributes below therefore carry a clause
naming what they cover.

**The convergence convention is [Stacks, Tag 015N]'s own**, i.e. [Stacks, Tag 012M]'s: a spectral
sequence "converging to `H^*(K)`" is one presented by its pages as the subquotients
`Z_r^{p,q}/D_r^{p,q}` of a filtered complex `K`, together with boundedness, finiteness of the
induced filtration on each `H^n(K)`, vanishing of `d_r` for `r ≫ 0`, and the stable-cycle and
stable-boundary equalities (012S) and (012T). The conclusions below are
[Stacks, Tag 015N]'s verbatim with three substitutions: `F := f_*`, `G := g_*`, and the abutment
rewritten from `H^n(R(g_* ∘ f_*)(M))` to `H^n(R(g ∘ f)_*(M))` along
[Stacks, Tag 0097] (1) (`Stacks.Cohomology.RelativeMayerVietoris.pushforwardCompIso`).

**The abutment datum `CochainComplex.Filtered.firstQuadrantAbutment` cannot be fed from here,
and that is a property of [Stacks, Tag 015N]'s statement.**
`CochainComplex.Filtered.firstQuadrantAbutment` needs the filtration of `K` to be *first
quadrant* — `F⁰K^n = K^n` for every `n` and `F^pK^n = 0` for `p > n`. The filtration
[Stacks, Tag 015N] produces does have that property (it is the second filtration of the double
complex `g_*(I)`, which lives in the first quadrant), but its *statement* records only
`Filtration.IsDegreewiseFinite` and *some* `a ≤ b` with `F^aH^n = H^n` and `F^bH^n = 0`. So the
`FirstQuadrantAbutment` of a relative Leray spectral sequence — and hence the five-term exact
sequence of [Stacks, Tag 01F2] for it — is owed by [Stacks, Tag 015N], not by this file.

**The module-level statement is the complex-level one at `ℱ[0]`, with nothing in between.**
`Functor.rightDerivedPlus i` is by definition `singleFunctor 0 ⋙ rightDerivedFunctorPlus ⋙
homologyFunctor i`, so both the `E₂` term and the abutment of
`exists_spectralSequence_relativeLeray_obj` are *definitionally* the complex-level ones at
`M := ℱ[0]`; the proof is a single application. A consumer wanting Mathlib's `ℕ`-indexed
`Functor.rightDerived` instead of `Functor.rightDerivedPlus` gets it from
`Stacks.DerivedIndexing.rightDerivedIso`.

**Relation to the closed-immersion case.**
`Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray.rightDerivedPushforwardCompIso` is the
*degeneration* `Rⁿ(i ≫ f)_* ≅ i_* ⋙ Rⁿ f_*` for `i` a closed immersion — a degreewise splitting,
which needs exactness of `i_*` and is strictly more than the spectral sequence; nothing here
replaces it. Its acyclicity input,
`…ClosedImmersionRelativeLeray.rightAcyclic_pushforward_pushforward_obj_of_injective`, *is*
subsumed by `rightAcyclic_modulePushforward_obj_of_injective` below: its statement is recovered
verbatim by applying this one at `Stacks.Cohomology.AffineBase.asRingedSpaceHom` of each
morphism, with no bridging lemma, since `modulePushforward (asRingedSpaceHom f)` *is*
`AlgebraicGeometry.Scheme.Modules.pushforward f`. It is not folded away here because this file
imports that one, so folding would invert the import direction; the subsumption is recorded for
that directory's next editor.

**Not an instance of [Stacks, Tag 0D5T] or [Stacks, Tag 0D6E].** Those files hold
`Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` for the *unbounded* derived category, conditional on
`StacksTag0D5T.PushforwardComputesDerived`, which asks for invertibility at every **K-injective
complex**. The lemma here is about **injective objects**, and nothing bridges the two, so it
cannot discharge that hypothesis.

## References

* [Stacks Project, Tag 01F5](https://stacks.math.columbia.edu/tag/01F5)
* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 05T2](https://stacks.math.columbia.edu/tag/05T2)
* [Stacks Project, Tag 09T0](https://stacks.math.columbia.edu/tag/09T0)
* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.RelativeLeray

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-! ### The subobject lattice of `Mod(𝒪_Z)`, at a declared type

The conclusions below are [Stacks, Tag 015N]'s, so they mention `⊓`, `⊔`, `⊤` and `⊥` of
`CategoryTheory.Subobject` at `Mod(𝒪_Z)`. Mathlib builds those from `HasPullbacks`, `HasImages`,
`HasBinaryCoproducts`, `HasInitial` and `InitialMonoClass`, and **with none of the five declared
the lattice is unreachable at this spelling**: `Max (Subobject B)` is `synthInstanceFailed` and
`Bot (Subobject B)` a typeclass timeout — not a cost, since raising the heartbeats twenty-fold
changes neither — while the very same searches succeed with no help at all for an abstract
`[Abelian C]`, and each of the five resolves by `inferInstance` here on its own.

The five are therefore declared at the type the conclusion needs. They are *jointly*, not
individually, load-bearing: with all five declared `Max`, `Min`, `Top` and `Bot` all
resolve; dropping any single one still resolves (5 of 5); keeping only one never resolves
(5 of 5). So no one of them is necessary and no one of them is sufficient, which is why an
arbitrary minimal subset is not chosen here. There is no mathematics in any of them — this is
the "only a declared return type works" cure with nothing added. -/

/-- The category of `𝒪_Z`-modules on a ringed space `Z` has images. -/
local instance hasImagesRingedSpaceModules (Z : AlgebraicGeometry.RingedSpace.{u, u}) :
    HasImages (SheafOfModules.{u} (structureSheafRing Z)) := inferInstance

/-- The category of `𝒪_Z`-modules on a ringed space `Z` has binary coproducts. -/
local instance hasBinaryCoproductsRingedSpaceModules
    (Z : AlgebraicGeometry.RingedSpace.{u, u}) :
    HasBinaryCoproducts (SheafOfModules.{u} (structureSheafRing Z)) := inferInstance

/-- The category of `𝒪_Z`-modules on a ringed space `Z` has pullbacks. -/
local instance hasPullbacksRingedSpaceModules (Z : AlgebraicGeometry.RingedSpace.{u, u}) :
    HasPullbacks (SheafOfModules.{u} (structureSheafRing Z)) := inferInstance

/-- The category of `𝒪_Z`-modules on a ringed space `Z` has an initial object. -/
local instance hasInitialRingedSpaceModules (Z : AlgebraicGeometry.RingedSpace.{u, u}) :
    HasInitial (SheafOfModules.{u} (structureSheafRing Z)) := inferInstance

/-- In the category of `𝒪_Z`-modules on a ringed space `Z`, every morphism out of an initial
object is a monomorphism. -/
local instance initialMonoClassRingedSpaceModules (Z : AlgebraicGeometry.RingedSpace.{u, u}) :
    InitialMonoClass (SheafOfModules.{u} (structureSheafRing Z)) := inferInstance

variable {X Y Z : AlgebraicGeometry.RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-! ### The acyclicity step of [Stacks, Tag 01F5] -/

/-- **`f_* I` is right acyclic for `g_*` when `I` is injective.** For morphisms of ringed spaces
`f : X ⟶ Y` and `g : Y ⟶ Z` and an injective `𝒪_X`-module `I`, every positive higher direct image
of `f_* I` along `g` vanishes, and `f_* I` therefore computes `Rg_*`.

**No hypothesis on `f` or on `g`.** This is the one step the proof of [Stacks, Tag 01F5] has to
make — *"It remains to show that `f_*ℐ` is `g_*`-acyclic"* — and it is also exactly the
hypothesis `hFG` of the Grothendieck spectral sequence [Stacks, Tag 015N] for the pair
`(f_*, g_*)`. The module `f_* I` is flasque by [Stacks, Tag 01EX] part (2), and a flasque module
has vanishing positive higher direct images along any morphism by [Stacks, Tag 09T0]; right
acyclicity is read off the `ℕ`-indexed right derived functors by
`Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat`.

**No `@[stacks 01F5]` attribute**: this is a step in that tag's proof, not its statement, which is
`derivedPushforwardPlusCompIso` below. -/
@[ega "0 12.2.4" "partial"]
theorem rightAcyclic_modulePushforward_obj_of_injective
    (I : SheafOfModules.{u} (structureSheafRing X)) (hI : Injective I) :
    (modulePushforward g).rightAcyclic ((modulePushforward f).obj I) := by
  rw [Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat]
  intro n hn
  refine (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ n _).2 ?_
  exact @Stacks.Cohomology.FlasquePushforward.isZero_rightDerivedPlus_modulePushforward_of_isFlasque
    _ _ g _
    (Stacks.AlgebraicGeometry.ClosedImmersionRelativeLeray.isFlasque_toSheaf_modulePushforward
      f I hI)
    (n : ℤ) (by exact_mod_cast hn)

/-! ### [Stacks, Tag 01F5]: the total derived functor of a composite -/

/-- **[Stacks, Tag 01F5]: `R(g ∘ f)_* ≅ Rf_* ⋙ Rg_*` as functors `D⁺(X) ⥤ D⁺(Z)`**, for
arbitrary morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`. No hypothesis.

The isomorphism is the **canonical** comparison of [Stacks, Tag 05T2],
`CategoryTheory.Functor.rightDerivedFunctorPlusComp`, inverted — not an arbitrary
identification — precomposed with the undeived composition formula
[Stacks, Tag 0097] (1) for `(g ∘ f)_* = g_* ∘ f_*`. Invertibility is the criterion of
[Stacks, Tag 015M], whose hypothesis is discharged by
`rightAcyclic_modulePushforward_obj_of_injective`. -/
@[stacks 01F5]
def derivedPushforwardPlusCompIso :
    (modulePushforward (f ≫ g)).rightDerivedFunctorPlus ≅
      (modulePushforward f).rightDerivedFunctorPlus ⋙
        (modulePushforward g).rightDerivedFunctorPlus :=
  have _ : IsIso (Functor.rightDerivedFunctorPlusComp
      (modulePushforward f) (modulePushforward g)) :=
    Stacks.Cohomology.AcyclicCollapse.isIso_derivedComposition _ _
      (fun I hI => rightAcyclic_modulePushforward_obj_of_injective f g I hI)
  Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedFunctorPlusNatIsoOfIso
      (Stacks.Cohomology.RelativeMayerVietoris.pushforwardCompIso f g) ≪≫
    asIso (Functor.rightDerivedFunctorPlusComp
      (modulePushforward f) (modulePushforward g))

/-! ### [Stacks, Tag 01F6]: the relative Leray spectral sequence -/

/-- **[Stacks, Tag 01F6] for a bounded below complex.** For morphisms of ringed spaces
`f : X ⟶ Y` and `g : Y ⟶ Z` and an object `M` of `D⁺(X)` there is a filtered complex `K` of
`𝒪_Z`-modules with `H^n(K) ≅ H^n(R(g ∘ f)_* M)` in every degree, whose filtration is finite in
each degree and whose spectral sequence `E`, presented as in [Stacks, Tag 012M] by its pages
`Z_r^{p,q}/D_r^{p,q}`, has

`E₂^{p,q} ≅ R^p g_*(H^q(Rf_* M))`,

is bounded, induces a finite filtration on each `H^n(K)`, and converges to `H^*(K)`.

This is the source's *"there is a version for bounded below complexes of `𝒪_X`-modules"*, and it
is the primary form: the module statement `exists_spectralSequence_relativeLeray_obj` is this one
at `M := ℱ[0]`. It is [Stacks, Tag 015N] for the pair `(f_*, g_*)`, whose hypothesis is
`rightAcyclic_modulePushforward_obj_of_injective`, with the abutment rewritten from
`H^n(R(g_* ∘ f_*) M)` to `H^n(R(g ∘ f)_* M)` along
`Stacks.Cohomology.RelativeMayerVietoris.pushforwardCompIso`.

**The tag's functoriality in `ℱ` is not included**, which is why the attribute carries a clause;
see the implementation notes. -/
@[stacks 01F6 "the spectral sequence for a bounded below complex, not its functoriality",
  ega "0 12.2.4", sga "4 V 5.4" "ringed spaces"]
theorem exists_spectralSequence_relativeLeray
    (M : DerivedCategory.Plus (SheafOfModules.{u} (structureSheafRing X))) :
    ∃ K : FilteredObject (CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) ℤᵒᵖ,
      (∀ n : ℤ, Nonempty (K.X.homology n ≅
        (DerivedCategory.Plus.homologyFunctor _ n).obj
          ((modulePushforward (f ≫ g)).rightDerivedFunctorPlus.obj M))) ∧
      K.filtration.IsDegreewiseFinite ∧
      ∀ (Fil : ∀ (_p n : ℤ), Subobject (K.X.X n))
        (_ : ∀ p n : ℤ, Fil p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
        (Zc : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
        (_ : ∀ r p n : ℤ, Zc r p n =
          Fil p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (Fil (p + r) (n + 1)))
        (Dc : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
        (_ : ∀ r p n : ℤ, Dc r p n = Zc (r - 1) (p + 1) n ⊔
          (Subobject.«exists» (K.X.d (n - 1) n)).obj (Zc (r - 1) (p - r + 1) (n - 1)))
        (FH : ∀ (n _p : ℤ), Subobject (K.X.homology n))
        (_ : ∀ n p : ℤ, FH n p =
          imageSubobject (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)),
      ∃ (E : CohomologicalSpectralSequence (SheafOfModules.{u} (structureSheafRing Z)) 0)
        (_ : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
          cokernel (Subobject.ofLE _ _ (inf_le_right : Dc r p n ⊓ Zc r p n ≤ Zc r p n))),
        (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
          ((modulePushforward g).rightDerivedPlus p).obj
            ((DerivedCategory.Plus.homologyFunctor _ q).obj
              ((modulePushforward f).rightDerivedFunctorPlus.obj M)))) ∧
        (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 0).X (p, n - p))}.Finite) ∧
        (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥) ∧
        (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
          (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
        (∀ p n : ℤ,
          IsGLB (Set.range fun r : ℕ =>
              Fil p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (Fil (p + r) (n + 1)) ⊔
                Fil (p + 1) n)
            (kernelSubobject (K.X.d n (n + 1)) ⊓ Fil p n ⊔ Fil (p + 1) n) ∧
          IsLUB (Set.range fun r : ℕ =>
              Fil p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (Fil (p - r) (n - 1)) ⊔
                Fil (p + 1) n)
            (imageSubobject (K.X.d (n - 1) n) ⊓ Fil p n ⊔ Fil (p + 1) n)) := by
  obtain ⟨K, hK, hfin, hrest⟩ :=
    CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp
      (modulePushforward f) (modulePushforward g)
      (fun I hI => rightAcyclic_modulePushforward_obj_of_injective f g I hI) M
  refine ⟨K, fun n => ?_, hfin, hrest⟩
  obtain ⟨e⟩ := hK n
  exact ⟨e ≪≫ (DerivedCategory.Plus.homologyFunctor _ n).mapIso
    ((Stacks.Cohomology.HigherDirectImagePresheaf.rightDerivedFunctorPlusNatIsoOfIso
        (Stacks.Cohomology.RelativeMayerVietoris.pushforwardCompIso f g)).app M).symm⟩

/-- **[Stacks, Tag 01F6], the relative Leray spectral sequence for a module.** For morphisms of
ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z` and an `𝒪_X`-module `ℱ` there is a spectral sequence
with

`E₂^{p,q} ≅ R^p g_*(R^q f_* ℱ)`

converging to `R^{p+q}(g ∘ f)_* ℱ`, in the presentation and convergence convention of
[Stacks, Tag 012M] and [Stacks, Tag 015N]. No hypothesis on `f`, on `g` or on `ℱ`.

This is `exists_spectralSequence_relativeLeray` at the complex `ℱ[0]`: the `E₂` term and the
abutment of that statement are *definitionally* `R^p g_*(R^q f_* ℱ)` and `R^n(g ∘ f)_* ℱ` there,
because `Functor.rightDerivedPlus i` is `singleFunctor 0 ⋙ rightDerivedFunctorPlus ⋙
homologyFunctor i` by definition.

**The tag's functoriality in `ℱ` is not included**; see the implementation notes. -/
@[stacks 01F6 "the spectral sequence for a module, not its functoriality"]
theorem exists_spectralSequence_relativeLeray_obj
    (F : SheafOfModules.{u} (structureSheafRing X)) :
    ∃ K : FilteredObject (CochainComplex (SheafOfModules.{u} (structureSheafRing Z)) ℤ) ℤᵒᵖ,
      (∀ n : ℤ, Nonempty (K.X.homology n ≅
        ((modulePushforward (f ≫ g)).rightDerivedPlus n).obj F)) ∧
      K.filtration.IsDegreewiseFinite ∧
      ∀ (Fil : ∀ (_p n : ℤ), Subobject (K.X.X n))
        (_ : ∀ p n : ℤ, Fil p n = Subobject.mk ((K.filtration.ι.app (op p)).f n))
        (Zc : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
        (_ : ∀ r p n : ℤ, Zc r p n =
          Fil p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (Fil (p + r) (n + 1)))
        (Dc : ∀ (_r _p n : ℤ), Subobject (K.X.X n))
        (_ : ∀ r p n : ℤ, Dc r p n = Zc (r - 1) (p + 1) n ⊔
          (Subobject.«exists» (K.X.d (n - 1) n)).obj (Zc (r - 1) (p - r + 1) (n - 1)))
        (FH : ∀ (n _p : ℤ), Subobject (K.X.homology n))
        (_ : ∀ n p : ℤ, FH n p =
          imageSubobject (HomologicalComplex.homologyMap (K.filtration.ι.app (op p)) n)),
      ∃ (E : CohomologicalSpectralSequence (SheafOfModules.{u} (structureSheafRing Z)) 0)
        (_ : ∀ (r p q n : ℤ) (hr : 0 ≤ r) (_ : n = p + q), (E.page r hr).X (p, q) ≅
          cokernel (Subobject.ofLE _ _ (inf_le_right : Dc r p n ⊓ Zc r p n ≤ Zc r p n))),
        (∀ p q : ℤ, Nonempty ((E.page 2 zero_le_two).X (p, q) ≅
          ((modulePushforward g).rightDerivedPlus p).obj
            (((modulePushforward f).rightDerivedPlus q).obj F))) ∧
        (∀ n : ℤ, {p : ℤ | ¬ IsZero ((E.page 0).X (p, n - p))}.Finite) ∧
        (∀ n : ℤ, ∃ a b : ℤ, a ≤ b ∧ FH n a = ⊤ ∧ FH n b = ⊥) ∧
        (∀ p q : ℤ, ∃ b : ℤ, ∀ (r : ℤ) (hr : 0 ≤ r), b ≤ r →
          (E.page r hr).d (p, q) (p + r, q - r + 1) = 0) ∧
        (∀ p n : ℤ,
          IsGLB (Set.range fun r : ℕ =>
              Fil p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (Fil (p + r) (n + 1)) ⊔
                Fil (p + 1) n)
            (kernelSubobject (K.X.d n (n + 1)) ⊓ Fil p n ⊔ Fil (p + 1) n) ∧
          IsLUB (Set.range fun r : ℕ =>
              Fil p n ⊓ (Subobject.«exists» (K.X.d (n - 1) n)).obj (Fil (p - r) (n - 1)) ⊔
                Fil (p + 1) n)
            (imageSubobject (K.X.d (n - 1) n) ⊓ Fil p n ⊔ Fil (p + 1) n)) :=
  exists_spectralSequence_relativeLeray f g
    ((DerivedCategory.Plus.singleFunctor _ 0).obj F)

end Stacks.Cohomology.RelativeLeray

end
