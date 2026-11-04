module

public import StacksFrontier.Algebra.Homology.CartanEilenbergResolutions
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplex
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Kernel
import StacksCore.Tactic.StacksAttribute

/-!
# The images and kernels of a bounded complex of finite locally free `𝒪_X`-modules

Let `X` be a scheme and let `ℰ^a ⟶ ⋯ ⟶ ℰ^b` be a bounded complex of finite locally free
`𝒪_X`-modules whose cohomology sheaves are perfect of tor dimension at most one.  Then every
image and every kernel of a differential of the complex is again finite locally free.  This is
the sheaf-level content of [Stacks, Tag 0F8J], and it is proved here by the source's descending
induction on the degree, alternating the two short exact sequences

  `0 ⟶ Im(d^{n-1}) ⟶ Ker(d^n) ⟶ H^n(ℰ) ⟶ 0`,   `0 ⟶ Ker(d^n) ⟶ ℰ^n ⟶ Im(d^n) ⟶ 0`.

The induction runs *downwards*: above the top degree the first differential out of a term is
zero, so the kernel there is the whole term; and from `Ker(d^{n+1})` the first sequence gives
`Im(d^n)` and then the second gives `Ker(d^n)`.

## Main results

* `Stacks.FiniteLocallyFree.isFiniteLocallyFree_Z` and
  `Stacks.FiniteLocallyFree.isFiniteLocallyFree_B`: the induction, run against an abstract
  degreewise presentation of the complex.
* `Stacks.FiniteLocallyFree.isFiniteLocallyFree_cycles` and
  `Stacks.FiniteLocallyFree.isFiniteLocallyFree_kernel_homologyπ`: the conclusion stated for the
  complex's own cycles `Ker(d^n)` and for the image `Im(d^{n-1})` into degree `n`.
* `Stacks.FiniteLocallyFree.boundedComplexSplitting`: the assembly of the two sequences into
  `Stacks.Chow.BoundedComplexSplitting`, the degreewise exactness datum that the Chern class of
  a complex is defined against.  This is the datum whose existence the consumers of
  `Stacks.Chow.BoundedComplexSplitting` had to assume.
* `Stacks.FiniteLocallyFree.nonempty_boundedComplexSplitting`: the same, with the hypotheses
  stated for `P.homology n` -- the form consumers hold them in.

## Implementation notes

**The degree bookkeeping, and why no object is transported along an equality.**  The image of a
differential *into* degree `n` is `Im(d^{n-1})`, so a naive family indexed by `n` is
`Abelian.image (P.d (n - 1) n)`; the degreewise sequence then needs a map
`ℰ^n ⟶ Abelian.image (P.d (n + 1 - 1) (n + 1))`, whose target is an image of a differential
whose *source object* is `P.X (n + 1 - 1)` rather than `P.X n`.  Supplying that map means
transporting along `n + 1 - 1 = n`, which puts an `eqToHom` into the data of the construction and
is exactly what makes such a definition unusable downstream.

Nothing of the sort happens here, because the presentation used is not that one.  The two
sequences are taken from `StacksDraft.CartanEilenbergResolutions.cochainGluingData`, whose family of
images is `Ker(ℰ-cycles ⟶ ℰ-cohomology)` in degree `n` — the kernel of
`HomologicalComplex.homologyπ`, which *is* the image of the differential into degree `n` and, as
that file's own note says, is indexed by `n` with no subtraction.  Every map it supplies comes
from a two-index piece of Mathlib's `HomologicalComplex` API (`toCycles i j`,
`toCycles_comp_homologyπ i j`, `homologyIsCokernel`), so the shifted index is always an
*instantiation* of a universally quantified degree and never an arithmetic rewrite.  The one
place a degree equality is unavoidable is
`Stacks.FiniteLocallyFree.isZero_B_of_isZero_X`, which is therefore stated over an arbitrary
`p + 1 = q` and `subst`s it; its conclusion is a `Prop`, so the substitution never enters the
data of the splitting.

**Which finite-local-freeness predicate.**  Every statement is about
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree` at `X.ringCatSheaf` — the spelling that
`Stacks.Chow.BoundedComplexSplitting`'s own fields use, and the one the two short exact sequence
results in `StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Kernel` are stated for, so no bridge
to either of the other two predicates of that name is needed.

**The hypotheses are the source's.**  The complex is bounded, its terms are finite locally free,
and each cohomology sheaf is perfect *and* of tor amplitude in `[-1, 0]`.  The tor condition is
carried, not discharged: the second sequence's conclusion is false without it, and perfectness is
what makes the sub-object finitely presented.

## References

* [Stacks Project, Tag 0F8J](https://stacks.math.columbia.edu/tag/0F8J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.PerfectComplexes Stacks.Cohomology.TorAmplitude
open StacksDraft.CartanEilenbergResolutions

universe u

namespace Stacks.FiniteLocallyFree

attribute [local instance] HasDerivedCategory.standard

variable {X : Scheme.{u}} (P : CochainComplex X.Modules ℤ) (G : CochainGluingData P)

/-! ### Degree bookkeeping at the two ends of the range -/

/-- **A vanishing term forces the image out of it to vanish**: `Im(d^p)` is the target of an
epimorphism out of `ℰ^p`.

The target degree `q` is a variable constrained by `p + 1 = q`, not the expression `p + 1`, so
that a caller holding the index `q` instantiates it directly.  The equality is `subst`ed, and
since the conclusion is a `Prop` the substitution does not reach the data of any construction. -/
theorem isZero_B_of_isZero_X (p q : ℤ) (hpq : p + 1 = q) (h : IsZero (P.X p)) :
    IsZero (G.B q) := by
  subst hpq
  have := (G.hA p).epi_g
  exact IsZero.of_epi (G.ee p) h

/-- **A vanishing term forces the image into it to vanish**: `Im(d^{p-1})` is a subobject of
`ℰ^p`, included as `Im(d^{p-1}) ↪ Ker(d^p) ↪ ℰ^p`.  Both degrees here are `p`, so there is no
arithmetic to do. -/
theorem isZero_B_of_isZero_X_self (p : ℤ) (h : IsZero (P.X p)) : IsZero (G.B p) := by
  have := (G.hB p).mono_f
  have := (G.hA p).mono_f
  exact IsZero.of_mono (G.aa p ≫ G.ci p) h

/-- **Above the top degree the kernel is the whole term**: if `ℰ^{p+1}` vanishes then `d^p` does,
so `Ker(d^p) ⟶ ℰ^p` is an isomorphism.  This is what starts the descending induction. -/
theorem isIso_ci_of_isZero_X_succ (p : ℤ) (h : IsZero (P.X (p + 1))) : IsIso (G.ci p) := by
  have := (G.hA p).mono_f
  have hzB : IsZero (G.B (p + 1)) := isZero_B_of_isZero_X_self P G (p + 1) h
  have : Epi (G.ci p) :=
    (ShortComplex.exact_iff_epi _ (hzB.eq_of_tgt _ _)).1 (G.hA p).exact
  exact isIso_of_mono_of_epi _

/-! ### The descending induction -/

/-- **The kernels of the differentials of a bounded-above complex of finite locally free
`𝒪_X`-modules with perfect cohomology of tor dimension at most one are finite locally free.**

This is the source's descending induction.  Above the top degree `b` the kernel is the whole
term, by `Stacks.FiniteLocallyFree.isIso_ci_of_isZero_X_succ`.  Descending one degree, the first
displayed sequence `0 ⟶ Im(d^n) ⟶ Ker(d^{n+1}) ⟶ H^{n+1}(ℰ) ⟶ 0` turns the kernel one degree up
into the image, by `Stacks.FiniteLocallyFree.isFiniteLocallyFree_X₁_of_shortExact_of_isPerfect`,
and then the second sequence `0 ⟶ Ker(d^n) ⟶ ℰ^n ⟶ Im(d^n) ⟶ 0` turns that image into the
kernel, by `Stacks.FiniteLocallyFree.isFiniteLocallyFree_X₁_of_shortExact`.  Only the first step
uses the hypotheses on the cohomology; the second needs none. -/
theorem isFiniteLocallyFree_Z
    (hterm : ∀ n : ℤ, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (P.X n))
    (hperf : ∀ n : ℤ, IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor X.Modules 0).obj (G.H n)))
    (htor : ∀ n : ℤ, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (G.H n)) (-1) 0)
    (b : ℤ) (hb : ∀ n : ℤ, b < n → IsZero (P.X n)) (n : ℤ) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (G.Z n) := by
  have htop : ∀ m : ℤ, b ≤ m → IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (G.Z m) := by
    intro m hm
    have := isIso_ci_of_isZero_X_succ P G m (hb (m + 1) (by omega))
    have := hterm m
    exact IsFiniteLocallyFree.of_iso.{u, u, u} (asIso (G.ci m)).symm
  have hrec : ∀ j : ℕ, ∀ m : ℤ, (b - m).toNat ≤ j →
      IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (G.Z m) := by
    intro j
    induction j with
    | zero => intro m hj; exact htop m (by omega)
    | succ j ih =>
        intro m hj
        by_cases hmb : b ≤ m
        · exact htop m hmb
        have hBsucc : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (G.B (m + 1)) :=
          isFiniteLocallyFree_X₁_of_shortExact_of_isPerfect _ (G.hB (m + 1))
            (ih (m + 1) (by omega)) (hperf (m + 1)) (htor (m + 1))
        exact isFiniteLocallyFree_X₁_of_shortExact _ (G.hA m) (hterm m) hBsucc
  exact hrec (b - n).toNat n le_rfl

/-- **The images of the differentials are finite locally free**, by the first displayed sequence
`0 ⟶ Im(d^{n-1}) ⟶ Ker(d^n) ⟶ H^n(ℰ) ⟶ 0` applied to the kernel supplied by
`Stacks.FiniteLocallyFree.isFiniteLocallyFree_Z`.  The degree is `n` throughout: the image into
degree `n` is indexed by `n` in this presentation, so the statement needs no shift. -/
theorem isFiniteLocallyFree_B
    (hterm : ∀ n : ℤ, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (P.X n))
    (hperf : ∀ n : ℤ, IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor X.Modules 0).obj (G.H n)))
    (htor : ∀ n : ℤ, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (G.H n)) (-1) 0)
    (b : ℤ) (hb : ∀ n : ℤ, b < n → IsZero (P.X n)) (n : ℤ) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (G.B n) :=
  isFiniteLocallyFree_X₁_of_shortExact_of_isPerfect _ (G.hB n)
    (isFiniteLocallyFree_Z P G hterm hperf htor b hb n) (hperf n) (htor n)

/-! ### Stacks 0F8J for the complex's own cycles and images -/

/-- **[Stacks, Tag 0F8J], the kernels.**  Let `ℰ` be a complex of finite locally free
`𝒪_X`-modules vanishing above degree `b`, each of whose cohomology sheaves is a perfect
`𝒪_X`-module of tor amplitude in `[-1, 0]`.  Then `Ker(d^n)` is finite locally free for every
`n`.

Boundedness below is not needed for this: the induction descends from `b`, and each step consumes
only the degree above. -/
@[stacks 0F8J "the kernels of the differentials, for a complex of finite locally free modules on
a scheme vanishing above a degree, with the cohomology sheaves perfect of tor amplitude in
[-1, 0]"]
theorem isFiniteLocallyFree_cycles
    (hterm : ∀ n : ℤ, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (P.X n))
    (hperf : ∀ n : ℤ, IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)))
    (htor : ∀ n : ℤ, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)) (-1) 0)
    (b : ℤ) [P.IsStrictlyLE b] (n : ℤ) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (P.cycles n) :=
  isFiniteLocallyFree_Z P (cochainGluingData P) hterm hperf htor b
    (fun m hm => P.isZero_of_isStrictlyLE b m hm) n

/-- **[Stacks, Tag 0F8J], the images.**  Under the hypotheses of
`Stacks.FiniteLocallyFree.isFiniteLocallyFree_cycles`, the image `Im(d^{n-1})` of the
differential into degree `n` is finite locally free.

That image is written here as `kernel (P.homologyπ n)`, the kernel of the projection from the
cocycles in degree `n` onto the cohomology there — the presentation
`StacksDraft.CartanEilenbergResolutions.cochainGluingData` uses, and the one that is indexed by `n`
with no subtraction.  It is the image in the categorical sense too:
`StacksDraft.CartanEilenbergResolutions.exists_imageIso_of_cochainGluingData` exhibits an
isomorphism
`CategoryTheory.Limits.image (P.dFrom (n - 1)) ≅ kernel (P.homologyπ n)` compatible with the
factorisation of the differential through it. -/
@[stacks 0F8J "the images of the differentials, presented as the kernels of the projections from
the cocycles onto the cohomology, for a complex of finite locally free modules on a scheme
vanishing above a degree, with the cohomology sheaves perfect of tor amplitude in [-1, 0]"]
theorem isFiniteLocallyFree_kernel_homologyπ
    (hterm : ∀ n : ℤ, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (P.X n))
    (hperf : ∀ n : ℤ, IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)))
    (htor : ∀ n : ℤ, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)) (-1) 0)
    (b : ℤ) [P.IsStrictlyLE b] (n : ℤ) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (kernel (P.homologyπ n)) :=
  isFiniteLocallyFree_B P (cochainGluingData P) hterm hperf htor b
    (fun m hm => P.isZero_of_isStrictlyLE b m hm) n

/-! ### The degreewise splitting datum -/

/-- **[Stacks, Tag 0F8J] assembled: the degreewise exactness datum of a bounded complex of finite
locally free `𝒪_X`-modules with perfect cohomology of tor dimension at most one.**

This is the source's conclusion in the form its consumers need.  `Stacks.Chow` defines the Chern
classes, the power sums and the Chern character of a complex against a
`Stacks.Chow.BoundedComplexSplitting` — the family of short exact sequences
`0 ⟶ Ker(d^n) ⟶ ℰ^n ⟶ Im(d^n) ⟶ 0` together with finite local freeness of every kernel and every
image — and before this nothing produced one.  The finite local freeness of the kernels and of
the images is precisely what the source takes from this tag; the rest of the datum is the
degreewise presentation of the complex, supplied by
`StacksDraft.CartanEilenbergResolutions.cochainGluingData`.

The two vanishing conditions at the ends of the range are the boundedness of the complex: nothing
enters degree `a` because `ℰ^{a-1}` vanishes, and nothing leaves degree `a + k` because
`ℰ^{a+k+1}` does. -/
@[stacks 0F8J "the degreewise exactness datum of a bounded complex of finite locally free modules
on a scheme, assembled from the two displayed short exact sequences, with the cohomology sheaves
perfect of tor amplitude in [-1, 0]"]
def boundedComplexSplitting (a : ℤ) (k : ℕ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE (a + (k : ℤ))]
    (hterm : ∀ n : ℤ, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (P.X n))
    (hperf : ∀ n : ℤ, IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor X.Modules 0).obj (G.H n)))
    (htor : ∀ n : ℤ, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (G.H n)) (-1) 0) :
    Stacks.Chow.BoundedComplexSplitting X P a k where
  cocycles := G.Z
  coboundaries := G.B
  isFiniteLocallyFree_X := hterm
  isFiniteLocallyFree_cocycles :=
    isFiniteLocallyFree_Z P G hterm hperf htor (a + (k : ℤ))
      (fun m hm => P.isZero_of_isStrictlyLE (a + (k : ℤ)) m hm)
  isFiniteLocallyFree_coboundaries :=
    isFiniteLocallyFree_B P G hterm hperf htor (a + (k : ℤ))
      (fun m hm => P.isZero_of_isStrictlyLE (a + (k : ℤ)) m hm)
  cocyclesι := G.ci
  toCoboundaries := G.ee
  coboundariesι n := G.aa n ≫ G.ci n
  mono_cocyclesι n := (G.hA n).mono_f
  epi_toCoboundaries n := (G.hA n).epi_g
  mono_coboundariesι n := by
    have := (G.hB n).mono_f
    have := (G.hA n).mono_f
    exact mono_comp _ _
  cocyclesι_comp_toCoboundaries := G.wA
  exact n := (G.hA n).exact
  toCoboundaries_comp_coboundariesι n := (G.hd n).symm
  isZero_coboundaries_bot :=
    isZero_B_of_isZero_X P G (a - 1) a (by ring)
      (P.isZero_of_isStrictlyGE a (a - 1) (by omega))
  isZero_coboundaries_top :=
    isZero_B_of_isZero_X_self P G (a + (k : ℤ) + 1)
      (P.isZero_of_isStrictlyLE (a + (k : ℤ)) (a + (k : ℤ) + 1) (by omega))

/-- **A bounded complex of finite locally free `𝒪_X`-modules whose cohomology sheaves are perfect
of tor dimension at most one has a degreewise exactness datum.**

This is `Stacks.FiniteLocallyFree.boundedComplexSplitting` in the form its consumers hold their
hypotheses in: the presentation is fixed to the canonical one, so the conditions on the
cohomology are stated for `P.homology n` rather than for a member of an abstract family. -/
theorem nonempty_boundedComplexSplitting (a : ℤ) (k : ℕ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE (a + (k : ℤ))]
    (hterm : ∀ n : ℤ, IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) (P.X n))
    (hperf : ∀ n : ℤ, IsPerfect.{u, u, u + 1}
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)))
    (htor : ∀ n : ℤ, HasTorAmplitude X.toRingedSpace
      ((DerivedCategory.singleFunctor X.Modules 0).obj (P.homology n)) (-1) 0) :
    Nonempty (Stacks.Chow.BoundedComplexSplitting X P a k) :=
  ⟨boundedComplexSplitting P (cochainGluingData P) a k hterm hperf htor⟩

end Stacks.FiniteLocallyFree

end
