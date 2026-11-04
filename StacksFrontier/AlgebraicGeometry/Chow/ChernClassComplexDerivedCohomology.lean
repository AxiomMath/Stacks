module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplexSchanuel
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplexIndependence

/-!
# The degreewise cohomology identification of two representatives of one derived object

This file supplies the hypothesis that
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplexSchanuel` was left waiting for.
`Stacks.Chow.ComplexCohomologyComparison.ofCohomologyIso` builds the
degreewise comparison datum of [Stacks, Tag 0ESZ] out of each complex's own presentation of its
own cohomology together with a degreewise identification of the two; nothing produced either
part.  Both are produced here, from a `Stacks.Chow.BoundedComplexSplitting` of each complex and an
isomorphism of the two complexes in `D(𝒪_X)`.

## Main definitions

* `Stacks.Chow.BoundedComplexSplitting.coboundariesToCocycles` — the inclusion
  `Im(d^{n-1}) ⟶ Ker(d^n)`.  Every consumer of `Stacks.Chow.ComplexCohomologyComparison` demanded
  this map as data; it is a consequence of `d ∘ d = 0`, and is constructed.
* `Stacks.Chow.BoundedComplexSplitting.cocyclesIso` — the identification of the splitting's
  abstract kernel `Ker(d^n)` with `HomologicalComplex.cycles`, which is what connects the
  splitting to the derived category.
* `Stacks.Chow.BoundedComplexSplitting.toHomology` — the resulting projection
  `Ker(d^n) ⟶ H^n(ℰ^•)` onto Mathlib's homology of the complex.
* `Stacks.Chow.homologyIsoOfRepresentation` — the cohomology of an object of `D(𝒪_X)` is the
  cohomology of any complex representing it, the bridge a hypothesis about `H^i(E)` needs to be
  used on a complex.
* `Stacks.Chow.homologyIsoOfDerivedIso` — the degreewise identification
  `H^n(ℰ^•) ≅ H^n(ℱ^•)` attached to an isomorphism `ℰ^• ≅ ℱ^•` in `D(𝒪_X)`.
* `Stacks.Chow.ComplexCohomologyComparison.ofDerivedIso` — **the comparison datum from a derived
  isomorphism alone.**

## Main results

* `Stacks.Chow.BoundedComplexSplitting.exact_toHomology` — the presentation
  `0 ⟶ Im(d^{n-1}) ⟶ Ker(d^n) ⟶ H^n(ℰ^•) ⟶ 0` of the complex's own cohomology, intrinsic to the
  splitting.
* `Stacks.Chow.hasCohomologyComparisonAtCommonWindow_of_derivedIso` — the hypothesis of the five
  locally bounded independence statements of
  `StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplexIndependence`, from splittings at a common
  window and a derived isomorphism.

## Implementation notes

### What is carried, and what is not

The two hypotheses are a `Stacks.Chow.BoundedComplexSplitting` of each complex and the derived
isomorphism.  Nothing else: no tor dimension, no modification, no admissible blowup, no finite
local freeness beyond what the splittings already record, and no hypothesis naming cohomology.

In particular **neither [Stacks, Tag 02UC] nor [Stacks, Tag 0ESR] is used or carried here.**  That
is not an accident of the formalization but the shape of the source's own proof.  The source needs
those two reductions to produce the *splittings* — on an arbitrary `X` the kernels and images of a
complex of finite locally free modules are not finite locally free, so
`Stacks.Chow.BoundedComplexSplitting` need not be inhabited, and Tag 0ESR is what makes the
cohomology perfect of tor dimension at most one on a modification, whereupon the sheaf-level form
of [Stacks, Tag 0F8J] gives the finite local freeness.  Once the splittings are *given*, the
identification of the cohomology modules is formal, and that is what this file is.  So the
division of labour is: Tags 02UC, 0ESR and 0F8J produce the splittings; this file turns a
splitting of each complex plus a derived isomorphism into the comparison datum.

### Why the splitting's kernel has to be identified with Mathlib's cycles

`Stacks.Chow.BoundedComplexSplitting` records `Ker(d^n)` and `Im(d^{n-1})` abstractly, as objects
with the universal properties that make them a kernel and an image: `S.exact n` says the inclusion
`S.cocyclesι n` is a kernel of `S.toCoboundaries n`, and `S.toCoboundaries (n-1)` is an
epimorphism onto `S.coboundaries n` whose composite with the inclusion is `d^{n-1}`.  Those
properties determine the objects up to canonical isomorphism but do not make them *equal* to
`HomologicalComplex.cycles` and the image of `HomologicalComplex.toCycles`, which is what the
derived category's homology functor is about.  `Stacks.Chow.BoundedComplexSplitting.cocyclesIso`
is that canonical isomorphism, built from the two kernel properties — the splitting's and
`HomologicalComplex.cyclesIsKernel` — using that `d^n` factors as `S.toCoboundaries n` followed by
a monomorphism.

With it, `H^n` of the splitting's presentation is Mathlib's `P.homology n`: the projection
`Stacks.Chow.BoundedComplexSplitting.toHomology` is a cokernel of
`Stacks.Chow.BoundedComplexSplitting.coboundariesToCocycles` because `P.homologyπ n` is a cokernel
of `P.toCycles (n-1) n`, that map factors through the splitting's inclusion by the *epimorphism*
`S.toCoboundaries (n-1)`, and precomposing a cokernel with an epimorphism does not change it.

### Which derived category

`CategoryTheory.HasDerivedCategory` is a class, and two instances of it for `X.Modules` give two
different categories: the locally small one of
`StacksFrontier.Homology.DerivedCategory.LocallySmall`, a global instance, and
`CategoryTheory.HasDerivedCategory.standard`, which
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Defined` fixes by a file-level local
instance and against which `Stacks.Chow.EnvelopePresentation.representation` -- the isomorphism
`Lf^*E` with a complex that is the natural source of the hypothesis used here -- is stated.

So the model is a parameter: the statements of the last section take
`[HasDerivedCategory.{w} X.Modules]` and are usable at either, and this file imports neither
instance.

### The index arithmetic

The fields of `Stacks.Chow.BoundedComplexSplitting` are stated at `n` and `n + 1`, while what is
needed at degree `n` is the field at the predecessor of `n`.  The composite
`S.toCoboundaries (n-1) ≫ S.coboundariesι n` does not even typecheck, `S.coboundaries (n-1+1)` and
`S.coboundaries n` not being the same term, and forcing it through by rewriting `n-1+1` to `n`
would transport along an equality of integers under a motive, which is then paid for in the kernel
at every later use.

Two devices avoid it.  Every *proposition* whose statement mentions only `n` —
`Stacks.Chow.BoundedComplexSplitting.coboundariesι_comp_toCoboundaries` and
`Stacks.Chow.BoundedComplexSplitting.coboundariesToCocycles_comp_toHomology` — opens with
`obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1`, which replaces `n` by `m + 1` in the goal, so the fields
apply at `m` with no cast anywhere.  The one statement that must mention both degrees,
`Stacks.Chow.BoundedComplexSplitting.toCoboundaries_comp_coboundariesToCocycles_comp_cocyclesIso`,
is therefore stated at `m` and `m + 1`.

`HomologicalComplex.toCycles` takes its two degrees as independent arguments, so `P.toCycles m n`
typechecks for any `m` and `n` and needs no such care.  The bridge used in a *data* position, where
`obtain` is unavailable because `Exists` cannot be eliminated into a type,
`Stacks.Chow.BoundedComplexSplitting.toCycles_comp_cocyclesIso_inv_comp`, exploits that: it takes
`m`, `n` and `m + 1 = n` and substitutes inside its own proof, and its call site passes `n - 1`,
`n` and `by omega`, matching `HomologicalComplex.homologyIsCokernel` on the nose.

## References

* [Stacks Project, Tag 0ESZ](https://stacks.math.columbia.edu/tag/0ESZ)
* [Stacks Project, Tag 0F8J](https://stacks.math.columbia.edu/tag/0F8J)
* [Stacks Project, Tag 00O3](https://stacks.math.columbia.edu/tag/00O3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe w u

namespace Stacks.Chow

variable {X : Scheme.{u}}

namespace BoundedComplexSplitting

variable {P : CochainComplex X.Modules ℤ} {a : ℤ} {k : ℕ}

/-! ### The inclusion of the coboundaries into the cocycles -/

/-- **The image of `d^{n-1}` is annihilated by `d^n`.** The composite
`Im(d^{n-1}) ⟶ ℰ^n ⟶ Im(d^n)` vanishes: after the epimorphism `ℰ^{n-1} ⟶ Im(d^{n-1})` and the
monomorphism `Im(d^{n+1}) ⟶ ℰ^{n+1}` it becomes `d^{n-1} ≫ d^n`.

The degree is written as a successor at the start of the proof, so that the fields of the
splitting apply without an index cast; see the implementation notes of this file. -/
theorem coboundariesι_comp_toCoboundaries (S : BoundedComplexSplitting X P a k) (n : ℤ) :
    S.coboundariesι n ≫ S.toCoboundaries n = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by omega⟩
  have := S.mono_coboundariesι (m + 1 + 1)
  have := S.epi_toCoboundaries m
  rw [← cancel_mono (S.coboundariesι (m + 1 + 1)), zero_comp, Category.assoc,
    S.toCoboundaries_comp_coboundariesι (m + 1), ← cancel_epi (S.toCoboundaries m), comp_zero,
    ← Category.assoc, S.toCoboundaries_comp_coboundariesι m, P.d_comp_d]

/-- **The inclusion `Im(d^{n-1}) ⟶ Ker(d^n)`.** It is the factorization of the inclusion of the
image into `ℰ^n` through the kernel of `d^n`, which exists by
`Stacks.Chow.BoundedComplexSplitting.coboundariesι_comp_toCoboundaries`.

Every consumer of `Stacks.Chow.ComplexCohomologyComparison` takes this map as data — the fields
`firstCoboundariesι` and `secondCoboundariesι`, and the parameters `fι` and `sι` of
`Stacks.Chow.ComplexCohomologyComparison.ofCohomologyPresentations`.  It is not an extra
hypothesis: a splitting already determines it. -/
def coboundariesToCocycles (S : BoundedComplexSplitting X P a k) (n : ℤ) :
    S.coboundaries n ⟶ S.cocycles n :=
  have := S.mono_cocyclesι n
  (KernelFork.IsLimit.lift' (S.exact n).fIsKernel
    (S.coboundariesι n) (S.coboundariesι_comp_toCoboundaries n)).1

/-- The defining property of `Stacks.Chow.BoundedComplexSplitting.coboundariesToCocycles`:
followed by the inclusion of `Ker(d^n)` into `ℰ^n` it is the splitting's own inclusion of
`Im(d^{n-1})`, which is the map it factors. -/
@[reassoc (attr := simp)]
theorem coboundariesToCocycles_comp (S : BoundedComplexSplitting X P a k) (n : ℤ) :
    S.coboundariesToCocycles n ≫ S.cocyclesι n = S.coboundariesι n := by
  have := S.mono_cocyclesι n
  simpa [coboundariesToCocycles] using
    (KernelFork.IsLimit.lift' (S.exact n).fIsKernel
      (S.coboundariesι n) (S.coboundariesι_comp_toCoboundaries n)).2

/-- **The inclusion `Im(d^{n-1}) ⟶ Ker(d^n)` is a monomorphism.** Composed with the inclusion of
the kernel into `ℰ^n` it is the monomorphism `S.coboundariesι n`. -/
instance mono_coboundariesToCocycles (S : BoundedComplexSplitting X P a k) (n : ℤ) :
    Mono (S.coboundariesToCocycles n) :=
  have := S.mono_coboundariesι n
  mono_of_mono_fac (S.coboundariesToCocycles_comp n)

/-! ### Identifying the splitting's kernel with the cycles of the complex -/

/-- The splitting's inclusion of `Ker(d^n)` into `ℰ^n` is annihilated by `d^n`: the differential
factors through `Im(d^n)`. -/
theorem cocyclesι_comp_d (S : BoundedComplexSplitting X P a k) (n : ℤ) :
    S.cocyclesι n ≫ P.d n (n + 1) = 0 := by
  rw [← S.toCoboundaries_comp_coboundariesι n, ← Category.assoc,
    S.cocyclesι_comp_toCoboundaries n, zero_comp]

/-- **The splitting's inclusion of `Ker(d^n)` is a kernel of `d^n`.** The splitting records it as
a kernel of its own surjection `ℰ^n ⟶ Im(d^n)`, by `S.exact n`; since `d^n` is that surjection
followed by a monomorphism, a map annihilated by `d^n` is annihilated by the surjection, so the
two kernel forks have the same universal property. -/
def isLimitKernelForkCocyclesι (S : BoundedComplexSplitting X P a k) (n : ℤ) :
    IsLimit (KernelFork.ofι (S.cocyclesι n) (S.cocyclesι_comp_d n)) :=
  have := S.mono_cocyclesι n
  have := S.mono_coboundariesι (n + 1)
  have key : ∀ {W : X.Modules} (g : W ⟶ P.X n), g ≫ P.d n (n + 1) = 0 →
      g ≫ S.toCoboundaries n = 0 := fun {W} g eq => by
    rw [← cancel_mono (S.coboundariesι (n + 1)), zero_comp, Category.assoc,
      S.toCoboundaries_comp_coboundariesι n, eq]
  KernelFork.IsLimit.ofι _ _
    (fun g' eq' => (KernelFork.IsLimit.lift' (S.exact n).fIsKernel g' (key g' eq')).1)
    (fun g' eq' => by
      simpa using (KernelFork.IsLimit.lift' (S.exact n).fIsKernel g' (key g' eq')).2)
    (fun g' eq' m hm => by
      rw [← cancel_mono (S.cocyclesι n), hm]
      simpa using (KernelFork.IsLimit.lift' (S.exact n).fIsKernel g' (key g' eq')).2.symm)

/-- **The splitting's `Ker(d^n)` is the cycles of the complex in degree `n`.** Both are kernels of
`d^n`: the splitting's inclusion is one by
`Stacks.Chow.BoundedComplexSplitting.isLimitKernelForkCocyclesι`, and
`HomologicalComplex.iCycles` is one by `HomologicalComplex.cyclesIsKernel`.  This is the
isomorphism that connects a splitting to the derived category, where the cohomology of the
complex is computed. -/
def cocyclesIso (S : BoundedComplexSplitting X P a k) (n : ℤ) : S.cocycles n ≅ P.cycles n :=
  IsLimit.conePointUniqueUpToIso (S.isLimitKernelForkCocyclesι n)
    (P.cyclesIsKernel n (n + 1) (by simp))

/-- `Stacks.Chow.BoundedComplexSplitting.cocyclesIso` carries one inclusion into `ℰ^n` to the
other: followed by `HomologicalComplex.iCycles` it is the splitting's own inclusion of
`Ker(d^n)`. -/
@[reassoc (attr := simp)]
theorem cocyclesIso_hom_comp (S : BoundedComplexSplitting X P a k) (n : ℤ) :
    (S.cocyclesIso n).hom ≫ P.iCycles n = S.cocyclesι n := by
  simpa [cocyclesIso] using IsLimit.conePointUniqueUpToIso_hom_comp
    (S.isLimitKernelForkCocyclesι n) (P.cyclesIsKernel n (n + 1) (by simp))
    WalkingParallelPair.zero

/-- The splitting's inclusion `Im(d^m) ⟶ Ker(d^{m+1})`, read in the cycles of the complex, is
`HomologicalComplex.toCycles` precomposed with the splitting's surjection onto the image.  Both
degrees occur, so the statement is at `m` and `m + 1`; see the implementation notes. -/
@[reassoc]
theorem toCoboundaries_comp_coboundariesToCocycles_comp_cocyclesIso
    (S : BoundedComplexSplitting X P a k) (m : ℤ) :
    S.toCoboundaries m ≫ S.coboundariesToCocycles (m + 1) ≫ (S.cocyclesIso (m + 1)).hom =
      P.toCycles m (m + 1) := by
  rw [← cancel_mono (P.iCycles (m + 1)), Category.assoc, Category.assoc,
    S.cocyclesIso_hom_comp (m + 1), S.coboundariesToCocycles_comp (m + 1),
    S.toCoboundaries_comp_coboundariesι m, P.toCycles_i]

/-! ### The splitting's presentation of the complex's cohomology -/

/-- **The projection `Ker(d^n) ⟶ H^n(ℰ^•)` of a splitting onto the cohomology of the complex.**
The splitting's kernel is the cycles, by
`Stacks.Chow.BoundedComplexSplitting.cocyclesIso`, and the cycles project onto the homology. -/
def toHomology (S : BoundedComplexSplitting X P a k) (n : ℤ) : S.cocycles n ⟶ P.homology n :=
  (S.cocyclesIso n).hom ≫ P.homologyπ n

/-- **The projection of a splitting onto the cohomology of the complex is an epimorphism**, being
an isomorphism followed by `HomologicalComplex.homologyπ`. -/
instance epi_toHomology (S : BoundedComplexSplitting X P a k) (n : ℤ) : Epi (S.toHomology n) := by
  rw [toHomology]
  exact epi_comp _ _

/-- **The coboundaries die in the cohomology.** The composite
`Im(d^{n-1}) ⟶ Ker(d^n) ⟶ H^n(ℰ^•)` vanishes, which is what makes the splitting's inclusion of
the image and its projection onto the cohomology a presentation of `H^n(ℰ^•)`.

The degree is written as a successor at the start of the proof, so that the fields of the
splitting apply without an index cast; see the implementation notes of this file. -/
@[reassoc (attr := simp)]
theorem coboundariesToCocycles_comp_toHomology (S : BoundedComplexSplitting X P a k) (n : ℤ) :
    S.coboundariesToCocycles n ≫ S.toHomology n = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, n = m + 1 := ⟨n - 1, by omega⟩
  have := S.epi_toCoboundaries m
  rw [← cancel_epi (S.toCoboundaries m), comp_zero, toHomology,
    S.toCoboundaries_comp_coboundariesToCocycles_comp_cocyclesIso_assoc m,
    P.toCycles_comp_homologyπ]

/-- The bridge used to descend a map out of the splitting's kernel through
`HomologicalComplex.homologyπ`: a map killed by the inclusion of the coboundaries, read in the
cycles, is killed by `HomologicalComplex.toCycles`.

The two degrees are separate arguments with an equation between them, rather than `n - 1` and `n`,
because the consumer is a *data* definition, where `∃` cannot be eliminated; see the
implementation notes of this file. -/
theorem toCycles_comp_cocyclesIso_inv_comp (S : BoundedComplexSplitting X P a k) (m n : ℤ)
    (h : m + 1 = n) {Z : X.Modules} (g : S.cocycles n ⟶ Z)
    (hg : S.coboundariesToCocycles n ≫ g = 0) :
    P.toCycles m n ≫ (S.cocyclesIso n).inv ≫ g = 0 := by
  subst h
  rw [← S.toCoboundaries_comp_coboundariesToCocycles_comp_cocyclesIso m, Category.assoc,
    Category.assoc, Iso.hom_inv_id_assoc, hg, comp_zero]

/-- **The projection onto the cohomology is a cokernel of the inclusion of the coboundaries.**
`P.homologyπ n` is a cokernel of `P.toCycles (n-1) n`, which factors as the *epimorphism*
`S.toCoboundaries (n-1)` followed by the inclusion read in the cycles; so a map out of the
splitting's kernel killing the inclusion descends through it, uniquely because it is an
epimorphism. -/
def isColimitCokernelCoforkToHomology (S : BoundedComplexSplitting X P a k) (n : ℤ) :
    IsColimit (CokernelCofork.ofπ (S.toHomology n)
      (S.coboundariesToCocycles_comp_toHomology n)) :=
  have hH := P.homologyIsCokernel (n - 1) n (by simp)
  CokernelCofork.IsColimit.ofπ _ _
    (fun g' eq' => (CokernelCofork.IsColimit.desc' hH _
      (S.toCycles_comp_cocyclesIso_inv_comp (n - 1) n (by omega) g' eq')).1)
    (fun g' eq' => by
      have h2 := (CokernelCofork.IsColimit.desc' hH _
        (S.toCycles_comp_cocyclesIso_inv_comp (n - 1) n (by omega) g' eq')).2
      simp only [CokernelCofork.π_ofπ] at h2
      rw [toHomology, Category.assoc, h2, Iso.hom_inv_id_assoc])
    (fun g' eq' m hm => by
      have := S.epi_toHomology n
      have h2 := (CokernelCofork.IsColimit.desc' hH _
        (S.toCycles_comp_cocyclesIso_inv_comp (n - 1) n (by omega) g' eq')).2
      simp only [CokernelCofork.π_ofπ] at h2
      rw [← cancel_epi (S.toHomology n), hm, toHomology, Category.assoc, h2,
        Iso.hom_inv_id_assoc])

/-- **The splitting presents the complex's cohomology: `0 ⟶ Im(d^{n-1}) ⟶ Ker(d^n) ⟶ H^n ⟶ 0` is
exact.** This is the presentation that
`Stacks.Chow.ComplexCohomologyComparison.ofCohomologyPresentations` asks for, and it is intrinsic
to the splitting: the projection is a cokernel of the inclusion by
`Stacks.Chow.BoundedComplexSplitting.isColimitCokernelCoforkToHomology`, and a cokernel is exact
where it sits. -/
theorem exact_toHomology (S : BoundedComplexSplitting X P a k) (n : ℤ) :
    (ShortComplex.mk (S.coboundariesToCocycles n) (S.toHomology n)
      (S.coboundariesToCocycles_comp_toHomology n)).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (S.isColimitCokernelCoforkToHomology n)

end BoundedComplexSplitting

/-! ### The degreewise identification from an isomorphism in the derived category -/

section DerivedCategory

-- The derived category is taken at whatever model the caller has, rather than at the locally
-- small one of `StacksFrontier.Homology.DerivedCategory.LocallySmall` or at
-- `HasDerivedCategory.standard`.  The two are different instances and hence different categories,
-- and `ChernClassDerived.Defined`, where the isomorphism supplied below comes from, fixes the
-- standard one by a file-level local instance.  Taking the model as a parameter serves both.
variable [HasDerivedCategory.{w} X.Modules]

/-- **The cohomology of an object of `D(𝒪_X)` is the cohomology of any complex representing
it.** The homology functor on the derived category factors through the quotient, by
`CategoryTheory.DerivedCategory.homologyFunctorFactors`.

This is the bridge a hypothesis about `H^i(E)` needs in order to be used on a complex: for
instance `AlgebraicGeometry.IsHomologyPerfectTorLEOne`, the conclusion of [Stacks, Tag 0ESR], is
a statement about `H^i(Lb^*E)` as an object of `X.Modules`, and the two sequences of
[Stacks, Tag 0F8J] consume exactly that pair of properties of the third term of a short exact
sequence — but the short exact sequence available is the one of a *complex*, whose third term is
the complex's own cohomology. -/
def homologyIsoOfRepresentation {E : DerivedCategory X.Modules} {P : CochainComplex X.Modules ℤ}
    (e : E ≅ DerivedCategory.Q.obj P) (n : ℤ) :
    (DerivedCategory.homologyFunctor X.Modules n).obj E ≅ P.homology n :=
  (DerivedCategory.homologyFunctor X.Modules n).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors X.Modules n).app P

/-- **Two complexes representing the same object of `D(𝒪_X)` have identified cohomology in every
degree.** The homology functor on the derived category factors through the quotient, by
`CategoryTheory.DerivedCategory.homologyFunctorFactors`, so an isomorphism of the two images in
`D(𝒪_X)` is carried to an isomorphism of the homology modules of the two complexes.

This is the identification that [Stacks, Tag 0ESZ] needs and that
`Stacks.Chow.ComplexCohomologyComparison.ofCohomologyIso` asks for.  It is a general fact about
the derived category and carries no geometric hypothesis. -/
def homologyIsoOfDerivedIso {P Q : CochainComplex X.Modules ℤ}
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (n : ℤ) :
    P.homology n ≅ Q.homology n :=
  (homologyIsoOfRepresentation (E := DerivedCategory.Q.obj P) (Iso.refl _) n).symm ≪≫
    homologyIsoOfRepresentation (E := DerivedCategory.Q.obj P) e n

/-- **The degreewise comparison datum of [Stacks, Tag 0ESZ] from an isomorphism in `D(𝒪_X)`.**
Given a splitting of each of two complexes at a common window and an isomorphism of the two in
the derived category, the comparison datum of
`Stacks.Chow.ComplexCohomologyComparison` exists.

Each splitting presents its own complex's cohomology, by
`Stacks.Chow.BoundedComplexSplitting.exact_toHomology`, and the two cohomologies are identified by
`Stacks.Chow.homologyIsoOfDerivedIso`; `Stacks.Chow.ComplexCohomologyComparison.ofCohomologyIso`
then produces the Schanuel module and its two short exact sequences.

**What this carries.** The two splittings and the derived isomorphism, and nothing else.  No tor
dimension, no modification, no blowup: neither [Stacks, Tag 02UC] nor [Stacks, Tag 0ESR] appears,
because in the source those two reductions are what produce the *splittings*, which here are
hypotheses.  See the implementation notes of this file. -/
def ComplexCohomologyComparison.ofDerivedIso {P Q : CochainComplex X.Modules ℤ} {a : ℤ} {k : ℕ}
    (S : BoundedComplexSplitting X P a k) (T : BoundedComplexSplitting X Q a k)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) :
    ComplexCohomologyComparison S T :=
  ComplexCohomologyComparison.ofCohomologyIso S T (fun n => P.homology n) (fun n => Q.homology n)
    (fun n => homologyIsoOfDerivedIso e n)
    S.coboundariesToCocycles S.coboundariesToCocycles_comp S.toHomology
    S.coboundariesToCocycles_comp_toHomology S.mono_coboundariesToCocycles S.epi_toHomology
    S.exact_toHomology
    T.coboundariesToCocycles T.coboundariesToCocycles_comp T.toHomology
    T.coboundariesToCocycles_comp_toHomology T.mono_coboundariesToCocycles T.epi_toHomology
    T.exact_toHomology

/-- **The hypothesis of the locally bounded independence statements of [Stacks, Tag 0ESZ], from a
derived isomorphism.** Two locally bounded complexes of finite locally free modules that vanish
outside one window, that admit a splitting there, and that represent the same object of `D(𝒪_X)`
satisfy `Stacks.Chow.HasCohomologyComparisonAtCommonWindow`.

This is what the five independence statements of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassComplexIndependence` reduce to, so with the
splittings in hand it closes the comparison half of them.  A common window always exists, by
`Stacks.Chow.exists_common_window_of_isLocallyBoundedFiniteLocallyFree`; what is carried is the
splittings and the derived isomorphism. -/
theorem hasCohomologyComparisonAtCommonWindow_of_derivedIso
    {P Q : CochainComplex X.Modules ℤ} (a : ℤ) (k : ℕ)
    (hP : ∀ n : ℤ, (n < a ∨ a + (k : ℤ) < n) → IsZero (P.X n))
    (hQ : ∀ n : ℤ, (n < a ∨ a + (k : ℤ) < n) → IsZero (Q.X n))
    (S : BoundedComplexSplitting X P a k) (T : BoundedComplexSplitting X Q a k)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) :
    HasCohomologyComparisonAtCommonWindow P Q :=
  ⟨a, k, hP, hQ, S, T, ⟨ComplexCohomologyComparison.ofDerivedIso S T e⟩⟩

end DerivedCategory

end Stacks.Chow

end
