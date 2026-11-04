module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportFrobeniusAction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricFrobeniusStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LefschetzTraceFormula

/-!
# The trace formula in dimension at most one

Let `k` be a finite field with `q = p ^ n` elements, let `X` be a separated scheme of finite
type over `k` of dimension at most one, let `Λ` be a finite ring whose cardinality is prime to
that of `k`, and let `K` be a bounded below complex of sheaves of `Λ`-modules on the small étale
site of `X`.  The trace formula asserts the identity

`Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)`

in the additive commutator quotient `Λ^natural`.  Both sides of it are produced here from the
geometry of `X`.  On the left, the base change `X_k̄` of `X` to an algebraically closed extension
`k̄` of `k` carries the geometric Frobenius `π_X × id` of [Stacks, Tag 03SQ]; an extension of
that endomorphism to a compactification of `X_k̄` over `Spec k̄` makes it act on
`RΓ_c(X_k̄, K|_{X_k̄})` through
`Stacks.EtaleCohomology.compactSupportPullback`, and the trace of the action is the global
Lefschetz number of [Stacks, Tag 03TX] evaluated on the datum
`Stacks.EtaleCohomology.frobeniusActionOnCompactSupport`.  On the right, a rational point `x` of
`X` determines a geometric point `x̄` of `X` over `k̄`, the Galois group of `k̄` over `k` acts on
the étale stalk there, and the inverse of the arithmetic Frobenius is the endomorphism `π_x` of
[Stacks, Tag 03SW]; taking it degreewise on the stalk of `K` gives the local Lefschetz number of
[Stacks, Tag 03TY].

So this file is where the Lefschetz machinery, which takes a perfect complex with an
endomorphism as opaque data, meets an actual scheme: the global datum is built by
`Stacks.EtaleCohomology.frobeniusActionOnCompactSupport` from a compactification endomorphism
over the geometric Frobenius, and the stalk data by
`Stacks.Frobenius.geometricFrobeniusStalkFunctor` from the Galois action at the geometric points
over the rational points.

## Main definitions

* `Stacks.EtaleCohomology.rationalPoints` — the set `X(k)` of `k`-rational points of a scheme
  over `k`, namely the sections of its structure morphism.
* `Stacks.EtaleCohomology.rationalPointStalkFunctor` — the étale stalk functor at the geometric
  point over a rational point, with coefficients in `Λ`-modules.
* `Stacks.EtaleCohomology.rationalPointStalkComplex` — the stalk `K_x̄` of a bounded below
  complex of sheaves of `Λ`-modules, taken degreewise.
* `Stacks.EtaleCohomology.rationalPointStalkFrobenius` — the endomorphism `π_x` of `K_x̄`,
  degreewise the geometric Frobenius of [Stacks, Tag 03SW].
* `Stacks.EtaleCohomology.geometricFrobeniusStalkDatum` — the datum of [Stacks, Tag 03TY]
  produced from the geometry: the stalk at each rational point with the Frobenius acting on it.
* `Stacks.EtaleCohomology.etaleModuleInverseImagePlus` — inverse image of a bounded below
  complex of sheaves of modules along a morphism of schemes, taken degreewise.
* `Stacks.EtaleCohomology.baseChangeCoefficients` — the restriction `K|_{X_k̄}` of the
  coefficient complex to the base change, as an object of the bounded below derived category.

## Main results

* `Stacks.EtaleCohomology.compactSupportLefschetzNumber_eq_localLefschetzNumber` — **the trace
  formula for a separated finite type scheme of dimension at most one**, in the geometric form
  just described.

## Implementation notes

The source states the theorem for `K` in `D_ctf(X, Λ)`, which in this development is
`Stacks.EtaleCohomology.ConstructibleFiniteTorDerivedCategory`.  That category is not available
in the framework the two sides of the identity live in: it is
indexed by a `Stacks.BigEtaleSite` and an object of its `B.Scheme`, its site is
`Stacks.SmallEtale.topology B X.obj X.property` rather than the `smallEtaleTopology` of a
scheme, it asks the coefficient ring to be commutative and Noetherian where the trace formula
asks only that it be finite and possibly noncommutative, and membership is
measured against a chosen family of derived tensor products on the slices of a ringed site, so
that instantiating the family specialises the subcategory.  Cohomology with compact support
`Stacks.EtaleCohomology.compactlySupportedCohomology`, by contrast, is a functor on
`DerivedCategory.Plus (EtaleModules Λ X)` for `X : Scheme`, and so is the étale stalk that the
Galois action of `Stacks.Frobenius.geometricFrobeniusStalkFunctor` operates on.

The comparison of the two presentations of the small étale site is *not* what is missing.
`AlgebraicGeometry.SmallEtale.toEtaleSite` is a dense subsite inclusion
(`AlgebraicGeometry.SmallEtale.isDenseSubsite_toEtaleSite`), so the two categories of sheaves
are identified by `AlgebraicGeometry.SmallEtale.sheafEquiv`, and
`AlgebraicGeometry.sheafEquivCompSheafFiberIso` identifies the stalk functor of
`AlgebraicGeometry.Scheme.pointSmallEtale` at a geometric point — which is exactly
`Stacks.EtaleCohomology.rationalPointStalkFunctor` below — with the bounded site's
`AlgebraicGeometry.etaleModuleStalkFunctor`.  What is missing is the rest: `X` would have to be
presented as an object of a big étale site, the coefficient ring reconciled, finite Tor
dimension transported across the comparison, and — for `hstalkPerfect` — the direction
(1) ⟹ (2) of [Stacks, Tag 03TT], which is what turns membership of `D_ctf` into the bounded
complex of constructible flat sheaves whose stalks
`AlgebraicGeometry.stalk_isPerfect_of_isConstructibleFlatModuleSheaf` proves perfect.  That
direction is unproved; the implementation notes of
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ConstructibleComplexes/ConstructibleFlat.lean`
record its state.  Accordingly the
coefficient object here is a bounded below complex of sheaves of `Λ`-modules on the small étale
site of `X`, and the two finiteness properties that `D_ctf` is there to supply — perfectness of
`RΓ_c(X_k̄, K)` and of each stalk `K_x̄` over `Λ` — are named hypotheses.  The first of them is
[Stacks, Tag 03TV].

The stalk of the coefficient complex is taken degreewise, which computes the derived stalk
because the étale stalk functor is exact; its additivity, needed to let it act on complexes, is
read off its left exactness, which in turn needs exactness of filtered colimits of `Λ`-modules
indexed by the universe of the site, supplied by `CategoryTheory.AB5OfSize_shrink`.  The
geometric Frobenius enters as a natural transformation of the stalk functor, so the degreewise
endomorphism of the stalk complex commutes with the differentials by naturality alone.

The restriction `K|_{X_k̄}` is the degreewise inverse image along the projection
`X_k̄ ⟶ X`, which is available for module coefficients and an arbitrary morphism of schemes by
`Stacks.EtaleCohomology.etaleModuleInverseImage`; the inverse image is additive and preserves
zero objects, so it carries bounded below complexes to bounded below complexes.  This is what
lets a single coefficient complex on `X` serve both sides of the identity.

Three further inputs of the source's proof are hypotheses rather than constructions.

The dévissage of Step 1, the filtration of `RΓ_c(X_k̄, K)` whose graded pieces are
`RΓ_c(U_k̄, K|_U)` for the open complement `U = X - X(k)` and the stalks at the rational points,
is the datum `Stacks.EtaleCohomology.LefschetzDevissage`, together with the two identifications
`hglobal` and `hstalk` of its underlying complex with `RΓ_c(X_k̄, K)` and of its graded pieces
at the rational points with the stalks.  Those identifications are the geometric content of
Steps 1 and 2 and are what make the dévissage a dévissage of this particular `K` on this
particular `X`.

Steps 7 to 9 enter as the Galois decomposition of the trace on the open complement: a finite
group, a prime `ℓ` a power of which annihilates `Λ^natural`, the integers `Tr_A^{Z_g}` and the
traces `Tr_Λ(g | M)`, the identity `hdecomposition` expressing the trace on `U` as the sum over
the group of their products, and the divisibility `hdivisible` saying that the order of the
stabiliser annihilates each coefficient trace at the chosen level.  The vanishing of the trace
on `U` is then proved, not assumed: the level is taken large enough that each coefficient trace
is divisible by the annihilating power of `ℓ`, so each term of the decomposition vanishes in
`Λ^natural`.  This is the input of [Stacks, Tag 03TZ].  The reductions of Steps 3 to 6 — of a
separated finite type scheme of dimension at most one to a smooth irreducible affine curve
without rational points, and the trivialisation of the coefficients by a finite étale Galois
cover — are not formalized here.

The separatedness, finite type and quasi-compactness of the structure morphism, the bound on the
dimension and the coprimality of the two cardinalities are carried in the statement because the
source carries them, although the deduction above uses none of them: they are what make the two
sides well posed, through the inputs just listed, rather than what makes the identity follow
from those inputs.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
* [Stacks Project, Tag 03UH](https://stacks.math.columbia.edu/tag/03UH)
* [Stacks Project, Tag 03SQ](https://stacks.math.columbia.edu/tag/03SQ)
* [Stacks Project, Tag 03SW](https://stacks.math.columbia.edu/tag/03SW)
* [Stacks Project, Tag 03TQ](https://stacks.math.columbia.edu/tag/03TQ)
* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
* [Stacks Project, Tag 03TX](https://stacks.math.columbia.edu/tag/03TX)
* [Stacks Project, Tag 03TY](https://stacks.math.columbia.edu/tag/03TY)
* [Stacks Project, Tag 03TZ](https://stacks.math.columbia.edu/tag/03TZ)
* [Stacks Project, Tag 0GJZ](https://stacks.math.columbia.edu/tag/0GJZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.FilteredDerived
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r t

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Exactness of filtered colimits at the universe of the site -/

/-- Filtered colimits of `Λ`-modules indexed by the universe of the objects of the small étale
site are exact.  This is the lowering of the corresponding statement at the universe of the
sections, and is what makes the étale stalk functor left exact with module coefficients. -/
private theorem etaleModuleCoefficients_ab5OfSize (Λ : Type r) [Ring Λ] :
    AB5OfSize.{u, u} (ModuleCat.{max (u + 1) r} Λ) :=
  AB5OfSize_shrink.{u, u, max (u + 1) r, max (u + 1) r} _

attribute [local instance] etaleModuleCoefficients_ab5OfSize

/-! ### Rational points -/

/-- **The set `X(k)` of `k`-rational points** of a scheme over `k`: the sections of its
structure morphism. -/
public def rationalPoints {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    Type u :=
  { x : Spec (.of k) ⟶ X // x ≫ f = 𝟙 (Spec (.of k)) }

/-! ### The stalk of the coefficient complex at a rational point -/

section Stalk

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] {X : Scheme.{u}}
  (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar]

/-- The étale stalk functor at the geometric point over a rational point `x`, with coefficients
in `Λ`-modules.  This is the functor the Galois group of `k̄` over `k` acts on. -/
public abbrev rationalPointStalkFunctor (x : Spec (.of k) ⟶ X) :
    EtaleModules.{u, r} Λ X ⥤ ModuleCat.{max (u + 1) r} Λ :=
  (Scheme.pointSmallEtale (Stacks.Frobenius.rationalGeometricPoint kbar x).hom).sheafFiber

/-- The étale stalk functor on sheaves of modules is additive, being left exact. -/
public instance rationalPointStalkFunctor_additive (x : Spec (.of k) ⟶ X) :
    (rationalPointStalkFunctor.{u, r} Λ kbar x).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **The stalk `K_x̄`** of a bounded below complex `K` of sheaves of `Λ`-modules at the
geometric point over a rational point `x`, taken degreewise.  The étale stalk functor is exact,
so this computes the derived stalk. -/
public def rationalPointStalkComplex (x : Spec (.of k) ⟶ X)
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ :=
  ((rationalPointStalkFunctor.{u, r} Λ kbar x).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((CochainComplex.Plus.ι _).obj K)

variable [Fintype k] (p q : ℕ) [Fact p.Prime] [CharP kbar p]

/-- **The endomorphism `π_x` of `K_x̄`**: degreewise the geometric Frobenius of
[Stacks, Tag 03SW] at the rational point `x`, which is the action of the inverse of the
arithmetic Frobenius of `k̄` over `k` on the étale stalk there.  It commutes with the
differentials because the geometric Frobenius is a natural transformation of the stalk
functor. -/
public def rationalPointStalkFrobenius (hcard : Fintype.card k = p ^ q)
    (x : Spec (.of k) ⟶ X) (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X)) :
    rationalPointStalkComplex.{u, r} Λ kbar x K ⟶
      rationalPointStalkComplex.{u, r} Λ kbar x K :=
  (NatTrans.mapHomologicalComplex
      (Stacks.Frobenius.geometricFrobeniusStalkFunctor (ModuleCat.{max (u + 1) r} Λ) kbar p q
        hcard x)
      (ComplexShape.up ℤ)).app ((CochainComplex.Plus.ι _).obj K)

variable [Finite Λ]

/-- **The datum of [Stacks, Tag 03TY] produced from the geometry.**  For each `k`-rational point
`x` of `X` it is the stalk `K_x̄` of the coefficient complex at the geometric point over `x`,
perfect over `Λ` by hypothesis, together with the geometric Frobenius `π_x` acting on it. -/
public def geometricFrobeniusStalkDatum (hcard : Fintype.card k = p ^ q)
    (f : X ⟶ Spec (.of k)) (K : CochainComplex.Plus (EtaleModules.{u, r} Λ X))
    (hstalkPerfect : ∀ x : rationalPoints f, StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, r} Λ kbar x.1 K))) :
    FrobeniusActionOnStalks.{r, max (u + 1) r, u} Λ (rationalPoints f) where
  stalk x := ⟨DerivedCategory.Q.obj (rationalPointStalkComplex.{u, r} Λ kbar x.1 K),
    hstalkPerfect x⟩
  frobeniusAction x :=
    DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, r} Λ kbar p q hcard x.1 K)

end Stalk

/-! ### Restriction of the coefficient complex to the base change -/

section Restriction

variable (Λ : Type r) [Ring Λ] {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- Inverse image of a bounded below complex of sheaves of `Λ`-modules along a morphism of
schemes, taken degreewise.  Inverse image is additive, so it preserves zero objects, and a
degreewise bound below is therefore preserved. -/
public def etaleModuleInverseImagePlus :
    CochainComplex.Plus (EtaleModules.{u, r} Λ X) ⥤
      CochainComplex.Plus (EtaleModules.{u, r} Λ Y) :=
  ObjectProperty.lift _
    (CochainComplex.Plus.ι _ ⋙
      (etaleModuleInverseImage.{u, r} Λ g).mapHomologicalComplex (ComplexShape.up ℤ))
    (by
      rintro ⟨K, n, hn⟩
      refine ⟨n, ?_⟩
      rw [CochainComplex.isStrictlyGE_iff]
      intro i hi
      exact Functor.map_isZero _ (CochainComplex.isZero_of_isStrictlyGE K n i hi))

end Restriction

section BaseChange

variable (Λ : Type r) [Ring Λ] {k : Type u} [Field k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

/-- **The restriction `K|_{X_k̄}`** of the coefficient complex to the base change of `X` to an
extension field `k̄`, as an object of the bounded below derived category: the degreewise inverse
image along the projection `X_k̄ ⟶ X`.  This is the coefficient object that
`RΓ_c(X_k̄, -)` is applied to. -/
public def baseChangeCoefficients (K : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left)) :
    DerivedCategory.Plus
      (EtaleModules.{u, r} Λ (Stacks.Frobenius.fieldBaseChange Y kbar)) :=
  DerivedCategory.Plus.Q.obj
    ((etaleModuleInverseImagePlus.{u, r} Λ
      (pullback.fst Y.hom (Stacks.Frobenius.specAlgebraMap k kbar))).obj K)

end BaseChange

/-! ### The trace formula -/

/-- **The trace formula in dimension at most one (Stacks 03UG).**  Let `k` be a finite field
with `p ^ q` elements, let `k̄` be an algebraically closed extension of `k`, let `X` be a
separated scheme of finite type over `k` of dimension at most one, let `Λ` be a finite ring
whose cardinality is prime to that of `k`, and let `K` be a bounded below complex of sheaves of
`Λ`-modules on the small étale site of `X`.  Then

`Tr(π_X^* | RΓ_c(X_k̄, K)) = ∑_{x ∈ X(k)} Tr(π_x | K_x̄)`

in `Λ^natural`, the left hand side being the trace of the action induced on
`RΓ_c(X_k̄, K|_{X_k̄})` by an extension of the geometric Frobenius `π_X × id` of
[Stacks, Tag 03SQ] to a compactification of `X_k̄` over `Spec k̄`, and the right hand side the
sum over the rational points of the traces of the geometric Frobenius of [Stacks, Tag 03SW] on
the stalks of `K` at the geometric points above them.

Perfectness of `RΓ_c(X_k̄, K|_{X_k̄})` and of each stalk, finiteness of `X(k)`, the dévissage of
Step 1 of the source with the identification of its graded pieces, and the Galois decomposition
of Steps 7 to 9 are hypotheses; the implementation notes of this file record what each of them
is and what remains unformalized. -/
@[stacks 03UG "RESTRICTED: 03UH with both sides built from the scheme; the extra hypotheses are \
03TV as hperf and hstalkPerfect (K is a bounded below complex of étale sheaves of modules \
rather than an object of the D_ctf of 03TQ: the two small étale sites are identified by \
SmallEtale.sheafEquiv, but the transport of finite Tor dimension across it and the direction \
(1) => (2) of 03TT are missing), finiteness of X(k), the Step 1 dévissage with the \
identification of its pieces (devissage, hglobal, hstalk), and the Steps 7 to 9 Galois \
decomposition feeding 03TZ \
(hdecomposition, hdivisible, hannihilate, hlevel); Steps 3 to 6 are not formalized"]
public theorem compactSupportLefschetzNumber_eq_localLefschetzNumber
    {k : Type u} [Field k] [Fintype k] {p q : ℕ} [Fact p.Prime] [CharP k p]
    (hcard : Fintype.card k = p ^ q) (Y : Over (Spec (.of k)))
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (_hdim : topologicalKrullDim Y.left ≤ 1)
    (kbar : Type u) [Field kbar] [IsAlgClosed kbar] [Algebra k kbar] [CharP kbar p]
    (Λ : Type r) [Ring Λ] [Finite Λ]
    (_hcoprime : Nat.Coprime (Nat.card Λ) (Fintype.card k))
    (K : CochainComplex.Plus (EtaleModules.{u, r} Λ Y.left))
    [Fintype (rationalPoints Y.hom)]
    (j : CompactificationOf
      (Over.mk (pullback.snd Y.hom (Stacks.Frobenius.specAlgebraMap k kbar))))
    (E : CompactificationEndomorphism j
      (Stacks.Frobenius.geometricFrobeniusBaseChange Y kbar p q hcard))
    (γ : 𝟭 (DerivedCategory.Plus (EtaleModules.{u, r} Λ j.space)) ⟶
      etaleModuleDerivedDirectImage.{u, r} Λ E.hom)
    (hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((compactlySupportedCohomology.{u, r} kbar
          (pullback.snd Y.hom (Stacks.Frobenius.specAlgebraMap k kbar)) j Λ).obj
        (baseChangeCoefficients.{u, r} Λ Y kbar K))))
    (hstalkPerfect : ∀ x : rationalPoints Y.hom, StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Q.obj (rationalPointStalkComplex.{u, r} Λ kbar x.1 K)))
    (devissage : LefschetzDevissage.{r, max (u + 1) r, u} Λ (rationalPoints Y.hom))
    (hglobal : devissage.globalDatum =
      frobeniusActionOnCompactSupport.{u, r} Λ E γ
        (baseChangeCoefficients.{u, r} Λ Y kbar K) hperf)
    (hstalk : devissage.stalkDatum =
      geometricFrobeniusStalkDatum.{u, r} Λ kbar p q hcard Y.hom K hstalkPerfect)
    (group : Type t) [Fintype group] (prime exponent level : ℕ)
    (stabilizerExponent : group → ℕ) (coefficientTrace : group → ℤ)
    (moduleTrace : group → AdditiveCommutatorQuotient Λ)
    (hprime : Nat.Prime prime)
    (hannihilate : ∀ y : AdditiveCommutatorQuotient Λ, ((prime : ℤ) ^ exponent) • y = 0)
    (hlevel : ∀ g : group, stabilizerExponent g + exponent ≤ level)
    (hdecomposition : globalLefschetzNumber Λ devissage.openDatum =
      ∑ g : group, coefficientTrace g • moduleTrace g)
    (hdivisible : ∀ g : group, ((prime : ℤ) ^ level) ∣
      ((prime : ℤ) ^ stabilizerExponent g) * coefficientTrace g) :
    compactSupportLefschetzNumber.{u, r} Λ E γ
        (baseChangeCoefficients.{u, r} Λ Y kbar K) hperf =
      localLefschetzNumber Λ (rationalPoints Y.hom)
        (geometricFrobeniusStalkDatum.{u, r} Λ kbar p q hcard Y.hom K hstalkPerfect) := by
  have hne : ((prime : ℤ)) ≠ 0 := by exact_mod_cast hprime.ne_zero
  have hdvd : ∀ g : group, ((prime : ℤ) ^ exponent) ∣ coefficientTrace g := by
    intro g
    have h : ((prime : ℤ) ^ stabilizerExponent g * (prime : ℤ) ^ exponent) ∣
        ((prime : ℤ) ^ stabilizerExponent g * coefficientTrace g) := by
      rw [← pow_add]
      exact dvd_trans (pow_dvd_pow _ (hlevel g)) (hdivisible g)
    exact (mul_dvd_mul_iff_left (pow_ne_zero _ hne)).mp h
  have hopen : globalLefschetzNumber Λ devissage.openDatum = 0 := by
    rw [hdecomposition]
    refine Finset.sum_eq_zero fun g _ => ?_
    obtain ⟨c, hc⟩ := hdvd g
    calc coefficientTrace g • moduleTrace g
        = (c * (prime : ℤ) ^ exponent) • moduleTrace g := by rw [hc, mul_comm]
      _ = c • (((prime : ℤ) ^ exponent) • moduleTrace g) := mul_smul _ _ _
      _ = 0 := by rw [hannihilate, smul_zero]
  have key := devissage.globalLefschetzNumber_eq_localLefschetzNumber_of_openDatum_eq_zero hopen
  rw [hglobal, hstalk] at key
  exact key

end Stacks.EtaleCohomology

end
