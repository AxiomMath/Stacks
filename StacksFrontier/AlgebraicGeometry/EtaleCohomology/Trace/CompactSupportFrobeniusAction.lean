module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedDirectImageComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ArithmeticFrobeniusInverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GlobalLefschetzNumber

/-!
# The Frobenius action on cohomology with compact support

Let `X` be a separated finite type scheme over a field, let `j` be a compactification of `X`
over that field, and let `Λ` be a ring.  Cohomology with compact support
`RΓ_c(X, -) = RΓ(Spec k, R(fbar)_* ∘ Rj_!)` is the composite of three derived functors, and the
only one of them that sees an endomorphism of the geometry is the middle one.  Accordingly an
endomorphism `π` of `X` over the base which extends to the compactification, together with the
adjoint `M ⟶ Rπbar_* M` of the canonical map `πbar^{-1} M ⟶ M`, induces an endomorphism

`π_X^* : RΓ_c(X, M) ⟶ RΓ_c(X, M)`

natural in the coefficient object `M`.  Specialised to the base change `X_K` of a scheme over a
finite field `k` to an extension field `K` and to the geometric Frobenius `π_X × id` of
[Stacks, Tag 03SQ], this is the action whose trace is the global Lefschetz number of
[Stacks, Tag 03TX].  This file constructs the endomorphism, and bridges it to the datum
`Stacks.EtaleCohomology.FrobeniusActionOnCohomology` that the Lefschetz machinery consumes.

## Main definitions

* `Stacks.EtaleCohomology.CompactificationEndomorphism` — an endomorphism of a compactification
  over the base, extending a given endomorphism of the interior.
* `Stacks.EtaleCohomology.compactSupportPullback` — the induced endomorphism `π_X^*` of
  `RΓ_c(X, -)`, as a natural transformation.
* `Stacks.EtaleCohomology.compactSupportPullbackObj` — its value `π_X^*` at a coefficient
  object.
* `Stacks.EtaleCohomology.geometricFrobeniusCompactSupportPullback` — the case of the geometric
  Frobenius `π_X × id` acting on `RΓ_c(X_K, -)`.
* `Stacks.EtaleCohomology.frobeniusActionOnCompactSupport` — the bridge from the geometry to
  `Stacks.EtaleCohomology.FrobeniusActionOnCohomology`, given perfectness of `RΓ_c(X, M)` as a
  hypothesis.
* `Stacks.EtaleCohomology.compactSupportLefschetzNumber` — the trace
  `Tr(π_X^* | RΓ_c(X, M))` in the additive commutator quotient `Λ^natural`.

## Main results

* `Stacks.EtaleCohomology.compactSupportLefschetzNumber_eq_alternatingTrace` — the trace is the
  alternating sum of the traces of any cochain endomorphism representing `π_X^*` on any bounded
  finite-projective representative.

## Implementation notes

The extension `πbar` of `π` to the compactification is data, not a construction: a
compactification is an arbitrary scheme proper over the base into which `X` embeds, and nothing
makes an endomorphism of `X` extend to it.  The square
`CompactificationEndomorphism.immersion_comp_hom` is what records that `πbar` restricts to `π`
on the interior; the construction of `π_X^*` itself uses only
`CompactificationEndomorphism.hom_comp_toBase`, which is what makes `Rπbar_* ⋙ R(fbar)_*`
comparable with `R(fbar)_*`.

The canonical map of the source is `c_M : πbar^{-1} M ⟶ M`.  Inverse image along an arbitrary
morphism of schemes is not available for module coefficients in this development, so the datum
is taken in its adjoint form `M ⟶ Rπbar_* M`, and at the level of the whole functor, as a
transformation `𝟭 ⟶ Rπbar_*`; this is what makes `π_X^*` natural in `M`.

Preservation of injective objects by `πbar_*` is not a hypothesis: it holds for the direct
image of sheaves of modules along every morphism of schemes, by
`Stacks.EtaleCohomology.etaleModuleDirectImage_preservesInjectiveObjects`, because the inverse
image `πbar^{-1}` of sheaves of modules is exact.  No equivalence of small étale sites is
needed, so nothing here asks `πbar` to be a Frobenius.

Finite type, quasi-compactness and separatedness of the structure morphism are absent here for
the same reason they are absent from the signature of
`Stacks.EtaleCohomology.compactlySupportedCohomology`: the formula uses none of them, so none
of them appears in the elaborated type of the functor these constructions act on.

Perfectness of `RΓ_c(X, M)` is likewise a named hypothesis of the bridge, rather than derived.
The corresponding statement for cohomology *without* supports is [Stacks, Tag 03TV], and that
one *is* available: it is proved as
`Stacks.EtaleCohomology.CurveGlobalSections.isPerfect` in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/Trace/CurveGlobalSections.lean`, for a projective
curve in a big étale site with coefficients in `D_ctf(X_étale, Λ)`.  Two things, not its absence,
keep it from discharging `hperf` here.  First, it is a statement about
`Stacks.EtaleCohomology.smallEtaleModuleDerivedGlobalSections`, that is about `RΓ(X_k̄, K)`,
whereas `hperf` asks for `RΓ_c(X_k̄, K)`; the two agree for a proper `X`, which the source uses,
but this development has no comparison of `Stacks.EtaleCohomology.compactlySupportedCohomology`
with derived global sections.  Second, it lives in the other of the two presentations of the
small étale site used here: it is indexed by a `Stacks.BigEtaleSite` and an object of its
`B.Scheme`, with sheaves on `Stacks.SmallEtale.topology B X.obj X.property`, while
`compactlySupportedCohomology` is a functor on `DerivedCategory.Plus (EtaleModules Λ X)` for a
`Scheme`, built from `Scheme.smallEtaleTopology`.  So what is missing is a bridge between the
two idioms together with the comparison of `RΓ_c` and `RΓ` in the proper case, not the
perfectness theorem.

## References

* [Stacks Project, Tag 03SQ](https://stacks.math.columbia.edu/tag/03SQ)
* [Stacks Project, Tag 03TV](https://stacks.math.columbia.edu/tag/03TV)
* [Stacks Project, Tag 03TX](https://stacks.math.columbia.edu/tag/03TX)
* [Stacks Project, Tag 0GJZ](https://stacks.math.columbia.edu/tag/0GJZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### Endomorphisms of a compactification -/

section Setup

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}

/-- An endomorphism of a compactification `j` of `X` over the base, extending an endomorphism
`π` of `X`.  The first condition says the endomorphism is a morphism over the base, the second
that it restricts to `π` through the open immersion. -/
public structure CompactificationEndomorphism (j : CompactificationOf (Over.mk f))
    (π : X ⟶ X) where
  /-- The endomorphism of the ambient proper scheme. -/
  hom : j.space ⟶ j.space
  /-- The endomorphism is a morphism over the base. -/
  hom_comp_toBase : hom ≫ j.toBase = j.toBase
  /-- The endomorphism restricts to `π` on the interior. -/
  immersion_comp_hom : j.immersion ≫ hom = π ≫ j.immersion

variable {j : CompactificationOf (Over.mk f)} {π : X ⟶ X}

/-- **The endomorphism `π_X^*` of cohomology with compact support induced by an endomorphism of
a compactification.**  It is the endomorphism of `R(fbar)_*` of
`Stacks.EtaleCohomology.etaleModuleDerivedDirectImageEndomorphism`, inserted between `Rj_!` and
`RΓ(Spec k, -)` in `RΓ_c(X, -) = RΓ(Spec k, R(fbar)_* ∘ Rj_!)`.

The transformation `γ : 𝟭 ⟶ Rπbar_*` is the adjoint form of the canonical map
`c : πbar^{-1} ⟶ 𝟭`. -/
public def compactSupportPullback (Λ : Type r) [Ring Λ]
    (E : CompactificationEndomorphism j π)
    (γ : 𝟭 (DerivedCategory.Plus (EtaleModules.{u, r} Λ j.space)) ⟶
      etaleModuleDerivedDirectImage.{u, r} Λ E.hom) :
    compactlySupportedCohomology.{u, r} k f j Λ ⟶
      compactlySupportedCohomology.{u, r} k f j Λ :=
  Functor.whiskerRight
    (Functor.whiskerLeft (etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion)
      (etaleModuleDerivedDirectImageEndomorphism.{u, r} Λ E.hom j.toBase E.hom_comp_toBase γ))
    (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of k)))

/-- The value of `π_X^*` at a coefficient object `M`: an endomorphism of `RΓ_c(X, M)`. -/
public def compactSupportPullbackObj (Λ : Type r) [Ring Λ]
    (E : CompactificationEndomorphism j π)
    (γ : 𝟭 (DerivedCategory.Plus (EtaleModules.{u, r} Λ j.space)) ⟶
      etaleModuleDerivedDirectImage.{u, r} Λ E.hom)
    (M : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)) :
    (compactlySupportedCohomology.{u, r} k f j Λ).obj M ⟶
      (compactlySupportedCohomology.{u, r} k f j Λ).obj M :=
  (compactSupportPullback.{u, r} Λ E γ).app M

/-- `π_X^*` at `M` is `RΓ(Spec k, -)` applied to the endomorphism of `R(fbar)_*` at `Rj_! M`. -/
public lemma compactSupportPullbackObj_eq (Λ : Type r) [Ring Λ]
    (E : CompactificationEndomorphism j π)
    (γ : 𝟭 (DerivedCategory.Plus (EtaleModules.{u, r} Λ j.space)) ⟶
      etaleModuleDerivedDirectImage.{u, r} Λ E.hom)
    (M : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)) :
    compactSupportPullbackObj.{u, r} Λ E γ M =
      (etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of k))).map
        ((etaleModuleDerivedDirectImageEndomorphism.{u, r} Λ E.hom j.toBase
          E.hom_comp_toBase γ).app
            ((etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion).obj M)) :=
  rfl

/-! ### The bridge to the global Lefschetz number -/

variable (Λ : Type r) [Ring Λ] [Finite Λ]

/-- **The datum of [Stacks, Tag 03TX] produced from the geometry.**  Given an endomorphism of a
compactification of `X` over the base, the adjoint canonical map, a coefficient object `M`, and
perfectness of `RΓ_c(X, M)` as a complex of `Λ`-modules, this is the perfect object of `D(Λ)`
together with the endomorphism `π_X^*` of it.

Perfectness is a hypothesis.  Its analogue without supports, [Stacks, Tag 03TV] for a curve
with coefficients that are constructible of finite Tor dimension, is proved as
`Stacks.EtaleCohomology.CurveGlobalSections.isPerfect`; the implementation notes of this file
record why that theorem does not discharge `hperf`. -/
public def frobeniusActionOnCompactSupport
    (E : CompactificationEndomorphism j π)
    (γ : 𝟭 (DerivedCategory.Plus (EtaleModules.{u, r} Λ j.space)) ⟶
      etaleModuleDerivedDirectImage.{u, r} Λ E.hom)
    (M : DerivedCategory.Plus (EtaleModules.{u, r} Λ X))
    (hperf : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Plus.ι.obj ((compactlySupportedCohomology.{u, r} k f j Λ).obj M))) :
    FrobeniusActionOnCohomology.{r, max (u + 1) r} Λ where
  cohomology := ⟨_, hperf⟩
  frobeniusAction :=
    DerivedCategory.Plus.ι.map (compactSupportPullbackObj.{u, r} Λ E γ M)

/-- **`Tr(π_X^* | RΓ_c(X, M))`**, the trace of the induced endomorphism of cohomology with
compact support, an element of the additive commutator quotient `Λ^natural`.  This is the
global Lefschetz number of [Stacks, Tag 03TX] evaluated on the datum that the geometry
produces. -/
public def compactSupportLefschetzNumber
    (E : CompactificationEndomorphism j π)
    (γ : 𝟭 (DerivedCategory.Plus (EtaleModules.{u, r} Λ j.space)) ⟶
      etaleModuleDerivedDirectImage.{u, r} Λ E.hom)
    (M : DerivedCategory.Plus (EtaleModules.{u, r} Λ X))
    (hperf : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Plus.ι.obj ((compactlySupportedCohomology.{u, r} k f j Λ).obj M))) :
    CategoryTheory.FilteredDerived.AdditiveCommutatorQuotient Λ :=
  globalLefschetzNumber.{r, max (u + 1) r} Λ
    (frobeniusActionOnCompactSupport.{u, r} Λ E γ M hperf)

/-- The trace of `π_X^*` on `RΓ_c(X, M)` is the alternating sum of the traces of any cochain
endomorphism representing it on any bounded finite-projective representative. -/
public theorem compactSupportLefschetzNumber_eq_alternatingTrace
    (E : CompactificationEndomorphism j π)
    (γ : 𝟭 (DerivedCategory.Plus (EtaleModules.{u, r} Λ j.space)) ⟶
      etaleModuleDerivedDirectImage.{u, r} Λ E.hom)
    (M : DerivedCategory.Plus (EtaleModules.{u, r} Λ X))
    (hperf : StacksDraft.Perfect.IsPerfect
      (DerivedCategory.Plus.ι.obj ((compactlySupportedCohomology.{u, r} k f j Λ).obj M)))
    (P : CochainComplex (ModuleCat.{max (u + 1) r} Λ) ℤ)
    (hP : CategoryTheory.FilteredDerived.finiteProjectiveComplex Λ P)
    (e : DerivedCategory.Q.obj P ≅
      DerivedCategory.Plus.ι.obj ((compactlySupportedCohomology.{u, r} k f j Λ).obj M))
    (g : P ⟶ P)
    (hg : DerivedCategory.Q.map g = e.hom ≫
      DerivedCategory.Plus.ι.map (compactSupportPullbackObj.{u, r} Λ E γ M) ≫ e.inv) :
    compactSupportLefschetzNumber.{u, r} Λ E γ M hperf =
      CategoryTheory.FilteredDerived.alternatingTrace Λ P hP g :=
  globalLefschetzNumber_eq_alternatingTrace.{r, max (u + 1) r} Λ _ P hP e g hg

end Setup

/-! ### The geometric Frobenius -/

section GeometricFrobenius

variable {k : Type u} [Field k] [Fintype k] (X : Over (Spec (.of k)))
  (Kfield : Type u) [Field Kfield] [Algebra k Kfield] (p q : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ q)

/-- The geometric Frobenius `π_X × id` of [Stacks, Tag 03SQ] is an endomorphism of the base
change `X_K` over `Spec K`, so it is admissible input for
`Stacks.EtaleCohomology.CompactificationEndomorphism`. -/
public lemma geometricFrobeniusBaseChange_comp_structure :
    Stacks.Frobenius.geometricFrobeniusBaseChange X Kfield p q hcard ≫
        pullback.snd X.hom (Stacks.Frobenius.specAlgebraMap k Kfield) =
      pullback.snd X.hom (Stacks.Frobenius.specAlgebraMap k Kfield) :=
  Stacks.Frobenius.geometricFrobeniusBaseChange_comp_snd X Kfield p q hcard

/-- **The geometric Frobenius action on `RΓ_c(X_K, -)`.**  For `X` over a finite field `k` and
an extension field `K`, this is the endomorphism of cohomology with compact support of the base
change `X_K` induced by the geometric Frobenius `π_X × id` of [Stacks, Tag 03SQ], through an
extension of it to a compactification of `X_K` over `Spec K` and the adjoint canonical map.

For `K` an algebraic closure of `k` this is the `π_X^*` of [Stacks, Tag 03TX]. -/
public def geometricFrobeniusCompactSupportPullback
    (j : CompactificationOf
      (Over.mk (pullback.snd X.hom (Stacks.Frobenius.specAlgebraMap k Kfield))))
    (E : CompactificationEndomorphism j
      (Stacks.Frobenius.geometricFrobeniusBaseChange X Kfield p q hcard))
    (Λ : Type r) [Ring Λ]
    (γ : 𝟭 (DerivedCategory.Plus (EtaleModules.{u, r} Λ j.space)) ⟶
      etaleModuleDerivedDirectImage.{u, r} Λ E.hom) :
    compactlySupportedCohomology.{u, r} Kfield
        (pullback.snd X.hom (Stacks.Frobenius.specAlgebraMap k Kfield)) j Λ ⟶
      compactlySupportedCohomology.{u, r} Kfield
        (pullback.snd X.hom (Stacks.Frobenius.specAlgebraMap k Kfield)) j Λ :=
  compactSupportPullback.{u, r} Λ E γ

end GeometricFrobenius

end Stacks.EtaleCohomology

end
