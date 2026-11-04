module

public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrict
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tor dimension on a ringed space

Let `(X, 𝒪_X)` be a ringed space. An object `E` of `D(𝒪_X)` *has Tor amplitude in `[a, b]`* when
`H^i(E ⊗_{𝒪_X}^{L} ℱ) = 0` for every `𝒪_X`-module `ℱ` and every `i ∉ [a, b]`; it *has finite Tor
dimension* when some interval works; it *locally has finite Tor dimension* when `X` is covered by
opens on which the restriction of `E` has finite Tor dimension. An `𝒪_X`-module `ℱ` *has Tor
dimension at most `n`* when `ℱ[0]` has Tor amplitude in `[-n, 0]`.

Both tensor products exist in this development. The underived `- ⊗_{𝒪_X} -` is
`Stacks.SheafOfModules.Tensor.sheafTensor`, the sheafification of `U ↦ ℱ(U) ⊗_{𝒪_X(U)} 𝒢(U)`, and
the derived `- ⊗^{L}_{𝒪_X} -` on `D(𝒪_X)` is `Stacks.Cohomology.TorAmplitude.derTensor`, the
derived tensor product of Stacks 06YU read at the site of opens of `X`. **Stacks 08CG is therefore
stated unconditionally**, against those, in
`StacksFrontier/Topology/Sheaves/Cohomology/TorAmplitude/OnARingedSpace.lean`, and that is where the
`08CG` tags for the four clauses of Definition 20.48.1 sit.

What is parameterized is only the development in *this* file, which is deliberately more general:
rather than fixing the derived tensor product it quantifies over certificates for one, so a
statement universally quantified over certificates is strictly stronger than its Stacks source.
The certificate is supplied together with the data that pins it down as the genuine
`- ⊗^{L}_{𝒪_X} -`:
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring` bundles an underived tensor
bifunctor, a derived tensor bifunctor, the comparison natural transformation with termwise
underived tensoring, and the `CategoryTheory.Functor.IsLeftDerivedFunctor` certificate saying that
each `- ⊗^{L} ℱ[0]` *is* the total left derived functor of `- ⊗ ℱ`. This is the same device, one
level up, as `StacksDraft.TorAmplitude.CertifiedDerivedTensoring` for a commutative ring, and the
same device as `Stacks.Cohomology.TorAmplitude.derTensor` and
`Stacks.SheafOfModules.DerivedTensorProduct` use on a ringed space and on a ringed site
respectively.

## Main definitions

* `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring` is a derived tensor product on
  `D(𝒪_X)` certified as the total left derived functor of an underived tensor product.
* `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.HasTorAmplitudeIn` is Tor
  amplitude in `[a, b]`, Stacks 08CG (1).
* `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.HasFiniteTorDimension` is finite
  Tor dimension, Stacks 08CG (2).
* `AlgebraicGeometry.RingedSpace.LocallyHasFiniteTorDimension` is locally finite Tor dimension,
  Stacks 08CG (3).
* `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.HasTorDimensionLE` is Tor
  dimension at most `n` for an `𝒪_X`-module, the last sentence of Stacks 08CG.
* `AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection` is a certificate
  built from the first-projection bifunctor; it exists to witness that the hypothesis bundle is
  inhabited.

## Main results

* `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.hasTorAmplitudeIn_iff` and
  `AlgebraicGeometry.RingedSpace.locallyHasFiniteTorDimension_iff` expose the defining
  quantifiers, so a consumer need not unfold the definitions.
* `AlgebraicGeometry.RingedSpace.instNonemptyCertifiedDerivedSheafTensoring`: the hypothesis
  bundle is inhabited, so a statement quantified over certificates is not vacuous.
* `AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_firstProjection_iff` measures how degenerate
  that witness is, which is what bounds what may be universally quantified over certificates.

## Implementation notes

Every binder is at the `StrictlyPerfect.OXMod` spelling of the category of `𝒪`-modules, because
`AlgebraicGeometry.RingedSpace.derivedRestrictModules` — which is what `E|_{U_i}` means in part
(3) — is stated there, and because the development must not acquire a further spelling of the
structure sheaf of rings.

The certificate is deliberately *lean*: it carries the bifunctor, the comparison and the
`IsLeftDerivedFunctor` property and nothing else. Carrying more (K-flat comparisons,
triangulatedness in each variable) would be a strictly richer datum, and a definition
parameterized by a richer datum has fewer instantiations, so it would say less than Stacks 08CG
does.

Three consequences of the hypothesis form are worth recording, since they decide what may and may
not be proved on top of these definitions.

* The definitions are *parameterized* by a certificate, not quantified over certificates, so they
  are faithful to Stacks 08CG for each supplied derived tensor product and in particular for the
  genuine one. That instantiation is carried out, not merely described:
  `AlgebraicGeometry.RingedSpace.canonicalCertifiedDerivedSheafTensoring` has `tensor` the
  sheafification `Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf` of
  `U ↦ ℱ(U) ⊗_{𝒪_X(U)} 𝒢(U)`, which is Stacks' `- ⊗_{𝒪_X} -`, and `derivedTensor` the derived
  tensor product of Stacks 06YU; at it the four predicates of this file are the unconditional ones
  of `Stacks.Cohomology.TorAmplitude`, by
  `AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_canonicalCertificate_iff`,
  `hasFiniteTorDimension_canonicalCertificate_iff`, `hasTorDimensionLE_canonicalCertificate_iff`
  and `locallyHasFiniteTorDimension_canonicalCertificate_iff`, each by `Iff.rfl`.
* A statement *universally* quantified over certificates is strictly stronger than its Stacks
  source, so proving one proves the source; a statement *existentially* quantified over
  certificates is strictly weaker, and is not the source.
* `certifiedDerivedSheafTensoringOfFirstProjection` shows the bundle is inhabited. It is not the
  derived tensor product: its underived "tensor" is the first projection `(ℰ, ℱ) ↦ ℰ`. It is here
  only to make inhabitedness a theorem rather than an expectation, and it is simultaneously a
  warning: for it, `HasTorAmplitudeIn E a b` degenerates to "the cohomology of `E` vanishes
  outside `[a, b]`", so a universally quantified equivalence between a property of a morphism and
  locally finite Tor dimension cannot be true, and such an equivalence has to name the genuine
  certificate.

Stacks 08CG carries the standing hypothesis `a ≤ b` on the interval. It is omitted here, as it is
in `StacksDraft.TorAmplitude.HasTorAmplitude` for a ring: `a > b` makes `Set.Icc a b` empty and
the predicate then says that `E ⊗^{L} ℱ` is acyclic for every `ℱ`, which is a harmless reading,
and omitting the hypothesis keeps the predicate total.

## References

* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Tag 0652](https://stacks.math.columbia.edu/tag/0652)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe d d' u

namespace AlgebraicGeometry.RingedSpace

section Certificate

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- A derived tensor product on `D(𝒪_X)`, certified as the total left derived functor of an
underived tensor product of `𝒪_X`-modules.

There is no tensor product of sheaves of modules in Mathlib, so both the underived and the derived
operation are data here. What makes the datum *the* derived tensor product rather than an
arbitrary bifunctor is `isLeftDerived`: for every `𝒪_X`-module `ℱ`, the functor
`- ⊗^{L} ℱ[0]` together with `comparison ℱ` is the total left derived functor of `- ⊗ ℱ`. A total
left derived functor is unique up to canonical isomorphism, so the certificate determines
`derivedTensor` from `tensor` up to canonical isomorphism.

This is the ringed-space analogue of `StacksDraft.TorAmplitude.CertifiedDerivedTensoring`, whose
three fields it mirrors; the extra field `additive` is needed because `tensor` is data here,
whereas `StacksDraft.TorAmplitude.tensorModuleRight` is a definition with a global `Additive`
instance. -/
public structure CertifiedDerivedSheafTensoring where
  /-- The underived tensor product `- ⊗_{𝒪_X} -` of `𝒪_X`-modules. -/
  tensor : OXMod.{u, u} X ⥤ OXMod.{u, u} X ⥤ OXMod.{u, u} X
  /-- Tensoring with a fixed `𝒪_X`-module is additive, so that it acts on complexes. -/
  additive : ∀ F : OXMod.{u, u} X, (tensor.flip.obj F).Additive
  /-- The derived tensor product `- ⊗^{L}_{𝒪_X} -` on `D(𝒪_X)`. -/
  derivedTensor : DerivedCategory (OXMod.{u, u} X) ⥤ DerivedCategory (OXMod.{u, u} X) ⥤
    DerivedCategory (OXMod.{u, u} X)
  /-- Comparison of `- ⊗^{L} ℱ[0]` with termwise underived tensoring by `ℱ`. -/
  comparison : ∀ F : OXMod.{u, u} X,
    letI := additive F
    DerivedCategory.Q ⋙
        derivedTensor.flip.obj ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F) ⟶
      (tensor.flip.obj F).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  /-- The comparison exhibits `- ⊗^{L} ℱ[0]` as the total left derived functor of `- ⊗ ℱ`. This
  is what makes the datum the derived tensor product. -/
  isLeftDerived : ∀ F : OXMod.{u, u} X,
    letI := additive F
    (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F)).IsLeftDerivedFunctor
      (comparison F) (HomologicalComplex.quasiIso (OXMod.{u, u} X) (ComplexShape.up ℤ))

namespace CertifiedDerivedSheafTensoring

variable {X}

/-- **Stacks 08CG (1).** An object `E` of `D(𝒪_X)` *has Tor amplitude in `[a, b]`* if, for every
`𝒪_X`-module `ℱ` and every integer `i` outside `[a, b]`, the cohomology sheaf
`H^i(E ⊗^{L}_{𝒪_X} ℱ)` vanishes.

The derived tensor product is the one carried by `D`; see the implementation notes of this file
for what the certificate buys and for why the interval is not assumed nonempty. -/
@[stacks 08CG "tor amplitude in an interval",
  sga "6 I 5.2" "Tor-amp(F) ⊂ [m,n]",
  sga "4½ Rapport 4.5" "sheaf tor-dimension ≤ r", sga "4 XVII 4.1.9" "ringed space, (i)"]
public def HasTorAmplitudeIn (D : CertifiedDerivedSheafTensoring.{d, u} X)
    (E : DerivedCategory (OXMod.{u, u} X)) (a b : ℤ) : Prop :=
  ∀ (F : OXMod.{u, u} X) (i : ℤ), i ∉ Set.Icc a b →
    IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj
      ((D.derivedTensor.obj E).obj ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F)))

/-- The vanishing criterion defining Tor amplitude, so that a consumer can use the defining
quantifiers without unfolding the definition. -/
public theorem hasTorAmplitudeIn_iff (D : CertifiedDerivedSheafTensoring.{d, u} X)
    (E : DerivedCategory (OXMod.{u, u} X)) (a b : ℤ) :
    D.HasTorAmplitudeIn E a b ↔
      ∀ (F : OXMod.{u, u} X) (i : ℤ), i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj
          ((D.derivedTensor.obj E).obj
            ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F))) :=
  Iff.rfl

/-- **Stacks 08CG (2).** An object `E` of `D(𝒪_X)` *has finite Tor dimension* if it has Tor
amplitude in some interval `[a, b]`. -/
@[stacks 08CG "finite tor dimension",
  sga "6 I 5.2" "finite flat amplitude",
  sga "4½ Rapport 4.5" "sheaf case, finite"]
public def HasFiniteTorDimension (D : CertifiedDerivedSheafTensoring.{d, u} X)
    (E : DerivedCategory (OXMod.{u, u} X)) : Prop :=
  ∃ a b : ℤ, D.HasTorAmplitudeIn E a b

/-- **The last sentence of Stacks 08CG.** An `𝒪_X`-module `ℱ` *has Tor dimension at most `n`* if
`ℱ[0]`, viewed in `D(𝒪_X)`, has Tor amplitude in `[-n, 0]`. -/
@[stacks 08CG "tor dimension of a module",
  sga "4½ Rapport 4.5" "sheaf module case",
  sga "4 XVII 4.1.9" "ringed space, module"]
public def HasTorDimensionLE (D : CertifiedDerivedSheafTensoring.{d, u} X)
    (F : OXMod.{u, u} X) (n : ℤ) : Prop :=
  D.HasTorAmplitudeIn ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F) (-n) 0

end CertifiedDerivedSheafTensoring

end Certificate

/-! ### Locally finite Tor dimension

Part (3) of Stacks 08CG restricts `E` to the members of an open covering, so it needs a derived
tensor product on each open subspace, not just on `X`. The restriction functor is
`AlgebraicGeometry.RingedSpace.derivedRestrictModules`, which exists because restriction of
`𝒪`-modules to an open subspace is exact. -/

section Local

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u, u} X)]
  [∀ U : Opens X.carrier,
    HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]

/-- **Stacks 08CG (3).** An object `E` of `D(𝒪_X)` *locally has finite Tor dimension* if there is
an open covering `X = ⋃ U i` such that `E|_{U i}` has finite Tor dimension for every `i`.

A derived tensor product is needed on each open subspace, so the certificate is a family `D`
indexed by the opens of `X`; `E|_{U i}` is
`AlgebraicGeometry.RingedSpace.derivedRestrictModules`. -/
@[stacks 08CG "locally finite tor dimension"]
public def LocallyHasFiniteTorDimension
    (D : ∀ U : Opens X.carrier,
      CertifiedDerivedSheafTensoring.{d', u} (X.restrict U.isOpenEmbedding))
    (E : DerivedCategory (OXMod.{u, u} X)) : Prop :=
  ∃ (I : Type u) (U : I → Opens X.carrier), iSup U = ⊤ ∧
    ∀ i : I, (D (U i)).HasFiniteTorDimension ((derivedRestrictModules X (U i)).obj E)

/-- The open-cover criterion defining locally finite Tor dimension, so that a consumer can use
the defining quantifiers without unfolding the definition. -/
public theorem locallyHasFiniteTorDimension_iff
    (D : ∀ U : Opens X.carrier,
      CertifiedDerivedSheafTensoring.{d', u} (X.restrict U.isOpenEmbedding))
    (E : DerivedCategory (OXMod.{u, u} X)) :
    LocallyHasFiniteTorDimension X D E ↔
      ∃ (I : Type u) (U : I → Opens X.carrier), iSup U = ⊤ ∧
        ∀ i : I, (D (U i)).HasFiniteTorDimension ((derivedRestrictModules X (U i)).obj E) :=
  Iff.rfl

end Local

/-! ### The hypothesis bundle is inhabited

A predicate whose hypotheses cannot all be satisfied is useless, and worse, a theorem quantified
over such hypotheses is vacuously true. The certificate below settles the question: it is a
genuine `CertifiedDerivedSheafTensoring`, built from the first-projection bifunctor, whose
`IsLeftDerivedFunctor` field is discharged by
`CategoryTheory.Functor.isLeftDerivedFunctor_of_inverts` because the first projection is exact and
so needs no resolution.

It is emphatically *not* the derived tensor product; see the implementation notes of this file. -/

section Inhabited

variable (X : RingedSpace.{u, u}) [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- The first projection `(ℰ, ℱ) ↦ ℰ` on `𝒪_X`-modules, as a bifunctor: the constant-functor
functor. It stands in for an underived tensor product in
`AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection`. -/
public def firstProjectionBifunctor : OXMod.{u, u} X ⥤ OXMod.{u, u} X ⥤ OXMod.{u, u} X :=
  Functor.const (OXMod.{u, u} X) (C := OXMod.{u, u} X)

/-- The first projection on `D(𝒪_X)`, as a bifunctor. -/
public def derivedFirstProjectionBifunctor :
    DerivedCategory (OXMod.{u, u} X) ⥤ DerivedCategory (OXMod.{u, u} X) ⥤
      DerivedCategory (OXMod.{u, u} X) :=
  Functor.const (DerivedCategory (OXMod.{u, u} X)) (C := DerivedCategory (OXMod.{u, u} X))

/-- Projecting onto the first factor is additive: it is the identity functor. -/
public instance additive_firstProjectionBifunctor (F : OXMod.{u, u} X) :
    ((firstProjectionBifunctor X).flip.obj F).Additive :=
  inferInstanceAs (𝟭 (OXMod.{u, u} X)).Additive

/-- The comparison of the derived first projection with the underived one: both are the identity,
so the comparison is the identity natural transformation. -/
public def firstProjectionComparison (F : OXMod.{u, u} X) :
    DerivedCategory.Q ⋙
        (derivedFirstProjectionBifunctor X).flip.obj
          ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F) ⟶
      ((firstProjectionBifunctor X).flip.obj F).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q :=
  𝟙 _

/-- The identity functor of `D(𝒪_X)` is the total left derived functor of the identity functor of
`𝒪_X`-modules read on complexes: the comparison is an isomorphism and `DerivedCategory.Q` is the
localization at the quasi-isomorphisms, so
`CategoryTheory.Functor.isLeftDerivedFunctor_of_inverts` applies. -/
public theorem isLeftDerived_firstProjectionComparison (F : OXMod.{u, u} X) :
    ((derivedFirstProjectionBifunctor X).flip.obj
        ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj F)).IsLeftDerivedFunctor
      (firstProjectionComparison X F)
      (HomologicalComplex.quasiIso (OXMod.{u, u} X) (ComplexShape.up ℤ)) :=
  Functor.isLeftDerivedFunctor_of_inverts _ _ (Iso.refl _)

/-- **The hypothesis bundle of this file is inhabited.** A certificate built from the
first-projection bifunctor, which is exact, hence its own total left derived functor.

This is the non-vacuity witness for every statement quantified over
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring`, and nothing more: the operation it
certifies is `(ℰ, ℱ) ↦ ℰ`, not a tensor product, so for this certificate
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.HasTorAmplitudeIn E a b` says only
that the cohomology of `E` vanishes outside `[a, b]`. -/
public def certifiedDerivedSheafTensoringOfFirstProjection :
    CertifiedDerivedSheafTensoring.{d, u} X where
  tensor := firstProjectionBifunctor X
  additive := additive_firstProjectionBifunctor X
  derivedTensor := derivedFirstProjectionBifunctor X
  comparison := firstProjectionComparison X
  isLeftDerived := isLeftDerived_firstProjectionComparison X

/-- There is a certificate on every ringed space, so a statement quantified over
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring` is not vacuous. -/
public instance : Nonempty (CertifiedDerivedSheafTensoring.{d, u} X) :=
  ⟨certifiedDerivedSheafTensoringOfFirstProjection X⟩

/-- **How degenerate the non-vacuity witness is**, stated rather than asserted: at the
first-projection certificate, Tor amplitude in `[a, b]` says exactly that the cohomology of `E`
vanishes outside `[a, b]`.

This is the companion of
`AlgebraicGeometry.RingedSpace.certifiedDerivedSheafTensoringOfFirstProjection`: the certificate
proves that quantifying over certificates is not vacuous, and this lemma measures the price, namely
that a *universally* quantified statement must also hold for a predicate that sees only the
cohomology of `E`. Any equivalence whose other side is not a boundedness condition therefore has
to name the genuine derived tensor product and cannot be universally quantified. -/
public theorem hasTorAmplitudeIn_firstProjection_iff
    (E : DerivedCategory (OXMod.{u, u} X)) (a b : ℤ) :
    (certifiedDerivedSheafTensoringOfFirstProjection.{d, u} X).HasTorAmplitudeIn E a b ↔
      ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E) :=
  ⟨fun h i hi => h (structureModule X) i hi, fun h _ i hi => h i hi⟩

end Inhabited

end AlgebraicGeometry.RingedSpace

end
