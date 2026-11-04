module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf

/-!
# The twisted inverse image, the relative dualizing complex and the relative dualizing module

Let `f : X ⟶ Y` be a morphism of schemes along which derived direct image preserves
quasi-coherence of cohomology, and suppose the restricted functor
`Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` has a right adjoint. That right adjoint is the *twisted
inverse image* `f^×` of [Stacks, Tag 0A9E]; on a proper morphism it is the exceptional inverse
image `f^!` of [Stacks, Tag 0AU3]. Applying it to an object `ω_Y^•` of `D_QCoh(𝒪_Y)` produces the
relative dualizing complex `ω_X^• = f^! ω_Y^•`, and its cohomology sheaf in degree minus the
dimension of `X` is the relative dualizing module `ω_X` of [Stacks, Tag 0AWI].

The two inputs are explicit arguments rather than global facts: `hpush` because the restricted
functor cannot be written down without it, and adjointness because [Stacks, Tag 0A9E] is not
available here at this generality. This is the interface
`StacksFrontier/AlgebraicGeometry/Duality/QuasiCoherentPushforwardAdjoint.lean` already uses, and
`Stacks.Duality.DerivedPushforward.isLeftAdjoint_quasiCoherentDerivedPushforward_of_generator`
is the statement that produces the instance from a compact generating family.

## Main definitions

* `Stacks.Duality.twistedInverseImage` — the right adjoint `f^×` of the restriction of `Rf_*` to
  complexes with quasi-coherent cohomology.
* `Stacks.Duality.relativeDualizingComplex` — `ω_X^• = f^! ω_Y^•`, the value of `f^×` on a chosen
  object of `D_QCoh(𝒪_Y)`.
* `Stacks.Duality.relativeDualizingModule` — `ω_X = H^{-dim(X)}(ω_X^•)`, the cohomology sheaf of
  the relative dualizing complex in degree minus the dimension of `X`.

## Main results

* `Stacks.Duality.relativeDualizingComplexHomEquiv` — the duality isomorphism
  `Hom_X(K, ω_X^•) ≃ Hom_Y(Rf_* K, ω_Y^•)` for each `K`. This is the adjunction read on Hom-sets,
  and it is the fourth equality in the proof of [Stacks, Tag 0AWP].
* `Stacks.Duality.relativeDualizingComplexTrace` — the trace `Rf_* ω_X^• ⟶ ω_Y^•`, the counit of
  the adjunction at `ω_Y^•`.
* `Stacks.Duality.relativeDualizingComplexHomEquiv_symm_apply` and
  `Stacks.Duality.relativeDualizingComplexHomEquiv_apply` — the duality isomorphism is given in
  both directions by composing with the trace, respectively with the unit.
* `Stacks.Duality.isQuasicoherent_relativeDualizingModule` — `ω_X` is quasi-coherent. This holds
  for every base and every `ω_Y^•`, with no properness and no dualizing hypothesis: it is read
  off the defining property of `D_QCoh(𝒪_X)`, in which `ω_X^•` lives by construction. It is the
  part of the assertion of [Stacks, Tag 0AWI] that `ω_X` is a coherent sheaf which the
  construction alone supplies; coherence needs the dualizing half of the example, and is
  `Stacks.Duality.isCoherent_relativeDualizingModule` in
  `StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/ModuleCoherence.lean`.

## Implementation notes

The morphism universe `w` of the derived categories is left free, as in
`QuasiCoherentPushforwardAdjoint.lean`, rather than fixed by `HasDerivedCategory.standard`. That
file records why this is forced rather than a matter of taste: at the standard model the morphisms
of `D(𝒪_X)` live one universe above the objects, and a `Type (u + 1)`-indexed family of sheaves of
`𝒪_X`-modules has no direct sum, so the `HasCoproducts.{w}` hypothesis of Brown representability
is false rather than unavailable. `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` is the
instance that specialises everything here to `w = u`, and it is the one under which
`AlgebraicGeometry.derivedTilde` identifies `D(A)` with `D_QCoh(𝒪_{Spec A})`.

The base is a general morphism of schemes, where [Stacks, Tag 0AWI] takes `Y = Spec(A)` for a
Noetherian local ring `A`: nothing in the *construction* of `ω_X^•` or `ω_X` uses the base, and
the properties the example asserts — that `ω_X^•` is dualizing, that `ω_X` is coherent, and the
location of the first nonvanishing cohomology — are separate statements which are not proved here.
For a proper `f : X ⟶ Spec(A)` over a Noetherian ring the three instances that the definitions
below need beyond the two explicit arguments are `QuasiCompact.compactSpace_of_compactSpace f`,
`quasiSeparatedSpace_of_quasiSeparated f` and `LocallyOfFiniteType.isLocallyNoetherian f`.

`ENat.toNat ((topologicalKrullDim X).getD 0)` is the dimension of `X` as a natural number; it
agrees with `dim(X)` whenever that is finite, and is `0` on the empty scheme, all of whose
cohomology sheaves vanish.

Tag 0AWI asserts four things beyond the definition of `ω_X` — that `ω_X^• = f^! ω_S^•` is a
dualizing complex, that `ω_X` is coherent, and that `ω_X` is the first nonvanishing cohomology
sheaf from both sides. None of those four is proved here, so the tag attribute on
`Stacks.Duality.relativeDualizingModule` carries the clause label "relative dualizing module:
definition only": it claims the definitional clause of the example and nothing else. The
scheme-level notion of a dualizing complex is
`Stacks.Duality.IsDualizingComplex` of
`StacksFrontier/AlgebraicGeometry/Duality/RelativeDualizing/DualizingComplexScheme.lean`
([Stacks, Tag 0A87]), so the remaining three clauses can be *stated* in this repository; what is
missing is their proofs, which in the source rest on [Stacks, Tag 0AU3].

No attribute is attached for Tag 0A9E on `Stacks.Duality.twistedInverseImage`: the adjointness
that tag asserts is a hypothesis here, not a theorem, so no clause of it is discharged.

## References

* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0AU3](https://stacks.math.columbia.edu/tag/0AU3)
* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0AWP](https://stacks.math.columbia.edu/tag/0AWP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe w u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w} Y.Modules]
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)

section TwistedInverseImage

variable [(quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint]

/-- **The twisted inverse image `f^×`** of [Stacks, Tag 0A9E]: the right adjoint to the
restriction of derived direct image to the complexes with quasi-coherent cohomology. For a proper
morphism this is the exceptional inverse image `f^!` of [Stacks, Tag 0AU3]. -/
def twistedInverseImage :
    quasiCoherentDerivedCategory Y ⥤ quasiCoherentDerivedCategory X :=
  (quasiCoherentDerivedPushforward f hpush).rightAdjoint

/-- The adjunction `Rf_* ⊣ f^×` exhibiting `Stacks.Duality.twistedInverseImage` as the right
adjoint of the restricted derived direct image. -/
def twistedInverseImageAdjunction :
    quasiCoherentDerivedPushforward f hpush ⊣ twistedInverseImage f hpush :=
  Adjunction.ofIsLeftAdjoint (quasiCoherentDerivedPushforward f hpush)

/-- **The relative dualizing complex `ω_X^• = f^! ω_Y^•`** of [Stacks, Tag 0AWI]: the value of
the twisted inverse image on a chosen object of `D_QCoh(𝒪_Y)`. Over `Y = Spec(A)` with `A` a
Noetherian local ring, taking `ω_Y^•` to correspond to a normalized dualizing complex `ω_A^•`
under `AlgebraicGeometry.derivedTilde` is the situation of that example. -/
def relativeDualizingComplex (ωY : quasiCoherentDerivedCategory Y) :
    quasiCoherentDerivedCategory X :=
  (twistedInverseImage f hpush).obj ωY

/-- **The relative dualizing module `ω_X = H^{-dim(X)}(ω_X^•)`** of [Stacks, Tag 0AWI]: the
cohomology sheaf of the relative dualizing complex in degree minus the dimension of `X`. -/
@[stacks 0AWI "relative dualizing module: definition only"]
def relativeDualizingModule (ωY : quasiCoherentDerivedCategory Y) : X.Modules :=
  (DerivedCategory.homologyFunctor X.Modules
    (-(ENat.toNat ((topologicalKrullDim X).getD 0) : ℤ))).obj
      (relativeDualizingComplex f hpush ωY).obj

/-- The relative dualizing module is quasi-coherent: the relative dualizing complex lies in
`D_QCoh(𝒪_X)`, whose defining property is that every cohomology sheaf is quasi-coherent. -/
theorem isQuasicoherent_relativeDualizingModule (ωY : quasiCoherentDerivedCategory Y) :
    (relativeDualizingModule f hpush ωY).IsQuasicoherent :=
  (relativeDualizingComplex f hpush ωY).property _

end TwistedInverseImage

section Duality

variable [(quasiCoherentDerivedPushforward f hpush).IsLeftAdjoint]
  (ωY : quasiCoherentDerivedCategory Y)

/-- **The duality isomorphism `Hom_X(K, ω_X^•) ≃ Hom_Y(Rf_* K, ω_Y^•)`.** This is the defining
property of the relative dualizing complex, and it is the fourth equality in the proof of
[Stacks, Tag 0AWP]. -/
def relativeDualizingComplexHomEquiv (K : quasiCoherentDerivedCategory X) :
    (K ⟶ relativeDualizingComplex f hpush ωY) ≃
      ((quasiCoherentDerivedPushforward f hpush).obj K ⟶ ωY) :=
  ((twistedInverseImageAdjunction f hpush).homEquiv K ωY).symm

/-- **The trace map `Rf_* ω_X^• ⟶ ω_Y^•`**, the counit of `Rf_* ⊣ f^!` at `ω_Y^•`. -/
def relativeDualizingComplexTrace :
    (quasiCoherentDerivedPushforward f hpush).obj (relativeDualizingComplex f hpush ωY) ⟶ ωY :=
  (twistedInverseImageAdjunction f hpush).counit.app ωY

/-- A map into the relative dualizing complex is sent by the duality isomorphism to its direct
image followed by the trace. -/
@[simp]
theorem relativeDualizingComplexHomEquiv_apply (K : quasiCoherentDerivedCategory X)
    (u : K ⟶ relativeDualizingComplex f hpush ωY) :
    relativeDualizingComplexHomEquiv f hpush ωY K u =
      (quasiCoherentDerivedPushforward f hpush).map u ≫
        relativeDualizingComplexTrace f hpush ωY :=
  (twistedInverseImageAdjunction f hpush).homEquiv_counit K ωY u

/-- The inverse of the duality isomorphism is the unit of `Rf_* ⊣ f^!` followed by `f^!` of the
given map. -/
@[simp]
theorem relativeDualizingComplexHomEquiv_symm_apply (K : quasiCoherentDerivedCategory X)
    (v : (quasiCoherentDerivedPushforward f hpush).obj K ⟶ ωY) :
    (relativeDualizingComplexHomEquiv f hpush ωY K).symm v =
      (twistedInverseImageAdjunction f hpush).unit.app K ≫
        (twistedInverseImage f hpush).map v :=
  (twistedInverseImageAdjunction f hpush).homEquiv_unit K ωY v

end Duality

end Stacks.Duality

end
