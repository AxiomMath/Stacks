module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedPullback
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback

/-!
# Derived direct image commutes with the coherator

Let `f : X ⟶ Y` be a morphism of schemes and write `DQ_X : D(𝒪_X) ⥤ D_QCoh(𝒪_X)` for a right
adjoint of the inclusion `D_QCoh(𝒪_X) ⥤ D(𝒪_X)` — the *coherator* of `X`. Given such right
adjoints on both sides, the two functors `D(𝒪_X) ⥤ D_QCoh(𝒪_Y)`

  `Rf_* ∘ DQ_X`   and   `DQ_Y ∘ Rf_*`

are canonically isomorphic. The source writes this as an equality; it is an identification of two
right adjoints of one functor, so what it asserts is a canonical natural isomorphism and that is
what is constructed here.

The argument is adjunction uniqueness and nothing else. Derived pullback `Lf^*` carries
`D_QCoh(𝒪_Y)` into `D_QCoh(𝒪_X)`, so `Lf^* : D_QCoh(𝒪_Y) ⥤ D(𝒪_X)` factors through the inclusion
in two ways: as the restricted `Lf^*` followed by `D_QCoh(𝒪_X) ⥤ D(𝒪_X)`, and as the inclusion
`D_QCoh(𝒪_Y) ⥤ D(𝒪_Y)` followed by the ambient `Lf^*`. Composing the restricted adjunction
`Lf^* ⊣ Rf_*` on `D_QCoh` with `ι_X ⊣ DQ_X` exhibits `Rf_* ∘ DQ_X` as a right adjoint of the
first factorisation; composing `ι_Y ⊣ DQ_Y` with the ambient `Lf^* ⊣ Rf_*` exhibits
`DQ_Y ∘ Rf_*` as a right adjoint of the second. The two factorisations agree, so the two
composites are right adjoint to one functor and `CategoryTheory.Adjunction.rightAdjointUniq`
produces the comparison.

## Main definitions

* `Stacks.Duality.coheratorDerivedPushforwardIso` — the canonical natural isomorphism
  `Rf_* ∘ DQ_X ≅ DQ_Y ∘ Rf_*`.

## Main results

* `Stacks.Duality.coheratorDerivedPushforwardIso_homEquiv_symm_hom_app` — the comparison is the
  canonical one: its adjoint transpose is the counit of `ι_X ⊣ DQ_X`, so it is the unique natural
  transformation compatible with the two counits.

## Implementation notes

*The quasi-coherence hypotheses.* That `Lf^*` preserves quasi-coherence of cohomology is
[Stacks, Tag 08DW] part (1), available for every morphism of schemes as
`Stacks.Duality.isQuasicoherent_homology_derivedPullback'`, and it is discharged here. Its `Rf_*`
counterpart [Stacks, Tag 08D5] part (1) appears instead as the argument `hpush`, in the form used
throughout the `Stacks.Duality` namespace. It is exactly what quasi-compactness and
quasi-separatedness of `f` supply in the source — the step "the statement makes sense because
`Rf_*` sends `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`" — and it is what makes the composite
`Rf_* ∘ DQ_X` well formed at all, so taking it as an argument rather than deriving it from
`[QuasiCompact f] [QuasiSeparated f]` generalises the statement rather than restricting it. The
reason it is not derived is that the library's form of Tag 08D5 part (1)
(`AlgebraicGeometry.isQuasicoherent_derivedPushforward`) is stated at
`CategoryTheory.HasDerivedCategory.standard`, while the quasi-coherent derived categories of
`Stacks.Duality` are available only at the locally small model; a statement for one model says
nothing about the other.

*The model of the derived categories.* As in
`StacksFrontier/AlgebraicGeometry/Duality/TwistedInverseImage/QuasiCoherentPullback.lean`, the
statements here are at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, with no `[HasDerivedCategory.{w}]` binder:
the restricted derived pullback and the restricted adjunction it consumes exist only there. No
declaration here mentions `CategoryTheory.HasDerivedCategory.standard`.

*Why the comparison is canonical.* `Adjunction.rightAdjointUniq` is the conjugate of the identity
isomorphism of the common left adjoint, so the comparison is pinned down by compatibility with
the two counits; that characterisation is recorded below and is what identifies the isomorphism
with the source's equality sign.

## References

* [Stacks Project, Tag 0CR1](https://stacks.math.columbia.edu/tag/0CR1)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

universe u

namespace Stacks.Duality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (hpush : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (DQX : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X)
  (DQY : DerivedCategory Y.Modules ⥤ quasiCoherentDerivedCategory Y)
  (adjX : (DerivedCategoryB.derivedCategoryB
    (A := X.Modules) (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⊣ DQX)
  (adjY : (DerivedCategoryB.derivedCategoryB
    (A := Y.Modules) (SheafOfModules.isQuasicoherent Y.ringCatSheaf)).ι ⊣ DQY)

/-- `Rf_* ∘ DQ_X`, as a right adjoint of `Lf^* : D_QCoh(𝒪_Y) ⥤ D(𝒪_X)` factored through
`D_QCoh(𝒪_X)`: the restricted adjunction `Lf^* ⊣ Rf_*` on the quasi-coherent derived categories
composed with the coherator adjunction `ι_X ⊣ DQ_X` of `X`. -/
def coheratorCompDerivedPushforwardAdjunction :
    quasiCoherentDerivedPullback f (isQuasicoherent_homology_derivedPullback' f) ⋙
        (DerivedCategoryB.derivedCategoryB
          (A := X.Modules) (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⊣
      DQX ⋙ quasiCoherentDerivedPushforward f hpush :=
  (quasiCoherentDerivedAdjunction f (isQuasicoherent_homology_derivedPullback' f) hpush).comp adjX

/-- `DQ_Y ∘ Rf_*`, as a right adjoint of the same functor `Lf^* : D_QCoh(𝒪_Y) ⥤ D(𝒪_X)`: the
coherator adjunction `ι_Y ⊣ DQ_Y` of `Y` composed with the ambient adjunction `Lf^* ⊣ Rf_*`,
transported along the identification of `ι_Y ⋙ Lf^*` with the restricted `Lf^*` followed by
`ι_X`. -/
def derivedPushforwardCompCoheratorAdjunction :
    quasiCoherentDerivedPullback f (isQuasicoherent_homology_derivedPullback' f) ⋙
        (DerivedCategoryB.derivedCategoryB
          (A := X.Modules) (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ι ⊣
      derivedPushforward f ⋙ DQY :=
  (adjY.comp (derivedAdjunction f)).ofNatIsoLeft
    (quasiCoherentDerivedPullbackCompιIso f (isQuasicoherent_homology_derivedPullback' f)).symm

/-- **Derived direct image commutes with the coherator.** Let `f : X ⟶ Y` be a morphism of
schemes along which `Rf_*` preserves quasi-coherence of cohomology — as it does whenever `f` is
quasi-compact and quasi-separated, by [Stacks, Tag 08D5] part (1) — and suppose the inclusions
`D_QCoh ⥤ D` admit right adjoints `DQ_X` and `DQ_Y` on `X` and on `Y`. Then the two functors
`D(𝒪_X) ⥤ D_QCoh(𝒪_Y)` given by `Rf_* ∘ DQ_X` and by `DQ_Y ∘ Rf_*` are canonically isomorphic.

Both are right adjoint to `Lf^* : D_QCoh(𝒪_Y) ⥤ D(𝒪_X)`, which lands in `D_QCoh(𝒪_X)` by
[Stacks, Tag 08DW] part (1), so they are identified by uniqueness of right adjoints. -/
@[stacks 0CR1]
def coheratorDerivedPushforwardIso :
    DQX ⋙ quasiCoherentDerivedPushforward f hpush ≅ derivedPushforward f ⋙ DQY :=
  Adjunction.rightAdjointUniq
    (coheratorCompDerivedPushforwardAdjunction f hpush DQX adjX)
    (derivedPushforwardCompCoheratorAdjunction f DQY adjY)

/-- The comparison `Rf_* ∘ DQ_X ≅ DQ_Y ∘ Rf_*` is the canonical one: on every object of
`D(𝒪_X)` its transpose under the adjunction defining `DQ_Y ∘ Rf_*` is the counit of the
coherator adjunction of `X`, so the comparison is the unique natural transformation compatible
with the two counits. -/
theorem coheratorDerivedPushforwardIso_homEquiv_symm_hom_app (K : DerivedCategory X.Modules) :
    ((derivedPushforwardCompCoheratorAdjunction f DQY adjY).homEquiv _ _).symm
        ((coheratorDerivedPushforwardIso f hpush DQX DQY adjX adjY).hom.app K) =
      (coheratorCompDerivedPushforwardAdjunction f hpush DQX adjX).counit.app K :=
  Adjunction.homEquiv_symm_rightAdjointUniq_hom_app _ _ K

end Stacks.Duality

end
