module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.CoheratorQuasiInverse
public import StacksFrontier.AlgebraicGeometry.Spaces.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.CoheratorFlatPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedComparison

/-!
# The derived coherator as quasi-inverse of the comparison on an algebraic space

Let `X` be a quasi-compact, quasi-separated algebraic space over a scheme `S` contained in a big
fppf site `B`.  The inclusion `ι : QCoh(𝒪_X) ⥤ Mod(𝒪_X)` of the quasi-coherent modules is exact
and has a right adjoint, the coherator `C_X` (Stacks 077V, part (2)); write `RQ_X` for a total
right derived functor of `C_X`.  Stacks 08F1 provides the comparison functor

`i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)`

and [Stacks, Tag 09TG] asserts that, under a compatibility hypothesis on the derived direct
images from affine étale charts of the quasi-compact opens of `X`, this functor **is an
equivalence with quasi-inverse given by `RQ_X`**.  This file proves the *second* clause: once
`i_X` is known to be an equivalence, its quasi-inverse is `RQ_X` restricted to the complexes with
quasi-coherent cohomology — for an arbitrary algebraic space and an arbitrary right-derived model
of an arbitrary coherator.

The argument is the formal one, and is the one the scheme analogue
`Stacks.DerivedQCoh.derivedCoherator_isoInv` ([Stacks, Tag 09T6]) uses.  The coherator adjunction
`ι ⊣ C_X` derives to an adjunction between the functor of derived categories induced by the exact
`ι` and the derived functor `RQ_X` ([Stacks, Tag 09T5], available at arbitrary chosen models as
`Stacks.DerivedModel.adjunctionOfExact`).  Composing `i_X` with the inclusion
`J : D_QCoh(𝒪_X) ⥤ D(𝒪_X)` recovers that induced functor, by
`AlgebraicGeometry.Space.quasicoherentDerivedComparisonCompιIso`, so restricting the derived
adjunction along the fully faithful `J` exhibits `J ⋙ RQ_X` as a right adjoint of `i_X`.  A right
adjoint is unique up to a unique natural isomorphism, and the inverse of an equivalence is one of
its right adjoints.

## Main definitions

* `AlgebraicGeometry.Space.AffineEtaleDerivedPushforwardCompatible` — the *hypothesis* of
  [Stacks, Tag 09TG]: for every étale `j : V ⟶ W` with `W ⊆ X` a quasi-compact open subspace and
  `V` affine, the right derived functor `Φ : D(QCoh(𝒪_V)) ⥤ D(QCoh(𝒪_W))` of the left exact
  `j_* : QCoh(𝒪_V) ⥤ QCoh(𝒪_W)` fits into the source's commutative square
  `i_W ∘ Φ ≅ Rj_* ∘ i_V`.
* `AlgebraicGeometry.Space.derivedCoheratorAdjunction` — [Stacks, Tag 09T5] for `ι ⊣ C_X`: the
  functor of derived categories induced by the exact inclusion is left adjoint to `RQ_X`.
* `AlgebraicGeometry.Space.comparisonDerivedCoheratorAdjunction` — the comparison functor of
  Stacks 08F1 is left adjoint to the restricted derived coherator, **unconditionally**.

## Main results

* `AlgebraicGeometry.Space.derivedCoherator_isoInv` — **[Stacks, Tag 09TG], quasi-inverse
  clause**: if the comparison functor is an equivalence, then `J ⋙ RQ_X` is its inverse.
* `AlgebraicGeometry.Space.exists_rightDerivedCoherator` — a coherator of an algebraic space has
  a total right derived functor with its derivation unit; this is the anti-vacuity check for the
  `RQ_X` binders.

## What is proved and what is not

[Stacks, Tag 09TG] asserts, under `AffineEtaleDerivedPushforwardCompatible`, that `i_X` *is an
equivalence* and that its quasi-inverse *is* `RQ_X`.  Only the second clause is established here,
and it is established from the equivalence rather than from the affine-étale hypothesis: the
first clause is the source's induction over the elementary distinguished squares of `X` (Stacks
09IT) together with Stacks 08GG, 09T5, 08H0, 03M9, 07RB and 08GZ, and it is not carried out in
this file.  Accordingly the tag on `AlgebraicGeometry.Space.derivedCoherator_isoInv` carries the
qualifier `"quasi-inverse clause, given the equivalence"`, and
`AlgebraicGeometry.Space.AffineEtaleDerivedPushforwardCompatible` is recorded but **not**
consumed: it is the input of the clause that is missing, written out so that the missing clause
has a statement.

The engine of the quasi-inverse clause,
`AlgebraicGeometry.Space.comparisonDerivedCoheratorAdjunction`, is unconditional: no hypothesis
on `X` beyond those under which the comparison functor of Stacks 08F1 is defined, and no
hypothesis on the model of `RQ_X` beyond its being a total right derived functor of a coherator.
In particular neither quasi-compactness nor quasi-separatedness of `X` is used — in the source
they are there for the first clause — so they are not binders here, and the statements are about
every algebraic space.

## What is assumed

Two instance binders travel with every statement here, as they do with the comparison functor
of Stacks 08F1 itself: quasi-coherence of `𝒪_X`-modules is closed under kernels and under
cokernels.  These are two clauses of Stacks 03M1, which Stacks 08F1 assumes rather than states,
and together with the unconditional closure under finite direct sums
(`SheafOfModules.isQuasicoherentOnSite_isClosedUnderFiniteProducts`) they are what make
`QCoh(𝒪_X)` abelian and the inclusion exact, hence what makes `D(QCoh(𝒪_X))` — the source of the
comparison — exist at all.  At the module universe `u` of the schemes, where this file works,
both are unconditional theorems of the library
(`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_schemeUniverse` and
`AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`, registered for a bundled
algebraic space as instances in
`StacksFrontier/AlgebraicGeometry/Spaces/CoheratorFlatPushforward.lean`); they are carried as
binders, exactly as in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentDerivedComparison.lean`, so that no statement
here is about a different comparison functor than the tagged one of Stacks 08F1.  Closure under
extensions is not needed: it is
what makes quasi-coherence a weak Serre class, and the comparison functor does not ask for
that.

The coherator is a hypothesis rather than a chosen functor, as in
`StacksFrontier/AlgebraicGeometry/Spaces/CoheratorFlatPushforward.lean`: Stacks 077V, part (2) is
the *existence* of a right adjoint of `ι`, a functor chosen out of it depends on that choice, and
the source's "the right adjoint" is determined only up to a canonical isomorphism.  So a
coherator `C_X` with its adjunction is taken as data, and the statements are then about every
coherator rather than about one chosen one, which is stronger.  For the same reason `RQ_X` is a
hypothesis: an arbitrary functor equipped with its derivation unit relative to
`CategoryTheory.DerivedCategory.Q`.  That the hypotheses are satisfiable is
`AlgebraicGeometry.Space.exists_coheratorAdjunction_smallEtale` for the coherator and, for its
derived functor, the K-injective resolutions of
`AlgebraicGeometry.Space.exists_quasiIso_isKInjective_modules`.

## Implementation notes

The module universe is the universe `u` of the schemes and not a free one, for the reason it is
so in `StacksFrontier/AlgebraicGeometry/Spaces/CoheratorFlatPushforward.lean`: the derived
adjunction `Stacks.DerivedModel.adjunctionOfExact` needs `Mod(𝒪_X)` to be Grothendieck abelian,
which `AlgebraicGeometry.Space.isGrothendieckAbelian_modules` gives at `m = u`, and the direct
image `AlgebraicGeometry.Space.modulePushforward` appearing in the hypothesis exists only there.
The derived categories are the standard models, as they are in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentDerivedComparison.lean` and
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentDerivedCategory.lean`, since that is where the
comparison functor of Stacks 08F1 and the category `D_QCoh(𝒪_X)` of Stacks 071X are stated; the
chosen localization of the cochain complexes is therefore `CategoryTheory.DerivedCategory.Q`,
which is what `CategoryTheory.Functor.mapDerivedCategory` — and hence the comparison functor — is
built from.  The bridge from that choice to the arbitrary-model machinery is
`Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory`, a general statement about an
exact functor between abelian categories, reused here from the scheme side rather than restated.

`StacksFrontier/AlgebraicGeometry/Spaces/PseudoCoherentCohomologyUnconditional.lean` is imported for
`AlgebraicGeometry.Space.modules_abelian` alone: at the module universe of the schemes the
generic abelian structure on sheaves of modules is stated at a join of universes that is never
`u`, so instance search for `Abelian (Mod(𝒪_X))` ends in an unsolvable universe constraint
unless that named instance is in scope.

In `AlgebraicGeometry.Space.AffineEtaleDerivedPushforwardCompatible` a quasi-compact open
`W ⊆ X` is an algebraic space together with an open immersion into `X` and quasi-compactness of
its own space, and both derived functors are asserted to *exist*, each together with its
derivation unit, rather than being named: the source says "the right derived functor", which is
determined only up to canonical isomorphism.  The commutative square is stated after composing
with the fully faithful inclusions `J : D_QCoh ⥤ D`, i.e. as `Φ ⋙ i_W ⋙ J_W ≅ i_V ⋙ J_V ⋙ Rj_*`
with `Rj_*` on the ambient derived categories, so that no factorisation of `Rj_*` through
`D_QCoh(𝒪_W)` has to be chosen as part of the hypothesis.  That `j_*` carries quasi-coherent
modules to quasi-coherent modules — Stacks 03M9, which the source's `j` satisfies, being étale
with affine source and quasi-compact target — is quantified over as well, since it is what makes
`j_* : QCoh(𝒪_V) ⥤ QCoh(𝒪_W)` exist.

## References

* [Stacks Project, Tag 09TG](https://stacks.math.columbia.edu/tag/09TG)
* [Stacks Project, Tag 08F1](https://stacks.math.columbia.edu/tag/08F1)
* [Stacks Project, Tag 077V](https://stacks.math.columbia.edu/tag/077V)
* [Stacks Project, Tag 071X](https://stacks.math.columbia.edu/tag/071X)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 09T6](https://stacks.math.columbia.edu/tag/09T6)
* [Stacks Project, Tag 03M9](https://stacks.math.columbia.edu/tag/03M9)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

/-! ### The hypothesis of Stacks 09TG -/

section Hypothesis

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The hypothesis of [Stacks, Tag 09TG].**  For every étale morphism `j : V ⟶ W` of algebraic
spaces with `W ⊆ X` a quasi-compact open subspace and `V` affine, the right derived functor
`Φ : D(QCoh(𝒪_V)) ⥤ D(QCoh(𝒪_W))` of the left exact `j_* : QCoh(𝒪_V) ⥤ QCoh(𝒪_W)` fits into the
commutative diagram

```
D(QCoh(𝒪_V)) --i_V--> D_QCoh(𝒪_V)
     | Φ                  | Rj_*
     v                     v
D(QCoh(𝒪_W)) --i_W--> D_QCoh(𝒪_W)
```

where `i_V`, `i_W` are the comparison functors of Stacks 08F1 and `Rj_*` is a total right derived
functor of the direct image of all modules along `j`.

See "Implementation notes" in the module documentation for the shape of the quantification: both
derived functors are asserted to exist together with their derivation units rather than named,
the square is stated after composing with the fully faithful inclusions of `D_QCoh` into the
ambient derived categories, and the preservation of quasi-coherence by `j_*` (Stacks 03M9) is
quantified over, being what makes `j_* : QCoh(𝒪_V) ⥤ QCoh(𝒪_W)` exist. -/
def AffineEtaleDerivedPushforwardCompatible : Prop :=
  ∀ (W : AlgebraicSpaces B S hS) (jW : W ⟶ (⟨F, hF⟩ : AlgebraicSpaces B S hS)),
    IsOpenImmersion B S hS jW.hom → IsQuasiCompactSpace B S hS W.1 →
    ∀ (V : AlgebraicSpaces B S hS) (j : V ⟶ W), IsEtale B S hS j.hom →
      IsAffineSpace B S hS V.1 →
      ∀ hpush : PushforwardPreservesQuasicoherence B S hS j,
      ∃ (Rj : DerivedCategory (Modules.{u, u} B S hS V.1 V.2) ⥤
            DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
        (ηj : (modulePushforward B S hS j).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q (C := Modules.{u, u} B S hS W.1 W.2) ⟶
          DerivedCategory.Q (C := Modules.{u, u} B S hS V.1 V.2) ⋙ Rj)
        (Φ : DerivedCategory (QuasicoherentSheaves.{u, u} B S hS V.1 V.2) ⥤
            DerivedCategory (QuasicoherentSheaves.{u, u} B S hS W.1 W.2))
        (ηΦ : (quasicoherentPushforward B S hS j hpush).mapHomologicalComplex
              (ComplexShape.up ℤ) ⋙
            DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS W.1 W.2) ⟶
          DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS V.1 V.2) ⋙ Φ),
        Rj.IsRightDerivedFunctor ηj
            (HomologicalComplex.quasiIso (Modules.{u, u} B S hS V.1 V.2)
              (ComplexShape.up ℤ)) ∧
          Φ.IsRightDerivedFunctor ηΦ
            (HomologicalComplex.quasiIso (QuasicoherentSheaves.{u, u} B S hS V.1 V.2)
              (ComplexShape.up ℤ)) ∧
          Nonempty (Φ ⋙ quasicoherentDerivedComparison B S hS W.1 W.2 ⋙
              (DerivedCategoryB.derivedCategoryB
                (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
                  ((Stacks.SheafOfModules.Tensor.ringSheaf
                    (smallEtaleRingedSite B S hS W.1 W.2).O)))).ι ≅
            quasicoherentDerivedComparison B S hS V.1 V.2 ⋙
              (DerivedCategoryB.derivedCategoryB
                (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
                  ((Stacks.SheafOfModules.Tensor.ringSheaf
                    (smallEtaleRingedSite B S hS V.1 V.2).O)))).ι ⋙ Rj)

end Hypothesis

/-! ### The quasi-inverse clause -/

section QuasiInverse

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    [(SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderKernels]
    [(SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderCokernels]
    (CF : Modules.{u, u} B S hS F hF ⥤ QuasicoherentSheaves.{u, u} B S hS F hF)
    (adjF : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).ι ⊣ CF) [CF.Additive]
    (RQ : DerivedCategory (Modules.{u, u} B S hS F hF) ⥤
      DerivedCategory (QuasicoherentSheaves.{u, u} B S hS F hF))
    (RQUnit : CF.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS F hF) ⟶
      DerivedCategory.Q (C := Modules.{u, u} B S hS F hF) ⋙ RQ)
    [RQ.IsRightDerivedFunctor RQUnit
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ))]

open Stacks.Injectives.KInjectiveResolution in
/-- **The `RQ_X` hypothesis is satisfiable on every algebraic space.**  A coherator `C_X` of an
algebraic space has a total right derived functor relative to
`CategoryTheory.DerivedCategory.Q`, together with its derivation unit.

The `𝒪_X`-modules are Grothendieck abelian at the universe of the schemes, so every cochain
complex of them has a K-injective resolution (Stacks 079P) and
`Stacks.Injectives.KInjectiveResolution.hasRightDerivedFunctor_mapHomologicalComplex_comp_Q`
applies.  This is the anti-vacuity check for the `RQ`/`RQUnit` binders below. -/
theorem exists_rightDerivedCoherator :
    ∃ (RQ : DerivedCategory (Modules.{u, u} B S hS F hF) ⥤
        DerivedCategory (QuasicoherentSheaves.{u, u} B S hS F hF))
      (η : CF.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS F hF) ⟶
        DerivedCategory.Q (C := Modules.{u, u} B S hS F hF) ⋙ RQ),
      RQ.IsRightDerivedFunctor η
        (HomologicalComplex.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ)) :=
  let := isGrothendieckAbelian_modules B S hS F hF
  have := hasRightDerivedFunctor_mapHomologicalComplex_comp_Q
    (A := QuasicoherentSheaves.{u, u} B S hS F hF) CF
  ⟨(CF.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS F hF)).totalRightDerived
      (DerivedCategory.Q (C := Modules.{u, u} B S hS F hF))
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ)),
    (CF.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS F hF)).totalRightDerivedUnit
      (DerivedCategory.Q (C := Modules.{u, u} B S hS F hF))
      (HomologicalComplex.quasiIso (Modules.{u, u} B S hS F hF) (ComplexShape.up ℤ)),
    inferInstance⟩

/-- **[Stacks, Tag 09T5] for the coherator adjunction of an algebraic space.**  The functor of
chosen derived categories induced by the exact inclusion `ι : QCoh(𝒪_X) ⥤ Mod(𝒪_X)` is left
adjoint to any total right derived functor of a coherator `C_X`.

The modules on the small étale ringed site of an algebraic space are Grothendieck abelian at the
universe of the schemes, which is the one hypothesis of
`Stacks.DerivedModel.adjunctionOfExact` beyond exactness of the left adjoint. -/
def derivedCoheratorAdjunction :
    Stacks.DerivedModel.derivedFunctorOfExact
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι
        (DerivedCategory.Q (C := Modules.{u, u} B S hS F hF))
        (DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS F hF)) ⊣ RQ :=
  letI := isGrothendieckAbelian_modules B S hS F hF
  Stacks.DerivedModel.adjunctionOfExact
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι
    (DerivedCategory.Q (C := Modules.{u, u} B S hS F hF))
    (DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS F hF)) adjF RQ RQUnit

/-- Composing the comparison functor of Stacks 08F1 with the inclusion of the complexes with
quasi-coherent cohomology gives the functor of derived categories induced by the exact inclusion
of the quasi-coherent modules, in the arbitrary-model spelling.

It is `AlgebraicGeometry.Space.quasicoherentDerivedComparisonCompιIso` followed by the general
comparison `Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory` between the two
spellings of the induced functor of an exact functor. -/
def comparisonCompιIsoDerivedFunctorOfExact :
    quasicoherentDerivedComparison B S hS F hF ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))).ι ≅
      Stacks.DerivedModel.derivedFunctorOfExact
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι
        (DerivedCategory.Q (C := Modules.{u, u} B S hS F hF))
        (DerivedCategory.Q (C := QuasicoherentSheaves.{u, u} B S hS F hF)) :=
  quasicoherentDerivedComparisonCompιIso B S hS F hF ≪≫
    (Stacks.DerivedQCoh.derivedFunctorOfExactIsoMapDerivedCategory
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι).symm

/-- **The comparison functor of Stacks 08F1 is left adjoint to the restricted derived
coherator.**  For an arbitrary algebraic space `X` and an arbitrary total right derived functor
`RQ_X` of a coherator, `i_X ⊣ J ⋙ RQ_X`, where `J : D_QCoh(𝒪_X) ⥤ D(𝒪_X)`.

This is `AlgebraicGeometry.Space.derivedCoheratorAdjunction` restricted along the identity of
`D(QCoh(𝒪_X))` and along the fully faithful `J`, which is legitimate because `i_X ⋙ J` is the
left adjoint of that adjunction. -/
def comparisonDerivedCoheratorAdjunction :
    quasicoherentDerivedComparison B S hS F hF ⊣
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf
            (smallEtaleRingedSite B S hS F hF).O)))).ι ⋙ RQ :=
  (derivedCoheratorAdjunction B S hS F hF CF adjF RQ RQUnit).restrictFullyFaithful
    (Functor.FullyFaithful.id _)
    (Functor.FullyFaithful.ofFullyFaithful
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))).ι)
    (Functor.leftUnitor _ ≪≫ (comparisonCompιIsoDerivedFunctorOfExact B S hS F hF).symm)
    (Functor.rightUnitor _).symm

/-- **[Stacks, Tag 09TG], quasi-inverse clause.**  Let `X` be an algebraic space whose comparison
functor `i_X : D(QCoh(𝒪_X)) ⥤ D_QCoh(𝒪_X)` of Stacks 08F1 is an equivalence, and let `RQ_X` be
any total right derived functor of a coherator `C_X` of `X`.  Then the quasi-inverse of `i_X` is
`RQ_X` restricted to the complexes with quasi-coherent cohomology.

`AlgebraicGeometry.Space.comparisonDerivedCoheratorAdjunction` exhibits that restriction as a
right adjoint of `i_X`, the inverse of an equivalence is another, and a right adjoint is unique
up to a unique natural isomorphism.

This is the second clause of the conclusion of [Stacks, Tag 09TG], deduced from the first clause
rather than from the tag's affine-étale hypothesis
`AlgebraicGeometry.Space.AffineEtaleDerivedPushforwardCompatible`; the first clause — that the
comparison functor is an equivalence — is the source's induction over the elementary
distinguished squares of a quasi-compact, quasi-separated algebraic space, and is not proved
here. -/
@[stacks 09TG "quasi-inverse clause, given the equivalence"]
def derivedCoherator_isoInv
    [(quasicoherentDerivedComparison B S hS F hF).IsEquivalence] :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))).ι ⋙ RQ ≅
      (quasicoherentDerivedComparison B S hS F hF).inv :=
  Adjunction.rightAdjointUniq
    (comparisonDerivedCoheratorAdjunction B S hS F hF CF adjF RQ RQUnit)
    (quasicoherentDerivedComparison B S hS F hF).asEquivalence.toAdjunction

end QuasiInverse

end AlgebraicGeometry.Space

end
