module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamDerived07LG
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothPresentationCohomology07LH

/-!
# [Stacks, Lemma 60.21.4, Tag 07LH]: the de Rham complex of a smooth presentation computes
`RΓ(Cris(X/S), ℱ)`

Let `ℱ` be a crystal in quasi-coherent modules over an affine crystalline situation, `A → P' → C`
ring maps with `A → P'` smooth and `P' → C` surjective with kernel `J'`, `D'` the `p`-adic
completion of the divided power envelope `D_{P', γ}(J')`, and `(M', ∇')` the pair over `D'`
corresponding to `ℱ` ([Stacks, Lemma 60.17.5, Tag 07L5], `...SmallSite.smoothPresentationPair`).
[Stacks, Lemma 60.21.4, Tag 07LH] says that the complex `M' ⊗^∧_{D'} Ω^*_{D'}` computes
`RΓ(Cris(X/S), ℱ)`.  This module proves it as an isomorphism in the derived category:

`M' ⊗^∧_{D'} Ω^*_{D'} ≅ RΓ(Cris(X/S), ℱ)`

in `D⁺(Ab)` (`...SmallSite.smoothPresentationPairDerivedPlusIso`) and in `D(Ab)`
(`...SmallSite.smoothPresentationPairDerivedIso`), `RΓ` being `...SmallSite.derivedGlobalSections`,
the right derived functor of global sections, and the complex being lifted to the universe of the
abelian sheaves on `Cris(X/S)` and extended by zero from `ℕ` to `ℤ`.

## The proof, following the source

The base change `M ⊗^∧_D Ω^*_D → M' ⊗^∧_{D'} Ω^*_{D'}` along the divided power map `a : D → D'` is
a quasi-isomorphism (`Crystalline.quasiIso_baseChangeHom_smoothPresentationOfTower`, fed with the
stratification of the crystal and the quasi-isomorphy of its coprojections, both proved in
`SmoothPresentationCohomology07LH.lean`), so it is inverted in the derived category, and
`M ⊗^∧_D Ω^*_D ≅ RΓ(Cris(X/S), ℱ)` is [Stacks, Proposition 60.21.3, Tag 07LG] in the derived
category (`...SmallSite.crystalPairDeRhamDerivedIso`).

## Main results

* `...SmallSite.smoothPresentationPairDerivedIso` — `M' ⊗^∧_{D'} Ω^*_{D'} ≅ RΓ(Cris(X/S), ℱ)` in
  `D(Ab)`, with `...SmallSite.smoothPresentationPairDerivedIso_hom` recording the composite.
* `...SmallSite.smoothPresentationPairDerivedPlusIso` — **[Stacks, Tag 07LH]**, in `D⁺(Ab)`.
* `...SmallSite.smoothPresentationPairDerivedHomologyIso` — its cohomology,
  `H^j(M' ⊗^∧_{D'} Ω^*_{D'}) ≅ H^j(Cris(X/S), ℱ)`, from which the degreewise statement
  `...SmallSite.smoothPresentationPair_computesCohomology` is recovered
  (`...SmallSite.smoothPresentationPair_computesCohomology_of_derived`).

## References

* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
-/

@[expose] public noncomputable section

open CategoryTheory DividedPowers Simplicial AlgebraicGeometry

universe w w' u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp] (Fc : QuasiCoherentCrystal S)

attribute [local instance] tensorPowerEnvelopeAlgebraInstance presentationEnvelopeAlgebraInst

variable {P' : Type u} [CommRing P'] [Algebra (affineSituation S hp).A P']
  (f' : P' →ₐ[(affineSituation S hp).A] (affineSituation S hp).C) (hf' : Function.Surjective f')
  (a : AdicCompletion (pAdicIdeal (A := (tensorPowerEnvelope (affineSituation S hp)
        (wholeSpacePresentation S hp) 0).object) (affineSituation S hp).p)
      (tensorPowerEnvelope (affineSituation S hp)
        (wholeSpacePresentation S hp) 0).object →ₐ[(affineSituation S hp).A]
    AdicCompletion (pAdicIdeal (A := (presentationEnvelope (affineSituation S hp) f').object)
        (affineSituation S hp).p) (presentationEnvelope (affineSituation S hp) f').object)
  (ha : IsDPMorphism (completionDividedPowers (affineSituation S hp).p
      (tensorPowerEnvelope (affineSituation S hp)
        (wholeSpacePresentation S hp) 0).object.dividedPowers
      (tensorPowerEnvelope_prime_nilpotent (affineSituation S hp) _
        (wholeSpacePresentation_surjective S hp) 0))
    (completionDividedPowers (affineSituation S hp).p
      (presentationEnvelope (affineSituation S hp) f').object.dividedPowers
      (presentationEnvelope_prime_nilpotent (affineSituation S hp) f' hf')) a.toRingHom)

/-- The base change `M ⊗^∧_D Ω^*_D → M' ⊗^∧_{D'} Ω^*_{D'}` along `a`, lifted to the universe of
the abelian sheaves on `Cris(X/S)` and extended by zero to `ℤ`. -/
abbrev smoothPresentationPairBaseChangeExtendMap :
    ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (crystalPairDeRhamComplex hp Fc)).extend ComplexShape.embeddingUpNat ⟶
      ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (smoothPresentationPair hp Fc f' hf' a ha).complex).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.extendMap
    ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((crystalPairConnModule hp Fc).baseChangeHom
        (FormsData.Hom.ofCompletion (affineSituation S hp).p (affineSituation S hp).A _
          (presTowerPrime_nilpotent (affineSituation S hp) (wholeSpacePresentation S hp)
            (wholeSpacePresentation_surjective S hp) 0) _
          (presentationEnvelope_prime_nilpotent (affineSituation S hp) f' hf') a ha)))
    ComplexShape.embeddingUpNat

variable [Nonempty (wholeSpaceIndex S hp)] [Algebra.Smooth ((affineSituation S hp).A : Type u) P']
  (haug : (completedEnvelopeAugmentation (affineSituation S hp) f' hf').comp a.toRingHom =
      completedEnvelopeAugmentation (affineSituation S hp)
        (tensorPowerPresentation (affineSituation S hp)
          (wholeSpacePresentation S hp) 0)
        (tensorPowerPresentation_surjective (affineSituation S hp) _
          (wholeSpacePresentation_surjective S hp) 0))

include haug in
/-- The base change `M ⊗^∧_D Ω^*_D → M' ⊗^∧_{D'} Ω^*_{D'}`, lifted and extended to `ℤ`, is a
quasi-isomorphism: `Crystalline.quasiIso_baseChangeHom_smoothPresentationOfTower`, with the
stratification of the crystal and the quasi-isomorphy of its coprojections. -/
theorem quasiIso_smoothPresentationPairBaseChangeExtendMap :
    QuasiIso (smoothPresentationPairBaseChangeExtendMap hp Fc f' hf' a ha) :=
  haveI := quasiIso_baseChangeHom_smoothPresentationOfTower (affineSituation S hp)
    (wholeSpacePresentation S hp) (wholeSpacePresentation_surjective S hp)
    (crystalPairConnModule hp Fc) (quasiIso_crystalPair_baseChangeHom_coprojection hp Fc)
    (crystalStratification hp Fc) (crystalStratification_bijective hp Fc) f' hf'
    (exists_tensorPowerSurjectionOfTower (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) P' f' hf') a ha haug
  (HomologicalComplex.quasiIso_extendMap_iff _ _).2 inferInstance

variable [HasDerivedCategory.{w} (Sheaf (smallTopology S) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w'} AddCommGrpCat.{u + 1}]

/-- **`M' ⊗^∧_{D'} Ω^*_{D'} ≅ RΓ(Cris(X/S), ℱ)` in `D(Ab)`**: the inverse of the class of the
quasi-isomorphism `M ⊗^∧_D Ω^*_D → M' ⊗^∧_{D'} Ω^*_{D'}` of base change along `a`, followed by
[Stacks, Tag 07LG] in the derived category (`...SmallSite.crystalPairDeRhamDerivedIso`). -/
def smoothPresentationPairDerivedIso :
    DerivedCategory.Q.obj
        (((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (smoothPresentationPair hp Fc f' hf' a ha).complex).extend
            ComplexShape.embeddingUpNat) ≅
      DerivedCategory.Plus.ι.obj ((derivedGlobalSections S).obj (abelianSheaf Fc.obj)) :=
  haveI := quasiIso_smoothPresentationPairBaseChangeExtendMap hp Fc f' hf' a ha haug
  (asIso (DerivedCategory.Q.map
    (smoothPresentationPairBaseChangeExtendMap hp Fc f' hf' a ha))).symm ≪≫
    crystalPairDeRhamDerivedIso hp Fc

/-- **The comparison of [Stacks, Tag 07LH] is the base change followed by [Stacks, Tag 07LG]**:
its inverse is the class of the comparison of [Stacks, Tag 07LG] inverted, followed by the class
of the base change along `a`. -/
theorem smoothPresentationPairDerivedIso_inv :
    (smoothPresentationPairDerivedIso hp Fc f' hf' a ha haug).inv =
      (crystalPairDeRhamDerivedIso hp Fc).inv ≫
        DerivedCategory.Q.map (smoothPresentationPairBaseChangeExtendMap hp Fc f' hf' a ha) :=
  rfl

/-- **[Stacks, Lemma 60.21.4, Tag 07LH]**: in the situation of
[Stacks, Proposition 60.21.3, Tag 07LG] (`X` and `S` affine, `p` nilpotent on `X`), let `ℱ` be a
crystal in quasi-coherent `𝒪_{X/S}`-modules, `A → P' → C` ring maps with `A → P'` smooth and
`P' → C` surjective with kernel `J'`, `D'` the `p`-adic completion of `D_{P', γ}(J')` and
`(M', ∇')` the pair over `D'` corresponding to `ℱ` (`...SmallSite.smoothPresentationPair`): the
base change of the pair `(M, ∇)` of `ℱ` along any divided power `A`-algebra map `a : D → D'`
compatible with the augmentations to `C` (one exists, `Crystalline.exists_smoothPresentationMap`).
Here `D` is the completed envelope of the presentation `A[x_i : i ∈ ι] → C` of the system, any one
with a variable (the instance `...SmallSite.WholeSpacePresentation S hp`, by default the
tautological `A[x_c : c ∈ C] → C`).  Then the complex `M' ⊗^∧_{D'} Ω^*_{D'}` computes
`RΓ(Cris(X/S), ℱ)`: there is an isomorphism

`M' ⊗^∧_{D'} Ω^*_{D'} ≅ RΓ(Cris(X/S), ℱ)`

in the bounded below derived category `D⁺(Ab)`, the complex lifted to the universe of the
abelian sheaves on `Cris(X/S)` and extended by zero to `ℤ`, and `RΓ(Cris(X/S), -)` being
`...SmallSite.derivedGlobalSections`, the right derived functor of global sections.  Read in
`D(Ab)` it is `...SmallSite.smoothPresentationPairDerivedIso`: the base change
`M ⊗^∧_D Ω^*_D → M' ⊗^∧_{D'} Ω^*_{D'}` inverted, followed by [Stacks, Tag 07LG]. -/
@[stacks 07LH "for A -> P' smooth and P' -> C surjective, D' the p-adically completed divided \
power envelope and (M', nabla') the pair over D' corresponding to F (the base change of the pair \
of 07JG, for any polynomial presentation A[x_i] -> C of the system with a variable \
(WholeSpacePresentation S hp, by default the tautological one), along any augmentation-compatible \
divided power map D -> D'), the complex M' ⊗^∧_{D'} Ω*_{D'} computes RΓ(Cris(X/S), F): an \
isomorphism M' ⊗^∧_{D'} Ω*_{D'} ≅ RΓ(Cris(X/S), F) in D⁺(Ab), the base change to D inverted \
followed by 07LG in the derived category"]
def smoothPresentationPairDerivedPlusIso :
    DerivedCategory.Plus.Q.obj (Stacks.Cohomology.extendPlusObj
        ((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (smoothPresentationPair hp Fc f' hf' a ha).complex)) ≅
      (derivedGlobalSections S).obj (abelianSheaf Fc.obj) :=
  DerivedCategory.Plus.ι.preimageIso (smoothPresentationPairDerivedIso hp Fc f' hf' a ha haug)

/-- **The derived comparison of [Stacks, Tag 07LH] read in `D(Ab)`** is
`...SmallSite.smoothPresentationPairDerivedIso`. -/
theorem ι_map_smoothPresentationPairDerivedPlusIso_hom :
    DerivedCategory.Plus.ι.map (smoothPresentationPairDerivedPlusIso hp Fc f' hf' a ha haug).hom =
      (smoothPresentationPairDerivedIso hp Fc f' hf' a ha haug).hom :=
  DerivedCategory.Plus.ι.map_preimage _

/-- **The cohomology of the derived comparison of [Stacks, Tag 07LH]**:
`H^j(M' ⊗^∧_{D'} Ω^*_{D'}) ≅ H^j(Cris(X/S), ℱ)` for every `j`, the degree-`j` cohomology of
`...SmallSite.smoothPresentationPairDerivedIso`, read through the identification of the
cohomology of `RΓ` with the graded crystalline cohomology
(`...SmallSite.homologyDerivedGlobalSectionsIsoObj`). -/
def smoothPresentationPairDerivedHomologyIso (j : ℕ) :
    AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
        ((smoothPresentationPair hp Fc f' hf' a ha).complex.homology j) ≅
      (cohomologyFunctor S j).obj (abelianSheaf Fc.obj) :=
  (Stacks.Homology.RestrictScalars.mapHomologicalComplexHomologyIso
      AddCommGrpCat.uliftFunctor.{u + 1, u} (smoothPresentationPair hp Fc f' hf' a ha).complex
      j).symm ≪≫
    (((AddCommGrpCat.uliftFunctor.{u + 1, u}.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (smoothPresentationPair hp Fc f' hf' a ha).complex).extendHomologyIso
        ComplexShape.embeddingUpNat (j' := (j : ℤ)) rfl).symm ≪≫
    ((DerivedCategory.homologyFunctorFactors AddCommGrpCat.{u + 1} (j : ℤ)).app _).symm ≪≫
    (DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} (j : ℤ)).mapIso
      (smoothPresentationPairDerivedIso hp Fc f' hf' a ha haug) ≪≫
    homologyDerivedGlobalSectionsIsoObj S (abelianSheaf Fc.obj) j

include haug in
/-- **The degreewise reading of [Stacks, Tag 07LH] follows from the derived one**: the conclusion
of `...SmallSite.smoothPresentationPair_computesCohomology`, obtained here as the cohomology of
the derived comparison (`...SmallSite.smoothPresentationPairDerivedHomologyIso`). -/
theorem smoothPresentationPair_computesCohomology_of_derived :
    ∀ j : ℕ, Nonempty (AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
        ((smoothPresentationPair hp Fc f' hf' a ha).complex.homology j) ≅
      (cohomologyFunctor S j).obj (abelianSheaf Fc.obj)) :=
  fun j => ⟨smoothPresentationPairDerivedHomologyIso.{w, w'} hp Fc f' hf' a ha haug j⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end
