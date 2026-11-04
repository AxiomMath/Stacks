module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.DevissageComparison
public import StacksFrontier.RingTheory.AdicCompletion.TateModule.FiniteComplete
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The algebraization hypothesis of Stacks 088B over an affine base

Let `A` be a Noetherian ring complete with respect to an ideal `I`, let `f : X ⟶ Spec A` be proper
and set `𝓘 = I · 𝒪_X`. The form of Stacks 088B this library carries,
`Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isProper`,
has exactly one hypothesis beyond the source's: the binder

`halg : (completionFunctor X (baseIdealSheaf A I f)).essImage G`

— that the object `G` of `Coh(X, 𝓘)` being compared is algebraizable. It stands for the source's
reduction of Stacks 088B to an affine base, which is the content of the first two paragraphs of
its proof.

This file discharges that binder **when `X` is affine**, and records Stacks 088B with no
algebraization hypothesis over such a base.

## Main results

* `Stacks.Algebraization.isAdicComplete_baseIdeal_of_isAffine` — for `X` affine and proper over
  `Spec A`, the ring `Γ(X, 𝒪_X)` is complete with respect to `I · Γ(X, 𝒪_X)`.
* `Stacks.Algebraization.essImage_completionFunctor_baseIdealSheaf_of_isAffine` — **the binder
  `halg`, proved**: over an affine `X` proper over `Spec A`, every object of `Coh(X, 𝓘)` is the
  completion of a coherent `𝒪_X`-module. No hypothesis beyond `IsAffine X`.
* `Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isAffine`
  — **Stacks 088B with the source's own hypotheses, over an affine base.** The map `α` and the
  bound on its levelwise kernels and cokernels, with `halg` gone.

## Why `IsAffine X` is the right hypothesis, and why it is not a restriction of the ring

The affine case of Grothendieck existence,
`Stacks.Coherent.essImage_completionFunctor_of_isAdicComplete` (Stacks 087W), asks three things of
the scheme carrying the system: that it be affine, that its ring of global functions be
Noetherian, and that *that ring* be complete along the ideal cutting out the adic ideal sheaf. Its
`IsAffine` is on the ambient scheme, not on a morphism, so nothing weaker than an affine base
scheme will feed it.

Over an affine base the first two are free, and the third is a theorem rather than a hypothesis.
The ideal sheaf `baseIdealSheaf A I f` is **by definition** `Scheme.IdealSheafData.ofIdealTop` of
the ideal `baseIdeal A I f = I · Γ(X, 𝒪_X)`, so 087W applies at that ideal with no transport at
all; and `Γ(X, 𝒪_X)` is complete along it because an affine morphism which is proper is finite
(`AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom`), so `Γ(X, 𝒪_X)` is a finite
`A`-module, and a finite module over a Noetherian ring complete along `I` is complete along `I`
(`AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing`, Stacks 031B). This is the one
place where properness of `f` is used for something other than the comparison itself: the source,
working over an affine open of its base, has no properness available and must instead *replace*
`B` by its completion `B ^∧`.

## What the general reduction still needs, and what of it is already here

The source reduces Stacks 088B to this case in two steps, and the library already has the
commutative algebra of the second but not the restatement the first needs.

**Step 1, locality on the base.** The source characterizes `α` by the requirement that
`𝒢_n ⟶ f_*𝓕 / 𝒥 ⁿ f_*𝓕 ⟶ f_*(𝓕 / ℐ ⁿ 𝓕)` be the composite `γ_n` of the adjunction map with
`f_*β_n`, and *because that characterization is unique* the construction may be carried out over
the members of an affine open cover and glued. The maps `γ_n` are
`Stacks.Coherent.directImageComparison`
(`CompletionProper/DirectImageComparison.lean`), and the gluing machinery is present and
unconditional: `Stacks.Coherent.existsUnique_systemHom_of_openCover` and
`Stacks.Coherent.existsUnique_coherentSystemIso_of_openCover`
(`CoherentAdicSystem/MorphismGluing.lean`), with the overlap hypothesis weakenable to affine opens
by `Stacks.Coherent.existsUnique_coherentSystemIso_of_affineComparison`; completion commutes with
restriction to an open by `Stacks.Algebraization.completionRestrictOpenIso`
(`CompletionFunctor/RestrictOpen.lean`), compatibly with the projections
(`Stacks.Algebraization.completionProjection_comp_completionRestrictOpenIso`); and a morphism out
of a completion is determined by its composites with the projections,
`Stacks.Algebraization.completionSystemHom_ext` (`AlgebraizeDual.lean`), which is the uniqueness
the source's argument runs on.

What is missing is not a lemma but a **restatement**. The `α` of this library is *constructed*
from an algebraization of `(𝒢_n)` — `Stacks.Coherent.properDirectImageCompletionMap` is the
completion of `𝒢 ⟶ f_*f^*𝒢 ⟶ f_*𝓕` — and a map built that way cannot be localized, because an
affine open of the base carries no algebraization coming from a global one. To localize, Stacks
088B has to be stated with `α` *characterized* by its composites with
`Stacks.Coherent.directImageComparison` rather than constructed from an algebraization. That is
the shape the binder `halg` is standing in for, and it is a restatement of 088B, not a missing
input to the present one.

**That restatement, and this step, are now carried out** in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProper/GeneralBaseAlgebraization.lean`:
`Stacks.Coherent.exists_isDirectImageCharacterized_isKernelCokernel_of_essImage` is Stacks 088B at
a general base with `α` characterized as well as annihilated,
`Stacks.Coherent.isDirectImageCharacterized_iff_restrictCover` is the locality of the
characterization on the base and `Stacks.Coherent.exists_isDirectImageCharacterized_of_openCover`
glues the local solutions, both unconditionally.
`Stacks.Algebraization.exists_isDirectImageCharacterized_isKernelCokernel_of_isAffine` is the
affine-base statement below with the characterization added to its conclusion, which is what the
gluing consumes. The uniqueness clause of the source's first paragraph is
`Stacks.Coherent.eq_of_comp_directImageQuotientComparisonSystem_eq`, carrying one hypothesis — that
the comparison `δ`, assembled there into a morphism of inverse systems
`Stacks.Coherent.directImageQuotientComparisonSystem`, is a monomorphism after passing to the
inverse limit, which is Stacks 02OC in degree zero and relative form. What remains after all that
is the second step below.

**Step 2, flat base change along `B ⟶ B ^∧`.** Every ingredient the source cites for this step is
in the library, so the step is not a commutative-algebra prerequisite:

* flatness of `B ⟶ B ^∧` (Algebra 00MB) is Mathlib's instance
  `AdicCompletion.flat_of_isNoetherian`;
* flat base change for a direct image (Cohomology of Schemes 02KH) is
  `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat`
  (`FlatBaseChangeCohomology/AffineDegreeZero/Modules.lean`) in degree zero over an arbitrary
  base, and `Stacks.AlgebraicGeometry.FlatBaseChange.isIso_pushforwardBaseChange_of_isAffine`
  (`FlatBaseChange/Affine.lean`) over an affine one — degree zero is all Stacks 088B reads;
* the equivalence between modules annihilated by `J ⁿ` and by `(J ^∧) ⁿ` (More on Algebra 05EC,
  i.e. More on Algebra 15.91.3) is `IPowerTorsion.baseChange_equiv_of_quotientMap_bijective`
  (`RingTheory/Localization/Glueing/IdealPowerTorsion.lean`);
* that a coherent sheaf supported on `V(𝒦)` is annihilated by a power of `𝒦` (00... Tag 01Y9) is
  `AlgebraicGeometry.exists_idealPowerMultiple_eq_bot_iff_supp_subset`
  (`Cohomology/Coherent/IdealPowerAnnihilation.lean`).

One `stacks` attribute is attached here, to
`Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isAffine`:
it registers Stacks 088B **for an affine base**, with a note saying so. The source does not assume
the base affine — it reduces to that case — so this is partial coverage, recorded the way partial
coverage is recorded elsewhere in this tree rather than left invisible. The two inputs are not
tagged: 087W already carries its tag on
`Stacks.Coherent.essImage_completionFunctor_of_isAdicComplete`, and completeness of the global
functions is Stacks 031B, whose tag belongs to the commutative algebra.

## References

* [Stacks Project, Tag 031B](https://stacks.math.columbia.edu/tag/031B)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 088B](https://stacks.math.columbia.edu/tag/088B)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

open Stacks.Cohomology.FormalFunctions Stacks.Coherent

/-! ### The global functions of an affine scheme proper over a complete base -/

/-- **An affine scheme proper over `Spec A` has `I`-adically complete global functions.** If
`f : X ⟶ Spec A` is proper, `X` is affine and `A` is Noetherian and complete with respect to `I`,
then `Γ(X, 𝒪_X)` is complete with respect to `I · Γ(X, 𝒪_X) = baseIdeal A I f`.

An affine morphism which is proper is finite, so `Γ(X, 𝒪_X)` is a finite `A`-module; a finite
module over a Noetherian ring complete along `I` is complete along `I` (Stacks 031B), and
`IsAdicComplete.map_algebraMap_iff` converts that into completeness along the extended ideal. -/
@[ega "IV 18.5.16"]
public theorem isAdicComplete_baseIdeal_of_isAffine
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] [IsAffine X] :
    IsAdicComplete (baseIdeal A I f) Γ(X, ⊤) := by
  have : IsFinite f := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  have happ : RingHom.Finite (f.appTop).hom := IsFinite.finite_app f ⊤ (isAffineOpen_top _)
  let : Algebra A Γ(X, ⊤) := (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).toAlgebra
  have hfin : RingHom.Finite (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom) := by
    rw [CommRingCat.hom_comp]
    exact happ.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).2)
  have : Module.Finite A Γ(X, ⊤) := hfin
  have hC : IsAdicComplete I Γ(X, ⊤) :=
    AdicCompletion.isAdicComplete_of_finite_of_isNoetherianRing I Γ(X, ⊤)
  have h := (IsAdicComplete.map_algebraMap_iff (S := Γ(X, ⊤)) I Γ(X, ⊤)).mpr hC
  rwa [RingHom.algebraMap_toAlgebra] at h

/-! ### Grothendieck existence over an affine scheme proper over a complete affine base -/

/-- **The hypothesis `halg` of Stacks 088B, proved over an affine base.** Let `A` be a Noetherian
ring complete with respect to `I`, let `f : X ⟶ Spec A` be proper with `X` affine and set
`𝓘 = I · 𝒪_X`. Then every object of `Coh(X, 𝓘)` is the completion of a coherent `𝒪_X`-module.

This is Grothendieck existence in the affine case,
`Stacks.Coherent.essImage_completionFunctor_of_isAdicComplete` (Stacks 087W), applied at the
ideal `baseIdeal A I f` of `Γ(X, 𝒪_X)`: the ideal sheaf `baseIdealSheaf A I f` is by definition
`Scheme.IdealSheafData.ofIdealTop` of that ideal, so there is nothing to transport, and the
completeness 087W asks of `Γ(X, 𝒪_X)` is `isAdicComplete_baseIdeal_of_isAffine`. -/
public theorem essImage_completionFunctor_baseIdealSheaf_of_isAffine
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f] [IsAffine X]
    (G : CoherentAdicSystems (baseIdealSheaf A I f)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (completionFunctor X (baseIdealSheaf A I f)).essImage G := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have := isAdicComplete_baseIdeal_of_isAffine A I f
  exact essImage_completionFunctor_of_isAdicComplete X (baseIdeal A I f) G

/-! ### Stacks 088B over an affine base -/

/-- **Stacks 088B with the source's own hypotheses, over an affine base.** Let `A` be a Noetherian
ring complete with respect to `I`, let `f : X ⟶ Spec A` be proper with `X` **affine**, set
`𝓘 = I · 𝒪_X`, let `π : X' ⟶ X` be proper and let `𝒦 ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals.
Given a coherent `𝒪_{X'}`-module `𝓕`, an object `G` of `Coh(X, 𝓘)`, the source's isomorphism
`β : π^*G ≅ 𝓕 ^∧` and the condition `hc` in which the source uses that `π` is an isomorphism away
from `V(𝒦)`, there is a morphism

`α : G ⟶ (π_*𝓕) ^∧`

whose levelwise kernels and cokernels are annihilated by a power of `𝒦`.

This is
`Stacks.Algebraization.exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isProper`
with its last binder `halg` discharged by
`Stacks.Algebraization.essImage_completionFunctor_baseIdealSheaf_of_isAffine`. Both hypotheses
remaining are the source's own, so over an affine base Stacks 088B is unconditional here; the
reduction of a general base to this one is discussed in the module docstring. -/
public theorem exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isAffine
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {X' X : Scheme.{u}} [IsNoetherian X'] [IsNoetherian X]
    (f : X ⟶ Spec (.of A)) (π : X' ⟶ X) [IsProper π] [IsProper f] [IsAffine X]
    (𝒦 : X.IdealSheafData)
    (𝓕 : AlgebraicGeometry.SheafOfModules.CoherentModules X'.ringCatSheaf)
    (G : CoherentAdicSystems (baseIdealSheaf A I f))
    (β : (coherentAdicPullback π (baseIdealSheaf A I f)).obj G ≅
      (completionFunctor X' ((baseIdealSheaf A I f).comap π)).obj 𝓕)
    (hc : ∀ 𝒜 : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
      (G ≅ (completionFunctor X (baseIdealSheaf A I f)).obj 𝒜) →
        IsIso ((Scheme.Modules.restrictFunctor (Scheme.Opens.ι 𝒦.support.compl)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction π).unit.app 𝒜.obj))) :
    ∃ α : G.obj ⟶ ((completionFunctor X (baseIdealSheaf A I f)).obj
        (properPushforwardCoherent π 𝓕)).obj,
      IsKernelCokernelAnnihilatedByPower 𝒦 α :=
  exists_isKernelCokernelAnnihilatedByPower_properDirectImage_of_isProper A I f π 𝒦 𝓕 G
    (essImage_completionFunctor_baseIdealSheaf_of_isAffine A I f G) β hc

end Stacks.Algebraization

end
