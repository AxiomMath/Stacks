module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Epi
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Exactness
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.FullyFaithfulComplete
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksCore.Tactic.StacksAttribute

/-!
# Grothendieck's existence theorem for a projective morphism

**Stacks 0885.** Let `A` be a Noetherian ring complete with respect to an ideal `I`, let
`f : X ⟶ Spec A` be projective and put `𝓘 = I · 𝒪_X`. Then the completion functor of Stacks 0880

  `Coh(𝒪_X) ⥤ Coh(X, 𝓘)`,  `F ↦ (F / 𝓘ⁿ F)`

is an **equivalence** — both halves, full faithfulness and essential surjectivity.

The source proves this in two steps. Full faithfulness is Stacks 0883, which holds for any proper
morphism. Essential surjectivity is reduced to the statement that *every* object of `Coh(X, 𝓘)` is
a quotient of an object in the image of the functor: an `f`-ample invertible sheaf `L` is chosen,
`H¹(X, Ker(F_{n+1} → F_n) ⊗ L^{⊗d})` is made to vanish for `d ≫ 0` (Stacks 0884), the resulting
surjectivity of the transition maps on `H⁰(X, F_n ⊗ L^{⊗d})` lifts a generating family of
`F_1 ⊗ L^{⊗d}` to a compatible system of sections of all the `F_n ⊗ L^{⊗d}`, and Stacks 087Y
turns the resulting map `((L^{⊗ -d})^{⊕t})^∧ ⟶ (F_n)` into an epimorphism. Granted that, each
object of `Coh(X, 𝓘)` is the cokernel of a map between objects in the image — the category is
abelian by Stacks 087X — and since the functor is fully faithful and exact (Stacks 0881) that
cokernel comes from a cokernel upstairs.

**This file carries the passage from the generation statement to the equivalence, and takes the
one input it does not have as a hypothesis.** That passage — the source's last paragraph, which
is what turns 0883 and 0884 into the lemma — is proved here with no hypotheses at all:
`Stacks.Algebraization.essSurj_of_forall_exists_epi`. The remaining input is

* `hGen`, that every coherent adic system receives an epimorphism from the completion of a
  coherent module. This is the paragraph of the source recalled above; it needs Stacks 0884,
  which is not carried by this library (0884 rests on Stacks 0897, also absent), together
  with an `f`-ample invertible sheaf for a projective `f` and Serre's global generation.

The other input of the source's argument, the theorem on formal functions in degree zero
(Stacks 087U), is *not* a hypothesis here: it is
`Stacks.Algebraization.isIso_globalSectionsToLimit_of_isProper`, proved unconditionally for a
proper morphism over a complete Noetherian base in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionFunctor/FullyFaithfulComplete.lean`.

For the source's notion of projectivity — clause (1) of Tag 01W8,
`AlgebraicGeometry.IsProjective`, a closed immersion into a projective bundle `𝐏(ℰ)` —
properness is available, by `AlgebraicGeometry.IsProjective.isProper` (Tag 01WC), and with it
local finite type and hence the local Noetherianity of `X`. So the statement registered for the
tag assumes nothing beyond the source's hypotheses except `hGen`. The H-projective notion of
clause (2), `AlgebraicGeometry.IsProjectiveMorphism`, is subsumed by clause (1) by Tag 01W9; the
statement for it is kept below but is not where the tag is registered.

## Main results

* `Stacks.Algebraization.essSurj_of_forall_exists_epi` — a fully faithful right exact functor
  between abelian categories such that every object of the target receives an epimorphism from
  the image is essentially surjective, and hence
  `Stacks.Algebraization.isEquivalence_of_forall_exists_epi` an equivalence. Unconditional.
* `Stacks.Algebraization.exists_epi_completionFunctor_of_epi_app_zero` — Stacks 087Y in the shape
  in which the generation hypothesis is met: surjectivity at the lowest level suffices.
* `Stacks.Algebraization.isEquivalence_completionFunctor_of_exists_epi` — the core: for a proper
  morphism to the spectrum of a complete Noetherian ring, `hFF` and `hGen` give the equivalence.
* `Stacks.Algebraization.isEquivalence_completionFunctor_of_forall_exists_epi` — the same with
  `hFF` discharged by Stacks 087U, so only `hGen` is assumed.
* `Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjective` — **Stacks 0885** for
  clause (1) of Tag 01W8, the source's notion.
* `Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjectiveMorphism` — the same for
  clause (2) of Tag 01W8, H-projectivity, which clause (1) subsumes.

## Implementation notes

The abstract lemma is the source's last paragraph made precise. Given `Y` in the target, choose an
epimorphism `p : F P ⟶ Y` and then an epimorphism `q : F Q ⟶ Ker p`. In an abelian category an
epimorphism is the cokernel of its kernel, and precomposing a cokernel with an epimorphism does
not change it, so `Y ≅ Coker(q ≫ Ker p ↪ F P)`. Full faithfulness turns `q ≫ Ker p ↪ F P` into
`F r` for a unique `r : Q ⟶ P`, and right exactness turns `F (Coker r)` into `Coker (F r) ≅ Y`.
Right exactness also makes `F` additive, which is what `PreservesCokernel.iso` needs.

Local Noetherianity of `X` is not an extra hypothesis: it follows from `LocallyOfFiniteType f`
over the Noetherian base. Full Noetherianity, which the abelian structure of `Coh(X, 𝓘)` needs
(Stacks 087X), follows as well, `X` being quasi-compact because a universally closed morphism is
quasi-compact and `Spec A` is quasi-compact. Local Noetherianity is introduced in the statements
with a `letI`, as in `CompletionFunctor/FullyFaithful.lean`, so that they read with the instance
the reader expects; the `IsLocallyNoetherian` carried by `IsNoetherian X` is the same
proposition, so proof irrelevance identifies the two completion functors.

The ideal sheaf `𝓘 = I · 𝒪_X` is `Stacks.Cohomology.FormalFunctions.baseIdealSheaf`, as
throughout this subtree. No statement here mentions `AlgebraicGeometry.Scheme.Modules`: the
categories are written as `AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf` and
`Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f)`, which is what the completion functor
of Stacks 0880 is declared between, so none of this file meets the transparency wall of that
definition.

`Stacks.Algebraization.isEquivalence_completionFunctor_of_exists_epi` is stated for a proper
morphism and is **not** offered as Stacks 088C: `hGen` is an input there, whereas the source
proves 088C from the projective case by Chow's lemma (Stacks 0200), dévissage on the ideal
sheaves not in the essential image (Stacks 01Y8) and Stacks 088A/088B. It is the proper-case core
of this file, shared by the two tagged statements.

## References

* [Stacks Project, Tag 0885](https://stacks.math.columbia.edu/tag/0885)
* [Stacks Project, Tag 0880](https://stacks.math.columbia.edu/tag/0880)
* [Stacks Project, Tag 0881](https://stacks.math.columbia.edu/tag/0881)
* [Stacks Project, Tag 0883](https://stacks.math.columbia.edu/tag/0883)
* [Stacks Project, Tag 0884](https://stacks.math.columbia.edu/tag/0884)
* [Stacks Project, Tag 087U](https://stacks.math.columbia.edu/tag/087U)
* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
* [Stacks Project, Tag 087Y](https://stacks.math.columbia.edu/tag/087Y)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe v₁ v₂ u₁ u₂ u

namespace Stacks.Algebraization

/-! ### Essential surjectivity from generation by the image -/

section Abstract

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Abelian C] [Abelian D]

/-- **A fully faithful right exact functor whose image generates is essentially surjective.**

Let `F : C ⥤ D` be a fully faithful functor between abelian categories which preserves finite
colimits, and suppose every object of `D` receives an epimorphism from an object of the form
`F P`. Then every object of `D` is isomorphic to one of the form `F Q`.

Given `Y`, take an epimorphism `p : F P ⟶ Y` and an epimorphism `q : F Q ⟶ Ker p`. Then `p` is a
cokernel of `Ker p ↪ F P`, and that cokernel is unchanged by precomposition with the epimorphism
`q`, so `Y` is a cokernel of `q ≫ (Ker p ↪ F P)`. Full faithfulness writes the latter as `F r`,
and right exactness identifies `F (Coker r)` with `Coker (F r) ≅ Y`. -/
public theorem essSurj_of_forall_exists_epi (F : C ⥤ D) [F.Full] [F.Faithful]
    [PreservesFiniteColimits F]
    (h : ∀ Y : D, ∃ (P : C) (p : F.obj P ⟶ Y), Epi p) : F.EssSurj := by
  have : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  have : F.Additive := Functor.additive_of_preservesBinaryBiproducts F
  refine ⟨fun Y => ?_⟩
  obtain ⟨P, p, hp⟩ := h Y
  obtain ⟨Q, q, hq⟩ := h (kernel p)
  obtain ⟨r, hr⟩ : ∃ r, F.map r = q ≫ kernel.ι p := ⟨F.preimage _, F.map_preimage _⟩
  refine ⟨cokernel r, ⟨?_⟩⟩
  refine PreservesCokernel.iso F r ≪≫ ?_
  refine cokernelIsoOfEq hr ≪≫ ?_
  refine cokernelEpiComp q (kernel.ι p) ≪≫ ?_
  exact IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel (kernel.ι p))
    (Abelian.epiIsCokernelOfKernel (KernelFork.ofι (kernel.ι p) (kernel.condition p))
      (kernelIsKernel p))

/-- **A fully faithful right exact functor whose image generates is an equivalence.** Essential
surjectivity is `Stacks.Algebraization.essSurj_of_forall_exists_epi`. -/
public theorem isEquivalence_of_forall_exists_epi (F : C ⥤ D) [F.Full] [F.Faithful]
    [PreservesFiniteColimits F]
    (h : ∀ Y : D, ∃ (P : C) (p : F.obj P ⟶ Y), Epi p) : F.IsEquivalence :=
  let _ := essSurj_of_forall_exists_epi F h
  { }

end Abstract

/-! ### Grothendieck existence for a projective morphism -/

section Projective

open Stacks.Cohomology.FormalFunctions

variable (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **The generation hypothesis is met at the lowest level.** By Stacks 087Y a morphism of
coherent adic systems is an epimorphism as soon as its component at the lowest level is one, so a
map from the completion of a coherent module which is surjective there exhibits the target as a
quotient of an object in the image of the completion functor. This is the shape in which the
source's construction — a compatible system of sections of `F_n ⊗ L^{⊗d}` lifting a generating
family of `F_1 ⊗ L^{⊗d}` — produces the hypothesis `hGen` below. -/
public theorem exists_epi_completionFunctor_of_epi_app_zero [IsLocallyNoetherian X]
    (J : X.IdealSheafData) {𝓕 : Stacks.Coherent.CoherentAdicSystems J}
    {P : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf}
    (p : (completionFunctor X J).obj P ⟶ 𝓕) (hp : Epi (p.hom.app (op 0))) :
    ∃ (Q : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
      (q : (completionFunctor X J).obj Q ⟶ 𝓕), Epi q :=
  ⟨P, p, (Stacks.Coherent.epi_iff_epi_app_zero _ p).mpr hp⟩

/-- **The proper-case core of Stacks 0885.** Let `A` be Noetherian and complete for `I` and let
`f : X ⟶ Spec A` be proper. Granted

* `hFF`, the theorem on formal functions in degree zero (Stacks 087U), through which Stacks 0883
  gives full faithfulness, and
* `hGen`, that every coherent adic system along `𝓘 = I · 𝒪_X` receives an epimorphism from the
  completion of a coherent module,

the completion functor `Coh(𝒪_X) ⥤ Coh(X, 𝓘)` of Stacks 0880 is an equivalence.

This is **not** Stacks 088C: there `hGen` is not an input but the conclusion of a reduction to the
projective case by Chow's lemma. It is the shared content of the two statements of Stacks 0885
below, which differ only in which clause of Tag 01W8 they read "projective" by. -/
public theorem isEquivalence_completionFunctor_of_exists_epi [IsProper f]
    (hFF : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ H : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf,
        IsIso (globalSectionsToLimit (baseIdealSheaf A I f) H))
    (hGen : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ 𝓕 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
        ∃ (P : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
          (p : (completionFunctor X (baseIdealSheaf A I f)).obj P ⟶ 𝓕), Epi p) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (completionFunctor X (baseIdealSheaf A I f)).IsEquivalence := by
  let _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let _ : IsNoetherian X := { }
  obtain ⟨hff⟩ := fullyFaithful_completionFunctor A I f hFF
  let _ := hff.full
  let _ := hff.faithful
  let _ := completionFunctor_preservesFiniteColimits X (baseIdealSheaf A I f)
  exact isEquivalence_of_forall_exists_epi _ hGen

/-- **The proper-case core of Stacks 0885 with the theorem on formal functions discharged.** For
`A` Noetherian and complete for `I` and `f : X ⟶ Spec A` proper, the generation statement of the
source's first paragraph (Stacks 0884 with 087Y, the hypothesis `hGen`) alone gives that the
completion functor `Coh(𝒪_X) ⥤ Coh(X, 𝓘)` of Stacks 0880 is an equivalence.

The other input of `Stacks.Algebraization.isEquivalence_completionFunctor_of_exists_epi`, the
theorem on formal functions in degree zero (Stacks 087U), is supplied by
`Stacks.Algebraization.isIso_globalSectionsToLimit_of_isProper`, which carries exactly the
hypotheses of this statement. -/
public theorem isEquivalence_completionFunctor_of_forall_exists_epi [IsProper f]
    (hGen : letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
      ∀ 𝓕 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
        ∃ (P : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
          (p : (completionFunctor X (baseIdealSheaf A I f)).obj P ⟶ 𝓕), Epi p) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (completionFunctor X (baseIdealSheaf A I f)).IsEquivalence :=
  isEquivalence_completionFunctor_of_exists_epi A I f
    (fun H => isIso_globalSectionsToLimit_of_isProper A I f H) hGen

/-- **Stacks 0885 for a projective morphism in the sense of clause (1) of Tag 01W8.** Let `A` be a
Noetherian ring complete with respect to `I`, let `f : X ⟶ Spec A` be projective — a closed
immersion over `Spec A` into a projective bundle `𝐏(ℰ)` — and set `𝓘 = I · 𝒪_X`. Granted the
generation statement of the source's first paragraph (Stacks 0884 with 087Y, the hypothesis
`hGen`), the completion functor `Coh(𝒪_X) ⥤ Coh(X, 𝓘)` of Stacks 0880 is an equivalence.

Properness of `f` is *not* an added hypothesis: it comes from projectivity by
`AlgebraicGeometry.IsProjective.isProper`, Tag 01WC, and with it the local Noetherianity of `X`
that the completion functor needs. The theorem on formal functions in degree zero (Stacks 087U)
is not an added hypothesis either; it is
`Stacks.Algebraization.isIso_globalSectionsToLimit_of_isProper`. So `hGen` is the only input
beyond the source's hypotheses, and it is an arrow rather than a named binder because properness
has to be introduced from `hf` before it can be stated at all.

No Stacks attribute for Tag 0885 is attached here. The tag is registered on
`Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjective_of_vanishing` in
`CompletionProjectiveEquivalence.lean`, which assumes strictly less: the generation statement
`hGen` is derived there from part (2) of Stacks 0897 for the associated graded algebra of the
ideal sheaf, and that input is now proved —
`Stacks.Coherent.hasAssociatedGradedTwistVanishing_of_isProper`, from properness and the
invertibility of an ample module alone. So the registered statement is unconditional, and this
one is the same conclusion still carrying `hGen` as an arrow hypothesis; it is kept because the
conditional form is what the dévissage consumes internally. -/
public theorem isEquivalence_completionFunctor_of_isProjective
    (hf : AlgebraicGeometry.IsProjective f) :
    letI : IsProper f := hf.isProper
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (∀ 𝓕 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
        ∃ (P : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
          (p : (completionFunctor X (baseIdealSheaf A I f)).obj P ⟶ 𝓕), Epi p) →
      (completionFunctor X (baseIdealSheaf A I f)).IsEquivalence := by
  let _ : IsProper f := hf.isProper
  exact fun hGen => isEquivalence_completionFunctor_of_forall_exists_epi A I f hGen

/-- **The H-projective case, clause (2) of Tag 01W8.** Let `A` be a Noetherian ring complete with
respect to `I`, let `f : X ⟶ Spec A` admit a closed immersion over `Spec A` into some
`ℙⁿ_{Spec A}` and set `𝓘 = I · 𝒪_X`. Granted the generation statement of the source's first
paragraph (Stacks 0884 with 087Y), the completion functor `Coh(𝒪_X) ⥤ Coh(X, 𝓘)` of Stacks 0880
is an equivalence.

This is subsumed by `Stacks.Algebraization.isEquivalence_completionFunctor_of_isProjective`,
which reads "projective" by clause (1) of Tag 01W8 — the weaker notion, by Tag 01W9 — and is
where Tag 0885 is registered. It is kept because H-projectivity is the hypothesis under which
properness is most directly available, through
`AlgebraicGeometry.isProper_of_isProjectiveMorphism`. -/
public theorem isEquivalence_completionFunctor_of_isProjectiveMorphism
    (hf : AlgebraicGeometry.IsProjectiveMorphism f) :
    letI : IsProper f := isProper_of_isProjectiveMorphism f hf
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    (∀ 𝓕 : Stacks.Coherent.CoherentAdicSystems (baseIdealSheaf A I f),
        ∃ (P : AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf)
          (p : (completionFunctor X (baseIdealSheaf A I f)).obj P ⟶ 𝓕), Epi p) →
      (completionFunctor X (baseIdealSheaf A I f)).IsEquivalence := by
  let _ : IsProper f := isProper_of_isProjectiveMorphism f hf
  exact fun hGen => isEquivalence_completionFunctor_of_forall_exists_epi A I f hGen

end Projective

end Stacks.Algebraization

end
