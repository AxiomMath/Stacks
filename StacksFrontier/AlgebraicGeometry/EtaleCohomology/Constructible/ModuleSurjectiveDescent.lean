module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.InverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleSheafPresentationColimits
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ModuleShriekFiniteGeneration
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.SmallEtaleInverseImageModuleExact
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ModuleCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleModules
import StacksCore.Tactic.StacksAttribute

/-!
# Constructibility of an étale sheaf of modules descends along a surjective morphism

Let `f : X ⟶ Y` be a surjective morphism of quasi-compact and quasi-separated schemes, let `Λ` be
a Noetherian ring and let `ℱ` be a sheaf of `Λ`-modules on `Y_étale`. Then `ℱ` is constructible as
soon as `f⁻¹ℱ` is; with Stacks 095G, which is the converse and needs neither surjectivity nor
quasi-compactness, this is the sheaves-of-modules statement of Stacks 095Q.

The argument is the source's, carried out in the abelian category of sheaves of `Λ`-modules.
Write `ℱ = colim_i ℱ_i` as a filtered colimit of constructible sheaves. Inverse image is a left
adjoint, so `f⁻¹ℱ = colim_i f⁻¹ℱ_i`, and `f⁻¹ℱ` is a compact object because it is constructible,
so the identity of `f⁻¹ℱ` factors through some `f⁻¹ℱ_i`; that makes `f⁻¹(ℱ_i ⟶ ℱ)` a split
epimorphism, and surjectivity of `f` carries the epimorphism back to `Y` by
`AlgebraicGeometry.epi_of_epi_smallEtalePullback_module`. So `ℱ` is a quotient of a constructible
sheaf — and this is the one step of the whole proof that uses `f` at all.

Applying that twice finishes it. For `p : 𝒢 ⟶ ℱ` such a quotient, the kernel of `p` has
constructible inverse image, since inverse image is left exact and the constructible sheaves of
`Λ`-modules are a weak Serre subcategory (Stacks 03RZ (3)); so the kernel is itself a quotient of
a constructible `ℋ`, and `ℱ` is the cokernel of the composite `ℋ ⟶ ker p ⟶ 𝒢`, hence
constructible by Stacks 03RZ (3) again.

## Nothing is granted

Every statement of the source used below is proved in the library. Two of them were granted here
until they became available; neither mentions `f`.

* **Stacks 095N**, in its quasi-compact quasi-separated form and at every quasi-compact
  quasi-separated scheme of `B`: a sheaf of `Λ`-modules is constructible exactly when it has a
  finite presentation by the sheaves `j_{U!}Λ` at quasi-compact quasi-separated étale objects.
  This is now `AlgebraicGeometry.isConstructibleModuleSheaf_iff_qcqsShriekPresentation`, which is
  unconditional; the private `isConstructibleModuleSheaf_iff_qcqs` below is that theorem with the
  quasi-compactness and quasi-separatedness of the scheme taken as hypotheses rather than as
  instances. Its forward direction gives the compactness of `f⁻¹ℱ` on `X`, through
  `AlgebraicGeometry.isFinitelyPresentable_of_hasFiniteShriekPresentation`, and its converse
  direction turns the stages produced by Stacks 093C on `Y` into constructible sheaves.
* **Stacks 093C (2)** at `Y`, in the spelling
  `AlgebraicGeometry.ModuleSheavesAreFilteredColimitsOfPresentations`. It is supplied internally
  from `AlgebraicGeometry.moduleSheavesAreFilteredColimitsOfPresentations`, which holds at every
  quasi-compact quasi-separated scheme of `B`.

The hypotheses `hXc`, `hXq`, `hYc` and `hYq` of the theorems below are the quasi-compactness and
quasi-separatedness of `X` and `Y`, which the source's statement assumes; they are what the two
results above ask for, and they are not granted mathematics.

## Main results

* `AlgebraicGeometry.exists_epi_of_isColimit_of_surjective_module` — the descent step: for `f`
  surjective and `ℱ` a filtered colimit whose inverse image is a compact object, some
  coprojection `ℱ_i ⟶ ℱ` is an epimorphism.
* `AlgebraicGeometry.exists_epi_isConstructibleModuleSheaf_of_pullback` — a sheaf of `Λ`-modules
  on `Y_étale` with constructible inverse image is a quotient of a constructible sheaf.
* `AlgebraicGeometry.isConstructibleModuleSheaf_of_isConstructibleModuleSheaf_pullback` and
  `AlgebraicGeometry.isConstructibleModuleSheaf_pullback_iff_of_surjective` — the
  sheaves-of-modules statement of Stacks 095Q, the converse implication and the equivalence.

The equivalence is unconditional, so the sheaves-of-modules part of Stacks 095Q is formalized
here. The only place `f` enters the argument is
`AlgebraicGeometry.exists_epi_of_isColimit_of_surjective_module`.

## Implementation notes

The coefficient universe is `ModuleCat.{u + 1} Λ` for `Λ : Type (u + 1)`, which is the universe at
which the shriek presentations and their compactness are available; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ColimitOfConstructibles`. The two
sheafification side conditions of `AlgebraicGeometry.IsConstructibleModuleSheaf` are the instances
`AlgebraicGeometry.SmallEtale.isRightAdjointPushforward_moduleCatSelf` and
`AlgebraicGeometry.SmallEtale.hasWeakSheafifyOver_moduleCatSelf` at that universe.

The compactness of `f⁻¹ℱ` is used as `CategoryTheory.IsFinitelyPresentable`, which is
`CategoryTheory.IsCardinalPresentable` at `ℵ₀`; a filtered category is `ℵ₀`-filtered, so
`CategoryTheory.IsCardinalPresentable.exists_hom_of_isColimit` applies to the image of the colimit
cocone under inverse image.

## References

* [Stacks Project, Tag 095Q](https://stacks.math.columbia.edu/tag/095Q)
* [Stacks Project, Tag 095G](https://stacks.math.columbia.edu/tag/095G)
* [Stacks Project, Tag 03SA](https://stacks.math.columbia.edu/tag/03SA)
* [Stacks Project, Tag 03RZ](https://stacks.math.columbia.edu/tag/03RZ)
* [Stacks Project, Tag 093C](https://stacks.math.columbia.edu/tag/093C)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts
attribute [local instance] Cardinal.fact_isRegular_aleph0

variable (B : BigEtaleSite.{u}) (Λ : Type (u + 1)) [CommRing Λ] [IsNoetherianRing Λ]
  {X Y : B.Scheme} (f : X ⟶ Y)

/-- The constructible sheaves of `Λ`-modules on the small étale site of a scheme of `B`, as a
property of objects of the category of sheaves of `Λ`-modules, at the coefficient universe of this
file. -/
private abbrev constructibleModuleSheavesOn (Z : B.Scheme) :
    ObjectProperty (Sheaf (SmallEtale.topology B Z.1 Z.property) (ModuleCat.{u + 1} Λ)) :=
  fun F => IsConstructibleModuleSheaf B Z Λ F

/-- The constructible sheaves of `Λ`-modules form a weak Serre subcategory; this is Stacks 03RZ (3)
with its coefficient universe pinned to the one of this file. -/
private instance isWeakSerreClass_constructibleModuleSheavesOn (Z : B.Scheme) :
    (constructibleModuleSheavesOn B Λ Z).IsWeakSerreClass :=
  SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, u + 1, u + 1} B Z Λ

omit [IsNoetherianRing Λ] in
/-- **The descent step of Stacks 095Q for sheaves of modules.** Let `f : X ⟶ Y` be a surjective
morphism of the big étale site and let `ℱ` be the colimit of a filtered diagram of sheaves of
`Λ`-modules on `Y_étale`. If the inverse image `f⁻¹ℱ` is a compact object of the category of
sheaves of `Λ`-modules on `X_étale`, then some coprojection `ℱ_i ⟶ ℱ` is an epimorphism.

Nothing is granted here: inverse image preserves the colimit, being a left adjoint, so compactness
of `f⁻¹ℱ` factors its identity through some `f⁻¹ℱ_i`, which makes `f⁻¹(ℱ_i ⟶ ℱ)` a split
epimorphism, and surjectivity of `f` carries that back to `Y` by
`AlgebraicGeometry.epi_of_epi_smallEtalePullback_module`. This is the one step of the proof of
Stacks 095Q at which `f` is used. -/
public theorem exists_epi_of_isColimit_of_surjective_module
    (hf : Function.Surjective (B.inclusion.map f).base)
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Sheaf (SmallEtale.topology B Y.1 Y.property) (ModuleCat.{u + 1} Λ))
    (t : Cocone D) (ht : IsColimit t)
    (hcompact : IsFinitelyPresentable.{u + 1}
      ((smallEtaleModulePullbackFunctor B Λ f).obj t.pt)) :
    ∃ i : I, Epi (t.ι.app i) := by
  have hadj := (smallEtaleBaseChange B f).sheafAdjunctionContinuous (ModuleCat.{u + 1} Λ)
    (SmallEtale.topology B Y.1 Y.property) (SmallEtale.topology B X.1 X.property)
  have := hadj.leftAdjoint_preservesColimits
  have : IsCardinalPresentable
      ((smallEtaleModulePullbackFunctor B Λ f).mapCocone t).pt Cardinal.aleph0.{u + 1} :=
    hcompact
  have : IsCardinalFiltered I Cardinal.aleph0.{u + 1} :=
    (isCardinalFiltered_aleph0_iff I).2 ‹IsFiltered I›
  obtain ⟨i, r, hr⟩ := IsCardinalPresentable.exists_hom_of_isColimit
    (κ := Cardinal.aleph0.{u + 1})
    (isColimitOfPreserves (smallEtaleModulePullbackFunctor B Λ f) ht) (𝟙 _)
  have hsplit : IsSplitEpi ((smallEtaleModulePullbackFunctor B Λ f).map (t.ι.app i)) :=
    ⟨⟨r, hr⟩⟩
  exact ⟨i, epi_of_epi_smallEtalePullback_module B Λ f hf (t.ι.app i) hsplit.epi⟩

/-- **Stacks 095N at a quasi-compact quasi-separated scheme of `B`**, in the form the descent
argument below consumes it: a sheaf of `Λ`-modules on `Z_étale` is constructible exactly when it
has a finite presentation by the sheaves `j_{U!}Λ` at the quasi-compact quasi-separated étale
objects of `Z`.

This is the unconditional
`AlgebraicGeometry.isConstructibleModuleSheaf_iff_qcqsShriekPresentation`, restated with the
quasi-compactness and quasi-separatedness of `Z` as hypotheses rather than instances so that it
can be applied at a scheme carrying them as hypotheses. -/
private theorem isConstructibleModuleSheaf_iff_qcqs (Z : B.Scheme) (hZc : CompactSpace Z.1)
    (hZq : QuasiSeparatedSpace Z.1)
    (G : Sheaf (SmallEtale.topology B Z.1 Z.property) (ModuleCat.{u + 1} Λ)) :
    IsConstructibleModuleSheaf B Z Λ G ↔
      HasFiniteShriekPresentation.{u, u + 1, u + 1} B Z Λ (IsQCQSEtaleObject B Z) G := by
  have := hZc
  have := hZq
  exact isConstructibleModuleSheaf_iff_qcqsShriekPresentation B Z Λ G

section QuasiCompact

variable (hYc : CompactSpace Y.1) (hYq : QuasiSeparatedSpace Y.1)
  (hXc : CompactSpace X.1) (hXq : QuasiSeparatedSpace X.1)

include hYc hYq hXc hXq

/-- **A sheaf of `Λ`-modules with constructible inverse image is a quotient of a constructible
sheaf.** Let `f : X ⟶ Y` be a surjective morphism of quasi-compact quasi-separated schemes and `ℱ`
a sheaf of `Λ`-modules on `Y_étale` whose inverse image along `f` is constructible. Then there is a
constructible sheaf of `Λ`-modules on `Y_étale` and an epimorphism from it onto `ℱ`.

Nothing is granted. Stacks 093C on `Y`,
`AlgebraicGeometry.moduleSheavesAreFilteredColimitsOfPresentations`, writes `ℱ` as a filtered
colimit of sheaves with a finite shriek presentation, which Stacks 095N makes constructible;
Stacks 095N on `X` makes `f⁻¹ℱ` a compact object, by
`AlgebraicGeometry.isFinitelyPresentable_of_hasFiniteShriekPresentation`; and
`AlgebraicGeometry.exists_epi_of_isColimit_of_surjective_module` then produces the epimorphism. -/
public theorem exists_epi_isConstructibleModuleSheaf_of_pullback
    (hf : Function.Surjective (B.inclusion.map f).base)
    (F : Sheaf (SmallEtale.topology B Y.1 Y.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleModuleSheaf B X Λ ((smallEtaleModulePullbackFunctor B Λ f).obj F)) :
    ∃ (G : Sheaf (SmallEtale.topology B Y.1 Y.property) (ModuleCat.{u + 1} Λ)) (p : G ⟶ F),
      IsConstructibleModuleSheaf B Y Λ G ∧ Epi p := by
  have := hYc
  have := hYq
  obtain ⟨I, hI, hfilt, D, ι, ⟨hcolim⟩, hD⟩ :=
    moduleSheavesAreFilteredColimitsOfPresentations B Y Λ F
  have hcompact : IsFinitelyPresentable.{u + 1}
      ((smallEtaleModulePullbackFunctor B Λ f).obj F) :=
    isFinitelyPresentable_of_hasFiniteShriekPresentation B X Λ (IsQCQSEtaleObject B X)
      (fun W hW => SmallEtale.hasFiniteQuasiCompactCoverings B X W hW.1 hW.2) _
      ((isConstructibleModuleSheaf_iff_qcqs B Λ X hXc hXq _).1 hF)
  obtain ⟨i, hi⟩ := exists_epi_of_isColimit_of_surjective_module B Λ f hf D
    (Cocone.mk F ι) hcolim hcompact
  exact ⟨D.obj i, ι.app i, (isConstructibleModuleSheaf_iff_qcqs B Λ Y hYc hYq _).2 (hD i), hi⟩

/-- **Stacks 095Q for sheaves of modules, the converse implication.** Let `f : X ⟶ Y` be a
surjective morphism of quasi-compact quasi-separated schemes, `Λ` a Noetherian ring and `ℱ` a sheaf
of `Λ`-modules on `Y_étale` whose inverse image `f⁻¹ℱ` is constructible. Then `ℱ` is constructible.

`AlgebraicGeometry.exists_epi_isConstructibleModuleSheaf_of_pullback` applied to `ℱ` gives a
constructible `𝒢` with an epimorphism `p : 𝒢 ⟶ ℱ`; applied to the kernel of `p`, whose inverse
image is the kernel of a map between constructible sheaves, it gives a constructible `ℋ`
surjecting onto that kernel. Then `ℱ` is the cokernel of `ℋ ⟶ ker p ⟶ 𝒢` and so is constructible
by Stacks 03RZ (3). -/
public theorem isConstructibleModuleSheaf_of_isConstructibleModuleSheaf_pullback
    (hf : Function.Surjective (B.inclusion.map f).base)
    (F : Sheaf (SmallEtale.topology B Y.1 Y.property) (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleModuleSheaf B X Λ ((smallEtaleModulePullbackFunctor B Λ f).obj F)) :
    IsConstructibleModuleSheaf B Y Λ F := by
  have := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B X Λ
  have := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B Y Λ
  have hexact : PreservesFiniteLimits (smallEtaleModulePullbackFunctor B Λ f) :=
    preservesFiniteLimits_smallEtaleSheafPullback_moduleCat.{u + 1, u, u + 1} B f Λ
  obtain ⟨G, p, hG, hp⟩ :=
    exists_epi_isConstructibleModuleSheaf_of_pullback B Λ f hYc hYq hXc hXq hf F hF
  have := hp
  have hGpull : IsConstructibleModuleSheaf B X Λ
      ((smallEtaleModulePullbackFunctor B Λ f).obj G) :=
    isConstructibleModuleSheaf_pullback B Λ f G hG
  have hKpull : IsConstructibleModuleSheaf B X Λ
      ((smallEtaleModulePullbackFunctor B Λ f).obj (kernel p)) :=
    (constructibleModuleSheavesOn B Λ X).prop_of_iso
      (PreservesKernel.iso (smallEtaleModulePullbackFunctor B Λ f) p).symm
      ((constructibleModuleSheavesOn B Λ X).prop_kernel
        ((smallEtaleModulePullbackFunctor B Λ f).map p) hGpull hF)
  obtain ⟨H, q, hH, hq⟩ := exists_epi_isConstructibleModuleSheaf_of_pullback B Λ f hYc hYq hXc
    hXq hf (kernel p) hKpull
  have := hq
  have hcoker : IsColimit (CokernelCofork.ofπ (f := q ≫ kernel.ι p) p
      (by rw [Category.assoc, kernel.condition, comp_zero])) :=
    isCokernelEpiComp (c := CokernelCofork.ofπ p (kernel.condition p))
      (Abelian.epiIsCokernelOfKernel _ (limit.isLimit _)) q rfl
  exact (constructibleModuleSheavesOn B Λ Y).prop_of_iso
    ((colimit.isColimit _).coconePointUniqueUpToIso hcoker)
    ((constructibleModuleSheavesOn B Λ Y).prop_cokernel (q ≫ kernel.ι p) hH hG)

/-- **Stacks 095Q for sheaves of modules.** Let `f : X ⟶ Y` be a surjective morphism of
quasi-compact and quasi-separated schemes, `Λ` a Noetherian ring and `ℱ` a sheaf of `Λ`-modules on
`Y_étale`. Then `ℱ` is constructible if and only if `f⁻¹ℱ` is constructible.

The forward implication is Stacks 095G, `AlgebraicGeometry.isConstructibleModuleSheaf_pullback`,
and needs neither surjectivity of `f` nor quasi-compactness. The converse is
`AlgebraicGeometry.isConstructibleModuleSheaf_of_isConstructibleModuleSheaf_pullback`.

Nothing is granted. The two statements of the source that were once hypotheses here are both
proved in the library, and both are supplied from `hXc`, `hXq`, `hYc` and `hYq`, the
quasi-compactness and quasi-separatedness of `X` and `Y` that the source's statement assumes:
Stacks 095N on the quasi-compact quasi-separated schemes of `B`, from the unconditional
`AlgebraicGeometry.isConstructibleModuleSheaf_iff_qcqsShriekPresentation`, and Stacks 093C (2) on
`Y`, from `AlgebraicGeometry.moduleSheavesAreFilteredColimitsOfPresentations`. -/
@[stacks 095Q "sheaves of modules"]
public theorem isConstructibleModuleSheaf_pullback_iff_of_surjective
    (hf : Function.Surjective (B.inclusion.map f).base)
    (F : Sheaf (SmallEtale.topology B Y.1 Y.property) (ModuleCat.{u + 1} Λ)) :
    IsConstructibleModuleSheaf B Y Λ F ↔
      IsConstructibleModuleSheaf B X Λ ((smallEtaleModulePullbackFunctor B Λ f).obj F) :=
  ⟨fun hF => isConstructibleModuleSheaf_pullback B Λ f F hF,
    isConstructibleModuleSheaf_of_isConstructibleModuleSheaf_pullback B Λ f hYc hYq hXc hXq
      hf F⟩

end QuasiCompact

end AlgebraicGeometry

end
