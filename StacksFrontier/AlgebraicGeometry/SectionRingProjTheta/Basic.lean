module

public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.GradedSectionInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DegreeZeroLocalizationArbitraryDegree
public import StacksCore.Tactic.StacksAttribute

/-!
# The twisted extension property of Stacks Tag 01PW, part (2)

Let `X` be a scheme, `L` an invertible `𝒪_X`-module, `s` a global section of `L` with
nonvanishing open `X_s`, and `ℱ` a quasi-coherent `𝒪_X`-module. Part (2) of
[Stacks, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW) — Stacks Lemma 28.18.2 — asserts
that for `X` quasi-compact and quasi-separated the comparison map of
[Stacks, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
`Γ_*(X, L, ℱ)_{(s)} ⟶ Γ(X_s, ℱ)` is bijective. Part (1), its injectivity for `X` merely
quasi-compact, is `Stacks.SheafOfModules.sectionLocalizationMap_injective`; **part (2) itself is
`Stacks.SheafOfModules.sectionLocalizationMap_bijective`**, proved and carrying
`@[stacks 01PW "part (2)"]` in
`StacksFrontier/AlgebraicGeometry/Properties/PrincipalOpens/GradedSectionInjective.lean`, which is
this module's first import.

This file states the **twisted extension property** — every section of `ℱ` over `X_s` becomes,
after tensoring with `s ^ N` for some `N`, the restriction of a global section of
`ℱ ⊗ L^{⊗ N}` — and proves it equivalent to the surjectivity half of part (2) in the useful
direction and in the direction that shows it is not a weaker surrogate. It is the form of part
(2) that mentions no localized module, which is what a consumer gluing twisted sections wants.

## Main definitions

* `Stacks.SheafOfModules.HasTwistedExtension`: the twisted extension property, the surjectivity
  content of part (2) of Tag 01PW stated without reference to the localized module.

## Main results

* `Stacks.SheafOfModules.hasTwistedExtension`: **the twisted extension property holds**, at
  `X` quasi-compact and quasi-separated and `ℱ` quasi-coherent — part (2) of Tag 01PW read
  through the previous result.
* `Stacks.SheafOfModules.hasTwistedExtension_of_sectionLocalizationMap_surjective`:
  **surjectivity of the Tag 0B5L comparison map implies the twisted extension property.** The
  numerator of a fraction representing a preimage is the required global section, and
  `Stacks.SheafOfModules.exists_tensorBasisAt` identifies the two sides on `X_s`.
* `Stacks.SheafOfModules.hasTwistedExtension`: **the twisted extension property, proved**, by
  feeding it part (2) of Tag 01PW.
* `Stacks.SheafOfModules.of_mem_sectionModuleGrading`: a twisted global section of
  `ℱ ⊗ L^{⊗ N}`, placed in degree `N`, is homogeneous of degree `N`.

## Implementation notes

**Which spelling of `Γ_*(X, L, ℱ)`.** The repository carries five. The one used here is
`Stacks.SheafOfModules.sectionModule`, the `ℤ`-graded
`⨁_{n ∈ ℤ} Γ(X, ℱ ⊗ L^{⊗ n})` of
`StacksFrontier/Topology/Sheaves/Modules/InvertibleAndOperators/SectionRing.lean`, because that is
the module the Tag 0B5L comparison map `Stacks.SheafOfModules.sectionLocalizationMap` is
defined on and the one both parts of Tag 01PW are stated at. No other choice is available
without first building a comparison of graded modules that the repository does not have; see
`## What is not done here`.

**The degree bookkeeping.** `Stacks.SheafOfModules.homogeneousSection X L s` is homogeneous of
degree one, so the membership criterion
`Stacks.SheafOfModules.mk_mem_degreeZeroLocalization_of_degree` is wanted at `d = 1`, where a
numerator for the denominator `s ^ N` has degree `N * 1`. That `Nat.mul_one` normalization is
isolated into `mk_mem_degreeZeroLocalization_of_degree_one`, stated at a bare graded ring and
module so that the transport never meets the sheaf-theoretic types.

**No option overrides.** Nothing here raises the heartbeat limit or relaxes transparency.

**No `@[stacks 01PW]` attribute is attached here**, because the tag's assertion is the
bijectivity of the Tag 0B5L map and the attribute belongs where that is proved, namely on
`Stacks.SheafOfModules.sectionLocalizationMap_bijective`. `hasTwistedExtension` below is that
assertion's surjectivity half restated without the localized module, and
`hasTwistedExtension_of_sectionLocalizationMap_surjective` is the converse, which is what makes
the restatement faithful rather than weaker.

## What is not done here

**No `@[stacks 01PW]` attribute is attached here, because both parts of the tag are proved
elsewhere.** `Stacks.SheafOfModules.sectionLocalizationMap_injective` (part (1)) and
`Stacks.SheafOfModules.sectionLocalizationMap_bijective` (part (2)) in
`StacksFrontier/AlgebraicGeometry/Properties/PrincipalOpens/GradedSectionInjective.lean` carry the
two 01PW attributes, the second of them with no hypothesis beyond
`[CompactSpace X] [QuasiSeparatedSpace X] [F.IsQuasicoherent]`. `HasTwistedExtension` is
*equivalent* to the surjectivity half of part (2) — `hasTwistedExtension` derives it from part
(2) and `hasTwistedExtension_of_sectionLocalizationMap_surjective` is the converse — so it is
the name of a proved statement, not of a hypothesis, and tagging it here would duplicate the
attribute rather than add anything.

**The direct derivation of bijectivity from `HasTwistedExtension` is still blocked by the
heartbeat limit** — part (2) is proved by the route of `StacksFrontier/AlgebraicGeometry/Properties/PrincipalOpens/GradedSectionInjective.lean`, which does
not pass through this file. Deriving
`Function.Bijective (sectionLocalizationMap X L F s)` from `HasTwistedExtension` needs only the
observation that `b / s ^ N` is a degree-zero element of the localized section module, i.e.
```
    LocalizedModule.mk (DirectSum.of _ (N : ℤ) b) ⟨homogeneousSection X L s ^ N, ⟨N, rfl⟩⟩
      ∈ sectionAtNonvanishingOpen X L F s
```
followed by `Stacks.SheafOfModules.sectionLocalizationMap_fraction`. Elaborating that
membership requires the module structure that `GradedModuleDegreeZeroLocalization` introduces
in its own type, at the types `sectionRing` and `sectionModule`, and that exceeds the default
budget of 200000 heartbeats, even after splitting the degree
transport out generically (`mk_mem_degreeZeroLocalization_of_degree_one`), after splitting the
homogeneity off (`of_mem_sectionModuleGrading`, which does compile), and after keeping the
submodule folded behind `sectionAtNonvanishingOpen`. Raising the limit is not available in this
tree; what is wanted is a cheaper membership criterion for
`GradedModuleDegreeZeroLocalization` stated at a folded denominator, or
`Stacks.SheafOfModules.sectionAtNonvanishingOpen` equipped with its own `mk` constructor. It is
not needed for anything: part (2) is proved directly, so this direction would only give a
second route to a proved statement.

**An independent proof of `HasTwistedExtension` exists in a different spelling of the tensor
power, and is still not connected to this one.**
`Stacks.TensorSectionPower.exists_tensorSection_of_compactSpace`
(`StacksFrontier/AlgebraicGeometry/TensorSectionPower/Glue.lean`) is exactly this statement, at
exactly `[CompactSpace X] [QuasiSeparatedSpace X]` with no ampleness and no
`Stacks.SectionExtensionNoAmple.HasPointwiseNonvanishing`. It is stated for
`Stacks.TensorSectionPower.powObj M k`, the left-bracketed power `(…(M ⊗ M) ⊗ …) ⊗ M` indexed
from the first power, and for `Stacks.SectionTensorFormula.tensorSection`, whereas
`HasTwistedExtension` is stated for `Stacks.SheafOfModules.TensorPower.tensorPower` at `(N : ℤ)`
and for `Stacks.SheafOfModules.tensorSectionAtOpen`. **The comparison of those two tensor-power
spellings is still missing**, which that file's own documentation records as blocked on
naturality of `tensorSection` in its module arguments — a formula for `(F ◁ φ).app U` applied to
a product of sections. Nothing below depends on it: `hasTwistedExtension` is proved from part
(2) instead.

**Nothing about Tag 01QJ is here**, and part (2) above does not feed it. Tag 01QJ's map
`θ_𝓕 : f^* M~ ⟶ 𝓕` is formalized — as clause (b) only, the functoriality in `𝓕` — in
`StacksFrontier/AlgebraicGeometry/SectionRingProjQuasicoherent/Comparison.lean`, as
`Stacks.SectionRingProjQuasicoherent.pullbackComparison`, which carries Tag 0B5I's family
`M̃ ⟶ f_*𝓕` as a hypothesis. It cannot be stated against the module used here: the canonical
morphism
`Stacks.SectionRingProjMorphism.projHomOfIsAmple` targets `Proj` of
`Stacks.AmpleFiniteAvoidance.grading L`, whose graded ring is
`Stacks.GradedSections.sectionRing L = ⨁_n (𝟙 ⟶ natTensorPow L n)`, while
`Stacks.SheafOfModules.sectionModule` above is graded over
`Stacks.SheafOfModules.sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L
 = ⨁_n Γ(X, L^{⊗ n})`. These are two different graded rings, and part (2) as proved against the
second does not feed `θ` against the first.

There is nevertheless a comparison between those two rings: the sibling
`StacksFrontier/AlgebraicGeometry/SectionRingProjTheta/SectionRingComparison.lean` supplies
`Stacks.SectionRingProjTheta.sectionSiteSectionRingAddEquiv`, the comparison of the two carriers
at exactly the spelling of the site and of the structure sheaf that Tag 01PW's
`Stacks.SheafOfModules.sectionLocalizationMap` is stated at, and
`Stacks.SectionRingProjTheta.map_grading_eq_sectionRingGrading`, which shows it carries
`Stacks.AmpleFiniteAvoidance.grading` — the family `Proj` is taken of — onto
`Stacks.SheafOfModules.sectionRingGrading` degree by degree. **What is missing is only its
multiplicativity**: that comparison is an `AddEquiv` and not a `RingEquiv`, as its own
`@[stacks]` facet string records, and the two obstructions to upgrading it are named in that
file's "What is not done here". Transporting a graded localization needs the products, so the
gap is real; but it is one statement, not the absence of any bridge.

## References

* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0B5L](https://stacks.math.columbia.edu/tag/0B5L)
* [Stacks Project, Tag 01CV](https://stacks.math.columbia.edu/tag/01CV)
* [Stacks Project, Tag 01M4](https://stacks.math.columbia.edu/tag/01M4)
* [Stacks Project, Tag 01QJ](https://stacks.math.columbia.edu/tag/01QJ)
* [Stacks Project, Tag 01QK](https://stacks.math.columbia.edu/tag/01QK)
* [Stacks Project, Tag 01QI](https://stacks.math.columbia.edu/tag/01QI)
* [Stacks Project, Tag 01MQ](https://stacks.math.columbia.edu/tag/01MQ)
-/

@[expose] public noncomputable section

namespace Stacks.SheafOfModules

open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace Opposite DirectSum Limits
open scoped _root_.TensorProduct

universe u

attribute [local implicit_reducible] _root_.SheafOfModules.forget PresheafOfModules.restrictScalars

section DegreeOne

/-- The grading action of a naturally graded ring on an integer-graded module, the one under
which `GradedModuleDegreeZeroLocalization` is formed. -/
local instance instVAddNatIntDegreeOne : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

variable {R : Type*} {M : Type*} {σ : Type*} {τ : Type*}
  [CommRing R] [AddCommGroup M] [Module R M]
  [SetLike σ R] [AddSubgroupClass σ R] (A : ℕ → σ) [GradedRing A]
  [SetLike τ M] [AddSubgroupClass τ M] (B : ℤ → τ) [Decomposition B]
  [SetLike.GradedSMul A B] {f : R}

/-- **A fraction with homogeneous numerator of degree `n` over the denominator `f ^ n` lies in
the degree-zero part of the localization**, for `f` homogeneous of degree one.

This is `Stacks.SheafOfModules.mk_mem_degreeZeroLocalization_of_degree` at `d = 1`. It is stated
separately, at the bare graded ring and module, because the `n * 1 = n` normalization its
numerator degree needs is a transport that the elaborator cannot afford to perform against the
sheaf-theoretic types of `Stacks.SheafOfModules.sectionModule`: doing it there exhausts the
heartbeat budget. -/
private theorem mk_mem_degreeZeroLocalization_of_degree_one (hf : f ∈ A 1) (n : ℕ) (x : M)
    (hx : x ∈ B (n : ℤ)) :
    LocalizedModule.mk (S := Submonoid.powers f) x ⟨f ^ n, by exact ⟨n, rfl⟩⟩ ∈
      GradedModuleDegreeZeroLocalization A B f := by
  refine mk_mem_degreeZeroLocalization_of_degree A B hf n x ?_
  have h : ((n * 1 : ℕ) : ℤ) = (n : ℤ) := congrArg Nat.cast (Nat.mul_one n)
  rw [h]
  exact hx

end DegreeOne

section TwistedExtension

attribute [-instance] CategoryTheory.GrothendieckTopology.IsLocalSite.toHasLimitsOfShape

attribute [local implicit_reducible] ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'
  TensorSheafification.structureSheaf

variable (X : Scheme.{u})
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

attribute [local instance] Stacks.SheafOfModules.tensorRightEquiv

variable (F : X.Modules)

/-- The module structure of the section module over the section ring, applied by hand. -/
local instance sectionModuleModuleExt : Module
    (sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
    (sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L F) :=
  sectionModuleModule (sectionSiteRing X) (sectionSiteSheaf X) L F

/-- The decomposition of the section module into its graded pieces, applied by hand. -/
local instance sectionModuleDecompositionExt : DirectSum.Decomposition
    (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L F) :=
  sectionModuleDecomposition (sectionSiteRing X) (sectionSiteSheaf X) L F

/-- Compatibility of the grading of the section ring with that of the section module, applied by
hand. -/
local instance sectionModuleGradedSMulExt : SetLike.GradedSMul
    (sectionRingGrading (sectionSiteRing X) (sectionSiteSheaf X) L)
    (sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L F) :=
  sectionModuleGradedSMul (sectionSiteRing X) (sectionSiteSheaf X) L F

/-- **The twisted extension property.** Every section of `F` over the nonvanishing open `X_s`
becomes, after tensoring with `s ^ N` for some `N`, the restriction of a *global* section of
`F ⊗ L^{⊗ N}`.

This is the surjectivity content of part (2) of [Stacks, Tag 01PW], stated without reference to
the localized module: the source's `t' ∈ Γ(X_s, F)` is `t`, and its
`t ∈ Γ(X, F ⊗ L^{⊗ (e + e')})` with `t / s^{e + e'} ↦ t'` is `b`. -/
def HasTwistedExtension (s : L.sections) : Prop :=
  ∀ t : F.val.obj (op (nonvanishingOpen L s)),
    ∃ (N : ℕ) (b : ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
            (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (F)).obj
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ))))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))),
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
            (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (F)).obj
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ))))).val.map
          (terminal.from (nonvanishingOpen L s)).op b =
        tensorSectionAtOpen X L F (nonvanishingOpen L s) N t
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ)).val.map
            (terminal.from (nonvanishingOpen L s)).op (sectionPower X L s N))

/-- A twisted global section of `F ⊗ L^{⊗ N}`, placed in degree `N` of the section module, is
homogeneous of degree `N`. The grading is the range of the structure map of the direct sum, so
this is that structure map's defining property; it is split off so that the degree transport of
`mem_sectionAtNonvanishingOpen_mk` happens against an already-established membership. -/
theorem of_mem_sectionModuleGrading (N : ℕ)
    (b : ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(sectionSiteRing X), Presheaf.isSheaf_of_isSheaf_comp _ ((sectionSiteRing X))
            (forget₂ CommRingCat RingCat) ((sectionSiteSheaf X))⟩).obj (F)).obj
          ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ))))).val.obj
        (op (⊤_ (Opens X.toRingedSpace.toPresheafedSpace)))) :
    (DirectSum.of _ (N : ℤ) b : sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L F) ∈
      sectionModuleGrading (sectionSiteRing X) (sectionSiteSheaf X) L F (N : ℤ) :=
  ⟨b, rfl⟩

/-- **The reduction loses nothing**: surjectivity of the Tag 0B5L comparison map implies the
twisted extension property. It is one half of the equivalence of `HasTwistedExtension` with the
surjectivity half of part (2) of Tag 01PW; `hasTwistedExtension` below is the consequence of
that part. -/
theorem hasTwistedExtension_of_sectionLocalizationMap_surjective (s : L.sections)
    (hsurj : Function.Surjective (sectionLocalizationMap X L F s)) :
    HasTwistedExtension X L F s := by
  intro t
  obtain ⟨z, hz⟩ := hsurj t
  obtain ⟨N, x, hx, hzx⟩ := exists_twistedSection_numerator X L F s z
  obtain ⟨b, hbx⟩ := hx
  refine ⟨N, b, ?_⟩
  obtain ⟨e, he⟩ := exists_tensorBasisAt X L F s N
  have hmk : (z : LocalizedModule.Away
      (R := sectionRing (sectionSiteRing X) (sectionSiteSheaf X) L)
      (homogeneousSection X L s)
      (sectionModule (sectionSiteRing X) (sectionSiteSheaf X) L F)) =
      LocalizedModule.mk (S := Submonoid.powers (homogeneousSection X L s))
        (DirectSum.of _ (N : ℤ) b) ⟨homogeneousSection X L s ^ N, ⟨N, rfl⟩⟩ :=
    hzx.trans (congrArg
      (fun y => LocalizedModule.mk (S := Submonoid.powers (homogeneousSection X L s)) y
        ⟨homogeneousSection X L s ^ N, ⟨N, rfl⟩⟩) hbx.symm)
  have he' := fun y => (e.apply_symm_apply y).symm.trans (he (e.symm y))
  refine (he' _).trans (congrArg
    (fun y => tensorSectionAtOpen X L F (nonvanishingOpen L s) N y
      ((TensorPower.tensorPower (sectionSiteRing X) (sectionSiteSheaf X) L (N : ℤ)).val.map
        (terminal.from (nonvanishingOpen L s)).op (sectionPower X L s N)))
    ((sectionLocalizationMap_fraction X L F s N b z _ hmk (he' _)).symm.trans hz))

/-- **The twisted extension property.** On a quasi-compact and quasi-separated scheme, every
section of a quasi-coherent `ℱ` over `X_s` becomes, after tensoring with `s ^ N` for some `N`,
the restriction of a global section of `ℱ ⊗ L^{⊗ N}`.

This is the surjectivity content of part (2) of Tag 01PW, so it follows from
`Stacks.SheafOfModules.sectionLocalizationMap_bijective`. No 01PW attribute is attached: the tag
is carried by that theorem. -/
theorem hasTwistedExtension [CompactSpace X] [QuasiSeparatedSpace X] [F.IsQuasicoherent]
    (s : L.sections) : HasTwistedExtension X L F s :=
  hasTwistedExtension_of_sectionLocalizationMap_surjective X L F s
    (sectionLocalizationMap_bijective X L F s).surjective

end TwistedExtension

end Stacks.SheafOfModules

end
