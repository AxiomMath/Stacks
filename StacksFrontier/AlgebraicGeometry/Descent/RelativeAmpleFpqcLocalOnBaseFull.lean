module

public import StacksFrontier.AlgebraicGeometry.AmpleQuasiAffineCover.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.RelativeAmpleFpqcLocalOnBase
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineBaseReduction
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.GlobalSections
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.FpqcDescent
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.LocalOnBase
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.CoveringRefinement
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 0D2P in full: relative ampleness descends along an fpqc covering of the base

Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible `𝒪_X`-module, and
`{g i : S' i ⟶ S}` an fpqc covering of the base. Write `f' i : X' i ⟶ S' i` for the base change
of `f` along `g i` and `p i : X' i ⟶ X` for the other projection, so that `(p i)^* L` is the
pullback of `L`. [Stacks, Tag 0D2P] asserts

> `L` is ample relative to `f` **if and only if** `(p i)^* L` is ample relative to `f' i` for
> every `i`.

`StacksFrontier/AlgebraicGeometry/Descent/RelativeAmpleFpqcLocalOnBase.lean` proves the implication
`(1) ⟹ (2)`, the first two steps of `(2) ⟹ (1)` (that `f` is quasi-compact and separated), and
the whole equivalence for a module isomorphic to the structure sheaf. This file completes
`(2) ⟹ (1)` for an arbitrary invertible module and an arbitrary fpqc covering indexed by an
arbitrary type, and states the equivalence.

Relative ampleness throughout is `Stacks.RelativeAmple.IsRelativelyAmple`, the library's form of
[Stacks, Tag 01VH]; no new predicate is introduced.

## Main results

* `Stacks.Descent.isRelativelyAmple_iff_forall_of_fpqcCover`: **Tag 0D2P** in full, the
  equivalence for an arbitrary invertible module and an arbitrary fpqc covering of the base. The
  source assumes nothing beyond that, so this statement is the whole tag and carries it.
* `Stacks.Descent.isRelativelyAmple_of_forall_of_fpqcCover`: **Tag 0D2P, (2) implies (1)**.
* `Stacks.Descent.isAmple_of_forall_isAmple_pullbackModule_of_affineFlatCover`: the core of
  (2) implies (1), over an affine base and a finite covering by affine schemes.
* `Stacks.Descent.exists_mem_nonvanishingLocus_of_isPullback`: flat base change for global
  sections at a point, which is how [Stacks, Tag 02KH] enters.

## The route

For `(2) ⟹ (1)`, the source's proof extracts from clause (2) two properties of `f` alone:
quasi-compactness, which is part of the definition of relative ampleness ([Stacks, Tag 01VH]),
and separatedness, which is [Stacks, Tag 01VI], formalized as
`AlgebraicGeometry.Scheme.Modules.IsRelativelyAmple.isSeparated`. Both descend along the
covering because each is fpqc local on the base — [Stacks, Tag 02KQ],
`Stacks.Descent.quasiCompact_isLocalAtTarget_fpqc`, and
`AlgebraicGeometry.isSeparated_isLocalAtTarget_fpqc`.

**From there the source goes through relative `Proj`, and the proof here does not.** The source
forms the quasi-coherent graded `𝒪_S`-algebra `𝒜 = ⨁_{d ≥ 0} f_* L^{⊗ d}` and the morphism
`r_{L, ψ} : X ⟶ Proj_S(𝒜)` of [Stacks, Tag 01O9], and reads ampleness off `r_{L, ψ}` being an
open immersion (clauses (4)–(6) of [Stacks, Tag 01VJ]). This repository constructs neither that
relative `Proj` nor the relative `ψ`. What replaces them is the *absolute* content of
[Stacks, Tag 01PW], which is what makes relative `Proj` work in the first place, used over the
affine opens of the base:

* **Reduction to an affine base.** Relative ampleness may be checked on an affine open covering
  of the base — [Stacks, Tag 01VJ], clause (3) implies clause (1),
  `Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple`. The definition of
  an fpqc covering gives, around each point of `S`, an affine open `V` and finitely many affine
  opens of members of the covering whose images cover `V`; restricting the cartesian squares to
  those opens is
  `Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isPullback_restrictBasesSquare`. So
  everything happens over an affine base, for a finite covering by affine schemes.
* **The nonvanishing opens cover.** At a point of `f⁻¹V`, ampleness upstairs supplies a global
  section of a tensor power of the pullback of `L` that does not vanish above it. Flat base
  change for sections — [Stacks, Tag 02KH] in degree zero,
  `Stacks.AlgebraicGeometry.SectionsBaseChange.exists_linearEquiv_sections_baseChange` — writes
  that section as a combination of pullbacks of global sections downstairs, so one of those does
  not vanish at the point ([Stacks, Tag 0H78] transports the nonvanishing).
* **Each nonvanishing open is quasi-affine.** Its base change to each member of the covering is
  the nonvanishing open of the pulled-back section, which is quasi-affine because the pulled-back
  module is ample there (`Stacks.AmpleAffineAvoidance.isQuasiAffine_nvOpen`), and quasi-affine
  morphisms are fpqc local on the base ([Stacks, Tag 02L7]).
* **Quasi-affine nonvanishing opens suffice for ampleness.** This is
  `Stacks.AmpleQuasiAffineCover.isAmple_of_forall_exists_isQuasiAffine_nonvanishingOpen`, whose
  engine is the surjectivity half of [Stacks, Tag 01PW] run over a quasi-compact rather than an
  affine cover, `Stacks.SectionRingChartBijective.exists_ratio_powSec_of_compact_cover`.

## References

* [Stacks Project, Tag 0D2P](https://stacks.math.columbia.edu/tag/0D2P)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01VI](https://stacks.math.columbia.edu/tag/01VI)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 0891](https://stacks.math.columbia.edu/tag/0891)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 02KQ](https://stacks.math.columbia.edu/tag/02KQ)
* [Stacks Project, Tag 02L7](https://stacks.math.columbia.edu/tag/02L7)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Ample (IsInvertibleModule unitModule)
open Stacks.AmpleLocallyClosed (pullbackModule)

universe v u

namespace Stacks.Descent

/-! ### Clause (2) implies clause (1): the affine-base core -/

section AffineCore

open Stacks.Ample (IsAmple nonvanishingLocus mem_nonvanishingLocus_iff tensorPowModule)
open Stacks.AlgebraicGeometry.SectionsBaseChange
open scoped TensorProduct

/-- **A section of a quasi-coherent module that survives a flat affine base change is the
restriction of nothing, but its nonvanishing points are hit by global sections downstairs.** For
a cartesian square with affine bases and flat `t`, a point `w` of the corner at which a global
section of the pullback of `F` does not vanish lies over a point at which *some* global section
of `F` does not vanish.

This is [Stacks, Tag 02KH] in degree zero, in the shape
`Stacks.AlgebraicGeometry.SectionsBaseChange.exists_linearEquiv_sections_baseChange`: every
global section of the pullback is a `Γ(T, 𝒪)`-combination of pullbacks of global sections of `F`,
and the germs of the latter all lie in `𝔪_w · (p^* F)_w` as soon as the germs downstairs lie in
`𝔪_{p w} · F_{p w}` ([Stacks, Tag 0H78]). -/
theorem exists_mem_nonvanishingLocus_of_isPullback {V T Y W : Scheme.{u}} [IsAffine V]
    [IsAffine T] {q : Y ⟶ V} {t : T ⟶ V} [Flat t] {pr : W ⟶ Y} {k : W ⟶ T}
    (H : IsPullback pr k q t) [CompactSpace Y] [QuasiSeparatedSpace Y]
    (F : Y.Modules) [F.IsQuasicoherent] (σ : Γ((Scheme.Modules.pullback pr).obj F, ⊤)) {w : W}
    (hw : w ∈ nonvanishingLocus ((Scheme.Modules.pullback pr).obj F) σ) :
    ∃ a : Γ(F, ⊤), pr.base w ∈ nonvanishingLocus F a := by
  classical
  by_contra hcontra
  have hcon : ∀ a : Γ(F, ⊤), pr.base w ∉ nonvanishingLocus F a := fun a ha => hcontra ⟨a, ha⟩
  -- the pullback of every global section of `F` vanishes at `w`
  have hvan : ∀ a : Γ(F, ⊤),
      ((((Scheme.Modules.pullback pr).obj F).presheaf.Γgerm w)).hom
          (pullbackSectionsHom pr F ⊤ ⊤ (le_preimage_top pr ⊤) a)
        ∈ Stacks.ModuleStalk.maximalSmul ((Scheme.Modules.pullback pr).obj F) w := by
    intro a
    have hmem : w ∉ nonvanishingLocus ((Scheme.Modules.pullback pr).obj F)
        (pullbackSectionsHom pr F ⊤ ⊤ (le_preimage_top pr ⊤) a) := by
      rw [show pullbackSectionsHom pr F ⊤ ⊤ (le_preimage_top pr ⊤) a
          = Stacks.NonvanishingPullback.pullbackGlobalSection pr F a from
            pullbackSectionsHom_top pr F a,
        ← Stacks.NonvanishingPullback.pullbackGlobalSections_eq_pullbackGlobalSection,
        ← Stacks.NonvanishingPullback.preimage_nonvanishingLocus_pullbackGlobalSections]
      exact hcon a
    exact not_not.mp (fun hc => hmem hc)
  let := baseAlgebra t
  let := baseModule q F ⊤
  let := baseModule (pr ≫ q) ((Scheme.Modules.pullback pr).obj F) ⊤
  let := baseModule k ((Scheme.Modules.pullback pr).obj F) ⊤
  let := baseTower H ((Scheme.Modules.pullback pr).obj F) ⊤
  obtain ⟨e, he⟩ := exists_linearEquiv_sections_baseChange H F
  -- every element of the base change has germ in `𝔪_w · G_w`
  have key : ∀ z : Γ(T, ⊤) ⊗[Γ(V, ⊤)] Γ(F, ⊤),
      ((((Scheme.Modules.pullback pr).obj F).presheaf.Γgerm w)).hom (e z)
        ∈ Stacks.ModuleStalk.maximalSmul ((Scheme.Modules.pullback pr).obj F) w := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
        rw [map_zero, map_zero]
        exact Submodule.zero_mem _
    | tmul b a =>
        rw [he b a]
        have hsm : (b • pullbackSectionsHom pr F ⊤ ⊤ (le_preimage_top pr ⊤) a :
              Γ((Scheme.Modules.pullback pr).obj F, ⊤))
            = ((k.appLE ⊤ ⊤ (le_preimage_top k ⊤)).hom b) •
              pullbackSectionsHom pr F ⊤ ⊤ (le_preimage_top pr ⊤) a := rfl
        rw [hsm, Stacks.ModuleStalk.Γgerm_smul]
        exact Submodule.smul_mem _ _ (hvan a)
    | add z₁ z₂ h₁ h₂ =>
        rw [map_add, map_add]
        exact Submodule.add_mem _ h₁ h₂
  obtain ⟨z, hz⟩ := e.surjective σ
  refine hw ?_
  rw [← hz]
  exact key z

/-- **Clause (2) implies clause (1) of [Stacks, Tag 0D2P] over an affine base, for a finite
covering by affine schemes.** Let `V` be an affine scheme, `qY : Y ⟶ V` a morphism out of a
quasi-compact quasi-separated scheme and `M` an invertible `𝒪_Y`-module. Let `{t j : T j ⟶ V}` be
a finite jointly surjective family of flat morphisms from affine schemes, and let `Y' j` be the
base change of `Y` along `t j`. If the pullback of `M` to each `Y' j` is ample, then `M` is
ample.

At a point `y` of `Y`, pick `j` with `qY y` in the image of `t j` and a point `w` of `Y' j` above
`y`; ampleness upstairs gives a global section of a positive tensor power of the pullback of `M`
not vanishing at `w`, and `Stacks.Descent.exists_mem_nonvanishingLocus_of_isPullback` — flat base
change for sections, [Stacks, Tag 02KH] — replaces it by a global section `a` of the same tensor
power of `M` not vanishing at `y`. The nonvanishing open `Y_a` is then quasi-affine: its base
change to each `T j` is the nonvanishing open of the pullback of `a`, quasi-affine because the
pullback of `M` is ample there
(`Stacks.AmpleQuasiAffineCover.isQuasiAffine_nonvanishingOpen_of_isAmple`), and quasi-affine
morphisms are fpqc local on the base ([Stacks, Tag 02L7]). Finally
`Stacks.AmpleQuasiAffineCover.isAmple_of_forall_exists_isQuasiAffine_nonvanishingOpen` upgrades a
cover by quasi-affine nonvanishing opens to ampleness. -/
theorem isAmple_of_forall_isAmple_pullbackModule_of_affineFlatCover {V Y : Scheme.{u}}
    [IsAffine V] (qY : Y ⟶ V) [CompactSpace Y] [QuasiSeparatedSpace Y] (M : Y.Modules)
    [IsInvertibleModule Y M] {m : ℕ} {T : Fin m → Scheme.{u}} [∀ j, IsAffine (T j)]
    {t : ∀ j, T j ⟶ V} [∀ j, Flat (t j)] (hcov : ∀ v : V, ∃ j, v ∈ Set.range (t j).base)
    {Y' : Fin m → Scheme.{u}} {pr : ∀ j, Y' j ⟶ Y} {q' : ∀ j, Y' j ⟶ T j}
    (hsq : ∀ j, IsPullback (pr j) (q' j) qY (t j))
    (hA : ∀ j, IsAmple (Y' j) (pullbackModule (pr j) M)) :
    IsAmple Y M := by
  have hfpqc : Presieve.ofArrows T t ∈ Scheme.fpqcPrecoverage V :=
    AlgebraicGeometry.Scheme.ofArrows_mem_fpqcPrecoverage_of_finite inferInstance T t
      (fun j => inferInstance) (fun j => inferInstance) hcov
  refine Stacks.AmpleQuasiAffineCover.isAmple_of_forall_exists_isQuasiAffine_nonvanishingOpen
    M fun y => ?_
  -- the comparison `(pr i)^* (M ^⊗ n) ≅ ((pr i)^* M) ^⊗ n`, read in `(Y' i).Modules`
  let e : ∀ (i : Fin m) (n : ℕ),
      ((Scheme.Modules.pullback (pr i)).obj (tensorPowModule Y M (n : ℤ)) : (Y' i).Modules) ≅
        tensorPowModule (Y' i) (pullbackModule (pr i) M) (n : ℤ) := fun i n =>
    Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso (pr i) M n
  obtain ⟨j, hj⟩ := hcov (qY.base y)
  obtain ⟨v, hv⟩ := hj
  obtain ⟨w, hw, -⟩ := Scheme.exists_preimage_of_isPullback (hsq j) y v hv.symm
  obtain ⟨n, hn, τ, U, hU, hwU, -⟩ := (hA j).exists_affine_nonvanishingLocus (x := w)
  have hqc : (tensorPowModule Y M (n : ℤ)).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_tensorPowModule M (n : ℤ)
  have hwτ : w ∈ nonvanishingLocus
      (tensorPowModule (Y' j) (pullbackModule (pr j) M) (n : ℤ)) τ := hU ▸ hwU
  have hwσ : w ∈ nonvanishingLocus
      ((Scheme.Modules.pullback (pr j)).obj (tensorPowModule Y M (n : ℤ)))
      ((e j n).symm.hom.app ⊤ τ) := by
    rw [Stacks.Ample.nonvanishingLocus_congr
      (e j n).symm τ]
    exact hwτ
  obtain ⟨a, ha⟩ := exists_mem_nonvanishingLocus_of_isPullback (hsq j)
    (tensorPowModule Y M (n : ℤ)) _ hwσ
  rw [hw] at ha
  refine ⟨n, hn, a, ha, ?_⟩
  -- the nonvanishing open is quasi-affine, by descent along the covering
  set A : Y.Opens := Stacks.NonvanishingOpen.nonvanishingOpen Y (tensorPowModule Y M (n : ℤ)) a
    with hAdef
  have hsq' : ∀ i, IsPullback ((pr i) ∣_ A) (((pr i) ⁻¹ᵁ A).ι ≫ q' i) (A.ι ≫ qY) (t i) :=
    fun i => (isPullback_morphismRestrict (pr i) A).paste_vert (hsq i)
  have hqa : ∀ i, ((pr i) ⁻¹ᵁ A).toScheme.IsQuasiAffine := by
    intro i
    have hcong := Stacks.Ample.nonvanishingLocus_congr
      (e i n)
      (Stacks.NonvanishingPullback.pullbackGlobalSection (pr i)
        (tensorPowModule Y M (n : ℤ)) a)
    have hpre := Stacks.NonvanishingPullback.preimage_nonvanishingLocus (pr i)
      (tensorPowModule Y M (n : ℤ)) a
    have heq : (pr i) ⁻¹ᵁ A = Stacks.NonvanishingOpen.nonvanishingOpen (Y' i)
        (tensorPowModule (Y' i) (pullbackModule (pr i) M) (n : ℤ))
        ((e i n).hom.app ⊤
          (Stacks.NonvanishingPullback.pullbackGlobalSection (pr i)
            (tensorPowModule Y M (n : ℤ)) a)) :=
      TopologicalSpace.Opens.ext (by
        rw [Stacks.NonvanishingOpen.coe_nonvanishingOpen, hcong]
        exact hpre)
    rw [heq]
    exact Stacks.AmpleQuasiAffineCover.isQuasiAffine_nonvanishingOpen_of_isAmple
      (pullbackModule (pr i) M) (hA i) hn _
  have hqah : IsQuasiAffineHom (A.ι ≫ qY) :=
    (forall_iff_of_fpqcCover (P := @IsQuasiAffineHom) hfpqc hsq').mpr fun i =>
      (isQuasiAffineHom_iff_isQuasiAffine _).mpr (hqa i)
  exact AlgebraicGeometry.Scheme.IsQuasiAffine.of_isQuasiAffineHom (A.ι ≫ qY)

end AffineCore

/-! ### Tag 0D2P in full -/

section Full

/-- **Stacks Tag 0D2P, clause (2) implies clause (1).** Let `f : X ⟶ S` be a morphism of schemes,
`L` an invertible `𝒪_X`-module and `{g i : S' i ⟶ S}` an fpqc covering of `S`, with each square
with sides `p i`, `f' i`, `f`, `g i` cartesian. If `(p i)^* L` is ample relative to `f' i` for
every `i`, then `L` is ample relative to `f`.

Quasi-compactness and separatedness of `f` come first, by
`Stacks.Descent.quasiCompact_of_forall_isRelativelyAmple_of_fpqcCover` and
`Stacks.Descent.isSeparated_of_forall_isRelativelyAmple_of_fpqcCover`. By [Stacks, Tag 01VJ],
clause (3) implies clause (1)
(`Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple`), it is then enough
to find, around every point of `S`, one affine open `V` over which `L` restricts to an ample
module. The definition of an fpqc covering supplies exactly that: an affine open `V` around the
point together with finitely many affine opens `W j` of members of the covering whose images
cover `V` (`Stacks.Cohomology.PseudoCoherence.FpqcDescent.exists_affineOpen_affine_images_cover`).
Restricting the cartesian squares to those opens
(`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isPullback_restrictBasesSquare`) puts the
hypotheses of `Stacks.Descent.isAmple_of_forall_isAmple_pullbackModule_of_affineFlatCover` in
place, and that theorem concludes. -/
@[ega "II 4.6.4" "Sufficiency",
  ega "II 8.10.6" "more general",
  ega "III 2.6.2.1" "more general",
  sga "1 VIII 7.8" "more general"]
theorem isRelativelyAmple_of_forall_of_fpqcCover {S : Scheme.{u}} {I : Type v}
    {S' : I → Scheme.{u}} {g : ∀ i, S' i ⟶ S}
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S) {X : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] {X' : I → Scheme.{u}} {p : ∀ i, X' i ⟶ X}
    {f' : ∀ i, X' i ⟶ S' i} (hsq : ∀ i, IsPullback (p i) (f' i) f (g i))
    (h : ∀ i, Stacks.RelativeAmple.IsRelativelyAmple (f' i) (pullbackModule (p i) L)) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  have hflat : ∀ i, Flat (g i) := fun i =>
    Stacks.Cohomology.PseudoCoherence.FpqcDescent.flat_of_mem_fpqcPrecoverage S' g hg i
  have hqcf : QuasiCompact f := quasiCompact_of_forall_isRelativelyAmple_of_fpqcCover hg L hsq h
  have hsepf : IsSeparated f := isSeparated_of_forall_isRelativelyAmple_of_fpqcCover hg L hsq h
  have hqsf : QuasiSeparated f := inferInstance
  refine Stacks.RelativeAmpleLocalOnBase.isRelativelyAmple_of_forall_exists_isAmple f L hqcf
    fun x => ?_
  obtain ⟨V, hVaff, hxV, m, aidx, W, hWaff, hWcov⟩ :=
    Stacks.Cohomology.PseudoCoherence.FpqcDescent.exists_affineOpen_affine_images_cover S' g hg x
  refine ⟨V, hVaff, hxV, ?_⟩
  have : IsAffine V.toScheme := hVaff
  have hWa : ∀ j, IsAffine ((W j).toScheme) := fun j => hWaff j
  have hle : ∀ j, W j ≤ (g (aidx j)) ⁻¹ᵁ V := fun j z hz => by
    have hmem : (g (aidx j)).base z ∈ (V : Set S) := by
      rw [← hWcov]
      exact Set.mem_iUnion.mpr ⟨j, ⟨z, hz, rfl⟩⟩
    exact hmem
  have hsq2 := fun j =>
    Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isPullback_restrictBasesSquare
      (hsq (aidx j)) V (hle j)
  have : CompactSpace (f ⁻¹ᵁ V).toScheme :=
    (quasiCompact_iff_compactSpace (f ∣_ V)).mp inferInstance
  have : QuasiSeparatedSpace (f ⁻¹ᵁ V).toScheme :=
    (quasiSeparated_iff_quasiSeparatedSpace (f ∣_ V)).mp inferInstance
  refine isAmple_of_forall_isAmple_pullbackModule_of_affineFlatCover (f ∣_ V)
    (pullbackModule (f ⁻¹ᵁ V).ι L) (T := fun j => (W j).toScheme)
    (t := fun j => (g (aidx j)).resLE V (W j) (hle j)) ?_ hsq2 ?_
  · -- the restricted family is jointly surjective
    intro v
    have hmem : V.ι.base v ∈ (V : Set S) := v.2
    rw [← hWcov] at hmem
    obtain ⟨j, z, hz, hzv⟩ := Set.mem_iUnion.mp hmem
    refine ⟨j, ⟨⟨z, hz⟩, ?_⟩⟩
    refine V.ι.isOpenEmbedding.injective ?_
    have hcomp : ((g (aidx j)).resLE V (W j) (hle j) ≫ V.ι).base ⟨z, hz⟩
        = ((W j).ι ≫ g (aidx j)).base ⟨z, hz⟩ := by
      rw [Scheme.Hom.resLE_comp_ι]
    exact hcomp.trans hzv
  · -- ampleness upstairs, transported across the identification of the two restrictions
    intro j
    refine (Stacks.RelativeVeryAmple.isAmple_congr _ _ ?_).mpr ((h (aidx j)).2 (W j) (hWaff j))
    exact (Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso
        ((p (aidx j)).resLE (f ⁻¹ᵁ V) (f' (aidx j) ⁻¹ᵁ (W j)) _) (f ⁻¹ᵁ V).ι L).symm
      ≪≫ Stacks.RelativeAmpleBaseChange.pullbackModuleCongr
          (Scheme.Hom.resLE_comp_ι (p (aidx j)) _) L
      ≪≫ Stacks.RelativeAmpleBaseChange.pullbackModuleCompIso (f' (aidx j) ⁻¹ᵁ (W j)).ι
          (p (aidx j)) L

/-- **Stacks Tag 0D2P.** Let `f : X ⟶ S` be a morphism of schemes, `L` an invertible
`𝒪_X`-module and `{g i : S' i ⟶ S}_{i ∈ I}` an fpqc covering of `S`. Let `f' i : X' i ⟶ S' i` be
the base change of `f` along `g i`, presented by a cartesian square with other projection
`p i : X' i ⟶ X`, and let `(p i)^* L` be the pullback of `L`. The following are equivalent:

1. `L` is ample on `X / S`;
2. `(p i)^* L` is ample on `X' i / S' i` for every `i ∈ I`.

Clause (1) implies clause (2) by [Stacks, Tag 0893] applied to each square,
`Stacks.Descent.isRelativelyAmple_pullbackModule_of_fpqcCover`. Clause (2) implies clause (1) is
`Stacks.Descent.isRelativelyAmple_of_forall_of_fpqcCover`. -/
@[stacks 0D2P, sga "1 VIII 7.8" "more general"]
theorem isRelativelyAmple_iff_forall_of_fpqcCover {S : Scheme.{u}} {I : Type v}
    {S' : I → Scheme.{u}} {g : ∀ i, S' i ⟶ S}
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S) {X : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] {X' : I → Scheme.{u}} {p : ∀ i, X' i ⟶ X}
    {f' : ∀ i, X' i ⟶ S' i} (hsq : ∀ i, IsPullback (p i) (f' i) f (g i)) :
    Stacks.RelativeAmple.IsRelativelyAmple f L ↔
      ∀ i, Stacks.RelativeAmple.IsRelativelyAmple (f' i) (pullbackModule (p i) L) :=
  ⟨isRelativelyAmple_pullbackModule_of_fpqcCover g hg f L hsq,
    isRelativelyAmple_of_forall_of_fpqcCover hg f L hsq⟩

end Full

end Stacks.Descent

end
