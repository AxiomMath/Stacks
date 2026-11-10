module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleWire.Basic
public import StacksFrontier.AlgebraicGeometry.HProjective.AffineBase
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.Basic
public import StacksFrontier.AlgebraicGeometry.ProperRelativeAmpleProjective.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.Basic
public import StacksFrontier.AlgebraicGeometry.ImmersionTwistGapUniform
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.BundleImmersion
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.SectionTransport
public import StacksFrontier.AlgebraicGeometry.QuasiProjectiveCompactification.UniformFamily
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.DirectImageAlgebra
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.GradedDirectImage

/-!
# Stacks Tag 07RM: a quasi-projective morphism is an open subscheme of a projective one

[Stacks, Tag 07RM] says that a quasi-projective morphism `f : X ⟶ S` with `S` quasi-compact and
quasi-separated factors as `X ⟶ X' ⟶ S` with `X ⟶ X'` an open immersion and `X' ⟶ S`
*projective*. "Projective" is clause (1) of Definition 01W8, `AlgebraicGeometry.IsProjective`: a
closed immersion over `S` into the projective bundle `𝐏(ℰ) = Proj_S(Sym(ℰ))` of a quasi-coherent
`𝒪_S`-module `ℰ` of finite type. This file proves the tag at exactly those hypotheses,
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`.

## The source's proof, and where each step is

Let `L` be ample relative to `f`.

1. *Over a finite affine covering `V_j` of `S`, one power `L^{⊗ d}` has generating sections over
   each `f⁻¹(V_j)` defining an immersion `f⁻¹(V_j) ⟶ ℙ^{n_j}_{V_j}`* ([Stacks, Tag 01VU] and
   [Stacks, Tag 02NP] in the source). This is
   `Stacks.QuasiProjectiveCompactification.exists_finite_affine_cover_familyImmersionTwist`,
   which keeps the sections.
2. *The finitely many sections, sections of `f_*L^{⊗ d}` over the `V_j`, come from one
   quasi-coherent `ℰ` of finite type mapping to `f_*L^{⊗ d}`* ([Stacks, Tag 01PK] in the source):
   `Stacks.QuasiProjectiveCompactification.exists_isFiniteType_hom_lift`, from the colimit half of
   [Stacks, Tag 01PG].
3. *The surjection `f^*ℰ ⟶ L^{⊗ d}` gives `r : X ⟶ 𝐏(ℰ)` over `S`*: the morphism of
   [Stacks, Tag 01O9] for the graded map `Sym(ℰ) ⟶ f_*(⨁_n L^{⊗ dn})` extending `ℰ ⟶ f_*L^{⊗ d}`
   (`Stacks.QuasiProjectiveCompactification.symLift` composed with
   `Stacks.RelativeAmple.directImagePowerMap`).
4. *`r` is an immersion*, because over `V_j` it factors the immersion of step 1 through the
   rational map `𝐏(ℰ)|_{V_j} ⇢ ℙ^{n_j}_{V_j}` ([Stacks, Tag 07RK]): on each chart `D₊(e)` of
   `𝐏(ℰ)` that rational map is the morphism of the coordinate ratios, which is
   `Stacks.QuasiProjectiveCompactification.isImmersion_toSpecAway`, and the charts are assembled
   by `Stacks.QuasiProjectiveCompactification.isImmersion_globalMorphism_of_chartsAreImmersions`.
   Steps 2 to 4 are
   `Stacks.QuasiProjectiveCompactification.exists_isImmersion_projectiveBundle_of_cover`.
5. *`r` is quasi-compact, so it factors as an open immersion onto a closed subscheme `X'` of
   `𝐏(ℰ)`* ([Stacks, Tag 03GI] and [Stacks, Tag 01RG]), and `X' ⟶ S` is projective by definition:
   `Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective` of
   `StacksFrontier/AlgebraicGeometry/QuasiProjectiveCompactification/Basic.lean`, whose immersion
   input `Stacks.QuasiProjectiveCompactification.ImmersionIntoProjective` is discharged here at
   `AlgebraicGeometry.IsProjective` as
   `Stacks.QuasiProjectiveCompactification.immersionIntoProjective_isProjective`.

## Main results

* `Stacks.QuasiProjectiveCompactification.isProjective_comp_of_isClosedImmersion`: a closed
  immersion into a projective `S`-scheme is projective over `S`.
* `exists_isOpenImmersion_isProjective_of_isHQuasiProjective` (in the namespace
  `Stacks.QuasiProjectiveCompactification`): an H-quasi-projective morphism factors as an open
  immersion followed by a projective morphism, over an arbitrary base.
* `Stacks.QuasiProjectiveCompactification.exists_isImmersion_isProjective_of_qcqs` and
  `Stacks.QuasiProjectiveCompactification.immersionIntoProjective_isProjective`: half 1 of the
  source's proof.
* `Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`:
  **[Stacks, Tag 07RM]**.
* `Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_isAffine`: the
  affine case, as a corollary.

## Implementation notes

**The two quasi-projectivity predicates are bridged, not duplicated.**
`AlgebraicGeometry.IsQuasiProjective` (Tag 01VW) and `Stacks.HProjective.IsQuasiProjective` differ
only in the spelling of relative ampleness, which
`Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple` identifies;
`Stacks.QuasiProjectiveCompactification.isQuasiProjective_hProjective` is that bridge. The
statements below are phrased with `AlgebraicGeometry.IsQuasiProjective`.

**The power `d` is absorbed into the module.** The graded map of step 3 is written for the
invertible module `L^{⊗ d}` itself, so its degree-one values are sections of `L^{⊗ d}`; the
identification of `(L^{⊗ d})|_{f⁻¹(V_j)}` with `(L|_{f⁻¹(V_j)})^{⊗ d}`, in which the sections of
step 1 live, is `Stacks.QuasiProjectiveCompactification.nonempty_natTensorPow_pullback_iso`.

## References

* [Stacks Project, Tag 07RM](https://stacks.math.columbia.edu/tag/07RM)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01W9](https://stacks.math.columbia.edu/tag/01W9)
* [Stacks Project, Tag 01RG](https://stacks.math.columbia.edu/tag/01RG)
* [Stacks Project, Tag 01VU](https://stacks.math.columbia.edu/tag/01VU)
* [Stacks Project, Tag 01PK](https://stacks.math.columbia.edu/tag/01PK)
* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 02NP](https://stacks.math.columbia.edu/tag/02NP)
* [Stacks Project, Tag 07RK](https://stacks.math.columbia.edu/tag/07RK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.SymGraded

universe u

namespace Stacks.QuasiProjectiveCompactification

/-! ### The two bridges between the two projectivity developments -/

/-- **H-projectivity of `Stacks.HProjective` is `AlgebraicGeometry.IsProjectiveMorphism`.**
The two definitions have the same body: a closed immersion into `ℙⁿ_S` over `S`. -/
theorem isProjectiveMorphism_of_isHProjective {X S : Scheme.{u}} {g : X ⟶ S}
    (hg : Stacks.HProjective.IsHProjective g) : IsProjectiveMorphism g := hg

/-- **The two spellings of quasi-projectivity agree.** `AlgebraicGeometry.IsQuasiProjective` and
`Stacks.HProjective.IsQuasiProjective` are both "locally of finite type and quasi-compact,
together with a relatively ample invertible module"; the two relative ampleness predicates of
[Stacks, Tag 01VH] are identified by
`Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple`. -/
theorem isQuasiProjective_hProjective {X S : Scheme.{u}} {f : X ⟶ S}
    (hf : AlgebraicGeometry.IsQuasiProjective f) : Stacks.HProjective.IsQuasiProjective f := by
  obtain ⟨hft, L, hL, hample⟩ := hf
  have hL' : Stacks.Ample.IsInvertibleModule X L := hL
  exact ⟨hft, L, hL', (Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple f L).mpr hample⟩

/-! ### "Projective by definition": a closed immersion into a projective `S`-scheme -/

/-- **A closed immersion into a projective `S`-scheme is projective over `S`.** This is the last
sentence of the proof of [Stacks, Tag 07RM], at clause (1) of Definition 01W8: compose the given
closed immersion with the closed immersion of the target into the projective bundle. -/
@[ega "II 5.5.5" "(ii)"]
theorem isProjective_comp_of_isClosedImmersion {X' Y S : Scheme.{u}} (c : X' ⟶ Y) (q : Y ⟶ S)
    (hc : IsClosedImmersion c) (hq : IsProjective q) : IsProjective (c ≫ q) := by
  obtain ⟨E, hE, hEft, hqc, i, hi, hiq⟩ := hq
  have := hc
  have := hi
  refine ⟨E, hE, hEft, hqc, c ≫ i, inferInstance, ?_⟩
  rw [Category.assoc, hiq]

/-! ### Half 2 of Tag 07RM at clause (1), with no hypothesis on the base -/

/-- **An H-quasi-projective morphism factors as an open immersion followed by a projective
morphism.** This is half 2 of the proof of [Stacks, Tag 07RM] read at clause (1) of
Definition 01W8, and it needs no hypothesis on the base.

The quasi-compact immersion `X ⟶ ℙⁿ_S` supplied by H-quasi-projectivity is factored by
[Stacks, Tag 01RG] as an open immersion onto a closed subscheme `X'` of `ℙⁿ_S`
(`AlgebraicGeometry.exists_isOpenImmersion_isProjectiveMorphism_of_isHQuasiProjective`, Tag
01WA); `X' ⟶ S` is then H-projective, hence projective by clause (2) of [Stacks, Tag 01W9]. -/
theorem exists_isOpenImmersion_isProjective_of_isHQuasiProjective {X S : Scheme.{u}}
    {f : X ⟶ S} (hf : AlgebraicGeometry.IsHQuasiProjective f) :
    ∃ (X' : Scheme.{u}) (j : X ⟶ X') (p : X' ⟶ S),
      IsOpenImmersion j ∧ IsProjective p ∧ j ≫ p = f := by
  obtain ⟨X', j, p, hj, hp, hjp⟩ :=
    exists_isOpenImmersion_isProjectiveMorphism_of_isHQuasiProjective hf
  exact ⟨X', j, p, hj, hp.isProjective, hjp⟩

/-- **A projective morphism is separated**, in the shape the parametric Tag 07RM of
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective` asks for. This is
the use the source makes of [Stacks, Tag 03GI]. -/
theorem isSeparated_of_isProjective {Y S : Scheme.{u}} (q : Y ⟶ S) (hq : IsProjective q) :
    IsSeparated q := hq.isSeparated

/-! ### Half 1: an immersion into the projective bundle of a finite-type module -/

/-- **Half 1 of the proof of [Stacks, Tag 07RM].** A quasi-projective morphism `f : X ⟶ S` with
`S` quasi-compact and quasi-separated admits an immersion over `S` into a projective `S`-scheme,
namely into the projective bundle `𝐏(ℰ)` of a quasi-coherent `𝒪_S`-module `ℰ` of finite type.

See the module documentation for the steps;
`Stacks.QuasiProjectiveCompactification.exists_isImmersion_projectiveBundle_of_cover` does the
work, for the graded map `f_*(⨁_n L^{⊗ dn})` of the power `L^{⊗ d}` of step 1. -/
@[ega "II 5.3.2" "(a) ⇒ (b)"]
theorem exists_isImmersion_isProjective_of_qcqs {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] (hf : Stacks.HProjective.IsQuasiProjective f) :
    ∃ (Y : Scheme.{u}) (g : X ⟶ Y) (q : Y ⟶ S), IsImmersion g ∧ IsProjective q ∧ g ≫ q = f := by
  obtain ⟨⟨hft, hqc⟩, L, hL, hample⟩ := hf
  have := hL
  have := hft
  have := hqc
  have := Stacks.RelativeAmple.IsRelativelyAmple.quasiSeparated hample
  obtain ⟨ι, hι, V, hV, hcov, d, -, hfam⟩ :=
    exists_finite_affine_cover_familyImmersionTwist f L hample
  have := hι
  choose n t ht himm using hfam
  let L' := Stacks.Ample.tensorPowModule X L d
  let P := Stacks.RelativeAmple.directImagePowerMap f L'
  let Φ := fun j => (nonempty_natTensorPow_pullback_iso L (f ⁻¹ᵁ V j) d).some
  have hsurj : ∀ j (y : Γ(Stacks.Ample.tensorPowModule (f ⁻¹ᵁ V j).toScheme
      ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V j).ι.toLRSHom.toShHom).obj L) d, ⊤)),
      ∃ σ : Γ((Stacks.RelativeAmple.directImageAlgebra f L').piece 1, V j),
        (Φ j).hom.app ⊤ (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection
          P.L (f ⁻¹ᵁ V j) 1 (P.value 1 (V j) σ)) = y := by
    intro j y
    obtain ⟨x, hx⟩ := restrictPowSection_surjective L' (f ⁻¹ᵁ V j) 1 ((Φ j).inv.app ⊤ y)
    refine ⟨(Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L' 1).hom.app (f ⁻¹ᵁ V j) x,
      ?_⟩
    have hinv : (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L' 1).inv.app
        (f ⁻¹ᵁ V j) ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L' 1).hom.app
          (f ⁻¹ᵁ V j) x) = x :=
      Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app
        (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L' 1).symm (f ⁻¹ᵁ V j) x
    change (Φ j).hom.app ⊤
      (Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.restrictPowSection
        L' (f ⁻¹ᵁ V j) 1 ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L' 1).inv.app
          (f ⁻¹ᵁ V j) ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare L' 1).hom.app
            (f ⁻¹ᵁ V j) x))) = y
    rw [hinv, hx]
    exact Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app (Φ j) ⊤ y
  have : ∀ j, Stacks.Ample.IsInvertibleModule (f ⁻¹ᵁ V j).toScheme
      (Stacks.Ample.tensorPowModule (f ⁻¹ᵁ V j).toScheme
        ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V j).ι.toLRSHom.toShHom).obj L) d) :=
    fun j => @Stacks.Ample.isInvertibleModule_tensorPowModule _ _
      (Stacks.InvertiblePullback.isInvertibleModule_restrict (f ⁻¹ᵁ V j) L) d
  obtain ⟨E, hEq, hEft, i, hi, hif⟩ := exists_isImmersion_projectiveBundle_of_cover P V hV hcov n
    (fun j => Stacks.Ample.tensorPowModule (f ⁻¹ᵁ V j).toScheme
      ((RingedSpaceModuleAdjunction.modulePullback (f ⁻¹ᵁ V j).ι.toLRSHom.toShHom).obj L) d)
    t ht himm Φ hsurj
  exact ⟨_, i, _, hi, isProjective_schemeProjectiveBundleToBase E, hif⟩

/-- **The immersion input of
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective` holds for
`AlgebraicGeometry.IsProjective`.** This is
`Stacks.QuasiProjectiveCompactification.exists_isImmersion_isProjective_of_qcqs`, in the shape of
that named condition. -/
theorem immersionIntoProjective_isProjective :
    ImmersionIntoProjective @AlgebraicGeometry.IsProjective.{u} :=
  fun _ _ f _ _ hf => exists_isImmersion_isProjective_of_qcqs f hf

/-! ### Tag 07RM -/

/-- **[Stacks, Tag 07RM].** Let `f : X ⟶ S` be a quasi-projective morphism with `S` quasi-compact
and quasi-separated. Then `f` factors as `X ⟶ X' ⟶ S` where `X ⟶ X'` is an open immersion and
`X' ⟶ S` is projective, in the sense of clause (1) of Definition 01W8.

Half 1 of the source's proof is
`Stacks.QuasiProjectiveCompactification.immersionIntoProjective_isProjective`; half 2, the
factorisation of a quasi-compact immersion through the closure of its image, is
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective`, whose two conditions
on the projectivity predicate are discharged by `AlgebraicGeometry.IsProjective.isSeparated` and
`Stacks.QuasiProjectiveCompactification.isProjective_comp_of_isClosedImmersion`. -/
@[stacks 07RM]
theorem exists_isOpenImmersion_isProjective_of_qcqs {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace S] [QuasiSeparatedSpace S] (hf : AlgebraicGeometry.IsQuasiProjective f) :
    ∃ (X' : Scheme.{u}) (j : X ⟶ X') (p : X' ⟶ S),
      IsOpenImmersion j ∧ IsProjective p ∧ j ≫ p = f :=
  exists_isOpenImmersion_isProjective (P := @AlgebraicGeometry.IsProjective.{u})
    isSeparated_of_isProjective
    (fun c q hc hq => isProjective_comp_of_isClosedImmersion c q hc hq)
    immersionIntoProjective_isProjective f (isQuasiProjective_hProjective hf)

/-- **[Stacks, Tag 07RM] over an affine base**, as a corollary of
`Stacks.QuasiProjectiveCompactification.exists_isOpenImmersion_isProjective_of_qcqs`: an affine
scheme is quasi-compact and quasi-separated. -/
@[ega "III 5.2.6" "more general", sga "4½ Th_finitude 2.6" "partial"]
theorem exists_isOpenImmersion_isProjective_of_isAffine {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) (hf : AlgebraicGeometry.IsQuasiProjective f) :
    ∃ (X' : Scheme.{u}) (j : X ⟶ X') (p : X' ⟶ S),
      IsOpenImmersion j ∧ IsProjective p ∧ j ≫ p = f :=
  exists_isOpenImmersion_isProjective_of_qcqs f hf

end Stacks.QuasiProjectiveCompactification

end
