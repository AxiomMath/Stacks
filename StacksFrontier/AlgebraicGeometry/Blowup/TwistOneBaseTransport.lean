module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesRestrictDegOne
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesSheafData
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistOneIdealSheaf
public import StacksFrontier.AlgebraicGeometry.RelativeProj.Twist.Multiplication

/-!
# The chartwise comparison of `𝒪(1)` along a chart transition of the blowup

Let `S` be a scheme, `ℐ` a quasi-coherent ideal sheaf on it and `h : U ≤ V` an inclusion of
affine opens of `S`. The chart of the blowup over `U` sits inside the chart over `V` through the
Tag 01NO transition `AlgebraicGeometry.Proj.map (Stacks.Blowup.reesRestrict ℐ h)`. This file
proves that the chartwise comparison of `𝒪(1)` with the exceptional ideal sheaf — the product
`Stacks.Blowup.chartCoeff · Stacks.Blowup.baseSectionRes` of
`StacksFrontier/AlgebraicGeometry/Blowup/TwistOneIdealSheaf.lean` — is natural for that transition.

This is what the comparison of `𝒪(1)` with the exceptional ideal sheaf needs in order to leave
the affine case: over a general base two charts come from two different affine opens of `S`, so
the two chartwise comparisons live on the `Proj` of two different Rees algebras, and they have to
be identified over the intersection before they can be glued.

## Main results

* `Stacks.Blowup.projMap_reesRestrict_toSpec`: the Tag 01NO transition lies over the restriction
  map of the base, i.e. it is a morphism of blowups over `Spec Γ(S, V) ← Spec Γ(S, U)`.
* `Stacks.Blowup.appTop_projMap_baseSection` and
  `Stacks.Blowup.app_projMap_baseSectionRes`: **the transport of `baseSection`.** Pulling the
  base section of `s` on the chart over `V` back along the transition gives the base section of
  the restriction of `s` to `U`, globally and over an open.
* `Stacks.Blowup.app_projMap_chartCoeff`: **the transport of `chartCoeff`**, i.e. the statement
  that the twist comparison `Stacks.ProjTwistComparison.sectionsMap` commutes with the
  trivialization `Stacks.AlgebraicGeometry.ProjTrivialization.trivializingEquiv`.
* `Stacks.Blowup.app_projMap_chartCoeff_mul_baseSectionRes`: **the two combined** — the chartwise
  comparison is natural for the chart transition.
* `Stacks.ProjTwistComparison.app_trivializingEquiv_symm`: **the transport of the trivializing
  coefficient at abstract gradings** — for any graded homomorphism carrying a degree-one element
  `f` to a degree-one element `g`, the coefficient read off against the trivializing section of
  `f` pulls back to the coefficient read off against that of `g`. This is the content of
  `Stacks.Blowup.app_chartCoeff_of_reesDegOne`, which is now its instance at the Rees grading.
* `Stacks.ProjTwistComparison.val_app_proj_map`,
  `Stacks.ProjTwistComparison.fibreMap_algebraMap` and
  `Stacks.ProjTwistComparison.fibreMap_trivializingFun`: the three pointwise facts about the
  fibre comparison that the transports are assembled from.

## Implementation notes

The statements about `Stacks.Blowup.toSpec` are phrased with
`CommRingCat.ofHom (Stacks.Blowup.sheafRestrict h).hom` rather than with `sheafRestrict h`
itself. `toSpec` of an ideal of `↥Γ(S, V)` has `Spec (CommRingCat.of ↥Γ(S, V))` as its target,
and that is not the spelling `Γ(S, V)` of the structure sheaf's value; naming the morphism
between the `CommRingCat.of` spellings keeps the composites in the statements type-correct
without a transport.

Every transport is proved at *abstract* rings first and then specialized by passing the sections
of the structure sheaf as arguments. Stated directly at `↥Γ(S, V)` each of the three proofs blows
the heartbeat limit in `isDefEq`: `↥Γ(X, W)` and
`↥((structureRingPresheaf X.presheaf).obj (op W))` are definitionally but not *reducibly* equal,
and the same holds for `(AlgebraicGeometry.Proj 𝒜).Opens` against
`Opens (ProjectiveSpectrum.top 𝒜)`. The consequence for
`Stacks.ProjTwistComparison.app_trivializingEquiv_symm` is sharper still: its goal mentions
`Stacks.AlgebraicGeometry.ProjTrivialization.trivializingFun` at an open of the *scheme*
spelling, so the goal is not type-correct at `implicit` transparency and `rw` cannot build a
motive for it at all. That proof is therefore a `calc` chain of `congrArg`s with every motive
written out.

`Stacks.Blowup.app_projMap_chartCoeff` is the lemma that was missing when the chartwise
comparison could not leave the affine case. It cannot be stated as an equation of linear maps:
`trivializingEquiv` is linear over `Γ(Proj (reesGrading ℐ(V)), W)` while `sectionsMap` is only
*semilinear*, over the structure-sheaf map of `AlgebraicGeometry.Proj.map`
(`Stacks.ProjTwistComparison.fibreMap_smul`), so no `RingHomCompTriple` relates the two scalar
rings and the composite equivalence does not typecheck. The route taken is pointwise: at each
fibre the comparison is `Localization.localRingHom`, which carries `mk (f ^ k) ⟨f ^ l, _⟩` to
`mk (φ f ^ k) ⟨φ f ^ l, _⟩`, and `Stacks.Blowup.reesRestrict_reesDegOne` identifies `φ a⁽¹⁾` with
the restricted degree-one element.

That pointwise argument uses nothing about the Rees algebra, so it is carried out once, for an
arbitrary graded homomorphism, in `Stacks.ProjTwistComparison.app_trivializingEquiv_symm`; the
blowup chart transition and the comparison of the two Rees gradings of a quasi-coherent ideal
sheaf are both instances of it.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial HomogeneousLocalization HomogeneousIdeal
open TopologicalSpace Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj (moduleSections twistGrading)
open Stacks.AlgebraicGeometry.ProjTrivialization (trivializingFun eq_of_val_mul_eq)

universe u

attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] ProjectiveSpectrum.isPrime

/-! ### The fibre comparison on the structure sheaf and on the trivializing value -/

namespace Stacks.ProjTwistComparison

section Fibre

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)

/-- **The pullback of a section of the structure sheaf along `AlgebraicGeometry.Proj.map`, read
pointwise.** At a point of the preimage its underlying fraction is the fibre comparison of the
underlying fraction of the value at the point below. -/
theorem val_app_proj_map (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (c : Γ(AlgebraicGeometry.Proj 𝒜, U))
    (y : AlgebraicGeometry.Proj.map φ hφ ⁻¹ᵁ U) :
    HomogeneousLocalization.val
        ((((AlgebraicGeometry.Proj.map φ hφ).app U).hom c).1 y) =
      fibreMap φ hφ y.1 (HomogeneousLocalization.val
        (c.1 ⟨ProjectiveSpectrum.comapFun φ hφ y.1, y.2⟩)) :=
  HomogeneousLocalization.val_localRingHom _

/-- **The fibre comparison carries a constant fraction to a constant fraction.** -/
theorem fibreMap_algebraMap (y : ProjectiveSpectrum ℬ) (m : A) :
    fibreMap φ hφ y
        (algebraMap A
          (Localization
            (ProjectiveSpectrum.comapFun φ hφ y).asHomogeneousIdeal.toIdeal.primeCompl) m) =
      algebraMap B (Localization y.asHomogeneousIdeal.toIdeal.primeCompl) (φ m) := by
  rw [← Localization.mk_one_eq_algebraMap, ← Localization.mk_one_eq_algebraMap]
  refine (fibreMap_mk φ hφ y m 1).trans ?_
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp))

/-- **The fibre comparison carries the trivializing value of `f` to that of its image.** The
trivializing value is the fraction `f ^ n / f ^ (-n)` and the fibre comparison applies `φ` to
numerator and denominator, so the image is the trivializing value of `φ f`. -/
theorem fibreMap_trivializingFun (n : ℤ) {f : A} {g : B} (hfg : φ f = g)
    {W : Opens (ProjectiveSpectrum.top 𝒜)} (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    {W' : Opens (ProjectiveSpectrum.top ℬ)} (hW' : W' ≤ ProjectiveSpectrum.basicOpen ℬ g)
    (y : W') (hy : ProjectiveSpectrum.comapFun φ hφ y.1 ∈ W) :
    fibreMap φ hφ y.1 (trivializingFun 𝒜 n hW ⟨_, hy⟩) = trivializingFun ℬ n hW' y := by
  have hden : f ^ (-n).toNat ∈
      (ProjectiveSpectrum.comapFun φ hφ y.1).asHomogeneousIdeal.toIdeal.primeCompl :=
    (ProjectiveSpectrum.comapFun φ hφ y.1).asHomogeneousIdeal.toIdeal.primeCompl.pow_mem
      (hW hy) _
  refine (fibreMap_mk φ hφ y.1 (f ^ n.toNat) ⟨f ^ (-n).toNat, hden⟩).trans ?_
  rw [trivializingFun]
  exact Localization.mk_eq_mk_iff.mpr (Localization.r_of_eq (by simp [hfg]))

/-- **The trivializing coefficient at a degree-one element commutes with the twist comparison.**
Pulling back along `AlgebraicGeometry.Proj.map φ` the section of the structure sheaf that
multiplies to `t` against the trivializing section of `f` gives the one that multiplies to the
twist comparison of `t` against the trivializing section of `φ f`.

It cannot be stated as an equation of linear maps:
`Stacks.AlgebraicGeometry.ProjTrivialization.trivializingEquiv` is linear over
`Γ(Proj 𝒜, W)` while `Stacks.ProjTwistComparison.sectionsMap` is only *semilinear*, over the
structure-sheaf map of `AlgebraicGeometry.Proj.map` (`fibreMap_smul`), so no
`RingHomCompTriple` relates the two scalar rings. The route taken is pointwise: the coefficient
is pinned down by its product with the trivializing value, and the fibre comparison carries that
product to the corresponding product because it carries the trivializing value of `f` to that of
`φ f`. -/
theorem app_trivializingEquiv_symm {f : A} (hf : f ∈ 𝒜 1) {g : B} (hg : g ∈ ℬ 1)
    (hfg : φ f = g) {W : (AlgebraicGeometry.Proj 𝒜).Opens}
    (hW : W ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (hW' : AlgebraicGeometry.Proj.map φ hφ ⁻¹ᵁ W ≤ ProjectiveSpectrum.basicOpen ℬ g)
    (t : moduleSections 𝒜 (twistGrading 𝒜 1) W) :
    ((AlgebraicGeometry.Proj.map φ hφ).app W).hom
        ((Stacks.AlgebraicGeometry.ProjTrivialization.trivializingEquiv 𝒜 hf 1 hW).symm t) =
      (Stacks.AlgebraicGeometry.ProjTrivialization.trivializingEquiv ℬ hg 1 hW').symm
        (sectionsMap φ hφ 1 W t) := by
  refine Subtype.ext (funext fun y => eq_of_val_mul_eq ℬ 1 hW' y ?_)
  have hy : ProjectiveSpectrum.comapFun φ hφ y.1 ∈ W := y.2
  calc HomogeneousLocalization.val
          ((((AlgebraicGeometry.Proj.map φ hφ).app W).hom
            ((Stacks.AlgebraicGeometry.ProjTrivialization.trivializingEquiv
              𝒜 hf 1 hW).symm t)).1 y) *
        trivializingFun ℬ 1 hW' y
      = fibreMap φ hφ y.1 (HomogeneousLocalization.val
              (((Stacks.AlgebraicGeometry.ProjTrivialization.trivializingEquiv
                𝒜 hf 1 hW).symm t).1 ⟨_, hy⟩)) *
          trivializingFun ℬ 1 hW' y :=
        congrArg (· * trivializingFun ℬ 1 hW' y)
          (val_app_proj_map φ hφ W _ y)
    _ = fibreMap φ hφ y.1 (HomogeneousLocalization.val
              (((Stacks.AlgebraicGeometry.ProjTrivialization.trivializingEquiv
                𝒜 hf 1 hW).symm t).1 ⟨_, hy⟩)) *
          fibreMap φ hφ y.1 (trivializingFun 𝒜 1 hW ⟨_, hy⟩) :=
        congrArg (fibreMap φ hφ y.1 (HomogeneousLocalization.val
              (((Stacks.AlgebraicGeometry.ProjTrivialization.trivializingEquiv
                𝒜 hf 1 hW).symm t).1 ⟨_, hy⟩)) * ·)
          (fibreMap_trivializingFun φ hφ 1 hfg hW hW' y hy).symm
    _ = fibreMap φ hφ y.1 (HomogeneousLocalization.val
              (((Stacks.AlgebraicGeometry.ProjTrivialization.trivializingEquiv
                𝒜 hf 1 hW).symm t).1 ⟨_, hy⟩) *
            trivializingFun 𝒜 1 hW ⟨_, hy⟩) :=
        (fibreMap_mul φ hφ y.1 _ _).symm
    _ = fibreMap φ hφ y.1 (t.1 ⟨_, hy⟩) :=
        congrArg (fibreMap φ hφ y.1)
          (Stacks.AlgebraicGeometry.ProjTrivialization.val_trivializingEquiv_symm_mul
            𝒜 hf 1 hW t ⟨_, hy⟩)
    _ = (sectionsMap φ hφ 1 W t).1 y := (sectionsMap_apply φ hφ 1 W t y).symm
    _ = HomogeneousLocalization.val
            (((Stacks.AlgebraicGeometry.ProjTrivialization.trivializingEquiv
              ℬ hg 1 hW').symm (sectionsMap φ hφ 1 W t)).1 y) *
          trivializingFun ℬ 1 hW' y :=
        (Stacks.AlgebraicGeometry.ProjTrivialization.val_trivializingEquiv_symm_mul
          ℬ hg 1 hW' _ y).symm

end Fibre

end Stacks.ProjTwistComparison

namespace Stacks.Blowup

attribute [local implicit_reducible] blowUpSpec

/-! ### The transport, at abstract rings -/

section Abstract

variable {A B : Type u} [CommRing A] [CommRing B] {J : Ideal A} {K : Ideal B}

/-- **The pullback of a base section along a morphism of affine blowups over the base.** If a
morphism of the two blowups induced by a graded homomorphism of Rees algebras lies over `Spec` of
a ring map `ψ`, then it carries the pullback of `a` to the pullback of `ψ a`.

The two rings are type variables rather than values of a structure sheaf: stated at
`↥Γ(S, V)` the `Scheme.ΓSpecIso` naturality square is not *reducibly* the one `rw` needs, and the
proof hits the heartbeat limit. The specialization below passes them as arguments instead. -/
theorem appTop_baseSection_of_toSpec_comm (φ : reesGrading J →+*ᵍ reesGrading K)
    (hφ : irrelevant (reesGrading K) ≤ (irrelevant (reesGrading J)).map φ) (ψ : A →+* B)
    (hcomm : Proj.map φ hφ ≫ toSpec J = toSpec K ≫ Spec.map (CommRingCat.ofHom ψ)) (a : A) :
    (Proj.map φ hφ).appTop (baseSection J a) = baseSection K (ψ a) := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      ((toSpec J).appTop ≫ (Proj.map φ hφ).appTop) =
      (CommRingCat.ofHom ψ ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).inv) ≫ (toSpec K).appTop := by
    rw [← Scheme.Hom.comp_appTop, hcomm, Scheme.Hom.comp_appTop, ← Category.assoc,
      ← Scheme.ΓSpecIso_inv_naturality]
  have h2 := DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp key) a
  simpa only [baseSection, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom]
    using h2

/-- **The fibre comparison of a morphism of affine blowups carries a base section to a base
section.** The base section is the constant fraction of the degree-zero copy of `a`, so all that
is needed is that the graded homomorphism carry that copy to the copy of `ψ a`.

Stated at abstract rings for the same reason as
`Stacks.Blowup.appTop_baseSection_of_toSpec_comm`. -/
theorem fibreMap_baseSection_val_of_gradingZero (φ : reesGrading J →+*ᵍ reesGrading K)
    (hφ : irrelevant (reesGrading K) ≤ (irrelevant (reesGrading J)).map φ) (ψ : A → B)
    (hψ : ∀ a : A, φ ((reesGradingZeroEquiv J a : reesGrading J 0) : reesAlgebra J) =
      ((reesGradingZeroEquiv K (ψ a) : reesGrading K 0) : reesAlgebra K))
    (a : A) (y : ProjectiveSpectrum.top (reesGrading K)) :
    Stacks.ProjTwistComparison.fibreMap φ hφ y
        (HomogeneousLocalization.val ((baseSection J a).1
          ⟨ProjectiveSpectrum.comapFun φ hφ y, trivial⟩))
      = HomogeneousLocalization.val ((baseSection K (ψ a)).1 ⟨y, trivial⟩) := by
  rw [baseSection_val, baseSection_val, Stacks.ProjTwistComparison.fibreMap_algebraMap]
  exact congrArg
    (algebraMap (reesAlgebra K) (Localization y.asHomogeneousIdeal.toIdeal.primeCompl)) (hψ a)

/-- **The chartwise comparison is natural for a morphism of affine blowups, at abstract rings.**
Pulling the chart coefficient at `b` back along a morphism of affine blowups carrying `b⁽¹⁾` to
`c⁽¹⁾` gives the chart coefficient at `c` of the twist comparison.

This is `Stacks.ProjTwistComparison.app_trivializingEquiv_symm` at the Rees grading, where the
degree-one elements are `Stacks.Blowup.reesDegOne`; `Stacks.Blowup.chartCoeff` is by definition
the trivializing coefficient there. -/
theorem app_chartCoeff_of_reesDegOne (φ : reesGrading J →+*ᵍ reesGrading K)
    (hφ : irrelevant (reesGrading K) ≤ (irrelevant (reesGrading J)).map φ)
    {b : A} (hb : b ∈ J) {c : B} (hc : c ∈ K)
    (hbc : φ (reesDegOne J hb) = reesDegOne K hc) {W : (blowUpSpec J).Opens}
    (hW : W ≤ ProjectiveSpectrum.basicOpen (reesGrading J) (reesDegOne J hb))
    (hW' : Proj.map φ hφ ⁻¹ᵁ W ≤
      ProjectiveSpectrum.basicOpen (reesGrading K) (reesDegOne K hc))
    (t : moduleSections (reesGrading J) (twistGrading (reesGrading J) 1) W) :
    ((Proj.map φ hφ).app W).hom (chartCoeff J hb hW t) =
      chartCoeff K hc hW' (Stacks.ProjTwistComparison.sectionsMap φ hφ 1 W t) :=
  Stacks.ProjTwistComparison.app_trivializingEquiv_symm φ hφ
    (reesDegOne_mem_reesGrading J hb) (reesDegOne_mem_reesGrading K hc) hbc hW hW' t

end Abstract

/-! ### The transport along the Tag 01NO chart transition -/

variable {S : Scheme.{u}} (ℐ : S.IdealSheafData)

/-- **The Tag 01NO chart transition of the blowup lies over the base.** For an inclusion
`h : U ≤ V` of affine opens, the transition `Proj (Γ(S, U)[ℐ(U)t]) ⟶ Proj (Γ(S, V)[ℐ(V)t])` and
the two structure morphisms to the spectra of `Γ(S, U)` and `Γ(S, V)` commute with the
restriction map of the structure sheaf. -/
theorem projMap_reesRestrict_toSpec {U V : S.affineOpens} (h : U ≤ V) :
    Proj.map (reesRestrict ℐ h) (reesIrrelevant_le ℐ h) ≫ toSpec (ℐ.ideal V) =
      toSpec (ℐ.ideal U) ≫ Spec.map (CommRingCat.ofHom (sheafRestrict h).hom) := by
  have hzero : CommRingCat.ofHom (reesGradingZeroEquiv (ℐ.ideal V)).toRingHom ≫
      CommRingCat.ofHom (reesRestrict ℐ h).gradedZeroRingHom =
      CommRingCat.ofHom (sheafRestrict h).hom ≫
        CommRingCat.ofHom (reesGradingZeroEquiv (ℐ.ideal U)).toRingHom :=
    (reesBase_restrict ℐ h).symm
  rw [toSpec, toSpec, ← Category.assoc, Proj.map_toSpecZero, Category.assoc, Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp, hzero]

/-- **The transport of the base section along the Tag 01NO chart transition.** Pulling the
pullback of `s ∈ Γ(S, V)` on the chart over `V` back along the transition gives the pullback of
the restriction of `s` to `U` on the chart over `U`. -/
theorem appTop_projMap_baseSection {U V : S.affineOpens} (h : U ≤ V) (s : Γ(S, V.1)) :
    (Proj.map (reesRestrict ℐ h) (reesIrrelevant_le ℐ h)).appTop
        (baseSection (ℐ.ideal V) s) =
      baseSection (ℐ.ideal U) ((sheafRestrict h).hom s) :=
  appTop_baseSection_of_toSpec_comm (reesRestrict ℐ h) (reesIrrelevant_le ℐ h)
    (sheafRestrict h).hom (projMap_reesRestrict_toSpec ℐ h) s

/-- **The transported base section, pointwise.** At a point of the chart over `U` the pullback of
the base section of `s` is the constant fraction of the restriction of `s` to `U`. -/
theorem appTop_projMap_baseSection_val {U V : S.affineOpens} (h : U ≤ V) (s : Γ(S, V.1))
    (x : ProjectiveSpectrum.top (reesGrading (ℐ.ideal U))) :
    HomogeneousLocalization.val
        (((Proj.map (reesRestrict ℐ h) (reesIrrelevant_le ℐ h)).appTop
          (baseSection (ℐ.ideal V) s)).1 ⟨x, trivial⟩) =
      algebraMap (reesAlgebra (ℐ.ideal U))
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)
        ((reesGradingZeroEquiv (ℐ.ideal U) ((sheafRestrict h).hom s) :
          reesGrading (ℐ.ideal U) 0) : reesAlgebra (ℐ.ideal U)) :=
  (congrArg (fun y : Γ(blowUpSpec (ℐ.ideal U), ⊤) ↦
      HomogeneousLocalization.val (y.1 ⟨x, trivial⟩))
    (appTop_projMap_baseSection ℐ h s)).trans
      (baseSection_val (ℐ.ideal U) ((sheafRestrict h).hom s) x)

/-- **The chart at `a` pulls back to the chart at the restriction of `a`.** The preimage under
the Tag 01NO transition of the standard open of the degree-one element of a section of `ℐ(V)` is
the standard open of the degree-one element of its restriction to `U`.

Stated in the `ProjectiveSpectrum.basicOpen` spelling, which is the one
`Stacks.Blowup.chartCoeff` takes its hypothesis in;
`Stacks.AlgebraicGeometry.ProjTrivialization.proj_basicOpen_eq` says it is the scheme-level
`AlgebraicGeometry.Proj.basicOpen`. -/
theorem projMap_preimage_basicOpen_reesDegOne {U V : S.affineOpens} (h : U ≤ V)
    (a : ℐ.ideal V) :
    Proj.map (reesRestrict ℐ h) (reesIrrelevant_le ℐ h) ⁻¹ᵁ
        ProjectiveSpectrum.basicOpen (reesGrading (ℐ.ideal V)) (reesDegOne (ℐ.ideal V) a.2) =
      ProjectiveSpectrum.basicOpen (reesGrading (ℐ.ideal U))
        (reesDegOne (ℐ.ideal U) (sheafRestrict_mem_ideal ℐ h a)) := by
  rw [← Stacks.AlgebraicGeometry.ProjTrivialization.proj_basicOpen_eq,
    ← Stacks.AlgebraicGeometry.ProjTrivialization.proj_basicOpen_eq,
    Proj.map_preimage_basicOpen, reesRestrict_reesDegOne]

/-- **An open of the chart at `a` pulls back into the chart at the restriction of `a`**, the
form `Stacks.Blowup.chartCoeff` takes its hypothesis in over `U`. -/
theorem projMap_preimage_le_basicOpen_reesDegOne {U V : S.affineOpens} (h : U ≤ V)
    (a : ℐ.ideal V) {W : (blowUpSpec (ℐ.ideal V)).Opens}
    (hW : W ≤ ProjectiveSpectrum.basicOpen (reesGrading (ℐ.ideal V))
      (reesDegOne (ℐ.ideal V) a.2)) :
    Proj.map (reesRestrict ℐ h) (reesIrrelevant_le ℐ h) ⁻¹ᵁ W ≤
      ProjectiveSpectrum.basicOpen (reesGrading (ℐ.ideal U))
        (reesDegOne (ℐ.ideal U) (sheafRestrict_mem_ideal ℐ h a)) :=
  le_of_le_of_eq (fun _ hx => hW hx) (projMap_preimage_basicOpen_reesDegOne ℐ h a)

/-! ### The transport of the chartwise comparison -/

/-- The restriction homomorphism of Rees algebras carries the degree-zero copy of a section of
the base to the degree-zero copy of its restriction. -/
theorem reesRestrict_coe_reesGradingZeroEquiv {U V : S.affineOpens} (h : U ≤ V)
    (s : Γ(S, V.1)) :
    reesRestrict ℐ h
        ((reesGradingZeroEquiv (ℐ.ideal V) s : reesGrading (ℐ.ideal V) 0) :
          reesAlgebra (ℐ.ideal V)) =
      ((reesGradingZeroEquiv (ℐ.ideal U) ((sheafRestrict h).hom s) :
        reesGrading (ℐ.ideal U) 0) : reesAlgebra (ℐ.ideal U)) :=
  Subtype.ext (by
    rw [coe_reesRestrict, coe_coe_reesGradingZeroEquiv, coe_coe_reesGradingZeroEquiv,
      Polynomial.map_C])

/-- **The fibre comparison of the Tag 01NO chart transition carries the base section to the base
section.** This is the pointwise form of `Stacks.Blowup.appTop_projMap_baseSection`: the base
section is the constant fraction of a degree-zero element, and the fibre comparison of a
constant fraction is the constant fraction of the image. -/
theorem fibreMap_baseSection_val {U V : S.affineOpens} (h : U ≤ V) (s : Γ(S, V.1))
    (y : ProjectiveSpectrum.top (reesGrading (ℐ.ideal U))) :
    Stacks.ProjTwistComparison.fibreMap (reesRestrict ℐ h) (reesIrrelevant_le ℐ h) y
        (HomogeneousLocalization.val ((baseSection (ℐ.ideal V) s).1
          ⟨ProjectiveSpectrum.comapFun (reesRestrict ℐ h) (reesIrrelevant_le ℐ h) y, trivial⟩))
      = HomogeneousLocalization.val
          ((baseSection (ℐ.ideal U) ((sheafRestrict h).hom s)).1 ⟨y, trivial⟩) :=
  fibreMap_baseSection_val_of_gradingZero (reesRestrict ℐ h) (reesIrrelevant_le ℐ h)
    (sheafRestrict h).hom (reesRestrict_coe_reesGradingZeroEquiv ℐ h) s y

/-- **The transport of the restricted base section along the Tag 01NO chart transition.**
Pulling the base section of `s` on an open of the chart over `V` back along the transition gives
the base section of the restriction of `s` on the preimage. -/
theorem app_projMap_baseSectionRes {U V : S.affineOpens} (h : U ≤ V) (s : Γ(S, V.1))
    (W : (blowUpSpec (ℐ.ideal V)).Opens) :
    ((Proj.map (reesRestrict ℐ h) (reesIrrelevant_le ℐ h)).app W).hom
        (baseSectionRes (ℐ.ideal V) s W) =
      baseSectionRes (ℐ.ideal U) ((sheafRestrict h).hom s)
        (Proj.map (reesRestrict ℐ h) (reesIrrelevant_le ℐ h) ⁻¹ᵁ W) :=
  Subtype.ext (funext fun y => HomogeneousLocalization.val_injective _
    ((Stacks.ProjTwistComparison.val_app_proj_map (reesRestrict ℐ h) (reesIrrelevant_le ℐ h)
      W (baseSectionRes (ℐ.ideal V) s W) y).trans (fibreMap_baseSection_val ℐ h s y.1)))

/-- **The transport of the chartwise comparison along the Tag 01NO chart transition.** Pulling
the chart coefficient of `t` at `a` back along the transition gives the chart coefficient, at the
restriction of `a`, of the twist comparison of `t`.

This is `Stacks.Blowup.app_chartCoeff_of_reesDegOne` at the chart transition, where
`Stacks.Blowup.reesRestrict_reesDegOne` supplies the identification of degree-one elements. -/
theorem app_projMap_chartCoeff {U V : S.affineOpens} (h : U ≤ V) (a : ℐ.ideal V)
    {W : (blowUpSpec (ℐ.ideal V)).Opens}
    (hW : W ≤ ProjectiveSpectrum.basicOpen (reesGrading (ℐ.ideal V))
      (reesDegOne (ℐ.ideal V) a.2))
    (t : moduleSections (reesGrading (ℐ.ideal V))
      (twistGrading (reesGrading (ℐ.ideal V)) 1) W) :
    ((Proj.map (reesRestrict ℐ h) (reesIrrelevant_le ℐ h)).app W).hom
        (chartCoeff (ℐ.ideal V) a.2 hW t) =
      chartCoeff (ℐ.ideal U) (sheafRestrict_mem_ideal ℐ h a)
        (projMap_preimage_le_basicOpen_reesDegOne ℐ h a hW)
        (Stacks.ProjTwistComparison.sectionsMap (reesRestrict ℐ h)
          (reesIrrelevant_le ℐ h) 1 W t) :=
  app_chartCoeff_of_reesDegOne (reesRestrict ℐ h) (reesIrrelevant_le ℐ h) a.2
    (sheafRestrict_mem_ideal ℐ h a) (reesRestrict_reesDegOne ℐ h a) hW
    (projMap_preimage_le_basicOpen_reesDegOne ℐ h a hW) t

/-- **The chartwise comparison of `𝒪(1)` with the exceptional ideal sheaf is natural for the
Tag 01NO chart transition.** Pulling the product `chartCoeff · baseSectionRes` over `V` back
along the transition gives the same product over `U`, formed from the twist comparison of `t` and
the restriction of `a`. -/
theorem app_projMap_chartCoeff_mul_baseSectionRes {U V : S.affineOpens} (h : U ≤ V)
    (a : ℐ.ideal V) {W : (blowUpSpec (ℐ.ideal V)).Opens}
    (hW : W ≤ ProjectiveSpectrum.basicOpen (reesGrading (ℐ.ideal V))
      (reesDegOne (ℐ.ideal V) a.2))
    (t : moduleSections (reesGrading (ℐ.ideal V))
      (twistGrading (reesGrading (ℐ.ideal V)) 1) W) :
    ((Proj.map (reesRestrict ℐ h) (reesIrrelevant_le ℐ h)).app W).hom
        (chartCoeff (ℐ.ideal V) a.2 hW t * baseSectionRes (ℐ.ideal V) (a : Γ(S, V.1)) W) =
      chartCoeff (ℐ.ideal U) (sheafRestrict_mem_ideal ℐ h a)
          (projMap_preimage_le_basicOpen_reesDegOne ℐ h a hW)
          (Stacks.ProjTwistComparison.sectionsMap (reesRestrict ℐ h)
            (reesIrrelevant_le ℐ h) 1 W t) *
        baseSectionRes (ℐ.ideal U) ((sheafRestrict h).hom (a : Γ(S, V.1)))
          (Proj.map (reesRestrict ℐ h) (reesIrrelevant_le ℐ h) ⁻¹ᵁ W) :=
  (map_mul ((Proj.map (reesRestrict ℐ h) (reesIrrelevant_le ℐ h)).app W).hom _ _).trans
    (congrArg₂ (· * ·) (app_projMap_chartCoeff ℐ h a hW t)
      (app_projMap_baseSectionRes ℐ h (a : Γ(S, V.1)) W))

end Stacks.Blowup

end
