module

public import StacksFrontier.AlgebraicGeometry.RelativeProj.ModuleSheaf.Descent
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjTwistTransition

/-!
# The sheaf attached to a graded module on a relative projective spectrum

Let `s` be a relative `Proj` situation and let `ℳ` be a graded module over its graded algebra
whose homogeneous pieces are quasi-coherent. Its relative projective spectrum is glued from the
absolute projective spectra `Proj 𝒜(W)` of the graded section rings over the affine opens `W` of
the base, and each chart carries the sheaf `ℳ̃(W)` attached to the graded module of sections of
`ℳ` over `W`. This file glues those into the sheaf `ℳ̃` on the relative `Proj`.

For an inclusion `W ≤ W'` of affine opens of the base the comparison morphism of charts
`r : Proj 𝒜(W) ⟶ Proj 𝒜(W')` carries the canonical comparison `ℳ̃(W') ⟶ r_* ℳ̃(W)`. Pushing it
forward along the chart over `W'` and composing with the identification of iterated pushforwards
gives a morphism of sheaves of modules on the relative `Proj`. On sections over an open lying
inside the chart over `W` it is bijective, so it inverts to the required linear equivalence, and
it is functorial in the inclusion because the fibre comparison is. That is exactly a locally
directed glueing datum, and hence the sheaf `ℳ̃` itself.

The whole file is the twist construction of
`StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjTwistTransition` run for an
arbitrary graded module. Everything about the *charts* is shared with it verbatim — the
identification of the part of a chart lying over an open of the relative `Proj`, the image of a
point under the comparison of charts, the monotonicity of the chart ranges and the local
directedness of the cover by charts — and only the comparison of the sheaves is new.

## Main definitions

* `Stacks.RelativeProj.Situation.moduleChart`: the sheaf attached to `ℳ` on the chart over an
  affine open of the base.
* `Stacks.RelativeProj.Situation.modulePushforwardMap`: the comparison of the pushed-forward chart
  sheaves attached to an inclusion of affine opens of the base.
* `Stacks.RelativeProj.Situation.moduleTransEquiv`: that comparison inverted on sections over an
  open lying in the smaller chart.
* `Stacks.RelativeProj.Situation.modulesDirectedGlueData`: **the locally directed glueing datum of
  the chart sheaves.**
* `Stacks.RelativeProj.Situation.moduleSheaf`: **`ℳ̃` on the relative projective spectrum**, glued
  from the chart sheaves.
* `Stacks.RelativeProj.Situation.moduleSheafChartIso`: `ℳ̃` restricts on the chart over `W` to the
  sheaf attached to the graded module of sections of `ℳ` over `W`.

## Main results

* `Stacks.RelativeProj.Situation.bijective_modulePushforwardMap_app`: the comparison is bijective
  on sections over an open of the relative `Proj` lying in the chart over the smaller affine
  open.
* `Stacks.RelativeProj.Situation.modulePushforwardMap_comp_apply` and
  `Stacks.RelativeProj.Situation.modulePushforwardMap_naturality`: the comparisons are functorial
  in the inclusion and commute with restriction.

## Implementation notes

The comparison is assembled from `Stacks.ProjModuleComparison.pushforwardModuleMap`, the adjoint
transpose of `r^* ℳ̃(W') ⟶ ℳ̃(W)`, rather than from that morphism itself: an equation between it
for a composite of graded ring homomorphisms and the composite of the two cannot be stated without
transporting along `AlgebraicGeometry.Proj.map_comp`, whereas on sections the comparison of a
composite *is* the composite of the comparisons. The only transport that survives is a restriction
along the equality of opens `chart W ⁻¹ᵁ V = r ⁻¹ᵁ (chart W' ⁻¹ᵁ V)`, supplied by
`AlgebraicGeometry.Scheme.Modules.pushforwardCongr`, and it is an isomorphism on sections.

Functoriality is proved pointwise in the module fibres. The two points of `Proj 𝒜(W'')` at which
the two sides read a section — the one below a point of `Proj 𝒜(W)` for the restriction map of
`W ≤ W''`, and the one reached in two steps — agree only propositionally, so
`Stacks.ProjModuleComparison.fibreMap_comp_of_eq` takes both halves of the factorization as
hypotheses and substitutes the ring half away, after which the two points agree definitionally
and the membership proofs are identified by proof irrelevance.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01NR](https://stacks.math.columbia.edu/tag/01NR)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)

## Not done here

No Stacks tag is carried. The identification of `ℳ̃` on a chart with the sheaf of the graded
module of sections is proved here, as `Stacks.RelativeProj.Situation.moduleSheafChartIso`; the
quasi-coherence of `ℳ̃` is `Stacks.RelativeProj.Situation.isQuasicoherent_moduleSheaf`, and the
canonical map `π^*ℳ_0 ⟶ ℳ̃` of property (3) of Tag 01O7 is
`Stacks.RelativeProj.Situation.degreeZeroSheafMap`.
`ℳ̃` is not identified with any construction on the `RelativeProjQcohSheaf` substrate, which is a
different spelling of the structure sheaf.

The *input* of the two constructions is, however, identified. `ℳ̃` here is glued from the sheaves
attached to the graded modules of sections `sectionModule ℳ W`, and the `RelativeProjQcohSheaf`
substrate builds its own from the graded modules of sections of a
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedModule`;
`StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SituationModuleComparison` shows those are the
same graded module, by the identity, for one and the same sheaf of graded algebras — the module
analogue of the comparison of the section rings in
`StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SituationComparison`. What is still missing for
a comparison of the two *sheaves* is the comparison of the two glueing frameworks, which that
file's own "Not done here" records.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite HomogeneousIdeal
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.ProjModuleComparison Stacks.SheafOfModules Stacks.GradedLocalization
open scoped Stacks.GradedLocalization

universe u

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local instance] Stacks.RelativeProj.Situation.sectionModuleDecomposition

namespace Stacks.ProjModuleComparison

variable {A B C M N P : Type u} {σ τ ρ μ ν π : Type u}
  [CommRing A] [CommRing B] [CommRing C]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N] [AddCommGroup P] [Module C P]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike ρ C] [AddSubgroupClass ρ C]
  [SetLike μ M] [AddSubgroupClass μ M] [SetLike ν N] [AddSubgroupClass ν N]
  [SetLike π P] [AddSubgroupClass π P]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ρ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  {𝒨 : ℤ → μ} {𝒩 : ℤ → ν} {𝒬 : ℤ → π}
  [DirectSum.Decomposition 𝒨] [DirectSum.Decomposition 𝒩] [DirectSum.Decomposition 𝒬]

/-- **The module fibre comparison of a graded ring homomorphism that factors is the composite of
the fibre comparisons of its factors**, read on a dependent family of module fibres indexed by the
points of `Proj 𝒜` lying below the points of `Proj 𝒞`. -/
public theorem fibreMap_comp_of_eq (φ : 𝒜 →+*ᵍ ℬ) (hφ : ℬ₊ ≤ 𝒜₊.map φ)
    (f : M →ₛₗ[φ.toRingHom] N) (ψ : ℬ →+*ᵍ 𝒞) (hψ : 𝒞₊ ≤ ℬ₊.map ψ)
    (f' : N →ₛₗ[ψ.toRingHom] P) (χ : 𝒜 →+*ᵍ 𝒞) (hχ : 𝒞₊ ≤ 𝒜₊.map χ) (hc : χ = ψ.comp φ)
    (fχ : M →ₛₗ[χ.toRingHom] P) (hfc : ∀ m : M, fχ m = f' (f m))
    (x : ProjectiveSpectrum 𝒞) {Q : ProjectiveSpectrum 𝒜 → Prop}
    (a : ∀ q : Subtype Q, ModuleFiber (M := M) 𝒜 q.1)
    (h₁ : Q (ProjectiveSpectrum.comapFun χ hχ x))
    (h₂ : Q (ProjectiveSpectrum.comapFun φ hφ (ProjectiveSpectrum.comapFun ψ hψ x))) :
    fibreMap χ hχ fχ x (a ⟨_, h₁⟩)
      = fibreMap ψ hψ f' x
          (fibreMap φ hφ f (ProjectiveSpectrum.comapFun ψ hψ x) (a ⟨_, h₂⟩)) := by
  subst hc
  exact fibreMap_comp φ hφ f ψ hψ f' hχ fχ hfc x (a ⟨_, h₁⟩)

end Stacks.ProjModuleComparison

namespace Stacks.RelativeProj.Situation

variable {s : Situation.{u}} (ℳ : SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra)

/-- The sheaf attached to `ℳ` on the chart of a relative projective spectrum over an affine open
`W` of the base: the sheaf of Tag 01M6 of the graded module of local sections of `ℳ` over `W`,
over the graded ring of sections of the algebra over `W`. -/
public noncomputable abbrev moduleChart (W : s.base.affineOpens) :
    (AlgebraicGeometry.Proj (s.sectionRingGrading W.1)).Modules :=
  associatedModuleSheaf (s.sectionRingGrading W.1) (sectionModuleGrading ℳ W.1)

/-- Restriction of sections along an equality of opens is bijective. -/
private theorem bijective_presheaf_map_eqToHom {Y : Scheme.{u}} (Z : Y.Modules)
    {Q R : Y.Opens} (e : Q = R) :
    Function.Bijective (Z.presheaf.map (eqToHom e).op) := by
  subst e
  simpa using Function.bijective_id

variable [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent]

/-- **The comparison of the pushed-forward chart sheaves attached to an inclusion `W ≤ W'` of
affine opens of the base**: the adjoint transpose of the canonical comparison across the
comparison morphism of charts, pushed forward along the chart over `W'`. -/
public def modulePushforwardMap {W W' : s.base.affineOpens} (h : W ≤ W') :
    (Scheme.Modules.pushforward (relativeProjChart s W')).obj (moduleChart ℳ W') ⟶
      (Scheme.Modules.pushforward (relativeProjChart s W)).obj (moduleChart ℳ W) :=
  (Scheme.Modules.pushforward (relativeProjChart s W')).map
      (pushforwardModuleMap (gradedSectionRestriction s W.1 W'.1 h)
        (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
        (sectionModuleRestrictₛₗ ℳ h) (sectionModuleRestrictₛₗ_mem_grading ℳ h)) ≫
    (Scheme.Modules.pushforwardComp
        (projInclusionMap s W.1 W'.1 h W.2 W'.2) (relativeProjChart s W')).hom.app _ ≫
    (Scheme.Modules.pushforwardCongr (relativeProjChart_transition s h)).hom.app _

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- On sections over an open `V` of the relative projective spectrum, the comparison is the
comparison on sections over the part of the chart over `W'` lying over `V`, followed by the
restriction along the identification of opens of the chart over `W`. -/
public theorem modulePushforwardMap_apply {W W' : s.base.affineOpens} (h : W ≤ W')
    {V : (relativeProj s).Opens}
    (y : ToType (openSections (relativeProjChart s W') (moduleChart ℳ W') V)) :
    ((modulePushforwardMap ℳ h).val.app (op V)).hom y =
      (moduleChart ℳ W).presheaf.map (eqToHom (preimage_relativeProjChart_eq s h V)).op
        (sectionsMap (gradedSectionRestriction s W.1 W'.1 h)
          (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
          (sectionModuleRestrictₛₗ ℳ h) (sectionModuleRestrictₛₗ_mem_grading ℳ h)
          (relativeProjChart s W' ⁻¹ᵁ V) y) := rfl

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- The value of the comparison at a point of the chart over `W`: the module fibre comparison of
the restriction of the graded modules of sections, applied to the value of the section at the
point below. -/
public theorem modulePushforwardMap_val {W W' : s.base.affineOpens} (h : W ≤ W')
    {V : (relativeProj s).Opens}
    (y : ToType (openSections (relativeProjChart s W') (moduleChart ℳ W') V))
    (x : relativeProjChart s W ⁻¹ᵁ V) :
    (((modulePushforwardMap ℳ h).val.app (op V)).hom y).1 x
      = fibreMap (gradedSectionRestriction s W.1 W'.1 h)
          (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
          (sectionModuleRestrictₛₗ ℳ h) x.1
          (y.1 ⟨_, comapFun_gradedSectionRestriction_mem s h x⟩) := rfl

/-- **The comparison is bijective on sections over an open of the relative projective spectrum
lying in the chart over `W`**, because over such an open the comparison of the sheaves attached to
`ℳ` on the two charts is bijective on sections. -/
public theorem bijective_modulePushforwardMap_app {W W' : s.base.affineOpens} (h : W ≤ W')
    {V : (relativeProj s).Opens} (hV : V ≤ (relativeProjChart s W).opensRange) :
    Function.Bijective ((modulePushforwardMap ℳ h).val.app (op V)).hom := by
  have hfun : ⇑((modulePushforwardMap ℳ h).val.app (op V)).hom =
      (fun z => (moduleChart ℳ W).presheaf.map
          (eqToHom (preimage_relativeProjChart_eq s h V)).op z) ∘
        sectionsMap (gradedSectionRestriction s W.1 W'.1 h)
          (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
          (sectionModuleRestrictₛₗ ℳ h) (sectionModuleRestrictₛₗ_mem_grading ℳ h)
          (relativeProjChart s W' ⁻¹ᵁ V) :=
    funext (modulePushforwardMap_apply ℳ h)
  rw [hfun]
  refine Function.Bijective.comp (bijective_presheaf_map_eqToHom _ _) ?_
  refine bijective_sectionsMap_sectionModuleRestrict ℳ h W.2 W'.2 _ fun x => ?_
  obtain ⟨z, hz⟩ := hV x.2
  refine ⟨z, (relativeProjChart s W').isOpenEmbedding.injective ?_⟩
  change relativeProjChart s W' (projInclusionMap s W.1 W'.1 h W.2 W'.2 z) = _
  rwa [← Scheme.Hom.comp_apply, relativeProjChart_transition s h]

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- **The comparisons are functorial in the inclusion**: the comparison attached to `W ≤ W''` is
the comparison attached to `W' ≤ W''` followed by the one attached to `W ≤ W'`. -/
public theorem modulePushforwardMap_comp_apply {W W' W'' : s.base.affineOpens} (h : W ≤ W')
    (h' : W' ≤ W'') {V : (relativeProj s).Opens}
    (y : ToType (openSections (relativeProjChart s W'') (moduleChart ℳ W'') V)) :
    ((modulePushforwardMap ℳ (h.trans h')).val.app (op V)).hom y
      = ((modulePushforwardMap ℳ h).val.app (op V)).hom
          (((modulePushforwardMap ℳ h').val.app (op V)).hom y) := by
  refine Subtype.ext (funext fun x => ?_)
  exact fibreMap_comp_of_eq (gradedSectionRestriction s W'.1 W''.1 h')
    (irrelevant_le_map_gradedSectionRestriction s W'.1 W''.1 h' W'.2 W''.2)
    (sectionModuleRestrictₛₗ ℳ h')
    (gradedSectionRestriction s W.1 W'.1 h)
    (irrelevant_le_map_gradedSectionRestriction s W.1 W'.1 h W.2 W'.2)
    (sectionModuleRestrictₛₗ ℳ h)
    (gradedSectionRestriction s W.1 W''.1 (h.trans h'))
    (irrelevant_le_map_gradedSectionRestriction s W.1 W''.1 (h.trans h') W.2 W''.2)
    (gradedSectionRestriction_comp s W.1 W'.1 W''.1 h h')
    (sectionModuleRestrictₛₗ ℳ (h.trans h')) (sectionModuleRestrictₛₗ_trans ℳ h h') x.1 y.1
    (comapFun_gradedSectionRestriction_mem s (h.trans h') x)
    (comapFun_gradedSectionRestriction_mem s h' ⟨_, comapFun_gradedSectionRestriction_mem s h x⟩)

omit [∀ n : ℤ, (ℳ.piece n).IsQuasicoherent] in
/-- **The comparisons commute with the restriction maps** of the pushed-forward chart sheaves. -/
public theorem modulePushforwardMap_naturality {W W' : s.base.affineOpens} (h : W ≤ W')
    {V U : (relativeProj s).Opens} (hUV : U ≤ V)
    (y : ToType (openSections (relativeProjChart s W') (moduleChart ℳ W') V)) :
    ((modulePushforwardMap ℳ h).val.app (op U)).hom
        (((Scheme.Modules.pushforward (relativeProjChart s W')).obj
          (moduleChart ℳ W')).val.map (homOfLE hUV).op y)
      = ((Scheme.Modules.pushforward (relativeProjChart s W)).obj
          (moduleChart ℳ W)).val.map (homOfLE hUV).op
          (((modulePushforwardMap ℳ h).val.app (op V)).hom y) :=
  PresheafOfModules.naturality_apply (modulePushforwardMap ℳ h).val (homOfLE hUV).op y

/-- The comparison of the sections of the chart sheaves over `W` and over `W'` on an open `V` of
the relative projective spectrum lying in the chart over `W`, linear over the functions on `V`:
the inverse of `Stacks.RelativeProj.Situation.modulePushforwardMap` there. -/
public def moduleTransEquiv {W W' : s.base.affineOpens} (h : W ≤ W')
    {V : (relativeProj s).Opens} (hV : V ≤ (relativeProjChart s W).opensRange) :
    openSections (relativeProjChart s W) (moduleChart ℳ W) V
      ≃ₗ[ToType ((relativeProj s).ringCatSheaf.obj.obj (op V))]
      openSections (relativeProjChart s W') (moduleChart ℳ W') V :=
  (LinearEquiv.ofBijective ((modulePushforwardMap ℳ h).val.app (op V)).hom
    (bijective_modulePushforwardMap_app ℳ h hV)).symm

/-- The comparison undoes the linear equivalence it was inverted from. -/
public theorem modulePushforwardMap_moduleTransEquiv {W W' : s.base.affineOpens} (h : W ≤ W')
    {V : (relativeProj s).Opens} (hV : V ≤ (relativeProjChart s W).opensRange)
    (t : ToType (openSections (relativeProjChart s W) (moduleChart ℳ W) V)) :
    ((modulePushforwardMap ℳ h).val.app (op V)).hom (moduleTransEquiv ℳ h hV t) = t :=
  (LinearEquiv.ofBijective _ (bijective_modulePushforwardMap_app ℳ h hV)).apply_symm_apply t

/-- **The locally directed glueing datum of the sheaves attached to `ℳ` on the charts of a
relative projective spectrum.** For each inclusion `W ≤ W'` of affine opens of the base the
comparison is the canonical one across the comparison morphism of charts, inverted on sections
over the opens lying in the chart over `W`. -/
public def modulesDirectedGlueData :
    ModulesDirectedGlueData (relativeProj s) (relativeProjChart s) where
  mod := moduleChart ℳ
  opensRange_mono := opensRange_relativeProjChart_mono s
  locallyDirected := locallyDirected_relativeProjChart s
  trans := fun {_ _} h {_} hV => moduleTransEquiv ℳ h hV
  trans_map := by
    intro W W' h V U hV hUV t
    refine (bijective_modulePushforwardMap_app ℳ h (hUV.trans hV)).1 ?_
    refine (modulePushforwardMap_moduleTransEquiv ℳ h (hUV.trans hV) _).trans
      ((modulePushforwardMap_naturality ℳ h hUV _).trans (congrArg
        (fun z => ((Scheme.Modules.pushforward (relativeProjChart s W)).obj
          (moduleChart ℳ W)).val.map (homOfLE hUV).op z)
        (modulePushforwardMap_moduleTransEquiv ℳ h hV t))).symm
  trans_trans := by
    intro W W' W'' h h' V hV t
    refine (bijective_modulePushforwardMap_app ℳ (h.trans h') hV).1 ?_
    rw [modulePushforwardMap_moduleTransEquiv ℳ (h.trans h') hV,
      modulePushforwardMap_comp_apply ℳ h h',
      modulePushforwardMap_moduleTransEquiv ℳ h'
        (hV.trans (opensRange_relativeProjChart_mono s h)),
      modulePushforwardMap_moduleTransEquiv ℳ h hV]

/-- **The sheaf `ℳ̃` attached to a graded module on a relative projective spectrum**, glued from
the sheaves attached to its graded modules of sections on the charts. -/
public noncomputable abbrev moduleSheaf : (relativeProj s).Modules :=
  (modulesDirectedGlueData ℳ).glued

/-- `ℳ̃` restricts on the chart over `W` to the sheaf attached to the graded module of sections of
`ℳ` over `W`. -/
public noncomputable def moduleSheafChartIso (W : s.base.affineOpens) :
    (moduleSheaf ℳ).restrict (relativeProjChart s W) ≅ moduleChart ℳ W :=
  (modulesDirectedGlueData ℳ).chartIso W

end Stacks.RelativeProj.Situation

end
