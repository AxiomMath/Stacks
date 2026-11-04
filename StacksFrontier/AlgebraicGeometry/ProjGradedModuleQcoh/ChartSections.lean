module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStructureSheaf
public import StacksFrontier.AlgebraicGeometry.GradedLocalization.ModuleMaps
public import StacksFrontier.AlgebraicGeometry.ProjGradedModuleQcoh.StructureRestriction
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Sections of the associated module sheaf on an affine chart of Proj

Let `A = ⨁_{d ≥ 0} 𝒜 d` be a graded ring, `M = ⨁_{i ∈ ℤ} 𝒨 i` a graded `A`-module and `f`
homogeneous of positive degree. The open immersion `AlgebraicGeometry.Proj.awayι` presents the
standard open `D₊(f)` as the affine scheme `Spec A₍f₎`, so the restriction of the associated
sheaf `M̃` to that chart is a module on an affine scheme. This file computes its sections.

An open `V` of the chart with image `W = D₊(g)` in `Proj` has `Γ(M̃|_chart, V) = Γ(M̃, W)`,
because restriction along an open immersion is sections over the image; combined with the
standard-open identification `Γ(M̃, D₊(g)) ≃ M₍g₎` of
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv` this makes
the chart sections over `V` into `M₍g₎`. The content is that the identification is linear for
the action of `A₍f₎` on the chart, which reduces to the commuting square of the structure
sheaf, and that it carries the chart's restriction maps to the degree-zero restriction maps.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.imageSectionsIso`: sections of a restricted
  module over `V` are sections over the image of `V`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.chartDegreeZeroEquiv`: the chart sections over
  `V` as the degree-zero localization `M₍g₎`, linearly over `A₍f₎`.

## Main results

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.awayι_appIso_top_inv` and
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.awayι_appIso_inv`: the scalar action of the
  chart's coordinate ring is `AlgebraicGeometry.Proj.awayToSection`, on all of the chart and
  on a general chart open respectively.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.isIso_awayToSection` and
  `AlgebraicGeometry.ProjectiveSpectrum.Proj.surjective_awayToSection`: **that comparison map is
  an isomorphism** for `f` of positive degree, being a composite of three identifications.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.standardOpenEquiv_restrict`: the standard-open
  identification carries sheaf restriction to the degree-zero restriction map.

## Implementation notes

The whole-chart case of the scalar compatibility is the one with content: there the chart's
coordinate ring is compared with the sections over `D₊(f)` through Mathlib's
`AlgebraicGeometry.Proj.basicOpenIsoSpec`, whose global-sections formula is
`AlgebraicGeometry.Proj.basicOpenToSpec_app_top`. The general case follows by naturality of
`AlgebraicGeometry.Scheme.Hom.appIso`, since any two inclusions of the same pair of opens are
equal.

## References

* [Stacks Project, Tag 01MB](https://stacks.math.columbia.edu/tag/01MB)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite TopCat DirectSum Stacks.GradedLocalization
open AlgebraicGeometry

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local implicit_reducible] PresheafOfModules.presheaf SheafOfModules.toSheaf
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

universe u v w t

section General

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i]

/-- Sections of a restricted module over `V` are sections over the image of `V`. -/
public noncomputable def imageSectionsIso (N : Y.Modules) (V : X.Opens) (W : Y.Opens)
    (hW : i ''ᵁ V = W) : Γ(N.restrict i, V) ≅ Γ(N, W) :=
  N.restrictAppIso i V ≪≫ N.presheaf.mapIso (eqToIso hW.symm).op

/-- The identification of restricted sections with sections over the image is semilinear for
the scalar action pulled back along the open immersion. -/
public lemma imageSectionsIso_smul (N : Y.Modules) (V : X.Opens) (W : Y.Opens)
    (hW : i ''ᵁ V = W) (s : Γ(X, V)) (x : Γ(N.restrict i, V)) :
    (imageSectionsIso i N V W hW).hom (s • x) =
      (Y.presheaf.map (eqToHom hW.symm).op ((i.appIso V).inv s)) •
        (imageSectionsIso i N V W hW).hom x := by
  simp only [imageSectionsIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom,
    ConcreteCategory.comp_apply, Scheme.Modules.smul_restrictAppIso_hom_apply, N.map_smul]

/-- The identification of restricted sections with sections over the image commutes with
restriction to a smaller open. -/
public lemma imageSectionsIso_naturality (N : Y.Modules) (V₁ V₂ : X.Opens) (W₁ W₂ : Y.Opens)
    (h₁ : i ''ᵁ V₁ = W₁) (h₂ : i ''ᵁ V₂ = W₂) (hV : V₂ ≤ V₁) (hW : W₂ ≤ W₁) :
    (N.restrict i).presheaf.map (homOfLE hV).op ≫
        (imageSectionsIso i N V₂ W₂ h₂).hom =
      (imageSectionsIso i N V₁ W₁ h₁).hom ≫ N.presheaf.map (homOfLE hW).op := by
  simp only [imageSectionsIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom,
    Category.assoc, Scheme.Modules.map_restrictAppIso_hom_assoc,
    ← Functor.map_comp]
  congr 2

end General

section Chart

variable {S : Type u} {σ : Type w}
  [CommRing S] [SetLike σ S] [AddSubgroupClass σ S] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- On the whole of the affine chart `Spec S₍f₎`, the scalar action of the chart's coordinate
ring is Mathlib's canonical comparison map `awayToSection`. -/
public lemma awayι_appIso_top_inv {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒜 f))).inv ≫
      ((AlgebraicGeometry.Proj.awayι 𝒜 f hf hd).appIso ⊤).inv ≫
      (AlgebraicGeometry.Proj 𝒜).presheaf.map (eqToHom (show
        AlgebraicGeometry.Proj.basicOpen 𝒜 f =
          (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd) ''ᵁ ⊤ by
        rw [Scheme.Hom.image_top_eq_opensRange, AlgebraicGeometry.Proj.opensRange_awayι])).op =
      AlgebraicGeometry.Proj.awayToSection 𝒜 f := by
  let i := AlgebraicGeometry.Proj.awayι 𝒜 f hf hd
  let e := AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 f hf hd
  have h : e.hom ≫ i = (AlgebraicGeometry.Proj.basicOpen 𝒜 f).ι := by
    simp [i, AlgebraicGeometry.Proj.awayι, e]
  have htop : i ''ᵁ ⊤ = AlgebraicGeometry.Proj.basicOpen 𝒜 f := by
    simp [i, Scheme.Hom.image_top_eq_opensRange, AlgebraicGeometry.Proj.opensRange_awayι]
  have hi : (⊤ : (Spec (.of (HomogeneousLocalization.Away 𝒜 f))).Opens) ≤
      i ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f := by
    rw [← htop, i.preimage_image_eq]
  have h2 : (⊤ : (AlgebraicGeometry.Proj.basicOpen 𝒜 f).toScheme.Opens) ≤ e.hom ⁻¹ᵁ ⊤ := by
    simp
  have hLE : e.hom.appLE ⊤ ⊤ h2 = e.hom.appTop := Scheme.Hom.appLE_eq_app e.hom
  have hcomp := Scheme.Hom.appLE_comp_appLE e.hom i
    (AlgebraicGeometry.Proj.basicOpen 𝒜 f) ⊤ ⊤ hi h2
  rw [hLE] at hcomp
  have hh : i.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 f) ⊤ hi ≫ e.hom.appTop =
      (AlgebraicGeometry.Proj.basicOpen 𝒜 f).topIso.inv := by
    refine hcomp.trans ?_
    simp only [h]
    rw [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    congr 1
  rw [show e.hom.appTop = (Scheme.ΓSpecIso _).hom ≫
      AlgebraicGeometry.Proj.awayToSection 𝒜 f ≫
      (AlgebraicGeometry.Proj.basicOpen 𝒜 f).topIso.inv from
      AlgebraicGeometry.Proj.basicOpenToSpec_app_top 𝒜 f] at hh
  simp only [← Category.assoc, Iso.comp_inv_eq] at hh
  simp only [Iso.inv_hom_id] at hh
  have hi_iso : IsIso (i.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 f) ⊤ hi) := by
    have hmap : i.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 f) ⊤ hi =
        (AlgebraicGeometry.Proj 𝒜).presheaf.map (eqToHom htop).op ≫ (i.appIso ⊤).hom := by
      simp [Scheme.Hom.appIso_hom']
    rw [hmap]
    infer_instance
  apply (cancel_epi (i.appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 f) ⊤ hi ≫
    (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒜 f))).hom)).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [Scheme.Hom.appLE_appIso_inv_assoc, ← Functor.map_comp]
  simpa [← Category.assoc] using hh.symm

/-- **The comparison map `A₍f₎ ⟶ Γ(D₊(f), 𝒪)` is an isomorphism** for `f` homogeneous of
positive degree. The previous lemma exhibits it as a composite of three isomorphisms: the
identification of the global sections of `Spec A₍f₎` with `A₍f₎`, the comparison of the sections
of the chart with the sections over its image, and the identification of that image with
`D₊(f)`. -/
public theorem isIso_awayToSection {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    IsIso (AlgebraicGeometry.Proj.awayToSection 𝒜 f) := by
  rw [← awayι_appIso_top_inv 𝒜 hf hd]
  infer_instance

/-- **Every section of the structure sheaf on a standard open `D₊(f)` is a degree-zero
fraction**, for `f` homogeneous of positive degree: the comparison map is an isomorphism. This is
what transfers semilinearity over `A₍f₎` into linearity over `Γ(D₊(f), 𝒪)`, the action of `A₍f₎`
on the sections of a sheaf on `D₊(f)` being the action of `Γ(D₊(f), 𝒪)` pulled back along the
comparison map. -/
public theorem surjective_awayToSection {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    Function.Surjective (AlgebraicGeometry.Proj.awayToSection 𝒜 f).hom :=
  have := isIso_awayToSection 𝒜 hf hd
  (ConcreteCategory.bijective_of_isIso (AlgebraicGeometry.Proj.awayToSection 𝒜 f)).2

/-- On a chart open `V` with image `W`, the scalar action of the chart's coordinate ring is
the restriction of `awayToSection`. -/
public lemma awayι_appIso_inv {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (V : (Spec (.of (HomogeneousLocalization.Away 𝒜 f))).Opens)
    (W : (AlgebraicGeometry.Proj 𝒜).Opens)
    (hW : (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd) ''ᵁ V = W)
    (hWU : W ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 f) :
    (Scheme.ΓSpecIso (.of (HomogeneousLocalization.Away 𝒜 f))).inv ≫
      (Spec (.of (HomogeneousLocalization.Away 𝒜 f))).presheaf.map V.leTop.op ≫
      ((AlgebraicGeometry.Proj.awayι 𝒜 f hf hd).appIso V).inv ≫
      (AlgebraicGeometry.Proj 𝒜).presheaf.map (eqToHom hW.symm).op =
      AlgebraicGeometry.Proj.awayToSection 𝒜 f ≫
        (AlgebraicGeometry.Proj 𝒜).presheaf.map (homOfLE hWU).op := by
  rw [Scheme.Hom.appIso_inv_naturality_assoc, ← awayι_appIso_top_inv 𝒜 hf hd]
  simp only [Category.assoc, ← Functor.map_comp]
  congr 2

end Chart

section Module

variable {S M : Type u} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨]

/-- On a chart open identified with a standard open `D₊(g)`, the sections of the associated
module sheaf are the degree-zero localization `M₍g₎`, linearly over `S₍f₎` acting through the
given ring map. -/
public noncomputable def chartDegreeZeroEquiv
    {f g : S} {d e : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) (hg : g ∈ 𝒜 e) (he : 0 < e)
    (hfg : AlgebraicGeometry.Proj.basicOpen 𝒜 g ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
    (V : (Spec (.of (HomogeneousLocalization.Away 𝒜 f))).Opens)
    (hV : (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd) ''ᵁ V =
      AlgebraicGeometry.Proj.basicOpen 𝒜 g)
    (α : HomogeneousLocalization.Away 𝒜 f →+* HomogeneousLocalization.Away 𝒜 g)
    (hα : CommRingCat.ofHom α ≫ AlgebraicGeometry.Proj.awayToSection 𝒜 g =
      AlgebraicGeometry.Proj.awayToSection 𝒜 f ≫
        (AlgebraicGeometry.Proj 𝒜).presheaf.map (homOfLE hfg).op) :
    letI := Module.compHom (GradedModuleDegreeZeroLocalization 𝒜 𝒨 g) α
    ((modulesSpecToSheaf.obj ((show (AlgebraicGeometry.Proj 𝒜).Modules from
      associatedModuleSheaf 𝒜 𝒨).restrict
      (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd))).obj.obj (.op V))
      ≃ₗ[HomogeneousLocalization.Away 𝒜 f] GradedModuleDegreeZeroLocalization 𝒜 𝒨 g := by
  letI := Module.compHom (GradedModuleDegreeZeroLocalization 𝒜 𝒨 g) α
  let N : (AlgebraicGeometry.Proj 𝒜).Modules := associatedModuleSheaf 𝒜 𝒨
  let i := AlgebraicGeometry.Proj.awayι 𝒜 f hf hd
  let E := associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hg he
  let I := imageSectionsIso i N V (AlgebraicGeometry.Proj.basicOpen 𝒜 g) hV
  let A := (AddEquiv.ofBijective I.hom.hom (ConcreteCategory.bijective_of_isIso I.hom)).trans
    E.toAddEquiv
  refine { A with map_smul' := ?_ }
  intro r x
  change E (I.hom (r • x)) = α r • E (I.hom x)
  change E (I.hom (((Spec (.of (HomogeneousLocalization.Away 𝒜 f))).presheaf.map
    V.leTop.op ((Scheme.ΓSpecIso _).inv r)) • (show Γ(N.restrict i, V) from x))) = _
  rw [imageSectionsIso_smul]
  have hscalar := congrArg (fun φ => φ.hom r) (awayι_appIso_inv 𝒜 hf hd V _ hV hfg)
  change (AlgebraicGeometry.Proj 𝒜).presheaf.map _
      ((i.appIso V).inv ((Spec _).presheaf.map _ ((Scheme.ΓSpecIso _).inv r))) =
      (AlgebraicGeometry.Proj 𝒜).presheaf.map _
        (AlgebraicGeometry.Proj.awayToSection 𝒜 f r) at hscalar
  rw [hscalar]
  have hscalar' := congrArg (fun φ => φ.hom r) hα
  change AlgebraicGeometry.Proj.awayToSection 𝒜 g (α r) =
    (AlgebraicGeometry.Proj 𝒜).presheaf.map _
      (AlgebraicGeometry.Proj.awayToSection 𝒜 f r) at hscalar'
  rw [← hscalar']
  exact E.map_smul (α r) _

/-- The inverse of the standard-open identification is the canonical comparison map. -/
public lemma associatedModuleSheafStandardOpenEquiv_symm_apply {f : S} {d : ℕ}
    (hf : f ∈ 𝒜 d) (hd : 0 < d) (a : GradedModuleDegreeZeroLocalization 𝒜 𝒨 f) :
    (associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf hd).symm a =
      degreeZeroToSection 𝒜 𝒨 f a := by
  have hsymm : (associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf hd).symm =
      LinearEquiv.ofBijective (degreeZeroToSection 𝒜 𝒨 f)
        ⟨degreeZeroToSection_injective 𝒜 𝒨 hf hd,
          degreeZeroToSection_surjective 𝒜 𝒨 hf hd⟩ := LinearEquiv.symm_symm _
  rw [hsymm]
  exact LinearEquiv.ofBijective_apply (degreeZeroToSection 𝒜 𝒨 f) a

/-- The standard-open identification inverts the canonical comparison map. -/
public lemma associatedModuleSheafStandardOpenEquiv_degreeZeroToSection {f : S} {d : ℕ}
    (hf : f ∈ 𝒜 d) (hd : 0 < d) (a : GradedModuleDegreeZeroLocalization 𝒜 𝒨 f) :
    associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf hd (degreeZeroToSection 𝒜 𝒨 f a) = a := by
  rw [← associatedModuleSheafStandardOpenEquiv_symm_apply 𝒜 𝒨 hf hd,
    LinearEquiv.apply_symm_apply]

/-- The standard-open identification carries sheaf restriction to the degree-zero
restriction map. -/
public lemma standardOpenEquiv_restrict
    {f g : S} {d e : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) (hg : g ∈ 𝒜 e) (he : 0 < e)
    (hfg : ProjectiveSpectrum.basicOpen 𝒜 g ≤ ProjectiveSpectrum.basicOpen 𝒜 f)
    (x : (associatedModuleSheaf 𝒜 𝒨).val.obj (.op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hg he
        ((associatedModuleSheaf 𝒜 𝒨).val.map (homOfLE hfg).op x) =
      (ProjectiveSpectrum.moduleRestrictionMaps 𝒜 𝒨 f g
        ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg).degreeZeroMap
        (associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf hd x) := by
  obtain ⟨a, rfl⟩ := degreeZeroToSection_surjective 𝒜 𝒨 hf hd x
  rw [degreeZeroToSection_restriction 𝒜 𝒨 f g ⟨d, hd, hf⟩ ⟨e, he, hg⟩ hfg a,
    associatedModuleSheafStandardOpenEquiv_degreeZeroToSection,
    associatedModuleSheafStandardOpenEquiv_degreeZeroToSection]

end Module

end AlgebraicGeometry.ProjectiveSpectrum.Proj
