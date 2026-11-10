module

public import StacksFrontier.AlgebraicGeometry.ProjGradedModuleQcoh.ChartSections
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartBaseChange
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartQcoh
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartTranspose
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ComparisonSections
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The chart sections of the twist comparison, and the twist transport

The affine invertibility criterion
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_transpose_of_isIso_extension` is applied, in
`StacksFrontier/AlgebraicGeometry/TwistChartLocality/ChartTranspose.lean`, to a transpose between
the
inverse images of two twisting sheaves along the chart spectra `AlgebraicGeometry.Proj.awayι`. It
consumes the global sections of those inverse images as modules over the chart coordinate rings,
so those modules have to be named: for a graded module `M` over a graded ring `𝒜` and `f`
homogeneous of positive degree, the global sections of the inverse image of `M̃` along
`awayι 𝒜 f` are the degree-zero localization `M₍f₎`.

This file proves that, proves the general facts about an inverse adjoint transpose along an open
immersion that the identification of the *morphism* needs, and closes the chain: the global
sections of the chart transpose are the algebraic chart comparison, whose coefficient extension is
invertible in degree one, so the chart inverse image of Tag 01MY's comparison map is invertible
and the twist transport holds at the polynomial grading.

## Main results

* `Stacks.AlgebraicGeometry.TwistChartLocality.restrictTranspose_app`: **the sections formula for
  a transpose along an open immersion.** The transpose of `u : M ⟶ i_* N` along
  `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` acts on sections over an open of the
  source as `u` acts on sections over its image.
* `Stacks.AlgebraicGeometry.TwistChartLocality.homEquiv_symm_eq_restrict`: the transpose along the
  inverse-image adjunction is that transpose, read through
  `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.
* `Stacks.AlgebraicGeometry.TwistChartLocality.chartTopDegreeZeroEquiv` and
  `Stacks.AlgebraicGeometry.TwistChartLocality.chartΓIso`: **the chart sections.** The global
  sections of the restriction, respectively of the inverse image, of `M̃` along the chart spectrum
  of `f` are `M₍f₎`, linearly over `𝒜₍f₎`.
* `Stacks.AlgebraicGeometry.TwistChartLocality.chartΓIso_moduleSpecΓ_chartAdjointTwistMap`: **the
  Γ bridge.** The global sections of
  `Stacks.AlgebraicGeometry.TwistChartLocality.chartAdjointTwistMap`, read through those chart
  identifications, are the algebraic chart comparison
  `Stacks.AlgebraicGeometry.TwistChartLocality.twistDegreeZeroMap`.
* `Stacks.AlgebraicGeometry.TwistChartLocality.isIso_transpose_chartAdjointTwistMap` and
  `Stacks.AlgebraicGeometry.TwistChartLocality.isIso_pullback_awayι_map_twistMap`: **the chart
  transpose and the chart inverse image of Tag 01MY's comparison map are invertible** at a
  homogeneous element of degree one.
* `Stacks.AlgebraicGeometry.TwistChartLocality.isIso_projTwistComparison`: **Tag 01MY's
  comparison map is an isomorphism** when the images of the degree-one part generate the
  irrelevant ideal of the target.
* `Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport`: **the twist transport at
  the polynomial grading and the coefficient map `ULift ℤ → S`**, which is the form the
  projective-space model comparison needs. It is weaker than clause (3) of [Stacks, Tag 01N2] —
  specialized in the grading and in the coefficient map, and asserting only that the two
  twisting sheaves are isomorphic rather than that the canonical comparison is an isomorphism —
  and carries no project tag.

## Implementation notes

The two general facts are routed through `restrictAdjunction` rather than
`AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction` because only the former has a
sections formula: `AlgebraicGeometry.Scheme.Modules.restrictAppIso` is the identity, so restricted
sections over `V` *are* the sections over `i ''ᵁ V`, and
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app` is an explicit restriction map,
whereas the unit of the inverse-image adjunction admits no such description. The two transposes
are then compared by `CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`.

`AlgebraicGeometry.ProjectiveSpectrum.Proj.chartDegreeZeroEquiv` is **not** what the chart sections
specialize: its target carries a `Module.compHom` along a ring homomorphism `𝒜₍f₎ ⟶ 𝒜₍g₎` in the
type, so at `g = f` it is an equivalence for a second scalar action and not for the one the
criterion consumes. What is reused instead are its two ingredients,
`AlgebraicGeometry.ProjectiveSpectrum.Proj.imageSectionsIso` at `V = ⊤` and
`AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv`, together with
the scalar compatibility `AlgebraicGeometry.ProjectiveSpectrum.Proj.awayι_appIso_top_inv`.

No local reducibility attribute is in force. `AlgebraicGeometry.moduleSpecΓFunctor` leaves its ring
implicit, and solving for it by unification against `Spec ?R` exhausts the heartbeat budget, so the
ring is supplied explicitly at every occurrence; the scalar action on its values is reached through
`Stacks.AlgebraicGeometry.SectionsColimit.moduleSpecΓ_smul` rather than by a conversion, and
`AlgebraicGeometry.ProjectiveSpectrum.Proj.imageSectionsIso_smul` is applied as a term for the same
reason.

## References

* [Stacks Project, Tag 01MB](https://stacks.math.columbia.edu/tag/01MB)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry DirectSum HomogeneousIdeal HomogeneousLocalization
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open AlgebraicGeometry.Scheme.Modules
open Stacks.GradedLocalization
open scoped ChangeOfRings TensorProduct

namespace Stacks.AlgebraicGeometry.TwistChartLocality

universe u

/-! ### The inverse adjoint transpose along an open immersion, on sections -/

section General

variable {X Y : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i] (M : Y.Modules) (N : X.Modules)
  (u : M ⟶ (pushforward i).obj N)

/-- **The transpose along the restriction adjunction, on sections.** For `u : M ⟶ i_* N` with `i`
an open immersion, the transpose of `u` along `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`
acts on sections over an open `V` of the source whose image is `W` as `u` acts on sections over
`W`.

This is the defining property of the transpose read at `W`, where the unit of the restriction
adjunction is the restriction map `Γ(M, W) ⟶ Γ(M, i ''ᵁ (i ⁻¹ᵁ W))` of
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app`; the hypotheses make that
restriction a map between equal opens. -/
public theorem restrictTranspose_app (V : X.Opens) (W : Y.Opens) (hW : i ''ᵁ V = W)
    (hV : i ⁻¹ᵁ W = V) (x : Γ(M, W)) :
    (((restrictAdjunction i).homEquiv M N).symm u).app V
        ((imageSectionsIso i M V W hW).inv x) =
      N.presheaf.map (eqToHom hV.symm).op (u.app W x) := by
  subst hV
  set θ := ((restrictAdjunction i).homEquiv M N).symm u with hθ
  have hdef : (restrictAdjunction i).unit.app M ≫ (pushforward i).map θ = u := by
    have h := ((restrictAdjunction i).homEquiv M N).apply_symm_apply u
    rwa [Adjunction.homEquiv_unit] at h
  have hd2 := congrArg (fun h => Scheme.Modules.Hom.app h W) hdef
  simp only [Hom.comp_app, pushforward_map_app] at hd2
  have hkey : M.presheaf.map (eqToHom hW).op =
      Hom.app ((restrictAdjunction i).unit.app M) W := by
    rw [restrictAdjunction_unit_app_app]
    congr 1
  have hid : N.presheaf.map (eqToHom (rfl : i ⁻¹ᵁ W = i ⁻¹ᵁ W)).op = 𝟙 _ := by
    rw [eqToHom_refl, op_id, N.presheaf.map_id]
  refine Eq.trans (congrArg (ConcreteCategory.hom (Hom.app θ _))
    (ConcreteCategory.congr_hom hkey x)) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _).symm ?_
  refine Eq.trans (ConcreteCategory.congr_hom hd2 x) ?_
  exact ((ConcreteCategory.congr_hom hid _).trans (ConcreteCategory.id_apply _)).symm

/-- The unit of the restriction adjunction, followed by the comparison with the inverse image, is
the unit of the inverse-image adjunction. -/
private theorem restrictAdjunction_unit_comp_map_hom :
    (restrictAdjunction i).unit.app M ≫
        (pushforward i).map ((restrictFunctorIsoPullback i).hom.app M) =
      (pullbackPushforwardAdjunction i).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ _

/-- **The inverse adjoint transpose along an open immersion is the transpose along the restriction
adjunction**, read through
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`.

Both functors are left adjoint to the direct image, and
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app` says the comparison of the two carries
the unit of one to the unit of the other; so the two transposes of the same morphism differ by
that comparison. -/
public theorem homEquiv_symm_eq_restrict :
    ((pullbackPushforwardAdjunction i).homEquiv M N).symm u =
      (restrictFunctorIsoPullback i).inv.app M ≫
        ((restrictAdjunction i).homEquiv M N).symm u := by
  have hu : (restrictFunctorIsoPullback i).hom.app M ≫
      ((pullbackPushforwardAdjunction i).homEquiv M N).symm u =
      ((restrictAdjunction i).homEquiv M N).symm u := by
    refine ((restrictAdjunction i).homEquiv M N).injective ?_
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_comp,
      ← Category.assoc, restrictAdjunction_unit_comp_map_hom, ← Adjunction.homEquiv_unit,
      Equiv.apply_symm_apply]
  rw [← hu, Iso.inv_hom_id_app_assoc]

/-- The action on sections of a morphism of modules commutes with restriction to a smaller
open. -/
@[reassoc]
public theorem app_naturality {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {V W : X.Opens}
    (h : V ⟶ W) :
    Scheme.Modules.Hom.app φ W ≫ N.presheaf.map h.op =
      M.presheaf.map h.op ≫ Scheme.Modules.Hom.app φ V :=
  (φ.mapPresheaf.naturality h.op).symm

/-- **The unit of the inverse-image adjunction of an open immersion, on sections.** It is the
restriction map `Γ(M, U) ⟶ Γ(M, i ''ᵁ (i ⁻¹ᵁ U))` of
`AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_app`, read into the restricted
module and then carried to the inverse image. -/
@[reassoc]
public theorem unit_app_eq_comp (U : Y.Opens) :
    Scheme.Modules.Hom.app ((pullbackPushforwardAdjunction i).unit.app M) U =
      M.presheaf.map (homOfLE (i.image_preimage_le U)).op ≫ (M.restrictAppIso i (i ⁻¹ᵁ U)).inv ≫
        Scheme.Modules.Hom.app ((restrictFunctorIsoPullback i).hom.app M) (i ⁻¹ᵁ U) := by
  have h1 := congrArg (fun h => Scheme.Modules.Hom.app h U)
    (restrictAdjunction_unit_comp_map_hom i M)
  simp only [Hom.comp_app, pushforward_map_app, restrictAdjunction_unit_app_app] at h1
  rw [← h1]
  rfl

/-- **The unit of the inverse-image adjunction of an open immersion, on a section.** -/
public theorem unit_app_apply (U : Y.Opens) (t : Γ(M, U)) :
    Scheme.Modules.Hom.app ((pullbackPushforwardAdjunction i).unit.app M) U t =
      Scheme.Modules.Hom.app ((restrictFunctorIsoPullback i).hom.app M) (i ⁻¹ᵁ U)
        ((M.restrictAppIso i (i ⁻¹ᵁ U)).inv
          (M.presheaf.map (homOfLE (i.image_preimage_le U)).op t)) := by
  refine Eq.trans (ConcreteCategory.congr_hom (unit_app_eq_comp i M U) t) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  exact ConcreteCategory.comp_apply _ _ _

/-- **The sections of the unit over the image of an open immersion collapse to the identity.**
The unit of the inverse-image adjunction at `U = i ''ᵁ ⊤`, followed by any two restriction maps of
the inverse image down to the whole source and by the identification of the restricted sections
over the source with `Γ(M, U)`, is the identity of `Γ(M, U)`.

Everything in sight is a restriction map of `M` between opens between which there is exactly one
morphism, the comparison of the restriction with the inverse image cancelling against its own
inverse; so the composite is `M.presheaf.map` of an identity. -/
public theorem collapse (U : Y.Opens) (hW : i ''ᵁ ⊤ = U) (V₂ : X.Opens)
    (h₂ : V₂ ⟶ i ⁻¹ᵁ U) (h₃ : (⊤ : X.Opens) ⟶ V₂) :
    M.presheaf.map (homOfLE (i.image_preimage_le U)).op ≫ (M.restrictAppIso i (i ⁻¹ᵁ U)).inv ≫
        Scheme.Modules.Hom.app ((restrictFunctorIsoPullback i).hom.app M) (i ⁻¹ᵁ U) ≫
        ((pullback i).obj M).presheaf.map h₂.op ≫
        ((pullback i).obj M).presheaf.map h₃.op ≫
        Scheme.Modules.Hom.app ((restrictFunctorIsoPullback i).inv.app M) ⊤ ≫
        (imageSectionsIso i M ⊤ U hW).hom = 𝟙 Γ(M, U) := by
  have hhi : Scheme.Modules.Hom.app ((restrictFunctorIsoPullback i).hom.app M) ⊤ ≫
      Scheme.Modules.Hom.app ((restrictFunctorIsoPullback i).inv.app M) ⊤ = 𝟙 _ := by
    rw [← Hom.comp_app, Iso.hom_inv_id_app, Hom.id_app]
  simp only [imageSectionsIso, Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]
  rw [app_naturality_assoc ((restrictFunctorIsoPullback i).hom.app M) h₂,
    app_naturality_assoc ((restrictFunctorIsoPullback i).hom.app M) h₃,
    ← Category.assoc (Scheme.Modules.Hom.app ((restrictFunctorIsoPullback i).hom.app M) ⊤),
    hhi, Category.id_comp]
  simp only [map_restrictAppIso_hom_assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp]
  exact Eq.trans (congrArg M.presheaf.map (Subsingleton.elim _ (𝟙 (Opposite.op U))))
    (M.presheaf.map_id _)

/-- **The collapse, on a section.** The element form of
`Stacks.AlgebraicGeometry.TwistChartLocality.collapse`. -/
public theorem collapse_apply (U : Y.Opens) (hW : i ''ᵁ ⊤ = U) (V₂ : X.Opens)
    (h₂ : V₂ ⟶ i ⁻¹ᵁ U) (h₃ : (⊤ : X.Opens) ⟶ V₂) (t : Γ(M, U)) :
    (imageSectionsIso i M ⊤ U hW).hom
        (Scheme.Modules.Hom.app ((restrictFunctorIsoPullback i).inv.app M) ⊤
          (((pullback i).obj M).presheaf.map h₃.op
            (((pullback i).obj M).presheaf.map h₂.op
              (Scheme.Modules.Hom.app ((restrictFunctorIsoPullback i).hom.app M) (i ⁻¹ᵁ U)
                ((M.restrictAppIso i (i ⁻¹ᵁ U)).inv
                  (M.presheaf.map (homOfLE (i.image_preimage_le U)).op t)))))) = t := by
  have h := ConcreteCategory.congr_hom (collapse i M U hW V₂ h₂ h₃) t
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ConcreteCategory.id_apply] at h
  exact h

/-- **The collapse, read off the unit of the inverse-image adjunction.** The unit of the
inverse-image adjunction at the image of the whole source, followed by two restriction maps of the
inverse image down to the whole source and by the identification of the restricted sections with
`Γ(M, U)`, leaves a section unchanged. -/
public theorem collapse_unit_apply (U : Y.Opens) (hW : i ''ᵁ ⊤ = U) (V₂ : X.Opens)
    (h₂ : V₂ ⟶ i ⁻¹ᵁ U) (h₃ : (⊤ : X.Opens) ⟶ V₂) (t : Γ(M, U)) :
    (imageSectionsIso i M ⊤ U hW).hom
        (Scheme.Modules.Hom.app ((restrictFunctorIsoPullback i).inv.app M) ⊤
          (((pullback i).obj M).presheaf.map h₃.op
            (((pullback i).obj M).presheaf.map h₂.op
              (Scheme.Modules.Hom.app ((pullbackPushforwardAdjunction i).unit.app M) U t))))
      = t := by
  rw [unit_app_apply]
  exact collapse_apply i M U hW V₂ h₂ h₃ t

end General

/-! ### The chart sections of an associated module sheaf -/

section ChartSections

variable {S M : Type u} {σ τ : Type u}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ) [Decomposition 𝒨]
  [SetLike.GradedSMul 𝒜 𝒨]

/-- The image of the whole chart spectrum of `f` is the standard open `D₊(f)`. -/
public theorem awayι_image_top {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    AlgebraicGeometry.Proj.awayι 𝒜 f hf hd ''ᵁ ⊤ = AlgebraicGeometry.Proj.basicOpen 𝒜 f := by
  rw [Scheme.Hom.image_top_eq_opensRange, AlgebraicGeometry.Proj.opensRange_awayι]

/-- **The global sections of the restriction of `M̃` to the chart of `f` are `M₍f₎`**, linearly
over the chart's coordinate ring `𝒜₍f₎` and with no auxiliary ring homomorphism in sight.

This is the whole-chart case of
`AlgebraicGeometry.ProjectiveSpectrum.Proj.chartDegreeZeroEquiv`, which it does *not* specialize:
that statement compares the sections over a chart open with `M₍g₎` for the `g` cutting out its
image and is therefore semilinear along a ring homomorphism `𝒜₍f₎ ⟶ 𝒜₍g₎` whose target module
structure is a `Module.compHom` written into the type. Here the open is the whole chart, so the
target is `AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheafStandardOpenEquiv`'s
plain action, which is the one the affine invertibility criterion consumes. -/
public def chartTopDegreeZeroEquiv {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (moduleSpecΓFunctor (R := CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).obj
        ((show (AlgebraicGeometry.Proj 𝒜).Modules from
          associatedModuleSheaf 𝒜 𝒨).restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd))
      ≃ₗ[HomogeneousLocalization.Away 𝒜 f] GradedModuleDegreeZeroLocalization 𝒜 𝒨 f := by
  let N : (AlgebraicGeometry.Proj 𝒜).Modules := associatedModuleSheaf 𝒜 𝒨
  let E := associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf hd
  let I := imageSectionsIso (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd) N ⊤
    (AlgebraicGeometry.Proj.basicOpen 𝒜 f) (awayι_image_top 𝒜 hf hd)
  let Aeq := (AddEquiv.ofBijective I.hom.hom (ConcreteCategory.bijective_of_isIso I.hom)).trans
    E.toAddEquiv
  refine { Aeq with map_smul' := fun r x => ?_ }
  change E (I.hom (r • x)) = r • E (I.hom x)
  rw [← Stacks.AlgebraicGeometry.SectionsColimit.moduleSpecΓ_smul
    (N.restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)) r x]
  have hscalar := ConcreteCategory.congr_hom (awayι_appIso_top_inv 𝒜 hf hd) r
  simp only [ConcreteCategory.comp_apply] at hscalar
  refine Eq.trans (congrArg E (imageSectionsIso_smul
    (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd) N ⊤
    (AlgebraicGeometry.Proj.basicOpen 𝒜 f) (awayι_image_top 𝒜 hf hd) _ x)) ?_
  rw [hscalar]
  exact E.map_smul r _

/-- The chart identification of
`Stacks.AlgebraicGeometry.TwistChartLocality.chartTopDegreeZeroEquiv` is, by construction, the
identification of restricted sections with sections over the image followed by the standard-open
identification. -/
public theorem chartTopDegreeZeroEquiv_apply {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (y : (moduleSpecΓFunctor (R := CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).obj
      ((show (AlgebraicGeometry.Proj 𝒜).Modules from
        associatedModuleSheaf 𝒜 𝒨).restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd))) :
    chartTopDegreeZeroEquiv 𝒜 𝒨 hf hd y =
      associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf hd
        ((imageSectionsIso (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)
          (show (AlgebraicGeometry.Proj 𝒜).Modules from associatedModuleSheaf 𝒜 𝒨) ⊤
          (AlgebraicGeometry.Proj.basicOpen 𝒜 f) (awayι_image_top 𝒜 hf hd)).hom y) :=
  rfl

/-- **The global sections of the inverse image of `M̃` along the chart spectrum of `f` are
`M₍f₎`**, as a module over the chart's coordinate ring.

The inverse image along an open immersion is the restriction, by
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback`, and the restricted sections are
`Stacks.AlgebraicGeometry.TwistChartLocality.chartTopDegreeZeroEquiv`. -/
public def chartΓIso {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    (moduleSpecΓFunctor (R := CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).obj
        ((pullback (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)).obj
          (associatedModuleSheaf 𝒜 𝒨)) ≅
      ModuleCat.of (HomogeneousLocalization.Away 𝒜 f)
        (GradedModuleDegreeZeroLocalization 𝒜 𝒨 f) :=
  (moduleSpecΓFunctor (R := CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).mapIso
      (((restrictFunctorIsoPullback (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)).app
        (associatedModuleSheaf 𝒜 𝒨)).symm) ≪≫
    (chartTopDegreeZeroEquiv 𝒜 𝒨 hf hd).toModuleIso

/-- The chart identification of
`Stacks.AlgebraicGeometry.TwistChartLocality.chartΓIso` is, by construction, the comparison of the
inverse image with the restriction, followed by the identification of restricted sections with
sections over the image and by the standard-open identification. -/
public theorem chartΓIso_hom_apply {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (w : (moduleSpecΓFunctor (R := CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).obj
      ((pullback (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)).obj (associatedModuleSheaf 𝒜 𝒨))) :
    (chartΓIso 𝒜 𝒨 hf hd).hom w =
      associatedModuleSheafStandardOpenEquiv 𝒜 𝒨 hf hd
        ((imageSectionsIso (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)
            (show (AlgebraicGeometry.Proj 𝒜).Modules from associatedModuleSheaf 𝒜 𝒨) ⊤
            (AlgebraicGeometry.Proj.basicOpen 𝒜 f) (awayι_image_top 𝒜 hf hd)).hom
          (Scheme.Modules.Hom.app
            ((restrictFunctorIsoPullback (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)).inv.app
              (associatedModuleSheaf 𝒜 𝒨)) ⊤ w)) :=
  rfl

/-- The whole chart spectrum of `f` is the inverse image of the standard open `D₊(f)`. -/
public theorem awayι_preimage_basicOpen_self {f : S} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    AlgebraicGeometry.Proj.awayι 𝒜 f hf hd ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f = ⊤ := by
  refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun x => ?_)
  have hx : (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd).base x ∈
      AlgebraicGeometry.Proj.basicOpen 𝒜 f := by
    rw [← AlgebraicGeometry.Proj.opensRange_awayι 𝒜 f hf hd]
    exact ⟨x, rfl⟩
  exact hx

end ChartSections

/-! ### The global sections of the chart transpose -/

section ChartTranspose

variable {A B : Type u} {σ τ : Type u}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
  (ψ : 𝒜 →+*ᵍ ℬ) (hψ : ℬ₊ ≤ 𝒜₊.map ψ) {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d) (n : ℤ)

/-- The two factorizations of the chart square's diagonal have the same inverse image of
`D₊(f)`. -/
public theorem awayι_comp_map_preimage :
    (Spec.map (CommRingCat.ofHom (Away.map ψ f)) ≫
          AlgebraicGeometry.Proj.awayι 𝒜 f hf hd) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f =
      (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd ≫
          AlgebraicGeometry.Proj.map ψ hψ) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f := by
  rw [AlgebraicGeometry.Proj.awayι_comp_map ψ hψ hd f hf]

/-- The inverse image of `D₊(f)` along the chart square's diagonal is the whole chart spectrum
of `ψ f`. -/
public theorem comp_preimage_basicOpen_self :
    (Spec.map (CommRingCat.ofHom (Away.map ψ f)) ≫
          AlgebraicGeometry.Proj.awayι 𝒜 f hf hd) ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen 𝒜 f = ⊤ := by
  rw [show (Spec.map (CommRingCat.ofHom (Away.map ψ f)) ≫
        AlgebraicGeometry.Proj.awayι 𝒜 f hf hd) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f =
      Spec.map (CommRingCat.ofHom (Away.map ψ f)) ⁻¹ᵁ
        (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd ⁻¹ᵁ
          AlgebraicGeometry.Proj.basicOpen 𝒜 f) from rfl,
    awayι_preimage_basicOpen_self 𝒜 hf hd]
  rfl

/-- **The morphism the chart square's composite adjunction transposes, on sections over
`D₊(f)`.** Its three trailing comparisons of direct images are, on sections, two identities and
one restriction along equal opens, so what is left is the explicit pointwise comparison followed
by the unit of the chart adjunction of `Proj ℬ`. -/
public theorem chartPushforwardTwistMap_app
    (w : Γ(twistingSheaf 𝒜 n, AlgebraicGeometry.Proj.basicOpen 𝒜 f)) :
    Scheme.Modules.Hom.app (chartPushforwardTwistMap 𝒜 ℬ ψ hψ hd hf n)
        (AlgebraicGeometry.Proj.basicOpen 𝒜 f) w =
      ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)).obj
            (twistingSheaf ℬ n)).presheaf.map
          (eqToHom (awayι_comp_map_preimage 𝒜 ℬ ψ hψ hd hf)).op
        (Scheme.Modules.Hom.app
          ((pullbackPushforwardAdjunction
              (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)).unit.app
            (twistingSheaf ℬ n))
            (AlgebraicGeometry.Proj.map ψ hψ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
          (Scheme.Modules.Hom.app (Stacks.ProjTwistComparison.pushforwardTwistMap ψ hψ n)
            (AlgebraicGeometry.Proj.basicOpen 𝒜 f) w)) :=
  rfl

/-- **The chart sections of the morphism the chart square's composite adjunction transposes.**
Read through the chart identification of the target, it is the explicit pointwise comparison on
sections over `D₊(f)`, everything else collapsing by
`Stacks.AlgebraicGeometry.TwistChartLocality.collapse_unit_apply`. -/
public theorem chartΓIso_chartPushforwardTwistMap
    (x : Γ(twistingSheaf 𝒜 n, AlgebraicGeometry.Proj.basicOpen 𝒜 f)) :
    (chartΓIso ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) hd).hom
        (((pushforward (Spec.map (CommRingCat.ofHom (Away.map ψ f)))).obj
              ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)).obj
                (twistingSheaf ℬ n))).presheaf.map
            (eqToHom (awayι_preimage_basicOpen_self 𝒜 hf hd).symm).op
          (Scheme.Modules.Hom.app (chartPushforwardTwistMap 𝒜 ℬ ψ hψ hd hf n)
            (AlgebraicGeometry.Proj.basicOpen 𝒜 f) x)) =
      associatedModuleSheafStandardOpenEquiv ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) hd
        (Scheme.Modules.Hom.app (Stacks.ProjTwistComparison.pushforwardTwistMap ψ hψ n)
          (AlgebraicGeometry.Proj.basicOpen 𝒜 f) x) := by
  refine Eq.trans (chartΓIso_hom_apply ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) hd _) ?_
  refine congrArg _ ?_
  exact collapse_unit_apply (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)
    (twistingSheaf ℬ n) (AlgebraicGeometry.Proj.basicOpen ℬ (ψ f))
    (awayι_image_top ℬ (ψ.map_mem hf) hd)
    ((Spec.map (CommRingCat.ofHom (Away.map ψ f)) ≫
        AlgebraicGeometry.Proj.awayι 𝒜 f hf hd) ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 f)
    (eqToHom (awayι_comp_map_preimage 𝒜 ℬ ψ hψ hd hf))
    (homOfLE (le_of_eq (comp_preimage_basicOpen_self 𝒜 ℬ ψ hd hf).symm))
    (Scheme.Modules.Hom.app (Stacks.ProjTwistComparison.pushforwardTwistMap ψ hψ n)
      (AlgebraicGeometry.Proj.basicOpen 𝒜 f) x)

/-- **The explicit pointwise comparison carries the section attached to an element of `𝒜(n)₍f₎` to
the section attached to its image.** This is
`Stacks.AlgebraicGeometry.TwistChartLocality.sectionsMap_degreeZeroToSection_val`, read as an
identity of sections rather than pointwise: the inverse image of `D₊(f)` along
`AlgebraicGeometry.Proj.map` *is* `D₊(ψ f)`, by `AlgebraicGeometry.Proj.map_preimage_basicOpen`,
so no transport of opens intervenes. -/
public theorem pushforwardTwistMap_degreeZeroToSection
    (z : GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 n) f) :
    Scheme.Modules.Hom.app (Stacks.ProjTwistComparison.pushforwardTwistMap ψ hψ n)
        (AlgebraicGeometry.Proj.basicOpen 𝒜 f)
        (degreeZeroToSection 𝒜 (twistGrading (S := A) 𝒜 n) f z) =
      degreeZeroToSection ℬ (twistGrading (S := B) ℬ n) (ψ f)
        (twistDegreeZeroMap 𝒜 ℬ ψ f n z) :=
  Subtype.ext (funext fun y => sectionsMap_degreeZeroToSection_val 𝒜 ℬ ψ hψ n z y y.2)

/-- **The explicit pointwise comparison is the algebraic map, in degree-zero coordinates.** -/
public theorem standardOpenEquiv_pushforwardTwistMap
    (x : (associatedModuleSheaf 𝒜 (twistGrading (S := A) 𝒜 n)).val.obj
      (.op (ProjectiveSpectrum.basicOpen 𝒜 f))) :
    associatedModuleSheafStandardOpenEquiv ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) hd
        (Scheme.Modules.Hom.app (Stacks.ProjTwistComparison.pushforwardTwistMap ψ hψ n)
          (AlgebraicGeometry.Proj.basicOpen 𝒜 f) x) =
      twistDegreeZeroMap 𝒜 ℬ ψ f n
        (associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading (S := A) 𝒜 n) hf hd x) := by
  obtain ⟨z, rfl⟩ := degreeZeroToSection_surjective 𝒜 (twistGrading (S := A) 𝒜 n) hf hd x
  rw [pushforwardTwistMap_degreeZeroToSection 𝒜 ℬ ψ hψ n z,
    associatedModuleSheafStandardOpenEquiv_degreeZeroToSection]
  exact associatedModuleSheafStandardOpenEquiv_degreeZeroToSection ℬ
    (twistGrading (S := B) ℬ n) (ψ.map_mem hf) hd _

/-- **THE Γ BRIDGE.** The global sections of
`Stacks.AlgebraicGeometry.TwistChartLocality.chartAdjointTwistMap`, read through the chart
identifications of its source and target, are the algebraic chart comparison
`Stacks.AlgebraicGeometry.TwistChartLocality.twistDegreeZeroMap`.

The transpose is taken along the chart of `Proj 𝒜`, so
`Stacks.AlgebraicGeometry.TwistChartLocality.restrictTranspose_app` computes its sections over the
whole chart spectrum as the sections of
`Stacks.AlgebraicGeometry.TwistChartLocality.chartPushforwardTwistMap` over `D₊(f)`; those are the
explicit pointwise comparison by
`Stacks.AlgebraicGeometry.TwistChartLocality.chartΓIso_chartPushforwardTwistMap`, and that is the
algebraic map by
`Stacks.AlgebraicGeometry.TwistChartLocality.standardOpenEquiv_pushforwardTwistMap`. -/
public theorem chartΓIso_moduleSpecΓ_chartAdjointTwistMap
    (y : (moduleSpecΓFunctor (R := CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).obj
      ((pullback (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)).obj (twistingSheaf 𝒜 n))) :
    (chartΓIso ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) hd).hom
        ((moduleSpecΓFunctor (R := CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).map
          (chartAdjointTwistMap 𝒜 ℬ ψ hψ hd hf n) y) =
      twistDegreeZeroMap 𝒜 ℬ ψ f n
        ((chartΓIso 𝒜 (twistGrading (S := A) 𝒜 n) hf hd).hom y) := by
  have hg := homEquiv_symm_eq_restrict (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)
    (twistingSheaf 𝒜 n)
    ((pushforward (Spec.map (CommRingCat.ofHom (Away.map ψ f)))).obj
      ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hd)).obj
        (twistingSheaf ℬ n)))
    (chartPushforwardTwistMap 𝒜 ℬ ψ hψ hd hf n)
  refine Eq.trans (congrArg (ConcreteCategory.hom
    (chartΓIso ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) hd).hom)
    (congrArg (fun m => ConcreteCategory.hom (Scheme.Modules.Hom.app m ⊤) y) hg)) ?_
  refine Eq.trans (congrArg (fun w => ConcreteCategory.hom
      (chartΓIso ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) hd).hom
      (ConcreteCategory.hom (Scheme.Modules.Hom.app
        (((restrictAdjunction (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)).homEquiv _ _).symm
          (chartPushforwardTwistMap 𝒜 ℬ ψ hψ hd hf n)) ⊤) w))
    (Iso.hom_inv_id_apply (imageSectionsIso (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd)
      (show (AlgebraicGeometry.Proj 𝒜).Modules from twistingSheaf 𝒜 n) ⊤
      (AlgebraicGeometry.Proj.basicOpen 𝒜 f) (awayι_image_top 𝒜 hf hd)) _).symm) ?_
  refine Eq.trans (congrArg (ConcreteCategory.hom
      (chartΓIso ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) hd).hom)
    (restrictTranspose_app (AlgebraicGeometry.Proj.awayι 𝒜 f hf hd) (twistingSheaf 𝒜 n) _
      (chartPushforwardTwistMap 𝒜 ℬ ψ hψ hd hf n) ⊤
      (AlgebraicGeometry.Proj.basicOpen 𝒜 f) (awayι_image_top 𝒜 hf hd)
      (awayι_preimage_basicOpen_self 𝒜 hf hd) _)) ?_
  refine Eq.trans (chartΓIso_chartPushforwardTwistMap 𝒜 ℬ ψ hψ hd hf n _) ?_
  refine Eq.trans (standardOpenEquiv_pushforwardTwistMap 𝒜 ℬ ψ hψ hd hf n _) ?_
  exact congrArg _ (chartΓIso_hom_apply 𝒜 (twistGrading (S := A) 𝒜 n) hf hd y).symm

end ChartTranspose

/-! ### The chart transpose is invertible, in degree one -/

section DegreeOne

universe v v'

variable {A B : Type u} {R : Type v} {R' : Type v'}
  [CommRing A] [CommRing B] [CommRing R] [CommRing R'] [Algebra R A] [Algebra R' B]
  (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R' B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  (ψ : 𝒜 →+*ᵍ ℬ) (hψ : ℬ₊ ≤ 𝒜₊.map ψ) {f : A} (hf : f ∈ 𝒜 1) (n : ℤ)

/-- The algebraic chart comparison as a semilinear map: a morphism into the restriction of
scalars of its target along the chart ring homomorphism, which is what
`CategoryTheory.Adjunction.homEquiv` of `ModuleCat.extendRestrictScalarsAdj` transposes. -/
public def twistDegreeZeroSemilinear :
    ModuleCat.of (Away 𝒜 f)
        (GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 n) f) ⟶
      (ModuleCat.restrictScalars (Away.map ψ f)).obj
        (ModuleCat.of (Away ℬ (ψ f))
          (GradedModuleDegreeZeroLocalization ℬ (twistGrading (S := B) ℬ n) (ψ f))) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (Away.map ψ f)).obj
      (ModuleCat.of (Away ℬ (ψ f))
        (GradedModuleDegreeZeroLocalization ℬ (twistGrading (S := B) ℬ n) (ψ f))))
    { toFun := twistDegreeZeroMap 𝒜 ℬ ψ f n
      map_add' := fun a b => map_add (twistDegreeZeroMap 𝒜 ℬ ψ f n) a b
      map_smul' := twistDegreeZeroMap_smul 𝒜 ℬ ψ f n }

/-- **The extension of scalars of the algebraic chart comparison**, the morphism of
`ModuleCat (ℬ₍ψ f₎)` out of `ℬ₍ψ f₎ ⊗_{𝒜₍f₎} 𝒜(n)₍f₎` that the affine invertibility criterion
consumes.

It is the inverse adjoint transpose of
`Stacks.AlgebraicGeometry.TwistChartLocality.twistDegreeZeroSemilinear`, written out as the
extension of scalars of that map followed by the counit rather than through
`CategoryTheory.Equiv.symm`: in that form its value on a pure tensor is `ModuleCat.map_tmul`,
which is a reflexivity, followed by
`ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul`. -/
public def twistDegreeZeroExtension :
    (ModuleCat.extendScalars (Away.map ψ f)).obj
        (ModuleCat.of (Away 𝒜 f)
          (GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 n) f)) ⟶
      ModuleCat.of (Away ℬ (ψ f))
        (GradedModuleDegreeZeroLocalization ℬ (twistGrading (S := B) ℬ n) (ψ f)) :=
  (ModuleCat.extendScalars (Away.map ψ f)).map (twistDegreeZeroSemilinear 𝒜 ℬ ψ n) ≫
    (ModuleCat.extendRestrictScalarsAdj (Away.map ψ f)).counit.app
      (ModuleCat.of (Away ℬ (ψ f))
        (GradedModuleDegreeZeroLocalization ℬ (twistGrading (S := B) ℬ n) (ψ f)))

/-- **The extension of scalars of the chart comparison, on a pure tensor.** -/
public theorem twistDegreeZeroExtension_tmul
    (z : GradedModuleDegreeZeroLocalization 𝒜 (twistGrading (S := A) 𝒜 n) f) :
    twistDegreeZeroExtension 𝒜 ℬ ψ n
        ((1 : Away ℬ (ψ f)) ⊗ₜ[Away 𝒜 f, Away.map ψ f] z) =
      twistDegreeZeroMap 𝒜 ℬ ψ f n z := by
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  exact ModuleCat.extendRestrictScalarsAdj_counit_app_apply_one_tmul (f := Away.map ψ f)
    (ModuleCat.of (Away ℬ (ψ f))
      (GradedModuleDegreeZeroLocalization ℬ (twistGrading (S := B) ℬ n) (ψ f)))
    (twistDegreeZeroMap 𝒜 ℬ ψ f n z)

/-- **The chart transpose of Tag 01MY's comparison map is invertible**, for `f` homogeneous of
degree one.

The affine criterion
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_transpose_of_isIso_extension` applies: both
chart modules are quasi-coherent by
`Stacks.AlgebraicGeometry.TwistChartLocality.isQuasicoherent_pullback_awayι_twistingSheaf`, their
global sections are the degree-zero localizations by
`Stacks.AlgebraicGeometry.TwistChartLocality.chartΓIso`, the global sections of the transpose are
the algebraic chart comparison by
`Stacks.AlgebraicGeometry.TwistChartLocality.chartΓIso_moduleSpecΓ_chartAdjointTwistMap`, and the
coefficient extension of that comparison is invertible in degree one by
`Stacks.AlgebraicGeometry.TwistChartDegreeOne.isIso_of_tmul_eq_twistDegreeZeroMap`. -/
public theorem isIso_transpose_chartAdjointTwistMap :
    IsIso (transpose (CommRingCat.ofHom (Away.map ψ f))
      ((pullback (AlgebraicGeometry.Proj.awayι 𝒜 f hf Nat.one_pos)).obj (twistingSheaf 𝒜 n))
      ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) Nat.one_pos)).obj
        (twistingSheaf ℬ n))
      (chartAdjointTwistMap 𝒜 ℬ ψ hψ Nat.one_pos hf n)) := by
  have := isQuasicoherent_pullback_awayι_twistingSheaf 𝒜 Nat.one_pos hf n
  have := isQuasicoherent_pullback_awayι_twistingSheaf ℬ Nat.one_pos (ψ.map_mem hf) n
  have : IsIso (twistDegreeZeroExtension 𝒜 ℬ ψ n) :=
    Stacks.AlgebraicGeometry.TwistChartDegreeOne.isIso_of_tmul_eq_twistDegreeZeroMap 𝒜 ℬ ψ hf n _
      (twistDegreeZeroExtension_tmul 𝒜 ℬ ψ n)
  refine isIso_transpose_of_isIso_extension _ _ _ _
    ((ModuleCat.extendScalars (Away.map ψ f)).map
        (chartΓIso 𝒜 (twistGrading (S := A) 𝒜 n) hf Nat.one_pos).hom ≫
      twistDegreeZeroExtension 𝒜 ℬ ψ n ≫
      (chartΓIso ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) Nat.one_pos).inv) ?_
  intro m
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ _) ?_
  refine Eq.trans (congrArg (ConcreteCategory.hom
      (chartΓIso ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) Nat.one_pos).inv)
    (twistDegreeZeroExtension_tmul 𝒜 ℬ ψ n _)) ?_
  refine Eq.trans (congrArg (ConcreteCategory.hom
      (chartΓIso ℬ (twistGrading (S := B) ℬ n) (ψ.map_mem hf) Nat.one_pos).inv)
    (chartΓIso_moduleSpecΓ_chartAdjointTwistMap 𝒜 ℬ ψ hψ Nat.one_pos hf n m).symm) ?_
  exact Iso.hom_inv_id_apply _ _

/-- **The chart inverse image of Tag 01MY's comparison map is invertible at a degree-one
element.** -/
public theorem isIso_pullback_awayι_map_twistMap :
    IsIso ((pullback (AlgebraicGeometry.Proj.awayι ℬ (ψ f) (ψ.map_mem hf) Nat.one_pos)).map
      (Stacks.ProjTwistComparison.twistMap ψ hψ n)) :=
  (isIso_pullback_awayι_map_twistMap_iff 𝒜 ℬ ψ hψ Nat.one_pos hf n).mpr
    (isIso_transpose_chartAdjointTwistMap 𝒜 ℬ ψ hψ hf n)

/-- **Tag 01MY's comparison map on the `n`-th twist is an isomorphism**, whenever the images of
the degree-one part of `𝒜` generate the irrelevant ideal of `ℬ`.

`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_projTwistComparison_of_forall_pullback_awayι`
reduces this to the chart spectra of the images of the degree-one elements, where
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_pullback_awayι_map_twistMap` answers it. The
hypothesis is what makes those charts cover `Proj ℬ`; it cannot be dropped, because the
freeness of `𝒜(n)₍f₎` that the chart argument uses fails at a homogeneous `f` of higher degree —
see `StacksFrontier/AlgebraicGeometry/TwistChartLocality/DegreeOneFree.lean`. -/
@[ega "II 2.8.8" "special case"]
public theorem isIso_projTwistComparison
    (hone : (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤ Ideal.span (ψ '' (𝒜 1 : Set A))) :
    IsIso (Stacks.ProjTwistComparison.twistMap ψ hψ n) :=
  isIso_projTwistComparison_of_forall_pullback_awayι 𝒜 ℬ ψ hψ hone n
    fun _g hg => isIso_pullback_awayι_map_twistMap 𝒜 ℬ ψ hψ hg n

end DegreeOne

/-! ### The twist transport for the polynomial grading -/

section Poly

open Stacks.ProjectiveCohomology

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The twist transport for the polynomial grading and the coefficient map `ULift ℤ → S`.**
The inverse image along `Stacks.ProjectiveCohomology.projModelMap` of the integral twisting sheaf
is isomorphic to the twisting sheaf of `S[T₀, …, Tₙ]`, in every degree.

`Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport_of_forall_pullback_awayι`
reduces this to the inverse images of Tag 01MY's comparison map along the chart spectra of the
degree-one elements, and that is
`Stacks.AlgebraicGeometry.TwistChartLocality.isIso_pullback_awayι_map_twistMap`.

This is not clause (3) of [Stacks, Tag 01N2], which asks that the canonical comparison `θ` be an
isomorphism for a graded algebra over an arbitrary base change: it is specialized to the
polynomial grading and to the single coefficient map
`Stacks.ProjectiveCohomology.fromULiftInt`, and its conclusion
`Stacks.ProjectiveCohomology.HasPolyTwistTransport` records only that the two twisting sheaves
are isomorphic, not which morphism realizes that. The underlying degree-one chart statement does
invert the canonical comparison; the general statement is not proved. -/
public theorem hasPolyTwistTransport (S : Type u) [CommRing S] (m : ℕ) :
    HasPolyTwistTransport S m :=
  hasPolyTwistTransport_of_forall_pullback_awayι S m fun e _g hg =>
    isIso_pullback_awayι_map_twistMap (polyGrading (ULift.{u} ℤ) m) (polyGrading S m)
      (polyGradedMap (Fin (m + 1)) (fromULiftInt S))
      (irrelevant_le_map_polyGradedMap (Fin (m + 1)) (fromULiftInt S)) hg e

end Poly

end Stacks.AlgebraicGeometry.TwistChartLocality

end
