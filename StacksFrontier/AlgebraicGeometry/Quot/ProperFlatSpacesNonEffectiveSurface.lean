module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpacesEffectiveLineBundle
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSchemeDeformations
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpaceOfSchemeObstruction
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatUnobstructedVersalDeformation
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeSpacePicard
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.DivisorOfSection
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.InvertibleTensor
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SourceChernSetup
public import StacksFrontier.AlgebraicGeometry.Thickenings.LineBundleLiftDivisor
public import StacksFrontier.AlgebraicGeometry.AmpleLimit.Unconditional
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationKodairaSpencerRealization

/-!
# The universal deformation of a surface with trivial canonical bundle is not effective

This file contains the argument of [Stacks, Section 0D1Q] (the discussion before Stacks 0D1R):
the versal formal deformation of a smooth projective surface `X` over a field of characteristic
zero with `H¹(X, 𝒪_X) = 0` and `ω_X ≅ 𝒪_X` (a K3 surface) is not effective as a formal object of
the stack `p'_{fp, flat, proper}`.

Suppose it were, with algebraization `Y`. Then `Y` carries a nontrivial line bundle `𝒪_Y(D)`
(the complement of an affine open), whose restriction `L₀` to `X` is nontrivial (because
`H¹(X, 𝒪_X) = 0`) and has a nonzero section, so `L₀ ≅ 𝒪_X(D₀)` for a nonempty effective
Cartier divisor `D₀ ⊂ X`. The line bundle `𝒪_Y(D)` restricts to every infinitesimal deformation
of `X`, hence `𝒪_X(D₀)` extends along every first-order deformation of `X`. But its Hodge first
Chern class is nonzero, and by Serre duality its cup product with the Kodaira–Spencer class of a
suitable first-order deformation is nonzero, which is the obstruction to extending it.

## Main results

* `AlgebraicGeometry.ProperFlatSpaceOfScheme.not_isEffective_ofPredeformation_of_surface`:
  the formal object of `p'_{fp, flat, proper}` given by a versal formal deformation of such a
  surface is not effective.
* `AlgebraicGeometry.ProperFlatSpaceOfScheme.exists_not_isEffective_of_surface`: such a surface
  gives a non-effective formal object of `p'_{fp, flat, proper}` over `Spec k`.

## References

* [Stacks Project, Section 0D1Q](https://stacks.math.columbia.edu/tag/0D1Q)
* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Deformation Deformation.Artin


universe u

namespace AlgebraicGeometry.ProperFlatSpaceOfScheme

attribute [local instance] PredeformationConstruction.category

variable (B : BigFppfSite.{u}) (k : Type u) [Field k] (hk : B.Contains (Spec (.of k)))
  {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A nonzero morphism `𝒪_X ⟶ ℒ` has a nonzero global section. -/
theorem eval_top_unitHomEquiv_ne_zero {ℒ : X.Modules}
    (t : @id X.Modules (SheafOfModules.unit X.ringCatSheaf) ⟶ ℒ) (ht : t ≠ 0) :
    (ℒ.unitHomEquiv t).eval (Opposite.op ⊤) ≠ 0 := by
  intro h
  apply ht
  apply ℒ.unitHomEquiv.injective
  exact Stacks.AlgebraicGeometry.ModuleLimits.sections_ext_top _ _ (h.trans rfl)


section KodairaSpencer

open Stacks.Thickenings.LineBundleLift (conormalModule kodairaSpencerClassOf)

/-- Transporting a Kodaira–Spencer class along `𝒞 ≅ 𝒪_X` and then `𝒪_X ≅ ω_X`: if the class
read through `ψ : 𝒞_{X/X'} ≅ 𝒪_X` is `α ∘ σ` for `σ : ω_X ≅ 𝒪_X`, then the class read through
`ψ ≪≫ σ⁻¹ : 𝒞_{X/X'} ≅ ω_X` is `α`. -/
theorem kodairaSpencerClassOf_comp_trans_symm {X' : Scheme.{u}} (i : X ⟶ X') [IsImmersion i]
    (q : X' ⟶ Spec (.of k)) [IsProper f] [Smooth f] (hq : i ≫ q = f)
    (ψ : conormalModule i ≅ SheafOfModules.unit X.ringCatSheaf)
    (σ : Stacks.Duality.dualizingModule f ≅ SheafOfModules.unit X.ringCatSheaf)
    (α : Ext.{u} (Scheme.Hom.relativeDifferentials f) (Stacks.Duality.dualizingModule f) 1)
    (h : (kodairaSpencerClassOf f i q hq).comp (Ext.mk₀ ψ.hom) (add_zero 1) =
      α.comp (Ext.mk₀ σ.hom) (add_zero 1)) :
    (kodairaSpencerClassOf f i q hq).comp (Ext.mk₀ (ψ ≪≫ σ.symm).hom) (add_zero 1) = α := by
  have e₁ : Ext.mk₀ (ψ ≪≫ σ.symm).hom = (Ext.mk₀ ψ.hom).comp (Ext.mk₀ σ.inv) (zero_add 0) :=
    (Ext.mk₀_comp_mk₀ _ _).symm
  have e₂ : (Ext.mk₀ σ.hom).comp (Ext.mk₀ σ.inv) (zero_add 0) = Ext.mk₀ (𝟙 _) :=
    (Ext.mk₀_comp_mk₀ _ _).trans (congrArg Ext.mk₀ σ.hom_inv_id)
  refine (congrArg (fun z => (kodairaSpencerClassOf f i q hq).comp z (add_zero 1)) e₁).trans ?_
  refine (Ext.comp_assoc _ _ _ (add_zero 1) (add_zero 0) (by omega)).symm.trans ?_
  refine (congrArg (fun z => z.comp (Ext.mk₀ σ.inv) (add_zero 1)) h).trans ?_
  refine (Ext.comp_assoc _ _ _ (add_zero 1) (add_zero 0) (by omega)).trans ?_
  exact (congrArg (fun z => α.comp z (add_zero 1)) e₂).trans (Ext.comp_mk₀_id α)

end KodairaSpencer

section NotEffective

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-- **The versal deformation of a K3-type surface is not effective** ([Stacks, Section 0D1Q]).
Let `k` have characteristic zero and let `f : X ⟶ Spec k` be smooth and projective of relative
dimension `2`, with `X` integral, equidimensional of dimension `2`, `H¹(X, 𝒪_X) = 0` and
`ω_X ≅ 𝒪_X`. Let `η` be a versal formal object, over a power series ring `k[[x_1, …, x_n]]`, of
the predeformation category of the point `[X]` of `p'_{fp, flat, proper}`. Then the formal object
of `p'_{fp, flat, proper}` given by `η` is not effective. -/
theorem not_isEffective_ofPredeformation_of_surface [CharZero k] [IsProper f] [Smooth f]
    [SmoothOfRelativeDimension 2 f] [IsIntegral X] (hproj : IsProjective f)
    (hrel : AlgebraicGeometry.RelativeDimension f 2)
    (hequi : TopologicalSpace.Equidimensional X) (hd : topologicalKrullDim X = (2 : ℕ))
    (hH1 : IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
      (SheafOfModules.unit _)))
    (hω : Nonempty (Stacks.Duality.dualizingModule f ≅ SheafOfModules.unit X.ringCatSheaf))
    (hfinite : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫
        𝟙 (Spec (.of k))) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ 𝟙 (Spec (.of k))))
    (η : Deformation.FormalObject (ProperFlatSpaceDeformation.predeformationCat B (Spec (.of k)) hk
      (𝟙 _) (point B k hk f) (projection_point B k hk f)).projection)
    (hR : ∃ n : ℕ, Nonempty (η.base ≃ₐ[k] MvPowerSeries (Fin n) k))
    (hη : IsVersal (ProperFlatSpaceDeformation.isDeformationCategory_predeformationCat B
      (Spec (.of k)) hk (𝟙 _) (point B k hk f) (projection_point B k hk f)
        hfinite).predeformation.cofibered η) :
    ¬ Deformation.Artin.FormalObject.IsEffective B (Spec (.of k)) hk
      (cartesianProperFlatProjection B (Spec (.of k)) hk)
      (cartesianProperFlatProjection_isFiberedInGroupoids B (Spec (.of k)) hk)
      (FormalObject.ofPredeformation B (Spec (.of k)) hk (𝟙 _)
        (cartesianProperFlatProjection B (Spec (.of k)) hk) (point B k hk f)
        (projection_point B k hk f) hfinite η) := by
  intro hξ
  have : IsIntegral ((BigFppfOver.toScheme B (Spec (.of k)) hk).obj (siteObj B k hk f)) :=
    ‹IsIntegral X›
  obtain ⟨𝒴, L, hL, g₀, hnt, ⟨s, hs⟩, hext⟩ :=
    exists_invertibleModule_of_isEffective B k hk f hH1 hfinite η hR hη hξ
  have hM := Space.modulePullbackInvertible g₀ L hL
  obtain ⟨ℒ, hℒ, hcℒ, t, ht⟩ :=
    Space.exists_picardClassOf_eq_picardGroupSchemeSpaceEquiv_of_ne_zero (siteObj B k hk f) _
      hM s hs
  have hntℒ : ¬ Nonempty (ℒ ≅ SheafOfModules.unit _) := by
    rintro ⟨e⟩
    apply hnt
    refine (Space.picardGroupSchemeSpaceEquiv_picardClass_eq_zero_iff _ _ hM).1 ?_
    rw [← hcℒ]
    exact (Stacks.WeilCohomology.picardClassOf_eq_of_iso _ _ _ hℒ
      (AlgebraicGeometry.SheafOfModules.isInvertible_unit _ _) e).trans
      (Stacks.WeilCohomology.picardClassOf_unit _)
  obtain ⟨D, hD, hDne, hDc⟩ := Stacks.Divisors.exists_isEffectiveCartierDivisor_picardClassOf_eq
    ℒ hℒ _ (eval_top_unitHomEquiv_ne_zero t ht) hntℒ
  have : Stacks.Divisors.IsEffectiveCartierDivisor (X := X) D := hD
  obtain ⟨α, hα⟩ := Stacks.Thickenings.LineBundleLift.not_extends_of_isEffectiveCartierDivisor
    f hproj hrel hequi hd D hDne _ hDc.symm
  obtain ⟨σ⟩ := hω
  obtain ⟨P, -, q, hq, ψ, hKS⟩ :=
    Deformation.Examples.exists_schemeDeformation_kodairaSpencerClass_eq f
      (α.comp (Ext.mk₀ σ.hom) (add_zero 1))
  obtain ⟨g, hg⟩ := hext (toDeformationObject B k hk f P)
  let g' : schemeSpace (siteObjOfDeformation B k hk f P) ⟶ 𝒴 := g
  have hsp : schemeSpaceMap (specialSiteHom B k hk f P) ≫ g' = g₀ := hg
  refine hα P.specialMap q hq (ψ ≪≫ σ.symm) ?_
    (Space.picardGroupSchemeSpaceEquiv (siteObjOfDeformation B k hk f P)
      (Space.picardPullback g' (Space.picardClass 𝒴 L hL))) ?_
  · exact kodairaSpencerClassOf_comp_trans_symm k f P.specialMap q hq ψ σ α hKS
  · rw [hcℒ, ← toScheme_map_specialSiteHom B k hk f P,
      ← Space.picardGroupSchemeSpaceEquiv_picardPullback, ← Space.picardPullback_comp, hsp,
      Space.picardPullback_picardClass]

/-- The structure morphism `Spec (k → k) ≫ 𝟙` of `Spec k` over itself is of finite type and
quasi-compact (it is the identity). -/
theorem locallyOfFiniteType_and_quasiCompact_specMap_algebraMap_self :
    LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ 𝟙 (Spec (.of k))) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ 𝟙 (Spec (.of k))) := by
  rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  exact ⟨inferInstance, inferInstance⟩

/-- **A K3-type surface gives a non-effective formal object of `p'_{fp, flat, proper}`**
([Stacks, Section 0D1Q]). Let `k` have characteristic zero and let `f : X ⟶ Spec k` be smooth
and projective of relative dimension `2`, with `X` integral and equidimensional of dimension
`2`, `H¹(X, 𝒪_X) = 0`, `ω_X ≅ 𝒪_X` and `Ext²(Ω_{X/k}, 𝒪_X) = H²(X, T_X) = 0`. Then the stack
`p'_{fp, flat, proper}` over `Spec k` has a formal object which is not effective: the image of
the versal formal deformation of `X` over `k[[x_1, …, x_n]]`. -/
theorem exists_not_isEffective_of_surface [CharZero k] [IsProper f] [Smooth f]
    [SmoothOfRelativeDimension 2 f] [IsIntegral X] (hproj : IsProjective f)
    (hrel : AlgebraicGeometry.RelativeDimension f 2)
    (hequi : TopologicalSpace.Equidimensional X) (hd : topologicalKrullDim X = (2 : ℕ))
    (hH1 : IsZero (((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)).rightDerived 1).obj
      (SheafOfModules.unit _)))
    (hω : Nonempty (Stacks.Duality.dualizingModule f ≅ SheafOfModules.unit X.ringCatSheaf))
    (hT : Subsingleton (Ext.{u} (Scheme.Hom.relativeDifferentials f)
      (SheafOfModules.unit X.ringCatSheaf) 2)) :
    ∃ ξ : Deformation.Artin.FormalObject B (Spec (.of k)) hk
        (cartesianProperFlatProjection B (Spec (.of k)) hk),
      ¬ Deformation.Artin.FormalObject.IsEffective B (Spec (.of k)) hk
        (cartesianProperFlatProjection B (Spec (.of k)) hk)
        (cartesianProperFlatProjection_isFiberedInGroupoids B (Spec (.of k)) hk) ξ := by
  have hfinite := locallyOfFiniteType_and_quasiCompact_specMap_algebraMap_self k
  letI := HasDerivedCategory.standard (Space.modelModules (point B k hk f).obj.obj.left)
  obtain ⟨ξ, η, n, rfl, ⟨e⟩, hmin, -⟩ :=
    ProperFlatSpaceDeformation.exists_formalObject_powerSeries_of_subsingleton_cotangentExtTwo
      B (Spec (.of k)) hk (𝟙 _) (point B k hk f) (projection_point B k hk f) hfinite
      (Deformation.isClassical_self k) (subsingleton_cotangentExtTwo_point B k hk f hT)
  exact ⟨_, not_isEffective_ofPredeformation_of_surface B k hk f hproj hrel hequi hd hH1 hω
    hfinite η ⟨n, ⟨e⟩⟩ hmin.1⟩

end NotEffective

end AlgebraicGeometry.ProperFlatSpaceOfScheme

end
