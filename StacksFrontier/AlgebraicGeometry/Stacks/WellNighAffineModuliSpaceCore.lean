module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.InvariantSpectrumQuotientInSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.QuotientStackModuliSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffineGroupoidPresentation

/-!
# The quotient stack of an affine finite locally free groupoid is a categorical moduli space

Let `G = (U, R, s, t, c)` be a groupoid scheme over `S` with `U` and `R` affine and `s, t` finite
locally free, whose object scheme, arrow scheme and invariant spectrum `M = Spec C` lie in the big
fppf site, and let `𝒳` be a category fibred in groupoids equivalent over the site to the quotient
stack `[U/R]`. This file shows that a 1-morphism `f : 𝒳 ⟶ N` to an algebraic space which is a
categorical moduli space in the category of affine algebraic spaces is a categorical moduli space
(`AlgebraicGeometry.Stack.isCategoricalModuliSpace_of_presentation`). This is the core of
**Stacks 0DUR**, the reduction of the uniform statement to it being Stacks 0DUJ.

The argument passes from `𝒳` to `[U/R]` along the equivalence, from `[U/R]` to `R`-invariant
morphisms out of `U` by Stacks 0DUH, identifies `N` with `M` because both are categorical
quotients of `U` among affine algebraic spaces, and concludes by the categorical quotient property
of `U ⟶ M` in all algebraic spaces
(`AlgebraicGeometry.Space.existsUnique_comp_quotientSite`).

## Main results

* `AlgebraicGeometry.Stack.isCategoricalModuliSpace_of_comp_equivalenceOver` and
  `AlgebraicGeometry.Stack.isBasedCategoricalModuliSpaceIn_comp_equivalenceOver`: the two
  universal properties transported along an equivalence over the site.
* `AlgebraicGeometry.Stack.isBasedCategoricalModuliSpace_quotientStack`: the quotient stack.
* `AlgebraicGeometry.Stack.isCategoricalModuliSpace_of_presentation`: a stack presented by `G`.

## References

* [Stacks Project, Tag 0DUR](https://stacks.math.columbia.edu/tag/0DUR)
* [Stacks Project, Tag 0DUH](https://stacks.math.columbia.edu/tag/0DUH)
-/

universe u

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids Stacks.Morphisms
open AlgebraicGeometry.GroupoidScheme

noncomputable section

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Transport along an equivalence over the site -/

section Transfer

variable {𝒜 𝒵 : BasedCategory (BigFppfOver B S hS)}
  (E : StacksRepresentableCFG.EquivalenceOver 𝒜.p 𝒵.p)

/-- The forward 1-morphism of an equivalence over the site, as a 1-morphism of based categories. -/
def equivalenceOverHom : 𝒜 ⥤ᵇ 𝒵 := { toFunctor := E.hom.functor, w := E.hom.w }

/-- The backward 1-morphism of an equivalence over the site, as a 1-morphism of based
categories. -/
def equivalenceOverInv : 𝒵 ⥤ᵇ 𝒜 := { toFunctor := E.inv.functor, w := E.inv.w }

/-- The counit of an equivalence over the site, as a based natural transformation. -/
def equivalenceOverCounit :
    BasedNatTrans (BasedFunctor.comp (equivalenceOverInv E) (equivalenceOverHom E))
      (BasedFunctor.id 𝒵) where
  toNatTrans := E.counitIso.hom
  isHomLift' t := E.isHomLift_counitIso_hom_app t

/-- The unit of an equivalence over the site, as a based natural transformation. -/
def equivalenceOverUnit :
    BasedNatTrans (BasedFunctor.id 𝒜)
      (BasedFunctor.comp (equivalenceOverHom E) (equivalenceOverInv E)) where
  toNatTrans := E.unitIso.hom
  isHomLift' a := E.isHomLift_unitIso_hom_app a

/-- A 1-morphism into the category attached to a presheaf is recovered from its composite with
the forward 1-morphism of an equivalence. -/
theorem comp_equivalenceOverInv_comp {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (k : 𝒵 ⥤ᵇ (fibredCategory B S hS W).val) :
    BasedFunctor.comp (equivalenceOverInv E) (BasedFunctor.comp (equivalenceOverHom E) k) = k :=
  comp_eq_of_basedNatTrans (equivalenceOverCounit E) k

/-- A 1-morphism out of `𝒜` into the category attached to a presheaf is recovered from its
composite with the backward 1-morphism of an equivalence. -/
theorem comp_equivalenceOverHom_comp {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (k : 𝒜 ⥤ᵇ (fibredCategory B S hS W).val) :
    BasedFunctor.comp (equivalenceOverHom E) (BasedFunctor.comp (equivalenceOverInv E) k) = k :=
  (comp_eq_of_basedNatTrans (equivalenceOverUnit E) k).symm

/-- **Being a categorical moduli space transports along an equivalence over the site.** -/
theorem isCategoricalModuliSpace_of_comp_equivalenceOver
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {𝒜 : BasedCategory (BigFppfOver B S hS)}
    (E : StacksRepresentableCFG.EquivalenceOver 𝒜.p 𝒳.val.p) (N : AlgebraicSpaces B S hS)
    (f : 𝒳 ⟶ fibredCategory B S hS N.obj)
    (h : IsBasedCategoricalModuliSpace N (BasedFunctor.comp (equivalenceOverHom E) f.hom)) :
    IsCategoricalModuliSpace B S hS N f := by
  rw [isCategoricalModuliSpace_iff_forall_basedFunctor]
  intro W k
  obtain ⟨h₀, hh₀, hu⟩ := h W (BasedFunctor.comp (equivalenceOverHom E) k)
  refine ⟨h₀, ?_, fun h₁ hh₁ => hu h₁ ?_⟩
  · exact (comp_equivalenceOverInv_comp E _).symm.trans
      ((congrArg (BasedFunctor.comp (equivalenceOverInv E)) hh₀).trans
        (comp_equivalenceOverInv_comp E k))
  · exact congrArg (BasedFunctor.comp (equivalenceOverHom E)) hh₁

/-- **Being a categorical moduli space in a full subcategory transports along an equivalence over
the site**, in the other direction. -/
theorem isBasedCategoricalModuliSpaceIn_comp_equivalenceOver
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {𝒜 : BasedCategory (BigFppfOver B S hS)}
    (E : StacksRepresentableCFG.EquivalenceOver 𝒜.p 𝒳.val.p) (P : AlgebraicSpaces B S hS → Prop)
    (N : AlgebraicSpaces B S hS) (f : 𝒳 ⟶ fibredCategory B S hS N.obj)
    (h : IsCategoricalModuliSpaceIn B S hS P N f) :
    IsBasedCategoricalModuliSpaceIn P N (BasedFunctor.comp (equivalenceOverHom E) f.hom) := by
  rw [isCategoricalModuliSpaceIn_iff_forall_basedFunctor] at h
  refine ⟨h.1, fun W hW k => ?_⟩
  obtain ⟨h₀, hh₀, hu⟩ := h.2 W hW (BasedFunctor.comp (equivalenceOverInv E) k)
  refine ⟨h₀, ?_, fun h₁ hh₁ => hu h₁ ?_⟩
  · exact (congrArg (BasedFunctor.comp (equivalenceOverHom E)) hh₀).trans
      (comp_equivalenceOverHom_comp E k)
  · exact (comp_equivalenceOverInv_comp E _).symm.trans
      (congrArg (BasedFunctor.comp (equivalenceOverInv E)) hh₁)

end Transfer

/-! ### The quotient stack -/

section QuotientStack

open Space

variable (G : GroupoidScheme S) [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
  (hU : B.Contains G.objects.left) (hR : B.Contains G.arrows.left)
  (σ : Spec (.of (invariantRing G)) ⟶ S) (hσ : objectsToInvariantSpectrum G ≫ σ = G.objects.hom)
  (hM : B.Contains (Spec (.of (invariantRing G))))
  (c : Deformation.composableArrows (yoneda.obj (schemeSiteObject B hS hU))
    (yoneda.obj (schemeSiteObject B hS hR)) (yoneda.map (sourceSite hS G hU hR))
    (yoneda.map (targetSite hS G hU hR)) ⟶ yoneda.obj (schemeSiteObject B hS hR))
  (hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid ((yoneda.map (sourceSite hS G hU hR)).app T)
    ((yoneda.map (targetSite hS G hU hR)).app T) fun p => c.app T p))

/-- The groupoid in algebraic spaces represented by `G` on the site. -/
abbrev siteGroupoid : GroupoidInAlgebraicSpaces B S hS (Space.terminalSpace B S hS) :=
  representedGroupoid B S hS (sourceSite hS G hU hR) (targetSite hS G hU hR) c hG

omit [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsFiniteLocallyFree (Over.Hom.left G.source)] [IsFiniteLocallyFree (Over.Hom.left G.target)] in
/-- Invariance under the represented groupoid of a morphism out of `U`. -/
theorem isInvariant_siteGroupoid_iff {W : AlgebraicSpaces B S hS}
    (ψ : (siteGroupoid G hU hR c hG).objects ⟶ W) :
    Space.IsInvariant (Space.groupoidPreRelation (siteGroupoid G hU hR c hG)) ψ.hom ↔
      yoneda.map (sourceSite hS G hU hR) ≫ ψ.hom = yoneda.map (targetSite hS G hU hR) ≫ ψ.hom := by
  rw [isInvariant_iff]
  exact ⟨fun h => (congrArg (fun g => g.hom) h).symm,
    fun h => ObjectProperty.hom_ext _ h.symm⟩

include hσ hM in
/-- **The quotient stack of `G` is a categorical moduli space as soon as it is one among affine
algebraic spaces.** -/
theorem isBasedCategoricalModuliSpace_quotientStack (N : AlgebraicSpaces B S hS)
    (F : quotientStack (siteGroupoid G hU hR c hG) ⥤ᵇ (fibredCategory B S hS N.obj).val)
    (hF : IsBasedCategoricalModuliSpaceIn (fun W => Space.IsAffineSpace B S hS W.obj) N F) :
    IsBasedCategoricalModuliSpace N F := by
  classical
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (invariantSpectrumSite hS G σ hM)) :=
    (inferInstance : IsAffine (Spec (.of (invariantRing G))))
  let Mspace : AlgebraicSpaces B S hS :=
    ⟨yoneda.obj (invariantSpectrumSite hS G σ hM), isAlgebraicSpace_yoneda B S hS _⟩
  let φM : (siteGroupoid G hU hR c hG).objects ⟶ Mspace :=
    ObjectProperty.homMk (yoneda.map (quotientSite hS G hU σ hσ hM))
  have hφN := (isInvariant_siteGroupoid_iff G hU hR c hG _).1
    (restrictedMorphism_isInvariant (siteGroupoid G hU hR c hG) F)
  -- the factorizations through `N` against affine algebraic spaces
  have hNaff : ∀ (W : AlgebraicSpaces B S hS), Space.IsAffineSpace B S hS W.obj →
      ∀ ψ : (siteGroupoid G hU hR c hG).objects ⟶ W,
        yoneda.map (sourceSite hS G hU hR) ≫ ψ.hom = yoneda.map (targetSite hS G hU hR) ≫ ψ.hom →
        ∃! h : N ⟶ W, restrictedMorphism (siteGroupoid G hU hR c hG) F ≫ h = ψ := by
    intro W hW ψ hψ
    obtain ⟨k, hk⟩ := exists_restrictedMorphism_eq (siteGroupoid G hU hR c hG) ψ
      ((isInvariant_siteGroupoid_iff G hU hR c hG ψ).2 hψ)
    obtain ⟨h₀, hh₀, hu⟩ := hF.2 W hW k
    refine ⟨h₀, ?_, fun h₁ hh₁ => hu h₁ (restrictedMorphism_injective _ _ _ ?_)⟩
    · exact (restrictedMorphism_comp_associatedMap _ F h₀).symm.trans
        ((congrArg (restrictedMorphism _) hh₀).trans hk)
    · exact (restrictedMorphism_comp_associatedMap _ F h₁).trans (hh₁.trans hk.symm)
  obtain ⟨α, hα, -⟩ := hNaff Mspace (Space.isAffineSpace_yoneda B S hS _ inferInstance) φM
    (quotientSite_invariant hS hU hR σ hσ hM)
  obtain ⟨β, hβ, -⟩ := existsUnique_comp_quotientSite hS hU hR σ hσ hM N.property
    (restrictedMorphism (siteGroupoid G hU hR c hG) F).hom hφN
  have hcomp : ∀ {W : AlgebraicSpaces B S hS} (g : Mspace ⟶ W)
      (ρ : (siteGroupoid G hU hR c hG).objects ⟶ W),
      yoneda.map (quotientSite hS G hU σ hσ hM) ≫ g.hom = ρ.hom →
        restrictedMorphism (siteGroupoid G hU hR c hG) F ≫ (α ≫ g) = ρ := fun g ρ h => by
    rw [← Category.assoc, hα]
    exact ObjectProperty.hom_ext _ h
  have hαβ : α ≫ (ObjectProperty.homMk β : Mspace ⟶ N) = 𝟙 N := by
    obtain ⟨h₀, -, hu⟩ := hNaff N hF.1 (restrictedMorphism _ F) hφN
    exact (hu _ (hcomp _ _ hβ)).trans (hu _ (Category.comp_id _)).symm
  intro W k
  have hψ := (isInvariant_siteGroupoid_iff G hU hR c hG _).1
    (restrictedMorphism_isInvariant (siteGroupoid G hU hR c hG) k)
  obtain ⟨h', hh', hu'⟩ := existsUnique_comp_quotientSite hS hU hR σ hσ hM W.property
    (restrictedMorphism (siteGroupoid G hU hR c hG) k).hom hψ
  refine ⟨α ≫ (ObjectProperty.homMk h' : Mspace ⟶ W),
    restrictedMorphism_injective _ _ _ ?_, fun h₂ hh₂ => ?_⟩
  · exact (restrictedMorphism_comp_associatedMap _ F _).trans (hcomp _ _ hh')
  · have h₂' : restrictedMorphism (siteGroupoid G hU hR c hG) F ≫ h₂ =
        restrictedMorphism (siteGroupoid G hU hR c hG) k :=
      (restrictedMorphism_comp_associatedMap _ F h₂).symm.trans
        (congrArg (restrictedMorphism _) hh₂)
    have hβh₂ : β ≫ h₂.hom = h' :=
      hu' _ ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ h₂.hom) hβ).trans
        (congrArg (fun g => g.hom) h₂')))
    calc h₂ = (α ≫ (ObjectProperty.homMk β : Mspace ⟶ N)) ≫ h₂ := by rw [hαβ, Category.id_comp]
      _ = α ≫ (ObjectProperty.homMk h' : Mspace ⟶ W) :=
          (Category.assoc _ _ _).trans (congrArg (α ≫ ·) (ObjectProperty.hom_ext _ hβh₂))

include hσ hM in
/-- **A stack presented by `G` is a categorical moduli space as soon as it is one among affine
algebraic spaces.** -/
theorem isCategoricalModuliSpace_of_presentation
    {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (E : StacksRepresentableCFG.EquivalenceOver
      (quotientStack (siteGroupoid G hU hR c hG)).p 𝒳.val.p)
    (N : AlgebraicSpaces B S hS) (f : 𝒳 ⟶ fibredCategory B S hS N.obj)
    (hf : IsCategoricalModuliSpaceIn B S hS (fun W => Space.IsAffineSpace B S hS W.obj) N f) :
    IsCategoricalModuliSpace B S hS N f :=
  isCategoricalModuliSpace_of_comp_equivalenceOver E N f
    (isBasedCategoricalModuliSpace_quotientStack G hU hR σ hσ hM c hG N _
      (isBasedCategoricalModuliSpaceIn_comp_equivalenceOver E _ N f hf))

end QuotientStack

end AlgebraicGeometry.Stack

end

end
