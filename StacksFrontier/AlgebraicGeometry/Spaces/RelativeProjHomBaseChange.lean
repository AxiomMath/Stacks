module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjFunctoriality
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjQuadruplesBaseChangeProj
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.RelativeProjCongrChart

/-!
# The data of Tag 07ZG at the scheme points of the base are compatible with base change

Let `ρ_A` and `ρ_B` be restriction data of Stacks 084A for two families `T ↦ A_T`, `T ↦ B_T` of
quasi-coherent graded algebras on the scheme points of an algebraic space `X`, and let `α` be a
family of homomorphisms `α_T : A_T ⟶ B_T` commuting with the restriction isomorphisms
`(f ∘ τ)^*A ≅ τ^*(f^*A)` of the two data. Write `P` and `Q` for the functors of quadruples of
Stacks 084A, with their identifications `Proj_T(A_T) = T ×_X P` of Stacks 084B.

This file proves that the open `U(α_T)` and the morphism `r_{α_T}` of Tag 07ZG are compatible with
base change in the test object, through the comparisons of the third assertion of Stacks 084B:
the comparison `Proj_{T'}(B_{T'}) ⟶ Proj_T(B_T)` over `τ : T' ⟶ T` carries `U(α_{T'})` into the
inverse image of `U(α_T)` exactly, and intertwines `r_{α_{T'}}` with `r_{α_T}`. Read on points
this is the compatibility asked of `AlgebraicGeometry.Space.RelativeProjHomPoints`, which is
therefore constructed here from `α` alone:
`AlgebraicGeometry.Space.GradedAlgebraRestriction.homPoints`.

The proof is the one the canonicity of the identifications of Stacks 084B makes available: the
comparison is the identification `Proj_{T'}((f ∘ τ)^*A) ≅ Proj_{T'}(τ^*(f^*A))` induced by the
restriction datum followed by the base-change morphism of Tag 01O3
(`AlgebraicGeometry.Space.GradedAlgebraRestriction.toScheme_map_projComparison`), and Tag 07ZG is
compatible with both (`…RelativeProjQcohSheaf.relativeProjCongr_preimage_relativeMapDomain`,
`…Tag07ZGMorphism.baseChangeHom_preimage_relativeMapDomain` and their companions for the
morphism).

## Main results

* `AlgebraicGeometry.Space.GradedAlgebraRestriction.preimage_relativeMapDomain_projComparison`:
  the comparison over `τ` carries `U(α_{T'})` onto the inverse image of `U(α_T)`.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.relativeMapHom_comp_projComparison`: the
  comparisons intertwine `r_{α_{T'}}` and `r_{α_T}`.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.sectionOfPoint_eq_comp_projComparison`: the
  section of `Proj_T(B_T)` attached to a point of `Q` over `f ∘ τ` is the section of
  `Proj_{T'}(B_{T'})` attached to it followed by the comparison.
* `AlgebraicGeometry.Space.GradedAlgebraRestriction.homPoints`: the map of graded algebras read
  over the scheme points of the base, with both compatibility conditions proved.

## References

* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 07ZG](https://stacks.math.columbia.edu/tag/07ZG)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjMapDomain
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist
open Stacks.AlgebraicGeometry.Tag07ZGMorphism

universe u

/-! ### Tag 07ZG along a restriction isomorphism followed by a base change -/

namespace Stacks.AlgebraicGeometry.Tag07ZGMorphism

variable {S S' : Scheme.{u}} {A B : SheafGradedAlgebra S} {A₁ B₁ : SheafGradedAlgebra S'}
  (g : S' ⟶ S)
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A₁)
    (situationAlgebra (A.pullback g)))
  (hΦ : ∀ n : ℤ, IsIso (Φ.app n))
  (Φ' : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra B₁)
    (situationAlgebra (B.pullback g)))
  (hΦ' : ∀ n : ℤ, IsIso (Φ'.app n))
  (ψ : SheafGradedAlgebraHom A B) (ψ₁ : SheafGradedAlgebraHom A₁ B₁)
  (hsq : ∀ n : ℤ, ψ₁.toSituationHom.app n ≫ Φ'.app n =
    Φ.app n ≫ (ψ.pullback g).toSituationHom.app n)

include hΦ hsq

/-- **The open of Tag 07ZG along an isomorphism onto a base change followed by the base-change
morphism.** -/
theorem relativeProjCongr_baseChangeHom_preimage_relativeMapDomain :
    ((relativeProjCongr Φ' hΦ').hom ≫ baseChangeHom B g) ⁻¹ᵁ ψ.relativeMapDomain =
      ψ₁.relativeMapDomain := by
  rw [Scheme.Hom.comp_preimage, baseChangeHom_preimage_relativeMapDomain ψ g,
    relativeProjCongr_preimage_relativeMapDomain Φ hΦ Φ' hΦ' ψ₁ (ψ.pullback g) hsq]

/-- **The morphism of Tag 07ZG along an isomorphism onto a base change followed by the
base-change morphism.** -/
theorem relativeMapHom_comp_relativeProjCongr_baseChangeHom :
    relativeMapHom ψ₁ ≫ (relativeProjCongr Φ hΦ).hom ≫ baseChangeHom A g =
      ((relativeProjCongr Φ' hΦ').hom ≫ baseChangeHom B g).resLE ψ.relativeMapDomain
          ψ₁.relativeMapDomain
          (relativeProjCongr_baseChangeHom_preimage_relativeMapDomain g Φ hΦ Φ' hΦ' ψ ψ₁
            hsq).ge ≫ relativeMapHom ψ := by
  rw [reassoc_of% (relativeMapHom_comp_relativeProjCongr Φ hΦ Φ' hΦ' ψ₁ (ψ.pullback g) hsq),
    relativeMapHom_pullback_comp_baseChangeHom, Scheme.Hom.resLE_comp_resLE_assoc]

end Stacks.AlgebraicGeometry.Tag07ZGMorphism

namespace AlgebraicGeometry.Space

/-- **Factoring a composite through an open subscheme**: if `k` lands in `D'` and `c` carries `D'`
into `D`, the factorization of `k ≫ c` through `D` is the factorization of `k` through `D'`
followed by the restriction of `c`. -/
theorem liftToOpens_comp_resLE {Y Z Z' : Scheme.{u}} (k : Y ⟶ Z) (c : Z ⟶ Z') (D : Z'.Opens)
    (D' : Z.Opens) (hle : D' ≤ c ⁻¹ᵁ D) (h' : k ⁻¹ᵁ D' = ⊤) (h : (k ≫ c) ⁻¹ᵁ D = ⊤) :
    liftToOpens (k ≫ c) D h = liftToOpens k D' h' ≫ c.resLE D D' hle :=
  (liftToOpens_unique _ _ h _ (by
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι, ← Category.assoc, liftToOpens_comp_ι])).symm

namespace GradedAlgebraRestriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option synthInstance.maxHeartbeats 400000 in
-- discrete limits of presheaves on the big fppf site are not found within the default budget
/-- Products of presheaves on the big fppf site over `S` (instance search times out without this
shortcut). -/
private instance (priority := high) hasLimitsOfShape_discrete_relativeProjHomBaseChange
    (J : Type) : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-! ### The section attached to a point, over a restricted point of the base -/

section Section

variable {Â : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X) →
      SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T)}
    (ρ : GradedAlgebraRestriction (GradedAlgebraPoints.ofQuasicoherentFamily Â))
    (hc : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      B.Contains (relativeProj (Â T f)).scheme)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)

/-- **The section attached to a point, read over a restricted point of the base.** A point `u` of
the functor of quadruples over `f ∘ r` has a section of `Proj_T(f^*A)` over `r` and a section of
`Proj_{T'}((f ∘ r)^*A)` over the identity; the first is the second followed by the comparison
morphism of the third assertion of Stacks 084B. -/
theorem sectionOfPoint_eq_comp_projComparison (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u : yoneda.obj T' ⟶ ρ.quadrupleSpace hc hX)
    (hu : u ≫ ρ.quadrupleSpaceπ hc hX = yoneda.map r ≫ f)
    (hu' : u ≫ ρ.quadrupleSpaceπ hc hX = yoneda.map (𝟙 T') ≫ (yoneda.map r ≫ f)) :
    (ρ.quadrupleRelativeProjPoints hc hX).sectionOfPoint T f r u hu =
      (ρ.quadrupleRelativeProjPoints hc hX).sectionOfPoint T' (yoneda.map r ≫ f) (𝟙 T') u hu' ≫
        (BigFppfOver.toScheme B S hS).map (ρ.projComparison hc f r) := by
  have h1 := ((ρ.quadrupleRelativeProjPoints hc hX).pointEquivOver T' (yoneda.map r ≫ f) (𝟙 T')
    ⟨u, hu'⟩).2
  have h2 := (ρ.quadrupleRelativeProjPoints hc hX).map_pointEquivOver T' (yoneda.map r ≫ f)
    (𝟙 T') ⟨u, hu'⟩
  set s' := ((ρ.quadrupleRelativeProjPoints hc hX).pointEquivOver T' (yoneda.map r ≫ f) (𝟙 T')
    ⟨u, hu'⟩).1 with hs'
  have hs : (s' ≫ ρ.projComparison hc f r) ≫
      (ρ.quadrupleRelativeProjPoints hc hX).fibreHom T f = r :=
    (Category.assoc _ _ _).trans ((congrArg (s' ≫ ·)
      ((ρ.relativeProjPoints hc).fibreComparison_comp_fibreHom T f r)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ r) h1).trans (Category.id_comp r))))
  have key : (ρ.quadrupleRelativeProjPoints hc hX).pointEquivOver T f r ⟨u, hu⟩ =
      ⟨s' ≫ ρ.projComparison hc f r, hs⟩ := by
    rw [← Equiv.eq_symm_apply]
    apply Subtype.ext
    change u = yoneda.map (s' ≫ ρ.projComparison hc f r) ≫ ρ.projToQuadrupleSpace hc hX f
    exact h2.symm.trans (((congrArg (yoneda.map s' ≫ ·)
      (ρ.projToQuadrupleSpace_comp hc hX f r)).symm.trans (Category.assoc _ _ _).symm).trans
        (congrArg (· ≫ ρ.projToQuadrupleSpace hc hX f) (Functor.map_comp _ _ _).symm))
  change (BigFppfOver.toScheme B S hS).map
      ((ρ.quadrupleRelativeProjPoints hc hX).pointEquivOver T f r ⟨u, hu⟩).1 ≫ 𝟙 _ =
    ((BigFppfOver.toScheme B S hS).map s' ≫ 𝟙 _) ≫ _
  rw [key, Category.comp_id, Category.comp_id]
  exact (BigFppfOver.toScheme B S hS).map_comp _ _

end Section

/-! ### The compatibility of Tag 07ZG with the comparisons of Stacks 084B -/

variable {ÂA ÂB : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X) →
      SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T)}
    (ρA : GradedAlgebraRestriction (GradedAlgebraPoints.ofQuasicoherentFamily ÂA))
    (ρB : GradedAlgebraRestriction (GradedAlgebraPoints.ofQuasicoherentFamily ÂB))
    (hcA : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      B.Contains (relativeProj (ÂA T f)).scheme)
    (hcB : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      B.Contains (relativeProj (ÂB T f)).scheme)
    (α : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X), SheafGradedAlgebraHom (ÂA T f) (ÂB T f))
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    (hα : ∀ {T T' : BigFppfOver B S hS} (τ : T' ⟶ T) (f : yoneda.obj T ⟶ X) (n : ℤ),
      (α T' (yoneda.map τ ≫ f)).toSituationHom.app n ≫ (ρB.restrict τ f _ rfl).app n =
        (ρA.restrict τ f _ rfl).app n ≫
          ((α T f).pullback ((BigFppfOver.toScheme B S hS).map τ)).toSituationHom.app n)

include hα in
/-- **The open of Tag 07ZG is compatible with the comparisons of Stacks 084B**: over `τ : T' ⟶ T`
the comparison `Proj_{T'}((f ∘ τ)^*B) ⟶ Proj_T(f^*B)` pulls `U(α_{T,f})` back to
`U(α_{T', f ∘ τ})`. -/
theorem preimage_relativeMapDomain_projComparison {T T' : BigFppfOver B S hS}
    (f : yoneda.obj T ⟶ X) (τ : T' ⟶ T) :
    (BigFppfOver.toScheme B S hS).map (ρB.projComparison hcB f τ) ⁻¹ᵁ
        (α T f).relativeMapDomain = (α T' (yoneda.map τ ≫ f)).relativeMapDomain := by
  rw [ρB.toScheme_map_projComparison hcB f τ, restrictProjIso]
  exact relativeProjCongr_baseChangeHom_preimage_relativeMapDomain _ _
    (ρA.isIso_restrict_app τ f _ rfl) _ (ρB.isIso_restrict_app τ f _ rfl) (α T f)
    (α T' (yoneda.map τ ≫ f)) (hα τ f)

include hα in
/-- **The morphism of Tag 07ZG is compatible with the comparisons of Stacks 084B**, read on a
morphism into `U(α_{T', f ∘ τ})`: the factorization through `U(α_{T,f})` of its composite with the
comparison, followed by `r_{α_{T,f}}`, is its factorization followed by `r_{α_{T', f ∘ τ}}` and the
comparison. -/
theorem liftToOpens_projComparison_comp_relativeMapHom {T T' : BigFppfOver B S hS}
    (f : yoneda.obj T ⟶ X) (τ : T' ⟶ T) {Y : Scheme.{u}}
    (k : Y ⟶ (relativeProj (ÂB T' (yoneda.map τ ≫ f))).scheme)
    (h' : k ⁻¹ᵁ (α T' (yoneda.map τ ≫ f)).relativeMapDomain = ⊤)
    (h : (k ≫ (BigFppfOver.toScheme B S hS).map (ρB.projComparison hcB f τ)) ⁻¹ᵁ
      (α T f).relativeMapDomain = ⊤) :
    liftToOpens (k ≫ (BigFppfOver.toScheme B S hS).map (ρB.projComparison hcB f τ))
        (α T f).relativeMapDomain h ≫ relativeMapHom (α T f) =
      liftToOpens k (α T' (yoneda.map τ ≫ f)).relativeMapDomain h' ≫
        relativeMapHom (α T' (yoneda.map τ ≫ f)) ≫
          (BigFppfOver.toScheme B S hS).map (ρA.projComparison hcA f τ) := by
  have hpre : ((ρB.restrictProjIso f τ).hom ≫
      baseChangeHom (ÂB T f) ((BigFppfOver.toScheme B S hS).map τ)) ⁻¹ᵁ
        (α T f).relativeMapDomain = (α T' (yoneda.map τ ≫ f)).relativeMapDomain :=
    ρB.toScheme_map_projComparison hcB f τ ▸
      preimage_relativeMapDomain_projComparison ρA ρB hcB α hα f τ
  have hmor : relativeMapHom (α T' (yoneda.map τ ≫ f)) ≫ (ρA.restrictProjIso f τ).hom ≫
      baseChangeHom (ÂA T f) ((BigFppfOver.toScheme B S hS).map τ) =
      ((ρB.restrictProjIso f τ).hom ≫
        baseChangeHom (ÂB T f) ((BigFppfOver.toScheme B S hS).map τ)).resLE
          (α T f).relativeMapDomain (α T' (yoneda.map τ ≫ f)).relativeMapDomain hpre.ge ≫
        relativeMapHom (α T f) :=
    relativeMapHom_comp_relativeProjCongr_baseChangeHom _ _
      (ρA.isIso_restrict_app τ f _ rfl) _ (ρB.isIso_restrict_app τ f _ rfl) (α T f)
      (α T' (yoneda.map τ ≫ f)) (hα τ f)
  have hk : (k ≫ (ρB.restrictProjIso f τ).hom ≫
      baseChangeHom (ÂB T f) ((BigFppfOver.toScheme B S hS).map τ)) ⁻¹ᵁ
        (α T f).relativeMapDomain = ⊤ := by
    rw [Scheme.Hom.comp_preimage, hpre, h']
  have e1 : liftToOpens (k ≫ (BigFppfOver.toScheme B S hS).map (ρB.projComparison hcB f τ))
      (α T f).relativeMapDomain h =
      liftToOpens (k ≫ (ρB.restrictProjIso f τ).hom ≫
        baseChangeHom (ÂB T f) ((BigFppfOver.toScheme B S hS).map τ))
          (α T f).relativeMapDomain hk :=
    liftToOpens_congr _ _ (congrArg (k ≫ ·) (ρB.toScheme_map_projComparison hcB f τ)) _ h hk
  have e2 := liftToOpens_comp_resLE (Z' := (relativeProj (ÂB T f)).scheme) k
    ((ρB.restrictProjIso f τ).hom ≫
      baseChangeHom (ÂB T f) ((BigFppfOver.toScheme B S hS).map τ))
    (α T f).relativeMapDomain _ hpre.ge h' hk
  refine (congrArg (· ≫ relativeMapHom (α T f)) (e1.trans e2)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (liftToOpens k (α T' (yoneda.map τ ≫ f)).relativeMapDomain h' ≫ ·)
    hmor.symm).trans ?_
  exact congrArg (fun z => liftToOpens k (α T' (yoneda.map τ ≫ f)).relativeMapDomain h' ≫
    relativeMapHom (α T' (yoneda.map τ ≫ f)) ≫ z) (ρA.toScheme_map_projComparison hcA f τ).symm

/-! ### The map of graded algebras over the scheme points of the base, constructed -/

include hα in
/-- The domain of definition at a point, read over the restricted point of the base. -/
theorem isDefinedOn_iff_isDefinedOn_restrict (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u : yoneda.obj T' ⟶ ρB.quadrupleSpace hcB hX)
    (hu : u ≫ ρB.quadrupleSpaceπ hcB hX = yoneda.map r ≫ f)
    (hu' : u ≫ ρB.quadrupleSpaceπ hcB hX = yoneda.map (𝟙 T') ≫ (yoneda.map r ≫ f)) :
    IsDefinedOn (ρA.quadrupleRelativeProjPoints hcA hX) (ρB.quadrupleRelativeProjPoints hcB hX)
        α T f r u hu ↔
      IsDefinedOn (ρA.quadrupleRelativeProjPoints hcA hX) (ρB.quadrupleRelativeProjPoints hcB hX)
        α T' (yoneda.map r ≫ f) (𝟙 T') u hu' := by
  change _ ⁻¹ᵁ _ = ⊤ ↔ _ ⁻¹ᵁ _ = ⊤
  rw [sectionOfPoint_eq_comp_projComparison ρB hcB hX T f r u hu hu']
  exact Iff.of_eq (congrArg (· = ⊤) ((Scheme.Hom.comp_preimage _ _ _).trans
    (congrArg _ (preimage_relativeMapDomain_projComparison ρA ρB hcB α hα f r))))

include hα in
/-- The domain of definition at a point is the domain of definition over its own image in the
base. -/
theorem isDefinedOn_iff_isDefined (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u : yoneda.obj T' ⟶ ρB.quadrupleSpace hcB hX)
    (hu : u ≫ ρB.quadrupleSpaceπ hcB hX = yoneda.map r ≫ f) :
    IsDefinedOn (ρA.quadrupleRelativeProjPoints hcA hX) (ρB.quadrupleRelativeProjPoints hcB hX)
        α T f r u hu ↔
      IsDefined (ρA.quadrupleRelativeProjPoints hcA hX) (ρB.quadrupleRelativeProjPoints hcB hX)
        α T' u := by
  have hu' : u ≫ ρB.quadrupleSpaceπ hcB hX = yoneda.map (𝟙 T') ≫ (yoneda.map r ≫ f) := by
    simpa using hu
  exact (isDefinedOn_iff_isDefinedOn_restrict ρA ρB hcA hcB α hX hα T f r u hu hu').trans
    (isDefinedOn_congr_base (ρA.quadrupleRelativeProjPoints hcA hX)
      (ρB.quadrupleRelativeProjPoints hcB hX) α T' (yoneda.map r ≫ f)
      (u ≫ ρB.quadrupleSpaceπ hcB hX) hu.symm (𝟙 T') u hu' (comp_eq_self u))

include hα in
/-- The induced point at a point of the base is the induced point over its own image in the
base. -/
theorem pointHomOn_eq_pointHomAt (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X)
    {T' : BigFppfOver B S hS} (r : T' ⟶ T) (u : yoneda.obj T' ⟶ ρB.quadrupleSpace hcB hX)
    (hu : u ≫ ρB.quadrupleSpaceπ hcB hX = yoneda.map r ≫ f)
    (h : IsDefinedOn (ρA.quadrupleRelativeProjPoints hcA hX)
      (ρB.quadrupleRelativeProjPoints hcB hX) α T f r u hu) :
    pointHomOn (ρA.quadrupleRelativeProjPoints hcA hX) (ρB.quadrupleRelativeProjPoints hcB hX)
        α T f r u hu h =
      pointHomAt (ρA.quadrupleRelativeProjPoints hcA hX) (ρB.quadrupleRelativeProjPoints hcB hX)
        α T' u ((isDefinedOn_iff_isDefined ρA ρB hcA hcB α hX hα T f r u hu).1 h) := by
  have hu' : u ≫ ρB.quadrupleSpaceπ hcB hX = yoneda.map (𝟙 T') ≫ (yoneda.map r ≫ f) := by
    simpa using hu
  have h₃ : IsDefinedOn (ρA.quadrupleRelativeProjPoints hcA hX)
      (ρB.quadrupleRelativeProjPoints hcB hX) α T' (yoneda.map r ≫ f) (𝟙 T') u hu' :=
    (isDefinedOn_iff_isDefinedOn_restrict ρA ρB hcA hcB α hX hα T f r u hu hu').1 h
  refine Eq.trans ?_ (pointHomOn_congr_base (ρA.quadrupleRelativeProjPoints hcA hX)
    (ρB.quadrupleRelativeProjPoints hcB hX) α T' _ _ hu.symm (𝟙 T') u hu' (comp_eq_self u) h₃ _)
  have hv := pointHomOn_comp (ρA.quadrupleRelativeProjPoints hcA hX)
    (ρB.quadrupleRelativeProjPoints hcB hX) α T' (yoneda.map r ≫ f) (𝟙 T') u hu' h₃
  have hv' : pointHomOn (ρA.quadrupleRelativeProjPoints hcA hX)
      (ρB.quadrupleRelativeProjPoints hcB hX) α T' (yoneda.map r ≫ f) (𝟙 T') u hu' h₃ ≫
        ρA.quadrupleSpaceπ hcA hX = yoneda.map r ≫ f := by
    rw [hv, CategoryTheory.Functor.map_id, Category.id_comp]
  refine (ρA.quadrupleRelativeProjPoints hcA hX).eq_of_sectionOfPoint_eq T f r _ _
    (pointHomOn_comp (ρA.quadrupleRelativeProjPoints hcA hX)
      (ρB.quadrupleRelativeProjPoints hcB hX) α T f r u hu h)
    hv' ?_
  have hs := sectionOfPoint_eq_comp_projComparison ρB hcB hX T f r u hu hu'
  have hlift : ((ρB.quadrupleRelativeProjPoints hcB hX).sectionOfPoint T' (yoneda.map r ≫ f)
      (𝟙 T') u hu' ≫ (BigFppfOver.toScheme B S hS).map (ρB.projComparison hcB f r)) ⁻¹ᵁ
        (α T f).relativeMapDomain = ⊤ := by
    rwa [← hs]
  refine (sectionOfPoint_pointHomOn (ρA.quadrupleRelativeProjPoints hcA hX)
    (ρB.quadrupleRelativeProjPoints hcB hX) α T f r u hu h).trans ?_
  refine Eq.trans ?_ ((sectionOfPoint_eq_comp_projComparison ρA hcA hX T f r _ hv' hv).trans
    (congrArg (· ≫ (BigFppfOver.toScheme B S hS).map (ρA.projComparison hcA f r))
      (sectionOfPoint_pointHomOn (ρA.quadrupleRelativeProjPoints hcA hX)
        (ρB.quadrupleRelativeProjPoints hcB hX) α T' (yoneda.map r ≫ f) (𝟙 T') u hu' h₃))).symm
  refine (congrArg (· ≫ relativeMapHom (α T f)) (liftToOpens_congr _ _ hs _ h hlift)).trans ?_
  exact (liftToOpens_projComparison_comp_relativeMapHom ρA ρB hcA hcB α hα f r _ h₃ hlift).trans
    (Category.assoc _ _ _).symm

include hα in
/-- **A family of maps of graded algebras over the scheme points of the base, compatible with the
restriction data, is a map of graded algebras over the scheme points of the base**: the two
compatibility conditions of `AlgebraicGeometry.Space.RelativeProjHomPoints` — that the open
`U(α_T)` and the morphism `r_{α_T}` of Tag 07ZG are compatible with base change in the test
object — are proved, from the canonicity of the identifications of Stacks 084B. -/
def homPoints : RelativeProjHomPoints (ρA.quadrupleRelativeProjPoints hcA hX)
    (ρB.quadrupleRelativeProjPoints hcB hX) where
  hom := α
  isDefinedOn_iff := isDefinedOn_iff_isDefined ρA ρB hcA hcB α hX hα
  pointHomOn_eq := pointHomOn_eq_pointHomAt ρA ρB hcA hcB α hX hα

/-- The underlying family of maps of `homPoints` is `α`. -/
@[simp] theorem homPoints_hom :
    (homPoints ρA ρB hcA hcB α hX hα).hom = α := rfl

end GradedAlgebraRestriction

end AlgebraicGeometry.Space

end
