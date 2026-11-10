/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedHilbertFunctionComparison
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotClosedSubschemeBaseChange

/-!
# Hilbert-bounded points of `𝒫olarized` form a Noetherian space

**Stacks 0E96.** Let `n` be a natural number, let `P` be a polynomial and let `T` be a set of
points of `|Polarized|` each of which is represented, over some field `k`, by a polarized proper
scheme `(X, L)` such that (1) the Hilbert polynomial of `L` on `X` is `P`, and (2) there is a
closed immersion `i : X -> Pn_k` with `i^*OO(1) ≅ L`. Then `T` is a Noetherian topological space.

Neither `n ≥ 1` nor the numericality of `P`, both hypotheses of the source's statement, is used.

## Main results

* `Stacks.IdealSheaf.exists_iso_subscheme_of_pushforwardUnit_iso`: a closed immersion whose
  pushed-forward structure sheaf is the quotient of `OO_X` by a sheaf of ideals `J` is the closed
  immersion of `J`, up to an isomorphism of its source over `X`.
* `AlgebraicGeometry.exists_universalPolarizedFamily_hilbertFunctor`: the universal family of
  `Hilb^P_{Pn_Z/Z}` with its mapping property.
* `AlgebraicGeometry.noetherianSpace_of_isHilbertPolarizedPoint`: Stacks 0E96.

## References

* [Stacks Project, Tag 0E96](https://stacks.math.columbia.edu/tag/0E96)
* [Stacks Project, Tag 01QQ](https://stacks.math.columbia.edu/tag/01QQ)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 0D3W](https://stacks.math.columbia.edu/tag/0D3W)
* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.IdealSheaf

variable {X : Scheme.{u}}

/-- For morphisms of schemes `i : Z ⟶ X` and `j : W ⟶ X` and a morphism
`φ : i_* 𝒪_Z ⟶ j_* 𝒪_W` of modules on `X` which is surjective on sections over an open `U`, the
kernel of `i` on `U` is contained in the kernel of `j` on `U`. -/
theorem ker_app_le_of_pushforwardUnit_hom {Z W : Scheme.{u}} (i : Z ⟶ X) (j : W ⟶ X)
    (φ : (Scheme.Modules.pushforward i).obj (Scheme.unitModule Z) ⟶
      (Scheme.Modules.pushforward j).obj (Scheme.unitModule W))
    (U : X.Opens) (hφ : Function.Surjective (φ.app U)) :
    RingHom.ker (i.app U).hom ≤ RingHom.ker (j.app U).hom := by
  intro x hx
  have hx0 : i.app U x = 0 := by rwa [← RingHom.mem_ker]
  have hkill : ∀ s, x • s =
      (0 : Γ((Scheme.Modules.pushforward i).obj (Scheme.unitModule Z), U)) := by
    intro s
    change (show Γ((Scheme.Modules.pushforward i).obj (Scheme.unitModule Z), U) from
      i.app U x * (show Γ(Z, i ⁻¹ᵁ U) from s)) = 0
    rw [hx0]
    show (show Γ((Scheme.Modules.pushforward i).obj (Scheme.unitModule Z), U) from
      (0 : Γ(Z, i ⁻¹ᵁ U)) * (show Γ(Z, i ⁻¹ᵁ U) from s)) = 0
    rw [zero_mul]
    rfl
  obtain ⟨s₀, hs₀⟩ := hφ (show Γ((Scheme.Modules.pushforward j).obj (Scheme.unitModule W), U) from
    (1 : Γ(W, j ⁻¹ᵁ U)))
  have hlin : φ.app U (x • s₀) = x • φ.app U s₀ := (φ.val.app (op U)).hom.map_smul x s₀
  have hone : x • (show Γ((Scheme.Modules.pushforward j).obj (Scheme.unitModule W), U) from
      (1 : Γ(W, j ⁻¹ᵁ U))) = 0 := by
    rw [← hs₀, ← hlin, hkill s₀, map_zero]
  rw [RingHom.mem_ker]
  have hmul : j.app U x * (1 : Γ(W, j ⁻¹ᵁ U)) = 0 := hone
  rwa [mul_one] at hmul

/-- **The kernel of a quasi-compact morphism is determined by its pushed-forward structure
sheaf.** If `i_* 𝒪_Z` is isomorphic, as a module on `X`, to the quotient of `𝒪_X` by a sheaf of
ideals `J`, then the kernel of `i` is `J`. No compatibility of the two quotient maps is
assumed. -/
theorem hom_ker_eq_of_pushforwardUnit_iso {Z : Scheme.{u}} (i : Z ⟶ X) [QuasiCompact i]
    (J : X.IdealSheafData)
    (e : (Scheme.Modules.pushforward i).obj (Scheme.unitModule Z) ≅
      (Scheme.Modules.pushforward J.subschemeι).obj (Scheme.unitModule J.subscheme)) :
    i.ker = J := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  rw [Scheme.Hom.ker_apply i U, ← Scheme.IdealSheafData.ker_subschemeι_app J U]
  refine le_antisymm
    (ker_app_le_of_pushforwardUnit_hom i J.subschemeι e.hom U.1 fun t => ⟨e.inv.app U.1 t, ?_⟩)
    (ker_app_le_of_pushforwardUnit_hom J.subschemeι i e.inv U.1 fun t => ⟨e.hom.app U.1 t, ?_⟩)
  · have h := congrArg (fun φ => Scheme.Modules.Hom.app φ U.1) e.inv_hom_id
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at h
    exact congrArg (fun f => AddCommGrpCat.Hom.hom f t) h
  · have h := congrArg (fun φ => Scheme.Modules.Hom.app φ U.1) e.hom_inv_id
    simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at h
    exact congrArg (fun f => AddCommGrpCat.Hom.hom f t) h

/-- **A closed immersion whose pushed-forward structure sheaf is the quotient of `𝒪_X` by a sheaf
of ideals `J` is the closed immersion of `J`**, up to an isomorphism of its source over `X`. -/
theorem exists_iso_subscheme_of_pushforwardUnit_iso {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (J : X.IdealSheafData)
    (e : (Scheme.Modules.pushforward i).obj (Scheme.unitModule Z) ≅
      (Scheme.Modules.pushforward J.subschemeι).obj (Scheme.unitModule J.subscheme)) :
    ∃ ψ : Z ≅ J.subscheme, ψ.hom ≫ J.subschemeι = i := by
  obtain rfl := hom_ker_eq_of_pushforwardUnit_iso i J e
  exact ⟨asIso i.toImage, i.toImage_imageι⟩

end Stacks.IdealSheaf

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)

/-- **The universal family of `Hilb^P_{ℙⁿ_ℤ/ℤ}`, with its mapping property.** Let `U₀` be an
object of the big fppf category over `S` whose represented presheaf is the Hilbert functor
`Quot^P_{𝒪/ℙⁿ_ℤ/ℤ}`, presented by the isomorphism `eH`. Then there is a polarized family `x₀` over
`U₀` to which every closed subscheme `i : Z ⟶ ℙⁿ_U` of projective space over a scheme `U` of the
site isomorphic to the spectrum of a field, flat and of finite presentation over `U` and with
`𝒪(1)|_Z` of Hilbert polynomial `P`, has a morphism of polarized families. -/
theorem exists_universalPolarizedFamily_hilbertFunctor (hT : IsTerminal (B.obj hS)) (n : ℕ)
    (P : Polynomial ℚ) (U₀ : BigFppfOver B S hS)
    (eH : yoneda.obj U₀ ⋙ uliftFunctor.{u + 1} ≅
      (BigFppfOver.toScheme B S hS).op ⋙ ProjectiveQuot.hilbertFunctor.{u} n 1 P) :
    ∃ x₀ : PolarizedFamily B, ∃ _ : x₀.base = U₀.left,
      ∀ (U : B.Schemes) (k : Type u) [Field k] (e : B.inclusion.obj U ≅ Spec (.of k))
        {Z : Scheme.{u}} (i : Z ⟶ projectiveSpaceOver n (B.inclusion.obj U))
        [IsClosedImmersion i]
        (hfl : Flat (i ≫ (projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U)))
        (hfp : FinitePresentation
          (i ≫ (projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U))),
        (∀ d : ℤ, (polarizedHilbertFunction (hilbertPolarizedFamily n U i hfl hfp) k e d : ℚ) =
          P.eval (d : ℚ)) →
        Nonempty (hilbertPolarizedFamily n U i hfl hfp ⟶ x₀) := by
  obtain ⟨K₀, hK₀, hmem₀⟩ :
      ∃ K₀ : Subobject (ProjectiveQuot.freeModule n 1 (B.inclusion.obj U₀.left)),
        K₀ = universalHilbertFamily B hS n P U₀ eH ∧
          K₀ ∈ ProjectiveQuot.hilbertFamilies n 1 P (B.inclusion.obj U₀.left) :=
    ⟨_, rfl, universalHilbertFamily_mem B hS n P U₀ eH⟩
  refine ⟨hilbertPolarizedFamily n U₀.left (ProjectiveQuot.subschemeOfFamilyι K₀ hmem₀.1.1)
    (ProjectiveQuot.flat_subschemeOfFamilyι_comp hmem₀.1)
    (ProjectiveQuot.finitePresentation_subschemeOfFamilyι_comp hmem₀.1), rfl, ?_⟩
  intro U k _ e Z i _ hfl hfp hP
  obtain ⟨K, hK, ⟨eQ⟩⟩ := hilbertFamilies_of_polarizedHilbertFunction B U k e i hfl hfp P hP
  obtain ⟨g, hg⟩ : ∃ g : (Over.mk (hT.from U) : BigFppfOver B S hS) ⟶ U₀,
      (eH.hom.app (op (Over.mk (hT.from U))) (ULift.up g)).1 = K := by
    have h2 := CategoryTheory.comp_apply (eH.inv.app (op (Over.mk (hT.from U))))
      (eH.hom.app (op (Over.mk (hT.from U)))) (⟨K, hK⟩ : _)
    rw [eH.inv_hom_id_app] at h2
    exact ⟨ULift.down (eH.inv.app (op (Over.mk (hT.from U))) ⟨K, hK⟩),
      congrArg Subtype.val (h2.symm.trans (CategoryTheory.id_apply _))⟩
  have hKeq : ProjectiveQuot.baseChange (B.inclusion.map g.left) K₀ = K := by
    have hnat : eH.hom.app (op (Over.mk (hT.from U)))
          ((yoneda.obj U₀ ⋙ uliftFunctor.{u + 1}).map (Quiver.Hom.op g) (ULift.up (𝟙 U₀))) =
        ((BigFppfOver.toScheme B S hS).op ⋙ ProjectiveQuot.hilbertFunctor.{u} n 1 P).map
          (Quiver.Hom.op g) (eH.hom.app (op U₀) (ULift.up (𝟙 U₀))) :=
      eH.hom.naturality_apply _ _
    have hup : (yoneda.obj U₀ ⋙ uliftFunctor.{u + 1}).map (Quiver.Hom.op g)
        (ULift.up (𝟙 U₀)) = ULift.up g := by
      change ULift.up (g ≫ 𝟙 U₀) = _
      rw [Category.comp_id]
    rw [hup] at hnat
    rw [hK₀]
    exact (congrArg Subtype.val hnat).symm.trans hg
  have hfpK' : (ProjectiveQuot.quotient
      (ProjectiveQuot.baseChange (B.inclusion.map g.left) K₀)).IsFinitePresentation := by
    rw [hKeq]
    exact hK.1.1
  have hJ : ProjectiveQuot.idealSheafDataOfFamily K hK.1.1 =
      (ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1).comap
        (projectiveSpaceOverMap n (B.inclusion.map g.left)) := by
    have hcongr : ∀ (K₁ K₂ : Subobject (ProjectiveQuot.freeModule n 1 (B.inclusion.obj U)))
        (_ : K₁ = K₂) (h₁ : (ProjectiveQuot.quotient K₁).IsFinitePresentation)
        (h₂ : (ProjectiveQuot.quotient K₂).IsFinitePresentation),
        ProjectiveQuot.idealSheafDataOfFamily K₁ h₁ =
          ProjectiveQuot.idealSheafDataOfFamily K₂ h₂ := by
      rintro K₁ _ rfl _ _
      rfl
    rw [hcongr K _ hKeq.symm hK.1.1 hfpK']
    exact ProjectiveQuot.idealSheafDataOfFamily_baseChange _ hmem₀.1.1 hfpK'
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Z ≅ ((ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1).comap
      (projectiveSpaceOverMap n (B.inclusion.map g.left))).subscheme,
      ψ.hom ≫ ((ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1).comap
        (projectiveSpaceOverMap n (B.inclusion.map g.left))).subschemeι = i := by
    rw [← hJ]
    exact Stacks.IdealSheaf.exists_iso_subscheme_of_pushforwardUnit_iso i _
      (eQ ≪≫ (ProjectiveQuot.pushforwardUnitSubschemeOfFamilyIso K hK.1.1).symm)
  have hw := Scheme.IdealSheafData.subschemeMap_subschemeι
    ((ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1).comap
      (projectiveSpaceOverMap n (B.inclusion.map g.left)))
    (ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1)
    (projectiveSpaceOverMap n (B.inclusion.map g.left))
    ((ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1).le_map_comap _)
  have sq : IsPullback (Scheme.IdealSheafData.subschemeMap _
      (ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1) _
      ((ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1).le_map_comap
        (projectiveSpaceOverMap n (B.inclusion.map g.left))))
      (((ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1).comap
          (projectiveSpaceOverMap n (B.inclusion.map g.left))).subschemeι ≫
        (projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U))
      ((ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1).subschemeι ≫
        (projectiveSpaceOver n (B.inclusion.obj U₀.left) ↘ B.inclusion.obj U₀.left))
      (B.inclusion.map g.left) :=
    (Stacks.Bertini.isPullback_subschemeι_comap _ _).flip.paste_vert
      (isPullback_projectiveSpaceOverMap n _)
  have htot : (ψ.hom ≫ Scheme.IdealSheafData.subschemeMap _
      (ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1) _
      ((ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1).le_map_comap
        (projectiveSpaceOverMap n (B.inclusion.map g.left)))) ≫
      (ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1).subschemeι =
      i ≫ projectiveSpaceOverMap n (B.inclusion.map g.left) := by
    rw [Category.assoc, hw, ← Category.assoc, hψ]
  have cart : IsPullback (ψ.hom ≫ Scheme.IdealSheafData.subschemeMap _
      (ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1) _
      ((ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1).le_map_comap
        (projectiveSpaceOverMap n (B.inclusion.map g.left))))
      (i ≫ (projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U))
      ((ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1).subschemeι ≫
        (projectiveSpaceOver n (B.inclusion.obj U₀.left) ↘ B.inclusion.obj U₀.left))
      (B.inclusion.map g.left) := by
    have h1 : IsPullback ψ.hom
        (i ≫ (projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U))
        (((ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1).comap
            (projectiveSpaceOverMap n (B.inclusion.map g.left))).subschemeι ≫
          (projectiveSpaceOver n (B.inclusion.obj U) ↘ B.inclusion.obj U))
        (𝟙 (B.inclusion.obj U)) :=
      IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id, ← Category.assoc, hψ]⟩
    have h2 := h1.paste_horiz sq
    rwa [Category.id_comp] at h2
  exact ⟨{ baseMap := g.left
           totalMap := ψ.hom ≫ Scheme.IdealSheafData.subschemeMap _
             (ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1) _
             ((ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1).le_map_comap
               (projectiveSpaceOverMap n (B.inclusion.map g.left)))
           cartesian := cart
           lineBundleIso :=
             (Scheme.Modules.pullbackComp _
                 (ProjectiveQuot.idealSheafDataOfFamily K₀ hmem₀.1.1).subschemeι).app _ ≪≫
               (Scheme.Modules.pullbackCongr htot).app _ ≪≫
               ((Scheme.Modules.pullbackComp i
                 (projectiveSpaceOverMap n (B.inclusion.map g.left))).app _).symm ≪≫
               (Scheme.Modules.pullback i).mapIso
                 (Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.twistOverPullbackIso
                   n (B.inclusion.map g.left) 1) }⟩

/-- Let `n ∈ ℕ`, let `P ∈ ℚ[t]` and let `T ⊆ |𝒫olarized|` be a set of points each represented
over a field by a polarized proper scheme `(X, ℒ)` satisfying conditions (1) and (2)
(`AlgebraicGeometry.IsHilbertPolarizedOver`): the Hilbert polynomial of `ℒ` on `X` is `P`, and
there is a closed immersion `i : X ⟶ ℙⁿ` over the base with `i^*𝒪(1) ≅ ℒ`. Then `T` is a
Noetherian topological space, in particular quasi-compact. The source's hypotheses `n ≥ 1` and
that `P` is numerical are not needed. -/
@[stacks 0E96]
theorem noetherianSpace_of_isHilbertPolarizedPoint (hT : IsTerminal (B.obj hS)) (n : ℕ)
    (P : Polynomial ℚ)
    (T : Set (Stack.points B S hS (polarizedStackUnconditional B hS hT).val
      (polarizedStackUnconditional B hS hT).property))
    (hTP : ∀ ξ ∈ T, ∃ p, Stack.pointClass B S hS _ _ p = ξ ∧
      IsHilbertPolarizedPoint B hS hT n P p) :
    letI := Stack.pointTopology B S hS (polarizedStackUnconditional B hS hT)
    NoetherianSpace T :=
  noetherianSpace_of_isHilbertPolarizedPoint_of_universalFamily B hS hT n P
    (fun U₀ eH => exists_universalPolarizedFamily_hilbertFunctor B hS hT n P U₀ eH) T hTP

end AlgebraicGeometry

end
