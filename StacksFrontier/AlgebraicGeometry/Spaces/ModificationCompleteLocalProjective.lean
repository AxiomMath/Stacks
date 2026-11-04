module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.FormalCurve.SpaceAlgebraization
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraizationMorphismAdicFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraizationMorphismSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.CompletionProperOverIsEquivalenceBaseObject
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.HomBijection.CompletionBijectiveOnHomsBaseObject
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.InductionClosedSubspaceTower
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationSpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksCore.Tactic.StacksAttribute

/-!
# Modifications of a complete local domain of dimension two are projective

If `(A, 𝔪, κ)` is a complete Noetherian local domain of dimension `2`, then every modification
of `Spec A` is projective over `A`.

## Main results

* `C1605.existsUnique_algebraization_adicFibre`: Grothendieck's algebraization of morphisms of
  algebraic spaces over a Noetherian adically complete ring, in the vocabulary of adic fibres.
* `C1605.exists_iso_isProjective_of_isProper_of_dimension_adicFibre_le_one`: a proper algebraic
  space over a complete Noetherian local ring whose special fibre has dimension at most one is a
  scheme projective over the ring.
* `AlgebraicGeometry.Space.exists_iso_isProjective_of_isIntegralModification`: every modification
  of `Spec A`, for `A` a complete Noetherian local domain of dimension `2`, is projective over `A`.

## References

* [Stacks Project, Tag 0AGN](https://stacks.math.columbia.edu/tag/0AGN)
* [Stacks Project, Tag 0AE7](https://stacks.math.columbia.edu/tag/0AE7)
* [Stacks Project, Tag 0A4Z](https://stacks.math.columbia.edu/tag/0A4Z)
* [Stacks Project, Tag 0E7R](https://stacks.math.columbia.edu/tag/0E7R)
* [Stacks Project, Tag 0AYJ](https://stacks.math.columbia.edu/tag/0AYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] isAffine_toScheme_baseObject isLocallyNoetherian_toScheme_baseObject

namespace C1605

/-- Grothendieck's algebraization of morphisms of algebraic spaces, in the vocabulary of adic
fibres. Let `A` be a Noetherian ring complete with respect to an ideal `I`, let `fX : X ⟶ Spec A`
be proper and `fY : Y ⟶ Spec A` separated and of finite type. Every compatible system of
morphisms `g n` over `Spec A` between the adic fibres of `fX` and of `fY` is induced by a unique
morphism `X ⟶ Y` over `Spec A`. -/
theorem existsUnique_algebraization_adicFibre (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) [IsAdicComplete I A] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of A)))
    (hSn : ∀ n, B.Contains (adicThickening A I n))
    {X Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hS X) (hY : IsAlgebraicSpace B (Spec (.of A)) hS Y)
    (fX : X ⟶ yoneda.obj (baseObject A B hS)) (fY : Y ⟶ yoneda.obj (baseObject A B hS))
    (hproper : IsProper B (Spec (.of A)) hS fX)
    (hseparated : IsSeparated B (Spec (.of A)) hS fY)
    (hfinite : IsFiniteType B (Spec (.of A)) hS fY)
    (g : ∀ n, adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fY n)
    (g_over : ∀ n, g n ≫ pullback.snd fY (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)))
    (g_compatible : ∀ n,
      adicFibreSucc A I B hS hSn fX n ≫ g (n + 1) = g n ≫ adicFibreSucc A I B hS hSn fY n) :
    ∃! algebraization : {f : X ⟶ Y // f ≫ fY = fX},
      ∀ n, adicFibreMap A I B hS hSn algebraization.1 algebraization.2 n = g n :=
  existsUnique_algebraization_of_adicFibre_of_closedSubspaceTowerAlgebraizes A I B hS hSn
    inferInstance
    (fun _ f => closedSubspaceTowerAlgebraizes_of_existence _ _ f
      (C1573.completionBijectiveOnHoms_baseObject A hS _ f)
      (C1573.completionProperOverIsEquivalence_baseObject A hS _ f))
    hX hY fX fY hproper hseparated hfinite g g_over g_compatible

/-- Let `(A, 𝔪, κ)` be a complete Noetherian local ring and `fX : X ⟶ Spec A` a proper morphism
of algebraic spaces with `dim X_κ ≤ 1`. Then `X` is a scheme projective over `A`: there are a
projective morphism of schemes `fY : Y ⟶ Spec A` and an isomorphism of `X` with the algebraic
space `Y` over `Spec A`. -/
theorem exists_iso_isProjective_of_isProper_of_dimension_adicFibre_le_one
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A]
    (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of A)))
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B (Spec (.of A)) hS X)
    (fX : X ⟶ yoneda.obj (baseObject A B hS)) (hproper : IsProper B (Spec (.of A)) hS fX)
    (hdim : dimension B (Spec (.of A)) hS
      (adicFibre A (maximalIdeal A) B hS (contains_adicThickening A _ B hS) fX 0)
      (isAlgebraicSpace_adicFibre A _ B hS (contains_adicThickening A _ B hS) hX fX 0) ≤ 1) :
    ∃ (Y : Scheme.{u}) (hY : B.Contains Y) (fY : Y ⟶ Spec (.of A)),
      IsProjective fY ∧ IsProjectiveMorphism fY ∧
      ∃ e : X ≅ yoneda.obj (siteObject B (Spec (.of A)) hS hY fY),
        e.hom ≫ yoneda.map (siteObjectToBase A B hS hY fY) = fX := by
  set I := maximalIdeal A
  set hSn := contains_adicThickening A I B hS
  have halg := fun {X Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} hX hY fX fY hp hs hf g
    hgo hgc => existsUnique_algebraization_adicFibre (X := X) (Y := Y) A I B hS hSn hX hY fX fY
      hp hs hf g hgo hgc
  have hy := isAlgebraicSpace_yoneda B (Spec (.of A)) hS
  have hbase := hy (baseObject A B hS)
  have hT := fun n => isAlgebraicSpace_adicFibre A I B hS hSn hX fX n
  have hp0 : IsProper B (Spec (.of A)) hS
      (pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn 0))) := by
    rw [← pullbackSymmetry_hom_comp_fst]
    have hP := isAlgebraicSpace_pullback B (Spec (.of A)) hS
      (yoneda.map (adicThickeningMap A I B hS hSn 0)) fX (hy _) hX hbase
    exact isProper_comp B (Spec (.of A)) hS (hT 0) hP (hy _) _ _
      (isProper_of_isClosedImmersion B (Spec (.of A)) hS (hT 0) hP _
        (isClosedImmersion_of_isIso B (Spec (.of A)) hS _))
      (isProper_pullback_fst B (Spec (.of A)) hS hX hbase (hy _) fX _ hproper)
  obtain ⟨Y, hY, fY, hfY, hfY', k, hk, hkpb⟩ :=
    exists_isProjective_algebraization_of_dimension_le_one A B hS
      (fun n => adicFibre A I B hS hSn fX n) hT
      (fun n => pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)))
      (fun n => adicFibreSucc A I B hS hSn fX n)
      (fun n => isPullback_adicFibreSucc A I B hS hSn fX n) hp0 hdim
  set fYs := yoneda.map (siteObjectToBase A B hS hY fY)
  have hYs := hy (siteObject B (Spec (.of A)) hS hY fY)
  have hfYsp : IsProper B (Spec (.of A)) hS fYs :=
    isProper_yoneda_map B (Spec (.of A)) hS _ hfY.isProper
  set g : ∀ n, adicFibre A I B hS hSn fX n ⟶ adicFibre A I B hS hSn fYs n :=
    fun n => (hkpb n).isoPullback.hom
  have hgs : ∀ n, g n ≫ pullback.snd fYs (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)) :=
    fun n => (hkpb n).isoPullback_hom_snd
  have hgf : ∀ n, g n ≫ pullback.fst fYs (yoneda.map (adicThickeningMap A I B hS hSn n)) = k n :=
    fun n => (hkpb n).isoPullback_hom_fst
  have hgc : ∀ n, adicFibreSucc A I B hS hSn fX n ≫ g (n + 1) =
      g n ≫ adicFibreSucc A I B hS hSn fYs n := by
    intro n
    apply pullback.hom_ext
    · rw [Category.assoc, hgf, hk, Category.assoc, adicFibreSucc_fst, hgf]
    · rw [Category.assoc, hgs, adicFibreSucc_snd, Category.assoc, adicFibreSucc_snd,
        ← Category.assoc, hgs]
  have hgs' : ∀ n, inv (g n) ≫ pullback.snd fX (yoneda.map (adicThickeningMap A I B hS hSn n)) =
      pullback.snd fYs (yoneda.map (adicThickeningMap A I B hS hSn n)) := fun n => by
    simp [IsIso.inv_comp_eq, hgs]
  have hgc' : ∀ n, adicFibreSucc A I B hS hSn fYs n ≫ inv (g (n + 1)) =
      inv (g n) ≫ adicFibreSucc A I B hS hSn fX n := fun n => by
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← hgc, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  obtain ⟨⟨φ, hφ⟩, hφn, -⟩ := halg hX hYs fX fYs hproper hfYsp.isSeparated hfYsp.isFiniteType
    g hgs hgc
  obtain ⟨⟨ψ, hψ⟩, hψn, -⟩ := halg hYs hX fYs fX hfYsp hproper.isSeparated
    hproper.isFiniteType (fun n => inv (g n)) hgs' hgc'
  have hid : ∀ {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
      (hX : IsAlgebraicSpace B (Spec (.of A)) hS X) (fX : X ⟶ yoneda.obj (baseObject A B hS))
      (hp : IsProper B (Spec (.of A)) hS fX) (φ : X ⟶ X) (hφ : φ ≫ fX = fX),
      (∀ n, adicFibreMap A I B hS hSn φ hφ n = 𝟙 _) → φ = 𝟙 X := by
    intro X hX fX hp φ hφ hn
    obtain ⟨_, _, huniq⟩ := halg hX hX fX fX hp hp.isSeparated hp.isFiniteType
      (fun n => 𝟙 _) (fun n => Category.id_comp _) (by simp)
    exact congrArg Subtype.val ((huniq ⟨φ, hφ⟩ hn).trans
      (huniq ⟨𝟙 X, Category.id_comp fX⟩ (adicFibreMap_id A I B hS hSn fX)).symm)
  have hφψ : φ ≫ ψ = 𝟙 X :=
    hid hX fX hproper _ (by rw [Category.assoc, hψ, hφ]) fun n => by
      rw [adicFibreMap_comp A I B hS hSn φ hφ ψ hψ n, hφn, hψn, IsIso.hom_inv_id]
  have hψφ : ψ ≫ φ = 𝟙 _ :=
    hid hYs fYs hfYsp _ (by rw [Category.assoc, hφ, hψ]) fun n => by
      rw [adicFibreMap_comp A I B hS hSn ψ hψ φ hφ n, hψn, hφn, IsIso.inv_hom_id]
  exact ⟨Y, hY, fY, hfY, hfY', ⟨φ, ψ, hφψ, hψφ⟩, hφ⟩

end C1605

/-- Let `(A, 𝔪, κ)` be a complete Noetherian local domain of dimension `2`. Every modification
`f : X ⟶ Spec A` (Stacks 0AD8) is projective over `A`: `X` is a scheme `Y`, in the sense that
there are a projective morphism of schemes `fY : Y ⟶ Spec A` and an isomorphism of `X` with the
algebraic space `Y` over `Spec A`. -/
@[stacks 0AGN]
theorem exists_iso_isProjective_of_isIntegralModification
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    [IsAdicComplete (maximalIdeal A) A] (hdim : ringKrullDim A = 2)
    (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of A)))
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hS X)
    (f : X ⟶ yoneda.obj (baseObject A B hS))
    (hf : IsIntegralModification B (Spec (.of A)) hS hX
      (isAlgebraicSpace_yoneda B (Spec (.of A)) hS _)
      (isIntegralSpace_yoneda_baseTerminal A B hS) f) :
    ∃ (Y : Scheme.{u}) (hY : B.Contains Y) (fY : Y ⟶ Spec (.of A)),
      IsProjective fY ∧ IsProjectiveMorphism fY ∧
      ∃ e : X ≅ yoneda.obj (siteObject B (Spec (.of A)) hS hY fY),
        e.hom ≫ yoneda.map (siteObjectToBase A B hS hY fY) = f :=
  C1605.exists_iso_isProjective_of_isProper_of_dimension_adicFibre_le_one A B hS hX f
    (hf.isProper B _ hS)
    (dimension_adicFibre_zero_le_one_of_isIntegralModification A B hS hdim hX f hf)

end AlgebraicGeometry.Space

end
