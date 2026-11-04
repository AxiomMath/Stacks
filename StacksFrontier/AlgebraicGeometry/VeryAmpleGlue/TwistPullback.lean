module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaClauseOne
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.DegreeOne
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.SectionGenerator
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.StalkBridge
public import StacksFrontier.AlgebraicGeometry.EtaleAlgebra.FlatBaseChange.AlgebraComparisonEpi
public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.EpiIso
public import StacksFrontier.AlgebraicGeometry.Divisors.SectionPowerOpen
public import StacksFrontier.AlgebraicGeometry.SectionPowerOverOpen.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleProjOpenImmersion
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.LocalOnBase
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare

/-!
# The pullback of `𝒪(1)` along the morphism `r_{L,ψ}` into a projective bundle

Let `f : T ⟶ S` be a morphism of schemes, `E` a quasi-coherent `𝒪_S`-module and
`P = (L, ψ)` a graded map `f^* Sym(E) ⟶ ⨁_{d ≥ 0} L^{⊗ d}` in the sense of [Stacks, Tag 01O8]
(`Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism.GradedPowerMap`). [Stacks, Tag 01O9]
attaches to it the morphism `r = r_{L,ψ} : U(ψ) ⟶ 𝐏(E)` and the map of graded algebras
`θ : r^*(⨁_d 𝒪(d)) ⟶ ⨁_d L^{⊗ d}|_{U(ψ)}`
(`…GradedPowerMap.globalMorphism`, `…GradedPowerMap.theta`). This file shows that the degree-one
component of `θ` is an isomorphism as soon as the values of `ψ` on degree-one sections generate
`L` at every point of `U(ψ)`, and hence that `r^* 𝒪_{𝐏(E)}(1) ≅ L` when moreover `U(ψ)` is all of
`T`. This is the twist half of the morphism `r_{L,ψ}` of [Stacks, Tag 01VR], whose immersion half
is `Stacks.QuasiProjectiveCompactification.isImmersion_globalMorphism_of_chartsAreImmersions`.

## Main results

* `Stacks.VeryAmpleGlue.epi_of_forall_mem_nonvanishingLocusOn`: a morphism into an invertible
  module is an epimorphism once, at every point, it carries some local section to a section that
  does not vanish there.
* `Stacks.VeryAmpleGlue.isIso_theta_one`: **the degree-one component of `θ` is an isomorphism**
  where the degree-one values of `ψ` generate.
* `Stacks.VeryAmpleGlue.pullbackTwistOneIso`: **`L ≅ r^* 𝒪_{𝐏(E)}(1)`** when `U(ψ) = T`.

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
* [Stacks Project, Tag 01O8](https://stacks.math.columbia.edu/tag/01O8)
* [Stacks Project, Tag 01VR](https://stacks.math.columbia.edu/tag/01VR)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open CategoryTheory.MonoidalCategory

universe u

namespace Stacks.VeryAmpleGlue

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-- **A morphism into an invertible module hitting a nonvanishing section at every point is an
epimorphism.** If for every point `z` there are an open `O` and a section `m` of `M` over `O` such
that `φ(m)` does not vanish at `z`, then `φ : M ⟶ N` is an epimorphism. -/
theorem epi_of_forall_mem_nonvanishingLocusOn {Z : Scheme.{u}} {M N : Z.Modules}
    [Stacks.Ample.IsInvertibleModule Z N] (φ : M ⟶ N)
    (h : ∀ z : Z, ∃ (O : Z.Opens) (m : Γ(M, O)),
      z ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn N O (φ.app O m)) :
    Epi φ := by
  refine Stacks.FundamentalGroup.epi_of_isLocallySurjective φ fun W t x hx => ?_
  obtain ⟨O, m, hxO⟩ := h x
  let W' : Z.Opens := W ⊓ Stacks.SectionPowerOpen.nonvanishingOpenOn N O (φ.app O m)
  have hW'O : W' ≤ O := inf_le_right.trans
    (Stacks.SectionPowerOpen.nonvanishingOpenOn_le N O (φ.app O m))
  have hbij := Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top
    N (φ.app O m) W' hW'O fun y hy =>
      (Stacks.NonvanishingPullback.mem_maximalSmul_iff _ _ _).not.mp hy.2.2
  obtain ⟨c, hc⟩ := hbij.2 (N.presheaf.map (homOfLE inf_le_left : W' ⟶ W).op t)
  refine ⟨W', inf_le_left, ⟨hx, hxO⟩, c • M.presheaf.map (homOfLE hW'O).op m, ?_⟩
  rw [Scheme.Modules.Hom.app_smul, ← hc]
  congr 1
  exact ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE hW'O).op) m


/-- **The unit of the module-pullback adjunction along the inclusion of an open subscheme is the
restriction isomorphism, on sections over an arbitrary open.** -/
theorem pullbackUnit_ι_eq_restrictIsoPullback_hom_app {X : Scheme.{u}} (U : X.Opens)
    (N : X.Modules) (V : X.Opens) (s : Γ(N, V)) :
    Stacks.RingedSpace.pullbackUnit U.ι.toLRSHom.toShHom N (op V) s =
      Scheme.Modules.Hom.app (Stacks.AmplePullbackPart1.restrictIsoPullback U N).hom (U.ι ⁻¹ᵁ V)
        ((N.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op).hom s) := by
  have h := congrArg (fun φ => Scheme.Modules.Hom.app φ V)
    (Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction U.ι)
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι) N)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app] at h
  exact (ConcreteCategory.congr_hom h s).symm

/-- **Nonvanishing survives restriction to an open subscheme.** If a section `s` of `N` over `V`
does not vanish at the image of a point `x` of the open subscheme `U`, then its restriction to `U`
does not vanish at `x`. -/
theorem mem_nonvanishingLocusOn_restrict {X : Scheme.{u}} (U : X.Opens) (N : X.Modules)
    (V : X.Opens) (s : Γ(N, V)) (x : U.toScheme)
    (hx : U.ι.base x ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn N V s) :
    x ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn (N.restrict U.ι) (U.ι ⁻¹ᵁ V)
      ((N.presheaf.map (homOfLE (U.ι.image_preimage_le V)).op).hom s) := by
  have h2 : x ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn
      (Stacks.AmpleLocallyClosed.pullbackModule U.ι N) (U.ι ⁻¹ᵁ V)
      (Stacks.RingedSpace.pullbackUnit U.ι.toLRSHom.toShHom N (op V) s) := by
    rwa [← Stacks.NonvanishingLocusRestrict.preimage_nonvanishingLocusOn U.ι N s]
  rw [pullbackUnit_ι_eq_restrictIsoPullback_hom_app U N V s] at h2
  exact (Stacks.SectionPowerOverOpen.mem_nonvanishingLocusOn_congr_iff _ _ _ h2.1).mp h2


section Theta

variable {S T : Scheme.{u}} {E : S.Modules} [E.IsQuasicoherent] {f : T ⟶ S}
  (P : GradedPowerMap (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E) f)

/-- The restriction of a tensor power of `L` to `U(ψ)` is invertible. -/
instance isInvertibleModule_powK (n : ℤ) :
    Stacks.Ample.IsInvertibleModule P.coveringOpen.toScheme (P.powK n) := by
  have : Stacks.Ample.IsInvertibleModule P.coveringOpen.toScheme
      (Stacks.AmpleLocallyClosed.pullbackModule P.coveringOpen.ι
        (Stacks.AmpleProjectiveImmersion.tensorPowerModule T P.L n)) := inferInstance
  exact Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso
    (Stacks.AmplePullbackPart1.restrictIsoPullback P.coveringOpen _).symm

/-- **The degree-one component of `θ` of [Stacks, Tag 01O9] is an isomorphism**
`r_{L,ψ}^* 𝒪_{𝐏(E)}(1) ≅ L|_{U(ψ)}`, provided every point of `U(ψ)` lies in the nonvanishing open
`U_{ψ(a)}` of the value of `ψ` on some section `a` of `Sym¹(E)` over an open of the base. -/
theorem isIso_theta_one
    (h : ∀ x : P.coveringOpen.toScheme, ∃ (V : S.Opens)
      (a : Γ((Stacks.Tag01VMRelativeVeryAmple.symAlgebra E).piece ((1 : ℕ) : ℤ), V)),
      P.coveringOpen.ι.base x ∈ P.nonvanishingOpenAt 1 V a) :
    IsIso (P.theta.app 1) := by
  have : Stacks.Ample.IsInvertibleModule P.coveringOpen.toScheme
      ((Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn P.L P.coveringOpen).piece 1) :=
    isInvertibleModule_powK P 1
  have hepi : Epi (P.theta.app 1) := by
    refine epi_of_forall_mem_nonvanishingLocusOn _ fun x => ?_
    obtain ⟨V, a, hx⟩ := h x
    refine ⟨P.globalMorphism (relativeProj _) ⁻¹ᵁ ((relativeProj _).toBase ⁻¹ᵁ V),
      Stacks.RingedSpace.pullbackUnit (P.globalMorphism (relativeProj _)).toLRSHom.toShHom
        (GradedPowerMap.Otw _ 1) (op ((relativeProj _).toBase ⁻¹ᵁ V))
        (GradedPowerMap.psiU _ 1 V a), ?_⟩
    have hxV : P.coveringOpen.ι.base x ∈ f ⁻¹ᵁ V := P.nonvanishingOpenAt_le_preimage 1 V a hx
    have h1 : P.coveringOpen.ι.base x ∈ Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn
        (Stacks.AmpleProjectiveImmersion.tensorPowerModule T P.L ((1 : ℕ) : ℤ)) (f ⁻¹ᵁ V)
        ((Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L 1).hom.app (f ⁻¹ᵁ V)
          (P.value 1 V a)) :=
      (Stacks.SectionPowerOverOpen.mem_nonvanishingLocusOn_congr_iff
        (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L 1) (f ⁻¹ᵁ V)
        (P.value 1 V a) hxV).mpr hx
    have h2 := mem_nonvanishingLocusOn_restrict P.coveringOpen _ (f ⁻¹ᵁ V) _ x h1
    have hle : P.toBase ⁻¹ᵁ V ≤
        P.globalMorphism (relativeProj _) ⁻¹ᵁ ((relativeProj _).toBase ⁻¹ᵁ V) :=
      (P.toBase_preimage_eq V).le
    have e : eqToHom (P.toBase_preimage_eq V) = homOfLE hle := Subsingleton.elim _ _
    rw [← P.theta_clauseOne V 1 a, e] at h2
    exact ((Set.ext_iff.mp (Stacks.NonvanishingLocusRestrict.nonvanishingLocusOn_res
      (P.powK 1) hle _) x).mp h2).2
  have hM : Stacks.SheafOfModules.IsInvertible P.coveringOpen.toScheme.presheaf
      P.coveringOpen.toScheme.ringCatSheaf.2
      ((Stacks.Conormal.gradedPullback (P.globalMorphism (relativeProj _))
        (GradedPowerMap.twD (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E)).algebra).piece 1) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
      (inferInstanceAs (Stacks.Ample.IsInvertibleModule P.coveringOpen.toScheme
        ((Scheme.Modules.pullback (P.globalMorphism (relativeProj
          (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E)))).obj
          (Stacks.Tag01VMVeryAmple.twistOne E))))
  have hN : Stacks.SheafOfModules.IsInvertible P.coveringOpen.toScheme.presheaf
      P.coveringOpen.toScheme.ringCatSheaf.2
      ((Stacks.AlgebraicGeometry.ProjChartGradedTriple.laurentOn P.L P.coveringOpen).piece 1) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr this
  exact @Stacks.SheafOfModules.isIso_of_epi_of_isInvertible P.coveringOpen.toScheme.toRingedSpace
    _ _ (P.theta.app 1) hepi hM hN


/-- **The pullback of `𝒪_{𝐏(E)}(1)` along `r_{L,ψ}` is `L`**, when `U(ψ) = T` and the degree-one
values of `ψ` generate `L` everywhere. -/
def pullbackTwistOneIso (hP : P.coveringOpen = ⊤)
    (h : ∀ x : P.coveringOpen.toScheme, ∃ (V : S.Opens)
      (a : Γ((Stacks.Tag01VMRelativeVeryAmple.symAlgebra E).piece ((1 : ℕ) : ℤ), V)),
      P.coveringOpen.ι.base x ∈ P.nonvanishingOpenAt 1 V a) :
    P.L ≅ (Scheme.Modules.pullback (T.topIso.inv ≫ (T.isoOfEq hP).inv ≫
      P.globalMorphism (relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E)))).obj
        (Stacks.Tag01VMVeryAmple.twistOne E) := by
  have := isIso_theta_one P h
  let j : T ⟶ P.coveringOpen.toScheme := T.topIso.inv ≫ (T.isoOfEq hP).inv
  have hj : j ≫ P.coveringOpen.ι = 𝟙 T := by
    simp only [j, Category.assoc, Scheme.isoOfEq_inv_ι, Scheme.toIso_inv_ι]
  let r := P.globalMorphism (relativeProj (Stacks.Tag01VMRelativeVeryAmple.symAlgebra E))
  exact (λ_ P.L).symm ≪≫ (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare P.L 1) ≪≫
    ((Scheme.Modules.pullbackId T).app _).symm ≪≫ ((Scheme.Modules.pullbackCongr hj).app _).symm ≪≫
    ((Scheme.Modules.pullbackComp j P.coveringOpen.ι).app _).symm ≪≫
    (Scheme.Modules.pullback j).mapIso
      (((Scheme.Modules.restrictFunctorIsoPullback P.coveringOpen.ι).app _).symm ≪≫
        (asIso (P.theta.app 1)).symm) ≪≫
    (Scheme.Modules.pullbackComp j r).app _ ≪≫ eqToIso rfl

end Theta

end Stacks.VeryAmpleGlue

end
