module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresentable

/-!
# An affine chart and a prime at a point lying over a closed subscheme of an affine base

Let `X` be an algebraic space with a morphism `h : X ⟶ T` to (the space of) an object `T` of the
big fppf site, `p₀ : T₀ ⟶ T` a morphism of the site, and `x` a point of `X` whose image in `|T|`
comes from `|T₀|`. This file produces the data the proof of [Stacks, Tag 0CX9] starts from: an
affine étale chart `U` of `X` and a prime `𝔭` of `Γ(U)` (the point of `U` over `x`) such that

* `𝔭` lies over a prime of `Γ(T)` coming from `Γ(T₀)`, so contains the image of
  `ker(Γ(T) → Γ(T₀))`;
* `x` lies in the image of every basic-open chart `D(g) ⊂ U` with `g ∉ 𝔭`.

## Main results

* `AlgebraicGeometry.Space.exists_isAffineChart_prime_of_pointsMap_mem_range`.

## References

* [Stacks Project, Tag 0CX9](https://stacks.math.columbia.edu/tag/0CX9)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The prime of `Γ(Z, ⊤)` of a point of a scheme `Z` lies over the prime of its image. -/
theorem toSpecΓ_asIdeal_map {Z Y : Scheme.{u}} (f : Z ⟶ Y) (z : Z) :
    (Y.toSpecΓ (f z)).asIdeal = Ideal.comap f.appTop.hom (Z.toSpecΓ z).asIdeal := by
  have := congrArg (fun k => k z) (Scheme.toSpecΓ_naturality f)
  simp only [Scheme.Hom.comp_apply] at this
  rw [this]
  rfl

/-- A point of a scheme lies in the basic open of `g` exactly when `g` is outside its prime. -/
theorem mem_basicOpen_iff_not_mem_toSpecΓ {Z : Scheme.{u}} (z : Z) (g : Γ(Z, ⊤)) :
    z ∈ Z.basicOpen g ↔ g ∉ (Z.toSpecΓ z).asIdeal := by
  rw [← Scheme.toSpecΓ_preimage_basicOpen]
  rfl

/-- **An affine chart and a prime at a point lying over `T₀`.** -/
theorem exists_isAffineChart_prime_of_pointsMap_mem_range (X : AlgebraicSpaces B S hS)
    {T T₀ : BigFppfOver B S hS} (h : X.1 ⟶ yoneda.obj T) (p₀ : T₀ ⟶ T)
    (x : points B S hS X.1)
    (hx : pointsMap B S hS X.1 h x ∈
      Set.range (pointsMap B S hS (yoneda.obj T₀) (yoneda.map p₀))) :
    ∃ (U : SmallEtale B S hS X.1) (_ : IsAffineChart B S hS X.1 U)
      (P : Ideal Γ(chartScheme U, ⊤)), P.IsPrime ∧
      RingHom.ker (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map p₀)).hom ≤
        P.comap (Scheme.Hom.appTop
          ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (U.1.hom ≫ h)))).hom ∧
      ∀ g : Γ(chartScheme U, ⊤), g ∉ P →
        x ∈ chartPointsRange (X := X) (openChart B S hS X.1 U ((chartScheme U).basicOpen g)) := by
  obtain ⟨W, b, hWaff, hb, w, hw⟩ := exists_affine_etale_chart_at_point B S hS X.1 X.2 x
  let U : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk b, hb⟩
  let Z : Scheme.{u} := (BigFppfOver.toScheme B S hS).obj W
  let s : Z := pointsToScheme B S hS W w
  refine ⟨U, hWaff, (Z.toSpecΓ s).asIdeal, (Z.toSpecΓ s).isPrime, ?_, fun g hg => ?_⟩
  · obtain ⟨t, ht⟩ := hx
    have e1 : pointsMap B S hS X.1 h x =
        pointsMap B S hS (yoneda.obj W) (yoneda.map (yoneda.preimage (U.1.hom ≫ h))) w := by
      rw [yoneda.map_preimage, pointsMap_comp_apply, ← hw]
      rfl
    have e2 := congrArg (pointsToScheme B S hS T) (ht.trans e1)
    rw [pointsToScheme_pointsMap_yoneda, pointsToScheme_pointsMap_yoneda] at e2
    have key : Ideal.comap (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map p₀)).hom
          (((BigFppfOver.toScheme B S hS).obj T₀).toSpecΓ
            (pointsToScheme B S hS T₀ t)).asIdeal =
        Ideal.comap (Scheme.Hom.appTop ((BigFppfOver.toScheme B S hS).map
          (yoneda.preimage (U.1.hom ≫ h)))).hom (Z.toSpecΓ s).asIdeal :=
      (toSpecΓ_asIdeal_map _ _).symm.trans
        ((congrArg (fun z => (Scheme.toSpecΓ _ z).asIdeal) e2).trans (toSpecΓ_asIdeal_map _ _))
    intro a ha
    rw [← key, Ideal.mem_comap, RingHom.mem_ker.1 ha]
    exact Ideal.zero_mem _
  · let O := (chartScheme U).basicOpen g
    obtain ⟨s', hs'⟩ : s ∈ Set.range O.ι := by
      rw [Scheme.Opens.range_ι]
      exact (mem_basicOpen_iff_not_mem_toSpecΓ s g).2 hg
    let w' := (pointsEquivScheme B S hS (openSub W O)).symm s'
    refine ⟨w', ?_⟩
    change pointsMap B S hS (yoneda.obj (openSub W O)) (yoneda.map (openSubHom W O) ≫ b) w' = x
    rw [pointsMap_comp_apply, ← hw]
    congr 1
    apply injective_pointsToScheme B S hS W
    rw [pointsToScheme_pointsMap_yoneda, toScheme_map_openSubHom]
    change O.ι (pointsEquivScheme B S hS (openSub W O) w') = s
    exact (congrArg O.ι (Equiv.apply_symm_apply _ s')).trans hs'

end AlgebraicGeometry.Space

end
