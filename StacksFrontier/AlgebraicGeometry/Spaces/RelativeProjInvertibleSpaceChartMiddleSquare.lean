module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartSquare

/-!
# The square of the scheme factor of the chart maps of Stacks 0D2Z
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.AlgebraicGeometry.ProjChartGradedTriple (laurentOn)
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

universe u m

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

open Stacks.AlgebraicGeometry.ModuleLimits (canHom)
open Stacks.AlgebraicGeometry.RelativeProj

section ChangeTargetValues

variable {Y Y' T : Scheme.{u}} (A : SheafGradedAlgebra.{u} Y) (hs : Y' ⟶ Y)
  {A₁ : SheafGradedAlgebra.{u} Y'}
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A₁)
    (situationAlgebra (A.pullback hs)))
  (hΦ : ∀ n : ℤ, IsIso (Φ.app n))
  {f₀ : T ⟶ Y'} {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
  (χ : Twisting f₀ (situationAlgebra A₁) 1 L)

/-- `thetaChangeSourceIso` as the composite of its factors. -/
theorem thetaChangeSourceIso_eq :
    thetaChangeSourceIso A hs Φ hΦ χ =
      pullbackGradedAlgebraMapIso
          (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le).toLRSHom.toShHom
          (pullbackGradedAlgebraMapIso
            ((toGradedPowerMap χ).globalMorphism (relativeProj A₁)).toLRSHom.toShHom
            (RelativeProjBaseChangeTwist.congrBaseChangeTwistIso A hs Φ hΦ
              (changeTargetProj A hs Φ hΦ) rfl).symm) ≪≫
        GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso _
          (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le)
          ((toGradedPowerMap χ).globalMorphism (relativeProj A₁)) ≪≫
        GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso _
          (T.homOfLE (coveringOpen_changeTarget A hs Φ hΦ χ).le ≫
            (toGradedPowerMap χ).globalMorphism (relativeProj A₁))
          (changeTargetProj A hs Φ hΦ) ≪≫
        GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso _
          (homOfLE_globalMorphism_changeTarget A hs Φ hΦ χ) :=
  rfl

variable {f' : T ⟶ Y} (h : f₀ ≫ hs = f')
  {ζ : Twisting f' (situationAlgebra A) 1 L}
  (hζ : ζ = Twisting.congrBase h (changeTarget A hs Φ hΦ χ))

/-- `thetaChangeSourceIsoOfEq` as the composite of its factors. -/
theorem thetaChangeSourceIsoOfEq_eq :
    thetaChangeSourceIsoOfEq A hs Φ hΦ χ h hζ =
      pullbackGradedAlgebraMapIso
          (T.homOfLE (coveringOpen_changeTarget_of_eq A hs Φ hΦ χ h hζ).le).toLRSHom.toShHom
          (pullbackGradedAlgebraMapIso
            ((toGradedPowerMap χ).globalMorphism (relativeProj A₁)).toLRSHom.toShHom
            (RelativeProjBaseChangeTwist.congrBaseChangeTwistIso A hs Φ hΦ
              (changeTargetProj A hs Φ hΦ) rfl).symm) ≪≫
        GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso _
          (T.homOfLE (coveringOpen_changeTarget_of_eq A hs Φ hΦ χ h hζ).le)
          ((toGradedPowerMap χ).globalMorphism (relativeProj A₁)) ≪≫
        GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso _
          (T.homOfLE (coveringOpen_changeTarget_of_eq A hs Φ hΦ χ h hζ).le ≫
            (toGradedPowerMap χ).globalMorphism (relativeProj A₁))
          (changeTargetProj A hs Φ hΦ) ≪≫
        GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso _
          (homOfLE_globalMorphism_changeTarget_of_eq A hs Φ hΦ χ h hζ) :=
  rfl

end ChangeTargetValues

section PullbackOfEqValues

variable {S X W : Scheme.{u}} {A : SheafGradedAlgebra.{u} S} {f : X ⟶ S}
  {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
  (ψ : Twisting f (situationAlgebra A) 1 L) (q : W ⟶ X) {f₂ : W ⟶ S} (h : q ≫ f = f₂)
  {χ₂ : Twisting f₂ (situationAlgebra A) 1 ((pullbackFunctor (ringedSpaceHom q)).obj L)}
  (hχ : χ₂ = Twisting.congrBase h (ψ.pullback q))

/-- `thetaSourceIsoOfEq` as the composite of its factors. -/
theorem thetaSourceIsoOfEq_eq :
    thetaSourceIsoOfEq ψ q h hχ =
      GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso (GradedPowerMap.twD A).algebra
          (coveringOpenPullbackOfEq ψ q h hχ)
          ((toGradedPowerMap ψ).globalMorphism (relativeProj A)) ≪≫
        GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso (GradedPowerMap.twD A).algebra
          (coveringOpenPullbackOfEq_globalMorphism ψ q h hχ) :=
  rfl

end PullbackOfEqValues

section SquareChainInv

variable {U₀ U₂ Uχ Uψ : Scheme.{u}} {k : U₀ ⟶ Uχ} {n : U₀ ⟶ U₂} {k₂ : U₂ ⟶ Uχ}
  {j₂ : U₂ ⟶ Uψ} {j : U₀ ⟶ Uψ} (hk : n ≫ k₂ = k) (hj : n ≫ j₂ = j)

/-- The degree-`d` component of the inverse of `squareChainIso`, written out, with the components
of the given identifications as variables. -/
theorem squareChainIso_inv_app
    {A₀ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf U₀.toRingedSpace)}
    {A₂ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf U₂.toRingedSpace)}
    {Aχ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Uχ.toRingedSpace)}
    {Aψ : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf Uψ.toRingedSpace)}
    (S₁ : pullbackGradedAlgebra k.toLRSHom.toShHom Aχ ≅ A₀)
    (S₂ : pullbackGradedAlgebra k₂.toLRSHom.toShHom Aχ ≅ A₂)
    (S₄ : pullbackGradedAlgebra j₂.toLRSHom.toShHom Aψ ≅ A₂) (d : ℤ)
    (S₁d : @SheafOfModules.GradedAlgebra.piece _ _ _ U₀.ringCatSheaf A₀ d ⟶
      (Scheme.Modules.pullback k).obj
        (@SheafOfModules.GradedAlgebra.piece _ _ _ Uχ.ringCatSheaf Aχ d)) (hS₁ : S₁.inv.app d = S₁d)
    (S₂d : (Scheme.Modules.pullback k₂).obj
        (@SheafOfModules.GradedAlgebra.piece _ _ _ Uχ.ringCatSheaf Aχ d) ⟶
      @SheafOfModules.GradedAlgebra.piece _ _ _ U₂.ringCatSheaf A₂ d)
    (hS₂ : S₂.hom.app d = S₂d)
    (S₄d : @SheafOfModules.GradedAlgebra.piece _ _ _ U₂.ringCatSheaf A₂ d ⟶
      (Scheme.Modules.pullback j₂).obj
        (@SheafOfModules.GradedAlgebra.piece _ _ _ Uψ.ringCatSheaf Aψ d))
        (hS₄ : S₄.inv.app d = S₄d) :
    (squareChainIso hk hj S₁ S₂ S₄).inv.app d =
      S₁d ≫ (Scheme.Modules.pullbackCongr hk).inv.app
          (@SheafOfModules.GradedAlgebra.piece _ _ _ Uχ.ringCatSheaf Aχ d) ≫
        (Scheme.Modules.pullbackComp n k₂).inv.app
          (@SheafOfModules.GradedAlgebra.piece _ _ _ Uχ.ringCatSheaf Aχ d) ≫
        (Scheme.Modules.pullback n).map (S₂d ≫ S₄d) ≫
        (Scheme.Modules.pullbackComp n j₂).hom.app
          (@SheafOfModules.GradedAlgebra.piece _ _ _ Uψ.ringCatSheaf Aψ d) ≫
        (Scheme.Modules.pullbackCongr hj).hom.app
          (@SheafOfModules.GradedAlgebra.piece _ _ _ Uψ.ringCatSheaf Aψ d) := by
  subst hS₁ hS₂ hS₄
  rfl

end SquareChainInv

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

namespace AlgebraicGeometry.Space

open Stacks.AlgebraicGeometry.ModuleLimits (canHom)
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

/-- The degree-`n` component of an isomorphism of sheaves of graded algebras on a scheme. -/
def schemeGradedIsoApp {Y : Scheme.{u}}
    {G H : SheafOfModules.GradedAlgebra.{u, u}
          (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace)}
    (e : G ≅ H) (n : ℤ) :
    @SheafOfModules.GradedAlgebra.piece _ _ _ Y.ringCatSheaf G n ≅
      @SheafOfModules.GradedAlgebra.piece _ _ _ Y.ringCatSheaf H n where
  hom := e.hom.app n
  inv := e.inv.app n
  hom_inv_id := congrArg (fun g => SheafOfModules.GradedAlgebra.Hom.app g n) e.hom_inv_id
  inv_hom_id := congrArg (fun g => SheafOfModules.GradedAlgebra.Hom.app g n) e.inv_hom_id

/-- **The square-chain identification of the inverse images of the twists, through the
comparisons of Stacks 03LU**: `AlgebraicGeometry.Space.canHom_squareChain_coherence` with the
inverses of the canonical identifications written as inverse transports followed by inverse
comparisons, and the identification `B` given as a variable with its value, grouped as the
inverse of `…RelativeProjInvertibleMorphism.squareChainIso` unfolds. -/
theorem canHom_squareChain_coherence_of_eq {Usq U₂ Uat Pw Px Px' Ux : Scheme.{u}}
    (rsq : Usq ⟶ Px') (ym : Px' ⟶ Px) (l : Usq ⟶ Ux) (rx : Ux ⟶ Px) (n : Usq ⟶ U₂)
    (k₂ : U₂ ⟶ Uat) (k : Usq ⟶ Uat) (j₂ : U₂ ⟶ Ux) (rat : Uat ⟶ Pw) (pc₁ : Pw ⟶ Px')
    (pc₂ : Pw ⟶ Px) (rtc : U₂ ⟶ Px)
    (hk' : n ≫ k₂ = k) (hj' : n ≫ j₂ = l) (h8 : (k ≫ rat) ≫ pc₁ = rsq)
    (h9 : (k₂ ≫ rat) ≫ pc₂ = rtc) (h10 : j₂ ≫ rx = rtc) (hcomp : pc₁ ≫ ym = pc₂)
    (H₁ : rsq ≫ ym = l ≫ rx)
    {X : Px.Modules} {X' : Px'.Modules} {W : Pw.Modules}
    (cy : (Scheme.Modules.pullback ym).obj X ≅ X') (c1 : (Scheme.Modules.pullback pc₁).obj X' ≅ W)
    (c2 : (Scheme.Modules.pullback pc₂).obj X ≅ W)
    (hc : c2.hom = (Scheme.Modules.pullbackCongr hcomp).inv.app X ≫
      (Scheme.Modules.pullbackComp pc₁ ym).inv.app X ≫
      (Scheme.Modules.pullback pc₁).map cy.hom ≫ c1.hom)
    (Bi : (Scheme.Modules.pullback rsq).obj X' ⟶
      (Scheme.Modules.pullback l).obj ((Scheme.Modules.pullback rx).obj X))
    (hBi : Bi = ((Scheme.Modules.pullbackCongr h8).inv.app X' ≫
        (Scheme.Modules.pullbackComp (k ≫ rat) pc₁).inv.app X' ≫
        (Scheme.Modules.pullbackComp k rat).inv.app ((Scheme.Modules.pullback pc₁).obj X') ≫
        (Scheme.Modules.pullback k).map ((Scheme.Modules.pullback rat).map c1.hom)) ≫
      (Scheme.Modules.pullbackCongr hk').inv.app ((Scheme.Modules.pullback rat).obj W) ≫
      (Scheme.Modules.pullbackComp n k₂).inv.app ((Scheme.Modules.pullback rat).obj W) ≫
      (Scheme.Modules.pullback n).map
        (((Scheme.Modules.pullback k₂).map ((Scheme.Modules.pullback rat).map c2.inv) ≫
            (Scheme.Modules.pullbackComp k₂ rat).hom.app ((Scheme.Modules.pullback pc₂).obj X) ≫
            (Scheme.Modules.pullbackComp (k₂ ≫ rat) pc₂).hom.app X ≫
            (Scheme.Modules.pullbackCongr h9).hom.app X) ≫
          (Scheme.Modules.pullbackCongr h10).inv.app X ≫
          (Scheme.Modules.pullbackComp j₂ rx).inv.app X) ≫
      (Scheme.Modules.pullbackComp n j₂).hom.app ((Scheme.Modules.pullback rx).obj X) ≫
      (Scheme.Modules.pullbackCongr hj').hom.app ((Scheme.Modules.pullback rx).obj X)) :
    (Scheme.Modules.pullback rsq).map cy.hom ≫ Bi =
      canHom rsq ym (l ≫ rx) H₁ X ≫ (Scheme.Modules.pullbackComp l rx).inv.app X := by
  subst hBi
  have key := canHom_squareChain_coherence rsq ym l rx n k₂ k j₂ rat pc₁ pc₂ rtc hk' hj' h8 h9
    h10 hcomp H₁ cy c1 c2 (hc.trans (by rw [inv_canHom_eq, Category.assoc]))
  have e1 : ∀ {A C : Scheme.{u}} (a : A ⟶ C) (F : C.Modules),
      (Scheme.Modules.pullbackCongr (rfl : a = a)).inv.app F = 𝟙 _ := fun _ _ => rfl
  have e2 : ∀ {A C : Scheme.{u}} (a : A ⟶ C) (F : C.Modules),
      (Scheme.Modules.pullbackCongr (rfl : a = a)).hom.app F = 𝟙 _ := fun _ _ => rfl
  simp only [inv_canHom_eq] at key
  simp only [canHom, e1, e2, Category.id_comp, Category.comp_id, Functor.map_comp,
    Category.assoc] at key ⊢
  exact key

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

open Stacks.AlgebraicGeometry.ModuleLimits (canHom)

/-- The degree-`d` form of a cocycle of comparisons of twists: an identification
`E₂ = (pc₂ = pc₁ ≫ y_P) ≪≫ (pc₁^*y_P^* ≅ (pc₁ ≫ y_P)^*)⁻¹ ≪≫ pc₁^*E_y ≪≫ E₁` of sheaves of graded
algebras, read in degree `d`. -/
theorem gradedIso_hom_app_eq_of_eq_trans {Pw Px Px' : Scheme.{u}} (pc₁ : Pw ⟶ Px') (ym : Px' ⟶ Px)
    {pc₂ : Pw ⟶ Px} (hcomp : pc₂ = pc₁ ≫ ym)
    {G : SheafOfModules.GradedAlgebra.{u, u}
          (Stacks.RingedSpace.structureRingSheaf Px.toRingedSpace)}
    {G' : SheafOfModules.GradedAlgebra.{u, u}
          (Stacks.RingedSpace.structureRingSheaf Px'.toRingedSpace)}
    {Gw : SheafOfModules.GradedAlgebra.{u, u}
          (Stacks.RingedSpace.structureRingSheaf Pw.toRingedSpace)}
    (Ey : pullbackGradedAlgebra ym.toLRSHom.toShHom G ≅ G')
    (E₁ : pullbackGradedAlgebra pc₁.toLRSHom.toShHom G' ≅ Gw)
    (E₂ : pullbackGradedAlgebra pc₂.toLRSHom.toShHom G ≅ Gw)
    (h : E₂ = Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso _
        hcomp ≪≫
      (Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso _
        pc₁ ym).symm ≪≫ pullbackGradedAlgebraMapIso _ Ey ≪≫ E₁) (d : ℤ) :
    E₂.hom.app d = (Scheme.Modules.pullbackCongr hcomp.symm).inv.app (G.piece d) ≫
      (Scheme.Modules.pullbackComp pc₁ ym).inv.app (G.piece d) ≫
      (Scheme.Modules.pullback pc₁).map (Ey.hom.app d) ≫ E₁.hom.app d := by
  subst h hcomp
  rfl

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

/-- The square `r_sq ≫ y_P = l ≫ r_x` of the square chain, from its pieces. -/
theorem squareChain_comp_eq {Usq U₂ Uat Pw Px Px' Ux : Scheme.{u}}
    (rsq : Usq ⟶ Px') (ym : Px' ⟶ Px) (l : Usq ⟶ Ux) (rx : Ux ⟶ Px) (n : Usq ⟶ U₂)
    (k₂ : U₂ ⟶ Uat) (k : Usq ⟶ Uat) (j₂ : U₂ ⟶ Ux) (rat : Uat ⟶ Pw) (pc₁ : Pw ⟶ Px')
    (pc₂ : Pw ⟶ Px) (rtc : U₂ ⟶ Px)
    (hk' : n ≫ k₂ = k) (hj' : n ≫ j₂ = l) (h8 : (k ≫ rat) ≫ pc₁ = rsq)
    (h9 : (k₂ ≫ rat) ≫ pc₂ = rtc) (h10 : j₂ ≫ rx = rtc) (hcomp : pc₁ ≫ ym = pc₂) :
    rsq ≫ ym = l ≫ rx := by
  subst h8 hj' hk' h10 hcomp
  simp only [Category.assoc] at h9 ⊢
  rw [h9]

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

open Stacks.AlgebraicGeometry.ModuleLimits (canHom)
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp
  (pullbackGradedAlgebraCompIso pullbackGradedAlgebraCongrIso)

/-- **The square-chain identification of the sources of `θ`, against a comparison of twists.**
Let `n ≫ k₂ = k`, `n ≫ j₂ = l`, `(k ≫ r) ≫ p₁ = r_sq`, `(k₂ ≫ r) ≫ p₂ = r_c`, `j₂ ≫ r_x = r_c` and
`p₁ ≫ y_P = p₂`, and let `E_y : y_P^*G ≅ G'`, `E₁ : p₁^*G' ≅ G_w`, `E₂ : p₂^*G ≅ G_w` be
isomorphisms of sheaves of graded algebras with `E₂` the contraction followed by `p₁^*E_y` and
`E₁`.  For the identifications `S₁ : k^*r^*G_w ≅ r_sq^*G'`, `S₂ : k₂^*r^*G_w ≅ r_c^*G` (through
`E₁`, `E₂` and the comparisons of Stacks 03LU) and `S₄ : j₂^*r_x^*G ≅ r_c^*G`, the inverse image
along `r_sq` of `E_y` followed by the inverse of the assembled identification
`squareChainIso S₁ S₂ S₄ : l^*r_x^*G ≅ r_sq^*G'` is, in every degree, the canonical identification
`r_sq^*(y_P^*G_d) ⟶ l^*(r_x^*G_d)` of Stacks 01ZR (2). -/
theorem pullback_map_comp_squareChainIso_inv_app {Usq U₂ Uat Pw Px Px' Ux : Scheme.{u}}
    (rsq : Usq ⟶ Px') (ym : Px' ⟶ Px) (l : Usq ⟶ Ux) (rx : Ux ⟶ Px) (n : Usq ⟶ U₂)
    (k₂ : U₂ ⟶ Uat) (k : Usq ⟶ Uat) (j₂ : U₂ ⟶ Ux) (rat : Uat ⟶ Pw) (pc₁ : Pw ⟶ Px')
    (pc₂ : Pw ⟶ Px) (rtc : U₂ ⟶ Px)
    (hk' : n ≫ k₂ = k) (hj' : n ≫ j₂ = l) (h8 : (k ≫ rat) ≫ pc₁ = rsq)
    (h9 : (k₂ ≫ rat) ≫ pc₂ = rtc) (h10 : j₂ ≫ rx = rtc) (hcomp : pc₁ ≫ ym = pc₂)
    (H₁ : rsq ≫ ym = l ≫ rx)
    {G : SheafOfModules.GradedAlgebra.{u, u}
          (Stacks.RingedSpace.structureRingSheaf Px.toRingedSpace)}
    {G' : SheafOfModules.GradedAlgebra.{u, u}
          (Stacks.RingedSpace.structureRingSheaf Px'.toRingedSpace)}
    {Gw : SheafOfModules.GradedAlgebra.{u, u}
          (Stacks.RingedSpace.structureRingSheaf Pw.toRingedSpace)}
    (Ey : pullbackGradedAlgebra ym.toLRSHom.toShHom G ≅ G')
    (E₁ : pullbackGradedAlgebra pc₁.toLRSHom.toShHom G' ≅ Gw)
    (E₂ : pullbackGradedAlgebra pc₂.toLRSHom.toShHom G ≅ Gw)
    (hE : E₂ = pullbackGradedAlgebraCongrIso _ hcomp.symm ≪≫
      (pullbackGradedAlgebraCompIso _ pc₁ ym).symm ≪≫ pullbackGradedAlgebraMapIso _ Ey ≪≫ E₁)
    (S₁ : pullbackGradedAlgebra k.toLRSHom.toShHom (pullbackGradedAlgebra rat.toLRSHom.toShHom Gw) ≅
      pullbackGradedAlgebra rsq.toLRSHom.toShHom G')
    (hS₁ : S₁ = pullbackGradedAlgebraMapIso k.toLRSHom.toShHom
        (pullbackGradedAlgebraMapIso rat.toLRSHom.toShHom E₁.symm) ≪≫
      pullbackGradedAlgebraCompIso _ k rat ≪≫ pullbackGradedAlgebraCompIso _ (k ≫ rat) pc₁ ≪≫
      pullbackGradedAlgebraCongrIso _ h8)
    (S₂ : pullbackGradedAlgebra k₂.toLRSHom.toShHom
          (pullbackGradedAlgebra rat.toLRSHom.toShHom Gw) ≅
      pullbackGradedAlgebra rtc.toLRSHom.toShHom G)
    (hS₂ : S₂ = pullbackGradedAlgebraMapIso k₂.toLRSHom.toShHom
        (pullbackGradedAlgebraMapIso rat.toLRSHom.toShHom E₂.symm) ≪≫
      pullbackGradedAlgebraCompIso _ k₂ rat ≪≫ pullbackGradedAlgebraCompIso _ (k₂ ≫ rat) pc₂ ≪≫
      pullbackGradedAlgebraCongrIso _ h9)
    (S₄ : pullbackGradedAlgebra j₂.toLRSHom.toShHom (pullbackGradedAlgebra rx.toLRSHom.toShHom G) ≅
      pullbackGradedAlgebra rtc.toLRSHom.toShHom G)
    (hS₄ : S₄ = pullbackGradedAlgebraCompIso _ j₂ rx ≪≫ pullbackGradedAlgebraCongrIso _ h10)
    (Bs : pullbackGradedAlgebra l.toLRSHom.toShHom (pullbackGradedAlgebra rx.toLRSHom.toShHom G) ≅
      pullbackGradedAlgebra rsq.toLRSHom.toShHom G')
    (hB : Bs = squareChainIso hk' hj' S₁ S₂ S₄)
    (d : ℤ) :
    (Scheme.Modules.pullback rsq).map (Ey.hom.app d) ≫ Bs.inv.app d =
      canHom rsq ym (l ≫ rx) H₁ (G.piece d) ≫
        (Scheme.Modules.pullbackComp l rx).inv.app (G.piece d) := by
  subst hB hS₁ hS₂ hS₄
  exact canHom_squareChain_coherence_of_eq rsq ym l rx n k₂ k j₂ rat pc₁ pc₂ rtc hk' hj' h8 h9
    h10 hcomp H₁ (schemeGradedIsoApp Ey d) (schemeGradedIsoApp E₁ d) (schemeGradedIsoApp E₂ d)
    (gradedIso_hom_app_eq_of_eq_trans pc₁ ym hcomp.symm Ey E₁ E₂ hE d) _
    (squareChainIso_inv_app hk' hj' _ _ _ d _ rfl _ rfl _ rfl)

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

open Stacks.AlgebraicGeometry.ModuleLimits (canHom)

/-- Two composites `c_y ↦ r^*c_y ≫ B` agree up to the identification of their equal sources and
targets (used to compare two spellings of the same morphism without unfolding it). -/
theorem pullback_map_comp_heq {U V : Scheme.{u}} {r : U ⟶ V} {A A' Y Y' : V.Modules}
    {Z Z' : U.Modules} (hA : A = A') (hY : Y = Y') (hZ : Z = Z') {c : A ⟶ Y} {c' : A' ⟶ Y'}
    (hc : HEq c c') {B : (Scheme.Modules.pullback r).obj Y ⟶ Z}
    {B' : (Scheme.Modules.pullback r).obj Y' ⟶ Z'} (hB : HEq B B') :
    HEq ((Scheme.Modules.pullback r).map c ≫ B) ((Scheme.Modules.pullback r).map c' ≫ B') := by
  subst hA hY hZ
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hB
  rfl

/-- The canonical identification of Stacks 01ZR (2) followed by the inverse contraction of
Stacks 03LU, for equal data. -/
theorem canHom_comp_pullbackComp_inv_app_heq {Usq Px' Ux P P' : Scheme.{u}} {rsq : Usq ⟶ Px'}
    {l : Usq ⟶ Ux} (hP : P = P') {ym : Px' ⟶ P} {ym' : Px' ⟶ P'} (hym : HEq ym ym')
    {rx : Ux ⟶ P} {rx' : Ux ⟶ P'} (hrx : HEq rx rx') {H : rsq ≫ ym = l ≫ rx}
    {H' : rsq ≫ ym' = l ≫ rx'} {X : P.Modules} {X' : P'.Modules} (hX : HEq X X') :
    HEq (canHom rsq ym (l ≫ rx) H X ≫ (Scheme.Modules.pullbackComp l rx).inv.app X)
      (canHom rsq ym' (l ≫ rx') H' X' ≫ (Scheme.Modules.pullbackComp l rx').inv.app X') := by
  subst hP
  obtain rfl := eq_of_heq hym
  obtain rfl := eq_of_heq hrx
  obtain rfl := eq_of_heq hX
  rfl

/-- The inverse transport along `j ≫ r = q` followed by the inverse contraction of Stacks 03LU,
for equal data. -/
theorem pullbackCongr_inv_app_comp_pullbackComp_inv_app_heq {U V P P' : Scheme.{u}} {j : U ⟶ V}
    (hP : P = P') {r : V ⟶ P} {r' : V ⟶ P'} (hr₀ : HEq r r') {q : U ⟶ P} {q' : U ⟶ P'}
    (hq : HEq q q') {hr : j ≫ r = q} {hr' : j ≫ r' = q'} {X : P.Modules} {X' : P'.Modules}
    (hX : HEq X X') :
    HEq ((Scheme.Modules.pullbackCongr hr).inv.app X ≫ (Scheme.Modules.pullbackComp j r).inv.app X)
      ((Scheme.Modules.pullbackCongr hr').inv.app X' ≫
        (Scheme.Modules.pullbackComp j r').inv.app X') := by
  subst hP
  obtain rfl := eq_of_heq hr₀
  obtain rfl := eq_of_heq hq
  obtain rfl := eq_of_heq hX
  rfl

/-- `AlgebraicGeometry.Space.source_square_coherence_of_squareChain` with the identification `B`
characterised through the inverse contraction `l^*r_x^* ≅ (l ≫ r_x)^*` of Stacks 03LU, and the
leading factor `A` of the source identification at `x'` given as a variable with its value. -/
theorem source_square_coherence_of_squareChain_of_value
    {T T' Fx Fx' Px Px' Ux Ux' Usq : Scheme.{u}}
    (τ : T' ⟶ T) (cx : T ⟶ Fx)
    (tx : Fx ⟶ Px) (gx : T ⟶ Ux) (rx : Ux ⟶ Px) (cx' : T' ⟶ Fx') (tx' : Fx' ⟶ Px')
    (gx' : T' ⟶ Ux') (rx' : Ux' ⟶ Px') (j : Ux' ⟶ Usq) (l : Usq ⟶ Ux) (rsq : Usq ⟶ Px')
    (y : Fx' ⟶ Fx) (ym : Px' ⟶ Px)
    (h1 : cx ≫ tx = gx ≫ rx) (h2 : cx' ≫ tx' = gx' ≫ rx') (hk : τ ≫ gx = gx' ≫ j ≫ l)
    (h4 : τ ≫ cx = cx' ≫ y) (h5 : y ≫ tx = tx' ≫ ym) (hr : j ≫ rsq = rx')
    (H₁ : rsq ≫ ym = l ≫ rx) {X : Px.Modules} {X' : Px'.Modules}
    (cy : (Scheme.Modules.pullback ym).obj X ⟶ X')
    (Bi : (Scheme.Modules.pullback rsq).obj X' ⟶
      (Scheme.Modules.pullback l).obj ((Scheme.Modules.pullback rx).obj X))
    (hBi : (Scheme.Modules.pullback rsq).map cy ≫ Bi =
      canHom rsq ym (l ≫ rx) H₁ X ≫ (Scheme.Modules.pullbackComp l rx).inv.app X)
    (Ai : (Scheme.Modules.pullback rx').obj X' ⟶
      (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback rsq).obj X'))
    (hAi : Ai = (Scheme.Modules.pullbackCongr hr).inv.app X' ≫
      (Scheme.Modules.pullbackComp j rsq).inv.app X')
    (E4 : (Scheme.Modules.pullback (τ ≫ cx)).obj ((Scheme.Modules.pullback tx).obj X) =
      (Scheme.Modules.pullback (cx' ≫ y)).obj ((Scheme.Modules.pullback tx).obj X)) :
    (Scheme.Modules.pullback τ).map ((Scheme.Modules.pullbackComp cx tx).hom.app X ≫
        (Scheme.Modules.pullbackCongr h1).hom.app X ≫
        (Scheme.Modules.pullbackComp gx rx).inv.app X) ≫
        ((Scheme.Modules.pullbackComp τ gx).hom.app ((Scheme.Modules.pullback rx).obj X) ≫
          (Scheme.Modules.pullbackCongr hk).hom.app ((Scheme.Modules.pullback rx).obj X) ≫
          (Scheme.Modules.pullbackComp gx' (j ≫ l)).inv.app ((Scheme.Modules.pullback rx).obj X) ≫
          (Scheme.Modules.pullback gx').map
            ((Scheme.Modules.pullbackComp j l).inv.app ((Scheme.Modules.pullback rx).obj X))) =
      ((Scheme.Modules.pullbackComp τ cx).hom.app ((Scheme.Modules.pullback tx).obj X) ≫
          eqToHom E4 ≫
          (Scheme.Modules.pullbackComp cx' y).inv.app ((Scheme.Modules.pullback tx).obj X) ≫
          (Scheme.Modules.pullback cx').map ((Scheme.Modules.pullbackComp y tx).hom.app X ≫
            (Scheme.Modules.pullbackCongr h5).hom.app X ≫
            (Scheme.Modules.pullbackComp tx' ym).inv.app X ≫
            (Scheme.Modules.pullback tx').map cy)) ≫
        ((Scheme.Modules.pullbackComp cx' tx').hom.app X' ≫
          (Scheme.Modules.pullbackCongr h2).hom.app X' ≫
          (Scheme.Modules.pullbackComp gx' rx').inv.app X') ≫
        (Scheme.Modules.pullback gx').map Ai ≫
        (Scheme.Modules.pullback gx').map ((Scheme.Modules.pullback j).map Bi) := by
  subst hAi
  exact source_square_coherence_of_squareChain τ cx tx gx rx cx' tx' gx' rx' j l rsq y ym
    h1 h2 hk h4 h5 hr H₁ cy Bi
    (hBi.trans (congrArg (_ ≫ ·) (pullbackComp_inv_app_eq_inv_canHom l rx X))) E4

section SourceFactors

local notation "pb" => Scheme.Modules.pullback
local notation "pC" => Scheme.Modules.pullbackComp
local notation "pCg" => Scheme.Modules.pullbackCongr

/-- **The source coherence of the square of the chart maps, with every factor a variable.**
`AlgebraicGeometry.Space.source_square_coherence_of_squareChain_of_value` restated in the exact
shape of the source hypothesis of
`AlgebraicGeometry.Space.pullback_map_comp_eq_of_theta_eq_of_factors`: every object and every
factor of that hypothesis (`M`, `M₂`, `M₃`, `Bi`, `Ai`, `e₁ … e₃'`, `σ`) is a variable, identified
with its value by an equation (objects) or a heterogeneous equation (morphisms).  The values are
written over separate copies of the data (for the twist at `x'`, for `σ`, for `Ai` and for `Bi`),
each tied to the main copy by equations of schemes and heterogeneous equations of morphisms and
modules, so that at a use every argument is a variable, `rfl` or `HEq.rfl`, each slot keeping its
own spelling of the data.  The proof is substitution followed by
`…source_square_coherence_of_squareChain_of_value`. -/
theorem source_square_coherence_of_factors
    {T T' Fx Fx' Px Px' Ux Ux' Usq : Scheme.{u}}
    (τ : T' ⟶ T) (g : T ⟶ Ux) (g' : T' ⟶ Ux') (j : Ux' ⟶ Usq) (l : Usq ⟶ Ux)
    (hk : τ ≫ g = g' ≫ j ≫ l)
    {M : Ux.Modules} {M₂ : Usq.Modules} {M₃ : Ux'.Modules}
    (Bi : M₂ ⟶ (pb l).obj M) (Ai : M₃ ⟶ (pb j).obj M₂)
    {P₀ P₀' P₀'' : T.Modules} (e₁ : P₀ ⟶ P₀') (e₂ : P₀' ⟶ P₀'') (e₃ : P₀'' ⟶ (pb g).obj M)
    {P₁ P₁' P₁'' : T'.Modules} (e₁' : P₁ ⟶ P₁') (e₂' : P₁' ⟶ P₁'')
    (e₃' : P₁'' ⟶ (pb g').obj M₃) (σ : (pb τ).obj P₀ ⟶ P₁)
    (cx : T ⟶ Fx) (tx : Fx ⟶ Px) (rx : Ux ⟶ Px) (cx' : T' ⟶ Fx') (tx' : Fx' ⟶ Px')
    (rx' : Ux' ⟶ Px') (rsq : Usq ⟶ Px') (y : Fx' ⟶ Fx) (ym : Px' ⟶ Px)
    (h1 : cx ≫ tx = g ≫ rx) (h2 : cx' ≫ tx' = g' ≫ rx') (h4 : τ ≫ cx = cx' ≫ y)
    (X : Px.Modules) (X' : Px'.Modules) (cy : (pb ym).obj X ⟶ X')
    (hM : M = (pb rx).obj X) (hM₂ : M₂ = (pb rsq).obj X') (hM₃ : M₃ = (pb rx').obj X')
    (hP₀ : P₀ = (pb tx ⋙ pb cx).obj X) (hP₀' : P₀' = (pb (cx ≫ tx)).obj X)
    (hP₀'' : P₀'' = (pb (g ≫ rx)).obj X)
    (hP₁ : P₁ = (pb tx' ⋙ pb cx').obj X') (hP₁' : P₁' = (pb (cx' ≫ tx')).obj X')
    (hP₁'' : P₁'' = (pb (g' ≫ rx')).obj X')
    (he₁ : HEq e₁ ((pC cx tx).hom.app X)) (he₂ : HEq e₂ ((pCg h1).hom.app X))
    (he₃ : HEq e₃ ((pC g rx).inv.app X))
    (he₁' : HEq e₁' ((pC cx' tx').hom.app X')) (he₂' : HEq e₂' ((pCg h2).hom.app X'))
    {Ux'₃ Px'₃ : Scheme.{u}} (g'₃ : T' ⟶ Ux'₃) (rx'₃ : Ux'₃ ⟶ Px'₃) (X'₃ : Px'₃.Modules)
    (he₃' : HEq e₃' ((pC g'₃ rx'₃).inv.app X'₃))
    (hUx'₃ : Ux'₃ = Ux') (hPx'₃ : Px'₃ = Px') (hg'₃ : HEq g'₃ g') (hrx'₃ : HEq rx'₃ rx')
    (hX'₃ : HEq X'₃ X')
    {Fx₄ Px₄ Fx'₄ Px'₄ : Scheme.{u}} (cx₄ : T ⟶ Fx₄) (tx₄ : Fx₄ ⟶ Px₄) (cx'₄ : T' ⟶ Fx'₄)
    (tx'₄ : Fx'₄ ⟶ Px'₄) (y₄ : Fx'₄ ⟶ Fx₄) (ym₄ : Px'₄ ⟶ Px₄) (h5₄ : y₄ ≫ tx₄ = tx'₄ ≫ ym₄)
    (X₄ : Px₄.Modules) (X'₄ : Px'₄.Modules) (cy₄ : (pb ym₄).obj X₄ ⟶ X'₄)
    (E4₄ : (pb (τ ≫ cx₄)).obj ((pb tx₄).obj X₄) = (pb (cx'₄ ≫ y₄)).obj ((pb tx₄).obj X₄))
    (hσ : HEq σ ((pC τ cx₄).hom.app ((pb tx₄).obj X₄) ≫ eqToHom E4₄ ≫
      (pC cx'₄ y₄).inv.app ((pb tx₄).obj X₄) ≫
      (pb cx'₄).map ((pC y₄ tx₄).hom.app X₄ ≫ (pCg h5₄).hom.app X₄ ≫ (pC tx'₄ ym₄).inv.app X₄ ≫
        (pb tx'₄).map cy₄)))
    (hFx₄ : Fx₄ = Fx) (hPx₄ : Px₄ = Px) (hFx'₄ : Fx'₄ = Fx') (hPx'₄ : Px'₄ = Px')
    (hcx₄ : HEq cx₄ cx) (htx₄ : HEq tx₄ tx) (hcx'₄ : HEq cx'₄ cx') (htx'₄ : HEq tx'₄ tx')
    (hy₄ : HEq y₄ y) (hym₄ : HEq ym₄ ym) (hX₄ : HEq X₄ X) (hX'₄ : HEq X'₄ X')
    (hcy₄ : HEq cy₄ cy)
    {S₅ T₅ : Scheme.{u}} {A₅ : SheafGradedAlgebra.{u} S₅} {f₅ : T₅ ⟶ S₅}
    (P₅ : GradedPowerMap A₅ f₅) {U₅ : T₅.Opens} (hU₅ : U₅ ≤ P₅.coveringOpen)
    {r'₅ : U₅.toScheme ⟶ (relativeProj A₅).scheme}
    (hr₅ : T₅.homOfLE hU₅ ≫ P₅.globalMorphism (relativeProj A₅) = r'₅) (d₅ : ℤ)
    (hAi : HEq Ai ((P₅.thetaTransportSourceIso hU₅ hr₅).inv.app d₅))
    (hUx'₅ : U₅.toScheme = Ux') (hUsq₅ : P₅.coveringOpen.toScheme = Usq)
    (hPx'₅ : (relativeProj A₅).scheme = Px') (hj₅ : HEq (T₅.homOfLE hU₅) j)
    (hrsq₅ : HEq (P₅.globalMorphism (relativeProj A₅)) rsq) (hrx'₅ : HEq r'₅ rx')
    (hX'₅ : HEq (GradedPowerMap.Otw A₅ d₅) X')
    {Usq₀ Ux₀ Px₀ Px'₀ : Scheme.{u}} (rsq₀ : Usq₀ ⟶ Px'₀) (ym₀ : Px'₀ ⟶ Px₀) (l₀ : Usq₀ ⟶ Ux₀)
    (rx₀ : Ux₀ ⟶ Px₀) (H₁₀ : rsq₀ ≫ ym₀ = l₀ ≫ rx₀)
    {G₀ : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf Px₀.toRingedSpace)}
    {G'₀ : SheafOfModules.GradedAlgebra.{u, u}
      (Stacks.RingedSpace.structureRingSheaf Px'₀.toRingedSpace)}
    (Ey₀ : pullbackGradedAlgebra ym₀.toLRSHom.toShHom G₀ ≅ G'₀)
    (Bs₀ : pullbackGradedAlgebra l₀.toLRSHom.toShHom
        (pullbackGradedAlgebra rx₀.toLRSHom.toShHom G₀) ≅
      pullbackGradedAlgebra rsq₀.toLRSHom.toShHom G'₀) (d : ℤ)
    (hBi₀ : (pb rsq₀).map (Ey₀.hom.app d) ≫ Bs₀.inv.app d =
      canHom rsq₀ ym₀ (l₀ ≫ rx₀) H₁₀ (G₀.piece d) ≫ (pC l₀ rx₀).inv.app (G₀.piece d))
    (hUsq : Usq₀ = Usq) (hUx : Ux₀ = Ux) (hPx : Px₀ = Px) (hPx' : Px'₀ = Px')
    (hrsq : HEq rsq₀ rsq) (hym : HEq ym₀ ym) (hl : HEq l₀ l) (hrx : HEq rx₀ rx)
    (hX : HEq (G₀.piece d) X) (hG'₀ : HEq G'₀ (GradedPowerMap.twD A₅).algebra) (hd : d = d₅)
    (hcy : HEq (Ey₀.hom.app d) cy) (hBs : HEq (Bs₀.inv.app d) Bi) :
    (Scheme.Modules.pullback τ).map (e₁ ≫ e₂ ≫ e₃) ≫
        ((Scheme.Modules.pullbackComp τ g).hom.app M ≫
          (Scheme.Modules.pullbackCongr hk).hom.app M ≫
          (Scheme.Modules.pullbackComp g' (j ≫ l)).inv.app M ≫
          (Scheme.Modules.pullback g').map ((Scheme.Modules.pullbackComp j l).inv.app M)) =
      σ ≫ (e₁' ≫ e₂' ≫ e₃') ≫ (Scheme.Modules.pullback g').map Ai ≫
        (Scheme.Modules.pullback g').map ((Scheme.Modules.pullback j).map Bi) := by
  subst hM hM₂ hM₃ hP₀ hP₀' hP₀'' hP₁ hP₁' hP₁'' hUsq hUx hPx hPx' hUx'₃ hPx'₃ hFx₄ hPx₄ hFx'₄
    hPx'₄ hUx'₅ hUsq₅ hPx'₅ hd
  subst hrsq hym hl hrx hX hG'₀ hg'₃ hrx'₃ hX'₃ hj₅ hrsq₅ hrx'₅ hX'₅ hcy hBs
    hcx₄ htx₄ hcx'₄ htx'₄ hy₄ hym₄ hX₄ hX'₄ hcy₄ he₁ he₂ he₃ he₁' he₂' he₃' hσ
  obtain rfl := eq_of_heq
    (hAi.trans (heq_of_eq (GradedPowerMap.thetaTransportSourceIso_inv_app P₅ hU₅ hr₅ _)))
  exact source_square_coherence_of_squareChain_of_value _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 hk h4
    h5₄ hr₅ H₁₀ _ _ hBi₀ _ rfl E4₄

end SourceFactors

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

namespace GradedAlgebraRestriction

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {Â : ∀ T : BigFppfOver B S hS, (yoneda.obj T ⟶ X) →
      SheafGradedAlgebra ((BigFppfOver.toScheme B S hS).obj T)}
    (ρ : GradedAlgebraRestriction (GradedAlgebraPoints.ofQuasicoherentFamily Â))
    (hc : ∀ (T : BigFppfOver B S hS) (f : yoneda.obj T ⟶ X),
      B.Contains (relativeProj (Â T f)).scheme)
    (hX : Presheaf.IsSheaf (BigFppfOver.topology B S hS) X)
    {Z : BigFppfOver B S hS} {f : yoneda.obj Z ⟶ X}
    {L : ((BigFppfOver.toScheme B S hS).obj Z).Modules}
    [Stacks.Ample.IsInvertibleModule _ L]
    (ψ : Twisting (𝟙 ((BigFppfOver.toScheme B S hS).obj Z))
      (situationAlgebra ((ρ.quadrupleRelativeProjPoints hc hX).algebra Z f)) 1 L)
    {X' Y' : BigFppfOver B S hS} (g : yoneda.obj Y' ⟶ X) (f' : X' ⟶ Y') (g' : X' ⟶ Z)
    (hsq : yoneda.map f' ≫ g = yoneda.map g' ≫ f)

/-- `squareThetaTargetIso` is the square-chain identification of its three factors. -/
theorem squareThetaTargetIso_eq_squareChainIso :
    ρ.squareThetaTargetIso hc hX ψ g f' g' hsq =
      squareChainIso (ρ.squareTheta_hk hc hX ψ g f' g' hsq) (ρ.squareTheta_hj hc hX ψ g f' g' hsq)
        (laurentOnHomOfLEIso ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g')).obj
                L) _)
        (laurentOnHomOfLEIso ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g')).obj
                L) _)
        (thetaTargetIsoOfEq ψ ((BigFppfOver.toScheme B S hS).map g') (comp_id_eq_id_comp g')
          (ρ.squareTargetChangeZ_eq hc hX ψ g f' g' hsq)) :=
  rfl

/-- The target coherence `AlgebraicGeometry.Space.chartScheme_target_coherence` along `g'` for
the square twisting of `ψ`, stated for an arbitrary graded power map `P'` on `X'` identified with
the square twisting by `e` and `hU'`. -/
theorem squareThetaTarget_coherence (d : ℤ)
    (gZ : (BigFppfOver.toScheme B S hS).obj Z ⟶ (toGradedPowerMap ψ).coveringOpen.toScheme)
    (hgZ : gZ ≫ (toGradedPowerMap ψ).coveringOpen.ι = 𝟙 _)
    {S'' : Scheme.{u}} {A'' : SheafGradedAlgebra.{u} S''}
    {f'' : (BigFppfOver.toScheme B S hS).obj X' ⟶ S''} (P' : GradedPowerMap A'' f'')
    (e : (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).L ≅ P'.L)
    (hU' : P'.coveringOpen ≤ (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).coveringOpen)
    (g'' : (BigFppfOver.toScheme B S hS).obj X' ⟶ P'.coveringOpen.toScheme)
    (hg'' : g'' ≫ P'.coveringOpen.ι = 𝟙 _)
    (hk : ((BigFppfOver.toScheme B S hS).map g') ≫ gZ = g'' ≫
          ((BigFppfOver.toScheme B S hS).obj X').homOfLE hU' ≫
      Scheme.Hom.resLE ((BigFppfOver.toScheme B S hS).map g') (toGradedPowerMap ψ).coveringOpen
          (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).coveringOpen
        (ρ.coveringOpen_squareTwisting hc hX ψ g f' g' hsq).le) :
    type_of% (chartScheme_target_coherence ((BigFppfOver.toScheme B S hS).map g') L _ P'.L d
      (Stacks.AlgebraicGeometry.ProjChartIntPullbackMul.intPullIso
            ((BigFppfOver.toScheme B S hS).map g') L d)
      (LaurentCongr.congrIso e d).hom _ _ _ _ _ gZ hgZ g'' hg'' _ _
      (by exact Scheme.Hom.resLE_comp_ι _ _) hk _ _ _ (ρ.squareTheta_hk hc hX ψ g f' g' hsq) _
      (ρ.squareTheta_hj hc hX ψ g f' g' hsq) (by exact Scheme.Hom.resLE_comp_ι _ _) _ _ _
      (laurentOnHomOfLEIso_hom_app _ _ d) (laurentOnHomOfLEIso_inv_app _ _ d)
      (thetaTargetIsoOfEq_hom_app _ _ _ (ρ.squareTargetChangeZ_eq hc hX ψ g f' g' hsq) d) _ rfl _
      (fun W t => laurentOnCongrPieceIso_hom_val_app _ _ d W t) _
      (GradedPowerMap.thetaTransportTargetIso_hom_app
            (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)) e hU' d) _
      (GradedPowerMap.laurentOnSectionPieceIso_hom_eq (toGradedPowerMap ψ) gZ hgZ d) _
      (GradedPowerMap.laurentOnSectionPieceIso_hom_eq P' g'' hg'' d) _ rfl) :=
  chartScheme_target_coherence ((BigFppfOver.toScheme B S hS).map g') L _ P'.L d
      (Stacks.AlgebraicGeometry.ProjChartIntPullbackMul.intPullIso
            ((BigFppfOver.toScheme B S hS).map g') L d)
      (LaurentCongr.congrIso e d).hom _ _ _ _ _ gZ hgZ g'' hg'' _ _
      (by exact Scheme.Hom.resLE_comp_ι _ _) hk _ _ _ (ρ.squareTheta_hk hc hX ψ g f' g' hsq) _
      (ρ.squareTheta_hj hc hX ψ g f' g' hsq) (by exact Scheme.Hom.resLE_comp_ι _ _) _ _ _
      (laurentOnHomOfLEIso_hom_app _ _ d) (laurentOnHomOfLEIso_inv_app _ _ d)
      (thetaTargetIsoOfEq_hom_app _ _ _ (ρ.squareTargetChangeZ_eq hc hX ψ g f' g' hsq) d) _ rfl _
      (fun W t => laurentOnCongrPieceIso_hom_val_app _ _ d W t) _
      (GradedPowerMap.thetaTransportTargetIso_hom_app
            (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)) e hU' d) _
      (GradedPowerMap.laurentOnSectionPieceIso_hom_eq (toGradedPowerMap ψ) gZ hgZ d) _
      (GradedPowerMap.laurentOnSectionPieceIso_hom_eq P' g'' hg'' d) _ rfl

/-- `…squareThetaTarget_coherence`, with the identification of the targets along the square
read as `…GradedAlgebraRestriction.squareThetaTargetIso`: the shape of the target hypothesis of
`AlgebraicGeometry.Space.pullback_map_comp_eq_of_theta_eq_of_factors` at the chart maps. -/
theorem squareThetaTarget_coherence_squareThetaTargetIso (d : ℤ)
    (gZ : (BigFppfOver.toScheme B S hS).obj Z ⟶ (toGradedPowerMap ψ).coveringOpen.toScheme)
    (hgZ : gZ ≫ (toGradedPowerMap ψ).coveringOpen.ι = 𝟙 _)
    {S'' : Scheme.{u}} {A'' : SheafGradedAlgebra.{u} S''}
    {f'' : ((BigFppfOver.toScheme B S hS).obj X') ⟶ S''} (P' : GradedPowerMap A'' f'')
    (e : (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).L ≅ P'.L)
    (hU' : P'.coveringOpen ≤ (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).coveringOpen)
    (g'' : ((BigFppfOver.toScheme B S hS).obj X') ⟶ P'.coveringOpen.toScheme)
    (hg'' : g'' ≫ P'.coveringOpen.ι = 𝟙 _)
    (hk : ((BigFppfOver.toScheme B S hS).map g') ≫ gZ = g'' ≫
          ((BigFppfOver.toScheme B S hS).obj X').homOfLE hU' ≫
      Scheme.Hom.resLE ((BigFppfOver.toScheme B S hS).map g') (toGradedPowerMap ψ).coveringOpen
          (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).coveringOpen
            (ρ.coveringOpen_squareTwisting hc hX ψ g f' g' hsq).le) :
    ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map g') gZ).hom.app
          ((laurentOn L (toGradedPowerMap ψ).coveringOpen).piece d) ≫
        (Scheme.Modules.pullbackCongr hk).hom.app
            ((laurentOn L (toGradedPowerMap ψ).coveringOpen).piece d) ≫
        (Scheme.Modules.pullbackComp g'' (((BigFppfOver.toScheme B S hS).obj X').homOfLE hU' ≫
          Scheme.Hom.resLE ((BigFppfOver.toScheme B S hS).map g') (toGradedPowerMap ψ).coveringOpen
              (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).coveringOpen
            (ρ.coveringOpen_squareTwisting hc hX ψ g f' g' hsq).le)).inv.app
                ((laurentOn L (toGradedPowerMap ψ).coveringOpen).piece d) ≫
        (Scheme.Modules.pullback g'').map
            ((Scheme.Modules.pullbackComp (((BigFppfOver.toScheme B S hS).obj X').homOfLE hU')
          (Scheme.Hom.resLE ((BigFppfOver.toScheme B S hS).map g') (toGradedPowerMap ψ).coveringOpen
                (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).coveringOpen
            (ρ.coveringOpen_squareTwisting hc hX ψ g f' g' hsq).le)).inv.app
                ((laurentOn L (toGradedPowerMap ψ).coveringOpen).piece d))) ≫
      (Scheme.Modules.pullback g'').map
        ((Scheme.Modules.pullback (((BigFppfOver.toScheme B S hS).obj X').homOfLE hU')).map
          ((ρ.squareThetaTargetIso hc hX ψ g f' g' hsq).hom.app d)) ≫
      (Scheme.Modules.pullback g'').map
      (((toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).thetaTransportTargetIso e
              hU').hom.app d) ≫
      (P'.laurentOnSectionPieceIso g'' hg'' d).hom =
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g')).map
    ((toGradedPowerMap ψ).laurentOnSectionPieceIso gZ hgZ d).hom ≫
      ((Stacks.AlgebraicGeometry.ProjChartIntPullbackMul.intPullIso
              ((BigFppfOver.toScheme B S hS).map g') L d).hom ≫
        (LaurentCongr.congrIso e d).hom) := by
  rw [ρ.squareThetaTargetIso_eq_squareChainIso hc hX ψ g f' g' hsq]
  exact ρ.squareThetaTarget_coherence hc hX ψ g f' g' hsq d gZ hgZ P' e hU' g'' hg'' hk


/-- `squareThetaSourceIso` is the square-chain identification of its three factors. -/
theorem squareThetaSourceIso_eq_squareChainIso :
    ρ.squareThetaSourceIso hc hX ψ g f' g' hsq =
      squareChainIso (ρ.squareTheta_hk hc hX ψ g f' g' hsq) (ρ.squareTheta_hj hc hX ψ g f' g' hsq)
        (thetaChangeSourceIsoOfEq (Â Y' g) ((BigFppfOver.toScheme B S hS).map f')
              (ρ.restrict f' g (yoneda.map f' ≫ g) rfl)
              (ρ.isIso_restrict_app f' g (yoneda.map f' ≫ g) rfl)
              (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq) (Category.id_comp _)
          (ρ.squareTwisting_eq_congrBase hc hX ψ g f' g' hsq))
        (thetaChangeSourceIso (Â Z f) _ _ _ (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq))
        (thetaSourceIsoOfEq ψ ((BigFppfOver.toScheme B S hS).map g') (comp_id_eq_id_comp g')
              (ρ.squareTargetChangeZ_eq hc hX ψ g f' g' hsq)) :=
  rfl

/-- The square `r_{ψ'} ≫ y_P = l ≫ r_ψ` of the square chain, for a morphism `y_P` with
`pc₁ ≫ y_P = pc₂`. -/
theorem squareTheta_globalMorphism_comp
    (ym : (relativeProj (Â Y' g)).scheme ⟶ (relativeProj (Â Z f)).scheme)
    (hcomp : (changeTargetProj (Â Y' g) ((BigFppfOver.toScheme B S hS).map f')
            (ρ.restrict f' g (yoneda.map f' ≫ g) rfl)
            (ρ.isIso_restrict_app f' g (yoneda.map f' ≫ g) rfl)) ≫ ym =
          (changeTargetProj (Â Z f) ((BigFppfOver.toScheme B S hS).map g')
            (ρ.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
            (ρ.isIso_restrict_app g' f _ hsq.symm))) :
    ((toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).globalMorphism
          (relativeProj (Â Y' g))) ≫ ym =
    (Scheme.Hom.resLE ((BigFppfOver.toScheme B S hS).map g') (toGradedPowerMap ψ).coveringOpen
          (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).coveringOpen
          (ρ.coveringOpen_squareTwisting hc hX ψ g f' g' hsq).le) ≫
    ((toGradedPowerMap ψ).globalMorphism
          (relativeProj ((ρ.quadrupleRelativeProjPoints hc hX).algebra Z f))) :=
  squareChain_comp_eq ((toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).globalMorphism
        (relativeProj (Â Y' g))) ym (Scheme.Hom.resLE ((BigFppfOver.toScheme B S hS).map g')
        (toGradedPowerMap ψ).coveringOpen
        (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).coveringOpen
        (ρ.coveringOpen_squareTwisting hc hX ψ g f' g' hsq).le)
      ((toGradedPowerMap ψ).globalMorphism
        (relativeProj ((ρ.quadrupleRelativeProjPoints hc hX).algebra Z f))) _ _ _ _ _
      (changeTargetProj (Â Y' g) ((BigFppfOver.toScheme B S hS).map f')
        (ρ.restrict f' g (yoneda.map f' ≫ g) rfl)
        (ρ.isIso_restrict_app f' g (yoneda.map f' ≫ g) rfl))
      (changeTargetProj (Â Z f) ((BigFppfOver.toScheme B S hS).map g')
        (ρ.restrict g' f (yoneda.map f' ≫ g) hsq.symm) (ρ.isIso_restrict_app g' f _ hsq.symm)) _
    (ρ.squareTheta_hk hc hX ψ g f' g' hsq) (ρ.squareTheta_hj hc hX ψ g f' g' hsq)
    (homOfLE_globalMorphism_changeTarget_of_eq (Â Y' g) ((BigFppfOver.toScheme B S hS).map f')
          (ρ.restrict f' g (yoneda.map f' ≫ g) rfl)
          (ρ.isIso_restrict_app f' g (yoneda.map f' ≫ g) rfl)
          (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq) (Category.id_comp _)
      (ρ.squareTwisting_eq_congrBase hc hX ψ g f' g' hsq))
    (homOfLE_globalMorphism_changeTarget (Â Z f) ((BigFppfOver.toScheme B S hS).map g')
          (ρ.restrict g' f (yoneda.map f' ≫ g) hsq.symm) (ρ.isIso_restrict_app g' f _ hsq.symm)
          (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq))
    (coveringOpenPullbackOfEq_globalMorphism ψ ((BigFppfOver.toScheme B S hS).map g')
          (comp_id_eq_id_comp g')
      (ρ.squareTargetChangeZ_eq hc hX ψ g f' g' hsq)) hcomp

open Stacks.AlgebraicGeometry.ModuleLimits (canHom) in
/-- **The inverse of the identification of the sources of `θ` along the square, against the
comparison of twists**: for a morphism `y_P : Proj_{Y'}(g^*𝒜) ⟶ Proj_Z(f^*𝒜)` with
`pc₁ ≫ y_P = pc₂` for the comparison morphisms of the two changes of target, and a comparison of
twists `E_y` along `y_P` satisfying the cocycle with the comparisons of twists along `pc₁` and
`pc₂`, the inverse image along `r_{ψ'}` of `E_y` followed by the inverse of
`…squareThetaSourceIso` is the canonical identification
`r_{ψ'}^*(y_P^*𝒪(d)) ⟶ l^*(r_ψ^*𝒪(d))` of Stacks 01ZR (2), for `l : U(ψ') ⟶ U(ψ)` the
restriction of `g'`. -/
theorem squareThetaSourceIso_inv_app_canHom (d : ℤ)
    (ym : (relativeProj (Â Y' g)).scheme ⟶ (relativeProj (Â Z f)).scheme)
    (Ey : pullbackGradedAlgebra ym.toLRSHom.toShHom (GradedPowerMap.twD (Â Z f)).algebra ≅
      (GradedPowerMap.twD (Â Y' g)).algebra)
    (hcomp : (changeTargetProj (Â Y' g) ((BigFppfOver.toScheme B S hS).map f')
            (ρ.restrict f' g (yoneda.map f' ≫ g) rfl)
            (ρ.isIso_restrict_app f' g (yoneda.map f' ≫ g) rfl)) ≫ ym =
          (changeTargetProj (Â Z f) ((BigFppfOver.toScheme B S hS).map g')
            (ρ.restrict g' f (yoneda.map f' ≫ g) hsq.symm) (ρ.isIso_restrict_app g' f _ hsq.symm)))
    (H₁ : ((toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).globalMorphism
            (relativeProj (Â Y' g))) ≫ ym =
          (Scheme.Hom.resLE ((BigFppfOver.toScheme B S hS).map g') (toGradedPowerMap ψ).coveringOpen
            (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).coveringOpen
            (ρ.coveringOpen_squareTwisting hc hX ψ g f' g' hsq).le) ≫
          ((toGradedPowerMap ψ).globalMorphism
            (relativeProj ((ρ.quadrupleRelativeProjPoints hc hX).algebra Z f))))
    (hE : (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.congrBaseChangeTwistIso (Â Z f)
            ((BigFppfOver.toScheme B S hS).map g') (ρ.restrict g' f (yoneda.map f' ≫ g) hsq.symm)
            (ρ.isIso_restrict_app g' f _ hsq.symm)
            (changeTargetProj (Â Z f) ((BigFppfOver.toScheme B S hS).map g')
              (ρ.restrict g' f (yoneda.map f' ≫ g) hsq.symm) (ρ.isIso_restrict_app g' f _ hsq.symm))
            rfl) =
      Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCongrIso _
          hcomp.symm ≪≫
        (Stacks.AlgebraicGeometry.GradedAlgebraPullbackComp.pullbackGradedAlgebraCompIso _
              (changeTargetProj (Â Y' g) ((BigFppfOver.toScheme B S hS).map f')
                (ρ.restrict f' g (yoneda.map f' ≫ g) rfl)
                (ρ.isIso_restrict_app f' g (yoneda.map f' ≫ g) rfl)) ym).symm ≪≫
        pullbackGradedAlgebraMapIso _ Ey ≪≫
            (Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist.congrBaseChangeTwistIso (Â Y' g)
              ((BigFppfOver.toScheme B S hS).map f') (ρ.restrict f' g (yoneda.map f' ≫ g) rfl)
              (ρ.isIso_restrict_app f' g (yoneda.map f' ≫ g) rfl)
              (changeTargetProj (Â Y' g) ((BigFppfOver.toScheme B S hS).map f')
                (ρ.restrict f' g (yoneda.map f' ≫ g) rfl)
                (ρ.isIso_restrict_app f' g (yoneda.map f' ≫ g) rfl)) rfl)) :
    (Scheme.Modules.pullback ((toGradedPowerMap
              (ρ.squareTwisting hc hX ψ g f' g' hsq)).globalMorphism (relativeProj (Â Y' g)))).map
    (Ey.hom.app d) ≫
        (ρ.squareThetaSourceIso hc hX ψ g f' g' hsq).inv.app d =
      canHom ((toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).globalMorphism
            (relativeProj (Â Y' g))) ym ((Scheme.Hom.resLE ((BigFppfOver.toScheme B S hS).map g')
              (toGradedPowerMap ψ).coveringOpen
              (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).coveringOpen
              (ρ.coveringOpen_squareTwisting hc hX ψ g f' g' hsq).le) ≫
            ((toGradedPowerMap ψ).globalMorphism
              (relativeProj ((ρ.quadrupleRelativeProjPoints hc hX).algebra Z f)))) H₁
          ((GradedPowerMap.twD (Â Z f)).algebra.piece d) ≫
        (Scheme.Modules.pullbackComp (Scheme.Hom.resLE ((BigFppfOver.toScheme B S hS).map g')
                (toGradedPowerMap ψ).coveringOpen
                (toGradedPowerMap (ρ.squareTwisting hc hX ψ g f' g' hsq)).coveringOpen
                (ρ.coveringOpen_squareTwisting hc hX ψ g f' g' hsq).le)
              ((toGradedPowerMap ψ).globalMorphism
                (relativeProj ((ρ.quadrupleRelativeProjPoints hc hX).algebra Z f)))).inv.app
        ((GradedPowerMap.twD (Â Z f)).algebra.piece d) := by
  have hS₁ := thetaChangeSourceIsoOfEq_eq (Â Y' g) ((BigFppfOver.toScheme B S hS).map f')
      (ρ.restrict f' g (yoneda.map f' ≫ g) rfl) (ρ.isIso_restrict_app f' g (yoneda.map f' ≫ g) rfl)
      (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq) (Category.id_comp _)
    (ρ.squareTwisting_eq_congrBase hc hX ψ g f' g' hsq)
  have hS₂ := thetaChangeSourceIso_eq (Â Z f) ((BigFppfOver.toScheme B S hS).map g')
      (ρ.restrict g' f (yoneda.map f' ≫ g) hsq.symm) (ρ.isIso_restrict_app g' f _ hsq.symm)
      (ρ.squareTwistingAtPoint hc hX ψ g f' g' hsq)
  have hS₄ := thetaSourceIsoOfEq_eq ψ ((BigFppfOver.toScheme B S hS).map g') (comp_id_eq_id_comp g')
      (ρ.squareTargetChangeZ_eq hc hX ψ g f' g' hsq)
  have key := pullback_map_comp_squareChainIso_inv_app _ ym _ _ _ _ _ _ _ _ _ _
    (ρ.squareTheta_hk hc hX ψ g f' g' hsq) (ρ.squareTheta_hj hc hX ψ g f' g' hsq) _ _ _ hcomp H₁ Ey
        _ _ hE _ hS₁ _ hS₂ _ hS₄ _ (ρ.squareThetaSourceIso_eq_squareChainIso hc hX ψ g f' g' hsq) d
  exact key

end GradedAlgebraRestriction

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space.RelativeProjSituation

open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
  Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist

variable (s : RelativeProjSituation.{u, m})

/-- **The comparison morphisms of relative homogeneous spectra compose**: along `τ` and along
`𝟙 ≫ τ = τ`, the comparison `Proj_{T'}(w^*𝒜) ⟶ Proj_T(u^*𝒜)` is the comparison
`Proj_{T'}(w^*𝒜) ⟶ Proj_{T'}(v^*𝒜)` along `𝟙` followed by a morphism `y` of base changes lying
over `τ`. -/
theorem relativeProjCongr_baseChangeHom_eq_comp {T T' : BigFppfOver s.site s.base s.containsBase}
    (τ : T' ⟶ T) (u : yoneda.obj T ⟶ s.space.1) (v : yoneda.obj T' ⟶ s.space.1)
    (w : yoneda.obj T' ⟶ s.space.1) (hw : yoneda.map (𝟙 T') ≫ v = w)
    (hw'' : yoneda.map τ ≫ u = w)
    (y : s.relativeProjPoints.fibre T' v ⟶ s.relativeProjPoints.fibre T u)
    (hy : s.relativeProjPoints.LiesOver y τ) :
    (relativeProjCongr (A₁ := s.shrink.pointAlgebra T' w)
        (A₂ := (s.shrink.pointAlgebra T u).pullback
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map τ))
        (s.quadrupleRestriction.restrict τ u w hw'')
        (s.quadrupleRestriction.isIso_restrict_app τ u w hw'')).hom ≫
        baseChangeHom (s.shrink.pointAlgebra T u)
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map τ) =
      ((relativeProjCongr (A₁ := s.shrink.pointAlgebra T' w)
        (A₂ := (s.shrink.pointAlgebra T' v).pullback
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map (𝟙 T')))
        (s.quadrupleRestriction.restrict (𝟙 T') v w hw)
        (s.quadrupleRestriction.isIso_restrict_app (𝟙 T') v w hw)).hom ≫
        baseChangeHom (s.shrink.pointAlgebra T' v)
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map (𝟙 T'))) ≫
        (BigFppfOver.toScheme s.site s.base s.containsBase).map y := by
  rw [← s.toScheme_map_eqToHom_projComparison u τ w hw'',
    ← s.toScheme_map_eqToHom_projComparison v (𝟙 T') w hw]
  exact (congrArg (BigFppfOver.toScheme s.site s.base s.containsBase).map
    (((s.liesOver_projComparison u τ).eqToHom_comp hw''.symm).eq
      (hy.comp ((s.liesOver_projComparison v (𝟙 T')).eqToHom_comp hw.symm))
      (Category.id_comp τ).symm)).trans
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp _ _)

end AlgebraicGeometry.Space.RelativeProjSituation

namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra)

variable {s : RelativeProjSituation.{u, m}}
  {X : (BigFppfOver s.site s.base s.containsBase)ᵒᵖ ⥤ Type u} {f : X ⟶ s.space.1}
  (R : s.InvertibleTwistingRestriction f)
  {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T) (x : yoneda.obj T ⟶ X)
  (hx : R.locusOpen T x = ⊤)

/-- **`τ` restricted to the loci**, for any restriction datum: the composite `T' ⟶ T ⟶ U(x^*ψ)`
of `τ` and the section of `U(x^*ψ) ⊆ T` is the section `T' ⟶ U((x ∘ τ)^*ψ)`, followed by
`U((x ∘ τ)^*ψ) ⊆ U(τ^*(x^*ψ))` and the restriction `U(τ^*(x^*ψ)) ⟶ U(x^*ψ)` of `τ`. -/
theorem map_comp_chartLift_of (hx' : R.locusOpen T' (yoneda.map τ ≫ x) = ⊤) :
    (BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map τ ≫
        R.chartLift x hx =
      R.chartLift (yoneda.map τ ≫ x) hx' ≫
        (Scheme.homOfLE ((BigFppfOver.toScheme s.shrink.site s.shrink.base
          s.shrink.containsBase).obj T') (R.coveringOpen_twisting_map_le τ x) ≫
        Scheme.Hom.resLE
          ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map τ)
          (toGradedPowerMap (R.twisting T x)).coveringOpen
          (toGradedPowerMap (s.quadrupleRestriction.squareTwisting
                  s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
                  (R.twisting T x) ((yoneda.map τ ≫ x) ≫ f) (𝟙 T') τ
                  (yoneda_map_id_comp_assoc s f τ x))).coveringOpen
          (s.quadrupleRestriction.coveringOpen_squareTwisting
                s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
                (R.twisting T x) ((yoneda.map τ ≫ x) ≫ f) (𝟙 T') τ
                (yoneda_map_id_comp_assoc s f τ x)).le) := by
  refine (cancel_mono (toGradedPowerMap (R.twisting T x)).coveringOpen.ι).1 ?_
  refine ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (R.chartLift_ι x hx)).trans (Category.comp_id _))).trans ?_
  refine Eq.symm ((Category.assoc _ _ _).trans ?_)
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Scheme.Hom.resLE_comp_ι _ _)))).trans ?_
  refine (congrArg (_ ≫ ·) ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (Scheme.homOfLE_ι _ _)))).trans ?_
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
    (R.chartLift_ι (yoneda.map τ ≫ x) hx')).trans (Category.id_comp _))

/-- The section `c_w`, read on schemes and followed by the identification of
`W ×_Y Proj_Y(𝒜)` with `Proj_W((f ∘ w)^*𝒜)` used by the twists, is `r_w`, for any restriction
datum. -/
theorem toScheme_map_chartSection_comp_toRelativeProj {W : BigFppfOver s.site s.base s.containsBase}
    (w : yoneda.obj W ⟶ X) (hw : R.locusOpen W w = ⊤) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map (R.chartSection w hw) ≫
        s.toRelativeProj W (w ≫ f) = R.chartMorphism w hw :=
  R.toScheme_map_chartSection w hw

/-- The degree-`d` comparison of `θ` along `τ`, for any restriction datum. -/
theorem theta_app_eq_pullback (d : ℤ) :
    type_of% (app_eq_comp_pullback_map_app _ _ _ _ _ _ _ _ (R.theta_map_eq_pullback τ x) d) :=
  app_eq_comp_pullback_map_app _ _ _ _ _ _ _ _ (R.theta_map_eq_pullback τ x) d

/-- The coherence of the identifications of the targets of `θ` around `τ`. -/
theorem chartTheta_target (d : ℤ) (hx' : R.locusOpen T' (yoneda.map τ ≫ x) = ⊤) :
    type_of% (s.quadrupleRestriction.squareThetaTarget_coherence_squareThetaTargetIso
          s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
          (R.twisting T x) ((yoneda.map τ ≫ x) ≫ f) (𝟙 T') τ (yoneda_map_id_comp_assoc s f τ x) d
      (R.chartLift x hx) (R.chartLift_ι x hx) (toGradedPowerMap (R.twisting T' (yoneda.map τ ≫ x)))
      (R.lineIso τ x) (R.coveringOpen_twisting_map_le τ x) (R.chartLift (yoneda.map τ ≫ x) hx')
      (R.chartLift_ι (yoneda.map τ ≫ x) hx') (R.map_comp_chartLift_of τ x hx hx')) :=
  s.quadrupleRestriction.squareThetaTarget_coherence_squareThetaTargetIso
      s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf (R.twisting T x)
      ((yoneda.map τ ≫ x) ≫ f) (𝟙 T') τ (yoneda_map_id_comp_assoc s f τ x) d
      (R.chartLift x hx) (R.chartLift_ι x hx) (toGradedPowerMap (R.twisting T' (yoneda.map τ ≫ x)))
      (R.lineIso τ x) (R.coveringOpen_twisting_map_le τ x) (R.chartLift (yoneda.map τ ≫ x) hx')
      (R.chartLift_ι (yoneda.map τ ≫ x) hx') (R.map_comp_chartLift_of τ x hx hx')

/-- **The sections `c_x` are natural, on schemes**: for a morphism `y` of base changes lying
over `τ`, `τ ≫ c_x = c_{x ∘ τ} ≫ y`, read through the scheme functor of the site. -/
theorem toScheme_map_comp_chartSection (hx' : R.locusOpen T' (yoneda.map τ ≫ x) = ⊤)
    (y : s.relativeProjPoints.fibre T' ((yoneda.map τ ≫ x) ≫ f) ⟶
      s.relativeProjPoints.fibre T (x ≫ f))
    (hy : s.relativeProjPoints.LiesOver y τ) :
    (BigFppfOver.toScheme s.site s.base s.containsBase).map τ ≫
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map (R.chartSection x hx)) =
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map
          (R.chartSection (yoneda.map τ ≫ x) hx')) ≫
    ((BigFppfOver.toScheme s.site s.base s.containsBase).map y) :=
  ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp _ _).symm.trans
    ((congrArg (BigFppfOver.toScheme s.site s.base s.containsBase).map
            (R.chartSection_comp_of_liesOver τ x hx _ hx' rfl y hy).symm).trans
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map_comp _ _))

/-- The comparison morphisms of relative homogeneous spectra along `𝟙 ≫ τ = τ` compose with the
morphism `y` of base changes over `τ`. -/
theorem chartTheta_hcomp (y : s.relativeProjPoints.fibre T' ((yoneda.map τ ≫ x) ≫ f) ⟶
      s.relativeProjPoints.fibre T (x ≫ f))
    (hy : s.relativeProjPoints.LiesOver y τ) :
    type_of% (s.relativeProjCongr_baseChangeHom_eq_comp τ (x ≫ f) ((yoneda.map τ ≫ x) ≫ f) _
    rfl (yoneda_map_id_comp_assoc s f τ x).symm y hy).symm :=
  (s.relativeProjCongr_baseChangeHom_eq_comp τ (x ≫ f) ((yoneda.map τ ≫ x) ≫ f) _
    rfl (yoneda_map_id_comp_assoc s f τ x).symm y hy).symm

/-- The cocycle of the comparisons of twists along `𝟙`, along `τ` and along `y`. -/
theorem chartTheta_hE (y : s.relativeProjPoints.fibre T' ((yoneda.map τ ≫ x) ≫ f) ⟶
      s.relativeProjPoints.fibre T (x ≫ f))
    (hy : s.relativeProjPoints.LiesOver y τ) :
    type_of% (s.pointTwistComparison_comp_of_comp_eq τ (𝟙 T') τ (Category.id_comp τ) (x ≫ f)
    ((yoneda.map τ ≫ x) ≫ f) _ (Category.assoc _ _ _).symm rfl
    (yoneda_map_id_comp_assoc s f τ x).symm
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y :
          (relativeProj (s.shrink.pointAlgebra T' ((yoneda.map τ ≫ x) ≫ f))).scheme ⟶
            (relativeProj (s.shrink.pointAlgebra T (x ≫ f))).scheme)
    (s.toScheme_map_eq_of_liesOver (Category.assoc _ _ _).symm hy) _ rfl _ rfl
        (chartTheta_hcomp τ x y hy).symm
    (s.toScheme_map_comp_toBase_of_liesOver (Category.assoc _ _ _).symm hy)
    (changeTargetProj_comp_toBase _ _ _ _)) :=
  (s.pointTwistComparison_comp_of_comp_eq τ (𝟙 T') τ (Category.id_comp τ) (x ≫ f)
    ((yoneda.map τ ≫ x) ≫ f) _ (Category.assoc _ _ _).symm rfl
    (yoneda_map_id_comp_assoc s f τ x).symm
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y :
          (relativeProj (s.shrink.pointAlgebra T' ((yoneda.map τ ≫ x) ≫ f))).scheme ⟶
            (relativeProj (s.shrink.pointAlgebra T (x ≫ f))).scheme)
    (s.toScheme_map_eq_of_liesOver (Category.assoc _ _ _).symm hy) _ rfl _ rfl
        (chartTheta_hcomp τ x y hy).symm
    (s.toScheme_map_comp_toBase_of_liesOver (Category.assoc _ _ _).symm hy)
    (changeTargetProj_comp_toBase _ _ _ _))

set_option maxHeartbeats 400000 in
-- the `refine` and its `rfl`/`HEq.rfl` side goals unify very large terms of the chart square
/-- **The square of the scheme factor of the chart maps of Stacks 0D2Z along `τ`**, for any
restriction datum: for `τ : T' ⟶ T`, a scheme point `x` at `T` with `x ∘ τ` at `T'`, and a
morphism `y` of base changes lying over `τ`, the inverse image along `τ` of
`c_x^*𝒪(d) ≅ r_x^*𝒪(d) ⟶ (x^*ℒ)^{⊗ d}` followed by the comparison `ρ` of the targets is the
comparison `σ` of the sources (through `y` and the comparison of twists along `y`) followed by
the same map at `x ∘ τ`. -/
theorem chartTheta_square (d : ℤ) (hx' : R.locusOpen T' (yoneda.map τ ≫ x) = ⊤)
    (y : s.relativeProjPoints.fibre T' ((yoneda.map τ ≫ x) ≫ f) ⟶
      s.relativeProjPoints.fibre T (x ≫ f))
    (hy : s.relativeProjPoints.LiesOver y τ)
    (ρ : (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ)).obj
        (Stacks.AmpleProjectiveImmersion.tensorPowerModule _ (R.line T x) d) ⟶
      Stacks.AmpleProjectiveImmersion.tensorPowerModule _ (R.line T' (yoneda.map τ ≫ x)) d)
    (hρ : ρ = (Stacks.AlgebraicGeometry.ProjChartIntPullbackMul.intPullIso
            ((BigFppfOver.toScheme s.shrink.site s.shrink.base s.shrink.containsBase).map τ)
            (R.line T x) d).hom ≫
      (LaurentCongr.congrIso (R.lineIso τ x) d).hom) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ)).map
    ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme s.site s.base s.containsBase).map
              (R.chartSection x hx)) (s.toRelativeProj T (x ≫ f) :
        (BigFppfOver.toScheme s.site s.base s.containsBase).obj
            (s.relativeProjPoints.fibre T (x ≫ f)) ⟶
          (relativeProj (s.relativeProjPoints.algebra T (x ≫ f))).scheme)).hom.app
              ((GradedPowerMap.twD (s.relativeProjPoints.algebra T (x ≫ f))).algebra.piece d) ≫
              (Scheme.Modules.pullbackCongr (R.toScheme_map_chartSection_comp_toRelativeProj x hx :
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map (R.chartSection x hx)) ≫
            (s.toRelativeProj T (x ≫ f) :
        (BigFppfOver.toScheme s.site s.base s.containsBase).obj
            (s.relativeProjPoints.fibre T (x ≫ f)) ⟶
          (relativeProj (s.relativeProjPoints.algebra T (x ≫ f))).scheme) = (R.chartLift x hx) ≫
              ((toGradedPowerMap (R.twisting T x)).globalMorphism
              (relativeProj (s.relativeProjPoints.algebra T (x ≫ f)))))).hom.app
              ((GradedPowerMap.twD (s.relativeProjPoints.algebra T (x ≫ f))).algebra.piece d) ≫
        R.chartTheta x hx d) ≫ ρ =
      ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ)
              ((BigFppfOver.toScheme s.site s.base s.containsBase).map
                (R.chartSection x hx))).hom.app
            ((Scheme.Modules.pullback (s.toRelativeProj T (x ≫ f) :
        (BigFppfOver.toScheme s.site s.base s.containsBase).obj
            (s.relativeProjPoints.fibre T (x ≫ f)) ⟶
          (relativeProj (s.relativeProjPoints.algebra T (x ≫ f))).scheme)).obj
              ((GradedPowerMap.twD (s.relativeProjPoints.algebra T (x ≫ f))).algebra.piece d)) ≫
        eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj
                ((Scheme.Modules.pullback (s.toRelativeProj T (x ≫ f) :
        (BigFppfOver.toScheme s.site s.base s.containsBase).obj
            (s.relativeProjPoints.fibre T (x ≫ f)) ⟶
          (relativeProj (s.relativeProjPoints.algebra T (x ≫ f))).scheme)).obj
              ((GradedPowerMap.twD (s.relativeProjPoints.algebra T (x ≫ f))).algebra.piece d)))
          (R.toScheme_map_comp_chartSection τ x hx hx' y hy)) ≫
        (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme s.site s.base s.containsBase).map
                (R.chartSection (yoneda.map τ ≫ x) hx'))
              ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)).inv.app
            ((Scheme.Modules.pullback (s.toRelativeProj T (x ≫ f) :
        (BigFppfOver.toScheme s.site s.base s.containsBase).obj
            (s.relativeProjPoints.fibre T (x ≫ f)) ⟶
          (relativeProj (s.relativeProjPoints.algebra T (x ≫ f))).scheme)).obj
              ((GradedPowerMap.twD (s.relativeProjPoints.algebra T (x ≫ f))).algebra.piece d)) ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map
                (R.chartSection (yoneda.map τ ≫ x) hx'))).map
            ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme s.site s.base s.containsBase).map
                  y) (s.toRelativeProj T (x ≫ f) :
        (BigFppfOver.toScheme s.site s.base s.containsBase).obj
            (s.relativeProjPoints.fibre T (x ≫ f)) ⟶
          (relativeProj (s.relativeProjPoints.algebra T (x ≫ f))).scheme)).hom.app
              ((GradedPowerMap.twD (s.relativeProjPoints.algebra T (x ≫ f))).algebra.piece d) ≫
          (Scheme.Modules.pullbackCongr (s.map_comp_toRelativeProj y :
                  (BigFppfOver.toScheme s.site s.base s.containsBase).map y ≫
                  (s.toRelativeProj T (x ≫ f) :
        (BigFppfOver.toScheme s.site s.base s.containsBase).obj
            (s.relativeProjPoints.fibre T (x ≫ f)) ⟶
          (relativeProj (s.relativeProjPoints.algebra T (x ≫ f))).scheme) =
              (s.toRelativeProj T' ((yoneda.map τ ≫ x) ≫ f) :
        (BigFppfOver.toScheme s.site s.base s.containsBase).obj
            (s.relativeProjPoints.fibre T' ((yoneda.map τ ≫ x) ≫ f)) ⟶
          (relativeProj (s.relativeProjPoints.algebra T' ((yoneda.map τ ≫ x) ≫ f))).scheme) ≫
              ((BigFppfOver.toScheme s.site s.base s.containsBase).map y :
        (relativeProj (s.relativeProjPoints.algebra T' ((yoneda.map τ ≫ x) ≫ f))).scheme ⟶
          (relativeProj (s.relativeProjPoints.algebra T (x ≫ f))).scheme))).hom.app
              ((GradedPowerMap.twD (s.relativeProjPoints.algebra T (x ≫ f))).algebra.piece d) ≫
              (Scheme.Modules.pullbackComp (s.toRelativeProj T' ((yoneda.map τ ≫ x) ≫ f) :
        (BigFppfOver.toScheme s.site s.base s.containsBase).obj
            (s.relativeProjPoints.fibre T' ((yoneda.map τ ≫ x) ≫ f)) ⟶
          (relativeProj (s.relativeProjPoints.algebra T' ((yoneda.map τ ≫ x) ≫ f))).scheme)
              ((BigFppfOver.toScheme s.site s.base s.containsBase).map y :
        (relativeProj (s.relativeProjPoints.algebra T' ((yoneda.map τ ≫ x) ≫ f))).scheme ⟶
          (relativeProj (s.relativeProjPoints.algebra T (x ≫ f))).scheme)).inv.app
              ((GradedPowerMap.twD (s.relativeProjPoints.algebra T (x ≫ f))).algebra.piece d) ≫
          (Scheme.Modules.pullback (s.toRelativeProj T' ((yoneda.map τ ≫ x) ≫ f) :
        (BigFppfOver.toScheme s.site s.base s.containsBase).obj
            (s.relativeProjPoints.fibre T' ((yoneda.map τ ≫ x) ≫ f)) ⟶
          (relativeProj (s.relativeProjPoints.algebra T' ((yoneda.map τ ≫ x) ≫ f))).scheme)).map
              ((@Iso.hom _ _ (pullbackGradedAlgebra
                ((BigFppfOver.toScheme s.site s.base s.containsBase).map y :
        (relativeProj (s.relativeProjPoints.algebra T' ((yoneda.map τ ≫ x) ≫ f))).scheme ⟶
          (relativeProj (s.relativeProjPoints.algebra T (x ≫ f))).scheme).toLRSHom.toShHom
        (GradedPowerMap.twD (s.shrink.pointAlgebra T (x ≫ f))).algebra)
        (GradedPowerMap.twD (s.shrink.pointAlgebra T' ((yoneda.map τ ≫ x) ≫ f))).algebra
            (s.pointTwistComparison τ (x ≫ f) ((yoneda.map τ ≫ x) ≫ f) (Category.assoc _ _ _).symm
              ((BigFppfOver.toScheme s.site s.base s.containsBase).map y :
        (relativeProj (s.relativeProjPoints.algebra T' ((yoneda.map τ ≫ x) ≫ f))).scheme ⟶
          (relativeProj (s.relativeProjPoints.algebra T (x ≫ f))).scheme)
        (s.toScheme_map_eq_of_liesOver (Category.assoc _ _ _).symm hy))).app d :
        (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map y :
        (relativeProj (s.relativeProjPoints.algebra T' ((yoneda.map τ ≫ x) ≫ f))).scheme ⟶
          (relativeProj (s.relativeProjPoints.algebra T (x ≫ f))).scheme)).obj
              ((GradedPowerMap.twD (s.relativeProjPoints.algebra T (x ≫ f))).algebra.piece d) ⟶
              ((GradedPowerMap.twD (s.relativeProjPoints.algebra T'
                ((yoneda.map τ ≫ x) ≫ f))).algebra.piece d)))) ≫
          ((Scheme.Modules.pullbackComp ((BigFppfOver.toScheme s.site s.base s.containsBase).map
              (R.chartSection (yoneda.map τ ≫ x) hx'))
              (s.toRelativeProj T' ((yoneda.map τ ≫ x) ≫ f) :
        (BigFppfOver.toScheme s.site s.base s.containsBase).obj
            (s.relativeProjPoints.fibre T' ((yoneda.map τ ≫ x) ≫ f)) ⟶
          (relativeProj (s.relativeProjPoints.algebra T' ((yoneda.map τ ≫ x) ≫ f))).scheme)).hom.app
              ((GradedPowerMap.twD (s.relativeProjPoints.algebra T'
                ((yoneda.map τ ≫ x) ≫ f))).algebra.piece d) ≫
              (Scheme.Modules.pullbackCongr (R.toScheme_map_chartSection_comp_toRelativeProj
              (yoneda.map τ ≫ x) hx' :
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map
              (R.chartSection (yoneda.map τ ≫ x) hx')) ≫
            (s.toRelativeProj T' ((yoneda.map τ ≫ x) ≫ f) :
        (BigFppfOver.toScheme s.site s.base s.containsBase).obj
            (s.relativeProjPoints.fibre T' ((yoneda.map τ ≫ x) ≫ f)) ⟶
          (relativeProj (s.relativeProjPoints.algebra T' ((yoneda.map τ ≫ x) ≫ f))).scheme) =
              (R.chartLift (yoneda.map τ ≫ x) hx') ≫
              ((toGradedPowerMap (R.twisting T' (yoneda.map τ ≫ x))).globalMorphism
              (relativeProj (s.relativeProjPoints.algebra T' ((yoneda.map τ ≫ x) ≫ f)))))).hom.app
              ((GradedPowerMap.twD (s.relativeProjPoints.algebra T'
              ((yoneda.map τ ≫ x) ≫ f))).algebra.piece d) ≫
        R.chartTheta (yoneda.map τ ≫ x) hx' d) := by
  subst hρ
  refine pullback_map_comp_eq_of_theta_eq_of_factors
      ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ) _ _ _ _
    (R.map_comp_chartLift_of τ x hx hx' : _)
    (M := (Scheme.Modules.pullback
            ((toGradedPowerMap (R.twisting T x)).globalMorphism
              (relativeProj (s.relativeProjPoints.algebra T (x ≫ f))))).obj
          ((GradedPowerMap.twD (s.relativeProjPoints.algebra T (x ≫ f))).algebra.piece d))
    (M₂ := (Scheme.Modules.pullback
            ((toGradedPowerMap (s.quadrupleRestriction.squareTwisting
                s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
                (R.twisting T x) ((yoneda.map τ ≫ x) ≫ f) (𝟙 T') τ
                (yoneda_map_id_comp_assoc s f τ x))).globalMorphism
              (relativeProj (s.shrink.pointAlgebra T' ((yoneda.map τ ≫ x) ≫ f))))).obj
          ((GradedPowerMap.twD (s.relativeProjPoints.algebra T'
                ((yoneda.map τ ≫ x) ≫ f))).algebra.piece d))
    (M₃ := (Scheme.Modules.pullback
            ((toGradedPowerMap (R.twisting T' (yoneda.map τ ≫ x))).globalMorphism
              (relativeProj (s.relativeProjPoints.algebra T' ((yoneda.map τ ≫ x) ≫ f))))).obj
          ((GradedPowerMap.twD (s.relativeProjPoints.algebra T'
                ((yoneda.map τ ≫ x) ≫ f))).algebra.piece d)) _ _ _ _ _ _
    (R.theta_app_eq_pullback τ x d : _)
    _ _ _ _ _ rfl _ _ _ _ _ rfl _ _ ?_ (R.chartTheta_target τ x hx d hx' : _)
  apply source_square_coherence_of_factors
  case hM | hM₂ | hM₃ | hP₀ | hP₀' | hP₀'' | hP₁ | hP₁' | hP₁'' => exact rfl
  case he₁ | he₂ | he₃ | he₁' | he₂' | he₃' => exact HEq.rfl
  case hUx'₃ | hPx'₃ => exact rfl
  case hg'₃ | hrx'₃ | hX'₃ => exact HEq.rfl
  case hσ => exact HEq.rfl
  case hFx₄ | hPx₄ | hFx'₄ | hPx'₄ => exact rfl
  case hcx₄ | htx₄ | hcx'₄ | htx'₄ | hy₄ | hym₄ | hX₄ | hX'₄ | hcy₄ | hAi => exact HEq.rfl
  case hUx'₅ | hUsq₅ | hPx'₅ => exact rfl
  case hj₅ | hrsq₅ | hrx'₅ | hX'₅ => exact HEq.rfl
  case h4 => exact R.toScheme_map_comp_chartSection τ x hx hx' y hy
  case hBi₀ =>
    exact s.quadrupleRestriction.squareThetaSourceIso_inv_app_canHom
        s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf (R.twisting T x)
        ((yoneda.map τ ≫ x) ≫ f) (𝟙 T') τ (yoneda_map_id_comp_assoc s f τ x) d
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
        (s.pointTwistComparison τ (x ≫ f) ((yoneda.map τ ≫ x) ≫ f) (Category.assoc _ _ _).symm
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map y)
          (s.toScheme_map_eq_of_liesOver (Category.assoc _ _ _).symm hy))
        (chartTheta_hcomp τ x y hy) (s.quadrupleRestriction.squareTheta_globalMorphism_comp
          s.shrink.contains_relativeProj_pointAlgebra s.shrink.space.property.isSheaf
          (R.twisting T x) ((yoneda.map τ ≫ x) ≫ f) (𝟙 T') τ (yoneda_map_id_comp_assoc s f τ x) _
          (chartTheta_hcomp τ x y hy)) (chartTheta_hE τ x y hy)
  case hUsq | hUx | hPx | hPx' => exact rfl
  case hrsq | hym | hl | hrx | hX | hG'₀ => exact HEq.rfl
  case hd => exact rfl
  case hcy | hBs => exact HEq.rfl

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
