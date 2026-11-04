module

public import StacksFrontier.AlgebraicGeometry.Morphism.TwistPsi
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.BaseChangeInG

/-!
# Chases with inverse images of sections

Small general facts about inverse images of sections along morphisms of schemes, used to compute
composites of the pseudofunctoriality isomorphisms of the inverse image on such sections.

## Main results

* `Stacks.AlgebraicGeometry.GradedAlgebraHomSections.app_unitApp_mul`: a map of graded algebras out
  of a pulled-back graded algebra is multiplicative on the inverse images of sections.
* `…pullbackId_hom_app_unitApp`, `…retract_chase`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.SectionRingBaseChange (unitApp unitApp_naturality unitApp_map
  hom_app_map map_map_homOfLE)

universe u

namespace Stacks.AlgebraicGeometry.GradedAlgebraHomSections

-- `CategoryTheory.catToReflQuiver` offers a second route from `Category` to `Quiver`; see
-- `Stacks.AlgebraicGeometry.ProjectiveDeformation.TwistSections`.
attribute [-instance] CategoryTheory.catToReflQuiver

variable {Z Y : Scheme.{u}}

/-- **A map of graded algebras out of a pulled-back graded algebra is multiplicative on the inverse
images of sections.** -/
theorem app_unitApp_mul (h : Z ⟶ Y) (G : SheafOfModules.GradedAlgebra.{u, u} Y.ringCatSheaf)
    {H : SheafOfModules.GradedAlgebra.{u, u} Z.ringCatSheaf}
    (Θ : SheafOfModules.GradedAlgebra.Hom (Stacks.Conormal.gradedPullback h G) H) (i j : ℤ)
    (O : Y.Opens) (s : Γ(G.piece i, O)) (t : Γ(G.piece j, O)) :
    Scheme.Modules.Hom.app (Θ.app (i + j)) (h ⁻¹ᵁ O)
        (unitApp h (G.piece (i + j)) O ((G.mul i j).app (op O) s t)) =
      (H.mul i j).app (op (h ⁻¹ᵁ O)) (Scheme.Modules.Hom.app (Θ.app i) (h ⁻¹ᵁ O)
        (unitApp h (G.piece i) O s)) (Scheme.Modules.Hom.app (Θ.app j) (h ⁻¹ᵁ O)
          (unitApp h (G.piece j) O t)) :=
  (congrArg (fun z => (Θ.app (i + j)).val.app (op (h ⁻¹ᵁ O)) z)
    (Stacks.RingedSpace.pullbackGradedAlgebra_mul_pullbackUnit h.toLRSHom.toShHom G i j O s
      t).symm).trans (Θ.map_mul i j (op (h ⁻¹ᵁ O)) _ _)

/-- The identification `(𝟙 X)^* M ≅ M` on the inverse image of a section. -/
theorem pullbackId_hom_app_unitApp {X : Scheme.{u}} (M : X.Modules) (W : X.Opens) (x : Γ(M, W)) :
    ((Scheme.Modules.pullbackId X).hom.app M).app W (unitApp (𝟙 X) M W x) = x := by
  have h := Stacks.AlgebraicGeometry.ModuleLimits.pullbackIdHom_pullbackSection_self M W x
  have h2 : Scheme.Modules.pullbackSection (𝟙 X) M W W le_rfl x = unitApp (𝟙 X) M W x :=
    Stacks.Conormal.pullbackSection_self (𝟙 X) M W x
  rw [h2] at h
  exact h

/-- A morphism of modules commutes with restriction along `U' ≤ U`, given its value on `x`. -/
private theorem app_map_homOfLE_of_app_eq {X : Scheme.{u}} {A B : X.Modules} (φ : A ⟶ B)
    {U' U : X.Opens} (h : U' ≤ U) {x : Γ(A, U)} {y : Γ(B, U)} (hxy : φ.app U x = y) :
    φ.app U' (A.presheaf.map (homOfLE h).op x) = B.presheaf.map (homOfLE h).op y :=
  (hom_app_map φ h x).trans (congrArg _ hxy)

/-- **The chase through a retraction of an open immersion.** For `r : P ⟶ D` with
`r ≫ ι = 𝟙 P` and a map `θ : rel^* M ⟶ ι^* N` carrying the inverse image of `p` to the restriction
of the inverse image of `q`, the composite `(r ≫ rel)^* M ⟶ r^* rel^* M ⟶ r^* ι^* N ⟶
(r ≫ ι)^* N = N` carries the inverse image of `p` to the restriction of `q`. -/
theorem retract_chase {P D X : Scheme.{u}} (r : P ⟶ D) (rel : D ⟶ X) (ι : D ⟶ P)
    (hr : r ≫ ι = 𝟙 P) {M : X.Modules} {N : P.Modules}
    (θ : (Scheme.Modules.pullback rel).obj M ⟶ (Scheme.Modules.pullback ι).obj N)
    (Wa : X.Opens) (Wb : P.Opens) (h1 : rel ⁻¹ᵁ Wa ≤ ι ⁻¹ᵁ Wb) (p : Γ(M, Wa)) (q : Γ(N, Wb))
    (hθ : θ.app (rel ⁻¹ᵁ Wa) (unitApp rel M Wa p) =
      ((Scheme.Modules.pullback ι).obj N).presheaf.map (homOfLE h1).op (unitApp ι N Wb q))
    (hfin : (r ≫ rel) ⁻¹ᵁ Wa ≤ Wb) :
    Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp r rel).inv.app M ≫
        (Scheme.Modules.pullback r).map θ ≫ (Scheme.Modules.pullbackComp r ι).hom.app N ≫
        (Scheme.Modules.pullbackCongr hr).hom.app N ≫ (Scheme.Modules.pullbackId P).hom.app N)
        ((r ≫ rel) ⁻¹ᵁ Wa) (unitApp (r ≫ rel) M Wa p) =
      N.presheaf.map (homOfLE hfin).op q := by
  let N' := (Scheme.Modules.pullback ι).obj N
  have hle : r ⁻¹ᵁ rel ⁻¹ᵁ Wa ≤ r ⁻¹ᵁ ι ⁻¹ᵁ Wb := r.preimage_mono h1
  have hle' : r ⁻¹ᵁ rel ⁻¹ᵁ Wa ≤ (r ≫ ι) ⁻¹ᵁ Wb := hle
  have hle'' : r ⁻¹ᵁ rel ⁻¹ᵁ Wa ≤ (𝟙 P) ⁻¹ᵁ Wb := by simpa using hfin
  have hcg : (r ≫ ι) ⁻¹ᵁ Wb ≤ (𝟙 P) ⁻¹ᵁ Wb := by rw [hr]
  have sB : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp r rel).inv.app M)
      (r ⁻¹ᵁ rel ⁻¹ᵁ Wa) (unitApp (r ≫ rel) M Wa p) =
      unitApp r ((Scheme.Modules.pullback rel).obj M) (rel ⁻¹ᵁ Wa) (unitApp rel M Wa p) :=
    Scheme.Modules.pullbackComp_inv_unit r rel M Wa p
  have sC : Scheme.Modules.Hom.app ((Scheme.Modules.pullback r).map θ) (r ⁻¹ᵁ rel ⁻¹ᵁ Wa)
      (unitApp r ((Scheme.Modules.pullback rel).obj M) (rel ⁻¹ᵁ Wa) (unitApp rel M Wa p)) =
      ((Scheme.Modules.pullback r).obj N').presheaf.map (homOfLE hle).op
        (unitApp r N' (ι ⁻¹ᵁ Wb) (unitApp ι N Wb q)) :=
    (unitApp_naturality r θ (rel ⁻¹ᵁ Wa) (unitApp rel M Wa p)).trans
      ((congrArg (unitApp r N' (rel ⁻¹ᵁ Wa)) hθ).trans (unitApp_map r N' h1 (unitApp ι N Wb q)))
  have sE : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackComp r ι).hom.app N)
      (r ⁻¹ᵁ rel ⁻¹ᵁ Wa) (((Scheme.Modules.pullback r).obj N').presheaf.map (homOfLE hle).op
        (unitApp r N' (ι ⁻¹ᵁ Wb) (unitApp ι N Wb q))) =
      ((Scheme.Modules.pullback (r ≫ ι)).obj N).presheaf.map (homOfLE hle').op
        (unitApp (r ≫ ι) N Wb q) :=
    app_map_homOfLE_of_app_eq _ hle
      (Stacks.AlgebraicGeometry.TwistMulLeg.pullbackComp_hom_app_unitApp r ι N Wb q)
  have sF : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackCongr hr).hom.app N)
      (r ⁻¹ᵁ rel ⁻¹ᵁ Wa) (((Scheme.Modules.pullback (r ≫ ι)).obj N).presheaf.map (homOfLE hle').op
        (unitApp (r ≫ ι) N Wb q)) =
      ((Scheme.Modules.pullback (𝟙 P)).obj N).presheaf.map (homOfLE hle'').op
        (unitApp (𝟙 P) N Wb q) :=
    (app_map_homOfLE_of_app_eq _ hle'
      (Stacks.AlgebraicGeometry.TwistMulLeg.pullbackCongr_hom_app_unitApp hr N Wb q)).trans
      (map_map_homOfLE _ hle' hcg hle'' _)
  have sG : Scheme.Modules.Hom.app ((Scheme.Modules.pullbackId P).hom.app N)
      (r ⁻¹ᵁ rel ⁻¹ᵁ Wa) (((Scheme.Modules.pullback (𝟙 P)).obj N).presheaf.map (homOfLE hle'').op
        (unitApp (𝟙 P) N Wb q)) = N.presheaf.map (homOfLE hfin).op q :=
    app_map_homOfLE_of_app_eq _ hle'' (pullbackId_hom_app_unitApp N Wb q)
  simp only [Stacks.AlgebraicGeometry.TwistMulLeg.app_comp_apply]
  erw [sB, sC, sE, sF, sG]

end Stacks.AlgebraicGeometry.GradedAlgebraHomSections

end
