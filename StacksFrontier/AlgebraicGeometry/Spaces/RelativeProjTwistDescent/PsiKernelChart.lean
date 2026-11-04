module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiKernelBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.Psi

/-!
# The kernel of an adjoint of `ψ` read on the atlas of a relative Proj

Let `π : P ⟶ X` be a relative Proj with scheme points (Stacks 084B), `u : U ⟶ X` the atlas of a
presentation of `X`, `c : P_U ⟶ P` the atlas of the induced presentation of `P` and
`π_U : P_U ⟶ U` the base change of `π`.  The chart identification
`c^*(π^*𝒜_n) ≅ (π_U^*(u^*𝒜)_n)^a` of Stacks 084D begins with the comparison of the two composite
inverse images around the square `c ≫ π = π_U ≫ u`; precomposed with the inverse of that
comparison it is the inverse image along `π_U` of the identification of `u^*𝒜_n` with the module
attached to its Zariski reading, followed by the identification of the inverse image of an
attached module.  This is the step of the chart dictionary of Stacks 085L that turns the base
change of an adjoint of `ψ` into a morphism of attached modules.

## Main results

* `AlgebraicGeometry.Space.C1359Bridge.map_homEquiv_comp_eq_homEquiv`: the reading of an adjoint
  through a mate identity.
* `AlgebraicGeometry.Space.C1359Bridge.squareComparison_app_eq`.
* `AlgebraicGeometry.Space.C1359Bridge.chartPullbackIso_eq_squareComparison`.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 085L](https://stacks.math.columbia.edu/tag/085L)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space.C1359Bridge

open RelativeProjPoints

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Abstract

variable {𝓜 𝓜' 𝓩 𝓩' : Type*} [Category 𝓜] [Category 𝓜'] [Category 𝓩] [Category 𝓩']
  {L : 𝓜 ⥤ 𝓜'} {Rt pf : 𝓜' ⥤ 𝓜} (adj : L ⊣ Rt) (adj' : L ⊣ pf) (p : pf ≅ Rt)
  (hunit : ∀ N, adj.unit.app N = adj'.unit.app N ≫ p.hom.app (L.obj N))
  (RT : 𝓜 ⥤ 𝓩) (RT' : 𝓜' ⥤ 𝓩') {rs : 𝓩 ⥤ 𝓩'} {rp : 𝓩' ⥤ 𝓩} (adjS : rs ⊣ rp)
  (zD : pf ⋙ RT ⟶ RT' ⋙ rp)

include hunit in
/-- **The reading of an adjoint through a mate identity.**  Let `L ⊣ R_t` and `L ⊣ p_f` be two
adjunctions whose units differ by an isomorphism `p : p_f ≅ R_t`, let `R_T`, `R_{T'}` be readings
and `ζ : R_T ∘ p_f ⟶ r_* ∘ R_{T'}` a comparison, and suppose the scheme-side transpose of
`R_T(η') ≫ ζ` is `r^*(a⁻¹) ≫ C` for an isomorphism `a`.  Then the reading of the adjoint of any
`v : L N ⟶ H`, followed by `R_T(p⁻¹) ≫ ζ`, is the scheme-side adjoint of
`r^*(a⁻¹) ≫ C ≫ R_{T'}(v)`. -/
theorem map_homEquiv_comp_eq_homEquiv {N : 𝓜} {H : 𝓜'} {Z₀ : 𝓩} (a : Z₀ ≅ RT.obj N)
    (C : rs.obj Z₀ ⟶ RT'.obj (L.obj N))
    (hUZ : rs.map a.hom ≫ (adjS.homEquiv _ _).symm
      (RT.map (adj'.unit.app N) ≫ zD.app (L.obj N)) = C) (v : L.obj N ⟶ H) :
    RT.map (adj.homEquiv N H v) ≫ RT.map (p.inv.app H) ≫ zD.app H =
      adjS.homEquiv _ _ (rs.map a.inv ≫ C ≫ RT'.map v) := by
  have h1 : adjS.homEquiv _ _ (rs.map a.inv ≫ C) =
      RT.map (adj'.unit.app N) ≫ zD.app (L.obj N) := by
    rw [← hUZ, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact Equiv.apply_symm_apply _ _
  have h3 : p.hom.app (L.obj N) ≫ Rt.map v ≫ p.inv.app H = pf.map v := by
    rw [p.inv.naturality, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  have h4 := zD.naturality v
  dsimp only [Functor.comp_map] at h4
  calc RT.map (adj.homEquiv N H v) ≫ RT.map (p.inv.app H) ≫ zD.app H
      = RT.map (adj'.unit.app N) ≫ RT.map (p.hom.app (L.obj N) ≫ Rt.map v ≫ p.inv.app H) ≫
          zD.app H := by
        rw [Adjunction.homEquiv_unit, hunit]
        simp only [Functor.map_comp, Category.assoc]
    _ = (RT.map (adj'.unit.app N) ≫ zD.app (L.obj N)) ≫ rp.map (RT'.map v) := by
        rw [h3, Category.assoc, h4]
    _ = adjS.homEquiv _ _ (rs.map a.inv ≫ C) ≫ rp.map (RT'.map v) := by rw [h1]
    _ = adjS.homEquiv _ _ (rs.map a.inv ≫ C ≫ RT'.map v) := by
        rw [← Category.assoc]
        exact (adjS.homEquiv_naturality_right _ _).symm

end Abstract

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y')
  (g' : X' ⟶ X) (comm : g' ≫ f = f' ≫ g)

/-- The comparison of the two composite inverse images around a square is its definition, as an
equation of natural transformations. -/
theorem modulePullbackSquareComparison_hom_def :
    (modulePullbackSquareComparison f g f' g' comm).hom =
      (modulePullbackCompIso B S hS g' f).hom ≫
        eqToHom (congrArg (fun k : X' ⟶ Y => modulePullback B S hS k) comm) ≫
        (modulePullbackCompIso B S hS f' g).inv :=
  rfl

/-- The comparison of the two composite inverse images around a square, at a module. -/
theorem modulePullbackSquareComparison_hom_app (F : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullbackSquareComparison f g f' g' comm).hom.app F =
      (modulePullbackCompIso B S hS g' f).hom.app F ≫
        eqToHom (congrArg (fun k : X' ⟶ Y => (modulePullback B S hS k).obj F) comm) ≫
        (modulePullbackCompIso B S hS f' g).inv.app F := by
  have h1 : (modulePullbackSquareComparison f g f' g' comm).hom.app F =
      (modulePullbackCompIso B S hS g' f).hom.app F ≫
        ((eqToHom (congrArg (fun k : X' ⟶ Y => modulePullback B S hS k) comm)).app F ≫
          (modulePullbackCompIso B S hS f' g).inv.app F) :=
    (NatTrans.congr_app (modulePullbackSquareComparison_hom_def f g f' g' comm) F).trans
      ((NatTrans.comp_app _ _ _).trans (congrArg (_ ≫ ·) (NatTrans.comp_app _ _ _)))
  have h2 : (eqToHom (congrArg (fun k : X' ⟶ Y => modulePullback B S hS k) comm)).app F =
      eqToHom (congrArg (fun k : X' ⟶ Y => (modulePullback B S hS k).obj F) comm) :=
    eqToHom_app _ _
  rw [h1, h2]

/-- **The comparison of the two composite inverse images around a square, at a module**, as
isomorphisms: the composition comparison along `g' ≫ f`, the transport along the square, and the
inverse of the composition comparison along `f' ≫ g`. -/
theorem squareComparison_app_eq (F : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullbackSquareComparison f g f' g' comm).app F =
      (modulePullbackCompIso B S hS g' f).app F ≪≫
        eqToIso (congrArg (fun k : X' ⟶ Y => (modulePullback B S hS k).obj F) comm) ≪≫
        ((modulePullbackCompIso B S hS f' g).app F).symm :=
  Iso.ext ((modulePullbackSquareComparison_hom_app f g f' g' comm F).trans (by
    rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv, eqToIso.hom]))

end Square

variable {X : AlgebraicSpaces B S hS} {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {π : P ⟶ X.obj}
  (d : RelativeProjPoints B S hS π) (Px : Presentation B S hS X.obj X.property)
  (hP : IsAlgebraicSpace B S hS P)
  (A : SheafOfModules.GradedAlgebra.{u, u} (structureRingSheaf B S hS X))
  (hA : ∀ n, (A.piece n).IsQuasicoherentOnSite)

/-- **The chart identification of `π^*𝒜_n` through the square comparison.**  The chart
identification `c^*(π^*𝒜_n) ≅ (π_U^*(u^*𝒜)_n)^a` is the comparison `c^*π^* ≅ π_U^*u^*` of the
square `c ≫ π = π_U ≫ u`, followed by the inverse image along `π_U` of the identification
`u^*𝒜_n ≅ ((u^*𝒜_n)_{Zar})^a` and the identification of the inverse image of an attached module. -/
theorem chartPullbackIso_eq_squareComparison (n : ℤ) :
    d.chartPullbackIso Px hP A hA n =
      (modulePullbackSquareComparison
        (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
        (pointHom Px.toSpace) (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))
        (presentationAtlas (d.spacePresentation Px hP))
        (d.presentationAtlas_comp_homMk Px hP)).app (A.piece n) ≪≫
      (modulePullback B S hS (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))).mapIso
        (zariskiReadingQuasicoherentIso Px.U ((etalePointAlgebra A Px.U Px.toSpace).piece n)
          (isQuasicoherentOnSite_etalePointAlgebra_piece A hA Px.toSpace n)) ≪≫
      modulePullbackRepresentedQuasicoherentIso B S hS (d.fibreHom Px.U Px.toSpace)
        (presentationPointPieceQcoh Px A hA n) := by
  refine Eq.trans ?_ (congrArg (· ≪≫ _) (squareComparison_app_eq
    (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ X)
    (pointHom Px.toSpace) (representedSpaceMap B S hS (d.fibreHom Px.U Px.toSpace))
    (presentationAtlas (d.spacePresentation Px hP))
    (d.presentationAtlas_comp_homMk Px hP) (A.piece n))).symm
  refine Eq.trans ?_ (Iso.trans_assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg (_ ≪≫ ·) (Iso.trans_assoc _ _ _)).symm
  rfl

end AlgebraicGeometry.Space.C1359Bridge

end
