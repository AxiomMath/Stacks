module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianBaseChangeUlift
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianBaseChangeQuasiIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianBaseChangeQuasiIsoConverse

/-!
# Proper base change for abelian sheaves at every coefficient universe

WIP.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.UniverseLift

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.EtaleCohomology

attribute [-instance] Stacks.SheafOfModules.coefficientSheafification

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
  Preadditive.preadditiveHasZeroMorphisms

section Complexes

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- **The base change comparison at a universe lift, followed by a morphism.** For an abelian
sheaf `M` on `X_étale` with coefficients in `AddCommGrpCat.{u + 1}` and a morphism
`q : (g')⁻¹ M ⟶ N`, the comparison `g⁻¹ f_* (U M) ⟶ f'_* (g')⁻¹ (U M)` followed by `f'_*` of
`λ_{g'}` and of `U q`, read in `U (f'_* N)`, is `λ_g` followed by the universe lift of the
comparison `g⁻¹ f_* M ⟶ f'_* (g')⁻¹ M ⟶ f'_* N`. -/
theorem etaleAbelianBaseChange_ulift_comp (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {N : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (q : (etaleAbelianInverseImage.{u, 0} g').obj M ⟶ N) :
    (etaleAbelianBaseChange.{u, v} f g g' f' h).app ((etaleUlift.{v} X).obj M) ≫
        (etaleAbelianDirectImage.{u, v} f').map
          ((etaleAbelianInverseImageUliftMate.{v} g').app M ≫ (etaleUlift.{v} X').map q) ≫
        (etaleAbelianDirectImageUliftIso.{v} f').inv.app N =
      (etaleAbelianInverseImageUliftMate.{v} g).app ((etaleAbelianDirectImage.{u, 0} f).obj M) ≫
        (etaleUlift.{v} Y').map ((etaleAbelianBaseChange.{u, 0} f g g' f' h).app M ≫
          (etaleAbelianDirectImage.{u, 0} f').map q) := by
  have hn := (etaleAbelianDirectImageUliftIso.{v} f').inv.naturality q
  simp only [Functor.comp_map] at hn
  rw [Functor.map_comp, Category.assoc, hn,
    reassoc_of% (etaleAbelianBaseChange_ulift.{v} f g g' f' h M), Functor.map_comp,
    etaleAbelianDirectImageUliftIso_inv_app]
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (congrArg (_ ≫ ·) (Category.id_comp _)))

end Complexes

section EtaleAbstract

variable {X X' Y' : Scheme.{u}}
  {A₀ : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
    Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}}
  {B₀ : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
    Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}}
  {F₀ : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
    Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1}}
  {A₁ : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
    Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  {B₁ : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
    Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  {F₁ : Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v} ⥤
    Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  [A₀.Additive] [B₀.Additive] [F₀.Additive] [A₁.Additive] [B₁.Additive] [F₁.Additive]
  {UX : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
    Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  {UX' : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
    Sheaf X'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  {UY' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
    Sheaf Y'.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}}
  [UX.Additive] [UX'.Additive] [UY'.Additive]
  [PreservesFiniteLimits UY'] [PreservesFiniteColimits UY']

/-- **A degreewise comparison through a resolution, transported along exact functors.** Let
`α_i : A_i ⟶ B_i ⋙ F_i` be comparisons at two levels `i = 0, 1`, related by functors `U` through
invertible comparisons `λ_A : U ⋙ A_1 ⟶ A_0 ⋙ U` and `λ_B : U ⋙ B_1 ⟶ B_0 ⋙ U` and an
isomorphism `ρ : U ⋙ F_1 ≅ F_0 ⋙ U`, compatibly (`hE`). If for complexes `I`, `L` and
`q : B_0(I) ⟶ L` the morphism `α_0 ≫ F_0(q)` is a quasi-isomorphism, so is
`α_1 ≫ F_1(λ_B ≫ U q)` at `U I`, the target functor `U` being exact. -/
theorem quasiIso_etaleNatTrans_comp_of_lift (α₀ : A₀ ⟶ B₀ ⋙ F₀) (α₁ : A₁ ⟶ B₁ ⋙ F₁)
    (lA : UX ⋙ A₁ ⟶ A₀ ⋙ UY') [∀ M, IsIso (lA.app M)] (lB : UX ⋙ B₁ ⟶ B₀ ⋙ UX')
    (ρ : UX' ⋙ F₁ ≅ F₀ ⋙ UY')
    (hE : ∀ (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      {N : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}} (q : B₀.obj M ⟶ N),
      α₁.app (UX.obj M) ≫ F₁.map (lB.app M ≫ UX'.map q) ≫ ρ.hom.app N =
        lA.app M ≫ UY'.map (α₀.app M ≫ F₀.map q))
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (L : CochainComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (q : (B₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ L)
    (hq : QuasiIso ((NatTrans.mapHomologicalComplex α₀ (ComplexShape.up ℤ)).app I ≫
      (F₀.mapHomologicalComplex (ComplexShape.up ℤ)).map q)) :
    QuasiIso
      ((NatTrans.mapHomologicalComplex α₁ (ComplexShape.up ℤ)).app
          ((UX.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        (F₁.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex lB (ComplexShape.up ℤ)).app I ≫
            (UX'.mapHomologicalComplex (ComplexShape.up ℤ)).map q)) := by
  set φ := (NatTrans.mapHomologicalComplex α₀ (ComplexShape.up ℤ)).app I ≫
    (F₀.mapHomologicalComplex (ComplexShape.up ℤ)).map q
  set y := (NatTrans.mapHomologicalComplex α₁ (ComplexShape.up ℤ)).app
          ((UX.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        (F₁.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex lB (ComplexShape.up ℤ)).app I ≫
            (UX'.mapHomologicalComplex (ComplexShape.up ℤ)).map q)
  let e₁ : (A₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((UX.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      (UY'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((A₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    HomologicalComplex.Hom.isoOfComponents (fun n => asIso (lA.app (I.X n)))
      (fun i j _ => (lA.naturality (I.d i j)).symm)
  let e₂ : (F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((UX'.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≅
      (UY'.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((F₀.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
    HomologicalComplex.Hom.isoOfComponents (fun n => ρ.app (L.X n))
      (fun i j _ => (ρ.hom.naturality (L.d i j)).symm)
  have hxy : y ≫ e₂.hom = e₁.hom ≫ (UY'.mapHomologicalComplex (ComplexShape.up ℤ)).map φ := by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    simp only [y, φ, e₁, e₂, HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplex_map_f, HomologicalComplex.Hom.isoOfComponents_hom_f,
      Iso.app_hom, Category.assoc]
    exact hE (I.X n) (q.f n)
  have : UY'.PreservesHomology := Functor.preservesHomologyOfExact _
  exact (quasiIso_iff_of_arrow_mk_iso _ _ (Arrow.isoMk e₁ e₂ hxy.symm)).2
    (HomologicalComplex.quasiIso_map_of_preservesHomology (φ := φ) (F := UY') (hφ := hq))

end EtaleAbstract


section Lift

variable {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
  (h : g' ≫ f = f' ≫ g)

/-- The comparison `g⁻¹ f_* ∘ U ⟶ U ∘ g⁻¹ f_*`: the comparison `λ_g` at direct images, direct
image commuting with the universe lift on the nose. -/
def etaleAbelianDirectInverseImageUliftMate :
    etaleUlift.{v} X ⋙ (etaleAbelianDirectImage.{u, v} f ⋙ etaleAbelianInverseImage.{u, v} g) ⟶
      (etaleAbelianDirectImage.{u, 0} f ⋙ etaleAbelianInverseImage.{u, 0} g) ⋙
        etaleUlift.{v} Y' where
  app M := (etaleAbelianInverseImageUliftMate.{v} g).app ((etaleAbelianDirectImage.{u, 0} f).obj M)
  naturality _ _ φ := (etaleAbelianInverseImageUliftMate.{v} g).naturality
    ((etaleAbelianDirectImage.{u, 0} f).map φ)

/-- The comparison `g⁻¹ f_* (U M) ⟶ U (g⁻¹ f_* M)` is an isomorphism for every abelian sheaf `M`
on `X_étale`. -/
instance (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso ((etaleAbelianDirectInverseImageUliftMate.{v} f g).app M) :=
  isIso_etaleAbelianInverseImageUliftMate_app g _

/-- **The degreewise base change comparison through a resolution, at a universe lift.** For
complexes `I` on `X_étale` and `L` on `X'_étale` with coefficients in `AddCommGrpCat.{u + 1}` and a
morphism `q : (g')⁻¹ I ⟶ L`, if `g⁻¹ f_* I ⟶ f'_* (g')⁻¹ I ⟶ f'_* L` is a quasi-isomorphism, so is
`g⁻¹ f_* (U I) ⟶ f'_* (g')⁻¹ (U I) ⟶ f'_* (U L)`, the second arrow being `f'_*` of `λ_{g'}`
followed by `U q`. -/
theorem quasiIso_etaleAbelianBaseChange_comp_ulift
    (I : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (L : CochainComplex (Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}) ℤ)
    (q : ((etaleAbelianInverseImage.{u, 0} g').mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ L)
    (hq : QuasiIso
      ((NatTrans.mapHomologicalComplex (etaleAbelianBaseChange.{u, 0} f g g' f' h)
          (ComplexShape.up ℤ)).app I ≫
        ((etaleAbelianDirectImage.{u, 0} f').mapHomologicalComplex (ComplexShape.up ℤ)).map q)) :
    QuasiIso
      ((NatTrans.mapHomologicalComplex (etaleAbelianBaseChange.{u, v} f g g' f' h)
          (ComplexShape.up ℤ)).app (((etaleUlift.{v} X).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I) ≫
        ((etaleAbelianDirectImage.{u, v} f').mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex (etaleAbelianInverseImageUliftMate.{v} g')
              (ComplexShape.up ℤ)).app I ≫
            ((etaleUlift.{v} X').mapHomologicalComplex (ComplexShape.up ℤ)).map q)) := by
  have hE : ∀ (M : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
      {N : Sheaf X'.smallEtaleTopology AddCommGrpCat.{u + 1}}
      (q : (etaleAbelianInverseImage.{u, 0} g').obj M ⟶ N),
      (etaleAbelianBaseChange.{u, v} f g g' f' h).app ((etaleUlift.{v} X).obj M) ≫
        (etaleAbelianDirectImage.{u, v} f').map
          ((etaleAbelianInverseImageUliftMate.{v} g').app M ≫ (etaleUlift.{v} X').map q) ≫
        (etaleAbelianDirectImageUliftIso.{v} f').symm.hom.app N =
      (etaleAbelianDirectInverseImageUliftMate.{v} f g).app M ≫
        (etaleUlift.{v} Y').map ((etaleAbelianBaseChange.{u, 0} f g g' f' h).app M ≫
          (etaleAbelianDirectImage.{u, 0} f').map q) :=
    fun M _ q => etaleAbelianBaseChange_ulift_comp f g g' f' h M q
  have hA : ∀ M, IsIso ((etaleAbelianDirectInverseImageUliftMate.{v} f g).app M) :=
    fun M => inferInstance
  -- the comparisons are made variables, so that the kernel compares the instantiation of the
  -- abstract statement with this one without unfolding them
  generalize etaleAbelianBaseChange.{u, v} f g g' f' h = α₁ at hE ⊢
  generalize etaleAbelianBaseChange.{u, 0} f g g' f' h = α₀ at hE hq ⊢
  generalize etaleAbelianInverseImageUliftMate.{v} g' = lB at hE ⊢
  generalize etaleAbelianDirectInverseImageUliftMate.{v} f g = lA at hE hA
  generalize (etaleAbelianDirectImageUliftIso.{v} f').symm = ρ at hE
  exact quasiIso_etaleNatTrans_comp_of_lift α₀ α₁ lA lB ρ hE I L q hq

end Lift

end Stacks.EtaleCohomology

end
