module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeTransformation
import all StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeTransformation

/-!
# The derived base change map computed on complexes which compute the derived functors

`Stacks.Cohomology.UnboundedComplexes.nonempty_derivedBaseChangeMapArrowIso` computes the
derived base change map `RF ⋙ Dβ ⟶ Dα ⋙ RF'` of `θ : F ⋙ β ⟶ α ⋙ F'` at a K-injective complex
`I`, through a K-injective resolution `t : α(I) ⟶ J`. The argument only uses that the
derived-functor units of `RF` at `I` and of `RF'` at `J` are invertible, that is, that `I`
computes `RF` and `J` computes `RF'`. This file records the computation under that weaker
hypothesis, and the corresponding comparison of the derived base change maps of a cube of
comparison functors, where the comparison functors need not preserve K-injectivity: it suffices
that they carry the chosen complexes to complexes computing the derived functors. This is the
situation of a comparison functor like `ε⁻¹ : D(X_étale) ⥤ D(X_proétale)`, which carries bounded
below complexes of injectives to bounded below complexes of acyclic objects.

## Main results

* `Stacks.Cohomology.UnboundedComplexes.nonempty_derivedBaseChangeMapArrowIso_of_isIso`.
* `Stacks.Cohomology.UnboundedComplexes.isIso_derivedBaseChangeMap_app_iff_of_cube_of_isIso`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.UnboundedComplexes

universe wA wA' dA dA' dB dB' vA uA vA' uA' vB uB vB' uB'
universe wC wC' dC dC' dE dE' vC uC vC' uC' vE uE vE' uE'

section Map

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{dA} A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [HasDerivedCategory.{dA'} A']
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{dB} B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [HasDerivedCategory.{dB'} B']
  (α : A ⥤ A') [α.Additive] [PreservesFiniteLimits α] [PreservesFiniteColimits α]
  (β : B ⥤ B') [β.Additive] [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  (F : A ⥤ B) [F.Additive] (F' : A' ⥤ B') [F'.Additive]
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (RF' : DerivedCategory A' ⥤ DerivedCategory B')
  (αF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  (αF' : F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF')
  (θ : F ⋙ β ⟶ α ⋙ F')
  [IsGrothendieckAbelian.{wA} A]
  [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- **The derived base change map at a complex computing `RF`.** For a complex `I` on `A` at
which the unit of `RF` is invertible and a quasi-isomorphism `t : α(I) ⟶ J` to a complex at which
the unit of `RF'` is invertible, the derived base change map at `I` is isomorphic, as an arrow of
`D(B')`, to the image of `θ_I ≫ F'(t)`. -/
public theorem nonempty_derivedBaseChangeMapArrowIso_of_isIso (I : CochainComplex A ℤ)
    (h₁ : IsIso (αF.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
    {J : CochainComplex A' ℤ} (t : (α.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
    [QuasiIso t]
    (h₂ : IsIso (αF'.app ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj J))) :
    Nonempty (Arrow.mk ((derivedBaseChangeMap α β F F' RF RF' αF αF' θ).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) ≅
      Arrow.mk (DerivedCategory.Qh.map ((HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).app I ≫
          (F'.mapHomologicalComplex (ComplexShape.up ℤ)).map t)))) := by
  let qI := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I
  have h₃ : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map t)) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ)) _
      (by
        rw [HomotopyCategory.quotient_map_mem_quasiIso_iff, HomologicalComplex.mem_quasiIso_iff]
        infer_instance)
  have hnat := αF'.naturality ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map t)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
  have hφ : (derivedBaseChangeMap α β F F' RF RF' αF αF' θ).app (DerivedCategory.Qh.obj qI) =
      inv (β.mapDerivedCategory.map (αF.app qI)) ≫
        (derivedBaseChangeMapUnit α β F F' RF' αF' θ).app qI := by
    rw [← derivedBaseChangeMap_fac_app α β F F' RF RF' αF αF' θ qI, IsIso.inv_hom_id_assoc]
  have key : (inv (β.mapDerivedCategory.map (αF.app qI)) ≫
        β.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj qI)) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).app I ≫
            (F'.mapHomologicalComplex (ComplexShape.up ℤ)).map t)) =
      (derivedBaseChangeMap α β F F' RF RF' αF αF' θ).app (DerivedCategory.Qh.obj qI) ≫
        RF'.map (α.mapDerivedCategoryFactorsh.hom.app qI) ≫
        RF'.map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map t)) ≫
        inv (αF'.app ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj J)) := by
    rw [hφ, derivedBaseChangeMapUnit_app_quotient]
    refine reassociate_aux _ _ _ _ _ _ _ _ _
      (αF'.app ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj J))
      ((congrArg DerivedCategory.Qh.map ((HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map_comp
        ((NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).app I)
        ((F'.mapHomologicalComplex (ComplexShape.up ℤ)).map t))).trans
        (DerivedCategory.Qh.map_comp _ _))
      ((RF'.map_comp _ _).symm.trans ((congrArg RF'.map
        (α.mapDerivedCategoryFactorsh.inv_hom_id_app qI)).trans (RF'.map_id _)))
      hnat (IsIso.hom_inv_id _)
  exact ⟨Arrow.isoMk
    ((asIso (β.mapDerivedCategory.map (αF.app qI))).symm ≪≫
      β.mapDerivedCategoryFactorsh.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj qI))
    (RF'.mapIso (α.mapDerivedCategoryFactorsh.app qI) ≪≫
      RF'.mapIso (@asIso _ _ _ _ (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map t)) h₃) ≪≫
      (asIso (αF'.app ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj J))).symm) key⟩

/-- **The derived base change map is characterized by its defining equation.** A transformation
`τ : RF ⋙ Dβ ⟶ Dα ⋙ RF'` which, precomposed with the exactness comparison for `β` and with `Dβ`
of the derived-functor unit of `RF`, is the degreewise action of `θ` followed by the
derived-functor unit of `RF'` and the exactness comparison for `α`, is the derived base change
map of `θ`. -/
public theorem eq_derivedBaseChangeMap_of_fac
    (τ : RF ⋙ β.mapDerivedCategory ⟶ α.mapDerivedCategory ⋙ RF')
    (h : ∀ K : HomotopyCategory A (ComplexShape.up ℤ),
      β.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          β.mapDerivedCategory.map (αF.app K) ≫ τ.app (DerivedCategory.Qh.obj K) =
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ β)) (ComplexShape.up ℤ)).hom.app K ≫
            (NatTrans.mapHomotopyCategory θ (ComplexShape.up ℤ)).app K ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (α ⋙ F'))
              (ComplexShape.up ℤ)).inv.app K) ≫
          αF'.app ((α.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
          RF'.map (α.mapDerivedCategoryFactorsh.inv.app K)) :
    τ = derivedBaseChangeMap α β F F' RF RF' αF αF' θ := by
  have := isRightDerivedFunctor_comp (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh) DerivedCategory.Qh RF αF β.mapDerivedCategory
  refine Functor.rightDerived_ext _
    (Functor.whiskerRight αF β.mapDerivedCategory ≫ (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _ _ _ ?_
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id]
  rw [derivedBaseChangeMap_fac_app, derivedBaseChangeMapUnit_app, NatTrans.comp_app,
    NatTrans.comp_app, ← h K]
  simp

end Map

section Cube

/-- The component of the degreewise action of an invertible transformation is invertible. -/
private theorem isIso_mapHomologicalComplex_app {V W : Type*} [Category V] [Category W]
    [Preadditive V] [Preadditive W] {G₁ G₂ : V ⥤ W} [G₁.Additive] [G₂.Additive] (σ : G₁ ⟶ G₂)
    [IsIso σ] (c : ComplexShape ℤ) (X : HomologicalComplex V c) :
    IsIso ((NatTrans.mapHomologicalComplex σ c).app X) :=
  ((NatIso.mapHomologicalComplex (asIso σ) c).app X).isIso_hom

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{dA} A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [HasDerivedCategory.{dA'} A']
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{dB} B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [HasDerivedCategory.{dB'} B']
  (α : A ⥤ A') [α.Additive] [PreservesFiniteLimits α] [PreservesFiniteColimits α]
  (β : B ⥤ B') [β.Additive] [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  (F : A ⥤ B) [F.Additive] (F' : A' ⥤ B') [F'.Additive]
  (RF : DerivedCategory A ⥤ DerivedCategory B)
  (RF' : DerivedCategory A' ⥤ DerivedCategory B')
  (αF : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF)
  (αF' : F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF')
  (θ : F ⋙ β ⟶ α ⋙ F')
  [IsGrothendieckAbelian.{wA} A]
  [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{dC} C]
  {C' : Type uC'} [Category.{vC'} C'] [Abelian C'] [HasDerivedCategory.{dC'} C']
  {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{dE} E]
  {E' : Type uE'} [Category.{vE'} E'] [Abelian E'] [HasDerivedCategory.{dE'} E']
  (α₁ : C ⥤ C') [α₁.Additive] [PreservesFiniteLimits α₁] [PreservesFiniteColimits α₁]
  (β₁ : E ⥤ E') [β₁.Additive] [PreservesFiniteLimits β₁] [PreservesFiniteColimits β₁]
  (F₁ : C ⥤ E) [F₁.Additive] (F₁' : C' ⥤ E') [F₁'.Additive]
  (RF₁ : DerivedCategory C ⥤ DerivedCategory E)
  (RF₁' : DerivedCategory C' ⥤ DerivedCategory E')
  (αF₁ : F₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF₁)
  (αF₁' : F₁'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF₁')
  (θ₁ : F₁ ⋙ β₁ ⟶ α₁ ⋙ F₁')
  [IsGrothendieckAbelian.{wC} C]
  [RF₁.IsRightDerivedFunctor αF₁ (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
  (ΦA : A ⥤ C) [ΦA.Additive] (ΦA' : A' ⥤ C') [ΦA'.Additive] [PreservesFiniteLimits ΦA']
  [PreservesFiniteColimits ΦA'] (ΦB : B ⥤ E) [ΦB.Additive] (ΦB' : B' ⥤ E') [ΦB'.Additive]
  [PreservesFiniteLimits ΦB'] [PreservesFiniteColimits ΦB']
  (τ₁ : ΦA ⋙ α₁ ⟶ α ⋙ ΦA') [IsIso τ₁] (τ₂ : ΦB ⋙ β₁ ⟶ β ⋙ ΦB') [IsIso τ₂]
  (σG : F ⋙ ΦB ⟶ ΦA ⋙ F₁) [IsIso σG] (σH : ΦA' ⋙ F₁' ⟶ F' ⋙ ΦB') [IsIso σH]

/-- **The derived base change maps of a cube are invertible together**, at a complex `I` and a
resolution `t : α(I) ⟶ J` such that `I`, `J` compute the front derived functors and `ΦA(I)`,
`ΦA'(J)` compute the back ones. No preservation of K-injectivity is assumed. -/
public theorem isIso_derivedBaseChangeMap_app_iff_of_cube_of_isIso
    (hcube : ∀ X : A, τ₂.app (F.obj X) ≫ ΦB'.map (θ.app X) =
      β₁.map (σG.app X) ≫ θ₁.app (ΦA.obj X) ≫ F₁'.map (τ₁.app X) ≫ σH.app (α.obj X))
    (I : CochainComplex A ℤ)
    (hI : IsIso (αF.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))
    (hΦI : IsIso (αF₁.app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
      ((ΦA.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))))
    {J : CochainComplex A' ℤ} (t : (α.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
    [QuasiIso t]
    (hJ : IsIso (αF'.app ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj J)))
    (hΦJ : IsIso (αF₁'.app ((HomotopyCategory.quotient C' (ComplexShape.up ℤ)).obj
      ((ΦA'.mapHomologicalComplex (ComplexShape.up ℤ)).obj J)))) :
    IsIso ((derivedBaseChangeMap α₁ β₁ F₁ F₁' RF₁ RF₁' αF₁ αF₁' θ₁).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          ((ΦA.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))) ↔
      IsIso (ΦB'.mapDerivedCategory.map ((derivedBaseChangeMap α β F F' RF RF' αF αF' θ).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))) := by
  let c := ComplexShape.up ℤ
  let T₁ := (NatTrans.mapHomologicalComplex τ₁ c).app I
  have : IsIso T₁ := isIso_mapHomologicalComplex_app τ₁ c I
  let t₁ : (α₁.mapHomologicalComplex c).obj ((ΦA.mapHomologicalComplex c).obj I) ⟶
      (ΦA'.mapHomologicalComplex c).obj J := T₁ ≫ (ΦA'.mapHomologicalComplex c).map t
  have : ΦA'.PreservesHomology := Functor.preservesHomologyOfExact ΦA'
  have : QuasiIso t₁ := quasiIso_comp T₁ ((ΦA'.mapHomologicalComplex c).map t)
  obtain ⟨eback⟩ := nonempty_derivedBaseChangeMapArrowIso_of_isIso α₁ β₁ F₁ F₁' RF₁ RF₁' αF₁ αF₁'
    θ₁ ((ΦA.mapHomologicalComplex c).obj I) hΦI t₁ hΦJ
  obtain ⟨efront⟩ := nonempty_derivedBaseChangeMapArrowIso_of_isIso α β F F' RF RF' αF αF' θ I hI
    t hJ
  let T₂ := (NatTrans.mapHomologicalComplex τ₂ c).app ((F.mapHomologicalComplex c).obj I)
  have : IsIso T₂ := isIso_mapHomologicalComplex_app τ₂ c _
  let SG := (NatTrans.mapHomologicalComplex σG c).app I
  have : IsIso SG := isIso_mapHomologicalComplex_app σG c I
  let SH := (NatTrans.mapHomologicalComplex σH c).app J
  have : IsIso SH := isIso_mapHomologicalComplex_app σH c J
  have hcx : T₂ ≫ (ΦB'.mapHomologicalComplex c).map
      ((NatTrans.mapHomologicalComplex θ c).app I ≫ (F'.mapHomologicalComplex c).map t) =
      (β₁.mapHomologicalComplex c).map SG ≫
        ((NatTrans.mapHomologicalComplex θ₁ c).app ((ΦA.mapHomologicalComplex c).obj I) ≫
          (F₁'.mapHomologicalComplex c).map t₁) ≫ SH := by
    ext n
    have h := hcube (I.X n)
    have hn := σH.naturality (t.f n)
    simp only [Functor.comp_obj, Functor.comp_map] at hn
    simp only [T₂, SG, SH, t₁, T₁, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f, Functor.map_comp, Category.assoc]
    rw [hn]
    exact (reassoc_of% h) (ΦB'.map (F'.map (t.f n)))
  let ecx : Arrow.mk ((ΦB'.mapHomologicalComplex c).map
      ((NatTrans.mapHomologicalComplex θ c).app I ≫ (F'.mapHomologicalComplex c).map t)) ≅
      Arrow.mk ((NatTrans.mapHomologicalComplex θ₁ c).app ((ΦA.mapHomologicalComplex c).obj I) ≫
        (F₁'.mapHomologicalComplex c).map t₁) :=
    Arrow.isoMk ((asIso T₂).symm ≪≫ (β₁.mapHomologicalComplex c).mapIso (asIso SG))
      (asIso SH).symm (by
        dsimp only [Arrow.mk_hom, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom,
          Functor.mapIso_hom]
        rw [IsIso.eq_comp_inv]
        exact (Category.assoc _ _ _).trans ((Category.assoc (inv T₂) _ _).trans
          ((congrArg (inv T₂ ≫ ·) hcx.symm).trans (IsIso.inv_hom_id_assoc _ _))))
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff
    (ΦB'.mapDerivedCategory.mapArrow.mapIso efront ≪≫
      ((Functor.mapArrowFunctor _ _).mapIso ΦB'.mapDerivedCategoryFactorsh).app
        (Arrow.mk ((HomotopyCategory.quotient B' c).map
          ((NatTrans.mapHomologicalComplex θ c).app I ≫ (F'.mapHomologicalComplex c).map t))) ≪≫
      (HomotopyCategory.quotient E' c ⋙ DerivedCategory.Qh).mapArrow.mapIso ecx ≪≫
      eback.symm)).symm

end Cube

end Stacks.Cohomology.UnboundedComplexes
