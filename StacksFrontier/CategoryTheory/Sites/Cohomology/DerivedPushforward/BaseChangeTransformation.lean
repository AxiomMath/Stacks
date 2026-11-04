module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquare
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOverASquareOfSites

/-!
# The derived base change map of a transformation of underived functors

Let `A`, `A'`, `B`, `B'` be abelian categories, `α : A ⥤ A'` and `β : B ⥤ B'` exact functors,
`F : A ⥤ B` and `F' : A' ⥤ B'` additive functors with right derived functors `RF`, `RF'` on the
unbounded derived categories, and `θ : F ⋙ β ⟶ α ⋙ F'` a natural transformation — for instance a
base change map `g⁻¹ f_* ⟶ f'_* (g')⁻¹` of sheaves, `α` and `β` being exact inverse images. This
file constructs the canonical map

`Dθ : RF ⋙ Dβ ⟶ Dα ⋙ RF'`

of derived functors that `θ` induces, and computes it at a K-injective complex `I`: up to
isomorphism of arrows it is the image in the derived category of the map of complexes
`θ_I ≫ F'(t)`, where `t : α(I) ⟶ J` is any K-injective resolution. Consequently `Dθ` is
invertible at `I` exactly when `θ_I ≫ F'(t)` is a quasi-isomorphism, and two such derived maps
related by a cube of comparisons are invertible at corresponding objects together.

## Main definitions

* `Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMapUnit` — the comparison
  `K(F) ⋙ Q ⋙ Dβ ⟶ Q ⋙ Dα ⋙ RF'` built from `θ` and the derived-functor unit of `RF'`.
* `Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap` — its descent `RF ⋙ Dβ ⟶ Dα ⋙ RF'`
  along the universal property of `RF ⋙ Dβ`.

## Main results

* `Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap_fac_app` — the defining equation.
* `Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMapArrowIso` — at a K-injective complex
  the derived map is the image of `θ_I ≫ F'(t)`.
* `Stacks.Cohomology.UnboundedComplexes.isIso_derivedBaseChangeMap_app_iff_quasiIso` — hence it is
  invertible there exactly when `θ_I ≫ F'(t)` is a quasi-isomorphism.
* `Stacks.Cohomology.UnboundedComplexes.isIso_derivedBaseChangeMap_app_iff_of_cube` — two derived
  base change maps connected by comparison functors and an objectwise cube identity are
  invertible together, at corresponding K-injective complexes, after applying the comparison
  functor at the corner of the targets.
* `Stacks.Homology.DerivedSquare.derivedSquare_eq_derivedBaseChangeMap` — the derived
  transformation `Stacks.Homology.DerivedSquare.derivedSquare` of a square is the derived base
  change map of its total right derived functors.

## Implementation notes

The construction is `Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeUnit` with the
isomorphism `α ⋙ F' ≅ F ⋙ β` there replaced by an arbitrary transformation `F ⋙ β ⟶ α ⋙ F'`;
the base change maps of interest are not invertible in general, and their invertibility at
particular objects is the content of base change theorems. The source category `A` is
Grothendieck abelian, so that `RF ⋙ Dβ` is a right derived functor of `K(F) ⋙ Q ⋙ Dβ`
(`Stacks.Cohomology.UnboundedComplexes.isRightDerivedFunctor_comp`) and the descent exists.

## References

* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 0A2A](https://stacks.math.columbia.edu/tag/0A2A)
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

/-- The comparison `K(F) ⋙ Q ⋙ Dβ ⟶ Q ⋙ (Dα ⋙ RF')` induced by `θ : F ⋙ β ⟶ α ⋙ F'`: the
identification of `Q ⋙ Dβ` with `K(β) ⋙ Q`, then `θ` applied degreewise, then the derived-functor
unit of `RF'` whiskered with `K(α)`, then the identification of `K(α) ⋙ Q` with `Q ⋙ Dα`. -/
public def derivedBaseChangeMapUnit :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙
        β.mapDerivedCategory ⟶
      DerivedCategory.Qh ⋙ (α.mapDerivedCategory ⋙ RF') :=
  Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ))
      β.mapDerivedCategoryFactorsh.hom ≫
    Functor.whiskerRight
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ β)) (ComplexShape.up ℤ)).hom ≫
        NatTrans.mapHomotopyCategory θ (ComplexShape.up ℤ) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (α ⋙ F')) (ComplexShape.up ℤ)).inv)
      DerivedCategory.Qh ≫
    Functor.whiskerLeft (α.mapHomotopyCategory (ComplexShape.up ℤ)) αF' ≫
    Functor.whiskerRight α.mapDerivedCategoryFactorsh.inv RF'

/-- The comparison `derivedBaseChangeMapUnit` at an object, written out. -/
public theorem derivedBaseChangeMapUnit_app (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    (derivedBaseChangeMapUnit α β F F' RF' αF' θ).app K =
      β.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          (((Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ β)) (ComplexShape.up ℤ)).hom ≫
            NatTrans.mapHomotopyCategory θ (ComplexShape.up ℤ) ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (α ⋙ F'))
              (ComplexShape.up ℤ)).inv).app K) ≫
        αF'.app ((α.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        RF'.map (α.mapDerivedCategoryFactorsh.inv.app K) :=
  rfl

variable [IsGrothendieckAbelian.{wA} A]
  [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- **The derived base change map `RF ⋙ Dβ ⟶ Dα ⋙ RF'` of `θ : F ⋙ β ⟶ α ⋙ F'`**: the descent
of `Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMapUnit` along the universal property
of `RF ⋙ Dβ` as a right derived functor of `K(F) ⋙ Q ⋙ Dβ`. -/
public def derivedBaseChangeMap :
    RF ⋙ β.mapDerivedCategory ⟶ α.mapDerivedCategory ⋙ RF' :=
  haveI := isRightDerivedFunctor_comp (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh) DerivedCategory.Qh RF αF β.mapDerivedCategory
  (RF ⋙ β.mapDerivedCategory).rightDerivedDesc
    (Functor.whiskerRight αF β.mapDerivedCategory ≫ (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (α.mapDerivedCategory ⋙ RF')
    (derivedBaseChangeMapUnit α β F F' RF' αF' θ)

/-- **The defining equation of the derived base change map**: precomposed with `Dβ` applied to
the derived-functor unit of `RF`, it is
`Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMapUnit`. -/
public theorem derivedBaseChangeMap_fac_app (K : HomotopyCategory A (ComplexShape.up ℤ)) :
    β.mapDerivedCategory.map (αF.app K) ≫
        (derivedBaseChangeMap α β F F' RF RF' αF αF' θ).app (DerivedCategory.Qh.obj K) =
      (derivedBaseChangeMapUnit α β F F' RF' αF' θ).app K := by
  have := isRightDerivedFunctor_comp (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh) DerivedCategory.Qh RF αF β.mapDerivedCategory
  have h := Functor.rightDerived_fac_app (RF ⋙ β.mapDerivedCategory)
    (Functor.whiskerRight αF β.mapDerivedCategory ≫ (Functor.associator _ _ _).hom)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (α.mapDerivedCategory ⋙ RF')
    (derivedBaseChangeMapUnit α β F F' RF' αF' θ) K
  dsimp only [derivedBaseChangeMap]
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Category.comp_id] using h

/-- At the image of a complex, the identification of `K(F) ⋙ K(β)` with `K(F ⋙ β)` used by
`Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMapUnit` is the identity. -/
private theorem mapHomotopyCategoryCompIso_refl_hom_app {C₁ C₂ C₃ : Type*} [Category* C₁]
    [Category* C₂] [Category* C₃] [Preadditive C₁] [Preadditive C₂] [Preadditive C₃]
    (G₁ : C₁ ⥤ C₂) (G₂ : C₂ ⥤ C₃) [G₁.Additive] [G₂.Additive] (K : CochainComplex C₁ ℤ) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (G₁ ⋙ G₂)) (ComplexShape.up ℤ)).hom.app
      ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) = 𝟙 _ :=
  rfl

/-- The inverse form of `mapHomotopyCategoryCompIso_refl_hom_app`. -/
private theorem mapHomotopyCategoryCompIso_refl_inv_app {C₁ C₂ C₃ : Type*} [Category* C₁]
    [Category* C₂] [Category* C₃] [Preadditive C₁] [Preadditive C₂] [Preadditive C₃]
    (G₁ : C₁ ⥤ C₂) (G₂ : C₂ ⥤ C₃) [G₁.Additive] [G₂.Additive] (K : CochainComplex C₁ ℤ) :
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (G₁ ⋙ G₂)) (ComplexShape.up ℤ)).inv.app
      ((HomotopyCategory.quotient C₁ (ComplexShape.up ℤ)).obj K) = 𝟙 _ :=
  rfl

omit [IsGrothendieckAbelian.{wA, vA, uA} A] in
/-- **The comparison `derivedBaseChangeMapUnit` at a complex**: the identification of `Dβ ∘ Q`
with `Q ∘ K(β)`, the image of `θ` at the complex, the unit of `RF'` and the identification of
`Q ∘ K(α)` with `Dα ∘ Q`. -/
public theorem derivedBaseChangeMapUnit_app_quotient (I : CochainComplex A ℤ) :
    (derivedBaseChangeMapUnit α β F F' RF' αF' θ).app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) =
      β.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).app I)) ≫
        αF'.app ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj
          ((α.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
        RF'.map (α.mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)) := by
  dsimp only [derivedBaseChangeMapUnit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  rw [mapHomotopyCategoryCompIso_refl_hom_app, mapHomotopyCategoryCompIso_refl_inv_app]
  congr 2
  exact congrArg DerivedCategory.Qh.map
    ((Category.id_comp ((NatTrans.mapHomotopyCategory θ (ComplexShape.up ℤ)).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) ≫ 𝟙 _)).trans
      (Category.comp_id _))

/-- The bookkeeping of the computation of `derivedBaseChangeMapArrowIso`, done for morphisms of
an abstract category so that no object needs to be matched up to definitional unfolding. -/
private lemma reassociate_aux {𝒞 : Type*} [Category* 𝒞] {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : 𝒞}
    (a : X₀ ⟶ X₁) (b : X₁ ⟶ X₂) (m : X₂ ⟶ X₇) (x : X₂ ⟶ X₃) (y : X₃ ⟶ X₇) (u : X₃ ⟶ X₄)
    (v : X₄ ⟶ X₅) (w : X₅ ⟶ X₄) (z : X₄ ⟶ X₆) (c : X₇ ⟶ X₆) {k : X₆ ⟶ X₇}
    (hm : m = x ≫ y) (hvw : v ≫ w = 𝟙 X₄) (hnat : y ≫ c = u ≫ z) (hck : c ≫ k = 𝟙 X₇) :
    (a ≫ b) ≫ m = (a ≫ b ≫ x ≫ u ≫ v) ≫ w ≫ z ≫ k := by
  simp only [Category.assoc, reassoc_of% hvw, ← reassoc_of% hnat, hck, Category.comp_id, hm]

/-- A morphism of complexes is a quasi-isomorphism exactly when its image in the derived category,
through the homotopy category, is an isomorphism. -/
private lemma isIso_Qh_map_quotient_map_iff {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜]
    [HasDerivedCategory 𝒜] {K L : CochainComplex 𝒜 ℤ} (m : K ⟶ L) :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map m)) ↔
      QuasiIso m := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
  have e : Arrow.mk (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map m)) ≅
      Arrow.mk (DerivedCategory.Q.map m) :=
    Arrow.isoMk ((DerivedCategory.quotientCompQhIso 𝒜).app K)
      ((DerivedCategory.quotientCompQhIso 𝒜).app L)
      ((DerivedCategory.quotientCompQhIso 𝒜).hom.naturality m).symm
  exact (MorphismProperty.isomorphisms _).arrow_mk_iso_iff e

variable [IsGrothendieckAbelian.{wA'} A']
  [RF'.IsRightDerivedFunctor αF' (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]

/-- **The derived base change map at a K-injective complex.** For a K-injective complex `I` on
`A` and a quasi-isomorphism `t : α(I) ⟶ J` to a K-injective complex, the derived base change map
at `I` is isomorphic, as an arrow of `D(B')`, to the image of the map of complexes
`θ_I ≫ F'(t) : β(F(I)) ⟶ F'(J)`. -/
public theorem nonempty_derivedBaseChangeMapArrowIso (I : CochainComplex A ℤ) (hI : I.IsKInjective)
    {J : CochainComplex A' ℤ} (t : (α.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J)
    [QuasiIso t] (hJ : J.IsKInjective) :
    Nonempty (Arrow.mk ((derivedBaseChangeMap α β F F' RF RF' αF αF' θ).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) ≅
      Arrow.mk (DerivedCategory.Qh.map ((HomotopyCategory.quotient B' (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).app I ≫
          (F'.mapHomologicalComplex (ComplexShape.up ℤ)).map t)))) := by
  let qI := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I
  have h₁ : IsIso (αF.app qI) := isIso_app_of_isKInjective _ _ RF αF I hI
  have h₂ : IsIso (αF'.app ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj J)) :=
    isIso_app_of_isKInjective _ _ RF' αF' J hJ
  have h₃ : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map t)) :=
    (isIso_Qh_map_quotient_map_iff t).2 inferInstance
  have hfac := derivedBaseChangeMap_fac_app α β F F' RF RF' αF αF' θ qI
  have hnat := αF'.naturality ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map t)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hnat
  have hφ : (derivedBaseChangeMap α β F F' RF RF' αF αF' θ).app (DerivedCategory.Qh.obj qI) =
      inv (β.mapDerivedCategory.map (αF.app qI)) ≫
        (derivedBaseChangeMapUnit α β F F' RF' αF' θ).app qI := by
    rw [← hfac, IsIso.inv_hom_id_assoc]
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

/-- **Invertibility of the derived base change map at a K-injective complex.** For a K-injective
complex `I` on `A` and a quasi-isomorphism `t : α(I) ⟶ J` to a K-injective complex, the derived
base change map is invertible at `I` exactly when `θ_I ≫ F'(t) : β(F(I)) ⟶ F'(J)` is a
quasi-isomorphism. -/
public theorem isIso_derivedBaseChangeMap_app_iff_quasiIso (I : CochainComplex A ℤ)
    (hI : I.IsKInjective) {J : CochainComplex A' ℤ}
    (t : (α.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J) [QuasiIso t]
    (hJ : J.IsKInjective) :
    IsIso ((derivedBaseChangeMap α β F F' RF RF' αF αF' θ).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I))) ↔
      QuasiIso ((NatTrans.mapHomologicalComplex θ (ComplexShape.up ℤ)).app I ≫
        (F'.mapHomologicalComplex (ComplexShape.up ℤ)).map t) := by
  obtain ⟨e⟩ := nonempty_derivedBaseChangeMapArrowIso α β F F' RF RF' αF αF' θ I hI t hJ
  rw [← isIso_Qh_map_quotient_map_iff]
  exact (MorphismProperty.isomorphisms _).arrow_mk_iso_iff e

end Map

/-- The component of the image under `NatTrans.mapHomologicalComplex` of an isomorphism is an
isomorphism. -/
private theorem isIso_mapHomologicalComplex_app {W₁ W₂ : Type*} [Category* W₁] [Category* W₂]
    [Preadditive W₁] [Preadditive W₂] {G₁ G₂ : W₁ ⥤ W₂} [G₁.Additive] [G₂.Additive]
    (τ : G₁ ⟶ G₂) [IsIso τ] (c : ComplexShape ℤ) (K : HomologicalComplex W₁ c) :
    IsIso ((NatTrans.mapHomologicalComplex τ c).app K) :=
  inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex (asIso τ) c).hom.app K))

section Cube

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
  [IsGrothendieckAbelian.{wA} A] [IsGrothendieckAbelian.{wA'} A']
  [RF.IsRightDerivedFunctor αF (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [RF'.IsRightDerivedFunctor αF' (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
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
  [IsGrothendieckAbelian.{wC} C] [IsGrothendieckAbelian.{wC'} C']
  [RF₁.IsRightDerivedFunctor αF₁ (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
  [RF₁'.IsRightDerivedFunctor αF₁' (HomotopyCategory.quasiIso C' (ComplexShape.up ℤ))]
  (ΦA : A ⥤ C) [ΦA.Additive] (ΦA' : A' ⥤ C') [ΦA'.Additive] [PreservesFiniteLimits ΦA']
  [PreservesFiniteColimits ΦA'] (ΦB : B ⥤ E) [ΦB.Additive] (ΦB' : B' ⥤ E') [ΦB'.Additive]
  [PreservesFiniteLimits ΦB'] [PreservesFiniteColimits ΦB']
  (τ₁ : ΦA ⋙ α₁ ⟶ α ⋙ ΦA') [IsIso τ₁] (τ₂ : ΦB ⋙ β₁ ⟶ β ⋙ ΦB') [IsIso τ₂]
  (σG : F ⋙ ΦB ⟶ ΦA ⋙ F₁) [IsIso σG] (σH : ΦA' ⋙ F₁' ⟶ F' ⋙ ΦB') [IsIso σH]

/-- **The derived base change maps of a cube are invertible together.** Let two derived base
change situations `θ : F ⋙ β ⟶ α ⋙ F'` (the front) and `θ₁ : F₁ ⋙ β₁ ⟶ α₁ ⋙ F₁'` (the back) be
connected by additive comparison functors `ΦA`, `ΦA'`, `ΦB`, `ΦB'` at the four corners, the last
two at the targets exact, and invertible comparisons `τ₁`, `τ₂` of the inverse images and `σG`,
`σH` of the direct images, satisfying the cube identity `hcube` objectwise — the shape of
`Stacks.CategoryTheory.mateEquiv_symm_hComp_eq_app`. Let `I` be a K-injective complex on `A`
with `ΦA(I)` K-injective, and suppose `ΦA'` preserves K-injectivity. Then the back derived base
change map is invertible at `ΦA(I)` exactly when the image under `ΦB'` of the front one at `I`
is. -/
public theorem isIso_derivedBaseChangeMap_app_iff_of_cube
    (hcube : ∀ X : A, τ₂.app (F.obj X) ≫ ΦB'.map (θ.app X) =
      β₁.map (σG.app X) ≫ θ₁.app (ΦA.obj X) ≫ F₁'.map (τ₁.app X) ≫ σH.app (α.obj X))
    (hKinj : ∀ J : CochainComplex A' ℤ, J.IsKInjective →
      CochainComplex.IsKInjective ((ΦA'.mapHomologicalComplex (ComplexShape.up ℤ)).obj J))
    (I : CochainComplex A ℤ) (hI : I.IsKInjective)
    (hΦI : CochainComplex.IsKInjective ((ΦA.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    IsIso ((derivedBaseChangeMap α₁ β₁ F₁ F₁' RF₁ RF₁' αF₁ αF₁' θ₁).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          ((ΦA.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)))) ↔
      IsIso (ΦB'.mapDerivedCategory.map ((derivedBaseChangeMap α β F F' RF RF' αF αF' θ).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)))) := by
  let c := ComplexShape.up ℤ
  obtain ⟨J, t, hJ, ht⟩ := Stacks.Injectives.exists_kInjective_resolution_of_grothendieck
    ((α.mapHomologicalComplex c).obj I)
  let T₁ := (NatTrans.mapHomologicalComplex τ₁ c).app I
  have : IsIso T₁ := isIso_mapHomologicalComplex_app τ₁ c I
  let t₁ : (α₁.mapHomologicalComplex c).obj ((ΦA.mapHomologicalComplex c).obj I) ⟶
      (ΦA'.mapHomologicalComplex c).obj J := T₁ ≫ (ΦA'.mapHomologicalComplex c).map t
  have : ΦA'.PreservesHomology := Functor.preservesHomologyOfExact ΦA'
  have : QuasiIso t₁ := quasiIso_comp T₁ ((ΦA'.mapHomologicalComplex c).map t)
  obtain ⟨eback⟩ := nonempty_derivedBaseChangeMapArrowIso α₁ β₁ F₁ F₁' RF₁ RF₁' αF₁ αF₁' θ₁
    ((ΦA.mapHomologicalComplex c).obj I) hΦI t₁ (hKinj J hJ)
  obtain ⟨efront⟩ := nonempty_derivedBaseChangeMapArrowIso α β F F' RF RF' αF αF' θ I hI t hJ
  -- The comparisons of the cube, applied degreewise.
  let T₂ := (NatTrans.mapHomologicalComplex τ₂ c).app ((F.mapHomologicalComplex c).obj I)
  have : IsIso T₂ := isIso_mapHomologicalComplex_app τ₂ c _
  let SG := (NatTrans.mapHomologicalComplex σG c).app I
  have : IsIso SG := isIso_mapHomologicalComplex_app σG c I
  let SH := (NatTrans.mapHomologicalComplex σH c).app J
  have : IsIso SH := isIso_mapHomologicalComplex_app σH c J
  -- The cube identity on complexes.
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
  -- The comparison of `Dφ ∘ Q` with `Q ∘ K(φ)` for the exact functor `ΦB'`.
  let efh : Arrow.mk (ΦB'.mapDerivedCategory.map (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient B' c).map
        ((NatTrans.mapHomologicalComplex θ c).app I ≫ (F'.mapHomologicalComplex c).map t)))) ≅
      Arrow.mk (DerivedCategory.Qh.map ((HomotopyCategory.quotient E' c).map
        ((ΦB'.mapHomologicalComplex c).map
          ((NatTrans.mapHomologicalComplex θ c).app I ≫ (F'.mapHomologicalComplex c).map t)))) :=
    Arrow.isoMk (ΦB'.mapDerivedCategoryFactorsh.app ((HomotopyCategory.quotient B' c).obj
        (((F ⋙ β).mapHomologicalComplex c).obj I)))
      (ΦB'.mapDerivedCategoryFactorsh.app ((HomotopyCategory.quotient B' c).obj
        ((F'.mapHomologicalComplex c).obj J)))
      (ΦB'.mapDerivedCategoryFactorsh.hom.naturality ((HomotopyCategory.quotient B' c).map
        ((NatTrans.mapHomologicalComplex θ c).app I ≫ (F'.mapHomologicalComplex c).map t))).symm
  have e := ΦB'.mapDerivedCategory.mapArrow.mapIso efront ≪≫ efh ≪≫
    (HomotopyCategory.quotient E' c ⋙ DerivedCategory.Qh).mapArrow.mapIso ecx ≪≫ eback.symm
  exact ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).symm

end Cube

end Stacks.Cohomology.UnboundedComplexes

namespace Stacks.Homology.DerivedSquare

open Stacks.Cohomology.SiteCohomologyPresheaf (totalRightDerivedCompUnit
  isRightDerivedFunctor_totalRightDerived_comp totalRightDerivedCompUnit_app)

universe wA wA' wB wB' vA vA' vB vB' uA uA' uB uB' wG

variable {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{wG} A]
  [HasDerivedCategory.{wA} A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [HasDerivedCategory.{wA'} A']
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [HasDerivedCategory.{wB'} B']
  {F : A ⥤ B} [F.Additive] {F' : A' ⥤ B'} [F'.Additive]
  [(F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [(F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
  {E : A ⥤ A'} [E.Additive] [PreservesFiniteLimits E] [PreservesFiniteColimits E]
  {E' : B ⥤ B'} [E'.Additive] [PreservesFiniteLimits E'] [PreservesFiniteColimits E']

/-- **The derived transformation of a square is its derived base change map.** For
`c : F ⋙ E' ⟶ E ⋙ F'` with `E`, `E'` exact, `Stacks.Homology.DerivedSquare.derivedSquare c` is
`Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap` of `c` for the total right derived
functors of `F` and `F'`: both are descents along the universal property of
`RF ⋙ E'.mapDerivedCategory`, of the same transformation. -/
public theorem derivedSquare_eq_derivedBaseChangeMap (c : F ⋙ E' ⟶ E ⋙ F') :
    derivedSquare c = Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap E E' F F'
      (totalRightDerived F) (totalRightDerived F') (totalRightDerivedUnit F)
      (totalRightDerivedUnit F') c := by
  have := isRightDerivedFunctor_totalRightDerived_comp
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) E'.mapDerivedCategory
  refine Functor.rightDerived_ext _ (totalRightDerivedCompUnit
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) E'.mapDerivedCategory)
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _ _ _ ?_
  ext K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, totalRightDerivedCompUnit_app]
  rw [derivedSquare_fac_app, Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap_fac_app]
  simp [derivedSquareBeta, Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMapUnit]

end Stacks.Homology.DerivedSquare

end
