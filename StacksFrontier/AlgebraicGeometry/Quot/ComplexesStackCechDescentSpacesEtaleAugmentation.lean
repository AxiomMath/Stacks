module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechDescentSpacesEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleStrictTransitionAppended
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.TwoIsoAugmentedTransitionCoherence

/-!
# The derived transitions of a pullback along an augmentation, realized

This file reduces
`AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.StrictAugmentationTransitionCoherent` (Stacks
0D7H (4) made explicit) to one identity of 2-morphisms of morphisms of topoi,
`AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.StrictAugmentationTwoMorphismCoherent`: the
2-morphism `g_n ⟶ g_m ∘ f_φ` of Stacks 04IC, with the augmentation `b` appended and the
realization `r_n` prepended, is the composite of the 2-isomorphisms of Stacks 0DE7 through `a_n`
and `a_m ∘ X(φ)`.

The derived transition is the inverse derived pullback isomorphism of the appended 2-morphism
(`CategoryTheory.SimplicialSiteSituation.derivedComponentModuleTransition_app_derivedPullback_eq`),
and every other factor is a composition isomorphism of Stacks 0D6D or a derived pullback
isomorphism of a 2-isomorphism; normalizing these composites of 2-isomorphisms brings both sides to
one 2-isomorphism each.

## References

* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- **A realized triangle, over arbitrary categories.** The transition `t` is `L u⁻¹ ≫ p ≫ v` (the
derived transition), the realizing isomorphisms are `Θ_n = R_n v⁻¹ ≫ q` and `Θ_m = R_m u⁻¹ ≫ o`,
the triangle is `tri⁻¹ = k`, the square is `sq_Y = s`; if `R_n p ≫ q` and `s ≫ P o ≫ k` are both a
common map `c` followed by `I_L` and `I_R`, and `I_L = I_R`, then `t` realizes the triangle. -/
theorem map_eq_of_realizedTriangle {𝒞m : Type*} {_ : Category 𝒞m} {𝒞n : Type*}
    {_ : Category 𝒞n} {𝒜m : Type*} {_ : Category 𝒜m} {𝒜n : Type*} {_ : Category 𝒜n}
    (L : 𝒞m ⥤ 𝒞n) (Rn : 𝒞n ⥤ 𝒜n) (Rm : 𝒞m ⥤ 𝒜m) (P : 𝒜m ⥤ 𝒜n) (sq : L ⋙ Rn ≅ Rm ⋙ P)
    {N₀ Y : 𝒞m} {N₁ Y' : 𝒞n} {Z₀ : 𝒜m} {Z₁ : 𝒜n} (u : Y ≅ N₀) (v : Y' ≅ N₁)
    (t : L.obj N₀ ⟶ N₁) {Y₁ Y₂ Y₃ : 𝒞n} (p₁ : L.obj Y ⟶ Y₁) (p₂ : Y₁ ⟶ Y₂) (p₃ : Y₂ ⟶ Y₃)
    (p₄ : Y₃ ⟶ Y') (ht : t = L.map u.inv ≫ p₁ ≫ p₂ ≫ p₃ ≫ p₄ ≫ v.hom)
    (Θn : Rn.obj N₁ ≅ Z₁) {W₁ W₂ : 𝒜n} (q₁ : Rn.obj Y' ⟶ W₁) (q₂ : W₁ ⟶ W₂) (q₃ : W₂ ⟶ Z₁)
    (hΘn : Θn.hom = Rn.map v.inv ≫ q₁ ≫ q₂ ≫ q₃)
    (Θm : Rm.obj N₀ ≅ Z₀) {U₁ U₂ : 𝒜m} (o₁ : Rm.obj Y ⟶ U₁) (o₂ : U₁ ⟶ U₂) (o₃ : U₂ ⟶ Z₀)
    (hΘm : Θm.hom = Rm.map u.inv ≫ o₁ ≫ o₂ ≫ o₃)
    (tri : Z₁ ≅ P.obj Z₀) {V₁ : 𝒜n} (k₁ : P.obj Z₀ ⟶ V₁) (k₂ : V₁ ⟶ Z₁)
    (htri : tri.inv = k₁ ≫ k₂)
    {S₁ S₂ : 𝒜n} (s₁ : Rn.obj (L.obj Y) ⟶ S₁) (s₂ : S₁ ⟶ S₂) (s₃ : S₂ ⟶ P.obj (Rm.obj Y))
    (hsq : sq.hom.app Y = s₁ ≫ s₂ ≫ s₃)
    {C₁ C₂ C₃ : 𝒜n} (c₁ : Rn.obj (L.obj Y) ⟶ C₁) (c₂ : C₁ ⟶ C₂) (c₃ : C₂ ⟶ C₃)
    (IL IR : C₃ ⟶ Z₁)
    (hBL : Rn.map (p₁ ≫ p₂ ≫ p₃ ≫ p₄) ≫ q₁ ≫ q₂ ≫ q₃ = c₁ ≫ c₂ ≫ c₃ ≫ IL)
    (hBR : s₁ ≫ s₂ ≫ s₃ ≫ P.map (o₁ ≫ o₂ ≫ o₃) ≫ k₁ ≫ k₂ = c₁ ≫ c₂ ≫ c₃ ≫ IR)
    (hIL : IL = IR) :
    Rn.map t = sq.hom.app N₀ ≫ P.map Θm.hom ≫ tri.inv ≫ Θn.inv := by
  rw [← cancel_mono Θn.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have nsq := sq.hom.naturality u.inv
  simp only [Functor.comp_map] at nsq
  rw [hΘn, hΘm, htri, ht, P.map_comp, Category.assoc, ← reassoc_of% nsq, hsq]
  simp only [Functor.map_comp, Category.assoc] at hBL hBR ⊢
  rw [← Rn.map_comp_assoc v.hom v.inv, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp, hBL, hBR, hIL]

/-- A natural transformation whose whiskering by an equivalence is invertible is invertible. -/
theorem isIso_of_isIso_whiskerLeft_of_isEquivalence {𝒞 : Type*} [Category* 𝒞] {𝒟 : Type*}
    [Category* 𝒟] {ℰ : Type*} [Category* ℰ] (F : 𝒞 ⥤ 𝒟) [F.IsEquivalence] {G H : 𝒟 ⥤ ℰ}
    (α : G ⟶ H) (h : IsIso (Functor.whiskerLeft F α)) : IsIso α := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Y
  rw [NatTrans.isIso_app_iff_of_iso α (F.objObjPreimageIso Y).symm]
  exact (inferInstance : IsIso ((Functor.whiskerLeft F α).app (F.objPreimage Y)))

end CategoryTheory

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.CategoryTheory.Hypercovering
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom
open Stacks.Cohomology.DerivedBaseChangeOfToposHom
open AlgebraicGeometry.RingedToposHom

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : SimplicialObject (AlgebraicSpaces B S hS)} {Z : AlgebraicSpaces B S hS}
  (a : X ⟶ (Functor.const _).obj Z)

/-- The degree-`k` composite `g_k ∘ r_k`. -/
abbrev strictComponentDegreeHom (k : SimplexCategory) :
    RingedToposHom (spacesEtaleRingedTopos B S hS (X.obj (op k))) (strictRingedTopos X) :=
  RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op k)))
    (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) k)
    (Z := strictRingedTopos X)
    ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) k)
    (strictComponentRingedToposHom X k)

/-- The pullback on homotopy categories along `strictComponentDegreeHom k` has a left derived
functor with respect to quasi-isomorphisms. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_strictComponentDegreeHom (k : SimplexCategory) :
    (pullbackOnHomotopy (strictComponentDegreeHom (X := X) k)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := strictRingedTopos X)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (strictComponentDegreeHom (X := X) k)

/-- The degree-`k` composite `b ∘ (g_k ∘ r_k)`. -/
abbrev strictAugmentationComponentDegreeHom (k : SimplexCategory) :
    RingedToposHom (spacesEtaleRingedTopos B S hS (X.obj (op k)))
      (spacesEtaleRingedTopos B S hS Z) :=
  RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op k)))
    (Y := strictRingedTopos X) (Z := spacesEtaleRingedTopos B S hS Z)
    (strictAugmentationRingedToposHom a) (strictComponentDegreeHom k)

/-- The pullback on homotopy categories along `strictAugmentationComponentDegreeHom a k` has a left
derived functor with respect to quasi-isomorphisms. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_strictAugmentationComponentDegreeHom
    (k : SimplexCategory) :
    (pullbackOnHomotopy (strictAugmentationComponentDegreeHom a k)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := spacesEtaleRingedTopos B S hS Z)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (strictAugmentationComponentDegreeHom a k)

/-- `b ∘ (g_k ∘ r_k) ≅ a_k`: the degree-`k` 2-isomorphism of Stacks 0DE7 for the augmentation
`b = a ∘ e⁻¹` of the strict total site, through `e ∘ d_k ≅ g_k ∘ r_k`, `b ∘ e ≅ a` and
`a ∘ d_k ≅ a_k`. -/
abbrev strictDegreeAugmentationTwoIso (k : SimplexCategory) :
    TwoIso (A := spacesEtaleRingedTopos B S hS (X.obj (op k)))
      (B := spacesEtaleRingedTopos B S hS Z)
      (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op k)))
        (Y := strictRingedTopos X) (Z := spacesEtaleRingedTopos B S hS Z)
        (strictAugmentationRingedToposHom a)
        (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op k)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) k)
          (Z := strictRingedTopos X)
          ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) k)
          (strictComponentRingedToposHom X k)))
      (spacesEtaleRingedToposHom (a.app (op k))) :=
  TwoIso.degreeAugmentationTwoIso.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1,
    u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} (strictDegreeTwoIso X k) (strictAugmentationTwoIso a)
    (augmentationDegreeTwoIso a k)

/-- The degree-`k` comparison `Lb^* ⋙ (-)_k ⋙ Lr_k^* ≅ La_k^*`, read at `M`: the inverse of
`Lg_k^* ≅ (-)_k`, the composition isomorphism along `b ∘ (g_k ∘ r_k)` and the derived pullback
isomorphism of `strictDegreeAugmentationTwoIso`. -/
theorem strictAugmentationDegreeDerivedIso_hom_app_eq (k : SimplexCategory)
    (M : spacesEtaleDerivedModules B S hS Z) :
    (strictAugmentationDegreeDerivedIso a k).hom.app M =
      (strictComponentDerivedRealize X k).map
          (((strictSituation X).derivedPullbackComponentIsoSimplicialSmallEtaleStrictDegree
            (strictStructureSheaf X) k).inv.app
            ((derivedPullback (X := strictRingedTopos X) (Y := spacesEtaleRingedTopos B S hS Z)
              (strictAugmentationRingedToposHom a)).obj M)) ≫
        (derivedPullbackCompComparison (X := spacesEtaleRingedTopos B S hS (X.obj (op k)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) k)
          (Z := strictRingedTopos X) (strictComponentRingedToposHom X k)
          ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) k)).app
            ((derivedPullback (X := strictRingedTopos X) (Y := spacesEtaleRingedTopos B S hS Z)
              (strictAugmentationRingedToposHom a)).obj M) ≫
        (derivedPullbackCompComparison (X := spacesEtaleRingedTopos B S hS (X.obj (op k)))
          (Y := strictRingedTopos X) (Z := spacesEtaleRingedTopos B S hS Z)
          (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op k)))
            (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) k)
            (Z := strictRingedTopos X)
            ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) k)
            (strictComponentRingedToposHom X k))
          (strictAugmentationRingedToposHom a)).app M ≫
        (derivedPullbackIsoOfTwoIso (strictDegreeAugmentationTwoIso a k)).hom.app M := by
  simp only [strictAugmentationDegreeDerivedIso, strictDegreeDerivedIso, Iso.trans_hom,
    Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_inv_app, Category.id_comp, Category.assoc,
    Functor.map_comp, derivedPullbackCompIso_hom]
  exact congrArg (_ ≫ ·) (derivedPullbackCompComparison_comp_degreeAugmentationTwoIso.{u + 1,
    u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1,
    u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (strictDegreeTwoIso X k) (strictAugmentationTwoIso a) (augmentationDegreeTwoIso a k) M)

section Transition

variable {m n : SimplexCategory} (φ : m ⟶ n)

/-- `g_m ∘ f_φ`. -/
abbrev strictComponentTransitionHom :
    RingedToposHom ((strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
      (strictRingedTopos X) :=
  RingedToposHom.comp (X := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
    (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
    (Z := strictRingedTopos X)
    ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) m)
    ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)

/-- The pullback on homotopy categories along `strictComponentTransitionHom φ` has a left derived
functor with respect to quasi-isomorphisms. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_strictComponentTransitionHom :
    (pullbackOnHomotopy (strictComponentTransitionHom (X := X) φ)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := strictRingedTopos X)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (strictComponentTransitionHom (X := X) φ)

/-- `b ∘ (g_m ∘ f_φ)`. -/
abbrev strictAugmentationComponentTransitionHom :
    RingedToposHom ((strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
      (spacesEtaleRingedTopos B S hS Z) :=
  RingedToposHom.comp (X := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
    (Y := strictRingedTopos X) (Z := spacesEtaleRingedTopos B S hS Z)
    (strictAugmentationRingedToposHom a) (strictComponentTransitionHom φ)

/-- The pullback on homotopy categories along `strictAugmentationComponentTransitionHom a φ` has a
left derived functor with respect to quasi-isomorphisms. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_strictAugmentationComponentTransitionHom :
    (pullbackOnHomotopy (strictAugmentationComponentTransitionHom a φ)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := spacesEtaleRingedTopos B S hS Z)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (strictAugmentationComponentTransitionHom a φ)

/-- `b ∘ g_n`. -/
abbrev strictAugmentationComponentHom (k : SimplexCategory) :
    RingedToposHom ((strictSituation X).componentRingedTopos (strictStructureSheaf X) k)
      (spacesEtaleRingedTopos B S hS Z) :=
  RingedToposHom.comp (X := (strictSituation X).componentRingedTopos (strictStructureSheaf X) k)
    (Y := strictRingedTopos X) (Z := spacesEtaleRingedTopos B S hS Z)
    (strictAugmentationRingedToposHom a)
    ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) k)

/-- The pullback on homotopy categories along `strictAugmentationComponentHom a k` has a left
derived functor with respect to quasi-isomorphisms. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_strictAugmentationComponentHom
    (k : SimplexCategory) :
    (pullbackOnHomotopy (strictAugmentationComponentHom a k)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := spacesEtaleRingedTopos B S hS Z)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (strictAugmentationComponentHom a k)

/-- `(b ∘ (g_m ∘ f_φ)) ∘ r_n`. -/
abbrev strictAugmentationComponentTransitionRealizeHom :
    RingedToposHom (spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (spacesEtaleRingedTopos B S hS Z) :=
  RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
    (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
    (Z := spacesEtaleRingedTopos B S hS Z)
    (strictAugmentationComponentTransitionHom a φ) (strictComponentRingedToposHom X n)

/-- The pullback on homotopy categories along `strictAugmentationComponentTransitionRealizeHom a φ`
has a left derived functor with respect to quasi-isomorphisms. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_strictAugmentationComponentTransitionRealizeHom :
    (pullbackOnHomotopy (strictAugmentationComponentTransitionRealizeHom a φ)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := spacesEtaleRingedTopos B S hS Z)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (strictAugmentationComponentTransitionRealizeHom a φ)

/-- `f_φ ∘ r_n`. -/
abbrev strictTransitionRealizeHom :
    RingedToposHom (spacesEtaleRingedTopos B S hS (X.obj (op n)))
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) m) :=
  RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
    (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
    (Z := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
    ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)
    (strictComponentRingedToposHom X n)

/-- The pullback on homotopy categories along `strictTransitionRealizeHom φ` has a left derived
functor with respect to quasi-isomorphisms. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_strictTransitionRealizeHom :
    (pullbackOnHomotopy (strictTransitionRealizeHom (X := X) φ)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (strictTransitionRealizeHom (X := X) φ)

/-- `r_m ∘ X(φ)`. -/
abbrev strictRealizeTransitionHom :
    RingedToposHom (spacesEtaleRingedTopos B S hS (X.obj (op n)))
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) m) :=
  RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
    (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
    (Z := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
    (strictComponentRingedToposHom X m) (spacesEtaleRingedToposHom (X.map φ.op))

/-- The pullback on homotopy categories along `strictRealizeTransitionHom φ` has a left derived
functor with respect to quasi-isomorphisms. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_strictRealizeTransitionHom :
    (pullbackOnHomotopy (strictRealizeTransitionHom (X := X) φ)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (strictRealizeTransitionHom (X := X) φ)

/-- `a_m ∘ X(φ)`. -/
abbrev augmentationTransitionHom :
    RingedToposHom (spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (spacesEtaleRingedTopos B S hS Z) :=
  RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
    (Y := spacesEtaleRingedTopos B S hS (X.obj (op m))) (Z := spacesEtaleRingedTopos B S hS Z)
    (spacesEtaleRingedToposHom (a.app (op m))) (spacesEtaleRingedToposHom (X.map φ.op))

/-- The pullback on homotopy categories along `augmentationTransitionHom a φ` has a left derived
functor with respect to quasi-isomorphisms. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_augmentationTransitionHom :
    (pullbackOnHomotopy (augmentationTransitionHom a φ)).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := spacesEtaleRingedTopos B S hS Z)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy (augmentationTransitionHom a φ)

/-- The square of the derived transition, read at an object: the composition isomorphisms and the
derived pullback isomorphism of `strictComponentTransitionTwoIso`. -/
theorem strictComponentDerivedTransitionIso_hom_app_eq
    (Y : DerivedCategory
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) m).Modules) :
    (strictComponentDerivedTransitionIso X φ).hom.app Y =
      (derivedPullbackCompComparison (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
        (Z := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
        (strictComponentRingedToposHom X n)
        ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)).app Y ≫
      (derivedPullbackIsoOfTwoIso (strictComponentTransitionTwoIso X φ)).hom.app Y ≫
      (derivedPullbackCompIso (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS (X.obj (op m)))
        (Z := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
        (spacesEtaleRingedToposHom (X.map φ.op))
        (strictComponentRingedToposHom X m)).inv.app Y := by
  open SimplicialSiteSituation in
  simp only [strictComponentDerivedTransitionIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    derivedTransitionPullbackIsoDerivedPullbackSimplicialSmallEtaleStrictBridge,
    derivedPullbackCompIso_hom]
  refine Eq.trans ?_ (Category.id_comp _)
  exact congrArg₂ (· ≫ ·) ((derivedPullback (strictComponentRingedToposHom X n)).map_id _) rfl

end Transition

section Coherent

variable {m n : SimplexCategory} (φ : m ⟶ n)

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- `a_m ∘ X(φ) ≅ a_n`: the composition 2-isomorphism of the spaces-étale ringed topoi, then the
equality `X(φ) ≫ a_m = a_n`. -/
abbrev strictAugmentationTriangleTwoIso (hk : X.map φ.op ≫ a.app (op m) = a.app (op n)) :
    TwoIso (A := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (B := spacesEtaleRingedTopos B S hS Z) (augmentationTransitionHom a φ)
      (spacesEtaleRingedToposHom (Z₂ := Z) (a.app (op n))) :=
  (spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp (Z := Z) (X.map φ.op)
    (a.app (op m))).symm.trans
      (TwoIso.ofEq.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
        (congrArg (fun g => spacesEtaleRingedToposHom (Z₂ := Z) g) hk))

/-- **The triangle of Stacks 0D6D along `X(φ) ≫ a_m = a_n`, inverted and read at an object**:
the composition isomorphism followed by the derived pullback isomorphism of
`strictAugmentationTriangleTwoIso`. -/
def StrictAugmentationTriangleUnfolds : Prop :=
  ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n) (hk : X.map φ.op ≫ a.app (op m) = a.app (op n))
    (M : spacesEtaleDerivedModules B S hS Z),
    (hypercoverPullTriangle (fun f => spacesEtaleDerivedPull B S hS f)
        (fun f g => spacesEtaleDerivedPullComp B S hS f g) hk).inv.app M =
      (derivedPullbackCompComparison (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
        (Y := spacesEtaleRingedTopos B S hS (X.obj (op m))) (Z := spacesEtaleRingedTopos B S hS Z)
        (spacesEtaleRingedToposHom (X.map φ.op)) (spacesEtaleRingedToposHom (a.app (op m)))).app M ≫
      (derivedPullbackIsoOfTwoIso (strictAugmentationTriangleTwoIso a φ hk)).hom.app M

/-- `(b ∘ (g_m ∘ f_φ)) ∘ r_n ≅ a_n` through `a_m ∘ X(φ)`: `strictComponentTransitionTwoIso`, the
degree-`m` 2-isomorphism and `strictAugmentationTriangleTwoIso`. -/
abbrev strictRealizedTransitionTwoIso (hk : X.map φ.op ≫ a.app (op m) = a.app (op n)) :
    TwoIso (A := spacesEtaleRingedTopos B S hS (X.obj (op n)))
      (B := spacesEtaleRingedTopos B S hS Z) (strictAugmentationComponentTransitionRealizeHom a φ)
      (spacesEtaleRingedToposHom (Z₂ := Z) (a.app (op n))) :=
  TwoIso.realizedTransitionTwoIso.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1,
    u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (strictComponentTransitionTwoIso X φ)
    (strictDegreeAugmentationTwoIso a m) (strictAugmentationTriangleTwoIso a φ hk)

/-- **The 2-morphism identity behind Stacks 0D7H (4), realized.** The 2-morphism
`t_φ : g_n ⟶ g_m ∘ f_φ` of Stacks 04IC, with the augmentation `b = a ∘ e⁻¹` appended and the
realization `r_n` prepended, is the composite of the 2-isomorphisms of Stacks 0DE7 through `a_n`
and `a_m ∘ X(φ)`: on direct images of sheaves of sets,
`r_n^* (b_* t_φ) = (b ∘ g_n) ∘ r_n ≅ b ∘ (g_n ∘ r_n) ≅ a_n ≅ (b ∘ (g_m ∘ f_φ)) ∘ r_n`. -/
def StrictAugmentationTwoMorphismCoherent : Prop :=
  ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n) (hk : X.map φ.op ≫ a.app (op m) = a.app (op n)),
    Functor.whiskerLeft (strictComponentRingedToposHom X n).toToposHom.pushforward
        (((strictSituation X).componentRingedTwoMorphism (strictStructureSheaf X) φ).whiskerRight
          (strictAugmentationRingedToposHom a)).t =
      ((TwoIso.associator (strictComponentRingedToposHom X n)
          ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)
          (strictAugmentationRingedToposHom a)).symm.trans
        ((strictDegreeAugmentationTwoIso a n).trans
          (strictRealizedTransitionTwoIso a φ hk).symm)).e.hom

variable {a}

/-- Under `StrictAugmentationTwoMorphismCoherent`, the 2-morphism `t_φ` becomes invertible after
the augmentation is appended: `r_n` is an equivalence. -/
theorem isIso_componentRingedTwoMorphism_whiskerRight
    (H : StrictAugmentationTwoMorphismCoherent a)
    (hk : X.map φ.op ≫ a.app (op m) = a.app (op n)) :
    IsIso (((strictSituation X).componentRingedTwoMorphism (strictStructureSheaf X) φ).whiskerRight
      (strictAugmentationRingedToposHom a)).t := by
  refine CategoryTheory.isIso_of_isIso_whiskerLeft_of_isEquivalence
    (strictComponentRingedToposHom X n).toToposHom.pushforward _ ?_
  rw [H φ hk]
  infer_instance

/-- Under `StrictAugmentationTwoMorphismCoherent`, the two 2-isomorphisms
`(b ∘ (g_m ∘ f_φ)) ∘ r_n ≅ a_n` agree. -/
theorem appendedTransitionTwoIso_eq_strictRealizedTransitionTwoIso
    (H : StrictAugmentationTwoMorphismCoherent a)
    (hk : X.map φ.op ≫ a.app (op m) = a.app (op n)) :
    TwoIso.appendedTransitionTwoIso.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1,
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
        ((strictSituation X).componentAppendedTwoIso (strictStructureSheaf X)
          (strictAugmentationRingedToposHom a) φ
          (isIso_componentRingedTwoMorphism_whiskerRight φ H hk))
        (strictDegreeAugmentationTwoIso a n) =
      strictRealizedTransitionTwoIso a φ hk := by
  set Ω := (strictSituation X).componentAppendedTwoIso (strictStructureSheaf X)
    (strictAugmentationRingedToposHom a) φ (isIso_componentRingedTwoMorphism_whiskerRight φ H hk)
  set Θ := (TwoIso.associator (strictComponentRingedToposHom X n)
      ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) n)
      (strictAugmentationRingedToposHom a)).symm.trans
    ((strictDegreeAugmentationTwoIso a n).trans (strictRealizedTransitionTwoIso a φ hk).symm)
  have hΩ' : Ω.whiskerLeft (strictComponentRingedToposHom X n) = Θ :=
    TwoIso.ext.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} (Iso.ext (H φ hk))
  have hΩ : Ω.symm.whiskerLeft (strictComponentRingedToposHom X n) = Θ.symm := by
    rw [← hΩ']
    exact TwoIso.ext.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} rfl
  unfold TwoIso.appendedTransitionTwoIso
  rw [hΩ]
  exact TwoIso.symm_trans_symm_trans_eq.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} _ _ _

end Coherent

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
