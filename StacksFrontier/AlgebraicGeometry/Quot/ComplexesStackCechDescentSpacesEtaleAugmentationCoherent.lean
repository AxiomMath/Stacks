module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechDescentSpacesEtaleAugmentation

/-!
# The derived transitions of a pullback along an augmentation, realized: the assembly

This file carries out the last two reductions of
`AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.StrictAugmentationTransitionCoherent`
(Stacks 0D7H (4) made explicit):

* `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.strictAugmentationTriangleUnfolds`: the
  triangle `La_n^* ≅ LX(φ)^* La_m^*` of Stacks 0D6D along `X(φ) ≫ a_m = a_n`, inverted, is the
  composition isomorphism followed by the derived pullback isomorphism of a 2-isomorphism. It is
  proved at the level of natural transformations for arbitrary `f ≫ g = k` (where the equation
  can be substituted) and then read at an object.
* `CategoryTheory.isRealizedHypercoverTriangle_of_chase`: the diagram chase, over arbitrary
  categories, with conclusion `CategoryTheory.IsRealizedHypercoverTriangle` itself.

Nothing here is registered.

## Implementation notes

Equations between components `T.app M` are proved at the level of the natural transformations
`T` and read at `M` through `congrArg (fun T => T.app M)` with `T` taken from the goal: the
kernel compares two components `T.app M`, `T'.app M` with `T`, `T'` only definitionally equal by
unfolding `T` and `T'` completely, which is out of reach for derived pullbacks.

## References

* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞₀ : Type u₃} [Category.{v₃} 𝒞₀] {𝒞₁ : Type u₄} [Category.{v₄} 𝒞₁]

/-- **The chase behind `StrictAugmentationTransitionCoherent`, in the shape of
`CategoryTheory.IsRealizedHypercoverTriangle`.** The transition `n` is `L u ≫ p ≫ v` (the derived
transition), the realizing isomorphisms are `Θ₁ = R₁ v' ≫ q` and `Θ₀ = R₀ u ≫ o` with `v ≫ v' = 𝟙`,
the inverse triangle is `k`, the square is `sq_Y = s`; if `R₁ p ≫ q` and `s ≫ P o ≫ k` are both a
common map `c` followed by `I_L` and `I_R`, and `I_L = I_R`, then `n` realizes the triangle. -/
theorem isRealizedHypercoverTriangle_of_chase {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂}
    [∀ a, Category.{v₂} (D a)] (pull : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a))
    (comp : ∀ {a b c : A} (f : a ⟶ b) (g : b ⟶ c), pull (f ≫ g) ≅ pull g ⋙ pull f)
    {X U₀ U₁ : A} (a₀ : U₀ ⟶ X) (f : U₁ ⟶ U₀) (a₁ : U₁ ⟶ X) (hk : f ≫ a₀ = a₁)
    (L : 𝒞₀ ⥤ 𝒞₁) (R₀ : 𝒞₀ ⥤ D U₀) (R₁ : 𝒞₁ ⥤ D U₁) (sq : L ⋙ R₁ ≅ R₀ ⋙ pull f)
    {N₀ : 𝒞₀} {N₁ : 𝒞₁} (n : L.obj N₀ ⟶ N₁) (K : D X) (Θ₀ : R₀.obj N₀ ≅ (pull a₀).obj K)
    (Θ₁ : R₁.obj N₁ ≅ (pull a₁).obj K) {Y : 𝒞₀} {Y' : 𝒞₁} (u : N₀ ⟶ Y) (v : Y' ⟶ N₁)
    (v' : N₁ ⟶ Y') (hv : v ≫ v' = 𝟙 Y') {Y₁ Y₂ Y₃ : 𝒞₁} (p₁ : L.obj Y ⟶ Y₁) (p₂ : Y₁ ⟶ Y₂)
    (p₃ : Y₂ ⟶ Y₃) (p₄ : Y₃ ⟶ Y') (ht : n = L.map u ≫ p₁ ≫ p₂ ≫ p₃ ≫ p₄ ≫ v)
    {W₁ W₂ : D U₁} (q₁ : R₁.obj Y' ⟶ W₁) (q₂ : W₁ ⟶ W₂) (q₃ : W₂ ⟶ (pull a₁).obj K)
    (hΘ₁ : Θ₁.hom = R₁.map v' ≫ q₁ ≫ q₂ ≫ q₃)
    {O₁ O₂ : D U₀} (o₁ : R₀.obj Y ⟶ O₁) (o₂ : O₁ ⟶ O₂) (o₃ : O₂ ⟶ (pull a₀).obj K)
    (hΘ₀ : Θ₀.hom = R₀.map u ≫ o₁ ≫ o₂ ≫ o₃)
    {V₁ : D U₁} (k₁ : (pull f).obj ((pull a₀).obj K) ⟶ V₁) (k₂ : V₁ ⟶ (pull a₁).obj K)
    (htri : (hypercoverPullTriangle pull comp hk).inv.app K = k₁ ≫ k₂)
    {S₁ S₂ : D U₁} (s₁ : R₁.obj (L.obj Y) ⟶ S₁) (s₂ : S₁ ⟶ S₂) (s₃ : S₂ ⟶ (pull f).obj (R₀.obj Y))
    (hsq : sq.hom.app Y = s₁ ≫ s₂ ≫ s₃)
    {C₁ C₂ C₃ : D U₁} (c₁ : R₁.obj (L.obj Y) ⟶ C₁) (c₂ : C₁ ⟶ C₂) (c₃ : C₂ ⟶ C₃)
    (IL IR : C₃ ⟶ (pull a₁).obj K)
    (hBL : R₁.map (p₁ ≫ p₂ ≫ p₃ ≫ p₄) ≫ q₁ ≫ q₂ ≫ q₃ = c₁ ≫ c₂ ≫ c₃ ≫ IL)
    (hBR : s₁ ≫ s₂ ≫ s₃ ≫ (pull f).map (o₁ ≫ o₂ ≫ o₃) ≫ k₁ ≫ k₂ = c₁ ≫ c₂ ≫ c₃ ≫ IR)
    (hIL : IL = IR) :
    IsRealizedHypercoverTriangle pull comp a₀ f a₁ hk L R₀ R₁ sq n K Θ₀ Θ₁ := by
  unfold IsRealizedHypercoverTriangle
  rw [← cancel_mono Θ₁.hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have nsq := sq.hom.naturality u
  simp only [Functor.comp_map] at nsq
  rw [hΘ₁, hΘ₀, htri, ht, (pull f).map_comp, Category.assoc, ← reassoc_of% nsq, hsq]
  simp only [Functor.map_comp, Category.assoc] at hBL hBR ⊢
  rw [← R₁.map_comp_assoc v v', hv, CategoryTheory.Functor.map_id, Category.id_comp, hBL, hBR, hIL]

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

section Triangle

variable {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ Z) {k : X ⟶ Z} (hk : f ≫ g = k)

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp

/-- The derived pullback along `g_{étale} ∘ f_{étale}` exists, as for every morphism of ringed
topoi. -/
instance hasLeftDerivedFunctor_pullbackOnHomotopy_spacesEtaleRingedToposHom_comp :
    (pullbackOnHomotopy (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS X)
        (Y := spacesEtaleRingedTopos B S hS Y) (Z := spacesEtaleRingedTopos B S hS Z)
        (spacesEtaleRingedToposHom g) (spacesEtaleRingedToposHom f))).HasLeftDerivedFunctor
      (quasiIsoTarget (Y := spacesEtaleRingedTopos B S hS Z)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy
    (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS X)
      (Y := spacesEtaleRingedTopos B S hS Y) (Z := spacesEtaleRingedTopos B S hS Z)
      (spacesEtaleRingedToposHom g) (spacesEtaleRingedToposHom f))

/-- `g ∘ f ≅ k` for `f ≫ g = k`, on the spaces-étale ringed topoi. -/
abbrev spacesEtaleTriangleTwoIso :
    TwoIso (A := spacesEtaleRingedTopos B S hS X) (B := spacesEtaleRingedTopos B S hS Z)
      (RingedToposHom.comp (X := spacesEtaleRingedTopos B S hS X)
        (Y := spacesEtaleRingedTopos B S hS Y) (Z := spacesEtaleRingedTopos B S hS Z)
        (spacesEtaleRingedToposHom g) (spacesEtaleRingedToposHom f))
      (spacesEtaleRingedToposHom (Z₂ := Z) k) :=
  (spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp (Z := Z) f g).symm.trans
      (TwoIso.ofEq.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
        (congrArg (fun g => spacesEtaleRingedToposHom (Z₂ := Z) g) hk))

/-- The triangle of Stacks 0D6D along `f ≫ g = k` on the spaces-étale sites, inverted and read at
an object: the composition isomorphism followed by the derived pullback isomorphism of
`spacesEtaleTriangleTwoIso`. -/
theorem hypercoverPullTriangle_spacesEtale_inv_app_eq (M : spacesEtaleDerivedModules B S hS Z) :
    (hypercoverPullTriangle (fun f => spacesEtaleDerivedPull B S hS f)
        (fun f g => spacesEtaleDerivedPullComp B S hS f g) hk).inv.app M =
      (derivedPullbackCompComparison (X := spacesEtaleRingedTopos B S hS X)
        (Y := spacesEtaleRingedTopos B S hS Y) (Z := spacesEtaleRingedTopos B S hS Z)
        (spacesEtaleRingedToposHom f) (spacesEtaleRingedToposHom g)).app M ≫
      (derivedPullbackIsoOfTwoIso (spacesEtaleTriangleTwoIso f g hk)).hom.app M := by
  subst hk
  rw [derivedPullbackIsoOfTwoIso_trans.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}, Iso.trans_hom,
    NatTrans.comp_app,
    derivedPullbackIsoOfTwoIso_symm_eq.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1},
    derivedPullbackIsoOfTwoIso_ofEq.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1},
    derivedPullbackCongr_hom_app.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}]
  simp only [hypercoverPullTriangle, Iso.trans_inv, NatTrans.comp_app, Iso.symm_inv,
    spacesEtaleDerivedPullbackCompIsoSpacesEtaleRingedToposHomComp, Iso.trans_hom,
    derivedPullbackCompIso_hom, eqToIso.inv, eqToHom_refl, NatTrans.id_app,
    Category.comp_id, spacesEtalePullbackModulesCompIsoSpacesEtaleRingedToposHomComp]

/-- The triangle of Stacks 0D6D along `f ≫ g = k` on the spaces-étale sites, inverted: the
composition isomorphism followed by the derived pullback isomorphism of
`spacesEtaleTriangleTwoIso`, as natural transformations. -/
theorem hypercoverPullTriangle_spacesEtale_inv_eq :
    (hypercoverPullTriangle (fun f => spacesEtaleDerivedPull B S hS f)
        (fun f g => spacesEtaleDerivedPullComp B S hS f g) hk).inv =
      derivedPullbackCompComparison (X := spacesEtaleRingedTopos B S hS X)
        (Y := spacesEtaleRingedTopos B S hS Y) (Z := spacesEtaleRingedTopos B S hS Z)
        (spacesEtaleRingedToposHom f) (spacesEtaleRingedToposHom g) ≫
      (derivedPullbackIsoOfTwoIso (spacesEtaleTriangleTwoIso f g hk)).hom := by
  ext M
  rw [NatTrans.comp_app]
  exact hypercoverPullTriangle_spacesEtale_inv_app_eq f g hk M

end Triangle

variable {X : SimplicialObject (AlgebraicSpaces B S hS)} {Z : AlgebraicSpaces B S hS}
  (a : X ⟶ (Functor.const _).obj Z)

section Unfolds

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp MorphismOfTopoi.comp


/-- **The triangle of Stacks 0D6D along `X(φ) ≫ a_m = a_n` unfolds**: inverted and read at an
object, it is the composition isomorphism followed by the derived pullback isomorphism of
`strictAugmentationTriangleTwoIso`. -/
theorem strictAugmentationTriangleUnfolds : StrictAugmentationTriangleUnfolds a := by
  intro m n φ hk M
  refine Eq.trans (congrArg (fun T => NatTrans.app T M) ?_) (NatTrans.comp_app _ _ M)
  exact hypercoverPullTriangle_spacesEtale_inv_eq (X.map φ.op) (a.app (op m)) hk

variable {a}

/-- **`StrictAugmentationTransitionCoherent` from the 2-morphism identity.** Given
`StrictAugmentationTwoMorphismCoherent`, the derived transitions of `Lb^*M` realize to the
composition isomorphisms `La_n^*M ≅ LX(φ)^* La_m^*M` of Stacks 0D6D: the derived transition is the
inverse derived pullback isomorphism of the appended 2-morphism, and both sides of the chase
normalize to the derived pullback isomorphisms of two 2-isomorphisms, which agree. -/
theorem strictAugmentationTransitionCoherent_of_twoMorphism
    (H : StrictAugmentationTwoMorphismCoherent a) : StrictAugmentationTransitionCoherent X a := by
  intro m n φ hk M
  have h := isIso_componentRingedTwoMorphism_whiskerRight φ H hk
  have hS2 := (strictSituation X).derivedComponentModuleTransition_app_derivedPullback_eq
    (strictStructureSheaf X) (strictAugmentationRingedToposHom a) φ h M
  have hBL := derivedPullbackCompComparison_comp_appendedTransitionTwoIso.{u + 1, u + 1, u + 1,
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    ((strictSituation X).componentAppendedTwoIso (strictStructureSheaf X)
      (strictAugmentationRingedToposHom a) φ h) (strictDegreeAugmentationTwoIso a n) M
  have hBR := derivedPullbackCompComparison_comp_realizedTransitionTwoIso.{u + 1, u + 1, u + 1,
      u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1,
      u + 1, u + 1}
    (strictComponentTransitionTwoIso X φ) (strictDegreeAugmentationTwoIso a m)
    (strictAugmentationTriangleTwoIso a φ hk) M
  have hsq := strictComponentDerivedTransitionIso_hom_app_eq φ
    ((derivedPullback (X := (strictSituation X).componentRingedTopos (strictStructureSheaf X) m)
      (Y := strictRingedTopos X)
      ((strictSituation X).componentRingedToposHom (strictStructureSheaf X) m)).obj
        ((derivedPullback (X := strictRingedTopos X) (Y := spacesEtaleRingedTopos B S hS Z)
          (strictAugmentationRingedToposHom a)).obj M))
  have hIs := congrArg
    (fun s => (derivedPullbackIsoOfTwoIso.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1} s).hom.app M)
    (appendedTransitionTwoIso_eq_strictRealizedTransitionTwoIso φ H hk)
  have hv := ((strictSituation X).derivedPullbackComponentIsoSimplicialSmallEtaleStrictDegree
    (strictStructureSheaf X) n).hom_inv_id_app
      ((derivedPullback (X := strictRingedTopos X) (Y := spacesEtaleRingedTopos B S hS Z)
          (strictAugmentationRingedToposHom a)).obj M)
  have htri := strictAugmentationTriangleUnfolds a φ hk M
  refine isRealizedHypercoverTriangle_of_chase (hv := hv) (ht := hS2)
    (htri := Eq.trans (congrArg (fun T => NatTrans.app T M) (by rfl)) htri) (hsq := hsq)
    (hBL := hBL) (hBR := hBR) (hIL := hIs) (hΘ₁ := ?_) (hΘ₀ := ?_) <;>
    rw [Iso.app_hom]
  exacts [strictAugmentationDegreeDerivedIso_hom_app_eq a n M,
    strictAugmentationDegreeDerivedIso_hom_app_eq a m M]

end Unfolds

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
