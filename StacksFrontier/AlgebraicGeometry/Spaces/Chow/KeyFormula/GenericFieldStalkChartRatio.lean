module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.KeyFormula.GenericRestrictionGeometricReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackChartFMapComp

/-!
# The ratio of the restricted generator to `s_ξ` through a chart of `Spec 𝒪_{U, u}`

Let `X` be a decent algebraic space, `Z ⊂ X` a prime divisor, `ℒ` an invertible `𝒪_X`-module
free on a family `e` over an étale chart `V` of `X`, and let `Q` be an étale chart of
`Spec 𝒪_{U, u}` over the base change of `V`, over which the inverse image of `e` is `v · s_ξ` for
a unit `v` of `𝒪(Q)`. On the base change `P = Spec κ(u) ×_{Spec 𝒪_{U, u}} Q`, an étale chart of
`Spec κ(u)` over `W' = V ×_X Z`, the ratio `w` of the inverse image of `e|_Z` to the image of
`s_ξ` (`AlgebraicGeometry.Space.PrimeDivisor.genericFieldChartRatio`) is the pullback of `v`.
This file compares inverse images of chart sections along two factorizations of one morphism of
algebraic spaces, and computes the inverse image of `e` to `Q`.

## Main results

* `AlgebraicGeometry.Space.modulePullbackChartFMap_eqToHom_of_eq`: chart sections along equal
  morphisms agree under the transport of the inverse images.
* `AlgebraicGeometry.Space.modulePullbackCompIso_trans_eqToIso_hom_apply`: the comparison of two
  factorizations `f₂ ≫ g₂ = f₁ ≫ g₁` on iterated chart sections.
* `AlgebraicGeometry.Space.PrimeDivisor.modulePullbackChartFMap_genericStalk_eq_restrict`: the
  inverse image of `e` to a chart `Q` of `Spec 𝒪_{U, u}` over the base change of `V`.

## Implementation notes

The kernel tries to reduce `eqToHom h` (by K-like reduction on `h`) whenever it compares two
terms containing it that are not syntactically equal, and checking that the two inverse images
`(f₂ ≫ g₂)^*M` and `(f₁ ≫ g₁)^*M` are definitionally equal is hopeless.  The statements are
therefore phrased so that every comparison around an `eqToHom` is syntactic: chart diagrams are
given by their components and the charts appear as the same terms on both sides.

## References

* [Stacks Project, Section 0EQU](https://stacks.math.columbia.edu/tag/0EQU)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Chart sections along equal morphisms agree under any transport of the inverse images, at a
chart diagram given by its components. -/
theorem modulePullbackChartFMap_eqToHom_of_eq {X Y : AlgebraicSpaces B S hS} {f₁ f₂ : X ⟶ Y}
    (hf : f₁ = f₂) (M : Modules.{u, u} B S hS Y.1 Y.2)
    (h : (modulePullback B S hS f₁).obj M = (modulePullback B S hS f₂).obj M)
    {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1}
    (a : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V)
    (ha₁ : U.1.hom ≫ f₁.hom = yoneda.map a ≫ V.1.hom)
    (ha₂ : U.1.hom ≫ f₂.hom = yoneda.map a ≫ V.1.hom) (s : M.val.obj (op V)) :
    ((eqToHom h).val.app (op U)).hom ((modulePullbackChartFMap B S hS f₁ M).app ⟨U, V, a, ha₁⟩ s) =
      (modulePullbackChartFMap B S hS f₂ M).app ⟨U, V, a, ha₂⟩ s := by
  subst hf
  rfl

section IsoApply

variable {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    {M N P : Modules.{u, u} B S hS F hF} (U : SmallEtale B S hS F)

/-- An isomorphism of modules followed by its inverse, on a section. -/
theorem modules_inv_hom_apply (α : M ≅ N) (x : M.val.obj (op U)) :
    (α.inv.val.app (op U)).hom ((α.hom.val.app (op U)).hom x) = x :=
  ConcreteCategory.congr_hom (congrArg (fun χ ↦ χ.val.app (op U)) α.hom_inv_id) x

/-- The composite `α ≫ eqToHom h ≫ γ⁻¹` of isomorphisms of modules sends `x` to `y` when `α x`
and `γ y` agree under the transport. -/
theorem modules_trans_eqToIso_trans_symm_hom_apply {M₁ M₂ M₃ M₄ : Modules.{u, u} B S hS F hF}
    (α : M₁ ≅ M₂) (h : M₂ = M₃) (γ : M₄ ≅ M₃) (x : M₁.val.obj (op U)) (y : M₄.val.obj (op U))
    (hxy : ((eqToHom h).val.app (op U)).hom ((α.hom.val.app (op U)).hom x) =
      (γ.hom.val.app (op U)).hom y) :
    ((α ≪≫ eqToIso h ≪≫ γ.symm).hom.val.app (op U)).hom x = y := by
  subst h
  change (γ.inv.val.app (op U)).hom ((α.hom.val.app (op U)).hom x) = y
  rw [show (α.hom.val.app (op U)).hom x = (γ.hom.val.app (op U)).hom y from hxy]
  exact modules_inv_hom_apply B S hS U γ y

end IsoApply

/-- Chart sections at two chart diagrams with equal vertical morphisms agree. -/
theorem modulePullbackChartFMap_congr_g {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) {U : SmallEtale B S hS X.1} {V : SmallEtale B S hS Y.1}
    {a a' : (SmallEtale.toOver B S hS X.1).obj U ⟶ (SmallEtale.toOver B S hS Y.1).obj V}
    (h : a = a') (ha : U.1.hom ≫ f.hom = yoneda.map a ≫ V.1.hom)
    (ha' : U.1.hom ≫ f.hom = yoneda.map a' ≫ V.1.hom) (s : M.val.obj (op V)) :
    (modulePullbackChartFMap B S hS f M).app ⟨U, V, a, ha⟩ s =
      (modulePullbackChartFMap B S hS f M).app ⟨U, V, a', ha'⟩ s := by
  subst h
  rfl

/-- For two factorizations `f₂ ≫ g₂ = f₁ ≫ g₁` of a morphism of algebraic spaces and two
compatible pairs of chart diagrams, the identification
`f₂^*(g₂^*M) ≅ (f₂ ≫ g₂)^*M = (f₁ ≫ g₁)^*M ≅ f₁^*(g₁^*M)` carries the iterated chart section of `s`
along `f₂, g₂` to the one along `f₁, g₁`. -/
theorem modulePullbackCompIso_trans_eqToIso_hom_apply {X' Y₁ Y₂ T : AlgebraicSpaces B S hS}
    (f₁ : X' ⟶ Y₁) (g₁ : Y₁ ⟶ T) (f₂ : X' ⟶ Y₂) (g₂ : Y₂ ⟶ T)
    (M : Modules.{u, u} B S hS T.1 T.2)
    (h : (modulePullback B S hS (f₂ ≫ g₂)).obj M = (modulePullback B S hS (f₁ ≫ g₁)).obj M)
    (hfg : f₂ ≫ g₂ = f₁ ≫ g₁)
    {U : SmallEtale B S hS X'.1} {V₁ : SmallEtale B S hS Y₁.1} {V₂ : SmallEtale B S hS Y₂.1}
    {W : SmallEtale B S hS T.1}
    (a₁ : (SmallEtale.toOver B S hS X'.1).obj U ⟶ (SmallEtale.toOver B S hS Y₁.1).obj V₁)
    (b₁ : (SmallEtale.toOver B S hS Y₁.1).obj V₁ ⟶ (SmallEtale.toOver B S hS T.1).obj W)
    (a₂ : (SmallEtale.toOver B S hS X'.1).obj U ⟶ (SmallEtale.toOver B S hS Y₂.1).obj V₂)
    (b₂ : (SmallEtale.toOver B S hS Y₂.1).obj V₂ ⟶ (SmallEtale.toOver B S hS T.1).obj W)
    (ha₁ : U.1.hom ≫ f₁.hom = yoneda.map a₁ ≫ V₁.1.hom)
    (hb₁ : V₁.1.hom ≫ g₁.hom = yoneda.map b₁ ≫ W.1.hom)
    (ha₂ : U.1.hom ≫ f₂.hom = yoneda.map a₂ ≫ V₂.1.hom)
    (hb₂ : V₂.1.hom ≫ g₂.hom = yoneda.map b₂ ≫ W.1.hom)
    (hab : a₂ ≫ b₂ = a₁ ≫ b₁) (s : M.val.obj (op W)) :
    ((((modulePullbackCompIso B S hS f₂ g₂).app M ≪≫ eqToIso h ≪≫
        ((modulePullbackCompIso B S hS f₁ g₁).app M).symm).hom.val.app (op U)).hom
      ((modulePullbackChartFMap B S hS f₂ ((modulePullback B S hS g₂).obj M)).app
        ⟨U, V₂, a₂, ha₂⟩ ((modulePullbackChartFMap B S hS g₂ M).app ⟨V₂, W, b₂, hb₂⟩ s))) =
      (modulePullbackChartFMap B S hS f₁ ((modulePullback B S hS g₁).obj M)).app
        ⟨U, V₁, a₁, ha₁⟩ ((modulePullbackChartFMap B S hS g₁ M).app ⟨V₁, W, b₁, hb₁⟩ s) := by
  refine modules_trans_eqToIso_trans_symm_hom_apply B S hS U _ h _ _ _ ?_
  have hc₂ : U.1.hom ≫ (f₂ ≫ g₂).hom = yoneda.map (a₂ ≫ b₂) ≫ W.1.hom :=
    (ChartDiagram.comp B S hS f₂ g₂ a₂ b₂ ha₂ hb₂).comm
  have hc₂' : U.1.hom ≫ (f₁ ≫ g₁).hom = yoneda.map (a₂ ≫ b₂) ≫ W.1.hom := by rwa [← hfg]
  have hc₁ : U.1.hom ≫ (f₁ ≫ g₁).hom = yoneda.map (a₁ ≫ b₁) ≫ W.1.hom :=
    (ChartDiagram.comp B S hS f₁ g₁ a₁ b₁ ha₁ hb₁).comm
  have e₁ : (((modulePullbackCompIso B S hS f₁ g₁).app M).hom.val.app (op U)).hom
      ((modulePullbackChartFMap B S hS f₁ ((modulePullback B S hS g₁).obj M)).app
        ⟨U, V₁, a₁, ha₁⟩ ((modulePullbackChartFMap B S hS g₁ M).app ⟨V₁, W, b₁, hb₁⟩ s)) =
      (modulePullbackChartFMap B S hS (f₁ ≫ g₁) M).app ⟨U, W, a₁ ≫ b₁, hc₁⟩ s :=
    modulePullbackCompIso_hom_app_modulePullbackChartFMap B S hS f₁ g₁ M a₁ b₁ ha₁ hb₁ s
  have e₂ : (((modulePullbackCompIso B S hS f₂ g₂).app M).hom.val.app (op U)).hom
      ((modulePullbackChartFMap B S hS f₂ ((modulePullback B S hS g₂).obj M)).app
        ⟨U, V₂, a₂, ha₂⟩ ((modulePullbackChartFMap B S hS g₂ M).app ⟨V₂, W, b₂, hb₂⟩ s)) =
      (modulePullbackChartFMap B S hS (f₂ ≫ g₂) M).app ⟨U, W, a₂ ≫ b₂, hc₂⟩ s :=
    modulePullbackCompIso_hom_app_modulePullbackChartFMap B S hS f₂ g₂ M a₂ b₂ ha₂ hb₂ s
  have e₃ := modulePullbackChartFMap_eqToHom_of_eq B S hS hfg M h (a₂ ≫ b₂) hc₂ hc₂' s
  have e₄ := modulePullbackChartFMap_congr_g B S hS (f₁ ≫ g₁) M hab hc₂' hc₁ s
  exact (congrArg ((eqToHom h).val.app (op U)).hom e₂).trans ((e₃.trans e₄).trans e₁.symm)

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)
    (L : Modules.{u, u} B S hS X hX) (hL : IsInvertibleModule (B := B) ⟨X, hX⟩ L)
    (V : SmallEtale B S hS X)
    (e : (W' : SmallEtale B S hS X) → (W' ⟶ V) → L.val.obj (op W'))
    (hcompat : ∀ (W₁ W₂ : SmallEtale B S hS X) (k : W₁ ⟶ V) (g : W₂ ⟶ W₁),
      (L.val.map g.op).hom (e W₁ k) = e W₂ (g ≫ k))
    (Q : SmallEtale B S hS (Z.genericStalkSpace B S hS hX hdec).1)
    (ι : Q ⟶ Z.genericStalkBaseChangeChart B S hS hX hdec V)

include hcompat in
/-- The inverse image of `e` to `Q` through `Spec 𝒪_{U, u}`, at the chart diagram `(Q, V)`, is
the restriction to `Q` of its inverse image to the base change of `V`. -/
theorem PrimeDivisor.modulePullbackChartFMap_genericStalk_eq_restrict
    (hQ : Q.1.hom ≫ (Z.genericStalkMorphism B S hS hX hdec).hom =
      yoneda.map ((SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
        (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g) ≫ V.1.hom) :
    (modulePullbackChartFMap B S hS (Z.genericStalkMorphism B S hS hX hdec) L).app
        ⟨Q, V, (SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
          (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g, hQ⟩ (e V (𝟙 V)) =
      modulePullbackChartSectionRestrict B S hS (Z.genericStalkMorphism B S hS hX hdec) L
        (Z.genericStalkBaseChangeDiagram B S hS hX hdec V) (e V (𝟙 V)) (𝟙 Q ≫ ι) := by
  have h2 : (L.val.map (𝟙 V).op).hom (e V (𝟙 V)) = e V (𝟙 V) :=
    (hcompat V V (𝟙 V) (𝟙 V)).trans (congrArg (e V) (Category.id_comp _))
  have hsq : (SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map (𝟙 Q ≫ ι) ≫
      (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g =
      ((SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
        (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g) ≫
        (SmallEtale.toOver B S hS X).map (𝟙 V) :=
    (congrArg (fun k ↦ (SmallEtale.toOver B S hS _).map k ≫
      (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g) (Category.id_comp ι)).trans
      ((congrArg (_ ≫ ·) (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)).symm
  have h1 : (modulePullbackChartFMap B S hS (Z.genericStalkMorphism B S hS hX hdec) L).app
        ⟨Q, V, (SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
          (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g, hQ⟩
        ((L.val.map (𝟙 V).op).hom (e V (𝟙 V))) =
      (((modulePullback B S hS (Z.genericStalkMorphism B S hS hX hdec)).obj L).val.map
        (𝟙 Q ≫ ι).op).hom
        ((modulePullbackChartFMap B S hS (Z.genericStalkMorphism B S hS hX hdec) L).app
          (Z.genericStalkBaseChangeDiagram B S hS hX hdec V) (e V (𝟙 V))) :=
    (modulePullbackChartFMap B S hS (Z.genericStalkMorphism B S hS hX hdec) L).naturality
      (Z.genericStalkBaseChangeDiagram B S hS hX hdec V)
      ⟨Q, V, (SmallEtale.toOver B S hS (Z.genericStalkSpace B S hS hX hdec).1).map ι ≫
          (Z.genericStalkBaseChangeDiagram B S hS hX hdec V).g, hQ⟩ (𝟙 Q ≫ ι) (𝟙 V) hsq
      (e V (𝟙 V))
  rwa [h2] at h1

end AlgebraicGeometry.Space

end
