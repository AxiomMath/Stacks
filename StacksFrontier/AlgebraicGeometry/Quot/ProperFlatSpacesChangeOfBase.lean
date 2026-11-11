module

public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatFamilyCartesian
public import StacksFrontier.AlgebraicGeometry.Quot.ProperFlatSpacesNotEffective
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductAlgebraicStackLocallySmall
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackSmallModel
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBase
public import StacksFrontier.CategoryTheory.FiberedCategory.EquivalenceOfFullyFaithful
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverIso

/-!
# Change of base for the stack of proper flat algebraic spaces

Let `g : S ⟶ S'` be a morphism of a big fppf site. The stack `p'_{fp, flat, proper}` of Stacks 0D1D
over the big fppf site of `S` (`AlgebraicGeometry.cartesianProperFlatBasedCategory B S hS`) is the
base change along `S ⟶ S'` of the stack `p'_{fp, flat, proper}` over the big fppf site of `S'`:
read over `S'` by Construction A of Stacks 04X5, it is equivalent over `(Sch/S')_{fppf}` to the
2-fibre product `(Sch/S) ×_{(Sch/S')} Spaces'_{fp, flat, proper}`. The equivalence sends a family
`X ⟶ T` over a scheme `T ⟶ S` to `T ⟶ S ⟶ S'` with its factorization through `S` and the
lower-shriek extension `Λ X ⟶ Λ h_T = h_{(T ⟶ S ⟶ S')}` of the family (Stacks 03I5 (2)); it is
fully faithful and essentially surjective by Stacks 04SG (algebraic spaces over `S` are algebraic
spaces over `S'` with a morphism to `S`), finite presentation, flatness and properness not
depending on the base, and `Λ` preserving and reflecting fibre products.

Consequently algebraicity of `p'_{fp, flat, proper}` over `S'` gives algebraicity over `S`
(Stacks 04TF for the 2-fibre product, Stacks 04X5 to return to the site of `S`), and a
non-effective formal object over `S` shows that `p'_{fp, flat, proper}` over `S'` is not
algebraic (Stacks 07X8). This is the step "after base change to `Spec(ℂ)`" in the proof of
Stacks 0D1R.

## Main definitions

* `AlgebraicGeometry.CartesianProperFlatSpaces.relocalize`: a family over `S`, read over `S'`.
* `AlgebraicGeometry.ProperFlatChangeOfBase.BaseChange`: the 2-fibre product
  `(Sch/S) ×_{(Sch/S')} Spaces'_{fp, flat, proper}` over the big fppf site of `S'`.
* `AlgebraicGeometry.ProperFlatChangeOfBase.comparison` and
  `AlgebraicGeometry.ProperFlatChangeOfBase.equivalence`: the comparison functor from Construction
  A of `Spaces'_{fp, flat, proper}` over `S`, and the equivalence over the site of `S'` it is.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_of_isAlgebraicStack_changeBase_of_largeHoms`:
  Construction A reflects algebraicity for categories with large hom-sets.
* `AlgebraicGeometry.isAlgebraicStack_cartesianProperFlatBasedCategory_of_changeBase`:
  `p'_{fp, flat, proper}` algebraic over `S'` implies algebraic over `S`.
* `AlgebraicGeometry.not_isAlgebraicStack_cartesianProperFlatBasedCategory_of_changeBase`:
  a non-effective formal object over `S` makes `p'_{fp, flat, proper}` over `S'` non-algebraic.

## References

* [Stacks Project, Tag 0D1D](https://stacks.math.columbia.edu/tag/0D1D)
* [Stacks Project, Tag 0D1R](https://stacks.math.columbia.edu/tag/0D1R)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 07X8](https://stacks.math.columbia.edu/tag/07X8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

/-- Discrete limits of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasLimitsOfShape_discrete_presheaf_properFlatChangeOfBase
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  functorCategoryHasLimitsOfShape

namespace CartesianProperFlatSpaces

variable {B : BigFppfSite.{u}} {S S' : Scheme.{u}} {hS : B.Contains S} {hS' : B.Contains S'}
  (g : B.obj hS ⟶ B.obj hS')

/-- The factorization through `S` of a scheme over `S`, read over `S'`. -/
def point (T : BigFppfOver B S hS) : (Over.map g).obj T ⟶ Over.mk g :=
  Over.homMk T.hom

/-- Read over `S'`, a morphism of schemes over `S` commutes with the factorizations through
`S`. -/
@[reassoc]
theorem map_comp_point {T T' : BigFppfOver B S hS} (c : T ⟶ T') :
    (Over.map g).map c ≫ point g T' = point g T :=
  Over.OverMorphism.ext (Over.w c)

/-- The lower-shriek extension of the representable presheaf of `T`, read through
`Λ h_T ≅ h_{(T ⟶ S ⟶ S')}`, has as structural morphism the factorization of `T` through `S`. -/
theorem relocalizeYonedaIso_hom_app_comp_yoneda_map_point (T : BigFppfOver B S hS) :
    (OverShriek.relocalizeYonedaIso g).hom.app T ≫ yoneda.map (point g T) =
      OverShriek.viewStructureMap g (yoneda.obj T) := by
  ext W x
  rcases x with ⟨⟨ψ, s⟩, hψ⟩
  exact Over.OverMorphism.ext (Over.w s)

/-! ### Properties of the structure morphism across the lower-shriek extension -/

section Properties

variable {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : BigFppfOver B S hS}

/-- Finite presentation of `Λ t`, read with target `h_{(T ⟶ S ⟶ S')}`, is finite presentation
of `t`. -/
theorem isFinitePresentation_relocalize_comp_iff (t : X ⟶ yoneda.obj T) :
    Space.IsFinitePresentation B S' hS'
        ((OverShriek.relocalizePresheafFunctor g).map t ≫
          (OverShriek.relocalizeYonedaIso g).hom.app T) ↔
      Space.IsFinitePresentation B S hS t := by
  let ι := (OverShriek.relocalizeYonedaIso g).hom.app T
  let Λt := (OverShriek.relocalizePresheafFunctor g).map t
  refine Iff.trans ⟨fun h => Space.isFinitePresentation_of_arrowIso B S' hS' (Λt ≫ ι) Λt (𝟙 _)
      (inv ι) (by simp) h,
    fun h => Space.isFinitePresentation_of_arrowIso B S' hS' Λt (Λt ≫ ι) (𝟙 _) ι (by simp) h⟩ ?_
  exact and_congr (Space.holdsOnEveryEtaleChart_relocalizeMap_iff B S S' hS hS' g _ t)
    (and_congr (Space.isQuasiCompact_relocalize_iff B S hS S' hS' g t)
      (Space.isQuasiSeparated_relocalize_iff B S hS S' hS' g t))

/-- Flatness of `Λ t`, read with target `h_{(T ⟶ S ⟶ S')}`, is flatness of `t`. -/
theorem isFlat_relocalize_comp_iff (t : X ⟶ yoneda.obj T) :
    Space.IsFlat B S' hS'
        ((OverShriek.relocalizePresheafFunctor g).map t ≫
          (OverShriek.relocalizeYonedaIso g).hom.app T) ↔
      Space.IsFlat B S hS t :=
  (Space.holdsOnEveryEtaleChart_comp_iso_iff B S' hS' _ _ _).trans
    (Space.holdsOnEveryEtaleChart_relocalizeMap_iff B S S' hS hS' g _ t)

/-- Properness of `Λ t`, read with target `h_{(T ⟶ S ⟶ S')}`, is properness of `t`. -/
theorem isProper_relocalize_comp_iff (hX : IsAlgebraicSpace B S hS X) (t : X ⟶ yoneda.obj T) :
    Space.IsProper B S' hS'
        ((OverShriek.relocalizePresheafFunctor g).map t ≫
          (OverShriek.relocalizeYonedaIso g).hom.app T) ↔
      Space.IsProper B S hS t :=
  (Space.isProper_comp_isIso_iff B S' hS' _ _).trans
    (Space.isProper_relocalize_iff B S hS S' hS' g hX (isAlgebraicSpace_yoneda B S hS T) t)

end Properties

/-! ### The functor `Spaces'_{fp, flat, proper}` over `S` to the one over `S'` -/

variable {g} in
/-- The structure morphism of the lower-shriek extension of a family, with target the
representable presheaf of its base read over `S'`. -/
abbrev relocalizeToBase (x : CartesianProperFlatSpaces B S hS) :
    (OverShriek.relocalizePresheafFunctor g).obj x.total ⟶ yoneda.obj ((Over.map g).obj x.base) :=
  (OverShriek.relocalizePresheafFunctor g).map x.toBase ≫
    (OverShriek.relocalizeYonedaIso g).hom.app x.base

/-- A family over a scheme `T` of the big fppf site of `S`, read over `S'`: the lower-shriek
extension of its total space over `T ⟶ S ⟶ S'`. -/
def relocalizeObj (x : CartesianProperFlatSpaces B S hS) : CartesianProperFlatSpaces B S' hS' :=
  mk' ((Over.map g).obj x.base) ((OverShriek.relocalizePresheafFunctor g).obj x.total)
    (isAlgebraicSpace_viewOver B S S' hS hS' g _ x.isAlgebraicSpace_total)
    (relocalizeToBase (g := g) x)
    ((isFinitePresentation_relocalize_comp_iff g x.toBase).2 x.isFinitePresentation_toBase)
    ((isFlat_relocalize_comp_iff g x.toBase).2 x.isFlat_toBase)
    ((isProper_relocalize_comp_iff g x.isAlgebraicSpace_total x.toBase).2 x.isProper_toBase)

/-- The cartesian square of a morphism of families, extended along `Λ`. -/
theorem isPullback_relocalize {x y : CartesianProperFlatSpaces B S hS} (φ : x ⟶ y) :
    IsPullback ((OverShriek.relocalizePresheafFunctor g).map φ.hom.hom.left.hom)
      (relocalizeToBase (g := g) x) (relocalizeToBase (g := g) y)
      (yoneda.map ((Over.map g).map φ.hom.hom.right)) :=
  ((isPullback_hom φ).map (OverShriek.relocalizePresheafFunctor g)).of_iso (Iso.refl _)
    (Iso.refl _) ((OverShriek.relocalizeYonedaIso g).app x.base)
    ((OverShriek.relocalizeYonedaIso g).app y.base) (by simp) (by simp) (by simp)
    ((OverShriek.relocalizeYonedaIso g).hom.naturality φ.hom.hom.right)

/-- **A family over `S`, read over `S'`.** The functor `Spaces'_{fp, flat, proper}` over `S` to
`Spaces'_{fp, flat, proper}` over `S'` given by the lower-shriek extension along `g : S ⟶ S'`
(Stacks 04SG). -/
def relocalize : CartesianProperFlatSpaces B S hS ⥤ CartesianProperFlatSpaces B S' hS' where
  obj := relocalizeObj g
  map {x y} φ := homOfIsPullback (x := relocalizeObj g x) (y := relocalizeObj g y)
    ((OverShriek.relocalizePresheafFunctor g).map φ.hom.hom.left.hom)
    ((Over.map g).map φ.hom.hom.right) (isPullback_relocalize g φ)
  map_id x := hom_ext' (by simp; rfl) (by simp; rfl)
  map_comp φ ψ := hom_ext' (by simp; rfl) (by simp; rfl)

/-- The structure morphism of the lower-shriek extension of a family, followed by the
factorization of its base through `S`, is the structural morphism `Λ X ⟶ h_{(S ⟶ S')}`. -/
@[reassoc]
theorem relocalizeToBase_comp_point (x : CartesianProperFlatSpaces B S hS) :
    relocalizeToBase (g := g) x ≫ yoneda.map (point g x.base) =
      OverShriek.viewStructureMap g x.total := by
  rw [Category.assoc, relocalizeYonedaIso_hom_app_comp_yoneda_map_point]
  ext W s
  rfl

/-- A family over `S` whose lower-shriek extension is identified with a family over `S'`, on
total spaces and on bases compatibly with the structure morphisms, is isomorphic to it after
`relocalize g`. -/
def relocalizeIsoOfIso (z : CartesianProperFlatSpaces B S hS)
    (Y : CartesianProperFlatSpaces B S' hS')
    (eX : (OverShriek.relocalizePresheafFunctor g).obj z.total ≅ Y.total)
    (θ : (Over.map g).obj z.base ≅ Y.base)
    (h : relocalizeToBase (g := g) z = eX.hom ≫ Y.toBase ≫ yoneda.map θ.inv) :
    (relocalize g).obj z ≅ Y :=
  have sq₁ : IsPullback eX.hom (relocalizeToBase (g := g) z) Y.toBase (yoneda.map θ.hom) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [h]
      simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.comp_id]⟩
  have sq₂ : IsPullback eX.inv Y.toBase (relocalizeToBase (g := g) z) (yoneda.map θ.inv) :=
    IsPullback.of_horiz_isIso ⟨by rw [h, Iso.inv_hom_id_assoc]⟩
  { hom := homOfIsPullback (x := relocalizeObj g z) eX.hom θ.hom sq₁
    inv := homOfIsPullback (y := relocalizeObj g z) eX.inv θ.inv sq₂
    hom_inv_id := hom_ext' eX.hom_inv_id θ.hom_inv_id
    inv_hom_id := hom_ext' eX.inv_hom_id θ.inv_hom_id }

/-- The map of bases of `relocalizeIsoOfIso` is `θ`. -/
@[simp]
theorem relocalizeIsoOfIso_hom_right (z : CartesianProperFlatSpaces B S hS)
    (Y : CartesianProperFlatSpaces B S' hS')
    (eX : (OverShriek.relocalizePresheafFunctor g).obj z.total ≅ Y.total)
    (θ : (Over.map g).obj z.base ≅ Y.base)
    (h : relocalizeToBase (g := g) z = eX.hom ≫ Y.toBase ≫ yoneda.map θ.inv) :
    (relocalizeIsoOfIso g z Y eX θ h).hom.hom.hom.right = θ.hom :=
  rfl

/-- `relocalize g` lies strictly over `Over.map g`. -/
theorem relocalize_comp_projection :
    relocalize g ⋙ cartesianProperFlatProjection B S' hS' =
      cartesianProperFlatProjection B S hS ⋙ Over.map g :=
  rfl

end CartesianProperFlatSpaces

/-! ### The comparison with the base change of `Spaces'_{fp, flat, proper}` over `S'` -/

/-- A morphism of a category lying over an identity for the identity functor is an `eqToHom`. -/
theorem eq_eqToHom_of_isHomLift_id {C : Type*} [Category C] {X Y U : C} (f : X ⟶ Y)
    (hX : X = U) (hY : Y = U) [h : (𝟭 C).IsHomLift (𝟙 U) f] :
    f = eqToHom (hX.trans hY.symm) := by
  subst hY
  subst hX
  exact (@IsHomLift.eq_of_isHomLift _ _ _ _ (𝟭 C) X X (𝟙 X) f h).symm.trans
    (eqToHom_refl _ _).symm

/-- A composite of `eqToHom`s from an object to itself is the identity. -/
theorem id_eq_eqToHom_comp_comp {C : Type*} [Category C] {U A A' A'' : C} (a : U = A)
    (b : A = A') (c : A' = A'') (d : A'' = U) :
    𝟙 U = eqToHom a ≫ (eqToHom b ≫ eqToHom c) ≫ eqToHom d := by
  subst a b c
  simp

namespace ProperFlatChangeOfBase

open CartesianProperFlatSpaces

variable {B : BigFppfSite.{u}} {S S' : Scheme.{u}} {hS : B.Contains S} {hS' : B.Contains S'}
  (g : B.obj hS ⟶ B.obj hS')

/-- The lower-shriek extension along `g`. -/
local notation "Λ" => OverShriek.relocalizePresheafFunctor g

/-- `Λ h_T ≅ h_{(T ⟶ S ⟶ S')}`. -/
local notation "ι" => OverShriek.relocalizeYonedaIso g

/-- The 2-fibre product `(Sch/S) ×_{(Sch/S')} Spaces'_{fp, flat, proper}` over the big fppf site
of `S'`, where `Sch/S` is the big fppf site of `S` read over `S'` along `g`: the base change of
`p'_{fp, flat, proper}` over `S'` along `S ⟶ S'`. -/
abbrev BaseChange :=
  TwoFibreProductOver (Over.forget (Over.mk g)) (cartesianProperFlatProjection B S' hS')
    (𝟭 (BigFppfOver B S' hS')) (Over.forget (Over.mk g)) (cartesianProperFlatProjection B S' hS')

/-- `ProperFlatChangeOfBase.BaseChange g` as a category over the big fppf site of `S'`. -/
abbrev baseChangeBased : BasedCategory (BigFppfOver B S' hS') :=
  BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor (Over.forget (Over.mk g))
    (cartesianProperFlatProjection B S' hS') (𝟭 (BigFppfOver B S' hS'))
    (Over.forget (Over.mk g)) (cartesianProperFlatProjection B S' hS'))

/-- A family over a scheme `T` over `S`, as an object of the base change: the scheme `T` over
`S'` with its factorization through `S`, and the family read over `S'`. -/
def comparisonObj (z : CartesianProperFlatSpaces B S hS) : BaseChange g where
  base := (Over.map g).obj z.base
  x := Over.mk (point g z.base)
  y := (relocalize g).obj z
  hx := rfl
  hy := rfl
  iso := Iso.refl _
  vertical := IsHomLift.id rfl

/-- A morphism of families over `S`, as a morphism of the base change. -/
def comparisonMap {z₁ z₂ : CartesianProperFlatSpaces B S hS} (φ : z₁ ⟶ z₂) :
    comparisonObj g z₁ ⟶ comparisonObj g z₂ where
  hbase := (Over.map g).map φ.hom.hom.right
  a := Over.homMk ((Over.map g).map φ.hom.hom.right) (map_comp_point g _)
  b := (relocalize g).map φ
  ha := IsHomLift.map (p := Over.forget (Over.mk g))
    (Over.homMk ((Over.map g).map φ.hom.hom.right) (map_comp_point g _) :
      Over.mk (point g z₁.base) ⟶ Over.mk (point g z₂.base))
  hb := IsHomLift.map (p := cartesianProperFlatProjection B S' hS') ((relocalize g).map φ)
  w := by
    change (Over.map g).map φ.hom.hom.right ≫ 𝟙 _ = 𝟙 _ ≫ (Over.map g).map φ.hom.hom.right
    simp

/-- **The comparison functor** from Construction A of `Spaces'_{fp, flat, proper}` over `S` to
the base change of `Spaces'_{fp, flat, proper}` over `S'` along `S ⟶ S'`, over the big fppf
site of `S'`. -/
def comparison :
    Stack.changeBase B S S' hS hS' g (cartesianProperFlatBasedCategory B S hS) ⥤ᵇ
      baseChangeBased g where
  obj := comparisonObj g
  map := comparisonMap g
  map_id z := TwoFibreProductOver.Hom.ext'
    (Over.OverMorphism.ext (by
      change (Over.map g).map (𝟙 z.base) = 𝟙 _
      exact (Over.map g).map_id _))
    ((relocalize g).map_id z)
  map_comp φ ψ := TwoFibreProductOver.Hom.ext'
    (Over.OverMorphism.ext (by
      change (Over.map g).map (φ.hom.hom.right ≫ ψ.hom.hom.right) = _
      exact (Over.map g).map_comp _ _))
    ((relocalize g).map_comp φ ψ)
  w := rfl

/-- The comparison functor is faithful: a morphism of families over `S` is determined by its
lower-shriek extension, `Λ` and `Over.map g` being faithful. -/
instance comparison_faithful : (comparison g).toFunctor.Faithful where
  map_injective {z₁ z₂} φ ψ h := by
    change comparisonMap g φ = comparisonMap g ψ at h
    have hb : (relocalize g).map φ = (relocalize g).map ψ :=
      congrArg TwoFibreProductOver.Hom.b h
    have hl : (Λ).map φ.hom.hom.left.hom =
        (Λ).map ψ.hom.hom.left.hom :=
      congrArg (fun m => m.hom.hom.left.hom) hb
    have hr : (Over.map g).map φ.hom.hom.right = (Over.map g).map ψ.hom.hom.right :=
      congrArg (fun m => m.hom.hom.right) hb
    have := relocalizePresheaf_faithful g
    have hr' := congrArg CommaMorphism.left hr
    exact hom_ext' ((Λ).map_injective hl)
      (Over.OverMorphism.ext hr')

/-- The square of a morphism of the base change between two families read over `S'` reads, on
structure morphisms, as a factorization through `S`: the lower-shriek extension of the morphism of
total spaces commutes with the structural morphisms to `h_{(S ⟶ S')}`. -/
theorem comp_viewStructureMap_of_comp {z₁ z₂ : CartesianProperFlatSpaces B S hS}
    (β : (Λ).obj z₁.total ⟶
      (Λ).obj z₂.total) (c : z₁.base ⟶ z₂.base)
    (hβ : β ≫ relocalizeToBase (g := g) z₂ =
      relocalizeToBase (g := g) z₁ ≫ yoneda.map ((Over.map g).map c)) :
    β ≫ OverShriek.viewStructureMap g z₂.total = OverShriek.viewStructureMap g z₁.total := by
  rw [← relocalizeToBase_comp_point, ← relocalizeToBase_comp_point, ← Category.assoc, hβ,
    Category.assoc, ← Functor.map_comp, map_comp_point]

/-- The comparison functor is full: a morphism of the base change has a factorization through
`S` of its morphism of bases, and its morphism of total spaces commutes with the structural
morphisms to `h_{(S ⟶ S')}`, so it is the lower-shriek extension of a morphism of total spaces
over `S` (Stacks 04SG), whose square is cartesian because `Λ` reflects fibre products. -/
theorem comparison_map_surjective {z₁ z₂ : CartesianProperFlatSpaces B S hS}
    (m : comparisonObj g z₁ ⟶ comparisonObj g z₂) : ∃ φ : z₁ ⟶ z₂, comparisonMap g φ = m := by
    have hm_a : m.hbase = m.a.left :=
      @IsHomLift.eq_of_isHomLift _ _ _ _ (Over.forget (Over.mk g)) (comparisonObj g z₁).x
        (comparisonObj g z₂).x m.hbase m.a m.ha
    have hm_b : m.b.hom.hom.right = m.hbase :=
      @hom_right_eq _ _ _ _ _ m.hbase m.b m.hb
    have hw := congrArg CommaMorphism.left (Over.w m.a)
    let c : z₁.base ⟶ z₂.base := Over.homMk m.a.left.left hw
    have hc : (Over.map g).map c = m.a.left := Over.OverMorphism.ext rfl
    have hbc : m.b.hom.hom.right = (Over.map g).map c := by rw [hm_b, hm_a, hc]
    let β : (Λ).obj z₁.total ⟶ (Λ).obj z₂.total := m.b.hom.hom.left.hom
    have hsq : IsPullback β (relocalizeToBase (g := g) z₁) (relocalizeToBase (g := g) z₂)
        (yoneda.map ((Over.map g).map c)) := by
      have h := isPullback_hom m.b
      rw [hbc] at h
      exact h
    obtain ⟨α, hα⟩ := Space.exists_map_eq_of_comp_viewStructureMap B hS hS' g β
      (comp_viewStructureMap_of_comp g β c hsq.w)
    have := relocalizePresheaf_faithful g
    have hn : (Λ).map (yoneda.map c) ≫ (ι).hom.app z₂.base =
        (ι).hom.app z₁.base ≫ yoneda.map ((Over.map g).map c) :=
      (ι).hom.naturality c
    have hcomm : α ≫ z₂.toBase = z₁.toBase ≫ yoneda.map c := by
      refine (Λ).map_injective ?_
      rw [← Iso.cancel_iso_hom_right _ _ ((ι).app z₂.base)]
      calc (Λ).map (α ≫ z₂.toBase) ≫ (ι).hom.app z₂.base
          = β ≫ ((Λ).map z₂.toBase ≫ (ι).hom.app z₂.base) := by
            rw [Functor.map_comp, Category.assoc, hα]
        _ = ((Λ).map z₁.toBase ≫ (ι).hom.app z₁.base) ≫ yoneda.map ((Over.map g).map c) := hsq.w
        _ = (Λ).map (z₁.toBase ≫ yoneda.map c) ≫ (ι).hom.app z₂.base := by
            rw [Functor.map_comp]
            simp only [Category.assoc]
            rw [hn]
    have hΛsq : IsPullback ((Λ).map α) ((Λ).map z₁.toBase) ((Λ).map z₂.toBase)
        ((Λ).map (yoneda.map c)) := by
      rw [hα]
      refine hsq.of_iso (Iso.refl _) (Iso.refl _) ((ι).app z₁.base).symm ((ι).app z₂.base).symm
        (by simp) (by simp [relocalizeToBase]) (by simp [relocalizeToBase]) ?_
      rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
      exact hn.symm
    have := relocalizePresheaf_reflectsPullbacks g
    have hαsq : IsPullback α z₁.toBase z₂.toBase (yoneda.map c) :=
      IsPullback.of_map Λ hcomm hΛsq
    exact ⟨homOfIsPullback α c hαsq, TwoFibreProductOver.Hom.ext'
      (Over.OverMorphism.ext hc) (hom_ext' hα hbc.symm)⟩

/-- The comparison functor is full. -/
instance comparison_full : (comparison g).toFunctor.Full where
  map_surjective m := comparison_map_surjective g m

/-- Every object of the base change is isomorphic to one in the image of the comparison: a
family over `S'` with a factorization of its base through `S` is the lower-shriek extension of a
family over `S` (Stacks 04SG). -/
theorem exists_comparisonObj_iso (y : BaseChange g) :
    ∃ (z : CartesianProperFlatSpaces B S hS) (e : comparisonObj g z ≅ y),
      (baseChangeBased g).p.IsHomLift (𝟙 y.base) e.hom := by
    let Y := y.y
    let ψ : Y.base ⟶ Over.mk g := y.iso.inv ≫ y.x.hom
    let T : BigFppfOver B S hS := Over.mk ψ.left
    let θ : (Over.map g).obj T ≅ Y.base :=
      Over.isoMk (Iso.refl _) (by rw [Iso.refl_hom, Category.id_comp]; exact (Over.w ψ).symm)
    have hθψ : θ.inv ≫ point g T = ψ := Over.OverMorphism.ext (by simp [θ, point, T])
    let X : AlgebraicSpaces B S' hS' := ⟨Y.total, Y.isAlgebraicSpace_total⟩
    let f : X ⟶ schemeSpace (Over.mk g) := ObjectProperty.homMk (Y.toBase ≫ yoneda.map ψ)
    obtain ⟨XT, e, he⟩ := Space.exists_relocalizeSpace_iso B hS hS' g X f
    let eX : (Λ).obj XT.1 ≅ Y.total := (ObjectProperty.ι _).mapIso e
    let k : (Λ).obj XT.1 ⟶ (Λ).obj (yoneda.obj T) :=
      eX.hom ≫ Y.toBase ≫ yoneda.map θ.inv ≫ (ι).inv.app T
    have hk : k ≫ OverShriek.viewStructureMap g (yoneda.obj T) =
        OverShriek.viewStructureMap g XT.1 := by
      rw [← relocalizeYonedaIso_hom_app_comp_yoneda_map_point]
      simp only [k, Category.assoc, Iso.inv_hom_id_app_assoc]
      rw [← Functor.map_comp, hθψ]
      exact (congrArg (fun φ => φ.hom) he).trans
        (Space.relocalizeHom_comp_relocalizeBaseHom B hS hS' g XT.2 _)
    obtain ⟨t, ht⟩ := Space.exists_map_eq_of_comp_viewStructureMap B hS hS' g k hk
    have hΛ : (Λ).map t ≫ (ι).hom.app T = eX.hom ≫ Y.toBase ≫ yoneda.map θ.inv := by
      rw [ht]
      simp [k]
    have hw : eX.inv ≫ ((Λ).map t ≫ (ι).hom.app T) = Y.toBase ≫ yoneda.map θ.inv := by
      rw [hΛ, Iso.inv_hom_id_assoc]
    have hfp : Space.IsFinitePresentation B S hS t :=
      (isFinitePresentation_relocalize_comp_iff g t).1
        (Space.isFinitePresentation_of_arrowIso B S' hS' Y.toBase _ eX.inv
          (yoneda.map θ.inv) hw Y.isFinitePresentation_toBase)
    have hfl : Space.IsFlat B S hS t := by
      refine (isFlat_relocalize_comp_iff g t).1 ?_
      change Space.IsFlat B S' hS' ((Λ).map t ≫ (ι).hom.app T)
      rw [hΛ]
      exact (Space.holdsOnEveryEtaleChart_iso_comp_iff B S' hS' _ eX.hom _).2
        ((Space.holdsOnEveryEtaleChart_comp_iso_iff B S' hS' _ Y.toBase _).2 Y.isFlat_toBase)
    have hpr : Space.IsProper B S hS t :=
      (isProper_relocalize_comp_iff g XT.2 t).1
        (Space.isProper_of_arrowIso B S' hS' Y.toBase _ eX.inv (yoneda.map θ.inv) hw
          Y.isProper_toBase)
    let i : Over.mk (point g T) ≅ y.x :=
      Over.isoMk (θ ≪≫ y.iso.symm)
        ((Category.assoc _ _ _).trans ((congrArg (θ.hom ≫ ·) hθψ.symm).trans
          (θ.hom_inv_id_assoc _)))
    have hv := y.vertical
    have hiso : y.iso.hom = eqToHom (y.hx.trans y.hy.symm) :=
      @eq_eqToHom_of_isHomLift_id _ _ _ _ _ y.iso.hom y.hx y.hy y.vertical
    have hinv : y.iso.inv = eqToHom (y.hx.trans y.hy.symm).symm :=
      Iso.inv_ext (by rw [hiso]; exact eqToHom_trans _ _ |>.trans (eqToHom_refl _ _))
    have hT : (Over.map g).obj T = Y.base := by
      change Over.mk (ψ.left ≫ g) = Y.base
      have h : ψ.left ≫ g = Y.base.hom := Over.w ψ
      rw [h]
      rfl
    have hθ : θ.hom = eqToHom hT :=
      Over.OverMorphism.ext (by rw [Over.eqToHom_left]; exact (eqToHom_refl _ _).symm)
    refine ⟨mk' T XT.1 XT.2 t hfp hfl hpr, TwoFibreProductOver.isoMk i
      (relocalizeIsoOfIso g (mk' T XT.1 XT.2 t hfp hfl hpr) Y eX θ hΛ) ?_ ?_, ?_⟩
    · change 𝟙 _ ≫ θ.hom ≫ eqToHom y.hy = 𝟙 _ ≫ (θ.hom ≫ y.iso.inv) ≫ eqToHom y.hx
      rw [hinv, Category.id_comp, Category.id_comp]
      exact (congrArg (θ.hom ≫ ·) (eqToHom_trans _ _).symm).trans (Category.assoc _ _ _).symm
    · change (θ.hom ≫ y.iso.inv) ≫ y.iso.hom = 𝟙 _ ≫ θ.hom
      exact (Category.assoc _ _ _).trans ((congrArg (θ.hom ≫ ·) y.iso.inv_hom_id).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm))
    · refine TwoFibreProductOver.structureFunctor_isHomLift _ (𝟙 y.base) ?_
      refine IsHomLift.of_fac (p := Over.forget (Over.mk g)) (𝟙 y.base) i.hom (hT.trans y.hy)
        y.hx ?_
      change 𝟙 y.base = eqToHom (hT.trans y.hy).symm ≫ (θ.hom ≫ y.iso.inv) ≫ eqToHom y.hx
      rw [hθ, hinv]
      exact id_eq_eqToHom_comp_comp _ _ _ _

/-- Every object of the base change is isomorphic to one in the image of the comparison. -/
instance comparison_essSurj : (comparison g).toFunctor.EssSurj where
  mem_essImage y :=
    let ⟨z, e, _⟩ := exists_comparisonObj_iso g y
    ⟨z, ⟨e⟩⟩

/-- The preimage, under the comparison, of an object of the base change. -/
def preimageObj (y : BaseChange g) : CartesianProperFlatSpaces B S hS :=
  (exists_comparisonObj_iso g y).choose

/-- The vertical isomorphism from the image of `preimageObj g y` to `y`. -/
def preimageIso (y : BaseChange g) : comparisonObj g (preimageObj g y) ≅ y :=
  (exists_comparisonObj_iso g y).choose_spec.choose

/-- `preimageIso g y` lies over the identity of the base of `y`. -/
theorem isHomLift_preimageIso (y : BaseChange g) :
    (baseChangeBased g).p.IsHomLift (𝟙 ((baseChangeBased g).p.obj y)) (preimageIso g y).hom :=
  (exists_comparisonObj_iso g y).choose_spec.choose_spec

/-- **Construction A of `Spaces'_{fp, flat, proper}` over `S` is equivalent, over the big fppf
site of `S'`, to the base change `(Sch/S) ×_{(Sch/S')} Spaces'_{fp, flat, proper}` of
`Spaces'_{fp, flat, proper}` over `S'` along `S ⟶ S'`.** -/
def equivalence :
    BasedCategory.Equivalence
      (Stack.changeBase B S S' hS hS' g (cartesianProperFlatBasedCategory B S hS))
      (baseChangeBased g) :=
  BasedCategory.Equivalence.ofFullyFaithfulLift (comparison g)
    (Functor.FullyFaithful.ofFullyFaithful _) (preimageObj g) (preimageIso g)
    (isHomLift_preimageIso g)

/-- The base change of an algebraic stack `Spaces'_{fp, flat, proper}` over `S'` along `S ⟶ S'`
is an algebraic stack over `S'` (Stacks 04TF). -/
theorem isAlgebraicStack_baseChangeBased
    (h : Stack.IsAlgebraicStack.{u, w} B S' hS' (cartesianProperFlatBasedCategory B S' hS')) :
    Stack.IsAlgebraicStack.{u, w} B S' hS' (baseChangeBased g) := by
  have := Stack.locallySmall_of_isAlgebraicStack B S' hS' h
  obtain ⟨_hTfib, hTst, hTdiag, _hTatlas⟩ := Stack.isAlgebraicStack_terminal.{u, w} B S' hS'
  exact Stack.isAlgebraicStack_twoFibreProduct_of_locallySmall B S' hS'
    (Stack.schemeFibredCategory B S' hS' (Over.mk g)).val
    (cartesianProperFlatBasedCategory B S' hS') (BasedCategory.ofFunctor (𝟭 _))
    ⟨Over.forget (Over.mk g), Functor.comp_id _⟩
    ⟨cartesianProperFlatProjection B S' hS', Functor.comp_id _⟩ hTst hTdiag
    (Stack.isAlgebraicStack_schemeFibredCategory.{u, w} B S' hS' (Over.mk g)) h

end ProperFlatChangeOfBase

/-! ### Algebraicity across a change of base -/

/-- **Construction A reflects algebraicity, for categories with large morphisms.** A category over
the big fppf site of `S` whose image under Construction A along `g : S ⟶ S'` is an algebraic
stack over `S'` is an algebraic stack over `S`. This is
`AlgebraicGeometry.Stack.isAlgebraicStack_changeBase_iff` (Stacks 04X5) for categories whose
morphisms live one universe up, through their shrunken forms. -/
theorem Stack.isAlgebraicStack_of_isAlgebraicStack_changeBase_of_largeHoms
    {B : BigFppfSite.{u}} {S S' : Scheme.{u}} {hS : B.Contains S} {hS' : B.Contains S'}
    (g : B.obj hS ⟶ B.obj hS') (𝒳 : BasedCategory.{v, u + 1} (BigFppfOver B S hS))
    (h : Stack.IsAlgebraicStack.{u, w} B S' hS' (Stack.changeBase B S S' hS hS' g 𝒳)) :
    Stack.IsAlgebraicStack.{u, w} B S hS 𝒳 := by
  have hls : LocallySmall.{u} (Stack.changeBase B S S' hS hS' g 𝒳).obj :=
    Stack.locallySmall_of_isAlgebraicStack B S' hS' h
  have : LocallySmall.{u} 𝒳.obj := hls
  have h₁ : Stack.IsAlgebraicStack.{u, w} B S' hS'
      (Stack.changeBase B S S' hS hS' g 𝒳.shrinkHoms) :=
    (Stack.isAlgebraicStack_shrinkHoms_iff B S' hS' (Stack.changeBase B S S' hS hS' g 𝒳)).2 h
  exact (Stack.isAlgebraicStack_shrinkHoms_iff B S hS 𝒳).1
    ((Stack.isAlgebraicStack_changeBase_iff B S S' hS hS' g 𝒳.shrinkHoms).1 h₁)

/-- **Algebraicity of `Spaces'_{fp, flat, proper}` is inherited by every smaller base.** If the
stack `p'_{fp, flat, proper}` of finitely presented, flat and proper algebraic spaces over the big
fppf site of `S'` is an algebraic stack, then so is the stack `p'_{fp, flat, proper}` over the big
fppf site of any `S` with a morphism `S ⟶ S'` of the site. The latter is, after Construction A
(Stacks 04X5), the base change of the former along `S ⟶ S'`, which is algebraic by Stacks 04TF. -/
theorem isAlgebraicStack_cartesianProperFlatBasedCategory_of_changeBase
    {B : BigFppfSite.{u}} {S S' : Scheme.{u}} {hS : B.Contains S} {hS' : B.Contains S'}
    (g : B.obj hS ⟶ B.obj hS')
    (h : Stack.IsAlgebraicStack.{u, w} B S' hS' (cartesianProperFlatBasedCategory B S' hS')) :
    Stack.IsAlgebraicStack.{u, w} B S hS (cartesianProperFlatBasedCategory B S hS) :=
  Stack.isAlgebraicStack_of_isAlgebraicStack_changeBase_of_largeHoms g _
    ((Stack.isAlgebraicStack_iff_of_equivalence B S' hS' (ProperFlatChangeOfBase.equivalence g)).2
      (ProperFlatChangeOfBase.isAlgebraicStack_baseChangeBased g h))

/-- **A non-effective formal object over a smaller base shows that `Spaces'_{fp, flat, proper}` is
not algebraic.** If the stack `p'_{fp, flat, proper}` over the big fppf site of `S` has a formal
object (Stacks 07X3) which is not effective (Stacks 07X7), and `S ⟶ S'` is a morphism of the site,
then `p'_{fp, flat, proper}` over the big fppf site of `S'` is not an algebraic stack: otherwise
its base change to `S` would be (`isAlgebraicStack_cartesianProperFlatBasedCategory_of_changeBase`),
and every formal object of an algebraic stack is effective (Stacks 07X8). -/
theorem not_isAlgebraicStack_cartesianProperFlatBasedCategory_of_changeBase
    {B : BigFppfSite.{u}} {S S' : Scheme.{u}} {hS : B.Contains S} {hS' : B.Contains S'}
    (g : B.obj hS ⟶ B.obj hS')
    (ξ : Deformation.Artin.FormalObject B S hS (cartesianProperFlatProjection B S hS))
    (hξ : ¬ Deformation.Artin.FormalObject.IsEffective B S hS
      (cartesianProperFlatProjection B S hS)
      (cartesianProperFlatProjection_isFiberedInGroupoids B S hS) ξ) :
    ¬ Stack.IsAlgebraicStack.{u, w} B S' hS' (cartesianProperFlatBasedCategory B S' hS') :=
  fun h => not_isAlgebraicStack_cartesianProperFlatProjection_of_not_isEffective.{u, w} B S hS ξ hξ
    (isAlgebraicStack_cartesianProperFlatBasedCategory_of_changeBase g h)

end AlgebraicGeometry

end
