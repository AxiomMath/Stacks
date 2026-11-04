module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RelativeMapBaseRestrict
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusChoice

/-!
# The relative map of Stacks 06CK under a morphism of quintuples

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
and let `d` be a natural number. A morphism `φ : Ξ ⟶ Ξ'` of the relative finite Hilbert category
`ℋ_d(𝒳/𝒴)` has a base component `f : U ⟶ U'`, and the remark preceding the definition of the
local complete intersection locus in the section of **Stacks 06CJ** says that the relative map
`x_α : Z ⟶ X_y` of **Stacks 06CK** attached to `Ξ` is read off the one attached to `Ξ'` along
`f`.

A set of data exhibiting the relative map of `Ξ'` is **transported** along `φ` to one for `Ξ`:
the scheme-valued point is restricted along `CategoryTheory.Over.map f`, the representing
algebraic space along the restriction of presheaves — which it remains, by part (1) of
Stacks 03I5 — and the two comparison morphisms are the unique vertical morphisms factoring
through the components of `φ`, which are strongly cartesian because `𝒴` is fibred in groupoids.
The relative map of the transport is the restriction of the original one, composed with the
comparison of the representable presheaf of the cover of `Ξ` with the restriction of the
representable presheaf of the cover of `Ξ'`.

## Main definitions

* `AlgebraicGeometry.Stack.FiniteHilbert.coverComparisonOfSquare`: the comparison of the two
  covers of a commutative square of the site.
* `AlgebraicGeometry.Stack.FiniteHilbert.baseComparison` and
  `AlgebraicGeometry.Stack.FiniteHilbert.coverComparison`: the base and the cover of the source
  quintuple, read over the base of the target one, compared with the base and the cover of the
  target.
* `AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData.homUnit` and
  `AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData.homAlpha`: the two comparison morphisms
  of the transported data.
* `AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData.ofHom`: the transport of a set of data
  exhibiting the relative map along a morphism of quintuples.

## Main results

* `AlgebraicGeometry.Stack.FiniteHilbert.Object.overMap_restrictBaseOver`,
  `AlgebraicGeometry.Stack.FiniteHilbert.Object.overMap_restrictCoverOver`,
  `AlgebraicGeometry.Stack.FiniteHilbert.Object.x_over_restrictCoverOver` and
  `AlgebraicGeometry.Stack.FiniteHilbert.restrictPoint_comp`: the base, the cover, the object `x`
  and a scheme-valued point of `𝒴`, all read along an arbitrary morphism `U ⟶ U'` of the site out
  of the base of a quintuple.
* `AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData.homUnit_comp` and
  `AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData.homAlpha_square`: the defining
  factorizations of the two comparison morphisms through the components of `φ`.
* `AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData.isIso_restrictYonedaHom_coverComparison`:
  the comparison of the representable presheaf of the cover of the source quintuple with the
  restriction of the representable presheaf of the cover of the target is an isomorphism.
* `AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData.map_hom_ofHom`: the relative map of the
  transported data is the restriction of the original relative map.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
* [Stacks Project, Tag 06CJ](https://stacks.math.columbia.edu/tag/06CJ)
* [Stacks Project, Tag 06CK](https://stacks.math.columbia.edu/tag/06CK)
-/

@[expose] public section

open CategoryTheory Opposite

universe u w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒴 : StackInGroupoids.{w} (BigFppfOver B S hS) (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory} {d : ℕ}

namespace FiniteHilbert

variable {P Q : Object B S hS 𝒳 𝒴 F d}

/-! ### The base and the cover, read over the base of the target -/

/-- The base component of a morphism of quintuples is a morphism over `S`. -/
theorem hom_f_left_comp (φ : P ⟶ Q) : φ.f.left ≫ Q.U.hom = P.U.hom :=
  Over.w φ.f

/-- The base of the source quintuple, read over the base of the target one through the base
component of the morphism, compared with the base of the target: the comparison is the base
component itself. -/
def baseComparison (φ : P ⟶ Q) :
    (Over.map φ.f.left).obj P.baseOver ⟶ Q.baseOver :=
  Over.homMk φ.f.left (by
    change φ.f.left ≫ 𝟙 Q.U.left = 𝟙 P.U.left ≫ φ.f.left
    simp)

/-- **The comparison of the two covers of a commutative square of the site.** For `g` a morphism
of covers over a morphism `i` of bases, the source cover read over the target base maps to the
target cover, by `g` itself. -/
def coverComparisonOfSquare {U U' Z Z' : BigFppfOver B S hS} {q : Z ⟶ U} {q' : Z' ⟶ U'}
    {g : Z ⟶ Z'} {i : U ⟶ U'} (hg : g ≫ q' = q ≫ i) :
    (Over.map i.left).obj (Over.mk q.left : BigFppfOver B U.left.1 U.left.2) ⟶
      (Over.mk q'.left : BigFppfOver B U'.left.1 U'.left.2) :=
  Over.homMk g.left (by
    have h := congrArg Over.Hom.left hg
    simp only [Over.comp_left] at h
    change g.left ≫ q'.left = q.left ≫ i.left
    exact h)

/-- The cover of the source quintuple, read over the base of the target one, compared with the
cover of the target: the comparison is the cover component of the morphism, whose compatibility
with the two structure morphisms is the commutation of the cartesian square. -/
def coverComparison (φ : P ⟶ Q) :
    (Over.map φ.f.left).obj P.coverOver ⟶ Q.coverOver :=
  coverComparisonOfSquare φ.square.w

/-- **The structure morphism of the cover is compatible with the two comparisons.** Reading the
structure morphism of the cover of the source quintuple over the base of the target and following
it with the base comparison is the cover comparison followed by the structure morphism of the
cover of the target. -/
theorem coverComparison_comp_coverToBase (φ : P ⟶ Q) :
    (Over.map φ.f.left).map P.coverToBase ≫ baseComparison φ =
      coverComparison φ ≫ Q.coverToBase := by
  refine Over.OverMorphism.ext ?_
  have h := congrArg Over.Hom.left φ.square.w
  simp only [Over.comp_left] at h
  show P.q.left ≫ φ.f.left = φ.g.left ≫ Q.q.left
  exact h.symm

/-! ### The base objects of the two slices -/

/-- Reading the base of a quintuple over itself and then forgetting the base returns the base. -/
theorem Object.overMap_baseOver (P : Object B S hS 𝒳 𝒴 F d) :
    (Over.map P.U.hom).obj P.baseOver = P.U := by
  show Over.mk (𝟙 P.U.left ≫ P.U.hom) = P.U
  exact PresheafOfCategories.over_mk_eq P.U (Category.id_comp P.U.hom)

/-- The base of a quintuple, read over an object `U'` of the site that its base maps to and then
over `S`, is the base of the quintuple. -/
theorem Object.overMap_restrictBaseOver (P : Object B S hS 𝒳 𝒴 F d)
    {U' : BigFppfOver B S hS} (i : P.U ⟶ U') :
    (Over.map U'.hom).obj ((Over.map i.left).obj P.baseOver) = P.U :=
  (Functor.congr_obj (overMap_comp_eq_of_comp_hom i.left (Over.w i)) P.baseOver).trans
    P.overMap_baseOver

/-- The cover of a quintuple, read over an object `U'` of the site that its base maps to and then
over `S`, is the cover of the quintuple. -/
theorem Object.overMap_restrictCoverOver (P : Object B S hS 𝒳 𝒴 F d)
    {U' : BigFppfOver B S hS} (i : P.U ⟶ U') :
    (Over.map U'.hom).obj ((Over.map i.left).obj P.coverOver) = P.Z :=
  (Functor.congr_obj (overMap_comp_eq_of_comp_hom i.left (Over.w i)) P.coverOver).trans
    P.overMap_coverOver

/-- The object `x` of a quintuple lies over its cover read over an object `U'` of the site that
its base maps to. -/
theorem Object.x_over_restrictCoverOver (P : Object B S hS 𝒳 𝒴 F d)
    {U' : BigFppfOver B S hS} (i : P.U ⟶ U') :
    𝒳.toBasedCategory.p.obj P.x =
      (Over.map U'.hom).obj ((Over.map i.left).obj P.coverOver) :=
  P.x_over.trans (Object.overMap_restrictCoverOver P i).symm

/-- **The restriction of a scheme-valued point of `𝒴` along a morphism of base objects is a
scheme-valued point over the source.** -/
theorem restrictPoint_comp {U U' : BigFppfOver B S hS} (i : U ⟶ U')
    {w : BigFppfOver B U'.left.1 U'.left.2 ⥤ 𝒴.toBasedCategory.obj}
    (hw : w ⋙ 𝒴.toBasedCategory.p = Over.map U'.hom) :
    (Over.map i.left ⋙ w) ⋙ 𝒴.toBasedCategory.p = Over.map U.hom := by
  rw [Functor.assoc, hw]
  exact overMap_comp_eq_of_comp_hom i.left (Over.w i)

/-- The base of the source quintuple, read over the base of the target one and then over `S`, is
the base of the source quintuple. -/
theorem overMap_obj_base (φ : P ⟶ Q) :
    (Over.map Q.U.hom).obj ((Over.map φ.f.left).obj P.baseOver) = P.U :=
  Object.overMap_restrictBaseOver P φ.f

/-- The cover of the source quintuple, read over the base of the target one and then over `S`, is
the cover of the source quintuple. -/
theorem overMap_obj_cover (φ : P ⟶ Q) :
    (Over.map Q.U.hom).obj ((Over.map φ.f.left).obj P.coverOver) = P.Z :=
  Object.overMap_restrictCoverOver P φ.f

/-! ### Transport of a lift along an identification of the base morphism -/

/-- A morphism lifting `f` lifts any morphism identified with `f` by identifications of its
source and target. -/
private theorem isHomLift_of_base_eq {𝒞 : Type*} [Category 𝒞] {𝒟 : Type*} [Category 𝒟]
    (p : 𝒟 ⥤ 𝒞) {R S' R' S'' : 𝒞} {a b : 𝒟} (f : R ⟶ S') (f' : R' ⟶ S'') (ψ : a ⟶ b)
    (hR : R' = R) (hS : S' = S'') (hff : f' = eqToHom hR ≫ f ≫ eqToHom hS)
    (h : p.IsHomLift f ψ) : p.IsHomLift f' ψ := by
  have := h
  refine CategoryTheory.IsHomLift.of_fac' p f' ψ
    ((CategoryTheory.IsHomLift.domain_eq p f ψ).trans hR.symm)
    ((CategoryTheory.IsHomLift.codomain_eq p f ψ).trans hS) ?_
  rw [CategoryTheory.IsHomLift.fac' p f ψ, hff]
  simp

/-- The base comparison lies over the base component of the morphism. -/
theorem isHomLift_baseComparison (φ : P ⟶ Q) :
    (Over.map Q.U.hom).IsHomLift φ.f (baseComparison φ) := by
  refine CategoryTheory.IsHomLift.of_fac' (Over.map Q.U.hom) φ.f (baseComparison φ)
    (overMap_obj_base φ) (Object.overMap_baseOver Q) ?_
  refine PresheafOfCategories.over_hom_eq_conj (overMap_obj_base φ)
    (Object.overMap_baseOver Q) rfl rfl _ _ ?_
  show φ.f.left = eqToHom rfl ≫ φ.f.left ≫ eqToHom rfl
  simp

/-- The cover comparison lies over the cover component of the morphism. -/
theorem isHomLift_coverComparison (φ : P ⟶ Q) :
    (Over.map Q.U.hom).IsHomLift φ.g (coverComparison φ) := by
  refine CategoryTheory.IsHomLift.of_fac' (Over.map Q.U.hom) φ.g (coverComparison φ)
    (overMap_obj_cover φ) (Object.overMap_coverOver Q) ?_
  refine PresheafOfCategories.over_hom_eq_conj (overMap_obj_cover φ)
    (Object.overMap_coverOver Q) rfl rfl _ _ ?_
  show φ.g.left = eqToHom rfl ≫ φ.g.left ≫ eqToHom rfl
  simp

/-- **The structure morphism of the cover of a quintuple, read in the slice of its base, lies over
itself.** -/
theorem isHomLift_coverToBase (P : Object B S hS 𝒳 𝒴 F d) :
    (Over.map P.U.hom).IsHomLift P.q P.coverToBase := by
  refine CategoryTheory.IsHomLift.of_fac' (Over.map P.U.hom) P.q P.coverToBase
    (Object.overMap_coverOver P) (Object.overMap_baseOver P) ?_
  refine PresheafOfCategories.over_hom_eq_conj (Object.overMap_coverOver P)
    (Object.overMap_baseOver P) rfl rfl _ _ ?_
  show P.q.left = eqToHom rfl ≫ P.q.left ≫ eqToHom rfl
  simp

/-- The object `x` of the source quintuple lies over its cover read over the base of the target
quintuple. -/
theorem x_over_cover (φ : P ⟶ Q) : 𝒳.toBasedCategory.p.obj P.x =
    (Over.map Q.U.hom).obj ((Over.map φ.f.left).obj P.coverOver) :=
  Object.x_over_restrictCoverOver P φ.f

/-- The `𝒳`-component of a morphism of quintuples lies over the cover comparison read over the
base of the target quintuple. -/
theorem isHomLift_hom_a (φ : P ⟶ Q) :
    𝒳.toBasedCategory.p.IsHomLift ((Over.map Q.U.hom).map (coverComparison φ)) φ.a := by
  refine isHomLift_of_base_eq 𝒳.toBasedCategory.p φ.g
    ((Over.map Q.U.hom).map (coverComparison φ)) φ.a (overMap_obj_cover φ)
    (Object.overMap_coverOver Q).symm ?_ φ.a_over
  refine PresheafOfCategories.over_hom_eq_conj (overMap_obj_cover φ)
    (Object.overMap_coverOver Q) rfl rfl _ _ ?_
  show φ.g.left = eqToHom rfl ≫ φ.g.left ≫ eqToHom rfl
  simp

/-! ### The transported data -/

namespace RelativeMapData

variable (φ : P ⟶ Q) (D : RelativeMapData Q)

/-- The transported scheme-valued point: the point of the target quintuple restricted along the
base component of the morphism. -/
abbrev homPoint : BigFppfOver B P.U.left.1 P.U.left.2 ⥤ 𝒴.toBasedCategory.obj :=
  Over.map φ.f.left ⋙ D.y

/-- The transported point is a section of `𝒴` over the big fppf site of the base of the source
quintuple. -/
theorem homPoint_comp : homPoint φ D ⋙ 𝒴.toBasedCategory.p = Over.map P.U.hom :=
  restrictPoint_comp φ.f D.y_comp

/-! #### The transported identification at the base -/

/-- The `𝒴`-component of a morphism of quintuples is strongly cartesian, `𝒴` being fibred in
groupoids. -/
instance isStronglyCartesian_hom_b (φ : P ⟶ Q) :
    𝒴.toBasedCategory.p.IsStronglyCartesian φ.f φ.b :=
  have := φ.b_over
  𝒴.isStackInGroupoids.isFiberedInGroupoids.isStronglyCartesian_homLift φ.f φ.b

/-- The restriction of the point along the base comparison lies over the base component. -/
theorem isHomLift_map_baseComparison :
    𝒴.toBasedCategory.p.IsHomLift φ.f (D.y.map (baseComparison φ)) :=
  PresheafOfCategories.isHomLift_map_of_comp D.y_comp φ.f (baseComparison φ)
    (isHomLift_baseComparison φ)

/-- The restriction of the point along the base comparison, followed by the identification of the
value of the point at the base of the target with the object `y` of the target quintuple, lies
over the base component. -/
instance isHomLift_baseUnit :
    𝒴.toBasedCategory.p.IsHomLift φ.f (D.y.map (baseComparison φ) ≫ D.yUnit) :=
  have := isHomLift_map_baseComparison φ D
  have := D.yUnit_over
  IsHomLift.comp_lift_id_right' 𝒴.toBasedCategory.p φ.f (D.y.map (baseComparison φ)) Q.U D.yUnit

/-- **The transported identification of the value of the point at the base with the object `y` of
the source quintuple.** It is the unique vertical morphism whose composite with the
`𝒴`-component of `φ` is the restriction of the point along the base comparison followed by the
identification of the target quintuple. -/
noncomputable def homUnit : (homPoint φ D).obj P.baseOver ⟶ P.y :=
  Functor.IsStronglyCartesian.map 𝒴.toBasedCategory.p φ.f φ.b (Category.id_comp φ.f).symm
    (D.y.map (baseComparison φ) ≫ D.yUnit)

/-- The transported identification is vertical. -/
instance isHomLift_homUnit : 𝒴.toBasedCategory.p.IsHomLift (𝟙 P.U) (homUnit φ D) :=
  Functor.IsStronglyCartesian.map_isHomLift 𝒴.toBasedCategory.p φ.f φ.b
    (Category.id_comp φ.f).symm (D.y.map (baseComparison φ) ≫ D.yUnit)

/-- **The defining factorization of the transported identification at the base.** -/
theorem homUnit_comp :
    homUnit φ D ≫ φ.b = D.y.map (baseComparison φ) ≫ D.yUnit :=
  Functor.IsStronglyCartesian.fac 𝒴.toBasedCategory.p φ.f φ.b (Category.id_comp φ.f).symm
    (D.y.map (baseComparison φ) ≫ D.yUnit)

/-! #### The transported identification at the cover -/

/-- The image under `F` of the `𝒳`-component of a morphism of quintuples lies over the cover
component. -/
instance isHomLift_map_hom_a : 𝒴.toBasedCategory.p.IsHomLift φ.g (F.toFunctor.map φ.a) :=
  PresheafOfCategories.isHomLift_map_of_comp F.w φ.g φ.a φ.a_over

/-- The image under `F` of the `𝒳`-component of a morphism of quintuples is strongly cartesian,
`𝒴` being fibred in groupoids. -/
instance isStronglyCartesian_map_hom_a :
    𝒴.toBasedCategory.p.IsStronglyCartesian φ.g (F.toFunctor.map φ.a) :=
  𝒴.isStackInGroupoids.isFiberedInGroupoids.isStronglyCartesian_homLift φ.g
    (F.toFunctor.map φ.a)

/-- The identification of the target quintuple is vertical over its cover. -/
theorem isHomLift_alpha : 𝒴.toBasedCategory.p.IsHomLift (𝟙 Q.Z) D.α.hom := by
  have h := D.α_over
  rwa [Object.overMap_coverOver] at h

/-- The restriction of the point along the cover comparison, followed by the identification of the
target quintuple, lies over the cover component. -/
instance isHomLift_coverAlpha :
    𝒴.toBasedCategory.p.IsHomLift φ.g (D.y.map (coverComparison φ) ≫ D.α.hom) :=
  have := PresheafOfCategories.isHomLift_map_of_comp D.y_comp φ.g (coverComparison φ)
    (isHomLift_coverComparison φ)
  have := isHomLift_alpha D
  IsHomLift.comp_lift_id_right' 𝒴.toBasedCategory.p φ.g (D.y.map (coverComparison φ)) Q.Z
    D.α.hom

/-- The transported identification at the cover, before it is recognised as an isomorphism: the
unique vertical morphism whose composite with the image under `F` of the `𝒳`-component of `φ` is
the restriction of the point along the cover comparison followed by the identification of the
target quintuple. -/
noncomputable def homAlphaHom : (homPoint φ D).obj P.coverOver ⟶ F.toFunctor.obj P.x :=
  Functor.IsStronglyCartesian.map 𝒴.toBasedCategory.p φ.g (F.toFunctor.map φ.a)
    (Category.id_comp φ.g).symm (D.y.map (coverComparison φ) ≫ D.α.hom)

/-- The transported identification at the cover is vertical. -/
instance isHomLift_homAlphaHom :
    𝒴.toBasedCategory.p.IsHomLift (𝟙 P.Z) (homAlphaHom φ D) :=
  Functor.IsStronglyCartesian.map_isHomLift 𝒴.toBasedCategory.p φ.g (F.toFunctor.map φ.a)
    (Category.id_comp φ.g).symm (D.y.map (coverComparison φ) ≫ D.α.hom)

/-- The transported identification at the cover is invertible. -/
instance isIso_homAlphaHom : IsIso (homAlphaHom φ D) :=
  have := 𝒴.isStackInGroupoids.isFiberedInGroupoids.isStronglyCartesian_homLift (𝟙 P.Z)
    (homAlphaHom φ D)
  Functor.IsStronglyCartesian.isIso_of_base_isIso 𝒴.toBasedCategory.p (𝟙 P.Z) (homAlphaHom φ D)

/-- **The transported identification of the restriction of the point to the cover with `F x`.** -/
noncomputable def homAlpha : (homPoint φ D).obj P.coverOver ≅ F.toFunctor.obj P.x :=
  asIso (homAlphaHom φ D)

/-- The transported identification at the cover, written out. -/
theorem homAlpha_hom : (homAlpha φ D).hom = homAlphaHom φ D := rfl

/-- **The comparison square of the two identifications at the cover**, which is the defining
factorization of the transported one: the restriction of the point along the cover comparison
carries the original identification to the transported one. -/
theorem homAlpha_square :
    D.y.map (coverComparison φ) ≫ D.α.hom =
      (homAlpha φ D).hom ≫ F.toFunctor.map φ.a :=
  (Functor.IsStronglyCartesian.fac 𝒴.toBasedCategory.p φ.g (F.toFunctor.map φ.a)
    (Category.id_comp φ.g).symm (D.y.map (coverComparison φ) ≫ D.α.hom)).symm

/-- The transported identification is vertical over the cover of the source quintuple, read in the
big fppf site of `S` through the slice functor of the base of the source quintuple. -/
theorem isHomLift_homAlpha :
    𝒴.toBasedCategory.p.IsHomLift (𝟙 ((Over.map P.U.hom).obj P.coverOver))
      (homAlpha φ D).hom := by
  have h := isHomLift_homAlphaHom φ D
  rwa [← Object.overMap_coverOver P] at h

/-- The transported identification is vertical for the cover read over the base of the target
quintuple. -/
theorem isHomLift_homAlpha' :
    𝒴.toBasedCategory.p.IsHomLift
      (𝟙 ((Over.map Q.U.hom).obj ((Over.map φ.f.left).obj P.coverOver)))
      (homAlpha φ D).hom := by
  have h := isHomLift_homAlpha φ D
  rwa [← Functor.congr_obj
    (overMap_comp_eq_of_comp_hom φ.f.left (hom_f_left_comp φ)) P.coverOver] at h

/-! #### Compatibility with the identification of the quintuple -/

/-- **The transported identifications recover the identification of the source quintuple.** -/
theorem homAlpha_comp :
    (homAlpha φ D).inv ≫ (homPoint φ D).map P.coverToBase ≫ homUnit φ D = P.α := by
  refine (Iso.inv_comp_eq (homAlpha φ D)).mpr ?_
  have hmap : 𝒴.toBasedCategory.p.IsHomLift P.q ((homPoint φ D).map P.coverToBase) :=
    PresheafOfCategories.isHomLift_map_of_comp (homPoint_comp φ D) P.q P.coverToBase
      (isHomLift_coverToBase P)
  have hL : 𝒴.toBasedCategory.p.IsHomLift P.q
      ((homPoint φ D).map P.coverToBase ≫ homUnit φ D) :=
    have := hmap
    IsHomLift.comp_lift_id_right' 𝒴.toBasedCategory.p P.q
      ((homPoint φ D).map P.coverToBase) P.U (homUnit φ D)
  have hvert : 𝒴.toBasedCategory.p.IsHomLift (𝟙 P.Z) (homAlpha φ D).hom :=
    isHomLift_homAlphaHom φ D
  have hR : 𝒴.toBasedCategory.p.IsHomLift P.q ((homAlpha φ D).hom ≫ P.α) :=
    have := hvert
    have := P.α_over
    IsHomLift.comp_lift_id_left' 𝒴.toBasedCategory.p P.Z (homAlpha φ D).hom P.q P.α
  have := hL
  have := hR
  refine Functor.IsStronglyCartesian.ext 𝒴.toBasedCategory.p φ.f φ.b P.q ?_
  have hQα : D.α.hom ≫ Q.α = D.y.map Q.coverToBase ≫ D.yUnit := by
    rw [← D.α_comp, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  show (D.y.map ((Over.map φ.f.left).map P.coverToBase) ≫ homUnit φ D) ≫ φ.b = _
  rw [Category.assoc, homUnit_comp, ← D.y.map_comp_assoc, coverComparison_comp_coverToBase,
    D.y.map_comp_assoc, ← hQα, reassoc_of% homAlpha_square, φ.compatible, Category.assoc]

/-! #### The transport -/

/-- **The transport of a set of data exhibiting the relative map along a morphism of
quintuples.** The point is restricted along the base component of the morphism, the representing
algebraic space is restricted along the same morphism — which it remains, by part (1) of
Stacks 03I5 — and the two comparison morphisms are produced by the universal property of the
components of the morphism. -/
noncomputable def ofHom : RelativeMapData P where
  y := homPoint φ D
  y_comp := homPoint_comp φ D
  yUnit := homUnit φ D
  yUnit_over := isHomLift_homUnit φ D
  Xy := (OverShriek.relocalizeRestrict φ.f.left).obj D.Xy
  isAlgebraicSpace := isAlgebraicSpace_relocalizeRestrict B P.U.left.1 Q.U.left.1 P.U.left.2
    Q.U.left.2 φ.f.left D.Xy D.isAlgebraicSpace
  e := relativeSpaceRestrictEquivalence F D.y D.e φ.f.left (hom_f_left_comp φ)
    𝒳.isStackInGroupoids.isFiberedInGroupoids 𝒴.isStackInGroupoids.isFiberedInGroupoids D.y_comp
  α := homAlpha φ D
  α_over := isHomLift_homAlpha φ D
  α_comp := homAlpha_comp φ D

/-! ### The relative map of the transported data -/

/-- **The comparison of the representable presheaf of the cover of the source quintuple with the
restriction of the representable presheaf of the cover of the target is an isomorphism.** -/
theorem isIso_restrictYonedaHom_coverComparison :
    IsIso (OverShriek.restrictYonedaHom φ.f.left (coverComparison φ)) :=
  OverShriek.isIso_restrictYonedaHom_of_isPullback φ.f.left (coverComparison φ)
    (IsPullback.map (Over.forget (B.obj hS)) φ.square)

/-- The relative map of the transported data is the restriction of the original relative map
along the base component of the morphism, read through the comparison of the representable
presheaf of the cover of the source quintuple with the restriction of the representable presheaf
of the cover of the target — an isomorphism by
`AlgebraicGeometry.Stack.FiniteHilbert.RelativeMapData.isIso_restrictYonedaHom_coverComparison`,
so that the relative map of the source *is* the base change of the relative map of the target. -/
@[stacks 06CJ "the remark preceding the definition of the locus: the relative map of the source \
of a morphism of quintuples is the base change of the relative map of the target along the base \
component"]
theorem map_hom_ofHom :
    (ofHom φ D).map.hom =
      OverShriek.restrictYonedaHom φ.f.left (coverComparison φ) ≫
        (OverShriek.relocalizeRestrict φ.f.left).map D.map.hom := by
  refine OverShriek.restrictYonedaHom_comp_relocalizeRestrict_map φ.f.left
    (coverComparison φ) D.Xy (relativeSection F D.y D.e Q.coverOver Q.x
      Q.x_over_coverOver D.α D.α_over) _ ?_
  exact relativeSection_relocalizeRestrict_map F D.y D.e φ.f.left
    (hom_f_left_comp φ) 𝒳.isStackInGroupoids.isFiberedInGroupoids
    𝒴.isStackInGroupoids.isFiberedInGroupoids D.y_comp P.coverOver Q.coverOver
    (coverComparison φ) φ.a P.x_over_coverOver (x_over_cover φ) Q.x_over_coverOver
    (homAlpha φ D) (isHomLift_homAlpha φ D) (isHomLift_homAlpha' φ D) D.α D.α_over
    (isHomLift_hom_a φ) (homAlpha_square φ D)

end RelativeMapData

end FiniteHilbert

end AlgebraicGeometry.Stack

end
