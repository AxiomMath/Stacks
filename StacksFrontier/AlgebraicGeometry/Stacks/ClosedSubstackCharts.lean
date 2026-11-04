module

public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubstackIntersection
public import StacksFrontier.AlgebraicGeometry.Stacks.JointlySurjectiveSmoothEtaleLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiCompactPointRepresentative
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SubstackSchemeProperty
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange
import all StacksFrontier.AlgebraicGeometry.FormalSpace.ClosedImmersionDescent
import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# Closed substacks and closed subspaces of charts (Stacks 0507)

Let `𝒳` be an algebraic stack over `S` and let `P` be a property of the objects of `𝒳` inherited
along morphisms. This file reads `P` on the site of `S`: at an object `y` of `𝒳` over `U` it cuts
out the subfunctor `objSubfunctor` of `yoneda U` whose sections over `T` are the morphisms
`T ⟶ U` along which a restriction of `y` has `P`, and along a 1-morphism
`v : (Sch/V)_fppf ⟶ 𝒳` it cuts out the *chart subfunctor* of `yoneda V`. These are the two halves
of the correspondence of **Stacks 0507** between closed substacks of `𝒳` and closed subspaces of
charts, in the form the rest of the library consumes them.

## Main definitions

* `AlgebraicGeometry.Stack.pointSubfunctor`: the subfunctor of `yoneda W` read off a
  scheme-valued point with values in `W`.
* `AlgebraicGeometry.Stack.objSubfunctor`: the subfunctor of `yoneda U` read off an object of `𝒳`
  over `U`.
* `AlgebraicGeometry.Stack.chartSubfunctor`: the subfunctor of `yoneda V` read off a 1-morphism
  `(Sch/V)_fppf ⟶ 𝒳`.

## Main results

Each closed-substack statement below is the case `Q` = closed immersions of a statement at an
arbitrary property `Q` of morphisms of schemes (`AlgebraicGeometry.Space.IsSubspaceWith`,
`AlgebraicGeometry.Stack.IsSubstackWith`), which is proved here too:
`AlgebraicGeometry.Stack.isSubspaceWith_pointSubfunctor_iff`,
`AlgebraicGeometry.Stack.isSubspaceWith_chartSubfunctor`,
`AlgebraicGeometry.Stack.isSubspaceWith_objSubfunctor`,
`AlgebraicGeometry.Stack.isSubstackWith_of_forall_isSubspaceWith_objSubfunctor` and
`AlgebraicGeometry.Stack.isSubspaceWith_objSubfunctor_of_covering`.

* `AlgebraicGeometry.Stack.isClosedSubspace_pointSubfunctor_iff`: the base change of the full
  subcategory of `P` along a scheme-valued point is a closed subspace over the site of `W` exactly
  when `pointSubfunctor` is one over the site of `S`.
* `AlgebraicGeometry.Stack.isClosedSubspace_chartSubfunctor` and
  `AlgebraicGeometry.Stack.isClosedSubspace_objSubfunctor`: the chart subfunctors and
  `objSubfunctor` of a closed substack are closed subspaces.
* `AlgebraicGeometry.Stack.isClosedSubstack_of_isClosedSubspace_chartSubfunctor`: conversely, a
  property inherited along morphisms and local on the big fppf site whose chart subfunctors along
  a jointly surjective family of smooth charts are closed subspaces cuts out a closed substack.

## Implementation notes

The descent step is performed on the site of `S`, not on the site of a scheme-valued point: the
étale-local lifts of an object of `𝒳` along the charts
(`AlgebraicGeometry.Stack.exists_etaleCovering_family_fibre_lift`) generate a covering sieve of
the base, over each arrow of which `objSubfunctor` is an inverse image of a chart subfunctor, and
closed immersions descend along covering sieves
(`AlgebraicGeometry.FormalSpace.presheafIsClosedImmersion_of_coveringSieve`). The passage between
the two sites is the lower-shriek extension, through
`AlgebraicGeometry.Stack.isClosedSubspace_pointSubfunctor_iff`. No invariance condition on the
charts appears: it is the content of the locality of `P`, which the consumer proves.

## References

* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
* [Stacks Project, Tag 07AN](https://stacks.math.columbia.edu/tag/07AN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A subfunctor of a representable presheaf whose inclusion is representable by morphisms with `Q`
is a `Q`-subspace. -/
private theorem isSubspaceWith_of_presheaf_ι {Q : MorphismProperty Scheme.{u}}
    {U : BigFppfOver B S hS} {Z : Subfunctor (yoneda.obj U)}
    (h : (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf Z.ι) :
    Space.IsSubspaceWith B S hS Q Z :=
  ⟨isAlgebraicSpace_of_relativelyRepresentable B S hS _ h.rep
    (isAlgebraicSpace_yoneda _ _ _ _), h⟩

/-- The inverse image of a closed subspace of a representable presheaf along a morphism between
representables is a closed subspace. -/
private theorem isClosedSubspace_preimage_yoneda {U V : BigFppfOver B S hS}
    {Z : Subfunctor (yoneda.obj V)} (hZ : Space.IsClosedSubspace B S hS Z) (k : U ⟶ V) :
    Space.IsClosedSubspace B S hS (Z.preimage (yoneda.map k)) :=
  Space.isClosedSubspace_preimage B S hS _ _ (isAlgebraicSpace_yoneda _ _ _ _)
    (isAlgebraicSpace_yoneda _ _ _ _) hZ

section PointSubfunctor

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {P : ObjectProperty 𝒳.val.val.obj}
  (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a)
include hP

/-- The subfunctor of the representable presheaf of `W`, on the big fppf site of `S`, whose
sections over `T` are the morphisms `t : T ⟶ W` at which a property `P` inherited along morphisms
holds at the value of a scheme-valued point `z` of `𝒳` with values in `W`. -/
def pointSubfunctor {W : BigFppfOver B S hS}
    (z : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.val.obj) :
    Subfunctor (yoneda.obj W) where
  obj T := {t | P (z.obj (Over.mk t.left))}
  map {T T'} i t ht := by
    change P (z.obj (Over.mk (i.unop ≫ t).left))
    exact hP (z.map (Over.homMk i.unop.left rfl :
      (Over.mk (i.unop ≫ t).left : Over W.left) ⟶ Over.mk t.left)) ht

/-- A morphism `t : T ⟶ W` is a section of `pointSubfunctor` over `T` if and only if `P` holds at
the value of `z` at `t`. -/
theorem mem_pointSubfunctor_iff {W : BigFppfOver B S hS}
    (z : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.val.obj) {T : BigFppfOver B S hS}
    (t : T ⟶ W) : t ∈ (pointSubfunctor hP z).obj (op T) ↔ P (z.obj (Over.mk t.left)) :=
  Iff.rfl

/-- The lower-shriek extension to `S` of the base change of the full subcategory of `P` along a
scheme-valued point `z` with values in `W` has image `pointSubfunctor` in `yoneda W`. -/
theorem range_relocalizeToYoneda_fullSubcategoryBaseChangeSubfunctor {W : BigFppfOver B S hS}
    (z : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.val.obj) :
    Subfunctor.range (OverShriek.relocalizeToYoneda W.hom
      (fullSubcategoryBaseChangeSubfunctor 𝒳 hP z).toFunctor) = pointSubfunctor hP z := by
  ext T t
  constructor
  · rintro ⟨x, rfl⟩
    exact x.1.2.2
  · intro ht
    exact ⟨⟨⟨t.left, ⟨Over.homMk t.left, ht⟩⟩, Over.w t⟩, rfl⟩

/-- The lower-shriek extension to `S` of the base change of the full subcategory of `P` along a
scheme-valued point is a monomorphism into `yoneda W`: a section is determined by the morphism to
`W` it carries, the sections of the base change over an object forming a subsingleton. -/
theorem mono_relocalizeToYoneda_fullSubcategoryBaseChangeSubfunctor {W : BigFppfOver B S hS}
    (z : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.val.obj) :
    Mono (OverShriek.relocalizeToYoneda W.hom
      (fullSubcategoryBaseChangeSubfunctor 𝒳 hP z).toFunctor) := by
  rw [NatTrans.mono_iff_mono_app]
  intro T
  rw [mono_iff_injective]
  rintro ⟨⟨ψ, s⟩, h⟩ ⟨⟨ψ', s'⟩, h'⟩ hxx'
  obtain rfl : ψ = ψ' := congrArg (fun k : unop T ⟶ Over.mk W.hom => k.left) hxx'
  have := subsingleton_fullSubcategoryBaseChangeSubfunctor 𝒳 hP z (op (Over.mk ψ))
  obtain rfl : s = s' := Subsingleton.elim _ _
  rfl

/-- **The base change of a substack along a scheme-valued point is a `Q`-subspace exactly when
its reading on the site of `S` is.** The lower-shriek extension to `S` of the subfunctor of
`yoneda W` on the site of `W` representing the base change is identified with `pointSubfunctor`
by its structural morphism to `yoneda W`, a monomorphism with that image; and the lower-shriek
extension preserves and reflects representability by morphisms with `Q`. -/
theorem isSubspaceWith_pointSubfunctor_iff {Q : MorphismProperty Scheme.{u}} [Q.RespectsIso]
    {W : BigFppfOver B S hS}
    (z : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.val.obj) :
    Space.IsSubspaceWith B S hS Q (pointSubfunctor hP z) ↔
      Space.IsSubspaceWith B W.left.1 W.left.2 Q
        (fullSubcategoryBaseChangeSubfunctor 𝒳 hP z) := by
  set Z := fullSubcategoryBaseChangeSubfunctor 𝒳 hP z
  set r := OverShriek.relocalizeToYoneda W.hom Z.toFunctor
  have _ : Mono r := mono_relocalizeToYoneda_fullSubcategoryBaseChangeSubfunctor hP z
  have hrι : (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r ↔
      (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (pointSubfunctor hP z).ι := by
    rw [← range_relocalizeToYoneda_fullSubcategoryBaseChangeSubfunctor hP z,
      ← Space.inv_toRange_comp r]
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).symm
  have _ : IsIso (OverShriek.relocalizeToYoneda W.hom
      (yoneda.obj (Over.mk (𝟙 W.left)) : (BigFppfOver B W.left.1 W.left.2)ᵒᵖ ⥤ Type u)) :=
    isIso_relocalizeToYoneda_yonedaId B W.left.1 S W.left.2 hS W.hom
  have hΛ : (OverShriek.relocalizePresheafFunctor W.hom).map Z.ι ≫
      OverShriek.relocalizeToYoneda W.hom
        (yoneda.obj (Over.mk (𝟙 W.left)) : (BigFppfOver B W.left.1 W.left.2)ᵒᵖ ⥤ Type u) = r :=
    relocalizeToYoneda_naturality B W.left.1 S W.left.2 hS W.hom Z.ι
  constructor
  · intro h
    have h₁ := hrι.2 h.2
    rw [← hΛ] at h₁
    have h₂ := presheaf_relocalizeMap_of B W.left.1 S W.left.2 hS W.hom Q Z.ι
      ((MorphismProperty.cancel_right_of_respectsIso _ _ _).mp h₁)
    exact isSubspaceWith_of_presheaf_ι h₂
  · intro h
    have h₁ : (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
        ((OverShriek.relocalizePresheafFunctor W.hom).map Z.ι) :=
      OverShriek.presheaf_map_relocalize _ (fun _ hk => hk) h.2
    have h₂ : (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf r := by
      rw [← hΛ]
      exact (MorphismProperty.cancel_right_of_respectsIso _ _ _).mpr h₁
    have h₃ := hrι.1 h₂
    exact isSubspaceWith_of_presheaf_ι h₃

/-- **The base change of a substack along a scheme-valued point is a closed subspace exactly when
its reading on the site of `S` is.** This is
`AlgebraicGeometry.Stack.isSubspaceWith_pointSubfunctor_iff` at the closed immersions. -/
theorem isClosedSubspace_pointSubfunctor_iff {W : BigFppfOver B S hS}
    (z : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.val.obj) :
    Space.IsClosedSubspace B S hS (pointSubfunctor hP z) ↔
      Space.IsClosedSubspace B W.left.1 W.left.2
        (fullSubcategoryBaseChangeSubfunctor 𝒳 hP z) :=
  isSubspaceWith_pointSubfunctor_iff hP z

end PointSubfunctor

section Transport

variable {𝒞 𝒮 : Type*} [Category 𝒞] [Category 𝒮] {p : 𝒮 ⥤ 𝒞}

/-- **A property inherited along morphisms of a category fibred in groupoids is transported along
factorizations of base morphisms.** Let `φ : a ⟶ y` lie over `f` and `ψ : b ⟶ y` lie over `f'`,
and let `g` be a morphism of the base with `g ≫ f' = f`. If `P b` then `P a`: `ψ` is strongly
cartesian, so `φ` factors through it over `g`. -/
theorem prop_of_isHomLift_of_comp_eq (hp : p.IsFiberedInGroupoids) {P : ObjectProperty 𝒮}
    (hP : ∀ {a b : 𝒮}, (a ⟶ b) → P b → P a) {R R' U : 𝒞} {f : R ⟶ U} {f' : R' ⟶ U}
    (g : R ⟶ R') (hg : g ≫ f' = f) {a b y : 𝒮} (φ : a ⟶ y) (ψ : b ⟶ y) [p.IsHomLift f φ]
    [p.IsHomLift f' ψ] (hb : P b) : P a := by
  have := Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift hp f' ψ
  exact hP (Functor.IsStronglyCartesian.map p f' ψ hg.symm φ) hb

end Transport

section ObjSubfunctor

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {P : ObjectProperty 𝒳.val.val.obj}
  (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a)
include hP

/-- The subfunctor of the representable presheaf of `U`, on the big fppf site of `S`, cut out by a
property `P` of the objects of `𝒳` inherited along morphisms at an object `y` of `𝒳` over `U`:
its sections over `T` are the morphisms `t : T ⟶ U` along which a restriction of `y` has `P`. -/
def objSubfunctor {U : BigFppfOver B S hS} (y : 𝒳.val.val.p.Fiber U) :
    Subfunctor (yoneda.obj U) where
  obj T := {t | ∃ (ζ : 𝒳.val.val.obj) (α : ζ ⟶ y.1), 𝒳.val.val.p.IsHomLift t α ∧ P ζ}
  map {T T'} i t := by
    rintro ⟨ζ, α, hα, hζ⟩
    have hζT : 𝒳.val.val.p.obj ζ = T.unop := IsHomLift.domain_eq _ t α
    obtain ⟨ζ', β, hβ⟩ := 𝒳.val.isFiberedInGroupoids.exists_lift i.unop ζ hζT
    exact ⟨ζ', β ≫ α, IsHomLift.comp _ i.unop t β α, hP β hζ⟩

/-- Membership in `objSubfunctor` along a morphism `t` is `P` at any restriction of `y` along
`t`. -/
theorem mem_objSubfunctor_iff {U T : BigFppfOver B S hS} (y : 𝒳.val.val.p.Fiber U) (t : T ⟶ U)
    {ζ : 𝒳.val.val.obj} (α : ζ ⟶ y.1) [𝒳.val.val.p.IsHomLift t α] :
    t ∈ (objSubfunctor hP y).obj (op T) ↔ P ζ := by
  refine ⟨?_, fun h => ⟨ζ, α, inferInstance, h⟩⟩
  rintro ⟨ζ', α', hα', hζ'⟩
  exact prop_of_isHomLift_of_comp_eq 𝒳.val.isFiberedInGroupoids hP (𝟙 T)
    (Category.id_comp t) α α' hζ'

/-- `objSubfunctor` is transported along morphisms of `𝒳`: its inverse image along the base
morphism `k` of a morphism `y' ⟶ y` is `objSubfunctor` at `y'`. -/
theorem objSubfunctor_preimage {U U' : BigFppfOver B S hS} (y : 𝒳.val.val.p.Fiber U)
    (y' : 𝒳.val.val.p.Fiber U') (k : U' ⟶ U) (α : y'.1 ⟶ y.1) (hα : 𝒳.val.val.p.IsHomLift k α) :
    (objSubfunctor hP y).preimage (yoneda.map k) = objSubfunctor hP y' := by
  ext T t
  show t ≫ k ∈ (objSubfunctor hP y).obj T ↔ t ∈ (objSubfunctor hP y').obj T
  obtain ⟨ζ, β, hβ⟩ := 𝒳.val.isFiberedInGroupoids.exists_lift t y'.1 y'.2
  rw [mem_objSubfunctor_iff hP y' t β, mem_objSubfunctor_iff hP y (t ≫ k) (β ≫ α)]

/-- A property inherited along morphisms holds at an object `y` over `U` exactly when the
identity of `U` lies in `objSubfunctor` at `y`. -/
theorem id_mem_objSubfunctor_iff {U : BigFppfOver B S hS} (y : 𝒳.val.val.p.Fiber U) :
    𝟙 U ∈ (objSubfunctor hP y).obj (op U) ↔ P y.1 := by
  obtain ⟨y, rfl⟩ := y
  exact mem_objSubfunctor_iff hP ⟨y, rfl⟩ (𝟙 _) (𝟙 y)

omit hP in
/-- The value at the terminal object of a scheme-valued point with values in `W` lies over
`W`. -/
theorem obj_mkId_eq {W : BigFppfOver B S hS}
    {z : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.val.obj}
    (hz : z ⋙ 𝒳.val.val.p = Over.map W.hom) :
    𝒳.val.val.p.obj (z.obj (Over.mk (𝟙 W.left))) = W := by
  rw [← Functor.comp_obj, hz]
  exact (congrArg Over.mk (Category.id_comp W.hom)).trans rfl

omit hP in
/-- The value of a scheme-valued point at a morphism `t : T ⟶ W` maps to its value at the
terminal object over `t`. -/
theorem isHomLift_map_homMk {W : BigFppfOver B S hS}
    {z : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.val.obj}
    (hz : z ⋙ 𝒳.val.val.p = Over.map W.hom) {T : BigFppfOver B S hS} (t : T ⟶ W) :
    𝒳.val.val.p.IsHomLift t (z.map (Over.homMk t.left (Category.comp_id _) :
      (Over.mk t.left : Over W.left) ⟶ Over.mk (𝟙 W.left))) := by
  set g : (Over.mk t.left : Over W.left) ⟶ Over.mk (𝟙 W.left) :=
    Over.homMk t.left (Category.comp_id _)
  have h₀ : 𝒳.val.val.p.IsHomLift ((Over.map W.hom).map g) (z.map g) :=
    Functor.isHomLift_map_of_comp_eq hz _ g
  have h₁ : T = (Over.map W.hom).obj (Over.mk t.left) :=
    (congrArg Over.mk (Over.w t).symm).trans rfl
  have h₂ : (Over.map W.hom).obj (Over.mk (𝟙 W.left)) = W :=
    (congrArg Over.mk (Category.id_comp W.hom)).trans rfl
  have ht : t = eqToHom h₁ ≫ (Over.map W.hom).map g ≫ eqToHom h₂ :=
    Over.OverMorphism.ext (by simp [g])
  have key : 𝒳.val.val.p.IsHomLift (eqToHom h₁ ≫ (Over.map W.hom).map g ≫ eqToHom h₂)
      (z.map g) := inferInstance
  exact (congrArg (fun f : T ⟶ W => 𝒳.val.val.p.IsHomLift f (z.map g)) ht).mpr key

/-- The subfunctor read off a scheme-valued point `z` with values in `W` is `objSubfunctor` at the
value of `z` at the terminal object. -/
theorem pointSubfunctor_eq_objSubfunctor {W : BigFppfOver B S hS}
    {z : BigFppfOver B W.left.1 W.left.2 ⥤ 𝒳.val.val.obj}
    (hz : z ⋙ 𝒳.val.val.p = Over.map W.hom) :
    pointSubfunctor hP z = objSubfunctor hP ⟨z.obj (Over.mk (𝟙 W.left)), obj_mkId_eq hz⟩ := by
  ext T t
  have := isHomLift_map_homMk hz t
  exact (mem_objSubfunctor_iff hP _ t (z.map (Over.homMk t.left (Category.comp_id _) :
    (Over.mk t.left : Over W.left) ⟶ Over.mk (𝟙 W.left)))).symm

end ObjSubfunctor

section ChartSubfunctor

/-- The image under `v` of the structure morphism `x ⟶ Over.mk (𝟙 V)` of an object `x` of
`(Sch/V)_fppf` lies over `x.hom`. -/
private theorem isHomLift_map_homMk_chart {𝒳 : AlgebraicStacks.{u, w} B S hS}
    {V : BigFppfOver B S hS} (v : schemeStack.{u, w} B S hS V ⟶ 𝒳) (x : Over V) :
    𝒳.val.val.p.IsHomLift x.hom (v.hom.hom.map
      (Over.homMk x.hom (Category.comp_id _) : x ⟶ Over.mk (𝟙 V))) := by
  let g : x ⟶ Over.mk (𝟙 V) := Over.homMk x.hom (Category.comp_id _)
  have : (schemeStack.{u, w} B S hS V).val.val.p.IsHomLift x.hom g :=
    (inferInstance : (Over.forget V).IsHomLift ((Over.forget V).map g) g)
  exact Functor.isHomLift_map_of_comp_eq v.hom.hom.w x.hom g

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {P : ObjectProperty 𝒳.val.val.obj}
  (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a)
include hP

/-- The subfunctor of the representable presheaf of `V`, on the big fppf site of `S`, cut out by a
property `P` of the objects of `𝒳` inherited along morphisms, along a 1-morphism
`v : (Sch/V)_fppf ⟶ 𝒳`: its sections over `T` are the morphisms `s : T ⟶ V` such that `P` holds
at the image under `v` of the object `s` of `(Sch/V)_fppf`. -/
def chartSubfunctor {V : BigFppfOver B S hS} (v : schemeStack.{u, w} B S hS V ⟶ 𝒳) :
    Subfunctor (yoneda.obj V) where
  obj T := {s | P (v.hom.hom.obj (Over.mk s))}
  map {T T'} i s hs := by
    change P (v.hom.hom.obj (Over.mk (i.unop ≫ s)))
    exact hP (v.hom.hom.map (Over.homMk i.unop rfl :
      (Over.mk (i.unop ≫ s) : Over V) ⟶ Over.mk s)) hs

/-- A morphism `s : T ⟶ V` is a section of `chartSubfunctor` over `T` if and only if `P` holds at
the image under `v` of the object `s` of `(Sch/V)_fppf`. -/
theorem mem_chartSubfunctor_iff {V : BigFppfOver B S hS} (v : schemeStack.{u, w} B S hS V ⟶ 𝒳)
    {T : BigFppfOver B S hS} (s : T ⟶ V) :
    s ∈ (chartSubfunctor hP v).obj (op T) ↔ P (v.hom.hom.obj (Over.mk s)) :=
  Iff.rfl

/-- The scheme-valued point of `𝒳` with values in `V` attached to a 1-morphism
`(Sch/V)_fppf ⟶ 𝒳`: the 1-morphism read on the big fppf site of `V` through the iterated slice
equivalence. -/
abbrev chartSchemePoint {V : BigFppfOver B S hS} (v : schemeStack.{u, w} B S hS V ⟶ 𝒳) :
    BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.val.obj :=
  V.iteratedSliceBackward ⋙ v.hom.hom.toFunctor

omit hP in
/-- The scheme-valued point `chartSchemePoint v`, followed by the structure functor of `𝒳`, is
postcomposition with the structure morphism `V ⟶ S`. -/
theorem chartSchemePoint_comp {V : BigFppfOver B S hS} (v : schemeStack.{u, w} B S hS V ⟶ 𝒳) :
    chartSchemePoint v ⋙ 𝒳.val.val.p = Over.map V.hom :=
  congrArg (V.iteratedSliceBackward ⋙ ·) v.hom.hom.w

/-- The chart subfunctor of a 1-morphism out of `(Sch/V)_fppf` is the subfunctor of `yoneda V`
read off the scheme-valued point it names. -/
theorem chartSubfunctor_eq_pointSubfunctor {V : BigFppfOver B S hS}
    (v : schemeStack.{u, w} B S hS V ⟶ 𝒳) :
    chartSubfunctor hP v = pointSubfunctor hP (chartSchemePoint v) := by
  ext T t
  let e : (Over.mk t : Over V) ≅ V.iteratedSliceBackward.obj (Over.mk t.left) :=
    Over.isoMk (Over.isoMk (Iso.refl _) ((Category.id_comp _).trans (Over.w t)))
      (Over.OverMorphism.ext (Category.id_comp _))
  exact ⟨fun h => hP (v.hom.hom.map e.inv) h, fun h => hP (v.hom.hom.map e.hom) h⟩

/-- The chart subfunctor of a `Q`-substack along any 1-morphism `(Sch/V)_fppf ⟶ 𝒳` is a
`Q`-subspace of `V`. -/
theorem isSubspaceWith_chartSubfunctor {Q : MorphismProperty Scheme.{u}} [Q.RespectsIso]
    (hPQ : IsSubstackWith Q 𝒳 P) {V : BigFppfOver B S hS}
    (v : schemeStack.{u, w} B S hS V ⟶ 𝒳) :
    Space.IsSubspaceWith B S hS Q (chartSubfunctor hP v) := by
  rw [chartSubfunctor_eq_pointSubfunctor, isSubspaceWith_pointSubfunctor_iff]
  exact isSubspaceWith_fullSubcategoryBaseChangeSubfunctor hPQ V (chartSchemePoint v)
    (chartSchemePoint_comp v)

/-- **Stacks 0507**, from closed substacks to closed subspaces of a chart: the chart subfunctor of
a closed substack along any 1-morphism `(Sch/V)_fppf ⟶ 𝒳` is a closed subspace of `V`. -/
theorem isClosedSubspace_chartSubfunctor (hPc : IsClosedSubstack 𝒳 P) {V : BigFppfOver B S hS}
    (v : schemeStack.{u, w} B S hS V ⟶ 𝒳) :
    Space.IsClosedSubspace B S hS (chartSubfunctor hP v) :=
  isSubspaceWith_chartSubfunctor hP hPc v

/-- The chart subfunctor of a 1-morphism out of `(Sch/V)_fppf` is `objSubfunctor` at the image of
the terminal object of `(Sch/V)_fppf`. -/
theorem chartSubfunctor_eq_objSubfunctor {V : BigFppfOver B S hS}
    (v : schemeStack.{u, w} B S hS V ⟶ 𝒳) :
    chartSubfunctor hP v =
      objSubfunctor hP ⟨v.hom.hom.obj (Over.mk (𝟙 V)), v.hom.hom.w_obj (Over.mk (𝟙 V))⟩ := by
  ext T s
  let g : (Over.mk s : Over V) ⟶ Over.mk (𝟙 V) := Over.homMk s (Category.comp_id s)
  have : 𝒳.val.val.p.IsHomLift s (v.hom.hom.map g) := isHomLift_map_homMk_chart v (Over.mk s)
  exact (mem_objSubfunctor_iff hP _ s (v.hom.hom.map g)).symm

/-- The chart subfunctor of the composite of the 1-morphism induced by a morphism `q` of the site
with `v` is the inverse image along `q` of the chart subfunctor of `v`. -/
theorem chartSubfunctor_schemeStackMap_comp {E V : BigFppfOver B S hS} (q : E ⟶ V)
    (v : schemeStack.{u, w} B S hS V ⟶ 𝒳) :
    chartSubfunctor hP (schemeStackMap.{u, w} B S hS q ≫ v) =
      (chartSubfunctor hP v).preimage (yoneda.map q) :=
  rfl

/-- The chart subfunctor is unchanged by a 2-isomorphism of 1-morphisms. -/
theorem chartSubfunctor_congr {V : BigFppfOver B S hS}
    {v v' : schemeStack.{u, w} B S hS V ⟶ 𝒳} (e : v ≅ v') :
    chartSubfunctor hP v = chartSubfunctor hP v' := by
  ext T s
  exact ⟨fun h => hP ((CatFiberedInGroupoids.underlyingIso
      (algebraicStacksTwoIsoHom B S hS e)).inv.app (Over.mk s)) h,
    fun h => hP ((CatFiberedInGroupoids.underlyingIso
      (algebraicStacksTwoIsoHom B S hS e)).hom.app (Over.mk s)) h⟩

end ChartSubfunctor

section Criterion

variable {𝒳 : AlgebraicStacks.{u, w} B S hS} {P : ObjectProperty 𝒳.val.val.obj}
  (hP : ∀ {a b : 𝒳.val.val.obj}, (a ⟶ b) → P b → P a)
include hP

/-- **The subfunctors cut out by a `Q`-substack are `Q`-subspaces**: `objSubfunctor` of a
`Q`-substack at any object of `𝒳` is a `Q`-subspace. The object names a 1-morphism out of
`(Sch/U)_fppf` by the 2-Yoneda lemma, whose chart subfunctor is a `Q`-subspace by
`AlgebraicGeometry.Stack.isSubspaceWith_chartSubfunctor`. -/
theorem isSubspaceWith_objSubfunctor {Q : MorphismProperty Scheme.{u}} [Q.RespectsIso]
    (hPQ : IsSubstackWith Q 𝒳 P) {U : BigFppfOver B S hS}
    (y : 𝒳.val.val.p.Fiber U) :
    Space.IsSubspaceWith B S hS Q (objSubfunctor hP y) := by
  let L := Functor.TwoYoneda.chosenLift 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids U y
    (Over.mk (𝟙 U))
  have hL : 𝒳.val.val.p.IsHomLift (𝟙 U) L.φ := L.isStronglyCartesian.toIsHomLift
  have h := isSubspaceWith_chartSubfunctor hP hPQ (fibreObjectStackMap B S hS 𝒳 U y)
  rw [chartSubfunctor_eq_objSubfunctor] at h
  have e := objSubfunctor_preimage hP y ⟨L.y, IsHomLift.domain_eq _ (𝟙 U) L.φ⟩ (𝟙 U) L.φ hL
  rw [CategoryTheory.Functor.map_id, Subfunctor.preimage_id] at e
  rw [e]
  exact h

/-- **A property whose subfunctors are all `Q`-subspaces cuts out a `Q`-substack**: a property of
the objects of `𝒳` inherited along morphisms cuts out a `Q`-substack as soon as its
`objSubfunctor` at every object of `𝒳` is a `Q`-subspace. -/
theorem isSubstackWith_of_forall_isSubspaceWith_objSubfunctor {Q : MorphismProperty Scheme.{u}}
    [Q.RespectsIso]
    (h : ∀ (U : BigFppfOver B S hS) (y : 𝒳.val.val.p.Fiber U),
      Space.IsSubspaceWith B S hS Q (objSubfunctor hP y)) :
    IsSubstackWith Q 𝒳 P :=
  isSubstackWith_of_forall_isSubspaceWith 𝒳 hP fun W z hz => by
    rw [← isSubspaceWith_pointSubfunctor_iff, pointSubfunctor_eq_objSubfunctor hP hz]
    exact h _ _

/-- **Being a `Q`-subspace is local on the base for `objSubfunctor`.** If `objSubfunctor` at `y`
is a sheaf and its inverse images along the arrows of a covering sieve of `U` are `Q`-subspaces,
then it is a `Q`-subspace of `U`, as soon as morphisms with `Q` descend effectively along covering
sieves (`AlgebraicGeometry.Space.presheaf_of_coveringSieve`). -/
theorem isSubspaceWith_objSubfunctor_of_covering {Q : MorphismProperty Scheme.{u}}
    (hdesc : Space.IsEffectiveDescentAlongCoveringSieve B S hS Q) {U : BigFppfOver B S hS}
    (y : 𝒳.val.val.p.Fiber U)
    (hsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (objSubfunctor hP y).toFunctor)
    {R : Sieve U} (hR : R ∈ BigFppfOver.topology B S hS U)
    (h : ∀ ⦃V : BigFppfOver B S hS⦄ (k : V ⟶ U), R k →
      Space.IsSubspaceWith B S hS Q ((objSubfunctor hP y).preimage (yoneda.map k))) :
    Space.IsSubspaceWith B S hS Q (objSubfunctor hP y) := by
  set Z := objSubfunctor hP y
  have hQ : (Q.inverseImage (BigFppfOver.toScheme B S hS)).presheaf Z.ι := by
    refine Space.presheaf_of_coveringSieve hdesc hsh Z.ι hR fun V k hk => ?_
    have hsq := Subfunctor.isPullback_preimage (yoneda.map k) Z
    rw [← hsq.isoIsPullback_inv_snd _ _ (IsPullback.of_hasPullback Z.ι (yoneda.map k))]
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr (h k hk).2
  exact isSubspaceWith_of_presheaf_ι hQ

/-- **Stacks 0507**, from closed substacks to closed subspaces: `objSubfunctor` of a closed
substack at any object of `𝒳` is a closed subspace. -/
theorem isClosedSubspace_objSubfunctor (hPc : IsClosedSubstack 𝒳 P) {U : BigFppfOver B S hS}
    (y : 𝒳.val.val.p.Fiber U) :
    Space.IsClosedSubspace B S hS (objSubfunctor hP y) :=
  isSubspaceWith_objSubfunctor hP hPc y

/-- **Stacks 0507**, from closed subspaces to closed substacks: a property of the objects of `𝒳`
inherited along morphisms cuts out a closed substack as soon as its `objSubfunctor` at every
object of `𝒳` is a closed subspace. -/
theorem isClosedSubstack_of_forall_isClosedSubspace_objSubfunctor
    (h : ∀ (U : BigFppfOver B S hS) (y : 𝒳.val.val.p.Fiber U),
      Space.IsClosedSubspace B S hS (objSubfunctor hP y)) :
    IsClosedSubstack 𝒳 P :=
  isSubstackWith_of_forall_isSubspaceWith_objSubfunctor hP h

/-- **Closedness of `objSubfunctor` is local on the base.** If `objSubfunctor` at `y` is a sheaf
and its inverse images along the arrows of a covering sieve of `U` are closed subspaces, then it
is a closed subspace of `U`: closed immersions descend along covering sieves of the big fppf
site (`AlgebraicGeometry.FormalSpace.isEffectiveDescentAlongCoveringSieve_isClosedImmersion`). -/
theorem isClosedSubspace_objSubfunctor_of_covering {U : BigFppfOver B S hS}
    (y : 𝒳.val.val.p.Fiber U)
    (hsh : Presheaf.IsSheaf (BigFppfOver.topology B S hS) (objSubfunctor hP y).toFunctor)
    {R : Sieve U} (hR : R ∈ BigFppfOver.topology B S hS U)
    (h : ∀ ⦃V : BigFppfOver B S hS⦄ (k : V ⟶ U), R k →
      Space.IsClosedSubspace B S hS ((objSubfunctor hP y).preimage (yoneda.map k))) :
    Space.IsClosedSubspace B S hS (objSubfunctor hP y) :=
  isSubspaceWith_objSubfunctor_of_covering hP
    (FormalSpace.isEffectiveDescentAlongCoveringSieve_isClosedImmersion B S hS) y hsh hR h

/-- `objSubfunctor` at the image under `v : (Sch/V)_fppf ⟶ 𝒳` of an object `x` of
`(Sch/V)_fppf` is the inverse image of the chart subfunctor of `v` along `x`. -/
theorem objSubfunctor_obj_eq {V : BigFppfOver B S hS} (v : schemeStack.{u, w} B S hS V ⟶ 𝒳)
    (x : Over V) {U : BigFppfOver B S hS} (hx : 𝒳.val.val.p.obj (v.hom.hom.obj x) = U) :
    objSubfunctor hP ⟨v.hom.hom.obj x, hx⟩ = (chartSubfunctor hP v).preimage
      (yoneda.map (eqToHom (hx.symm.trans (v.hom.hom.w_obj x)) ≫ x.hom)) := by
  have hU : U = x.left := hx.symm.trans (v.hom.hom.w_obj x)
  have h₁ := isHomLift_map_homMk_chart v x
  have h₂ : 𝒳.val.val.p.IsHomLift (eqToHom hU ≫ x.hom) (v.hom.hom.map
      (Over.homMk x.hom (Category.comp_id _) : x ⟶ Over.mk (𝟙 V))) := inferInstance
  rw [chartSubfunctor_eq_objSubfunctor]
  exact (objSubfunctor_preimage hP ⟨v.hom.hom.obj (Over.mk (𝟙 V)), v.hom.hom.w_obj _⟩
    ⟨v.hom.hom.obj x, hx⟩ (eqToHom hU ≫ x.hom) _ h₂).symm

/-- If the chart subfunctor of `v : (Sch/V)_fppf ⟶ 𝒳` is a closed subspace, then so is
`objSubfunctor` at the image under `v` of every object of `(Sch/V)_fppf`: the latter is an inverse
image of the former. -/
theorem isClosedSubspace_objSubfunctor_obj {V : BigFppfOver B S hS}
    (v : schemeStack.{u, w} B S hS V ⟶ 𝒳)
    (hcl : Space.IsClosedSubspace B S hS (chartSubfunctor hP v)) (x : Over V)
    {U : BigFppfOver B S hS} (hx : 𝒳.val.val.p.obj (v.hom.hom.obj x) = U) :
    Space.IsClosedSubspace B S hS (objSubfunctor hP ⟨v.hom.hom.obj x, hx⟩) := by
  rw [objSubfunctor_obj_eq]
  exact isClosedSubspace_preimage_yoneda hcl _

/-- **`objSubfunctor` is a sheaf when the property is local.** If a property inherited along
morphisms holds at an object as soon as it holds at its restrictions along the arrows of a
covering sieve, then `objSubfunctor` at every object is a sheaf for the big fppf topology. -/
theorem isSheaf_objSubfunctor
    (hloc : ∀ ⦃U : BigFppfOver B S hS⦄ (y : 𝒳.val.val.p.Fiber U) ⦃R : Sieve U⦄,
      R ∈ BigFppfOver.topology B S hS U →
      (∀ ⦃V : BigFppfOver B S hS⦄ (k : V ⟶ U), R k → k ∈ (objSubfunctor hP y).obj (op V)) →
      P y.1)
    {U : BigFppfOver B S hS} (y : 𝒳.val.val.p.Fiber U) :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (objSubfunctor hP y).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  refine (Subfunctor.isSheaf_iff _ ((isSheaf_iff_isSheaf_of_type _ _).1
    (BigFppfOver.isSheaf_yoneda_obj B S hS U))).2 fun T t ht => ?_
  obtain ⟨ζ, α, hα⟩ := 𝒳.val.isFiberedInGroupoids.exists_lift t y.1 y.2
  rw [mem_objSubfunctor_iff hP y t α]
  refine hloc ⟨ζ, IsHomLift.domain_eq _ t α⟩ ht fun V k hk => ?_
  rw [← objSubfunctor_preimage hP y ⟨ζ, IsHomLift.domain_eq _ t α⟩ t α hα]
  exact hk

/-- **Stacks 0507**, from invariant closed subspaces of charts to closed substacks. Let `P` be a
property of the objects of an algebraic stack `𝒳` over `S` which is inherited along morphisms and
local on the big fppf site, and let `v j : (Sch/V j)_fppf ⟶ 𝒳` be a family of smooth 1-morphisms
which is jointly surjective on points. If the chart subfunctor of `P` along every `v j` is a
closed subspace of `V j`, then `P` cuts out a closed substack of `𝒳`.

At an object `y` of `𝒳` over `U`, the family has étale-local lifts (the smooth analogue of
**Stacks 07AN**, `AlgebraicGeometry.Stack.exists_etaleCovering_family_fibre_lift`), over each of
which `objSubfunctor` at `y` is an inverse image of a chart subfunctor; closed immersions descend
along the covering sieve generated by the lifts. -/
theorem isClosedSubstack_of_isClosedSubspace_chartSubfunctor
    (hloc : ∀ ⦃U : BigFppfOver B S hS⦄ (y : 𝒳.val.val.p.Fiber U) ⦃R : Sieve U⦄,
      R ∈ BigFppfOver.topology B S hS U →
      (∀ ⦃V : BigFppfOver B S hS⦄ (k : V ⟶ U), R k → k ∈ (objSubfunctor hP y).obj (op V)) →
      P y.1)
    {J : Type*} {V : J → BigFppfOver B S hS} (v : ∀ j, schemeStack.{u, w} B S hS (V j) ⟶ 𝒳)
    (hsm : ∀ j, AlgebraicStacks.IsSmooth B S hS (v j))
    (hjs : (Set.univ : Set (AlgebraicStacks.points B S hS 𝒳)) =
      ⋃ j, Set.range (AlgebraicStacks.pointsMap B S hS (v j)))
    (hcl : ∀ j, Space.IsClosedSubspace B S hS (chartSubfunctor hP (v j))) :
    IsClosedSubstack 𝒳 P := by
  refine isClosedSubstack_of_forall_isClosedSubspace_objSubfunctor hP fun U y => ?_
  obtain ⟨I, W, e, a, het, hsurj, hlift⟩ :=
    exists_etaleCovering_family_fibre_lift B S hS v hsm hjs U y
  have hR := mem_topology_of_family B S hS W e (fun i => by have := het i; infer_instance)
    (fun i => by have := het i; infer_instance) hsurj
  refine isClosedSubspace_objSubfunctor_of_covering hP y (isSheaf_objSubfunctor hP hloc y) hR ?_
  rintro T k ⟨_, g, _, ⟨i⟩, rfl⟩
  obtain ⟨x, α, hα⟩ := hlift i
  set q : (Over.mk (e i ≫ U.hom) : BigFppfOver B S hS) ⟶ U := Over.homMk (e i) rfl
  have he := objSubfunctor_preimage hP y ⟨_, IsHomLift.domain_eq _ q α⟩ q α hα
  rw [CategoryTheory.Functor.map_comp, Subfunctor.preimage_comp]
  exact he ▸ isClosedSubspace_preimage_yoneda
    (isClosedSubspace_objSubfunctor_obj hP (v (a i)) (hcl _) x _) _

end Criterion

end AlgebraicGeometry.Stack

end
