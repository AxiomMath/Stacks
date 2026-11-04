module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.AlgebraicGeometry.Pushout.QuasiFiniteFunctoriality
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.Deformation.Artin.Infinitesimal.LiftClassSheaf

/-!
# The functor of isomorphism classes of infinitesimal lifts (Stacks 0DNS): the construction

For an algebraic stack `𝒳` over `S` and a deformation situation `(i : U ⟶ U', x)` of affine
objects of the big affine fppf site, this file constructs the functor
`F : B' ↦ {lifts of x|_{B' ⊗_{A'} A} to B'}/isomorphism` on `Over U'` of Stacks 0DNS, as an
inhabitant `Deformation.Artin.LiftClassSheaf.liftClassPresheaf` of
`Deformation.Artin.LiftClassSheaf.LiftClassPresheaf`.

## Main definitions and results

* `Deformation.Artin.LiftClassSheaf.Restriction.isPullback`: the square of a restriction of `x`
  is cartesian, since on global sections it is a pushout of rings of affine schemes.
* `Deformation.Artin.LiftClassSheaf.Restriction.canonical`: the restriction of `x` over every
  affine `A'`-algebra, through the fibre product `W ×_{U'} U` of the site.
* `Deformation.Artin.LiftClassSheaf.InfinitesimalLift.baseChange`: base change of a lift along a
  morphism of `Over U'`, between any two restrictions, and
  `Deformation.Artin.LiftClassSheaf.InfinitesimalLift.isRestrictionAlong_baseChange`.
* `Deformation.Artin.LiftClassSheaf.InfinitesimalLift.isomorphic_of_isRestrictionAlong`: base
  change respects isomorphism of lifts.
* `Deformation.Artin.LiftClassSheaf.liftClassPresheaf`: the functor `F` with its
  characterization.

## Implementation notes

The value of `F` at `W` is the quotient of the lifts over one chosen restriction of `x` over
`W`; a lift over any other restriction is moved to the chosen one by base change along the
identity of `W`. All the arrows of `𝒳` are strongly cartesian, `𝒳` being fibred in groupoids, so
base change of lifts is the cartesian factorization through chosen pullbacks.

## References

* [Stacks Project, Tag 0DNS](https://stacks.math.columbia.edu/tag/0DNS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace Deformation.Artin.LiftClassSheaf

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Stack.AlgebraicStacks.{u, w} B S hS}
  {U U' : BigAffineFppf B S hS} {i : U ⟶ U'} {x : 𝒳.val.val.obj}
  {hx : 𝒳.val.val.p.obj x = (BigAffineFppf.inclusion B S hS).obj U}

/-- The structure functor of an algebraic stack is fibred: it is fibred in groupoids. -/
instance isFibered_p : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered

/-- A lift of a morphism of the base is a lift of every equal morphism. -/
theorem isHomLift_of_eq' {V V' : BigFppfOver B S hS} {f f' : V ⟶ V'} (e : f = f')
    {a b : 𝒳.val.val.obj} (φ : a ⟶ b) [h : 𝒳.val.val.p.IsHomLift f φ] :
    𝒳.val.val.p.IsHomLift f' φ :=
  e ▸ h

/-- A square of the big affine fppf site is cartesian in the big fppf site as soon as its square of
schemes is. -/
theorem isPullback_inclusion_of_toScheme {P Q R T : BigAffineFppf B S hS} {p : P ⟶ Q}
    {q : P ⟶ R} {c : Q ⟶ T} {d : R ⟶ T}
    (h : IsPullback ((BigAffineFppf.toScheme B S hS).map p) ((BigAffineFppf.toScheme B S hS).map q)
      ((BigAffineFppf.toScheme B S hS).map c) ((BigAffineFppf.toScheme B S hS).map d)) :
    IsPullback ((BigAffineFppf.inclusion B S hS).map p) ((BigAffineFppf.inclusion B S hS).map q)
      ((BigAffineFppf.inclusion B S hS).map c) ((BigAffineFppf.inclusion B S hS).map d) := by
  have _ : ReflectsLimit (cospan ((BigAffineFppf.inclusion B S hS).map c)
      ((BigAffineFppf.inclusion B S hS).map d)) (BigFppfOver.toScheme B S hS) :=
    reflectsLimit_of_reflectsIsomorphisms _ _
  exact IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) h

/-- The chosen pullbacks of `𝒳` are strongly cartesian. -/
theorem isStronglyCartesian_pullbackMap {V V' : BigFppfOver B S hS} {a : 𝒳.val.val.obj}
    (ha : 𝒳.val.val.p.obj a = V') (f : V ⟶ V') :
    𝒳.val.val.p.IsStronglyCartesian f (IsPreFibered.pullbackMap ha f) :=
  have : 𝒳.val.val.p.IsCartesian f (IsPreFibered.pullbackMap ha f) :=
    IsPreFibered.pullbackMap.IsCartesian ha f
  𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift f _

namespace Restriction

variable {W : Over U'} (r : Restriction B S hS 𝒳 i x hx W)

/-- **The square of a restriction is cartesian**: `Spec (B' ⊗_{A'} A) = Spec B' ×_{Spec A'} Spec A`
in the big fppf site, since on global sections the square is a pushout. -/
theorem isPullback :
    IsPullback ((BigAffineFppf.inclusion B S hS).map r.toDef)
      ((BigAffineFppf.inclusion B S hS).map r.toCover)
      ((BigAffineFppf.inclusion B S hS).map i) ((BigAffineFppf.inclusion B S hS).map W.hom) :=
  isPullback_inclusion_of_toScheme (isPullback_of_isPushout_appTop r.isPushout)

/-- The morphism into the base of a restriction induced by a commutative square. -/
def lift {V : BigAffineFppf B S hS} (t : V ⟶ U) (s : V ⟶ W.left) (h : t ≫ i = s ≫ W.hom) :
    V ⟶ r.base :=
  (BigAffineFppf.inclusion B S hS).preimage
    (r.isPullback.lift ((BigAffineFppf.inclusion B S hS).map t)
      ((BigAffineFppf.inclusion B S hS).map s) (by rw [← Functor.map_comp, ← Functor.map_comp, h]))

/-- The morphism `lift t s h` followed by the projection to `U` is `t`. -/
@[reassoc (attr := simp)]
theorem lift_toDef {V : BigAffineFppf B S hS} (t : V ⟶ U) (s : V ⟶ W.left)
    (h : t ≫ i = s ≫ W.hom) : r.lift t s h ≫ r.toDef = t :=
  (BigAffineFppf.inclusion B S hS).map_injective
    (by simp only [lift, Functor.map_comp, Functor.map_preimage, IsPullback.lift_fst])

/-- The morphism `lift t s h` followed by the projection to `W` is `s`. -/
@[reassoc (attr := simp)]
theorem lift_toCover {V : BigAffineFppf B S hS} (t : V ⟶ U) (s : V ⟶ W.left)
    (h : t ≫ i = s ≫ W.hom) : r.lift t s h ≫ r.toCover = s :=
  (BigAffineFppf.inclusion B S hS).map_injective
    (by simp only [lift, Functor.map_comp, Functor.map_preimage, IsPullback.lift_snd])

/-- Two morphisms into the base of a restriction agreeing after both projections are equal. -/
theorem hom_ext {V : BigAffineFppf B S hS} {b b' : V ⟶ r.base} (h₁ : b ≫ r.toDef = b' ≫ r.toDef)
    (h₂ : b ≫ r.toCover = b' ≫ r.toCover) : b = b' :=
  (BigAffineFppf.inclusion B S hS).map_injective
    (r.isPullback.hom_ext (by rw [← Functor.map_comp, ← Functor.map_comp, h₁])
      (by rw [← Functor.map_comp, ← Functor.map_comp, h₂]))

/-- The arrow of a restriction to `x` is strongly cartesian, as an instance. -/
instance isStronglyCartesian_hom :
    𝒳.val.val.p.IsStronglyCartesian ((BigAffineFppf.inclusion B S hS).map r.toDef) r.hom :=
  r.isCartesian

variable (B S hS 𝒳 i x hx) in
/-- The restriction of `x` over an affine `A'`-algebra `W`, through the fibre product
`U ×_{U'} W` of the big affine fppf site and the chosen pullback of `x` along its projection to
`U`. -/
def canonical (W : Over U') : Restriction B S hS 𝒳 i x hx W where
  base := pullback i W.hom
  toCover := pullback.snd i W.hom
  toDef := pullback.fst i W.hom
  comm := pullback.condition
  isPushout := isPushout_appTop_of_isPullback
    (IsPullback.map (BigAffineFppf.toScheme B S hS) (IsPullback.of_hasPullback i W.hom))
  obj := IsPreFibered.pullbackObj hx ((BigAffineFppf.inclusion B S hS).map (pullback.fst i W.hom))
  hom := IsPreFibered.pullbackMap hx ((BigAffineFppf.inclusion B S hS).map (pullback.fst i W.hom))
  isCartesian := isStronglyCartesian_pullbackMap _ _

end Restriction

namespace InfinitesimalLift

variable {W W₁ W₂ W₃ : Over U'}

/-- The arrow of a lift from its restriction is strongly cartesian, as an instance. -/
instance isStronglyCartesian_hom {r : Restriction B S hS 𝒳 i x hx W}
    (l : InfinitesimalLift B S hS 𝒳 i x hx r) :
    𝒳.val.val.p.IsStronglyCartesian ((BigAffineFppf.inclusion B S hS).map r.toCover) l.hom :=
  l.isCartesian

/-- The lifted object of a lift lies over `W`. -/
theorem obj_proj {r : Restriction B S hS 𝒳 i x hx W} (l : InfinitesimalLift B S hS 𝒳 i x hx r) :
    𝒳.val.val.p.obj l.obj = (BigAffineFppf.inclusion B S hS).obj W.left :=
  IsHomLift.codomain_eq 𝒳.val.val.p ((BigAffineFppf.inclusion B S hS).map r.toCover) l.hom

/-! ### Isomorphism of lifts is an equivalence relation -/

/-- Every lift is isomorphic to itself. -/
theorem Isomorphic.refl {r : Restriction B S hS 𝒳 i x hx W}
    (l : InfinitesimalLift B S hS 𝒳 i x hx r) :
    Isomorphic B S hS 𝒳 i x hx l l :=
  ⟨𝟙 _, inferInstance, IsHomLift.id (obj_proj l), Category.comp_id _⟩

/-- Isomorphism of lifts is symmetric. -/
theorem Isomorphic.symm {r : Restriction B S hS 𝒳 i x hx W}
    {l m : InfinitesimalLift B S hS 𝒳 i x hx r} (h : Isomorphic B S hS 𝒳 i x hx l m) :
    Isomorphic B S hS 𝒳 i x hx m l := by
  obtain ⟨φ, hφ, hφl, hw⟩ := h
  exact ⟨inv φ, inferInstance, inferInstance, by rw [← hw, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]⟩

/-- Isomorphism of lifts is transitive. -/
theorem Isomorphic.trans {r : Restriction B S hS 𝒳 i x hx W}
    {l m n : InfinitesimalLift B S hS 𝒳 i x hx r} (h : Isomorphic B S hS 𝒳 i x hx l m)
    (h' : Isomorphic B S hS 𝒳 i x hx m n) : Isomorphic B S hS 𝒳 i x hx l n := by
  obtain ⟨φ, hφ, hφl, hw⟩ := h
  obtain ⟨φ', hφ', hφl', hw'⟩ := h'
  exact ⟨φ ≫ φ', inferInstance, inferInstance, by rw [← Category.assoc, hw, hw']⟩

/-- The setoid of isomorphism of lifts. -/
def setoid (r : Restriction B S hS 𝒳 i x hx W) : Setoid (InfinitesimalLift B S hS 𝒳 i x hx r) where
  r := Isomorphic B S hS 𝒳 i x hx
  iseqv := ⟨Isomorphic.refl, Isomorphic.symm, Isomorphic.trans⟩

/-! ### Base change of lifts -/

/-- The morphism `Spec (B'₂ ⊗_{A'} A) ⟶ Spec (B'₁ ⊗_{A'} A)` of the bases of two restrictions
induced by `g : W₂ ⟶ W₁`. -/
def baseMap (r₁ : Restriction B S hS 𝒳 i x hx W₁) (r₂ : Restriction B S hS 𝒳 i x hx W₂)
    (g : W₂ ⟶ W₁) : r₂.base ⟶ r₁.base :=
  r₁.lift r₂.toDef (r₂.toCover ≫ g.left) (by rw [r₂.comm, Category.assoc, Over.w g])

/-- The morphism `baseMap r₁ r₂ g` commutes with the projections to `U`. -/
@[reassoc (attr := simp)]
theorem baseMap_toDef (r₁ : Restriction B S hS 𝒳 i x hx W₁)
    (r₂ : Restriction B S hS 𝒳 i x hx W₂) (g : W₂ ⟶ W₁) :
    baseMap r₁ r₂ g ≫ r₁.toDef = r₂.toDef :=
  r₁.lift_toDef _ _ _

/-- The morphism `baseMap r₁ r₂ g` lies over `g` on the projections to `W₂` and `W₁`. -/
@[reassoc (attr := simp)]
theorem baseMap_toCover (r₁ : Restriction B S hS 𝒳 i x hx W₁)
    (r₂ : Restriction B S hS 𝒳 i x hx W₂) (g : W₂ ⟶ W₁) :
    baseMap r₁ r₂ g ≫ r₁.toCover = r₂.toCover ≫ g.left :=
  r₁.lift_toCover _ _ _

/-- The arrow between two restrictions of `x` over `baseMap r₁ r₂ g`. -/
def restrictionMap (r₁ : Restriction B S hS 𝒳 i x hx W₁) (r₂ : Restriction B S hS 𝒳 i x hx W₂)
    (g : W₂ ⟶ W₁) : r₂.obj ⟶ r₁.obj :=
  IsStronglyCartesian.map 𝒳.val.val.p _ r₁.hom
    (by rw [← Functor.map_comp, baseMap_toDef] :
      (BigAffineFppf.inclusion B S hS).map r₂.toDef =
        (BigAffineFppf.inclusion B S hS).map (baseMap r₁ r₂ g) ≫
          (BigAffineFppf.inclusion B S hS).map r₁.toDef) r₂.hom

/-- The arrow `restrictionMap r₁ r₂ g` lies over `baseMap r₁ r₂ g`. -/
instance isHomLift_restrictionMap (r₁ : Restriction B S hS 𝒳 i x hx W₁)
    (r₂ : Restriction B S hS 𝒳 i x hx W₂) (g : W₂ ⟶ W₁) :
    𝒳.val.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (baseMap r₁ r₂ g))
      (restrictionMap r₁ r₂ g) :=
  IsStronglyCartesian.map_isHomLift _ _ _ _ _

/-- The arrow `restrictionMap r₁ r₂ g` commutes with the arrows of the two restrictions to
`x`. -/
@[reassoc (attr := simp)]
theorem restrictionMap_hom (r₁ : Restriction B S hS 𝒳 i x hx W₁)
    (r₂ : Restriction B S hS 𝒳 i x hx W₂) (g : W₂ ⟶ W₁) :
    restrictionMap r₁ r₂ g ≫ r₁.hom = r₂.hom :=
  IsStronglyCartesian.fac _ _ _ _ _

/-- Base change of a lift `l` along `g : W₂ ⟶ W₁`, from a restriction `r₁` of `x` over `W₁` to a
restriction `r₂` over `W₂`: the chosen pullback of the lifted object along `g`, with the arrow
from `r₂` obtained by the cartesian factorization. -/
def baseChange {r₁ : Restriction B S hS 𝒳 i x hx W₁} (r₂ : Restriction B S hS 𝒳 i x hx W₂)
    (g : W₂ ⟶ W₁) (l : InfinitesimalLift B S hS 𝒳 i x hx r₁) :
    InfinitesimalLift B S hS 𝒳 i x hx r₂ where
  obj := IsPreFibered.pullbackObj (obj_proj l) ((BigAffineFppf.inclusion B S hS).map g.left)
  hom := IsStronglyCartesian.map 𝒳.val.val.p _
    (IsPreFibered.pullbackMap (obj_proj l) ((BigAffineFppf.inclusion B S hS).map g.left))
    (by rw [← Functor.map_comp, ← Functor.map_comp, baseMap_toCover] :
      (BigAffineFppf.inclusion B S hS).map (baseMap r₁ r₂ g) ≫
          (BigAffineFppf.inclusion B S hS).map r₁.toCover =
        (BigAffineFppf.inclusion B S hS).map r₂.toCover ≫
          (BigAffineFppf.inclusion B S hS).map g.left)
    (restrictionMap r₁ r₂ g ≫ l.hom)
  isCartesian := 𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift _ _

/-- The arrow of the base change of `l` followed by the chosen pullback arrow along `g` is
`restrictionMap r₁ r₂ g` followed by the arrow of `l`. -/
@[reassoc]
theorem baseChange_hom_comp {r₁ : Restriction B S hS 𝒳 i x hx W₁}
    (r₂ : Restriction B S hS 𝒳 i x hx W₂) (g : W₂ ⟶ W₁) (l : InfinitesimalLift B S hS 𝒳 i x hx r₁) :
    (baseChange r₂ g l).hom ≫
        IsPreFibered.pullbackMap (obj_proj l) ((BigAffineFppf.inclusion B S hS).map g.left) =
      restrictionMap r₁ r₂ g ≫ l.hom := by
  have := isStronglyCartesian_pullbackMap (obj_proj l) ((BigAffineFppf.inclusion B S hS).map g.left)
  dsimp only [baseChange]
  exact IsStronglyCartesian.fac _ _ _ _ _

/-- **Base change is a restriction**: `baseChange r₂ g l` is a restriction of `l` along `g`. -/
theorem isRestrictionAlong_baseChange {r₁ : Restriction B S hS 𝒳 i x hx W₁}
    (r₂ : Restriction B S hS 𝒳 i x hx W₂) (g : W₂ ⟶ W₁) (l : InfinitesimalLift B S hS 𝒳 i x hx r₁) :
    IsRestrictionAlong B S hS 𝒳 i x hx g l (baseChange r₂ g l) := by
  have := isStronglyCartesian_pullbackMap (obj_proj l) ((BigAffineFppf.inclusion B S hS).map g.left)
  exact ⟨baseMap r₁ r₂ g, restrictionMap r₁ r₂ g,
    IsPreFibered.pullbackMap (obj_proj l) ((BigAffineFppf.inclusion B S hS).map g.left),
    baseMap_toCover _ _ _, baseMap_toDef _ _ _, inferInstance, restrictionMap_hom _ _ _,
    this, baseChange_hom_comp _ _ _⟩

/-- The restriction relation does not see the base morphism beyond its equality class. -/
theorem IsRestrictionAlong.congr {r₁ : Restriction B S hS 𝒳 i x hx W₁}
    {r₂ : Restriction B S hS 𝒳 i x hx W₂} {g g' : W₂ ⟶ W₁} (e : g = g')
    {l : InfinitesimalLift B S hS 𝒳 i x hx r₁} {m : InfinitesimalLift B S hS 𝒳 i x hx r₂}
    (h : IsRestrictionAlong B S hS 𝒳 i x hx g l m) : IsRestrictionAlong B S hS 𝒳 i x hx g' l m :=
  e ▸ h

/-- A lift is a restriction of itself along the identity. -/
theorem IsRestrictionAlong.refl {r : Restriction B S hS 𝒳 i x hx W}
    (l : InfinitesimalLift B S hS 𝒳 i x hx r) : IsRestrictionAlong B S hS 𝒳 i x hx (𝟙 W) l l := by
  have hl : 𝒳.val.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (𝟙 W : W ⟶ W).left)
      (𝟙 l.obj) := by
    rw [Over.id_left, CategoryTheory.Functor.map_id]
    exact IsHomLift.id (obj_proj l)
  refine ⟨𝟙 _, 𝟙 _, 𝟙 _, by simp, Category.id_comp _, ?_, Category.id_comp _,
    𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift _ _, by simp⟩
  rw [CategoryTheory.Functor.map_id]
  exact IsHomLift.id
    (IsHomLift.domain_eq 𝒳.val.val.p ((BigAffineFppf.inclusion B S hS).map r.toDef) r.hom)

/-- Restriction along a composite is restriction along the two factors in turn. -/
theorem IsRestrictionAlong.trans {r₁ : Restriction B S hS 𝒳 i x hx W₁}
    {r₂ : Restriction B S hS 𝒳 i x hx W₂} {r₃ : Restriction B S hS 𝒳 i x hx W₃}
    {g : W₂ ⟶ W₁} {g' : W₃ ⟶ W₂} {l : InfinitesimalLift B S hS 𝒳 i x hx r₁}
    {m : InfinitesimalLift B S hS 𝒳 i x hx r₂} {n : InfinitesimalLift B S hS 𝒳 i x hx r₃}
    (h : IsRestrictionAlong B S hS 𝒳 i x hx g l m)
    (h' : IsRestrictionAlong B S hS 𝒳 i x hx g' m n) :
    IsRestrictionAlong B S hS 𝒳 i x hx (g' ≫ g) l n := by
  obtain ⟨b, ψ, φ, hb₁, hb₂, hψ, hψw, hφ, hw⟩ := h
  obtain ⟨b', ψ', φ', hb₁', hb₂', hψ', hψw', hφ', hw'⟩ := h'
  have hφφ : 𝒳.val.val.p.IsStronglyCartesian
      ((BigAffineFppf.inclusion B S hS).map (g' ≫ g).left) (φ' ≫ φ) := by
    rw [Over.comp_left, Functor.map_comp]
    infer_instance
  have hψψ : 𝒳.val.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (b' ≫ b)) (ψ' ≫ ψ) := by
    rw [Functor.map_comp]
    infer_instance
  refine ⟨b' ≫ b, ψ' ≫ ψ, φ' ≫ φ, ?_, ?_, hψψ, ?_, hφφ, ?_⟩
  · rw [Category.assoc, hb₁, ← Category.assoc, hb₁', Category.assoc, Over.comp_left]
  · rw [Category.assoc, hb₂, hb₂']
  · rw [Category.assoc, hψw, hψw']
  · rw [← Category.assoc, hw', Category.assoc, hw, Category.assoc]

/-- **Base change respects isomorphism of lifts**: restrictions along one and the same morphism
of isomorphic lifts are isomorphic. -/
theorem isomorphic_of_isRestrictionAlong {r₁ : Restriction B S hS 𝒳 i x hx W₁}
    {r₂ : Restriction B S hS 𝒳 i x hx W₂} {g : W₂ ⟶ W₁}
    {l l' : InfinitesimalLift B S hS 𝒳 i x hx r₁} {m m' : InfinitesimalLift B S hS 𝒳 i x hx r₂}
    (h : IsRestrictionAlong B S hS 𝒳 i x hx g l m) (h' : IsRestrictionAlong B S hS 𝒳 i x hx g l' m')
    (hl : Isomorphic B S hS 𝒳 i x hx l l') : Isomorphic B S hS 𝒳 i x hx m m' := by
  obtain ⟨b, ψ, φ, hb₁, hb₂, hψ, hψw, hφ, hw⟩ := h
  obtain ⟨b', ψ', φ', hb₁', hb₂', hψ', hψw', hφ', hw'⟩ := h'
  obtain ⟨θ, hθ, hθl, hθw⟩ := hl
  have hbb : b = b' := r₁.hom_ext (hb₂.trans hb₂'.symm) (hb₁.trans hb₁'.symm)
  subst hbb
  have hψψ : ψ = ψ' := IsStronglyCartesian.ext 𝒳.val.val.p
    ((BigAffineFppf.inclusion B S hS).map r₁.toDef) r₁.hom
    ((BigAffineFppf.inclusion B S hS).map b) (hψw.trans hψw'.symm)
  subst hψψ
  have : 𝒳.val.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map g.left) (φ ≫ θ) :=
    inferInstance
  let μ := IsStronglyCartesian.map 𝒳.val.val.p ((BigAffineFppf.inclusion B S hS).map g.left) φ'
    (Category.id_comp _).symm (φ ≫ θ)
  have hμ : μ ≫ φ' = φ ≫ θ := IsStronglyCartesian.fac _ _ _ _ _
  have hμl : 𝒳.val.val.p.IsHomLift (𝟙 ((BigAffineFppf.inclusion B S hS).obj W₂.left)) μ :=
    IsStronglyCartesian.map_isHomLift _ _ _ _ _
  have := 𝒳.val.isFiberedInGroupoids.isStronglyCartesian_homLift
    (𝟙 ((BigAffineFppf.inclusion B S hS).obj W₂.left)) μ
  refine ⟨μ, IsStronglyCartesian.isIso_of_base_isIso (p := 𝒳.val.val.p)
    (f := 𝟙 ((BigAffineFppf.inclusion B S hS).obj W₂.left)) μ, hμl, ?_⟩
  have : 𝒳.val.val.p.IsHomLift ((BigAffineFppf.inclusion B S hS).map r₂.toCover) (m.hom ≫ μ) :=
    inferInstance
  refine IsStronglyCartesian.ext 𝒳.val.val.p ((BigAffineFppf.inclusion B S hS).map g.left) φ'
    ((BigAffineFppf.inclusion B S hS).map r₂.toCover) ?_
  rw [Category.assoc, hμ, ← Category.assoc, hw, Category.assoc, hθw, hw']

end InfinitesimalLift

open InfinitesimalLift

variable (B S hS 𝒳 i x hx)

/-- The chosen restriction of `x` over `W`. -/
abbrev chosen (W : Over U') : Restriction B S hS 𝒳 i x hx W :=
  Restriction.canonical B S hS 𝒳 i x hx W

/-- The functor `F` of Stacks 0DNS: the isomorphism classes of lifts over the chosen restriction
of `x`, with base change as restriction maps. -/
def liftClassFunctor : (Over U')ᵒᵖ ⥤ Type (u + 1) where
  obj W := Quotient (setoid (chosen B S hS 𝒳 i x hx W.unop))
  map {W₁ W₂} g := ↾Quotient.map (baseChange (chosen B S hS 𝒳 i x hx W₂.unop) g.unop)
    (fun _ _ h ↦ isomorphic_of_isRestrictionAlong (isRestrictionAlong_baseChange _ _ _)
      (isRestrictionAlong_baseChange _ _ _) h)
  map_id W := by
    ext q
    induction q using Quotient.ind with
    | _ l =>
    exact Quotient.sound (isomorphic_of_isRestrictionAlong (isRestrictionAlong_baseChange _ _ _)
      (IsRestrictionAlong.refl l) (Isomorphic.refl l))
  map_comp {W₁ W₂ W₃} f g := by
    ext q
    induction q using Quotient.ind with
    | _ l =>
    exact Quotient.sound (isomorphic_of_isRestrictionAlong (isRestrictionAlong_baseChange _ _ _)
      ((isRestrictionAlong_baseChange _ _ _).trans (isRestrictionAlong_baseChange _ _ _))
      (Isomorphic.refl l))

/-- The class in `F(W)` of a lift over any restriction of `x` over `W`: the class of its base
change to the chosen restriction along the identity. -/
def liftClass {W : Over U'} (r : Restriction B S hS 𝒳 i x hx W)
    (l : InfinitesimalLift B S hS 𝒳 i x hx r) : (liftClassFunctor B S hS 𝒳 i x hx).obj (op W) :=
  Quotient.mk (setoid (chosen B S hS 𝒳 i x hx W)) (baseChange _ (𝟙 W) l)

/-- **The functor `F` of Stacks 0DNS**: isomorphism classes of lifts of `x|_{B' ⊗_{A'} A}` to `B'`,
with base change as its restriction maps. -/
def liftClassPresheaf : LiftClassPresheaf B S hS 𝒳 i x hx where
  presheaf := liftClassFunctor B S hS 𝒳 i x hx
  nonempty_restriction W := ⟨Restriction.canonical B S hS 𝒳 i x hx W⟩
  cls r l := liftClass B S hS 𝒳 i x hx r l
  cls_surjective {W} r := by
    intro q
    induction q using Quotient.ind with
    | _ l =>
    refine ⟨baseChange r (𝟙 W) l, Quotient.sound ?_⟩
    exact isomorphic_of_isRestrictionAlong
      (((isRestrictionAlong_baseChange _ _ _).trans (isRestrictionAlong_baseChange _ _ _)).congr
        (Category.id_comp _))
      (IsRestrictionAlong.refl l) (Isomorphic.refl l)
  cls_eq_iff {W} r l m := by
    constructor
    · intro h
      have h₂ := isomorphic_of_isRestrictionAlong (r₂ := r) (g := 𝟙 W)
        (isRestrictionAlong_baseChange r _ (baseChange (chosen B S hS 𝒳 i x hx W) (𝟙 W) l))
        (isRestrictionAlong_baseChange r _ (baseChange (chosen B S hS 𝒳 i x hx W) (𝟙 W) m))
        (Quotient.exact h)
      have hl := isomorphic_of_isRestrictionAlong (IsRestrictionAlong.refl l)
        (((isRestrictionAlong_baseChange (chosen B S hS 𝒳 i x hx W) (𝟙 W) l).trans
          (isRestrictionAlong_baseChange r (𝟙 W) _)).congr (Category.id_comp _))
        (Isomorphic.refl l)
      have hm := isomorphic_of_isRestrictionAlong (IsRestrictionAlong.refl m)
        (((isRestrictionAlong_baseChange (chosen B S hS 𝒳 i x hx W) (𝟙 W) m).trans
          (isRestrictionAlong_baseChange r (𝟙 W) _)).congr (Category.id_comp _))
        (Isomorphic.refl m)
      exact hl.trans (h₂.trans hm.symm)
    · intro h
      exact Quotient.sound (isomorphic_of_isRestrictionAlong (isRestrictionAlong_baseChange _ _ _)
        (isRestrictionAlong_baseChange _ _ _) h)
  cls_map {W₁ W₂} g r₁ r₂ l m h := by
    refine Quotient.sound (isomorphic_of_isRestrictionAlong (g := g) ?_ ?_ (Isomorphic.refl l))
    · exact ((isRestrictionAlong_baseChange _ _ _).trans
        (isRestrictionAlong_baseChange _ _ _)).congr (Category.comp_id _)
    · exact (h.trans (isRestrictionAlong_baseChange _ _ _)).congr (Category.id_comp _)

end Deformation.Artin.LiftClassSheaf

end
