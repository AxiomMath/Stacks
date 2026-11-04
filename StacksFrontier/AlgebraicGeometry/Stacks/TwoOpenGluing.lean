module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RationalMapDomainOfDefinition
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackKernelPairDescent
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.LocallyGroupoid

/-!
# Gluing two 1-morphisms out of open subspaces of an algebraic space

Let `T` be an algebraic space over `S`, let `U₀, U₁ ⊆ T` be open subspaces whose points cover
`|T|`, and let `F₀ : U₀ ⟶ 𝒴`, `F₁ : U₁ ⟶ 𝒴` be 1-morphisms into an algebraic stack together with
a 2-isomorphism `ψ` between their restrictions to `U₀ ∩ U₁`. Then there is a 1-morphism
`G : T ⟶ 𝒴` whose restrictions to `U₀` and `U₁` are 2-isomorphic to `F₀` and `F₁`. For two members
the cocycle condition of descent is automatic. This is the gluing step of the proof of
[Stacks, Tag 0CQ7].

## Main results

* `AlgebraicGeometry.Stack.twoOpenGluing`: the pointwise gluing data.
* `AlgebraicGeometry.Stack.exists_hom_of_two_opens`: the glued 1-morphism.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Bicategory

universe u w

namespace AlgebraicGeometry.Stack

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒴 : AlgebraicStacks.{u, w} B S hS} {T : AlgebraicSpaces B S hS}
  (U₀ U₁ : Subfunctor T.obj) (hU₀ : Space.IsOpenSubspace B S hS U₀)
  (hU₁ : Space.IsOpenSubspace B S hS U₁)

/-- The open subspace `U₀` as an algebraic space. -/
abbrev twoOpenFst : AlgebraicSpaces B S hS := ⟨U₀.toFunctor, hU₀.1⟩

/-- The open subspace `U₁` as an algebraic space. -/
abbrev twoOpenSnd : AlgebraicSpaces B S hS := ⟨U₁.toFunctor, hU₁.1⟩

/-- The intersection `U₀ ∩ U₁` as an algebraic space. -/
abbrev twoOpenInter : AlgebraicSpaces B S hS :=
  ⟨(U₀ ⊓ U₁).toFunctor, (Space.isOpenSubspace_inf B S hS T.property U₀ U₁ hU₀ hU₁).1⟩

/-- The inclusion `U₀ ∩ U₁ ⟶ U₀`. -/
abbrev twoOpenInterFst : twoOpenInter U₀ U₁ hU₀ hU₁ ⟶ twoOpenFst U₀ hU₀ :=
  ObjectProperty.homMk (Subfunctor.homOfLe inf_le_left)

/-- The inclusion `U₀ ∩ U₁ ⟶ U₁`. -/
abbrev twoOpenInterSnd : twoOpenInter U₀ U₁ hU₀ hU₁ ⟶ twoOpenSnd U₁ hU₁ :=
  ObjectProperty.homMk (Subfunctor.homOfLe inf_le_right)

variable (F₀ : (algebraicSpaceStackFunctor.{u, w} B S hS).obj (twoOpenFst U₀ hU₀) ⟶ 𝒴)
  (F₁ : (algebraicSpaceStackFunctor.{u, w} B S hS).obj (twoOpenSnd U₁ hU₁) ⟶ 𝒴)
  (ψ : (algebraicSpaceStackFunctor.{u, w} B S hS).map (twoOpenInterFst U₀ U₁ hU₀ hU₁) ≫ F₀ ≅
    (algebraicSpaceStackFunctor.{u, w} B S hS).map (twoOpenInterSnd U₀ U₁ hU₀ hU₁) ≫ F₁)

/-- The component of `ψ` at a point `r` of `U₀ ∩ U₁`. -/
def twoOpenComp {V : BigFppfOver B S hS} (r : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V)) :
    F₀.hom.hom.obj (elt.{u, w} (twoOpenFst U₀ hU₀) V ((Subfunctor.homOfLe inf_le_left).app _ r)) ⟶
      F₁.hom.hom.obj
        (elt.{u, w} (twoOpenSnd U₁ hU₁) V ((Subfunctor.homOfLe inf_le_right).app _ r)) :=
  ψ.hom.hom.hom.app (elt.{u, w} (twoOpenInter U₀ U₁ hU₀ hU₁) V r)

/-- The component of `ψ⁻¹` at a point `r` of `U₀ ∩ U₁`. -/
def twoOpenCompInv {V : BigFppfOver B S hS} (r : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V)) :
    F₁.hom.hom.obj
        (elt.{u, w} (twoOpenSnd U₁ hU₁) V ((Subfunctor.homOfLe inf_le_right).app _ r)) ⟶
      F₀.hom.hom.obj
        (elt.{u, w} (twoOpenFst U₀ hU₀) V ((Subfunctor.homOfLe inf_le_left).app _ r)) :=
  ψ.inv.hom.hom.app (elt.{u, w} (twoOpenInter U₀ U₁ hU₀ hU₁) V r)

/-- The component of `ψ` at `r` followed by that of `ψ⁻¹` is the identity. -/
theorem twoOpenComp_comp_inv {V : BigFppfOver B S hS}
    (r : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V)) :
    twoOpenComp U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r ≫ twoOpenCompInv U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r = 𝟙 _ :=
  congrArg (fun γ => γ.hom.hom.app (elt.{u, w} (twoOpenInter U₀ U₁ hU₀ hU₁) V r)) ψ.hom_inv_id

/-- The component of `ψ⁻¹` at `r` followed by that of `ψ` is the identity. -/
theorem twoOpenCompInv_comp {V : BigFppfOver B S hS}
    (r : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V)) :
    twoOpenCompInv U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r ≫ twoOpenComp U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r = 𝟙 _ :=
  congrArg (fun γ => γ.hom.hom.app (elt.{u, w} (twoOpenInter U₀ U₁ hU₀ hU₁) V r)) ψ.inv_hom_id

/-- Morphisms of elements of `U₀` and of `U₁` over `g` are the images of one morphism of elements
of `U₀ ∩ U₁`. -/
private theorem exists_twoOpenInter_hom {V W : BigFppfOver B S hS}
    (r : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V)) (g : W ⟶ V)
    (κa : elt.{u, w} (twoOpenFst U₀ hU₀) W
        ((Subfunctor.homOfLe inf_le_left).app _ ((U₀ ⊓ U₁).toFunctor.map g.op r)) ⟶
      elt.{u, w} (twoOpenFst U₀ hU₀) V ((Subfunctor.homOfLe inf_le_left).app _ r))
    (κb : elt.{u, w} (twoOpenSnd U₁ hU₁) W
        ((Subfunctor.homOfLe inf_le_right).app _ ((U₀ ⊓ U₁).toFunctor.map g.op r)) ⟶
      elt.{u, w} (twoOpenSnd U₁ hU₁) V ((Subfunctor.homOfLe inf_le_right).app _ r))
    (hκa : κa.base = g) (hκb : κb.base = g) :
    ∃ κr : elt.{u, w} (twoOpenInter U₀ U₁ hU₀ hU₁) W ((U₀ ⊓ U₁).toFunctor.map g.op r) ⟶
        elt.{u, w} (twoOpenInter U₀ U₁ hU₀ hU₁) V r,
      κa = ((algebraicSpaceStackFunctor.{u, w} B S hS).map
        (twoOpenInterFst U₀ U₁ hU₀ hU₁)).hom.hom.map κr ∧
      κb = ((algebraicSpaceStackFunctor.{u, w} B S hS).map
        (twoOpenInterSnd U₀ U₁ hU₀ hU₁)).hom.hom.map κr :=
  ⟨eltHom g rfl, elt_hom_ext hκa, elt_hom_ext hκb⟩

/-- **The components of `ψ` are natural in the point of `U₀ ∩ U₁`.** -/
theorem twoOpenComp_naturality {V W : BigFppfOver B S hS}
    (r : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V)) (g : W ⟶ V)
    (κa : elt.{u, w} (twoOpenFst U₀ hU₀) W
        ((Subfunctor.homOfLe inf_le_left).app _ ((U₀ ⊓ U₁).toFunctor.map g.op r)) ⟶
      elt.{u, w} (twoOpenFst U₀ hU₀) V ((Subfunctor.homOfLe inf_le_left).app _ r))
    (κb : elt.{u, w} (twoOpenSnd U₁ hU₁) W
        ((Subfunctor.homOfLe inf_le_right).app _ ((U₀ ⊓ U₁).toFunctor.map g.op r)) ⟶
      elt.{u, w} (twoOpenSnd U₁ hU₁) V ((Subfunctor.homOfLe inf_le_right).app _ r))
    (hκa : κa.base = g) (hκb : κb.base = g) :
    F₀.hom.hom.map κa ≫ twoOpenComp U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r =
      twoOpenComp U₀ U₁ hU₀ hU₁ F₀ F₁ ψ ((U₀ ⊓ U₁).toFunctor.map g.op r) ≫
        F₁.hom.hom.map κb := by
  obtain ⟨κr, rfl, rfl⟩ := exists_twoOpenInter_hom.{u, w} U₀ U₁ hU₀ hU₁ r g κa κb hκa hκb
  exact ψ.hom.hom.hom.naturality κr

/-- **The components of `ψ⁻¹` are natural in the point of `U₀ ∩ U₁`.** -/
theorem twoOpenCompInv_naturality {V W : BigFppfOver B S hS}
    (r : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V)) (g : W ⟶ V)
    (κa : elt.{u, w} (twoOpenFst U₀ hU₀) W
        ((Subfunctor.homOfLe inf_le_left).app _ ((U₀ ⊓ U₁).toFunctor.map g.op r)) ⟶
      elt.{u, w} (twoOpenFst U₀ hU₀) V ((Subfunctor.homOfLe inf_le_left).app _ r))
    (κb : elt.{u, w} (twoOpenSnd U₁ hU₁) W
        ((Subfunctor.homOfLe inf_le_right).app _ ((U₀ ⊓ U₁).toFunctor.map g.op r)) ⟶
      elt.{u, w} (twoOpenSnd U₁ hU₁) V ((Subfunctor.homOfLe inf_le_right).app _ r))
    (hκa : κa.base = g) (hκb : κb.base = g) :
    F₁.hom.hom.map κb ≫ twoOpenCompInv U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r =
      twoOpenCompInv U₀ U₁ hU₀ hU₁ F₀ F₁ ψ ((U₀ ⊓ U₁).toFunctor.map g.op r) ≫
        F₀.hom.hom.map κa := by
  obtain ⟨κr, rfl, rfl⟩ := exists_twoOpenInter_hom.{u, w} U₀ U₁ hU₀ hU₁ r g κa κb hκa hκb
  exact ψ.inv.hom.hom.naturality κr

/-! ### Transported components -/

/-- The component of `ψ` at `r`, transported to two points equal to the images of `r`. -/
def twoOpenComponent {V : BigFppfOver B S hS} (r : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V))
    {a : U₀.toFunctor.obj (Opposite.op V)} {b : U₁.toFunctor.obj (Opposite.op V)}
    (ha : (Subfunctor.homOfLe inf_le_left).app _ r = a)
    (hb : (Subfunctor.homOfLe inf_le_right).app _ r = b) :
    F₀.hom.hom.obj (elt.{u, w} (twoOpenFst U₀ hU₀) V a) ⟶
      F₁.hom.hom.obj (elt.{u, w} (twoOpenSnd U₁ hU₁) V b) :=
  eqToHom (congrArg (fun z => F₀.hom.hom.obj (elt.{u, w} (twoOpenFst U₀ hU₀) V z)) ha.symm) ≫
    twoOpenComp U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r ≫
      eqToHom (congrArg (fun z => F₁.hom.hom.obj (elt.{u, w} (twoOpenSnd U₁ hU₁) V z)) hb)

/-- The component of `ψ⁻¹` at `r`, transported to two points equal to the images of `r`. -/
def twoOpenComponentInv {V : BigFppfOver B S hS} (r : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V))
    {a : U₀.toFunctor.obj (Opposite.op V)} {b : U₁.toFunctor.obj (Opposite.op V)}
    (ha : (Subfunctor.homOfLe inf_le_left).app _ r = a)
    (hb : (Subfunctor.homOfLe inf_le_right).app _ r = b) :
    F₁.hom.hom.obj (elt.{u, w} (twoOpenSnd U₁ hU₁) V b) ⟶
      F₀.hom.hom.obj (elt.{u, w} (twoOpenFst U₀ hU₀) V a) :=
  eqToHom (congrArg (fun z => F₁.hom.hom.obj (elt.{u, w} (twoOpenSnd U₁ hU₁) V z)) hb.symm) ≫
    twoOpenCompInv U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r ≫
      eqToHom (congrArg (fun z => F₀.hom.hom.obj (elt.{u, w} (twoOpenFst U₀ hU₀) V z)) ha)

/-- Along reflexivity proofs, `twoOpenComponent` is the component `twoOpenComp` of `ψ`. -/
theorem twoOpenComponent_rfl {V : BigFppfOver B S hS}
    (r : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V)) :
    twoOpenComponent U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r rfl rfl = twoOpenComp U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r := by
  simp only [twoOpenComponent, eqToHom_refl, Category.id_comp]
  exact Category.comp_id _

/-- Along reflexivity proofs, `twoOpenComponentInv` is the component `twoOpenCompInv` of
`ψ⁻¹`. -/
theorem twoOpenComponentInv_rfl {V : BigFppfOver B S hS}
    (r : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V)) :
    twoOpenComponentInv U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r rfl rfl =
      twoOpenCompInv U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r := by
  simp only [twoOpenComponentInv, eqToHom_refl, Category.id_comp]
  exact Category.comp_id _

/-- The transported components `twoOpenComponent` of `ψ` are natural in the point of `U₀ ∩ U₁`. -/
theorem twoOpenComponent_naturality {V W : BigFppfOver B S hS}
    (r : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V)) (r' : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op W))
    {a : U₀.toFunctor.obj (Opposite.op V)} {b : U₁.toFunctor.obj (Opposite.op V)}
    {a' : U₀.toFunctor.obj (Opposite.op W)} {b' : U₁.toFunctor.obj (Opposite.op W)}
    (ha : (Subfunctor.homOfLe inf_le_left).app _ r = a)
    (hb : (Subfunctor.homOfLe inf_le_right).app _ r = b)
    (ha' : (Subfunctor.homOfLe inf_le_left).app _ r' = a')
    (hb' : (Subfunctor.homOfLe inf_le_right).app _ r' = b')
    (κa : elt.{u, w} (twoOpenFst U₀ hU₀) W a' ⟶ elt.{u, w} (twoOpenFst U₀ hU₀) V a)
    (κb : elt.{u, w} (twoOpenSnd U₁ hU₁) W b' ⟶ elt.{u, w} (twoOpenSnd U₁ hU₁) V b)
    (g : W ⟶ V) (hκa : κa.base = g) (hκb : κb.base = g)
    (hr : r' = (U₀ ⊓ U₁).toFunctor.map g.op r) :
    F₀.hom.hom.map κa ≫ twoOpenComponent U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r ha hb =
      twoOpenComponent U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r' ha' hb' ≫ F₁.hom.hom.map κb := by
  subst ha hb ha' hb' hr
  rw [twoOpenComponent_rfl, twoOpenComponent_rfl]
  exact twoOpenComp_naturality U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r g κa κb hκa hκb

/-- The transported components `twoOpenComponentInv` of `ψ⁻¹` are natural in the point of
`U₀ ∩ U₁`. -/
theorem twoOpenComponentInv_naturality {V W : BigFppfOver B S hS}
    (r : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V)) (r' : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op W))
    {a : U₀.toFunctor.obj (Opposite.op V)} {b : U₁.toFunctor.obj (Opposite.op V)}
    {a' : U₀.toFunctor.obj (Opposite.op W)} {b' : U₁.toFunctor.obj (Opposite.op W)}
    (ha : (Subfunctor.homOfLe inf_le_left).app _ r = a)
    (hb : (Subfunctor.homOfLe inf_le_right).app _ r = b)
    (ha' : (Subfunctor.homOfLe inf_le_left).app _ r' = a')
    (hb' : (Subfunctor.homOfLe inf_le_right).app _ r' = b')
    (κa : elt.{u, w} (twoOpenFst U₀ hU₀) W a' ⟶ elt.{u, w} (twoOpenFst U₀ hU₀) V a)
    (κb : elt.{u, w} (twoOpenSnd U₁ hU₁) W b' ⟶ elt.{u, w} (twoOpenSnd U₁ hU₁) V b)
    (g : W ⟶ V) (hκa : κa.base = g) (hκb : κb.base = g)
    (hr : r' = (U₀ ⊓ U₁).toFunctor.map g.op r) :
    F₁.hom.hom.map κb ≫ twoOpenComponentInv U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r ha hb =
      twoOpenComponentInv U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r' ha' hb' ≫ F₀.hom.hom.map κa := by
  subst ha hb ha' hb' hr
  rw [twoOpenComponentInv_rfl, twoOpenComponentInv_rfl]
  exact twoOpenCompInv_naturality U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r g κa κb hκa hκb

/-- A transported component of `ψ` followed by a transported component of `ψ⁻¹` at the same point
is the transport `eqToHom` between the two points of `U₀`. -/
theorem twoOpenComponent_comp_inv {V : BigFppfOver B S hS}
    (r r' : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V)) (hrr : r = r')
    {a a' : U₀.toFunctor.obj (Opposite.op V)} {b : U₁.toFunctor.obj (Opposite.op V)}
    (ha : (Subfunctor.homOfLe inf_le_left).app _ r = a)
    (hb : (Subfunctor.homOfLe inf_le_right).app _ r = b)
    (ha' : (Subfunctor.homOfLe inf_le_left).app _ r' = a')
    (hb' : (Subfunctor.homOfLe inf_le_right).app _ r' = b) (haa : a = a') :
    twoOpenComponent U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r ha hb ≫
        twoOpenComponentInv U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r' ha' hb' =
      eqToHom (congrArg (fun z => F₀.hom.hom.obj (elt.{u, w} (twoOpenFst U₀ hU₀) V z)) haa) := by
  subst hrr ha hb haa
  rw [twoOpenComponent_rfl, twoOpenComponentInv_rfl, twoOpenComp_comp_inv, eqToHom_refl]

/-- A transported component of `ψ⁻¹` followed by a transported component of `ψ` at the same point
is the transport `eqToHom` between the two points of `U₁`. -/
theorem twoOpenComponentInv_comp {V : BigFppfOver B S hS}
    (r r' : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V)) (hrr : r = r')
    {a : U₀.toFunctor.obj (Opposite.op V)} {b b' : U₁.toFunctor.obj (Opposite.op V)}
    (ha : (Subfunctor.homOfLe inf_le_left).app _ r = a)
    (hb : (Subfunctor.homOfLe inf_le_right).app _ r = b)
    (ha' : (Subfunctor.homOfLe inf_le_left).app _ r' = a)
    (hb' : (Subfunctor.homOfLe inf_le_right).app _ r' = b') (hbb : b = b') :
    twoOpenComponentInv U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r ha hb ≫
        twoOpenComponent U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r' ha' hb' =
      eqToHom (congrArg (fun z => F₁.hom.hom.obj (elt.{u, w} (twoOpenSnd U₁ hU₁) V z)) hbb) := by
  subst hrr ha hb hbb
  rw [twoOpenComponentInv_rfl, twoOpenComponent_rfl, twoOpenCompInv_comp, eqToHom_refl]

/-- Precomposing a transported component of `ψ` with a transport along an equality of points of
`U₀` gives the transported component at the new point. -/
theorem eqToHom_comp_twoOpenComponent {V : BigFppfOver B S hS}
    (r r' : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V)) (hrr : r = r')
    {a a' : U₀.toFunctor.obj (Opposite.op V)} {b : U₁.toFunctor.obj (Opposite.op V)}
    (haa : a' = a) (ha : (Subfunctor.homOfLe inf_le_left).app _ r = a)
    (hb : (Subfunctor.homOfLe inf_le_right).app _ r = b)
    (ha' : (Subfunctor.homOfLe inf_le_left).app _ r' = a')
    (hb' : (Subfunctor.homOfLe inf_le_right).app _ r' = b) :
    eqToHom (congrArg (fun z => F₀.hom.hom.obj (elt.{u, w} (twoOpenFst U₀ hU₀) V z)) haa) ≫
        twoOpenComponent U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r ha hb =
      twoOpenComponent U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r' ha' hb' := by
  subst hrr haa ha hb
  rw [eqToHom_refl, Category.id_comp]

/-- Postcomposing a transported component of `ψ` with a transport along an equality of points of
`U₁` gives the transported component at the new point. -/
theorem twoOpenComponent_comp_eqToHom {V : BigFppfOver B S hS}
    (r r' : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V)) (hrr : r = r')
    {a : U₀.toFunctor.obj (Opposite.op V)} {b b' : U₁.toFunctor.obj (Opposite.op V)}
    (hbb : b = b') (ha : (Subfunctor.homOfLe inf_le_left).app _ r = a)
    (hb : (Subfunctor.homOfLe inf_le_right).app _ r = b)
    (ha' : (Subfunctor.homOfLe inf_le_left).app _ r' = a)
    (hb' : (Subfunctor.homOfLe inf_le_right).app _ r' = b') :
    twoOpenComponent U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r ha hb ≫
        eqToHom (congrArg (fun z => F₁.hom.hom.obj (elt.{u, w} (twoOpenSnd U₁ hU₁) V z)) hbb) =
      twoOpenComponent U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r' ha' hb' := by
  subst hrr hbb ha hb
  rw [eqToHom_refl, Category.comp_id]

/-- Precomposing a transported component of `ψ⁻¹` with a transport along an equality of points of
`U₁` gives the transported component at the new point. -/
theorem eqToHom_comp_twoOpenComponentInv {V : BigFppfOver B S hS}
    (r r' : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V)) (hrr : r = r')
    {a : U₀.toFunctor.obj (Opposite.op V)} {b b' : U₁.toFunctor.obj (Opposite.op V)}
    (hbb : b' = b) (ha : (Subfunctor.homOfLe inf_le_left).app _ r = a)
    (hb : (Subfunctor.homOfLe inf_le_right).app _ r = b)
    (ha' : (Subfunctor.homOfLe inf_le_left).app _ r' = a)
    (hb' : (Subfunctor.homOfLe inf_le_right).app _ r' = b') :
    eqToHom (congrArg (fun z => F₁.hom.hom.obj (elt.{u, w} (twoOpenSnd U₁ hU₁) V z)) hbb) ≫
        twoOpenComponentInv U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r ha hb =
      twoOpenComponentInv U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r' ha' hb' := by
  subst hrr hbb ha hb
  rw [eqToHom_refl, Category.id_comp]

/-- Postcomposing a transported component of `ψ⁻¹` with a transport along an equality of points
of `U₀` gives the transported component at the new point. -/
theorem twoOpenComponentInv_comp_eqToHom {V : BigFppfOver B S hS}
    (r r' : (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V)) (hrr : r = r')
    {a a' : U₀.toFunctor.obj (Opposite.op V)} {b : U₁.toFunctor.obj (Opposite.op V)}
    (haa : a = a') (ha : (Subfunctor.homOfLe inf_le_left).app _ r = a)
    (hb : (Subfunctor.homOfLe inf_le_right).app _ r = b)
    (ha' : (Subfunctor.homOfLe inf_le_left).app _ r' = a')
    (hb' : (Subfunctor.homOfLe inf_le_right).app _ r' = b) :
    twoOpenComponentInv U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r ha hb ≫
        eqToHom (congrArg (fun z => F₀.hom.hom.obj (elt.{u, w} (twoOpenFst U₀ hU₀) V z)) haa) =
      twoOpenComponentInv U₀ U₁ hU₀ hU₁ F₀ F₁ ψ r' ha' hb' := by
  subst hrr haa ha hb
  rw [eqToHom_refl, Category.comp_id]

/-! ### The pointwise gluing data -/

/-- The two members of the covering. -/
def twoOpenSpace : Bool → AlgebraicSpaces B S hS
  | false => twoOpenFst U₀ hU₀
  | true => twoOpenSnd U₁ hU₁

/-- The inclusions of the two members. -/
def twoOpenIncl : ∀ k, twoOpenSpace U₀ U₁ hU₀ hU₁ k ⟶ T
  | false => ObjectProperty.homMk U₀.ι
  | true => ObjectProperty.homMk U₁.ι

/-- The two 1-morphisms to glue. -/
def twoOpenMap : ∀ k,
    (algebraicSpaceStackFunctor.{u, w} B S hS).obj (twoOpenSpace U₀ U₁ hU₀ hU₁ k) ⟶ 𝒴
  | false => F₀
  | true => F₁

/-- The point of `U₀ ∩ U₁` given by a point of `U₀` and a point of `U₁` with the same image. -/
def twoOpenPt {V : BigFppfOver B S hS} (a : U₀.toFunctor.obj (Opposite.op V))
    (b : U₁.toFunctor.obj (Opposite.op V)) (h : a.1 = b.1) :
    (U₀ ⊓ U₁).toFunctor.obj (Opposite.op V) :=
  ⟨a.1, a.2, by rw [h]; exact b.2⟩

omit hU₀ hU₁ in
/-- The image of `twoOpenPt a b h` in `U₀` is `a`. -/
theorem twoOpenPt_fst {V : BigFppfOver B S hS} (a : U₀.toFunctor.obj (Opposite.op V))
    (b : U₁.toFunctor.obj (Opposite.op V)) (h : a.1 = b.1) :
    (Subfunctor.homOfLe inf_le_left).app _ (twoOpenPt U₀ U₁ a b h) = a :=
  Subtype.ext rfl

omit hU₀ hU₁ in
/-- The image of `twoOpenPt a b h` in `U₁` is `b`. -/
theorem twoOpenPt_snd {V : BigFppfOver B S hS} (a : U₀.toFunctor.obj (Opposite.op V))
    (b : U₁.toFunctor.obj (Opposite.op V)) (h : a.1 = b.1) :
    (Subfunctor.homOfLe inf_le_right).app _ (twoOpenPt U₀ U₁ a b h) = b :=
  Subtype.ext h

/-- The identifications of the pointwise gluing data: transports on each member, and the
components of `ψ` and of `ψ⁻¹` between the two members. -/
def twoOpenPhi : ∀ (k l : Bool) (V : BigFppfOver B S hS)
    (a : (twoOpenSpace U₀ U₁ hU₀ hU₁ k).obj.obj (Opposite.op V))
    (b : (twoOpenSpace U₀ U₁ hU₀ hU₁ l).obj.obj (Opposite.op V)),
    (twoOpenIncl U₀ U₁ hU₀ hU₁ k).hom.app _ a = (twoOpenIncl U₀ U₁ hU₀ hU₁ l).hom.app _ b →
      ((twoOpenMap U₀ U₁ hU₀ hU₁ F₀ F₁ k).hom.hom.obj
          (elt.{u, w} (twoOpenSpace U₀ U₁ hU₀ hU₁ k) V a) ⟶
        (twoOpenMap U₀ U₁ hU₀ hU₁ F₀ F₁ l).hom.hom.obj
          (elt.{u, w} (twoOpenSpace U₀ U₁ hU₀ hU₁ l) V b))
  | false, false, V, _, _, h =>
    eqToHom (congrArg (fun z => F₀.hom.hom.obj (elt.{u, w} (twoOpenFst U₀ hU₀) V z))
      (Subtype.ext h))
  | false, true, _, a, b, h =>
    twoOpenComponent U₀ U₁ hU₀ hU₁ F₀ F₁ ψ (twoOpenPt U₀ U₁ a b h) (twoOpenPt_fst U₀ U₁ a b h)
      (twoOpenPt_snd U₀ U₁ a b h)
  | true, false, _, a, b, h =>
    twoOpenComponentInv U₀ U₁ hU₀ hU₁ F₀ F₁ ψ (twoOpenPt U₀ U₁ b a h.symm)
      (twoOpenPt_fst U₀ U₁ b a h.symm) (twoOpenPt_snd U₀ U₁ b a h.symm)
  | true, true, V, _, _, h =>
    eqToHom (congrArg (fun z => F₁.hom.hom.obj (elt.{u, w} (twoOpenSnd U₁ hU₁) V z))
      (Subtype.ext h))

/-- Transporting a morphism lying over `𝟙 V` along equalities of objects keeps it over `𝟙 V`. -/
private theorem isHomLift_eqToHom_comp_comp_eqToHom {𝒳 𝒞 : Type*} [Category 𝒳] [Category 𝒞]
    (p : 𝒳 ⥤ 𝒞) {V : 𝒞} {X X' Y Y' : 𝒳} (f : X ⟶ Y) (hf : p.IsHomLift (𝟙 V) f) (e₁ : X' = X)
    (e₂ : Y = Y') : p.IsHomLift (𝟙 V) (eqToHom e₁ ≫ f ≫ eqToHom e₂) := by
  subst e₁ e₂
  simpa using hf

/-- Each identification `twoOpenPhi` lies over the identity of `V`. -/
theorem isHomLift_twoOpenPhi (k l : Bool) (V : BigFppfOver B S hS)
    (a : (twoOpenSpace U₀ U₁ hU₀ hU₁ k).obj.obj (Opposite.op V))
    (b : (twoOpenSpace U₀ U₁ hU₀ hU₁ l).obj.obj (Opposite.op V))
    (h : (twoOpenIncl U₀ U₁ hU₀ hU₁ k).hom.app _ a = (twoOpenIncl U₀ U₁ hU₀ hU₁ l).hom.app _ b) :
    𝒴.val.val.p.IsHomLift (𝟙 V) (twoOpenPhi U₀ U₁ hU₀ hU₁ F₀ F₁ ψ k l V a b h) := by
  cases k <;> cases l
  · unfold twoOpenPhi
    exact IsHomLift.eqToHom_domain_lift_id _ (BasedFunctor.w_obj F₀.hom.hom _)
  · exact isHomLift_eqToHom_comp_comp_eqToHom _ _
      (ψ.hom.hom.hom.isHomLift' (elt.{u, w} (twoOpenInter U₀ U₁ hU₀ hU₁) V (twoOpenPt U₀ U₁ a b h)))
      _ _
  · exact isHomLift_eqToHom_comp_comp_eqToHom _ _
      (ψ.inv.hom.hom.isHomLift'
        (elt.{u, w} (twoOpenInter U₀ U₁ hU₀ hU₁) V (twoOpenPt U₀ U₁ b a h.symm))) _ _
  · unfold twoOpenPhi
    exact IsHomLift.eqToHom_domain_lift_id _ (BasedFunctor.w_obj F₁.hom.hom _)

/-- A morphism of the category of elements between two points of one member is determined by
its base, and transports along equal points commute with it. -/
theorem map_comp_eqToHom_of_eq {T₀ : AlgebraicSpaces B S hS}
    (F : (algebraicSpaceStackFunctor.{u, w} B S hS).obj T₀ ⟶ 𝒴) {V W : BigFppfOver B S hS}
    {a b : T₀.obj.obj (Opposite.op V)} {a' b' : T₀.obj.obj (Opposite.op W)}
    (κa : elt.{u, w} T₀ W a' ⟶ elt.{u, w} T₀ V a) (κb : elt.{u, w} T₀ W b' ⟶ elt.{u, w} T₀ V b)
    (hκ : κa.base = κb.base) (h : a = b) (h' : a' = b') :
    F.hom.hom.map κa ≫ eqToHom (congrArg (fun z => F.hom.hom.obj (elt.{u, w} T₀ V z)) h) =
      eqToHom (congrArg (fun z => F.hom.hom.obj (elt.{u, w} T₀ W z)) h') ≫ F.hom.hom.map κb := by
  subst h h'
  obtain rfl : κa = κb := elt_hom_ext hκ
  simp

/-- **Pointwise gluing data for two opens.** -/
def twoOpenGluing :
    PointwiseGluing (twoOpenIncl U₀ U₁ hU₀ hU₁) (twoOpenMap U₀ U₁ hU₀ hU₁ F₀ F₁) where
  φ := twoOpenPhi U₀ U₁ hU₀ hU₁ F₀ F₁ ψ
  isHomLift := isHomLift_twoOpenPhi U₀ U₁ hU₀ hU₁ F₀ F₁ ψ
  naturality := fun k l {V W} {a a' b b'} κa κb hκ h h' => by
    cases k <;> cases l
    · exact map_comp_eqToHom_of_eq F₀ κa κb hκ (Subtype.ext h) (Subtype.ext h')
    · exact twoOpenComponent_naturality U₀ U₁ hU₀ hU₁ F₀ F₁ ψ (twoOpenPt U₀ U₁ a b h)
        (twoOpenPt U₀ U₁ a' b' h') (twoOpenPt_fst U₀ U₁ a b h) (twoOpenPt_snd U₀ U₁ a b h)
        (twoOpenPt_fst U₀ U₁ a' b' h') (twoOpenPt_snd U₀ U₁ a' b' h') κa κb κa.base rfl
        hκ.symm (Subtype.ext (congrArg Subtype.val (point_eq_of_hom.{u, w} κa) :))
    · exact twoOpenComponentInv_naturality U₀ U₁ hU₀ hU₁ F₀ F₁ ψ (twoOpenPt U₀ U₁ b a h.symm)
        (twoOpenPt U₀ U₁ b' a' h'.symm) (twoOpenPt_fst U₀ U₁ b a h.symm)
        (twoOpenPt_snd U₀ U₁ b a h.symm) (twoOpenPt_fst U₀ U₁ b' a' h'.symm)
        (twoOpenPt_snd U₀ U₁ b' a' h'.symm) κb κa κb.base rfl
        hκ (Subtype.ext (congrArg Subtype.val (point_eq_of_hom.{u, w} κb) :))
    · exact map_comp_eqToHom_of_eq F₁ κa κb hκ (Subtype.ext h) (Subtype.ext h')
  cocycle := fun k l m V a b c h₁ h₂ => by
    cases k <;> cases l <;> cases m
    · unfold twoOpenPhi
      exact eqToHom_trans _ _
    · exact eqToHom_comp_twoOpenComponent U₀ U₁ hU₀ hU₁ F₀ F₁ ψ (twoOpenPt U₀ U₁ b c h₂)
        (twoOpenPt U₀ U₁ a c (h₁.trans h₂)) (Subtype.ext h₁.symm) (Subtype.ext h₁)
        (twoOpenPt_fst U₀ U₁ b c h₂) (twoOpenPt_snd U₀ U₁ b c h₂)
        (twoOpenPt_fst U₀ U₁ a c (h₁.trans h₂)) (twoOpenPt_snd U₀ U₁ a c (h₁.trans h₂))
    · exact twoOpenComponent_comp_inv U₀ U₁ hU₀ hU₁ F₀ F₁ ψ (twoOpenPt U₀ U₁ a b h₁)
        (twoOpenPt U₀ U₁ c b h₂.symm) (Subtype.ext (h₁.trans h₂)) (twoOpenPt_fst U₀ U₁ a b h₁)
        (twoOpenPt_snd U₀ U₁ a b h₁) (twoOpenPt_fst U₀ U₁ c b h₂.symm)
        (twoOpenPt_snd U₀ U₁ c b h₂.symm) (Subtype.ext (h₁.trans h₂))
    · exact twoOpenComponent_comp_eqToHom U₀ U₁ hU₀ hU₁ F₀ F₁ ψ (twoOpenPt U₀ U₁ a b h₁)
        (twoOpenPt U₀ U₁ a c (h₁.trans h₂)) (Subtype.ext rfl) (Subtype.ext h₂)
        (twoOpenPt_fst U₀ U₁ a b h₁) (twoOpenPt_snd U₀ U₁ a b h₁)
        (twoOpenPt_fst U₀ U₁ a c (h₁.trans h₂)) (twoOpenPt_snd U₀ U₁ a c (h₁.trans h₂))
    · exact twoOpenComponentInv_comp_eqToHom U₀ U₁ hU₀ hU₁ F₀ F₁ ψ (twoOpenPt U₀ U₁ b a h₁.symm)
        (twoOpenPt U₀ U₁ c a (h₁.trans h₂).symm) (Subtype.ext h₂) (Subtype.ext h₂)
        (twoOpenPt_fst U₀ U₁ b a h₁.symm) (twoOpenPt_snd U₀ U₁ b a h₁.symm)
        (twoOpenPt_fst U₀ U₁ c a (h₁.trans h₂).symm) (twoOpenPt_snd U₀ U₁ c a (h₁.trans h₂).symm)
    · exact twoOpenComponentInv_comp U₀ U₁ hU₀ hU₁ F₀ F₁ ψ (twoOpenPt U₀ U₁ b a h₁.symm)
        (twoOpenPt U₀ U₁ b c h₂) (Subtype.ext rfl) (twoOpenPt_fst U₀ U₁ b a h₁.symm)
        (twoOpenPt_snd U₀ U₁ b a h₁.symm) (twoOpenPt_fst U₀ U₁ b c h₂)
        (twoOpenPt_snd U₀ U₁ b c h₂) (Subtype.ext (h₁.trans h₂))
    · exact eqToHom_comp_twoOpenComponentInv U₀ U₁ hU₀ hU₁ F₀ F₁ ψ (twoOpenPt U₀ U₁ c b h₂.symm)
        (twoOpenPt U₀ U₁ c a (h₁.trans h₂).symm) (Subtype.ext rfl) (Subtype.ext h₁)
        (twoOpenPt_fst U₀ U₁ c b h₂.symm) (twoOpenPt_snd U₀ U₁ c b h₂.symm)
        (twoOpenPt_fst U₀ U₁ c a (h₁.trans h₂).symm) (twoOpenPt_snd U₀ U₁ c a (h₁.trans h₂).symm)
    · unfold twoOpenPhi
      exact eqToHom_trans _ _

include ψ in
/-- **Gluing two 1-morphisms out of open subspaces.** Let `U₀, U₁ ⊆ T` be open subspaces of an
algebraic space whose points cover `|T|`, and let `F₀ : U₀ ⟶ 𝒴`, `F₁ : U₁ ⟶ 𝒴` be 1-morphisms
into an algebraic stack with a 2-isomorphism `ψ` between their restrictions to `U₀ ∩ U₁`. Then
there is a 1-morphism `G : T ⟶ 𝒴` restricting to `F₀` on `U₀` and to `F₁` on `U₁`, up to
2-isomorphism. -/
theorem exists_hom_of_two_opens
    (hcov : Set.range (Space.pointsMap B S hS U₀.toFunctor U₀.ι) ∪
      Set.range (Space.pointsMap B S hS U₁.toFunctor U₁.ι) = Set.univ) :
    ∃ G : (algebraicSpaceStackFunctor.{u, w} B S hS).obj T ⟶ 𝒴,
      Nonempty ((algebraicSpaceStackFunctor.{u, w} B S hS).map
          (ObjectProperty.homMk U₀.ι : twoOpenFst U₀ hU₀ ⟶ T) ≫ G ≅ F₀) ∧
        Nonempty ((algebraicSpaceStackFunctor.{u, w} B S hS).map
          (ObjectProperty.homMk U₁.ι : twoOpenSnd U₁ hU₁ ⟶ T) ≫ G ≅ F₁) := by
  have he : Space.IsEtaleCovering B S hS (fun k => (twoOpenSpace U₀ U₁ hU₀ hU₁ k).obj)
      (fun k => (twoOpenIncl U₀ U₁ hU₀ hU₁ k).hom) := by
    refine ⟨T.property, fun k => (twoOpenSpace U₀ U₁ hU₀ hU₁ k).property, fun k => ?_, ?_⟩
    · cases k
      · exact Space.isEtale_ι_of_isOpenSubspace hU₀
      · exact Space.isEtale_ι_of_isOpenSubspace hU₁
    · rw [← hcov]
      ext y
      simp only [Set.mem_iUnion, Set.mem_union, Bool.exists_bool]
      exact Iff.rfl
  obtain ⟨G, ψk, -⟩ := exists_hom_of_isEtaleCovering he (twoOpenGluing U₀ U₁ hU₀ hU₁ F₀ F₁ ψ)
  exact ⟨G, ⟨Bicategory.InducedBicategory.isoMk (CatFiberedInGroupoids.twoIso (ψk false).hom)⟩,
    ⟨Bicategory.InducedBicategory.isoMk (CatFiberedInGroupoids.twoIso (ψk true).hom)⟩⟩

end AlgebraicGeometry.Stack

end
