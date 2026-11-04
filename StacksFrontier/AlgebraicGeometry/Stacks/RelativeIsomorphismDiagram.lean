module

public import StacksFrontier.AlgebraicGeometry.Stacks.AbsoluteIsomorphismDiagonal

/-!
# The relative isomorphism diagram of a 1-morphism of algebraic stacks

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, let `Z` be an algebraic space over
`S`, let `x₁, x₂ : Z ⟶ 𝒳` be two algebraic-space-valued points of `𝒳`, and let `α` be a
2-morphism `x₁ ≫ f ⟶ x₂ ≫ f` in the target. Stacks 06PP part (2) builds, out of these data, the
cospan whose 2-fibre product is the category of *relative* isomorphisms `x₁ ≅ x₂` lifting `α`:

* the functorial map `H : Isom(x₁, x₂) ⟶ Isom(x₁ ≫ f, x₂ ≫ f)` on 2-fibre products, which keeps
  the two points of `Z` and applies `f` to the isomorphism between them;
* the *twisted* diagonal `Δ : Z ⟶ Isom(x₁ ≫ f, x₂ ≫ f)`, which sends a point `z` to the pair
  `(z, z)` together with the component of `α` at `z` as its comparison isomorphism.

That the 2-fibre product of `H` along `Δ` is an algebraic space over `Z`, the other half of part
(2), is not proved here.

The two constructions are carried out generically for 2-fibre products of categories over a base
(Stacks 0040), where neither needs any fibredness hypothesis:
`CategoryTheory.TwoFibreProductOver.postcomposeTarget` only needs the postcomposing functor to be
strictly over the base, and `CategoryTheory.TwoFibreProductOver.twistedDiagonal` only needs the
2-morphism to be invertible and vertical componentwise. At the stack level both hypotheses are
free: a 1-morphism of categories fibred in groupoids *is* a functor over the site, and every
component of a 2-morphism is vertical, hence invertible because the fibres are groupoids
(Stacks 02XS clause (3) together with Stacks 003V).

`CategoryTheory.TwoFibreProductOver.twistedDiagonal` generalises
`CategoryTheory.TwoFibreProductOver.diagonal`, which is the case of the identity 2-morphism
between a functor and itself.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.postcomposeTarget`: the functor of 2-fibre products induced
  by postcomposing the cospan with a functor over the base.
* `CategoryTheory.TwoFibreProductOver.twistedDiagonal`: the diagonal twisted by a vertical
  invertible 2-morphism.
* `AlgebraicGeometry.Stack.absoluteIsomorphismImageBasedFunctor`: the map `H` above, as a
  1-morphism over the big fppf site.
* `AlgebraicGeometry.Stack.relativeIsomorphismTwistedDiagonalBasedFunctor`: the twisted diagonal
  `Δ` above, as a 1-morphism over the big fppf site.

## Main results

* `AlgebraicGeometry.Stack.exists_relativeIsomorphismDiagram`: the part of **Stacks 06PP** part
  (2) that produces the functorial map and the twisted diagonal, with their components specified.

## References

* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  {𝒮' : Type u₅} [Category.{v₅} 𝒮']
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {p𝒮' : 𝒮' ⥤ 𝒞}

section PostcomposeTarget

variable {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- **Postcomposing the cospan with a functor over the base.** A functor `K : 𝒮 ⥤ 𝒮'` strictly
over `𝒞` carries the 2-fibre product `𝒳 ×_{F, 𝒮, G} 𝒴` into `𝒳 ×_{F ⋙ K, 𝒮', G ⋙ K} 𝒴`: it
keeps the base object and both components of a quadruple `(U, x, y, φ)` and replaces the
comparison isomorphism `φ` by `K φ`, which is again vertical because `K` is over `𝒞`. On
morphisms it is the identity on both components. No fibredness hypothesis is needed. -/
def postcomposeTarget (K : 𝒮 ⥤ 𝒮') (hK : K ⋙ p𝒮' = p𝒮) :
    TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G ⥤
      TwoFibreProductOver p𝒳 p𝒴 p𝒮' (F ⋙ K) (G ⋙ K) where
  obj P :=
    { base := P.base
      x := P.x
      y := P.y
      hx := P.hx
      hy := P.hy
      iso := K.mapIso P.iso
      vertical := by
        have := P.vertical
        exact Functor.isHomLift_map_of_comp_eq hK (𝟙 P.base) P.iso.hom }
  map {P Q} Φ :=
    { hbase := Φ.hbase
      a := Φ.a
      b := Φ.b
      ha := Φ.ha
      hb := Φ.hb
      w := by
        simp only [Functor.comp_map, Functor.mapIso_hom, ← K.map_comp, Φ.w] }
  map_id _ := Hom.ext' rfl rfl
  map_comp _ _ := Hom.ext' rfl rfl

variable (K : 𝒮 ⥤ 𝒮') (hK : K ⋙ p𝒮' = p𝒮)

/-- The base object of the image of a quadruple under `postcomposeTarget` is its base object. -/
@[simp] lemma postcomposeTarget_obj_base (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    ((postcomposeTarget K hK).obj P).base = P.base := rfl

/-- The first component of the image of a quadruple under `postcomposeTarget` is its first
component. -/
@[simp] lemma postcomposeTarget_obj_x (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    ((postcomposeTarget K hK).obj P).x = P.x := rfl

/-- The second component of the image of a quadruple under `postcomposeTarget` is its second
component. -/
@[simp] lemma postcomposeTarget_obj_y (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    ((postcomposeTarget K hK).obj P).y = P.y := rfl

/-- The comparison isomorphism of the image of a quadruple under `postcomposeTarget K hK` is the
image under `K` of its comparison isomorphism. -/
@[simp] lemma postcomposeTarget_obj_iso (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G) :
    ((postcomposeTarget K hK).obj P).iso = K.mapIso P.iso := rfl

/-- `postcomposeTarget` is the identity on the first component of a morphism. -/
@[simp] lemma postcomposeTarget_map_a {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (Φ : P ⟶ Q) :
    ((postcomposeTarget K hK).map Φ).a = Φ.a := rfl

/-- `postcomposeTarget` is the identity on the second component of a morphism. -/
@[simp] lemma postcomposeTarget_map_b {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (Φ : P ⟶ Q) :
    ((postcomposeTarget K hK).map Φ).b = Φ.b := rfl

/-- Postcomposing the cospan is a functor over `𝒞`: it does not move the base object of a
quadruple nor the base morphism of a pair. -/
lemma postcomposeTarget_comp_structureFunctor :
    postcomposeTarget (p𝒳 := p𝒳) (p𝒴 := p𝒴) (F := F) (G := G) K hK ⋙
        structureFunctor p𝒳 p𝒴 p𝒮' (F ⋙ K) (G ⋙ K) =
      structureFunctor p𝒳 p𝒴 p𝒮 F G := rfl

end PostcomposeTarget

section TwistedDiagonal

variable {F G : 𝒳 ⥤ 𝒮} (α : F ⟶ G)
  (hiso : ∀ a : 𝒳, IsIso (α.app a))
  (hvert : ∀ a : 𝒳, p𝒮.IsHomLift (𝟙 (p𝒳.obj a)) (α.app a))

/-- **The diagonal twisted by a vertical invertible 2-morphism.** Given `α : F ⟶ G` between two
functors `𝒳 ⥤ 𝒮` whose components are invertible and vertical over `𝒞`, the functor sending
`a : 𝒳` to the quadruple `(p a, a, a, α_a)` of the 2-fibre product `𝒳 ×_{F, 𝒮, G} 𝒳`, and a
morphism `φ` to the pair `(φ, φ)`. The comparison square of the image of `φ` is the naturality
square of `α`.

For `F = G` and `α` the identity this is
`CategoryTheory.TwoFibreProductOver.diagonal`. -/
noncomputable def twistedDiagonal : 𝒳 ⥤ TwoFibreProductOver p𝒳 p𝒳 p𝒮 F G where
  obj a :=
    { base := p𝒳.obj a
      x := a
      y := a
      hx := rfl
      hy := rfl
      iso := @asIso _ _ _ _ (α.app a) (hiso a)
      vertical := hvert a }
  map {_ _} φ :=
    { hbase := p𝒳.map φ
      a := φ
      b := φ
      ha := inferInstance
      hb := inferInstance
      w := α.naturality φ }
  map_id _ := Hom.ext' rfl rfl
  map_comp _ _ := Hom.ext' rfl rfl

/-- The base object of the image of `a` under the twisted diagonal is `p a`. -/
@[simp] lemma twistedDiagonal_obj_base (a : 𝒳) :
    ((twistedDiagonal α hiso hvert).obj a).base = p𝒳.obj a := rfl

/-- The first component of the image of `a` under the twisted diagonal is `a`. -/
@[simp] lemma twistedDiagonal_obj_x (a : 𝒳) : ((twistedDiagonal α hiso hvert).obj a).x = a := rfl

/-- The second component of the image of `a` under the twisted diagonal is `a`. -/
@[simp] lemma twistedDiagonal_obj_y (a : 𝒳) : ((twistedDiagonal α hiso hvert).obj a).y = a := rfl

/-- The comparison isomorphism of the image of `a` under the twisted diagonal is `α_a`. -/
@[simp] lemma twistedDiagonal_obj_iso_hom (a : 𝒳) :
    ((twistedDiagonal α hiso hvert).obj a).iso.hom = α.app a := rfl

/-- The first component of the image of `φ` under the twisted diagonal is `φ`. -/
@[simp] lemma twistedDiagonal_map_a {a b : 𝒳} (φ : a ⟶ b) :
    ((twistedDiagonal α hiso hvert).map φ).a = φ := rfl

/-- The second component of the image of `φ` under the twisted diagonal is `φ`. -/
@[simp] lemma twistedDiagonal_map_b {a b : 𝒳} (φ : a ⟶ b) :
    ((twistedDiagonal α hiso hvert).map φ).b = φ := rfl

/-- The twisted diagonal is a functor over `𝒞`: it sends `a` to a quadruple with base `p a` and a
morphism `φ` to a pair over `p φ`. -/
lemma twistedDiagonal_comp_structureFunctor :
    twistedDiagonal (p𝒳 := p𝒳) (p𝒮 := p𝒮) α hiso hvert ⋙ structureFunctor p𝒳 p𝒳 p𝒮 F G =
      p𝒳 := rfl

end TwistedDiagonal

end CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z)
variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

/-- **The map on absolute isomorphism categories induced by a 1-morphism `f : 𝒳 ⟶ 𝒴`.** It sends
an isomorphism `φ : x₁(z₁) ≅ x₂(z₂)` of `𝒳` to `f φ`, keeping the two points `z₁`, `z₂` of `Z`.
This is `CategoryTheory.TwoFibreProductOver.postcomposeTarget` applied to the functor underlying
`f`, which is strictly over the big fppf site. -/
def absoluteIsomorphismImageBasedFunctor
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) :
    (absoluteIsomorphismCategory B S hS Z hZ 𝒳 x₁ x₂).val ⥤ᵇ
      (absoluteIsomorphismCategory B S hS Z hZ 𝒴 (x₁ ≫ f) (x₂ ≫ f)).val where
  toFunctor :=
    TwoFibreProductOver.postcomposeTarget f.hom.hom.toFunctor f.hom.hom.w
  w := rfl

/-- **The twisted diagonal determined by a 2-morphism `α : x₁ ≫ f ⟶ x₂ ≫ f` of the target.** It
sends a point `z` of `Z` to the pair `(z, z)` together with the component `α_z` of `α` as its
comparison isomorphism, so its image lands in the isomorphisms of `𝒴` between the two points
`x₁ ≫ f` and `x₂ ≫ f` that `α` prescribes.

Every component of a 2-morphism of categories fibred in groupoids is vertical (Stacks 02XS clause
(3)) and therefore invertible, the fibres being groupoids (Stacks 003V), so both hypotheses of
`CategoryTheory.TwoFibreProductOver.twistedDiagonal` are available with no extra assumption. -/
noncomputable def relativeIsomorphismTwistedDiagonalBasedFunctor
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val ⥤ᵇ
      (absoluteIsomorphismCategory B S hS Z hZ 𝒴 (x₁ ≫ f) (x₂ ≫ f)).val where
  toFunctor :=
    TwoFibreProductOver.twistedDiagonal α.hom.hom.toNatTrans
      (fun a => Functor.IsFiberedInGroupoids.isIso_of_isHomLift_id
        𝒴.val.isFiberedInGroupoids _ (α.hom.hom.isHomLift' a))
      (fun a => α.hom.hom.isHomLift' a)
  w := rfl

/-- For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks, two algebraic-space-valued points
`x₁, x₂ : Z ⟶ 𝒳` and a 2-morphism `α : x₁ ≫ f ⟶ x₂ ≫ f` of the target, there are a 1-morphism `H`
from the isomorphism category of `x₁`, `x₂` to that of `x₁ ≫ f`, `x₂ ≫ f` which keeps the two
points of `Z` and applies `f` to the isomorphism between them, and a 1-morphism `Δ` from `Z` to the
latter whose value at `z` is the pair `(z, z)` with comparison isomorphism `α_z`.

The 2-fibre product of `H` along `Δ` is the category of isomorphisms `x₁ ≅ x₂` lifting `α`; that
it is represented by an algebraic space over `Z` is the remaining half of part (2) and is not
asserted here. The witnesses are
`AlgebraicGeometry.Stack.absoluteIsomorphismImageBasedFunctor` and
`AlgebraicGeometry.Stack.relativeIsomorphismTwistedDiagonalBasedFunctor`. -/
@[stacks 06PP "part (2): functorial map and twisted diagonal"]
theorem exists_relativeIsomorphismDiagram
    (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS Z hZ ⟶ 𝒳) (α : x₁ ≫ f ⟶ x₂ ≫ f) :
    let PX := absoluteIsomorphismCategory B S hS Z hZ 𝒳 x₁ x₂
    let PY := absoluteIsomorphismCategory B S hS Z hZ 𝒴 (x₁ ≫ f) (x₂ ≫ f)
    ∃ (H : PX.val ⥤ᵇ PY.val)
      (Δ : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val ⥤ᵇ PY.val),
      (∀ A : PX.val.obj,
        HEq (H.toFunctor.obj A).x A.x ∧
        HEq (H.toFunctor.obj A).y A.y ∧
        HEq (H.toFunctor.obj A).iso.hom
          (f.hom.hom.toFunctor.map A.iso.hom)) ∧
      (∀ A : (algebraicSpaceStack.{u, w} B S hS Z hZ).val.val.obj,
        HEq (Δ.toFunctor.obj A).x A ∧
        HEq (Δ.toFunctor.obj A).y A ∧
        HEq (Δ.toFunctor.obj A).iso.hom
          (α.hom.hom.toNatTrans.app A)) :=
  ⟨absoluteIsomorphismImageBasedFunctor B S hS Z hZ f x₁ x₂,
    relativeIsomorphismTwistedDiagonalBasedFunctor B S hS Z hZ f x₁ x₂ α,
    fun _ => ⟨HEq.rfl, HEq.rfl, HEq.rfl⟩, fun _ => ⟨HEq.rfl, HEq.rfl, HEq.rfl⟩⟩

end AlgebraicGeometry.Stack

end
