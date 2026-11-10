module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AbsoluteIsomorphismDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationFibreProductProperties
public import StacksFrontier.CategoryTheory.FiberedCategory.DiscreteTwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.CatFiberedInGroupoids
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence

/-!
# Separation and the maps on points and isomorphism spaces (Stacks 0CPL, 0DU8)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. Stacks 0CPL reads two consequences
off a separation axiom on `f`:

1. for algebraic spaces `T₁`, `T₂` over `S` and points `xᵢ : Tᵢ ⟶ 𝒳` with `yᵢ = xᵢ ≫ f`, the
   comparison `T₁ ×_{x₁, 𝒳, x₂} T₂ ⟶ T₁ ×_{y₁, 𝒴, y₂} T₂`, and
2. for a single algebraic space `T` over `S` and points `x₁, x₂ : T ⟶ 𝒳`, the induced map
   `Isom_𝒳(x₁, x₂) ⟶ Isom_𝒴(y₁, y₂)`

is proper (resp. quasi-compact and quasi-separated, resp. locally quasi-finite, resp. unramified)
as soon as `f` is separated (resp. quasi-separated, resp. quasi-DM, resp. Deligne–Mumford).

Part (1) is Stacks 050H parts (4)–(7) at a cospan of algebraic spaces. Part (2) rests on the
2-cartesian square

```text
  Isom_𝒳(x₁, x₂)  ------->  T ×_{x₁, 𝒳, x₂} T
        |                           |
        |                           |
        v                           v
  Isom_𝒴(y₁, y₂)  ------->  T ×_{y₁, 𝒴, y₂} T
```

whose horizontal arrows are the inclusions of the isomorphisms between the two points into all
isomorphisms between their values, and whose right-hand arrow is the comparison of part (1): the
map of part (2) is a base change of the map of part (1), and the conditions of Stacks 04XB are
stable under base change.

**Stacks 0DU8** is part (2) read at `x₁ = x₂ = x` and at an arbitrary property of morphisms of
algebraic spaces. There `G ⟶ H` is the pullback to `T` of the stabilizer comparison
`ℐ_𝒳 ⟶ 𝒳 ×_𝒴 ℐ_𝒴` of Stacks 06R5, which is the map `Isom_𝒳(x, x) ⟶ Isom_𝒴(f ∘ x, f ∘ x)` on
automorphism spaces: an object of `ℐ_𝒳 ×_𝒳 T` over a scheme is a point `t` of `T` together with a
vertical automorphism of `x(t)`, and likewise for `(𝒳 ×_𝒴 ℐ_𝒴) ×_𝒳 T` with `f ∘ x`. So `G ⟶ H`
is a base change of `T ×_𝒳 T ⟶ T ×_𝒴 T`, which is a base change of `Δ_f`, and every property of
morphisms of algebraic spaces passes from `Δ_f` to `G ⟶ H` — unramified and étale among them.
This is the remark's own reason, and it is why it asks the reader to compare with Stacks 0CPL.

## Main definitions

* `AlgebraicGeometry.Stack.HigherDiagonal.isomStack`: `Isom_𝒳(x₁, x₂)`, as a category fibred in
  groupoids over the big fppf site of `S`.
* `AlgebraicGeometry.Stack.HigherDiagonal.isomInclusion`: its inclusion into `T ×_𝒳 T`.
* `AlgebraicGeometry.Stack.HigherDiagonal.isomMap`: the map `Isom_𝒳(x₁, x₂) ⟶ Isom_𝒴(y₁, y₂)`.
* `AlgebraicGeometry.Stack.HigherDiagonal.isomSquare`: the square displayed above.

## Main results

* `AlgebraicGeometry.Stack.HigherDiagonal.isProper_mapBase_of_isSeparated`,
  `isQuasiCompactAndQuasiSeparated_mapBase`, `isLocallyQuasiFinite_mapBase_of_isQuasiDM` and
  `isUnramified_mapBase_of_isDM`: **Stacks 0CPL**, part (1).
* `AlgebraicGeometry.Stack.HigherDiagonal.isTwoFibreProduct_isomSquare`: the square is
  2-cartesian.
* `AlgebraicGeometry.Stack.HigherDiagonal.isProper_isomMap_of_isSeparated`,
  `isQuasiCompactAndQuasiSeparated_isomMap`, `isLocallyQuasiFinite_isomMap_of_isQuasiDM` and
  `isUnramified_isomMap_of_isDM`: **Stacks 0CPL**, part (2).
* `AlgebraicGeometry.Stack.HigherDiagonal.prop_isomMap_of_prop_relativeDiagonal`:
  **Stacks 0DU8**, for an arbitrary property of morphisms of algebraic spaces over `S`.

## Implementation notes

The unramified conclusions are written out longhand, as
`AlgebraicGeometry.Stack.AlgebraicStacks.isUnramified_mapBase_of_isDM` is: the library has
`AlgebraicGeometry.Stack.IsProper`, `.IsQuasiCompact`, `.IsQuasiSeparated` and
`.IsLocallyQuasiFinite` for the condition of Stacks 04XB but no abbreviation for it at
unramifiedness.

`AlgebraicGeometry.Stack.HigherDiagonal.restrictComparison` identifies a full subcategory with a
2-fibre product and is pure category theory; it is the only thing the 2-cartesianness of the
square needs beyond the fact that a vertical morphism of the category of elements of a presheaf
of sets has equal endpoints, which is what makes the two points of an object of `T ×_𝒴 T` equal
as soon as they are equal after an isomorphism.

## References

* [Stacks Project, Tag 0CPL](https://stacks.math.columbia.edu/tag/0CPL)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 050H](https://stacks.math.columbia.edu/tag/050H)
* [Stacks Project, Tag 06PP](https://stacks.math.columbia.edu/tag/06PP)
* [Stacks Project, Tag 06R5](https://stacks.math.columbia.edu/tag/06R5)
* [Stacks Project, Tag 0DU8](https://stacks.math.columbia.edu/tag/0DU8)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.HigherDiagonal

/-! ### A full subcategory as a 2-fibre product -/

section Restriction

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒜 : Type u₂} [Category.{v₂} 𝒜]
  {𝒟 : Type u₃} [Category.{v₃} 𝒟]
  (p : 𝒜 ⥤ 𝒞) (q : 𝒟 ⥤ 𝒞) (F : 𝒜 ⥤ 𝒟) (hF : F ⋙ q = p)
  (P : ObjectProperty 𝒜) (Q : ObjectProperty 𝒟) (hPQ : ∀ a, P a ↔ Q (F.obj a))

/-- The restriction of a functor `F` over `𝒞` to full subcategories cut out by properties that
`F` matches: on objects it is `F` itself. -/
def restrictFullSubcategory : P.FullSubcategory ⥤ Q.FullSubcategory :=
  Q.lift (P.ι ⋙ F) fun a => (hPQ a.obj).mp a.property

/-- **A full subcategory as a 2-fibre product.** The comparison functor from `P.FullSubcategory`
to the 2-fibre product `Q.FullSubcategory ×_{Q.ι, 𝒟, F} 𝒜` over `𝒞`: an object `a` of the former
is sent to `F a` on the first factor, to `a` itself on the second, and to the identity as
comparison isomorphism. -/
def restrictComparison :
    P.FullSubcategory ⥤ TwoFibreProductOver (Q.ι ⋙ q) p q Q.ι F where
  obj a :=
    { base := p.obj a.obj
      x := (restrictFullSubcategory F P Q hPQ).obj a
      y := a.obj
      hx := Functor.congr_obj hF a.obj
      hy := rfl
      iso := Iso.refl _
      vertical := IsHomLift.id (Functor.congr_obj hF a.obj) }
  map k :=
    { hbase := p.map k.hom
      a := (restrictFullSubcategory F P Q hPQ).map k
      b := k.hom
      ha := IsHomLift.of_fac' (Q.ι ⋙ q) _ _
        (Functor.congr_obj hF _) (Functor.congr_obj hF _) (Functor.congr_hom hF k.hom)
      hb := IsHomLift.map p k.hom
      w := by simp [restrictFullSubcategory] }
  map_id a := by apply TwoFibreProductOver.Hom.ext' <;> simp
  map_comp k l := by apply TwoFibreProductOver.Hom.ext' <;> simp

attribute [local implicit_reducible] restrictComparison restrictFullSubcategory

/-- **The comparison of `AlgebraicGeometry.Stack.HigherDiagonal.restrictComparison` is an
equivalence**, provided `Q` is stable under vertical isomorphism. Faithfulness and fullness are
those of the inclusion `P.ι` on the second factor; for essential surjectivity, an object
`(x, y, φ)` of the 2-fibre product has `Q (F y)` because `φ : Q.ι x ≅ F y` is vertical, hence
`P y`, and `φ⁻¹` is an isomorphism onto it from the image of `y`. -/
theorem isEquivalence_restrictComparison
    (hQ : ∀ (x y : 𝒟) (e : x ≅ y) (c : 𝒞), q.IsHomLift (𝟙 c) e.hom → Q x → Q y) :
    (restrictComparison p q F hF P Q hPQ).IsEquivalence := by
  refine { faithful := ⟨?_⟩, full := ⟨?_⟩, essSurj := ⟨?_⟩ }
  · intro a b k l h
    exact ObjectProperty.hom_ext _ (congrArg (fun t => t.b) h)
  · intro a b k
    refine ⟨ObjectProperty.homMk k.b, ?_⟩
    apply TwoFibreProductOver.Hom.ext'
    · exact ObjectProperty.hom_ext _ (by
        simpa [restrictComparison, restrictFullSubcategory] using k.w.symm)
    · rfl
  · intro t
    have hPt : P t.y :=
      (hPQ t.y).mpr (hQ t.x.obj (F.obj t.y) t.iso t.base t.vertical t.x.property)
    refine ⟨⟨t.y, hPt⟩, ?_⟩
    let k : (restrictComparison p q F hF P Q hPQ).obj ⟨t.y, hPt⟩ ⟶ t :=
      { hbase := eqToHom t.hy
        a := ObjectProperty.homMk t.iso.inv
        b := 𝟙 t.y
        ha := by
          have h₁ : q.IsHomLift (𝟙 t.base) t.iso.hom := t.vertical
          have h₂ : q.IsHomLift (𝟙 t.base) t.iso.inv := inferInstance
          refine IsHomLift.of_fac' (Q.ι ⋙ q) (eqToHom t.hy)
            (ObjectProperty.homMk t.iso.inv :
              ((restrictComparison p q F hF P Q hPQ).obj ⟨t.y, hPt⟩).x ⟶ t.x)
            (Functor.congr_obj hF t.y) t.hx ?_
          change q.map t.iso.inv = _
          rw [IsHomLift.fac' q (𝟙 t.base) t.iso.inv]
          simp only [Category.id_comp, eqToHom_trans]
        hb := by
          refine IsHomLift.of_fac' p _ _ rfl t.hy ?_
          simp [restrictComparison]
        w := by simp [restrictComparison, restrictFullSubcategory] }
    have : IsIso k := by
      refine TwoFibreProductOver.isIso_of_isIso_components _ _ _ _ _ k ?_ ?_
      · exact (ObjectProperty.isIso_hom_iff _).mp (inferInstanceAs (IsIso t.iso.inv))
      · exact inferInstanceAs (IsIso (𝟙 t.y))
    exact ⟨asIso k⟩

end Restriction

/-! ### Vertical morphisms of a category of elements -/

section Elements

universe vC uC

variable {C : Type uC} [Category.{vC} C]

/-- **A vertical morphism of the category of elements of a presheaf of sets has equal
endpoints**: both objects lie over the same object of `C` and name the same element, because the
element named by the source is the restriction of the one named by the target along an
identity. -/
theorem obj_eq_of_isHomLift_id (P : Cᵒᵖ ⥤ Type vC)
    {X Y : (presheafOfCategories (P ⋙ typeToCat)).obj} {c : C} (u : X ⟶ Y)
    (h : (PresheafOfCategories.discreteProjection P).IsHomLift (𝟙 c) u) : X = Y := by
  have hX : X.base = c :=
    IsHomLift.domain_eq (PresheafOfCategories.discreteProjection P) (𝟙 c) u
  have hY : Y.base = c :=
    IsHomLift.codomain_eq (PresheafOfCategories.discreteProjection P) (𝟙 c) u
  refine PresheafOfCategories.obj_eq_of_elementOf_eq hX hY ?_
  simpa using PresheafOfCategories.elementOf_eq_map hX hY (𝟙 c) u h

end Elements

/-! ### Stacks 0CPL -/

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)

section Points

variable (T₁ T₂ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  (hT₁ : IsAlgebraicSpace B S hS T₁) (hT₂ : IsAlgebraicSpace B S hS T₂)
  (x₁ : algebraicSpaceStack.{u, w} B S hS T₁ hT₁ ⟶ 𝒳)
  (x₂ : algebraicSpaceStack.{u, w} B S hS T₂ hT₂ ⟶ 𝒳)

/-- **Stacks 0CPL, part (1), the separated case.** If `f : 𝒳 ⟶ 𝒴` is separated then the
comparison `T₁ ×_{x₁, 𝒳, x₂} T₂ ⟶ T₁ ×_{y₁, 𝒴, y₂} T₂` of algebraic-space-valued points of `𝒳`
is proper, in the sense of Stacks 04XB.

This is Stacks 050H part (6) at a cospan whose two sources are algebraic spaces. -/
@[stacks 0CPL "part (1): proper"]
theorem isProper_mapBase_of_isSeparated (hf : AlgebraicStacks.IsSeparated B S hS f) :
    Stack.IsProper.{u, u, u + 1} B S hS (AlgebraicStacks.mapBase B S hS x₁ x₂ f).hom :=
  AlgebraicStacks.isProper_mapBase_of_isSeparated B S hS x₁ x₂ f hf

/-- **Stacks 0CPL, part (1), the quasi-separated case.** If `f : 𝒳 ⟶ 𝒴` is quasi-separated then
the comparison `T₁ ×_{x₁, 𝒳, x₂} T₂ ⟶ T₁ ×_{y₁, 𝒴, y₂} T₂` of algebraic-space-valued points of
`𝒳` is quasi-compact and quasi-separated, in the sense of Stacks 04XB.

This is Stacks 050H part (7) at a cospan whose two sources are algebraic spaces. -/
@[stacks 0CPL "part (1): quasi-compact and quasi-separated"]
theorem isQuasiCompactAndQuasiSeparated_mapBase
    (hf : AlgebraicStacks.IsQuasiSeparated B S hS f) :
    Stack.IsQuasiCompact.{u, u, u + 1} B S hS
        (AlgebraicStacks.mapBase B S hS x₁ x₂ f).hom ∧
      Stack.IsQuasiSeparated.{u, u, u + 1} B S hS
        (AlgebraicStacks.mapBase B S hS x₁ x₂ f).hom :=
  AlgebraicStacks.isQuasiCompactAndQuasiSeparated_mapBase B S hS x₁ x₂ f hf

/-- **Stacks 0CPL, part (1), the quasi-DM case.** If `f : 𝒳 ⟶ 𝒴` is quasi-DM then the comparison
`T₁ ×_{x₁, 𝒳, x₂} T₂ ⟶ T₁ ×_{y₁, 𝒴, y₂} T₂` of algebraic-space-valued points of `𝒳` is locally
quasi-finite, in the sense of Stacks 04XB.

This is Stacks 050H part (5) at a cospan whose two sources are algebraic spaces. -/
@[stacks 0CPL "part (1): locally quasi-finite"]
theorem isLocallyQuasiFinite_mapBase_of_isQuasiDM
    (hf : AlgebraicStacks.IsQuasiDM B S hS f) :
    Stack.IsLocallyQuasiFinite.{u, u, u + 1} B S hS
      (AlgebraicStacks.mapBase B S hS x₁ x₂ f).hom :=
  AlgebraicStacks.isLocallyQuasiFinite_mapBase_of_isQuasiDM B S hS x₁ x₂ f hf

/-- **Stacks 0CPL, part (1), the Deligne–Mumford case.** If `f : 𝒳 ⟶ 𝒴` is Deligne–Mumford then
the comparison `T₁ ×_{x₁, 𝒳, x₂} T₂ ⟶ T₁ ×_{y₁, 𝒴, y₂} T₂` of algebraic-space-valued points of
`𝒳` is unramified, in the sense of Stacks 04XB.

This is Stacks 050H part (4) at a cospan whose two sources are algebraic spaces. -/
@[stacks 0CPL "part (1): unramified"]
theorem isUnramified_mapBase_of_isDM (hf : Stack.IsDM B S hS f) :
    ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤
        (AlgebraicStacks.twoFibreProduct B S hS (x₁ ≫ f) (x₂ ≫ f)).val.val.obj)
      (_hz : z ⋙ (AlgebraicStacks.twoFibreProduct B S hS (x₁ ≫ f) (x₂ ≫ f)).val.val.p =
        Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (AlgebraicStacks.twoFibreProduct B S hS x₁ x₂).val.val.p
            (AlgebraicStacks.twoFibreProduct B S hS (x₁ ≫ f) (x₂ ≫ f)).val.val.p z
            (CatFiberedInGroupoids.homFunctor (AlgebraicStacks.mapBase B S hS x₁ x₂ f).hom))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Space.IsUnramified B S hS
          (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom :=
  AlgebraicStacks.isUnramified_mapBase_of_isDM B S hS x₁ x₂ f hf

end Points

section Isom

variable (T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hT : IsAlgebraicSpace B S hS T)

/-- **`Isom_𝒵(z₁, z₂)`, as a category fibred in groupoids over the big fppf site of `S`.** Its
objects are the vertical isomorphisms `z₁(t) ≅ z₂(t)` at a single point `t` of the algebraic
space `T`, i.e. the objects of `T ×_{z₁, 𝒵, z₂} T` whose two points of `T` agree; this is a
category fibred in groupoids by Stacks 06PP. -/
def isomStack {𝒵 : AlgebraicStacks.{u, w} B S hS}
    (z₁ z₂ : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒵) :
    CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk
    (BasedCategory.ofFunctor (absoluteIsomorphismDiagonalProjection B S hS T hT z₁ z₂))
    (isFiberedInGroupoids_absoluteIsomorphismDiagonal B S hS T hT z₁ z₂)

/-- **The inclusion `Isom_𝒵(z₁, z₂) ⟶ T ×_{z₁, 𝒵, z₂} T`** of the isomorphisms between the two
points into all isomorphisms between their values. -/
def isomInclusion {𝒵 : AlgebraicStacks.{u, w} B S hS}
    (z₁ z₂ : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒵) :
    isomStack B S hS T hT z₁ z₂ ⟶ (AlgebraicStacks.twoFibreProduct B S hS z₁ z₂).val :=
  Bicategory.InducedBicategory.mkHom ⟨ObjectProperty.ι _, rfl⟩

variable (x₁ x₂ : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)

/-- **The map `Isom_𝒳(x₁, x₂) ⟶ Isom_𝒴(y₁, y₂)` of Stacks 0CPL part (2)**, where `yᵢ = xᵢ ≫ f`:
it applies `f` to an isomorphism `x₁(t) ≅ x₂(t)`, keeping the point `t` of `T`. It is the
restriction of the comparison of part (1) to the isomorphisms between the two points, which the
comparison preserves because it keeps both points. -/
def isomMap :
    isomStack B S hS T hT x₁ x₂ ⟶ isomStack B S hS T hT (x₁ ≫ f) (x₂ ≫ f) :=
  Bicategory.InducedBicategory.mkHom
    ⟨restrictFullSubcategory (AlgebraicStacks.mapBase B S hS x₁ x₂ f).hom.hom.toFunctor
      (fun A => A.x = A.y) (fun A => A.x = A.y) (fun _ => Iff.rfl), rfl⟩

/-- **The square of Stacks 0CPL part (2)**: the map on isomorphism spaces over the comparison of
part (1), with the two inclusions of the isomorphisms between the two points as horizontal
arrows. It commutes strictly, both composites applying `f` to the comparison isomorphism and then
forgetting the diagonal condition. -/
def isomSquare :
    Bicategory.TwoCommSq (isomInclusion B S hS T hT (x₁ ≫ f) (x₂ ≫ f))
      (AlgebraicStacks.mapBase B S hS x₁ x₂ f).hom where
  pt := isomStack B S hS T hT x₁ x₂
  fst := isomMap B S hS f T hT x₁ x₂
  snd := isomInclusion B S hS T hT x₁ x₂
  iso := Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso (Iso.refl _) fun _ => IsHomLift.id rfl)

/-- **The diagonal condition is stable under vertical isomorphism.** If two objects of
`T ×_{z₁, 𝒵, z₂} T` are isomorphic over an identity and the two points of `T` of the first
agree, then so do those of the second: each component of the isomorphism is a vertical morphism
of the category of elements of `T`, hence has equal endpoints. -/
theorem diag_of_isHomLift_id_of_diag {𝒵 : AlgebraicStacks.{u, w} B S hS}
    (z₁ z₂ : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒵)
    (A D : (AlgebraicStacks.twoFibreProduct B S hS z₁ z₂).val.val.obj) (e : A ≅ D)
    (c : BigFppfOver B S hS)
    (he : (AlgebraicStacks.twoFibreProduct B S hS z₁ z₂).val.val.p.IsHomLift (𝟙 c) e.hom)
    (hA : A.x = A.y) : D.x = D.y := by
  have hAc : A.base = c :=
    IsHomLift.domain_eq (AlgebraicStacks.twoFibreProduct B S hS z₁ z₂).val.val.p (𝟙 c) e.hom
  have hDc : D.base = c :=
    IsHomLift.codomain_eq (AlgebraicStacks.twoFibreProduct B S hS z₁ z₂).val.val.p (𝟙 c) e.hom
  have hb : e.hom.hbase = eqToHom hAc ≫ eqToHom hDc.symm := by
    have hh : e.hom.hbase = eqToHom hAc ≫ 𝟙 c ≫ eqToHom hDc.symm :=
      IsHomLift.fac' (AlgebraicStacks.twoFibreProduct B S hS z₁ z₂).val.val.p (𝟙 c) e.hom
    simpa only [Category.id_comp] using hh
  have key : ∀ {X Y : (algebraicSpaceStack.{u, w} B S hS T hT).val.val.obj} (u : X ⟶ Y),
      (algebraicSpaceStack.{u, w} B S hS T hT).val.val.p.IsHomLift e.hom.hbase u →
      (algebraicSpaceStack.{u, w} B S hS T hT).val.val.p.obj X = c →
      (algebraicSpaceStack.{u, w} B S hS T hT).val.val.p.obj Y = c → X = Y := by
    intro X Y u hu hX hY
    refine obj_eq_of_isHomLift_id T u (c := c) ?_
    refine IsHomLift.of_fac' (algebraicSpaceStack.{u, w} B S hS T hT).val.val.p _ _ hX hY ?_
    rw [IsHomLift.fac' (algebraicSpaceStack.{u, w} B S hS T hT).val.val.p e.hom.hbase u]
    simp [hb]
  have hx := key e.hom.a e.hom.ha (A.hx.trans hAc) (D.hx.trans hDc)
  have hy := key e.hom.b e.hom.hb (A.hy.trans hAc) (D.hy.trans hDc)
  exact hx.symm.trans (hA.trans hy)

/-- **The comparison of the square of Stacks 0CPL part (2) into the canonical 2-fibre product is
an equivalence**: it is `AlgebraicGeometry.Stack.HigherDiagonal.restrictComparison` at the
diagonal condition, which `AlgebraicGeometry.Stack.HigherDiagonal.diag_of_isHomLift_id_of_diag`
shows to be stable under vertical isomorphism. -/
theorem isEquivalence_liftIsomSquare :
    (CatFiberedInGroupoids.liftTwoFibreProductSquare.{u, u, u + 1, u + 1}
        (isomInclusion B S hS T hT (x₁ ≫ f) (x₂ ≫ f))
        (AlgebraicStacks.mapBase B S hS x₁ x₂ f).hom
        (isomSquare B S hS f T hT x₁ x₂)).hom.toFunctor.IsEquivalence := by
  have h := isEquivalence_restrictComparison
    (AlgebraicStacks.twoFibreProduct B S hS x₁ x₂).val.val.p
    (AlgebraicStacks.twoFibreProduct B S hS (x₁ ≫ f) (x₂ ≫ f)).val.val.p
    (AlgebraicStacks.mapBase B S hS x₁ x₂ f).hom.hom.toFunctor rfl
    (fun A => A.x = A.y) (fun A => A.x = A.y) (fun _ => Iff.rfl)
    (diag_of_isHomLift_id_of_diag B S hS T hT (x₁ ≫ f) (x₂ ≫ f))
  exact h

/-- **The square of Stacks 0CPL part (2) is 2-cartesian**, so the map on isomorphism spaces is a
base change of the comparison of part (1). -/
noncomputable def isTwoFibreProduct_isomSquare :
    Bicategory.IsTwoFibreProduct (isomSquare B S hS f T hT x₁ x₂) :=
  Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (isomInclusion B S hS T hT (x₁ ≫ f) (x₂ ≫ f))
      (AlgebraicStacks.mapBase B S hS x₁ x₂ f).hom)
    (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u, u + 1, u + 1}
      (isomInclusion B S hS T hT (x₁ ≫ f) (x₂ ≫ f))
      (AlgebraicStacks.mapBase B S hS x₁ x₂ f).hom
      (isomSquare B S hS f T hT x₁ x₂))
    (isEquivalence_liftIsomSquare B S hS f T hT x₁ x₂)

/-- **The transfer of a condition of Stacks 04XB from the comparison of part (1) to the map on
isomorphism spaces**, for an arbitrary property `P` of morphisms of algebraic spaces over `S`:
the map on isomorphism spaces is a base change of the comparison. -/
theorem prop_isomMap_of_prop_mapBase (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (AlgebraicStacks.twoFibreProduct B S hS (x₁ ≫ f) (x₂ ≫ f)).val.val.obj)
      (_hy : y ⋙ (AlgebraicStacks.twoFibreProduct B S hS (x₁ ≫ f) (x₂ ≫ f)).val.val.p =
        Over.map U.hom)
      (G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hG : IsAlgebraicSpace B U.left.1 U.left.2 G),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (AlgebraicStacks.twoFibreProduct B S hS x₁ x₂).val.val.p
            (AlgebraicStacks.twoFibreProduct B S hS (x₁ ≫ f) (x₂ ≫ f)).val.val.p y
            (CatFiberedInGroupoids.homFunctor (AlgebraicStacks.mapBase B S hS x₁ x₂ f).hom))
          (presheafOfCategories (G ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨G, hG⟩))) :
    ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤
        (isomStack B S hS T hT (x₁ ≫ f) (x₂ ≫ f)).val.obj)
      (_hz : z ⋙ (isomStack B S hS T hT (x₁ ≫ f) (x₂ ≫ f)).val.p = Over.map U.hom)
      (G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hG : IsAlgebraicSpace B U.left.1 U.left.2 G),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (isomStack B S hS T hT x₁ x₂).val.p
            (isomStack B S hS T hT (x₁ ≫ f) (x₂ ≫ f)).val.p z
            (CatFiberedInGroupoids.homFunctor (isomMap B S hS f T hT x₁ x₂)))
          (presheafOfCategories (G ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨G, hG⟩)) :=
  prop_baseChange_of_isTwoFibreProduct.{u, u, u} B S hS P
    (AlgebraicStacks.twoFibreProduct B S hS x₁ x₂).val
    (AlgebraicStacks.twoFibreProduct B S hS (x₁ ≫ f) (x₂ ≫ f)).val
    (isomStack B S hS T hT (x₁ ≫ f) (x₂ ≫ f))
    (AlgebraicStacks.mapBase B S hS x₁ x₂ f).hom
    (isomInclusion B S hS T hT (x₁ ≫ f) (x₂ ≫ f))
    (isomSquare B S hS f T hT x₁ x₂) (isTwoFibreProduct_isomSquare B S hS f T hT x₁ x₂) hP

/-- **Stacks 0CPL, part (2), the separated case.** If `f : 𝒳 ⟶ 𝒴` is separated then the induced
map `Isom_𝒳(x₁, x₂) ⟶ Isom_𝒴(y₁, y₂)` is proper, in the sense of Stacks 04XB. -/
@[stacks 0CPL "part (2): proper"]
theorem isProper_isomMap_of_isSeparated (hf : AlgebraicStacks.IsSeparated B S hS f) :
    Stack.IsProper.{u, u, u + 1} B S hS (isomMap B S hS f T hT x₁ x₂) :=
  prop_isomMap_of_prop_mapBase B S hS f T hT x₁ x₂
    (fun _ _ m => Space.IsProper B S hS m.hom)
    (isProper_mapBase_of_isSeparated B S hS f T T hT hT x₁ x₂ hf)

/-- **Stacks 0CPL, part (2), the quasi-separated case.** If `f : 𝒳 ⟶ 𝒴` is quasi-separated then
the induced map `Isom_𝒳(x₁, x₂) ⟶ Isom_𝒴(y₁, y₂)` is quasi-compact and quasi-separated, in the
sense of Stacks 04XB. -/
@[stacks 0CPL "part (2): quasi-compact and quasi-separated"]
theorem isQuasiCompactAndQuasiSeparated_isomMap
    (hf : AlgebraicStacks.IsQuasiSeparated B S hS f) :
    Stack.IsQuasiCompact.{u, u, u + 1} B S hS (isomMap B S hS f T hT x₁ x₂) ∧
      Stack.IsQuasiSeparated.{u, u, u + 1} B S hS (isomMap B S hS f T hT x₁ x₂) :=
  ⟨prop_isomMap_of_prop_mapBase B S hS f T hT x₁ x₂
      (fun _ _ m => Space.IsQuasiCompact B S hS m.hom)
      (isQuasiCompactAndQuasiSeparated_mapBase B S hS f T T hT hT x₁ x₂ hf).1,
    prop_isomMap_of_prop_mapBase B S hS f T hT x₁ x₂
      (fun _ _ m => Space.IsQuasiSeparated B S hS m.hom)
      (isQuasiCompactAndQuasiSeparated_mapBase B S hS f T T hT hT x₁ x₂ hf).2⟩

/-- **Stacks 0CPL, part (2), the quasi-DM case.** If `f : 𝒳 ⟶ 𝒴` is quasi-DM then the induced
map `Isom_𝒳(x₁, x₂) ⟶ Isom_𝒴(y₁, y₂)` is locally quasi-finite, in the sense of Stacks 04XB. -/
@[stacks 0CPL "part (2): locally quasi-finite"]
theorem isLocallyQuasiFinite_isomMap_of_isQuasiDM
    (hf : AlgebraicStacks.IsQuasiDM B S hS f) :
    Stack.IsLocallyQuasiFinite.{u, u, u + 1} B S hS (isomMap B S hS f T hT x₁ x₂) :=
  prop_isomMap_of_prop_mapBase B S hS f T hT x₁ x₂
    (fun _ _ m => Space.IsLocallyQuasiFinite B S hS m.hom)
    (isLocallyQuasiFinite_mapBase_of_isQuasiDM B S hS f T T hT hT x₁ x₂ hf)

/-- **Stacks 0CPL, part (2), the Deligne–Mumford case.** If `f : 𝒳 ⟶ 𝒴` is Deligne–Mumford then
the induced map `Isom_𝒳(x₁, x₂) ⟶ Isom_𝒴(y₁, y₂)` is unramified, in the sense of
Stacks 04XB. -/
@[stacks 0CPL "part (2): unramified"]
theorem isUnramified_isomMap_of_isDM (hf : Stack.IsDM B S hS f) :
    ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤
        (isomStack B S hS T hT (x₁ ≫ f) (x₂ ≫ f)).val.obj)
      (_hz : z ⋙ (isomStack B S hS T hT (x₁ ≫ f) (x₂ ≫ f)).val.p = Over.map U.hom)
      (G : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hG : IsAlgebraicSpace B U.left.1 U.left.2 G),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (isomStack B S hS T hT x₁ x₂).val.p
            (isomStack B S hS T hT (x₁ ≫ f) (x₂ ≫ f)).val.p z
            (CatFiberedInGroupoids.homFunctor (isomMap B S hS f T hT x₁ x₂)))
          (presheafOfCategories (G ⋙ typeToCat)).p) →
        Space.IsUnramified B S hS
          (algebraicSpaceMap B S hS U
            ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨G, hG⟩)).hom :=
  prop_isomMap_of_prop_mapBase B S hS f T hT x₁ x₂
    (fun _ _ m => Space.IsUnramified B S hS m.hom)
    (isUnramified_mapBase_of_isDM B S hS f T T hT hT x₁ x₂ hf)

/-- **Stacks 0DU8.** Let `x : T ⟶ 𝒳` have an algebraic space as source, and let `G ⟶ H` be the
pullback to `T` of the stabilizer comparison `ℐ_𝒳 ⟶ 𝒳 ×_𝒴 ℐ_𝒴`, that is, the map
`G = Isom_𝒳(x, x) ⟶ Isom_𝒴(f ∘ x, f ∘ x) = H` on automorphism spaces. Then `G ⟶ H` satisfies a
condition of Stacks 04XB as soon as the relative diagonal `Δ_f` does, for an arbitrary property
`P` of morphisms of algebraic spaces over `S`: if `Δ_f` is unramified, étale, proper, … then so
is `G ⟶ H`.

The square `T ×_𝒳 T ⟶ 𝒳`, `T ×_𝒴 T ⟶ 𝒳 ×_𝒴 𝒳` over `Δ_f` is 2-cartesian, so `T ×_𝒳 T ⟶ T ×_𝒴 T`
is a base change of `Δ_f` (Stacks 050H), and `G ⟶ H` is a base change of that along the diagonal
of `T` (Stacks 0CPL, part (2)). -/
@[stacks 0DU8]
theorem prop_isomMap_of_prop_relativeDiagonal
    (x : algebraicSpaceStack.{u, w} B S hS T hT ⟶ 𝒳)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hP : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (AlgebraicStacks.twoFibreProduct B S hS f f).val.val.obj)
      (_hy : y ⋙ (AlgebraicStacks.twoFibreProduct B S hS f f).val.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.val.p
            (AlgebraicStacks.twoFibreProduct B S hS f f).val.val.p y
            (CatFiberedInGroupoids.homFunctor
              (Stack.relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val 𝒴.val f.hom)))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩))) :
    ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤
        (isomStack B S hS T hT (x ≫ f) (x ≫ f)).val.obj)
      (_hz : z ⋙ (isomStack B S hS T hT (x ≫ f) (x ≫ f)).val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (isomStack B S hS T hT x x).val.p
            (isomStack B S hS T hT (x ≫ f) (x ≫ f)).val.p z
            (CatFiberedInGroupoids.homFunctor (isomMap B S hS f T hT x x)))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        P (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)) :=
  prop_isomMap_of_prop_mapBase B S hS f T hT x x P
    (AlgebraicStacks.prop_mapBase_of_prop_relativeDiagonal B S hS x x f P hP)

end Isom

end AlgebraicGeometry.Stack.HigherDiagonal

end
