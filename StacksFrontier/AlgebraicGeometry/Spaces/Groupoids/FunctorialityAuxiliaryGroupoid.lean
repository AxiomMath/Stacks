module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialityAuxiliarySpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.Diagrams
public import StacksFrontier.Deformation.Groupoid.Loops

/-!
# The auxiliary groupoid of a morphism of groupoids in algebraic spaces

Let `φ : G ⟶ G'` be a morphism of groupoids in algebraic spaces over an algebraic space `B` over
a scheme `S` of a big fppf site, written `f : U ⟶ U'` on objects and `f : R ⟶ R'` on arrows.
Section 78.21 of the Stacks project attaches to `φ` the groupoid in algebraic spaces over `B`

```
U'' = U ×_{f, U', t'} R',      R'' = R ×_{f ∘ s, U', t'} R',
s''(r, r') = (s(r), r'),       t''(r, r') = (t(r), c'(f(r), r')),
c''((r₁, r'₁), (r₂, r'₂)) = (c(r₁, r₂), r'₂),
```

whose quotient stack Stacks 04Y4 identifies with the 2-fibre product of `[f] : [U/R] ⟶ [U'/R']`
with the projection `S_{U'} ⟶ [U'/R']`. The two spaces, their projections and `s''` are built in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/FunctorialityAuxiliarySpaces.lean`; this file
builds `t''` and `c''`, assembles the groupoid itself, and supplies the two morphisms out of it
that the square of Stacks 04Y4 is made of.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxTarget`: the target map `t''`, which on points
  sends `(r, r')` to `(t(r), c'(f(r), r'))`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxComp`: the composition `c''`, which on points
  sends `((r₁, r'₁), (r₂, r'₂))` to `(c(r₁, r₂), r'₂)`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxGroupoid`: the groupoid in algebraic spaces
  `(U'', R'', s'', t'', c'')` of Section 78.21.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxHom`: the morphism
  `g : (U'', R'', s'', t'', c'') ⟶ (U, R, s, t, c)` given by the two first projections.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxToTargetObjects`: the morphism `U'' ⟶ U'`
  sending `(u, r')` to `s'(r')`, which exhibits the auxiliary groupoid as a groupoid over `U'`.

## Main results

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxToTargetObjects_invariant`: that morphism takes
  the same value on the source and the target of every arrow of the auxiliary groupoid, which is
  what makes it descend to the quotient stack.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxPointwiseGroupoid`: the evaluation of
  `(U'', R'', s'', t'', c'')` at a test object is a groupoid. This is the content of the
  construction, and the reason the five maps above assemble into a groupoid at all.

## Implementation notes

The pointwise groupoid condition is the only thing in the construction that is not a formal
consequence of the universal properties of the two fibre products, and it is proved by exhibiting
the evaluated groupoid in a form in which its groupoid laws are visible.

`AlgebraicGeometry.AuxPoint` is that form. For a functor `F : A ⥤ Bb` its objects are an object
`x` of `A` together with an arrow of `Bb` with target `F x`, and an arrow `P ⟶ Q` is an arrow
`r : P.obj ⟶ Q.obj` of `A` together with the equality `P.arr ≫ F.map r = Q.arr` of arrows of
`Bb`. That equality does not typecheck on the nose, the two sides having different sources, so
the equality of the sources is carried as a field and the comparison is inserted; it is a field
and not a side condition because `AlgebraicGeometry.AuxHom` is then a plain structure whose
`arrow` field determines it, equality of proofs being no information. Composition, the identity
and the inverse are those of `A`, and every law of `AlgebraicGeometry.AuxPoint` reduces by
`AlgebraicGeometry.AuxHom.ext'` to the corresponding law of `A`; nothing about `Bb` beyond
functoriality of `F` is used.

With `A` the evaluated groupoid of `G` at a test object `T`, `Bb` the evaluated groupoid of `G'`
at `T` and `F` the evaluated functor of `φ`, the points of `U''` over `T` index objects of
`AuxPoint F` — the arrow being the second projection of the point, whose target is the first
projection's image by the defining square of `U''` — and
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxArrowEquiv` identifies the arrows of
`AuxPoint F` between two such objects with the points of `R''` having the prescribed source and
target. The identification is where `t''` is used: an arrow of `AuxPoint F` out of the object
indexed by `(u, r')` carries the equality `c'(f(r), r') = r'₁`, which is exactly the second
component of `t''`.

Points of a fibre product of algebraic spaces over a test object are compared with pairs of
points by `AlgebraicGeometry.Space.fiberProductAtEquiv`, limits of presheaves being computed
pointwise; `AlgebraicGeometry.GroupoidInAlgebraicSpaces.fibreProduct_ext` and
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.fibreProductMk` are the resulting extensionality
principle and constructor, and `auxObjects_ext`, `auxArrows_ext` and `auxArrowOfHom` their
instances for the two spaces at hand.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 043Z](https://stacks.math.columbia.edu/tag/043Z)
* [Stacks Project, Tag 04P9](https://stacks.math.columbia.edu/tag/04P9)
* [Stacks Project, Tag 04Y4](https://stacks.math.columbia.edu/tag/04Y4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u u₁ u₂ v₁ v₂ u₃ v₃ w₃

namespace AlgebraicGeometry

/-! ### The comma-style groupoid in which the pointwise laws are visible -/

/-- An object `x` of `A` together with an arrow of `Bb` whose target is `F x`. For `F` the
evaluated functor of a morphism of groupoids in algebraic spaces this is the shape of a point of
the space `U''` of Section 78.21. -/
structure AuxPoint {A : Type u₁} [Category.{v₁} A] {Bb : Type u₂} [Category.{v₂} Bb]
    (F : A ⥤ Bb) where
  /-- The object of `A`. -/
  obj : A
  /-- The source of the arrow of `Bb`. -/
  src : Bb
  /-- The arrow of `Bb` with target `F obj`. -/
  arr : src ⟶ F.obj obj

variable {A : Type u₁} [Category.{v₁} A] {Bb : Type u₂} [Category.{v₂} Bb] {F : A ⥤ Bb}

/-- An arrow of `AlgebraicGeometry.AuxPoint`: an arrow of `A` between the two objects which
carries the arrow of `Bb` of the source to the arrow of `Bb` of the target. The equality of the
sources of those two arrows is a consequence of that condition, and is carried as a field so
that the condition typechecks. -/
structure AuxHom (P Q : AuxPoint F) where
  /-- The two arrows of `Bb` have the same source. -/
  base : P.src = Q.src
  /-- The arrow of `A`. -/
  arrow : P.obj ⟶ Q.obj
  /-- The arrow of `A` carries the arrow of the source to the arrow of the target. -/
  w : P.arr ≫ F.map arrow = eqToHom base ≫ Q.arr

/-- An arrow of `AlgebraicGeometry.AuxPoint` is determined by its arrow of `A`. -/
theorem AuxHom.ext' {P Q : AuxPoint F} {m n : AuxHom P Q} (h : m.arrow = n.arrow) : m = n := by
  obtain ⟨b₁, a₁, w₁⟩ := m
  obtain ⟨b₂, a₂, w₂⟩ := n
  cases h
  cases Subsingleton.elim b₁ b₂
  rfl

/-- The category structure on `AlgebraicGeometry.AuxPoint F`, with arrows
`AlgebraicGeometry.AuxHom` and identities and composition those of `A`. -/
instance AuxPoint.category : Category.{v₁} (AuxPoint F) where
  Hom := AuxHom
  id P := ⟨rfl, 𝟙 P.obj, by simp⟩
  comp {P Q R} m n :=
    ⟨m.base.trans n.base, m.arrow ≫ n.arrow, by
      rw [F.map_comp, ← Category.assoc, m.w, Category.assoc, n.w, ← Category.assoc,
        eqToHom_trans]⟩
  id_comp m := AuxHom.ext' (Category.id_comp m.arrow)
  comp_id m := AuxHom.ext' (Category.comp_id m.arrow)
  assoc m n p := AuxHom.ext' (Category.assoc m.arrow n.arrow p.arrow)

/-- The arrow of `A` underlying the identity of `P` is the identity of `P.obj`. -/
@[simp]
theorem AuxPoint.id_arrow (P : AuxPoint F) : AuxHom.arrow (𝟙 P) = 𝟙 P.obj := rfl

/-- The arrow of `A` underlying a composite is the composite of the underlying arrows. -/
@[simp]
theorem AuxPoint.comp_arrow {P Q R : AuxPoint F} (m : P ⟶ Q) (n : Q ⟶ R) :
    (m ≫ n).arrow = m.arrow ≫ n.arrow := rfl

section Inverse

variable {A' : Type u₁} [Groupoid.{v₁} A'] {F' : A' ⥤ Bb}

/-- The inverse of an arrow of `AlgebraicGeometry.AuxPoint`, when `A` is a groupoid. -/
def AuxHom.inv {P Q : AuxPoint F'} (m : AuxHom P Q) : AuxHom Q P where
  base := m.base.symm
  arrow := Groupoid.inv m.arrow
  w := by
    have h : Q.arr = eqToHom m.base.symm ≫ P.arr ≫ F'.map m.arrow := by
      rw [m.w, ← Category.assoc, eqToHom_trans]
      simp
    rw [h, Category.assoc, Category.assoc, ← F'.map_comp, Groupoid.comp_inv, F'.map_id,
      Category.comp_id]

/-- `AlgebraicGeometry.AuxPoint F'` is a groupoid when `A'` is, the inverse of an arrow being
`AlgebraicGeometry.AuxHom.inv`. -/
instance AuxPoint.groupoid : Groupoid.{v₁} (AuxPoint F') where
  inv m := AuxHom.inv m
  inv_comp m := AuxHom.ext' (by
    change Groupoid.inv m.arrow ≫ m.arrow = _
    simp)
  comp_inv m := AuxHom.ext' (by
    change m.arrow ≫ Groupoid.inv m.arrow = _
    simp)

end Inverse

namespace GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B}

/-! ### The target map `t''` -/

/-- The composable pair `(f(r), r')` of arrows of `G'` attached to a point `(r, r')` of `R''`:
the two are composable because `s'(f(r)) = f(s(r)) = t'(r')`, which is the defining condition
of `R''`. -/
noncomputable def auxComposable (φ : Hom G G') :
    auxArrows φ ⟶ AlgebraicSpaces.fiberProduct C S hS G'.source G'.target :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G'.source G'.target).lift
    (auxArrowsFst φ ≫ φ.arrowsMap) (auxArrowsSnd φ) (by
      rw [Category.assoc, φ.arrowsMap_comp_source]
      exact (isPullback_auxArrows φ).w)

/-- The first component of `auxComposable φ` is `(r, r') ↦ f(r)`. -/
@[simp]
theorem auxComposable_comp_fst (φ : Hom G G') :
    auxComposable φ ≫ (ObjectProperty.homMk (pullback.fst G'.source.hom G'.target.hom) :
        AlgebraicSpaces.fiberProduct C S hS G'.source G'.target ⟶ G'.arrows) =
      auxArrowsFst φ ≫ φ.arrowsMap :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G'.source G'.target).lift_fst _ _ _

/-- The second component of `auxComposable φ` is `(r, r') ↦ r'`. -/
@[simp]
theorem auxComposable_comp_snd (φ : Hom G G') :
    auxComposable φ ≫ (ObjectProperty.homMk (pullback.snd G'.source.hom G'.target.hom) :
        AlgebraicSpaces.fiberProduct C S hS G'.source G'.target ⟶ G'.arrows) =
      auxArrowsSnd φ :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G'.source G'.target).lift_snd _ _ _

/-- The second component `(r, r') ↦ c'(f(r), r')` of the target map `t''`. -/
noncomputable def auxTargetSnd (φ : Hom G G') : auxArrows φ ⟶ G'.arrows :=
  auxComposable φ ≫ G'.comp

/-- The target map `t'' : R'' ⟶ U''` of the groupoid of Section 78.21. On points it sends a pair
`(r, r')` with `t'(r') = f(s(r))` to the pair `(t(r), c'(f(r), r'))`. -/
noncomputable def auxTarget (φ : Hom G G') : auxArrows φ ⟶ auxObjects φ :=
  (isPullback_auxObjects φ).lift (auxArrowsFst φ ≫ G.target) (auxTargetSnd φ) (by
    calc (auxArrowsFst φ ≫ G.target) ≫ φ.objectsMap
        = auxArrowsFst φ ≫ φ.arrowsMap ≫ G'.target := by
          rw [Category.assoc, ← φ.arrowsMap_comp_target]
      _ = (auxComposable φ ≫ (ObjectProperty.homMk
            (pullback.fst G'.source.hom G'.target.hom) :
              AlgebraicSpaces.fiberProduct C S hS G'.source G'.target ⟶ G'.arrows)) ≫
            G'.target := by
          rw [auxComposable_comp_fst, Category.assoc]
      _ = (auxComposable φ ≫ G'.comp) ≫ G'.target := by
          rw [Category.assoc, Category.assoc, (Space.isPullback_fst_comp G').w]
      _ = auxTargetSnd φ ≫ G'.target := rfl)

/-- The first projection of `t''` is `(r, r') ↦ t(r)`. -/
@[simp]
theorem auxTarget_comp_auxObjectsFst (φ : Hom G G') :
    auxTarget φ ≫ auxObjectsFst φ = auxArrowsFst φ ≫ G.target :=
  (isPullback_auxObjects φ).lift_fst _ _ _

/-- The second projection of `t''` is `(r, r') ↦ c'(f(r), r')`. -/
@[simp]
theorem auxTarget_comp_auxObjectsSnd (φ : Hom G G') :
    auxTarget φ ≫ auxObjectsSnd φ = auxTargetSnd φ :=
  (isPullback_auxObjects φ).lift_snd _ _ _

/-! ### The composition `c''` -/

section Comp

variable (φ : Hom G G')

/-- The first projection of the space of composable pairs of arrows of the groupoid of
Section 78.21. -/
noncomputable abbrev auxFirstArrow :
    AlgebraicSpaces.fiberProduct C S hS (auxSource φ) (auxTarget φ) ⟶ auxArrows φ :=
  ObjectProperty.homMk (pullback.fst (auxSource φ).hom (auxTarget φ).hom)

/-- The second projection of the space of composable pairs of arrows of the groupoid of
Section 78.21. -/
noncomputable abbrev auxSecondArrow :
    AlgebraicSpaces.fiberProduct C S hS (auxSource φ) (auxTarget φ) ⟶ auxArrows φ :=
  ObjectProperty.homMk (pullback.snd (auxSource φ).hom (auxTarget φ).hom)

/-- A composable pair of arrows of the groupoid of Section 78.21 has composable first
projections in `G`. -/
theorem auxFirstArrow_comp_source :
    (auxFirstArrow φ ≫ auxArrowsFst φ) ≫ G.source =
      (auxSecondArrow φ ≫ auxArrowsFst φ) ≫ G.target := by
  calc (auxFirstArrow φ ≫ auxArrowsFst φ) ≫ G.source
      = auxFirstArrow φ ≫ auxSource φ ≫ auxObjectsFst φ := by
        rw [auxSource_comp_auxObjectsFst, Category.assoc]
    _ = auxSecondArrow φ ≫ auxTarget φ ≫ auxObjectsFst φ := by
        rw [← Category.assoc, ← Category.assoc,
          (AlgebraicSpaces.isPullback_fiberProduct C S hS (auxSource φ) (auxTarget φ)).w]
    _ = (auxSecondArrow φ ≫ auxArrowsFst φ) ≫ G.target := by
        rw [auxTarget_comp_auxObjectsFst, Category.assoc]

/-- The composable pair of arrows of `G` underlying a composable pair of arrows of the groupoid
of Section 78.21. -/
noncomputable def auxCompPair :
    AlgebraicSpaces.fiberProduct C S hS (auxSource φ) (auxTarget φ) ⟶
      AlgebraicSpaces.fiberProduct C S hS G.source G.target :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).lift
    (auxFirstArrow φ ≫ auxArrowsFst φ) (auxSecondArrow φ ≫ auxArrowsFst φ)
    (auxFirstArrow_comp_source φ)

/-- The first arrow of `auxCompPair φ` is the first projection of the first arrow of the pair. -/
@[simp]
theorem auxCompPair_comp_fst :
    auxCompPair φ ≫ (ObjectProperty.homMk (pullback.fst G.source.hom G.target.hom) :
        AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows) =
      auxFirstArrow φ ≫ auxArrowsFst φ :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).lift_fst _ _ _

/-- The second arrow of `auxCompPair φ` is the first projection of the second arrow of the
pair. -/
@[simp]
theorem auxCompPair_comp_snd :
    auxCompPair φ ≫ (ObjectProperty.homMk (pullback.snd G.source.hom G.target.hom) :
        AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows) =
      auxSecondArrow φ ≫ auxArrowsFst φ :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source G.target).lift_snd _ _ _

/-- The composition `c'' : R'' ×_{s'', U'', t''} R'' ⟶ R''` of the groupoid of Section 78.21.
On points it sends `((r₁, r'₁), (r₂, r'₂))` to `(c(r₁, r₂), r'₂)`. -/
noncomputable def auxComp :
    AlgebraicSpaces.fiberProduct C S hS (auxSource φ) (auxTarget φ) ⟶ auxArrows φ :=
  (isPullback_auxArrows φ).lift (auxCompPair φ ≫ G.comp)
    (auxSecondArrow φ ≫ auxArrowsSnd φ) (by
      have h : (auxCompPair φ ≫ G.comp) ≫ G.source =
          (auxSecondArrow φ ≫ auxArrowsFst φ) ≫ G.source := by
        rw [Category.assoc, (Space.isPullback_comp_source G).w, ← Category.assoc,
          auxCompPair_comp_snd]
      rw [← Category.assoc, h]
      simpa only [Category.assoc] using congrArg (auxSecondArrow φ ≫ ·) (isPullback_auxArrows φ).w)

/-- The first projection of `c''` is `((r₁, r'₁), (r₂, r'₂)) ↦ c(r₁, r₂)`. -/
@[simp]
theorem auxComp_comp_auxArrowsFst :
    auxComp φ ≫ auxArrowsFst φ = auxCompPair φ ≫ G.comp :=
  (isPullback_auxArrows φ).lift_fst _ _ _

/-- The second projection of `c''` is `((r₁, r'₁), (r₂, r'₂)) ↦ r'₂`. -/
@[simp]
theorem auxComp_comp_auxArrowsSnd :
    auxComp φ ≫ auxArrowsSnd φ = auxSecondArrow φ ≫ auxArrowsSnd φ :=
  (isPullback_auxArrows φ).lift_snd _ _ _

end Comp

/-! ### Points of the two spaces over a test object -/

/-- A point of a fibre product of algebraic spaces over a test object is determined by its two
projections, limits of presheaves being computed pointwise. -/
theorem fibreProduct_ext {F₁ F₂ H₁ : AlgebraicSpaces C S hS} (f : F₁ ⟶ H₁) (g : F₂ ⟶ H₁)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    {x y : (AlgebraicSpaces.fiberProduct C S hS f g).obj.obj T}
    (h₁ : (pullback.fst f.hom g.hom).app T x = (pullback.fst f.hom g.hom).app T y)
    (h₂ : (pullback.snd f.hom g.hom).app T x = (pullback.snd f.hom g.hom).app T y) : x = y := by
  refine (Space.fiberProductAtEquiv f g T).injective (Subtype.ext (Prod.ext ?_ ?_))
  · rw [Space.fiberProductAtEquiv_fst, Space.fiberProductAtEquiv_fst, h₁]
  · rw [Space.fiberProductAtEquiv_snd, Space.fiberProductAtEquiv_snd, h₂]

/-- A point of a fibre product of algebraic spaces over a test object from its two
projections. -/
noncomputable def fibreProductMk {F₁ F₂ H₁ : AlgebraicSpaces C S hS} (f : F₁ ⟶ H₁) (g : F₂ ⟶ H₁)
    (T : (BigFppfOver C S hS)ᵒᵖ) (x : F₁.obj.obj T) (y : F₂.obj.obj T)
    (h : f.hom.app T x = g.hom.app T y) :
    (AlgebraicSpaces.fiberProduct C S hS f g).obj.obj T :=
  (Space.fiberProductAtEquiv f g T).symm ⟨(x, y), h⟩

/-- The first projection of `fibreProductMk f g T x y h` is `x`. -/
@[simp]
theorem fibreProductMk_fst {F₁ F₂ H₁ : AlgebraicSpaces C S hS} (f : F₁ ⟶ H₁) (g : F₂ ⟶ H₁)
    (T : (BigFppfOver C S hS)ᵒᵖ) (x : F₁.obj.obj T) (y : F₂.obj.obj T)
    (h : f.hom.app T x = g.hom.app T y) :
    (pullback.fst f.hom g.hom).app T (fibreProductMk f g T x y h) = x := by
  have hx := Space.fiberProductAtEquiv_fst f g T (fibreProductMk f g T x y h)
  rw [fibreProductMk, Equiv.apply_symm_apply] at hx
  exact hx.symm

/-- The second projection of `fibreProductMk f g T x y h` is `y`. -/
@[simp]
theorem fibreProductMk_snd {F₁ F₂ H₁ : AlgebraicSpaces C S hS} (f : F₁ ⟶ H₁) (g : F₂ ⟶ H₁)
    (T : (BigFppfOver C S hS)ᵒᵖ) (x : F₁.obj.obj T) (y : F₂.obj.obj T)
    (h : f.hom.app T x = g.hom.app T y) :
    (pullback.snd f.hom g.hom).app T (fibreProductMk f g T x y h) = y := by
  have hy := Space.fiberProductAtEquiv_snd f g T (fibreProductMk f g T x y h)
  rw [fibreProductMk, Equiv.apply_symm_apply] at hy
  exact hy.symm

/-- The composition of a groupoid in algebraic spaces, read on a point of the chosen fibre
product through its two projections. -/
theorem comp_app_eq_compose (K : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (z : (AlgebraicSpaces.fiberProduct C S hS K.source K.target).obj.obj T)
    {x y : K.arrows.obj.obj T} (h : K.source.hom.app T x = K.target.hom.app T y)
    (h₁ : (pullback.fst K.source.hom K.target.hom).app T z = x)
    (h₂ : (pullback.snd K.source.hom K.target.hom).app T z = y) :
    K.comp.hom.app T z = K.toGroupoidInFunctors.compose T x y h := by
  have hz : z = (composableToPullback K.source.hom K.target.hom).app T ⟨(x, y), h⟩ :=
    fibreProduct_ext K.source K.target T
      (by rw [h₁, pullbackFst_app_composableToPullback])
      (by rw [h₂, pullbackSnd_app_composableToPullback])
  rw [hz]
  rfl

/-- Equal morphisms of algebraic spaces agree at every point over a test object. -/
private theorem hom_app_congr {X Y : AlgebraicSpaces C S hS} {f g : X ⟶ Y} (h : f = g)
    (T : (BigFppfOver C S hS)ᵒᵖ) (x : X.obj.obj T) : f.hom.app T x = g.hom.app T x :=
  natTrans_app_congr (congrArg (fun k => k.hom) h) T x

/-! ### The pointwise groupoid -/

section Pointwise

variable (φ : Hom G G') (T : (BigFppfOver C S hS)ᵒᵖ)

/-- The two projections of a point of `R''` are a composable pair of arrows of `G'` after `f`. -/
theorem auxArrows_composable (a : (auxArrows φ).obj.obj T) :
    G'.source.hom.app T (φ.toGroupoidHom.mapArrows.app T ((auxArrowsFst φ).hom.app T a)) =
      G'.target.hom.app T ((auxArrowsSnd φ).hom.app T a) :=
  (φ.toGroupoidHom.map_source T ((auxArrowsFst φ).hom.app T a)).trans <|
    hom_app_congr (isPullback_auxArrows φ).w T a

/-- The target of the second projection of a point of `U''` is the image of its first
projection. -/
theorem auxObjects_target_app (P : (auxObjects φ).obj.obj T) :
    G'.target.hom.app T ((auxObjectsSnd φ).hom.app T P) =
      φ.toGroupoidHom.mapObjects.app T ((auxObjectsFst φ).hom.app T P) :=
  (hom_app_congr (isPullback_auxObjects φ).w T P).symm

/-- The second component of `t''` on a point of `R''`. -/
theorem auxTargetSnd_app (a : (auxArrows φ).obj.obj T) :
    (auxTargetSnd φ).hom.app T a =
      G'.toGroupoidInFunctors.compose T
        (φ.toGroupoidHom.mapArrows.app T ((auxArrowsFst φ).hom.app T a))
        ((auxArrowsSnd φ).hom.app T a) (auxArrows_composable φ T a) :=
  comp_app_eq_compose G' T ((auxComposable φ).hom.app T a) (auxArrows_composable φ T a)
    (hom_app_congr (auxComposable_comp_fst φ) T a)
    (hom_app_congr (auxComposable_comp_snd φ) T a)

/-- The first projection of `s''` on a point of `R''`. -/
theorem auxSource_app_fst (a : (auxArrows φ).obj.obj T) :
    (auxObjectsFst φ).hom.app T ((auxSource φ).hom.app T a) =
      G.source.hom.app T ((auxArrowsFst φ).hom.app T a) :=
  hom_app_congr (auxSource_comp_auxObjectsFst φ) T a

/-- The second projection of `s''` on a point of `R''`. -/
theorem auxSource_app_snd (a : (auxArrows φ).obj.obj T) :
    (auxObjectsSnd φ).hom.app T ((auxSource φ).hom.app T a) =
      (auxArrowsSnd φ).hom.app T a :=
  hom_app_congr (auxSource_comp_auxObjectsSnd φ) T a

/-- The first projection of `t''` on a point of `R''`. -/
theorem auxTarget_app_fst (a : (auxArrows φ).obj.obj T) :
    (auxObjectsFst φ).hom.app T ((auxTarget φ).hom.app T a) =
      G.target.hom.app T ((auxArrowsFst φ).hom.app T a) :=
  hom_app_congr (auxTarget_comp_auxObjectsFst φ) T a

/-- The second projection of `t''` on a point of `R''`. -/
theorem auxTarget_app_snd (a : (auxArrows φ).obj.obj T) :
    (auxObjectsSnd φ).hom.app T ((auxTarget φ).hom.app T a) =
      (auxTargetSnd φ).hom.app T a :=
  hom_app_congr (auxTarget_comp_auxObjectsSnd φ) T a

/-- Two arrows of an evaluated groupoid with the same target and with sources identified by an
equality agree up to that identification as soon as they represent the same arrow. -/
theorem evaluationArrow_eq_of_val {D : Type u₃} [Category.{v₃} D]
    (K : Deformation.GroupoidInFunctors.{u₃, v₃, w₃} D) (Tt : D) {x y z : K.Evaluation Tt}
    (h : x = y) (m : x ⟶ z) (n : y ⟶ z)
    (hmn : (K.evaluationArrowEquiv Tt x z m).1 = (K.evaluationArrowEquiv Tt y z n).1) :
    m = eqToHom h ≫ n := by
  cases h
  rw [eqToHom_refl, Category.id_comp]
  exact (K.evaluationArrowEquiv Tt x z).injective (Subtype.ext hmn)

/-- The converse: two such arrows that agree up to the identification represent the same
arrow. -/
theorem evaluationArrow_val_of_eq {D : Type u₃} [Category.{v₃} D]
    (K : Deformation.GroupoidInFunctors.{u₃, v₃, w₃} D) (Tt : D) {x y z : K.Evaluation Tt}
    (h : x = y) {m : x ⟶ z} {n : y ⟶ z} (hmn : m = eqToHom h ≫ n) :
    (K.evaluationArrowEquiv Tt x z m).1 = (K.evaluationArrowEquiv Tt y z n).1 := by
  cases h
  rw [eqToHom_refl, Category.id_comp] at hmn
  rw [hmn]

/-- The evaluated functor of `φ` at a test object. -/
noncomputable abbrev auxEval :
    G.toGroupoidInFunctors.Evaluation T ⥤ G'.toGroupoidInFunctors.Evaluation T :=
  φ.toGroupoidHom.evaluation T

/-- The object of `AlgebraicGeometry.AuxPoint` indexed by a point of `U''` over a test object:
its first projection, together with its second projection read as an arrow of the evaluated
groupoid of `G'` with target the image of the first. -/
noncomputable def auxIndex (P : (auxObjects φ).obj.obj T) : AuxPoint (auxEval φ T) where
  obj := (auxObjectsFst φ).hom.app T P
  src := G'.source.hom.app T ((auxObjectsSnd φ).hom.app T P)
  arr := (G'.toGroupoidInFunctors.evaluationArrowEquiv T _ _).symm
    ⟨(auxObjectsSnd φ).hom.app T P, rfl, auxObjects_target_app φ T P⟩

/-- The object of `A` of `auxIndex φ T P` is the first projection of `P`. -/
@[simp]
theorem auxIndex_obj (P : (auxObjects φ).obj.obj T) :
    (auxIndex φ T P).obj = (auxObjectsFst φ).hom.app T P := rfl

/-- The arrow of `auxIndex φ T P` is represented by the second projection of `P`. -/
@[simp]
theorem auxIndex_arr_val (P : (auxObjects φ).obj.obj T) :
    (G'.toGroupoidInFunctors.evaluationArrowEquiv T _ _ (auxIndex φ T P).arr).1 =
      (auxObjectsSnd φ).hom.app T P :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- A point of `R''` whose first projection represents a given arrow of the evaluated groupoid
of `G` out of the first projection of `P`. -/
noncomputable def auxArrowOfHom {P Q : (auxObjects φ).obj.obj T}
    (r : (auxIndex φ T P).obj ⟶ (auxIndex φ T Q).obj) : (auxArrows φ).obj.obj T :=
  fibreProductMk (G.source ≫ φ.objectsMap) G'.target T
    (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ r).1
    ((auxObjectsSnd φ).hom.app T P)
    (((congrArg (φ.toGroupoidHom.mapObjects.app T)
      (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ r).2.1).trans
        (auxObjects_target_app φ T P).symm))

/-- The first projection of `auxArrowOfHom φ T r` is the point of `R` representing `r`. -/
@[simp]
theorem auxArrowOfHom_fst {P Q : (auxObjects φ).obj.obj T}
    (r : (auxIndex φ T P).obj ⟶ (auxIndex φ T Q).obj) :
    (auxArrowsFst φ).hom.app T (auxArrowOfHom φ T r) =
      (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ r).1 :=
  fibreProductMk_fst _ _ _ _ _ _

/-- The second projection of `auxArrowOfHom φ T r` is the second projection of `P`. -/
@[simp]
theorem auxArrowOfHom_snd {P Q : (auxObjects φ).obj.obj T}
    (r : (auxIndex φ T P).obj ⟶ (auxIndex φ T Q).obj) :
    (auxArrowsSnd φ).hom.app T (auxArrowOfHom φ T r) = (auxObjectsSnd φ).hom.app T P :=
  fibreProductMk_snd _ _ _ _ _ _

/-- A point of `U''` is determined by its two projections. -/
theorem auxObjects_ext {P Q : (auxObjects φ).obj.obj T}
    (h₁ : (auxObjectsFst φ).hom.app T P = (auxObjectsFst φ).hom.app T Q)
    (h₂ : (auxObjectsSnd φ).hom.app T P = (auxObjectsSnd φ).hom.app T Q) : P = Q :=
  fibreProduct_ext φ.objectsMap G'.target T h₁ h₂

/-- A point of `R''` is determined by its two projections. -/
theorem auxArrows_ext {a b : (auxArrows φ).obj.obj T}
    (h₁ : (auxArrowsFst φ).hom.app T a = (auxArrowsFst φ).hom.app T b)
    (h₂ : (auxArrowsSnd φ).hom.app T a = (auxArrowsSnd φ).hom.app T b) : a = b :=
  fibreProduct_ext (G.source ≫ φ.objectsMap) G'.target T h₁ h₂

/-- **Arrows of `AlgebraicGeometry.AuxPoint` between two indexed points are exactly the points
of `R''` with the prescribed source and target.** The condition carried by an arrow of
`AuxPoint` is `c'(f(r), r') = r'₁`, which is the second component of `t''`; so the points of
`R''` with source `P` and target `Q` are the arrows `P.obj ⟶ Q.obj` satisfying it. -/
noncomputable def auxArrowEquiv (P Q : (auxObjects φ).obj.obj T) :
    (auxIndex φ T P ⟶ auxIndex φ T Q) ≃
      {a : (auxArrows φ).obj.obj T //
        (auxSource φ).hom.app T a = P ∧ (auxTarget φ).hom.app T a = Q} where
  toFun m :=
    ⟨auxArrowOfHom φ T m.arrow,
      auxObjects_ext φ T
        (by
          rw [auxSource_app_fst, auxArrowOfHom_fst]
          exact (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ m.arrow).2.1)
        (by rw [auxSource_app_snd, auxArrowOfHom_snd]),
      auxObjects_ext φ T
        (by
          rw [auxTarget_app_fst, auxArrowOfHom_fst]
          exact (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _ m.arrow).2.2)
        (by
          have hw := evaluationArrow_val_of_eq G'.toGroupoidInFunctors T m.base m.w
          simp only [Deformation.GroupoidInFunctors.evaluationArrowEquiv_comp,
            Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow, auxIndex_arr_val] at hw
          refine Eq.trans ?_ hw
          refine (auxTarget_app_snd φ T _).trans ((auxTargetSnd_app φ T _).trans ?_)
          exact Deformation.GroupoidInFunctors.compose_congr G'.toGroupoidInFunctors T _ _
            (congrArg (φ.toGroupoidHom.mapArrows.app T) (auxArrowOfHom_fst φ T m.arrow))
            (auxArrowOfHom_snd φ T m.arrow))⟩
  invFun a := by
    obtain ⟨a, hs, ht⟩ := a
    have h₁ : (auxObjectsSnd φ).hom.app T P = (auxArrowsSnd φ).hom.app T a :=
      (congrArg ((auxObjectsSnd φ).hom.app T) hs).symm.trans (auxSource_app_snd φ T a)
    have h₂ : (auxObjectsSnd φ).hom.app T Q =
        G'.toGroupoidInFunctors.compose T
          (φ.toGroupoidHom.mapArrows.app T ((auxArrowsFst φ).hom.app T a))
          ((auxArrowsSnd φ).hom.app T a) (auxArrows_composable φ T a) :=
      (congrArg ((auxObjectsSnd φ).hom.app T) ht).symm.trans
        ((auxTarget_app_snd φ T a).trans (auxTargetSnd_app φ T a))
    refine
      { base := ?_
        arrow := (G.toGroupoidInFunctors.evaluationArrowEquiv T _ _).symm
          ⟨(auxArrowsFst φ).hom.app T a,
            (auxSource_app_fst φ T a).symm.trans
              (congrArg ((auxObjectsFst φ).hom.app T) hs),
            (auxTarget_app_fst φ T a).symm.trans
              (congrArg ((auxObjectsFst φ).hom.app T) ht)⟩
        w := ?_ }
    · exact (congrArg (G'.source.hom.app T) h₁).trans
        (((G'.toGroupoidInFunctors.pointwiseData T).source_comp _ _
          (auxArrows_composable φ T a)).symm.trans
          (congrArg (G'.source.hom.app T) h₂.symm))
    · refine evaluationArrow_eq_of_val G'.toGroupoidInFunctors T _ _ _ ?_
      simp only [Deformation.GroupoidInFunctors.evaluationArrowEquiv_comp,
        Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow, auxIndex_arr_val,
        Equiv.apply_symm_apply]
      exact (Deformation.GroupoidInFunctors.compose_congr G'.toGroupoidInFunctors T _
        (auxArrows_composable φ T a) rfl h₁).trans h₂.symm
  left_inv m := AuxHom.ext' (by
    simp only [auxArrowOfHom_fst]
    exact Equiv.symm_apply_apply _ _)
  right_inv a := by
    obtain ⟨a, hs, ht⟩ := a
    refine Subtype.ext (auxArrows_ext φ T ?_ ?_)
    · rw [auxArrowOfHom_fst, Equiv.apply_symm_apply]
    · exact (auxArrowOfHom_snd φ T _).trans
        ((congrArg ((auxObjectsSnd φ).hom.app T) hs).symm.trans (auxSource_app_snd φ T a))

/-- `auxArrowEquiv φ T P Q` sends an arrow `m` to the point `auxArrowOfHom φ T m.arrow`. -/
@[simp]
theorem auxArrowEquiv_apply_val (P Q : (auxObjects φ).obj.obj T)
    (m : auxIndex φ T P ⟶ auxIndex φ T Q) :
    (auxArrowEquiv φ T P Q m).1 = auxArrowOfHom φ T m.arrow := rfl

/-- The first projections of a composable pair of arrows of the auxiliary groupoid are a
composable pair of arrows of `G`. -/
theorem auxComp_composable
    (p : {q : (auxArrows φ).obj.obj T × (auxArrows φ).obj.obj T //
      (auxSource φ).hom.app T q.1 = (auxTarget φ).hom.app T q.2}) :
    G.source.hom.app T ((auxArrowsFst φ).hom.app T p.1.1) =
      G.target.hom.app T ((auxArrowsFst φ).hom.app T p.1.2) :=
  (auxSource_app_fst φ T p.1.1).symm.trans
    ((congrArg ((auxObjectsFst φ).hom.app T) p.2).trans (auxTarget_app_fst φ T p.1.2))

/-- The first projection of `c''` on a composable pair: the composite in `G` of the two first
projections. -/
theorem auxComp_app_fst
    (p : {q : (auxArrows φ).obj.obj T × (auxArrows φ).obj.obj T //
      (auxSource φ).hom.app T q.1 = (auxTarget φ).hom.app T q.2}) :
    (auxArrowsFst φ).hom.app T
        ((composableToPullback (auxSource φ).hom (auxTarget φ).hom ≫
          (auxComp φ).hom).app T p) =
      G.toGroupoidInFunctors.compose T ((auxArrowsFst φ).hom.app T p.1.1)
        ((auxArrowsFst φ).hom.app T p.1.2) (auxComp_composable φ T p) := by
  refine Eq.trans (hom_app_congr (auxComp_comp_auxArrowsFst φ) T _) ?_
  refine comp_app_eq_compose G T _ (auxComp_composable φ T p) ?_ ?_
  · refine Eq.trans (hom_app_congr (auxCompPair_comp_fst φ) T _) ?_
    exact congrArg ((auxArrowsFst φ).hom.app T)
      (pullbackFst_app_composableToPullback _ _ T p)
  · refine Eq.trans (hom_app_congr (auxCompPair_comp_snd φ) T _) ?_
    exact congrArg ((auxArrowsFst φ).hom.app T)
      (pullbackSnd_app_composableToPullback _ _ T p)

/-- The second projection of `c''` on a composable pair: the second projection of the arrow
applied first. -/
theorem auxComp_app_snd
    (p : {q : (auxArrows φ).obj.obj T × (auxArrows φ).obj.obj T //
      (auxSource φ).hom.app T q.1 = (auxTarget φ).hom.app T q.2}) :
    (auxArrowsSnd φ).hom.app T
        ((composableToPullback (auxSource φ).hom (auxTarget φ).hom ≫
          (auxComp φ).hom).app T p) =
      (auxArrowsSnd φ).hom.app T p.1.2 := by
  refine Eq.trans (hom_app_congr (auxComp_comp_auxArrowsSnd φ) T _) ?_
  exact congrArg ((auxArrowsSnd φ).hom.app T)
    (pullbackSnd_app_composableToPullback _ _ T p)

/-- **The evaluation of `(U'', R'', s'', t'', c'')` at a test object is a groupoid.** The
objects of `U''` over the test object index objects of `AlgebraicGeometry.AuxPoint`, whose
groupoid structure is that of the evaluated groupoid of `G`, and
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.auxArrowEquiv` identifies arrows there with points
of `R''`. -/
noncomputable def auxPointwiseGroupoid :
    Deformation.PointwiseGroupoid ((auxSource φ).hom.app T) ((auxTarget φ).hom.app T)
      (fun p => (composableToPullback (auxSource φ).hom (auxTarget φ).hom ≫
        (auxComp φ).hom).app T p) :=
  Deformation.PointwiseGroupoid.ofIndexing (auxIndex φ T) _ _ _ (auxArrowEquiv φ T) (by
    intro x y z g f
    refine auxArrows_ext φ T ?_ ?_
    · refine Eq.trans ?_ (auxComp_app_fst φ T _).symm
      refine (auxArrowOfHom_fst φ T (g.arrow ≫ f.arrow)).trans ?_
      refine (Deformation.GroupoidInFunctors.evaluationArrowEquiv_comp _ T g.arrow f.arrow).trans ?_
      exact Deformation.GroupoidInFunctors.compose_congr G.toGroupoidInFunctors T _ _
        (auxArrowOfHom_fst φ T f.arrow).symm (auxArrowOfHom_fst φ T g.arrow).symm
    · refine Eq.trans ?_ (auxComp_app_snd φ T _).symm
      exact (auxArrowOfHom_snd φ T (g.arrow ≫ f.arrow)).trans
        (auxArrowOfHom_snd φ T g.arrow).symm)

end Pointwise

/-! ### The auxiliary groupoid -/

/-- **The groupoid in algebraic spaces `(U'', R'', s'', t'', c'')` of Section 78.21**, attached
to a morphism `φ : G ⟶ G'` of groupoids in algebraic spaces over `B`. Its objects are the pairs
`(u, r')` with `f(u) = t'(r')`, its arrows the pairs `(r, r')` with `f(s(r)) = t'(r')`, and its
source, target and composition are
`s''(r, r') = (s(r), r')`, `t''(r, r') = (t(r), c'(f(r), r'))` and
`c''((r₁, r'₁), (r₂, r'₂)) = (c(r₁, r₂), r'₂)`. -/
noncomputable def auxGroupoid (φ : Hom G G') : GroupoidInAlgebraicSpaces C S hS B where
  objects := auxObjects φ
  arrows := auxArrows φ
  objectsToBase := auxObjectsFst φ ≫ G.objectsToBase
  arrowsToBase := auxArrowsFst φ ≫ G.arrowsToBase
  source := auxSource φ
  target := auxTarget φ
  source_over := by
    rw [← Category.assoc, auxSource_comp_auxObjectsFst, Category.assoc, G.source_over]
  target_over := by
    rw [← Category.assoc, auxTarget_comp_auxObjectsFst, Category.assoc, G.target_over]
  comp := auxComp φ
  comp_over := by
    calc auxComp φ ≫ auxArrowsFst φ ≫ G.arrowsToBase
        = (auxComp φ ≫ auxArrowsFst φ) ≫ G.arrowsToBase := by simp only [Category.assoc]
      _ = (auxCompPair φ ≫ G.comp) ≫ G.arrowsToBase :=
          congrArg (fun k => k ≫ G.arrowsToBase) (auxComp_comp_auxArrowsFst φ)
      _ = auxCompPair φ ≫ G.comp ≫ G.arrowsToBase := by simp only [Category.assoc]
      _ = auxCompPair φ ≫ (ObjectProperty.homMk
            (pullback.fst G.source.hom G.target.hom) :
              AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows) ≫
            G.arrowsToBase := congrArg (fun k => auxCompPair φ ≫ k) G.comp_over
      _ = (auxCompPair φ ≫ (ObjectProperty.homMk
            (pullback.fst G.source.hom G.target.hom) :
              AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows)) ≫
            G.arrowsToBase := by simp only [Category.assoc]
      _ = (auxFirstArrow φ ≫ auxArrowsFst φ) ≫ G.arrowsToBase :=
          congrArg (fun k => k ≫ G.arrowsToBase) (auxCompPair_comp_fst φ)
      _ = auxFirstArrow φ ≫ auxArrowsFst φ ≫ G.arrowsToBase := by simp only [Category.assoc]
  pointwiseGroupoid T := ⟨auxPointwiseGroupoid φ T⟩

/-- The space of objects of `auxGroupoid φ` is `U''`. -/
@[simp]
theorem auxGroupoid_objects (φ : Hom G G') : (auxGroupoid φ).objects = auxObjects φ := rfl

/-- The space of arrows of `auxGroupoid φ` is `R''`. -/
@[simp]
theorem auxGroupoid_arrows (φ : Hom G G') : (auxGroupoid φ).arrows = auxArrows φ := rfl

/-- The source map of `auxGroupoid φ` is `s''`. -/
@[simp]
theorem auxGroupoid_source (φ : Hom G G') : (auxGroupoid φ).source = auxSource φ := rfl

/-- The target map of `auxGroupoid φ` is `t''`. -/
@[simp]
theorem auxGroupoid_target (φ : Hom G G') : (auxGroupoid φ).target = auxTarget φ := rfl

/-- The underlying morphism of groupoids in presheaves of the morphism
`g : (U'', R'', s'', t'', c'') ⟶ (U, R, s, t, c)` of Section 78.21: the two first projections
`U'' ⟶ U` and `R'' ⟶ R`. -/
noncomputable def auxGroupoidHom (φ : Hom G G') :
    Deformation.GroupoidInFunctors.Hom (auxGroupoid φ).toGroupoidInFunctors
      G.toGroupoidInFunctors where
  mapObjects := (auxObjectsFst φ).hom
  mapArrows := (auxArrowsFst φ).hom
  map_source T a := (auxSource_app_fst φ T a).symm
  map_target T a := (auxTarget_app_fst φ T a).symm
  map_id T x :=
    Space.mapIdentityOfMapComp (G := (auxGroupoid φ).toGroupoidInFunctors)
      (H := G.toGroupoidInFunctors) (auxObjectsFst φ).hom (auxArrowsFst φ).hom
      (fun T a => (auxSource_app_fst φ T a).symm)
      (fun T a => (auxTarget_app_fst φ T a).symm)
      (fun T a b h => (auxComp_app_fst φ T ⟨(a, b), h⟩).symm) T x
  map_comp T a b h := (auxComp_app_fst φ T ⟨(a, b), h⟩).symm

/-- **The morphism `g : (U'', R'', s'', t'', c'') ⟶ (U, R, s, t, c)`** of Section 78.21, as a
morphism of groupoids in algebraic spaces over `B`. -/
noncomputable def auxHom (φ : Hom G G') : Hom (auxGroupoid φ) G where
  toGroupoidHom := auxGroupoidHom φ
  mapObjects_over := rfl
  mapArrows_over := rfl

/-- The underlying morphism of groupoids in presheaves of `auxHom φ` is `auxGroupoidHom φ`. -/
@[simp]
theorem auxHom_toGroupoidHom (φ : Hom G G') :
    (auxHom φ).toGroupoidHom = auxGroupoidHom φ := rfl

/-- On objects, `auxGroupoidHom φ` is the first projection `U'' ⟶ U`. -/
@[simp]
theorem auxGroupoidHom_mapObjects (φ : Hom G G') :
    (auxGroupoidHom φ).mapObjects = (auxObjectsFst φ).hom := rfl

/-- On arrows, `auxGroupoidHom φ` is the first projection `R'' ⟶ R`. -/
@[simp]
theorem auxGroupoidHom_mapArrows (φ : Hom G G') :
    (auxGroupoidHom φ).mapArrows = (auxArrowsFst φ).hom := rfl

/-- **The morphism `U'' ⟶ U'`** of Section 78.21, sending a point `(u, r')` to `s'(r')`. It is
what exhibits `(U'', R'', s'', t'', c'')` as a groupoid in algebraic spaces over `U'`. -/
noncomputable def auxToTargetObjects (φ : Hom G G') : auxObjects φ ⟶ G'.objects :=
  auxObjectsSnd φ ≫ G'.source

/-- **The morphism `U'' ⟶ U'` takes the same value on the source and the target of every arrow
of the auxiliary groupoid.** On points this is `s'(r') = s'(c'(f(r), r'))`, the source of a
composite being the source of the arrow applied first; it is what makes the morphism descend to
the quotient stack `[U''/R'']`. -/
theorem auxToTargetObjects_invariant (φ : Hom G G') :
    (auxGroupoid φ).target ≫ auxToTargetObjects φ =
      (auxGroupoid φ).source ≫ auxToTargetObjects φ := by
  have hright : (auxGroupoid φ).source ≫ auxToTargetObjects φ = auxArrowsSnd φ ≫ G'.source :=
    (Category.assoc (auxSource φ) (auxObjectsSnd φ) G'.source).symm.trans
      (congrArg (fun k => k ≫ G'.source) (auxSource_comp_auxObjectsSnd φ))
  refine Eq.trans ?_ hright.symm
  have h1 : (auxGroupoid φ).target ≫ auxToTargetObjects φ = auxTargetSnd φ ≫ G'.source :=
    (Category.assoc (auxTarget φ) (auxObjectsSnd φ) G'.source).symm.trans
      (congrArg (fun k => k ≫ G'.source) (auxTarget_comp_auxObjectsSnd φ))
  have h3 : auxComposable φ ≫ G'.comp ≫ G'.source =
      auxComposable φ ≫ (ObjectProperty.homMk
        (pullback.snd G'.source.hom G'.target.hom) :
          AlgebraicSpaces.fiberProduct C S hS G'.source G'.target ⟶ G'.arrows) ≫ G'.source :=
    congrArg (fun k => auxComposable φ ≫ k) (Space.isPullback_comp_source G').w
  refine h1.trans (Eq.trans (Category.assoc (auxComposable φ) G'.comp G'.source) ?_)
  refine h3.trans (Eq.trans (Category.assoc _ _ _).symm ?_)
  exact congrArg (fun k => k ≫ G'.source) (auxComposable_comp_snd φ)

end GroupoidInAlgebraicSpaces

end AlgebraicGeometry

end
