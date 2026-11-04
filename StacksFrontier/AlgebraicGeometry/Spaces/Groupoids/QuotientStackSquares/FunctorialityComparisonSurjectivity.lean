module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FunctorialityComparisonFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.FunctorialitySquareTerminality

/-!
# Local essential surjectivity of the comparison 1-morphism, and Stacks 04ZN

Let `φ : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in algebraic spaces
over an algebraic space `B` over a scheme `S` of a big fppf site, and assume the **source square**

```
R ---f---> R'
|          |
s          s'
v          v
U ---f---> U'
```

is cartesian, which is the hypothesis of Stacks 04ZN. This file proves that the comparison
1-morphism `c : 𝒮_U ⟶ [U/R] ×_{[U'/R']} 𝒮_{U'}` of
`AlgebraicGeometry.Stack.functorialityComparison` is then **locally essentially surjective on
fibres**. That is the second of the two halves into which
`AlgebraicGeometry.Stack.isTwoFibreProduct_functorialitySquare` splits Stacks 04ZN; the first,
fullness, is `AlgebraicGeometry.Stack.functorialityComparison_full`. With both in hand the square

```
𝒮_U ----π----> [U/R]
 |              |
𝒮_f            [φ]
 v              v
𝒮_{U'} --π'--> [U'/R']
```

is a 2-fibre product, which is Stacks 04ZN, and that is the last declaration of this file.

## Main results

* `AlgebraicGeometry.Stack.locallyEssSurjOnFibers_functorialityComparison`: **the comparison
  1-morphism of Stacks 04ZN is locally essentially surjective on fibres as soon as the source
  square of `φ` is cartesian.**
* `AlgebraicGeometry.Stack.isTwoFibreProduct_functorialitySquare_of_isPullback`: **Stacks 04ZN** —
  the square above is a 2-fibre product of stacks in groupoids over the big fppf site.
* `AlgebraicGeometry.Stack.functorialityComparison_obj_iso_inv` and
  `AlgebraicGeometry.Stack.quotientStackMap_commutes_inv_hom_app`: the *inverse* of the comparison
  isomorphism of the object of the 2-fibre product attached to a point of the object space is a
  component of the 2-isomorphism of Stacks 046Q, the companions of
  `AlgebraicGeometry.Stack.functorialityComparison_obj_iso_hom` and
  `AlgebraicGeometry.Stack.quotientStackMap_commutes_hom_inv_app`.
* `AlgebraicGeometry.Stack.functorialityComparison_iso_inv_naturality`: the naturality of
  Stacks 046Q at an arrow of the evaluated groupoid `G(V)`, with both components spelled through
  those inverses. This is the shape in which the commuting square of the morphism of the 2-fibre
  product that the argument builds consumes Stacks 046Q.

## Implementation notes

*The argument.* Let `P = (T, y, u', α)` be an object of the 2-fibre product over a test object
`T`, with `y` an object of `[U/R]_T`, `u'` a `T`-point of `U'` and `α : [φ](y) ≅ π'(u')` vertical.
By Stacks 044X (1), `AlgebraicGeometry.Stack.essImage_toQuotientStack`, there is a covering sieve
of `T` along each member `f : V ⟶ T` of which the base change of `y` is isomorphic in `[U/R]_V` to
`π(u)` for a `V`-point `u` of `U`; the sieve this file produces is that one, and the whole of the
work is then over a single `f`.

Over such an `f` one has a morphism `ξ : π(u) ⟶ y` of `[U/R]` lying over `f`. Pushing it through
`[φ]`, composing with `α` and cancelling the filler of the square gives a morphism
`π'(f(u)) ⟶ π'(u')` lying over `f`; a cartesian lift `β : v' ⟶ u'` of `f` in the object-space
fibration gives a second one, `π'(β)`. Both are cartesian, because `[U'/R']` is fibred in
groupoids and so every morphism of it lying over `f` is
(`AlgebraicGeometry.Stack.isFiberedInGroupoids_quotientStack`), so
`CategoryTheory.Functor.fiberIsoOfCartesian` compares them by a *vertical* isomorphism
`π'(f(u)) ≅ π'(v')`, and Stacks 044X (2) in the form
`AlgebraicGeometry.Stack.exists_evaluationArrow` writes that isomorphism as an arrow `r'` of the
evaluated groupoid `G'(V)`, i.e. as a `V`-point of `R'` with source `f(u)` and target `v'`.

The cartesian source square now lifts `r'` to a `V`-point `r` of `R` with `s(r) = u` and
`f(r) = r'`, by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.existsUnique_arrow_of_isPullback_source` — this
is the only place the hypothesis of Stacks 04ZN is used in this file, and it is what makes the
whole argument work. Its target `ũ = t(r)` is the second point of the object space, and the
`map_target` clause of a morphism of groupoids gives `f(ũ) = t'(r') = v'` **on the nose**, so the
`𝒮_{U'}`-component of the morphism of the 2-fibre product out of `c(ũ)` is `β` itself, with no
transport. The `[U/R]`-component is `ρ⁻¹ ≫ ξ`, where `ρ : π(u) ⟶ π(ũ)` is the vertical
isomorphism that `r` induces.

Its commuting square is then formal: it is an identity between five composites in `[U'/R']` whose
inputs are the naturality of Stacks 046Q at `r`, the comparison of the two cartesian lifts above,
and the two triangles of the filler. That identity is `square_aux`, proved over plain variables.

*Why the generic helpers.* Every step above is a lemma stated over **plain variables** and then
instantiated. Two reasons. First, `rw [CategoryTheory.Category.assoc]` is unusable
on a composite in `[U'/R']`: the two `≫`s of a nested composite reach their `Category` instance by
different paths, so `rw` does not match a pattern that is visibly present. Second, typeclass
resolution does not see through the semireducible definitions in play — `IsPreFibered`,
`IsCartesian` and `IsIso` for the quotient stacks all fail to resolve at the spellings this file
needs them at, whereas in a generic context, where the instance is a variable, they resolve
syntactically. So `exists_inv_of_vertical`, `isCartesian_of_isHomLift`, `isCartesian_pullbackMap`,
`isHomLift_pullbackMap` and `nonempty_iso_pullbackFiber` each wrap one such resolution, and
`map_congr` replaces the `congrArg`s whose function type the elaborator could not infer at the
concrete terms; `CategoryTheory.eq_whisker` does the same for a composite's left factor.

*The subtlety about `f(ũ) = v'`.* The point `v'` is produced by the cartesian lift `β`, hence
before `ũ`, and the equality `f(ũ) = v'` is only available after it. It is eliminated by `subst`,
which replaces `v'` throughout — including in the type of `β` — by `f(ũ)`. That is why every
intermediate datum of the proof is introduced by `obtain` rather than `let` or `set`: `subst`
rewrites the types of hypotheses, but a `let`-bound body is not a type and would be left behind.

## References

* [Stacks Project, Tag 003Q](https://stacks.math.columbia.edu/tag/003Q)
* [Stacks Project, Tag 0040](https://stacks.math.columbia.edu/tag/0040)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 046Q](https://stacks.math.columbia.edu/tag/046Q)
* [Stacks Project, Tag 04ZN](https://stacks.math.columbia.edu/tag/04ZN)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Pseudofunctor

namespace AlgebraicGeometry.Stack

universe u

open AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G G' : GroupoidInAlgebraicSpaces C S hS B}

/-! ### Generic helpers -/

/- A morphism of a category fibred in groupoids lying over an identity is an isomorphism, and its
inverse is again vertical. -/
private theorem exists_inv_of_vertical {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    (p : 𝒳 ⥤ 𝒞) (hp : p.IsFiberedInGroupoids) {U : 𝒞} {a b : 𝒳} (α : a ⟶ b)
    (hα : p.IsHomLift (𝟙 U) α) :
    ∃ αinv : b ⟶ a, p.IsHomLift (𝟙 U) αinv ∧ αinv ≫ α = 𝟙 b := by
  have := hα
  have := hp.isStronglyCartesian_homLift (𝟙 U) α
  have : IsIso α := Functor.IsStronglyCartesian.isIso_of_base_isIso (p := p) (f := 𝟙 U) α
  exact ⟨CategoryTheory.inv α, inferInstance, IsIso.inv_hom_id α⟩

/- The domain of a morphism lying over `f : V ⟶ U` lies over `V`, with the morphism an explicit
argument so that the instance argument is never a metavariable. -/
private theorem domain_eq_of_isHomLift {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    (p : 𝒳 ⥤ 𝒞) {U V : 𝒞} (f : V ⟶ U) {a b : 𝒳} (α : a ⟶ b) (hα : p.IsHomLift f α) :
    p.obj a = V := by
  have := hα
  exact IsHomLift.domain_eq p f α

/- Every morphism of a category fibred in groupoids lying over `f` is cartesian over `f`. -/
private theorem isCartesian_of_isHomLift {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    (p : 𝒳 ⥤ 𝒞) (hp : p.IsFiberedInGroupoids) {U V : 𝒞} (f : V ⟶ U) {a b : 𝒳} (α : a ⟶ b)
    (hα : p.IsHomLift f α) : p.IsCartesian f α := by
  have := hα
  have := hp.isStronglyCartesian_homLift f α
  infer_instance

/-- The chosen pullback morphism lies over the morphism it is chosen for. -/
public theorem isHomLift_pullbackMap {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    (p : 𝒳 ⥤ 𝒞) [p.IsPreFibered] {U V : 𝒞} {a : 𝒳} (ha : p.obj a = U) (f : V ⟶ U) :
    p.IsHomLift f (Functor.IsPreFibered.pullbackMap ha f) := inferInstance

/- The chosen pullback morphism is cartesian. -/
private theorem isCartesian_pullbackMap {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    (p : 𝒳 ⥤ 𝒞) [p.IsPreFibered] {U V : 𝒞} {a : 𝒳} (ha : p.obj a = U) (f : V ⟶ U) :
    p.IsCartesian f (Functor.IsPreFibered.pullbackMap ha f) := inferInstance

/- Two morphisms over `f` into the same object of a category fibred in groupoids are related by a
vertical morphism. -/
private theorem exists_vertical_comp_eq {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    (p : 𝒳 ⥤ 𝒞) (hp : p.IsFiberedInGroupoids) {U V : 𝒞} (f : V ⟶ U) {x x' y : 𝒳}
    (Φ : x ⟶ y) (Φ' : x' ⟶ y) (hΦ : p.IsHomLift f Φ) (hΦ' : p.IsHomLift f Φ') :
    ∃ m : x ⟶ x', p.IsHomLift (𝟙 V) m ∧ m ≫ Φ' = Φ := by
  have hc := isCartesian_of_isHomLift p hp f Φ hΦ
  have hc' := isCartesian_of_isHomLift p hp f Φ' hΦ'
  have hx := domain_eq_of_isHomLift p f Φ hΦ
  have hx' := domain_eq_of_isHomLift p f Φ' hΦ'
  exact ⟨_, (Functor.fiberIsoOfCartesian (z := (⟨x, hx⟩ : p.Fiber V))
    (z' := (⟨x', hx'⟩ : p.Fiber V)) f Φ Φ' hc hc').hom.2,
    Functor.fiberIsoOfCartesian_hom_fac (z := (⟨x, hx⟩ : p.Fiber V))
    (z' := (⟨x', hx'⟩ : p.Fiber V)) f Φ Φ' hc hc'⟩

/- A vertical morphism followed by one over `f` lies over `f`. -/
private theorem isHomLift_id_comp {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    (p : 𝒳 ⥤ 𝒞) {U V : 𝒞} (f : V ⟶ U) {a b c : 𝒳} (g : a ⟶ b) (h : b ⟶ c)
    (hg : p.IsHomLift (𝟙 V) g) (hh : p.IsHomLift f h) : p.IsHomLift f (g ≫ h) := by
  have := hg
  have := hh
  have h₂ : p.IsHomLift (𝟙 V ≫ f) (g ≫ h) := inferInstance
  rwa [Category.id_comp] at h₂

/- A morphism over `f` followed by a vertical one lies over `f`. -/
private theorem isHomLift_comp_id {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    (p : 𝒳 ⥤ 𝒞) {U V : 𝒞} (f : V ⟶ U) {a b c : 𝒳} (g : a ⟶ b) (h : b ⟶ c)
    (hg : p.IsHomLift f g) (hh : p.IsHomLift (𝟙 U) h) : p.IsHomLift f (g ≫ h) := by
  have := hg
  have := hh
  have h₂ : p.IsHomLift (f ≫ 𝟙 U) (g ≫ h) := inferInstance
  rwa [Category.comp_id] at h₂

/- The inverse of an isomorphism is any one-sided inverse, over plain variables. -/
private theorem iso_inv_eq {D : Type*} [Category* D] {X Y : D} (e : X ≅ Y) (g : Y ⟶ X)
    (h : e.hom ≫ g = 𝟙 X) : e.inv = g := by
  rw [← Category.id_comp g, ← e.inv_hom_id, Category.assoc, h, Category.comp_id]

/- Congruence of a functor in its morphism argument, over plain variables: the shape in which the
identities between morphisms of the quotient stacks below are transported, `rw` being unavailable
on goals that mention the fibre inclusion of a `CoGrothendieck` category. -/
private theorem map_congr {D : Type*} [Category* D] {E : Type*} [Category* E]
    (F : D ⥤ E) {a b : D} {g g' : a ⟶ b} (h : g = g') : F.map g = F.map g' := by rw [h]

/- Reassociating the image of a composite, over plain variables. -/
private theorem map_comp_comp_aux {D : Type*} [Category* D] {E : Type*} [Category* E]
    (F : D ⥤ E) {a b c : D} (g : a ⟶ b) (h : b ⟶ c) {z : E} (k : F.obj c ⟶ z)
    (w : F.obj a ⟶ z) (hw : F.map g ≫ F.map h ≫ k = w) :
    F.map (g ≫ h) ≫ k = w := by
  rw [F.map_comp, Category.assoc]
  exact hw

/- A functor carries a one-sided inverse to a one-sided inverse, over plain variables. -/
private theorem map_comp_eq_id {D : Type*} [Category* D] {E : Type*} [Category* E]
    (F : D ⥤ E) {a b : D} (g : a ⟶ b) (h : b ⟶ a) (hgh : g ≫ h = 𝟙 a) :
    F.map g ≫ F.map h = 𝟙 (F.obj a) := by
  rw [← F.map_comp, hgh, CategoryTheory.Functor.map_id]

/- The comparison of a presented object with the chosen pullback, over plain variables: a
cartesian morphism over `f` out of the image of an object of the fibre of `p` over `V` exhibits
the chosen pullback along `f` as lying in the essential image of the induced functor on fibres. -/
private theorem nonempty_iso_pullbackFiber {𝒞 : Type*} [Category* 𝒞] {𝒳 : Type*} [Category* 𝒳]
    {𝒴 : Type*} [Category* 𝒴] (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) [q.IsPreFibered] (F : 𝒳 ⥤ 𝒴)
    (hF : F ⋙ q = p) {U V : 𝒞} (x : q.Fiber U) (f : V ⟶ U) (z : p.Fiber V)
    (Φ : F.obj z.1 ⟶ x.1) (hΦ : q.IsCartesian f Φ) :
    Nonempty ((Functor.Fiber.mapOfComp p q F hF V).obj z ≅ Functor.pullbackFiber q x f) :=
  ⟨Functor.fiberIsoOfCartesian (p := q) (z := (Functor.Fiber.mapOfComp p q F hF V).obj z)
    (z' := Functor.pullbackFiber q x f) f Φ (Functor.IsPreFibered.pullbackMap x.2 f) hΦ
    (isCartesian_pullbackMap q x.2 f)⟩

/- The commuting square of the morphism of the 2-fibre product that local essential surjectivity
produces, as an identity between plain morphisms of a category. Stated over variables because the
composites it manipulates live in `[U'/R']`, where the two `≫`s of a nested composite reach their
`Category` instance by different paths, so neither `rw [Category.assoc]` nor `simp` fires. -/
private theorem square_aux {D : Type*} [Category* D] {A₁ A₂ B₁ B₂ Z : D}
    (H₁ : B₁ ⟶ A₁) (I₁ : A₁ ⟶ B₁) (H₂ : B₂ ⟶ A₂) (I₂ : A₂ ⟶ B₂)
    (Arr : B₁ ⟶ B₂) (Bet : B₂ ⟶ Z) (Xi : A₁ ⟶ Z) (Rho : A₁ ⟶ A₂) (Rinv : A₂ ⟶ A₁)
    (h₁ : Arr ≫ Bet = H₁ ≫ Xi) (h₂ : Arr ≫ H₂ = H₁ ≫ Rho)
    (h₃ : I₁ ≫ H₁ = 𝟙 A₁) (h₄ : H₂ ≫ I₂ = 𝟙 B₂) (h₅ : Rinv ≫ Rho = 𝟙 A₂) :
    Rinv ≫ Xi = I₂ ≫ Bet := by
  have hRho : I₁ ≫ Arr ≫ H₂ = Rho := by
    rw [h₂, ← Category.assoc, h₃, Category.id_comp]
  have key : Rho ≫ I₂ ≫ Bet = Xi := by
    rw [← hRho]
    simp only [Category.assoc]
    rw [← Category.assoc H₂ I₂ Bet, h₄, Category.id_comp, h₁, ← Category.assoc, h₃,
      Category.id_comp]
  rw [← key, ← Category.assoc Rinv Rho (I₂ ≫ Bet), h₅, Category.id_comp]

/-! ### The inverse of the filler -/

/-- The components of the inverse and of the 2-isomorphism of Stacks 046Q compose to the
identity. -/
theorem quotientStackMap_commutes_inv_hom_app (φ : Hom G G')
    (z : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).obj) :
    (quotientStackMap_commutes φ).inv.toNatTrans.app z ≫
        (quotientStackMap_commutes φ).hom.toNatTrans.app z = 𝟙 _ :=
  NatTrans.congr_app
    (congrArg (fun α => BasedNatTrans.toNatTrans α) (quotientStackMap_commutes φ).inv_hom_id) z

/-- **The inverse of the comparison isomorphism of the object of the 2-fibre product attached to a
point of the object space is a component of the 2-isomorphism of Stacks 046Q.** -/
theorem functorialityComparison_obj_iso_inv (φ : Hom G G')
    (w : (liftedFibredCategory G.objects).obj) :
    ((functorialityComparison φ).obj w).iso.inv =
      (quotientStackMap_commutes φ).hom.toNatTrans.app
        ((pointwiseObjectInclusion G).obj ((liftedFibredCategoryDown G.objects).obj w)) :=
  iso_inv_eq _ _
    (((eq_whisker (functorialityComparison_obj_iso_hom φ w)
      ((quotientStackMap_commutes φ).hom.toNatTrans.app
        ((pointwiseObjectInclusion G).obj ((liftedFibredCategoryDown G.objects).obj w))))).trans
      (quotientStackMap_commutes_inv_hom_app φ _))

/-- **Stacks 046Q read through the filler of the square of Stacks 04ZN**: the naturality of the
2-isomorphism of Stacks 046Q at an arrow of the evaluated groupoid `G(V)`, with its two components
spelled as the inverses of the comparison isomorphisms of the two objects of the 2-fibre product
that the comparison 1-morphism attaches to the two endpoints of the arrow. -/
theorem functorialityComparison_iso_inv_naturality (φ : Hom G G') (V : BigFppfOver C S hS)
    {u₁ u₂ : G.toGroupoidInFunctors.Evaluation (op V)} (arr : u₁ ⟶ u₂) :
    (pointwiseToQuotientStack G').map ((quotientPointwiseMap φ).map ((CoGrothendieck.ι
          (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor' V).map arr)) ≫
        ((functorialityComparison φ).obj (enlargedPoint G V u₂)).iso.inv =
      ((functorialityComparison φ).obj (enlargedPoint G V u₁)).iso.inv ≫
        (quotientStackMap φ).map ((pointwiseToQuotientStack G).map ((CoGrothendieck.ι
          (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
            Grpd.forgetToCat).toPseudofunctor' V).map arr)) := by
  rw [functorialityComparison_obj_iso_inv, functorialityComparison_obj_iso_inv]
  exact quotientStackMap_commutes_naturality φ ((CoGrothendieck.ι
    (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
      Grpd.forgetToCat).toPseudofunctor' V).map arr)

/-! ### The second point of the object space -/

/- **The step of Stacks 04ZN that produces the object of the fibre of `𝒮_U`.** Given a point `u`
of the object space over a test object `V` and a morphism `ξ` of `[U/R]` over `f : V ⟶ P.base`
from `π(u)` to the `[U/R]`-component of an object `P` of the 2-fibre product, the cartesian source
square produces a second point `ũ` of the object space over `V` and a morphism of the 2-fibre
product from `c(ũ)` to `P` lying over `f`. -/
private theorem exists_hom_of_presented (φ : Hom G G')
    (hφ : IsPullback φ.toGroupoidHom.mapArrows G.source.hom G'.source.hom
      φ.toGroupoidHom.mapObjects)
    (P : functorialityTwoFibreProductObj φ) {V : BigFppfOver C S hS} (f : V ⟶ P.base)
    (u : G.objects.obj.obj (op V))
    (ξ : (pointwiseToQuotientStack G).obj ⟨V, u⟩ ⟶ P.x)
    (hξ : (quotientStack G).p.IsHomLift f ξ) :
    ∃ (ũ : G.objects.obj.obj (op V))
      (Φ : (functorialityComparison φ).obj (enlargedPoint G V ũ) ⟶ P),
      (functorialityTwoFibreProduct φ).IsHomLift f Φ := by
  -- the cartesian lift of `f` at the `𝒮_{U'}`-component of `P`
  have hgpdY : (liftedFibredCategory G'.objects).p.IsFiberedInGroupoids :=
    isFiberedInGroupoids_uliftHom _ (fibredCategory C S hS G'.objects.obj).property
  obtain ⟨y₀, β, hβ⟩ := hgpdY.exists_lift f P.y P.hy
  obtain ⟨Vc, dpt⟩ := y₀
  obtain ⟨v'⟩ := dpt
  have hVc : V = Vc :=
    (domain_eq_of_isHomLift (liftedFibredCategory G'.objects).p f β hβ).symm
  subst hVc
  -- the two legs over `f` into `π'(P.y)` in the quotient stack `[U'/R']`
  have hmapξ : (quotientStack G').p.IsHomLift f ((quotientStackMap φ).map ξ) := by
    have := hξ
    exact Functor.isHomLift_map_of_comp_eq (quotientStackMap φ).w f ξ
  have hcell : (quotientStack G').p.IsHomLift (𝟙 V)
      ((functorialityComparison φ).obj (enlargedPoint G V u)).iso.hom :=
    functorialityProjectionCellLifted_isHomLift φ (enlargedPoint G V u)
  have hcellinv : (quotientStack G').p.IsHomLift (𝟙 V)
      ((functorialityComparison φ).obj (enlargedPoint G V u)).iso.inv := by
    have := hcell
    infer_instance
  have hD : (quotientStack G').p.IsHomLift f
      (((functorialityComparison φ).obj (enlargedPoint G V u)).iso.inv ≫
        (quotientStackMap φ).map ξ ≫ P.iso.hom) :=
    isHomLift_id_comp (quotientStack G').p f
      ((functorialityComparison φ).obj (enlargedPoint G V u)).iso.inv
      ((quotientStackMap φ).map ξ ≫ P.iso.hom) hcellinv
      (isHomLift_comp_id (quotientStack G').p f ((quotientStackMap φ).map ξ) P.iso.hom
        hmapξ P.vertical)
  have hβ' : (quotientStack G').p.IsHomLift f ((liftedQuotientStackProjection G').map β) := by
    have := hβ
    exact Functor.isHomLift_map_of_comp_eq (liftedQuotientStackProjection G').w f β
  -- Stacks 044X (2): the comparison of the two cartesian lifts is induced by an arrow of `R'`
  obtain ⟨arr', hstar⟩ : ∃ arr' : (show G'.toGroupoidInFunctors.Evaluation (op V) from
        φ.toGroupoidHom.mapObjects.app (op V) u) ⟶ v',
      (pointwiseToQuotientStack G').map ((CoGrothendieck.ι
            (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
              Grpd.forgetToCat).toPseudofunctor' V).map arr') ≫
          (liftedQuotientStackProjection G').map β =
        ((functorialityComparison φ).obj (enlargedPoint G V u)).iso.inv ≫
          (quotientStackMap φ).map ξ ≫ P.iso.hom := by
    obtain ⟨m, hm, hmfac⟩ := exists_vertical_comp_eq (quotientStack G').p
      (isFiberedInGroupoids_quotientStack G') f _ _ hD hβ'
    obtain ⟨arr', harr'⟩ := exists_evaluationArrow G' V _ v' m hm
    exact ⟨arr', (eq_whisker harr' _).trans hmfac⟩
  -- the `R'`-point the arrow names, and the `R`-point the cartesian source square lifts it to
  obtain ⟨r', hr'⟩ : ∃ r', (G'.toGroupoidInFunctors.evaluationArrowEquiv (op V)
      (φ.toGroupoidHom.mapObjects.app (op V) u) v' arr').1 = r' := ⟨_, rfl⟩
  have hr's : G'.source.hom.app (op V) r' = φ.toGroupoidHom.mapObjects.app (op V) u := by
    rw [← hr']
    exact (G'.toGroupoidInFunctors.evaluationArrowEquiv (op V) _ v' arr').2.1
  have hr't : G'.target.hom.app (op V) r' = v' := by
    rw [← hr']
    exact (G'.toGroupoidInFunctors.evaluationArrowEquiv (op V) _ v' arr').2.2
  obtain ⟨r, ⟨hrA, hrS⟩, -⟩ := Hom.existsUnique_arrow_of_isPullback_source φ hφ u r' hr's
  obtain ⟨ũ, hũ⟩ : ∃ ũ, G.target.hom.app (op V) r = ũ := ⟨_, rfl⟩
  have hfu : φ.toGroupoidHom.mapObjects.app (op V) ũ = v' := by
    rw [← hũ]
    exact (φ.toGroupoidHom.map_target (op V) r).symm.trans
      ((congrArg (G'.target.hom.app (op V)) hrA).trans hr't)
  subst hfu
  -- the arrow of the evaluated groupoid `G(V)` from `u` to `ũ`, and its image in `G'(V)`
  obtain ⟨arr, harrEq⟩ :
      ∃ arr, (G.toGroupoidInFunctors.evaluationArrowEquiv (op V) u ũ arr).1 = r :=
    ⟨(G.toGroupoidInFunctors.evaluationArrowEquiv (op V) u ũ).symm ⟨r, hrS, hũ⟩,
      congrArg Subtype.val (Equiv.apply_symm_apply _ _)⟩
  have hid : (φ.toGroupoidHom.evaluation (op V)).map arr = arr' :=
    (G'.toGroupoidInFunctors.evaluationArrowEquiv (op V)
      (φ.toGroupoidHom.mapObjects.app (op V) u)
      (φ.toGroupoidHom.mapObjects.app (op V) ũ)).injective
      (Subtype.ext (((Deformation.GroupoidInFunctors.Hom.evaluation_map_arrow
        φ.toGroupoidHom (op V) arr).trans
        ((congrArg (φ.toGroupoidHom.mapArrows.app (op V)) harrEq).trans hrA)).trans hr'.symm))
  -- the vertical isomorphism of `[U/R]` that the arrow induces, and its inverse
  have hρ : (quotientStack G).p.IsHomLift (𝟙 V)
      ((pointwiseToQuotientStack G).map ((CoGrothendieck.ι
        (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' V).map arr)) := by
    have h₀ : (presheafOfGroupoids (evaluationGroupoidFunctor G.toGroupoidInFunctors)).p.IsHomLift
        (𝟙 V) ((CoGrothendieck.ι (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' V).map arr) :=
      CoGrothendieck.isHomLift_of_base_eq_id V ((CoGrothendieck.ι
        (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' V).map arr) rfl
    exact Functor.isHomLift_map_of_comp_eq
      (isFibredOneMorphism_pointwiseToQuotientStack G).comp_eq (𝟙 V) _
  obtain ⟨ρinv, hρinv, hρinvcomp⟩ := exists_inv_of_vertical (quotientStack G).p
    (isFiberedInGroupoids_quotientStack G) _ hρ
  -- the commuting square of the morphism of the 2-fibre product
  have hw := map_comp_comp_aux (quotientStackMap φ).toFunctor ρinv ξ P.iso.hom
    (((functorialityComparison φ).obj (enlargedPoint G V ũ)).iso.hom ≫
      (liftedQuotientStackProjection G').map β)
    (square_aux ((functorialityComparison φ).obj (enlargedPoint G V u)).iso.inv
      ((functorialityComparison φ).obj (enlargedPoint G V u)).iso.hom
      ((functorialityComparison φ).obj (enlargedPoint G V ũ)).iso.inv
      ((functorialityComparison φ).obj (enlargedPoint G V ũ)).iso.hom
      ((pointwiseToQuotientStack G').map ((CoGrothendieck.ι
        (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' V).map arr'))
      ((liftedQuotientStackProjection G').map β)
      ((quotientStackMap φ).map ξ ≫ P.iso.hom)
      ((quotientStackMap φ).map ((pointwiseToQuotientStack G).map ((CoGrothendieck.ι
        (evaluationGroupoidFunctor G.toGroupoidInFunctors ⋙
          Grpd.forgetToCat).toPseudofunctor' V).map arr)))
      ((quotientStackMap φ).map ρinv) hstar
      ((eq_whisker (map_congr (pointwiseToQuotientStack G')
          ((quotientPointwiseMap_map_ι φ V arr).trans
            (map_congr (CoGrothendieck.ι (evaluationGroupoidFunctor G'.toGroupoidInFunctors ⋙
              Grpd.forgetToCat).toPseudofunctor' V) hid)))
        ((functorialityComparison φ).obj (enlargedPoint G V ũ)).iso.inv).symm.trans
        (functorialityComparison_iso_inv_naturality φ V arr))
      (((functorialityComparison φ).obj (enlargedPoint G V u)).iso.hom_inv_id)
      (((functorialityComparison φ).obj (enlargedPoint G V ũ)).iso.inv_hom_id)
      (map_comp_eq_id (quotientStackMap φ).toFunctor ρinv _ hρinvcomp))
  -- the morphism of the 2-fibre product
  obtain ⟨Φ, hΦb⟩ : ∃ Φ : (functorialityComparison φ).obj (enlargedPoint G V ũ) ⟶ P,
      (functorialityTwoFibreProduct φ).map Φ = f :=
    ⟨⟨f, ρinv ≫ ξ, β, isHomLift_id_comp (quotientStack G).p f ρinv ξ hρinv hξ, hβ, hw⟩, rfl⟩
  refine ⟨ũ, Φ, ?_⟩
  have hlift := IsHomLift.map (functorialityTwoFibreProduct φ) Φ
  rwa [hΦb] at hlift

/-! ### Local essential surjectivity on fibres -/

/-- **The comparison 1-morphism of Stacks 04ZN is locally essentially surjective on fibres when
the source square of `φ` is cartesian.**

For every object `P` of the 2-fibre product `[U/R] ×_{[U'/R']} 𝒮_{U'}` over a test object `T`
there is a covering sieve of `T` such that along each member `f : V ⟶ T` the base change of `P` is
isomorphic, in the fibre over `V`, to the image under the comparison 1-morphism of a `V`-point of
the object space. The sieve is the one Stacks 044X (1) supplies for the `[U/R]`-component of `P`,
and the point is produced from the cartesian source square by
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.Hom.existsUnique_arrow_of_isPullback_source`.

Together with `AlgebraicGeometry.Stack.functorialityComparison_full` this is everything
`AlgebraicGeometry.Stack.isTwoFibreProduct_functorialitySquare` asks for, so Stacks 04ZN follows;
it is `AlgebraicGeometry.Stack.isTwoFibreProduct_functorialitySquare_of_isPullback` below, which
is the declaration that carries the tag. -/
theorem locallyEssSurjOnFibers_functorialityComparison (φ : Hom G G')
    (hφ : IsPullback φ.toGroupoidHom.mapArrows G.source.hom G'.source.hom
      φ.toGroupoidHom.mapObjects) :
    Functor.LocallyEssSurjOnFibers (isFibered_functorialityTwoFibreProduct φ)
      (isFibredOneMorphism_functorialityComparison φ).comp_eq
      (BigFppfOver.topology C S hS) := by
  intro T x
  obtain ⟨P, hPT⟩ := x
  subst hPT
  obtain ⟨R₀, hR₀, hess⟩ := essImage_toQuotientStack G _ ⟨P.x, P.hx⟩
  refine ⟨R₀, hR₀, ?_⟩
  intro V f hf
  obtain ⟨w, ⟨e⟩⟩ := hess hf
  obtain ⟨w₀, hw₀⟩ := w
  obtain ⟨Vb, upt⟩ := w₀
  have hVb : V = Vb := hw₀.symm
  subst hVb
  obtain ⟨ũ, Φ, hΦ⟩ := exists_hom_of_presented φ hφ P f upt
    (Functor.Fiber.fiberInclusion.map e.hom ≫ Functor.IsPreFibered.pullbackMap P.hx f)
    (isHomLift_id_comp (quotientStack G).p f _ _ e.hom.2
      (isHomLift_pullbackMap (quotientStack G).p P.hx f))
  have hfib : (functorialityTwoFibreProduct φ).IsFibered :=
    isFibered_functorialityTwoFibreProduct φ
  exact ⟨⟨enlargedPoint G V ũ, rfl⟩,
    nonempty_iso_pullbackFiber (liftedFibredCategory G.objects).p
      (functorialityTwoFibreProduct φ) (functorialityComparison φ)
      (isFibredOneMorphism_functorialityComparison φ).comp_eq ⟨P, rfl⟩ f
      ⟨enlargedPoint G V ũ, rfl⟩ Φ
      (isCartesian_of_isHomLift (functorialityTwoFibreProduct φ)
        (isFiberedInGroupoids_functorialityTwoFibreProduct φ) f Φ hΦ)⟩

/-! ### Stacks 04ZN -/

/-- **Stacks 04ZN.** Let `φ : (U, R, s, t, c) ⟶ (U', R', s', t', c')` be a morphism of groupoids in
algebraic spaces over an algebraic space `B` over a scheme `S` of a big fppf site, and suppose the
square formed by the two **source** maps,

```
R ---f---> R'
|          |
s          s'
v          v
U ---f---> U'
```

is cartesian. Then the square

```
𝒮_U ----π----> [U/R]
 |              |
𝒮_f            [φ]
 v              v
𝒮_{U'} --π'--> [U'/R']
```

of the projections of Stacks 044R, the induced 1-morphism of Stacks 046Q and the 1-morphism of
Stacks 0458 **is a 2-fibre product** in the 2-category of stacks in groupoids over the big fppf
site.

Both halves of the proof consume the cartesian source square and nothing else:
`AlgebraicGeometry.Stack.functorialityComparison_full` for fullness of the comparison
1-morphism — and faithfulness is free — and
`AlgebraicGeometry.Stack.locallyEssSurjOnFibers_functorialityComparison` for local essential
surjectivity on fibres. The reduction of the 2-fibre product property to those two is
`AlgebraicGeometry.Stack.isTwoFibreProduct_functorialitySquare`. -/
@[stacks 04ZN]
noncomputable def isTwoFibreProduct_functorialitySquare_of_isPullback (φ : Hom G G')
    (hφ : IsPullback φ.toGroupoidHom.mapArrows G.source.hom G'.source.hom
      φ.toGroupoidHom.mapObjects) :
    Bicategory.IsTwoFibreProduct (functorialitySquare φ) :=
  isTwoFibreProduct_functorialitySquare φ (functorialityComparison_full φ hφ)
    (locallyEssSurjOnFibers_functorialityComparison φ hφ)

end AlgebraicGeometry.Stack

end
