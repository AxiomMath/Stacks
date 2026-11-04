module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.SubstackFactorizationPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveFlatFppfLocalSections
public import StacksFrontier.AlgebraicGeometry.Stacks.ThickeningBaseChange

/-!
# The scheme theoretic image of a morphism of algebraic stacks (Stacks 0CMI, 0CMJ, 0CPV)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`. Following **Stacks 0CMI**, a
closed substack of `𝒴` is *the* scheme theoretic image of `f` when `f` factors through it and it
is contained in every closed substack of `𝒴` through which `f` factors. **Stacks 0CMJ** says that
precomposing `f` with a surjective, flat 1-morphism locally of finite presentation
`g : 𝒲 ⟶ 𝒳` changes neither the existence of the scheme theoretic image nor its value.
**Stacks 0CPV** says that a commutative square of algebraic stacks induces a 1-morphism between
the scheme theoretic images of its two horizontal 1-morphisms, compatible with the inclusions
into the targets and with any two factorizations through the images.

The proof is the source's. Both halves reduce to the single statement that factoring through a
*fixed* closed substack is unchanged by the precomposition, since the two minimality conditions
then quantify over the same closed substacks. One direction of that statement is formal. For the
other, let `x` be an object of `𝒳` over an object `T` of the site and ask that `f(x)` lie in the
substack. **Stacks 06QA** applied to `g` produces an fppf covering of `T` over each member `k` of
which some object `w` of `𝒲` maps to `x` over `k`; then `f(g(w))` lies in the substack by
hypothesis and maps to `f(x)` over `k`, so the restriction of `f(x)` along `k` lies in the
substack because `𝒴` is fibred in groupoids. Membership of a substack is local on the big fppf
site, which descends this to `f(x)` itself.

## Main definitions

* `AlgebraicGeometry.Stack.FactorsThroughSubstack`: a 1-morphism factors through the full
  subcategory cut out by a property of the objects of its target, over the big fppf site of `S`
  and up to a 2-isomorphism.
* `AlgebraicGeometry.Stack.IsSchemeTheoreticImage`: **Stacks 0CMI**, being the scheme theoretic
  image.
* `AlgebraicGeometry.Stack.HasSchemeTheoreticImage`: existence of the scheme theoretic image.
* `AlgebraicGeometry.Stack.factorsThroughSubstackHom` and
  `AlgebraicGeometry.Stack.factorsThroughSubstackIso`: that factorization read as a 1-morphism of
  algebraic stacks, together with the 2-isomorphism of its composite with the inclusion of the
  substack and the original 1-morphism.
* `AlgebraicGeometry.Stack.substackMapOfLe`: the 1-morphism of substacks induced by a 1-morphism
  of the ambient algebraic stacks carrying one substack into another.
* `AlgebraicGeometry.Stack.schemeTheoreticImageMap`: **Stacks 0CPV**, the induced 1-morphism of
  scheme theoretic images.

## Main results

* `AlgebraicGeometry.Stack.factorsThroughSubstack_comp_iff`: factoring through a fixed closed
  substack is unchanged by precomposition with a surjective, flat 1-morphism locally of finite
  presentation.
* `AlgebraicGeometry.Stack.hasSchemeTheoreticImage_comp_iff`: **Stacks 0CMJ**, the equivalence of
  the two existence statements.
* `AlgebraicGeometry.Stack.eq_of_isSchemeTheoreticImage_comp`: **Stacks 0CMJ**, the two scheme
  theoretic images agree.
* `AlgebraicGeometry.Stack.isClosedSubstack_inverseImage`: the preimage of a closed substack
  under a 1-morphism of algebraic stacks is a closed substack.
* `AlgebraicGeometry.Stack.le_inverseImage_of_isSchemeTheoreticImage`: **Stacks 0CPV**, the
  containment of scheme theoretic images that induces the morphism.
* `AlgebraicGeometry.Stack.schemeTheoreticImageMap_comp_inclusion` and
  `AlgebraicGeometry.Stack.schemeTheoreticImageMapFactorizationSquare`: **Stacks 0CPV**, the two
  squares of the induced commutative diagram.

## The proof of Stacks 0CPV

The preimage of the scheme theoretic image of `f₂` under `𝒴₁ ⟶ 𝒴₂` is a closed substack of
`𝒴₁` through which `f₁` factors, so the minimality of the scheme theoretic image of `f₁` places
the latter inside it, which is exactly the datum of the induced 1-morphism. That the preimage is
again a closed substack is the one geometric input: the full subcategory it cuts out is the
2-fibre product of `𝒴₁` with the full subcategory cut out upstairs, so it is an algebraic stack
by **Stacks 04T2** and its inclusion is a closed immersion because closed immersions are stable
under base change. The identification with the 2-fibre product is the equivalence over the big
fppf site sending an object `X` of `𝒴₁` with `b X` in the substack to the pair `(X, b X)` with
identity comparison isomorphism, and an object of the 2-fibre product to its `𝒴₁`-component.

## Implementation notes

A closed substack is a property of the objects of `𝒴` satisfying
`AlgebraicGeometry.Stack.IsClosedSubstack`, and containment of closed substacks is the order on
object properties, so minimality is `≤` and the agreement of the two images is an equality of
object properties. Factorization is taken over the big fppf site and up to a 2-isomorphism, the
shape in which `AlgebraicGeometry.Stack.exists_based_factorization_iff` and the factorization
criterion of Stacks 0507 meet it; being the scheme theoretic image is therefore a predicate on
object properties, and existence is the bare existential over it, so no choice is made.

The preimage of an object property is `CategoryTheory.ObjectProperty.inverseImage` along the
underlying functor, and the containment of Stacks 0CPV is the resulting `≤`. The two scheme
theoretic images cut out closed substacks and so are algebraic stacks already, by
`AlgebraicGeometry.Stack.IsSchemeTheoreticImage.isAlgebraicStack`, which is what the induced
1-morphism and the squares are formed from; the left-hand square is stated for arbitrary
factorizations, since factoring through a substack is an existential statement.

## References

* [Stacks Project, Tag 0CMI](https://stacks.math.columbia.edu/tag/0CMI)
* [Stacks Project, Tag 0CMJ](https://stacks.math.columbia.edu/tag/0CMJ)
* [Stacks Project, Tag 0CPV](https://stacks.math.columbia.edu/tag/0CPV)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A 1-morphism of algebraic stacks *factors through* the full subcategory of its target cut out
by a property of the objects when it does so over the big fppf site of `S` and up to a
2-isomorphism. -/
def FactorsThroughSubstack {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (P : ObjectProperty 𝒴.val.val.obj) : Prop :=
  ∃ g : 𝒳.val.val ⥤ᵇ fullSubcategoryBased 𝒴 P,
    Nonempty (g.comp (fullSubcategoryBasedInclusion 𝒴 P) ≅ f.hom.hom)

/-- The factorization of a 1-morphism through the substack cut out by `P`, read as a 1-morphism
of algebraic stacks: `AlgebraicGeometry.Stack.FactorsThroughSubstack` supplies a 1-morphism over
the big fppf site of `S`, and the 2-category of algebraic stacks has the 1-morphisms of the
ambient one, so it is reached by two applications of
`CategoryTheory.Bicategory.InducedBicategory.mkHom`, exactly as
`AlgebraicGeometry.Stack.substackMapOfLe` does. -/
noncomputable def factorsThroughSubstackHom {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {P : ObjectProperty 𝒴.val.val.obj}
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴 P))
    (hfac : FactorsThroughSubstack f P) :
    𝒳 ⟶ fullSubcategoryAlgebraicStack 𝒴 P hA :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom hfac.choose)

/-- The factorization `AlgebraicGeometry.Stack.factorsThroughSubstackHom` composed with the
inclusion of the substack is the original 1-morphism, up to the 2-isomorphism that
`AlgebraicGeometry.Stack.FactorsThroughSubstack` carries. -/
noncomputable def factorsThroughSubstackIso {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {P : ObjectProperty 𝒴.val.val.obj}
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴 P))
    (hfac : FactorsThroughSubstack f P) :
    factorsThroughSubstackHom f hA hfac ≫ fullSubcategoryInclusion 𝒴 P hA ≅ f :=
  Bicategory.InducedBicategory.isoMk
    (Bicategory.InducedBicategory.isoMk hfac.choose_spec.some)

/-- A 1-morphism factors through a strictly full subcategory of its target exactly when the
property cutting it out holds at every object in its image. -/
theorem factorsThroughSubstack_iff_forall {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    {P : ObjectProperty 𝒴.val.val.obj} [P.IsClosedUnderIsomorphisms] :
    FactorsThroughSubstack f P ↔ ∀ X : 𝒳.val.val.obj, P (f.hom.hom.obj X) :=
  exists_based_factorization_iff f.hom.hom

/-- **Stacks 0CMI.** A property of the objects of `𝒴` is *the scheme theoretic image* of a
1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S` when it cuts out a closed substack of `𝒴`
through which `f` factors, and is contained in every closed substack of `𝒴` through which `f`
factors. -/
@[stacks 0CMI, ega "I 9.5.3"]
def IsSchemeTheoreticImage {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (P : ObjectProperty 𝒴.val.val.obj) : Prop :=
  IsClosedSubstack 𝒴 P ∧ FactorsThroughSubstack f P ∧
    ∀ Q : ObjectProperty 𝒴.val.val.obj, IsClosedSubstack 𝒴 Q → FactorsThroughSubstack f Q →
      P ≤ Q

/-- A 1-morphism of algebraic stacks *has a scheme theoretic image* when some closed substack of
its target is one. -/
def HasSchemeTheoreticImage {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∃ P : ObjectProperty 𝒴.val.val.obj, IsSchemeTheoreticImage f P

/-- The scheme theoretic image is unique: two object properties that are both the scheme
theoretic image of the same 1-morphism are equal, each being contained in the other. -/
theorem IsSchemeTheoreticImage.unique {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}
    {P Q : ObjectProperty 𝒴.val.val.obj} (hP : IsSchemeTheoreticImage f P)
    (hQ : IsSchemeTheoreticImage f Q) : P = Q :=
  le_antisymm (hP.2.2 Q hQ.1 hQ.2.1) (hQ.2.2 P hP.1 hP.2.1)

/-- The full subcategory cut out by the scheme theoretic image of a 1-morphism is an algebraic
stack, being a closed substack of the target. -/
theorem IsSchemeTheoreticImage.isAlgebraicStack {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    {f : 𝒳 ⟶ 𝒴} {P : ObjectProperty 𝒴.val.val.obj} (hP : IsSchemeTheoreticImage f P) :
    IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴 P) :=
  hP.1.2.choose

/-- **The descent step of Stacks 0CMJ.** Let `g : 𝒲 ⟶ 𝒳` be surjective, flat and locally of
finite presentation and let `P` cut out a strictly full subcategory of `𝒴` which is an algebraic
stack. If `P` holds at every object in the image of `g ≫ f`, then it holds at every object in the
image of `f`.

For an object `X` of `𝒳` over `T`, **Stacks 06QA** supplies an fppf covering sieve of `T` and,
over each of its members `k`, an object `W` of `𝒲` with a morphism `g(W) ⟶ X` over `k`. Its image
under `f` is a morphism `f(g(W)) ⟶ f(X)` over `k`, and it is strongly cartesian because `𝒴` is
fibred in groupoids, so the chosen restriction of `f(X)` along `k` is isomorphic over the
identity to `f(g(W))`, which has the property by hypothesis.
`AlgebraicGeometry.Stack.prop_of_locally_isoOverId` descends this to `f(X)`. -/
theorem forall_prop_of_forall_comp {𝒲 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒳)
    (hsurj : IsSurjective B S hS g)
    (hflat : AlgebraicStacks.IsFlat B S hS g)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    {P : ObjectProperty 𝒴.val.val.obj} [P.IsClosedUnderIsomorphisms]
    (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴 P))
    (h : ∀ W : 𝒲.val.val.obj, P ((g ≫ f).hom.hom.obj W)) :
    ∀ X : 𝒳.val.val.obj, P (f.hom.hom.obj X) := by
  have hfibY : 𝒴.val.val.p.IsFibered := 𝒴.val.property.isFibered
  intro X
  obtain ⟨R, hR, hloc⟩ :=
    exists_fppfCovering_fibre_lift B S hS g hsurj hflat hlfp (𝒳.val.val.p.obj X) ⟨X, rfl⟩
  refine prop_of_locally_isoOverId hPalg ⟨f.hom.hom.obj X, f.hom.hom.w_obj X⟩ hR ?_
  intro V k hk
  obtain ⟨W, α, hα⟩ := hloc hk
  have : 𝒴.val.val.p.IsHomLift k (f.hom.hom.toFunctor.map α) :=
    Functor.isHomLift_map_of_comp_eq f.hom.hom.w k α
  have := 𝒴.val.property.isStronglyCartesian_homLift k (f.hom.hom.toFunctor.map α)
  exact Functor.isoOverId_pullbackFiber 𝒴.val.val.p P
    ⟨f.hom.hom.obj X, f.hom.hom.w_obj X⟩ k (f.hom.hom.toFunctor.map α) inferInstance (h W)

/-- Factoring through a fixed closed substack of the target is unchanged by precomposition with a
surjective, flat 1-morphism locally of finite presentation.

One direction is formal, the composite factoring through whatever the 1-morphism does. The other
is `AlgebraicGeometry.Stack.forall_prop_of_forall_comp`, both sides being read objectwise. -/
theorem factorsThroughSubstack_comp_iff {𝒲 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒳)
    (hsurj : IsSurjective B S hS g)
    (hflat : AlgebraicStacks.IsFlat B S hS g)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    {P : ObjectProperty 𝒴.val.val.obj} (hP : IsClosedSubstack 𝒴 P) :
    FactorsThroughSubstack f P ↔ FactorsThroughSubstack (g ≫ f) P := by
  have hiso : P.IsClosedUnderIsomorphisms := hP.1
  rw [factorsThroughSubstack_iff_forall, factorsThroughSubstack_iff_forall]
  exact ⟨fun h W => h _,
    fun h => forall_prop_of_forall_comp f g hsurj hflat hlfp hP.2.choose h⟩

/-- Being the scheme theoretic image is unchanged by precomposition with a surjective, flat
1-morphism locally of finite presentation: both the factorization through a closed substack and
the minimality among closed substacks are, by
`AlgebraicGeometry.Stack.factorsThroughSubstack_comp_iff`. -/
theorem isSchemeTheoreticImage_comp_iff {𝒲 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒳)
    (hsurj : IsSurjective B S hS g)
    (hflat : AlgebraicStacks.IsFlat B S hS g)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    {P : ObjectProperty 𝒴.val.val.obj} :
    IsSchemeTheoreticImage f P ↔ IsSchemeTheoreticImage (g ≫ f) P :=
  and_congr_right fun hP => and_congr (factorsThroughSubstack_comp_iff f g hsurj hflat hlfp hP)
    (forall₂_congr fun _ hQ =>
      imp_congr_left (factorsThroughSubstack_comp_iff f g hsurj hflat hlfp hQ))

/-- **Stacks 0CMJ**, the existence assertion. Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic
stacks over `S` and let `g : 𝒲 ⟶ 𝒳` be a surjective, flat 1-morphism locally of finite
presentation. Then the scheme theoretic image of `f` exists if and only if the scheme theoretic
image of `g ≫ f` exists. -/
@[stacks 0CMJ "existence_iff"]
theorem hasSchemeTheoreticImage_comp_iff {𝒲 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒳)
    (hsurj : IsSurjective B S hS g)
    (hflat : AlgebraicStacks.IsFlat B S hS g)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g) :
    HasSchemeTheoreticImage f ↔ HasSchemeTheoreticImage (g ≫ f) :=
  ⟨fun ⟨P, hP⟩ => ⟨P, (isSchemeTheoreticImage_comp_iff f g hsurj hflat hlfp).1 hP⟩,
    fun ⟨P, hP⟩ => ⟨P, (isSchemeTheoreticImage_comp_iff f g hsurj hflat hlfp).2 hP⟩⟩

/-- **Stacks 0CMJ**, the agreement of the two images. Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
algebraic stacks over `S` and let `g : 𝒲 ⟶ 𝒳` be a surjective, flat 1-morphism locally of finite
presentation. If `P` is the scheme theoretic image of `f` and `Q` is the scheme theoretic image of
`g ≫ f`, then `P = Q`. -/
@[stacks 0CMJ "images_equal"]
theorem eq_of_isSchemeTheoreticImage_comp {𝒲 𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (g : 𝒲 ⟶ 𝒳)
    (hsurj : IsSurjective B S hS g)
    (hflat : AlgebraicStacks.IsFlat B S hS g)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS g)
    {P Q : ObjectProperty 𝒴.val.val.obj} (hP : IsSchemeTheoreticImage f P)
    (hQ : IsSchemeTheoreticImage (g ≫ f) Q) : P = Q :=
  ((isSchemeTheoreticImage_comp_iff f g hsurj hflat hlfp).1 hP).unique hQ

section InverseImage

variable {𝒴₁ 𝒴₂ : AlgebraicStacks.{u, w} B S hS}

/-- The comparison functor from the full subcategory of `𝒴₁` cut out by the preimage of a
property `P` of the objects of `𝒴₂` under a 1-morphism `b : 𝒴₁ ⟶ 𝒴₂`, to the 2-fibre product of
`𝒴₁` with the full subcategory of `𝒴₂` cut out by `P`: an object `X` with `P (b X)` goes to the
pair `(X, b X)` with identity comparison isomorphism. -/
def inverseImageToTwoFibreProduct (b : 𝒴₁ ⟶ 𝒴₂) (P : ObjectProperty 𝒴₂.val.val.obj) :
    (P.inverseImage b.hom.hom.toFunctor).FullSubcategory ⥤
      TwoFibreProductOver 𝒴₁.val.val.p (P.ι ⋙ 𝒴₂.val.val.p) 𝒴₂.val.val.p
        b.hom.hom.toFunctor P.ι where
  obj X :=
    { base := 𝒴₁.val.val.p.obj X.obj
      x := X.obj
      y := ⟨b.hom.hom.toFunctor.obj X.obj, X.property⟩
      hx := rfl
      hy := Functor.congr_obj b.hom.hom.w X.obj
      iso := Iso.refl _
      vertical := IsHomLift.id (Functor.congr_obj b.hom.hom.w X.obj) }
  map {X Y} φ :=
    TwoFibreProductOver.Hom.mk' φ.hom (ObjectProperty.homMk (b.hom.hom.toFunctor.map φ.hom))
      (by
        have h := Functor.congr_hom b.hom.hom.w φ.hom
        simp only [Functor.comp_map] at h
        simp [h])
      (by simp)
  map_id X := TwoFibreProductOver.Hom.ext' rfl (ObjectProperty.hom_ext P (by simp))
  map_comp {X Y Z} φ ψ :=
    TwoFibreProductOver.Hom.ext' rfl (ObjectProperty.hom_ext P (by simp))

/-- The comparison functor back: an object of the 2-fibre product of `𝒴₁` with the full
subcategory of `𝒴₂` cut out by `P` has its `𝒴₁`-component in the preimage of `P`, by the
comparison isomorphism. -/
def twoFibreProductToInverseImage (b : 𝒴₁ ⟶ 𝒴₂) (P : ObjectProperty 𝒴₂.val.val.obj)
    [P.IsClosedUnderIsomorphisms] :
    TwoFibreProductOver 𝒴₁.val.val.p (P.ι ⋙ 𝒴₂.val.val.p) 𝒴₂.val.val.p
        b.hom.hom.toFunctor P.ι ⥤ (P.inverseImage b.hom.hom.toFunctor).FullSubcategory where
  obj T := ⟨T.x, P.prop_of_iso T.iso.symm T.y.property⟩
  map φ := ObjectProperty.homMk φ.a
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The 2-fibre product of `𝒴₁` with the full subcategory of `𝒴₂` cut out by `P`, along a
1-morphism `b : 𝒴₁ ⟶ 𝒴₂`, as a category over the big fppf site of `S`. -/
abbrev inverseImageTwoFibreProduct (b : 𝒴₁ ⟶ 𝒴₂) (P : ObjectProperty 𝒴₂.val.val.obj) :
    BasedCategory.{u, u + 1} (BigFppfOver B S hS) :=
  BasedCategory.ofFunctor (TwoFibreProductOver.structureFunctor 𝒴₁.val.val.p
    (P.ι ⋙ 𝒴₂.val.val.p) 𝒴₂.val.val.p b.hom.hom.toFunctor P.ι)

/-- `AlgebraicGeometry.Stack.inverseImageToTwoFibreProduct` as a 1-morphism over the big fppf
site of `S`: an object of the preimage subcategory and its image in the 2-fibre product lie over
the same object of the site. -/
def inverseImageToTwoFibreProductBased (b : 𝒴₁ ⟶ 𝒴₂) (P : ObjectProperty 𝒴₂.val.val.obj) :
    fullSubcategoryBased 𝒴₁ (P.inverseImage b.hom.hom.toFunctor) ⥤ᵇ
      inverseImageTwoFibreProduct b P where
  toFunctor := inverseImageToTwoFibreProduct b P
  w := CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => rfl)

/-- `AlgebraicGeometry.Stack.twoFibreProductToInverseImage` as a 1-morphism over the big fppf
site of `S`: the `𝒴₁`-component of an object of the 2-fibre product lies over its base. -/
def twoFibreProductToInverseImageBased (b : 𝒴₁ ⟶ 𝒴₂) (P : ObjectProperty 𝒴₂.val.val.obj)
    [P.IsClosedUnderIsomorphisms] :
    inverseImageTwoFibreProduct b P ⥤ᵇ
      fullSubcategoryBased 𝒴₁ (P.inverseImage b.hom.hom.toFunctor) where
  toFunctor := twoFibreProductToInverseImage b P
  w := CategoryTheory.Functor.ext (fun T => T.hx) (fun T T' φ => by
    have := φ.ha
    change 𝒴₁.val.val.p.map φ.a = eqToHom T.hx ≫ φ.hbase ≫ eqToHom T'.hx.symm
    exact IsHomLift.fac' 𝒴₁.val.val.p φ.hbase φ.a)

/-- Reading an object `T` of the 2-fibre product through its `𝒴₁`-component and back returns the
pair `(T.x, b T.x)`, which is isomorphic to `T` by the comparison isomorphism of `T`. -/
def twoFibreProductInverseImageIso (b : 𝒴₁ ⟶ 𝒴₂) (P : ObjectProperty 𝒴₂.val.val.obj)
    [P.IsClosedUnderIsomorphisms]
    (T : TwoFibreProductOver 𝒴₁.val.val.p (P.ι ⋙ 𝒴₂.val.val.p) 𝒴₂.val.val.p
      b.hom.hom.toFunctor P.ι) :
    (inverseImageToTwoFibreProduct b P).obj ((twoFibreProductToInverseImage b P).obj T) ≅ T where
  hom :=
    { hbase := eqToHom T.hx
      a := 𝟙 T.x
      b := ObjectProperty.homMk T.iso.hom
      ha := IsHomLift.id_lift_eqToHom_domain T.hx rfl
      hb := by
        have := T.vertical
        have h : 𝒴₂.val.val.p.IsHomLift (eqToHom T.hx) T.iso.hom :=
          IsHomLift.of_fac' 𝒴₂.val.val.p (eqToHom T.hx) T.iso.hom
            (Functor.congr_obj b.hom.hom.w T.x) T.hy (by
              rw [IsHomLift.fac' 𝒴₂.val.val.p (𝟙 T.base) T.iso.hom]; simp)
        exact (Functor.isHomLift_comp_iff P.ι 𝒴₂.val.val.p (eqToHom T.hx) _).2 h
      w := by
        change b.hom.hom.toFunctor.map (𝟙 T.x) ≫ T.iso.hom = 𝟙 _ ≫ T.iso.hom
        simp }
  inv :=
    { hbase := eqToHom T.hx.symm
      a := 𝟙 T.x
      b := ObjectProperty.homMk T.iso.inv
      ha := IsHomLift.id_lift_eqToHom_codomain T.hx.symm rfl
      hb := by
        have := T.vertical
        have := IsHomLift.lift_id_inv 𝒴₂.val.val.p T.base T.iso
        have h : 𝒴₂.val.val.p.IsHomLift (eqToHom T.hx.symm) T.iso.inv :=
          IsHomLift.of_fac' 𝒴₂.val.val.p (eqToHom T.hx.symm) T.iso.inv
            T.hy (Functor.congr_obj b.hom.hom.w T.x) (by
              rw [IsHomLift.fac' 𝒴₂.val.val.p (𝟙 T.base) T.iso.inv]; simp)
        exact (Functor.isHomLift_comp_iff P.ι 𝒴₂.val.val.p (eqToHom T.hx.symm) _).2 h
      w := by
        change b.hom.hom.toFunctor.map (𝟙 T.x) ≫ 𝟙 _ = T.iso.hom ≫ T.iso.inv
        simp }
  hom_inv_id :=
    TwoFibreProductOver.Hom.ext' (Category.comp_id _) (ObjectProperty.hom_ext P T.iso.hom_inv_id)
  inv_hom_id :=
    TwoFibreProductOver.Hom.ext' (Category.comp_id _) (ObjectProperty.hom_ext P T.iso.inv_hom_id)

/-- The full subcategory of `𝒴₁` cut out by the preimage of `P` under `b` is equivalent, over the
big fppf site of `S`, to the 2-fibre product of `𝒴₁` with the full subcategory of `𝒴₂` cut out by
`P`. Both composites are the identity, one on the nose and the other by
`AlgebraicGeometry.Stack.twoFibreProductInverseImageIso`. -/
def inverseImageEquivalence (b : 𝒴₁ ⟶ 𝒴₂) (P : ObjectProperty 𝒴₂.val.val.obj)
    [P.IsClosedUnderIsomorphisms] :
    BasedCategory.Equivalence (inverseImageTwoFibreProduct b P)
      (fullSubcategoryBased 𝒴₁ (P.inverseImage b.hom.hom.toFunctor)) where
  functor := twoFibreProductToInverseImageBased b P
  inverse := inverseImageToTwoFibreProductBased b P
  unitIso := BasedNatIso.mkNatIso
    (NatIso.ofComponents (fun T => twoFibreProductInverseImageIso b P T) (fun {T T'} φ =>
      TwoFibreProductOver.Hom.ext'
        ((Category.comp_id φ.a).trans (Category.id_comp φ.a).symm)
        (ObjectProperty.hom_ext P φ.w)))
    (fun T => IsHomLift.of_fac' (inverseImageTwoFibreProduct b P).p (𝟙 T.base)
      (twoFibreProductInverseImageIso b P T).hom T.hx rfl (by
        change eqToHom T.hx = eqToHom T.hx ≫ 𝟙 T.base ≫ eqToHom rfl
        simp))
  counitIso := BasedNatIso.mkNatIso (Iso.refl _) (fun _ => IsHomLift.id rfl)

/-- The full subcategory of `𝒴₁` cut out by the preimage of a substack of `𝒴₂` which is an
algebraic stack is itself an algebraic stack: it is equivalent over the big fppf site of `S` to
the 2-fibre product of `𝒴₁` with that substack, which is an algebraic stack by **Stacks 04T2**,
and being an algebraic stack is invariant under such an equivalence by **Stacks 03YQ**. -/
theorem isAlgebraicStack_inverseImage (b : 𝒴₁ ⟶ 𝒴₂) (P : ObjectProperty 𝒴₂.val.val.obj)
    [P.IsClosedUnderIsomorphisms]
    (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴₂ P)) :
    IsAlgebraicStack.{u, w} B S hS
      (fullSubcategoryBased 𝒴₁ (P.inverseImage b.hom.hom.toFunctor)) :=
  isAlgebraicStack_of_equivalence.{u, u, u + 1, w} B S hS (inverseImageEquivalence b P)
    (isAlgebraicStack_twoFibreProductSquare B S hS b (fullSubcategoryInclusion 𝒴₂ P hPalg))

/-- The square exhibiting the full subcategory of `𝒴₁` cut out by the preimage of `P` as a base
change along `b` of the full subcategory of `𝒴₂` cut out by `P`: its legs are the inclusion and
the 1-morphism sending `X` to `b X`, and the two composites to `𝒴₂` agree on the nose. -/
def inverseImageSquare (b : 𝒴₁ ⟶ 𝒴₂) (P : ObjectProperty 𝒴₂.val.val.obj)
    [P.IsClosedUnderIsomorphisms]
    (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴₂ P)) :
    Bicategory.TwoCommSq b (fullSubcategoryInclusion 𝒴₂ P hPalg) where
  pt := fullSubcategoryAlgebraicStack 𝒴₁ (P.inverseImage b.hom.hom.toFunctor)
    (isAlgebraicStack_inverseImage b P hPalg)
  fst := fullSubcategoryInclusion 𝒴₁ (P.inverseImage b.hom.hom.toFunctor)
    (isAlgebraicStack_inverseImage b P hPalg)
  snd := Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := ObjectProperty.lift P
        ((P.inverseImage b.hom.hom.toFunctor).ι ⋙ b.hom.hom.toFunctor) (fun X => X.property)
      w := by
        change ((P.inverseImage b.hom.hom.toFunctor).ι ⋙ b.hom.hom.toFunctor) ⋙
          𝒴₂.val.val.p = _
        rw [Functor.assoc, b.hom.hom.w]
        rfl })
  iso := Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso (Iso.refl _)
      (fun X => IsHomLift.id (Functor.congr_obj b.hom.hom.w X.obj))))

/-- The comparison 1-morphism from `AlgebraicGeometry.Stack.inverseImageSquare` to the canonical
2-fibre product square acts as `AlgebraicGeometry.Stack.inverseImageToTwoFibreProduct`: the two
agree on objects and their morphisms have the same two components. -/
def liftInverseImageSquareIso (b : 𝒴₁ ⟶ 𝒴₂) (P : ObjectProperty 𝒴₂.val.val.obj)
    [P.IsClosedUnderIsomorphisms]
    (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴₂ P)) :
    (CatFiberedInGroupoids.liftTwoFibreProductSquare.{u, u, u + 1, u + 1} b.hom
        (fullSubcategoryInclusion 𝒴₂ P hPalg).hom
        (inverseImageSquare b P hPalg).underlying).hom.toFunctor ≅
      inverseImageToTwoFibreProduct b P :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun φ =>
    TwoFibreProductOver.Hom.ext'
      ((Category.comp_id φ.hom).trans (Category.id_comp φ.hom).symm)
      (ObjectProperty.hom_ext P ((Category.comp_id _).trans (Category.id_comp _).symm)))

/-- **The preimage square is a 2-fibre product.** Its comparison 1-morphism to the canonical
2-fibre product square of the same cospan is an equivalence of the underlying categories, by
`AlgebraicGeometry.Stack.inverseImageEquivalence`, so the square of categories fibred in
groupoids underlying it is a 2-fibre product; the 2-category of algebraic stacks being full, so
is the square itself. -/
noncomputable def isTwoFibreProduct_inverseImageSquare (b : 𝒴₁ ⟶ 𝒴₂)
    (P : ObjectProperty 𝒴₂.val.val.obj) [P.IsClosedUnderIsomorphisms]
    (hPalg : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴₂ P)) :
    Bicategory.IsTwoFibreProduct (inverseImageSquare b P hPalg) := by
  haveI hequiv : (inverseImageToTwoFibreProduct b P).IsEquivalence :=
    (inverseImageEquivalence b P).symm.equiv.isEquivalence_functor
  refine Bicategory.isTwoFibreProduct_of_underlying
    (Bicategory.isTwoFibreProduct_of_isEquivalence_to
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        b.hom (fullSubcategoryInclusion 𝒴₂ P hPalg).hom)
      (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u, u + 1, u + 1} b.hom
        (fullSubcategoryInclusion 𝒴₂ P hPalg).hom (inverseImageSquare b P hPalg).underlying)
      ?_)
  exact (Functor.isEquivalence_iff_of_iso (liftInverseImageSquareIso b P hPalg)).2 hequiv

/-- **The preimage of a closed substack is a closed substack.** Let `b : 𝒴₁ ⟶ 𝒴₂` be a
1-morphism of algebraic stacks over `S` and let `P` cut out a closed substack of `𝒴₂`. Then the
preimage of `P` under `b` cuts out a closed substack of `𝒴₁`.

The full subcategory it cuts out is the base change along `b` of the one `P` cuts out
(`AlgebraicGeometry.Stack.isTwoFibreProduct_inverseImageSquare`), so it is an algebraic stack and
its inclusion is a closed immersion because closed immersions are stable under base change. -/
theorem isClosedSubstack_inverseImage (b : 𝒴₁ ⟶ 𝒴₂) {P : ObjectProperty 𝒴₂.val.val.obj}
    (hP : IsClosedSubstack 𝒴₂ P) :
    IsClosedSubstack 𝒴₁ (P.inverseImage b.hom.hom.toFunctor) := by
  obtain ⟨_, hPalg, hclosed⟩ := hP
  exact ⟨inferInstance, isAlgebraicStack_inverseImage b P hPalg,
    AlgebraicStacks.isClosedImmersion_baseChange B S hS (inverseImageSquare b P hPalg)
      (isTwoFibreProduct_inverseImageSquare b P hPalg) hclosed⟩

/-- The 1-morphism of substacks induced by a 1-morphism `b : 𝒴₁ ⟶ 𝒴₂` which carries the
substack cut out by `P₁` into the one cut out by `P₂`: on objects it is `b` itself, tagged with
the containment. -/
def substackMapOfLe (b : 𝒴₁ ⟶ 𝒴₂) {P₁ : ObjectProperty 𝒴₁.val.val.obj}
    {P₂ : ObjectProperty 𝒴₂.val.val.obj}
    (hA₁ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴₁ P₁))
    (hA₂ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴₂ P₂))
    (hle : P₁ ≤ P₂.inverseImage b.hom.hom.toFunctor) :
    fullSubcategoryAlgebraicStack 𝒴₁ P₁ hA₁ ⟶ fullSubcategoryAlgebraicStack 𝒴₂ P₂ hA₂ :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    { toFunctor := ObjectProperty.lift P₂ (P₁.ι ⋙ b.hom.hom.toFunctor)
        (fun X => hle X.obj X.property)
      w := by
        change (P₁.ι ⋙ b.hom.hom.toFunctor) ⋙ 𝒴₂.val.val.p = _
        rw [Functor.assoc, b.hom.hom.w]
        rfl })

/-- The induced 1-morphism of substacks is `b` on objects, so composing it with the inclusion of
the target substack gives the inclusion of the source substack followed by `b`. -/
theorem substackMapOfLe_comp_inclusion (b : 𝒴₁ ⟶ 𝒴₂) {P₁ : ObjectProperty 𝒴₁.val.val.obj}
    {P₂ : ObjectProperty 𝒴₂.val.val.obj}
    (hA₁ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴₁ P₁))
    (hA₂ : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴₂ P₂))
    (hle : P₁ ≤ P₂.inverseImage b.hom.hom.toFunctor) :
    substackMapOfLe b hA₁ hA₂ hle ≫ fullSubcategoryInclusion 𝒴₂ P₂ hA₂ =
      fullSubcategoryInclusion 𝒴₁ P₁ hA₁ ≫ b :=
  rfl

/-- A vertical 2-isomorphism between two 1-morphisms into a substack can be read off one between
their composites with the inclusion, the inclusion of a full subcategory being fully faithful and
its components lying over identities. -/
def twoIsoOfCompInclusion {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    {P : ObjectProperty 𝒴.val.val.obj}
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒴 P))
    {F G : 𝒳 ⟶ fullSubcategoryAlgebraicStack 𝒴 P hA}
    (e : F ≫ fullSubcategoryInclusion 𝒴 P hA ≅ G ≫ fullSubcategoryInclusion 𝒴 P hA) :
    F ≅ G :=
  Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso
      (NatIso.ofComponents
        (fun X => ObjectProperty.isoMk P
          ((CatFiberedInGroupoids.underlyingIso (algebraicStacksTwoIsoHom B S hS e)).app X))
        (fun φ => ObjectProperty.hom_ext P
          ((CatFiberedInGroupoids.underlyingIso
            (algebraicStacksTwoIsoHom B S hS e)).hom.naturality φ)))
      (fun X => (Functor.isHomLift_comp_iff P.ι 𝒴.val.val.p (𝟙 (𝒳.val.val.p.obj X)) _).2
        (e.hom.hom.hom.isHomLift' X))))

end InverseImage

section SchemeTheoreticImageMap

variable {𝒳₁ 𝒳₂ 𝒴₁ 𝒴₂ : AlgebraicStacks.{u, w} B S hS}

/-- In a commutative square of algebraic stacks, if `f₂` factors through the substack cut out by
`P₂` then `f₁` factors through the preimage of `P₂`: the square identifies `b (f₁ X)` with
`f₂ (a X)`, which lies in `P₂`, and `P₂` is closed under isomorphism. -/
theorem factorsThroughSubstack_inverseImage {f₁ : 𝒳₁ ⟶ 𝒴₁} {f₂ : 𝒳₂ ⟶ 𝒴₂} {a : 𝒳₁ ⟶ 𝒳₂}
    {b : 𝒴₁ ⟶ 𝒴₂} (sq : f₁ ≫ b ≅ a ≫ f₂) {P₂ : ObjectProperty 𝒴₂.val.val.obj}
    [P₂.IsClosedUnderIsomorphisms] (h₂ : FactorsThroughSubstack f₂ P₂) :
    FactorsThroughSubstack f₁ (P₂.inverseImage b.hom.hom.toFunctor) := by
  rw [factorsThroughSubstack_iff_forall]
  intro X
  exact P₂.prop_of_iso
    ((CatFiberedInGroupoids.underlyingIso (algebraicStacksTwoIsoHom B S hS sq)).app X).symm
    ((factorsThroughSubstack_iff_forall f₂).1 h₂ (a.hom.hom.obj X))

/-- **Stacks 0CPV**, the containment that induces the morphism. Let a commutative square of
algebraic stacks over `S` be given, with horizontal 1-morphisms `f₁ : 𝒳₁ ⟶ 𝒴₁`, `f₂ : 𝒳₂ ⟶ 𝒴₂`
and vertical ones `a : 𝒳₁ ⟶ 𝒳₂`, `b : 𝒴₁ ⟶ 𝒴₂`, and let `Pᵢ` be the scheme theoretic image of
`fᵢ`. Then `P₁` is contained in the preimage of `P₂` under `b`.

The preimage of `P₂` cuts out a closed substack of `𝒴₁`
(`AlgebraicGeometry.Stack.isClosedSubstack_inverseImage`) through which `f₁` factors
(`AlgebraicGeometry.Stack.factorsThroughSubstack_inverseImage`), so the minimality of the scheme
theoretic image applies to it. -/
@[stacks 0CPV "containment"]
theorem le_inverseImage_of_isSchemeTheoreticImage {f₁ : 𝒳₁ ⟶ 𝒴₁} {f₂ : 𝒳₂ ⟶ 𝒴₂} {a : 𝒳₁ ⟶ 𝒳₂}
    {b : 𝒴₁ ⟶ 𝒴₂} (sq : f₁ ≫ b ≅ a ≫ f₂) {P₁ : ObjectProperty 𝒴₁.val.val.obj}
    {P₂ : ObjectProperty 𝒴₂.val.val.obj} (h₁ : IsSchemeTheoreticImage f₁ P₁)
    (h₂ : IsSchemeTheoreticImage f₂ P₂) :
    P₁ ≤ P₂.inverseImage b.hom.hom.toFunctor := by
  have := h₂.1.1
  exact h₁.2.2 _ (isClosedSubstack_inverseImage b h₂.1)
    (factorsThroughSubstack_inverseImage sq h₂.2.1)

/-- **Stacks 0CPV**, the induced 1-morphism. The 1-morphism `b : 𝒴₁ ⟶ 𝒴₂` of a commutative
square of algebraic stacks carries the scheme theoretic image of `f₁` into the scheme theoretic
image of `f₂`, and therefore induces a 1-morphism `𝒵₁ ⟶ 𝒵₂` between them. -/
@[stacks 0CPV "induced_morphism"]
def schemeTheoreticImageMap {f₁ : 𝒳₁ ⟶ 𝒴₁} {f₂ : 𝒳₂ ⟶ 𝒴₂} {a : 𝒳₁ ⟶ 𝒳₂} {b : 𝒴₁ ⟶ 𝒴₂}
    (sq : f₁ ≫ b ≅ a ≫ f₂) {P₁ : ObjectProperty 𝒴₁.val.val.obj}
    {P₂ : ObjectProperty 𝒴₂.val.val.obj} (h₁ : IsSchemeTheoreticImage f₁ P₁)
    (h₂ : IsSchemeTheoreticImage f₂ P₂) :
    fullSubcategoryAlgebraicStack 𝒴₁ P₁ h₁.isAlgebraicStack ⟶
      fullSubcategoryAlgebraicStack 𝒴₂ P₂ h₂.isAlgebraicStack :=
  substackMapOfLe b h₁.isAlgebraicStack h₂.isAlgebraicStack
    (le_inverseImage_of_isSchemeTheoreticImage sq h₁ h₂)

/-- **Stacks 0CPV**, the right-hand square of the induced diagram: the induced 1-morphism
`𝒵₁ ⟶ 𝒵₂` composed with the inclusion `𝒵₂ ⟶ 𝒴₂` is the inclusion `𝒵₁ ⟶ 𝒴₁` followed by `b`. -/
@[stacks 0CPV "inclusion_square"]
theorem schemeTheoreticImageMap_comp_inclusion {f₁ : 𝒳₁ ⟶ 𝒴₁} {f₂ : 𝒳₂ ⟶ 𝒴₂} {a : 𝒳₁ ⟶ 𝒳₂}
    {b : 𝒴₁ ⟶ 𝒴₂} (sq : f₁ ≫ b ≅ a ≫ f₂) {P₁ : ObjectProperty 𝒴₁.val.val.obj}
    {P₂ : ObjectProperty 𝒴₂.val.val.obj} (h₁ : IsSchemeTheoreticImage f₁ P₁)
    (h₂ : IsSchemeTheoreticImage f₂ P₂) :
    schemeTheoreticImageMap sq h₁ h₂ ≫ fullSubcategoryInclusion 𝒴₂ P₂ h₂.isAlgebraicStack =
      fullSubcategoryInclusion 𝒴₁ P₁ h₁.isAlgebraicStack ≫ b :=
  rfl

/-- **Stacks 0CPV**, the left-hand square of the induced diagram. Let `kᵢ : 𝒳ᵢ ⟶ 𝒵ᵢ` be
factorizations of `fᵢ` through the scheme theoretic images. Then the induced 1-morphism
`𝒵₁ ⟶ 𝒵₂` makes the square with `a : 𝒳₁ ⟶ 𝒳₂` 2-commute.

Both composites `𝒳₁ ⟶ 𝒵₂ ⟶ 𝒴₂` are 2-isomorphic, by the given square and the two
factorizations, and the inclusion of `𝒵₂` is fully faithful, so the 2-isomorphism descends to
`𝒵₂`. -/
@[stacks 0CPV "factorization_square"]
noncomputable def schemeTheoreticImageMapFactorizationSquare {f₁ : 𝒳₁ ⟶ 𝒴₁} {f₂ : 𝒳₂ ⟶ 𝒴₂}
    {a : 𝒳₁ ⟶ 𝒳₂} {b : 𝒴₁ ⟶ 𝒴₂} (sq : f₁ ≫ b ≅ a ≫ f₂)
    {P₁ : ObjectProperty 𝒴₁.val.val.obj} {P₂ : ObjectProperty 𝒴₂.val.val.obj}
    (h₁ : IsSchemeTheoreticImage f₁ P₁) (h₂ : IsSchemeTheoreticImage f₂ P₂)
    (k₁ : 𝒳₁ ⟶ fullSubcategoryAlgebraicStack 𝒴₁ P₁ h₁.isAlgebraicStack)
    (k₂ : 𝒳₂ ⟶ fullSubcategoryAlgebraicStack 𝒴₂ P₂ h₂.isAlgebraicStack)
    (e₁ : k₁ ≫ fullSubcategoryInclusion 𝒴₁ P₁ h₁.isAlgebraicStack ≅ f₁)
    (e₂ : k₂ ≫ fullSubcategoryInclusion 𝒴₂ P₂ h₂.isAlgebraicStack ≅ f₂) :
    k₁ ≫ schemeTheoreticImageMap sq h₁ h₂ ≅ a ≫ k₂ :=
  twoIsoOfCompInclusion h₂.isAlgebraicStack
    ((Bicategory.associator k₁ (schemeTheoreticImageMap sq h₁ h₂)
          (fullSubcategoryInclusion 𝒴₂ P₂ h₂.isAlgebraicStack)).symm ≪≫
      Bicategory.whiskerLeftIso k₁
        (eqToIso (schemeTheoreticImageMap_comp_inclusion sq h₁ h₂)) ≪≫
      Bicategory.associator k₁ (fullSubcategoryInclusion 𝒴₁ P₁ h₁.isAlgebraicStack) b ≪≫
      Bicategory.whiskerRightIso e₁ b ≪≫ sq ≪≫
      Bicategory.whiskerLeftIso a e₂.symm ≪≫
      (Bicategory.associator a k₂ (fullSubcategoryInclusion 𝒴₂ P₂ h₂.isAlgebraicStack)).symm)

end SchemeTheoreticImageMap

end AlgebraicGeometry.Stack

end
