module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTripleTwist
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence

/-!
# Twisting a morphism, and a short exact sequence, of coherent triples

Let `A` be a local ring and `f ∈ A`, and let `(L, L₀, λ)` be an invertible coherent triple for
`(A, f)`. Tensoring with a pair of invertible modules identified over the punctured closed fibre
is functorial and exact on coherent triples: a morphism `(F, F₀, α) ⟶ (G, G₀, β)` induces a
morphism of the twists, and a short exact sequence of coherent triples induces a short exact
sequence of the twists. In particular both hold for the integer twists by `(L, L₀, λ)`.

The content of the functoriality is the compatibility over the punctured closed fibre: the square
formed by the twisted morphism and the twisted identifications commutes. It is pasted from two
instances of the naturality of [Stacks, Tag 01CD] in its module arguments and one instance of the
compatibility of the original morphism. The content of the exactness is that tensoring on the
right by an invertible module is an equivalence of categories, hence preserves finite limits and
colimits, hence carries a short exact sequence to a short exact sequence.

## Main definitions

* `Stacks.Algebraization.tensorSheafMapPair` and `Stacks.Algebraization.tensorModulesMap`: the
  tensor product of two morphisms of `𝒪_X`-modules, at the bifunctor's own spelling and at the
  spelling the triples' identifications are written in.
* `Stacks.Algebraization.CoherentTriple.Hom.tensorInvertible` and
  `Stacks.Algebraization.CoherentTriple.Hom.twistZ`: the twist of a morphism of coherent triples
  by an invertible coherent triple, and by its `n`-th tensor power.
* `Stacks.Algebraization.CoherentTriple.Hom.inverse`: **the inverse of a morphism of coherent
  triples both of whose members are isomorphisms** — the inverse of an identification of two
  coherent triples, there being no `Iso` of coherent triples.

## Main results

* `Stacks.Algebraization.tensorModulesMap_comp` and
  `Stacks.Algebraization.tensorModulesMap_id`: functoriality of the tensor product in both
  arguments.
* `Stacks.Algebraization.pullbackTensorModulesIso_naturality`: **[Stacks, Tag 01CD] is natural in
  both module arguments.**
* `Stacks.Algebraization.compatible_tensorModule`: the compatibility square of a twisted
  morphism of coherent triples.
* `Stacks.Algebraization.comp_eq_of_three_squares`: three commuting squares in a row paste to one
  commuting rectangle.
* `Stacks.Algebraization.CoherentTriple.ShortExact.tensorInvertible` and
  `Stacks.Algebraization.CoherentTriple.ShortExact.twistZ`: **a short exact sequence of coherent
  triples stays short exact after twisting.**
* `Stacks.Algebraization.CoherentTriple.ShortExact.midIso`: **a short exact sequence of coherent
  triples stays short exact when its middle term is replaced by an isomorphic one** -- the
  companion of `Stacks.Algebraization.CoherentTriple.ShortExact.compIso` and
  `Stacks.Algebraization.CoherentTriple.ShortExact.isoComp`, which move the third and the first
  term, and the one of the three that needs
  `Stacks.Algebraization.CoherentTriple.Hom.inverse`.

## Implementation notes

`Stacks.Algebraization.tensorModulesMap` is the action of the bifunctor
`Stacks.RingedSpace.tensorSheaf` on a pair of morphisms, and
`Stacks.Algebraization.pullbackTensorModulesIso_naturality` is the naturality of the isomorphism
of bifunctors `Stacks.PullbackTensorIso.pullbackTensorIso` at a pair of morphisms. Both are
two-line consequences of the bifunctor, but they have to be *stated* at the
`Stacks.RelativeVeryAmple.tensorModules` spelling, because that is the spelling the triples'
identifications are written in.

The passage between the two spellings is the one place that costs something. Elaborating
`(Stacks.RingedSpace.tensorSheaf X.toRingedSpace).map (a, b)` against an expected type written
with `Stacks.RelativeVeryAmple.tensorModules` exhausts the heartbeat budget: the type of the pair
`(a, b)` has to be read off the expected type, which sends the unifier through the sheafification
that the tensor product is. Supplying the pair's type explicitly does not help. So the morphism is
built in two steps — `Stacks.Algebraization.tensorSheafMapPair` at the bifunctor's own spelling,
then `Stacks.Algebraization.tensorModulesMap` as that morphism read at the other spelling, where
the objects are already determined and the conversion is immediate.

Exactness is `CategoryTheory.ShortComplex.ShortExact.map_of_exact` applied to
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorRightModules`, which is tensoring on the
right read as an endofunctor of `X.Modules`; the three instances that result needs --
preservation of zero morphisms, of finite limits and of finite colimits -- are proved there for an
invertible module, so nothing about additivity has to be proved. That the twisted morphisms are
*defined* as the image of a morphism under that functor, rather than as
`Stacks.Algebraization.tensorModulesMap` of the morphism with an identity, is what makes the
exactness statement reachable: the two are equal by
`Stacks.Algebraization.tensorRightModules_map`, and with the functor spelling the twisted short
complex and the image of the untwisted one differ only in how their objects are written, so the
conversion stays at the level of objects. Written the other way the whole `ShortExact` structure
has to be converted, which exhausts the heartbeat budget.

That equation is *not* definitional. `Stacks.Algebraization.tensorModulesMap` is
`CategoryTheory.Functor.uncurry` of the tensor bifunctor at a pair, hence the composite of the
bifunctor's two legs, and the second leg at an identity is the identity only by
`CategoryTheory.Functor.map_id`. The compatibility square is therefore stated twice: once at the
bifunctor spelling as `Stacks.Algebraization.compatible_tensorModule`, and once at the functor
spelling, which is what the `compatible` fields below consume.

The diagram chase is performed in an abstract category, by
`Stacks.Algebraization.comp_eq_of_three_squares`, rather than in `X.Modules`. In `X.Modules` a
rewrite along `CategoryTheory.Category.assoc` does not fire — the category instance is reached
through a definition that the unifier does not unfold at reducible transparency — so neither
`rw`, nor `simp`, nor the associativity-normalising `reassoc_of%` and `slice_lhs` can be used on
the concrete square. Abstracting the objects and morphisms removes the obstruction entirely, and
the concrete statement is then a single application.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0F27](https://stacks.math.columbia.edu/tag/0F27)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.RelativeVeryAmple
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence (tensorRightModules)

universe u

namespace Stacks.Algebraization

/-! ### The tensor product of two morphisms of modules -/

/-- The tensor product of two morphisms of `𝒪_X`-modules, at the spelling of the bifunctor
`Stacks.RingedSpace.tensorSheaf` itself. Stating it this way is what keeps the type of the pair
of morphisms from having to be read off an expected type written with
`Stacks.RelativeVeryAmple.tensorModules`; see the implementation notes of this file. -/
public noncomputable def tensorSheafMapPair (X : Scheme.{u}) {A A' B B' : X.Modules}
    (a : A ⟶ A') (b : B ⟶ B') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩))).obj (A, B) ⟶
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩))).obj (A', B') :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩))).map (a, b)

/-- **The tensor product of two morphisms of `𝒪_X`-modules**, read off the bifunctor
`Stacks.RingedSpace.tensorSheaf`. -/
public noncomputable def tensorModulesMap (X : Scheme.{u}) {A A' B B' : X.Modules}
    (a : A ⟶ A') (b : B ⟶ B') : tensorModules X A B ⟶ tensorModules X A' B' :=
  tensorSheafMapPair X a b

/-- The tensor product of two isomorphisms is the tensor product of the two morphisms. -/
public theorem tensorModulesMapIso_hom (X : Scheme.{u}) {A A' B B' : X.Modules}
    (e : A ≅ A') (g : B ≅ B') :
    (tensorModulesMapIso X e g).hom = tensorModulesMap X e.hom g.hom := rfl

/-- **The tensor product of morphisms is compatible with composition.** -/
public theorem tensorModulesMap_comp (X : Scheme.{u}) {A A' A'' B B' B'' : X.Modules}
    (a : A ⟶ A') (a' : A' ⟶ A'') (b : B ⟶ B') (b' : B' ⟶ B'') :
    tensorModulesMap X a b ≫ tensorModulesMap X a' b' =
      tensorModulesMap X (a ≫ a') (b ≫ b') :=
  (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩))).map_comp
    (((a, b) : ((A, B) : X.Modules × X.Modules) ⟶ (A', B')))
    (((a', b') : ((A', B') : X.Modules × X.Modules) ⟶ (A'', B'')))).symm

/-- **The tensor product of two identities is the identity.** -/
public theorem tensorModulesMap_id (X : Scheme.{u}) (A B : X.Modules) :
    tensorModulesMap X (𝟙 A) (𝟙 B) = 𝟙 (tensorModules X A B) :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩))).map_id (A, B)

/-- **Tensoring on the right by `M` is the tensor product with the identity of `M`.** The
equation is recorded because the twisted morphisms below are defined at the functor spelling and
the compatibility square is stated at the other one.

Both sides are the sheafification of the objectwise tensor product of `a` with the identity of
`M`: the left one because `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.tensorRightModules`
is the second leg of `Stacks.SheafOfModules.Tensor.sheafTensor`, whose action on a morphism of
the first variable is `PresheafOfModules.tensorHom a.val (𝟙 M.val)` sheafified; the right one by
`Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map`. The two are *not* definitionally equal:
`CategoryTheory.Functor.uncurry` sends a pair to the composite of the two legs, and the second
leg at an identity is the identity only by `CategoryTheory.Functor.map_id`. -/
public theorem tensorRightModules_map (X : Scheme.{u}) {A A' : X.Modules} (M : X.Modules)
    (a : A ⟶ A') : (tensorRightModules X M).map a = tensorModulesMap X a (𝟙 M) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
    (R := ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩) a (𝟙 M)).symm

/-- **[Stacks, Tag 01CD] is natural in both module arguments.** The comparison of the inverse
image of a tensor product with the tensor product of the inverse images is a morphism of
bifunctors. -/
public theorem pullbackTensorModulesIso_naturality {X S : Scheme.{u}} (g : X ⟶ S)
    {A A' B B' : S.Modules} (a : A ⟶ A') (b : B ⟶ B') :
    (Scheme.Modules.pullback g).map (tensorModulesMap S a b) ≫
        (pullbackTensorModulesIso g A' B').hom =
      (pullbackTensorModulesIso g A B).hom ≫
        tensorModulesMap X ((Scheme.Modules.pullback g).map a)
          ((Scheme.Modules.pullback g).map b) :=
  (Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.naturality
    (((a, b) : ((A, B) : S.Modules × S.Modules) ⟶ (A', B')))

/-! ### Pasting three commuting squares -/

/-- Three commuting squares in a row paste to one commuting rectangle. This is stated for an
abstract category because in `X.Modules` a rewrite along `CategoryTheory.Category.assoc` does not
fire; see the implementation notes of this file. -/
public theorem comp_eq_of_three_squares {C : Type*} [Category C] {W X Y V R X' U' R'' : C}
    (a : W ⟶ X) (p' : X ⟶ Y) (c : Y ⟶ V) (q' : V ⟶ R)
    (p : W ⟶ X') (b : X' ⟶ Y) (c' : X' ⟶ U') (d : U' ⟶ V) (q : U' ⟶ R'') (z : R'' ⟶ R)
    (h₁ : a ≫ p' = p ≫ b) (h₂ : b ≫ c = c' ≫ d) (h₃ : d ≫ q' = q ≫ z) :
    a ≫ p' ≫ c ≫ q' = p ≫ c' ≫ q ≫ z := by
  rw [← Category.assoc, h₁, Category.assoc, ← Category.assoc b, h₂]
  simp only [Category.assoc, h₃]

/-! ### Inverting a morphism of coherent triples -/

/-- A commuting square whose two parallel edges are isomorphisms commutes with both of them
inverted. Stated for an abstract category so that the rewrites along
`CategoryTheory.Category.assoc` fire; in `X.Modules` they do not, for the reason recorded in the
implementation notes of this file. -/
public theorem inv_comp_eq_comp_inv {C : Type*} [Category C] {W X Y Z : C} (u : W ⟶ X) [IsIso u]
    (s : X ⟶ Z) (t : W ⟶ Y) (v : Y ⟶ Z) [IsIso v] (h : u ≫ s = t ≫ v) :
    inv u ≫ t = s ≫ inv v := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- **The inverse of a morphism of coherent triples both of whose members are isomorphisms.**

There is no `Iso` of coherent triples: an identification of two triples is a `Hom` whose two
members are isomorphisms, which is what
`Stacks.Algebraization.CoherentTriple.ShortExact.compIso` and
`Stacks.Algebraization.CoherentTriple.eulerCharacteristic_eq_of_hom` consume. This is the inverse
of such an identification, and together with
`Stacks.Algebraization.CoherentTriple.Hom.comp` it makes those identifications composable in
both directions. -/
public noncomputable def CoherentTriple.Hom.inverse {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} {T S : CoherentTriple A f} (φ : T.Hom S) [IsIso φ.onPunctured]
    [IsIso φ.onClosedFibre] : S.Hom T where
  onPunctured := inv φ.onPunctured
  onClosedFibre := inv φ.onClosedFibre
  compatible := by
    rw [CategoryTheory.Functor.map_inv, CategoryTheory.Functor.map_inv]
    exact inv_comp_eq_comp_inv _ _ _ _ φ.compatible

/-- The punctured-spectrum member of the inverse is the inverse of the punctured-spectrum
member. -/
public theorem CoherentTriple.Hom.inverse_onPunctured {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} {T S : CoherentTriple A f} (φ : T.Hom S) [IsIso φ.onPunctured]
    [IsIso φ.onClosedFibre] : φ.inverse.onPunctured = inv φ.onPunctured := rfl

/-- The closed-fibre member of the inverse is the inverse of the closed-fibre member. -/
public theorem CoherentTriple.Hom.inverse_onClosedFibre {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} {T S : CoherentTriple A f} (φ : T.Hom S) [IsIso φ.onPunctured]
    [IsIso φ.onClosedFibre] : φ.inverse.onClosedFibre = inv φ.onClosedFibre := rfl

/-- If `φ ≫ ψ = 0` then `(φ ≫ θ) ≫ inv θ ≫ ψ = 0`. -/
private theorem comp_comp_inv_comp_eq_zero {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y Z W : C} (φ : X ⟶ Y) (ψ : Y ⟶ Z) (θ : Y ⟶ W) [IsIso θ] (h : φ ≫ ψ = 0) :
    (φ ≫ θ) ≫ inv θ ≫ ψ = 0 := by
  simp [h]

/-- A short exact sequence stays short exact when its middle term is replaced along an
isomorphism `θ`: the injection is followed by `θ` and the surjection preceded by `inv θ`. -/
private theorem shortExact_comp_comp_inv_comp {C : Type*} [Category C] [Abelian C]
    {X Y Z W : C} (φ : X ⟶ Y) (ψ : Y ⟶ Z) (θ : Y ⟶ W) [IsIso θ] {w : φ ≫ ψ = 0}
    (h : (ShortComplex.mk φ ψ w).ShortExact) :
    (ShortComplex.mk (φ ≫ θ) (inv θ ≫ ψ) (comp_comp_inv_comp_eq_zero φ ψ θ w)).ShortExact := by
  refine ShortComplex.shortExact_of_iso ?_ h
  exact ShortComplex.isoMk (Iso.refl _) (asIso θ) (Iso.refl _) (by simp) (by simp)

/-- **A short exact sequence of coherent triples stays short exact when its middle term is
replaced by an isomorphic one.** The replacement is a morphism of coherent triples both of whose
members are isomorphisms; the new injection is the old one followed by it and the new surjection
is the old one preceded by its inverse.

Together with `Stacks.Algebraization.CoherentTriple.ShortExact.compIso` (third term) and
`Stacks.Algebraization.CoherentTriple.ShortExact.isoComp` (first term) this moves every term of a
short exact sequence of coherent triples along an identification. It is the one of the three that
needs `Stacks.Algebraization.CoherentTriple.Hom.inverse`, which is why it lives here rather than
beside the other two.

This is the transport the second clause of
`Stacks.Algebraization.HasHilbertInductionStep` consumes: twisting the degree-one sequence
`0 → T → T ⊗ L → G → 0` by `L^{⊗ n}` leaves the middle term as `(T ⊗ L) ⊗ L^{⊗ n}`, and the
clause asks for `T ⊗ L^{⊗ (n + 1)}`;
`Stacks.Algebraization.CoherentTriple.tensorInvertibleTwistZSuccDegreeOneHom` is the
identification between them. -/
public theorem CoherentTriple.ShortExact.midIso {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} {T S S' R : CoherentTriple A f} {φ : T.Hom S} {ψ : S.Hom R}
    (h : CoherentTriple.ShortExact φ ψ) (θ : S.Hom S') [IsIso θ.onPunctured]
    [IsIso θ.onClosedFibre] :
    CoherentTriple.ShortExact (φ.comp θ) (θ.inverse.comp ψ) where
  zero_punctured := comp_comp_inv_comp_eq_zero _ _ _ h.zero_punctured
  zero_closedFibre := comp_comp_inv_comp_eq_zero _ _ _ h.zero_closedFibre
  punctured := shortExact_comp_comp_inv_comp _ _ _ h.punctured
  closedFibre := shortExact_comp_comp_inv_comp _ _ _ h.closedFibre

/-! ### Isomorphism members under the operations on morphisms -/

/-- The punctured-spectrum member of a composite of morphisms of coherent triples whose members
are isomorphisms is an isomorphism. Stated as a lemma rather than left to instance search, which
does not see through `Stacks.Algebraization.CoherentTriple.Hom.comp` to the composite of the
members. -/
public theorem CoherentTriple.isIso_comp_onPunctured {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} {T S R : CoherentTriple A f} (φ : T.Hom S) (ψ : S.Hom R) [IsIso φ.onPunctured]
    [IsIso ψ.onPunctured] : IsIso (φ.comp ψ).onPunctured := by
  rw [CoherentTriple.Hom.comp_onPunctured]
  infer_instance

/-- The closed-fibre counterpart of
`Stacks.Algebraization.CoherentTriple.isIso_comp_onPunctured`. -/
public theorem CoherentTriple.isIso_comp_onClosedFibre {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} {T S R : CoherentTriple A f} (φ : T.Hom S) (ψ : S.Hom R) [IsIso φ.onClosedFibre]
    [IsIso ψ.onClosedFibre] : IsIso (φ.comp ψ).onClosedFibre := by
  rw [CoherentTriple.Hom.comp_onClosedFibre]
  infer_instance

/-- The punctured-spectrum member of the inverse of a morphism of coherent triples whose members
are isomorphisms is an isomorphism. -/
public theorem CoherentTriple.isIso_inverse_onPunctured {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} {T S : CoherentTriple A f} (φ : T.Hom S) [IsIso φ.onPunctured]
    [IsIso φ.onClosedFibre] : IsIso φ.inverse.onPunctured := by
  rw [CoherentTriple.Hom.inverse_onPunctured]
  infer_instance

/-- The closed-fibre counterpart of
`Stacks.Algebraization.CoherentTriple.isIso_inverse_onPunctured`. -/
public theorem CoherentTriple.isIso_inverse_onClosedFibre {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} {T S : CoherentTriple A f} (φ : T.Hom S) [IsIso φ.onPunctured]
    [IsIso φ.onClosedFibre] : IsIso φ.inverse.onClosedFibre := by
  rw [CoherentTriple.Hom.inverse_onClosedFibre]
  infer_instance

/-! ### The compatibility square of a twisted morphism -/

/-- **The compatibility square of a twisted morphism of coherent triples.** Tensoring a morphism
of coherent triples with the identity of a pair of modules identified over the punctured closed
fibre is compatible with the two twisted identifications. -/
public theorem compatible_tensorModule {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    {T S : CoherentTriple A f} (φ : T.Hom S)
    (M : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    (M₀ : (closedFibre A f).Modules)
    (μ : (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).obj M ≅
      (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj M₀) :
    (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map
          (tensorModulesMap (Stacks.Divisors.puncturedSpectrum A).toScheme
            φ.onPunctured (𝟙 M)) ≫
        (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A)) S.F M).hom ≫
          tensorModulesMap (puncturedClosedFibre A f).toScheme S.alpha.hom μ.hom ≫
          (pullbackTensorModulesIso (puncturedClosedFibre A f).ι S.F₀ M₀).inv =
      (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A)) T.F M).hom ≫
        tensorModulesMap (puncturedClosedFibre A f).toScheme T.alpha.hom μ.hom ≫
        (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀ M₀).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
            (tensorModulesMap (closedFibre A f) φ.onClosedFibre (𝟙 M₀)) := by
  have hnatk := pullbackTensorModulesIso_naturality (morphismRestrict (closedImmersion A f)
    (Stacks.Divisors.puncturedSpectrum A)) φ.onPunctured (𝟙 M)
  have hnatj := pullbackTensorModulesIso_naturality (puncturedClosedFibre A f).ι
    φ.onClosedFibre (𝟙 M₀)
  rw [CategoryTheory.Functor.map_id] at hnatk hnatj
  have key : tensorModulesMap (puncturedClosedFibre A f).toScheme
        ((Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).map φ.onPunctured) (𝟙 _) ≫
      tensorModulesMap (puncturedClosedFibre A f).toScheme S.alpha.hom μ.hom =
      tensorModulesMap (puncturedClosedFibre A f).toScheme T.alpha.hom μ.hom ≫
        tensorModulesMap (puncturedClosedFibre A f).toScheme
          ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map φ.onClosedFibre) (𝟙 _) := by
    rw [tensorModulesMap_comp, tensorModulesMap_comp, Category.id_comp, Category.comp_id,
      φ.compatible]
  have hnatj' : tensorModulesMap (puncturedClosedFibre A f).toScheme
        ((Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map φ.onClosedFibre) (𝟙 _) ≫
      (pullbackTensorModulesIso (puncturedClosedFibre A f).ι S.F₀ M₀).inv =
      (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀ M₀).inv ≫
        (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
          (tensorModulesMap (closedFibre A f) φ.onClosedFibre (𝟙 M₀)) :=
    (Iso.comp_inv_eq _).2
      ((((Category.assoc _ _ _).trans
        (congrArg (fun t => (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀ M₀).inv ≫ t)
          hnatj)).trans (Iso.inv_hom_id_assoc _ _)).symm)
  exact comp_eq_of_three_squares _ _ _ _ _ _ _ _ _ _ hnatk key hnatj'

/-- `Stacks.Algebraization.compatible_tensorModule` with its two outer morphisms written at the
functor spelling, which is the spelling the twisted morphisms below are *defined* at. The two
spellings are `Stacks.Algebraization.tensorRightModules_map` apart, and that equation is not
definitional, so the field cannot read the bifunctor statement off the functor one by
conversion. Both ends are moved by rewriting along that equation. -/
public theorem compatible_tensorRightModules {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    {T S : CoherentTriple A f} (φ : T.Hom S)
    (M : (Stacks.Divisors.puncturedSpectrum A).toScheme.Modules)
    (M₀ : (closedFibre A f).Modules)
    (μ : (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A))).obj M ≅
      (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).obj M₀) :
    (Scheme.Modules.pullback (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A))).map
          ((tensorRightModules (Stacks.Divisors.puncturedSpectrum A).toScheme M).map
            φ.onPunctured) ≫
        (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
            (Stacks.Divisors.puncturedSpectrum A)) S.F M).hom ≫
          tensorModulesMap (puncturedClosedFibre A f).toScheme S.alpha.hom μ.hom ≫
          (pullbackTensorModulesIso (puncturedClosedFibre A f).ι S.F₀ M₀).inv =
      (pullbackTensorModulesIso (morphismRestrict (closedImmersion A f)
          (Stacks.Divisors.puncturedSpectrum A)) T.F M).hom ≫
        tensorModulesMap (puncturedClosedFibre A f).toScheme T.alpha.hom μ.hom ≫
        (pullbackTensorModulesIso (puncturedClosedFibre A f).ι T.F₀ M₀).inv ≫
          (Scheme.Modules.pullback (puncturedClosedFibre A f).ι).map
            ((tensorRightModules (closedFibre A f) M₀).map φ.onClosedFibre) := by
  rw [tensorRightModules_map, tensorRightModules_map]
  exact compatible_tensorModule φ M M₀ μ

/-! ### Twisting a morphism of coherent triples -/

/-- **The tensor product of a morphism of coherent triples with an invertible coherent
triple.** -/
public noncomputable def CoherentTriple.Hom.tensorInvertible {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} {T S : CoherentTriple A f} (φ : T.Hom S) (L : CoherentTriple A f)
    (hL : IsInvertibleTriple L) :
    (T.tensorInvertible L hL).Hom (S.tensorInvertible L hL) where
  onPunctured := (tensorRightModules (Stacks.Divisors.puncturedSpectrum A).toScheme L.F).map
    φ.onPunctured
  onClosedFibre := (tensorRightModules (closedFibre A f) L.F₀).map φ.onClosedFibre
  compatible := compatible_tensorRightModules φ L.F L.F₀ L.alpha

/-- The punctured-spectrum member of the tensor product of a morphism of coherent triples with
an invertible coherent triple is the image of the member under tensoring on the right. -/
public theorem CoherentTriple.Hom.tensorInvertible_onPunctured {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} {T S : CoherentTriple A f} (φ : T.Hom S) (L : CoherentTriple A f)
    (hL : IsInvertibleTriple L) :
    (φ.tensorInvertible L hL).onPunctured =
      (tensorRightModules (Stacks.Divisors.puncturedSpectrum A).toScheme L.F).map
        φ.onPunctured := rfl

/-- The closed-fibre member of the tensor product of a morphism of coherent triples with an
invertible coherent triple is the image of the member under tensoring on the right. -/
public theorem CoherentTriple.Hom.tensorInvertible_onClosedFibre {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} {T S : CoherentTriple A f} (φ : T.Hom S) (L : CoherentTriple A f)
    (hL : IsInvertibleTriple L) :
    (φ.tensorInvertible L hL).onClosedFibre =
      (tensorRightModules (closedFibre A f) L.F₀).map φ.onClosedFibre := rfl

/-- The punctured-spectrum member of the tensor product of a morphism of coherent triples with
an invertible coherent triple is an isomorphism when the member of the morphism is: tensoring on
the right is a functor. -/
public theorem CoherentTriple.isIso_tensorInvertible_onPunctured {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} {T S : CoherentTriple A f} (φ : T.Hom S) [IsIso φ.onPunctured]
    (L : CoherentTriple A f) (hL : IsInvertibleTriple L) :
    IsIso (φ.tensorInvertible L hL).onPunctured :=
  ((tensorRightModules (Stacks.Divisors.puncturedSpectrum A).toScheme L.F).mapIso
    (asIso φ.onPunctured)).isIso_hom

/-- The closed-fibre counterpart of
`Stacks.Algebraization.CoherentTriple.isIso_tensorInvertible_onPunctured`. -/
public theorem CoherentTriple.isIso_tensorInvertible_onClosedFibre {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} {T S : CoherentTriple A f} (φ : T.Hom S) [IsIso φ.onClosedFibre]
    (L : CoherentTriple A f) (hL : IsInvertibleTriple L) :
    IsIso (φ.tensorInvertible L hL).onClosedFibre :=
  ((tensorRightModules (closedFibre A f) L.F₀).mapIso (asIso φ.onClosedFibre)).isIso_hom

/-- **The twist of a morphism of coherent triples by the `n`-th tensor power of an invertible
coherent triple**, for `n : ℤ`. -/
public noncomputable def CoherentTriple.Hom.twistZ {A : Type u} [CommRing A] [IsLocalRing A]
    {f : A} {T S : CoherentTriple A f} (φ : T.Hom S) (L : CoherentTriple A f)
    (hL : IsInvertibleTriple L) (n : ℤ) : (T.twistZ L hL n).Hom (S.twistZ L hL n) :=
  letI := hL.invertible_F
  letI := hL.invertible_F₀
  { onPunctured := (tensorRightModules (Stacks.Divisors.puncturedSpectrum A).toScheme
      (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n)).map φ.onPunctured
    onClosedFibre := (tensorRightModules (closedFibre A f)
      (tensorPowScheme (closedFibre A f) L.F₀ n)).map φ.onClosedFibre
    compatible := compatible_tensorRightModules φ _ _ (hL.alphaPow n) }

/-! ### Twisting a short exact sequence of coherent triples -/

/-- **The composite of two twisted morphisms of modules vanishes when the composite of the two
morphisms does.** -/
public theorem tensorRightModules_map_comp_eq_zero {X : Scheme.{u}} {A B C : X.Modules}
    (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M] {u : A ⟶ B} {v : B ⟶ C}
    (huv : u ≫ v = 0) :
    (tensorRightModules X M).map u ≫ (tensorRightModules X M).map v = 0 :=
  ((tensorRightModules X M).map_comp u v).symm.trans
    ((congrArg (tensorRightModules X M).map huv).trans
      (CategoryTheory.Functor.map_zero (tensorRightModules X M) A C))

/-- **A short exact sequence of coherent triples stays short exact after tensoring with an
invertible coherent triple.** Both component sequences are carried by tensoring on the right with
an invertible module, which is an equivalence of categories and hence preserves finite limits and
colimits. -/
public theorem CoherentTriple.ShortExact.tensorInvertible {A : Type u} [CommRing A]
    [IsLocalRing A] {f : A} {T S R : CoherentTriple A f} {φ : T.Hom S} {ψ : S.Hom R}
    (h : CoherentTriple.ShortExact φ ψ) (L : CoherentTriple A f) (hL : IsInvertibleTriple L) :
    CoherentTriple.ShortExact (φ.tensorInvertible L hL) (ψ.tensorInvertible L hL) :=
  have := hL.invertible_F
  have := hL.invertible_F₀
  { zero_punctured := tensorRightModules_map_comp_eq_zero L.F h.zero_punctured
    zero_closedFibre := tensorRightModules_map_comp_eq_zero L.F₀ h.zero_closedFibre
    punctured := h.punctured.map_of_exact
      (tensorRightModules (Stacks.Divisors.puncturedSpectrum A).toScheme L.F)
    closedFibre := h.closedFibre.map_of_exact
      (tensorRightModules (Stacks.Algebraization.closedFibre A f) L.F₀) }

/-- **A short exact sequence of coherent triples stays short exact after twisting by the `n`-th
tensor power of an invertible coherent triple**, for every integer `n`. Together with
`Stacks.Algebraization.CoherentTriple.Hom.twistZ` this makes the integer twists of a short exact
sequence of coherent triples a short exact sequence for every `n`, which is the input the
induction step of [Stacks, Tag 0F27] consumes. -/
public theorem CoherentTriple.ShortExact.twistZ {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    {T S R : CoherentTriple A f} {φ : T.Hom S} {ψ : S.Hom R}
    (h : CoherentTriple.ShortExact φ ψ) (L : CoherentTriple A f) (hL : IsInvertibleTriple L)
    (n : ℤ) : CoherentTriple.ShortExact (φ.twistZ L hL n) (ψ.twistZ L hL n) :=
  have := hL.invertible_F
  have := hL.invertible_F₀
  have := isInvertibleModule_tensorPowScheme
    (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n
  have := isInvertibleModule_tensorPowScheme (Stacks.Algebraization.closedFibre A f) L.F₀ n
  { zero_punctured := tensorRightModules_map_comp_eq_zero _ h.zero_punctured
    zero_closedFibre := tensorRightModules_map_comp_eq_zero _ h.zero_closedFibre
    punctured := h.punctured.map_of_exact
      (tensorRightModules (Stacks.Divisors.puncturedSpectrum A).toScheme
        (tensorPowScheme (Stacks.Divisors.puncturedSpectrum A).toScheme L.F n))
    closedFibre := h.closedFibre.map_of_exact
      (tensorRightModules (Stacks.Algebraization.closedFibre A f)
        (tensorPowScheme (Stacks.Algebraization.closedFibre A f) L.F₀ n)) }

end Stacks.Algebraization

end
