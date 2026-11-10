module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.ExtensionByZeroFunctor

/-!
# Covariance of extension by zero in the open subscheme

Let `X ⊃ U ⊃ U'` be open subschemes of a Noetherian scheme `X`, let `j : U ⟶ X` and
`j' : U' ⟶ X` be the inclusions and let `i : U' ⟶ U` be the inclusion, so that `j' = j ∘ i` and
hence `j'^* = i^* ∘ j^*`. There is then a canonical map of pro-objects

`Rj'_!(K|_{U'}) ⟶ Rj_! K`

functorial for `K` in `D^b_{Coh}(𝒪_U)`. It is pinned down by the requirement that under the
identifications of Stacks 0G4N it induce the restriction map on morphisms into a constant
pro-object: for every `L` in `D^b_{Coh}(𝒪_X)` the composite

`Hom_{Pro}(Rj_! K, L) = Hom_U(K, L|_U) → Hom_{U'}(K|_{U'}, L|_{U'}) = Hom_{Pro}(Rj'_!(K|_{U'}), L)`

is functorial in `L`, and a transformation of the functors of points is exactly a morphism of
pro-objects in the other direction (Stacks 0G2X); functoriality in `K` comes from functoriality
of the displayed arrow in `K`.

This file carries out that construction at the level of generality of
`CategoryTheory.extensionByZero`, the functor `Rj_!` of Stacks 0G4N: for functors
`j^* : 𝒟 ⥤ 𝒞` and `j'^* : 𝒟 ⥤ 𝒞'`, a functor `i^* : 𝒞 ⥤ 𝒞'` and an identification
`e : j^* ⋙ i^* ≅ j'^*`, together with a `CategoryTheory.DeligneSystemAssignment` on each side.
For an open immersion of Noetherian schemes `𝒞 = D^b_{Coh}(𝒪_U)`, `𝒞' = D^b_{Coh}(𝒪_{U'})` and
`𝒟 = D^b_{Coh}(𝒪_X)`, and the assignments send an object to a Deligne system with that value.

## Main definitions

* `CategoryTheory.restrictionHomNatTrans`: the displayed arrow of the source, the restriction map
  `Hom_𝒞(K, j^* L) ⟶ Hom_{𝒞'}(i^* K, j'^* L)`, as a transformation of functors in `L`.
* `CategoryTheory.extensionByZeroCovariance`: the canonical map `Rj'_!(i^* K) ⟶ Rj_! K`, as a
  transformation `i^* ⋙ Rj'_! ⟶ Rj_!` of functors `𝒞 ⥤ Pro-𝒟`; its naturality is the
  functoriality in `K` claimed by the source.

## Main results

* `CategoryTheory.extensionByZeroCovariance_app_unop_hom_app`: the canonical map is the
  restriction map on functors of points.
* `CategoryTheory.extensionByZeroHomEquiv_covariance`: **the characterising property.** Under the
  adjointness bijections of Stacks 0G4N, composing with the canonical map is the restriction map
  `Hom_𝒞(K, j^* L) → Hom_{𝒞'}(i^* K, j'^* L)`. This is the display of the source.
* `CategoryTheory.extensionByZeroCovariance_app_eq`: **the canonical map is the only one with
  that property**, which is what the appeal to Stacks 0G2X in the source provides.

## Implementation notes

The category `Pro-𝒟` of `CategoryTheory.ProSeq` is the opposite of a full subcategory of
`𝒟 ⥤ Type v`, so a morphism of pro-objects *is* a transformation of the functors of points in
the opposite direction, and `CategoryTheory.Pro.homEquiv` (Stacks 0G2X) identifies that with a
morphism of pro-systems. The appeal to Stacks 0G2X in the source is therefore absorbed into the
construction of the pro-category, and the uniqueness statement
`CategoryTheory.extensionByZeroCovariance_app_eq` is proved from the co-Yoneda lemma: a
transformation out of `Hom_𝒞(K, j^* -)` is determined by its values, and every value is reached
by a morphism into a constant pro-object.

Nothing beyond the two `CategoryTheory.DeligneSystemAssignment`s is assumed. The assignments
themselves carry the identification of Stacks 0G2H, exactly as they do for Stacks 0G4N.

The second half of the source's remark, the explicit construction of the arrow by the inclusions
`(𝓘')^n 𝓕^• ⊆ 𝓘^n 𝓕^•`, is `AlgebraicGeometry.IdealPowerComplexSystem.compareHom`. It is not
compared here with the canonical map: identifying the two needs the restriction of each inclusion
`𝓘^n 𝓕^• ⟶ 𝓕^•` to `U'` to be an isomorphism, and a restriction functor
`D^b_{Coh}(𝒪_U) ⥤ D^b_{Coh}(𝒪_{U'})` on the bounded coherent derived categories.

## References

* [Stacks Project, Tag 0G4Y](https://stacks.math.columbia.edu/tag/0G4Y)
* [Stacks Project, Tag 0G4N](https://stacks.math.columbia.edu/tag/0G4N)
* [Stacks Project, Tag 0G2X](https://stacks.math.columbia.edu/tag/0G2X)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] CategoryTheory.uliftCategory

universe v u u' u''

namespace CategoryTheory

variable {𝒞 : Type u'} [Category.{v} 𝒞] {𝒞' : Type u''} [Category.{v} 𝒞']
  {𝒟 : Type u} [Category.{v} 𝒟]

variable (jstar : 𝒟 ⥤ 𝒞) (jstar' : 𝒟 ⥤ 𝒞') (istar : 𝒞 ⥤ 𝒞')
  (e : jstar ⋙ istar ≅ jstar')

include e

/-- The displayed arrow of [Stacks, Tag 0G4Y]: the restriction map

`Hom_U(K, L|_U) ⟶ Hom_{U'}(K|_{U'}, L|_{U'})`,

sending `α` to `i^* α` followed by the identification `e : j^* ⋙ i^* ≅ j'^*`, read as a
transformation of the functors `L ↦ Hom_𝒞(K, j^* L)` and `L ↦ Hom_{𝒞'}(i^* K, j'^* L)`. Its
naturality in `L` is the functoriality in `L` that the source uses to pin the canonical map
down. -/
@[stacks 0G4Y "the restriction map Hom_U(K, L|_U) → Hom_{U'}(K|_{U'}, L|_{U'}) of the display, \
as a transformation functorial in L"]
public def restrictionHomNatTrans (K : 𝒞) :
    jstar ⋙ coyoneda.obj (op K) ⟶ jstar' ⋙ coyoneda.obj (op (istar.obj K)) where
  app L := ↾fun (α : K ⟶ jstar.obj L) => istar.map α ≫ e.hom.app L
  naturality L L' ψ := by
    ext α
    change istar.map (α ≫ jstar.map ψ) ≫ e.hom.app L' =
      (istar.map α ≫ e.hom.app L) ≫ jstar'.map ψ
    rw [istar.map_comp, Category.assoc, Category.assoc, ← e.hom.naturality ψ]
    rfl

/-- The displayed arrow of [Stacks, Tag 0G4Y] is the restriction map: it sends
`α : K ⟶ j^* L` to `i^* α` followed by the identification of `i^* j^* L` with `j'^* L`. -/
public lemma restrictionHomNatTrans_app_apply (K : 𝒞) (L : 𝒟) (α : K ⟶ jstar.obj L) :
    (restrictionHomNatTrans jstar jstar' istar e K).app L α = istar.map α ≫ e.hom.app L :=
  rfl

/-- The displayed arrow of [Stacks, Tag 0G4Y] is functorial in `K`: precomposing with
`φ : K ⟶ K'` before restricting is restricting and then precomposing with `i^* φ`. -/
public lemma restrictionHomNatTrans_naturality {K K' : 𝒞} (φ : K ⟶ K') (L : 𝒟)
    (α : K' ⟶ jstar.obj L) :
    (restrictionHomNatTrans jstar jstar' istar e K).app L (φ ≫ α) =
      istar.map φ ≫ (restrictionHomNatTrans jstar jstar' istar e K').app L α := by
  change istar.map (φ ≫ α) ≫ e.hom.app L = istar.map φ ≫ istar.map α ≫ e.hom.app L
  rw [istar.map_comp, Category.assoc]

variable (A : DeligneSystemAssignment jstar) (A' : DeligneSystemAssignment jstar')

/-- **Stacks Project, Tag 0G4Y.** Let `X ⊃ U ⊃ U'` be open subschemes of a Noetherian scheme,
let `j : U ⟶ X`, `j' : U' ⟶ X` and `i : U' ⟶ U` be the inclusions. There is a canonical map

`Rj'_!(K|_{U'}) ⟶ Rj_! K`

in `Pro-D^b_{Coh}(𝒪_X)`, functorial for `K` in `D^b_{Coh}(𝒪_U)`. Here it is produced as a
transformation `i^* ⋙ Rj'_! ⟶ Rj_!` of functors `𝒞 ⥤ Pro-𝒟`, so that the functoriality in `K`
is its naturality.

A morphism of pro-objects is a transformation of their functors of points in the opposite
direction, which is the appeal to [Stacks, Tag 0G2X] in the source; the transformation used is
the restriction map `CategoryTheory.restrictionHomNatTrans`, whose naturality in `L` is the
functoriality in `L` of the display. -/
@[stacks 0G4Y "the canonical map Rj'_!(K|_{U'}) ⟶ Rj_! K, with the functoriality in K as its \
naturality; the Deligne-system assignments on both sides supplied as data"]
public def extensionByZeroCovariance :
    istar ⋙ extensionByZero jstar' A' ⟶ extensionByZero jstar A where
  app K := (ObjectProperty.homMk (restrictionHomNatTrans jstar jstar' istar e K)).op
  naturality K K' φ := Quiver.Hom.unop_inj <| ObjectProperty.hom_ext _ <| by
    ext L α
    exact (restrictionHomNatTrans_naturality jstar jstar' istar e φ L α).symm

/-- The canonical map of [Stacks, Tag 0G4Y] is the restriction map on functors of points: on
`α : K ⟶ j^* L` it is `i^* α` followed by the identification of `i^* j^* L` with `j'^* L`. -/
public lemma extensionByZeroCovariance_app_unop_hom_app (K : 𝒞) (L : 𝒟) (α : K ⟶ jstar.obj L) :
    ((extensionByZeroCovariance jstar jstar' istar e A A').app K).unop.hom.app L α =
      istar.map α ≫ e.hom.app L :=
  rfl

omit e in
/-- Composing a morphism `Rj_! K ⟶ L` into a constant pro-object with a morphism
`g : Rj'_!(i^* K) ⟶ Rj_! K` of pro-objects is, under the adjointness bijections of
[Stacks, Tag 0G4N], the map that `g` induces on functors of points. This is the co-Yoneda
lemma. -/
public lemma extensionByZeroHomEquiv_comp (K : 𝒞) (L : 𝒟)
    (g : (extensionByZero jstar' A').obj (istar.obj K) ⟶ (extensionByZero jstar A).obj K)
    (f : (extensionByZero jstar A).obj K ⟶ ProSeq.const.obj L) :
    extensionByZeroHomEquiv jstar' A' (istar.obj K) L (g ≫ f) =
      g.unop.hom.app L (extensionByZeroHomEquiv jstar A K L f) :=
  coyonedaEquiv_comp f.unop.hom g.unop.hom

/-- **The characterising property of the canonical map of [Stacks, Tag 0G4Y].** Under the
adjointness bijections of [Stacks, Tag 0G4N], composing a morphism `Rj_! K ⟶ L` with the
canonical map `Rj'_!(K|_{U'}) ⟶ Rj_! K` is the restriction map of the display:

`Hom_{Pro}(Rj_! K, L) = Hom_U(K, L|_U) → Hom_{U'}(K|_{U'}, L|_{U'}) = Hom_{Pro}(Rj'_!(K|_{U'}), L)`

This is the equality the source asks the canonical map to satisfy; by
`CategoryTheory.extensionByZeroCovariance_app_eq` it determines the map. -/
@[stacks 0G4Y "the display: composing with the canonical map is the restriction map \
Hom_U(K, L|_U) → Hom_{U'}(K|_{U'}, L|_{U'})"]
public lemma extensionByZeroHomEquiv_covariance (K : 𝒞) (L : 𝒟)
    (f : (extensionByZero jstar A).obj K ⟶ ProSeq.const.obj L) :
    extensionByZeroHomEquiv jstar' A' (istar.obj K) L
        ((extensionByZeroCovariance jstar jstar' istar e A A').app K ≫ f) =
      istar.map (extensionByZeroHomEquiv jstar A K L f) ≫ e.hom.app L :=
  extensionByZeroHomEquiv_comp jstar jstar' istar A A' K L _ f

/-- The pointwise form of `CategoryTheory.extensionByZeroCovariance_app_eq`: a morphism `g` of
pro-objects which induces the restriction map on morphisms into constant pro-objects acts on
functors of points as the restriction map does. -/
lemma extensionByZeroCovariance_unop_hom_app_of_homEquiv (K : 𝒞)
    (g : (extensionByZero jstar' A').obj (istar.obj K) ⟶ (extensionByZero jstar A).obj K)
    (hg : ∀ (L : 𝒟) (f : (extensionByZero jstar A).obj K ⟶ ProSeq.const.obj L),
      extensionByZeroHomEquiv jstar' A' (istar.obj K) L (g ≫ f) =
        istar.map (extensionByZeroHomEquiv jstar A K L f) ≫ e.hom.app L)
    (L : 𝒟) (α : K ⟶ jstar.obj L) :
    g.unop.hom.app L α = istar.map α ≫ e.hom.app L := by
  have h := hg L ((extensionByZeroHomEquiv jstar A K L).symm α)
  rwa [extensionByZeroHomEquiv_comp, Equiv.apply_symm_apply] at h

/-- **The canonical map of [Stacks, Tag 0G4Y] is the unique map with its characterising
property.** This is what the appeal to [Stacks, Tag 0G2X] in the source provides: a morphism of
pro-objects `Rj'_!(K|_{U'}) ⟶ Rj_! K` is determined by the induced map
`Hom_{Pro}(Rj_! K, L) → Hom_{Pro}(Rj'_!(K|_{U'}), L)`, functorially in `L`, so requiring that map
to be the restriction map of the display leaves exactly one choice. -/
@[stacks 0G4Y "the canonical map is the only one inducing the restriction map on morphisms into \
constant pro-objects, which is the appeal to Tag 0G2X"]
public lemma extensionByZeroCovariance_app_eq (K : 𝒞)
    (g : (extensionByZero jstar' A').obj (istar.obj K) ⟶ (extensionByZero jstar A).obj K)
    (hg : ∀ (L : 𝒟) (f : (extensionByZero jstar A).obj K ⟶ ProSeq.const.obj L),
      extensionByZeroHomEquiv jstar' A' (istar.obj K) L (g ≫ f) =
        istar.map (extensionByZeroHomEquiv jstar A K L f) ≫ e.hom.app L) :
    g = (extensionByZeroCovariance jstar jstar' istar e A A').app K :=
  Quiver.Hom.unop_inj <| ObjectProperty.hom_ext _ <| by
    ext L α
    exact extensionByZeroCovariance_unop_hom_app_of_homEquiv jstar jstar' istar e A A' K g hg L α

end CategoryTheory

end
