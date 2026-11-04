module

public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The inverse of an equivalence of ringed topoi

A morphism of topoi `f` whose direct image is an equivalence has an inverse: the same pair of
functors read the other way round, with the adjunction `f_* ⊣ f⁻¹` obtained from `f⁻¹ ⊣ f_*` by
uniqueness of adjoints.  If moreover `f` is a morphism of *ringed* topoi whose structure map
`f♯ : O_D ⟶ f_*O_C` is an isomorphism, then its inverse-image form `f⁻¹O_D ⟶ O_C` is an
isomorphism too, and its inverse is a structure map for the inverse morphism of topoi.  This
file constructs that inverse morphism of ringed topoi and identifies the structure map of the
round trip `Y ⟶ X ⟶ Y`.

The round trip is not the identity on the nose — there is no identity morphism of ringed topoi
in this development, and the composite's inverse image is only *isomorphic* to the identity
functor, through the unit of `f⁻¹ ⊣ f_*`.  What the last lemma below says is that under that
isomorphism the composite's structure map is the identity.  That is the input to a
transport-of-properties argument along an equivalence of ringed topoi: Stacks 03DM, that each of
the local conditions on a sheaf of modules of Stacks 03DL is intrinsic.

## Main definitions

* `MorphismOfTopoi.inverse`: the inverse of a morphism of topoi whose direct image is an
  equivalence.
* `AlgebraicGeometry.RingedToposHom.inverse`: the inverse of an equivalence of ringed topoi.

## Main results

* `AlgebraicGeometry.RingedToposHom.isIso_fSharpInverseImage`: the inverse-image form of the
  structure map of an equivalence of ringed topoi is an isomorphism.
* `AlgebraicGeometry.RingedToposHom.forgetRing_map_comp_inverse_fSharp`: the structure map of
  the round trip `Y ⟶ X ⟶ Y` is the unit of `f⁻¹ ⊣ f_*`.

## Implementation notes

The adjunction of the inverse morphism of topoi is `CategoryTheory.Adjunction.toEquivalence` of
`f⁻¹ ⊣ f_*`, read backwards.  That needs the unit and the counit as instances, which
`MorphismOfTopoi.isIso_adj_unit` and `MorphismOfTopoi.isIso_adj_counit` supply; they are
declared rather than produced by a `haveI` inside the definition so that the definition is a
structure literal whose projections reduce, which is what makes
`AlgebraicGeometry.RingedToposHom.inverse_fSharp` hold by `rfl`.

The structure-map lemma is proved on underlying sheaves of *sets*, which is the level at
which the two forms of the structure map are related: the equation
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget` holds there and nowhere else, and
`AlgebraicGeometry.RingedToposHom.comp_fSharp_forget` is likewise stated there.  Since
`AlgebraicGeometry.RingedTopos.forgetRing` reflects isomorphisms, no generality is lost.

## References

* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback

universe v u w v' u' w'

/-- The inverse image of a morphism of topoi whose direct image is an equivalence is itself an
equivalence, being its quasi-inverse. -/
@[sga "4 IV 3.4" "partial"]
instance MorphismOfTopoi.isEquivalence_inverseImage {E : Type u} [Category.{v} E] {F : Type u'}
    [Category.{v'} F] (f : MorphismOfTopoi E F) [f.pushforward.IsEquivalence] :
    f.inverseImage.IsEquivalence :=
  f.adj.isEquivalence_left_of_isEquivalence_right

/-- The unit of `f⁻¹ ⊣ f_*` is an isomorphism when the direct image is an equivalence. -/
instance MorphismOfTopoi.isIso_adj_unit {E : Type u} [Category.{v} E] {F : Type u'}
    [Category.{v'} F] (f : MorphismOfTopoi E F) [f.pushforward.IsEquivalence] :
    IsIso f.adj.unit :=
  f.adj.unit_isIso_of_L_fully_faithful

/-- The counit of `f⁻¹ ⊣ f_*` is an isomorphism when the direct image is an equivalence. -/
instance MorphismOfTopoi.isIso_adj_counit {E : Type u} [Category.{v} E] {F : Type u'}
    [Category.{v'} F] (f : MorphismOfTopoi E F) [f.pushforward.IsEquivalence] :
    IsIso f.adj.counit :=
  f.adj.counit_isIso_of_R_fully_faithful

/-- **The inverse of a morphism of topoi whose direct image is an equivalence.**  Its direct
image is `f⁻¹` and its inverse image is `f_*`, and its adjunction is the adjoint equivalence
`f⁻¹ ⊣ f_*` read backwards. -/
@[implicit_reducible]
def MorphismOfTopoi.inverse {E : Type u} [Category.{v} E] {F : Type u'} [Category.{v'} F]
    (f : MorphismOfTopoi E F) [f.pushforward.IsEquivalence] : MorphismOfTopoi F E where
  pushforward := f.inverseImage
  inverseImage := f.pushforward
  adj := f.adj.toEquivalence.symm.toAdjunction
  preservesFiniteLimits := inferInstance

/-- The direct image of `MorphismOfTopoi.inverse f` is the inverse image of `f`. -/
@[simp]
lemma MorphismOfTopoi.inverse_pushforward {E : Type u} [Category.{v} E] {F : Type u'}
    [Category.{v'} F] (f : MorphismOfTopoi E F) [f.pushforward.IsEquivalence] :
    f.inverse.pushforward = f.inverseImage := rfl

/-- The inverse image of `MorphismOfTopoi.inverse f` is the direct image of `f`. -/
@[simp]
lemma MorphismOfTopoi.inverse_inverseImage {E : Type u} [Category.{v} E] {F : Type u'}
    [Category.{v'} F] (f : MorphismOfTopoi E F) [f.pushforward.IsEquivalence] :
    f.inverse.inverseImage = f.pushforward := rfl

namespace AlgebraicGeometry.RingedToposHom

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- **The inverse-image form of the structure map of an equivalence of ringed topoi is an
isomorphism.**  On underlying sheaves of sets it is the direct image of `f♯` followed by the
counit of `f⁻¹ ⊣ f_*`, by
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget`; the first factor is an
isomorphism because `f♯` is, and the second because `f_*` is fully faithful. -/
instance isIso_fSharpInverseImage (f : RingedToposHom X Y)
    [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp] :
    IsIso f.fSharpInverseImage := by
  suffices IsIso (X.forgetRing.map f.fSharpInverseImage) from
    isIso_of_reflects_iso f.fSharpInverseImage X.forgetRing
  have h0 : IsIso (Y.forgetRing.map f.fSharp) := Functor.map_isIso Y.forgetRing f.fSharp
  have h1 : IsIso (f.toToposHom.inverseImage.map (Y.forgetRing.map f.fSharp)) :=
    Functor.map_isIso f.toToposHom.inverseImage (Y.forgetRing.map f.fSharp)
  have h2 : IsIso (f.toToposHom.adj.counit.app (X.forgetRing.obj X.O)) := inferInstance
  rw [fSharpInverseImage_forget]
  exact IsIso.comp_isIso' h1 h2

/-- **The inverse of an equivalence of ringed topoi.**  Its underlying morphism of topoi is
`MorphismOfTopoi.inverse`, and its structure map is the inverse of the inverse-image form
`f⁻¹O_D ⟶ O_C` of the structure map of `f`, which
`AlgebraicGeometry.RingedToposHom.isIso_fSharpInverseImage` exhibits as an isomorphism. -/
@[implicit_reducible]
def inverse (f : RingedToposHom X Y) [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp] :
    RingedToposHom Y X where
  toToposHom := f.toToposHom.inverse
  fSharp := inv f.fSharpInverseImage

/-- The structure map of `inverse f` is the inverse of the inverse-image form of the structure
map of `f`. -/
@[simp]
lemma inverse_fSharp (f : RingedToposHom X Y) [f.toToposHom.pushforward.IsEquivalence]
    [IsIso f.fSharp] : (inverse f).fSharp = inv f.fSharpInverseImage := rfl

/-- The underlying morphism of topoi of `inverse f` is `MorphismOfTopoi.inverse` of that of
`f`. -/
@[simp]
lemma inverse_toToposHom (f : RingedToposHom X Y) [f.toToposHom.pushforward.IsEquivalence]
    [IsIso f.fSharp] : (inverse f).toToposHom = f.toToposHom.inverse := rfl

/-- **The structure map of the round trip `Y ⟶ X ⟶ Y` is the unit of `f⁻¹ ⊣ f_*`** on
underlying sheaves of sets.  Since the inverse image of the round trip is the identity functor up
to that same unit, this is the statement that the round trip is the identity morphism of ringed
topoi up to canonical isomorphism, which is what makes a property of sheaves of modules
transported along `f` and back agree with the original.

The computation is the triangle identity: the inverse-image form of the structure map of `f` is
adjunct to its direct-image form (`fSharpInverseImage_forget_homEquiv`), so composing the unit
with its direct image returns `f♯`; the round trip's structure map is `f♯` composed with the
direct image of the *inverse* of that map, so the two direct images cancel. -/
lemma forgetRing_map_comp_inverse_fSharp (f : RingedToposHom X Y)
    [f.toToposHom.pushforward.IsEquivalence] [IsIso f.fSharp] :
    Y.forgetRing.map (f.comp (inverse f)).fSharp =
      f.toToposHom.adj.unit.app (Y.forgetRing.obj Y.O) := by
  have key : f.toToposHom.adj.unit.app (Y.forgetRing.obj Y.O) ≫
      f.toToposHom.pushforward.map (X.forgetRing.map f.fSharpInverseImage) =
      Y.forgetRing.map f.fSharp := by
    rw [fSharpInverseImage_forget_homEquiv]
    exact (f.toToposHom.adj.homEquiv_unit (Y.forgetRing.obj Y.O)
        (X.forgetRing.obj X.O) _).symm.trans
      ((f.toToposHom.adj.homEquiv (Y.forgetRing.obj Y.O)
        (X.forgetRing.obj X.O)).apply_symm_apply (Y.forgetRing.map f.fSharp))
  have hcancel : f.toToposHom.pushforward.map (X.forgetRing.map f.fSharpInverseImage) ≫
      f.toToposHom.pushforward.map (X.forgetRing.map (inv f.fSharpInverseImage)) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, IsIso.hom_inv_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rw [comp_fSharp_forget, inverse_fSharp, ← key]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k ↦ f.toToposHom.adj.unit.app (Y.forgetRing.obj Y.O) ≫ k) hcancel).trans
      (Category.comp_id _))

end AlgebraicGeometry.RingedToposHom

end

end
