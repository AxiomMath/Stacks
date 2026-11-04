module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.Transition
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphism
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationMorphism
import StacksCore.Tactic.StacksAttribute

/-!
# Ringed augmentations of a simplicial site

Let `S` be a simplicial-site situation and `a₀` an augmentation of `S` towards a site `(D, K)`,
with total augmentation `a : Sh(C_total) ⟶ Sh(D)`. A *ringed* augmentation adds a sheaf of
commutative rings `O` on the total site, a sheaf of commutative rings `O_D` on `(D, K)` and a map
`a^♯ : O_D ⟶ a_*O`. These make `a : (Sh(C_total), O) ⟶ (Sh(D), O_D)` a morphism of ringed topoi,
and composing it with the component inclusions `g_n : (Sh(C_n), O_n) ⟶ (Sh(C_total), O)` gives
morphisms of ringed topoi `a_n = a ∘ g_n`. The simplicial transitions `f_φ` are morphisms of
ringed topoi for the structure-sheaf transitions `f_φ⁻¹O_m ⟶ O_n`, and `a_m ∘ f_φ = a_n`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation`: the data `O`, `O_D`, `a^♯`.
* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.augmentationRingedTopos`: the
  augmentation site with its structure sheaf.
* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.totalRingedHom`: the morphism of
  ringed topoi `a`.
* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.componentRingedHom`: the morphism
  of ringed topoi `a_n = a ∘ g_n`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.Augmentation.componentCompPushforwardIso`: the
  direct-image form of the identification `a ∘ g_n = a_n` of Stacks 0D70.
* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.transitionComponentPushforwardIso`:
  the identification `a_m ∘ f_φ = a_n` on direct images of sheaves of sets.

## Implementation notes

An equality of morphisms of topoi is a canonical isomorphism of direct-image functors, as
everywhere in this development: composites of adjunctions are not definitionally equal. In
inverse images the identification `a ∘ g_n = a_n` is
`CategoryTheory.SimplicialSiteSituation.Augmentation.totalMorphismOfTopoi_componentMorphism_iso`;
its direct-image form is obtained from uniqueness of right adjoints and so needs no coherence of
its own. The transition identification is then that comparison in degree `m`, the transition
comparison `Augmentation.transitionPushforwardIso` of Stacks 0D70, and the inverse of the
comparison in degree `n`.

The structure sheaf of the augmentation site is a field of the ringed augmentation rather than a
parameter, matching the source, where it is introduced together with `a^♯`. The two structure
sheaves on the simplicial side are the total one and its restrictions `O_n`, which are the
structure sheaves of `CategoryTheory.SimplicialSiteSituation.componentRingedTopos`, so nothing
further is chosen in degree `n`.

The structure map is stored in the direct-image form `a^♯ : O_D ⟶ a_*O` that the source states
and that `AlgebraicGeometry.RingedToposHom` takes as its data, so `totalRingedHom` stores it
unchanged.

## References

* [Stacks Project, Section 85.10 (Tag 0D9D)](https://stacks.math.columbia.edu/tag/0D9D)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 0D6Z](https://stacks.math.columbia.edu/tag/0D6Z)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

attribute [local implicit_reducible] AlgebraicGeometry.RingedToposHom.comp
  MorphismOfTopoi.comp

namespace CategoryTheory.SimplicialSiteSituation

namespace Augmentation

variable (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u}) (K : GrothendieckTopology D)
  (a : Augmentation S D K)

/-- **Stacks 0D70, compatibility (b), in direct images.** The direct image of the morphism of
topoi which Stacks 09WG attaches to the simplicial degree `n`, followed by the direct image of
the total augmentation, is the direct image of the augmentation of that degree.

The two functors are right adjoints of the two inverse images compared by
`totalMorphismOfTopoi_componentMorphism_iso`, so this is uniqueness of adjoints. -/
def componentCompPushforwardIso (n : SimplexCategory) :
    (componentMorphism S n).pushforward ⋙ (totalMorphismOfTopoi S D K a).pushforward ≅
      (componentAugmentation S D K a n).pushforward :=
  Adjunction.rightAdjointUniq
    ((totalMorphismOfTopoi S D K a).comp (componentMorphism S n)).adj
    ((componentAugmentation S D K a n).adj.ofNatIsoLeft
      (totalMorphismOfTopoi_componentMorphism_iso S D K a n).symm)

end Augmentation

/-- **Stacks 0D9D.** The data of a ringed augmentation of a simplicial site: a sheaf of
commutative rings `O` on the total site, a sheaf of commutative rings `O_D` on the augmentation
site, and a map `a^♯ : O_D ⟶ a_*O` into the direct image of `O` along the total augmentation. -/
@[stacks 0D9D "the data `O`, `O_D` and `a^♯` of a ringed augmentation"]
structure RingedAugmentation (S : SimplicialSiteSituation.{u}) (D : Cat.{u, u})
    (K : GrothendieckTopology D) (a : Augmentation S D K) where
  /-- The structure sheaf on the total site. -/
  O : Sheaf S.totalTopology CommRingCat.{u}
  /-- The structure sheaf on the augmentation site. -/
  OD : Sheaf K CommRingCat.{u}
  /-- The structure map `a^♯ : O_D ⟶ a_*O`. -/
  aSharp : OD ⟶ (pushforwardCommRingFunctor
    (Augmentation.totalMorphismOfTopoi S D K a)).obj O

namespace RingedAugmentation

variable {S : SimplicialSiteSituation.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  {a : Augmentation S D K} (A : RingedAugmentation S D K a)

/-- The augmentation site together with its structure sheaf, as a ringed topos. -/
def augmentationRingedTopos : RingedTopos.{u, u, u} where
  C := D
  J := K
  O := A.OD

/-- **Stacks 0D9D.** The morphism of ringed topoi
`a : (Sh(C_total), O) ⟶ (Sh(D), O_D)` determined by the total augmentation of Stacks 0D70 and
the structure map `a^♯`. -/
@[stacks 0D9D "the morphism of ringed topoi `a : (Sh(C_total), O) ⟶ (Sh(D), O_D)`"]
def totalRingedHom :
    RingedToposHom (S.totalRingedTopos A.O) A.augmentationRingedTopos where
  toToposHom := Augmentation.totalMorphismOfTopoi S D K a
  fSharp := A.aSharp

/-- The underlying morphism of topoi of `a` is the total augmentation of Stacks 0D70. -/
@[simp] theorem totalRingedHom_toToposHom :
    A.totalRingedHom.toToposHom = Augmentation.totalMorphismOfTopoi S D K a :=
  rfl

/-- **Stacks 0D9D.** The morphism of ringed topoi
`a_n = a ∘ g_n : (Sh(C_n), O_n) ⟶ (Sh(D), O_D)`, the composite of the component inclusion of
Stacks 0D72 with the ringed augmentation. -/
@[stacks 0D9D "the morphisms of ringed topoi `a_n = a ∘ g_n`"]
def componentRingedHom (n : SimplexCategory) :
    RingedToposHom (S.componentRingedTopos A.O n) A.augmentationRingedTopos :=
  RingedToposHom.comp (X := S.componentRingedTopos A.O n) (Y := S.totalRingedTopos A.O)
    (Z := A.augmentationRingedTopos) A.totalRingedHom (componentRingedToposHom S A.O n)

/-- The underlying morphism of topoi of `a_n` is the component morphism of Stacks 09WG followed
by the total augmentation. -/
@[simp] theorem componentRingedHom_toToposHom (n : SimplexCategory) :
    (A.componentRingedHom n).toToposHom =
      (Augmentation.totalMorphismOfTopoi S D K a).comp (componentMorphism S n) :=
  rfl

/-- The underlying morphism of topoi of `a_m ∘ f_φ` is the morphism of topoi of the simplicial
transition followed by that of `a_m`. -/
@[simp] theorem transitionCompRingedHom_toToposHom {m n : SimplexCategory} (φ : m ⟶ n) :
    ((A.componentRingedHom m).comp (S.transitionRingedToposHom A.O φ)).toToposHom =
      ((Augmentation.totalMorphismOfTopoi S D K a).comp
        (componentMorphism S m)).comp (S.transitionMorphism φ) :=
  rfl

/-- **Stacks 0D9D.** The identification `a_m ∘ f_φ = a_n` on direct images of sheaves of sets:
the direct image of the simplicial transition followed by that of `a_m` is the direct image of
`a_n`, for every simplex map `φ : m ⟶ n`. -/
@[stacks 0D9D "`a_m ∘ f_φ = a_n`, on direct images of sheaves of sets"]
def transitionComponentPushforwardIso {m n : SimplexCategory} (φ : m ⟶ n) :
    ((A.componentRingedHom m).comp (S.transitionRingedToposHom A.O φ)).toToposHom.pushforward ≅
      (A.componentRingedHom n).toToposHom.pushforward :=
  Functor.isoWhiskerLeft (S.transitionMorphism φ).pushforward
      (Augmentation.componentCompPushforwardIso S D K a m) ≪≫
    Augmentation.transitionPushforwardIso S D K a φ ≪≫
      (Augmentation.componentCompPushforwardIso S D K a n).symm

end RingedAugmentation

end CategoryTheory.SimplicialSiteSituation

end
