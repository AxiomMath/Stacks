module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.RingedPoint
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedProjection
public import StacksFrontier.Cotangent.Resolution
import StacksCore.Tactic.StacksAttribute

/-!
# The site of polynomial algebras over a ring map and its diagram of ringed topoi

Let `A → B` be a map of commutative rings. The objects of the category considered here are the
`A`-algebra maps `α : P → B` with `P` a polynomial algebra over `A`, and its morphisms are the
`A`-algebra maps compatible with the augmentations; the site `C_{B/A}` is the *opposite* of that
category, carrying the chaotic topology, so that every presheaf on it is a sheaf.

On `C_{B/A}` there are two sheaves of rings: the tautological one `𝒪`, which sends `(P, α)` to
`P`, and the constant sheaf `B`, written with an underline in the source. The augmentations `α`
assemble into a map of sheaves of rings `𝒪 → B`, and the resulting diagram of ringed topoi is

```
(Sh(C_{B/A}), B) --i--> (Sh(C_{B/A}), 𝒪)
      |π
(Sh(*), B)
```

in which `i` is the identity on underlying topoi with `i♯` the augmentation, and `π` is the
projection to the ringed point of the chaotic site.

## Main definitions

* `CommAlgCat.PolynomialAugmentation`: the category of polynomial `A`-algebras augmented to `B`.
* `CommAlgCat.polynomialSite`: its opposite, the site `C_{B/A}`.
* `CommAlgCat.polynomialRingedPoint`: the ringed point of Tag 08PF through which `π` is formed.
* `CommAlgCat.polynomialStructureSheaf`: the tautological sheaf of rings `𝒪`.
* `CommAlgCat.polynomialConstantSheaf`: the constant sheaf of rings `B`.
* `CommAlgCat.polynomialAugmentation`: the map of sheaves of rings `𝒪 → B`.
* `CommAlgCat.polynomialStructureRingedTopos` and
  `CommAlgCat.polynomialConstantRingedTopos`: the ringed topoi `(Sh(C_{B/A}), 𝒪)` and
  `(Sh(C_{B/A}), B)`.
* `CommAlgCat.polynomialIdentityTopos`: the identity geometric morphism underlying `i`.
* `CommAlgCat.polynomialInclusion`: the morphism of ringed topoi `i`.
* `CommAlgCat.polynomialProjection`: the morphism of ringed topoi `π`.

## Main results

* `CommAlgCat.polynomialTopology_eq_bot`: the topology of `C_{B/A}` is the chaotic one, so all
  presheaves on it are sheaves.
* `CommAlgCat.polynomialConstantSheafIso`: the constant sheaf of rings really is the constant
  presheaf with value `B`.
* `CommAlgCat.polynomialAugmentation_app`: on sections over `(P, α)` the augmentation of sheaves
  is `α`.
* `CommAlgCat.polynomialInclusion_toToposHom`: `i` is the identity on underlying topoi.
* `CommAlgCat.polynomialConstantRingedTopos_eq_totalRingedTopos`: the source of `i` is the total
  ringed topos of Tag 08P8 for the ringed point of `C_{B/A}`, so `π` starts there too.

## Implementation notes

Objects of the site are a full subcategory of `Over B` in `CommAlgCat A`, cut out by the
predicate `CommAlgCat.IsPolynomialAlgebra` of Tag 08QI; `Over B` already encodes an algebra
together with an augmentation to `B`, and the full-subcategory morphisms are exactly the
`A`-algebra maps over `B`.

The ringed point and the morphism of ringed topoi `π` are not constructed here: the chaotic site
over its ringed point is Tag 08PF (`Stacks.ChaoticSite.RingedPointSituation`), whose
`fibredSituation` is an instance of the standing data of Tag 08P8, and `π` is that situation's
`ringedProjection`. In particular the constant sheaf `B` is `π⁻¹` of the ring on the point, which
is how Tag 08PF produces it, rather than a separately defined constant sheaf; that it *is* the
constant presheaf is `polynomialConstantSheafIso`, obtained from
`Stacks.Sheaves.ToposPullback.restrictionCommRingIso` — transporting the ring operations of a
sheaf along restriction of sheaves of sets is restriction of sheaves of rings.

Tag 08PF forms the morphism of topoi on sheaves valued in a universe containing the site, so the
ring on the point and the sections of both sheaves of rings live in `Type (u + 1)` when `A` and
`B` live in `Type u`; the universe lifts `CommAlgCat.uliftFunctor` and
`Stacks.ChaoticSite.RingedPointSituation.pointRingSheafLiftIso` move between the two.

`i` is recorded as an `AlgebraicGeometry.RingedToposHom`, the two-field form of Tag 01D3 in which
a morphism of ringed topoi is a geometric morphism together with `f♯` in direct-image form; `π`
is recorded in the four-field form `Stacks.Sheaves.RingedToposModules.RingedToposHom` because
that is the form in which Tag 08P8 produces it.

## References

* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A)

/-! ### The site -/

/-- The property of an `A`-algebra over `B` of being a polynomial algebra over `A`. -/
abbrev IsPolynomialAlgebraOver : ObjectProperty (Over B) :=
  fun P => IsPolynomialAlgebra A P.left

/-- The category whose objects are the `A`-algebra maps `α : P → B` with `P` a polynomial
algebra over `A`, and whose morphisms are the `A`-algebra maps compatible with the
augmentations. -/
abbrev PolynomialAugmentation := (IsPolynomialAlgebraOver A B).FullSubcategory

/-- **Stacks 08PR.** The site `C_{B/A}`: the opposite of the category of polynomial `A`-algebras
augmented to `B`. Its topology is the chaotic one, recorded through the ringed point below. -/
@[stacks 08PR "the site C_{B/A}"]
abbrev polynomialSite := (PolynomialAugmentation A B)ᵒᵖ

/-- The ringed point of Tag 08PF attached to the site `C_{B/A}` and the ring `B`: the data from
which the chaotic topology on `C_{B/A}`, the constant sheaf `B` and the projection `π` are
produced. -/
def polynomialRingedPoint : Stacks.ChaoticSite.RingedPointSituation.{u, u, u + 1} where
  C := polynomialSite A B
  B := CommRingCat.of (ULift.{u + 1} (B : Type u))

/-- The topology of the site `C_{B/A}`. -/
abbrev polynomialTopology : GrothendieckTopology (polynomialSite A B) :=
  (polynomialRingedPoint A B).fibredSituation.topology

/-- **Stacks 08PR.** The topology of `C_{B/A}` is the chaotic topology: its only coverings are
the maximal sieves, so every presheaf on `C_{B/A}` is a sheaf. -/
@[stacks 08PR "the chaotic topology on C_{B/A}"]
theorem polynomialTopology_eq_bot : polynomialTopology A B = ⊥ :=
  ((polynomialRingedPoint A B).topology_eq_trivial).trans GrothendieckTopology.trivial_eq_bot

/-- The functor from `C_{B/A}` to the point is continuous for the topology of `C_{B/A}` and the
trivial topology on the point. -/
instance polynomialStar_isContinuous :
    (Functor.star (polynomialSite A B)).IsContinuous (polynomialTopology A B)
      (GrothendieckTopology.trivial (Discrete PUnit.{u + 2})) :=
  (polynomialRingedPoint A B).fibredSituation.isContinuous

/-! ### The two sheaves of rings -/

/-- The tautological presheaf of rings on `C_{B/A}`, sending `(P, α)` to `P`, with its sections
lifted to the universe in which the morphism of topoi `π` is formed. -/
def polynomialStructurePresheaf : (polynomialSite A B)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  unopUnop (PolynomialAugmentation A B) ⋙ (IsPolynomialAlgebraOver A B).ι ⋙
    Over.forget B ⋙ CommAlgCat.uliftFunctor.{u + 1, u} A ⋙
      forget₂ (CommAlgCat.{u + 1} A) CommRingCat.{u + 1}

/-- **Stacks 08PR.** The tautological sheaf of rings `𝒪` on `C_{B/A}`, which sends the object
`(P, α)` to `P`. It is a sheaf because the topology of `C_{B/A}` is chaotic. -/
@[stacks 08PR "the structure sheaf 𝒪"]
def polynomialStructureSheaf : Sheaf (polynomialTopology A B) CommRingCat.{u + 1} :=
  ⟨polynomialStructurePresheaf A B, by
    rw [show polynomialTopology A B = ⊥ from polynomialTopology_eq_bot A B]
    exact Presheaf.isSheaf_bot _⟩

/-- **Stacks 08PR.** The constant sheaf of rings `B` on `C_{B/A}`, written with an underline in
the source. By Tag 08PF it is the inverse image along `π` of the ring on the point. -/
@[stacks 08PR "the constant sheaf B"]
def polynomialConstantSheaf : Sheaf (polynomialTopology A B) CommRingCat.{u + 1} :=
  (polynomialRingedPoint A B).constantRingSheaf

/-- The inverse image along `π` of the ring on the point is the restriction, along the unique
functor to the point, of that ring regarded as a sheaf of rings. -/
def polynomialConstantSheafRestrictionIso :
    polynomialConstantSheaf A B ≅
      ((Functor.star (polynomialSite A B)).sheafPushforwardContinuous CommRingCat.{u + 1}
          (polynomialTopology A B)
          (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))).obj
        (polynomialRingedPoint A B).fibredSituation.liftedBaseSheaf :=
  haveI := (polynomialRingedPoint A B).fibredSituation.isContinuous
  restrictionCommRingIso (polynomialTopology A B)
    (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))
    (Functor.star (polynomialSite A B))
    (polynomialRingedPoint A B).fibredSituation.liftedBaseSheaf

/-- The constant presheaf of rings with value `B`, with its sections in the universe in which
`π` is formed. -/
abbrev polynomialConstantPresheaf : (polynomialSite A B)ᵒᵖ ⥤ CommRingCat.{u + 1} :=
  (Functor.const (polynomialSite A B)ᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} (B : Type u)))

/-- **Stacks 08PR.** The constant sheaf of rings `B` of Tag 08PF is the constant presheaf with
value `B`. -/
@[stacks 08PR "the constant sheaf B is constant"]
def polynomialConstantSheafIso :
    (polynomialConstantSheaf A B).obj ≅ polynomialConstantPresheaf A B :=
  (sheafToPresheaf _ _).mapIso (polynomialConstantSheafRestrictionIso A B) ≪≫
    (sheafToPresheaf _ _).mapIso
      (((Functor.star (polynomialSite A B)).sheafPushforwardContinuous CommRingCat.{u + 1}
          (polynomialTopology A B)
          (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))).mapIso
        (polynomialRingedPoint A B).pointRingSheafLiftIso) ≪≫
    (Functor.sheafPushforwardContinuousCompSheafToPresheafIso
        (Functor.star (polynomialSite A B)) CommRingCat.{u + 1} (polynomialTopology A B)
        (GrothendieckTopology.trivial (Discrete PUnit.{u + 2}))).app
      (polynomialRingedPoint A B).pointRingSheaf ≪≫
    NatIso.ofComponents (fun _ => Iso.refl _) (by intro X Y f; ext x; rfl)

/-! ### The augmentation -/

/-- The augmentations `α : P → B`, as a map from the tautological presheaf of rings to the
constant presheaf with value `B`. -/
def polynomialAugmentationPresheaf :
    polynomialStructurePresheaf A B ⟶ polynomialConstantPresheaf A B where
  app X := (forget₂ (CommAlgCat.{u + 1} A) CommRingCat.{u + 1}).map
    ((CommAlgCat.uliftFunctor.{u + 1, u} A).map X.unop.unop.obj.hom)
  naturality := by
    intro X Y f
    have hw := congrArg (fun g =>
        (forget₂ (CommAlgCat.{u + 1} A) CommRingCat.{u + 1}).map
          ((CommAlgCat.uliftFunctor.{u + 1, u} A).map g)) f.unop.unop.hom.w
    exact CommRingCat.hom_ext (congrArg CommRingCat.Hom.hom hw)

/-- **Stacks 08PR.** The map of sheaves of rings `𝒪 → B` given by the augmentations. -/
@[stacks 08PR "the augmentation 𝒪 ⟶ B"]
def polynomialAugmentation :
    polynomialStructureSheaf A B ⟶ polynomialConstantSheaf A B :=
  (fullyFaithfulSheafToPresheaf (polynomialTopology A B) CommRingCat.{u + 1}).preimage
    (polynomialAugmentationPresheaf A B ≫ (polynomialConstantSheafIso A B).inv)

/-- **Stacks 08PR.** On sections over the object `(P, α)` of `C_{B/A}`, the augmentation of
sheaves of rings is `α`, read through the identification of the constant sheaf with the constant
presheaf. -/
@[stacks 08PR "the augmentation is given by α"]
theorem polynomialAugmentation_app (X : polynomialSite A B) :
    (polynomialAugmentation A B).hom.app (Opposite.op X) ≫
        (polynomialConstantSheafIso A B).hom.app (Opposite.op X) =
      (polynomialAugmentationPresheaf A B).app (Opposite.op X) := by
  have hmap :
      (sheafToPresheaf (polynomialTopology A B) CommRingCat.{u + 1}).map
          (polynomialAugmentation A B) =
        polynomialAugmentationPresheaf A B ≫ (polynomialConstantSheafIso A B).inv :=
    (fullyFaithfulSheafToPresheaf (polynomialTopology A B) CommRingCat.{u + 1}).map_preimage _
  have key : polynomialAugmentationPresheaf A B ≫
      (polynomialConstantSheafIso A B).inv ≫ (polynomialConstantSheafIso A B).hom =
        polynomialAugmentationPresheaf A B := by
    rw [Iso.inv_hom_id, Category.comp_id]
  have hcancel :
      (sheafToPresheaf (polynomialTopology A B) CommRingCat.{u + 1}).map
            (polynomialAugmentation A B) ≫ (polynomialConstantSheafIso A B).hom =
        polynomialAugmentationPresheaf A B := by
    rw [hmap]
    exact (Category.assoc _ _ _).trans key
  exact congrArg
    (fun f : polynomialStructurePresheaf A B ⟶ polynomialConstantPresheaf A B =>
      f.app (Opposite.op X)) hcancel

/-! ### The diagram of ringed topoi -/

/-- The ringed topos `(Sh(C_{B/A}), 𝒪)`. -/
def polynomialStructureRingedTopos : AlgebraicGeometry.RingedTopos.{u, u + 1, u + 1} where
  C := polynomialSite A B
  J := polynomialTopology A B
  O := polynomialStructureSheaf A B

/-- The ringed topos `(Sh(C_{B/A}), B)`, which Tag 08PF produces as the total ringed topos of
the chaotic site over its ringed point. -/
def polynomialConstantRingedTopos : AlgebraicGeometry.RingedTopos.{u, u + 1, u + 1} where
  C := polynomialSite A B
  J := polynomialTopology A B
  O := polynomialConstantSheaf A B

/-- The ringed topos `(Sh(C_{B/A}), B)` is the total ringed topos of Tag 08P8 for the ringed
point of `C_{B/A}`. -/
theorem polynomialConstantRingedTopos_eq_totalRingedTopos :
    polynomialConstantRingedTopos A B =
      (polynomialRingedPoint A B).fibredSituation.totalRingedTopos := rfl

/-- The identity geometric morphism of the topos of sheaves on `C_{B/A}`, which underlies `i`. -/
def polynomialIdentityTopos :
    MorphismOfTopoi (Sheaf (polynomialTopology A B) (Type (u + 1)))
      (Sheaf (polynomialTopology A B) (Type (u + 1))) where
  pushforward := 𝟭 _
  inverseImage := 𝟭 _
  adj := Adjunction.id
  preservesFiniteLimits := by infer_instance

/-- The direct image of the constant sheaf of rings along the identity geometric morphism. -/
def polynomialIdentityPushforward : Sheaf (polynomialTopology A B) CommRingCat.{u + 1} :=
  (pushforwardCommRingFunctor (polynomialIdentityTopos A B)).obj (polynomialConstantSheaf A B)

/-- Transporting the ring operations along the identity geometric morphism does nothing: the
direct image of the constant sheaf along `i` is the constant sheaf. -/
def polynomialIdentityPushforwardIso :
    polynomialIdentityPushforward A B ≅ polynomialConstantSheaf A B :=
  (pullbackCommRingSheafFunctorId.{u + 1, u, u + 1} (polynomialTopology A B)).app
    (polynomialConstantSheaf A B)

/-- **Stacks 08PR.** The morphism of ringed topoi `i : (Sh(C_{B/A}), B) ⟶ (Sh(C_{B/A}), 𝒪)`:
the identity on underlying topoi, with `i♯ : 𝒪 ⟶ i_*B` the augmentation. -/
@[stacks 08PR "the morphism i of ringed topoi"]
def polynomialInclusion :
    AlgebraicGeometry.RingedToposHom (polynomialConstantRingedTopos A B)
      (polynomialStructureRingedTopos A B) where
  toToposHom := polynomialIdentityTopos A B
  fSharp := polynomialAugmentation A B ≫ (polynomialIdentityPushforwardIso A B).inv

/-- **Stacks 08PR.** The geometric morphism underlying `i` is the identity. -/
@[stacks 08PR "i is the identity on topoi"]
theorem polynomialInclusion_toToposHom :
    (polynomialInclusion A B).toToposHom = polynomialIdentityTopos A B := rfl

/-- The inverse image of the identity geometric morphism is the identity functor. -/
theorem polynomialIdentityTopos_inverseImage :
    (polynomialIdentityTopos A B).inverseImage =
      𝟭 (Sheaf (polynomialTopology A B) (Type (u + 1))) := rfl

/-- The direct image of the identity geometric morphism is the identity functor. -/
theorem polynomialIdentityTopos_pushforward :
    (polynomialIdentityTopos A B).pushforward =
      𝟭 (Sheaf (polynomialTopology A B) (Type (u + 1))) := rfl

/-- **Stacks 08PR.** The morphism of ringed topoi `π : (Sh(C_{B/A}), B) ⟶ (Sh(*), B)`, the
projection of the chaotic site to its ringed point. -/
@[stacks 08PR "the morphism π of ringed topoi"]
abbrev polynomialProjection := (polynomialRingedPoint A B).fibredSituation.ringedProjection

end CommAlgCat

end
