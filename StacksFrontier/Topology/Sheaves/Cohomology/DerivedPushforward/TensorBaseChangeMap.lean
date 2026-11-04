module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProduct
import StacksCore.Tactic.StacksAttribute

/-!
# The base-change-and-cup-product map of an external tensor product

Let

```
            g'
    X' ----------→ X
    |              |
 f' |              | f
    v      g       v
    S' ----------→ S
```

be a commutative square of ringed spaces, let `G ∈ D(𝒪_{S'})` and let `F ∈ D(𝒪_X)`.  There is a
canonical morphism

`G ⊗^L_{𝒪_{S'}} Lg^*Rf_*F ⟶ Rf'_*(L(f')^*G ⊗^L_{𝒪_{X'}} L(g')^*F)`

in `D(𝒪_{S'})`: tensor the adjunction unit `G ⟶ Rf'_*L(f')^*G` of Stacks 079W with the derived
base change map `Lg^*Rf_*F ⟶ Rf'_*L(g')^*F` of Stacks 08HY, then apply the relative cup product
of Stacks 0B68 for `f'`.  It is the map [Stacks, Tag 0GN5] constructs from left to right.

## Main definitions

* `Stacks.Cohomology.DerivedTensorBaseChange.bitensorBaseChangeMap`: the construction over
  abstract categories, an adjunction, two bifunctors, a base change family and a cup product
  family.
* `Stacks.Cohomology.DerivedTensorBaseChange.tensorBaseChangeMap`: the morphism above, for a
  commutative square of ringed spaces.
* `Stacks.Cohomology.DerivedTensorBaseChange.schemeTensorBaseChangeMap`: the same morphism for
  the cartesian square of schemes of [Stacks, Tag 02KF].

## Main results

* `Stacks.Cohomology.DerivedTensorBaseChange.tensorBaseChangeMap_eq`: it is that composite.
* `Stacks.Cohomology.DerivedTensorBaseChange.tensorBaseChangeMap_naturality_left` and
  `..._naturality_right`: it is natural in `G` and in `F`, with
  `schemeTensorBaseChangeMap_naturality_left` and `..._naturality_right` the same for a
  cartesian square of schemes.

## Implementation notes

*Generality.*  The construction needs only commutativity of the square: no cartesian hypothesis,
no quasi-compactness or quasi-separatedness of `f`, no flatness of `G`, and no boundedness or
quasi-coherence of either argument.  [Stacks, Tag 0GN5] needs those hypotheses for its assertion
that the induced map on the `i`-th cohomology sheaf is invertible, not for the map itself.

*Where the map lands.*  The target is the derived tensor product `L(f')^*G ⊗^L L(g')^*F`, which
is where the source's chain of maps arrives before its last arrow to the underived tensor
product.  The identification of the source's `i`-th cohomology sheaf with
`G ⊗_{𝒪_{S'}} g^*R^if_*F` uses the mixed derived tensor product of [Stacks, Tag 08DE] in its
`𝒪_{S'}`-linear form, namely
`Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.spaceDerivedLinearMixedTensorIso` (and
`Stacks.Cohomology.MixedDerivedTensorOnARingedSpace.derivedLinearMixedTensorIso`).  What
remains between that identification and the cohomology sheaves is the flatness of `G` over
`g^{-1}𝒪_S` and the exactness of `g^{-1}`, which [Stacks, Tag 0GN5] assumes and this file does
not.

*Why the naturality is proved abstractly.*  The two bifunctors are indexed by the structure
sheaves of two ringed spaces, whose types are definitionally but not syntactically the ones the
derived tensor product of Stacks 06YU is indexed by, so a rewrite inside a geometric goal is not
type-correct.  Over abstract categories nothing of the kind arises, and the geometric statements
are instantiations.

*The four sheafification binders.*  `HasSheafify` and `WEqualsLocallyBijective` for
`AddCommGrpCat.{u}` on the sites of opens of `X'` and of `S'` are the binders the derived tensor
product of Stacks 06YU is stated under.  Both are `Prop`s and both are inhabited for every
ringed space, so they are not a weakening.

## References

* [Stacks Project, Tag 0GN5](https://stacks.math.columbia.edu/tag/0GN5)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange
open Stacks.Cohomology.DerivedRelativeCupProduct
open Stacks.DerivedTensor.RingedSite

namespace Stacks.Cohomology.DerivedTensorBaseChange

/-! ### The construction over abstract categories -/

section Abstract

variable {P P' Q Q' : Type*} [Category P] [Category P'] [Category Q] [Category Q']
  {Lf' : P' ⥤ Q'} {Rf' : Q' ⥤ P'} (adjf' : Lf' ⊣ Rf')
  {Rf : Q ⥤ P} {Lg : P ⥤ P'} {Lg' : Q ⥤ Q'}
  (AP' : P' ⥤ P' ⥤ P') (AQ' : Q' ⥤ Q' ⥤ Q')
  (bc : ∀ F : Q, Lg.obj (Rf.obj F) ⟶ Rf'.obj (Lg'.obj F))
  (cup : ∀ K M : Q', (AP'.obj (Rf'.obj K)).obj (Rf'.obj M) ⟶ Rf'.obj ((AQ'.obj K).obj M))

/-- The abstract base-change-and-cup-product map
`AP'(G, Lg(Rf F)) ⟶ Rf'(AQ'(Lf' G, Lg' F))`: the unit of `Lf' ⊣ Rf'` in the first argument of
`AP'`, the base change family in the second, and then the cup product family. -/
def bitensorBaseChangeMap (G : P') (F : Q) :
    (AP'.obj G).obj (Lg.obj (Rf.obj F)) ⟶
      Rf'.obj ((AQ'.obj (Lf'.obj G)).obj (Lg'.obj F)) :=
  (AP'.map (adjf'.unit.app G)).app (Lg.obj (Rf.obj F)) ≫
    (AP'.obj (Rf'.obj (Lf'.obj G))).map (bc F) ≫ cup (Lf'.obj G) (Lg'.obj F)

/-- The abstract map is natural in the first argument, given naturality of the cup product
family in its first argument. -/
lemma bitensorBaseChangeMap_naturality_left
    (hcupL : ∀ (K K' M : Q') (k : K ⟶ K'),
      (AP'.map (Rf'.map k)).app (Rf'.obj M) ≫ cup K' M =
        cup K M ≫ Rf'.map ((AQ'.map k).app M))
    {G G' : P'} (w : G ⟶ G') (F : Q) :
    (AP'.map w).app (Lg.obj (Rf.obj F)) ≫
        bitensorBaseChangeMap adjf' AP' AQ' bc cup G' F =
      bitensorBaseChangeMap adjf' AP' AQ' bc cup G F ≫
        Rf'.map ((AQ'.map (Lf'.map w)).app (Lg'.obj F)) := by
  have h1 := congr_arg (fun t => (AP'.map t).app (Lg.obj (Rf.obj F))) (adjf'.unit.naturality w)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.map_comp, NatTrans.comp_app] at h1
  have h2 := (AP'.map (Rf'.map (Lf'.map w))).naturality (bc F)
  have h3 := hcupL _ _ (Lg'.obj F) (Lf'.map w)
  unfold bitensorBaseChangeMap
  simp only [Category.assoc]
  rw [reassoc_of% h1, ← reassoc_of% h2, h3]

/-- The abstract map is natural in the second argument, given naturality of the base change
family and of the cup product family in its second argument. -/
lemma bitensorBaseChangeMap_naturality_right
    (hbc : ∀ (F F' : Q) (u : F ⟶ F'), Lg.map (Rf.map u) ≫ bc F' = bc F ≫ Rf'.map (Lg'.map u))
    (hcupR : ∀ (K M M' : Q') (m : M ⟶ M'),
      (AP'.obj (Rf'.obj K)).map (Rf'.map m) ≫ cup K M' =
        cup K M ≫ Rf'.map ((AQ'.obj K).map m))
    (G : P') {F F' : Q} (u : F ⟶ F') :
    (AP'.obj G).map (Lg.map (Rf.map u)) ≫
        bitensorBaseChangeMap adjf' AP' AQ' bc cup G F' =
      bitensorBaseChangeMap adjf' AP' AQ' bc cup G F ≫
        Rf'.map ((AQ'.obj (Lf'.obj G)).map (Lg'.map u)) := by
  have h1 := (AP'.map (adjf'.unit.app G)).naturality (Lg.map (Rf.map u))
  simp only [Functor.id_obj, Functor.comp_obj] at h1
  have h2 := congr_arg (AP'.obj (Rf'.obj (Lf'.obj G))).map (hbc _ _ u)
  simp only [Functor.map_comp] at h2
  have h3 := hcupR (Lf'.obj G) _ _ (Lg'.map u)
  unfold bitensorBaseChangeMap
  simp only [Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h2, h3]

end Abstract

/-! ### The construction for a commutative square of ringed spaces -/

universe u

attribute [local instance] HasDerivedCategory.standard

variable {X' X S' S : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)
  [HasSheafify (Opens.grothendieckTopology X'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology S'.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S'.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The left-to-right map of [Stacks, Tag 0GN5]** attached to a commutative square of ringed
spaces:

`G ⊗^L_{𝒪_{S'}} Lg^*Rf_*F ⟶ Rf'_*(L(f')^*G ⊗^L_{𝒪_{X'}} L(g')^*F)`.

It is the adjunction unit `G ⟶ Rf'_*L(f')^*G` of Stacks 079W in the first tensor factor and the
derived base change map of Stacks 08HY in the second, followed by the relative cup product of
Stacks 0B68 for `f'`. -/
@[stacks 0GN5 "the canonical map from left to right, in the derived category"]
def tensorBaseChangeMap (G : DerivedCategory (SheafOfModules.{u} (structureSheafRing S')))
    (F : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    ((derivedTensorProductFunctor S'.sheaf).obj G).obj
        ((derivedPullback g).obj ((derivedPushforward f).obj F)) ⟶
      (derivedPushforward f').obj
        (((derivedTensorProductFunctor X'.sheaf).obj ((derivedPullback f').obj G)).obj
          ((derivedPullback g').obj F)) :=
  bitensorBaseChangeMap (derivedAdjunction f')
    (derivedTensorProductFunctor S'.sheaf) (derivedTensorProductFunctor X'.sheaf)
    (fun F => derivedBaseChangeMap g' f' f g sq F) (fun K M => relativeCupProduct f' K M) G F

/-- The map of [Stacks, Tag 0GN5] is the unit of Stacks 079W tensored with the derived base
change map of Stacks 08HY, followed by the relative cup product of Stacks 0B68. -/
theorem tensorBaseChangeMap_eq (G : DerivedCategory (SheafOfModules.{u} (structureSheafRing S')))
    (F : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    tensorBaseChangeMap g' f' f g sq G F =
      ((derivedTensorProductFunctor S'.sheaf).map ((derivedAdjunction f').unit.app G)).app
          ((derivedPullback g).obj ((derivedPushforward f).obj F)) ≫
        ((derivedTensorProductFunctor S'.sheaf).obj
            ((derivedPushforward f').obj ((derivedPullback f').obj G))).map
          (derivedBaseChangeMap g' f' f g sq F) ≫
        relativeCupProduct f' ((derivedPullback f').obj G) ((derivedPullback g').obj F) :=
  rfl

/-- The map of [Stacks, Tag 0GN5] is natural in the derived module on the base `S'`. -/
@[stacks 0GN5 "naturality of the canonical map in the module on the base"]
theorem tensorBaseChangeMap_naturality_left
    {G G' : DerivedCategory (SheafOfModules.{u} (structureSheafRing S'))} (w : G ⟶ G')
    (F : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    ((derivedTensorProductFunctor S'.sheaf).map w).app
          ((derivedPullback g).obj ((derivedPushforward f).obj F)) ≫
        tensorBaseChangeMap g' f' f g sq G' F =
      tensorBaseChangeMap g' f' f g sq G F ≫
        (derivedPushforward f').map
          (((derivedTensorProductFunctor X'.sheaf).map ((derivedPullback f').map w)).app
            ((derivedPullback g').obj F)) :=
  bitensorBaseChangeMap_naturality_left (derivedAdjunction f')
    (derivedTensorProductFunctor S'.sheaf) (derivedTensorProductFunctor X'.sheaf)
    (fun F => derivedBaseChangeMap g' f' f g sq F) (fun K M => relativeCupProduct f' K M)
    (fun _ _ M k => relativeCupProduct_natural_left f' k M) w F

/-- The map of [Stacks, Tag 0GN5] is natural in the derived module on `X`. -/
@[stacks 0GN5 "naturality of the canonical map in the module upstairs"]
theorem tensorBaseChangeMap_naturality_right
    (G : DerivedCategory (SheafOfModules.{u} (structureSheafRing S')))
    {F F' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (u : F ⟶ F') :
    ((derivedTensorProductFunctor S'.sheaf).obj G).map
          ((derivedPullback g).map ((derivedPushforward f).map u)) ≫
        tensorBaseChangeMap g' f' f g sq G F' =
      tensorBaseChangeMap g' f' f g sq G F ≫
        (derivedPushforward f').map
          (((derivedTensorProductFunctor X'.sheaf).obj ((derivedPullback f').obj G)).map
            ((derivedPullback g').map u)) :=
  bitensorBaseChangeMap_naturality_right (derivedAdjunction f')
    (derivedTensorProductFunctor S'.sheaf) (derivedTensorProductFunctor X'.sheaf)
    (fun F => derivedBaseChangeMap g' f' f g sq F) (fun K M => relativeCupProduct f' K M)
    (fun _ _ u => derivedBaseChangeMap_naturality g' f' f g sq u)
    (fun K _ _ m => relativeCupProduct_natural_right f' K m) G u

/-! ### The construction for a cartesian square of schemes -/

section Schemes

variable {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S}
  [HasSheafify (Opens.grothendieckTopology X'.toRingedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X'.toRingedSpace.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}]
  [HasSheafify (Opens.grothendieckTopology S'.toRingedSpace.carrier) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology S'.toRingedSpace.carrier).WEqualsLocallyBijective
    AddCommGrpCat.{u}]

/-- **The left-to-right map of [Stacks, Tag 0GN5]** for the cartesian square of schemes of
[Stacks, Tag 02KF]:

`G ⊗^L_{𝒪_{S'}} Lg^*Rf_*F ⟶ Rf'_*(L(f')^*G ⊗^L_{𝒪_{X'}} L(g')^*F)`.

It is the map above at the underlying ringed spaces. -/
@[stacks 0GN5 "the canonical map from left to right, for a cartesian square of schemes"]
def schemeTensorBaseChangeMap (H : IsPullback g' f' f g) (G : DerivedCategory S'.Modules)
    (F : DerivedCategory X.Modules) :
    ((derivedTensorProductFunctor S'.toRingedSpace.sheaf).obj G).obj
        ((derivedPullback g.toLRSHom.toShHom).obj
          ((derivedPushforward f.toLRSHom.toShHom).obj F)) ⟶
      (derivedPushforward f'.toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor X'.toRingedSpace.sheaf).obj
            ((derivedPullback f'.toLRSHom.toShHom).obj G)).obj
          ((derivedPullback g'.toLRSHom.toShHom).obj F)) :=
  tensorBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
    g.toLRSHom.toShHom
    (by
      simpa only [Scheme.Hom.comp_toLRSHom, LocallyRingedSpace.comp_toShHom] using
        congrArg (fun k : X' ⟶ S => k.toLRSHom.toShHom) H.w)
    G F

/-- The map of [Stacks, Tag 0GN5] for a cartesian square of schemes is natural in the derived
module on the base `S'`. -/
@[stacks 0GN5 "naturality for a cartesian square of schemes, in the module on the base"]
theorem schemeTensorBaseChangeMap_naturality_left (H : IsPullback g' f' f g)
    {G G' : DerivedCategory S'.Modules} (w : G ⟶ G') (F : DerivedCategory X.Modules) :
    ((derivedTensorProductFunctor S'.toRingedSpace.sheaf).map w).app
          ((derivedPullback g.toLRSHom.toShHom).obj
            ((derivedPushforward f.toLRSHom.toShHom).obj F)) ≫
        schemeTensorBaseChangeMap H G' F =
      schemeTensorBaseChangeMap H G F ≫
        (derivedPushforward f'.toLRSHom.toShHom).map
          (((derivedTensorProductFunctor X'.toRingedSpace.sheaf).map
            ((derivedPullback f'.toLRSHom.toShHom).map w)).app
              ((derivedPullback g'.toLRSHom.toShHom).obj F)) :=
  tensorBaseChangeMap_naturality_left _ _ _ _ _ w F

/-- The map of [Stacks, Tag 0GN5] for a cartesian square of schemes is natural in the derived
module on `X`. -/
@[stacks 0GN5 "naturality for a cartesian square of schemes, in the module upstairs"]
theorem schemeTensorBaseChangeMap_naturality_right (H : IsPullback g' f' f g)
    (G : DerivedCategory S'.Modules) {F F' : DerivedCategory X.Modules} (u : F ⟶ F') :
    ((derivedTensorProductFunctor S'.toRingedSpace.sheaf).obj G).map
          ((derivedPullback g.toLRSHom.toShHom).map
            ((derivedPushforward f.toLRSHom.toShHom).map u)) ≫
        schemeTensorBaseChangeMap H G F' =
      schemeTensorBaseChangeMap H G F ≫
        (derivedPushforward f'.toLRSHom.toShHom).map
          (((derivedTensorProductFunctor X'.toRingedSpace.sheaf).obj
            ((derivedPullback f'.toLRSHom.toShHom).obj G)).map
              ((derivedPullback g'.toLRSHom.toShHom).map u)) :=
  tensorBaseChangeMap_naturality_right _ _ _ _ _ G u

end Schemes

end Stacks.Cohomology.DerivedTensorBaseChange

end
