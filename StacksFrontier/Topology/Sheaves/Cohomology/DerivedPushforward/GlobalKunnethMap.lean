module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.KunnethMap
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections
public import StacksFrontier.Homology.Tor.DerivedTensor
public import Mathlib.AlgebraicGeometry.Pullbacks
import StacksCore.Tactic.StacksAttribute

/-!
# The global Künneth map

Let `a : X ⟶ S` and `b : Y ⟶ S` be two spaces over a base `S`, let `p : W ⟶ X` and `q : W ⟶ Y`
be two morphisms and let `f : W ⟶ S` be a morphism with `p ≫ a = f = q ≫ b`; the source takes
`W = X ×_S Y` with its two projections.  Set `A = Γ(S, 𝒪_S)`.  For `K ∈ D(𝒪_X)` and
`M ∈ D(𝒪_Y)` there is a canonical map

`RΓ(X, K) ⊗^𝐋_A RΓ(Y, M) ⟶ RΓ(W, Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M)`

in `D(A)`, Equation 36.23.0.2 of the Stacks project.  Following the source it is built from the
two pullback maps on derived global sections and the global cup product over `A` of Cohomology,
Section 0FKU.  Here it is assembled in the equivalent form the source itself uses when it
compares the two Künneth maps: the global cup product on the base, followed by `RΓ(S, -)` of the
*relative* Künneth map `Ra_*K ⊗^𝐋_{𝒪_S} Rb_*M ⟶ Rf_*(Lp^*K ⊗^𝐋 Lq^*M)` of Tag 0FLP, read
through the Leray isomorphism `RΓ(S, -) ∘ Rc_* ≅ RΓ(c⁻¹⊤, -)` of Tag 0D5W in each of the three
places where it occurs.  That the relative map induces the global one on applying `RΓ(S, -)` is
the source's own description of the relation between Tags 0FLP and 0G7V (Cohomology, Lemma
0FP6), and the two pullback maps on derived global sections are exactly the composites of the
adjunction unit with Leray that this assembly performs.

## Main definitions

* `Stacks.Cohomology.GlobalKunneth.baseRing` — the ring `A = Γ(S, 𝒪_S)`.
* `Stacks.Cohomology.GlobalKunneth.baseSections` — `RΓ(S, -) : D(𝒪_S) ⥤ D(A)`.
* `Stacks.Cohomology.GlobalKunneth.sectionsOverBase` — `RΓ(V, -) : D(𝒪_V) ⥤ D(A)` for a space
  `V` over `S`, namely derived sections over `c⁻¹ ⊤ = ⊤` with scalars restricted to `A`.
* `Stacks.Cohomology.GlobalKunneth.GlobalCupProduct` — the type of `A`-linear global cup products
  on the base, `RΓ(S, U) ⊗^𝐋_A RΓ(S, V) ⟶ RΓ(S, U ⊗^𝐋_{𝒪_S} V)`, as morphisms of bifunctors.
* `Stacks.Cohomology.GlobalKunneth.kunnethTrans` — the relative Künneth map of Tag 0FLP
  packaged as a natural transformation of bifunctors.
* `Stacks.Cohomology.GlobalKunneth.kunnethGlobalTrans` and
  `Stacks.Cohomology.GlobalKunneth.kunnethGlobalMap` — the global Künneth map built from a given
  global cup product, as a transformation of bifunctors and on objects.  At the global cup product
  of Section 0FKU it is
  `Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapCanonical`, the map of Tag 0G7V.
* `Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapScheme` — the same map for a cartesian
  square of schemes, at the fibre product `X ×_S Y` with its two canonical projections, which
  is the situation of the source.

## Main results

* `Stacks.Cohomology.GlobalKunneth.kunnethGlobalMap_eq` — the map is the four-step composite
  just described; it holds by `rfl` and is stated so that a consumer can see the construction.
* `Stacks.Cohomology.GlobalKunneth.kunnethGlobalMap_naturality`,
  `kunnethGlobalMap_naturality_left`, `kunnethGlobalMap_naturality_right` — the map is natural
  jointly and in each variable separately, for arbitrary derived modules.
* `Stacks.Cohomology.GlobalKunneth.isIso_kunnethGlobalMap` — if the cup product and the
  relative Künneth map are invertible, so is the global Künneth map.  This is the deduction the
  source makes in the first proof of Tag 0FLQ, and it is recorded here because it shows that the
  construction does not collapse: on invertible input it is invertible, hence in particular not
  the zero map.

## Implementation notes

*The four factors.*  Three of the four factors are the repository's own:

* the relative Künneth map of Tag 0FLP is
  `Stacks.Cohomology.DerivedKunneth.kunnethMap`, whose joint naturality
  `adjunctionBitensorMap_natural` is exactly the naturality field needed to package it as
  `kunnethTrans`;
* the Leray isomorphism of Tag 0D5W is
  `Stacks.Cohomology.DerivedSectionsLeray.lerayComparison`, invertible for every morphism by
  `Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison`;
* the derived tensor product on `D(A)` is the canonical one of Tag 064M,
  `CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor`, and the derived tensor
  products on `D(𝒪_S)` and `D(𝒪_W)` are the canonical ones of Tag 06YU.

The fourth factor, the `A`-linear global cup product on the base, is an argument
`GlobalCupProduct S` here.  The global cup product of Cohomology, Section 0FKU — the relative
cup product of Tag 0B68 for the morphism from `S` to the one-point space with ring `A`, read
through the identification of modules on that point with `A`-modules — is constructed in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMapCanonical` as
`Stacks.Cohomology.GlobalKunneth.globalCupProductCanonical`, and the map of Tag 0G7V is
`kunnethGlobalMap` at it, `Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapCanonical`.

*Why the cup product is a morphism of bifunctors and not a family of maps.*  Taking the cup
product as a natural transformation between the two bifunctors `D(𝒪_S) × D(𝒪_S) ⥤ D(A)` builds
its joint naturality into the datum, which is the whole of what the construction needs; the
naturality of the global Künneth map is then the naturality of a composite of natural
transformations and no separate axiom is required.  For the same reason `kunnethGlobalTrans` is
built first and `kunnethGlobalMap` is read off it.

*The base ring.*  `A` is `Γ(S, 𝒪_S)` for an arbitrary base, not only for `S = Spec A`, so the
construction has the generality of the source.  The left-hand tensor product is over `A` and
over nothing else: `baseSections` is `Stacks.Cohomology.DerivedSectionsLeray` derived sections
over `⊤ ⊆ S`, which lands in complexes of `Γ(S, 𝒪_S)`-modules, and `sectionsOverBase` is
derived sections over `c⁻¹ ⊤` with scalars restricted along `c^♯` to the *same* ring, so the
two factors of the source of the Künneth map are complexes of `A`-modules and the bifunctor
tensoring them is the derived tensor product over `A`.

*Derived and not ordinary pullback.*  The target is the derived tensor product of the two
*derived* pullbacks, as in the source: `p` and `q` enter only through
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback`.  The underived shadow of
this map is the separate Tag 0G49.

*Spaces rather than schemes.*  Like `Stacks.Cohomology.DerivedKunneth.kunnethMap`, which
carries Tag 0FLP in this repository, the statement is for morphisms of ringed spaces with the
two projections and the two factorizations of `f` taken as data.  The fibre product plays no
role in the construction, and a cartesian square of schemes is an instance of the data, so this
specializes to the source's situation; `kunnethGlobalMapScheme` is that specialization, stated
at the fibre product `X ×_S Y` of schemes with its two canonical projections.

## References

* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Tag 0FLP](https://stacks.math.columbia.edu/tag/0FLP)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Section 0FKU](https://stacks.math.columbia.edu/tag/0FKU)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 064M](https://stacks.math.columbia.edu/tag/064M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedProjectionFormula (uncurry_map_id_left uncurry_map_id_right)
open scoped CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.GlobalKunneth

attribute [local instance] HasDerivedCategory.standard

/-! ### Identities for an uncurried bifunctor -/

section Uncurry

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
  {C₃ : Type u₃} [Category.{v₃} C₃] (T : C₁ ⥤ C₂ ⥤ C₃)

/-- An uncurried bifunctor on a morphism whose second component is the image of an identity. -/
private lemma uncurry_map_map_id_right {D : Type*} [Category D] (F : D ⥤ C₂)
    {Z Z' : C₁} (u : Z ⟶ Z') (W : D) :
    (Functor.uncurry.obj T).map (u ×ₘ F.map (𝟙 W)) = (T.map u).app (F.obj W) := by
  rw [CategoryTheory.Functor.map_id]
  exact uncurry_map_id_right T u _

/-- An uncurried bifunctor on a morphism whose first component is the image of an identity. -/
private lemma uncurry_map_map_id_left {D : Type*} [Category D] (F : D ⥤ C₁) (Z : D)
    {W W' : C₂} (v : W ⟶ W') :
    (Functor.uncurry.obj T).map (F.map (𝟙 Z) ×ₘ v) = (T.obj (F.obj Z)).map v := by
  rw [CategoryTheory.Functor.map_id]
  exact uncurry_map_id_left T _ v

end Uncurry

/-! ### Derived global sections over the functions on the base -/

/-- **The base ring** `A = Γ(S, 𝒪_S)`, the global functions on the base space. -/
abbrev baseRing (S : RingedSpace.{u, u}) : CommRingCat.{u} :=
  S.presheaf.obj (op (⊤ : Opens S.carrier))

/-- **The derived tensor product over `A = Γ(S, 𝒪_S)`**, as a bifunctor on `D(A)`: the
canonical derived tensor product of complexes of `A`-modules of Tag 064M. -/
abbrev tensorBase (S : RingedSpace.{u, u}) :
    DerivedCategory (ModuleCat.{u} (baseRing S)) ⥤
      DerivedCategory (ModuleCat.{u} (baseRing S)) ⥤
        DerivedCategory (ModuleCat.{u} (baseRing S)) :=
  CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor (baseRing S)

/-- **`A`-linear derived global sections of the base**, `RΓ(S, -) : D(𝒪_S) ⥤ D(A)`. -/
abbrev baseSections (S : RingedSpace.{u, u}) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (ModuleCat.{u} (baseRing S)) :=
  derivedSectionsOverOpen S ⊤

/-- **`A`-linear derived global sections of a space over the base**, `RΓ(V, -) : D(𝒪_V) ⥤ D(A)`
for `c : V ⟶ S`: derived sections over `c⁻¹ ⊤ = ⊤`, regarded as complexes of
`A = Γ(S, 𝒪_S)`-modules by restriction of scalars along `c^♯`. -/
abbrev sectionsOverBase {S V : RingedSpace.{u, u}} (c : V ⟶ S) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing V)) ⥤
      DerivedCategory (ModuleCat.{u} (baseRing S)) :=
  derivedPreimageSections c ⊤

/-- The Leray isomorphism of Tag 0D5W in the form used below: `RΓ(S, Rc_*(-)) ≅ RΓ(V, -)` as
functors `D(𝒪_V) ⥤ D(A)`, for an arbitrary morphism `c : V ⟶ S` of ringed spaces. -/
abbrev lerayIso {S V : RingedSpace.{u, u}} (c : V ⟶ S) :
    derivedPushforward c ⋙ baseSections S ≅ sectionsOverBase c :=
  derivedSectionsPushforwardIso c ⊤

/-! ### Global cup products over the base -/

/-- **`A`-linear global cup products on the base.**  A morphism of bifunctors whose component at
`(U, V)` is a map

`RΓ(S, U) ⊗^𝐋_A RΓ(S, V) ⟶ RΓ(S, U ⊗^𝐋_{𝒪_S} V)`

of the shape of the global cup product of Cohomology, Section 0FKU, which is
`Stacks.Cohomology.GlobalKunneth.globalCupProductCanonical`.  Being a morphism of bifunctors, it
is jointly natural in `U` and `V`. -/
abbrev GlobalCupProduct (S : RingedSpace.{u, u}) :=
  (baseSections S).prod (baseSections S) ⋙ Functor.uncurry.obj (tensorBase S) ⟶
    Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf) ⋙ baseSections S

/-! ### The relative Künneth map as a transformation of bifunctors -/

section

variable {S X Y W : RingedSpace.{u, u}} (a : X ⟶ S) (b : Y ⟶ S) (p : W ⟶ X) (q : W ⟶ Y)
  (f : W ⟶ S) (hp : p ≫ a = f) (hq : q ≫ b = f)

/-- The relative Künneth map of Tag 0FLP, `Ra_*K ⊗^𝐋_{𝒪_S} Rb_*M ⟶ Rf_*(Lp^*K ⊗^𝐋 Lq^*M)`,
packaged as a natural transformation between the two bifunctors `D(𝒪_X) × D(𝒪_Y) ⥤ D(𝒪_S)` it
compares.  The naturality field is the joint naturality of the abstract Künneth map, which the
relative one is by definition. -/
def kunnethTrans :
    (derivedPushforward a).prod (derivedPushforward b) ⋙
        Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf) ⟶
      (derivedPullback p).prod (derivedPullback q) ⋙
        Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf) ⋙ derivedPushforward f where
  app KM := Stacks.Cohomology.DerivedKunneth.kunnethMap a b p q f hp hq KM.1 KM.2
  naturality _ _ km :=
    Stacks.Cohomology.DerivedKunneth.adjunctionBitensorMap_natural (derivedAdjunction f)
      (Functor.uncurry.obj (derivedTensorProductFunctor S.sheaf))
      (Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf))
      (Stacks.Cohomology.DerivedProjectionFormula.pullbackTensorComparison f)
      (Stacks.Cohomology.DerivedKunneth.pullbackCounitLeg a p f hp)
      (Stacks.Cohomology.DerivedKunneth.pullbackCounitLeg b q f hq) km.1 km.2

/-- On objects, `kunnethTrans` is the relative Künneth map of Tag 0FLP. -/
theorem kunnethTrans_app (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (kunnethTrans a b p q f hp hq).app (K, M) =
      Stacks.Cohomology.DerivedKunneth.kunnethMap a b p q f hp hq K M :=
  rfl

/-! ### The global Künneth map -/

/-- **The global Künneth map of Tag 0G7V, as a transformation of bifunctors.**  For a global cup
product `κ` on the base it is the composite of four canonical maps: the Leray isomorphism of
Tag 0D5W in each tensor factor, the cup product `κ`, derived global sections of the relative
Künneth map of Tag 0FLP, and the Leray isomorphism again on the target. -/
def kunnethGlobalTrans (κ : GlobalCupProduct S) :
    (sectionsOverBase a).prod (sectionsOverBase b) ⋙ Functor.uncurry.obj (tensorBase S) ⟶
      (derivedPullback p).prod (derivedPullback q) ⋙
        Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf) ⋙ sectionsOverBase f :=
  Functor.whiskerRight (NatTrans.prod (lerayIso a).inv (lerayIso b).inv)
      (Functor.uncurry.obj (tensorBase S)) ≫
    Functor.whiskerLeft ((derivedPushforward a).prod (derivedPushforward b)) κ ≫
    Functor.whiskerRight (kunnethTrans a b p q f hp hq) (baseSections S) ≫
    Functor.whiskerLeft ((derivedPullback p).prod (derivedPullback q) ⋙
      Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)) (lerayIso f).hom

/-- **The global Künneth map**

`RΓ(X, K) ⊗^𝐋_A RΓ(Y, M) ⟶ RΓ(W, Lp^*K ⊗^𝐋_{𝒪_W} Lq^*M)`

in `D(A)` for `A = Γ(S, 𝒪_S)`, where `p ≫ a = f = q ≫ b`; the source takes `W = X ×_S Y` with
its two projections.  It is defined for arbitrary `K ∈ D(𝒪_X)` and `M ∈ D(𝒪_Y)`, and is built
from the global cup product `κ` over `A` on the base together with the relative Künneth map of
Tag 0FLP and the Leray isomorphism of Tag 0D5W. -/
def kunnethGlobalMap (κ : GlobalCupProduct S)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    ((tensorBase S).obj ((sectionsOverBase a).obj K)).obj ((sectionsOverBase b).obj M) ⟶
      (sectionsOverBase f).obj
        (((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj K)).obj
          ((derivedPullback q).obj M)) :=
  (kunnethGlobalTrans a b p q f hp hq κ).app (K, M)

/-- The global Künneth map is the four-step composite of the Leray isomorphisms in the two
tensor factors, the global cup product on the base, derived global sections of the relative
Künneth map of Tag 0FLP, and the Leray isomorphism on the target. -/
theorem kunnethGlobalMap_eq (κ : GlobalCupProduct S)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    kunnethGlobalMap a b p q f hp hq κ K M =
      (Functor.uncurry.obj (tensorBase S)).map
            ((lerayIso a).inv.app K ×ₘ (lerayIso b).inv.app M) ≫
        κ.app ((derivedPushforward a).obj K, (derivedPushforward b).obj M) ≫
        (baseSections S).map
          (Stacks.Cohomology.DerivedKunneth.kunnethMap a b p q f hp hq K M) ≫
        (lerayIso f).hom.app
          (((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj K)).obj
            ((derivedPullback q).obj M)) :=
  rfl

/-- **The global Künneth map is natural in both variables jointly.** -/
theorem kunnethGlobalMap_naturality (κ : GlobalCupProduct S)
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {M M' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))} (k : K ⟶ K') (m : M ⟶ M') :
    (Functor.uncurry.obj (tensorBase S)).map
          ((sectionsOverBase a).map k ×ₘ (sectionsOverBase b).map m) ≫
        kunnethGlobalMap a b p q f hp hq κ K' M' =
      kunnethGlobalMap a b p q f hp hq κ K M ≫
        (sectionsOverBase f).map
          ((Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
            ((derivedPullback p).map k ×ₘ (derivedPullback q).map m)) :=
  (kunnethGlobalTrans a b p q f hp hq κ).naturality (X := (K, M)) (Y := (K', M')) (k, m)

/-- The global Künneth map is natural in the derived module on the first factor. -/
theorem kunnethGlobalMap_naturality_left (κ : GlobalCupProduct S)
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (k : K ⟶ K')
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    ((tensorBase S).map ((sectionsOverBase a).map k)).app ((sectionsOverBase b).obj M) ≫
        kunnethGlobalMap a b p q f hp hq κ K' M =
      kunnethGlobalMap a b p q f hp hq κ K M ≫
        (sectionsOverBase f).map
          (((derivedTensorProductFunctor W.sheaf).map ((derivedPullback p).map k)).app
            ((derivedPullback q).obj M)) := by
  have h := kunnethGlobalMap_naturality a b p q f hp hq κ k (𝟙 M)
  have h₂ : (sectionsOverBase f).map
        ((Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
          ((derivedPullback p).map k ×ₘ (derivedPullback q).map (𝟙 M))) =
      (sectionsOverBase f).map
        (((derivedTensorProductFunctor W.sheaf).map ((derivedPullback p).map k)).app
          ((derivedPullback q).obj M)) :=
    congrArg (fun g => (sectionsOverBase f).map g)
      (uncurry_map_map_id_right (derivedTensorProductFunctor W.sheaf) (derivedPullback q)
        ((derivedPullback p).map k) M)
  rw [uncurry_map_map_id_right, h₂] at h
  exact h

/-- The global Künneth map is natural in the derived module on the second factor. -/
theorem kunnethGlobalMap_naturality_right (κ : GlobalCupProduct S)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {M M' : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))} (m : M ⟶ M') :
    ((tensorBase S).obj ((sectionsOverBase a).obj K)).map ((sectionsOverBase b).map m) ≫
        kunnethGlobalMap a b p q f hp hq κ K M' =
      kunnethGlobalMap a b p q f hp hq κ K M ≫
        (sectionsOverBase f).map
          (((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj K)).map
            ((derivedPullback q).map m)) := by
  have h := kunnethGlobalMap_naturality a b p q f hp hq κ (𝟙 K) m
  have h₂ : (sectionsOverBase f).map
        ((Functor.uncurry.obj (derivedTensorProductFunctor W.sheaf)).map
          ((derivedPullback p).map (𝟙 K) ×ₘ (derivedPullback q).map m)) =
      (sectionsOverBase f).map
        (((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj K)).map
          ((derivedPullback q).map m)) :=
    congrArg (fun g => (sectionsOverBase f).map g)
      (uncurry_map_map_id_left (derivedTensorProductFunctor W.sheaf) (derivedPullback p) K
        ((derivedPullback q).map m))
  rw [uncurry_map_map_id_left, h₂] at h
  exact h

/-- **The construction does not collapse.**  If the global cup product on the base is invertible
at `(Ra_*K, Rb_*M)` and the relative Künneth map of Tag 0FLP is invertible at `(K, M)`, then the
global Künneth map is invertible; in particular it is not the zero map whenever its source is
nonzero.  This is the deduction the source makes in the first proof of Tag 0FLQ: the source and
target of the global map are the result of applying `RΓ(S, -)` to those of the relative one. -/
theorem isIso_kunnethGlobalMap (κ : GlobalCupProduct S)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (M : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)))
    (hκ : IsIso (κ.app ((derivedPushforward a).obj K, (derivedPushforward b).obj M)))
    (hK : IsIso (Stacks.Cohomology.DerivedKunneth.kunnethMap a b p q f hp hq K M)) :
    IsIso (kunnethGlobalMap a b p q f hp hq κ K M) := by
  rw [kunnethGlobalMap_eq]
  exact ((Functor.uncurry.obj (tensorBase S)).mapIso
      (Iso.prod (asIso ((lerayIso a).inv.app K)) (asIso ((lerayIso b).inv.app M))) ≪≫
      (@asIso _ _ _ _ (κ.app ((derivedPushforward a).obj K, (derivedPushforward b).obj M)) hκ ≪≫
        ((baseSections S).mapIso
            (@asIso _ _ _ _
              (Stacks.Cohomology.DerivedKunneth.kunnethMap a b p q f hp hq K M) hK) ≪≫
          (lerayIso f).app
            (((derivedTensorProductFunctor W.sheaf).obj ((derivedPullback p).obj K)).obj
              ((derivedPullback q).obj M))))).isIso_hom

end

/-! ### The global Künneth map for a cartesian square of schemes -/

section Schemes

variable {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)

/-- The fibre product of two schemes over a base is an instance of the data the construction
takes: read on the underlying ringed spaces, `pullback.condition` says that the second
projection followed by `b` is the structure morphism `p ≫ a` of `X ×_S Y`. -/
theorem toShHom_pullback_condition :
    (pullback.snd a b).toLRSHom.toShHom ≫ b.toLRSHom.toShHom =
      (pullback.fst a b ≫ a).toLRSHom.toShHom :=
  congrArg (fun g : pullback a b ⟶ S => g.toLRSHom.toShHom) pullback.condition.symm

/-- **The global Künneth map of Tag 0G7V at the fibre product of two schemes.**  For schemes
`a : X ⟶ S` and `b : Y ⟶ S` over a base and `A = Γ(S, 𝒪_S)`, the canonical map

`RΓ(X, K) ⊗^𝐋_A RΓ(Y, M) ⟶ RΓ(X ×_S Y, Lp^*K ⊗^𝐋_{𝒪_{X ×_S Y}} Lq^*M)`

in `D(A)`, where `p` and `q` are the two projections of `X ×_S Y`; it is
`kunnethGlobalMap` at the projections and the structure morphism `p ≫ a`.  The base scheme is
arbitrary and `K`, `M` are arbitrary; Tag 0FLQ says when this map is an isomorphism. -/
def kunnethGlobalMapScheme (κ : GlobalCupProduct S.toRingedSpace)
    (K : DerivedCategory X.Modules) (M : DerivedCategory Y.Modules) :
    ((tensorBase S.toRingedSpace).obj ((sectionsOverBase a.toLRSHom.toShHom).obj K)).obj
        ((sectionsOverBase b.toLRSHom.toShHom).obj M) ⟶
      (sectionsOverBase (pullback.fst a b ≫ a).toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor (pullback a b).toRingedSpace.sheaf).obj
            ((derivedPullback (pullback.fst a b).toLRSHom.toShHom).obj K)).obj
          ((derivedPullback (pullback.snd a b).toLRSHom.toShHom).obj M)) :=
  kunnethGlobalMap a.toLRSHom.toShHom b.toLRSHom.toShHom
    (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
    (pullback.fst a b ≫ a).toLRSHom.toShHom rfl (toShHom_pullback_condition a b) κ K M

/-- **The global Künneth map at the fibre product of two schemes is natural in both complexes.**
-/
theorem kunnethGlobalMapScheme_naturality (κ : GlobalCupProduct S.toRingedSpace)
    {K K' : DerivedCategory X.Modules} {M M' : DerivedCategory Y.Modules} (k : K ⟶ K')
    (m : M ⟶ M') :
    (Functor.uncurry.obj (tensorBase S.toRingedSpace)).map
          ((sectionsOverBase a.toLRSHom.toShHom).map k ×ₘ
            (sectionsOverBase b.toLRSHom.toShHom).map m) ≫
        kunnethGlobalMapScheme a b κ K' M' =
      kunnethGlobalMapScheme a b κ K M ≫
        (sectionsOverBase (pullback.fst a b ≫ a).toLRSHom.toShHom).map
          ((Functor.uncurry.obj
              (derivedTensorProductFunctor (pullback a b).toRingedSpace.sheaf)).map
            ((derivedPullback (pullback.fst a b).toLRSHom.toShHom).map k ×ₘ
              (derivedPullback (pullback.snd a b).toLRSHom.toShHom).map m)) :=
  kunnethGlobalMap_naturality a.toLRSHom.toShHom b.toLRSHom.toShHom
    (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
    (pullback.fst a b ≫ a).toLRSHom.toShHom rfl (toShHom_pullback_condition a b) κ k m

end Schemes

end Stacks.Cohomology.GlobalKunneth

end
