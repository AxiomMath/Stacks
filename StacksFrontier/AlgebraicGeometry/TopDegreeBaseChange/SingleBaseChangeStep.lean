module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SingleComparisonSquare
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeTensorNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMap
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The derived and the ordinary base-change mates agree at the structure sheaf

Let

```
      g'
  X' ---→ X
  |       |
f'|       |f
  v   g   v
  S' ---→ S
```

be a commutative square of ringed spaces.  The derived base-change map of [Stacks, Tag 08HY] for
the **transposed** square is the mate, under the derived adjunctions of `g` and `g'`, of the
comparison of the two iterated derived pullbacks; the ordinary comparison
`f^*(g_*𝒪_{S'}) ⟶ g'_*𝒪_{X'}` is the mate, under the ordinary adjunctions of `g` and `g'`, of
the identification `g'^*f^* ≅ f'^*g^*` of the two composite inverse images.  This file proves
that the first is the second, read through the single-complex comparisons of the two derived
functors — the compatibility of the two mates.

Everything is over ringed spaces and the ordinary comparison is carried as a parameter: the
invertibility inputs, and nothing else, belong to schemes, and they are supplied in
`StacksFrontier/AlgebraicGeometry/BaseChange/TorIndependence/BaseChangeUnitSingle.lean`.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedPullbackCompIsoLeft_eq` — the comparison
  of the two iterated derived pullbacks of [Stacks, Tag 08HY] is the composition isomorphism of
  [Stacks, Tag 0D5S] followed by the transport along the equality of the two composites, as an
  equality of isomorphisms.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle_congrLeft` and
  `...derivedToOrdinaryPullbackSingle_squareLeft` — the transport and the square compatibility of
  the single-complex pullback comparison, in the shape the adjoint characterization of the
  derived base-change map produces.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.iteratedComparison_naturality` — that comparison
  is natural.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.pullback_derivedCounit` and
  `...derivedCounit_single_naturality` — the derived counit at a single complex, along `g` and
  along `g'`.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedBaseChangeMap_singleUnit_eq_of` — **the
  compatibility of the two mates**.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.isIso_derivedBaseChangeMap_singleUnit_of` — the
  invertibility it yields, granted the five invertibility inputs.
* `Stacks.SingleComparison.mainChain`, `...transpose_three`, `...transpose_two`,
  `...map_comp_three`, `Stacks.AlgebraicGeometry.TopDegreeBaseChange.compChain` — the
  composition bookkeeping, with no geometry in it.

## Implementation notes

*Two rules the kernel imposes at this spelling.*  The `Category` instance of
`DerivedCategory (SheafOfModules (structureSheafRing _))` is built through definitions the module
system does not expose, so the elaborator leaves them folded and succeeds while the kernel
unfolds them and does not finish inside its deterministic limit.  Two consequences shape every
statement and proof here.

First, **no component of a composite of natural transformations is ever split**: the identity
`(α ≫ β).app Z = α.app Z ≫ β.app Z` is true by `rfl` and the kernel does not check it here, with
or without `CategoryTheory.NatTrans.comp_app`.  So the transport along the equality of the two
composites stays folded inside an isomorphism — that is why
`derivedToOrdinaryPullbackSingle_congrIso` exists beside
`derivedToOrdinaryPullbackSingle_congr`, and why `derivedPullbackCompIsoLeft_eq` is stated for
isomorphisms and consumed by `subst` rather than by `rw`.

Second, **one object is never spelled two ways**: `X.toRingedSpace` and the domain of
`X.toLRSHom.toShHom` are the same ringed space through two definitional unfoldings, and a kernel
defeq between two `Hom` types whose objects differ by those unfoldings does not terminate either.
That is why the whole identification runs over ringed-space variables and the scheme-level file
only instantiates it.

*The bookkeeping is over variables.*  `Stacks.SingleComparison.mainChain` and its companions
carry no geometry: the chain of rewrites they perform exceeds the heartbeat limit in `isDefEq`
when run against the concrete goal, and costs nothing over variables.  This is the remedy the
implementation notes of
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/TopDegreePullbackIdentity.lean` record for the
same wall.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)
open Stacks.Cohomology.DerivedBaseChange (derivedPullbackCompIsoLeft)

universe u

namespace Stacks.SingleComparison

/-- **The bookkeeping of the identification, with no geometry in it.**  Six equations chain the
six-fold composite on the left into the four-fold composite on the right.

Over variables because at the `SheafOfModules (structureSheafRing _)` spelling the unification of
these rewrites against the goal exceeds the heartbeat limit in `isDefEq`. -/
theorem mainChain {C : Type*} [Category C]
    {P Q Bq₁ Bq Dq R E Bp V N B₁ B₂ S₄ T₁ T₂ : C}
    (p : P ⟶ Q) (a1 : Q ⟶ Bq₁) (a2 : Bq₁ ⟶ Bq) (a3 : Bq ⟶ Dq) (nu1 : Dq ⟶ R) (nu2 : R ⟶ E)
    (aa : P ⟶ Bp) (u : Bp ⟶ Bq) (v : Bp ⟶ V) (s1 : V ⟶ Dq) (n1 : V ⟶ N) (s2 : N ⟶ R)
    (b1 : P ⟶ B₁) (b2 : B₁ ⟶ B₂) (s3 : B₂ ⟶ N) (s4 : B₂ ⟶ S₄) (s5' : S₄ ⟶ E)
    (t1 : B₁ ⟶ T₁) (t2 : T₁ ⟶ T₂) (s5 : T₂ ⟶ E)
    (h1 : p ≫ a1 ≫ a2 = aa ≫ u)
    (h2 : u ≫ a3 = v ≫ s1)
    (h3 : s1 ≫ nu1 = n1 ≫ s2)
    (h4 : aa ≫ v ≫ n1 = b1 ≫ b2 ≫ s3)
    (h5 : s3 ≫ s2 ≫ nu2 = s4 ≫ s5')
    (h6 : t1 ≫ t2 ≫ s5 = b2 ≫ s4 ≫ s5') :
    p ≫ (a1 ≫ a2 ≫ a3) ≫ nu1 ≫ nu2 = b1 ≫ t1 ≫ t2 ≫ s5 := by
  simp only [Category.assoc]
  rw [reassoc_of% h1, reassoc_of% h2, reassoc_of% h3, reassoc_of% h4, h5, ← h6]

/-- The transpose of a three-fold composite whose last factor is in the image of the right
adjoint. -/
theorem transpose_three {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {A B : C} {Y Z : D} (x : A ⟶ B) (y : B ⟶ R.obj Y) (z : Y ⟶ Z)
    {t : L.obj B ⟶ Y} (hy : (adj.homEquiv B Y).symm y = t) :
    (adj.homEquiv A Z).symm (x ≫ y ≫ R.map z) = L.map x ≫ t ≫ z := by
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_right_symm, hy]

/-- The transpose of a three-fold composite, pulling the first two factors out. -/
theorem transpose_two {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {A B B' : C} {Z : D} (x : A ⟶ B) (y : B ⟶ B') (w : B' ⟶ R.obj Z)
    {t : L.obj B' ⟶ Z} (hw : (adj.homEquiv B' Z).symm w = t) :
    (adj.homEquiv A Z).symm (x ≫ y ≫ w) = L.map x ≫ L.map y ≫ t := by
  rw [Adjunction.homEquiv_naturality_left_symm, Adjunction.homEquiv_naturality_left_symm, hw]

/-- A functor distributes over a three-fold composite. -/
theorem map_comp_three {C D : Type*} [Category C] [Category D] (F : C ⥤ D) {A B B' B'' : C}
    (a : A ⟶ B) (b : B ⟶ B') (c : B' ⟶ B'') :
    F.map (a ≫ b ≫ c) = F.map a ≫ F.map b ≫ F.map c := by
  rw [F.map_comp, F.map_comp]

end Stacks.SingleComparison

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

open _root_.DerivedCategory

variable {X' X S' S : RingedSpace.{u, u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)

attribute [local instance] HasDerivedCategory.standard
attribute [-instance] Stacks.SheafOfModules.coefficientSheafification
  Stacks.SheafOfModules.coefficientLocallyBijective
  Stacks.Cohomology.SiteModules.moduleSheavesAbelian

/-- **The two readings of the comparison of the two iterated derived pullbacks agree.**
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft` is the composition isomorphism
of [Stacks, Tag 0D5S] followed by the transport along the equality of the two composites. True by
definition, and recorded as an equality of *isomorphisms* so that no consumer has to split the
component of a composite of natural transformations, which the kernel does not check within its
limit at this spelling. -/
theorem derivedPullbackCompIsoLeft_eq (w : g' ≫ f = f' ≫ g) :
    derivedPullbackCompIsoLeft f' g' g f w.symm =
      derivedPullbackCompIsoCanonical g' f ≪≫
        eqToIso (congrArg (fun k : X' ⟶ S => derivedPullback k) w) := rfl

/-- Composition bookkeeping for the naturality of a two-factor comparison. -/
theorem compChain {C : Type*} [Category C] {P Q R T U V : C}
    (p : P ⟶ Q) (d1' : Q ⟶ R) (ci' : R ⟶ T) (d1 : P ⟶ U) (mid : U ⟶ R) (ci : U ⟶ V) (u : V ⟶ T)
    (hn1 : p ≫ d1' = d1 ≫ mid) (hn2 : mid ≫ ci' = ci ≫ u) :
    p ≫ d1' ≫ ci' = (d1 ≫ ci) ≫ u := by
  rw [← Category.assoc, hn1, Category.assoc, hn2, Category.assoc]

/-- **The single-complex comparison transported along the square's equality of composites**,
with the transport read through
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft`.

`derivedToOrdinaryPullbackSingle_congrIso` after rewriting the isomorphism, which is
`derivedPullbackCompIsoLeft_eq`: the rewrite happens at the level of isomorphisms, so no
component of a composite of natural transformations is split. -/
theorem derivedToOrdinaryPullbackSingle_congrLeft (w : g' ≫ f = f' ≫ g)
    (M : SheafOfModules.{u} (structureSheafRing S)) (d : ℤ) :
    (derivedPullbackCompIsoLeft f' g' g f w.symm).hom.app
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing S)) d).obj M) ≫
        derivedToOrdinaryPullbackSingle (f' ≫ g) M d =
      (derivedPullbackCompIsoCanonical g' f).hom.app
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing S)) d).obj M) ≫
        derivedToOrdinaryPullbackSingle (g' ≫ f) M d ≫
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X')) d).map
            ((eqToHom (congrArg (fun k : X' ⟶ S => modulePullback k) w)).app M) :=
  derivedToOrdinaryPullbackSingle_congrOf w (derivedPullbackCompIsoCanonical g' f)
    (derivedPullbackCompIsoLeft f' g' g f w.symm) (derivedPullbackCompIsoLeft_eq g' f' f g w) M d

/-- **The single-complex pullback comparison around the square**, with the comparison of the two
iterated derived pullbacks written as the adjoint characterization of the derived base-change map
writes it.  This is `derivedToOrdinaryPullbackSingle_square` in that shape; its proof repeats the
bookkeeping with `derivedToOrdinaryPullbackSingle_congrLeft` in place of
`derivedToOrdinaryPullbackSingle_congr`. -/
theorem derivedToOrdinaryPullbackSingle_squareLeft (w : g' ≫ f = f' ≫ g)
    (M : SheafOfModules.{u} (structureSheafRing S)) (d : ℤ) :
    ((derivedPullbackCompIsoLeft f' g' g f w.symm).hom.app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing S)) d).obj M) ≫
          (derivedPullbackCompIsoCanonical f' g).inv.app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing S)) d).obj M)) ≫
        (derivedPullback f').map (derivedToOrdinaryPullbackSingle g M d) ≫
        derivedToOrdinaryPullbackSingle f' ((modulePullback g).obj M) d =
      (derivedPullback g').map (derivedToOrdinaryPullbackSingle f M d) ≫
        derivedToOrdinaryPullbackSingle g' ((modulePullback f).obj M) d ≫
        (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X')) d).map
          ((modulePullbackSquareIso g' f' f g w).hom.app M) := by
  have hs : (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing X')) d).map
        ((modulePullbackSquareIso g' f' f g w).hom.app M) =
      (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X')) d).map
          ((Stacks.DerivedPullback.Composition.modulePullbackComp g' f).hom.app M) ≫
        (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X')) d).map
            ((eqToHom (congrArg (fun k : X' ⟶ S => modulePullback k) w)).app M) ≫
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X')) d).map
            ((Stacks.DerivedPullback.Composition.modulePullbackComp f' g).inv.app M) := by
    simp only [modulePullbackSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      eqToIso.hom, Functor.map_comp]
  have hsa : (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X')) d).map
          ((Stacks.DerivedPullback.Composition.modulePullbackComp g' f).inv.app M) ≫
        (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X')) d).map
          ((Stacks.DerivedPullback.Composition.modulePullbackComp g' f).hom.app M) = 𝟙 _ := by
    rw [← (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing X')) d).map_comp,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  exact Stacks.SingleComparison.squareChainIso _ _ _ _ _ _ _ _ _ _ _ _ _
    (derivedToOrdinaryPullbackSingle_comp f' g d M)
    (derivedToOrdinaryPullbackSingle_comp g' f d M)
    (derivedToOrdinaryPullbackSingle_congrLeft g' f' f g w M d)
    hs ((derivedPullbackCompIsoCanonical f' g).inv_hom_id_app _) hsa

/-- The hypothesis `h1` of `Stacks.SingleComparison.mainChain`: the naturality of the comparison
of the two iterated derived pullbacks, in the shape the adjoint characterization of the derived
base-change map produces.  Each of the two factors is natural; the composite naturality is
`compChain`. -/
theorem iteratedComparison_naturality (w : g' ≫ f = f' ≫ g)
    {Z Z' : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))} (φ : Z ⟶ Z') :
    (derivedPullback g').map ((derivedPullback f).map φ) ≫
        (derivedPullbackCompIsoLeft f' g' g f w.symm).hom.app Z' ≫
          (derivedPullbackCompIsoCanonical f' g).inv.app Z' =
      ((derivedPullbackCompIsoLeft f' g' g f w.symm).hom.app Z ≫
          (derivedPullbackCompIsoCanonical f' g).inv.app Z) ≫
        (derivedPullback f').map ((derivedPullback g).map φ) :=
  compChain _ _ _ _ _ _ _
    ((derivedPullbackCompIsoLeft f' g' g f w.symm).hom.naturality φ)
    ((derivedPullbackCompIsoCanonical f' g).inv.naturality φ)

/-- The hypothesis `h2` of `Stacks.SingleComparison.mainChain`: the derived counit at a single
complex, pulled back along `f'`. -/
theorem pullback_derivedCounit (M : SheafOfModules.{u} (structureSheafRing S')) :
    (derivedPullback f').map
          ((derivedPullback g).map (singlePushforwardComparison g M 0)) ≫
        (derivedPullback f').map
          ((derivedAdjunction g).counit.app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing S')) 0).obj M)) =
      (derivedPullback f').map
          (derivedToOrdinaryPullbackSingle g ((modulePushforward g).obj M) 0) ≫
        (derivedPullback f').map
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing S')) 0).map
            ((modulePullbackPushforwardAdjunction g).counit.app M)) := by
  rw [← (derivedPullback f').map_comp, ← (derivedPullback f').map_comp]
  exact congrArg (derivedPullback f').map
    (derivedCounit_singlePushforwardComparison g 0 M)

/-- The hypothesis `h6` of `Stacks.SingleComparison.mainChain`: the derived counit at a single
complex along `g'`, preceded by the derived pullback of a map into a direct image. -/
theorem derivedCounit_single_naturality
    {B : SheafOfModules.{u} (structureSheafRing X)}
    (N : SheafOfModules.{u} (structureSheafRing X'))
    (ψ : B ⟶ (modulePushforward g').obj N) :
    (derivedPullback g').map
          ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X)) 0).map ψ) ≫
        (derivedPullback g').map (singlePushforwardComparison g' N 0) ≫
          (derivedAdjunction g').counit.app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X')) 0).obj N) =
      derivedToOrdinaryPullbackSingle g' B 0 ≫
        (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing X')) 0).map
            ((modulePullback g').map ψ) ≫
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (structureSheafRing X')) 0).map
            ((modulePullbackPushforwardAdjunction g').counit.app N) := by
  rw [derivedCounit_singlePushforwardComparison, ← Category.assoc,
    Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle_naturality
      g' ψ 0, Category.assoc]

/-! ### The identification of the two mates, over ringed spaces -/

/-- **The derived base-change map of the transposed square at the structure sheaf in degree zero
is the ordinary comparison**, over ringed spaces, with the ordinary comparison `psi`, the
identification `nu : f'^*𝒪_{S'} ⟶ 𝒪_{X'}` and the ordinary identity `h5` carried as parameters.

This is the compatibility of the two mates.  Its six inputs are: the naturality of the comparison
of the two iterated derived pullbacks (`iteratedComparison_naturality`), the derived counit at a
single complex along `g` and along `g'`
(`Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedCounit_singlePushforwardComparison`, used
through `pullback_derivedCounit` and `derivedCounit_single_naturality`), the naturality of
`derivedToOrdinaryPullbackSingle` along `f'`, the single-complex pullback comparison around the
square (`derivedToOrdinaryPullbackSingle_squareLeft`) and `h5`. -/
@[sga "4 XVII 4.2.13" "special case"]
theorem derivedBaseChangeMap_singleUnit_eq_of (w : g' ≫ f = f' ≫ g)
    (psi : (modulePullback f).obj
          ((modulePushforward g).obj (SheafOfModules.unit (structureSheafRing S'))) ⟶
        (modulePushforward g').obj (SheafOfModules.unit (structureSheafRing X')))
    (nu : (modulePullback f').obj (SheafOfModules.unit (structureSheafRing S')) ⟶
      SheafOfModules.unit (structureSheafRing X'))
    (h5 : (modulePullbackSquareIso g' f' f g w).hom.app
            ((modulePushforward g).obj (SheafOfModules.unit (structureSheafRing S'))) ≫
          (modulePullback f').map
              ((modulePullbackPushforwardAdjunction g).counit.app
                (SheafOfModules.unit (structureSheafRing S'))) ≫
            nu =
        (modulePullback g').map psi ≫
          (modulePullbackPushforwardAdjunction g').counit.app
            (SheafOfModules.unit (structureSheafRing X'))) :
    (derivedPullback f).map
          (singlePushforwardComparison g (SheafOfModules.unit (structureSheafRing S')) 0) ≫
        Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap f' g' g f w.symm
            ((singleFunctor _ 0).obj (SheafOfModules.unit (structureSheafRing S'))) ≫
          (derivedPushforward g').map
            (derivedToOrdinaryPullbackSingle f'
                (SheafOfModules.unit (structureSheafRing S')) 0 ≫
              (singleFunctor _ 0).map nu) =
      derivedToOrdinaryPullbackSingle f
          ((modulePushforward g).obj (SheafOfModules.unit (structureSheafRing S'))) 0 ≫
        (singleFunctor _ 0).map psi ≫
          singlePushforwardComparison g' (SheafOfModules.unit (structureSheafRing X')) 0 := by
  have h5' := ((Stacks.SingleComparison.map_comp_three
        (singleFunctor (SheafOfModules.{u} (structureSheafRing X')) 0) _ _ _).symm.trans
      (congrArg (singleFunctor (SheafOfModules.{u} (structureSheafRing X')) 0).map h5)).trans
    ((singleFunctor (SheafOfModules.{u} (structureSheafRing X')) 0).map_comp _ _)
  refine ((derivedAdjunction g').homEquiv _ _).symm.injective ?_
  exact (Stacks.SingleComparison.transpose_three (derivedAdjunction g') _ _ _
      (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_adjoint f' g' g f w.symm
        ((singleFunctor _ 0).obj (SheafOfModules.unit (structureSheafRing S'))))).trans
    ((Stacks.SingleComparison.mainChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (iteratedComparison_naturality g' f' f g w
          (singlePushforwardComparison g (SheafOfModules.unit (structureSheafRing S')) 0))
        (pullback_derivedCounit f' g (SheafOfModules.unit (structureSheafRing S')))
        (derivedToOrdinaryPullbackSingle_naturality f'
          ((modulePullbackPushforwardAdjunction g).counit.app
            (SheafOfModules.unit (structureSheafRing S'))) 0)
        (derivedToOrdinaryPullbackSingle_squareLeft g' f' f g w
          ((modulePushforward g).obj (SheafOfModules.unit (structureSheafRing S'))) 0)
        h5'
        (derivedCounit_single_naturality g'
          (SheafOfModules.unit (structureSheafRing X')) psi)).trans
      (Stacks.SingleComparison.transpose_two (derivedAdjunction g') _ _ _
        (Adjunction.homEquiv_counit (derivedAdjunction g') _ _
          (singlePushforwardComparison g'
            (SheafOfModules.unit (structureSheafRing X')) 0))).symm)

/-- **The derived base-change map of the transposed square is invertible at the structure sheaf
in degree zero**, over ringed spaces and granted the five invertibility inputs.

`derivedBaseChangeMap_singleUnit_eq_of` identifies the map, read through the three single-complex
comparisons, with the ordinary comparison `psi`; the right-hand side of that identification is a
composite of three invertible maps, and the two factors flanking the base-change map on the left
are invertible too. -/
theorem isIso_derivedBaseChangeMap_singleUnit_of (w : g' ≫ f = f' ≫ g)
    (psi : (modulePullback f).obj
          ((modulePushforward g).obj (SheafOfModules.unit (structureSheafRing S'))) ⟶
        (modulePushforward g').obj (SheafOfModules.unit (structureSheafRing X')))
    (nu : (modulePullback f').obj (SheafOfModules.unit (structureSheafRing S')) ⟶
      SheafOfModules.unit (structureSheafRing X'))
    (h5 : (modulePullbackSquareIso g' f' f g w).hom.app
            ((modulePushforward g).obj (SheafOfModules.unit (structureSheafRing S'))) ≫
          (modulePullback f').map
              ((modulePullbackPushforwardAdjunction g).counit.app
                (SheafOfModules.unit (structureSheafRing S'))) ≫
            nu =
        (modulePullback g').map psi ≫
          (modulePullbackPushforwardAdjunction g').counit.app
            (SheafOfModules.unit (structureSheafRing X')))
    (hPg : IsIso (singlePushforwardComparison g (SheafOfModules.unit (structureSheafRing S')) 0))
    (hPg' : IsIso
      (singlePushforwardComparison g' (SheafOfModules.unit (structureSheafRing X')) 0))
    (hDf : IsIso (derivedToOrdinaryPullbackSingle f
      ((modulePushforward g).obj (SheafOfModules.unit (structureSheafRing S'))) 0))
    (hDf' : IsIso
      (derivedToOrdinaryPullbackSingle f' (SheafOfModules.unit (structureSheafRing S')) 0))
    (hnu : IsIso nu) (hpsi : IsIso psi) :
    IsIso (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap f' g' g f w.symm
      ((singleFunctor _ 0).obj (SheafOfModules.unit (structureSheafRing S')))) := by
  refine (isIso_comp_left_iff ((derivedPullback f).map
      (singlePushforwardComparison g (SheafOfModules.unit (structureSheafRing S')) 0)) _).1
    ((isIso_comp_right_iff _ ((derivedPushforward g').map
      (derivedToOrdinaryPullbackSingle f' (SheafOfModules.unit (structureSheafRing S')) 0 ≫
        (singleFunctor _ 0).map nu))).1 ?_)
  rw [assoc, derivedBaseChangeMap_singleUnit_eq_of g' f' f g w psi nu h5]
  infer_instance

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
