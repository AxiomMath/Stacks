module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SinglePushforwardCounit

/-!
# The single-complex pullback comparison around a commutative square

Let

```
      g'
  X' ---→ X
  |       |
f'|       |f
  v   g   v
  S' ---→ S
```

be a commutative square of ringed spaces.  The comparison
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle` is multiplicative
in the morphism (`derivedToOrdinaryPullbackSingle_comp`); this file reads that around the square.
The resulting statement is: the comparison of the two iterated derived pullbacks — the 2-cell
whose mate is the derived base-change map of [Stacks, Tag 08HY] — followed by one comparison
along each route, is the comparison along the other route followed by the *ordinary*
identification `g'^*f^* ≅ f'^*g^*` of the two composite inverse images.

## Main definitions

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.modulePullbackSquareIso` — the identification
  `f^* ⋙ g'^* ≅ g^* ⋙ f'^*` of the two composite inverse images of the square, for ringed
  spaces, built from `Stacks.DerivedPullback.Composition.modulePullbackComp` and the equality of
  the two composites.

## Main results

* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle_congr` — the
  comparison transported along an equality of morphisms of ringed spaces.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle_congrIso` and
  `...derivedToOrdinaryPullbackSingle_congrOf` — the same with the transport folded into an
  isomorphism, and with that isomorphism carried as a variable.
* `Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle_square` — **the
  theorem**.
* `Stacks.SingleComparison.squareChain` and `Stacks.SingleComparison.squareChainIso` — the
  composition bookkeeping, with no geometry in it.

## Implementation notes

Both routes are rewritten by `derivedToOrdinaryPullbackSingle_comp`, which leaves the two
comparisons for the common composite `g' ≫ f = f' ≫ g` and the transport between them; that
transport is `derivedToOrdinaryPullbackSingle_congr`, and what remains is the definition of
`modulePullbackSquareIso` and the full faithfulness of the single functor, which the proof uses
only through `CategoryTheory.Functor.map_comp`.

*Why the transport comes in two shapes.*  A consumer that holds the comparison as
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft` — which is what the adjoint
characterization of the derived base-change map produces — cannot split its component into the
composition isomorphism and the transport: at this spelling of the categories the kernel does not
check `(α ≫ β).app Z = α.app Z ≫ β.app Z` inside its deterministic limit.  So the transport is
also offered folded, by `derivedToOrdinaryPullbackSingle_congrIso`, and with the folded
isomorphism as a variable identified by a hypothesis, by
`derivedToOrdinaryPullbackSingle_congrOf`, which a consumer discharges by `subst`.  See the
implementation notes of
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/SingleBaseChangeStep.lean`.

## References

* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Category AlgebraicGeometry
open RingedSpaceModuleAdjunction HomologicalComplex
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

open DerivedCategory

universe u

/-! ### The composition bookkeeping -/

namespace Stacks.SingleComparison

/-- **The bookkeeping of the square, with no geometry in it.**  Given the two factorizations of
the two routes around the square (`hA` and `hB`), the transport between the two comparisons for
the common composite (`hcongr`), the factorization of the ordinary identification (`hs`) and the
two cancellations (`hci` and `hsa`), the two routes agree.

The chain is five rewrites long, and at the `SheafOfModules (structureSheafRing _)` spelling the
unification of its patterns against the goal exceeds the heartbeat limit in `isDefEq`; over
variables it costs nothing. -/
theorem squareChain {C : Type*} [Category C] {A B B₂ A₂ Y₀ T Z₀ Z R R₀ : C}
    (c1 : A ⟶ B) (t : B ⟶ B₂) (ci : B₂ ⟶ A₂) (ch : A₂ ⟶ B₂)
    (rS1 : A₂ ⟶ Y₀) (rS2 : Y₀ ⟶ T) (rX1 : A ⟶ Z₀) (rX2 : Z₀ ⟶ Z)
    (Da : B ⟶ R₀) (Db : B₂ ⟶ R) (sa : R₀ ⟶ Z) (sb : R ⟶ T) (m : R₀ ⟶ R) (n : Z ⟶ R₀)
    (s : Z ⟶ T)
    (hA : rS1 ≫ rS2 = ch ≫ Db ≫ sb)
    (hB : rX1 ≫ rX2 = c1 ≫ Da ≫ sa)
    (hcongr : t ≫ Db = Da ≫ m)
    (hs : s = n ≫ m ≫ sb)
    (hci : ci ≫ ch = 𝟙 B₂)
    (hsa : sa ≫ n = 𝟙 R₀) :
    (c1 ≫ t ≫ ci) ≫ rS1 ≫ rS2 = rX1 ≫ rX2 ≫ s := by
  calc (c1 ≫ t ≫ ci) ≫ rS1 ≫ rS2
      = c1 ≫ t ≫ (ci ≫ ch) ≫ Db ≫ sb := by rw [hA]; simp only [Category.assoc]
    _ = c1 ≫ (t ≫ Db) ≫ sb := by rw [hci]; simp only [Category.id_comp, Category.assoc]
    _ = c1 ≫ Da ≫ m ≫ sb := by rw [hcongr]; simp only [Category.assoc]
    _ = (c1 ≫ Da ≫ sa) ≫ n ≫ m ≫ sb := by
        simp only [Category.assoc]
        rw [← Category.assoc sa n, hsa, Category.id_comp]
    _ = rX1 ≫ rX2 ≫ s := by rw [← hB, hs]; simp only [Category.assoc]

/-- **The bookkeeping of the square with the transport folded in.**  As `squareChain`, but with
the first two factors of the left-hand route given as one morphism `d1`, and the transport
hypothesis `hd1` stated for it. -/
theorem squareChainIso {C : Type*} [Category C] {A B₂ A₂ Y₀ T R₀ R R' Z S₃ : C}
    (d1 : A ⟶ B₂) (ci : B₂ ⟶ A₂) (ch : A₂ ⟶ B₂)
    (rS1 : A₂ ⟶ Y₀) (rS2 : Y₀ ⟶ T) (rX1 : A ⟶ Z) (rX2 : Z ⟶ S₃)
    (c1h : A ⟶ R₀) (Da : R₀ ⟶ R) (Db : B₂ ⟶ R') (sa : R ⟶ S₃) (sb : R' ⟶ T) (m : R ⟶ R')
    {n : S₃ ⟶ R} {s : S₃ ⟶ T}
    (hA : rS1 ≫ rS2 = ch ≫ Db ≫ sb)
    (hB : rX1 ≫ rX2 = c1h ≫ Da ≫ sa)
    (hd1 : d1 ≫ Db = c1h ≫ Da ≫ m)
    (hs : s = n ≫ m ≫ sb)
    (hci : ci ≫ ch = 𝟙 B₂)
    (hsa : sa ≫ n = 𝟙 R) :
    (d1 ≫ ci) ≫ rS1 ≫ rS2 = rX1 ≫ rX2 ≫ s := by
  simpa using squareChain (𝟙 A) d1 ci ch rS1 rS2 rX1 rX2 (c1h ≫ Da) Db sa sb m n s hA
    (by simpa using hB) (by simpa using hd1) hs hci hsa

end Stacks.SingleComparison

/-! ### Transport along an equality of morphisms -/

section Congr

variable {X S : RingedSpace.{u, u}}

attribute [local instance] HasDerivedCategory.standard

/-- **The single-complex comparison transported along an equality of morphisms.**  For
`h : a = b` of morphisms of ringed spaces, the comparison for `b` precomposed with the transport
of the derived pullbacks is the comparison for `a` followed by the transport of the ordinary
pullbacks. -/
theorem derivedToOrdinaryPullbackSingle_congr {a b : X ⟶ S} (h : a = b)
    (M : SheafOfModules.{u} (structureSheafRing S)) (d : ℤ) :
    (eqToHom (congrArg (fun k : X ⟶ S => derivedPullback k) h)).app
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing S)) d).obj M) ≫
        derivedToOrdinaryPullbackSingle b M d =
      derivedToOrdinaryPullbackSingle a M d ≫
        (singleFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
          ((eqToHom (congrArg (fun k : X ⟶ S => modulePullback k) h)).app M) := by
  subst h
  simp


/-- **The single-complex comparison transported along an equality of morphisms, with the
transport folded into an isomorphism.**  This is `derivedToOrdinaryPullbackSingle_congr` with the
transport composed into a given isomorphism of the derived pullback along `a`.

Folding it is not cosmetic: at the `SheafOfModules (structureSheafRing _)` spelling the kernel
does not check `(α ≫ β).app Z = α.app Z ≫ β.app Z` within its deterministic limit — the derived
category's instance is built through definitions the elaborator leaves folded and the kernel does
not — so a consumer must never split the component of a composite there.  Folded, the statement
is proved by `subst`, where the transport becomes the identity. -/
theorem derivedToOrdinaryPullbackSingle_congrIso {a b : X ⟶ S} (h : a = b)
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (c : K ≅ derivedPullback a)
    (M : SheafOfModules.{u} (structureSheafRing S)) (d : ℤ) :
    (c ≪≫ eqToIso (congrArg (fun k : X ⟶ S => derivedPullback k) h)).hom.app
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing S)) d).obj M) ≫
        derivedToOrdinaryPullbackSingle b M d =
      c.hom.app ((singleFunctor (SheafOfModules.{u} (structureSheafRing S)) d).obj M) ≫
        derivedToOrdinaryPullbackSingle a M d ≫
          (singleFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
            ((eqToHom (congrArg (fun k : X ⟶ S => modulePullback k) h)).app M) := by
  subst h
  simp


/-- **The single-complex comparison transported along an equality of morphisms, for any
isomorphism presented as the transport.**  `derivedToOrdinaryPullbackSingle_congrIso` with the
isomorphism carried as a variable and its identification as a hypothesis, so that a consumer
instantiates rather than rewrites.

The distinction matters at this spelling of the categories: a `rw` leaves the kernel a motive to
type-check, and type-checking a motive over `DerivedCategory (SheafOfModules (structureSheafRing
_))` exceeds its deterministic limit, while `subst` on a hypothesis leaves it nothing to do. -/
theorem derivedToOrdinaryPullbackSingle_congrOf {a b : X ⟶ S} (h : a = b)
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (c : K ≅ derivedPullback a) (e : K ≅ derivedPullback b)
    (he : e = c ≪≫ eqToIso (congrArg (fun k : X ⟶ S => derivedPullback k) h))
    (M : SheafOfModules.{u} (structureSheafRing S)) (d : ℤ) :
    e.hom.app ((singleFunctor (SheafOfModules.{u} (structureSheafRing S)) d).obj M) ≫
        derivedToOrdinaryPullbackSingle b M d =
      c.hom.app ((singleFunctor (SheafOfModules.{u} (structureSheafRing S)) d).obj M) ≫
        derivedToOrdinaryPullbackSingle a M d ≫
          (singleFunctor (SheafOfModules.{u} (structureSheafRing X)) d).map
            ((eqToHom (congrArg (fun k : X ⟶ S => modulePullback k) h)).app M) := by
  subst he
  exact derivedToOrdinaryPullbackSingle_congrIso h c M d

end Congr

/-! ### The identification of the two composite inverse images -/

section Square

variable {X' X S' S : RingedSpace.{u, u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)

/-- **The identification `f^* ⋙ g'^* ≅ g^* ⋙ f'^*` of the two composite inverse images** around
a commutative square of ringed spaces: the composition isomorphism down one route, the transport
along the equality of the two composites, and the inverse of the composition isomorphism down
the other. -/
def modulePullbackSquareIso (w : g' ≫ f = f' ≫ g) :
    modulePullback f ⋙ modulePullback g' ≅ modulePullback g ⋙ modulePullback f' :=
  Stacks.DerivedPullback.Composition.modulePullbackComp g' f ≪≫
    eqToIso (congrArg (fun k : X' ⟶ S => modulePullback k) w) ≪≫
    (Stacks.DerivedPullback.Composition.modulePullbackComp f' g).symm

attribute [local instance] HasDerivedCategory.standard

/-- **The single-complex pullback comparison around a commutative square.**  The comparison of
the two iterated derived pullbacks, followed by the single-complex comparison along the route
through `S'`, equals the single-complex comparison along the route through `X` followed by the
ordinary identification `g'^*f^*M ≅ f'^*g^*M`.

Both routes are `derivedToOrdinaryPullbackSingle_comp`; what is left is the transport along the
equality of the two composites, which is `derivedToOrdinaryPullbackSingle_congr`. -/
theorem derivedToOrdinaryPullbackSingle_square (w : g' ≫ f = f' ≫ g)
    (M : SheafOfModules.{u} (structureSheafRing S)) (d : ℤ) :
    ((derivedPullbackCompIsoCanonical g' f).hom.app
            ((singleFunctor (SheafOfModules.{u} (structureSheafRing S)) d).obj M) ≫
          (eqToHom (congrArg (fun k : X' ⟶ S => derivedPullback k) w)).app
            ((singleFunctor (SheafOfModules.{u} (structureSheafRing S)) d).obj M) ≫
          (derivedPullbackCompIsoCanonical f' g).inv.app
            ((singleFunctor (SheafOfModules.{u} (structureSheafRing S)) d).obj M)) ≫
        (derivedPullback f').map (derivedToOrdinaryPullbackSingle g M d) ≫
        derivedToOrdinaryPullbackSingle f' ((modulePullback g).obj M) d =
      (derivedPullback g').map (derivedToOrdinaryPullbackSingle f M d) ≫
        derivedToOrdinaryPullbackSingle g' ((modulePullback f).obj M) d ≫
        (singleFunctor (SheafOfModules.{u} (structureSheafRing X')) d).map
          ((modulePullbackSquareIso g' f' f g w).hom.app M) := by
  have hs : (singleFunctor (SheafOfModules.{u} (structureSheafRing X')) d).map
        ((modulePullbackSquareIso g' f' f g w).hom.app M) =
      (singleFunctor (SheafOfModules.{u} (structureSheafRing X')) d).map
          ((Stacks.DerivedPullback.Composition.modulePullbackComp g' f).hom.app M) ≫
        (singleFunctor (SheafOfModules.{u} (structureSheafRing X')) d).map
            ((eqToHom (congrArg (fun k : X' ⟶ S => modulePullback k) w)).app M) ≫
          (singleFunctor (SheafOfModules.{u} (structureSheafRing X')) d).map
            ((Stacks.DerivedPullback.Composition.modulePullbackComp f' g).inv.app M) := by
    simp only [modulePullbackSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      eqToIso.hom, Functor.map_comp]
  have hsa : (singleFunctor (SheafOfModules.{u} (structureSheafRing X')) d).map
          ((Stacks.DerivedPullback.Composition.modulePullbackComp g' f).inv.app M) ≫
        (singleFunctor (SheafOfModules.{u} (structureSheafRing X')) d).map
          ((Stacks.DerivedPullback.Composition.modulePullbackComp g' f).hom.app M) = 𝟙 _ := by
    rw [← (singleFunctor (SheafOfModules.{u} (structureSheafRing X')) d).map_comp,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  exact Stacks.SingleComparison.squareChain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (derivedToOrdinaryPullbackSingle_comp f' g d M)
    (derivedToOrdinaryPullbackSingle_comp g' f d M)
    (derivedToOrdinaryPullbackSingle_congr w M d) hs
    ((derivedPullbackCompIsoCanonical f' g).inv_hom_id_app _) hsa


end Square

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
