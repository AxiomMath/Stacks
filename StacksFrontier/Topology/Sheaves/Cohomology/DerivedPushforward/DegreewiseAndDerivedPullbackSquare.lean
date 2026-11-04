module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeMapUnderived
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditional
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OrdinaryAndDerivedBaseChange

/-!
# The degreewise and the derived comparison of the two iterated pullbacks of a square

Let

```
X' --g'--> X
|f'        |f
S' --g-->  S
```

be a commutative square of ringed spaces.  Two comparisons of the two iterated pullbacks around
it are available: the **derived** one,
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackSquare`, a two-square
`Lg^* ⋙ Lf'^* ⟶ Lf^* ⋙ Lg'^*` built from the composition isomorphism of [Stacks, Tag 0D5S] at
`(f', g)` and at `(g', f)`, and the **degreewise** one, built here in exactly the same way from
the degreewise pullback-composition isomorphism
`Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso`.

This file identifies the two: at a complex `N` of `𝒪_S`-modules the derived comparison, followed
by the comparison `Lk^* ⟶ k^*` of [Stacks, Tag 06YJ] for `k = f` and for `k = g'`, agrees with
the comparison for `g` and for `f'` followed by the degreewise comparison.

## Main definitions

* `Stacks.Cohomology.DerivedBaseChange.homotopyPullbackSquare`: the degreewise analogue of
  `Stacks.Cohomology.DerivedBaseChange.derivedPullbackSquare`, read as a two-square.  Its left
  leg is the iterated degreewise pullback down the left and along the bottom identified with
  degreewise pullback along the common composite, which is
  `Stacks.Cohomology.DerivedBaseChange.pullbackOnHomotopyCompIsoLeft`.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft_hom_app_comp_comparison`:
  [Stacks, Tag 0D5S] at `(f', g)`, transported along the commutativity of the square — the
  composition isomorphism down the left factors the comparison for the common composite through
  the degreewise one.
* `Stacks.Cohomology.DerivedBaseChange.comparison_comp_homotopyPullbackSquare`: **the two
  comparisons of the square agree**, at a complex of `𝒪_S`-modules: the derived pullback along
  `f'` of the comparison for `g`, then the comparison for `f'`, then the degreewise two-square,
  equals the derived two-square, then the derived pullback along `g'` of the comparison for `f`,
  then the comparison for `g'`.

## References

* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 06YJ](https://stacks.math.columbia.edu/tag/06YJ)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedPushforwardComposition

namespace Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Mate

section Objectwise

variable {C : Type*} [Category C] {P P' P'' Q R T V W : C}
  (α : P ⟶ Q) (β : Q ⟶ R) (γ : R ⟶ T) (δ : T ⟶ V) (γ' : V ⟶ T)
  (e : P ⟶ P') (i : P' ⟶ P'') (j : P'' ⟶ P') (c : P' ⟶ T) (ζ : P'' ⟶ W) (η : W ⟶ V)

/-- **The two comparisons of a square agree, objectwise.**  If `e ≫ c = α ≫ β ≫ γ` and
`j ≫ c = ζ ≫ η ≫ γ'`, `i` is a section of `j` and `δ` is a retraction of `γ'`, then
`α ≫ β ≫ γ ≫ δ = e ≫ i ≫ ζ ≫ η`. -/
theorem comparison_comp_of_comp_eq (hij : i ≫ j = 𝟙 P') (hδ : γ' ≫ δ = 𝟙 V)
    (hA : e ≫ c = α ≫ β ≫ γ) (hB : j ≫ c = ζ ≫ η ≫ γ') :
    α ≫ β ≫ γ ≫ δ = e ≫ i ≫ ζ ≫ η := by
  have hζη : ζ ≫ η = j ≫ c ≫ δ := by rw [reassoc_of% hB, hδ, Category.comp_id]
  rw [hζη, reassoc_of% hij, reassoc_of% hA]

end Objectwise

end Mate

section Canonical

variable {X' X S' S : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)

/-- The comparison `K(g^*) ⋙ K((f')^*) ⟶ K(f^*) ⋙ K((g')^*)` of the two iterated degreewise
pullbacks around a commutative square of ringed spaces, read as a two-square.  This is the
degreewise analogue of `Stacks.Cohomology.DerivedBaseChange.derivedPullbackSquare`, formed in
the same way from the two composition isomorphisms. -/
def homotopyPullbackSquare :
    TwoSquare ((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ))
      ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ))
      ((modulePullback f').mapHomotopyCategory (ComplexShape.up ℤ))
      ((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)) :=
  TwoSquare.mk _ _ _ _
    ((pullbackOnHomotopyCompIsoLeft g' f' f g sq).hom ≫ (pullbackOnHomotopyCompIso g' f).inv)

/-- `Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft` is the composition
isomorphism of [Stacks, Tag 0D5S] at `(f', g)` followed by the transport along the square. -/
theorem derivedPullbackCompIsoLeft_eq :
    derivedPullbackCompIsoLeft g' f' f g sq =
      derivedPullbackCompIsoCanonical f' g ≪≫ eqToIso (congrArg (fun h : X' ⟶ S =>
        derivedPullback h) sq.symm) :=
  rfl

/-- The component of `Stacks.Cohomology.DerivedBaseChange.derivedPullbackSquare` at an object,
written out as the composite of the two composition isomorphisms. -/
theorem derivedPullbackSquare_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S))) :
    (derivedPullbackSquare g' f' f g sq).app K =
      (derivedPullbackCompIsoLeft g' f' f g sq).hom.app K ≫
        (derivedPullbackCompIsoCanonical g' f).inv.app K :=
  rfl

/-- The component of `Stacks.Cohomology.DerivedBaseChange.homotopyPullbackSquare` at an object,
written out as the composite of the two degreewise composition isomorphisms. -/
theorem homotopyPullbackSquare_app
    (K : HomotopyCategory (SheafOfModules.{u} (structureSheafRing S)) (ComplexShape.up ℤ)) :
    (homotopyPullbackSquare g' f' f g sq).app K =
      (pullbackOnHomotopyCompIsoLeft g' f' f g sq).hom.app K ≫
        (pullbackOnHomotopyCompIso g' f).inv.app K :=
  rfl

end Canonical

section Transport

variable {X' S' S : RingedSpace.{u, u}}

/-- **[Stacks, Tag 0D5S] at `(f', g)`, with the composite named.**  For any morphism `k` equal to
`f' ≫ g`, the composition isomorphism at `(f', g)` followed by the transport along that equality
factors the comparison `Lk^* ⟶ k^*` through the comparison for `g`, the comparison for `f'` and
the degreewise composition isomorphism. -/
theorem derivedPullbackCompIsoCanonical_trans_hom_app_comp_comparison {k : X' ⟶ S}
    (f' : X' ⟶ S') (g : S' ⟶ S) (e : f' ≫ g = k)
    (N : HomotopyCategory (SheafOfModules.{u} (structureSheafRing S)) (ComplexShape.up ℤ)) :
    (derivedPullbackCompIsoCanonical f' g ≪≫ eqToIso (congrArg (fun h : X' ⟶ S =>
          derivedPullback h) e)).hom.app (DerivedCategory.Qh.obj N) ≫
        (derivedPullbackComparison k).app N =
      (derivedPullback f').map ((derivedPullbackComparison g).app N) ≫
        (derivedPullbackComparison f').app
            (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj N) ≫
          DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso f' g ≪≫ eqToIso (congrArg
            (fun h : X' ⟶ S => (modulePullback h).mapHomotopyCategory
              (ComplexShape.up ℤ)) e)).hom.app N) := by
  subst e
  simp only [eqToIso_refl, Iso.trans_refl]
  exact derivedPullbackCompIsoCanonical_hom_app_comp_comparison f' g N

end Transport

section Square

variable {X' X S' S : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)

/-- **[Stacks, Tag 0D5S] down the left of the square.**
`Stacks.Cohomology.DerivedBaseChange.derivedPullbackCompIsoLeft` factors the comparison
`L(g' ≫ f)^* ⟶ (g' ≫ f)^*` through the comparison for `g`, the comparison for `f'` and the
degreewise `Stacks.Cohomology.DerivedBaseChange.pullbackOnHomotopyCompIsoLeft`. -/
theorem derivedPullbackCompIsoLeft_hom_app_comp_comparison
    (N : HomotopyCategory (SheafOfModules.{u} (structureSheafRing S)) (ComplexShape.up ℤ)) :
    (derivedPullbackCompIsoLeft g' f' f g sq).hom.app (DerivedCategory.Qh.obj N) ≫
        (derivedPullbackComparison (g' ≫ f)).app N =
      (derivedPullback f').map ((derivedPullbackComparison g).app N) ≫
        (derivedPullbackComparison f').app
            (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj N) ≫
          DerivedCategory.Qh.map
            ((pullbackOnHomotopyCompIsoLeft g' f' f g sq).hom.app N) := by
  rw [derivedPullbackCompIsoLeft_eq]
  exact derivedPullbackCompIsoCanonical_trans_hom_app_comp_comparison f' g sq.symm N

/-- The degreewise pullback-composition isomorphism at `(g', f)` stays invertible after
localizing to the derived category, componentwise. -/
theorem Qh_map_pullbackOnHomotopyCompIso_hom_inv_app
    (N : HomotopyCategory (SheafOfModules.{u} (structureSheafRing S)) (ComplexShape.up ℤ)) :
    DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso g' f).hom.app N) ≫
        DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso g' f).inv.app N) = 𝟙 _ := by
  rw [← DerivedCategory.Qh.map_comp, Iso.hom_inv_id_app]
  simp

/-- **The degreewise and the derived comparison of the two iterated pullbacks of the square
agree.**  At a complex `N` of `𝒪_S`-modules, the derived pullback along `f'` of the comparison
for `g`, then the comparison for `f'`, then the degreewise two-square, equals the derived
two-square, then the derived pullback along `g'` of the comparison for `f`, then the comparison
for `g'`. -/
theorem comparison_comp_homotopyPullbackSquare
    (N : HomotopyCategory (SheafOfModules.{u} (structureSheafRing S)) (ComplexShape.up ℤ)) :
    (derivedPullback f').map ((derivedPullbackComparison g).app N) ≫
        (derivedPullbackComparison f').app
            (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj N) ≫
          DerivedCategory.Qh.map ((pullbackOnHomotopyCompIsoLeft g' f' f g sq).hom.app N) ≫
            DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso g' f).inv.app N) =
      (derivedPullbackCompIsoLeft g' f' f g sq).hom.app (DerivedCategory.Qh.obj N) ≫
        (derivedPullbackCompIsoCanonical g' f).inv.app (DerivedCategory.Qh.obj N) ≫
          (derivedPullback g').map ((derivedPullbackComparison f).app N) ≫
            (derivedPullbackComparison g').app
              (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).obj N) :=
  Mate.comparison_comp_of_comp_eq
    ((derivedPullback f').map ((derivedPullbackComparison g).app N))
    ((derivedPullbackComparison f').app
      (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj N))
    (DerivedCategory.Qh.map ((pullbackOnHomotopyCompIsoLeft g' f' f g sq).hom.app N))
    (DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso g' f).inv.app N))
    (DerivedCategory.Qh.map ((pullbackOnHomotopyCompIso g' f).hom.app N))
    ((derivedPullbackCompIsoLeft g' f' f g sq).hom.app (DerivedCategory.Qh.obj N))
    ((derivedPullbackCompIsoCanonical g' f).inv.app (DerivedCategory.Qh.obj N))
    ((derivedPullbackCompIsoCanonical g' f).hom.app (DerivedCategory.Qh.obj N))
    ((derivedPullbackComparison (g' ≫ f)).app N)
    ((derivedPullback g').map ((derivedPullbackComparison f).app N))
    ((derivedPullbackComparison g').app
      (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).obj N))
    ((derivedPullbackCompIsoCanonical g' f).inv_hom_id_app (DerivedCategory.Qh.obj N))
    (Qh_map_pullbackOnHomotopyCompIso_hom_inv_app g' f N)
    (derivedPullbackCompIsoLeft_hom_app_comp_comparison g' f' f g sq N)
    (derivedPullbackCompIsoCanonical_hom_app_comp_comparison g' f N)

end Square

end Stacks.Cohomology.DerivedBaseChange

end
