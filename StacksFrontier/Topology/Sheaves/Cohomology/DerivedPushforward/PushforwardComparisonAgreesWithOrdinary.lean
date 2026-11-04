module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.BaseChangeTranspose
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.OrdinaryBaseChangeTranspose

/-!
# The two comparisons of the iterated pushforwards around a square agree

For a commutative square of ringed spaces

```
X' --g'--> X
|f'        |f
S' --g-->  S
```

the **derived** base change map of [Stacks, Tag 08HY] and the **ordinary** one of
[Stacks, Tag 0096] agree, conjugated by the comparisons of the models (`derivedBaseChangeMap_fac`).
Transposed along the bottom of the square, this becomes an identity between the two routes from
`Q(f_* M)` to `Rg_* (Rf'_* (Q((g')^* M)))`:

* down the derived side: the comparison `Q(f_* M) ⟶ Rf_* (Q M)`, then `Rf_*` of the **derived**
  unit of `L(g')^* ⊣ R(g')_*`, then the derived comparison of the two iterated derived
  pushforwards, then `Rg_* Rf'_*` of the comparison `L(g')^*(Q M) ⟶ Q((g')^* M)`;
* down the ordinary side: `Q` of the **degreewise** unit of `(g)^* ⊣ g_*`, then the comparison
  `Q(g^* (f_* M)) ⟶ Rg_*(Q((g)^* f_* M))`, then `Rg_*` of `Q` of the ordinary base change map,
  then `Rg_*` of the comparison `Q(f'_* (g')^* M) ⟶ Rf'_*(Q((g')^* M))`.

## Main results

* `Stacks.Cohomology.DerivedBaseChange.derivedPushforwardComparison_fac`: **the identity
  displayed above.**
* `Stacks.Cohomology.DerivedBaseChange.Mate.homEquiv_map_comp_comp` and
  `Stacks.Cohomology.DerivedBaseChange.Mate.homEquiv_comp_comp`: transposing a composite of three
  factors under an adjunction, at variables of abstract categories.
* `Stacks.Cohomology.DerivedBaseChange.derivedPullbackComparison_homEquiv`: the transpose, under
  the derived adjunction, of the comparison `Lk^* (Q N) ⟶ Q (k^* N)` — it is `Q` of the degreewise
  unit followed by the comparison `Q (k_* (k^* N)) ⟶ Rk_* (Q (k^* N))`.
* `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare_eq_mate` and
  `derivedBaseChangeSquare_app_eq`: the derived base change two-square of a commutative square of
  ringed spaces is the generic `Mate` two-square at the square's data, as an equality of
  two-squares and read at a complex.
* `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_fac_mate`:
  `derivedBaseChangeMap_fac` with its derived base change map written as the component of the
  generic `Mate` two-square.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction Stacks.DerivedPullback.Composition
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.Cohomology.DerivedBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### Transposing a composite, on variables -/

/-- Transposing a composite whose first factor is the image of a morphism under the left adjoint:
the transposition moves past it, and a last factor is carried by the right adjoint. -/
theorem Mate.homEquiv_map_comp_comp {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {A A' X : C} {B B' : D} (u : A ⟶ A') (w : L.obj A' ⟶ B)
    (c : B ⟶ B') {t₁ : A' ⟶ X} {t₂ : X ⟶ R.obj B} (ht : adj.homEquiv A' B w = t₁ ≫ t₂) :
    adj.homEquiv A B' (L.map u ≫ w ≫ c) = u ≫ t₁ ≫ t₂ ≫ R.map c := by
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_left, ht]
  simp only [Category.assoc]

/-- Transposing a composite of three factors whose first one has a known transpose. -/
theorem Mate.homEquiv_comp_comp {C D : Type*} [Category C] [Category D] {L : C ⥤ D}
    {R : D ⥤ C} (adj : L ⊣ R) {A X : C} {B B₁ B₂ : D} (b : L.obj A ⟶ B) (q : B ⟶ B₁)
    (v : B₁ ⟶ B₂) {t₁ : A ⟶ X} {t₂ : X ⟶ R.obj B} (ht : adj.homEquiv A B b = t₁ ≫ t₂) :
    adj.homEquiv A B₂ (b ≫ q ≫ v) = t₁ ≫ t₂ ≫ R.map q ≫ R.map v := by
  simpa using Mate.homEquiv_map_comp_comp adj (𝟙 A) b (q ≫ v) ht

/-! ### The transpose of the derived pullback comparison -/

variable {X' X S' S : RingedSpace.{u, u}}

/-- **The transpose, under the derived adjunction, of the comparison
`Lk^* (Q N) ⟶ Q (k^* N)`.**  It is `Q` of the degreewise unit of `k^* ⊣ k_*`, followed by the
comparison `Q (k_* (k^* N)) ⟶ Rk_* (Q (k^* N))`. -/
theorem derivedPullbackComparison_homEquiv {A B : RingedSpace.{u, u}} (k : A ⟶ B)
    (N : HomotopyCategory (SheafOfModules.{u} (structureSheafRing B)) (ComplexShape.up ℤ)) :
    (derivedAdjunction k).homEquiv (DerivedCategory.Qh.obj N)
        (DerivedCategory.Qh.obj
          (((modulePullback k).mapHomotopyCategory (ComplexShape.up ℤ)).obj N))
        ((derivedPullbackComparison k).app N) =
      DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction k).unit.app N) ≫
        (derivedPushforwardUnit k).app
          (((modulePullback k).mapHomotopyCategory (ComplexShape.up ℤ)).obj N) := by
  rw [Adjunction.homEquiv_unit]
  exact derivedAdjunction_unit_fac k N

/-! ### The two comparisons of the iterated pushforwards agree -/

variable (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)

/-- **The derived base change two-square of a commutative square of ringed spaces is the generic
`Mate` two-square at the square's data**, as an equality of two-squares. -/
theorem derivedBaseChangeSquare_eq_mate :
    derivedBaseChangeSquare g' f' f g sq =
      Mate.derivedBaseChangeSquare (derivedAdjunction f) (derivedAdjunction f')
        (derivedPullbackCompIsoLeft g' f' f g sq)
        (derivedPullbackCompIsoCanonical g' f) :=
  rfl

/-- The derived base change map of a commutative square of ringed spaces, at a complex, written as
the component of the generic `Mate` two-square. -/
theorem derivedBaseChangeSquare_app_eq
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedBaseChangeSquare g' f' f g sq).app K =
      (Mate.derivedBaseChangeSquare (derivedAdjunction f) (derivedAdjunction f')
        (derivedPullbackCompIsoLeft g' f' f g sq)
        (derivedPullbackCompIsoCanonical g' f)).app K := by
  rw [derivedBaseChangeSquare_eq_mate]

/-- `Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap_fac` with its derived base change
map written as the component of the generic `Mate` two-square. -/
theorem derivedBaseChangeMap_fac_mate
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPullback g).map ((derivedPushforwardUnit f).app M) ≫
        (Mate.derivedBaseChangeSquare (derivedAdjunction f) (derivedAdjunction f')
            (derivedPullbackCompIsoLeft g' f' f g sq)
            (derivedPullbackCompIsoCanonical g' f)).app (DerivedCategory.Qh.obj M) ≫
          (derivedPushforward f').map ((derivedPullbackComparison g').app M) =
      (derivedPullbackComparison g).app
          (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Qh.map ((homotopyBaseChangeSquare g' f' f g sq).app M) ≫
          (derivedPushforwardUnit f').app
            (((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).obj M) :=
  Eq.trans
    (congrArg (fun x => (derivedPullback g).map ((derivedPushforwardUnit f).app M) ≫
        x ≫ (derivedPushforward f').map ((derivedPullbackComparison g').app M))
      (derivedBaseChangeSquare_app_eq g' f' f g sq (DerivedCategory.Qh.obj M)).symm)
    (derivedBaseChangeMap_fac g' f' f g sq M)

/-- **The derived comparison of the two iterated derived pushforwards around a commutative square
of ringed spaces agrees with the ordinary one**, conjugated by the comparisons of the models and
precomposed with the two units of the square's top horizontal morphism and of its bottom one. -/
theorem derivedPushforwardComparison_fac
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPushforwardUnit f).app M ≫
        (derivedPushforward f).map
          ((derivedAdjunction g').unit.app (DerivedCategory.Qh.obj M)) ≫
        (Mate.derivedPushforwardComparisonSquare (derivedAdjunction f) (derivedAdjunction f')
            (derivedAdjunction g) (derivedAdjunction g')
            (derivedPullbackCompIsoLeft g' f' f g sq)
            (derivedPullbackCompIsoCanonical g' f)).app
          ((derivedPullback g').obj (DerivedCategory.Qh.obj M)) ≫
        (derivedPushforward g).map
          ((derivedPushforward f').map ((derivedPullbackComparison g').app M)) =
      DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction g).unit.app
          (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) ≫
        (derivedPushforwardUnit g).app
          (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) ≫
        (derivedPushforward g).map
          (DerivedCategory.Qh.map ((homotopyBaseChangeSquare g' f' f g sq).app M)) ≫
        (derivedPushforward g).map
          ((derivedPushforwardUnit f').app
            (((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) :=
  Eq.trans
    (Eq.trans
      (Mate.homEquiv_map_comp_comp (derivedAdjunction g) ((derivedPushforwardUnit f).app M) _
        ((derivedPushforward f').map ((derivedPullbackComparison g').app M))
        (Mate.derivedBaseChangeMap_homEquiv (derivedAdjunction f) (derivedAdjunction f')
          (derivedAdjunction g) (derivedAdjunction g')
          (derivedPullbackCompIsoLeft g' f' f g sq) (derivedPullbackCompIsoCanonical g' f)
          (DerivedCategory.Qh.obj M))).symm
      (congrArg _ (derivedBaseChangeMap_fac_mate g' f' f g sq M)))
    (Mate.homEquiv_comp_comp (derivedAdjunction g) _ _ _
      (derivedPullbackComparison_homEquiv g
        (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)))

end Stacks.Cohomology.DerivedBaseChange

end
