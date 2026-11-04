module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PushforwardComparisonAgreesWithOrdinary

/-!
# The derived base change map transposed along the bottom, against the ordinary data

Let

```
X' --g'--> X
|f'        |f
S' --g-->  S
```

be a commutative square of ringed spaces. This file writes
`Stacks.Cohomology.DerivedBaseChange.derivedPushforwardComparison_fac` with its derived side as
one morphism transposed under `Lg^* ⊣ Rg_*`: the comparison `Q(f_* M) ⟶ Rf_*(Q M)` followed by
the transpose of the derived base change map of the square composed with `Rf'_*` of the
derived-pullback comparison is the route of the degreewise units of [Stacks, Tag 0096]. The
identity is then transported along an isomorphism `Q M ≅ K` and a trailing map
`Q((g')^* M) ⟶ N`, and solved for the transpose at a K-injective complex.

## Main results

* `map_unit_comp_edge_comp_map`: for an adjunction `L ⊣ R` and a natural transformation
  `E : R ⋙ H ⟶ H' ⋙ P`, the composite `H(η) ≫ E ≫ P(H'(φ))` is `H` of the transpose of `φ`
  followed by `E`.
* `homEquiv_derivedBaseChangeSquare_app`: the transpose of the derived base change map of the
  square.
* `derivedPushforwardUnit_comp_homEquiv_fac`: `derivedPushforwardComparison_fac` with its derived
  side written as one transposed morphism.
* `derivedPushforwardUnit_comp_map_hom_comp_homEquiv_fac`: the same, transported along an
  isomorphism `Q M ≅ K` and a trailing map.
* `map_hom_comp_homEquiv_derivedBaseChangeSquare_eq_inv_comp`: at a K-injective complex `I`, the
  transposed composite is the inverse of the comparison `Q(f_* [I]) ⟶ Rf_*(Q [I])` followed by the
  route of the degreewise units.

## Implementation notes

The rearrangements `comp_comp_tail`, `comp_pair_comp_comp`, `map_hom_comp_map_inv_comp`,
`homEquiv_comp_eq`, `iso_hom_comp_eq`, `map_comp_map_comp_comp` and `map_hom_comp_app_comp_map`
are stated at variables of abstract categories: a `Category.assoc` rewrite on the concrete
composites of total derived functors times out in `isDefEq`. `map_hom_comp_app_comp_map` writes
its two sides as `G.map (F.map _)` and `Q.map (P.map _)`, so that the base change two-square
matches it syntactically.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance] HasDerivedCategory.standard

/-! ### The rearrangements, on variables -/

section Abstract

variable {C D A₁ A₂ : Type*} [Category C] [Category D] [Category A₁] [Category A₂]

/-- If `a ≫ b = c₁ ≫ c₂ ≫ c₃ ≫ c₄`, then `a ≫ b ≫ t = c₁ ≫ c₂ ≫ c₃ ≫ c₄ ≫ t`. -/
theorem comp_comp_tail {A B₀ B₁ Z₁ Z₂ Z₃ W : C} {a : A ⟶ B₀} {b : B₀ ⟶ B₁} {c₁ : A ⟶ Z₁}
    {c₂ : Z₁ ⟶ Z₂} {c₃ : Z₂ ⟶ Z₃} {c₄ : Z₃ ⟶ B₁} (h : a ≫ b = c₁ ≫ c₂ ≫ c₃ ≫ c₄) (t : B₁ ⟶ W) :
    a ≫ b ≫ t = c₁ ≫ c₂ ≫ c₃ ≫ c₄ ≫ t := by
  rw [reassoc_of% h]

/-- If `t₁ ≫ t₂ = u₁ ≫ u₂` and `u₁ ≫ u₂ ≫ m = v₁ ≫ v₂`, then
`a ≫ t₁ ≫ t₂ ≫ m ≫ c = a ≫ v₁ ≫ v₂ ≫ c`. -/
theorem comp_pair_comp_comp {A B₀ B₁ B₂ B₃ B₄ Z Z' : C} (a : A ⟶ B₀) {t₁ : B₀ ⟶ B₁} {t₂ : B₁ ⟶ B₂}
    {m : B₂ ⟶ B₃} {u₁ : B₀ ⟶ Z} {u₂ : Z ⟶ B₂} {v₁ : B₀ ⟶ Z'} {v₂ : Z' ⟶ B₃}
    (hu : t₁ ≫ t₂ = u₁ ≫ u₂) (hv : u₁ ≫ u₂ ≫ m = v₁ ≫ v₂) (c : B₃ ⟶ B₄) :
    a ≫ t₁ ≫ t₂ ≫ m ≫ c = a ≫ v₁ ≫ v₂ ≫ c := by
  rw [reassoc_of% hu, reassoc_of% hv]

/-- The images under a functor of an isomorphism and of its inverse cancel in front of a
composite. -/
theorem map_hom_comp_map_inv_comp (F : C ⥤ D) {A B : C} (i : A ≅ B) {Z : D}
    (x : F.obj A ⟶ Z) : F.map i.hom ≫ F.map i.inv ≫ x = x := by
  rw [← Category.assoc, ← F.map_comp, i.hom_inv_id, F.map_id, Category.id_comp]

/-- If the transpose of `w` under `L ⊣ R` is `t₁ ≫ t₂`, then the transpose of `w ≫ c` is
`t₁ ≫ t₂ ≫ R.map c`. -/
theorem homEquiv_comp_eq {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {A Z : C} {B B' : D}
    (w : L.obj A ⟶ B) (c : B ⟶ B') {t₁ : A ⟶ Z} {t₂ : Z ⟶ R.obj B}
    (ht : adj.homEquiv A B w = t₁ ≫ t₂) :
    adj.homEquiv A B' (w ≫ c) = t₁ ≫ t₂ ≫ R.map c := by
  rw [Adjunction.homEquiv_naturality_right, ht, Category.assoc]

/-- If `x = i.inv ≫ y`, then `i.hom ≫ x = y`. -/
theorem iso_hom_comp_eq {A B Z : C} (i : A ≅ B) {x : B ⟶ Z} {y : A ⟶ Z} (h : x = i.inv ≫ y) :
    i.hom ≫ x = y := by
  rw [h, i.hom_inv_id_assoc]

/-- If `a ≫ b ≫ m = c`, then `H.map (a ≫ b) ≫ H.map m ≫ x ≫ y = H.map c ≫ x ≫ y`. -/
theorem map_comp_map_comp_comp (H : C ⥤ D) {P Q₁ Q₂ R : C} {a : P ⟶ Q₁} {b : Q₁ ⟶ Q₂}
    {m : Q₂ ⟶ R} {c : P ⟶ R} (h : a ≫ b ≫ m = c) {Z W : D} (x : H.obj R ⟶ Z) (y : Z ⟶ W) :
    H.map (a ≫ b) ≫ H.map m ≫ x ≫ y = H.map c ≫ x ≫ y := by
  rw [← Category.assoc, ← H.map_comp, Category.assoc, h]

/-- **An edge morphism absorbs a direct image of a map on cohomology.** For an adjunction
`L ⊣ R`, functors `H : C ⥤ A₁`, `H' : D ⥤ A₂` and `P : A₂ ⥤ A₁` and a natural transformation
`E : R ⋙ H ⟶ H' ⋙ P`, the composite

> `H(unit) ≫ E ≫ P(H'(φ))`

is `H` of the transpose of `φ` under `L ⊣ R`, followed by `E`. -/
theorem map_unit_comp_edge_comp_map {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (H : C ⥤ A₁)
    (H' : D ⥤ A₂) (P : A₂ ⥤ A₁) (E : R ⋙ H ⟶ H' ⋙ P) {K : C} {M : D} (φ : L.obj K ⟶ M) :
    H.map (adj.unit.app K) ≫ E.app (L.obj K) ≫ P.map (H'.map φ) =
      H.map (adj.homEquiv K M φ) ≫ E.app M := by
  rw [Adjunction.homEquiv_unit, H.map_comp, Category.assoc]
  exact H.map (adj.unit.app K) ≫= (E.naturality φ).symm

/-- **Transporting a natural transformation between composite functors along an isomorphism.**
For `β : F ⋙ G ⟶ P ⋙ Q` and an isomorphism `e : M₀ ≅ K`, the component of `β` at `K`, preceded
by `G(F(e.hom))` and followed by `Q` of a composite beginning with `P(e.inv)`, is the component
at `M₀` followed by `Q` of the rest. -/
theorem map_hom_comp_app_comp_map {ℬ : Type*} [Category ℬ] {F : C ⥤ D} {G : D ⥤ A₁} {P : C ⥤ ℬ}
    {Q : ℬ ⥤ A₁} (β : F ⋙ G ⟶ P ⋙ Q) {M₀ K : C} (e : M₀ ≅ K) {N₀ N : ℬ} (w : P.obj M₀ ⟶ N₀)
    (r : N₀ ⟶ N) :
    G.map (F.map e.hom) ≫ β.app K ≫ Q.map (P.map e.inv ≫ w ≫ r) =
      (β.app M₀ ≫ Q.map w) ≫ Q.map r := by
  have h : G.map (F.map e.hom) ≫ β.app K = β.app M₀ ≫ Q.map (P.map e.hom) := β.naturality e.hom
  rw [← Category.assoc, h, Category.assoc, ← Q.map_comp, map_hom_comp_map_inv_comp P e,
    Q.map_comp, Category.assoc]

end Abstract

/-! ### The transpose of the derived base change map against the ordinary data -/

section RingedSpaces

open Stacks.Cohomology.DerivedBaseChange Stacks.DerivedPullback.Composition

variable {X' X S' S : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)

/-- **The transpose of the derived base change map of a commutative square of ringed spaces**,
under the derived adjunction along the bottom of the square: it is the derived pushforward along
`f` of the derived unit of `Lg'^* ⊣ Rg'_*`, followed by the comparison of the two iterated
derived pushforwards. -/
theorem homEquiv_derivedBaseChangeSquare_app
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (derivedAdjunction g).homEquiv _ _ ((derivedBaseChangeSquare g' f' f g sq).app K) =
      (derivedPushforward f).map ((derivedAdjunction g').unit.app K) ≫
        (Mate.derivedPushforwardComparisonSquare (derivedAdjunction f) (derivedAdjunction f')
            (derivedAdjunction g) (derivedAdjunction g')
            (derivedPullbackCompIsoLeft g' f' f g sq)
            (derivedPullbackCompIsoCanonical g' f)).app ((derivedPullback g').obj K) :=
  (congrArg (fun x => (derivedAdjunction g).homEquiv _ _ x)
      (derivedBaseChangeSquare_app_eq g' f' f g sq K)).trans
    (Mate.derivedBaseChangeMap_homEquiv (derivedAdjunction f) (derivedAdjunction f')
      (derivedAdjunction g) (derivedAdjunction g') (derivedPullbackCompIsoLeft g' f' f g sq)
      (derivedPullbackCompIsoCanonical g' f) K)

/-- **The two comparisons of the iterated pushforwards agree, with the derived side written as
one transposed morphism.** The comparison `Q(f_* M) ⟶ Rf_*(Q M)`, followed by the transpose along
the bottom of the square of

> `Lg^*(Rf_* (Q M)) ⟶ Rf'_*(Lg'^*(Q M)) ⟶ Rf'_*(Q((g')^* M))`

— the derived base change map of [Stacks, Tag 08HY] and the derived pushforward of the
derived-pullback comparison — is the route of the **degreewise** units of [Stacks, Tag 0096]: the
degreewise unit of `g^* ⊣ g_*`, the comparison `Q(g^*(f_* M)) ⟶ Rg_*(Q(g^*(f_* M)))`, and `Rg_*`
of the ordinary base change map and of the comparison `Q(f'_*((g')^* M)) ⟶ Rf'_*(Q((g')^* M))`.
-/
theorem derivedPushforwardUnit_comp_homEquiv_fac
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :
    (derivedPushforwardUnit f).app M ≫
        (derivedAdjunction g).homEquiv _ _
          ((derivedBaseChangeSquare g' f' f g sq).app (DerivedCategory.Qh.obj M) ≫
            (derivedPushforward f').map ((derivedPullbackComparison g').app M)) =
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
  ((derivedPushforwardUnit f).app M ≫=
      homEquiv_comp_eq (derivedAdjunction g)
        ((derivedBaseChangeSquare g' f' f g sq).app (DerivedCategory.Qh.obj M))
        ((derivedPushforward f').map ((derivedPullbackComparison g').app M))
        (homEquiv_derivedBaseChangeSquare_app g' f' f g sq
          (DerivedCategory.Qh.obj M))).trans
    (derivedPushforwardComparison_fac g' f' f g sq M)

/-- **The transposed derived base change composite, transported along an isomorphism
`Q M ≅ K` and a trailing map.** Read at `K` rather than at `Q M`, and with the derived-pullback
comparison extended by an arbitrary `r : Q((g')^* M) ⟶ N`, the transpose differs from the one at
`Q M` by the derived pushforward of `e.hom` in front and by `Rg_*(Rf'_*(r))` behind. -/
theorem map_hom_comp_homEquiv_derivedBaseChangeSquare
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (e : DerivedCategory.Qh.obj M ≅ K)
    {N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    (r : DerivedCategory.Qh.obj
      (((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ⟶ N) :
    (derivedPushforward f).map e.hom ≫
        (derivedAdjunction g).homEquiv _ _
          ((derivedBaseChangeSquare g' f' f g sq).app K ≫
            (derivedPushforward f').map ((derivedPullback g').map e.inv ≫
              (derivedPullbackComparison g').app M ≫ r)) =
      (derivedAdjunction g).homEquiv _ _
          ((derivedBaseChangeSquare g' f' f g sq).app (DerivedCategory.Qh.obj M) ≫
            (derivedPushforward f').map ((derivedPullbackComparison g').app M)) ≫
        (derivedPushforward g).map ((derivedPushforward f').map r) :=
  Eq.trans
    (Adjunction.homEquiv_naturality_left (derivedAdjunction g)
      ((derivedPushforward f).map e.hom) _).symm
    (Eq.trans
      (congrArg (fun x => (derivedAdjunction g).homEquiv _ _ x)
        (map_hom_comp_app_comp_map (derivedBaseChangeSquare g' f' f g sq) e
          ((derivedPullbackComparison g').app M) r))
      (Adjunction.homEquiv_naturality_right (derivedAdjunction g) _ _))

/-- **The two comparisons of the iterated pushforwards agree, at an arbitrary presentation of the
object and with an arbitrary trailing map.** The comparison `Q(f_* M) ⟶ Rf_*(Q M)`, the derived
pushforward of an isomorphism `Q M ≅ K`, and the transpose along the bottom of the derived base
change map at `K` followed by `Rf'_*` of the derived-pullback comparison extended by `r`, compose
to the route of the degreewise units of [Stacks, Tag 0096] followed by `Rg_*(Rf'_*(r))`. -/
theorem derivedPushforwardUnit_comp_map_hom_comp_homEquiv_fac
    (M : HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (e : DerivedCategory.Qh.obj M ≅ K)
    {N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    (r : DerivedCategory.Qh.obj
      (((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ⟶ N) :
    (derivedPushforwardUnit f).app M ≫
        (derivedPushforward f).map e.hom ≫
        (derivedAdjunction g).homEquiv _ _
          ((derivedBaseChangeSquare g' f' f g sq).app K ≫
            (derivedPushforward f').map ((derivedPullback g').map e.inv ≫
              (derivedPullbackComparison g').app M ≫ r)) =
      DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction g).unit.app
          (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) ≫
        (derivedPushforwardUnit g).app
          (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) ≫
        (derivedPushforward g).map
          (DerivedCategory.Qh.map ((homotopyBaseChangeSquare g' f' f g sq).app M)) ≫
        (derivedPushforward g).map
          ((derivedPushforwardUnit f').app
            (((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) ≫
        (derivedPushforward g).map ((derivedPushforward f').map r) :=
  ((derivedPushforwardUnit f).app M ≫=
      map_hom_comp_homEquiv_derivedBaseChangeSquare g' f' f g sq M e r).trans
    (comp_comp_tail (derivedPushforwardUnit_comp_homEquiv_fac g' f' f g sq M)
      ((derivedPushforward g).map ((derivedPushforward f').map r)))

/-- **The transposed derived base change composite at a K-injective complex.** For a K-injective
complex `I`, the derived pushforward of an isomorphism `Q [I] ≅ K` followed by the transpose
along the bottom of the derived base change map at `K` and of `Rf'_*` of the derived-pullback
comparison extended by `r` is the inverse of the comparison `Q(f_* [I]) ⟶ Rf_*(Q [I])` followed
by the route of the degreewise units of [Stacks, Tag 0096] and by `Rg_*(Rf'_*(r))`. -/
theorem map_hom_comp_homEquiv_derivedBaseChangeSquare_eq_inv_comp
    (I : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (hI : I.IsKInjective)
    {K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    (e : DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
        (ComplexShape.up ℤ)).obj I) ≅ K)
    {N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    (r : DerivedCategory.Qh.obj
      (((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
          (ComplexShape.up ℤ)).obj I)) ⟶ N) :
    (derivedPushforward f).map e.hom ≫
        (derivedAdjunction g).homEquiv _ _
          ((derivedBaseChangeSquare g' f' f g sq).app K ≫
            (derivedPushforward f').map ((derivedPullback g').map e.inv ≫
              (derivedPullbackComparison g').app
                ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
                  (ComplexShape.up ℤ)).obj I) ≫ r)) =
      haveI := isIso_derivedPushforwardUnit_app_of_isKInjective f I hI
      inv ((derivedPushforwardUnit f).app
          ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
            (ComplexShape.up ℤ)).obj I)) ≫
        DerivedCategory.Qh.map ((homotopyPullbackPushforwardAdjunction g).unit.app
            (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
                (ComplexShape.up ℤ)).obj I))) ≫
          (derivedPushforwardUnit g).app
            (((modulePullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj
              (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
                ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
                  (ComplexShape.up ℤ)).obj I))) ≫
          (derivedPushforward g).map
            (DerivedCategory.Qh.map ((homotopyBaseChangeSquare g' f' f g sq).app
              ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
                (ComplexShape.up ℤ)).obj I))) ≫
          (derivedPushforward g).map
            ((derivedPushforwardUnit f').app
              (((modulePullback g').mapHomotopyCategory (ComplexShape.up ℤ)).obj
                ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
                  (ComplexShape.up ℤ)).obj I))) ≫
          (derivedPushforward g).map ((derivedPushforward f').map r) :=
  have := isIso_derivedPushforwardUnit_app_of_isKInjective f I hI
  (IsIso.eq_inv_comp _).2
    (derivedPushforwardUnit_comp_map_hom_comp_homEquiv_fac g' f' f g sq _ e r)

end RingedSpaces

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
