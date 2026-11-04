module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OrdinaryTopDegreeBaseChange
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedModelCrossingNaturality

/-!
# The transposed derived base change composite, through the ordinary unit

`…TopDegreeBaseChange.derivedPushforwardUnit_comp_map_hom_comp_homEquiv_fac` computes the
transpose along the bottom of the square of the two-step derived composite that the canonical map
`γ⁺` of [Stacks, Tag 0EX3] (c) displays, via
`Stacks.Cohomology.DerivedBaseChange.derivedPushforwardComparison_fac`; that identity determines
the transpose only after the comparison `Q(f_* M) ⟶ Rf_*(Q M)`, which is not invertible. At the
single complex `F'[0]` the degree-`d` cohomology of that comparison is taken at the zero object
(`…TopDegreeBaseChange.isZero_homologyFunctor_pushforwardToDerivedCategory_single_of_ne_zero`), so
nothing about the transpose follows from it in the degree of the tag.

This file computes the same transpose with **no comparison in front of it**. The route is the
mate identity rather than the degreewise factorisation: by
`…TopDegreeBaseChange.homEquiv_derivedBaseChangeSquare_app` the transpose of the derived base
change map is the derived pushforward along `f` of the **derived unit** of `Lg'^* ⊣ Rg'_*`
followed by the comparison of the two iterated derived pushforwards, and that comparison is a
conjugate of the comparison of the two iterated derived pullbacks
(`Stacks.Cohomology.DerivedBaseChange.derivedPushforwardComparisonSquare_eq_conjugateEquiv`),
hence an isomorphism. So the transpose is determined, for an arbitrary commutative square and
with nothing assumed about the object, as

> `Rf_*(η) ≫ (comparison of the two iterated derived pushforwards)`,

with `η` the derived unit followed by `Rg'_*` of the trailing map.

The derived unit is then removed at a single complex. `derivedToOrdinaryPullbackSingle` is the
derived-pullback comparison conjugated by the identifications of the single functors, and
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_unit_fac` says that the
derived unit followed by `Rg'_*` of that comparison is the **ordinary** unit of `(g')^* ⊣ (g')_*`
on complexes followed by the comparison `Q((g')_* K) ⟶ R(g')_*(Q K)`. So at `F'[0]` the whole
transpose is written through the ordinary unit of [Stacks, Tag 0096], and no derived base change
map, no derived unit and no inverted comparison is left in it.

## Main results

* `…TopDegreeBaseChange.homEquiv_comp_map_eq_map_comp_app`: the rearrangement, at variables of
  abstract categories — a transpose whose value is known as `G(u) ≫ β` acquires a trailing
  factor by the naturality of `β`.
* `…TopDegreeBaseChange.map_comp_app_comp_map_eq`: the trailing map carried across such a `β` and
  folded into the leading factor, at variables.
* `…TopDegreeBaseChange.unit_comp_map_comp_comp`: the companion rearrangement for a unit followed
  by the right adjoint of a three-fold composite whose first factor is the left adjoint of a
  morphism, at variables.
* `…TopDegreeBaseChange.homEquiv_derivedBaseChangeSquare_comp`: **the transpose of the derived
  base change map extended by an arbitrary trailing map, with no comparison in front.** For a
  commutative square of ringed spaces, an object `K` of `D(𝒪_X)` and any
  `c : Lg'^* K ⟶ N`, the transpose along the bottom of
  `(derivedBaseChangeSquare …).app K ≫ Rf'_*(c)` is the derived pushforward along `f` of the
  derived unit of `Lg'^* ⊣ Rg'_*` followed by `Rg'_*(c)`, and then the comparison of the two
  iterated derived pushforwards at `N`.
* `…TopDegreeBaseChange.derivedAdjunction_unit_comp_map_derivedToOrdinaryPullbackSingle`: **the
  derived unit followed by the comparison from derived to ordinary pullback at a single complex is
  the ordinary unit.** The identification of the two single functors, the degreewise unit of
  `(g')^* ⊣ (g')_*` of [Stacks, Tag 0096], the comparison `Q((g')_* K) ⟶ R(g')_*(Q K)`, and the
  two remaining identifications of the single functors.
* `…TopDegreeBaseChange.homEquiv_derivedBaseChangeSquare_comp_right`: the same transpose with the
  trailing map carried past the comparison instead of through it, so that it occurs only inside
  `Rg_*(Rf'_*(-))`.
* `…TopDegreeBaseChange.homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv_app`: the
  transpose of `γ⁺` with the derived base change map written as a component of the base change
  two-square rather than through its wrapper.
* `…TopDegreeBaseChange.homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv_eq_mate`: **the
  transpose of `γ⁺` with no derived base change map in it**, and nothing in front of it — the
  derived pushforward along `f'` of the derived unit of `Lh'^* ⊣ Rh'_*`, the comparison of the two
  iterated derived pushforwards, and `Rh_*(Rf''_*)` of the comparison from derived to ordinary
  pullback, then the cohomology edge morphism and `h_*` of the crossing at `f''`. Its two
  companions `…_app_of_eq` and `…map_homEquiv_comp_eq_map_mate` are the two halves it composes.

## Implementation notes

The identity of `…TopDegreeBaseChange.derivedPushforwardUnit_comp_map_hom_comp_homEquiv_fac`
factors the transpose through `Q(f_* M) ⟶ Rf_*(Q M)`, being an identity of morphisms out of
`Q(f_* M)`. The mate identity used here is an identity of morphisms out of `Rf_*(K)` itself, so no
such factor appears; the right-hand side instead keeps the comparison of the two iterated derived
pushforwards, which is an isomorphism.

At the square underlying a top-degree base-change situation, the comparison from derived to
ordinary pullback and the base change map enter the statements as variables carrying their
defining equations, each discharged by `rfl`.

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

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The two rearrangements, on variables -/

section Abstract

variable {𝒞 𝒟 ℰ ℱ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ] [Category ℱ]

/-- **A transpose whose value is known acquires a trailing factor by naturality.** For an
adjunction `L ⊣ R`, functors `F : ℱ ⥤ ℰ`, `G : ℰ ⥤ 𝒞` and `P : ℱ ⥤ 𝒟` and a natural
transformation `β : F ⋙ G ⟶ P ⋙ R`, if the transpose of `x : L(G K) ⟶ P N₀` is `G(u) ≫ β` at
`N₀`, then the transpose of `x ≫ P(c)` is `G(u ≫ F(c)) ≫ β` at `N`. -/
theorem homEquiv_comp_map_eq_map_comp_app {L : 𝒞 ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} (adj : L ⊣ R)
    {F : ℱ ⥤ ℰ} {G : ℰ ⥤ 𝒞} {P : ℱ ⥤ 𝒟} (β : F ⋙ G ⟶ P ⋙ R) {K : ℰ} {N₀ N : ℱ}
    (u : K ⟶ F.obj N₀) (c : N₀ ⟶ N) {x : L.obj (G.obj K) ⟶ P.obj N₀}
    (hx : adj.homEquiv (G.obj K) (P.obj N₀) x = G.map u ≫ β.app N₀) :
    adj.homEquiv (G.obj K) (P.obj N) (x ≫ P.map c) = G.map (u ≫ F.map c) ≫ β.app N := by
  rw [Adjunction.homEquiv_naturality_right, hx, G.map_comp, Category.assoc,
    Category.assoc]
  exact G.map u ≫= (β.naturality c).symm

/-- **A unit followed by the right adjoint of a three-fold composite whose first factor is the
left adjoint of a morphism.** The naturality of the unit moves that morphism out in front, and
the value of the unit followed by the right adjoint of the second factor is then substituted. -/
theorem unit_comp_map_comp_comp {L : 𝒞 ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞} (adj : L ⊣ R) {K K' Z : 𝒞} {B B' : 𝒟}
    (w : K ⟶ K') {m : L.obj K' ⟶ B} {p : K' ⟶ Z} {q : Z ⟶ R.obj B}
    (hf : adj.unit.app K' ≫ R.map m = p ≫ q) (t : B ⟶ B') :
    adj.unit.app K ≫ R.map (L.map w ≫ m ≫ t) = w ≫ p ≫ q ≫ R.map t := by
  have h₁ : adj.unit.app K ≫ R.map (L.map w) = w ≫ adj.unit.app K' :=
    (adj.unit.naturality w).symm
  have h₂ : adj.unit.app K ≫ R.map (L.map w ≫ m) = w ≫ p ≫ q := by
    rw [R.map_comp, ← Category.assoc, h₁, Category.assoc, hf]
  rw [show L.map w ≫ m ≫ t = (L.map w ≫ m) ≫ t from (Category.assoc _ _ _).symm, R.map_comp,
    ← Category.assoc, h₂]
  simp only [Category.assoc]

/-- **Substituting for the morphism a functor is applied to, in front of a trailing factor.**
If `x = y` then `G(x) ≫ t = G(y) ≫ t`. -/
theorem map_comp_congr (G : 𝒟 ⥤ 𝒞) {A B : 𝒟} {x y : A ⟶ B} (h : x = y) {Z : 𝒞}
    (t : G.obj B ⟶ Z) : G.map x ≫ t = G.map y ≫ t := by rw [h]

/-- **The trailing map carried across a natural transformation between composite functors, folded
into the leading factor.** For `β : F ⋙ G ⟶ P ⋙ R`, if `u ≫ F(c) = w` then
`G(u) ≫ β ≫ R(P(c))` is `G(w) ≫ β` read at the other end. -/
theorem map_comp_app_comp_map_eq {F : ℱ ⥤ ℰ} {G : ℰ ⥤ 𝒞} {P : ℱ ⥤ 𝒟} {R : 𝒟 ⥤ 𝒞}
    (β : F ⋙ G ⟶ P ⋙ R) {K : ℰ} {N₀ N : ℱ} (u : K ⟶ F.obj N₀) (c : N₀ ⟶ N) {w : K ⟶ F.obj N}
    (hw : u ≫ F.map c = w) :
    G.map u ≫ β.app N₀ ≫ R.map (P.map c) = G.map w ≫ β.app N := by
  rw [← hw, G.map_comp, Category.assoc]
  exact G.map u ≫= (β.naturality c).symm

/-- **A trailing map pulled out through a natural transformation between composite functors.**
For `ν : Pp ⋙ Qb ⟶ Qa ⋙ Rr`, the component of `ν` followed by `Rr` of a composite beginning with
`Qa(s)` is `Qb(Pp(s))` followed by the component at the other end and by `Rr` of the rest. -/
theorem app_comp_map_comp_map {K₀ K₁ D₀ D₁ : Type*} [Category K₀] [Category K₁] [Category D₀]
    [Category D₁] {Pp : K₀ ⥤ K₁} {Qb : K₁ ⥤ D₁} {Qa : K₀ ⥤ D₀} {Rr : D₀ ⥤ D₁}
    (ν : Pp ⋙ Qb ⟶ Qa ⋙ Rr) {X Y : K₀} (s : X ⟶ Y) {Z : D₀} (z : Qa.obj Y ⟶ Z) :
    ν.app X ≫ Rr.map (Qa.map s ≫ z) = Qb.map (Pp.map s) ≫ ν.app Y ≫ Rr.map z := by
  rw [Rr.map_comp]
  exact (ν.naturality_assoc s _).symm

/-- **A two-fold composite solved for, against a retraction.** From `a ≫ b ≫ u = c` and
`u ≫ v = 𝟙` one gets `a ≫ b = c ≫ v`. -/
theorem comp_eq_comp_of_comp_comp_eq {A B C' D' : 𝒞} (a : A ⟶ B) (b : B ⟶ C')
    {u : C' ⟶ D'} {v : D' ⟶ C'} (huv : u ≫ v = 𝟙 C') {c : A ⟶ D'} (h : a ≫ b ≫ u = c) :
    a ≫ b = c ≫ v := by
  rw [← h, Category.assoc, Category.assoc, huv, Category.comp_id]

/-- **Two consecutive functor images merged, substituted and split again.** From
`x ≫ y = x' ≫ y'` one gets `G(x) ≫ G(y) ≫ t = G(x') ≫ G(y') ≫ t`. -/
theorem map_comp_map_comp_eq_split (G : 𝒟 ⥤ 𝒞) {A B C₁ C₂ : 𝒟} (x : A ⟶ B) (y : B ⟶ C₂)
    {x' : A ⟶ C₁} {y' : C₁ ⟶ C₂} (h : x ≫ y = x' ≫ y') {W : 𝒞} (t : G.obj C₂ ⟶ W) :
    G.map x ≫ G.map y ≫ t = G.map x' ≫ G.map y' ≫ t := by
  rw [← Category.assoc, ← G.map_comp, h, G.map_comp, Category.assoc]

/-- **Splitting a composite inside two nested functor images, in front of a trailing map.**
`H(G(x ≫ y) ≫ m) ≫ t = H(G x) ≫ H(G y ≫ m) ≫ t`. -/
theorem map_map_comp_split (G : 𝒟 ⥤ 𝒞) (H : 𝒞 ⥤ ℰ) {A B C' : 𝒟} (x : A ⟶ B) (y : B ⟶ C')
    {Z : 𝒞} (m : G.obj C' ⟶ Z) {W : ℰ} (t : H.obj Z ⟶ W) :
    H.map (G.map (x ≫ y) ≫ m) ≫ t = H.map (G.map x) ≫ H.map (G.map y ≫ m) ≫ t := by
  rw [G.map_comp, Category.assoc, H.map_comp, Category.assoc]

/-- **A morphism determined after an isomorphism, against a naturality square.** If
`x ≫ cG.hom = cF.hom ≫ rh` and `cF.hom ≫ g = x ≫ rr`, then `g = rh ≫ cG.inv ≫ rr`. -/
theorem eq_of_iso_hom_comp_eq {A B C' D' Z : 𝒞} (cF : A ≅ B) (cG : C' ≅ D') {g : B ⟶ Z}
    {x : A ⟶ C'} {rr : C' ⟶ Z} {rh : B ⟶ D'} (hnat : x ≫ cG.hom = cF.hom ≫ rh)
    (hs : cF.hom ≫ g = x ≫ rr) : g = rh ≫ cG.inv ≫ rr := by
  have hx : x = cF.hom ≫ rh ≫ cG.inv := by
    rw [← Category.assoc, ← hnat, Category.assoc, cG.hom_inv_id, Category.comp_id]
  rw [hx, Category.assoc, Category.assoc] at hs
  exact (cancel_epi cF.hom).mp hs

/-- **A leading component moved past a functor image, by naturality.** For `α : L ⟶ M₁ ⋙ N`, the
component of `α` followed by `N(M₁(w))` and a trailing map is `L(w)` followed by the component at
the other end and the trailing map. -/
theorem app_comp_map_comp {A₀ B₀ C₀ : Type*} [Category A₀] [Category B₀] [Category C₀]
    {L : A₀ ⥤ C₀} {M₁ : A₀ ⥤ B₀} {N : B₀ ⥤ C₀} (α : L ⟶ M₁ ⋙ N) {X Y : A₀} (w : X ⟶ Y)
    {Z : C₀} (z : N.obj (M₁.obj Y) ⟶ Z) :
    α.app X ≫ N.map (M₁.map w) ≫ z = L.map w ≫ α.app Y ≫ z :=
  (α.naturality_assoc w z).symm

end Abstract

/-! ### The unit of the induced adjunction at a single complex -/

section SingleUnit

variable {C₁ C₂ : Type*} [Category C₁] [Category C₂] [Abelian C₁] [Abelian C₂]
  {P : C₁ ⥤ C₂} {Q : C₂ ⥤ C₁} [P.Additive] [Q.Additive]

/-- **The unit of the induced adjunction on homotopy categories, at a single complex, is the unit
of the original adjunction.** Conjugating the unit of
`CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction` at
`CategoryTheory.HomotopyCategory.singleFunctor C₂ n` by the two identifications
`CategoryTheory.Functor.mapHomotopyCategorySingleFunctor` of the single functor with `Q` and with
`P` returns the single functor applied to the unit at the object. -/
theorem mapHomotopyCategoryAdjunction_unit_app_singleFunctor (adj : Q ⊣ P) (n : ℤ) (M : C₂) :
    (Adjunction.mapHomotopyCategoryAdjunction adj (ComplexShape.up ℤ)).unit.app
          ((HomotopyCategory.singleFunctor C₂ n).obj M) ≫
        (P.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((Q.mapHomotopyCategorySingleFunctor n).hom.app M) ≫
        (P.mapHomotopyCategorySingleFunctor n).hom.app (Q.obj M) =
      (HomotopyCategory.singleFunctor C₂ n).map (adj.unit.app M) := by
  have h := congrArg (HomotopyCategory.quotient C₂ (ComplexShape.up ℤ)).map
    (Adjunction.mapHomologicalComplexAdjunction_unit_app_single adj (ComplexShape.up ℤ) n M)
  rw [Functor.map_comp, Functor.map_comp] at h
  rw [mapHomotopyCategorySingleFunctor_hom_app_eq (T := Q) n M,
    mapHomotopyCategorySingleFunctor_hom_app_eq (T := P) n (Q.obj M)]
  exact h

end SingleUnit

/-! ### The transpose, with no comparison in front -/

section RingedSpaces

open Stacks.Cohomology.DerivedBaseChange Stacks.DerivedPullback.Composition
open DerivedCategory

variable {X' X S' S : RingedSpace.{u, u}}
  (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S) (sq : g' ≫ f = f' ≫ g)

/-- **The transpose along the bottom of the derived base change map extended by an arbitrary
trailing map, with no comparison in front of it.** For a commutative square of ringed spaces, an
object `K` of `D(𝒪_X)` and any `c : Lg'^*(K) ⟶ N`, the transpose under `Lg^* ⊣ Rg_*` of

> `Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K) ⟶ Rf'_*(N)`

— the derived base change map of [Stacks, Tag 08HY] followed by `Rf'_*(c)` — is the derived
pushforward along `f` of the derived unit of `Lg'^* ⊣ Rg'_*` followed by `Rg'_*(c)`, and then the
comparison of the two iterated derived pushforwards at `N`.

Nothing stands in front of the left-hand side: unlike
`…TopDegreeBaseChange.derivedPushforwardUnit_comp_map_hom_comp_homEquiv_fac`, which factors the
transpose through the comparison `Q(f_* M) ⟶ Rf_*(Q M)` and therefore says nothing where that
comparison's cohomology vanishes, this determines the transpose itself. The comparison of the two
iterated derived pushforwards that remains on the right is an isomorphism, by
`Stacks.Cohomology.DerivedBaseChange.derivedPushforwardComparisonSquare_eq_conjugateEquiv`. -/
theorem homEquiv_derivedBaseChangeSquare_comp
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    (c : (derivedPullback g').obj K ⟶ N) :
    (derivedAdjunction g).homEquiv _ _
        ((derivedBaseChangeSquare g' f' f g sq).app K ≫ (derivedPushforward f').map c) =
      (derivedPushforward f).map
          ((derivedAdjunction g').unit.app K ≫ (derivedPushforward g').map c) ≫
        (Mate.derivedPushforwardComparisonSquare (derivedAdjunction f) (derivedAdjunction f')
            (derivedAdjunction g) (derivedAdjunction g')
            (derivedPullbackCompIsoLeft g' f' f g sq)
            (derivedPullbackCompIsoCanonical g' f)).app N :=
  homEquiv_comp_map_eq_map_comp_app (derivedAdjunction g)
    (Mate.derivedPushforwardComparisonSquare (derivedAdjunction f) (derivedAdjunction f')
      (derivedAdjunction g) (derivedAdjunction g') (derivedPullbackCompIsoLeft g' f' f g sq)
      (derivedPullbackCompIsoCanonical g' f))
    ((derivedAdjunction g').unit.app K) c
    (homEquiv_derivedBaseChangeSquare_app g' f' f g sq K)

/-- **The derived unit followed by the comparison from derived to ordinary pullback, at a single
complex, is the ordinary unit.** For a morphism of ringed spaces `k`, a sheaf of modules `M` and a
degree `d`, the derived unit of `Lk^* ⊣ Rk_*` at `M[-d]` followed by `Rk_*` of
`…TopDegreeBaseChange.derivedToOrdinaryPullbackSingle` is the identification of the two single
functors, the **ordinary** unit of `k^* ⊣ k_*` of [Stacks, Tag 0096] on complexes, the comparison
`Q(k_*(k^* M)[-d]) ⟶ Rk_*(Q((k^* M)[-d]))`, and the two remaining identifications of the single
functors. -/
theorem derivedAdjunction_unit_comp_map_derivedToOrdinaryPullbackSingle {A B : RingedSpace.{u, u}}
    (k : A ⟶ B) (M : SheafOfModules.{u} (structureSheafRing B)) (d : ℤ) :
    (derivedAdjunction k).unit.app
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing B)) d).obj M) ≫
        (derivedPushforward k).map (derivedToOrdinaryPullbackSingle k M d) =
      (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing B)) d).hom.app M ≫
        Qh.map ((homotopyPullbackPushforwardAdjunction k).unit.app
            ((HomotopyCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing B)) d).obj M)) ≫
          (derivedPushforwardUnit k).app
            (((modulePullback k).mapHomotopyCategory (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.singleFunctor
                (SheafOfModules.{u} (structureSheafRing B)) d).obj M)) ≫
          (derivedPushforward k).map
            (Qh.map ((Functor.mapHomotopyCategorySingleFunctor (modulePullback k) d).hom.app M) ≫
              (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing A)) d).inv.app
                ((modulePullback k).obj M)) := by
  rw [derivedToOrdinaryPullbackSingle_eq_comp]
  exact unit_comp_map_comp_comp (derivedAdjunction k) _
    (derivedAdjunction_unit_fac k
      ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing B)) d).obj M)) _

/-- **The same transpose with the trailing map carried past the comparison.** For a commutative
square of ringed spaces, an object `K` and any `c : Lg'^*(K) ⟶ N`, the transpose along the bottom
of the derived base change map followed by `Rf'_*(c)` is the derived pushforward along `f` of the
derived unit, the comparison of the two iterated derived pushforwards at `Lg'^*(K)`, and
`Rg_*(Rf'_*(c))`. -/
theorem homEquiv_derivedBaseChangeSquare_comp_right
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    {N : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    (c : (derivedPullback g').obj K ⟶ N) :
    (derivedAdjunction g).homEquiv _ _
        ((derivedBaseChangeSquare g' f' f g sq).app K ≫ (derivedPushforward f').map c) =
      (derivedPushforward f).map ((derivedAdjunction g').unit.app K) ≫
        (Mate.derivedPushforwardComparisonSquare (derivedAdjunction f) (derivedAdjunction f')
            (derivedAdjunction g) (derivedAdjunction g')
            (derivedPullbackCompIsoLeft g' f' f g sq)
            (derivedPullbackCompIsoCanonical g' f)).app
            ((derivedPullback g').obj K) ≫
          (derivedPushforward g).map ((derivedPushforward f').map c) :=
  homEquiv_comp_eq (derivedAdjunction g)
    ((derivedBaseChangeSquare g' f' f g sq).app K) ((derivedPushforward f').map c)
    (homEquiv_derivedBaseChangeSquare_app g' f' f g sq K)

end RingedSpaces

/-! ### The ordinary unit of [Stacks, Tag 0096] in front -/

section SingleUnitRingedSpace

open DerivedCategory

variable {A B : RingedSpace.{u, u}} (k : A ⟶ B)
  (M : SheafOfModules.{u} (structureSheafRing B)) (d : ℤ)

/-- **The comparison of the two models of `Rk_*` absorbs the identification of the single
functors.** The component of `…DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit` at the
degreewise pullback of a single complex, followed by `Rk_*` of a composite beginning with the
identification of the two single functors along `k^*`, is that identification carried by the
degreewise direct image followed by the component at the single complex. -/
theorem derivedPushforwardUnit_app_comp_map_single :
    (derivedPushforwardUnit k).app
          (((modulePullback k).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.singleFunctor
                  (SheafOfModules.{u} (structureSheafRing B)) d).obj M)) ≫
        (derivedPushforward k).map
          (Qh.map ((Functor.mapHomotopyCategorySingleFunctor (modulePullback k) d).hom.app M) ≫
            (singleFunctorIsoCompQh
                  (SheafOfModules.{u} (structureSheafRing A)) d).inv.app
              ((modulePullback k).obj M)) =
      Qh.map (((modulePushforward k).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((Functor.mapHomotopyCategorySingleFunctor (modulePullback k) d).hom.app M)) ≫
        (derivedPushforwardUnit k).app
            ((HomotopyCategory.singleFunctor
                  (SheafOfModules.{u} (structureSheafRing A)) d).obj ((modulePullback k).obj M)) ≫
          (derivedPushforward k).map
            ((singleFunctorIsoCompQh
                  (SheafOfModules.{u} (structureSheafRing A)) d).inv.app
              ((modulePullback k).obj M)) :=
  app_comp_map_comp_map (derivedPushforwardUnit k) _ _

/-- **The homotopy-category unit at a single complex, carried by the degreewise direct image of
the identification along `k^*`, is the single functor of the ordinary unit.** This is
`mapHomotopyCategoryAdjunction_unit_app_singleFunctor` at the degreewise adjunction
`k^* ⊣ k_*` of [Stacks, Tag 0096], solved for the two-fold composite against the identification
of the single functors along `k_*`. -/
theorem homotopyUnit_app_single_comp_map :
    (homotopyPullbackPushforwardAdjunction k).unit.app
          ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing B)) d).obj M) ≫
        ((modulePushforward k).mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((Functor.mapHomotopyCategorySingleFunctor (modulePullback k) d).hom.app M) =
      (HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing B)) d).map
          ((modulePullbackPushforwardAdjunction k).unit.app M) ≫
        (Functor.mapHomotopyCategorySingleFunctor (modulePushforward k) d).inv.app
          ((modulePullback k).obj M) :=
  comp_eq_comp_of_comp_comp_eq _ _
    ((Functor.mapHomotopyCategorySingleFunctor (modulePushforward k) d).hom_inv_id_app _)
    (mapHomotopyCategoryAdjunction_unit_app_singleFunctor
      (modulePullbackPushforwardAdjunction k) d M)

/-- **The derived transpose of the derived-to-ordinary pullback comparison is the ordinary unit of
[Stacks, Tag 0096] placed in degree `-d`, followed by the comparison of the two models of
`Rk_*`.** The derived unit of `Lk^* ⊣ Rk_*` at `M[-d]` followed by `Rk_*` of
`…TopDegreeBaseChange.derivedToOrdinaryPullbackSingle` is

> `M[-d] ⟶ (k_* k^* M)[-d] ⟶ Rk_*((k^* M)[-d])`,

the single functor applied to the **ordinary** unit `M ⟶ k_*(k^* M)`, followed by the
identification of the two single functors, the identification of the single functors along `k_*`
inverted, the comparison `Q(K) ⟶ Rk_*(Q K)` at the single complex on `k^* M`, and the
identification of the two single functors inverted. -/
theorem derivedAdjunction_unit_comp_map_derivedToOrdinary_eq_single_unit :
    (derivedAdjunction k).unit.app ((singleFunctor
          (SheafOfModules.{u} (structureSheafRing B)) d).obj M) ≫
        (derivedPushforward k).map (derivedToOrdinaryPullbackSingle k M d) =
      (singleFunctor (SheafOfModules.{u} (structureSheafRing B)) d).map
          ((modulePullbackPushforwardAdjunction k).unit.app M) ≫
        (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing B)) d).hom.app
            ((modulePushforward k).obj ((modulePullback k).obj M)) ≫
          Qh.map ((Functor.mapHomotopyCategorySingleFunctor (modulePushforward k) d).inv.app
              ((modulePullback k).obj M)) ≫
            (derivedPushforwardUnit k).app
                ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing A)) d).obj
                  ((modulePullback k).obj M)) ≫
              (derivedPushforward k).map
                ((singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing A)) d).inv.app
                  ((modulePullback k).obj M)) :=
  (derivedAdjunction_unit_comp_map_derivedToOrdinaryPullbackSingle k M d).trans
    (Eq.trans
      ((singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing B)) d).hom.app M ≫=
        (Qh.map ((homotopyPullbackPushforwardAdjunction k).unit.app
            ((HomotopyCategory.singleFunctor
                  (SheafOfModules.{u} (structureSheafRing B)) d).obj M)) ≫=
          derivedPushforwardUnit_app_comp_map_single k M d))
      (Eq.trans
        ((singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing B)) d).hom.app M ≫=
          map_comp_map_comp_eq_split Qh _ _ (homotopyUnit_app_single_comp_map k M d) _)
        (app_comp_map_comp (singleFunctorIsoCompQh
              (SheafOfModules.{u} (structureSheafRing B)) d).hom
          ((modulePullbackPushforwardAdjunction k).unit.app M) _)))

end SingleUnitRingedSpace

/-! ### The transpose of `γ⁺` through the ordinary unit -/

section Card

open Stacks.Cohomology.DerivedBaseChange Stacks.DerivedPullback.Composition
open DerivedCategory

variable {X'' Y'' : Scheme.{u}}
  (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (F' : S.X'.Modules) [F'.IsQuasicoherent]
  (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
  (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
    = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom)

/-- **The transpose of `γ⁺`, with the derived base change map written as a component of the base
change two-square.** This is
`…TopDegreeBaseChange.homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv` with the wrapper
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap` exchanged for the component of
`Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeSquare`. -/
theorem homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv_app :
    (homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ)).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
          (topDirectImageBaseChangeMapPlus S F' h' f'' h sq) =
      (homologyFunctor S.Y'.Modules (S.d : ℤ)).map
          ((derivedAdjunction h.toLRSHom.toShHom).homEquiv _ _
            ((derivedBaseChangeSquare h'.toLRSHom.toShHom f''.toLRSHom.toShHom
                  S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq).app
                ((singleFunctor S.X'.Modules 0).obj F') ≫
              (derivedPushforward f''.toLRSHom.toShHom).map
                (derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F' 0))) ≫
        (derivedPushforwardHomologyComparison h.toLRSHom.toShHom (S.d : ℤ)).app
          ((derivedPushforward f''.toLRSHom.toShHom).obj
            ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
        (Scheme.Modules.pushforward h).map
          (homologyFunctorDerivedPushforwardIso f''
            ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom :=
  homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv S F' h' f'' h sq

/-- **The transpose of `γ⁺`, with the comparison from derived to ordinary pullback named by a
variable.** `…TopDegreeBaseChange.homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv_app`
with the one occurrence of `…TopDegreeBaseChange.derivedToOrdinaryPullbackSingle` replaced by a
variable carrying its defining equation. -/
theorem homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv_app_of_eq
    {c : (derivedPullback h'.toLRSHom.toShHom).obj ((singleFunctor S.X'.Modules 0).obj F') ⟶
      (singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F')}
    (hc : derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F' 0 = c) :
    (homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ)).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
          (topDirectImageBaseChangeMapPlus S F' h' f'' h sq) =
      (homologyFunctor S.Y'.Modules (S.d : ℤ)).map
          ((derivedAdjunction h.toLRSHom.toShHom).homEquiv _ _
            ((derivedBaseChangeSquare h'.toLRSHom.toShHom f''.toLRSHom.toShHom
                  S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq).app
                ((singleFunctor S.X'.Modules 0).obj F') ≫
              (derivedPushforward f''.toLRSHom.toShHom).map c)) ≫
        (derivedPushforwardHomologyComparison h.toLRSHom.toShHom (S.d : ℤ)).app
          ((derivedPushforward f''.toLRSHom.toShHom).obj
            ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
        (Scheme.Modules.pushforward h).map
          (homologyFunctorDerivedPushforwardIso f''
            ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom := by
  rw [← hc]
  exact homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv_app S F' h' f'' h sq

omit [SheafOfModules.IsQuasicoherent F'] in
/-- **The mate identity read inside the degree-`d` cohomology, at a variable trailing map.** The
substitution `homEquiv_derivedBaseChangeSquare_comp_right` performs, carried through
`H^d` and the two factors that follow it. -/
theorem map_homEquiv_comp_eq_map_mate
    {c : (derivedPullback h'.toLRSHom.toShHom).obj ((singleFunctor S.X'.Modules 0).obj F') ⟶
      (singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F')} :
      (homologyFunctor S.Y'.Modules (S.d : ℤ)).map
          ((derivedAdjunction h.toLRSHom.toShHom).homEquiv _ _
            ((derivedBaseChangeSquare h'.toLRSHom.toShHom f''.toLRSHom.toShHom
                  S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq).app
                ((singleFunctor S.X'.Modules 0).obj F') ≫
              (derivedPushforward f''.toLRSHom.toShHom).map c)) ≫
        (derivedPushforwardHomologyComparison h.toLRSHom.toShHom (S.d : ℤ)).app
          ((derivedPushforward f''.toLRSHom.toShHom).obj
            ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
        (Scheme.Modules.pushforward h).map
          (homologyFunctorDerivedPushforwardIso f''
            ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom =
      (homologyFunctor S.Y'.Modules (S.d : ℤ)).map
          ((derivedPushforward S.f'.toLRSHom.toShHom).map
              ((derivedAdjunction h'.toLRSHom.toShHom).unit.app
                ((singleFunctor S.X'.Modules 0).obj F')) ≫
            (Mate.derivedPushforwardComparisonSquare
                (derivedAdjunction S.f'.toLRSHom.toShHom)
                (derivedAdjunction f''.toLRSHom.toShHom)
                (derivedAdjunction h.toLRSHom.toShHom)
                (derivedAdjunction h'.toLRSHom.toShHom)
                (derivedPullbackCompIsoLeft h'.toLRSHom.toShHom f''.toLRSHom.toShHom
                  S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq)
                (derivedPullbackCompIsoCanonical h'.toLRSHom.toShHom
                  S.f'.toLRSHom.toShHom)).app
                ((derivedPullback h'.toLRSHom.toShHom).obj
                  ((singleFunctor S.X'.Modules 0).obj F')) ≫
              (derivedPushforward h.toLRSHom.toShHom).map
                ((derivedPushforward f''.toLRSHom.toShHom).map c)) ≫
        (derivedPushforwardHomologyComparison h.toLRSHom.toShHom (S.d : ℤ)).app
          ((derivedPushforward f''.toLRSHom.toShHom).obj
            ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
        (Scheme.Modules.pushforward h).map
          (homologyFunctorDerivedPushforwardIso f''
            ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom :=
  map_comp_congr (homologyFunctor S.Y'.Modules (S.d : ℤ))
    (homEquiv_derivedBaseChangeSquare_comp_right h'.toLRSHom.toShHom f''.toLRSHom.toShHom
      S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq _ c) _

/-- **The transpose of `γ⁺` with no derived base change map in it.** The crossing of the two
models of `Rf_*` followed by the transpose of `γ⁺` under `h^* ⊣ h_*` is the degree-`d` cohomology
of

> `Rf'_*(F'[0]) ⟶ Rf'_*(Rh'_*(Lh'^*(F'[0]))) ⟶ Rh_*(Rf''_*(Lh'^*(F'[0])))`
> `⟶ Rh_*(Rf''_*((h')^* F'[0]))`,

the derived pushforward along `f'` of the derived unit of `Lh'^* ⊣ Rh'_*`, the comparison of the
two iterated derived pushforwards, and `Rh_*(Rf''_*)` of the comparison from derived to ordinary
pullback, followed by the cohomology edge morphism of `Rh_*` and by `h_*` of the crossing at
`f''`. The comparison from derived to ordinary pullback is the variable `c`, given by its defining
equation `hc`. -/
theorem homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv_eq_mate
    {c : (derivedPullback h'.toLRSHom.toShHom).obj ((singleFunctor S.X'.Modules 0).obj F') ⟶
      (singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F')}
    (hc : derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F' 0 = c) :
    (homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ)).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
          (topDirectImageBaseChangeMapPlus S F' h' f'' h sq) =
      (homologyFunctor S.Y'.Modules (S.d : ℤ)).map
          ((derivedPushforward S.f'.toLRSHom.toShHom).map
              ((derivedAdjunction h'.toLRSHom.toShHom).unit.app
                ((singleFunctor S.X'.Modules 0).obj F')) ≫
            (Mate.derivedPushforwardComparisonSquare
                (derivedAdjunction S.f'.toLRSHom.toShHom)
                (derivedAdjunction f''.toLRSHom.toShHom)
                (derivedAdjunction h.toLRSHom.toShHom)
                (derivedAdjunction h'.toLRSHom.toShHom)
                (derivedPullbackCompIsoLeft h'.toLRSHom.toShHom f''.toLRSHom.toShHom
                  S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq)
                (derivedPullbackCompIsoCanonical h'.toLRSHom.toShHom
                  S.f'.toLRSHom.toShHom)).app
                ((derivedPullback h'.toLRSHom.toShHom).obj
                  ((singleFunctor S.X'.Modules 0).obj F')) ≫
              (derivedPushforward h.toLRSHom.toShHom).map
                ((derivedPushforward f''.toLRSHom.toShHom).map c)) ≫
        (derivedPushforwardHomologyComparison h.toLRSHom.toShHom (S.d : ℤ)).app
          ((derivedPushforward f''.toLRSHom.toShHom).obj
            ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
        (Scheme.Modules.pushforward h).map
          (homologyFunctorDerivedPushforwardIso f''
            ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom :=
  (homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv_app_of_eq S F' h' f'' h sq hc).trans
    (map_homEquiv_comp_eq_map_mate S F' h' f'' h sq)

/-- **The transpose of `γ⁺` with the whole route upstairs folded into one morphism of
`D(𝒪_{X'})`.** Given the comparison from derived to ordinary pullback as a variable `c` with its
equation, and the composite of the derived unit of `Lh'^* ⊣ Rh'_*` with `Rh'_*(c)` as a variable
`w` with its equation, the crossing of the two models of `Rf_*` followed by the transpose of `γ⁺`
is the degree-`d` cohomology of `Rf'_*(w)` and of the comparison of the two iterated derived
pushforwards, followed by the cohomology edge morphism of `Rh_*` and by `h_*` of the crossing at
`f''`.

`w` is the derived transpose of `c` — the map `F'[0] ⟶ Rh'_*((h')^* F'[0])` the source of the tag
calls *the canonical map* — so this says: **the transpose of `γ⁺` is `Rf'_*` of the derived
transpose of the derived-to-ordinary pullback comparison, read through the comparison of the two
iterated derived pushforwards and the edge morphism.** -/
theorem homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv_eq_transpose
    {c : (derivedPullback h'.toLRSHom.toShHom).obj ((singleFunctor S.X'.Modules 0).obj F') ⟶
      (singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F')}
    (hc : derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F' 0 = c)
    {w : (singleFunctor S.X'.Modules 0).obj F' ⟶
      (derivedPushforward h'.toLRSHom.toShHom).obj
        ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))}
    (hw : (derivedAdjunction h'.toLRSHom.toShHom).unit.app
          ((singleFunctor S.X'.Modules 0).obj F') ≫
        (derivedPushforward h'.toLRSHom.toShHom).map c = w) :
    (homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ)).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
          (topDirectImageBaseChangeMapPlus S F' h' f'' h sq) =
      (homologyFunctor S.Y'.Modules (S.d : ℤ)).map
          ((derivedPushforward S.f'.toLRSHom.toShHom).map w ≫
            (Mate.derivedPushforwardComparisonSquare
                (derivedAdjunction S.f'.toLRSHom.toShHom)
                (derivedAdjunction f''.toLRSHom.toShHom)
                (derivedAdjunction h.toLRSHom.toShHom)
                (derivedAdjunction h'.toLRSHom.toShHom)
                (derivedPullbackCompIsoLeft h'.toLRSHom.toShHom f''.toLRSHom.toShHom
                  S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq)
                (derivedPullbackCompIsoCanonical h'.toLRSHom.toShHom
                  S.f'.toLRSHom.toShHom)).app
              ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
        (derivedPushforwardHomologyComparison h.toLRSHom.toShHom (S.d : ℤ)).app
          ((derivedPushforward f''.toLRSHom.toShHom).obj
            ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
        (Scheme.Modules.pushforward h).map
          (homologyFunctorDerivedPushforwardIso f''
            ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom :=
  (homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv_eq_mate S F' h' f'' h sq hc).trans
    (map_comp_congr (homologyFunctor S.Y'.Modules (S.d : ℤ))
      (map_comp_app_comp_map_eq
        (Mate.derivedPushforwardComparisonSquare
                (derivedAdjunction S.f'.toLRSHom.toShHom)
                (derivedAdjunction f''.toLRSHom.toShHom)
                (derivedAdjunction h.toLRSHom.toShHom)
                (derivedAdjunction h'.toLRSHom.toShHom)
                (derivedPullbackCompIsoLeft h'.toLRSHom.toShHom f''.toLRSHom.toShHom
                  S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq)
                (derivedPullbackCompIsoCanonical h'.toLRSHom.toShHom
                  S.f'.toLRSHom.toShHom))
        ((derivedAdjunction h'.toLRSHom.toShHom).unit.app
          ((singleFunctor S.X'.Modules 0).obj F')) c hw) _)

omit [SheafOfModules.IsQuasicoherent F'] in
/-- **The derived transpose at the situation, through the ordinary unit of [Stacks, Tag 0096].**
`derivedAdjunction_unit_comp_map_derivedToOrdinary_eq_single_unit` at the morphism of ringed
spaces underlying `h'`, with the leading factor written with the scheme-level single functor and
the unit that of the adjunction of ringed spaces. -/
theorem derivedUnit_comp_map_derivedToOrdinary_single_unit :
    (derivedAdjunction h'.toLRSHom.toShHom).unit.app
          ((singleFunctor S.X'.Modules 0).obj F') ≫
        (derivedPushforward h'.toLRSHom.toShHom).map
          (derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F' 0) =
      (singleFunctor S.X'.Modules 0).map
          ((modulePullbackPushforwardAdjunction h'.toLRSHom.toShHom).unit.app F') ≫
        (singleFunctorIsoCompQh
            (SheafOfModules.{u} (structureSheafRing S.X'.toSheafedSpace)) 0).hom.app
          ((modulePushforward h'.toLRSHom.toShHom).obj
            ((modulePullback h'.toLRSHom.toShHom).obj F')) ≫
        Qh.map ((Functor.mapHomotopyCategorySingleFunctor
              (modulePushforward h'.toLRSHom.toShHom) 0).inv.app
            ((modulePullback h'.toLRSHom.toShHom).obj F')) ≫
          (derivedPushforwardUnit h'.toLRSHom.toShHom).app
              ((HomotopyCategory.singleFunctor
                  (SheafOfModules.{u} (structureSheafRing X''.toSheafedSpace)) 0).obj
                ((modulePullback h'.toLRSHom.toShHom).obj F')) ≫
            (derivedPushforward h'.toLRSHom.toShHom).map
              ((singleFunctorIsoCompQh
                  (SheafOfModules.{u} (structureSheafRing X''.toSheafedSpace)) 0).inv.app
                ((modulePullback h'.toLRSHom.toShHom).obj F')) :=
  derivedAdjunction_unit_comp_map_derivedToOrdinary_eq_single_unit h'.toLRSHom.toShHom F' 0

/-- **The transpose of `γ⁺`, with the route upstairs split at a variable and the tail named.**
`homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv_eq_transpose` with the route upstairs
split as `x ≫ y` and everything after `R^d f'_*(x)` carried by `Θ`. -/
theorem homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv_eq_split
    {B₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X'.toSheafedSpace))}
    {x : (singleFunctor S.X'.Modules 0).obj F' ⟶ B₀}
    {y : B₀ ⟶ (derivedPushforward h'.toLRSHom.toShHom).obj
        ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))}
    (hxy : (derivedAdjunction h'.toLRSHom.toShHom).unit.app
            ((singleFunctor S.X'.Modules 0).obj F') ≫
          (derivedPushforward h'.toLRSHom.toShHom).map
            (derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F' 0) = x ≫ y)
    {Θ : (homologyFunctor S.Y'.Modules (S.d : ℤ)).obj
          ((derivedPushforward S.f'.toLRSHom.toShHom).obj B₀) ⟶
        (Scheme.Modules.pushforward h).obj
          (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
            ((Scheme.Modules.pullback h').obj F'))}
    (hΘ : (homologyFunctor S.Y'.Modules (S.d : ℤ)).map
            ((derivedPushforward S.f'.toLRSHom.toShHom).map y ≫
              (Mate.derivedPushforwardComparisonSquare
                  (derivedAdjunction S.f'.toLRSHom.toShHom)
                  (derivedAdjunction f''.toLRSHom.toShHom)
                  (derivedAdjunction h.toLRSHom.toShHom)
                  (derivedAdjunction h'.toLRSHom.toShHom)
                  (derivedPullbackCompIsoLeft h'.toLRSHom.toShHom f''.toLRSHom.toShHom
                    S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq)
                  (derivedPullbackCompIsoCanonical h'.toLRSHom.toShHom
                    S.f'.toLRSHom.toShHom)).app
                ((singleFunctor X''.Modules 0).obj
                  ((Scheme.Modules.pullback h').obj F'))) ≫
          (derivedPushforwardHomologyComparison h.toLRSHom.toShHom (S.d : ℤ)).app
            ((derivedPushforward f''.toLRSHom.toShHom).obj
                ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
          (Scheme.Modules.pushforward h).map
            (homologyFunctorDerivedPushforwardIso f''
              ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom = Θ) :
    (homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ)).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
          (topDirectImageBaseChangeMapPlus S F' h' f'' h sq) =
      (homologyFunctor S.Y'.Modules (S.d : ℤ)).map
          ((derivedPushforward S.f'.toLRSHom.toShHom).map x) ≫ Θ :=
  ((homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv_eq_transpose S F' h' f'' h sq rfl
        hxy).trans
      (map_map_comp_split (derivedPushforward S.f'.toLRSHom.toShHom)
        (homologyFunctor S.Y'.Modules (S.d : ℤ)) x y _ _)).trans
    ((homologyFunctor S.Y'.Modules (S.d : ℤ)).map
      ((derivedPushforward S.f'.toLRSHom.toShHom).map x) ≫= hΘ)

/-- **The transpose of `γ⁺` split at the ordinary unit of [Stacks, Tag 0096].**
`homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv_eq_split` with its first half discharged
by `derivedUnit_comp_map_derivedToOrdinary_single_unit`: the crossing of the two models of `Rf'_*`
followed by the transpose of `γ⁺` is the degree-`d` cohomology of `Rf'_*` of the single functor of
the ordinary unit `F' ⟶ (h')_*(h')^* F'`, followed by `Θ`. -/
theorem homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv_eq_split_unit
    {Θ : (homologyFunctor S.Y'.Modules (S.d : ℤ)).obj
          ((derivedPushforward S.f'.toLRSHom.toShHom).obj
            ((singleFunctor S.X'.Modules 0).obj
              ((modulePullback h'.toLRSHom.toShHom ⋙
                modulePushforward h'.toLRSHom.toShHom).obj F'))) ⟶
        (Scheme.Modules.pushforward h).obj
          (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
            ((Scheme.Modules.pullback h').obj F'))}
    (hΘ : (homologyFunctor S.Y'.Modules (S.d : ℤ)).map
            ((derivedPushforward S.f'.toLRSHom.toShHom).map
                ((singleFunctorIsoCompQh
                  (SheafOfModules.{u} (structureSheafRing S.X'.toSheafedSpace)) 0).hom.app
                ((modulePushforward h'.toLRSHom.toShHom).obj
                  ((modulePullback h'.toLRSHom.toShHom).obj F')) ≫
              Qh.map ((Functor.mapHomotopyCategorySingleFunctor
                    (modulePushforward h'.toLRSHom.toShHom) 0).inv.app
                  ((modulePullback h'.toLRSHom.toShHom).obj F')) ≫
                (derivedPushforwardUnit h'.toLRSHom.toShHom).app
                    ((HomotopyCategory.singleFunctor
                      (SheafOfModules.{u} (structureSheafRing X''.toSheafedSpace)) 0).obj
                      ((modulePullback h'.toLRSHom.toShHom).obj F')) ≫
                  (derivedPushforward h'.toLRSHom.toShHom).map
                    ((singleFunctorIsoCompQh
                        (SheafOfModules.{u} (structureSheafRing X''.toSheafedSpace)) 0).inv.app
                      ((modulePullback h'.toLRSHom.toShHom).obj F'))) ≫
              (Mate.derivedPushforwardComparisonSquare
                  (derivedAdjunction S.f'.toLRSHom.toShHom)
                  (derivedAdjunction f''.toLRSHom.toShHom)
                  (derivedAdjunction h.toLRSHom.toShHom)
                  (derivedAdjunction h'.toLRSHom.toShHom)
                  (derivedPullbackCompIsoLeft h'.toLRSHom.toShHom f''.toLRSHom.toShHom
                    S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq)
                  (derivedPullbackCompIsoCanonical h'.toLRSHom.toShHom
                    S.f'.toLRSHom.toShHom)).app
                ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
          (derivedPushforwardHomologyComparison h.toLRSHom.toShHom (S.d : ℤ)).app
            ((derivedPushforward f''.toLRSHom.toShHom).obj
              ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
          (Scheme.Modules.pushforward h).map
            (homologyFunctorDerivedPushforwardIso f''
              ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom = Θ) :
    (homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ)).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
          (topDirectImageBaseChangeMapPlus S F' h' f'' h sq) =
      (homologyFunctor S.Y'.Modules (S.d : ℤ)).map
          ((derivedPushforward S.f'.toLRSHom.toShHom).map
            ((singleFunctor S.X'.Modules 0).map
              ((modulePullbackPushforwardAdjunction h'.toLRSHom.toShHom).unit.app F'))) ≫ Θ :=
  homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv_eq_split S F' h' f'' h sq
    (derivedUnit_comp_map_derivedToOrdinary_single_unit S F' h') hΘ

/-- **The transpose of `γ⁺` is `R^d f'_*` of the ordinary unit of `(h')^* ⊣ (h')_*`, followed by a
composite of canonical comparisons.** For a top-degree base-change situation `S`, a quasi-coherent
`F'` and a **commutative** square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
the adjoint transpose of the canonical map `γ⁺` of [Stacks, Tag 0EX3] (c) under `h^* ⊣ h_*` is

> `R^d f'_* F' ⟶ R^d f'_*((h')_*(h')^* F') ⟶ h_* R^d f''_*((h')^* F')`,

the degree-`d` higher direct image along `f'` of the **ordinary** unit `F' ⟶ (h')_*(h')^* F'` of
[Stacks, Tag 0096], then the crossing of the two models of `Rf'_*` inverted, then the degree-`d`
cohomology of `Rf'_*` of the comparison of the two models of `Rh'_*` and of the comparison of the
two iterated derived pushforwards, the cohomology edge morphism of `Rh_*`, and `h_*` of the
crossing at `f''`. -/
theorem homEquiv_topDirectImageBaseChangeMapPlus_eq_rightDerivedPlus_unit :
    (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
        (topDirectImageBaseChangeMapPlus S F' h' f'' h sq) =
      ((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).map
          ((modulePullbackPushforwardAdjunction h'.toLRSHom.toShHom).unit.app F') ≫
        (homologyFunctorDerivedPushforwardIso S.f'
            ((modulePullback h'.toLRSHom.toShHom ⋙
              modulePushforward h'.toLRSHom.toShHom).obj F') (S.d : ℤ)).inv ≫
          (homologyFunctor S.Y'.Modules (S.d : ℤ)).map
            ((derivedPushforward S.f'.toLRSHom.toShHom).map
                ((singleFunctorIsoCompQh
                  (SheafOfModules.{u} (structureSheafRing S.X'.toSheafedSpace)) 0).hom.app
                ((modulePushforward h'.toLRSHom.toShHom).obj
                  ((modulePullback h'.toLRSHom.toShHom).obj F')) ≫
              Qh.map ((Functor.mapHomotopyCategorySingleFunctor
                    (modulePushforward h'.toLRSHom.toShHom) 0).inv.app
                  ((modulePullback h'.toLRSHom.toShHom).obj F')) ≫
                (derivedPushforwardUnit h'.toLRSHom.toShHom).app
                    ((HomotopyCategory.singleFunctor
                      (SheafOfModules.{u} (structureSheafRing X''.toSheafedSpace)) 0).obj
                      ((modulePullback h'.toLRSHom.toShHom).obj F')) ≫
                  (derivedPushforward h'.toLRSHom.toShHom).map
                    ((singleFunctorIsoCompQh
                        (SheafOfModules.{u} (structureSheafRing X''.toSheafedSpace)) 0).inv.app
                      ((modulePullback h'.toLRSHom.toShHom).obj F'))) ≫
              (Mate.derivedPushforwardComparisonSquare
                  (derivedAdjunction S.f'.toLRSHom.toShHom)
                  (derivedAdjunction f''.toLRSHom.toShHom)
                  (derivedAdjunction h.toLRSHom.toShHom)
                  (derivedAdjunction h'.toLRSHom.toShHom)
                  (derivedPullbackCompIsoLeft h'.toLRSHom.toShHom f''.toLRSHom.toShHom
                    S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq)
                  (derivedPullbackCompIsoCanonical h'.toLRSHom.toShHom
                    S.f'.toLRSHom.toShHom)).app
                ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
          (derivedPushforwardHomologyComparison h.toLRSHom.toShHom (S.d : ℤ)).app
            ((derivedPushforward f''.toLRSHom.toShHom).obj
              ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
          (Scheme.Modules.pushforward h).map
            (homologyFunctorDerivedPushforwardIso f''
              ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom :=
  eq_of_iso_hom_comp_eq (homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ))
    (homologyFunctorDerivedPushforwardIso S.f'
      ((modulePullback h'.toLRSHom.toShHom ⋙
        modulePushforward h'.toLRSHom.toShHom).obj F') (S.d : ℤ))
    (homologyFunctorDerivedPushforwardIso_hom_naturality S.f'
      ((modulePullbackPushforwardAdjunction h'.toLRSHom.toShHom).unit.app F') (S.d : ℤ))
    (homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv_eq_split_unit S F' h' f'' h sq rfl)

end Card

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
